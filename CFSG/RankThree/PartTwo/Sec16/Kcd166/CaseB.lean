module

public import CFSG.GroupTheory.SteinbergCBHHBIntertwiner
public import CFSG.LinearAlgebra.CoprimeActions.IrreducibleCentralCharacter
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.GroupTheory.Commutator.ThreeSubgroupsModNormal
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.CharacterTheory.SteinbergBYModularRealization
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalPGroupSimpleModule
public import CFSG.RankThree.PartTwo.Sec16.Item166ThetaCompY
public import CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreducibleFiniteCenterCyclic
public import CFSG.GroupTheory.QuaternionCentralizers
public import CFSG.Holt.TwoGroups
public import CFSG.CGT.PushingUpLit.CGT6.Diag.IdentRep
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCentralTransferKernel
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Involution
public import TauCeti.GroupTheory.QuotientGroup.MulAut
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open scoped commutatorElement
open CFSG CFSG.RankThree.PartTwo

attribute [local instance] commutatorElement

private theorem injective_of_commutator_mem_center
    {𝕜 Q W : Type*} [Field 𝕜] [Group Q] [AddCommGroup W] [Module 𝕜 W]
    (σ : Representation 𝕜 Q W)
    (hcl : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q)
    (hfaith : ∀ z ∈ Subgroup.center Q, σ z = 1 → z = 1) : Function.Injective σ := by
  classical
  let ρ : Q →* (Module.End 𝕜 W)ˣ := σ.asGroupHom
  have hρval : ∀ g : Q, ((ρ g : (Module.End 𝕜 W)ˣ) : Module.End 𝕜 W) = σ g :=
    fun g => σ.asGroupHom_apply g
  have hker_center : ∀ x : Q, σ x = 1 → x ∈ Subgroup.center Q := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxu : ρ x = 1 := by
      apply Units.ext
      simp [hρval, hx]
    have hcomm : σ ⁅x, y⁆ = 1 := by
      have h1 : ρ ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement, hxu]
        simp
      have h1val : ((ρ ⁅x, y⁆ : (Module.End 𝕜 W)ˣ) : Module.End 𝕜 W) = 1 := by
        rw [h1]
        rfl
      simpa only [hρval] using h1val
    exact (commutatorElement_eq_one_iff_mul_comm.mp
      (hfaith ⁅x, y⁆ (hcl x y) hcomm)).symm
  intro x y hxy
  have hxyu : ρ x = ρ y := Units.ext hxy
  have h1 : σ (x * y⁻¹) = 1 := by
    have h1u : ρ (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxyu, mul_inv_cancel]
    have h1val : ((ρ (x * y⁻¹) : (Module.End 𝕜 W)ˣ) : Module.End 𝕜 W) = 1 := by
      rw [h1u]
      rfl
    simpa only [hρval] using h1val
  have hmem : x * y⁻¹ ∈ Subgroup.center Q := hker_center _ h1
  exact mul_inv_eq_one.mp (hfaith _ hmem h1)

theorem card_quotient_center_eq_finrank_sq {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
    {Q : Type*} [Group Q] [Finite Q]
    {W : Type*} [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W]
    (σ : Representation 𝕜 Q W) (hirr : σ.IsIrreducible)
    (hcl : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q)
    (hfaith : ∀ z ∈ Subgroup.center Q, σ z = 1 → z = 1) :
    Nat.card (Q ⧸ Subgroup.center Q) = Module.finrank 𝕜 W ^ 2 := by
  classical
  haveI : Nontrivial W :=
    CFSG.RankThree.GroupTheory.nontrivial_of_isIrreducible hirr
  have hσ_inj : Function.Injective σ :=
    injective_of_commutator_mem_center σ hcl hfaith
  obtain ⟨χ, -, hχ⟩ :=
    CFSG.LinearAlgebra.CoprimeActions.IrreducibleCentralCharacter.exists_character
      σ hσ_inj hirr
  let ρ : Q →* (Module.End 𝕜 W)ˣ := σ.asGroupHom
  have hρval : ∀ g : Q, ((ρ g : (Module.End 𝕜 W)ˣ) : Module.End 𝕜 W) = σ g :=
    fun g => σ.asGroupHom_apply g
  have hsc : ∀ c ∈ Subgroup.center Q, ∃ μ : 𝕜,
      ((ρ c : (Module.End 𝕜 W)ˣ) : Module.End 𝕜 W) = μ • 1 := by
    intro c hc
    exact ⟨(χ ⟨c, hc⟩ : 𝕜), by
      simpa [hρval, Module.End.one_eq_id] using hχ ⟨c, hc⟩⟩
  have hcl' : ∀ s t : Q, t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center Q := by
    intro s t
    simpa [commutatorElement_def] using hcl t s
  have hirr' : ∀ W₁ : Submodule 𝕜 W,
      (∀ g : Q, ∀ w ∈ W₁, ((ρ g : (Module.End 𝕜 W)ˣ) : Module.End 𝕜 W) w ∈ W₁) →
        W₁ = ⊥ ∨ W₁ = ⊤ := by
    intro W₁ hW
    exact CFSG.RankThree.GroupTheory.eq_bot_or_eq_top_of_isIrreducible hirr W₁
      (fun g v hv => hW g v hv)
  have hρ_inj : Function.Injective ρ := by
    intro x y hxy
    exact hσ_inj (by
      simpa only [hρval] using congrArg
        (fun u : (Module.End 𝕜 W)ˣ => (u : Module.End 𝕜 W)) hxy)
  exact (CFSG.GroupTheory.HallHigmanB.finrank_sq_eq_card_quotient_center
    ρ hρ_inj hsc hcl' hirr').symm


section MainProof

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜] {p : ℕ} [CharP 𝕜 p]
variable {Γ : Type*} [Group Γ] [Finite Γ]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
variable {T : Type*} [Group T]
variable {ρ : Representation 𝕜 Γ V}

private abbrev centerMap (Q : Subgroup Γ) : Subgroup Γ :=
  (Subgroup.center Q).map Q.subtype

private abbrev frattiniMap (Q : Subgroup Γ) : Subgroup Γ :=
  (frattini Q).map Q.subtype

private noncomputable def conjOnQuotient (Q : Subgroup Γ) [Q.Normal] :
    Γ →* MulAut (Q ⧸ Subgroup.center Q) :=
  letI : (Subgroup.center Q).Characteristic := Subgroup.centerCharacteristic
  (MulAut.mapQuotient (Subgroup.center Q)).comp (MulAut.conjNormal (H := Q))

private noncomputable def K0 (Q : Subgroup Γ) [Q.Normal] : Subgroup Γ :=
  (conjOnQuotient Q).ker

private abbrev centralizerQ (Q : Subgroup Γ) : Subgroup Γ :=
  Subgroup.centralizer (Q : Set Γ)

private lemma centerMap_normal {Q : Subgroup Γ} [Q.Normal] :
    (centerMap Q).Normal := by
  letI : (Subgroup.center Q).Characteristic := Subgroup.centerCharacteristic
  exact ConjAct.normal_of_characteristic_of_normal

private lemma centerMap_lt {Q : Subgroup Γ} (hQc : ¬ IsMulCommutative Q) :
    centerMap Q < Q := by
  refine lt_of_le_of_ne (Subgroup.map_subtype_le _) ?_
  intro hZeq
  have hZeq' : (Subgroup.center Q).map Q.subtype = Q := hZeq
  have hcenter_top : Subgroup.center Q = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    rw [hZeq', Subgroup.map_top, Subgroup.range_subtype]
  exact hQc ⟨⟨fun a b => by
    have ha : a ∈ Subgroup.center Q := by rw [hcenter_top]; trivial
    exact (Subgroup.mem_center_iff.mp ha b).symm⟩⟩

private lemma centerMap_central {Q : Subgroup Γ} [Q.Normal]
    (hQc : ¬ IsMulCommutative Q)
    (hmin : ∀ R : Subgroup Γ, R.Normal → R < Q → R ≤ Subgroup.center Γ) :
    centerMap Q ≤ Subgroup.center Γ :=
  hmin _ (centerMap_normal) (centerMap_lt hQc)

private lemma frattiniMap_normal {Q : Subgroup Γ} [Q.Normal] :
    (frattiniMap Q).Normal := by
  letI : (frattini Q).Characteristic := frattini_characteristic
  exact ConjAct.normal_of_characteristic_of_normal

private lemma frattiniMap_lt {Q : Subgroup Γ} [Nontrivial Q] :
    frattiniMap Q < Q := by
  have hfr_ne_top : frattini Q ≠ ⊤ := by
    intro htop
    have hbot : (⊥ : Subgroup Q) = ⊤ :=
      frattini_nongenerating (G := Q) (K := ⊥) (by rw [htop, bot_sup_eq])
    exact bot_ne_top hbot
  refine lt_of_le_of_ne (Subgroup.map_subtype_le _) ?_
  intro hQ0eq
  have hQ0eq' : (frattini Q).map Q.subtype = Q := hQ0eq
  apply hfr_ne_top
  apply Subgroup.map_subtype_inj.mp
  rw [hQ0eq', Subgroup.map_top, Subgroup.range_subtype]

private lemma frattiniMap_central {Q : Subgroup Γ} [Q.Normal] [Nontrivial Q]
    (hmin : ∀ R : Subgroup Γ, R.Normal → R < Q → R ≤ Subgroup.center Γ) :
    frattiniMap Q ≤ Subgroup.center Γ :=
  hmin _ (frattiniMap_normal) (frattiniMap_lt)

private lemma commutator_mem_center {Q : Subgroup Γ} {r : ℕ} (hr : r.Prime)
    (hQr : IsPGroup r Q)
    (hQ0center : frattiniMap Q ≤ Subgroup.center Γ) :
    ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q := by
  letI : Fact r.Prime := ⟨hr⟩
  letI : Fact (IsPGroup r Q) := ⟨hQr⟩
  intro x y
  have hmem : ((⁅x, y⁆ : Q) : Γ) ∈ frattiniMap Q := by
    refine Subgroup.mem_map.mpr ⟨⁅x, y⁆, ?_, rfl⟩
    exact CFSG.commutator_le_frattini_of_isPGroup (p := r) (R := Q)
      (Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤)
        (Subgroup.mem_top x) (Subgroup.mem_top y))
  have hc : ((⁅x, y⁆ : Q) : Γ) ∈ Subgroup.center Γ := hQ0center hmem
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro z
  exact Subtype.ext (hc (z : Γ))

private lemma pow_mem_center {Q : Subgroup Γ} {r : ℕ} (hr : r.Prime)
    (hQr : IsPGroup r Q)
    (hQ0center : frattiniMap Q ≤ Subgroup.center Γ) :
    ∀ x : Q, x ^ r ∈ Subgroup.center Q := by
  letI : Fact r.Prime := ⟨hr⟩
  letI : Fact (IsPGroup r Q) := ⟨hQr⟩
  intro x
  have hmem : ((x ^ r : Q) : Γ) ∈ frattiniMap Q :=
    Subgroup.mem_map.mpr ⟨x ^ r,
      CFSG.pth_power_mem_frattini_of_isPGroup (p := r) x, rfl⟩
  have hc : ((x ^ r : Q) : Γ) ∈ Subgroup.center Γ := hQ0center hmem
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro z
  exact Subtype.ext (hc (z : Γ))

private lemma quotient_elementary {Q : Subgroup Γ} {r : ℕ} (hr : r.Prime)
    (hcommQ : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q)
    (hpowQ : ∀ x : Q, x ^ r ∈ Subgroup.center Q) :
    CFSG.IsElementaryAbelian r (Q ⧸ Subgroup.center Q) := by
  letI : Fact r.Prime := ⟨hr⟩
  have hclass : _root_.commutator Q ≤ Subgroup.center Q := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hcommQ x y
  have hQquotComm : IsMulCommutative (Q ⧸ Subgroup.center Q) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := Subgroup.center Q)).2 hclass
  have hQquotExp : ∀ x : Q ⧸ Subgroup.center Q, x ^ r = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) x
    have h : QuotientGroup.mk' (Subgroup.center Q) (y ^ r) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hpowQ y)
    simpa using h
  exact { toIsMulCommutative := hQquotComm
          exponent_dvd_p :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hQquotExp }

private lemma r_ne_p {Q : Subgroup Γ} [Q.Normal] {r : ℕ} (hp : p.Prime)
    (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    (hQr : IsPGroup r Q) (hQc : ¬ IsMulCommutative Q) (hrp : r = p) : False := by
  letI : Fact p.Prime := ⟨hp⟩
  have hQrp : IsPGroup p Q := hrp ▸ hQr
  have hact : ∀ q : Q, ρ (q : Γ) = 1 := fun q =>
    CFSG.TwoRankLowerBound.Helpers.normal_p_subgroup_irreducible_action_trivial
      p ρ Q hQrp q
  have hQbot : Q = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have hq1 : q = 1 := hfaith (by simpa using hact ⟨q, hq⟩)
    simpa [hq1]
  exact hQc (by rw [hQbot]; infer_instance)

private lemma r_ne_three {Q : Subgroup Γ} [Nontrivial Q] {r : ℕ} {π : Γ →* T}
    (hQr : IsPGroup r Q) (hQD : Q ≤ π.ker)
    (hker3 : Nat.Coprime (Nat.card π.ker) 3) (hr3 : r = 3) : False := by
  subst hr3
  obtain ⟨n, hn⟩ := hQr.exists_card_eq
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      haveI : Subsingleton Q := by
        rw [h0, pow_zero] at hn
        exact (Nat.card_eq_one_iff_unique.mp hn).1
      exact false_of_nontrivial_of_subsingleton Q
    · exact hpos
  have h3Q : 3 ∣ Nat.card Q := by
    rw [hn]
    exact dvd_pow_self 3 hnpos.ne'
  have h3K : 3 ∣ Nat.card π.ker := h3Q.trans (Subgroup.card_dvd_of_le hQD)
  have hgcd : Nat.gcd (Nat.card π.ker) 3 = 1 := hker3
  have h3gcd : 3 ∣ Nat.gcd (Nat.card π.ker) 3 := Nat.dvd_gcd h3K (dvd_rfl)
  rw [hgcd] at h3gcd
  exact absurd h3gcd (by norm_num)

private lemma exists_center_character {Q : Subgroup Γ} [Q.Normal] [Nontrivial V]
    (hZcenter : centerMap Q ≤ Subgroup.center Γ)
    (hfaith : Function.Injective ρ) (hirr : ρ.IsIrreducible) :
    ∃ χQ : Subgroup.center Q →* 𝕜ˣ, Function.Injective χQ ∧
      (∀ z : Subgroup.center Q,
        ρ (z : Γ) = (χQ z : 𝕜) • (1 : Module.End 𝕜 V)) := by
  obtain ⟨χΓ, hχΓinj, hχΓ⟩ :=
    CFSG.LinearAlgebra.CoprimeActions.IrreducibleCentralCharacter.exists_character
      ρ hfaith hirr
  let centerToCenter : Subgroup.center Q →* Subgroup.center Γ :=
    { toFun := fun z => ⟨(z : Γ), hZcenter (Subgroup.mem_map.mpr ⟨z, z.2, rfl⟩)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  let χQ : Subgroup.center Q →* 𝕜ˣ := χΓ.comp centerToCenter
  refine ⟨χQ, ?_, ?_⟩
  · refine hχΓinj.comp ?_
    intro x y hxy
    have h1 : ((x : Q) : Γ) = ((y : Q) : Γ) :=
      congrArg (fun w : Subgroup.center Γ => (w : Γ)) hxy
    exact Subtype.ext (Q.subtype_injective h1)
  · intro z
    exact hχΓ (centerToCenter z)

private lemma center_action_faithful {Q : Subgroup Γ}
    {W : Subrepresentation (ρ.comp Q.subtype)} [Nontrivial W.toSubmodule]
    {χQ : Subgroup.center Q →* 𝕜ˣ}
    (hχQinj : Function.Injective χQ)
    (hχQspec : ∀ z : Subgroup.center Q,
      ρ (z : Γ) = (χQ z : 𝕜) • (1 : Module.End 𝕜 V)) :
    ∀ z ∈ Subgroup.center Q, W.toRepresentation z = 1 → z = 1 := by
  intro z hz hz1
  have hzχ : χQ ⟨z, hz⟩ = 1 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W.toSubmodule)
    have hwV : ((w : V)) ≠ 0 := fun h => hw (Subtype.ext h)
    have h1 : ((χQ ⟨z, hz⟩ : 𝕜) • (((w : W.toSubmodule) : V))) = (w : V) := by
      have h2 : (W.toRepresentation z) w = w := by
        have := congrArg (fun f : W.toSubmodule →ₗ[𝕜] W.toSubmodule => f w) hz1
        simpa using this
      calc ((χQ ⟨z, hz⟩ : 𝕜) • (((w : W.toSubmodule) : V)))
          = ρ z (w : V) := by
            rw [hχQspec ⟨z, hz⟩]
            rfl
        _ = ((W.toRepresentation z) w : V) := rfl
        _ = (w : V) := congrArg Subtype.val h2
    have hscalar : (χQ ⟨z, hz⟩ : 𝕜) = 1 := by
      exact smul_left_injective 𝕜 hwV (by simpa using h1)
    exact Units.ext hscalar
  have hz1' : (⟨z, hz⟩ : Subgroup.center Q) = 1 := hχQinj (by simpa using hzχ)
  exact congrArg (fun w : Subgroup.center Q => (w : Q)) hz1'

private lemma m_bounds {Q : Subgroup Γ} {W : Subrepresentation (ρ.comp Q.subtype)}
    {r m : ℕ} (hr : r.Prime) (hQc : ¬ IsMulCommutative Q)
    (hm : Nat.card (Q ⧸ Subgroup.center Q) = r ^ m)
    (hWsq : Module.finrank 𝕜 W.toSubmodule ^ 2 = r ^ m)
    (hWdim_le : Module.finrank 𝕜 W.toSubmodule ≤ 9) :
    m ≤ 6 ∧ 0 < m ∧ Even m := by
  have hWsq_le : Module.finrank 𝕜 W.toSubmodule ^ 2 ≤ 81 := by
    nlinarith [hWdim_le, Nat.zero_le (Module.finrank 𝕜 W.toSubmodule)]
  have hm_le : m ≤ 6 := by
    have h2m : 2 ^ m ≤ 81 := by
      calc 2 ^ m ≤ r ^ m := Nat.pow_le_pow_left (Nat.Prime.two_le hr) m
        _ = Module.finrank 𝕜 W.toSubmodule ^ 2 := hWsq.symm
        _ ≤ 81 := hWsq_le
    by_contra h
    have h7 : 7 ≤ m := by omega
    have hpow : 2 ^ 7 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h7
    have : 128 ≤ 81 := le_trans hpow h2m
    norm_num at this
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      have hcard1 : Nat.card (Q ⧸ Subgroup.center Q) = 1 := by rw [hm, h0, pow_zero]
      have hsub : Subsingleton (Q ⧸ Subgroup.center Q) :=
        (Nat.card_eq_one_iff_unique.mp hcard1).1
      have htop : Subgroup.center Q = ⊤ := QuotientGroup.subsingleton_iff.mp hsub
      exact hQc ⟨⟨fun a b => by
        have ha : a ∈ Subgroup.center Q := by rw [htop]; trivial
        exact (Subgroup.mem_center_iff.mp ha b).symm⟩⟩
    · exact hpos
  have hm_even : Even m := by
    have hsquare : IsSquare (r ^ m) := ⟨Module.finrank 𝕜 W.toSubmodule,
      by rw [← hWsq]; ring⟩
    have h := (Nat.isSquare_iff_even_factorization.mp hsquare) r hr
    rwa [Nat.factorization_pow_self hr] at h
  exact ⟨hm_le, hm_pos, hm_even⟩

private lemma K0_ne_top {Q : Subgroup Γ} [Q.Normal]
    (hZcenter : centerMap Q ≤ Subgroup.center Γ)
    (hQc : ¬ IsMulCommutative Q) (hperf : Group.IsPerfect Γ) :
    K0 Q ≠ ⊤ := by
  intro hK0top
  have hcomm_le : ⁅(⊤ : Subgroup Γ), Q⁆ ≤ Subgroup.center Γ := by
    rw [Subgroup.commutator_le]
    intro g _ x hx
    have hg : g ∈ K0 Q := by rw [hK0top]; trivial
    have hψg : conjOnQuotient Q g = 1 := MonoidHom.mem_ker.mp hg
    have h1 : (MulAut.mapQuotient (Subgroup.center Q) (MulAut.conjNormal g))
        (QuotientGroup.mk ⟨x, hx⟩) = QuotientGroup.mk ⟨x, hx⟩ := by
      have := congrArg (fun f : MulAut (Q ⧸ Subgroup.center Q) =>
        f (QuotientGroup.mk ⟨x, hx⟩)) hψg
      simpa [conjOnQuotient] using this
    rw [MulAut.mapQuotient_mk] at h1
    have h2 : (MulAut.conjNormal g ⟨x, hx⟩) / ⟨x, hx⟩ ∈ Subgroup.center Q :=
      QuotientGroup.eq_iff_div_mem.mp h1
    have h3 : ((⁅g, x⁆ : Γ)) = ((((MulAut.conjNormal g ⟨x, hx⟩) / ⟨x, hx⟩ : Q) : Γ)) := by
      simp [MulAut.conjNormal_apply, div_eq_mul_inv, commutatorElement_def]
    rw [h3]
    exact hZcenter (Subgroup.mem_map.mpr ⟨_, h2, rfl⟩)
  have hbot : ⁅(⊤ : Subgroup Γ), Q⁆ = ⊥ := by
    refine CFSG.GroupTheory.commutator_eq_bot_of_commutator_le_of_centralizer
      (A := (⊤ : Subgroup Γ)) (V := Q) (V₀ := Subgroup.center Γ) hcomm_le ?_ ?_
    · rw [Subgroup.centralizer_center]
    · exact hperf.commutator_eq_top
  have hQcenter : Q ≤ Subgroup.center Γ := by
    have hle : (⊤ : Subgroup Γ) ≤ Subgroup.centralizer (Q : Set Γ) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro g
    exact ((Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g))) q hq).symm
  exact hQc ⟨⟨fun a b => by
    have ha : (a : Γ) ∈ Subgroup.center Γ := hQcenter a.2
    exact Subtype.ext ((Subgroup.mem_center_iff.mp ha b).symm)⟩⟩

private lemma K0_card_dvd (Q : Subgroup Γ) [Q.Normal] :
    Nat.card (Γ ⧸ K0 Q) ∣ Nat.card (MulAut (Q ⧸ Subgroup.center Q)) := by
  letI : (K0 Q).Normal := MonoidHom.normal_ker _
  exact Subgroup.card_dvd_of_injective (QuotientGroup.kerLift (conjOnQuotient Q))
    (QuotientGroup.kerLift_injective (conjOnQuotient Q))

private lemma K0_GL_dvd {Q : Subgroup Γ} [Q.Normal] {r m : ℕ} (hr : r.Prime)
    (hQquotComm : IsMulCommutative (Q ⧸ Subgroup.center Q))
    (hQquotExp : ∀ x : Q ⧸ Subgroup.center Q, x ^ r = 1)
    (hm : Nat.card (Q ⧸ Subgroup.center Q) = r ^ m) :
    Nat.card (Γ ⧸ K0 Q) ∣ Nat.card (GL (Fin m) (ZMod r)) := by
  letI : Fact r.Prime := ⟨hr⟩
  letI : (K0 Q).Normal := MonoidHom.normal_ker _
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (p := r) (W := Q ⧸ Subgroup.center Q) (n := m)
    (fun a b => hQquotComm.is_comm.comm a b) hQquotExp hm
  have hcardMulAut : Nat.card (MulAut (Q ⧸ Subgroup.center Q)) =
      Nat.card (GL (Fin m) (ZMod r)) :=
    CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e
  rw [← hcardMulAut]
  exact K0_card_dvd Q

private lemma card_alternating_six :
    Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

private noncomputable def toA6 {T : Type*} [Group T]
    (hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover T (alternatingGroup (Fin 6))) :
    T →* alternatingGroup (Fin 6) :=
  hT.2.some.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center T))

private lemma toA6_surjective {T : Type*} [Group T]
    (hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover T (alternatingGroup (Fin 6))) :
    Function.Surjective (toA6 hT) :=
  hT.2.some.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center T))

private lemma toA6_ker {T : Type*} [Group T]
    (hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover T (alternatingGroup (Fin 6))) :
    (toA6 hT).ker = Subgroup.center T := by
  ext x
  rw [MonoidHom.mem_ker]
  change hT.2.some (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center T
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

private lemma K0_le_ker_of_image_bot {Q : Subgroup Γ} [Q.Normal] {π : Γ →* T}
    (σT : T →* alternatingGroup (Fin 6))
    (hbot : ((K0 Q).map π).map σT = ⊥) :
    K0 Q ≤ (σT.comp π).ker := by
  intro g hg
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  have hmem : σT (π g) ∈ ((K0 Q).map π).map σT :=
    Subgroup.mem_map.mpr ⟨π g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩, rfl⟩
  rw [hbot] at hmem
  simpa using hmem

private lemma K0_top_of_image_top {Q : Subgroup Γ} [Q.Normal] [Group.IsPerfect Γ]
    {π : Γ →* T} (hπ : Function.Surjective π) (σT : T →* alternatingGroup (Fin 6))
    (hσT_surj : Function.Surjective σT)
    (hσT_ker : σT.ker = Subgroup.center T)
    (hkerS : Group.IsSolvable π.ker) (hK0ne : K0 Q ≠ ⊤)
    (htop : ((K0 Q).map π).map σT = ⊤) : False := by
  letI : (K0 Q).Normal := MonoidHom.normal_ker _
  have hsup : (K0 Q).map π ⊔ σT.ker = ⊤ := by
    have h := htop
    rw [← MonoidHom.range_eq_top.mpr hσT_surj] at h
    exact codisjoint_iff.mp (Subgroup.map_eq_range_iff.mp h)
  haveI : Group.IsPerfect T := Group.IsPerfect.ofSurjective hπ
  have hπKtop : (K0 Q).map π = ⊤ :=
    CFSG.GroupTheory.eq_top_of_sup_le_center_of_isPerfect (L := (K0 Q).map π)
      (Z := σT.ker) (by rw [hσT_ker]) hsup
  have hsupΓ : K0 Q ⊔ π.ker = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : π g ∈ (K0 Q).map π := by rw [hπKtop]; trivial
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg
    have hgk : g * k⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      rw [hkg]
      exact mul_inv_cancel _
    have heq : g = (g * k⁻¹) * k := by group
    rw [heq]
    simpa [sup_comm] using Subgroup.mul_mem_sup (S := π.ker) (T := K0 Q) hgk hk
  have hsurjKer : Function.Surjective
      ((QuotientGroup.mk' (K0 Q)).comp (π.ker).subtype) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (K0 Q) y
    have hg : g ∈ K0 Q ⊔ π.ker := by rw [hsupΓ]; trivial
    obtain ⟨k, hk, n, hn, hkn⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    refine ⟨⟨n, hn⟩, ?_⟩
    have hk1 : QuotientGroup.mk' (K0 Q) k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    change QuotientGroup.mk' (K0 Q) n = QuotientGroup.mk' (K0 Q) g
    rw [← hkn, map_mul, hk1, one_mul]
  haveI : Group.IsSolvable π.ker := hkerS
  haveI : Group.IsSolvable (Γ ⧸ K0 Q) := Group.isSolvable_of_surjective hsurjKer
  haveI : Group.IsPerfect (Γ ⧸ K0 Q) := Group.IsPerfect.instQuotientSubgroup
  have hsub : Subsingleton (Γ ⧸ K0 Q) := by
    by_contra h
    haveI : Nontrivial (Γ ⧸ K0 Q) := (not_subsingleton_iff_nontrivial).mp h
    exact (Group.IsPerfect.not_isSolvable (Γ ⧸ K0 Q)) inferInstance
  have hK0top : K0 Q = ⊤ := QuotientGroup.subsingleton_iff.mp hsub
  exact hK0ne hK0top

private lemma three_dvd_of_image_bot {Q : Subgroup Γ} [Q.Normal] {π : Γ →* T}
    (hπ : Function.Surjective π) (σT : T →* alternatingGroup (Fin 6))
    (hσT_surj : Function.Surjective σT)
    (hbot : ((K0 Q).map π).map σT = ⊥) :
    360 ∣ Nat.card (Γ ⧸ K0 Q) := by
  letI : (K0 Q).Normal := MonoidHom.normal_ker _
  have hle : K0 Q ≤ (σT.comp π).ker := K0_le_ker_of_image_bot σT hbot
  let φbar : Γ ⧸ K0 Q →* alternatingGroup (Fin 6) :=
    QuotientGroup.lift (K0 Q) (σT.comp π) hle
  have hφbar_surj : Function.Surjective φbar := by
    intro y
    obtain ⟨g, rfl⟩ := hσT_surj.comp hπ y
    refine ⟨QuotientGroup.mk' (K0 Q) g, ?_⟩
    exact QuotientGroup.lift_mk' (N := K0 Q) (φ := σT.comp π) hle g
  have hdvd : Nat.card (alternatingGroup (Fin 6)) ∣ Nat.card (Γ ⧸ K0 Q) :=
    Subgroup.card_dvd_of_surjective hφbar_surj
  rw [← card_alternating_six]
  exact hdvd

private lemma three_dvd_card_quotient {Q : Subgroup Γ} [Q.Normal] [Group.IsPerfect Γ]
    {π : Γ →* T} (hπ : Function.Surjective π)
    (hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hkerS : Group.IsSolvable π.ker) (hK0ne : K0 Q ≠ ⊤) :
    360 ∣ Nat.card (Γ ⧸ K0 Q) := by
  letI : (K0 Q).Normal := MonoidHom.normal_ker _
  let σT : T →* alternatingGroup (Fin 6) := toA6 hT
  have hσT_surj : Function.Surjective σT := toA6_surjective hT
  have hσT_ker : σT.ker = Subgroup.center T := toA6_ker hT
  haveI : Group.IsPerfect T := Group.IsPerfect.ofSurjective hπ
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hσKnormal : (((K0 Q).map π).map σT).Normal :=
    ((MonoidHom.normal_ker _).map π hπ).map σT hσT_surj
  rcases hσKnormal.eq_bot_or_eq_top with hbot | htop
  · exact three_dvd_of_image_bot hπ σT hσT_surj hbot
  · exact absurd (K0_top_of_image_top hπ σT hσT_surj hσT_ker hkerS hK0ne htop)
      (by norm_num)

private lemma exclude_m_two {Q : Subgroup Γ} {W : Subrepresentation (ρ.comp Q.subtype)}
    {r m : ℕ} (hr : r.Prime)
    (hWsq : Module.finrank 𝕜 W.toSubmodule ^ 2 = r ^ m)
    (hWdim_le : Module.finrank 𝕜 W.toSubmodule ≤ 9)
    (h360GL : 360 ∣ Nat.card (GL (Fin m) (ZMod r)))
    (hr3ne : r ≠ 3) (h2 : m = 2) : False := by
  subst h2
  have hd_eq : Module.finrank 𝕜 W.toSubmodule = r := by
    apply Nat.pow_left_injective (n := 2) (by norm_num)
    change Module.finrank 𝕜 W.toSubmodule ^ 2 = r ^ 2
    rw [hWsq]
  have hr_le : r ≤ 9 := by
    rw [← hd_eq]
    exact hWdim_le
  letI : Fact r.Prime := ⟨hr⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod, Fin.prod_univ_two] at h360GL
  interval_cases r
  · norm_num at hr
  · norm_num at hr
  · norm_num at h360GL
  · exact absurd rfl hr3ne
  · norm_num at hr
  · norm_num at h360GL
  · norm_num at hr
  · norm_num at h360GL
  · norm_num at hr
  · norm_num at hr

private lemma r_eq_two_of_m_four {Q : Subgroup Γ}
    {W : Subrepresentation (ρ.comp Q.subtype)} {r m : ℕ} (hr : r.Prime)
    (hWsq : Module.finrank 𝕜 W.toSubmodule ^ 2 = r ^ m)
    (hWdim_le : Module.finrank 𝕜 W.toSubmodule ≤ 9)
    (hr3ne : r ≠ 3) (h4 : m = 4) : r = 2 := by
  subst h4
  have hd_eq : Module.finrank 𝕜 W.toSubmodule = r ^ 2 := by
    apply Nat.pow_left_injective (n := 2) (by norm_num)
    change Module.finrank 𝕜 W.toSubmodule ^ 2 = (r ^ 2) ^ 2
    rw [hWsq]
    ring
  have hr_le : r ^ 2 ≤ 9 := by
    rw [← hd_eq]
    exact hWdim_le
  have hr_le3 : r ≤ 3 := by nlinarith [Nat.Prime.two_le hr, hr_le]
  interval_cases r
  · norm_num at hr
  · norm_num at hr
  · rfl
  · exact absurd rfl hr3ne

private lemma r_eq_two_of_m_six {Q : Subgroup Γ}
    {W : Subrepresentation (ρ.comp Q.subtype)} {r m : ℕ} (hr : r.Prime)
    (hWsq : Module.finrank 𝕜 W.toSubmodule ^ 2 = r ^ m)
    (hWdim_le : Module.finrank 𝕜 W.toSubmodule ≤ 9)
    (h6 : m = 6) : r = 2 := by
  subst h6
  have hd_eq : Module.finrank 𝕜 W.toSubmodule = r ^ 3 := by
    apply Nat.pow_left_injective (n := 2) (by norm_num)
    change Module.finrank 𝕜 W.toSubmodule ^ 2 = (r ^ 3) ^ 2
    rw [hWsq]
    ring
  have hr_le : r ^ 3 ≤ 9 := by
    rw [← hd_eq]
    exact hWdim_le
  have hr_le2 : r ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ r := by omega
    have h27 : 3 ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left h3 3
    norm_num at h27
    omega
  have hr2 : r = 2 := by
    have := Nat.Prime.two_le hr
    omega
  exact hr2

private lemma arithmetic_final {Q : Subgroup Γ}
    {W : Subrepresentation (ρ.comp Q.subtype)} {r m : ℕ} (hr : r.Prime)
    (hWsq : Module.finrank 𝕜 W.toSubmodule ^ 2 = r ^ m)
    (hWdim_le : Module.finrank 𝕜 W.toSubmodule ≤ 9)
    (h360GL : 360 ∣ Nat.card (GL (Fin m) (ZMod r)))
    (hr3ne : r ≠ 3) (hm_cases : m = 2 ∨ m = 4 ∨ m = 6) :
    r = 2 ∧ (m = 4 ∨ m = 6) := by
  rcases hm_cases with h2 | h4 | h6
  · exact absurd (exclude_m_two hr hWsq hWdim_le h360GL hr3ne h2)
      (by norm_num)
  · subst h4
    exact ⟨r_eq_two_of_m_four hr hWsq hWdim_le hr3ne rfl, Or.inl rfl⟩
  · subst h6
    exact ⟨r_eq_two_of_m_six hr hWsq hWdim_le rfl, Or.inr rfl⟩

private lemma atMostOne_of_no_outside {Q : Subgroup Γ}
    [IsCyclic (Subgroup.center Q)]
    (hno : ∀ x : Q, x * x = 1 → x ≠ 1 → x ∈ Subgroup.center Q) :
    CFSG.ComponentClassification.AschbacherToolkit.AtMostOneInvolution Q := by
  intro x y hx hy
  have hx2 : x * x = 1 := by
    rw [← pow_two, ← hx]
    exact pow_orderOf_eq_one x
  have hy2 : y * y = 1 := by
    rw [← pow_two, ← hy]
    exact pow_orderOf_eq_one y
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    norm_num at hx
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    norm_num at hy
  have hxc : x ∈ Subgroup.center Q := hno x hx2 hx1
  have hyc : y ∈ Subgroup.center Q := hno y hy2 hy1
  have hx2c : orderOf (⟨x, hxc⟩ : Subgroup.center Q) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hx
  have hy2c : orderOf (⟨y, hyc⟩ : Subgroup.center Q) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hy
  have heq := CFSG.Semidihedral.Principal.eq_of_orderOf_eq_two_of_isCyclic hx2c hy2c
  exact congrArg (fun w : Subgroup.center Q => (w : Q)) heq

private lemma quaternion_center_card {k : ℕ} (hk2 : 2 ≤ k) :
    Nat.card (Subgroup.center (QuaternionGroup k)) = 2 := by
  haveI : NeZero k := ⟨by positivity⟩
  have hcenter_iff : ∀ g : QuaternionGroup k,
      g ∈ Subgroup.center (QuaternionGroup k) ↔
        g = QuaternionGroup.a (0 : ZMod (2 * k)) ∨
          g = QuaternionGroup.a (k : ZMod (2 * k)) := by
    intro g
    simpa using (CFSG.GroupTheory.quaternion_centralizers (m := k) hk2).2.2.1 g
  have hak_ord : orderOf (QuaternionGroup.a (k : ZMod (2 * k))) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two, QuaternionGroup.a_mul_a]
      have h : ((k : ZMod (2 * k)) + (k : ZMod (2 * k))) = 0 := by
        rw [← Nat.cast_add, show k + k = 2 * k by ring, ZMod.natCast_self]
      rw [h, QuaternionGroup.a_zero]
    · intro h
      have h0 : (k : ZMod (2 * k)) = 0 := QuaternionGroup.a.inj h
      have hdvd : 2 * k ∣ k := (ZMod.natCast_eq_zero_iff k (2 * k)).mp h0
      have hkpos : 0 < k := by positivity
      have := Nat.le_of_dvd hkpos hdvd
      omega
  have hcenter_eq : Subgroup.center (QuaternionGroup k) =
      Subgroup.zpowers (QuaternionGroup.a (k : ZMod (2 * k))) := by
    ext g
    rw [hcenter_iff g, mem_zpowers_iff_mem_range_orderOf, hak_ord]
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
    · rintro ⟨n, hn, hng⟩
      interval_cases n
      · left
        rw [pow_zero] at hng
        exact hng.symm
      · right
        rw [pow_one] at hng
        exact hng.symm
  rw [hcenter_eq, Nat.card_zpowers, hak_ord]

private lemma quaternion_a4_not_center {k : ℕ} (hk8 : 8 ≤ k) :
    QuaternionGroup.a (4 : ZMod (2 * k)) ∉
      Subgroup.center (QuaternionGroup k) := by
  have hk2 : 2 ≤ k := by omega
  have hcenter_iff : ∀ g : QuaternionGroup k,
      g ∈ Subgroup.center (QuaternionGroup k) ↔
        g = QuaternionGroup.a (0 : ZMod (2 * k)) ∨
          g = QuaternionGroup.a (k : ZMod (2 * k)) := by
    intro g
    simpa using (CFSG.GroupTheory.quaternion_centralizers (m := k) hk2).2.2.1 g
  rw [hcenter_iff]
  push Not
  constructor
  · intro h
    have h0 : (4 : ZMod (2 * k)) = 0 := QuaternionGroup.a.inj h
    have hdvd : 2 * k ∣ 4 := (ZMod.natCast_eq_zero_iff 4 (2 * k)).mp h0
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · intro h
    have hmod : 4 ≡ k [MOD 2 * k] :=
      (ZMod.natCast_eq_natCast_iff 4 k (2 * k)).mp (QuaternionGroup.a.inj h)
    have hlt : k < 2 * k := by omega
    have h4lt : 4 < 2 * k := by omega
    rw [Nat.ModEq, Nat.mod_eq_of_lt h4lt, Nat.mod_eq_of_lt hlt] at hmod
    omega

private lemma quaternion_quotient_card {Q : Subgroup Γ} {m n : ℕ}
    (e : Q ≃* QuaternionGroup (2 ^ (n - 2))) (hn3 : 3 ≤ n)
    (hm : Nat.card (Q ⧸ Subgroup.center Q) = 2 ^ m)
    (hm46 : m = 4 ∨ m = 6) :
    let k := 2 ^ (n - 2)
    Nat.card (Q ⧸ Subgroup.center Q) = 2 * k ∧ 8 ≤ k := by
  let k := 2 ^ (n - 2)
  have hk2 : 2 ≤ k := by
    dsimp [k]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
  have hcardZ : Nat.card (Subgroup.center Q) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact quaternion_center_card hk2
  have hcardQ : Nat.card Q = 4 * k := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcardQuot : Nat.card (Q ⧸ Subgroup.center Q) = 2 * k := by
    have hmul := Subgroup.card_mul_index (Subgroup.center Q)
    rw [hcardZ, hcardQ, Subgroup.index_eq_card] at hmul
    omega
  have hm4 : 4 ≤ m := by rcases hm46 with rfl | rfl <;> norm_num
  have hquot_ge : 16 ≤ Nat.card (Q ⧸ Subgroup.center Q) := by
    rw [hm]
    exact Nat.pow_le_pow_right (n := 2) (by norm_num) hm4
  exact ⟨hcardQuot, by omega⟩

private lemma quaternion_quotient_false {Q : Subgroup Γ} {m n : ℕ}
    (e : Q ≃* QuaternionGroup (2 ^ (n - 2))) (hn3 : 3 ≤ n)
    (hm : Nat.card (Q ⧸ Subgroup.center Q) = 2 ^ m)
    (hm46 : m = 4 ∨ m = 6)
    (hQquotExp : ∀ x : Q ⧸ Subgroup.center Q, x ^ 2 = 1) : False := by
  let k := 2 ^ (n - 2)
  obtain ⟨hcardQuot, hk8⟩ := quaternion_quotient_card e hn3 hm hm46
  have ha4_not_center := quaternion_a4_not_center hk8
  let eQ : (Q ⧸ Subgroup.center Q) ≃*
      (QuaternionGroup k ⧸ Subgroup.center (QuaternionGroup k)) :=
    QuotientGroup.congr (Subgroup.center Q) (Subgroup.center (QuaternionGroup k))
      e (Subgroup.map_center_eq e)
  have hmodel_exp : ∀ t : QuaternionGroup k ⧸ Subgroup.center (QuaternionGroup k),
      t ^ 2 = 1 := by
    intro t
    have h := hQquotExp (eQ.symm t)
    have h' := congrArg eQ h
    rw [map_pow, map_one] at h'
    rw [eQ.apply_symm_apply] at h'
    exact h'
  have ht2 := hmodel_exp (QuotientGroup.mk (QuaternionGroup.a (2 : ZMod (2 * k))))
  have ha2sq : (QuaternionGroup.a (2 : ZMod (2 * k))) ^ 2 =
      QuaternionGroup.a (4 : ZMod (2 * k)) := by
    rw [pow_two, QuaternionGroup.a_mul_a]
    congr 1
    norm_num
  have ht2' : (QuotientGroup.mk (QuaternionGroup.a (2 : ZMod (2 * k))) :
      QuaternionGroup k ⧸ Subgroup.center (QuaternionGroup k)) ^ 2 =
        QuotientGroup.mk (QuaternionGroup.a (4 : ZMod (2 * k))) := by
    change (QuotientGroup.mk' (Subgroup.center (QuaternionGroup k))
      (QuaternionGroup.a (2 : ZMod (2 * k)))) ^ 2 = _
    rw [← map_pow]
    exact congrArg (QuotientGroup.mk' (Subgroup.center (QuaternionGroup k))) ha2sq
  rw [ht2'] at ht2
  exact ha4_not_center ((QuotientGroup.eq_one_iff _).mp ht2)

private lemma exists_involution_outside_center {Q : Subgroup Γ} {m : ℕ}
    [IsCyclic (Subgroup.center Q)]
    (hQr : IsPGroup 2 Q) (hQc : ¬ IsMulCommutative Q)
    (hm : Nat.card (Q ⧸ Subgroup.center Q) = 2 ^ m)
    (hm46 : m = 4 ∨ m = 6)
    (hQquotExp : ∀ x : Q ⧸ Subgroup.center Q, x ^ 2 = 1) :
    ∃ x : Q, x * x = 1 ∧ x ≠ 1 ∧ x ∉ Subgroup.center Q := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  have hAtMost := atMostOne_of_no_outside hno
  rcases CFSG.Holt.isCyclic_or_quaternion_of_atMostOneInvolution hQr hAtMost with
    hcyc | ⟨n, hn3, ⟨e⟩⟩
  · exact hQc (IsCyclic.isMulCommutative (α := Q))
  · exact quaternion_quotient_false e hn3 hm hm46 hQquotExp

private lemma commutator_data {Q : Subgroup Γ} {x y : Q}
    (hcommQ : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q)
    {χQ : Subgroup.center Q →* 𝕜ˣ}
    (hχQinj : Function.Injective χQ)
    (hχQspec : ∀ z : Subgroup.center Q,
      ρ (z : Γ) = (χQ z : 𝕜) • (1 : Module.End 𝕜 V))
    (hx2 : x * x = 1) (hyx : x * y ≠ y * x) :
    ∃ hz : (⁅x, y⁆ : Q) ∈ Subgroup.center Q,
      (⁅x, y⁆ : Q) ≠ 1 ∧
      (⁅x, y⁆ : Q) * (⁅x, y⁆ : Q) = 1 ∧
      (χQ ⟨⁅x, y⁆, hz⟩ : 𝕜) = -1 ∧
      ρ ((⁅x, y⁆ : Q) : Γ) = (-1 : 𝕜) • (1 : Module.End 𝕜 V) := by
  have hz_center : (⁅x, y⁆ : Q) ∈ Subgroup.center Q := hcommQ x y
  have hz_ne_one : (⁅x, y⁆ : Q) ≠ 1 := by
    intro h
    exact hyx (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hz_comm_x : Commute x (⁅x, y⁆ : Q) :=
    Subgroup.mem_center_iff.mp hz_center x
  have hz_sq : (⁅x, y⁆ : Q) * (⁅x, y⁆ : Q) = 1 := by
    have h := hz_comm_x.commutatorElement_pow_left 2
    rw [show x ^ 2 = 1 from by simpa [pow_two] using hx2,
      commutatorElement_one_left] at h
    simpa [pow_two] using h
  have hχz_sq : (χQ ⟨⁅x, y⁆, hz_center⟩ : 𝕜) ^ 2 = 1 := by
    have h := congrArg (fun u : 𝕜ˣ => (u : 𝕜))
      (map_pow χQ ⟨⁅x, y⁆, hz_center⟩ 2)
    rw [show (⟨⁅x, y⁆, hz_center⟩ : Subgroup.center Q) ^ 2 = 1 from
      Subtype.ext (by simpa [pow_two] using hz_sq), map_one] at h
    simpa using h.symm
  have hχz_ne_one : (χQ ⟨⁅x, y⁆, hz_center⟩ : 𝕜) ≠ 1 := by
    intro h
    have hz1 : (⟨⁅x, y⁆, hz_center⟩ : Subgroup.center Q) = 1 :=
      hχQinj (Units.ext (by simpa using h))
    exact hz_ne_one (congrArg (fun w : Subgroup.center Q => (w : Q)) hz1)
  have hχz_neg : (χQ ⟨⁅x, y⁆, hz_center⟩ : 𝕜) = -1 := by
    rcases sq_eq_one_iff.mp hχz_sq with h | h
    · exact absurd h hχz_ne_one
    · exact h
  have hρz : ρ ((⁅x, y⁆ : Q) : Γ) = (-1 : 𝕜) • (1 : Module.End 𝕜 V) := by
    rw [hχQspec ⟨⁅x, y⁆, hz_center⟩, hχz_neg]
  exact ⟨hz_center, hz_ne_one, hz_sq, hχz_neg, hρz⟩

private lemma conjugate_identity {Q : Subgroup Γ} {x y : Q}
    (hcommQ : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q) :
    y⁻¹ * x * y = x * ⁅x, y⁆ := by
  have hz_center : (⁅x, y⁆ : Q) ∈ Subgroup.center Q := hcommQ x y
  have hz_comm_y : Commute y (⁅x, y⁆ : Q) :=
    Subgroup.mem_center_iff.mp hz_center y
  have h1 : y⁻¹ * x * y = ⁅y⁻¹, x⁆ * x := by
    simpa [MulAut.conj_apply] using
      (conj_eq_commutatorElement_mul (g₁ := y⁻¹) (g₂ := x))
  have h2 : ⁅y⁻¹, x⁆ = (⁅x, y⁆ : Q) := by
    rw [commutatorElement_inv_left]
    calc y⁻¹ * ⁅x, y⁆ * y = y⁻¹ * (⁅x, y⁆ * y) := by group
      _ = y⁻¹ * (y * ⁅x, y⁆) := by rw [hz_comm_y.eq]
      _ = ⁅x, y⁆ := by group
  rw [h1, h2]
  exact (Subgroup.mem_center_iff.mp hz_center x).symm

private lemma involution_eigenspace_decomp {Q : Subgroup Γ} {x : Q}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hx2 : x * x = 1) :
    IsCompl (Module.End.eigenspace (ρ (x : Γ)) 1) (Module.End.eigenspace (ρ (x : Γ)) (-1)) := by
  have hT2 : (ρ (x : Γ) : Module.End 𝕜 V) * ρ (x : Γ) = 1 := by
    rw [show (ρ (x : Γ) : Module.End 𝕜 V) * ρ (x : Γ) = ρ ((x : Γ) * (x : Γ)) by
      simp]
    rw [show (x : Γ) * (x : Γ) = 1 from by
      simpa using congrArg (fun q : Q => (q : Γ)) hx2, map_one]
  have h2 : (2 : 𝕜) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff 𝕜 p 2).mp h
    have hp2 : p ≠ 2 := by omega
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  exact CFSG.ClassicalInvolution.Models.OrthogonalPairs.isCompl_eigenspace_of_mul_self
    h2 hT2

private lemma eigenspace_conjugate_maps {Q : Subgroup Γ} {x y : Q}
    (hconj : y⁻¹ * x * y = x * ⁅x, y⁆)
    (hρz : ρ ((⁅x, y⁆ : Q) : Γ) = (-1 : 𝕜) • (1 : Module.End 𝕜 V)) :
    (∀ v ∈ Module.End.eigenspace (ρ (x : Γ)) 1,
      ρ (x : Γ) (ρ (y : Γ) v) = -ρ (y : Γ) v) ∧
    (∀ v ∈ Module.End.eigenspace (ρ (x : Γ)) (-1),
      ρ (x : Γ) (ρ (y : Γ) v) = ρ (y : Γ) v) := by
  let Tx : Module.End 𝕜 V := ρ (x : Γ)
  have hconjΓ : (y : Γ)⁻¹ * (x : Γ) * (y : Γ) =
      (x : Γ) * ((⁅x, y⁆ : Q) : Γ) := by
    simpa using congrArg (fun q : Q => (q : Γ)) hconj
  have hTconj : ρ (y : Γ)⁻¹ * Tx * ρ (y : Γ) = -Tx := by
    have h1 : ρ ((y : Γ)⁻¹ * (x : Γ) * (y : Γ)) =
        ρ ((x : Γ) * ((⁅x, y⁆ : Q) : Γ)) := by rw [hconjΓ]
    rw [map_mul, map_mul, map_mul, hρz] at h1
    have h2' : Tx * ((-1 : 𝕜) • (1 : Module.End 𝕜 V)) = -Tx := by
      rw [mul_smul_comm, mul_one]
      simp
    simpa [Tx, h2'] using h1
  have hA : ρ (y : Γ) * ρ ((y : Γ)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hTmy : Tx * ρ (y : Γ) = -ρ (y : Γ) * Tx := by
    calc Tx * ρ (y : Γ) = (ρ (y : Γ) * ρ ((y : Γ)⁻¹)) * (Tx * ρ (y : Γ)) := by
          rw [hA, one_mul]
      _ = ρ (y : Γ) * (ρ ((y : Γ)⁻¹) * (Tx * ρ (y : Γ))) := by group
      _ = ρ (y : Γ) * ((ρ ((y : Γ)⁻¹) * Tx) * ρ (y : Γ)) := by group
      _ = ρ (y : Γ) * (-Tx) := by rw [hTconj]
      _ = -(ρ (y : Γ) * Tx) := by simp
  constructor
  · intro v hv
    have hv1 : Tx v = v := by simpa using (Module.End.mem_eigenspace_iff.mp hv)
    calc Tx (ρ (y : Γ) v) = (Tx * ρ (y : Γ)) v := rfl
      _ = (-ρ (y : Γ) * Tx) v := by rw [hTmy]
      _ = -ρ (y : Γ) (Tx v) := by simp
      _ = -ρ (y : Γ) v := by rw [hv1]
  · intro v hv
    have hv1 : Tx v = -v := by simpa using (Module.End.mem_eigenspace_iff.mp hv)
    calc Tx (ρ (y : Γ) v) = (Tx * ρ (y : Γ)) v := rfl
      _ = (-ρ (y : Γ) * Tx) v := by rw [hTmy]
      _ = -ρ (y : Γ) (Tx v) := by simp
      _ = -ρ (y : Γ) (-v) := by rw [hv1]
      _ = ρ (y : Γ) v := by simp

private lemma eigenspace_finrank_eq {Q : Subgroup Γ} {x y : Q}
    (hmaps_plus : ∀ v ∈ Module.End.eigenspace (ρ (x : Γ)) 1,
      ρ (x : Γ) (ρ (y : Γ) v) = -ρ (y : Γ) v)
    (hmaps_minus : ∀ v ∈ Module.End.eigenspace (ρ (x : Γ)) (-1),
      ρ (x : Γ) (ρ (y : Γ) v) = ρ (y : Γ) v) :
    Module.finrank 𝕜 (Module.End.eigenspace (ρ (x : Γ)) 1) =
      Module.finrank 𝕜 (Module.End.eigenspace (ρ (x : Γ)) (-1)) := by
  let φ : Module.End.eigenspace (ρ (x : Γ)) 1 →ₗ[𝕜] Module.End.eigenspace (ρ (x : Γ)) (-1) :=
    { toFun := fun v => ⟨ρ (y : Γ) v, by
        rw [Module.End.mem_eigenspace_iff]
        rw [show (-1 : 𝕜) • (ρ (y : Γ) v) = -ρ (y : Γ) v from neg_one_smul 𝕜 _]
        exact hmaps_plus v v.2⟩
      map_add' := by intro a b; ext; simp
      map_smul' := by intro c a; ext; simp }
  let ψ : Module.End.eigenspace (ρ (x : Γ)) (-1) →ₗ[𝕜] Module.End.eigenspace (ρ (x : Γ)) 1 :=
    { toFun := fun v => ⟨ρ (y : Γ) v, by
        rw [Module.End.mem_eigenspace_iff]
        simpa using hmaps_minus v v.2⟩
      map_add' := by intro a b; ext; simp
      map_smul' := by intro c a; ext; simp }
  have hy_inj : Function.Injective (ρ (y : Γ) : Module.End 𝕜 V) := by
    intro a b hab
    have h := congrArg (fun v : V => ρ ((y : Γ)⁻¹) v) hab
    simpa [← Module.End.mul_apply, ← map_mul] using h
  have hφinj : Function.Injective φ := by
    intro a b hab
    exact Subtype.ext (hy_inj (by
      simpa [φ] using congrArg (fun v : Module.End.eigenspace (ρ (x : Γ)) (-1) => (v : V)) hab))
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact Subtype.ext (hy_inj (by
      simpa [ψ] using congrArg (fun v : Module.End.eigenspace (ρ (x : Γ)) 1 => (v : V)) hab))
  exact le_antisymm (LinearMap.finrank_le_finrank_of_injective hφinj)
    (LinearMap.finrank_le_finrank_of_injective hψinj)

private lemma involution_finrank_bound {Q : Subgroup Γ} {x : Q}
    (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hcompl : IsCompl (Module.End.eigenspace (ρ (x : Γ)) 1)
      (Module.End.eigenspace (ρ (x : Γ)) (-1)))
    (hdim_eq : Module.finrank 𝕜 (Module.End.eigenspace (ρ (x : Γ)) 1) =
      Module.finrank 𝕜 (Module.End.eigenspace (ρ (x : Γ)) (-1)))
    (hr3 : ∀ t : Γ, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) ≤ 3) :
    Module.finrank 𝕜 V ≤ 6 := by
  have hVdim : Module.finrank 𝕜 V =
      2 * Module.finrank 𝕜 (Module.End.eigenspace (ρ (x : Γ)) 1) := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hdim_eq] at h
    omega
  have hxΓ2 : (x : Γ) * (x : Γ) = 1 := by
    simpa using congrArg (fun q : Q => (q : Γ)) hx2
  have hxΓ1 : (x : Γ) ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext h)
  have hxP : IsPGroup 2 (Subgroup.zpowers (x : Γ)) := by
    have hord : orderOf (x : Γ) = 2 :=
      orderOf_eq_prime (by simpa [pow_two] using hxΓ2) hxΓ1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hEplus : Module.End.eigenspace (ρ (x : Γ)) 1 = LinearMap.ker (ρ (x : Γ) - 1) := by
    ext v
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    simp
  have hEplus_le3 : Module.finrank 𝕜 (Module.End.eigenspace (ρ (x : Γ)) 1) ≤ 3 := by
    rw [hEplus]
    exact hr3 (x : Γ) hxP hxΓ1
  rw [hVdim]
  omega

private lemma m_ne_six {Q : Subgroup Γ} {W : Subrepresentation (ρ.comp Q.subtype)}
    {m : ℕ} (hWsq : Module.finrank 𝕜 W.toSubmodule ^ 2 = 2 ^ m)
    (hVdim_le6 : Module.finrank 𝕜 V ≤ 6) (h6 : m = 6) : False := by
  subst h6
  have hWdim_le6 : Module.finrank 𝕜 W.toSubmodule ≤ 6 :=
    (Submodule.finrank_le W.toSubmodule).trans hVdim_le6
  have hd_eq : Module.finrank 𝕜 W.toSubmodule = 8 := by
    apply Nat.pow_left_injective (n := 2) (by norm_num)
    change Module.finrank 𝕜 W.toSubmodule ^ 2 = 8 ^ 2
    rw [hWsq]
    norm_num
  omega

private lemma m_eq_four {m : ℕ} (hm46 : m = 4 ∨ m = 6) (hm_ne6 : m ≠ 6) : m = 4 := by
  rcases hm46 with h4 | h6
  · exact h4
  · exact absurd h6 hm_ne6

private lemma W_dim_four {Q : Subgroup Γ} {W : Subrepresentation (ρ.comp Q.subtype)}
    {m : ℕ} (hWsq : Module.finrank 𝕜 W.toSubmodule ^ 2 = 2 ^ m)
    (hm4 : m = 4) : Module.finrank 𝕜 W.toSubmodule = 4 := by
  apply Nat.pow_left_injective (n := 2) (by norm_num)
  change Module.finrank 𝕜 W.toSubmodule ^ 2 = 4 ^ 2
  rw [hWsq, hm4]
  norm_num

private lemma quotient_character_faithful {Q : Subgroup Γ} [Q.Normal]
    {W : Subrepresentation (ρ.comp Q.subtype)} [Nontrivial W.toSubmodule]
    {W2 : Subrepresentation W.quotient} [Nontrivial W2.toSubmodule]
    {χQ : Subgroup.center Q →* 𝕜ˣ}
    (hχQinj : Function.Injective χQ)
    (hχQspec : ∀ z : Subgroup.center Q,
      ρ (z : Γ) = (χQ z : 𝕜) • (1 : Module.End 𝕜 V)) :
    ∀ z : Q, z ∈ Subgroup.center Q → W2.toRepresentation z = 1 → z = 1 := by
  have hquotz : ∀ (z' : Q) (hz' : z' ∈ Subgroup.center Q)
      (x : V ⧸ W.toSubmodule),
      W.quotient z' x = (χQ ⟨z', hz'⟩ : 𝕜) • x := by
    intro z' hz' t
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W.toSubmodule t
    have hv : W.toSubmodule.mkQ v = (⟦v⟧ : V ⧸ W.toSubmodule) := rfl
    rw [hv, Subrepresentation.quotient_apply_mk W z' v]
    change Submodule.Quotient.mk (ρ (z' : Γ) v) =
      (χQ ⟨z', hz'⟩ : 𝕜) • (Submodule.Quotient.mk v : V ⧸ W.toSubmodule)
    rw [hχQspec ⟨z', hz'⟩]
    simp
  intro z' hz' hz1
  obtain ⟨w, hw⟩ := exists_ne (0 : W2.toSubmodule)
  have hwQ : ((w : V ⧸ W.toSubmodule)) ≠ 0 := by
    intro h
    exact hw (Subtype.ext h)
  have h1 : (χQ ⟨z', hz'⟩ : 𝕜) • ((w : V ⧸ W.toSubmodule)) =
      (w : V ⧸ W.toSubmodule) := by
    have h2 : (W2.toRepresentation z') w = w := by
      have := congrArg (fun f : W2.toSubmodule →ₗ[𝕜] W2.toSubmodule => f w) hz1
      simpa using this
    calc (χQ ⟨z', hz'⟩ : 𝕜) • ((w : V ⧸ W.toSubmodule))
        = W.quotient z' (w : V ⧸ W.toSubmodule) :=
            (hquotz z' hz' (w : V ⧸ W.toSubmodule)).symm
      _ = ((W2.toRepresentation z') w : V ⧸ W.toSubmodule) := rfl
      _ = (w : V ⧸ W.toSubmodule) := congrArg Subtype.val h2
  have hχ' : (χQ ⟨z', hz'⟩ : 𝕜) = 1 :=
    smul_left_injective 𝕜 hwQ (by simpa using h1)
  have hz1' : (⟨z', hz'⟩ : Subgroup.center Q) = 1 :=
    hχQinj (Units.ext (by simpa using hχ'))
  exact congrArg (fun w : Subgroup.center Q => (w : Q)) hz1'

private lemma quotient_constituent_dim_four {Q : Subgroup Γ} [Q.Normal]
    {W : Subrepresentation (ρ.comp Q.subtype)} [Nontrivial W.toSubmodule]
    {χQ : Subgroup.center Q →* 𝕜ˣ} {m : ℕ}
    (hWirr : W.toRepresentation.IsIrreducible)
    (hcommQ : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q)
    (hχQinj : Function.Injective χQ)
    (hχQspec : ∀ z : Subgroup.center Q,
      ρ (z : Γ) = (χQ z : 𝕜) • (1 : Module.End 𝕜 V))
    (hm : Nat.card (Q ⧸ Subgroup.center Q) = 2 ^ m)
    (hm4 : m = 4) (hUne : W.toSubmodule ≠ ⊤) :
    ∃ W2 : Subrepresentation W.quotient, W2 ≠ ⊥ ∧
      Module.finrank 𝕜 W2.toSubmodule = 4 ∧
      Module.finrank 𝕜 W2.toSubmodule ≤
        Module.finrank 𝕜 (V ⧸ W.toSubmodule) := by
  haveI : Nontrivial (V ⧸ W.toSubmodule) :=
    Submodule.Quotient.nontrivial_iff.mpr hUne
  obtain ⟨W2, hW2ne, hW2irr⟩ :=
    CFSG.CharacterTheory.SteinbergBY.exists_isIrreducible_subrepresentation W.quotient
  haveI : Nontrivial W2.toSubmodule := by
    rw [Submodule.nontrivial_iff_ne_bot]
    intro h
    apply hW2ne
    apply Subrepresentation.toSubmodule_injective
    have hbot : (⊥ : Subrepresentation W.quotient).toSubmodule = ⊥ := by
      ext x
      change x ∈ (⊥ : Submodule 𝕜 (V ⧸ W.toSubmodule)) ↔ x = 0
      simp
    rw [hbot]
    exact h
  have hfaithW2 : ∀ z : Q, z ∈ Subgroup.center Q →
      W2.toRepresentation z = 1 → z = 1 :=
    quotient_character_faithful hχQinj hχQspec
  have hW2aux := card_quotient_center_eq_finrank_sq
    W2.toRepresentation hW2irr hcommQ hfaithW2
  have hQcard16 : Nat.card (Q ⧸ Subgroup.center Q) = 16 := by
    rw [hm, hm4]
    norm_num
  have hW2dim4 : Module.finrank 𝕜 W2.toSubmodule = 4 := by
    apply Nat.pow_left_injective (n := 2) (by norm_num)
    change Module.finrank 𝕜 W2.toSubmodule ^ 2 = 4 ^ 2
    rw [← hW2aux, hQcard16]
  exact ⟨W2, hW2ne, hW2dim4, Submodule.finrank_le _⟩

private lemma no_proper_quotient_constituent {Q : Subgroup Γ}
    {W : Subrepresentation (ρ.comp Q.subtype)} {W2 : Subrepresentation W.quotient}
    (hWdim4 : Module.finrank 𝕜 W.toSubmodule = 4)
    (hVdim_le6 : Module.finrank 𝕜 V ≤ 6)
    (hW2dim4 : Module.finrank 𝕜 W2.toSubmodule = 4)
    (hW2le : Module.finrank 𝕜 W2.toSubmodule ≤
      Module.finrank 𝕜 (V ⧸ W.toSubmodule)) : False := by
  have hquotdim : Module.finrank 𝕜 (V ⧸ W.toSubmodule) =
      Module.finrank 𝕜 V - Module.finrank 𝕜 W.toSubmodule := by
    have h := Submodule.finrank_quotient_add_finrank W.toSubmodule
    omega
  have hle : Module.finrank 𝕜 (V ⧸ W.toSubmodule) ≤ 2 := by
    rw [hquotdim, hWdim4]
    omega
  omega

private lemma V_eq_W {Q : Subgroup Γ} [Q.Normal]
    {W : Subrepresentation (ρ.comp Q.subtype)} [Nontrivial W.toSubmodule]
    {χQ : Subgroup.center Q →* 𝕜ˣ} {m : ℕ}
    (hWirr : W.toRepresentation.IsIrreducible)
    (hcommQ : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q)
    (hχQinj : Function.Injective χQ)
    (hχQspec : ∀ z : Subgroup.center Q,
      ρ (z : Γ) = (χQ z : 𝕜) • (1 : Module.End 𝕜 V))
    (hm : Nat.card (Q ⧸ Subgroup.center Q) = 2 ^ m)
    (hm4 : m = 4) (hWdim4 : Module.finrank 𝕜 W.toSubmodule = 4)
    (hVdim_le6 : Module.finrank 𝕜 V ≤ 6) :
    W.toSubmodule = ⊤ := by
  by_contra hUne
  obtain ⟨W2, _, hW2dim4, hW2le⟩ :=
    quotient_constituent_dim_four hWirr hcommQ hχQinj hχQspec hm hm4 hUne
  exact no_proper_quotient_constituent hWdim4 hVdim_le6 hW2dim4 hW2le

private lemma V_dim_four {Q : Subgroup Γ} {W : Subrepresentation (ρ.comp Q.subtype)}
    (hWdim4 : Module.finrank 𝕜 W.toSubmodule = 4)
    (hWtop : W.toSubmodule = ⊤) : Module.finrank 𝕜 V = 4 := by
  calc Module.finrank 𝕜 V = Module.finrank 𝕜 (⊤ : Submodule 𝕜 V) :=
        (finrank_top 𝕜 V).symm
    _ = Module.finrank 𝕜 W.toSubmodule := by rw [← hWtop]
    _ = 4 := hWdim4

private lemma centralizer_scalar {Q : Subgroup Γ} [Q.Normal]
    {W : Subrepresentation (ρ.comp Q.subtype)} [Nontrivial W.toSubmodule]
    (hWtop : W.toSubmodule = ⊤)
    (hWirr : W.toRepresentation.IsIrreducible) :
    ∀ g ∈ centralizerQ Q, ∃ μ : 𝕜, ρ g = μ • (1 : Module.End 𝕜 V) := by
  intro g hg
  let B : Module.End 𝕜 W.toSubmodule :=
    { toFun := fun w => ⟨ρ g w, by simp [hWtop]⟩
      map_add' := by intro a b; ext; simp
      map_smul' := by intro c a; ext; simp }
  have hB : ∀ q : Q, B * W.toRepresentation q = W.toRepresentation q * B := by
    intro q
    ext w
    simp only [B, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk]
    have hcomm : g * (q : Γ) = (q : Γ) * g :=
      (Subgroup.mem_centralizer_iff.mp hg (q : Γ) q.2).symm
    calc ρ g (ρ (q : Γ) w) = ρ (g * (q : Γ)) w := by rw [map_mul]; rfl
      _ = ρ ((q : Γ) * g) w := by rw [hcomm]
      _ = ρ (q : Γ) (ρ g w) := by rw [map_mul]; rfl
  obtain ⟨μ, hμ⟩ := CFSG.GroupTheory.HallHigmanB.eq_smul_one_of_commute_irreducible
    W.toRepresentation.asGroupHom
    (fun W1 hW1 => CFSG.RankThree.GroupTheory.eq_bot_or_eq_top_of_isIrreducible hWirr W1 hW1)
    B hB
  refine ⟨μ, ?_⟩
  ext v
  have h := congrArg (fun w : W.toSubmodule => (w : V))
    (LinearMap.congr_fun hμ ⟨v, by simp [hWtop]⟩)
  simpa [B] using h

private lemma centralizer_is_two_group {Q : Subgroup Γ} [Q.Normal] [Group.IsPerfect Γ]
    (hfaith : Function.Injective ρ) (hVdim4 : Module.finrank 𝕜 V = 4)
    (hC_scalar : ∀ g ∈ centralizerQ Q,
      ∃ μ : 𝕜, ρ g = μ • (1 : Module.End 𝕜 V)) :
    IsPGroup 2 (centralizerQ Q) := by
  rw [isPGroup_iff_exists_orderOf_dvd_pow]
  refine ⟨2, ?_⟩
  intro g
  obtain ⟨μ, hμ⟩ := hC_scalar g g.2
  let D : Γ →* 𝕜ˣ := ((LinearMap.det : Module.End 𝕜 V →* 𝕜).comp ρ).toHomUnits
  have hDg : D (g : Γ) = 1 :=
    CFSG.CGT.PushingUpLit.CGT6.Diag.Ident.perfect_hom_one D (g : Γ)
  have hdet : LinearMap.det (ρ (g : Γ)) = 1 := by
    have hval : ((D (g : Γ) : 𝕜ˣ) : 𝕜) = 1 := by rw [hDg]; rfl
    simpa [D] using hval
  have hμ4 : μ ^ 4 = 1 := by
    rw [hμ, LinearMap.det_smul, map_one, hVdim4, mul_one] at hdet
    exact hdet
  have hg4 : (g : Γ) ^ 4 = 1 := by
    apply hfaith
    rw [map_pow, hμ]
    rw [show (μ • (1 : Module.End 𝕜 V)) ^ 4 =
        μ ^ 4 • (1 : Module.End 𝕜 V) by rw [smul_pow, one_pow]]
    rw [hμ4, one_smul, map_one]
  rw [Subgroup.orderOf_mk]
  exact orderOf_dvd_iff_pow_eq_one.mpr hg4

private lemma K0_comm {Q : Subgroup Γ} [Q.Normal] :
    ∀ g ∈ K0 Q, ∀ x : Q, (⁅g, (x : Γ)⁆ : Γ) ∈ centerMap Q := by
  intro g hgK x
  have hψg : conjOnQuotient Q g = 1 := MonoidHom.mem_ker.mp hgK
  have h1 : (MulAut.mapQuotient (Subgroup.center Q) (MulAut.conjNormal g))
      (QuotientGroup.mk x) = QuotientGroup.mk x := by
    have := congrArg (fun f : MulAut (Q ⧸ Subgroup.center Q) =>
      f (QuotientGroup.mk x)) hψg
    simpa [conjOnQuotient] using this
  rw [MulAut.mapQuotient_mk] at h1
  have h2 : (MulAut.conjNormal g x) / x ∈ Subgroup.center Q :=
    QuotientGroup.eq_iff_div_mem.mp h1
  have h3 : (⁅g, (x : Γ)⁆ : Γ) = ((((MulAut.conjNormal g x) / x : Q) : Γ)) := by
    simp [MulAut.conjNormal_apply, div_eq_mul_inv, commutatorElement_def]
  rw [h3]
  exact Subgroup.mem_map.mpr ⟨_, h2, rfl⟩

private lemma K0_odd_central {Q : Subgroup Γ} [Q.Normal]
    (hQr : IsPGroup 2 Q)
    (hZcenter : centerMap Q ≤ Subgroup.center Γ)
    (hZle : centerMap Q ≤ Q) :
    ∀ g ∈ K0 Q, Odd (orderOf g) → g ∈ centralizerQ Q := by
  intro g hgK hodd
  rw [Subgroup.mem_centralizer_iff]
  intro x hxQ
  let xQ : Q := ⟨x, hxQ⟩
  have hzZ := K0_comm g hgK xQ
  have hzQ : (⁅g, (xQ : Γ)⁆ : Γ) ∈ Q := hZle hzZ
  let zQ : Q := ⟨⁅g, (xQ : Γ)⁆, hzQ⟩
  have hz_center_Γ : (⁅g, (xQ : Γ)⁆ : Γ) ∈ Subgroup.center Γ := hZcenter hzZ
  have hz_comm : Commute g (⁅g, (xQ : Γ)⁆ : Γ) :=
    Subgroup.mem_center_iff.mp hz_center_Γ g
  have hz_pow : (⁅g, (xQ : Γ)⁆ : Γ) ^ orderOf g = 1 := by
    rw [hz_comm.commutatorElement_pow_left, pow_orderOf_eq_one, commutatorElement_one_left]
  have hdvd1 : orderOf (⁅g, (xQ : Γ)⁆ : Γ) ∣ orderOf g :=
    orderOf_dvd_of_pow_eq_one hz_pow
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQr zQ
  have hk' : orderOf (⁅g, (xQ : Γ)⁆ : Γ) = 2 ^ k := by
    change orderOf (zQ : Γ) = 2 ^ k
    exact (Subgroup.orderOf_mk (zQ : Γ) zQ.2).symm.trans hk
  have hcop : Nat.Coprime (2 ^ k) (orderOf g) :=
    (Nat.coprime_two_left.mpr hodd).pow_left k
  have hdvd : orderOf (⁅g, (xQ : Γ)⁆ : Γ) ∣ Nat.gcd (2 ^ k) (orderOf g) :=
    Nat.dvd_gcd (by rw [hk']) hdvd1
  rw [hcop.gcd_eq_one] at hdvd
  have hz1 : (⁅g, (xQ : Γ)⁆ : Γ) = 1 :=
    orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hz1).symm

private lemma K0_is_two_group {Q : Subgroup Γ} [Q.Normal]
    (hQr : IsPGroup 2 Q)
    (hZcenter : centerMap Q ≤ Subgroup.center Γ)
    (hZle : centerMap Q ≤ Q)
    (hC2 : IsPGroup 2 (centralizerQ Q)) :
    IsPGroup 2 (K0 Q) := by
  rw [IsPGroup.iff_orderOf]
  intro g
  rw [Subgroup.orderOf_mk]
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (orderOf (g : Γ)) with
    ⟨k, hk⟩ | ⟨p, hp, hpd, hpo⟩
  · exact ⟨k, hk⟩
  · exfalso
    have hpdK : p ∣ orderOf g := by
      rwa [Subgroup.orderOf_mk]
    let eK : K0 Q := g ^ (orderOf g / p)
    have heo : orderOf eK = p :=
      orderOf_pow_orderOf_div (orderOf_pos g).ne' hpdK
    have heKmem : (eK : Γ) ∈ K0 Q := eK.property
    have hCe : (eK : Γ) ∈ centralizerQ Q :=
      K0_odd_central hQr hZcenter hZle (g := (eK : Γ)) heKmem (by
        rw [← Subgroup.orderOf_mk (eK : Γ) heKmem, heo]
        exact hpo)
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hC2 ⟨eK, hCe⟩
    have hm' : orderOf eK = 2 ^ m := by
      simpa [Subgroup.orderOf_mk] using hm
    have hpm : p = 2 ^ m := by rw [← heo, hm']
    cases m with
    | zero =>
        have hp1 : p = 1 := by simpa using hpm
        exact hp.ne_one hp1
    | succ m =>
        have h2dvd : 2 ∣ p := by
          rw [hpm]
          exact dvd_pow_self 2 (Nat.succ_ne_zero m)
        exact hpo.not_two_dvd_nat h2dvd

private lemma K0_le_ker_of_map_bot {Q : Subgroup Γ} [Q.Normal] {π : Γ →* T}
    (hbot : (K0 Q).map π = ⊥) : K0 Q ≤ π.ker := by
  intro g hg
  have hmem : π g ∈ (K0 Q).map π := ⟨g, hg, rfl⟩
  rw [hbot] at hmem
  simpa using hmem

private lemma pi_K0_bot {Q : Subgroup Γ} [Q.Normal] [Group.IsPerfect Γ]
    {π : Γ →* T} (hπ : Function.Surjective π)
    (hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hK0_2 : IsPGroup 2 (K0 Q)) : (K0 Q).map π = ⊥ := by
  letI : (K0 Q).Normal := MonoidHom.normal_ker _
  letI : Finite T := Finite.of_surjective π hπ
  have hπK02 : IsPGroup 2 ((K0 Q).map π) := hK0_2.map π
  have hπK0not3 : ¬ 3 ∣ Nat.card ((K0 Q).map π) := by
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq (p := 2) hπK02
    rw [hn]
    intro h3
    have h32 : (3 : ℕ) ∣ 2 :=
      Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3
    norm_num at h32
  haveI : ((K0 Q).map π).Normal := (MonoidHom.normal_ker _).map π hπ
  haveI : Group.IsPerfect T := Group.IsPerfect.ofSurjective hπ
  exact CFSG.RankThree.PartTwo.Sec16.ThetaCompY.eq_bot_of_normal_of_not_three_dvd hT hπK0not3

private lemma T_card {T : Type*} [Group T]
    (hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover T (alternatingGroup (Fin 6))) :
    Nat.card T = 1080 := by
  obtain ⟨hcenter, ⟨eA⟩⟩ := hT
  have hmul := Subgroup.card_mul_index (Subgroup.center T)
  rw [hcenter, Subgroup.index_eq_card] at hmul
  have hquot : Nat.card (T ⧸ Subgroup.center T) = 360 := by
    rw [Nat.card_congr eA.toEquiv, card_alternating_six]
  rw [hquot] at hmul
  omega

private lemma final_contradiction {Q : Subgroup Γ} [Q.Normal] {π : Γ →* T}
    (hπ : Function.Surjective π)
    (hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hK0_le_ker : K0 Q ≤ π.ker)
    (hGLdvd : Nat.card (Γ ⧸ K0 Q) ∣ Nat.card (GL (Fin 4) (ZMod 2))) : False := by
  letI : (K0 Q).Normal := MonoidHom.normal_ker _
  have hK0index_dvd : Nat.card T ∣ Nat.card (Γ ⧸ K0 Q) := by
    have h := Subgroup.index_dvd_of_le hK0_le_ker
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card] at h
    have hkerquot : Nat.card (Γ ⧸ π.ker) = Nat.card T :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv
    rwa [hkerquot] at h
  have h1080 : 1080 ∣ Nat.card (Γ ⧸ K0 Q) := by
    rwa [T_card hT] at hK0index_dvd
  have h20160 : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
    rw [CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2), Fin.prod_univ_four]
    norm_num
  have hK0dvd20160 : Nat.card (Γ ⧸ K0 Q) ∣ 20160 := by
    rwa [h20160] at hGLdvd
  have : 1080 ∣ 20160 := Nat.dvd_trans h1080 hK0dvd20160
  norm_num at this

private structure Stage1 (𝕜 : Type*) [Field 𝕜] [IsAlgClosed 𝕜]
    (p : ℕ) [CharP 𝕜 p] (Γ : Type*) [Group Γ] [Finite Γ]
    (V : Type*) [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 Γ V) (Q : Subgroup Γ) (r : ℕ) where
  m : ℕ
  W : Subrepresentation (ρ.comp Q.subtype)
  hWirr : W.toRepresentation.IsIrreducible
  χQ : Subgroup.center Q →* 𝕜ˣ
  hχQinj : Function.Injective χQ
  hχQspec : ∀ z : Subgroup.center Q,
    ρ (z : Γ) = (χQ z : 𝕜) • (1 : Module.End 𝕜 V)
  hm : Nat.card (Q ⧸ Subgroup.center Q) = r ^ m
  hWsq : Module.finrank 𝕜 W.toSubmodule ^ 2 = r ^ m
  hm_cases : m = 2 ∨ m = 4 ∨ m = 6
  hrp : r ≠ p
  hr3ne : r ≠ 3
  hZcenter : centerMap Q ≤ Subgroup.center Γ
  hQ0center : frattiniMap Q ≤ Subgroup.center Γ
  hcommQ : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q
  hQquotElem : CFSG.IsElementaryAbelian r (Q ⧸ Subgroup.center Q)
  hZcyc : IsCyclic (Subgroup.center Q)

private structure Stage2 (𝕜 : Type*) [Field 𝕜] [IsAlgClosed 𝕜]
    (p : ℕ) [CharP 𝕜 p] (Γ : Type*) [Group Γ] [Finite Γ]
    (V : Type*) [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 Γ V) (Q : Subgroup Γ) [Q.Normal] (r : ℕ)
    (S : Stage1 𝕜 p Γ V ρ Q r) where
  hr2 : r = 2
  hm46 : S.m = 4 ∨ S.m = 6
  hGLdvd : Nat.card (Γ ⧸ K0 Q) ∣ Nat.card (GL (Fin S.m) (ZMod r))

private structure Stage1Core (𝕜 : Type*) [Field 𝕜] [IsAlgClosed 𝕜]
    (p : ℕ) [CharP 𝕜 p] (Γ : Type*) [Group Γ] [Finite Γ]
    (Q : Subgroup Γ) (r : ℕ) where
  hrp : r ≠ p
  hr3ne : r ≠ 3
  hZcenter : centerMap Q ≤ Subgroup.center Γ
  hQ0center : frattiniMap Q ≤ Subgroup.center Γ
  hcommQ : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q
  hQquotElem : CFSG.IsElementaryAbelian r (Q ⧸ Subgroup.center Q)

private lemma stage1a {Q : Subgroup Γ} {r : ℕ} {π : Γ →* T}
    (hp : p.Prime) (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    (hr : r.Prime) (hQn : Q.Normal) (hQD : Q ≤ π.ker)
    (hQr : IsPGroup r Q) (hQc : ¬ IsMulCommutative Q)
    (hker3 : Nat.Coprime (Nat.card π.ker) 3)
    (hmin : ∀ R : Subgroup Γ, R.Normal → R < Q → R ≤ Subgroup.center Γ) :
    Stage1Core 𝕜 p Γ Q r := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact r.Prime := ⟨hr⟩
  haveI : Q.Normal := hQn
  haveI : Fact (IsPGroup r Q) := ⟨hQr⟩
  have hQnontrivial : Nontrivial Q := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hQc ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  have hrp : r ≠ p := fun hrp => r_ne_p hp hirr hfaith hQr hQc hrp
  have hr3ne : r ≠ 3 := fun hr3 => r_ne_three hQr hQD hker3 hr3
  have hZcenter : centerMap Q ≤ Subgroup.center Γ := centerMap_central hQc hmin
  have hQ0center : frattiniMap Q ≤ Subgroup.center Γ := frattiniMap_central hmin
  have hcommQ : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q :=
    commutator_mem_center hr hQr hQ0center
  have hpowQ : ∀ x : Q, x ^ r ∈ Subgroup.center Q :=
    pow_mem_center hr hQr hQ0center
  have hQquotElem : CFSG.IsElementaryAbelian r (Q ⧸ Subgroup.center Q) :=
    quotient_elementary hr hcommQ hpowQ
  exact { hrp := hrp, hr3ne := hr3ne, hZcenter := hZcenter, hQ0center := hQ0center
          hcommQ := hcommQ, hQquotElem := hQquotElem }

private noncomputable def stage1b {Q : Subgroup Γ} [Q.Normal] {r : ℕ}
    {C : Stage1Core 𝕜 p Γ Q r} (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    (hdim : Module.finrank 𝕜 V ≤ 9) (hr : r.Prime) (hQr : IsPGroup r Q)
    (hQc : ¬ IsMulCommutative Q) : Stage1 𝕜 p Γ V ρ Q r := by
  classical
  letI : Fact r.Prime := ⟨hr⟩
  haveI : Nontrivial V := CFSG.RankThree.GroupTheory.nontrivial_of_isIrreducible hirr
  let m := Classical.choose ((hQr.to_quotient (Subgroup.center Q)).exists_card_eq)
  have hm := Classical.choose_spec ((hQr.to_quotient (Subgroup.center Q)).exists_card_eq)
  let W := Classical.choose
    (CFSG.CharacterTheory.SteinbergBY.exists_isIrreducible_subrepresentation (ρ.comp Q.subtype))
  obtain ⟨hWne, hWirr⟩ := Classical.choose_spec
    (CFSG.CharacterTheory.SteinbergBY.exists_isIrreducible_subrepresentation (ρ.comp Q.subtype))
  haveI : Nontrivial W.toSubmodule :=
    CFSG.RankThree.GroupTheory.nontrivial_of_isIrreducible hWirr
  let χQ := Classical.choose (exists_center_character C.hZcenter hfaith hirr)
  obtain ⟨hχQinj, hχQspec⟩ := Classical.choose_spec
    (exists_center_character C.hZcenter hfaith hirr)
  have hfaithW : ∀ z ∈ Subgroup.center Q, W.toRepresentation z = 1 → z = 1 :=
    center_action_faithful hχQinj hχQspec
  have hWfaith : Function.Injective W.toRepresentation :=
    injective_of_commutator_mem_center W.toRepresentation C.hcommQ hfaithW
  haveI hZcyc : IsCyclic (Subgroup.center Q) :=
    CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreducibleFiniteCenterCyclic.cyclic_center
      W.toRepresentation hWfaith hWirr
  have hWaux := card_quotient_center_eq_finrank_sq W.toRepresentation hWirr C.hcommQ hfaithW
  have hWsq : Module.finrank 𝕜 W.toSubmodule ^ 2 = r ^ m := by
    rw [← hWaux, hm]
  have hWdim_le : Module.finrank 𝕜 W.toSubmodule ≤ 9 :=
    (Submodule.finrank_le W.toSubmodule).trans hdim
  obtain ⟨hm_le, hm_pos, hm_even⟩ := m_bounds hr hQc hm hWsq hWdim_le
  have hm_cases : m = 2 ∨ m = 4 ∨ m = 6 := by
    obtain ⟨k, hk⟩ := hm_even
    omega
  exact { m := m, W := W, hWirr := hWirr, χQ := χQ, hχQinj := hχQinj
          hχQspec := hχQspec, hm := hm, hWsq := hWsq, hm_cases := hm_cases
          hrp := C.hrp, hr3ne := C.hr3ne, hZcenter := C.hZcenter
          hQ0center := C.hQ0center, hcommQ := C.hcommQ, hQquotElem := C.hQquotElem
          hZcyc := hZcyc }

private noncomputable def stage1 {Q : Subgroup Γ} {r : ℕ} {π : Γ →* T}
    (hp : p.Prime) (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    (hdim : Module.finrank 𝕜 V ≤ 9) (hr : r.Prime) (hQn : Q.Normal) (hQD : Q ≤ π.ker)
    (hQr : IsPGroup r Q) (hQc : ¬ IsMulCommutative Q)
    (hker3 : Nat.Coprime (Nat.card π.ker) 3)
    (hmin : ∀ R : Subgroup Γ, R.Normal → R < Q → R ≤ Subgroup.center Γ) :
    Stage1 𝕜 p Γ V ρ Q r :=
  stage1b (C := stage1a (π := π) hp hirr hfaith hr hQn hQD hQr hQc hker3 hmin)
    hirr hfaith hdim hr hQr hQc

private lemma stage2 {Q : Subgroup Γ} [Q.Normal] {r : ℕ} {π : Γ →* T}
    {S : Stage1 𝕜 p Γ V ρ Q r}
    (hperf : Group.IsPerfect Γ) (hr : r.Prime) (hQc : ¬ IsMulCommutative Q)
    (hπ : Function.Surjective π)
    (hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hkerS : Group.IsSolvable π.ker) (hdim : Module.finrank 𝕜 V ≤ 9) :
    Stage2 𝕜 p Γ V ρ Q r S := by
  haveI : Group.IsPerfect Γ := hperf
  have hQquotComm : IsMulCommutative (Q ⧸ Subgroup.center Q) :=
    S.hQquotElem.toIsMulCommutative
  have hQquotExp : ∀ x : Q ⧸ Subgroup.center Q, x ^ r = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp S.hQquotElem.exponent_dvd_p x
  have hK0ne : K0 Q ≠ ⊤ := K0_ne_top S.hZcenter hQc hperf
  have hGLdvd : Nat.card (Γ ⧸ K0 Q) ∣ Nat.card (GL (Fin S.m) (ZMod r)) :=
    K0_GL_dvd hr hQquotComm hQquotExp S.hm
  have h360 : 360 ∣ Nat.card (Γ ⧸ K0 Q) :=
    three_dvd_card_quotient hπ hT hkerS hK0ne
  have h360GL : 360 ∣ Nat.card (GL (Fin S.m) (ZMod r)) := h360.trans hGLdvd
  have hWdim_le : Module.finrank 𝕜 S.W.toSubmodule ≤ 9 :=
    (Submodule.finrank_le S.W.toSubmodule).trans hdim
  obtain ⟨hr2, hm46⟩ :=
    arithmetic_final hr S.hWsq hWdim_le h360GL S.hr3ne S.hm_cases
  exact ⟨hr2, hm46, hGLdvd⟩

private structure Stage3Data (𝕜 : Type*) [Field 𝕜] [IsAlgClosed 𝕜]
    (p : ℕ) [CharP 𝕜 p] (Γ : Type*) [Group Γ] [Finite Γ]
    (V : Type*) [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 Γ V) (Q : Subgroup Γ) [Q.Normal]
    (S : Stage1 𝕜 p Γ V ρ Q 2) where
  hm4 : S.m = 4
  hWtop : S.W.toSubmodule = ⊤
  hVdim4 : Module.finrank 𝕜 V = 4

private lemma stage3a {Q : Subgroup Γ} [Q.Normal]
    (S : Stage1 𝕜 p Γ V ρ Q 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hQr : IsPGroup 2 Q)
    (hQc : ¬ IsMulCommutative Q) (hm46 : S.m = 4 ∨ S.m = 6)
    (hr3 : ∀ t : Γ, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) ≤ 3) :
    Stage3Data 𝕜 p Γ V ρ Q S := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (Subgroup.center Q) := S.hZcyc
  haveI : Nontrivial S.W.toSubmodule :=
    CFSG.RankThree.GroupTheory.nontrivial_of_isIrreducible S.hWirr
  have hQquotExp : ∀ x : Q ⧸ Subgroup.center Q, x ^ 2 = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp S.hQquotElem.exponent_dvd_p x
  obtain ⟨x, hx2, hx1, hxZ⟩ :=
    exists_involution_outside_center hQr hQc S.hm hm46 hQquotExp
  obtain ⟨y, hyx⟩ : ∃ y : Q, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact hxZ (Subgroup.mem_center_iff.mpr fun y => (h y).symm)
  obtain ⟨-, -, -, -, hρz⟩ := commutator_data S.hcommQ S.hχQinj S.hχQspec hx2 hyx
  have hcompl : IsCompl (Module.End.eigenspace (ρ (x : Γ)) 1)
      (Module.End.eigenspace (ρ (x : Γ)) (-1)) := involution_eigenspace_decomp hp hp5 hx2
  obtain ⟨hmaps_plus, hmaps_minus⟩ :=
    eigenspace_conjugate_maps (conjugate_identity S.hcommQ) hρz
  have hdim_eq : Module.finrank 𝕜 (Module.End.eigenspace (ρ (x : Γ)) 1) =
      Module.finrank 𝕜 (Module.End.eigenspace (ρ (x : Γ)) (-1)) :=
    eigenspace_finrank_eq hmaps_plus hmaps_minus
  have hVdim_le6 : Module.finrank 𝕜 V ≤ 6 :=
    involution_finrank_bound hx2 hx1 hcompl hdim_eq hr3
  have hm4 : S.m = 4 :=
    m_eq_four hm46 (fun h6 => m_ne_six S.hWsq hVdim_le6 h6)
  have hVeqW : S.W.toSubmodule = ⊤ :=
    V_eq_W S.hWirr S.hcommQ S.hχQinj S.hχQspec S.hm hm4
      (W_dim_four S.hWsq hm4) hVdim_le6
  exact ⟨hm4, hVeqW, V_dim_four (W_dim_four S.hWsq hm4) hVeqW⟩

private lemma stage3b {Q : Subgroup Γ} [Q.Normal] [Group.IsPerfect Γ]
    (S : Stage1 𝕜 p Γ V ρ Q 2) (D : Stage3Data 𝕜 p Γ V ρ Q S) {π : Γ →* T}
    (hQr : IsPGroup 2 Q) (hfaith : Function.Injective ρ)
    (hGLdvd : Nat.card (Γ ⧸ K0 Q) ∣ Nat.card (GL (Fin S.m) (ZMod 2)))
    (hπ : Function.Surjective π)
    (hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hkerS : Group.IsSolvable π.ker) : False := by
  haveI : Nontrivial S.W.toSubmodule :=
    CFSG.RankThree.GroupTheory.nontrivial_of_isIrreducible S.hWirr
  have hC_scalar : ∀ g ∈ centralizerQ Q, ∃ μ : 𝕜,
      ρ g = μ • (1 : Module.End 𝕜 V) := centralizer_scalar D.hWtop S.hWirr
  have hK02 : IsPGroup 2 (K0 Q) :=
    K0_is_two_group hQr S.hZcenter (Subgroup.map_subtype_le _)
      (centralizer_is_two_group hfaith D.hVdim4 hC_scalar)
  have hK0_le_ker : K0 Q ≤ π.ker :=
    K0_le_ker_of_map_bot (pi_K0_bot hπ hT hK02)
  rw [D.hm4] at hGLdvd
  exact final_contradiction hπ hT hK0_le_ker hGLdvd

private lemma stage3 {Q : Subgroup Γ} [Q.Normal] [Group.IsPerfect Γ]
    (S : Stage1 𝕜 p Γ V ρ Q 2) {π : Γ →* T}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hQr : IsPGroup 2 Q)
    (hQc : ¬ IsMulCommutative Q) (hm46 : S.m = 4 ∨ S.m = 6)
    (hGLdvd : Nat.card (Γ ⧸ K0 Q) ∣ Nat.card (GL (Fin S.m) (ZMod 2)))
    (hfaith : Function.Injective ρ)
    (hr3 : ∀ t : Γ, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) ≤ 3)
    (hπ : Function.Surjective π)
    (hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hkerS : Group.IsSolvable π.ker) : False :=
  stage3b S (stage3a S hp hp5 hQr hQc hm46 hr3) hQr hfaith hGLdvd hπ hT hkerS

end MainProof

theorem false_of_nonabelian_minimal {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜] {p : ℕ} [CharP 𝕜 p]
    (hp : p.Prime) (hp5 : 5 ≤ p)
    {Γ : Type*} [Group Γ] [Finite Γ] (hperf : Group.IsPerfect Γ)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 Γ V) (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    (hdim : Module.finrank 𝕜 V ≤ 9)
    {T : Type*} [Group T] (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hker3 : Nat.Coprime (Nat.card π.ker) 3) (hkerS : Group.IsSolvable π.ker)
    (hr3 : ∀ t : Γ, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) ≤ 3)
    {r : ℕ} (hr : r.Prime) {Q : Subgroup Γ} (hQn : Q.Normal) (hQD : Q ≤ π.ker)
    (hQr : IsPGroup r Q) (hQc : ¬ IsMulCommutative Q)
    (hmin : ∀ R : Subgroup Γ, R.Normal → R < Q → R ≤ Subgroup.center Γ) : False := by
  classical
  haveI : Q.Normal := hQn
  haveI : Group.IsPerfect Γ := hperf
  let S := stage1 (π := π) hp hirr hfaith hdim hr hQn hQD hQr hQc hker3 hmin
  have h2 := stage2 (S := S) hperf hr hQc hπ hT hkerS hdim
  obtain ⟨hr2, hm46, hGLdvd⟩ := h2
  subst hr2
  exact stage3 S hp hp5 hQr hQc hm46 hGLdvd hfaith hr3 hπ hT hkerS

end CFSG.RankThree.PartTwo.Sec16.Kcd166




