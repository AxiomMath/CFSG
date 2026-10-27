module

public import CFSG.Quasithin.Background.C118BridgeTwo
public import CFSG.Quasithin.Background.C118NoOuterAct

public section

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement

section Prelim

variable {Ω : Type} [Group Ω] {B H : Subgroup Ω} {n : ℕ}

theorem C118NatData.alpha_surjective (d : C118NatData B H n) (hn : 2 ≤ n) : Function.Surjective d.α := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchp : CharP d.F 2 := charP_of_card_eq_prime_pow d.hcard
  have hfin : Finite d.F := Finite.of_fintype d.F
  have h4 : ∃ s : Finset d.F, s.card = 4 := by
    have h4' : 4 ≤ (Finset.univ : Finset d.F).card := by
      rw [Finset.card_univ, d.hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4'
    exact ⟨t, ht⟩
  have htop : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) d.F)) ≠ ⊥ := by
    intro h
    apply not_commutative_sl2 (F := d.F)
    intro a b
    have ha : a = 1 := Subgroup.mem_bot.mp (h ▸ Subgroup.mem_top a)
    have hb : b = 1 := Subgroup.mem_bot.mp (h ▸ Subgroup.mem_top b)
    rw [ha, hb]
  have hcomm : commutator (Matrix.SpecialLinearGroup (Fin 2) d.F) = ⊤ :=
    commutator_top_sl2_eq_top h4 ⊤ htop
  apply MonoidHom.range_eq_top.mp
  rw [d.hα_range, hcomm]

theorem C118NatData.not_le_centralizer (d : C118NatData B H n) (hαs : Function.Surjective d.α) :
    ¬ H ≤ Subgroup.centralizer (clV B H : Set Ω) := by
  intro hle
  apply not_commutative_sl2 (F := d.F)
  intro a b
  have h1 : ∀ k : ↥(clK B H), d.α k = 1 := fun k => by
    have : k ∈ d.α.ker := by
      rw [d.hα_ker, Subgroup.mem_subgroupOf]
      exact hle (clK_le B H k.2)
    exact this
  obtain ⟨ka, rfl⟩ := hαs a
  obtain ⟨kb, rfl⟩ := hαs b
  rw [h1 ka, h1 kb]

end Prelim

section Thompson

variable {Ω : Type} [Group Ω] [Finite Ω] {B H M : Subgroup Ω}

theorem not_commutator_thompsonJ_eq_bot (hB : IsSylowTwoOf B H) (hchar : CharTwo H)
    (hMP : MinParabolic H B M) (hbaum : baum B = B)
    (hHV : ¬ H ≤ Subgroup.centralizer (clV B H : Set Ω)) : ⁅clV B H, thompsonJ B⁆ ≠ ⊥ := by
  intro h1
  have hred : IsTwoReducedIn H (clV B H) :=
    isTwoReducedIn_conjClosure_of_sylowIn hB.1 hB.2.1 hB.2.2 hchar le_rfl
  have h3 := ((MinParabolic.tfae_thompsonJ hMP hred hHV).out 1 3).mp h1
  have hBQ : B ≤ pCoreOf 2 H := by
    calc B = baum B := hbaum.symm
      _ = baum (pCoreOf 2 H) := h3
      _ ≤ pCoreOf 2 H := C1GN.baum_le _
  have hQB := B6.pCoreOf_two_le_of_isSylowTwoOf hB
  have hBeq : B = pCoreOf 2 H := le_antisymm hBQ hQB
  exact hMP.not_normal (hBeq ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)

end Thompson

section Main

variable {Ω : Type} [Group Ω] [Finite Ω] {B H : Subgroup Ω} {n : ℕ}

theorem noOuter_of_natData (hB : IsSylowTwoOf B H) (hchar : CharTwo H)
    (hmin : IsMinParabolicOf H H) (hbaum : baum B = B) (d : C118NatData B H n) (hn : 2 ≤ n) :
    B ≤ clK B H := by
  classical
  obtain ⟨M, hMP⟩ := exists_minParabolic hB hmin
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchp : CharP d.F 2 := charP_of_card_eq_prime_pow d.hcard
  have hfin : Finite d.F := Finite.of_fintype d.F
  have hαs := d.alpha_surjective hn
  have hBH : B ≤ H := hB.1
  have hBp : IsPGroup 2 ↥B := hB.2.1
  obtain ⟨ρ, hadd, hact⟩ := d.exists_permAction
  let ρB : ↥B →* Equiv.Perm (Fin 2 → d.F) := ρ.comp (Subgroup.inclusion hBH)
  have hsem : ∀ p : ↥B, ∃ σ : d.F ≃+* d.F, IsSemilinearWith (ρB p) σ :=
    fun p => hact.exists_semilinear hadd hαs (Subgroup.inclusion hBH p)
  obtain ⟨σ, hσ, hcocycle⟩ := exists_fieldHom ρB (fun p x y => hadd _ x y) hsem
  have hδ0 : ∀ p : ↥B, (semilinMatrix (ρB p)).det ≠ 0 :=
    fun p => semilinMatrix_det_ne_zero (fun x y => hadd _ x y) (hσ p)
  have hF : 1 < Nat.card d.F - 1 := by
    rw [Nat.card_eq_fintype_card, d.hcard]
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨u, hu⟩ := exists_rescale hBp hF σ (fun p => (semilinMatrix (ρB p)).det) hδ0 hcocycle
  have hmem : ∀ p : ↥B, scalePerm u * ρB p * (scalePerm u)⁻¹ ∈ Gamma d.F :=
    fun p => scale_conj_mem_Gamma (fun x y => hadd _ x y) (hσ p) u (hu p)
  let ρ' : ↥B →* Gamma d.F :=
    (((MulAut.conj (scalePerm u : Equiv.Perm (Fin 2 → d.F))).toMonoidHom).comp ρB).codRestrict
      (Gamma d.F) hmem
  have hρ' : ∀ p : ↥B, ((ρ' p : Gamma d.F) : Equiv.Perm (Fin 2 → d.F)) =
      scalePerm u * ρB p * (scalePerm u)⁻¹ := fun p => rfl
  have hW1B : clW1 B H ≤ B :=
    (clW1_le_clV B H).trans ((clV_le_core hB hchar).trans (B6.pCoreOf_two_le_of_isSylowTwoOf hB))
  let V' : Subgroup ↥B := (clW1 B H).subgroupOf B
  have hVn : V'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hW1B).mpr
    (fun b hb => H_le_normalizer_clW1 B H (hBH hb))
  have hW1e : CFSG.Open.IsElemAbelian 2 (clW1 B H) := by
    obtain ⟨hc, hsq⟩ := B6.isElemAbelian_iff.mp (clV_facts hB hchar).2
    exact B6.isElemAbelian_iff.mpr ⟨fun a ha b hb => hc a (clW1_le_clV B H ha) b
      (clW1_le_clV B H hb), fun a ha => hsq a (clW1_le_clV B H ha)⟩
  have hVe : IsElementaryAbelian 2 V' :=
    BlueprintB2.isElementaryAbelian_subgroupOf
      ((BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mp hW1e)
  let ι : ↥V' ≃* ↥(clW1 B H) := Subgroup.subgroupOfEquivOfLe hW1B
  let sm : Multiplicative (Fin 2 → d.F) →* Multiplicative (Fin 2 → d.F) :=
    { toFun := fun x => Multiplicative.ofAdd ((u : d.F) • Multiplicative.toAdd x)
      map_one' := by simp
      map_mul' := fun x y => by simp [smul_add] }
  let φ : ↥V' →* Multiplicative (Fin 2 → d.F) := sm.comp (d.β.comp ι.toMonoidHom)
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨w, hw⟩ :=
      d.hβ_surj (Multiplicative.ofAdd (((u⁻¹ : Units d.F) : d.F) • Multiplicative.toAdd z))
    refine ⟨ι.symm w, ?_⟩
    show sm (d.β (ι (ι.symm w))) = z
    rw [MulEquiv.apply_symm_apply, hw]
    show Multiplicative.ofAdd
      ((u : d.F) • (((u⁻¹ : Units d.F) : d.F) • Multiplicative.toAdd z)) = z
    rw [smul_smul]
    simp
  have hφρ : ∀ (r : ↥B) (v v' : ↥V'), (v' : ↥B) = r * v * r⁻¹ →
      Multiplicative.toAdd (φ v') =
        ((ρ' r : Gamma d.F) : Equiv.Perm (Fin 2 → d.F)) (Multiplicative.toAdd (φ v)) := by
    intro r v v' hv
    have h1 : actW1 B H (Subgroup.inclusion hBH r) (ι v) = ι v' := by
      apply Subtype.ext
      rw [actW1_coe]
      have := congrArg (fun x : ↥B => (x : Ω)) hv
      have e1 : ((ι v : ↥(clW1 B H)) : Ω) = ((v : ↥B) : Ω) := rfl
      have e2 : ((ι v' : ↥(clW1 B H)) : Ω) = ((v' : ↥B) : Ω) := rfl
      rw [e1, e2]
      exact this.symm
    have h2 : ρ (Subgroup.inclusion hBH r) (Multiplicative.toAdd (d.β (ι v))) =
        Multiplicative.toAdd (d.β (ι v')) := by
      rw [hact, h1]
    have e : ((u⁻¹ : Units d.F) : d.F) • ((u : d.F) • Multiplicative.toAdd (d.β (ι v))) =
        Multiplicative.toAdd (d.β (ι v)) := by
      rw [smul_smul, Units.inv_mul, one_smul]
    show (u : d.F) • Multiplicative.toAdd (d.β (ι v')) = _
    rw [hρ' r]
    simp only [Equiv.Perm.mul_apply, scalePerm_apply, scalePerm_inv_apply]
    show _ = (u : d.F) • ρ (Subgroup.inclusion hBH r)
      (((u⁻¹ : Units d.F) : d.F) • ((u : d.F) • Multiplicative.toAdd (d.β (ι v))))
    rw [e, h2]
  have hρB1 : ∀ b : ↥B, ρ' b = 1 ↔ ρB b = 1 := by
    intro b
    constructor
    · intro h
      have h2 : scalePerm u * ρB b * (scalePerm u)⁻¹ = 1 := by
        rw [← hρ' b, h]
        rfl
      have h3 : scalePerm u * ρB b = scalePerm u := mul_inv_eq_one.mp h2
      exact mul_left_cancel (h3.trans (mul_one _).symm)
    · intro h
      apply Subtype.ext
      rw [hρ' b, h, mul_one, mul_inv_cancel]
      rfl
  have hker : ρ'.ker = Subgroup.centralizer (V' : Set ↥B) := by
    ext b
    rw [MonoidHom.mem_ker, hρB1, Subgroup.mem_centralizer_iff]
    constructor
    · intro hb v hv
      have h2 := hact.mem_centralizer_of_eq_one (Subgroup.inclusion hBH b) hb
      have hvV : (v : Ω) ∈ clV B H := clW1_le_clV B H (Subgroup.mem_subgroupOf.mp hv)
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h2 v hvV)
    · intro hb
      refine Equiv.ext fun x => ?_
      have hM : ∀ w : ↥(clW1 B H),
          Multiplicative.toAdd (d.β (actW1 B H (Subgroup.inclusion hBH b) w)) =
            (1 : Matrix (Fin 2) (Fin 2) d.F).mulVec (Multiplicative.toAdd (d.β w)) := by
        intro w
        have hw : actW1 B H (Subgroup.inclusion hBH b) w = w := by
          apply Subtype.ext
          rw [actW1_coe]
          have := hb ⟨w, hW1B w.2⟩ (Subgroup.mem_subgroupOf.mpr w.2)
          have h3 : (w : Ω) * b = b * w := congrArg (fun x : ↥B => (x : Ω)) this
          show (b : Ω) * w * (b : Ω)⁻¹ = w
          calc (b : Ω) * w * (b : Ω)⁻¹ = ((w : Ω) * b) * (b : Ω)⁻¹ := by rw [h3]
            _ = w := by group
        rw [hw, Matrix.one_mulVec]
      have := hact.eq_mulVec (Subgroup.inclusion hBH b) 1 hM x
      rw [Matrix.one_mulVec] at this
      exact this
  have hJ : ⁅elemThompson ↥B 2, V'⁆ ≠ ⊥ := by
    intro hbot
    apply not_commutator_thompsonJ_eq_bot hB hchar hMP hbaum (d.not_le_centralizer hαs)
    have hJle : thompsonJ B ≤ Subgroup.centralizer (clV B H : Set Ω) := by
      rw [← elemThompson_map_subtype_eq_thompsonJ B]
      rintro _ ⟨j, hj, rfl⟩
      have hjV' : j ∈ Subgroup.centralizer (V' : Set ↥B) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) hj
      rw [← hker, MonoidHom.mem_ker, hρB1] at hjV'
      exact hact.mem_centralizer_of_eq_one (Subgroup.inclusion hBH j) hjV'
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hJle
  obtain ⟨ℓ, -, hBaum, -⟩ :=
    natural_quotient_internal_Thompson_Baumann_image hBp V' hVe ρ' φ hφs hφρ hker hJ
  have hbaumtop : elemBaumann ↥B 2 = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [elemBaumann_map_subtype_eq_baum, hbaum, Subgroup.map_top, Subgroup.range_subtype]
  rw [hbaumtop, Subgroup.map_top] at hBaum
  intro b hb
  have hbR : ρ' ⟨b, hb⟩ ∈ ρ'.range := ⟨⟨b, hb⟩, rfl⟩
  rw [hBaum] at hbR
  obtain ⟨A, hA⟩ := mem_slGamma_iff.mp (rootGamma_le_slGamma ℓ hbR)
  have hρbA : ∀ x, ρ (Subgroup.inclusion hBH ⟨b, hb⟩) x =
      (A : Matrix (Fin 2) (Fin 2) d.F).mulVec x := by
    intro x
    have hE : scalePerm u * ρB ⟨b, hb⟩ * (scalePerm u)⁻¹ = slPerm d.F A := (hρ' _).symm.trans hA
    have h1 := congrArg (fun g : Equiv.Perm (Fin 2 → d.F) => g ((u : d.F) • x)) hE
    simp only [Equiv.Perm.mul_apply, scalePerm_apply, scalePerm_inv_apply, slPerm_apply] at h1
    rw [smul_smul, Units.inv_mul, one_smul] at h1
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec_smul] at h1
    exact smul_right_injective _ (Units.ne_zero u) h1
  obtain ⟨k₀, hk₀⟩ := hαs A
  set g : ↥H := (Subgroup.inclusion (clK_le B H) k₀)⁻¹ * Subgroup.inclusion hBH ⟨b, hb⟩ with hg
  have hgtriv : ρ g = 1 := by
    refine Equiv.ext fun x => ?_
    rw [hg, map_mul, map_inv, Equiv.Perm.mul_apply]
    show (ρ (Subgroup.inclusion (clK_le B H) k₀))⁻¹
      (ρ (Subgroup.inclusion hBH ⟨b, hb⟩) x) = x
    rw [Equiv.Perm.inv_eq_iff_eq, hρbA, hact.incl, hk₀]
  have hgC := hact.mem_centralizer_of_eq_one g hgtriv
  have hgK : (g : Ω) ∈ clK B H :=
    inf_centralizer_le_fstarPre H (VZ B H) (H_le_normalizer_clV B H) ⟨g.2, hgC⟩
  have hbeq : b = (k₀ : Ω) * (g : Ω) := by
    simp [hg]
  rw [hbeq]
  exact (clK B H).mul_mem k₀.2 hgK

end Main

theorem noOuterFact : NoOuterFact := by
  intro Ω _ _ B H hbaum hcl
  obtain ⟨n, hn2, hsec⟩ := hcl.two
  obtain ⟨d⟩ := exists_natData (B := B) (H := H) hsec
  exact noOuter_of_natData hcl.cls.isSylow hcl.cls.charTwo hcl.cls.minParabolic hbaum d hn2

theorem theoremC118 : TheoremC118 := theoremC118_of_noOuter noOuterFact

end CFSG.Quasithin
