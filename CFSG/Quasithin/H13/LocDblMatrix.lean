module

public import CFSG.Quasithin.H13.LocDblCriterion
public import CFSG.LinearAlgebra.SteinbergBQPerfectCentralizer
public import CFSG.Quasithin.SteinbergBQDegreeThreeAutomizer
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Open CFSG.Quasithin Module
open scoped commutatorElement

section Fitting

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem map_subtype_top (L : Subgroup G) : (⊤ : Subgroup ↥L).map L.subtype = L := by
  rw [Subgroup.map_top, Subgroup.range_subtype]

omit [Finite G] in
theorem subnormal_map_subtype {X L : Subgroup G} (hL : IsSubnormal L X) {T : Subgroup ↥L}
    (hT : T.IsSubnormal) : IsSubnormal (T.map L.subtype) X := by
  have h2 := A3.subnormal_map L.subtype (A3.subnormal_top_iff.mpr hT)
  rw [map_subtype_top] at h2
  exact A3.subnormal_trans h2 hL

omit [Finite G] in
theorem layer_eq_bot_of_mem_cComp {X L : Subgroup G} (hL : L ∈ cComp X)
    (hq : ¬ CFSG.IsQuasisimple ↥L) : CFSG.layer ↥L = ⊥ := by
  refine le_bot_iff.mp (sSup_le fun T hT => ?_)
  exfalso
  obtain ⟨hTq, hTsub⟩ := hT
  have hTne : T ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot T).mp (CFSG.LocalCores.isQuasisimple_nontrivial hTq)
  have hTperf : ⁅T, T⁆ = T := Subgroup.isPerfect_iff.mp hTq.1
  set T' : Subgroup G := T.map L.subtype with hT'
  have hT'le : T' ≤ L := Subgroup.map_subtype_le T
  have hT'ne : T' ≠ ⊥ := fun h =>
    hTne ((Subgroup.map_eq_bot_iff_of_injective T L.subtype_injective).mp h)
  have hT'perf : ⁅T', T'⁆ = T' := by rw [hT', ← Subgroup.map_commutator, hTperf]
  have hT'sub : IsSubnormal T' X := subnormal_map_subtype (subnormal_of_mem_cComp hL) hTsub
  have hT'eq : T' = L := by
    by_contra hne
    exact not_subnormal_of_mem_cComp hL (lt_of_le_of_ne hT'le hne) hT'ne hT'perf hT'sub
  have hTtop : T = ⊤ :=
    Subgroup.map_injective L.subtype_injective (by rw [← hT', hT'eq, map_subtype_top])
  apply hq
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((MulEquiv.subgroupCongr hTtop).trans Subgroup.topEquiv) hTq

theorem nonquasisimple_Fitting_of_mem_cComp {X L : Subgroup G} (hL : L ∈ cComp X)
    (hq : ¬ CFSG.IsQuasisimple ↥L) :
    CFSG.layer ↥L = ⊥ ∧ CFSG.generalizedFitting ↥L = CFSG.fittingSubgroup ↥L ∧
      CFSG.fittingSubgroup ↥L ≠ ⊥ ∧ Group.IsNilpotent ↥(CFSG.fittingSubgroup ↥L) ∧
      ⁅(⊤ : Subgroup ↥L), CFSG.fittingSubgroup ↥L⁆ ≠ ⊥ := by
  have hE := layer_eq_bot_of_mem_cComp hL hq
  have hF : CFSG.generalizedFitting ↥L = CFSG.fittingSubgroup ↥L := by
    rw [CFSG.generalizedFitting, hE, sup_bot_eq]
  have hcent := CFSG.centralizer_generalizedFitting_le ↥L
  rw [hF] at hcent
  have hnil := (CFSG.LocalCores.fitting_nilpotent (G := ↥L)).1
  refine ⟨hE, hF, ?_, hnil, ?_⟩
  · intro hbot
    rw [hbot, Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.mpr
      (Set.singleton_subset_iff.mpr (Subgroup.one_mem _))] at hcent
    apply ne_bot_of_mem_cComp hL
    have htop : (⊤ : Subgroup ↥L) = ⊥ := le_bot_iff.mp hcent
    rw [← map_subtype_top L, htop, Subgroup.map_bot]
  · intro hcomm
    have hle : (⊤ : Subgroup ↥L) ≤ CFSG.fittingSubgroup ↥L :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hcent
    have : Group.IsNilpotent ↥L := by
      have e : ↥(CFSG.fittingSubgroup ↥L) ≃* ↥L :=
        (MulEquiv.subgroupCongr (top_le_iff.mp hle)).trans Subgroup.topEquiv
      exact Group.nilpotent_of_surjective e.toMonoidHom e.surjective
    exact not_isSolvable_of_mem_cComp hL inferInstance

theorem Ccomm_structure_nonquasisimple_Fitting {L : Subgroup G}
    (hL : L ∈ cComp (⊤ : Subgroup G)) (hq : ¬ CFSG.IsQuasisimple ↥L) :
    CFSG.layer ↥L = ⊥ ∧ CFSG.generalizedFitting ↥L = CFSG.fittingSubgroup ↥L ∧
      CFSG.fittingSubgroup ↥L ≠ ⊥ ∧ Group.IsNilpotent ↥(CFSG.fittingSubgroup ↥L) ∧
      ⁅(⊤ : Subgroup ↥L), CFSG.fittingSubgroup ↥L⁆ ≠ ⊥ :=
  nonquasisimple_Fitting_of_mem_cComp hL hq

theorem commutator_fitting_eq_bot_of_pCore {L : Type*} [Group L] [Finite L]
    (h : ∀ ℓ : ℕ, ℓ.Prime → ⁅(⊤ : Subgroup L), CFSG.pCore ℓ L⁆ = ⊥) :
    ⁅(⊤ : Subgroup L), CFSG.fittingSubgroup L⁆ = ⊥ := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer,
    CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun ℓ => ?_
  have := h ℓ (Nat.prime_of_mem_primeFactors ℓ.2)
  rwa [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at this

end Fitting

section Linear

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem commute_of_flag {W : Submodule k V} {g h : V →ₗ[k] V} (hg1 : ∀ v, g v - v ∈ W)
    (hg2 : ∀ w ∈ W, g w = w) (hh1 : ∀ v, h v - v ∈ W) (hh2 : ∀ w ∈ W, h w = w) :
    g ∘ₗ h = h ∘ₗ g := by
  ext v
  simp only [LinearMap.comp_apply]
  have e1 : g (h v) = g v + (h v - v) := by
    have : h v = v + (h v - v) := by abel
    rw [this, map_add, hg2 _ (hh1 v)]
    abel
  have e2 : h (g v) = h v + (g v - v) := by
    have : g v = v + (g v - v) := by abel
    rw [this, map_add, hh2 _ (hg1 v)]
    abel
  rw [e1, e2]
  abel

@[expose] def fixedSpace (U : Subgroup (LinearMap.GeneralLinearGroup k V)) : Submodule k V where
  carrier := {v | ∀ u ∈ U, (u : V →ₗ[k] V) v = v}
  add_mem' := by
    intro a b ha hb u hu
    rw [map_add, ha u hu, hb u hu]
  zero_mem' := by
    intro u _
    exact map_zero _
  smul_mem' := by
    intro c v hv u hu
    rw [map_smul, hv u hu]

theorem mem_fixedSpace {U : Subgroup (LinearMap.GeneralLinearGroup k V)} {v : V} :
    v ∈ fixedSpace U ↔ ∀ u ∈ U, (u : V →ₗ[k] V) v = v := Iff.rfl

theorem fixedSpace_ne_top {U : Subgroup (LinearMap.GeneralLinearGroup k V)} (hU : U ≠ ⊥) :
    fixedSpace U ≠ ⊤ := by
  intro htop
  apply hU
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  apply Units.ext
  ext v
  have hv : v ∈ fixedSpace U := htop ▸ Submodule.mem_top
  exact hv u hu

theorem fixedSpace_invariant {U : Subgroup (LinearMap.GeneralLinearGroup k V)}
    {m : LinearMap.GeneralLinearGroup k V} (hm : m ∈ Subgroup.normalizer (U : Set _)) {v : V}
    (hv : v ∈ fixedSpace U) : (m : V →ₗ[k] V) v ∈ fixedSpace U := by
  intro u hu
  have hu' : m⁻¹ * u * m ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) u).mp hu
    simpa using this
  have h := hv _ hu'
  have : (u : V →ₗ[k] V) ((m : V →ₗ[k] V) v) =
      (m : V →ₗ[k] V) (((m⁻¹ * u * m : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) v) := by
    simp only [Units.val_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply (m : V →ₗ[k] V), ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  rw [this, h]

theorem exists_fixed_ne_zero [Finite k] [FiniteDimensional k V] {p : ℕ} [hp : Fact p.Prime]
    [CharP k p] (hV : finrank k V ≠ 0) {U : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hU : IsPGroup p U) : fixedSpace U ≠ ⊥ := by
  have : Finite V := Module.finite_of_finite k
  have hmod := hU.card_modEq_card_fixedPoints V
  have hpV : p ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := k)]
    refine dvd_pow ?_ hV
    have := addOrderOf_dvd_natCard (1 : k)
    rwa [CharP.eq k (CharP.addOrderOf_one k) ‹CharP k p›] at this
  have hfix : p ∣ Nat.card (MulAction.fixedPoints U V) :=
    (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hpV)))
  have h0 : (0 : V) ∈ MulAction.fixedPoints U V := fun u => by
    show (u : LinearMap.GeneralLinearGroup k V) • (0 : V) = 0
    exact smul_zero _
  have h2 : 1 < Nat.card (MulAction.fixedPoints U V) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints U V) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨0, h0⟩⟩, inferInstance⟩
    have := Nat.le_of_dvd hpos hfix
    have := hp.out.two_le
    omega
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := Finite.one_lt_card_iff_nontrivial.mp h2 |>.exists_pair_ne
  intro hbot
  have hfa : a ∈ fixedSpace U := fun u hu => ha ⟨u, hu⟩
  have hfb : b ∈ fixedSpace U := fun u hu => hb ⟨u, hu⟩
  rw [hbot, Submodule.mem_bot] at hfa hfb
  exact hab (Subtype.ext (hfa.trans hfb.symm))

@[expose] def blockEndHom : Module.End k V →* Module.End k (V × k) where
  toFun f := f.prodMap LinearMap.id
  map_one' := by ext <;> simp
  map_mul' f g := by ext <;> simp

@[expose] def blockEmbed :
    LinearMap.GeneralLinearGroup k V →* LinearMap.GeneralLinearGroup k (V × k) :=
  Units.map blockEndHom

theorem blockEmbed_apply (g : LinearMap.GeneralLinearGroup k V) (v : V) (c : k) :
    ((blockEmbed g : LinearMap.GeneralLinearGroup k (V × k)) : V × k →ₗ[k] V × k) (v, c) =
      ((g : V →ₗ[k] V) v, c) := rfl

theorem blockEmbed_injective : Function.Injective (blockEmbed (k := k) (V := V)) := by
  intro g h hgh
  apply Units.ext
  ext v
  have := congrArg (fun x : LinearMap.GeneralLinearGroup k (V × k) =>
    ((x : V × k →ₗ[k] V × k) (v, 0)).1) hgh
  simpa [blockEmbed_apply] using this

theorem sub_mem_of_finrank_succ [FiniteDimensional k V]
    {P : Subgroup (LinearMap.GeneralLinearGroup k V)} (hPperf : ⁅P, P⁆ = P)
    {A B : Submodule k V} (hAB : A ≤ B) (hdim : finrank k B = finrank k A + 1)
    (hPB : ∀ g ∈ P, ∀ b ∈ B, (g : V →ₗ[k] V) b ∈ B)
    (hPA : ∀ g ∈ P, ∀ a ∈ A, (g : V →ₗ[k] V) a ∈ A)
    {g : LinearMap.GeneralLinearGroup k V} (hg : g ∈ P) {b : V} (hb : b ∈ B) :
    (g : V →ₗ[k] V) b - b ∈ A := by
  refine CFSG.LinearAlgebra.SteinbergBQ.sub_mem_of_commute_mod hPperf hPB hPA
    (fun g hg h hh b hb => ?_) hg hb
  obtain ⟨α, hα⟩ := CFSG.LinearAlgebra.SteinbergBQ.exists_scalar_of_finrank_succ hAB hdim
    (hPA g hg) (hPB g hg)
  obtain ⟨β, hβ⟩ := CFSG.LinearAlgebra.SteinbergBQ.exists_scalar_of_finrank_succ hAB hdim
    (hPA h hh) (hPB h hh)
  set G' : V →ₗ[k] V := (g : V →ₗ[k] V)
  set H' : V →ₗ[k] V := (h : V →ₗ[k] V)
  have hgb := hα b hb
  have hhb := hβ b hb
  have e1 : G' (H' b) = G' (H' b - β • b) + β • (G' b - α • b) + (β * α) • b := by
    rw [map_sub, map_smul, smul_sub, smul_smul]
    abel
  have e2 : H' (G' b) = H' (G' b - α • b) + α • (H' b - β • b) + (α * β) • b := by
    rw [map_sub, map_smul, smul_sub, smul_smul]
    abel
  rw [e1, e2, mul_comm β α]
  have h1 : G' (H' b - β • b) ∈ A := hPA g hg _ hhb
  have h2 : H' (G' b - α • b) ∈ A := hPA h hh _ hgb
  have : G' (H' b - β • b) + β • (G' b - α • b) + (α * β) • b -
      (H' (G' b - α • b) + α • (H' b - β • b) + (α * β) • b) =
      G' (H' b - β • b) + β • (G' b - α • b) - (H' (G' b - α • b) + α • (H' b - β • b)) := by
    abel
  rw [this]
  exact A.sub_mem (A.add_mem h1 (A.smul_mem _ hgb)) (A.add_mem h2 (A.smul_mem _ hhb))

end Linear

section Cores

variable {Γ : Type*} [Group Γ]

theorem le_normalizer_map_pCore (B : Subgroup Γ) (ℓ : ℕ) :
    B ≤ Subgroup.normalizer (((CFSG.pCore ℓ ↥B).map B.subtype : Subgroup Γ) : Set Γ) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hn : (CFSG.pCore ℓ ↥B).Normal := CFSG.pCore_normal
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨b, hb⟩ * y * ⟨b, hb⟩⁻¹, hn.conj_mem y hy _, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨b, hb⟩⁻¹ * y * ⟨b, hb⟩, ?_, ?_⟩
    · have := hn.conj_mem y hy ⟨b, hb⟩⁻¹
      simpa using this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyx ⊢
      rw [hyx]
      group

theorem commutator_pCore_eq_bot {B : Subgroup Γ} {ℓ : ℕ}
    (h : ∀ b ∈ B, ∀ x ∈ (CFSG.pCore ℓ ↥B).map B.subtype, b * x = x * b) :
    ⁅(⊤ : Subgroup ↥B), CFSG.pCore ℓ ↥B⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro y _
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  apply Subtype.ext
  exact (h y y.2 x ⟨x, hx, rfl⟩).symm

end Cores

section DegreeTwo

variable {k V : Type*} [Field k] [Finite k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [Finite k] [FiniteDimensional k V] in
theorem eq_bot_of_flag {W : Submodule k V} {P : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hPperf : ⁅P, P⁆ = P) (h1 : ∀ g ∈ P, ∀ v, (g : V →ₗ[k] V) v - v ∈ W)
    (h2 : ∀ g ∈ P, ∀ w ∈ W, (g : V →ₗ[k] V) w = w) : P = ⊥ := by
  have hcomm : ⁅P, P⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    apply Units.ext
    exact commute_of_flag (h1 h hh) (h2 h hh) (h1 g hg) (h2 g hg)
  rw [← hPperf, hcomm]

theorem pCore_eq_bot_of_finrank_two {p : ℕ} [Fact p.Prime] [CharP k p] (hV : finrank k V = 2)
    {B : Subgroup (LinearMap.GeneralLinearGroup k V)} (hBperf : ⁅B, B⁆ = B) (hBne : B ≠ ⊥) :
    CFSG.pCore p ↥B = ⊥ := by
  by_contra hU
  set U : Subgroup (LinearMap.GeneralLinearGroup k V) := (CFSG.pCore p ↥B).map B.subtype with hUdef
  have hUne : U ≠ ⊥ := fun h =>
    hU ((Subgroup.map_eq_bot_iff_of_injective _ B.subtype_injective).mp h)
  have hUp : IsPGroup p ↥U := CFSG.pCore_isPGroup.map B.subtype
  set W := fixedSpace U with hW
  have hW0 : W ≠ ⊥ := exists_fixed_ne_zero (by omega) hUp
  have hWtop : W ≠ ⊤ := fixedSpace_ne_top hUne
  have hWdim : finrank k W = 1 := by
    have h1 : 1 ≤ finrank k W := Submodule.one_le_finrank_iff.mpr hW0
    have h2 : finrank k W < finrank k V := Submodule.finrank_lt hWtop
    omega
  have hBN := le_normalizer_map_pCore B p
  have hBW : ∀ g ∈ B, ∀ w ∈ W, (g : V →ₗ[k] V) w ∈ W := fun g hg w hw =>
    fixedSpace_invariant (hBN hg) hw
  have htriv1 : ∀ g ∈ B, ∀ w ∈ W, (g : V →ₗ[k] V) w = w := by
    intro g hg w hw
    have := sub_mem_of_finrank_succ hBperf (bot_le : (⊥ : Submodule k V) ≤ W)
      (by rw [finrank_bot, hWdim]) hBW (fun g _ a ha => by
        rw [Submodule.mem_bot] at ha ⊢
        rw [ha, map_zero]) hg hw
    rw [Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have htriv2 : ∀ g ∈ B, ∀ v, (g : V →ₗ[k] V) v - v ∈ W := by
    intro g hg v
    exact sub_mem_of_finrank_succ hBperf (le_top : W ≤ ⊤) (by rw [finrank_top, hWdim, hV])
      (fun _ _ _ _ => Submodule.mem_top) hBW hg Submodule.mem_top
  exact hBne (eq_bot_of_flag hBperf htriv2 htriv1)

theorem finite_GL : Finite (LinearMap.GeneralLinearGroup k V) := by
  have : Finite (V →ₗ[k] V) := Module.finite_of_finite k
  exact instFiniteUnits

theorem commutator_pCore_eq_bot_of_finrank_three {p ℓ : ℕ} [Fact p.Prime] [CharP k p]
    [Fact ℓ.Prime] (hV : finrank k V = 3) (hℓp : ℓ ≠ p)
    {B : Subgroup (LinearMap.GeneralLinearGroup k V)} (hBperf : ⁅B, B⁆ = B) :
    ⁅(⊤ : Subgroup ↥B), CFSG.pCore ℓ ↥B⁆ = ⊥ := by
  have : Finite (LinearMap.GeneralLinearGroup k V) := finite_GL
  set P : Subgroup (LinearMap.GeneralLinearGroup k V) := (CFSG.pCore ℓ ↥B).map B.subtype with hP
  have hPp : IsPGroup ℓ ↥P := CFSG.pCore_isPGroup.map B.subtype
  obtain ⟨-, -, h3⟩ :=
    CFSG.Quasithin.SteinbergBQ.degree_three_coprime_automizer_solvable hV hℓp P hPp
  have hC := h3 B (le_normalizer_map_pCore B ℓ) hBperf
  refine commutator_pCore_eq_bot fun b hb x hx => ?_
  exact (Subgroup.mem_centralizer_iff.mp (hC hb) x hx).symm

theorem commutator_pCore_eq_bot_of_finrank_two {p ℓ : ℕ} [Fact p.Prime] [CharP k p]
    [Fact ℓ.Prime] (hV : finrank k V = 2) (hℓp : ℓ ≠ p)
    {B : Subgroup (LinearMap.GeneralLinearGroup k V)} (hBperf : ⁅B, B⁆ = B) :
    ⁅(⊤ : Subgroup ↥B), CFSG.pCore ℓ ↥B⁆ = ⊥ := by
  have : Finite (LinearMap.GeneralLinearGroup k (V × k)) := finite_GL
  have hV3 : finrank k (V × k) = 3 := by rw [Module.finrank_prod, hV, Module.finrank_self]
  set P : Subgroup (LinearMap.GeneralLinearGroup k (V × k)) :=
    ((CFSG.pCore ℓ ↥B).map B.subtype).map blockEmbed with hP
  have hPp : IsPGroup ℓ ↥P := (CFSG.pCore_isPGroup.map B.subtype).map blockEmbed
  obtain ⟨-, -, h3⟩ :=
    CFSG.Quasithin.SteinbergBQ.degree_three_coprime_automizer_solvable hV3 hℓp P hPp
  have hBN : B.map blockEmbed ≤ Subgroup.normalizer (P : Set _) :=
    (Subgroup.map_mono (le_normalizer_map_pCore B ℓ)).trans (Subgroup.le_normalizer_map _)
  have hperf : ⁅B.map blockEmbed, B.map blockEmbed⁆ = B.map blockEmbed := by
    rw [← Subgroup.map_commutator, hBperf]
  have hC := h3 _ hBN hperf
  refine commutator_pCore_eq_bot fun b hb x hx => blockEmbed_injective ?_
  rw [map_mul, map_mul]
  exact (Subgroup.mem_centralizer_iff.mp (hC ⟨b, hb, rfl⟩) (blockEmbed x) ⟨x, hx, rfl⟩).symm

theorem commutator_eq_bot_of_quasisimple {Γ : Type*} [Group Γ] [Finite Γ] {H B C : Subgroup Γ}
    (hB : B ∈ cComp H) (hC : C ∈ cComp H) (hqB : CFSG.IsQuasisimple ↥B)
    (hqC : CFSG.IsQuasisimple ↥C) (hBC : B ≠ C) : ⁅B, C⁆ = ⊥ := by
  have hBH := le_of_mem_cComp hB
  have hCH := le_of_mem_cComp hC
  have hB' : CFSG.IsComponent (B.subgroupOf H) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBH).symm hqB,
      A3.subnormal_top_iff.mp (subnormal_of_mem_cComp (subgroupOf_mem_cComp hB))⟩
  have hC' : CFSG.IsComponent (C.subgroupOf H) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCH).symm hqC,
      A3.subnormal_top_iff.mp (subnormal_of_mem_cComp (subgroupOf_mem_cComp hC))⟩
  rcases CFSG.LocalCores.distinct_components_commute hB' hC' with h | h
  · exfalso
    apply hBC
    have := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hBH, Subgroup.map_subgroupOf_eq_of_le hCH] at this
  · have := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hBH,
      Subgroup.map_subgroupOf_eq_of_le hCH, Subgroup.map_bot] at this

theorem cComp_quasisimple_and_subsingleton_of_finrank_two {p : ℕ} [Fact p.Prime] [CharP k p]
    (hV : finrank k V = 2) (H : Subgroup (LinearMap.GeneralLinearGroup k V)) :
    (∀ B ∈ cComp H, CFSG.IsQuasisimple ↥B) ∧ (cComp H).Subsingleton := by
  have : Finite (LinearMap.GeneralLinearGroup k V) := finite_GL
  have hq : ∀ B ∈ cComp H, CFSG.IsQuasisimple ↥B := by
    intro B hB
    by_contra hnq
    obtain ⟨-, -, -, -, hcomm⟩ := nonquasisimple_Fitting_of_mem_cComp hB hnq
    apply hcomm
    refine commutator_fitting_eq_bot_of_pCore fun ℓ hℓ => ?_
    by_cases hℓp : ℓ = p
    · subst hℓp
      rw [pCore_eq_bot_of_finrank_two hV (perfect_of_mem_cComp hB) (ne_bot_of_mem_cComp hB),
        Subgroup.commutator_bot_right]
    · have : Fact ℓ.Prime := ⟨hℓ⟩
      exact commutator_pCore_eq_bot_of_finrank_two hV hℓp (perfect_of_mem_cComp hB)
  refine ⟨hq, fun B hB C hC => ?_⟩
  by_contra hne
  have hBC := commutator_eq_bot_of_quasisimple hB hC (hq B hB) (hq C hC) hne
  have : Finite (LinearMap.GeneralLinearGroup k (V × k)) := finite_GL
  have hV3 : finrank k (V × k) = 3 := by rw [Module.finrank_prod, hV, Module.finrank_self]
  have hne' : B.map blockEmbed ≠ ⊥ := fun h => ne_bot_of_mem_cComp hB
    ((Subgroup.map_eq_bot_iff_of_injective B blockEmbed_injective).mp h)
  have hperf' : ⁅B.map blockEmbed, B.map blockEmbed⁆ = B.map blockEmbed := by
    rw [← Subgroup.map_commutator, perfect_of_mem_cComp hB]
  obtain ⟨-, hsolv⟩ :=
    CFSG.LinearAlgebra.degree_three_perfect_matrix_subgroup_centralizer_metabelian hV3 _ hne' hperf'
  have hCle : C.map blockEmbed ≤ Subgroup.centralizer (B.map blockEmbed : Set _) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hcomm : b * c = c * b := by
      have : ⁅b, c⁆ ∈ ⁅B, C⁆ := Subgroup.commutator_mem_commutator hb hc
      rw [hBC, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    rw [← map_mul, ← map_mul, hcomm]
  have : Group.IsSolvable ↥(C.map blockEmbed) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hCle)
      (Subgroup.inclusion_injective hCle)
  exact not_isSolvable_of_mem_cComp hC (Group.isSolvable_of_isSolvable_injective
    (f := (C.equivMapOfInjective _ blockEmbed_injective).toMonoidHom)
    (C.equivMapOfInjective _ blockEmbed_injective).injective)

end DegreeTwo

section DegreeThree

variable {k V : Type*} [Field k] [Finite k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem normalizer_le_normalizer_map_pCore {Γ : Type*} [Group Γ] (B : Subgroup Γ) (p : ℕ) :
    Subgroup.normalizer (B : Set Γ) ≤
      Subgroup.normalizer (((CFSG.pCore p ↥B).map B.subtype : Subgroup Γ) : Set Γ) := by
  intro m hm
  rw [← map_conj_eq_iff] at hm ⊢
  set e : ↥B ≃* ↥B := (MulEquiv.subgroupMap (MulAut.conj m) B).trans (MulEquiv.subgroupCongr hm)
  have he : (CFSG.pCore p ↥B).map e.toMonoidHom = CFSG.pCore p ↥B :=
    CFSG.LieType.SteinbergBR.pCore_map_equiv p e
  conv_rhs => rw [← he]
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

omit [Finite k] [FiniteDimensional k V] in
theorem isSolvable_of_flag {M : Type*} [Group M] {W : Submodule k V}
    (φ : M →* LinearMap.GeneralLinearGroup k V) (K : Subgroup M)
    (h1 : ∀ x ∈ K, ∀ v, (φ x : V →ₗ[k] V) v - v ∈ W)
    (h2 : ∀ x ∈ K, ∀ w ∈ W, (φ x : V →ₗ[k] V) w = w) (hφ : Function.Injective φ) :
    Group.IsSolvable ↥K := by
  refine Group.isSolvable_of_comm fun x y => Subtype.ext (hφ ?_)
  apply Units.ext
  simp only [Subgroup.coe_mul, map_mul, Units.val_mul]
  exact commute_of_flag (h1 x x.2) (h2 x x.2) (h1 y y.2) (h2 y y.2)

theorem eq_of_two_dim_image {Q : Type*} [AddCommGroup Q] [Module k Q] [FiniteDimensional k Q]
    {p : ℕ} [Fact p.Prime] [CharP k p] (hQ : finrank k Q = 2)
    {M B C : Subgroup (LinearMap.GeneralLinearGroup k V)} (hBM : B ∈ cComp M)
    (hCM : C ∈ cComp M) (ρ : ↥M →* LinearMap.GeneralLinearGroup k Q)
    (hker : Group.IsSolvable ρ.ker) : B = C := by
  have : Finite (LinearMap.GeneralLinearGroup k V) := finite_GL
  have : Finite (LinearMap.GeneralLinearGroup k Q) := finite_GL
  have hB' := subgroupOf_mem_cComp hBM
  have hC' := subgroupOf_mem_cComp hCM
  have h := (cComp_quasisimple_and_subsingleton_of_finrank_two hQ _).2
    (map_mem_cComp_of_ker ρ hker hB') (map_mem_cComp_of_ker ρ hker hC')
  have h' := map_injOn_cComp ρ hker ⊤ hB' hC' h
  have := congrArg (Subgroup.map M.subtype) h'
  rwa [Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hBM),
    Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hCM)] at this

theorem eq_of_nonquasisimple_finrank_three {p : ℕ} [Fact p.Prime] [CharP k p]
    (hV : finrank k V = 3) {H B C : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hB : B ∈ cComp H) (hC : C ∈ cComp H) (hnq : ¬ CFSG.IsQuasisimple ↥B) : B = C := by
  have : Finite (LinearMap.GeneralLinearGroup k V) := finite_GL
  obtain ⟨-, -, -, -, hcomm⟩ := nonquasisimple_Fitting_of_mem_cComp hB hnq
  have hBperf := perfect_of_mem_cComp hB
  have hUne : CFSG.pCore p ↥B ≠ ⊥ := by
    intro hbot
    apply hcomm
    refine commutator_fitting_eq_bot_of_pCore fun ℓ hℓ => ?_
    by_cases hℓp : ℓ = p
    · subst hℓp
      rw [hbot, Subgroup.commutator_bot_right]
    · have : Fact ℓ.Prime := ⟨hℓ⟩
      exact commutator_pCore_eq_bot_of_finrank_three hV hℓp hBperf
  set U : Subgroup (LinearMap.GeneralLinearGroup k V) := (CFSG.pCore p ↥B).map B.subtype with hU
  have hUne' : U ≠ ⊥ := fun h =>
    hUne ((Subgroup.map_eq_bot_iff_of_injective _ B.subtype_injective).mp h)
  have hUp : IsPGroup p ↥U := CFSG.pCore_isPGroup.map B.subtype
  set M : Subgroup (LinearMap.GeneralLinearGroup k V) := B ⊔ C with hM
  have hMH : M ≤ H := sup_le (le_of_mem_cComp hB) (le_of_mem_cComp hC)
  have hBM : B ∈ cComp M := cComp_mem_of_le hB le_sup_left hMH
  have hCM : C ∈ cComp M := cComp_mem_of_le hC le_sup_right hMH
  have hMperf : ⁅M, M⁆ = M := by
    refine le_antisymm (A3.commutator_self_le M) (sup_le ?_ ?_)
    · calc B = ⁅B, B⁆ := hBperf.symm
        _ ≤ ⁅M, M⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc C = ⁅C, C⁆ := (perfect_of_mem_cComp hC).symm
        _ ≤ ⁅M, M⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
  have hMN : M ≤ Subgroup.normalizer (U : Set _) :=
    (sup_le Subgroup.le_normalizer (le_normalizer_of_mem_cComp hB hC)).trans
      (normalizer_le_normalizer_map_pCore B p)
  set W : Submodule k V := fixedSpace U with hW
  have hW0 : W ≠ ⊥ := exists_fixed_ne_zero (by omega) hUp
  have hWtop : W ≠ ⊤ := fixedSpace_ne_top hUne'
  have hMW : ∀ g ∈ M, ∀ w ∈ W, (g : V →ₗ[k] V) w ∈ W := fun g hg w hw =>
    fixedSpace_invariant (hMN hg) hw
  have hd1 : 1 ≤ finrank k W := Submodule.one_le_finrank_iff.mpr hW0
  have hd2 : finrank k W < 3 := hV ▸ Submodule.finrank_lt hWtop
  rcases (by omega : finrank k W = 1 ∨ finrank k W = 2) with h1 | h2
  ·
    have htrivW : ∀ g ∈ M, ∀ w ∈ W, (g : V →ₗ[k] V) w = w := by
      intro g hg w hw
      have := sub_mem_of_finrank_succ hMperf (bot_le : (⊥ : Submodule k V) ≤ W)
        (by rw [finrank_bot, h1]) hMW (fun g _ a ha => by
          rw [Submodule.mem_bot] at ha ⊢
          rw [ha, map_zero]) hg hw
      rwa [Submodule.mem_bot, sub_eq_zero] at this
    set ρ := (CFSG.LinearAlgebra.SteinbergBQ.segRep M (A := W) (B := ⊤)
      (fun _ _ _ _ => Submodule.mem_top) hMW).toHomUnits with hρ
    have hQ : finrank k (↥(⊤ : Submodule k V) ⧸ W.comap (⊤ : Submodule k V).subtype) = 2 := by
      have h := Submodule.finrank_quotient_add_finrank (W.comap (⊤ : Submodule k V).subtype)
      rw [(Submodule.comapSubtypeEquivOfLe (le_top : W ≤ ⊤)).finrank_eq, finrank_top, hV,
        h1] at h
      omega
    refine eq_of_two_dim_image hQ hBM hCM ρ (isSolvable_of_flag (W := W) M.subtype ρ.ker
      (fun x hx v => ?_) (fun x _ w hw => htrivW x x.2 w hw) M.subtype_injective)
    have hx' : CFSG.LinearAlgebra.SteinbergBQ.segRep M (A := W) (B := ⊤)
        (fun _ _ _ _ => Submodule.mem_top) hMW x = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hx)
      rwa [hρ, MonoidHom.coe_toHomUnits, Units.val_one] at this
    have := LinearMap.congr_fun hx' (Submodule.Quotient.mk ⟨v, Submodule.mem_top⟩)
    rw [CFSG.LinearAlgebra.SteinbergBQ.segRep_mk, Module.End.one_apply,
      Submodule.Quotient.eq] at this
    exact this
  ·
    have htrivQ : ∀ g ∈ M, ∀ v, (g : V →ₗ[k] V) v - v ∈ W := fun g hg v =>
      sub_mem_of_finrank_succ hMperf (le_top : W ≤ ⊤) (by rw [finrank_top, hV, h2])
        (fun _ _ _ _ => Submodule.mem_top) hMW hg Submodule.mem_top
    have hbot : ∀ g ∈ M, ∀ a ∈ (⊥ : Submodule k V), (g : V →ₗ[k] V) a ∈ (⊥ : Submodule k V) :=
      fun g _ a ha => by
        rw [Submodule.mem_bot] at ha ⊢
        rw [ha, map_zero]
    set ρ := (CFSG.LinearAlgebra.SteinbergBQ.segRep M (A := ⊥) (B := W) hMW hbot).toHomUnits
      with hρ
    have hQ : finrank k (↥W ⧸ (⊥ : Submodule k V).comap W.subtype) = 2 := by
      have h := Submodule.finrank_quotient_add_finrank ((⊥ : Submodule k V).comap W.subtype)
      rw [(Submodule.comapSubtypeEquivOfLe (bot_le : (⊥ : Submodule k V) ≤ W)).finrank_eq,
        finrank_bot, h2] at h
      omega
    refine eq_of_two_dim_image hQ hBM hCM ρ (isSolvable_of_flag (W := W) M.subtype ρ.ker
      (fun x _ v => htrivQ x x.2 v) (fun x hx w hw => ?_) M.subtype_injective)
    have hx' : CFSG.LinearAlgebra.SteinbergBQ.segRep M (A := ⊥) (B := W) hMW hbot x = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hx)
      rwa [hρ, MonoidHom.coe_toHomUnits, Units.val_one] at this
    have := LinearMap.congr_fun hx' (Submodule.Quotient.mk ⟨w, hw⟩)
    rw [CFSG.LinearAlgebra.SteinbergBQ.segRep_mk, Module.End.one_apply,
      Submodule.Quotient.eq] at this
    have h0 : ((x : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) w - w ∈
        (⊥ : Submodule k V) := this
    rwa [Submodule.mem_bot, sub_eq_zero] at h0

theorem cComp_subsingleton_of_finrank_three {p : ℕ} [Fact p.Prime] [CharP k p]
    (hV : finrank k V = 3) (H : Subgroup (LinearMap.GeneralLinearGroup k V)) :
    (cComp H).Subsingleton := by
  have : Finite (LinearMap.GeneralLinearGroup k V) := finite_GL
  intro B hB C hC
  by_cases hqB : CFSG.IsQuasisimple ↥B
  · by_cases hqC : CFSG.IsQuasisimple ↥C
    · by_contra hne
      have hBC := commutator_eq_bot_of_quasisimple hB hC hqB hqC hne
      obtain ⟨-, hsolv⟩ :=
        CFSG.LinearAlgebra.degree_three_perfect_matrix_subgroup_centralizer_metabelian hV B
          (ne_bot_of_mem_cComp hB) (perfect_of_mem_cComp hB)
      have hCle : C ≤ Subgroup.centralizer (B : Set _) := by
        intro c hc
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have : ⁅b, c⁆ ∈ ⁅B, C⁆ := Subgroup.commutator_mem_commutator hb hc
        rw [hBC, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this
      exact not_isSolvable_of_mem_cComp hC (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hCle) (Subgroup.inclusion_injective hCle))
    · exact (eq_of_nonquasisimple_finrank_three hV hC hB hqC).symm
  · exact eq_of_nonquasisimple_finrank_three hV hB hC hqB

end DegreeThree

section Models

open CFSG.Assembly.LowTwoRank

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem fact_ringChar_prime : Fact (ringChar K).Prime :=
  ⟨(CharP.char_is_prime_or_zero K (ringChar K)).resolve_right
    (CharP.char_ne_zero_of_finite K (ringChar K))⟩

theorem cComp_subsingleton_GL (hn : n = 2 ∨ n = 3) (Y : Subgroup (GL (Fin n) K)) :
    (cComp Y).Subsingleton := by
  have := fact_ringChar_prime (K := K)
  set e : GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K) :=
    Matrix.GeneralLinearGroup.toLin
  have hdim : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hsub : (cComp (Y.map e.toMonoidHom)).Subsingleton := by
    rcases hn with rfl | rfl
    · exact (cComp_quasisimple_and_subsingleton_of_finrank_two (p := ringChar K) hdim _).2
    · exact cComp_subsingleton_of_finrank_three (p := ringChar K) hdim _
  have : Finite (GL (Fin n) K) := inferInstance
  have : Finite (LinearMap.GeneralLinearGroup K (Fin n → K)) := finite_GL
  intro L₁ h₁ L₂ h₂
  exact map_injOn_cComp e.toMonoidHom (isSolvable_ker_of_injective _ e.injective) Y h₁ h₂
    (hsub (map_mem_cComp_of_ker _ (isSolvable_ker_of_injective _ e.injective) h₁)
      (map_mem_cComp_of_ker _ (isSolvable_ker_of_injective _ e.injective) h₂))

theorem cComp_subsingleton_statedProj (hn : n = 2 ∨ n = 3) (H : Subgroup (GL (Fin n) K))
    (Y : Subgroup (CFSG.Assembly.LowTwoRank.StatedProj H)) : (cComp Y).Subsingleton := by
  have : Finite (GL (Fin n) K) := inferInstance
  set π : ↥H →* CFSG.Assembly.LowTwoRank.StatedProj H := QuotientGroup.mk' _ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : Group.IsSolvable π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    refine Group.isSolvable_of_comm fun x y => Subtype.ext (Subtype.ext ?_)
    have hx : ((x : ↥H) : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact x.2
    exact (Subgroup.mem_center_iff.mp hx _).symm
  have hY : (Y.comap π).map π = Y := Subgroup.map_comap_eq_self_of_surjective hπs Y
  have hsub : (cComp (Y.comap π)).Subsingleton := by
    intro L₁ h₁ L₂ h₂
    have h := cComp_subsingleton_GL hn ((Y.comap π).map H.subtype)
      (map_mem_cComp_of_ker H.subtype (isSolvable_ker_of_injective _ H.subtype_injective) h₁)
      (map_mem_cComp_of_ker H.subtype (isSolvable_ker_of_injective _ H.subtype_injective) h₂)
    exact map_injOn_cComp H.subtype (isSolvable_ker_of_injective _ H.subtype_injective) _ h₁ h₂ h
  intro L₁ h₁ L₂ h₂
  rw [← hY] at h₁ h₂
  obtain ⟨M₁, hM₁, rfl⟩ := map_surjOn_cComp π hker _ h₁
  obtain ⟨M₂, hM₂, rfl⟩ := map_surjOn_cComp π hker _ h₂
  rw [hsub hM₁ hM₂]

theorem sylowNoDouble_statedProj (hn : n = 2 ∨ n = 3) (H : Subgroup (GL (Fin n) K)) :
    SylowNoDouble (CFSG.Assembly.LowTwoRank.StatedProj H) := fun _ _ Y _ _ =>
  noIsoDouble_of_subsingleton' (cComp_subsingleton_statedProj hn H Y)

end Models

end CFSG.Quasithin.H13.LocDbl
