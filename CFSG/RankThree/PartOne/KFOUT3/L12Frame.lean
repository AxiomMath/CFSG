module

public import CFSG.RankThree.PartOne.KFOUT3.L12Plane
public import CFSG.RankThree.PartOne.KF.R12Unitary
public import CFSG.RankThree.PartOne.KF.RowCore
public import CFSG.RankThree.PartOne.KF.R1Model

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem isCentralPQuot_comp_mulEquiv {E P P' : Type} [Group E] [Group P] [Group P'] {p : ℕ}
    {ε : E →* P} (hε : IsCentralPQuot p ε) (α : P ≃* P') :
    IsCentralPQuot p (α.toMonoidHom.comp ε) := by
  have hker : (α.toMonoidHom.comp ε).ker = ε.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    simp
  refine ⟨α.surjective.comp hε.surjective, by rw [hker]; exact hε.central,
    by rw [hker]; exact hε.coprime⟩

section Image

variable {G : Type} [Group G] [Finite G] {L A₀ F : Subgroup G}

theorem image_facts (h : Table123Core 5 L A₀ F) {P : Type} [Group P] (ε : ↥L →* P)
    (hε : IsCentralPQuot 5 ε) :
    Nat.card ((A₀.subgroupOf L).map ε) = 25 ∧
      ∃ S : Subgroup P, S ≠ ⊥ ∧ IsPGroup 2 S ∧
        ∀ a ∈ (A₀.subgroupOf L).map ε, ∀ s ∈ S, a * s * a⁻¹ ∈ S := by
  classical
  obtain ⟨S₀, hS₀L, hS₀ne, hS₀2, hAS₀, hS₀comm⟩ := h.A₀_invariant
  have hA₀pow : ∀ g ∈ A₀, g ^ 5 = 1 := fun g hg => by
    have := h.A₀_elem
    exact elemPow_eq_one_of_isElementaryAbelian g hg
  refine ⟨?_, (S₀.subgroupOf L).map ε, ?_, ?_, ?_⟩
  ·
    have hAinj : Function.Injective (ε.comp (A₀.subgroupOf L).subtype) := by
      intro x y hxy
      have hx5 : ((x : ↥L)) ^ 5 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hA₀pow _ (Subgroup.mem_subgroupOf.mp x.2))
      have hy5 : ((y : ↥L)) ^ 5 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hA₀pow _ (Subgroup.mem_subgroupOf.mp y.2))
      exact Subtype.ext (hε.eq_of_map_eq hx5 hy5 hxy)
    have hrange : (ε.comp (A₀.subgroupOf L).subtype).range = (A₀.subgroupOf L).map ε := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hAinj).toEquiv.symm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.A₀_le).toEquiv, h.A₀_card]
    norm_num
  · intro hbot
    apply hS₀ne
    have hcent : ∀ s ∈ S₀, ∀ a ∈ A₀, s * a = a * s := by
      intro s hs a ha
      have h1 : ε ⟨s, hS₀L hs⟩ = 1 := by
        have : ε ⟨s, hS₀L hs⟩ ∈ (S₀.subgroupOf L).map ε :=
          ⟨⟨s, hS₀L hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
        rw [hbot] at this
        exact this
      have h3 := hε.central (show (⟨s, hS₀L hs⟩ : ↥L) ∈ ε.ker from h1)
      have := Subgroup.mem_center_iff.mp h3 ⟨a, h.A₀_le ha⟩
      exact (congrArg Subtype.val this).symm
    refine hS₀comm.trans (eq_bot_iff.mpr (Subgroup.commutator_le.mpr fun s hs a ha => ?_))
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcent s hs a ha)
  · intro x
    obtain ⟨y, hy, hyx⟩ := x.2
    obtain ⟨k, hk⟩ := hS₀2 ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hy' : y ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [Subgroup.coe_pow, ← hyx, ← map_pow, hy', map_one]
    rfl
  · rintro _ ⟨a₀, ha₀, rfl⟩ _ ⟨s₀, hs₀, rfl⟩
    refine ⟨a₀ * s₀ * a₀⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    have ha₀' := Subgroup.mem_subgroupOf.mp ha₀
    have hs₀' := Subgroup.mem_subgroupOf.mp hs₀
    exact (Subgroup.mem_normalizer_iff.mp (hAS₀ ha₀') _).mp hs₀'

end Image

section Main

variable {f : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem scalarsU_le_torus (hU : UnitaryFieldData 2 f K) :
    scalarsU K f ≤ (torusSU 5 5 K).subgroupOf (unitarySU 2 f K 5) := by
  intro w hw
  have hw' : (w : GL (Fin 5) K) ∈ StatedScalars (Fin 5) K := Subgroup.mem_subgroupOf.mp hw
  obtain ⟨c, hc⟩ := hw'
  have hdet := ((mem_unitarySU_iff hU).mp w.2).1
  have hc5 : c ^ 5 = 1 := by
    rw [← hc] at hdet
    have h2 : ((Matrix.GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = (c : K) • (1 : Matrix (Fin 5) (Fin 5) K) := by
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal]
    rw [h2, det_smul_one_five] at hdet
    exact Units.ext (by simpa using hdet)
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 5) c = diagU (fun _ => c) := by
    apply Units.ext
    rw [diagU_val]
    simp [Matrix.GeneralLinearGroup.scalar]
  rw [Subgroup.mem_subgroupOf, ← hc, h1]
  exact mem_torusSU_iff.mpr ⟨fun _ => c, fun _ => hc5, by simp [Finset.prod_const, hc5], rfl⟩

variable {G : Type} [Group G] [Finite G] {L A₀ F : Subgroup G}

theorem exists_r12plane (h : Table123Core 5 L A₀ F) (hmodel : RowModel 5 L 12) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : UnitaryFieldData 2 f K),
      1 ≤ f ∧ 5 ∣ 2 ^ f + 1 ∧ ¬ 25 ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f ∧
      ∃ ε : ↥L →* StatedProj (unitarySU 2 f K 5), IsCentralPQuot 5 ε ∧
        (A₀.subgroupOf L).map ε = (piSU f K).map (projU K f) := by
  classical
  obtain ⟨-, -, f, hf1, h5, h25, hmod⟩ := hmodel
  have hmod' := hmod
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod'
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot hU Nat.prime_five h5
  have hcop : Nat.Coprime 5 (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h.center_pPrime
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ↥L →* StatedProj (unitarySU 2 f K 5), IsCentralPQuot 5 ε₀ :=
    ⟨_, isCentralPQuot_center e hcop⟩
  obtain ⟨hcard₀, S₁, hS₁ne, hS₁2, hAS₁⟩ := image_facts h ε₀ hε₀
  have hA₀pow : ∀ g ∈ A₀, g ^ 5 = 1 := fun g hg => by
    have := h.A₀_elem
    exact elemPow_eq_one_of_isElementaryAbelian g hg
  have hXe : ∀ x ∈ (A₀.subgroupOf L).map ε₀, x ^ 5 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    have : a ^ 5 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hA₀pow _ (Subgroup.mem_subgroupOf.mp ha))
    rw [this, map_one]
  have hXc : ∀ x ∈ (A₀.subgroupOf L).map ε₀, ∀ y ∈ (A₀.subgroupOf L).map ε₀, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have hc := h.A₀_elem.is_comm.comm ⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩
      ⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩
    exact Subtype.ext (congrArg (fun x : ↥A₀ => (x : G)) hc)
  obtain ⟨α, hα⟩ := toral_conj_of_contains hU h5 h25 ((A₀.subgroupOf L).map ε₀)
    ((A₀.subgroupOf L).map ε₀) S₁ le_rfl hcard₀ hXe hXc hS₁ne hS₁2 hAS₁
  set ε₁ : ↥L →* StatedProj (unitarySU 2 f K 5) := α.toMonoidHom.comp ε₀ with hε₁def
  have hε₁ : IsCentralPQuot 5 ε₁ := isCentralPQuot_comp_mulEquiv hε₀ α
  obtain ⟨hcard₁, S₂, hS₂ne, hS₂2, hAS₂⟩ := image_facts h ε₁ hε₁
  have hA₁T : ∀ x ∈ (A₀.subgroupOf L).map ε₁, x ∈ torusBar K f := by
    rintro _ ⟨a, ha, rfl⟩
    exact hα _ ⟨a, ha, rfl⟩
  set A₁ := (A₀.subgroupOf L).map ε₁ with hA₁def
  set Pt : Subgroup ↥(unitarySU 2 f K 5) := A₁.comap (projU K f) with hPt
  have hPcard : Nat.card Pt = 5 ^ 3 := by
    rw [hPt, card_comap_projU, hcard₁, card_scalarsU hU h5 hz]
    norm_num
  have hPtor : ∀ g ∈ Pt, (g : GL (Fin 5) K) ∈ torusSU 5 5 K := by
    intro g hg
    have hg1 : projU K f g ∈ torusBar K f := hA₁T _ hg
    obtain ⟨g', hg', hgg'⟩ := hg1
    have hzz : g'⁻¹ * g ∈ scalarsU K f := by
      rw [← ker_projU, MonoidHom.mem_ker, map_mul, map_inv, hgg', inv_mul_cancel]
    have hgg : g = g' * (g'⁻¹ * g) := by group
    have hmem : g ∈ (torusSU 5 5 K).subgroupOf (unitarySU 2 f K 5) := by
      rw [hgg]
      exact Subgroup.mul_mem _ hg' (scalarsU_le_torus hU hzz)
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨T, hTne, hT2, hPT⟩ := exists_two_subgroup_lift (projU K f) projU_surjective
    (scalarsU K f) ker_projU scalarsU_le_center S₂ hS₂ne hS₂2 Pt
    (fun a ha s hs => hAS₂ _ ha s hs)
  obtain ⟨σ, hσ⟩ := exists_perm_conj_eq_piSU hU Pt T hPtor hPcard hTne hT2 hPT
  set π : ↥(unitarySU 2 f K 5) := ⟨permGL σ, permGL_mem_unitarySU hU σ⟩ with hπ
  set ε₂ : ↥L →* StatedProj (unitarySU 2 f K 5) :=
    (MulAut.conj (projU K f π)).toMonoidHom.comp ε₁ with hε₂def
  have hε₂ : IsCentralPQuot 5 ε₂ := isCentralPQuot_comp_mulEquiv hε₁ (MulAut.conj (projU K f π))
  refine ⟨f, K, hKf, hKfin, hU, hf1, h5, h25, hmod, ε₂, hε₂, ?_⟩
  have hA₁eq : A₁ = Pt.map (projU K f) :=
    (Subgroup.map_comap_eq_self_of_surjective projU_surjective A₁).symm
  have h2 : (A₀.subgroupOf L).map ε₂ = A₁.map (MulAut.conj (projU K f π)).toMonoidHom := by
    rw [hε₂def, ← Subgroup.map_map]
  rw [h2, hA₁eq, Subgroup.map_map, ← hσ, Subgroup.map_map]
  congr 1

end Main

end CFSG.RankThree.PartOne.KFOUT3
