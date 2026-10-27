module

public import CFSG.Quasithin.Background.Sp4InfA6Gen
public meta import CFSG.Quasithin.Background.Sp4InfA6Basic
public import CFSG.Quasithin.Background.Sp4InfAbs
public import Certificates.Certificate8065
public import Certificates.Certificate8066
public import Certificates.Certificate8067
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.Quasithin

namespace Sp4Inf

open Equiv Pointwise

theorem s0_le_q1 : s0 ≤ q1 := inf_le_left

theorem s0_le_q2 : s0 ≤ q2 := inf_le_right

theorem s0_le_alt : s0 ≤ alternatingGroup (Fin 6) := s0_le_q1.trans q1_le_alt

theorem exists_not_mem_q1 :
    ∃ y : Perm (Fin 6), y ∈ alternatingGroup (Fin 6) ∧ y ∉ q1 :=
  Certificates.certificate8065.1

theorem exists_not_mem_q2 :
    ∃ y : Perm (Fin 6), y ∈ alternatingGroup (Fin 6) ∧ y ∉ q2 :=
  Certificates.certificate8065.2.1

theorem exists_conj_s0
    {S : Subgroup (Perm (Fin 6))} (hS : S ≤ alternatingGroup (Fin 6))
    (hcard : Nat.card S = 8) :
    ∃ h ∈ alternatingGroup (Fin 6), S = s0.map (MulAut.conj h).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := alternatingGroup (Fin 6) with hA
  have hcardA : Nat.card ↥A = 360 := card_alt_six'
  have hSyl : ∀ T : Subgroup (Perm (Fin 6)), T ≤ A → Nat.card T = 8 →
      ∃ P : Sylow 2 ↥A, (P : Subgroup ↥A) = T.subgroupOf A := by
    intro T hT hTc
    have hc : Nat.card ↥(T.subgroupOf A) = 8 := by
      rw [← hTc]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv)
    have hp : IsPGroup 2 ↥(T.subgroupOf A) := IsPGroup.of_card (n := 3) (by rw [hc]; norm_num)
    have hi : ¬ 2 ∣ (T.subgroupOf A).index := by
      have h1 := (T.subgroupOf A).card_mul_index
      rw [hc, hcardA] at h1
      have : (T.subgroupOf A).index = 45 := by omega
      rw [this]
      norm_num
    exact ⟨hp.toSylow hi, rfl⟩
  obtain ⟨P₁, hP₁⟩ := hSyl S hS hcard
  obtain ⟨P₂, hP₂⟩ := hSyl s0 s0_le_alt card_s0
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥A P₂ P₁
  refine ⟨(h : Perm (Fin 6)), h.2, ?_⟩
  ext x
  constructor
  · intro hx
    have hxA : x ∈ A := hS hx
    have hmem : (⟨x, hxA⟩ : ↥A) ∈ (P₁ : Subgroup ↥A) := by rw [hP₁]; exact hx
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
    obtain ⟨b, hb, hbx⟩ := hmem
    rw [hP₂] at hb
    refine ⟨(b : Perm (Fin 6)), hb, ?_⟩
    have := congrArg Subtype.val hbx
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  · rintro ⟨b, hb, rfl⟩
    have hbA : b ∈ A := s0_le_alt hb
    have hb' : (⟨b, hbA⟩ : ↥A) ∈ (P₂ : Subgroup ↥A) := by rw [hP₂]; exact hb
    have hmem : (MulAut.conj h) • (⟨b, hbA⟩ : ↥A) ∈ ((h • P₂ : Sylow 2 ↥A) : Subgroup ↥A) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨⟨b, hbA⟩, hb', rfl⟩
    rw [hh, hP₁] at hmem
    exact Subgroup.mem_subgroupOf.mp (by simpa [MulAut.smul_def, MulAut.conj_apply] using hmem)

theorem exists_two_parabolics_alt6
    {S : Subgroup (Perm (Fin 6))} (hS : S ≤ alternatingGroup (Fin 6))
    (hcard : Nat.card S = 8) :
    ∃ Q₁ Q₂ : Subgroup (Perm (Fin 6)), Q₁ ≤ alternatingGroup (Fin 6) ∧ Q₂ ≤ alternatingGroup (Fin 6) ∧
      Q₁ ≠ alternatingGroup (Fin 6) ∧ Q₂ ≠ alternatingGroup (Fin 6) ∧
      Q₁ ⊔ Q₂ = alternatingGroup (Fin 6) ∧ S ≤ Q₁ ∧ S ≤ Q₂ ∧
      ∀ g : Perm (Fin 6), (∀ x ∈ S, g * x * g⁻¹ ∈ S) →
        (∀ x ∈ Q₁, g * x * g⁻¹ ∈ Q₁) ∧ ∀ x ∈ Q₂, g * x * g⁻¹ ∈ Q₂ := by
  obtain ⟨h, hhA, rfl⟩ := exists_conj_s0 hS hcard
  have hmapA : (alternatingGroup (Fin 6)).map (MulAut.conj h).toMonoidHom =
      alternatingGroup (Fin 6) := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Perm.mem_alternatingGroup]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp [hy]
    · intro hx
      refine ⟨h⁻¹ * x * h, ?_, by group⟩
      simp [hx]
  have hle : ∀ Q : Subgroup (Perm (Fin 6)), Q ≤ alternatingGroup (Fin 6) →
      Q.map (MulAut.conj h).toMonoidHom ≤ alternatingGroup (Fin 6) := fun Q hQ => by
    rw [← hmapA]
    exact Subgroup.map_mono hQ
  refine ⟨q1.map (MulAut.conj h).toMonoidHom, q2.map (MulAut.conj h).toMonoidHom, hle _ q1_le_alt,
    hle _ q2_le_alt, ?_, ?_, ?_, Subgroup.map_mono s0_le_q1, Subgroup.map_mono s0_le_q2, ?_⟩
  · intro hq
    obtain ⟨y, hyA, hy⟩ := exists_not_mem_q1
    have : h * y * h⁻¹ ∈ q1.map (MulAut.conj h).toMonoidHom := by
      rw [hq, ← hmapA]
      exact ⟨y, hyA, by simp [MulAut.conj_apply]⟩
    obtain ⟨z, hz, hzy⟩ := this
    apply hy
    have : z = y := by
      have := congrArg (fun w => h⁻¹ * w * h) hzy
      simpa [MulAut.conj_apply, mul_assoc] using this
    rwa [← this]
  · intro hq
    obtain ⟨y, hyA, hy⟩ := exists_not_mem_q2
    have : h * y * h⁻¹ ∈ q2.map (MulAut.conj h).toMonoidHom := by
      rw [hq, ← hmapA]
      exact ⟨y, hyA, by simp [MulAut.conj_apply]⟩
    obtain ⟨z, hz, hzy⟩ := this
    apply hy
    have : z = y := by
      have := congrArg (fun w => h⁻¹ * w * h) hzy
      simpa [MulAut.conj_apply, mul_assoc] using this
    rwa [← this]
  · rw [← Subgroup.map_sup, sup_eq_alt, hmapA]
  · intro g hg
    have hg' : ∀ x, bs0 x = true → bs0 (h⁻¹ * g * h * x * (h⁻¹ * g * h)⁻¹) = true := by
      intro x hx
      have hxs : x ∈ s0 := (mem_s0 x).2 hx
      have h1 : h * x * h⁻¹ ∈ s0.map (MulAut.conj h).toMonoidHom := ⟨x, hxs, by simp [MulAut.conj_apply]⟩
      have h2 := hg _ h1
      obtain ⟨y, hy, hyx⟩ := h2
      have : y = h⁻¹ * g * h * x * (h⁻¹ * g * h)⁻¹ := by
        have := congrArg (fun w => h⁻¹ * w * h) hyx
        simpa [MulAut.conj_apply, mul_assoc] using this
      rw [← this]
      exact (mem_s0 y).1 hy
    obtain ⟨hf1, hf2⟩ := fix_of_normalizes_s0 (h⁻¹ * g * h) hg'
    constructor
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨h⁻¹ * g * h * y * (h⁻¹ * g * h)⁻¹, (mem_q1 _).2 (hf1 y ((mem_q1 y).1 hy)), ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨h⁻¹ * g * h * y * (h⁻¹ * g * h)⁻¹, (mem_q2 _).2 (hf2 y ((mem_q2 y).1 hy)), ?_⟩
      simp [MulAut.conj_apply, mul_assoc]

@[expose] def InducedByS6 (φ : MulAut ↥(alternatingGroup (Fin 6))) : Prop :=
  ∃ g : Perm (Fin 6), ∀ x : ↥(alternatingGroup (Fin 6)),
    ((φ x : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) = g * x * g⁻¹

theorem card_sylow_alt6
    (S : Sylow 2 ↥(alternatingGroup (Fin 6))) :
    Nat.card ((S : Subgroup ↥(alternatingGroup (Fin 6))).map (alternatingGroup (Fin 6)).subtype) = 8 := by
  rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective,
    Sylow.card_eq_multiplicity, card_alt_six', Nat.factorization_def _ Nat.prime_two]
  exact Certificates.certificate8065.2.2

theorem exists_two_parabolics_alt6'
    (S : Sylow 2 ↥(alternatingGroup (Fin 6))) :
    ∃ Q₁ Q₂ : Subgroup ↥(alternatingGroup (Fin 6)), Q₁ ≠ ⊤ ∧ Q₂ ≠ ⊤ ∧ Q₁ ⊔ Q₂ = ⊤ ∧
      (S : Subgroup ↥(alternatingGroup (Fin 6))) ≤ Q₁ ∧ (S : Subgroup ↥(alternatingGroup (Fin 6))) ≤ Q₂ ∧
      ∀ φ : MulAut ↥(alternatingGroup (Fin 6)),
        (S : Subgroup ↥(alternatingGroup (Fin 6))).map (φ : ↥(alternatingGroup (Fin 6)) →* _) =
          (S : Subgroup ↥(alternatingGroup (Fin 6))) →
        InducedByS6 φ →
          Q₁.map (φ : ↥(alternatingGroup (Fin 6)) →* _) = Q₁ ∧
            Q₂.map (φ : ↥(alternatingGroup (Fin 6)) →* _) = Q₂ := by
  have hfinj : Function.Injective (alternatingGroup (Fin 6)).subtype :=
    (alternatingGroup (Fin 6)).subtype_injective
  have hS'A : (S : Subgroup ↥(alternatingGroup (Fin 6))).map (alternatingGroup (Fin 6)).subtype ≤
      alternatingGroup (Fin 6) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨Q₁, Q₂, hQ₁A, hQ₂A, hQ₁ne, hQ₂ne, hsup, hS₁, hS₂, hfix⟩ :=
    exists_two_parabolics_alt6 hS'A (card_sylow_alt6 S)
  have hmapcomap : ∀ Q : Subgroup (Perm (Fin 6)), Q ≤ alternatingGroup (Fin 6) →
      (Q.comap (alternatingGroup (Fin 6)).subtype).map (alternatingGroup (Fin 6)).subtype = Q :=
    fun Q hQ => by
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_eq_right.2 hQ
  have hne : ∀ Q : Subgroup (Perm (Fin 6)), Q ≤ alternatingGroup (Fin 6) → Q ≠ alternatingGroup (Fin 6) →
      Q.comap (alternatingGroup (Fin 6)).subtype ≠ ⊤ := fun Q hQ hQne h => by
    apply hQne
    refine le_antisymm hQ fun x hx => ?_
    have : (⟨x, hx⟩ : ↥(alternatingGroup (Fin 6))) ∈ Q.comap (alternatingGroup (Fin 6)).subtype := by
      rw [h]
      trivial
    exact this
  refine ⟨Q₁.comap (alternatingGroup (Fin 6)).subtype, Q₂.comap (alternatingGroup (Fin 6)).subtype,
    hne Q₁ hQ₁A hQ₁ne, hne Q₂ hQ₂A hQ₂ne, ?_, ?_, ?_, ?_⟩
  · apply Subgroup.map_injective hfinj
    rw [Subgroup.map_sup, hmapcomap Q₁ hQ₁A, hmapcomap Q₂ hQ₂A, hsup, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro x hx
    exact hS₁ ⟨x, hx, rfl⟩
  · intro x hx
    exact hS₂ ⟨x, hx, rfl⟩
  · rintro φ hφS ⟨g, hg⟩
    have hnorm : ∀ x ∈ (S : Subgroup ↥(alternatingGroup (Fin 6))).map
        (alternatingGroup (Fin 6)).subtype, g * x * g⁻¹ ∈ (S : Subgroup ↥(alternatingGroup (Fin 6))).map
        (alternatingGroup (Fin 6)).subtype := by
      rintro _ ⟨y, hy, rfl⟩
      have : φ y ∈ (S : Subgroup ↥(alternatingGroup (Fin 6))).map (φ : ↥(alternatingGroup (Fin 6)) →* _) :=
        ⟨y, hy, rfl⟩
      rw [hφS] at this
      refine ⟨φ y, this, ?_⟩
      exact hg y
    obtain ⟨h1, h2⟩ := hfix g hnorm
    have key : ∀ Q : Subgroup (Perm (Fin 6)), (∀ x ∈ Q, g * x * g⁻¹ ∈ Q) →
        (Q.comap (alternatingGroup (Fin 6)).subtype).map (φ : ↥(alternatingGroup (Fin 6)) →* _) =
          Q.comap (alternatingGroup (Fin 6)).subtype := by
      intro Q hQ
      have hle : (Q.comap (alternatingGroup (Fin 6)).subtype).map
          (φ : ↥(alternatingGroup (Fin 6)) →* _) ≤ Q.comap (alternatingGroup (Fin 6)).subtype := by
        rintro _ ⟨y, hy, rfl⟩
        have : ((φ y : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) = g * y * g⁻¹ := hg y
        show ((φ y : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) ∈ Q
        rw [this]
        exact hQ _ hy
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective φ.injective]
    exact ⟨key Q₁ h1, key Q₂ h2⟩

theorem swapGeo_alt6 :
    B69.SwapGeo ↥(alternatingGroup (Fin 6)) InducedByS6 :=
  B69.swapGeo_of_two_parabolics fun S => exists_two_parabolics_alt6' S

end Sp4Inf

end CFSG.Quasithin
