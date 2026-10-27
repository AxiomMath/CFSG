module

public import CFSG.RankThree.PartOne.AUTSL.PushShared
public import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.RankThree.PartOne.AUTSL

theorem relIndex_inf_le_four {R : Type*} [Group R] [Finite R] {I D E : Subgroup R}
    (hID : I ≤ D) (hDE : D ≤ E) (hD2 : ∀ δ ∈ D, δ ^ 2 ∈ I → δ ∈ I) (hDn : D.Normal)
    (hEn : E.Normal) (hcyc : ∃ g ∈ E, ∀ x ∈ E, ∃ k : ℤ, g ^ k * x ∈ D) (hE : E.index ≤ 2)
    {F : Subgroup R} (hF : ∀ x ∈ F, x ^ 2 = 1) : (F ⊓ I).relIndex F ≤ 4 := by
  classical
  have h1 : F ⊓ I = F ⊓ D := by
    refine le_antisymm (inf_le_inf_left _ hID) ?_
    rintro x ⟨hxF, hxD⟩
    exact ⟨hxF, hD2 x hxD (by rw [hF x hxF]; exact I.one_mem)⟩
  rw [h1]
  have h2 : (F ⊓ D).relIndex (F ⊓ E) * (F ⊓ E).relIndex F = (F ⊓ D).relIndex F :=
    Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_inf_left _ hDE) inf_le_left
  have h3 : (F ⊓ E).relIndex F ≤ 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_index_of_normal E F)).trans hE
  have h4 : (F ⊓ D).relIndex (F ⊓ E) ≤ 2 := by
    obtain ⟨g, hgE, hg⟩ := hcyc
    let D' : Subgroup ↥E := D.subgroupOf E
    have : D'.Normal := hDn.subgroupOf E
    have hcycQ : IsCyclic (↥E ⧸ D') := by
      refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun y => ?_⟩⟩
      induction y using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨k, hk⟩ := hg x x.2
        refine Subgroup.mem_zpowers_iff.2 ⟨-k, ?_⟩
        have hmem : ((⟨g, hgE⟩ : ↥E) ^ k * x) ∈ D' := by
          show (((⟨g, hgE⟩ : ↥E) ^ k * x : ↥E) : R) ∈ D
          simpa using hk
        have h1 := (QuotientGroup.eq_one_iff _).2 hmem
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
        rw [zpow_neg]
        exact inv_eq_of_mul_eq_one_right h1
    let ρ : ↥(F ⊓ E) →* ↥E ⧸ D' :=
      (QuotientGroup.mk' D').comp (Subgroup.inclusion (inf_le_right : F ⊓ E ≤ E))
    have hker : ρ.ker = (F ⊓ D).subgroupOf (F ⊓ E) := by
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      show QuotientGroup.mk (⟨(x : R), x.2.2⟩ : ↥E) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff]
      exact ⟨fun h => ⟨x.2.1, h⟩, fun h => h.2⟩
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
    have : Fintype ↥ρ.range := Fintype.ofFinite _
    have hsq : ∀ y : ↥ρ.range, y ^ 2 = 1 := by
      rintro ⟨_, ⟨x, rfl⟩⟩
      apply Subtype.ext
      show ρ x ^ 2 = 1
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (hF x x.2.1)
      rw [this, map_one]
    have hcr : IsCyclic ↥ρ.range := inferInstance
    rw [Nat.card_eq_fintype_card]
    have := IsCyclic.card_pow_eq_one_le (α := ↥ρ.range) (n := 2) two_pos
    have hfilt : (Finset.univ.filter fun a : ↥ρ.range => a ^ 2 = 1) = Finset.univ := by
      ext a
      simp [hsq a]
    rwa [hfilt, Finset.card_univ] at this
  rw [← h2]
  exact (Nat.mul_le_mul h4 h3).trans (by norm_num)

section Projective

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane CFSG.RankThree.PartOne.OutStructure

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem not_two_dvd_gcd : ¬ 2 ∣ Nat.gcd 4 (Nat.card K - 1) := by
  intro h
  have h2 : 2 ∣ Nat.card K - 1 := h.trans (Nat.gcd_dvd_right _ _)
  have := Fintype.ofFinite K
  obtain ⟨f, hp, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [← Nat.card_eq_fintype_card] at hf; exact hf
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have h2K : 2 ∣ Nat.card K := by rw [hK]; exact dvd_pow_self 2 (by omega)
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  omega

theorem outer_bound_projectiveSL (F : Subgroup (MulAut (projectiveSL 4 K)))
    (hF : ∀ x ∈ F, x ^ 2 = 1) :
    (F ⊓ (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range).relIndex F ≤ 4 := by
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) (n := 4) (by norm_num)
  obtain ⟨hID, -, hDn, hEn, -, hcyc, -, hidx, -, -⟩ :=
    standard_outer_quotients (n := 4) (K := K)
  have : Finite (MulAut (projectiveSL 4 K)) := finite_mulAut_projectiveSL 4
  have hnorm : ∀ N : Subgroup (MulAut (projectiveSL 4 K)),
      (N.subgroupOf (standardAutGroup 4 K)).Normal → N.Normal := by
    intro N hN
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup 4 K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup 4 K := hgenTop ▸ Subgroup.mem_top d
    have := hN.conj_mem ⟨d, hd'⟩ (Subgroup.mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hidx' : (semilinearAutGroup 4 K).index ≤ 2 := by
    have h2 : (semilinearAutGroup 4 K).relIndex (standardAutGroup 4 K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  exact relIndex_inf_le_four hID linearAutGroup_le_semilinearAutGroup
    (fun δ hδ h => linear_D2 Nat.prime_two (by norm_num) not_two_dvd_gcd δ hδ 1
      (by rw [pow_one]; exact h))
    (hnorm _ hDn) (hnorm _ hEn) hcyc hidx' hF

theorem map_innL_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    (InnL X).map (MulAut.congr e).toMonoidHom = InnL Y := by
  ext z
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨e a, ?_⟩
    ext w
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · rintro ⟨b, rfl⟩
    refine ⟨MulAut.conj (e.symm b), ⟨e.symm b, rfl⟩, ?_⟩
    ext w
    simp [MulAut.congr_apply, MulAut.conj_apply]

theorem outer_bound_of_equiv {X : Type} [Group X] (e : X ≃* projectiveSL 4 K)
    (F : Subgroup (MulAut X)) (hF : ∀ x ∈ F, x ^ 2 = 1) : (F ⊓ InnL X).relIndex F ≤ 4 := by
  have h1 := outer_bound_projectiveSL (F.map (MulAut.congr e).toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hF x hx, map_one])
  have h2 : (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range =
      (InnL X).map (MulAut.congr e).toMonoidHom := (map_innL_congr e).symm
  rw [h2, ← Subgroup.map_inf _ _ _ (MulAut.congr e).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.congr e).injective] at h1
  exact h1

end Projective

end CFSG.RankThree.PartOne.AUTSL
