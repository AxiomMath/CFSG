module

public import CFSG.Quasithin.Vol2.Ch10SecABasicV
public import CFSG.Quasithin.Vol2.Ch10StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

theorem relIndex_eq_two_pow {V : Subgroup G} (hV : IsPGroup 2 V) (U : Subgroup G) :
    U.relIndex V = 2 ^ E3.mQuot V U := by
  have hdvd := Subgroup.relIndex_dvd_card U V
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥V)).mp hV
  rw [hn, Nat.dvd_prime_pow Nat.prime_two] at hdvd
  obtain ⟨k, -, hk⟩ := hdvd
  rw [E3.mQuot, hk, padicValNat.prime_pow]

theorem le_rParam_of_part_one {T L I K : Subgroup G} (hyp : Hyp10 G T L I)
    (hKV : ⁅fsuVM T L I, K⁆ ≤ fsuVM T L I)
    (h1 : ∀ v ∈ ⁅fsuVM T L I, K⁆, v ≠ 1 →
      Subgroup.centralizer ({v} : Set G) ≤ fsuM T L) :
    ((E3.mQuot ⁅fsuVM T L I, K⁆ ⊥ : ℕ) : ℕ∞) ≤ E3.rParam (fsuVM T L I) := by
  set V := fsuVM T L I
  have hV2 : IsPGroup 2 V := SecA.isPGroup_fsuVM hyp
  have hW2 : IsPGroup 2 (⁅V, K⁆ : Subgroup G) := hV2.to_le hKV
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hUN⟩ := hU
  have hbot : U ⊓ ⁅V, K⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    by_contra hu1
    apply hUN
    intro y hy
    have hyu : y ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Subgroup.mem_centralizer_iff.mp hy u hu.1
    exact SecA.fsuM_le_normalizer_fsuVM T L I (h1 u hu.2 hu1 hyu)
  have hle : U.relIndex ⁅V, K⁆ ≤ U.relIndex V :=
    Subgroup.relIndex_le_of_le_right hKV
      (Subgroup.index_ne_zero_of_finite : (U.subgroupOf V).index ≠ 0)
  rw [← Subgroup.inf_relIndex_right, hbot] at hle
  rw [relIndex_eq_two_pow hW2, relIndex_eq_two_pow hV2] at hle
  exact_mod_cast (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

theorem le_normalizer_of_part_one {T L I K : Subgroup G} (hyp : Hyp10 G T L I)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (hK : IsLi T L K)
    (h1 : ∀ v ∈ ⁅fsuVM T L I, K⁆, v ≠ 1 →
      Subgroup.centralizer ({v} : Set G) ≤ fsuM T L) :
    ∀ v ∈ ⁅fsuVM T L I, K⁆, v ∉ Subgroup.centralizer (fsuL0 T L : Set G) →
      Subgroup.centralizer ({v} : Set G) ≤ fsuM T L ⊓ Subgroup.normalizer (Vi T L I K : Set G) := by
  intro v hv hvL0 c hc
  have hv1 : v ≠ 1 := fun h => hvL0 (h ▸ Subgroup.one_mem _)
  have hcM : c ∈ fsuM T L := h1 v hv hv1 hc
  refine ⟨hcM, ?_⟩
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  have hTM : T ≤ fsuM T L := SecA.le_fsuM T L
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ fsuM T L, K = CFSG.conjugate L r := by
    rcases hK with hK | ⟨s, hs, -, hK⟩
    · exact ⟨1, (fsuM T L).one_mem, hK.trans (SecA.conjugate_one L).symm⟩
    · exact ⟨s, hTM hs, hK⟩
  have hvc : v ∈ ⁅fsuVM T L I, CFSG.conjugate L (r * c)⁆ := by
    have hcomm := SecA.conjugate_commutator (fsuVM T L I) (CFSG.conjugate L r) c
    rw [SecA.conjugate_fsuVM hcM] at hcomm
    rw [← SecA.conjugate_conjugate, ← hcomm]
    have hcv : c⁻¹ * v * c = v := by
      have := Subgroup.mem_centralizer_iff.mp hc v rfl
      rw [mul_assoc, this]
      group
    rw [← hcv]
    exact SecA.conj_mem_conjugate c hv
  have hV1V2 : ⁅fsuVM T L I, L⁆ ⊓ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤
      Subgroup.centralizer (fsuL0 T L : Set G) := fun x hx =>
    ((hdec t ht htn).2.2.2.le ⟨Subgroup.mem_sup_left hx.1, Subgroup.mem_sup_left hx.2⟩).2
  by_cases heq : CFSG.conjugate L (r * c) = CFSG.conjugate L r
  ·
    have hcn : c ∈ Subgroup.normalizer ((CFSG.conjugate L r : Subgroup G) : Set G) := by
      rw [← SecA.conjugate_eq_self_iff, SecA.conjugate_conjugate, heq]
    have hX : Subgroup.normalizer (fsuVM T L I : Set G) ⊓
        Subgroup.normalizer ((CFSG.conjugate L r : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((⁅fsuVM T L I, CFSG.conjugate L r⁆ : Subgroup G) : Set G) :=
      SecA.le_normalizer_commutator inf_le_left inf_le_right
    exact hX ⟨SecA.fsuM_le_normalizer_fsuVM T L I hcM, hcn⟩
  ·
    exfalso
    apply hvL0
    rcases SecA.conjugate_eq_or h37 h38 hyp ht htn hr with hr1 | hr1 <;>
    rcases SecA.conjugate_eq_or h37 h38 hyp ht htn ((fsuM T L).mul_mem hr hcM) with hrc | hrc
    · exact absurd (hrc.trans hr1.symm) heq
    · rw [hr1] at hv
      rw [hrc] at hvc
      exact hV1V2 ⟨hv, hvc⟩
    · rw [hr1] at hv
      rw [hrc] at hvc
      exact hV1V2 ⟨hvc, hv⟩
    · exact absurd (hrc.trans hr1.symm) heq

end CFSG.Quasithin.Vol2.Ch10.SecC
