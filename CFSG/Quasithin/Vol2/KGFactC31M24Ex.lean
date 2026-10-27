module

public import CFSG.Quasithin.Vol2.KGFactC31M24Set
public import CFSG.Quasithin.Vol2.KGFactC31M24Nor

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31 _root_.Certificates

variable {A : Type} [Group A] [Finite A]

theorem false_r2
    {S M₀ R M V : Subgroup A}
    (h : Setup S M₀ R M V) {f : G₀ →* A} (hf : Iso f) (hR : R = (eSub basis_r2).map f) :
    False := by
  have hN : Subgroup.normalizer (R : Set A) = (eNorm basis_r2).map f := by
    rw [hR, hf.map_normalizer]
  have hX : CB0.map f ≤ Subgroup.normalizer (R : Set A) := by
    rw [hN]
    exact Subgroup.map_mono CB0_le
  have hRc : Nat.card R = 16 := by rw [hR, hf.card_map, card_eSub]; norm_num
  rcases card_normalizer_eq hf h.R_ne_bot (by rw [hRc]; norm_num) h.hrad hX
      (by rw [card_CB0]; norm_num) with
    ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
  · rw [hN, hf.card_map] at h1
    have := card_eNorm_r2_le
    omega
  all_goals rw [hRc] at h2; norm_num at h2

theorem false_rt
    {S M₀ R M V : Subgroup A} (h : Setup S M₀ R M V) {f : G₀ →* A} (hf : Iso f)
    (hR : R = (eSub basis_t).map f) : False := by
  have hN : Subgroup.normalizer (R : Set A) = (eNorm basis_t).map f := by
    rw [hR, hf.map_normalizer]
  have hX : Nt.map f ≤ Subgroup.normalizer (R : Set A) := by
    rw [hN]
    exact Subgroup.map_mono Nt_le
  have hRc : Nat.card R = 64 := by rw [hR, hf.card_map, card_eSub]; norm_num
  have hdvd : 64512 ∣ Nat.card (Subgroup.normalizer (R : Set A)) := by
    rw [← card_Nt, ← hf.card_map]
    exact card_dvd_of_le hX
  have hNc : Nat.card (Subgroup.normalizer (R : Set A)) = 64512 := by
    rcases card_normalizer_eq hf h.R_ne_bot (by rw [hRc]; norm_num) h.hrad hX
        (by rw [card_Nt]; norm_num) with
      ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
    · rw [hRc] at h2; norm_num at h2
    · exact h1
    · rw [h1] at hdvd; norm_num at hdvd
    all_goals rw [hRc] at h2; norm_num at h2
  have hq : f qt ∈ Subgroup.normalizer (R : Set A) := by
    rw [hN]
    exact ⟨qt, qt_mem, rfl⟩
  have hqR : f qt ∉ R := by
    rw [hR, Subgroup.mem_map_iff_mem hf.inj]
    exact qt_not_mem
  have hq2 : f qt * f qt ∈ R := by
    rw [hR, ← map_mul]
    exact ⟨qt * qt, qt_sq_mem, rfl⟩
  set K := sectionCent R hq with hK
  have hKq : Kq.map f ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxN, hxq⟩ := Kq_le hx
    refine ⟨?_, ?_⟩
    · rw [hN]
      exact ⟨x, hxN, rfl⟩
    · rw [hR]
      refine ⟨x * qt * x⁻¹ * qt⁻¹, hxq, ?_⟩
      simp [map_mul, map_inv]
  have hKN : K ≤ Subgroup.normalizer (R : Set A) := fun x hx => hx.1
  have hi : K.relIndex (Subgroup.normalizer (R : Set A)) ≤ 4 := by
    have h1 := K.relIndex_mul_card (K := Subgroup.normalizer (R : Set A))
    rw [inf_eq_left.mpr hKN, hNc] at h1
    have h2 : 21504 ≤ Nat.card K := by
      rw [← card_Kq, ← hf.card_map]
      exact Subgroup.card_le_of_le hKq
    by_contra h3
    have h4 : 5 ≤ K.relIndex (Subgroup.normalizer (R : Set A)) := by omega
    have : 5 * 21504 ≤ K.relIndex (Subgroup.normalizer (R : Set A)) * Nat.card K :=
      Nat.mul_le_mul h4 h2
    omega
  have hM₀K : M₀ ≤ K := le_of_perfect_of_relIndex_le h.hM₀R h.hper hi
  exact false_of_sylow_witness h.hR2 h.hMN h.hM₀R h.hsyl h.hNR hq hq2 hqR
    fun m hm => (hM₀K hm).2

end CFSG.Quasithin.KGC31.M24

end
