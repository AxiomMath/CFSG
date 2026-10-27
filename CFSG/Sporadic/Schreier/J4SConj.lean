
module

public import CFSG.Sporadic.Schreier.J4SConjBase

public import CFSG.Sporadic.Schreier.J4SBinary
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem η_congr
    {i k : ℕ} (h : toVecD 11 i = toVecD 11 k) : η i = η k := by
  rw [η_eq, η_eq, h]

theorem inv_conj_η_of_cols
    {g : J} {C D : Array ℕ} (hC : ∀ a, g * η a * g⁻¹ = η (app11 C a))
    (hCD : comp11 C D = idRows 11) (a : ℕ) : g⁻¹ * η a * g = η (app11 D a) := by
  have e : η (app11 C (app11 D a)) = η a :=
    η_congr (by rw [← toVecD_app11_comp11, hCD, toVecD_app11_idRows])
  have h := hC (app11 D a)
  rw [e] at h
  rw [← h]
  group

theorem x_inv_conj_η
    (a : ℕ) : x⁻¹ * η a * x = η (app11 xInvColumns a) :=
  inv_conj_η_of_cols x_conj_η comp11_x_inv a

theorem y_inv_conj_η
    (a : ℕ) : y⁻¹ * η a * y = η (app11 yInvColumns a) :=
  inv_conj_η_of_cols y_conj_η comp11_y_inv a

theorem letter_conj_η (l : ℤ) (a : ℕ) :
    letter x y l * η a * (letter x y l)⁻¹ = η (letterApp l a) := by
  unfold letter letterApp
  split_ifs
  · exact x_conj_η a
  · rw [inv_inv]; exact x_inv_conj_η a
  · exact y_conj_η a
  · rw [inv_inv]; exact y_inv_conj_η a
  · group

theorem word_conj_η : ∀ (w : List ℤ) (a : ℕ),
    signedWord x y w * η a * (signedWord x y w)⁻¹ = η (app11W w a)
  | [], a => by
    rw [signedWord, List.map_nil, List.prod_nil, app11W]
    group
  | l :: w, a => by
    rw [signedWord, List.map_cons, List.prod_cons, app11W, ← letter_conj_η, ← word_conj_η w a,
      signedWord]
    group

theorem x_mem_normalizer : x ∈ NN :=
  mem_normalizer_N_of fun j => by rw [x_conj_u]; exact η_mem_N _

theorem y_mem_normalizer : y ∈ NN :=
  mem_normalizer_N_of fun j => by rw [y_conj_u]; exact η_mem_N _

theorem K_le_normalizer : K ≤ NN := by
  rw [K, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact x_mem_normalizer
  · exact y_mem_normalizer

theorem H_le_normalizer : H ≤ NN := by
  rw [H, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact x_mem_normalizer
  · exact y_mem_normalizer
  · exact Subgroup.le_normalizer z_mem_N

theorem N_normal_in_H : (N.subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer N_le_H).2 H_le_normalizer

theorem conj_mem_N_of_mem_K
    {k n : J} (hk : k ∈ K) (hn : n ∈ N) : k * n * k⁻¹ ∈ N :=
  ((Subgroup.mem_normalizer_iff.1 (K_le_normalizer hk)) n).1 hn

end CFSG.Sporadic.J4Schreier
