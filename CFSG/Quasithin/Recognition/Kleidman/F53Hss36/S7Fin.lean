module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open Equiv CFSG.Quasithin.F53Mod

private theorem d_ex : ∀ y : Perm (Fin 5), y 4 ≠ 4 →
    ∃ d ∈ S5SylF, ∃ d' ∈ S5SylF,
      d * y * d' = swap 3 4 ∨ d * y * d' = swap 2 3 * swap 3 4 := by
  decide +kernel


theorem S5g_mem : S5g ∈ S5Syl := Subgroup.subset_closure (Or.inl rfl)

theorem swap02_mem : swap (0 : Fin 5) 2 ∈ S5Syl := Subgroup.subset_closure (Or.inr rfl)

theorem eq_top_of_wordSet (gens : List (Perm (Fin 5))) (k : ℕ)
    (hw : ∀ x : Perm (Fin 5), x ∈ wordSet gens k) {K : Subgroup (Perm (Fin 5))}
    (hK : ∀ g ∈ gens, g ∈ K) : K = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : x ∈ Subgroup.closure {g | g ∈ gens} := wordSet_subset_closure gens k x (hw x)
  exact (Subgroup.closure_le K).mpr (fun g hg => hK g hg) h1

private theorem top_of_words {K : Subgroup (Perm (Fin 5))} {a b z : Perm (Fin 5)}
    (ha : a ∈ K) (hb : b ∈ K) (hz : z ∈ K) (w0 w1 w2 w3 : List (Fin 3))
    (h0 : (w0.map ![a, b, z]).prod = swap 0 1) (h1 : (w1.map ![a, b, z]).prod = swap 1 2)
    (h2 : (w2.map ![a, b, z]).prod = swap 2 3) (h3 : (w3.map ![a, b, z]).prod = swap 3 4) :
    K = ⊤ := by
  have hw : ∀ w : List (Fin 3), (w.map ![a, b, z]).prod ∈ K := by
    intro w
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    fin_cases i
    exacts [ha, hb, hz]
  have m0 := hw w0
  have m1 := hw w1
  have m2 := hw w2
  have m3 := hw w3
  rw [h0] at m0
  rw [h1] at m1
  rw [h2] at m2
  rw [h3] at m3
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submonoid.closure (Set.range fun i : Fin 4 ↦ swap i.castSucc i.succ) := by
    rw [Perm.mclosure_swap_castSucc_succ 4]
    exact Submonoid.mem_top x
  refine (Submonoid.closure_le (S := K.toSubmonoid)).mpr ?_ hx
  rintro _ ⟨i, rfl⟩
  fin_cases i
  exacts [m0, m1, m2, m3]

theorem S5Syl_sup_zpowers_eq_top {y : Perm (Fin 5)} (hy : y 4 ≠ 4) :
    S5Syl ⊔ Subgroup.zpowers y = ⊤ := by
  obtain ⟨d, hd, d', hd', h⟩ := d_ex y hy
  have hdS : d ∈ S5Syl := (mem_S5Syl_iff d).mpr hd
  have hdS' : d' ∈ S5Syl := (mem_S5Syl_iff d').mpr hd'
  have hyK : y ∈ S5Syl ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hz : d * y * d' ∈ S5Syl ⊔ Subgroup.zpowers y :=
    mul_mem (mul_mem (Subgroup.mem_sup_left hdS) hyK) (Subgroup.mem_sup_left hdS')
  have ha := Subgroup.mem_sup_left (T := Subgroup.zpowers y) S5g_mem
  have hb := Subgroup.mem_sup_left (T := Subgroup.zpowers y) swap02_mem
  rcases h with h | h
  · rw [h] at hz
    exact top_of_words ha hb hz [0, 0, 0, 2, 0, 1, 2, 0, 2] [0, 1, 2, 0, 1, 2, 0, 1, 2]
      [1, 2, 0, 1, 2, 0, 2] [2] (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · rw [h] at hz
    exact top_of_words ha hb hz [0, 2, 0, 2, 1] [1, 0, 2, 0, 2] [0, 2, 0, 2, 0]
      [0, 2, 0, 2, 0, 2] (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)


theorem exists_syl_sup_zpowers_eq_top {y : Perm (Fin 5)} (hy : y ≠ 1) :
    ∃ τ : Perm (Fin 5),
      S5Syl.map (MulAut.conj τ).toMonoidHom ⊔ Subgroup.zpowers y = ⊤ := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ i := by
    by_contra h
    push Not at h
    exact hy (Equiv.ext h)
  refine ⟨swap 4 i, ?_⟩
  have hy' : ((swap 4 i)⁻¹ * y * swap 4 i) 4 ≠ 4 := by
    rw [Perm.mul_apply, Perm.mul_apply, swap_apply_left, swap_inv]
    intro h
    have h' : swap 4 i (y i) = swap 4 i i := by
      rw [h, swap_apply_right]
    have := (swap 4 i).injective h'
    exact hi this
  have h1 := S5Syl_sup_zpowers_eq_top hy'
  have h2 := congrArg (Subgroup.map (MulAut.conj (swap 4 i)).toMonoidHom) h1
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top_of_surjective _
    (MulAut.conj (swap 4 i)).surjective] at h2
  have hs : swap (4 : Fin 5) i * swap 4 i = 1 := swap_mul_self _ _
  have hconj : swap 4 i * (swap 4 i * y * swap 4 i) * swap 4 i = y := by
    calc swap 4 i * (swap 4 i * y * swap 4 i) * swap 4 i
        = (swap 4 i * swap 4 i) * y * (swap 4 i * swap 4 i) := by simp only [mul_assoc]
      _ = y := by rw [hs]; simp
  convert h2 using 3
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, swap_inv]
  rw [hconj]

end CFSG.Quasithin.Kleidman.F53Hss36
