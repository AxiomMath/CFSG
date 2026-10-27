module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Ctx
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P53b

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem five_not_fix (F : FanTree Γ G) {x : G} {o p : V} (hord : orderOf x = 5)
    (hxo : x ∈ MulAction.stabilizer G o) (hop : Γ.Adj o p) (hxp : x • p = p) : False := by
  have h2 := F.edge_two o p hop
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h2)
    (⟨x, hxo, MulAction.mem_stabilizer_iff.2 hxp⟩ :
      ↥(MulAction.stabilizer G o ⊓ MulAction.stabilizer G p))
  rw [← Subgroup.orderOf_coe] at hk
  simp only [hord] at hk
  rcases k with _ | k
  · norm_num at hk
  · have : 2 ∣ 5 := by rw [hk]; exact dvd_pow_self 2 (by omega)
    omega

theorem not_comm_five (F : FanTree Γ G) {z : G} {α o : V} (C : LblCtx Γ z α o) {x : G}
    (hord : orderOf x = 5) (hxo : x ∈ MulAction.stabilizer G o) {p q : V} (hp : Γ.Adj o p)
    (hq : Γ.Adj o q) (hpq : p ≠ q)
    (hcomm : x * (Lb z α p * Lb z α q) = (Lb z α p * Lb z α q) * x) : False := by
  have hxo' : x • o = o := MulAction.mem_stabilizer_iff.1 hxo
  have hxp : Γ.Adj o (x • p) := by
    have := (F.adj_smul x o p).2 hp
    rwa [hxo'] at this
  have hxq : Γ.Adj o (x • q) := by
    have := (F.adj_smul x o q).2 hq
    rwa [hxo'] at this
  have e1 := Lb_conj C.cinv (C.conj_ex F hp) x
  have e2 := Lb_conj C.cinv (C.conj_ex F hq) x
  have hW : Lb z α (x • p) * Lb z α (x • q) = Lb z α p * Lb z α q := by
    rw [← e1, ← e2]
    calc x * Lb z α p * x⁻¹ * (x * Lb z α q * x⁻¹) = x * (Lb z α p * Lb z α q) * x⁻¹ := by group
      _ = Lb z α p * Lb z α q := by rw [hcomm]; group
  have hne : x • p ≠ x • q := fun h => hpq (MulAction.injective x h)
  have hx5 : x ^ 5 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  have hnf : ∀ u : V, Γ.Adj o u → x • u ≠ u := fun u hu hxu => five_not_fix F hord hxo hu hxu
  rcases C.two_subset F hxp hxq hp hq hne hpq hW with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact hnf p hp h1
  · have hxx : (x * x) • p = p := by rw [mul_smul, h1, h2]
    have hst : (x * x) ^ 3 ∈ MulAction.stabilizer G p :=
      pow_mem (MulAction.mem_stabilizer_iff.2 hxx) 3
    have hxe : (x * x) ^ 3 = x := by
      calc (x * x) ^ 3 = x ^ 6 := by rw [← pow_two, ← pow_mul]
        _ = x ^ 5 * x := by rw [pow_succ]
        _ = x := by rw [hx5, one_mul]
    rw [hxe] at hst
    exact hnf p hp (MulAction.mem_stabilizer_iff.1 hst)

theorem not_cen_pred (F : FanTree Γ G) (h40 : Fan40 F) (h51a : Fan51a F) (T : Track Γ G)
    {z : G} {a : ℤ} (C : LblCtx Γ z (T.line.vert (a + 1)) (T.line.vert (a + 2))) {p q : V}
    (hp : Γ.Adj (T.line.vert (a + 2)) p) (hq : Γ.Adj (T.line.vert (a + 2)) q) (hpq : p ≠ q)
    (hW1 : Lb z (T.line.vert (a + 1)) p * Lb z (T.line.vert (a + 1)) q ∈
      Cen (T.line.edgeCirc (G := G) (a + 1)))
    (hW2 : Lb z (T.line.vert (a + 1)) p * Lb z (T.line.vert (a + 1)) q ∈
      Cen (T.line.edgeCirc (G := G) (a + 2))) : False := by
  obtain ⟨x, ⟨hxcl, hxst⟩, hxord⟩ := h51a h40 T.line (a + 1) 2 le_rfl
    (not_lineSingLe_of_fan40 h40 T.line (by norm_num)) 1 le_rfl (by norm_num)
  have e1 : a + 1 + ((1 : ℕ) : ℤ) = a + 2 := by push_cast; ring
  have e2 : a + 1 + (((2 - 1 : ℕ)) : ℤ) = a + 2 := by norm_num; ring
  rw [e1] at hxst hxord
  rw [e2] at hxcl
  have hsub : (T.line.edgeCirc (G := G) (a + 1) ∪ T.line.edgeCirc (G := G) (a + 2)) ⊆
      (Subgroup.centralizer {Lb z (T.line.vert (a + 1)) p * Lb z (T.line.vert (a + 1)) q} :
        Subgroup G) := by
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    rcases hs with hs | hs
    · exact (hW1.2 s hs).symm
    · exact (hW2.2 s hs).symm
  have hx := Subgroup.closure_le _ |>.2 hsub hxcl
  rw [Subgroup.mem_centralizer_iff] at hx
  have hx' := hx _ (Set.mem_singleton _)
  exact not_comm_five F C (hxord.trans C.v5) hxst hp hq hpq hx'.symm

end P514

end CFSG.Quasithin.Fan86
