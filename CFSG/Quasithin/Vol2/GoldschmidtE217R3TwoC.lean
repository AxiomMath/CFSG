module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Star
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3L2
public import CFSG.Quasithin.Vol2.Ch3E213MOS12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.GLS.IVK CFSG.GH74.GLS B6 E2P Ch3E213M

namespace E217R3

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

theorem asHyp_star' (hmp : MinParabolic H T M) (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hC2 : Case2 H T M K) (hsimp : IsSimpleGroup ↥(E2.star M H K))
    (hZ : Subgroup.center ↥(E2.star M H K) = ⊥)
    (hnab : ∃ a b : ↥(E2.star M H K), a * b ≠ b * a) :
    E2P.ASHyp (E2.star M H K) (E2.star M H T) (E2.star M H M) := by
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hHK' : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hC2.1
  have hmp' := minParabolic_star hmp
  have hn := OS.normal_star (M := M) hKH hHK'
  have hsup := OS.star_sup_eq_top (M := M) hHK
  exact ⟨hmp', hn, hsimp, hnab, hsup, OS.centralizer_eq_bot hmp' (kerIn_star M H) hn hZ hsup⟩

theorem asHyp_star_of_psl2 (hmp : MinParabolic H T M) (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hC2 : Case2 H T M K) {p e : ℕ} (hp3 : 3 < p) (he : e = 1 ∨ e = 2)
    (hpsl : IsPSL 2 p e ↥(E2.star M H K)) :
    E2P.ASHyp (E2.star M H K) (E2.star M H T) (E2.star M H M) := by
  obtain ⟨-, F, _, _, hcard, ⟨e₀⟩⟩ := id hpsl
  have he0 : e ≠ 0 := by omega
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    exact lt_of_lt_of_le hp3 (Nat.le_self_pow he0 p)
  have : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hsimp : IsSimpleGroup ↥(E2.star M H K) := (e₀.trans (L2.equivPSL F)).isSimpleGroup
  have hinj := conj_injective_of_L2 e₀
  have hZ : Subgroup.center ↥(E2.star M H K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply hinj
    rw [map_one]
    ext y
    have h := (Subgroup.mem_center_iff.mp hx) y
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h, mul_inv_cancel_right]
  have hnab : ∃ a b : ↥(E2.star M H K), a * b ≠ b * a := by
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥(E2.star M H K))
    have hca : MulAut.conj a ≠ 1 := fun h => ha (hinj (by rw [h, map_one]))
    obtain ⟨b, hb⟩ : ∃ b, MulAut.conj a b ≠ b := by
      by_contra hcon
      exact hca (MulEquiv.ext fun b => not_not.mp fun h => hcon ⟨b, h⟩)
    refine ⟨a, b, fun h => hb ?_⟩
    rw [MulAut.conj_apply, h, mul_inv_cancel_right]
  exact asHyp_star' hmp hKc hHK hC2 hsimp hZ hnab

theorem card_eq_seven_of_twoC (h12 : IVK_1_2_general) (h13a : IVK_1_3a) (h13b : IVK_1_3b)
    (hcoat : ∀ (F : Type) [Field F] [Finite F], L2Field F → 11 ≤ Nat.card F →
      ∀ (L : Type) [Group L] [Finite L], (L ≃* L2 F) → ∀ u : L, orderOf u = 2 →
        IsCoatom (Subgroup.centralizer ({u} : Set L)))
    (h : Hyp2 H T M V) (hKc : K ∈ cComp H) (hHK : H = K ⊔ T) (hC2 : Case2 H T M K) {p e : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (he : e = 1 ∨ e = 2) (hp8 : p ^ e % 8 = 1 ∨ p ^ e % 8 = 7)
    (hpsl : IsPSL 2 p e ↥(E2.star M H K))
    (hMK : E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)))
    (hAut : 8 < E2.autCard (E2.star M H T) (E2.star M H K)) : p ^ e = 7 := by
  have hmp := h.hyp.minParabolic
  have hX := asHyp_star_of_psl2 hmp hKc hHK hC2 hp3 he hpsl
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTK : E2.star M H (T ⊓ K) = E2.star M H T ⊓ E2.star M H K :=
    star_inf_T hmp.isSylow hKc.2.2.1 hKH
  have hMK' : E2.star M H M ⊓ E2.star M H K = E2.star M H K ⊓
      Subgroup.centralizer (zOf (E2.star M H T ⊓ E2.star M H K) : Set (E2.StarQuot M H)) := by
    rw [← star_inf_M, hMK, ← hTK]
    rfl
  obtain ⟨v, hv2, hv1, hvT, hvM, hodd⟩ := exists_vbar h
  exact (card_eq_seven_of_asHyp h12 h13a h13b hcoat hX hp hp3 he hp8 hpsl hMK' hAut hv2 hv1 hvT
    hvM hodd).1

end E217R3

end CFSG.Quasithin
