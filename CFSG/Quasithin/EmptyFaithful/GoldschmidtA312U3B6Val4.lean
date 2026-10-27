module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3B6Val2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3B6Val3
public import CFSG.RankThree.SubgroupLists.LinearTwoFamily

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.GorensteinWalter CFSG.RankThree.SubgroupLists CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem valentiner_inner {K : Type} [Field K] [Finite K] (h5 : (5 : K) ≠ 0)
    {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 9) (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSL 2 F)) {g : GL (Fin 3) K}
    (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (α : MulAut (H ⧸ Subgroup.center H))
    (hα : ∀ x : H, α (QuotientGroup.mk x) = QuotientGroup.mk ⟨g * x * g⁻¹, hg x x.2⟩) :
    ∃ A : PGL2 F, pgl2InnerAutPSL2 F hK hcard A = MulAut.congr (toPSL2 e) α := by
  obtain ⟨i, hi⟩ := exists_sq_neg_one_card_nine hF
  have hl := sq_add_sub_one_eq_zero hF hi
  set l : F := 1 - i with hldef
  set e' := toPSL2 e with he'
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center hZ hz
  have hP : ¬ 5 ^ 2 ∣ Nat.card (H ⧸ Subgroup.center H) := by
    have h360 : Nat.card (H ⧸ Subgroup.center H) = 360 := by
      rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL_two (p := 9) (by decide) hF]
      norm_num
    rw [h360]
    norm_num
  have h53 : Nat.Coprime 5 3 := by norm_num
  set u₀ := e'.symm (xPSL2 l) with hu₀def
  have hu₀5 : u₀ ^ 5 = 1 := by rw [hu₀def, ← map_pow, xPSL2_pow_five hl, map_one]
  have hu₀1 : u₀ ≠ 1 := fun h => xPSL2_ne_one l (e'.symm.injective (by rw [← hu₀def, h, map_one]))
  obtain ⟨u, hu, hu5⟩ := exists_lift_pow_eq_one le_rfl hZ3 h53 u₀ hu₀5
  have hu1 : u ≠ 1 := fun h => hu₀1 (by rw [← hu, h, QuotientGroup.mk_one])
  have hunc : u ∉ Subgroup.center H := fun h =>
    hu₀1 (by rw [← hu]; exact (QuotientGroup.eq_one_iff u).mpr h)
  have hinv : IsConj u u⁻¹ := by
    refine isConj_of_isConj_mk le_rfl hZ3 h53 hu5 (by rw [inv_pow, hu5, inv_one]) ?_
    rw [QuotientGroup.mk_inv, hu]
    refine isConj_iff.mpr ⟨e'.symm (QuotientGroup.mk' (Subgroup.center SL(2, F)) (wSL2 i hi)), ?_⟩
    have := congrArg e'.symm (xPSL2_conj i l hi)
    rw [hu₀def]
    simpa [map_mul, map_inv] using this
  set v : H := ⟨g * u * g⁻¹, hg u u.2⟩ with hvdef
  have hv5 : v ^ 5 = 1 := by
    apply Subtype.ext
    show (g * (u : GL (Fin 3) K) * g⁻¹) ^ 5 = 1
    rw [conj_pow, ← Subgroup.coe_pow, hu5, Subgroup.coe_one]
    simp
  have hv1 : v ≠ 1 := fun h => hu1 (by
    have h' : g * (u : GL (Fin 3) K) * g⁻¹ = 1 := congrArg Subtype.val h
    have : (u : GL (Fin 3) K) = 1 := by
      calc (u : GL (Fin 3) K) = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = 1 := by rw [h']; group
    exact Subtype.ext this)
  have htr : trH v = trH u := trace_conj_gl g _
  obtain ⟨k, hk⟩ := exists_conj_pow_lift hZ3 hP hu5 hunc hv5 hv1
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_trace_eq h5 hdet hu5 hu1 hv1 hinv hk htr)
  have hβ : (MulAut.congr e') α (xPSL2 l) = (e' (QuotientGroup.mk c))⁻¹ * xPSL2 l *
      ((e' (QuotientGroup.mk c))⁻¹)⁻¹ := by
    have hαu : α u₀ = (QuotientGroup.mk v : H ⧸ Subgroup.center H) := by
      rw [← hu]; exact hα u
    have hv' : (QuotientGroup.mk v : H ⧸ Subgroup.center H) =
        (QuotientGroup.mk c)⁻¹ * u₀ * ((QuotientGroup.mk c)⁻¹)⁻¹ := by
      rw [← hu, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul]
      congr 1
      calc v = c⁻¹ * (c * v * c⁻¹) * c := by group
        _ = c⁻¹ * u * c⁻¹⁻¹ := by rw [hc]; simp
    have hee : e' u₀ = xPSL2 l := by rw [hu₀def]; exact e'.apply_symm_apply _
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    rw [← hu₀def, hαu, hv']
    simp only [map_mul, map_inv, hee]
  exact exists_inner_of_conj hF hK hcard hl _ _ hβ

end CFSG.Quasithin.A312U3
