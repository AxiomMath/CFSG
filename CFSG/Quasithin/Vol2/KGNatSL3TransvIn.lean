module

public import CFSG.Quasithin.Vol2.KGNatPointT
public import CFSG.Quasithin.Vol2.Ch11SecHFacts
public import CFSG.Quasithin.Vol2.KGNatSL3PointB
public import CFSG.Quasithin.Vol2.KGNatSemiLin

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)

theorem factTransvInSL3_holds : Ch11.SecH.FactTransvInSL3 := by
  intro F _ _ n hn hF W _ _ hW H π hπ y hyN hyy hcard
  have : CharP F 2 := charP_two_of_card (by omega) hF
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h => injective_of_bot hf h
  have hy' : ∀ h ∈ H, y⁻¹ * h * y ∈ H := fun h hh => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) h).mp hh
    rwa [inv_inv] at this
  have he0 : (![1, 0, 0] : Fin 3 → F) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSL (by norm_num) T hT)
    he0 y (bot_maps y) (bot_maps y⁻¹) hy'
  set T := hf.autMap y (bot_maps y) with hTdef
  have hTf : ∀ w, T (f w) = f (y w) := hf.autMap_apply y (bot_maps y)
  have hfix : Nat.card (fixAdd T) = Nat.card {w : W // y w = w} := by
    refine (Nat.card_congr (Equiv.ofBijective (fun w : {w : W // y w = w} =>
      (⟨f w, ?_⟩ : fixAdd T)) ⟨?_, ?_⟩)).symm
    · rw [mem_fixAdd, hTf, w.2]
    · intro a b hab
      exact Subtype.ext (hinj _ _ (congrArg Subtype.val hab))
    · rintro ⟨x, hx⟩
      obtain ⟨w, rfl⟩ := hf.surj x
      exact ⟨⟨w, hinj _ _ ((hTf w).symm.trans hx)⟩, rfl⟩
  have hW3 : Nat.card W = Nat.card F ^ 3 := by
    rw [Nat.card_congr (Equiv.ofBijective f ⟨fun a b h => hinj a b h, hf.surj⟩), Nat.card_fun,
      Nat.card_fin]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hC2 : Nat.card F ^ 2 ≤ Nat.card (fixAdd T) := by
    rw [hfix]
    have h1 : Nat.card F ^ 3 ≤ Nat.card F * Nat.card {w : W // y w = w} := by
      rw [← hW3, hF]
      exact hcard
    rw [pow_succ'] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have hσid : ∀ c, σ c = c := semilinear_eq_id_of_card_fix hσ (by
    rw [Nat.card_fun, Nat.card_fin]
    calc Nat.card F ^ 3 < Nat.card F ^ 4 := Nat.pow_lt_pow_right hq (by norm_num)
      _ = (Nat.card F ^ 2) ^ 2 := by ring
      _ ≤ Nat.card (fixAdd T) ^ 2 := Nat.pow_le_pow_left hC2 2)
  let TL : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := T
      map_add' := map_add T
      map_smul' := fun c x => by rw [hσ, hσid]; rfl }
  have hTT : TL.comp TL = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨w, rfl⟩ := hf.surj x
    change T (T (f w)) = f w
    rw [hTf, hTf, ← MulAut.mul_apply, hyy, MulAut.one_apply]
  set A := LinearMap.toMatrix' TL with hA
  have hAA : A * A = 1 := by
    rw [hA, ← LinearMap.toMatrix'_comp, hTT, LinearMap.toMatrix'_id]
  have hdet : A.det = 1 := by
    have h1 : A.det * A.det = 1 := by rw [← Matrix.det_mul, hAA, Matrix.det_one]
    have h2z : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have h3 : (A.det + 1) ^ 2 = 0 := by linear_combination h1 + A.det * h2z + h2z
    have h4 := pow_eq_zero_iff two_ne_zero |>.mp h3
    linear_combination h4 - h2z
  set B : Matrix.SpecialLinearGroup (Fin 3) F := ⟨A, hdet⟩
  have hyB : y = ((rho3 π B : ↥H) : MulAut W) := by
    ext w
    apply hinj
    rw [hf.act3, ← hTf]
    change TL (f w) = A *ᵥ f w
    rw [hA, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rw [hyB]
  exact (rho3 π B).2

end CFSG.Quasithin.Vol2.KGNat
