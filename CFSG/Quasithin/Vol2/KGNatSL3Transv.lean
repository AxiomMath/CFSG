module

public import CFSG.Quasithin.Vol2.KGNatSemiLin
public import CFSG.Quasithin.Vol2.KGNatSL3PointB
public import CFSG.Quasithin.Vol2.Ch11SecCFacts4
public import CFSG.Quasithin.Vol2.KGNatSemi

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)

theorem factTransvPointSL3_holds : Ch11.SecC.FactTransvPointSL3 := by
  intro F _ _ n hn hF W _ _ hW H π hπ S hS y hyN hyy hy1 hcard
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hF (by omega) hf hS
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h => injective_of_bot hf h
  have hy' : ∀ h ∈ H, y⁻¹ * h * y ∈ H := fun h hh => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) h).mp hh
    rwa [inv_inv] at this
  have hyZ : ∀ z ∈ (⊥ : Subgroup W), y z ∈ (⊥ : Subgroup W) := fun z hz => by
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  have hyZ' : ∀ z ∈ (⊥ : Subgroup W), y⁻¹ z ∈ (⊥ : Subgroup W) := fun z hz => by
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  have he0 : (![1, 0, 0] : Fin 3 → F) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSL (by norm_num) T hT)
    he0 y hyZ hyZ' hy'
  set T := hf.autMap y hyZ with hTdef
  have hTf : ∀ w, T (f w) = f (y w) := hf.autMap_apply y hyZ
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
  have hTL : ∀ x, TL x = T x := fun _ => rfl
  have hT1 : ∃ x, TL x ≠ x := by
    by_contra hcon
    push Not at hcon
    apply hy1
    ext w
    exact hinj _ _ ((hTf w).symm.trans (hcon (f w)))
  have hker : Nat.card F ^ 2 ≤ Nat.card (LinearMap.ker (TL - LinearMap.id)) := by
    refine hC2.trans (le_of_eq (Nat.card_congr
      { toFun := fun x => ⟨x.1, ?_⟩
        invFun := fun x => ⟨x.1, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }))
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hTL, mem_fixAdd.mp x.2,
        sub_self]
    · have := x.2
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hTL, sub_eq_zero] at this
      exact this
  obtain ⟨v, hv0, hrange⟩ := exists_span_eq_range_sub TL hT1 hker
  have hge0 : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] ≠ 0 := by
    intro h0
    have := congrArg (fun x => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ x) h0
    simp only [ginv_g_mulVec, Matrix.mulVec_zero] at this
    exact he0 this
  obtain ⟨γ, hγ⟩ := exists_sl3_lin_eq _ v hge0 hv0
  set h : MulAut W := ((π γ : ↥H) : MulAut W) with hhdef
  have hact : ∀ x, f (h x) = (linModelNat (StatedSL 3 F)).lin γ (f x) := hf.act γ
  have hlinj : ∀ a b, (linModelNat (StatedSL 3 F)).lin γ a =
      (linModelNat (StatedSL 3 F)).lin γ b → a = b := by
    intro a b hab
    obtain ⟨a', rfl⟩ := hf.surj a
    obtain ⟨b', rfl⟩ := hf.surj b
    rw [← hact, ← hact] at hab
    rw [h.injective (hinj _ _ hab)]
  have hfixS : ∀ x : W, (∀ s ∈ S, s x = x) ↔ ∃ t : F, f x = t • ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ![1, 0, 0]) := by
    intro x
    rw [← mem_gmap_stdLine_iff, ← fixedW_iff hf hg x]
    simp only [Subgroup.mem_bot, mul_inv_eq_one]
  have hsub : ∀ w' : W,
      (TL - LinearMap.id : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) (f w') = f (y w' * w'⁻¹) := by
    intro w'
    rw [LinearMap.sub_apply, LinearMap.id_apply, hTL, hTf, hf.map_mul_inv]
  refine ⟨h, (π γ).2, fun w => ⟨?_, fun hx => ?_⟩⟩
  · rintro ⟨w', rfl⟩
    rw [hfixS]
    have hmem : f (y w' * w'⁻¹) ∈ LinearMap.range (TL - LinearMap.id) := ⟨f w', hsub w'⟩
    rw [hrange, Submodule.mem_span_singleton] at hmem
    obtain ⟨t, ht⟩ := hmem
    refine ⟨t, hlinj _ _ ?_⟩
    rw [← hact, MulAut.apply_inv_self, LinearMap.map_smul, hγ, ht]
  · obtain ⟨t, ht⟩ := (hfixS _).mp hx
    have hfw : f w = t • v := by
      rw [← MulAut.apply_inv_self W h w, hact, ht, LinearMap.map_smul, hγ]
    have hmem : f w ∈ LinearMap.range (TL - LinearMap.id) := by
      rw [hrange, Submodule.mem_span_singleton]
      exact ⟨t, hfw.symm⟩
    obtain ⟨z, hz⟩ := hmem
    obtain ⟨w', rfl⟩ := hf.surj z
    exact ⟨w', hinj _ _ (by rw [← hsub, hz])⟩

end CFSG.Quasithin.Vol2.KGNat
