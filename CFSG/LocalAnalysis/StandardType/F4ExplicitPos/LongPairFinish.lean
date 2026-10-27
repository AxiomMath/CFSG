module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSpRoot
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6PairDescent

@[expose] public section

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal

open CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem Matrix

open CFSG.SeitzReduction.F4Pilot

open CFSG.Timmesfeld.ARS.CaseM

open CFSG.StandardType.F4ExplicitPos.Sp6PairDescent

namespace CFSG.StandardType.F4ExplicitPos.LongPairFinish

theorem map_spTrans {n : ℕ} {k Ω : Type} [Field k] [Field Ω] (φ : k →+* Ω)
    (v : Fin n ⊕ Fin n → k) (c : k) :
    (spTrans v c).map φ = spTrans (fun i => φ (v i)) (φ c) := by
  rw [spTrans, spTrans, Matrix.map_add φ (fun a b => map_add φ a b),
    Matrix.map_one φ (map_zero φ) (map_one φ),
    Matrix.map_smul' φ c (spNil v) (fun a b => map_mul φ a b), map_spNil]

theorem map_smul_spNil {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (lam : k) (v₀ : Fin 3 ⊕ Fin 3 → k) :
    (lam • spNil v₀).map (algebraMap k Ω) =
      (algebraMap k Ω lam) • (spNil v₀).map (algebraMap k Ω) :=
  Matrix.map_smul' (algebraMap k Ω) lam (spNil v₀) (fun a b => map_mul _ a b)

theorem card_of_isTransGroup {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {v : Fin n ⊕ Fin n → F} (hv : v ≠ 0) {X : Subgroup (StatedSp n F)}
    (hX : IsTransGroup v X) : Nat.card X = Nat.card F := by
  classical
  have hsp : spNil v ≠ 0 := spNil_ne_zero hv
  let f : F → X := fun c => ⟨Classical.choose (hX.2 c),
    (hX.1 _).mpr ⟨c, Classical.choose_spec (hX.2 c)⟩⟩
  have hf : ∀ c : F, SpExtras.mat n F (f c : StatedSp n F) = spTrans v c :=
    fun c => Classical.choose_spec (hX.2 c)
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · intro c d hcd
    have h1 : spTrans v c = spTrans v d := by rw [← hf c, hcd, hf d]
    rw [spTrans, spTrans] at h1
    have h2 : c • spNil v = d • spNil v := add_left_cancel h1
    have h3 : (c - d) • spNil v = 0 := by rw [sub_smul, h2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hsp)
  · intro x
    obtain ⟨c, hc⟩ := (hX.1 (x : StatedSp n F)).mp x.2
    exact ⟨c, Subtype.ext (SpExtras.mat_injective ((hf c).trans hc.symm))⟩

theorem map_subtype_eq_matTransvGroup_of_isTransGroup {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {v : Fin n ⊕ Fin n → F} {X : Subgroup (StatedSp n F)} (hX : IsTransGroup v X) :
    X.map (StatedSp n F).subtype = matTransvGroup v (Matrix.mulVec (spGram n F) v) := by
  rw [matTransvGroup]
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    obtain ⟨c, hc⟩ := (hX.1 x).mp hx
    exact Subgroup.subset_closure ⟨c, hc.trans (spTrans_eq v c)⟩
  · rw [Subgroup.closure_le]
    rintro g ⟨c, hc⟩
    obtain ⟨x, hx⟩ := hX.2 c
    exact Subgroup.mem_map.mpr ⟨x, (hX.1 x).mpr ⟨c, hx⟩,
      Units.ext (hx.trans ((spTrans_eq v c).trans hc.symm))⟩

theorem long_case_recognition {k Ω : Type} [Field k] [Finite k] [CharP k 2]
    [Field Ω] [Algebra k Ω] [CharP Ω 2]
    {P : Subgroup (StatedSp 3 k)} (hP : Nat.card P = Nat.card k)
    {X : Subgroup (StatedSp 3 Ω)} {v : Fin 3 ⊕ Fin 3 → Ω} (hv : v ≠ 0)
    (hX : IsTransGroup v X)
    (hPX : P.map (statedSpMap (algebraMap k Ω) 3) ≤ X) :
    ∃ v₀ : Fin 3 ⊕ Fin 3 → k, v₀ ≠ 0 ∧ IsTransGroup v₀ P ∧
      ∃ μ : Ω, μ ≠ 0 ∧ spNil v = μ • spNil (fun i => algebraMap k Ω (v₀ i)) := by
  classical
  have hq : 2 ≤ Nat.card k := Finite.one_lt_card
  have hP2 : 2 ≤ Nat.card P := by rw [hP]; exact hq
  have : Nontrivial P := (Finite.one_lt_card_iff_nontrivial).mp hP2
  obtain ⟨r, hr1⟩ := exists_ne (1 : P)
  have hrne : (r : StatedSp 3 k) ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hrX : statedSpMap (algebraMap k Ω) 3 (r : StatedSp 3 k) ∈ X :=
    hPX ⟨r, r.2, rfl⟩
  obtain ⟨t, ht⟩ := (hX.1 _).mp hrX
  have ht0 : t ≠ 0 := by
    intro h0
    have hj1 : statedSpMap (algebraMap k Ω) 3 (r : StatedSp 3 k) = 1 := by
      apply SpExtras.mat_injective
      rw [ht, h0, spTrans_zero, map_one]
    exact hrne (statedSpMap_injective (algebraMap k Ω) 3 (by rw [hj1, map_one]))
  let N₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k :=
    SpExtras.mat 3 k (r : StatedSp 3 k) - 1
  have hmat_map : ∀ x : StatedSp 3 k,
      (SpExtras.mat 3 k x).map (algebraMap k Ω) =
        SpExtras.mat 3 Ω (statedSpMap (algebraMap k Ω) 3 x) := by
    intro x
    rw [SpExtras.mat_apply, SpExtras.mat_apply, coe_statedSpMap, coe_map_GL]
  have hsub_map : ∀ x : StatedSp 3 k,
      (SpExtras.mat 3 k x - 1).map (algebraMap k Ω) =
        (SpExtras.mat 3 k x).map (algebraMap k Ω) - 1 := by
    intro x
    ext p q
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, map_sub]
    by_cases hpq : p = q <;> simp [hpq]
  have hN : N₀.map (algebraMap k Ω) = t • spNil v := by
    show (SpExtras.mat 3 k (r : StatedSp 3 k) - 1).map (algebraMap k Ω) = t • spNil v
    rw [hsub_map, hmat_map, ht, spTrans]
    abel
  obtain ⟨v₀, hv₀, lam, _hlam0, hN₀⟩ := long_support_descent hv ht0 hN
  have hmap : t • spNil v = (algebraMap k Ω lam) •
      spNil (fun i => algebraMap k Ω (v₀ i)) := by
    have h := congrArg (fun M => M.map (algebraMap k Ω)) hN₀
    rw [map_smul_spNil, map_spNil, hN] at h
    exact h
  have hspv : spNil v = ((algebraMap k Ω lam) / t) •
      spNil (fun i => algebraMap k Ω (v₀ i)) := by
    calc spNil v = t⁻¹ • (t • spNil v) := by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
      _ = t⁻¹ • ((algebraMap k Ω lam) •
          spNil (fun i => algebraMap k Ω (v₀ i))) := by rw [hmap]
      _ = ((algebraMap k Ω lam) / t) •
          spNil (fun i => algebraMap k Ω (v₀ i)) := by
            rw [smul_smul]; congr 1; ring
  refine ⟨v₀, hv₀, ?_, ?_⟩
  · let Y : Subgroup (StatedSp 3 k) :=
      { carrier := {x | ∃ c : k, SpExtras.mat 3 k x = spTrans v₀ c}
        mul_mem' := by
          rintro x y ⟨c, hc⟩ ⟨d, hd⟩
          exact ⟨c + d, by rw [map_mul, hc, hd, spTrans_mul]⟩
        one_mem' := ⟨0, by rw [map_one, spTrans_zero]⟩
        inv_mem' := by
          rintro x ⟨c, hc⟩
          refine ⟨c, ?_⟩
          have hxx : x * x = 1 := by
            apply SpExtras.mat_injective
            rw [map_mul, hc, spTrans_mul_self, map_one]
          rw [inv_eq_of_mul_eq_one_right hxx, hc] }
    have hY : IsTransGroup v₀ Y := by
      constructor
      · intro x; rfl
      · intro c
        obtain ⟨x, hx⟩ := CFSG.Timmesfeld.Transvection.ModelRank.exists_mat_eq_spTrans v₀ c
        exact ⟨x, hx⟩
    have hPY : P ≤ Y := by
      intro x hxP
      have hxX : statedSpMap (algebraMap k Ω) 3 x ∈ X := hPX ⟨x, hxP, rfl⟩
      obtain ⟨c, hc⟩ := (hX.1 _).mp hxX
      have hNx : (SpExtras.mat 3 k x - 1).map (algebraMap k Ω) = c • spNil v := by
        rw [hsub_map, hmat_map, hc, spTrans]
        abel
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (spNil_ne_zero hv)
      obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
      have hs : spNil v i j ≠ 0 := hij
      have ha : algebraMap k Ω ((SpExtras.mat 3 k x - 1) i j) = c * spNil v i j := by
        have := congrFun (congrFun hNx i) j
        simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using this
      have hb : algebraMap k Ω ((SpExtras.mat 3 k r - 1) i j) = t * spNil v i j := by
        have := congrFun (congrFun hN i) j
        simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using this
      let a : k := (SpExtras.mat 3 k x - 1) i j
      let b : k := (SpExtras.mat 3 k r - 1) i j
      have hb0 : b ≠ 0 := by
        intro hb0
        have h1 : algebraMap k Ω b = 0 := by rw [hb0, map_zero]
        rw [hb] at h1
        exact (mul_ne_zero ht0 hs) h1
      let c0 : k := a * lam / b
      refine ⟨c0, ?_⟩
      have hd : algebraMap k Ω c0 = c * algebraMap k Ω lam / t := by
        change algebraMap k Ω (a * lam / b) = c * algebraMap k Ω lam / t
        rw [map_div₀, map_mul, ha, hb]
        field_simp
      have hkey : c • spNil v = (algebraMap k Ω c0) •
          spNil (fun i => algebraMap k Ω (v₀ i)) := by
        rw [hspv, hd, smul_smul, mul_div_assoc]
      have hxmap : (SpExtras.mat 3 k x).map (algebraMap k Ω) = 1 + c • spNil v := by
        have h1 : (SpExtras.mat 3 k x).map (algebraMap k Ω) - 1 = c • spNil v := by
          rw [← hNx]
          exact (hsub_map x).symm
        rw [sub_eq_iff_eq_add] at h1
        rw [h1, add_comm]
      apply Matrix.map_injective (algebraMap k Ω).injective
      change (SpExtras.mat 3 k x).map (algebraMap k Ω) =
        (spTrans v₀ c0).map (algebraMap k Ω)
      rw [hxmap, hkey, map_spTrans, spTrans]
    have : Fintype k := Fintype.ofFinite k
    have : Finite (StatedSp 3 k) := Subtype.finite
    have : Finite Y := Subtype.finite
    have hcardY : Nat.card Y = Nat.card k := card_of_isTransGroup hv₀ hY
    have hPYeq : P = Y := Subgroup.eq_of_le_of_card_ge hPY (by rw [hcardY, hP])
    rw [hPYeq]
    exact hY
  · exact ⟨(algebraMap k Ω lam) / t,
      div_ne_zero (fun h => _hlam0 ((algebraMap k Ω).injective (by simpa using h))) ht0, hspv⟩

end CFSG.StandardType.F4ExplicitPos.LongPairFinish

end

end
