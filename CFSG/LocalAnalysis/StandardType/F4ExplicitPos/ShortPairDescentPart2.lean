module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSpRoot
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ShortPairDescentPart1

@[expose] public section

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal
open CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem Matrix
open CFSG.SeitzReduction.F4Pilot
open CFSG.Timmesfeld.ARS.CaseM
open CFSG.Timmesfeld.Transvection.ModelRank
open CFSG.StandardType.F4ExplicitPos.Sp6PairDescent

namespace CFSG.StandardType.F4ExplicitPos.ShortPairDescent

theorem eq_smul_of_map_eq_smul_map {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {N₀ N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k} {lam : Ω}
    (h : N₀.map (algebraMap k Ω) = lam • N.map (algebraMap k Ω)) (hN : N ≠ 0) :
    ∃ d : k, N₀ = d • N := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hN
  obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
  have hmapij : algebraMap k Ω (N i j) ≠ 0 :=
    fun h0 => hij ((algebraMap k Ω).injective (by simpa using h0))
  refine ⟨N₀ i j / N i j, ?_⟩
  apply Matrix.map_injective (algebraMap k Ω).injective
  ext p q
  have hpq := congrFun (congrFun h p) q
  have hij' := congrFun (congrFun h i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hpq hij' ⊢
  rw [map_mul, map_div₀, hpq, hij']
  field_simp

theorem short_case_recognition {k Ω : Type} [Field k] [Finite k] [CharP k 2]
    [Field Ω] [Algebra k Ω] [CharP Ω 2]
    {P : Subgroup (StatedSp 3 k)} (hP : Nat.card P = Nat.card k)
    {X : Subgroup (StatedSp 3 Ω)} {a b : Fin 3 ⊕ Fin 3 → Ω}
    (haa : spForm a a = 0) (hbb : spForm b b = 0) (hab : spForm a b = 0)
    (hX : IsAltSiegelGroup a b X)
    (hPX : P.map (statedSpMap (algebraMap k Ω) 3) ≤ X) :
    ∃ (u v : Fin 3 ⊕ Fin 3 → k) (_ : u ≠ 0) (_ : v ≠ 0),
      IsAltSiegelGroup u v P ∧ spForm u u = 0 ∧ spForm v v = 0 ∧ spForm u v = 0 ∧
      (∃ μ : Ω, μ ≠ 0 ∧ altNil a b = μ • altNil
        (fun i => algebraMap k Ω (u i)) (fun i => algebraMap k Ω (v i))) := by
  classical
  have hq : 2 ≤ Nat.card k := Finite.one_lt_card
  have hP2 : 2 ≤ Nat.card P := by rw [hP]; exact hq
  have : Nontrivial P := (Finite.one_lt_card_iff_nontrivial).mp hP2
  obtain ⟨r, hr1⟩ := exists_ne (1 : P)
  have hrne : (r : StatedSp 3 k) ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hrX : statedSpMap (algebraMap k Ω) 3 (r : StatedSp 3 k) ∈ X := hPX ⟨r, r.2, rfl⟩
  obtain ⟨c, hc⟩ := (hX.1 _).mp hrX
  have hc0 : c ≠ 0 := by
    intro h0
    have hj1 : statedSpMap (algebraMap k Ω) 3 (r : StatedSp 3 k) = 1 := by
      apply SpExtras.mat_injective
      rw [hc, h0, zero_smul, add_zero, map_one]
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
  have hN : N₀.map (algebraMap k Ω) = c • altNil a b := by
    show (SpExtras.mat 3 k (r : StatedSp 3 k) - 1).map (algebraMap k Ω) = c • altNil a b
    rw [hsub_map, hmat_map, hc]
    abel
  have hN₀ : N₀ ≠ 0 := by
    intro h0
    apply hrne
    apply SpExtras.mat_injective
    have h1 : SpExtras.mat 3 k (r : StatedSp 3 k) - 1 = 0 := h0
    rw [sub_eq_zero] at h1
    rw [h1, map_one]
  obtain ⟨u, v, hu0, hv0, cu, hcu0, hN₀eq, huu, hvv, huv⟩ :=
    short_support_descent haa hbb hab hc0 hN hN₀
  have hN2 : altNil u v * altNil u v = 0 := by
    rw [altNil_mul_self, huv, huu, hvv]; simp
  have hE : altNil u v ≠ 0 := by
    intro h0
    apply hN₀
    rw [hN₀eq, h0, smul_zero]
  have hNmap : N₀.map (algebraMap k Ω) = (algebraMap k Ω cu) •
      altNil (fun i => algebraMap k Ω (u i)) (fun i => algebraMap k Ω (v i)) := by
    rw [hN₀eq, map_smul_altNil, map_altNil]
  have hμeq : altNil a b = ((algebraMap k Ω cu) / c) •
      altNil (fun i => algebraMap k Ω (u i)) (fun i => algebraMap k Ω (v i)) := by
    calc altNil a b = c⁻¹ • (c • altNil a b) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • N₀.map (algebraMap k Ω) := by rw [← hN]
      _ = c⁻¹ • ((algebraMap k Ω cu) • altNil (fun i => algebraMap k Ω (u i))
            (fun i => algebraMap k Ω (v i))) := by rw [hNmap]
      _ = ((algebraMap k Ω cu) / c) • altNil (fun i => algebraMap k Ω (u i))
            (fun i => algebraMap k Ω (v i)) := by rw [smul_smul]; congr 1; ring
  have hμ0 : ((algebraMap k Ω cu) / c) ≠ 0 :=
    div_ne_zero (fun h0 => hcu0 ((algebraMap k Ω).injective (by simpa using h0))) hc0
  have hPY : P ≤ spAltSiegelSub u v hN2 := by
    intro x hx
    rw [mem_spAltSiegelSub_iff]
    have hxX : statedSpMap (algebraMap k Ω) 3 x ∈ X := hPX ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := (hX.1 _).mp hxX
    have hNx : (SpExtras.mat 3 k x - 1).map (algebraMap k Ω) = e • altNil a b := by
      rw [hsub_map, hmat_map, he]
      abel
    have hlam : (SpExtras.mat 3 k x - 1).map (algebraMap k Ω) =
        (e * ((algebraMap k Ω cu) / c)) • (altNil u v).map (algebraMap k Ω) := by
      rw [hNx, hμeq, smul_smul, map_altNil]
    obtain ⟨d, hd⟩ := eq_smul_of_map_eq_smul_map hlam hE
    refine ⟨d, ?_⟩
    rw [sub_eq_iff_eq_add] at hd
    rw [hd, add_comm]
  have hcardY : Nat.card (spAltSiegelSub u v hN2) = Nat.card k :=
    card_spAltSiegelSub huv hN2 hE
  have hPeq : P = spAltSiegelSub u v hN2 :=
    Subgroup.eq_of_le_of_card_ge hPY (by rw [hcardY, hP])
  refine ⟨u, v, hu0, hv0, ?_, huu, hvv, huv, ⟨(algebraMap k Ω cu) / c, hμ0, hμeq⟩⟩
  rw [hPeq]
  exact ⟨fun x => mem_spAltSiegelSub_iff hN2 x, fun e =>
    ⟨Classical.choose (exists_mat_eq_altNil huv e),
      Classical.choose_spec (exists_mat_eq_altNil huv e)⟩⟩

theorem isAltSiegelGroup_of_map_subtype_eq {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a b : Fin n ⊕ Fin n → F}
    (haa : spForm a a = 0) (hbb : spForm b b = 0) (hab : spForm a b = 0)
    {X : Subgroup (StatedSp n F)}
    (hX : X.map (StatedSp n F).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a b) :
    IsAltSiegelGroup a b X := by
  have hN : altNil a b * altNil a b = 0 := by rw [altNil_mul_self, hab, haa, hbb]; simp
  have hsub := altSiegelGroup_eq_altSiegelSub (F := F) (a := a) (b := b) haa hbb hab
  have hXeq : X = spAltSiegelSub a b hN := by
    rw [spAltSiegelSub, ← hsub, ← hX]
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_comap]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [Subgroup.mem_comap, Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rwa [Subgroup.subtype_injective (StatedSp n F) hyx] at hy
  rw [hXeq]
  exact ⟨fun x => mem_spAltSiegelSub_iff hN x, fun c =>
    ⟨Classical.choose (exists_mat_eq_altNil hab c),
      Classical.choose_spec (exists_mat_eq_altNil hab c)⟩⟩

theorem short_case_recognition_of_altSiegelGroup {k Ω : Type} [Field k] [Finite k] [CharP k 2]
    [Field Ω] [Algebra k Ω] [CharP Ω 2]
    {P : Subgroup (StatedSp 3 k)} (hP : Nat.card P = Nat.card k)
    {X : Subgroup (StatedSp 3 Ω)} {a b : Fin 3 ⊕ Fin 3 → Ω}
    (haa : spForm a a = 0) (hbb : spForm b b = 0) (hab : spForm a b = 0)
    (hX : X.map (StatedSp 3 Ω).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) Ω) a b)
    (hPX : P.map (statedSpMap (algebraMap k Ω) 3) ≤ X) :
    ∃ (u v : Fin 3 ⊕ Fin 3 → k) (_ : u ≠ 0) (_ : v ≠ 0),
      IsAltSiegelGroup u v P ∧ spForm u u = 0 ∧ spForm v v = 0 ∧ spForm u v = 0 ∧
      (∃ μ : Ω, μ ≠ 0 ∧ altNil a b = μ • altNil
        (fun i => algebraMap k Ω (u i)) (fun i => algebraMap k Ω (v i))) :=
  short_case_recognition hP haa hbb hab
    (isAltSiegelGroup_of_map_subtype_eq haa hbb hab hX) hPX

theorem map_subtype_eq_altSiegelGroup_of_isAltSiegelGroup {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a b : Fin n ⊕ Fin n → F} (hab : spForm a b = 0)
    {X : Subgroup (StatedSp n F)} (hX : IsAltSiegelGroup a b X) :
    X.map (StatedSp n F).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a b := by
  have hN : altNil a b * altNil a b = 0 := by
    rw [altNil_mul_self, hab, spForm_self, spForm_self]; simp
  have hsub := altSiegelGroup_eq_altSiegelSub (F := F) (a := a) (b := b)
    (spForm_self a) (spForm_self b) hab
  rw [hsub]
  apply le_antisymm
  · rintro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact (hX.1 x).mp hx
  · intro g hg
    obtain ⟨c, hc⟩ := hg
    rw [Subgroup.mem_map]
    obtain ⟨x, hx⟩ := hX.2 c
    exact ⟨x, (hX.1 x).mpr ⟨c, hx⟩,
      Units.ext (by
        change (SpExtras.mat n F x) = (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        rw [hx, hc])⟩

end CFSG.StandardType.F4ExplicitPos.ShortPairDescent

end

end
