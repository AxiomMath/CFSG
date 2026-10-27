module

public import CFSG.LocalAnalysis.StandardType.GGReeB2PairDefs
public import CFSG.LocalAnalysis.StandardType.GGReeB2WeightDefs
public import CFSG.Quasithin.Background.SmithB45SzSplit
public import CFSG.LinearAlgebra.CoprimeActions.AbelianCoprimeWeightSpaceDecomposition
public import CFSG.RepresentationTheory.SzMartineau.Weights

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.X7 CFSG.Blueprint CFSG.LieType.Ree
  CFSG.Quasithin.B45Sz CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.RepresentationTheory.SzMartineau
open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

@[expose] def szIdx (m : ℕ) (J : Finset (Fin (2 * m + 1))) : Finset ℕ :=
  J.image fun j : Fin (2 * m + 1) => 2 * (j : ℕ)

theorem szIdx_subset_szOmega {m : ℕ} (J : Finset (Fin (2 * m + 1))) : szIdx m J ⊆ szOmega m := by
  intro i hi
  rw [szIdx, Finset.mem_image] at hi
  obtain ⟨j, -, rfl⟩ := hi
  rw [mem_szOmega]
  exact ⟨(j : ℕ), j.isLt, rfl⟩

theorem exists_szIdx_eq {m : ℕ} {A : Finset ℕ} (hA : A ⊆ szOmega m) :
    ∃ J : Finset (Fin (2 * m + 1)), szIdx m J = A := by
  refine ⟨Finset.univ.filter fun j : Fin (2 * m + 1) => 2 * (j : ℕ) ∈ A, ?_⟩
  ext i
  rw [szIdx, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    have hjA : 2 * (j : ℕ) ∈ A := (Finset.mem_filter.mp hj).2
    simpa [hji] using hjA
  · intro hi
    obtain ⟨c, hc, hci⟩ := mem_szOmega.mp (hA hi)
    refine ⟨⟨c, hc⟩, ⟨?_, hci⟩⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hci]; exact hi⟩

theorem wchar1_injective {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type) [Field k]
    [Algebra K k] (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Function.Injective (wchar1 (K := K) k : ZMod (2 ^ (2 * m + 1) - 1) → (Kˣ →* kˣ)) := by
  classical
  intro x y hxy
  obtain ⟨g, hgen⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hg : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hgen
  have hcard : Nat.card Kˣ = 2 ^ (2 * m + 1) - 1 := by rw [Nat.card_units, hK]
  have hρinj : Function.Injective (Units.map (algebraMap K k : K →* k)) :=
    Units.map_injective (RingHom.injective (algebraMap K k : K →+* k))
  have hord : orderOf (Units.map (algebraMap K k : K →* k) g) = 2 ^ (2 * m + 1) - 1 := by
    rw [orderOf_injective _ hρinj g, hg, hcard]
  have hval : (Units.map (algebraMap K k : K →* k) g) ^ x.val =
      (Units.map (algebraMap K k : K →* k) g) ^ y.val := by
    have h := congrArg (fun f : Kˣ →* kˣ => f g) hxy
    simpa only [wchar1, MonoidHom.pow_apply] using h
  have hmod : x.val % (2 ^ (2 * m + 1) - 1) = y.val % (2 ^ (2 * m + 1) - 1) := by
    have h := pow_inj_mod.mp hval
    rwa [hord] at h
  rw [Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.mod_eq_of_lt (ZMod.val_lt y)] at hmod
  exact ZMod.val_injective _ hmod

theorem exists_wchar1_eq {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type) [Field k]
    [Algebra K k] [CharP k 2] [IsAlgClosed k] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (χ : Kˣ →* kˣ) : ∃ x : ZMod (2 ^ (2 * m + 1) - 1), wchar1 (K := K) k x = χ := by
  classical
  obtain ⟨g, hgen⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hg : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hgen
  have hcard : Nat.card Kˣ = 2 ^ (2 * m + 1) - 1 := by rw [Nat.card_units, hK]
  have hρinj : Function.Injective (Units.map (algebraMap K k : K →* k)) :=
    Units.map_injective (RingHom.injective (algebraMap K k : K →+* k))
  have hord : orderOf (Units.map (algebraMap K k : K →* k) g) = 2 ^ (2 * m + 1) - 1 := by
    rw [orderOf_injective _ hρinj g, hg, hcard]
  have hζ : IsPrimitiveRoot (Units.map (algebraMap K k : K →* k) g)
      (2 ^ (2 * m + 1) - 1) := IsPrimitiveRoot.iff_orderOf.mpr hord
  have hgN : g ^ (2 ^ (2 * m + 1) - 1) = 1 := by
    rw [← hcard, ← hg]
    exact pow_orderOf_eq_one g
  have hχN : (χ g) ^ (2 ^ (2 * m + 1) - 1) = 1 := by
    rw [← map_pow, hgN, map_one]
  obtain ⟨i, hi, hzi⟩ := IsPrimitiveRoot.eq_pow_of_mem_rootsOfUnity (R := k) hζ
    ((mem_rootsOfUnity (2 ^ (2 * m + 1) - 1) (χ g)).mpr hχN)
  refine ⟨(i : ZMod (2 ^ (2 * m + 1) - 1)), ?_⟩
  have hxval : ((i : ZMod (2 ^ (2 * m + 1) - 1))).val = i := ZMod.val_natCast_of_lt hi
  have hwg : wchar1 (K := K) k (i : ZMod (2 ^ (2 * m + 1) - 1)) g = χ g := by
    rw [wchar1, MonoidHom.pow_apply, hxval]
    exact hzi
  apply MonoidHom.ext
  intro y
  have hy : y ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers]
    exact hgen y
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y g).mp hy
  calc wchar1 (K := K) k (i : ZMod (2 ^ (2 * m + 1) - 1)) y
      = wchar1 (K := K) k (i : ZMod (2 ^ (2 * m + 1) - 1)) (g ^ n) := by rw [hn]
    _ = (wchar1 (K := K) k (i : ZMod (2 ^ (2 * m + 1) - 1)) g) ^ n := map_pow _ _ _
    _ = (χ g) ^ n := by rw [hwg]
    _ = χ (g ^ n) := (map_pow χ g n).symm
    _ = χ y := by rw [hn]

theorem iSup_weightSpace_wchar1 {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type)
    [Field k] [Algebra K k] {W : Type} [AddCommGroup W] [Module k W] [CharP k 2] [IsAlgClosed k]
    (hK : Nat.card K = 2 ^ (2 * m + 1)) [Module.Finite k W] (τ : Representation k Kˣ W) :
    ⨆ x : ZMod (2 ^ (2 * m + 1) - 1), weightSpace τ (wchar1 (K := K) k x) = ⊤ := by
  classical
  have hcard : Nat.card Kˣ = 2 ^ (2 * m + 1) - 1 := by rw [Nat.card_units, hK]
  have hN : (Nat.card Kˣ : k) ≠ 0 := by
    rw [hcard]
    intro hzero
    have h2pow : ((2 ^ (2 * m + 1) : ℕ) : k) = 0 := by
      push_cast
      rw [CharTwo.two_eq_zero]
      exact zero_pow (by omega)
    have hcast : ((2 ^ (2 * m + 1) - 1 : ℕ) : k) = -1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow, h2pow]
      ring
    rw [hcast] at hzero
    exact (neg_ne_zero.mpr one_ne_zero) hzero
  have htop := CFSG.LinearAlgebra.CoprimeActions.AbelianCoprimeWeightSpaceDecomposition.span_eq_top
    (F := k) (E := Kˣ) (V := W) τ hN
  rw [← htop]
  apply le_antisymm
  · apply iSup_le
    intro x
    exact le_iSup (fun χ => weightSpace τ χ) (wchar1 (K := K) k x)
  · apply iSup_le
    intro χ
    obtain ⟨x, rfl⟩ := exists_wchar1_eq (K := K) k hK χ
    exact le_iSup (fun x => weightSpace τ (wchar1 (K := K) k x)) x

theorem iSupIndep_weightSpace_wchar1 {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ}
    (k : Type) [Field k] [Algebra K k] {W : Type} [AddCommGroup W] [Module k W]
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (τ : Representation k Kˣ W) :
    iSupIndep fun x : ZMod (2 ^ (2 * m + 1) - 1) => weightSpace τ (wchar1 (K := K) k x) := by
  exact independent τ (fun x => wchar1 (K := K) k x)
    (wchar1_injective (K := K) k hK)

private lemma S_eq_natCast (e : ℕ) (J : Finset (Fin e)) :
    S e J = ((∑ j ∈ J, 2 ^ (j : ℕ) : ℕ) : ZMod (2 ^ e - 1)) := by
  rw [S]
  push_cast
  rfl

private lemma sum_szIdx_nat (m : ℕ) (J : Finset (Fin (2 * m + 1))) :
    (Finset.range (2 * m + 1)).filter (fun i => 2 * i ∈ szIdx m J) =
      J.image (fun j : Fin (2 * m + 1) => (j : ℕ)) := by
  ext i
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hir, h2i⟩
    rw [szIdx, Finset.mem_image] at h2i
    obtain ⟨j, hjJ, hj⟩ := h2i
    exact ⟨j, hjJ, by omega⟩
  · rintro ⟨j, hjJ, rfl⟩
    exact ⟨Finset.mem_range.mpr j.isLt, by
      rw [szIdx, Finset.mem_image]
      exact ⟨j, hjJ, rfl⟩⟩

private lemma mIdx_szIdx (m : ℕ) (J : Finset (Fin (2 * m + 1))) :
    mIdx (2 * m + 1) (szIdx m J) = ∑ j ∈ J, 2 ^ (j : ℕ) := by
  rw [mIdx, ← Finset.sum_filter, sum_szIdx_nat]
  exact Finset.sum_image (by intro a _ b _ h; exact Fin.ext (by exact_mod_cast h))

private lemma hw_val (m : ℕ) (J : Finset (Fin (2 * m + 1))) :
    (hw m J).val =
      ((1 + 2 ^ m) * (∑ j ∈ J, 2 ^ (j : ℕ))) % (2 ^ (2 * m + 1) - 1) := by
  have ha : (1 + 2 ^ m : ZMod (2 ^ (2 * m + 1) - 1)) =
      ((1 + 2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) := by
    push_cast
    ring
  rw [hw, ZMod.val_mul, S_eq_natCast, ZMod.val_natCast, ha, ZMod.val_natCast]
  simp only [Nat.mod_mod, Nat.mul_mod]

private lemma hwS_weight_scalar {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type)
    [Field k] [Algebra K k] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (J : Finset (Fin (2 * m + 1))) (l : Kˣ) :
    algebraMap K k ((l ^ (1 + (2 ^ m : ℤ)) : Kˣ) : K) ^ mIdx (2 * m + 1) (szIdx m J) =
      ((wchar1 (K := K) k (hw m J) l : kˣ) : k) := by
  have hz : (1 + (2 ^ m : ℤ)) = ((1 + 2 ^ m : ℕ) : ℤ) := by
    push_cast
    ring
  have hc : algebraMap K k ((l ^ (1 + (2 ^ m : ℤ)) : Kˣ) : K) =
      algebraMap K k (l : K) ^ (1 + 2 ^ m) := by
    rw [hz, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  have hbaseN : algebraMap K k (l : K) ^ (2 ^ (2 * m + 1) - 1) = 1 := by
    have h1 : ((l : K)) ^ (2 ^ (2 * m + 1) - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val (a := l) (n := 2 ^ (2 * m + 1) - 1),
        unit_pow_card_sub_one hK l]
      rfl
    rw [← map_pow, h1, map_one]
  have hm : mIdx (2 * m + 1) (szIdx m J) = ∑ j ∈ J, 2 ^ (j : ℕ) := mIdx_szIdx m J
  have hwv : (hw m J).val =
      ((1 + 2 ^ m) * (∑ j ∈ J, 2 ^ (j : ℕ))) % (2 ^ (2 * m + 1) - 1) := hw_val m J
  calc algebraMap K k ((l ^ (1 + (2 ^ m : ℤ)) : Kˣ) : K) ^ mIdx (2 * m + 1) (szIdx m J)
      = (algebraMap K k (l : K) ^ (1 + 2 ^ m)) ^ mIdx (2 * m + 1) (szIdx m J) := by rw [hc]
    _ = algebraMap K k (l : K) ^ ((1 + 2 ^ m) * mIdx (2 * m + 1) (szIdx m J)) := by rw [pow_mul]
    _ = algebraMap K k (l : K) ^ ((1 + 2 ^ m) * ∑ j ∈ J, 2 ^ (j : ℕ)) := by rw [hm]
    _ = algebraMap K k (l : K) ^
        (((1 + 2 ^ m) * ∑ j ∈ J, 2 ^ (j : ℕ)) % (2 ^ (2 * m + 1) - 1)) :=
          pow_eq_pow_mod _ hbaseN
    _ = algebraMap K k (l : K) ^ (hw m J).val := by rw [hwv]
    _ = ((wchar1 (K := K) k (hw m J) l : kˣ) : k) := by rw [wchar1_apply]

theorem szT_hwS_weight {K : Type} [Field K] [CharP K 2] [Fintype K]
    {m : ℕ} (k : Type) [Field k] [Algebra K k] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (J : Finset (Fin (2 * m + 1))) (l : Kˣ) :
    matRep (szT k hK (szIdx m J)) (szD K m l) (hwS k (szIdx m J)) =
      ((wchar1 (K := K) k (hw m J) l : kˣ) : k) • hwS k (szIdx m J) := by
  have hA : szIdx m J ⊆ szOmega m := szIdx_subset_szOmega J
  rw [matRep_apply]
  change (szT k hK (szIdx m J) (suzukiDElt m K l)).mulVec (hwS k (szIdx m J)) =
    ((wchar1 (K := K) k (hw m J) l : kˣ) : k) • hwS k (szIdx m J)
  rw [szT_suzukiDElt_hwS k hK hA l, hwS_weight_scalar k hK J l]

private noncomputable def dSpUnit {K : Type} [Field K] (j : ℕ) (s t : Kˣ) (y : Fin 4) : Kˣ :=
  ![s ^ 2 ^ j, t ^ 2 ^ j, (t ^ 2 ^ j)⁻¹, (s ^ 2 ^ j)⁻¹] y

private lemma dSpUnit_zero {K : Type} [Field K] (j : ℕ) (s t : Kˣ) :
    dSpUnit j s t 0 = s ^ 2 ^ j := rfl

private lemma dSpUnit_one {K : Type} [Field K] (j : ℕ) (s t : Kˣ) :
    dSpUnit j s t 1 = t ^ 2 ^ j := rfl

private lemma dSpUnit_two {K : Type} [Field K] (j : ℕ) (s t : Kˣ) :
    dSpUnit j s t 2 = (t ^ 2 ^ j)⁻¹ := rfl

private lemma dSpUnit_three {K : Type} [Field K] (j : ℕ) (s t : Kˣ) :
    dSpUnit j s t 3 = (s ^ 2 ^ j)⁻¹ := rfl

private lemma szWt_zero (m : ℕ) : szWt m 0 = 1 + 2 ^ m := rfl

private lemma szWt_one (m : ℕ) : szWt m 1 = 2 ^ m := rfl

private lemma szWt_two (m : ℕ) : szWt m 2 = -(2 ^ m) := rfl

private lemma szWt_three (m : ℕ) : szWt m 3 = -(1 + 2 ^ m) := rfl

private lemma one_add_theta_mul_R (m : ℕ) :
    (1 + 2 ^ m) * R (2 * m + 1) = 2 ^ m := by
  rw [R]
  have hd : (2 * m + 1 + 1) / 2 = m + 1 := by
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  rw [hd]
  have h2m : (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ (2 * m + 1) = 1 := by
    have hN : ((2 ^ (2 * m + 1) : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) = 1 := by
      rw [show 2 ^ (2 * m + 1) = (2 ^ (2 * m + 1) - 1) + 1 by
            exact (Nat.sub_add_cancel Nat.one_le_two_pow).symm,
        Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hN
  have hsplit : (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ m * 2 ^ (m + 1) = 1 := by
    rw [← pow_add]
    rw [show m + (m + 1) = 2 * m + 1 by omega]
    exact h2m
  calc (1 + 2 ^ m) * ((2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ (m + 1) - 1)
      = (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ (m + 1) - 1 +
          (2 ^ m * 2 ^ (m + 1) - 2 ^ m) := by ring
    _ = (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ (m + 1) - 1 + (1 - 2 ^ m) := by rw [hsplit]
    _ = (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ (m + 1) - 2 ^ m := by ring
    _ = 2 ^ m := by rw [pow_succ]; ring

private lemma one_add_theta_mul_negR (m : ℕ) :
    (1 + 2 ^ m) * (-(R (2 * m + 1))) = -(2 ^ m) := by
  rw [mul_neg, one_add_theta_mul_R]

private noncomputable def epsA (m : ℕ) (εfun : Fin (2 * m + 1) → Fin 4) (i : ℕ) : Fin 4 :=
  if h : i / 2 < 2 * m + 1 then εfun ⟨i / 2, h⟩ else 0

private lemma epsA_two_mul (m : ℕ) (εfun : Fin (2 * m + 1) → Fin 4) {j : ℕ}
    (hj : j < 2 * m + 1) : epsA m εfun (2 * j) = εfun ⟨j, hj⟩ := by
  unfold epsA
  have h2 : 2 * j / 2 = j := Nat.mul_div_cancel_left j (by norm_num : 0 < 2)
  split_ifs with h
  · exact congrArg εfun (Fin.ext h2)
  · rw [h2] at h
    exact absurd hj h

private lemma natRepS_dSp_even_apply {K : Type} [Field K] [CharP K 2] [Finite K] (k : Type)
    [Field k] [Algebra K k] (j : ℕ) (s t : Kˣ) (y y' : Fin 4) :
    natRepS k (2 * j) (dSp s t) y y' =
      if y = y' then algebraMap K k ((dSpUnit j s t y : Kˣ) : K) else 0 := by
  rw [natRepS_apply, minorAut_pow_two_mul_dSp, glMat_dSp, Matrix.map_apply, dmat,
    Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    congr 1
    fin_cases y <;> simp [dSpUnit]
  · exact map_zero _

private lemma wchar1_sum {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type)
    [Field k] [Algebra K k] (hK : Nat.card K = 2 ^ (2 * m + 1)) {ι : Type*}
    (s : Finset ι) (a : ι → ZMod (2 ^ (2 * m + 1) - 1)) (l : Kˣ) :
    ∏ i ∈ s, wchar1 (K := K) k (a i) l = wchar1 (K := K) k (∑ i ∈ s, a i) l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wchar1]
  | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx, ih]
      have h := congrArg (fun f : Kˣ →* kˣ => f l) (wchar1_add k hK (a x) (∑ i ∈ s, a i))
      rw [MonoidHom.mul_apply] at h
      exact h.symm

private lemma units_map_pow_eq_wchar1 {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ}
    (k : Type) [Field k] [Algebra K k] (hK : Nat.card K = 2 ^ (2 * m + 1)) (n : ℕ) (l : Kˣ) :
    Units.map (algebraMap K k : K →* k) (l ^ n) =
      wchar1 (K := K) k (n : ZMod (2 ^ (2 * m + 1) - 1)) l := by
  have hrhoN : (Units.map (algebraMap K k : K →* k) l) ^ (2 ^ (2 * m + 1) - 1) = 1 := by
    rw [← map_pow, unit_pow_card_sub_one hK l, map_one]
  rw [map_pow, wchar1, MonoidHom.pow_apply, ZMod.val_natCast]
  exact pow_eq_pow_mod n hrhoN

private lemma wchar1_pow_apply {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type)
    [Field k] [Algebra K k] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (x : ZMod (2 ^ (2 * m + 1) - 1)) (n : ℕ) (l : Kˣ) :
    (wchar1 (K := K) k x l) ^ n = wchar1 (K := K) k ((n : ZMod (2 ^ (2 * m + 1) - 1)) * x) l := by
  rw [← map_pow, wchar1_pow k hK x n l]

private lemma wchar1_neg {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type)
    [Field k] [Algebra K k] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (x : ZMod (2 ^ (2 * m + 1) - 1)) (l : Kˣ) :
    (wchar1 (K := K) k x l)⁻¹ = wchar1 (K := K) k (-x) l := by
  have h : wchar1 (K := K) k x l * wchar1 (K := K) k (-x) l = 1 := by
    have hprod : wchar1 (K := K) k x * wchar1 (K := K) k (-x) = 1 := by
      rw [← wchar1_add k hK x (-x), add_neg_cancel]
      ext l
      simp [wchar1]
    exact congrArg (fun f : Kˣ →* kˣ => f l) hprod
  exact inv_eq_of_mul_eq_one_right h

private lemma eigen_factor {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type)
    [Field k] [Algebra K k] (hK : Nat.card K = 2 ^ (2 * m + 1)) (j : ℕ) (y : Fin 4) (l : Kˣ) :
    Units.map (algebraMap K k : K →* k) (dSpUnit j (l ^ (1 + 2 ^ m)) (l ^ (2 ^ m)) y) =
      wchar1 (K := K) k ((2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ j * szWt m y) l := by
  have hs := units_map_pow_eq_wchar1 (K := K) k hK (1 + 2 ^ m) l
  have ht := units_map_pow_eq_wchar1 (K := K) k hK (2 ^ m) l
  fin_cases y
  · simp only [id_eq, Fin.reduceFinMk]
    rw [dSpUnit_zero, szWt_zero, map_pow, hs, wchar1_pow_apply k hK]
    congr 1
    push_cast
    ring
  · simp only [id_eq, Fin.reduceFinMk]
    rw [dSpUnit_one, szWt_one, map_pow, ht, wchar1_pow_apply k hK]
    congr 1
    push_cast
    ring
  · simp only [id_eq, Fin.reduceFinMk]
    rw [dSpUnit_two, szWt_two, map_inv, map_pow, ht, wchar1_pow_apply k hK, wchar1_neg k hK]
    congr 1
    push_cast
    ring
  · simp only [id_eq, Fin.reduceFinMk]
    rw [dSpUnit_three, szWt_three, map_inv, map_pow, hs, wchar1_pow_apply k hK, wchar1_neg k hK]
    congr 1
    push_cast
    ring

private lemma eigen_prod_eq {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type)
    [Field k] [Algebra K k] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (J : Finset (Fin (2 * m + 1))) (c : Fin (2 * m + 1) → ZMod (2 ^ (2 * m + 1) - 1))
    (εfun : Fin (2 * m + 1) → Fin 4)
    (hε : ∀ j ∈ J, (1 + 2 ^ m) * c j = szWt m (εfun j)) (l : Kˣ) :
    (∏ i : ↥(szIdx m J),
        Units.map (algebraMap K k : K →* k)
          (dSpUnit (i.val / 2) (l ^ (1 + 2 ^ m)) (l ^ (2 ^ m)) (epsA m εfun i.val))) =
      wchar1 (K := K) k ((1 + 2 ^ m) * ∑ j ∈ J, c j * 2 ^ (j : ℕ)) l := by
  set Φ : ℕ → kˣ := fun i => Units.map (algebraMap K k : K →* k)
    (dSpUnit (i / 2) (l ^ (1 + 2 ^ m)) (l ^ (2 ^ m)) (epsA m εfun i)) with hΦ
  change (∏ i : ↥(szIdx m J), Φ i) = _
  rw [Finset.prod_coe_sort (szIdx m J) Φ, szIdx,
    Finset.prod_image (s := J) (g := fun j : Fin (2 * m + 1) => 2 * (j : ℕ))
      (by intro a _ b _ h; exact Fin.ext (Nat.mul_left_cancel (by norm_num : 0 < 2) h))]
  have hstep : ∀ j ∈ J, Φ (2 * (j : ℕ)) =
      wchar1 (K := K) k ((2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ (j : ℕ) * szWt m (εfun j)) l := by
    intro j hj
    simp only [hΦ, epsA_two_mul m εfun j.isLt,
      Nat.mul_div_cancel_left (j : ℕ) (by norm_num : 0 < 2)]
    exact eigen_factor k hK (j : ℕ) (εfun j) l
  rw [Finset.prod_congr rfl hstep, wchar1_sum k hK J
    (fun j => (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ (j : ℕ) * szWt m (εfun j)) l]
  have hsum : (∑ j ∈ J, (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ (j : ℕ) * szWt m (εfun j)) =
      (1 + 2 ^ m) * ∑ j ∈ J, c j * 2 ^ (j : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← hε j hj]
    ring
  rw [hsum]

private lemma tensorRepS_mulVec_single {K : Type} [Field K] [CharP K 2] [Finite K] (k : Type)
    [Field k] [Algebra K k] (A : Finset ℕ) (g : antiSp K) (d : ℕ → Fin 4 → k)
    (hd : ∀ i ∈ A, ∀ y y' : Fin 4, natRepS k i g y y' = if y = y' then d i y else 0)
    (ε : ↥A → Fin 4) :
    (tensorRepS k A g).mulVec (Pi.single ε 1) =
      (∏ i : ↥A, d i.val (ε i)) • Pi.single ε 1 := by
  classical
  funext x
  rw [Matrix.mulVec_single_one, Matrix.col_apply, tensorRepS_apply]
  rw [Finset.prod_congr rfl (fun i _ => hd i.val i.property (x i) (ε i)), Fintype.prod_ite_zero]
  by_cases hx : x = ε
  · subst hx
    rw [if_pos (fun _ => rfl)]
    simp [Pi.single_eq_same]
  · have h : ¬ (∀ i : ↥A, x i = ε i) := fun hh => hx (funext hh)
    rw [if_neg h]
    simp [Pi.single_apply, hx]

theorem szT_exists_weight {K : Type} [Field K] [CharP K 2]
    [Fintype K] {m : ℕ} (k : Type) [Field k] [Algebra K k] [CharP k 2]
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (J : Finset (Fin (2 * m + 1)))
    {x : ZMod (2 ^ (2 * m + 1) - 1)} (hx : x ∈ wtSet m J) :
    ∃ v : (szIdx m J → Fin 4) → k, v ≠ 0 ∧ ∀ l : Kˣ,
      matRep (szT k hK (szIdx m J)) (szD K m l) v = ((wchar1 (K := K) k x l : kˣ) : k) • v := by
  classical
  rw [wtSet] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Lam] at hy
  obtain ⟨c, hc, hyeq⟩ := hy
  rw [hyeq]
  have hεexists : ∀ j ∈ J, ∃ t : Fin 4, (1 + 2 ^ m) * c j = szWt m t := by
    intro j hj
    have hmem : c j ∈ units (2 * m + 1) := hc j hj
    simp only [units, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h2 | h3 | h4
    · exact ⟨0, by rw [h1, mul_one, szWt_zero]⟩
    · exact ⟨3, by rw [h2, mul_neg, mul_one, szWt_three]⟩
    · exact ⟨1, by rw [h3, one_add_theta_mul_R, szWt_one]⟩
    · exact ⟨2, by rw [h4, one_add_theta_mul_negR, szWt_two]⟩
  let εfun : Fin (2 * m + 1) → Fin 4 :=
    fun j => if h : j ∈ J then Classical.choose (hεexists j h) else 0
  have hε : ∀ j ∈ J, (1 + 2 ^ m) * c j = szWt m (εfun j) := by
    intro j hj
    simp only [εfun, dif_pos hj]
    exact Classical.choose_spec (hεexists j hj)
  refine ⟨Pi.single (fun i => epsA m εfun i.val) 1, ?_, ?_⟩
  · intro h0
    have h1 := congrFun h0 (fun i => epsA m εfun i.val)
    rw [Pi.single_eq_same] at h1
    exact one_ne_zero h1
  · intro l
    rw [matRep_apply]
    change (szT k hK (szIdx m J) (suzukiDElt m K l)).mulVec
        (Pi.single (fun i => epsA m εfun i.val) 1) =
      ((wchar1 (K := K) k ((1 + 2 ^ m) * ∑ j ∈ J, c j * 2 ^ (j : ℕ)) l : kˣ) : k) •
        Pi.single (fun i => epsA m εfun i.val) 1
    rw [szT_apply, szIncl_suzukiDElt hK l,
      show (1 + (2 ^ m : ℤ)) = ((1 + 2 ^ m : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      show (2 ^ m : ℤ) = ((2 ^ m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    have hd : ∀ i ∈ szIdx m J, ∀ y y' : Fin 4,
        natRepS k i (dSp (l ^ (1 + 2 ^ m)) (l ^ (2 ^ m))) y y' =
          if y = y' then algebraMap K k
            ((dSpUnit (i / 2) (l ^ (1 + 2 ^ m)) (l ^ (2 ^ m)) y : Kˣ) : K) else 0 := by
      intro i hi y y'
      obtain ⟨cc, -, hci⟩ := mem_szOmega.mp (szIdx_subset_szOmega J hi)
      rw [show i = 2 * cc from hci.symm, Nat.mul_div_cancel_left cc (by norm_num : 0 < 2)]
      exact natRepS_dSp_even_apply k cc (l ^ (1 + 2 ^ m)) (l ^ (2 ^ m)) y y'
    have hsingle := tensorRepS_mulVec_single k (szIdx m J)
      (dSp (l ^ (1 + 2 ^ m)) (l ^ (2 ^ m)))
      (fun i y => algebraMap K k
        ((dSpUnit (i / 2) (l ^ (1 + 2 ^ m)) (l ^ (2 ^ m)) y : Kˣ) : K))
      hd (fun i => epsA m εfun i.val)
    rw [hsingle]
    have hscalar : (∏ i : ↥(szIdx m J), algebraMap K k
        ((dSpUnit (i.val / 2) (l ^ (1 + 2 ^ m)) (l ^ (2 ^ m)) (epsA m εfun i.val) : Kˣ) : K)) =
        ((wchar1 (K := K) k ((1 + 2 ^ m) * ∑ j ∈ J, c j * 2 ^ (j : ℕ)) l : kˣ) : k) := by
      have hcast : (∏ i : ↥(szIdx m J), algebraMap K k
          ((dSpUnit (i.val / 2) (l ^ (1 + 2 ^ m)) (l ^ (2 ^ m)) (epsA m εfun i.val) : Kˣ) : K)) =
          ((∏ i : ↥(szIdx m J), Units.map (algebraMap K k : K →* k)
            (dSpUnit (i.val / 2) (l ^ (1 + 2 ^ m)) (l ^ (2 ^ m)) (epsA m εfun i.val)) : kˣ) : k) := by
        exact (map_prod (Units.coeHom k)
            (fun i : ↥(szIdx m J) => Units.map (algebraMap K k : K →* k)
              (dSpUnit (i.val / 2) (l ^ (1 + 2 ^ m)) (l ^ (2 ^ m)) (epsA m εfun i.val)))
            Finset.univ).symm
      rw [hcast, eigen_prod_eq k hK J c εfun hε l]
    rw [hscalar]

end CFSG.StandardType.ReeB2Fixed
