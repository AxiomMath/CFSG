module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverRanks
import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV

open Matrix
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.RankThree.PartTwo.Sec4.Census (diagHom coe_diagHom)

section Torus

variable {K : Type} [Field K]

@[expose] noncomputable def torusSnoc (m : ℕ) : (Fin m → Kˣ) →* (Fin (m + 1) → Kˣ) where
  toFun x := Fin.snoc (α := fun _ => Kˣ) x (∏ i, x i)⁻¹
  map_one' := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last, Pi.one_apply, Finset.prod_const_one, inv_one]
    · simp only [Fin.snoc_castSucc, Pi.one_apply]
  map_mul' x y := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last, Pi.mul_apply, Finset.prod_mul_distrib, mul_inv]
    · simp only [Fin.snoc_castSucc, Pi.mul_apply]

theorem torusSnoc_castSucc (m : ℕ) (x : Fin m → Kˣ) (i : Fin m) :
    torusSnoc m x i.castSucc = x i :=
  Fin.snoc_castSucc (α := fun _ => Kˣ) _ _ _

theorem torusSnoc_last (m : ℕ) (x : Fin m → Kˣ) :
    torusSnoc m x (Fin.last m) = (∏ i, x i)⁻¹ :=
  Fin.snoc_last (α := fun _ => Kˣ) _ _

theorem prod_torusSnoc (m : ℕ) (x : Fin m → Kˣ) : ∏ j, torusSnoc m x j = 1 := by
  rw [Fin.prod_univ_castSucc, torusSnoc_last]
  simp only [torusSnoc_castSucc, mul_inv_cancel]

theorem torusSnoc_mem (m : ℕ) {U : Subgroup Kˣ} {x : Fin m → Kˣ} (hx : ∀ i, x i ∈ U)
    (j : Fin (m + 1)) : torusSnoc m x j ∈ U := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [torusSnoc_last]
    exact inv_mem (prod_mem fun i _ => hx i)
  · rw [torusSnoc_castSucc]
    exact hx i

end Torus

section SU

variable (m p f : ℕ) [Fact p.Prime]

theorem diagHom_mem_su {n : ℕ} {d : Fin n → (GaloisField p (2 * f))ˣ} (hdet : ∏ j, d j = 1)
    (hd : ∀ j, d j ^ (p ^ f + 1) = 1) :
    diagHom d ∈ {A : GL (Fin n) (GaloisField p (2 * f)) | GeneralLinearGroup.det A = 1 ∧
      ((A : Matrix (Fin n) (Fin n) (GaloisField p (2 * f))).map (· ^ (p ^ f)))ᵀ *
        (A : Matrix (Fin n) (Fin n) (GaloisField p (2 * f))) = 1} := by
  refine ⟨Units.ext ?_, ?_⟩
  · rw [GeneralLinearGroup.val_det_apply, coe_diagHom, det_diagonal, Units.val_one]
    have h1 := congrArg Units.val hdet
    rw [Units.coe_prod, Units.val_one] at h1
    exact h1
  · have h0 : (0 : GaloisField p (2 * f)) ^ (p ^ f) = 0 :=
      zero_pow (pow_ne_zero f (Fact.out : p.Prime).ne_zero)
    rw [coe_diagHom, Matrix.diagonal_map h0, diagonal_transpose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext j
    have h1 := congrArg Units.val (hd j)
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ] at h1
    exact h1

@[expose] noncomputable def torusSU (U : Subgroup (GaloisField p (2 * f))ˣ)
    (hU : ∀ u ∈ U, u ^ (p ^ f + 1) = 1) : (Fin m → U) →* projSU (m + 1) p f :=
  MonoidHom.codRestrict
    (ProjGenLinGroup.mk.comp (diagHom.comp ((torusSnoc m).comp (U.subtype.compLeft (Fin m)))))
    _ fun x => ⟨_, Subgroup.subset_closure (diagHom_mem_su p f (prod_torusSnoc m _)
      fun j => hU _ (torusSnoc_mem m (fun i => (x i).2) j)), rfl⟩

variable {m p f}

theorem torusSU_injective (U : Subgroup (GaloisField p (2 * f))ˣ)
    (hU : ∀ u ∈ U, u ^ (p ^ f + 1) = 1) (hinj : ∀ u ∈ U, u ^ (m + 1) = 1 → u = 1) :
    Function.Injective (torusSU m p f U hU) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  set t := torusSnoc m fun i => (x i : (GaloisField p (2 * f))ˣ) with ht
  have h1 : ProjGenLinGroup.mk (diagHom t) = 1 := congrArg Subtype.val hx
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at h1
  obtain ⟨c, hc⟩ := h1
  have hent : ∀ j, ((t j : (GaloisField p (2 * f))ˣ) : GaloisField p (2 * f)) = c := fun j => by
    have := congrFun (congrFun hc j) j
    rw [coe_diagHom, diagonal_apply_eq, scalar_apply, diagonal_apply_eq] at this
    exact this.symm
  have hall : ∀ j, t j = t (Fin.last m) := fun j =>
    Units.ext ((hent j).trans (hent (Fin.last m)).symm)
  have hw1 : t (Fin.last m) ^ (m + 1) = 1 := by
    have h2 := prod_torusSnoc m fun i => (x i : (GaloisField p (2 * f))ˣ)
    rw [← ht, Finset.prod_congr rfl fun j _ => hall j, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h2
    exact h2
  have hw : t (Fin.last m) = 1 :=
    hinj _ (torusSnoc_mem m (fun i => (x i).2) (Fin.last m)) hw1
  funext i
  apply Subtype.ext
  have h3 := hall i.castSucc
  rw [hw, ht, torusSnoc_castSucc] at h3
  exact h3

theorem isMulCommutative_range_torusSU (U : Subgroup (GaloisField p (2 * f))ˣ)
    (hU : ∀ u ∈ U, u ^ (p ^ f + 1) = 1) : IsMulCommutative (torusSU m p f U hU).range := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  obtain ⟨_, ⟨u, rfl⟩⟩ := a
  obtain ⟨_, ⟨v, rfl⟩⟩ := b
  change torusSU m p f U hU u * torusSU m p f U hU v = torusSU m p f U hU v * torusSU m p f U hU u
  rw [← map_mul, ← map_mul]
  exact congrArg (torusSU m p f U hU) (mul_comm u v)

theorem range_torusSU_mono {U U' : Subgroup (GaloisField p (2 * f))ˣ}
    (hUU' : U ≤ U') (hU : ∀ u ∈ U, u ^ (p ^ f + 1) = 1) (hU' : ∀ u ∈ U', u ^ (p ^ f + 1) = 1) :
    (torusSU m p f U hU).range ≤ (torusSU m p f U' hU').range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨fun i => ⟨x i, hUU' (x i).2⟩, Subtype.ext rfl⟩

theorem card_range_torusSU (U : Subgroup (GaloisField p (2 * f))ˣ)
    (hU : ∀ u ∈ U, u ^ (p ^ f + 1) = 1) (hinj : ∀ u ∈ U, u ^ (m + 1) = 1 → u = 1) :
    Nat.card (torusSU m p f U hU).range = Nat.card U ^ m := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (torusSU_injective U hU hinj)).toEquiv,
    Nat.card_fun, Nat.card_fin]

end SU

theorem card_rootsOfUnity_of_dvd_card_units {K : Type} [Field K] [Finite K] {d : ℕ} [NeZero d]
    (hd : d ∣ Nat.card Kˣ) : Nat.card (rootsOfUnity d K) = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hog : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨k, hk⟩ := hd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact Nat.card_pos.ne' hk
  have hζ : orderOf (g ^ k) = d := by
    rw [orderOf_pow' g hk0, hog, hk, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]
  have hprim : IsPrimitiveRoot ((g ^ k : Kˣ) : K) d :=
    IsPrimitiveRoot.coe_units_iff.mpr (hζ ▸ IsPrimitiveRoot.orderOf (g ^ k))
  exact hprim.card_rootsOfUnity

theorem pow_eq_one_of_mem_rootsOfUnity {K : Type} [Field K] {d q : ℕ} (hd : d ∣ q + 1)
    {u : Kˣ} (hu : u ∈ rootsOfUnity d K) : u ^ (q + 1) = 1 := by
  obtain ⟨k, hk⟩ := hd
  rw [hk, pow_mul, (mem_rootsOfUnity d u).mp hu, one_pow]

theorem eq_one_of_mem_rootsOfUnity {K : Type} [Field K] {d n : ℕ} (hdn : Nat.Coprime d n)
    {u : Kˣ} (hu : u ∈ rootsOfUnity d K) (hn : u ^ n = 1) : u = 1 := by
  have := pow_gcd_eq_one.mpr ⟨(mem_rootsOfUnity d u).mp hu, hn⟩
  rwa [hdn, pow_one] at this

theorem exists_elemAbelian_projSU_torus (m p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f)
    (hq : 3 ∣ p ^ f + 1) (hm : ¬ 3 ∣ m + 1) :
    ∃ E : Subgroup (projSU (m + 1) p f), CFSG.Assembly.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ m := by
  have hK : Nat.card (GaloisField p (2 * f)) = p ^ (2 * f) := GaloisField.card p (2 * f) (by omega)
  have h3K : 3 ∣ Nat.card (GaloisField p (2 * f))ˣ := by
    rw [Nat.card_units, hK, pow_mul', sq, ← one_mul 1, Nat.mul_self_sub_mul_self_eq]
    exact dvd_mul_of_dvd_left hq _
  have hcop : Nat.Coprime 3 (m + 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm
  have hU := fun u (hu : u ∈ rootsOfUnity 3 (GaloisField p (2 * f))) =>
    pow_eq_one_of_mem_rootsOfUnity hq hu
  refine ⟨(torusSU m p f _ hU).range, ⟨isMulCommutative_range_torusSU _ hU, ?_⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := funext fun i =>
      CFSG.RankThree.PartTwo.Census.rootsOfUnity_pow_eq_one (x i)
    rw [this, map_one]
  · rw [card_range_torusSU _ hU fun u hu => eq_one_of_mem_rootsOfUnity hcop hu,
      card_rootsOfUnity_of_dvd_card_units h3K]

theorem exists_torus_projSU_five_eight :
    ∃ N E : Subgroup (projSU 5 2 3), IsMulCommutative N ∧ Nat.card N = 3 ^ 8 ∧ E ≤ N ∧
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 81 := by
  have hK : Nat.card (GaloisField 2 (2 * 3))ˣ = 63 := by
    rw [Nat.card_units, GaloisField.card 2 (2 * 3) (by norm_num)]
    norm_num
  have hU9 := fun u (hu : u ∈ rootsOfUnity 9 (GaloisField 2 (2 * 3))) =>
    pow_eq_one_of_mem_rootsOfUnity (q := 2 ^ 3) (by norm_num) hu
  have hU3 := fun u (hu : u ∈ rootsOfUnity 3 (GaloisField 2 (2 * 3))) =>
    pow_eq_one_of_mem_rootsOfUnity (q := 2 ^ 3) (by norm_num) hu
  refine ⟨(torusSU 4 2 3 _ hU9).range, (torusSU 4 2 3 _ hU3).range,
    isMulCommutative_range_torusSU _ hU9, ?_,
    range_torusSU_mono (rootsOfUnity_le_of_dvd (by norm_num)) hU3 hU9,
    ⟨isMulCommutative_range_torusSU _ hU3, ?_⟩, ?_⟩
  · rw [card_range_torusSU _ hU9 fun u hu => eq_one_of_mem_rootsOfUnity (by norm_num) hu,
      card_rootsOfUnity_of_dvd_card_units (by rw [hK]; norm_num)]
    norm_num
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := funext fun i =>
      CFSG.RankThree.PartTwo.Census.rootsOfUnity_pow_eq_one (x i)
    rw [this, map_one]
  · rw [card_range_torusSU _ hU3 fun u hu => eq_one_of_mem_rootsOfUnity (by norm_num) hu,
      card_rootsOfUnity_of_dvd_card_units (by rw [hK]; norm_num)]
    norm_num

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV
