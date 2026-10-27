module

public import CFSG.Timmesfeld.Transvection.OddPairs
import CFSG.Timmesfeld.Transvection.OddPairsModel
import CFSG.Timmesfeld.Transvection.OddModelSU3
import CFSG.Timmesfeld.RankTwo.SimplyLaced

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Timmesfeld.Transvection.Pres
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H]
  (Ψ₀ : SU (unitaryInvolution F 2 n) (2 * r) →* H) (θ : SU (unitaryInvolution F 2 n) 3 →* H)

private theorem even_last_of_mem_pairRoots_of_ne {i j : Fin ((2 * r + 1) / 2)}
    (hi : i ≠ bcLastIdx r (Nat.one_le_of_lt hr)) (hj : j ≠ bcLastIdx r (Nat.one_le_of_lt hr))
    {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : γ ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1)) i j) :
    Even (γ (bcLastIdx r (Nat.one_le_of_lt hr))) := by
  rw [eq_zero_last_of_mem_pairRoots hFn hr hi hj hγ]
  exact Even.zero

private theorem even_last_of_even {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (h : Even (γ ⟨r - 1, Nat.lt_of_lt_of_le (Nat.sub_one_lt_of_lt hr)
      (Nat.le_div_iff_mul_le Nat.two_pos |>.mpr (Nat.le_succ_of_le (Nat.mul_comm r 2).le))⟩)) :
    Even (γ (bcLastIdx r (Nat.one_le_of_lt hr))) := by
  simpa only [bcLastIdx] using h

theorem extendsToHom_pairRoots_oddFrameMap_of_ne_last {i j : Fin ((2 * r + 1) / 2)}
    (hi : i ≠ bcLastIdx r (Nat.one_le_of_lt hr)) (hj : j ≠ bcLastIdx r (Nat.one_le_of_lt hr)) :
    ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (pairRoots (Unitary.rootDatum hFn (2 * r + 1)) i j) (oddFrameMap hFn hr Ψ₀ θ) := by
  refine extendsToHom_of_injective (D := Unitary.rootDatum hFn (2 * r + 1))
    (K := SU (unitaryInvolution F 2 n) (2 * r + 1))
    (l := oddEmb (unitaryInvolution F 2 n) r)
    (oddEmb_injective (σ := unitaryInvolution F 2 n) (r := r)) Ψ₀ ?_
  intro γ hγ g
  have hEven := even_last_of_mem_pairRoots_of_ne hFn hr hi hj hγ
  have hEven' := even_last_of_even hr hEven
  have hmem : (g : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      (oddEmb (unitaryInvolution F 2 n) r).range :=
    rootGroup_le_range_oddEmb (σ := unitaryInvolution F 2 n)
      (hσ := unitaryInvolution_involutive hFn) (r := r) (Nat.one_le_of_lt hr) hEven' g.2
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy, oddFrameMap_eq_of_even hFn hr Ψ₀ θ hEven g y hy⟩

theorem extendsToHom_rankOne_oddFrameMap (k : Fin ((2 * r + 1) / 2)) :
    ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      {Pi.single k 1, -Pi.single k 1} (oddFrameMap hFn hr Ψ₀ θ) := by
  by_cases hk : k = bcLastIdx r (Nat.one_le_of_lt hr)
  · subst hk
    refine extendsToHom_of_injective (D := Unitary.rootDatum hFn (2 * r + 1))
      (K := SU (unitaryInvolution F 2 n) (2 * r + 1))
      (l := su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr)))
      (su3Emb_injective (σ := unitaryInvolution F 2 n) (n := 2 * r + 1)
        (Nat.not_even_two_mul_add_one r) (bcLastIdx r (Nat.one_le_of_lt hr))) θ ?_
    intro γ hγ g
    rcases hγ with rfl | rfl
    · have hto : toStd (2 * r + 1) (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) =
          wt (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) := (toStd_bc2 hr).2.1
      have hmem : (g : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
          (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
            (bcLastIdx r (Nat.one_le_of_lt hr))).range :=
        rootGroup_le_range_su3Emb (σ := unitaryInvolution F 2 n)
          (hσ := unitaryInvolution_involutive hFn) (n := 2 * r + 1)
          (Nat.not_even_two_mul_add_one r) (a := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) hto
          g.2
      obtain ⟨A, hA⟩ := hmem
      exact ⟨A, hA, oddFrameMap_eq_of_toStd_last hFn hr Ψ₀ θ (a := Sum.inl (bcLastIdx r
        (Nat.one_le_of_lt hr))) rfl hto g A hA⟩
    · have hto : toStd (2 * r + 1) (-Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) =
          wt (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) := (toStd_bc2_neg hr).1
      have hmem : (g : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
          (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
            (bcLastIdx r (Nat.one_le_of_lt hr))).range :=
        rootGroup_le_range_su3Emb (σ := unitaryInvolution F 2 n)
          (hσ := unitaryInvolution_involutive hFn) (n := 2 * r + 1)
          (Nat.not_even_two_mul_add_one r) (a := Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) hto
          g.2
      obtain ⟨A, hA⟩ := hmem
      exact ⟨A, hA, oddFrameMap_eq_of_toStd_last hFn hr Ψ₀ θ (a := Sum.inr (bcLastIdx r
        (Nat.one_le_of_lt hr))) rfl hto g A hA⟩
  · have hsub : ({Pi.single k 1, -Pi.single k 1} : Set (Fin ((2 * r + 1) / 2) → ℤ)) ⊆
        pairRoots (Unitary.rootDatum hFn (2 * r + 1)) k k := by
      intro γ hγ
      rcases hγ with rfl | rfl
      exacts [(Levi.single_mem_pairRoots (D := Unitary.rootDatum hFn (2 * r + 1))
        (Or.inl rfl)).1,
        (Levi.single_mem_pairRoots (D := Unitary.rootDatum hFn (2 * r + 1))
          (Or.inl rfl)).2]
    exact (extendsToHom_pairRoots_oddFrameMap_of_ne_last hFn hr Ψ₀ θ hk hk).mono hsub

theorem range_oddFrameMap_single_of_ne {k : Fin ((2 * r + 1) / 2)}
    (hk : k ≠ bcLastIdx r (Nat.one_le_of_lt hr)) :
    Set.range (oddFrameMap hFn hr Ψ₀ θ (Pi.single k 1)) =
      ((CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
        (unitaryInvolution_involutive hFn) (2 * r)
          (Pi.single ((finCastOdd r).symm k) 1)).map Ψ₀ : Set H) := by
  have hEven : Even ((Pi.single k 1 : Fin ((2 * r + 1) / 2) → ℤ)
      (bcLastIdx r (Nat.one_le_of_lt hr))) := by
    rw [Pi.single_eq_of_ne (Ne.symm hk)]
    exact Even.zero
  have hk' : ((finCastOdd r).symm k).val + 1 ≠ r := by
    intro h
    apply hk
    apply Fin.ext
    have hval : ((finCastOdd r).symm k).val = k.val := by simp
    simp only [bcLastIdx, Fin.val_mk]
    omega
  have hrootCast : rootCast r (Pi.single ((finCastOdd r).symm k) 1) = Pi.single k 1 := by
    rw [rootCast_single (r := r) hk', Equiv.apply_symm_apply]
  ext h
  constructor
  · rintro ⟨x, rfl⟩
    have hxmap : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
        (CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
          (unitaryInvolution_involutive hFn) (2 * r) (Pi.single ((finCastOdd r).symm k) 1)).map
          (oddEmb (unitaryInvolution F 2 n) r) := by
      rw [map_rootGroup_oddEmb (σ := unitaryInvolution F 2 n)
        (hσ := unitaryInvolution_involutive hFn) (r := r), hrootCast]
      exact x.2
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hxmap
    exact ⟨y, hy, (oddFrameMap_eq_of_even hFn hr Ψ₀ θ hEven x y hxy).symm⟩
  · rintro ⟨y, hy, rfl⟩
    have hxmem : oddEmb (unitaryInvolution F 2 n) r y ∈
        (Unitary.rootDatum hFn (2 * r + 1)).rootGroup (Pi.single k 1) := by
      have hm := Subgroup.mem_map_of_mem (f := oddEmb (unitaryInvolution F 2 n) r) hy
      rwa [map_rootGroup_oddEmb (σ := unitaryInvolution F 2 n)
        (hσ := unitaryInvolution_involutive hFn) (r := r), hrootCast] at hm
    exact ⟨⟨oddEmb (unitaryInvolution F 2 n) r y, hxmem⟩,
      oddFrameMap_eq_of_even hFn hr Ψ₀ θ hEven _ y rfl⟩

theorem range_oddFrameMap_neg_single_of_ne {k : Fin ((2 * r + 1) / 2)}
    (hk : k ≠ bcLastIdx r (Nat.one_le_of_lt hr)) :
    Set.range (oddFrameMap hFn hr Ψ₀ θ (-Pi.single k 1)) =
      ((CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
        (unitaryInvolution_involutive hFn) (2 * r)
          (-Pi.single ((finCastOdd r).symm k) 1)).map Ψ₀ : Set H) := by
  have hEven : Even ((-Pi.single k 1 : Fin ((2 * r + 1) / 2) → ℤ)
      (bcLastIdx r (Nat.one_le_of_lt hr))) := by
    rw [Pi.neg_apply, Pi.single_eq_of_ne (Ne.symm hk)]
    exact Even.zero
  have hk' : ((finCastOdd r).symm k).val + 1 ≠ r := by
    intro h
    apply hk
    apply Fin.ext
    have hval : ((finCastOdd r).symm k).val = k.val := by simp
    simp only [bcLastIdx, Fin.val_mk]
    omega
  have hrootCast : rootCast r (-Pi.single ((finCastOdd r).symm k) 1) = -Pi.single k 1 := by
    rw [rootCast_neg, rootCast_single (r := r) hk', Equiv.apply_symm_apply]
  ext h
  constructor
  · rintro ⟨x, rfl⟩
    have hxmap : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
        (CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
          (unitaryInvolution_involutive hFn) (2 * r)
            (-Pi.single ((finCastOdd r).symm k) 1)).map
          (oddEmb (unitaryInvolution F 2 n) r) := by
      rw [map_rootGroup_oddEmb (σ := unitaryInvolution F 2 n)
        (hσ := unitaryInvolution_involutive hFn) (r := r), hrootCast]
      exact x.2
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hxmap
    exact ⟨y, hy, (oddFrameMap_eq_of_even hFn hr Ψ₀ θ hEven x y hxy).symm⟩
  · rintro ⟨y, hy, rfl⟩
    have hxmem : oddEmb (unitaryInvolution F 2 n) r y ∈
        (Unitary.rootDatum hFn (2 * r + 1)).rootGroup (-Pi.single k 1) := by
      have hm := Subgroup.mem_map_of_mem (f := oddEmb (unitaryInvolution F 2 n) r) hy
      rwa [map_rootGroup_oddEmb (σ := unitaryInvolution F 2 n)
        (hσ := unitaryInvolution_involutive hFn) (r := r), hrootCast] at hm
    exact ⟨⟨oddEmb (unitaryInvolution F 2 n) r y, hxmem⟩,
      oddFrameMap_eq_of_even hFn hr Ψ₀ θ hEven _ y rfl⟩

theorem range_oddFrameMap_single_last :
    Set.range (oddFrameMap hFn hr Ψ₀ θ (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) =
      ((CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
        (unitaryInvolution_involutive hFn) 3 (Pi.single (0 : Fin (3 / 2)) 1)).map θ : Set H) := by
  have hto : toStd (2 * r + 1) (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) =
      wt (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) := (toStd_bc2 hr).2.1
  have hmap := map_rootGroup_su3Emb (σ := unitaryInvolution F 2 n)
    (hσ := unitaryInvolution_involutive hFn) (n := 2 * r + 1)
    (Nat.not_even_two_mul_add_one r) (bcLastIdx r (Nat.one_le_of_lt hr))
    (γ := Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) hto
  ext h
  constructor
  · rintro ⟨x, rfl⟩
    have hx : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
        (CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
          (unitaryInvolution_involutive hFn) 3 (Pi.single (0 : Fin (3 / 2)) 1)).map
          (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
            (bcLastIdx r (Nat.one_le_of_lt hr))) := by
      rw [hmap]
      exact x.2
    obtain ⟨A, hA, hAx⟩ := Subgroup.mem_map.mp hx
    exact ⟨A, hA, (oddFrameMap_eq_of_toStd_last hFn hr Ψ₀ θ
      (a := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) rfl hto x A hAx).symm⟩
  · rintro ⟨A, hA, rfl⟩
    have hx : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr)) A ∈
        (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
          (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) := by
      change su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr)) A ∈
        Unitary.rootGroup (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (2 * r + 1) (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hA
    exact ⟨⟨su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcLastIdx r (Nat.one_le_of_lt hr)) A, hx⟩,
      oddFrameMap_eq_of_toStd_last hFn hr Ψ₀ θ
        (a := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) rfl hto _ A rfl⟩

theorem range_oddFrameMap_neg_single_last :
    Set.range (oddFrameMap hFn hr Ψ₀ θ (-Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) =
      ((CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
        (unitaryInvolution_involutive hFn) 3 (-Pi.single (0 : Fin (3 / 2)) 1)).map θ : Set H) := by
  have hto : toStd (2 * r + 1) (-Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) =
      wt (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) := (toStd_bc2_neg hr).1
  have hmap := map_rootGroup_su3Emb_neg (σ := unitaryInvolution F 2 n)
    (hσ := unitaryInvolution_involutive hFn) (n := 2 * r + 1)
    (Nat.not_even_two_mul_add_one r) (bcLastIdx r (Nat.one_le_of_lt hr))
    (γ := -Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) hto
  ext h
  constructor
  · rintro ⟨x, rfl⟩
    have hx : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
        (CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
          (unitaryInvolution_involutive hFn) 3 (-Pi.single (0 : Fin (3 / 2)) 1)).map
          (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
            (bcLastIdx r (Nat.one_le_of_lt hr))) := by
      rw [hmap]
      exact x.2
    obtain ⟨A, hA, hAx⟩ := Subgroup.mem_map.mp hx
    exact ⟨A, hA, (oddFrameMap_eq_of_toStd_last hFn hr Ψ₀ θ
      (a := Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) rfl hto x A hAx).symm⟩
  · rintro ⟨A, hA, rfl⟩
    have hx : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr)) A ∈
        (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
          (-Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) := by
      change su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr)) A ∈
        Unitary.rootGroup (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (2 * r + 1) (-Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hA
    exact ⟨⟨su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcLastIdx r (Nat.one_le_of_lt hr)) A, hx⟩,
      oddFrameMap_eq_of_toStd_last hFn hr Ψ₀ θ
        (a := Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) rfl hto _ A rfl⟩

namespace OddFrameCompatible

variable {hFn hr Ψ₀ θ}

theorem exists_su3Emb_eq_oddFrameMap (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : γ ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1))
      (bcLastIdx r (Nat.one_le_of_lt hr)) (bcLastIdx r (Nat.one_le_of_lt hr)))
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ) :
    ∃ A, su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr)) A = x ∧ oddFrameMap hFn hr Ψ₀ θ γ x = θ A := by
  rcases eq_of_mem_pairRoots_last hFn hr hγ with rfl | rfl | rfl | rfl
  · have hto : toStd (2 * r + 1) (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) =
        wt (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) := (toStd_bc2 hr).2.1
    have hmem : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
        (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
          (bcLastIdx r (Nat.one_le_of_lt hr))).range :=
      rootGroup_le_range_su3Emb (σ := unitaryInvolution F 2 n)
        (hσ := unitaryInvolution_involutive hFn) (n := 2 * r + 1)
        (Nat.not_even_two_mul_add_one r) (a := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) hto x.2
    obtain ⟨A, hA⟩ := hmem
    exact ⟨A, hA, oddFrameMap_eq_of_toStd_last hFn hr Ψ₀ θ
      (a := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) rfl hto x A hA⟩
  · have hto : toStd (2 * r + 1) (-Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) =
        wt (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) := (toStd_bc2_neg hr).1
    have hmem : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
        (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
          (bcLastIdx r (Nat.one_le_of_lt hr))).range :=
      rootGroup_le_range_su3Emb (σ := unitaryInvolution F 2 n)
        (hσ := unitaryInvolution_involutive hFn) (n := 2 * r + 1)
        (Nat.not_even_two_mul_add_one r) (a := Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) hto x.2
    obtain ⟨A, hA⟩ := hmem
    exact ⟨A, hA, oddFrameMap_eq_of_toStd_last hFn hr Ψ₀ θ
      (a := Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) rfl hto x A hA⟩
  · obtain ⟨c, hc0, hxc⟩ := (mem_rootGroup_iff_suLong_odd
      (unitaryInvolution_involutive hFn) (a := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
      (toStd_bc2 hr).2.2.1 x).mp x.2
    have hc : unitaryInvolution F 2 n c = c := add_map_eq_zero_iff.1 hc0
    refine ⟨suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c, ?_, ?_⟩
    · rw [su3Emb_suLong_inl (σ := unitaryInvolution F 2 n)
        (Nat.not_even_two_mul_add_one r) (bcLastIdx r (Nat.one_le_of_lt hr)) c, hxc]
    · have hEven : Even ((2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 :
          Fin ((2 * r + 1) / 2) → ℤ) (bcLastIdx r (Nat.one_le_of_lt hr))) := by
        rw [Pi.smul_apply, Pi.single_eq_same]
        change Even (2 : ℤ)
        exact even_two
      have hy : oddEmb (unitaryInvolution F 2 n) r
          (suLong (unitaryInvolution F 2 n) (Sum.inl (cLastIdx r hr)) c) = x := by
        rw [oddEmb_suLong, sCast_inl, finCastOdd_cLastIdx, hxc]
      exact (oddFrameMap_eq_of_even hFn hr Ψ₀ θ hEven x
        (suLong (unitaryInvolution F 2 n) (Sum.inl (cLastIdx r hr)) c) hy).trans
        (hd.long_last c hc).1
  · obtain ⟨c, hc0, hxc⟩ := (mem_rootGroup_iff_suLong_odd
      (unitaryInvolution_involutive hFn) (a := Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr)))
      (toStd_bc2_neg hr).2.1 x).mp x.2
    have hc : unitaryInvolution F 2 n c = c := add_map_eq_zero_iff.1 hc0
    refine ⟨suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) c, ?_, ?_⟩
    · rw [su3Emb_suLong_inr (σ := unitaryInvolution F 2 n)
        (Nat.not_even_two_mul_add_one r) (bcLastIdx r (Nat.one_le_of_lt hr)) c, hxc]
    · have hEven : Even ((-(2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) :
          Fin ((2 * r + 1) / 2) → ℤ) (bcLastIdx r (Nat.one_le_of_lt hr))) := by
        rw [Pi.neg_apply, Pi.smul_apply, Pi.single_eq_same]
        change Even (-(2 : ℤ))
        exact even_neg.mpr even_two
      have hy : oddEmb (unitaryInvolution F 2 n) r
          (suLong (unitaryInvolution F 2 n) (Sum.inr (cLastIdx r hr)) c) = x := by
        rw [oddEmb_suLong, sCast_inr, finCastOdd_cLastIdx, hxc]
      exact (oddFrameMap_eq_of_even hFn hr Ψ₀ θ hEven x
        (suLong (unitaryInvolution F 2 n) (Sum.inr (cLastIdx r hr)) c) hy).trans
        (hd.long_last c hc).2

theorem extendsToHom_pairRoots_last (hd : OddFrameCompatible hFn hr Ψ₀ θ) :
    ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcLastIdx r (Nat.one_le_of_lt hr))
        (bcLastIdx r (Nat.one_le_of_lt hr))) (oddFrameMap hFn hr Ψ₀ θ) := by
  refine extendsToHom_of_injective (D := Unitary.rootDatum hFn (2 * r + 1))
    (K := SU (unitaryInvolution F 2 n) (2 * r + 1))
    (l := su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcLastIdx r (Nat.one_le_of_lt hr)))
    (su3Emb_injective (σ := unitaryInvolution F 2 n) (n := 2 * r + 1)
      (Nat.not_even_two_mul_add_one r) (bcLastIdx r (Nat.one_le_of_lt hr))) θ ?_
  intro γ hγ g
  exact hd.exists_su3Emb_eq_oddFrameMap hγ g

private theorem exists_a1bc1_factor_data (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    {i : Fin ((2 * r + 1) / 2)} (hi : i.val + 3 ≤ r) :
    ∃ N : Subgroup (SU (unitaryInvolution F 2 n) (2 * r)),
      N.map (oddEmb (unitaryInvolution F 2 n) r) =
        CFSG.LieType.CurtisTits.rankOne
          (CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
            (unitaryInvolution_involutive hFn) (2 * r + 1)) i ∧
      (∀ (x : N) (A : SU (unitaryInvolution F 2 n) 3),
        Commute (((oddEmb (unitaryInvolution F 2 n) r).comp N.subtype) x)
          (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
            (bcLastIdx r (Nat.one_le_of_lt hr)) A)) ∧
      (∀ (x : N) (A : SU (unitaryInvolution F 2 n) 3),
        Commute ((Ψ₀.comp N.subtype) x) (θ A)) := by
  let σ : F ≃+* F := unitaryInvolution F 2 n
  let hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hFn
  let L : Fin ((2 * r + 1) / 2) := bcLastIdx r (Nat.one_le_of_lt hr)
  let i' : Fin (2 * r / 2) := (finCastOdd r).symm i
  have hi' : i'.val = i.val := by simp [i']
  have hik' : i'.val + 3 ≤ r := by
    rw [hi']
    exact hi
  have hLodd : ¬L.val + 1 < (2 * r + 1) / 2 := by
    simp only [L, bcLastIdx, Fin.val_mk]
    omega
  have hikL : i.val + 2 ≤ L.val := by
    simp only [L, bcLastIdx, Fin.val_mk]
    omega
  have hk' : i'.val + 1 ≠ r := by omega
  let N : Subgroup (SU σ (2 * r)) := CFSG.LieType.CurtisTits.rankOne
    (CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r)) i'
  have hNmap : N.map (oddEmb σ r) = CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r + 1)) i := by
    change (CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r)) i').map (oddEmb σ r) = _
    rw [map_rankOne_oddEmb (σ := σ) (hσ := hσ) (r := r) (k := i') hk']
    simp only [i', Equiv.apply_symm_apply]
  have hcommK : ∀ (x : N) (A : SU σ 3),
      Commute (((oddEmb σ r).comp N.subtype) x)
        (su3Emb σ (Nat.not_even_two_mul_add_one r) L A) := by
    intro x A
    have hx : oddEmb σ r (x : SU σ (2 * r)) ∈ CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r + 1)) i := by
      have hm := Subgroup.mem_map_of_mem (f := oddEmb σ r) x.2
      rwa [hNmap] at hm
    have hA : su3Emb σ (Nat.not_even_two_mul_add_one r) L A ∈
        CFSG.LieType.CurtisTits.rankOne
          (CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r + 1)) L := by
      rw [← range_su3Emb_last hFn (Nat.not_even_two_mul_add_one r) (k := L) hLodd]
      exact ⟨A, rfl⟩
    exact commute_of_mem_rankOne_of_mem_rankOne_last (σ := σ) (hσ := hσ)
      (n := 2 * r + 1) (Nat.not_even_two_mul_add_one r) hLodd hikL hx hA
  have hcomm : ∀ (x : N) (A : SU σ 3),
      Commute ((Ψ₀.comp N.subtype) x) (θ A) := by
    intro x A
    exact hd.commute_short i' hik' (x : SU σ (2 * r)) x.2 A
  exact ⟨N, hNmap, hcommK, hcomm⟩

private theorem injective_a1bc1_coprod {i : Fin ((2 * r + 1) / 2)} (hi : i.val + 3 ≤ r)
    (N : Subgroup (SU (unitaryInvolution F 2 n) (2 * r)))
    (hNmap : N.map (oddEmb (unitaryInvolution F 2 n) r) =
      CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
          (unitaryInvolution_involutive hFn) (2 * r + 1)) i)
    (hcommK : ∀ (x : N) (A : SU (unitaryInvolution F 2 n) 3),
      Commute (((oddEmb (unitaryInvolution F 2 n) r).comp N.subtype) x)
        (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
          (bcLastIdx r (Nat.one_le_of_lt hr)) A)) :
    Function.Injective (((oddEmb (unitaryInvolution F 2 n) r).comp N.subtype).noncommCoprod
      (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr))) hcommK) := by
  have hLodd : ¬(bcLastIdx r (Nat.one_le_of_lt hr)).val + 1 < (2 * r + 1) / 2 := by
    simp only [bcLastIdx, Fin.val_mk]
    omega
  have hikL : i.val + 2 ≤ (bcLastIdx r (Nat.one_le_of_lt hr)).val := by
    have h := hi
    simp only [bcLastIdx, Fin.val_mk] at h ⊢
    omega
  rw [MonoidHom.noncommCoprod_injective]
  refine ⟨?_, ?_, ?_⟩
  · exact (oddEmb_injective (σ := unitaryInvolution F 2 n) (r := r)).comp N.subtype_injective
  · exact su3Emb_injective (σ := unitaryInvolution F 2 n) (n := 2 * r + 1)
      (Nat.not_even_two_mul_add_one r) (bcLastIdx r (Nat.one_le_of_lt hr))
  · have h1 : ((oddEmb (unitaryInvolution F 2 n) r).comp N.subtype).range =
        CFSG.LieType.CurtisTits.rankOne
          (CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
            (unitaryInvolution_involutive hFn) (2 * r + 1)) i := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hNmap]
    have h2 : (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr))).range =
        CFSG.LieType.CurtisTits.rankOne
          (CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
            (unitaryInvolution_involutive hFn) (2 * r + 1))
          (bcLastIdx r (Nat.one_le_of_lt hr)) :=
      range_su3Emb_last hFn (Nat.not_even_two_mul_add_one r)
        (k := bcLastIdx r (Nat.one_le_of_lt hr)) hLodd
    rw [h1, h2]
    exact disjoint_iff.2 (rankOne_inf_rankOne_last_eq_bot
      (σ := unitaryInvolution F 2 n) (hσ := unitaryInvolution_involutive hFn)
      (n := 2 * r + 1) (Nat.not_even_two_mul_add_one r) hLodd hikL)

theorem extendsToHom_pairRoots_a1bc1 (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    {i : Fin ((2 * r + 1) / 2)} (hi : i.val + 3 ≤ r) :
    ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (pairRoots (Unitary.rootDatum hFn (2 * r + 1)) i
        (bcLastIdx r (Nat.one_le_of_lt hr))) (oddFrameMap hFn hr Ψ₀ θ) := by
  obtain ⟨N, hNmap, hcommK, hcomm⟩ := exists_a1bc1_factor_data hd hi
  let σ : F ≃+* F := unitaryInvolution F 2 n
  let L : Fin ((2 * r + 1) / 2) := bcLastIdx r (Nat.one_le_of_lt hr)
  let l : N × SU σ 3 →* SU σ (2 * r + 1) :=
    ((oddEmb σ r).comp N.subtype).noncommCoprod
      (su3Emb σ (Nat.not_even_two_mul_add_one r) L) hcommK
  let φ : N × SU σ 3 →* H := (Ψ₀.comp N.subtype).noncommCoprod θ hcomm
  have hlinj : Function.Injective l := by
    change Function.Injective (MonoidHom.noncommCoprod
      ((oddEmb (unitaryInvolution F 2 n) r).comp N.subtype)
      (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr))) hcommK)
    exact injective_a1bc1_coprod (hFn := hFn) (hr := hr) hi N hNmap hcommK
  refine extendsToHom_of_injective (D := Unitary.rootDatum hFn (2 * r + 1))
    (K := SU σ (2 * r + 1)) (l := l) hlinj φ ?_
  intro γ hγ g
  have hiL : i ≠ L := by
    intro h
    have hval := congrArg Fin.val h
    simp only [L, bcLastIdx, Fin.val_mk] at hval
    omega
  rcases eq_single_or_mem_pairRoots_last hFn hr hi hγ with hsingle | hlast
  · rcases hsingle with rfl | rfl
    · have hEven : Even ((Pi.single i 1 : Fin ((2 * r + 1) / 2) → ℤ) L) := by
        rw [Pi.single_eq_of_ne (Ne.symm hiL)]
        exact Even.zero
      have hg : (g : SU σ (2 * r + 1)) ∈ N.map (oddEmb σ r) := by
        rw [hNmap]
        exact Subgroup.mem_sup_left g.2
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hg
      refine ⟨(⟨y, hy⟩, 1), ?_, ?_⟩
      · change ((oddEmb σ r).comp N.subtype) (⟨y, hy⟩ : N) * su3Emb σ
          (Nat.not_even_two_mul_add_one r) L 1 = g
        rw [map_one, mul_one]
        exact hxy
      · change oddFrameMap hFn hr Ψ₀ θ (Pi.single i 1) g =
          ((Ψ₀.comp N.subtype) (⟨y, hy⟩ : N)) * θ 1
        rw [map_one, mul_one]
        exact oddFrameMap_eq_of_even hFn hr Ψ₀ θ hEven g y hxy
    · have hEven : Even ((-Pi.single i 1 : Fin ((2 * r + 1) / 2) → ℤ) L) := by
        rw [Pi.neg_apply, Pi.single_eq_of_ne (Ne.symm hiL)]
        exact Even.zero
      have hg : (g : SU σ (2 * r + 1)) ∈ N.map (oddEmb σ r) := by
        rw [hNmap]
        exact Subgroup.mem_sup_right g.2
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hg
      refine ⟨(⟨y, hy⟩, 1), ?_, ?_⟩
      · change ((oddEmb σ r).comp N.subtype) (⟨y, hy⟩ : N) * su3Emb σ
          (Nat.not_even_two_mul_add_one r) L 1 = g
        rw [map_one, mul_one]
        exact hxy
      · change oddFrameMap hFn hr Ψ₀ θ (-Pi.single i 1) g =
          ((Ψ₀.comp N.subtype) (⟨y, hy⟩ : N)) * θ 1
        rw [map_one, mul_one]
        exact oddFrameMap_eq_of_even hFn hr Ψ₀ θ hEven g y hxy
  · obtain ⟨A, hA, hval⟩ := hd.exists_su3Emb_eq_oddFrameMap hlast g
    refine ⟨(1, A), ?_, ?_⟩
    · change ((oddEmb σ r).comp N.subtype) 1 * su3Emb σ
        (Nat.not_even_two_mul_add_one r) L A = g
      rw [map_one, one_mul]
      exact hA
    · change oddFrameMap hFn hr Ψ₀ θ γ g = ((Ψ₀.comp N.subtype) 1) * θ A
      rw [map_one, one_mul]
      exact hval

theorem extendsToHom_cone (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    (hPL : ∀ α ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcPrevIdx r hr)
        (bcLastIdx r (Nat.one_le_of_lt hr)),
      ∀ β ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcPrevIdx r hr)
        (bcLastIdx r (Nat.one_le_of_lt hr)),
      ¬CFSG.LieType.Universal.IsNegMultiple α β →
      ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
        ((Unitary.rootDatum hFn (2 * r + 1)).cone α β ∩
          pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcPrevIdx r hr)
            (bcLastIdx r (Nat.one_le_of_lt hr))) (oddFrameMap hFn hr Ψ₀ θ)) :
    ∀ i j, ∀ α ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1)) i j,
      ∀ β ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1)) i j,
      ¬CFSG.LieType.Universal.IsNegMultiple α β →
      ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
        ((Unitary.rootDatum hFn (2 * r + 1)).cone α β ∩
          pairRoots (Unitary.rootDatum hFn (2 * r + 1)) i j) (oddFrameMap hFn hr Ψ₀ θ) := by
  let L := bcLastIdx r (Nat.one_le_of_lt hr)
  have hlocal : ∀ i : Fin ((2 * r + 1) / 2),
      ∀ α ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1)) i L,
      ∀ β ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1)) i L,
      ¬CFSG.LieType.Universal.IsNegMultiple α β →
      ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
        ((Unitary.rootDatum hFn (2 * r + 1)).cone α β ∩
          pairRoots (Unitary.rootDatum hFn (2 * r + 1)) i L)
        (oddFrameMap hFn hr Ψ₀ θ) := by
    intro i α hα β hβ hneg
    by_cases hiL : i = L
    · subst hiL
      exact (hd.extendsToHom_pairRoots_last).mono Set.inter_subset_right
    · by_cases hiP : i = bcPrevIdx r hr
      · subst hiP
        exact hPL α hα β hβ hneg
      · have hi : i.val + 3 ≤ r := by
          have hlt := i.isLt
          have hLval : L.val = r - 1 := by
            simp only [L, bcLastIdx, Fin.val_mk]
          have hPval : (bcPrevIdx r hr).val = r - 2 := by
            simp only [bcPrevIdx, Fin.val_mk]
          have hneL : i.val ≠ r - 1 := by
            intro h
            exact hiL (Fin.ext (by rw [hLval]; exact h))
          have hneP : i.val ≠ r - 2 := by
            intro h
            exact hiP (Fin.ext (by rw [hPval]; exact h))
          omega
        exact (hd.extendsToHom_pairRoots_a1bc1 hi).mono Set.inter_subset_right
  intro i j α hα β hβ hneg
  by_cases hjL : j = L
  · subst hjL
    exact hlocal i α hα β hβ hneg
  · by_cases hiL : i = L
    · subst hiL
      rw [pairRoots_comm (D := Unitary.rootDatum hFn (2 * r + 1)) L j] at hα hβ ⊢
      exact hlocal j α hα β hβ hneg
    · exact (extendsToHom_pairRoots_oddFrameMap_of_ne_last hFn hr Ψ₀ θ hiL hjL).mono
        Set.inter_subset_right

end OddFrameCompatible
end CFSG.Timmesfeld.Transvection
