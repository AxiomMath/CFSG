module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddFB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

namespace F53.Stellmacher.S43

namespace Odd

namespace Chain

theorem sign_eq_one_of_central :
    ∀ σ ∈ S5SylF, (∀ τ ∈ S5SylF, σ * τ = τ * σ) → Perm.sign σ = 1 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

theorem exists_chain {H U A B : Subgroup G} (hA : IsNormalIn H U A) (hB : IsNormalIn H U B)
    (hAB : A ≤ B) : ∃ (r : ℕ) (W : ℕ → Subgroup G), W 0 = A ∧ W r = B ∧
      ∀ i, i < r → IsChiefStep H U (W i) (W (i + 1)) := by
  induction A using WellFoundedGT.induction with
  | _ A ih =>
    by_cases hAB' : A = B
    · exact ⟨0, fun _ => A, rfl, hAB', fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    · obtain ⟨J, ⟨hJ, hAJ, hJB⟩, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min
        {J | IsNormalIn H U J ∧ A < J ∧ J ≤ B} ⟨B, hB, lt_of_le_of_ne hAB hAB', le_rfl⟩
      have hstep : IsChiefStep H U A J := by
        refine ⟨hJ, hA, hAJ, fun K hK hAK hKJ => ?_⟩
        rcases eq_or_lt_of_le hAK with h | h
        · exact Or.inl h.symm
        · right
          by_contra hne
          exact hmin K ⟨hK, h, hKJ.trans hJB⟩ (lt_of_le_of_ne hKJ hne)
      obtain ⟨r, W, h0, hr, hW⟩ := ih J hAJ hJ hJB
      refine ⟨r + 1, fun i => match i with | 0 => A | i + 1 => W i, rfl, hr, fun i hi => ?_⟩
      cases i with
      | zero =>
        show IsChiefStep H U A (W 0)
        rw [h0]
        exact hstep
      | succ i => exact hW i (by omega)

theorem three_le_secIdx {X : Subgroup G} (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    {L N : Subgroup G} (hstep : IsChiefStep X (pCoreOf 2 X) L N) (hnc : ¬ IsCentralStep X L N)
    {x : G} (hx : x ∈ X) (hxQ : x ∉ pCoreOf 2 X) (hxL : x ∈ oTwoRes X ⊔ pCoreOf 2 X) :
    3 ≤ secIdx (Subgroup.zpowers x) L N := by
  obtain ⟨hcS, hno⟩ := (chief_central_or_nat_or_orth hq le_rfl hstep).resolve_left hnc
  have hLN : L ≤ N := hstep.2.2.1.le
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := normalizer_left hstep
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans (pCoreOf_le 2 X)).trans hXL
  have hxc : x ∉ cSecIn X L N := by rw [hcS]; exact hxQ
  have h1 : secIdx (Subgroup.zpowers x) L N ≠ 1 := fun h =>
    hxc ((mem_cSecIn_iff hXL).mpr ⟨hx, (secIdx_eq_one_iff hNL (hXL hx)).mp h⟩)
  have h2 : secIdx (Subgroup.zpowers x) L N ≠ 2 := by
    intro h
    rcases hno with hnat | horth
    · have := IsNatSec.four_le_secIdx hnat hLN hx hxc
      omega
    · obtain ⟨θ, -, hθk, hsw⟩ := IsOrthSec.exists_swap_iff horth hLN
      have hsign := ((hsw x hx hxc).mp h).sign_eq
      obtain ⟨l, hl, q, hq', rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
        ((pCoreOf_le 2 X).trans (le_normalizer_oTwoRes X))).mp hxL
      have hlX : l ∈ X := oTwoRes_le X hl
      have hqX : q ∈ X := pCoreOf_le 2 X hq'
      have hθq : θ ⟨q, hqX⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf, hcS]
        exact hq'
      have hθl : θ ⟨l, hlX⟩ ∈ alternatingGroup (Fin 5) :=
        map_oTwoRes_le_alt θ ⟨⟨l, hlX⟩, hl, rfl⟩
      have e : (⟨l * q, hx⟩ : ↥X) = ⟨l, hlX⟩ * ⟨q, hqX⟩ := rfl
      rw [e, map_mul, hθq, mul_one] at hsign
      rw [Perm.mem_alternatingGroup, hsign] at hθl
      exact absurd hθl (by decide)
  have h0 := secIdx_pos (Subgroup.zpowers x) L N
  omega

theorem le_two_or_le_two_of_prod_le_four {f : ℕ → ℕ} {r : ℕ} (hpos : ∀ i, 0 < f i)
    (hprod : ∏ i ∈ Finset.range r, f i ≤ 4) {i j : ℕ} (hi : i < r) (hj : j < r) (hij : i ≠ j) :
    f i ≤ 2 ∨ f j ≤ 2 := by
  have h1 : ∏ k ∈ ({i, j} : Finset ℕ), f k ≤ 4 := by
    refine (Finset.prod_le_prod_of_subset_of_one_le (fun k hk => ?_) fun k _ _ => hpos k).trans
      hprod
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simpa
  rw [Finset.prod_pair hij] at h1
  by_contra hcon
  push Not at hcon
  have : 3 * 3 ≤ f i * f j := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem central_or_central_of_le_four {X : Subgroup G}
    (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5))) {W : ℕ → Subgroup G} {r : ℕ}
    (hXW : ∀ i, i ≤ r → X ≤ Subgroup.normalizer (W i : Set G))
    (hWQ : ∀ i, i ≤ r → W i ≤ pCoreOf 2 X)
    (hstep : ∀ i, i < r → IsChiefStep X (pCoreOf 2 X) (W i) (W (i + 1)))
    {x : G} (hx : x ∈ X) (hxQ : x ∉ pCoreOf 2 X) (hxL : x ∈ oTwoRes X ⊔ pCoreOf 2 X)
    (h4 : secIdx (Subgroup.zpowers x) (W 0) (W r) ≤ 4) :
    ∀ i j, i < r → j < r → i ≠ j →
      IsCentralStep X (W i) (W (i + 1)) ∨ IsCentralStep X (W j) (W (j + 1)) := by
  intro i j hi hj hij
  by_contra hcon
  push Not at hcon
  have hnorm : ∀ a b, a ≤ r → b ≤ r → W b ≤ Subgroup.normalizer (W a : Set G) :=
    fun a b ha hb => ((hWQ b hb).trans (pCoreOf_le 2 X)).trans (hXW a ha)
  have hprod := (secIdx_prod_le (F.chain_mono hstep) hnorm (fun a ha => hXW a ha hx)).trans h4
  have h3i := three_le_secIdx hq (hstep i hi) hcon.1 hx hxQ hxL
  have h3j := three_le_secIdx hq (hstep j hj) hcon.2 hx hxQ hxL
  rcases le_two_or_le_two_of_prod_le_four
    (f := fun k => secIdx (Subgroup.zpowers x) (W k) (W (k + 1))) (fun k => secIdx_pos _ _ _)
    hprod hi hj hij with h | h
  · exact absurd h (by omega)
  · exact absurd h (by omega)

end Chain

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
