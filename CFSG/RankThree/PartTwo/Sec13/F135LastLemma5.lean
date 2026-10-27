module

public import CFSG.RankThree.PartTwo.Sec13.F135LastPerfect
public import CFSG.RankThree.PartTwo.Sec13.F135LastCritical
public import CFSG.RankThree.PartTwo.Sec13.F135LastFixed
public import CFSG.RankThree.PartTwo.Sec13.F135LastWeights
public import CFSG.RankThree.PartTwo.Sec13.F135LastFourCube
public import CFSG.RankThree.PartTwo.Sec13.F135LastBridge
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open scoped commutatorElement

universe u

theorem L10a {V : Type u} [Group V] [Finite V] (hVc : ∀ v w : V, v * w = w * v)
    (hV3 : ∀ v : V, v ^ 3 = 1)
    {T : Type*} [Group T] [Finite T] (hT : ∀ t : T, t * t = 1) {n : ℕ} (hn : 1 ≤ n)
    (hcard : Nat.card T = 2 ^ n) (ρ : T →* MulAut V) (hρ : Function.Injective ρ) :
    ∃ t : T, t ≠ 1 ∧ 3 ^ (n - 1) ≤ Nat.card (fixedSubgroup (ρ t)) := by
  obtain ⟨W, _, _, _, ρ', hker, hcardW⟩ := exists_representation hVc hV3 ρ
  have hinj : Function.Injective ρ' := by
    rw [injective_iff_map_eq_one]
    intro t ht
    exact (injective_iff_map_eq_one ρ).1 hρ t ((hker t).2 ht)
  obtain ⟨t, ht1, hdim⟩ := L10a_lin hT hn hcard ρ' hinj
  exact ⟨t, ht1, by rw [hcardW t]; exact Nat.pow_le_pow_right (by norm_num) hdim⟩

theorem L10b {V : Type u} [Group V] [Finite V] (hVc : ∀ v w : V, v * w = w * v)
    (hV3 : ∀ v : V, v ^ 3 = 1)
    {B : Type*} [Group B] [Finite B] (A : Subgroup B) (x : B) (hAx : FourCubeSeven A x)
    (ρ : B →* MulAut V) (hfaith : ∀ a ∈ A, a ^ 2 = 1 → a ≠ 1 → ρ a ≠ 1) :
    ∃ a ∈ A, a ^ 2 = 1 ∧ a ≠ 1 ∧ 3 ^ 6 ≤ Nat.card (fixedSubgroup (ρ a)) := by
  obtain ⟨W, _, _, _, ρ', hker, hcardW⟩ := exists_representation hVc hV3 ρ
  obtain ⟨a, haA, ha2, ha1, hdim⟩ := L10b_lin A x hAx ρ'
    (fun a ha h2 h1 h => hfaith a ha h2 h1 ((hker a).2 h))
  exact ⟨a, haA, ha2, ha1, by rw [hcardW a]; exact Nat.pow_le_pow_right (by norm_num) hdim⟩

theorem frattini_quotient_elementary {Q : Type u} [Group Q] [Finite Q] (hQ : IsPGroup 3 Q) :
    (∀ v w : Q ⧸ frattini Q, v * w = w * v) ∧ (∀ v : Q ⧸ frattini Q, v ^ 3 = 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hcomm, hpow, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hQ
  exact ⟨fun v w => hcomm.is_comm.comm v w, hpow⟩

theorem even_card_quotient {K : Type*} [Group K] [Finite K] (hKperf : commutator K = ⊤)
    (N : Subgroup K) [N.Normal] (hS : IsSimpleGroup (K ⧸ N)) :
    Even (Nat.card (K ⧸ N)) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  haveI : Group.IsSolvable (K ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hKperf
  haveI : Group.IsPerfect (K ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  haveI : Nontrivial (K ⧸ N) := hS.toNontrivial
  exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance

theorem lemma5_abstract {P : Type u} [Group P] [Finite P] (hP : IsPGroup 3 P)
    {K : Type u} [Group K] [Finite K] (φ : K →* MulAut P) (hφ : φ ≠ 1)
    (hrank : ∀ t : K, t ≠ 1 → t * t = 1 → CFSG.pRank 3 (fixedSubgroup (φ t)) ≤ 3)
    (hKperf : commutator K = ⊤) (N : Subgroup K) [N.Normal] (hNodd : Odd (Nat.card N))
    (hS : IsSimpleGroup (K ⧸ N))
    (hstruct : (∃ T : Subgroup K, (∀ t ∈ T, t * t = 1) ∧ Nat.card T = 2 ^ 6) ∨
        ∃ (A : Subgroup K) (x : K), FourCubeSeven A x) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have heven := even_card_quotient hKperf N hS
  have hKgen := closure_twoElements_eq_top hKperf N hNodd hS heven
  have hdich : ∀ N₁ : Subgroup K, N₁.Normal → N₁ = ⊤ ∨ N₁ ≤ N :=
    fun N₁ h => by haveI := h; exact normal_dichotomy hKperf N hNodd hS N₁
  obtain ⟨Q, ψ, hQexp, hQcl, hcompat, hfaith⟩ :=
    exists_faithful_action hP φ hφ hKgen N hNodd hdich
  have hQ3 : IsPGroup 3 ↥Q := hP.to_subgroup Q
  obtain ⟨hVc, hV3⟩ := frattini_quotient_elementary hQ3
  have hbound : ∀ t : K, t ≠ 1 → t * t = 1 → Nat.card (fixedSubgroup (ψ t)) ≤ 3 ^ 4 :=
    fun t ht1 ht2 => card_fixed_le hP Q hQexp hQcl φ ψ hcompat t ht2 (hrank t ht1 ht2)
  have hfaith2 : ∀ y : K, y ^ 2 = 1 → ψ y = 1 → y = 1 :=
    fun y hy => hfaith y ⟨1, by simpa using hy⟩
  rcases hstruct with ⟨T, hT, hTcard⟩ | ⟨A, x, hAx⟩
  · have hT' : ∀ t : T, t * t = 1 := fun t => Subtype.ext (hT t t.2)
    have hinj : Function.Injective (ψ.comp T.subtype) := by
      rw [injective_iff_map_eq_one]
      intro t ht
      have h2 : (t : K) ^ 2 = 1 := by rw [pow_two]; exact hT t t.2
      exact Subtype.ext (hfaith2 t h2 ht)
    obtain ⟨t, ht1, hge⟩ := L10a hVc hV3 hT' (n := 6) (by norm_num) hTcard (ψ.comp T.subtype) hinj
    have hle := hbound (t : K) (fun h => ht1 (Subtype.ext h)) (hT t t.2)
    have h54 : 3 ^ 5 ≤ 3 ^ 4 := hge.trans hle
    norm_num at h54
  · obtain ⟨a, haA, ha2, ha1, hge⟩ := L10b hVc hV3 A x hAx ψ
      (fun a _ h2 h1 hψ => h1 (hfaith2 a h2 hψ))
    have hle := hbound a ha1 (by rw [← pow_two]; exact ha2)
    have h64 : 3 ^ 6 ≤ 3 ^ 4 := hge.trans hle
    norm_num at h64

end CFSG.RankThree.PartTwo.Sec13.F135Last
