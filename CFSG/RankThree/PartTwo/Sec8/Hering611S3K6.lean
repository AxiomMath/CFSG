module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S3KBase
import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofJ3

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

private theorem card_comap_mul_of_surjective {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (U : Subgroup Y) :
    Nat.card (U.comap f) * Nat.card Y = Nat.card X * Nat.card U := by
  have h1 := Subgroup.card_mul_index (U.comap f)
  rw [Subgroup.index_comap_of_surjective U hf] at h1
  have h2 := Subgroup.card_mul_index U
  rw [← h1, ← h2]
  ring

private theorem exists_subgroup_card_le_comap {X Y : Type} [Group X] [Group Y] [Finite X]
    [Finite Y] (f : X →* Y) (hf : Function.Surjective f) (W : Subgroup Y) (p : ℕ) [Fact p.Prime]
    (n : ℕ) (hW : Nat.card W = p ^ n) :
    ∃ Q : Subgroup X, Q ≤ W.comap f ∧ Nat.card Q = p ^ n := by
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_surjective hf
  have hY : 0 < Nat.card Y := Nat.card_pos
  have key := card_comap_mul_of_surjective f hf W
  have hdvd : p ^ n ∣ Nat.card (W.comap f) := by
    refine ⟨c, Nat.eq_of_mul_eq_mul_right hY ?_⟩
    rw [key, hc, hW]
    ring
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  exact ⟨Q.map (W.comap f).subtype, Subgroup.map_subtype_le Q,
    by rw [Subgroup.card_subtype, hQ]⟩

theorem exists_E27_in_join
    {K K₀ : Subgroup G} (hK₀ : K₀ ≤ K) (himg : imageSub K K₀ = ⊤)
    (e : K ⧸ aschbacherSolvableCore 3 K ≃* Blueprint.NativeSporadic.J3) :
    ∃ B : Subgroup G, B ≤ K₀ ∧ CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Bbar, hBbar, hBbarcard⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Res423Three.exists_E27_of_J3 e
  have hsurj : Function.Surjective ((QuotientGroup.mk' (aschbacherSolvableCore 3 K)).comp
      (K₀.subgroupOf K).subtype) := by
    intro kbar
    have hk : kbar ∈ imageSub K K₀ := by rw [himg]; exact Subgroup.mem_top _
    obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.mp hk
    exact ⟨⟨x, hx⟩, hxk⟩
  obtain ⟨Q, hQle, hQcard⟩ :=
    exists_subgroup_card_le_comap _ hsurj Bbar 3 3 (hBbarcard.trans (by norm_num))
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup G,
      B = Q.map (K.subtype.comp (K₀.subgroupOf K).subtype) := ⟨_, rfl⟩
  have hφinj : Function.Injective (K.subtype.comp (K₀.subgroupOf K).subtype) :=
    fun a b hab => Subtype.ext (Subtype.ext hab)
  have hBcard : Nat.card B = 3 ^ 3 := by
    rw [hBdef, Subgroup.card_map_of_injective hφinj, hQcard]
  have hBcard27 : Nat.card B = 27 := hBcard.trans (by norm_num)
  have hBmem : ∀ y ∈ B, ∃ hy : y ∈ K, y ∈ K₀ ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨y, hy⟩ ∈ Bbar := by
    intro y hy
    rw [hBdef, Subgroup.mem_map] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    exact ⟨q.1.2, Subgroup.mem_subgroupOf.mp q.2, Subgroup.mem_comap.mp (hQle hq)⟩
  have hBle : B ≤ K₀ := by
    intro y hy
    obtain ⟨-, h, -⟩ := hBmem y hy
    exact h
  have hθ := CFSG.RankThree.PartTwo.Sec11.not_three_dvd_card_inSubgroup_theta K
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 3) (hBcard27.trans (by norm_num))
  have hinj : ∀ a b : K, (a : G) ∈ B → (b : G) ∈ B →
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) a =
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) b → a = b :=
    fun a b ha hb hab => mk_injOn_of_isPGroup hBp hθ ha hb hab
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨hxK, -, hxB⟩ := hBmem x hx
    obtain ⟨hyK, -, hyB⟩ := hBmem y hy
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨x, hxK⟩ : K) *
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨y, hyK⟩ : K) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨y, hyK⟩ : K) *
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨x, hxK⟩ : K) :=
      hBbar.comm hxB hyB
    have h2 : (⟨x, hxK⟩ * ⟨y, hyK⟩ : K) = ⟨y, hyK⟩ * ⟨x, hxK⟩ := by
      refine hinj _ _ ?_ ?_ ?_
      · exact B.mul_mem hx hy
      · exact B.mul_mem hy hx
      · rw [map_mul, map_mul]
        exact h1
    exact congrArg Subtype.val h2
  have hpow : ∀ x ∈ B, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨hxK, -, hxB⟩ := hBmem x hx
    have h1 : (⟨x, hxK⟩ : K) ^ 3 = 1 := by
      refine hinj _ _ ?_ B.one_mem ?_
      · exact B.pow_mem hx 3
      · rw [map_pow, map_one]
        exact hBbar.2 _ hxB
    exact congrArg Subtype.val h1
  exact ⟨B, hBle, ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => hpow x hx⟩,
    hBcard27⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611
