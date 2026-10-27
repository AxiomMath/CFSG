module

public import CFSG.Quasithin.MS93.S36SpESec
public import CFSG.Quasithin.MS93.S38ESecMod

public section

namespace CFSG.Quasithin.MS93.S52i

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36E
open scoped commutatorElement

variable {G : Type} [Group G] {M A B : Subgroup G} {S : Type} [CommGroup S]
  {p : ↥A →* S} {ρ : ↥M →* MulAut S}

theorem irr_of_max (hs : SecData M A B S p ρ) (hBA : B ≤ A)
    (hmax : ∀ J : Subgroup G, M ≤ Subgroup.normalizer (J : Set G) → B ≤ J → J ≤ A →
      J = B ∨ J = A)
    (W : Subgroup S) (hW : ∀ m : ↥M, ∀ w ∈ W, ρ m w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  set J : Subgroup G := (W.comap p).map A.subtype with hJ
  have hmemJ : ∀ a : ↥A, (a : G) ∈ J ↔ p a ∈ W := by
    intro a
    constructor
    · rintro ⟨a', ha', he⟩
      have : a' = a := Subtype.ext he
      rw [← this]
      exact ha'
    · intro ha
      exact ⟨a, ha, rfl⟩
  have hJA : J ≤ A := Subgroup.map_subtype_le _
  have hBJ : B ≤ J := fun b hb => (hmemJ ⟨b, hBA hb⟩).2 (by
    rw [(hs.ker ⟨b, hBA hb⟩).2 hb]
    exact W.one_mem)
  have hJn : M ≤ Subgroup.normalizer (J : Set G) := by
    have key : ∀ m : ↥M, ∀ x ∈ J, (m : G) * x * (m : G)⁻¹ ∈ J := by
      intro m x hx
      have hxA := hJA hx
      rw [show x = ((⟨x, hxA⟩ : ↥A) : G) from rfl, hmemJ] at hx
      rw [hmemJ ⟨_, conj_mem hs.hMA m.2 hxA⟩, ← hs.conj m ⟨x, hxA⟩]
      exact hW m _ hx
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key ⟨m, hm⟩ x, fun hx => ?_⟩
    have := key ⟨m, hm⟩⁻¹ _ hx
    simpa [mul_assoc] using this
  rcases hmax J hJn hBJ hJA with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨a, rfl⟩ := hs.surj w
    have : (a : G) ∈ J := (hmemJ a).2 hw
    rw [h] at this
    rw [Subgroup.mem_bot, hs.ker]
    exact this
  · right
    rw [eq_top_iff]
    intro w _
    obtain ⟨a, rfl⟩ := hs.surj w
    have : (a : G) ∈ J := by rw [h]; exact a.2
    exact (hmemJ a).1 this

theorem sq_eq_one_of_irr [Finite S] (h2 : IsPGroup 2 S)
    (hirr : ∀ W : Subgroup S, (∀ m : ↥M, ∀ w ∈ W, ρ m w ∈ W) → W = ⊥ ∨ W = ⊤) (s : S) :
    s ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J : Subgroup S := (powMonoidHom 2 : S →* S).range with hJ
  have hJinv : ∀ m : ↥M, ∀ w ∈ J, ρ m w ∈ J := by
    rintro m _ ⟨v, rfl⟩
    exact ⟨ρ m v, by simp [map_pow]⟩
  rcases hirr J hJinv with hbot | htop
  · have : s ^ 2 ∈ J := ⟨s, rfl⟩
    rw [hbot] at this
    exact this
  · by_contra hs
    have hS1 : Nontrivial S := ⟨⟨s, 1, fun h1 => hs (by rw [h1, one_pow])⟩⟩
    have hsurj : Function.Surjective (powMonoidHom 2 : S →* S) := fun v => by
      have : v ∈ J := by rw [htop]; exact Subgroup.mem_top v
      exact this
    have hinj := (Finite.injective_iff_surjective).2 hsurj
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp h2)
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr hS1).ne' hn
    have hdvd : 2 ∣ Nat.card S := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx
      norm_num at hx
    exact hx1 (hinj (by simp [hx2]))

theorem rho_eq_one_of_pGroup [Finite S] (hsq : ∀ s : S, s ^ 2 = 1)
    (hirr : ∀ W : Subgroup S, (∀ m : ↥M, ∀ w ∈ W, ρ m w ∈ W) → W = ⊥ ∨ W = ⊤)
    {P : Subgroup G} (hPn : M ≤ Subgroup.normalizer (P : Set G)) (hP2 : IsPGroup 2 ↥P)
    (m : ↥M) (hm : (m : G) ∈ P) : ρ m = 1 := by
  by_cases hS1 : Nontrivial S
  · set P' := (P.subgroupOf M).map ρ with hP'
    have hP'2 : IsPGroup 2 ↥P' := by
      have h1 : IsPGroup 2 ↥(P.subgroupOf M) :=
        hP2.comap_of_injective (Subgroup.subtype M) M.subtype_injective |>.of_equiv
          (MulEquiv.refl _)
      exact h1.map ρ
    have hfix := S38E.fixV_ne_bot_of_isPGroup hsq hP'2
    have hinv : ∀ n : ↥M, ∀ s ∈ fixV P', ρ n s ∈ fixV P' := by
      intro n s hs x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' : n⁻¹ * y * n ∈ P.subgroupOf M := by
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
        rw [Subgroup.mem_subgroupOf]
        have := (Subgroup.mem_normalizer_iff.mp (hPn (M.inv_mem n.2)) y).mp hy
        simpa using this
      have h1 := hs _ ⟨n⁻¹ * y * n, hy', rfl⟩
      have e : ρ y (ρ n s) = ρ n (ρ (n⁻¹ * y * n) s) := by
        rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
      rw [e, h1]
    rcases hirr _ hinv with hb | ht
    · exact absurd hb hfix
    · ext s
      have hs : s ∈ fixV P' := by rw [ht]; exact Subgroup.mem_top s
      have := hs _ ⟨m, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
      simpa using this
  · rw [not_nontrivial_iff_subsingleton] at hS1
    ext s
    exact Subsingleton.elim _ _

theorem isIrrRep_of_max [Finite G] (hs : SecData M A B S p ρ) (hBA : B ≤ A) {L : Subgroup G}
    (hLM : L ≤ M) (hA2 : IsPGroup 2 ↥A)
    (hmax : ∀ J : Subgroup G, M ≤ Subgroup.normalizer (J : Set G) → B ≤ J → J ≤ A →
      J = B ∨ J = A)
    (hL : ∃ l ∈ L, ∃ a ∈ A, l * a * l⁻¹ * a⁻¹ ∉ B) : S38E.IsIrrRep L ρ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite S := Finite.of_surjective p hs.surj
  have hS2 : IsPGroup 2 S := hA2.of_surjective p hs.surj
  have hirr := irr_of_max hs hBA hmax
  have hsq := sq_eq_one_of_irr hS2 hirr
  refine hs.isIrrRep hBA hLM (fun a ha => ?_) (fun q hq a ha => ?_) hmax hL
  · rw [← hs.ker ⟨_, A.pow_mem ha 2⟩]
    have e : (⟨a ^ 2, A.pow_mem ha 2⟩ : ↥A) = (⟨a, ha⟩ : ↥A) ^ 2 := rfl
    rw [e, map_pow, hsq]
  · have hqM : q ∈ M := pCoreOf_le' M hq
    have h1 := rho_eq_one_of_pGroup hsq hirr (le_normalizer_pCoreOf M)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) ⟨q, hqM⟩ hq
    exact (hs.rho_eq_one_iff ⟨q, hqM⟩).1 h1 a ha

end CFSG.Quasithin.MS93.S52i
