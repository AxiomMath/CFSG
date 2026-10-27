module

public import CFSG.Quasithin.Vol2.Ch11SecBK9B

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

variable {G : Type} [Group G] {V : Subgroup G} {ι : Type} [Fintype ι] {K : Type} [Field K]
  [CharP K 2] {f : ↥V → (ι → K)} (hmul : ∀ u u' : ↥V, f (u * u') = f u + f u')

include hmul in
theorem f_one : f 1 = 0 := by
  have h := hmul 1 1
  rw [mul_one] at h
  exact (add_eq_left.mp h.symm)

@[expose] def hypHom (a : ι → K) : ↥V →* Multiplicative K where
  toFun v := Multiplicative.ofAdd (tr (a ⬝ᵥ f v))
  map_one' := by rw [f_one hmul, dotProduct_zero, tr_zero]; rfl
  map_mul' u u' := by rw [hmul, dotProduct_add, tr_add]; rfl

theorem mem_ker_hypHom (a : ι → K) (v : ↥V) : v ∈ (hypHom hmul a).ker ↔ tr (a ⬝ᵥ f v) = 0 := by
  rw [MonoidHom.mem_ker]
  exact ofAdd_eq_one

@[expose] def hypOf (a : ι → K) : Subgroup G := (hypHom hmul a).ker.map V.subtype

theorem mem_hypOf {a : ι → K} {g : G} :
    g ∈ hypOf hmul a ↔ ∃ hg : g ∈ V, tr (a ⬝ᵥ f ⟨g, hg⟩) = 0 := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, (mem_ker_hypHom hmul a v).mp hv⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, (mem_ker_hypHom hmul a _).mpr h, rfl⟩

theorem hypOf_le (a : ι → K) : hypOf hmul a ≤ V := by
  rintro _ ⟨v, -, rfl⟩
  exact v.2

theorem subgroupOf_hypOf (a : ι → K) : (hypOf hmul a).subgroupOf V = (hypHom hmul a).ker :=
  Subgroup.comap_map_eq_self_of_injective V.subtype_injective _

variable [Finite K]

theorem tr_dot_cases (hK : Nat.card K = 4) (a x : ι → K) : tr (a ⬝ᵥ x) = 0 ∨ tr (a ⬝ᵥ x) = 1 :=
  tr_eq_zero_or_one hK _

theorem mem_hypSet_hypOf [DecidableEq ι] (hK : Nat.card K = 4)
    (hsurj : Function.Surjective f) {a : ι → K} (ha : a ≠ 0) : hypOf hmul a ∈ hypSet V := by
  refine ⟨hypOf_le hmul a, ?_⟩
  rw [Subgroup.relIndex, subgroupOf_hypOf]
  obtain ⟨x, hx⟩ := exists_tr_dot_eq_one hK ha
  obtain ⟨v₀, rfl⟩ := hsurj x
  refine Subgroup.index_eq_two_iff.mpr ⟨v₀, fun b => ?_⟩
  rw [mem_ker_hypHom, mem_ker_hypHom, hmul, dotProduct_add, tr_add, hx]
  rcases tr_dot_cases hK a (f b) with h | h <;> rw [h]
  · exact Or.inr ⟨rfl, by rw [zero_add]; exact one_ne_zero⟩
  · exact Or.inl ⟨CharTwo.add_self_eq_zero 1, one_ne_zero⟩

theorem exists_param [DecidableEq ι] (hK : Nat.card K = 4) (hinj : Function.Injective f)
    (hsurj : Function.Surjective f) {U : Subgroup G} (hU : U ∈ hypSet V) :
    ∃ a : ι → K, a ≠ 0 ∧ U = hypOf hmul a := by
  classical
  have hUV : U ≤ V := hU.1
  have hidx : (U.subgroupOf V).index = 2 := hU.2
  set e : ↥V ≃ (ι → K) := Equiv.ofBijective f ⟨hinj, hsurj⟩ with he_def
  have he : ∀ v, e.symm (f v) = v := fun v => e.symm_apply_apply v
  have he' : ∀ x, f (e.symm x) = x := fun x => e.apply_symm_apply x
  have hadd : ∀ x y, e.symm (x + y) = e.symm x * e.symm y := fun x y =>
    hinj (by rw [he', hmul, he', he'])
  let χ : (ι → K) →+ K :=
    { toFun := fun x => if e.symm x ∈ U.subgroupOf V then 0 else 1
      map_zero' := by
        have h0 : e.symm 0 = 1 := hinj (by rw [he', f_one hmul])
        simp only [h0, Subgroup.one_mem, ite_true]
      map_add' := fun x y => by
        rw [hadd]
        have hm := Subgroup.mul_mem_iff_of_index_two hidx (a := e.symm x) (b := e.symm y)
        by_cases hx : e.symm x ∈ U.subgroupOf V <;> by_cases hy : e.symm y ∈ U.subgroupOf V <;>
          simp [hx, hy, hm, CharTwo.add_self_eq_zero] }
  have hχ : ∀ x, χ x = if e.symm x ∈ U.subgroupOf V then 0 else 1 := fun x => rfl
  obtain ⟨a, ha⟩ := exists_dot_eq hK χ fun x => by
    rw [hχ]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hU' : U = hypOf hmul a := by
    ext g
    rw [mem_hypOf]
    constructor
    · intro hg
      refine ⟨hUV hg, ?_⟩
      rw [← ha, hχ, he]
      simp only [show (⟨g, hUV hg⟩ : ↥V) ∈ U.subgroupOf V from hg, ite_true]
    · rintro ⟨hgV, hg⟩
      rw [← ha, hχ, he] at hg
      split_ifs at hg with h
      · exact Subgroup.mem_subgroupOf.mp h
      · exact absurd hg one_ne_zero
  refine ⟨a, fun ha0 => ?_, hU'⟩
  have htop : U.subgroupOf V = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [Subgroup.mem_subgroupOf, hU', mem_hypOf]
    exact ⟨v.2, by rw [ha0, zero_dotProduct, tr_zero]⟩
  rw [htop, Subgroup.index_top] at hidx
  omega

theorem hypOf_injective [DecidableEq ι] (hK : Nat.card K = 4) (hsurj : Function.Surjective f) :
    Function.Injective (hypOf hmul) := by
  intro a a' h
  have hiff : ∀ x, tr (a ⬝ᵥ x) = 0 ↔ tr (a' ⬝ᵥ x) = 0 := fun x => by
    obtain ⟨v, rfl⟩ := hsurj x
    have h1 : (v : G) ∈ hypOf hmul a ↔ (v : G) ∈ hypOf hmul a' := by rw [h]
    simpa only [mem_hypOf, Subtype.coe_eta, SetLike.coe_mem, exists_true_left] using h1
  have heq : ∀ x, tr ((a + a') ⬝ᵥ x) = 0 := fun x => by
    rw [add_dotProduct, tr_add]
    rcases tr_dot_cases hK a x with h0 | h0 <;> rcases tr_dot_cases hK a' x with h1 | h1
    · rw [h0, h1, add_zero]
    · exact absurd ((hiff x).mp h0) (by rw [h1]; exact one_ne_zero)
    · exact absurd ((hiff x).mpr h1) (by rw [h0]; exact one_ne_zero)
    · rw [h0, h1, CharTwo.add_self_eq_zero]
  by_contra hne
  have hne' : a + a' ≠ 0 := fun h0 => hne (funext fun i => by
    have h1 := congrFun h0 i
    simp only [Pi.add_apply, Pi.zero_apply] at h1
    exact (eq_neg_of_add_eq_zero_left h1).trans (CharTwo.neg_eq _))
  obtain ⟨x, hx⟩ := exists_tr_dot_eq_one hK hne'
  rw [heq x] at hx
  exact zero_ne_one hx

include hmul in
theorem card_hypSet_add_one [DecidableEq ι] (hK : Nat.card K = 4) (hinj : Function.Injective f)
    (hsurj : Function.Surjective f) : Nat.card ↥(hypSet V) + 1 = Nat.card (ι → K) := by
  classical
  have := Fintype.ofFinite K
  let Φ : {a : ι → K // a ≠ 0} → ↥(hypSet V) := fun a =>
    ⟨hypOf hmul a.1, mem_hypSet_hypOf hmul hK hsurj a.2⟩
  have hΦ : Function.Bijective Φ := by
    refine ⟨fun a b h => Subtype.ext (hypOf_injective hmul hK hsurj
      (congrArg Subtype.val h)), fun U => ?_⟩
    obtain ⟨a, ha, hUa⟩ := exists_param hmul hK hinj hsurj U.2
    exact ⟨⟨a, ha⟩, Subtype.ext hUa.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ), Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have : 0 < Fintype.card (ι → K) := Fintype.card_pos
  omega

include hmul in
theorem not_two_dvd_card_hypSet [DecidableEq ι] [Nonempty ι] (hK : Nat.card K = 4)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) :
    ¬ 2 ∣ Nat.card ↥(hypSet V) := by
  have h := card_hypSet_add_one hmul hK hinj hsurj
  rw [Nat.card_fun, hK] at h
  have hι : 0 < Nat.card ι := Nat.card_pos
  have h2 : 2 ∣ 4 ^ Nat.card ι := dvd_pow (by norm_num : 2 ∣ 4) hι.ne'
  omega

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
