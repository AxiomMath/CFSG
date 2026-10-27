module

public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG.Blueprint

@[expose] def ThreePrimeB3 (Q : Type) [Group Q] : Prop :=
  ∀ β : MulAut Q, β ^ 3 = 1 → ∀ C Y R : Subgroup Q, (∀ z, z ∈ C ↔ β z = z) → Y ≤ C →
    (Y.subgroupOf C).IsSubnormal → Group.IsPerfect Y → ¬ 3 ∣ Nat.card Y → R ≤ Y →
    ∀ [(R.subgroupOf Y).Normal], Group.IsSolvable R →
    (∃ f, SuzukiModel (Y ⧸ R.subgroupOf Y) 2 f) → ⁅R, Y⁆ = ⊥

namespace BThreeCensus

variable {Q Q' : Type} [Group Q] [Group Q']

theorem map_subgroupOf_subgroupMap (e : Q ≃* Q') (H K : Subgroup Q) :
    (H.subgroupOf K).map (e.subgroupMap K).toMonoidHom =
      (H.map e.toMonoidHom).subgroupOf (K.map e.toMonoidHom) := by
  ext ⟨x, hx⟩
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨k, hk, hkx⟩
    refine ⟨k, hk, ?_⟩
    have := congrArg Subtype.val hkx
    exact (by simpa using this : e k = x)
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨k, hkK, hk⟩ := hx
    have hhk : h = k := e.injective (by simpa using hk.symm)
    subst hhk
    exact ⟨⟨h, hkK⟩, hh, Subtype.ext (by simp)⟩

theorem threePrimeB3_of_mulEquiv (e : Q ≃* Q') (h : ThreePrimeB3 Q') : ThreePrimeB3 Q := by
  intro β hβ C Y R hC hYC hsn hYp hY3 hRY hRn hRs hsz
  set f : Q →* Q' := e.toMonoidHom with hf
  have hRn' : ((R.map f).subgroupOf (Y.map f)).Normal := by
    rw [← map_subgroupOf_subgroupMap]
    exact hRn.map _ (e.subgroupMap Y).surjective
  have hYp' : Group.IsPerfect (Y.map f) := Group.IsPerfect.map f
  have key := @h (MulAut.congr e β) (by rw [← map_pow, hβ, map_one]) (C.map f) (Y.map f)
    (R.map f) (fun z => ?_) (Subgroup.map_mono hYC) ?_ hYp' ?_ (Subgroup.map_mono hRY) hRn' ?_ ?_
  · rw [← Subgroup.map_commutator] at key
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp key
  · rw [MulAut.congr_apply]
    constructor
    · rintro ⟨c, hc, rfl⟩
      simp [(hC c).mp hc, hf]
    · intro hz
      refine ⟨e.symm z, (hC _).mpr ?_, by simp [hf]⟩
      apply e.injective
      simpa using hz
  · rw [← map_subgroupOf_subgroupMap]
    exact hsn.map (e.subgroupMap C).surjective
  · rwa [Subgroup.card_map_of_injective e.injective]
  · have := hRs
    exact Group.isSolvable_of_surjective (f := (e.subgroupMap R).toMonoidHom)
      (e.subgroupMap R).surjective
  · obtain ⟨n, hn⟩ := hsz
    obtain ⟨h2, a, ha, K, _, _, hn', hK, ⟨eK⟩⟩ := hn
    refine ⟨n, h2, a, ha, K, inferInstance, inferInstance, hn', hK, ⟨?_⟩⟩
    refine (QuotientGroup.congr (R.subgroupOf Y) ((R.map f).subgroupOf (Y.map f))
      (e.subgroupMap Y) (map_subgroupOf_subgroupMap e R Y)).symm.trans eK

theorem threePrimeB3_of_forall_not_suzukiModel
    (h : ∀ (H : Subgroup Q) (N : Subgroup H) [N.Normal] (f : ℕ), ¬ SuzukiModel (H ⧸ N) 2 f) :
    ThreePrimeB3 Q := by
  intro β _ C Y R _ _ _ _ _ _ _ _ hsz
  obtain ⟨f, hf⟩ := hsz
  exact absurd hf (h Y (R.subgroupOf Y) f)

@[expose] def suzukiOrder (a : ℕ) : ℕ :=
  (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)

theorem card_eq_suzukiOrder {T : Type} [Group T] {f : ℕ}
    (h : SuzukiModel T 2 f) : ∃ a, 1 ≤ a ∧ Nat.card T = suzukiOrder a := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  exact ⟨a, ha, by rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]; rfl⟩

theorem threePrimeB3_of_suzukiOrder_not_dvd [Finite Q]
    (h : ∀ a, 1 ≤ a → ¬ suzukiOrder a ∣ Nat.card Q) : ThreePrimeB3 Q := by
  refine threePrimeB3_of_forall_not_suzukiModel fun H N _ f hS => ?_
  obtain ⟨a, ha, hcard⟩ := card_eq_suzukiOrder hS
  refine h a ha ?_
  rw [← hcard]
  exact (Subgroup.card_quotient_dvd_card N).trans (Subgroup.card_subgroup_dvd_card H)

theorem five_dvd_suzukiOrder (a : ℕ) : 5 ∣ suzukiOrder a := by
  unfold suzukiOrder
  apply Dvd.dvd.mul_left
  have h : (2 ^ (2 * a + 1)) ^ 2 = 4 * 16 ^ a := by
    rw [← pow_mul, show (2 * a + 1) * 2 = 2 + 4 * a by ring, pow_add, pow_mul]
    norm_num
  rw [h, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem le_suzukiOrder (a : ℕ) : 2 ^ (4 * a + 2) ≤ suzukiOrder a := by
  unfold suzukiOrder
  have h1 : 1 ≤ 2 ^ (2 * a + 1) - 1 := by
    have : 2 ≤ 2 ^ (2 * a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2 : (2 ^ (2 * a + 1)) ^ 2 = 2 ^ (4 * a + 2) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [h2]
  calc 2 ^ (4 * a + 2) = 2 ^ (4 * a + 2) * 1 * 1 := by ring
    _ ≤ 2 ^ (4 * a + 2) * (2 ^ (2 * a + 1) - 1) * ((2 ^ (4 * a + 2)) + 1) := by
      gcongr
      omega

theorem le_of_suzukiOrder_dvd {M B a : ℕ} (hM : 0 < M) (hB : M < 2 ^ (4 * B + 6))
    (hdvd : suzukiOrder a ∣ M) : a ≤ B := by
  by_contra haB
  have h1 := Nat.le_of_dvd hM hdvd
  have h2 := le_suzukiOrder a
  have h3 : 2 ^ (4 * B + 6) ≤ 2 ^ (4 * a + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem threePrimeB3_of_dvd [Finite Q] {M B : ℕ}
    (hQM : Nat.card Q ∣ M) (hM : 0 < M) (hB : M < 2 ^ (4 * B + 6))
    (h : ∀ a ∈ Finset.Icc 1 B, ¬ suzukiOrder a ∣ M) : ThreePrimeB3 Q :=
  threePrimeB3_of_suzukiOrder_not_dvd fun a ha hdvd =>
    h a (Finset.mem_Icc.mpr ⟨ha, le_of_suzukiOrder_dvd hM hB (hdvd.trans hQM)⟩)
      (hdvd.trans hQM)

theorem threePrimeB3_of_not_five_dvd [Finite Q]
    (h5 : ¬ 5 ∣ Nat.card Q) : ThreePrimeB3 Q :=
  threePrimeB3_of_suzukiOrder_not_dvd fun a _ hdvd => h5 ((five_dvd_suzukiOrder a).trans hdvd)

theorem commutator_eq_bot_of_card_prime {Y R : Subgroup Q} (hRY : R ≤ Y)
    [(R.subgroupOf Y).Normal] (hYp : Group.IsPerfect Y) (hR : (Nat.card R).Prime) :
    ⁅R, Y⁆ = ⊥ := by
  set N := R.subgroupOf Y with hN
  have hNcard : Nat.card N = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRY).toEquiv
  have : Fact (Nat.card N).Prime := ⟨hNcard ▸ hR⟩
  have : IsCyclic N := isCyclic_of_prime_card rfl
  let _ : CommGroup (MulAut N) := (IsCyclic.mulAutMulEquiv N).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv N).injective
  have hker : commutator Y ≤ (MulAut.conjNormal (H := N)).ker :=
    Abelianization.commutator_subset_ker _
  rw [hYp.commutator_eq_top] at hker
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := hker (Subgroup.mem_top ⟨y, hy⟩)
  rw [MonoidHom.mem_ker] at h1
  have h2 := congrArg (fun φ : MulAut N => ((φ ⟨⟨r, hRY hr⟩, hr⟩ : N) : Y)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  have h3 := congrArg Subtype.val h2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
  calc y * r = y * r * y⁻¹ * y := by group
    _ = r * y := by rw [h3]

theorem card_eq_card_mul_card_quotient {Y R : Subgroup Q} (hRY : R ≤ Y)
    [(R.subgroupOf Y).Normal] :
    Nat.card Y = Nat.card R * Nat.card (Y ⧸ R.subgroupOf Y) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf Y), mul_comm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRY).toEquiv]

theorem threePrimeB3_of_dvd_two [Finite Q] {M : ℕ}
    (hQM : Nat.card Q ∣ M)
    (h : ∀ a, 1 ≤ a → ∀ n, n * suzukiOrder a ∣ M → ¬ 3 ∣ n → n ∣ 2) : ThreePrimeB3 Q := by
  intro β _ C Y R _ _ _ hYp hY3 hRY hRn _ hsz
  obtain ⟨f, hf⟩ := hsz
  obtain ⟨a, ha, hcard⟩ := card_eq_suzukiOrder hf
  have hYcard : Nat.card Y = Nat.card R * suzukiOrder a := by
    rw [card_eq_card_mul_card_quotient hRY, hcard]
  have hdvd : Nat.card R * suzukiOrder a ∣ M :=
    hYcard ▸ (Subgroup.card_subgroup_dvd_card Y).trans hQM
  have h3 : ¬ 3 ∣ Nat.card R := fun h3 => hY3 (hYcard ▸ Dvd.dvd.mul_right h3 _)
  rcases (Nat.dvd_prime Nat.prime_two).mp (h a ha _ hdvd h3) with h1 | h2
  · rw [Subgroup.eq_bot_of_card_eq R h1, Subgroup.commutator_bot_left]
  · exact commutator_eq_bot_of_card_prime hRY hYp (h2 ▸ Nat.prime_two)

theorem eq_bot_of_isPerfect_of_isSolvable {Y : Subgroup Q} (hYp : Group.IsPerfect Y)
    (hYs : Group.IsSolvable Y) : Y = ⊥ := by
  by_contra hY
  have : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY
  exact Group.IsPerfect.not_isSolvable Y hYs

theorem threePrimeB3_of_isSolvable
    (h : ∀ Y : Subgroup Q, ¬ 3 ∣ Nat.card Y → Group.IsSolvable Y) : ThreePrimeB3 Q := by
  intro β _ C Y R _ _ _ hYp hY3 hRY _ _ _
  have hY := eq_bot_of_isPerfect_of_isSolvable hYp (h Y hY3)
  rw [hY, Subgroup.commutator_bot_right]

theorem commutator_eq_bot_of_isSimpleGroup_or_isSolvable {C Y R : Subgroup Q}
    (hC : IsSimpleGroup C ∨ Group.IsSolvable C) (hYC : Y ≤ C) (hsn : (Y.subgroupOf C).IsSubnormal)
    (hYp : Group.IsPerfect Y) (hRY : R ≤ Y) (hRn : (R.subgroupOf Y).Normal)
    (hRs : Group.IsSolvable R) : ⁅R, Y⁆ = ⊥ := by
  suffices hR : R = ⊥ by rw [hR, Subgroup.commutator_bot_left]
  rcases hC with hC | hC
  · rcases hsn.eq_bot_or_top_of_isSimpleGroup hC with h0 | h0
    · have hY : Y = ⊥ := by
        rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hYC] at h0
        exact h0
      exact le_bot_iff.mp (hY ▸ hRY)
    · have hYeq : Y = C := le_antisymm hYC ((Subgroup.subgroupOf_eq_top).mp h0)
      subst hYeq
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf Y) with h1 | h1
      · rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hRY] at h1
        exact h1
      · have hReq : R = Y := le_antisymm hRY ((Subgroup.subgroupOf_eq_top).mp h1)
        subst hReq
        exact eq_bot_of_isPerfect_of_isSolvable hYp hRs
  · have := hC
    have hYs : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hYC) (Subgroup.inclusion_injective hYC)
    have hY := eq_bot_of_isPerfect_of_isSolvable hYp hYs
    exact le_bot_iff.mp (hY ▸ hRY)

end BThreeCensus

end CFSG.RankThree.PartTwo.Sec6
