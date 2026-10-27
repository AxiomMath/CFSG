module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup
open scoped commutatorElement

theorem s16_LemmaP_exists_fixed {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} (hA : IsPGroup 2 A)
    {N : Subgroup W} (hN : N ≠ ⊥) (hAN : ∀ a ∈ A, ∀ n ∈ N, a n ∈ N) :
    ∃ n ∈ N, n ≠ 1 ∧ ∀ a ∈ A, a n = n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let s : SubMulAction A W :=
    { carrier := (N : Set W)
      smul_mem' := fun a n hn => hAN a a.2 n hn }
  have hmod := hA.card_modEq_card_fixedPoints s
  have hcard : Nat.card s = Nat.card N := rfl
  have hN2 : IsPGroup 2 N := (isPGroup_two_of_sq_eq_one hW).to_subgroup N
  obtain ⟨k, hk⟩ := hN2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hN (Subgroup.card_eq_one.1 hk)
  have h2 : 2 ∣ Nat.card s := by
    rw [hcard, hk]
    exact dvd_pow_self 2 hk0
  have h3 : 2 ∣ Nat.card (MulAction.fixedPoints A s) := by
    unfold Nat.ModEq at hmod
    exact Nat.dvd_of_mod_eq_zero (by rw [← hmod]; exact Nat.mod_eq_zero_of_dvd h2)
  let one : s := ⟨1, N.one_mem⟩
  have hone : one ∈ MulAction.fixedPoints A s := by
    intro a
    apply Subtype.ext
    show (a : MulAut W) 1 = 1
    exact map_one _
  haveI : Nonempty (MulAction.fixedPoints A s) := ⟨⟨one, hone⟩⟩
  have h4 : 0 < Nat.card (MulAction.fixedPoints A s) := Nat.card_pos
  have h5 : 1 < Nat.card (MulAction.fixedPoints A s) := by
    have := Nat.le_of_dvd h4 h3
    omega
  haveI : Nontrivial (MulAction.fixedPoints A s) := Finite.one_lt_card_iff_nontrivial.mp h5
  obtain ⟨x, hx⟩ := exists_ne (⟨one, hone⟩ : MulAction.fixedPoints A s)
  refine ⟨x.1.1, x.1.2, fun h1 => hx (Subtype.ext (Subtype.ext h1)), fun a ha => ?_⟩
  have := x.2 ⟨a, ha⟩
  exact congrArg Subtype.val this

theorem s16_LemmaP_normalizes_inf_centralizer {G : Type*} [Group G] {A X S : Subgroup G}
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hSA : S ≤ A)
    (hAX : A ≤ normalizer (X : Set G)) :
    A ≤ normalizer ((X ⊓ centralizer (S : Set G) : Subgroup G) : Set G) := by
  have key : ∀ b ∈ A, ∀ y ∈ X ⊓ centralizer (S : Set G),
      b * y * b⁻¹ ∈ X ⊓ centralizer (S : Set G) := by
    intro b hb y hy
    obtain ⟨hyX, hyS⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hAX hb) y).1 hyX, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hc : Commute h b := hAcomm h (hSA hh) b hb
    have hy' : Commute h y := Subgroup.mem_centralizer_iff.1 hyS h hh
    exact ((hc.mul_right hy').mul_right hc.inv_right).eq
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key a ha y, fun hy => ?_⟩
  have := key a⁻¹ (A.inv_mem ha) _ hy
  simpa [mul_assoc] using this

theorem s16_LemmaP_mem_fixV_of_commute {W : Type*} [CommGroup W] {X B : Subgroup (MulAut W)}
    (hXB : ∀ x ∈ X, ∀ b ∈ B, b * x = x * b) {x : MulAut W} (hx : x ∈ X) {u : W}
    (hu : u ∈ fixV B) : x u ∈ fixV B := by
  intro b hb
  have h1 : b (x u) = (b * x) u := rfl
  have h2 : (x * b) u = x (b u) := rfl
  rw [h1, hXB x hx b hb, h2, hu b hb]

theorem s16_LemmaP_commutator_le_centSub {W : Type*} [CommGroup W] {X A : Subgroup (MulAut W)}
    (hXU : ∀ x ∈ X, ∀ u ∈ fixV A, x u ∈ fixV A) : ⁅X, A⁆ ≤ centSub (fixV A) := by
  rw [Subgroup.commutator_le]
  intro x hx a ha
  rw [mem_centSub]
  intro u hu
  have h1 : a⁻¹ u = u := hu a⁻¹ (A.inv_mem ha)
  have h2 : x⁻¹ u ∈ fixV A := hXU x⁻¹ (X.inv_mem hx) u hu
  have h3 : a (x⁻¹ u) = x⁻¹ u := h2 a ha
  have h4 : ⁅x, a⁆ u = x (a (x⁻¹ (a⁻¹ u))) := by
    rw [commutatorElement_def]
    rfl
  rw [h4, h1, h3]
  simp

theorem s16_LemmaP_normalizes_commutator {G : Type*} [Group G] {A X : Subgroup G}
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAX : A ≤ normalizer (X : Set G)) :
    ∀ a ∈ A, ∀ z ∈ ⁅X, A⁆, a * z * a⁻¹ ∈ ⁅X, A⁆ := by
  intro a ha z hz
  have hle : ⁅X, A⁆ ≤ (⁅X, A⁆).comap (MulAut.conj a).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro x hx b hb
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj a).toMonoidHom ⁅x, b⁆ = ⁅a * x * a⁻¹, b⁆ := by
      have hab : a * b * a⁻¹ = b := by
        rw [hAcomm a ha b hb]; group
      calc (MulAut.conj a).toMonoidHom ⁅x, b⁆ = ⁅a * x * a⁻¹, a * b * a⁻¹⁆ := by
            simp [commutatorElement_def]; group
        _ = ⁅a * x * a⁻¹, b⁆ := by rw [hab]
    rw [e]
    exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 (hAX ha) x).1 hx) hb
  exact Subgroup.mem_comap.1 (hle hz)

theorem s16_LemmaP_commSub_ne_bot {W : Type*} [CommGroup W] {Z : Subgroup (MulAut W)}
    (hZ : Z ≠ ⊥) : commSub (⊤ : Subgroup W) Z ≠ ⊥ := by
  intro h
  rw [commSub_eq_bot_iff] at h
  apply hZ
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  ext w
  exact h (Subgroup.mem_top w) z hz

theorem s16_LemmaP_commSub_invariant {W : Type*} [CommGroup W] {A Z : Subgroup (MulAut W)}
    (hAZ : ∀ a ∈ A, ∀ z ∈ Z, a * z * a⁻¹ ∈ Z) :
    ∀ a ∈ A, ∀ n ∈ commSub (⊤ : Subgroup W) Z, a n ∈ commSub (⊤ : Subgroup W) Z := by
  intro a ha n hn
  refine Subgroup.closure_induction (p := fun n _ => a n ∈ commSub (⊤ : Subgroup W) Z)
    ?_ ?_ ?_ ?_ hn
  · rintro _ ⟨z, hz, w, -, rfl⟩
    have e : a (z w * w⁻¹) = (a * z * a⁻¹) (a w) * (a w)⁻¹ := by
      simp
    rw [e]
    exact Subgroup.subset_closure ⟨a * z * a⁻¹, hAZ a ha z hz, a w, Subgroup.mem_top _, rfl⟩
  · simp
  · intro x y _ _ hx hy
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    rw [map_inv]
    exact Subgroup.inv_mem _ hx

theorem s16_LemmaP_step {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A X : Subgroup (MulAut W)} (hAel : IsElemAbelian2 A) (hX : Odd (Nat.card X))
    (hAX : A ≤ normalizer (X : Set (MulAut W)))
    (hXU : ∀ x ∈ X, ∀ u ∈ fixV A, x u ∈ fixV A) : ⁅X, A⁆ = ⊥ := by
  by_contra hne
  have hZX : ⁅X, A⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro x hx a ha
    rw [commutatorElement_def]
    have h1 : a * x⁻¹ * a⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.1 (hAX ha) x⁻¹).1 (X.inv_mem hx)
    have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    rw [e]
    exact X.mul_mem hx h1
  have hZodd : Odd (Nat.card (⁅X, A⁆ : Subgroup (MulAut W))) :=
    Odd.of_dvd_nat hX (Subgroup.card_dvd_of_le hZX)
  have hZc := s16_LemmaP_commutator_le_centSub hXU
  have hZA := s16_LemmaP_normalizes_commutator hAel.1 hAX
  obtain ⟨-, hinter⟩ := coprime_decomp hZodd hW (W := (⊤ : Subgroup W))
    (fun _ _ _ _ => Subgroup.mem_top _)
  have hNne := s16_LemmaP_commSub_ne_bot hne
  have hNA := s16_LemmaP_commSub_invariant hZA
  have hAp : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by simpa using hAel.2 a a.2)⟩
  obtain ⟨n, hnN, hn1, hnA⟩ := s16_LemmaP_exists_fixed hW hAp hNne hNA
  have hnZ : n ∈ fixV ⁅X, A⁆ := fun z hz => hZc hz n hnA
  have hmem : n ∈ commSub (⊤ : Subgroup W) ⁅X, A⁆ ⊓ ((⊤ : Subgroup W) ⊓ fixV ⁅X, A⁆) :=
    ⟨hnN, Subgroup.mem_top _, hnZ⟩
  rw [hinter] at hmem
  exact hn1 (Subgroup.mem_bot.1 hmem)

theorem thin_four_twentySix_commutator_eq_bot {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y A X : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 Y)
    (hX : Odd (Nat.card X)) (hAX : A ≤ normalizer (X : Set (MulAut W))) : ⁅X, A⁆ = ⊥ := by
  obtain ⟨-, hA1, hAel, hAfix⟩ := hA
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 hA1
  haveI : IsMulCommutative A := ⟨⟨fun x y => Subtype.ext (hAel.1 x x.2 y y.2)⟩⟩
  haveI : IsElementaryAbelian 2 A :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hAel.2 x x.2) }
  suffices h : ∀ n : ℕ, ∀ X : Subgroup (MulAut W), Nat.card X = n → Odd n →
      A ≤ normalizer (X : Set (MulAut W)) → ⁅X, A⁆ = ⊥ from h _ X rfl hX hAX
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hXn hXodd hAX
    by_cases hgood : ∃ B : Subgroup A, B.index = 2 ∧
        X ≤ centralizer ((B.map A.subtype : Subgroup (MulAut W)) : Set (MulAut W))
    · obtain ⟨B, hBidx, hXB⟩ := hgood
      have hB'A : B.map A.subtype ≤ A := Subgroup.map_subtype_le B
      have hm : E3.mQuot A (B.map A.subtype) < 2 := by
        have h1 : (B.map A.subtype).relIndex A = 2 := by
          rw [Subgroup.relIndex, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
          exact hBidx
        unfold E3.mQuot
        rw [h1]
        simp
      have hfix := hAfix _ hB'A hm
      refine s16_LemmaP_step hW hAel (hXn ▸ hXodd) hAX ?_
      intro x hx u hu
      rw [← hfix] at hu ⊢
      exact s16_LemmaP_mem_fixV_of_commute
        (fun x hx b hb => Subgroup.mem_centralizer_iff.1 (hXB hx) b hb) hx hu
    · have hA2 : ¬ 2 ∣ Nat.card X := by
        intro h2
        exact (Nat.not_even_iff_odd.2 (hXn ▸ hXodd)) (even_iff_two_dvd.2 h2)
      letI : MulDistribMulAction A X := Subgroup.conjMulDistribMulActionOfLeNormalizer A X hAX
      have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := X) hA2
      set Ct : Subgroup X := (centralizer (A : Set (MulAut W))).comap X.subtype with hCt
      have hle : ⨆ (B : Subgroup A) (_ : B.index = 2), CFSG.fixedPointSubgroup B X ≤ Ct := by
        refine iSup₂_le fun B hB => ?_
        set B' : Subgroup (MulAut W) := B.map A.subtype with hB'
        have hB'A : B' ≤ A := Subgroup.map_subtype_le B
        set Z : Subgroup (MulAut W) := X ⊓ centralizer (B' : Set (MulAut W)) with hZ
        have hZX : Z ≤ X := inf_le_left
        have hproper : Z ≠ X := fun h => hgood ⟨B, hB, inf_eq_left.1 h⟩
        have hZlt : Nat.card Z < n := by
          have hle' : Nat.card Z ≤ Nat.card X :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hZX)
          have hne : Nat.card Z ≠ Nat.card X := fun h =>
            hproper (Subgroup.eq_of_le_of_card_ge hZX h.ge)
          omega
        have hZodd : Odd (Nat.card Z) :=
          Odd.of_dvd_nat (hXn ▸ hXodd) (Subgroup.card_dvd_of_le hZX)
        have hN' : A ≤ normalizer (Z : Set (MulAut W)) :=
          s16_LemmaP_normalizes_inf_centralizer hAel.1 hB'A hAX
        have hbot := ih _ hZlt Z rfl hZodd hN'
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
        intro x hx
        have hxfix : ∀ b ∈ B', b * (x : MulAut W) = (x : MulAut W) * b := by
          intro b hb
          obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.1 hb
          have h1 := congrArg Subtype.val (hx ⟨b0, hb0⟩)
          change (b0 : MulAut W) * (x : MulAut W) * (b0 : MulAut W)⁻¹ = (x : MulAut W) at h1
          calc (b0 : MulAut W) * (x : MulAut W)
              = (b0 : MulAut W) * (x : MulAut W) * (b0 : MulAut W)⁻¹ * (b0 : MulAut W) := by
                group
            _ = (x : MulAut W) * (b0 : MulAut W) := by rw [h1]
        exact hbot (Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_iff.2 hxfix⟩)
      rw [hgen, top_le_iff] at hle
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      have hxC : (⟨x, hx⟩ : X) ∈ Ct := hle ▸ Subgroup.mem_top _
      exact hxC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
