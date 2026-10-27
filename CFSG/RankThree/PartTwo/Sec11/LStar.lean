module

public import CFSG.RankThree.PartTwo.Sec11.Steps
public import CFSG.RankThree.PartTwo.Sec10.Item108
public import CFSG.RankThree.PartTwo.KFacts.K73Lines

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Action

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem conj_eq_of_mem_inf_normalizer (h : Sec9.Hyp91 G A c L a R) {l : G} (hlL : l ∈ L)
    (hlW : l ∈ Subgroup.normalizer (A : Set G)) : l * c * l⁻¹ = c := by
  have hcA := h.mem_A
  have hsc : c ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    rw [h.sectionCentralizer_eq]
    exact Subgroup.mem_zpowers c
  have hz : c * l * c⁻¹ * l⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype := hsc.2 l hlL
  have hzA : c * l * c⁻¹ * l⁻¹ ∈ A := by
    have h1 : l * c⁻¹ * l⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hlW c⁻¹).mp (A.inv_mem hcA)
    have e : c * l * c⁻¹ * l⁻¹ = c * (l * c⁻¹ * l⁻¹) := by group
    rw [e]
    exact A.mul_mem hcA h1
  have h3 : (c * l * c⁻¹ * l⁻¹) ^ 3 = 1 := h.mem_partTwoF.1.2 _ hzA
  have hθ : ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 L).map L.subtype) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hz1 : c * l * c⁻¹ * l⁻¹ = 1 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    by_contra hne
    have hord : orderOf (c * l * c⁻¹ * l⁻¹) = 3 := orderOf_eq_prime h3 hne
    have h1 := Subgroup.orderOf_dvd_natCard _ hz
    rw [hord] at h1
    exact hθ h1
  have hcl : c * l = l * c := by
    calc c * l = c * l * c⁻¹ * l⁻¹ * (l * c) := by group
      _ = l * c := by rw [hz1, one_mul]
  rw [← hcl, mul_inv_cancel_right]

end Action

@[expose] def LStarTransvection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y →
      ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), (∃ k : ℕ, l ^ 3 ^ k = 1) ∧
        ∃ x ∈ A, l * x * l⁻¹ ≠ x

theorem item115_of_lStar (h97 : Sec9.Item97) (hL : Sec10.HWNormalizesL)
    (hT : LStarTransvection) : Item115 := by
  intro G _ _ A c L a R Y h hirr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨d, hdL, hd3, hA⟩ := Sec10.exists_inf_eq_zpowers h97 h.toHyp91
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hdA := hdAL.1
  have hcA := h.mem_A
  have haA := h.a_mem
  have hdpow3 : d ^ 3 = 1 := by rw [← hd3]; exact pow_orderOf_eq_one d
  have haN := h.toHyp81.a_mem_normalizer
  have key : ∀ l ∈ L ⊓ Subgroup.normalizer (A : Set G), (∃ k : ℕ, l ^ 3 ^ k = 1) →
      l * c * l⁻¹ = c ∧ l * d = d * l ∧ ∃ m : ℕ, l * a * l⁻¹ = a * d ^ m := by
    rintro l ⟨hlL, hlW⟩ ⟨k, hk⟩
    have hlc := conj_eq_of_mem_inf_normalizer h.toHyp91 hlL hlW
    have hld : l * d * l⁻¹ ∈ Subgroup.zpowers d := by
      rw [← hdL]
      exact ⟨(Subgroup.mem_normalizer_iff.mp hlW d).mp hdA,
        L.mul_mem (L.mul_mem hlL hdAL.2) (L.inv_mem hlL)⟩
    have hld' : l * d = d * l := Sec12.commute_of_conj_mem_zpowers hd3 hld hk
    have hla : l * a * l⁻¹ * a⁻¹ ∈ Subgroup.zpowers d := by
      rw [← hdL]
      refine ⟨A.mul_mem ((Subgroup.mem_normalizer_iff.mp hlW a).mp haA) (A.inv_mem haA), ?_⟩
      have h1 : a * l⁻¹ * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haN _).mp (L.inv_mem hlL)
      have e : l * a * l⁻¹ * a⁻¹ = l * (a * l⁻¹ * a⁻¹) := by group
      rw [e]
      exact L.mul_mem hlL h1
    rw [← (isOfFinOrder_of_finite d).mem_powers_iff_mem_zpowers] at hla
    obtain ⟨m, hm⟩ := Submonoid.mem_powers_iff _ _ |>.mp hla
    refine ⟨hlc, hld', m, ?_⟩
    have hda : d ^ m * a = a * d ^ m := (hcomm _ (A.pow_mem hdA m) a haA)
    calc l * a * l⁻¹ = l * a * l⁻¹ * a⁻¹ * a := by group
      _ = a * d ^ m := by rw [← hm, hda]
  have hext : ∀ g g' : G, g * c * g⁻¹ = g' * c * g'⁻¹ → g * a * g⁻¹ = g' * a * g'⁻¹ →
      g * d * g⁻¹ = g' * d * g'⁻¹ → ∀ x ∈ A, g * x * g⁻¹ = g' * x * g'⁻¹ := by
    intro g g' h1 h2 h3 x hx
    have hle : A ≤ (MulAut.conj g).toMonoidHom.eqLocus (MulAut.conj g').toMonoidHom := by
      rw [hA, Subgroup.closure_le]
      rintro _ (rfl | rfl | rfl)
      · exact h1
      · exact h2
      · exact h3
    exact hle hx
  obtain ⟨l₀, hl₀, hl₀3, x₀, hx₀A, hx₀⟩ := hT G A c L a R Y h
  obtain ⟨hl₀c, hl₀d, m₀, hl₀a⟩ := key l₀ hl₀ hl₀3
  have hl₀W := hl₀.2
  have hm₀ : m₀ % 3 ≠ 0 := by
    intro h0
    apply hx₀
    have hdm : d ^ m₀ = 1 := by
      rw [← Nat.mod_add_div m₀ 3, h0, zero_add, pow_mul, hdpow3, one_pow]
    have := hext l₀ 1 (by rw [hl₀c]; group) (by rw [hl₀a, hdm]; group)
      (by rw [hl₀d, mul_inv_cancel_right]; group) x₀ hx₀A
    rw [this]
    group
  set φ := A.normalizerMonoidHom with hφ
  set σ₀ := φ ⟨l₀, hl₀W⟩ with hσ₀
  have hσ₀app : ∀ x : A, ((σ₀ x : A) : G) = l₀ * x * l₀⁻¹ := fun x =>
    Sec4.normalizerMonoidHom_apply_coe hl₀W x
  have hσ₀T : σ₀ ∈ Sec12.transvectionGroup A ⟨d, hdA⟩ := by
    refine ⟨Subtype.ext (by rw [hσ₀app, hl₀d, mul_inv_cancel_right]), fun x => ?_⟩
    rw [Sec12.mem_zpowers_subtype_iff, Subgroup.coe_mul, hσ₀app, Subgroup.coe_inv]
    have hP : ∀ y ∈ A, l₀ * y * l₀⁻¹ * y⁻¹ ∈ Subgroup.zpowers d := by
      intro y hy
      rw [hA] at hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hz | hz | hz
        · rw [hz, hl₀c, mul_inv_cancel]
          exact Subgroup.one_mem _
        · rw [hz, hl₀a, ← hcomm _ (A.pow_mem hdA m₀) a haA, mul_inv_cancel_right]
          exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) _
        · rw [hz, hl₀d, mul_inv_cancel_right, mul_inv_cancel]
          exact Subgroup.one_mem _
      | one => simp
      | mul y z hy hz ihy ihz =>
        rw [← hA] at hy hz
        have hzc : l₀ * z * l₀⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hl₀W z).mp hz
        have e : l₀ * (y * z) * l₀⁻¹ * (y * z)⁻¹ =
            (l₀ * y * l₀⁻¹) * ((l₀ * z * l₀⁻¹) * z⁻¹) * y⁻¹ := by group
        have hc1 : (l₀ * z * l₀⁻¹) * z⁻¹ ∈ A := A.mul_mem hzc (A.inv_mem hz)
        rw [e, mul_assoc, hcomm _ hc1 _ (A.inv_mem hy), ← mul_assoc]
        exact Subgroup.mul_mem _ ihy ihz
      | inv y hy ihy =>
        rw [← hA] at hy
        have hyc : l₀ * y * l₀⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hl₀W y).mp hy
        have e : l₀ * y⁻¹ * l₀⁻¹ * y⁻¹⁻¹ = (l₀ * y * l₀⁻¹)⁻¹ * y := by group
        rw [e, hcomm _ (A.inv_mem hyc) _ hy]
        have e2 : y * (l₀ * y * l₀⁻¹)⁻¹ = (l₀ * y * l₀⁻¹ * y⁻¹)⁻¹ := by group
        rw [e2]
        exact Subgroup.inv_mem _ ihy
    exact hP x x.2
  have hσ₀1 : σ₀ ≠ 1 := by
    intro h1
    apply hx₀
    have := congrArg (fun τ : MulAut A => ((τ ⟨x₀, hx₀A⟩ : A) : G)) h1
    simpa [hσ₀app] using this
  have hpow : ∀ (n : ℕ) (x : A), ((σ₀ ^ n) x : G) = l₀ ^ n * x * (l₀ ^ n)⁻¹ := by
    intro n x
    rw [hσ₀, ← map_pow, Sec4.normalizerMonoidHom_apply_coe]
    simp
  have hl₀dm : l₀ * d ^ m₀ = d ^ m₀ * l₀ := (Commute.pow_right hl₀d m₀).eq
  have hl₀an : ∀ n : ℕ, l₀ ^ n * a * (l₀ ^ n)⁻¹ = a * d ^ (m₀ * n) := by
    intro n
    rw [KFacts.conj_pow_eq_mul_pow hl₀a hl₀dm n, ← pow_mul]
  have hl₀cn : ∀ n : ℕ, l₀ ^ n * c * (l₀ ^ n)⁻¹ = c := by
    intro n
    have hcomm' : Commute l₀ c := by
      calc l₀ * c = l₀ * c * l₀⁻¹ * l₀ := by group
        _ = c * l₀ := by rw [hl₀c]
    rw [(hcomm'.pow_left n).eq, mul_inv_cancel_right]
  have hl₀dn : ∀ n : ℕ, l₀ ^ n * d * (l₀ ^ n)⁻¹ = d := by
    intro n
    rw [((Commute.pow_left hl₀d n)).eq, mul_inv_cancel_right]
  have hσ₀3 : σ₀ ^ 3 = 1 := by
    ext x
    rw [hpow, MulAut.one_apply]
    have hdm3 : d ^ (m₀ * 3) = 1 := by rw [pow_mul, ← pow_mul, mul_comm, pow_mul, hdpow3, one_pow]
    exact hext (l₀ ^ 3) 1 (by rw [hl₀cn]; group) (by rw [hl₀an, hdm3]; group)
      (by rw [hl₀dn]; group) x x.2 |>.trans (by group)
  have hord : orderOf σ₀ = 3 := orderOf_eq_prime hσ₀3 hσ₀1
  have hd1 : (⟨d, hdA⟩ : A) ≠ 1 := by
    intro h1
    have : d = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at hd3
    norm_num at hd3
  have hc1 : (⟨c, hcA⟩ : A) ≠ 1 := fun h1 => h.ne_one (congrArg Subtype.val h1)
  have hσ₀c : σ₀ ⟨c, hcA⟩ = ⟨c, hcA⟩ := Subtype.ext (by rw [hσ₀app, hl₀c])
  refine KFacts.false_of_irreducible_of_normal_three hAe h.card_eq hirr hd1
    (Sec4.mem_autIn_iff.mpr ⟨l₀, hl₀W, hl₀W, rfl⟩) hσ₀T hσ₀1 hc1
    (N := Subgroup.zpowers σ₀) (by rw [Nat.card_zpowers, hord]) ?_ ?_
  · intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have h1 : (σ₀ ^ k) ⟨c, hcA⟩ = ⟨c, hcA⟩ :=
      MulAction.mem_fixedBy_zpow (show (⟨c, hcA⟩ : A) ∈ MulAction.fixedBy A σ₀ from hσ₀c) k
    rw [h1]
    exact Subgroup.mem_zpowers _
  · intro τ hτ hτc n hn
    obtain ⟨g, hgW, -, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
    have hgc : g * c * g⁻¹ = c := by
      have := congrArg Subtype.val hτc
      rwa [Sec4.normalizerMonoidHom_apply_coe] at this
    have hgH : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      Sec10.mem_normalizer_zpowers_of_conj_mem (by rw [hgc]; exact Subgroup.mem_zpowers c)
    have hgL := hL G A c L a R h.toHyp91 ⟨hgH, hgW⟩
    set l₁ := g * l₀ * g⁻¹ with hl₁
    have hl₁L : l₁ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hgL l₀).mp hl₀.1
    have hl₁W : l₁ ∈ Subgroup.normalizer (A : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgW hl₀W) (Subgroup.inv_mem _ hgW)
    have hl₁3 : ∃ k : ℕ, l₁ ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hl₀3
      exact ⟨k, by rw [hl₁, conj_pow, hk, mul_one, mul_inv_cancel]⟩
    obtain ⟨hl₁c, hl₁d, m₁, hl₁a⟩ := key l₁ ⟨hl₁L, hl₁W⟩ hl₁3
    have hm₁ : m₁ % 3 ≠ 0 := by
      intro h0
      apply hx₀
      have hdm : d ^ m₁ = 1 := by
        rw [← Nat.mod_add_div m₁ 3, h0, zero_add, pow_mul, hdpow3, one_pow]
      have hgx : g * x₀ * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgW x₀).mp hx₀A
      have := hext l₁ 1 (by rw [hl₁c]; group) (by rw [hl₁a, hdm]; group)
        (by rw [hl₁d, mul_inv_cancel_right]; group) _ hgx
      have e : l₀ * x₀ * l₀⁻¹ = g⁻¹ * (l₁ * (g * x₀ * g⁻¹) * l₁⁻¹) * g := by
        rw [hl₁]; group
      rw [e, this]
      group
    have hτσ : φ ⟨g, hgW⟩ * σ₀ * (φ ⟨g, hgW⟩)⁻¹ = φ ⟨l₁, hl₁W⟩ := by
      rw [hσ₀, ← map_mul, ← map_inv, ← map_mul]
      rfl
    have hmem : φ ⟨g, hgW⟩ * σ₀ * (φ ⟨g, hgW⟩)⁻¹ ∈ Subgroup.zpowers σ₀ := by
      rw [hτσ]
      by_cases hm : m₀ % 3 = m₁ % 3
      · have hdm : d ^ m₁ = d ^ (m₀ * 1) := by
          rw [mul_one, pow_eq_pow_iff_modEq, hd3]
          exact hm.symm
        have heq : φ ⟨l₁, hl₁W⟩ = σ₀ ^ 1 := by
          ext x
          rw [hpow, Sec4.normalizerMonoidHom_apply_coe]
          exact hext l₁ (l₀ ^ 1) (by rw [hl₁c, hl₀cn]) (by rw [hl₁a, hl₀an, hdm])
            (by rw [hl₁d, mul_inv_cancel_right, hl₀dn]) x x.2
        rw [heq]
        exact Subgroup.npow_mem_zpowers _ _
      · have hdm : d ^ m₁ = d ^ (m₀ * 2) := by
          rw [pow_eq_pow_iff_modEq, hd3]
          change m₁ % 3 = m₀ * 2 % 3
          omega
        have heq : φ ⟨l₁, hl₁W⟩ = σ₀ ^ 2 := by
          ext x
          rw [hpow, Sec4.normalizerMonoidHom_apply_coe]
          exact hext l₁ (l₀ ^ 2) (by rw [hl₁c, hl₀cn]) (by rw [hl₁a, hl₀an, hdm])
            (by rw [hl₁d, mul_inv_cancel_right, hl₀dn]) x x.2
        rw [heq]
        exact Subgroup.npow_mem_zpowers _ _
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hmem k

end CFSG.RankThree.PartTwo.Sec11
