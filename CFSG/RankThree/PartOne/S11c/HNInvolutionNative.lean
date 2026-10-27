module

public import CFSG.RankThree.PartOne.S11c.HNPrescribedBlock
public import CFSG.RankThree.PartOne.HNB.Native
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.NativeSporadic (Carrier IsSporadic)
open CFSG.RankThree.PartOne.HNB (NativeData HNNativeFive)
open scoped commutatorElement

@[expose] def IsNativeWitness {M : Type} [Group M] (f t : M) (K Y : Subgroup M) : Prop :=
  orderOf f = 5 ∧ K ≤ Subgroup.centralizer ({f} : Set M) ∧
    (K.subgroupOf (Subgroup.centralizer ({f} : Set M))).Normal ∧
    Subgroup.zpowers f ⊓ K = ⊥ ∧ IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧
    StatedClassicalModel K .PSU 3 5 1 ∧ Y ≤ K ∧
    Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
    t ∈ Y ∧ orderOf t = 2 ∧ ∀ y ∈ Y, y * t = t * y

@[expose] def HNFiveCoverage : Prop :=
  ∀ (f t : Carrier .HN) (K Y : Subgroup (Carrier .HN)), IsNativeWitness f t K Y →
    Subgroup.centralizer ({f} : Set (Carrier .HN)) ≤ Subgroup.zpowers f ⊔ K ∧
    ∀ w : Carrier .HN, orderOf w = 5 →
      (∃ K' : Subgroup (Carrier .HN), K' ≤ Subgroup.centralizer ({w} : Set (Carrier .HN)) ∧
        StatedClassicalModel K' .PSU 3 5 1) →
      ∃ (g : Carrier .HN) (a : ℕ), w = g * f ^ a * g⁻¹

@[expose] def HNNativeInvolution : Prop :=
  ∀ (f t : Carrier .HN) (K Y : Subgroup (Carrier .HN)), IsNativeWitness f t K Y →
    ∃ q : ↥(Subgroup.centralizer ({t} : Set (Carrier .HN))) →* MulAut (Carrier .HS),
      ∀ x : ↥(Subgroup.centralizer ({t} : Set (Carrier .HN))), q x = 1 →
        (x : Carrier .HN) = 1 ∨ (x : Carrier .HN) = t

section Group

variable {G : Type*} [Group G]

theorem perfect_le_of_le_zpowers_sup (f : G) (K₀ P : Subgroup G)
    (hK₀ : ∀ k ∈ K₀, f * k = k * f) (hP : P ≤ zpowers f ⊔ K₀) (hperf : Group.IsPerfect P) :
    P ≤ K₀ := by
  have hfz : ∀ (k : G), k ∈ K₀ → ∀ i : ℤ, f ^ i * k = k * f ^ i := fun k hk i =>
    (Commute.zpow_left (show Commute f k from hK₀ k hk) i).eq
  have hform : ∀ x ∈ zpowers f ⊔ K₀, ∃ (i : ℤ) (k : G), k ∈ K₀ ∧ x = f ^ i * k := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        exact ⟨i, 1, K₀.one_mem, by simp⟩
      · exact ⟨0, x, hx, by simp⟩
    | one => exact ⟨0, 1, K₀.one_mem, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, k, hk, rfl⟩ := hx
      obtain ⟨j, k', hk', rfl⟩ := hy
      refine ⟨i + j, k * k', K₀.mul_mem hk hk', ?_⟩
      calc f ^ i * k * (f ^ j * k') = f ^ i * (k * f ^ j) * k' := by group
        _ = f ^ i * (f ^ j * k) * k' := by rw [hfz k hk j]
        _ = f ^ (i + j) * (k * k') := by rw [zpow_add]; group
    | inv x _ hx =>
      obtain ⟨i, k, hk, rfl⟩ := hx
      refine ⟨-i, k⁻¹, K₀.inv_mem hk, ?_⟩
      calc (f ^ i * k)⁻¹ = k⁻¹ * f ^ (-i) := by group
        _ = f ^ (-i) * k⁻¹ := by
          have := hfz k⁻¹ (K₀.inv_mem hk) (-i)
          exact this.symm
  have hcomm : ∀ p₁ ∈ P, ∀ p₂ ∈ P, ⁅p₁, p₂⁆ ∈ K₀ := by
    intro p₁ h₁ p₂ h₂
    obtain ⟨i, k, hk, rfl⟩ := hform p₁ (hP h₁)
    obtain ⟨j, k', hk', rfl⟩ := hform p₂ (hP h₂)
    have hz : ⁅k, k'⁆ ∈ K₀ := by
      rw [commutatorElement_def]
      exact K₀.mul_mem (K₀.mul_mem (K₀.mul_mem hk hk') (K₀.inv_mem hk)) (K₀.inv_mem hk')
    have h1 : f ^ i * k * (f ^ j * k') = f ^ (i + j) * (k * k') := by
      calc f ^ i * k * (f ^ j * k') = f ^ i * (k * f ^ j) * k' := by group
        _ = f ^ i * (f ^ j * k) * k' := by rw [hfz k hk j]
        _ = f ^ (i + j) * (k * k') := by rw [zpow_add]; group
    have h2 : f ^ j * k' * (f ^ i * k) = f ^ (i + j) * (k' * k) := by
      calc f ^ j * k' * (f ^ i * k) = f ^ j * (k' * f ^ i) * k := by group
        _ = f ^ j * (f ^ i * k') * k := by rw [hfz k' hk' i]
        _ = f ^ (i + j) * (k' * k) := by rw [add_comm, zpow_add]; group
    have hxy : ⁅f ^ i * k, f ^ j * k'⁆ =
        (f ^ i * k * (f ^ j * k')) * (f ^ j * k' * (f ^ i * k))⁻¹ := by
      rw [commutatorElement_def]
      group
    have hc : f ^ (i + j) * ⁅k, k'⁆ = ⁅k, k'⁆ * f ^ (i + j) := hfz _ hz (i + j)
    have e : ⁅f ^ i * k, f ^ j * k'⁆ = ⁅k, k'⁆ := by
      rw [hxy, h1, h2]
      calc f ^ (i + j) * (k * k') * (f ^ (i + j) * (k' * k))⁻¹ =
            f ^ (i + j) * (k * k' * (k' * k)⁻¹) * (f ^ (i + j))⁻¹ := by group
        _ = f ^ (i + j) * ⁅k, k'⁆ * (f ^ (i + j))⁻¹ := by rw [commutatorElement_def]; group
        _ = ⁅k, k'⁆ := by rw [hc]; group
    rw [e]
    exact hz
  intro p hp
  have hperf' : commutator P = ⊤ := Group.isPerfect_def.1 hperf
  have hle : commutator P ≤ K₀.comap P.subtype := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    exact hcomm a a.2 b b.2
  have hp' : (⟨p, hp⟩ : P) ∈ commutator P := by rw [hperf']; trivial
  exact hle hp'

end Group

section Abstract

variable {J Q T : Type} [Group J] [Group Q] [Group T]

theorem transport_of_native_abstract (f t₀ : J) (K₀ : Subgroup J) (hf5 : orderOf f = 5)
    (hK₀f : K₀ ≤ Subgroup.centralizer ({f} : Set J))
    (hK₀mod : StatedClassicalModel K₀ .PSU 3 5 1) (ht₀K₀ : t₀ ∈ K₀) (ht₀2 : orderOf t₀ = 2)
    (hcen : Subgroup.centralizer ({f} : Set J) ≤ Subgroup.zpowers f ⊔ K₀)
    (hcov : ∀ w : J, orderOf w = 5 →
      (∃ K' : Subgroup J, K' ≤ Subgroup.centralizer ({w} : Set J) ∧
        StatedClassicalModel K' .PSU 3 5 1) → ∃ (g : J) (a : ℕ), w = g * f ^ a * g⁻¹)
    (q₀ : ↥(Subgroup.centralizer ({t₀} : Set J)) →* Q)
    (hq₀ : ∀ x : ↥(Subgroup.centralizer ({t₀} : Set J)), q₀ x = 1 →
      (x : J) = 1 ∨ (x : J) = t₀)
    (e : T ≃* J) (w : T) (hw5 : orderOf w = 5) (K : Subgroup T)
    (hwK : ∀ k ∈ K, w * k * w⁻¹ = k) (hKmod : StatedClassicalModel K .PSU 3 5 1)
    (t' : T) (ht'K : t' ∈ K) (ht'2 : orderOf t' = 2) :
    ∃ q : ↥(Subgroup.centralizer ({t'} : Set T)) →* Q,
      ∀ x : ↥(Subgroup.centralizer ({t'} : Set T)), q x = 1 → (x : T) = 1 ∨ (x : T) = t' := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let w' : J := e w
  have hw'5 : orderOf w' = 5 := by rw [MulEquiv.orderOf_eq]; exact hw5
  let K' : Subgroup J := K.map e.toMonoidHom
  let eK : ↥K ≃* ↥K' := K.equivMapOfInjective e.toMonoidHom e.injective
  have hK'mod : StatedClassicalModel K' .PSU 3 5 1 :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv eK.symm hKmod
  have hK'c : K' ≤ Subgroup.centralizer ({w'} : Set J) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hwk : w * k = k * w := mul_inv_eq_iff_eq_mul.1 (hwK k hk)
    show e k * e w = e w * e k
    rw [← map_mul, ← map_mul, ← hwk]
  obtain ⟨g, a, hga⟩ := hcov w' hw'5 ⟨K', hK'c, hK'mod⟩
  have hf5' : f ^ 5 = 1 := by rw [← hf5]; exact pow_orderOf_eq_one f
  have ha5 : ¬ 5 ∣ a := by
    rintro ⟨m, rfl⟩
    have h1 : w' = 1 := by
      rw [hga, pow_mul, hf5', one_pow]
      group
    rw [h1, orderOf_one] at hw'5
    omega
  let ψ : T →* J := (MulAut.conj g⁻¹).toMonoidHom.comp e.toMonoidHom
  have hψ : Function.Injective ψ := (MulAut.conj g⁻¹).injective.comp e.injective
  have hψapp : ∀ x : T, ψ x = g⁻¹ * e x * g := fun x => by
    simp [ψ]
  let K'' : Subgroup J := K.map ψ
  let eK'' : ↥K ≃* ↥K'' := K.equivMapOfInjective ψ hψ
  have hperfK : Group.IsPerfect ↥K :=
    (CFSG.RankThree.Classical.unitary_three_five_model K hKmod).2.1
  have hK''perf : Group.IsPerfect ↥K'' :=
    Group.IsPerfect.ofSurjective (f := eK''.toMonoidHom) eK''.surjective
  obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 ha5).symm (by norm_num : 1 < 5)
  have hfb : f = (f ^ a) ^ b := by rw [← pow_mul, pow_eq_pow_mod _ hf5', hb, pow_one]
  have hK''f : K'' ≤ Subgroup.centralizer ({f} : Set J) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : e k * w' = w' * e k := Subgroup.mem_centralizer_singleton_iff.1 (hK'c ⟨k, hk, rfl⟩)
    have h2 : (g⁻¹ * e k * g) * f ^ a = f ^ a * (g⁻¹ * e k * g) := by
      have h3 : g⁻¹ * (e k * w') * g = g⁻¹ * (w' * e k) * g := by rw [h1]
      rw [hga] at h3
      calc (g⁻¹ * e k * g) * f ^ a = g⁻¹ * (e k * (g * f ^ a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * f ^ a * g⁻¹) * e k) * g := h3
        _ = f ^ a * (g⁻¹ * e k * g) := by group
    have h4 := (Commute.pow_right (show Commute (g⁻¹ * e k * g) (f ^ a) from h2) b).eq
    rw [← hfb] at h4
    show ψ k * f = f * ψ k
    rw [hψapp]
    exact h4
  have hK''le : K'' ≤ K₀ :=
    perfect_le_of_le_zpowers_sup f K₀ K'' (fun k hk =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hK₀f hk)).symm) (hK''f.trans hcen) hK''perf
  have hcard₀ := (CFSG.RankThree.Classical.unitary_three_five_model K₀ hK₀mod).1
  have hcardK := (CFSG.RankThree.Classical.unitary_three_five_model K hKmod).1
  have : Finite ↥K₀ := Nat.finite_of_card_ne_zero (by rw [hcard₀]; norm_num)
  have hK''eq : K'' = K₀ := by
    refine Subgroup.eq_of_le_of_card_ge hK''le ?_
    rw [hcard₀, Nat.card_congr eK''.toEquiv.symm, hcardK]
  have ht''K : ψ t' ∈ K₀ := hK''le ⟨t', ht'K, rfl⟩
  have ht''2 : orderOf (ψ t') = 2 := by rw [orderOf_injective ψ hψ t']; exact ht'2
  have hconj := (CFSG.RankThree.Classical.unitary_three_five_model K₀ hK₀mod).2.2.2
    ⟨t₀, ht₀K₀⟩ ⟨ψ t', ht''K⟩ (by rw [Subgroup.orderOf_mk]; exact ht₀2)
    (by rw [Subgroup.orderOf_mk]; exact ht''2)
  obtain ⟨u, hu⟩ := isConj_iff.1 hconj
  have hu' : (u : J) * t₀ * (u : J)⁻¹ = ψ t' := congrArg Subtype.val hu
  set c : J := g * (u : J) with hc
  have hct : e t' = c * t₀ * c⁻¹ := by
    have h1 : e t' = g * ψ t' * g⁻¹ := by rw [hψapp]; group
    rw [h1, ← hu', hc]
    group
  let φ : ↥(Subgroup.centralizer ({t'} : Set T)) →* ↥(Subgroup.centralizer ({t₀} : Set J)) :=
    { toFun := fun x => ⟨c⁻¹ * e x * c, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 : (x : T) * t' = t' * x := Subgroup.mem_centralizer_singleton_iff.1 x.2
        have h2 : e x * e t' = e t' * e x := by rw [← map_mul, ← map_mul, h1]
        rw [hct] at h2
        calc c⁻¹ * e x * c * t₀ = c⁻¹ * (e x * (c * t₀ * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * t₀ * c⁻¹) * e x) * c := by rw [h2]
          _ = t₀ * (c⁻¹ * e x * c) := by group⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        simp only [Subgroup.coe_mul, map_mul]
        group) }
  refine ⟨q₀.comp φ, fun x hx => ?_⟩
  rcases hq₀ (φ x) hx with h | h
  · left
    have h1 : c⁻¹ * e x * c = 1 := h
    have h2 : e x = 1 := by
      calc e x = c * (c⁻¹ * e x * c) * c⁻¹ := by group
        _ = 1 := by rw [h1]; group
    exact e.injective (by rw [h2, map_one])
  · right
    have h1 : c⁻¹ * e x * c = t₀ := h
    apply e.injective
    rw [hct, ← h1]
    group

end Abstract

section Main

theorem hnInvolutionTransport_of_native
    (hN : HNNativeFive) (hC : HNFiveCoverage) (hI : HNNativeInvolution) :
    HNInvolutionTransport := by
  classical
  obtain ⟨-, -, f, t₀, K₀, Y₀, hw⟩ := hN
  obtain ⟨hcen, hcov⟩ := hC f t₀ K₀ Y₀ hw
  obtain ⟨q₀, hq₀⟩ := hI f t₀ K₀ Y₀ hw
  obtain ⟨hf5, hK₀f, -, -, -, -, hK₀mod, hY₀K₀, -, ht₀Y, ht₀2, -⟩ := hw
  intro T _ _ hsimple hnab hHN β hβ K hKfix hKmod t' ht'K ht'2
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : IsSimpleGroup T := hsimple
  obtain ⟨e⟩ := hHN
  have hOut : ¬ 5 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) := by
    have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Carrier .HN)) = 2 :=
      CFSG.Sporadic.HNSchreier.card_outer_HN
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv,
      h2]
    norm_num
  obtain ⟨w, hwβ⟩ := CFSG.RankThree.PartOne.exists_inner_of_pow_eq_one_of_not_dvd_card_outer
    Nat.prime_five hOut β (by rw [← hβ]; exact pow_orderOf_eq_one β)
  have hcenT : Subgroup.center T = ⊥ := CFSG.RankThree.PartOne.center_eq_bot_of_simple hnab
  have hinj := CFSG.RankThree.PartOne.conj_injective_of_center_eq_bot hcenT
  have hw5 : orderOf w = 5 := by
    have h1 := orderOf_injective _ hinj w
    rw [hwβ] at h1
    rw [← h1]
    exact hβ
  have hwK : ∀ k ∈ K, w * k * w⁻¹ = k := fun k hk => by
    have h1 := hKfix k hk
    rw [← hwβ, MulAut.conj_apply] at h1
    exact h1
  exact transport_of_native_abstract f t₀ K₀ hf5 hK₀f hK₀mod (hY₀K₀ ht₀Y) ht₀2 hcen hcov q₀ hq₀
    e w hw5 K hwK hKmod t' ht'K ht'2

theorem hnPrescribedBlockNormalizedTwo_of_native
    (hN : HNNativeFive) (hC : HNFiveCoverage) (hI : HNNativeInvolution) :
    HNPrescribedBlockNormalizedTwo :=
  hnPrescribedBlockNormalizedTwo_of_transport (hnInvolutionTransport_of_native hN hC hI)

end Main

end CFSG.RankThree.PartOne.HNRed
