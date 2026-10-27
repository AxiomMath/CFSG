module

public import CFSG.RankThree.PartTwo.Sec17.PropUStepTwoA
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec17.PropU

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS
open scoped commutatorElement

theorem pu_G1a_core {N : Type} [Group N] [Finite N] (W : Subgroup N)
    (hW : ∀ x ∈ W, ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hcent : ∀ x ∈ W, ∀ f ∈ CFSG.generalizedFitting N, f * x = x * f) :
    W ≤ CFSG.pCore 2 N := by
  have hFconj : ∀ g : N, ∀ f ∈ CFSG.generalizedFitting N,
      g * f * g⁻¹ ∈ CFSG.generalizedFitting N := by
    intro g f hf
    have h := CFSG.WholeGroup.generalizedFitting_map_mulEquiv (MulAut.conj g : N ≃* N)
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj g : N ≃* N).toMonoidHom hf
    rw [h] at hmem
    simpa [MulAut.conj_apply] using hmem
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup N, ∀ x : N, x ∈ Z ↔
      x ∈ CFSG.generalizedFitting N ∧ ∀ f ∈ CFSG.generalizedFitting N, f * x = x * f :=
    ⟨CFSG.generalizedFitting N ⊓ Subgroup.centralizer (CFSG.generalizedFitting N : Set N),
      fun x => by simp [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]⟩
  have hZN : Z.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hnF, hnc⟩ := (hZ n).1 hn
    rw [hZ]
    refine ⟨hFconj g n hnF, fun f hf => ?_⟩
    have key := hnc _ (hFconj g⁻¹ f hf)
    have e1 : f * (g * n * g⁻¹) = g * ((g⁻¹ * f * g⁻¹⁻¹) * n) * g⁻¹ := by group
    have e2 : g * n * g⁻¹ * f = g * (n * (g⁻¹ * f * g⁻¹⁻¹)) * g⁻¹ := by group
    rw [e1, e2, key]
  have hcomm : ∀ a ∈ Z, ∀ b ∈ Z, Commute a b := by
    intro a ha b hb
    exact (((hZ a).1 ha).2 b ((hZ b).1 hb).1).symm
  have hTone : (1 : N) ∈ Z ∧ ∃ k : ℕ, (1 : N) ^ 2 ^ k = 1 := ⟨Z.one_mem, 0, by simp⟩
  have hTinv : ∀ a : N, (a ∈ Z ∧ ∃ k : ℕ, a ^ 2 ^ k = 1) →
      (a⁻¹ ∈ Z ∧ ∃ k : ℕ, a⁻¹ ^ 2 ^ k = 1) := by
    rintro a ⟨haZ, k, hk⟩
    exact ⟨Z.inv_mem haZ, k, by rw [inv_pow, hk, inv_one]⟩
  have hTmul : ∀ a b : N, (a ∈ Z ∧ ∃ k : ℕ, a ^ 2 ^ k = 1) →
      (b ∈ Z ∧ ∃ l : ℕ, b ^ 2 ^ l = 1) → (a * b ∈ Z ∧ ∃ k : ℕ, (a * b) ^ 2 ^ k = 1) := by
    rintro a b ⟨haZ, k, hk⟩ ⟨hbZ, l, hl⟩
    refine ⟨Z.mul_mem haZ hbZ, k + l, ?_⟩
    have hA : a ^ 2 ^ (k + l) = 1 := by
      rw [show (2 : ℕ) ^ (k + l) = 2 ^ k * 2 ^ l from pow_add 2 k l, pow_mul, hk, one_pow]
    have hB : b ^ 2 ^ (k + l) = 1 := by
      rw [show (2 : ℕ) ^ (k + l) = 2 ^ l * 2 ^ k by rw [pow_add, mul_comm], pow_mul, hl, one_pow]
    rw [(hcomm a haZ b hbZ).mul_pow, hA, hB, one_mul]
  obtain ⟨T, hT⟩ : ∃ T : Subgroup N, ∀ x : N, x ∈ T ↔ (x ∈ Z ∧ ∃ k : ℕ, x ^ 2 ^ k = 1) :=
    ⟨{ carrier := {x | x ∈ Z ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
       mul_mem' := fun {a b} ha hb => hTmul a b ha hb
       one_mem' := hTone
       inv_mem' := fun {x} hx => hTinv x hx }, fun x => Iff.rfl⟩
  have hTN : T.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hnZ, k, hk⟩ := (hT n).1 hn
    rw [hT]
    exact ⟨hZN.conj_mem n hnZ g, k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  have hTp : IsPGroup 2 T := by
    show ∀ g : T, ∃ k : ℕ, g ^ 2 ^ k = 1
    intro g
    obtain ⟨_, k, hk⟩ := (hT (g : N)).1 g.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hTcore : T ≤ CFSG.pCore 2 N := by
    unfold CFSG.pCore
    exact le_sSup (show T ∈ {K : Subgroup N | K.Normal ∧ IsPGroup 2 K} from ⟨hTN, hTp⟩)
  have hWT : W ≤ T := by
    intro x hx
    obtain ⟨k, hk⟩ := hW x hx
    refine (hT x).2 ⟨?_, k, hk⟩
    have hxc : x ∈ Subgroup.centralizer (CFSG.generalizedFitting N : Set N) := by
      rw [Subgroup.mem_centralizer_iff]
      exact fun f hf => hcent x hx f hf
    exact (hZ x).2 ⟨CFSG.centralizer_generalizedFitting_le N hxc, fun f hf => hcent x hx f hf⟩
  exact hWT.trans hTcore

theorem eq_bot_of_two_group_centralizes_fstar {G : Type} [Group G] [Finite G] {N₀ V : Subgroup G}
    (hV : IsPGroup 2 V) (hVN : V ≤ N₀) (hO2 : CFSG.Open.pCoreOf 2 N₀ = ⊥)
    (hc : V ≤ Subgroup.centralizer ((inSubgroup CFSG.generalizedFitting N₀ : Subgroup G) : Set G)) :
    V = ⊥ := by
  have hW : ∀ x ∈ V.subgroupOf N₀, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hV ⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hcent : ∀ x ∈ V.subgroupOf N₀, ∀ f ∈ CFSG.generalizedFitting ↥N₀, f * x = x * f := by
    intro x hx f hf
    have hxV : (x : G) ∈ V := Subgroup.mem_subgroupOf.1 hx
    have hfG : (f : G) ∈ (inSubgroup CFSG.generalizedFitting N₀ : Subgroup G) :=
      Subgroup.mem_map_of_mem N₀.subtype hf
    have h1 : (f : G) * (x : G) = (x : G) * (f : G) :=
      (Subgroup.mem_centralizer_iff.1 (hc hxV)) _ hfG
    exact Subtype.ext h1
  have hcore := pu_G1a_core (V.subgroupOf N₀) hW hcent
  have hVcore : V ≤ CFSG.Open.pCoreOf 2 N₀ := by
    intro v hv
    have hx : (⟨v, hVN hv⟩ : ↥N₀) ∈ V.subgroupOf N₀ := Subgroup.mem_subgroupOf.2 hv
    show v ∈ (CFSG.pCore 2 ↥N₀).map N₀.subtype
    exact Subgroup.mem_map.2 ⟨⟨v, hVN hv⟩, hcore hx, rfl⟩
  rw [hO2] at hVcore
  exact le_bot_iff.1 hVcore

theorem pu_comm_left {G : Type*} [Group G] (x y z : G) (h : z * y = y * z) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have hc : z * y * z⁻¹ = y := by rw [h, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc x * z * y * (z⁻¹ * x⁻¹) * y⁻¹ = x * (z * y * z⁻¹) * x⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [hc]

theorem pu_comm_right {G : Type*} [Group G] (x y z : G) (h : z * x = x * z) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have hc : z * x⁻¹ = x⁻¹ * z := by
    calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
      _ = x⁻¹ * (z * x) * x⁻¹ := by rw [h]
      _ = x⁻¹ * z := by group
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc x * (y * z) * x⁻¹ * (z⁻¹ * y⁻¹) = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [hc]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem sup_eq_top_of_card_eq {F : Type*} [Group F] [Finite F] (N X : Subgroup F) [N.Normal]
    (hXN : X ⊓ N = ⊥) (hcard : Nat.card X = Nat.card (F ⧸ N)) : X ⊔ N = ⊤ := by
  let f : X →* F ⧸ N := (QuotientGroup.mk' N).comp X.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : ((x : F) : F ⧸ N) = 1 := hx
    have hxN : (x : F) ∈ N := (QuotientGroup.eq_one_iff (x : F)).mp hx'
    have hmem : (x : F) ∈ X ⊓ N := Subgroup.mem_inf.mpr ⟨x.2, hxN⟩
    rw [hXN, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (le_of_eq hcard.symm)
  have htop : ∀ g : F, g ∈ X ⊔ N := by
    intro g
    obtain ⟨x, hx⟩ := hbij.2 (QuotientGroup.mk g : F ⧸ N)
    have hx' : (QuotientGroup.mk (x : F) : F ⧸ N) = QuotientGroup.mk g := hx
    have h1 : (x : F)⁻¹ * g ∈ N := QuotientGroup.eq.mp hx'
    have h2 : (x : F) * ((x : F)⁻¹ * g) ∈ X ⊔ N := Subgroup.mul_mem_sup x.2 h1
    rwa [mul_inv_cancel_left] at h2
  exact (Subgroup.eq_top_iff' _).mpr htop

theorem commutator_eq_of_central_sup {G : Type*} [Group G] {C X Z : Subgroup G} (hXC : X ≤ C)
    (hZC : Z ≤ C) (hsup : X ⊔ Z = C) (hcent : ∀ z ∈ Z, ∀ c ∈ C, z * c = c * z)
    (hperf : ⁅X, X⁆ = X) : ⁅C, C⁆ = X := by
  obtain ⟨T, hT⟩ : ∃ T : Subgroup G, ∀ c : G, c ∈ T ↔ ∃ x ∈ X, ∃ z ∈ Z, c = x * z := by
    refine ⟨{ carrier := {c | ∃ x ∈ X, ∃ z ∈ Z, c = x * z}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun c => Iff.rfl⟩
    · rintro _ _ ⟨x₁, hx₁, z₁, hz₁, rfl⟩ ⟨x₂, hx₂, z₂, hz₂, rfl⟩
      refine ⟨x₁ * x₂, X.mul_mem hx₁ hx₂, z₁ * z₂, Z.mul_mem hz₁ hz₂, ?_⟩
      have h12 : z₁ * x₂ = x₂ * z₁ := hcent z₁ hz₁ x₂ (hXC hx₂)
      calc x₁ * z₁ * (x₂ * z₂) = x₁ * (z₁ * x₂) * z₂ := by simp only [mul_assoc]
        _ = x₁ * (x₂ * z₁) * z₂ := by rw [h12]
        _ = x₁ * x₂ * (z₁ * z₂) := by simp only [mul_assoc]
    · exact ⟨1, X.one_mem, 1, Z.one_mem, by simp⟩
    · rintro _ ⟨x, hx, z, hz, rfl⟩
      refine ⟨x⁻¹, X.inv_mem hx, z⁻¹, Z.inv_mem hz, ?_⟩
      have h : z * x = x * z := hcent z hz x (hXC hx)
      rw [← h, mul_inv_rev]
  have hXT : X ≤ T := fun x hx => (hT x).mpr ⟨x, hx, 1, Z.one_mem, (mul_one x).symm⟩
  have hZT : Z ≤ T := fun z hz => (hT z).mpr ⟨1, X.one_mem, z, hz, (one_mul z).symm⟩
  have hCT : C ≤ T := by
    rw [← hsup]
    exact sup_le hXT hZT
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨x₁, hx₁, z₁, hz₁, rfl⟩ := (hT g₁).mp (hCT hg₁)
    obtain ⟨x₂, hx₂, z₂, hz₂, rfl⟩ := (hT g₂).mp (hCT hg₂)
    have h12 : z₁ * x₂ = x₂ * z₁ := hcent z₁ hz₁ x₂ (hXC hx₂)
    have h1z2 : z₁ * z₂ = z₂ * z₁ := hcent z₁ hz₁ z₂ (hZC hz₂)
    have h2x1 : z₂ * x₁ = x₁ * z₂ := hcent z₂ hz₂ x₁ (hXC hx₁)
    have hy : z₁ * (x₂ * z₂) = x₂ * z₂ * z₁ := by
      rw [← mul_assoc, h12, mul_assoc x₂ z₁ z₂, h1z2, ← mul_assoc]
    rw [pu_comm_left x₁ (x₂ * z₂) z₁ hy, pu_comm_right x₁ x₂ z₂ h2x1]
    have hmem : ⁅x₁, x₂⁆ ∈ ⁅X, X⁆ := Subgroup.commutator_mem_commutator hx₁ hx₂
    rw [hperf] at hmem
    exact hmem
  · have h1 : ⁅X, X⁆ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hXC hXC
    rw [hperf] at h1
    exact h1

theorem pu_conj_mem_fstar {G : Type} [Group G] (N₀ : Subgroup G) {k : G}
    (hk : k ∈ Subgroup.normalizer (N₀ : Set G)) (z : G)
    (hz : z ∈ inSubgroup CFSG.generalizedFitting N₀) :
    k * z * k⁻¹ ∈ inSubgroup CFSG.generalizedFitting N₀ := by
  unfold inSubgroup at hz ⊢
  let e : ↥N₀ ≃* ↥N₀ := N₀.normalizerMonoidHom ⟨k, hk⟩
  have hα : ∀ x : ↥N₀, ((e x : ↥N₀) : G) = k * (x : G) * k⁻¹ := fun x => rfl
  have hF : (CFSG.generalizedFitting ↥N₀).map e.toMonoidHom = CFSG.generalizedFitting ↥N₀ :=
    CFSG.WholeGroup.generalizedFitting_map_mulEquiv e
  obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.1 hz
  have hmem : e z₀ ∈ CFSG.generalizedFitting ↥N₀ := by
    rw [← hF]
    exact Subgroup.mem_map.2 ⟨z₀, hz₀, rfl⟩
  exact Subgroup.mem_map.2 ⟨e z₀, hmem, hα z₀⟩

theorem le_normalizer_fstar {G : Type} [Group G] [Finite G] {K F : Subgroup G}
    (hKF : K ≤ Subgroup.normalizer (F : Set G)) :
    K ≤ Subgroup.normalizer
      ((inSubgroup CFSG.generalizedFitting (pPrimeCoreOf 3 F) : Subgroup G) : Set G) := by
  have hKN : K ≤ Subgroup.normalizer ((pPrimeCoreOf 3 F : Subgroup G) : Set G) :=
    hKF.trans (CFSG.RankThree.PartTwo.Sec14.normalizer_le_normalizer_pPrimeCoreOf 3 F)
  intro k hk
  refine Subgroup.mem_set_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · exact pu_conj_mem_fstar (pPrimeCoreOf 3 F) (hKN hk) h hh
  · have h' := pu_conj_mem_fstar (pPrimeCoreOf 3 F) (hKN (inv_mem hk)) (k * h * k⁻¹) hh
    have e : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
    rw [e] at h'
    exact h'

theorem isPerfect_J2 : Group.IsPerfect J2 := by
  haveI : IsSimpleGroup J2 := Sporadic.J2.isSimpleGroup_J2
  have hncomm : ¬ IsMulCommutative J2 := by
    intro h
    have hp := IsSimpleGroup.prime_card (α := J2)
    rw [CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2] at hp
    exact absurd hp (by norm_num)
  exact CFSG.OrderReductions.Helpers.simple_noncommutative_isPerfect J2 hncomm

theorem le_normalizer_commutator_self {G : Type*} [Group G] {K C : Subgroup G}
    (hC : K ≤ Subgroup.normalizer (C : Set G)) :
    K ≤ Subgroup.normalizer ((⁅C, C⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hC hh)]

theorem le_normalizer_centralizer_of {G : Type*} [Group G] {K S : Subgroup G}
    (hS : K ≤ Subgroup.normalizer (S : Set G)) :
    K ≤ Subgroup.normalizer ((Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
  have key : ∀ k ∈ K, ∀ g ∈ Subgroup.centralizer (S : Set G),
      k * g * k⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro k hk g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro s hs
    have hs' : k⁻¹ * s * k ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (hS (inv_mem hk)) s).mp hs
      simpa using this
    have h := hg _ hs'
    calc s * (k * g * k⁻¹) = k * ((k⁻¹ * s * k) * g) * k⁻¹ := by group
      _ = k * (g * (k⁻¹ * s * k)) * k⁻¹ := by rw [h]
      _ = k * g * k⁻¹ * s := by group
  intro k hk
  refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨key k hk g, fun h => ?_⟩
  have := key k⁻¹ (inv_mem hk) _ h
  simpa [mul_assoc] using this

theorem pu_le_normalizer_inf {G : Type*} [Group G] {K X Y : Subgroup G}
    (hX : K ≤ Subgroup.normalizer (X : Set G)) (hY : K ≤ Subgroup.normalizer (Y : Set G)) :
    K ≤ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hX ha) h,
    Subgroup.mem_normalizer_iff.mp (hY ha) h]

theorem step3 {G : Type} [Group G] [Finite G] {K F X : Subgroup G}
    (hKF : K ≤ Subgroup.normalizer (F : Set G))
    (hFcard : Nat.card (↥F ⧸ CFSG.pPrimeCore 3 ↥F) = 604800) (hXF : X ≤ F)
    (hXJ : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* J2))
    (hXN : X ⊓ pPrimeCoreOf 3 F = CFSG.Open.pCoreOf 2 X)
    (hO2 : CFSG.Open.pCoreOf 2 (pPrimeCoreOf 3 F) = ⊥)
    (hcent : X ≤ Subgroup.centralizer
      ((inSubgroup CFSG.generalizedFitting (pPrimeCoreOf 3 F) : Subgroup G) : Set G)) :
    CFSG.Open.pCoreOf 2 X = ⊥ ∧ K ≤ Subgroup.normalizer (X : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₀ := pPrimeCoreOf 3 F with hN₀
  set Fs : Subgroup G := inSubgroup CFSG.generalizedFitting N₀ with hFs
  obtain ⟨eX⟩ := hXJ
  have hV : CFSG.Open.pCoreOf 2 X = ⊥ := by
    refine eq_bot_of_two_group_centralizes_fstar (N₀ := N₀) (V := CFSG.Open.pCoreOf 2 X) ?_ ?_
      hO2 ?_
    · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
    · rw [← hXN]; exact inf_le_right
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hcent
  refine ⟨hV, ?_⟩
  have hXN1 : X ⊓ N₀ = ⊥ := by rw [hXN, hV]
  have hpC : CFSG.pCore 2 ↥X = ⊥ := by
    have h : (CFSG.pCore 2 ↥X).map X.subtype = ⊥ := hV
    rw [Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at h
    exact le_bot_iff.mp h
  have hcardX : Nat.card ↥X = 604800 := by
    have h1 : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = 604800 :=
      (Nat.card_congr eX.toEquiv).trans CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X)
    rw [hpC, Subgroup.card_bot, mul_one] at h2
    rw [h2]
    rw [← hpC]
    exact h1
  have hcardF : Nat.card (↥F ⧸ CFSG.pPrimeCore 3 ↥F) = 604800 := hFcard
  set N' := CFSG.pPrimeCore 3 ↥F with hN'
  have hN'map : N'.map F.subtype = N₀ := rfl
  set X' : Subgroup ↥F := X.subgroupOf F with hX'
  have hX'N' : X' ⊓ N' = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgX, hgN⟩ := Subgroup.mem_inf.mp hg
    have h1 : (g : G) ∈ X := hgX
    have h2 : (g : G) ∈ N₀ := by rw [← hN'map]; exact Subgroup.mem_map_of_mem _ hgN
    have h3 : (g : G) ∈ X ⊓ N₀ := ⟨h1, h2⟩
    rw [hXN1, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.mpr (Subtype.ext h3)
  have hcardX' : Nat.card X' = Nat.card (↥F ⧸ N') := by
    rw [hcardF]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXF).toEquiv).trans hcardX
  have hsupF : X' ⊔ N' = ⊤ := sup_eq_top_of_card_eq N' X' hX'N' hcardX'
  set C : Subgroup G := F ⊓ Subgroup.centralizer (Fs : Set G) with hC
  set Z : Subgroup G := C ⊓ N₀ with hZ
  have hXC : X ≤ C := le_inf hXF hcent
  have hsup : X ⊔ Z = C := by
    refine le_antisymm (sup_le hXC inf_le_left) ?_
    intro c hc
    have hcF : c ∈ F := hc.1
    have hmem : (⟨c, hcF⟩ : ↥F) ∈ X' ⊔ N' := by rw [hsupF]; exact Subgroup.mem_top _
    obtain ⟨x', hx', n', hn', hxn⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    have hxX : (x' : G) ∈ X := hx'
    have hnN : (n' : G) ∈ N₀ := by rw [← hN'map]; exact Subgroup.mem_map_of_mem _ hn'
    have hcxn : c = (x' : G) * (n' : G) := by
      have := congrArg Subtype.val hxn
      simpa using this.symm
    have hn_def : (n' : G) = (x' : G)⁻¹ * c := by rw [hcxn]; group
    have hnC : (n' : G) ∈ C := by
      rw [hn_def]
      exact C.mul_mem (C.inv_mem (hXC hxX)) hc
    have hnZ : (n' : G) ∈ Z := ⟨hnC, hnN⟩
    rw [hcxn]
    exact Subgroup.mul_mem_sup hxX hnZ
  have hZcent : ∀ z ∈ Z, ∀ c ∈ C, z * c = c * z := by
    intro z hz c hc
    have hzN : z ∈ N₀ := hz.2
    have hzFs : z ∈ Fs := by
      have h1 : (⟨z, hzN⟩ : ↥N₀) ∈
          Subgroup.centralizer ((CFSG.generalizedFitting ↥N₀ : Subgroup ↥N₀) : Set ↥N₀) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        apply Subtype.ext
        have hwFs : (w : G) ∈ Fs := Subgroup.mem_map_of_mem N₀.subtype hw
        exact Subgroup.mem_centralizer_iff.mp hz.1.2 _ hwFs
      have h2 := CFSG.centralizer_generalizedFitting_le ↥N₀ h1
      exact Subgroup.mem_map_of_mem N₀.subtype h2
    exact Subgroup.mem_centralizer_iff.mp hc.2 z hzFs
  have hXperf : ⁅X, X⁆ = X := by
    haveI := isPerfect_J2
    let eX'' : ↥X ≃* J2 :=
      ((QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hpC.symm)).trans eX
    haveI : Group.IsPerfect ↥X :=
      Group.IsPerfect.ofSurjective (G := J2) (f := eX''.symm.toMonoidHom) eX''.symm.surjective
    exact Subgroup.isPerfect_iff.mp inferInstance
  have hCC : ⁅C, C⁆ = X := commutator_eq_of_central_sup hXC inf_le_left hsup hZcent hXperf
  have hKC : K ≤ Subgroup.normalizer (C : Set G) :=
    pu_le_normalizer_inf hKF (le_normalizer_centralizer_of (le_normalizer_fstar hKF))
  rw [← hCC]
  exact le_normalizer_commutator_self hKC

end CFSG.RankThree.PartTwo.Sec17.PropU
