module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveOut
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp4Out
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Act

public section

namespace CFSG.Quasithin.Sp4

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

variable {K : Type} [Field K] [Finite K]

theorem finite_ringEquiv_sp4 : Finite (K ≃+* K) :=
  Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective

omit [Finite K] in
theorem fixed_of_mem_zpowers_sp4 {σ τ : K ≃+* K} (hτ : τ ∈ Subgroup.zpowers σ) {y : K}
    (hy : σ y = y) : τ y = y := by
  have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) y :=
    (Subgroup.zpowers_le (H := MulAction.stabilizer (K ≃+* K) y)).mpr hy
  exact hstab hτ

theorem card_twistedFixed_le_sp4 {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {σ : K ≃+* K} (hσ : σ ≠ 1) {t : K} (ht : t ≠ 0) :
    Nat.card {x : K // t * σ x = x} ≤ 2 ^ (n / 2) := by
  have : Finite (K ≃+* K) := finite_ringEquiv_sp4
  obtain ⟨-, -, -, -, -, h⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hK
  obtain ⟨-, S0, hS0, hcard⟩ := h (Subgroup.zpowers σ)
  have hord : 2 ≤ Nat.card (Subgroup.zpowers σ) := by
    rw [Nat.card_zpowers]
    have h1 : orderOf σ ≠ 1 := fun h => hσ (orderOf_eq_one_iff.mp h)
    have h2 : 0 < orderOf σ := orderOf_pos σ
    omega
  have hle : Nat.card S0 ≤ 2 ^ (n / 2) := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_left hord (by norm_num))
  by_cases hex : ∃ x0 : K, x0 ≠ 0 ∧ t * σ x0 = x0
  · obtain ⟨x0, hx0, hx0t⟩ := hex
    have hmem : ∀ x : {x : K // t * σ x = x}, x.1 / x0 ∈ S0 := by
      rintro ⟨x, hx⟩
      have hσx : σ x = x / t := by
        rw [eq_div_iff ht, mul_comm]
        exact hx
      have hσx0 : σ x0 = x0 / t := by
        rw [eq_div_iff ht, mul_comm]
        exact hx0t
      have hfix : σ (x / x0) = x / x0 := by
        rw [map_div₀, hσx, hσx0]
        field_simp
      have : x / x0 ∈ (S0 : Set K) := by
        rw [hS0]
        intro τ hτ
        exact fixed_of_mem_zpowers_sp4 hτ hfix
      exact this
    have hinj : Function.Injective
        (fun x : {x : K // t * σ x = x} => (⟨x.1 / x0, hmem x⟩ : S0)) := by
      intro x y hxy
      have h1 : x.1 / x0 = y.1 / x0 := congrArg Subtype.val hxy
      exact Subtype.ext ((div_left_inj' hx0).mp h1)
    exact (Nat.card_le_card_of_injective _ hinj).trans hle
  · have hex' : ∀ x0 : K, x0 ≠ 0 → t * σ x0 ≠ x0 := fun x0 h0 h => hex ⟨x0, h0, h⟩
    have hsub : Subsingleton {x : K // t * σ x = x} := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hx : x.1 = 0 := by
        by_contra h
        exact hex' x.1 h x.2
      have hy : y.1 = 0 := by
        by_contra h
        exact hex' y.1 h y.2
      rw [hx, hy]
    have h1 : Nat.card {x : K // t * σ x = x} ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    exact h1.trans Nat.one_le_two_pow

omit [Finite K] in
theorem vAct_false_eq_self_iff {l₁ l₂ : K} {σ : K ≃+* K} {x : K × K} :
    vAct l₁ l₂ σ false x = x ↔ l₁ * σ x.1 = x.1 ∧ l₂ * σ x.2 = x.2 := by
  simp [vAct, Prod.ext_iff]

omit [Finite K] in
theorem vAct_true_eq_self_iff {l₁ l₂ : K} {σ : K ≃+* K} {x : K × K} :
    vAct l₁ l₂ σ true x = x ↔ l₁ * σ x.2 ^ 2 = x.1 ∧ l₂ * σ x.1 = x.2 := by
  simp [vAct, Prod.ext_iff]

theorem card_fixed_vAct_le {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {l₁ l₂ : K}
    (h1 : l₁ ≠ 0) (h2 : l₂ ≠ 0) (σ : K ≃+* K) (ε : Bool)
    (hne : ∃ x, vAct l₁ l₂ σ ε x ≠ x) :
    Nat.card {x : K × K // vAct l₁ l₂ σ ε x = x} ≤ 2 ^ n := by
  cases ε with
  | true =>
    refine (Nat.card_le_card_of_injective
      (fun x : {x : K × K // vAct l₁ l₂ σ true x = x} => x.1.1) ?_).trans hK.le
    intro x y hxy
    apply Subtype.ext
    have hx := (vAct_true_eq_self_iff.mp x.2).2
    have hy := (vAct_true_eq_self_iff.mp y.2).2
    have hxy' : x.1.1 = y.1.1 := hxy
    exact Prod.ext hxy' (by rw [← hx, ← hy, hxy'])
  | false =>
    by_cases hσ : σ = 1
    · subst hσ
      by_cases hl1 : l₁ = 1
      · have hl2 : l₂ ≠ 1 := by
          intro hl2
          obtain ⟨x0, hx0⟩ := hne
          apply hx0
          subst hl1 hl2
          simp [vAct]
        have hzero : ∀ x : {x : K × K // vAct l₁ l₂ 1 false x = x}, x.1.2 = 0 := by
          intro x
          have hx : l₂ * x.1.2 = x.1.2 := (vAct_false_eq_self_iff.mp x.2).2
          have : (l₂ - 1) * x.1.2 = 0 := by linear_combination hx
          exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hl2)
        refine (Nat.card_le_card_of_injective
          (fun x : {x : K × K // vAct l₁ l₂ 1 false x = x} => x.1.1) ?_).trans hK.le
        intro x y hxy
        apply Subtype.ext
        exact Prod.ext (by exact hxy) (by rw [hzero x, hzero y])
      · have hzero : ∀ x : {x : K × K // vAct l₁ l₂ 1 false x = x}, x.1.1 = 0 := by
          intro x
          have hx : l₁ * x.1.1 = x.1.1 := (vAct_false_eq_self_iff.mp x.2).1
          have : (l₁ - 1) * x.1.1 = 0 := by linear_combination hx
          exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hl1)
        refine (Nat.card_le_card_of_injective
          (fun x : {x : K × K // vAct l₁ l₂ 1 false x = x} => x.1.2) ?_).trans hK.le
        intro x y hxy
        apply Subtype.ext
        exact Prod.ext (by rw [hzero x, hzero y]) (by exact hxy)
    · let f : {x : K × K // vAct l₁ l₂ σ false x = x} →
          {b : K // l₁ * σ b = b} × {c : K // l₂ * σ c = c} := fun x =>
        (⟨x.1.1, (vAct_false_eq_self_iff.mp x.2).1⟩, ⟨x.1.2, (vAct_false_eq_self_iff.mp x.2).2⟩)
      have hf : Function.Injective f := by
        intro x y hxy
        apply Subtype.ext
        have h1 := congrArg (fun p => (p.1 : K)) hxy
        have h2 := congrArg (fun p => (p.2 : K)) hxy
        exact Prod.ext h1 h2
      refine (Nat.card_le_card_of_injective f hf).trans ?_
      rw [Nat.card_prod]
      have hb := card_twistedFixed_le_sp4 hn hK hσ h1
      have hc := card_twistedFixed_le_sp4 hn hK hσ h2
      calc Nat.card {b : K // l₁ * σ b = b} * Nat.card {c : K // l₂ * σ c = c}
          ≤ 2 ^ (n / 2) * 2 ^ (n / 2) := Nat.mul_le_mul hb hc
        _ = 2 ^ (n / 2 + n / 2) := (pow_add 2 _ _).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem centralizes_of_offender_vAct {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {V A : Subgroup G} (w : K × K → G) (hwinj : Function.Injective w)
    (hwV : ∀ x, w x ∈ V) (hVw : ∀ y ∈ V, ∃ x, w x = y) (hA : CFSG.Open.IsElemAbelian 2 A)
    (hact : ∀ a ∈ A, ∃ (l₁ l₂ : K) (σ : K ≃+* K) (ε : Bool), l₁ ≠ 0 ∧ l₂ ≠ 0 ∧
      ∀ x : K × K, a * w x * a⁻¹ = w (vAct l₁ l₂ σ ε x))
    (hidx : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)))
    (hineq : Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
      Nat.card A * Nat.card ↥(A ⊓ V)) :
    A ≤ Subgroup.centralizer (V : Set G) := by
  classical
  by_contra hnot
  obtain ⟨a0, ha0A, ha0C⟩ : ∃ a0 ∈ A, a0 ∉ Subgroup.centralizer (V : Set G) := by
    by_contra h
    exact hnot fun a ha => by
      by_contra hc
      exact h ⟨a, ha, hc⟩
  obtain ⟨l₁, l₂, σ, ε, h1, h2, hw0⟩ := hact a0 ha0A
  have hne : ∃ x, vAct l₁ l₂ σ ε x ≠ x := by
    by_contra h
    have h' : ∀ x, vAct l₁ l₂ σ ε x = x := fun x => by
      by_contra hx
      exact h ⟨x, hx⟩
    apply ha0C
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := hVw y hy
    have h3 := hw0 x
    rw [h' x, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  have hfixmem : ∀ y : ↥(A ⊓ V), vAct l₁ l₂ σ ε (Classical.choose (hVw y.1 y.2.2)) =
      Classical.choose (hVw y.1 y.2.2) := by
    intro y
    have hwx : w (Classical.choose (hVw y.1 y.2.2)) = y.1 := Classical.choose_spec (hVw y.1 y.2.2)
    apply hwinj
    rw [← hw0, hwx]
    have hcomm : a0 * y.1 = y.1 * a0 :=
      congrArg Subtype.val (hA.1.is_comm.comm ⟨a0, ha0A⟩ ⟨y.1, y.2.1⟩)
    rw [hcomm]
    group
  have hfix : Nat.card ↥(A ⊓ V) ≤ 2 ^ n := by
    refine le_trans ?_ (card_fixed_vAct_le (by omega) hK h1 h2 σ ε hne)
    refine Nat.card_le_card_of_injective
      (fun y : ↥(A ⊓ V) => (⟨Classical.choose (hVw y.1 y.2.2), hfixmem y⟩ :
        {x : K × K // vAct l₁ l₂ σ ε x = x})) ?_
    intro y y' hyy
    have h3 : Classical.choose (hVw y.1 y.2.2) = Classical.choose (hVw y'.1 y'.2.2) :=
      congrArg Subtype.val hyy
    apply Subtype.ext
    rw [← Classical.choose_spec (hVw y.1 y.2.2), ← Classical.choose_spec (hVw y'.1 y'.2.2), h3]
  have hVcard : Nat.card V = 2 ^ n * 2 ^ n := by
    have hbij : Function.Bijective (fun x : K × K => (⟨w x, hwV x⟩ : V)) := by
      refine ⟨fun x y h => hwinj (Subtype.mk.inj h), fun y => ?_⟩
      obtain ⟨x, hx⟩ := hVw y.1 y.2
      exact ⟨x, Subtype.ext hx⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, hK]
  have hCpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  have h4 : 2 ^ n * 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
      (2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))) * 2 ^ n := by
    calc 2 ^ n * 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))
        = Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by rw [hVcard]
      _ ≤ Nat.card A * Nat.card ↥(A ⊓ V) := hineq
      _ ≤ (2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))) * 2 ^ n :=
          Nat.mul_le_mul hidx hfix
  have h5 : 2 ^ n * 2 ^ n ≤ 2 * 2 ^ n :=
    Nat.le_of_mul_le_mul_right (c := Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)))
      (h4.trans (le_of_eq (by ring))) hCpos
  have h6 : 2 ^ n ≤ 2 := Nat.le_of_mul_le_mul_right h5 (by positivity)
  have h7 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem card_le_two_mul_of_out {G : Type} [Group G] [Finite G] {L S R V A : Subgroup G}
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (φ : ↥L ≃* StatedProj (StatedSp 2 F))
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hS2 : IsPGroup 2 S)
    (hRL : R ≤ L) (hRS : R ≤ S) (hRsyl : IsSylowTwoOf R L)
    (hVL : V ≤ L) (hVR : ∀ r ∈ R, ∀ v ∈ V, r * v = v * r)
    (hAS : A ≤ S) (hA : CFSG.Open.IsElemAbelian 2 A) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hF
  let _ : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hF]
  obtain ⟨hcyc, hcard⟩ := CFSG.QuasithinUnique.Lin2.sp4OutCyclic F n hFc (by omega)
  have : Finite (Outer (StatedProj (StatedSp 2 F))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  let _ : Fintype (Outer (StatedProj (StatedSp 2 F))) := Fintype.ofFinite _
  have hZ : Subgroup.center ↥L = ⊥ := CFSG.QuasithinUnique.Lin2.Five.center_eq_bot_of_equiv φ
  let Ψ : S →* Outer (StatedProj (StatedSp 2 F)) :=
    (equivalence φ).toMonoidHom.comp (CFSG.QuasithinUnique.Lin2.Five.outAct L hSN)
  have hker : ∀ t : S, Ψ t = 1 ↔ (t : G) ∈ R ⊔ (S ⊓ Subgroup.centralizer (L : Set G)) := fun t => by
    show equivalence φ (CFSG.QuasithinUnique.Lin2.Five.outAct L hSN t) = 1 ↔ _
    rw [map_eq_one_iff _ (equivalence φ).injective]
    exact CFSG.QuasithinUnique.Lin2.Five.mem_ker_outAct_iff hZ hSN hS2 hRL hRS hRsyl t
  let ΨA : A →* Outer (StatedProj (StatedSp 2 F)) := Ψ.comp (Subgroup.inclusion hAS)
  have hrange : Nat.card ΨA.range ≤ 2 := by
    have hsq : ∀ y : ΨA.range, (y : Outer (StatedProj (StatedSp 2 F))) ^ 2 = 1 := by
      rintro ⟨_, x, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (hA.2 x.1 x.2)
      rw [this, map_one]
    have hle := IsCyclic.card_pow_eq_one_le (α := Outer (StatedProj (StatedSp 2 F))) (n := 2)
      (by norm_num)
    calc Nat.card ΨA.range
        ≤ Nat.card {y : Outer (StatedProj (StatedSp 2 F)) // y ^ 2 = 1} :=
          Nat.card_le_card_of_injective (fun y => ⟨y.1, hsq y⟩)
            (fun y z h => Subtype.ext (Subtype.mk.inj h))
      _ = (Finset.univ.filter fun y : Outer (StatedProj (StatedSp 2 F)) => y ^ 2 = 1).card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      _ ≤ 2 := hle
  have hkerC : R ⊔ (S ⊓ Subgroup.centralizer (L : Set G)) ≤
      Subgroup.centralizer (V : Set G) := by
    refine sup_le (fun r hr => ?_) (fun c hc => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hVR r hr v hv).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_iff.mp hc.2 v (hVL hv)
  have hkerle : Nat.card ΨA.ker ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun x : ΨA.ker => (⟨x.1.1, x.1.2,
        hkerC ((hker ⟨x.1.1, hAS x.1.2⟩).mp (MonoidHom.mem_ker.mp x.2))⟩ :
        ↥(A ⊓ Subgroup.centralizer (V : Set G)))) ?_
    intro x y hxy
    have h1 : (x.1.1 : G) = y.1.1 := Subtype.mk.inj hxy
    exact Subtype.ext (Subtype.ext h1)
  have hmul := Subgroup.index_mul_card ΨA.ker
  rw [Subgroup.index_ker] at hmul
  calc Nat.card A = Nat.card ΨA.range * Nat.card ΨA.ker := hmul.symm
    _ ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := Nat.mul_le_mul hrange hkerle

end CFSG.Quasithin.Sp4
