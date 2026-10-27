module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Local
public import CFSG.RankThree.PartTwo.Late.Cores17
public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
import CFSG.RankThree.PartTwo.Sec13.Item136Lift

public section

namespace CFSG.RankThree.PartTwo.Sec13.L3Proof

open CFSG
open scoped commutatorElement

section General

variable {Γ : Type} [Group Γ]

theorem mul_comm_of_mem {A : Subgroup Γ} (hA : IsMulCommutative A) {a b : Γ} (ha : a ∈ A)
    (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (hA.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem exists_fixed_of_inverting {A : Subgroup Γ} (hA : IsMulCommutative A) {x t : Γ}
    (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A) (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (ht2 : t * t = 1)
    (htx : t * x * t⁻¹ = x⁻¹) (hx3 : x ^ 3 = 1) (hfix : ∀ a ∈ A, x * a = a * x → a = 1)
    (hne : A ≠ ⊥) : ∃ a ∈ A, a ≠ 1 ∧ t * a * t⁻¹ = a := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hs : ∀ v ∈ A, t * (v * (t * v * t⁻¹)) * t⁻¹ = v * (t * v * t⁻¹) := by
    intro v hv
    have e : t * (v * (t * v * t⁻¹)) * t⁻¹ = (t * v * t⁻¹) * v := by
      calc t * (v * (t * v * t⁻¹)) * t⁻¹ = (t * v * t⁻¹) * ((t * t) * v * (t⁻¹ * t⁻¹)) := by
            group
        _ = (t * v * t⁻¹) * v := by rw [ht2, ← mul_inv_rev, ht2]; group
    rw [e]
    exact mul_comm_of_mem hA (htA v hv) hv
  obtain ⟨v, hvA, hv1⟩ := (Subgroup.bot_or_exists_ne_one A).resolve_left hne
  by_cases h1 : v * (t * v * t⁻¹) = 1
  · set v' := x * v * x⁻¹ with hv'
    have hv'A : v' ∈ A := hxA v hvA
    by_cases h2 : v' * (t * v' * t⁻¹) = 1
    · exfalso
      have e1 : t * v * t⁻¹ = v⁻¹ := (eq_inv_of_mul_eq_one_right h1)
      have e2 : t * v' * t⁻¹ = v'⁻¹ := (eq_inv_of_mul_eq_one_right h2)
      have e3 : t * v' * t⁻¹ = x⁻¹ * v⁻¹ * x := by
        calc t * v' * t⁻¹ = (t * x * t⁻¹) * (t * v * t⁻¹) * (t * x * t⁻¹)⁻¹ := by
              rw [hv']; group
          _ = x⁻¹ * v⁻¹ * x := by rw [htx, e1, inv_inv]
      have hc : Commute (x * x) v⁻¹ := by
        have h := e3.symm.trans e2
        rw [hv'] at h
        have h' : x⁻¹ * v⁻¹ * x = x * v⁻¹ * x⁻¹ := by rw [h]; group
        change (x * x) * v⁻¹ = v⁻¹ * (x * x)
        calc (x * x) * v⁻¹ = x * (x * v⁻¹ * x⁻¹) * x := by group
          _ = x * (x⁻¹ * v⁻¹ * x) * x := by rw [h']
          _ = v⁻¹ * (x * x) := by group
      have hc' : Commute (x * x) v := by simpa using hc.inv_right
      have hx4 : (x * x) * (x * x) = x := by
        calc (x * x) * (x * x) = x ^ 3 * x := by rw [pow_three]; group
          _ = x := by rw [hx3, one_mul]
      have hxv : x * v = v * x := by
        have := hc'.mul_left hc'
        rw [hx4] at this
        exact this
      exact hv1 (hfix v hvA hxv)
    · exact ⟨_, A.mul_mem hv'A (htA v' hv'A), h2, hs v' hv'A⟩
  · exact ⟨_, A.mul_mem hvA (htA v hvA), h1, hs v hvA⟩

theorem commutator_inf_centralizer_eq_bot [Finite Γ] {V B : Subgroup Γ} (hV : IsMulCommutative V)
    (hBV : B ≤ Subgroup.normalizer (V : Set Γ)) (hcop : Nat.Coprime (Nat.card B) (Nat.card V)) :
    ⁅V, B⁆ ⊓ Subgroup.centralizer (B : Set Γ) = ⊥ := by
  let : CommGroup V := IsMulCommutative.instCommGroup
  let := Fintype.ofFinite B
  let ψ : B → (V →* V) := fun b => (V.normalizerMonoidHom ⟨b, hBV b.2⟩).toMonoidHom
  have hψ : ∀ (b : B) (y : V), ((ψ b y : V) : Γ) = b * y * (b : Γ)⁻¹ := fun b y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe V _ y
  have hψmul : ∀ (b b' : B) (y : V), ψ b' (ψ b y) = ψ (b' * b) y := fun b b' y => by
    apply Subtype.ext
    rw [hψ, hψ, hψ, Subgroup.coe_mul]
    group
  let N : V →* V := ∏ b : B, ψ b
  have hN : ∀ y : V, N y = ∏ b : B, ψ b y := fun y => MonoidHom.finsetProd_apply _ _ _
  have hNψ : ∀ (b : B) (y : V), N (ψ b y) = N y := by
    intro b y
    rw [hN, hN]
    simp only [hψmul]
    exact Fintype.prod_equiv (Equiv.mulRight b) _ _ fun b' => rfl
  have hmemV : ∀ v ∈ V, ∀ b ∈ B, ⁅v, b⁆ ∈ V := by
    intro v hv b hb
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine V.mul_mem hv ?_
    have := (Subgroup.mem_normalizer_iff.mp (hBV hb) v⁻¹).mp (V.inv_mem hv)
    simpa [mul_assoc] using this
  have hcommV : ⁅V, B⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    exact hmemV
  have hker : ⁅V, B⁆ ≤ N.ker.map V.subtype := by
    rw [Subgroup.commutator_le]
    intro v hv b hb
    refine ⟨⟨⁅v, b⁆, hmemV v hv b hb⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have e : (⟨⁅v, b⁆, hmemV v hv b hb⟩ : V) = ⟨v, hv⟩ * (ψ ⟨b, hb⟩ ⟨v, hv⟩)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hψ]
      change ⁅v, b⁆ = v * (b * v * b⁻¹)⁻¹
      rw [commutatorElement_def]
      group
    rw [e, map_mul, map_inv, hNψ, mul_inv_cancel]
  rw [eq_bot_iff]
  intro w ⟨hwc, hwC⟩
  have hwV : w ∈ V := hcommV hwc
  obtain ⟨y, hy, hyw⟩ := hker hwc
  have hyw' : y = ⟨w, hwV⟩ := Subtype.ext hyw
  subst hyw'
  have hpow : N ⟨w, hwV⟩ = ⟨w, hwV⟩ ^ Nat.card B := by
    have hfix : ∀ b : B, ψ b ⟨w, hwV⟩ = ⟨w, hwV⟩ := fun b => by
      apply Subtype.ext
      rw [hψ, Subgroup.mem_centralizer_iff.mp hwC b b.2]
      group
    rw [hN, Finset.prod_congr rfl fun b _ => hfix b, Finset.prod_const, Finset.card_univ,
      Fintype.card_eq_nat_card]
  rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy
  rw [hy] at hpow
  have h1 : orderOf (⟨w, hwV⟩ : V) ∣ Nat.card B := orderOf_dvd_of_pow_eq_one hpow.symm
  have h2 : orderOf (⟨w, hwV⟩ : V) ∣ Nat.card V := orderOf_dvd_natCard _
  have h3 : orderOf (⟨w, hwV⟩ : V) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff] at h3
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h3

theorem mem_normalizer_commutator {H K : Subgroup Γ} {g : Γ}
    (hH : g ∈ Subgroup.normalizer (H : Set Γ)) (hK : g ∈ Subgroup.normalizer (K : Set Γ)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup Γ) : Set Γ) := by
  have hmap : ∀ {S : Subgroup Γ}, g ∈ Subgroup.normalizer (S : Set Γ) →
      S.map (MulAut.conj g).toMonoidHom = S := by
    intro S hS
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hS y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff.mp hS _).mpr (by simpa [mul_assoc]), ?_⟩
      change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  have e : (⁅H, K⁆ : Subgroup Γ).map (MulAut.conj g).toMonoidHom = ⁅H, K⁆ := by
    rw [Subgroup.map_commutator, hmap hH, hmap hK]
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    rw [← e]
    exact ⟨w, hw, rfl⟩
  · intro hw
    rw [← e] at hw
    obtain ⟨y, hy, hyw⟩ := hw
    have : y = w := by
      have h' : g * y * g⁻¹ = g * w * g⁻¹ := hyw
      simpa using h'
    rwa [← this]

theorem sup_zpowers_facts {x₁ x₂ : Γ} (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1)
    (h2 : x₂ ^ 3 = 1) :
    IsMulCommutative (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup Γ) ∧
      ∀ e ∈ (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup Γ), e ^ 3 = 1 := by
  have hc : ∀ i j k l : ℤ, x₁ ^ i * x₂ ^ j * (x₁ ^ k * x₂ ^ l) =
      x₁ ^ k * x₂ ^ l * (x₁ ^ i * x₂ ^ j) := by
    intro i j k l
    have hc1 : ∀ a b : ℤ, x₂ ^ b * x₁ ^ a = x₁ ^ a * x₂ ^ b := fun a b =>
      (Commute.zpow_zpow h12 a b).eq.symm
    calc x₁ ^ i * x₂ ^ j * (x₁ ^ k * x₂ ^ l) = x₁ ^ i * (x₂ ^ j * x₁ ^ k) * x₂ ^ l := by group
      _ = x₁ ^ i * (x₁ ^ k * x₂ ^ j) * x₂ ^ l := by rw [hc1]
      _ = x₁ ^ k * (x₁ ^ i * x₂ ^ l) * x₂ ^ j := by
          rw [← mul_assoc, ← zpow_add, add_comm, zpow_add]
          simp only [mul_assoc]
          rw [← zpow_add, ← zpow_add, add_comm j l]
      _ = x₁ ^ k * (x₂ ^ l * x₁ ^ i) * x₂ ^ j := by rw [hc1]
      _ = x₁ ^ k * x₂ ^ l * (x₁ ^ i * x₂ ^ j) := by group
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
  · obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup h12 a.2
    obtain ⟨k, l, hkl⟩ := Sec4.exists_zpow_mul_of_mem_sup h12 b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hij, hkl]
    exact hc i j k l
  · obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup h12 he
    have hc1 : Commute (x₁ ^ i) (x₂ ^ j) := Commute.zpow_zpow h12 i j
    rw [hc1.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm,
      zpow_mul, mul_comm j, zpow_mul]
    simp only [Nat.cast_ofNat]
    rw [show (x₁ ^ (3 : ℤ)) = 1 by exact_mod_cast h1, show (x₂ ^ (3 : ℤ)) = 1 by
      exact_mod_cast h2, one_zpow, one_zpow, one_mul]

theorem mem_normalizer_of_conj_mem_of_finite [Finite Γ] {Y : Subgroup Γ} {g : Γ}
    (h : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) : g ∈ Subgroup.normalizer (Y : Set Γ) := by
  have hle : Y.map (MulAut.conj g).toMonoidHom ≤ Y := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : Y.map (MulAut.conj g).toMonoidHom = Y := Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  rw [← heq] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  have hzy' : g * z * g⁻¹ = g * y * g⁻¹ := hzy
  have : z = y := by simpa using hzy'
  rwa [← this]

theorem mem_centralizer_zpowers_of_commute {a x : Γ} (h : a * x = x * a) :
    a ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, rfl⟩
  exact (Commute.zpow_left (show Commute x a from h.symm) k).eq

end General

section Critical

variable {X : Type} [Group X] [Finite X] {r : ℕ} [hr : Fact r.Prime] {D : Subgroup X}

omit [Finite X] hr in
theorem isPGroup_of_criticalAt (hD : Sec4.Census.CriticalAt r D) : IsPGroup r D :=
  CFSG.pCore_isPGroup.to_le hD.le

theorem commutator_mem_frattini_map (hD : Sec4.Census.CriticalAt r D) {a b : X} (ha : a ∈ D)
    (hb : b ∈ D) : ⁅a, b⁆ ∈ (frattini D).map D.subtype := by
  refine ⟨⁅⟨a, ha⟩, ⟨b, hb⟩⁆, CFSG.SectionRank.Ccomm.commutator_mem_frattini
    (isPGroup_of_criticalAt hD) _ _, ?_⟩
  simp [commutatorElement_def]

omit [Finite X] in
theorem frattini_map_le (D : Subgroup X) : (frattini D).map D.subtype ≤ D :=
  Subgroup.map_subtype_le _

omit [Finite X] hr in
theorem mem_frattiniKer_of_forall (hD : Sec4.Census.CriticalAt r D) {e : X}
    (he : ∀ d ∈ D, d⁻¹ * (e * d * e⁻¹) ∈ (frattini D).map D.subtype) : e ∈ hD.frattiniKer := by
  rw [Sec4.Census.CriticalAt.mem_frattiniKer_iff]
  ext q
  induction q using QuotientGroup.induction_on with
  | H d =>
    change (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini D)
      (hD.conjD e)) (QuotientGroup.mk' _ d) = QuotientGroup.mk' _ d
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h := he d d.2
    have hmem : ((hD.conjD e d)⁻¹ * d : D) ∈ frattini D := by
      rw [← Subgroup.mem_map_iff_mem D.subtype_injective]
      have e1 : D.subtype ((hD.conjD e d)⁻¹ * d) = ((d : X)⁻¹ * (e * d * e⁻¹))⁻¹ := by
        rw [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, hD.conjD_apply]
        group
      rw [e1]
      exact Subgroup.inv_mem _ h
    exact hmem

omit [Finite X] in
theorem exists_lift_fixed (hD : Sec4.Census.CriticalAt r D) (hr2 : r ≠ 2) {t : X}
    (ht2 : t * t = 1) {u₀ : X} (hu₀ : u₀ ∈ D)
    (hfix : u₀⁻¹ * (t * u₀ * t⁻¹) ∈ (frattini D).map D.subtype) :
    ∃ u ∈ D, u₀⁻¹ * u ∈ (frattini D).map D.subtype ∧ t * u * t⁻¹ = u := by
  have := hD.normal
  set z := u₀⁻¹ * (t * u₀ * t⁻¹) with hz
  have hzD : z ∈ D := frattini_map_le D hfix
  have hzr : z ^ r = 1 := hD.exp z hzD
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htz : t * z * t⁻¹ = z⁻¹ := by
    rw [hz]
    calc t * (u₀⁻¹ * (t * u₀ * t⁻¹)) * t⁻¹ = t * u₀⁻¹ * t⁻¹ * ((t * t) * u₀ * (t⁻¹ * t⁻¹)) := by
          group
      _ = (u₀⁻¹ * (t * u₀ * t⁻¹))⁻¹ := by rw [ht2, ← mul_inv_rev, ht2]; group
  obtain ⟨m, hm⟩ : Odd r := hr.out.odd_of_ne_two hr2
  refine ⟨u₀ * z ^ (m + 1), D.mul_mem hu₀ (D.pow_mem hzD _), ?_, ?_⟩
  · rw [inv_mul_cancel_left]
    exact Subgroup.pow_mem _ hfix _
  · have htu : t * u₀ * t⁻¹ = u₀ * z := by rw [hz]; group
    have hzz : z ^ (m + 1) * z ^ (m + 1) = z := by
      rw [← pow_add, show m + 1 + (m + 1) = r + 1 by omega, pow_succ, hzr, one_mul]
    calc t * (u₀ * z ^ (m + 1)) * t⁻¹ = (t * u₀ * t⁻¹) * (t * z * t⁻¹) ^ (m + 1) := by
          rw [conj_pow]; group
      _ = u₀ * (z * (z ^ (m + 1))⁻¹) := by rw [htu, htz, inv_pow]; group
      _ = u₀ * z ^ (m + 1) := by
          congr 1
          rw [mul_inv_eq_iff_eq_mul, hzz]

theorem three_le_pRank_of_card_map [D.Normal] (hD : Sec4.Census.CriticalAt r D) {P : Subgroup X}
    (hPD : P ≤ D)
    (hcard : r ^ 3 ≤ Nat.card (P.map (QuotientGroup.mk' ((frattini D).map D.subtype)))) :
    3 ≤ CFSG.pRank r P := by
  have hp : r.Prime := hr.out
  set Φ : Subgroup X := (frattini D).map D.subtype with hΦ
  have hPp : IsPGroup r P := (isPGroup_of_criticalAt hD).to_le hPD
  have hexpP : ∀ x : P, x ^ r = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hD.exp x (hPD x.2))
  have hclassP : commutator P ≤ Subgroup.center P := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h := (hD.comm a (hPD a.2) b (hD.le (hPD b.2))).2 g (hPD g.2)
    simp only [Subgroup.coe_mul]
    have hc : ((⁅a, b⁆ : P) : X) = ⁅(a : X), (b : X)⁆ := by simp [commutatorElement_def]
    rw [hc]
    exact h.symm
  set φ : P →* X ⧸ Φ := (QuotientGroup.mk' Φ).comp P.subtype with hφ
  have hker : commutator P ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    have hc : P.subtype ⁅a, b⁆ = ⁅(a : X), (b : X)⁆ := by simp [commutatorElement_def]
    rw [hc]
    exact commutator_mem_frattini_map hD (hPD a.2) (hPD b.2)
  have hrange : φ.range = P.map (QuotientGroup.mk' Φ) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hle : Nat.card (P.map (QuotientGroup.mk' Φ)) ≤ Nat.card (P ⧸ commutator P) := by
    rw [← hrange]
    refine Nat.card_le_card_of_surjective
      (fun q => ⟨QuotientGroup.lift (commutator P) φ hker q, ?_⟩) ?_
    · induction q using QuotientGroup.induction_on with
      | H x => exact ⟨x, rfl⟩
    · rintro ⟨_, ⟨x, rfl⟩⟩
      exact ⟨(x : P ⧸ commutator P), rfl⟩
  obtain ⟨k, hk⟩ := (hPp.to_quotient (commutator P)).exists_card_eq
  have hk3 : 3 ≤ k := by
    have h1 : r ^ 3 ≤ r ^ k := hk ▸ hcard.trans hle
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
  have hrk := (quotient_commutator_rank hp hexpP hk).2
  by_contra hlt
  push Not at hlt
  have h2 := (class_two_small_rank_order_bounds hPp hexpP hclassP).1 (by omega)
  omega

theorem eq_and_eq_of_mul_eq {Γ : Type*} [Group Γ] {H K : Subgroup Γ} (hHK : Disjoint H K)
    {x x' y y' : Γ} (hx : x ∈ H) (hx' : x' ∈ H) (hy : y ∈ K) (hy' : y' ∈ K)
    (h : x * y = x' * y') : x = x' ∧ y = y' := by
  have e : x'⁻¹ * x = y' * y⁻¹ := by
    calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
      _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h]
      _ = y' * y⁻¹ := by group
  have hmem : x'⁻¹ * x ∈ H ⊓ K :=
    ⟨H.mul_mem (H.inv_mem hx') hx, e ▸ K.mul_mem hy' (K.inv_mem hy)⟩
  rw [hHK.eq_bot, Subgroup.mem_bot] at hmem
  have h1 : x = x' := by
    calc x = x' * (x'⁻¹ * x) := by group
      _ = x' := by rw [hmem, mul_one]
  subst h1
  exact ⟨rfl, mul_left_cancel h⟩

theorem three_le_pRank_inf_centralizer (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hD : Sec4.Census.CriticalAt r D) {x₁ x₂ t : X} (h12 : x₁ * x₂ = x₂ * x₁)
    (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hE9 : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup X) = 9)
    (ht2 : t * t = 1) (ht₁ : t * x₁ * t⁻¹ = x₁⁻¹) (ht₂ : t * x₂ * t⁻¹ = x₂⁻¹)
    (htr : ∀ x ∈ (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup X), x ≠ 1 →
      ∀ y ∈ (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup X), y ≠ 1 →
        ∃ n ∈ Subgroup.normalizer
          ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup X) : Set X), n * x * n⁻¹ = y)
    (hne : ∃ e ∈ (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup X),
      ∃ y ∈ CFSG.pCore r X, e * y * e⁻¹ ≠ y) :
    3 ≤ CFSG.pRank r ↥(D ⊓ Subgroup.centralizer {t}) := by
  classical
  have hp : r.Prime := hr.out
  have := hD.normal
  set E : Subgroup X := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ with hEdef
  obtain ⟨hEc, hE3⟩ := sup_zpowers_facts h12 h1 h2
  set Φ : Subgroup X := (frattini D).map D.subtype with hΦ
  have hΦD : Φ ≤ D := frattini_map_le D
  set π : X →* X ⧸ Φ := QuotientGroup.mk' Φ with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective Φ
  have hπker : ∀ x : X, π x = 1 ↔ x ∈ Φ := fun x => QuotientGroup.eq_one_iff x
  have hDp : IsPGroup r D := isPGroup_of_criticalAt hD
  have hcop3 : ∀ {k : ℕ}, Nat.Coprime 3 (r ^ k) := fun {k} =>
    Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hr3))
  have hinj1 : ∀ x ∈ E, π x = 1 → x = 1 := by
    intro x hx hx1
    have hxD : x ∈ D := hΦD ((hπker x).mp hx1)
    obtain ⟨n, hn⟩ := hDp ⟨x, hxD⟩
    have hn' : x ^ r ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hE3 x hx)
    have hrn : orderOf x ∣ r ^ n := orderOf_dvd_of_pow_eq_one hn'
    have := Nat.eq_one_of_dvd_coprimes hcop3 h3 hrn
    exact orderOf_eq_one_iff.mp this
  have hinj : Set.InjOn π E := by
    intro a ha b hb hab
    have h := hinj1 (a⁻¹ * b) (E.mul_mem (E.inv_mem ha) hb) (by
      rw [map_mul, map_inv, hab, inv_mul_cancel])
    calc a = a * (a⁻¹ * b) := by rw [h, mul_one]
      _ = b := by group
  set V : Subgroup (X ⧸ Φ) := D.map π with hV
  have hVn : V.Normal := Subgroup.Normal.map inferInstance π hπsurj
  have hVc : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (by
    obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h := commutator_mem_frattini_map hD (D.inv_mem hb') (D.inv_mem ha')
    rw [commutatorElement_def, inv_inv, inv_inv] at h
    rw [show (a' * b')⁻¹ * (b' * a') = b'⁻¹ * a'⁻¹ * b' * a' by group]
    exact h)⟩⟩
  have hVp : IsPGroup r V := hDp.map π
  obtain ⟨kV, hkV⟩ := hVp.exists_card_eq
  have hVexp : ∀ v ∈ V, v ^ r = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_pow, hD.exp d hd, map_one]
  set y₁ := π x₁ with hy₁
  set y₂ := π x₂ with hy₂
  set Eb : Subgroup (X ⧸ Φ) := E.map π with hEb
  have hEbeq : Eb = Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ := by
    rw [hEb, hEdef, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  have hEb9 : Nat.card Eb = 9 := by
    rw [hEb, Sec13.card_map_eq_of_injOn π hinj, hE9]
  have hy12 : y₁ * y₂ = y₂ * y₁ := by rw [hy₁, hy₂, ← map_mul, ← map_mul, h12]
  have hy13 : y₁ ^ 3 = 1 := by rw [hy₁, ← map_pow, h1, map_one]
  have hy23 : y₂ ^ 3 = 1 := by rw [hy₂, ← map_pow, h2, map_one]
  obtain ⟨hEbc, hEb3⟩ := sup_zpowers_facts hy12 hy13 hy23
  rw [← hEbeq] at hEbc hEb3
  have hEbel : CFSG.Assembly.IsElemAbelian 3 Eb := ⟨hEbc, hEb3⟩
  have hy₁E : y₁ ∈ Eb := hEbeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers y₁)
  have hy₂E : y₂ ∈ Eb := hEbeq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y₂)
  have hEbV : Eb ≤ Subgroup.normalizer (V : Set (X ⧸ Φ)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hVn]
    exact le_top
  set W : Subgroup (X ⧸ Φ) := ⁅V, Eb⁆ with hW
  have hWV : W ≤ V := Subgroup.commutator_le_left V Eb
  have hWc : IsMulCommutative W :=
    ⟨⟨fun a b => Subtype.ext (mul_comm_of_mem hVc (hWV a.2) (hWV b.2))⟩⟩
  have hnormW : ∀ g ∈ Subgroup.normalizer (Eb : Set (X ⧸ Φ)),
      g ∈ Subgroup.normalizer (W : Set (X ⧸ Φ)) := fun g hg =>
    mem_normalizer_commutator (by rw [Subgroup.normalizer_eq_top_iff.mpr hVn]; trivial) hg
  have hEbW : Eb ≤ Subgroup.normalizer (W : Set (X ⧸ Φ)) := fun g hg =>
    hnormW g (Subgroup.le_normalizer hg)
  have hWp : IsPGroup r W := hVp.to_le hWV
  obtain ⟨kW, hkW⟩ := hWp.exists_card_eq
  have hcopW : Nat.Coprime 3 (Nat.card W) := hkW ▸ hcop3
  have hfix : W ⊓ Subgroup.centralizer (Eb : Set (X ⧸ Φ)) = ⊥ :=
    commutator_inf_centralizer_eq_bot hVc hEbV (by
      rw [hEb9, hkV, show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left 2 hcop3)
  have hWne : W ≠ ⊥ := by
    intro hWbot
    obtain ⟨e, he, y, hy, hey⟩ := hne
    apply hey
    have hcomm : ∀ d ∈ D, d⁻¹ * (e * d * e⁻¹) ∈ Φ := by
      intro d hd
      have hc : ⁅π d, π e⁆ ∈ W :=
        Subgroup.commutator_mem_commutator ⟨d, hd, rfl⟩ ⟨e, he, rfl⟩
      rw [hWbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      rw [← hπker, map_mul, map_inv, map_mul, map_mul, map_inv, ← hc]
      group
    have hmem := mem_frattiniKer_of_forall hD hcomm
    have hord : Nat.Coprime (orderOf e) r :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one (hE3 e he))
        ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hr3))
    exact hD.centralizes_of_mem_frattiniKer hmem hord y hy
  obtain ⟨hgen, hind⟩ := Late.iSup_inf_centralizer_eq_and_iSupIndep Nat.prime_three hEbel
    (by rw [hEb9]; norm_num) hEbW hWc hcopW hfix
  obtain ⟨w₀, hw₀W, hw₀1, z₀, hz₀E, hz₀1, hw₀z₀⟩ :
      ∃ w ∈ W, w ≠ 1 ∧ ∃ z ∈ Eb, z ≠ 1 ∧ w * z = z * w := by
    by_contra hcon
    push Not at hcon
    apply hWne
    rw [← hgen, eq_bot_iff]
    refine iSup_le fun D₀ => ?_
    rintro w ⟨hwW, hwC⟩
    rw [Subgroup.mem_bot]
    by_contra hw1
    obtain ⟨z, hz, hz1⟩ := (Subgroup.bot_or_exists_ne_one (D₀ : Subgroup (X ⧸ Φ))).resolve_left
      (by
        intro h
        have h3 := D₀.2.2
        rw [h, Subgroup.card_bot] at h3
        norm_num at h3)
    exact hcon w hwW hw1 z (D₀.2.1 hz) hz1 (Subgroup.mem_centralizer_iff.mp hwC z hz).symm
  have htrans : ∀ xb ∈ Eb, xb ≠ 1 → ∃ w ∈ W, w ≠ 1 ∧ w * xb = xb * w := by
    intro xb hxb hxb1
    obtain ⟨x, hx, rfl⟩ := hxb
    obtain ⟨y, hy, rfl⟩ := hz₀E
    have hx1 : x ≠ 1 := fun h => hxb1 (by rw [h, map_one])
    have hy1 : y ≠ 1 := fun h => hz₀1 (by rw [h, map_one])
    obtain ⟨n, hn, hny⟩ := htr y hy hy1 x hx hx1
    have hnE : π n ∈ Subgroup.normalizer (Eb : Set (X ⧸ Φ)) :=
      Subgroup.le_normalizer_map π ⟨n, hn, rfl⟩
    have hnW := hnormW (π n) hnE
    refine ⟨π n * w₀ * (π n)⁻¹, (Subgroup.mem_normalizer_iff.mp hnW w₀).mp hw₀W, ?_, ?_⟩
    · intro h
      apply hw₀1
      calc w₀ = (π n)⁻¹ * (π n * w₀ * (π n)⁻¹) * π n := by group
        _ = 1 := by rw [h]; group
    · rw [← hny, map_mul, map_mul, map_inv]
      calc π n * w₀ * (π n)⁻¹ * (π n * π y * (π n)⁻¹) = π n * (w₀ * π y) * (π n)⁻¹ := by
            group
        _ = π n * (π y * w₀) * (π n)⁻¹ := by rw [hw₀z₀]
        _ = π n * π y * (π n)⁻¹ * (π n * w₀ * (π n)⁻¹) := by group
  have htE : ∀ y ∈ E, t * y * t⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup h12 hy
    rw [show t * (x₁ ^ i * x₂ ^ j) * t⁻¹ = (t * x₁ * t⁻¹) ^ i * (t * x₂ * t⁻¹) ^ j by
      rw [conj_zpow, conj_zpow]; group, ht₁, ht₂, inv_zpow', inv_zpow',
      (Commute.zpow_zpow h12 i j).eq, mul_inv_rev, zpow_neg, zpow_neg]
  have htN : t ∈ Subgroup.normalizer (E : Set X) := mem_normalizer_of_conj_mem_of_finite
    fun y hy => by rw [htE y hy]; exact E.inv_mem hy
  set tb := π t with htb
  have htbE : ∀ y ∈ Eb, tb * y * tb⁻¹ = y⁻¹ := by
    rintro _ ⟨y, hy, rfl⟩
    rw [htb, ← map_inv, ← map_mul, ← map_mul, htE y hy, map_inv]
  have htbW : tb ∈ Subgroup.normalizer (W : Set (X ⧸ Φ)) :=
    hnormW tb (Subgroup.le_normalizer_map π ⟨t, htN, rfl⟩)
  have htbt : tb * tb = 1 := by rw [htb, ← map_mul, ht2, map_one]
  have hS3 : ∀ xb zb : X ⧸ Φ, xb ∈ Eb → zb ∈ Eb → xb ≠ 1 →
      (∀ a : X ⧸ Φ, a * xb = xb * a → a * zb = zb * a → a * y₁ = y₁ * a ∧ a * y₂ = y₂ * a) →
      ∃ w ∈ W, w ≠ 1 ∧ w * xb = xb * w ∧ tb * w * tb⁻¹ = w := by
    intro xb zb hxb hzb hxb1 hgen2
    set A : Subgroup (X ⧸ Φ) := W ⊓ Subgroup.centralizer ({xb} : Set (X ⧸ Φ)) with hA
    have hAc : IsMulCommutative A :=
      ⟨⟨fun a b => Subtype.ext (mul_comm_of_mem hWc a.2.1 b.2.1)⟩⟩
    have hzxb : zb * xb = xb * zb := mul_comm_of_mem hEbc hzb hxb
    have hzA : ∀ a ∈ A, zb * a * zb⁻¹ ∈ A := by
      intro a ha
      obtain ⟨haW, haC⟩ := Subgroup.mem_inf.mp ha
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hEbW hzb) a).mp haW, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at haC ⊢
      have hxz : zb⁻¹ * xb * zb = xb := by rw [mul_assoc, ← hzxb]; group
      have hzx : zb * xb * zb⁻¹ = xb := by rw [hzxb]; group
      calc zb * a * zb⁻¹ * xb = zb * (a * (zb⁻¹ * xb * zb)) * zb⁻¹ := by group
        _ = zb * (a * xb) * zb⁻¹ := by rw [hxz]
        _ = zb * (xb * a) * zb⁻¹ := by rw [haC]
        _ = (zb * xb * zb⁻¹) * (zb * a * zb⁻¹) := by group
        _ = xb * (zb * a * zb⁻¹) := by rw [hzx]
    have htA : ∀ a ∈ A, tb * a * tb⁻¹ ∈ A := by
      intro a ha
      obtain ⟨haW, haC⟩ := Subgroup.mem_inf.mp ha
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp htbW a).mp haW, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at haC ⊢
      have hτ' : tb * xb⁻¹ * tb⁻¹ = xb := by
        have h := htbE xb⁻¹ (Eb.inv_mem hxb)
        rwa [inv_inv] at h
      have hτ : tb⁻¹ * xb * tb = xb⁻¹ := by
        calc tb⁻¹ * xb * tb = tb⁻¹ * (tb * xb⁻¹ * tb⁻¹) * tb := by rw [hτ']
          _ = xb⁻¹ := by group
      have haC' : a * xb⁻¹ = xb⁻¹ * a := (Commute.inv_right (show Commute a xb from haC)).eq
      calc tb * a * tb⁻¹ * xb = tb * (a * (tb⁻¹ * xb * tb)) * tb⁻¹ := by group
        _ = tb * (a * xb⁻¹) * tb⁻¹ := by rw [hτ]
        _ = tb * (xb⁻¹ * a) * tb⁻¹ := by rw [haC']
        _ = (tb * xb⁻¹ * tb⁻¹) * (tb * a * tb⁻¹) := by group
        _ = xb * (tb * a * tb⁻¹) := by rw [hτ']
    have hfixA : ∀ a ∈ A, zb * a = a * zb → a = 1 := by
      intro a ha hza
      obtain ⟨haW, haC⟩ := Subgroup.mem_inf.mp ha
      rw [Subgroup.mem_centralizer_singleton_iff] at haC
      obtain ⟨h1', h2'⟩ := hgen2 a haC hza.symm
      have hC : a ∈ Subgroup.centralizer (Eb : Set (X ⧸ Φ)) := by
        have hle : Eb ≤ Subgroup.centralizer ({a} : Set (X ⧸ Φ)) := by
          rw [hEbeq]
          exact sup_le (Subgroup.zpowers_le.mpr
              (Subgroup.mem_centralizer_singleton_iff.mpr h1'.symm))
            (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h2'.symm))
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
      have hmem : a ∈ W ⊓ Subgroup.centralizer (Eb : Set (X ⧸ Φ)) := ⟨haW, hC⟩
      rw [hfix, Subgroup.mem_bot] at hmem
      exact hmem
    have hAne : A ≠ ⊥ := by
      obtain ⟨w, hwW, hw1, hwx⟩ := htrans xb hxb hxb1
      intro hAbot
      have hwA : w ∈ A :=
        Subgroup.mem_inf.mpr ⟨hwW, Subgroup.mem_centralizer_singleton_iff.mpr hwx⟩
      rw [hAbot, Subgroup.mem_bot] at hwA
      exact hw1 hwA
    obtain ⟨a, haA, ha1, hta⟩ := exists_fixed_of_inverting hAc hzA htA htbt (htbE zb hzb)
      (hEb3 zb hzb) hfixA hAne
    obtain ⟨haW, haC⟩ := Subgroup.mem_inf.mp haA
    exact ⟨a, haW, ha1, Subgroup.mem_centralizer_singleton_iff.mp haC, hta⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle3 : ∀ y : X ⧸ Φ, y ^ 3 = 1 → Nat.card (Subgroup.zpowers y) ≤ 3 := fun y hy => by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hy
  have hnot12 : y₂ ∉ Subgroup.zpowers y₁ := by
    intro h
    have hle : Eb ≤ Subgroup.zpowers y₁ := by
      rw [hEbeq]
      exact sup_le le_rfl (Subgroup.zpowers_le.mpr h)
    have := (Subgroup.card_le_of_le hle).trans (hle3 y₁ hy13)
    omega
  have hnot21 : y₁ ∉ Subgroup.zpowers y₂ := by
    intro h
    have hle : Eb ≤ Subgroup.zpowers y₂ := by
      rw [hEbeq]
      exact sup_le (Subgroup.zpowers_le.mpr h) le_rfl
    have := (Subgroup.card_le_of_le hle).trans (hle3 y₂ hy23)
    omega
  have hy₁1 : y₁ ≠ 1 := fun h => hnot21 (h ▸ Subgroup.one_mem _)
  have hy₂1 : y₂ ≠ 1 := fun h => hnot12 (h ▸ Subgroup.one_mem _)
  have hy₃E : y₁ * y₂ ∈ Eb := Eb.mul_mem hy₁E hy₂E
  have hy₃1 : y₁ * y₂ ≠ 1 := by
    intro h
    apply hnot12
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y₁)
  have hcard3 : ∀ y ∈ Eb, y ≠ 1 → Nat.card (Subgroup.zpowers y) = 3 := fun y hy hy1 => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hEb3 y hy) hy1
  let i₁ : {D : Subgroup (X ⧸ Φ) // D ≤ Eb ∧ Nat.card D = 3} :=
    ⟨Subgroup.zpowers y₁, Subgroup.zpowers_le.mpr hy₁E, hcard3 y₁ hy₁E hy₁1⟩
  let i₂ : {D : Subgroup (X ⧸ Φ) // D ≤ Eb ∧ Nat.card D = 3} :=
    ⟨Subgroup.zpowers y₂, Subgroup.zpowers_le.mpr hy₂E, hcard3 y₂ hy₂E hy₂1⟩
  let i₃ : {D : Subgroup (X ⧸ Φ) // D ≤ Eb ∧ Nat.card D = 3} :=
    ⟨Subgroup.zpowers (y₁ * y₂), Subgroup.zpowers_le.mpr hy₃E, hcard3 _ hy₃E hy₃1⟩
  have h12' : i₁ ≠ i₂ := by
    intro h
    apply hnot12
    have h' : Subgroup.zpowers y₁ = Subgroup.zpowers y₂ := congrArg Subtype.val h
    rw [h']
    exact Subgroup.mem_zpowers y₂
  have h13' : i₁ ≠ i₃ := by
    intro h
    apply hnot12
    have h' : Subgroup.zpowers y₁ = Subgroup.zpowers (y₁ * y₂) := congrArg Subtype.val h
    have h3 : y₁ * y₂ ∈ Subgroup.zpowers y₁ := h' ▸ Subgroup.mem_zpowers (y₁ * y₂)
    have e : y₂ = y₁⁻¹ * (y₁ * y₂) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y₁)) h3
  have h23' : i₂ ≠ i₃ := by
    intro h
    apply hnot21
    have h' : Subgroup.zpowers y₂ = Subgroup.zpowers (y₁ * y₂) := congrArg Subtype.val h
    have h3 : y₁ * y₂ ∈ Subgroup.zpowers y₂ := h' ▸ Subgroup.mem_zpowers (y₁ * y₂)
    have e : y₁ = (y₁ * y₂) * y₂⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ (Subgroup.mem_zpowers y₂))
  obtain ⟨w₁, hw₁W, hw₁1, hw₁c, hw₁t⟩ := hS3 y₁ y₂ hy₁E hy₂E hy₁1 fun a h1 h2 => ⟨h1, h2⟩
  obtain ⟨w₂, hw₂W, hw₂1, hw₂c, hw₂t⟩ := hS3 y₂ y₁ hy₂E hy₁E hy₂1 fun a h1 h2 => ⟨h2, h1⟩
  obtain ⟨w₃, hw₃W, hw₃1, hw₃c, hw₃t⟩ := hS3 (y₁ * y₂) y₁ hy₃E hy₁E hy₃1 fun a h1 h2 => by
    refine ⟨h2, ?_⟩
    have hc : Commute a (y₁⁻¹ * (y₁ * y₂)) :=
      (show Commute a y₁ from h2).inv_right.mul_right (show Commute a (y₁ * y₂) from h1)
    rw [show y₁⁻¹ * (y₁ * y₂) = y₂ by group] at hc
    exact hc.eq
  set f := fun D : {D : Subgroup (X ⧸ Φ) // D ≤ Eb ∧ Nat.card D = 3} =>
    W ⊓ Subgroup.centralizer ((D : Subgroup (X ⧸ Φ)) : Set (X ⧸ Φ)) with hf
  have hw₁f : w₁ ∈ f i₁ := Subgroup.mem_inf.mpr ⟨hw₁W, mem_centralizer_zpowers_of_commute hw₁c⟩
  have hw₂f : w₂ ∈ f i₂ := Subgroup.mem_inf.mpr ⟨hw₂W, mem_centralizer_zpowers_of_commute hw₂c⟩
  have hw₃f : w₃ ∈ f i₃ := Subgroup.mem_inf.mpr ⟨hw₃W, mem_centralizer_zpowers_of_commute hw₃c⟩
  have hdisj1 : Disjoint (f i₁) (f i₂ ⊔ f i₃) := by
    have h := hind.disjoint_biSup (x := i₁) (y := {i₂, i₃}) (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h12', h13'⟩)
    rwa [iSup_insert, iSup_singleton] at h
  have hdisj2 : Disjoint (f i₂) (f i₃) := hind.pairwiseDisjoint h23'
  have hord : ∀ w ∈ W, w ≠ 1 → orderOf w = r := fun w hw hw1 =>
    orderOf_eq_prime (hVexp w (hWV hw)) hw1
  have hlift : ∀ w ∈ W, tb * w * tb⁻¹ = w → ∃ u ∈ D ⊓ Subgroup.centralizer {t}, π u = w := by
    intro w hwW hwt
    obtain ⟨u₀, hu₀, rfl⟩ := hWV hwW
    have hfix0 : u₀⁻¹ * (t * u₀ * t⁻¹) ∈ Φ := by
      rw [← hπker, map_mul, map_inv, map_mul, map_mul, map_inv, ← htb, hwt, inv_mul_cancel]
    obtain ⟨u, huD, hu₀u, htu⟩ := exists_lift_fixed hD hr2 ht2 hu₀ hfix0
    refine ⟨u, Subgroup.mem_inf.mpr ⟨huD, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, ?_⟩
    · calc u * t = t * u * t⁻¹ * t := by rw [htu]
        _ = t * u := by group
    · have h := (hπker _).mpr hu₀u
      rw [map_mul, map_inv, inv_mul_eq_one] at h
      exact h.symm
  obtain ⟨u₁, hu₁P, hu₁⟩ := hlift w₁ hw₁W hw₁t
  obtain ⟨u₂, hu₂P, hu₂⟩ := hlift w₂ hw₂W hw₂t
  obtain ⟨u₃, hu₃P, hu₃⟩ := hlift w₃ hw₃W hw₃t
  set P := D ⊓ Subgroup.centralizer {t} with hP
  refine three_le_pRank_of_card_map hD inf_le_left ?_
  have hmemF : ∀ a b c : ℕ, w₁ ^ a * (w₂ ^ b * w₃ ^ c) ∈ P.map π := fun a b c =>
    ⟨u₁ ^ a * (u₂ ^ b * u₃ ^ c), P.mul_mem (P.pow_mem hu₁P a)
      (P.mul_mem (P.pow_mem hu₂P b) (P.pow_mem hu₃P c)), by
      rw [map_mul, map_mul, map_pow, map_pow, map_pow, hu₁, hu₂, hu₃]⟩
  let F : Fin r × Fin r × Fin r → P.map π := fun abc =>
    ⟨w₁ ^ (abc.1 : ℕ) * (w₂ ^ (abc.2.1 : ℕ) * w₃ ^ (abc.2.2 : ℕ)), hmemF _ _ _⟩
  have hFinj : Function.Injective F := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    have h' : w₁ ^ (a : ℕ) * (w₂ ^ (b : ℕ) * w₃ ^ (c : ℕ)) =
        w₁ ^ (a' : ℕ) * (w₂ ^ (b' : ℕ) * w₃ ^ (c' : ℕ)) := congrArg Subtype.val h
    obtain ⟨ha, hbc⟩ := eq_and_eq_of_mul_eq hdisj1 ((f i₁).pow_mem hw₁f _)
      ((f i₁).pow_mem hw₁f _)
      ((f i₂ ⊔ f i₃).mul_mem (Subgroup.mem_sup_left ((f i₂).pow_mem hw₂f _))
        (Subgroup.mem_sup_right ((f i₃).pow_mem hw₃f _)))
      ((f i₂ ⊔ f i₃).mul_mem (Subgroup.mem_sup_left ((f i₂).pow_mem hw₂f _))
        (Subgroup.mem_sup_right ((f i₃).pow_mem hw₃f _))) h'
    obtain ⟨hb, hc⟩ := eq_and_eq_of_mul_eq hdisj2 ((f i₂).pow_mem hw₂f _)
      ((f i₂).pow_mem hw₂f _) ((f i₃).pow_mem hw₃f _) ((f i₃).pow_mem hw₃f _) hbc
    have e1 : (a : ℕ) = a' := pow_injOn_Iio_orderOf
      (show (a : ℕ) ∈ Set.Iio (orderOf w₁) by rw [hord w₁ hw₁W hw₁1]; exact a.2)
      (show (a' : ℕ) ∈ Set.Iio (orderOf w₁) by rw [hord w₁ hw₁W hw₁1]; exact a'.2) ha
    have e2 : (b : ℕ) = b' := pow_injOn_Iio_orderOf
      (show (b : ℕ) ∈ Set.Iio (orderOf w₂) by rw [hord w₂ hw₂W hw₂1]; exact b.2)
      (show (b' : ℕ) ∈ Set.Iio (orderOf w₂) by rw [hord w₂ hw₂W hw₂1]; exact b'.2) hb
    have e3 : (c : ℕ) = c' := pow_injOn_Iio_orderOf
      (show (c : ℕ) ∈ Set.Iio (orderOf w₃) by rw [hord w₃ hw₃W hw₃1]; exact c.2)
      (show (c' : ℕ) ∈ Set.Iio (orderOf w₃) by rw [hord w₃ hw₃W hw₃1]; exact c'.2) hc
    rw [Fin.ext e1, Fin.ext e2, Fin.ext e3]
  calc r ^ 3 = Nat.card (Fin r × Fin r × Fin r) := by
        rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]
        ring
    _ ≤ Nat.card (P.map π) := Nat.card_le_card_of_injective F hFinj

end Critical

end CFSG.RankThree.PartTwo.Sec13.L3Proof
