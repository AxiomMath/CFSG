module

public import CFSG.Walter.W67.JR.R5
public import CFSG.Walter.W67.JR.Basic
public import CFSG.Walter.JRFacts
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement
open JRBasic

section General

variable {G : Type*} [Group G]

theorem le_commutator_of_fixedPointFree [Finite G] {X Y U : Subgroup G} {g : G} (hgU : g ∈ U)
    (hXY : X ≤ Y) (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hfpf : ∀ x ∈ X, g * x * g⁻¹ = x → x = 1) : X ≤ ⁅U, Y⁆ := by
  have hconj : ∀ x ∈ X, g * x * g⁻¹ ∈ X := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hgX x).mp hx
  let φ : X → X := fun x => ⟨g * x * g⁻¹ * (x : G)⁻¹, X.mul_mem (hconj _ x.2) (X.inv_mem x.2)⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : g * (x : G) * g⁻¹ * (x : G)⁻¹ = g * (y : G) * g⁻¹ * (y : G)⁻¹ :=
      congrArg Subtype.val hxy
    have h2 : g * ((y : G)⁻¹ * x) * g⁻¹ = (y : G)⁻¹ * x := by
      calc g * ((y : G)⁻¹ * x) * g⁻¹
          = (g * (y : G) * g⁻¹)⁻¹ * (g * (x : G) * g⁻¹ * (x : G)⁻¹) * x := by group
        _ = (g * (y : G) * g⁻¹)⁻¹ * (g * (y : G) * g⁻¹ * (y : G)⁻¹) * x := by rw [h1]
        _ = (y : G)⁻¹ * x := by group
    have h3 := hfpf _ (X.mul_mem (X.inv_mem y.2) x.2) h2
    apply Subtype.ext
    rw [← mul_left_cancel_iff (a := (y : G)⁻¹), h3, inv_mul_cancel]
  have hφs : Function.Surjective φ := Finite.injective_iff_surjective.mp hφ
  intro z hz
  obtain ⟨x, hx⟩ := hφs ⟨z, hz⟩
  have : g * (x : G) * g⁻¹ * (x : G)⁻¹ = z := congrArg Subtype.val hx
  rw [← this]
  exact Subgroup.commutator_mem_commutator hgU (hXY x.2)

theorem mem_normalizer_centralizer [Finite G] {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  rw [← JT.conj_smul_eq_iff] at hg ⊢
  rw [← centralizer_conj_smul, hg]

theorem mem_normalizer_zpowers_of_conj_eq_inv [Finite G] {a x : G} (hx : x * a * x⁻¹ = a⁻¹) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  refine JT.conj_smul_eq_iff.mp ?_
  change (Subgroup.zpowers a).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers a
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers (x * a * x⁻¹) = Subgroup.zpowers a
  rw [hx, Subgroup.zpowers_inv]

end General

namespace JRGroup

variable {L : Type} [Group L] [Finite L] (h : JRGroup L)

theorem r4_core
    (hJT : JTThreeHyp) (hq : 5 < h.q) (s : JT.Setup (h.toJTHyp hq)) :
    IsCyclic s.Q ∧ 4 * Nat.card s.Q = h.q + 1 ∧
    Subgroup.centralizer (s.Q : Set L) = s.T ⊔ s.Q ∧
    ∃ (S : Sylow 2 L) (U : Subgroup L), s.T ≤ S ∧
      (∀ a ∈ s.Q, a ≠ 1 → cstarSet a = ((S : Subgroup L) ⊔ s.Q : Subgroup L)) ∧
      Nat.card U = 3 ∧
      Subgroup.normalizer (s.T : Set L) = Subgroup.normalizer (s.Q : Set L) ∧
      Subgroup.normalizer (s.T : Set L) = U ⊔ (S : Subgroup L) ⊔ s.Q ∧
      ⁅U, (S : Subgroup L)⁆ = s.T ∧ ⁅U, s.Q⁆ = s.Q ∧
      s.T ⊔ ((S : Subgroup L) ⊓ Subgroup.centralizer (U : Set L)) = S ∧
      s.T ⊓ Subgroup.centralizer (U : Set L) = ⊥ ∧
      ∀ a ∈ s.Q, a ≠ 1 → Subgroup.centralizer ({a} : Set L) = s.T ⊔ s.Q ∧
        Subgroup.normalizer (Subgroup.zpowers a : Set L) = Subgroup.normalizer (s.Q : Set L) := by
  have hp3 := h.p_eq_three hJT hq
  have hp : (h.toJTHyp hq).p ≠ 2 := h.p_ne_two
  have hS : JT.SuzukiFourGroupTheorem := CFSG.Walter.suzukiFourGroupTheorem
  obtain ⟨hCT, hQc, hQcard, hQ1⟩ := s.lemma_4_2_a hp
  obtain ⟨μ, t₁, hμS, hμT, hμ3, ht₁S, ht₁2, hμt₁, hμfpfT, hNT, ht₁fpf, hNTQ⟩ :=
    s.lemma_4_2_c hp
  have hNQ : Subgroup.normalizer (s.Q : Set L) = Subgroup.normalizer (s.T : Set L) :=
    s.lemma_7_1_b hp3 hS
  have h712 := (h.toJTHyp hq).lemma_7_12_a hp3
  have heps : (h.toJTHyp hq).eps = 1 := (h.toJTHyp hq).eps_eq_one_of_eq_three hp3
  have hQcomm : ∀ a ∈ s.Q, ∀ b ∈ s.Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.commGroup (α := s.Q)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hQodd : ∀ a ∈ s.Q, Odd (orderOf a) := fun a ha => ((s.mem_Q_iff hp).mp ha).2
  obtain ⟨a₀, ha₀Q, ha₀1⟩ : ∃ a ∈ s.Q, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hQ1
    have : s.Q = ⊥ := eq_bot_iff.mpr fun x hx => hcon x hx
    rw [this, Subgroup.card_bot]
  have hTQ : s.T ≤ Subgroup.centralizer (s.Q : Set L) := s.T_le_centralizer_Q
  have hTconj : ∀ v ∈ s.T, ∀ y ∈ s.Q, v * y * v⁻¹ = y := fun v hv y hy => by
    rw [← (Subgroup.mem_centralizer_iff.mp (hTQ hv)) y hy, mul_inv_cancel_right]
  have hSinv : ∀ x ∈ (s.S : Subgroup L), x ∉ s.T → ∀ y ∈ s.Q, x * y * x⁻¹ = y⁻¹ :=
    fun x hx hxT y hy => s.conj_eq_inv_of_mem_S hp hx hxT hy
  have hNQ' : Subgroup.normalizer (s.T : Set L) ≤ Subgroup.normalizer (s.Q : Set L) := hNTQ
  have hconjQ : ∀ g ∈ Subgroup.normalizer (s.Q : Set L), ∀ y ∈ s.Q, g * y * g⁻¹ ∈ s.Q :=
    fun g hg y hy => (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  have hCTN : Subgroup.centralizer (s.T : Set L) ≤ Subgroup.normalizer (s.T : Set L) :=
    Subgroup.centralizer_le_normalizer _
  have hSN : (s.S : Subgroup L) ≤ Subgroup.normalizer (s.Q : Set L) :=
    (hCT ▸ le_sup_left : (s.S : Subgroup L) ≤ Subgroup.centralizer (s.T : Set L)).trans
      (hCTN.trans hNQ')
  have hUN : Subgroup.zpowers μ ≤ Subgroup.normalizer (s.Q : Set L) :=
    Subgroup.zpowers_le.mpr (hNQ' hμT)
  have hfpf : ∀ ν ∈ Subgroup.zpowers μ, ν ≠ 1 → ∀ y ∈ s.Q, ν * y * ν⁻¹ = y → y = 1 := by
    intro ν hν hν1 y hy hνy
    have hν3 : ν ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hν
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hμ3,
        pow_orderOf_eq_one, one_zpow]
    have hνo : orderOf ν = 3 := orderOf_eq_prime hν3 hν1
    refine h712 s ν (hUN hν) hνo y hy ?_
    calc ν * y = (ν * y * ν⁻¹) * ν := by group
      _ = y * ν := by rw [hνy]
  have hsq : ∀ ν ∈ Subgroup.zpowers μ, ν ≠ 1 → ν * ν ≠ 1 := by
    intro ν hν hν1 hνν
    have hν3 : ν ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hν
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hμ3,
        pow_orderOf_eq_one, one_zpow]
    apply hν1
    calc ν = ν ^ 3 * (ν * ν)⁻¹ := by group
      _ = 1 := by rw [hν3, hνν, inv_one, mul_one]
  have hμCT : Subgroup.zpowers μ ≤
      Subgroup.normalizer ((Subgroup.centralizer (s.T : Set L) : Subgroup L) : Set L) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_centralizer hμT)
  have hdec : ∀ x ∈ Subgroup.normalizer (s.T : Set L), ∃ b ∈ s.Q, ∃ s' ∈ (s.S : Subgroup L),
      ∃ e ∈ Subgroup.zpowers μ, x = b * s' * e := by
    intro x hx
    rw [hNT, sup_comm] at hx
    obtain ⟨c, hc, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hμCT).mp hx
    rw [hCT, sup_comm] at hc
    obtain ⟨b, hb, s', hs', rfl⟩ := (mem_sup_iff_of_le_normalizer hSN).mp hc
    exact ⟨b, hb, s', hs', e, he, rfl⟩
  have hkey : ∀ x ∈ Subgroup.normalizer (s.T : Set L), ∀ a ∈ s.Q, a ≠ 1 →
      (x * a * x⁻¹ = a → x ∈ s.T ⊔ s.Q) ∧
        (x * a * x⁻¹ = a⁻¹ → x ∈ (s.S : Subgroup L) ⊔ s.Q) := by
    intro x hx a haQ ha1
    obtain ⟨b, hb, s', hs', e, he, rfl⟩ := hdec x hx
    have hne : a⁻¹ ≠ a := inv_ne_self_of_odd (hQodd a haQ) ha1
    set a₁ := e * a * e⁻¹ with ha₁
    have ha₁Q : a₁ ∈ s.Q := hconjQ e (hUN he) a haQ
    have hconj : b * s' * e * a * (b * s' * e)⁻¹ = b * (s' * a₁ * s'⁻¹) * b⁻¹ := by
      rw [ha₁]; group
    have hb' : ∀ y ∈ s.Q, b * y * b⁻¹ = y := fun y hy => by
      rw [hQcomm b hb y hy, mul_inv_cancel_right]
    by_cases he1 : e = 1
    · subst he1
      have ha₁a : a₁ = a := by rw [ha₁]; group
      rw [ha₁a] at hconj
      refine ⟨fun h1 => ?_, fun _ => ?_⟩
      · by_cases hsT : s' ∈ s.T
        · rw [mul_one]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left hsT)
        · exfalso
          rw [hconj, hSinv s' hs' hsT a haQ, hb' _ (s.Q.inv_mem haQ)] at h1
          exact hne h1
      · rw [mul_one]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left hs')
    · have he2 := hsq e he he1
      have hee : e * e ∈ Subgroup.zpowers μ := Subgroup.mul_mem _ he he
      have hfix1 : a₁ ≠ a := fun h1 => ha1 (hfpf e he he1 a haQ h1)
      have hfix2 : a₁ ≠ a⁻¹ := by
        intro h1
        apply ha1
        refine hfpf (e * e) hee he2 a haQ ?_
        calc e * e * a * (e * e)⁻¹ = e * (e * a * e⁻¹) * e⁻¹ := by group
          _ = e * a⁻¹ * e⁻¹ := by rw [← ha₁, h1]
          _ = (e * a * e⁻¹)⁻¹ := by group
          _ = a := by rw [← ha₁, h1, inv_inv]
      have hval : b * s' * e * a * (b * s' * e)⁻¹ = a₁ ∨
          b * s' * e * a * (b * s' * e)⁻¹ = a₁⁻¹ := by
        rw [hconj]
        by_cases hsT : s' ∈ s.T
        · left
          rw [hTconj s' hsT a₁ ha₁Q, hb' a₁ ha₁Q]
        · right
          rw [hSinv s' hs' hsT a₁ ha₁Q, hb' _ (s.Q.inv_mem ha₁Q)]
      refine ⟨fun h1 => ?_, fun h1 => ?_⟩
      · exfalso
        rcases hval with h2 | h2 <;> rw [h1] at h2
        · exact hfix1 h2.symm
        · exact hfix2 (by rw [h2, inv_inv])
      · exfalso
        rcases hval with h2 | h2 <;> rw [h1] at h2
        · exact hfix2 h2.symm
        · exact hfix1 (inv_injective h2.symm)
  have ht₁T : t₁ ∉ s.T := fun ht => ha₀1 (ht₁fpf a₀ ha₀Q (hTconj t₁ ht a₀ ha₀Q))
  have hSab : ∀ x ∈ (s.S : Subgroup L), ∀ y ∈ (s.S : Subgroup L), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val
      ((h.elementary_sylow s.S).toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hTt₁ : s.T ⊔ Subgroup.zpowers t₁ = s.S := by
    have hle : s.T ⊔ Subgroup.zpowers t₁ ≤ s.S := sup_le s.le_S (Subgroup.zpowers_le.mpr ht₁S)
    have hc : ∀ x ∈ s.T, ∀ y ∈ Subgroup.zpowers t₁, x * y = y * x := fun x hx y hy =>
      hSab x (s.le_S hx) y ((Subgroup.zpowers_le.mpr ht₁S) hy)
    obtain ⟨hcard, -⟩ := card_sup_mul_card_inf_of_commute _ _ hc
    have hd : s.T ⊓ Subgroup.zpowers t₁ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases eq_one_or_eq_of_mem_zpowers ht₁2 hx.2 with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hx.1) ht₁T
    rw [hd, Subgroup.card_bot, mul_one, Nat.card_zpowers, ht₁2, s.four.card_four] at hcard
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h.card_sylow s.S])
  have hμt₁' : ∀ u ∈ Subgroup.zpowers μ, u * t₁ = t₁ * u := fun u hu => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (Commute.zpow_left hμt₁ k).eq
  have hμT' : Subgroup.zpowers μ ≤ Subgroup.normalizer (s.T : Set L) :=
    Subgroup.zpowers_le.mpr hμT
  have hCQ : Subgroup.centralizer (s.Q : Set L) = s.T ⊔ s.Q := by
    apply le_antisymm
    · intro x hx
      have hxN : x ∈ Subgroup.normalizer (s.T : Set L) := by
        rw [← hNQ]
        exact Subgroup.centralizer_le_normalizer _ hx
      refine (hkey x hxN a₀ ha₀Q ha₀1).1 ?_
      rw [← (Subgroup.mem_centralizer_iff.mp hx) a₀ ha₀Q, mul_inv_cancel_right]
    · exact sup_le hTQ fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hQcomm y hy x hx
  refine ⟨hQc, ?_, hCQ, s.S, Subgroup.zpowers μ, s.le_S, ?_, ?_, hNQ.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := hQcard
    rw [heps, show (h.toJTHyp hq).q = h.q from rfl] at h1
    have h2 : ((4 * Nat.card s.Q : ℕ) : ℤ) = ((h.q + 1 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast h2
  ·
    intro a ha ha1
    ext x
    constructor
    · intro hx
      have hxN : x ∈ Subgroup.normalizer (s.T : Set L) := by
        rw [← hNQ, ← s.lemma_4_3 hp hS (Subgroup.zpowers_le.mpr ha) (by
          rw [Ne, Subgroup.zpowers_eq_bot]; exact ha1)]
        rcases hx with h1 | h1
        · exact JT.mem_normalizer_zpowers_of_commute (by
            calc x * a = (x * a * x⁻¹) * x := by group
              _ = a * x := by rw [h1])
        · exact mem_normalizer_zpowers_of_conj_eq_inv h1
      rcases hx with h1 | h1
      · exact (sup_le_sup_right s.le_S _) ((hkey x hxN a ha ha1).1 h1)
      · exact (hkey x hxN a ha ha1).2 h1
    · intro hx
      have hx' : x ∈ s.Q ⊔ (s.S : Subgroup L) := by rw [sup_comm]; exact hx
      obtain ⟨b, hb, s', hs', rfl⟩ := (mem_sup_iff_of_le_normalizer hSN).mp hx'
      have hb' : ∀ y ∈ s.Q, b * y * b⁻¹ = y := fun y hy => by
        rw [hQcomm b hb y hy, mul_inv_cancel_right]
      by_cases hsT : s' ∈ s.T
      · left
        rw [show b * s' * a * (b * s')⁻¹ = b * (s' * a * s'⁻¹) * b⁻¹ by group,
          hTconj s' hsT a ha, hb' a ha]
      · right
        rw [show b * s' * a * (b * s')⁻¹ = b * (s' * a * s'⁻¹) * b⁻¹ by group,
          hSinv s' hs' hsT a ha, hb' _ (s.Q.inv_mem ha)]
  · rw [Nat.card_zpowers, hμ3]
  ·
    rw [hNT, hCT, sup_assoc]
  ·
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro u hu x hx
      rw [← hTt₁] at hx
      have hset := (card_sup_mul_card_inf_of_commute s.T (Subgroup.zpowers t₁) fun v hv y hy =>
        hSab v (s.le_S hv) y ((Subgroup.zpowers_le.mpr ht₁S) hy)).2
      have hx' : x ∈ ((s.T ⊔ Subgroup.zpowers t₁ : Subgroup L) : Set L) := hx
      rw [hset] at hx'
      obtain ⟨v, hv, w, hw, hvw⟩ := hx'
      simp only at hvw
      subst hvw
      have huw : u * w = w * u := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact (Commute.zpow_right (hμt₁' u hu : Commute u t₁) k).eq
      have hvw : v * w = w * v := hSab v (s.le_S hv) w ((Subgroup.zpowers_le.mpr ht₁S) hw)
      have hwu : w * u⁻¹ = u⁻¹ * w := by
        calc w * u⁻¹ = u⁻¹ * (u * w) * u⁻¹ := by group
          _ = u⁻¹ * (w * u) * u⁻¹ := by rw [huw]
          _ = u⁻¹ * w := by group
      have hc : ⁅u, v * w⁆ = u * v * u⁻¹ * v⁻¹ := by
        rw [commutatorElement_def]
        calc u * (v * w) * u⁻¹ * (v * w)⁻¹ = u * v * (w * u⁻¹) * w⁻¹ * v⁻¹ := by group
          _ = u * v * (u⁻¹ * w) * w⁻¹ * v⁻¹ := by rw [hwu]
          _ = u * v * u⁻¹ * v⁻¹ := by group
      rw [hc]
      exact s.T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hμT' hu) v).mp hv) (s.T.inv_mem hv)
    · exact le_commutator_of_fixedPointFree (Subgroup.mem_zpowers μ) s.le_S hμT hμfpfT
  ·
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro u hu b hb
      rw [commutatorElement_def]
      exact s.Q.mul_mem (hconjQ u (hUN hu) b hb) (s.Q.inv_mem hb)
    · refine le_commutator_of_fixedPointFree (Subgroup.mem_zpowers μ) le_rfl (hNQ' hμT) ?_
      intro x hx hμx
      refine hfpf μ (Subgroup.mem_zpowers μ) ?_ x hx hμx
      intro h0
      rw [h0, orderOf_one] at hμ3
      omega
  ·
    apply le_antisymm (sup_le s.le_S inf_le_left)
    calc (s.S : Subgroup L) = s.T ⊔ Subgroup.zpowers t₁ := hTt₁.symm
      _ ≤ s.T ⊔ ((s.S : Subgroup L) ⊓ Subgroup.centralizer (Subgroup.zpowers μ : Set L)) :=
        sup_le_sup_left (Subgroup.zpowers_le.mpr
          (Subgroup.mem_inf.mpr
            ⟨ht₁S, Subgroup.mem_centralizer_iff.mpr fun u hu => hμt₁' u hu⟩)) _
  ·
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxC⟩
    refine hμfpfT x hxT ?_
    rw [(Subgroup.mem_centralizer_iff.mp hxC) μ (Subgroup.mem_zpowers μ), mul_inv_cancel_right]
  ·
    intro a ha ha1
    have hN := s.lemma_4_3 hp hS (Subgroup.zpowers_le.mpr ha) (by
      rw [Ne, Subgroup.zpowers_eq_bot]; exact ha1)
    refine ⟨le_antisymm ?_ ?_, hN⟩
    · intro x hx
      have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hx
      have hxN : x ∈ Subgroup.normalizer (s.T : Set L) := by
        rw [← hNQ, ← hN]
        exact JT.mem_normalizer_zpowers_of_commute hxa
      refine (hkey x hxN a ha ha1).1 ?_
      rw [hxa, mul_inv_cancel_right]
    · rw [← hCQ]
      exact Subgroup.centralizer_le (by simpa using ha)

theorem r4
    (hJT : JTThreeHyp) (hq5 : h.q ≠ 5) : h.R4 := by
  intro hq3 t htK ht2
  have hq := h.five_lt_q hq5 hq3
  have hp : (h.toJTHyp hq).p ≠ 2 := h.p_ne_two
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    omega
  have hJt : Commute h.J t := (h.commute_J_of_mem_K htK).symm
  have hJt' : h.J ≠ t := fun h0 => h.J_not_mem (h0 ▸ htK)
  set V₀ := GorensteinWalter.kleinFourOfCommutingInvolutions h.J t h.J_mul_J htt hJt with hV₀def
  have hV₀ : IsKleinFour V₀ := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    _ _ _ _ h.J_ne_one ht1 hJt' hJt
  have hmem : ∀ x, x ∈ V₀ ↔ x = h.J * t ∨ x = h.J ∨ x = t ∨ x = 1 := fun x => Iff.rfl
  have hJV : h.J ∈ V₀ := (hmem _).mpr (Or.inr (Or.inl rfl))
  have htV : t ∈ V₀ := (hmem _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hcl : Subgroup.closure ({h.J, t} : Set L) = V₀ := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hJV
      · exact htV
    · intro x hx
      have hJ' : h.J ∈ Subgroup.closure ({h.J, t} : Set L) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have ht' : t ∈ Subgroup.closure ({h.J, t} : Set L) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      rcases (hmem x).mp hx with rfl | rfl | rfl | rfl
      · exact Subgroup.mul_mem _ hJ' ht'
      · exact hJ'
      · exact ht'
      · exact Subgroup.one_mem _
  have hV2 : IsPGroup 2 V₀ := IsPGroup.of_card (n := 2) (by rw [hV₀.card_four]; norm_num)
  obtain ⟨S, hVS⟩ := hV2.exists_le_sylow
  let s : JT.Setup (h.toJTHyp hq) := ⟨S, hVS hJV, V₀, hVS, hV₀, hJV⟩
  have hX : h.K ⊓ Subgroup.centralizer ({t} : Set L) ≤ Subgroup.centralizer (s.T : Set L) := by
    rintro x ⟨hxK, hxt⟩
    have h1 : x * h.J = h.J * x := h.commute_J_of_mem_K hxK
    have h2 : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxt
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases (hmem y).mp hy with rfl | rfl | rfl | rfl
    · calc h.J * t * x = h.J * (x * t) := by rw [mul_assoc, h2]
        _ = x * (h.J * t) := by rw [← mul_assoc, ← h1, mul_assoc]
    · exact h1.symm
    · exact h2.symm
    · rw [one_mul, mul_one]
  have hAQ : oddPart (h.K ⊓ Subgroup.centralizer ({t} : Set L)) = s.Q := by
    set X := h.K ⊓ Subgroup.centralizer ({t} : Set L) with hXdef
    apply le_antisymm
    · intro x hx
      exact (s.mem_Q_iff hp).mpr ⟨hX (oddPart_le _ hx), odd_orderOf_of_mem_oddPart hx⟩
    · have hQX : s.Q ≤ X := fun y hy => ⟨s.Q_le_F hp hy, Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp (s.Q_le_centralizer_T hy)) t htV).symm⟩
      have hnorm : (s.Q.subgroupOf X).Normal := by
        refine ⟨fun n hn g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        obtain ⟨hnC, hnodd⟩ := (s.mem_Q_iff hp).mp hn
        refine (s.mem_Q_iff hp).mpr ⟨?_, ?_⟩
        · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hX g.2) hnC)
            (Subgroup.inv_mem _ (hX g.2))
        · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [orderOf_conj_mul]
          exact hnodd
      have hcop : Nat.Coprime 2 (Nat.card (s.Q.subgroupOf X)) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv]
        exact Nat.coprime_two_left.mpr (s.odd_card_Q hp)
      have hle : s.Q.subgroupOf X ≤ CFSG.pPrimeCore 2 X := le_sSup ⟨hnorm, hcop⟩
      intro y hy
      exact Subgroup.mem_map.mpr ⟨⟨y, hQX hy⟩, hle (by rw [Subgroup.mem_subgroupOf]; exact hy),
        rfl⟩
  intro A V
  have hVeq : V = s.T := hcl
  have hAeq : A = s.Q := hAQ
  rw [hVeq, hAeq]
  exact h.r4_core hJT hq s

end JRGroup

end CFSG.Walter.W67
