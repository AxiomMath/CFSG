module

public import CFSG.RankThree.GF2n.Parrott.Lemma13Structure
import CFSG.RankThree.GF2n.Parrott.Lemma13Representative

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem commute_of_mem_zpowers_of_mem_H {g d : G} (hg : g ∈ H z) (hd : d ∈ Subgroup.zpowers z) :
    g * d = d * g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
  have hgz : Commute g z := Subgroup.mem_centralizer_singleton_iff.mp hg
  exact (hgz.zpow_right k).eq

theorem card_le_two_mul_card_inf_centralizer_of_mem_zpowers (hz : orderOf z = 2)
    {B : Subgroup G} (hBH : B ≤ H z) {w : G} (hwH : w ∈ H z)
    (hBw : ∀ b ∈ B, b * w * b⁻¹ * w⁻¹ ∈ Subgroup.zpowers z) :
    Nat.card B ≤ 2 * Nat.card (B ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) := by
  let f : ↥B →* G := MonoidHom.mk' (fun b => (b : G) * w * (b : G)⁻¹ * w⁻¹) (fun a b => by
    set d := (b : G) * w * (b : G)⁻¹ * w⁻¹ with hd
    have hdz : d ∈ Subgroup.zpowers z := hBw b b.2
    have had : (a : G) * d = d * a := commute_of_mem_zpowers_of_mem_H (hBH a.2) hdz
    have hxH : (a : G) * w * (a : G)⁻¹ * w⁻¹ ∈ H z :=
      (H z).mul_mem ((H z).mul_mem ((H z).mul_mem (hBH a.2) hwH)
        ((H z).inv_mem (hBH a.2))) ((H z).inv_mem hwH)
    have hdx := commute_of_mem_zpowers_of_mem_H hxH hdz
    have hbw : (b : G) * w * (b : G)⁻¹ = d * w := by rw [hd]; group
    change (a : G) * b * w * ((a : G) * b)⁻¹ * w⁻¹ =
      ((a : G) * w * (a : G)⁻¹ * w⁻¹) * ((b : G) * w * (b : G)⁻¹ * w⁻¹)
    calc (a : G) * b * w * ((a : G) * b)⁻¹ * w⁻¹
        = (a : G) * ((b : G) * w * (b : G)⁻¹) * (a : G)⁻¹ * w⁻¹ := by group
      _ = (a : G) * (d * w) * (a : G)⁻¹ * w⁻¹ := by rw [hbw]
      _ = ((a : G) * d) * w * (a : G)⁻¹ * w⁻¹ := by group
      _ = (d * a) * w * (a : G)⁻¹ * w⁻¹ := by rw [had]
      _ = d * ((a : G) * w * (a : G)⁻¹ * w⁻¹) := by group
      _ = ((a : G) * w * (a : G)⁻¹ * w⁻¹) * d := hdx.symm
      _ = ((a : G) * w * (a : G)⁻¹ * w⁻¹) * ((b : G) * w * (b : G)⁻¹ * w⁻¹) := by rw [hd])
  have hker : f.ker.map B.subtype = B ⊓ Subgroup.centralizer ({w} : Set G) := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b.2, ?_⟩
      have h1 : (b : G) * w * (b : G)⁻¹ * w⁻¹ = 1 := hb
      calc (b : G) * w = (b : G) * w * (b : G)⁻¹ * w⁻¹ * (w * b) := by group
        _ = w * b := by rw [h1, one_mul]
    · rintro ⟨hgB, hgw⟩
      refine ⟨⟨g, hgB⟩, ?_, rfl⟩
      change g * w * g⁻¹ * w⁻¹ = 1
      rw [hgw]
      group
  have hkercard : Nat.card f.ker =
      Nat.card (B ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) := by
    rw [← hker, Subgroup.card_map_of_injective B.subtype_injective]
  have hrange : Nat.card f.range ≤ 2 := by
    have hle : f.range ≤ Subgroup.zpowers z := by
      intro g hg
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hg
      exact hBw b b.2
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, hz] at this
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hkercard] at hmul
  calc Nat.card B = Nat.card (B ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) *
        Nat.card f.range := hmul.symm
    _ ≤ Nat.card (B ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) * 2 :=
        Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card (B ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) := mul_comm _ _

theorem exists_not_commute_of_le_J_of_card (h : Tim79a.ParrottHyp z) {M : Subgroup G}
    (hMJ : M ≤ J z) (hM : 64 ≤ Nat.card M)
    (hZ : ∀ a ∈ M, (∀ b ∈ M, a * b = b * a) → a ∈ centerIn (J z)) {x : G} (hxH : x ∈ H z)
    (hMx : ∀ m ∈ M, m * x * m⁻¹ * x⁻¹ ∈ Subgroup.zpowers z) :
    ∃ a ∈ M, ∃ b ∈ M, a * x = x * a ∧ b * x = x * b ∧ a * b ≠ b * a := by
  have hz : orderOf z = 2 := h.1
  have hJc : ∀ a ∈ J z, ∀ b ∈ J z, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := by
    intro a ha b hb
    have hJcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := by
      obtain ⟨-, -, hcomm, -, -⟩ := h
      simpa [J, H] using hcomm
    have hmem : ⁅a, b⁆ ∈ ⁅J z, J z⁆ := Subgroup.commutator_mem_commutator ha hb
    rwa [hJcomm, commutatorElement_def] at hmem
  have hMH : M ≤ H z := hMJ.trans J_le_H
  set A := M ⊓ Subgroup.centralizer ({x} : Set G) with hA
  by_contra hcon
  push Not at hcon
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    hcon a ha.1 b hb.1 (Subgroup.mem_centralizer_singleton_iff.mp ha.2)
      (Subgroup.mem_centralizer_singleton_iff.mp hb.2)
  have hAJ : A ≤ J z := inf_le_left.trans hMJ
  have hMA : Nat.card M ≤ 2 * Nat.card A :=
    card_le_two_mul_card_inf_centralizer_of_mem_zpowers hz hMH hxH hMx
  have hZcard : Nat.card (centerIn (J z)) = 4 := card_centerIn_J h
  have hAM : ∃ w ∈ M, w ∉ A := by
    by_contra hall
    push Not at hall
    have hle : M ≤ centerIn (J z) := fun a ha =>
      hZ a ha (fun d hd => hAab a (hall a ha) d (hall d hd))
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨w, hwM, hwA⟩ := hAM
  set Aw := A ⊓ Subgroup.centralizer ({w} : Set G) with hAw
  have hAw2 : Nat.card A ≤ 2 * Nat.card Aw :=
    card_le_two_mul_card_inf_centralizer_of_mem_zpowers hz (hAJ.trans J_le_H)
      (J_le_H (hMJ hwM)) (fun a ha => hJc a (hAJ ha) w (hMJ hwM))
  have hsup : A ⊔ Subgroup.zpowers w = M := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left (Subgroup.zpowers_le.mpr hwM))
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (le_sup_left : A ≤ A ⊔ Subgroup.zpowers w)
    have hm1 : m ≠ 1 := by
      rintro rfl
      apply hwA
      rw [Subgroup.eq_of_le_of_card_ge (le_sup_left : A ≤ A ⊔ Subgroup.zpowers w)
        (by rw [hm, mul_one])]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    have hm0 : m ≠ 0 := by
      rintro rfl
      have hpos : 0 < Nat.card (A ⊔ Subgroup.zpowers w : Subgroup G) := Nat.card_pos
      omega
    rw [hm]
    have : 2 ≤ m := by omega
    nlinarith
  have hAwZ : Aw ≤ centerIn (J z) := by
    intro a ha
    apply hZ a ha.1.1
    intro d hd
    have hle : A ⊔ Subgroup.zpowers w ≤ Subgroup.centralizer ({a} : Set G) := by
      apply sup_le
      · intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hAab a ha.1 b hb).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp ha.2).symm
    have hd' := hle (by rw [hsup]; exact hd)
    rw [Subgroup.mem_centralizer_singleton_iff] at hd'
    exact hd'.symm
  have := Subgroup.card_le_of_le hAwZ
  omega


theorem commutator_le_J_of_le_centralizer_sigma1Nine_mul_inv [hN : ((J z).subgroupOf (H z)).Normal]
    (D : QuotientData (z := z) hN) {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) {S : Subgroup G}
    (hSH : S ≤ H z)
    (hSσ : S ≤ Subgroup.centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hS2 : IsPGroup 2 S) : ⁅S, S⁆ ≤ J z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥S →* QA45.originalSubgroup := (qH D).comp (Subgroup.inclusion hSH)
  have hqσ : qH D (sigma1Nine (z := z) D * σ₂⁻¹) =
      (⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩ : QA45.originalSubgroup) := by
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
    rfl
  have hle : φ.range ≤ Subgroup.centralizer
      ({(⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩ : QA45.originalSubgroup)} :
        Set QA45.originalSubgroup) := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hqσ]
    have hyH : Subgroup.inclusion hSH y * (sigma1Nine (z := z) D * σ₂⁻¹) =
        (sigma1Nine (z := z) D * σ₂⁻¹) * Subgroup.inclusion hSH y :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hSσ y.2))
    change qH D (Subgroup.inclusion hSH y) * qH D (sigma1Nine (z := z) D * σ₂⁻¹) =
      qH D (sigma1Nine (z := z) D * σ₂⁻¹) * qH D (Subgroup.inclusion hSH y)
    rw [← map_mul, ← map_mul, hyH]
  have hdvd : Nat.card φ.range ∣ 108 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [card_centralizer_sigma1_mul_sigma2_inv_QA45] at this
  have hp : IsPGroup 2 φ.range := hS2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hn2 : n ≤ 2 := by
    by_contra hcon
    have h8 : (8 : ℕ) ∣ 108 := by
      have h8n : (8 : ℕ) ∣ 2 ^ n := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
        exact Nat.pow_dvd_pow 2 (by omega)
      exact h8n.trans (by rw [← hn]; exact hdvd)
    omega
  have hcomm : ∀ a b : ↥φ.range, a * b = b * a := by
    interval_cases n
    · have : Subsingleton ↥φ.range := by
        rw [← Finite.card_le_one_iff_subsingleton, hn]
        norm_num
      intro a b
      exact Subsingleton.elim _ _
    · have hc : IsCyclic ↥φ.range := isCyclic_of_prime_card (p := 2) (by rw [hn]; norm_num)
      exact fun a b => (IsCyclic.commutative.is_comm.comm a b)
    · exact IsPGroup.commutative_of_card_eq_prime_sq (p := 2) hn
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hc := hcomm ⟨φ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩⟩ ⟨φ ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩⟩
  have hc' : φ ⟨a, ha⟩ * φ ⟨b, hb⟩ = φ ⟨b, hb⟩ * φ ⟨a, ha⟩ := congrArg Subtype.val hc
  have hone : qH D (Subgroup.inclusion hSH (⁅(⟨a, ha⟩ : ↥S), ⟨b, hb⟩⁆)) = 1 := by
    change φ ⁅(⟨a, ha⟩ : ↥S), ⟨b, hb⟩⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hc']
    group
  have hJ := Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr hone)
  simpa [commutatorElement_def] using hJ

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem exists_sylow_of_mem_tCJ_of_equalityBranch (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j)
    {σ : ↥(H z)} (hσ : σ = sigma1Nine (z := z) D * σ₂⁻¹)
    {t : ↥(H z)} (ht : (tH D)⁻¹ * t ∈ (J z).subgroupOf (H z)) (htσ : t * σ = σ * t) :
    ∀ ⦃x : G⦄, (∃ c ∈ CJ z (σ : G), x = (t : G) * c) → orderOf x = 2 →
      ∃ K : Subgroup G, K ≤ H z ∧
        IsSylowOf 2 K (Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ({(σ : G)} : Set G)) ∧
        z ∈ ⁅K, K⁆ ∧ ⁅K, K⁆ ≤ J z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx hx2
  subst hσ
  have hσ3 : orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3 :=
    orderOf_mul_inv_of_commute_of_hom (qH D) (sigma1Nine_order D) hσ₂ (qH_sigma1Nine D) hq₂ hcomm
  set B : Subgroup G := CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) with hBdef
  have hBJ : B ≤ J z := inf_le_right
  have hzH : ∀ g ∈ H z, ∀ d ∈ Subgroup.zpowers z, g * d = d * g :=
    fun g hg d hd => commute_of_mem_zpowers_of_mem_H hg hd
  have hJc : ∀ a ∈ J z, ∀ b ∈ J z, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := by
    intro a ha b hb
    have hJcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := by
      obtain ⟨-, -, hcomm, -, -⟩ := h
      simpa [J, H] using hcomm
    have hmem : ⁅a, b⁆ ∈ ⁅J z, J z⁆ := Subgroup.commutator_mem_commutator ha hb
    rwa [hJcomm, commutatorElement_def] at hmem
  obtain ⟨t₀, ht₀, ht₀σ, ht₀J0⟩ :=
    exists_lift_tH_commute_sigma_centralizes_J0 D h hσ₂ hq₂ hcomm hEq rfl
  have hqt₀ : qH D t₀ = (⟨_root_.CFSG.RankThree.GF2n.Parrott.t, t_mem_A⟩ : QA45.originalSubgroup) := by
    have h1 := (J_mem_iff D _).mp ht₀
    rw [map_mul, map_inv, qH_tH, inv_mul_eq_one] at h1
    exact h1.symm
  have ht₀B : ∀ b ∈ B, (t₀ : G) * b * (t₀ : G)⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := by
    intro b hb
    obtain ⟨a, ha, q, hq, rfl⟩ := exists_mul_of_mem_CJ_mul_inv D h hEq hb
    have he := conj_mul_inv_mem_zpowers_of_mem_inf_sigma1Commutator D h hσ₂ hq₂ hcomm hEq hqt₀
      ht₀σ hq
    have hta : (t₀ : G) * a = a * (t₀ : G) := ht₀J0 a ha
    have hae : a * ((t₀ : G) * q * (t₀ : G)⁻¹ * q⁻¹) = ((t₀ : G) * q * (t₀ : G)⁻¹ * q⁻¹) * a :=
      hzH a (J_le_H (mem_CJ.mp ha).2) _ he
    have e : (t₀ : G) * (a * q) * (t₀ : G)⁻¹ * (a * q)⁻¹ = (t₀ : G) * q * (t₀ : G)⁻¹ * q⁻¹ := by
      calc (t₀ : G) * (a * q) * (t₀ : G)⁻¹ * (a * q)⁻¹
          = ((t₀ : G) * a) * q * (t₀ : G)⁻¹ * q⁻¹ * a⁻¹ := by group
        _ = (a * (t₀ : G)) * q * (t₀ : G)⁻¹ * q⁻¹ * a⁻¹ := by rw [hta]
        _ = (a * ((t₀ : G) * q * (t₀ : G)⁻¹ * q⁻¹)) * a⁻¹ := by group
        _ = (((t₀ : G) * q * (t₀ : G)⁻¹ * q⁻¹) * a) * a⁻¹ := by rw [hae]
        _ = (t₀ : G) * q * (t₀ : G)⁻¹ * q⁻¹ := by group
    rw [e]
    exact he
  obtain ⟨c, hcB, rfl⟩ := hx
  have htt₀ : (t₀ : G)⁻¹ * t ∈ B := by
    have hJ1 : ((t₀⁻¹ * t : ↥(H z)) : G) ∈ J z := by
      have hq1 : qH D (t₀⁻¹ * t) = 1 := by
        have h2 := (J_mem_iff D _).mp ht
        rw [map_mul, map_inv, qH_tH, inv_mul_eq_one] at h2
        rw [map_mul, map_inv, hqt₀, ← h2, inv_mul_cancel]
      exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr hq1)
    refine mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simpa using hJ1⟩
    have h1 : (t₀ : G) * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) =
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * (t₀ : G) := congrArg Subtype.val ht₀σ
    have h2 : (t : G) * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) =
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * (t : G) := congrArg Subtype.val htσ
    set s := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) with hs
    have h1' : (t₀ : G)⁻¹ * s = s * (t₀ : G)⁻¹ := by
      calc (t₀ : G)⁻¹ * s = (t₀ : G)⁻¹ * (s * (t₀ : G)) * (t₀ : G)⁻¹ := by group
        _ = (t₀ : G)⁻¹ * ((t₀ : G) * s) * (t₀ : G)⁻¹ := by rw [h1]
        _ = s * (t₀ : G)⁻¹ := by group
    calc (t₀ : G)⁻¹ * t * s = (t₀ : G)⁻¹ * ((t : G) * s) := by group
      _ = (t₀ : G)⁻¹ * (s * t) := by rw [h2]
      _ = ((t₀ : G)⁻¹ * s) * t := by group
      _ = (s * (t₀ : G)⁻¹) * t := by rw [h1']
      _ = s * ((t₀ : G)⁻¹ * t) := by group
  set c' := (t₀ : G)⁻¹ * t * c with hc'
  have hc'B : c' ∈ B := B.mul_mem htt₀ hcB
  have hxeq : (t : G) * c = (t₀ : G) * c' := by rw [hc']; group
  have hxH : (t : G) * c ∈ H z := (H z).mul_mem t.2 (J_le_H (hBJ hcB))
  have hBx : ∀ b ∈ B, b * ((t : G) * c) * b⁻¹ * ((t : G) * c)⁻¹ ∈ Subgroup.zpowers z := by
    intro b hb
    rw [hxeq]
    have hbJ : b ∈ J z := hBJ hb
    have hc'J : c' ∈ J z := hBJ hc'B
    set e₁ := c' * b * c'⁻¹ * b⁻¹ with he₁
    have he₁z : e₁ ∈ Subgroup.zpowers z := hJc c' hc'J b hbJ
    set e₂ := (t₀ : G) * b * (t₀ : G)⁻¹ * b⁻¹ with he₂
    have he₂z : e₂ ∈ Subgroup.zpowers z := ht₀B b hb
    have hcomm1 : (t₀ : G) * e₁ = e₁ * (t₀ : G) := hzH _ t₀.2 _ he₁z
    have e : (t₀ : G) * c' * b * ((t₀ : G) * c')⁻¹ * b⁻¹ = e₁ * e₂ := by
      have h3 : c' * b * c'⁻¹ = e₁ * b := by rw [he₁]; group
      have h4 : (t₀ : G) * b * (t₀ : G)⁻¹ = e₂ * b := by rw [he₂]; group
      calc (t₀ : G) * c' * b * ((t₀ : G) * c')⁻¹ * b⁻¹
          = (t₀ : G) * (c' * b * c'⁻¹) * (t₀ : G)⁻¹ * b⁻¹ := by group
        _ = (t₀ : G) * (e₁ * b) * (t₀ : G)⁻¹ * b⁻¹ := by rw [h3]
        _ = ((t₀ : G) * e₁) * b * (t₀ : G)⁻¹ * b⁻¹ := by group
        _ = (e₁ * (t₀ : G)) * b * (t₀ : G)⁻¹ * b⁻¹ := by rw [hcomm1]
        _ = e₁ * ((t₀ : G) * b * (t₀ : G)⁻¹) * b⁻¹ := by group
        _ = e₁ * (e₂ * b) * b⁻¹ := by rw [h4]
        _ = e₁ * e₂ := by group
    have hinv : b * ((t₀ : G) * c') * b⁻¹ * ((t₀ : G) * c')⁻¹ =
        ((t₀ : G) * c' * b * ((t₀ : G) * c')⁻¹ * b⁻¹)⁻¹ := by group
    rw [hinv, e]
    exact (Subgroup.zpowers z).inv_mem ((Subgroup.zpowers z).mul_mem he₁z he₂z)
  have hBcard : 64 ≤ Nat.card B := by
    rw [hBdef, card_CJ_mul_inv_of_equalityBranch D h hσ₂ hq₂ hcomm hEq]
  obtain ⟨a, haB, b, hbB, hax, hbx, hab⟩ := exists_not_commute_of_le_J_of_card h hBJ hBcard
    (fun a ha hcomm' => mem_centerIn_of_mem_CJ_of_commute h hσ3 ha hcomm') hxH hBx
  have hz_ab : a * b * a⁻¹ * b⁻¹ = z := by
    have hmem := hJc a (hBJ haB) b (hBJ hbB)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hzo : orderOf z = 2 := h.1
    rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
    · exfalso
      apply hab
      have h1 : a * b * a⁻¹ * b⁻¹ = 1 := by
        rw [← hk, ← zpow_mod_orderOf, hzo]
        simp [hk0]
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    · rw [← hk, ← zpow_mod_orderOf, hzo]
      simp [hk1]
  set L : Subgroup G := Subgroup.centralizer ({(t : G) * c} : Set G) ⊓
    Subgroup.centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) with hL
  set A : Subgroup G := B ⊓ Subgroup.centralizer ({(t : G) * c} : Set G) with hA
  have hAHL : A ≤ H z ⊓ L := fun g hg =>
    ⟨J_le_H (hBJ hg.1), hg.2, (mem_CJ.mp hg.1).1⟩
  have hA2 : IsPGroup 2 A := (isPGroup_J h).to_le (inf_le_left.trans hBJ)
  have hAsub : IsPGroup 2 (A.subgroupOf (H z ⊓ L)) := hA2.comap_subtype
  obtain ⟨S₀, hAS₀⟩ := hAsub.exists_le_sylow
  set S : Subgroup G := (S₀ : Subgroup ↥(H z ⊓ L)).map (H z ⊓ L).subtype with hS
  have hSsyl : IsSylowOf 2 S (H z ⊓ L) := ⟨S₀, rfl⟩
  have hAS : A ≤ S := by
    rw [hS, ← Subgroup.map_subgroupOf_eq_of_le hAHL]
    exact Subgroup.map_mono hAS₀
  have hzS : z ∈ ⁅S, S⁆ := by
    rw [← hz_ab]
    have hmem := Subgroup.commutator_mem_commutator (hAS ⟨haB, Subgroup.mem_centralizer_singleton_iff.mpr hax⟩)
      (hAS ⟨hbB, Subgroup.mem_centralizer_singleton_iff.mpr hbx⟩)
    rwa [commutatorElement_def] at hmem
  have hSH : S ≤ H z := hSsyl.le.trans inf_le_left
  have hSJ : ⁅S, S⁆ ≤ J z := commutator_le_J_of_le_centralizer_sigma1Nine_mul_inv D hq₂ hSH
    (hSsyl.le.trans (inf_le_right.trans inf_le_right)) hSsyl.isPGroup
  refine ⟨S, hSH, ?_, hzS, hSJ⟩
  refine CFSG.GroupTheory.isSylowOf_of_forall_pElement_normalizer_le hSsyl ?_
  intro g _ hgN _
  have hSmap : S.map (MulAut.conj g).toMonoidHom = S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
  have hmap : (⁅S, S⁆).map (MulAut.conj g).toMonoidHom = ⁅S, S⁆ := by
    rw [Subgroup.map_commutator, hSmap]
  have hzg : g * z * g⁻¹ ∈ ⁅S, S⁆ := by
    have hmem : (MulAut.conj g) z ∈ (⁅S, S⁆).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hzS
    simpa [MulAut.conj_apply] using hmap ▸ hmem
  have hz2 : orderOf (g * z * g⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) z
    rwa [MulAut.conj_apply, h.1] at this
  have hz_eq : g * z * g⁻¹ = z := by
    by_contra hne
    exact hJ _ (hSJ hzg) hz2 hne g rfl
  rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [hz_eq]

end CFSG.RankThree.GF2n.Parrott
