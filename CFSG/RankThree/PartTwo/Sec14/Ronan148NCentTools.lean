module

import CFSG.RankThree.PartTwo.Sec14.Item1418Res2Proof1418
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148N

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

section Comm

variable {Γ : Type*} [Group Γ]

theorem commutatorElement_mul_right_of_commute148 {x b y : Γ} (h : x * b = b * x) :
    ⁅x, b * y⁆ = b * ⁅x, y⁆ * b⁻¹ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (b * y) * x⁻¹ * (b * y)⁻¹ = (x * b) * y * x⁻¹ * y⁻¹ * b⁻¹ := by group
    _ = (b * x) * y * x⁻¹ * y⁻¹ * b⁻¹ := by rw [h]
    _ = b * (x * y * x⁻¹ * y⁻¹) * b⁻¹ := by group

theorem commutatorElement_mul_left_of_commute148 {u v c : Γ} (h : v * c = c * v) :
    ⁅u * v, c⁆ = ⁅u, c⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc u * v * c * (u * v)⁻¹ * c⁻¹ = u * (v * c) * v⁻¹ * u⁻¹ * c⁻¹ := by group
    _ = u * (c * v) * v⁻¹ * u⁻¹ * c⁻¹ := by rw [h]
    _ = u * c * u⁻¹ * c⁻¹ := by group

theorem commutatorElement_mul_split148 {u v g : Γ} (h : u * ⁅v, g⁆ = ⁅v, g⁆ * u) :
    ⁅u * v, g⁆ = ⁅v, g⁆ * ⁅u, g⁆ := by
  have e1 : ⁅u * v, g⁆ = u * ⁅v, g⁆ * (g * u⁻¹ * g⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e1, h, commutatorElement_def u g]
  group

theorem mem_normalizer_centralizer148 {H : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (H : Set Γ)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (H : Set Γ) : Set Γ) := by
  have key : ∀ {w : Γ}, w ∈ Subgroup.normalizer (H : Set Γ) → ∀ z : Γ,
      z ∈ Subgroup.centralizer (H : Set Γ) → w * z * w⁻¹ ∈ Subgroup.centralizer (H : Set Γ) := by
    intro w hw z hz
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro h hh
    have hh' : w⁻¹ * h * w ∈ H := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw) h).mp hh
      simpa using this
    have hc := hz _ hh'
    calc h * (w * z * w⁻¹) = w * ((w⁻¹ * h * w) * z) * w⁻¹ := by group
      _ = w * (z * (w⁻¹ * h * w)) * w⁻¹ := by rw [hc]
      _ = w * z * w⁻¹ * h := by group
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact key hg z
  · intro hz
    have := key (Subgroup.inv_mem _ hg) _ hz
    simpa [mul_assoc] using this

theorem mem_normalizer_inf148 {H K : Subgroup Γ} {g : Γ}
    (hH : g ∈ Subgroup.normalizer (H : Set Γ)) (hK : g ∈ Subgroup.normalizer (K : Set Γ)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp hH x,
    ← Subgroup.mem_normalizer_iff.mp hK x]

theorem le_normalizer_of_forall148 {H S : Subgroup Γ}
    (h : ∀ c ∈ H, ∀ w ∈ S, c * w * c⁻¹ ∈ S) : H ≤ Subgroup.normalizer (S : Set Γ) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨h c hc w, fun hw => ?_⟩
  have := h c⁻¹ (H.inv_mem hc) _ hw
  simpa [mul_assoc] using this

end Comm

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_mul_zpow_of_hyperplane148 {A B : Subgroup G} (hA : Late.IsE27 A)
    (hB : IsHyperplane A B) {g : G} (hgA : g ∈ A) (hgB : g ∉ B) {a : G} (ha : a ∈ A) :
    ∃ b ∈ B, ∃ k : ℕ, a = b * g ^ k := by
  have hAeq := Proof1418Res2.eq_sup_zpowers_of_not_mem hA hB hgA hgB
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hN : Subgroup.zpowers g ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hcomm g hgA x (hB.1 hx), mul_assoc, mul_inv_cancel, mul_one]
      exact hx
    · intro hx
      have hxA : x ∈ A := by
        have h1 : g * x * g⁻¹ ∈ A := hB.1 hx
        have h2 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [← h2]
        exact A.mul_mem (A.mul_mem (A.inv_mem hgA) h1) hgA
      rwa [hcomm g hgA x hxA, mul_assoc, mul_inv_cancel, mul_one] at hx
  have hmem : a ∈ (B : Set G) * (Subgroup.zpowers g : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left B (Subgroup.zpowers g) hN, ← hAeq]
    exact ha
  obtain ⟨b, hb, z, hz, rfl⟩ := hmem
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, g ^ k = z :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
  exact ⟨b, hb, k, rfl⟩

theorem centralizer_inf_le_of_hyperplane148 {A B B' : Subgroup G} (hA : Late.IsE27 A)
    (hB : IsHyperplane A B) (hB' : IsHyperplane A B') (hne : B' ≠ B) :
    Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer (B' : Set G) ≤
      Subgroup.centralizer (A : Set G) := by
  have : ∃ g ∈ B', g ∉ B := by
    by_contra hcon
    push Not at hcon
    have hle : B' ≤ B := fun g hg => hcon g hg
    apply hne
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := hB.2
    have h2 := hB'.2
    omega
  obtain ⟨g, hgB', hgB⟩ := this
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨b, hb, k, rfl⟩ := exists_mem_mul_zpow_of_hyperplane148 hA hB (hB'.1 hgB') hgB ha
  have h1 := Subgroup.mem_centralizer_iff.mp hx.1 b hb
  have h2 : g ^ k * x = x * g ^ k :=
    (Commute.pow_left (Subgroup.mem_centralizer_iff.mp hx.2 g hgB') k)
  calc b * g ^ k * x = b * (g ^ k * x) := by group
    _ = b * (x * g ^ k) := by rw [h2]
    _ = (b * x) * g ^ k := by group
    _ = (x * b) * g ^ k := by rw [h1]
    _ = x * (b * g ^ k) := by group

theorem pPrimeCoreOf_centralizer_mem_scriptQ {A B : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : Late.IsE27 A) (hB : IsHyperplane A B) :
    pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ∈ scriptQ A LB := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hO
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAC : A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm b (hB.1 hb) a ha
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAC.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hOC : O ≤ Subgroup.centralizer (B : Set G) := pPrimeCoreOf_le 3 _
  have hO3 : Nat.Coprime 3 (Nat.card O) := coprime_card_pPrimeCoreOf 3 _
  refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three O).mpr
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO3), hAO, fun B' hB' => ?_⟩
  by_cases hBB : B' = B
  · subst hBB
    exact inf_le_left.trans (le_sup_left.trans le_sup_left)
  ·
    have hle : O ⊓ Subgroup.centralizer (B' : Set G) ≤
        O ⊓ Subgroup.centralizer (A : Set G) := fun x hx =>
      ⟨hx.1, centralizer_inf_le_of_hyperplane148 hA hB hB' hBB ⟨hOC hx.1, hx.2⟩⟩
    refine hle.trans (le_trans ?_ (le_sup_right.trans le_sup_left))
    refine le_pPrimeCoreOf inf_le_right ?_
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hO3)
    intro g hg
    have hgB : g ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro b hb
      exact hg b (hB.1 hb)
    have hgO : g ∈ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 _ hgB
    have hgC : g ∈ Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) :=
      Subgroup.le_normalizer hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp hgO x,
      ← Subgroup.mem_normalizer_iff.mp hgC x]

theorem le_pPrimeCoreOf_centralizer_of_scriptQZero {A B Q : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hA : Late.IsE27 A) (hB : IsHyperplane A B)
    (hLB : LB B = ⊥) (hQ : Q ∈ scriptQZero A LB)
    (hQB : Q ≤ Subgroup.centralizer (B : Set G)) :
    Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
  set O := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hO
  set OA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hOA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAC : A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm b (hB.1 hb) a ha
  have hCA_CB : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.centralizer_le hB.1
  have hOAN : OA ≤ Subgroup.normalizer (O : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (hCA_CB.trans (le_normalizer_pPrimeCoreOf 3 _))
  have hQle : Q ≤ O ⊔ OA := by
    have h1 : Q ⊓ Subgroup.centralizer (B : Set G) ≤ qBound A LB B := hQ.1.2 B hB
    rw [inf_eq_left.mpr hQB, qBound, hLB, sup_bot_eq] at h1
    exact h1
  have hcommO : ⁅O ⊔ OA, A⁆ ≤ O := by
    rw [Subgroup.commutator_le]
    intro x hx a ha
    have hx' : x ∈ (O : Set G) * (OA : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left O OA hOAN]
      exact hx
    obtain ⟨o, ho, c, hc, rfl⟩ := hx'
    have hca : c * a = a * c :=
      (Subgroup.mem_centralizer_iff.mp (pPrimeCoreOf_le 3 _ hc) a ha).symm
    have haO : a ∈ Subgroup.normalizer (O : Set G) := hAC.trans (le_normalizer_pPrimeCoreOf 3 _) ha
    have e1 : ⁅o * c, a⁆ = o * (a * o⁻¹ * a⁻¹) := by
      rw [commutatorElement_def]
      calc o * c * a * (o * c)⁻¹ * a⁻¹ = o * (c * a) * c⁻¹ * o⁻¹ * a⁻¹ := by group
        _ = o * (a * c) * c⁻¹ * o⁻¹ * a⁻¹ := by rw [hca]
        _ = o * (a * o⁻¹ * a⁻¹) := by group
    rw [e1]
    exact O.mul_mem ho ((Subgroup.mem_normalizer_iff.mp haO o⁻¹).mp (O.inv_mem ho))
  rw [hQ.2]
  exact (Subgroup.commutator_mono hQle le_rfl).trans hcommO

section Lift

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem exists_lift_centralizer148 (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {J B : Subgroup G}
    (hJY : J ≤ Y) (hBA : B ≤ A) (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hB3 : IsPGroup 3 B)
    {c : ↥(Y ⊔ A) ⧸ ker148 A Y} (hcJ : c ∈ img148 A Y J)
    (hcB : c ∈ Subgroup.centralizer (img148 A Y B : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    ∃ (x : G) (hx : x ∈ Y ⊔ A), x ∈ J ∧ x ∈ Subgroup.centralizer (B : Set G) ∧
      QuotientGroup.mk' (ker148 A Y) ⟨x, hx⟩ = c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := pPrimeCoreOf 3 Y with hR
  obtain ⟨k, hkM, hkJ, rfl⟩ := mem_img148_iff.mp hcJ
  set N := J ⊓ R with hN
  have hN3 : Nat.Coprime 3 (Nat.card N) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (coprime_card_pPrimeCoreOf 3 Y)
  have hBR : B ≤ Subgroup.normalizer (R : Set G) :=
    (hBA.trans hAY).trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  have hBN : B ≤ Subgroup.normalizer (N : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hN, Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp (hBJ hb) x,
      ← Subgroup.mem_normalizer_iff.mp (hBR hb) x]
  have hk : ∀ b ∈ B, k⁻¹ * (b * k * b⁻¹) ∈ N := by
    intro b hb
    have hbM : b ∈ Y ⊔ A := Subgroup.mem_sup_right (hBA hb)
    refine ⟨J.mul_mem (J.inv_mem hkJ) ((Subgroup.mem_normalizer_iff.mp (hBJ hb) k).mp hkJ), ?_⟩
    have hbimg : QuotientGroup.mk' (ker148 A Y) ⟨b, hbM⟩ ∈ img148 A Y B :=
      mem_img148_iff.mpr ⟨b, hbM, hb, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp hcB _ hbimg
    have heq : QuotientGroup.mk' (ker148 A Y) ⟨k, hkM⟩ =
        QuotientGroup.mk' (ker148 A Y) (⟨b, hbM⟩ * ⟨k, hkM⟩ * ⟨b, hbM⟩⁻¹) := by
      rw [map_mul, map_mul, map_inv, hc, mul_assoc, mul_inv_cancel, mul_one]
    have := mk'_ker148_eq_iff.mp heq
    simpa [mul_assoc] using this
  obtain ⟨y, hky, hyB⟩ := exists_commute_mem_coset148 hB3 hN3 hBN hk
  have hyJ : y ∈ J := by
    have : y = k * (k⁻¹ * y) := by group
    rw [this]
    exact J.mul_mem hkJ hky.1
  have hyM : y ∈ Y ⊔ A := Subgroup.mem_sup_left (hJY hyJ)
  refine ⟨y, hyM, hyJ, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hyB b hb)
  · rw [mk'_ker148_eq_iff]
    have := R.inv_mem hky.2
    simpa using this

end Lift

end CFSG.RankThree.PartTwo.Sec14.Ronan148N
