module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119KCoord
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

structure TData {G : Type} [Group G] [Finite G] (A Q D M Y : Subgroup G) (d e t₀ : G) : Prop where
  hAe : IsElemAbelian 3 A
  hA27 : Nat.card A = 27
  hdA : d ∈ A
  hd1 : d ≠ 1
  hQX : IsExtra2127 Q
  hQS : IsSylowOf 3 Q (Subgroup.normalizer (A : Set G))
  hAQ : A ≤ Q
  hQC : Q ⊓ Subgroup.centralizer (A : Set G) = A
  hdc : ∀ q ∈ Q, q * d * q⁻¹ = d
  heA : e ∈ A
  hed : e ∉ Subgroup.zpowers d
  hDe : IsElemAbelian 3 D
  hD81 : Nat.card D = 81
  hdD : d ∈ D
  hDY : D ≤ Y
  hQY : Q ≤ Y
  hLA : Hering2119S.LineAbs D M Y e
  h729 : ∀ R : Subgroup G, IsPGroup 3 R → R ≤ Y → Nat.card R ≤ 729
  hrank : ∀ b ∈ A, b ∉ Subgroup.zpowers d → ∀ X : Subgroup G, IsPGroup 3 X →
    (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → X ≤ Subgroup.centralizer ({b} : Set G) →
      Nat.card X ≤ 27
  ht₀Y : t₀ ∈ Y
  ht₀D : ∀ x ∈ D, t₀ * x * t₀⁻¹ = x⁻¹

namespace TData

variable {G : Type} [Group G] [Finite G] {A Q D M Y : Subgroup G} {d e t₀ : G}

theorem hDc (h : TData A Q D M Y d e t₀) : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (h.hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem hD3 (h : TData A Q D M Y d e t₀) : IsPGroup 3 D :=
  Item2119End8Proof.isPGroup_of_pow h.hDe.2

theorem hQD (h : TData A Q D M Y d e t₀) : Q ≤ Subgroup.normalizer (D : Set G) :=
  h.hQY.trans h.hLA.hYN

theorem hQ243 (h : TData A Q D M Y d e t₀) : Nat.card Q = 243 := by
  obtain ⟨-, h35, -⟩ := h.hQX
  rw [h35]; norm_num

theorem hQ3 (h : TData A Q D M Y d e t₀) : IsPGroup 3 Q := h.hQS.isPGroup

theorem card_QD (h : TData A Q D M Y d e t₀) :
    Nat.card (Q ⊔ D : Subgroup G) = 729 ∧ Nat.card (D ⊓ Q : Subgroup G) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQD27 : Nat.card (D ⊓ Q : Subgroup G) ≤ 27 := by
    have h' := Item2119End3Proof.card_le_of_commute_of_extraspecial h.hQX.1 h.hQ243
      (B := (D ⊓ Q).subgroupOf Q) (fun x hx y hy => Subtype.ext
        (h.hDc _ (Subgroup.mem_subgroupOf.mp hx).1 _ (Subgroup.mem_subgroupOf.mp hy).1))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h'
  have hm := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer h.hQD
  rw [h.hD81, h.hQ243] at hm
  have hP3 : IsPGroup 3 (Q ⊔ D : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' h.hQ3 h.hD3 h.hQD
  have h729 : Nat.card (Q ⊔ D : Subgroup G) ≤ 729 :=
    h.h729 _ hP3 (sup_le h.hQY h.hDY)
  have hP729 : Nat.card (Q ⊔ D : Subgroup G) = 729 := by
    have h1 : 81 * 243 ≤ Nat.card (D ⊔ Q : Subgroup G) * 27 := by
      rw [← hm]
      exact Nat.mul_le_mul_left _ hQD27
    rw [sup_comm] at h729 ⊢
    omega
  refine ⟨hP729, ?_⟩
  rw [sup_comm] at hP729
  rw [hP729] at hm
  omega

theorem hP'N (h : TData A Q D M Y d e t₀) : Q ⊔ D ≤ Subgroup.normalizer (Q : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Item2119End8Proof.le_normalizer_of_card le_sup_left
    (IsPGroup.to_sup_of_normal_right' h.hQ3 h.hD3 h.hQD) (by rw [h.card_QD.1, h.hQ243])

theorem hP'ND (h : TData A Q D M Y d e t₀) : Q ⊔ D ≤ Subgroup.normalizer (D : Set G) :=
  sup_le h.hQD Subgroup.le_normalizer

theorem hP'3 (h : TData A Q D M Y d e t₀) : IsPGroup 3 (Q ⊔ D : Subgroup G) :=
  IsPGroup.to_sup_of_normal_right' h.hQ3 h.hD3 h.hQD

theorem hP'Y (h : TData A Q D M Y d e t₀) : Q ⊔ D ≤ Y := sup_le h.hQY h.hDY

theorem sylow_P' (h : TData A Q D M Y d e t₀) : IsSylowOf 3 (Q ⊔ D : Subgroup G) Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS, hle⟩ := exists_sylowOf_ge h.hP'3 h.hP'Y
  have h1 : Nat.card S ≤ 729 := h.h729 S hS.isPGroup hS.le
  have h2 : S = (Q ⊔ D : Subgroup G) :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_QD.1]; exact h1)).symm
  rw [← h2]; exact hS

theorem mem_D_of_centralizes (h : TData A Q D M Y d e t₀) {c : G} (hcQ : c ∈ Q)
    (hc : ∀ m ∈ D ⊓ Q, c * m = m * c) : c ∈ D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, h27⟩ := h.card_QD
  set M' := D ⊓ Q with hM'
  have hM'c : ∀ x ∈ M', ∀ y ∈ M', x * y = y * x := fun x hx y hy => h.hDc x hx.1 y hy.1
  have hB : ∀ x ∈ Subgroup.zpowers c ⊔ M', ∀ y ∈ Subgroup.zpowers c ⊔ M', x * y = y * x :=
    Item2119End8Proof.comm_sup (Item2119End8Proof.comm_zpowers_self c) hM'c
      (Item2119End8Proof.comm_zpowers hc)
  have hBQ : Subgroup.zpowers c ⊔ M' ≤ Q := sup_le (Subgroup.zpowers_le.mpr hcQ) inf_le_right
  have hle : Nat.card (Subgroup.zpowers c ⊔ M' : Subgroup G) ≤ 27 := by
    have h' := Item2119End3Proof.card_le_of_commute_of_extraspecial h.hQX.1 h.hQ243
      (B := (Subgroup.zpowers c ⊔ M').subgroupOf Q) (fun x hx y hy => Subtype.ext
        (hB _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy)))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv] at h'
  have heq : M' = Subgroup.zpowers c ⊔ M' :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h27]; exact hle)
  have : c ∈ M' := by
    rw [heq]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  exact this.1

theorem centralizer_P'_eq (h : TData A Q D M Y d e t₀) :
    (Q ⊔ D) ⊓ Subgroup.centralizer (D : Set G) = D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := (Q ⊔ D) ⊓ Subgroup.centralizer (D : Set G) with hZ
  have hDZ : D ≤ Z := fun x hx => ⟨Subgroup.mem_sup_right hx,
    Subgroup.mem_centralizer_iff.mpr fun y hy => (h.hDc y hy x hx)⟩
  have hZN : Z ≤ Subgroup.normalizer (Q : Set G) := inf_le_left.trans h.hP'N
  have hZQ : Q ⊓ Z ≤ D ⊓ Q := fun c hc => ⟨h.mem_D_of_centralizes hc.1 fun m hm =>
    (Subgroup.mem_centralizer_iff.mp hc.2.2 m hm.1).symm, hc.1⟩
  have hm := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hZN
  have h1 : Nat.card (Q ⊔ Z : Subgroup G) ≤ 729 := by
    rw [← h.card_QD.1]
    exact Subgroup.card_le_of_le (sup_le le_sup_left inf_le_left)
  have h2 : Nat.card (Q ⊓ Z : Subgroup G) ≤ 27 := by
    rw [← h.card_QD.2]; exact Subgroup.card_le_of_le hZQ
  rw [h.hQ243] at hm
  have h3 : 243 * Nat.card Z ≤ 729 * 27 := by
    rw [← hm]; exact Nat.mul_le_mul h1 h2
  have h4 : Nat.card Z ≤ Nat.card D := by rw [h.hD81]; omega
  exact (Subgroup.eq_of_le_of_card_ge hDZ h4).symm

theorem ht₀D' (h : TData A Q D M Y d e t₀) : ∀ x ∈ D, t₀⁻¹ * x * t₀ = x⁻¹ := by
  intro x hx
  have hz : t₀⁻¹ * x * t₀ ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp (h.hLA.hYN (Y.inv_mem h.ht₀Y)) x).mp hx
    simpa using this
  have h1 := h.ht₀D _ hz
  have h2 : t₀ * (t₀⁻¹ * x * t₀) * t₀⁻¹ = x := by group
  rw [h2] at h1
  calc t₀⁻¹ * x * t₀ = (t₀⁻¹ * x * t₀)⁻¹⁻¹ := (inv_inv _).symm
    _ = x⁻¹ := by rw [← h1]

theorem exists_g (h : TData A Q D M Y d e t₀) :
    ∃ g : G, g ∈ Y ∧ g ∈ Subgroup.normalizer ((Q ⊔ D : Subgroup G) : Set G) ∧
      ∀ x ∈ D, g * x * g⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P' : Subgroup G := Q ⊔ D with hP'def
  have hP'S : IsSylowOf 3 P' Y := h.sylow_P'
  have hP'D : P' ≤ Subgroup.normalizer (D : Set G) := h.hP'ND
  have hP'Y : P' ≤ Y := h.hP'Y
  let X : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ ∃ p ∈ P', ∀ x ∈ D, y * x * y⁻¹ = p * x * p⁻¹}
      mul_mem' := by
        rintro a b ⟨haY, p, hp, hap⟩ ⟨hbY, q, hq, hbq⟩
        refine ⟨Y.mul_mem haY hbY, p * q, P'.mul_mem hp hq, fun x hx => ?_⟩
        have hqx : q * x * q⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hP'D hq) x).mp hx
        calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
          _ = a * (q * x * q⁻¹) * a⁻¹ := by rw [hbq x hx]
          _ = p * (q * x * q⁻¹) * p⁻¹ := hap _ hqx
          _ = p * q * x * (p * q)⁻¹ := by group
      one_mem' := ⟨Y.one_mem, 1, P'.one_mem, fun x hx => by simp⟩
      inv_mem' := by
        rintro a ⟨haY, p, hp, hap⟩
        refine ⟨Y.inv_mem haY, p⁻¹, P'.inv_mem hp, fun x hx => ?_⟩
        have hpx : p⁻¹ * x * p ∈ D := by
          have := (Subgroup.mem_normalizer_iff.mp (hP'D (P'.inv_mem hp)) x).mp hx
          simpa using this
        have h1 := hap _ hpx
        have h2 : p * (p⁻¹ * x * p) * p⁻¹ = x := by group
        rw [h2] at h1
        calc a⁻¹ * x * a⁻¹⁻¹ = a⁻¹ * (a * (p⁻¹ * x * p) * a⁻¹) * a⁻¹⁻¹ := by rw [h1]
          _ = p⁻¹ * x * p⁻¹⁻¹ := by group }
  have hXY : X ≤ Y := fun y hy => hy.1
  have hP'X : P' ≤ X := fun p hp => ⟨hP'Y hp, p, hp, fun x _ => rfl⟩
  let P'' : Subgroup G := P'.map (MulAut.conj t₀).toMonoidHom
  have hmemP'' : ∀ x, x ∈ P'' ↔ ∃ y ∈ P', t₀ * y * t₀⁻¹ = x := by
    intro x
    simp only [P'', Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hP''Y : P'' ≤ Y := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmemP'' x).mp hx
    exact Y.mul_mem (Y.mul_mem h.ht₀Y (hP'Y hy)) (Y.inv_mem h.ht₀Y)
  have hP''S : IsSylowOf 3 P'' Y := by
    refine isSylowOf_of_card hP''Y ?_
    rw [← hP'S.card_eq]
    exact Subgroup.card_map_of_injective (MulAut.conj t₀).injective
  have hP''X : P'' ≤ X := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmemP'' x).mp hx
    refine ⟨hP''Y ((hmemP'' _).mpr ⟨y, hy, rfl⟩), y, hy, fun z hz => ?_⟩
    have hyz : y * z⁻¹ * y⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hP'D hy) z⁻¹).mp (D.inv_mem hz)
    have h1 : t₀ * (y * z⁻¹ * y⁻¹) * t₀⁻¹ = (y * z⁻¹ * y⁻¹)⁻¹ := h.ht₀D _ hyz
    have h2 : t₀⁻¹ * z * t₀ = z⁻¹ := h.ht₀D' z hz
    calc t₀ * y * t₀⁻¹ * z * (t₀ * y * t₀⁻¹)⁻¹
        = t₀ * y * (t₀⁻¹ * z * t₀) * y⁻¹ * t₀⁻¹ := by group
      _ = t₀ * (y * z⁻¹ * y⁻¹) * t₀⁻¹ := by rw [h2]; group
      _ = (y * z⁻¹ * y⁻¹)⁻¹ := h1
      _ = y * z * y⁻¹ := by group
  obtain ⟨c, hcX, hc⟩ := (hP'S.of_le hP'X hXY).exists_mem_conj (hP''S.of_le hP''X hXY)
  obtain ⟨hcY, p, hp, hcp⟩ := hcX
  have hca : ∀ y ∈ D, c⁻¹ * y * c = p⁻¹ * y * p := by
    intro y hy
    have hpy : p⁻¹ * y * p ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (hP'D (P'.inv_mem hp)) y).mp hy
      simpa using this
    have h1 := hcp _ hpy
    have h2 : p * (p⁻¹ * y * p) * p⁻¹ = y := by group
    rw [h2] at h1
    calc c⁻¹ * y * c = c⁻¹ * (c * (p⁻¹ * y * p) * c⁻¹) * c := by rw [h1]
      _ = p⁻¹ * y * p := by group
  refine ⟨p * c⁻¹ * t₀, Y.mul_mem (Y.mul_mem (hP'Y hp) (Y.inv_mem hcY)) h.ht₀Y, ?_, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have h1 : t₀ * x * t₀⁻¹ ∈ P'' := (hmemP'' _).mpr ⟨x, hx, rfl⟩
    have h2 := (hc _).mp h1
    have h3 : p * c⁻¹ * t₀ * x * (p * c⁻¹ * t₀)⁻¹ = p * (c⁻¹ * (t₀ * x * t₀⁻¹) * c) * p⁻¹ := by
      group
    rw [h3]
    exact P'.mul_mem (P'.mul_mem hp h2) (P'.inv_mem hp)
  · intro x hx
    have h1 : t₀ * x * t₀⁻¹ = x⁻¹ := h.ht₀D x hx
    calc p * c⁻¹ * t₀ * x * (p * c⁻¹ * t₀)⁻¹
        = p * (c⁻¹ * (t₀ * x * t₀⁻¹) * c) * p⁻¹ := by group
      _ = p * (c⁻¹ * x⁻¹ * c) * p⁻¹ := by rw [h1]
      _ = p * (p⁻¹ * x⁻¹ * p) * p⁻¹ := by rw [hca _ (D.inv_mem hx)]
      _ = x⁻¹ := by group

theorem inv_conj_of_inv (h : TData A Q D M Y d e t₀) {g : G} (hgY : g ∈ Y)
    (hg : ∀ x ∈ D, g * x * g⁻¹ = x⁻¹) : ∀ x ∈ D, g⁻¹ * x * g = x⁻¹ := by
  intro x hx
  have hz : g⁻¹ * x * g ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp (h.hLA.hYN (Y.inv_mem hgY)) x).mp hx
    simpa using this
  have h1 := hg _ hz
  have h2 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [h2] at h1
  calc g⁻¹ * x * g = (g⁻¹ * x * g)⁻¹⁻¹ := (inv_inv _).symm
    _ = x⁻¹ := by rw [← h1]

theorem delta_mem (h : TData A Q D M Y d e t₀) {g : G} (hgY : g ∈ Y)
    (hgN : g ∈ Subgroup.normalizer ((Q ⊔ D : Subgroup G) : Set G))
    (hg : ∀ x ∈ D, g * x * g⁻¹ = x⁻¹) {b : G} (hb : b ∈ Q) : b⁻¹ * g * b * g⁻¹ ∈ D := by
  have hbP : b ∈ Q ⊔ D := Subgroup.mem_sup_left hb
  have hgbP : g * b * g⁻¹ ∈ Q ⊔ D := (Subgroup.mem_normalizer_iff.mp hgN b).mp hbP
  have hδP : b⁻¹ * g * b * g⁻¹ ∈ Q ⊔ D := by
    have : b⁻¹ * g * b * g⁻¹ = b⁻¹ * (g * b * g⁻¹) := by group
    rw [this]
    exact (Q ⊔ D).mul_mem ((Q ⊔ D).inv_mem hbP) hgbP
  have hginv := h.inv_conj_of_inv hgY hg
  have hδC : b⁻¹ * g * b * g⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hbx : b * x⁻¹ * b⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (h.hQD hb) x⁻¹).mp (D.inv_mem hx)
    have h1 : g * (b * x⁻¹ * b⁻¹) * g⁻¹ = (b * x⁻¹ * b⁻¹)⁻¹ := hg _ hbx
    have h2 : (b⁻¹ * g * b * g⁻¹) * x * (b⁻¹ * g * b * g⁻¹)⁻¹ = x := by
      calc (b⁻¹ * g * b * g⁻¹) * x * (b⁻¹ * g * b * g⁻¹)⁻¹
          = b⁻¹ * (g * (b * (g⁻¹ * x * g) * b⁻¹) * g⁻¹) * b := by group
        _ = b⁻¹ * (g * (b * x⁻¹ * b⁻¹) * g⁻¹) * b := by rw [hginv x hx]
        _ = b⁻¹ * (b * x⁻¹ * b⁻¹)⁻¹ * b := by rw [h1]
        _ = x := by group
    calc x * (b⁻¹ * g * b * g⁻¹) = ((b⁻¹ * g * b * g⁻¹) * x * (b⁻¹ * g * b * g⁻¹)⁻¹) *
          (b⁻¹ * g * b * g⁻¹) := by rw [h2]
      _ = (b⁻¹ * g * b * g⁻¹) * x := by group
  rw [← h.centralizer_P'_eq]
  exact ⟨hδP, hδC⟩

@[expose] def phi (b x : G) : G := (b * x * b⁻¹) * (b * (b * x * b⁻¹) * b⁻¹) * x

theorem phi_eq {b : G} (hb : b ^ 3 = 1) (x : G) : (b * x) ^ 3 = phi b x := by
  have hb3 : b * b * b = 1 := by
    rw [← pow_three']; exact hb
  have hb2 : b⁻¹ * b⁻¹ = b := by
    calc b⁻¹ * b⁻¹ = b⁻¹ * b⁻¹ * (b * b * b) := by rw [hb3, mul_one]
      _ = b := by group
  unfold phi
  calc (b * x) ^ 3 = b * x * b * x * b * x := by rw [pow_three']; simp only [mul_assoc]
    _ = b * x * b * x * (b⁻¹ * b⁻¹) * x := by rw [hb2]
    _ = b * x * b⁻¹ * (b * (b * x * b⁻¹) * b⁻¹) * x := by group

theorem phi_one (b : G) : phi b 1 = 1 := by simp [phi]

theorem phi_mul (h : TData A Q D M Y d e t₀) {b : G} (hb : b ∈ Subgroup.normalizer (D : Set G))
    {x y : G} (hx : x ∈ D) (hy : y ∈ D) : phi b (x * y) = phi b x * phi b y := by
  have hσ : ∀ z ∈ D, b * z * b⁻¹ ∈ D := fun z hz => (Subgroup.mem_normalizer_iff.mp hb z).mp hz
  have ha : b * x * b⁻¹ ∈ D := hσ x hx
  have ha' : b * (b * x * b⁻¹) * b⁻¹ ∈ D := hσ _ ha
  have hc : b * y * b⁻¹ ∈ D := hσ y hy
  have hc' : b * (b * y * b⁻¹) * b⁻¹ ∈ D := hσ _ hc
  set a := b * x * b⁻¹ with hadef
  set a' := b * a * b⁻¹ with ha'def
  set c := b * y * b⁻¹ with hcdef
  set c' := b * c * b⁻¹ with hc'def
  have e1 : b * (x * y) * b⁻¹ = a * c := by rw [hadef, hcdef]; group
  have e2 : b * (a * c) * b⁻¹ = a' * c' := by rw [ha'def, hc'def]; group
  unfold phi
  rw [e1, e2]
  calc a * c * (a' * c') * (x * y) = a * (c * a') * c' * x * y := by group
    _ = a * (a' * c) * c' * x * y := by rw [h.hDc c hc a' ha']
    _ = a * a' * (c * c' * x) * y := by group
    _ = a * a' * (x * (c * c')) * y := by rw [h.hDc (c * c') (D.mul_mem hc hc') x hx]
    _ = (a * a' * x) * (c * c' * y) := by group

theorem pow3_Q (h : TData A Q D M Y d e t₀) : ∀ q ∈ Q, q ^ 3 = 1 := by
  intro q hq
  have := Monoid.pow_exponent_eq_one (⟨q, hq⟩ : Q)
  rw [h.hQX.2.2] at this
  simpa using congrArg Subtype.val this

def kSub (h : TData A Q D M Y d e t₀) {b : G} (hb : b ∈ Subgroup.normalizer (D : Set G)) :
    Subgroup G where
  carrier := {x | x ∈ D ∧ phi b x = 1}
  mul_mem' := by
    rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
    exact ⟨D.mul_mem hx hy, by rw [h.phi_mul hb hx hy, hx1, hy1, one_mul]⟩
  one_mem' := ⟨D.one_mem, phi_one b⟩
  inv_mem' := by
    rintro x ⟨hx, hx1⟩
    refine ⟨D.inv_mem hx, ?_⟩
    have h1 := h.phi_mul hb hx (D.inv_mem hx)
    rw [mul_inv_cancel, phi_one, hx1, one_mul] at h1
    exact h1.symm

theorem mixed_mem (h : TData A Q D M Y d e t₀) {b : G} (hbQ : b ∈ Q) (hb3 : b ^ 3 = 1)
    (hmix : ∃ x ∈ D, (b * x) ^ 3 ≠ 1) {δ : G} (hδ : δ ∈ D) (hδ3 : (b * δ) ^ 3 = 1) :
    δ ∈ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbN : b ∈ Subgroup.normalizer (D : Set G) := h.hQD hbQ
  set K := h.kSub hbN with hK
  have hKD : K ≤ D := fun x hx => hx.1
  have hMK : D ⊓ Q ≤ K := by
    intro m hm
    refine ⟨hm.1, ?_⟩
    rw [← phi_eq hb3]
    exact h.pow3_Q _ (Q.mul_mem hbQ hm.2)
  have hKne : Nat.card K ≠ 81 := by
    intro h81
    have hKD' : K = D := Subgroup.eq_of_le_of_card_ge hKD (by rw [h.hD81, h81])
    obtain ⟨x, hx, hx3⟩ := hmix
    apply hx3
    rw [phi_eq hb3]
    have hxK : x ∈ K := hKD'.symm ▸ hx
    exact hxK.2
  have hdvd : Nat.card K ∣ 3 ^ 4 := by
    have := Subgroup.card_dvd_of_le hKD
    rwa [h.hD81, show (81 : ℕ) = 3 ^ 4 by norm_num] at this
  have hge : 27 ≤ Nat.card K := by
    rw [← h.card_QD.2]; exact Subgroup.card_le_of_le hMK
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hK27 : Nat.card K = 27 := by
    generalize Nat.card K = n at hge hKne hk'
    interval_cases k <;> omega
  have hKeq : D ⊓ Q = K := Subgroup.eq_of_le_of_card_ge hMK (by rw [h.card_QD.2]; omega)
  have hδK : δ ∈ K := ⟨hδ, by rw [← phi_eq hb3]; exact hδ3⟩
  rw [← hKeq] at hδK
  exact hδK.2

theorem conj_mixed (h : TData A Q D M Y d e t₀) {g : G} (hgY : g ∈ Y)
    (hgN : g ∈ Subgroup.normalizer ((Q ⊔ D : Subgroup G) : Set G))
    (hg : ∀ x ∈ D, g * x * g⁻¹ = x⁻¹) {b : G} (hbQ : b ∈ Q) (hb3 : b ^ 3 = 1)
    (hmix : ∃ x ∈ D, (b * x) ^ 3 ≠ 1) : g * b * g⁻¹ ∈ Q := by
  have hδD := h.delta_mem hgY hgN hg hbQ
  have hbδ : b * (b⁻¹ * g * b * g⁻¹) = g * b * g⁻¹ := by group
  have hδ3 : (b * (b⁻¹ * g * b * g⁻¹)) ^ 3 = 1 := by
    rw [hbδ, conj_pow, hb3]; group
  have := h.mixed_mem hbQ hb3 hmix hδD hδ3
  rw [← hbδ]
  exact Q.mul_mem hbQ this

theorem quad_of_cube (h : TData A Q D M Y d e t₀) {b : G}
    (hb : b ∈ Subgroup.normalizer (D : Set G)) (hb3 : b ^ 3 = 1)
    (hcube : ∀ x ∈ D, (b * x) ^ 3 = 1) :
    ∀ x ∈ D, b * (b * x * b⁻¹ * x⁻¹) = (b * x * b⁻¹ * x⁻¹) * b := by
  intro x hx
  have hσ : ∀ z ∈ D, b * z * b⁻¹ ∈ D := fun z hz => (Subgroup.mem_normalizer_iff.mp hb z).mp hz
  have hs : b * x * b⁻¹ ∈ D := hσ x hx
  set s := b * x * b⁻¹ with hsdef
  have hs2 : b * s * b⁻¹ ∈ D := hσ s hs
  set s2 := b * s * b⁻¹ with hs2def
  have hphi : s * s2 * x = 1 := by
    have := hcube x hx
    rw [phi_eq hb3] at this
    exact this
  have hs2eq : s2 = s⁻¹ * x⁻¹ := by
    calc s2 = s⁻¹ * (s * s2 * x) * x⁻¹ := by group
      _ = s⁻¹ * x⁻¹ := by rw [hphi]; group
  have hs3 : s ^ 3 = 1 := h.hDe.2 s hs
  have hs3' : s * s * s = 1 := by rw [← pow_three']; exact hs3
  have hcomm : x⁻¹ * s⁻¹ = s⁻¹ * x⁻¹ := h.hDc _ (D.inv_mem hx) _ (D.inv_mem hs)
  have hss : s⁻¹ * s⁻¹ = s := by
    calc s⁻¹ * s⁻¹ = s⁻¹ * s⁻¹ * (s * s * s) := by rw [hs3', mul_one]
      _ = s := by group
  have hconj : b * (s * x⁻¹) * b⁻¹ = s * x⁻¹ := by
    calc b * (s * x⁻¹) * b⁻¹ = (b * s * b⁻¹) * (b * x * b⁻¹)⁻¹ := by group
      _ = s2 * s⁻¹ := by rw [← hsdef, ← hs2def]
      _ = (s⁻¹ * x⁻¹) * s⁻¹ := by rw [hs2eq]
      _ = s⁻¹ * (x⁻¹ * s⁻¹) := by group
      _ = s⁻¹ * (s⁻¹ * x⁻¹) := by rw [hcomm]
      _ = (s⁻¹ * s⁻¹) * x⁻¹ := by group
      _ = s * x⁻¹ := by rw [hss]
  have hfinal : b * (s * x⁻¹) = (s * x⁻¹) * b := by
    calc b * (s * x⁻¹) = (b * (s * x⁻¹) * b⁻¹) * b := by group
      _ = (s * x⁻¹) * b := by rw [hconj]
  calc b * (b * x * b⁻¹ * x⁻¹) = b * (s * x⁻¹) := by rw [hsdef]
    _ = (s * x⁻¹) * b := hfinal
    _ = (b * x * b⁻¹ * x⁻¹) * b := by rw [hsdef]

@[expose] def Quad (D : Subgroup G) (b : G) : Prop :=
  ∀ x ∈ D, b * (b * x * b⁻¹ * x⁻¹) = (b * x * b⁻¹ * x⁻¹) * b

theorem quad_e (h : TData A Q D M Y d e t₀) : Quad D e := by
  intro x hx
  have hm := h.hLA.hεM x hx
  have h1 := h.hLA.hMc _ hm
  calc e * (e * x * e⁻¹ * x⁻¹) = (e * (e * x * e⁻¹ * x⁻¹) * e⁻¹) * e := by group
    _ = (e * x * e⁻¹ * x⁻¹) * e := by rw [h1]

theorem hAc (h : TData A Q D M Y d e t₀) : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (h.hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem exists_b2 (h : TData A Q D M Y d e t₀) :
    ∃ b₂ ∈ A, b₂ ∉ Subgroup.zpowers e ⊔ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have heA := h.heA
  have he1 : e ≠ 1 := by
    rintro rfl; exact h.hed (Subgroup.one_mem _)
  have hecard : Nat.card (Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (h.hAe.2 e heA) he1]
  have hdcard : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (h.hAe.2 d h.hdA) h.hd1]
  have hN : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    intro x hx
    have hxA : x ∈ A := (Subgroup.zpowers_le.mpr h.hdA) hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hy : y ∈ Subgroup.zpowers e → y ∈ A := fun hy => (Subgroup.zpowers_le.mpr heA) hy
    constructor
    · intro hy'
      have := h.hAc x hxA y (hy hy')
      have e2 : x * y * x⁻¹ = y := by rw [this]; group
      rw [e2]; exact hy'
    · intro hxy
      have hyA : y ∈ A := by
        have : x * y * x⁻¹ ∈ A := (Subgroup.zpowers_le.mpr heA) hxy
        have h2 := A.mul_mem (A.mul_mem (A.inv_mem hxA) this) hxA
        have e1 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
        rwa [e1] at h2
      have := h.hAc x hxA y hyA
      have e2 : x * y * x⁻¹ = y := by rw [this]; group
      rwa [e2] at hxy
  have hm := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hN
  rw [hecard, hdcard] at hm
  have hle : Nat.card (Subgroup.zpowers e ⊔ Subgroup.zpowers d : Subgroup G) ≤ 9 := by
    have hpos : 0 < Nat.card (Subgroup.zpowers e ⊓ Subgroup.zpowers d : Subgroup G) :=
      Nat.card_pos
    nlinarith
  have hA : A ≤ Subgroup.zpowers e ⊔ Subgroup.zpowers d := fun x hx => hcon x hx
  have := Subgroup.card_le_of_le hA
  rw [h.hA27] at this
  omega

theorem Q_eq_sup (h : TData A Q D M Y d e t₀) : D ⊓ Q ⊔ A = Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M' := D ⊓ Q with hM'
  have hAN : A ≤ Subgroup.normalizer (M' : Set G) := by
    intro a ha
    have haQ : a ∈ Q := h.hAQ ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxD, hxQ⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (h.hQD haQ) x).mp hxD,
        Q.mul_mem (Q.mul_mem haQ hxQ) (Q.inv_mem haQ)⟩
    · rintro ⟨hxD, hxQ⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (h.hQD haQ) x).mpr hxD, ?_⟩
      have := Q.mul_mem (Q.mul_mem (Q.inv_mem haQ) hxQ) haQ
      simpa [mul_assoc] using this
  have hm := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hAN
  rw [h.card_QD.2, h.hA27] at hm
  have hinf : M' ⊓ A ≤ Subgroup.zpowers d := by
    intro x hx
    by_contra hxd
    have hxD : x ∈ D := hx.1.1
    have hle := h.hrank x hx.2 hxd D h.hD3 h.hDc
      (Item2119End8Proof.le_centralizer_of_mem h.hDc hxD)
    rw [h.hD81] at hle
    omega
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (h.hAe.2 d h.hdA) h.hd1]
  have hinf3 : Nat.card (M' ⊓ A : Subgroup G) ≤ 3 := by
    rw [← hd3]; exact Subgroup.card_le_of_le hinf
  have hsupQ : M' ⊔ A ≤ Q := sup_le inf_le_right h.hAQ
  have hcardsup : 243 ≤ Nat.card (M' ⊔ A : Subgroup G) := by
    have hpos : 0 < Nat.card (M' ⊔ A : Subgroup G) := Nat.card_pos
    nlinarith
  exact Subgroup.eq_of_le_of_card_ge hsupQ (by rw [h.hQ243]; exact hcardsup)

theorem not_quad_pair (h : TData A Q D M Y d e t₀) {b : G} (hbA : b ∈ A)
    (hbH : b ∉ Subgroup.zpowers e ⊔ Subgroup.zpowers d) : ¬ (Quad D b ∧ Quad D (e * b)) := by
  rintro ⟨hq, hq'⟩
  exact Item2119End8Proof.false_of_quadratic h.hAe h.hA27 h.hdA h.hd1 h.hQX h.hQS h.hAQ h.hQC
    h.hdc h.heA hbA h.hed hbH h.hDe h.hD81 h.hdD h.hQD h.quad_e hq hq' h.card_QD.1.le

theorem normalizes_Q (h : TData A Q D M Y d e t₀) {g : G} (hgY : g ∈ Y)
    (hgN : g ∈ Subgroup.normalizer ((Q ⊔ D : Subgroup G) : Set G))
    (hg : ∀ x ∈ D, g * x * g⁻¹ = x⁻¹) : g ∈ Subgroup.normalizer (Q : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b₂, hb₂A, hb₂H⟩ := h.exists_b2
  set H := Subgroup.zpowers e ⊔ Subgroup.zpowers d with hH
  have heH : e ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers e)
  have heA := h.heA
  have he3 : e * e * e = 1 := by rw [← pow_three']; exact h.hAe.2 e heA
  let S : Subgroup G := Q ⊓ Q.comap (MulAut.conj g).toMonoidHom
  have hmemS : ∀ x, x ∈ S ↔ x ∈ Q ∧ g * x * g⁻¹ ∈ Q := fun x => by
    simp [S, MulAut.conj_apply]
  have hMS : D ⊓ Q ≤ S := by
    intro m hm
    refine (hmemS m).mpr ⟨hm.2, ?_⟩
    rw [hg m hm.1]
    exact Q.inv_mem hm.2
  have hmixS : ∀ u ∈ A, ¬ Quad D u → u ∈ S := by
    intro u hu hnq
    have hu3 : u ^ 3 = 1 := h.hAe.2 u hu
    have hmix : ∃ x ∈ D, (u * x) ^ 3 ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hnq (h.quad_of_cube (h.hQD (h.hAQ hu)) hu3 hcon)
    exact (hmemS u).mpr ⟨h.hAQ hu, h.conj_mixed hgY hgN hg (h.hAQ hu) hu3 hmix⟩
  have hu1A : b₂ ∈ A := hb₂A
  have hu2A : e * b₂ ∈ A := A.mul_mem heA hb₂A
  have hu3A : e * (e * b₂) ∈ A := A.mul_mem heA hu2A
  have hu2H : e * b₂ ∉ H := fun hx => hb₂H (by
    have := H.mul_mem (H.inv_mem heH) hx
    simpa using this)
  have hu3H : e * (e * b₂) ∉ H := fun hx => hu2H (by
    have := H.mul_mem (H.inv_mem heH) hx
    simpa using this)
  have hq1 := h.not_quad_pair hu1A hb₂H
  have hq2 := h.not_quad_pair hu2A hu2H
  have hq3 := h.not_quad_pair hu3A hu3H
  have hu4 : e * (e * (e * b₂)) = b₂ := by
    calc e * (e * (e * b₂)) = (e * e * e) * b₂ := by group
      _ = b₂ := by rw [he3, one_mul]
  rw [hu4] at hq3
  have key : e ∈ S ∧ b₂ ∈ S := by
    by_cases hQ1 : Quad D b₂
    · have hn2 : ¬ Quad D (e * b₂) := fun hq => hq1 ⟨hQ1, hq⟩
      have hn3 : ¬ Quad D (e * (e * b₂)) := fun hq => hq3 ⟨hq, hQ1⟩
      have s2 := hmixS _ hu2A hn2
      have s3 := hmixS _ hu3A hn3
      have heS : e ∈ S := by
        have := S.mul_mem s3 (S.inv_mem s2)
        simpa [mul_assoc] using this
      refine ⟨heS, ?_⟩
      have := S.mul_mem (S.inv_mem heS) s2
      simpa using this
    · have s1 := hmixS _ hu1A hQ1
      by_cases hQ2 : Quad D (e * b₂)
      · have hn3 : ¬ Quad D (e * (e * b₂)) := fun hq => hq2 ⟨hQ2, hq⟩
        have s3 := hmixS _ hu3A hn3
        have hee : e * e ∈ S := by
          have := S.mul_mem s3 (S.inv_mem s1)
          simpa [mul_assoc] using this
        have heS : e ∈ S := by
          have := S.mul_mem hee hee
          have e4 : e * e * (e * e) = e := by
            calc e * e * (e * e) = (e * e * e) * e := by group
              _ = e := by rw [he3, one_mul]
          rwa [e4] at this
        exact ⟨heS, s1⟩
      · have s2 := hmixS _ hu2A hQ2
        have heS : e ∈ S := by
          have := S.mul_mem s2 (S.inv_mem s1)
          simpa [mul_assoc] using this
        exact ⟨heS, s1⟩
  have hdS : d ∈ S := hMS ⟨h.hdD, h.hAQ h.hdA⟩
  have hAS : A ≤ S := by
    rw [← Item2119End8Proof.sup_zpowers_eq h.hAe.2 h.hA27 h.hdA h.hd1 heA hb₂A h.hed hb₂H]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.zpowers_le.mpr key.1
    · exact Subgroup.zpowers_le.mpr hdS
    · exact Subgroup.zpowers_le.mpr key.2
  have hQS : Q ≤ S := by
    rw [← h.Q_eq_sup]
    exact sup_le hMS hAS
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  exact ((hmemS x).mp (hQS hx)).2

theorem exists_psi (h : TData A Q D M Y d e t₀) :
    ∀ m ∈ M, ∃ w ∈ D, e * w * e⁻¹ * w⁻¹ = m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLA := h.hLA
  have hσ : ∀ z ∈ D, e * z * e⁻¹ ∈ D := fun z hz => (Subgroup.mem_normalizer_iff.mp hLA.heN z).mp hz
  let ψ : D →* D :=
    { toFun := fun w => ⟨e * w * e⁻¹ * w⁻¹, D.mul_mem (hσ w w.2) (D.inv_mem w.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro w₁ w₂
        apply Subtype.ext
        have ha₁ : e * w₁ * e⁻¹ ∈ D := hσ w₁ w₁.2
        have ha₂ : e * w₂ * e⁻¹ ∈ D := hσ w₂ w₂.2
        have hcomm : (w₁ : G)⁻¹ * (e * w₂ * e⁻¹ * (w₂ : G)⁻¹) =
            (e * w₂ * e⁻¹ * (w₂ : G)⁻¹) * (w₁ : G)⁻¹ :=
          h.hDc _ (D.inv_mem w₁.2) _ (D.mul_mem ha₂ (D.inv_mem w₂.2))
        show e * ((w₁ : G) * w₂) * e⁻¹ * ((w₁ : G) * w₂)⁻¹ =
          (e * w₁ * e⁻¹ * (w₁ : G)⁻¹) * (e * w₂ * e⁻¹ * (w₂ : G)⁻¹)
        calc e * ((w₁ : G) * w₂) * e⁻¹ * ((w₁ : G) * w₂)⁻¹
            = (e * w₁ * e⁻¹) * ((e * w₂ * e⁻¹ * (w₂ : G)⁻¹) * (w₁ : G)⁻¹) := by group
          _ = (e * w₁ * e⁻¹) * ((w₁ : G)⁻¹ * (e * w₂ * e⁻¹ * (w₂ : G)⁻¹)) := by rw [hcomm]
          _ = (e * w₁ * e⁻¹ * (w₁ : G)⁻¹) * (e * w₂ * e⁻¹ * (w₂ : G)⁻¹) := by group }
  have hker : ψ.ker ≤ M.subgroupOf D := by
    intro w hw
    have hw1 : e * (w : G) * e⁻¹ * (w : G)⁻¹ = 1 := congrArg Subtype.val hw
    exact hLA.hkerM w w.2 hw1
  have hrange : ψ.range ≤ M.subgroupOf D := by
    rintro _ ⟨w, rfl⟩
    exact hLA.hεM w w.2
  have hMD := hLA.hMD
  have hM9 : Nat.card (M.subgroupOf D) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMD).toEquiv, hLA.hM9]
  have hk9 : Nat.card ψ.ker ≤ 9 := by rw [← hM9]; exact Subgroup.card_le_of_le hker
  have hr9 : Nat.card ψ.range ≤ 9 := by rw [← hM9]; exact Subgroup.card_le_of_le hrange
  have hprod := Subgroup.card_ker_mul_card_range ψ
  have hD' : Nat.card D = 81 := h.hD81
  rw [hD'] at hprod
  have hr : Nat.card ψ.range = 9 := by nlinarith
  have heq : ψ.range = M.subgroupOf D :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hr, hM9])
  intro m hm
  have hmem : (⟨m, hMD hm⟩ : D) ∈ M.subgroupOf D := hm
  rw [← heq] at hmem
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

theorem exists_w (h : TData A Q D M Y d e t₀) {g : G} (hgY : g ∈ Y)
    (hg : ∀ x ∈ D, g * x * g⁻¹ = x⁻¹) :
    ∃ w ∈ D, (w * g * w⁻¹) * e * (w * g * w⁻¹)⁻¹ = e := by
  have hLA := h.hLA
  obtain ⟨h₀, hh₀M, hh₀⟩ := hLA.hcent g hgY
  have hh₀D : h₀ ∈ D := hLA.hMD hh₀M
  obtain ⟨w, hwD, hw⟩ := h.exists_psi h₀⁻¹ (M.inv_mem hh₀M)
  have hhD : h₀⁻¹ ∈ D := D.inv_mem hh₀D
  have hwh : w * h₀⁻¹ = h₀⁻¹ * w := h.hDc _ hwD _ hhD
  have hwh0 : w * h₀ = h₀ * w := h.hDc _ hwD _ hh₀D
  have hew : e * w = h₀⁻¹ * w * e := by
    calc e * w = (e * w * e⁻¹ * w⁻¹) * w * e := by group
      _ = h₀⁻¹ * w * e := by rw [hw]
  have hE1 : w⁻¹ * e * w = h₀⁻¹ * e := by
    calc w⁻¹ * e * w = w⁻¹ * (e * w) := by group
      _ = w⁻¹ * (h₀⁻¹ * w * e) := by rw [hew]
      _ = (w⁻¹ * h₀⁻¹ * w) * e := by group
      _ = h₀⁻¹ * e := by
        have : w⁻¹ * h₀⁻¹ * w = h₀⁻¹ := by
          calc w⁻¹ * h₀⁻¹ * w = w⁻¹ * (h₀⁻¹ * w) := by group
            _ = w⁻¹ * (w * h₀⁻¹) := by rw [hwh]
            _ = h₀⁻¹ := by group
        rw [this]
  have hE2 : w * e * w⁻¹ = h₀ * e := by
    calc w * e * w⁻¹ = h₀ * (w * (h₀⁻¹ * e) * w⁻¹) := by
          calc w * e * w⁻¹ = h₀ * (h₀⁻¹ * (w * e * w⁻¹)) := by group
            _ = h₀ * (w * (h₀⁻¹ * e) * w⁻¹) := by
              congr 1
              calc h₀⁻¹ * (w * e * w⁻¹) = (h₀⁻¹ * w) * e * w⁻¹ := by group
                _ = (w * h₀⁻¹) * e * w⁻¹ := by rw [hwh]
                _ = w * (h₀⁻¹ * e) * w⁻¹ := by group
      _ = h₀ * (w * (w⁻¹ * e * w) * w⁻¹) := by rw [hE1]
      _ = h₀ * e := by group
  have hMc : e * h₀ = h₀ * e := by
    calc e * h₀ = (e * h₀ * e⁻¹) * e := by group
      _ = h₀ * e := by rw [hLA.hMc h₀ hh₀M]
  have hh3 : h₀ ^ 3 = 1 := h.hDe.2 h₀ hh₀D
  have hh3' : h₀ * h₀ * h₀ = 1 := by rw [← pow_three']; exact hh3
  refine ⟨w, hwD, ?_⟩
  have hginv : g * h₀⁻¹ * g⁻¹ = h₀ := by
    have := hg h₀⁻¹ hhD
    simpa using this
  calc (w * g * w⁻¹) * e * (w * g * w⁻¹)⁻¹
      = w * g * (w⁻¹ * e * w) * g⁻¹ * w⁻¹ := by group
    _ = w * g * (h₀⁻¹ * e) * g⁻¹ * w⁻¹ := by rw [hE1]
    _ = w * ((g * h₀⁻¹ * g⁻¹) * (g * e * g⁻¹)) * w⁻¹ := by group
    _ = w * (h₀ * (e * h₀)) * w⁻¹ := by rw [hginv, hh₀]
    _ = (w * h₀ * w⁻¹) * ((w * e * w⁻¹) * (w * h₀ * w⁻¹)) := by group
    _ = h₀ * ((h₀ * e) * h₀) := by
        have e1 : w * h₀ * w⁻¹ = h₀ := by rw [hwh0]; group
        rw [e1, hE2]
    _ = (h₀ * h₀ * h₀) * e := by
        calc h₀ * ((h₀ * e) * h₀) = h₀ * (h₀ * (e * h₀)) := by group
          _ = h₀ * (h₀ * (h₀ * e)) := by rw [hMc]
          _ = (h₀ * h₀ * h₀) * e := by group
    _ = e := by rw [hh3', one_mul]

theorem exists_t' (h : TData A Q D M Y d e t₀) :
    ∃ t : G, t ∈ Y ∧ t ∈ Subgroup.normalizer ((Q ⊔ D : Subgroup G) : Set G) ∧
      t ∈ Subgroup.normalizer (Q : Set G) ∧ t ∈ Subgroup.centralizer ({e} : Set G) ∧
      (∃ k : ℕ, t ^ (2 ^ k) = 1) ∧ ∀ x ∈ D, t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨g, hgY, hgN, hg⟩ := h.exists_g
  have hgQ := h.normalizes_Q hgY hgN hg
  obtain ⟨w, hwD, hwe⟩ := h.exists_w hgY hg
  set g' := w * g * w⁻¹ with hg'def
  have hwQ : w ∈ Subgroup.normalizer (Q : Set G) := h.hP'N (Subgroup.mem_sup_right hwD)
  have hg'Q : g' ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).mul_mem
      ((Subgroup.normalizer (Q : Set G)).mul_mem hwQ hgQ)
      ((Subgroup.normalizer (Q : Set G)).inv_mem hwQ)
  have hg'D : ∀ x ∈ D, g' * x * g'⁻¹ = x⁻¹ := by
    intro x hx
    have hwx : w⁻¹ * x * w = x := by
      have := h.hDc _ (D.inv_mem hwD) _ hx
      calc w⁻¹ * x * w = x * w⁻¹ * w := by rw [this]
        _ = x := by group
    calc g' * x * g'⁻¹ = w * g * (w⁻¹ * x * w) * g⁻¹ * w⁻¹ := by rw [hg'def]; group
      _ = w * (g * x * g⁻¹) * w⁻¹ := by rw [hwx]; group
      _ = w * x⁻¹ * w⁻¹ := by rw [hg x hx]
      _ = x⁻¹ := by
        have := h.hDc _ hwD _ (D.inv_mem hx)
        rw [this]; group
  have hg'e : g' ∈ Subgroup.centralizer ({e} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g' * e = (g' * e * g'⁻¹) * g' := by group
      _ = e * g' := by rw [hwe]
  have hg'g : g' * g' ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hconj2 : (g' * g') * x * (g' * g')⁻¹ = x := by
      calc (g' * g') * x * (g' * g')⁻¹ = g' * (g' * x * g'⁻¹) * g'⁻¹ := by group
        _ = g' * x⁻¹ * g'⁻¹ := by rw [hg'D x hx]
        _ = (x⁻¹)⁻¹ := hg'D x⁻¹ (D.inv_mem hx)
        _ = x := inv_inv x
    calc x * (g' * g') = ((g' * g') * x * (g' * g')⁻¹) * (g' * g') := by rw [hconj2]
      _ = (g' * g') * x := by group
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g').ne'
  obtain ⟨j, hj⟩ := hm
  have hg'Y : g' ∈ Y := Y.mul_mem (Y.mul_mem (h.hDY hwD) hgY) (Y.inv_mem (h.hDY hwD))
  have hg'P : g' ∈ Subgroup.normalizer ((Q ⊔ D : Subgroup G) : Set G) :=
    (Subgroup.normalizer ((Q ⊔ D : Subgroup G) : Set G)).mul_mem
      ((Subgroup.normalizer ((Q ⊔ D : Subgroup G) : Set G)).mul_mem
        (Subgroup.le_normalizer (Subgroup.mem_sup_right hwD)) hgN)
      ((Subgroup.normalizer ((Q ⊔ D : Subgroup G) : Set G)).inv_mem
        (Subgroup.le_normalizer (Subgroup.mem_sup_right hwD)))
  refine ⟨g' ^ m, Y.pow_mem hg'Y m, Subgroup.pow_mem _ hg'P m, Subgroup.pow_mem _ hg'Q m,
    Subgroup.pow_mem _ hg'e m, ⟨k, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm m (2 ^ k), ← hn]
    exact pow_orderOf_eq_one g'
  · intro x hx
    have ht : g' ^ m = (g' * g') ^ j * g' := by rw [hj, pow_succ, pow_mul, sq]
    have hc : (g' * g') ^ j ∈ Subgroup.centralizer (D : Set G) := Subgroup.pow_mem _ hg'g j
    have hcx : ∀ y ∈ D, (g' * g') ^ j * y * ((g' * g') ^ j)⁻¹ = y := by
      intro y hy
      have := Subgroup.mem_centralizer_iff.mp hc y hy
      calc (g' * g') ^ j * y * ((g' * g') ^ j)⁻¹ = (y * (g' * g') ^ j) * ((g' * g') ^ j)⁻¹ := by
            rw [this]
        _ = y := by group
    rw [ht]
    calc (g' * g') ^ j * g' * x * ((g' * g') ^ j * g')⁻¹
        = (g' * g') ^ j * (g' * x * g'⁻¹) * ((g' * g') ^ j)⁻¹ := by group
      _ = (g' * g') ^ j * x⁻¹ * ((g' * g') ^ j)⁻¹ := by rw [hg'D x hx]
      _ = x⁻¹ := hcx _ (D.inv_mem hx)

end TData

end CFSG.RankThree.PartTwo.Sec21.Hering2119S

