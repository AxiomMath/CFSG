module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81Sec44
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42B
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32A
import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
import CFSG.RankThree.PartOne.KE8F.HyperGen

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem opp_coprime (b : G) : Nat.Coprime (Nat.card (Opp 3 (Cen b))) 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Opp, CFSG.inSubgroup, Subgroup.card_map_of_injective (Cen b).subtype_injective]
  exact Nat.Coprime.symm CFSG.pPrimeCore_coprime_card

theorem opp_conj {g o : G} (hg : g ∈ Cen b) (ho : o ∈ Opp 3 (Cen b)) :
    g * o * g⁻¹ ∈ Opp 3 (Cen b) :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  inSubgroup_conj_mem (CFSG.pPrimeCore_normal (p := 3) (G := ↥(Cen b))) hg ho

theorem opp_le_cen (b : G) : Opp 3 (Cen b) ≤ Cen b := Subgroup.map_subtype_le _

theorem eq_one_of_dvd_three_pow {o : G} {k m : ℕ} (hk : o ^ 3 ^ k = 1) (hm : orderOf o ∣ m)
    (hco : Nat.Coprime m 3) : o = 1 :=
  orderOf_eq_one_iff.mp (((Nat.Coprime.pow_right k hco).coprime_dvd_left hm).eq_one_of_dvd
    (orderOf_dvd_of_pow_eq_one hk))

theorem orderOf_dvd_card_opp {o : G} (ho : o ∈ Opp 3 (Cen b)) :
    orderOf o ∣ Nat.card (Opp 3 (Cen b)) :=
  Subgroup.orderOf_dvd_natCard _ ho

theorem pow_card_opp {o : G} (ho : o ∈ Opp 3 (Cen b)) : o ^ Nat.card (Opp 3 (Cen b)) = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_card_opp ho)

theorem FF81Basis.opp_eq_one (hB : FF81Basis b L B b₁ b₂ b₃) {o l : G} {j : ℕ}
    (ho : o ∈ Opp 3 (Cen b)) (hl : l ∈ L) (h : o = b ^ j * l) : o = 1 := by
  have hlc : l ∈ L ⊓ CenS L := by
    refine ⟨hl, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h1 : Commute y o := (hB.opp_comm ho hy).symm
    have h2 : Commute y (b ^ j) := (Commute.pow_left (hB.b_comm hy) j).symm
    have hl' : l = (b ^ j)⁻¹ * o := by rw [h]; group
    rw [hl']
    exact (h2.inv_right.mul_right h1).eq
  rw [hB.inf_cenS_self, Subgroup.mem_bot] at hlc
  rw [hlc, mul_one] at h
  refine eq_one_of_dvd_three_pow (k := 1) ?_ (orderOf_dvd_card_opp ho) (opp_coprime b)
  rw [h, pow_one, ← pow_mul, mul_comm, pow_mul, hB.hyp.b_cube, one_pow]

theorem FF81Basis.B_comm (hB : FF81Basis b L B b₁ b₂ b₃) {x y : G} (hx : x ∈ B) (hy : y ∈ B) :
    x * y = y * x :=
  comm_of_isElemAb hB.mono.1 x hx y hy

theorem FF81Basis.B_cube (hB : FF81Basis b L B b₁ b₂ b₃) {x : G} (hx : x ∈ B) : x ^ 3 = 1 :=
  haveI := hB.mono.1.1
  CFSG.elemPow_eq_one_of_isElementaryAbelian x hx

theorem FF81Basis.mem_B (hB : FF81Basis b L B b₁ b₂ b₃) {x : G}
    (hx : x ∈ ({b, b₁, b₂, b₃} : Set G)) : x ∈ B := by
  rw [hB.mono.2.1]; exact Subgroup.subset_closure hx

theorem FF81Basis.B₁_le_B (hB : FF81Basis b L B b₁ b₂ b₃) :
    Subgroup.closure {b₁, b₂, b₃} ≤ B :=
  (Subgroup.closure_le _).mpr fun x hx => hB.mem_B (by
    rcases hx with rfl | rfl | rfl <;> simp)

theorem FF81Basis.B₁_le_L (hB : FF81Basis b L B b₁ b₂ b₃) :
    Subgroup.closure {b₁, b₂, b₃} ≤ L :=
  (Subgroup.closure_le _).mpr fun x hx => by
    rcases hx with rfl | rfl | rfl
    exacts [hB.hb₁, hB.hb₂, hB.hb₃]

theorem FF81Basis.opp_part_eq_one (hB : FF81Basis b L B b₁ b₂ b₃) {o l y : G} {i : ℤ}
    (ho : o ∈ Opp 3 (Cen b)) (hl : l ∈ L) (hy : y = o * b ^ i * l) (hy3 : y ^ 3 = 1) :
    o = 1 := by
  have hc : o * (b ^ i * l) = (b ^ i * l) * o := by
    have h1 : o * b ^ i = b ^ i * o :=
      (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (opp_le_cen b ho)) i).eq
    rw [← mul_assoc, h1, mul_assoc, hB.opp_comm ho hl, mul_assoc]
  have h3 : o ^ 3 * (b ^ i * l) ^ 3 = 1 := by
    rw [← (Commute.mul_pow hc 3), ← mul_assoc, ← hy, hy3]
  have hbl : (b ^ i * l) ^ 3 = l ^ 3 := by
    rw [(Commute.mul_pow ((Commute.zpow_left (hB.b_comm hl) i)) 3), ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hB.hyp.b_cube, one_zpow, one_mul]
  rw [hbl] at h3
  have ho3 : o ^ 3 = 1 := by
    have hmem : o ^ 3 ∈ Opp 3 (Cen b) := Subgroup.pow_mem _ ho 3
    exact hB.opp_eq_one (j := 0) hmem (L.inv_mem (L.pow_mem hl 3))
      (by rw [pow_zero, one_mul]; exact eq_inv_of_mul_eq_one_left h3)
  exact eq_one_of_dvd_three_pow (k := 1) (by rw [pow_one]; exact ho3) (orderOf_dvd_card_opp ho)
    (opp_coprime b)

theorem FF81Basis.conj_opp_mem (hB : FF81Basis b L B b₁ b₂ b₃) {g o : G}
    (hg : g * b * g⁻¹ ∈ B) (ho : o ∈ Opp 3 (Cen b)) : g * o * g⁻¹ ∈ Opp 3 (Cen b) := by
  set o' := g * o * g⁻¹ with ho'
  have hcomm : ∀ β ∈ B, o' * β = β * o' := by
    intro β hβ
    have hy : g⁻¹ * β * g ∈ Cen b := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hB.B_comm hβ hg
      calc g⁻¹ * β * g * b = g⁻¹ * (β * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * b * g⁻¹) * β) * g := by rw [h]
        _ = b * (g⁻¹ * β * g) := by group
    obtain ⟨o₁, ho₁, i, l, hl, hdec⟩ := hB.cen_dec hy
    have hy3 : (g⁻¹ * β * g) ^ 3 = 1 := by
      rw [show g⁻¹ * β * g = MulAut.conj g⁻¹ β by simp [MulAut.conj_apply], ← map_pow,
        hB.B_cube hβ, map_one]
    have h1 := hB.opp_part_eq_one ho₁ hl hdec hy3
    rw [h1, one_mul] at hdec
    have hoy : o * (g⁻¹ * β * g) = (g⁻¹ * β * g) * o := by
      rw [hdec, ← mul_assoc,
        (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (opp_le_cen b ho)) i).eq,
        mul_assoc, hB.opp_comm ho hl, mul_assoc]
    calc o' * β = g * (o * (g⁻¹ * β * g)) * g⁻¹ := by rw [ho']; group
      _ = g * ((g⁻¹ * β * g) * o) * g⁻¹ := by rw [hoy]
      _ = β * o' := by rw [ho']; group
  have hob : o' ∈ Cen b :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm b (hB.mem_B (by simp)))
  obtain ⟨o₂, ho₂, j, l₂, hl₂, hdec⟩ := hB.cen_dec hob
  have hl₂B : l₂ ∈ B := by
    have : l₂ ∈ L ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) := by
      refine ⟨hl₂, Subgroup.mem_centralizer_iff.mpr fun β hβ => ?_⟩
      have hβL := hB.B₁_le_L hβ
      have h1 : Commute β o' := (hcomm β (hB.B₁_le_B hβ)).symm
      have h2 : Commute β o₂ := (hB.opp_comm ho₂ hβL).symm
      have h3 : Commute β (b ^ j) := (Commute.zpow_left (hB.b_comm hβL) j).symm
      have hl : l₂ = (o₂ * b ^ j)⁻¹ * o' := by rw [hdec]; group
      rw [hl]
      exact ((h2.mul_right h3).inv_right.mul_right h1).eq
    rw [hB.selfcen] at this
    exact hB.B₁_le_B this
  have hvB : b ^ j * l₂ ∈ B := B.mul_mem (B.zpow_mem (hB.mem_B (by simp)) j) hl₂B
  have hv : o' = o₂ * (b ^ j * l₂) := by rw [hdec, mul_assoc]
  have hc₂ : Commute o₂ (b ^ j * l₂) :=
    (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (opp_le_cen b ho₂)) j).mul_right
      (hB.opp_comm ho₂ hl₂)
  have ho'm : o' ^ Nat.card (Opp 3 (Cen b)) = 1 := by
    rw [ho', show g * o * g⁻¹ = MulAut.conj g o by simp [MulAut.conj_apply], ← map_pow,
      pow_card_opp ho, map_one]
  have hvm : (b ^ j * l₂) ^ Nat.card (Opp 3 (Cen b)) = 1 := by
    have hv' : b ^ j * l₂ = o₂⁻¹ * o' := by rw [hv]; group
    have hc : Commute o₂⁻¹ o' := by
      rw [hv]; exact (Commute.refl o₂).inv_left.mul_right hc₂.inv_left
    rw [hv', hc.mul_pow, inv_pow, pow_card_opp ho₂, ho'm, inv_one, one_mul]
  have hv1 : b ^ j * l₂ = 1 := eq_one_of_dvd_three_pow (k := 1)
    (by rw [pow_one]; exact hB.B_cube hvB) (orderOf_dvd_of_pow_eq_one hvm) (opp_coprime b)
  rw [hv, hv1, mul_one]; exact ho₂

theorem FF81Basis.conj_opp_eq (hB : FF81Basis b L B b₁ b₂ b₃) {g : G} (hg : g * b * g⁻¹ ∈ B) :
    conjBy g (Opp 3 (Cen b)) = Opp 3 (Cen b) :=
  Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨o, ho, rfl⟩; exact hB.conj_opp_mem hg ho)
    (by rw [card_conjBy])

theorem FF81Basis.opp_conj_of_cen (hB : FF81Basis b L B b₁ b₂ b₃) {g c o : G}
    (hg : g * b * g⁻¹ ∈ B) (hc : c ∈ Cen (g * b * g⁻¹)) (ho : o ∈ Opp 3 (Cen b)) :
    c * o * c⁻¹ ∈ Opp 3 (Cen b) := by
  have ho' : o ∈ conjBy g (Opp 3 (Cen b)) := (hB.conj_opp_eq hg).symm ▸ ho
  obtain ⟨z, hz, rfl⟩ := ho'
  have hy : g⁻¹ * c * g ∈ Cen b := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    calc g⁻¹ * c * g * b = g⁻¹ * (c * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * c) * g := by rw [hc]
      _ = b * (g⁻¹ * c * g) := by group
  have := hB.conj_opp_mem hg (opp_conj hy hz)
  show c * (g * z * g⁻¹) * c⁻¹ ∈ _
  convert this using 1
  group

variable {t₀ s₀ : G}

theorem FF81Sec5.A₁_le_B (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) :
    Subgroup.closure {b, b₁, b₂ * b₃} ≤ B :=
  (Subgroup.closure_le _).mpr fun x hx => by
    rcases hx with rfl | rfl | rfl
    · exact h5.basis.mem_B (by simp)
    · exact h5.basis.mem_B (by simp)
    · exact B.mul_mem (h5.basis.mem_B (by simp)) (h5.basis.mem_B (by simp))

theorem FF81Sec5.mono4 (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) :
    HasMonomial4 B b b₁ b₂ b₃ ∧ ∃ n ∈ Nor B, n * b * n⁻¹ = b * b₁ * b₂ * b₃ := by
  rcases h5.caseII with h | h
  exacts [⟨h.1, h.2.2.2⟩, ⟨h.1, h.2.2.2⟩]

theorem conj_mul4 (g a c d e : G) :
    g * (a * c * d * e) * g⁻¹ = (g * a * g⁻¹) * (g * c * g⁻¹) * (g * d * g⁻¹) * (g * e * g⁻¹) := by
  group

theorem conj_inv' (g x : G) : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group

theorem conj_conj (g h x : G) : (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group

theorem key_zmod3 : ∀ u v w : Multiplicative (ZMod 3), u = 1 ∨ v = 1 ∨ u * v * w = 1 ∨
    u * v⁻¹ * w = 1 ∨ u⁻¹ * v * w = 1 ∨ u⁻¹ * v⁻¹ * w = 1 := by decide

theorem FF81Sec5.exists_conj_mem (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
    (Γ : Subgroup ↥(Subgroup.closure ({b, b₁, b₂ * b₃} : Set G))) (hΓ : Γ.index = 3) :
    ∃ g : G, g * b * g⁻¹ ∈ Γ.map (Subgroup.closure ({b, b₁, b₂ * b₃} : Set G)).subtype := by
  have hB := h5.basis
  have hA₁B := h5.A₁_le_B
  have hcomm : ∀ x y : ↥(Subgroup.closure ({b, b₁, b₂ * b₃} : Set G)), x * y = y * x := fun x y =>
    Subtype.ext (hB.B_comm (hA₁B x.2) (hA₁B y.2))
  haveI : Γ.Normal := ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A₁ := Subgroup.closure ({b, b₁, b₂ * b₃} : Set G)
  let e : A₁ ⧸ Γ ≃* Multiplicative (ZMod 3) :=
    mulEquivOfPrimeCardEq (p := 3) (by rw [← Subgroup.index_eq_card, hΓ]) (by simp)
  let φ : A₁ →* Multiplicative (ZMod 3) := e.toMonoidHom.comp (QuotientGroup.mk' Γ)
  have hφ : ∀ a : A₁, φ a = 1 → (a : G) ∈ Γ.map A₁.subtype := fun a ha => by
    have h1 : (QuotientGroup.mk' Γ a) = 1 := e.injective (by rw [map_one]; exact ha)
    exact ⟨a, (QuotientGroup.eq_one_iff a).mp h1, rfl⟩
  let u : A₁ := ⟨b, Subgroup.subset_closure (by simp)⟩
  let v : A₁ := ⟨b₁, Subgroup.subset_closure (by simp)⟩
  let w : A₁ := ⟨b₂ * b₃, Subgroup.subset_closure (by simp)⟩
  obtain ⟨hM, n, -, hn⟩ := h5.mono4
  obtain ⟨τ, -, hτ, -⟩ := hM.2.2.2.1
  obtain ⟨n₀, -, h₀b, h₀1, h₀2, h₀3⟩ := hB.mono.2.2.1
  obtain ⟨n₁, -, h₁b, h₁1, h₁2, h₁3⟩ := hB.mono.2.2.2.1
  have e1 : (n₁ * n) * b * (n₁ * n)⁻¹ = b * b₁⁻¹ * (b₂ * b₃) := by
    rw [conj_conj, hn, conj_mul4, h₁b, h₁1, h₁2, h₁3, mul_assoc _ b₂]
  have e2 : (n₀ * n) * b * (n₀ * n)⁻¹ = b⁻¹ * b₁ * (b₂ * b₃) := by
    rw [conj_conj, hn, conj_mul4, h₀b, h₀1, h₀2, h₀3, mul_assoc _ b₂]
  have e3 : (n₀ * (n₁ * n)) * b * (n₀ * (n₁ * n))⁻¹ = b⁻¹ * b₁⁻¹ * (b₂ * b₃) := by
    rw [conj_conj, conj_conj, hn, conj_mul4, h₁b, h₁1, h₁2, h₁3, conj_mul4, h₀b, conj_inv', h₀1,
      h₀2, h₀3, mul_assoc _ b₂]
  rcases key_zmod3 (φ u) (φ v) (φ w) with h | h | h | h | h | h
  · exact ⟨1, by rw [one_mul, inv_one, mul_one]; exact hφ u h⟩
  · exact ⟨τ, by rw [hτ]; exact hφ v h⟩
  · refine ⟨n, ?_⟩
    rw [hn, mul_assoc _ b₂]
    exact hφ (u * v * w) (by rw [map_mul, map_mul]; exact h)
  · refine ⟨n₁ * n, ?_⟩
    rw [e1]
    exact hφ (u * v⁻¹ * w) (by rw [map_mul, map_mul, map_inv]; exact h)
  · refine ⟨n₀ * n, ?_⟩
    rw [e2]
    exact hφ (u⁻¹ * v * w) (by rw [map_mul, map_mul, map_inv]; exact h)
  · refine ⟨n₀ * (n₁ * n), ?_⟩
    rw [e3]
    exact hφ (u⁻¹ * v⁻¹ * w) (by rw [map_mul, map_mul, map_inv, map_inv]; exact h)

theorem FF81Sec5.opp_comm_op_two (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {Γ : Subgroup G}
    (hΓ : Γ ≤ Subgroup.closure {b, b₁, b₂ * b₃}) {g : G} (hg : g * b * g⁻¹ ∈ Γ) {o u : G}
    (ho : o ∈ Opp 3 (Cen b)) (hu : u ∈ Op 2 (Cen s₀) ⊓ CenS Γ) : o * u = u * o := by
  have hB := h5.basis
  have hoA : Subgroup.closure {b, b₁, b₂ * b₃} ≤ Cen o := (Subgroup.closure_le _).mpr fun x hx => by
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hx with rfl | rfl | rfl
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (opp_le_cen x ho)).symm
    · exact (hB.opp_comm ho hB.hb₁).symm
    · exact (hB.opp_comm ho (L.mul_mem hB.hb₂ hB.hb₃)).symm
  have hos : o ∈ Cen s₀ := Subgroup.mem_centralizer_singleton_iff.mpr (hB.opp_comm ho h5.hs₀L)
  have hgB : g * b * g⁻¹ ∈ B := h5.A₁_le_B (hΓ hg)
  have huc : u ∈ Cen (g * b * g⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hu.2 _ hg).symm
  have hk1 : o * u * o⁻¹ * u⁻¹ ∈ Op 2 (Cen s₀) :=
    Subgroup.mul_mem _ (op_two_conj hos hu.1) (Subgroup.inv_mem _ hu.1)
  have hk2 : o * u * o⁻¹ * u⁻¹ ∈ Opp 3 (Cen b) := by
    rw [show o * u * o⁻¹ * u⁻¹ = o * (u * o⁻¹ * u⁻¹) by group]
    exact Subgroup.mul_mem _ ho (hB.opp_conj_of_cen hgB huc (Subgroup.inv_mem _ ho))
  obtain ⟨n, hn⟩ := op_two_isPGroup s₀ ⟨_, hk1⟩
  have hk : o * u * o⁻¹ * u⁻¹ = 1 :=
    eq_one_of_pow_two_of_odd (by simpa using congrArg Subtype.val hn) (orderOf_dvd_card_opp hk2)
      hB.o3odd
  rwa [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hk

theorem FF81Sec5.opp_eq_bot (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) : Opp 3 (Cen b) = ⊥ := by
  have hB := h5.basis
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A₁ := Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) with hA₁
  set S := Op 2 (Cen s₀) with hS
  have hA₁B := h5.A₁_le_B
  haveI : IsElementaryAbelian 3 A₁ :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hB.B_comm (hA₁B x.2) (hA₁B y.2))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (by simpa using hB.B_cube (hA₁B x.2)) }
  haveI : Nontrivial A₁ := ⟨⟨⟨b, Subgroup.subset_closure (by simp)⟩, 1,
    fun h => hB.hyp.b_ne_one (congrArg Subtype.val h)⟩⟩
  have hAV : A₁ ≤ Subgroup.normalizer (S : Set G) := fun a ha =>
    Subgroup.mem_normalizer_fintype fun _ hu => op_two_conj
      (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp h5.hs₀A a ha)) hu
  have hVp : ¬ 3 ∣ Nat.card S := by
    obtain ⟨k, hk⟩ := (op_two_isPGroup s₀).exists_card_eq
    rw [hk]
    exact fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hle : S ≤ CenS (Opp 3 (Cen b)) := by
    refine (CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers hAV hVp).trans
      (iSup₂_le fun Γ hΓ => ?_)
    obtain ⟨g, hg⟩ := h5.exists_conj_mem Γ hΓ
    exact fun u hu => Subgroup.mem_centralizer_iff.mpr fun o ho =>
      h5.opp_comm_op_two (Subgroup.map_subtype_le Γ) hg ho hu
  refine eq_bot_iff.mpr fun o ho => ?_
  have hos : o ∈ Cen s₀ := Subgroup.mem_centralizer_singleton_iff.mpr (hB.opp_comm ho h5.hs₀L)
  have hoS : o ∈ S := hB.mem_op_two_of_comm h5.hs₀ hos fun u hu =>
    Subgroup.mem_centralizer_iff.mp (hle hu) o ho
  obtain ⟨n, hn⟩ := op_two_isPGroup s₀ ⟨o, hoS⟩
  exact Subgroup.mem_bot.mpr (eq_one_of_pow_two_of_odd (by simpa using congrArg Subtype.val hn)
    (orderOf_dvd_card_opp ho) hB.o3odd)

end CFSG.RankThree.PartTwo.Sec21.FF81
