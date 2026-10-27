module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreModel
public import CFSG.RankThree.PartTwo.Sec21.FF84S47Transport
public import CFSG.RankThree.PartTwo.Sec21.FF84S49AGen
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Inputs
public import CFSG.Sporadic.Schreier.J4SSylowBase


public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {b : G} {L B K : Subgroup G} {b₁ b₂ : G}

theorem b_cube (h : FF84Post b L B K b₁ b₂) : b ^ 3 = 1 :=
  pow3_of_mem h.sec (mem_b h.sec)

theorem P4_inv_elt (h : FF84Post b L B K b₁ b₂) :
    ∃ s : G, orderOf s = 2 ∧ s ∈ Nor B ∧ s * b * s⁻¹ = b⁻¹ ∧
      s ∈ CenS (Subgroup.closure {b₁, b₂}) := by
  obtain ⟨-, hBgen, -, ⟨n, hn, hnb, hnb₁, hnb₂⟩, -⟩ := h.sec.mono
  have e1 : n * b = b⁻¹ * n := by
    calc n * b = (n * b * n⁻¹) * n := by group
      _ = b⁻¹ * n := by rw [hnb]
  have e1' : n * b⁻¹ = b * n := by
    have : n * b⁻¹ * n⁻¹ = b := by
      rw [show n * b⁻¹ * n⁻¹ = (n * b * n⁻¹)⁻¹ by group, hnb, inv_inv]
    calc n * b⁻¹ = (n * b⁻¹ * n⁻¹) * n := by group
      _ = b * n := by rw [this]
  have e2 : n * b₁ = b₁ * n := by
    calc n * b₁ = (n * b₁ * n⁻¹) * n := by group
      _ = b₁ * n := by rw [hnb₁]
  have e3 : n * b₂ = b₂ * n := by
    calc n * b₂ = (n * b₂ * n⁻¹) * n := by group
      _ = b₂ * n := by rw [hnb₂]
  have hb2 : n * n * b = b * (n * n) := by
    calc n * n * b = n * (n * b) := by group
      _ = n * (b⁻¹ * n) := by rw [e1]
      _ = (n * b⁻¹) * n := by group
      _ = (b * n) * n := by rw [e1']
      _ = b * (n * n) := by group
  have hb12 : n * n * b₁ = b₁ * (n * n) := by
    calc n * n * b₁ = n * (n * b₁) := by group
      _ = n * (b₁ * n) := by rw [e2]
      _ = (n * b₁) * n := by group
      _ = (b₁ * n) * n := by rw [e2]
      _ = b₁ * (n * n) := by group
  have hb22 : n * n * b₂ = b₂ * (n * n) := by
    calc n * n * b₂ = n * (n * b₂) := by group
      _ = n * (b₂ * n) := by rw [e3]
      _ = (n * b₂) * n := by group
      _ = (b₂ * n) * n := by rw [e3]
      _ = b₂ * (n * n) := by group
  have hBle : B ≤ Cen (n * n) := by
    rw [hBgen, Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hx with rfl | rfl | rfl
    · exact hb2.symm
    · exact hb12.symm
    · exact hb22.symm
  have hn2 : n * n ∈ CenS B := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.1 (hBle hy)
  rw [h.cB] at hn2
  have hn6 : (n * n) ^ 3 = 1 := pow3_of_mem h.sec hn2
  have hs2 : n * n * n * (n * n * n) = 1 := by
    calc n * n * n * (n * n * n) = (n * n) ^ 3 := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hn6
  have hsb : n * n * n * b * (n * n * n)⁻¹ = b⁻¹ := by
    calc n * n * n * b * (n * n * n)⁻¹ = n * (n * n * b * (n * n)⁻¹) * n⁻¹ := by group
      _ = n * b * n⁻¹ := by rw [hb2]; group
      _ = b⁻¹ := hnb
  have hs1 : n * n * n ≠ 1 := by
    intro h1
    rw [h1] at hsb
    have hb' : b * b = 1 := by
      have : b = b⁻¹ := by simpa using hsb
      calc b * b = b * b⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel b
    apply b_ne_one h.sec
    have h3 := b_cube h
    calc b = b ^ 3 * (b * b)⁻¹ := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]; group
      _ = 1 := by rw [h3, hb']; simp
  refine ⟨n * n * n, ?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hn) hn, hsb, ?_⟩
  · exact orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  · have hle : Subgroup.closure {b₁, b₂} ≤ Cen (n * n * n) := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hc1 : n * n * n * b₁ = b₁ * (n * n * n) := by
        calc n * n * n * b₁ = n * n * (n * b₁) := by group
          _ = n * n * (b₁ * n) := by rw [e2]
          _ = (n * n * b₁) * n := by group
          _ = (b₁ * (n * n)) * n := by rw [hb12]
          _ = b₁ * (n * n * n) := by group
      have hc2 : n * n * n * b₂ = b₂ * (n * n * n) := by
        calc n * n * n * b₂ = n * n * (n * b₂) := by group
          _ = n * n * (b₂ * n) := by rw [e3]
          _ = (n * n * b₂) * n := by group
          _ = (b₂ * (n * n)) * n := by rw [hb22]
          _ = b₂ * (n * n * n) := by group
      rcases hx with rfl | rfl
      · exact hc1.symm
      · exact hc2.symm
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

theorem zpowers_central (a x : G) (ha : a ∈ Subgroup.zpowers b) (hx : x ∈ Cen b) :
    Commute a x := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have : Commute b x := (Subgroup.mem_centralizer_singleton_iff.1 hx).symm
  exact this.zpow_left i

theorem zpowers_cube (h : FF84Post b L B K b₁ b₂) : ∀ a ∈ Subgroup.zpowers b, a ^ 3 = 1 := by
  intro a ha
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, b_cube h, one_zpow]

theorem zpowers_comm_L (h : FF84Post b L B K b₁ b₂) :
    ∀ a ∈ Subgroup.zpowers b, ∀ n ∈ L, a * n = n * a := fun a ha n hn =>
  (zpowers_central a n ha (h.sec.hyp.hLC hn)).eq

theorem sq_mem_L (h : FF84Post b L B K b₁ b₂) {z : G} (hz : z ∈ Cen b) (hz2 : z * z = 1) :
    z ∈ L :=
  mem_of_sq_one_sup (zpowers_comm_L h) (zpowers_cube h) (h.cb ▸ hz) hz2

theorem comm_mul_central {a l y : G} (hal : Commute a l) (hay : Commute a y) :
    ⁅a * l, y⁆ = ⁅l, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hz : Commute a (l * y * l⁻¹) := (hal.mul_right hay).mul_right hal.inv_right
  calc a * l * y * (a * l)⁻¹ * y⁻¹ = a * (l * y * l⁻¹) * a⁻¹ * y⁻¹ := by group
    _ = (l * y * l⁻¹) * a * a⁻¹ * y⁻¹ := by rw [hz.eq]
    _ = l * y * l⁻¹ * y⁻¹ := by group

theorem cen_comm_le (h : FF84Post b L B K b₁ b₂) : ⁅Cen b, Cen b⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hLC := h.sec.hyp.hLC
  have hg₁' : g₁ ∈ Subgroup.zpowers b ⊔ L := by rw [h.cb]; exact hg₁
  have hg₂' : g₂ ∈ Subgroup.zpowers b ⊔ L := by rw [h.cb]; exact hg₂
  obtain ⟨a, ha, l, hl, rfl⟩ := exists_mul_of_mem_sup_of_comm (zpowers_comm_L h) hg₁'
  obtain ⟨a', ha', l', hl', rfl⟩ := exists_mul_of_mem_sup_of_comm (zpowers_comm_L h) hg₂'
  rw [comm_mul_central (zpowers_central a l ha (hLC hl)) (zpowers_central a _ ha hg₂)]
  have h1 : ⁅l, a' * l'⁆ = (⁅a' * l', l⁆)⁻¹ := by
    have := commutatorElement_inv l (a' * l')
    rw [← this, inv_inv]
  rw [h1, comm_mul_central (zpowers_central a' l' ha' (hLC hl')) (zpowers_central a' l ha' (hLC hl))]
  exact L.inv_mem (by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl')) (L.inv_mem hl))

theorem L_eq_comm (h : FF84Post b L B K b₁ b₂) : ⁅Cen b, Cen b⁆ = L := by
  refine le_antisymm (cen_comm_le h) ?_
  calc L = ⁅L, L⁆ := (perfect_L h.sec.hyp).symm
    _ ≤ ⁅Cen b, Cen b⁆ := Subgroup.commutator_mono h.sec.hyp.hLC h.sec.hyp.hLC

theorem nor_cen_le_nor_L (h : FF84Post b L B K b₁ b₂) : Nor (Cen b) ≤ Nor L := by
  apply le_nor_of_conj
  intro g hg x hx
  set f : G →* G := (MulAut.conj g).toMonoidHom with hf
  have hle : (Cen b).map f ≤ Cen b := by
    rintro _ ⟨y, hy, rfl⟩
    exact conj_mem_of_le_nor le_rfl hg hy
  have hL : L.map f ≤ L := by
    calc L.map f = ⁅Cen b, Cen b⁆.map f := by rw [L_eq_comm h]
      _ = ⁅(Cen b).map f, (Cen b).map f⁆ := Subgroup.map_commutator _ _ _
      _ ≤ ⁅Cen b, Cen b⁆ := Subgroup.commutator_mono hle hle
      _ = L := L_eq_comm h
  have := hL ⟨x, hx, rfl⟩
  simpa [hf] using this

theorem nor_cen_of_inv {g : G} (hg : g * b * g⁻¹ = b⁻¹) : g ∈ Nor (Cen b) := by
  have key : ∀ g : G, g * b * g⁻¹ = b⁻¹ → ∀ x ∈ Cen b, g * x * g⁻¹ ∈ Cen b := by
    intro g hg x hx
    have h1 : g * b⁻¹ * g⁻¹ = b := by
      rw [show g * b⁻¹ * g⁻¹ = (g * b * g⁻¹)⁻¹ by group, hg, inv_inv]
    have h2 : g⁻¹ * b * g = b⁻¹ := by
      calc g⁻¹ * b * g = g⁻¹ * (g * b⁻¹ * g⁻¹) * g := by rw [h1]
        _ = b⁻¹ := by group
    have hxb : Commute x b := Subgroup.mem_centralizer_singleton_iff.1 hx
    have hxb' : x * b⁻¹ = b⁻¹ * x := (hxb.inv_right).eq
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * x * g⁻¹ * b = g * x * (g⁻¹ * b * g) * g⁻¹ := by group
      _ = g * (x * b⁻¹) * g⁻¹ := by rw [h2]; group
      _ = g * (b⁻¹ * x) * g⁻¹ := by rw [hxb']
      _ = (g * b⁻¹ * g⁻¹) * (g * x * g⁻¹) := by group
      _ = b * (g * x * g⁻¹) := by rw [h1]
  have hg' : g⁻¹ * b * g⁻¹⁻¹ = b⁻¹ := by
    have h1 : g * b⁻¹ * g⁻¹ = b := by
      rw [show g * b⁻¹ * g⁻¹ = (g * b * g⁻¹)⁻¹ by group, hg, inv_inv]
    calc g⁻¹ * b * g⁻¹⁻¹ = g⁻¹ * (g * b⁻¹ * g⁻¹) * g := by rw [h1]; group
      _ = b⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ hg' _ hx
  simpa [mul_assoc] using this

theorem nor_L_of_inv (h : FF84Post b L B K b₁ b₂) {g : G} (hg : g * b * g⁻¹ = b⁻¹) :
    g ∈ Nor L :=
  nor_cen_le_nor_L h (nor_cen_of_inv hg)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
