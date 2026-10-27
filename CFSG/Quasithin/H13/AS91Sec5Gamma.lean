module

public import CFSG.Quasithin.H13.AS91Sec5Eltr

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94

@[expose] def Stmt5_Gamma2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ a b : G ⧸ c.G1, a ∈ c.ptsP → b ∈ c.ptsP → c.Delta.Adj a b →
      ∀ m : G ⧸ c.G2, CInc c.G1 c.G2 a m → CInc c.G1 c.G2 b m → m ∈ c.lnsP

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem mk_eq_one_iff (A : Subgroup G) (g : G) : ((g : G ⧸ A) = ((1 : G) : G ⧸ A)) ↔ g ∈ A := by
  rw [QuotientGroup.eq]
  simp

theorem x0_mem_ptsP : c.x0 ∈ c.ptsP := cInc_mk c.G1 c.G3 1

theorem exists_G13_line (hG : ∀ a b : G ⧸ c.G1, a ∈ c.ptsP → b ∈ c.ptsP → c.Delta.Adj a b →
      ∀ m : G ⧸ c.G2, CInc c.G1 c.G2 a m → CInc c.G1 c.G2 b m → m ∈ c.lnsP)
    {a : G ⧸ c.G1} (ha : a ∈ c.nbrP) :
    ∃ v ∈ c.G1 ⊓ c.G3, ∃ a₀ ∈ c.ptsL, a₀ ≠ c.x0 ∧ v • a₀ = a := by
  classical
  obtain ⟨haP, hadj⟩ := ha
  obtain ⟨hne, m, hx0m, ham⟩ := hadj
  have hm : m ∈ c.lnsP := hG c.x0 a c.x0_mem_ptsP haP ⟨hne, m, hx0m, ham⟩ m hx0m ham
  obtain ⟨u, hum, hupi⟩ := hm
  have huG3 : u ∈ c.G3 := (mk_eq_one_iff c.G3 u).mp hupi
  obtain ⟨w, hw1, hw2⟩ := hx0m
  have hwG1 : w ∈ c.G1 := by
    have : (w : G ⧸ c.G1) = ((1 : G) : G ⧸ c.G1) := hw1
    exact (mk_eq_one_iff c.G1 w).mp this
  have huw : u⁻¹ * w ∈ c.G2 := by
    have : (u : G ⧸ c.G2) = (w : G ⧸ c.G2) := hum.trans hw2.symm
    rw [QuotientGroup.eq] at this
    exact this
  have hwx : w • c.x0 = c.x0 := by
    have : w ∈ stabilizer G c.x0 := by rw [c.stab_x0]; exact hwG1
    exact mem_stabilizer_iff.mp this
  have hp : u⁻¹ • c.x0 ∈ c.ptsL := by
    have : u⁻¹ • c.x0 = (u⁻¹ * w) • c.x0 := by rw [mul_smul, hwx]
    rw [this]
    exact smul_mem_objOf_base huw c.x0_mem_ptsL
  obtain ⟨s, hsCZ, hs⟩ := c.exists_CZ_perm
    (Equiv.swap (⟨c.x0, c.x0_mem_ptsL⟩ : ↥c.ptsL) ⟨u⁻¹ • c.x0, hp⟩)
  have hsx : s • c.x0 = u⁻¹ • c.x0 := by
    have := hs ⟨c.x0, c.x0_mem_ptsL⟩
    rw [Equiv.swap_apply_left] at this
    exact this
  have hvx : (u * s) • c.x0 = c.x0 := by rw [mul_smul, hsx, smul_inv_smul]
  have hvG1 : u * s ∈ c.G1 := by
    rw [← c.stab_x0]
    exact mem_stabilizer_iff.mpr hvx
  have hvG3 : u * s ∈ c.G3 := mul_mem huG3 (c.CZ_le_G3 hsCZ)
  have hsG2 : s ∈ c.G2 := c.CZ_le_G2 hsCZ
  have hvl : ((u * s : G) : G ⧸ c.G2) = m := by
    rw [← hum]
    rw [QuotientGroup.eq]
    simpa using inv_mem hsG2
  obtain ⟨t, ht1, ht2⟩ := ham
  have htG2 : (u * s)⁻¹ * t ∈ c.G2 := by
    have : ((u * s : G) : G ⧸ c.G2) = (t : G ⧸ c.G2) := hvl.trans ht2.symm
    rw [QuotientGroup.eq] at this
    exact this
  have hv_inv : (u * s)⁻¹ • a = (((u * s)⁻¹ * t : G) : G ⧸ c.G1) := by
    rw [← ht1, mk_mul_eq_smul]
  have ha₀ : (u * s)⁻¹ • a ∈ c.ptsL := by
    rw [hv_inv, c.mem_ptsL_iff]
    exact ⟨_, htG2, rfl⟩
  refine ⟨u * s, Subgroup.mem_inf.mpr ⟨hvG1, hvG3⟩, (u * s)⁻¹ • a, ha₀, ?_, smul_inv_smul _ _⟩
  intro h
  apply hne
  have : a = (u * s) • c.x0 := by
    rw [← h, smul_inv_smul]
  rw [this, hvx]

theorem nbrP_transitive (hG : ∀ a b : G ⧸ c.G1, a ∈ c.ptsP → b ∈ c.ptsP → c.Delta.Adj a b →
      ∀ m : G ⧸ c.G2, CInc c.G1 c.G2 a m → CInc c.G1 c.G2 b m → m ∈ c.lnsP) :
    ∀ a ∈ c.nbrP, ∀ b ∈ c.nbrP, ∃ g ∈ c.G1 ⊓ c.G3, g • a = b := by
  intro a ha b hb
  obtain ⟨va, hva, a₀, ha₀, ha₀x, rfl⟩ := c.exists_G13_line hG ha
  obtain ⟨vb, hvb, b₀, hb₀, hb₀x, rfl⟩ := c.exists_G13_line hG hb
  obtain ⟨e, he, heab⟩ := c.E_transitive ha₀ hb₀ ha₀x hb₀x
  refine ⟨vb * e * va⁻¹, ?_, ?_⟩
  · refine mul_mem (mul_mem hvb ?_) (inv_mem hva)
    exact Subgroup.mem_inf.mpr ⟨c.E_le_G1 he, c.E_le_G3 he⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, heab]

end Loc49

theorem stmt5_3_1u_of_gamma2 (h : Stmt5_Gamma2) : Stmt5_3_1u := by
  intro G _ _ z hJ c
  exact c.nbrP_transitive (h G z hJ c)

end CFSG.Quasithin.H13.AS91
