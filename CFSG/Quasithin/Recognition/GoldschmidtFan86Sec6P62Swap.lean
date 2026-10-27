module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Br

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

theorem exists_stab_smul_br (F : FanTree Γ G) (h40 : Fan40 F) {d ν ν' l l' : V}
    (hd : valence Γ d = 5) (h : Br Γ d ν l) (h' : Br Γ d ν' l') :
    ∃ g ∈ MulAction.stabilizer G d, g • l = l' := by
  obtain ⟨g₁, hg₁, hg₁ν⟩ := F.loc_trans d ν ν' h.1 h'.1
  have hg₁d : g₁ • d = d := MulAction.mem_stabilizer_iff.1 hg₁
  have hbr : Br Γ d ν' (g₁ • l) := by
    have := Br.smul F g₁ h
    rwa [hg₁d, hg₁ν] at this
  obtain ⟨k, hk, hkl⟩ := F.exists_mem_nbrStab_smul_eq_of_valence_three h40 h'.1
    (Br.valence F hd h').1 hbr.2.1 hbr.2.2 h'.2.1 h'.2.2
  exact ⟨k * g₁, (MulAction.stabilizer G d).mul_mem (F.nbrStab_le_stabilizer d hk) hg₁,
    by rw [mul_smul, hkl]⟩

theorem mul_mem_nbrStab_of_sq_mem (F : FanTree Γ G) {v a : V} (hva : Γ.Adj v a) {g h : G}
    (hg : g ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a)
    (hh : h ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a)
    (hg2 : g * g ∈ nbrStab Γ G v) (hh2 : h * h ∈ nbrStab Γ G v) (hgn : g ∉ nbrStab Γ G v)
    (hhn : h ∉ nbrStab Γ G v) : g * h ∈ nbrStab Γ G v := by
  obtain ⟨φ, hφ, -⟩ := F.exists_edge_char hva
  have hp : valence Γ v = 3 ∨ valence Γ v = 5 := F.valence v
  let e : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) := ⟨g, hg⟩
  let e' : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) := ⟨h, hh⟩
  have h1 : φ e ≠ 1 := fun x => hgn ((hφ e).2 x)
  have h1' : φ e' ≠ 1 := fun x => hhn ((hφ e').2 x)
  have h2 : φ e * φ e = 1 := by rw [← map_mul]; exact (hφ (e * e)).1 hg2
  have h2' : φ e' * φ e' = 1 := by rw [← map_mul]; exact (hφ (e' * e')).1 hh2
  have h3 := units_sq_eq_one_unique hp (φ e) (φ e') h1 h2 h1' h2'
  have h4 : φ (e * e') = 1 := by rw [map_mul, ← h3]; exact h2
  exact (hφ (e * e')).2 h4

theorem exists_reflection (F : FanTree Γ G) {v a : V} (ha : Γ.Adj v a) :
    ∃ t, t ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a ∧ t ∉ nbrStab Γ G v ∧
      t * t ∈ nbrStab Γ G v := by
  obtain ⟨g, hgS, hg4, hgen⟩ := F.exists_cyclic_gen ha
    (MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) le_rfl
  have hgn : g ∉ nbrStab Γ G v := by
    intro hgK
    obtain ⟨g', hg', hg'a, c, hc, hg'c⟩ := F.frobenius_nonreg v a ha
    have hg'S : g' ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a :=
      ⟨hg', MulAction.mem_stabilizer_iff.2 hg'a⟩
    obtain ⟨n, hn⟩ := hgen g' hg'S
    have h1 : g ^ n ∈ nbrStab Γ G v := zpow_mem hgK n
    have h2 : g'⁻¹ ∈ nbrStab Γ G v := by
      have := (nbrStab Γ G v).mul_mem ((nbrStab Γ G v).inv_mem h1) hn
      simpa using this
    have h3 : g' ∈ nbrStab Γ G v := by simpa using (nbrStab Γ G v).inv_mem h2
    exact hg'c (mem_nbrStab.1 h3 c hc)
  by_cases hg2 : g * g ∈ nbrStab Γ G v
  · exact ⟨g, hgS, hgn, hg2⟩
  · refine ⟨g * g, (MulAction.stabilizer G v ⊓ MulAction.stabilizer G a).mul_mem hgS hgS, hg2, ?_⟩
    have : g * g * (g * g) = g ^ 4 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [this]
    exact hg4

end P62

end CFSG.Quasithin.Fan86
