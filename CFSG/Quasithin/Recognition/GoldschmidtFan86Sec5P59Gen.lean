module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Shift

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P59

theorem cen_conj_stab {g z : G} {u w : V}
    (hz : z ∈ Cen ((MulAction.stabilizer G u ⊓ MulAction.stabilizer G w : Subgroup G) : Set G)) :
    g * z * g⁻¹ ∈ Cen ((MulAction.stabilizer G (g • u) ⊓ MulAction.stabilizer G (g • w) :
      Subgroup G) : Set G) := by
  refine (P55.cen_conj_iff g (fun k => ?_) z).2 hz
  have hst : ∀ v : V, (g * k * g⁻¹) • (g • v) = g • v ↔ k • v = v := by
    intro v
    simp only [mul_smul, inv_smul_smul]
    exact (MulAction.injective g).eq_iff
  simp only [SetLike.mem_coe, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rw [hst, hst]

theorem adj_two (ℓ : Line Γ) (i : ℤ) : Γ.Adj (ℓ.vert (i + 1)) (ℓ.vert (i + 2)) := by
  have := ℓ.adj (i + 1)
  rwa [show i + 1 + 1 = i + 2 by ring] at this

variable (F : FanTree Γ G)
include F

theorem stab_le_closure_two (ℓ : Line Γ) (i : ℤ) :
    MulAction.stabilizer G (ℓ.vert (i + 1)) ≤ Subgroup.closure
      ((ℓ.edgeStab (G := G) i : Set G) ∪ (ℓ.edgeStab (G := G) (i + 1) : Set G)) := by
  set M := Subgroup.closure ((ℓ.edgeStab (G := G) i : Set G) ∪
    (ℓ.edgeStab (G := G) (i + 1) : Set G)) with hM
  have hEi : ℓ.edgeStab (G := G) i ≤ M := fun g hg => Subgroup.subset_closure (Or.inl hg)
  have hEi1 : ℓ.edgeStab (G := G) (i + 1) ≤ M := fun g hg => Subgroup.subset_closure (Or.inr hg)
  have hu : Γ.Adj (ℓ.vert (i + 1)) (ℓ.vert i) := (ℓ.adj i).symm
  have hw : Γ.Adj (ℓ.vert (i + 1)) (ℓ.vert (i + 2)) := adj_two ℓ i
  have huw : ℓ.vert i ≠ ℓ.vert (i + 2) := ℓ.nb i
  obtain ⟨g₁, hg₁, hg₁u, c₁, hc₁, hg₁c⟩ := F.frobenius_nonreg _ _ hu
  obtain ⟨g₂, hg₂, hg₂w, c₂, hc₂, hg₂c⟩ := F.frobenius_nonreg _ _ hw
  have h₁w : g₁ • ℓ.vert (i + 2) ≠ ℓ.vert (i + 2) := fun h =>
    hg₁c (F.frobenius_two _ _ _ hu hw huw g₁ hg₁ hg₁u h c₁ hc₁)
  have h₂u : g₂ • ℓ.vert i ≠ ℓ.vert i := fun h =>
    hg₂c (F.frobenius_two _ _ _ hw hu huw.symm g₂ hg₂ hg₂w h c₂ hc₂)
  have hg₁M : g₁ ∈ M := hEi ⟨MulAction.mem_stabilizer_iff.2 hg₁u, hg₁⟩
  have hg₂M : g₂ ∈ M := hEi1 ⟨hg₂, MulAction.mem_stabilizer_iff.2 (by
    rw [show i + 1 + 1 = i + 2 by ring]; exact hg₂w)⟩
  intro h hh
  obtain ⟨m, hm, hmα, hmu⟩ := F.transitive_of_two_fixers hu hw huw hg₁ hg₂ hg₁u h₁w hg₂w h₂u hu
    (F.adj_smul_of_mem_stabilizer hh hu)
  have hmM : m ∈ M := by
    have : Subgroup.closure ({g₁, g₂} : Set G) ≤ M := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact hg₁M
      · exact hg₂M
    exact this hm
  have hmh : m⁻¹ * h ∈ ℓ.edgeStab (G := G) i :=
    ⟨MulAction.mem_stabilizer_iff.2 (by rw [mul_smul, ← hmu, inv_smul_smul]),
      MulAction.mem_stabilizer_iff.2 (by
        rw [mul_smul, MulAction.mem_stabilizer_iff.1 hh, inv_smul_eq_iff]
        exact hmα.symm)⟩
  have : m * (m⁻¹ * h) ∈ M := M.mul_mem hmM (hEi hmh)
  simpa using this

theorem cen_stab_of_edges (ℓ : Line Γ) (i : ℤ) {z : G}
    (h1 : z ∈ Cen (ℓ.edgeStab (G := G) i : Set G))
    (h2 : z ∈ Cen (ℓ.edgeStab (G := G) (i + 1) : Set G)) :
    z ∈ Cen (MulAction.stabilizer G (ℓ.vert (i + 1)) : Set G) := by
  refine ⟨(Subgroup.mem_inf.1 h1.1).2, fun h hh => ?_⟩
  have hle : Subgroup.closure ((ℓ.edgeStab (G := G) i : Set G) ∪
      (ℓ.edgeStab (G := G) (i + 1) : Set G)) ≤ Subgroup.centralizer ({z} : Set G) :=
    closure_le_centralizer fun s hs => by
      rcases hs with hs | hs
      · exact h1.2 s hs
      · exact h2.2 s hs
  have := (Subgroup.mem_centralizer_iff.1 (hle (stab_le_closure_two F ℓ i hh))) z rfl
  exact this.symm

omit F in
theorem exists_core (ℓ : Line Γ) {P : ℤ → Prop} {z : G} {tL tR i : ℤ}
    (hfix : ∀ k, k ∈ ℓ.fixIdx z ↔ tL ≤ k ∧ k ≤ tR)
    (hP : ∀ k, P k → k ∈ ℓ.fixIdx z ∧ k + 1 ∈ ℓ.fixIdx z) (hi : P i) :
    ∃ a b : ℤ, a ≤ i ∧ i < b ∧ ℓ.IsCoreWith P z a b := by
  classical
  have hiL : tL ≤ i := ((hfix i).1 (hP i hi).1).1
  have hiR : i + 1 ≤ tR := ((hfix (i + 1)).1 (hP i hi).2).2
  obtain ⟨a, ⟨ha1, ha2, ha3⟩, hamin⟩ := Int.exists_least_of_bdd
    (P := fun a => tL ≤ a ∧ a ≤ i ∧ ∀ k, a ≤ k → k ≤ i → P k)
    ⟨tL, fun a ha => ha.1⟩ ⟨i, hiL, le_rfl, fun k h1 h2 => by
      have : k = i := le_antisymm h2 h1
      rwa [this]⟩
  obtain ⟨b, ⟨hb1, hb2, hb3⟩, hbmax⟩ := Int.exists_greatest_of_bdd
    (P := fun b => i < b ∧ b ≤ tR ∧ ∀ k, i ≤ k → k < b → P k)
    ⟨tR, fun b hb => hb.2.1⟩ ⟨i + 1, by omega, hiR, fun k h1 h2 => by
      have : k = i := by omega
      rwa [this]⟩
  refine ⟨a, b, ha2, hb1, by omega, fun k h1 h2 => (hfix k).2 ⟨by omega, by omega⟩,
    fun k h1 h2 => ?_, ?_, ?_⟩
  · by_cases hk : k ≤ i
    · exact ha3 k h1 hk
    · exact hb3 k (by omega) h2
  · rintro ⟨h1, h2⟩
    have := hamin (a - 1) ⟨((hfix _).1 h1).1, by omega, fun k hk1 hk2 => by
      by_cases hk : k = a - 1
      · rw [hk]; exact h2
      · exact ha3 k (by omega) hk2⟩
    omega
  · rintro ⟨h1, h2⟩
    have := hbmax (b + 1) ⟨by omega, ((hfix _).1 (hP b h2).2).2, fun k hk1 hk2 => by
      by_cases hk : k = b
      · rw [hk]; exact h2
      · exact hb3 k hk1 (by omega)⟩
    omega

end P59

end CFSG.Quasithin.Fan86
