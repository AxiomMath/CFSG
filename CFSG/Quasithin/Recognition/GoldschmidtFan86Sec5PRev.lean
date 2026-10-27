module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCore
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PConj

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

open scoped Classical in
@[expose] noncomputable def Ecirc (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V]
    (u w : V) : Set G :=
  if valence Γ u = 5 then Gcirc Γ G u w else Gcirc Γ G w u

theorem Line.edgeCirc_eq_Ecirc (ℓ : Line Γ) (i : ℤ) :
    ℓ.edgeCirc (G := G) i = Ecirc Γ G (ℓ.vert i) (ℓ.vert (i + 1)) := rfl

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem Ecirc_comm {u w : V} (huw : Γ.Adj u w) : Ecirc Γ G u w = Ecirc Γ G w u := by
  have h1 : Fan86.valence Γ u ≠ Fan86.valence Γ w := F.alternating _ _ huw
  have h2 : Fan86.valence Γ u = 3 ∨ Fan86.valence Γ u = 5 := F.valence u
  have h3 : Fan86.valence Γ w = 3 ∨ Fan86.valence Γ w = 5 := F.valence w
  unfold Ecirc
  by_cases h : Fan86.valence Γ u = 5
  · have : ¬ Fan86.valence Γ w = 5 := by omega
    simp [h, this]
  · have : Fan86.valence Γ w = 5 := by omega
    simp [h, this]

theorem Ecirc_smul (g : G) {u w : V} {h : G} (hh : h ∈ Ecirc Γ G u w) :
    g * h * g⁻¹ ∈ Ecirc Γ G (g • u) (g • w) := by
  have key : ∀ {a b : V} {h : G}, h ∈ Gcirc Γ G a b →
      g * h * g⁻¹ ∈ Gcirc Γ G (g • a) (g • b) := by
    rintro a b h ⟨⟨ha, hb⟩, hhh⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine MulAction.mem_stabilizer_iff.2 ?_
      rw [mul_smul, mul_smul, inv_smul_smul, MulAction.mem_stabilizer_iff.1 ha]
    · refine MulAction.mem_stabilizer_iff.2 ?_
      rw [mul_smul, mul_smul, inv_smul_smul, MulAction.mem_stabilizer_iff.1 hb]
    · have := F.conj_mem_nbrStab_smul g hhh
      have e : g * h * g⁻¹ * (g * h * g⁻¹) = g * (h * h) * g⁻¹ := by group
      rw [e]
      exact this
  unfold Ecirc at hh ⊢
  rw [F.valence_smul_eq g u]
  split_ifs at hh ⊢
  · exact key hh
  · exact key hh

end FanTree

namespace Line

variable (ℓ : Line Γ)

theorem rev_edgeStab (i : ℤ) : ℓ.rev.edgeStab (G := G) i = ℓ.edgeStab (-i - 1) := by
  simp only [edgeStab, rev_vert]
  rw [show -(i + 1) = -i - 1 by omega, show -i - 1 + 1 = -i by omega, inf_comm]

theorem rev_edgeCirc (F : FanTree Γ G) (i : ℤ) :
    ℓ.rev.edgeCirc (G := G) i = ℓ.edgeCirc (-i - 1) := by
  have hadj : Γ.Adj (ℓ.vert (-i)) (ℓ.vert (-i - 1)) := by
    have := (ℓ.adj (-i - 1)).symm
    rwa [show -i - 1 + 1 = -i by omega] at this
  rw [edgeCirc_eq_Ecirc, edgeCirc_eq_Ecirc, rev_vert, rev_vert, show -(i + 1) = -i - 1 by omega,
    show -i - 1 + 1 = -i by omega]
  exact F.Ecirc_comm hadj

theorem mem_rev_fixIdx (z : G) (i : ℤ) : i ∈ ℓ.rev.fixIdx z ↔ -i ∈ ℓ.fixIdx z := Iff.rfl

variable {ℓ}

theorem IsCoreWith.rev {P : ℤ → Prop} {z : G} {a b : ℤ}
    (hP : ∀ i, P i → i ∈ ℓ.fixIdx z ∧ i + 1 ∈ ℓ.fixIdx z) (h : ℓ.IsCoreWith P z a b) :
    ℓ.rev.IsCoreWith (fun i => P (-i - 1)) z (-b) (-a) := by
  obtain ⟨hab, hfix, hcen, hl, hr⟩ := h
  refine ⟨by omega, fun i h1 h2 => hfix (-i) (by omega) (by omega),
    fun i h1 h2 => hcen (-i - 1) (by omega) (by omega), ?_, ?_⟩
  · rintro ⟨-, hPb⟩
    rw [show -(-b - 1) - 1 = b by omega] at hPb
    exact hr ⟨(hP b hPb).1, hPb⟩
  · rintro ⟨-, hPa⟩
    rw [show -(-a) - 1 = a - 1 by omega] at hPa
    exact hl ⟨(hP (a - 1) hPa).1, hPa⟩

theorem IsCoreC.rev (F : FanTree Γ G) {z : G} {a b : ℤ} (h : ℓ.IsCoreC z a b) :
    ℓ.rev.IsCoreC z (-b) (-a) := by
  have := IsCoreWith.rev (ℓ := ℓ) (fun i hi => edgeCirc_fix ℓ hi.1) h
  unfold IsCoreC
  simpa only [rev_edgeCirc ℓ F] using this

theorem IsCore.rev {z : G} {a b : ℤ} (h : ℓ.IsCore z a b) : ℓ.rev.IsCore z (-b) (-a) := by
  have hP : ∀ i, z ∈ Cen (ℓ.edgeStab (G := G) i : Set G) →
      i ∈ ℓ.fixIdx z ∧ i + 1 ∈ ℓ.fixIdx z := fun i hi =>
    ⟨MulAction.mem_stabilizer_iff.1 hi.1.1, MulAction.mem_stabilizer_iff.1 hi.1.2⟩
  have := IsCoreWith.rev (ℓ := ℓ) hP h
  unfold IsCore
  simpa only [rev_edgeStab ℓ] using this

theorem IsCoreCFix.rev (F : FanTree Γ G) {z : G} {a b tL tR : ℤ} (h : ℓ.IsCoreCFix z a b tL tR) :
    ℓ.rev.IsCoreCFix z (-b) (-a) (-tR) (-tL) :=
  ⟨fun i => by
    have := h.fix (-i)
    rw [mem_rev_fixIdx, this]
    omega, h.core.rev F⟩

theorem IsCoreFix.rev {z : G} {a b tL tR : ℤ} (h : ℓ.IsCoreFix z a b tL tR) :
    ℓ.rev.IsCoreFix z (-b) (-a) (-tR) (-tL) :=
  ⟨fun i => by
    have := h.fix (-i)
    rw [mem_rev_fixIdx, this]
    omega, h.core.rev⟩

theorem ZZ_rev {z : G} (h : z ∈ ℓ.ZZ) : z ∈ ℓ.rev.ZZ := by
  obtain ⟨hzz, i, hi⟩ := h
  refine ⟨hzz, -i - 1, ?_⟩
  rw [rev_edgeStab, show -(-i - 1) - 1 = i by omega]
  exact hi

end Line

end CFSG.Quasithin.Fan86
