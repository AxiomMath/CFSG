module

public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3
open scoped commutatorElement

variable {G V : Type} [Group G] [CommGroup V]

@[expose] def Fx (ρ : G →* MulAut V) (X : Subgroup G) : Subgroup V := fixV (X.map ρ)

private theorem rho_inv_apply_apply (ρ : G →* MulAut V) (a : G) (w : V) :
    ρ a⁻¹ (ρ a w) = w := by
  have h : ρ a⁻¹ * ρ a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc ρ a⁻¹ (ρ a w) = (ρ a⁻¹ * ρ a) w := (MulAut.mul_apply _ (ρ a⁻¹) (ρ a) w).symm
    _ = (1 : MulAut V) w := by rw [h]
    _ = w := MulAut.one_apply _ w

private theorem rho_apply_inv_apply (ρ : G →* MulAut V) (a : G) (w : V) :
    ρ a (ρ a⁻¹ w) = w := by
  have h : ρ a * ρ a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc ρ a (ρ a⁻¹ w) = (ρ a * ρ a⁻¹) w := (MulAut.mul_apply _ (ρ a) (ρ a⁻¹) w).symm
    _ = (1 : MulAut V) w := by rw [h]
    _ = w := MulAut.one_apply _ w

private theorem rho_conj_apply (ρ : G →* MulAut V) (a b : G) (w : V) :
    ρ (a * b * a⁻¹) (ρ a w) = ρ a (ρ b w) := by
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, rho_inv_apply_apply]

theorem mem_Fx {ρ : G →* MulAut V} {X : Subgroup G} {v : V} :
    v ∈ Fx ρ X ↔ ∀ x ∈ X, ρ x v = v := by
  unfold Fx
  rw [mem_fixV]
  constructor
  · intro h x hx
    exact h (ρ x) ⟨x, hx, rfl⟩
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact h x hx

theorem Fx_anti {ρ : G →* MulAut V} {X Y : Subgroup G} (h : X ≤ Y) : Fx ρ Y ≤ Fx ρ X := by
  intro v hv
  rw [mem_Fx] at hv ⊢
  exact fun x hx => hv x (h hx)

theorem mem_Fx_conjSubgroup {ρ : G →* MulAut V} {X : Subgroup G} {g : G} {v : V} :
    v ∈ Fx ρ (conjSubgroup X g) ↔ ρ g v ∈ Fx ρ X := by
  rw [mem_Fx, mem_Fx]
  constructor
  · intro h x hx
    have hxy : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    have hy : g⁻¹ * x * g ∈ conjSubgroup X g := by
      rw [CFSG.Quasithin.mem_conjSubgroup_iff, hxy]
      exact hx
    have key := rho_conj_apply ρ g (g⁻¹ * x * g) v
    rw [h _ hy, hxy] at key
    exact key
  · intro h y hy
    rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hy
    have h1 := h _ hy
    rw [rho_conj_apply] at h1
    calc ρ y v = ρ g⁻¹ (ρ g (ρ y v)) := (rho_inv_apply_apply ρ g (ρ y v)).symm
      _ = ρ g⁻¹ (ρ g v) := by rw [h1]
      _ = v := rho_inv_apply_apply ρ g v

@[expose] def cenV (ρ : G →* MulAut V) (U : Subgroup V) : Subgroup G where
  carrier := {g | ∀ u ∈ U, ρ g u = u}
  one_mem' := fun u _ => by simp
  mul_mem' := fun {a b} ha hb u hu => by simp [ha u hu, hb u hu]
  inv_mem' := fun {a} ha u hu => by
    have := ha u hu
    calc ρ a⁻¹ u = ρ a⁻¹ (ρ a u) := by rw [this]
      _ = u := by simp [← MulAut.mul_apply, ← map_mul]

@[expose] def stabV (ρ : G →* MulAut V) (U : Subgroup V) : Subgroup G where
  carrier := {g | ∀ v : V, ρ g v ∈ U ↔ v ∈ U}
  one_mem' := fun v => by simp
  mul_mem' := fun {a b} ha hb v => by
    rw [map_mul, MulAut.mul_apply]
    exact (ha (ρ b v)).trans (hb v)
  inv_mem' := fun {a} ha v => by
    have h1 := ha (ρ a⁻¹ v)
    rw [rho_apply_inv_apply] at h1
    exact h1.symm

theorem mem_stabV {ρ : G →* MulAut V} {U : Subgroup V} {g : G} :
    g ∈ stabV ρ U ↔ ∀ v : V, ρ g v ∈ U ↔ v ∈ U := Iff.rfl

theorem cenV_le_stabV (ρ : G →* MulAut V) (U : Subgroup V) : cenV ρ U ≤ stabV ρ U := by
  intro g hg
  have hg' : ∀ u ∈ U, ρ g u = u := hg
  have hginv : ∀ u ∈ U, ρ g⁻¹ u = u := Subgroup.inv_mem (cenV ρ U) hg
  rw [mem_stabV]
  intro v
  constructor
  · intro hv
    have h1 : ρ g⁻¹ (ρ g v) = v := rho_inv_apply_apply ρ g v
    have h2 : ρ g⁻¹ (ρ g v) = ρ g v := hginv _ hv
    rw [h2] at h1
    rw [h1] at hv
    exact hv
  · intro hv
    rw [hg' v hv]
    exact hv

theorem mem_stabV_Fx_of_conj {ρ : G →* MulAut V} {X : Subgroup G} {g : G}
    (h : conjSubgroup X g = X) : g ∈ stabV ρ (Fx ρ X) := by
  rw [mem_stabV]
  intro v
  rw [← mem_Fx_conjSubgroup, h]

theorem cenV_anti (ρ : G →* MulAut V) {U U' : Subgroup V} (h : U ≤ U') :
    cenV ρ U' ≤ cenV ρ U := by
  intro g hg u hu
  exact hg u (h hu)

@[expose] def Om (ρ : G →* MulAut V) (n : ℕ) (A : Subgroup G) : Prop :=
  A ≠ ⊥ ∧ (∀ a ∈ A, a ^ 2 = 1) ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
    ∀ B : Subgroup G, B ≤ A → mQuot A B < n → Fx ρ B = Fx ρ A

@[expose] def Wset (Ω : Set (Subgroup G)) (c : ℕ) : Set (Subgroup G) :=
  {B | ∃ A ∈ Ω, B ≤ A ∧ mQuot A B ≤ c}

@[expose] def Wcl (Ω : Set (Subgroup G)) (c : ℕ) (S : Subgroup G) : Subgroup G :=
  sSup {B | B ≤ S ∧ B ∈ Wset Ω c}

theorem le_Wcl {Ω : Set (Subgroup G)} {c : ℕ} {S B : Subgroup G} (hBS : B ≤ S)
    (hB : B ∈ Wset Ω c) : B ≤ Wcl Ω c S :=
  le_sSup ⟨hBS, hB⟩

theorem Wcl_le_self (Ω : Set (Subgroup G)) (c : ℕ) (S : Subgroup G) : Wcl Ω c S ≤ S :=
  sSup_le fun _ hB => hB.1

theorem Wcl_mono_level {Ω : Set (Subgroup G)} {c c' : ℕ} (h : c ≤ c') (S : Subgroup G) :
    Wcl Ω c S ≤ Wcl Ω c' S := by
  refine sSup_le fun B hB => ?_
  obtain ⟨hBS, A, hA, hBA, hm⟩ := hB
  exact le_Wcl hBS ⟨A, hA, hBA, hm.trans h⟩

theorem Wcl_mono_base {Ω : Set (Subgroup G)} (c : ℕ) {S S' : Subgroup G} (h : S ≤ S') :
    Wcl Ω c S ≤ Wcl Ω c S' := by
  refine sSup_le fun B hB => ?_
  exact le_Wcl (hB.1.trans h) hB.2

private theorem conjSubgroup_Wcl_le {Ω : Set (Subgroup G)}
    (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω) (c : ℕ) (S : Subgroup G) (g : G) :
    conjSubgroup (Wcl Ω c S) g ≤ Wcl Ω c (conjSubgroup S g) := by
  refine Subgroup.map_le_iff_le_comap.mpr ?_
  refine sSup_le fun B hB => ?_
  refine Subgroup.map_le_iff_le_comap.mp ?_
  obtain ⟨A, hA, hBA, hm⟩ := hB.2
  have hmem : conjSubgroup B g ∈ Wset Ω c :=
    ⟨conjSubgroup A g, hΩ A hA g, CFSG.Quasithin.E3.conjSubgroup_mono_left g hBA,
      by rw [CFSG.Quasithin.E3.mQuot_conjSubgroup]; exact hm⟩
  exact le_Wcl (CFSG.Quasithin.E3.conjSubgroup_mono_left g hB.1) hmem

theorem Wcl_conjSubgroup {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (c : ℕ) (S : Subgroup G) (g : G) :
    Wcl Ω c (conjSubgroup S g) = conjSubgroup (Wcl Ω c S) g := by
  have h1 := conjSubgroup_Wcl_le hΩ c (conjSubgroup S g) g⁻¹
  rw [CFSG.Quasithin.E3.conjSubgroup_conj_inv] at h1
  have h2 := CFSG.Quasithin.E3.conjSubgroup_mono_left g h1
  rw [CFSG.Quasithin.E3.conjSubgroup_inv_conj] at h2
  exact le_antisymm h2 (conjSubgroup_Wcl_le hΩ c S g)

theorem conjSubgroup_Wcl_eq {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (c : ℕ) {S : Subgroup G} {g : G} (h : conjSubgroup S g = S) :
    conjSubgroup (Wcl Ω c S) g = Wcl Ω c S := by
  rw [← Wcl_conjSubgroup hΩ c S g, h]

theorem Wcl_eq_of_le {Ω : Set (Subgroup G)} {c : ℕ} {S T : Subgroup G} (hST : S ≤ T)
    (h : Wcl Ω c T ≤ S) : Wcl Ω c T = Wcl Ω c S := by
  refine le_antisymm ?_ (Wcl_mono_base c hST)
  refine sSup_le fun B hB => ?_
  exact le_Wcl ((le_Wcl hB.1 hB.2).trans h) hB.2

end CFSG.Quasithin.RonanE42
