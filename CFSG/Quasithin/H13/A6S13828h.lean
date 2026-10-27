module

public import CFSG.Quasithin.H13.A6S13828g

public section

namespace CFSG.Quasithin.H13.A6

open Matrix Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

@[expose] def tau3 : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def V3Pts (σ : Perm (Fin 6)) (y : P6) : Prop :=
  y = e0123 ∨ y = act4f σ e0123 ∨ y = act4f (σ * σ) e0123 ∨ y = act4f (tau3 * σ) e0123 ∨
    y = act4f (tau3 * (σ * σ)) e0123 ∨ y = act4f (tau3 * tau3 * σ) e0123 ∨
    y = act4f (tau3 * tau3 * (σ * σ)) e0123

instance (σ : Perm (Fin 6)) (y : P6) : Decidable (V3Pts σ y) := by unfold V3Pts; infer_instance

theorem v3pt_check : ∀ σ : Perm (Fin 6), (StabW2 σ ∧ σ ^ 45 = 1 ∧ act4f σ e0123 ≠ e0123) →
    ∀ y : P6, (InW4 y ∧ InW3 y ∧ y ≠ 1) → V3Pts σ y := by
  decide +kernel

theorem gq_check : ∀ σ : Perm (Fin 6), (StabW2 σ ∧ σ ^ 45 = 1 ∧ act4f σ e0123 ≠ e0123) →
    ∀ y : P6, InW4 y → ∃ i : Fin 3, InW3 (act4f (σ⁻¹ ^ (i : ℕ)) y) := by
  decide +kernel

theorem tau3_facts : InW3 (act4f tau3 (dv 0 1)) ∧ InW3 (act4f (tau3 * tau3) (dv 0 1)) ∧
    act4f tau3 (dv 0 1) = dv 0 1 * dv 0 2 := by
  decide

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
  {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}
  {γ : ↥(conjClosure V S.G1) →* Multiplicative (Fin 6 → ZMod 2)}

theorem psi_conj_u1 (x : ↥(Subgroup.normalizer (V : Set G))) :
    (S.frame.ψ ⟨(x : G) * S.u1 * (x : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp x.2 _).mp S.u1_mem_V⟩ : P6) =
      act4f (S.frame.ρ x) (dv 0 1) := by
  have := S.psi_conj x ⟨S.u1, S.u1_mem_V⟩
  have h1 : (S.frame.ψ ⟨S.u1, S.u1_mem_V⟩ : P6) = dv 0 1 := S.psi_u1
  rw [← h1]
  exact congrArg Subtype.val this

theorem eq_of_psi_eq {a b : G} {ha : a ∈ V} {hb : b ∈ V}
    (h : (S.frame.ψ ⟨a, ha⟩ : P6) = (S.frame.ψ ⟨b, hb⟩ : P6)) : a = b :=
  congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))

theorem mem_G1_iff_conj {x : G} : x ∈ S.G1 ↔ x * S.z * x⁻¹ = S.z := by
  rw [G1, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [h, mul_inv_cancel_right]
  · intro h
    calc x * S.z = x * S.z * x⁻¹ * x := by group
      _ = S.z * x := by rw [h]

theorem inv_mul_mem_G1 {x y : G} (h : x * S.z * x⁻¹ = y * S.z * y⁻¹) : y⁻¹ * x ∈ S.G1 := by
  rw [S.mem_G1_iff_conj]
  calc y⁻¹ * x * S.z * (y⁻¹ * x)⁻¹ = y⁻¹ * (x * S.z * x⁻¹) * y := by group
    _ = S.z := by rw [h]; group

theorem conjSub_UH_mul_G1 {x y : G} (hy : y ∈ S.G1) :
    conjSub (x * y) (conjClosure S.V3 S.G1) = conjSub x (conjClosure S.V3 S.G1) := by
  rw [conjSub_mul]
  congr 1
  ext u
  rw [mem_conjSub]
  have := (Subgroup.mem_normalizer_iff.mp
    (le_normalizer_conjClosure S.V3 S.G1 (S.G1.inv_mem hy)) u).symm
  simpa using this

section Cover

variable {g c : G}

theorem conjSub_UH_eq_of_conj {l x : G} (h : l * S.z * l⁻¹ = x * S.z * x⁻¹) :
    conjSub l (conjClosure S.V3 S.G1) = conjSub x (conjClosure S.V3 S.G1) := by
  have h1 := S.inv_mul_mem_G1 h
  have e : l = x * (x⁻¹ * l) := by group
  rw [e, S.conjSub_UH_mul_G1 h1]

structure GData (g : G) : Prop where
  L : g ∈ L
  N : g ∈ Subgroup.normalizer (S.V2 : Set G)
  H : g ∉ S.G1
  odd : ∃ m, Odd m ∧ g ^ m = 1

structure CData (c : G) : Prop where
  L : c ∈ L
  G1 : c ∈ S.G1
  V : c ∈ Subgroup.normalizer (V : Set G)
  rho : S.frame.ρ ⟨c, V⟩ = tau3

theorem GData.sigma {g : G} (hg : S.GData g) :
    StabW2 (S.frame.ρ ⟨g, S.frame.L_le hg.L⟩) ∧ S.frame.ρ ⟨g, S.frame.L_le hg.L⟩ ^ 45 = 1 ∧
      act4f (S.frame.ρ ⟨g, S.frame.L_le hg.L⟩) e0123 ≠ e0123 := by
  set gN : ↥(Subgroup.normalizer (V : Set G)) := ⟨g, S.frame.L_le hg.L⟩ with hgN
  refine ⟨S.stabW2_of_mem (x := gN) hg.N, ?_, fun h => hg.H ?_⟩
  · obtain ⟨m, hm, hgm⟩ := hg.odd
    refine pow_45_of_odd hm ?_
    rw [← map_pow]
    have : gN ^ m = 1 := Subtype.ext (by simpa using hgm)
    rw [this, map_one]
  · rw [S.mem_G1_iff_conj]
    have h1 := S.psi_conj_z gN
    rw [h] at h1
    exact S.eq_of_psi_eq (h1.trans (congrArg Subtype.val S.psi_z).symm)

theorem CData.u1_mem_V3 (hc : S.CData c) : c * S.u1 * c⁻¹ ∈ S.V3 :=
  S.mem_pre.2 ⟨_, by
    have h1 := S.psi_conj_u1 ⟨c, hc.V⟩
    rw [hc.rho] at h1
    show InW3 _
    rw [h1]
    exact tau3_facts.1⟩

theorem CData.sq_u1_mem_V3 (hc : S.CData c) : c * c * S.u1 * (c * c)⁻¹ ∈ S.V3 := by
  have hV : c * c ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ hc.V hc.V
  refine S.mem_pre.2 ⟨(Subgroup.mem_normalizer_iff.mp hV _).mp S.u1_mem_V, ?_⟩
  have h1 := S.psi_conj_u1 ⟨c * c, hV⟩
  have h2 : S.frame.ρ ⟨c * c, hV⟩ = tau3 * tau3 := by
    rw [show (⟨c * c, hV⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨c, hc.V⟩ * ⟨c, hc.V⟩ from rfl,
      map_mul, hc.rho]
  rw [h2] at h1
  show InW3 _
  rw [h1]
  exact tau3_facts.2.1

theorem CData.u1_eq (hc : S.CData c) : c * S.u1 * c⁻¹ = S.u1 * S.u2 := by
  have h1 := S.psi_conj_u1 ⟨c, hc.V⟩
  rw [hc.rho, tau3_facts.2.2] at h1
  refine S.eq_of_psi_eq (hb := V.mul_mem S.u1_mem_V S.u2_mem_V) (h1.trans ?_)
  have e : (⟨S.u1 * S.u2, V.mul_mem S.u1_mem_V S.u2_mem_V⟩ : ↥V) =
      ⟨S.u1, S.u1_mem_V⟩ * ⟨S.u2, S.u2_mem_V⟩ := rfl
  rw [e, map_mul, Subgroup.coe_mul, S.psi_u1, S.psi_u2]

variable {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}
  {γ : ↥(conjClosure V S.G1) →* Multiplicative (Fin 6 → ZMod 2)}

theorem conjSub_UH_le_Xs_of_V3 [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β)
    (hg : S.GData g) (hc : S.CData c)
    (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v)
    {l : G} (hl : l ∈ L) (hl3 : l * S.z * l⁻¹ ∈ S.V3) :
    conjSub l (conjClosure S.V3 S.G1) ≤ S.Xs β γ := by
  set gN : ↥(Subgroup.normalizer (V : Set G)) := ⟨g, S.frame.L_le hg.L⟩ with hgN
  set cN : ↥(Subgroup.normalizer (V : Set G)) := ⟨c, hc.V⟩ with hcN
  set lN : ↥(Subgroup.normalizer (V : Set G)) := ⟨l, S.frame.L_le hl⟩ with hlN
  have hgV := S.frame.L_le hg.L
  have hU0X := S.U0_le_Xs D hg.L hg.N hg.H hγ hΘ
  have hk : ∀ k : ℕ, conjSub (g ^ k) (conjClosure S.V3 S.G1) ≤ S.U0 g :=
    S.conjSub_pow_UH_le_U0 D hgV hg.N hg.H
  have hc1 : conjSub c (S.U0 g) ≤ S.Xs β γ :=
    S.conjSub_U0_le_Xs (c := ⟨c, hc.G1⟩) D hg.L hg.N hg.H hγ hΘ hc.u1_mem_V3
  have hc2 : conjSub (c * c) (S.U0 g) ≤ S.Xs β γ :=
    S.conjSub_U0_le_Xs (c := ⟨c * c, S.G1.mul_mem hc.G1 hc.G1⟩) D hg.L hg.N hg.H hγ hΘ
      hc.sq_u1_mem_V3
  have hlz : l * S.z * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp lN.2 _).mp S.z_mem_V
  have hy3 : InW3 (S.frame.ψ ⟨_, hlz⟩ : P6) := by
    obtain ⟨hV, hW⟩ := S.mem_pre.1 hl3
    exact hW
  have hy1 : (S.frame.ψ ⟨_, hlz⟩ : P6) ≠ 1 := by
    intro h1
    apply S.z_ne_one
    have h2 : (⟨l * S.z * l⁻¹, hlz⟩ : ↥V) = 1 :=
      S.frame.ψ.injective (by rw [map_one]; exact Subtype.ext h1)
    have h3 : l * S.z * l⁻¹ = 1 := congrArg Subtype.val h2
    calc S.z = l⁻¹ * (l * S.z * l⁻¹) * l := by group
      _ = 1 := by rw [h3]; group
  have hpts := v3pt_check _ hg.sigma _ ⟨(S.frame.ψ ⟨_, hlz⟩).2, hy3, hy1⟩
  have key : ∀ x : ↥(Subgroup.normalizer (V : Set G)),
      (S.frame.ψ ⟨_, hlz⟩ : P6) = act4f (S.frame.ρ x) e0123 →
      conjSub (x : G) (conjClosure S.V3 S.G1) ≤ S.Xs β γ →
      conjSub l (conjClosure S.V3 S.G1) ≤ S.Xs β γ := by
    intro x hx hxX
    rw [S.conjSub_UH_eq_of_conj (S.eq_of_psi_eq (hx.trans (S.psi_conj_z x).symm))]
    exact hxX
  have hρc : S.frame.ρ cN = tau3 := hc.rho
  rcases hpts with h | h | h | h | h | h | h
  · refine key 1 (by rw [h, map_one, act4f_one _ e0123_mem_W4]) ?_
    rw [show ((1 : ↥(Subgroup.normalizer (V : Set G))) : G) = 1 from rfl, conjSub_one]
    exact (le_sup_left.trans hU0X)
  · refine key gN h ?_
    have h1 : conjSub g (conjClosure S.V3 S.G1) ≤ S.U0 g := by simpa using hk 1
    exact h1.trans hU0X
  · refine key (gN * gN) (by rw [h, map_mul]) ?_
    have e : ((gN * gN : ↥(Subgroup.normalizer (V : Set G))) : G) = g ^ 2 := by
      simp [hgN, pow_two]
    rw [e]
    exact (hk 2).trans hU0X
  · refine key (cN * gN) (by rw [h, map_mul, hρc]) ?_
    have e : ((cN * gN : ↥(Subgroup.normalizer (V : Set G))) : G) = c * g ^ 1 := by
      simp [hgN, hcN]
    rw [e, conjSub_mul]
    exact (conjSub_mono _ (hk 1)).trans hc1
  · refine key (cN * (gN * gN)) (by rw [h, map_mul, map_mul, hρc]) ?_
    have e : ((cN * (gN * gN) : ↥(Subgroup.normalizer (V : Set G))) : G) = c * g ^ 2 := by
      simp [hgN, hcN, pow_two]
    rw [e, conjSub_mul]
    exact (conjSub_mono _ (hk 2)).trans hc1
  · refine key (cN * cN * gN) (by rw [h, map_mul, map_mul, hρc]) ?_
    have e : ((cN * cN * gN : ↥(Subgroup.normalizer (V : Set G))) : G) = c * c * g ^ 1 := by
      simp [hgN, hcN]
    rw [e, conjSub_mul]
    exact (conjSub_mono _ (hk 1)).trans hc2
  · refine key (cN * cN * (gN * gN)) (by rw [h, map_mul, map_mul, map_mul, hρc]) ?_
    have e : ((cN * cN * (gN * gN) : ↥(Subgroup.normalizer (V : Set G))) : G) =
        c * c * g ^ 2 := by
      simp [hgN, hcN, pow_two]
    rw [e, conjSub_mul]
    exact (conjSub_mono _ (hk 2)).trans hc2

theorem exists_conjSub_UH_le [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β)
    (hg : S.GData g) (hc : S.CData c)
    (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v)
    {l : G} (hl : l ∈ L) :
    ∃ i : Fin 3, conjSub l (conjClosure S.V3 S.G1) ≤ conjSub (g ^ (i : ℕ)) (S.Xs β γ) := by
  set gN : ↥(Subgroup.normalizer (V : Set G)) := ⟨g, S.frame.L_le hg.L⟩ with hgN
  set lN : ↥(Subgroup.normalizer (V : Set G)) := ⟨l, S.frame.L_le hl⟩ with hlN
  have hlz : l * S.z * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp lN.2 _).mp S.z_mem_V
  obtain ⟨i, hi⟩ := gq_check _ hg.sigma _ (S.frame.ψ ⟨_, hlz⟩).2
  refine ⟨i, ?_⟩
  set x : ↥(Subgroup.normalizer (V : Set G)) := (gN ^ (i : ℕ))⁻¹ with hx
  have hxL : (x : G) * l ∈ L := by
    refine L.mul_mem ?_ hl
    rw [hx]
    simpa using L.inv_mem (L.pow_mem hg.L (i : ℕ))
  have h3 : ((x : G) * l) * S.z * ((x : G) * l)⁻¹ ∈ S.V3 := by
    have hv := S.psi_conj x ⟨_, hlz⟩
    have e : ((x : G) * l) * S.z * ((x : G) * l)⁻¹ = (x : G) * (l * S.z * l⁻¹) * (x : G)⁻¹ := by
      group
    rw [e]
    refine S.mem_pre.2 ⟨(Subgroup.mem_normalizer_iff.mp x.2 _).mp hlz, ?_⟩
    show InW3 (S.frame.ψ ⟨_, _⟩ : P6)
    rw [show (S.frame.ψ ⟨(x : G) * (l * S.z * l⁻¹) * (x : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp x.2 _).mp hlz⟩ : P6) =
      (act4 (S.frame.ρ x) (S.frame.ψ ⟨_, hlz⟩) : P6) from congrArg Subtype.val hv]
    rw [hx, map_inv, map_pow, ← inv_pow]
    exact hi
  have h4 := S.conjSub_UH_le_Xs_of_V3 D hg hc hγ hΘ hxL h3
  have e : l = (g ^ (i : ℕ)) * ((x : G) * l) := by
    rw [hx]
    simp [hgN]
  rw [e, conjSub_mul]
  exact conjSub_mono _ h4

end Cover

end Setting4

end CFSG.Quasithin.H13.A6

