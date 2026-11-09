module

import CFSG.Quasithin.Background.F7Basic
public import CFSG.LocalAnalysis.QuasithinUnique.AGFusion

section

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique

section Fixed

variable {G : Type*} [Group G] [Finite G]

theorem isSylowTwoOf_of_unique_fixed {X Y P : Subgroup G} {z : G} (hXY : X ≤ Y)
    (hP : IsSylowTwoOf P X) (hzP : z ∈ P) (H1 : ∀ g ∈ Y, g⁻¹ * z * g ∈ X → g ∈ X) :
    IsSylowTwoOf P Y := by
  have hPX : P ≤ X := hP.1
  have hPY : P ≤ Y := hPX.trans hXY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X' : Subgroup ↥Y := X.subgroupOf Y with hX'
  set P' : Subgroup ↥Y := P.subgroupOf Y with hP'
  have hP2 : IsPGroup 2 ↥P' := hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm
  have hmod := hP2.card_modEq_card_fixedPoints (↥Y ⧸ X')
  have hfix : MulAction.fixedPoints ↥P' (↥Y ⧸ X') = {((1 : ↥Y) : ↥Y ⧸ X')} := by
    ext c
    induction c using QuotientGroup.induction_on with
    | H g =>
      simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
      constructor
      · intro h
        have hz : (⟨z, hPY hzP⟩ : ↥Y) ∈ P' := hzP
        have h1 := h ⟨⟨z, hPY hzP⟩, hz⟩
        have h2 : ((⟨z, hPY hzP⟩ * g : ↥Y) : ↥Y ⧸ X') = (g : ↥Y ⧸ X') := h1
        rw [QuotientGroup.eq] at h2
        have hg : (g : G)⁻¹ * z * (g : G) ∈ X := by
          have := X.inv_mem (Subgroup.mem_subgroupOf.1 h2)
          simpa [mul_assoc] using this
        have hgX : (g : G) ∈ X := H1 g g.2 hg
        rw [QuotientGroup.eq]
        have : (g : ↥Y) ∈ X' := Subgroup.mem_subgroupOf.2 hgX
        simpa using this
      · intro h m
        have hg : (g : ↥Y) ∈ X' := by
          rw [QuotientGroup.eq] at h
          simpa using X'.inv_mem h
        have hm : ((m : ↥P') : ↥Y) ∈ X' := hPX m.2
        show (((m : ↥P') : ↥Y) * g : ↥Y) = (g : ↥Y ⧸ X')
        rw [QuotientGroup.eq]
        simpa [mul_assoc] using X'.mul_mem (X'.mul_mem (X'.inv_mem hg) (X'.inv_mem hm)) hg
  rw [hfix] at hmod
  have hcard : Nat.card (↥Y ⧸ X') % 2 = 1 := by
    have h1 : Nat.card (↥(({((1 : ↥Y) : ↥Y ⧸ X')} : Set (↥Y ⧸ X')))) = 1 := by simp
    have := hmod
    unfold Nat.ModEq at this
    rw [h1] at this
    simpa using this
  refine ⟨hPY, hP.2.1, ?_⟩
  have hodd : ¬ 2 ∣ X.relIndex Y := by
    rw [Subgroup.relIndex]
    change ¬ 2 ∣ Nat.card (↥Y ⧸ X')
    omega
  have hX2 : ¬ 2 ∣ P.relIndex X := hP.2.2
  intro h
  have : 2 ∣ P.relIndex X * X.relIndex Y := by
    rw [Subgroup.relIndex_mul_relIndex P X Y hPX hXY]
    exact h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 this with h1 | h1
  · exact hX2 h1
  · exact hodd h1

theorem exists_conj_of_unique_fixed {X P : Subgroup G} {z : G} (hPG : IsSylowTwoOf P ⊤)
    (hPX : P ≤ X) (hzP : z ∈ P) (hzc : ∀ y ∈ P, y * z = z * y)
    (H1 : ∀ g : G, g⁻¹ * z * g ∈ X → g ∈ X) {a g : G} (ha : a ∈ X) (ha2 : ∃ k : ℕ, a ^ 2 ^ k = 1)
    (hag : g⁻¹ * a * g ∈ X) : ∃ x ∈ X, g⁻¹ * a * g = x⁻¹ * a * x := by
  refine exists_conj_eq_of_ag hPG hPX (fun D hD n hn => ?_) ha ha2 hag
  have hzD : z ∈ D := hD.center_le hPG ⟨hzP, Subgroup.mem_centralizer_iff.2 hzc⟩
  have h1 : n⁻¹ * z * n ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (D : Set G)).inv_mem hn) z).mp
      hzD
    simpa using this
  exact H1 n (hPX (hD.1 h1))

end Fixed

end CFSG.Quasithin.H13.F431.Un

end

end

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

structure Loc442UCore {G : Type} [Group G] (X Y V U R K P : Subgroup G) (z t : G) : Prop where
  XY : X ≤ Y
  t_cent : ∀ y ∈ Y, y * t = t * y
  t_U : t ∈ U
  H1 : ∀ x ∈ X, ∀ g ∈ Y, g⁻¹ * (x * z * x⁻¹) * g ∈ X → g ∈ X
  P_X : P ≤ X
  P_syl : IsSylowTwoOf P X
  z_P : z ∈ P
  P_z : ∀ y ∈ P, y * z = z * y
  P_U : ∀ y ∈ P, ∀ u ∈ U, y * u = u * y
  V_X : V ≤ X
  V_norm : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V
  V_ab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  V_sq : ∀ a ∈ V, a ^ 2 = 1
  U_V : U ≤ V
  U_norm : ∀ x ∈ X, ∀ u ∈ U, x * u * x⁻¹ ∈ U
  K_X : K ≤ X
  K_perf : ⁅K, K⁆ = K
  V_K : V ≤ K
  K_cent : ∀ k ∈ K, ∀ u ∈ U, k * u = u * k
  coset : ∀ v ∈ V, v ∉ U → ∃ x ∈ X, ∃ u ∈ U, v = x * z * x⁻¹ * u
  nonsolv : ∃ L : Subgroup G, L ≤ X ∧ ¬ Group.IsSolvable ↥L ∧ ∀ L' : Subgroup G, L' ≤ L →
    (∀ x ∈ L', ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ U) → Group.IsSolvable ↥L'
  R_V : R ≤ V
  R_two : ∃ a ∈ R, ∃ b ∈ R, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b
  R_cls : ∀ r ∈ R, r ≠ 1 → ∃ x ∈ X, r = x * z * x⁻¹
  R_U : ∀ r ∈ R, r ∈ U → r = 1

@[expose] def nS {G : Type} [Group G] (S W : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (W : Set G) ⊓ S

theorem le_normalizer_of_conj {H : Type*} [Group H] {S W : Subgroup H}
    (h : ∀ x ∈ S, ∀ w ∈ W, x * w * x⁻¹ ∈ W) : S ≤ Subgroup.normalizer (W : Set H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => h x hx w hw, fun hw => ?_⟩
  have := h x⁻¹ (S.inv_mem hx) _ hw
  rwa [show x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ = w by group] at this

section Basic

variable {G : Type} [Group G] {X Y V U R K P : Subgroup G} {z t : G}

theorem Loc442UCore.X_le_normalizer_U (D : Loc442UCore X Y V U R K P z t) :
    X ≤ Subgroup.normalizer (U : Set G) :=
  le_normalizer_of_conj D.U_norm

theorem Loc442UCore.X_le_normalizer_V (D : Loc442UCore X Y V U R K P z t) :
    X ≤ Subgroup.normalizer (V : Set G) :=
  le_normalizer_of_conj D.V_norm

theorem Loc442UCore.not_V_le_U (D : Loc442UCore X Y V U R K P z t) : ¬ V ≤ U := by
  intro hVU
  obtain ⟨L, hLX, hLns, hL⟩ := D.nonsolv
  refine hLns (hL L le_rfl fun x hx v hv => ?_)
  exact U.mul_mem (hVU (D.V_norm x (hLX hx) v hv)) (U.inv_mem (hVU hv))

theorem Loc442UCore.H1' (D : Loc442UCore X Y V U R K P z t) :
    ∀ g ∈ Y, g⁻¹ * z * g ∈ X → g ∈ X := fun g hg h =>
  D.H1 1 X.one_mem g hg (by simpa using h)

theorem Loc442UCore.sylow_Y [Finite G] (D : Loc442UCore X Y V U R K P z t) :
    IsSylowTwoOf P Y :=
  isSylowTwoOf_of_unique_fixed D.XY D.P_syl D.z_P D.H1'

theorem isSylowTwoOf_subgroupOf_top' {P N : Subgroup G} (hP : IsSylowTwoOf P N) :
    IsSylowTwoOf (P.subgroupOf N) ⊤ := by
  refine ⟨le_top, hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm, ?_⟩
  have h : ((P.subgroupOf N).subgroupOf (⊤ : Subgroup N)).index = (P.subgroupOf N).index :=
    Subgroup.relIndex_top_right (P.subgroupOf N)
  rw [h]
  exact hP.2.2

end Basic

section Fusion

variable {G : Type} [Group G] [Finite G] {X Y V U R K P : Subgroup G} {z t : G}

theorem Loc442UCore.fusion_nS (D : Loc442UCore X Y V U R K P z t) {W : Subgroup G}
    (hPW : P ≤ Subgroup.normalizer (W : Set G)) {a g : G} (ha : a ∈ nS X W) (ha2 : a ^ 2 = 1)
    (hg : g ∈ nS Y W) (hag : g⁻¹ * a * g ∈ nS X W) :
    ∃ x ∈ nS X W, g⁻¹ * a * g = x⁻¹ * a * x := by
  set N : Subgroup G := nS Y W with hN
  have hNY : N ≤ Y := inf_le_right
  have hXN : nS X W ≤ N := fun x hx => ⟨hx.1, D.XY hx.2⟩
  have hPN : P ≤ N := fun p hp => ⟨hPW hp, D.XY (D.P_X hp)⟩
  have hzN : z ∈ N := hPN D.z_P
  have hPsyl : IsSylowTwoOf P N := F7.isSylowTwoOf_mono_right D.sylow_Y hPN hNY
  have hH1 : ∀ g : ↥N, g⁻¹ * (⟨z, hzN⟩ : ↥N) * g ∈ (nS X W).subgroupOf N →
      g ∈ (nS X W).subgroupOf N := fun g hg => ⟨g.2.1, D.H1' g (hNY g.2) hg.2⟩
  obtain ⟨x, hx, hxe⟩ := exists_conj_of_unique_fixed (X := (nS X W).subgroupOf N)
    (P := P.subgroupOf N) (z := (⟨z, hzN⟩ : ↥N)) (isSylowTwoOf_subgroupOf_top' hPsyl)
    (fun p hp => ⟨hPW hp, D.P_X hp⟩) D.z_P (fun y hy => Subtype.ext (D.P_z y hy)) hH1
    (a := (⟨a, hXN ha⟩ : ↥N)) (g := (⟨g, hg⟩ : ↥N)) ha
    ⟨1, by rw [pow_one]; exact Subtype.ext ha2⟩ hag
  exact ⟨(x : G), hx, congrArg Subtype.val hxe⟩

end Fusion

section Extremal

variable {G : Type} [Group G] [Finite G] {X Y V U R K P : Subgroup G} {z t : G}

@[expose] def Qual (X Y U : Subgroup G) (t : G) (W : Subgroup G) : Prop :=
  t ∈ W ∧ W ≤ U ∧ nS X W < nS Y W

omit [Finite G] in
theorem Loc442UCore.conj_zpowers (D : Loc442UCore X Y V U R K P z t) {y : G} (hy : y ∈ Y) :
    ∀ w ∈ Subgroup.zpowers t, y * w * y⁻¹ = w := by
  intro w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hc : y * t * y⁻¹ = t := by rw [D.t_cent y hy]; group
  rw [← conj_zpow, hc]

omit [Finite G] in
theorem Loc442UCore.Y_le_normalizer (D : Loc442UCore X Y V U R K P z t) :
    Y ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => by rw [D.conj_zpowers hy w hw]; exact hw, fun hw => ?_⟩
  have h1 := D.conj_zpowers (Y.inv_mem hy) _ hw
  rw [show y⁻¹ * (y * w * y⁻¹) * y⁻¹⁻¹ = w by group] at h1
  rw [← h1] at hw
  exact hw

theorem Loc442UCore.exists_maximal (D : Loc442UCore X Y V U R K P z t) (hYX : ¬ Y ≤ X) :
    ∃ W, Qual X Y U t W ∧ ∀ W', Qual X Y U t W' → W ≤ W' → W' ≤ W := by
  have hQ : Qual X Y U t (Subgroup.zpowers t) := by
    refine ⟨Subgroup.mem_zpowers t, Subgroup.zpowers_le.mpr D.t_U, ?_⟩
    have e1 : nS X (Subgroup.zpowers t) = X := inf_eq_right.mpr (D.XY.trans D.Y_le_normalizer)
    have e2 : nS Y (Subgroup.zpowers t) = Y := inf_eq_right.mpr D.Y_le_normalizer
    rw [e1, e2]
    exact lt_of_le_of_ne D.XY (fun h => hYX (le_of_eq h.symm))
  obtain ⟨W, hW⟩ := Set.Finite.exists_maximal (Set.toFinite {W : Subgroup G | Qual X Y U t W})
    ⟨_, hQ⟩
  exact ⟨W, hW.1, fun W' h1 h2 => hW.2 h1 h2⟩

end Extremal

end CFSG.Quasithin.H13.F431.Un
