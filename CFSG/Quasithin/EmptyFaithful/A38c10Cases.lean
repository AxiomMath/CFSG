module

public import CFSG.Quasithin.EmptyFaithful.SBd7Gen
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.FLcLn
public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.EmptyFaithful.S153Cases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.InternalSec CFSG.Quasithin.S1417
open scoped commutatorElement IsMulCommutative

section Cases

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem exists_moves_Z (h113 : StageLemma14113) (hh : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    ∃ y ∈ Yp, ∃ z ∈ quasithinOmegaOneCenter T, y * z * y⁻¹ ≠ z := by
  by_contra hcon
  push Not at hcon
  have hcc : conjClosure (quasithinOmegaOneCenter T) Yp ≤ quasithinOmegaOneCenter T :=
    conjClosure_le fun g hg z hz => by rw [hcon g hg z hz]; exact hz
  have hcen : ∀ y ∈ Yp, ∀ v ∈ quasithinOmegaOneCenter T, v * y = y * v := by
    intro y hy v hv
    have := hcon y hy v hv
    calc v * y = (y * v * y⁻¹) * y := by rw [this]
      _ = y * v := by group
  rcases hh.cases with hY | ⟨-, hY⟩
  · refine hh.hyp.Y153_not_le_centralizer h113 ?_
    have hVZ : VZ T M ≤ quasithinOmegaOneCenter T := by
      rw [hh.hyp.VZ_eq_conjClosure_Y153 h113, ← hY]
      exact hcc
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rw [hY] at hcen
    exact hcen y hy v (hVZ hv)
  · have hV₂ : V₂ ≤ quasithinOmegaOneCenter T := by
      have := hh.hyp.V₂_le_conjClosure_Yplus h113 hh.decomp
      rw [← hY] at this
      exact this.trans hcc
    have hYV₁ : Yp ≤ Subgroup.centralizer (V₁ : Set G) := by
      rw [hY]
      exact (oTwoUpper_le _).trans inf_le_right
    have hYV₂ : Yp ≤ Subgroup.centralizer (V₂ : Set G) := fun y hy => by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hcen y hy v (hV₂ hv)
    have hYV : Yp ≤ Subgroup.centralizer (VZ T M : Set G) := by
      rw [Subgroup.le_centralizer_iff, ← hh.decomp.sup]
      exact sup_le (Subgroup.le_centralizer_iff.mp hYV₁) (Subgroup.le_centralizer_iff.mp hYV₂)
    rw [hY] at hYV
    exact hh.hyp.Yplus_not_le_centralizer h113 hh.decomp hYV

end Cases
section Odd

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_isPGroup_odd {P : Subgroup G} (hP : IsPGroup 2 ↥P) {y : G} (hy : y ∈ P)
    (hodd : Odd (orderOf y)) : y = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨y, hy⟩
  have hk' : orderOf y = 2 ^ k := (Subgroup.orderOf_coe (⟨y, hy⟩ : P)).trans hk
  rw [hk'] at hodd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hk0, pow_zero] at hk'
  exact orderOf_eq_one_iff.mp hk'

theorem card_eq_nine_of_elemAbelian {X : Type*} [Group X] (hE : IsElemAbelianOfRank 3 2 X) :
    Nat.card X = 9 := by
  obtain ⟨e⟩ := hE
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  simp [Fintype.card_pi]

variable {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem odd_centralizes_Z_trivial (h113 : StageLemma14113) (hh : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (hYY : Yp = Y153 Mc M) (hE : IsElemAbelianOfRank 3 2 (OTwoQuot Yp)) {y : G} (hy : y ∈ Yp)
    (hodd : Odd (orderOf y)) (hz : ∀ z ∈ quasithinOmegaOneCenter T, y * z * y⁻¹ = z) : y = 1 := by
  subst hYY
  rcases Hyp153.lemma_15_3_7_cases h113 hh.hyp with ⟨hcore, -⟩ | ⟨hP, -⟩
  · obtain ⟨e⟩ := hE
    have hab : ∀ a b : OTwoQuot (Y153 Mc M), a * b = b * a := by
      intro a b
      apply e.injective
      rw [map_mul, map_mul]
      exact mul_comm _ _
    have hcomm : ∀ g ∈ Y153 Mc M, (g⁻¹ * y * g) * y⁻¹ ∈ pCoreOf 2 (Y153 Mc M) := by
      intro g hg
      have h1 : (⟨g, hg⟩ : ↥(Y153 Mc M))⁻¹ * ⟨y, hy⟩ * ⟨g, hg⟩ * ⟨y, hy⟩⁻¹ ∈
          CFSG.Open.pCore 2 ↥(Y153 Mc M) := by
        have : (⟨g, hg⟩ : ↥(Y153 Mc M))⁻¹ * ⟨y, hy⟩ * ⟨g, hg⟩ * ⟨y, hy⟩⁻¹ =
            ⁅(⟨g, hg⟩ : ↥(Y153 Mc M))⁻¹, ⟨y, hy⟩⁆ := by simp [commutatorElement_def]
        have h2 : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(Y153 Mc M)))
            ⁅(⟨g, hg⟩ : ↥(Y153 Mc M))⁻¹, ⟨y, hy⟩⁆ = 1 := by
          rw [map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.2 (hab _ _)
        rw [this, ← QuotientGroup.eq_one_iff]
        exact h2
      exact ⟨_, h1, rfl⟩
    have hcen : ∀ g ∈ Y153 Mc M, ∀ z ∈ quasithinOmegaOneCenter T,
        (g * z * g⁻¹) * y = y * (g * z * g⁻¹) := by
      intro g hg z hz'
      have ho := hcore ▸ hcomm g hg
      have hoc : ((g⁻¹ * y * g) * y⁻¹) * z = z * ((g⁻¹ * y * g) * y⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp ho.2 z (hh.hyp.Z_le_VZ hz')).symm
      have hyz : y * z = z * y := by
        have := hz z hz'
        calc y * z = (y * z * y⁻¹) * y := by group
          _ = z * y := by rw [this]
      calc (g * z * g⁻¹) * y = g * (z * ((g⁻¹ * y * g) * y⁻¹) * y) * g⁻¹ := by group
        _ = g * (((g⁻¹ * y * g) * y⁻¹) * z * y) * g⁻¹ := by rw [← hoc]
        _ = g * ((g⁻¹ * y * g) * (y⁻¹ * (z * y))) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * (y⁻¹ * (y * z))) * g⁻¹ := by rw [hyz]
        _ = y * (g * z * g⁻¹) := by group
    have hV : VZ T M ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [hh.hyp.VZ_eq_conjClosure_Y153 h113]
      refine conjClosure_le fun g hg z hz' => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcen g hg z hz'
    have hyC : y ∈ Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
      refine ⟨hy, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
      exact (Subgroup.mem_centralizer_singleton_iff).mp (hV hv)
    rw [← hcore] at hyC
    exact eq_one_of_isPGroup_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hyC hodd
  · exfalso
    have h27 : Nat.card (OTwoQuot (Y153 Mc M)) = 3 ^ 3 := hP.2.1
    rw [card_eq_nine_of_elemAbelian hE] at h27
    omega

end Odd
section Close

variable {G : Type} [Group G] [Finite G]

theorem closeV {L S Yp Y₁ Y₂ Vp V₁ : Subgroup G}
    (hUc : ∀ a ∈ Vp, ∀ b ∈ Vp, a * b = b * a) (hV2 : ∀ a ∈ Vp, a ^ 2 = 1)
    (hLN : L ≤ Subgroup.normalizer (Vp : Set G)) (hS2 : IsPGroup 2 ↥S)
    (hsplit : ∀ w ∈ Vp, ∃ c ∈ Vp ⊓ Subgroup.centralizer (L : Set G), ∃ u ∈ ⁅Vp, L⁆, w = c * u)
    (hkey : ∀ u ∈ ⁅Vp, L⁆, (∀ b ∈ S ⊓ L, b * u * b⁻¹ = u) → (∀ y ∈ Y₁ ⊔ Y₂, y * u * y⁻¹ = u) →
      u = 1)
    (hV₁ : V₁ ≤ Vp) (hSV₁ : S ≤ Subgroup.normalizer (V₁ : Set G))
    (hYV₁ : Yp ≤ Subgroup.centralizer (V₁ : Set G)) (hY : Y₁ ⊔ Y₂ ≤ Yp) (hYL : Yp ≤ L) :
    V₁ ≤ Subgroup.centralizer (L : Set G) := by
  classical
  have hUVp : ⁅Vp, L⁆ ≤ Vp := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  have hLU : ∀ l ∈ L, ∀ u ∈ ⁅Vp, L⁆, l * u * l⁻¹ ∈ ⁅Vp, L⁆ := fun l hl u hu =>
    (Subgroup.mem_normalizer_iff.mp
      (SBd5.mem_normalizer_commutator_of (hLN hl) (Subgroup.le_normalizer hl)) u).mp hu
  let X : Subgroup G :=
    { carrier := {u | u ∈ ⁅Vp, L⁆ ∧ ∃ c ∈ Vp ⊓ Subgroup.centralizer (L : Set G), c * u ∈ V₁}
      one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, c₁, hc₁, h₁⟩ ⟨hb, c₂, hc₂, h₂⟩
        refine ⟨Subgroup.mul_mem _ ha hb, c₁ * c₂, Subgroup.mul_mem _ hc₁ hc₂, ?_⟩
        have e : c₁ * c₂ * (a * b) = (c₁ * a) * (c₂ * b) := by
          have := hUc c₂ hc₂.1 a (hUVp ha)
          calc c₁ * c₂ * (a * b) = c₁ * (c₂ * a) * b := by group
            _ = c₁ * (a * c₂) * b := by rw [this]
            _ = (c₁ * a) * (c₂ * b) := by group
        rw [e]
        exact V₁.mul_mem h₁ h₂
      inv_mem' := by
        rintro a ⟨ha, c, hc, h⟩
        refine ⟨Subgroup.inv_mem _ ha, c⁻¹, Subgroup.inv_mem _ hc, ?_⟩
        have e : c⁻¹ * a⁻¹ = (c * a)⁻¹ := by
          have := hUc c hc.1 a (hUVp ha)
          calc c⁻¹ * a⁻¹ = (a * c)⁻¹ := by group
            _ = (c * a)⁻¹ := by rw [this]
        rw [e]
        exact V₁.inv_mem h }
  have hXmem : ∀ u, u ∈ X ↔ u ∈ ⁅Vp, L⁆ ∧ ∃ c ∈ Vp ⊓ Subgroup.centralizer (L : Set G), c * u ∈ V₁ :=
    fun u => Iff.rfl
  have hX2 : IsPGroup 2 ↥X := fun x => ⟨1, Subtype.ext (by simpa using hV2 x (hUVp x.2.1))⟩
  have hB2 : IsPGroup 2 ↥(S ⊓ L) := hS2.to_le inf_le_left
  have hBX : ∀ b ∈ S ⊓ L, ∀ u ∈ X, b * u * b⁻¹ ∈ X := by
    intro b hb u hu
    obtain ⟨hu1, c, hc, hcu⟩ := (hXmem u).1 hu
    refine (hXmem _).2 ⟨hLU b hb.2 u hu1, c, hc, ?_⟩
    have h1 : b * (c * u) * b⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp (hSV₁ hb.1) _).mp hcu
    have hbc : b * c * b⁻¹ = c := by
      have := Subgroup.mem_centralizer_iff.mp hc.2 b hb.2
      calc b * c * b⁻¹ = c * b * b⁻¹ := by rw [← this]
        _ = c := by group
    have e : c * (b * u * b⁻¹) = b * (c * u) * b⁻¹ := by
      calc c * (b * u * b⁻¹) = (b * c * b⁻¹) * (b * u * b⁻¹) := by rw [hbc]
        _ = b * (c * u) * b⁻¹ := by group
    rw [e]
    exact h1
  have hBN : S ⊓ L ≤ Subgroup.normalizer (X : Set G) :=
    FLc.le_normalizer_of_conj_mem hBX
  have hX0 : X = ⊥ := by
    by_contra hne
    have hsup : IsPGroup 2 ↥(X ⊔ (S ⊓ L)) := hX2.to_sup_of_normal_left' hB2 hBN
    obtain ⟨u, huX, hu1, hufix⟩ := SBd7.exists_central_of_normal hsup le_sup_left
      (sup_le Subgroup.le_normalizer hBN) hne
    obtain ⟨hu, c, hc, hcu⟩ := (hXmem u).1 huX
    apply hu1
    refine hkey u hu (fun b hb => hufix b (Subgroup.mem_sup_right hb)) (fun y hy => ?_)
    have hyp : y ∈ Yp := hY hy
    have hyc : y * c * y⁻¹ = c := by
      have := Subgroup.mem_centralizer_iff.mp hc.2 y (hYL hyp)
      calc y * c * y⁻¹ = c * y * y⁻¹ := by rw [← this]
        _ = c := by group
    have hyv : y * (c * u) * y⁻¹ = c * u := by
      have := Subgroup.mem_centralizer_iff.mp (hYV₁ hyp) _ hcu
      calc y * (c * u) * y⁻¹ = (c * u) * y * y⁻¹ := by rw [← this]
        _ = c * u := by group
    have e : y * (c * u) * y⁻¹ = c * (y * u * y⁻¹) := by
      calc y * (c * u) * y⁻¹ = (y * c * y⁻¹) * (y * u * y⁻¹) := by group
        _ = c * (y * u * y⁻¹) := by rw [hyc]
    rw [e] at hyv
    exact mul_left_cancel hyv
  intro v hv
  obtain ⟨c, hc, u, hu, hvcu⟩ := hsplit v (hV₁ hv)
  have huX : u ∈ X := (hXmem u).2 ⟨hu, c, hc, hvcu ▸ hv⟩
  rw [hX0, Subgroup.mem_bot] at huX
  rw [hvcu, huX, mul_one]
  exact hc.2

end Close

end CFSG.Quasithin.A38c10
