module

public import CFSG.Quasithin.EmptyFaithful.SBc8Fix
public import CFSG.Quasithin.EmptyFaithful.SBc8Dual

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc8

section Irr

variable {G : Type} [Group G] {F : Type} [Field F] [Fintype F]

theorem irreducible_of_natural (hF : Fintype.card F = 2) {L W : Subgroup G}
    (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (hαs : Function.Surjective α)
    (β : ↥W →* Multiplicative (Fin 1 → Fin 3 → F)) (hβi : Function.Injective β)
    (hβe : ∀ (a : ↥L) (u v : ↥W), (v : G) = a * u * a⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        ((α a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (β u) i)) :
    ∀ X : Subgroup G, X ≤ W → L ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = W := by
  intro X hXW hLX
  let A : AddSubgroup (Fin 3 → F) :=
    { carrier := {v | ∃ u : G, ∃ hu : u ∈ X, Multiplicative.toAdd (β ⟨u, hXW hu⟩) 0 = v}
      zero_mem' := ⟨1, X.one_mem, by
        rw [show (⟨1, hXW X.one_mem⟩ : ↥W) = 1 from rfl, map_one]
        rfl⟩
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        refine ⟨u * u', X.mul_mem hu hu', ?_⟩
        rw [show (⟨u * u', hXW (X.mul_mem hu hu')⟩ : ↥W) = ⟨u, hXW hu⟩ * ⟨u', hXW hu'⟩ from rfl,
          map_mul, toAdd_mul]
        rfl
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        refine ⟨u⁻¹, X.inv_mem hu, ?_⟩
        rw [show (⟨u⁻¹, hXW (X.inv_mem hu)⟩ : ↥W) = (⟨u, hXW hu⟩ : ↥W)⁻¹ from rfl, map_inv,
          toAdd_inv]
        rfl }
  have hA : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∀ x ∈ A,
      (g : Matrix (Fin 3) (Fin 3) F).mulVec x ∈ A := by
    rintro g _ ⟨u, hu, rfl⟩
    obtain ⟨a, ha⟩ := SBd5.act_surj hαs g
    have hauX : (a : G) * u * (a : G)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hLX a.2) u).mp hu
    refine ⟨_, hauX, ?_⟩
    rw [hβe a ⟨u, hXW hu⟩ ⟨_, hXW hauX⟩ rfl 0, ha]
  rcases SBd6.irreducible_vec hF A hA with hAb | hAt
  · left
    rw [eq_bot_iff]
    intro u hu
    have h0 : Multiplicative.toAdd (β ⟨u, hXW hu⟩) 0 = 0 := by
      have : Multiplicative.toAdd (β ⟨u, hXW hu⟩) 0 ∈ A := ⟨u, hu, rfl⟩
      rw [hAb] at this
      simpa using this
    have hβ1 : β ⟨u, hXW hu⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      exact h0
    have : (⟨u, hXW hu⟩ : ↥W) = 1 := hβi (by rw [hβ1, map_one])
    have h1 : u = 1 := congrArg Subtype.val this
    rw [h1]
    exact Subgroup.one_mem _
  · right
    refine le_antisymm hXW ?_
    intro w hw
    have : Multiplicative.toAdd (β ⟨w, hw⟩) 0 ∈ A := by rw [hAt]; trivial
    obtain ⟨u, hu, h1⟩ := this
    have hβeq : β ⟨u, hXW hu⟩ = β ⟨w, hw⟩ := by
      apply Multiplicative.toAdd.injective
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      exact h1
    have h2 : (⟨u, hXW hu⟩ : ↥W) = ⟨w, hw⟩ := hβi hβeq
    have h3 : u = w := congrArg Subtype.val h2
    rw [← h3]
    exact hu

end Irr


section Comm

theorem commutator_mul_central {G : Type} [Group G] {r r' w w' : G} (hwr' : w * r' = r' * w)
    (hww' : w * w' = w' * w) (hw'r : w' * r = r * w') : ⁅r * w, r' * w'⁆ = ⁅r, r'⁆ := by
  have e2 : w * w' * w⁻¹ = w' := by
    calc w * w' * w⁻¹ = (w' * w) * w⁻¹ := by rw [hww']
      _ = w' := by group
  have e3 : w' * r⁻¹ = r⁻¹ * w' := by
    have h1 : r⁻¹ * (w' * r) * r⁻¹ = r⁻¹ * (r * w') * r⁻¹ := by rw [hw'r]
    have h2 : r⁻¹ * w' = w' * r⁻¹ := by simpa [mul_assoc] using h1
    exact h2.symm
  calc ⁅r * w, r' * w'⁆ = r * (w * r') * w' * w⁻¹ * r⁻¹ * w'⁻¹ * r'⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = r * (r' * w) * w' * w⁻¹ * r⁻¹ * w'⁻¹ * r'⁻¹ := by rw [hwr']
    _ = r * r' * (w * w' * w⁻¹) * r⁻¹ * w'⁻¹ * r'⁻¹ := by group
    _ = r * r' * w' * r⁻¹ * w'⁻¹ * r'⁻¹ := by rw [e2]
    _ = r * r' * (w' * r⁻¹) * w'⁻¹ * r'⁻¹ := by group
    _ = r * r' * (r⁻¹ * w') * w'⁻¹ * r'⁻¹ := by rw [e3]
    _ = ⁅r, r'⁆ := by
        rw [commutatorElement_def]
        group

end Comm

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem blockU_le_Yp_of_case3 (h113 : StageLemma14113) (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hout : Outcome31 T V₁ I L) (h3 : IsC134Case 3 I (Sgp153 T V₁) L) : blockU L ≤ Yp := by
  have hCW : centerOf (c134Q I L) ⊓ Subgroup.centralizer (Yp : Set G) = ⊥ :=
    centerOf_inf_centralizer_eq_bot h113 c hout (Or.inr (Or.inr h3))
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hQeq : blockU L = c134Q I L := blockU_eq_c134Q c
  have hLQ' : L ≤ Subgroup.normalizer (c134Q I L : Set G) := by
    rw [← hQeq]
    exact Subgroup.normalizer_commutator_ge_right (pCoreOf 2 L) L
  change IsC134Case3 I (Sgp153 T V₁) L at h3
  obtain ⟨⟨n, F, hFfield, hFin, α, hcard, hmod, hsum1, hsum2⟩, -⟩ := h3
  have hF2 : Fintype.card F = 2 := SBc7.card_field_eq_two c hout hcard hmod
  obtain ⟨hLW, -, β₁, hβ₁s, hβ₁k, hβ₁e⟩ := hsum1
  obtain ⟨-, -, β₂, hβ₂s, hβ₂k, hβ₂e⟩ := hsum2
  have hβ₁i : Function.Injective β₁ :=
    (MonoidHom.ker_eq_bot_iff β₁).1 (by rw [hβ₁k, Subgroup.bot_subgroupOf])
  have hβ₂e' : ∀ (a : ↥L) (u v : ↥(c134Q I L)), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β₂ v) i =
        ((((α a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))⁻¹).transpose.mulVec
          (Multiplicative.toAdd (β₂ u) i) := fun a u v h i => by
    simpa [moduleAct, Matrix.coe_units_inv] using hβ₂e a u v h i
  have hβ₁e' : ∀ (a : ↥L) (u v : ↥(centerOf (c134Q I L))), (v : G) = a * u * a⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β₁ v) i =
        ((α a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (β₁ u) i) := fun a u v h i => by
    simpa [moduleAct] using hβ₁e a u v h i
  have hQS : c134Q I L ≤ Sgp153 T V₁ := hQeq ▸ SBc7.blockU_le_Sgp c.toCtx15330
  have hQY : c134Q I L ≤ Subgroup.normalizer (Yp : Set G) :=
    hQS.trans (SBc7.Sgp_le_normalizer_Yp c.toCtx15330)
  have hR₀Q : ⁅c134Q I L, Yp⁆ ≤ c134Q I L :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hYL.trans hLQ')
  have hR₀Y : ⁅c134Q I L, Yp⁆ ≤ Yp := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hQY
  suffices hQR : c134Q I L ≤ ⁅c134Q I L, Yp⁆ by
    rw [hQeq]
    exact hQR.trans hR₀Y
  set R₀ : Subgroup G := ⁅c134Q I L, Yp⁆ with hR₀def
  let 𝒢 : Set (Matrix (Fin 3) (Fin 3) F) :=
    {A | ∃ y : ↥L, (y : G) ∈ Yp ∧
      A = ((α y : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)}
  have hdet : ∀ A ∈ 𝒢, IsUnit A := by
    rintro _ ⟨y, -, rfl⟩
    exact Units.isUnit _
  have hfixG : ∀ u : Fin 3 → F, (∀ A ∈ 𝒢, A.mulVec u = u) → u = 0 := by
    intro u hu
    obtain ⟨w, hw⟩ := hβ₁s (Multiplicative.ofAdd (fun _ : Fin 1 => u))
    have hwu : Multiplicative.toAdd (β₁ w) 0 = u := by
      rw [hw]
      rfl
    have hwC : (w : G) ∈ Subgroup.centralizer (Yp : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyL : y ∈ L := hYL hy
      have hyw : (y : G) * w * y⁻¹ ∈ centerOf (c134Q I L) := S153D.conj_mem_centerOf (hLQ' hyL) w.2
      have h1 := hβ₁e' ⟨y, hyL⟩ w ⟨y * w * y⁻¹, hyw⟩ rfl 0
      rw [hwu, hu _ ⟨⟨y, hyL⟩, hy, rfl⟩] at h1
      have h2 : β₁ ⟨y * w * y⁻¹, hyw⟩ = β₁ w := by
        apply Multiplicative.toAdd.injective
        funext j
        have hj : j = 0 := Subsingleton.elim _ _
        subst hj
        rw [h1, hwu]
      have h3 := hβ₁i h2
      have h4 : y * (w : G) * y⁻¹ = (w : G) := congrArg Subtype.val h3
      calc y * (w : G) = (y * w * y⁻¹) * y := by group
        _ = (w : G) * y := by rw [h4]
    have : (w : G) ∈ (centerOf (c134Q I L)) ⊓ Subgroup.centralizer (Yp : Set G) := ⟨w.2, hwC⟩
    rw [hCW, Subgroup.mem_bot] at this
    have hw1 : w = 1 := Subtype.ext this
    rw [← hwu, hw1, map_one]
    rfl
  have hDual := closure_dual_commutators_eq_top hF2 𝒢 hdet hfixG
  let 𝒩 : AddSubgroup (Fin 2 → Fin 3 → F) :=
    { carrier := {x | ∃ r : G, ∃ hr : r ∈ (c134Q I L), r ∈ R₀ ∧ Multiplicative.toAdd (β₂ ⟨r, hr⟩) = x}
      zero_mem' := ⟨1, (c134Q I L).one_mem, R₀.one_mem, by
        rw [show (⟨1, (c134Q I L).one_mem⟩ : ↥(c134Q I L)) = 1 from rfl, map_one]
        rfl⟩
      add_mem' := by
        rintro _ _ ⟨r, hr, hrR, rfl⟩ ⟨r', hr', hr'R, rfl⟩
        refine ⟨r * r', (c134Q I L).mul_mem hr hr', R₀.mul_mem hrR hr'R, ?_⟩
        rw [show (⟨r * r', (c134Q I L).mul_mem hr hr'⟩ : ↥(c134Q I L)) = ⟨r, hr⟩ * ⟨r', hr'⟩ from rfl, map_mul,
          toAdd_mul]
      neg_mem' := by
        rintro _ ⟨r, hr, hrR, rfl⟩
        refine ⟨r⁻¹, (c134Q I L).inv_mem hr, R₀.inv_mem hrR, ?_⟩
        rw [show (⟨r⁻¹, (c134Q I L).inv_mem hr⟩ : ↥(c134Q I L)) = (⟨r, hr⟩ : ↥(c134Q I L))⁻¹ from rfl, map_inv, toAdd_inv] }
  have hsingle : ∀ (i : Fin 2) (x₀ : Fin 3 → F),
      x₀ ∈ AddSubgroup.closure {x : Fin 3 → F | ∃ A ∈ 𝒢, ∃ u : Fin 3 → F,
        x = (A⁻¹).transpose.mulVec u - u} → (Pi.single i x₀ : Fin 2 → Fin 3 → F) ∈ 𝒩 := by
    intro i x₀ hx₀
    refine (AddSubgroup.closure_le (𝒩.comap (AddMonoidHom.single (fun _ : Fin 2 => Fin 3 → F) i))
      |>.mpr ?_) hx₀
    rintro _ ⟨_, ⟨y, hy, rfl⟩, u, rfl⟩
    show (Pi.single i (((((α y : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F))⁻¹).transpose.mulVec u - u) : Fin 2 → Fin 3 → F) ∈ 𝒩
    obtain ⟨q, hq⟩ := hβ₂s (Multiplicative.ofAdd (Pi.single i u))
    have hyL : (y : G) ∈ L := y.2
    have hyq : (y : G) * q * (y : G)⁻¹ ∈ (c134Q I L) := (Subgroup.mem_normalizer_iff.mp (hLQ' hyL) q).mp q.2
    have hcomm : (q : G) * y * (q : G)⁻¹ * (y : G)⁻¹ ∈ R₀ :=
      Subgroup.commutator_mem_commutator q.2 hy
    have hcommQ : (q : G) * y * (q : G)⁻¹ * (y : G)⁻¹ ∈ (c134Q I L) := hR₀Q hcomm
    refine (𝒩.neg_mem_iff).1 ?_
    refine ⟨_, hcommQ, hcomm, ?_⟩
    have hdecomp : (⟨(q : G) * y * (q : G)⁻¹ * (y : G)⁻¹, hcommQ⟩ : ↥(c134Q I L)) =
        q * (⟨(y : G) * q * (y : G)⁻¹, hyq⟩ : ↥(c134Q I L))⁻¹ := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [hdecomp, map_mul, map_inv, toAdd_mul, toAdd_inv]
    funext i'
    have h1 := hβ₂e' y q ⟨(y : G) * q * (y : G)⁻¹, hyq⟩ rfl i'
    have hq' : Multiplicative.toAdd (β₂ q) = Pi.single i u := by
      rw [hq]
      rfl
    simp only [Pi.add_apply, Pi.neg_apply, h1, hq']
    by_cases hi : i' = i
    · subst hi
      simp [Pi.single_eq_same, sub_eq_add_neg]
    · simp [Pi.single_eq_of_ne hi]
  have h𝒩 : 𝒩 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ i, (Pi.single i (x i) : Fin 2 → Fin 3 → F) := by
      rw [Finset.univ_sum_single]
    rw [hx]
    exact AddSubgroup.sum_mem _ fun i _ => hsingle i (x i) (by rw [hDual]; trivial)
  have hcover : ∀ q ∈ (c134Q I L), ∃ r ∈ R₀, r⁻¹ * q ∈ (centerOf (c134Q I L)) := by
    intro q hq
    have hmem : Multiplicative.toAdd (β₂ ⟨q, hq⟩) ∈ 𝒩 := by rw [h𝒩]; trivial
    obtain ⟨r, hr, hrR, hrq⟩ := hmem
    refine ⟨r, hrR, ?_⟩
    have h1 : β₂ ⟨r, hr⟩ = β₂ ⟨q, hq⟩ := Multiplicative.toAdd.injective hrq
    have h2 : (⟨r, hr⟩ : ↥(c134Q I L))⁻¹ * ⟨q, hq⟩ ∈ β₂.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    rw [hβ₂k] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have hWQ : centerOf (c134Q I L) ≤ c134Q I L := inf_le_left
  have hcentral : ∀ w ∈ centerOf (c134Q I L), ∀ z ∈ c134Q I L, z * w = w * z := fun w hw z hz =>
    Subgroup.mem_centralizer_iff.mp hw.2 z hz
  have hXW : ⁅c134Q I L, c134Q I L⁆ ≤ centerOf (c134Q I L) := by
    rw [Subgroup.commutator_le]
    intro q hq q' hq'
    have hcQ : ⁅q, q'⁆ ∈ c134Q I L := by
      rw [commutatorElement_def]
      exact (c134Q I L).mul_mem ((c134Q I L).mul_mem ((c134Q I L).mul_mem hq hq')
        ((c134Q I L).inv_mem hq)) ((c134Q I L).inv_mem hq')
    have hker : (⟨⁅q, q'⁆, hcQ⟩ : ↥(c134Q I L)) ∈ β₂.ker := by
      rw [MonoidHom.mem_ker]
      have : (⟨⁅q, q'⁆, hcQ⟩ : ↥(c134Q I L)) = ⁅(⟨q, hq⟩ : ↥(c134Q I L)), ⟨q', hq'⟩⁆ := rfl
      rw [this, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    rw [hβ₂k] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  have hXne : ⁅c134Q I L, c134Q I L⁆ ≠ ⊥ := by
    intro hbot
    have hcomm : ∀ q ∈ c134Q I L, ∀ q' ∈ c134Q I L, q * q' = q' * q := by
      intro q hq q' hq'
      have h1 : ⁅q, q'⁆ ∈ ⁅c134Q I L, c134Q I L⁆ := Subgroup.commutator_mem_commutator hq hq'
      rw [hbot, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    have hQW : c134Q I L ≤ centerOf (c134Q I L) := fun q hq => ⟨hq,
      Subgroup.mem_centralizer_iff.mpr fun z hz => hcomm z hz q hq⟩
    have hker_top : β₂.ker = ⊤ := by
      rw [hβ₂k, eq_top_iff]
      intro x _
      exact Subgroup.mem_subgroupOf.mpr (hQW x.2)
    obtain ⟨q, hq⟩ := hβ₂s (Multiplicative.ofAdd (Pi.single 0 (Pi.single 0 1) : Fin 2 → Fin 3 → F))
    have hq1 : β₂ q = 1 := by
      have : q ∈ β₂.ker := by rw [hker_top]; trivial
      exact this
    rw [hq1] at hq
    have h2 := congrArg Multiplicative.toAdd hq
    have h3 := congrFun (congrFun h2 0) 0
    simp at h3
  have hLX : L ≤ Subgroup.normalizer ((⁅c134Q I L, c134Q I L⁆ : Subgroup G) : Set G) :=
    fun g hg => SBd5.mem_normalizer_commutator_of (hLQ' hg) (hLQ' hg)
  have hXeq : ⁅c134Q I L, c134Q I L⁆ = centerOf (c134Q I L) :=
    (irreducible_of_natural hF2 α hmod.1 β₁ hβ₁i hβ₁e' _ hXW hLX).resolve_left hXne
  have hXR : ⁅c134Q I L, c134Q I L⁆ ≤ R₀ := by
    rw [Subgroup.commutator_le]
    intro q hq q' hq'
    obtain ⟨r, hrR, hw⟩ := hcover q hq
    obtain ⟨r', hr'R, hw'⟩ := hcover q' hq'
    have hrQ := hR₀Q hrR
    have hr'Q := hR₀Q hr'R
    have hwr' : (r⁻¹ * q) * r' = r' * (r⁻¹ * q) := (hcentral _ hw r' hr'Q).symm
    have hww' : (r⁻¹ * q) * (r'⁻¹ * q') = (r'⁻¹ * q') * (r⁻¹ * q) :=
      (hcentral _ hw _ (hWQ hw')).symm
    have hw'r : (r'⁻¹ * q') * r = r * (r'⁻¹ * q') := (hcentral _ hw' r hrQ).symm
    have e1 : q = r * (r⁻¹ * q) := by group
    have e2 : q' = r' * (r'⁻¹ * q') := by group
    have key : ⁅q, q'⁆ = ⁅r, r'⁆ := by
      have := commutator_mul_central hwr' hww' hw'r
      rw [← e1, ← e2] at this
      exact this
    rw [key, commutatorElement_def]
    exact R₀.mul_mem (R₀.mul_mem (R₀.mul_mem hrR hr'R) (R₀.inv_mem hrR)) (R₀.inv_mem hr'R)
  have hWR : centerOf (c134Q I L) ≤ R₀ := hXeq ▸ hXR
  intro q hq
  obtain ⟨r, hrR, hw⟩ := hcover q hq
  have e : q = r * (r⁻¹ * q) := by group
  rw [e]
  exact R₀.mul_mem hrR (hWR hw)

end Main

end SBc8

end CFSG.Quasithin
