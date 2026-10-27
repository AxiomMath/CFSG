module

public import CFSG.Quasithin.EmptyFaithful.S146zISw

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Q

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem clsU_commutator (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {u y : G} (hu : u ∈ conjClosure (VZ T M) H) (hyH : y ∈ H)
    (hcU : u * y * u⁻¹ * y⁻¹ ∈ conjClosure (VZ T M) H) :
    clsU h91 hcU = clsU h91 hu * rhoH h91 ⟨y, hyH⟩ (clsU h91 hu) := by
  have hyu : y * u⁻¹ * y⁻¹ ∈ conjClosure (VZ T M) H :=
    conj_mem_UH hyH ((conjClosure (VZ T M) H).inv_mem hu)
  have e1 : clsU h91 hcU = clsU h91 hu * clsU h91 hyu := by
    rw [clsU_mul]
    exact clsU_congr h91 _ _ (by group)
  rw [e1, ← rhoH_clsU h91 ⟨y, hyH⟩ ((conjClosure (VZ T M) H).inv_mem hu),
    ← clsU_inv h91 hu, map_inv]
  congr 1
  exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using IntMod.sq_eq_one _)

theorem IsDecP.rho_fix_W₂ (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (c : ↥H) (hc : (c : G) ∈ H₁) {w : UMod h91} (hw : w ∈ Wsub h91 (uHi T M H H₂)) :
    rhoH h91 c w = w := by
  obtain ⟨u, hu, hui, rfl⟩ :=
    exists_clsU_of_mem_Wsub h91 (uHi_le_conjClosure (h.le₂.trans h.le)) hw
  rw [rhoH_clsU_eq_iff]
  have h1 : ⁅u, (c : G)⁆ ∈ quasithinOmegaOneCenter T :=
    h.cent₂ (Subgroup.commutator_mem_commutator hui hc)
  have e : (c : G) * u * (c : G)⁻¹ * u⁻¹ = (⁅u, (c : G)⁆)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e]
  exact (quasithinOmegaOneCenter T).inv_mem h1

theorem clsU_mem_Wsub_iff {T V L V₁ Vp : Subgroup G} (h : HypF91 T V L V₁ Vp H) {X : Subgroup G}
    (hXU : X ≤ conjClosure Vp H) (hVX : V₁ ≤ X) {u : G} (hu : u ∈ conjClosure Vp H) :
    clsU h hu ∈ Wsub h X ↔ u ∈ X := by
  constructor
  · intro hw
    obtain ⟨x, hx, hxX, hxu⟩ := exists_clsU_of_mem_Wsub h hXU hw
    have h1 : x⁻¹ * u ∈ V₁ := (clsU_eq_iff h hx hu).mp hxu
    have e : u = x * (x⁻¹ * u) := by group
    rw [e]
    exact X.mul_mem hxX (hVX h1)
  · intro hx
    exact clsU_mem_Wsub h hu hx

theorem IsDecP.exists_pCore_noncomm (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ 3) (h : IsDecP T M H 3 H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4)
    (hQ : ¬ pCoreOf 2 H ≤ Subgroup.centralizer (uK T M H : Set G))
    {z' a b : G} (haU : a ∈ conjClosure (VZ T M) H) (hbU : b ∈ conjClosure (VZ T M) H)
    (ha : a ∈ uHi T M H H₁) (hb : b ∈ uHi T M H H₂) (hab : z' = a * b)
    (hζ₁ne : clsU h91 haU ≠ 1) :
    ∃ q ∈ pCoreOf 2 H, q * z' ≠ z' * q := by
  classical
  by_contra hall
  push Not at hall
  have hH : IsHTM T M H := hred.isHTM
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hi₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₂.trans h.le)
  have hz'U : z' ∈ conjClosure (VZ T M) H := hab ▸ (conjClosure (VZ T M) H).mul_mem haU hbU
  set X : Subgroup G := conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) with hX
  have hXU : X ≤ conjClosure (VZ T M) H := inf_le_left
  have hZX : quasithinOmegaOneCenter T ≤ X := by
    intro z hz
    refine ⟨le_conjClosure (VZ T M) H (h91.V₁_le_V hz), Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have h1 := (Subgroup.mem_centralizer_iff.mp (h91.H_le_centralizer (pCoreOf_le 2 H hq))) z hz
    exact h1.symm
  have hXinv : ∀ c : ↥H, conjSub (c : G) X = X := by
    intro c
    have h1 : conjSub (c : G) (conjClosure (VZ T M) H) = conjClosure (VZ T M) H :=
      conjSub_eq_of_mem_normalizer (hHU c.2)
    have h2 : conjSub (c : G) (pCoreOf 2 H) = pCoreOf 2 H :=
      conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H c.2)
    rw [hX, conjSub_inf, h1, ← conjSub_centralizer, h2]
  have hz'X : z' ∈ X := ⟨hz'U, Subgroup.mem_centralizer_iff.mpr fun q hq => hall q hq⟩
  have hζC : clsU h91 hz'U ∈ Wsub h91 X := clsU_mem_Wsub h91 hz'U hz'X
  have hζab : clsU h91 hz'U = clsU h91 haU * clsU h91 hbU := by
    rw [clsU_mul]
    exact clsU_congr h91 _ _ hab
  have hζ₁W : clsU h91 haU ∈ Wsub h91 (uHi T M H H₁) := clsU_mem_Wsub h91 haU ha
  have hζ₂W : clsU h91 hbU ∈ Wsub h91 (uHi T M H H₂) := clsU_mem_Wsub h91 hbU hb
  obtain ⟨w', hw'W, hw'1, hw'ζ⟩ : ∃ w' ∈ Wsub h91 (uHi T M H H₁), w' ≠ 1 ∧ w' ≠ clsU h91 haU := by
    by_contra hno
    push Not at hno
    have hinj : Function.Injective (fun w : Wsub h91 (uHi T M H H₁) => decide ((w : UMod h91) = 1)) := by
      intro w₁ w₂ hww
      have h' : decide ((w₁ : UMod h91) = 1) = decide ((w₂ : UMod h91) = 1) := hww
      by_cases h1 : (w₁ : UMod h91) = 1
      · have h2 : (w₂ : UMod h91) = 1 := by
          by_contra h2
          simp [h1, h2] at h'
        exact Subtype.ext (h1.trans h2.symm)
      · have h2 : ¬ (w₂ : UMod h91) = 1 := by
          intro h2
          simp [h1, h2] at h'
        exact Subtype.ext ((hno _ w₁.2 h1).trans (hno _ w₂.2 h2).symm)
    have := Nat.card_le_card_of_injective _ hinj
    simp at this
    omega
  obtain ⟨c, hcH₁, hcζ⟩ := h.exists_rot_of_card_four S hred h91 hcard hζ₁W hζ₁ne hw'W hw'1
  have hcinv : conjSub (c : G) (uHi T M H H₁) = uHi T M H H₁ :=
    conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₁ S hred (h.le₁ hcH₁))
  have hη : rhoH h91 c (clsU h91 hz'U) * (clsU h91 hz'U)⁻¹ = w' * (clsU h91 haU)⁻¹ := by
    rw [hζab, map_mul, hcζ, h.rho_fix_W₂ h91 c hcH₁ hζ₂W]
    group
  have hηC : w' * (clsU h91 haU)⁻¹ ∈ Wsub h91 X := by
    rw [← hη]
    exact (Wsub h91 X).mul_mem (rhoH_mem_Wsub h91 c hXU (hXinv c) hζC) ((Wsub h91 X).inv_mem hζC)
  have hηW : w' * (clsU h91 haU)⁻¹ ∈ Wsub h91 (uHi T M H H₁) :=
    (Wsub h91 (uHi T M H H₁)).mul_mem hw'W ((Wsub h91 (uHi T M H H₁)).inv_mem hζ₁W)
  have hη1 : w' * (clsU h91 haU)⁻¹ ≠ 1 := fun e => hw'ζ (mul_inv_eq_one.mp e)
  have hW₁C : ∀ w ∈ Wsub h91 (uHi T M H H₁), w ∈ Wsub h91 X := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]
      exact (Wsub h91 X).one_mem
    · obtain ⟨c', hc'H₁, hc'η⟩ := h.exists_rot_of_card_four S hred h91 hcard hηW hη1 hw hw1
      rw [← hc'η]
      exact rhoH_mem_Wsub h91 c' hXU (hXinv c') hηC
  have htH : t ∈ H := hred.isHTM.1.1 h.t_mem
  have hW₂C : ∀ w ∈ Wsub h91 (uHi T M H H₂), w ∈ Wsub h91 X := by
    intro w hw
    have hsw : conjSub t (uHi T M H H₁) = uHi T M H H₂ := h.conjSub_uHi hred
    have hsw' : conjSub t⁻¹ (uHi T M H H₂) = uHi T M H H₁ := by
      rw [← hsw, conjSub_conjSub_inv]
    have h1 : rhoH h91 ⟨t⁻¹, H.inv_mem htH⟩ w ∈ Wsub h91 (uHi T M H H₁) :=
      rhoH_mem_Wsub h91 ⟨t⁻¹, H.inv_mem htH⟩ hi₂ hsw' hw
    have h2 := rhoH_mem_Wsub h91 ⟨t, htH⟩ hXU (hXinv ⟨t, htH⟩) (hW₁C _ h1)
    have e : rhoH h91 ⟨t, htH⟩ (rhoH h91 ⟨t⁻¹, H.inv_mem htH⟩ w) = w := by
      rw [← MulAut.mul_apply, ← map_mul]
      have : (⟨t, htH⟩ : ↥H) * ⟨t⁻¹, H.inv_mem htH⟩ = 1 := Subtype.ext (mul_inv_cancel t)
      rw [this, map_one]
      rfl
    rwa [e] at h2
  apply hQ
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨a', ha', b', hb', rfl⟩ := h.exists_decomp S hred hu
  have ha'U := hi₁ ha'
  have hb'U := hi₂ hb'
  have hmem : clsU h91 ((conjClosure (VZ T M) H).mul_mem ha'U hb'U) ∈ Wsub h91 X := by
    rw [← clsU_mul h91 ha'U hb'U]
    exact (Wsub h91 X).mul_mem (hW₁C _ (clsU_mem_Wsub h91 ha'U ha'))
      (hW₂C _ (clsU_mem_Wsub h91 hb'U hb'))
  have hux : a' * b' ∈ X := (clsU_mem_Wsub_iff h91 hXU hZX _).mp hmem
  exact ((Subgroup.mem_centralizer_iff.mp hux.2) q hq).symm

end Q

end CFSG.Quasithin
