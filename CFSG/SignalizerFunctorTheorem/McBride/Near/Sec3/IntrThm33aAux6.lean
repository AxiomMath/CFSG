module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux5
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma213
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux3

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33a

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A X Y X₁ X₂ : Subgroup Γ}

omit [Finite Γ] in
theorem mem_Y_of_commute (hP : (X₁, X₂) ∈ iPairsY A X Y) {W : Subgroup Γ} (hWX₁ : W ≤ X₁)
    (hWX : W ⊔ X₂ = X₁) {x : Γ} (hx : x ∈ cenIn X (A : Set Γ))
    (hc : ∀ w ∈ W, w * x = x * w) : x ∈ Y := by
  have hxH₀ : x ∈ X₁ ⊔ cenIn X (A : Set Γ) := Subgroup.mem_sup_right hx
  have hxH : x ∈ X₁ ⊔ cenIn X (A : Set Γ) ⊔ A := Subgroup.mem_sup_left hxH₀
  have hxN₂ : x ∈ Subgroup.normalizer (X₂ : Set Γ) := pair_admits_H₂ hP hxH
  have hWN : W ≤ Subgroup.normalizer (X₂ : Set Γ) := (hWX₁.trans le_H).trans (pair_admits_H₂ hP)
  have hmem : x ∈ secCenIn (X₁ ⊔ cenIn X (A : Set Γ)) X₁ X₂ := by
    refine Subgroup.mem_inf.mpr ⟨hxH₀, ?_⟩
    rw [mem_sectionCentralizer_iff]
    refine ⟨hxN₂, pair_admits_H hP hxH, fun y hy => ?_⟩
    have hy' : y ∈ (↑(W ⊔ X₂) : Set Γ) := by
      rw [hWX]
      exact hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right W X₂ hWN] at hy'
    obtain ⟨w, hw, x₂, hx₂, rfl⟩ := hy'
    have hxw : x * w = w * x := (hc w hw).symm
    have h1 : x * x₂ * x⁻¹ * x₂⁻¹ ∈ X₂ :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hxN₂ x₂).mp hx₂) (inv_mem hx₂)
    have h2 : w * (x * x₂ * x⁻¹ * x₂⁻¹) * w⁻¹ ∈ X₂ :=
      (Subgroup.mem_normalizer_iff.mp (hWN hw) _).mp h1
    have e : ⁅x, w * x₂⁆ = w * (x * x₂ * x⁻¹ * x₂⁻¹) * w⁻¹ := by
      rw [commutatorElement_def]
      calc x * (w * x₂) * x⁻¹ * (w * x₂)⁻¹ = (x * w) * x₂ * x⁻¹ * x₂⁻¹ * w⁻¹ := by group
        _ = (w * x) * x₂ * x⁻¹ * x₂⁻¹ * w⁻¹ := by rw [hxw]
        _ = w * (x * x₂ * x⁻¹ * x₂⁻¹) * w⁻¹ := by group
    rw [e]
    exact h2
  rw [pair_secCenIn hP] at hmem
  rw [← pair_inf hP]
  exact Subgroup.mem_inf.mpr ⟨hmem, hx⟩

theorem final_argument
    (h : NearAsolvAction p A X) (hsol : sol X = ⊥) (hXne : X ≠ ⊥)
    (hP : (X₁, X₂) ∈ iPairsY A X Y) (hθ : iThetaU A X Y = X) {W : Subgroup Γ}
    (hWB : W ≤ kOf X ⊓ X₁) (hWperf : Group.IsPerfect ↥W)
    (hWadm : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) W) (hWX : W ⊔ X₂ = X₁) (hWinf : W ⊓ X₂ = ⊥)
    (key : ∀ N : Subgroup Γ, N ≤ X → Admits X N → Admits A N → N ⊓ X₁ ≤ X₂ → N = ⊥) :
    Y = ⊥ := by
  have hKX : kOf X ≤ X := kOf_le X
  have hWK : W ≤ kOf X := hWB.trans inf_le_left
  have hWX₁ : W ≤ X₁ := hWB.trans inf_le_right
  have hXK : Admits X (kOf X) :=
    Subgroup.le_normalizer.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hAK : Admits A (kOf X) := h.admits.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hDAH : cenIn X (A : Set Γ) ⊔ A ≤ X₁ ⊔ cenIn X (A : Set Γ) ⊔ A :=
    sup_le dsub_le_H le_sup_right
  have hWDA : Admits (cenIn X (A : Set Γ) ⊔ A) W := hDAH.trans hWadm
  have hWX₁adm : Admits X₁ W := le_H.trans hWadm
  have hX₂adm : Admits X₁ X₂ := le_H.trans (pair_admits_H₂ hP)
  have hcomm : ∀ w ∈ W, ∀ x ∈ X₂, w * x = x * w := fun w hw x hx =>
    (commute_of_inf_eq_bot hWX₁adm hX₂adm hWX₁ (pair_le₂ hP) hWinf hw hx).eq
  have hZ : ∀ Z ∈ iUset A X Y, Admits Z (k1 X W) := by
    intro Z hZ
    have hYZ : Y ≤ Z := (pair_Y_le hP).trans hZ.2.1
    refine lemma213d h hsol hXne hWK hWDA hWperf (Z₀ := orbitClosure Y Z) hZ.1.1
      ⟨orbitClosure_le_of_admits hYZ Subgroup.le_normalizer,
        Nonsolv.SolQuot.le_normalizer_orbitClosure Y Z⟩
      (admits_orbitClosure (pair_admits_Y hP) hZ.1.2) hZ.1.2 ?_
    ext x
    simp only [cenIn, k1, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hxZ₀, hxK⟩, hxX, hxA⟩
      have hxY : x ∈ Y := by
        rw [← hZ.2.2]
        exact Subgroup.mem_inf.mpr ⟨hxZ₀, hxX, hxA⟩
      exact ⟨⟨hxK, Subgroup.mem_centralizer_iff.mpr fun w hw =>
        hcomm w hw x (pair_Y_le₂ hP hxY)⟩, hxA⟩
    · rintro ⟨⟨hxK, hxC⟩, hxA⟩
      have hxD : x ∈ cenIn X (A : Set Γ) := Subgroup.mem_inf.mpr ⟨hKX hxK, hxA⟩
      have hxY : x ∈ Y := mem_Y_of_commute hP hWX₁ hWX hxD
        (fun w hw => Subgroup.mem_centralizer_iff.mp hxC w hw)
      exact ⟨⟨le_orbitClosure Y Z hxY, hxK⟩, hKX hxK, hxA⟩
  have hXk1 : Admits X (k1 X W) := by
    have : iThetaU A X Y ≤ Subgroup.normalizer (k1 X W : Set Γ) := iThetaU_le_of hZ
    rwa [hθ] at this
  have hWA : Admits A W := le_sup_right.trans hWadm
  have hAk1 : Admits A (k1 X W) :=
    Admits.inf hAK (hWA.trans (Thm211.normalizer_le_normalizer_centralizer W))
  have hk1X : k1 X W ≤ X := inf_le_left.trans hKX
  have hk1X₁ : k1 X W ⊓ X₁ ≤ X₂ := by
    have hH_k1 : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) (k1 X W) :=
      sup_le (sup_le ((pair_le hP).trans hXk1) (inf_le_left.trans hXk1)) hAk1
    rcases chief_dichotomy (pair_chief hP) (hH_k1.inf (pair_admits_H hP)) inf_le_right with
      hle | heq
    · exact hle
    · refine (false_of_commute hP inf_le_right hWX₁ heq hWX ?_).elim
      intro m hm w hw
      exact (Subgroup.mem_centralizer_iff.mp hm.1.2 w hw).symm
  have hk1bot : k1 X W = ⊥ := key (k1 X W) hk1X hXk1 hAk1 hk1X₁
  have hcen := lemma213c h hsol hXne hWK hWDA hWperf hk1bot
  refine eq_bot_iff.mpr fun y hy => ?_
  have hyD : y ∈ cenIn X (A : Set Γ) := pair_Y_le hP hy
  have hy1 : y ∈ cenIn X (W : Set Γ) :=
    Subgroup.mem_inf.mpr ⟨hyD.1, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      hcomm w hw y (pair_Y_le₂ hP hy)⟩
  rw [hcen] at hy1
  exact hy1

omit [Finite Γ] in
theorem orbitClosure_bot (Z : Subgroup Γ) : orbitClosure ⊥ Z = ⊥ :=
  le_bot_iff.mp (orbitClosure_le fun a _ => by rw [Subgroup.map_bot])

theorem main_case
    (ih : Thm33aBelow.{u} p (Nat.card ↥X)) (h : NearAsolvAction p A X)
    (hY : (iPairsY A X Y).Nonempty) (hθ : iThetaU A X Y = X) :
    orbitClosure Y X ⊓ cenIn X (A : Set Γ) = Y := by
  obtain ⟨⟨X₁', X₂'⟩, hP'⟩ := hY
  obtain ⟨X₁, X₂, -, -, hP, hX₂sol, -⟩ := iThm32 h hP'
  by_contra hfail
  have key : ∀ N : Subgroup Γ, N ≤ X → Admits X N → Admits A N → N ⊓ X₁ ≤ X₂ → N = ⊥ := by
    intro N hNX hXN hAN hN
    by_contra hN1
    exact hfail (quotient_step ih rfl h hP hθ hNX hXN hAN hN hN1)
  have hXne : X ≠ ⊥ := by
    intro hX0
    have h1 : X₁ = ⊥ := le_bot_iff.mp (hX0 ▸ pair_le hP)
    have h2 : X₂ = ⊥ := le_bot_iff.mp (h1 ▸ pair_le₂ hP)
    exact (pair_lt hP).ne (h2.trans h1.symm)
  have hsol : sol X = ⊥ := by
    have hHsol : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) (sol X) :=
      sup_le (sup_le ((pair_le hP).trans (Nonsolv.SolQuot.le_nrm_sol X))
        (inf_le_left.trans (Nonsolv.SolQuot.le_nrm_sol X)))
        (h.admits.trans (Nonsolv.SolQuot.normalizer_le_nrm_sol X))
    refine key (sol X) (sol_le X) (Nonsolv.SolQuot.le_nrm_sol X)
      (h.admits.trans (Nonsolv.SolQuot.normalizer_le_nrm_sol X)) ?_
    exact le_of_solvable hP inf_le_right (Admits.inf hHsol (pair_admits_H hP))
      (Thm211.isSolvable_of_le inf_le_left (isSolvable_sol X))
  have hXK : Admits X (kOf X) :=
    Subgroup.le_normalizer.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hAK : Admits A (kOf X) := h.admits.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hKX₁ : ¬ (kOf X ⊓ X₁ ≤ X₂) := fun hle =>
    Thm211.kOf_ne_bot hsol hXne (key (kOf X) (kOf_le X) hXK hAK hle)
  obtain ⟨W, hWB, hWperf, hWadm, hWX, hWinf⟩ := exists_perfect_sup h hsol hXne hP hX₂sol hKX₁
  have hY0 : Y = ⊥ := final_argument h hsol hXne hP hθ hWB hWperf hWadm hWX hWinf key
  apply hfail
  rw [hY0, orbitClosure_bot, bot_inf_eq]

theorem main_step
    (ih : Thm33aBelow.{u} p (Nat.card ↥X)) (h : NearAsolvAction p A X)
    (hY : (iPairsY A X Y).Nonempty) : iThetaU A X Y ∈ iUset A X Y := by
  obtain ⟨⟨X₁, X₂⟩, hP⟩ := hY
  by_cases hθ : iThetaU A X Y = X
  · refine iThetaU_mem_iUset_of hP ?_
    rw [hθ]
    exact main_case ih h ⟨_, hP⟩ hθ
  · have hle : iThetaU A X Y ≤ X := iThetaU_le
    have hlt : iThetaU A X Y < X := lt_of_le_of_ne hle hθ
    have hDX' : cenIn X (A : Set Γ) ≤ iThetaU A X Y := dsub_le_iThetaU hP
    have hcard : Nat.card ↥(iThetaU A X Y) < Nat.card ↥X := Thm211.card_lt_of_ne hle hθ
    have hnear : NearAsolvAction p A (iThetaU A X Y) :=
      Thm211.nearAsolvAction_of_le h hle (le_sup_right.trans admits_iThetaU)
    have hP' : (X₁, X₂) ∈ iPairsY A (iThetaU A X Y) Y := by
      rw [iPairsY_of_le hDX' hle]
      exact ⟨hP, pair_le_iThetaU hP⟩
    have hmem := ih Γ A (iThetaU A X Y) Y hcard hnear ⟨_, hP'⟩
    rwa [iThetaU_eq_of_iThetaU_le hDX' hle le_rfl,
      iUset_eq_of_iThetaU_le hDX' hle le_rfl] at hmem

theorem thm33a_below
    (p : ℕ) (n : ℕ) : Thm33aBelow.{u} p n := by
  induction n with
  | zero =>
    intro Γ _ _ A X Y hn
    exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro Γ _ _ A X Y hn h hY
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
    · exact ih Γ A X Y hlt h hY
    · exact main_step (heq ▸ ih) h hY

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33a
