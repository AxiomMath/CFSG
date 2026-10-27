module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33bAux4
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33bAux1

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33b

open Thm33a

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A X Y : Subgroup Γ}

theorem exists_iEset_greatest
    (h : NearAsolvAction p A X) (hsol : sol X = ⊥) (hXne : X ≠ ⊥) :
    ∃ R : Subgroup Γ, R ≤ kOf X ∧ R ∈ iEset A X ⊥ ∧ ∀ Z ∈ iEset A X ⊥, Z ≤ R := by
  have hss := semisimpleAction_kOf h hsol hXne
  obtain ⟨⟨hRK, hRadm, hRD⟩, hmax⟩ := thm210k hss
  set F := CFSG.fittingSubgroupOf (mOf A (kOf X)) with hF
  refine ⟨⁅F, A⁆, hRK, ⟨⟨hRK.trans (kOf_le X), ?_⟩, ?_⟩, fun Z hZ => ?_⟩
  · refine sup_le ?_ (le_sup_right.trans hRadm)
    have hQK : cenIn X (A : Set Γ) ≤ Subgroup.normalizer (kOf X : Set Γ) := fun d hd =>
      Thm211.normalizer_le_normalizer_kOf X (Subgroup.le_normalizer (Subgroup.mem_inf.mp hd).1)
    have hQA : cenIn X (A : Set Γ) ≤ Subgroup.normalizer (A : Set Γ) := fun d hd =>
      Subgroup.centralizer_le_normalizer (A : Set Γ) (Subgroup.mem_inf.mp hd).2
    intro d hd
    have hdM : d ∈ Subgroup.normalizer (mOf A (kOf X) : Set Γ) :=
      Thm211.le_normalizer_mOf hQK hQA hd
    have hdF : d ∈ Subgroup.normalizer (F : Set Γ) :=
      Thm211.normalizer_le_normalizer_fitting _ hdM
    have hdA : d ∈ Subgroup.normalizer (A : Set Γ) := hQA hd
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp hdF,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hdA]
  · refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hxK : x ∈ cenIn (kOf X) (A : Set Γ) :=
      Subgroup.mem_inf.mpr ⟨hRK hx1, (Subgroup.mem_inf.mp hx2).2⟩
    have : x ∈ ⁅F, A⁆ ⊓ cenIn (kOf X) (A : Set Γ) := Subgroup.mem_inf.mpr ⟨hx1, hxK⟩
    rwa [hRD] at this
  · obtain ⟨hZK, -⟩ := le_kOf_of_inf_dsub_eq_bot h hsol hXne hZ.1.1 hZ.1.2 hZ.2
    refine hmax ⟨hZK, (sup_le_sup_right (inf_le_inf_right _ (kOf_le X)) A).trans hZ.1.2, ?_⟩
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have : x ∈ Z ⊓ cenIn X (A : Set Γ) := Subgroup.mem_inf.mpr ⟨hx1,
      Subgroup.mem_inf.mpr ⟨kOf_le X (Subgroup.mem_inf.mp hx2).1, (Subgroup.mem_inf.mp hx2).2⟩⟩
    rwa [hZ.2] at this

theorem concl_of_key
    (h : NearAsolvAction p A X) (hY : (iPairsY A X Y).Nonempty)
    (hXe : X = kOf X ⊔ iThetaU A X Y)
    (key : ∀ N : Subgroup Γ, N ≤ X → Admits X N → Admits A N →
      N ⊓ cenIn X (A : Set Γ) ≤ Y → N = ⊥) : Concl A X Y := by
  obtain ⟨⟨X₁, X₂⟩, hP⟩ := hY
  have hXne : X ≠ ⊥ := by
    intro hX0
    have h1 : X₁ = ⊥ := le_bot_iff.mp (hX0 ▸ pair_le hP)
    have h2 : X₂ = ⊥ := le_bot_iff.mp (h1 ▸ pair_le₂ hP)
    exact (pair_lt hP).ne (h2.trans h1.symm)
  have hsol : sol X = ⊥ := sol_eq_bot_of_key h hP key
  obtain ⟨Z₁, Z₂, -, -, hZP, hZsol, -⟩ := iThm32 h hP
  obtain ⟨W₀, -, -, -, -, -, -, -, hY0⟩ := pair_rigid h hsol hXne hXe key hZP hZsol
  subst hY0
  have hXK : Admits X (kOf X) :=
    Subgroup.le_normalizer.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hAK : Admits A (kOf X) := h.admits.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hall : ∀ P ∈ iPairsY A X ⊥, P.2 = ⊥ ∧ P.1 ≤ kOf X ∧ Group.IsPerfect ↥P.1 ∧
      cenIn X (P.1 : Set Γ) = ⊥ := fun P hP' =>
    pair_eq_of_Y_bot h hsol hXne hXe key (X₁ := P.1) (X₂ := P.2) hP'
  obtain ⟨hX₂, hX₁K, hX₁perf, hX₁cen⟩ := hall (X₁, X₂) hP
  have hP' : (X₁, (⊥ : Subgroup Γ)) ∈ iPairsY A X ⊥ := by
    obtain rfl : X₂ = ⊥ := hX₂
    exact hP
  have hKH : kOf X ⊔ cenIn X (A : Set Γ) ⊔ A ≤ Subgroup.normalizer (kOf X : Set Γ) :=
    sup_le (sup_le Subgroup.le_normalizer (inf_le_left.trans hXK)) hAK
  have hKpair : (kOf X, (⊥ : Subgroup Γ)) ∈ iPairsY A X ⊥ := by
    refine ⟨⟨⟨kOf_le X, sup_le (inf_le_left.trans hXK) hAK⟩, ⟨bot_le, admits_bot _⟩, ?_, ?_⟩,
      bot_inf_eq _⟩
    · refine ⟨⟨bot_le, admits_bot _⟩, ⟨le_sup_left.trans le_sup_left, hKH⟩,
        bot_lt_iff_ne_bot.mpr (Thm211.kOf_ne_bot hsol hXne), ?_⟩
      intro V hV _ hVK
      exact eq_bot_or_eq_kOf h hsol hXne hP' hX₁K hX₁perf hX₁cen hVK hV.2
    · refine eq_bot_iff.mpr fun g hg => ?_
      obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨-, -, hgc⟩ := mem_sectionCentralizer_iff.mp hg2
      have hgX : g ∈ X := (sup_le (kOf_le X) inf_le_left) hg1
      have hgmem : g ∈ cenIn X (X₁ : Set Γ) := Subgroup.mem_inf.mpr ⟨hgX,
        Subgroup.mem_centralizer_iff.mpr fun y hy => by
          have h1 := hgc y (hX₁K hy)
          rw [Subgroup.mem_bot] at h1
          exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm⟩
      rwa [hX₁cen] at hgmem
  have hθM : iThetaM A X ⊥ = kOf X :=
    le_antisymm (iSup₂_le fun P hP'' => (hall P hP'').2.1)
      (le_iSup₂ (f := fun (Q : Subgroup Γ × Subgroup Γ) (_ : Q ∈ iPairsY A X ⊥) => Q.1)
        (kOf X, ⊥) hKpair)
  have hθL : iThetaL A X ⊥ = ⊥ := le_bot_iff.mp (iSup₂_le fun P hP'' => (hall P hP'').1.le)
  obtain ⟨R, hRK, hRE, hRmax⟩ := exists_iEset_greatest h hsol hXne
  have hθY : iThetaY A X ⊥ = R :=
    le_antisymm (iSup₂_le fun Z hZ => hRmax Z hZ)
      (le_iSup₂ (f := fun Z (_ : Z ∈ iEset A X ⊥) => Z) R hRE)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hθM, hθL]
    exact hKpair
  · rw [hθM]
  · rw [hθY]
    exact hRE
  · rw [hθY, hθM]
    exact hRK

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33b
