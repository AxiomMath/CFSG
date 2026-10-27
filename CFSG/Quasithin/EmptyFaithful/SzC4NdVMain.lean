module

public import CFSG.Quasithin.EmptyFaithful.SzC4NdPkg
public import CFSG.Quasithin.EmptyFaithful.A38c10Iso
public import CFSG.Quasithin.EmptyFaithful.A38c10Split

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open Matrix CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section VMain2

variable {V : Type} [CommGroup V]

@[expose] def MSDataAt (Λ B W Y₁ Y₂ : Subgroup (MulAut V)) (U : Subgroup V)
    (P : Subgroup (MulAut V)) (ψ : ↥P →* SLt 3) (q : V) : Prop :=
  B ≤ P ∧ P ≤ Λ ∧ P ≠ Λ ∧ (∀ w ∈ W, ∀ p ∈ P, w * p * w⁻¹ ∈ P) ∧
    (∀ X : Subgroup (MulAut V), B ≤ X → X ≤ Λ → X ≠ Λ → Y₁ ⊔ Y₂ ≤ X → ¬ P ≤ X) ∧
    (Y₁ ≤ P ∨ Y₂ ≤ P) ∧ Function.Surjective ψ ∧ (∀ x : ↥P, ψ x = 1 → (x : MulAut V) ∈ B) ∧
    q ∈ U ∧ q ≠ 1 ∧ (∀ a ∈ P, (a : MulAut V) q = q) ∧ q ∈ commV (oTwoUpper P)

@[expose] def MSData2 (Λ B W Y₁ Y₂ : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∃ (D : BorelIso 4 Λ B) (P₁ P₃ : Subgroup (MulAut V)),
    D.model P₁ = QI 4 {1} ∧ D.model P₃ = QI 4 {3} ∧
    (∃ (ψ : ↥P₁ →* SLt 3) (q : V), MSDataAt Λ B W Y₁ Y₂ U P₁ ψ q) ∧
    (∃ (ψ : ↥P₃ →* SLt 3) (q : V), MSDataAt Λ B W Y₁ Y₂ U P₃ ψ q)

theorem exists_psi_of_model [Finite V] {Λ B : Subgroup (MulAut V)} (D : BorelIso 4 Λ B)
    {P : Subgroup (MulAut V)} (hPL : P ≤ Λ) {k : ℕ} (hmodel : D.model P = QI 4 {k})
    {ψ₀ : ↥(QI 4 {k}) →* SLt 3} (hψs : Function.Surjective ψ₀)
    (hψk : ∀ x : ↥(QI 4 {k}), ψ₀ x = 1 → (x : SLt 4) ∈ Ut 4) :
    ∃ ψ : ↥P →* SLt 3, Function.Surjective ψ ∧ ∀ x : ↥P, ψ x = 1 → (x : MulAut V) ∈ B := by
  have hmem : ∀ x : ↥P, D.e ⟨(x : MulAut V), hPL x.2⟩ ∈ QI 4 {k} := fun x =>
    hmodel ▸ (D.mem_model ⟨(x : MulAut V), hPL x.2⟩).2 x.2
  let φ : ↥P →* ↥(QI 4 {k}) :=
    ((D.e.toMonoidHom).comp (Subgroup.inclusion hPL)).codRestrict (QI 4 {k}) hmem
  refine ⟨ψ₀.comp φ, ?_, ?_⟩
  · intro t
    obtain ⟨s, hs⟩ := hψs t
    have hsP : (s : SLt 4) ∈ D.model P := by rw [hmodel]; exact s.2
    obtain ⟨y, hy, hys⟩ := hsP
    refine ⟨⟨(y : MulAut V), Subgroup.mem_subgroupOf.1 hy⟩, ?_⟩
    have : φ ⟨(y : MulAut V), Subgroup.mem_subgroupOf.1 hy⟩ = s := Subtype.ext hys
    show ψ₀ (φ _) = t
    rw [this, hs]
  · intro x hx
    have h1 : ((φ x : ↥(QI 4 {k})) : SLt 4) ∈ Ut 4 := hψk (φ x) hx
    have h2 : D.e ⟨(x : MulAut V), hPL x.2⟩ ∈ D.model B := by
      rw [D.model_B]
      exact h1
    exact (D.mem_model _).1 h2

theorem exists_psi_of_cuts_one [Finite V] {Λ B : Subgroup (MulAut V)} (D : BorelIso 4 Λ B)
    (hBL : B ≤ Λ) {P : Subgroup (MulAut V)} (hBP : B ≤ P) (hPL : P ≤ Λ)
    (hPk : D.cutsOf P = {1}) :
    ∃ ψ : ↥P →* SLt 3, Function.Surjective ψ ∧ ∀ x : ↥P, ψ x = 1 → (x : MulAut V) ∈ B := by
  obtain ⟨ψ₀, hψs, hψk⟩ := exists_psi1
  exact exists_psi_of_model D hPL (model_eq_QI_of_cuts D hBL hBP hPk) hψs hψk

theorem vmain2 [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {Λ B W Y₁ Y₂ : Subgroup (MulAut V)}
    (hF : Frame4 Λ B W Y₁ Y₂) (hne : Λ ≠ ⊥) (hΛ : Nat.card ↥Λ = 20160)
    (hAlt : Alt15127 Λ (commV Λ))
    (hp2 : ¬ IsIntDirect (commV Λ) (fixV Λ) ⊤ → commV Λ ∈ IrrPlus Λ ⊤ ∧
      B51NaturalList2 Λ (commV Λ) (fixV Λ ⊓ commV Λ))
    (u : V) (hu : u ∈ commV Λ) (huB : ∀ b ∈ B, (b : MulAut V) u = u)
    (huY : ¬ ∀ y ∈ Y₁ ⊔ Y₂, (y : MulAut V) u = u) :
    IsIntDirect (commV Λ) (fixV Λ) ⊤ ∧
      (∀ u' ∈ commV Λ, (∀ b ∈ B, (b : MulAut V) u' = u') → (∀ y ∈ Y₁ ⊔ Y₂, (y : MulAut V) u' = u') →
        u' = 1) ∧
      ((∀ y ∈ Y₁, (y : MulAut V) u = u) ∨ (∀ y ∈ Y₂, (y : MulAut V) u = u) ∨
        MSData2 Λ B W Y₁ Y₂ (commV Λ)) := by
  have hBL : B ≤ Λ := hF.sylow.1
  have hBX : B ≤ Λ ⊓ fixSub u := fun b hb => ⟨hBL hb, huB b hb⟩
  rcases hAlt with ⟨Z, hZ, -, hext⟩ | h5 | ⟨n, hnd⟩ | ⟨n, hn, k, hk1, hk, hnat⟩
  ·
    exfalso
    obtain ⟨D, hcuts⟩ := orth_package hV2 hne hF.sylow (hZ.trans inf_le_left) hext
    obtain ⟨P₁, P₂, P₃, -, ⟨hBP₂, hP₂L, hP₂c⟩, -, -, -, hY₂P, -, -⟩ := core4_frame hF D
    have hsub : D.cutsOf (Λ ⊓ fixSub u) ⊆ D.cutsOf P₂ := by
      rw [hP₂c]
      exact hcuts u hu huB
    have hP₂X : P₂ ≤ Λ ⊓ fixSub u := (D.cutsOf_le_iff hBL hBP₂ hP₂L hBX).2 hsub
    exact huY fun y hy => (hP₂X (hY₂P hy)).2
  · exfalso
    obtain ⟨π, hπ⟩ := h5
    exact false_of_sl5 hΛ π hπ.1
  · obtain ⟨hn45, hnd'⟩ := hnd
    rcases hn45 with rfl | rfl
    · have hnd4 : SumNatDual Λ (commV Λ) 4 := ⟨Or.inl rfl, hnd'⟩
      obtain ⟨D, hcuts, hq₁, hq₃, hfix⟩ := nd_package2 hV2 hne hF.sylow hnd4
      have hsplit := isIntDirect_nd hp2 hnd4 hfix
      have hkey := hkey_of_cuts hF D (C := {1, 3}) (by
        intro i hi
        rcases hi with rfl | rfl <;> norm_num) hcuts hfix
      refine ⟨hsplit, hkey, Or.inr (Or.inr ?_)⟩
      obtain ⟨P₁, P₂, P₃, ⟨hBP₁, hP₁L, hP₁c⟩, ⟨hBP₂, hP₂L, hP₂c⟩, ⟨hBP₃, hP₃L, hP₃c⟩, hinv, hall,
        -, -, hpos⟩ := core4_frame hF D
      refine ⟨D, P₁, P₃, model_eq_QI_of_cuts D hBL hBP₁ hP₁c,
        model_eq_QI_of_cuts D hBL hBP₃ hP₃c, ?_, ?_⟩
      · obtain ⟨q, hqU, hq1, hqP, hqc⟩ := hq₁ P₁ hBP₁ hP₁L hP₁c
        obtain ⟨ψ, hψs, hψk⟩ := exists_psi_of_cuts_one D hBL hBP₁ hP₁L hP₁c
        refine ⟨ψ, q, hBP₁, hP₁L, ?_, hinv P₁ hBP₁ hP₁L, ?_, ?_, hψs, hψk, hqU, hq1, hqP, hqc⟩
        · intro h
          rw [h, D.cutsOf_L] at hP₁c
          exact absurd hP₁c (Set.empty_ne_singleton 1)
        · intro X hBX' hXL hXne hYX hP₁X
          rcases hall X hBX' hXL hXne with h | h | h
          · have hY₁ : Y₁ ≤ P₁ := le_sup_left.trans (hYX.trans h)
            have hY₂ : Y₂ ≤ P₁ := le_sup_right.trans (hYX.trans h)
            rcases hpos with ⟨-, -, -, h4⟩ | ⟨-, h2, -, -⟩
            · exact h4 hY₂
            · exact h2 hY₁
          · have h12 : P₁ ≤ P₂ := hP₁X.trans h
            have hsub := (D.cutsOf_le_iff hBL hBP₁ hP₁L hBP₂).1 h12
            rw [hP₂c, hP₁c] at hsub
            have := hsub (Set.mem_singleton 2)
            norm_num at this
          · have hY₁ : Y₁ ≤ P₃ := le_sup_left.trans (hYX.trans h)
            have hY₂ : Y₂ ≤ P₃ := le_sup_right.trans (hYX.trans h)
            rcases hpos with ⟨-, h2, -, -⟩ | ⟨-, -, -, h4⟩
            · exact h2 hY₁
            · exact h4 hY₂
        · rcases hpos with ⟨h1, -, -, -⟩ | ⟨-, -, h3, -⟩
          · exact Or.inl h1
          · exact Or.inr h3
      · obtain ⟨q, hqU, hq1, hqP, hqc⟩ := hq₃ P₃ hBP₃ hP₃L hP₃c
        obtain ⟨ψ, hψs, hψk⟩ := exists_psi_of_cuts D hBL hBP₃ hP₃L hP₃c
        refine ⟨ψ, q, hBP₃, hP₃L, ?_, hinv P₃ hBP₃ hP₃L, ?_, ?_, hψs, hψk, hqU, hq1, hqP, hqc⟩
        · intro h
          rw [h, D.cutsOf_L] at hP₃c
          exact absurd hP₃c (Set.empty_ne_singleton 3)
        · intro X hBX' hXL hXne hYX hP₃X
          rcases hall X hBX' hXL hXne with h | h | h
          · have hY₁ : Y₁ ≤ P₁ := le_sup_left.trans (hYX.trans h)
            have hY₂ : Y₂ ≤ P₁ := le_sup_right.trans (hYX.trans h)
            rcases hpos with ⟨-, -, -, h4⟩ | ⟨-, h2, -, -⟩
            · exact h4 hY₂
            · exact h2 hY₁
          · have h32 : P₃ ≤ P₂ := hP₃X.trans h
            have hsub := (D.cutsOf_le_iff hBL hBP₃ hP₃L hBP₂).1 h32
            rw [hP₂c, hP₃c] at hsub
            have := hsub (Set.mem_singleton 2)
            norm_num at this
          · have hY₁ : Y₁ ≤ P₃ := le_sup_left.trans (hYX.trans h)
            have hY₂ : Y₂ ≤ P₃ := le_sup_right.trans (hYX.trans h)
            rcases hpos with ⟨-, h2, -, -⟩ | ⟨-, -, -, h4⟩
            · exact h2 hY₁
            · exact h4 hY₂
        · rcases hpos with ⟨-, -, h3, -⟩ | ⟨h1, -, -, -⟩
          · exact Or.inr h3
          · exact Or.inl h1
    · exfalso
      obtain ⟨π, U₁, U₂, -, hr₁, -⟩ := hnd'
      exact false_of_sl5 hΛ π hr₁.1
  · rcases hn with rfl | rfl
    · obtain ⟨D, hcuts, hfix⟩ := iso_package hV2 hne hF.sylow hk1 hnat
      have hsplit := isIntDirect_iso hΛ hk1 hp2 hnat hfix
      have hkey := hkey_of_cuts hF D (C := {1}) (by
        intro i hi
        rw [Set.mem_singleton_iff] at hi
        omega) hcuts hfix
      refine ⟨hsplit, hkey, ?_⟩
      obtain ⟨P₁, P₂, P₃, ⟨hBP₁, hP₁L, hP₁c⟩, -, -, -, -, -, -, hpos⟩ := core4_frame hF D
      have hP₁X : P₁ ≤ Λ ⊓ fixSub u :=
        (D.cutsOf_le_iff hBL hBP₁ hP₁L hBX).2 (by rw [hP₁c]; exact hcuts u hu huB)
      rcases hpos with ⟨h1, -, -, -⟩ | ⟨-, -, h2, -⟩
      · exact Or.inl fun y hy => (hP₁X (h1 hy)).2
      · exact Or.inr (Or.inl fun y hy => (hP₁X (h2 hy)).2)
    · exfalso
      obtain ⟨I, π, -, -, -, hreal⟩ := hnat
      exact false_of_sl5 hΛ π (hreal ⟨0, hk1⟩).1

end VMain2

end CFSG.Quasithin.A38c10
