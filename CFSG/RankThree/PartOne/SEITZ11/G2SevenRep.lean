module

public import CFSG.RankThree.PartOne.SEITZ11.G2SevenData
public import CFSG.LieType.Steinberg.RankTwo.Statement
public import CFSG.LieType.Steinberg.RankTwo.G2Extras
public import CFSG.LieType.Steinberg.RankTwo.G2Comm
public import CFSG.LieType.Steinberg.RankTwo.G2CommCheck

public section

namespace CFSG.RankThree.PartOne.SEITZ11.G2Seven

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.RankTwo CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps CFSG.LieType.Universal
  CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley.RootWalk
open scoped commutatorElement

section Units

variable (R : Type*) [CommRing R]

@[expose] def rootU (g : ℕ) (hg : g < 12) (t : R) : GL (Fin 7) R :=
  ⟨rootMat g t, rootMat g (-t), by rw [← rootMat_add g hg]; simp [rootMat_zero],
    by rw [← rootMat_add g hg]; simp [rootMat_zero]⟩

@[expose] def posU (g : ℕ) (t : R) : GL (Fin 7) R := if h : g < 12 then rootU R g h t else 1

theorem posU_add (g : ℕ) (c d : R) : posU R g (c + d) = posU R g c * posU R g d := by
  unfold posU
  split_ifs with h
  · exact Units.ext (by simp [rootU, rootMat_add g h])
  · simp

theorem posU_neg (g : ℕ) (c : R) : posU R g (-c) = (posU R g c)⁻¹ := by
  unfold posU
  split_ifs with h
  · exact Units.ext (by simp [rootU])
  · simp

theorem val_posU (g : ℕ) (hg : g < 12) (t : R) :
    ((posU R g t : GL (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) = rootMat g t := by
  simp [posU, hg, rootU]

@[expose] def Holds {H : Type*} [Group H] (yp : ℕ → R → H) (a b : ℕ) (fs : List Factor) : Prop :=
  ∀ c d : R, ⁅yp a c, yp b d⁆ =
    (fs.map fun f => yp f.2.2.1 ((f.2.2.2 : R) * c ^ f.1 * d ^ f.2.1)).prod

theorem Holds.inv {H : Type*} [Group H] {yp : ℕ → R → H}
    (hneg : ∀ a c, yp a (-c) = (yp a c)⁻¹) {a b : ℕ} {fs : List Factor}
    (h : Holds R yp b a fs) : Holds R yp a b (g2CommInv fs) := by
  intro c d
  rw [← commutatorElement_inv, h d c, List.prod_inv_reverse, g2CommInv, List.map_map,
    List.map_map, List.map_reverse]
  congr 2
  refine List.map_congr_left fun f _ => ?_
  simp only [Function.comp_apply]
  rw [← hneg]
  congr 1
  push_cast
  ring

theorem Holds.lookup {H : Type*} [Group H] {yp : ℕ → R → H}
    (hneg : ∀ a c, yp a (-c) = (yp a c)⁻¹) {T : List ((ℕ × ℕ) × List Factor)}
    (hT : ∀ e ∈ T, Holds R yp e.1.1 e.1.2 e.2) {a b : ℕ} (hne : g2CommLookup T a b ≠ []) :
    Holds R yp a b (g2CommLookup T a b) := by
  unfold g2CommLookup at hne ⊢
  rcases h1 : T.find? (fun e => e.1 == (a, b)) with _ | e
  · rw [h1] at hne ⊢
    rcases h2 : T.find? (fun e => e.1 == (b, a)) with _ | e
    · rw [h2] at hne
      exact absurd rfl hne
    · rw [h2]
      have hkey : e.1 = (b, a) := by simpa using List.find?_some h2
      have := hT e (List.mem_of_find?_eq_some h2)
      rw [hkey] at this
      exact this.inv R hneg
  · rw [h1]
    have hkey : e.1 = (a, b) := by simpa using List.find?_some h1
    have := hT e (List.mem_of_find?_eq_some h1)
    rwa [hkey] at this

theorem holds_of_repCheck {a b : ℕ} {fs : List Factor} (ha : a < 12) (hb : b < 12)
    (hfs : ∀ f ∈ fs, f.2.2.1 < 12) (h : repCheck7 a b fs = true) :
    Holds R (posU R) a b fs := by
  intro c d
  have hm := repCheck7_sound (R := R) h c d
  have hfac : ∀ f ∈ fs, ((posU R f.2.2.1 ((f.2.2.2 : R) * c ^ f.1 * d ^ f.2.1) : GL (Fin 7) R) :
      Matrix (Fin 7) (Fin 7) R) = facMat f c d := fun f hf => by
    rw [val_posU R _ (hfs f hf)]; rfl
  have hprod : ((fs.map fun f => posU R f.2.2.1 ((f.2.2.2 : R) * c ^ f.1 * d ^ f.2.1)).prod :
      GL (Fin 7) R).val = (fs.map fun f => facMat f c d).prod := by
    rw [show ((fs.map fun f => posU R f.2.2.1 ((f.2.2.2 : R) * c ^ f.1 * d ^ f.2.1)).prod :
        GL (Fin 7) R).val = (Units.coeHom (Matrix (Fin 7) (Fin 7) R))
        (fs.map fun f => posU R f.2.2.1 ((f.2.2.2 : R) * c ^ f.1 * d ^ f.2.1)).prod from rfl,
      map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun f hf => ?_
    simpa using hfac f hf
  rw [commutatorElement_def]
  have hmain : posU R a c * posU R b d = (fs.map fun f => posU R f.2.2.1 ((f.2.2.2 : R) *
      c ^ f.1 * d ^ f.2.1)).prod * (posU R b d * posU R a c) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hprod, val_posU R a ha, val_posU R b hb]
    exact hm
  rw [hmain]
  simp [mul_assoc]

theorem holds_posU_table : ∀ e ∈ g2CommPairs, Holds R (posU R) e.1.1 e.1.2 e.2 := fun e he =>
  holds_of_repCheck R (table_lt e he).1 (table_lt e he).2.1 (table_lt e he).2.2
    (List.all_eq_true.1 tableOk_true e he)

theorem holds_posU (a b : ℕ) (ha : a < 12) (hb : b < 12) (hab : a ≠ b)
    (hs : g2CommRoot a + g2CommRoot b ≠ 0) : Holds R (posU R) a b (g2CommFactors a b) := by
  by_cases h0 : g2CommFactors a b = []
  · rw [h0]
    have hr : repCheck7 a b [] = true := by
      have hc := List.all_eq_true.1 (List.all_eq_true.1 commOk_true a (List.mem_range.2 ha)) b
        (List.mem_range.2 hb)
      simpa [hab, hs, h0] using hc
    exact holds_of_repCheck R ha hb (fun f hf => absurd hf List.not_mem_nil) hr
  · exact Holds.lookup R (posU_neg R) (holds_posU_table R) h0

end Units


section Table

open _root_.Classical in
@[expose] noncomputable def ordList
    (α β : Fin (Tag.rank .G2) → ℤ) : List (ℕ × ℕ) :=
  if h : IsRoot .G2 α ∧ IsRoot .G2 β ∧ α ≠ β ∧ α + β ≠ 0 then
    g2CommExps (g2CommFactors (rootPos (⟨α, h.1⟩ : Root .G2)) (rootPos (⟨β, h.2.1⟩ : Root .G2)))
  else []

open _root_.Classical in
@[expose] noncomputable def constC
    (α β : Fin (Tag.rank .G2) → ℤ) (p : ℕ × ℕ) : ℤ :=
  if h : IsRoot .G2 α ∧ IsRoot .G2 β then
    g2CommCoeff (g2CommFactors (rootPos (⟨α, h.1⟩ : Root .G2)) (rootPos (⟨β, h.2⟩ : Root .G2))) p
  else 1

theorem pos_lt_twelve
    (α : Root .G2) : rootPos α < 12 := by
  have := rootPos_lt α
  rwa [g2CommRoot_length] at this

theorem commFormula_of_holds
    {R : Type*} [CommRing R] {H : Type*} [Group H] (yy : (Fin (Tag.rank .G2) → ℤ) → R → H)
    (hadd : ∀ γ, IsRoot .G2 γ → ∀ c d, yy γ (c + d) = yy γ c * yy γ d)
    (hold : ∀ a b, a < 12 → b < 12 → a ≠ b → g2CommRoot a + g2CommRoot b ≠ 0 → ∀ c d : R,
      ⁅yy (g2CommRoot a) c, yy (g2CommRoot b) d⁆ = ((g2CommFactors a b).map fun f =>
        yy (g2CommRoot f.2.2.1) ((f.2.2.2 : R) * c ^ f.1 * d ^ f.2.1)).prod) :
    ∀ α β : Fin (Tag.rank .G2) → ℤ, IsRoot .G2 α → IsRoot .G2 β → α + β ≠ 0 → ∀ c d : R,
      ⁅yy α c, yy β d⁆ = ((ordList α β).map fun p =>
        yy (p.1 • α + p.2 • β) ((constC α β p : R) * c ^ p.1 * d ^ p.2)).prod := by
  intro α β hα hβ hsum c d
  by_cases hne : α = β
  · subst hne
    have hnil : ordList α α = [] := by
      classical
      unfold ordList
      split_ifs with h
      · exact absurd rfl h.2.2.1
      · rfl
    rw [hnil, List.map_nil, List.prod_nil, commutatorElement_eq_one_iff_commute, Commute,
      SemiconjBy, ← hadd α hα, ← hadd α hα, add_comm]
  · obtain ⟨a, ha⟩ : ∃ a, a = rootPos (⟨α, hα⟩ : Root .G2) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = rootPos (⟨β, hβ⟩ : Root .G2) := ⟨_, rfl⟩
    have ha12 : a < 12 := by rw [ha]; exact pos_lt_twelve _
    have hb12 : b < 12 := by rw [hb]; exact pos_lt_twelve _
    have hra : g2CommRoot a = α := by rw [ha]; exact root_rootPos _
    have hrb : g2CommRoot b = β := by rw [hb]; exact root_rootPos _
    have hab : a ≠ b := fun h => hne (by rw [← hra, ← hrb, h])
    have hs : g2CommRoot a + g2CommRoot b ≠ 0 := by rw [hra, hrb]; exact hsum
    obtain ⟨hd, hok, -⟩ := g2CommPairOk_spec ha12 hb12 hab hs
    obtain ⟨hcone, hcomp, hnd, hcomm⟩ := g2CommListOk_spec hok
    have hroot : ∀ f ∈ g2CommFactors a b,
        g2CommRoot f.2.2.1 = f.1 • g2CommRoot a + f.2.1 • g2CommRoot b := fun f hf => by
      have hc := List.all_eq_true.1 hcone f hf
      simp only [coneOk, Bool.and_eq_true] at hc
      exact CFSG.LieType.Ree.vecBEq_iff.1 hc.2
    have hlist : ordList α β = g2CommExps (g2CommFactors a b) := by
      classical
      unfold ordList
      split_ifs with h
      · rw [← ha, ← hb]
      · exact absurd ⟨hα, hβ, hne, hsum⟩ h
    have hconst : ∀ p, constC α β p = g2CommCoeff (g2CommFactors a b) p := fun p => by
      classical
      unfold constC
      split_ifs with h
      · rw [← ha, ← hb]
      · exact absurd ⟨hα, hβ⟩ h
    rw [hlist, g2CommExps, List.map_map]
    have := hold a b ha12 hb12 hab hs c d
    rw [hra, hrb] at this
    rw [this]
    congr 1
    refine List.map_congr_left fun f hf => ?_
    simp only [Function.comp_apply, hconst, g2CommCoeff_of_mem hnd hf]
    rw [hroot f hf, hra, hrb]

end Table


section Rep

noncomputable def ordOrder
    (k : Type) [Field k] :
    CommOrder (RootSystem.ofCartan (g2Datum k).isFiniteType (g2Datum k).divisible) where
  list := ordList
  nodup := fun α β => by
    classical
    unfold ordList
    split_ifs with h
    · obtain ⟨hα, hβ, hne, hsum⟩ := h
      have ha12 := pos_lt_twelve (⟨α, hα⟩ : Root .G2)
      have hb12 := pos_lt_twelve (⟨β, hβ⟩ : Root .G2)
      have hra : g2CommRoot (rootPos (⟨α, hα⟩ : Root .G2)) = α := root_rootPos _
      have hrb : g2CommRoot (rootPos (⟨β, hβ⟩ : Root .G2)) = β := root_rootPos _
      have hab : rootPos (⟨α, hα⟩ : Root .G2) ≠ rootPos (⟨β, hβ⟩ : Root .G2) := fun h =>
        hne (by rw [← hra, ← hrb, h])
      have hs : g2CommRoot (rootPos (⟨α, hα⟩ : Root .G2)) +
          g2CommRoot (rootPos (⟨β, hβ⟩ : Root .G2)) ≠ 0 := by
        rw [hra, hrb]; exact hsum
      exact (g2CommListOk_spec (g2CommPairOk_spec ha12 hb12 hab hs).2.1).2.2.1
    · exact List.nodup_nil
  mem_iff := fun α hα β hβ hsum p => by
    classical
    have hΦ : (RootSystem.ofCartan (g2Datum k).isFiniteType (g2Datum k).divisible).roots =
        {γ | IsRoot .G2 γ} := adjDatum_roots _ k
    have hα' : IsRoot .G2 α := by rw [hΦ] at hα; exact hα
    have hβ' : IsRoot .G2 β := by rw [hΦ] at hβ; exact hβ
    by_cases hne : α = β
    · subst hne
      have hnil : ordList α α = [] := by
        unfold ordList
        split_ifs with h
        · exact absurd rfl h.2.2.1
        · rfl
      rw [hnil]
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨h1, h2, h3⟩
      rw [hΦ, ← add_nsmul] at h3
      have := eq_one_of_isRoot_nsmul (τ := .G2) h3
      omega
    · obtain ⟨a, ha⟩ : ∃ a, a = rootPos (⟨α, hα'⟩ : Root .G2) := ⟨_, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b, b = rootPos (⟨β, hβ'⟩ : Root .G2) := ⟨_, rfl⟩
      have ha12 : a < 12 := by rw [ha]; exact pos_lt_twelve _
      have hb12 : b < 12 := by rw [hb]; exact pos_lt_twelve _
      have hra : g2CommRoot a = α := by rw [ha]; exact root_rootPos _
      have hrb : g2CommRoot b = β := by rw [hb]; exact root_rootPos _
      have hab : a ≠ b := fun h => hne (by rw [← hra, ← hrb, h])
      have hs : g2CommRoot a + g2CommRoot b ≠ 0 := by rw [hra, hrb]; exact hsum
      obtain ⟨hd, hok, -⟩ := g2CommPairOk_spec ha12 hb12 hab hs
      obtain ⟨hcone, hcomp, hnd, hcomm⟩ := g2CommListOk_spec hok
      have hlist : ordList α β = g2CommExps (g2CommFactors a b) := by
        unfold ordList
        split_ifs with h
        · rw [← ha, ← hb]
        · exact absurd ⟨hα', hβ', hne, hsum⟩ h
      rw [hlist, mem_g2CommExps_iff hd hcone hcomp p, hra, hrb]
      change _ ↔ (_ ∧ _ ∧ _ ∈ _)
      rw [hΦ]
      rfl

@[expose] noncomputable def yfam
    (k : Type) [Field k] (γ : Fin (Tag.rank .G2) → ℤ) (c : k) : GL (Fin 7) k := by
  classical
  exact posU k (if h : IsRoot .G2 γ then rootPos (⟨γ, h⟩ : Root .G2) else 12) c

theorem yfam_root
    (k : Type) [Field k] {a : ℕ} (ha : a < 12) (c : k) :
    yfam k (g2CommRoot a) c = posU k a c := by
  classical
  have hr := isRoot_rootCertificate_root (τ := .G2) (k := a)
    (by rw [g2CommRoot_length]; exact ha)
  unfold yfam
  split_ifs with h
  · congr 2
    exact rootPos_eq (by rw [g2CommRoot_length]; exact ha) rfl
  · exact absurd hr h

theorem yfam_add
    (k : Type) [Field k] (γ : Fin (Tag.rank .G2) → ℤ) (c d : k) :
    yfam k γ (c + d) = yfam k γ c * yfam k γ d := by
  classical
  unfold yfam
  exact posU_add k _ c d

theorem hold_yfam
    (k : Type) [Field k] (a b : ℕ) (ha : a < 12) (hb : b < 12) (hab : a ≠ b)
    (hs : g2CommRoot a + g2CommRoot b ≠ 0) (c d : k) :
    ⁅yfam k (g2CommRoot a) c, yfam k (g2CommRoot b) d⁆ = ((g2CommFactors a b).map fun f =>
      yfam k (g2CommRoot f.2.2.1) ((f.2.2.2 : k) * c ^ f.1 * d ^ f.2.1)).prod := by
  rw [yfam_root k ha, yfam_root k hb, holds_posU k a b ha hb hab hs c d]
  congr 1
  refine List.map_congr_left fun f hf => ?_
  rw [yfam_root k (factors_lt a ha b hb f hf)]

theorem holds_xPar_table
    (k : Type) [Field k] :
    ∀ e ∈ g2CommPairs, Holds k (fun a => xPar (rootOperatorFamily .G2) (g2CommRoot a) (K := k))
      e.1.1 e.1.2 e.2 := fun e he c d =>
  CFSG.Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := .G2)
    (List.all_eq_true.1 g2CommPairs_check e he) c d

theorem holds_xPar
    (k : Type) [Field k] (a b : ℕ) (ha : a < 12) (hb : b < 12) (hab : a ≠ b)
    (hs : g2CommRoot a + g2CommRoot b ≠ 0) :
    Holds k (fun a => xPar (rootOperatorFamily .G2) (g2CommRoot a) (K := k)) a b
      (g2CommFactors a b) := by
  obtain ⟨hd, hok, -⟩ := g2CommPairOk_spec ha hb hab hs
  by_cases h0 : g2CommFactors a b = []
  · intro c d
    rw [h0, List.map_nil, List.prod_nil]
    have hcomp := (g2CommListOk_spec hok).2.1
    rw [h0] at hcomp
    exact commutator_g2CommRoot_eq_one ha hb hd hcomp c d
  · exact Holds.lookup k (fun a c => (xPar_neg _ _).symm) (holds_xPar_table k) h0

theorem existsUnique_rep7
    (k : Type) [Field k] [Finite k] :
    ∃! φ : adjointGroup .G2 k →* GL (Fin 7) k,
      ∀ γ, IsRoot .G2 γ → ∀ c, φ (xPar (rootOperatorFamily .G2) γ c) = yfam k γ c := by
  have hrt : RankTwoPresentation.{0, 0} (g2Datum k) k
      (xPar (rootOperatorFamily .G2) (K := k)) :=
    rankTwoPresentation_of_conclusionB
      (g2_conclusionB_of_comm fun O => g2_exists_commutatorFormula k O)
  have hΦ : (RootSystem.ofCartan (g2Datum k).isFiniteType (g2Datum k).divisible).roots =
      {γ | IsRoot .G2 γ} := adjDatum_roots _ k
  have hCx : CommutatorFormula (xPar (rootOperatorFamily .G2) (K := k)) (ordOrder k) constC :=
    fun α hα β hβ hsum c d =>
      commFormula_of_holds (xPar (rootOperatorFamily .G2) (K := k))
        (fun γ _ c d => xPar_add γ c d)
        (fun a b ha hb hab hs c d => holds_xPar k a b ha hb hab hs c d)
        α β (by rw [hΦ] at hα; exact hα) (by rw [hΦ] at hβ; exact hβ) hsum c d
  have hCy : CommutatorFormula (yfam k) (ordOrder k) constC :=
    fun α hα β hβ hsum c d =>
      commFormula_of_holds (yfam k) (fun γ _ c d => yfam_add k γ c d)
        (fun a b ha hb hab hs c d => hold_yfam k a b ha hb hab hs c d)
        α β (by rw [hΦ] at hα; exact hα) (by rw [hΦ] at hβ; exact hβ) hsum c d
  obtain ⟨φ, hφ, huniq⟩ := hrt.2.2.1 (ordOrder k) constC hCx (GL (Fin 7) k) (yfam k)
    (fun γ _ c d => yfam_add k γ c d) hCy
  exact ⟨φ, fun γ hγ c => hφ γ (by rw [hΦ]; exact hγ) c, fun ψ hψ =>
    huniq ψ fun γ hγ c => hψ γ (by rw [hΦ] at hγ; exact hγ) c⟩

@[expose] noncomputable def rep7
    (k : Type) [Field k] [Finite k] : adjointGroup .G2 k →* GL (Fin 7) k :=
  (existsUnique_rep7 k).choose

theorem rep7_xPar
    (k : Type) [Field k] [Finite k] {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (c : k) :
    rep7 k (xPar (rootOperatorFamily .G2) γ c) = yfam k γ c :=
  (existsUnique_rep7 k).choose_spec.1 γ hγ c

theorem rep7_unique
    (k : Type) [Field k] [Finite k] (ψ : adjointGroup .G2 k →* GL (Fin 7) k)
    (h : ∀ γ, IsRoot .G2 γ → ∀ c, ψ (xPar (rootOperatorFamily .G2) γ c) = yfam k γ c) :
    ψ = rep7 k :=
  (existsUnique_rep7 k).unique h (existsUnique_rep7 k).choose_spec.1

theorem rep7_xPar_pos
    (k : Type) [Field k] [Finite k] {a : ℕ} (ha : a < 12) (c : k) :
    ((rep7 k (xPar (rootOperatorFamily .G2) (g2CommRoot a) c) : GL (Fin 7) k) :
      Matrix (Fin 7) (Fin 7) k) = rootMat a c := by
  have hr := isRoot_rootCertificate_root (τ := .G2) (k := a)
    (by rw [g2CommRoot_length]; exact ha)
  rw [rep7_xPar k hr, yfam_root k ha, val_posU k a ha]

end Rep

end CFSG.RankThree.PartOne.SEITZ11.G2Seven
