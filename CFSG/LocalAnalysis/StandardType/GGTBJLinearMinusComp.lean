module

public import CFSG.LocalAnalysis.StandardType.GGTBJLinearMinusFrame
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLComp
public import CFSG.GroupTheory.SubgroupCardMul
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Polynomial CFSG.RankThree.CALinearPlane
open Multiplicative

private theorem exists_frame_block_of_linMinus
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2] {g : F[X]} [Fact (Irreducible g)]
    {r f s t : ℕ} {Bs X J : Subgroup G} {u w₀ : G}
    {φ : Matrix.SpecialLinearGroup (Fin (r + 1)) F →* G}
    {ε : Fin (r + 1) ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin t}
    {hC : (CoordSL.rootMat g).det = 1} {hCp : CoordSL.rootMat g ^ p = 1}
    (hp2 : p ≠ 2) (hF : Nat.card F = 2 ^ f) (hpq : p ∣ 2 ^ f + 1)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) F))
    (hgd : g ∣ cyclotomic p F) (hζ : AdjoinRoot.root g ^ p = 1)
    (hrange : φ.range = X)
    (hframe : (CoordSL.frameHom φ 1 ε hC hCp).range = Bs ⊓ X)
    (htriv : Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (hsup : (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) = Bs)
    (hBs : IsElemAbelian p Bs) (huBs : u ∈ Bs)
    (huX : u ∉ Subgroup.centralizer (X : Set G))
    (hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({u} : Set G)))
    (hw₀ : w₀ ∈ Bs ⊓ Subgroup.centralizer (X : Set G)) (hw₀ne : w₀ ≠ 1)
    (hw₀J : w₀ ∈ Subgroup.centralizer (J : Set G))
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    ∃ (A₁ : Matrix.SpecialLinearGroup (Fin (r + 1)) F) (β₁ : Fin s → ZMod p),
      (CoordSL.frameHom φ A₁ ε hC hCp).range = Bs ⊓ X ∧
      ((∃ j j' : Fin s, (∀ i, i ≠ j → i ≠ j' → β₁ i = 0) ∧
          J = (coordBlockSL F (CoordSL.zeroCoords ε β₁)).map (SLRep.ggFrame φ A₁)) ∨
        (∃ (k : Fin s) (c : ZMod p), c ≠ 0 ∧ (∀ i, i ≠ k → β₁ i = c) ∧
          J = (coordBlockSL (AdjoinRoot g) (CoordSL.classSet β₁ c)).map
            ((SLRep.ggFrame φ A₁).comp (CoordSL.theta g ε)))) := by
  classical
  have hcommAC : ∀ a ∈ Bs ⊓ X, ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G),
      a * b = b * a := fun a ha b hb => hBs.comm ha.1 hb.1
  have hu' : u ∈ (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [hsup]
    exact huBs
  obtain ⟨w, hw, c, hc, hwcu⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommAC hu'
  have hw1 : w ≠ 1 := by
    intro h
    apply huX
    rw [← hwcu, h, one_mul]
    exact hc.2
  have hiff : ∀ z ∈ X, (u * z = z * u ↔ w * z = z * w) := by
    intro z hzX
    have hcz : c * z = z * c := (Subgroup.mem_centralizer_iff.mp hc.2 z hzX).symm
    have h1 : z * u = (z * w) * c := by rw [← hwcu, mul_assoc]
    have h2 : u * z = (w * z) * c := by rw [← hwcu, mul_assoc, hcz, ← mul_assoc]
    rw [h2, h1, mul_right_cancel_iff]
  have hcent : X ⊓ Subgroup.centralizer ({w} : Set G) =
      X ⊓ Subgroup.centralizer ({u} : Set G) := by
    ext z
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hzX, hzc⟩
      refine ⟨hzX, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hzc ⊢
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact (hiff z hzX).mpr (hzc w rfl)
    · rintro ⟨hzX, hzc⟩
      refine ⟨hzX, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hzc ⊢
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact (hiff z hzX).mp (hzc u rfl)
  have hwr : w ∈ (CoordSL.frameHom φ 1 ε hC hCp).range := by
    rw [hframe]
    exact hw
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hwr
  obtain ⟨β, hβ⟩ : ∃ β : Fin s → ZMod p,
      CoordSL.frameHom φ 1 ε hC hCp (ofAdd β) = w := ⟨Multiplicative.toAdd a, ha⟩
  have hb1 : CoordSL.frameHom φ 1 ε hC hCp (ofAdd β) ≠ 1 := by
    rw [hβ]
    exact hw1
  have hw₀p : w₀ ^ p = 1 := hBs.2 w₀ hw₀.1
  have hw₀card : Nat.card (Subgroup.zpowers w₀) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hw₀p hw₀ne]
  have hAle : (Bs ⊓ X) ⊓ Subgroup.centralizer (J : Set G) ≤
      Bs ⊓ Subgroup.centralizer (J : Set G) := by
    refine le_inf ?_ inf_le_right
    exact inf_le_left.trans inf_le_left
  have hWle : Subgroup.zpowers w₀ ≤ Bs ⊓ Subgroup.centralizer (J : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hw₀.1, hw₀J⟩
  have hdisj : ((Bs ⊓ X) ⊓ Subgroup.centralizer (J : Set G)) ⊓ Subgroup.zpowers w₀ = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    have h1 : (z : G) ∈ Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) :=
      ⟨⟨hz.1.1.1, hz.1.1.2⟩, (Subgroup.zpowers_le.mpr hw₀.2) hz.2⟩
    rw [htriv] at h1
    exact h1
  have hcard : Nat.card ↥((Bs ⊓ X) ⊓ Subgroup.centralizer (J : Set G)) * p ≤
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
    have h := CFSG.card_mul_card_le_of_inf_eq_bot hAle hWle hdisj
    rwa [hw₀card] at h
  have hamb : Nat.card ↥((Bs ⊓ X) ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 2 := by
    have hmain : Nat.card ↥((Bs ⊓ X) ⊓ Subgroup.centralizer (J : Set G)) * p ≤ p ^ 2 * p := by
      refine hcard.trans (hCJ.trans (le_of_eq ?_))
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
    exact Nat.le_of_mul_le_mul_right hmain (Fact.out : p.Prime).pos
  have hpK : ¬ p ∣ Nat.card F - 1 := by
    rw [hF]
    intro hdvd
    have h2 : p ∣ 2 := by
      have hsub := Nat.dvd_sub hpq hdvd
      have hcalc : 2 ^ f + 1 - (2 ^ f - 1) = 2 := by
        have := Nat.two_pow_pos f
        omega
      rwa [hcalc] at hsub
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact hp2 (by omega)
  have hcomp' : IsComponentOf J (φ.range ⊓ Subgroup.centralizer
      ({CoordSL.frameHom φ 1 ε hC hCp (ofAdd β)} : Set G)) := by
    rw [hrange, hβ, hcent]
    exact hcomp
  have hcardFin : Nat.card ((CoordSL.frameHom φ 1 ε hC hCp).range ⊓
      Subgroup.centralizer (J : Set G) : Subgroup G) ≤ p ^ 2 := by
    rw [hframe]
    exact hamb
  obtain ⟨A₁, β₁, hAr, -, hres⟩ :=
    CoordSL.comp_eq_of_frame (ψ := φ) (A₀ := 1) (ε := ε) (hC := hC) (hCp := hCp)
      (β := β) (L₁ := J) hp2 hpK hker hgd hζ hb1 hcomp' hcardFin
  exact ⟨A₁, β₁, hAr.trans hframe, hres⟩

theorem exists_comp_of_linMinus_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (g : F[X])
      (_ : Fact (Irreducible g)) (hC : (CoordSL.rootMat g).det = 1)
      (hCp : CoordSL.rootMat g ^ p = 1) (s t : ℕ)
      (ε : Fin (r + 1) ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin t)
      (φ : Matrix.SpecialLinearGroup (Fin (r + 1)) F →* G)
      (A₁ : Matrix.SpecialLinearGroup (Fin (r + 1)) F) (β : Fin s → ZMod p),
      Nat.card F = 2 ^ f ∧ g ∣ cyclotomic p F ∧ AdjoinRoot.root g ^ p = 1 ∧
        φ.range = L ∧ φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) F) ∧
        3 ≤ s ∧ (CoordSL.frameHom φ A₁ ε hC hCp).range = Bs ⊓ L ∧
        Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
        (Bs ⊓ L) ⊔ (Bs ⊓ Subgroup.centralizer (L : Set G)) = Bs ∧
        ((∃ j j' : Fin s, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
            J = (coordBlockSL F (CoordSL.zeroCoords ε β)).map (SLRep.ggFrame φ A₁)) ∨
          (∃ (k : Fin s) (c : ZMod p), c ≠ 0 ∧ (∀ i, i ≠ k → β i = c) ∧
            J = (coordBlockSL (AdjoinRoot g) (CoordSL.classSet β c)).map
              ((SLRep.ggFrame φ A₁).comp (CoordSL.theta g ε)))) := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  obtain ⟨F, hField, hFinite, hChar, g, hIrr, hC, hCp, s, t, ε, φ,
    hF, hgd, hζ, hrange, hker, h3s, hframe, htriv, hsup⟩ :=
    exists_frame_of_linMinus_side hH (Or.inl rfl) hpq hmark
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have : Fact (Irreducible g) := hIrr
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hH.1.tableB_facts.2.2.2.1 hl) x rfl).symm
  have hyBs : y ∈ Bs := hH.1.2.1.1 hnb.1.2.1
  have hyD : y ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (by simp)
  have hyL : y ∉ Subgroup.centralizer (L : Set G) := by
    intro hyc
    have hyzx : y ∈ Subgroup.zpowers x := by
      rw [← hH.1.bstar_inf_centralizer_L]
      exact ⟨hyBs, hyc⟩
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hnb.2.1, Subgroup.closure_le]
      intro z hz
      rw [Set.mem_insert_iff] at hz
      rcases hz with h | h
      · rw [h]
        exact Subgroup.mem_zpowers x
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact hyzx
    have hcardD : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
    have hcardx : Nat.card (Subgroup.zpowers x) = p := by
      rw [Nat.card_zpowers, hH.1.orderOf_x]
    have hle : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDle
    rw [hcardD, hcardx] at hle
    have h2 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num)
    omega
  have hcentD : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    refine le_antisymm ?_ ?_
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (by rintro z rfl; exact hyD))
    · rintro l ⟨hlL, hly⟩
      refine ⟨hlL, ?_⟩
      rw [hnb.2.1, Subgroup.centralizer_closure]
      change l ∈ Subgroup.centralizer ({x, y} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      change l ∈ Subgroup.centralizer ({y} : Set G) at hly
      rw [Subgroup.mem_centralizer_iff] at hly
      intro z hz
      rw [Set.mem_insert_iff] at hz
      rcases hz with h | h
      · rw [h]
        exact (Subgroup.mem_centralizer_iff.mp hxC l hlL).symm
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact hly y rfl
  have hcompL : IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) := by
    rw [← hcentD]
    exact hH.1.2.2.1.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hxJ : x ∈ Subgroup.centralizer (J : Set G) :=
    Subgroup.centralizer_le (hcompL.1.trans inf_le_left) hxC
  obtain ⟨A₁, β, hAr, hres⟩ :=
    exists_frame_block_of_linMinus hp2 hF hpq hker hgd hζ hrange hframe htriv hsup
      hH.1.2.1.2.1 hyBs hyL hcompL ⟨hxBs, hxC⟩ hH.1.1.2.2.2.2.2.2.1.2.2.1 hxJ
      hH.1.card_bstar_inf_centralizer_J_le
  exact ⟨F, hField, hFinite, hChar, g, hIrr, hC, hCp, s, t, ε, φ, A₁, β,
    hF, hgd, hζ, hrange, hker, h3s, hAr, htriv, hsup, hres⟩

theorem exists_comp_of_linMinus_K
    (hI3 : GGNbrSubcomponentInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (g : F[X])
      (_ : Fact (Irreducible g)) (hC : (CoordSL.rootMat g).det = 1)
      (hCp : CoordSL.rootMat g ^ p = 1) (s t : ℕ)
      (ε : Fin (r + 1) ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin t)
      (φ : Matrix.SpecialLinearGroup (Fin (r + 1)) F →* G)
      (A₁ : Matrix.SpecialLinearGroup (Fin (r + 1)) F) (β : Fin s → ZMod p),
      Nat.card F = 2 ^ f ∧ g ∣ cyclotomic p F ∧ AdjoinRoot.root g ^ p = 1 ∧
        φ.range = K ∧ φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) F) ∧
        3 ≤ s ∧ (CoordSL.frameHom φ A₁ ε hC hCp).range = Bs ⊓ K ∧
        Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G) = ⊥ ∧
        (Bs ⊓ K) ⊔ (Bs ⊓ Subgroup.centralizer (K : Set G)) = Bs ∧
        ((∃ j j' : Fin s, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
            J = (coordBlockSL F (CoordSL.zeroCoords ε β)).map (SLRep.ggFrame φ A₁)) ∨
          (∃ (k : Fin s) (c : ZMod p), c ≠ 0 ∧ (∀ i, i ≠ k → β i = c) ∧
            J = (coordBlockSL (AdjoinRoot g) (CoordSL.classSet β c)).map
              ((SLRep.ggFrame φ A₁).comp (CoordSL.theta g ε)))) := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hnb
  obtain ⟨F, hField, hFinite, hChar, g, hIrr, hC, hCp, s, t, ε, φ,
    hF, hgd, hζ, hrange, hker, h3s, hframe, htriv, hsup⟩ :=
    exists_frame_of_linMinus_side hH (Or.inr rfl) hpq hmark
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have : Fact (Irreducible g) := hIrr
  have hxD : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (by simp)
  have hxBs : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hxD)
  have hxK : x ∉ Subgroup.centralizer (K : Set G) := by
    intro hx
    have hKle : K ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      rw [← Subgroup.le_centralizer_iff]
      exact Subgroup.zpowers_le.mpr hx
    have hbot : ⁅K, Subgroup.zpowers x⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKle
    exact hnb.2.2.2 (hbot.le.trans bot_le)
  have hcompK : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  have hyBs : y ∈ Bs := hH.1.2.1.1 hnb.1.2.1
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hnb.1.2.2.2.1 hk) y rfl).symm
  have hyJ : y ∈ Subgroup.centralizer (J : Set G) := Subgroup.centralizer_le hJK hyK
  obtain ⟨A₁, β, hAr, hres⟩ :=
    exists_frame_block_of_linMinus hp2 hF hpq hker hgd hζ hrange hframe htriv hsup
      hH.1.2.1.2.1 hxBs hxK hcompK ⟨hyBs, hyK⟩ hnb.1.2.2.1 hyJ
      hH.1.card_bstar_inf_centralizer_J_le
  exact ⟨F, hField, hFinite, hChar, g, hIrr, hC, hCp, s, t, ε, φ, A₁, β,
    hF, hgd, hζ, hrange, hker, h3s, hAr, htriv, hsup, hres⟩

end CFSG.StandardType

end
