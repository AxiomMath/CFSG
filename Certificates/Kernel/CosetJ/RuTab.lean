
module

public import CFSG.Sporadic.Recognition.RuMultiplierTablesBase
public import Certificates.Kernel.CosetJ.RuTabChk
public import Certificates.Kernel.GMS78.W
public import Certificates.Kernel.LocalComp.SurjGen
public import CFSG.Certificates.Kernel.SurjKSound
public import CFSG.Certificates.Kernel.Spor.NatWordsTxt
import all Init.Data.List.SplitOn.Basic
import all Init.Data.Nat.ToString
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import all CFSG.Sporadic.Recognition.RuMultiplierInputs
import all CFSG.Sporadic.Presentation.RuExactInputs
import all CFSG.LieType.Multipliers.CoverWords
import all CFSG.LieType.Multipliers.TitsCheckInputs
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis
meta import Certificates.Data.CFSGNative.Bridge.SurjD
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Sporadic.Bridge.RuSurjBase

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCosetJ.RuTabIT CFSG.Sporadic.Bridge.SurjD.Native.ruImgText

#lc_words CertificateChecks.KernelCosetJ.RuTabIT CFSG.Sporadic.Bridge.SurjD.Native.ruImgText

namespace CertificateChecks.KernelCosetJ.RuTab

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.GMSW CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge
  CFSG.CosetTable CFSG.Sporadic.Bridge.VecSurj CFSG.Sporadic.Recognition.RuMultiplier
  CFSG.Sporadic.Presentation.Ru.Exact
open CertificateChecks.KernelSpor.SmallF2Rels (mat mat_mul mat_one mat_injective mat_inv)

local notation "Dt" => CFSG.Sporadic.Ru.Native.ruData

local notation "MUL" => CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28)
  (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM

noncomputable abbrev Y (M : Nat) := CertificateChecks.KernelGMS78.W.Y M

theorem imgOK : CFSG.KS.NatWords.digitsOK CertificateChecks.KernelCosetJ.RuTabIT.chars = true := by
  quickRfl

theorem img_words : (CFSG.KS.NatWords.natWords CertificateChecks.KernelCosetJ.RuTabIT.chars ==
    CertificateChecks.KernelCosetJ.RuTabIT.W) = true := by
  quickRfl

theorem neg_digits : notB (CFSG.KS.NatWords.digitsOK ['1', ' ', '-', '2']) = true := by quickRfl

theorem img_eq : CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.imgWords =
    CertificateChecks.KernelCosetJ.RuTabIT.W.toArray := by
  have e : CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.imgWords =
      CFSG.Sporadic.Bridge.SurjD.Native.parseWords
        CFSG.Sporadic.Bridge.SurjD.Native.ruImgText := rfl
  rw [e, CertificateChecks.KernelCosetJ.RuTabIT.eq, CFSG.KS.NatWords.parseWords_ofList imgOK,
    beq_iff_eq.mp img_words]

theorem RI_bind : relsEqK RI (mkImgK CertificateChecks.KernelCosetJ.RuTabIT.W (nat_lit 0)) = true := by
  quickRfl

theorem RT_eq : RT = ruTabWords.map fun w => w.map fun l => (l.1.val + 2, l.2) := by
  decide +kernel

theorem hom {R : List (List (Nat × Bool))} {n : Nat} (hb : relsBounded R 5 = true)
    (hall : relsAll RG MUL R 5 CFSG.KD.OrdRu.ONE 0 n = true) (hn : Nat.beq (lenRels R) n = true) :
    (∀ g < 5, Y (RG (g + 1)) * Y (RG (5 + 1 + g)) = 1) ∧
      ∀ v ∈ R, (v.map fun x => Y (letM RG 5 x)).prod = 1 :=
  CertificateChecks.KernelGMS78.W.homM roots invs hb hall hn

theorem inv_reg : ∀ g < 5, Y (RG (g + 1)) * Y (RG (5 + 1 + g)) = 1 := (hom RI_bd RI_all RI_len).1

theorem mat_a : mat Dt (a Dt) = Y (RG 1) := by
  rw [CertificateChecks.KernelGMS78.W.mat_a, Nat.eq_of_beq_eq_true CertificateChecks.KernelGMS78.W.bindA,
    ← Nat.eq_of_beq_eq_true bindA]

theorem mat_b : mat Dt (b Dt) = Y (RG 2) := by
  rw [CertificateChecks.KernelGMS78.W.mat_b, Nat.eq_of_beq_eq_true CertificateChecks.KernelGMS78.W.bindB,
    ← Nat.eq_of_beq_eq_true bindB]

@[expose] noncomputable def phi (g : ℕ) : J Dt :=
  if g = 0 then a Dt else if g = 1 then b Dt else img CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt) (g - 2)

theorem phi_img (k : ℕ) : phi (k + 2) = img CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt) k := by
  simp [phi]

theorem mat_wordProd {x : ℕ → J Dt} {L0 : Nat} (hL : L0 ≤ 5)
    (hx : ∀ g < L0, mat Dt (x g) = Y (RG (g + 1))) :
    ∀ v : List (ℕ × Bool), (∀ l ∈ v, l.1 < L0) →
      mat Dt (wordProd x v) = (v.map fun l => Y (letM RG 5 l)).prod
  | [], _ => rfl
  | l :: v, h => by
    have ih := mat_wordProd hL hx v fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have hl : l.1 < L0 := h l List.mem_cons_self
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [mat_mul, ih]
    congr 1
    obtain ⟨g, s⟩ := l
    cases s
    · exact mat_inv Dt (hx g hl) (inv_reg g (by omega))
    · exact hx g hl

theorem mat_phi_lt2 : ∀ g < 2, mat Dt (phi g) = Y (RG (g + 1)) := by
  intro g hg
  interval_cases g
  · simpa [phi] using mat_a
  · simpa [phi] using mat_b

theorem seedG_eq {z : Int} (h : imgLetK z ≠ badLet) :
    seedG Dt z.toNat = if (imgLetK z).2 then phi (imgLetK z).1 else (phi (imgLetK z).1)⁻¹ := by
  obtain ⟨-, hz, e⟩ := imgLetK_of_ne h
  rw [e]
  generalize z.toNat = n at hz ⊢
  interval_cases n <;> simp [seedG, phi]

theorem wordG_seedG (w : List Int) (h : ∀ z ∈ w, imgLetK z ≠ badLet) :
    CFSG.Sporadic.Th.wordG (fun z => seedG Dt z.toNat) w = wordProd phi (w.map imgLetK) := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    simp only [CFSG.Sporadic.Th.wordG, wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih fun z' hz' => h z' (List.mem_cons_of_mem _ hz'), seedG_eq (h z List.mem_cons_self)]

theorem ne_bad {R : List (List (Nat × Bool))} (hb : relsBounded R 5 = true) {v : List (Nat × Bool)}
    (hv : v ∈ R) {l : Nat × Bool} (hl : l ∈ v) : l ≠ badLet := by
  rintro rfl
  have := CFSG.KS.Ord.relsBounded_spec hb v hv _ hl
  exact absurd this (by decide)

theorem imgWords_getElem (k : ℕ) :
    CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.imgWords[k]! =
      CertificateChecks.KernelCosetJ.RuTabIT.W.getD k [] := by
  rw [img_eq, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    ← List.getD_eq_getElem?_getD, List.toList_toArray]
  rfl

theorem mat_img {k : ℕ} (hk : k < 3) :
    mat Dt (img CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt) k) = Y (RG (k + 3)) := by
  have hb := hom RI_bd RI_all RI_len
  set w := CertificateChecks.KernelCosetJ.RuTabIT.W.getD k [] with hw
  have hlen : CertificateChecks.KernelCosetJ.RuTabIT.W.length = 3 := by decide +kernel
  have hmem : ((k + 2, false) :: w.map imgLetK) ∈ RI := by
    rw [relsEqK_eq RI_bind, mkImgK_eq]
    exact List.mem_map.2 ⟨k, List.mem_range.2 (by omega), by rw [Nat.zero_add]⟩
  have hbad : ∀ z ∈ w, imgLetK z ≠ badLet := fun z hz =>
    ne_bad RI_bd hmem (List.mem_cons_of_mem _ (List.mem_map_of_mem hz))
  have hlt : ∀ l ∈ w.map imgLetK, l.1 < 2 := by
    intro l hl
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hl
    obtain ⟨-, hz4, e⟩ := imgLetK_of_ne (hbad z hz)
    rw [e]
    simp only
    omega
  have h1 := hb.2 _ hmem
  rw [List.map_cons, List.prod_cons] at h1
  have e : img CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt) k = wordProd phi (w.map imgLetK) := by
    rw [img, imgWords_getElem, ← hw, wordG_seedG w hbad]
  rw [e, mat_wordProd (by norm_num) mat_phi_lt2 _ hlt]
  have h2 : Y (letM RG 5 (k + 2, false)) = Y (RG (5 + 1 + (k + 2))) := rfl
  rw [h2] at h1
  calc (List.map (fun l => Y (letM RG 5 l)) (List.map imgLetK w)).prod
      = Y (RG (k + 2 + 1)) * (Y (RG (5 + 1 + (k + 2))) *
          (List.map (fun l => Y (letM RG 5 l)) (List.map imgLetK w)).prod) := by
        rw [← Matrix.mul_assoc, inv_reg (k + 2) (by omega), Matrix.one_mul]
    _ = Y (RG (k + 3)) := by rw [h1, Matrix.mul_one]

theorem mat_phi : ∀ g < 5, mat Dt (phi g) = Y (RG (g + 1)) := by
  intro g hg
  rcases Nat.lt_or_ge g 2 with h | h
  · exact mat_phi_lt2 g h
  · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
    rw [phi_img, mat_img (by omega)]

theorem wordProd_shift (w : List (Fin gc × Bool)) :
    wordProd (img CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt)) (w.map fun l => (l.1.val, l.2)) =
      wordProd phi (w.map fun l => (l.1.val + 2, l.2)) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, phi_img]

theorem fact : RuTabFact := by
  intro w hw
  have hv : (w.map fun l => (l.1.val + 2, l.2)) ∈ RT := by
    rw [RT_eq]
    exact List.mem_map_of_mem hw
  have e : FreeGroup.lift ruGen (FreeGroup.mk w) =
      wordProd (img CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt)) (w.map fun l => (l.1.val, l.2)) :=
    CFSG.LieType.Multipliers.lift_mk_eq_wordProd (img CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt)) w
  rw [e, wordProd_shift]
  apply mat_injective Dt
  rw [mat_one, mat_wordProd le_rfl mat_phi _ (CFSG.KS.Ord.relsBounded_spec RT_bd _ hv)]
  exact (hom RT_bd RT_all RT_len).2 _ hv

end CertificateChecks.KernelCosetJ.RuTab

end
