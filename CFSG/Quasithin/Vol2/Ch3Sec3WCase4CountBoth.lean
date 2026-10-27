module

public import CFSG.Quasithin.Vol2.Ch3Sec3Case4CountBoth
public import CFSG.Quasithin.Background.C134Case4KappaM

public section

namespace CFSG.Quasithin.H13.Case4Count

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq)
open CFSG.Quasithin.H13.L3321 (RData SL4)
open CFSG.Quasithin.CubicCount CFSG.Quasithin.SevenL4Model
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Data

variable {T L R : Subgroup G} {α : ↥L →* SL4}

theorem kappa_eq_of_case4W {Y : Subgroup G} (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    {α₂ : ↥Y →* ↥(StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj Y α₂)
    (h4 : CFSG.Quasithin.C134Case4Min (Y ⊔ R) R Y) {y : G} (hy : y ∈ Y) (hy7 : y ^ 7 = 1)
    (hy1 : y ≠ 1) :
    kappa false y ⊥ (pCoreOf 2 (Y ⊔ R)) = kappa true y ⊥ (pCoreOf 2 (Y ⊔ R)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 (Y ⊔ R) with hP
  set Q := c134Q (Y ⊔ R) Y with hQ
  have hNbot : ∀ K : Subgroup G, K ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun _ =>
    Subgroup.le_normalizer_of_normal
  have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hPle : P ≤ Y ⊔ R := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hQP : Q ≤ P := by
    rw [hQ, c134Q, Subgroup.commutator_le]
    intro p hp z hz
    have e : ⁅p, z⁆ = p * (z * p⁻¹ * z⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact P.mul_mem hp ((Subgroup.mem_normalizer_iff.mp (hYP hz) _).mp (P.inv_mem hp))
  have hyP : y ∈ Subgroup.normalizer (P : Set G) := hYP hy
  have hyQ : y ∈ Subgroup.normalizer (Q : Set G) :=
    C134Case4Kappa.mem_normalizer_commutator hyP (Subgroup.le_normalizer hy)
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := fun p hp =>
    C134Case4Kappa.mem_normalizer_commutator (Subgroup.le_normalizer hp)
      ((hPle.trans (sup_le Subgroup.le_normalizer hRY)) hp)
  have hfix : Fixes y Q P := by
    intro p hp
    have e : y * p * y⁻¹ * p⁻¹ = ⁅p, y⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Q.inv_mem (Subgroup.commutator_mem_commutator hp hy)
  have hyB : y ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := hNbot ⊤ (Subgroup.mem_top y)
  have hsplit : ∀ b : Bool, kappa b y ⊥ P = kappa b y ⊥ Q * kappa b y Q P := fun b =>
    kappa_trans bot_le hQP (hNbot _) hPQ hyB hyQ hyP b
  rw [hsplit, hsplit, kappa_eq_one_of_fixes hQP hPQ hyQ hyP hP2 hfix,
    kappa_eq_one_of_fixes hQP hPQ hyQ hyP hP2 hfix,
    C134Case4Kappa.kappa_eq_of_case4CorrW h4 hα₂ hYP hy hy7 hy1]

theorem not_case4Corr_bothW (hR : Data G T L R α)
    (h4₁ : CFSG.Quasithin.C134Case4Min (liftCore α (FLc.QI 4 {1}) ⊔ R) R
      (liftCore α (FLc.QI 4 {1})))
    (h4₃ : CFSG.Quasithin.C134Case4Min (liftCore α (FLc.QI 4 {3}) ⊔ R) R
      (liftCore α (FLc.QI 4 {3}))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y₁ := liftCore α (FLc.QI 4 {1}) with hY₁
  set Y₃ := liftCore α (FLc.QI 4 {3}) with hY₃
  set A := qL L T with hA
  set P₁ := pCoreOf 2 (Y₁ ⊔ R) with hP₁
  set P₃ := pCoreOf 2 (Y₃ ⊔ R) with hP₃
  set Q₁ := c134Q (Y₁ ⊔ R) Y₁ with hQ₁
  have hY₁L : Y₁ ≤ L := liftCore_le α _
  have hY₃L : Y₃ ≤ L := liftCore_le α _
  have hNbot : ∀ K : Subgroup G, K ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun _ =>
    Subgroup.le_normalizer_of_normal
  have hLTA : L ⊔ T ≤ Subgroup.normalizer (A : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hA2 : IsPGroup 2 ↥A := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hsetup : ∀ {Y : Subgroup G}, Y ≤ L →
      A ≤ pCoreOf 2 (Y ⊔ R) ∧ pCoreOf 2 (Y ⊔ R) ≤ Y ⊔ R ∧
        Y ≤ Subgroup.normalizer (pCoreOf 2 (Y ⊔ R) : Set G) ∧
          IsPGroup 2 ↥(pCoreOf 2 (Y ⊔ R)) ∧
            pCoreOf 2 (Y ⊔ R) ≤ Subgroup.normalizer (A : Set G) := by
    intro Y hYL
    have hYRLT : Y ⊔ R ≤ L ⊔ T := sup_le_sup hYL hR.RT
    exact ⟨CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hR.QR.trans le_sup_right)
        (hYRLT.trans hLTA) hA2, CFSG.LieType.BorelTits.pCoreOf_le 2 _,
      le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _),
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _,
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hYRLT).trans hLTA⟩
  obtain ⟨hAP₁, hP₁le, hY₁P, hP₁2, hP₁NA⟩ := hsetup hY₁L
  obtain ⟨hAP₃, hP₃le, hY₃P, hP₃2, hP₃NA⟩ := hsetup hY₃L
  obtain ⟨α₁, hα₁⟩ := hR.exists_modO2_one
  obtain ⟨α₃, hα₃⟩ := hR.exists_modO2_three
  obtain ⟨g, hgY, hgL, hgα, hg7⟩ := exists_x1 hR.surj hR.ker
  have hg1 : g ≠ 1 := fun h1 => by
    have e : (⟨g, hgL⟩ : ↥L) = 1 := Subtype.ext h1
    rw [e, map_one] at hgα
    exact x1_ne_one hgα.symm
  obtain ⟨k, hk⟩ := hR.surj k0
  have hhL : (k : G) * g * (k : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem k.2 hgL) (L.inv_mem k.2)
  have hhα : α ⟨(k : G) * g * (k : G)⁻¹, hhL⟩ = x3 := by
    have e : (⟨(k : G) * g * (k : G)⁻¹, hhL⟩ : ↥L) = k * ⟨g, hgL⟩ * k⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hk, hgα, k0_conj_x1]
  have hh7 : ((k : G) * g * (k : G)⁻¹) ^ 7 = 1 := by
    rw [conj_pow, hg7, mul_one, mul_inv_cancel]
  have hhY : (k : G) * g * (k : G)⁻¹ ∈ Y₃ :=
    mem_liftCore_of_pow_seven hR.surj hR.ker hhL (by rw [hhα]; exact x3_mem_perfectCore) hh7
  set h := (k : G) * g * (k : G)⁻¹ with hhdef
  have hh1 : h ≠ 1 := fun h1 => by
    have e : (⟨h, hhL⟩ : ↥L) = 1 := Subtype.ext h1
    rw [e, map_one] at hhα
    exact x3_ne_one hhα.symm
  have E1 : kappa false g ⊥ P₁ = kappa true g ⊥ P₁ :=
    kappa_eq_of_case4W hR.RY1 hα₁ h4₁ hgY hg7 hg1
  have E2 : kappa false h ⊥ P₃ = kappa true h ⊥ P₃ :=
    kappa_eq_of_case4W hR.RY3 hα₃ h4₃ hhY hh7 hh1
  have hk₁ : Kills true g A P₁ := hR.kills_rad1 hAP₁ hP₁le hY₁P hP₁2 hgL hgα
  have hk₃ : Kills false h A P₃ := hR.kills_rad3 hAP₃ hP₃le hY₃P hP₃2 hhL hhα
  have hgA : g ∈ Subgroup.normalizer (A : Set G) := hLTA (Subgroup.mem_sup_left hgL)
  have hhA : h ∈ Subgroup.normalizer (A : Set G) := hLTA (Subgroup.mem_sup_left hhL)
  have hgP : g ∈ Subgroup.normalizer (P₁ : Set G) := hY₁P hgY
  have hhP : h ∈ Subgroup.normalizer (P₃ : Set G) := hY₃P hhY
  have hgB : g ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := hNbot ⊤ (Subgroup.mem_top g)
  have hhB : h ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := hNbot ⊤ (Subgroup.mem_top h)
  have sg : ∀ b : Bool, kappa b g ⊥ P₁ = kappa b g ⊥ A * kappa b g A P₁ := fun b =>
    kappa_trans bot_le hAP₁ (hNbot _) hP₁NA hgB hgA hgP b
  have sh : ∀ b : Bool, kappa b h ⊥ P₃ = kappa b h ⊥ A * kappa b h A P₃ := fun b =>
    kappa_trans bot_le hAP₃ (hNbot _) hP₃NA hhB hhA hhP b
  have hgh : ∀ b : Bool, kappa b h ⊥ A = kappa b g ⊥ A := fun b =>
    kappa_conj_of_mem b g bot_le (hNbot _) hgB hgA (hNbot ⊤ (Subgroup.mem_top _))
      (hLTA (Subgroup.mem_sup_left k.2))
  have r1f : kappa false g A P₁ = 1 := kappa_eq_one_of_kills hAP₁ hP₁NA hgA hgP hP₁2 hk₁
  have r1t : kappa true g A P₁ = A.relIndex P₁ := kappa_of_kills hAP₁ hP₁NA hgA hgP hk₁
  have r3f : kappa false h A P₃ = A.relIndex P₃ := kappa_of_kills hAP₃ hP₃NA hhA hhP hk₃
  have r3t : kappa true h A P₃ = 1 := kappa_eq_one_of_kills hAP₃ hP₃NA hhA hhP hP₃2 hk₃
  rw [sg, sg, r1f, r1t, mul_one] at E1
  rw [sh, sh, r3f, r3t, mul_one, hgh, hgh] at E2
  have hat := kappa_ne_zero true g ⊥ A
  have hm : A.relIndex P₁ * A.relIndex P₃ = 1 := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hat) ?_
    calc kappa true g ⊥ A * (A.relIndex P₁ * A.relIndex P₃)
        = kappa true g ⊥ A * A.relIndex P₁ * A.relIndex P₃ := by ring
      _ = kappa false g ⊥ A * A.relIndex P₃ := by rw [E1]
      _ = kappa true g ⊥ A := E2
      _ = kappa true g ⊥ A * 1 := by ring
  have hm1 : A.relIndex P₁ = 1 := Nat.eq_one_of_mul_eq_one_right hm
  have hPA : P₁ ≤ A := Subgroup.relIndex_eq_one.mp hm1
  have hQP : Q₁ ≤ P₁ := by
    rw [hQ₁, c134Q, Subgroup.commutator_le]
    intro p hp z hz
    have e : ⁅p, z⁆ = p * (z * p⁻¹ * z⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact P₁.mul_mem hp ((Subgroup.mem_normalizer_iff.mp (hY₁P hz) _).mp (P₁.inv_mem hp))
  have hQ8 : 8 * Nat.card ↥(Q₁ ⊓ pCoreOf 2 L) ≤ Nat.card ↥Q₁ := hR.card_Q_ge_one
  have hQL : Q₁ ≤ L := (L3321.FData.Q_le_Y hR.RY1).trans hY₁L
  have hAL : A ⊓ L ≤ pCoreOf 2 L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun l hl => ?_)
      hA2.to_inf_left
    exact OperatorJH.mem_normalizer_inf_of (hLTA (Subgroup.mem_sup_left hl))
      (Subgroup.le_normalizer hl)
  have hQO : Q₁ ⊓ pCoreOf 2 L = Q₁ :=
    inf_eq_left.mpr fun q hq => hAL ⟨hPA (hQP hq), hQL hq⟩
  rw [hQO] at hQ8
  have hpos : 0 < Nat.card ↥Q₁ := Nat.card_pos
  omega


end Data

end CFSG.Quasithin.H13.Case4Count
