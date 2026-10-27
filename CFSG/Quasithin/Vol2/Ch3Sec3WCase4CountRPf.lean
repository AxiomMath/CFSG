module

public import CFSG.Quasithin.Background.C134Case4KappaM
public import CFSG.Quasithin.Vol2.Ch3Sec3Case4CountTools

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

theorem case4CorrA1Twist_holdsW :
    ∀ (G : Type) [Group G] [Finite G] (T M L D S : Subgroup G)
      (α : ↥L →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) (t₀ : G),
      L3321.RData G T M L D S α → (∃ _ : IsMulCommutative ↥(vPlus L T), Mod3321Sum T L) →
      t₀ ∈ T → t₀ ∉ S → (∀ x ∈ T, x ∈ S ∨ x * t₀⁻¹ ∈ S) →
      (∀ y ∈ liftCore α (FLc.QI 4 {1}), t₀ * y * t₀⁻¹ ∈ liftCore α (FLc.QI 4 {3})) →
      (∀ y ∈ liftCore α (FLc.QI 4 {3}), t₀⁻¹ * y * t₀ ∈ liftCore α (FLc.QI 4 {1})) →
      ¬ CFSG.Quasithin.C134Case4Min (liftCore α (FLc.QI 4 {1}) ⊔ S) S (liftCore α (FLc.QI 4 {1})) := by
  intro G _ _ T M L D S α t₀ hR _ ht₀ ht₀S hdich h13 h31 h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y₁ := liftCore α (FLc.QI 4 {1}) with hY₁
  set Y₃ := liftCore α (FLc.QI 4 {3}) with hY₃
  set A := qL L T with hA
  set P₁ := pCoreOf 2 (Y₁ ⊔ S) with hP₁
  set Q₁ := c134Q (Y₁ ⊔ S) Y₁ with hQ₁
  have hY₁L : Y₁ ≤ L := liftCore_le α _
  have hY₃L : Y₃ ≤ L := liftCore_le α _
  have hNbot : ∀ K : Subgroup G, K ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun _ =>
    Subgroup.le_normalizer_of_normal
  have hLTA : L ⊔ T ≤ Subgroup.normalizer (A : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hST : S ≤ T := hR.RT
  have hP₁2 : IsPGroup 2 ↥P₁ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hP₁le : P₁ ≤ Y₁ ⊔ S := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hYSN : Y₁ ⊔ S ≤ Subgroup.normalizer (P₁ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hY₁P : Y₁ ≤ Subgroup.normalizer (P₁ : Set G) := le_sup_left.trans hYSN
  have hYSLT : Y₁ ⊔ S ≤ L ⊔ T := sup_le_sup hY₁L hST
  have hAP₁ : A ≤ P₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hR.QR.trans le_sup_right)
      (hYSLT.trans hLTA) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hP₁NA : P₁ ≤ Subgroup.normalizer (A : Set G) := (hP₁le.trans hYSLT).trans hLTA
  have ht₀sq : t₀ * t₀ ∈ S := by
    rcases hdich _ (T.mul_mem ht₀ ht₀) with h1 | h1
    · exact h1
    · exact absurd (by simpa using h1) ht₀S
  have hTS : t₀ ∈ Subgroup.normalizer (S : Set G) := by
    refine OperatorJH.mem_normalizer_of_conj_mem_of fun s hs => ?_
    rcases hdich _ (T.mul_mem (T.mul_mem ht₀ (hST hs)) (T.inv_mem ht₀)) with h1 | h1
    · exact h1
    · exfalso
      apply ht₀S
      have e : t₀ = t₀ * s * t₀⁻¹ * t₀⁻¹ * (t₀ * t₀) * s⁻¹ := by group
      rw [e]
      exact S.mul_mem (S.mul_mem h1 ht₀sq) (S.inv_mem hs)
  have ht₀A : t₀ ∈ Subgroup.normalizer (A : Set G) := hLTA (Subgroup.mem_sup_right ht₀)
  have hconj : ∀ {X : Subgroup G}, t₀ ∈ Subgroup.normalizer (X : Set G) →
      X.map (MulAut.conj t₀).toMonoidHom = X := fun hX => by
    rw [MulEquiv.toMonoidHom_eq_coe]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hX
  have hY13 : Y₁.map (MulAut.conj t₀).toMonoidHom = Y₃ := by
    refine le_antisymm ?_ fun y hy => ⟨t₀⁻¹ * y * t₀, h31 y hy, by
      show t₀ * (t₀⁻¹ * y * t₀) * t₀⁻¹ = y
      group⟩
    rintro _ ⟨y, hy, rfl⟩
    exact h13 y hy
  obtain ⟨ψ, hψs, hψk, -⟩ := hR.exists_levi_one
  have hα₂ : IsModO2Surj Y₁ ((specialLinearGroupEquivStatedSL 3 (ZMod 2)).toMonoidHom.comp ψ) := by
    refine ⟨?_, ?_⟩
    · rw [MonoidHom.coe_comp]
      exact (MulEquiv.surjective _).comp hψs
    · rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _), hψk]
  have key₁ : ∀ y ∈ Y₁, y ^ 7 = 1 → y ≠ 1 → kappa false y ⊥ P₁ = kappa true y ⊥ P₁ := by
    intro y hy hy7 hy1
    have hyP : y ∈ Subgroup.normalizer (P₁ : Set G) := hY₁P hy
    have hyQ : y ∈ Subgroup.normalizer (Q₁ : Set G) :=
      C134Case4Kappa.mem_normalizer_commutator hyP (Subgroup.le_normalizer hy)
    have hQP : Q₁ ≤ P₁ := by
      rw [hQ₁, c134Q, Subgroup.commutator_le]
      intro p hp z hz
      have e : ⁅p, z⁆ = p * (z * p⁻¹ * z⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact P₁.mul_mem hp ((Subgroup.mem_normalizer_iff.mp (hY₁P hz) _).mp (P₁.inv_mem hp))
    have hPQ : P₁ ≤ Subgroup.normalizer (Q₁ : Set G) := fun p hp =>
      C134Case4Kappa.mem_normalizer_commutator (Subgroup.le_normalizer hp)
        ((hP₁le.trans (sup_le Subgroup.le_normalizer (hR.le_normalizer_Y {1}))) hp)
    have hfix : Fixes y Q₁ P₁ := by
      intro p hp
      have e : y * p * y⁻¹ * p⁻¹ = ⁅p, y⁆⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Q₁.inv_mem (Subgroup.commutator_mem_commutator hp hy)
    have hyB : y ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := hNbot ⊤ (Subgroup.mem_top y)
    have hsplit : ∀ b : Bool, kappa b y ⊥ P₁ = kappa b y ⊥ Q₁ * kappa b y Q₁ P₁ := fun b =>
      kappa_trans bot_le hQP (hNbot _) hPQ hyB hyQ hyP b
    rw [hsplit, hsplit, kappa_eq_one_of_fixes hQP hPQ hyQ hyP hP₁2 hfix,
      kappa_eq_one_of_fixes hQP hPQ hyQ hyP hP₁2 hfix,
      C134Case4Kappa.kappa_eq_of_case4CorrW h4 hα₂ hY₁P hy hy7 hy1]
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
  have hh'Y : t₀⁻¹ * h * t₀ ∈ Y₁ := h31 h hhY
  have hh'7 : (t₀⁻¹ * h * t₀) ^ 7 = 1 := by
    have e : t₀⁻¹ * h * t₀ = t₀⁻¹ * h * t₀⁻¹⁻¹ := by rw [inv_inv]
    rw [e, conj_pow, hh7, mul_one, mul_inv_cancel]
  have hh'1 : t₀⁻¹ * h * t₀ ≠ 1 := fun h1 => hh1 (by
    have e : h = t₀ * (t₀⁻¹ * h * t₀) * t₀⁻¹ := by group
    rw [e, h1, mul_one, mul_inv_cancel])
  set P₃ := P₁.map (MulAut.conj t₀).toMonoidHom with hP₃
  have key₃ : kappa false h ⊥ P₃ = kappa true h ⊥ P₃ := by
    have hc := fun b : Bool => kappa_conj t₀ b (t₀⁻¹ * h * t₀) (C := ⊥) (D := P₁) bot_le (hNbot _)
      (hNbot ⊤ (Subgroup.mem_top _)) (hY₁P hh'Y)
    have e : t₀ * (t₀⁻¹ * h * t₀) * t₀⁻¹ = h := by group
    simp only [e, Subgroup.map_bot] at hc
    rw [hc false, hc true]
    exact key₁ _ hh'Y hh'7 hh'1
  have hAP₃ : A ≤ P₃ := by
    rw [← hconj ht₀A]
    exact Subgroup.map_mono hAP₁
  have hP₃le : P₃ ≤ Y₃ ⊔ S := by
    refine (Subgroup.map_mono hP₁le).trans ?_
    rw [Subgroup.map_sup, hY13, hconj hTS]
  have hY₃P : Y₃ ≤ Subgroup.normalizer (P₃ : Set G) := by
    rw [← hY13, hP₃, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hY₁P
  have hP₃2 : IsPGroup 2 ↥P₃ := hP₁2.map _
  have hP₃NA : P₃ ≤ Subgroup.normalizer (A : Set G) :=
    (hP₃le.trans (sup_le_sup hY₃L hST)).trans hLTA
  have hk₁ : Kills true g A P₁ := kills_rad1 hR hAP₁ hP₁le hY₁P hP₁2 hgL hgα
  have hk₃ : Kills false h A P₃ := kills_rad3 hR hAP₃ hP₃le hY₃P hP₃2 hhL hhα
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
  have E1 := key₁ g hgY hg7 hg1
  rw [sg, sg, r1f, r1t, mul_one] at E1
  have E2 := key₃
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
  have hQ8 : 8 * Nat.card ↥(Q₁ ⊓ pCoreOf 2 L) ≤ Nat.card ↥Q₁ := hR.card_Q_ge_one
  have hQP : Q₁ ≤ P₁ := by
    rw [hQ₁, c134Q, Subgroup.commutator_le]
    intro p hp z hz
    have e : ⁅p, z⁆ = p * (z * p⁻¹ * z⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact P₁.mul_mem hp ((Subgroup.mem_normalizer_iff.mp (hY₁P hz) _).mp (P₁.inv_mem hp))
  have hQL : Q₁ ≤ L := (L3321.FData.Q_le_Y (hR.le_normalizer_Y {1})).trans hY₁L
  have hAL : A ⊓ L ≤ pCoreOf 2 L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun l hl => ?_)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_inf_left
    exact OperatorJH.mem_normalizer_inf_of (hLTA (Subgroup.mem_sup_left hl))
      (Subgroup.le_normalizer hl)
  have hQO : Q₁ ⊓ pCoreOf 2 L = Q₁ :=
    inf_eq_left.mpr fun q hq => hAL ⟨hPA (hQP hq), hQL hq⟩
  rw [hQO] at hQ8
  have hpos : 0 < Nat.card ↥Q₁ := Nat.card_pos
  omega

end CFSG.Quasithin.H13.Case4Count
