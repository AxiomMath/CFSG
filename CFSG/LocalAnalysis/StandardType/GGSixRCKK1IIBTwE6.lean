module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBPair
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongTwE6Datum
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Rad
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots
public import CFSG.LieType.Steinberg.TwistedE6.Local
public import CFSG.LieType.Steinberg.TwistedE6.Datum
public import CFSG.LieType.Steinberg.TwistedE6.Generation
public import CFSG.LieType.Steinberg.TwistedE6.Weyl
public import CFSG.LieType.HighestRoot.Gen
public import CFSG.LieType.HighestRoot.GenBasic
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.GH74.Generic.BProg.B3.S3Sec29H
public import CFSG.GH74.GLS.C3.Layer1.Th2Pump

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.Open
open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Chevalley
open CFSG.LieType.HighestRoot CFSG.SeitzReduction CFSG.SeitzReduction.F4Pilot
  CFSG.LieType.Steinberg.Adjoint
open CFSG.StandardType.LieKnownR2.Short CFSG.ClassicalInvolution.ModelFacts
open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

private theorem rckp5_mem_zpowers_invol {G : Type} [Group G] {v h : G} (hv : v * v = 1)
    (hh : h ∈ Subgroup.zpowers v) : h = 1 ∨ h = v := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  have hv2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hv
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · left; rw [zpow_mul, hv2, one_zpow]
  · right; rw [zpow_add, zpow_mul, hv2, one_zpow, one_mul, zpow_one]

private theorem rckp5_comm_of_mem_zpowers {G : Type} [Group G] {v₁ v₂ : G}
    (h₁ : v₁ * v₁ = 1) (h₁₂ : v₁ * v₂ = v₂ * v₁) :
    ∀ h ∈ Subgroup.zpowers v₁, h * v₂ = v₂ * h := by
  intro h hh
  rcases rckp5_mem_zpowers_invol h₁ hh with rfl | rfl
  · simp
  · exact h₁₂

private theorem rckp5_mem_four {G : Type} [Group G] {v₁ v₂ g : G}
    (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1) (h₁₂ : v₁ * v₂ = v₂ * v₁)
    (hg : g ∈ Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂) :
    g = 1 ∨ g = v₁ ∨ g = v₂ ∨ g = v₁ * v₂ := by
  obtain ⟨h, hh, rfl | rfl⟩ :=
    CFSG.GH74.Generic.BProg.B3.S3Sec29H.mem_sup_zpowers h₂
      (rckp5_comm_of_mem_zpowers h₁ h₁₂) hg
  · rcases rckp5_mem_zpowers_invol h₁ hh with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases rckp5_mem_zpowers_invol h₁ hh with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (by simp)))
    · exact Or.inr (Or.inr (Or.inr rfl))

private theorem rckp5_isElemAbelian_four {G : Type} [Group G] {v₁ v₂ : G}
    (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1) (h₁₂ : v₁ * v₂ = v₂ * v₁) :
    IsElemAbelian 2 (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂) := by
  have hEA : CFSG.IsElementaryAbelian 2 ↥(Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂) :=
    CFSG.GH74.Generic.BProg.B3.S3Sec29H.isElementaryAbelian_sup_zpowers
      (CFSG.GH74.Generic.BProg.B3.S3Sec29H.isElementaryAbelian_zpowers h₁) h₂
      (rckp5_comm_of_mem_zpowers h₁ h₁₂)
  haveI := hEA
  exact ⟨hEA.toIsMulCommutative, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩

private theorem rckp5_card_four {G : Type} [Group G] {v₁ v₂ : G}
    (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1) (h₁₂ : v₁ * v₂ = v₂ * v₁)
    (h₁1 : v₁ ≠ 1) (h₂1 : v₂ ≠ 1) (hne : v₁ ≠ v₂) :
    Nat.card ↥(Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂) = 4 := by
  have hnot : v₂ ∉ Subgroup.zpowers v₁ := by
    intro h
    rcases rckp5_mem_zpowers_invol h₁ h with h0 | h0
    · exact h₂1 h0
    · exact hne h0.symm
  have hord : orderOf v₁ = 2 := orderOf_eq_prime (by rw [sq]; exact h₁) h₁1
  rw [show Nat.card ↥(Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂) =
      2 * Nat.card ↥(Subgroup.zpowers v₁) from
        CFSG.GH74.Generic.BProg.B3.S3Sec29H.card_sup_zpowers
          (H := Subgroup.zpowers v₁) h₂ hnot (rckp5_comm_of_mem_zpowers h₁ h₁₂),
    Nat.card_zpowers, hord]

private theorem rckp5_conj_eq_commutator_mul {G : Type*} [Group G] (a b : G) :
    a * b * a⁻¹ = ⁅a, b⁆ * b := by
  rw [commutatorElement_def]; group

private theorem rckp5_coe_commutator {G : Type*} [Group G] (H : Subgroup G) (x y : H) :
    ((⁅x, y⁆ : H) : G) = ⁅(x : G), (y : G)⁆ := by
  change (H.subtype (⁅x, y⁆) : G) = ⁅(x : G), (y : G)⁆
  rw [map_commutatorElement H.subtype]
  simp only [Subgroup.subtype_apply]

private abbrev rckp5_zeroF4 : Fin (Tag.rank .F4) := ⟨0, by decide⟩

private abbrev rckp5_gamma : Fin (Tag.rank .F4) → ℤ := ![1, 3, 4, 2]

private abbrev rckp5_aGamma : Fin (Tag.rank .E6) → ℤ := ![1, 1, 2, 3, 2, 1]

private abbrev rckp5_aZ : Fin (Tag.rank .E6) → ℤ := ![0, -1, 0, 0, 0, 0]

private theorem rckp5_height_le_rootR :
    ∀ δ ∈ rootFinset .F4, (∑ i, δ i) ≤ ∑ i, (![2, 3, 4, 2] : Fin 4 → ℤ) i := by
  decide +kernel

private theorem rckp5_commSign_eq_one
    (α β : Fin (Tag.rank .E6) → ℤ) :
    ((e6Data_valid.commSign (GaloisField 2 2) α β : ℤ) : GaloisField 2 2) = 1 := by
  rcases e6Data_valid.commSign_eq_one_or (GaloisField 2 2) α β with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num
    exact CharTwo.neg_eq 1

private theorem rckp5_frobQ_fixed_eq
    (c : GaloisField 2 2) (hc : frobQ 2 1 c = c) : c = 0 ∨ c = 1 := by
  have h : c ^ (2 ^ 1) = c := (frobQ_apply 2 1 c).symm.trans hc
  rw [show (2 : ℕ) ^ 1 = 2 from rfl, pow_two] at h
  have hmul : c * (c - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp hmul with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

private theorem rckp5_rootGroup_eq_pair
    {k : Type*} [Field k] (θ : k →+* k) (hfixeds : ∀ c, θ c = c → c = 0 ∨ c = 1)
    {β : Fin (Tag.rank .F4) → ℤ} {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (hproj : proj α = β) (hfix : rho α = α) :
    (twistedRootGroup k θ β : Set (fixedGroup k θ)) =
      {1, xFixed θ hα hfix 1 (map_one θ)} := by
  ext g
  constructor
  · intro hg
    obtain ⟨c, hc, hgval⟩ :=
      (mem_twistedRootGroup_iff_of_fixed θ hα hproj hfix g).1 hg
    rcases hfixeds c hc with rfl | rfl
    · left; apply Subtype.ext; rw [hgval, e6Data_valid.xm_zero]; rfl
    · right; apply Subtype.ext; rw [hgval, xFixed_val]
  · rintro (rfl | rfl)
    · exact one_mem _
    · rw [← hproj]
      exact xFixed_mem θ hα hfix 1 (map_one θ)

private theorem rckp5_cartan_mul_highRoot_F4_rat (l : Fin (Tag.rank .F4)) :
    ∑ k, (Tag.cartan .F4 l k : ℚ) * (highRoot .F4 k : ℚ) =
      if l = rckp5_zeroF4 then 1 else 0 := by
  fin_cases l <;> decide +kernel

private theorem rckp5_form_highRoot_F4
    (hA : TauCeti.IsFiniteType (Tag.cartan .F4)) (x : Fin (Tag.rank .F4) → ℚ) :
    form hA x (toRat (highRoot .F4)) = symmetrizer hA rckp5_zeroF4 * x rckp5_zeroF4 := by
  calc form hA x (toRat (highRoot .F4))
      = form hA (toRat (highRoot .F4)) x := form_comm hA x _
    _ = ∑ l, x l * form hA (toRat (highRoot .F4)) (Pi.single l 1) := form_eq_sum hA _ _
    _ = x rckp5_zeroF4 * form hA (toRat (highRoot .F4)) (Pi.single rckp5_zeroF4 1) :=
          Finset.sum_eq_single_of_mem rckp5_zeroF4 (Finset.mem_univ rckp5_zeroF4)
            fun l _ hl => by
              rw [form_single_right]
              simp only [toRat_apply]
              rw [rckp5_cartan_mul_highRoot_F4_rat, if_neg hl, mul_zero, mul_zero]
    _ = symmetrizer hA rckp5_zeroF4 * x rckp5_zeroF4 := by
          rw [form_single_right]
          simp only [toRat_apply]
          rw [rckp5_cartan_mul_highRoot_F4_rat, if_pos rfl, mul_one]
          ring

private theorem rckp5_rootForm_highRoot_pos
    {k : Type*} [Field k] (θ : k →+* k) (γ : Fin (Tag.rank .F4) → ℤ)
    (hγ0 : 0 < γ rckp5_zeroF4) :
    0 < rootForm (twistedDatum k θ) γ (highRoot .F4) := by
  have hform : rootForm (twistedDatum k θ) γ (highRoot .F4) =
      (symmetrizer (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) rckp5_zeroF4 : ℚ) *
        (γ rckp5_zeroF4 : ℚ) := by
    change form (twistedDatum k θ).isFiniteType (toRat γ) (toRat (highRoot .F4)) = _
    change form (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) (toRat γ)
      (toRat (highRoot .F4)) = _
    rw [rckp5_form_highRoot_F4 (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) (toRat γ)]
    simp only [toRat_apply]
  rw [hform]
  exact mul_pos
    (by exact_mod_cast symmetrizer_pos (isFiniteType_cartan .F4) rckp5_zeroF4)
    (by exact_mod_cast hγ0)

private theorem rckp5_isIrreducible_cartan_F4 :
    IsIrreducible (Tag.cartan .F4) := by
  refine isIrreducible_of_parent (0 : Fin 4) (![0, 0, 1, 2] : Fin 4 → Fin 4) (fun j => j.val) ?_
  intro j hj
  fin_cases j
  · exact (hj rfl).elim
  · decide
  · decide
  · decide

theorem rckIIPair_TwE6
    (n : ℕ) (hadm : StatedLieAdmissible .twistedE6 n 2 1) : RCKIIPair .twistedE6 n := by
  classical
  unfold RCKIIPair
  simp only [ggU, lieUniversal]
  let θ : GaloisField 2 2 →+* GaloisField 2 2 := frobQ 2 1
  have hθf : ∀ c, θ c = c → c = 0 ∨ c = 1 := fun c hc => rckp5_frobQ_fixed_eq c hc
  have hθ : ∀ c, θ (θ c) = c := fun c => frobQ_frobQ 2 1 (by omega) c
  have htop : ⨆ β ∈ (twistedDatum (GaloisField 2 2) θ).roots,
      (twistedDatum (GaloisField 2 2) θ).rootGroup β = ⊤ :=
    iSup_twistedDatum_rootGroup θ hθ
  have hct := twistedDatum_isCTGroupDatum θ hθ htop
  have hext := twistedDatum_steinbergExtras θ hθ
  have hβmem : (highRoot .F4 : Fin (Tag.rank .F4) → ℤ) ∈
      (twistedDatum (GaloisField 2 2) θ).roots := by
    rw [twistedDatum_roots]; exact isRoot_highRoot .F4
  have hβlong : GGLongRoot (twistedDatum (GaloisField 2 2) θ)
      (highRoot .F4 : Fin (Tag.rank .F4) → ℤ) := by
    refine ⟨1, highRoot .F4, hβmem, ?_, ?_⟩
    · intro δ hδ
      rw [twistedDatum_roots] at hδ
      exact rckp5_height_le_rootR δ (mem_rootFinset.2 hδ)
    · show (highRoot .F4 : Fin (Tag.rank .F4) → ℤ) =
        weylAction (twistedDatum (GaloisField 2 2) θ).isFiniteType 1 (highRoot .F4)
      rw [map_one]; rfl
  have hαθ : IsRoot .E6 (highRoot .E6) := isRoot_highRoot .E6
  have hfixαθ : rho (highRoot .E6) = highRoot .E6 := by decide +kernel
  have hαγ : IsRoot .E6 rckp5_aGamma := mem_rootFinset.1 (by decide +kernel)
  have hfixαγ : rho rckp5_aGamma = rckp5_aGamma := by decide +kernel
  have hαz : IsRoot .E6 rckp5_aZ := mem_rootFinset.1 (by decide +kernel)
  have hfixαz : rho rckp5_aZ = rckp5_aZ := by decide +kernel
  have hprojθ : proj (highRoot .E6) = (highRoot .F4 : Fin (Tag.rank .F4) → ℤ) := by
    decide +kernel
  have hprojαγ : proj rckp5_aGamma = rckp5_gamma := by decide +kernel
  have hsum : rckp5_aZ + highRoot .E6 = rckp5_aGamma := by decide +kernel
  have hne_sum : rckp5_aZ + highRoot .E6 ≠ 0 := by decide
  have hroot_sum : IsRoot .E6 (rckp5_aZ + highRoot .E6) := by rw [hsum]; exact hαγ
  let x : fixedGroup (GaloisField 2 2) θ := xFixed θ hαθ hfixαθ 1 (map_one θ)
  let y : fixedGroup (GaloisField 2 2) θ := xFixed θ hαγ hfixαγ 1 (map_one θ)
  let z : fixedGroup (GaloisField 2 2) θ := xFixed θ hαz hfixαz 1 (map_one θ)
  have hxval : (x : e6Data_valid.minGroup (GaloisField 2 2)) =
      e6Data_valid.xm (GaloisField 2 2) (highRoot .E6) 1 := xFixed_val θ hαθ hfixαθ 1 (map_one θ)
  have hyval : (y : e6Data_valid.minGroup (GaloisField 2 2)) =
      e6Data_valid.xm (GaloisField 2 2) rckp5_aGamma 1 := xFixed_val θ hαγ hfixαγ 1 (map_one θ)
  have hzval : (z : e6Data_valid.minGroup (GaloisField 2 2)) =
      e6Data_valid.xm (GaloisField 2 2) rckp5_aZ 1 := xFixed_val θ hαz hfixαz 1 (map_one θ)
  have hXβ : (twistedRootGroup (GaloisField 2 2) θ (highRoot .F4) :
      Set (fixedGroup (GaloisField 2 2) θ)) = {1, x} :=
    rckp5_rootGroup_eq_pair θ hθf hαθ hprojθ hfixαθ
  have hXγ : (twistedRootGroup (GaloisField 2 2) θ rckp5_gamma :
      Set (fixedGroup (GaloisField 2 2) θ)) = {1, y} :=
    rckp5_rootGroup_eq_pair θ hθf hαγ hprojαγ hfixαγ
  have hxmem : x ∈ twistedRootGroup (GaloisField 2 2) θ (highRoot .F4) :=
    (Set.ext_iff.mp hXβ x).mpr (Or.inr rfl)
  have hymem : y ∈ twistedRootGroup (GaloisField 2 2) θ rckp5_gamma :=
    (Set.ext_iff.mp hXγ y).mpr (Or.inr rfl)
  have hx2 : x * x = 1 := by
    apply Subtype.ext
    change (x : e6Data_valid.minGroup (GaloisField 2 2)) *
      (x : e6Data_valid.minGroup (GaloisField 2 2)) = 1
    rw [hxval, ← e6Data_valid.xm_add]
    rw [show (1 : GaloisField 2 2) + 1 = 0 by exact CharTwo.add_self_eq_zero 1,
      e6Data_valid.xm_zero]
  have hy2 : y * y = 1 := by
    apply Subtype.ext
    change (y : e6Data_valid.minGroup (GaloisField 2 2)) *
      (y : e6Data_valid.minGroup (GaloisField 2 2)) = 1
    rw [hyval, ← e6Data_valid.xm_add]
    rw [show (1 : GaloisField 2 2) + 1 = 0 by exact CharTwo.add_self_eq_zero 1,
      e6Data_valid.xm_zero]
  have hx1 : x ≠ 1 := by
    intro h
    have h1 : (x : e6Data_valid.minGroup (GaloisField 2 2)) = 1 := congrArg Subtype.val h
    rw [hxval] at h1
    have h3 : e6Data_valid.xm (GaloisField 2 2) (highRoot .E6) 1 =
        e6Data_valid.xm (GaloisField 2 2) (highRoot .E6) 0 := by
      rw [h1, e6Data_valid.xm_zero]
    exact one_ne_zero (e6Data_valid.xm_injective (GaloisField 2 2) hαθ h3)
  have hy1 : y ≠ 1 := by
    intro h
    have h1 : (y : e6Data_valid.minGroup (GaloisField 2 2)) = 1 := congrArg Subtype.val h
    rw [hyval] at h1
    have h3 : e6Data_valid.xm (GaloisField 2 2) rckp5_aGamma 1 =
        e6Data_valid.xm (GaloisField 2 2) rckp5_aGamma 0 := by
      rw [h1, e6Data_valid.xm_zero]
    exact one_ne_zero (e6Data_valid.xm_injective (GaloisField 2 2) hαγ h3)
  have hxy : x * y = y * x := by
    apply Subtype.ext
    change (x : e6Data_valid.minGroup (GaloisField 2 2)) *
      (y : e6Data_valid.minGroup (GaloisField 2 2)) =
      (y : e6Data_valid.minGroup (GaloisField 2 2)) *
        (x : e6Data_valid.minGroup (GaloisField 2 2))
    rw [hxval, hyval]
    refine commutatorElement_eq_one_iff_mul_comm.mp
      ((e6Data_valid.commutator_xm (GaloisField 2 2) hαθ hαγ ?_).2 ?_ 1 1)
    · decide
    · rw [← mem_rootFinset]; decide +kernel
  have hXβneγ : (twistedRootGroup (GaloisField 2 2) θ (highRoot .F4) :
      Subgroup (fixedGroup (GaloisField 2 2) θ)) ≠
      twistedRootGroup (GaloisField 2 2) θ rckp5_gamma := by
    intro heq
    obtain ⟨w', hw'⟩ := exists_smul_eq_rootR (γ := (rckp5_gamma : Fin (Tag.rank .F4) → ℤ))
      (by rw [← mem_rootFinset]; decide +kernel)
      (show iform (rckp5_gamma : Fin (Tag.rank .F4) → ℤ) rckp5_gamma = 4 by decide +kernel)
    have hwβ : weylAction (twistedDatum (GaloisField 2 2) θ).isFiniteType w'⁻¹
        (highRoot .F4 : Fin (Tag.rank .F4) → ℤ) = rckp5_gamma := by
      change w'⁻¹ • (rootR : Fin (Tag.rank .F4) → ℤ) = rckp5_gamma
      rw [← hw', inv_smul_smul]
    have h := weylAction_eq_of_rootGroup_eq hct hext hβmem (w := w'⁻¹) (by
      rw [hwβ]; exact heq.symm)
    rw [hwβ] at h
    exact (by decide +kernel : (rckp5_gamma : Fin (Tag.rank .F4) → ℤ) ≠ highRoot .F4) h
  have hne_xy : x ≠ y := by
    intro heq
    have heq2 : (twistedRootGroup (GaloisField 2 2) θ (highRoot .F4) :
        Subgroup (fixedGroup (GaloisField 2 2) θ)) =
        twistedRootGroup (GaloisField 2 2) θ rckp5_gamma := by
      apply le_antisymm
      · intro g hg
        have hg' : g ∈ (twistedRootGroup (GaloisField 2 2) θ (highRoot .F4) :
            Set (fixedGroup (GaloisField 2 2) θ)) := hg
        rw [hXβ] at hg'
        change g ∈ (twistedRootGroup (GaloisField 2 2) θ rckp5_gamma : Set _)
        rw [hXγ]
        rcases hg' with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr heq
      · intro g hg
        have hg' : g ∈ (twistedRootGroup (GaloisField 2 2) θ rckp5_gamma :
            Set (fixedGroup (GaloisField 2 2) θ)) := hg
        rw [hXγ] at hg'
        change g ∈ (twistedRootGroup (GaloisField 2 2) θ (highRoot .F4) : Set _)
        rw [hXβ]
        rcases hg' with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr heq.symm
    exact hXβneγ heq2
  let V : Subgroup (fixedGroup (GaloisField 2 2) θ) :=
    Subgroup.zpowers x ⊔ Subgroup.zpowers y
  have hxV : x ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hVab : IsElemAbelian 2 V := rckp5_isElemAbelian_four hx2 hy2 hxy
  have hVcard : Nat.card V = 4 := rckp5_card_four hx2 hy2 hxy hx1 hy1 hne_xy
  have hgen := highestRootGen_of_isHighestRoot hct hext
    (divisibleNormalizes_of_divisible_eq_empty
      (show (twistedDatum (GaloisField 2 2) θ).divisible = ∅ from rfl))
    (divisibleWeylMem_of_divisible_eq_empty
      (show (twistedDatum (GaloisField 2 2) θ).divisible = ∅ from rfl))
    rckp5_isIrreducible_cartan_F4
    (fun γ hγ => isPGroup_two_twistedRootGroup θ hγ)
    (isHighestRoot_twistedE6 θ)
  obtain ⟨-, hradP, hradN, hNrad, -⟩ := hgen
  have hxrad : x ∈ highestRootRadical (twistedDatum (GaloisField 2 2) θ) (highRoot .F4) :=
    rootGroup_le_highestRootRadical hβmem
      (rckp5_rootForm_highRoot_pos θ (highRoot .F4) (by decide +kernel)) hxmem
  have hyrad : y ∈ highestRootRadical (twistedDatum (GaloisField 2 2) θ) (highRoot .F4) :=
    rootGroup_le_highestRootRadical (by
      rw [twistedDatum_roots]
      change IsRoot Tag.F4 rckp5_gamma
      rw [← mem_rootFinset]
      decide +kernel)
      (rckp5_rootForm_highRoot_pos θ rckp5_gamma (by decide +kernel)) hymem
  have hVrad : V ≤ highestRootRadical (twistedDatum (GaloisField 2 2) θ) (highRoot .F4) := by
    intro v hv
    rcases rckp5_mem_four hx2 hy2 hxy hv with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hxrad
    · exact hyrad
    · exact Subgroup.mul_mem _ hxrad hyrad
  have hVpCore : V ≤ pCoreOf 2 (Subgroup.normalizer
      ((twistedDatum (GaloisField 2 2) θ).rootGroup (highRoot .F4) :
        Set (fixedGroup (GaloisField 2 2) θ))) :=
    hVrad.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hradN hNrad hradP)
  have hroot : (twistedDatum (GaloisField 2 2) θ).rootGroup (highRoot .F4) =
      Subgroup.zpowers x := by
    apply le_antisymm
    · intro g hg
      have hg' : g ∈ (twistedRootGroup (GaloisField 2 2) θ (highRoot .F4) :
          Set (fixedGroup (GaloisField 2 2) θ)) := hg
      rw [hXβ] at hg'
      rcases hg' with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers x
    · rw [Subgroup.zpowers_le]
      exact hxmem
  have hcomm_zx : ⁅z, x⁆ = y := by
    apply Subtype.ext
    rw [rckp5_coe_commutator]
    rw [hzval, hxval]
    rw [e6Data_valid.commutator_xm_commSign (GaloisField 2 2) hαz hαθ hne_sum hroot_sum 1 1]
    simp only [rckp5_commSign_eq_one, one_mul]
    rw [hsum, hyval]
  have hconjy : nHat θ (0 : Fin (Tag.rank .F4)) * x *
      (nHat θ (0 : Fin (Tag.rank .F4)))⁻¹ = y := by
    have hconjel := nHat_conj_mem θ (0 : Fin (Tag.rank .F4)) (isRoot_highRoot .F4) hxmem
    have hrefl : reflect .F4 (0 : Fin (Tag.rank .F4)) (highRoot .F4) = rckp5_gamma := by
      decide +kernel
    have hconjel' : nHat θ (0 : Fin (Tag.rank .F4)) * x *
        (nHat θ (0 : Fin (Tag.rank .F4)))⁻¹ ∈
        (twistedRootGroup (GaloisField 2 2) θ rckp5_gamma :
          Set (fixedGroup (GaloisField 2 2) θ)) := by
      rw [← hrefl]; exact hconjel
    rw [hXγ] at hconjel'
    have hconjel1 : nHat θ (0 : Fin (Tag.rank .F4)) * x *
        (nHat θ (0 : Fin (Tag.rank .F4)))⁻¹ ≠ 1 := by
      intro h
      apply hx1
      calc x = (nHat θ (0 : Fin (Tag.rank .F4)))⁻¹ *
            (nHat θ (0 : Fin (Tag.rank .F4)) * x *
              (nHat θ (0 : Fin (Tag.rank .F4)))⁻¹) *
            nHat θ (0 : Fin (Tag.rank .F4)) := by group
        _ = 1 := by rw [h]; group
    rcases hconjel' with h0 | h0
    · exact absurd h0 hconjel1
    · exact h0
  have hzx : z * x * z⁻¹ = x * y := by
    rw [rckp5_conj_eq_commutator_mul, hcomm_zx]
    exact hxy.symm
  refine ⟨highRoot .F4, x, V, hβmem, hβlong, hroot, hx2, hx1, hxV, hVab, hVcard, hVpCore, ?_⟩
  intro v hv hv1
  rcases rckp5_mem_four hx2 hy2 hxy hv with rfl | rfl | rfl | rfl
  · exact absurd rfl hv1
  · refine ⟨1, ?_⟩
    change (x : twistedE6Group 2 1) = (1 : twistedE6Group 2 1) * (x : twistedE6Group 2 1) *
      (1 : twistedE6Group 2 1)⁻¹
    rw [one_mul, inv_one, mul_one]
  · exact ⟨nHat θ (0 : Fin (Tag.rank .F4)), hconjy.symm⟩
  · exact ⟨z, hzx.symm⟩

end CFSG.StandardType.RCKK1II
