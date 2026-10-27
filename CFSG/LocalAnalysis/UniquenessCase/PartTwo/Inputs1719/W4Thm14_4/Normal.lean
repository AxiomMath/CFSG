module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsMain
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.Quasithin.Background.B69Cent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem w4Thm14_4_normal (hHom : KA5Homog) (hOm : KA5OmegaMinusB) (hSum : KA5NatSum)
    (hInv : KA5InvertsThree) (hFpf : KA5NatFpf)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L₁ L₂ X : Subgroup (MulAut W)} (hO2 : O2Trivial Y) (hB : IsBasicModule Y)
    (hc₁ : IsComponentOf L₁ Y) (hc₂ : IsComponentOf L₂ Y) (ha₁ : IsAlt ↥L₁ 5)
    (ha₂ : IsAlt ↥L₂ 5) (hne : L₁ ≠ L₂) (hX : X = L₁ ⊔ L₂)
    (hb₁ : bParam L₁ Y = 2) (hb₂ : bParam L₂ Y = 2) (hm : E3.mParam Y = 4)
    (hn₁ : (L₁.subgroupOf Y).Normal) (hn₂ : (L₂.subgroupOf Y).Normal)
    (hfix₁ : fixV L₁ = ⊥) (hfix₂ : fixV L₂ = ⊥) :
    IsOmegaPlus ↥X 4 2 ∧ NatOmegaPlus X ⊤ ⊥ 4 2 := by
  classical
  have hcard₁ : Nat.card ↥L₁ = 60 := by
    obtain ⟨e⟩ := ha₁
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcard₂ : Nat.card ↥L₂ = 60 := by
    obtain ⟨e⟩ := ha₂
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hL₁ne : L₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard₁
    omega
  have hL₂ne : L₂ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard₂
    omega
  have hL₁Y : L₁ ≤ Y := hc₁.1
  have hL₂Y : L₂ ≤ Y := hc₂.1
  have hnormY₁ : Y ≤ Subgroup.normalizer (L₁ : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL₁Y).mp hn₁
  have hnormY₂ : Y ≤ Subgroup.normalizer (L₂ : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL₂Y).mp hn₂
  have hmap₁ : ∀ g ∈ Y, L₁.map (MulAut.conj g).toMonoidHom = L₁ := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormY₁ hg)
  have hmap₂ : ∀ g ∈ Y, L₂.map (MulAut.conj g).toMonoidHom = L₂ := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormY₂ hg)
  have hself₁ : L₁ = ⨆ g ∈ Y, L₁.map (MulAut.conj g).toMonoidHom := by
    refine le_antisymm ?_ (iSup₂_le fun g hg => le_of_eq (hmap₁ g hg))
    have hcone : (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) := by
      ext x
      simp
    have h1 : L₁.map (MulAut.conj (1 : MulAut W)).toMonoidHom = L₁ := by
      rw [hcone, Subgroup.map_id]
    exact (le_of_eq h1.symm).trans (le_iSup₂_of_le (1 : MulAut W) Y.one_mem le_rfl)
  have hself₂ : L₂ = ⨆ g ∈ Y, L₂.map (MulAut.conj g).toMonoidHom := by
    refine le_antisymm ?_ (iSup₂_le fun g hg => le_of_eq (hmap₂ g hg))
    have hcone : (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) := by
      ext x
      simp
    have h1 : L₂.map (MulAut.conj (1 : MulAut W)).toMonoidHom = L₂ := by
      rw [hcone, Subgroup.map_id]
    exact (le_of_eq h1.symm).trans (le_iSup₂_of_le (1 : MulAut W) Y.one_mem le_rfl)
  have h125₁ :=
    (w4Lem12_5_holds (W := W) hW Y hO2 hB L₁ hL₁ne hL₁Y hn₁).2 L₁ hc₁ hself₁
  have hIrr₁ : IrrSpanTrans Y L₁ := h125₁.1
  have hSup₁ : (⨆ I ∈ irrSet L₁, I) = ⊤ := by simpa [hfix₁] using h125₁.2
  have h125₂ :=
    (w4Lem12_5_holds (W := W) hW Y hO2 hB L₂ hL₂ne hL₂Y hn₂).2 L₂ hc₂ hself₂
  have hIrr₂ : IrrSpanTrans Y L₂ := h125₂.1
  have hSup₂ : (⨆ I ∈ irrSet L₂, I) = ⊤ := by simpa [hfix₂] using h125₂.2
  have hN₁ : ∀ I ∈ irrSet L₁, BinaryNaturalSL L₁ I ⊥ 2 2 := by
    rcases hHom W hW Y L₁ hL₁Y hn₁ ha₁ hfix₁ hIrr₁ with hN | hO
    · exact hN
    · exfalso
      have hle := hOm W hW Y L₁ hL₁Y hn₁ ha₁ hfix₁ hSup₁ hO
      rw [hb₁] at hle
      omega
  have hN₂ : ∀ I ∈ irrSet L₂, BinaryNaturalSL L₂ I ⊥ 2 2 := by
    rcases hHom W hW Y L₂ hL₂Y hn₂ ha₂ hfix₂ hIrr₂ with hN | hO
    · exact hN
    · exfalso
      have hle := hOm W hW Y L₂ hL₂Y hn₂ ha₂ hfix₂ hSup₂ hO
      rw [hb₂] at hle
      omega
  have hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x :=
    B69.components_mul_comm_of_ne hc₂ hc₁ (Ne.symm hne)
  obtain ⟨hrkI, n, hrkW, hsum⟩ :=
    hSum W hW L₁ L₂ X hX hcomm ha₁ ha₂ hSup₁ hSup₂ hN₁ hN₂
  have hEvenY : Even (Nat.card Y) := by
    have hdvd : Nat.card ↥L₁ ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hL₁Y
    rw [hcard₁] at hdvd
    exact even_iff_two_dvd.mpr (dvd_trans (by norm_num : 2 ∣ 60) hdvd)
  obtain ⟨t, htY, ht2, htm⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam Y hEvenY
  have ht4 : rkIdx (fixV (Subgroup.zpowers t)) = 4 := htm.trans hm
  have hrkt : rk ↥(commV (Subgroup.zpowers t)) = 4 := by
    rw [← rkIdx_fixV_zpowers, ht4]
  have htpow : t ^ 2 = 1 := by
    rw [← ht2]
    exact pow_orderOf_eq_one t
  have ht2mul : t * t = 1 := by
    rw [← pow_two]
    exact htpow
  have hperf₁ : Group.IsPerfect ↥L₁ := by
    obtain ⟨e⟩ := ha₁
    have h : Group.IsPerfect ↥(alternatingGroup (Fin 5)) :=
      Group.isPerfect_def.2 (commutator_alternatingGroup_eq_top (by simp))
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hperf₂ : Group.IsPerfect ↥L₂ := by
    obtain ⟨e⟩ := ha₂
    have h : Group.IsPerfect ↥(alternatingGroup (Fin 5)) :=
      Group.isPerfect_def.2 (commutator_alternatingGroup_eq_top (by simp))
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hQT₁ : QuadTrivial L₁ :=
    quadTrivial_of_commutator_eq_top (Group.isPerfect_def.mp hperf₁)
  have hQT₂ : QuadTrivial L₂ :=
    quadTrivial_of_commutator_eq_top (Group.isPerfect_def.mp hperf₂)
  have hQT : QuadTrivial X := by
    have hfam : QuadTrivial (⨆ b : Bool, (if b then L₁ else L₂)) := by
      refine quadTrivial_iSup fun b => ?_
      cases b with
      | false => simpa using hQT₂
      | true => simpa using hQT₁
    have hsup : L₁ ⊔ L₂ = ⨆ b : Bool, (if b then L₁ else L₂) := by
      refine le_antisymm ?_ ?_
      · refine sup_le ?_ ?_
        · simpa using le_iSup (fun b : Bool => (if b then L₁ else L₂)) true
        · simpa using le_iSup (fun b : Bool => (if b then L₁ else L₂)) false
      · exact iSup_le fun b => by cases b <;> simp
    rw [hX, hsup]
    exact hfam
  have hkey : (∀ x ∈ L₁, t * x = x * t) → (∀ x ∈ L₂, t * x = x * t) →
      ∀ x ∈ X, t * x = x * t := by
    intro h1 h2 x hx
    have hcx₁ : L₁ ≤ Subgroup.centralizer ({t} : Set (MulAut W)) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact h1 y hy
    have hcx₂ : L₂ ≤ Subgroup.centralizer ({t} : Set (MulAut W)) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact h2 y hy
    have hx' : x ∈ L₁ ⊔ L₂ := by rwa [← hX]
    have hle : L₁ ⊔ L₂ ≤ Subgroup.centralizer ({t} : Set (MulAut W)) := sup_le hcx₁ hcx₂
    exact Subgroup.mem_centralizer_iff.mp (hle hx') t (Set.mem_singleton t)
  by_cases hcent : ∀ x ∈ X, t * x = x * t
  ·
    exfalso
    have hTstab : StableUnder X (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
      refine stableUnder_commSub ?_ (fun x _ u _ => Subgroup.mem_top u)
      intro h hh x hx
      have hcx : h * x = x * h := by
        have hle : Subgroup.zpowers t ≤ Subgroup.centralizer ({h} : Set (MulAut W)) := by
          rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact (hcent h hh).symm
        exact Subgroup.mem_centralizer_iff.mp (hle hx) h (Set.mem_singleton h)
      rw [hcx]
      simpa using hx
    have hfixX : fixV X = ⊥ := by
      rw [eq_bot_iff]
      exact (B1.fixV_le_fixV (show L₁ ≤ X by rw [hX]; exact le_sup_left)).trans
        (le_of_eq hfix₁)
    have hneT : commSub (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) X ≠ ⊥ := by
      intro hbot
      have hle : commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ≤ fixV X :=
        commSub_eq_bot_iff.mp hbot
      have hbot2 : commSub (⊤ : Subgroup W) (Subgroup.zpowers t) = ⊥ :=
        le_bot_iff.mp (hle.trans (le_of_eq hfixX))
      have h4 : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) = 4 := by
        rw [← commV_eq_commSub]
        exact hrkt
      rw [hbot2, rk_bot] at h4
      omega
    obtain ⟨I, hI, hIle⟩ := exists_mem_irrSet_le hQT hTstab hneT
    have h8 : rk ↥I = 8 := hrkI I hI
    have h4 : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) = 4 := by
      rw [← commV_eq_commSub]
      exact hrkt
    have := rk_mono hIle
    omega
  ·
    push Not at hcent
    obtain ⟨x, hxX, hncx⟩ := hcent
    have hnc_or : (∃ x ∈ L₁, t * x ≠ x * t) ∨ (∃ x ∈ L₂, t * x ≠ x * t) := by
      by_contra h
      push Not at h
      exact hncx (hkey h.1 h.2 x hxX)
    have hnorm₁ : ∀ x ∈ L₁, t * x * t⁻¹ ∈ L₁ := by
      intro x hx
      have hmem : (MulAut.conj t) x ∈ L₁.map (MulAut.conj t).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hmap₁ t htY] at hmem
      simpa [MulAut.conj_apply] using hmem
    have hnorm₂ : ∀ x ∈ L₂, t * x * t⁻¹ ∈ L₂ := by
      intro x hx
      have hmem : (MulAut.conj t) x ∈ L₂.map (MulAut.conj t).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hmap₂ t htY] at hmem
      simpa [MulAut.conj_apply] using hmem
    have hstep : ∀ L : Subgroup (MulAut W), IsAlt ↥L 5 →
        (∀ x ∈ L, t * x * t⁻¹ ∈ L) → (∃ x ∈ L, t * x ≠ x * t) →
        (⨆ I ∈ irrSet L, I) = ⊤ → (∀ I ∈ irrSet L, BinaryNaturalSL L I ⊥ 2 2) → n = 1 := by
      intro L haL hnormL hncL hSupL hNL
      obtain ⟨z, hzL, hzord, htz⟩ := hInv (MulAut W) L t haL htpow hnormL hncL
      have hzfix : fixV (Subgroup.zpowers z) = ⊥ :=
        hFpf W hW L haL hSupL hNL z hzL hzord
      have hz3 : z ^ 3 = 1 := by
        rw [← hzord]
        exact pow_orderOf_eq_one z
      have h2 := two_mul_rk_commV_of_inv_fpf hW hz3 hzfix ht2mul htz
      have hrk8 : rk W = 8 := by
        rw [hrkt] at h2
        omega
      omega
    have hn1 : n = 1 := by
      rcases hnc_or with hnc₁ | hnc₂
      · exact hstep L₁ ha₁ hnorm₁ hnc₁ hSup₁ hN₁
      · exact hstep L₂ ha₂ hnorm₂ hnc₂ hSup₂ hN₂
    have hNat : NatOmegaPlus X ⊤ ⊥ 4 2 := by
      rw [hn1] at hsum
      obtain ⟨I, -, -, hsup, hN⟩ := hsum
      have hI : I 0 = ⊤ := by
        rw [bot_sup_eq, iSup_unique] at hsup
        exact hsup
      exact hI ▸ hN 0
    refine ⟨?_, hNat⟩
    rw [hX]
    exact isOmegaPlus_sup_of_isAlt_five hcomm (inf_eq_bot_of_commute_isAlt_five hcomm ha₁) ha₁ ha₂

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
