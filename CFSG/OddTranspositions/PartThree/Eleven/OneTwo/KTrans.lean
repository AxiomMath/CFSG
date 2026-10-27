module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Frame
public import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.Timmesfeld.Bridge.Asc72ConjOrbit
import CFSG.OddTranspositions.DeltaCentSet
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.OddTranspositions.FusionStep
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open scoped Pointwise

section KTrans

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenTwoFrame

variable {hC : HypothesisC D} {S : Sylow 2 G} {T : Sylow 2 (Halpha D hC.alpha)}
  {r : Fin 3 → Halpha D hC.alpha}

private theorem commSet_subset_DalphaStar (h : ElevenTwoHyp hC) :
    commSet D hC.d ⊆ DalphaStar D hC.alpha := by
  intro x hx
  rcases hx with ⟨hxD, hxcomm, hxne⟩
  have hunion : x ∈ hC.alpha ∪ DalphaStar D hC.alpha ∪ AalphaStar D hC.alpha := by
    rw [← hC.eq_alpha_union]
    exact hxD
  rcases hunion with (hxα | hxE) | hxA
  · rw [h.alpha_eq] at hxα
    exact absurd (Set.mem_singleton_iff.mp hxα) hxne
  · exact hxE
  · rw [hC.AalphaStar_eq_diff_alpha] at hxA
    exact absurd hxcomm hxA.1.2

private theorem DalphaStar_subset_commSet :
    DalphaStar D hC.alpha ⊆ commSet D hC.d := by
  rw [hC.DalphaStar_alpha]
  exact OddLocal.subset_commSet hC.setup.normal hC.hE

private theorem commute_d_frameT (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    Commute hC.d (frameT hC r) := by
  have hri : ∀ i : Fin 3, Commute hC.d ((r i : Halpha D hC.alpha) : G) := by
    intro i
    have hmem : r i ∈ DstarH hC := by
      have : r i ∈ ((T : Subgroup (Halpha D hC.alpha)) : Set (Halpha D hC.alpha)) ∩
          DstarH hC := by
        rw [hF.frame.inter_eq]
        exact ⟨i, rfl⟩
      exact this.2
    exact (DalphaStar_subset_commSet ((mem_DstarH_iff hC).mp hmem)).2.1.symm
  rw [frameT]
  exact ((hri 0).mul_right (hri 1)).mul_right (hri 2)

private theorem Halpha_le_normalizer_zpowers_d (hC : HypothesisC D) :
    Halpha D hC.alpha ≤ Subgroup.normalizer
      (((Subgroup.zpowers hC.d : Subgroup G)) : Set G) := by
  intro b hb
  rw [Subgroup.mem_set_normalizer_iff]
  intro w
  have hbu : Commute b hC.d :=
    (Subgroup.mem_centralizer_iff.mp (Halpha_le_centralizer_d hC hb) hC.d
      (Set.mem_singleton _)).symm
  have hle : Subgroup.zpowers hC.d ≤ Subgroup.centralizer {b} :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hbu.eq)
  constructor
  · intro hw
    have hbw : Commute b w :=
      Subgroup.mem_centralizer_iff.mp (hle hw) b (Set.mem_singleton _)
    have hbw' : b * w * b⁻¹ = w := by rw [hbw.eq]; group
    rwa [hbw']
  · intro hw
    have hbz : Commute b (b * w * b⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hle hw) b (Set.mem_singleton _)
    have h2 : b⁻¹ * (b * w * b⁻¹) * b = b * w * b⁻¹ := by
      rw [hbz.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
    have h1 : b⁻¹ * (b * w * b⁻¹) * b = w := by group
    rw [h1] at h2
    rwa [h2]

private theorem image_mem_centSet (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    {y : Halpha D hC.alpha} (hy : y ∈ centSet (DstarH hC) (r 0 * r 1 * r 2)) :
    (y : G) ∈ centSet D (frameE hC r) := by
  have hyE : (y : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp hy.1
  have hyc := hC.DalphaStar_subset_commute hyE
  have hyct : Commute (y : G) ((r 0 * r 1 * r 2 : Halpha D hC.alpha) : G) :=
    hy.2.map (Subgroup.subtype (Halpha D hC.alpha))
  refine ⟨hyc.1, ?_⟩
  rw [frameE]
  exact hyc.2.mul_right hyct

private theorem orbit_commute (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    {O₁ O₂ : Set G} (hO₁ : O₁ ⊆ centSet D (frameE hC r))
    (hO₂ : O₂ ⊆ centSet D (frameE hC r))
    (hinv₁ : ∀ k ∈ localGroup D (frameE hC r), ∀ y ∈ O₁, k * y * k⁻¹ ∈ O₁)
    (hinv₂ : ∀ k ∈ localGroup D (frameE hC r), ∀ y ∈ O₂, k * y * k⁻¹ ∈ O₂)
    (hdisj : Disjoint O₁ O₂) :
    ∀ y ∈ O₁, ∀ z ∈ O₂, Commute y z := by
  intro y hy z hz
  exact thirdK_orbits_commute (z := frameE hC r) hC.setup
    (by rwa [CFSG.OddTranspositions.Delta_eq_centSet])
    (by rwa [CFSG.OddTranspositions.Delta_eq_centSet])
    (by intro k hk; rw [CFSG.OddTranspositions.thirdK_eq_localGroup] at hk; exact hinv₁ k hk)
    (by intro k hk; rw [CFSG.OddTranspositions.thirdK_eq_localGroup] at hk; exact hinv₂ k hk)
    hdisj y hy z hz

theorem transitive (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    ∀ x ∈ centSet D (frameE hC r), ∃ k ∈ localGroup D (frameE hC r), k * hC.d * k⁻¹ = x := by
  classical
  let Γ : Set G := centSet D (frameE hC r)
  let K : Subgroup G := localGroup D (frameE hC r)
  let C : Set G := (fun y : Halpha D hC.alpha => (y : G)) ''
    centSet (DstarH hC) (r 0 * r 1 * r 2)
  have hTmem : ∀ i : Fin 3, r i ∈ (T : Subgroup (Halpha D hC.alpha)) := by
    intro i
    have : r i ∈ ((T : Subgroup (Halpha D hC.alpha)) : Set (Halpha D hC.alpha)) ∩
        DstarH hC := by
      rw [hF.frame.inter_eq]
      exact ⟨i, rfl⟩
    exact this.1
  have hmemTheta : ∀ i : Fin 3, r i ∈ DstarH hC := by
    intro i
    have : r i ∈ ((T : Subgroup (Halpha D hC.alpha)) : Set (Halpha D hC.alpha)) ∩
        DstarH hC := by
      rw [hF.frame.inter_eq]
      exact ⟨i, rfl⟩
    exact this.2
  have hmemCent : ∀ i : Fin 3, r i ∈ centSet (DstarH hC) (r 0 * r 1 * r 2) :=
    fun i => ⟨hmemTheta i,
      ((hF.frame.commute i 0).mul_right (hF.frame.commute i 1)).mul_right
        (hF.frame.commute i 2)⟩
  have hCsubΓ : C ⊆ Γ := by
    rintro y ⟨z, hz, rfl⟩
    exact image_mem_centSet h hF hz
  have hpre : ∀ y ∈ Γ, Commute y hC.d → y ≠ hC.d → y ∈ C := by
    intro y hy hcy hyne
    have hyE : y ∈ DalphaStar D hC.alpha :=
      commSet_subset_DalphaStar h ⟨hy.1, hcy, hyne⟩
    have hyH : y ∈ Halpha D hC.alpha := Subgroup.subset_closure hyE
    refine ⟨⟨y, hyH⟩, ⟨(mem_DstarH_iff hC).mpr hyE, ?_⟩, rfl⟩
    have hdd : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
    have ht : frameT hC r = hC.d * frameE hC r := by
      calc frameT hC r = (hC.d * hC.d) * frameT hC r := by rw [hdd, one_mul]
        _ = hC.d * (hC.d * frameT hC r) := by group
        _ = hC.d * frameE hC r := by rw [frameE]
    have hyt : Commute y (frameT hC r) := by
      rw [ht]
      exact hcy.mul_right hy.2
    exact Subtype.ext hyt.eq
  have hCsingle : ∀ y ∈ C, y ∈ conjOrbit K ((r 0 : Halpha D hC.alpha) : G) := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨g, hg, hgz⟩ := hF.frame.transitive z hz (r 0) (hmemCent 0)
    have hgK : (g : G) ∈ K := by
      have hle : Subgroup.closure (centSet (DstarH hC) (r 0 * r 1 * r 2)) ≤
          Subgroup.comap (Subgroup.subtype (Halpha D hC.alpha)) K := by
        rw [Subgroup.closure_le]
        intro w hw
        show (w : G) ∈ K
        exact Subgroup.subset_closure (image_mem_centSet h hF hw)
      exact Subgroup.mem_comap.mp (hle hg)
    refine ⟨((g : G))⁻¹, Subgroup.inv_mem _ hgK, ?_⟩
    have hgzG : (g : G) * (z : G) * (g : G)⁻¹ = ((r 0 : Halpha D hC.alpha) : G) :=
      congrArg (fun w : Halpha D hC.alpha => (w : G)) hgz
    show (z : G) = ((g : G))⁻¹ * ((r 0 : Halpha D hC.alpha) : G) * ((g : G))⁻¹⁻¹
    rw [← hgzG]
    group
  intro x hxΓ
  by_contra hxnot
  push Not at hxnot
  have hx_not_Ou : x ∉ conjOrbit K hC.d := by
    rintro ⟨k, hk, hkx⟩
    exact hxnot k hk hkx.symm
  have hxcomm : Commute x hC.d := by
    have hdisj : Disjoint (conjOrbit K hC.d) (conjOrbit K x) :=
      disjoint_conjOrbit_of_not_mem (M := K) hx_not_Ou
    have hpar := orbit_commute h hF (O₁ := conjOrbit K hC.d) (O₂ := conjOrbit K x)
      (fun y hy => conjOrbit_subset_centSet hC.setup.normal
        (show hC.d ∈ centSet D (frameE hC r) from
          ⟨hC.hd, (Commute.refl hC.d).mul_right (commute_d_frameT h hF)⟩) hy)
      (fun y hy => conjOrbit_subset_centSet hC.setup.normal hxΓ hy)
      (fun k hk y hy => conj_mem_conjOrbit hk hy)
      (fun k hk y hy => conj_mem_conjOrbit hk hy) hdisj
    exact (hpar hC.d (self_mem_conjOrbit K hC.d) x (self_mem_conjOrbit K x)).symm
  have hxne : x ≠ hC.d := by
    intro hxeq
    exact hx_not_Ou (hxeq ▸ self_mem_conjOrbit K hC.d)
  have hxC : x ∈ C := hpre x hxΓ hxcomm hxne
  have hxOr : x ∈ conjOrbit K ((r 0 : Halpha D hC.alpha) : G) := hCsingle x hxC
  have hOu_ne_Or : conjOrbit K hC.d ≠ conjOrbit K ((r 0 : Halpha D hC.alpha) : G) := by
    intro hEq
    exact hx_not_Ou (hEq ▸ hxOr)
  have hr0_not_Ou : ((r 0 : Halpha D hC.alpha) : G) ∉ conjOrbit K hC.d := by
    intro hr0Ou
    apply hOu_ne_Or
    obtain ⟨k0, hk0, hk0eq⟩ := hr0Ou
    apply Set.Subset.antisymm
    · rintro y ⟨k, hk, rfl⟩
      refine ⟨k * k0⁻¹, Subgroup.mul_mem _ hk (Subgroup.inv_mem _ hk0), ?_⟩
      have hkey : k0⁻¹ * ((r 0 : Halpha D hC.alpha) : G) * k0 = hC.d := by
        rw [hk0eq]; group
      calc k * hC.d * k⁻¹
          = k * (k0⁻¹ * ((r 0 : Halpha D hC.alpha) : G) * k0) * k⁻¹ := by rw [hkey]
        _ = (k * k0⁻¹) * ((r 0 : Halpha D hC.alpha) : G) * (k * k0⁻¹)⁻¹ := by group
    · rintro y ⟨k, hk, rfl⟩
      refine ⟨k * k0, Subgroup.mul_mem _ hk hk0, ?_⟩
      rw [hk0eq]
      group
  have hdisj : Disjoint (conjOrbit K hC.d) (conjOrbit K ((r 0 : Halpha D hC.alpha) : G)) :=
    disjoint_conjOrbit_of_not_mem (M := K) hr0_not_Ou
  have hriOr : ∀ i : Fin 3,
      ((r i : Halpha D hC.alpha) : G) ∈ conjOrbit K ((r 0 : Halpha D hC.alpha) : G) := by
    intro i
    fin_cases i
    · exact self_mem_conjOrbit K _
    · exact hCsingle _ ⟨⟨r 1, Subgroup.subset_closure (hmemTheta 1)⟩, hmemCent 1, rfl⟩
    · exact hCsingle _ ⟨⟨r 2, Subgroup.subset_closure (hmemTheta 2)⟩, hmemCent 2, rfl⟩
  have huS : hC.d ∈ (S : Set G) ∩ D := ⟨hF.d_mem, hC.hd⟩
  have hr0S : ((r 0 : Halpha D hC.alpha) : G) ∈ (S : Set G) ∩ D := by
    refine ⟨hF.le (Subgroup.mem_map.mpr ⟨r 0, hTmem 0, rfl⟩),
      (DalphaStar_subset_commSet ((mem_DstarH_iff hC).mp (hmemTheta 0))).1⟩
  obtain ⟨c, hcN, hcu⟩ :=
    CFSG.OddTranspositions.sylow_inter_D_transitive hC.setup.isClass hC.setup.oddT S huS hr0S
  have hce : Commute c (frameE hC r) :=
    (Subgroup.mem_centralizer_iff.mp (normalizer_le h hF hcN) (frameE hC r)
      (Set.mem_singleton _)).symm
  have hce' : c * frameE hC r * c⁻¹ = frameE hC r := by
    rw [hce.eq]; group
  have hΓ : ∀ y : G, y ∈ Γ ↔ c * y * c⁻¹ ∈ Γ := by
    intro y
    constructor
    · intro hy
      refine ⟨hC.setup.normal c y hy.1, ?_⟩
      have hcy := hy.2.map (MulAut.conj c)
      rw [MulAut.conj_apply, MulAut.conj_apply] at hcy
      rwa [hce'] at hcy
    · intro hy
      refine ⟨?_, ?_⟩
      · have hmem := hC.setup.normal c⁻¹ (c * y * c⁻¹) hy.1
        rwa [show c⁻¹ * (c * y * c⁻¹) * (c⁻¹)⁻¹ = y by group] at hmem
      · have hcy := hy.2.map (MulAut.conj c⁻¹)
        simp only [MulAut.conj_apply, inv_inv] at hcy
        have h1 : c⁻¹ * (c * y * c⁻¹) * c = y := by group
        have h2 : c⁻¹ * frameE hC r * c = frameE hC r := by
          rw [hce.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
        rwa [h1, h2] at hcy
  have hΓinv : ∀ y : G, y ∈ Γ ↔ c⁻¹ * y * c ∈ Γ := by
    intro y
    have := hΓ (c⁻¹ * y * c)
    rw [show c * (c⁻¹ * y * c) * c⁻¹ = y by group] at this
    exact this.symm
  have hK : ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
    intro k hk
    have hk' := hk
    change k ∈ Subgroup.closure Γ at hk'
    refine Subgroup.closure_induction (p := fun a _ => c * a * c⁻¹ ∈ K)
      (fun y hy => Subgroup.subset_closure ((hΓ y).mp hy)) ?_ ?_ ?_ hk'
    · simpa using Subgroup.one_mem K
    · intro a b _ _ iha ihb
      have h1 : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
      rw [h1]; exact Subgroup.mul_mem K iha ihb
    · intro a _ iha
      have h1 : c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := by group
      rw [h1]; exact Subgroup.inv_mem K iha
  have hKinv : ∀ k ∈ K, c⁻¹ * k * c ∈ K := by
    intro k hk
    have hk' := hk
    change k ∈ Subgroup.closure Γ at hk'
    refine Subgroup.closure_induction (p := fun a _ => c⁻¹ * a * c ∈ K)
      (fun y hy => Subgroup.subset_closure ((hΓinv y).mp hy)) ?_ ?_ ?_ hk'
    · simpa using Subgroup.one_mem K
    · intro a b _ _ iha ihb
      have h1 : c⁻¹ * (a * b) * c = (c⁻¹ * a * c) * (c⁻¹ * b * c) := by group
      rw [h1]; exact Subgroup.mul_mem K iha ihb
    · intro a _ iha
      have h1 : c⁻¹ * a⁻¹ * c = (c⁻¹ * a * c)⁻¹ := by group
      rw [h1]; exact Subgroup.inv_mem K iha
  have hphiOr : ∀ y ∈ conjOrbit K ((r 0 : Halpha D hC.alpha) : G), c⁻¹ * y * c ∈
      conjOrbit K hC.d := by
    rintro y ⟨k, hk, rfl⟩
    refine ⟨c⁻¹ * k * c, hKinv k hk, ?_⟩
    have hkey : c⁻¹ * ((r 0 : Halpha D hC.alpha) : G) * c = hC.d := by
      rw [← hcu]; group
    calc c⁻¹ * (k * ((r 0 : Halpha D hC.alpha) : G) * k⁻¹) * c
        = c⁻¹ * k * (c * hC.d * c⁻¹) * k⁻¹ * c := by rw [← hcu]; group
      _ = (c⁻¹ * k * c) * hC.d * (c⁻¹ * k * c)⁻¹ := by group
  have hphiΔ : ∀ y ∈ (S : Set G) ∩ D, c⁻¹ * y * c ∈ (S : Set G) ∩ D := by
    intro y hy
    exact (Subgroup.mem_set_normalizer_iff''.mp hcN y).mp hy
  have hr1Δ : ((r 1 : Halpha D hC.alpha) : G) ∈ (S : Set G) ∩ D := by
    rw [hF.inter_eq]
    exact Set.mem_insert_of_mem _ ⟨1, rfl⟩
  have hr2Δ : ((r 2 : Halpha D hC.alpha) : G) ∈ (S : Set G) ∩ D := by
    rw [hF.inter_eq]
    exact Set.mem_insert_of_mem _ ⟨2, rfl⟩
  have hOuΔ : conjOrbit K hC.d ∩ ((S : Set G) ∩ D) ⊆ {hC.d} := by
    rintro y ⟨hyOu, hyΔ⟩
    rw [hF.inter_eq] at hyΔ
    rcases hyΔ with rfl | ⟨i, rfl⟩
    · exact Set.mem_singleton _
    · exfalso
      exact (Set.disjoint_left.mp hdisj hyOu) (hriOr i)
  have hphi1 : c⁻¹ * ((r 1 : Halpha D hC.alpha) : G) * c ∈ conjOrbit K hC.d ∩
      ((S : Set G) ∩ D) := ⟨hphiOr _ (hriOr 1), hphiΔ _ hr1Δ⟩
  have hphi2 : c⁻¹ * ((r 2 : Halpha D hC.alpha) : G) * c ∈ conjOrbit K hC.d ∩
      ((S : Set G) ∩ D) := ⟨hphiOr _ (hriOr 2), hphiΔ _ hr2Δ⟩
  have heq1 : c⁻¹ * ((r 1 : Halpha D hC.alpha) : G) * c = hC.d :=
    Set.mem_singleton_iff.mp (hOuΔ hphi1)
  have heq2 : c⁻¹ * ((r 2 : Halpha D hC.alpha) : G) * c = hC.d :=
    Set.mem_singleton_iff.mp (hOuΔ hphi2)
  have h12 : ((r 1 : Halpha D hC.alpha) : G) = ((r 2 : Halpha D hC.alpha) : G) := by
    calc ((r 1 : Halpha D hC.alpha) : G)
        = c * (c⁻¹ * ((r 1 : Halpha D hC.alpha) : G) * c) * c⁻¹ := by group
      _ = c * hC.d * c⁻¹ := by rw [heq1]
      _ = c * (c⁻¹ * ((r 2 : Halpha D hC.alpha) : G) * c) * c⁻¹ := by rw [← heq2]
      _ = ((r 2 : Halpha D hC.alpha) : G) := by group
  have hne : ((r 1 : Halpha D hC.alpha) : G) ≠ ((r 2 : Halpha D hC.alpha) : G) := by
    intro hEq
    exact (by decide : (1 : Fin 3) ≠ 2) (hF.frame.injective (Subtype.ext hEq))
  exact absurd h12 hne

theorem centralizer_d_inf (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    Subgroup.centralizer {hC.d} ⊓ Subgroup.centralizer {frameE hC r} =
      Subgroup.zpowers hC.d ⊔ (Halpha D hC.alpha ⊓ Subgroup.centralizer {frameT hC r}) := by
  have hle : Subgroup.zpowers hC.d ≤ Subgroup.centralizer {frameE hC r} :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ((Commute.refl hC.d).mul_right (commute_d_frameT h hF)).eq.symm)
  have hdd : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have ht : frameT hC r = hC.d * frameE hC r := by
    calc frameT hC r = (hC.d * hC.d) * frameT hC r := by rw [hdd, one_mul]
      _ = hC.d * (hC.d * frameT hC r) := by group
      _ = hC.d * frameE hC r := by rw [frameE]
  rw [h.centralizer_d]
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨hxsup, hxe⟩
    have hxmem : x ∈ (Subgroup.zpowers hC.d : Set G) * (Halpha D hC.alpha : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers hC.d)
        (Halpha D hC.alpha) (Halpha_le_normalizer_zpowers_d hC)]
      exact hxsup
    rcases hxmem with ⟨a, ha, b, hb, rfl⟩
    have hae : Commute a (frameE hC r) :=
      (Subgroup.mem_centralizer_iff.mp (hle ha) (frameE hC r) (Set.mem_singleton _)).symm
    have hxe' : Commute (a * b) (frameE hC r) :=
      (Subgroup.mem_centralizer_iff.mp hxe (frameE hC r) (Set.mem_singleton _)).symm
    have hbe : Commute b (frameE hC r) := by
      have hb_eq : b = a⁻¹ * (a * b) := by group
      rw [hb_eq]
      exact hae.inv_left.mul_left hxe'
    have hbu : Commute b hC.d :=
      (Subgroup.mem_centralizer_iff.mp (Halpha_le_centralizer_d hC hb) hC.d
        (Set.mem_singleton _)).symm
    have hbt : Commute b (frameT hC r) := by
      rw [ht]
      exact hbu.mul_right hbe
    have hbtmem : b ∈ Subgroup.centralizer {frameT hC r} :=
      Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hbt.eq.symm
    exact Subgroup.mul_mem_sup ha ⟨hb, hbtmem⟩
  · intro x hx
    have hxmem : x ∈ (Subgroup.zpowers hC.d : Set G) *
        (↑(Halpha D hC.alpha ⊓ Subgroup.centralizer {frameT hC r}) : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers hC.d)
        (Halpha D hC.alpha ⊓ Subgroup.centralizer {frameT hC r})
        (le_trans inf_le_left (Halpha_le_normalizer_zpowers_d hC))]
      exact hx
    rcases hxmem with ⟨a, ha, b, hb, rfl⟩
    rcases hb with ⟨hbH, hbt⟩
    have hae : Commute a (frameE hC r) :=
      (Subgroup.mem_centralizer_iff.mp (hle ha) (frameE hC r) (Set.mem_singleton _)).symm
    have hbu : Commute b hC.d :=
      (Subgroup.mem_centralizer_iff.mp (Halpha_le_centralizer_d hC hbH) hC.d
        (Set.mem_singleton _)).symm
    have hbtc : Commute b (frameT hC r) :=
      (Subgroup.mem_centralizer_iff.mp hbt (frameT hC r) (Set.mem_singleton _)).symm
    have hbe : Commute b (frameE hC r) := by
      rw [show frameE hC r = hC.d * frameT hC r from rfl]
      exact hbu.mul_right hbtc
    refine ⟨Subgroup.mul_mem_sup ha hbH,
      Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (hae.mul_left hbe).eq.symm

theorem card_centralizer_d_inf (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    Nat.card ↥(Subgroup.centralizer {hC.d} ⊓ Subgroup.centralizer {frameE hC r}) = 480 := by
  rw [centralizer_d_inf h hF]
  let B : Subgroup G := Halpha D hC.alpha ⊓ Subgroup.centralizer {frameT hC r}
  have hcardB : Nat.card B = 240 := by
    have hmap : (Subgroup.centralizer {(r 0 * r 1 * r 2 : Halpha D hC.alpha)}).map
        (Subgroup.subtype (Halpha D hC.alpha)) = B := by
      ext g
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
        rw [Set.mem_singleton_iff] at hz
        subst hz
        have hyc : Commute y (r 0 * r 1 * r 2 : Halpha D hC.alpha) :=
          (Subgroup.mem_centralizer_iff.mp hy (r 0 * r 1 * r 2) (Set.mem_singleton _)).symm
        have hycG : Commute (y : G) (frameT hC r) :=
          hyc.map (Subgroup.subtype (Halpha D hC.alpha))
        exact hycG.eq.symm
      · rintro ⟨hgH, hgc⟩
        refine ⟨⟨g, hgH⟩, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        have hgc' : Commute g (frameT hC r) :=
          (Subgroup.mem_centralizer_iff.mp hgc (frameT hC r) (Set.mem_singleton _)).symm
        apply Subtype.ext
        exact hgc'.eq.symm
    rw [← hmap, Subgroup.card_map_of_injective
      (Subgroup.subtype_injective (Halpha D hC.alpha))]
    exact hF.frame.card_centralizer
  have hdisj : Disjoint (Subgroup.zpowers hC.d) B := by
    rw [disjoint_iff, eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hdd : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
    rcases (mem_zpowers_of_mul_self hdd).mp hz.1 with hz1 | hz1
    · exact hz1
    · exfalso
      exact h.d_not_mem_Halpha (hz1 ▸ hz.2.1)
  have hnorm : B ≤ Subgroup.normalizer
      (((Subgroup.zpowers hC.d : Subgroup G)) : Set G) :=
    le_trans inf_le_left (Halpha_le_normalizer_zpowers_d hC)
  have hcardu : Nat.card (Subgroup.zpowers hC.d) = 2 := by
    rw [Nat.card_zpowers]
    exact hC.setup.oddT.1 hC.d hC.hd
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Subgroup.zpowers hC.d) B hnorm hdisj, hcardB, hcardu]

theorem mul_frameE_not_mem (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    ∀ a ∈ centSet D (frameE hC r), a * frameE hC r ∉ D := by
  intro a ha hmem
  obtain ⟨k, hk, hka⟩ := transitive h hF a ha
  have hke : Commute k (frameE hC r) := commute_of_mem_localGroup hk
  have hdd : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hae : a * frameE hC r = k * frameT hC r * k⁻¹ := by
    calc a * frameE hC r = (k * hC.d * k⁻¹) * frameE hC r := by rw [← hka]
      _ = k * hC.d * (k⁻¹ * frameE hC r) := by group
      _ = k * hC.d * (frameE hC r * k⁻¹) := by rw [hke.inv_left.eq]
      _ = k * (hC.d * frameE hC r) * k⁻¹ := by group
      _ = k * frameT hC r * k⁻¹ := by
        rw [frameE, show hC.d * (hC.d * frameT hC r) = frameT hC r from by
          rw [← mul_assoc, hdd, one_mul]]
  rw [hae] at hmem
  exact frameT_not_mem h hF (by
    have hmem' := hC.setup.normal k⁻¹ (k * frameT hC r * k⁻¹) hmem
    rwa [show k⁻¹ * (k * frameT hC r * k⁻¹) * (k⁻¹)⁻¹ = frameT hC r by group] at hmem')

end ElevenTwoFrame

end KTrans

end CFSG.OddTranspositions.PartThree
