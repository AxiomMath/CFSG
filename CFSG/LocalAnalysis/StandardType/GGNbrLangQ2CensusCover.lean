module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Bridge
import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


private theorem q2cCover_ggBeta_eq_ggInducedAut_gamma {G : Type} [Group G] {L B Bs : Subgroup G}
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hBBs : B ≤ Bs) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (b : B) :
    ggBeta L θ hBN b = ggInducedAut θ (ggGamma L hN ⟨b, hBBs b.2⟩) := by
  rw [ggBeta_eq, ggLAut_eq_ggInducedAut]
  congr 1

private theorem q2cCover_layer_unique_component {X : Type} [Group X] [Finite X]
    {u : MulAut X} {J : Subgroup X}
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u))
    (hlayer : J = LargeEvenLayer (ggAutFixedSubgroup u)) :
    ∀ J' : Subgroup X, CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup u) → J' = J := by
  intro J' hJ'
  have hJ'le : J' ≤ J := by
    rw [hlayer]
    exact le_sSup (CFSG.Assembly.isComponentOf_iff_open.2 hJ')
  have hsubJ : CFSG.Open.IsSubnormal J' J := by
    have h := CFSG.Open.IsSubnormal.inf_of_le hJ'.2.1 hJ.1
    rwa [inf_eq_left.mpr hJ'le] at h
  exact CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple
    ⟨hJ'le, hsubJ, hJ'.2.2⟩ hJ.2.2

theorem q2c_cover {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {lab : LargeEvenLabel}
    (hmark : GGInnerDiagOnLab (fun _ lab' => lab' = lab) p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) {d m : ℕ} (hd : 3 ≤ d) (hm : 2 ≤ m)
    (hpd : p ∣ d) (hpm : p ∣ 2 ^ m - 1) (hlow : d ≤ LargeEvenTwoLocalRank p G)
    (hup : LargeEvenTwoLocalRank p G ≤ d + 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ m)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    {S : LargeEvenLabel → Prop} {C : Q2RowKind → Prop} (hR : Q2CensusRLevel S C) (hS : S lab) :
    ∃ kind : Q2RowKind, C kind ∧ q2RowFits kind p d (2 ^ m) lab := by
  have hβ4 : p ∈ LargeEvenBeta 4 G := hcfg.1.2.2.2.2.2.1
  have hp : p.Prime := hβ4.1
  have hp2 : p ≠ 2 := hβ4.2.1
  have h4mu : 4 ≤ LargeEvenTwoLocalRank p G := hβ4.2.2.2
  have hSstar : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBst : GGBstar p B Bs := hcfg.2.1
  have hBBs : B ≤ Bs := hBst.1
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hSstar.1.2.1
  obtain ⟨hperf, lab', hΛ', hraw⟩ := hmark
  obtain ⟨R, instR, I, F, hsimple, hnab, θL, hlab'_eq, hsplit', hNL, hact⟩ :=
    largeEvenRawDatum_exists hraw
  subst hlab'_eq
  have hAll := hR p d m lab' hp hp2 hΛ' hsplit' hS hd hm hpd hpm
  have hraw' := hAll _ hraw
  obtain ⟨R', instR', I', F', hmark', hQ⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨hsimple', hnab', θL', -, hsplit'', hNL', hact'⟩ := hmark'
  obtain ⟨y, uL, hyD, hyu, huord, hcommL, hJL, hJcomp, hlayer⟩ :=
    q1_fixed_component_layer_data hcfg hNL'
  have hDB : D ≤ B := hcfg.2.2.1.1
  have hBNL : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hNL'
  let π : ↥L →* R' := q2CoverMap θL'
  obtain ⟨hJ₀comp, ι, ι_mk⟩ := q2_cover_data hperf θL' uL (J.subgroupOf L) hJcomp
  let J₀ : Subgroup R' := (J.subgroupOf L).map π
  let β : MulAut R' := ggInducedAut θL' uL
  let A' : Subgroup (MulAut R') := (ggBeta L θL' hBNL).range
  have hAcard : Nat.card A' = p ^ (LargeEvenTwoLocalRank p G - 1) := by
    have h := card_range_ggBeta_mul L θL' hp hSstar hperf hBNL
    rw [hBcard] at h
    have hdecomp : p ^ LargeEvenTwoLocalRank p G =
        p ^ (LargeEvenTwoLocalRank p G - 1) * p := by
      conv_lhs =>
        rw [show LargeEvenTwoLocalRank p G = (LargeEvenTwoLocalRank p G - 1) + 1 by omega,
          pow_succ]
    rw [hdecomp] at h
    exact Nat.mul_right_cancel hp.pos h
  have hAb : IsElemAbelian p A' :=
    isElemAbelian_range_ggBeta θL' hSstar.1.1 hBNL
  have h3B : ∀ b ∈ B, ∃ φ ∈ I', LargeEvenInduces θL'
      (fun l l' => (l' : G) = b⁻¹ * l * b) φ := fun b hb => hact' b (hBBs hb)
  have hAI : ∀ a ∈ A', a ∈ I' := by
    intro a ha
    change a ∈ (ggBeta L θL' hBNL).range at ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha
    exact ggBeta_mem L θL' hBNL h3B b
  have hbig : ∀ r : ℕ, GGTorusLift p r R' → p ^ r ≤ Nat.card A' :=
    fun r hlift => pow_le_card_range_ggBeta hp hSstar hperf θL' hBNL hlift
  have h3card : p ^ 3 ≤ Nat.card A' := by
    rw [hAcard]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hlo : p ^ (d - 1) ≤ Nat.card A' := by
    rw [hAcard]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hup' : Nat.card A' ≤ p ^ d := by
    rw [hAcard]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  let yB : ↥B := ⟨y, hDB hyD⟩
  have hβmem : β ∈ A' := by
    change β ∈ (ggBeta L θL' hBNL).range
    rw [MonoidHom.mem_range]
    refine ⟨yB, ?_⟩
    rw [q2cCover_ggBeta_eq_ggInducedAut_gamma θL' hBBs hBNL hNL' yB]
    have hy' : (⟨yB, hBBs yB.2⟩ : ↥Bs) = y := Subtype.ext rfl
    rw [hy', hyu]
  have hβord : orderOf β = p := by
    have hinj : Function.Injective (ggInducedAut θL') :=
      ggInducedAut_injective_of_perfect hperf θL'
    have h1 : orderOf (ggInducedAut θL' uL) = orderOf uL :=
      orderOf_injective (ggInducedAut θL') hinj uL
    change orderOf (ggInducedAut θL' uL) = p
    rw [h1, huord]
  have hcomm_all : ∀ (a : MulAut ↥L) (x : ↥L),
      π (a x) = ggInducedAut θL' a (π x) := by
    intro a x
    simpa [π, q2CoverMap] using (ggInducedAut_apply θL' a x).symm
  have hAJ : ∀ a ∈ A', ∀ j ∈ J₀, a j ∈ J₀ := by
    intro a ha j hj
    change a ∈ (ggBeta L θL' hBNL).range at ha
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp ha
    rw [← hb]
    rw [q2cCover_ggBeta_eq_ggInducedAut_gamma θL' hBBs hBNL hNL' b]
    obtain ⟨j', hj', hjj'⟩ := Subgroup.mem_map.mp hj
    rw [← hjj']
    rw [← hcomm_all]
    refine Subgroup.mem_map.mpr ⟨ggGamma L hNL' ⟨b, hBBs b.2⟩ j', ?_, rfl⟩
    show ((ggGamma L hNL' ⟨b, hBBs b.2⟩ j' : ↥L) : G) ∈ J
    rw [ggGamma_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hN (hBBs b.2)) (j' : G)).mp
      (Subgroup.mem_subgroupOf.mp hj')
  have huniq : ∀ J' : Subgroup R', CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup β) →
      J' = J₀ := by
    intro J' hJ'
    obtain ⟨K', hK'comp, hK'map⟩ :=
      TablePThreeKG.exists_component_of_induced hperf θL' uL
        (CFSG.Assembly.isComponentOf_iff_open.2 hJ')
    have hK'comp' : CFSG.Open.IsComponentOf K' (ggAutFixedSubgroup uL) :=
      CFSG.Assembly.isComponentOf_iff_open.1 hK'comp
    have hK'eq : K' = J.subgroupOf L :=
      q2cCover_layer_unique_component hJcomp hlayer K' hK'comp'
    rw [hK'eq] at hK'map
    rw [← hK'map]
    rfl
  let φ : ↥(J.subgroupOf L) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJL
  let e : ↥J ⧸ Subgroup.center ↥J ≃* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
    (centerQuotCongr φ).symm.trans ι
  let θ' : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K) := e.symm.trans θ
  have hP0 : Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K)) := ⟨θ'⟩
  exact hQ A' hAb hAI hbig h3card hlo hup' β hβmem hβord J₀ hJ₀comp huniq hAJ K hK hP0

end CFSG.StandardType
