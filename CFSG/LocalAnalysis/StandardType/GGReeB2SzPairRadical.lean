module

public import CFSG.LocalAnalysis.StandardType.GGReeB2SzPairDefs
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersRankOne

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.SectionRank.LargeRee CFSG.LieType.Ree CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Quasithin.B45Sz
open CFSG.LieType.Ree.LargeReeCover CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Ree.ReeTag

private def reeJ : Set (Fin F4.tag.rank) := {1, 2}

private def reeRoot (i : Fin 4) : Fin F4.tag.rank → ℤ := largeReeRoot i

private noncomputable def blockWeyl0
: WeylGroup F4.tag :=
  (CFSG.SectionRank.LargeRee.blockGen (0 : Fin 2) : ReeTag.F4.relWeylRee).1

private noncomputable def blockWeyl1
: WeylGroup F4.tag :=
  (CFSG.SectionRank.LargeRee.blockGen (1 : Fin 2) : ReeTag.F4.relWeylRee).1

private theorem rankOneGroupTwo_le_parabolicSubgroup
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) :
    rankOneGroupTwo K m ≤ parabolicSubgroup F4.tag K reeJ := by
  rw [rankOneGroupTwo]
  refine (Subgroup.closure_le (parabolicSubgroup F4.tag K reeJ)).mpr ?_
  rintro g ((hg | ⟨v, rfl⟩) | rfl)
  · have hg1 : g ∈ rootSpan F4.tag K
        (ReeTag.fixedOrbitRoots ReeTag.F4 ⟨1, by decide⟩) :=
      (Subgroup.mem_inf.mp hg).1
    exact le_trans (parabolicLeviUnipotent_le_parabolicLevi reeJ)
      (parabolicLevi_le_parabolicSubgroup reeJ) hg1
  · rw [pairedTorusHom_apply]
    exact torusGroup_le_parabolicSubgroup reeJ
      (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
  · have hw := ReeTag.fixedOrbitElement_mem_fixedOrbitWeyl (t := ReeTag.F4) ⟨1, by decide⟩
    change ReeTag.fixedOrbitElement ReeTag.F4 ⟨1, by decide⟩ ∈
      parabolicWeylGroup F4.tag reeJ at hw
    exact canonicalRep_mem_parabolicSubgroup hw

private theorem reeSz₁_mem_parabolicSubgroup
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) (x : suzukiGroup m K) :
    reeFixedEmb K m (reeSz₁ hK hm x) ∈ parabolicSubgroup F4.tag K reeJ := by
  refine rankOneGroupTwo_le_parabolicSubgroup hK ?_
  rw [rankOneGroupTwo_eq_map hK]
  exact Subgroup.mem_map.mpr ⟨(r2 K m hK).subtype
    (((r2EquivSuzuki K m hK hm).symm.toMonoidHom).comp
      ((MulAut.conj (CFSG.LieType.Ree.suzukiWElt m K)).toMonoidHom) x), Subtype.mem _, rfl⟩

private theorem conj_mem_of_mem_normalizer {G : Type*} [Group G] {H : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (H : Set G)) {x : G} (hx : x ∈ H) :
    y * x * y⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hy x).mp hx

private theorem reeFixedEmb_relNrepHom
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {m : ℕ}
    (w : ReeTag.F4.relWeylRee) :
    reeFixedEmb K m (CFSG.SectionRank.LargeRee.relNrepHom K m w) =
      canonicalRep (coxeterSystem F4.tag) K w.1 := by
  change ((CFSG.SectionRank.LargeRee.relNrepHom K m w : adjointGroup F4.tag K) :
    ModGL F4.tag K) = _
  rw [CFSG.SectionRank.LargeRee.coe_relNrepHom]
  rfl

private theorem blockElt_zero_smul_mem
 (i : Fin 4) :
    IsRoot F4.tag (reeRoot i) ∧
      blockWeyl0 • reeRoot i ∈ parabolicRadicalRoots F4.tag reeJ := by
  refine ⟨(largeReeRoot_pos i).1, ?_⟩
  change (coxeterSystem F4.tag).wordProd (ReeTag.F4.reeOrbitWord (0 : Fin 4)) •
      reeRoot i ∈ parabolicRadicalRoots F4.tag reeJ
  rw [CFSG.LieType.Chevalley.wordProd_smul, mem_parabolicRadicalRoots_iff]
  fin_cases i <;>
    exact ⟨RootOps.isRootB_iff.1 (by decide +kernel), by decide +kernel, by
      simp only [reeJ, Set.mem_insert_iff, Set.mem_singleton_iff]
      decide +kernel⟩

private theorem blockElt_one_zero_smul_mem
 (i : Fin 4) :
    (blockWeyl1 * blockWeyl0) • reeRoot i ∈ parabolicRadicalRoots F4.tag reeJ := by
  change ((coxeterSystem F4.tag).wordProd (ReeTag.F4.reeOrbitWord (1 : Fin 4)) *
      (coxeterSystem F4.tag).wordProd (ReeTag.F4.reeOrbitWord (0 : Fin 4))) •
        reeRoot i ∈ parabolicRadicalRoots F4.tag reeJ
  rw [← CoxeterSystem.wordProd_append, CFSG.LieType.Chevalley.wordProd_smul,
    mem_parabolicRadicalRoots_iff]
  fin_cases i <;>
    exact ⟨RootOps.isRootB_iff.1 (by decide +kernel), by decide +kernel, by
      simp only [reeJ, Set.mem_insert_iff, Set.mem_singleton_iff]
      decide +kernel⟩

private theorem blockElt_zero_smul_check
 :
    ∀ γ ∈ ReeTag.fixedOrbitRoots ReeTag.F4 ⟨1, by decide⟩,
      IsRoot F4.tag γ ∧ ReeTag.F4.blockElt (0 : Fin 4) • γ ∈
        parabolicRadicalRoots F4.tag reeJ := by
  intro γ hγ
  rw [F4_fixedOrbitRoots_one] at hγ
  obtain ⟨i, rfl⟩ := mem_largeReeBlockRoots.1 hγ
  change IsRoot F4.tag (reeRoot i) ∧ ReeTag.F4.blockElt (0 : Fin 4) • reeRoot i ∈
    parabolicRadicalRoots F4.tag reeJ
  exact blockElt_zero_smul_mem i

private theorem blockElt_one_zero_smul_check
 :
    ∀ γ ∈ ReeTag.fixedOrbitRoots ReeTag.F4 ⟨1, by decide⟩,
      IsRoot F4.tag γ ∧
        (blockWeyl1 * blockWeyl0) • γ ∈ parabolicRadicalRoots F4.tag reeJ := by
  intro γ hγ
  rw [F4_fixedOrbitRoots_one] at hγ
  obtain ⟨i, rfl⟩ := mem_largeReeBlockRoots.1 hγ
  change IsRoot F4.tag (reeRoot i) ∧
    (blockWeyl1 * blockWeyl0) • reeRoot i ∈ parabolicRadicalRoots F4.tag reeJ
  exact ⟨(largeReeRoot_pos i).1, blockElt_one_zero_smul_mem i⟩

private theorem reeSz₁_mem_blockX
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m)
    {x : suzukiGroup m K} (hx : x ∈ szUp m K) :
    reeSz₁ hK hm x ∈ CFSG.SectionRank.LargeRee.blockX (K := K) m 1 := by
  obtain ⟨u, hu, hxu⟩ := hx
  have hW2 : CFSG.LieType.Ree.suzukiWElt m K * CFSG.LieType.Ree.suzukiWElt m K = 1 :=
    CFSG.LieType.Ree.suzukiWElt_mul_self
  have hWx : (MulAut.conj (CFSG.LieType.Ree.suzukiWElt m K)).toMonoidHom x = u := by
    rw [← hxu]
    change MulAut.conj (CFSG.LieType.Ree.suzukiWElt m K)
      (MulAut.conj (CFSG.LieType.Ree.suzukiWElt m K) u) = u
    rw [MulAut.conj_apply, MulAut.conj_apply]
    calc CFSG.LieType.Ree.suzukiWElt m K *
          (CFSG.LieType.Ree.suzukiWElt m K * u *
            (CFSG.LieType.Ree.suzukiWElt m K)⁻¹) *
          (CFSG.LieType.Ree.suzukiWElt m K)⁻¹
        = (CFSG.LieType.Ree.suzukiWElt m K * CFSG.LieType.Ree.suzukiWElt m K) * u *
            ((CFSG.LieType.Ree.suzukiWElt m K)⁻¹ *
              (CFSG.LieType.Ree.suzukiWElt m K)⁻¹) := by group
      _ = u := by
          rw [hW2, one_mul, ← mul_inv_rev, hW2, inv_one, mul_one]
  have hK' : Nat.card K = 2 ^ (2 * m + 1) := by
    rw [hK]
    rfl
  obtain ⟨p, q, huS⟩ :=
    (CFSG.LieType.Ree.mem_suzukiU_iff (a := m) (K := K) hK').mp hu
  obtain ⟨x₀, hx₀U, hx₀F, hx₀v⟩ :=
    CFSG.SectionRank.LargeRee.exists_reeFixed_vMat_eq_suzukiS (K := K) (a := m) hK p q
  let xr : reeFixed ReeTag.F4 K m := ⟨x₀, hx₀F⟩
  have hxr_blockX : xr ∈ CFSG.SectionRank.LargeRee.blockX (K := K) m 1 :=
    (CFSG.SectionRank.LargeRee.mem_blockX_one (K := K) (a := m)).mpr hx₀U
  have hxr_r2 : xr ∈ CFSG.SectionRank.LargeRee.r2 K m hK :=
    CFSG.SectionRank.LargeRee.blockX_le_r2 hK hxr_blockX
  let xr2 : CFSG.SectionRank.LargeRee.r2 K m hK := ⟨xr, hxr_r2⟩
  have hrep : CFSG.SectionRank.LargeRee.r2Rep K m hK xr2 =
      (CFSG.LieType.Ree.suzukiSElt m K p q : GL (Fin 4) K) := by
    apply Units.ext
    rw [CFSG.SectionRank.LargeRee.coe_r2Rep, CFSG.LieType.Ree.coe_suzukiSElt]
    exact hx₀v
  have hsuz : (CFSG.SectionRank.LargeRee.r2EquivSuzuki K m hK hm) xr2 = u := by
    apply Subtype.ext
    rw [CFSG.SectionRank.LargeRee.coe_r2EquivSuzuki, hrep, ← huS]
  have hsymm : (CFSG.SectionRank.LargeRee.r2EquivSuzuki K m hK hm).symm u = xr2 := by
    rw [← hsuz, MulEquiv.symm_apply_apply]
  change (CFSG.SectionRank.LargeRee.r2 K m hK).subtype
      ((CFSG.SectionRank.LargeRee.r2EquivSuzuki K m hK hm).symm
        ((MulAut.conj (CFSG.LieType.Ree.suzukiWElt m K)).toMonoidHom x)) ∈
    CFSG.SectionRank.LargeRee.blockX (K := K) m 1
  rw [hWx, hsymm]
  exact hxr_blockX

private theorem reeSz₁_mem_rootSpan_E2
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m)
    {x : suzukiGroup m K} (hx : x ∈ szUp m K) :
    reeFixedEmb K m (reeSz₁ hK hm x) ∈
      rootSpan F4.tag K (ReeTag.fixedOrbitRoots ReeTag.F4 ⟨1, by decide⟩) := by
  have hblock := reeSz₁_mem_blockX hK hm hx
  have hmem : reeFixedEmb K m (reeSz₁ hK hm x) ∈
      (CFSG.SectionRank.LargeRee.blockX (K := K) m 1).map (reeFixedEmb K m) :=
    Subgroup.mem_map.mpr ⟨reeSz₁ hK hm x, hblock, rfl⟩
  rw [CFSG.LieType.Ree.LargeReeInvolution.map_blockX_one] at hmem
  exact (Subgroup.mem_inf.mp hmem).1

private theorem conj_mem_radical
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m)
    {x : suzukiGroup m K}
    (hx : x ∈ szUp m K) {w : WeylGroup F4.tag}
    (hw : ∀ γ ∈ ReeTag.fixedOrbitRoots ReeTag.F4 ⟨1, by decide⟩, IsRoot F4.tag γ ∧ w • γ ∈
        parabolicRadicalRoots F4.tag reeJ) :
    (canonicalRep (coxeterSystem F4.tag) K w : ModGL F4.tag K) *
        reeFixedEmb K m (reeSz₁ hK hm x) *
        ((canonicalRep (coxeterSystem F4.tag) K w : ModGL F4.tag K))⁻¹ ∈
      parabolicRadical F4.tag K reeJ := by
  have h1 := CFSG.LieType.Chevalley.canonicalRep_conj_mem_rootSpan (w := w)
    (fun γ hγ => (hw γ hγ).1) (reeSz₁_mem_rootSpan_E2 hK hm hx)
  refine rootSpan_mono ?_ h1
  rintro δ ⟨γ, hγ, rfl⟩
  exact (hw γ hγ).2

theorem reeUb_norm
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) :
    ∀ x, ∀ u ∈ reeUb K m, reeSz₁ hK hm x * u * (reeSz₁ hK hm x)⁻¹ ∈ reeUb K m := by
  intro x u hu
  have hP : reeFixedEmb K m (reeSz₁ hK hm x) ∈ parabolicSubgroup F4.tag K reeJ :=
    reeSz₁_mem_parabolicSubgroup hK hm x
  have huQ : reeFixedEmb K m u ∈ parabolicRadical F4.tag K reeJ := hu
  have hconj := conj_mem_of_mem_normalizer
    (parabolicSubgroup_le_normalizer_parabolicRadical reeJ hP) huQ
  change reeFixedEmb K m (reeSz₁ hK hm x * u * (reeSz₁ hK hm x)⁻¹) ∈
    parabolicRadical F4.tag K reeJ
  rw [map_mul, map_mul, map_inv]
  exact hconj

private theorem canonicalRep_blockElt_one_mul_zero
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {m : ℕ} :
    canonicalRep (coxeterSystem F4.tag) K (blockWeyl1 * blockWeyl0) =
      canonicalRep (coxeterSystem F4.tag) K blockWeyl1 *
        canonicalRep (coxeterSystem F4.tag) K blockWeyl0 := by
  have hco : (CFSG.SectionRank.LargeRee.blockGen (1 : Fin 2) *
      CFSG.SectionRank.LargeRee.blockGen (0 : Fin 2) : ReeTag.F4.relWeylRee).1 =
      blockWeyl1 * blockWeyl0 := rfl
  calc canonicalRep (coxeterSystem F4.tag) K (blockWeyl1 * blockWeyl0)
      = canonicalRep (coxeterSystem F4.tag) K
          (CFSG.SectionRank.LargeRee.blockGen (1 : Fin 2) *
            CFSG.SectionRank.LargeRee.blockGen (0 : Fin 2) : ReeTag.F4.relWeylRee).1 := by
        rw [hco]
    _ = reeFixedEmb K m (CFSG.SectionRank.LargeRee.relNrepHom K m
          (CFSG.SectionRank.LargeRee.blockGen (1 : Fin 2) *
            CFSG.SectionRank.LargeRee.blockGen (0 : Fin 2))) := by
        rw [← reeFixedEmb_relNrepHom]
    _ = reeFixedEmb K m (CFSG.SectionRank.LargeRee.relNrepHom K m
          (CFSG.SectionRank.LargeRee.blockGen (1 : Fin 2)) *
          CFSG.SectionRank.LargeRee.relNrepHom K m
            (CFSG.SectionRank.LargeRee.blockGen (0 : Fin 2))) := by
        rw [map_mul]
    _ = canonicalRep (coxeterSystem F4.tag) K blockWeyl1 *
        canonicalRep (coxeterSystem F4.tag) K blockWeyl0 := by
        rw [map_mul, reeFixedEmb_relNrepHom, reeFixedEmb_relNrepHom]
        try rfl

private theorem reeNa_reeSz₂_eq
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) (x : suzukiGroup m K) :
    reeNa K m * reeSz₂ hK hm x * (reeNa K m)⁻¹ =
      (reeNb K m * reeNa K m) * reeSz₁ hK hm x * (reeNb K m * reeNa K m)⁻¹ := by
  have hna : reeNa K m * reeNa K m = 1 := by
    change CFSG.SectionRank.LargeRee.relNrepHom K m
        (CFSG.SectionRank.LargeRee.blockGen (0 : Fin 2)) *
      CFSG.SectionRank.LargeRee.relNrepHom K m
        (CFSG.SectionRank.LargeRee.blockGen (0 : Fin 2)) = 1
    exact CFSG.SectionRank.LargeRee.relNrepHom_blockGen_mul_self (i := 0)
  have hg : reeNa K m * (reeNa K m * reeNb K m * reeNa K m) = reeNb K m * reeNa K m := by
    calc reeNa K m * (reeNa K m * reeNb K m * reeNa K m)
        = (reeNa K m * reeNa K m) * reeNb K m * reeNa K m := by group
      _ = reeNb K m * reeNa K m := by rw [hna, one_mul]
  simp only [reeSz₂, MonoidHom.comp_apply, MulAut.conj_apply]
  calc reeNa K m * ((reeNa K m * reeNb K m * reeNa K m) * reeSz₁ hK hm x *
          (reeNa K m * reeNb K m * reeNa K m)⁻¹) * (reeNa K m)⁻¹
      = (reeNa K m * (reeNa K m * reeNb K m * reeNa K m)) * reeSz₁ hK hm x *
          (reeNa K m * (reeNa K m * reeNb K m * reeNa K m))⁻¹ := by group
    _ = (reeNb K m * reeNa K m) * reeSz₁ hK hm x * (reeNb K m * reeNa K m)⁻¹ := by
        rw [hg]

theorem reeNa_up
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) :
    (∀ x ∈ szUp m K, reeNa K m * reeSz₁ hK hm x * (reeNa K m)⁻¹ ∈ reeUb K m) ∧
      ∀ x ∈ szUp m K, reeNa K m * reeSz₂ hK hm x * (reeNa K m)⁻¹ ∈ reeUb K m := by
  constructor
  · intro x hx
    have hconj := conj_mem_radical hK hm hx blockElt_zero_smul_check
    change reeFixedEmb K m (reeNa K m * reeSz₁ hK hm x * (reeNa K m)⁻¹) ∈
      parabolicRadical F4.tag K reeJ
    rw [map_mul, map_mul, map_inv]
    change canonicalRep (coxeterSystem F4.tag) K
          blockWeyl0 *
        reeFixedEmb K m (reeSz₁ hK hm x) *
        (canonicalRep (coxeterSystem F4.tag) K
          blockWeyl0)⁻¹ ∈
      parabolicRadical F4.tag K reeJ
    exact hconj
  · intro x hx
    have hconj := conj_mem_radical hK hm hx blockElt_one_zero_smul_check
    rw [canonicalRep_blockElt_one_mul_zero (K := K) (m := m)] at hconj
    have hid := reeNa_reeSz₂_eq hK hm x
    change reeFixedEmb K m (reeNa K m * reeSz₂ hK hm x * (reeNa K m)⁻¹) ∈
      parabolicRadical F4.tag K reeJ
    rw [hid, map_mul, map_mul, map_inv]
    change canonicalRep (coxeterSystem F4.tag) K
          blockWeyl1 *
        canonicalRep (coxeterSystem F4.tag) K
          blockWeyl0 *
        reeFixedEmb K m (reeSz₁ hK hm x) *
        (canonicalRep (coxeterSystem F4.tag) K
          blockWeyl1 *
          canonicalRep (coxeterSystem F4.tag) K
            blockWeyl0)⁻¹ ∈
      parabolicRadical F4.tag K reeJ
    exact hconj

end CFSG.StandardType.ReeB2Fixed
