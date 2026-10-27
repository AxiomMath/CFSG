module

public import CFSG.LocalAnalysis.WeakClosure81.W183Q
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineComm
public import CFSG.LocalAnalysis.WeakClosure81.W18PackFix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

structure Tail1812TwoCtx (G : Type) [Group G] [Finite G] (D : Data G) (V₀ V H : Subgroup G)
    (i : ℕ) (g : G) : Prop where
  h162 : W3Thm162Gt2 G
  h172 : W3Thm172Weak G
  h5_4 : Asch5_4
  h5_11 : Asch5_11AS
  h5_12 : Asch5_12
  h5_13 : Asch5_13AS
  cex : MinCex183 D V₀ V H i
  not_concl : ¬ Concl182 D V₀ V H i
  hgT : vInH V H g ≤ D.T
  hgK : ¬ vInH V H g ≤ kerMV V H
  hgi : E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i
  hA : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) = 2

structure Tail1812TwoSetting {G : Type} [Group G] (K C H : Subgroup G) {Y : Type} [Group Y]
    [Finite Y] (π : ↥H →* Y) (a₁ : ↥H) (Kk P : Subgroup Y) : Prop where
  surj : Function.Surjective π
  ker_iff : ∀ h : ↥H, π h = 1 ↔ (h : G) ∈ C
  ker_le : ∀ h : ↥H, π h = 1 → (h : G) ∈ K
  mem_kk : ∀ h : ↥H, π h ∈ Kk ↔ (h : G) ∈ K
  ord : orderOf (π a₁) = 2
  not_mem : π a₁ ∉ Kk
  comm_or_conj : ∀ c d : Y, IsConj (π a₁) c → IsConj (π a₁) d →
    c * d = d * c ∨ ∃ z ∈ Subgroup.closure ({c, d} : Set Y), d = z * c * z⁻¹
  o2 : CFSG.pCore 2 Y = ⊥
  kk_normal : Kk.Normal
  p_normal : P.Normal
  kk_le_p : Kk ≤ P
  kk_central : Kk ≤ Subgroup.centralizer (P : Set Y)
  kk_odd : Odd (Nat.card ↥Kk)
  two_quot : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ P
  le_of_not_le : ∀ N : Subgroup Y, N.Normal → ¬ N ≤ Kk → P ≤ N
  radical : ∀ R : Subgroup Y, R.Normal → Group.IsSolvable ↥R → R ≤ Kk

theorem tail1812Two_setting (hB : ListBNonabelian) {g : G}
    (cx : Tail1812TwoCtx G D V₀ V H i g) (M : ModDataE H (eOmegaZ H D.T)) {a₁ : ↥H}
    (ha₁K : (a₁ : G) ∉ kerMV V H) (himg : M.img (vInH V H g) = Subgroup.zpowers (M.ρ a₁))
    (hord : orderOf (M.ρ a₁) = 2) :
    ∃ (π : ↥H →* ↥(M.img H)) (Kk P : Subgroup ↥(M.img H)),
      (∀ j : ↥H, ((π j : ↥(M.img H)) : LGL 2 M.W) = M.ρ j) ∧
        Tail1812TwoSetting (kerMV V H) (Subgroup.centralizer (eOmegaZ H D.T : Set G)) H π a₁
          Kk P := by
  classical
  have h2 := cx.not_concl
  have x : Ctx188 D V₀ V H i 3 := cx.cex.ctx188_three_AS cx.h162 cx.h5_11 h2
  obtain ⟨hgam188, -⟩ := x.exists_involution_img M cx.hgK cx.hgi cx.hA
  have hgam : Gam183 V H (eOmegaZ H D.T) i g :=
    ⟨cx.hgi, fun hle =>
      cx.hgK ((le_inf (inf_le_right : vInH V H g ≤ H) hle).trans
        cx.cex.hyp.inf_centralizer_eOmegaZ_le_kerMV)⟩
  obtain ⟨Kk, F, hsoc, hKk, -, -, hKP, hKC, hodd⟩ :=
    cx.cex.kernel_182 hB cx.h162 cx.h172 cx.h5_4 cx.h5_11 cx.h5_13 h2 M hgam cx.hgT
  have hKs : Group.IsSolvable ↥(kerMV V H) :=
    cx.cex.kerMV_isSolvable_182 cx.h172 cx.h5_4 cx.h5_11 cx.h5_13 h2
  have hK := cx.cex.kernSetting_of_minCex_182 hB h2 x M hsoc hKs hKk
  obtain ⟨π, hπs, hπval, hπk⟩ := M.exists_surjective_img
  obtain ⟨hOK, -⟩ := cx.cex.exists_component182_ker_AS cx.h172 cx.h5_4 cx.h5_11 cx.h5_13 h2
  have hker : ∀ h : ↥H, π h = 1 → (h : G) ∈ kerMV V H := fun h hh =>
    cx.cex.hyp.inf_centralizer_eOmegaZ_le_kerMV ⟨h.2, (hπk h).1 hh⟩
  have hπkersolv : Group.IsSolvable ↥π.ker := by
    haveI := hKs
    have hle : π.ker ≤ (kerMV V H).subgroupOf H := fun h hh =>
      Subgroup.mem_subgroupOf.2 (hker h hh)
    haveI : Group.IsSolvable ↥((kerMV V H).subgroupOf H) := by
      refine Group.isSolvable_of_isSolvable_injective
        (f := (H.subtype.comp (Subgroup.subtype ((kerMV V H).subgroupOf H))).codRestrict
          (kerMV V H) fun q => q.2) ?_
      intro a b hab
      exact Subtype.ext (H.subtype_injective
        (congrArg (fun z : ↥(kerMV V H) => (z : G)) hab))
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have ha2 : orderOf (π a₁) = 2 := by
    rw [← Subgroup.orderOf_coe (π a₁), hπval a₁]
    exact hord
  have hΓ : Subgroup.zpowers ((π a₁ : ↥(M.img H)) : LGL 2 M.W) ∈ x.packFamily M :=
    ⟨g, hgam188, by rw [hπval a₁]; exact himg.symm⟩
  refine ⟨π, Kk, opResidual 2 (⊤ : Subgroup ↥(M.img H)), hπval, ?_⟩
  refine
    { surj := hπs
      ker_iff := hπk
      ker_le := hker
      mem_kk := fun h => hKk h (π h) (hπval h)
      ord := ha2
      not_mem := fun hmem => ha₁K ((hKk a₁ (π a₁) (hπval a₁)).1 hmem)
      comm_or_conj := fun c d hc hd =>
        commute_or_exists_conj_of_isConj (x.assumption131 M)
          (fun A hA => x.mRank_le_iStar M hA) (fun A _ => x.packSpace_le_fixSub M A)
          hΓ ha2 hc hd
      o2 := hK.o2_eq_bot (CFSG.pCore 2 ↥(M.img H))
        (inferInstance : (CFSG.pCore 2 ↥(M.img H)).Normal)
        (CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2)
      kk_normal := hsoc.normal_left
      p_normal := hK.normal
      kk_le_p := hKP
      kk_central := le_of_eq hKC
      kk_odd := hodd
      two_quot := hK.two_quotient
      le_of_not_le := hK.le_of_not_le
      radical := fun R hR hRsol => ?_ }
  intro r hr
  have hcomapSolv : Group.IsSolvable ↥(R.comap π) := by
    have hle : π.ker ≤ R.comap π := fun x hx => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
      exact one_mem R
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle)
      ((π.comp (Subgroup.subtype (R.comap π))).codRestrict R fun x => x.2) ?_
    intro x hx
    have hx1 : π (x : ↥(R.comap π)) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact ⟨⟨x, MonoidHom.mem_ker.mpr hx1⟩, rfl⟩
  have hleRad : R.comap π ≤ CFSG.solvableRadical ↥H :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
      (Subgroup.Normal.comap hR π) hcomapSolv
  have hmapLe : (R.comap π).map H.subtype ≤ kerMV V H := by
    rw [← hOK]
    exact Subgroup.map_mono hleRad
  obtain ⟨h, rfl⟩ := hπs r
  exact (hKk h (π h) (hπval h)).2
    (hmapLe (Subgroup.mem_map_of_mem H.subtype (Subgroup.mem_comap.2 hr)))

theorem tail1812Two_exists_setting (hB : ListBNonabelian) {g : G}
    (cx : Tail1812TwoCtx G D V₀ V H i g) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (π : ↥H →* Y) (a₁ : ↥H) (Kk P : Subgroup Y),
      Tail1812TwoSetting (kerMV V H) (Subgroup.centralizer (eOmegaZ H D.T : Set G)) H π a₁
        Kk P := by
  obtain ⟨M⟩ := exists_modDataE cx.cex.hyp.isElemAbelian_eOmegaZ
    (Hyp183.normalizer_eOmegaZ H D.T)
  have x : Ctx188 D V₀ V H i 3 := cx.cex.ctx188_three_AS cx.h162 cx.h5_11 cx.not_concl
  obtain ⟨-, a₁, -, ha₁K, himg, hord⟩ := x.exists_involution_img M cx.hgK cx.hgi cx.hA
  obtain ⟨π, Kk, P, -, hS⟩ := tail1812Two_setting hB cx M ha₁K himg hord
  exact ⟨↥(M.img H), inferInstance, inferInstance, π, a₁, Kk, P, hS⟩

end CFSG.LocalAnalysis.WeakClosure81

end
