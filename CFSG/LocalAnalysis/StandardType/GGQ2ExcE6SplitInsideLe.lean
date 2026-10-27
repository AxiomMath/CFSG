module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitRoots
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitOccursDict
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitLabel
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideOrth
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreOccursDict
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreAmbientRefl
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyQuad
import CFSG.LocalAnalysis.StandardType.GGLinImageSubspace
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4Center

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes

noncomputable section


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup .E6 L p}
  {T₀ : Subgroup (ModGL .E6 L)}

theorem E6SplitDatum.root_eq_zero_of_mem_ggLinImage_rootSpan (d : E6SplitDatum S T₀)
    {c : Finset (ExcRaw.Root 1)} {k : ExcRaw.Root 1}
    (hk : ∀ δ ∈ e6SplitCodeRoots c, iform (e6SplitRoot k) δ = 0) {v : ExcRaw.V 1}
    (hv : v ∈ ggLinImage (p := 3) d.coord (rootSpan .E6 L (e6SplitCodeRoots c))) :
    ExcRaw.root 1 k v = 0 := by
  classical
  let t : ↥T₀ := Additive.toMul (d.coord.symm v)
  have htv : d.coord (Additive.ofMul t) = v := by simp [t]
  have hmem : (t : ModGL .E6 L) ∈ rootSpan .E6 L (e6SplitCodeRoots c) :=
    (mem_ggLinImage d.coord (rootSpan .E6 L (e6SplitCodeRoots c)) v).mp hv
  obtain ⟨a, ha, -, -⟩ := exists_family_of_le_fullThreeTorus d.le_fullThreeTorus
  let b := a t
  have hb : (t : ModGL .E6 L) = rootDiagUnit .E6 b := (ha t).symm
  have hγk : IsRoot .E6 (e6SplitRoot k) := isRoot_e6SplitRoot k
  have htwo : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ → iform γ γ = 2 :=
    fun γ hγ => CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two
      (τ := .E6) (Or.inr (Or.inl rfl)) hγ
  have hcomm : ∀ β ∈ e6SplitCodeRoots c, ∀ x ∈ rootSubgroup .E6 L β,
      ∀ y ∈ rootSubgroup .E6 L (e6SplitRoot k), Commute x y := by
    intro β hβ x hx y hy
    have hβroot : IsRoot .E6 β := isRoot_of_mem_e6SplitCodeRoots hβ
    have horth : iform β (e6SplitRoot k) = 0 := by
      rw [iform_comm]
      exact hk β hβ
    have hne : β ≠ e6SplitRoot k := by
      intro h
      have h2 : iform (e6SplitRoot k) (e6SplitRoot k) = 0 := by
        have := hk β hβ
        rwa [h] at this
      rw [htwo _ hγk] at h2
      norm_num at h2
    have hne' : β ≠ -e6SplitRoot k := by
      intro h
      have h2 : iform (e6SplitRoot k) (-e6SplitRoot k) = 0 := by
        have := hk β hβ
        rwa [h] at this
      rw [iform_neg_right, htwo _ hγk] at h2
      norm_num at h2
    have hnot : ¬ IsRoot .E6 (β + e6SplitRoot k) :=
      not_isRoot_add_of_orth (τ := .E6) (Or.inr (Or.inl rfl)) hβroot hγk horth
    exact (simply_laced_root_commutator_unit .E6 (Or.inr (Or.inl rfl)) hβroot hγk hne hne').2
      hnot L x hx y hy
  have hbroot : rootDiagUnit .E6 b ∈ rootSpan .E6 L (e6SplitCodeRoots c) := by
    rwa [ha t]
  have hrootchar : rootChar b (e6SplitRoot k) = 1 :=
    rootChar_eq_one_of_mem_rootSpan hγk hcomm hbroot
  have hchar : d.ζ ^ (ExcRaw.root 1 k v).val = 1 := by
    rw [← htv, ← d.rootChar_eq t b hb k]
    exact hrootchar
  have hzero : ExcRaw.root 1 k v = 0 :=
    zeta_pow_val_injective d.ζ_pow_three d.ζ_ne_one (by simpa using hchar)
  simpa using hzero

theorem E6SplitDatum.eq_zero_of_mem_ggLinImage_of_mem_cent (hS : E6SplitLangTwo S)
    (d : E6SplitDatum S T₀) {U : Submodule (ZMod 3) (ExcRaw.V 1)} {c : Finset (ExcRaw.Root 1)}
    (hc : ExcRaw.occurs 1 U c) (ht : (c.card, ExcRaw.longCount 1 c) = (9, 6)) {w : ExcRaw.V 1}
    (hw : w ∈ ggLinImage (p := 3) d.coord (rootSpan .E6 L (e6SplitCodeRoots c)))
    (hwc : w ∈ ExcRaw.cent 1 c) : w = 0 := by
  classical
  have hchar : CharP L 2 :=
    CFSG.StandardType.LangRat.charP_two_of_langSetup_q_eq_two_pow (f := 1) S
      (by rw [hS.1, pow_one])
  have hc' : ExcRaw.occurs 1 (ExcRaw.cent 1 c) c := ExcRaw.occurs_cent_of_occurs hc
  obtain ⟨A, hA, hAU⟩ := exists_le_ggLinImage_eq_of_addEquiv (p := 3) d.coord (ExcRaw.cent 1 c)
  obtain ⟨a, ha, hT, _⟩ := exists_family_of_le_fullThreeTorus (hA.trans d.le_fullThreeTorus)
  let χ := famCharHom a
  obtain ⟨j, hj⟩ := E6SplitDatum.exists_kernelComponent_of_occurs hS d hA ha (by rwa [hAU])
  have hlong6 : ExcRaw.longCount 1 c = 6 := congrArg Prod.snd ht
  have hcard9 : c.card = 9 := congrArg Prod.fst ht
  have hroots : componentRoots χ j = e6SplitCodeRoots c :=
    componentRoots_eq_e6SplitCodeRoots_of_longCount_ne_zero hS hT j hj
      (by rw [hlong6]; norm_num)
  have h24R : (e6SplitCodeRoots c).ncard = 24 := by
    rw [ncard_e6SplitCodeRoots c, hlong6, hcard9]
  have h24 : (componentRoots χ j).ncard = 24 := by rw [hroots]; exact h24R
  have hne : (componentRoots χ j).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [h24]; norm_num)
  have hr : compRank (componentRoots χ j) = 4 :=
    compRank_eq_four_of_ncard_eq_24 (isRootComponent_componentRoots j) hne h24
  have hcenter : Subgroup.center (rootSpan .E6 L (componentRoots χ j)) = ⊥ :=
    letI : CharP L 2 := hchar
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.center_eq_bot_of_compRank_four_ncard_24
      (τ := .E6) (L := L) (χ := χ) j hr h24
  have hspan : rootSpan .E6 L (componentRoots χ j) =
      rootSpan .E6 L (e6SplitCodeRoots c) := by rw [hroots]
  have hcenter' : Subgroup.center (rootSpan .E6 L (e6SplitCodeRoots c)) = ⊥ := by
    rw [hspan] at hcenter
    exact hcenter
  let t : ↥T₀ := Additive.toMul (d.coord.symm w)
  have htw : d.coord (Additive.ofMul t) = w := by simp [t]
  have htS : (t : ModGL .E6 L) ∈ rootSpan .E6 L (e6SplitCodeRoots c) :=
    (mem_ggLinImage d.coord (rootSpan .E6 L (e6SplitCodeRoots c)) w).mp hw
  have hwA : w ∈ ggLinImage (p := 3) d.coord A := by rw [hAU]; exact hwc
  have htA : (t : ModGL .E6 L) ∈ A := (mem_ggLinImage d.coord A w).mp hwA
  let u : ↥A := ⟨t, htA⟩
  have ha_u : rootDiagUnit .E6 (a u) = (t : ModGL .E6 L) := ha u
  have hcent_i : ∀ v ∈ ExcRaw.cent 1 c, ∀ i ∈ c, ExcRaw.root 1 i v = 0 := by
    intro v hv
    simpa only [ExcRaw.cent, Submodule.mem_iInf, LinearMap.mem_ker] using hv
  have hker : ∀ δ ∈ e6SplitCodeRoots c, rootChar (a u) δ = 1 := by
    intro δ hδ
    obtain ⟨i, hi, hδi⟩ := hδ
    have hV : ExcRaw.Vanish 1 (ggLinImage (p := 3) d.coord A) i := by
      intro v hv
      rw [hAU] at hv
      exact hcent_i v hv i hi
    have hkerδ : δ ∈ kernelRoots (famCharHom a) :=
      (E6SplitDatum.mem_kernelRoots_family_iff hS d hA ha).2
        ⟨i, ⟨i, Finset.mem_singleton_self i, hδi⟩, hV⟩
    exact ((CFSG.StandardType.TableCRes.mem_kernelRoots_famChar a).1 hkerδ).2 u
  have hkerRoot : e6SplitCodeRoots c ⊆ rootCharKernel (a u) := by
    intro δ hδ
    exact ⟨isRoot_of_mem_e6SplitCodeRoots hδ, hker δ hδ⟩
  have hle := rootSpan_le_centralizer (K := L) (a u) hkerRoot
  have hmem_center : (⟨t, htS⟩ : ↥(rootSpan .E6 L (e6SplitCodeRoots c))) ∈
      Subgroup.center (rootSpan .E6 L (e6SplitCodeRoots c)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hy := hle y.2
    rw [Subgroup.mem_centralizer_iff] at hy
    have hcomm : rootDiagUnit .E6 (a u) * (y : ModGL .E6 L) =
        (y : ModGL .E6 L) * rootDiagUnit .E6 (a u) :=
      hy _ (Set.mem_singleton _)
    rw [ha_u] at hcomm
    exact hcomm.symm
  have hx_one : (⟨t, htS⟩ : ↥(rootSpan .E6 L (e6SplitCodeRoots c))) = 1 := by
    have h := hmem_center
    rw [hcenter'] at h
    exact Subgroup.mem_bot.1 h
  have ht_one : (t : ModGL .E6 L) = 1 := by
    have := congrArg Subtype.val hx_one
    simpa using this
  have ht_eq : t = 1 := Subtype.ext ht_one
  calc w = d.coord (Additive.ofMul t) := htw.symm
    _ = d.coord (Additive.ofMul (1 : ↥T₀)) := by rw [ht_eq]
    _ = 0 := by simp

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
