module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeCount
import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelCount
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5Lin

public section

namespace CFSG.StandardType.TwE6NormThree

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.StandardType.TwE6RootKill Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem exists_zetaHom
    {L : Type} [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3) :
    ∃ E : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3) →* ModGL TwistTag.E6.tag L,
      Function.Injective E ∧ ∀ v, E (Multiplicative.ofAdd v) =
        rootDiagUnit TwistTag.E6.tag (fun k => ζ ^ ((v k).val : ℤ)) := by
  have hz : ∀ {w : ZMod 3} {m : ℤ}, (m : ZMod 3) = w → ζ ^ ((w.val : ℕ) : ℤ) = ζ ^ m :=
    fun h => by rw [zpow_eq_zpow_iff_wk hζ, Int.cast_natCast, ZMod.natCast_zmod_val, h]
  refine ⟨{ toFun := fun v => rootDiagUnit TwistTag.E6.tag
              (fun k => ζ ^ (((Multiplicative.toAdd v) k).val : ℤ))
            map_one' := ?_
            map_mul' := fun v v' => ?_ }, fun v v' h => ?_, fun v => rfl⟩
  · rw [show (fun k => ζ ^ (((Multiplicative.toAdd (1 : Multiplicative
        (Fin TwistTag.E6.tag.rank → ZMod 3))) k).val : ℤ)) = 1 from funext fun k => by simp]
    exact rootDiagUnit_one
  · rw [← rootDiagUnit_mul]
    congr 1
    funext k
    simp only [toAdd_mul, Pi.add_apply, Pi.mul_apply, ← zpow_add]
    exact hz (by simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val])
  · simp only [MonoidHom.coe_mk, OneHom.coe_mk] at h
    refine Multiplicative.toAdd.injective (funext fun k => ?_)
    have := congrFun (rootDiagUnit_injective h) k
    rwa [zpow_eq_zpow_iff_wk hζ, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val] at this

theorem three_pow_three_le_card_inf_centralizer
    {L : Type} [Field L] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ 3)
    {G : Type*} [Group G] {f : G →* ModGL TwistTag.E6.tag L} (hf : Function.Injective f)
    {A : Subgroup G} (hA : IsElemAbelian 3 A) (hA4 : 3 ^ 4 ≤ Nat.card A)
    (hAd : ∀ x ∈ A, ∃ c, rootDiagUnit TwistTag.E6.tag c = f x)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hαA : ∀ x ∈ A, ∀ c, rootDiagUnit TwistTag.E6.tag c = f x → rootChar c α = 1)
    {x₀ : G} (hx₀ : x₀ ∈ A) {a₀ : Fin TwistTag.E6.tag.rank → Lˣ}
    (ha₀ : rootDiagUnit TwistTag.E6.tag a₀ = f x₀) (i : KernelComponent (rootCharHom a₀))
    (hend : ∀ x ∈ A, (∀ c, rootDiagUnit TwistTag.E6.tag c = f x →
      ∀ γ ∈ componentRoots (rootCharHom a₀) i, rootChar c γ = 1) → x ∈ Subgroup.zpowers x₀)
    {G' : Type*} [Group G'] {f' : G' →* ModGL TwistTag.E6.tag L} {H : Subgroup G'} [Finite H]
    (hH : ∀ γ ∈ componentRoots (rootCharHom a₀) i,
      ∃ h ∈ H, rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) = f' h)
    {u : G'} (hu : ∀ h ∈ H, ∀ c, rootDiagUnit TwistTag.E6.tag c = f' h → rootChar c α = 1 →
      u * h = h * u) :
    3 ^ 3 ≤ Nat.card ↥(H ⊓ Subgroup.centralizer {u}) := by
  classical
  obtain ⟨E, hEi, hE⟩ := exists_zetaHom hζ
  have hcard : ∀ W : Submodule (ZMod 3) (Fin TwistTag.E6.tag.rank → ZMod 3),
      Nat.card W = 3 ^ finrank (ZMod 3) W := fun W => by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]
  have hlog : ∀ {x c}, x ∈ A → rootDiagUnit TwistTag.E6.tag c = f x →
      ∃ v : Fin TwistTag.E6.tag.rank → ZMod 3, (fun k => ζ ^ ((v k).val : ℤ)) = c :=
    fun {x c} hx hc => exists_zpow_val_eq_rk hζ fun k => by
      have h3 : rootDiagUnit TwistTag.E6.tag (c ^ 3) = rootDiagUnit TwistTag.E6.tag 1 := by
        rw [← rootDiagUnit_pow, hc, ← map_pow, hA.2 x hx, map_one, rootDiagUnit_one]
      exact congrFun (rootDiagUnit_injective h3) k
  have hmemV : ∀ v, v ∈ SmallExc.subgroupModule E (A.map f) ↔
      ∃ x ∈ A, f x = rootDiagUnit TwistTag.E6.tag (fun k => ζ ^ ((v k).val : ℤ)) := fun v => by
    rw [SmallExc.mem_subgroupModule, Subgroup.mem_map, hE]
  have hV : 4 ≤ finrank (ZMod 3) (SmallExc.subgroupModule E (A.map f)) := by
    have hw : ∀ x : A, ∃ v : SmallExc.subgroupModule E (A.map f),
        rootDiagUnit TwistTag.E6.tag (fun k => ζ ^ ((v.1 k).val : ℤ)) = f x := fun x => by
      obtain ⟨c, hc⟩ := hAd x x.2
      obtain ⟨v, rfl⟩ := hlog x.2 hc
      exact ⟨⟨v, (hmemV v).2 ⟨x, x.2, hc.symm⟩⟩, hc⟩
    choose w hw using hw
    have hinj : Function.Injective w := fun x x' h => Subtype.ext (hf (by rw [← hw, ← hw, h]))
    exact (pow_le_pow_iff_right₀ (by norm_num : 1 < 3)).1
      (hA4.trans ((Nat.card_le_card_of_injective w hinj).trans (hcard _).le))
  have hαV : ∀ v ∈ SmallExc.subgroupModule E (A.map f), dot3 α v = 0 := fun v hv => by
    obtain ⟨x, hx, hxv⟩ := (hmemV v).1 hv
    exact (rootChar_val_eq_one_iff_wk hζ v α).1 (hαA x hx _ hxv.symm)
  obtain ⟨y, hy⟩ := hlog hx₀ ha₀
  have hend' : ∀ v ∈ SmallExc.subgroupModule E (A.map f),
      (∀ γ ∈ componentRoots (rootCharHom a₀) i, dot3 γ v = 0) →
        v ∈ Submodule.span (ZMod 3) {y} := fun v hv hvΨ => by
    obtain ⟨x, hx, hxv⟩ := (hmemV v).1 hv
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hend x hx fun c hc γ hγ => by
      rw [hxv] at hc
      rw [rootDiagUnit_injective hc]
      exact (rootChar_val_eq_one_iff_wk hζ v γ).2 (hvΨ γ hγ))
    have hvy : E (Multiplicative.ofAdd v) = E (Multiplicative.ofAdd (m • y)) := by
      rw [hE, ← hxv, ← hm, map_zpow, ← ha₀, ofAdd_zsmul, map_zpow, hE, hy]
    rw [Multiplicative.ofAdd.injective (hEi hvy)]
    exact Submodule.mem_span_singleton.2 ⟨(m : ZMod 3), Int.cast_smul_eq_zsmul (ZMod 3) m y⟩
  have hker : ∀ {δ}, δ ∈ kernelRoots (rootCharHom a₀) ↔
      IsRoot TwistTag.E6.tag δ ∧ dot3 δ y = 0 := fun {δ} => by
    rw [← hy]
    exact and_congr_right fun _ => rootChar_val_eq_one_iff_wk hζ y δ
  obtain ⟨⟨γ₀, hγ₀⟩, hi⟩ := Quotient.exists_rep i
  have h3 := three_le_finrank_cartan3_inf hα (isRootComponent_componentRoots i) ⟨hγ₀, hi⟩
    (fun γ ⟨hγ, _⟩ => (hker.1 hγ).2)
    (fun γ ⟨hγ, hγi⟩ δ hδ hδy hγδ => ⟨hker.2 ⟨hδ, hδy⟩,
      (mk_eq_of_iform_ne_zero (α := ⟨γ, hγ⟩) (β := ⟨δ, hker.2 ⟨hδ, hδy⟩⟩) hγδ).symm.trans hγi⟩)
    hV hαV hend'
  have hT : Submodule.span (ZMod 3) (cartan3 '' componentRoots (rootCharHom a₀) i) ≤
      SmallExc.subgroupModule E (H.map f') := by
    rw [Submodule.span_le]
    rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨h, hh, hhγ⟩ := hH γ hγ
    refine SmallExc.mem_subgroupModule.2 (Subgroup.mem_map.2 ⟨h, hh, ?_⟩)
    rw [← hhγ, hE]
    congr 1
    funext k
    show ζ ^ (∑ l, TwistTag.E6.tag.cartan k l * γ l) = _
    exact (zpow_eq_zpow_iff_wk hζ _ _).2 (by rw [Int.cast_natCast, ZMod.natCast_zmod_val]; rfl)
  have hmem : ∀ v : ↥(Submodule.span (ZMod 3) (cartan3 '' componentRoots (rootCharHom a₀) i) ⊓
      LinearFlag.dotOrth (Submodule.span (ZMod 3) {mod3 α})),
      ∃ h ∈ H ⊓ Subgroup.centralizer {u}, f' h = E (Multiplicative.ofAdd v.1) := fun v => by
    have hv := Submodule.mem_inf.1 v.2
    obtain ⟨h, hh, hhv⟩ := Subgroup.mem_map.1 (SmallExc.mem_subgroupModule.1 (hT hv.1))
    refine ⟨h, ⟨hh, Subgroup.mem_centralizer_singleton_iff.2
      (hu h hh _ (hhv.trans (hE v.1)).symm ?_).symm⟩, hhv⟩
    exact (rootChar_val_eq_one_iff_wk hζ v.1 α).2 (mem_dotOrth_mod3.1 hv.2)
  choose g hg hgv using hmem
  haveI : Finite ↥(H ⊓ Subgroup.centralizer {u}) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : H ⊓ _ ≤ H))
  have hinj : Function.Injective fun v => (⟨g v, hg v⟩ : ↥(H ⊓ Subgroup.centralizer {u})) :=
    fun v v' hvv => Subtype.ext (Multiplicative.ofAdd.injective (hEi (by
      rw [← hgv, ← hgv]
      exact congrArg (fun x => f' x.1) hvv)))
  exact (pow_le_pow_right₀ (by norm_num) h3).trans
    ((hcard _).symm.le.trans (Nat.card_le_card_of_injective _ hinj))

end CFSG.StandardType.TwE6NormThree

end
