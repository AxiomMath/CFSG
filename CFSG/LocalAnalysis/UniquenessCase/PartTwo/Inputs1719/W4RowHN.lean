module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowMGe
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Sub
public import CFSG.Sporadic.HNOddCore.OuterFix
public import CFSG.Sporadic.HNOddCore.SixA
public import CFSG.Sporadic.HN.Local.Main
public import CFSG.Sporadic.HNSchreier.InvolSpec
public import Certificates.Certificate1037101
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowGen
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
import CFSG.Quasithin.Background.SmithB45ExcEngine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHN

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.HNOddCore CFSG.QuasithinUnique.Setup

theorem isConj_or_isConj_of_cover {G H : Type*} [Group G] [Group H] (e : G ≃* H) {a b : G}
    (hcov : ∀ g : G, g ^ 2 = 1 → g ≠ 1 → IsConj a g ∨ IsConj b g) {x y : H} (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) (hxy : ¬IsConj x y) {t : H} (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) : IsConj x t ∨ IsConj y t := by
  have key : ∀ z : H, z ^ 2 = 1 → z ≠ 1 → IsConj (e a) z ∨ IsConj (e b) z := by
    intro z hz2 hz1
    have h2 : e.symm z ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
    have h1 : e.symm z ≠ 1 := fun h => hz1 (by simpa using congrArg e h)
    rcases hcov _ h2 h1 with h | h
    · exact Or.inl (by simpa using e.toMonoidHom.map_isConj h)
    · exact Or.inr (by simpa using e.toMonoidHom.map_isConj h)
  rcases key x hx2 hx1 with hx | hx <;> rcases key y hy2 hy1 with hy | hy
  · exact absurd (hx.symm.trans hy) hxy
  · rcases key t ht2 ht1 with h | h
    · exact Or.inl (hx.symm.trans h)
    · exact Or.inr (hy.symm.trans h)
  · rcases key t ht2 ht1 with h | h
    · exact Or.inr (hy.symm.trans h)
    · exact Or.inl (hx.symm.trans h)
  · exact absurd (hx.symm.trans hy) hxy

theorem exists_orderOf_mem_closure_conjSet_of_isConj {S : Type*} [Group S] {B : Subgroup S}
    {x t g₁ g₂ : S} {n : ℕ} (htB : t ∈ B) (hxt : IsConj x t)
    (h : orderOf (x * (g₁ * x * g₁⁻¹) * (g₂ * x * g₂⁻¹)) = n) :
    ∃ cs : List S, cs.length = 3 ∧
      ∃ y ∈ Subgroup.closure (X1.conjSet cs (B : Set S)), orderOf y = n := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hxt
  refine ⟨[1, c * g₁ * c⁻¹, c * g₂ * c⁻¹], rfl,
    t * ((c * g₁ * c⁻¹) * t * (c * g₁ * c⁻¹)⁻¹) * ((c * g₂ * c⁻¹) * t * (c * g₂ * c⁻¹)⁻¹),
    Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure ⟨1, by simp, t, htB, by group⟩)
      (Subgroup.subset_closure ⟨_, by simp, t, htB, rfl⟩))
      (Subgroup.subset_closure ⟨_, by simp, t, htB, rfl⟩), ?_⟩
  have e : t * ((c * g₁ * c⁻¹) * t * (c * g₁ * c⁻¹)⁻¹) * ((c * g₂ * c⁻¹) * t * (c * g₂ * c⁻¹)⁻¹) =
      MulAut.conj c (x * (g₁ * x * g₁⁻¹) * (g₂ * x * g₂⁻¹)) := by
    rw [MulAut.conj_apply, ← hc]
    group
  rw [e, MulEquiv.orderOf_eq, h]

theorem orderOf_conj_mul_conj {G : Type*} [Group G] (a t v : G) :
    orderOf (a * t * a⁻¹ * (a * v * a⁻¹ * (a * t * a⁻¹) * (a * v * a⁻¹)⁻¹)) =
      orderOf (t * (v * t * v⁻¹)) := by
  have e : a * t * a⁻¹ * (a * v * a⁻¹ * (a * t * a⁻¹) * (a * v * a⁻¹)⁻¹) =
      MulAut.conj a (t * (v * t * v⁻¹)) := by
    rw [MulAut.conj_apply]
    group
  rw [e, MulEquiv.orderOf_eq]

theorem jh_involution_classes
    {u : JH} (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) (hnc : ¬IsConj aJ u) {t : JH} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    IsConj aJ t ∨ IsConj u t :=
  @isConj_or_isConj_of_cover CFSG.Blueprint.NativeSporadic.HN JH inferInstance
    (Subgroup.toGroup JH) hnEquivJ CFSG.Sporadic.HN.Local.hnT2 CFSG.Sporadic.HN.Local.hnT4
    CFSG.Sporadic.HN.Local.hn_involution_cover aJ u aJ_sq aJ_ne_one hu2 hu1 hnc t ht2 ht1

theorem exists_of_isConj_J {B : Subgroup JH} {x t g₁ g₂ : JH} (htB : t ∈ B) (hxt : IsConj x t)
    (h : orderOf (x * (g₁ * x * g₁⁻¹) * (g₂ * x * g₂⁻¹)) = 19) :
    ∃ cs : List JH, cs.length = 3 ∧
      ∃ y ∈ Subgroup.closure (X1.conjSet cs (B : Set JH)), orderOf y = 19 :=
  @exists_orderOf_mem_closure_conjSet_of_isConj JH (Subgroup.toGroup JH) B x t g₁ g₂ 19 htB hxt h

theorem jh_gen3
    (B : Subgroup JH) (hsq : ∀ x ∈ B, x * x = 1) (hne : B ≠ ⊥) :
    ∃ cs : List JH, cs.length = 3 ∧
      ∃ x ∈ Subgroup.closure (X1.conjSet cs (B : Set JH)), orderOf x = 19 := by
  obtain ⟨u, g₁, g₂, h₁, h₂, hu2, hu1, hnc, ha, hu⟩ := Certificates.certificate1037101.1
  obtain ⟨⟨t, htB⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht2 : t ^ 2 = 1 := by rw [sq]; exact hsq t htB
  rcases jh_involution_classes hu2 hu1 hnc ht2 ht1' with h | h
  · exact exists_of_isConj_J htB h ha
  · exact exists_of_isConj_J htB h hu

theorem orderOf_t1R_triple :
    ∃ w : JH, orderOf (t1R * (jR w * t1R * (jR w)⁻¹)) = 19 := by
  obtain ⟨w, hw⟩ : ∃ w : JH, orderOf (cU * ((w : GL (Fin hnsData.d) (ZMod 5)) * cU *
      (w : GL (Fin hnsData.d) (ZMod 5))⁻¹)) = 19 := Certificates.certificate1037101.2
  refine ⟨w, ?_⟩
  rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, jR_val, t1R, cR_val]
  exact hw

theorem orderOf_conjR
    (r : RH) : orderOf (conjR r) = orderOf r := by
  have key := orderOf_injective (G := RH) (H := MulAut JH)
  exact key conjR conjR_injective r

theorem orderOf_conj_mul_conj_R
    (a t v : RH) :
    orderOf (a * t * a⁻¹ * (a * v * a⁻¹ * (a * t * a⁻¹) * (a * v * a⁻¹)⁻¹)) =
      orderOf (t * (v * t * v⁻¹)) :=
  @orderOf_conj_mul_conj RH (Subgroup.toGroup RH) a t v

theorem jh_outer_dihedral
    (ψ : MulAut JH)
    (hψ : ψ ∉ (MulAut.conj (G := JH)).range) (h2 : ψ * ψ = 1) :
    ∃ α : MulAut JH, orderOf (ψ * (α * ψ * α⁻¹)) = 19 := by
  obtain ⟨r, rfl⟩ := conjR_surjective ψ
  have hr2 : r ^ 2 = 1 := conjR_injective (by rw [map_pow, sq, h2, map_one])
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hψ (MonoidHom.mem_range.2 ⟨1, by rw [map_one, map_one]⟩)
  have hout : r ∉ jR.range := by
    intro h
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 h
    exact hψ (MonoidHom.mem_range.2 ⟨g, (conjR_jR g).symm⟩)
  obtain ⟨g, hg⟩ := fuse_t1R r hr2 hr1 hout
  obtain ⟨w, hw⟩ := orderOf_t1R_triple
  refine ⟨conjR (jR g * jR w * (jR g)⁻¹), ?_⟩
  rw [← map_inv conjR, ← map_mul conjR, ← map_mul conjR, ← map_mul conjR, orderOf_conjR, ← hg,
    orderOf_conj_mul_conj_R, hw]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHN

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore W4RowHN

theorem w4Thm11_1RowMGe_HN_holds :
    W4Thm11_1RowMGe .HN 6 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hcard : Nat.card (MulAut JH) ≤ 2 * Nat.card JH := by rw [card_aut, card_JH]
  have hpS : 19 ∣ Nat.card JH := by rw [card_JH]; norm_num
  have hρ : 3 * 6 < orderOf (2 : ZMod 19) + 3 := by
    rw [CFSG.QuasithinUnique.Setup.X1.orderOf_two_zmod_19]; norm_num
  have hρq : 2 * 6 < orderOf (2 : ZMod 19) + 2 := by
    rw [CFSG.QuasithinUnique.Setup.X1.orderOf_two_zmod_19]; norm_num
  refine W4Row.le_mParam_of_gen_out2 (S := JH) (k := 3) (p := 19) (q := 19) (ρ := 6) hW hLY hLn
    hF hq hO2 ?_ center_JH hcard (by norm_num) (by norm_num) (by norm_num) hpS hρ hρq jh_gen3
    jh_outer_dihedral
  exact e₀.trans hnEquivJ

theorem w4Thm11_1RowM4_HN_holds :
    W4Thm11_1RowM4 .HN :=
  w4Thm11_1RowMGe_HN_holds.mono (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
