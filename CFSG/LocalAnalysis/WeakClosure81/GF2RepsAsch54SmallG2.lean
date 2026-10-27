module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxG2Pair

import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2a
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512WrAbs
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallFour
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallG2CF
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallG2Solv
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxG2Core
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxG2Gen
import CFSG.Quasithin.Background.GoldschmidtShultLink
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch80G2

open Subgroup CFSG.Quasithin
open CFSG.Blueprint (LieModel)

open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)


variable {Q : Type} [Group Q]

def subgroupOfCentralizerEquiv (E : Subgroup Q) {z : Q} (hz : z ∈ E) :
    ↥(E.subgroupOf (centralizer ({z} : Set Q))) ≃* ↥(centralizer ({(⟨z, hz⟩ : ↥E)} : Set ↥E)) where
  toFun x := ⟨⟨x.1.1, mem_subgroupOf.1 x.2⟩,
    mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 x.1.2))⟩
  invFun k := ⟨⟨k.1.1, mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (mem_centralizer_singleton_iff.1 k.2))⟩, mem_subgroupOf.2 k.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem orderOf_mk_eq_two {E : Subgroup Q} {z : Q} (hzE : z ∈ E) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) : orderOf (⟨z, hzE⟩ : ↥E) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two]
    exact Subtype.ext hz2
  · intro h
    exact hz1 (congrArg Subtype.val h)


theorem not_hasCompFactor_centralizer_of_g2 [Finite Q] {E : Subgroup Q} [E.Normal]
    (hq : Group.IsSolvable (Q ⧸ E)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hE : LieModel ↥E .G2 0 r 1) {z : Q} (hzE : z ∈ E) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ¬ HasCompFactor (centralizer ({z} : Set Q)) IsCalL0 := by
  obtain ⟨F, _, _, S, -, -⟩ :=
    CFSG.GH74.GLS.IVK.GHInv.exists_shape_G2 hr hr2 hE _ (orderOf_mk_eq_two hzE hz2 hz1)
  refine not_hasCompFactor_of_subgroupOf
    (fun L _ _ hL => (isCalL0_nonabelian_not_sectionalTwoRankLE L hL).1) hq _ ?_
  exact not_isCompositionFactor_of_mulEquiv (subgroupOfCentralizerEquiv E hzE).symm
    (shape_not_isCompositionFactor isCalL0_nonabelian_not_sectionalTwoRankLE S)

theorem isSolvable_normalizer_of_g2 [Finite Q] {E : Subgroup Q} [E.Normal]
    (hq : Group.IsSolvable (Q ⧸ E)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hE : LieModel ↥E .G2 0 r 1) {z : Q} (hzE : z ∈ E) (hz2 : z * z = 1) (hz1 : z ≠ 1) {u : Q}
    (hu : u ∈ sqCent E z) (hu2 : u * u = 1) (huz : u ∉ zpowers z) :
    Group.IsSolvable ↥(normalizer ((zpowers z ⊔ zpowers u : Subgroup Q) : Set Q)) := by
  obtain ⟨F, _, _, S, hcard, hSz⟩ :=
    CFSG.GH74.GLS.IVK.GHInv.exists_shape_G2 hr hr2 hE _ (orderOf_mk_eq_two hzE hz2 hz1)
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hr.odd_of_ne_two hr2).pow
  let φ : ↥(centralizer ({(⟨z, hzE⟩ : ↥E)} : Set ↥E)) →* Q :=
    E.subtype.comp (centralizer ({(⟨z, hzE⟩ : ↥E)} : Set ↥E)).subtype
  have hφinj : Function.Injective φ := E.subtype_injective.comp (Subgroup.subtype_injective _)
  have hφz : φ S.z = z := congrArg Subtype.val hSz
  have hpair : SL2Pair E z (S.I₁.map φ) (S.I₂.map φ) :=
    sl2Pair_of_shape hodd hodd S φ hφinj hφz (fun k => (k : ↥E).2) fun g hgE hgz =>
      ⟨⟨⟨g, hgE⟩, mem_centralizer_singleton_iff.2 (Subtype.ext hgz)⟩, rfl⟩
  obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, haa, hbb, rfl⟩ := hpair.exists_mul hu hu2 huz
  have haa' : a * a = S.z := hφinj (by rw [map_mul, haa, hφz])
  have hbb' : b * b = S.z := hφinj (by rw [map_mul, hbb, hφz])
  have := shape_isSolvable_centralizer_mul S ha hb haa' hbb'
  set V := zpowers z ⊔ zpowers (φ a * φ b)
  have hzV : z ∈ V := mem_sup_left (mem_zpowers z)
  have huV : φ a * φ b ∈ V := mem_sup_right (mem_zpowers _)
  have hzu : z * (φ a * φ b) = φ a * φ b * z := by
    rw [← map_mul]
    exact (congrArg Subtype.val (mem_centralizer_singleton_iff.1 (a * b).2)).symm
  refine isSolvable_normalizer_of_card_le_four hq (natCard_sup_zpowers_le_four hz2 hu2 hzu) ?_
  set B := (centralizer ({a * b} : Set ↥(centralizer ({(⟨z, hzE⟩ : ↥E)} : Set ↥E)))).map φ
  have : Group.IsSolvable ↥B := solvable_of_surjective (MonoidHom.subgroupMap_surjective φ _)
  have hB : ∀ y ∈ E, y ∈ centralizer (V : Set Q) → y ∈ B := by
    intro y hyE hyV
    have hyz : y * z = z * y := ((mem_centralizer_iff.1 hyV) z hzV).symm
    refine ⟨⟨⟨y, hyE⟩, mem_centralizer_singleton_iff.2 (Subtype.ext hyz)⟩,
      mem_centralizer_singleton_iff.2 ?_, rfl⟩
    apply hφinj
    rw [map_mul, map_mul]
    exact ((mem_centralizer_iff.1 hyV) _ huV).symm
  let g : ↥(E.subgroupOf (centralizer (V : Set Q))) →* ↥B :=
    { toFun := fun x => ⟨x.1.1, hB _ (mem_subgroupOf.1 x.2) x.1.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine solvable_of_solvable_injective (f := g) fun x y h => ?_
  have h' : ((g x : ↥B) : Q) = ((g y : ↥B) : Q) := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

end CFSG.LocalAnalysis.WeakClosure81.Asch80G2

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)


theorem asch54Case_g2Prime (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    Asch54Case fun X _ => ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ CFSG.Blueprint.LieModel X .G2 0 r 1 := by
  intro Q _ _ L T hKQ hLn hLs hLnab hC hPL _ hT _
  obtain ⟨r, hr, hr2, hE⟩ := hPL
  have := hLn
  have hKL : CFSG.Open.IsKGroup ↥L := hKQ.of_injective L.subtype L.subtype_injective
  have hcat := hKL.isCatalogGroup_of_surjective ⊤ hLnab (Subgroup.subtype ⊤)
    (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have hq : Group.IsSolvable (Q ⧸ L) :=
    isSolvable_quotient_of_outSolvable L (by rw [hC]; exact bot_le)
      (CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer (hS _ hLs hLnab hcat))
  have hmem : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → ¬ HasCompFactor X IsCalL0 →
      X ≤ lGen IsCalL0 ⊤ T := fun X hTX hX hnot => le_iSup₂_of_le X ⟨hTX, hX, hnot⟩ le_rfl
  left
  refine Asch80G2.eq_top_of_gen hLn hr hr2 hE hC hT
    (fun _ _ hz hz' hz1 hz1' hne hc hZ =>
      Asch80G2.g2_sup_centralizer_eq_top hr hr2 hE hz hz' hz1 hz1' hne hc hZ) ?_ ?_ ?_
  · intro z hzL hz2 hz1 hTz hlt
    exact hmem _ hTz hlt (Asch80G2.not_hasCompFactor_centralizer_of_g2 hq hr hr2 hE hzL hz2 hz1)
  · intro z hzL hz2 hz1 _ u hu hu2 huz hTV hlt
    exact hmem _ hTV hlt (not_hasCompFactor_of_isSolvable
      (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
      (Asch80G2.isSolvable_normalizer_of_g2 hq hr hr2 hE hzL hz2 hz1 hu hu2 huz))
  · intro hlt
    exact hmem _ Asch80Wr.le_normalizer_inf_of_normal hlt
      (not_hasCompFactor_normalizer_inf isCalL0_nonabelian_not_sectionalTwoRankLE hq
        (CFSG.Quasithin.Shult.isSylowTwoOf_inf_normal hT))

end CFSG.LocalAnalysis.WeakClosure81

end
