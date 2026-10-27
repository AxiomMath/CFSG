module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBFourPermExcDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylInfDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageOfPosition
import CFSG.LocalAnalysis.StandardType.GGRCTransfer
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImage
import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylF4
import CFSG.LocalAnalysis.StandardType.GGSignedCoordConj
import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialRows
import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab
import CFSG.LocalAnalysis.StandardType.ZS.SignedOvergroup
import CFSG.LocalAnalysis.StandardType.ZS.SignedOvergroupIrred
import CFSG.LocalAnalysis.StandardType.ZS.SignedOvergroupMonomial
import CFSG.LocalAnalysis.StandardType.ZS.ExcB3
import CFSG.LocalAnalysis.StandardType.ZS.B3Chain
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem sgnAut_not_mem_dCoordinateBlock {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (i0 a : Fin n) : SpCoord.sgnAut a ∉ dCoordinateBlock n p i0 := by
  intro h
  exact sgnAut_not_mem_coordProdStab (Fact.out : p.Prime) hp2 a
    (dCoordinateBlock_le_coordProdStab i0 h)

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

omit [Finite G] in
private theorem closure_range_simple_eq {ι : Type} {M : CoxeterMatrix ι}
    {A : Subgroup (MulAut ↥Bs)} {e : M.Group ≃* ↥A} :
    Subgroup.closure (Set.range fun i : ι => ((e (M.simple i) : ↥A) : MulAut ↥Bs)) = A := by
  have h1 := map_closure_range_eq_of_simple M (A.subtype.comp e.toMonoidHom) M.simple
    (A.subtype.comp e.toMonoidHom) (fun i => rfl)
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top,
    Subgroup.range_subtype, MonoidHom.map_closure, ← Set.range_comp] at h1
  exact h1

private theorem reflGenerated_ggAInf (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) :
    GGReflGenerated p (ggAInf p B Bs x L D J) := by
  have hgen := closure_range_simple_eq (A := ggAutomizerJoin L Bs 𝒦) (M := M) (e := e)
  have hAle : ggAutomizerJoin L Bs 𝒦 ≤
      Subgroup.closure {φ | φ ∈ ggAInf p B Bs x L D J ∧ GGIsReflection p φ} := by
    rw [← hgen]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    exact Subgroup.subset_closure
      ⟨GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1 (e (M.simple i)).2, hP.2 i⟩
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun φ hφ => hφ.1)
  rw [ggAInf]
  refine sup_le ?_ (iSup_le fun y => iSup_le fun K => iSup_le fun hN => ?_)
  · exact le_sup_left.trans hAle
  · rw [hR.2.1 y K hN]
    exact (Subgroup.closure_le _).mpr fun φ hφ =>
      Subgroup.subset_closure ⟨ggAutomizer_le_ggAInf_of_nbr hN hφ.1, hφ.2⟩

omit [Finite G] in
private theorem card_ggAutomizerJoin_of_bSignedFull [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p) :
    Nat.card (ggAutomizerJoin L Bs 𝒦) = 2 ^ n * n.factorial := by
  have hcard : Nat.card (ggAutomizerJoin L Bs 𝒦) = Nat.card (bSignedFull n p) := by
    rw [← hK]
    exact (Subgroup.card_map_of_injective (MulAut.congr eta).injective).symm
  rw [hcard, bSignedFull_eq_signedPermSubgroup,
    SignedPermCount.card_signedPermSubgroup (Fact.out : p.Prime) hp2]

omit [Finite G] in
private theorem mem_of_congr_mem {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {A : Subgroup (MulAut ↥Bs)} {φ : MulAut ↥Bs}
    (h : MulAut.congr eta φ ∈ A.map (MulAut.congr eta).toMonoidHom) : φ ∈ A := by
  have h1 := (Subgroup.mem_map_equiv (f := MulAut.congr eta) (K := A)).mp h
  have h2 : (MulAut.congr eta).symm (MulAut.congr eta φ) = φ :=
    MulEquiv.symm_apply_apply (MulAut.congr eta) φ
  rwa [h2] at h1

omit [Finite G] in
private theorem dCoordinateBlock_fix_of_automizer_fix {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 : Fin n} {x : G} (hx : x ∈ Bs)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p i0)
    (hxfix : ∀ u ∈ ggAutomizer L Bs, u ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∀ u ∈ dCoordinateBlock n p i0, u (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
  intro u hu
  rw [← hL] at hu
  obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hu
  rw [← hvu]
  simpa [MulAut.congr_apply] using congrArg eta (hxfix v hv)

omit [Finite G] in
private theorem sgnAut_fix_of_dCoordinateBlock_fix [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    (hn : 3 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 a : Fin n}
    (hai0 : a ≠ i0) {x : G} (hx : x ∈ Bs)
    (hfix : ∀ u ∈ dCoordinateBlock n p i0, u (eta ⟨x, hx⟩) = eta ⟨x, hx⟩) :
    SpCoord.sgnAut a (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
  have hcoord :=
    (forall_dCoordinateBlock_fix_iff (Fact.out : p.Prime) hp2 hn i0 (eta ⟨x, hx⟩)).mp hfix
  funext k
  rw [SpCoord.sgnAut_apply]
  by_cases hk : k = a
  · rw [hk, Function.update_self, hcoord a hai0, inv_one]
  · rw [Function.update_of_ne hk]

private theorem false_of_dCoordinateBlock [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hx : x ∈ Bs)
    (hsat : ∀ φ ∈ ggAInf p B Bs x L D J, GGIsReflection p φ → φ ⟨x, hx⟩ = ⟨x, hx⟩ →
      φ ∈ ggAutomizer L Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 : Fin n}
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p i0) :
    False := by
  obtain ⟨a, hai0, -⟩ := SpCoord.coord_exists_ne_ne hn i0 i0
  let φ : MulAut ↥Bs := (MulAut.congr eta).symm (SpCoord.sgnAut a)
  have hcongr : MulAut.congr eta φ = SpCoord.sgnAut a := by
    rw [show φ = (MulAut.congr eta).symm (SpCoord.sgnAut a) from rfl]
    exact MulEquiv.apply_symm_apply (MulAut.congr eta) (SpCoord.sgnAut a)
  have hφA : φ ∈ ggAInf p B Bs x L D J := by
    refine GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1 ?_
    have hmem : MulAut.congr eta φ ∈
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom := by
      rw [hK, hcongr]
      exact Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
    have h1 := (Subgroup.mem_map_equiv (f := MulAut.congr eta)
      (K := ggAutomizerJoin L Bs 𝒦)).mp hmem
    rwa [hcongr] at h1
  have hφrefl : GGIsReflection p φ := by
    rw [show φ = (MulAut.congr eta).symm (SpCoord.sgnAut a) from rfl]
    exact ggIsReflection_congr_sgnAut hp2 eta a
  have hxfix : ∀ u ∈ ggAutomizer L Bs, u ⟨x, hx⟩ = ⟨x, hx⟩ :=
    ggRM_AL_fixes_x (ggSecFiveRouteCfg'_of_routeCfg hR) hx
  have hfixall := dCoordinateBlock_fix_of_automizer_fix eta hx hL hxfix
  have hsgnfix := sgnAut_fix_of_dCoordinateBlock_fix hp2 hn eta hai0 hx hfixall
  have hφx : φ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    apply eta.injective
    calc eta (φ ⟨x, hx⟩) = MulAut.congr eta φ (eta ⟨x, hx⟩) := by
          rw [MulAut.congr_apply]
          simp
      _ = SpCoord.sgnAut a (eta ⟨x, hx⟩) := by rw [hcongr]
      _ = eta ⟨x, hx⟩ := hsgnfix
  have hφL : φ ∈ ggAutomizer L Bs := hsat φ hφA hφrefl hφx
  have hsgn : SpCoord.sgnAut a ∈ dCoordinateBlock n p i0 := by
    rw [← hL, ← hcongr]
    exact Subgroup.mem_map_of_mem _ hφL
  exact sgnAut_not_mem_dCoordinateBlock hp2 i0 a hsgn

private theorem permAut_mem_aPermutationFull {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    SpCoord.permAut (p := p) σ ∈ aPermutationFull n p := by
  refine Equiv.Perm.swap_induction_on (motive := fun σ : Equiv.Perm (Fin n) =>
    SpCoord.permAut (p := p) σ ∈ aPermutationFull n p) σ ?_ ?_
  · change ggSpSigned_permAutHom p n 1 ∈ aPermutationFull n p
    rw [map_one]
    exact Subgroup.one_mem _
  · intro f x y hxy hf
    change ggSpSigned_permAutHom p n (Equiv.swap x y * f) ∈ aPermutationFull n p
    rw [map_mul]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨x, y, hxy, rfl⟩) hf

private theorem exists_signed_twist {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}
    (b : Module.Basis (Fin n) (ZMod p) U) {i j : Fin n} (hij : i ≠ j) {c : (ZMod p)ˣ}
    (hc : (c : ZMod p) = 1 ∨ (c : ZMod p) = -1) :
    ∃ (σ : Equiv.Perm (Fin n)) (c' : Fin n → ZMod p), (∀ k, c' k = 1 ∨ c' k = -1) ∧
      ∀ k, (ZS.diagMap p b (ZS.pairUnit p i j c) * ZS.permMap p b (Equiv.swap i j)) (b k) =
        c' k • b (σ k) := by
  refine ⟨Equiv.swap i j, fun k => (ZS.pairUnit p i j c (Equiv.swap i j k) : ZMod p), ?_, ?_⟩
  · intro k
    dsimp only
    rcases hc with hc | hc
    · have hc1 : c = 1 := Units.ext hc
      by_cases hki : Equiv.swap i j k = i
      · rw [hki]
        exact Or.inl (by simp [ZS.pairUnit, hc1])
      · by_cases hkj : Equiv.swap i j k = j
        · rw [hkj]
          exact Or.inl (by simp [ZS.pairUnit, hc1, Ne.symm hij])
        · exact Or.inl (by simp [ZS.pairUnit, hki, hkj])
    · have hc1 : c = -1 := Units.ext (by simpa using hc)
      by_cases hki : Equiv.swap i j k = i
      · rw [hki]
        exact Or.inr (by simp [ZS.pairUnit, hc1])
      · by_cases hkj : Equiv.swap i j k = j
        · rw [hkj]
          exact Or.inr (by simp [ZS.pairUnit, hc1, Ne.symm hij])
        · exact Or.inl (by simp [ZS.pairUnit, hki, hkj])
  · intro k
    rw [LinearEquiv.mul_apply, ZS.permMap_apply_basis, ZS.diagMap_apply_basis]

omit [Finite G] in
private theorem false_of_ggLin_eq_sign [Fact p.Prime] {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {A : Subgroup (MulAut ↥Bs)}
    (hK : A.map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {s : MulAut ↥Bs} (hsnot : s ∉ A) {i : Fin n}
    (hi : ggLin (p := p) (bCoordIota eta) s =
      ZS.diagMap p (Pi.basisFun (ZMod p) (Fin n)) (fun j => if j = i then -1 else 1)) :
    False := by
  have hs : s = (MulAut.congr eta).symm (SpCoord.sgnAut i) := by
    apply ggLin_injective (p := p) (bCoordIota eta)
    rw [hi, ← ggLin_bCoordIota_sgnAut eta i]
  have hcongrs : MulAut.congr eta s = SpCoord.sgnAut i := by
    rw [hs]
    exact MulEquiv.apply_symm_apply (MulAut.congr eta) (SpCoord.sgnAut i)
  refine hsnot (mem_of_congr_mem (A := A) eta ?_)
  rw [hK, hcongrs]
  exact Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)

omit [Finite G] in
private theorem false_of_twist_signed [Fact p.Prime] {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {A : Subgroup (MulAut ↥Bs)}
    (hK : A.map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {s : MulAut ↥Bs} (hsnot : s ∉ A) {i j : Fin n} (hij : i ≠ j) {c : (ZMod p)ˣ}
    (hcij : ggLin (p := p) (bCoordIota eta) s =
      ZS.diagMap p (Pi.basisFun (ZMod p) (Fin n)) (ZS.pairUnit p i j c) *
        ZS.permMap p (Pi.basisFun (ZMod p) (Fin n)) (Equiv.swap i j))
    (hcsigned : (c : ZMod p) = 1 ∨ (c : ZMod p) = -1) : False := by
  have hsigned : MulAut.congr eta s ∈ bSignedFull n p := by
    refine (congr_mem_bSignedFull_iff eta s).mpr ?_
    obtain ⟨σ, c', hc', hval⟩ :=
      exists_signed_twist (Pi.basisFun (ZMod p) (Fin n)) hij hcsigned
    exact ⟨σ, c', hc', fun k => by rw [hcij]; exact hval k⟩
  refine hsnot (mem_of_congr_mem (A := A) eta ?_)
  rw [hK]
  exact hsigned

private theorem card_ggAutomizerJoin_singleton_le [Fact p.Prime]
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {y : G} {K : Subgroup G}
    (hN : GGNbr p B x D J y K) :
    Nat.card (ggAutomizerJoin L Bs {K}) ≤ Nat.card (ggAutomizerJoin L Bs 𝒦) := by
  obtain ⟨-, -, hbest⟩ := hR.2.2.2
  have hsingle : GGNbrSet p B x D J {K} := by
    refine ⟨by simp, ?_⟩
    intro K' hK'
    rw [Finset.mem_singleton] at hK'
    subst hK'
    exact ⟨y, hN⟩
  have hW : GGWeylReflectionGroup p (ggAutomizerJoin L Bs {K}) := by
    rw [ggAutomizerJoin_singleton]
    exact hR.1.2.2.2.2.1 y K hN (hR.2.1 y K hN) (Or.inr hR.2.1)
  exact hbest {K} hsingle hW

private theorem false_of_twist_unsigned [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {y : G} {K : Subgroup G} (hN : GGNbr p B x D J y K)
    {s : MulAut ↥Bs} (hsK : s ∈ ggAutomizer K Bs) {i j : Fin n} (hij : i ≠ j)
    {c : (ZMod p)ˣ}
    (hcij : ggLin (p := p) (bCoordIota eta) s =
      ZS.diagMap p (Pi.basisFun (ZMod p) (Fin n)) (ZS.pairUnit p i j c) *
        ZS.permMap p (Pi.basisFun (ZMod p) (Fin n)) (Equiv.swap i j))
    (hc1 : (c : ZMod p) ≠ 1) (hc2 : (c : ZMod p) ≠ -1) : False := by
  let T := ggLin (p := p) (bCoordIota eta)
  let Jaut : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let H : Subgroup ((Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) := Jaut.map T
  have hpermH : ∀ σ : Equiv.Perm (Fin n),
      ZS.permMap p (Pi.basisFun (ZMod p) (Fin n)) σ ∈ H := by
    intro σ
    have hPσ : SpCoord.permAut σ ∈ aPermutationFull n p := permAut_mem_aPermutationFull σ
    have hmemL : (MulAut.congr eta).symm (SpCoord.permAut σ) ∈ ggAutomizer L Bs := by
      refine (Subgroup.mem_map_equiv (f := MulAut.congr eta)
        (K := ggAutomizer L Bs)).mp ?_
      rw [hL]
      exact hPσ
    rw [← ggLin_bCoordIota_permAut eta σ]
    exact Subgroup.mem_map_of_mem T (Subgroup.mem_sup_left hmemL)
  have htwistH : ZS.diagMap p (Pi.basisFun (ZMod p) (Fin n)) (ZS.pairUnit p i j c) *
      ZS.permMap p (Pi.basisFun (ZMod p) (Fin n)) (Equiv.swap i j) ∈ H := by
    rw [← hcij]
    exact Subgroup.mem_map_of_mem T
      (Subgroup.mem_sup_right (S := ggAutomizer L Bs) (T := ggAutomizer K Bs) hsK)
  have hlt := ZS.two_pow_mul_factorial_lt_card_of_twist_mem hn
    (Pi.basisFun (ZMod p) (Fin n)) hpermH hij hc1 hc2 htwistH
  have hcardH : Nat.card H = Nat.card Jaut :=
    (Nat.card_congr (Subgroup.equivMapOfInjective Jaut T
      (ggLin_injective (p := p) (bCoordIota eta)))).symm
  have hmax : Nat.card Jaut ≤ Nat.card (ggAutomizerJoin L Bs 𝒦) := by
    have hle := card_ggAutomizerJoin_singleton_le (p := p) hR hN
    rwa [ggAutomizerJoin_singleton] at hle
  have hcardK : Nat.card (ggAutomizerJoin L Bs 𝒦) = 2 ^ n * n.factorial :=
    card_ggAutomizerJoin_of_bSignedFull hp2 eta hK
  rw [hcardH] at hlt
  omega

private theorem false_of_aPermutationFull_of_monomial [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    (hn : 3 ≤ n) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hmon : ∀ φ ∈ ggAInf p B Bs x L D J, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i) =
        c i • Pi.basisFun (ZMod p) (Fin n) (σ i))
    (hnot : ¬ ggAInf p B Bs x L D J ≤ ggAutomizerJoin L Bs 𝒦) : False := by
  obtain ⟨y, K, hN, s, hsK, hsrefl, hsnot⟩ : ∃ (y : G) (K : Subgroup G)
      (hN : GGNbr p B x D J y K) (s : MulAut ↥Bs), s ∈ ggAutomizer K Bs ∧
        GGIsReflection p s ∧ s ∉ ggAutomizerJoin L Bs 𝒦 := by
    by_contra hcon
    apply hnot
    rw [ggAInf]
    refine sup_le le_sup_left (iSup_le fun y => iSup_le fun K => iSup_le fun hN => ?_)
    rw [hR.2.1 y K hN]
    refine (Subgroup.closure_le _).mpr fun φ hφ => ?_
    by_contra hφnot
    exact hcon ⟨y, K, hN, φ, hφ.1, hφ.2, hφnot⟩
  have hsAInf : s ∈ ggAInf p B Bs x L D J := ggAutomizer_le_ggAInf_of_nbr hN hsK
  have hsrefl' : ZS.IsRefl p (ggLin (p := p) (bCoordIota eta) s) :=
    (ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) s).mp hsrefl
  obtain ⟨σ, c, hc, hmon'⟩ := hmon s hsAInf
  rcases ZS.eq_sign_or_eq_twist_of_isRefl hp2 (Pi.basisFun (ZMod p) (Fin n)) hsrefl'
      ⟨σ, c, hc, hmon'⟩ with ⟨i, hi⟩ | ⟨i, j, hij, c, hcij⟩
  · exact false_of_ggLin_eq_sign (A := ggAutomizerJoin L Bs 𝒦) eta hK hsnot hi
  · by_cases hcsigned : (c : ZMod p) = 1 ∨ (c : ZMod p) = -1
    · exact false_of_twist_signed (A := ggAutomizerJoin L Bs 𝒦) eta hK hsnot hij hcij hcsigned
    · exact false_of_twist_unsigned hp2 hn hR eta hK hL hN hsK hij hcij
        (fun h => hcsigned (Or.inl h)) (fun h => hcsigned (Or.inr h))

end Config

section Assembly

variable {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
  {i0 : Fin n}

private theorem mem_ggAInf_of_congr_mem_bSignedFull
    (hKle : ggAutomizerJoin L Bs 𝒦 ≤ ggAInf p B Bs x L D J)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {u : MulAut (Fin n → Multiplicative (ZMod p))} (hu : u ∈ bSignedFull n p) :
    (MulAut.congr eta).symm u ∈ ggAInf p B Bs x L D J := by
  rw [← hK] at hu
  obtain ⟨a, ha, hEq⟩ := Subgroup.mem_map.mp hu
  rw [← hEq]
  change (MulAut.congr eta).symm ((MulAut.congr eta) a) ∈ ggAInf p B Bs x L D J
  rw [MulEquiv.symm_apply_apply]
  exact hKle ha

private theorem permMap_mem_map_ggAInf
    (hKle : ggAutomizerJoin L Bs 𝒦 ≤ ggAInf p B Bs x L D J)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (σ : Equiv.Perm (Fin n)) :
    ZS.permMap p (Pi.basisFun (ZMod p) (Fin n)) σ ∈
      (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)) := by
  let a := (MulAut.congr eta).symm (SpCoord.permAut σ)
  have ha : a ∈ ggAInf p B Bs x L D J :=
    mem_ggAInf_of_congr_mem_bSignedFull hKle hK (by
      rw [bSignedFull_eq_signedPermSubgroup]
      exact SpCoord.isSignedPerm_permAut σ)
  have hTa : ggLin (p := p) (bCoordIota eta) a = ZS.permMap p (Pi.basisFun (ZMod p) (Fin n)) σ :=
    ggLin_bCoordIota_permAut eta σ
  rw [← hTa]
  exact Subgroup.mem_map_of_mem _ ha

private theorem sgnMap_mem_map_ggAInf
    (hKle : ggAutomizerJoin L Bs 𝒦 ≤ ggAInf p B Bs x L D J)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (i : Fin n) :
    ZS.diagMap p (Pi.basisFun (ZMod p) (Fin n)) (fun j => if j = i then -1 else 1) ∈
      (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)) := by
  let a := (MulAut.congr eta).symm (SpCoord.sgnAut i)
  have ha : a ∈ ggAInf p B Bs x L D J :=
    mem_ggAInf_of_congr_mem_bSignedFull hKle hK
      (Subgroup.subset_closure (Or.inl ⟨i, rfl⟩))
  have hTa : ggLin (p := p) (bCoordIota eta) a =
      ZS.diagMap p (Pi.basisFun (ZMod p) (Fin n)) (fun j => if j = i then -1 else 1) :=
    ggLin_bCoordIota_sgnAut eta i
  rw [← hTa]
  exact Subgroup.mem_map_of_mem _ ha

private theorem reflGen_map_ggAInf
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp2 : p ≠ 2)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) :
    ZS.ReflGen p ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))) := by
  unfold ZS.ReflGen
  have h := reflGenerated_ggAInf hR hP
  unfold GGReflGenerated at h
  have hset : (ggLin (p := p) (bCoordIota eta) ''
      {φ | φ ∈ ggAInf p B Bs x L D J ∧ GGIsReflection p φ}) =
      {t | t ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)) ∧
        ZS.IsRefl p t} := by
    ext t
    constructor
    · rintro ⟨φ, ⟨hφ, hφrefl⟩, rfl⟩
      exact ⟨Subgroup.mem_map_of_mem _ hφ,
        (ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) φ).mp hφrefl⟩
    · rintro ⟨ht, htrefl⟩
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp ht
      exact ⟨φ, ⟨hφ, (ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) φ).mpr htrefl⟩, rfl⟩
  have h1 : (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)) =
      Subgroup.closure (ggLin (p := p) (bCoordIota eta) ''
        {φ | φ ∈ ggAInf p B Bs x L D J ∧ GGIsReflection p φ}) := by
    conv_lhs => rw [h]
    rw [MonoidHom.map_closure]
  have h2 : Subgroup.closure {t | t ∈ (ggAInf p B Bs x L D J).map
        (ggLin (p := p) (bCoordIota eta)) ∧ ZS.IsRefl p t} =
      Subgroup.closure (ggLin (p := p) (bCoordIota eta) ''
        {φ | φ ∈ ggAInf p B Bs x L D J ∧ GGIsReflection p φ}) := by
    conv_rhs => rw [hset]
  conv_lhs => rw [h1]
  exact h2.symm

private theorem dvd_card_map_ggAInf
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp2 : p ≠ 2)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p) :
    2 ^ n * n.factorial ∣
      Nat.card ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))) := by
  have hcardK := card_ggAutomizerJoin_of_bSignedFull hp2 eta hK
  have hle : ggAutomizerJoin L Bs 𝒦 ≤ ggAInf p B Bs x L D J :=
    GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1
  have hdv : Nat.card (ggAutomizerJoin L Bs 𝒦) ∣ Nat.card (ggAInf p B Bs x L D J) :=
    Subgroup.card_dvd_of_le hle
  rw [hcardK] at hdv
  have hcard : Nat.card ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))) =
      Nat.card (ggAInf p B Bs x L D J) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ (ggLin (p := p) (bCoordIota eta))
      (ggLin_injective _)).toEquiv).symm
  rwa [hcard]

private theorem noTransvection_map_ggAInf
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    ∀ τ ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)),
      Module.finrank (ZMod p) (LinearMap.range
        ((τ : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) - LinearMap.id)) = 1 →
        ∃ v, τ (τ v - v) ≠ τ v - v := by
  intro τ hτ hrank
  obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hτ
  by_contra h
  push Not at h
  refine hR.1.2.2.2.1 φ (ggRM_ainf_le_induced (G := G) hφ) ?_
  refine (ggIsTransvection_iff_ggLin (bCoordIota eta) φ).mpr ⟨hrank, ?_⟩
  rintro w ⟨v, hv⟩ a ha
  rw [Set.mem_singleton_iff] at ha
  rw [ha]
  rw [← hv]
  exact h v

omit [Finite G] in
private theorem signed_of_mem_automizer
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p) :
    ∀ φ ∈ ggAutomizer L Bs, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧
        ∀ i, ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i) =
          c i • Pi.basisFun (ZMod p) (Fin n) (σ i) := by
  intro φ hφ
  have hmem : MulAut.congr eta φ ∈ bSignedFull n p := by
    rw [← hK]
    exact Subgroup.mem_map_of_mem _
      (show φ ∈ ggAutomizerJoin L Bs 𝒦 from Subgroup.mem_sup_left hφ)
  exact (congr_mem_bSignedFull_iff eta φ).mp hmem

private theorem fix_x_of_bCoordinateBlock
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp2 : p ≠ 2) (hx : x ∈ Bs)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {φ : MulAut ↥Bs}
    (hfix : ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i0) =
      Pi.basisFun (ZMod p) (Fin n) i0) :
    φ ⟨x, hx⟩ = ⟨x, hx⟩ := by
  have hcfg' := ggSecFiveRouteCfg'_of_routeCfg hR
  have hALx := ggRM_AL_fixes_x hcfg' hx
  have hfixB : ∀ u ∈ bCoordinateBlock n p i0, u (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
    intro u hu
    rw [← hLB] at hu
    obtain ⟨a, ha, hEq⟩ := Subgroup.mem_map.mp hu
    have h1 : ((MulAut.congr eta).toMonoidHom a) (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
      change (eta.symm.trans (a.trans eta)) (eta ⟨x, hx⟩) = eta ⟨x, hx⟩
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        hALx a ha]
    rwa [hEq] at h1
  have hxcoord := (forall_bCoordinateBlock_fix_iff (Fact.out : p.Prime) hp2 i0
    (eta ⟨x, hx⟩)).mp hfixB
  exact fix_of_coord_single eta hxcoord hfix

private theorem fix_x_of_aPermutationFull
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hx : x ∈ Bs)
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {φ : MulAut ↥Bs}
    (hfix : ggLin (p := p) (bCoordIota eta) φ (∑ i, Pi.basisFun (ZMod p) (Fin n) i) =
      ∑ i, Pi.basisFun (ZMod p) (Fin n) i) :
    φ ⟨x, hx⟩ = ⟨x, hx⟩ := by
  have hcfg' := ggSecFiveRouteCfg'_of_routeCfg hR
  have hALx := ggRM_AL_fixes_x hcfg' hx
  have hfixA : ∀ u ∈ aPermutationFull n p, u (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
    intro u hu
    rw [← hLA] at hu
    obtain ⟨a, ha, hEq⟩ := Subgroup.mem_map.mp hu
    have h1 : ((MulAut.congr eta).toMonoidHom a) (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
      change (eta.symm.trans (a.trans eta)) (eta ⟨x, hx⟩) = eta ⟨x, hx⟩
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        hALx a ha]
    rwa [hEq] at h1
  have hxconst := (forall_aPermutationFull_fix_iff (eta ⟨x, hx⟩)).mp hfixA
  exact fix_of_coord_const eta hxconst hfix

omit [Finite G] in
private theorem false_of_refl_not_monomial
    (hLsigned : ∀ φ ∈ ggAutomizer L Bs, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧
        ∀ i, ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i) =
          c i • Pi.basisFun (ZMod p) (Fin n) (σ i))
    {φ : MulAut ↥Bs} (hφL : φ ∈ ggAutomizer L Bs)
    {r : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)}
    (hTφ : ggLin (p := p) (bCoordIota eta) φ = r)
    (hrmon : ¬ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      ∀ i, r (Pi.basisFun (ZMod p) (Fin n) i) =
        c i • Pi.basisFun (ZMod p) (Fin n) (σ i)) : False := by
  obtain ⟨σ, c, -, hσc⟩ := hLsigned φ hφL
  rw [hTφ] at hσc
  exact hrmon ⟨σ, c, hσc⟩

omit [Finite G] in
private theorem false_of_twist_of_bCoordinateBlock
    (hLsigned : ∀ φ ∈ ggAutomizer L Bs, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧
        ∀ i, ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i) =
          c i • Pi.basisFun (ZMod p) (Fin n) (σ i))
    {φ : MulAut ↥Bs} (hφL : φ ∈ ggAutomizer L Bs)
    {a1 a2 : Fin n} (ha12 : a1 ≠ a2) {ζ : (ZMod p)ˣ} (hζ1 : (ζ : ZMod p) ≠ 1)
    (hζ2 : (ζ : ZMod p) ≠ -1)
    (hTφ : ggLin (p := p) (bCoordIota eta) φ =
      ZS.diagMap p (Pi.basisFun (ZMod p) (Fin n)) (ZS.pairUnit p a1 a2 ζ) *
        ZS.permMap p (Pi.basisFun (ZMod p) (Fin n)) (Equiv.swap a1 a2)) : False := by
  obtain ⟨σ, c, hc, hσc⟩ := hLsigned φ hφL
  rw [hTφ] at hσc
  exact ZS.twist_not_signed (Pi.basisFun (ZMod p) (Fin n)) ha12 hζ1 hζ2 ⟨σ, c, hc, hσc⟩

private theorem false_of_twist_of_aPermutationFull
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hmon : ∀ a ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)),
      ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
        ∀ i, a ((Pi.basisFun (ZMod p) (Fin n)) i) = c i • (Pi.basisFun (ZMod p) (Fin n)) (σ i))
    {a1 a2 : Fin n} (ha12 : a1 ≠ a2) {ζ : (ZMod p)ˣ} (hζ1 : (ζ : ZMod p) ≠ 1)
    (hζ2 : (ζ : ZMod p) ≠ -1)
    (ht : ZS.diagMap p (Pi.basisFun (ZMod p) (Fin n)) (ZS.pairUnit p a1 a2 ζ) *
        ZS.permMap p (Pi.basisFun (ZMod p) (Fin n)) (Equiv.swap a1 a2) ∈
      (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))) : False := by
  obtain ⟨φ, hφ, hφr⟩ := Subgroup.mem_map.mp ht
  have hmonAinf : ∀ ψ ∈ ggAInf p B Bs x L D J,
      ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
        ∀ i, ggLin (p := p) (bCoordIota eta) ψ (Pi.basisFun (ZMod p) (Fin n) i) =
          c i • Pi.basisFun (ZMod p) (Fin n) (σ i) := by
    intro ψ hψ
    exact hmon (ggLin (p := p) (bCoordIota eta) ψ) (Subgroup.mem_map_of_mem _ hψ)
  have hnot : ¬ ggAInf p B Bs x L D J ≤ ggAutomizerJoin L Bs 𝒦 := by
    intro hle
    have hcongr : MulAut.congr eta φ ∈ bSignedFull n p := by
      rw [← hK]
      exact Subgroup.mem_map_of_mem _ (hle hφ)
    obtain ⟨σ, c, hc, hσc⟩ := (congr_mem_bSignedFull_iff eta φ).mp hcongr
    rw [hφr] at hσc
    exact ZS.twist_not_signed (Pi.basisFun (ZMod p) (Fin n)) ha12 hζ1 hζ2 ⟨σ, c, hc, hσc⟩
  exact false_of_aPermutationFull_of_monomial hp2 hn hR eta hK hLA hmonAinf hnot

private theorem weyl_of_bCoordinateBlock
    (hp2 : p ≠ 2) (hn : 5 ≤ n)
    (hfam : ZS.Family p ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))))
    (hperm : ∀ σ, ZS.permMap p (Pi.basisFun (ZMod p) (Fin n)) σ ∈
      (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)))
    (hsgn : ∀ i, ZS.diagMap p (Pi.basisFun (ZMod p) (Fin n)) (fun j => if j = i then -1 else 1) ∈
      (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)))
    (hdvd : 2 ^ n * n.factorial ∣
      Nat.card ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))))
    (htv : ∀ τ ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)),
      Module.finrank (ZMod p) (LinearMap.range
        ((τ : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) - LinearMap.id)) = 1 →
        ∃ v, τ (τ v - v) ≠ τ v - v)
    (hLsigned : ∀ φ ∈ ggAutomizer L Bs, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧
        ∀ i, ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i) =
          c i • Pi.basisFun (ZMod p) (Fin n) (σ i))
    (hsatB : ∀ φ ∈ ggAInf p B Bs x L D J,
      ZS.IsRefl p (ggLin (p := p) (bCoordIota eta) φ) →
        ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i0) =
          Pi.basisFun (ZMod p) (Fin n) i0 → φ ∈ ggAutomizer L Bs) :
    GGWeylReflectionGroup p (ggAInf p B Bs x L D J) := by
  rcases ZS.linWeyl_or_reflFix_or_twist_of_signed_le hp2 hn
    (Pi.basisFun (ZMod p) (Fin n)) hfam hperm hsgn hdvd htv i0 with
    hW | ⟨r, hr, hrefl, hri0, -, hrmon⟩ | ⟨-, htw⟩
  · exact ggRC_weylReflGroup_of_linWeyl (bCoordIota eta) _ hW
  · obtain ⟨φ, hφ, hφr⟩ := Subgroup.mem_map.mp hr
    have hφL := hsatB φ hφ (by rw [hφr]; exact hrefl) (by rw [hφr]; exact hri0)
    exact (false_of_refl_not_monomial hLsigned hφL hφr hrmon).elim
  · obtain ⟨a1, ha1, -⟩ := Fin.exists_ne_and_ne_of_two_lt i0 i0 (by omega : 2 < n)
    obtain ⟨a2, ha2, ha21⟩ := Fin.exists_ne_and_ne_of_two_lt i0 a1 (by omega : 2 < n)
    obtain ⟨ζ, hζ1, hζ2, ht⟩ := htw a1 a2 (Ne.symm ha21)
    obtain ⟨φ, hφ, hφr⟩ := Subgroup.mem_map.mp ht
    have hφL := hsatB φ hφ
      (by rw [hφr]; exact
        ZS.isRefl_diagMap_mul_permMap_swap (Pi.basisFun (ZMod p) (Fin n)) (Ne.symm ha21) ζ)
      (by rw [hφr]; exact
        ZS.twist_apply_basis_of_ne (Pi.basisFun (ZMod p) (Fin n)) (Ne.symm ha1) (Ne.symm ha2) ζ)
    exact (false_of_twist_of_bCoordinateBlock hLsigned hφL (Ne.symm ha21) hζ1 hζ2 hφr).elim

private theorem weyl_of_aPermutationFull
    (i0 : Fin n) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp2 : p ≠ 2) (hn : 5 ≤ n)
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hfam : ZS.Family p ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))))
    (hperm : ∀ σ, ZS.permMap p (Pi.basisFun (ZMod p) (Fin n)) σ ∈
      (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)))
    (hsgn : ∀ i, ZS.diagMap p (Pi.basisFun (ZMod p) (Fin n)) (fun j => if j = i then -1 else 1) ∈
      (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)))
    (hdvd : 2 ^ n * n.factorial ∣
      Nat.card ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))))
    (htv : ∀ τ ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)),
      Module.finrank (ZMod p) (LinearMap.range
        ((τ : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) - LinearMap.id)) = 1 →
        ∃ v, τ (τ v - v) ≠ τ v - v)
    (hLsigned : ∀ φ ∈ ggAutomizer L Bs, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧
        ∀ i, ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i) =
          c i • Pi.basisFun (ZMod p) (Fin n) (σ i))
    (hsatA : ∀ φ ∈ ggAInf p B Bs x L D J,
      ZS.IsRefl p (ggLin (p := p) (bCoordIota eta) φ) →
        ggLin (p := p) (bCoordIota eta) φ (∑ i, Pi.basisFun (ZMod p) (Fin n) i) =
          ∑ i, Pi.basisFun (ZMod p) (Fin n) i →
          φ ∈ ggAutomizer L Bs) :
    GGWeylReflectionGroup p (ggAInf p B Bs x L D J) := by
  rcases ZS.linWeyl_or_reflFix_or_twist_of_signed_le hp2 hn
    (Pi.basisFun (ZMod p) (Fin n)) hfam hperm hsgn hdvd htv i0 with
    hW | ⟨r, hr, hrefl, -, hrsum, hrmon⟩ | ⟨hmon, htw⟩
  · exact ggRC_weylReflGroup_of_linWeyl (bCoordIota eta) _ hW
  · obtain ⟨φ, hφ, hφr⟩ := Subgroup.mem_map.mp hr
    have hφL := hsatA φ hφ (by rw [hφr]; exact hrefl) (by rw [hφr]; exact hrsum)
    exact (false_of_refl_not_monomial hLsigned hφL hφr hrmon).elim
  · let a1 : Fin n := ⟨0, by omega⟩
    let a2 : Fin n := ⟨1, by omega⟩
    have ha12 : a1 ≠ a2 := by
      intro h
      have h' : (a1 : ℕ) = (a2 : ℕ) := congrArg Fin.val h
      simp only [a1, a2] at h'
      omega
    obtain ⟨ζ, hζ1, hζ2, ht⟩ := htw a1 a2 ha12
    exact (false_of_twist_of_aPermutationFull hR hp2 (by omega) hK hLA hmon ha12 hζ1 hζ2 ht).elim

private theorem sat_of_bCoordinateBlock
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp2 : p ≠ 2) (hx : x ∈ Bs)
    (hsat : ∀ φ ∈ ggAInf p B Bs x L D J, GGIsReflection p φ →
      φ ⟨x, hx⟩ = ⟨x, hx⟩ → φ ∈ ggAutomizer L Bs)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    ∀ φ ∈ ggAInf p B Bs x L D J, ZS.IsRefl p (ggLin (p := p) (bCoordIota eta) φ) →
      ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i0) =
        Pi.basisFun (ZMod p) (Fin n) i0 → φ ∈ ggAutomizer L Bs := by
  intro φ hφ hrefl hfix
  exact hsat φ hφ ((ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) φ).mpr hrefl)
    (fix_x_of_bCoordinateBlock hR hp2 hx hLB hfix)

private theorem sat_of_aPermutationFull
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp2 : p ≠ 2) (hx : x ∈ Bs)
    (hsat : ∀ φ ∈ ggAInf p B Bs x L D J, GGIsReflection p φ →
      φ ⟨x, hx⟩ = ⟨x, hx⟩ → φ ∈ ggAutomizer L Bs)
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    ∀ φ ∈ ggAInf p B Bs x L D J, ZS.IsRefl p (ggLin (p := p) (bCoordIota eta) φ) →
      ggLin (p := p) (bCoordIota eta) φ (∑ i, Pi.basisFun (ZMod p) (Fin n) i) =
        ∑ i, Pi.basisFun (ZMod p) (Fin n) i → φ ∈ ggAutomizer L Bs := by
  intro φ hφ hrefl hfix
  exact hsat φ hφ ((ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) φ).mpr hrefl)
    (fix_x_of_aPermutationFull hR hx hLA hfix)

end Assembly

private theorem ggSecFiveWeylInfAt_BGe5_aux
    (hPos : BOriginalPositionInput) (hUse : ZS.UseInput) (hSat : GGSecFiveBReflSatInput)
    (G : Type) [Group G] [Finite G] (p : ℕ) [fact : Fact p.Prime]
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (𝒦 : Finset (Subgroup G))
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (ιM : Type) (M : CoxeterMatrix ιM) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixBGe 5 M) :
    GGWeylReflectionGroup p (ggAInf p B Bs x L D J) := by
  obtain ⟨-, -, hx, -, -⟩ := hR.1.1.tableB_facts
  obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hsat := hSat G p B Bs x L D J 𝒦 hR ιM M e hP hM hx
  obtain ⟨n, e', hn5, rfl⟩ := hM
  obtain ⟨-, eta, i0, hK, hL⟩ :=
    hPos G p B Bs x L D J 𝒦 hR n (by omega) _ (GGCoxeterPres.of_reindex_B (by omega) hP)
  set T := ggLin (p := p) (bCoordIota eta) with hT
  set b := Pi.basisFun (ZMod p) (Fin n) with hb
  set A := (ggAInf p B Bs x L D J).map T with hA
  have hKle : ggAutomizerJoin L Bs 𝒦 ≤ ggAInf p B Bs x L D J :=
    GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1
  have hperm : ∀ σ, ZS.permMap p b σ ∈ A := fun σ =>
    permMap_mem_map_ggAInf (eta := eta) hKle hK σ
  have hsgn : ∀ i, ZS.diagMap p b (fun j => if j = i then -1 else 1) ∈ A := fun i =>
    sgnMap_mem_map_ggAInf (eta := eta) hKle hK i
  have hgen : ZS.ReflGen p A :=
    reflGen_map_ggAInf (eta := eta) hR hp2 (GGCoxeterPres.of_reindex_B (by omega) hP)
  have hirr : ZS.AbsIrred p A := ZS.absIrred_of_signed_le hp2 (by omega) b hperm hsgn
  have hfam : ZS.Family p A :=
    hUse p (Fin n → ZMod p) A hp2 (by rw [Module.finrank_fin_fun]; omega) hgen hirr
  have hdvd : 2 ^ n * n.factorial ∣ Nat.card A :=
    dvd_card_map_ggAInf (eta := eta) hR hp2 hK
  have htv : ∀ τ ∈ A,
      Module.finrank (ZMod p) (LinearMap.range ((τ : (Fin n → ZMod p) →ₗ[ZMod p] _) -
        LinearMap.id)) = 1 → ∃ v, τ (τ v - v) ≠ τ v - v :=
    noTransvection_map_ggAInf (eta := eta) hR
  have hLsigned : ∀ φ ∈ ggAutomizer L Bs, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, T φ (b i) = c i • b (σ i) :=
    signed_of_mem_automizer (eta := eta) hK
  rcases hL with hLB | hLD | hLA
  · have hsatB := sat_of_bCoordinateBlock hR hp2 hx hsat hLB
    exact weyl_of_bCoordinateBlock hp2 hn5 hfam hperm hsgn hdvd htv hLsigned hsatB
  · exact (false_of_dCoordinateBlock hp2 (by omega) hR hx hsat eta hK hLD).elim
  · have hsatA := sat_of_aPermutationFull hR hp2 hx hsat hLA
    exact weyl_of_aPermutationFull i0 hR hp2 hn5 hLA hK hfam hperm hsgn hdvd htv
      hLsigned hsatA

theorem ggSecFiveWeylInfAt_BGe5_of_inputs (hPos : BOriginalPositionInput) (hUse : ZS.UseInput)
    (hSat : GGSecFiveBReflSatInput) : GGSecFiveWeylInfAt (GGIsWeylMatrixBGe 5) := by
  intro G _ _ p B Bs x L D J 𝒦 hR ιM M e hP hM
  obtain ⟨hp, -, -, -, -⟩ := hR.1.1.tableB_facts
  exact ggSecFiveWeylInfAt_BGe5_aux (fact := ⟨hp⟩) hPos hUse hSat G p B Bs x L D J 𝒦 hR
    ιM M e hP hM

theorem ggSecFiveWeylInfAt_B_of_ge_five_of_four (hPos : BOriginalPositionInput)
    (h5 : GGSecFiveWeylInfAt (GGIsWeylMatrixBGe 5)) (h4 : GGSecFiveWeylInfAt GGIsWeylMatrixBFour) :
    GGSecFiveWeylInfAt GGIsWeylMatrixB := by
  intro G _ _ p B Bs x L D J 𝒦 hR ιM M e hP hM
  obtain ⟨n, e', hn2, rfl⟩ := hM
  have hn4 : 4 ≤ n :=
    (hPos G p B Bs x L D J 𝒦 hR n hn2 _ (GGCoxeterPres.of_reindex_B hn2 hP)).1
  rcases Nat.lt_or_ge n 5 with hn | hn
  · obtain rfl : n = 4 := by omega
    exact h4 G p B Bs x L D J 𝒦 hR ιM _ e hP ⟨e', rfl⟩
  · exact h5 G p B Bs x L D J 𝒦 hR ιM _ e hP ⟨n, e', hn, rfl⟩

section DegreeFour

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {i0 : Fin 4}

private theorem exists_refl_inv_of_bCoordinateBlock (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hp2 : p ≠ 2) (hx : x ∈ Bs)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0) :
    ∃ t ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection p t ∧ t ⟨x, hx⟩ = ⟨x, hx⟩⁻¹ := by
  let t : MulAut ↥Bs := (MulAut.congr eta).symm (SpCoord.sgnAut i0)
  have htK : t ∈ ggAutomizerJoin L Bs 𝒦 := by
    refine mem_of_congr_mem eta ?_
    simp only [t, MulEquiv.apply_symm_apply, hK]
    exact Subgroup.subset_closure (Or.inl ⟨i0, rfl⟩)
  have htrefl : GGIsReflection p t := by
    dsimp [t]
    exact ggIsReflection_congr_sgnAut hp2 eta i0
  have hALx : ∀ u ∈ ggAutomizer L Bs, u ⟨x, hx⟩ = ⟨x, hx⟩ :=
    ggRM_AL_fixes_x (ggSecFiveRouteCfg'_of_routeCfg hR) hx
  have hfixB : ∀ u ∈ bCoordinateBlock 4 p i0, u (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
    intro u hu
    rw [← hLB] at hu
    obtain ⟨a, ha, hEq⟩ := Subgroup.mem_map.mp hu
    have h1 : ((MulAut.congr eta).toMonoidHom a) (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
      change (eta.symm.trans (a.trans eta)) (eta ⟨x, hx⟩) = eta ⟨x, hx⟩
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hALx a ha]
    rwa [hEq] at h1
  have hxcoord : ∀ k, k ≠ i0 → eta ⟨x, hx⟩ k = 1 :=
    (forall_bCoordinateBlock_fix_iff (Fact.out : p.Prime) hp2 i0 (eta ⟨x, hx⟩)).mp hfixB
  have hsgn : SpCoord.sgnAut i0 (eta ⟨x, hx⟩) = (eta ⟨x, hx⟩)⁻¹ := by
    funext k
    by_cases hk : k = i0
    · subst hk
      simp [SpCoord.sgnAut_apply, Pi.inv_apply]
    · rw [SpCoord.sgnAut_apply, Function.update_of_ne hk]
      simp [Pi.inv_apply, hxcoord k hk]
  have htapply : eta (t ⟨x, hx⟩) = eta ⟨x, hx⟩⁻¹ := by
    have ht_eq : MulAut.congr eta t = SpCoord.sgnAut i0 := by
      dsimp [t]
      rw [MulEquiv.apply_symm_apply]
    have h1 : MulAut.congr eta t (eta ⟨x, hx⟩) = eta (t ⟨x, hx⟩) := by
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [← h1, ht_eq, hsgn, map_inv]
  exact ⟨t, htK, htrefl, eta.injective htapply⟩

private theorem exists_refl_inv_of_dCoordinateBlock (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hp2 : p ≠ 2) (hx : x ∈ Bs)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (hLD : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock 4 p i0) :
    ∃ t ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection p t ∧ t ⟨x, hx⟩ = ⟨x, hx⟩⁻¹ := by
  let t : MulAut ↥Bs := (MulAut.congr eta).symm (SpCoord.sgnAut i0)
  have htK : t ∈ ggAutomizerJoin L Bs 𝒦 := by
    refine mem_of_congr_mem eta ?_
    simp only [t, MulEquiv.apply_symm_apply, hK]
    exact Subgroup.subset_closure (Or.inl ⟨i0, rfl⟩)
  have htrefl : GGIsReflection p t := by
    dsimp [t]
    exact ggIsReflection_congr_sgnAut hp2 eta i0
  have hALx : ∀ u ∈ ggAutomizer L Bs, u ⟨x, hx⟩ = ⟨x, hx⟩ :=
    ggRM_AL_fixes_x (ggSecFiveRouteCfg'_of_routeCfg hR) hx
  have hfixD : ∀ u ∈ dCoordinateBlock 4 p i0, u (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
    intro u hu
    rw [← hLD] at hu
    obtain ⟨a, ha, hEq⟩ := Subgroup.mem_map.mp hu
    have h1 : ((MulAut.congr eta).toMonoidHom a) (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
      change (eta.symm.trans (a.trans eta)) (eta ⟨x, hx⟩) = eta ⟨x, hx⟩
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hALx a ha]
    rwa [hEq] at h1
  have hxcoord : ∀ k, k ≠ i0 → eta ⟨x, hx⟩ k = 1 :=
    (forall_dCoordinateBlock_fix_iff (Fact.out : p.Prime) hp2 (by norm_num : 3 ≤ 4) i0
      (eta ⟨x, hx⟩)).mp hfixD
  have hsgn : SpCoord.sgnAut i0 (eta ⟨x, hx⟩) = (eta ⟨x, hx⟩)⁻¹ := by
    funext k
    by_cases hk : k = i0
    · subst hk
      simp [SpCoord.sgnAut_apply, Pi.inv_apply]
    · rw [SpCoord.sgnAut_apply, Function.update_of_ne hk]
      simp [Pi.inv_apply, hxcoord k hk]
  have htapply : eta (t ⟨x, hx⟩) = eta ⟨x, hx⟩⁻¹ := by
    have ht_eq : MulAut.congr eta t = SpCoord.sgnAut i0 := by
      dsimp [t]
      rw [MulEquiv.apply_symm_apply]
    have h1 : MulAut.congr eta t (eta ⟨x, hx⟩) = eta (t ⟨x, hx⟩) := by
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [← h1, ht_eq, hsgn, map_inv]
  exact ⟨t, htK, htrefl, eta.injective htapply⟩

private theorem equivFun_of_action_basis {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin n) (ZMod p) U) {g : U ≃ₗ[ZMod p] U} (σ : Equiv.Perm (Fin n))
    (c : Fin n → ZMod p) (hg : ∀ i, g (f i) = c i • f (σ i))
    {k : Fin n} (hfix : g (f k) = f k) (v : U) :
    f.equivFun (g v) k = f.equivFun v k := by
  have hfixk : f.equivFun (g (f k)) k = f.equivFun (f k) k := by rw [hfix]
  have hcoordk : c k * (if σ k = k then 1 else 0) = 1 := by
    have h1 : f.equivFun (g (f k)) k = c k * (if σ k = k then 1 else 0) := by
      rw [hg k, map_smul, Pi.smul_apply, Module.Basis.equivFun_self, smul_eq_mul]
    rw [h1, Module.Basis.equivFun_self] at hfixk
    simpa using hfixk
  have hσk : σ k = k := by
    by_cases h : σ k = k
    · exact h
    · exfalso
      rw [if_neg h, mul_zero] at hcoordk
      exact zero_ne_one hcoordk
  have hck : c k = 1 := by
    rw [if_pos hσk, mul_one] at hcoordk
    exact hcoordk
  have hsum : g v = ∑ i, (f.equivFun v i * c i) • f (σ i) := by
    conv_lhs => rw [← f.sum_equivFun v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hg i, smul_smul]
  have hreindex : (∑ i, (f.equivFun v i * c i) • f (σ i)) =
      ∑ j, (f.equivFun v (σ.symm j) * c (σ.symm j)) • f j := by
    refine Fintype.sum_equiv σ _ _ fun i => ?_
    simp only [Equiv.symm_apply_apply]
  have hcoord : f.equivFun (g v) =
      fun j => f.equivFun v (σ.symm j) * c (σ.symm j) := by
    rw [hsum, hreindex]
    simpa only [Module.Basis.equivFun_apply] using
      f.repr_sum_self (fun j => f.equivFun v (σ.symm j) * c (σ.symm j))
  have hσsymm : σ.symm k = k := by
    rw [Equiv.symm_apply_eq]
    exact hσk.symm
  simpa [hσsymm, hck] using congrFun hcoord k

private theorem exists_fixed_basis_of_refl_form {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin 4) (ZMod p) U) {r : U ≃ₗ[ZMod p] U}
    (h : (∃ i : Fin 4, r = ZS.diagMap p f (fun j => if j = i then -1 else 1)) ∨
      ∃ (i j : Fin 4), i ≠ j ∧ ∃ c : (ZMod p)ˣ,
        r = ZS.diagMap p f (ZS.pairUnit p i j c) * ZS.permMap p f (Equiv.swap i j)) :
    ∃ k : Fin 4, r (f k) = f k := by
  rcases h with ⟨i, rfl⟩ | ⟨i, j, _, c, rfl⟩
  · have hcard : 1 < Fintype.card (Fin 4) := by
      rw [Fintype.card_fin]
      norm_num
    obtain ⟨k, hki⟩ := Fintype.exists_ne_of_one_lt_card hcard i
    exact ⟨k, by rw [ZS.diagMap_apply_basis, if_neg hki]; simp⟩
  · have hk : ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by
      by_contra h
      simp only [not_exists, not_and, not_not] at h
      have hsub : (Finset.univ : Finset (Fin 4)) ⊆ ({i, j} : Finset (Fin 4)) := by
        intro k _
        by_cases hki : k = i
        · simp [hki]
        · have hkj : k = j := h k hki
          simp [hkj]
      have h1 : 4 ≤ ({i, j} : Finset (Fin 4)).card := by
        simpa using Finset.card_le_card hsub
      have h2 : ({i, j} : Finset (Fin 4)).card ≤ 2 := by
        simpa using Finset.card_insert_le i ({j} : Finset (Fin 4))
      omega
    obtain ⟨k, hki, hkj⟩ := hk
    exact ⟨k, by
      rw [LinearEquiv.mul_apply, ZS.permMap_apply_basis,
        Equiv.swap_apply_of_ne_of_ne hki hkj, ZS.diagMap_apply_basis]
      simp [ZS.pairUnit, hki, hkj]⟩

private theorem coord_const_of_aPermutationFull (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hx : x ∈ Bs)
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p) :
    (∀ a b, eta ⟨x, hx⟩ a = eta ⟨x, hx⟩ b) ∧
      ∀ k, bCoordIota eta (Additive.ofMul ⟨x, hx⟩) k ≠ 0 := by
  have hxne : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hALx : ∀ u ∈ ggAutomizer L Bs, u ⟨x, hx⟩ = ⟨x, hx⟩ :=
    ggRM_AL_fixes_x (ggSecFiveRouteCfg'_of_routeCfg hR) hx
  have hfixA : ∀ u ∈ aPermutationFull 4 p, u (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
    intro u hu
    rw [← hLA] at hu
    obtain ⟨a, ha, hEq⟩ := Subgroup.mem_map.mp hu
    have h1 : ((MulAut.congr eta).toMonoidHom a) (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
      change (eta.symm.trans (a.trans eta)) (eta ⟨x, hx⟩) = eta ⟨x, hx⟩
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hALx a ha]
    rwa [hEq] at h1
  have hxconst : ∀ a b, eta ⟨x, hx⟩ a = eta ⟨x, hx⟩ b :=
    (forall_aPermutationFull_fix_iff (eta ⟨x, hx⟩)).mp hfixA
  refine ⟨hxconst, fun k hk => ?_⟩
  have hk1 : eta ⟨x, hx⟩ k = 1 := by
    have h := hk
    rw [bCoordIota_apply_ofMul] at h
    simpa using h
  have heta1 : eta ⟨x, hx⟩ = 1 := by
    funext l
    rw [hxconst l k, hk1]
    rfl
  have hx1 : (⟨x, hx⟩ : ↥Bs) = 1 := eta.injective (by simpa using heta1)
  exact hxne (by simpa using congrArg Subtype.val hx1)

theorem GGSecFiveRouteCfg.not_exists_refl_inv_of_aPermutationFull
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hp2 : p ≠ 2) (hx : x ∈ Bs)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p) :
    ¬ ∃ t ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection p t ∧ t ⟨x, hx⟩ = ⟨x, hx⟩⁻¹ := by
  obtain ⟨-, hv_ne⟩ := coord_const_of_aPermutationFull hR hx hLA
  rintro ⟨t, htK, htrefl, htinv⟩
  set T : (Fin 4 → ZMod p) ≃ₗ[ZMod p] (Fin 4 → ZMod p) :=
    ggLin (p := p) (bCoordIota eta) t
  have hTrefl : ZS.IsRefl p T :=
    (ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) t).mp htrefl
  have hmem : MulAut.congr eta t ∈ bSignedFull 4 p := by
    rw [← hK]
    exact Subgroup.mem_map_of_mem _ htK
  obtain ⟨σ, c, hc, hform⟩ := (congr_mem_bSignedFull_iff eta t).mp hmem
  have hcne : ∀ i, c i ≠ 0 := fun i => by rcases hc i with h | h <;> simp [h]
  have hk : ∃ k, T (Pi.basisFun (ZMod p) (Fin 4) k) = Pi.basisFun (ZMod p) (Fin 4) k := by
    rcases ZS.eq_sign_or_eq_twist_of_isRefl hp2 (Pi.basisFun (ZMod p) (Fin 4)) hTrefl
        ⟨σ, c, hcne, hform⟩ with hsign | htwist
    · exact exists_fixed_basis_of_refl_form _ (Or.inl hsign)
    · exact exists_fixed_basis_of_refl_form _ (Or.inr htwist)
  obtain ⟨k, hfixk⟩ := hk
  set v : Fin 4 → ZMod p := bCoordIota eta (Additive.ofMul ⟨x, hx⟩)
  have hneg : T v = -v := (ggLin_inv_iff (p := p) (bCoordIota eta) t ⟨x, hx⟩).mp htinv
  have hv0 : (Pi.basisFun (ZMod p) (Fin 4)).equivFun v k ≠ 0 := by
    change (Pi.basisFun (ZMod p) (Fin 4)).repr v k ≠ 0
    rw [Pi.basisFun_repr]
    exact hv_ne k
  have heqk : (Pi.basisFun (ZMod p) (Fin 4)).equivFun (T v) k =
      (Pi.basisFun (ZMod p) (Fin 4)).equivFun v k :=
    equivFun_of_action_basis (Pi.basisFun (ZMod p) (Fin 4)) σ c hform hfixk v
  have hcEq : (Pi.basisFun (ZMod p) (Fin 4)).equivFun v k =
      - (Pi.basisFun (ZMod p) (Fin 4)).equivFun v k := by
    calc (Pi.basisFun (ZMod p) (Fin 4)).equivFun v k
        = (Pi.basisFun (ZMod p) (Fin 4)).equivFun (T v) k := heqk.symm
      _ = (Pi.basisFun (ZMod p) (Fin 4)).equivFun (-v) k := by rw [hneg]
      _ = - (Pi.basisFun (ZMod p) (Fin 4)).equivFun v k := by simp
  have h2 : (2 : ZMod p) * (Pi.basisFun (ZMod p) (Fin 4)).equivFun v k = 0 := by
    have hsum : (Pi.basisFun (ZMod p) (Fin 4)).equivFun v k +
        (Pi.basisFun (ZMod p) (Fin 4)).equivFun v k = 0 :=
      (eq_neg_iff_add_eq_zero).mp hcEq
    simpa [two_mul] using hsum
  exact hv0 ((mul_eq_zero.mp h2).resolve_left (zmod_two_ne_zero hp2))

private theorem permMap_swap_mul_sgn_mul_swap {a c : Fin 4} (hac : a ≠ c) :
    ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap a c) *
        ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = c then -1 else 1) *
        ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap a c) =
      ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = a then -1 else 1) := by
  set b := Pi.basisFun (ZMod p) (Fin 4)
  set σ := Equiv.swap a c
  have hsq : ZS.permMap p b σ * ZS.permMap p b σ = 1 := by
    rw [ZS.permMap_mul, Equiv.swap_mul_self]
    show b.equiv b (Equiv.refl (Fin 4)) = 1
    rw [Module.Basis.equiv_refl]
    rfl
  have hinv : ZS.permMap p b σ = (ZS.permMap p b σ)⁻¹ :=
    (inv_eq_of_mul_eq_one_right hsq).symm
  calc ZS.permMap p b σ * ZS.diagMap p b (fun j => if j = c then -1 else 1) *
        ZS.permMap p b σ
      = ZS.permMap p b σ * ZS.diagMap p b (fun j => if j = c then -1 else 1) *
        (ZS.permMap p b σ)⁻¹ := by
        conv_lhs => enter [2]; rw [hinv]
    _ = ZS.diagMap p b ((fun j => if j = c then -1 else 1) ∘ σ.symm) :=
        ZS.permMap_mul_diagMap_mul_inv b σ _
    _ = ZS.diagMap p b (fun j => if j = a then -1 else 1) := by
        congr 1
        funext j
        simp only [Function.comp_apply, σ, Equiv.symm_swap]
        by_cases hja : j = a
        · subst hja
          simp
        · have hne : Equiv.swap a c j ≠ c := by
            intro h
            apply hja
            have h' := congrArg (Equiv.swap a c) h
            rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h'
            exact h'
          simp [hne, hja]

private theorem permMap_swap_mul_swap_mul_swap {a c d : Fin 4} (hac : a ≠ c) (had : a ≠ d) :
    ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap c d) *
        ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap a c) *
        ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap c d) =
      ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap a d) := by
  rw [ZS.permMap_mul, ZS.permMap_mul, Equiv.swap_mul_swap_mul_swap hac had, Equiv.swap_comm]

omit [Finite G] in
private theorem isRefl_sgnMap (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p)))
    (hp2 : p ≠ 2) (i : Fin 4) :
    ZS.IsRefl p (ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4))
      (fun j => if j = i then -1 else 1)) := by
  have h := ggIsReflection_congr_sgnAut (p := p) hp2 eta (n := 4) i
  have h' := (ggIsReflection_iff_ggLinRefl (p := p) hp2 (bCoordIota eta) _).mp h
  rw [ggLin_bCoordIota_sgnAut eta i] at h'
  exact h'

private theorem b3Chain_sgn_mem
    {H : Subgroup ((Fin 4 → ZMod p) ≃ₗ[ZMod p] (Fin 4 → ZMod p))}
    (h1 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) ∈ H)
    (h2 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) ∈ H)
    (h3 : ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4))
      (fun j => if j = i0.succAbove 2 then -1 else 1) ∈ H)
    {i : Fin 4} (hi : i ≠ i0) :
    ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i then -1 else 1) ∈ H := by
  set b := Pi.basisFun (ZMod p) (Fin 4)
  have h01 : i0.succAbove 0 ≠ i0.succAbove 1 :=
    (Fin.succAbove_right_injective (p := i0)).ne (by norm_num)
  have h12 : i0.succAbove 1 ≠ i0.succAbove 2 :=
    (Fin.succAbove_right_injective (p := i0)).ne (by norm_num)
  have hsign1 : ZS.diagMap p b (fun j => if j = i0.succAbove 1 then -1 else 1) ∈ H := by
    have h := permMap_swap_mul_sgn_mul_swap (p := p) h12
    rw [← h]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 h3) h2
  have hsign0 : ZS.diagMap p b (fun j => if j = i0.succAbove 0 then -1 else 1) ∈ H := by
    have h := permMap_swap_mul_sgn_mul_swap (p := p) h01
    rw [← h]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 hsign1) h1
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (x := i) (y := i0) hi
  rw [← hk]
  fin_cases k
  · exact hsign0
  · exact hsign1
  · exact h3

private theorem b3Chain_swap_mem
    {H : Subgroup ((Fin 4 → ZMod p) ≃ₗ[ZMod p] (Fin 4 → ZMod p))}
    (h1 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) ∈ H)
    (h2 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) ∈ H)
    {a c : Fin 4} (ha : a ≠ i0) (hc : c ≠ i0) (hac : a ≠ c) :
    ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap a c) ∈ H := by
  set b := Pi.basisFun (ZMod p) (Fin 4)
  have h01 : i0.succAbove 0 ≠ i0.succAbove 1 :=
    (Fin.succAbove_right_injective (p := i0)).ne (by norm_num)
  have h02 : i0.succAbove 0 ≠ i0.succAbove 2 :=
    (Fin.succAbove_right_injective (p := i0)).ne (by norm_num)
  have hswap02 : ZS.permMap p b (Equiv.swap (i0.succAbove 0) (i0.succAbove 2)) ∈ H := by
    have h := permMap_swap_mul_swap_mul_swap (p := p) (a := i0.succAbove 0)
      (c := i0.succAbove 1) (d := i0.succAbove 2) h01 h02
    rw [← h]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 h1) h2
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (x := a) (y := i0) ha
  obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (x := c) (y := i0) hc
  rw [← hk, ← hl] at hac ⊢
  fin_cases k <;> fin_cases l
  · exact absurd rfl hac
  · exact h1
  · exact hswap02
  · rw [Equiv.swap_comm]
    exact h1
  · exact absurd rfl hac
  · exact h2
  · rw [Equiv.swap_comm]
    exact hswap02
  · rw [Equiv.swap_comm]
    exact h2
  · exact absurd rfl hac

private theorem b3Chain_swap_i0_mem
    {H : Subgroup ((Fin 4 → ZMod p) ≃ₗ[ZMod p] (Fin 4 → ZMod p))}
    (h1 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) ∈ H)
    (h2 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) ∈ H)
    (h4 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap i0 (i0.succAbove 0)) ∈ H)
    {a : Fin 4} (ha : a ≠ i0) :
    ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap i0 a) ∈ H := by
  set b := Pi.basisFun (ZMod p) (Fin 4)
  have h0 : i0 ≠ i0.succAbove 0 := (Fin.succAbove_ne i0 0).symm
  have h1' : i0 ≠ i0.succAbove 1 := (Fin.succAbove_ne i0 1).symm
  have h2' : i0 ≠ i0.succAbove 2 := (Fin.succAbove_ne i0 2).symm
  have htrans1 : ZS.permMap p b (Equiv.swap i0 (i0.succAbove 1)) ∈ H := by
    have h := permMap_swap_mul_swap_mul_swap (p := p) (a := i0) (c := i0.succAbove 0)
      (d := i0.succAbove 1) h0 h1'
    rw [← h]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h4) h1
  have htrans2 : ZS.permMap p b (Equiv.swap i0 (i0.succAbove 2)) ∈ H := by
    have h := permMap_swap_mul_swap_mul_swap (p := p) (a := i0) (c := i0.succAbove 1)
      (d := i0.succAbove 2) h1' h2'
    rw [← h]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 htrans1) h2
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (x := a) (y := i0) ha
  rw [← hk]
  fin_cases k
  · exact h4
  · exact htrans1
  · exact htrans2

private theorem b3Chain_sgn_i0_mem
    {H : Subgroup ((Fin 4 → ZMod p) ≃ₗ[ZMod p] (Fin 4 → ZMod p))}
    (h4 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap i0 (i0.succAbove 0)) ∈ H)
    (h0 : ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4))
      (fun j => if j = i0.succAbove 0 then -1 else 1) ∈ H) :
    ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i0 then -1 else 1) ∈ H := by
  have h := permMap_swap_mul_sgn_mul_swap (p := p) (Fin.succAbove_ne i0 0).symm
  rw [← h]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h4 h0) h4

omit [Finite G] in
private theorem closure_b3Chain_le_map_automizer
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0) :
    Subgroup.closure
        {ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)),
          ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)),
          ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i0.succAbove 2 then -1 else 1)} ≤
      (ggAutomizer L Bs).map (ggLin (p := p) (bCoordIota eta)) := by
  set b := Pi.basisFun (ZMod p) (Fin 4) with hb
  set T := ggLin (p := p) (bCoordIota eta) with hT
  set r1 := ZS.permMap p b (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) with hr1
  set r2 := ZS.permMap p b (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) with hr2
  set r3 := ZS.diagMap p b (fun j => if j = i0.succAbove 2 then -1 else 1) with hr3
  let T' := T.comp (MulAut.congr eta).symm.toMonoidHom
  have hT'_sgn : ∀ i : Fin 4, T' (SpCoord.sgnAut i) =
      ZS.diagMap p b (fun j => if j = i then -1 else 1) := fun i => ggLin_bCoordIota_sgnAut eta i
  have hT'_perm : ∀ σ : Equiv.Perm (Fin 4), T' (SpCoord.permAut σ) = ZS.permMap p b σ :=
    fun σ => ggLin_bCoordIota_permAut eta σ
  have hmap : (ggAutomizer L Bs).map T = (bCoordinateBlock 4 p i0).map T' := by
    rw [← hLB, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun φ => ?_
    show T φ = T ((MulAut.congr eta).symm (MulAut.congr eta φ))
    rw [MulEquiv.symm_apply_apply]
  have hS : (bCoordinateBlock 4 p i0).map T' = Subgroup.closure (T' '' {r |
      (∃ i : Fin 4, i ≠ i0 ∧ r = SpCoord.sgnAut i) ∨
        (∃ a c : Fin 4, a ≠ c ∧ a ≠ i0 ∧ c ≠ i0 ∧
          r = SpCoord.permAut (Equiv.swap a c))}) := by
    rw [bCoordinateBlock, MonoidHom.map_closure]
  rw [hmap, hS]
  have h01 : i0.succAbove 0 ≠ i0.succAbove 1 :=
    (Fin.succAbove_right_injective (p := i0)).ne (by norm_num)
  have h12 : i0.succAbove 1 ≠ i0.succAbove 2 :=
    (Fin.succAbove_right_injective (p := i0)).ne (by norm_num)
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · refine Subgroup.subset_closure
      ⟨SpCoord.permAut (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)),
        Or.inr ⟨_, _, h01, by simp, by simp, rfl⟩, ?_⟩
    rw [hT'_perm, hr1]
  · refine Subgroup.subset_closure
      ⟨SpCoord.permAut (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)),
        Or.inr ⟨_, _, h12, by simp, by simp, rfl⟩, ?_⟩
    rw [hT'_perm, hr2]
  · refine Subgroup.subset_closure
      ⟨SpCoord.sgnAut (i0.succAbove 2), Or.inl ⟨_, by simp, rfl⟩, ?_⟩
    rw [hT'_sgn, hr3]

omit [Finite G] in
private theorem map_automizer_le_closure_b3Chain
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0) :
    (ggAutomizer L Bs).map (ggLin (p := p) (bCoordIota eta)) ≤
      Subgroup.closure
        {ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)),
          ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)),
          ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i0.succAbove 2 then -1 else 1)} := by
  set b := Pi.basisFun (ZMod p) (Fin 4) with hb
  set T := ggLin (p := p) (bCoordIota eta) with hT
  set r1 := ZS.permMap p b (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) with hr1
  set r2 := ZS.permMap p b (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) with hr2
  set r3 := ZS.diagMap p b (fun j => if j = i0.succAbove 2 then -1 else 1) with hr3
  let T' := T.comp (MulAut.congr eta).symm.toMonoidHom
  have hT'_sgn : ∀ i : Fin 4, T' (SpCoord.sgnAut i) =
      ZS.diagMap p b (fun j => if j = i then -1 else 1) := fun i => ggLin_bCoordIota_sgnAut eta i
  have hT'_perm : ∀ σ : Equiv.Perm (Fin 4), T' (SpCoord.permAut σ) = ZS.permMap p b σ :=
    fun σ => ggLin_bCoordIota_permAut eta σ
  have hmap : (ggAutomizer L Bs).map T = (bCoordinateBlock 4 p i0).map T' := by
    rw [← hLB, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun φ => ?_
    show T φ = T ((MulAut.congr eta).symm (MulAut.congr eta φ))
    rw [MulEquiv.symm_apply_apply]
  have hS : (bCoordinateBlock 4 p i0).map T' = Subgroup.closure (T' '' {r |
      (∃ i : Fin 4, i ≠ i0 ∧ r = SpCoord.sgnAut i) ∨
        (∃ a c : Fin 4, a ≠ c ∧ a ≠ i0 ∧ c ≠ i0 ∧
          r = SpCoord.permAut (Equiv.swap a c))}) := by
    rw [bCoordinateBlock, MonoidHom.map_closure]
  rw [hmap, hS]
  rw [Subgroup.closure_le]
  rintro x ⟨g, hg, rfl⟩
  rcases hg with ⟨i, hi, rfl⟩ | ⟨a, c, hac, ha, hc, rfl⟩
  · rw [hT'_sgn]
    exact b3Chain_sgn_mem (p := p) (i0 := i0)
      (by rw [← hr1]; exact Subgroup.subset_closure (by simp))
      (by rw [← hr2]; exact Subgroup.subset_closure (by simp))
      (by rw [← hr3]; exact Subgroup.subset_closure (by simp)) hi
  · rw [hT'_perm]
    exact b3Chain_swap_mem (p := p) (i0 := i0)
      (by rw [← hr1]; exact Subgroup.subset_closure (by simp))
      (by rw [← hr2]; exact Subgroup.subset_closure (by simp)) ha hc hac

omit [Finite G] in
private theorem closure_b3Chain_eq_map_automizer
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0) :
    Subgroup.closure
        {ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)),
          ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)),
          ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i0.succAbove 2 then -1 else 1)} =
      (ggAutomizer L Bs).map (ggLin (p := p) (bCoordIota eta)) :=
  le_antisymm (closure_b3Chain_le_map_automizer hLB)
    (map_automizer_le_closure_b3Chain hLB)

private theorem b3Chain_sgn_mem_of_mem
    {H : Subgroup ((Fin 4 → ZMod p) ≃ₗ[ZMod p] (Fin 4 → ZMod p))}
    (h1 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) ∈ H)
    (h2 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) ∈ H)
    (h3 : ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4))
      (fun j => if j = i0.succAbove 2 then -1 else 1) ∈ H)
    (h4 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap i0 (i0.succAbove 0)) ∈ H) (i : Fin 4) :
    ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i then -1 else 1) ∈ H := by
  by_cases hi : i = i0
  · rw [hi]
    exact b3Chain_sgn_i0_mem (p := p) (i0 := i0) h4
      (b3Chain_sgn_mem (p := p) (i0 := i0) h1 h2 h3 (by simp))
  · exact b3Chain_sgn_mem (p := p) (i0 := i0) h1 h2 h3 hi

private theorem b3Chain_perm_mem_of_mem
    {H : Subgroup ((Fin 4 → ZMod p) ≃ₗ[ZMod p] (Fin 4 → ZMod p))}
    (h1 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) ∈ H)
    (h2 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) ∈ H)
    (h4 : ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
      (Equiv.swap i0 (i0.succAbove 0)) ∈ H)
    {a c : Fin 4} (hac : a ≠ c) :
    ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap a c) ∈ H := by
  by_cases ha0 : a = i0
  · rw [ha0] at hac ⊢
    exact b3Chain_swap_i0_mem (p := p) (i0 := i0) h1 h2 h4 hac.symm
  · by_cases hc0 : c = i0
    · rw [hc0, Equiv.swap_comm]
      exact b3Chain_swap_i0_mem (p := p) (i0 := i0) h1 h2 h4 ha0
    · exact b3Chain_swap_mem (p := p) (i0 := i0) h1 h2 ha0 hc0 hac

omit [Finite G] in
private theorem closure_b3Chain_swap_le_map_join
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p) :
    Subgroup.closure
        {ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)),
          ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)),
          ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i0.succAbove 2 then -1 else 1),
          ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap i0 (i0.succAbove 0))} ≤
      (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := p) (bCoordIota eta)) := by
  set b := Pi.basisFun (ZMod p) (Fin 4) with hb
  set T := ggLin (p := p) (bCoordIota eta) with hT
  set r1 := ZS.permMap p b (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) with hr1
  set r2 := ZS.permMap p b (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) with hr2
  set r3 := ZS.diagMap p b (fun j => if j = i0.succAbove 2 then -1 else 1) with hr3
  set r4 := ZS.permMap p b (Equiv.swap i0 (i0.succAbove 0)) with hr4
  let T' := T.comp (MulAut.congr eta).symm.toMonoidHom
  have hT'_sgn : ∀ i : Fin 4, T' (SpCoord.sgnAut i) =
      ZS.diagMap p b (fun j => if j = i then -1 else 1) := fun i => ggLin_bCoordIota_sgnAut eta i
  have hT'_perm : ∀ σ : Equiv.Perm (Fin 4), T' (SpCoord.permAut σ) = ZS.permMap p b σ :=
    fun σ => ggLin_bCoordIota_permAut eta σ
  have hmap : (ggAutomizerJoin L Bs 𝒦).map T = (bSignedFull 4 p).map T' := by
    rw [← hK, Subgroup.map_map]; congr 1
    refine MonoidHom.ext fun φ => ?_
    show T φ = T ((MulAut.congr eta).symm (MulAut.congr eta φ))
    rw [MulEquiv.symm_apply_apply]
  have hS : (bSignedFull 4 p).map T' = Subgroup.closure (T' '' {r |
      (∃ i : Fin 4, r = SpCoord.sgnAut i) ∨
        (∃ a c : Fin 4, a ≠ c ∧ r = SpCoord.permAut (Equiv.swap a c))}) := by
    rw [bSignedFull, MonoidHom.map_closure]
  rw [hmap, hS]
  have h01 : i0.succAbove 0 ≠ i0.succAbove 1 := (Fin.succAbove_right_injective (p := i0)).ne (by norm_num)
  have h12 : i0.succAbove 1 ≠ i0.succAbove 2 := (Fin.succAbove_right_injective (p := i0)).ne (by norm_num)
  rw [Subgroup.closure_le]; rintro x (rfl | rfl | rfl | rfl)
  · refine Subgroup.subset_closure
      ⟨SpCoord.permAut (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)),
        Or.inr ⟨_, _, h01, rfl⟩, ?_⟩
    rw [hT'_perm, hr1]
  · refine Subgroup.subset_closure
      ⟨SpCoord.permAut (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)),
        Or.inr ⟨_, _, h12, rfl⟩, ?_⟩
    rw [hT'_perm, hr2]
  · refine Subgroup.subset_closure
      ⟨SpCoord.sgnAut (i0.succAbove 2), Or.inl ⟨_, rfl⟩, ?_⟩
    rw [hT'_sgn, hr3]
  · refine Subgroup.subset_closure
      ⟨SpCoord.permAut (Equiv.swap i0 (i0.succAbove 0)),
        Or.inr ⟨_, _, (Fin.succAbove_ne i0 0).symm, rfl⟩, ?_⟩
    rw [hT'_perm, hr4]

omit [Finite G] in
private theorem map_join_le_closure_b3Chain_swap
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p) :
    (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := p) (bCoordIota eta)) ≤
      Subgroup.closure
        {ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)),
          ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)),
          ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i0.succAbove 2 then -1 else 1),
          ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap i0 (i0.succAbove 0))} := by
  set b := Pi.basisFun (ZMod p) (Fin 4) with hb
  set T := ggLin (p := p) (bCoordIota eta) with hT
  set r1 := ZS.permMap p b (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) with hr1
  set r2 := ZS.permMap p b (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) with hr2
  set r3 := ZS.diagMap p b (fun j => if j = i0.succAbove 2 then -1 else 1) with hr3
  set r4 := ZS.permMap p b (Equiv.swap i0 (i0.succAbove 0)) with hr4
  let T' := T.comp (MulAut.congr eta).symm.toMonoidHom
  have hT'_sgn : ∀ i : Fin 4, T' (SpCoord.sgnAut i) =
      ZS.diagMap p b (fun j => if j = i then -1 else 1) := fun i => ggLin_bCoordIota_sgnAut eta i
  have hT'_perm : ∀ σ : Equiv.Perm (Fin 4), T' (SpCoord.permAut σ) = ZS.permMap p b σ :=
    fun σ => ggLin_bCoordIota_permAut eta σ
  have hmap : (ggAutomizerJoin L Bs 𝒦).map T = (bSignedFull 4 p).map T' := by
    rw [← hK, Subgroup.map_map]; congr 1
    refine MonoidHom.ext fun φ => ?_
    show T φ = T ((MulAut.congr eta).symm (MulAut.congr eta φ))
    rw [MulEquiv.symm_apply_apply]
  have hS : (bSignedFull 4 p).map T' = Subgroup.closure (T' '' {r |
      (∃ i : Fin 4, r = SpCoord.sgnAut i) ∨
        (∃ a c : Fin 4, a ≠ c ∧ r = SpCoord.permAut (Equiv.swap a c))}) := by
    rw [bSignedFull, MonoidHom.map_closure]
  rw [hmap, hS]
  have h1C : ZS.permMap p b (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) ∈
      Subgroup.closure {r1, r2, r3, r4} := by
    rw [← hr1]; exact Subgroup.subset_closure (by simp)
  have h2C : ZS.permMap p b (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) ∈
      Subgroup.closure {r1, r2, r3, r4} := by
    rw [← hr2]; exact Subgroup.subset_closure (by simp)
  have h3C : ZS.diagMap p b (fun j => if j = i0.succAbove 2 then -1 else 1) ∈
      Subgroup.closure {r1, r2, r3, r4} := by
    rw [← hr3]; exact Subgroup.subset_closure (by simp)
  have h4C : ZS.permMap p b (Equiv.swap i0 (i0.succAbove 0)) ∈
      Subgroup.closure {r1, r2, r3, r4} := by
    rw [← hr4]; exact Subgroup.subset_closure (by simp)
  rw [Subgroup.closure_le]; rintro x ⟨g, hg, rfl⟩
  rcases hg with ⟨i, rfl⟩ | ⟨a, c, hac, rfl⟩
  · rw [hT'_sgn]; exact b3Chain_sgn_mem_of_mem (p := p) (i0 := i0)
      (H := Subgroup.closure {r1, r2, r3, r4}) h1C h2C h3C h4C i
  · rw [hT'_perm]; exact b3Chain_perm_mem_of_mem (p := p) (i0 := i0)
      (H := Subgroup.closure {r1, r2, r3, r4}) h1C h2C h4C hac

omit [Finite G] in
private theorem closure_b3Chain_swap_eq_map_join
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p) :
    Subgroup.closure
        {ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)),
          ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)),
          ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i0.succAbove 2 then -1 else 1),
          ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap i0 (i0.succAbove 0))} =
      (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := p) (bCoordIota eta)) :=
  le_antisymm (closure_b3Chain_swap_le_map_join hK)
    (map_join_le_closure_b3Chain_swap hK)

private theorem b3Chain_mem_map
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0) :
    ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) ∈
        (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)) ∧
      ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) ∈
        (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)) ∧
      ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4))
          (fun j => if j = i0.succAbove 2 then -1 else 1) ∈
        (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)) ∧
      ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap i0 (i0.succAbove 0)) ∈
        (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)) := by
  set b := Pi.basisFun (ZMod p) (Fin 4) with hb
  set T := ggLin (p := p) (bCoordIota eta) with hT
  set r1 := ZS.permMap p b (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) with hr1
  set r2 := ZS.permMap p b (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) with hr2
  set r3 := ZS.diagMap p b (fun j => if j = i0.succAbove 2 then -1 else 1) with hr3
  set r4 := ZS.permMap p b (Equiv.swap i0 (i0.succAbove 0)) with hr4
  set A' := (ggAInf p B Bs x L D J).map T with hA'
  have hKle : ggAutomizerJoin L Bs 𝒦 ≤ ggAInf p B Bs x L D J :=
    GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1
  have hALle : (ggAutomizer L Bs).map T ≤ A' := Subgroup.map_mono (le_sup_left.trans hKle)
  have hALmap : Subgroup.closure {r1, r2, r3} = (ggAutomizer L Bs).map T :=
    closure_b3Chain_eq_map_automizer hLB
  have hmem1 : r1 ∈ (ggAutomizer L Bs).map T := by
    rw [← hALmap]; exact Subgroup.subset_closure (by simp)
  have hmem2 : r2 ∈ (ggAutomizer L Bs).map T := by
    rw [← hALmap]; exact Subgroup.subset_closure (by simp)
  have hmem3 : r3 ∈ (ggAutomizer L Bs).map T := by
    rw [← hALmap]; exact Subgroup.subset_closure (by simp)
  refine ⟨hALle hmem1, hALle hmem2, hALle hmem3, ?_⟩
  rw [hA', hr4]
  exact permMap_mem_map_ggAInf (eta := eta) hKle hK (Equiv.swap i0 (i0.succAbove 0))

omit [Finite G] in
private theorem b3Chain_refl_order
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))) (hp2 : p ≠ 2) :
    ZS.IsRefl p (ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
        (Equiv.swap (i0.succAbove 0) (i0.succAbove 1))) ∧
      ZS.IsRefl p (ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
        (Equiv.swap (i0.succAbove 1) (i0.succAbove 2))) ∧
      ZS.IsRefl p (ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4))
        (fun j => if j = i0.succAbove 2 then -1 else 1)) ∧
      ZS.IsRefl p (ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
        (Equiv.swap i0 (i0.succAbove 0))) ∧
      orderOf (ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
          (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) *
        ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
          (Equiv.swap (i0.succAbove 1) (i0.succAbove 2))) = 3 ∧
      orderOf (ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
          (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) *
        ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4))
          (fun j => if j = i0.succAbove 2 then -1 else 1)) = 4 ∧
      orderOf (ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4))
          (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) *
        ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4))
          (fun j => if j = i0.succAbove 2 then -1 else 1)) = 2 := by
  have h01 : i0.succAbove 0 ≠ i0.succAbove 1 :=
    (Fin.succAbove_right_injective (p := i0)).ne (by norm_num)
  have h12 : i0.succAbove 1 ≠ i0.succAbove 2 :=
    (Fin.succAbove_right_injective (p := i0)).ne (by norm_num)
  obtain ⟨h12o, h23o, h13o⟩ :=
    ZS.orderOf_b3Chain (p := p) hp2 (Pi.basisFun (ZMod p) (Fin 4)) i0
  exact ⟨ZS.isRefl_permMap_swap _ h01, ZS.isRefl_permMap_swap _ h12,
    isRefl_sgnMap eta hp2 (i0.succAbove 2),
    ZS.isRefl_permMap_swap _ (Fin.succAbove_ne i0 0).symm, h12o, h23o, h13o⟩

private theorem finite_linearEquiv_four (p : ℕ) [Fact p.Prime] :
    Finite ((Fin 4 → ZMod p) ≃ₗ[ZMod p] (Fin 4 → ZMod p)) :=
  Finite.of_injective _ DFunLike.coe_injective

omit [Finite G] in
private theorem b3Chain_swap_card (hp2 : p ≠ 2)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p) :
    Nat.card (Subgroup.closure
        {ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)),
          ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)),
          ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i0.succAbove 2 then -1 else 1),
          ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap i0 (i0.succAbove 0))}) = 384 := by
  rw [closure_b3Chain_swap_eq_map_join hK,
    Subgroup.card_map_of_injective (ggLin_injective (p := p) (bCoordIota eta)),
    card_ggAutomizerJoin_of_bSignedFull hp2 eta hK]
  norm_num

private theorem b3Chain_N4_le_card (hp2 : p ≠ 2)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0)
    {y : G} {K : Subgroup G} (hN : GGNbr p B x D J y K)
    {s : MulAut ↥Bs} (hsK : s ∈ ggAutomizer K Bs) :
    Nat.card (Subgroup.closure
        {ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)),
          ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)),
          ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i0.succAbove 2 then -1 else 1),
          ggLin (p := p) (bCoordIota eta) s}) ≤ 384 := by
  set b := Pi.basisFun (ZMod p) (Fin 4) with hb
  set T := ggLin (p := p) (bCoordIota eta) with hT
  set r1 := ZS.permMap p b (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) with hr1
  set r2 := ZS.permMap p b (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) with hr2
  set r3 := ZS.diagMap p b (fun j => if j = i0.succAbove 2 then -1 else 1) with hr3
  have hclosure : Subgroup.closure {r1, r2, r3} ≤
      (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map T := by
    rw [closure_b3Chain_eq_map_automizer hLB]; exact Subgroup.map_mono le_sup_left
  have hleH : Subgroup.closure {r1, r2, r3, T s} ≤
      (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map T := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hclosure (Subgroup.subset_closure (by simp))
    · exact hclosure (Subgroup.subset_closure (by simp))
    · exact hclosure (Subgroup.subset_closure (by simp))
    · exact Subgroup.map_mono le_sup_right (Subgroup.mem_map_of_mem T hsK)
  have hcard : Nat.card ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map T) =
      Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    Subgroup.card_map_of_injective (ggLin_injective (p := p) (bCoordIota eta))
  have hjoin : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤
      Nat.card (ggAutomizerJoin L Bs 𝒦) := by
    have h := card_ggAutomizerJoin_singleton_le (p := p) hR hN
    rwa [ggAutomizerJoin_singleton] at h
  have hcardK : Nat.card (ggAutomizerJoin L Bs 𝒦) = 384 := by
    rw [card_ggAutomizerJoin_of_bSignedFull hp2 eta hK]; norm_num
  calc Nat.card (Subgroup.closure {r1, r2, r3, T s}) ≤
        Nat.card ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map T) :=
        @Subgroup.card_le_of_le _ _ (Subgroup.closure {r1, r2, r3, T s})
          ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map T)
          (@Finite.of_injective _ _ (finite_linearEquiv_four (p := p)) _ Subtype.coe_injective) hleH
    _ = Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) := hcard
    _ ≤ Nat.card (ggAutomizerJoin L Bs 𝒦) := hjoin
    _ = 384 := hcardK

private theorem ggAInf_le_of_bCoordinateBlock_N4 (hp2 : p ≠ 2)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0)
    (hone : ZS.OneClass p ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))))
    (hmod : ZS.ModelIso p .N4 ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)))) :
    ggAInf p B Bs x L D J ≤ ggAutomizerJoin L Bs 𝒦 := by
  set T := ggLin (p := p) (bCoordIota eta) with hT
  set b := Pi.basisFun (ZMod p) (Fin 4) with hb
  set r1 := ZS.permMap p b (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) with hr1
  set r2 := ZS.permMap p b (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) with hr2
  set r3 := ZS.diagMap p b (fun j => if j = i0.succAbove 2 then -1 else 1) with hr3
  set r4 := ZS.permMap p b (Equiv.swap i0 (i0.succAbove 0)) with hr4
  set A' := (ggAInf p B Bs x L D J).map T with hA'
  obtain ⟨hr1A', hr2A', hr3A', hr4A'⟩ := b3Chain_mem_map (p := p) hR hK hLB
  obtain ⟨hr1refl, hr2refl, hr3refl, hr4refl, h12', h23', h13'⟩ :=
    b3Chain_refl_order (p := p) eta hp2
  have hgen : Subgroup.closure {r1, r2, r3, r4} = (ggAutomizerJoin L Bs 𝒦).map T :=
    closure_b3Chain_swap_eq_map_join hK
  refine sup_le le_sup_left (iSup_le fun y => iSup_le fun K => iSup_le fun hN => ?_)
  rw [hR.2.1 y K hN]
  refine (Subgroup.closure_le _).mpr fun s hs => ?_
  obtain ⟨hsK, hsrefl⟩ := hs
  have hsAInf : s ∈ ggAInf p B Bs x L D J := ggAutomizer_le_ggAInf_of_nbr hN hsK
  have htA' : T s ∈ A' := by
    rw [hA']; exact Subgroup.mem_map_of_mem T hsAInf
  have htrefl : ZS.IsRefl p (T s) :=
    (ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) s).mp hsrefl
  have hW : Nat.card (Subgroup.closure {r1, r2, r3, r4}) = 384 :=
    b3Chain_swap_card (p := p) hp2 hK
  have hle := b3Chain_N4_le_card (p := p) hp2 hR hK hLB hN hsK
  have htmem := ZS.mem_closure_of_b3Chain_of_N4 (p := p) (A := A') hone hmod
    hr1A' hr2A' hr3A' hr4A' htA' hr1refl hr2refl hr3refl hr4refl htrefl
    h12' h23' h13' hW hle
  have htjoin : T s ∈ (ggAutomizerJoin L Bs 𝒦).map T := by
    rw [← hgen]; exact htmem
  exact (Subgroup.mem_map_iff_mem (f := T)
    (ggLin_injective (p := p) (bCoordIota eta))).mp htjoin

private theorem false_of_bCoordinateBlock_EN4 (hp2 : p ≠ 2)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0)
    (hsatB : ∀ φ ∈ ggAInf p B Bs x L D J,
      ZS.IsRefl p (ggLin (p := p) (bCoordIota eta) φ) →
        ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin 4) i0) =
          Pi.basisFun (ZMod p) (Fin 4) i0 → φ ∈ ggAutomizer L Bs)
    (hone : ZS.OneClass p ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))))
    (hmod : ZS.ModelIso p .EN4 ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)))) :
    False := by
  set T := ggLin (p := p) (bCoordIota eta) with hT
  set b := Pi.basisFun (ZMod p) (Fin 4) with hb
  set r1 := ZS.permMap p b (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) with hr1
  set r2 := ZS.permMap p b (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) with hr2
  set r3 := ZS.diagMap p b (fun j => if j = i0.succAbove 2 then -1 else 1) with hr3
  set A' := (ggAInf p B Bs x L D J).map T with hA'
  obtain ⟨hr1A', hr2A', hr3A', _⟩ := b3Chain_mem_map (p := p) hR hK hLB
  obtain ⟨hr1refl, hr2refl, hr3refl, _, h12', h23', h13'⟩ :=
    b3Chain_refl_order (p := p) eta hp2
  have hALmap := closure_b3Chain_eq_map_automizer (p := p) (i0 := i0) hLB
  obtain ⟨s1, hs1A, s2, hs2A, hs12, hs1refl, hs2refl, hc1, hc2, hs1not, hs2not⟩ :=
    ZS.exists_two_refl_commute_not_mem_of_EN4 (p := p) (A := A') hone hmod
      hr1A' hr2A' hr3A' hr1refl hr2refl hr3refl h12' h23' h13'
  have hz : (r1 * r2 * r3) ^ 3 = ZS.diagMap p b (fun j => if j = i0 then 1 else -1) := by
    rw [hr1, hr2, hr3]
    exact ZS.b3Chain_cube (p := p) (Pi.basisFun (ZMod p) (Fin 4)) i0
  rw [hz] at hc1 hc2; have hcase1 := ZS.fix_or_eq_sgn_of_commute (p := p) hp2
    (Pi.basisFun (ZMod p) (Fin 4)) i0 hs1refl hc1
  have hcase2 := ZS.fix_or_eq_sgn_of_commute (p := p) hp2
    (Pi.basisFun (ZMod p) (Fin 4)) i0 hs2refl hc2
  have hex : ∃ s ∈ A', ZS.IsRefl p s ∧ s (b i0) = b i0 ∧ s ∉ Subgroup.closure {r1, r2, r3} := by
    by_cases hfix : s1 (b i0) = b i0
    · exact ⟨s1, hs1A, hs1refl, hfix, hs1not⟩
    · have hsgn1 : s1 = ZS.diagMap p b (fun j => if j = i0 then -1 else 1) := by
        rcases hcase1 with h | h
        · exact absurd h hfix
        · exact h
      have hfix2 : s2 (b i0) = b i0 := by
        by_contra hnot
        have hsgn2 : s2 = ZS.diagMap p b (fun j => if j = i0 then -1 else 1) := by
          rcases hcase2 with h | h
          exacts [absurd h hnot, h]
        exact hs12 (hsgn1.trans hsgn2.symm)
      exact ⟨s2, hs2A, hs2refl, hfix2, hs2not⟩
  obtain ⟨s, hsA, hsrefl, hfix, hsnot⟩ := hex
  rw [hA'] at hsA; obtain ⟨φ, hφ, hφs⟩ := Subgroup.mem_map.mp hsA
  have hφL : φ ∈ ggAutomizer L Bs :=
    hsatB φ hφ (by rw [hφs]; exact hsrefl) (by rw [hφs]; exact hfix)
  refine hsnot ?_
  rw [hALmap, ← hφs]; exact Subgroup.mem_map_of_mem T hφL

private theorem weyl_of_bCoordinateBlock_four
    (hp2 : p ≠ 2)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ιM : Type} {M : CoxeterMatrix ιM}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0)
    (hfam : ZS.Family p ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))))
    (hirr : ZS.AbsIrred p ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))))
    (hperm : ∀ σ, ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) σ ∈
      (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)))
    (hsgn : ∀ i, ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i then -1 else 1) ∈
      (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)))
    (hdvd : 2 ^ 4 * Nat.factorial 4 ∣
      Nat.card ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))))
    (htv : ∀ τ ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)),
      Module.finrank (ZMod p) (LinearMap.range
        ((τ : (Fin 4 → ZMod p) →ₗ[ZMod p] (Fin 4 → ZMod p)) - LinearMap.id)) = 1 →
        ∃ v, τ (τ v - v) ≠ τ v - v)
    (hLsigned : ∀ φ ∈ ggAutomizer L Bs, ∃ (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧
        ∀ i, ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin 4) i) =
          c i • Pi.basisFun (ZMod p) (Fin 4) (σ i))
    (hsatB : ∀ φ ∈ ggAInf p B Bs x L D J,
      ZS.IsRefl p (ggLin (p := p) (bCoordIota eta) φ) →
        ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin 4) i0) =
          Pi.basisFun (ZMod p) (Fin 4) i0 → φ ∈ ggAutomizer L Bs) :
    GGWeylReflectionGroup p (ggAInf p B Bs x L D J) := by
  rcases ZS.linWeyl_or_cases_of_signed_four hp2 (Pi.basisFun (ZMod p) (Fin 4)) hfam hirr hperm hsgn
    hdvd htv i0 with
    hW | ⟨-, ⟨r, hr, hrefl, hri0, hrmon⟩, -⟩ | ⟨-, htw⟩ | ⟨hp3, Q, hQ, hplus, hA⟩ |
      ⟨k, hk, -, -, hone, hmod, -⟩
  · exact ggRC_weylReflGroup_of_linWeyl (bCoordIota eta) _ hW
  · obtain ⟨φ, hφ, hφr⟩ := Subgroup.mem_map.mp hr
    have hφL := hsatB φ hφ (by rw [hφr]; exact hrefl) (by rw [hφr]; exact hri0)
    exact (false_of_refl_not_monomial hLsigned hφL hφr hrmon).elim
  · obtain ⟨a1, ha1, -⟩ := Fin.exists_ne_and_ne_of_two_lt i0 i0 (by norm_num : 2 < 4)
    obtain ⟨a2, ha2, ha21⟩ := Fin.exists_ne_and_ne_of_two_lt i0 a1 (by norm_num : 2 < 4)
    obtain ⟨ζ, hζ1, hζ2, ht⟩ := htw a1 a2 (Ne.symm ha21)
    obtain ⟨φ, hφ, hφr⟩ := Subgroup.mem_map.mp ht
    have hφL := hsatB φ hφ
      (by rw [hφr]; exact
        ZS.isRefl_diagMap_mul_permMap_swap (Pi.basisFun (ZMod p) (Fin 4)) (Ne.symm ha21) ζ)
      (by rw [hφr]; exact
        ZS.twist_apply_basis_of_ne (Pi.basisFun (ZMod p) (Fin 4)) (Ne.symm ha1) (Ne.symm ha2) ζ)
    exact (false_of_twist_of_bCoordinateBlock hLsigned hφL (Ne.symm ha21) hζ1 hζ2 hφr).elim
  · exact OrthF3.ggWeylReflectionGroup_of_orth_plus Q hQ hp3 (Module.finrank_fin_fun _) hplus
      (bCoordIota eta) (ggAInf p B Bs x L D J) fun g => by rw [← Subgroup.mem_map]; exact hA g
  · rcases hk with rfl | rfl
    · have hEq : ggAInf p B Bs x L D J = ggAutomizerJoin L Bs 𝒦 :=
        le_antisymm (ggAInf_le_of_bCoordinateBlock_N4 hp2 hR hK hLB hone hmod)
          (GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1)
      rw [hEq]
      exact ⟨ιM, M, hP.1, e, hP.2⟩
    · exact (false_of_bCoordinateBlock_EN4 hp2 hR hK hLB hsatB hone hmod).elim

private theorem exists_modelIso_ggAInf (hp2 : p ≠ 2) {k : ZS.ExcRow}
    (hmod : ZS.ModelIso p k ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)))) :
    ∃ f : ↥(ZS.model k) ≃* ↥(ggAInf p B Bs x L D J),
      ∀ g : ↥(ZS.model k), ZS.IsReflMat g.1 ↔ GGIsReflection p (f g : MulAut ↥Bs) := by
  obtain ⟨f₀, hf⟩ := hmod
  let E := Subgroup.equivMapOfInjective (ggAInf p B Bs x L D J)
    (ggLin (p := p) (bCoordIota eta)) (ggLin_injective (bCoordIota eta))
  have hcoe : ∀ x : ↥(ggAInf p B Bs x L D J),
      (E x : (Fin 4 → ZMod p) ≃ₗ[ZMod p] (Fin 4 → ZMod p)) =
        ggLin (p := p) (bCoordIota eta) x :=
    fun x => Subgroup.coe_equivMapOfInjective_apply _ _ _ x
  refine ⟨f₀.trans E.symm, fun g => ?_⟩
  have hT : ggLin (p := p) (bCoordIota eta) (E.symm (f₀ g)) =
      (f₀ g : (Fin 4 → ZMod p) ≃ₗ[ZMod p] (Fin 4 → ZMod p)) := by
    rw [← hcoe, MulEquiv.apply_symm_apply]
  rw [show ((f₀.trans E.symm) g : MulAut ↥Bs) = E.symm (f₀ g) from rfl, hf g, ← hT]
  change GGLinRefl (ggLin (p := p) (bCoordIota eta) (E.symm (f₀ g))) ↔
    GGIsReflection p (E.symm (f₀ g) : MulAut ↥Bs)
  exact (ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta)
    (E.symm (f₀ g) : MulAut ↥Bs)).symm

private theorem oneClass_ggAInf (hp2 : p ≠ 2)
    (hone : ZS.OneClass p ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)))) :
    ∀ s ∈ ggAInf p B Bs x L D J, ∀ t ∈ ggAInf p B Bs x L D J, GGIsReflection p s →
      GGIsReflection p t → ∃ g ∈ ggAInf p B Bs x L D J, t = g * s * g⁻¹ := by
  intro s hs t ht hsr htr
  obtain ⟨g', hg', hgt⟩ := hone _ (Subgroup.mem_map_of_mem _ hs) _ (Subgroup.mem_map_of_mem _ ht)
    ((ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) s).mp hsr)
    ((ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) t).mp htr)
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
  refine ⟨g, hg, ggLin_injective (p := p) (bCoordIota eta) ?_⟩
  rw [hgt]
  simp only [map_mul, map_inv]

private theorem orderOf_mul_le_ggAInf (hp2 : p ≠ 2) {d : ℕ}
    (hD : ZS.DMax p ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))) d) :
    ∀ s ∈ ggAInf p B Bs x L D J, ∀ t ∈ ggAInf p B Bs x L D J, GGIsReflection p s →
      GGIsReflection p t → orderOf (s * t) ≤ d := by
  intro s hs t ht hsr htr
  have h := hD.1 _ (Subgroup.mem_map_of_mem _ hs) _ (Subgroup.mem_map_of_mem _ ht)
    ((ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) s).mp hsr)
    ((ggIsReflection_iff_ggLinRefl hp2 (bCoordIota eta) t).mp htr)
  rwa [← map_mul, orderOf_injective _ (ggLin_injective (p := p) (bCoordIota eta))] at h

private theorem false_of_refl_fix_sum_of_aPermutationFull (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (ha₀ : GGLNoncyclicInput) (hx : x ∈ Bs)
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p)
    {r : (Fin 4 → ZMod p) ≃ₗ[ZMod p] (Fin 4 → ZMod p)}
    (hr : r ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)))
    (hrsum : r (∑ i, Pi.basisFun (ZMod p) (Fin 4) i) = ∑ i, Pi.basisFun (ZMod p) (Fin 4) i)
    (hrne : ∀ (k : Fin 4) (c s : ZMod p), r (Pi.basisFun (ZMod p) (Fin 4) 3) ≠
      c • Pi.basisFun (ZMod p) (Fin 4) k + s • ∑ i, Pi.basisFun (ZMod p) (Fin 4) i) : False := by
  obtain ⟨φ, hφ, hφr⟩ := Subgroup.mem_map.mp hr
  have hfix : φ ⟨x, hx⟩ = ⟨x, hx⟩ :=
    fix_x_of_aPermutationFull hR hx hLA (by rw [hφr]; exact hrsum)
  have hφI : φ ∈ ggInduced ⊤ Bs := ggRM_ainf_le_induced hφ
  obtain ⟨c, a, ha, hca⟩ := hR.nativeImage_of_aPermutationFull ha₀ le_rfl hLA hx hφI hfix
  obtain ⟨σ, hσ⟩ := hR.exists_perm_of_native_aPermutationFull hLA hx ha hca
  obtain ⟨s, hs⟩ := hσ 3
  rw [hφr] at hs
  exact hrne (σ 3) c s hs

private theorem weyl_of_aPermutationFull_four
    (hp2 : p ≠ 2) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (ha₀ : GGLNoncyclicInput) (hPermX : GGSecFiveBFourPermExcInput) {ιM : Type}
    {M : CoxeterMatrix ιM} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixBFour M) (hx : x ∈ Bs)
    (hnot : ¬ ∃ t ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection p t ∧ t ⟨x, hx⟩ = ⟨x, hx⟩⁻¹)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p)
    (hfam : ZS.Family p ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))))
    (hirr : ZS.AbsIrred p ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))))
    (hperm : ∀ σ, ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) σ ∈
      (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)))
    (hsgn : ∀ i, ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i then -1 else 1) ∈
      (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)))
    (hdvd : 2 ^ 4 * Nat.factorial 4 ∣
      Nat.card ((ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta))))
    (htv : ∀ τ ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) (bCoordIota eta)),
      Module.finrank (ZMod p) (LinearMap.range
        ((τ : (Fin 4 → ZMod p) →ₗ[ZMod p] (Fin 4 → ZMod p)) - LinearMap.id)) = 1 →
        ∃ v, τ (τ v - v) ≠ τ v - v) :
    GGWeylReflectionGroup p (ggAInf p B Bs x L D J) := by
  rcases ZS.linWeyl_or_cases_of_signed_four hp2 (Pi.basisFun (ZMod p) (Fin 4)) hfam hirr hperm hsgn
    hdvd htv 0 with
    hW | ⟨-, -, r, hr, -, hrsum, hrne⟩ | ⟨hmon, htw⟩ | ⟨hp3, Q, hQ, hplus, hA⟩ |
      ⟨k, hk, -, hD, hone, hmod, h4⟩
  · exact ggRC_weylReflGroup_of_linWeyl (bCoordIota eta) _ hW
  · exact (false_of_refl_fix_sum_of_aPermutationFull hR ha₀ hx hLA hr hrsum hrne).elim
  · obtain ⟨ζ, hζ1, hζ2, ht⟩ := htw 0 1 (by decide)
    exact (false_of_twist_of_aPermutationFull hR hp2 (by norm_num) hK hLA hmon (by decide) hζ1 hζ2
      ht).elim
  · exact OrthF3.ggWeylReflectionGroup_of_orth_plus Q hQ hp3 (Module.finrank_fin_fun _) hplus
      (bCoordIota eta) (ggAInf p B Bs x L D J) fun g => by
        rw [← Subgroup.mem_map]
        exact hA g
  · have hd : k.dmax = 4 := by rcases hk with rfl | rfl <;> rfl
    exact hPermX G p B Bs x L D J 𝒦 hR ιM M e hP hM hx hnot eta hLA k hk h4
      (exists_modelIso_ggAInf hp2 hmod) (oneClass_ggAInf hp2 hone)
      (by rw [← hd]; exact orderOf_mul_le_ggAInf hp2 hD)

end DegreeFour

private theorem ggSecFiveWeylInfAt_BFour_aux
    (hPos : BOriginalPositionInput) (hUse : ZS.UseInput) (hSat4 : GGSecFiveBFourCoordSatInput)
    (hPerm4 : GGSecFiveBFourPermWeylInput)
    (G : Type) [Group G] [Finite G] (p : ℕ) [fact : Fact p.Prime]
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (𝒦 : Finset (Subgroup G))
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (ιM : Type) (M : CoxeterMatrix ιM) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixBFour M) :
    GGWeylReflectionGroup p (ggAInf p B Bs x L D J) := by
  obtain ⟨-, -, hx, -, -⟩ := hR.1.1.tableB_facts
  obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hsat := hSat4 G p B Bs x L D J 𝒦 hR ιM M e hP hM hx
  have hperm4 := hPerm4 G p B Bs x L D J 𝒦 hR ιM M e hP hM hx
  obtain ⟨e', rfl⟩ := hM
  obtain ⟨-, eta, i0, hK, hL⟩ :=
    hPos G p B Bs x L D J 𝒦 hR 4 (by norm_num) _ (GGCoxeterPres.of_reindex_B (by norm_num) hP)
  rcases hL with hLB | hLD | hLA
  · have hsat' := hsat (exists_refl_inv_of_bCoordinateBlock hR hp2 hx hK hLB)
    set T := ggLin (p := p) (bCoordIota eta) with hT
    set b := Pi.basisFun (ZMod p) (Fin 4) with hb
    set A := (ggAInf p B Bs x L D J).map T with hA
    have hKle : ggAutomizerJoin L Bs 𝒦 ≤ ggAInf p B Bs x L D J :=
      GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1
    have hperm : ∀ σ, ZS.permMap p b σ ∈ A := fun σ =>
      permMap_mem_map_ggAInf (eta := eta) hKle hK σ
    have hsgn : ∀ i, ZS.diagMap p b (fun j => if j = i then -1 else 1) ∈ A := fun i =>
      sgnMap_mem_map_ggAInf (eta := eta) hKle hK i
    have hgen : ZS.ReflGen p A :=
      reflGen_map_ggAInf (eta := eta) hR hp2 (GGCoxeterPres.of_reindex_B (by norm_num) hP)
    have hirr : ZS.AbsIrred p A := ZS.absIrred_of_signed_le hp2 (by norm_num) b hperm hsgn
    have hfam : ZS.Family p A :=
      hUse p (Fin 4 → ZMod p) A hp2 (by rw [Module.finrank_fin_fun]; norm_num) hgen hirr
    have hdvd : 2 ^ 4 * Nat.factorial 4 ∣ Nat.card A :=
      dvd_card_map_ggAInf (eta := eta) hR hp2 hK
    have htv : ∀ τ ∈ A,
        Module.finrank (ZMod p) (LinearMap.range ((τ : (Fin 4 → ZMod p) →ₗ[ZMod p] _) -
          LinearMap.id)) = 1 → ∃ v, τ (τ v - v) ≠ τ v - v :=
      noTransvection_map_ggAInf (eta := eta) hR
    have hLsigned : ∀ φ ∈ ggAutomizer L Bs, ∃ (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → ZMod p),
        (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, T φ (b i) = c i • b (σ i) :=
      signed_of_mem_automizer (eta := eta) hK
    exact weyl_of_bCoordinateBlock_four hp2 hR hP hK hLB hfam hirr hperm hsgn hdvd htv hLsigned
      (sat_of_bCoordinateBlock hR hp2 hx hsat' hLB)
  · exact (false_of_dCoordinateBlock hp2 (by norm_num) hR hx
      (hsat (exists_refl_inv_of_dCoordinateBlock hR hp2 hx hK hLD)) eta hK hLD).elim
  · exact hperm4 (hR.not_exists_refl_inv_of_aPermutationFull hp2 hx hK hLA)

theorem ggSecFiveWeylInfAt_BFour_of_inputs
    (hPos : BOriginalPositionInput) (hUse : ZS.UseInput) (hSat4 : GGSecFiveBFourCoordSatInput)
    (hPerm4 : GGSecFiveBFourPermWeylInput) : GGSecFiveWeylInfAt GGIsWeylMatrixBFour := by
  intro G _ _ p B Bs x L D J 𝒦 hR ιM M e hP hM
  obtain ⟨hp, -, -, -, -⟩ := hR.1.1.tableB_facts
  exact ggSecFiveWeylInfAt_BFour_aux (fact := ⟨hp⟩) hPos hUse hSat4 hPerm4 G p B Bs x L D J 𝒦 hR
    ιM M e hP hM

private theorem ggSecFiveBFourPermWeylInput_aux
    (hPos : BOriginalPositionInput) (hUse : ZS.UseInput)
    (ha₀ : GGLNoncyclicInput) (hPermX : GGSecFiveBFourPermExcInput)
    (G : Type) [Group G] [Finite G] (p : ℕ) [fact : Fact p.Prime]
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (𝒦 : Finset (Subgroup G))
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (ιM : Type) (M : CoxeterMatrix ιM) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixBFour M)
    (hx : x ∈ Bs)
    (hnot : ¬ ∃ t ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection p t ∧ t ⟨x, hx⟩ = ⟨x, hx⟩⁻¹) :
    GGWeylReflectionGroup p (ggAInf p B Bs x L D J) := by
  obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hM4 : GGIsWeylMatrixBFour M := hM
  obtain ⟨e', rfl⟩ := hM4
  obtain ⟨-, eta, i0, hK, hL⟩ :=
    hPos G p B Bs x L D J 𝒦 hR 4 (by norm_num) _ (GGCoxeterPres.of_reindex_B (by norm_num) hP)
  rcases hL with hLB | hLD | hLA
  · exact (hnot (exists_refl_inv_of_bCoordinateBlock hR hp2 hx hK hLB)).elim
  · exact (hnot (exists_refl_inv_of_dCoordinateBlock hR hp2 hx hK hLD)).elim
  · set T := ggLin (p := p) (bCoordIota eta) with hT
    set b := Pi.basisFun (ZMod p) (Fin 4) with hb
    set A := (ggAInf p B Bs x L D J).map T with hA
    have hKle : ggAutomizerJoin L Bs 𝒦 ≤ ggAInf p B Bs x L D J :=
      GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1
    have hperm : ∀ σ, ZS.permMap p b σ ∈ A := fun σ =>
      permMap_mem_map_ggAInf (eta := eta) hKle hK σ
    have hsgn : ∀ i, ZS.diagMap p b (fun j => if j = i then -1 else 1) ∈ A := fun i =>
      sgnMap_mem_map_ggAInf (eta := eta) hKle hK i
    have hgen : ZS.ReflGen p A :=
      reflGen_map_ggAInf (eta := eta) hR hp2 (GGCoxeterPres.of_reindex_B (by norm_num) hP)
    have hirr : ZS.AbsIrred p A := ZS.absIrred_of_signed_le hp2 (by norm_num) b hperm hsgn
    have hfam : ZS.Family p A :=
      hUse p (Fin 4 → ZMod p) A hp2 (by rw [Module.finrank_fin_fun]; norm_num) hgen hirr
    have hdvd : 2 ^ 4 * Nat.factorial 4 ∣ Nat.card A :=
      dvd_card_map_ggAInf (eta := eta) hR hp2 hK
    have htv : ∀ τ ∈ A,
        Module.finrank (ZMod p) (LinearMap.range ((τ : (Fin 4 → ZMod p) →ₗ[ZMod p] _) -
          LinearMap.id)) = 1 → ∃ v, τ (τ v - v) ≠ τ v - v :=
      noTransvection_map_ggAInf (eta := eta) hR
    exact weyl_of_aPermutationFull_four hp2 hR ha₀ hPermX hP hM hx hnot hK hLA hfam hirr hperm
      hsgn hdvd htv

theorem ggSecFiveBFourPermWeylInput_of_nativeImage
    (hPos : BOriginalPositionInput) (hUse : ZS.UseInput)
    (ha₀ : GGLNoncyclicInput) (hPermX : GGSecFiveBFourPermExcInput) :
    GGSecFiveBFourPermWeylInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR ιM M e hP hM hx hnot
  obtain ⟨hp, -, -, -, -⟩ := hR.1.1.tableB_facts
  exact ggSecFiveBFourPermWeylInput_aux (fact := ⟨hp⟩) hPos hUse ha₀ hPermX G p B Bs x L D J 𝒦 hR
    ιM M e hP hM hx hnot

end CFSG.StandardType

end
