module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGSecFiveRestOriginalWeyl
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup
import CFSG.LocalAnalysis.StandardType.GGSignedCoordConj

public section

namespace CFSG.StandardType

open SpCoord

private theorem card_fixedPoints_map_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (A : Subgroup (MulAut X)) :
    Nat.card {y : Y // ∀ φ ∈ A.map (MulAut.congr e).toMonoidHom, φ y = y} =
      Nat.card {x : X // ∀ ψ ∈ A, ψ x = x} := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv ?_)
  have hcongr_apply : ∀ (ψ : MulAut X) (z : Y),
      (MulAut.congr e ψ) z = e (ψ (e.symm z)) := fun _ _ => rfl
  intro y
  constructor
  · intro hy ψ hψ
    have h := hy (MulAut.congr e ψ) (Subgroup.mem_map.mpr ⟨ψ, hψ, rfl⟩)
    rw [hcongr_apply ψ y] at h
    simpa using congrArg e.symm h
  · intro hx φ hφ
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] at hx
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hφ
    change ((MulAut.congr e) ψ) y = y
    rw [hcongr_apply ψ y, hx ψ hψ, e.apply_symm_apply]

private theorem congr_reflection_data {G : Type} [Group G] {p n : ℕ} {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {φ : MulAut ↥Bs}
    (h : GGIsReflection p φ) :
    (MulAut.congr eta φ) ^ 2 = 1 ∧
      Nat.card {x : Fin n → Multiplicative (ZMod p) // MulAut.congr eta φ x = x} * p =
        Nat.card (Fin n → Multiplicative (ZMod p)) := by
  refine ⟨?_, ?_⟩
  · rw [← map_pow, h.1, map_one]
  · have hfix : Nat.card {x : Fin n → Multiplicative (ZMod p) //
        MulAut.congr eta φ x = x} = Nat.card {b : ↥Bs // φ b = b} := by
      refine Nat.card_congr (Equiv.subtypeEquiv eta.symm.toEquiv fun x => ?_)
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.toEquiv_eq_coe,
        MulEquiv.coe_toEquiv]
      constructor
      · intro h
        have h' := congrArg eta.symm h
        rwa [MulEquiv.symm_apply_apply] at h'
      · intro h
        rw [h, MulEquiv.apply_symm_apply]
    rw [hfix]
    calc Nat.card {b : ↥Bs // φ b = b} * p = Nat.card ↥Bs := h.2
      _ = Nat.card (Fin n → Multiplicative (ZMod p)) := Nat.card_congr eta.toEquiv

private theorem exists_reflections_with_closure {G : Type} [Group G] {p n : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {A : Subgroup (MulAut ↥Bs)} (hA : A.map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n p)
    {κ : Type} {M' : CoxeterMatrix κ} (hM' : GGIsWeylMatrix M') (f : M'.Group ≃* ↥A)
    (hf : ∀ i, GGIsReflection p ((f (M'.simple i) : ↥A) : MulAut ↥Bs)) :
    ∃ r : κ → MulAut (Fin n → Multiplicative (ZMod p)),
      (∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
        (r k = permAut (Equiv.swap a b) ∨
          r k = sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹)) ∧
      (∀ a b, Relation.ReflTransGen (fun a b => r a * r b ≠ r b * r a) a b) ∧
      Subgroup.closure (Set.range r) = A.map (MulAut.congr eta).toMonoidHom := by
  let g : M'.Group →* MulAut (Fin n → Multiplicative (ZMod p)) :=
    (MulAut.congr eta).toMonoidHom.comp (A.subtype.comp f.toMonoidHom)
  let r : κ → MulAut (Fin n → Multiplicative (ZMod p)) := fun i => g (M'.simple i)
  have hmem : ∀ k, r k ∈ bSignedFull n p := fun k =>
    hA (Subgroup.mem_map.mpr ⟨((f (M'.simple k) : ↥A) : MulAut ↥Bs), (f (M'.simple k)).2, rfl⟩)
  have hdata : ∀ k, (r k) ^ 2 = 1 ∧
      Nat.card {x : Fin n → Multiplicative (ZMod p) // r k x = x} * p =
        Nat.card (Fin n → Multiplicative (ZMod p)) := fun k =>
    congr_reflection_data eta (hf k)
  have hr : ∀ k, (∃ i, r k = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (r k = permAut (Equiv.swap a b) ∨
        r k = sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) :=
    fun k => eq_sgnAut_or_swap_of_isRefl hp hp2 (hmem k) (hdata k).1 (hdata k).2
  have hconn : ∀ a b, Relation.ReflTransGen
      (fun a b => r a * r b ≠ r b * r a) a b :=
    reflTransGen_ne_comm_of_weyl hM' (MonoidHom.id _) r g
      ((MulAut.congr eta).injective.comp (Subtype.val_injective.comp f.injective))
      (fun i => rfl)
  have hclosure : Subgroup.closure (Set.range r) = A.map (MulAut.congr eta).toMonoidHom := by
    have hmap := map_closure_range_eq_of_simple M' (MonoidHom.id _) r g (fun i => rfl)
    have hrange : g.range = A.map (MulAut.congr eta).toMonoidHom := by
      rw [MonoidHom.range_comp, MonoidHom.range_comp,
        MonoidHom.range_eq_top.mpr f.surjective, Subgroup.map_top, Subgroup.range_subtype]
    rw [← hrange]
    simpa using hmap
  exact ⟨r, hr, hconn, hclosure⟩

theorem exists_conj_eq_block_of_weyl {G : Type} [Group G] {p n : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {A : Subgroup (MulAut ↥Bs)} (hA : A.map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n p)
    (hW : GGWeylReflectionGroup p A) (hfix : Nat.card {b : ↥Bs // ∀ φ ∈ A, φ b = b} = p) :
    ∃ δ ∈ bSignedFull n p, ∃ i0 : Fin n,
      (A.map (MulAut.congr eta).toMonoidHom).map (MulAut.conj δ).toMonoidHom =
          bCoordinateBlock n p i0 ∨
        (A.map (MulAut.congr eta).toMonoidHom).map (MulAut.conj δ).toMonoidHom =
          dCoordinateBlock n p i0 ∨
        (A.map (MulAut.congr eta).toMonoidHom).map (MulAut.conj δ).toMonoidHom =
          aPermutationFull n p := by
  obtain ⟨κ, M', hM', f, hf⟩ := hW
  obtain ⟨r, hr, hconn, hclosure⟩ := exists_reflections_with_closure hp hp2 eta hA hM' f hf
  have hfixA : Nat.card {v : Fin n → Multiplicative (ZMod p) //
      ∀ u ∈ Subgroup.closure (Set.range r), u v = v} = p := by
    rw [hclosure]
    exact (card_fixedPoints_map_congr eta A).trans hfix
  rw [← hclosure]
  exact exists_conj_eq_block_of_connected hp hp2 r hr hconn hfixA

theorem exists_isSignedBlockOn_of_weyl {G : Type} [Group G] {p n : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {A : Subgroup (MulAut ↥Bs)} (hA : A.map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n p)
    (hW : GGWeylReflectionGroup p A) :
    ∃ I : Finset (Fin n), IsSignedBlockOn n p I (A.map (MulAut.congr eta).toMonoidHom) := by
  obtain ⟨κ, M', hM', f, hf⟩ := hW
  obtain ⟨r, hr, hconn, hclosure⟩ := exists_reflections_with_closure hp hp2 eta hA hM' f hf
  rw [← hclosure]
  exact closure_isSignedBlockOn_of_connected hp hp2 r hr hconn

theorem bOriginalPositionTheoryInput_holds : BOriginalPositionTheoryInput := by
  intro hTBF hWI hX hTCJ hRig G _ _ p B Bs x L D J 𝒦 hR n hn e hP
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨h4, eta, hEta⟩ := GGSecFiveRouteCfg.exists_bSignedFull_coords hR hTBF hWI hn e hP
  have hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n p := by
    rw [← hEta]
    exact Subgroup.map_mono fun _ hφ => Subgroup.mem_sup_left hφ
  obtain ⟨-, hBs, -, -, -⟩ := hR.1.1.tableB_facts
  have hfix : Nat.card {b : ↥Bs // ∀ φ ∈ ggAutomizer L Bs, φ b = b} = p :=
    (hR.1.fixLineComp_L hTBF hR.2.1).card_fix hp hBs hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  obtain ⟨δ, hδ, i0, hblock⟩ := exists_conj_eq_block_of_weyl hp hp2 eta hA
    (GGSecFiveRestHyp.weylReflectionGroup_L hX hTCJ hRig hR.1 hR.2.1) hfix
  let eta' : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)) := eta.trans δ
  have hcongr : (MulAut.congr eta').toMonoidHom =
      (MulAut.conj δ).toMonoidHom.comp (MulAut.congr eta).toMonoidHom := by
    refine MonoidHom.ext fun φ => ?_
    change MulAut.congr (eta.trans δ) φ = (MulAut.conj δ) (MulAut.congr eta φ)
    rw [CFSG.SeitzReduction.SymplecticPilot.mulAut_congr_trans_apply eta δ φ,
      CFSG.RankThree.PartTwo.Sec4.mulAut_congr_eq_conj, MulAut.conj_apply]
  have hjoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta').toMonoidHom =
      bSignedFull n p := by
    rw [hcongr, ← Subgroup.map_map, hEta, CFSG.Walter.map_conj_eq_self_of_mem hδ]
  have hblock' : (ggAutomizer L Bs).map (MulAut.congr eta').toMonoidHom =
      bCoordinateBlock n p i0 ∨
      (ggAutomizer L Bs).map (MulAut.congr eta').toMonoidHom = dCoordinateBlock n p i0 ∨
      (ggAutomizer L Bs).map (MulAut.congr eta').toMonoidHom = aPermutationFull n p := by
    have heq : (ggAutomizer L Bs).map (MulAut.congr eta').toMonoidHom =
        ((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom).map
          (MulAut.conj δ).toMonoidHom := by
      rw [hcongr, ← Subgroup.map_map]
    rw [heq]
    exact hblock
  exact ⟨h4, eta', i0, hjoin, hblock'⟩

end CFSG.StandardType

end
