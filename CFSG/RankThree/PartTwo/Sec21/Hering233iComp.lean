module

public import CFSG.RankThree.PartTwo.Sec21.Item233ComponentsOf
import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

theorem item233Components_at (h45 : Sec4.Item4_5) (h232 : Item232) {G : Type} [Group G]
    [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G} (hpair : Sec21Pair G A E U c L)
    {B : Subgroup G} (hBA : B ≤ A) (hB3 : Nat.card B = 3)
    (hi : ∀ X : Subgroup (iGroup A ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
      CFSG.IsComponent X → X.map (iGroup A ⊓ Subgroup.centralizer (B : Set G)).subtype ∈
        thetaComponentsIn (Subgroup.centralizer (B : Set G))) :
    Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (layerCent (iGroup A) B : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAp : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  obtain ⟨hAI, h2⟩ := h232 G A E U c L hpair
  obtain ⟨Q, hQ⟩ := (hAp.comap_subtype (K := iGroup A)).exists_le_sylow
  have hAQ : A ≤ (Q : Subgroup (iGroup A)).map (iGroup A).subtype := by
    intro a ha
    exact ⟨⟨a, hAI ha⟩, hQ (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  obtain ⟨-, hJ, hW, S, hS⟩ := h2 Q hAQ
  have hJ' : (CFSG.elemThompson (S : Subgroup G) 3).map (S : Subgroup G).subtype = A := by
    rw [hS]; exact hJ
  have huniq := unique_of_elemThompson_eq S hAe hJ'
  have hB1 : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB3
    omega
  obtain ⟨⟨b, hbB⟩, hb'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  have hb1 : b ≠ 1 := fun h => hb' (Subtype.ext h)
  have hBb := eq_zpowers_of_card_three hB3 hbB hb1
  have hCB : Subgroup.centralizer (B : Set G) = Subgroup.centralizer ({b} : Set G) := by
    rw [hBb, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  set H := Subgroup.centralizer (B : Set G) with hHdef
  set K := iGroup A ⊓ H with hKdef
  set Y := layerCent (iGroup A) B with hYdef
  have hAH : A ≤ H := le_centralizer_of_isElemAbelian hAe hBA
  have h45b : ∀ X ∈ thetaComponentsAt 3 b, A ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe
      (hBA hbB) hb1
  have hwY : ∀ w ∈ H, w ∈ nGroup A → Y.map (MulAut.conj w).toMonoidHom = Y := by
    intro w hwH hwN
    have hI : (iGroup A).map (MulAut.conj w).toMonoidHom = iGroup A := map_conj_eq_self hwN
    have hH : H.map (MulAut.conj w).toMonoidHom = H :=
      map_conj_eq_self (Subgroup.le_normalizer hwH)
    have hK : K.map (MulAut.conj w).toMonoidHom = K := by
      rw [hKdef, Subgroup.map_inf_eq _ _ _ (MulAut.conj w).injective, hI, hH]
    rw [hYdef, layerCent, ← hKdef, map_inSubgroup_layer (MulAut.conj w) K]
    change inSubgroup CFSG.layer (K.map (MulAut.conj w).toMonoidHom) = _
    rw [hK]
  have key : ∀ h ∈ H, ∀ X : Subgroup K, CFSG.IsComponent X →
      (X.map K.subtype).map (MulAut.conj h).toMonoidHom ≤ Y := by
    intro h hh X hX
    set X' := X.map K.subtype with hX'def
    have hX'Y : X' ≤ Y := Subgroup.map_mono (CFSG.LocalCores.component_le_layer hX)
    have hX'θ : X' ∈ thetaComponentsAt 3 b := by
      rw [thetaComponentsAt_eq_thetaComponentsIn, ← hCB]
      exact hi X hX
    have hhb : MulAut.conj h b = b := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hCB ▸ hh)
      rw [MulAut.conj_apply, this, mul_inv_cancel_right]
    have hX'hθ : X'.map (MulAut.conj h).toMonoidHom ∈ thetaComponentsAt 3 b := by
      have := map_mem_thetaComponentsAt (MulAut.conj h) hX'θ
      rwa [hhb] at this
    set M := Subgroup.normalizer (X' : Set G) ⊓ H
    have hAM : A ≤ M := le_inf (h45b X' hX'θ) hAH
    have hAhM : A.map (MulAut.conj h⁻¹).toMonoidHom ≤ M := by
      refine le_inf ?_ ?_
      · have h1 := map_conj_le_normalizer_map (h45b _ hX'hθ) h⁻¹
        rwa [map_conj_map_conj', inv_mul_cancel, show (MulAut.conj (1 : G)).toMonoidHom =
          MonoidHom.id G from by ext; simp, Subgroup.map_id] at h1
      · rintro _ ⟨a, ha, rfl⟩
        exact H.mul_mem (H.mul_mem (H.inv_mem hh) (hAH ha)) (H.inv_mem (H.inv_mem hh))
    obtain ⟨m, hmM, hmA⟩ := exists_mem_map_conj_eq hAe huniq hAM hAhM
      (isElemAbelian_map hAe _) (le_of_eq
        (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).symm)
    have hwA : h * m ∈ Subgroup.normalizer (A : Set G) := by
      have h1 : A.map (MulAut.conj (m⁻¹ * h⁻¹)).toMonoidHom = A := by
        rw [← map_conj_map_conj', hmA]
      have h2 := Subgroup.inv_mem _ (mem_normalizer_of_map_conj_eq_self' h1)
      rwa [_root_.mul_inv_rev, inv_inv, inv_inv] at h2
    have hwH : h * m ∈ H := H.mul_mem hh hmM.2
    have hX'm : X'.map (MulAut.conj m⁻¹).toMonoidHom = X' :=
      map_conj_eq_self (Subgroup.inv_mem _ hmM.1)
    calc X'.map (MulAut.conj h).toMonoidHom
        = (X'.map (MulAut.conj m⁻¹).toMonoidHom).map (MulAut.conj (h * m)).toMonoidHom := by
          rw [map_conj_map_conj', mul_inv_cancel_right]
      _ = X'.map (MulAut.conj (h * m)).toMonoidHom := by rw [hX'm]
      _ ≤ Y.map (MulAut.conj (h * m)).toMonoidHom := Subgroup.map_mono hX'Y
      _ = Y := hwY _ hwH (hW hwA)
  have hYh : ∀ h ∈ H, Y.map (MulAut.conj h).toMonoidHom ≤ Y := by
    intro h hh
    rw [hYdef, layerCent, ← hKdef, inSubgroup, CFSG.layer, Subgroup.map_map,
      (Subgroup.gc_map_comap _).l_sSup]
    refine iSup₂_le fun X hX => ?_
    rw [← Subgroup.map_map]
    exact key h hh X hX
  intro h hh
  refine mem_normalizer_of_map_conj_eq_self' (le_antisymm (hYh h hh) ?_)
  intro y hy
  have h1 := hYh h⁻¹ (H.inv_mem hh) ⟨y, hy, rfl⟩
  exact ⟨_, h1, by simp [MulAut.conj_apply, mul_assoc]⟩

end CFSG.RankThree.PartTwo.Sec21
