module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofSLThree
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofTools
public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def K423CoverFrame : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H) [L.Normal], IsQuasisimple L →
    aschbacherSolvableCore 3 L = ⊥ → IsList46 L → Subgroup.center L ≠ ⊥ →
    ¬ IsSLThreePiAny L →
  ∀ (A : Subgroup H) (c : H),
    Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
    orderOf c = 3 → A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c →
    autIn A L ≤ (MulAut.conj : L →* MulAut L).range →
  ∀ Y : Subgroup (MulAut L), (MulAut.conj : L →* MulAut L).range ≤ Y →
    thetaAlpha 3 ((autIn A L).subgroupOf Y) ≠ ⊥ →
      IsHeisCentral ↥(A ⊔ L) ↥L ∧
        (IsTripleCover L (alternatingGroup (Fin 7)) ∨
          IsTripleCover L CFSG.Blueprint.NativeSporadic.M22) ∧
        CFSG.Assembly.IsElemAbelian 3 (autIn L A) ∧ Nat.card (autIn L A) = 9

namespace Res423Four

open Sec21.Item211Proof

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G}

theorem map_autThetaQuot_eq (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {Φ₀ : Sec21.lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : Sec21.lBar L) : QuotX L A) =
      piX L A ⟨l, Subgroup.mem_sup_left l.2⟩) :
    (autThetaQuot A L).map (MulAut.congr Φ₀).toMonoidHom = autIn (aOne L A) (lOne L A) := by
  have key : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)) (hxA : x ∈ A),
      MulAut.congr Φ₀ (thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hx⟩)) =
        (lOne L A).normalizerMonoidHom
          ⟨_, mem_normalizer_lOne hAL (piX L A ⟨x, Subgroup.mem_sup_right hxA⟩)⟩ := by
    intro x hx hxA
    refine MulEquiv.ext fun z => ?_
    change Φ₀ (thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hx⟩) (Φ₀.symm z)) = _
    rw [lEquiv_conj hΦ₀ hxA hx _ (Φ₀.symm z), MulEquiv.apply_symm_apply]
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨x, hx, hxA, rfl⟩ := mem_autThetaQuot_iff.mp hτ
    change MulAut.congr Φ₀ _ ∈ _
    rw [key x hx hxA]
    exact mem_autIn_iff.mpr ⟨_, _, piX_mem_aOne hxA, rfl⟩
  · intro hσ
    obtain ⟨y, hy, hyA, rfl⟩ := mem_autIn_iff.mp hσ
    obtain ⟨x, hxA, rfl⟩ := exists_eq_piX_of_mem_aOne hyA
    exact ⟨_, mem_autThetaQuot_iff.mpr ⟨x, hAL hxA, hxA, rfl⟩, key x (hAL hxA) hxA⟩

theorem range_conj_le_map_autThetaQuot_top (Φ₀ : Sec21.lBar L ≃* lOne L A) :
    (MulAut.conj : lOne L A →* MulAut (lOne L A)).range ≤
      (autThetaQuot ⊤ L).map (MulAut.congr Φ₀).toMonoidHom := by
  rintro _ ⟨l, rfl⟩
  refine ⟨MulAut.conj (Φ₀.symm l), Config423.range_conj_le_autThetaQuot_top L ⟨_, rfl⟩, ?_⟩
  change MulAut.congr Φ₀ (MulAut.conj (Φ₀.symm l)) = MulAut.conj l
  rw [Res423Two.mulAut_congr_conj, MulEquiv.apply_symm_apply]

end Res423Four

open Res423Four Sec21.Item211Proof

section Main


theorem k423Cover_of (h45 : Item4_5) (h46 : Item4_6) (hF : K423CoverFrame) : K423Cover := by
  intro G _ _ A L a h h9 hα hany hZ hinner
  have hAL := h.le_normalizer h45
  have hA : IsPGroup 3 A := h.isPGroup
  have hCA := h.inf_thetaQuotCentralizer hAL
  have hLsn : L.IsSubnormal := h.mem_thetaComponents.2.1
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAL
  have hL₁n : (lOne L A).Normal := normal_lOne hAL
  have hLq : IsQuasisimple (lOne L A) :=
    LocalCores.isQuasisimple_of_mulEquiv Φ₀ h.isQuasisimple_L
  have hmax : Maximal (fun B : Subgroup (QuotX L A) => CFSG.Assembly.IsElemAbelian 3 B)
      (aOne L A) :=
    maximal_aOne h.isElemAbelian (fun B hB hAB => h.maximal.eq_of_ge hB hAB)
  have hA27 : Nat.card (aOne L A) = 27 := by
    rw [← Nat.card_congr (aEquiv (L := L) hA).toEquiv, h.card_eq]
  set c₁ : QuotX L A := piX L A ⟨a, Subgroup.mem_sup_right h.a_mem⟩ with hc₁def
  have hc₁ : orderOf c₁ = 3 := by
    have h1 : c₁ = ((aEquiv (L := L) hA ⟨a, h.a_mem⟩ : aOne L A) : QuotX L A) := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact h.orderOf_a
  have hAc₁ : aOne L A ⊓ Subgroup.centralizer (lOne L A : Set (QuotX L A)) =
      Subgroup.zpowers c₁ := aOne_inf_centralizer hA hAL h.a_mem hCA
  obtain ⟨eT⟩ := nonempty_sup_equiv_thetaImage hLsn hA hAL
  obtain ⟨eAut⟩ := nonempty_autIn_lOne_equiv' hA hAL
  have h3 : 3 ∣ Nat.card (Subgroup.center G) := by
    rw [← h.orderOf_a]
    exact Subgroup.orderOf_dvd_natCard _ h.a_mem_center
  have hL46 : IsList46 (lOne L A) := Sec21.Item223PrintProof.isList46_of_mulEquiv Φ₀
    (h46 G h.sectionFourHyp h3 L h.mem_thetaComponents)
  have hZ₁ : Subgroup.center (lOne L A) ≠ ⊥ := by
    intro hbot
    apply hZ
    rw [← Sec13.map_center_mulEquiv Φ₀.symm, hbot, Subgroup.map_bot]
  have hSL₁ : ¬ IsSLThreePiAny (lOne L A) := by
    rintro (hS | ⟨p, e, hp, he, hiso⟩)
    · exact hany (Or.inl (Sec13.isSLThreePi_of_mulEquiv Φ₀.symm hS))
    · exact hany (Or.inr ⟨p, e, hp, he, Sec21.Item211Proof.isoLThreePi_of_mulEquiv Φ₀.symm hiso⟩)
  have hB := map_autThetaQuot_eq hAL hΦ₀
  have hinn₁ : autIn (aOne L A) (lOne L A) ≤
      (MulAut.conj : lOne L A →* MulAut (lOne L A)).range := by
    rw [← hB]
    rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨x, hx, hxA, rfl⟩ := mem_autThetaQuot_iff.mp hτ
    have hin : thetaQuotMulAut L (compAction L ⟨x, hx⟩) ∈
        (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* MulAut _).range := by
      by_contra hout
      exact hinner x hxA ⟨hx, hout⟩
    obtain ⟨w, hw⟩ := hin
    refine ⟨Φ₀ w, ?_⟩
    change MulAut.conj (Φ₀ w) = MulAut.congr Φ₀ _
    rw [← Res423Two.mulAut_congr_conj, hw]
    rfl
  have hα₁ : thetaAlpha 3 ((autIn (aOne L A) (lOne L A)).subgroupOf
      ((autThetaQuot ⊤ L).map (MulAut.congr Φ₀).toMonoidHom)) ≠ ⊥ := by
    rw [← hB]
    exact (Sec13.thetaAlpha_subgroupOf_map_ne_bot_iff (MulAut.congr Φ₀) _ _).mpr hα
  obtain ⟨hHeis, hTC, hab, hcard9⟩ := hF _ _ hLq (theta_lOne_eq_bot Φ₀) hL46 hZ₁ hSL₁ _ _ hmax
    hA27 hc₁ hAc₁ hinn₁ _ (range_conj_le_map_autThetaQuot_top Φ₀) hα₁
  refine Or.inr (Or.inr (Or.inl ⟨Sec13.isHeisCentral_of_mulEquiv eT Φ₀.symm hHeis, ?_,
    Sec21.Item211Proof.isElemAbelian_of_mulEquiv eAut hab,
    by rw [← Nat.card_congr eAut.toEquiv, hcard9]⟩))
  rcases hTC with h7 | h22
  · exact Or.inl (Sec13.isTripleCover_of_mulEquiv Φ₀.symm h7)
  · exact Or.inr (Or.inl (Sec13.isTripleCover_of_mulEquiv Φ₀.symm h22))

end Main

end CFSG.RankThree.PartTwo.Sec4
