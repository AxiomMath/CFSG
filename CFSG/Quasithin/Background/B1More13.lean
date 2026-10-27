module

public import CFSG.Quasithin.Background.B1More13B
public import CFSG.Quasithin.Background.B1More13C
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

theorem B1_13 {𝒦 : ∀ (X : Type) [Group X], Prop} {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) (hI : AsB113Inputs 𝒦) {G T K : Subgroup (MulAut V)} (hGK : 𝒦 ↥G)
    (hO2 : pCoreOf 2 G = ⊥) (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G) (hKG : K ≤ G)
    (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) (hsub : IsSubnormal K (K ⊔ T))
    (hKJ : ⁅K, ffJP {A | IsFFStarOffender G A} T⁆ = K) : B113Conclusion G K := by
  have hTG : T ≤ G := hT.1
  rw [B113.ffJP_eq_ffJ hTG] at hKJ
  have hsub' : IsSubnormal K (T ⊔ K) := by rwa [sup_comm] at hsub
  have hK' : CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3 :=
    hK.imp B1Red.isQuasisimple_to_open id
  have hK0 : K ≠ ⊥ := B113.ne_bot_of_quasisimple_or_card_three hK'
  obtain ⟨A₀, hA₀, -, hKA₀⟩ := B113.exists_offender_commutator_eq hTG hKJ hK0 hK'
  have hKF : K ≤ Subgroup.centralizer (fittingOf G : Set (MulAut V)) := fun k hk =>
    (B1_10 hV hO2 hKG hA₀ hKA₀ hK hk).2
  have hJcomp : ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L G →
      ffJ T ≤ Subgroup.normalizer (L : Set (MulAut V)) := fun L hL =>
    B113.ffJ_le_normalizer_comps hI.timmesfeld hV hTG hL
  have hKcomp : ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L G →
      K ≤ Subgroup.normalizer (L : Set (MulAut V)) := fun L hL =>
    B113.le_normalizer_of_commutator_of_comps hKG hJcomp hKJ hL
  by_cases hcent : ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L G →
      K ≤ Subgroup.centralizer (L : Set (MulAut V))
  ·
    exact Or.inl (B113.case_centralizes_components hKG hKF hcent hK)
  push Not at hcent
  obtain ⟨L, hL, hKL⟩ := hcent
  right
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLqF : CFSG.IsQuasisimple ↥L := B1Red.isQuasisimple_of_open hLq
  have hKnL : ∀ b ∈ K, ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun b hb l hl =>
    B19Aux.conj_mem_of_le_normalizer (hKcomp L hL) hb hl
  have hJnL : ∀ b ∈ ffJ T, ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun b hb l hl =>
    B19Aux.conj_mem_of_le_normalizer (hJcomp L hL) hb hl
  have hLJ : ⁅L, ffJ T⁆ = L := by
    rcases B1Red.commutator_eq_or_commute (Or.inl hLq) hJnL with h | h
    · exact h
    · exfalso
      apply hKL
      calc K = ⁅K, ffJ T⁆ := hKJ.symm
        _ ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
          rw [Subgroup.commutator_le]
          intro k hk j hj
          have hjc : j ∈ Subgroup.centralizer (L : Set (MulAut V)) :=
            Subgroup.mem_centralizer_iff.2 fun l hl => (h j hj l hl).symm
          have hjc' : j⁻¹ ∈ Subgroup.centralizer (L : Set (MulAut V)) :=
            (Subgroup.centralizer (L : Set (MulAut V))).inv_mem hjc
          have h1 := B113.conj_mem_centralizer_of_normalizes (hKcomp L hL hk) hjc
          have h3 : ⁅k, j⁆ = (k * j * k⁻¹) * j⁻¹ := rfl
          rw [h3]
          exact Subgroup.mul_mem _ h1 hjc'
  obtain ⟨A, hA, -, hLA⟩ := B113.exists_offender_commutator_eq hTG hLJ
    (B113.ne_bot_of_quasisimple_or_card_three (Or.inl hLq)) (Or.inl hLq)
  have hdet : IsLieAltType ↥L := hI.determination V hV G A L hGK hO2 hA hL hLA
  have hTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B113.isSylowTwoOf_inf_of_isSubnormal hT hL.2.1
  have hdich : K ≤ L ∨
      K ≤ Subgroup.centralizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rcases hK with hq | h3
    · have hKH : CFSG.Open.IsComponentOf K (K ⊔ T) :=
        ⟨le_sup_left, hsub, B1Red.isQuasisimple_to_open hq⟩
      have hX : IsSubnormal ((K ⊔ T) ⊓ L) (K ⊔ T) :=
        B113.isSubnormal_inf_of_le hL.2.1 (sup_le hKG hTG)
      rcases B113.component_le_or_commutator_eq_bot hKH hX with h | h
      · exact Or.inl (h.trans inf_le_right)
      · right
        have h1 : ⁅K, T ⊓ L⁆ ≤ ⁅K, (K ⊔ T) ⊓ L⁆ :=
          Subgroup.commutator_mono le_rfl (inf_le_inf_right L le_sup_right)
        rw [h] at h1
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 h1)
    · have hMnormL : twelveM T K ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
        sup_le (hJcomp L hL) (conjClosure_le fun t ht z hz =>
          B113.conj_mem_normalizer_of_comps hKcomp hL (hTG ht) hz)
      exact B113.card_three_le_or_centralizes hV hT h3 hKJ hsub' hMnormL (hKcomp L hL)
  rcases hdich with hKLle | hKcent
  swap
  ·
    exfalso
    apply hKL
    refine B113.le_centralizer_of_odd hK' fun x hx hxo => ?_
    exact hI.sylowCentralizer (MulAut V) L (T ⊓ L) hLqF hdet hTL x (hKcomp L hL hx) (hKcent hx)
      hxo
  by_cases hKeq : K = L
  · subst hKeq
    exact Or.inl ⟨hL, hdet⟩
  right
  refine ⟨L, hL, hKLle, ?_⟩
  have hXH : (K ⊔ T) ⊓ L ≤ K ⊔ T := inf_le_left
  have hKX : K ≤ (K ⊔ T) ⊓ L := le_inf le_sup_left hKLle
  have hKXsub : IsSubnormal K ((K ⊔ T) ⊓ L) := by
    have := B113.isSubnormal_inf_of_le hsub hXH
    rwa [inf_of_le_right hKX] at this
  have hXne : (K ⊔ T) ⊓ L ≠ L := by
    intro hXL
    have hKL' : IsSubnormal K L := by rwa [hXL] at hKXsub
    have h1 : IsSubnormal (K.subgroupOf L) ⊤ := (isSubnormal_subgroupOf_top_iff hKLle).2 hKL'
    rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hLq _ h1 with
      hc | htop
    · apply hKL
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have := Subgroup.mem_center_iff.1
        (hc (show (⟨k, hKLle hk⟩ : ↥L) ∈ K.subgroupOf L from hk)) ⟨l, hl⟩
      exact congrArg Subtype.val this
    · apply hKeq
      refine le_antisymm hKLle fun l hl => ?_
      have : (⟨l, hl⟩ : ↥L) ∈ K.subgroupOf L := by rw [htop]; trivial
      exact this
  exact hI.overgroups (MulAut V) L (T ⊓ L) ((K ⊔ T) ⊓ L) K hLqF hdet hTL
    (inf_le_inf_right L le_sup_right) inf_le_right hXne hKX hKXsub hK hKL

end CFSG.Quasithin
