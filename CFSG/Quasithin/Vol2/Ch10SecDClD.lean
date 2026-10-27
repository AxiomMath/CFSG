module

public import CFSG.Quasithin.Vol2.Ch10SecDClC
public import CFSG.Quasithin.Vol2.Ch10SecD33

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isLocal_of_le
    (hW : FactSymFiveWrTwo) (hA : FactPSL2NormA5) (hAut : FactAutSL)
    (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat) (h1024 : Stmt10_2_4)
    {T L I : Subgroup G} (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {P Y H K₁ : Subgroup G} {s y : G}
    (hPmax : IsMaxSubgroupIn (fsuL0 T L ⊔ T) P) (hTP : T ≤ P)
    (hHM : ¬ H ≤ fsuM T L) (hHY : H ≤ Y) (hTY : IsSylowTwoOf T Y)
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo) (hK₁ : K₁ ∈ cComp Y) (hs : s ∈ T)
    (hO : oTwoUpper H ≤ K₁ ⊔ CFSG.conjugate K₁ s) (hKT : K₁ ⊔ CFSG.conjugate K₁ s ⊔ T = H)
    (hXK : oTwoUpper P ≤ K₁ ⊔ CFSG.conjugate K₁ s) (hXM : oTwoUpper P ≤ fsuM T L)
    (hyX : y ∈ oTwoUpper P) (hyo : Odd (orderOf y)) (hy1 : y ≠ 1)
    {K' : Subgroup G} (hK' : quasithinIsLocal T K') (hle : K₁ ≤ K') : K' = K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hKT ▸ le_sup_right
  have hKzH : K₁ ⊔ CFSG.conjugate K₁ s ≤ H := hKT ▸ le_sup_left
  have hK₁H : K₁ ≤ H := le_sup_left.trans hKzH
  have hsY : s ∈ Y := hTY.1 hs
  have hY2 : pCoreOf 2 Y ≤ H := (IsSylowTwoOf.pCoreOf_le hTY).trans hTH
  have hyH : y ∈ H := hKzH (hXK hyX)
  have hTH' : T ≤ K' ⊔ T := le_sup_right
  have hsH' : s ∈ K' ⊔ T := hTH' hs
  have hK'c : K' ∈ cComp (K' ⊔ T) := hK'.2.1
  have hH'2 : pCoreOf 2 (K' ⊔ T) ≠ ⊥ := hK'.2.2.2
  have hT' : IsSylowTwoOf T (K' ⊔ T) := ⟨hTH', hK'.1, hK'.2.2.1⟩
  have hK₁H' : K₁ ≤ K' ⊔ T := hle.trans le_sup_left
  have hKzH' : K₁ ⊔ CFSG.conjugate K₁ s ≤ K' ⊔ T :=
    sup_le hK₁H' (conjugate_le_of_mem hK₁H' hsH')
  have hHH' : H ≤ K' ⊔ T := hKT ▸ sup_le hKzH' hTH'
  have hInH : InH (oTwoUpper P ⊔ T) (K' ⊔ T) := ⟨sup_le (hXK.trans hKzH') hTH', hH'2⟩
  have h4 := h1024 G T L I h h3.1 (not_case10_1_1Five h3 hc) P hPmax hTP (K' ⊔ T) hInH
  have hXJ : oTwoUpper P ≤ KOf P (K' ⊔ T) := le_conjClosure _ _
  have hJN : K' ⊔ T ≤ Subgroup.normalizer (KOf P (K' ⊔ T) : Set G) :=
    le_normalizer_conjClosure _ _
  have hnot : ¬ ∀ j ∈ KOf P (K' ⊔ T), ∀ k ∈ K', j * k * j⁻¹ * k⁻¹ ∈ pCoreOf 2 (K' ⊔ T) :=
    fun hJK => false_of_comm hW e hHY hK₁ hsY hO hY2 hK₁H' hsH' hyH (hXK hyX) hyo hy1
      (fun k hk => hJK y (hXJ hyX) k (hle hk))
      (fun k hk => hJK _ ((Subgroup.mem_normalizer_iff.mp (hJN hsH') y).mp (hXJ hyX)) k
        (hle hk))
  rcases h4 with h4 | ⟨J₁, u, hu, hJ₁, hun, hJeq, htype⟩ | ⟨hJc, k, hk, ⟨eA⟩⟩
  ·
    exfalso
    have hXN : H ≤ Subgroup.normalizer (oTwoUpper P : Set G) := by
      rw [← h4]
      exact hHH'.trans hJN
    apply hHM
    rw [← oTwoUpper_sup_eq (A4.isSylowTwoOf_mono hTY hTH hHY)]
    refine sup_le (le_trans ?_ hXM) (SecA.le_fsuM T L)
    exact (Subgroup.closure_le _).mpr fun x hx =>
      forall_odd_mem_of_normal hW e (hXK.trans hKzH) hXN hyX hyo hy1 hx.1 hx.2
  ·
    have hJ₂ : CFSG.conjugate J₁ u ∈ cComp (K' ⊔ T) := conjugate_mem_cComp hJ₁ (hTH' hu)
    have hK'J : K' = J₁ ∨ K' = CFSG.conjugate J₁ u := by
      by_contra hne
      push Not at hne
      apply hnot
      have h1 := (Vol2Native.lemma_1_2_1_two hK h37 hH'2 hK'c hJ₁ hne.1).1
      have h2 := (Vol2Native.lemma_1_2_1_two hK h37 hH'2 hK'c hJ₂ hne.2).1
      have hN : K' ⊔ (J₁ ⊔ CFSG.conjugate J₁ u) ≤ Subgroup.normalizer (K' : Set G) :=
        sup_le Subgroup.le_normalizer (sup_le (le_normalizer_of_mem_cComp hK'c hJ₁)
          (le_normalizer_of_mem_cComp hK'c hJ₂))
      refine comm_mem_of_commutator_le (subnormal_of_mem_cComp hK'c) ?_
      rw [hJeq, SecA.commutator_sup_left_of_le le_sup_left (le_sup_left.trans le_sup_right)
        (le_sup_right.trans le_sup_right) hN]
      exact sup_le (h1.trans inf_le_left) (h2.trans inf_le_left)
    have hK'J' : K' ≤ KOf P (K' ⊔ T) := by
      rw [hJeq]
      rcases hK'J with h' | h'
      · rw [h']
        exact le_sup_left
      · rw [h']
        exact le_sup_right
    have hKzJ : K₁ ⊔ CFSG.conjugate K₁ s ≤ KOf P (K' ⊔ T) := by
      refine sup_le (hle.trans hK'J') fun x hx => ?_
      have hx' : s * x * s⁻¹ ∈ K₁ := SecA.mem_conjugate_iff.mp hx
      have e1 : x = s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ := by group
      rw [e1]
      exact (Subgroup.mem_normalizer_iff.mp (hJN ((K' ⊔ T).inv_mem hsH')) _).mp
        (hle.trans hK'J' hx')
    have hTJ : T ≤ Subgroup.normalizer ((J₁ ⊔ CFSG.conjugate J₁ u : Subgroup G) : Set G) := by
      rw [← hJeq]
      exact hTH'.trans hJN
    have hOJ : oTwoUpper H ≤ J₁ ⊔ CFSG.conjugate J₁ u := by
      rw [← hJeq]
      exact hO.trans hKzJ
    have hJ₁H := le_of_case_two hW hA hK h37 hH'2 hJ₁ hu hun hTJ hT' hTH hHH' hOJ e htype
    have hJ₂H : CFSG.conjugate J₁ u ≤ H := conjugate_le_of_mem hJ₁H (hTH hu)
    have hK'H : K' ≤ H := by
      rcases hK'J with h' | h'
      · rw [h']
        exact hJ₁H
      · rw [h']
        exact hJ₂H
    have hK'cH : K' ∈ cComp H := cComp_mem_of_le hK'c hK'H hHH'
    have hK₁cH : K₁ ∈ cComp H := cComp_mem_of_le hK₁ hK₁H hHY
    by_contra hne
    exact hK'cH.2.2.2 K₁ (lt_of_le_of_ne hle (Ne.symm hne)) (ne_bot_of_mem_cComp hK₁)
      (perfect_of_mem_cComp hK₁) (subnormal_of_mem_cComp hK₁cH)
  ·
    exfalso
    have hK'J : K' = KOf P (K' ⊔ T) := by
      by_contra hne
      apply hnot
      exact comm_mem_of_commutator_le (subnormal_of_mem_cComp hK'c)
        ((Vol2Native.lemma_1_2_1_two hK h37 hH'2 hK'c hJc hne).1.trans inf_le_left)
    have hHJ : H ≤ KOf P (K' ⊔ T) ⊔ T := by
      rw [← hK'J]
      exact hHH'
    exact false_of_le_aut hAut hHJ e hk eA

end CFSG.Quasithin.Vol2.Ch10.SecD
