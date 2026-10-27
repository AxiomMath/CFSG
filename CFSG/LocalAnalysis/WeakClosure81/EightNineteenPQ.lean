module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPBorel
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFit
import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)

variable {Q : Type} [Group Q] [Finite Q] {T A B R L₀ : Subgroup Q}

private theorem wc819pq_card_isL2 {X : Type} [Group X] (h : IsL2 X 2) : Nat.card X = 60 := by
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h]
  decide

theorem Cfg813.inf_ne_bot (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (hF2 : FourGroupInnerFact) (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) : T ⊓ J ≠ ⊥ := by
  classical
  obtain ⟨J₁, hJ₁, hne⟩ := h.exists_component
  obtain ⟨hAst, -, hAstCard, -⟩ := h.astar_facts hF0 hF1 hF2 hJ₁ hne
  have hSne₁ : T ⊓ J₁ ≠ ⊥ := by
    intro hbot
    have hzero : Astar T J₁ A = ⊥ := le_bot_iff.mp (hAst.trans (le_of_eq hbot))
    have hcard : Nat.card (Astar T J₁ A) = 1 := by rw [hzero, Subgroup.card_bot]
    omega
  obtain ⟨t, htT, hJeq⟩ := h.component_conj hJ₁ hJ
  have hTconj : conjSubgroup T t = T := by
    rw [conjSubgroup_eq_iff_mem_normalizer]
    exact Subgroup.le_normalizer htT
  have hconj : conjSubgroup (T ⊓ J₁) t = T ⊓ J := by
    rw [conjSubgroup, Subgroup.map_inf _ _ _ (MulAut.conj t⁻¹).injective]
    rw [← conjSubgroup, ← conjSubgroup, hTconj, hJeq]
  rw [← hconj, conjSubgroup]
  intro hbot
  exact hSne₁ ((Subgroup.map_eq_bot_iff_of_injective (T ⊓ J₁)
    (f := (MulAut.conj t⁻¹).toMonoidHom) (MulAut.conj t⁻¹).injective).mp hbot)


private theorem wc819pq_eq_of_isSylowIn_ge {H P K : Subgroup Q} (hP : IsSylowIn 2 P H)
    (hKH : K ≤ H) (hK : IsPGroup 2 K) (hPK : P ≤ K) : K = P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.eq_of_le_of_card_ge hPK ?_).symm
  rw [hP.card_eq]
  obtain ⟨j, hj⟩ := hK.exists_card_eq
  rw [hj]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have hdvd : 2 ^ j ∣ Nat.card H := by
    rw [← hj]
    exact Subgroup.card_dvd_of_le hKH
  exact (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.card_pos (α := ↥H)).ne').mp hdvd

private theorem wc819pq_exists_mul_sup_of_commute {A C : Subgroup Q}
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) {x : Q} (hx : x ∈ A ⊔ C) :
    ∃ a ∈ A, ∃ c ∈ C, (∀ y ∈ A, c * y = y * c) ∧ x = a * c := by
  let F : Bool → Subgroup Q := fun b => if b then C else A
  have hF : (⨆ b, F b) = A ⊔ C := by
    rw [iSup_bool_eq]
    simp [F, sup_comm]
  have hx' : x ∈ ⨆ b, F b := by rw [hF]; exact hx
  refine Subgroup.iSup_induction F (C := fun x => ∃ a ∈ A, ∃ c ∈ C,
    (∀ y ∈ A, c * y = y * c) ∧ x = a * c) hx' ?_ ?_ ?_
  · intro b z hz
    cases b
    · simp only [F, Bool.false_eq_true, if_false] at hz
      exact ⟨z, hz, 1, C.one_mem, fun y _ => by simp, by simp⟩
    · simp only [F, if_true] at hz
      exact ⟨1, A.one_mem, z, hz, fun y hy => (hcomm y hy z hz).symm, by simp⟩
  · exact ⟨1, A.one_mem, 1, C.one_mem, fun y _ => by simp, by simp⟩
  · rintro u v ⟨a₁, ha₁, c₁, hc₁, hc₁comm, rfl⟩ ⟨a₂, ha₂, c₂, hc₂, hc₂comm, rfl⟩
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, c₁ * c₂, C.mul_mem hc₁ hc₂, ?_, ?_⟩
    · intro y hy
      rw [mul_assoc, hc₂comm y hy, ← mul_assoc, hc₁comm y hy, mul_assoc]
    · have hc₁a₂ : c₁ * a₂ = a₂ * c₁ := hc₁comm a₂ ha₂
      calc a₁ * c₁ * (a₂ * c₂) = a₁ * (c₁ * a₂) * c₂ := by group
        _ = a₁ * (a₂ * c₁) * c₂ := by rw [hc₁a₂]
        _ = a₁ * a₂ * (c₁ * c₂) := by group

private theorem wc819pq_sup_components_inf_le (hF0 : OddSchurMultiplierFact)
    (hF1 : InvolutionCentralizerFact) (hF2 : FourGroupInnerFact)
    (hF3 : BorelOvergroupFact) (h : Cfg813 T A B R L₀)
    (s : Finset {J : Subgroup Q // IsComponentOf J ⊤}) :
    s.sup (fun i => i.1) ⊓ B ≤ s.sup (fun i => B ⊓ i.1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sup_insert, Finset.sup_insert]
    intro x hx
    obtain ⟨hxsup, hxB⟩ := Subgroup.mem_inf.mp hx
    have hTB : T ≤ B := by
      have hBmem : B ∈ calNIn (⊤ : Subgroup Q) T := by
        rw [h.maxT]
        exact Set.mem_singleton B
      exact hBmem.1
    have hcomm : ∀ u ∈ a.1, ∀ v ∈ t.sup (fun i => i.1), u * v = v * u := by
      intro u hu v hv
      have hle : t.sup (fun i => i.1) ≤ Subgroup.centralizer (a.1 : Set Q) := by
        refine Finset.sup_le fun i hi => ?_
        have hne : i.1 ≠ a.1 := by
          intro heq
          exact ha (Subtype.ext heq ▸ hi)
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne i.1 a.1 i.2 a.2 hne)
      exact Subgroup.mem_centralizer_iff.mp (hle hv) u hu
    obtain ⟨a₀, ha₀A, c₀, hc₀C, hc₀comm, hxac⟩ :=
      wc819pq_exists_mul_sup_of_commute hcomm hxsup
    have hS : IsSylowIn 2 (T ⊓ a.1) a.1 := h.isSylowIn_inf_component a.2
    have hSne : T ⊓ a.1 ≠ ⊥ := h.inf_ne_bot hF0 hF1 hF2 a.2
    have hBeq : B ⊓ a.1 = a.1 ⊓ Subgroup.normalizer ((T ⊓ a.1 : Subgroup Q) : Set Q) :=
      h.inf_component_eq hF0 hF3 a.2 hSne
    have hc₀cent : c₀ ∈ Subgroup.centralizer ((T ⊓ a.1 : Subgroup Q) : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hc₀comm y (Subgroup.mem_inf.mp hy).2).symm
    have hconjS : conjSubgroup (T ⊓ a.1) c₀⁻¹ = T ⊓ a.1 := by
      rw [conjSubgroup_eq_iff_mem_normalizer]
      exact Subgroup.inv_mem _ ((Subgroup.centralizer_le_normalizer _) hc₀cent)
    have hconjEq : conjSubgroup (T ⊓ a.1) a₀⁻¹ = conjSubgroup (T ⊓ a.1) x⁻¹ := by
      rw [hxac, mul_inv_rev, ← conjSubgroup_conjSubgroup, hconjS]
    have hxSleB : conjSubgroup (T ⊓ a.1) x⁻¹ ≤ B := by
      intro y hy
      rw [conjSubgroup, Subgroup.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      simpa [MulAut.conj_apply] using
        B.mul_mem (B.mul_mem hxB (hTB (Subgroup.mem_inf.mp hz).1)) (B.inv_mem hxB)
    have hconj_le_A : conjSubgroup (T ⊓ a.1) a₀⁻¹ ≤ a.1 := by
      intro y hy
      rw [conjSubgroup, Subgroup.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      simpa [MulAut.conj_apply] using
        a.1.mul_mem (a.1.mul_mem ha₀A (Subgroup.mem_inf.mp hz).2) (a.1.inv_mem ha₀A)
    have hconj_le_H0 : conjSubgroup (T ⊓ a.1) a₀⁻¹ ≤
        a.1 ⊓ Subgroup.normalizer ((T ⊓ a.1 : Subgroup Q) : Set Q) := by
      rw [← hBeq]
      exact le_inf (by rw [hconjEq]; exact hxSleB) hconj_le_A
    have hS_H0 : IsSylowIn 2 (T ⊓ a.1)
        (a.1 ⊓ Subgroup.normalizer ((T ⊓ a.1 : Subgroup Q) : Set Q)) := by
      refine isSylowIn_of_le_of_le hS ?_ inf_le_left
      exact le_inf inf_le_right
        (Subgroup.le_normalizer : (T ⊓ a.1) ≤
          Subgroup.normalizer ((T ⊓ a.1 : Subgroup Q) : Set Q))
    set K : Subgroup Q := conjSubgroup (T ⊓ a.1) a₀⁻¹ with hK
    have hK_le_H0 : K ≤ a.1 ⊓
        Subgroup.normalizer ((T ⊓ a.1 : Subgroup Q) : Set Q) := by
      rw [hK]
      exact hconj_le_H0
    have hK2 : IsPGroup 2 ↥(K ⊔ (T ⊓ a.1)) := by
      have hK2' : IsPGroup 2 ↥K := by
        rw [hK, conjSubgroup, inv_inv]
        exact hS.isPGroup.map (MulAut.conj a₀).toMonoidHom
      exact IsPGroup.to_sup_of_normal_right' (p := 2) (H := K) (K := T ⊓ a.1)
        hK2' hS.isPGroup (hK_le_H0.trans inf_le_right)
    have hKleH0 : K ⊔ (T ⊓ a.1) ≤
        a.1 ⊓ Subgroup.normalizer ((T ⊓ a.1 : Subgroup Q) : Set Q) := by
      refine sup_le hK_le_H0 ?_
      exact le_inf inf_le_right
        (Subgroup.le_normalizer : (T ⊓ a.1) ≤
          Subgroup.normalizer ((T ⊓ a.1 : Subgroup Q) : Set Q))
    have hsup_eq : K ⊔ (T ⊓ a.1) = T ⊓ a.1 :=
      wc819pq_eq_of_isSylowIn_ge hS_H0 hKleH0 hK2 le_sup_right
    have hK_le : K ≤ T ⊓ a.1 := by
      rw [← hsup_eq]
      exact le_sup_left
    have hcard : Nat.card K = Nat.card ↥(T ⊓ a.1) := by
      rw [hK, conjSubgroup, inv_inv]
      exact Subgroup.card_map_of_injective (K := T ⊓ a.1)
        (f := (MulAut.conj a₀).toMonoidHom) (MulAut.conj a₀).injective
    have hK_eq : K = T ⊓ a.1 :=
      Subgroup.eq_of_le_of_card_ge hK_le (le_of_eq hcard.symm)
    have ha₀_norm : a₀ ∈ Subgroup.normalizer ((T ⊓ a.1 : Subgroup Q) : Set Q) := by
      have hconj_eq : conjSubgroup (T ⊓ a.1) a₀⁻¹ = T ⊓ a.1 := by
        rw [← hK]
        exact hK_eq
      have hinv : a₀⁻¹ ∈ Subgroup.normalizer ((T ⊓ a.1 : Subgroup Q) : Set Q) :=
        conjSubgroup_eq_iff_mem_normalizer.mp hconj_eq
      simpa using Subgroup.inv_mem _ hinv
    have ha₀B : a₀ ∈ B := by
      have hmem : a₀ ∈ a.1 ⊓ Subgroup.normalizer ((T ⊓ a.1 : Subgroup Q) : Set Q) :=
        Subgroup.mem_inf.mpr ⟨ha₀A, ha₀_norm⟩
      rw [← hBeq] at hmem
      exact (Subgroup.mem_inf.mp hmem).1
    have hc₀B : c₀ ∈ B := by
      have hc₀eq : c₀ = a₀⁻¹ * x := by rw [hxac]; group
      rw [hc₀eq]
      exact B.mul_mem (B.inv_mem ha₀B) hxB
    have hc₀_inf : c₀ ∈ t.sup (fun i => i.1) ⊓ B :=
      Subgroup.mem_inf.mpr ⟨hc₀C, hc₀B⟩
    rw [hxac]
    exact ((B ⊓ a.1) ⊔ t.sup (fun i => B ⊓ i.1)).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨ha₀B, ha₀A⟩))
      (Subgroup.mem_sup_right (ih hc₀_inf))

theorem Cfg813.inf_layer_inf_B_le_iSup (hF0 : OddSchurMultiplierFact)
    (hF1 : InvolutionCentralizerFact) (hF2 : FourGroupInnerFact) (hF3 : BorelOvergroupFact)
    (h : Cfg813 T A B R L₀) :
    genFittingLayer Q ⊓ B ≤ ⨆ (J : Subgroup Q) (_ : IsComponentOf J ⊤), B ⊓ J := by
  classical
  let idx := {J : Subgroup Q // IsComponentOf J ⊤}
  haveI : Fintype idx := Fintype.ofFinite idx
  have hmain := wc819pq_sup_components_inf_le hF0 hF1 hF2 hF3 h (Finset.univ : Finset idx)
  have hE : (Finset.univ : Finset idx).sup (fun J => J.1) = genFittingLayer Q := by
    have hrange : Set.range (fun J : idx => J.1) = {L : Subgroup Q | IsComponentOf L ⊤} := by
      ext L
      constructor
      · rintro ⟨J, rfl⟩
        exact J.2
      · intro hL
        exact ⟨⟨L, hL⟩, rfl⟩
    rw [Finset.sup_univ_eq_iSup, genFittingLayer.eq_sSup, ← sSup_range, hrange]
  have hP : (Finset.univ : Finset idx).sup (fun J => B ⊓ J.1) =
      ⨆ (J : Subgroup Q) (_ : IsComponentOf J ⊤), B ⊓ J := by
    rw [Finset.sup_univ_eq_iSup, iSup_subtype]
  rwa [hE, hP] at hmain

private def wc819pq_oddSet (P : Subgroup Q) : Set (Subgroup Q) :=
  {Q' | ⊥ ≤ Q' ∧ Q' ≤ P ∧ (Q'.subgroupOf P).Normal ∧ Odd (Q'.relIndex P)}

private theorem wc819pq_relIndex_sup_eq {T D : Subgroup Q}
    (hT : T ≤ Subgroup.normalizer (D : Set Q)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

private theorem wc819pq_not_two_dvd_relIndex_inf {T H D : Subgroup Q} [Finite T]
    (hTH : T ≤ H) (hDH : D ≤ H) (hT : ¬ 2 ∣ T.relIndex H)
    (hTD : T ≤ Subgroup.normalizer (D : Set Q)) :
    ¬ 2 ∣ (T ⊓ D).relIndex D := by
  have h1 : (T ⊓ D).relIndex T * T.relIndex (T ⊔ D) = (T ⊓ D).relIndex (T ⊔ D) :=
    Subgroup.relIndex_mul_relIndex (H := T ⊓ D) (K := T) (L := T ⊔ D) inf_le_left le_sup_left
  have h2 : (T ⊓ D).relIndex D * D.relIndex (T ⊔ D) = (T ⊓ D).relIndex (T ⊔ D) :=
    Subgroup.relIndex_mul_relIndex (H := T ⊓ D) (K := D) (L := T ⊔ D) inf_le_right le_sup_right
  have h3 : D.relIndex (T ⊔ D) = (T ⊓ D).relIndex T :=
    (wc819pq_relIndex_sup_eq hTD).trans (Subgroup.inf_relIndex_left T D).symm
  have h4 : 0 < (T ⊓ D).relIndex T :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := ((T ⊓ D).subgroupOf T)))
  have h5 : (T ⊓ D).relIndex D = T.relIndex (T ⊔ D) := by
    refine Nat.eq_of_mul_eq_mul_left h4 ?_
    rw [h3] at h2
    rw [mul_comm ((T ⊓ D).relIndex T) ((T ⊓ D).relIndex D), h2, ← h1]
  rw [h5]
  intro hd
  apply hT
  rw [← Subgroup.relIndex_mul_relIndex (H := T) (K := T ⊔ D) (L := H) le_sup_left
    (sup_le hTH hDH)]
  exact hd.mul_right _

private theorem wc819pq_odd_inf_relIndex {H K P : Subgroup Q} (hHP : H ≤ P) (hKP : K ≤ P)
    (hHnormal : (H.subgroupOf P).Normal) (hKnormal : (K.subgroupOf P).Normal)
    (hHodd : Odd (H.relIndex P)) (hKodd : Odd (K.relIndex P)) :
    Odd ((H ⊓ K).relIndex P) := by
  have hHnormK : H ≤ Subgroup.normalizer (K : Set Q) :=
    hHP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKP).mp hKnormal)
  have hnot : ¬ 2 ∣ H.relIndex K := by
    have h := wc819pq_not_two_dvd_relIndex_inf (T := H) (H := P) (D := K) hHP hKP
      hHodd.not_two_dvd_nat hHnormK
    rwa [Subgroup.inf_relIndex_right] at h
  have hHoddK : Odd (H.relIndex K) :=
    Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  rw [← Subgroup.relIndex_inf_mul_relIndex (H := H) (K := K) (L := P), inf_eq_left.mpr hKP]
  exact hHoddK.mul hKodd

private theorem wc819pq_finset_inf_facts (P : Subgroup Q)
    (s : Finset {Q' : Subgroup Q // Q' ∈ wc819pq_oddSet P}) :
    (s.inf (fun i => i.1) ⊓ P) ≤ P ∧
      (((s.inf (fun i => i.1) ⊓ P).subgroupOf P).Normal) ∧
      Odd (((s.inf (fun i => i.1) ⊓ P).relIndex P)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨inf_le_right, ?_, ?_⟩
      · simp [Finset.inf_empty]
      · simp [Finset.inf_empty]
  | insert a t ha ih =>
      obtain ⟨ihle, ihnormal, ihodd⟩ := ih
      rw [Finset.inf_insert]
      have hA : a.1 ≤ P := a.2.2.1
      have hAnormal : (a.1.subgroupOf P).Normal := a.2.2.2.1
      have hAodd : Odd (a.1.relIndex P) := a.2.2.2.2
      have hKle : t.inf (fun i => i.1) ⊓ P ≤ P := inf_le_right
      have hKnormal : ((t.inf (fun i => i.1) ⊓ P).subgroupOf P).Normal := ihnormal
      have hKodd : Odd ((t.inf (fun i => i.1) ⊓ P).relIndex P) := ihodd
      have hEq : (a.1 ⊓ t.inf (fun i => i.1)) ⊓ P =
          a.1 ⊓ (t.inf (fun i => i.1) ⊓ P) := inf_assoc _ _ _
      rw [hEq]
      refine ⟨(inf_le_right : a.1 ⊓ (t.inf (fun i => i.1) ⊓ P) ≤
        t.inf (fun i => i.1) ⊓ P).trans inf_le_right, ?_, ?_⟩
      · have hPleA : P ≤ Subgroup.normalizer (a.1 : Set Q) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hA).mp hAnormal
        have hPleK : P ≤ Subgroup.normalizer
            ((t.inf (fun i => i.1) ⊓ P : Subgroup Q) : Set Q) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mp hKnormal
        have hPleInf : P ≤ Subgroup.normalizer
            ((a.1 ⊓ (t.inf (fun i => i.1) ⊓ P) : Subgroup Q) : Set Q) :=
          (le_inf hPleA hPleK).trans Subgroup.inf_normalizer_le_normalizer_inf
        have hleP : a.1 ⊓ (t.inf (fun i => i.1) ⊓ P) ≤ P :=
          (inf_le_right : a.1 ⊓ (t.inf (fun i => i.1) ⊓ P) ≤
            t.inf (fun i => i.1) ⊓ P).trans inf_le_right
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer hleP).mpr hPleInf
      · exact wc819pq_odd_inf_relIndex hA hKle hAnormal hKnormal hAodd hKodd

private theorem wc819pq_oddResMod_relIndex (P : Subgroup Q) :
    Odd ((oddResMod (⊥ : Subgroup Q) P).relIndex P) := by
  classical
  let S := wc819pq_oddSet P
  let idx := {Q' : Subgroup Q // Q' ∈ S}
  haveI : Fintype idx := Fintype.ofFinite idx
  have hPmem : P ∈ S := by
    refine ⟨bot_le, le_rfl, ?_, ?_⟩
    · simpa [Subgroup.subgroupOf_self]
    · simp [Subgroup.relIndex_self]
  have hfact := wc819pq_finset_inf_facts P (Finset.univ : Finset idx)
  have hinf_le_P : (Finset.univ : Finset idx).inf (fun i => i.1) ≤ P := by
    let iP : idx := ⟨P, hPmem⟩
    simpa using (Finset.inf_le (Finset.mem_univ iP) :
      (Finset.univ : Finset idx).inf (fun i => i.1) ≤ (fun i : idx => i.1) iP)
  have hinf_eq : (Finset.univ : Finset idx).inf (fun i => i.1) ⊓ P =
      (Finset.univ : Finset idx).inf (fun i => i.1) := inf_eq_left.mpr hinf_le_P
  have hK_eq : oddResMod (⊥ : Subgroup Q) P =
      (Finset.univ : Finset idx).inf (fun i => i.1) := by
    rw [oddResMod]
    refine le_antisymm ?_ ?_
    · refine Finset.le_inf fun i _ => ?_
      exact (iInf_le (fun Q' => ⨅ (_ : Q' ∈ wc819pq_oddSet P), Q') i.1).trans
        (iInf_le (fun _ => i.1) i.2)
    · refine le_iInf fun Q' => le_iInf fun hQ' => ?_
      exact Finset.inf_le (Finset.mem_univ (⟨Q', hQ'⟩ : idx))
  rw [hK_eq, ← hinf_eq]
  exact hfact.2.2

private theorem wc819pq_caseB (hF0 : OddSchurMultiplierFact)
    (hF1 : InvolutionCentralizerFact) (hF2 : FourGroupInnerFact) (hF3 : BorelOvergroupFact)
    (h : Cfg813 T A B R L₀) {L K P : Subgroup Q} (hL : IsComponentOf L ⊤) (hK : K ≤ L)
    (hc : HasQuotShape K ((oTwoMod (⊥ : Subgroup Q) K : Subgroup Q) : Set Q)
      (fun X _ => IsL2 X 2))
    (hT : IsSylowIn 2 (T ⊓ K) K)
    (hPmax : IsMaxParabolicMod (⊥ : Subgroup Q) L P)
    (hKeq : K = oddResMod (⊥ : Subgroup Q) P) :
    B ⊓ L ≤ normalizer (K : Set Q) := by
  classical
  have hS : IsSylowIn 2 (T ⊓ L) L := h.isSylowIn_inf_component hL
  have hSne : T ⊓ L ≠ ⊥ := h.inf_ne_bot hF0 hF1 hF2 hL
  have hBeq : B ⊓ L = L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) :=
    h.inf_component_eq hF0 hF3 hL hSne
  rw [hBeq]
  obtain ⟨hbotP, hPL, hmax, S', hbotS, hS'L, hS'2pow, hS'odd, hNormS'⟩ := hPmax
  let Sset := {Q' : Subgroup Q | ⊥ ≤ Q' ∧ Q' ≤ P ∧ (Q'.subgroupOf P).Normal ∧
    Odd (Q'.relIndex P)}
  have hPmem : P ∈ Sset := by
    refine ⟨bot_le, le_rfl, ?_, ?_⟩
    · simpa [Subgroup.subgroupOf_self]
    · simp [Subgroup.relIndex_self]
  have hKleP : K ≤ P := by
    rw [hKeq]
    exact iInf_le_of_le P (iInf_le_of_le hPmem le_rfl)
  have hPnormK : P ≤ Subgroup.normalizer (K : Set Q) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      rw [hKeq] at hk ⊢
      simp only [oddResMod] at hk ⊢
      rw [Subgroup.mem_iInf] at hk ⊢
      intro Q'
      have hkQ' := hk Q'
      rw [Subgroup.mem_iInf] at hkQ' ⊢
      intro hQ'
      have hQ'leP : Q' ≤ P := hQ'.2.1
      have hQ'norm : (Q'.subgroupOf P).Normal := hQ'.2.2.1
      have hPleNorm : P ≤ Subgroup.normalizer (Q' : Set Q) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQ'leP).mp hQ'norm
      exact (Subgroup.mem_normalizer_iff.mp (hPleNorm hp) k).mp (hkQ' hQ')
    · intro hk
      rw [hKeq] at hk ⊢
      simp only [oddResMod] at hk ⊢
      rw [Subgroup.mem_iInf] at hk ⊢
      intro Q'
      have hkQ' := hk Q'
      rw [Subgroup.mem_iInf] at hkQ' ⊢
      intro hQ'
      have hQ'leP : Q' ≤ P := hQ'.2.1
      have hQ'norm : (Q'.subgroupOf P).Normal := hQ'.2.2.1
      have hPleNorm : P ≤ Subgroup.normalizer (Q' : Set Q) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQ'leP).mp hQ'norm
      have hkQ' : k ∈ Q' := by
        have h := (Subgroup.mem_normalizer_iff.mp (hPleNorm (P.inv_mem hp))
          (p * k * p⁻¹)).mp (hkQ' hQ')
        convert h using 1
        group
      exact hkQ'
  have hKnormalP : (K.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleP).mpr hPnormK
  have hKrelOdd : Odd (K.relIndex P) := hKeq ▸ wc819pq_oddResMod_relIndex P
  have hS'2 : IsPGroup 2 S' := by
    intro s
    obtain ⟨k, hk⟩ := hS'2pow s s.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hS'leP : S' ≤ P := by
    have h1 : S' ≤ L ⊓ Subgroup.normalizer (S' : Set Q) :=
      le_inf hS'L Subgroup.le_normalizer
    exact h1.trans hNormS'
  have hS'sylL : IsSylowIn 2 S' L := ⟨hS'L, hS'2, hS'odd⟩
  have hS'sylP : IsSylowIn 2 S' P :=
    isSylowIn_of_le_of_le hS'sylL hS'leP (le_of_lt hPL)
  have hS'oddOdd : Odd (S'.relIndex L) :=
    Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  have hPLodd : Odd (P.relIndex L) := by
    have hdvd : P.relIndex L ∣ S'.relIndex L :=
      Subgroup.relIndex_dvd_of_le_left (H := S') (K := P) (L := L) hS'leP
    exact hS'oddOdd.of_dvd_nat hdvd
  have hKrelLodd : Odd (K.relIndex L) := by
    rw [← Subgroup.relIndex_mul_relIndex (H := K) (K := P) (L := L) hKleP
      (le_of_lt hPL)]
    exact hKrelOdd.mul hPLodd
  have hTKsylL : IsSylowIn 2 (T ⊓ K) L := by
    refine ⟨inf_le_right.trans hK, hT.isPGroup, ?_⟩
    have hrel : (T ⊓ K).relIndex K * K.relIndex L = (T ⊓ K).relIndex L :=
      Subgroup.relIndex_mul_relIndex (H := T ⊓ K) (K := K) (L := L) hT.le hK
    rw [← hrel]
    intro h2
    rcases (Nat.prime_two.dvd_mul).mp h2 with h | h
    · exact hT.not_dvd_relIndex h
    · exact hKrelLodd.not_two_dvd_nat h
  have hcardTK : Nat.card ↥(T ⊓ K) = Nat.card ↥(T ⊓ L) := by
    rw [hTKsylL.card_eq, hS.card_eq]
  have hTK_eq_S : T ⊓ K = T ⊓ L :=
    Subgroup.eq_of_le_of_card_ge (inf_le_inf_left T hK) (le_of_eq hcardTK.symm)
  have hS_le_K : T ⊓ L ≤ K := by
    rw [← hTK_eq_S]
    exact inf_le_right
  have hSsylP : IsSylowIn 2 (T ⊓ L) P :=
    isSylowIn_of_le_of_le hS (hS_le_K.trans hKleP) (le_of_lt hPL)
  obtain ⟨p, hpP, hpconj⟩ := Ch1Sec3.exists_conj_of_isSylowIn hSsylP hS'sylP
  have hLNS_le_P : L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) ≤ P := by
    intro x hx
    obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
    have hpL : p ∈ L := le_of_lt hPL hpP
    have hxP : p * x * p⁻¹ ∈ P := by
      have hxL' : p * x * p⁻¹ ∈ L := L.mul_mem (L.mul_mem hpL hxL) (L.inv_mem hpL)
      have hxN' : p * x * p⁻¹ ∈ Subgroup.normalizer ((S' : Subgroup Q) : Set Q) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          apply (hpconj ((p * x * p⁻¹) * y * (p * x * p⁻¹)⁻¹)).mpr
          have hyS : p⁻¹ * y * p ∈ T ⊓ L := (hpconj y).mp hy
          have h1 : x * (p⁻¹ * y * p) * x⁻¹ ∈ T ⊓ L :=
            (Subgroup.mem_normalizer_iff.mp hxN (p⁻¹ * y * p)).mp hyS
          convert h1 using 1
          group
        · intro hy
          apply (hpconj y).mpr
          have hy' : p⁻¹ * ((p * x * p⁻¹) * y * (p * x * p⁻¹)⁻¹) * p ∈ T ⊓ L :=
            (hpconj ((p * x * p⁻¹) * y * (p * x * p⁻¹)⁻¹)).mp hy
          have h1 : x * (p⁻¹ * y * p) * x⁻¹ ∈ T ⊓ L := by
            convert hy' using 1
            group
          exact (Subgroup.mem_normalizer_iff.mp hxN (p⁻¹ * y * p)).mpr h1
      exact hNormS' (Subgroup.mem_inf.mpr ⟨hxL', hxN'⟩)
    have hx_eq : x = p⁻¹ * (p * x * p⁻¹) * p := by group
    rw [hx_eq]
    exact P.mul_mem (P.mul_mem (P.inv_mem hpP) hxP) hpP
  exact hLNS_le_P.trans hPnormK

theorem Cfg813.inf_layer_inf_B_le_normalizer (hF0 : OddSchurMultiplierFact)
    (hF1 : InvolutionCentralizerFact) (hF2 : FourGroupInnerFact) (hF3 : BorelOvergroupFact)
    (h : Cfg813 T A B R L₀) {L K : Subgroup Q} (hL : IsComponentOf L ⊤) (hK : K ≤ L)
    (hc : HasQuotShape K ((oTwoMod (⊥ : Subgroup Q) K : Subgroup Q) : Set Q)
      (fun X _ => IsL2 X 2))
    (hT : IsSylowIn 2 (T ⊓ K) K) (hAB : Case813AB (⊥ : Subgroup Q) L K) :
    genFittingLayer Q ⊓ B ≤ normalizer (K : Set Q) := by
  refine (h.inf_layer_inf_B_le_iSup hF0 hF1 hF2 hF3).trans ?_
  refine iSup_le fun J => iSup_le fun hJ => ?_
  by_cases hJL : J = L
  · rw [hJL] at hJ ⊢
    have hS : IsSylowIn 2 (T ⊓ L) L := h.isSylowIn_inf_component hL
    have hSne : T ⊓ L ≠ ⊥ := h.inf_ne_bot hF0 hF1 hF2 hL
    have hBeq : B ⊓ L = L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) :=
      h.inf_component_eq hF0 hF3 hL hSne
    rw [hBeq]
    rcases hAB with hL2 | ⟨hr, P, hPmax, hKeq⟩
    · obtain ⟨X, hXgrp, φ, hφsurj, hφker, hXL2⟩ := hL2
      have hφinj : Function.Injective φ := by
        intro a b hab
        have h1 : φ (a * b⁻¹) = 1 := by
          rw [map_mul, map_inv, hab, mul_inv_cancel]
        have h2 : (a * b⁻¹ : ↥L) = 1 := by
          apply Subtype.ext
          have := (hφker (a * b⁻¹)).mp h1
          simpa using this
        exact mul_inv_eq_one.mp h2
      have hLcard : Nat.card ↥L = 60 := by
        have hXcard : Nat.card X = 60 := wc819pq_card_isL2 hXL2
        have e : ↥L ≃* X := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
        rw [← hXcard]
        exact Nat.card_congr e.toEquiv
      obtain ⟨Y, hYgrp, ψ, hψsurj, hψker, hYL2⟩ := hc
      have hYcard : Nat.card Y = 60 := wc819pq_card_isL2 hYL2
      have hKY : Nat.card Y ≤ Nat.card ↥K := Nat.card_le_card_of_surjective ψ hψsurj
      have hKcard : Nat.card ↥K = 60 := by
        refine le_antisymm ?_ ?_
        · calc Nat.card ↥K ≤ Nat.card ↥L := Subgroup.card_le_of_le hK
            _ = 60 := hLcard
        · rw [← hYcard]
          exact hKY
      have hKL : K = L := Subgroup.eq_of_le_of_card_ge hK (by omega)
      rw [hKL]
      exact inf_le_left.trans Subgroup.le_normalizer
    · rw [← hBeq]
      exact wc819pq_caseB hF0 hF1 hF2 hF3 h hL hK hc hT hPmax hKeq
  · have hJcomm : J ≤ Subgroup.centralizer (L : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne J L hJ hL hJL)
    have hJK : J ≤ Subgroup.normalizer (K : Set Q) :=
      hJcomm.trans ((Subgroup.centralizer_le
        (show (K : Set Q) ⊆ (L : Set Q) from hK)).trans
          (Subgroup.centralizer_le_normalizer (K : Set Q)))
    exact inf_le_right.trans hJK

end CFSG.LocalAnalysis.WeakClosure81

end
