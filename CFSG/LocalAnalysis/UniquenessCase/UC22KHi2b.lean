module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open CFSG.Quasithin (IsMaxElemAbelian)
open P22x
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace P22k2

theorem card_le_two_of_lt {V₀ K : Subgroup G} (hcard : Nat.card V₀ = 4) (hK : K ≤ V₀) (hne : K ≠ V₀) :
    Nat.card K ≤ 2 := by
  have hd : Nat.card K ∣ 4 := hcard ▸ Subgroup.card_dvd_of_le hK
  have hle : Nat.card K ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  have hne4 : Nat.card K ≠ 4 := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge hK (by rw [hcard, h]))
  interval_cases h : Nat.card K <;> simp_all

theorem card_le_two_mul_inf {S A V₀ : Subgroup G} (hAS : A ≤ S)
    (hidx : (S ⊓ centralizer (V₀ : Set G)).relIndex S ≤ 2) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ centralizer (V₀ : Set G)) := by
  have h1 : (centralizer (V₀ : Set G)).relIndex A = (S ⊓ centralizer (V₀ : Set G)).relIndex A := by
    rw [← Subgroup.inf_relIndex_right (centralizer (V₀ : Set G)),
      ← Subgroup.inf_relIndex_right (S ⊓ centralizer (V₀ : Set G))]
    congr 1
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨hx, hxA⟩ => ⟨⟨hAS hxA, hx⟩, hxA⟩, fun ⟨⟨_, hx⟩, hxA⟩ => ⟨hx, hxA⟩⟩
  have h2 : (S ⊓ centralizer (V₀ : Set G)).relIndex A ≤ (S ⊓ centralizer (V₀ : Set G)).relIndex S :=
    Subgroup.relIndex_le_of_le_right hAS Subgroup.index_ne_zero_of_finite
  have h3 := Subgroup.relIndex_mul_card (H := centralizer (V₀ : Set G)) (K := A)
  rw [inf_comm] at h3
  calc Nat.card A = (centralizer (V₀ : Set G)).relIndex A * Nat.card ↥(A ⊓ centralizer (V₀ : Set G)) :=
        h3.symm
    _ ≤ 2 * Nat.card ↥(A ⊓ centralizer (V₀ : Set G)) :=
        Nat.mul_le_mul_right _ (h1 ▸ h2.trans hidx)

theorem lemma49_klein {T S V₀ : Subgroup G} (hAS : ∀ A : Subgroup G, IsMaxElemAbelian T A → A ≤ S)
    (hV₀T : V₀ ≤ T) (hel : IsElemAbelian 2 V₀) (hcard : Nat.card V₀ = 4)
    (hidx : (S ⊓ centralizer (V₀ : Set G)).relIndex S ≤ 2) :
    ∀ A : Subgroup G, IsMaxElemAbelian T A → IsMaxElemAbelian T ((A ⊓ centralizer (V₀ : Set G)) ⊔ V₀) := by
  intro A hA
  have hAS' := hAS A hA
  obtain ⟨hAT, hAel, hAmax⟩ := hA
  set A₀ : Subgroup G := A ⊓ centralizer (V₀ : Set G) with hA₀
  have hcomm : ∀ a ∈ A₀, ∀ v ∈ V₀, a * v = v * a := fun a ha v hv =>
    (Subgroup.mem_centralizer_iff.1 ha.2 v hv).symm
  have hBel : IsElemAbelian 2 (A₀ ⊔ V₀) := (hAel.mono inf_le_left).sup_of_commute hel hcomm
  have hBT : A₀ ⊔ V₀ ≤ T := sup_le (inf_le_left.trans hAT) hV₀T
  have hAB : Nat.card A ≤ Nat.card ↥(A₀ ⊔ V₀) := by
    by_cases hc : A ≤ centralizer (V₀ : Set G)
    · exact Subgroup.card_le_of_le (by rw [hA₀, inf_eq_left.2 hc]; exact le_sup_left)
    · obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₀ V₀ hcomm
      have hinf : Nat.card ↥(A₀ ⊓ V₀) ≤ 2 := by
        refine (Subgroup.card_le_of_le (inf_le_inf_right V₀ inf_le_left)).trans ?_
        refine card_le_two_of_lt hcard inf_le_right fun h => hc ?_
        have hVA : V₀ ≤ A := h ▸ inf_le_left
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact hAel.comm (hVA hv) ha
      have hA2 := card_le_two_mul_inf hAS' hidx
      rw [← hA₀] at hA2
      have hpos : 0 < Nat.card ↥(A₀ ⊓ V₀) := Nat.card_pos
      rw [hcard] at hprod
      have h1 : Nat.card ↥(A₀ ⊔ V₀) * Nat.card ↥(A₀ ⊓ V₀) ≤ Nat.card ↥(A₀ ⊔ V₀) * 2 :=
        Nat.mul_le_mul_left _ hinf
      nlinarith
  exact ⟨hBT, hBel, fun D hDT hDel => (hAmax D hDT hDel).trans hAB⟩

theorem inf_le_jOf_of_klein {T S R V₀ : Subgroup G} (hST : S ≤ T)
    (hAS : ∀ A : Subgroup G, IsMaxElemAbelian T A → A ≤ S) (hRS : R ≤ S) (hV₀R : V₀ ≤ R)
    (hel : IsElemAbelian 2 V₀) (hcard : Nat.card V₀ = 4) (hRV₀ : R ≤ centralizer (V₀ : Set G))
    (hSC : S ⊓ centralizer (V₀ : Set G) ≤ R) (hidx : (S ⊓ centralizer (V₀ : Set G)).relIndex S ≤ 2)
    {A : Subgroup G} (hA : IsMaxElemAbelian T A) : A ⊓ R ≤ jOf R := by
  have hRT : R ≤ T := hRS.trans hST
  have hB := lemma49_klein hAS (hV₀R.trans hRT) hel hcard hidx A hA
  have hAS' := hAS A hA
  have hBR : (A ⊓ centralizer (V₀ : Set G)) ⊔ V₀ ≤ R :=
    sup_le (fun x hx => hSC ⟨hAS' hx.1, hx.2⟩) hV₀R
  have hBmax : IsMaxElemAbelian R ((A ⊓ centralizer (V₀ : Set G)) ⊔ V₀) :=
    ⟨hBR, hB.2.1, fun D hDR hD => hB.2.2 D (hDR.trans hRT) hD⟩
  have hBJ := le_jOf_of_isMax hBmax
  exact fun x hx => hBJ (Subgroup.mem_sup_left ⟨hx.1, hRV₀ hx.2⟩)

theorem lemma25_klein {T S R V₀ : Subgroup G} (hST : S ≤ T)
    (hAS : ∀ A : Subgroup G, IsMaxElemAbelian T A → A ≤ S) (hRS : R ≤ S) (hV₀R : V₀ ≤ R)
    (hel : IsElemAbelian 2 V₀) (hcard : Nat.card V₀ = 4) (hRV₀ : R ≤ centralizer (V₀ : Set G))
    (hSC : S ⊓ centralizer (V₀ : Set G) ≤ R) (hidx : (S ⊓ centralizer (V₀ : Set G)).relIndex S ≤ 2)
    (hÊ : ∀ a ∈ jOf T, ∀ z ∈ ⁅V₀, jOf T⁆, a * z = z * a) :
    ⁅omegaZJ22 R, jOf T⁆ = ⁅V₀, jOf T⁆ := by
  set N : Subgroup G := omegaZJ22 R with hNdef
  set X : Subgroup G := ⁅V₀, jOf T⁆ with hXdef
  have hRT : R ≤ T := hRS.trans hST
  have hNR : N ≤ R := (uc22p22e_omegaZJ_le_jOf R).trans (uc22p22e_jOf_le_self R)
  have hNT : N ≤ T := hNR.trans hRT
  have hNel : IsElemAbelian 2 N := P22sp.isElemAbelian_omegaZJ22 R
  have hV₀N : V₀ ≤ N := fun v hv =>
    uc22p22e_mem_omegaZJ'.2 ⟨hV₀R hv, fun j hj =>
      (Subgroup.mem_centralizer_iff.1 (hRV₀ (uc22p22e_jOf_le_self R hj)) v hv).symm, hel.2 v hv⟩
  have hRcomm : ∀ x ∈ jOf R, ∀ e ∈ N, x * e = e * x := fun x hx e he =>
    (uc22p22e_mem_omegaZJ.1 he).2.1 x hx
  have hRidx : R.relIndex S ≤ 2 := by
    have : S ⊓ centralizer (V₀ : Set G) = R := le_antisymm hSC (le_inf hRS hRV₀)
    rw [← this]
    exact hidx
  have hgen : ∀ A : Subgroup G, IsMaxElemAbelian T A → ∀ a ∈ A, ∀ e ∈ N, ⁅e, a⁆ ∈ X := by
    intro A hA a ha e he
    have hAJ : A ≤ jOf T := le_jOf_of_isMax hA
    have haS : a ∈ S := hAS A hA ha
    have hAR : ∀ x ∈ A ⊓ R, x ∈ jOf R := fun x hx =>
      inf_le_jOf_of_klein hST hAS hRS hV₀R hel hcard hRV₀ hSC hidx hA hx
    by_cases haR : a ∈ R
    · have h1 : e * a = a * e := (hRcomm a (hAR a ⟨ha, haR⟩) e he).symm
      rw [commutatorElement_eq_one_iff_mul_comm.2 h1]
      exact X.one_mem
    · have hanc : a ∉ centralizer (V₀ : Set G) := fun h => haR (hSC ⟨haS, h⟩)
      obtain ⟨v, hv, hva⟩ : ∃ v ∈ V₀, v * a ≠ a * v := by
        by_contra hcon
        push Not at hcon
        exact hanc (Subgroup.mem_centralizer_iff.2 hcon)
      have hvN : v ∈ N := hV₀N hv
      have h2 : (centralizer (N : Set G)).relIndex A ≤ 2 := by
        have hle : A ⊓ R ≤ centralizer (N : Set G) ⊓ A := fun x hx =>
          ⟨Subgroup.mem_centralizer_iff.2 fun e he => (hRcomm x (hAR x hx) e he).symm, hx.1⟩
        calc (centralizer (N : Set G)).relIndex A = (centralizer (N : Set G) ⊓ A).relIndex A :=
              (Subgroup.inf_relIndex_right (centralizer (N : Set G)) A).symm
          _ ≤ (A ⊓ R).relIndex A := Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
          _ = R.relIndex A := Subgroup.inf_relIndex_left _ _
          _ ≤ R.relIndex S := Subgroup.relIndex_le_of_le_right (hAS A hA) Subgroup.index_ne_zero_of_finite
          _ ≤ 2 := hRidx
      have h1 := uc22p22xf_relIndex_le hNT hNel hA
      have h3 : (centralizer ({a} : Set G)).relIndex N ≤ (centralizer (A : Set G)).relIndex N :=
        Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le (Set.singleton_subset_iff.2 ha))
          Subgroup.index_ne_zero_of_finite
      have hle2 : (centralizer ({a} : Set G)).relIndex N ≤ 2 := h3.trans (h1.trans h2)
      have hne1 : (centralizer ({a} : Set G)).relIndex N ≠ 1 := by
        intro h
        have hNa : N ≤ centralizer ({a} : Set G) := Subgroup.relIndex_eq_one.1 h
        exact hva (Subgroup.mem_centralizer_iff.1 (hNa hvN) a (Set.mem_singleton a)).symm
      have hpos : 0 < (centralizer ({a} : Set G)).relIndex N :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hidx2 : ((centralizer ({a} : Set G)).subgroupOf N).index = 2 := by
        change (centralizer ({a} : Set G)).relIndex N = 2
        omega
      by_cases hec : e ∈ centralizer ({a} : Set G)
      · have h1' : e * a = a * e := (Subgroup.mem_centralizer_iff.1 hec a (Set.mem_singleton a)).symm
        rw [commutatorElement_eq_one_iff_mul_comm.2 h1']
        exact X.one_mem
      · have hv' : (⟨v⁻¹, N.inv_mem hvN⟩ : ↥N) ∉ (centralizer ({a} : Set G)).subgroupOf N := by
          intro h
          have h' : v⁻¹ ∈ centralizer ({a} : Set G) := h
          have := Subgroup.mem_centralizer_iff.1 ((centralizer ({a} : Set G)).inv_mem h') a (Set.mem_singleton a)
          rw [inv_inv] at this
          exact hva this.symm
        have he' : (⟨e, he⟩ : ↥N) ∉ (centralizer ({a} : Set G)).subgroupOf N := hec
        have hmem := (Subgroup.mul_mem_iff_of_index_two hidx2 (a := ⟨v⁻¹, N.inv_mem hvN⟩)
          (b := ⟨e, he⟩)).2 (iff_of_false hv' he')
        have hc : a * (v⁻¹ * e) = (v⁻¹ * e) * a :=
          Subgroup.mem_centralizer_iff.1 hmem a (Set.mem_singleton a)
        have hca : (v⁻¹ * e) * a * (v⁻¹ * e)⁻¹ = a := by
          rw [← hc]
          group
        have key : ⁅e, a⁆ = ⁅v, a⁆ := by
          calc ⁅e, a⁆ = ⁅v * (v⁻¹ * e), a⁆ := by rw [mul_inv_cancel_left]
            _ = v * ((v⁻¹ * e) * a * (v⁻¹ * e)⁻¹) * v⁻¹ * a⁻¹ := by
                simp only [commutatorElement_def]
                group
            _ = ⁅v, a⁆ := by
                rw [hca]
                simp only [commutatorElement_def]
        rw [key]
        exact Subgroup.commutator_mem_commutator hv (hAJ ha)
  let Y : Subgroup G :=
    { carrier := {a | a ∈ jOf T ∧ ∀ e ∈ N, ⁅e, a⁆ ∈ X}
      mul_mem' := by
        rintro a b ⟨haJ, haX⟩ ⟨hbJ, hbX⟩
        refine ⟨mul_mem haJ hbJ, fun e he => ?_⟩
        have eq : ⁅e, a * b⁆ = ⁅e, a⁆ * (a * ⁅e, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [eq]
        have hz : a * ⁅e, b⁆ * a⁻¹ = ⁅e, b⁆ := by
          rw [hÊ a haJ _ (hbX e he)]
          group
        rw [hz]
        exact X.mul_mem (haX e he) (hbX e he)
      one_mem' := ⟨one_mem _, fun e _ => by rw [commutatorElement_one_right]; exact X.one_mem⟩
      inv_mem' := by
        rintro a ⟨haJ, haX⟩
        refine ⟨inv_mem haJ, fun e he => ?_⟩
        have eq : ⁅e, a⁻¹⁆ = a⁻¹ * ⁅e, a⁆⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        have hz : a⁻¹ * ⁅e, a⁆⁻¹ * a = ⁅e, a⁆⁻¹ := by
          have h := hÊ a haJ _ (X.inv_mem (haX e he))
          calc a⁻¹ * ⁅e, a⁆⁻¹ * a = a⁻¹ * (⁅e, a⁆⁻¹ * a) := by group
            _ = a⁻¹ * (a * ⁅e, a⁆⁻¹) := by rw [h]
            _ = ⁅e, a⁆⁻¹ := by group
        rw [eq, hz]
        exact X.inv_mem (haX e he) }
  have hJY : jOf T ≤ Y := jOf_le_of_forall_isMax fun A hA a ha =>
    ⟨le_jOf_of_isMax hA ha, fun e he => hgen A hA a ha e he⟩
  refine le_antisymm ?_ (Subgroup.commutator_mono hV₀N le_rfl)
  rw [Subgroup.commutator_le]
  intro e he a ha
  exact (hJY ha).2 e he

end P22k2

end CFSG.LocalAnalysis.UniquenessCase.UC22
