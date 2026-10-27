module

public import CFSG.Quasithin.Vol2.Ch3xE2
public import CFSG.Quasithin.Background.E2PairMore
public import CFSG.Quasithin.Background.E2Hyp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace Ch3n

section Finite

variable {G : Type} [Group G]

theorem cjSub_eq_conjSub (g : G) (A : Subgroup G) : cjSub g A = B6.conjSub g A :=
  Subgroup.ext fun x => by rw [mem_cjSub, B6.mem_conjSub]

theorem relIndex_conjSub (g : G) (H K : Subgroup G) :
    (B6.conjSub g H).relIndex (B6.conjSub g K) = H.relIndex K := by
  have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) H K
    (MulAut.conj g).injective
  exact h

@[expose] def pairI (V : Subgroup G) (g : G) : Subgroup G := V ⊔ B6.conjSub g V

variable [Finite G]

theorem exists_cubic_of_pair {X T M V : Subgroup G} {g : G} (h : E2.Pair X T M V g)
    (hchar : CharTwo X) (hXV : X ≠ V) :
    B6.conjSub g (kerIn M X ⊓ V) ≤ T ∧ B6.conjSub g (kerIn M X ⊓ V) ≤ B6.conjSub g V ∧
      IsElemAbelian 2 (B6.conjSub g (kerIn M X ⊓ V)) ∧
      ⁅⁅⁅V, B6.conjSub g (kerIn M X ⊓ V)⁆, B6.conjSub g (kerIn M X ⊓ V)⁆,
        B6.conjSub g (kerIn M X ⊓ V)⁆ = ⊥ ∧
      ¬ B6.conjSub g (kerIn M X ⊓ V) ≤ Subgroup.centralizer (V : Set G) ∧
      B6.conjSub g (kerIn M X ⊓ V) ⊓ Subgroup.centralizer (V : Set G) = V ⊓ B6.conjSub g V := by
  set B := kerIn M X ⊓ V with hB
  set A := B6.conjSub g B with hA
  set Z := V ⊓ B6.conjSub g V with hZ
  have hAX : A ≤ X := h.A_le_pCoreOf.trans (pCoreOf_le 2 X)
  have hAle : A ≤ B6.conjSub g V := (B6.conjSub g).monotone inf_le_right
  refine ⟨h.A_le_pCoreOf.trans h.pCoreOf_le_T, hAle, ?_, ?_, h.not_le_centralizer hchar hXV, ?_⟩
  · refine isElemAbelian_mono hAle ?_
    rw [← cjSub_eq_conjSub]
    exact isElemAbelian_cjSub h.elem
  · have c1 : ⁅V, A⁆ ≤ B := by
      rw [Subgroup.commutator_le]
      intro v hv a ha
      rw [commutatorElement_def]
      exact h.commutator_mem_B hv (h.A_le_pCoreOf ha)
    have c2 : ⁅B, A⁆ ≤ Z := by
      rw [Subgroup.commutator_le]
      intro b hb a ha
      rw [commutatorElement_def]
      exact h.commutator_B_A hb ha
    have c3 : ⁅Z, A⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro z hz a ha
      rw [commutatorElement_def, Subgroup.mem_bot, h.mem_center hz (hAX ha)]
      group
    exact le_bot_iff.1 ((Subgroup.commutator_mono (Subgroup.commutator_mono c1 le_rfl) le_rfl).trans
      ((Subgroup.commutator_mono c2 le_rfl).trans c3.le))
  · apply le_antisymm
    · intro a ha
      have haB : a ∈ B := by
        refine h.mem_B_of_commutator_mem_Z (Subgroup.mem_sup_right ha.1) fun v hv => ?_
        rw [Subgroup.mem_centralizer_iff.mp ha.2 v hv]
        simp only [mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
      have : a ∈ B ⊓ A := ⟨haB, ha.1⟩
      rwa [hB, hA, h.B_inf_A] at this
    · intro z hz
      exact ⟨h.inf_conj_le_conjSub hz, Subgroup.mem_centralizer_iff.mpr fun v hv => h.comm hv hz.1⟩

theorem count_of_pair {X T M V : Subgroup G} {g : G} (h : E2.Pair X T M V g)
    (hrank : (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ B6.conjSub g V).relIndex (kerIn M X ⊓ V)) :
    (V ⊓ Subgroup.centralizer ((B6.conjSub g (kerIn M X ⊓ V) : Subgroup G) : Set G)).relIndex V ≤
      ((B6.conjSub g (kerIn M X ⊓ V) ⊓ Subgroup.centralizer (V : Set G)).relIndex
        (B6.conjSub g (kerIn M X ⊓ V))) ^ 2 := by
  set B := kerIn M X ⊓ V with hB
  set A := B6.conjSub g B with hA
  set Z := V ⊓ B6.conjSub g V with hZ
  have hAX : A ≤ X := h.A_le_pCoreOf.trans (pCoreOf_le 2 X)
  have hACV : A ⊓ Subgroup.centralizer (V : Set G) = Z := by
    apply le_antisymm
    · intro a ha
      have haB : a ∈ B := by
        refine h.mem_B_of_commutator_mem_Z (Subgroup.mem_sup_right ha.1) fun v hv => ?_
        rw [Subgroup.mem_centralizer_iff.mp ha.2 v hv]
        simp only [mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
      have : a ∈ B ⊓ A := ⟨haB, ha.1⟩
      rwa [hB, hA, h.B_inf_A] at this
    · intro z hz
      exact ⟨h.inf_conj_le_conjSub hz, Subgroup.mem_centralizer_iff.mpr fun v hv => h.comm hv hz.1⟩
  have hZB : Z ≤ B := h.inf_conj_le_kerIn_inf
  have hBV : B ≤ V := inf_le_right
  have hZg : B6.conjSub g Z = Z := B6.conjSub_eq_self (h.le_normalizer_Z h.mem)
  have hZA : Z.relIndex A = Z.relIndex B := by
    have := relIndex_conjSub g Z B
    rwa [hZg] at this
  have hZC : Z ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
    intro z hz
    refine ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact (h.mem_center hz (hAX ha)).symm
  have hdvd : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ∣ Z.relIndex V :=
    Subgroup.relIndex_dvd_of_le_left V hZC
  have hpos : 0 < Z.relIndex V := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hmul : Z.relIndex B * B.relIndex V = Z.relIndex V :=
    Subgroup.relIndex_mul_relIndex Z B V hZB hBV
  rw [hACV, hZA, sq]
  calc (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ Z.relIndex V := Nat.le_of_dvd hpos hdvd
    _ = Z.relIndex B * B.relIndex V := hmul.symm
    _ ≤ Z.relIndex B * Z.relIndex B := Nat.mul_le_mul_left _ hrank

@[expose] def E213Member : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G), E2.Hyp28 H T M V → CharTwo H →
    ¬ Group.IsSolvable H →
    ∃ g ∈ H, E2.Pair (pairI V g) (T ⊓ pairI V g) (M ⊓ pairI V g) V g ∧ CharTwo (pairI V g) ∧
      pairI V g ≠ V ∧
      (kerIn (M ⊓ pairI V g) (pairI V g) ⊓ V).relIndex V ≤
        (V ⊓ B6.conjSub g V).relIndex (kerIn (M ⊓ pairI V g) (pairI V g) ⊓ V)

@[expose] def E215Member : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G), E2.Hyp28 H T M V → CharTwo H →
    IsTISetIn V M → ¬ Group.IsSolvable H →
    ∃ g ∈ H, E2.Pair (pairI V g) (T ⊓ pairI V g) (M ⊓ pairI V g) V g ∧ CharTwo (pairI V g) ∧
      pairI V g ≠ V ∧
      (V ⊓ Subgroup.centralizer ((B6.conjSub g
          (kerIn (M ⊓ pairI V g) (pairI V g) ⊓ V) : Subgroup G) : Set G)).relIndex V <
        ((B6.conjSub g (kerIn (M ⊓ pairI V g) (pairI V g) ⊓ V) ⊓
            Subgroup.centralizer (V : Set G)).relIndex
          (B6.conjSub g (kerIn (M ⊓ pairI V g) (pairI V g) ⊓ V))) ^ 2

theorem hyp28_of_hypE28 {H T M V : Subgroup G} (h : HypE28 H T M V) : E2.Hyp28 H T M V :=
  ⟨h.minParabolic, ⟨h.sqtk.2, h.sqtk.1⟩, h.le_T, h.normal_T, h.elemAbelian, h.le_pCore, h.not_le_ker⟩

theorem e213ThreeNonsolvable_of_member (hM : E213Member) : E213ThreeNonsolvable := by
  intro G _ _ H T M V h hchar hns
  obtain ⟨g, hg, hP, hcI, hIV, hrank⟩ := hM G H T M V (hyp28_of_hypE28 h) hchar hns
  obtain ⟨hAT, hAV, hAel, hcub, hAC, -⟩ := exists_cubic_of_pair hP hcI hIV
  have hcount := count_of_pair hP hrank
  have hAT' : B6.conjSub g (kerIn (M ⊓ pairI V g) (pairI V g) ⊓ V) ≤ T := hAT.trans inf_le_left
  exact E2.qhatOf_le_two_of_cubic (hAT'.trans h.minParabolic.isSylow.1) (hAT'.trans h.normal_T) hAel
    hcub hAC hcount

theorem e215Nonsolvable_of_member (hM : E215Member) : E215Nonsolvable := by
  intro G _ _ H T M V h hchar hTI hns
  obtain ⟨g, hg, hP, hcI, hIV, hlt⟩ := hM G H T M V (hyp28_of_hypE28 h) hchar hTI hns
  obtain ⟨hAT, hAV, hAel, hcub, hAC, -⟩ := exists_cubic_of_pair hP hcI hIV
  have hAT' : B6.conjSub g (kerIn (M ⊓ pairI V g) (pairI V g) ⊓ V) ≤ T := hAT.trans inf_le_left
  exact E2.qhatOf_lt_two_of_cubic (hAT'.trans h.minParabolic.isSylow.1) (hAT'.trans h.normal_T) hAel
    hcub hAC hlt

end Finite

end Ch3n

end CFSG.Quasithin
