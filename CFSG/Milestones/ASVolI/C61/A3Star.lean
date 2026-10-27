module

public import CFSG.Milestones.ASVolI.C61.A3S4
public import CFSG.Milestones.ASVolI.C61.PBasic245Lin2Final

public section

namespace CFSG.QuasithinUnique.burnsideC56_P

open CFSG.Open CFSG.Quasithin Subgroup
open scoped commutatorElement

namespace C56

open CFSG.QuasithinUnique.C56

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem burnsideC56_a3_rank1 (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L)
    (h3 : IsAltType L 3) {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T)
    (h2 : S.relIndex M₀ = 2) :
    ∃ W : Subgroup G,
      C5.Rank1 (baum S) (baum S ⊓ centralizer (blockU L : Set G)) (blockU L) W 2 ∧
      (∀ x ∈ M₀, x ∉ S →
        SingleRank1Concl S H L (baum S ⊓ centralizer (blockU L : Set G)) 2 x) := by
  obtain ⟨q, W, -, hidxQ, hidxW, hZ, hcent, hcomm, hmain, -⟩ :=
    single_rank1 naturalModuleStructure hcs hj (Or.inr h3) hSM hMT h2
  have hq : q = 2 := by
    have h4 := relIndex_blockZ_isAltType3 (G := G) (L := L) h3
    have : q ^ 2 = 2 ^ 2 := hZ.symm.trans (h4.trans (by norm_num))
    exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) this
  subst hq
  have hLsh := isShort hcs
  have hBS : baum S ≤ S := inf_le_left
  have hBU : baum S ≤ normalizer (blockU L : Set G) := hBS.trans (S_le_normalizer_blockU hj)
  obtain ⟨x₀, hx₀, hx₀S⟩ := burnsideC56_exists_mem_diff hSM h2
  obtain ⟨-, -, -, -, o5, -, -, -, -, -, -, -⟩ := hmain x₀ hx₀ hx₀S
  have hWU : W ≤ blockU L := by
    rw [← hcomm, Subgroup.commutator_le]
    intro u hu b hb
    have h1 : b * u⁻¹ * b⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (hBU hb) _).mp (inv_mem hu)
    have := mul_mem hu h1
    rw [commutatorElement_def]
    simpa [mul_assoc] using this
  refine ⟨W, ?_, hmain⟩
  exact
    { U_le_Q := by rw [← o5]; exact blockU_le_pCoreOf hcs hj
      Q_le_B := inf_le_left
      B_le_normQ := fun _ hb => C5.mem_normalizer_inf (Subgroup.le_normalizer hb)
        (C5.mem_normalizer_centralizer (hBU hb))
      B_le_normU := hBU
      Q_eq := rfl
      W_le_U := hWU
      idx_Q := hidxQ
      idx_W := hidxW
      q_ne_zero := by omega
      cent_y := hcent
      comm_UB := hcomm
      U_comm := (C1.elemAb2_blockU hLsh).1 }

theorem burnsideC56_a3_baum_eq (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L)
    (h3 : IsAltType L 3) : baum S = S := by
  obtain ⟨c, hl⟩ := burnsideC56_a3Local hcs h3 hj
  obtain ⟨M₀, hSM, hMT, h2⟩ := exists_index_two hcs
  obtain ⟨x, hx, hxS⟩ := burnsideC56_exists_mem_diff hSM h2
  have hd := burnsideC56_a3Data hcs hj hl hSM hMT h2 hx hxS
  obtain ⟨W, hR1, hmain⟩ := burnsideC56_a3_rank1 hcs hj h3 hSM hMT h2
  obtain ⟨-, -, -, -, -, -, -, -, o9, -, o11, o12⟩ := hmain x hx hxS
  have hQB : baum S ⊓ centralizer (blockU L : Set G) ≤ baum S := inf_le_left
  have hDQ : H ⊓ centralizer (L : Set G) ≤ baum S ⊓ centralizer (blockU L : Set G) := by
    intro d hd'
    have : d ∈ S ⊓ centralizer (L : Set G) := ⟨hl.D_le_S hd', hd'.2⟩
    rw [o12] at this
    exact this.1
  refine le_antisymm inf_le_left ?_
  calc S = (blockU L ⊔ conjSubgroup (blockU L) x) ⊔ (H ⊓ centralizer (L : Set G)) :=
        hd.S_eq_R_sup_D
    _ ≤ baum S :=
      sup_le (sup_le (hR1.U_le_Q.trans hQB)
        ((le_sup_right.trans o9.symm.le).trans (le_sup_right.trans o11.symm.le)))
        (hDQ.trans hQB)

theorem burnsideC56_a3_star (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L)
    (h3 : IsAltType L 3) (hD : S ⊓ centralizer (L : Set G) ≠ ⊥) {M₀ : Subgroup G}
    (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) {A : Subgroup G} (hAM : A ≤ M₀)
    (hA : IsElemAbelian 2 A) (hQA : Nat.card (pCoreOf 2 H) ≤ Nat.card A) : A ≤ S := by
  by_contra hAS
  obtain ⟨x, hxA, hxS⟩ := IsConcreteLE.not_le_iff_exists.mp hAS
  have hxM : x ∈ M₀ := hAM hxA
  have hA' := C5.isElemAbelian_two_iff.mp hA
  have hsq : ∀ e ∈ A, e * e = 1 := fun e he => by
    have := hA'.2 e he
    rwa [pow_two] at this
  have hxx : x * x = 1 := hsq x hxA
  obtain ⟨W, hR1, hmain⟩ := burnsideC56_a3_rank1 hcs hj h3 hSM hMT h2
  obtain ⟨o1, -, -, o4, o5, o6, -, -, o9, -, -, o12⟩ := hmain x hxM hxS
  have hBS := burnsideC56_a3_baum_eq hcs hj h3
  have hxB : x ∈ normalizer (baum S : Set G) :=
    normalizer_le_normalizer_baum S (normalizer_of_relIndex_two hSM h2 hxM)
  have hx1 : ¬ conjSubgroup (blockU L) x ≤ baum S ⊓ centralizer (blockU L : Set G) := by
    rw [← o5]
    exact not_conj_le_of_mem_diff hcs hSM hMT h2 hxM hxS
  have hAN : A ⊓ S ≤ (baum S ⊓ centralizer (blockU L : Set G)) ⊓
      conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) x := by
    intro t ht
    have htB : t ∈ baum S := by rw [hBS]; exact ht.2
    exact invol_mem_inf_conj hR1 hxB hxx hx1 o6 htB (hsq t ht.1) (hA'.1 x hxA t ht.1)
  have hQcard : Nat.card ↥(baum S ⊓ centralizer (blockU L : Set G)) =
      Nat.card ↥((baum S ⊓ centralizer (blockU L : Set G)) ⊓
        conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) x) * 2 := by
    have := C5.card_eq_card_mul_relIndex (inf_le_left : (baum S ⊓ centralizer (blockU L : Set G)) ⊓
      conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) x ≤
        baum S ⊓ centralizer (blockU L : Set G))
    rwa [o1] at this
  have hQA' : Nat.card ↥(baum S ⊓ centralizer (blockU L : Set G)) ≤ Nat.card A := by
    rwa [o5] at hQA
  have hAE : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ S) := by
    have h1 := C5.card_eq_card_mul_relIndex (inf_le_left : A ⊓ S ≤ A)
    have h2' : (A ⊓ S).relIndex A ≤ 2 := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
      calc S.relIndex A ≤ S.relIndex M₀ :=
            Subgroup.relIndex_le_of_le_right hAM (by rw [h2]; norm_num)
        _ = 2 := h2
    rw [h1]
    calc Nat.card ↥(A ⊓ S) * (A ⊓ S).relIndex A ≤ Nat.card ↥(A ⊓ S) * 2 :=
          Nat.mul_le_mul_left _ h2'
      _ = 2 * Nat.card ↥(A ⊓ S) := mul_comm _ _
  have hASN := Subgroup.card_le_of_le hAN
  have heq : A ⊓ S = (baum S ⊓ centralizer (blockU L : Set G)) ⊓
      conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) x :=
    Subgroup.eq_of_le_of_card_ge hAN (by omega)
  have hDN : (baum S ⊓ centralizer (blockU L : Set G)) ⊓ centralizer (L : Set G) ≤
      (baum S ⊓ centralizer (blockU L : Set G)) ⊓
        conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) x :=
    le_inf inf_le_left (by rw [o9]; exact le_sup_left)
  have hDA : (baum S ⊓ centralizer (blockU L : Set G)) ⊓ centralizer (L : Set G) ≤ A := by
    intro d hd'
    have : d ∈ A ⊓ S := by rw [heq]; exact hDN hd'
    exact this.1
  have hxD : x ∈ normalizer (((baum S ⊓ centralizer (blockU L : Set G)) ⊓
      centralizer (L : Set G) : Subgroup G) : Set G) :=
    A3Dich.mem_normalizer_of_forall_comm fun d hd' => hA'.1 x hxA d (hDA hd')
  rw [C5.conjSubgroup_eq_self hxD, inf_idem] at o4
  exact hD (o12.trans o4)

theorem burnsideC56_a3_isMaxElemAbelian_iff (hcs : burnsideC56_CS G T M H S L)
    (hj : conjJoin S L = L) (h3 : IsAltType L 3) (hD : S ⊓ centralizer (L : Set G) ≠ ⊥)
    {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) (A : Subgroup G) :
    IsMaxElemAbelian M₀ A ↔ IsMaxElemAbelian S A := by
  obtain ⟨x₀, hx₀, hx₀S⟩ := burnsideC56_exists_mem_diff hSM h2
  obtain ⟨W, hR1, hmain⟩ := burnsideC56_a3_rank1 hcs hj h3 hSM hMT h2
  obtain ⟨-, -, -, -, o5, -, o7, -, -, -, -, -⟩ := hmain x₀ hx₀ hx₀S
  have hQS : IsMaxElemAbelian S (pCoreOf 2 H) := by rw [o5]; exact o7
  constructor
  · rintro ⟨hAM, hAe, hmax⟩
    have hQA : Nat.card (pCoreOf 2 H) ≤ Nat.card A :=
      hmax _ (hQS.1.trans hSM) hQS.2.1
    have hAS : A ≤ S := burnsideC56_a3_star hcs hj h3 hD hSM hMT h2 hAM hAe hQA
    exact ⟨hAS, hAe, fun B hBS hBe => hmax B (hBS.trans hSM) hBe⟩
  · rintro ⟨hAS, hAe, hmax⟩
    refine ⟨hAS.trans hSM, hAe, fun B hBM hBe => ?_⟩
    by_contra hlt
    push Not at hlt
    have hQA : Nat.card (pCoreOf 2 H) ≤ Nat.card A := hmax _ hQS.1 hQS.2.1
    have hBS : B ≤ S :=
      burnsideC56_a3_star hcs hj h3 hD hSM hMT h2 hBM hBe (hQA.trans hlt.le)
    exact absurd (hmax B hBS hBe) (not_le.mpr hlt)

theorem burnsideC56_a3_index_two (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L)
    (h3 : IsAltType L 3) (hD : S ⊓ centralizer (L : Set G) ≠ ⊥) :
    S.relIndex T = 2 ∧ thompsonJ S = thompsonJ T := by
  obtain ⟨M₀, hSM, hMT, h2⟩ := exists_index_two hcs
  obtain ⟨x₀, hx₀, hx₀S⟩ := burnsideC56_exists_mem_diff hSM h2
  obtain ⟨W, hR1, hmain⟩ := burnsideC56_a3_rank1 hcs hj h3 hSM hMT h2
  obtain ⟨-, -, -, -, o5, -, -, o8, -, -, -, -⟩ := hmain x₀ hx₀ hx₀S
  have hiff := burnsideC56_a3_isMaxElemAbelian_iff hcs hj h3 hD hSM hMT h2
  have hAM : ∀ A : Subgroup G, IsMaxElemAbelian M₀ A ↔
      A = pCoreOf 2 H ∨ A = conjR (pCoreOf 2 H) x₀ := by
    intro A
    have h8 := o8 A
    rw [← o5] at h8
    exact (hiff A).trans h8
  have hJ : thompsonJ M₀ = thompsonJ S := by
    unfold thompsonJ
    refine iSup_congr fun A => ?_
    exact iSup_congr_Prop (hiff A) fun _ => rfl
  have hNle := normalizer_le_of_isMaxElemAbelian hcs hSM hMT hx₀ hAM
  have hMeq : M₀ = T := by
    by_contra hne'
    have hlt : M₀ < T := lt_of_le_of_ne hMT hne'
    obtain ⟨y, hyT, hyN, hyM⟩ := exists_mem_normalizer_not_mem_of_lt hcs.T_two hlt
    exact hyM (hNle ⟨hyT, hyN⟩)
  subst hMeq
  exact ⟨h2, hJ.symm⟩

end C56

end CFSG.QuasithinUnique.burnsideC56_P
