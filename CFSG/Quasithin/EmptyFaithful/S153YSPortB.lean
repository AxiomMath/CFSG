module

public import CFSG.Quasithin.EmptyFaithful.S153YSPortA

public section

namespace CFSG.QuasithinUnique.C56W

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

namespace WSet1

variable (hcs : WSet1 H S L)
include hcs

theorem single_rank1 (hN : NaturalModuleStructure)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3)
    {M₀ : Subgroup G} (hC : C5.NoCommonNormal S H M₀) (hSM : S ≤ M₀) (h2 : S.relIndex M₀ = 2) :
    ∃ (q : ℕ) (W : Subgroup G), 2 ≤ q ∧
      (baum S ⊓ centralizer (blockU L : Set G)).relIndex (baum S) = q ∧
      W.relIndex (blockU L) = q ∧
      (blockU L ⊓ centralizer (L : Set G)).relIndex (blockU L) = q ^ 2 ∧
      (∀ y ∈ baum S, y ∉ baum S ⊓ centralizer (blockU L : Set G) →
        ∀ u ∈ blockU L, (u ∈ W ↔ u * y = y * u)) ∧ ⁅blockU L, baum S⁆ = W ∧
      (∀ x ∈ M₀, x ∉ S →
        C56.SingleRank1Concl S H L (baum S ⊓ centralizer (blockU L : Set G)) q x) ∧
      blockQ L ≤ blockU L := by
  have hLsh := hcs.isShort
  have hSN := hcs.normalizes
  obtain ⟨hBN, hBsyl⟩ := C56.baumann_single hcs.minParabolic hcs.block hL hcs.thompson hcs.eq_join hSN
  obtain ⟨q, W, hq2, hWU, hidxQ, hidxW, hcent, hcomm, hZ, hgen, hSC⟩ :=
    hN G S H L hcs.minParabolic hcs.charTwo hcs.block hL hcs.thompson hcs.eq_join hSN
  set B := baum S with hBdef
  set U := blockU L with hUdef
  set Q := B ⊓ centralizer (U : Set G) with hQdef
  set P := pCoreOf 2 H with hPdef
  have hBS : B ≤ S := inf_le_left
  have hB2 : IsPGroup 2 B := hcs.isPGroup_S.to_le hBS
  have hBU : B ≤ normalizer (U : Set G) := hBS.trans hcs.S_le_normalizer_blockU
  set X := L ⊔ B with hXdef
  have hLX : L ≤ X := le_sup_left
  have hBX : B ≤ X := le_sup_right
  have hXN : X ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  have hXpow : ∀ g ∈ X, ∃ k : ℕ, g ^ 2 ^ k ∈ L := fun _ hg =>
    C1.exists_pow_mem_of_mem_sup hB2 hBN hg
  have hC111X : X ⊓ centralizer (U : Set G) = pCoreOf 2 X :=
    C1.inf_centralizer_blockU_eq hLsh hLX hXN hXpow
  have hQX : Q = pCoreOf 2 X := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
    · have : g ∈ X ⊓ centralizer (U : Set G) := ⟨hBX hg.1, hg.2⟩
      rwa [hC111X] at this
    · have h1 : g ∈ X ⊓ centralizer (U : Set G) := by rw [hC111X]; exact hg
      exact ⟨hBsyl.pCoreOf_le hg, h1.2⟩
  have hKQ : L ≤ normalizer (Q : Set G) := by
    rw [hQX]
    exact hLX.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X)
  have hQLX : blockQ L ≤ pCoreOf 2 X :=
    C1.le_pCoreOf_of_normalized ((C1.blockQ_le L).trans hLX)
      (fun _ hg => C1.mem_normalizer_blockQ (hXN hg)) (C1.blockQ_isPGroup L)
  have hUQ : U ≤ Q := by
    rw [hQX]
    exact (C1.blockU_le_blockQ hLsh).trans hQLX
  have hR1 : C5.Rank1 B Q U W q :=
    { U_le_Q := hUQ
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
  have hHP : H ≤ normalizer (P : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hC111 : H ⊓ centralizer (U : Set G) = P := hcs.inf_centralizer_eq
  have hSP : S ≤ normalizer (P : Set G) := fun _ hg => hHP (hcs.sylow.le hg)
  have hQP : Q ≤ P := fun g hg => by
    rw [← hC111]
    exact ⟨hcs.sylow.le (hBS hg.1), hg.2⟩
  have hUP : U ≤ P := hcs.blockU_le_pCoreOf
  have hPU : ∀ p ∈ P, ∀ u ∈ U, u * p = p * u := fun p hp u hu => by
    have : p ∈ H ⊓ centralizer (U : Set G) := by rw [hC111]; exact hp
    exact Subgroup.mem_centralizer_iff.mp this.2 u hu
  have hCRU : S ⊓ centralizer (U : Set G) ≤ P := fun g hg => by
    rw [← hC111]
    exact ⟨hcs.sylow.le hg.1, hg.2⟩
  have hxfacts : ∀ x ∈ M₀, x ∉ S → ¬ conjSubgroup U x ≤ Q ∧ ¬ conjSubgroup U x⁻¹ ≤ Q := by
    intro x hx hxS
    have hxinvS : x⁻¹ ∉ S := fun h => hxS (by simpa using inv_mem h)
    exact ⟨fun h => hcs.not_conj_le_of_mem_diff hC hSM h2 hx hxS (h.trans hQP),
      fun h => hcs.not_conj_le_of_mem_diff hC hSM h2 (inv_mem hx) hxinvS (h.trans hQP)⟩
  have hmain : ∀ x ∈ M₀, x ∉ S → C56.SingleRank1Concl S H L Q q x := by
    intro x hx hxS
    obtain ⟨hx1, hx2⟩ := hxfacts x hx hxS
    refine ⟨(hR1.relIndex_inf_conj (normalizer_le_normalizer_baum S
      (normalizer_of_relIndex_two hSM h2 hx)) hx1).1, ?_⟩
    exact C5.Rank1.rank1_main hR1 hC rfl hq2 (normalizer_of_relIndex_two hSM h2 hx)
      (mul_self_mem_of_relIndex_two h2 hx hxS) hx1 hx2 (C1.blockU_sq hLsh)
      ((C1.blockU_le_blockQ hLsh).trans (C1.blockQ_le L)) hKQ hZ hgen hSN
      hcs.S_le_normalizer_blockU hcs.eq_join.le
      (le_sup_zpowers_of_relIndex_two h2 hx hxS) hcs.pCoreOf_le_S
      hSP hHP hUP hQP hPU hCRU
      (fun r hr h => hSC r hr (fun b hb => by simpa [commutatorElement_def] using h b hb))
  obtain ⟨x₀, hx₀, hx₀S⟩ := exists_mem_diff_of_relIndex_two h2
  obtain ⟨hx1, hx2⟩ := hxfacts x₀ hx₀ hx₀S
  have hxB : x₀ ∈ normalizer (B : Set G) :=
    normalizer_le_normalizer_baum S (normalizer_of_relIndex_two hSM h2 hx₀)
  obtain ⟨-, -, -, -, -, hQe, -⟩ := hmain x₀ hx₀ hx₀S
  have hQ2 : IsPGroup 2 Q := hB2.to_le inf_le_left
  have hLQ' : blockQ L ≤ Q := by
    rw [hQX]
    exact hQLX
  have hQX₁ : Q ≤ L ⊔ Q := le_sup_right
  have hX₁Q : L ⊔ Q ≤ normalizer (Q : Set G) := sup_le hKQ Subgroup.le_normalizer
  have hXX₁ : L ⊔ Q ≤ X := sup_le hLX (inf_le_left.trans hBX)
  have hXN₁ : X ≤ normalizer ((L ⊔ Q : Subgroup G) : Set G) :=
    sup_le (fun l hl => Subgroup.le_normalizer (Subgroup.mem_sup_left hl))
      (fun b hb => C1.mem_normalizer_sup (hBN hb) (hR1.B_le_normQ hb))
  have hP₁ : IsSylowTwoOf (B ⊓ (L ⊔ Q)) (L ⊔ Q) :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hBsyl hXX₁
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXX₁).mpr hXN₁).isSubnormal
  have hUxB : conjSubgroup U x₀ ≤ B := hR1.conj_le_B hxB
  have hBeq : conjSubgroup U x₀ ⊔ Q = B := hR1.sup_Q_conj hxB hx2
  have hUxN : conjSubgroup U x₀ ≤ normalizer (Q : Set G) := hUxB.trans hR1.B_le_normQ
  obtain ⟨C, hCE, hCF, hCsupF⟩ := C5.exists_complement_elemAb2
    (E := conjSubgroup U x₀ ⊓ (L ⊔ Q)) (F := conjSubgroup U x₀ ⊓ (L ⊔ Q) ⊓ Q)
    (((C1.elemAb2_blockU hLsh).conjSubgroup x₀).mono inf_le_left) inf_le_left
  have hCP : C ≤ B ⊓ (L ⊔ Q) := fun c hc => ⟨hUxB (hCE hc).1, (hCE hc).2⟩
  have hCQ : C ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcC, hcQ⟩
    have : c ∈ C ⊓ (conjSubgroup U x₀ ⊓ (L ⊔ Q) ⊓ Q) := ⟨hcC, hCE hcC, hcQ⟩
    rw [hCF] at this
    exact this
  have hCsup : C ⊔ Q = B ⊓ (L ⊔ Q) := by
    refine le_antisymm (sup_le hCP (le_inf inf_le_left hQX₁)) fun g hg => ?_
    obtain ⟨hgB, hgX⟩ := hg
    rw [← hBeq] at hgB
    obtain ⟨a, ha, q', hq', rfl⟩ := C5.mem_sup_of_le_normalizer hUxN hgB
    have haX : a ∈ L ⊔ Q := by
      have := Subgroup.mul_mem _ hgX (Subgroup.inv_mem _ (hQX₁ hq'))
      simpa using this
    have : a ∈ C ⊔ (conjSubgroup U x₀ ⊓ (L ⊔ Q) ⊓ Q) := by
      rw [hCsupF]
      exact ⟨ha, haX⟩
    exact Subgroup.mul_mem _ (sup_le_sup_left inf_le_right C this) (Subgroup.mem_sup_right hq')
  obtain ⟨X₀, -, hX₀inf, hX₀sup⟩ := C5.exists_complement_of_sylow_split hQX₁ hX₁Q hQe.1 hQ2 hP₁
    hCP hCQ hCsup
  have hUeq : blockQ L ≤ blockU L :=
    C5.blockQ_le_blockU_of_split hLsh hQe.1 hQe.2 hKQ (fun q hq u hu => hPU q (hQP hq) u hu)
      (fun q hq l hl => hcs.bb1 q (hQP hq) l hl) hLQ' hX₀inf hX₀sup
  exact ⟨q, W, hq2, hidxQ, hidxW, hZ, hcent, hcomm, hmain, hUeq⟩

end WSet1

end CFSG.QuasithinUnique.C56W
