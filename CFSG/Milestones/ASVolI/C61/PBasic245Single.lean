module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Single
public import CFSG.Milestones.ASVolI.C61.CS

public section

namespace CFSG.QuasithinUnique.burnsideC56_P

open CFSG.Open CFSG.Quasithin Subgroup
open scoped commutatorElement

namespace C56
open CFSG.QuasithinUnique.C56

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem isShort (hcs : burnsideC56_CS G T M H S L) : IsShort2 L := hcs.block.1.1

theorem le_H (hcs : burnsideC56_CS G T M H S L) : L ≤ H := hcs.block.1.2.1

theorem isPGroup_S (hcs : burnsideC56_CS G T M H S L) : IsPGroup 2 S := hcs.sylow.isPGroup

theorem H_eq (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L) : H = L ⊔ S := by
  rw [hcs.eq_join, hj]

theorem H_le_normalizer (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L) :
    H ≤ normalizer (L : Set G) := by
  rw [H_eq hcs hj]
  exact sup_le Subgroup.le_normalizer (S_le_normalizer hj)

theorem H_pow_mem (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L) :
    ∀ g ∈ H, ∃ k : ℕ, g ^ 2 ^ k ∈ L := fun _ hg =>
  C1.exists_pow_mem_of_mem_sup (isPGroup_S hcs) (S_le_normalizer hj) (H_eq hcs hj ▸ hg)

theorem inf_centralizer_eq (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L) :
    H ⊓ centralizer (blockU L : Set G) = pCoreOf 2 H :=
  C1.inf_centralizer_blockU_eq (isShort hcs) (le_H hcs) (H_le_normalizer hcs hj) (H_pow_mem hcs hj)

theorem pCoreOf_le_S (hcs : burnsideC56_CS G T M H S L) : pCoreOf 2 H ≤ S :=
  hcs.sylow.pCoreOf_le

theorem blockQ_le_pCoreOf (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L) :
    blockQ L ≤ pCoreOf 2 H :=
  C1.le_pCoreOf_of_normalized ((C1.blockQ_le L).trans (le_H hcs))
    (fun _ hg => C1.mem_normalizer_blockQ (H_le_normalizer hcs hj hg)) (C1.blockQ_isPGroup L)

theorem blockU_le_pCoreOf (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L) :
    blockU L ≤ pCoreOf 2 H :=
  (C1.blockU_le_blockQ (isShort hcs)).trans (blockQ_le_pCoreOf hcs hj)

theorem noCommonNormal (hcs : burnsideC56_CS G T M H S L) {M₀ : Subgroup G} (hSM : S ≤ M₀)
    (hMT : M₀ ≤ T) (hne : S ≠ M₀) : C5.NoCommonNormal S H M₀ := by
  intro X hXS hXne hHX hM₀X
  have h244 := hcs.l244 X hXne hXS hHX
  apply hne
  refine le_antisymm hSM fun m hm => ?_
  have : m ∈ T ⊓ normalizer (X : Set G) := ⟨hMT hm, hM₀X hm⟩
  rw [h244] at this
  exact this

theorem blockQ_le_pCoreOf_conjJoin (hcs : burnsideC56_CS G T M H S L) :
    blockQ L ≤ pCoreOf 2 (conjJoin S L) := by
  have hLK : L ≤ conjJoin S L := le_conjJoin L (one_mem _)
  refine C1.le_pCoreOf_of_normalized ((C1.blockQ_le L).trans hLK) ?_ (C1.blockQ_isPGroup L)
  rcases hcs.blocks with hj | ⟨t, ht, hne, hK, hcomm⟩
  · rw [hj]
    exact C1.le_normalizer_blockQ L
  · rw [hK]
    refine sup_le (C1.le_normalizer_blockQ L) ?_
    have hc : L.map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact C5.le_normalizer_of_commute fun u hu a ha =>
      (Subgroup.mem_centralizer_iff.mp (hc hu) a (C1.blockQ_le L ha)).symm

theorem pCoreOf_conjJoin_le (hcs : burnsideC56_CS G T M H S L) :
    pCoreOf 2 (conjJoin S L) ≤ pCoreOf 2 H := by
  have hKH : conjJoin S L ≤ H := by
    rw [hcs.eq_join]
    exact le_sup_left
  have hHK : H ≤ normalizer (conjJoin S L : Set G) := by
    rw [hcs.eq_join]
    exact sup_le Subgroup.le_normalizer (S_le_normalizer_conjJoin L)
  refine C1.le_pCoreOf_of_normalized ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans hKH)
    (fun g hg => ?_) (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (conjJoin S L) (hHK hg)

theorem blockU_le_pCoreOf_general (hcs : burnsideC56_CS G T M H S L) :
    blockU L ≤ pCoreOf 2 H :=
  (C1.blockU_le_blockQ (isShort hcs)).trans
    ((blockQ_le_pCoreOf_conjJoin hcs).trans (pCoreOf_conjJoin_le hcs))

theorem exists_index_two (hcs : burnsideC56_CS G T M H S L) :
    ∃ M₀ : Subgroup G, S ≤ M₀ ∧ M₀ ≤ T ∧ S.relIndex M₀ = 2 :=
  exists_relIndex_two hcs.T_two hcs.le_T hcs.ne_T

theorem not_conj_le_of_exists (hcs : burnsideC56_CS G T M H S L) {M₀ : Subgroup G}
    (h2 : S.relIndex M₀ = 2) (hex : ∃ y ∈ M₀, ¬ conjR (blockU L) y ≤ pCoreOf 2 H) {x : G}
    (hx : x ∈ M₀) (hxS : x ∉ S) : ¬ conjR (blockU L) x ≤ pCoreOf 2 H := by
  obtain ⟨y, hy, hyU⟩ := hex
  have hyS : y ∉ S := by
    intro hyS
    apply hyU
    have hUP := blockU_le_pCoreOf_general hcs
    have hPn : y ∈ normalizer (pCoreOf 2 H : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H (hcs.sylow.le hyS)
    have := C5.conjSubgroup_mono hUP y
    rwa [C5.conjSubgroup_eq_self hPn] at this
  have hs : y⁻¹ * x ∈ S := inv_mul_mem_of_relIndex_two h2 hy hyS hx hxS
  intro hxP
  apply hyU
  have hPn : (y⁻¹ * x)⁻¹ ∈ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
      (hcs.sylow.le (inv_mem hs))
  have h1 := C5.conjSubgroup_mono hxP (y⁻¹ * x)⁻¹
  rw [conjR_eq, conjSubgroup_conjSubgroup, C5.conjSubgroup_eq_self hPn] at h1
  have e : x * (y⁻¹ * x)⁻¹ = y := by group
  rw [e] at h1
  exact h1

theorem H_le_normalizer_conjJoin (hcs : burnsideC56_CS G T M H S L) :
    H ≤ normalizer (conjJoin S L : Set G) := by
  rw [hcs.eq_join]
  exact sup_le Subgroup.le_normalizer (S_le_normalizer_conjJoin L)

theorem bb1 (hcs : burnsideC56_CS G T M H S L) :
    ∀ p ∈ pCoreOf 2 H, ∀ l ∈ L, p * l * p⁻¹ * l⁻¹ ∈ blockU L := by
  intro p hp l hl
  rcases hcs.blocks with hj | ⟨t, -, -, hK, hcomm⟩
  · exact C1.commutator_mem_blockU_of_mem_blockQ (isShort hcs)
      (fun l hl => C1.commutator_mem_blockQ_of_mem_pCoreOf (le_H hcs)
        (H_le_normalizer hcs hj) hp hl) l hl
  · have hLc : L ≤ centralizer ((L.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hc : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj t).toMonoidHom, a * b = b * a :=
      fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hLc ha) b hb).symm
    refine C1.commutator_mem_blockU_double (isShort hcs) hc (le_H hcs) ?_ hp hl
    rw [← hK]
    exact H_le_normalizer_conjJoin hcs

theorem c55 (hcs : burnsideC56_CS G T M H S L)
    {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (hne : S ≠ M₀) :
    ∃ y ∈ M₀, ¬ conjR (blockU L) y ≤ pCoreOf 2 H := by
  by_contra hcon
  push Not at hcon
  have hL := isShort hcs
  set U := blockU L with hU
  set P := pCoreOf 2 H with hP
  set X : Subgroup G := ⨆ y : M₀, conjR U (y : G) with hX
  have hXP : X ≤ P := iSup_le fun y => hcon y y.2
  have hUX : U ≤ X := by
    have h1 : conjR U ((⟨1, one_mem _⟩ : M₀) : G) ≤ X :=
      le_iSup (fun y : M₀ => conjR U (y : G)) ⟨1, one_mem _⟩
    have h2 : conjR U ((⟨1, one_mem _⟩ : M₀) : G) = U := conjSubgroup_one U
    rwa [h2] at h1
  have hXne : X ≠ ⊥ := fun h => blockU_ne_bot hL (le_bot_iff.mp (h ▸ hUX))
  have hXS : X ≤ S := hXP.trans (pCoreOf_le_S hcs)
  have hM₀X : M₀ ≤ normalizer (X : Set G) := by
    intro m hm
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    have hle : conjSubgroup X m ≤ X := by
      have : conjSubgroup X m = ⨆ y : M₀, conjSubgroup (conjR U (y : G)) m := by
        simp only [conjSubgroup, hX]
        exact Subgroup.map_iSup _ _
      rw [this]
      refine iSup_le fun y => ?_
      have : conjSubgroup (conjR U (y : G)) m = conjR U ((y : G) * m) :=
        conjSubgroup_conjSubgroup U (y : G) m
      rw [this]
      exact le_iSup (fun y : M₀ => conjR U (y : G)) ⟨(y : G) * m, mul_mem y.2 hm⟩
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [C5.card_conjSubgroup])
  have key : ∀ l ∈ L, ∀ x ∈ X, l * x * l⁻¹ ∈ X := by
    intro l hl x hx
    refine Subgroup.iSup_induction (fun y : M₀ => conjR U (y : G))
      (C := fun x => l * x * l⁻¹ ∈ X) hx ?_ ?_ ?_
    · intro y x hxy
      have hxP : x ∈ P := hcon y y.2 hxy
      have hc : l * x * l⁻¹ * x⁻¹ ∈ U := by
        have h1 := bb1 hcs x hxP l hl
        have e : l * x * l⁻¹ * x⁻¹ = (x * l * x⁻¹ * l⁻¹)⁻¹ := by group
        rw [e]
        exact inv_mem h1
      have hxX : x ∈ X := le_iSup (fun y : M₀ => conjR U (y : G)) y hxy
      have e : l * x * l⁻¹ = (l * x * l⁻¹ * x⁻¹) * x := by group
      rw [e]
      exact mul_mem (hUX hc) hxX
    · simp
    · intro a b ha hb
      have e : l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
  have hLX : L ≤ normalizer (X : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => key l hl x hx
    · intro h
      have := key l⁻¹ (inv_mem hl) _ h
      simpa [mul_assoc] using this
  have hHX : H ≤ normalizer (X : Set G) := by
    rw [hcs.eq_join]
    refine sup_le (iSup_le fun s => ?_) (hSM.trans hM₀X)
    rintro g ⟨l, hl, rfl⟩
    have hs : (s : G) ∈ normalizer (X : Set G) := hM₀X (hSM s.2)
    have e : (MulAut.conj (s : G)).toMonoidHom l = (s : G) * l * (s : G)⁻¹ := by
      simp [MulAut.conj_apply]
    rw [e]
    exact mul_mem (mul_mem hs (hLX hl)) (inv_mem hs)
  exact noCommonNormal hcs hSM hMT hne X hXS hXne hHX hM₀X

theorem not_conj_le_of_mem_diff (hcs : burnsideC56_CS G T M H S L)
    {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) {x : G}
    (hx : x ∈ M₀) (hxS : x ∉ S) : ¬ conjR (blockU L) x ≤ pCoreOf 2 H := by
  have hne : S ≠ M₀ := by
    intro h
    apply hxS
    rw [h]
    exact hx
  exact not_conj_le_of_exists hcs h2 (c55 hcs hSM hMT hne) hx hxS

theorem single_rank1 (hN : NaturalModuleStructure)
    (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3)
    {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) :
    ∃ (q : ℕ) (W : Subgroup G), 2 ≤ q ∧
      (baum S ⊓ centralizer (blockU L : Set G)).relIndex (baum S) = q ∧
      W.relIndex (blockU L) = q ∧
      (blockU L ⊓ centralizer (L : Set G)).relIndex (blockU L) = q ^ 2 ∧
      (∀ y ∈ baum S, y ∉ baum S ⊓ centralizer (blockU L : Set G) →
        ∀ u ∈ blockU L, (u ∈ W ↔ u * y = y * u)) ∧ ⁅blockU L, baum S⁆ = W ∧
      (∀ x ∈ M₀, x ∉ S →
        SingleRank1Concl S H L (baum S ⊓ centralizer (blockU L : Set G)) q x) ∧
      blockQ L ≤ blockU L := by
  have hLsh := isShort hcs
  have hLH := le_H hcs
  have hHN := H_le_normalizer hcs hj
  have hSN := S_le_normalizer hj
  have hne : S ≠ M₀ := by
    intro h
    rw [← h] at h2
    simp at h2
  obtain ⟨hBN, hBsyl⟩ := baumann_single hcs.minParabolic hcs.block hL hcs.thompson (H_eq hcs hj) hSN
  obtain ⟨q, W, hq2, hWU, hidxQ, hidxW, hcent, hcomm, hZ, hgen, hSC⟩ :=
    hN G S H L hcs.minParabolic hcs.charTwo hcs.block hL hcs.thompson (H_eq hcs hj) hSN
  set B := baum S with hBdef
  set U := blockU L with hUdef
  set Q := B ⊓ centralizer (U : Set G) with hQdef
  set P := pCoreOf 2 H with hPdef
  have hBS : B ≤ S := inf_le_left
  have hB2 : IsPGroup 2 B := (isPGroup_S hcs).to_le hBS
  have hBU : B ≤ normalizer (U : Set G) := hBS.trans (S_le_normalizer_blockU hj)
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
  have hPH : P ≤ H := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H
  have hHP : H ≤ normalizer (P : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hC111 : H ⊓ centralizer (U : Set G) = P := inf_centralizer_eq hcs hj
  have hSP : S ≤ normalizer (P : Set G) := fun _ hg => hHP (hcs.sylow.le hg)
  have hQP : Q ≤ P := fun g hg => by
    rw [← hC111]
    exact ⟨hcs.sylow.le (hBS hg.1), hg.2⟩
  have hUP : U ≤ P := blockU_le_pCoreOf hcs hj
  have hPU : ∀ p ∈ P, ∀ u ∈ U, u * p = p * u := fun p hp u hu => by
    have : p ∈ H ⊓ centralizer (U : Set G) := by rw [hC111]; exact hp
    exact Subgroup.mem_centralizer_iff.mp this.2 u hu
  have hCRU : S ⊓ centralizer (U : Set G) ≤ P := fun g hg => by
    rw [← hC111]
    exact ⟨hcs.sylow.le hg.1, hg.2⟩
  have hC := noCommonNormal hcs hSM hMT hne
  have hxfacts : ∀ x ∈ M₀, x ∉ S → ¬ conjSubgroup U x ≤ Q ∧ ¬ conjSubgroup U x⁻¹ ≤ Q := by
    intro x hx hxS
    have hxinvS : x⁻¹ ∉ S := fun h => hxS (by simpa using inv_mem h)
    exact ⟨fun h => not_conj_le_of_mem_diff hcs hSM hMT h2 hx hxS (h.trans hQP),
      fun h => not_conj_le_of_mem_diff hcs hSM hMT h2 (inv_mem hx) hxinvS (h.trans hQP)⟩
  have hmain : ∀ x ∈ M₀, x ∉ S → SingleRank1Concl S H L Q q x := by
    intro x hx hxS
    obtain ⟨hx1, hx2⟩ := hxfacts x hx hxS
    refine ⟨(hR1.relIndex_inf_conj (normalizer_le_normalizer_baum S
      (normalizer_of_relIndex_two hSM h2 hx)) hx1).1, ?_⟩
    exact C5.Rank1.rank1_main hR1 hC rfl hq2 (normalizer_of_relIndex_two hSM h2 hx)
      (mul_self_mem_of_relIndex_two h2 hx hxS) hx1 hx2 (C1.blockU_sq hLsh)
      ((C1.blockU_le_blockQ hLsh).trans (C1.blockQ_le L)) hKQ hZ hgen hSN
      (S_le_normalizer_blockU hj) (H_eq hcs hj ▸ le_rfl)
      (le_sup_zpowers_of_relIndex_two h2 hx hxS) (pCoreOf_le_S hcs)
      hSP hHP hUP hQP hPU hCRU
      (fun r hr h => hSC r hr (fun b hb => by simpa [commutatorElement_def] using h b hb))
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
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
      (fun q hq l hl => bb1 hcs q (hQP hq) l hl) hLQ' hX₀inf hX₀sup
  exact ⟨q, W, hq2, hidxQ, hidxW, hZ, hcent, hcomm, hmain, hUeq⟩

theorem c56_7_single (hN : NaturalModuleStructure)
    (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) (h5 : ¬ IsAltType L 5)
    {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) :
    C56_7Concl S H L M₀ := by
  have hLsh := isShort hcs
  have hSN := S_le_normalizer hj
  have hne : S ≠ M₀ := by
    intro h
    rw [← h] at h2
    simp at h2
  obtain ⟨_, -, -, -, -, -, -, -, hmain, hUeq⟩ := single_rank1 hN hcs hj hL hSM hMT h2
  set B := baum S with hBdef
  set U := blockU L with hUdef
  set Q := B ⊓ centralizer (U : Set G) with hQdef
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  obtain ⟨-, o1, o2, -, o4, -, o6, -, -, o9, -, o11⟩ := hmain x₀ hx₀ hx₀S
  have hUL : U ≤ L := (C1.blockU_le_blockQ hLsh).trans (C1.blockQ_le L)
  have hbaumD : baumD S L = Q ⊓ centralizer (L : Set G) := by
    have hCLU : centralizer (L : Set G) ≤ centralizer (U : Set G) :=
      Subgroup.centralizer_le (fun u hu => hUL hu)
    show baum S ⊓ centralizer ((conjJoin S L : Subgroup G) : Set G) = _
    rw [hj]
    refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
    · exact ⟨⟨hg.1, hCLU hg.2⟩, hg.2⟩
    · exact ⟨hg.1.1, hg.2⟩
  have hblockD : blockD S L = Q ⊓ centralizer (L : Set G) := by
    show S ⊓ centralizer ((conjJoin S L : Subgroup G) : Set G) = _
    rw [hj]
    exact o11
  have hblockU0 : blockU0 S L = U := by
    show conjJoin S (blockU L) = blockU L
    exact conjJoin_eq_of_le_normalizer (S_le_normalizer_blockU hj)
  unfold C56_7Concl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hblockU0, hj]
    exact le_antisymm (C1.blockU_le_blockQ hLsh) hUeq
  · rw [hbaumD]
    exact C5.isElemAbelian_two_iff.mpr o2
  · rw [hbaumD, hblockD]
  · rw [hbaumD, hblockU0, o4]
    calc Q = U ⊔ (Q ⊓ centralizer (L : Set G)) := o1
      _ = (Q ⊓ centralizer (L : Set G)) ⊔ U := sup_comm _ _
  · rw [o4]
    exact o6
  · exact o9.symm
  · intro x hx hxS
    obtain ⟨-, p1, -, p3, p4, -, -, p7, p8, -, p10, -⟩ := hmain x hx hxS
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hbaumD]
      exact p3
    · rw [hbaumD, hblockU0]
      exact sup_sup_aux p1 p8 p10
    · intro _ _ A
      rw [p4]
      exact p7 A
    · intro _ h
      exact absurd h h5
    · intro h
      exact absurd hj h

end C56

end CFSG.QuasithinUnique.burnsideC56_P
