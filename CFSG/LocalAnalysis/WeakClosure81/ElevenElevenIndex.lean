module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenNineTwo
public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenTransv

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

private theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := B2F.relIndex_sup_eq_of_le_normalizer' hA
  have h2 := Subgroup.relIndex_mul_card B (A ⊔ B)
  have h3 := Subgroup.relIndex_mul_card B A
  have h4 : B ⊓ (A ⊔ B) = B := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [← h2, ← h3, inf_comm]
  ring

theorem eleven11_comm_D_le {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) :
    ∀ d ∈ Q ⊓ centralizerModCore L, ∀ l ∈ L, d * l * d⁻¹ * l⁻¹ ∈ blockU L := by
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  intro d hd' l hl
  exact ((ThmOne.mem_centralizerModCore_iff_blockU hLb.2.2.1.residual_eq).mp
    (Subgroup.mem_inf.1 hd').2).2 l hl

theorem eleven11_normalizer_D {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) :
    ∀ l ∈ L, ∀ d ∈ Q ⊓ centralizerModCore L, l * d * l⁻¹ ∈ Q ⊓ centralizerModCore L := by
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  intro l hl d hdD
  have hw : d * l * d⁻¹ * l⁻¹ ∈ blockU L := eleven11_comm_D_le hd d hdD l hl
  have hWD : blockU L ≤ Q ⊓ centralizerModCore L := fun w hw =>
    Subgroup.mem_inf.2 ⟨eleven11_blockU_le_Q hd hw,
      Glue.oTwoIn_le_centralizerModCore L (blockU_le_oTwoIn L hw)⟩
  have h2 : (d * l * d⁻¹ * l⁻¹)⁻¹ * d = l * d * l⁻¹ := by group
  rw [← h2]
  exact (Q ⊓ centralizerModCore L).mul_mem ((Q ⊓ centralizerModCore L).inv_mem (hWD hw)) hdD

theorem eleven11_card_Q {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) :
    Nat.card Q = 4 * Nat.card (Q ⊓ centralizerModCore L : Subgroup G) := by
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
  have h78 : IsLTwoBlockType L 2 := (eleven11_blockType_two hd h8).1
  have key : ∀ q ∈ Q, ∀ d ∈ Q ⊓ centralizerModCore L, q * d * q⁻¹ ∈ Q ⊓ centralizerModCore L :=
    fun q hq d hdD =>
      Subgroup.mem_inf.2 ⟨Q.mul_mem (Q.mul_mem hq (Subgroup.mem_inf.1 hdD).1) (Q.inv_mem hq),
        Glue.conj_mem_centralizerModCore (eleven11_Q_le_normalizer hd hq)
          (Subgroup.mem_inf.1 hdD).2⟩
  have hQN : Q ≤ Subgroup.normalizer ((Q ⊓ centralizerModCore L : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key q hq h hh, fun hh => ?_⟩
    have := key q⁻¹ (Q.inv_mem hq) _ hh
    simpa [mul_assoc] using this
  have hprod := card_sup_mul_card_inf_of_le_normalizer (inf_le_right.trans hQN : L ⊓ Q ≤ _)
  have hsup : (L ⊓ Q) ⊔ (Q ⊓ centralizerModCore L) = Q := by
    refine le_antisymm (sup_le inf_le_right inf_le_left) ?_
    intro x hx
    obtain ⟨s, hs, c, hc, rfl⟩ := eleven_nine_two hd.setting hUΓ hLb hLM h78 x hx
    exact mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hc)
  have hinf : (L ⊓ Q) ⊓ (Q ⊓ centralizerModCore L) = oTwoIn L := by
    rw [← eleven11_inf_centralizerModCore hd h8]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  rw [hsup, hinf, eleven11_card_sylow hd h8] at hprod
  have hpos : 0 < Nat.card (oTwoIn L : Subgroup G) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [hprod]
  ring

theorem eleven11_cent_blockU_eq {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) :
    Q ⊓ Subgroup.centralizer (blockU L : Set G) = Q ⊓ centralizerModCore L := by
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
  have h78 : IsLTwoBlockType L 2 := (eleven11_blockType_two hd h8).1
  have hD2 : IsPGroup 2 (Q ⊓ centralizerModCore L : Subgroup G) :=
    hd.setting.sylowQ.2.1.to_le inf_le_left
  have hDC : Q ⊓ centralizerModCore L ≤ Subgroup.centralizer (blockU L : Set G) :=
    ThmOne.le_centralizer_blockU_of_le_centralizerModCore hLb.2.2.1 hD2 inf_le_right
  refine le_antisymm ?_ (le_inf inf_le_left (hDC))
  intro y hy
  obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨t, ht, d, hdD, rfl⟩ := eleven_nine_two hd.setting hUΓ hLb hLM h78 y hyQ
  by_cases ht0 : t ∈ oTwoIn L
  · have hP0 : oTwoIn L ≤ Q ⊓ centralizerModCore L := fun g hg =>
      Subgroup.mem_inf.2 ⟨eleven_nine_oTwoIn_le_Q hd.setting hUΓ hLb hg,
        Glue.oTwoIn_le_centralizerModCore L hg⟩
    exact (Q ⊓ centralizerModCore L).mul_mem (hP0 ht0) hdD
  · exfalso
    have hdW : ∀ w ∈ blockU L, w * d = d * w := fun w hw =>
      Subgroup.mem_centralizer_iff.1 (hDC hdD) w hw
    have htW : blockU L ≤ Subgroup.centralizer ({t} : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : w * (t * d) = (t * d) * w := (Subgroup.mem_centralizer_iff.1 hyC w hw)
      have h2 : w * t * d = t * w * d := by
        calc w * t * d = w * (t * d) := by rw [mul_assoc]
          _ = (t * d) * w := h1
          _ = t * (d * w) := by rw [mul_assoc]
          _ = t * (w * d) := by rw [hdW w hw]
          _ = t * w * d := by rw [mul_assoc]
      exact mul_right_cancel h2
    have hle : blockU L ≤ ⁅V, X⁆ ⊔ blockZ L := by
      rw [← eleven11_blockU_inf_centralizer hd h8 ht ht0]
      exact le_inf le_rfl htW
    have h4 := eleven11_card_blockU_eq_four_mul hd h8
    have hcard := Subgroup.card_le_of_le hle
    have hpos : 0 < Nat.card (⁅V, X⁆ ⊔ blockZ L : Subgroup G) := Nat.card_pos
    omega

theorem eleven11_blockU_inf_centralizer_of_mem
    {M V Q U L X : Subgroup G} (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8)
    {y : G} (hy : y ∈ Q) (hyD : y ∉ centralizerModCore L) :
    blockU L ⊓ Subgroup.centralizer ({y} : Set G) = ⁅V, X⁆ ⊔ blockZ L := by
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
  have h78 : IsLTwoBlockType L 2 := (eleven11_blockType_two hd h8).1
  obtain ⟨t, ht, d, hdD, rfl⟩ := eleven_nine_two hd.setting hUΓ hLb hLM h78 y hy
  have hdC : d ∈ Subgroup.centralizer (blockU L : Set G) := by
    have h : d ∈ Q ⊓ Subgroup.centralizer (blockU L : Set G) := by
      rw [eleven11_cent_blockU_eq hd h8]
      exact hdD
    exact (Subgroup.mem_inf.1 h).2
  have ht0 : t ∉ oTwoIn L := by
    intro h
    exact hyD (mul_mem (Glue.oTwoIn_le_centralizerModCore L h) (Subgroup.mem_inf.1 hdD).2)
  have hdW : ∀ w ∈ blockU L, w * d = d * w := fun w hw => Subgroup.mem_centralizer_iff.1 hdC w hw
  rw [← eleven11_blockU_inf_centralizer hd h8 ht ht0]
  ext w
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun hw => ?_
  constructor
  · intro h
    have h2 : w * t * d = t * w * d := by
      calc w * t * d = w * (t * d) := by rw [mul_assoc]
        _ = (t * d) * w := h
        _ = t * (d * w) := by rw [mul_assoc]
        _ = t * (w * d) := by rw [hdW w hw]
        _ = t * w * d := by rw [mul_assoc]
    exact mul_right_cancel h2
  · intro h
    calc w * (t * d) = w * t * d := by rw [mul_assoc]
      _ = t * w * d := by rw [h]
      _ = t * (w * d) := by rw [mul_assoc]
      _ = t * (d * w) := by rw [hdW w hw]
      _ = (t * d) * w := by rw [mul_assoc]

structure TransvPair (Q W S : Subgroup G) : Prop where
  le : W ≤ Q
  normal : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ ∈ W
  comm : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w
  le_W : S ≤ W
  card_index : Nat.card Q = 4 * Nat.card (Q ⊓ Subgroup.centralizer (W : Set G) : Subgroup G)
  card_S : Nat.card W = 4 * Nat.card S
  centralizer_eq : ∀ y ∈ Q, y ∉ Subgroup.centralizer (W : Set G) →
    W ⊓ Subgroup.centralizer ({y} : Set G) = S

theorem eleven11_transvPair {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) :
    TransvPair Q (blockU L) (⁅V, X⁆ ⊔ blockZ L) := by
  obtain ⟨hle, -, -, -, -⟩ := eleven11_commutator_VX hd h8
  refine ⟨eleven11_blockU_le_Q hd, fun q hq w hw =>
    conj_mem_blockU (eleven11_Q_le_normalizer hd hq) hw, eleven11_blockU_comm hd,
    sup_le (hle.trans inf_le_right) (blockZ_le_blockU L), ?_,
    eleven11_card_blockU_eq_four_mul hd h8, fun y hy hyC => ?_⟩
  · rw [eleven11_cent_blockU_eq hd h8]
    exact eleven11_card_Q hd h8
  · refine eleven11_blockU_inf_centralizer_of_mem hd h8 hy fun h => hyC ?_
    have hyD : y ∈ Q ⊓ centralizerModCore L := Subgroup.mem_inf.2 ⟨hy, h⟩
    rw [← eleven11_cent_blockU_eq hd h8] at hyD
    exact (Subgroup.mem_inf.1 hyD).2

private theorem mem_conj_smul_iff' {g x : G} {Y : Subgroup G} :
    x ∈ MulAut.conj g • Y ↔ g⁻¹ * x * g ∈ Y := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply, inv_inv]

private theorem card_conj_smul' (g : G) (Y : Subgroup G) :
    Nat.card ↥(MulAut.conj g • Y) = Nat.card Y :=
  (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) Y).toEquiv).symm

private theorem mul_comm_conj_iff (x a b : G) :
    (x⁻¹ * a * x) * (x⁻¹ * b * x) = (x⁻¹ * b * x) * (x⁻¹ * a * x) ↔ a * b = b * a := by
  constructor
  · intro h
    have h2 : x * ((x⁻¹ * a * x) * (x⁻¹ * b * x)) * x⁻¹ =
        x * ((x⁻¹ * b * x) * (x⁻¹ * a * x)) * x⁻¹ := by rw [h]
    simpa [mul_assoc] using h2
  · intro h
    calc (x⁻¹ * a * x) * (x⁻¹ * b * x) = x⁻¹ * (a * b) * x := by group
      _ = x⁻¹ * (b * a) * x := by rw [h]
      _ = (x⁻¹ * b * x) * (x⁻¹ * a * x) := by group

theorem TransvPair.conj {Q W S : Subgroup G} (h : TransvPair Q W S) {x : G}
    (hx : x ∈ Subgroup.normalizer (Q : Set G)) :
    TransvPair Q (MulAut.conj x • W) (MulAut.conj x • S) := by
  have hxQ : ∀ y : G, y ∈ Q ↔ x⁻¹ * y * x ∈ Q := fun y => by
    simpa using Subgroup.mem_normalizer_iff.1 (inv_mem hx) y
  have hcent : ∀ y : G, y ∈ Subgroup.centralizer ((MulAut.conj x • W : Subgroup G) : Set G) ↔
      x⁻¹ * y * x ∈ Subgroup.centralizer (W : Set G) := by
    intro y
    simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, mem_conj_smul_iff']
    constructor
    · intro hy w hw
      have h1 := hy (x * w * x⁻¹) (by rw [show x⁻¹ * (x * w * x⁻¹) * x = w by group]; exact hw)
      have h2 := (mul_comm_conj_iff x (x * w * x⁻¹) y).2 h1
      simpa [mul_assoc] using h2
    · intro hy w' hw'
      have h1 := hy (x⁻¹ * w' * x) hw'
      exact (mul_comm_conj_iff x w' y).1 h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact (hxQ y).2 (h.le (mem_conj_smul_iff'.1 hy))
  · intro q hq w hw
    rw [mem_conj_smul_iff'] at hw ⊢
    have := h.normal (x⁻¹ * q * x) ((hxQ q).1 hq) _ hw
    simpa [mul_assoc] using this
  · intro w hw w' hw'
    rw [mem_conj_smul_iff'] at hw hw'
    exact (mul_comm_conj_iff x w w').1 (h.comm _ hw _ hw')
  · exact (Subgroup.pointwise_smul_le_pointwise_smul_iff).2 h.le_W
  · have hset : Q ⊓ Subgroup.centralizer ((MulAut.conj x • W : Subgroup G) : Set G) =
        MulAut.conj x • (Q ⊓ Subgroup.centralizer (W : Set G)) := by
      ext y
      rw [Subgroup.mem_inf, hcent, mem_conj_smul_iff', Subgroup.mem_inf, ← hxQ]
    rw [hset, card_conj_smul']
    exact h.card_index
  · rw [card_conj_smul', card_conj_smul']
    exact h.card_S
  · intro y hy hyC
    have hy' : x⁻¹ * y * x ∈ Q := (hxQ y).1 hy
    have hyC' : x⁻¹ * y * x ∉ Subgroup.centralizer (W : Set G) := fun hh => hyC ((hcent y).2 hh)
    have key := h.centralizer_eq _ hy' hyC'
    ext z
    rw [Subgroup.mem_inf, mem_conj_smul_iff', mem_conj_smul_iff', ← key, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    refine and_congr Iff.rfl ?_
    exact (mul_comm_conj_iff x z y).symm

end CFSG.LocalAnalysis.WeakClosure81
