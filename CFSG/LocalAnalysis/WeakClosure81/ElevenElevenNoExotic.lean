module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenJoin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem card_le_sixteen_mul_card_inf {D E E' : Subgroup G} (hE : E ≤ D) (hE' : E' ≤ D)
    (h : Nat.card D = 4 * Nat.card E) (h' : Nat.card D = 4 * Nat.card E') :
    Nat.card D ≤ 16 * Nat.card ↥(E ⊓ E') := by
  have hr : E.relIndex D = 4 := by
    have := Subgroup.relIndex_mul_card E D
    rw [inf_of_le_left hE, h] at this
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
  have hr' : E'.relIndex D = 4 := by
    have := Subgroup.relIndex_mul_card E' D
    rw [inf_of_le_left hE', h'] at this
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
  have hle : (E ⊓ E').relIndex D ≤ 16 := by
    calc _ ≤ _ := Subgroup.relIndex_inf_le
      _ = 16 := by rw [hr, hr']
  have hmul := Subgroup.relIndex_mul_card (E ⊓ E') D
  rw [inf_of_le_left (inf_le_left.trans hE)] at hmul
  rw [← hmul]
  exact Nat.mul_le_mul_right _ hle

private theorem mem_conj_smul_iff_aux {g z : G} {Y : Subgroup G} :
    z ∈ MulAut.conj g • Y ↔ g⁻¹ * z * g ∈ Y := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply, inv_inv]

theorem card_inf_centralizer_conj_smul {D A : Subgroup G} {k : G}
    (hk : ∀ d ∈ D, k * d * k⁻¹ ∈ D) (hk' : ∀ d ∈ D, k⁻¹ * d * k ∈ D) :
    Nat.card ↥(D ⊓ Subgroup.centralizer ((MulAut.conj k • A : Subgroup G) : Set G)) =
      Nat.card ↥(D ⊓ Subgroup.centralizer (A : Set G)) := by
  have key : D ⊓ Subgroup.centralizer ((MulAut.conj k • A : Subgroup G) : Set G) =
      MulAut.conj k • (D ⊓ Subgroup.centralizer (A : Set G)) := by
    ext z
    simp only [Subgroup.mem_inf, SetLike.mem_coe, Subgroup.mem_centralizer_iff,
      mem_conj_smul_iff_aux]
    constructor
    · rintro ⟨hz, hc⟩
      refine ⟨hk' z hz, fun a ha => ?_⟩
      have h1 := hc (k * a * k⁻¹) (by rw [show k⁻¹ * (k * a * k⁻¹) * k = a by group]; exact ha)
      calc a * (k⁻¹ * z * k) = k⁻¹ * ((k * a * k⁻¹) * z) * k := by group
        _ = k⁻¹ * (z * (k * a * k⁻¹)) * k := by rw [h1]
        _ = (k⁻¹ * z * k) * a := by group
    · rintro ⟨hz, hc⟩
      refine ⟨?_, fun h hh => ?_⟩
      · simpa [mul_assoc] using hk _ hz
      · have h1 := hc (k⁻¹ * h * k) hh
        calc h * z = k * ((k⁻¹ * h * k) * (k⁻¹ * z * k)) * k⁻¹ := by group
          _ = k * ((k⁻¹ * z * k) * (k⁻¹ * h * k)) * k⁻¹ := by rw [h1]
          _ = z * h := by group
  rw [key]
  exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj k) _).toEquiv).symm

private theorem card_sup_mul_card_inf_aux {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := B2F.relIndex_sup_eq_of_le_normalizer' hA
  have h2 := Subgroup.relIndex_mul_card B (A ⊔ B)
  have h3 := Subgroup.relIndex_mul_card B A
  have h4 : B ⊓ (A ⊔ B) = B := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [← h2, ← h3, inf_comm]
  ring

private theorem le_normalizer_of_forall_mem {Q W : Subgroup G}
    (h : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ ∈ W) : Q ≤ Subgroup.normalizer (W : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h q hq x, fun hx => ?_⟩
  have := h q⁻¹ (Q.inv_mem hq) _ hx
  simpa [mul_assoc] using this

theorem eleven11_D_eq_mul {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) :
    Q ⊓ centralizerModCore L = blockU L ⊔ (Q ⊓ Subgroup.centralizer (L : Set G)) := by
  classical
  obtain ⟨x, hx, hxD⟩ := eleven11_exists_conj_blockU hd
  obtain ⟨k, hkL, hkjoin⟩ := eleven11_le_join_conj hd h8 hx hxD
  have h := eleven11_transvPair hd h8
  have h' := h.conj hx
  have hne := eleven11_conj_not_le_centralizer hd h8 hx hxD
  have hcent := eleven11_cent_blockU_eq hd h8
  have hkD : ∀ d ∈ Q ⊓ centralizerModCore L, k * d * k⁻¹ ∈ Q ⊓ centralizerModCore L :=
    fun d hdD => eleven11_normalizer_D hd k hkL d hdD
  have hkD' : ∀ d ∈ Q ⊓ centralizerModCore L, k⁻¹ * d * k ∈ Q ⊓ centralizerModCore L :=
    fun d hdD => by simpa using eleven11_normalizer_D hd k⁻¹ (inv_mem hkL) d hdD
  have hE : Nat.card ↥(Q ⊓ centralizerModCore L) =
      4 * Nat.card ↥(Q ⊓ centralizerModCore L ⊓
        Subgroup.centralizer ((MulAut.conj x • blockU L : Subgroup G) : Set G)) := by
    have := h.card_inf_centralizer h' hne
    rwa [hcent] at this
  have hconj : MulAut.conj (k * x) • blockU L = MulAut.conj k • (MulAut.conj x • blockU L) := by
    rw [map_mul, mul_smul]
  have hE' : Nat.card ↥(Q ⊓ centralizerModCore L) =
      4 * Nat.card ↥(Q ⊓ centralizerModCore L ⊓
        Subgroup.centralizer ((MulAut.conj (k * x) • blockU L : Subgroup G) : Set G)) := by
    rw [hconj, card_inf_centralizer_conj_smul hkD hkD']
    exact hE
  have h16 := card_le_sixteen_mul_card_inf inf_le_left inf_le_left hE hE'
  have hEEP : (Q ⊓ centralizerModCore L ⊓
        Subgroup.centralizer ((MulAut.conj x • blockU L : Subgroup G) : Set G)) ⊓
      (Q ⊓ centralizerModCore L ⊓
        Subgroup.centralizer ((MulAut.conj (k * x) • blockU L : Subgroup G) : Set G)) ≤
      Q ⊓ Subgroup.centralizer (L : Set G) := by
    intro z hz
    simp only [Subgroup.mem_inf] at hz
    obtain ⟨⟨⟨hzQ, -⟩, hz1⟩, ⟨-, hz2⟩⟩ := hz
    refine Subgroup.mem_inf.2 ⟨hzQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hsup : MulAut.conj x • blockU L ⊔ MulAut.conj (k * x) • blockU L ≤
        Subgroup.centralizer ({z} : Set G) :=
      sup_le (fun w hw => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hz1 w hw))
        (fun w hw => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hz2 w hw))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hsup (hkjoin hl))
  have hD16 : Nat.card ↥(Q ⊓ centralizerModCore L) ≤
      16 * Nat.card ↥(Q ⊓ Subgroup.centralizer (L : Set G)) :=
    h16.trans (Nat.mul_le_mul_left 16 (Subgroup.card_le_of_le hEEP))
  have hPD : Q ⊓ Subgroup.centralizer (L : Set G) ≤ Q ⊓ centralizerModCore L := by
    intro z hz
    obtain ⟨hzQ, hzC⟩ := Subgroup.mem_inf.1 hz
    refine Subgroup.mem_inf.2 ⟨hzQ, Subgroup.centralizer_le_normalizer _ hzC, fun l hl => ?_⟩
    have hcomm : l * z = z * l := Subgroup.mem_centralizer_iff.1 hzC l hl
    have : z * l * z⁻¹ * l⁻¹ = 1 := by
      rw [← hcomm]
      group
    rw [this]
    exact (oTwoIn L).one_mem
  have hWD : blockU L ≤ Q ⊓ centralizerModCore L :=
    le_inf (eleven11_blockU_le_Q hd)
      ((blockU_le_oTwoIn L).trans (Glue.oTwoIn_le_centralizerModCore L))
  have hZeq : (Q ⊓ Subgroup.centralizer (L : Set G)) ⊓ blockU L = blockZ L := by
    ext z
    simp only [Subgroup.mem_inf, blockZ]
    constructor
    · rintro ⟨⟨_, hc⟩, hw⟩
      exact ⟨hw, hc⟩
    · rintro ⟨hw, hc⟩
      exact ⟨⟨eleven11_blockU_le_Q hd hw, hc⟩, hw⟩
  have hPN : Q ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (blockU L : Set G) :=
    inf_le_left.trans (le_normalizer_of_forall_mem h.normal)
  have hprod := card_sup_mul_card_inf_aux hPN
  rw [hZeq, eleven11_card_blockU hd h8] at hprod
  have hZpos : 0 < Nat.card (blockZ L : Subgroup G) := Nat.card_pos
  have hPW : Nat.card ↥(Q ⊓ Subgroup.centralizer (L : Set G) ⊔ blockU L) =
      16 * Nat.card ↥(Q ⊓ Subgroup.centralizer (L : Set G)) := by
    refine Nat.eq_of_mul_eq_mul_right hZpos ?_
    rw [hprod]
    ring
  have heq : Q ⊓ Subgroup.centralizer (L : Set G) ⊔ blockU L = Q ⊓ centralizerModCore L :=
    Subgroup.eq_of_le_of_card_ge (sup_le hPD hWD) (by rw [hPW]; exact hD16)
  rw [← heq, sup_comm]

theorem eleven11_exists_mul_of_mem_D {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) {d : G}
    (hdD : d ∈ Q ⊓ centralizerModCore L) :
    ∃ w ∈ blockU L, ∃ p ∈ Q ⊓ Subgroup.centralizer (L : Set G), d = w * p := by
  have hd' : d ∈ ((blockU L ⊔ (Q ⊓ Subgroup.centralizer (L : Set G)) : Subgroup G) : Set G) := by
    rw [← eleven11_D_eq_mul hd h8]
    exact hdD
  have hPN : Q ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (blockU L : Set G) :=
    inf_le_left.trans (le_normalizer_of_forall_mem (eleven11_transvPair hd h8).normal)
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hPN] at hd'
  obtain ⟨w, hw, p, hp, hwp⟩ := hd'
  exact ⟨w, hw, p, hp, hwp.symm⟩

theorem eleven11_noExotic {M V Q : Subgroup G} :
    Eleven11NoExotic M V Q := by
  intro U L X hd _ _ h8 q hq
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
  have h78 : IsLTwoBlockType L 2 := (eleven11_blockType_two hd h8).1
  obtain ⟨t, ht, d, hdD, rfl⟩ := eleven_nine_two hd.setting hUΓ hLb hLM h78 q hq
  obtain ⟨w, hw, p, hp, rfl⟩ := eleven11_exists_mul_of_mem_D hd h8 hdD
  refine ⟨t * w, Subgroup.mem_inf.2 ⟨mul_mem (Subgroup.mem_inf.1 ht).1
    (oTwoIn_le L (blockU_le_oTwoIn L hw)), mul_mem (Subgroup.mem_inf.1 ht).2
    (eleven11_blockU_le_Q hd hw)⟩, p, hp, by group⟩

end CFSG.LocalAnalysis.WeakClosure81
