module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenCenter

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem eleven11_U_le_cent {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) : U ≤ Q ⊓ Subgroup.centralizer (L : Set G) := by
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  intro u hu
  refine Subgroup.mem_inf.2 ⟨hd.setting.V_le_Q (hUΓ.1 hu), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_iff.1 (hLb.1 hl) u hu).symm

theorem eleven11_blockZ_le {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X)
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3) (h8 : Nat.card V = 8) :
    blockZ L ≤ U := by
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  intro z hz
  have hzW : z ∈ blockU L := blockZ_le_blockU L hz
  have hzQ : z ∈ Q := eleven11_blockU_le_Q hd hzW
  have hzC : z ∈ Subgroup.centralizer (L : Set G) := hz.2
  have hzL : z ∈ L := oTwoIn_le L (blockU_le_oTwoIn L hzW)
  have hcent : ∀ q ∈ Q, q * z = z * q := by
    intro q hq
    obtain ⟨t, ht, p, hp, rfl⟩ := eleven11_noExotic _ _ _ hd h21 h3 h8 q hq
    have h1 : t * z = z * t := Subgroup.mem_centralizer_iff.1 hzC t (Subgroup.mem_inf.1 ht).1
    have h2 : z * p = p * z := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hp).2 z hzL
    calc t * p * z = t * (p * z) := mul_assoc _ _ _
      _ = t * (z * p) := by rw [h2]
      _ = (t * z) * p := (mul_assoc _ _ _).symm
      _ = (z * t) * p := by rw [h1]
      _ = z * (t * p) := mul_assoc _ _ _
  have hz2 : z ^ 2 = 1 := ThmOne.pow_two_eq_one_of_mem_blockU hLb.2.2.1 hzW
  have hzV : z ∈ V := eleven11_central_involution_mem hd h21 h3 h8 hzQ hcent hz2
  exact eleven11_inf_centralizer_le hd (Subgroup.mem_inf.2 ⟨hzV, hzC⟩)

theorem eleven11_cent_le_D
    {M V Q U L X U' L' X' : Subgroup G} (hd : Eleven11Data M V Q U L X)
    (hd' : Eleven11Data M V Q U' L' X')
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3) (h8 : Nat.card V = 8) :
    Q ⊓ Subgroup.centralizer (L' : Set G) ≤ Q ⊓ centralizerModCore L := by
  by_contra hcon
  have hND : ¬ (Q ⊓ Subgroup.centralizer (L' : Set G)) ≤ centralizerModCore L :=
    fun h => hcon (le_inf inf_le_left h)
  obtain ⟨t, ht, ht0, hcomm⟩ :=
    eleven11_lemmaK hd h8 inf_le_left (eleven11_cent_normalized hd') hND
  have hle := eleven11_commutator_zpowers_le_line hd h8 ht ht0
  have hUV : U ≤ V := (deltaEleven_subset_gammaEleven M V hd.mem_delta).1
  have hVsub : ⁅V, X⁆ ⊔ blockZ L ≤ V :=
    sup_le ((eleven11_commutator_VX hd h8).1.trans inf_le_left)
      ((eleven11_blockZ_le hd h21 h3 h8).trans hUV)
  have hsub : ⁅Subgroup.zpowers t, blockU L⁆ ≤ U' := fun x hx =>
    eleven11_inf_centralizer_le hd'
      (Subgroup.mem_inf.2 ⟨hVsub (hle hx), (Subgroup.mem_inf.1 (hcomm hx)).2⟩)
  have hcard := Subgroup.card_le_of_le hsub
  rw [eleven11_card_commutator_zpowers hd h8 ht ht0, eleven11_card_U hd' h8] at hcard
  omega

theorem eleven11_cent_eq {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X)
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3) (h8 : Nat.card V = 8) :
    Q ⊓ Subgroup.centralizer (L : Set G) = U := by
  refine le_antisymm ?_ (eleven11_U_le_cent hd)
  obtain ⟨A, L', X', hfam, hdist⟩ := eleven11_exists_family hd h21 h3 h8
  choose hd' h3' using hfam
  obtain ⟨i, hi⟩ : ∃ i : Fin 7, A i ≠ U := by
    by_cases h : A 0 = U
    · exact ⟨1, fun h1 => hdist 0 1 (by decide) (h.trans h1.symm)⟩
    · exact ⟨0, h⟩
  have hne : U ≠ A i := fun h => hi h.symm
  have hPD : Q ⊓ Subgroup.centralizer (L : Set G) ≤ Q ⊓ centralizerModCore (L' i) :=
    eleven11_cent_le_D (hd' i) hd h21 (h3' i) h8
  have hTI := eleven11_cent_inf_cent_eq_bot hd (hd' i) h21 h3 (h3' i) hne
  have hLb' : IsBlockOfInX (Subgroup.centralizer (A i : Set G)) (L' i) :=
    isBlockOfInX_of_mem_elevenBlocksB (hd' i).setting
      (deltaEleven_subset_gammaEleven M V (hd' i).mem_delta) (hd' i).mem_blocks
  have hexp : ∀ p ∈ Q ⊓ Subgroup.centralizer (L : Set G), p ^ 2 = 1 := by
    intro p hp
    obtain ⟨w, hw, q', hq', hpwq⟩ := eleven11_exists_mul_of_mem_D (hd' i) h8 (hPD hp)
    have hwL : w ∈ L' i := oTwoIn_le _ (blockU_le_oTwoIn _ hw)
    have hcomm : w * q' = q' * w :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hq').2 w hwL
    have hw2 : w ^ 2 = 1 := ThmOne.pow_two_eq_one_of_mem_blockU hLb'.2.2.1 hw
    have hsq : p ^ 2 = q' ^ 2 := by
      rw [hpwq, (show Commute w q' from hcomm).mul_pow, hw2, one_mul]
    have hmem : p ^ 2 ∈ (Q ⊓ Subgroup.centralizer (L : Set G)) ⊓
        (Q ⊓ Subgroup.centralizer (L' i : Set G)) :=
      Subgroup.mem_inf.2 ⟨pow_mem hp 2, hsq ▸ pow_mem hq' 2⟩
    rw [hTI] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hab : ∀ p ∈ Q ⊓ Subgroup.centralizer (L : Set G),
      ∀ p' ∈ Q ⊓ Subgroup.centralizer (L : Set G), p * p' = p' * p := by
    intro p hp p' hp'
    have e1 : p⁻¹ = p := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hexp p hp)
    have e2 : p'⁻¹ = p' := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hexp p' hp')
    have e3 : (p * p')⁻¹ = p * p' := inv_eq_of_mul_eq_one_right
      (by simpa [pow_two] using hexp (p * p') (mul_mem hp hp'))
    calc p * p' = (p * p')⁻¹ := e3.symm
      _ = p'⁻¹ * p⁻¹ := mul_inv_rev p p'
      _ = p' * p := by rw [e1, e2]
  intro p hp
  have hcent : ∀ q ∈ Q, q * p = p * q := by
    intro q hq
    obtain ⟨t, ht, p', hp', rfl⟩ := eleven11_noExotic _ _ _ hd h21 h3 h8 q hq
    have h1 : t * p = p * t :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hp).2 t (Subgroup.mem_inf.1 ht).1
    have h2 : p' * p = p * p' := hab p' hp' p hp
    calc t * p' * p = t * (p' * p) := mul_assoc _ _ _
      _ = t * (p * p') := by rw [h2]
      _ = (t * p) * p' := (mul_assoc _ _ _).symm
      _ = (p * t) * p' := by rw [h1]
      _ = p * (t * p') := mul_assoc _ _ _
  have hpV : p ∈ V :=
    eleven11_central_involution_mem hd h21 h3 h8 (Subgroup.mem_inf.1 hp).1 hcent (hexp p hp)
  exact eleven11_inf_centralizer_le hd (Subgroup.mem_inf.2 ⟨hpV, (Subgroup.mem_inf.1 hp).2⟩)

end CFSG.LocalAnalysis.WeakClosure81
