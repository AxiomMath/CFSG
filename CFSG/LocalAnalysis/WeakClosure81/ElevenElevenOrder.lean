module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenCent
public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenDecomp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem eleven11_D_eq_sup {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X)
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3) (h8 : Nat.card V = 8) :
    Q ⊓ centralizerModCore L = blockU L ⊔ U := by
  rw [eleven11_D_eq_mul hd h8, eleven11_cent_eq hd h21 h3 h8]

theorem eleven11_card_D {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X)
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3) (h8 : Nat.card V = 8) :
    Nat.card (Q ⊓ centralizerModCore L : Subgroup G) = 32 ∧ Nat.card Q = 128 := by
  have hUC : U ≤ Subgroup.centralizer (L : Set G) :=
    (eleven11_U_le_cent hd).trans inf_le_right
  have hWL : blockU L ≤ L := (blockU_le_oTwoIn L).trans (oTwoIn_le L)
  have hcomm : ∀ a ∈ blockU L, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (hUC hb) a (hWL ha)
  have hinf : blockU L ⊓ U = blockZ L := by
    refine le_antisymm ?_ (le_inf (blockZ_le_blockU L) (eleven11_blockZ_le hd h21 h3 h8))
    intro x hx
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, hUC (Subgroup.mem_inf.1 hx).2⟩
  have hmul := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [hinf, eleven11_card_blockU hd h8, eleven11_card_U hd h8] at hmul
  have hpos : 0 < Nat.card (blockZ L : Subgroup G) := Nat.card_pos
  have h32 : Nat.card (blockU L ⊔ U : Subgroup G) = 32 := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hmul]
    ring
  rw [← eleven11_D_eq_sup hd h21 h3 h8] at h32
  refine ⟨h32, ?_⟩
  rw [eleven11_card_Q hd h8, h32]

theorem eleven11_V_le_D {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X)
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3) (h8 : Nat.card V = 8) :
    V ≤ Q ⊓ centralizerModCore L := by
  obtain ⟨hle, -, -, hV, -⟩ := eleven11_commutator_VX hd h8
  rw [eleven11_D_eq_sup hd h21 h3 h8]
  conv_lhs => rw [hV]
  exact sup_le le_sup_right ((hle.trans inf_le_right).trans le_sup_left)

theorem eleven11_D_comm {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X)
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3) (h8 : Nat.card V = 8) :
    ∀ x ∈ Q ⊓ centralizerModCore L, ∀ y ∈ Q ⊓ centralizerModCore L, x * y = y * x := by
  have hUC : U ≤ Subgroup.centralizer (L : Set G) :=
    (eleven11_U_le_cent hd).trans inf_le_right
  have hWL : blockU L ≤ L := (blockU_le_oTwoIn L).trans (oTwoIn_le L)
  have hWU : ∀ a ∈ blockU L, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (hUC hb) a (hWL ha)
  have hUV : U ≤ V := (deltaEleven_subset_gammaEleven M V hd.mem_delta).1
  have hVC : V ≤ Subgroup.centralizer (Q : Set G) :=
    eleven_a (hd.setting.sylowQ.1.trans inf_le_right)
  have hUU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (hVC (hUV ha)) b (hd.setting.V_le_Q (hUV hb))).symm
  intro x hx y hy
  rw [eleven11_D_eq_sup hd h21 h3 h8] at hx hy
  obtain ⟨w, hw, a, ha, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute_elementwise hWU hx
  obtain ⟨w', hw', a', ha', rfl⟩ := exists_mul_eq_of_mem_sup_of_commute_elementwise hWU hy
  have h1 : w * a * (w' * a') = w * w' * (a * a') :=
    (show Commute a w' from (hWU w' hw' a ha).symm).mul_mul_mul_comm w a'
  have h2 : w' * a' * (w * a) = w' * w * (a' * a) :=
    (show Commute a' w from (hWU w hw a' ha').symm).mul_mul_mul_comm w' a
  rw [h1, h2, eleven11_blockU_comm hd w hw w' hw', hUU a ha a' ha']

theorem eleven11_D_ne {M V Q U L X U' L' X' : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (hd' : Eleven11Data M V Q U' L' X')
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3)
    (h3' : Nat.card (autI hd.setting.isElemAbelian X') = 3) (h8 : Nat.card V = 8)
    (hne : U ≠ U') :
    Q ⊓ centralizerModCore L ≠ Q ⊓ centralizerModCore L' := by
  intro hDD
  have hcard := (eleven11_card_D hd h21 h3 h8).1
  have hE : (Q ⊓ centralizerModCore L : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hE2 : IsPGroup 2 (Q ⊓ centralizerModCore L : Subgroup G) :=
    hd.setting.sylowQ.2.1.to_le inf_le_left
  have hLN : L ≤ Subgroup.normalizer ((Q ⊓ centralizerModCore L : Subgroup G) : Set G) := by
    intro l hl
    refine Subgroup.mem_normalizer_fintype fun d hdD => ?_
    exact eleven11_normalizer_D hd l hl d hdD
  have hLN' : L' ≤ Subgroup.normalizer ((Q ⊓ centralizerModCore L : Subgroup G) : Set G) := by
    rw [hDD]
    intro l hl
    refine Subgroup.mem_normalizer_fintype fun d hdD => ?_
    exact eleven11_normalizer_D hd' l hl d hdD
  have hUC : U ≤ Subgroup.centralizer (L : Set G) :=
    (eleven11_U_le_cent hd).trans inf_le_right
  have hUV : U ≤ V := (deltaEleven_subset_gammaEleven M V hd.mem_delta).1
  have hCN : M ⊓ Subgroup.centralizer (V : Set G) ≤
      Subgroup.normalizer ((Q ⊓ centralizerModCore L : Subgroup G) : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun d hdD => ?_
    obtain ⟨w, hw, p, hp, rfl⟩ := eleven11_exists_mul_of_mem_D hd h8 hdD
    have hpU : p ∈ U := by
      rw [eleven11_cent_eq hd h21 h3 h8] at hp
      exact hp
    have hgN : g ∈ Subgroup.normalizer (L : Set G) :=
      eleven11_cent_le_normalizer hd hg
    have hcomm : g * p = p * g :=
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2 p (hUV hpU)).symm
    have hpg' : p * g⁻¹ = g⁻¹ * p := by
      calc p * g⁻¹ = g⁻¹ * (g * p) * g⁻¹ := by group
        _ = g⁻¹ * (p * g) * g⁻¹ := by rw [hcomm]
        _ = g⁻¹ * p := by group
    have hgN : g ∈ Subgroup.normalizer (L : Set G) :=
      eleven11_cent_le_normalizer hd hg
    have hWD : blockU L ⊔ U = Q ⊓ centralizerModCore L :=
      (eleven11_D_eq_sup hd h21 h3 h8).symm
    have hmem : g * w * g⁻¹ * p ∈ blockU L ⊔ U :=
      (blockU L ⊔ U).mul_mem (Subgroup.mem_sup_left (conj_mem_blockU hgN hw))
        (Subgroup.mem_sup_right hpU)
    rw [hWD] at hmem
    have e : g * (w * p) * g⁻¹ = g * w * g⁻¹ * p := by
      calc g * (w * p) * g⁻¹ = g * w * (p * g⁻¹) := by group
        _ = g * w * (g⁻¹ * p) := by rw [hpg']
        _ = g * w * g⁻¹ * p := by group
    rw [e]
    exact hmem
  exact eleven11_false_of_normalized_join hd hd' h21 h3 h3' hne hE hE2 hLN hLN' hCN

theorem eleven11_D_inf_D {M V Q U L X U' L' X' : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (hd' : Eleven11Data M V Q U' L' X')
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3)
    (h3' : Nat.card (autI hd.setting.isElemAbelian X') = 3) (h8 : Nat.card V = 8)
    (hne : U ≠ U') :
    (Q ⊓ centralizerModCore L) ⊓ (Q ⊓ centralizerModCore L') = V := by
  refine le_antisymm ?_
    (le_inf (eleven11_V_le_D hd h21 h3 h8) (eleven11_V_le_D hd' h21 h3' h8))
  have hDne := eleven11_D_ne hd hd' h21 h3 h3' h8 hne
  have hc := (eleven11_card_D hd h21 h3 h8).1
  have hc' := (eleven11_card_D hd' h21 h3' h8).1
  have hnle : ¬ (Q ⊓ centralizerModCore L' : Subgroup G) ≤ Q ⊓ centralizerModCore L := by
    intro h
    exact hDne (Subgroup.eq_of_le_of_card_ge h (le_of_eq (by rw [hc, hc']))).symm
  obtain ⟨e, heD', heD⟩ := SetLike.not_le_iff_exists.1 hnle
  have heQ : e ∈ Q := (Subgroup.mem_inf.1 heD').1
  have heC : e ∉ centralizerModCore L := fun h => heD (Subgroup.mem_inf.2 ⟨heQ, h⟩)
  have hWe := eleven11_blockU_inf_centralizer_of_mem hd h8 heQ heC
  have hUV : U ≤ V := (deltaEleven_subset_gammaEleven M V hd.mem_delta).1
  have hVC : V ≤ Subgroup.centralizer (Q : Set G) :=
    eleven_a (hd.setting.sylowQ.1.trans inf_le_right)
  have hVsub : ⁅V, X⁆ ⊔ blockZ L ≤ V :=
    sup_le ((eleven11_commutator_VX hd h8).1.trans inf_le_left)
      ((eleven11_blockZ_le hd h21 h3 h8).trans hUV)
  intro x hx
  obtain ⟨hxD, hxD'⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨w, hw, p, hp, rfl⟩ := eleven11_exists_mul_of_mem_D hd h8 hxD
  have hpU : p ∈ U := by
    rw [eleven11_cent_eq hd h21 h3 h8] at hp
    exact hp
  have hpe : p * e = e * p :=
    (Subgroup.mem_centralizer_iff.1 (hVC (hUV hpU)) e heQ).symm
  have hxe : w * p * e = e * (w * p) :=
    eleven11_D_comm hd' h21 h3' h8 (w * p) hxD' e heD'
  have hwe : w * e = e * w := by
    have h1 : w * (e * p) = (e * w) * p := by
      calc w * (e * p) = w * (p * e) := by rw [hpe]
        _ = w * p * e := (mul_assoc _ _ _).symm
        _ = e * (w * p) := hxe
        _ = e * w * p := (mul_assoc _ _ _).symm
    rw [← mul_assoc] at h1
    exact mul_right_cancel h1
  have hwV : w ∈ V := by
    have hmem : w ∈ blockU L ⊓ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_inf.2 ⟨hw, Subgroup.mem_centralizer_singleton_iff.2 hwe⟩
    rw [hWe] at hmem
    exact hVsub hmem
  exact V.mul_mem hwV (hUV hpU)

end CFSG.LocalAnalysis.WeakClosure81
