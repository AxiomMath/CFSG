module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenBlock

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem eleven11_blockType_two {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) :
    IsLTwoBlockType L 2 ∧ rMV M V = 2 := by
  obtain ⟨n, hn, h78, hr, -⟩ := hd.ten
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hd.setting.isElemAbelian
  have hcard : Nat.card V = 2 ^ E3.mQuot V U * Nat.card U := E3.card_eq_two_pow_mul hVpg hUΓ.1
  rw [h8, eleven11_card_U hd h8] at hcard
  have hm : E3.mQuot V U = 2 := by
    have h4 : 2 ^ E3.mQuot V U = 4 := by omega
    have h22 : (2 : ℕ) ^ E3.mQuot V U = 2 ^ 2 := by rw [h4]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h22
  have hq : (E3.mQuot V U : ℕ∞) = rMV M V := hd.mem_delta.2
  rw [hm] at hq
  have hr2 : rMV M V = 2 := by rw [← hq]; norm_num
  have hn2 : n = 2 := by
    rw [hr2] at hr
    exact_mod_cast hr.symm
  subst hn2
  exact ⟨h78, hr2⟩

theorem eleven11_commutator_VX {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) :
    ⁅V, X⁆ ≤ V ⊓ blockU L ∧ Nat.card (⁅V, X⁆ : Subgroup G) = 4 ∧ ⁅V, X⁆ ⊓ blockZ L = ⊥ ∧
      V = U ⊔ ⁅V, X⁆ ∧ U ⊓ ⁅V, X⁆ = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h78 : IsLTwoBlockType L 2 := (eleven11_blockType_two hd h8).1
  obtain ⟨n, -, -, -, -, hD⟩ := hd.ten
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
  have hUV : U ≤ V := hUΓ.1
  have hVcm : V ≤ centralizerModCore L :=
    eleven_nine_V_le_centralizerModCore hd.setting hUΓ hLb h78
  have hVcomm : ∀ v' ∈ V, ∀ l ∈ L, v' * l * v'⁻¹ * l⁻¹ ∈ blockU L := fun v' hv' l hl =>
    ((ThmOne.mem_centralizerModCore_iff_blockU hLb.2.2.1.residual_eq).mp (hVcm hv')).2 l hl
  have hXM : X ≤ M := fun x hx => (hd.isHall.1 hx).2
  have hXL : X ≤ L := fun x hx => (hd.isHall.1 hx).1
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := fun x hx => hd.setting.normal (hXM hx)
  have hcomm_le : ⁅V, X⁆ ≤ V ⊓ blockU L := by
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_le]
      intro v hv d hd'
      have hdv : d * v * d⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hXN hd') v).mp hv
      rw [show ⁅v, d⁆ = v * (d * v * d⁻¹)⁻¹ from by group]
      exact V.mul_mem hv (V.inv_mem hdv)
    · rw [Subgroup.commutator_le]
      intro v hv d hd'
      have := hVcomm v hv d (hXL hd')
      rwa [commutatorElement_def]
  have hcard : Nat.card (⁅V, X⁆ : Subgroup G) = 4 := by
    have := eleven_nine_card_commutator_hall hd.setting hUΓ hLb hLM h78 hd.isHall
    simpa using this
  have hZ : ⁅V, X⁆ ⊓ blockZ L = ⊥ :=
    eleven_nine_commutator_inf_blockZ_eq_bot hd.setting hUΓ hLb hLM h78 hd.isHall
  have hXU : V ⊓ Subgroup.centralizer (X : Set G) = U := (hD X hd.isHall).2.2.1
  have hVsup : V = U ⊔ ⁅V, X⁆ := by
    refine le_antisymm ?_ (sup_le hUV (hcomm_le.trans inf_le_left))
    have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hd.setting.isElemAbelian
    have hcop : Nat.Coprime (Nat.card X) (Nat.card V) := by
      obtain ⟨k, hk⟩ := hVpg.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hd.isHall.2.1.not_two_dvd_nat).symm
    have hsolv : Group.IsSolvable ↥V := isSolvable_of_comm (fun a b =>
      Subtype.ext (B2F.isElemAbelian_comm hd.setting.isElemAbelian a.2 b.2))
    calc V ≤ ⁅V, X⁆ ⊔ V ⊓ Subgroup.centralizer (X : Set G) :=
          CFSG.AGLEmbedding.le_commutator_sup_inf_centralizer_of_coprime hXN hcop hsolv
      _ = U ⊔ ⁅V, X⁆ := by rw [hXU, sup_comm]
  have hVab := hd.setting.isElemAbelian.1
  have hUcomm : ∀ a ∈ U, ∀ b ∈ ⁅V, X⁆, a * b = b * a := fun a ha b hb =>
    setLike_mul_comm (hUV ha) (hcomm_le.trans inf_le_left hb)
  have hinf : U ⊓ ⁅V, X⁆ = ⊥ := by
    have hmul := B2F.card_sup_mul_card_inf_of_commute hUcomm
    rw [← hVsup, h8, eleven11_card_U hd h8, hcard] at hmul
    have h1 : Nat.card (U ⊓ ⁅V, X⁆ : Subgroup G) = 1 := by omega
    exact Subgroup.card_eq_one.1 h1
  exact ⟨hcomm_le, hcard, hZ, hVsup, hinf⟩

private theorem mem_sup_of_commute_aux {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  have key : ∀ a ∈ A, ∀ h ∈ B, a * h * a⁻¹ ∈ B := by
    intro a ha h hh
    rw [hAB a ha h hh, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  have hle : A ≤ normalizer (B : Set G) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key a ha h hh, fun hh => ?_⟩
    have h2 := key a⁻¹ (A.inv_mem ha) _ hh
    have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rwa [e] at h2
  have := Subgroup.coe_mul_of_left_le_normalizer_right A B hle
  have hg' : g ∈ ((A ⊔ B : Subgroup G) : Set G) := hg
  rw [this] at hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := hg'
  exact ⟨a, ha, b, hb, rfl⟩

theorem eleven11_inf_blockU_sup_blockZ {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) :
    (V ⊓ blockU L) ⊔ blockZ L = ⁅V, X⁆ ⊔ blockZ L := by
  obtain ⟨hle, -, -, hVsup, -⟩ := eleven11_commutator_VX hd h8
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hUV : U ≤ V := hUΓ.1
  refine le_antisymm ?_ (sup_le_sup_right hle _)
  refine sup_le ?_ le_sup_right
  intro v hv
  have hvV : v ∈ V := (Subgroup.mem_inf.1 hv).1
  have hvW : v ∈ blockU L := (Subgroup.mem_inf.1 hv).2
  have hvsup : v ∈ U ⊔ ⁅V, X⁆ := hVsup ▸ hvV
  have hVab := hd.setting.isElemAbelian.1
  have hUcomm : ∀ a ∈ U, ∀ b ∈ ⁅V, X⁆, a * b = b * a := fun a ha b hb =>
    setLike_mul_comm (hUV ha) ((hle.trans inf_le_left) hb)
  obtain ⟨u, hu, l, hl, rfl⟩ := mem_sup_of_commute_aux hUcomm hvsup
  have hlW : l ∈ blockU L := (hle hl).2
  have huW : u ∈ blockU L := by
    have := (blockU L).mul_mem hvW ((blockU L).inv_mem hlW)
    simpa using this
  have huC : u ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.1 (hLb.1 hg) u hu).symm
  have huZ : u ∈ blockZ L := ⟨huW, huC⟩
  exact (⁅V, X⁆ ⊔ blockZ L).mul_mem ((le_sup_right : blockZ L ≤ ⁅V, X⁆ ⊔ blockZ L) huZ)
    ((le_sup_left : ⁅V, X⁆ ≤ ⁅V, X⁆ ⊔ blockZ L) hl)

end CFSG.LocalAnalysis.WeakClosure81
