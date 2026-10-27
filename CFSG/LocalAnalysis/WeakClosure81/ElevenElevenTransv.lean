module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenModel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem eleven11_mem_of_comm_mem_blockZ {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) {t : G} (ht : t ∈ L ⊓ Q)
    (ht0 : t ∉ oTwoIn L) {w : G} (hw : w ∈ blockU L) (hc : t * w * t⁻¹ * w⁻¹ ∈ blockZ L) :
    w ∈ ⁅V, X⁆ ⊔ blockZ L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, ψ, p, -, hαk, -, hψk, hψe, hαS, hfix⟩ := eleven11_exists_model hd h8
  have htL : t ∈ L := (Subgroup.mem_inf.1 ht).1
  have htα : α ⟨t, htL⟩ ∈ CFSG.QuasithinUnique.Setup.Campbell.rootGrp p := by
    rw [← hαS]
    exact Subgroup.mem_map_of_mem α (Subgroup.mem_subgroupOf.2 ht)
  have htα1 : α ⟨t, htL⟩ ≠ 1 := by
    intro h
    have hker : (⟨t, htL⟩ : ↥L) ∈ α.ker := h
    rw [hαk, Subgroup.mem_subgroupOf] at hker
    exact ht0 hker
  have htw : t * w * t⁻¹ ∈ blockU L := conj_mem_blockU (Subgroup.le_normalizer htL) hw
  have hψtw : Multiplicative.toAdd (ψ ⟨t * w * t⁻¹, htw⟩) =
      (α ⟨t, htL⟩) • Multiplicative.toAdd (ψ ⟨w, hw⟩) := by
    have := congrArg Multiplicative.toAdd (hψe ⟨t, htL⟩ ⟨w, hw⟩ htw)
    simpa [Matrix.SpecialLinearGroup.smul_def] using this
  have hker : (⟨t * w * t⁻¹ * w⁻¹, hc.1⟩ : ↥(blockU L)) ∈ ψ.ker := by
    rw [hψk, Subgroup.mem_subgroupOf]
    exact hc
  have hc1 : ψ ⟨t * w * t⁻¹, htw⟩ = ψ ⟨w, hw⟩ := by
    have h1 : ψ ⟨t * w * t⁻¹, htw⟩ * (ψ ⟨w, hw⟩)⁻¹ = 1 := by
      have : (⟨t * w * t⁻¹ * w⁻¹, hc.1⟩ : ↥(blockU L)) =
          ⟨t * w * t⁻¹, htw⟩ * (⟨w, hw⟩ : ↥(blockU L))⁻¹ := rfl
      rw [← map_inv, ← map_mul, ← this]
      exact hker
    exact mul_inv_eq_one.1 h1
  have hfixed : (α ⟨t, htL⟩) • Multiplicative.toAdd (ψ ⟨w, hw⟩) =
      Multiplicative.toAdd (ψ ⟨w, hw⟩) := by
    rw [← hψtw, hc1]
  have hmem := (CFSG.QuasithinUnique.Setup.Campbell.smul_eq_self_iff_mem_of_mem_rootGrp htα htα1
    _).1 hfixed
  obtain ⟨u, huV, hu⟩ := (hfix _).2 hmem
  have huW : (u : G) ∈ blockU L := u.2
  have hwu : w * (u : G)⁻¹ ∈ blockZ L := by
    have hk : ψ (⟨w, hw⟩ * u⁻¹) = 1 := by
      rw [map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      simp [hu]
    have hk' : (⟨w, hw⟩ * u⁻¹ : ↥(blockU L)) ∈ ψ.ker := hk
    rw [hψk, Subgroup.mem_subgroupOf] at hk'
    exact hk'
  rw [← eleven11_inf_blockU_sup_blockZ hd h8]
  have : w = (w * (u : G)⁻¹) * (u : G) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hwu)
    (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨huV, huW⟩))

theorem eleven11_blockU_inf_centralizer {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) {t : G} (ht : t ∈ L ⊓ Q)
    (ht0 : t ∉ oTwoIn L) :
    blockU L ⊓ Subgroup.centralizer ({t} : Set G) = ⁅V, X⁆ ⊔ blockZ L := by
  classical
  refine le_antisymm ?_ ?_
  · intro w hw
    obtain ⟨hwW, hwC⟩ := Subgroup.mem_inf.1 hw
    have h1 : w * t = t * w := Subgroup.mem_centralizer_singleton_iff.1 hwC
    have hcomm : t * w * t⁻¹ * w⁻¹ ∈ blockZ L := by
      have : t * w * t⁻¹ * w⁻¹ = 1 := by
        rw [← h1]
        group
      rw [this]
      exact (blockZ L).one_mem
    exact eleven11_mem_of_comm_mem_blockZ hd h8 ht ht0 hwW hcomm
  · have hVQ : V ≤ Subgroup.centralizer (Q : Set G) :=
      eleven_a (hd.setting.sylowQ.1.trans inf_le_right)
    have htL : t ∈ L := (Subgroup.mem_inf.1 ht).1
    have htQ : t ∈ Q := (Subgroup.mem_inf.1 ht).2
    obtain ⟨hle, -, -, -, -⟩ := eleven11_commutator_VX hd h8
    refine le_inf (sup_le (hle.trans inf_le_right) (blockZ_le_blockU L)) (sup_le ?_ ?_)
    · intro v hv
      have hvV : v ∈ V := (Subgroup.mem_inf.1 (hle hv)).1
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 (hVQ hvV) t htQ).symm
    · intro z hz
      have hzC : z ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.1 hz).2
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hzC t htL).symm

theorem eleven11_card_blockU_eq_four_mul {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) :
    Nat.card (blockU L : Subgroup G) = 4 * Nat.card (⁅V, X⁆ ⊔ blockZ L : Subgroup G) := by
  obtain ⟨hle, hcard, hZ, -, -⟩ := eleven11_commutator_VX hd h8
  have h16 := eleven11_card_blockU hd h8
  have hWab := eleven11_blockU_comm hd
  have hcomm : ∀ a ∈ ⁅V, X⁆, ∀ b ∈ blockZ L, a * b = b * a := fun a ha b hb =>
    hWab a (Subgroup.mem_inf.1 (hle ha)).2 b (blockZ_le_blockU L hb)
  have hmul := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [hZ, Subgroup.card_bot, mul_one, hcard] at hmul
  omega

end CFSG.LocalAnalysis.WeakClosure81
