module

public import CFSG.RankThree.PartTwo.Toolkit.Statements
import CFSG.RankThree.PartTwo.Sec13.Item137ProofM12
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Ronan138SNorm
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartTwo.KFacts.KS18M12
public import CFSG.RankThree.PartTwo.Sec13.Item137Tools
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec13.Item13Prod
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SP
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_s_of_m12 (h131 : Item131) (hspor : SporadicModels131)
    (h414 : Sec4.Item4_14_local) (hK18 : KFacts.KS18M12)
    (hM12D : ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) →
      Toolkit.M12ThreeLocalData X)
    {A L E F : Subgroup G} {c : G} (hH : Hyp138 A c L E) (hF : IsF138N L E F)
    {x y : G} (hframe : HeisFrame (E ⊓ F) x y) (hxE : x ∈ E) (hyF : y ∈ F)
    (h81 : Nat.card (E ⊔ F : Subgroup G) = 81) (h9 : Nat.card (E ⊓ F : Subgroup G) = 9)
    {e : G} {K : Subgroup G} (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e)
    (heF : e ∈ F)
    (hφ : Nonempty (lBarA e K E ≃*
      Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12)) :
    ∃ s : G, s ∈ K ∧ s ∈ Subgroup.normalizer ((E ⊔ F : Subgroup G) : Set G) ∧
      s * ⁅x, y⁆ * s⁻¹ = ⁅x, y⁆⁻¹ ∧ s ∉ Subgroup.normalizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := E ⊔ F with hP
  obtain ⟨φ⟩ := hφ
  obtain ⟨h, -, -, hE3, hE27, -, -, hST, -⟩ := hH
  obtain ⟨⟨-, hF3, hF27, -, hFN⟩, -⟩ := hF
  have hXE : E ∈ partTwoE G ∧ E ∉ partTwoT G := by
    rcases hST with hS | hT
    · exact ⟨hS.1, hS.2.1⟩
    · exact ⟨hT.1, hT.2.1⟩
  have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hXF : E ∈ partTwoF G := hFE ▸ hXE.1
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF
      not_mem_partTwoT := hXE.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  have hspor' := hspor
  obtain ⟨-, ⟨hM12p, hM12z⟩, -⟩ := hspor'
  obtain ⟨φK⟩ := nonempty_thetaQuot_equiv hD hM12p φ
  have hKM : Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.M12) :=
    ⟨φK⟩
  obtain ⟨heK, hEK9, ⟨eAut⟩⟩ := facts_of_m12 h131 hspor hD hKM
  have hZK : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    center_eq_bot_of_mulEquiv φK hM12z
  have heE : e ∈ E := hD.mem_A
  have he3 : e ^ 3 = 1 := hE3.2 e heE
  have he1 : e ≠ 1 := hD.ne_one
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) := hD.le_centralizer
  have hKc : ∀ k ∈ K, k * e = e * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKe hk)
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEN' : E ≤ Subgroup.normalizer (F : Set G) :=
    le_sup_left.trans (le_normalizer_of_card le_sup_right hF27 h81)
  have hPNE : P ≤ Subgroup.normalizer (E : Set G) := le_normalizer_of_card le_sup_left hE27 h81
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 4) (by rw [h81]; norm_num)
  have hPexp : ∀ z ∈ P, z ^ 3 = 1 := fun z hz => pow_three_of_mem_sup hFN hEN' hE3 hF3 hz
  have hPe : ∀ z ∈ P, z * e = e * z := by
    have hPC : P ≤ Subgroup.centralizer ({e} : Set G) := sup_le
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hEab a ha e heE))
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hFab a ha e heF))
    exact fun z hz => Subgroup.mem_centralizer_singleton_iff.mp (hPC hz)
  have hEdec : E = Subgroup.zpowers e ⊔ (E ⊓ K) := by
    have hle : Subgroup.zpowers e ⊔ (E ⊓ K) ≤ E :=
      sup_le (Subgroup.zpowers_le.mpr heE) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine he3
      (fun heB : e ∈ E ⊓ K => heK heB.2) le_rfl hEK9
      (fun b hb => hE3.2 b hb.1) (fun b hb => hD.commute hD.mem_A hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hE27, hcard])).symm
  obtain ⟨b, hbEK, hb1⟩ : ∃ b ∈ E ⊓ K, b ≠ 1 := by
    by_contra hall
    push Not at hall
    have : E ⊓ K = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
    rw [this, Subgroup.card_bot] at hEK9
    norm_num at hEK9
  have hPNK : P ≤ Subgroup.normalizer (K : Set G) := fun z hz =>
    mem_normalizer_of_mem_lA hK he3 heK (Subgroup.mem_inf.mp hbEK).1
      (Subgroup.mem_inf.mp hbEK).2 hb1 (hPNE hz) (hPe z hz)
  have hinner : ∀ σ : MulAut (K ⧸ aschbacherSolvableCore 3 K), σ ^ 3 = 1 →
      σ ∈ (MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* _).range := by
    intro σ hσ
    obtain ⟨-, -, hinn, -⟩ := hK18 (K ⧸ aschbacherSolvableCore 3 K) hKM
    obtain ⟨w, hw⟩ := hinn σ ⟨1, by rw [pow_one]; exact hσ⟩
    exact ⟨w, hw.symm⟩
  have hPeK := le_zpowers_sup_of_inner hZK hinner hE3 hXF.2.1 hEdec hKe le_sup_left hP3 hPexp
    hPNK hPe
  have heP : e ∈ P := Subgroup.mem_sup_left heE
  have hPeq : P = Subgroup.zpowers e ⊔ (P ⊓ K) := by
    refine le_antisymm (fun z hz => ?_) (sup_le (Subgroup.zpowers_le.mpr heP) inf_le_left)
    obtain ⟨i, k, hk, rfl⟩ := exists_zpow_mul_of_mem_zpowers_sup hKe (hPeK hz)
    have hkP : k ∈ P := by
      have := P.mul_mem (P.inv_mem (P.zpow_mem heP i)) hz
      rwa [inv_mul_cancel_left] at this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers e i))
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hkP, hk⟩))
  have hPK27 : Nat.card (P ⊓ K : Subgroup G) = 27 := by
    have hcomm : ∀ a ∈ Subgroup.zpowers e, ∀ k ∈ P ⊓ K, a * k = k * a := by
      intro a ha k hk
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (hKc k (Subgroup.mem_inf.mp hk).2).symm j).eq
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    rw [← hPeq, h81, eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans
        (zpowers_inf_eq_bot he3 heK).le), Subgroup.card_bot, mul_one,
      card_zpowers_of_pow_three he3 he1] at hcard
    omega
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 3 K))
  have hS₀ : Nat.card (S₀ : Subgroup K) = 27 := by
    set Qb₀ : Sylow 3 (K ⧸ aschbacherSolvableCore 3 K) :=
      S₀.mapSurjective (QuotientGroup.mk'_surjective _)
    have hQb₀ : (Qb₀ : Subgroup _) =
        (S₀ : Subgroup K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) :=
      Sylow.coe_mapSurjective _ _
    obtain ⟨hHeis₀, -⟩ := h414 _ hKM Qb₀
    rw [← card_map_eq_of_injOn _ (injOn_mk_of_isPGroup Nat.prime_three S₀.isPGroup'), ← hQb₀]
    exact hHeis₀.2.1
  have hSylPK : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ K) K := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card inf_le_right ?_
    rw [hPK27, ← hS₀, Sylow.card_eq_multiplicity]
  obtain ⟨SK, hSK⟩ := hSylPK
  have hS3 : IsPGroup 3 (SK : Subgroup K) := SK.isPGroup'
  have hEKP : E ⊓ K ≤ P ⊓ K := inf_le_inf_right K le_sup_left
  set B : Subgroup K := (E ⊓ K).subgroupOf K with hBdef
  have hBmap : B.map K.subtype = E ⊓ K := by
    rw [hBdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have hBS : B ≤ (SK : Subgroup K) := by
    intro z hz
    have hz' : (z : G) ∈ P ⊓ K := hEKP (Subgroup.mem_subgroupOf.mp hz)
    rw [← hSK] at hz'
    obtain ⟨z', hz'S, hzz⟩ := hz'
    rwa [← Subtype.ext hzz]
  have hB9 : Nat.card B = 9 := by
    rw [← hEK9, ← hBmap, Subgroup.card_map_of_injective K.subtype_injective]
  have hEKp : IsPGroup 3 (E ⊓ K : Subgroup G) := IsPGroup.of_card (n := 2) (by rw [hEK9]; norm_num)
  have hBaut : Nat.card (Sec4.autIn ⊤ (B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)))) =
      6 := by
    obtain ⟨e₁⟩ := nonempty_autIn_zpowers_sup_equiv he3 heK hKc (inf_le_right : E ⊓ K ≤ K) hEKp
    rw [← hEdec] at e₁
    rw [Nat.card_congr (e₁.symm.trans eAut).toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  obtain ⟨Eb, Fb, t₀, ht₀, hinv, -, hncard, -, -, hHeis⟩ :=
    exists_bar_config h414 hM12D hKM SK hBS hB9 hBaut
  have hPeq' : P = Subgroup.zpowers e ⊔ (SK : Subgroup K).map K.subtype := by
    rw [hSK]
    exact hPeq
  refine ⟨(t₀ : G), t₀.2, ?_, ?_, ?_⟩
  · rw [hPeq']
    exact mem_normalizer_zpowers_sup hKc ht₀
  · have hinvP := inv_of_mem_commutator hKc hS3 hHeis ht₀ hinv
    rw [← hPeq'] at hinvP
    exact hinvP _ (Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hxE)
      (Subgroup.mem_sup_right hyF))
  ·
    intro hsE
    have hne : B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) ≠
        conjugate (B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)))
          (QuotientGroup.mk' (aschbacherSolvableCore 3 K) t₀) := by
      intro heq
      have := (ne_of_ncard_eq_four hncard)
      exact this.2.2.2.2.2 heq
    apply hne
    have htB : t₀ ∈ Subgroup.normalizer (B : Set K) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      simp only [hBdef, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.mem_inf]
      constructor
      · rintro ⟨hzE, hzK⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hsE z).mp hzE,
          mul_mem (mul_mem t₀.2 hzK) (inv_mem t₀.2)⟩
      · rintro ⟨hzE, -⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hsE z).mpr hzE, z.2⟩
    have htBbar : QuotientGroup.mk' (aschbacherSolvableCore 3 K) t₀ ∈ Subgroup.normalizer
        ((B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) : Subgroup _) : Set _) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at htB ⊢
      rw [Subgroup.map_map]
      conv_rhs => rw [← htB, Subgroup.map_map]
      congr 1
    exact (KFacts.KS14.conjugate_eq_of_mem_normalizer htBbar).symm

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
