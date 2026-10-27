module

public import CFSG.RankThree.PartTwo.Sec8.Item84PairProofSU3
import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
import CFSG.RankThree.PartTwo.Sec6.Item65Tools

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item84Pair

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open scoped MatrixGroups

@[expose] def fixSubgroup {M : Type*} [Group M] (α : MulAut M) : Subgroup M where
  carrier := {z | α z = z}
  mul_mem' {u v} hu hv := by
    change α (u * v) = u * v
    rw [map_mul, show α u = u from hu, show α v = v from hv]
  one_mem' := map_one α
  inv_mem' {u} hu := by
    change α u⁻¹ = u⁻¹
    rw [map_inv, show α u = u from hu]

theorem exists_involution_of_two_dvd {M : Type*} [Group M] [Finite M] {S : Subgroup M}
    (h2 : 2 ∣ Nat.card S) : ∃ z ∈ S, z ≠ 1 ∧ z ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 h2
  refine ⟨z, z.2, fun h1 => ?_, ?_⟩
  · have : z = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz
    norm_num at hz
  · have h := pow_orderOf_eq_one z
    rw [hz] at h
    exact congrArg Subtype.val h

theorem two_dvd_card_of_map {M N : Type*} [Group M] [Group N] (e : M ≃* N) {T : Subgroup M}
    {S : Subgroup N} (hS : T.map e.toMonoidHom = S) (h2 : 2 ∣ Nat.card T) : 2 ∣ Nat.card S := by
  rw [← hS, Subgroup.card_map_of_injective e.injective]
  exact h2

section ModTheta

variable {G : Type} [Group G] [Finite G]

theorem eq_sup_of_imageModTheta_eq_top {X K : Subgroup G} (hKX : K ≤ X)
    (h : imageModTheta X K = ⊤) : X = K ⊔ inSubgroup (aschbacherSolvableCore 3) X := by
  refine le_antisymm (fun x hx => ?_) (sup_le hKX (Subgroup.map_subtype_le _))
  have hmem : QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨x, hx⟩ ∈ imageModTheta X K := by
    rw [h]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, hkx⟩ := hmem
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkx
  have hx' : x = (k : G) * ((k⁻¹ * ⟨x, hx⟩ : X) : G) := by simp
  rw [hx']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
    (Subgroup.mem_sup_right ⟨_, hkx, rfl⟩)

theorem card_quot_dvd_card_imageModTheta {X K : Subgroup G} (hKX : K ≤ X) :
    Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ Nat.card (imageModTheta X K) := by
  obtain ⟨-, -, -, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  set ρ := Item87Proof.modThetaOnto hKX with hρ
  have hρs : Function.Surjective ρ := Item87Proof.modThetaOnto_surjective hKX
  have hkθ : ρ.ker ≤ aschbacherSolvableCore 3 K :=
    hθmax _ (MonoidHom.normal_ker ρ) (Item87Proof.isSolvable_ker_modThetaOnto hKX)
      (Item87Proof.not_three_dvd_card_ker_modThetaOnto hKX)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 K)
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).toEquiv] at h1
  obtain ⟨t, ht⟩ := (Subgroup.card_dvd_of_le hkθ)
  have hpos : 0 < Nat.card ρ.ker := Nat.card_pos
  refine ⟨t, ?_⟩
  have h3 : Nat.card (imageModTheta X K) * Nat.card ρ.ker =
      Nat.card (K ⧸ aschbacherSolvableCore 3 K) * t * Nat.card ρ.ker := by
    rw [← h1, h2, ht]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h3

end ModTheta

theorem nine_dvd_two_pow_sq_sub_one (n : ℕ) : 9 ∣ (2 ^ (3 * n)) ^ 2 - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow 64 1 n
  rw [one_pow] at h
  have e : (2 ^ (3 * n)) ^ 2 = 64 ^ n := by
    rw [← pow_mul, show 3 * n * 2 = 6 * n by ring, pow_mul]
    norm_num
  rw [e]
  exact (show (9 : ℕ) ∣ 64 - 1 by norm_num).trans h

theorem center_eq_bot_of_isSimpleGroup {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (h : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases (Subgroup.center Q).normal_of_characteristic.eq_bot_or_eq_top with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    exact hab (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top a) b).symm

section Fix

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {x : G}

theorem kf_unitary_fix (hxN : x ∈ Subgroup.normalizer (X : Set G)) (hx3 : x ^ 3 = 1) {m : ℕ}
    (hm : 2 ≤ m) (hU : IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m)
    (hk : ¬ (KFacts.InducesStdKind X x .field ∨ KFacts.InducesStdKind X x .graphField))
    (h2 : 2 ∣ Nat.card (barCentralizer (Subgroup.zpowers x) X))
    (hne : barCentralizer (Subgroup.zpowers x) X ≠ ⊤) :
    Odd m ∧ Nonempty (imageModTheta X (inSubgroup perfectResidual
      (X ⊓ Subgroup.centralizer ({x} : Set G))) ≃* projSL 2 (GaloisField 2 m)) := by
  have hq4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hq : 2 < 2 ^ m := by omega
  have hx3' : ∃ j : ℕ, x ^ 3 ^ j = 1 := ⟨1, by rw [pow_one]; exact hx3⟩
  rcases hU with hU1 | ⟨K₀, _, _, hK₀, hU2⟩
  ·
    obtain ⟨eX⟩ := hU1
    have h₀ : UnitaryFieldData 2 m (GaloisField 2 (2 * m)) :=
      ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
    set e : X ⧸ aschbacherSolvableCore 3 X ≃* unitaryPSU h₀ 3 :=
      eX.trans ((Sec4.Census.statedSUEquivProjSU 3 2 m).symm.trans
        (unitaryPSUEquiv h₀ (by norm_num)).symm) with he
    set α := inducedAutHom X e ⟨x, hxN⟩ with hα
    have hα3 : α ^ 3 = 1 := inducedAutHom_pow_eq_one X e hxN hx3
    have hmem : α ∈ (psuConj h₀).range := by
      by_cases hin : IsInnerAut α
      · exact (stdPinnedPSU3 h₀).inn_le hin
      · rcases hasKind_psu3_diagonal_or_field_of_pow_three_eq_one hq hα3 hin with hd | hf
        · exact hd.1
        · exact absurd (Or.inl (KFacts.InducesStdKind.psu3 h₀ hq ⟨e, hxN, hf⟩)) hk
    obtain ⟨A₀, hA₀⟩ := hmem
    set S := fixSubgroup α with hSdef
    have hS : ∀ z, z ∈ S ↔ inducedAutHom X e ⟨x, hxN⟩ z = z := fun z => Iff.rfl
    have hmap := map_barCentralizer_eq hxN e S hS
    have hS2 : 2 ∣ Nat.card S := two_dvd_card_of_map e hmap h2
    have hα1 : psuConj h₀ A₀ ≠ 1 := by
      intro h1
      apply hne
      rw [eq_top_iff]
      intro y _
      rw [mem_barCentralizer_zpowers_iff hxN]
      have h3 : α (e y) = e y := by rw [← hA₀, h1, MulAut.one_apply]
      change e (Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨x, hxN⟩) (e.symm (e y))) = e y at h3
      rw [MulEquiv.symm_apply_apply] at h3
      exact e.injective h3
    have hS' : ∀ z, z ∈ S ↔ psuConj h₀ A₀ z = z := fun z => by rw [hA₀]; exact Iff.rfl
    obtain ⟨hmo, F₀, hF₀, hF₀', hcard, ⟨ι⟩⟩ := kf_psu3_fix h₀ hm A₀ hα1 (by rw [hA₀]; exact hα3)
      S hS' (exists_involution_of_two_dvd hS2)
    obtain ⟨κ⟩ := nonempty_imageModTheta_perfectResidual_mulEquiv hxN hx3' e S hS
    obtain ⟨σ⟩ := nonempty_sl2_mulEquiv_projSL hcard
    exact ⟨hmo, ⟨κ.trans (ι.trans σ)⟩⟩
  ·
    obtain ⟨eX⟩ := hU2
    have h₀ : UnitaryFieldData 2 m K₀ :=
      ⟨Nat.prime_two, by omega, by rw [hK₀, ← pow_mul, mul_comm]⟩
    set e : X ⧸ aschbacherSolvableCore 3 X ≃* unitarySU 2 m K₀ 3 := eX with he
    set α := inducedAutHom X e ⟨x, hxN⟩ with hα
    have hα3 : α ^ 3 = 1 := inducedAutHom_pow_eq_one X e hxN hx3
    set β := MulAut.congr (suCenterEquiv h₀ hq) (centerDescend _ α) with hβ
    have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, ← map_pow, hα3, map_one, map_one]
    have hmem : β ∈ (psuConj h₀).range := by
      by_cases hin : IsInnerAut β
      · exact (stdPinnedPSU3 h₀).inn_le hin
      · rcases hasKind_psu3_diagonal_or_field_of_pow_three_eq_one hq hβ3 hin with hd | hf
        · exact hd.1
        · exact absurd (Or.inl (KFacts.InducesStdKind.su3 h₀ hq ⟨e, hxN, hf⟩)) hk
    obtain ⟨A₀, hA₀⟩ := hmem
    have hαA : α = suConj h₀ A₀ := by
      apply eq_of_centerDescend_eq h₀ hq
      rw [OutFixCentralThree.congr_centerDescend_suConj hq A₀, hA₀]
    set S := suCentralizer (2 ^ m) (A₀ : GL (Fin 3) K₀) with hSdef
    have hS : ∀ z, z ∈ S ↔ inducedAutHom X e ⟨x, hxN⟩ z = z := by
      intro z
      rw [← hα, hαA, mem_suCentralizer, ← Subtype.coe_inj, coe_suConj, Subgroup.coe_inv,
        mul_inv_eq_iff_eq_mul, eq_comm]
    have hmap := map_barCentralizer_eq hxN e S hS
    have hS2 : 2 ∣ Nat.card S := two_dvd_card_of_map e hmap h2
    have hα1 : suConj h₀ A₀ ≠ 1 := by
      intro h1
      apply hne
      rw [eq_top_iff]
      intro y _
      rw [mem_barCentralizer_zpowers_iff hxN]
      have h3 : α (e y) = e y := by rw [hαA, h1, MulAut.one_apply]
      change e (Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨x, hxN⟩) (e.symm (e y))) = e y at h3
      rw [MulEquiv.symm_apply_apply] at h3
      exact e.injective h3
    obtain ⟨z, hzS, hz1, hz2⟩ := exists_involution_of_two_dvd hS2
    obtain ⟨hmo, F₀, hF₀, hF₀', hcard, ⟨ι⟩⟩ := kf_su3_fix h₀ hm A₀ hα1 (by rw [← hαA]; exact hα3)
      ⟨z, hzS, hz1, hz2⟩
    obtain ⟨κ⟩ := nonempty_imageModTheta_perfectResidual_mulEquiv hxN hx3' e S hS
    obtain ⟨σ⟩ := nonempty_sl2_mulEquiv_projSL hcard
    exact ⟨hmo, ⟨κ.trans (ι.trans σ)⟩⟩

end Fix

section Main

open Item86ResProof

theorem pair84GammaU_of (h45 : Sec4.Item4_5) (h418 : Item418Theta) (hF : KF84FieldStd) :
    Pair84GammaU := by
  intro G _ _ A c L a d n h b X hb hrel hXU
  have hd := h.data83
  have hn1 : 1 ≤ n := hd.odd.pos
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have h3 : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  obtain ⟨hbΓ, -, -⟩ := partner_data h hb hrel
  obtain ⟨-, hck⟩ := kinds_of_partner h418 hF h hb hrel
  have hbA : b ∈ A := hbΓ.1
  have hb1 : b ≠ 1 := hbΓ.2.1
  have hX : X ∈ thetaComponentsAt 3 b := hrel.2.2.1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  obtain ⟨hKmem, -, hK1⟩ := Item87Proof.residual_of_isGammaIndex h.mem_thetaComponentsAt hbΓ
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hKdef
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hKX : K ≤ X := hrel.2.2.2.1
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := hKL.trans hLc
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using h3 u u.2)⟩
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hz b hbA)
  have hAN : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 hG (h3 b hbA) hb1 hA3 hAb X hX
  have hcN : c ∈ Subgroup.normalizer (X : Set G) := hAN h.mem_A
  have hc3 : c ^ 3 = 1 := h3 c h.mem_A
  have hc3' : ∃ j : ℕ, c ^ 3 ^ j = 1 := ⟨1, by rw [pow_one]; exact hc3⟩
  set M := inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) with hMdef
  have hMX : M ≤ X := (Item87Proof.residual_le _).trans inf_le_left
  have hKM : K ≤ M := KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
    (le_inf hKX hKc)
  have hKeqM : IsQuasisimple (imageModTheta X M) → K = M := by
    intro hq
    have hMq := Item87Proof.isQuasisimple_quot_of_imageModTheta hMX hq
    have hMmem := Item87Proof.mem_thetaComponentsIn_residual hX hMq
    rw [inf_comm] at hMmem
    exact Sec6.eq_of_mem_thetaComponentsIn_of_le hKmem hMmem (Item87Proof.isPerfect_residual _)
      hK1 le_rfl hKM
  have hXq : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hX
  have hXns : ¬ Group.IsSolvable (X ⧸ aschbacherSolvableCore 3 X) := by
    have : Nontrivial (X ⧸ aschbacherSolvableCore 3 X) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hXq
    have := hXq.1
    exact Group.IsPerfect.not_isSolvable _
  obtain ⟨-, -, -, hcases⟩ := Item87Proof.isGammaIndex_cases hbΓ
  have h9K : 9 ∣ Nat.card K := by
    refine Dvd.dvd.trans ?_ (Item86ResProof.card_imageModTheta_dvd hKL)
    rcases hcases with ⟨-, F, _, _, hFc, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · have hU : UnitaryFieldData 2 (3 * n) F := ⟨Nat.prime_two, by omega, by
        rw [hFc, ← pow_mul, mul_comm]⟩
      rw [Nat.card_congr φ.toEquiv, KFacts.card_unitarySU_three hU]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (nine_dvd_two_pow_sq_sub_one n) _) _
    · rw [Nat.card_congr φ.toEquiv, Sec21.card_projSL_two _ (by omega)]
      exact Dvd.dvd.mul_left (nine_dvd_two_pow_sq_sub_one n) _
  have h9X : 9 ∣ Nat.card (X ⧸ aschbacherSolvableCore 3 X) := by
    have h1 := Item86ResProof.pow_three_dvd_card_imageModTheta hKX (k := 2) h9K
    exact h1.trans (Subgroup.card_subgroup_dvd_card _)
  obtain ⟨m, hm⟩ := hXU
  have hm2 : 2 ≤ m := by
    by_contra hlt
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · rcases hm with hm1 | ⟨F, _, _, hFc, -⟩
      · obtain ⟨e⟩ := hm1
        have h1 : 9 ∣ 168 :=
          (h9X.trans (by rw [Nat.card_congr e.toEquiv])).trans card_projSU_three_zero_dvd
        norm_num at h1
      · have := Finite.one_lt_card (α := F)
        rw [hFc] at this
        norm_num at this
    · apply hXns
      rcases hm with hm1 | ⟨F, _, _, hFc, ⟨e⟩⟩
      · obtain ⟨e⟩ := hm1
        have := Sec13.isSolvable_projSU_two
        exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      · have hU : UnitaryFieldData 2 1 F := ⟨Nat.prime_two, le_rfl, by rw [hFc]; norm_num⟩
        have := CFSG.StandardType.WitSU.isSolvable_unitarySU_two_one hU (k := 3) (by norm_num)
          le_rfl
        exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hne : barCentralizer (Subgroup.zpowers c) X ≠ ⊤ := by
    intro htop
    have himg : imageModTheta X M = ⊤ := by
      rw [KFacts.imageModTheta_perfectResidual_centralizer_eq hcN hc3', htop,
        CFSG.RankThree.inSubgroup_perfectResidual_of_isPerfect
          (Group.IsPerfect.top_iff.mpr hXq.1)]
    have hq : IsQuasisimple (imageModTheta X M) := by
      rw [himg]
      exact LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hXq
    have hKM' := hKeqM hq
    apply hrel.2.2.2.2
    rw [← hKM'] at himg
    exact eq_sup_of_imageModTheta_eq_top hKX himg
  have hNTL : NoThetaNormal (imageModTheta L K) := by
    rcases hcases with ⟨-, F, _, _, hFc, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · exact Item87Proof.NoThetaNormal.of_mulEquiv φ
        (Item87Proof.noThetaNormal_statedSU hFc (by omega))
    · exact Item87Proof.NoThetaNormal.of_mulEquiv φ
        (Item87Proof.noThetaNormal_projSL_two (by omega))
  obtain ⟨eKL⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hKL hNTL
  have h2 : 2 ∣ Nat.card (barCentralizer (Subgroup.zpowers c) X) := by
    have hle : imageModTheta X K ≤ barCentralizer (Subgroup.zpowers c) X := by
      have h1 : imageModTheta X K ≤ imageModTheta X M := Subgroup.map_mono (fun z hz => hKM hz)
      rw [KFacts.imageModTheta_perfectResidual_centralizer_eq hcN hc3'] at h1
      exact h1.trans (Item87Proof.residual_le _)
    refine Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le hle)
    refine Dvd.dvd.trans ?_ (card_quot_dvd_card_imageModTheta hKX)
    rw [Nat.card_congr eKL.toEquiv]
    rcases hcases with ⟨-, F, _, _, hFc, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · have hU : UnitaryFieldData 2 (3 * n) F := ⟨Nat.prime_two, by omega, by
        rw [hFc, ← pow_mul, mul_comm]⟩
      rw [Nat.card_congr φ.toEquiv, KFacts.card_unitarySU_three hU]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) _) _
    · rw [Nat.card_congr φ.toEquiv, Sec21.card_projSL_two _ (by omega)]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  obtain ⟨-, ⟨eM⟩⟩ := kf_unitary_fix hcN hc3 hm2 hm hck h2 hne
  have hq2 : IsQuasisimple (imageModTheta X M) :=
    LocalCores.isQuasisimple_of_mulEquiv eM.symm (Item87Proof.isQuasisimple_projSL_two hm2)
  have hKM' : K = M := hKeqM hq2
  have eM' : imageModTheta X K ≃* projSL 2 (GaloisField 2 m) := by
    rw [hKM']
    exact eM
  obtain ⟨eKX⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hKX
    (Item87Proof.NoThetaNormal.of_mulEquiv eM' (Item87Proof.noThetaNormal_projSL_two hm2))
  have hm3 : m = 3 * n := by
    rcases hcases with ⟨-, F, _, _, hFc, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · exfalso
      have hU : UnitaryFieldData 2 (3 * n) F := ⟨Nat.prime_two, by omega, by
        rw [hFc, ← pow_mul, mul_comm]⟩
      have h3n : 3 ∣ 2 ^ (3 * n) + 1 := KFacts.three_dvd_two_pow_three_mul_add_one hd.odd
      obtain ⟨z, hz, hz1, -⟩ := KFacts.exists_mem_center_statedSU_ne_one hU h3n
      set ι : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (3 * n) F 3 ≃*
          projSL 2 (GaloisField 2 m) := (φ.symm.trans eKL.symm).trans (eKX.trans eM') with hι
      have : IsSimpleGroup (projSL 2 (GaloisField 2 m)) := Sec21.isSimpleGroup_projSL_two hm2
      have hcen : Subgroup.center (projSL 2 (GaloisField 2 m)) = ⊥ := by
        apply center_eq_bot_of_isSimpleGroup
        obtain ⟨-, -, u, v, huv⟩ := Item87Proof.isQuasisimple_projSL_two hm2
        obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
        obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
        exact ⟨u', v', fun h' => huv (by rw [← QuotientGroup.mk_mul, h', QuotientGroup.mk_mul])⟩
      have hιz : ι z ∈ Subgroup.center (projSL 2 (GaloisField 2 m)) := by
        rw [← Subgroup.map_center_eq ι]
        exact ⟨z, hz, rfl⟩
      rw [hcen, Subgroup.mem_bot, map_eq_one_iff ι ι.injective] at hιz
      exact hz1 hιz
    · have e : projSL 2 (GaloisField 2 m) ≃* projSL 2 (GaloisField 2 (3 * n)) :=
        ((eM'.symm.trans eKX.symm).trans eKL).trans φ
      have hc := Nat.card_congr e.toEquiv
      obtain ⟨r, hr, hcr⟩ := card_projSL_two_eq (g := m) (by omega)
      obtain ⟨s, hs, hcs⟩ := card_projSL_two_eq (g := 3 * n) (by omega)
      rw [hcr, hcs] at hc
      exact CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs hc
  subst hm3
  refine ⟨h.mem_A, h.ne_one, hn1, Or.inr ⟨?_, ⟨eM⟩⟩⟩
  rcases hm with hm1 | hm1
  · exact Or.inr (Or.inr (Or.inl hm1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hm1)))

end Main

end CFSG.RankThree.PartTwo.Sec8.Item84Pair
