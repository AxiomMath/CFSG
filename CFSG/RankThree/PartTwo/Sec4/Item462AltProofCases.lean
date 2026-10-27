module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofTrans
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofField
import CFSG.RankThree.PartTwo.Sec4.Census.Cover46
import CFSG.RankThree.PartTwo.Sec10.Sec10XProofCover
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU localRank)
open Matrix (ProjGenLinGroup)

theorem isSimpleGroup_projSL_three (F : Type) [Field F] : IsSimpleGroup (projSL 3 F) :=
  CFSG.PGLModel.isSimpleGroup_projSL_of_two_le F (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))

theorem isSimpleGroup_projSU_three (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (hq : p ^ e ≠ 2) :
    IsSimpleGroup (projSU 3 p e) :=
  CFSG.PGLModel.isSimpleGroup_projSU_of_admissible ⟨Fact.out, he, le_rfl, fun h => hq (Prod.mk.inj h).2⟩

theorem exists_isSLThreePiAt_pow {X : Type} [Group X] (h : IsSLThreePi X) :
    ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ IsSLThreePiAt X (p ^ f) := by
  obtain ⟨q, K, _, _, hK⟩ := h
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  set p := ringChar K
  have hcardK : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have : Fact p.Prime := ⟨hp⟩
  rcases hK with ⟨hq, hq3, ⟨e⟩⟩ | ⟨hq, hq3, ⟨e⟩⟩
  · have hqn : q = p ^ (n : ℕ) := by rw [← hq, hcardK]
    subst hqn
    exact ⟨p, n, inferInstance, n.pos, K, inferInstance, inferInstance, Or.inl ⟨hq, hq3, ⟨e⟩⟩⟩
  · have hdvd : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← hcardK, hq, sq]⟩
    obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        simp at hq3
      · exact h0
    exact ⟨p, m, inferInstance, hm1, K, inferInstance, inferInstance, Or.inr ⟨hq, hq3, ⟨e⟩⟩⟩

section List

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem list463_of_model (hKL3 : KSLThreeCentralizerQ) (h41 : Item4_1LargePrime)
    (hS4 : SectionFourHyp G) (hL : L ∈ thetaComponents 3 G)
    {β : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hβ3 : orderOf β = 3)
    (hβ : InnThetaNoncyclic β) {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (h : IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ f) ∨
      IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p f) :
    List463 L := by
  have : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  have hp : p.Prime := Fact.out
  have hp2 := (KSLThreeCentralizerQ.inst hKL3 hL hf h hβ3 hβ).1
  have hp3' : p ≠ 3 := by
    rintro rfl
    have h0 := Census.three_pow_mod_three hf
    rcases h with ⟨K, _, _, ⟨-, hq, -⟩ | ⟨-, hq, -⟩⟩ | ⟨hq, -⟩ | ⟨hq, -⟩ <;> omega
  have hp3 : 3 < p := by
    have := hp.two_le
    by_contra hle
    interval_cases p <;> simp_all
  have hiso := isoLThreePi_solvableRadical hL hf h
  have hf2 := le_two_of_isoLThreePi hp3 hf (localRank_solvableRadical_lt h41 hS4 hL hp hp3) hiso
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, inferInstance, hp3, hf, hf2, hiso⟩))))

end List

section Heis

variable {G : Type} [Group G] [Finite G]

theorem card_inf_eq_three_of_isHeisCentral {L A : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA3 : ∀ x ∈ A, x ^ 3 = 1)
    (h27 : Nat.card A = 27)
    (h : IsHeisCentral (thetaImage (L ⊔ A)) (L ⧸ aschbacherSolvableCore 3 L)) :
    Nat.card (A ⊓ L : Subgroup G) = 3 := by
  obtain ⟨U₀, V₀, hUV, hcomm, hHeis, ⟨eV⟩, hUV3⟩ := h
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U₀ V₀ hcomm).1
  rw [hUV, hUV3, Subgroup.card_top, hHeis.2.1, Nat.card_congr eV.toEquiv] at h1
  have h2 := card_thetaImage_mul hL hAN hA3
  rw [h27] at h2
  have hpos : 0 < Nat.card (thetaImage (L ⊔ A)) := Nat.card_pos
  have h3 : Nat.card (thetaImage (L ⊔ A)) * Nat.card (A ⊓ L : Subgroup G) =
      Nat.card (thetaImage (L ⊔ A)) * 3 := by
    rw [h2, h1]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos h3

theorem false_of_isHeisCentral {A B D L : Subgroup G} {a b : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27)
    (haZ : a ∈ Subgroup.center G) (ha3 : orderOf a = 3)
    (haB : a ∈ B) (hbB : b ∈ B) (hba : b ∉ Subgroup.zpowers a) (hBA : B ≤ A)
    (hB9 : Nat.card B = 9) (hDA : D ≤ A) (hBDA : B ⊔ D = A) (hD3 : Nat.card D = 3)
    (hND : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G))
    (hL : L ∈ thetaComponents 3 G) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hH : IsHeisCentral (thetaImage (L ⊔ A)) (L ⧸ aschbacherSolvableCore 3 L))
    (hel : CFSG.Assembly.IsElemAbelian 3 (autIn L A)) (h9 : Nat.card (autIn L A) = 9) : False := by
  have h3 := card_inf_eq_three_of_isHeisCentral hL hAL hAe.2 h27 hH
  have hle := card_autIn_le hAe haZ ha3 haB hbB hba hBA hB9 hDA hBDA hD3 hND hAL hel.2
  omega

theorem list463_of_isHeisCentral (hKL3 : KSLThreeCentralizerQ) (h41 : Item4_1LargePrime)
    (hS4 : SectionFourHyp G) {L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    {β : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hβ3 : orderOf β = 3)
    (hβ : InnThetaNoncyclic β)
    (h : IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22 ∨
      IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L)) :
    List463 L := by
  have : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  obtain ⟨eR⟩ := Sec10.Sec10XProof.nonempty_quotient_center_mulEquiv (Y := L) hL.2.2
  rcases h with ⟨-, ⟨e7⟩⟩ | ⟨-, ⟨e22⟩⟩ | hSL
  · exact Or.inl ⟨eR.symm.trans e7⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨eR.symm.trans e22⟩)))
  · obtain ⟨p, f, hpF, hf, hpf⟩ := exists_isSLThreePiAt_pow hSL
    exact list463_of_model hKL3 h41 hS4 hL hβ3 hβ hf (Or.inl hpf)

end Heis

section PGL

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem inducesOuterTheta_of_inducesTypeOn_three (hL : L ∈ thetaComponents 3 G) {x : G}
    (hx : InducesTypeOn L x 3) : InducesOuterTheta x L := by
  obtain ⟨hxN, π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  refine ⟨hxN, fun ⟨w, hw⟩ => ?_⟩
  have hPerfL : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hL.2.2.1
  have hPerf : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply Sec4.not_inner_of_type3 hK hq hyH hy3
  obtain ⟨s, hs, hse⟩ := (e w).2
  refine ⟨s, hs, ?_⟩
  have hmod : ∀ m ∈ Sec4.slPi π 3 (p ^ f) K,
      s⁻¹ * y * m * (s⁻¹ * y)⁻¹ * m⁻¹ ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K := by
    intro m hm
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars]
    set z := e.symm ⟨ProjGenLinGroup.mk m, Subgroup.mem_map_of_mem _ hm⟩ with hz
    have hez : (e z : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk m := by
      rw [hz, MulEquiv.apply_symm_apply]
    have h1 := hact z
    have h2 : thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) z = w * z * w⁻¹ := by
      change thetaQuotMulAut L (compAction L ⟨x, hxN⟩) z = _
      rw [← hw, MulAut.conj_apply]
    rw [h2, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      ← hse, hez] at h1
    simp only [map_mul, map_inv]
    calc (ProjGenLinGroup.mk s)⁻¹ * ProjGenLinGroup.mk y * ProjGenLinGroup.mk m *
          ((ProjGenLinGroup.mk s)⁻¹ * ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk m)⁻¹ =
        (ProjGenLinGroup.mk s)⁻¹ * (ProjGenLinGroup.mk y * ProjGenLinGroup.mk m *
          (ProjGenLinGroup.mk y)⁻¹) * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk m)⁻¹ := by group
      _ = 1 := by rw [← h1]; group
  intro m hm
  have hc := Sec4.commute_of_comm_mod_scalars hmod m hm
  calc y * m * y⁻¹ = s * (s⁻¹ * y * m) * y⁻¹ := by group
    _ = s * (m * (s⁻¹ * y)) * y⁻¹ := by rw [hc]
    _ = s * m * s⁻¹ := by group

theorem model_of_inducesTypeOn (hL : L ∈ thetaComponents 3 G) {x : G} {k : ℕ}
    (hx : InducesTypeOn L x k) :
    ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p f ∧
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ := by
  obtain ⟨-, π, p, f, K, _, hK, hq, e, -⟩ := hx
  have : Fact p.Prime := ⟨hK.prime⟩
  have hPerfL : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hL.2.2.1
  have hPerf : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨p, f, inferInstance, hK.one_le,
    isoLThreePi_of_mulEquiv e (isoLThreePi_projImage_slPi hK hq), ?_⟩
  rw [← Subgroup.map_center_eq e.symm, Sec4.center_projImage_eq_bot hK hq, Subgroup.map_bot]

theorem false_of_isZ3PGLThreePi (hKL3 : KSLThreeCentralizerQ) {A B D : Subgroup G} {a b : G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (h27 : Nat.card A = 27) (haA : a ∈ A) (haZ : a ∈ Subgroup.center G) (ha3 : orderOf a = 3)
    (haB : a ∈ B) (hbB : b ∈ B) (hba : b ∉ Subgroup.zpowers a) (hBA : B ≤ A)
    (hB9 : Nat.card B = 9) (hDA : D ≤ A) (hBDA : B ⊔ D = A) (hD3 : Nat.card D = 3)
    (hND : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G))
    (hL : L ∈ thetaComponents 3 G) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hCA : ∀ y ∈ A, y ∈ thetaQuotCentralizer L ↔ y ∈ Subgroup.zpowers a)
    (hβ3 : orderOf (thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hAL (hBA hbB)⟩)) = 3)
    (hβ : InnThetaNoncyclic (thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hAL (hBA hbB)⟩)))
    (hAut : Nonempty (autIn L A ≃* Multiplicative (ZMod 3)))
    (hx : ∃ x ∈ A, x ≠ 1 ∧ InducesTypeOn L x 3) : False := by
  classical
  have hAe := hmax.1
  have hbA := hBA hbB
  obtain ⟨x, hxA, -, hxT⟩ := hx
  have hxout := inducesOuterTheta_of_inducesTypeOn_three hL hxT
  obtain ⟨p, f, hpF, hf, hiso, hZ⟩ := model_of_inducesTypeOn hL hxT
  have haL : a ∉ L := Census.not_mem_of_center_eq_bot haZ ha3 hZ
  obtain ⟨-, v, -, hβv⟩ := KSLThreeCentralizerQ.inst hKL3 hL hf (Or.inr hiso) hβ3 hβ
  have hbin : ¬ InducesOuterTheta b L := by
    rw [inducesOuterTheta_iff (hAL hbA), not_not, hβv]
    exact ⟨v, rfl⟩
  have hbLa := Item462Proof.mem_sup_zpowers_of_not_inducesOuterTheta hmax hL hAL hCA hZ hbA hbin
  have hZn : (Subgroup.zpowers a).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr haZ)
  obtain ⟨w, hw, z, hz, hwz⟩ := Subgroup.mem_sup_of_normal_right.mp hbLa
  have hzA : z ∈ A := (Subgroup.zpowers_le.mpr haA) hz
  have hwA : w ∈ A := by
    have := A.mul_mem hbA (A.inv_mem hzA)
    rwa [← hwz, mul_inv_cancel_right] at this
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [one_mul] at hwz
    exact hba (hwz ▸ hz)
  have hle := card_inf_le_three_of_outer h27 haA haZ ha3 haL hxA hxout
  have hAL3 : Nat.card (A ⊓ L : Subgroup G) = 3 := by
    have hne : A ⊓ L ≠ ⊥ := fun h => hw1 (by
      have : w ∈ A ⊓ L := ⟨hwA, hw⟩
      rwa [h, Subgroup.mem_bot] at this)
    have h1 : 1 < Nat.card (A ⊓ L : Subgroup G) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hk] at h1 hle ⊢
    interval_cases k <;> simp_all
  obtain ⟨eA⟩ := hAut
  have hcard3 : Nat.card (autIn L A) = 3 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have hexp : ∀ σ ∈ autIn L A, σ ^ 3 = 1 := by
    intro σ hσ
    have h1 : (eA ⟨σ, hσ⟩) ^ 3 = 1 := by
      have := pow_card_eq_one (G := Multiplicative (ZMod 3)) (x := eA ⟨σ, hσ⟩)
      rwa [Fintype.card_multiplicative, ZMod.card] at this
    have h2 : (⟨σ, hσ⟩ : autIn L A) ^ 3 = 1 := by
      apply eA.injective
      rw [map_pow, h1, map_one]
    exact congrArg Subtype.val h2
  have hne : autIn L A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard3
    omega
  obtain ⟨⟨σ, hσ⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hσ1' : σ ≠ 1 := fun h => hσ1 (Subtype.ext h)
  apply hσ1'
  obtain ⟨h, hN, hhL, rfl⟩ := mem_autIn_iff.mp hσ
  have hhALn : h ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyA, hyL⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hN y).mp hyA,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hhL) y).mp hyL⟩
    · rintro ⟨hyA, hyL⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hN y).mpr hyA,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hhL) y).mpr hyL⟩
  have hw' := fix_of_mem_autIn hAL3 inf_le_left hN hhALn (hexp _ hσ) ⟨hwA, hw⟩
  have hz' : h * z * h⁻¹ = z := by
    rw [Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr haZ) hz) h, mul_inv_cancel_right]
  refine eq_one_of_mem_autIn hAe haZ ha3 haB hbB hba hBA hB9 hDA hBDA hD3 hND hσ (hexp _ hσ) ?_
  rw [Sec4.normalizerMonoidHom_apply_coe]
  change h * b * h⁻¹ = b
  rw [← hwz, show h * (w * z) * h⁻¹ = (h * w * h⁻¹) * (h * z * h⁻¹) by group, hw', hz']

theorem list463_of_inducesTypeOn (hKL3 : KSLThreeCentralizerQ) (h41 : Item4_1LargePrime)
    (hS4 : SectionFourHyp G) (hL : L ∈ thetaComponents 3 G)
    {β : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hβ3 : orderOf β = 3)
    (hβ : InnThetaNoncyclic β) {x : G} (hx : InducesTypeOn L x 3) : List463 L := by
  obtain ⟨p, f, hpF, hf, hiso, -⟩ := model_of_inducesTypeOn hL hx
  exact list463_of_model hKL3 h41 hS4 hL hβ3 hβ hf (Or.inr hiso)

theorem list463_of_isZ3LThreePi (hKL3 : KSLThreeCentralizerQ) (h41 : Item4_1LargePrime)
    (hS4 : SectionFourHyp G) {A : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {β : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hβ3 : orderOf β = 3)
    (hβ : InnThetaNoncyclic β) (h : Sec8.IsZ3LThreePi (thetaImage (L ⊔ A))) : List463 L := by
  obtain ⟨p, e, hpF, he, ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩⟩ := h
  · obtain ⟨eX⟩ := Item462Proof.nonempty_mulEquiv_of_thetaImage hL hAL
      (isSimpleGroup_projSL_three (GaloisField p e)) φ
    exact list463_of_model hKL3 h41 hS4 hL hβ3 hβ he (Or.inr (Or.inl ⟨hq, ⟨eX⟩⟩))
  · by_cases h2 : p ^ e = 2
    · exfalso
      have hp : p.Prime := Fact.out
      have hp2 : p = 2 := by
        have h1 : p ∣ 2 := ⟨p ^ (e - 1), by rw [← pow_succ', Nat.sub_add_cancel he, h2]⟩
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1
      have he1 : e = 1 := by
        rw [hp2] at h2
        exact Nat.pow_right_injective le_rfl (show 2 ^ e = 2 ^ 1 by rw [h2, pow_one])
      subst hp2
      subst he1
      have hsolv : Group.IsSolvable (projSU 3 2 1) := Sec13.isSolvable_projSU_two
      have hH : Group.IsSolvable (thetaImage (L ⊔ A)) :=
        Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
      obtain ⟨-, hK, ⟨η, -⟩, -⟩ := theta_component_quotient_structure Nat.prime_three hL
      have hKH : L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≤ thetaImage (L ⊔ A) :=
        Subgroup.map_mono le_sup_left
      have hKs : Group.IsSolvable (L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKH)
          (Subgroup.inclusion_injective hKH)
      have hLs : Group.IsSolvable (L ⧸ aschbacherSolvableCore 3 L) :=
        Group.isSolvable_of_isSolvable_injective (f := η.toMonoidHom) η.injective
      have hq' := hL.2.2
      have : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hq'.1
      have := CFSG.LocalCores.isQuasisimple_nontrivial hq'
      exact Group.IsPerfect.not_isSolvable (L ⧸ aschbacherSolvableCore 3 L) hLs
    · obtain ⟨eX⟩ := Item462Proof.nonempty_mulEquiv_of_thetaImage hL hAL
        (isSimpleGroup_projSU_three p e he h2) φ
      exact list463_of_model hKL3 h41 hS4 hL hβ3 hβ he (Or.inr (Or.inr ⟨hq, ⟨eX⟩⟩))

end PGL

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof
