module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofBorel
public import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofPairing
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofTrans
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def D4PairingE9 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (q : ℕ) (σ : K ≃+* K), Nat.card K = q ^ 3 →
    (∀ c, σ c = c ^ q) → ¬ 3 ∣ q →
    ∀ c ∈ Subgroup.centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), c ^ 3 = 1 → c ≠ 1 →
    ∀ d ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom, d ^ 3 = 1 → d ≠ 1 →
      (∃ a : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          a * d * a⁻¹ = d⁻¹ ∧ a * c * a⁻¹ = c) ∧
        (∃ b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          b * d * b⁻¹ = d ∧ b * c * b⁻¹ = c⁻¹) ∧
        ∃ t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, t * d * t⁻¹ = d ∧ t * c * t⁻¹ = c * d

@[expose] def D4PairingTransTwo :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (q : ℕ) (σ : K ≃+* K), Nat.card K = q ^ 3 →
    (∀ c, σ c = c ^ q) → q % 3 = 2 →
    ∀ c ∈ Subgroup.centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), c ^ 3 = 1 → c ≠ 1 →
    ∀ d ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom, d ^ 3 = 1 → d ≠ 1 →
      ∃ t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, t * d * t⁻¹ = d ∧ t * c * t⁻¹ = c * d

theorem Item1118Res3Proof.conj_symm_eq {Z C : Type} [Group Z] [Group C] (e : Z ≃* C) {a : C}
    {x y : Z} (h : a * e x * a⁻¹ = e y) : e.symm a * x * (e.symm a)⁻¹ = y := by
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h]

section Pairing

theorem k424PairingD4_of (hP : D4PairingE9) : K424PairingD4 := by
  intro X _ _ hX hq hZ hSL hXT D c d K h
  obtain ⟨q, hqv, ⟨f⟩⟩ := hXT
  have hXp : Group.IsPerfect X := hq.1
  have e : X ≃* _root_.commutator X :=
    ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv).symm
  have hDe := h.maximal.prop
  have hc3 : c ^ 3 = 1 := hDe.2 c h.c_mem
  have hd3 : d ^ 3 = 1 := hDe.2 d h.d_mem
  have hd1 : d ≠ 1 := fun h1 => h.d_not_mem (h1 ▸ Subgroup.one_mem _)
  have hz3 : MulAut.conj c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  have hJ : K ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj c)) := by
    rw [KS11Lie4Proof.fixSub_conj_eq_centralizer]
    exact h.mem_thetaComponentsIn
  by_cases hp3 : q.p = 3
  · exact (KS11Lie3Proof.false_of_isType424_d4_three hp3 f e hz3 hJ h.isType424).elim
  · have hZ' : ∃ (X' : Type) (_ : Group X'), (∃ (q : TauCeti.PrimePower)
        (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p ≠ 3 ∧
          Nonempty (X' ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
        Nonempty (X ≃* _root_.commutator X') :=
      ⟨X, inferInstance, ⟨q, hqv, hp3, ⟨f⟩⟩, ⟨e⟩⟩
    obtain ⟨K', _, _, q', σ, hK', hσ, h3, -, -, -, e', hec, hthree⟩ :=
      KS11Lie4Proof.exists_d4_threeB KS11Lie6Proof.d4ThreeConj_holds
        KS11Lie6Proof.d4ThreeACent_holds KS11Lie6Proof.d4ThreeBCent_holds hZ' hz3 hJ h.isType424
    have hKS := hthree.eq hJ
    have hed : e' d ∈ KS11Lie4Proof.d4ShortSL2 K' σ.toRingHom := by
      have hdK : d ∈ (KS11Lie4Proof.d4ShortSL2 K' σ.toRingHom).comap e'.toMonoidHom :=
        hKS ▸ h.d_mem_K
      exact hdK
    have hec3 : e' c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
    have hec1 : e' c ≠ 1 := fun h1 => h.c_ne_one (e'.injective (h1.trans (map_one e').symm))
    have hed3 : e' d ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
    have hed1 : e' d ≠ 1 := fun h1 => hd1 (e'.injective (h1.trans (map_one e').symm))
    obtain ⟨⟨a', ha'd, ha'c⟩, ⟨b', hb'd, hb'c⟩, ⟨t', ht'd, ht'c⟩⟩ :=
      hP K' q' σ hK' hσ h3 (e' c) hec hec3 hec1 (e' d) hed hed3 hed1
    refine Item1118Res3Proof.nonempty_autIn_dihedral_of_borel h
      (a := e'.symm a') (b := e'.symm b') (t := e'.symm t') ⟨?_, ?_⟩ ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · exact Item1118Res3Proof.conj_symm_eq e' (by rw [ha'd, map_inv])
    · exact Item1118Res3Proof.conj_symm_eq e' ha'c
    · exact Item1118Res3Proof.conj_symm_eq e' hb'd
    · exact Item1118Res3Proof.conj_symm_eq e' (by rw [hb'c, map_inv])
    · exact Item1118Res3Proof.conj_symm_eq e' ht'd
    · exact Item1118Res3Proof.conj_symm_eq e' (by rw [ht'c, map_mul])

theorem d4PairingE9_of (hT : D4PairingTransTwo) : D4PairingE9 := by
  intro K _ _ q σ hK hσ h3 c hc hc3 hc1 d hd hd3 hd1
  obtain ⟨ℓ, f, hℓ, hf, rfl⟩ := KS11Lie5Proof.exists_prime_pow_of_card_eq_cube hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    exact h3 (dvd_pow_self 3 (by omega))
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := f * 3) (by omega) (by rw [hK, pow_mul])
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  have h3K : (3 : K) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h')
  refine ⟨Item1118Res3Proof.exists_inv_short hσ3 h3K hc hd hd3 hd1,
    Item1118Res3Proof.exists_inv_centS hf hℓ3 hK hσ hc hc3 hc1 hd, ?_⟩
  have h0 : ℓ ^ f % 3 ≠ 0 := fun h => h3 (Nat.dvd_of_mod_eq_zero h)
  have hlt : ℓ ^ f % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2) with h1 | h2
  · exact Item1118Res3Proof.exists_trans_split hf hℓ3 hK hσ h1 hc hc3 hc1 hd hd3 hd1
  · exact hT K (ℓ ^ f) σ hK hσ h2 c hc hc3 hc1 d hd hd3 hd1

end Pairing

end CFSG.RankThree.PartTwo.Sec11
