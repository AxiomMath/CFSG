module

public import CFSG.Quasithin.Background.F6CatRecogTools3
public import CFSG.Quasithin.Background.F6CatAssemblyMS
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurEight
public import CFSG.Quasithin.Background.F6CatRecogTools2

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter

namespace F6

theorem card_sq_ne_one_le {A B : Type*} [Group A] [Group B] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A →* B) (hf : Function.Injective f) :
    (Finset.univ.filter fun x : A => x * x ≠ 1).card ≤
      (Finset.univ.filter fun x : B => x * x ≠ 1).card := by
  refine Finset.card_le_card_of_injOn f (fun x hx => ?_) (fun x _ y _ h => hf h)
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
  intro h
  apply hx
  apply hf
  rw [map_mul, h, map_one]

theorem mod_eight_of_sq_mod_sixteen {p : ℕ} (h : p ^ 2 % 16 = 7 ∨ p ^ 2 % 16 = 9) :
    p % 8 = 3 ∨ p % 8 = 5 := by
  have h1 : p ^ 2 % 16 = (p % 16) ^ 2 % 16 := Nat.pow_mod p 2 16
  have h2 : p % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h3 : p % 8 = p % 16 % 8 := (Nat.mod_mod_of_dvd p (by norm_num)).symm
  rw [h1] at h
  rw [h3]
  interval_cases (p % 16) <;> simp_all

theorem f618RecogZ2D8SQT_holds
    (hW : WalterModelsStatement) (hL28 : L28AutFact)
    (hZD : Z2D8SylowListFact) (hPG : PGammaL2InspectionFact) : F618RecogZ2D8SQT := by
  intro D _ _ hS hT
  obtain ⟨S, ⟨eS⟩⟩ := hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS16 : Nat.card (S : Subgroup D) = 16 := (Nat.card_congr eS.toEquiv).trans (by
    rw [Nat.card_prod, DihedralGroup.nat_card]
    simp)
  have : IsSimpleGroup (TwoResidualQuot D) := hS.quasisimple.2.1
  have hnonab : ∃ a b : TwoResidualQuot D, a * b ≠ b * a := hS.quasisimple.2.2
  have : Group.IsPerfect ↥(twoResidual (⊤ : Subgroup D)) := hS.quasisimple.1
  have := twoResidual_top_normal (D := D)
  obtain ⟨Q, ⟨eQ⟩⟩ := exists_sylow_quotient_of_setting hS.toF618RecogSetting S
  have h4 := (not_isCyclic_sylow_two hnonab Q).2
  rw [← Nat.card_congr eQ.toEquiv] at h4
  have hdvd : Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hS16]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨n, hn⟩ := exists_index_twoResidual_eq (D := D)
  have hidx := card_sylow_eq_mul_index (twoResidual ⊤) hn S
  rw [hS16] at hidx
  have hcases : Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) = 4 ∨
      Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) = 8 ∨
      Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) = 16 := by
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hie] at h4 ⊢
    interval_cases i
    · norm_num at h4
    · norm_num at h4
    · left; norm_num
    · right; left; norm_num
    · right; right; norm_num
  rcases hcases with hP | hP | hP
  ·
    exfalso
    obtain ⟨p, K, _, _, hp, -, hp5, hK, -, -, ⟨eK⟩⟩ := psl_two_of_card_inf_eq_four hS S hP
    have : Fact p.Prime := ⟨hp⟩
    have hc : Nat.card (MulAut (TwoResidualQuot D)) = 2 * Nat.card (TwoResidualQuot D) := by
      rw [Nat.card_congr (MulAut.congr eK).toEquiv, Nat.card_congr eK.toEquiv]
      exact card_mulAut_psl_two_prime K hp5 hK
    have h2 := index_dvd_of_card_mulAut hS.toF618RecogSetting hc
    rw [hP] at hidx
    have h4' : (twoResidual (⊤ : Subgroup D)).index = 4 := by rw [hn]; omega
    rw [h4'] at h2
    norm_num at h2
  ·
    rw [hP] at hidx
    have hindex : (twoResidual (⊤ : Subgroup D)).index = 2 := by rw [hn]; omega
    have hQ8 : Nat.card (Q : Subgroup (TwoResidualQuot D)) = 8 := by
      rw [← Nat.card_congr eQ.toEquiv, hP]
    by_cases hab : IsMulCommutative (Q : Subgroup (TwoResidualQuot D))
    ·
      exfalso
      rcases (walter_cases hW hS Q hab).2 hQ8 with ⟨K, _, _, hK8, ⟨eK⟩⟩ | hJ
      · have hc : Nat.card (MulAut (TwoResidualQuot D)) = 3 * Nat.card (TwoResidualQuot D) := by
          rw [Nat.card_congr (MulAut.congr eK).toEquiv, Nat.card_congr eK.toEquiv]
          exact hL28 K hK8
        have h3 := index_dvd_of_card_mulAut hS.toF618RecogSetting hc
        rw [hindex] at h3
        norm_num at h3
      · have h1 := card_mul_index_dvd_card_mulAut hS.toF618RecogSetting
        rw [hindex] at h1
        have h2 := Nat.le_of_dvd Nat.card_pos h1
        have h3 := card_mulAut_le_of_isSporadic_J1 hJ
        have hpos : 0 < Nat.card (TwoResidualQuot D) := Nat.card_pos
        omega
    ·
      have hnc : ∃ a b : (Q : Subgroup (TwoResidualQuot D)), a * b ≠ b * a := by
        by_contra h
        push Not at h
        exact hab ⟨⟨h⟩⟩
      rcases CFSG.ComponentClassification.WalterSchur.dihedral_or_quaternion_of_card_eq_eight hQ8
          hnc with heD | heQ8
      ·
        obtain ⟨eD⟩ := heD
        rcases psl_two_or_alternating_seven_of_dihedral hS S ⟨eQ.trans eD⟩ with
          ⟨p, e, K, _, _, hp, hp2, he1, he2, h16, -, hK, ⟨eK⟩, hZ9, hZ⟩ | ⟨⟨e7⟩, hZ⟩
        · have : Fact p.Prime := ⟨hp⟩
          have hodd : IsOddPrimePower (Nat.card K) :=
            ⟨p, e, hp, hp.odd_of_ne_two hp2, he1, hK⟩
          interval_cases e
          ·
            exfalso
            rw [pow_one] at hK h16 hZ9
            have hp9 : p ≠ 9 := by
              rintro rfl
              norm_num at hp
            have hp5 : 5 ≤ p := by
              have := hp.two_le
              omega
            have hc : Nat.card (MulAut (TwoResidualQuot D)) =
                Nat.card (TwoResidualQuot D) * (twoResidual (⊤ : Subgroup D)).index := by
              rw [hindex, Nat.card_congr (MulAut.congr eK).toEquiv, Nat.card_congr eK.toEquiv,
                card_mulAut_psl_two_prime K hp5 hK, mul_comm]
            obtain ⟨ψ⟩ := nonempty_quotient_mulEquiv_mulAut hS.toF618RecogSetting hc
            let ε : D ≃* PGL2 K :=
              (mulEquiv_quotient_ker_of_center_eq_bot hS.toF618RecogSetting (hZ9 hp9)).trans
                (ψ.trans ((MulAut.congr (eK.trans
                  (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)).trans
                    (mulAutPSL2EquivPGL2 K hp5 hK)))
            obtain ⟨S', ⟨ι⟩⟩ := exists_sylow_mulEquiv_of_mulEquiv ε S
            obtain ⟨m, -, ⟨eDm⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model K hodd S'
            have hm : 2 ^ m = 2 ^ 3 := by
              have h1 := Nat.card_congr (ι.trans eDm).toEquiv
              rw [hS16, DihedralGroup.nat_card] at h1
              omega
            have hm3 : m = 3 := Nat.pow_right_injective le_rfl hm
            subst hm3
            let φ : Multiplicative (ZMod 2) × DihedralGroup 4 ≃* DihedralGroup 8 :=
              eS.symm.trans (ι.trans eDm)
            apply dihedral_eight_pow_four
            have h1 := z2_dihedral_pow_four (φ.symm (DihedralGroup.r 1))
            have h2 := congrArg φ h1
            rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at h2
          ·
            have hp8 := mod_eight_of_sq_mod_sixteen h16
            have h3 : 3 < Nat.card K := by
              rw [hK]
              have := hp.two_le
              nlinarith
            obtain ⟨H, hle, hrel, ⟨eH⟩⟩ :=
              exists_pGammaL2_subgroup_of_setting hS.toF618RecogSetting hK hodd h3 eK
            rw [hindex] at hrel
            obtain ⟨Q₁, ⟨e₁⟩⟩ := exists_sylow_quotient_ker hS.toF618RecogSetting S
            have : Finite (PGammaL2 K) := finite_pGammaL2 K
            obtain ⟨Q₂, ⟨e₂⟩⟩ := exists_sylow_mulEquiv_of_mulEquiv eH Q₁
            have hHeq : H = PSigmaL2 K := (hPG p K hp hK hp8).1 H hle hrel
              ⟨Q₂, ⟨(e₂.symm.trans e₁.symm).trans eS⟩⟩
            let eH' : D ⧸ (conjQuotHom D).ker ≃* ↥(PSigmaL2 K) :=
              eH.trans (MulEquiv.subgroupCongr hHeq)
            rcases hZ with hZb | hZ3
            · exact Or.inl ⟨p, hp, hp8, hp, K, inferInstance, inferInstance, hK,
                ⟨(mulEquiv_quotient_ker_of_center_eq_bot hS.toF618RecogSetting hZb).trans eH'⟩⟩
            · have h9 : p ^ 2 = 9 := by
                by_contra h
                rw [hZ9 h, Subgroup.card_bot] at hZ3
                norm_num at hZ3
              have hK9 : Nat.card K = 9 := by rw [hK, h9]
              obtain ⟨e6⟩ := nonempty_mulEquiv_alternating_six hK9 eK
              obtain ⟨σ⟩ := nonempty_pSigmaL2_mulEquiv_perm_six K hK9
              exact Or.inr (Or.inl (isHatSym_of_setting hS.toF618RecogSetting (by norm_num) hZ3 e6
                (eH'.trans σ)))
        ·
          have hc : Nat.card (MulAut (TwoResidualQuot D)) =
              Nat.card (TwoResidualQuot D) * (twoResidual (⊤ : Subgroup D)).index := by
            rw [hindex, Nat.card_congr (MulAut.congr e7).toEquiv, Nat.card_congr e7.toEquiv,
              card_mulAut_alternating_seven, mul_comm]
          obtain ⟨ψ⟩ := nonempty_quotient_mulEquiv_mulAut hS.toF618RecogSetting hc
          let σ : D ⧸ (conjQuotHom D).ker ≃* Equiv.Perm (Fin 7) :=
            ψ.trans ((MulAut.congr e7).trans (MulEquiv.ofBijective _
              (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
                (by norm_num) (by norm_num))).symm)
          rcases hZ with hZb | hZ3
          · exact Or.inr (Or.inr (Or.inl
              ⟨(mulEquiv_quotient_ker_of_center_eq_bot hS.toF618RecogSetting hZb).trans σ⟩))
          · exact Or.inr (Or.inr (Or.inr
              (isHatSym_of_setting hS.toF618RecogSetting (by norm_num) hZ3 e7 σ)))
      ·
        exfalso
        obtain ⟨eQ8⟩ := heQ8
        let f : QuaternionGroup 2 →* Multiplicative (ZMod 2) × DihedralGroup 4 :=
          eS.toMonoidHom.comp ((Subgroup.inclusion inf_le_left).comp
            (eQ.trans eQ8).symm.toMonoidHom)
        have hf : Function.Injective f :=
          eS.injective.comp ((Subgroup.inclusion_injective inf_le_left).comp
            (eQ.trans eQ8).symm.injective)
        have h := card_sq_ne_one_le f hf
        rw [card_sq_ne_one_quaternion, card_sq_ne_one_z2_dihedral] at h
        norm_num at h
  ·
    exfalso
    have hSL : (S : Subgroup D) ⊓ twoResidual ⊤ = S :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hP, hS16])
    exact hZD (TwoResidualQuot D) hS.list Q
      ⟨eQ.symm.trans ((MulEquiv.subgroupCongr hSL).trans eS)⟩

end F6

end CFSG.Quasithin
