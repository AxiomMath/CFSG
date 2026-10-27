module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U5Cartan
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientBridge
public import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSU
public import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcShared
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitBorel
public import CFSG.LocalAnalysis.UniquenessCase.UCKOutPB
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.RankThree.CentralLiftU.UnitaryTorus
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoordinateLinear
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldMatrix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.Quasithin.Background.A3Structure315Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

theorem k_U5TorusRank_holds :
    K_U5TorusRank := by
  intro K _ _ f hadm hL hq S hS s hs hsdvd hexc
  have hf1 : 1 ≤ f := hadm.2.1
  have hs2 : s ≠ 2 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_ne_two_of_dvd_add_one hf1 hs hsdvd
  have hB : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit K s 2 := by
    rcases Nat.lt_or_ge f 2 with hf | hf
    · have hf1' : f = 1 := by omega
      subst hf1'
      have hs3 : s = 3 := by
        refine (Nat.prime_dvd_prime_iff_eq hs (by norm_num : Nat.Prime 3)).1 ?_
        simpa using hsdvd
      subst hs3
      obtain ⟨Kf, hFld, hFin, h, ⟨e⟩⟩ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_exists_hypPSU
          (Y := K ⧸ Subgroup.center K) (n := 1) (r := 2) (ε := 1)
          (by norm_num) (by norm_num) hL
      have : CharP Kf 2 := h.charP
      have hZcard : Nat.card (hypScalars h 2 1) = 1 := by
        rw [card_hypScalars h (by norm_num : 1 ≤ 2 * 2 + 1)]
        norm_num
      have hZbot : hypScalars h 2 1 = ⊥ := Subgroup.card_eq_one.mp hZcard
      have eZ : hypPSU h 2 1 ≃* hypSU h 2 1 :=
        (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
      have e₂ : (K ⧸ Subgroup.center K) ≃* hypSU h 2 1 := e.trans eZ
      obtain ⟨R, hR⟩ := exists_isHypTransport (h := h) (r := 2) (ε := 1)
      let Φ : hypSU h 2 1 ≃* StatedSU 5 (2 ^ 1) Kf := hypTransport h hR
      let π : K →* StatedSU 5 (2 ^ 1) Kf :=
        Φ.toMonoidHom.comp (e₂.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
      have hπ : Function.Surjective π :=
        Φ.surjective.comp (e₂.surjective.comp (QuotientGroup.mk'_surjective _))
      have : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
      have hπc : π.ker ≤ Subgroup.center K := by
        intro x hx
        have hx2 : e₂ (QuotientGroup.mk x) = 1 := by
          apply Φ.injective
          simpa [π] using hx
        exact (QuotientGroup.eq_one_iff x).1 (e₂.injective (by simpa using hx2))
      obtain ⟨σ, hσ⟩ :=
        CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
          (p := 2) (f := 1) (F := Kf) (n := 5) (by rw [h.card]; norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (E := K) (π := π) hπ hπc
      have hkerbot : π.ker = ⊥ :=
        CFSG.LieType.Steinberg.CentralExt.SUOdd.ker_eq_bot_of_section hπc hσ
      have hcenter : Subgroup.center K = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hxq : QuotientGroup.mk x = 1 := (QuotientGroup.eq_one_iff x).2 hx
        have hxπ : x ∈ π.ker := by
          rw [MonoidHom.mem_ker]
          show Φ (e₂ (QuotientGroup.mk x)) = 1
          rw [hxq]
          simp
        rw [hkerbot] at hxπ
        simpa using hxπ
      obtain ⟨e0⟩ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwex_equiv_quot_of_center_eq_bot hcenter
      have eK : K ≃* hypSU h 2 1 := e0.trans e₂
      obtain ⟨μ, hcardμ, hexpμ, hμ⟩ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_exists_mu (h := h) (n := 1)
          (ℓ := 3) (by norm_num) (by norm_num)
      have hinj : ∀ x : (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_ratio μ 2 1).ker,
          eK.symm (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_hom hμ x) = 1 → x = 1 := by
        intro x hx
        apply CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_eq_one_of_hom_eq_one hμ x
        exact eK.symm.injective (by simpa using hx)
      exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_borelWit_core (h := h)
        (hμ := hμ) (hℓ := by norm_num) (hodd := by decide) (hcard := hcardμ) (hexp := hexpμ)
        (r := 2) (ε := 1) (hr := by norm_num) (hε := by norm_num) (X := K)
        (α := eK.symm.toMonoidHom) (hα := eK.symm.surjective) (hinj := hinj)
    · by_cases hs5 : s = 5
      · subst hs5
        have hf2 : 2 ≤ f := by
          rcases Nat.lt_or_ge f 2 with hf' | hf'
          · have hf1' : f = 1 := by omega
            subst hf1'
            norm_num at hsdvd
          · exact hf'
        obtain ⟨Kf, hFld, hFin, h, ⟨e⟩⟩ :=
          CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_exists_hypPSU
            (Y := K ⧸ Subgroup.center K) (n := f) (r := 2) (ε := 1)
            hf1 (by norm_num) hL
        have : CharP Kf 2 := h.charP
        obtain ⟨α, hα, hker, hαπ⟩ :=
          CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_exists_cover h
            (r := 2) (ε := 1) le_rfl (by norm_num) hf2 hq e
        have hZcard : Nat.card (hypScalars h 2 1) = 5 := by
          rw [card_hypScalars h (by norm_num : 1 ≤ 2 * 2 + 1)]
          exact Nat.gcd_eq_left hsdvd
        by_cases hZ : Subgroup.center K = ⊥
        ·
          have hZk : Nat.card (Subgroup.center K) = 1 := by rw [hZ]; simp
          have h25 : 25 ∣ 2 ^ f + 1 := by
            by_contra h
            exact hexc ⟨rfl, hZk, h⟩
          have h25K : 25 ∣ Nat.card Kfˣ := by
            rw [Nat.card_units, h.card]
            have hsq : 2 ^ (2 * f) - 1 = ((2 ^ f) + 1) * ((2 ^ f) - 1) := by
              rw [show 2 ^ (2 * f) = (2 ^ f) ^ 2 by
                rw [show 2 * f = f * 2 by ring, ← pow_mul]]
              simpa using Nat.sq_sub_sq (2 ^ f) 1
            rw [hsq]
            exact Dvd.dvd.mul_right h25 _
          obtain ⟨ζ, hζ⟩ :=
            CFSG.LocalAnalysis.UniquenessCase.UCK.OutP.exists_orderOf_eq_of_dvd h25K
          have hζ25 : ζ ^ 25 = 1 := by
            rw [← hζ]
            exact pow_orderOf_eq_one ζ
          have hζ25K : ((ζ : Kf)) ^ 25 = 1 := by
            simpa using congrArg (fun u : Kfˣ => (u : Kf)) hζ25
          have hqmod : 2 ^ f % 25 = 24 := by
            have h := Nat.dvd_iff_mod_eq_zero.mp h25
            rw [Nat.add_mod] at h
            have hlt := Nat.mod_lt (2 ^ f) (by norm_num : 0 < 25)
            omega
          have hζ24 : ζ ^ 24 = ζ⁻¹ := by
            apply eq_inv_of_mul_eq_one_left
            rw [← pow_succ, show 24 + 1 = 25 by norm_num, hζ25]
          have hbarζ : h.bar ((ζ : Kf)) = ((ζ : Kf))⁻¹ := by
            rw [UnitaryFieldData.bar_apply,
              pow_eq_pow_mod (n := 25) (m := 2 ^ f) (a := ((ζ : Kf))) hζ25K, hqmod]
            simpa using congrArg (fun u : Kfˣ => (u : Kf)) hζ24
          let ω : Kfˣ := ζ ^ 5
          have hωord : orderOf ω = 5 := by
            change orderOf (ζ ^ 5) = 5
            rw [orderOf_pow_of_dvd (by norm_num) (by rw [hζ]; norm_num), hζ]
          have hω5 : ω ^ 5 = 1 := by
            change (ζ ^ 5) ^ 5 = 1
            rw [← pow_mul, show 5 * 5 = 25 by norm_num, hζ25]
          have hωne : ω ≠ 1 := by
            intro h
            rw [h, orderOf_one] at hωord
            norm_num at hωord
          have hω25 : ω ^ 25 = 1 := by
            rw [show (25 : ℕ) = 5 * 5 by norm_num, pow_mul, hω5, one_pow]
          have hbarω : h.bar ((ω : Kf)) = ((ω : Kf))⁻¹ := by
            change h.bar (((ζ ^ 5 : Kfˣ) : Kf)) = (((ζ ^ 5 : Kfˣ) : Kf))⁻¹
            rw [Units.val_pow_eq_pow_val, map_pow, hbarζ, inv_pow]
          have hζq : ζ ^ (2 ^ f + 1) = 1 := by
            obtain ⟨m, hm⟩ := h25
            rw [hm, pow_mul, hζ25, one_pow]
          have hωq : ω ^ (2 ^ f + 1) = 1 := by
            obtain ⟨m, hm⟩ := h25
            rw [hm, pow_mul, hω25, one_pow]
          let aX : Fin 2 → Kfˣ := fun _ => ζ
          let dX : Fin 1 → Kfˣ := fun _ => (ζ ^ 4)⁻¹
          have hdXq : ∀ k, (dX k) ^ (2 ^ f + 1) = 1 := by
            intro k
            change ((ζ ^ 4)⁻¹) ^ (2 ^ f + 1) = 1
            rw [inv_pow, ← pow_mul, Nat.mul_comm 4, pow_mul, hζq, one_pow, inv_one]
          have hdX : ∀ k, h.norm (dX k : Kf) = 1 := by
            intro k
            rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, hdXq k,
              Units.val_one]
          have hpX : torusRatio h aX dX = 1 := by
            rw [torusRatio]
            simp only [Fin.prod_univ_two, Fin.prod_univ_one, aX, dX]
            rw [hbarζ]
            simp only [div_eq_mul_inv, inv_inv]
            have hζ0 : (ζ : Kf) ≠ 0 := Units.ne_zero ζ
            field_simp [hζ0]
            rw [Units.val_inv_eq_inv_val]
            exact mul_inv_cancel₀ (pow_ne_zero 4 hζ0)
          let aY : Fin 2 → Kfˣ := fun i => if i = 0 then ω else 1
          let dY : Fin 1 → Kfˣ := fun _ => (ω ^ 2)⁻¹
          have hdYq : ∀ k, (dY k) ^ (2 ^ f + 1) = 1 := by
            intro k
            change ((ω ^ 2)⁻¹) ^ (2 ^ f + 1) = 1
            rw [inv_pow, ← pow_mul, Nat.mul_comm 2, pow_mul, hωq, one_pow, inv_one]
          have hdY : ∀ k, h.norm (dY k : Kf) = 1 := by
            intro k
            rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, hdYq k,
              Units.val_one]
          have hpY : torusRatio h aY dY = 1 := by
            rw [torusRatio]
            simp only [Fin.prod_univ_two, Fin.prod_univ_one, dY]
            have h0K : ((aY 0 : Kfˣ) : Kf) = (ω : Kf) := by simp [aY]
            have h1K : ((aY 1 : Kfˣ) : Kf) = (1 : Kf) := by simp [aY]
            change (((aY 0 : Kfˣ) : Kf) / h.bar ((aY 0 : Kfˣ) : Kf)) *
                (((aY 1 : Kfˣ) : Kf) / h.bar ((aY 1 : Kfˣ) : Kf)) *
                ((dY 0 : Kfˣ) : Kf) = 1
            rw [h0K, h1K, hbarω, map_one]
            have hω0 : (ω : Kf) ≠ 0 := Units.ne_zero ω
            have hdY0 : ((dY 0 : Kfˣ) : Kf) = ((ω : Kf) ^ 2)⁻¹ := by
              change (((ω ^ 2)⁻¹ : Kfˣ) : Kf) = ((ω : Kf) ^ 2)⁻¹
              rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
            rw [hdY0]
            simp only [div_eq_mul_inv, inv_inv, inv_one, mul_one, one_mul]
            simpa [pow_two] using mul_inv_cancel₀ (pow_ne_zero 2 hω0)
          obtain ⟨x, hxT, hxmat⟩ := torusMat_mem_hypSU h aX (d := dX) hdX hpX
          obtain ⟨y, hyT, hymat⟩ := torusMat_mem_hypSU h aY (d := dY) hdY hpY
          have hζinv : (h.bar ((ζ : Kf)))⁻¹ = (ζ : Kf) := by rw [hbarζ, inv_inv]
          have hωinv : (h.bar ((ω : Kf)))⁻¹ = (ω : Kf) := by rw [hbarω, inv_inv]
          have hωval : (ω : Kf) = (ζ : Kf) ^ 5 := by
            change (((ζ ^ 5 : Kfˣ) : Kf)) = (ζ : Kf) ^ 5
            rw [Units.val_pow_eq_pow_val]
          have hdX5u : ∀ k : Fin 1, (dX k) ^ 5 = ζ ^ 5 := by
            intro k
            change ((ζ ^ 4)⁻¹) ^ 5 = ζ ^ 5
            rw [inv_pow, ← pow_mul, show 4 * 5 = 20 by norm_num]
            rw [inv_eq_iff_mul_eq_one, ← pow_add, show 20 + 5 = 25 by norm_num, hζ25]
          have hdX5K : ∀ k : Fin 1, (((dX k : Kfˣ) : Kf) ^ 5) = (ω : Kf) := by
            intro k
            have h := congrArg (fun u : Kfˣ => ((u : Kf))) (hdX5u k)
            rw [Units.val_pow_eq_pow_val] at h
            exact h.trans hωval.symm
          have hentriesX5 : ∀ i : HypIndex 2 1,
              torusEntries h aX dX i ^ 5 = (ω : Kf) := by
            intro i
            rcases i with i | k | i
            · fin_cases i <;> simpa [torusEntries, aX, hωval]
            · fin_cases k
              simpa [torusEntries, dX] using hdX5K 0
            · fin_cases i <;> simpa [torusEntries, aX, hζinv, hωval]
          have hnormω : h.norm ((ω : Kf)) = 1 := by
            rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, hωq,
              Units.val_one]
          have hω5K : (ω : Kf) ^ 5 = 1 := by
            simpa using congrArg (fun u : Kfˣ => ((u : Kf))) hω5
          have hx5mem : x ^ 5 ∈ hypScalars h 2 1 := by
            refine ⟨ω, hnormω, hω5, ?_⟩
            apply Units.ext
            rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hxmat, Matrix.diagonal_pow]
            ext i j
            by_cases hij : i = j
            · subst hij
              simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
                Matrix.diagonal_apply_eq, hentriesX5 i]
            · simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hij]
          have hdY5u : ∀ k : Fin 1, (dY k) ^ 5 = 1 := by
            intro k
            change ((ω ^ 2)⁻¹) ^ 5 = 1
            rw [inv_pow, ← pow_mul, show 2 * 5 = 10 by norm_num,
              show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, hω5, one_pow, inv_one]
          have hdY5K : ∀ k : Fin 1, (((dY k : Kfˣ) : Kf) ^ 5) = 1 := by
            intro k
            have h := congrArg (fun u : Kfˣ => ((u : Kf))) (hdY5u k)
            rw [Units.val_pow_eq_pow_val] at h
            simpa using h
          have hentriesY5 : ∀ i : HypIndex 2 1, torusEntries h aY dY i ^ 5 = 1 := by
            intro i
            rcases i with i | k | i
            · fin_cases i <;> simpa [torusEntries, aY, hω5K]
            · fin_cases k
              simpa [torusEntries, dY] using hdY5K 0
            · fin_cases i <;> simpa [torusEntries, aY, hωinv, hω5K]
          have hy5 : y ^ 5 = 1 := by
            apply Subtype.ext
            rw [Subgroup.coe_pow]
            apply Units.ext
            rw [Units.val_pow_eq_pow_val, hymat, Matrix.diagonal_pow, Subgroup.coe_one,
              Units.val_one, ← Matrix.diagonal_one]
            congr 1
            funext i
            exact hentriesY5 i
          have hx00 : (((x : GL (HypIndex 2 1) Kf) :
              Matrix (HypIndex 2 1) (HypIndex 2 1) Kf) (Sum.inl 0) (Sum.inl 0)) =
              (ζ : Kf) := by
            rw [hxmat, Matrix.diagonal_apply_eq]
            simp [torusEntries, aX]
          have hxmid : (((x : GL (HypIndex 2 1) Kf) :
              Matrix (HypIndex 2 1) (HypIndex 2 1) Kf)
                (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 0))) =
              (((ζ ^ 4 : Kfˣ) : Kf))⁻¹ := by
            rw [hxmat, Matrix.diagonal_apply_eq]
            simp [torusEntries, dX]
          have hy00 : (((y : GL (HypIndex 2 1) Kf) :
              Matrix (HypIndex 2 1) (HypIndex 2 1) Kf) (Sum.inl 0) (Sum.inl 0)) =
              (ω : Kf) := by
            rw [hymat, Matrix.diagonal_apply_eq]
            simp [torusEntries, aY]
          have hy11 : (((y : GL (HypIndex 2 1) Kf) :
              Matrix (HypIndex 2 1) (HypIndex 2 1) Kf) (Sum.inl 1) (Sum.inl 1)) =
              (1 : Kf) := by
            rw [hymat, Matrix.diagonal_apply_eq]
            simp [torusEntries, aY]
          have hxnot : x ∉ hypScalars h 2 1 := by
            intro hx
            obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hx
            have h1 : (ζ : Kf) = (c : Kf) := by
              have := congrArg (fun g : GL (HypIndex 2 1) Kf =>
                ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) Kf)
                  (Sum.inl 0) (Sum.inl 0))) hc
              simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hx00]
                using this
            have h2 : (((ζ ^ 4 : Kfˣ) : Kf))⁻¹ = (c : Kf) := by
              have := congrArg (fun g : GL (HypIndex 2 1) Kf =>
                ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) Kf)
                  (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 0)))) hc
              simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hxmid]
                using this
            have h2' : (((ζ : Kf) ^ 4))⁻¹ = (ζ : Kf) := by
              rw [← Units.val_pow_eq_pow_val]
              exact h2.trans h1.symm
            have hζ5 : (ζ : Kf) ^ 5 = 1 := by
              calc (ζ : Kf) ^ 5 = (ζ : Kf) ^ 4 * (ζ : Kf) := by
                    rw [show (5 : ℕ) = 4 + 1 by norm_num, pow_succ]
                _ = (ζ : Kf) ^ 4 * ((ζ : Kf) ^ 4)⁻¹ := by rw [h2']
                _ = 1 := mul_inv_cancel₀ (pow_ne_zero 4 (Units.ne_zero ζ))
            have hζ5u : ζ ^ 5 = 1 := Units.ext hζ5
            have hdvd : 25 ∣ 5 := by
              rw [← hζ]
              exact orderOf_dvd_of_pow_eq_one hζ5u
            norm_num at hdvd
          have hynot : y ∉ hypScalars h 2 1 := by
            intro hy
            obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hy
            have h1 : (ω : Kf) = (c : Kf) := by
              have := congrArg (fun g : GL (HypIndex 2 1) Kf =>
                ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) Kf)
                  (Sum.inl 0) (Sum.inl 0))) hc
              simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hy00]
                using this
            have h2 : (1 : Kf) = (c : Kf) := by
              have := congrArg (fun g : GL (HypIndex 2 1) Kf =>
                ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) Kf)
                  (Sum.inl 1) (Sum.inl 1))) hc
              simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hy11]
                using this
            exact hωne (Units.ext (h1.trans h2.symm))
          have hπx5 : (hypProj h 2 1 x) ^ 5 = 1 := by
            rw [← map_pow]
            exact MonoidHom.mem_ker.1 (by rwa [ker_hypProj])
          have hπy5 : (hypProj h 2 1 y) ^ 5 = 1 := by
            rw [← map_pow, hy5, map_one]
          have hπxne : hypProj h 2 1 x ≠ 1 := by
            intro h1
            have h2 : x ∈ (hypProj h 2 1).ker := MonoidHom.mem_ker.2 h1
            rw [ker_hypProj] at h2
            exact hxnot h2
          have hπyne : hypProj h 2 1 y ≠ 1 := by
            intro h1
            have h2 : y ∈ (hypProj h 2 1).ker := MonoidHom.mem_ker.2 h1
            rw [ker_hypProj] at h2
            exact hynot h2
          have hπxord : orderOf (hypProj h 2 1 x) = 5 :=
            orderOf_eq_prime hπx5 hπxne
          have hπyord : orderOf (hypProj h 2 1 y) = 5 :=
            orderOf_eq_prime hπy5 hπyne
          have hxy : Commute x y :=
            CFSG.Quasithin.H13.Sec53F.Unit.hypTorus_comm h hxT hyT
          have hcomm : ∀ a ∈ Subgroup.zpowers (hypProj h 2 1 x),
              a * hypProj h 2 1 y = hypProj h 2 1 y * a := by
            intro a ha
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
            exact ((hxy.map (hypProj h 2 1)).zpow_left k).eq
          have hπyNot : hypProj h 2 1 y ∉
              Subgroup.zpowers (hypProj h 2 1 x) := by
            intro hmem
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
            have hx5z : (hypProj h 2 1 x) ^ (5 : ℤ) = 1 := by
              rw [show (5 : ℤ) = (5 : ℕ) by norm_num, zpow_natCast, hπx5]
            have hkmod : (hypProj h 2 1 x) ^ k =
                (hypProj h 2 1 x) ^ ((k % 5).toNat : ℤ) := by
              rw [zpow_eq_zpow_emod' (x := hypProj h 2 1 x) k hx5z]
              congr 1
              exact (Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))).symm
            set j : ℕ := (k % 5).toNat with hj
            have hkj : (hypProj h 2 1 x) ^ j = hypProj h 2 1 y := by
              rw [← hk, hkmod, zpow_natCast]
            have hscal : x ^ j * y⁻¹ ∈ hypScalars h 2 1 := by
              have h1 : hypProj h 2 1 (x ^ j * y⁻¹) = 1 := by
                rw [map_mul, map_pow, map_inv, hkj, mul_inv_cancel]
              have h2 : x ^ j * y⁻¹ ∈ (hypProj h 2 1).ker := MonoidHom.mem_ker.2 h1
              rwa [ker_hypProj] at h2
            obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hscal
            let xT : hypTorus h 2 1 := ⟨x, hxT⟩
            let yT : hypTorus h 2 1 := ⟨y, hyT⟩
            let zT : hypTorus h 2 1 := xT ^ j * yT⁻¹
            have hxT0 : CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) xT = ζ := by
              apply Units.ext
              change ((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) xT : Kfˣ) : Kf) =
                (ζ : Kf)
              rw [CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 0 hxmat]
              simp [torusEntries, aX, xT]
            have hxT1 : CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) xT = ζ := by
              apply Units.ext
              change ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) xT : Kfˣ) : Kf) =
                (ζ : Kf)
              rw [CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 1 hxmat]
              simp [torusEntries, aX, xT]
            have hyT0 : CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) yT = ω := by
              apply Units.ext
              change ((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) yT : Kfˣ) : Kf) =
                (ω : Kf)
              rw [CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 0 hymat]
              simp [torusEntries, aY, yT]
            have hyT1 : CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) yT = 1 := by
              apply Units.ext
              change ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) yT : Kfˣ) : Kf) =
                (1 : Kf)
              rw [CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 1 hymat]
              simp [torusEntries, aY, yT]
            have hz0 : CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) zT =
                ζ ^ j * ω⁻¹ := by
              change CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2)
                (xT ^ j * yT⁻¹) = ζ ^ j * ω⁻¹
              rw [map_mul, map_pow, map_inv, hxT0, hyT0]
            have hz1 : CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) zT = ζ ^ j := by
              change CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2)
                (xT ^ j * yT⁻¹) = ζ ^ j
              rw [map_mul, map_pow, map_inv, hxT1, hyT1]
              simp
            have hzmat : (((zT : hypSU h 2 1) : GL (HypIndex 2 1) Kf) :
                Matrix (HypIndex 2 1) (HypIndex 2 1) Kf) =
                Matrix.diagonal (fun _ => (c : Kf)) := by
              have hzcoe : (zT : hypSU h 2 1) = x ^ j * y⁻¹ := by
                simp [zT, xT, yT]
              rw [hzcoe]
              have hg := congrArg (fun g : GL (HypIndex 2 1) Kf =>
                ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) Kf))) hc
              simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using hg
            have ht0 : CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) zT = c := by
              apply Units.ext
              change ((CFSG.RankThree.CentralLiftU.tcoord h (0 : Fin 2) zT : Kfˣ) : Kf) =
                (c : Kf)
              rw [CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 0 hzmat]
            have ht1 : CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) zT = c := by
              apply Units.ext
              change ((CFSG.RankThree.CentralLiftU.tcoord h (1 : Fin 2) zT : Kfˣ) : Kf) =
                (c : Kf)
              rw [CFSG.RankThree.CentralLiftU.coe_tcoord_of_diag h 1 hzmat]
            have h1 : ζ ^ j * ω⁻¹ = c := by rw [← hz0, ht0]
            have h2 : ζ ^ j = c := by rw [← hz1, ht1]
            have h3 : ζ ^ j * ω⁻¹ = ζ ^ j := h1.trans h2.symm
            have hz : (ζ : Kf) ^ j ≠ 0 := pow_ne_zero j (Units.ne_zero ζ)
            have h3K : (ζ : Kf) ^ j * ((ω : Kf))⁻¹ = (ζ : Kf) ^ j := by
              simpa using congrArg (fun u : Kfˣ => ((u : Kf))) h3
            have hinv : ((ω : Kf))⁻¹ = 1 := by
              apply mul_left_cancel₀ hz
              rw [mul_one]
              exact h3K
            have hω1 : (ω : Kf) = 1 := inv_eq_one.mp hinv
            exact hωne (Units.ext hω1)
          have hEA := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
            (r := 5) (G := hypPSU h 2 1)
            (X := Subgroup.zpowers (hypProj h 2 1 x)) (v := hypProj h 2 1 y)
            (by rw [Nat.card_zpowers, hπxord]) hπyord hπyNot hcomm
          obtain ⟨-, -, -, -, ⟨P₀, hP₀⟩, -, -⟩ :=
            unitary_order_and_Sylow h (r := 2) (ε := 1) (by norm_num) le_rfl
          have hxN : hypProj h 2 1 x ∈
              Subgroup.normalizer (P₀ : Set (hypPSU h 2 1)) := by
            have hxU : x ∈ Subgroup.normalizer
                (hypUnitriangular h 2 1 : Set (hypSU h 2 1)) := by
              have hSyl :=
                (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_Sylow_normalizers
                  h (r := 2) (ε := 1) (by norm_num) le_rfl).1
              rw [hSyl]
              exact hypTorus_le_hypBorel h hxT
            have hle := Subgroup.le_normalizer_map (H := hypUnitriangular h 2 1)
              (hypProj h 2 1) ⟨x, hxU, rfl⟩
            have hP : (P₀ : Subgroup (hypPSU h 2 1)) =
                (hypUnitriangular h 2 1).map (hypProj h 2 1) := by
              rw [hP₀]
              rfl
            have hPset : (P₀ : Set (hypPSU h 2 1)) =
                (((hypUnitriangular h 2 1).map (hypProj h 2 1) :
                  Subgroup (hypPSU h 2 1)) : Set (hypPSU h 2 1)) :=
              congrArg (fun S : Subgroup (hypPSU h 2 1) =>
                (S : Set (hypPSU h 2 1))) hP
            rw [hPset]
            exact hle
          have hyN : hypProj h 2 1 y ∈
              Subgroup.normalizer (P₀ : Set (hypPSU h 2 1)) := by
            have hyU : y ∈ Subgroup.normalizer
                (hypUnitriangular h 2 1 : Set (hypSU h 2 1)) := by
              have hSyl :=
                (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_Sylow_normalizers
                  h (r := 2) (ε := 1) (by norm_num) le_rfl).1
              rw [hSyl]
              exact hypTorus_le_hypBorel h hyT
            have hle := Subgroup.le_normalizer_map (H := hypUnitriangular h 2 1)
              (hypProj h 2 1) ⟨y, hyU, rfl⟩
            have hP : (P₀ : Subgroup (hypPSU h 2 1)) =
                (hypUnitriangular h 2 1).map (hypProj h 2 1) := by
              rw [hP₀]
              rfl
            have hPset : (P₀ : Set (hypPSU h 2 1)) =
                (((hypUnitriangular h 2 1).map (hypProj h 2 1) :
                  Subgroup (hypPSU h 2 1)) : Set (hypPSU h 2 1)) :=
              congrArg (fun S : Subgroup (hypPSU h 2 1) =>
                (S : Set (hypPSU h 2 1))) hP
            rw [hPset]
            exact hle
          have hF_le_N : Subgroup.zpowers (hypProj h 2 1 x) ⊔
              Subgroup.zpowers (hypProj h 2 1 y) ≤
              Subgroup.normalizer (P₀ : Set (hypPSU h 2 1)) :=
            sup_le (Subgroup.zpowers_le.mpr hxN) (Subgroup.zpowers_le.mpr hyN)
          have hW : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit
              (hypPSU h 2 1) 5 2 :=
            CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_borelWit_of_sylow P₀
              (Subgroup.zpowers (hypProj h 2 1 x) ⊔
                Subgroup.zpowers (hypProj h 2 1 y)) hF_le_N hEA.1 hEA.2
          obtain ⟨e0⟩ :=
            CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwex_equiv_quot_of_center_eq_bot hZ
          let eK : K ≃* hypPSU h 2 1 := e0.trans e
          let P₀K : Sylow 2 K := P₀.mapSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
          let FK : Subgroup K :=
            (Subgroup.zpowers (hypProj h 2 1 x) ⊔
              Subgroup.zpowers (hypProj h 2 1 y)).map eK.symm.toMonoidHom
          have hFK_le : FK ≤ Subgroup.normalizer (P₀K : Set K) := by
            have hP : (P₀K : Subgroup K) = (P₀ : Subgroup (hypPSU h 2 1)).map
                eK.symm.toMonoidHom := Sylow.coe_mapSurjective _ _
            change FK ≤ Subgroup.normalizer ((P₀K : Subgroup K) : Set K)
            rw [hP]
            have hmap := Subgroup.map_mono (f := eK.symm.toMonoidHom) hF_le_N
            have hnorm : (Subgroup.normalizer (P₀ : Set (hypPSU h 2 1))).map
                eK.symm.toMonoidHom = Subgroup.normalizer
                (((P₀ : Subgroup (hypPSU h 2 1)).map eK.symm.toMonoidHom :
                  Subgroup K) : Set K) := by
              simpa using Subgroup.map_equiv_normalizer_eq
                (H := (P₀ : Subgroup (hypPSU h 2 1))) (f := eK.symm)
            rw [hnorm] at hmap
            exact hmap
          exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_borelWit_of_sylow P₀K FK
            hFK_le (CFSG.SectionRank.isElemAbelian_map hEA.1 eK.symm.toMonoidHom)
            (by rw [Subgroup.card_map_of_injective eK.symm.injective, hEA.2])
        · have hbot : α.ker = ⊥ := by
            by_contra hne
            apply hZ
            have hcardN : Nat.card α.ker = 5 := by
              have hd : Nat.card α.ker ∣ 5 := hZcard ▸ Subgroup.card_dvd_of_le hker
              rcases (Nat.dvd_prime (by norm_num)).1 hd with h1 | h5
              · exact absurd (Subgroup.card_eq_one.1 h1) hne
              · exact h5
            have hEq : α.ker = hypScalars h 2 1 :=
              Subgroup.eq_of_le_of_card_ge hker (by rw [hcardN, hZcard])
            rw [eq_bot_iff]
            intro z hz
            obtain ⟨s0, rfl⟩ := hα z
            have h1 : (QuotientGroup.mk (α s0) : K ⧸ Subgroup.center K) = 1 :=
              (QuotientGroup.eq_one_iff _).2 hz
            rw [hαπ s0] at h1
            have h2 : hypProj h 2 1 s0 = 1 := by simpa using h1
            have h3 : s0 ∈ hypScalars h 2 1 := by
              rw [← ker_hypProj]
              exact h2
            rw [← hEq] at h3
            exact (MonoidHom.mem_ker.1 h3 : α s0 = 1) ▸ Subgroup.one_mem _
          obtain ⟨μ, hcardμ, hexpμ, hμ⟩ :=
            CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_exists_mu (h := h) (n := f)
              (ℓ := 5) (by norm_num) hsdvd
          exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_borelWit_core (h := h)
            (hμ := hμ) (hℓ := by norm_num) (hodd := by decide) (hcard := hcardμ)
            (hexp := hexpμ) (r := 2) (ε := 1) (hr := by norm_num) (hε := by norm_num)
            (X := K) (α := α) (hα := hα) (hinj := fun x hx => by
              apply CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_eq_one_of_hom_eq_one hμ x
              have : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_hom hμ x ∈ α.ker := hx
              rw [hbot] at this
              exact this)
      · have hs5dvd : ¬ s ∣ 2 * 2 + 1 := by
          intro hd
          exact hs5 ((Nat.prime_dvd_prime_iff_eq hs (by norm_num)).1 (by simpa using hd))
        exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_borelWit_of_lieModel
          (r := 2) (ε := 1) hq (by norm_num) le_rfl (by norm_num) hf hL hs hsdvd hs5dvd
  have h := (le_pRank_normalizerQuotient_of_borelWit hs hs2 hB S hS).1
  simpa using h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
