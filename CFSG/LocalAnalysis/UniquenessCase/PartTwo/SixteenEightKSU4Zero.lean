module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSUComm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSU4ZeroA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSU4ZeroB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_su4_zero (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSU : IsSUn ↥(lBar V₀ V hV L) 4 1)
    (hN : NatSUn (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 4 1)
    (hσ : 3 ∈ D.sig) (hrk : 4 ≤ CFSG.Open.pRank 3 (Mbar D.M V₀ V hV))
    (hZ : fixV (lBar V₀ V hV L) = ⊥) : False := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, hR⟩ := hN
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hK4 : Nat.card K = 4 := by simpa using hKcard
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1)
      (by rw [hK4]; norm_num)
  let σ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K 2 1
  have hσu : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
      (by rw [hK4]; norm_num)
  have hσapply : ∀ x : K, σ x = x ^ 2 := fun x => by
    rw [show σ = CFSG.LieType.BorelTits.unitaryInvolution K 2 1 from rfl,
      CFSG.LieType.BorelTits.unitaryInvolution_apply, pow_one]
  let Γ : Subgroup (GL (Fin 4) K) := StatedSU 4 2 K
  have hRΓ : (FFModel.nat Γ).Realizes (lBar V₀ V hV L) ⊤
      (fixV (lBar V₀ V hV L)) := by
    simpa [Γ, h.comm_top, top_inf_eq] using hR
  have hHA : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV h.setting.hyp151.le
  have hHn : ∀ a ∈ Mbar D.M V₀ V hV, ∀ x ∈ lBar V₀ V hV L,
      a * x * a⁻¹ ∈ lBar V₀ V hV L := by
    intro a ha x hx
    exact (Subgroup.mem_normalizer_iff.1 (h.mBar_le_normalizer ha) x).1 hx
  obtain ⟨π, β, ρ, hβsurj, hβker, hρinj, hρN, hβeq, hπact⟩ :=
    s16k_exists_embedding_equiv (W := Vtil V₀ V hV)
      (A := Mbar D.M V₀ V hV) (H := lBar V₀ V hV L) hHA hHn hRΓ h.comm_top
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxfix : x ∈ fixV (lBar V₀ V hV L) := (hβker x).1 hx
    rw [hZ] at hxfix
    exact Subgroup.mem_bot.1 hxfix
  obtain ⟨E, hErange, hEel, hEcard⟩ :=
    s16g_exists_elem_of_le_pRank ρ hρinj Nat.prime_three hrk
  have hEN : E ≤ s16gNorm Γ :=
    hErange.trans (s16g_range_le_norm (ι := Fin 4) (K := K) hρN)
  have hAdd : AddCommutantScalar Γ := by
    simpa [Γ] using s16k_addCommutantScalar_statedSU hK4 (by norm_num : 3 ≤ 4)
  have hcardAut : Nat.card (RingAut K) = 2 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
      (n := 2) (by rw [hK4]; norm_num)).1
  have h3Aut : ¬ 3 ∣ Nat.card (RingAut K) := by
    rw [hcardAut]
    norm_num
  have hEL : E ≤ s16gLin (Fin 4) K :=
    s16g_le_lin_of_coprime hAdd Nat.prime_three h3Aut hEN hEel.isPGroup
  obtain ⟨F, hFN, hFE⟩ := s16g_exists_matrix_subgroup hEN hEL
  have hF_eq : F = E.comap (s16gNatHom (Fin 4) K) := by
    ext x
    constructor
    · intro hx
      exact Subgroup.mem_comap.mpr (by rw [← hFE]; exact Subgroup.mem_map_of_mem _ hx)
    · intro hx
      rw [Subgroup.mem_comap] at hx
      rw [← hFE] at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hyx' : y = x := s16gNatHom_injective hyx
      rwa [hyx'] at hy
  have hF : IsElemAbelian 3 F := by
    rw [hF_eq]
    exact hEel.comap (s16gNatHom_injective (ι := Fin 4) (K := K))
  have hcardFE : Nat.card F = Nat.card E := by
    rw [← hFE]
    exact (Subgroup.card_map_of_injective
      (s16gNatHom_injective (ι := Fin 4) (K := K))).symm
  have hFcard : 81 ≤ Nat.card F := by
    rw [hcardFE]
    simpa using hEcard
  obtain ⟨B₁, B₂, w₁, w₂, hB₁F, hB₂F, hB₁p, hB₂p, hB₁card, hB₂card,
    hB₁nc, hB₂nc, hw₁, hw₁norm, hw₂, hw₂norm, hB₁fix, hB₂fix⟩ :=
    s16k_exists_torus_pair (K := K) hK4 hFN hF hFcard
  have hfixnorm : ∀ x : K, σ x = x → x = 0 ∨ x = 1 := by
    intro x hx
    have hx2 : x ^ 2 = x := by
      have h := hx
      rw [show σ = CFSG.LieType.BorelTits.unitaryInvolution K 2 1 from rfl] at h
      rwa [CFSG.LieType.BorelTits.unitaryInvolution_apply, pow_one] at h
    have h : x * (x - 1) = 0 := by linear_combination hx2
    rcases mul_eq_zero.mp h with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h0)
  have hval : ∀ y : Fin 4 → K, herm σ y y = 0 ∨ herm σ y y = 1 := fun y =>
    hfixnorm (herm σ y y) (herm_self_fixed σ hσu.invol y)
  have hSUeq : SUid σ 4 = StatedSU 4 2 K := by
    change SUid (frobeniusEquiv K 2) 4 = StatedSU 4 2 K
    simpa using CFSG.LieType.Universal.Unitary.SUid_eq_statedSU
      (p := 2) (f := 1) (by rw [hK4]; norm_num) 4
  have hρπ : ∀ A : ↥Γ, ρ ⟨π A, hHA (π A).2⟩ =
      s16gNatHom (Fin 4) K (A : GL (Fin 4) K) := by
    intro A
    ext y
    obtain ⟨z, rfl⟩ := hβsurj y
    rw [← hβeq, hπact]
  have hkey : ∀ (v : Vtil V₀ V hV) (C : Subgroup (GL (Fin 4) K)) (w : Fin 4 → K) (k : ℕ),
      C ≤ F → IsPGroup 3 C → Nat.card C = 3 ^ k → 2 ≤ k →
      ¬ IsCyclic ↥C → (∀ b ∈ C, (b : Matrix (Fin 4) (Fin 4) K) *ᵥ w = w) →
      w ≠ 0 → β v ≠ 1 → (herm σ (β v) (β v) = 1 ∧ herm σ w w = 1) ∨
        (herm σ (β v) (β v) = 0 ∧ herm σ w w = 0) →
      ∃ B : Subgroup (MulAut (Vtil V₀ V hV)),
        B ≤ Mbar D.M V₀ V hV ∧ IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧
        ∀ b ∈ B, b v = v := by
    intro v C w k hCF hCp hCcard hk2 hCnc hCw hwne hv0 hnorm
    have hCexp : ∀ c ∈ C, c ^ 3 = 1 := fun c hc => hF.2 c (hCF hc)
    have hv0' : Multiplicative.toAdd (β v) ≠ 0 := fun h =>
      hv0 (toAdd_eq_zero.mp h)
    have hexA : ∃ A : ↥Γ, (A : GL (Fin 4) K) ∈ StatedSU 4 2 K ∧
        s16gNatHom (Fin 4) K (A : GL (Fin 4) K) (Multiplicative.ofAdd w) = β v := by
      rcases hnorm with ⟨hy1, hw1⟩ | ⟨hy0, hw0⟩
      · obtain ⟨t, -, ht⟩ :=
          CFSG.ClassicalGroups.Unitary.exists_mem_T_smul_eq_of_norm_one hσu
            (Or.inl (by norm_num : 4 ≤ 4)) hw1 hy1
        let Agl : Matrix.GeneralLinearGroup (Fin 4) K :=
          (t : Matrix.GeneralLinearGroup (Fin 4) K)
        have hmem : Agl ∈ SUid σ 4 := (t : SUid σ 4).2
        have hAgl : Agl ∈ StatedSU 4 2 K := hSUeq ▸ hmem
        let A : ↥Γ := ⟨Agl, hAgl⟩
        exact ⟨A, hAgl, by
          simpa only [A, Agl, CFSG.ClassicalGroups.Unitary.smul_def, s16gNatHom_apply,
            toAdd_ofAdd]
            using (congrArg Multiplicative.ofAdd ht).trans
              (ofAdd_toAdd (β v))⟩
      · obtain ⟨t, -, ht⟩ :=
          CFSG.ClassicalGroups.Unitary.exists_mem_T_smul_eq_of_iso hσu
            (by norm_num : 3 ≤ 4) hwne hw0 hv0' hy0
        let Agl : Matrix.GeneralLinearGroup (Fin 4) K :=
          (t : Matrix.GeneralLinearGroup (Fin 4) K)
        have hmem : Agl ∈ SUid σ 4 := (t : SUid σ 4).2
        have hAgl : Agl ∈ StatedSU 4 2 K := hSUeq ▸ hmem
        let A : ↥Γ := ⟨Agl, hAgl⟩
        exact ⟨A, hAgl, by
          simpa only [A, Agl, CFSG.ClassicalGroups.Unitary.smul_def, s16gNatHom_apply,
            toAdd_ofAdd]
            using (congrArg Multiplicative.ofAdd ht).trans
              (ofAdd_toAdd (β v))⟩
    obtain ⟨A, hAΓ, hAw⟩ := hexA
    let a : ↥(Mbar D.M V₀ V hV) := ⟨π A, hHA (π A).2⟩
    let A' : MulAut (Multiplicative (Fin 4 → K)) :=
      s16gNatHom (Fin 4) K (A : GL (Fin 4) K)
    have hρa : ρ a = A' := by
      ext y
      obtain ⟨z, rfl⟩ := hβsurj y
      rw [← hβeq, hπact]
    set Cmap : Subgroup (MulAut (Multiplicative (Fin 4 → K))) :=
      C.map (s16gNatHom (Fin 4) K) with hCmap_def
    set E' : Subgroup (MulAut (Multiplicative (Fin 4 → K))) :=
      Cmap.map (MulAut.conj A').toMonoidHom with hE'_def
    have hCmap_range : Cmap ≤ ρ.range := by
      rintro y ⟨c, hc, rfl⟩
      have hcE : s16gNatHom (Fin 4) K c ∈ E := by
        rw [← hFE]
        exact Subgroup.mem_map_of_mem _ (hCF hc)
      exact hErange hcE
    have hA'range : A' ∈ ρ.range := ⟨a, hρa⟩
    have hconjmem : ∀ g ∈ ρ.range, ∀ y ∈ ρ.range, MulAut.conj g y ∈ ρ.range := by
      rintro g ⟨mg, rfl⟩ y ⟨my, rfl⟩
      refine ⟨mg * my * mg⁻¹, ?_⟩
      rw [MulAut.conj_apply]
      simp only [map_mul, map_inv]
    have hE'range : E' ≤ ρ.range := by
      rintro y ⟨z, hz, rfl⟩
      exact hconjmem A' hA'range z (hCmap_range hz)
    have hCmap_p : IsPGroup 3 Cmap := by
      rw [hCmap_def]
      exact hCp.map (s16gNatHom (Fin 4) K)
    have hE'p : IsPGroup 3 E' := by
      rw [hE'_def]
      exact hCmap_p.map (MulAut.conj A').toMonoidHom
    let B : Subgroup (MulAut (Vtil V₀ V hV)) :=
      (E'.comap ρ).map (Mbar D.M V₀ V hV).subtype
    have hBle : B ≤ Mbar D.M V₀ V hV := Subgroup.map_subtype_le _
    have hBp : IsPGroup 3 B := by
      have h1 : IsPGroup 3 (E'.comap ρ) := hE'p.comap_of_injective ρ hρinj
      exact h1.map (Mbar D.M V₀ V hV).subtype
    have hBcard : Nat.card B = Nat.card C := by
      calc Nat.card B = Nat.card (E'.comap ρ) :=
            Subgroup.card_map_of_injective (Mbar D.M V₀ V hV).subtype_injective
        _ = Nat.card ((E'.comap ρ).map ρ) :=
            (Subgroup.card_map_of_injective hρinj).symm
        _ = Nat.card E' := by
            rw [Subgroup.map_comap_eq, inf_eq_right.mpr hE'range]
        _ = Nat.card Cmap := by
            let fConj : MulAut (Multiplicative (Fin 4 → K)) →*
                MulAut (Multiplicative (Fin 4 → K)) := (MulAut.conj A').toMonoidHom
            have hfConj : Function.Injective fConj := (MulAut.conj A').injective
            have hE'map : E' = Cmap.map fConj := hE'_def
            rw [hE'map]
            exact Subgroup.card_map_of_injective hfConj
        _ = Nat.card C :=
            Subgroup.card_map_of_injective (s16gNatHom_injective (ι := Fin 4) (K := K))
    have hBexp : ∀ b : ↥B, b ^ 3 = 1 := by
      intro b
      obtain ⟨m, hm, hmb⟩ := Subgroup.mem_map.mp b.2
      have hmE' : ρ m ∈ E' := hm
      obtain ⟨cm, hcm, hcm_eq⟩ := Subgroup.mem_map.mp hmE'
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hcm
      have hc3 : c ^ 3 = 1 := hCexp c hc
      have hnat3 : (s16gNatHom (Fin 4) K c) ^ 3 = 1 := by
        rw [← map_pow, hc3, map_one]
      have hρm3 : (ρ m) ^ 3 = 1 := by
        rw [← hcm_eq]
        change ((MulAut.conj A') (s16gNatHom (Fin 4) K c)) ^ 3 = 1
        rw [← map_pow, hnat3, map_one]
      have hm3 : m ^ 3 = 1 := by
        apply hρinj
        rw [map_pow, hρm3, map_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      rw [show (b : MulAut (Vtil V₀ V hV)) = m from hmb.symm]
      simpa using congrArg (fun z : ↥(Mbar D.M V₀ V hV) =>
        (z : MulAut (Vtil V₀ V hV))) hm3
    have hBnc : ¬ IsCyclic ↥B :=
      s16k_not_isCyclic_of_card_pow (p := 3) (k := k) Nat.prime_three hk2
        (by rw [hBcard, hCcard]) hBexp
    have hBfix : ∀ b ∈ B, b v = v := by
      intro b hb
      obtain ⟨m, hm, hmb⟩ := Subgroup.mem_map.mp hb
      apply hβinj
      rw [show (b : MulAut (Vtil V₀ V hV)) = m from hmb.symm]
      rw [hβeq]
      have hmE' : ρ m ∈ E' := hm
      obtain ⟨cm, hcm, hcm_eq⟩ := Subgroup.mem_map.mp hmE'
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hcm
      have hAinv : A'⁻¹ (β v) = Multiplicative.ofAdd w := by
        have hA'w : A' (Multiplicative.ofAdd w) = β v := hAw
        have h := congrArg (fun z => (A'⁻¹ : MulAut (Multiplicative (Fin 4 → K))) z) hA'w
        simpa only [MulAut.inv_apply_self] using h.symm
      have hCwM : s16gNatHom (Fin 4) K c (Multiplicative.ofAdd w) =
          Multiplicative.ofAdd w := by
        simpa only [s16gNatHom_apply, toAdd_ofAdd] using
          congrArg Multiplicative.ofAdd (hCw c hc)
      have hρm : ρ m = A' * s16gNatHom (Fin 4) K c * A'⁻¹ := by
        rw [← hcm_eq]
        rfl
      rw [hρm]
      calc (A' * s16gNatHom (Fin 4) K c * A'⁻¹) (β v) =
          A' (s16gNatHom (Fin 4) K c (A'⁻¹ (β v))) := by simp [MulAut.mul_apply]
        _ = A' (s16gNatHom (Fin 4) K c (Multiplicative.ofAdd w)) := by rw [hAinv]
        _ = A' (Multiplicative.ofAdd w) := by rw [hCwM]
        _ = β v := hAw
    exact ⟨B, hBle, hBp, hBnc, hBfix⟩
  refine s16g_false_of_fix D h.std (hV := hV) h.setting Nat.prime_three hσ ?_
  intro y hy1
  have hyne : β y ≠ 1 := by
    intro h1
    have hyfix : y ∈ fixV (lBar V₀ V hV L) := (hβker y).1 h1
    rw [hZ] at hyfix
    exact hy1 (Subgroup.mem_bot.1 hyfix)
  have hynorm : (herm σ (β y) (β y) = 1 ∧ herm σ w₁ w₁ = 1) ∨
      (herm σ (β y) (β y) = 0 ∧ herm σ w₂ w₂ = 0) := by
    rcases hval (β y) with h0 | h1
    · exact Or.inr ⟨h0, hw₂norm⟩
    · exact Or.inl ⟨h1, hw₁norm⟩
  by_cases hcase : herm σ (β y) (β y) = 1
  · exact hkey y B₁ w₁ 3 hB₁F hB₁p (by rw [hB₁card]; norm_num) (by norm_num) hB₁nc hB₁fix hw₁ hyne
      (Or.inl ⟨hcase, hw₁norm⟩)
  · have hcase0 : herm σ (β y) (β y) = 0 := by
      rcases hval (β y) with h0 | h1
      · exact h0
      · exact absurd h1 hcase
    exact hkey y B₂ w₂ 2 hB₂F hB₂p (by rw [hB₂card]; norm_num) (by norm_num) hB₂nc hB₂fix hw₂ hyne
      (Or.inr ⟨hcase0, hw₂norm⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
