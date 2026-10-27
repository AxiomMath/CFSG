module

public import CFSG.RankThree.PartTwo.Sec17.Item174StarJ1
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Main
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.GL2Max
import CFSG.GH74.GLS.Stage4.T2CentSL
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartTwo.KFacts.AutPSpOrderThree
import CFSG.RankThree.PartTwo.Census.Classical.Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host

open CFSG Matrix CFSG.LargeExtraspecial.A2Mod CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves

private theorem eq_one_of_dvd_odd {G : Type} [Group G] {D : Subgroup G} (hD : IsPGroup 2 D)
    {k : G} (hkD : k ∈ D) {r : ℕ} (hr : Odd r) (hk : orderOf k ∣ r) : k = 1 := by
  obtain ⟨n, hn⟩ := hD ⟨k, hkD⟩
  have h1 : k ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  rcases m with _ | m
  · rw [pow_zero] at hm
    exact orderOf_eq_one_iff.mp hm
  · exfalso
    have : 2 ∣ r := (dvd_pow_self 2 (Nat.succ_ne_zero m)).trans (hm ▸ hk)
    exact (Nat.not_even_iff_odd.mpr hr) (even_iff_two_dvd.mpr this)

section SL3

variable {F : Type} [Field F] [Finite F]

private theorem commute_or_inv_of_mem_Nt {X : GL (Fin 2) F}
    (hX : X ∈ (Nt : Subgroup (GL (Fin 2) F))) :
    X * cGL = cGL * X ∨ X * cGL * X⁻¹ = cGL⁻¹ := by
  have hm : X * cGL * X⁻¹ ∈ Subgroup.zpowers (cGL (F := F)) :=
    (Subgroup.mem_normalizer_iff.mp hX _).mp (Subgroup.mem_zpowers _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
  rw [← zpow_mod_orderOf, orderOf_cGL] at hk
  have hr : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hr with h | h | h
  · exfalso
    rw [h, zpow_zero] at hk
    apply cGL_ne_one (F := F)
    have h' : X * cGL * X⁻¹ = 1 := hk.symm
    rw [mul_inv_eq_one] at h'
    calc cGL = X⁻¹ * (X * cGL) := by group
      _ = 1 := by rw [h', inv_mul_cancel]
  · left
    rw [h, zpow_one] at hk
    calc X * cGL = (X * cGL * X⁻¹) * X := by group
      _ = cGL * X := by rw [← hk]
  · right
    rw [← hk, h, eq_inv_iff_mul_eq_one]
    calc cGL (F := F) ^ ((2 : ℕ) : ℤ) * cGL = cGL ^ 3 := by
          rw [zpow_natCast, ← pow_succ]
      _ = 1 := cGL_pow_three

private theorem comm_of_le_P1 (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    (hmax : GL2NonsplitMax F) {I D : Subgroup (SL3 F)} (hIP : I ≤ P1)
    (hNI : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ I) (hDI : D ≤ I)
    (hD : IsPGroup 2 D) (hID : I ≤ Subgroup.normalizer (D : Set (SL3 F))) :
    ⁅D, (A0 : Subgroup (SL3 F))⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c : SL3 F := lev (cGL (F := F)) with hc_def
  have hcI : c ∈ I := hNI (Subgroup.le_normalizer (Subgroup.mem_zpowers c))
  set Ib := (I.subgroupOf P1).map rho1 with hIb
  set Db := (D.subgroupOf P1).map rho1 with hDb
  have hDb2 : IsPGroup 2 Db :=
    (hD.comap_of_injective P1.subtype (Subgroup.subtype_injective _)).map rho1
  have hDbIb : Db ≤ Ib := Subgroup.map_mono (fun y hy => hDI hy)
  have hIDP : I.subgroupOf P1 ≤ Subgroup.normalizer ((D.subgroupOf P1 : Subgroup P1) : Set P1) :=
    fun y hy => Subgroup.le_normalizer_comap P1.subtype (hID hy)
  have hIbD : Ib ≤ Subgroup.normalizer (Db : Set (GL (Fin 2) F)) :=
    (Subgroup.map_mono hIDP).trans (Subgroup.le_normalizer_map rho1)
  have hNtIb : (Nt : Subgroup (GL (Fin 2) F)) ≤ Ib := le_map_rho1 hNI
  have hcGL : cGL (F := F) ∈ (Nt : Subgroup (GL (Fin 2) F)) :=
    Subgroup.le_normalizer (Subgroup.mem_zpowers _)
  have hcGLD : cGL (F := F) ∈ Subgroup.normalizer (Db : Set (GL (Fin 2) F)) := hIbD (hNtIb hcGL)
  have hclaim : ∀ x ∈ Db, x * cGL = cGL * x := by
    rcases hmax Ib hNtIb with hEq | hSL
    · intro x hx
      have hxN : x ∈ (Nt : Subgroup (GL (Fin 2) F)) := hEq ▸ hDbIb hx
      rcases commute_or_inv_of_mem_Nt hxN with h | h
      · exact h
      · exact (not_inv_of_mem hDb2 orderOf_cGL hcGLD hx h).elim
    · haveI hN : (Db.comap
          (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F)).Normal := by
        constructor
        intro n hn g
        have hg : SpecialLinearGroup.toGL g ∈ Subgroup.normalizer (Db : Set (GL (Fin 2) F)) :=
          hIbD (hSL ⟨g, rfl⟩)
        rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hg _).mp hn
      set cS : SpecialLinearGroup (Fin 2) F := ⟨cMat, cMat_det⟩
      have hcS : SpecialLinearGroup.toGL cS = cGL (F := F) := Units.ext rfl
      rcases CFSG.GH74.GLS.Stage4.Rest.t2C_normal_sl2 h4
          (Db.comap (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F))
          with hC | hT
      · intro x hx
        set m := x * cGL * x⁻¹ * cGL⁻¹ with hm_def
        have hmD : m ∈ Db := by
          have h1 : cGL * x⁻¹ * cGL⁻¹ ∈ Db :=
            (Subgroup.mem_normalizer_iff.mp hcGLD _).mp (inv_mem hx)
          have h2 := mul_mem hx h1
          rwa [show x * (cGL * x⁻¹ * cGL⁻¹) = m by rw [hm_def]; group] at h2
        have hmR : m ∈ (SpecialLinearGroup.toGL :
            SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range := by
          rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, hm_def, map_mul, map_mul,
            map_mul, map_inv, map_inv, mul_right_comm (GeneralLinearGroup.det x), mul_inv_cancel,
            one_mul, mul_inv_cancel]
        obtain ⟨mS, hmS⟩ := hmR
        have hmc : m * cGL = cGL * m := by
          have hz := Subgroup.mem_center_iff.mp (hC (show mS ∈ Db.comap _ by
            rw [Subgroup.mem_comap, hmS]; exact hmD)) cS
          have := congrArg SpecialLinearGroup.toGL hz
          rw [map_mul, map_mul, hcS, hmS] at this
          exact this.symm
        have hm3 : m ^ 3 = 1 := by
          have hxc : x * cGL * x⁻¹ = m * cGL := by rw [hm_def]; group
          have h1 : (x * cGL * x⁻¹) ^ 3 = 1 := by
            rw [conj_pow, cGL_pow_three, mul_one, mul_inv_cancel]
          rw [hxc, (Commute.mul_pow hmc 3), cGL_pow_three, mul_one] at h1
          exact h1
        have hm1 : m = 1 := eq_one_of_dvd_odd hDb2 hmD (by decide : Odd 3)
          (orderOf_dvd_of_pow_eq_one hm3)
        rw [hm_def] at hm1
        calc x * cGL = (x * cGL * x⁻¹ * cGL⁻¹) * cGL * x := by group
          _ = cGL * x := by rw [hm1, one_mul]
      · exfalso
        have hcD : cGL (F := F) ∈ Db := by
          have : cS ∈ Db.comap SpecialLinearGroup.toGL := hT ▸ Subgroup.mem_top cS
          rwa [Subgroup.mem_comap, hcS] at this
        exact not_mem_of_orderOf_three hDb2 orderOf_cGL hcD
  refine commutator_zpowers_eq_bot fun d hd => ?_
  have hdP : d ∈ P1 := hIP (hDI hd)
  have hcP : c ∈ P1 := lev_mem_P1 _
  set k := d * c * d⁻¹ * c⁻¹ with hk_def
  have hkD : k ∈ D := by
    have h1 : c * d⁻¹ * c⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hID hcI) _).mp (inv_mem hd)
    have h2 := mul_mem hd h1
    rwa [show d * (c * d⁻¹ * c⁻¹) = k by rw [hk_def]; group] at h2
  have hkP : k ∈ P1 := mul_mem (mul_mem (mul_mem hdP hcP) (inv_mem hdP)) (inv_mem hcP)
  have hkQ : k ∈ (Q1 : Subgroup (SL3 F)) := by
    have hx : rho1 ⟨d, hdP⟩ ∈ Db := ⟨⟨d, hdP⟩, hd, rfl⟩
    have hrc : rho1 ⟨c, hcP⟩ = cGL := rho1_lev _
    have hkk : (⟨k, hkP⟩ : P1) = ⟨d, hdP⟩ * ⟨c, hcP⟩ * ⟨d, hdP⟩⁻¹ * ⟨c, hcP⟩⁻¹ := rfl
    refine (mem_ker_rho1 (g := (⟨k, hkP⟩ : P1))).mp ?_
    rw [hkk, map_mul, map_mul, map_mul, map_inv, map_inv, hrc, hclaim _ hx]
    group
  have hk1 : k = 1 := eq_one_of_dvd_odd hD hkD (r := Nat.card (Q1 : Subgroup (SL3 F)))
    (by rw [card_Q1]; exact hodd.pow) (Subgroup.orderOf_dvd_natCard _ hkQ)
  calc d * c = (d * c * d⁻¹ * c⁻¹) * c * d := by group
    _ = c * d := by rw [← hk_def, hk1, one_mul]

private theorem eq_bot_of_transitive (hq : Nat.card F % 3 = 2) {I D : Subgroup (SL3 F)}
    (htr : ∀ v : Fin 3 → F, v ≠ 0 → InOrbit I v) (hDI : D ≤ I) (hD : IsPGroup 2 D)
    (hID : I ≤ Subgroup.normalizer (D : Set (SL3 F))) : D = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd ((P1 : Subgroup (SL3 F)).relIndex I) := by
    rw [relIndex_P1_of_transitive htr, index_P1]
    have : Even (Nat.card F ^ 2 + Nat.card F) := by
      rw [show Nat.card F ^ 2 + Nat.card F = Nat.card F * (Nat.card F + 1) by ring]
      exact Nat.even_mul_succ_self _
    exact this.add_one
  set A := (P1 : Subgroup (SL3 F)).subgroupOf I
  set Y := D.subgroupOf I
  haveI : Y.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDI).mpr hID
  have hY : IsPGroup 2 Y := hD.comap_of_injective _ (Subgroup.subtype_injective _)
  have h1 : A.relIndex (Y ⊔ A) ∣ A.index := by
    rw [← Subgroup.relIndex_top_right]
    exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex A (Y ⊔ A) ⊤ le_sup_right le_top)
  rw [relIndex_sup_normal] at h1
  have h2 : A.relIndex Y ∣ Nat.card Y := Subgroup.relIndex_dvd_card A Y
  obtain ⟨n, hn⟩ := hY.exists_card_eq
  rw [hn] at h2
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hm0 : m = 0 := by
    rcases m with _ | m
    · rfl
    · exfalso
      have : 2 ∣ A.index := (dvd_pow_self 2 (Nat.succ_ne_zero m)).trans (hm ▸ h1)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  rw [hm0, pow_zero, Subgroup.relIndex_eq_one] at hm
  have hDP : ∀ d ∈ D, d ∈ P1 := fun d hd => hm (show (⟨d, hDI hd⟩ : I) ∈ Y from hd)
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  have heig : ∀ v : Fin 3 → F, v ≠ 0 →
      ∃ a : F, a • ((d : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
    intro v hv
    obtain ⟨g, hg, c, hc, hgc⟩ := htr v hv
    have hgd : g⁻¹ * d * g ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (hID (I.inv_mem hg)) d).mp hd
      rwa [inv_inv] at this
    obtain ⟨a, ha⟩ := mem_P1_iff_exists.mp (hDP _ hgd)
    have hgrp : d * g = g * (g⁻¹ * d * g) := by group
    have hv1 : (d : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ e0) =
        a • ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ e0) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, hgrp, Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_smul]
    rw [hgc, Matrix.mulVec_smul, smul_comm a c] at hv1
    have hv2 : (d : Matrix (Fin 3) (Fin 3) F) *ᵥ v = a • v :=
      smul_right_injective (Fin 3 → F) hc hv1
    have ha0 : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_smul] at hv2
      apply hv
      have := CFSG.LargeExtraspecial.A2Mod.sl_inv_mulVec_mulVec d v
      rw [hv2, Matrix.mulVec_zero] at this
      exact this.symm
    exact ⟨a⁻¹, by rw [hv2, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩
  obtain ⟨s, hs⟩ := CFSG.RankThree.PartTwo.KFacts.exists_eq_smul_one_of_forall heig
  have hdet : (d : Matrix (Fin 3) (Fin 3) F).det = 1 := d.2
  rw [hs, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at hdet
  have hs1 := cube_eq_one_imp hq hdet
  exact Subtype.ext (by rw [hs, hs1, one_smul, Matrix.SpecialLinearGroup.coe_one])

private theorem comm_A0 (hq : Nat.card F % 3 = 2) (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hmax : GL2NonsplitMax F) {I D : Subgroup (SL3 F)}
    (hNI : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ I) (hDI : D ≤ I)
    (hD : IsPGroup 2 D) (hID : I ≤ Subgroup.normalizer (D : Set (SL3 F))) :
    ⁅D, (A0 : Subgroup (SL3 F))⁆ = ⊥ := by
  have h4 : 4 ≤ Nat.card F := by omega
  have hroot := sq_add_self_add_one_ne_zero hq
  have hcube := exists_cube hq
  have hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) → lev X ∈ I :=
    fun X hX => hNI (lev_mem_normalizer_A0 (mem_Nt_of_comm hX))
  rcases le_P1_or_le_P2_or_transitive hroot hcube hlev with h | h | h
  · exact comm_of_le_P1 hodd h4 hmax h hNI hDI hD hID
  · have h' := comm_of_le_P1 hodd h4 hmax (I := I.map (dualAut (F := F)).toMonoidHom)
      (D := D.map (dualAut (F := F)).toMonoidHom)
      (by rintro _ ⟨x, hx, rfl⟩; exact dualAut_mem_P1 (h hx))
      (by rw [← map_dualAut_normalizer_A0]; exact Subgroup.map_mono hNI)
      (Subgroup.map_mono hDI) (hD.map _)
      (by rw [← Subgroup.map_equiv_normalizer_eq]; exact Subgroup.map_mono hID)
    rw [← map_dualAut_A0, ← Subgroup.map_commutator] at h'
    exact (Subgroup.map_eq_bot_iff_of_injective _ (dualAut (F := F)).injective).mp h'
  · rw [eq_bot_of_transitive hq h hDI hD hID, Subgroup.commutator_bot_left]

private theorem starCore_SL3 (hq : Nat.card F % 3 = 2)
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hcyc : ∀ X : Subgroup (SL3 F), IsPGroup 3 X → IsCyclic X) : StarCore (SL3 F) := by
  intro _ t ht I hI D hDI hD hID hc
  exfalso
  apply hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_eq_three hcyc card_A0
    (show Nat.card (Subgroup.zpowers t) = 3 by rw [Nat.card_zpowers, ht])
  set φ := (MulAut.conj g).toMonoidHom with hφ_def
  have hφ : Function.Injective φ := (MulAut.conj g).injective
  have hφs : Function.Surjective φ := (MulAut.conj g).surjective
  have key := comm_A0 hq hodd h5 (gl2NonsplitMax hq h5) (I := I.comap φ) (D := D.comap φ)
    (by
      intro x hx
      show φ x ∈ I
      apply hI
      rw [hg, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨x, hx, rfl⟩)
    (Subgroup.comap_mono hDI) (hD.comap_of_injective φ hφ)
    (fun x hx => Subgroup.le_normalizer_comap φ (hID hx))
  have := congrArg (Subgroup.map φ) key
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hφs, ← hg,
    Subgroup.map_bot] at this
  exact this

end SL3

theorem starL3Odd_proved : StarL3Odd := by
  intro H _ _ d q hp2 hq hd ⟨e⟩
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := GaloisField q.p q.exponent
  have hF : Nat.card F = q.card := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def]
  have hqF : Nat.card F % 3 = 2 := by rw [hF]; exact hq
  have hodd : Odd (Nat.card F) := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne']
    exact (q.prime_p.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ Nat.card F := by
    obtain ⟨k, hk⟩ := hodd
    have h2 : 2 ≤ Nat.card F := by
      rw [hF, TauCeti.PrimePower.card_def]
      exact Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt
    omega
  have eS : SL3 F ≃* CFSG.PGLModel.projSL 3 F :=
    ((pslEquivSL3 hqF).symm.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm).trans
      (CFSG.RankThree.PartTwo.Census.typeAGroupEquivProjSL 2 q hv)
  have hcyc : ∀ X : Subgroup (SL3 F), IsPGroup 3 X → IsCyclic X := by
    intro X hX
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
    have := CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_of_mulEquiv_projSL hqF eS Q
    exact Subgroup.isCyclic_of_le hQ
  exact starFor_of_starCore (starCore_of_mulEquiv
    ((e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans (pslEquivSL3 hqF))
    (starCore_SL3 hqF hodd h5 hcyc))

theorem kfactStar_of_U3
    (hS : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOneSimple) (hU3 : StarU3) :
    KFactStar :=
  kfactStar_of_L3U3 hS starL3Odd_proved hU3

end CFSG.RankThree.PartTwo.Sec17.Proof174Host
