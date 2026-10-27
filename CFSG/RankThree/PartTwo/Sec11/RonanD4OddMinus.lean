module

public import CFSG.RankThree.PartTwo.Sec11.RonanD4OddKill
public import CFSG.RankThree.PartTwo.Sec11.RonanD4OddHeis
public import CFSG.RankThree.PartTwo.Sec11.RonanD4OddHeisU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Unit

public section

namespace CFSG.RankThree.PartTwo.Sec11.RonanD4Odd

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.RootWalk CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.SP
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 renaming fixSub → fixSubO
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


noncomputable abbrev unC {K : Type} [Field K] [Finite K] (σ ε : K ≃+* K)
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  foldFix ((MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ : MulAut
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊓
      foldFix ((unTau σ ε : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

section Core

theorem unitary_core_heis {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2)
    (hq5 : 5 ≤ p ^ f) {K : Type} [Field K] [Finite K] [CharP K p] {σ ε : K ≃+* K}
    (hK : Nat.card K = ((p ^ f) ^ 4) ^ 3) (hσ : ∀ c, σ c = c ^ ((p ^ f) ^ 4))
    (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9)) {b : Kˣ} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1]) :
    ∃ (J : Subgroup ↥(unC σ ε s)) (_ : J.Normal), CFSG.IsQuasisimple ↥J ∧
      Group.IsSolvable (↥(unC σ ε s) ⧸ J) ∧
      ∃ x y : ↥(unC σ ε s), x ∈ J ∧ y ∈ J ∧ x ≠ 1 ∧ x ^ 3 = 1 ∧ y ^ 3 = 1 ∧
        Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧ y ∉ Subgroup.zpowers x := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set q := p ^ f with hqdef
  set q₄ := q ^ 4 with hq₄def
  have hq2 : 2 ≤ q := by omega
  have hq4two : 2 ≤ q₄ := by
    calc 2 ≤ q := hq2
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hmod : q₄ % 3 = 1 := by rw [hq₄def, Nat.pow_mod, hq]
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hb3' : (b : K) ^ 3 = 1 := by
    have := congrArg Units.val hb3
    simpa using this
  have hbσ : Units.map σ.toRingHom.toMonoidHom b = b := by
    apply Units.ext
    show σ (b : K) = b
    rw [hσ]
    obtain ⟨k, hk⟩ : ∃ k, q₄ = 3 * k + 1 := ⟨q₄ / 3, by omega⟩
    rw [hk, pow_succ, pow_mul, hb3', one_pow, one_mul]
  have hεb : Units.map ε.toRingHom.toMonoidHom b = b⁻¹ := by
    apply Units.ext
    show ε (b : K) = ((b⁻¹ : Kˣ) : K)
    rw [hε]
    have h9 : (q ^ 9) % 3 = 2 := by rw [Nat.pow_mod, hq]
    obtain ⟨k, hk⟩ : ∃ k, q ^ 9 = 3 * k + 2 := ⟨q ^ 9 / 3, by omega⟩
    have hb2 : (b : K) ^ 2 = ((b⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ]
      exact hb3'
    rw [hk, pow_add, pow_mul, hb3', one_pow, one_mul, hb2]
  have hA : A2Std σ b q₄ := ⟨hq4two, hK, hσ, hmod, hodd, hbσ, hb3, hb1⟩
  have hε4 : ∀ c, ε (ε (ε (ε c))) = c := by
    intro c
    simp only [hε]
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    have hN : Nat.card K = q₄ ^ 3 := hK
    have hpowN : ∀ n : ℕ, c ^ (Nat.card K ^ n) = c := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, pow_mul, ih]
        haveI : Fintype K := Fintype.ofFinite K
        rw [Nat.card_eq_fintype_card, FiniteField.pow_card]
    have : q ^ 9 * (q ^ 9 * (q ^ 9 * q ^ 9)) = Nat.card K ^ 3 := by
      rw [hN, hq₄def]
      ring
    rw [this]
    exact hpowN 3
  obtain ⟨μ, hμ, hμε⟩ := exists_mu_unitary (p := p) (f := f) hf hA.toCore rfl hε hεb hε4
  set φ₄ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ with hφ₄
  have hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ₄ y : ModGL TwistTag.D4.tag K) = a2Conj σ b (y : ModGL TwistTag.D4.tag K) :=
    a2_hφ_of_class (σ := σ) (d := b) hs
  obtain ⟨ρ, hnt, hcard, h1, h2, h3, h4, h5, h6⟩ :=
    exists_hom_fixSub_mu hA.toCore φ₄ hφ μ hμ
  obtain ⟨hker, hN, hsolv⟩ := sl3_hom_structure ρ hnt hcard
  have hcompat := tau_rho_compat hA.toCore φ₄ ρ hμε h1 h2 h3 h4 h5 h6
  have hFcard : Nat.card (fixSubfield σ) = q₄ :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hA.two_le hA.card hA.frob
  haveI hFchar : CharP (fixSubfield σ) p :=
    ((fixSubfield σ).subtype.charP_iff (fixSubfield σ).subtype_injective p).2 inferInstance
  let σQ : fixSubfield σ ≃+* fixSubfield σ := fixSubfieldRestrict ε σ
  have hσQ : ∀ c : fixSubfield σ, σQ c = c ^ (p ^ f) :=
    eps_restrict_frob (Q := p ^ f) rfl hσ hε
  obtain ⟨F₂, hF₂, ⟨e⟩⟩ := stdUnitary_equiv_fin (ℓ := p) (f := f) (ν := 3) hp
    (L := ↥(fixSubfield σ)) hf σQ hσQ le_rfl (by rw [hFcard])
  haveI hF₂char : CharP ↥F₂ p := (F₂.subtype.charP_iff F₂.subtype_injective p).2 inferInstance
  let θ : SL(3, fixSubfield σ) ≃* SL(3, fixSubfield σ) := stdUnitaryEquiv (ν := 3) σQ
  let S : Subgroup SL(3, fixSubfield σ) :=
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup θ
  have hSmem : ∀ x, x ∈ S ↔ θ x = x := fun x =>
    CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup
  have hFD : LieFactorData p ↥(StatedSU 3 (p ^ f) ↥F₂) :=
    lieFactorData_statedSU_three hp hF₂ hq5
  have hSperf : Group.IsPerfect ↥S := ⟨(hFD.of_mulEquiv e).perfect⟩
  let ρY : SL(3, fixSubfield σ) →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (fixSubO φ₄).subtype.comp ρ
  let τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := unTau σ ε
  have hτρ : ∀ x, τ.toMonoidHom (ρY x) = ρY (θ.toMonoidHom x) := fun x => hcompat x
  have hkerY : ρY.ker ≤ Subgroup.center SL(3, fixSubfield σ) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact Subtype.ext hx
  have hrange_le : ρY.range ≤ fixSubO φ₄ := by
    rintro _ ⟨x, rfl⟩
    exact (ρ x).2
  have hrng : ρY.range.subgroupOf (fixSubO φ₄) = ρ.range := by
    ext ⟨c, hc⟩
    simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, congrArg Subtype.val hx⟩
  haveI hN' : (ρY.range.subgroupOf (fixSubO φ₄)).Normal := by
    rw [hrng]
    exact hN
  have hsolv' : Group.IsSolvable (↥(fixSubO φ₄) ⧸ ρY.range.subgroupOf (fixSubO φ₄)) := by
    have e' := QuotientGroup.quotientMulEquivOfEq hrng
    exact Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
  have hC' : ∀ g, g ∈ foldFix (φ₄ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊓ foldFix (τ : graphFixedRootGroup
          TwistTag.D4 K σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ↔
      g ∈ fixSubO φ₄ ∧ τ.toMonoidHom g = g := by
    intro g
    rw [Subgroup.mem_inf, mem_foldFix, mem_foldFix]
    rfl
  obtain ⟨hSle, hNorm, hSolv⟩ := normal_solvable_of_fixed ρY θ.toMonoidHom τ.toMonoidHom hτρ hkerY
    S hSmem hSperf (fixSubO φ₄) hrange_le hsolv' _ hC'
  set C' := foldFix (φ₄ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊓ foldFix (τ : graphFixedRootGroup
          TwistTag.D4 K σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) with hC'def
  haveI hJN := hNorm
  let J : Subgroup ↥C' := (S.map ρY).subgroupOf C'
  let ρS : ↥S →* ↥C' := (ρY.comp S.subtype).codRestrict C' (fun x => hSle ⟨x, x.2, rfl⟩)
  let gS : ↥S →* ↥J := ρS.codRestrict J (fun x => ⟨x, x.2, rfl⟩)
  let g : ↥(StatedSU 3 (p ^ f) ↥F₂) →* ↥J := gS.comp e.toMonoidHom
  have hg : Function.Surjective g := by
    intro j
    obtain ⟨x, hx, hxj⟩ := j.2
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show ρY ((e (e.symm ⟨x, hx⟩) : ↥S) : SL(3, fixSubfield σ)) = ((j : ↥C') : _)
    rw [MulEquiv.apply_symm_apply]
    exact hxj
  have hgk : g.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ f) ↥F₂) := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : ρY ((e y : ↥S) : SL(3, fixSubfield σ)) = 1 := by
      have := congrArg (fun j : ↥J => ((j : ↥C') : graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
        hy
      exact this
    have hz : ((e y : ↥S) : SL(3, fixSubfield σ)) ∈ Subgroup.center SL(3, fixSubfield σ) :=
      hkerY h1
    rw [Subgroup.mem_center_iff]
    intro y'
    apply e.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.1 hz _
  haveI : Fintype ↥F₂ := Fintype.ofFinite _
  have hnq : (3, p ^ f) ≠ (3, 2) := fun h => by
    have := congrArg Prod.snd h
    simp only at this
    omega
  obtain ⟨hqs, -⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU
    (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF₂ le_rfl hnq)
    (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F₂ p f hF₂ 3 le_rfl hnq)
  have hJq : CFSG.IsQuasisimple ↥J := CFSG.LocalCores.isQuasisimple_of_surjective hqs g hg hgk
  have hbfix : σ.toRingHom (b : K) = b := congrArg Units.val hbσ
  let ω : fixSubfield σ := ⟨(b : K), hbfix⟩
  have hω3 : ω ^ 3 = 1 := by
    apply Subtype.ext
    have h := congrArg Units.val hb3
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    exact h
  have hω1 : ω ≠ 1 := by
    intro h
    apply hb1
    apply Units.ext
    have := congrArg Subtype.val h
    simpa [ω] using this
  have hσQω : σQ.toRingHom ω = ω⁻¹ := by
    have h1 : σQ ω = ω ^ (p ^ f) := hσQ ω
    have h2 : ω ^ (p ^ f) = ω ^ 2 := by
      obtain ⟨k, hk⟩ : ∃ k, p ^ f = 3 * k + 2 := ⟨(p ^ f) / 3, by omega⟩
      rw [hk, pow_add, pow_mul, hω3, one_pow, one_mul]
    have h3 : ω ^ 2 = ω⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hω3)
    exact h1.trans (h2.trans h3)
  have hxS : heisX ω hω3 ∈ S := (hSmem _).2 (by
    show stdUnitary σQ.toRingHom (heisX ω hω3) = heisX ω hω3
    exact stdUnitary_heisX σQ.toRingHom ω hω3 hσQω)
  have hyS : (heisY : SL(3, fixSubfield σ)) ∈ S := (hSmem _).2 (by
    show stdUnitary σQ.toRingHom (heisY : SL(3, fixSubfield σ)) = heisY
    exact stdUnitary_heisY σQ.toRingHom)
  obtain ⟨hx1, hx3, hy3, hcx, hcy, hyx⟩ := heis_of_hom ω hω3 hω1 ρY hkerY
  have hxC : ρY (heisX ω hω3) ∈ C' := hSle ⟨_, hxS, rfl⟩
  have hyC : ρY heisY ∈ C' := hSle ⟨_, hyS, rfl⟩
  refine ⟨J, hJN, hJq, hSolv, ⟨_, hxC⟩, ⟨_, hyC⟩, ⟨_, hxS, rfl⟩, ⟨_, hyS, rfl⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hx1 (congrArg Subtype.val h)
  · exact Subtype.ext hx3
  · exact Subtype.ext hy3
  · refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hcx.eq
  · refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hcy.eq
  · intro hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hyx
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    have := congrArg Subtype.val hi
    rw [Subgroup.coe_zpow] at this
    exact this

theorem not_hasType424_fixSub_a2Minus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hs : D4MinusToral p f hp K σ s) :
    ¬ KS11Lie2Proof.HasType424
      ↥(CFSG.RankThree.PartTwo.Sec4.autFix
        (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨K₄, _, _, hCh, hK₄, σ₄, ε, hσ₄, hε, b, hb3, hb1, s₄, hs₄, ψ₄, hinj, hint, hfix⟩ :=
    un_frame hp hf hq K hK σ hσ s hs
  haveI : Finite (ModGL TwistTag.D4.tag K₄) := finite_modGL
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
    omega
  have hq5 : 5 ≤ p ^ f := hp5.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨J, hJn, hJq, hsolv, x, y, hxJ, hyJ, hx1, hx3, hy3, hcx, hcy, hyx⟩ :=
    unitary_core_heis (p := p) hp2 hf hq hq5 hK₄ hσ₄ hε hb3 hb1 hs₄
  obtain ⟨e, -⟩ := un_fixSub_equiv (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)
    (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄) (unTau σ₄ ε) ψ₄ hinj hint hfix
  haveI := hJn
  have hC' : ¬ KS11Lie2Proof.HasType424 ↥(unC σ₄ ε s₄) :=
    not_hasType424_of_quasisimple J hJq hsolv hxJ hyJ hx1 hx3 hy3 hcx hcy hyx
  intro h
  have h1 : KS11Lie2Proof.HasType424
      ↥(fixSubO (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) :=
    h.of_mulEquiv (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl))
  exact hC' (h1.of_mulEquiv e)

end Core

end CFSG.RankThree.PartTwo.Sec11.RonanD4Odd
