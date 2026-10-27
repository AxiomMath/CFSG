module

public import CFSG.Quasithin.Background.TrivialLineExtension
public import CFSG.Quasithin.Background.F918D4
public import CFSG.HardMathSupport.Cooperstein.Proving.KerGenDual
public import CFSG.LinearAlgebra.AlternatingSL

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank
open Matrix
open scoped Matrix

variable {B Q : Type} [Group B] [AddCommGroup Q] [Module (ZMod 2) Q]

theorem card_commSub_eq_two_pow_finrank_range_sub_one
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (τ : MulAut (Multiplicative E)) (T : E →ₗ[ZMod 2] E)
    (hT : ∀ x, Multiplicative.toAdd (τ (Multiplicative.ofAdd x)) = T x) :
    Nat.card ↥(commSub (⊤ : Subgroup (Multiplicative E)) (Subgroup.zpowers τ)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (T - 1)) := by
  let a : G11.GLV E := G11.linEquivMulAut.symm τ
  have ha : ∀ x, a x = T x := by
    intro x
    rw [G11.linEquivMulAut_symm_apply]
    exact hT x
  have haeq : G11.linEquivMulAut a = τ := by
    simp [a]
  rw [← commV_eq_commSub, ← haeq, G11.commV_zpowers_toMulSub,
    G11.natCard_subToSubgroup_eq]
  have hrange : LinearMap.range ((a : E →ₗ[ZMod 2] E) - LinearMap.id) =
      LinearMap.range (T - 1) := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by simpa [LinearMap.sub_apply, ha y] using hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by simpa [LinearMap.sub_apply, ha y] using hy⟩
  rw [hrange]


private theorem finrank_eq_three_of_addEquiv
    (β : Q ≃+ ((Fin 3) → ZMod 2)) : Module.finrank (ZMod 2) Q = 3 := by
  let e : Q ≃ₗ[ZMod 2] ((Fin 3) → ZMod 2) :=
    @G11.addEquivToLinear Q _ _ ((Fin 3) → ZMod 2) _
      (Pi.Function.module (Fin 3) (ZMod 2) (ZMod 2)) β
  have h := e.finrank_eq
  simpa [Module.finrank_fin_fun] using h

private theorem moduleFinite_of_addEquiv
    (β : Q ≃+ ((Fin 3) → ZMod 2)) : Module.Finite (ZMod 2) Q := by
  let e : Q ≃ₗ[ZMod 2] ((Fin 3) → ZMod 2) :=
    @G11.addEquivToLinear Q _ _ ((Fin 3) → ZMod 2) _
      (Pi.Function.module (Fin 3) (ZMod 2) (ZMod 2)) β
  haveI : Module.Finite (ZMod 2) ((Fin 3) → ZMod 2) := Module.Finite.of_finite
  exact Module.Finite.equiv e.symm

private theorem eq_zero_of_forall_intertwiner_fixed
    (ρQ : Representation (ZMod 2) B Q)
    {θ : B ≃* SpecialLinearGroup (Fin (3 : ℕ)) (ZMod 2)}
    {β : Q ≃+ ((Fin 3) → ZMod 2)}
    (hβ : ∀ b q, β (ρQ b q) = θ b • β q)
    {q : Q} (hq : ∀ b : B, ρQ b q = q) : q = 0 := by
  have hvec : ∀ A : SpecialLinearGroup (Fin (3 : ℕ)) (ZMod 2),
      ((A : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) (ZMod 2)) *ᵥ β q) = β q := by
    intro A
    obtain ⟨b, rfl⟩ := θ.surjective A
    have h1 : θ b • β q = β q := by rw [← hβ b q, hq b]
    simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using h1
  have hzero := CFSG.LinearAlgebra.eq_zero_of_forall_specialLinear_mulVec_eq hvec
  exact β.injective (hzero.trans (map_zero β).symm)

private theorem eq_zero_of_forall_intertwiner_invariant_functional
    (ρQ : Representation (ZMod 2) B Q)
    {θ : B ≃* SpecialLinearGroup (Fin (3 : ℕ)) (ZMod 2)}
    {β : Q ≃+ ((Fin 3) → ZMod 2)}
    (hβ : ∀ b q, β (ρQ b q) = θ b • β q)
    (ψ : Module.Dual (ZMod 2) Q) (hψ : ∀ b q, ψ (ρQ b q) = ψ q) : ψ = 0 := by
  let e : Q ≃ₗ[ZMod 2] ((Fin 3) → ZMod 2) :=
    @G11.addEquivToLinear Q _ _ ((Fin 3) → ZMod 2) _
      (Pi.Function.module (Fin 3) (ZMod 2) (ZMod 2)) β
  let lam : ((Fin 3) → ZMod 2) →ₗ[ZMod 2] ZMod 2 := ψ.comp e.symm.toLinearMap
  have he : ∀ q : Q, e q = β q := fun q => rfl
  have hlam : ∀ (A : SpecialLinearGroup (Fin (3 : ℕ)) (ZMod 2)) (v : ((Fin (3 : ℕ)) → ZMod 2)),
      lam ((A : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) (ZMod 2)) *ᵥ v) = lam v := by
    intro A v
    obtain ⟨b, rfl⟩ := θ.surjective A
    have hv : ((θ b : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) (ZMod 2)) *ᵥ v) =
        β (ρQ b (e.symm v)) := by
      rw [hβ b (e.symm v)]
      have hve : β (e.symm v) = v := by
        change e (e.symm v) = v
        exact e.apply_symm_apply v
      rw [hve]
      rw [← Matrix.smul_eq_mulVec, ← Matrix.SpecialLinearGroup.smul_def]
    change ψ (e.symm ((θ b : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) (ZMod 2)) *ᵥ v)) = ψ (e.symm v)
    rw [hv]
    have hsymm : e.symm (β (ρQ b (e.symm v))) = ρQ b (e.symm v) := by
      change e.symm (e (ρQ b (e.symm v))) = ρQ b (e.symm v)
      exact e.symm_apply_apply _
    rw [hsymm, hψ b (e.symm v)]
  let S : AddSubgroup ((Fin 3) → ZMod 2) := (LinearMap.ker lam).toAddSubgroup
  have hS : S = ⊥ ∨ S = ⊤ := by
    refine CFSG.LinearAlgebra.eq_bot_or_eq_top_of_specialLinear_invariant S ?_
    intro A s hs
    change lam ((A : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) (ZMod 2)) *ᵥ s) = 0
    rw [hlam A s]
    exact hs
  rcases hS with hbot | htop
  · have hinj : Function.Injective lam := by
      intro x y hxy
      have hmem : x - y ∈ S := by
        show lam (x - y) = 0
        rw [map_sub, hxy]
        exact sub_self (lam y)
      rw [hbot, AddSubgroup.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
    have hle := LinearMap.finrank_le_finrank_of_injective (f := lam) hinj
    rw [Module.finrank_fin_fun, Module.finrank_self] at hle
    norm_num at hle
  · ext q
    have h1 : lam (e q) = 0 := by
      have hmem : e q ∈ S := by rw [htop]; exact AddSubgroup.mem_top _
      exact hmem
    have h2 : lam (e q) = ψ q := by simp [lam]
    rw [← h2]
    exact h1

theorem naturalThree_finrank_trivialLineExtension
    (ρQ : Representation (ZMod 2) B Q) {ε : Explicit.NatDual}
    (hnat : Explicit.BinaryNaturalSL ρQ 3 (ZMod 2) ε) :
    Module.finrank (ZMod 2) (ZMod 2 × Q) = 4 := by
  obtain ⟨-, β, -⟩ := JonesParshall.BinaryNaturalSL.intertwiner hnat
  haveI : Module.Finite (ZMod 2) Q := moduleFinite_of_addEquiv β
  rw [Module.finrank_prod, finrank_eq_three_of_addEquiv β, Module.finrank_self]


theorem naturalThree_trivialLineExtension_fixV
    (ρQ : Representation (ZMod 2) B Q) {ε : Explicit.NatDual}
    (hnat : Explicit.BinaryNaturalSL ρQ 3 (ZMod 2) ε)
    (d : B → Module.Dual (ZMod 2) Q)
    (hd : d ∈ Z1 (Representation.dual ρQ)) :
    fixV (FFModel.repMulAut (trivialLineExtension ρQ d hd)).range =
      G11.subToSubgroup (LinearMap.ker (LinearMap.snd (ZMod 2) (ZMod 2) Q)) := by
  obtain ⟨θ, β, hβ⟩ := JonesParshall.BinaryNaturalSL.intertwiner hnat
  let ρE := trivialLineExtension ρQ d hd
  have hQfix : ∀ q : Q, (∀ b : B, ρQ b q = q) → q = 0 :=
    fun q hq => eq_zero_of_forall_intertwiner_fixed ρQ hβ hq
  ext x
  rw [mem_fixV, G11.mem_subToSubgroup, LinearMap.mem_ker, LinearMap.snd_apply]
  constructor
  · intro hx
    have hx' : ∀ b : B, ρE b (Multiplicative.toAdd x) = Multiplicative.toAdd x := by
      intro b
      have h := hx (FFModel.repMulAut ρE b) (MonoidHom.mem_range.mpr ⟨b, rfl⟩)
      exact Multiplicative.ofAdd.injective (by
        simpa [ρE, FFModel.repMulAut_apply] using h)
    exact (trivialLineExtension_fixed_iff ρQ d hd hQfix
      (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2).1 hx'
  · intro hx f hf
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hf
    apply Multiplicative.ofAdd.injective
    rw [FFModel.repMulAut_apply]
    have h := (trivialLineExtension_fixed_iff ρQ d hd hQfix
      (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2).2 hx
    simpa using congrArg Multiplicative.ofAdd (h b)

theorem naturalThree_trivialLineExtension_card_fixV
    (ρQ : Representation (ZMod 2) B Q) {ε : Explicit.NatDual}
    (hnat : Explicit.BinaryNaturalSL ρQ 3 (ZMod 2) ε)
    (d : B → Module.Dual (ZMod 2) Q)
    (hd : d ∈ Z1 (Representation.dual ρQ)) :
    Nat.card ↥(fixV (FFModel.repMulAut (trivialLineExtension ρQ d hd)).range) = 2 := by
  obtain ⟨θ, β, hβ⟩ := JonesParshall.BinaryNaturalSL.intertwiner hnat
  let ρE := trivialLineExtension ρQ d hd
  let LE : Subgroup (MulAut (Multiplicative (ZMod 2 × Q))) := (FFModel.repMulAut ρE).range
  have hQfix : ∀ q : Q, (∀ b : B, ρQ b q = q) → q = 0 :=
    fun q hq => eq_zero_of_forall_intertwiner_fixed ρQ hβ hq
  let e : ↥(fixV LE) ≃ ZMod 2 :=
  { toFun := fun x => (Multiplicative.toAdd (x : Multiplicative (ZMod 2 × Q))).1
    invFun := fun a => ⟨Multiplicative.ofAdd (a, 0), by
      rw [mem_fixV]
      intro f hf
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hf
      apply Multiplicative.ofAdd.injective
      rw [FFModel.repMulAut_apply, trivialLineExtension_apply]
      simp⟩
    left_inv := fun x => by
      apply Subtype.ext
      apply Multiplicative.ofAdd.injective
      have hxall : ∀ b : B, ρE b (Multiplicative.toAdd (x : Multiplicative (ZMod 2 × Q))) =
          Multiplicative.toAdd (x : Multiplicative (ZMod 2 × Q)) := by
        intro b
        have h := x.2 (FFModel.repMulAut ρE b) (MonoidHom.mem_range.mpr ⟨b, rfl⟩)
        exact Multiplicative.ofAdd.injective (by
          simpa [LE, ρE, FFModel.repMulAut_apply] using h)
      have hq0 := (trivialLineExtension_fixed_iff ρQ d hd hQfix
        (Multiplicative.toAdd (x : Multiplicative (ZMod 2 × Q))).1
        (Multiplicative.toAdd (x : Multiplicative (ZMod 2 × Q))).2).1 hxall
      exact Prod.ext rfl hq0.symm
    right_inv := fun a => rfl }
  rw [Nat.card_congr e, Nat.card_zmod]

private abbrev naturalSL3Model : FFModel := FFModel.nat (StatedSL 3 (ZMod 2))

private theorem realizes_nat_of_coords
    (ρQ : Representation (ZMod 2) B Q) {ε : Explicit.NatDual}
    (hnat : Explicit.BinaryNaturalSL ρQ 3 (ZMod 2) ε)
    (d : B → Module.Dual (ZMod 2) Q)
    (hd : d ∈ Z1 (Representation.dual ρQ))
    {θ : B ≃* SpecialLinearGroup (Fin 3) (ZMod 2)}
    {β : Q ≃+ ((Fin 3) → ZMod 2)}
    (hβ : ∀ b q, β (ρQ b q) = θ b • β q) :
    (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia
      (FFModel.repMulAut (trivialLineExtension ρQ d hd)).range
      ⊤ (fixV (FFModel.repMulAut (trivialLineExtension ρQ d hd)).range)
      ((FFModel.repMulAut (trivialLineExtension ρQ d hd)).rangeRestrict.comp
        (θ.symm.toMonoidHom.comp
          (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm.toMonoidHom)) := by
  let ρE := trivialLineExtension ρQ d hd
  let LE : Subgroup (MulAut (Multiplicative (ZMod 2 × Q))) := (FFModel.repMulAut ρE).range
  let S := StatedSL 3 (ZMod 2)
  let eSL := specialLinearGroupEquivStatedSL 3 (ZMod 2)
  let sB : S →* B := θ.symm.toMonoidHom.comp eSL.symm.toMonoidHom
  let π : S →* ↥LE := (FFModel.repMulAut ρE).rangeRestrict.comp sB
  let qE : ↥(⊤ : Subgroup (Multiplicative (ZMod 2 × Q))) →*
      Multiplicative ((Fin 3) → ZMod 2) :=
    { toFun := fun u => Multiplicative.ofAdd
        (β (Multiplicative.toAdd (u : Multiplicative (ZMod 2 × Q))).2)
      map_one' := by simp
      map_mul' := by
        intro x y
        simp [map_add] }
  let βmap : ↥(⊤ : Subgroup (Multiplicative (ZMod 2 × Q))) →* naturalSL3Model.Sec :=
    (QuotientGroup.mk' (naturalSL3Model.ker.subgroupOf naturalSL3Model.sec)).comp
      (qE.codRestrict naturalSL3Model.sec (fun _ => Subgroup.mem_top _))
  have hβmk : ∀ u : ↥(⊤ : Subgroup (Multiplicative (ZMod 2 × Q))),
      βmap u = QuotientGroup.mk (⟨qE u, Subgroup.mem_top _⟩ : ↥naturalSL3Model.sec) := fun u => rfl
  refine ⟨?_, le_top, bot_le, ?_, ?_, ?_, ?_, ?_⟩
  · exact (MonoidHom.rangeRestrict_surjective _).comp
      (θ.symm.surjective.comp eSL.symm.surjective)
  · intro h u _; exact Subgroup.mem_top _
  · intro h z hz
    rw [mem_fixV] at hz ⊢
    intro g hg
    rw [hz h h.2, hz g hg]
  · intro γ m _; exact Subgroup.mem_top _
  · intro γ m hm
    rw [show naturalSL3Model.ker = ⊥ from rfl, Subgroup.mem_bot] at hm ⊢
    rw [hm]
    rfl
  · refine ⟨βmap, ?_, ?_, ?_⟩
    · intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨v, hv⟩ := β.surjective (Multiplicative.toAdd (show Multiplicative ((Fin 3) → ZMod 2) from (m : naturalSL3Model.Amb)))
      refine ⟨⟨Multiplicative.ofAdd (0, v), Subgroup.mem_top _⟩, ?_⟩
      rw [hβmk]
      congr 1
      apply Subtype.ext
      change Multiplicative.ofAdd (β v) = (m : naturalSL3Model.Amb)
      rw [hv]
      exact rfl
    · intro u
      have hq1 : βmap u = 1 ↔ qE u = 1 := by
        constructor
        · intro h
          have h' : (QuotientGroup.mk (⟨qE u, Subgroup.mem_top _⟩ : ↥naturalSL3Model.sec) : naturalSL3Model.Sec) = 1 := by
            simpa [hβmk] using h
          have hmem : (⟨qE u, Subgroup.mem_top _⟩ : ↥naturalSL3Model.sec) ∈ naturalSL3Model.ker.subgroupOf naturalSL3Model.sec :=
            (QuotientGroup.eq_one_iff _).mp h'
          have hbot : ((⟨qE u, Subgroup.mem_top _⟩ : ↥naturalSL3Model.sec) : naturalSL3Model.Amb) ∈ naturalSL3Model.ker :=
            (Subgroup.mem_subgroupOf).mp hmem
          rw [show naturalSL3Model.ker = ⊥ from rfl, Subgroup.mem_bot] at hbot
          exact hbot
        · intro h
          rw [hβmk, h]
          rfl
      have hqE1 : ∀ u : ↥(⊤ : Subgroup (Multiplicative (ZMod 2 × Q))),
          qE u = 1 ↔ (Multiplicative.toAdd (u : Multiplicative (ZMod 2 × Q))).2 = 0 := by
        intro u
        constructor
        · intro h
          have hb : β (Multiplicative.toAdd (u : Multiplicative (ZMod 2 × Q))).2 = 0 := by
            simpa [qE] using congrArg Multiplicative.toAdd h
          exact β.injective (hb.trans (map_zero β).symm)
        · intro h
          apply Multiplicative.ofAdd.injective
          simp [qE, h]
      rw [hq1, hqE1, naturalThree_trivialLineExtension_fixV ρQ hnat d hd,
        G11.mem_subToSubgroup, LinearMap.mem_ker, LinearMap.snd_apply]
    · intro γ u m hu hm hbu
      let γS : S := γ
      have hq : qE u = (m : naturalSL3Model.Amb) := by
        have hmem : (⟨qE u, Subgroup.mem_top _⟩ : ↥naturalSL3Model.sec)⁻¹ * m ∈
            naturalSL3Model.ker.subgroupOf naturalSL3Model.sec := by
          have h' : (QuotientGroup.mk (⟨qE u, Subgroup.mem_top _⟩ : ↥naturalSL3Model.sec) :
              naturalSL3Model.Sec) = (QuotientGroup.mk m : naturalSL3Model.Sec) := by
            simpa [hβmk] using hbu
          exact (QuotientGroup.eq).mp h'
        have hbot : (show Multiplicative ((Fin 3) → ZMod 2) from
            (((⟨qE u, Subgroup.mem_top _⟩ : ↥naturalSL3Model.sec)⁻¹ * m : ↥naturalSL3Model.sec)
              : naturalSL3Model.Amb)) = 1 := by
          have h2 := (Subgroup.mem_subgroupOf).mp hmem
          rw [show naturalSL3Model.ker = ⊥ from rfl, Subgroup.mem_bot] at h2
          exact h2
        have h3 := inv_mul_eq_one.mp hbot
        simpa using h3
      let b : B := sB γS
      have hπ : ((π γS : ↥LE) : MulAut (Multiplicative (ZMod 2 × Q))) =
          FFModel.repMulAut ρE b := rfl
      have hqE_rep : qE ⟨FFModel.repMulAut ρE b
            (u : Multiplicative (ZMod 2 × Q)), hu⟩ =
          Multiplicative.ofAdd
            (β (ρQ b (Multiplicative.toAdd (u : Multiplicative (ZMod 2 × Q))).2)) := by
        rw [show qE ⟨FFModel.repMulAut ρE b (u : Multiplicative (ZMod 2 × Q)), hu⟩ =
            Multiplicative.ofAdd (β (Multiplicative.toAdd
              (FFModel.repMulAut ρE b (u : Multiplicative (ZMod 2 × Q)))).2) from rfl]
        rw [FFModel.repMulAut_apply, toAdd_ofAdd, trivialLineExtension_apply]
      have hcoe : ((eSL.symm γS : SpecialLinearGroup (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          ((γS : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
        rw [← specialLinearGroupEquivStatedSL_coe 3 (ZMod 2) (eSL.symm γS),
          eSL.apply_symm_apply]
      have hθb : θ b = eSL.symm γS := by
        change θ (θ.symm (eSL.symm γS)) = eSL.symm γS
        exact θ.apply_symm_apply _
      have hact : qE ⟨((π γS : ↥LE) : MulAut (Multiplicative (ZMod 2 × Q)))
            (u : Multiplicative (ZMod 2 × Q)), hu⟩ = naturalSL3Model.act γS (m : naturalSL3Model.Amb) := by
        rw [hπ, hqE_rep]
        have hm1 : (m : naturalSL3Model.Amb) = Multiplicative.ofAdd
            (β (Multiplicative.toAdd (u : Multiplicative (ZMod 2 × Q))).2) := by
          rw [← hq]; rfl
        rw [hm1]
        rw [hβ b (Multiplicative.toAdd (u : Multiplicative (ZMod 2 × Q))).2, hθb]
        congr 1
        rw [Matrix.SpecialLinearGroup.smul_def, hcoe]
        simp [Matrix.smul_eq_mulVec]
      change QuotientGroup.mk (⟨qE ⟨((π γS : ↥LE) : MulAut (Multiplicative (ZMod 2 × Q)))
          (u : Multiplicative (ZMod 2 × Q)), hu⟩, Subgroup.mem_top _⟩ : ↥naturalSL3Model.sec) =
        QuotientGroup.mk (⟨naturalSL3Model.act γS (m : naturalSL3Model.Amb), hm⟩ : ↥naturalSL3Model.sec)
      exact congrArg QuotientGroup.mk (Subtype.ext hact)

theorem naturalThree_trivialLineExtension_binaryNaturalSL
    (ρQ : Representation (ZMod 2) B Q) {ε : Explicit.NatDual}
    (hnat : Explicit.BinaryNaturalSL ρQ 3 (ZMod 2) ε)
    (d : B → Module.Dual (ZMod 2) Q)
    (hd : d ∈ Z1 (Representation.dual ρQ)) :
    BinaryNaturalSL (FFModel.repMulAut (trivialLineExtension ρQ d hd)).range
      ⊤ (fixV (FFModel.repMulAut (trivialLineExtension ρQ d hd)).range) 3 1 := by
  obtain ⟨θ, β, hβ⟩ := JonesParshall.BinaryNaturalSL.intertwiner hnat
  refine ⟨ZMod 2, inferInstance, inferInstance, by simp, ?_⟩
  exact ⟨_, realizes_nat_of_coords ρQ hnat d hd hβ⟩


theorem naturalThree_trivialLineExtension_perfect
    (ρQ : Representation (ZMod 2) B Q) {ε : Explicit.NatDual}
    (hnat : Explicit.BinaryNaturalSL ρQ 3 (ZMod 2) ε)
    (d : B → Module.Dual (ZMod 2) Q)
    (hd : d ∈ Z1 (Representation.dual ρQ))
    (hdn : d ∉ B1 (Representation.dual ρQ)) :
    XMod.commOf ↥((FFModel.repMulAut (trivialLineExtension ρQ d hd)).range)
      (⊤ : Subgroup (Multiplicative (ZMod 2 × Q))) = ⊤ := by
  obtain ⟨θ, β, hβ⟩ := JonesParshall.BinaryNaturalSL.intertwiner hnat
  let ρE := trivialLineExtension ρQ d hd
  let LE : Subgroup (MulAut (Multiplicative (ZMod 2 × Q))) := (FFModel.repMulAut ρE).range
  let ρlin : B →* G11.GLV (ZMod 2 × Q) :=
    G11.linEquivMulAut.symm.toMonoidHom.comp (FFModel.repMulAut ρE)
  have hQ : ∀ ψ : Module.Dual (ZMod 2) Q,
      (∀ b q, ψ (ρQ b q) = ψ q) → ψ = 0 :=
    fun ψ hψ => eq_zero_of_forall_intertwiner_invariant_functional ρQ hβ ψ hψ
  have hρlin : ∀ (b : B) (x : ZMod 2 × Q), ρlin b x = ρE b x := by
    intro b x
    rw [show ρlin b = G11.linEquivMulAut.symm (FFModel.repMulAut ρE b) from rfl,
      G11.linEquivMulAut_symm_apply, FFModel.repMulAut_apply, toAdd_ofAdd]
    rfl
  have hno : ∀ ψ : (ZMod 2 × Q) →ₗ[ZMod 2] ZMod 2,
      (∀ a : B, ψ.comp (ρlin a⁻¹ : (ZMod 2 × Q) →ₗ[ZMod 2] (ZMod 2 × Q)) = ψ) → ψ = 0 := by
    intro ψ hψ
    refine trivialLineExtension_noInvariantFunctional ρQ d hd hdn hQ ψ ?_
    intro b x
    have h2 : ψ (ρlin b⁻¹ (ρE b x)) = ψ (ρE b x) := by
      have h := LinearMap.congr_fun (hψ b) (ρE b x)
      simpa using h
    rw [hρlin] at h2
    have h3 : ρE b⁻¹ (ρE b x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [h3] at h2
    exact h2.symm
  have hspan := CFSG.HardMathSupport.Cooperstein.Proving.span_eq_top_of_no_invariant ρlin hno
  have hcommV : commV LE = G11.subToSubgroup
      (Submodule.span (ZMod 2) {x : ZMod 2 × Q | ∃ a u, x = ρlin a u - u}) := by
    rw [commV_eq_commSub, G11.subToSubgroup_span]
    unfold commSub
    congr 1
    ext c
    constructor
    · rintro ⟨x, hx, w, hw, rfl⟩
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hx
      refine ⟨ρlin b (Multiplicative.toAdd w) - Multiplicative.toAdd w,
        ⟨b, Multiplicative.toAdd w, rfl⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      simp [FFModel.repMulAut_apply, hρlin, sub_eq_add_neg]
    · rintro ⟨x, ⟨b, u, rfl⟩, rfl⟩
      refine ⟨FFModel.repMulAut ρE b, ⟨b, rfl⟩, Multiplicative.ofAdd u, Subgroup.mem_top _, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      simp [FFModel.repMulAut_apply, hρlin, sub_eq_add_neg]
  have hperfect : commV LE = ⊤ := by
    rw [hcommV, hspan]
    exact OrderIso.map_top G11.subToSubgroup
  rw [commOf_eq_commSub, ← commV_eq_commSub]
  exact hperfect

theorem naturalThree_trivialLineExtension_involution_finrank
    (ρQ : Representation (ZMod 2) B Q) {ε : Explicit.NatDual}
    (hnat : Explicit.BinaryNaturalSL ρQ 3 (ZMod 2) ε)
    (d : B → Module.Dual (ZMod 2) Q)
    (hd : d ∈ Z1 (Representation.dual ρQ))
    (hdn : d ∉ B1 (Representation.dual ρQ))
    (b : B) (hb2 : b ^ 2 = 1)
    (hne : trivialLineExtension ρQ d hd b ≠ 1) :
    Module.finrank (ZMod 2)
      (LinearMap.range (trivialLineExtension ρQ d hd b - 1)) = 2 := by
  obtain ⟨θ, β, hβ⟩ := JonesParshall.BinaryNaturalSL.intertwiner hnat
  haveI : Finite Q := Finite.of_injective β β.injective
  haveI : Finite (ZMod 2 × Q) := inferInstance
  haveI : Finite (Multiplicative (ZMod 2 × Q)) := inferInstance
  let ρE := trivialLineExtension ρQ d hd
  let LE : Subgroup (MulAut (Multiplicative (ZMod 2 × Q))) := (FFModel.repMulAut ρE).range
  let T : (ZMod 2 × Q) →ₗ[ZMod 2] (ZMod 2 × Q) := ρE b
  let τ : MulAut (Multiplicative (ZMod 2 × Q)) := FFModel.repMulAut ρE b
  have hτmem : τ ∈ LE := ⟨b, rfl⟩
  have hτne : τ ≠ 1 := by
    intro hτ
    apply hne
    apply LinearMap.ext
    intro x
    have h := congrArg (fun f : MulAut (Multiplicative (ZMod 2 × Q)) =>
      Multiplicative.toAdd (f (Multiplicative.ofAdd x))) hτ
    simpa [τ, FFModel.repMulAut_apply] using h
  have hτ2 : τ ^ 2 = 1 := by
    rw [show τ ^ 2 = FFModel.repMulAut ρE (b ^ 2) by rw [← map_pow]]
    rw [hb2, map_one]
  have hcomm : XMod.commOf ↥LE (⊤ : Subgroup (Multiplicative (ZMod 2 × Q))) = ⊤ :=
    naturalThree_trivialLineExtension_perfect ρQ hnat d hd hdn
  have hnatB : BinaryNaturalSL LE ⊤ (fixV LE) 3 1 :=
    naturalThree_trivialLineExtension_binaryNaturalSL ρQ hnat d hd
  have hcard : Nat.card ↥(fixV LE) = 2 :=
    naturalThree_trivialLineExtension_card_fixV ρQ hnat d hd
  have hcov := cover_commSub_involution (G11.multiplicative_sq_eq_one (V := ZMod 2 × Q))
    LE ⊤ (fun _ _ _ _ => Subgroup.mem_top _) hcomm
    (by simpa [LE, top_inf_eq] using hnatB) (by simpa [LE, top_inf_eq] using hcard)
    τ hτmem hτne hτ2
  have hc4 : Nat.card ↥(commSub (⊤ : Subgroup (Multiplicative (ZMod 2 × Q)))
      (Subgroup.zpowers τ)) = 4 := hcov.1
  have hT : ∀ x, Multiplicative.toAdd (τ (Multiplicative.ofAdd x)) = T x := by
    intro x
    rw [show τ = FFModel.repMulAut ρE b from rfl, FFModel.repMulAut_apply, toAdd_ofAdd]
    rfl
  have hbridge := card_commSub_eq_two_pow_finrank_range_sub_one τ T hT
  have hpow : 2 ^ Module.finrank (ZMod 2) (LinearMap.range (T - 1)) = 2 ^ 2 := by
    rw [← hbridge, hc4]
    norm_num
  have hdim : Module.finrank (ZMod 2) (LinearMap.range (T - 1)) = 2 :=
    Nat.pow_right_injective (le_refl 2) hpow
  simpa [T, ρE] using hdim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
