module

public import CFSG.Milestones.ASVolI.F4Small
public import CFSG.Milestones.ASVolI.F4TISets
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldOuter
public import CFSG.GH74.KGroups.U33
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.LieType.Chevalley

section F429One

theorem burnsideF429_card_mulAut_eq {G : Type*} [Group G] [Finite G]
    (hZ : Subgroup.center G = ⊥) :
    Nat.card (MulAut G) = Nat.card (Outer G) * Nat.card G := by
  haveI : Finite (MulAut G) :=
    Finite.of_injective (fun f : MulAut G => (f : G → G)) fun _ _ h => MulEquiv.ext (congrFun h)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner G)
  rw [h1]
  congr 1
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro x
    have h2 := congrArg (fun φ : MulAut G => φ x) (MonoidHom.mem_ker.1 hy)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc x * y = y * x * y⁻¹ * y := by rw [h2]
      _ = y * x := by group
  exact Nat.card_range_of_injective hinj

theorem burnsideF429_eq_top_or_of_card_outer {E : Type} [Group E] [Finite E] {Gp : Subgroup E}
    [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥) {p : ℕ} (hp : p.Prime)
    (hout : Nat.card (Outer ↥Gp) = p) :
    Gp = ⊤ ∨ (Gp.index = p ∧ Nat.card E = Nat.card (MulAut ↥Gp)) := by
  set α : E →* MulAut ↥Gp := MulAut.conjNormal with hα
  have hαinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hcg : g ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun φ : MulAut ↥Gp => ((φ ⟨x, hx⟩ : ↥Gp) : E)) (MonoidHom.mem_ker.1 hg)
      simp only [hα, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rw [hc] at hcg
    exact hcg
  have hZ : Subgroup.center ↥Gp = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzc : (z : E) ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := Subgroup.mem_center_iff.1 hz ⟨x, hx⟩
      exact congrArg Subtype.val this
    rw [hc, Subgroup.mem_bot] at hzc
    exact (Subgroup.mem_bot).2 (Subtype.ext hzc)
  have hcardAut : Nat.card (MulAut ↥Gp) = p * Nat.card Gp := by
    rw [burnsideF429_card_mulAut_eq hZ, hout]
  haveI : Finite (MulAut ↥Gp) :=
    Finite.of_injective (fun f : MulAut ↥Gp => (f : ↥Gp → ↥Gp)) fun _ _ h =>
      MulEquiv.ext (congrFun h)
  have hGmap : (Gp.map α).relIndex ((⊤ : Subgroup E).map α) = Gp.index := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ hαinj, Subgroup.relIndex_top_right]
  have hcardGmap : Nat.card (Gp.map α) = Nat.card Gp := Subgroup.card_map_of_injective hαinj
  have hidxAut : (Gp.map α).index = p := by
    have h1 := (Gp.map α).index_mul_card
    rw [hcardGmap, hcardAut] at h1
    have hpos : 0 < Nat.card Gp := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hdvd : Gp.index ∣ p := by
    have h1 := Subgroup.relIndex_mul_relIndex (Gp.map α) ((⊤ : Subgroup E).map α) ⊤
      (Subgroup.map_mono le_top) le_top
    rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right, hidxAut, hGmap] at h1
    exact Dvd.intro _ h1
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · left
    exact Subgroup.index_eq_one.1 h1
  · right
    refine ⟨h1, ?_⟩
    rw [hcardAut, ← Gp.index_mul_card, h1]

end F429One

section OuterOrders

theorem burnsideF429_card_outer_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Outer G) = Nat.card (Outer H) :=
  Nat.card_congr (equivalence e).toEquiv

theorem burnsideF429_card_outer_D4two
    {H : Type} [Group H] (h : IsGenLie H .D4tw 2 1) : Nat.card (Outer H) = 3 := by
  obtain ⟨-, -, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  have hK' : Nat.card K = (2 ^ 1) ^ 3 := hK
  obtain ⟨σ', hσ', -, -⟩ :=
    CFSG.LieType.Chevalley.finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two le_rfl K hK'
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, ⟨Θ, -, hΘsurj, hΘker, -⟩, -, hcardAut, -, -, ⟨eDC⟩⟩ :=
    CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form le_rfl K hK' σ' hσ'
  rw [burnsideF429_card_outer_congr (e.trans eDC)]
  have hinner : inner (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) = Θ.ker := by
    rw [hΘker]
    rfl
  have e2 : Outer (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) ≃* (K ≃+* K) :=
    (QuotientGroup.quotientMulEquivOfEq hinner).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hΘsurj)
  rw [Nat.card_congr e2.toEquiv, hcardAut]

theorem burnsideF429_card_outer_Un_two {n : ℕ} (hn : n = 4 ∨ n = 5) {H : Type} [Group H]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (e : H ≃* StatedProj (StatedSU n (2 ^ 1) K)) : Nat.card (Outer H) = 2 := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ 1 = 2) := by omega
  obtain ⟨-, -, -, -, hout, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order hU hn3 hq
  rw [burnsideF429_card_outer_congr
    (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm), hout]
  rcases hn with rfl | rfl <;> norm_num

theorem burnsideF429_card_outer_U4two {H : Type} [Group H] (h : IsGenLie H .U4 2 1) :
    Nat.card (Outer H) = 2 := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := h
  exact burnsideF429_card_outer_Un_two (Or.inl rfl) hK e

theorem burnsideF429_card_outer_U5two {H : Type} [Group H] (h : IsGenLie H .U5 2 1) :
    Nat.card (Outer H) = 2 := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := h
  exact burnsideF429_card_outer_Un_two (Or.inr rfl) hK e

end OuterOrders

section F429Kinds

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_F429_one_D4two
    (hyp : HypF_4_4 .D4tw 2 1 Gp M₁ M₂) :
    Gp = ⊤ ∨ (Gp.index = 3 ∧ Nat.card E = Nat.card (MulAut ↥Gp)) := by
  haveI := hyp.finite
  haveI := hyp.normal
  exact burnsideF429_eq_top_or_of_card_outer hyp.centralizer_trivial Nat.prime_three
    (burnsideF429_card_outer_D4two hyp.model)

theorem burnsideF429_F429_one_Un_two {κ : GLKind} (hκ : κ = .U4 ∨ κ = .U5)
    (hyp : HypF_4_4 κ 2 1 Gp M₁ M₂) :
    Gp = ⊤ ∨ (Gp.index = 2 ∧ Nat.card E = Nat.card (MulAut ↥Gp)) := by
  haveI := hyp.finite
  haveI := hyp.normal
  have hout : Nat.card (Outer ↥Gp) = 2 := by
    rcases hκ with rfl | rfl
    · exact burnsideF429_card_outer_U4two hyp.model
    · exact burnsideF429_card_outer_U5two hyp.model
  exact burnsideF429_eq_top_or_of_card_outer hyp.centralizer_trivial Nat.prime_two hout

end F429Kinds

section L3Top

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF429_L3_marking {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .L3 2 1 Gp M₁ M₂) :
    ∃ θ : burnsideF4c_SL ≃* ↥Gp, burnsideF4c_P.map θ.toMonoidHom = M₁.subgroupOf Gp ∧
      burnsideF4c_L.map θ.toMonoidHom = M₂.subgroupOf Gp := by
  obtain ⟨marking, h1, h2⟩ := burnsideF4c_marking hyp
  have hcard : Nat.card marking.field = 2 := by
    have := marking.field_card
    simpa using this
  have hbasis : marking.basis = 1 := marking.basis_compatible
  let ε : marking.field ≃+* ZMod 2 := burnsideF4c_ringEquiv marking.field hcard
  let f1 := burnsideF4c_slEquiv marking.field ε.symm
  let f2 : Matrix.SpecialLinearGroup (Fin 3) marking.field ≃*
      ↥(nativeGroup .L3 (2 ^ 1) marking.field) :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field
  have hbot : (StatedScalars (Coord .L3) marking.field).subgroupOf
      (nativeGroup .L3 (2 ^ 1) marking.field) = ⊥ := burnsideF4c_scalars_bot marking.field ε
  let g : ↥(nativeGroup .L3 (2 ^ 1) marking.field) ≃*
      StatedProj (nativeGroup .L3 (2 ^ 1) marking.field) :=
    MulEquiv.ofBijective (projectiveMap .L3 (2 ^ 1) marking.field) ⟨by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact (QuotientGroup.ker_mk' _).trans hbot, QuotientGroup.mk'_surjective _⟩
  let θ₀ : burnsideF4c_SL ≃* ↥Gp := f1.trans (f2.trans (g.trans marking.identification))
  have hθ₀ : θ₀.toMonoidHom = marking.transport.comp (f2.toMonoidHom.comp f1.toMonoidHom) :=
    MonoidHom.ext fun _ => rfl
  have hent : ∀ (x : burnsideF4c_SL) (i j : Fin 3),
      (((f2 (f1 x) : ↥(nativeGroup .L3 (2 ^ 1) marking.field)) : GL (Fin 3) marking.field) :
        Matrix (Fin 3) (Fin 3) marking.field) i j =
      ε.symm ((x : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) := by
    intro x i j
    exact burnsideF4c_slEquiv_coe marking.field ε.symm x i j
  have hmemP : ∀ x : burnsideF4c_SL,
      f2 (f1 x) ∈ nativeParabolic .L3 (2 ^ 1) marking.field marking.basis false ↔
        x ∈ burnsideF4c_P := by
    intro x
    show ((f2 (f1 x) : ↥(nativeGroup .L3 (2 ^ 1) marking.field)) : GL (Fin 3) marking.field) ∈
      rawStabilizer ((fun vector => ((marking.basis : GL (Fin 3) marking.field) :
        Matrix (Fin 3) (Fin 3) marking.field).mulVec vector) '' coordinateSpace (flagOne .L3)) ↔ _
    rw [hbasis, burnsideF4c_flag_one, hent, hent]
    show ε.symm _ = 0 ∧ ε.symm _ = 0 ↔ burnsideF4c_inP x
    rw [map_eq_zero_iff _ ε.symm.injective, map_eq_zero_iff _ ε.symm.injective]
    exact Iff.rfl
  have hmemL : ∀ x : burnsideF4c_SL,
      f2 (f1 x) ∈ nativeParabolic .L3 (2 ^ 1) marking.field marking.basis true ↔
        x ∈ burnsideF4c_L := by
    intro x
    show ((f2 (f1 x) : ↥(nativeGroup .L3 (2 ^ 1) marking.field)) : GL (Fin 3) marking.field) ∈
      rawStabilizer ((fun vector => ((marking.basis : GL (Fin 3) marking.field) :
        Matrix (Fin 3) (Fin 3) marking.field).mulVec vector) '' coordinateSpace (flagTwo .L3)) ↔ _
    rw [hbasis, burnsideF4c_flag_two, hent, hent]
    show ε.symm _ = 0 ∧ ε.symm _ = 0 ↔ burnsideF4c_inL x
    rw [map_eq_zero_iff _ ε.symm.injective, map_eq_zero_iff _ ε.symm.injective]
    exact Iff.rfl
  have hsurj : Function.Surjective (f2.toMonoidHom.comp f1.toMonoidHom) := by
    intro y
    obtain ⟨a, rfl⟩ := f2.surjective y
    obtain ⟨x, rfl⟩ := f1.surjective a
    exact ⟨x, rfl⟩
  have hinj : Function.Injective (f2.toMonoidHom.comp f1.toMonoidHom) :=
    f2.injective.comp f1.injective
  have hmapP : burnsideF4c_P.map (f2.toMonoidHom.comp f1.toMonoidHom) =
      nativeParabolic .L3 (2 ^ 1) marking.field marking.basis false := by
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    rw [Subgroup.mem_map_iff_mem hinj]
    exact (hmemP x).symm
  have hmapL : burnsideF4c_L.map (f2.toMonoidHom.comp f1.toMonoidHom) =
      nativeParabolic .L3 (2 ^ 1) marking.field marking.basis true := by
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    rw [Subgroup.mem_map_iff_mem hinj]
    exact (hmemL x).symm
  refine ⟨θ₀, ?_, ?_⟩
  · rw [h1, hθ₀, ← Subgroup.map_map, hmapP]
    rfl
  · rw [h2, hθ₀, ← Subgroup.map_map, hmapL]
    rfl

@[expose] def burnsideF429_restrictAut {G : Type*} [Group G] (ψ : G ≃* G) (H : Subgroup G)
    (hH : ∀ x, ψ x ∈ H ↔ x ∈ H) : MulAut ↥H where
  toFun x := ⟨ψ (x : G), (hH x).2 x.2⟩
  invFun x := ⟨ψ.symm (x : G), (hH _).1 (by simpa using x.2)⟩
  left_inv x := Subtype.ext (ψ.symm_apply_apply (x : G))
  right_inv x := Subtype.ext (ψ.apply_symm_apply (x : G))
  map_mul' x y := Subtype.ext (map_mul ψ (x : G) (y : G))

theorem burnsideF429_restrictAut_apply {G : Type*} [Group G] (ψ : G ≃* G) (H : Subgroup G)
    (hH : ∀ x, ψ x ∈ H ↔ x ∈ H) (x : ↥H) :
    ((burnsideF429_restrictAut ψ H hH x : ↥H) : G) = ψ (x : G) := rfl

theorem burnsideF429_L3_aut_inner (ψ : burnsideF4c_SL ≃* burnsideF4c_SL)
    (hP : ∀ x, ψ x ∈ burnsideF4c_P ↔ x ∈ burnsideF4c_P)
    (hL : ∀ x, ψ x ∈ burnsideF4c_L ↔ x ∈ burnsideF4c_L) :
    ∃ g : burnsideF4c_SL, ∀ x, ψ x = g * x * g⁻¹ := by
  obtain ⟨g₀, hg₀⟩ := burnsideF4c_inn_P (burnsideF429_restrictAut ψ burnsideF4c_P hP)
  set g : burnsideF4c_SL := (g₀ : burnsideF4c_SL) with hgdef
  have hg : ∀ m ∈ burnsideF4c_P, ψ m = g * m * g⁻¹ := by
    intro m hm
    have := congrArg Subtype.val (hg₀ ⟨m, hm⟩)
    simpa [burnsideF429_restrictAut_apply] using this
  have hgD : g ∈ burnsideF4c_P ⊓ burnsideF4c_L := by
    refine burnsideF4c_norm_P g g₀.2 fun b hb => ?_
    rw [← hg b hb.1]
    exact ⟨(hP b).2 hb.1, (hL b).2 hb.2⟩
  have hgL : g ∈ burnsideF4c_L := hgD.2
  let ψ' : burnsideF4c_SL ≃* burnsideF4c_SL := ψ.trans (MulAut.conj g⁻¹)
  have hψ' : ∀ x, ψ' x = g⁻¹ * ψ x * g := by
    intro x
    show g⁻¹ * ψ x * g⁻¹⁻¹ = g⁻¹ * ψ x * g
    rw [inv_inv]
  have hψ'P : ∀ m ∈ burnsideF4c_P, ψ' m = m := by
    intro m hm
    rw [hψ', hg m hm]
    group
  have hψ'L : ∀ x, ψ' x ∈ burnsideF4c_L ↔ x ∈ burnsideF4c_L := by
    intro x
    rw [hψ', ← hL x]
    constructor
    · intro h
      have := burnsideF4c_L.mul_mem (burnsideF4c_L.mul_mem hgL h) (burnsideF4c_L.inv_mem hgL)
      simpa [mul_assoc] using this
    · intro h
      exact burnsideF4c_L.mul_mem (burnsideF4c_L.mul_mem (burnsideF4c_L.inv_mem hgL) h) hgL
  obtain ⟨h₀, hh₀⟩ := burnsideF4c_inn_L (burnsideF429_restrictAut ψ' burnsideF4c_L hψ'L)
  set h : burnsideF4c_SL := (h₀ : burnsideF4c_SL) with hhdef
  have hh : ∀ m ∈ burnsideF4c_L, ψ' m = h * m * h⁻¹ := by
    intro m hm
    have := congrArg Subtype.val (hh₀ ⟨m, hm⟩)
    simpa [burnsideF429_restrictAut_apply] using this
  have hcent : ∀ d ∈ burnsideF4c_P ⊓ burnsideF4c_L, h * d = d * h := by
    intro d hd
    have e1 := hh d hd.2
    rw [hψ'P d hd.1] at e1
    calc h * d = (h * d * h⁻¹) * h := by group
      _ = d * h := by rw [← e1]
  have hhD : h ∈ burnsideF4c_P ⊓ burnsideF4c_L := by
    refine burnsideF4c_norm_L h h₀.2 fun b hb => ?_
    have e : h * b * h⁻¹ = b := by rw [hcent b hb]; group
    rw [e]
    exact hb
  rcases burnsideF4c_centD h hhD hcent with h1 | hz
  · have hid : ∀ x, ψ' x = x := by
      have hle : burnsideF4c_P ⊔ burnsideF4c_L ≤
          MonoidHom.eqLocus ψ'.toMonoidHom (MonoidHom.id burnsideF4c_SL) := by
        refine sup_le (fun m hm => hψ'P m hm) (fun m hm => ?_)
        show ψ' m = m
        rw [hh m hm, h1]
        group
      rw [burnsideF4c_P_sup_L] at hle
      exact fun x => hle (Subgroup.mem_top x)
    refine ⟨g, fun x => ?_⟩
    have e := hid x
    rw [hψ'] at e
    calc ψ x = g * (g⁻¹ * ψ x * g) * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [e]
  · exfalso
    apply burnsideF4c_beta_not_equiv
    refine ⟨ψ', fun d x => ?_⟩
    cases d
    · obtain ⟨y, hy⟩ := x
      exact hψ'P y hy
    · obtain ⟨y, hy⟩ := x
      show ψ' y = burnsideF4c_z * y * burnsideF4c_z⁻¹
      rw [hh y hy, hz]
    · obtain ⟨y, hy⟩ := x
      exact hψ'P y hy.1

theorem burnsideF429_L3_Gp_top {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 1 Gp M₁ M₂) : Gp = ⊤ := by
  haveI : Gp.Normal := hyp.normal
  obtain ⟨θ, hθP, hθL⟩ := burnsideF429_L3_marking hyp.toHypF_4_4g
  have hconj : ∀ {M : Subgroup E} {e : E}, e ∈ M → ∀ y : E, e * y * e⁻¹ ∈ M ↔ y ∈ M := by
    intro M e he y
    constructor
    · intro h
      have := M.mul_mem (M.mul_mem (M.inv_mem he) h) he
      simpa [mul_assoc] using this
    · intro h
      exact M.mul_mem (M.mul_mem he h) (M.inv_mem he)
  have key : ∀ e ∈ M₁ ⊓ M₂, e ∈ Gp := by
    intro e he
    let c : ↥Gp ≃* ↥Gp := MulAut.conjNormal e
    have hc : ∀ y : ↥Gp, ((c y : ↥Gp) : E) = e * y * e⁻¹ := fun y => MulAut.conjNormal_apply e y
    let ψ : burnsideF4c_SL ≃* burnsideF4c_SL := θ.trans (c.trans θ.symm)
    have hψ : ∀ x, θ (ψ x) = c (θ x) := fun x => θ.apply_symm_apply _
    have hmem : ∀ {Q : Subgroup burnsideF4c_SL} {M : Subgroup E},
        Q.map θ.toMonoidHom = M.subgroupOf Gp → ∀ x, x ∈ Q ↔ ((θ x : ↥Gp) : E) ∈ M := by
      intro Q M hQ x
      rw [← Subgroup.mem_subgroupOf, ← hQ]
      exact (Subgroup.mem_map_iff_mem θ.injective).symm
    have hP : ∀ x, ψ x ∈ burnsideF4c_P ↔ x ∈ burnsideF4c_P := by
      intro x
      rw [hmem hθP, hmem hθP, hψ, hc]
      exact hconj he.1 _
    have hL : ∀ x, ψ x ∈ burnsideF4c_L ↔ x ∈ burnsideF4c_L := by
      intro x
      rw [hmem hθL, hmem hθL, hψ, hc]
      exact hconj he.2 _
    obtain ⟨g, hg⟩ := burnsideF429_L3_aut_inner ψ hP hL
    set t : E := ((θ g : ↥Gp) : E) with htdef
    have hcy : ∀ y : ↥Gp, e * y * e⁻¹ = t * y * t⁻¹ := by
      intro y
      have h1 := congrArg θ (hg (θ.symm y))
      rw [hψ, MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
      have h2 := congrArg Subtype.val h1
      rw [hc] at h2
      simpa [htdef] using h2
    have hcent : t⁻¹ * e ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hcy ⟨y, hy⟩
      simp only at h1
      calc y * (t⁻¹ * e) = t⁻¹ * (t * y * t⁻¹) * e := by group
        _ = t⁻¹ * (e * y * e⁻¹) * e := by rw [h1]
        _ = t⁻¹ * e * y := by group
    rw [hyp.centralizer_trivial, Subgroup.mem_bot] at hcent
    have he' : e = t := by
      calc e = t * (t⁻¹ * e) := by group
        _ = t := by rw [hcent, mul_one]
    rw [he']
    exact (θ g).2
  rw [eq_top_iff]
  intro x _
  obtain ⟨n, hn, k, hk, rfl⟩ := hyp.split x
  exact Gp.mul_mem hn (key k hk)

end L3Top

section TopSp

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF429_eq_zero_or_one_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2)
    (c : K) : c = 0 ∨ c = 1 := by
  classical
  by_contra h
  push Not at h
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have := Fintype.ofFinite K
  have h3 : ({0, 1, c} : Finset K).card = 3 :=
    Finset.card_eq_three.mpr ⟨0, 1, c, zero_ne_one, Ne.symm h.1, Ne.symm h.2, rfl⟩
  have hle := Finset.card_le_univ ({0, 1, c} : Finset K)
  rw [h3, ← Nat.card_eq_fintype_card, hK] at hle
  omega

theorem burnsideF429_ringEquiv_eq_one_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2)
    (φ : K ≃+* K) : φ = 1 := by
  ext c
  rcases burnsideF429_eq_zero_or_one_of_card_two hK c with rfl | rfl
  · rw [map_zero]
    rfl
  · rw [map_one]
    rfl

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_sp4_model_card (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (θ : StatedSp 2 K →* E),
      Nat.card K = 2 ^ f ∧ Function.Injective θ ∧ θ.range = Gp ∧
        Gp ⊓ M₁ = (Q2 K 0).map θ ∧ Gp ⊓ M₂ = (Q2 K 1).map θ := by
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .Sp4) hyp.toHypF_4_4g
  have hK : Nat.card marking.field = 2 ^ f := by
    have := marking.field_card
    simpa using this
  haveI : CharP marking.field 2 := burnsideF4gSp_charP_of_card hK
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have hinj : Function.Injective marking.transport := by
    refine (injective_iff_map_eq_one marking.transport).2 fun a ha => ?_
    have h3 := (burnsideF4f_transport_eq_one_iff marking a).1 ha
    exact Subtype.ext (burnsideF4gSpInv_scalar_eq_one h3 a.2)
  have hsurj := burnsideF4f_transport_surjective marking
  have keyS : ∀ (S : Set (Fin 2 ⊕ Fin 2))
      (W : Submodule marking.field (Fin 2 ⊕ Fin 2 → marking.field))
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) marking.field),
      (∀ v, v ∈ coordinateSpace S ↔ v ∈ W) →
      ((∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ coordinateSpace S ↔
          v ∈ coordinateSpace S) ↔
        ∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ W ↔ v ∈ W) := by
    intro S W A hS
    simp only [hS]
  have key : ∀ b : Bool, nativeParabolic .Sp4 (2 ^ f) marking.field marking.basis b =
      Q2 marking.field (if b then 1 else 0) := by
    intro b
    rw [hbasis]
    ext g
    have h1 : g ∈ nativeParabolic .Sp4 (2 ^ f) marking.field 1 b ↔
        (g : GL (Coord .Sp4) marking.field) ∈ rawStabilizer ((fun vector =>
            ((1 : GL (Coord .Sp4) marking.field) : Matrix (Coord .Sp4) (Coord .Sp4)
              marking.field).mulVec vector) ''
          coordinateSpace (if b then flagTwo .Sp4 else flagOne .Sp4 : Set (Coord .Sp4))) :=
      Iff.rfl
    rw [h1, burnsideF4gSp_mem_rawStabilizer, burnsideF4gSp_image_one, Q2]
    refine Iff.trans ?_
      (burnsideF4gSp_mem_stabilizer_iff (r := 2) (K := marking.field) _ g).symm
    cases b
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).1)
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).2)
  let θ : StatedSp 2 marking.field →* E := Gp.subtype.comp marking.transport
  have hθinj : Function.Injective θ := Gp.subtype_injective.comp hinj
  have hrange : θ.range = Gp := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (marking.transport y).2
    · intro hx
      obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  have hpar : ∀ (b : Bool) (M : Subgroup E), M.subgroupOf Gp = marking.parabolic b →
      Gp ⊓ M = (Q2 marking.field (if b then 1 else 0)).map θ := by
    intro b M hM
    have e1 : marking.parabolic b =
        (Q2 marking.field (if b then 1 else 0)).map marking.transport :=
      congrArg (Subgroup.map marking.transport) (key b)
    calc Gp ⊓ M = (M.subgroupOf Gp).map Gp.subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      _ = ((Q2 marking.field (if b then 1 else 0)).map marking.transport).map Gp.subtype := by
          rw [hM, e1]
      _ = (Q2 marking.field (if b then 1 else 0)).map θ := Subgroup.map_map _ _ _
  exact ⟨marking.field, inferInstance, inferInstance, inferInstance, θ, hK, hθinj, hrange,
    by simpa using hpar false M₁ h1, by simpa using hpar true M₂ h2⟩

theorem burnsideF429_transvectionT₀_eq {K : Type} [Field K] :
    CFSG.RankThree.PartOne.KCSpComm.transvectionT₀ K = burnsideF4gSpInv_xl (1 : K) := by
  apply Subtype.ext
  apply Units.ext
  rw [burnsideF4gSpInv_xl_val]
  exact coe_upperUnipotentSp _

theorem burnsideF429_xl_mem_ctr_oPPrime {K : Type} [Field K] [Finite K] [CharP K 2] {t : K}
    (ht : t ≠ 0) : burnsideF4gSpInv_xl t ∈ ctr (oPPrime 2 (Q2 K 0)) := by
  rw [burnsideF4gSpInv_oPPrime_eq_S1]
  refine ⟨show burnsideF4gSpInv_xl t ∈ burnsideF4gSpInv_S1 K from ?_,
    Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
  · rw [burnsideF4gSpInv_mem_S1, burnsideF4gSpInv_xl_mv]
    simp
  · rw [← burnsideF4gSpInv_centralizer_xl ht] at hs
    exact Subgroup.mem_centralizer_singleton_iff.1 hs

theorem burnsideF429_top_Sp4two (hyp : HypF_4_4 .Sp4 2 1 Gp M₁ M₂) : Gp = ⊤ := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨K, _, _, _, θ, hK, hθinj, hrange, hM₁, -⟩ := burnsideF429_sp4_model_card hyp
  rw [pow_one] at hK
  let Ψ : StatedSp 2 K ≃* ↥Gp :=
    (MonoidHom.ofInjective hθinj).trans (MulEquiv.subgroupCongr hrange)
  have hΨ : ∀ g, ((Ψ g : ↥Gp) : E) = θ g := fun g => rfl
  let π : StatedSp 2 K ≃* StatedProj (StatedSp 2 K) :=
    MulEquiv.ofBijective (proj 2 K) CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
  have hπ : ∀ g, π g = proj 2 K g := fun g => rfl
  let Φ : StatedProj (StatedSp 2 K) ≃* ↥Gp := π.symm.trans Ψ
  have hΦ : ∀ g, Φ (proj 2 K g) = Ψ g := fun g => by
    show Ψ (π.symm (proj 2 K g)) = Ψ g
    rw [← hπ, MulEquiv.symm_apply_apply]
  have hZ1 : ctr (oPPrime 2 (Gp ⊓ M₁)) = (ctr (oPPrime 2 (Q2 K 0))).map θ := by
    rw [hM₁, burnsideF4d_oPPrime_map θ hθinj, burnsideF4j_ctr_map θ hθinj]
  have hxl1 : burnsideF4gSpInv_xl (1 : K) ≠ 1 := burnsideF4gSpInv_xl_ne_one one_ne_zero
  rw [eq_top_iff]
  intro e _
  obtain ⟨n, hn, x, hx, rfl⟩ := hyp.split e
  suffices hxG : x ∈ Gp from Gp.mul_mem hn hxG
  have hfixE : x * θ (burnsideF4gSpInv_xl 1) * x⁻¹ = θ (burnsideF4gSpInv_xl 1) := by
    have hxN : x ∈ Subgroup.normalizer ((ctr (oPPrime 2 (Gp ⊓ M₁)) : Subgroup E) : Set E) :=
      burnsideF4j_mem_normalizer_ctr (burnsideF4d_Z1_normalizer_oPPrime
        (burnsideF4j_le_normalizer_inf hyp.normal M₁ hx.1))
    have hmem : θ (burnsideF4gSpInv_xl 1) ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) := by
      rw [hZ1]
      exact ⟨_, burnsideF429_xl_mem_ctr_oPPrime one_ne_zero, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff.mp hxN _).mp hmem
    rw [hZ1] at hconj
    obtain ⟨z', hz', hz'e⟩ := hconj
    obtain ⟨t, rfl⟩ := burnsideF4gSpInv_ctr_oPPrime hz'
    rcases burnsideF429_eq_zero_or_one_of_card_two hK t with rfl | rfl
    · exfalso
      rw [burnsideF4gSpInv_xl_zero, map_one] at hz'e
      have h1 : θ (burnsideF4gSpInv_xl 1) = 1 := by
        have := congrArg (fun y => x⁻¹ * y * x) hz'e
        simpa [mul_assoc] using this.symm
      exact hxl1 (hθinj (h1.trans (map_one θ).symm))
    · exact hz'e.symm
  let α : MulAut (StatedProj (StatedSp 2 K)) := (Φ.trans (burnsideF4d_rho Gp x)).trans Φ.symm
  have hα : ∀ g, Φ (α (proj 2 K g)) = burnsideF4d_rho Gp x (Ψ g) := fun g => by
    show Φ (Φ.symm (burnsideF4d_rho Gp x (Φ (proj 2 K g)))) = _
    rw [MulEquiv.apply_symm_apply, hΦ]
  have hfix : α (proj 2 K (CFSG.RankThree.PartOne.KCSpComm.transvectionT₀ K)) =
      proj 2 K (CFSG.RankThree.PartOne.KCSpComm.transvectionT₀ K) := by
    rw [burnsideF429_transvectionT₀_eq]
    apply Φ.injective
    rw [hα, hΦ]
    apply Subtype.ext
    rw [burnsideF4d_rho_apply, hΨ, hfixE]
  have hαE : α ∈ spSemilinearAutGroup 2 K := by
    by_contra h
    exact CFSG.RankThree.PartOne.KCSpComm.not_fixes_transvectionT₀_of_not_mem h hfix
  obtain ⟨g, φ, hgφ⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exists_eq_spInner_mul_fieldAut hαE
  rw [burnsideF429_ringEquiv_eq_one_of_card_two hK φ, map_one, mul_one,
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.spInner_eq_conj] at hgφ
  have hcomm : ∀ m ∈ Gp, x * m * x⁻¹ = θ g * m * (θ g)⁻¹ := by
    intro m hm
    obtain ⟨h, rfl⟩ := hrange ▸ hm
    have h1 := hα h
    rw [hgφ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hΦ] at h1
    have h2 := congrArg Subtype.val h1
    rw [burnsideF4d_rho_apply, hΨ, hΨ, map_mul, map_mul, map_inv] at h2
    exact h2.symm
  have hcx : (θ g)⁻¹ * x ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 := hcomm m hm
    calc m * ((θ g)⁻¹ * x) = (θ g)⁻¹ * (θ g * m * (θ g)⁻¹) * x := by group
      _ = (θ g)⁻¹ * (x * m * x⁻¹) * x := by rw [h1]
      _ = (θ g)⁻¹ * x * m := by group
  rw [hyp.centralizer_trivial, Subgroup.mem_bot, inv_mul_eq_one] at hcx
  rw [← hcx, ← hrange]
  exact ⟨g, rfl⟩

end TopSp

section TopGeneral

theorem burnsideF429_finite_mulAut (H : Type) [Group H] [Finite H] : Finite (MulAut H) :=
  Finite.of_injective (fun f : MulAut H => (f : H → H)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem burnsideF429_eq_top_of_derived {E : Type} [Group E] [Finite E] {Gp : Subgroup E}
    [hGn : Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hcN : ∀ g ∈ Gp, (∀ n ∈ ⁅Gp, Gp⁆, g * n = n * g) → g = 1)
    (haut : Nat.card (MulAut ↥⁅Gp, Gp⁆) ≤ Nat.card Gp) : Gp = ⊤ := by
  haveI hN : (⁅Gp, Gp⁆ : Subgroup E).Normal := Subgroup.commutator_normal Gp Gp
  have hinj : Function.Injective (MulAut.conjNormal : E →* MulAut ↥⁅Gp, Gp⁆) := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hen : ∀ n ∈ ⁅Gp, Gp⁆, e * n = n * e := by
      intro n hn
      have h := congrArg (fun φ : MulAut ↥⁅Gp, Gp⁆ => ((φ ⟨n, hn⟩ : ↥⁅Gp, Gp⁆) : E)) he
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
      calc e * n = e * n * e⁻¹ * e := by group
        _ = n * e := by rw [h]
    have heC : e ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hk : e * g * e⁻¹ ∈ Gp := hGn.conj_mem g hg e
      have hh : g⁻¹ * (e * g * e⁻¹) ∈ Gp := Gp.mul_mem (Gp.inv_mem hg) hk
      have h1 : g⁻¹ * (e * g * e⁻¹) = 1 := by
        refine hcN _ hh fun n hn => ?_
        have hgn : g * n * g⁻¹ ∈ ⁅Gp, Gp⁆ := hN.conj_mem n hn g
        have hc1 : e⁻¹ * n = n * e⁻¹ := by
          calc e⁻¹ * n = e⁻¹ * (n * e) * e⁻¹ := by group
            _ = e⁻¹ * (e * n) * e⁻¹ := by rw [hen n hn]
            _ = n * e⁻¹ := by group
        have hc2 := hen _ hgn
        calc g⁻¹ * (e * g * e⁻¹) * n = g⁻¹ * e * g * (e⁻¹ * n) := by group
          _ = g⁻¹ * e * g * (n * e⁻¹) := by rw [hc1]
          _ = g⁻¹ * (e * (g * n * g⁻¹)) * g * e⁻¹ := by group
          _ = g⁻¹ * ((g * n * g⁻¹) * e) * g * e⁻¹ := by rw [hc2]
          _ = n * (g⁻¹ * (e * g * e⁻¹)) := by group
      have h2 : e * g * e⁻¹ = g := by
        calc e * g * e⁻¹ = g * (g⁻¹ * (e * g * e⁻¹)) := by group
          _ = g := by rw [h1, mul_one]
      calc g * e = e * g * e⁻¹ * e := by rw [h2]
        _ = e * g := by group
    rw [hc, Subgroup.mem_bot] at heC
    exact heC
  haveI := burnsideF429_finite_mulAut ↥⁅Gp, Gp⁆
  have hle : Nat.card E ≤ Nat.card (MulAut ↥⁅Gp, Gp⁆) := Nat.card_le_card_of_injective _ hinj
  exact Subgroup.eq_top_of_card_eq Gp
    (le_antisymm (Subgroup.card_le_card_group Gp) (hle.trans haut))

theorem burnsideF429_eq_top_of_model {E : Type} [Group E] [Finite E] {Gp : Subgroup E}
    [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥) {M : Type} [Group M]
    (ψ : M ≃* ↥Gp) (hcM : ∀ g : M, (∀ n ∈ commutator M, g * n = n * g) → g = 1)
    (hautM : Nat.card (MulAut ↥(commutator M)) ≤ Nat.card M) : Gp = ⊤ := by
  let f : M →* E := Gp.subtype.comp ψ.toMonoidHom
  have hf : ∀ m, f m = ((ψ m : ↥Gp) : E) := fun _ => rfl
  have hfi : Function.Injective f := Gp.subtype_injective.comp ψ.injective
  have hrange : f.range = Gp := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      rw [hf]
      exact (ψ m).2
    · intro hx
      exact ⟨ψ.symm ⟨x, hx⟩, by rw [hf, MulEquiv.apply_symm_apply]⟩
  have hmap : (commutator M).map f = ⁅Gp, Gp⁆ := by
    rw [map_commutator_eq, hrange]
  refine burnsideF429_eq_top_of_derived hc ?_ ?_
  · intro g hg hgN
    have hg' : g ∈ f.range := hrange.symm ▸ hg
    obtain ⟨m, rfl⟩ := hg'
    have hm : m = 1 := hcM m fun n hn => hfi (by
      rw [map_mul, map_mul]
      exact hgN (f n) (hmap ▸ Subgroup.mem_map_of_mem f hn))
    rw [hm, map_one]
  · have e1 : ↥(commutator M) ≃* ↥⁅Gp, Gp⁆ :=
      ((commutator M).equivMapOfInjective f hfi).trans (MulEquiv.subgroupCongr hmap)
    rw [← Nat.card_congr (MulAut.congr e1).toEquiv, ← Nat.card_congr ψ.toEquiv]
    exact hautM

theorem burnsideF429_indexTwo_centralizer {J N : Type*} [Group J] [Group N] {f : J →* N}
    {ρ : N} {Φ : J ≃* J} (D : CFSG.Quasithin.IndexTwoData f ρ Φ) (hZ : Subgroup.center J = ⊥)
    (g : N) (hg : ∀ x, g * f x = f x * g) : g = 1 := by
  rcases D.cover g with ⟨w, rfl⟩ | ⟨w, hw⟩
  · have hw : w ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply D.inj
      rw [map_mul, map_mul]
      exact (hg x).symm
    rw [hZ, Subgroup.mem_bot] at hw
    rw [hw, map_one]
  · exfalso
    apply D.outer
    have hsq : ρ * ρ = 1 := D.sq
    have hρ : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hsq
    have hg' : g = f w * ρ := by
      calc g = g * ρ * ρ := by rw [mul_assoc, hsq, mul_one]
        _ = f w * ρ := by rw [hw]
    refine ⟨w⁻¹, fun x => D.inj ?_⟩
    have h1 := hg x
    rw [hg'] at h1
    have h3 : ρ * f x * ρ⁻¹ = f (Φ x) := D.conj x
    rw [map_mul, map_mul, map_inv, inv_inv, ← h3, hρ]
    calc ρ * f x * ρ = (f w)⁻¹ * (f w * ρ * f x) * ρ := by group
      _ = (f w)⁻¹ * (f x * (f w * ρ)) * ρ := by rw [h1]
      _ = (f w)⁻¹ * f x * f w * (ρ * ρ) := by group
      _ = (f w)⁻¹ * f x * f w := by rw [hsq, mul_one]

end TopGeneral

section G2Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin

set_option linter.unusedSectionVars false

theorem burnsideF429_u33_equiv_QP :
    Nonempty (U33G ≃* ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup) := by
  obtain ⟨e3⟩ := CFSG.Quasithin.u33Pres_mulEquiv_perm
  have hsz : CFSG.Quasithin.u33Gens.size = 5 := CFSG.Quasithin.u33Chain_check.1
  have hset : {g | ∃ k < CFSG.Quasithin.u33Gens.size,
      CFSG.Monster.B.Co2.permOfArr 28 CFSG.Quasithin.u33Gens[k]! = g} =
      Set.range CFSG.Quasithin.u33Img := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [hsz] at hk
      exact ⟨⟨k, hk⟩, (CFSG.Quasithin.permOfArr_u33Gens ⟨k, hk⟩).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by rw [hsz]; exact k.2, CFSG.Quasithin.permOfArr_u33Gens k⟩
  rw [hset, CFSG.GH74.KGroups.U33.J_eq] at e3
  exact ⟨e3⟩

theorem burnsideF429_g2_commutator {K : Type} [Field K] (h2 : (2 : K) = 0)
    (hk2 : ∀ c : K, c = 0 ∨ c = 1) : commutator (G2Group K) = (g2HomC h2).range := by
  apply Subgroup.map_injective (adjointGroup Tag.G2 K).subtype_injective
  have hcomp : (adjointGroup Tag.G2 K).subtype.comp (g2HomC h2) = g2Hom h2 :=
    MonoidHom.ext fun _ => rfl
  rw [map_commutator_eq, Subgroup.range_subtype, g2_derived_eq_range h2 hk2, MonoidHom.map_range,
    hcomp]

theorem burnsideF429_g2_centralizer {K : Type} [Field K] (h2 : (2 : K) = 0)
    (hk2 : ∀ c : K, c = 0 ∨ c = 1) (g : G2Group K)
    (hg : ∀ n ∈ commutator (G2Group K), g * n = n * g) : g = 1 := by
  rw [burnsideF429_g2_commutator h2 hk2] at hg
  exact burnsideF429_indexTwo_centralizer (g2IndexTwoData h2 hk2) burnsideF4h_g2_center_u33 g
    fun x => hg _ ⟨x, rfl⟩

theorem burnsideF429_g2_card_mulAut {K : Type} [Field K] (h2 : (2 : K) = 0)
    (hk2 : ∀ c : K, c = 0 ∨ c = 1) :
    Nat.card (MulAut ↥(commutator (G2Group K))) ≤ Nat.card (G2Group K) := by
  have e1 : ↥(commutator (G2Group K)) ≃* U33G :=
    (MulEquiv.subgroupCongr (burnsideF429_g2_commutator h2 hk2)).trans
      (MonoidHom.ofInjective (g2HomC_injective h2)).symm
  obtain ⟨e3⟩ := burnsideF429_u33_equiv_QP
  rw [CFSG.GH74.KGroups.U33.card_mulAut (e1.trans e3)]
  have hidx := (g2IndexTwoData h2 hk2).index_range
  have hcard : Nat.card (g2HomC h2).range = 6048 := by
    rw [← card_u33Pres]
    exact (Nat.card_congr (MonoidHom.ofInjective (g2HomC_injective h2)).toEquiv).symm
  have h := Subgroup.card_mul_index (g2HomC h2).range
  rw [hcard, hidx] at h
  omega

theorem burnsideF429_top_of_G2two {E : Type} [Group E] [Finite E] {Gp : Subgroup E} [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) (hmodel : IsGenLie ↥Gp .G2 2 1) : Gp = ⊤ := by
  obtain ⟨-, -, K, fK, finK, hK, ⟨e⟩⟩ := hmodel
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have h2 := two_eq_zero_of_card_two hK2
  have hk2 := eq_zero_or_eq_one_of_card_two hK2
  have hZ : Subgroup.center (G2Group K) = ⊥ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let φ : AdjointQuotient Tag.G2 K ≃* G2Group K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact burnsideF429_eq_top_of_model hc (φ.symm.trans e.symm) (burnsideF429_g2_centralizer h2 hk2)
    (burnsideF429_g2_card_mulAut h2 hk2)

end G2Two

section F4Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Sporadic.Schreier.Tits CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag

set_option linter.unusedSectionVars false

theorem burnsideF429_titsA_commutator : commutator ↥titsA = titsD.subgroupOf titsA := by
  apply Subgroup.map_injective titsA.subtype_injective
  rw [map_commutator_eq, Subgroup.range_subtype, titsA_commutator,
    Subgroup.map_subgroupOf_eq_of_le titsD_le_titsA]

theorem burnsideF429_titsA_centralizer (g : ↥titsA)
    (hg : ∀ n ∈ commutator ↥titsA, g * n = n * g) : g = 1 := by
  rw [burnsideF429_titsA_commutator] at hg
  apply titsConj_injective
  rw [map_one]
  refine MulEquiv.ext fun d => Subtype.ext ?_
  rw [coe_titsConj_apply, MulAut.one_apply]
  have h := congrArg Subtype.val (hg ⟨d, titsD_le_titsA d.2⟩ d.2)
  simp only [Subgroup.coe_mul] at h
  rw [h, mul_inv_cancel_right]

theorem burnsideF429_titsA_card_mulAut :
    Nat.card (MulAut ↥(commutator ↥titsA)) ≤ Nat.card ↥titsA := by
  have e1 : ↥(commutator ↥titsA) ≃* ↥titsD :=
    (MulEquiv.subgroupCongr burnsideF429_titsA_commutator).trans
      (Subgroup.subgroupOfEquivOfLe titsD_le_titsA)
  rw [Nat.card_congr (MulAut.congr e1).toEquiv, ← Nat.card_congr titsConjEquiv.toEquiv]

theorem burnsideF429_top_of_F4two {E : Type} [Group E] [Finite E] {Gp : Subgroup E} [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) (hmodel : IsGenLie ↥Gp .F4tw 2 1) : Gp = ⊤ := by
  obtain ⟨-, -, ⟨-, K, fK, finK, hK, ⟨e⟩⟩ | ⟨h3, -⟩⟩ := hmodel
  · haveI : CharP K 2 := by
      have : Fintype K := Fintype.ofFinite K
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
    haveI : CharP K F4.prime := (inferInstance : CharP K 2)
    haveI : Fact (Nat.card K = 2) := ⟨hK⟩
    have hR : ExceptionalRoots.reeGroup K 0 = F4.reeGamma K 0 := burnsideF4gF4_reeGroup_eq
    let ψ1 : ↥(ExceptionalRoots.reeGroup K 0) ≃* ↥(F4.reeGamma K 0) := MulEquiv.subgroupCongr hR
    let ψ2 : ↥(reeFixed F4 K 0) ≃* ↥titsA := titsIso
    let ψ3 : ↥(reeFixed F4 K 0) ≃* ↥(F4.reeGamma K 0) := reeFixedEquivReeGamma K 0
    let ψ : ↥(ExceptionalRoots.reeGroup K 0) ≃* ↥titsA := (ψ1.trans ψ3.symm).trans ψ2
    have hZ : Subgroup.center ↥(ExceptionalRoots.reeGroup K 0) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      have h1 : ψ z = 1 := burnsideF429_titsA_centralizer (ψ z) fun n _ => by
        obtain ⟨m, rfl⟩ := ψ.surjective n
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz m]
      exact ψ.injective (h1.trans (map_one ψ).symm)
    let φ : (↥(ExceptionalRoots.reeGroup K 0) ⧸ Subgroup.center ↥(ExceptionalRoots.reeGroup K 0))
        ≃* ↥(ExceptionalRoots.reeGroup K 0) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact burnsideF429_eq_top_of_model hc ((ψ.symm.trans φ.symm).trans e.symm)
      burnsideF429_titsA_centralizer burnsideF429_titsA_card_mulAut
  · omega

end F4Two

section TopTwo

set_option linter.unusedSectionVars false

theorem burnsideF429_top_G2two {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 1 Gp M₁ M₂) : Gp = ⊤ := by
  haveI := hyp.finite
  haveI := hyp.normal
  exact burnsideF429_top_of_G2two hyp.centralizer_trivial hyp.model

end TopTwo

section TopF4

set_option linter.unusedSectionVars false

theorem burnsideF429_top_F4two {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .F4tw 2 1 Gp M₁ M₂) : Gp = ⊤ := by
  haveI := hyp.finite
  haveI := hyp.normal
  exact burnsideF429_top_of_F4two hyp.centralizer_trivial hyp.model

end TopF4

section Clause1

open CFSG.ASVolI.ChF

theorem burnsideF429_clause1 :
    ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ 2 f Gp M₁ M₂ → κ.IsLie → f = 1 →
        Gp = ⊤ ∨ (κ = .D4tw ∧ Gp.index = 3 ∧ Nat.card E = Nat.card (MulAut ↥Gp)) ∨
          ((κ = .U4 ∨ κ = .U5) ∧ Gp.index = 2 ∧ Nat.card E = Nat.card (MulAut ↥Gp)) := by
  intro κ f E _ Gp M₁ M₂ hyp hκ hf
  subst hf
  cases κ with
  | L3 => exact Or.inl (burnsideF429_L3_Gp_top hyp)
  | Sp4 => exact Or.inl (burnsideF429_top_Sp4two hyp)
  | G2 => exact Or.inl (burnsideF429_top_G2two hyp)
  | D4tw =>
    rcases burnsideF429_F429_one_D4two hyp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, h⟩)
  | F4tw => exact Or.inl (burnsideF429_top_F4two hyp)
  | U4 =>
    rcases burnsideF429_F429_one_Un_two (Or.inl rfl) hyp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨Or.inl rfl, h⟩)
  | U5 =>
    rcases burnsideF429_F429_one_Un_two (Or.inr rfl) hyp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨Or.inr rfl, h⟩)
  | G2d => exact absurd rfl hκ.1
  | Tits => exact absurd rfl hκ.2

end Clause1

end CFSG.ASVolI
