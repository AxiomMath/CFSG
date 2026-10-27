module

public import CFSG.Milestones.ASVolI.F48.Small.Base
public import CFSG.Milestones.ASVolI.F4Small
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F4Native

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF48s_L3_marking {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
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

@[expose] def burnsideF48s_restrictAut {G : Type*} [Group G] (ψ : G ≃* G) (H : Subgroup G)
    (hH : ∀ x, ψ x ∈ H ↔ x ∈ H) : MulAut ↥H where
  toFun x := ⟨ψ (x : G), (hH x).2 x.2⟩
  invFun x := ⟨ψ.symm (x : G), (hH _).1 (by simpa using x.2)⟩
  left_inv x := Subtype.ext (ψ.symm_apply_apply (x : G))
  right_inv x := Subtype.ext (ψ.apply_symm_apply (x : G))
  map_mul' x y := Subtype.ext (map_mul ψ (x : G) (y : G))

theorem burnsideF48s_restrictAut_apply {G : Type*} [Group G] (ψ : G ≃* G) (H : Subgroup G)
    (hH : ∀ x, ψ x ∈ H ↔ x ∈ H) (x : ↥H) :
    ((burnsideF48s_restrictAut ψ H hH x : ↥H) : G) = ψ (x : G) := rfl

theorem burnsideF48s_L3_aut_inner (ψ : burnsideF4c_SL ≃* burnsideF4c_SL)
    (hP : ∀ x, ψ x ∈ burnsideF4c_P ↔ x ∈ burnsideF4c_P)
    (hL : ∀ x, ψ x ∈ burnsideF4c_L ↔ x ∈ burnsideF4c_L) :
    ∃ g : burnsideF4c_SL, ∀ x, ψ x = g * x * g⁻¹ := by
  obtain ⟨g₀, hg₀⟩ := burnsideF4c_inn_P (burnsideF48s_restrictAut ψ burnsideF4c_P hP)
  set g : burnsideF4c_SL := (g₀ : burnsideF4c_SL) with hgdef
  have hg : ∀ m ∈ burnsideF4c_P, ψ m = g * m * g⁻¹ := by
    intro m hm
    have := congrArg Subtype.val (hg₀ ⟨m, hm⟩)
    simpa [burnsideF48s_restrictAut_apply] using this
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
  obtain ⟨h₀, hh₀⟩ := burnsideF4c_inn_L (burnsideF48s_restrictAut ψ' burnsideF4c_L hψ'L)
  set h : burnsideF4c_SL := (h₀ : burnsideF4c_SL) with hhdef
  have hh : ∀ m ∈ burnsideF4c_L, ψ' m = h * m * h⁻¹ := by
    intro m hm
    have := congrArg Subtype.val (hh₀ ⟨m, hm⟩)
    simpa [burnsideF48s_restrictAut_apply] using this
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

theorem burnsideF48s_L3_Gp_top {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 1 Gp M₁ M₂) : Gp = ⊤ := by
  haveI : Gp.Normal := hyp.normal
  obtain ⟨θ, hθP, hθL⟩ := burnsideF48s_L3_marking hyp.toHypF_4_4g
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
    obtain ⟨g, hg⟩ := burnsideF48s_L3_aut_inner ψ hP hL
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

@[expose] def burnsideF48s_L3_tau : burnsideF4c_Amal.Iso burnsideF4c_Amal where
  φ1 := MulEquiv.refl _
  φ12 := MulEquiv.refl _
  φ2 := MulAut.conj (⟨burnsideF4c_z, burnsideF4c_z_mem.2⟩ : ↥burnsideF4c_L)
  comm1 _ := rfl
  comm2 d := by
    obtain ⟨y, hy⟩ := d
    apply Subtype.ext
    show y = burnsideF4c_z * y * burnsideF4c_z⁻¹
    rw [burnsideF4c_z_central y hy, mul_inv_cancel_right]

theorem burnsideF48s_L3_qe_concrete {Y : Type} [Group Y] (c : burnsideF4c_Amal.Completion Y)
    (hc : c.IsFaithful) (hs : c.IsSmall 3) :
    Amalgam.Completion.IsQuasiEquivalent c.toCompletion burnsideF4c_beta1.toCompletion := by
  have h12 : ∀ (e : Y ≃* burnsideF4c_SL),
      (∀ (a : burnsideF4c_SL) (ha : a ∈ burnsideF4c_P), e (burnsideF4c_ph1 c ⟨a, ha⟩) = a) →
      ∀ x : ↥(burnsideF4c_P ⊓ burnsideF4c_L), e (c.φ12 x) = x := by
    intro e he1 x
    rw [← c.comm1 x]
    exact he1 _ x.2.1
  rcases burnsideF4c_classify hc hs with ⟨e, he1, he2⟩ | ⟨e, he1, he2⟩
  · refine ⟨e, burnsideF48_toAmIso
      ⟨MulEquiv.refl _, MulEquiv.refl _, MulEquiv.refl _, fun _ => rfl, fun _ => rfl⟩,
      fun d x => ?_⟩
    cases d
    · exact he1 _ (x : ↥burnsideF4c_P).2
    · exact he2 _ (x : ↥burnsideF4c_L).2
    · exact h12 e he1 x
  · refine ⟨e, burnsideF48_toAmIso burnsideF48s_L3_tau, fun d x => ?_⟩
    cases d
    · exact he1 _ (x : ↥burnsideF4c_P).2
    · exact he2 _ (x : ↥burnsideF4c_L).2
    · exact h12 e he1 x

section


theorem burnsideF48s_small_L3_two {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 1 Gp M₁ M₂) : F48Concl .L3 2 1 Gp M₁ M₂ := by
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  have hGp := burnsideF48s_L3_Gp_top hyp
  subst hGp
  obtain ⟨θ, rfl, rfl⟩ := burnsideF4c_part0 hyp
  let ψ := burnsideF4c_amalIso θ burnsideF4c_P burnsideF4c_L
  refine burnsideF48s_concl_of_qe hext (burnsideF48_comap ψ burnsideF4c_beta1)
    ((burnsideF48_comap_isFaithful_iff ψ _).2 burnsideF4c_beta1_faithful)
    ((burnsideF48_comap_isSmall_iff ψ _ 3).2 burnsideF4c_beta1_small) θ ?_
  intro Y _ β hβ hs
  refine burnsideF48_isQuasiEquivalent_comap ψ β burnsideF4c_beta1 ?_
  exact burnsideF48s_L3_qe_concrete _
    ((burnsideF48_comap_isFaithful_iff (burnsideF48_isoSymm ψ) β).2 hβ)
    ((burnsideF48_comap_isSmall_iff (burnsideF48_isoSymm ψ) β 3).2 hs)

end

end CFSG.ASVolI
