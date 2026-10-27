module

public import CFSG.RankThree.GF2n.Smith81.S81TNonfused
public import CFSG.RankThree.GF2n.Smith81.S81KInvolRed
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.PairTransfer

public section

namespace CFSG.RankThree.GF2n.Smith81.SK

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.EGeom

section ElemBound

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {E : Type} [AddCommGroup E] [Module K E] {Γ U₀ : Subgroup (E ≃ₗ[K] E)} {p₀ : E}
  {ψ : M₀.E ≃ₗ[K] E} {φ : Lgen M (LB M Q B) →* (E ≃ₗ[K] E)}

theorem elemBound_transport (hc : Ctx M Q Z B)
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) [(Q.subgroupOf M).Normal] (m : ℕ)
    (hcore : ∀ A' : Subgroup (E ≃ₗ[K] E), A' ≤ Γ → IsElemAbelian 2 A' → Nat.card A' ≤ m)
    (A : Subgroup (↥M ⧸ Q.subgroupOf M)) (hAS : A ≤ bar M Q (Lgen M (LB M Q B)))
    (hAel : IsElemAbelian 2 A) : Nat.card A ≤ m := by
  have hLM : Lgen M (LB M Q B) ≤ M := iSup₂_le fun m hm => by
    calc conjSubgroup m (LB M Q B) ≤ conjSubgroup m M := Subgroup.map_mono hc.LB_le_M
      _ = M := hc.conj_M_eq hm
  set θ : ↥(Lgen M (LB M Q B)) →* ↥M ⧸ Q.subgroupOf M :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hLM) with hθ
  have hker : θ.ker = φ.ker := by
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, d.ker s, hθ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hAθ : A ≤ θ.range := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp (hAS ha)
    exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
  let e : θ.range ≃* φ.range := (QuotientGroup.quotientKerEquivRange θ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange φ))
  set A₁ : Subgroup θ.range := A.subgroupOf θ.range with hA₁
  set A₂ : Subgroup (E ≃ₗ[K] E) := (A₁.map e.toMonoidHom).map φ.range.subtype with hA₂
  have hA₂le : A₂ ≤ Γ := by
    rw [← d.range]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hA₁el : IsElemAbelian 2 A₁ := hAel.comap θ.range.subtype_injective
  have hA₂el : IsElemAbelian 2 A₂ := (hA₁el.map _).map _
  have hcardE : Nat.card A₂ = Nat.card A := by
    have h2 : Nat.card A₂ = Nat.card A₁ := by
      rw [hA₂, Subgroup.card_map_of_injective φ.range.subtype_injective,
        Subgroup.card_map_of_injective e.injective]
    have h3 : Nat.card A₁ = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAθ).toEquiv
    rw [h2, h3]
  rw [← hcardE]
  exact hcore A₂ hA₂le hA₂el

end ElemBound

section ElemBoundTargets

open CFSG.RankThree.GF2n.Smith81.D6Spin CFSG.RankThree.GF2n.Smith81.E7Model

@[expose] def ElemAbelianBoundE4 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ A : Subgroup (W K ≃ₗ[K] W K), A ≤ EAut0 K → IsElemAbelian 2 A →
      Nat.card A ≤ Nat.card K ^ 15

theorem elemBoundE4_of_core
    (hcore : ElemAbelianBoundE4) (hFE1 : D6Spin.Smith24E4UniformStatement) :
    ElemBoundE4Statement := by
  intro G _ _ M Q Z B IH hc h4 _ n hw A hAS hAel
  have hw16 : Width Q Z 16 := by
    obtain ⟨t, -, h⟩ := h4
    exact h.1
  have hn : n = 16 := width_unique hc.ctx.hyp hw hw16
  subst hn
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h4 K γ M₀ hg
  have hq : 4 ≤ Nat.card K := hg.card ▸ hc.ctx.hyp.q4
  have := elemBound_transport hc.ctx d (Nat.card K ^ 15) (hcore K hq) A hAS hAel
  rw [hg.card] at this
  simpa using this

end ElemBoundTargets

section Lam

open CFSG.RankThree.GF2n.Smith81.D6Spin CFSG.RankThree.GF2n.Smith81.D6X
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.MinuscT
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.Assembly.LowTwoRank


theorem eq_of_indW {K : Type} [Field K] [Finite K] [CharP K 2] {x x' : Gp K}
    (hx : x ∈ LamG K) (hx' : x' ∈ LamG K) {y : W K ≃ₗ[K] W K} (h : IndW x y)
    (h' : IndW x' y) : x = x' := by
  have h1 : IndW (x⁻¹ * x') (y⁻¹ * y) := h.inv.mul h'
  rw [inv_mul_cancel] at h1
  have := eq_one_of_indW_one (mul_mem (inv_mem hx) hx') h1
  exact inv_mul_eq_one.1 this

theorem exists_lam_elemAbelian {K : Type} [Field K] [Finite K] [CharP K 2]
    (A : Subgroup (W K ≃ₗ[K] W K)) (hA : A ≤ EAut0 K) (hel : IsElemAbelian 2 A) :
    ∃ A₀ : Subgroup (Gp K), A₀ ≤ LamG K ∧ IsElemAbelian 2 A₀ ∧ Nat.card A₀ = Nat.card A := by
  let A₀ : Subgroup (Gp K) :=
    { carrier := {x | x ∈ LamG K ∧ ∃ y ∈ A, IndW x y}
      mul_mem' := by
        rintro a b ⟨ha, y, hy, hay⟩ ⟨hb, z, hz, hbz⟩
        exact ⟨mul_mem ha hb, y * z, mul_mem hy hz, hay.mul hbz⟩
      one_mem' := ⟨one_mem _, 1, one_mem _, IndW.one⟩
      inv_mem' := by
        rintro a ⟨ha, y, hy, hay⟩
        exact ⟨inv_mem ha, y⁻¹, inv_mem hy, hay.inv⟩ }
  have hle : A₀ ≤ LamG K := fun x hx => hx.1
  refine ⟨A₀, hle, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨ha, y, hy, hay⟩ := a.2
    obtain ⟨hb, z, hz, hbz⟩ := b.2
    apply Subtype.ext
    have hyz : y * z = z * y := Subtype.ext_iff.1 (hel.1.1.comm ⟨y, hy⟩ ⟨z, hz⟩)
    apply eq_of_indW (mul_mem ha hb) (mul_mem hb ha) (y := y * z) (hay.mul hbz)
    rw [hyz]
    exact hbz.mul hay
  · obtain ⟨hxL, y, hy, hxy⟩ := hx
    have h2 : y ^ 2 = 1 := hel.2 y hy
    rw [pow_two] at h2 ⊢
    have := hxy.mul hxy
    rw [h2] at this
    exact eq_one_of_indW_one (mul_mem hxL hxL) this
  · classical
    let f : A₀ → A := fun x => ⟨Classical.choose x.2.2, (Classical.choose_spec x.2.2).1⟩
    have hf : ∀ x : A₀, IndW (x : Gp K) (f x : W K ≃ₗ[K] W K) := fun x =>
      (Classical.choose_spec x.2.2).2
    have hinj : Function.Injective f := by
      intro x x' h
      apply Subtype.ext
      apply eq_of_indW x.2.1 x'.2.1 (y := (f x : W K ≃ₗ[K] W K)) (hf x)
      rw [h]
      exact hf x'
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨x, hxL, hxy⟩ := (mem_EAut0_iff (K := K)).1 (hA y.2)
      refine ⟨⟨x, hxL, y, y.2, hxy⟩, Subtype.ext ?_⟩
      exact (hf ⟨x, hxL, y, y.2, hxy⟩).unique hxy
    exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

end Lam

section D6Abel

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.E7Model


@[expose] def d6R : List (List ℤ) :=
  [[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
    [0, 0, 1, 1, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 1, 0, 0],
    [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 1, 1, 0, 0], [0, 1, 1, 1, 1, 0, 0], [0, 1, 1, 2, 1, 0, 0],
    [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 1, 1, 0], [0, 1, 0, 1, 1, 1, 0],
    [0, 0, 1, 1, 1, 1, 0], [0, 1, 1, 1, 1, 1, 0], [0, 1, 1, 2, 1, 1, 0], [0, 1, 1, 2, 2, 1, 0],
    [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1, 1], [0, 0, 0, 1, 1, 1, 1],
    [0, 1, 0, 1, 1, 1, 1], [0, 0, 1, 1, 1, 1, 1], [0, 1, 1, 1, 1, 1, 1], [0, 1, 1, 2, 1, 1, 1],
    [0, 1, 1, 2, 2, 1, 1], [0, 1, 1, 2, 2, 2, 1]]

@[expose] def d6rNb : List ℕ :=
  (List.range d6R.length).map fun v => bitsOf d6R.length (adjP d6R [] v)

theorem d6r_nb :
    d6rNb = (List.range d6R.length).map fun v => bitsOf d6R.length (adjP d6R [] v) :=
  rfl

theorem d6r_chk : (pairGraph 0 d6rNb 1 1).bnb (List.range d6R.length) 200
    (bitsOf d6R.length fun _ => true) 15 = true := by
  decide +kernel

theorem d6R_mem (γ : Fin (Tag.rank .E7) → ℤ) :
    ((IsRoot .E7 γ ∧ MinData.toWeight γ ⬝ᵥ theta = 0) ∧ 0 < ht γ) ↔ List.ofFn γ ∈ d6R := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  have hfwd : ∀ k : Fin 126, MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0 →
      0 < ht ((Tag.rootCertificate .E7).root k) →
      List.ofFn ((Tag.rootCertificate .E7).root k) ∈ d6R := by
    decide +kernel
  have hbwd : ∀ k : Fin 126, List.ofFn ((Tag.rootCertificate .E7).root k) ∈ d6R →
      MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0 ∧
        0 < ht ((Tag.rootCertificate .E7).root k) := by
    decide +kernel
  have hall : ∀ l ∈ d6R, ∃ k : Fin 126, List.ofFn ((Tag.rootCertificate .E7).root k) = l := by
    decide +kernel
  constructor
  · rintro ⟨⟨hroot, hperp⟩, hpos⟩
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hroot
    exact hfwd ⟨k, by omega⟩ hperp hpos
  · intro h
    obtain ⟨k, hk⟩ := hall _ h
    have hγ : γ = (Tag.rootCertificate .E7).root k := List.ofFn_injective hk.symm
    subst hγ
    refine ⟨⟨RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega), ?_⟩, ?_⟩
    · exact (hbwd k h).1
    · exact (hbwd k h).2

theorem d6_abelian_card_le (X : Finset (Fin (Tag.rank .E7) → ℤ))
    (hX : ∀ γ ∈ X, γ ∈ Perp ∧ 0 < ht γ)
    (hXX : ∀ γ ∈ X, ∀ δ ∈ X, ¬ IsRoot .E7 (γ + δ)) : X.card ≤ 15 := by
  refine abelian_transfer d6R d6rNb (List.range d6R.length) 15
    (fun γ => ((IsRoot .E7 γ ∧ MinData.toWeight γ ⬝ᵥ theta = 0) ∧ 0 < ht γ)) d6r_nb d6r_chk
    d6R_mem X hX ?_
  intro γ hγ δ hδ h
  have hγP := hX γ hγ
  have hδP := hX δ hδ
  exact hXX γ hγ δ hδ h.1.1

end D6Abel

section ElemCoreE4

open CFSG.RankThree.GF2n.Smith81.D6Spin CFSG.RankThree.GF2n.Smith81.D6X
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.MinuscT
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.Assembly.LowTwoRank

open CFSG.Blueprint.Chevalley


@[expose] def LeadRootsBoundStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (A : Subgroup (Gp K)), A ≤ ULG K →
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      ∃ X : Finset (Fin (Tag.rank .E7) → ℤ),
        (∀ γ ∈ X, γ ∈ Perp ∧ 0 < CFSG.LieType.Steinberg.ht γ) ∧
        (∀ γ ∈ X, ∀ δ ∈ X, ¬ IsRoot .E7 (γ + δ)) ∧ Nat.card A ≤ Nat.card K ^ X.card

theorem elemAbelianBoundE4_of_lead (h : LeadRootsBoundStatement) : ElemAbelianBoundE4 := by
  intro K _ _ _ hq A hA hel
  obtain ⟨A₀, hA₀L, hA₀el, hcard⟩ := exists_lam_elemAbelian A hA hel
  obtain ⟨g, hg, hconj⟩ := lam_conj_into_ULG A₀ hA₀L hA₀el.isPGroup
  have hA₁el : IsElemAbelian 2 (A₀.map (MulAut.conj g).toMonoidHom) := hA₀el.map _
  have hcard1 : Nat.card (A₀.map (MulAut.conj g).toMonoidHom) = Nat.card A₀ :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨X, hXP, hXX, hX⟩ := h K (A₀.map (MulAut.conj g).toMonoidHom) hconj
    fun a ha b hb => Subtype.ext_iff.1 (hA₁el.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h15 := d6_abelian_card_le X hXP hXX
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  calc Nat.card A = Nat.card A₀ := hcard.symm
    _ = Nat.card (A₀.map (MulAut.conj g).toMonoidHom) := hcard1.symm
    _ ≤ Nat.card K ^ X.card := hX
    _ ≤ Nat.card K ^ 15 := Nat.pow_le_pow_right hq1 h15

end ElemCoreE4

end CFSG.RankThree.GF2n.Smith81.SK
