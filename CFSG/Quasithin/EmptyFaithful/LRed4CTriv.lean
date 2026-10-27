module

public import CFSG.Quasithin.EmptyFaithful.LRed4Lines
public import CFSG.Quasithin.EmptyFaithful.LRed4Orth
public import CFSG.Quasithin.Background.Module

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth CFSG.QuasithinUnique CFSG.Quasithin.LRed4L

namespace LRed4

@[expose] def nrmLin : ↥(permCore 8) →ₗ[ZMod 2] V8 where
  toFun x := nrm x.1
  map_add' x y := nrm_add x.1 y.1
  map_smul' c x := by
    funext i
    simp [nrm, mul_add]

theorem nrmLin_L8 : p4insporth_L8 ≤ LinearMap.ker nrmLin := by
  rw [p4insporth_L8, Submodule.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  show nrmLin p4insporth_one8 = 0
  funext i
  show nrm (fun _ => 1) i = 0
  simp [nrm, two_add_self]

@[expose] def toVec : p4insporth_V8 →ₗ[ZMod 2] V8 := p4insporth_L8.liftQ nrmLin nrmLin_L8

theorem toVec_mk (x : ↥(permCore 8)) : toVec (Submodule.Quotient.mk x) = nrm x.1 := rfl

theorem toVec_isNE (u : p4insporth_V8) : isNE (toVec u) := by
  induction u using Submodule.Quotient.induction_on with
  | H x =>
    rw [toVec_mk]
    have hx : ∑ i, x.1 i = 0 := x.2
    exact ⟨by simp [nrm, two_add_self], sum_nrm _ hx⟩

theorem toVec_injective : Function.Injective toVec := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  induction u using Submodule.Quotient.induction_on with
  | H x =>
    rw [toVec_mk] at hu
    have h0 : ∀ i, x.1 i = x.1 0 := by
      intro i
      have := congrFun hu i
      simp only [nrm, Pi.zero_apply] at this
      have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact key _ _ this
    have hx : ∑ i, x.1 i = 0 := x.2
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (x.1 0) with h | h
    · have : x = 0 := Subtype.ext (funext fun i => by rw [h0 i, h]; rfl)
      rw [this]; exact Submodule.Quotient.mk_zero _
    · have : x = p4insporth_one8 := Subtype.ext (funext fun i => by rw [h0 i, h]; rfl)
      rw [this]
      exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span rfl)

theorem toVec_surj {y : V8} (hy : isNE y) : ∃ u, toVec u = y := by
  refine ⟨Submodule.Quotient.mk ⟨y, hy.2⟩, ?_⟩
  rw [toVec_mk]
  exact nrm_of_zero y hy.1

theorem toVec_perm (σ : Equiv.Perm (Fin 8)) (u : p4insporth_V8) :
    toVec (p4insporth_perm8Hom σ u) = act σ (toVec u) := by
  induction u using Submodule.Quotient.induction_on with
  | H x =>
    rw [p4insporth_perm8Hom_mk, toVec_mk, toVec_mk]
    show nrm (pv σ x.1) = nrm (pv σ (nrm x.1))
    rw [nrm_pv_nrm]

theorem hom_trivial_of_odd {G A : Type} [Group G] [Finite G] [Group A] {R S' : Subgroup G}
    (hle : S' ≤ R) (hodd : ¬ 2 ∣ S'.index) (χ : ↥R →* A)
    (hχ : ∀ s : ↥R, (s : G) ∈ S' → χ s = 1) (hcard : Nat.card ↥χ.range ≤ 2) :
    ∀ s, χ s = 1 := by
  have h1 : S'.subgroupOf R ≤ χ.ker := fun s hs => (MonoidHom.mem_ker).2 (hχ s hs)
  have h2 : χ.ker.index ∣ S'.relIndex R := Subgroup.index_dvd_of_le h1
  have h3 : S'.relIndex R ∣ S'.index := Dvd.intro _ (Subgroup.relIndex_mul_index hle)
  have h4 : χ.ker.index ∣ S'.index := h2.trans h3
  have h5 : χ.ker.index ≤ 2 := by rw [Subgroup.index_ker]; exact hcard
  have h6 : 0 < χ.ker.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have h7 : χ.ker.index = 1 := by
    interval_cases h : χ.ker.index
    · rfl
    · exact absurd (h ▸ h4) hodd
  have h8 : χ.ker = ⊤ := Subgroup.index_eq_one.1 h7
  intro s
  have : s ∈ χ.ker := by rw [h8]; trivial
  exact (MonoidHom.mem_ker).1 this

theorem exists_fixed_vector {V : Type} [CommGroup V] [Finite V] {S : Subgroup (MulAut V)}
    (hS : IsPGroup 2 S) {V₂ : Subgroup V} (hV₂ : Nat.card ↥V₂ = 4)
    (hSV₂ : ∀ s ∈ S, ∀ v ∈ V₂, s v ∈ V₂) :
    ∃ v ∈ V₂, v ≠ 1 ∧ ∀ s ∈ S, s v = v := by
  classical
  let α : Type := {x : ↥V₂ // x ≠ 1}
  let f : ↥S → α → α := fun s x =>
    ⟨⟨(s : MulAut V) x.1.1, hSV₂ s s.2 x.1.1 x.1.2⟩, fun h => x.2 (by
      have h1 : (s : MulAut V) x.1.1 = 1 := congrArg Subtype.val h
      have h2 : x.1.1 = 1 := by
        have := (s : MulAut V).injective (h1.trans (map_one (s : MulAut V)).symm)
        exact this
      exact Subtype.ext h2)⟩
  let _ : MulAction ↥S α :=
    { smul := f
      one_smul := fun x => Subtype.ext (Subtype.ext rfl)
      mul_smul := fun s t x => Subtype.ext (Subtype.ext rfl) }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := IsPGroup.card_modEq_card_fixedPoints hS α
  have hα : Nat.card α = 3 := by
    have h1 : Nat.card (Option α) = Nat.card ↥V₂ :=
      Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥V₂))
    have h2 : Nat.card (Option α) = Nat.card α + 1 := by
      have := Fintype.ofFinite α
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]
    omega
  have hpos : 0 < Nat.card ↑(MulAction.fixedPoints ↥S α) := by
    rw [hα] at hmod
    have : Nat.card ↑(MulAction.fixedPoints ↥S α) % 2 = 1 := by
      have := hmod.symm
      unfold Nat.ModEq at this
      omega
    omega
  have : Nonempty ↑(MulAction.fixedPoints ↥S α) := (Nat.card_pos_iff.1 hpos).1
  obtain ⟨⟨p, hp⟩⟩ := this
  refine ⟨p.1.1, p.1.2, fun h => p.2 (Subtype.ext h), fun s hs => ?_⟩
  have := (MulAction.mem_fixedPoints.1 hp) ⟨s, hs⟩
  exact congrArg (fun q : α => q.1.1) this

theorem line_relation {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {V₂ : Subgroup V} (hV₂ : Nat.card ↥V₂ = 4) {y : MulAut V}
    (hyV₂ : ∀ v ∈ V₂, y v ∈ V₂) (hyfix : ∀ v ∈ V₂, y v = v → v = 1) {v : V} (hv : v ∈ V₂)
    (hv1 : v ≠ 1) : y v ≠ v ∧ v * y v * y (y v) = 1 := by
  classical
  have hyne : y v ≠ v := fun h => hv1 (hyfix v hv h)
  have hy1 : y v ≠ 1 := fun h => hv1 (y.injective (h.trans (map_one y).symm))
  have hyv : y v ∈ V₂ := hyV₂ v hv
  have hvyv1 : v * y v ≠ 1 := by
    intro h
    apply hyne
    have : y v = v⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV v)
  have hvyvm : v * y v ∈ V₂ := V₂.mul_mem hv hyv
  have hmem : ∀ x ∈ V₂, x = 1 ∨ x = v ∨ x = y v ∨ x = v * y v := by
    let F : Finset V := {1, v, y v, v * y v}
    have hv1' : (1 : V) ≠ v := fun h => hv1 h.symm
    have hy1' : (1 : V) ≠ y v := fun h => hy1 h.symm
    have hvm : (1 : V) ≠ v * y v := fun h => hvyv1 h.symm
    have hnv : v ≠ y v := fun h => hyne h.symm
    have hnm : v ≠ v * y v := fun h =>
      hy1 (mul_left_cancel (a := v) (b := 1) (c := y v) (by rw [mul_one]; exact h)).symm
    have hnm' : y v ≠ v * y v := fun h =>
      hv1 (mul_right_cancel (a := 1) (b := y v) (c := v) (by rw [one_mul]; exact h)).symm
    have hF : F.card = 4 := by
      simp only [F]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simp [hnm']
      · simp [hnv, hnm]
      · simp [hv1', hy1', hvm]
    have hsub : (F : Set V) ⊆ (V₂ : Set V) := by
      intro x hx
      simp only [F, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact V₂.one_mem
      · exact hv
      · exact hyv
      · exact hvyvm
    have hcard : (V₂ : Set V).ncard ≤ (F : Set V).ncard := by
      rw [Set.ncard_coe_finset, hF, ← Nat.card_coe_set_eq]
      exact hV₂.le
    have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
    intro x hx
    have : x ∈ (F : Set V) := by rw [heq]; exact hx
    simpa [F] using this
  refine ⟨hyne, ?_⟩
  have hyy : y (y v) ∈ V₂ := hyV₂ _ hyv
  have hyy1 : y (y v) ≠ 1 := fun h => hy1 (y.injective (h.trans (map_one y).symm))
  have hyy2 : y (y v) ≠ y v := fun h => hyne (y.injective h)
  have hyy3 : y (y v) ≠ v := by
    intro h
    have hfix : y (v * y v) = v * y v := by rw [map_mul, h, mul_comm]
    exact hvyv1 (hyfix _ hvyvm hfix)
  rcases hmem _ hyy with h | h | h | h
  · exact absurd h hyy1
  · exact absurd h hyy3
  · exact absurd h hyy2
  · rw [h, ← pow_two]
    exact hV _

section Psi

variable {V : Type} [CommGroup V]

theorem exists_psiZ {X : Subgroup (MulAut V)} {Z : Subgroup V} (h : SymmetricNatural X ⊤ Z 8) :
    ∃ (π : Equiv.Perm (Fin 8) →* ↥X) (φ : V →* Multiplicative V8),
      Function.Surjective π ∧ (∀ u, φ u = 1 ↔ u ∈ Z) ∧ (∀ u, isNE (Multiplicative.toAdd (φ u))) ∧
      (∀ y, isNE y → ∃ u, Multiplicative.toAdd (φ u) = y) ∧
      (∀ σ u, φ (((π σ : ↥X) : MulAut V) u) =
        Multiplicative.ofAdd (act σ (Multiplicative.toAdd (φ u)))) ∧
      (∀ x : ↥X, ∀ z ∈ Z, (x : MulAut V) z ∈ Z) := by
  obtain ⟨π, hπs, -, -, -, hZinv, -, -, β, hβs, hβk, hβe⟩ := h
  let Ψ : V →* Multiplicative p4insporth_V8 :=
    thetaEquiv.toMonoidHom.comp
      (β.comp (Subgroup.topEquiv.symm : V ≃* ↥(⊤ : Subgroup V)).toMonoidHom)
  have hΨ : ∀ w : V, Ψ w = thetaEquiv (β ⟨w, trivial⟩) := fun w => rfl
  have hΨs : Function.Surjective Ψ := by
    intro d
    obtain ⟨m, hm⟩ := hβs (thetaEquiv.symm d)
    refine ⟨m.1, ?_⟩
    rw [hΨ]
    have : (⟨m.1, trivial⟩ : ↥(⊤ : Subgroup V)) = m := Subtype.ext rfl
    rw [this, hm, MulEquiv.apply_symm_apply]
  let φ : V →* Multiplicative V8 :=
    (AddMonoidHom.toMultiplicative (toVec : p4insporth_V8 →ₗ[ZMod 2] V8).toAddMonoidHom).comp Ψ
  have hφ : ∀ u, Multiplicative.toAdd (φ u) = toVec (Multiplicative.toAdd (Ψ u)) := fun u => rfl
  refine ⟨π, φ, hπs, ?_, fun u => ?_, ?_, ?_, hZinv⟩
  · intro u
    have e1 : φ u = 1 ↔ Ψ u = 1 := by
      constructor
      · intro h
        have h1 : toVec (Multiplicative.toAdd (Ψ u)) = 0 := by
          rw [← hφ]; exact congrArg Multiplicative.toAdd h
        have h2 : Multiplicative.toAdd (Ψ u) = 0 :=
          toVec_injective (by rw [h1, map_zero])
        exact Multiplicative.toAdd.injective h2
      · intro h
        show (AddMonoidHom.toMultiplicative
          (toVec : p4insporth_V8 →ₗ[ZMod 2] V8).toAddMonoidHom) (Ψ u) = 1
        rw [h, map_one]
    rw [e1, hΨ, MulEquiv.map_eq_one_iff]
    exact hβk ⟨u, trivial⟩
  · rw [hφ]; exact toVec_isNE _
  · intro y hy
    obtain ⟨d, hd⟩ := toVec_surj hy
    obtain ⟨u, hu⟩ := hΨs (Multiplicative.ofAdd d)
    exact ⟨u, by rw [hφ, hu, toAdd_ofAdd, hd]⟩
  · intro σ u
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, trivial⟩)
    have hb : β ⟨((π σ : ↥X) : MulAut V) u, trivial⟩ =
        (FFModel.symDn_isActionModel 8).modAct σ (β ⟨u, trivial⟩) := by
      have := hβe σ ⟨u, trivial⟩ m trivial (by
        exact (FFModel.symDn_isActionModel 8).sec_inv σ m m.2) hm.symm
      rw [this, ← hm]
      rfl
    have h1 : Ψ (((π σ : ↥X) : MulAut V) u) =
        Multiplicative.ofAdd (p4insporth_perm8Hom σ (Multiplicative.toAdd (Ψ u))) := by
      rw [hΨ, hΨ, hb]
      exact thetaEquiv_modAct σ _
    have h2 : toVec (Multiplicative.toAdd (Ψ (((π σ : ↥X) : MulAut V) u))) =
        act σ (toVec (Multiplicative.toAdd (Ψ u))) := by
      rw [h1, toAdd_ofAdd, toVec_perm]
    exact congrArg Multiplicative.ofAdd h2

end Psi

section Orbit

abbrev NEV : Type := {x : V8 // isNE x}

instance : MulAction (Equiv.Perm (Fin 8)) NEV where
  smul σ x := ⟨act σ x.1, isNE_act σ x.2.2⟩
  one_smul x := Subtype.ext (act_one x.1 x.2.1)
  mul_smul σ τ x := Subtype.ext (act_mul σ τ x.1)

theorem card_NEV : Nat.card NEV = 64 := by
  rw [Nat.card_eq_fintype_card]
  exact (by decide +kernel : Fintype.card {x : V8 // isNE x} = 64)

theorem ns_trans {x : V8} (hx : x ∈ NS) : ∃ σ : Equiv.Perm (Fin 8), act σ nsRoot = x := by
  obtain ⟨σ, -, hσ⟩ := bfsL_sound gensAll (fun _ => True) trivial (fun _ _ _ _ => trivial) nsRoot
    (by decide) 13 x (ns_bfs x hx)
  exact ⟨σ, hσ⟩

theorem index_stab_NS (x : NEV) (hx : qP8 x.1 = 1) :
    (MulAction.stabilizer (Equiv.Perm (Fin 8)) x).index = 28 := by
  rw [MulAction.index_stabilizer]
  have horb : MulAction.orbit (Equiv.Perm (Fin 8)) x = {z : NEV | qP8 z.1 = 1} := by
    ext z
    constructor
    · rintro ⟨σ, rfl⟩
      show qP8 (act σ x.1) = 1
      rw [qP8_act σ x.2.2, hx]
    · intro hz
      have hz' : z.1 ∈ NS := mem_NS.2 ⟨z.2, hz⟩
      have hx' : x.1 ∈ NS := mem_NS.2 ⟨x.2, hx⟩
      obtain ⟨σ₁, hσ₁⟩ := ns_trans hx'
      obtain ⟨σ₂, hσ₂⟩ := ns_trans hz'
      refine ⟨σ₂ * σ₁⁻¹, Subtype.ext ?_⟩
      show act (σ₂ * σ₁⁻¹) x.1 = z.1
      rw [act_mul, ← hσ₁, act_inv_act σ₁ nsRoot (by decide), hσ₂]
  rw [horb]
  have himg : Subtype.val '' {z : NEV | qP8 z.1 = 1} = (NS : Set V8) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mem_NS.2 ⟨z.2, hz⟩
    · intro hw
      have := mem_NS.1 hw
      exact ⟨⟨w, this.1⟩, this.2, rfl⟩
  rw [← Set.ncard_image_of_injective _ (Subtype.val_injective (p := isNE)), himg,
    Set.ncard_coe_finset, card_NS]

end Orbit

theorem three_le_card {G : Type} [Finite G] {a b c : G} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ Nat.card G := by
  have hinj : Function.Injective (![a, b, c] : Fin 3 → G) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
  calc 3 = Nat.card (Fin 3) := by simp
    _ ≤ Nat.card G := Nat.card_le_card_of_injective _ hinj

section Main

theorem ctrivial {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X S : Subgroup (MulAut V)} {Z V₂ : Subgroup V} {y : MulAut V}
    (hS : IsSylowTwoOf S X) (hcomm : commV ⁅X, X⁆ = ⊤)
    (hZ : Z ≤ fixV ⁅X, X⁆) (hZ2 : Nat.card ↥Z ≤ 2) (hsym : SymmetricNatural X ⊤ Z 8)
    (hV₂ : Nat.card ↥V₂ = 4) (hSV₂ : ∀ s ∈ S, ∀ v ∈ V₂, s v ∈ V₂)
    (hy : y ∈ ⁅X, X⁆) (hyV₂ : ∀ v ∈ V₂, y v ∈ V₂) (hyfix : ∀ v ∈ V₂, y v = v → v = 1) :
    Z = ⊥ := by
  classical
  obtain ⟨π, φ, hπs, hφZ, hφNE, hφsurj, hφeq, hZinv⟩ := exists_psiZ hsym
  let ρ : Equiv.Perm (Fin 8) →* MulAut V := X.subtype.comp π
  have hρ : ∀ σ, ρ σ = ((π σ : ↥X) : MulAut V) := fun σ => rfl
  have hKX : ⁅X, X⁆ ≤ X := Subgroup.commutator_le.2 fun a ha b hb =>
    X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
  have hZfix : ∀ (σ : Equiv.Perm (Fin 8)), ∀ z ∈ Z, ρ σ z = z := by
    intro σ z hz
    by_cases hz1 : z = 1
    · rw [hz1, map_one]
    · have hmem : ρ σ z ∈ Z := hZinv (π σ) z hz
      have hne : ρ σ z ≠ 1 := fun h => hz1 ((ρ σ).injective (h.trans (map_one _).symm))
      by_contra hne'
      have h3 := three_le_card (G := ↥Z) (a := ⟨1, Z.one_mem⟩) (b := ⟨z, hz⟩) (c := ⟨ρ σ z, hmem⟩)
        (fun h => hz1 (congrArg Subtype.val h).symm) (fun h => hne (congrArg Subtype.val h).symm)
        (fun h => hne' (congrArg Subtype.val h).symm)
      omega
  have hKy : ∀ z ∈ Z, y z = z := fun z hz => hZ hz y hy
  have hV₂Z : ∀ z ∈ V₂, z ∈ Z → z = 1 := fun z hz hzZ => hyfix z hz (hKy z hzZ)
  obtain ⟨v, hv₂, hv1, hvS⟩ := exists_fixed_vector hS.2.1 hV₂ hSV₂
  have hvZ : φ v ≠ 1 := fun h => hv1 (hV₂Z v hv₂ ((hφZ v).1 h))
  set a : V8 := Multiplicative.toAdd (φ v) with ha
  have haNE : isNE a := hφNE v
  have ha0 : a ≠ 0 := fun h => hvZ (Multiplicative.toAdd.injective h)
  have hS'idx : ¬ 2 ∣ (S.comap ρ).index := by
    have h1 : S.comap ρ = (S.subgroupOf X).comap π := by
      ext σ
      simp [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hρ]
    rw [h1, Subgroup.index_comap_of_surjective _ hπs]
    exact hS.2.2
  have haS' : ∀ σ ∈ S.comap ρ, act σ a = a := by
    intro σ hσ
    have h1 := hφeq σ v
    have h2 : ((π σ : ↥X) : MulAut V) v = v := hvS _ hσ
    rw [h2] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    rw [toAdd_ofAdd] at h3
    exact h3.symm
  have hqa : qP8 a = 0 := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (qP8 a) with h | h
    · exact h
    · exfalso
      have hidx := index_stab_NS ⟨a, haNE⟩ h
      have hle : S.comap ρ ≤ MulAction.stabilizer (Equiv.Perm (Fin 8)) (⟨a, haNE⟩ : NEV) := by
        intro σ hσ
        rw [MulAction.mem_stabilizer_iff]
        exact Subtype.ext (haS' σ hσ)
      have := Subgroup.index_dvd_of_le hle
      rw [hidx] at this
      exact hS'idx (dvd_trans (by norm_num) this)
  have haSing : a ∈ Sing := mem_Sing.2 ⟨haNE, ha0, hqa⟩
  set R : Subgroup (Equiv.Perm (Fin 8)) :=
    MulAction.stabilizer (Equiv.Perm (Fin 8)) (⟨a, haNE⟩ : NEV) with hR
  have hRa : ∀ σ ∈ R, act σ a = a := fun σ hσ =>
    congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hσ)
  have hS'R : S.comap ρ ≤ R := fun σ hσ => by
    rw [hR, MulAction.mem_stabilizer_iff]
    exact Subtype.ext (haS' σ hσ)
  have hχZ : ∀ σ ∈ R, ρ σ v * v⁻¹ ∈ Z := by
    intro σ hσ
    rw [← hφZ, map_mul, map_inv]
    have h1 := hφeq σ v
    rw [hRa σ hσ] at h1
    rw [show φ (ρ σ v) = φ v from h1.trans (ofAdd_toAdd _)]
    exact mul_inv_cancel _
  let χ : ↥R →* V :=
    { toFun := fun σ => ρ σ.1 v * v⁻¹
      map_one' := by simp
      map_mul' := fun σ τ => by
        have hz := hχZ τ.1 τ.2
        have hfix := hZfix σ.1 _ hz
        have key : ρ σ.1 (ρ τ.1 v) = (ρ τ.1 v * v⁻¹) * ρ σ.1 v := by
          calc ρ σ.1 (ρ τ.1 v) = ρ σ.1 ((ρ τ.1 v * v⁻¹) * v) := by rw [inv_mul_cancel_right]
            _ = ρ σ.1 (ρ τ.1 v * v⁻¹) * ρ σ.1 v := map_mul _ _ _
            _ = _ := by rw [hfix]
        show ρ (σ.1 * τ.1) v * v⁻¹ = (ρ σ.1 v * v⁻¹) * (ρ τ.1 v * v⁻¹)
        rw [map_mul]
        show ρ σ.1 (ρ τ.1 v) * v⁻¹ = _
        rw [key]
        ac_rfl }
  have hχrange : χ.range ≤ Z := by
    rintro _ ⟨σ, rfl⟩
    exact hχZ σ.1 σ.2
  have hχ1 := hom_trivial_of_odd hS'R hS'idx χ
    (fun σ hσ => by
      show ρ σ.1 v * v⁻¹ = 1
      rw [hvS _ hσ, mul_inv_cancel])
    ((Subgroup.card_le_of_le hχrange).trans hZ2)
  have hvR : ∀ σ, act σ a = a → ρ σ v = v := by
    intro σ hσ
    have h := hχ1 ⟨σ, by rw [hR, MulAction.mem_stabilizer_iff]; exact Subtype.ext hσ⟩
    have h' : ρ σ v * v⁻¹ = 1 := h
    exact mul_inv_eq_one.1 h'
  obtain ⟨hyne, hrel⟩ := line_relation hV hV₂ hyV₂ hyfix hv₂ hv1
  obtain ⟨g, hg⟩ := hπs ⟨y, hKX hy⟩
  have hρg : ρ g = y := by
    rw [hρ]
    exact congrArg Subtype.val hg
  have hrel' : v * ρ g v * ρ (g * g) v = 1 := by
    rw [map_mul, hρg]
    exact hrel
  have hφg : φ (ρ g v) = Multiplicative.ofAdd (act g a) := hφeq g v
  have hφgg : φ (ρ (g * g) v) = Multiplicative.ofAdd (act (g * g) a) := hφeq (g * g) v
  have hbS : act g a ∈ Sing := act_mem_Sing g haSing
  have hab : a ≠ act g a := by
    intro h
    apply hyne
    have h1 : y v * v⁻¹ ∈ Z := by
      rw [← hφZ, map_mul, map_inv]
      have : φ (y v) = φ v := by
        rw [← hρg, hφg, ← h]
        exact ofAdd_toAdd _
      rw [this]
      exact mul_inv_cancel _
    have h2 : y v * v⁻¹ ∈ V₂ := V₂.mul_mem (hyV₂ v hv₂) (V₂.inv_mem hv₂)
    exact mul_inv_eq_one.1 (hV₂Z _ h2 h1)
  have hsum : a + act g a ∈ Sing := by
    have h1 := congrArg φ hrel'
    rw [map_mul, map_mul, map_one, hφg, hφgg] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    simp only [toAdd_mul, toAdd_ofAdd, toAdd_one] at h2
    have h3 : a + act g a = act (g * g) a := by
      funext i
      have := congrFun h2 i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      have key : ∀ p q r : ZMod 2, p + q + r = 0 → p + q = r := by decide
      exact key _ _ _ this
    rw [h3]
    exact act_mem_Sing _ haSing
  obtain ⟨τ, hτa, hτb⟩ := trans_pairs haSing hbS hab hsum
  have hinva : act τ⁻¹ a = a0 := by rw [← hτa, act_inv_act τ a0 (by decide)]
  have hinvb : act τ⁻¹ (act g a) = b0 := by rw [← hτb, act_inv_act τ b0 (by decide)]
  have hφρ : ∀ (σ : Equiv.Perm (Fin 8)) (u : V),
      φ (ρ σ u) = Multiplicative.ofAdd (act σ (Multiplicative.toAdd (φ u))) := hφeq
  have e1 : ρ (τ⁻¹ * g * τ) (ρ τ⁻¹ v) = ρ τ⁻¹ (ρ g v) := by
    show (ρ (τ⁻¹ * g * τ) * ρ τ⁻¹) v = (ρ τ⁻¹ * ρ g) v
    rw [← map_mul, ← map_mul]; congr 2; group
  have e2 : ρ (τ⁻¹ * g * τ * (τ⁻¹ * g * τ)) (ρ τ⁻¹ v) = ρ τ⁻¹ (ρ (g * g) v) := by
    show (ρ (τ⁻¹ * g * τ * (τ⁻¹ * g * τ)) * ρ τ⁻¹) v = (ρ τ⁻¹ * ρ (g * g)) v
    rw [← map_mul, ← map_mul]; congr 2; group
  obtain ⟨W, hWinv, hWsurj, hWcard⟩ := core hV ρ φ hφρ (ρ τ⁻¹ v)
    (by rw [hφρ, ← ha, toAdd_ofAdd]; exact hinva)
    (by
      intro σ hσ
      have h1 : act (τ * σ * τ⁻¹) a = a := by
        rw [act_mul, act_mul, hinva, hσ, hτa]
      have h2 := hvR _ h1
      calc ρ σ (ρ τ⁻¹ v) = ρ (τ⁻¹ * (τ * σ * τ⁻¹)) v := by
            show (ρ σ * ρ τ⁻¹) v = _
            rw [← map_mul]; congr 2; group
        _ = ρ τ⁻¹ (ρ (τ * σ * τ⁻¹) v) := by rw [map_mul]; rfl
        _ = ρ τ⁻¹ v := by rw [h2])
    (τ⁻¹ * g * τ)
    (by rw [act_mul, act_mul, hτa, hinvb])
    (by rw [e1, e2, ← map_mul, ← map_mul, hrel', map_one])
  have hfsurj : Function.Surjective (fun x : ↥W => (⟨Multiplicative.toAdd (φ x.1), hφNE x.1⟩ : NEV)) := by
    rintro ⟨y', hy'⟩
    obtain ⟨x, hxW, hx⟩ := hWsurj y' hy'
    exact ⟨⟨x, hxW⟩, Subtype.ext hx⟩
  have hfbij : Function.Bijective (fun x : ↥W => (⟨Multiplicative.toAdd (φ x.1), hφNE x.1⟩ : NEV)) := by
    rw [Nat.bijective_iff_surjective_and_card]
    refine ⟨hfsurj, le_antisymm (hWcard.trans_eq (card_NEV).symm) ?_⟩
    exact Nat.card_le_card_of_surjective _ hfsurj
  have hWZ : ∀ x ∈ W, x ∈ Z → x = 1 := by
    intro x hxW hxZ
    have h1 : φ x = 1 := (hφZ x).2 hxZ
    have h2 := hfbij.1 (a₁ := ⟨x, hxW⟩) (a₂ := ⟨1, W.one_mem⟩) (Subtype.ext (by
      show Multiplicative.toAdd (φ x) = Multiplicative.toAdd (φ 1)
      rw [h1, map_one φ]))
    exact congrArg Subtype.val h2
  have hWX : ∀ x ∈ X, ∀ w ∈ W, x w ∈ W := by
    intro x hx w hw
    obtain ⟨σ, hσ⟩ := hπs ⟨x, hx⟩
    have : ρ σ = x := by rw [hρ]; exact congrArg Subtype.val hσ
    rw [← this]
    exact hWinv σ w hw
  have hcommW : commV ⁅X, X⁆ ≤ W := by
    rw [commV]
    refine (Subgroup.closure_le W).2 ?_
    rintro _ ⟨k, hk, u, rfl⟩
    obtain ⟨w, hwW, hwφ⟩ := hWsurj (Multiplicative.toAdd (φ u)) (hφNE u)
    have hzZ : u * w⁻¹ ∈ Z := by
      rw [← hφZ, map_mul, map_inv, show φ w = φ u from Multiplicative.toAdd.injective hwφ]
      exact mul_inv_cancel _
    have hkz : k (u * w⁻¹) = u * w⁻¹ := hZ hzZ k hk
    have e1 : k u = k (u * w⁻¹) * k w := by
      rw [← map_mul]; congr 1; simp
    rw [e1, hkz]
    have : u * w⁻¹ * k w * u⁻¹ = k w * w⁻¹ := by
      calc u * w⁻¹ * k w * u⁻¹ = k w * w⁻¹ * (u * u⁻¹) := by ac_rfl
        _ = k w * w⁻¹ := by rw [mul_inv_cancel, mul_one]
    rw [this]
    exact W.mul_mem (hWX k (hKX hk) w hwW) (W.inv_mem hwW)
  have hWtop : W = ⊤ := eq_top_iff.2 (hcomm ▸ hcommW)
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  exact hWZ z (by rw [hWtop]; trivial) hz

end Main

end LRed4

end CFSG.Quasithin
