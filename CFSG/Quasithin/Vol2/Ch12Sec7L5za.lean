module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5z
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.Quasithin.Vol2.Ch10SecG31L

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G31

open CFSG.Open CFSG.Quasithin.ASInputs
open scoped commutatorElement

noncomputable def gl2EquivSL (d : ℕ) :
    GL (Fin d) (ZMod 2) ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2) :=
  (MulEquiv.ofBijective (Matrix.SpecialLinearGroup.toGL (n := Fin d) (R := ZMod 2))
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => by
      have hdet : Matrix.GeneralLinearGroup.det A = 1 := by
        have : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
        exact this _
      have : A ∈ (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin d) (ZMod 2) →*
          Matrix.GeneralLinearGroup (Fin d) (ZMod 2)).range := by
        rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
        exact hdet
      exact this⟩).symm

variable {W : Type} [CommGroup W] [Finite W]

theorem nonempty_mulAut_equiv (hW : ∀ w : W, w ^ 2 = 1) {d : ℕ} (hd : Nat.card W = 2 ^ d) :
    Nonempty (MulAut W ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b : W => mul_comm a b) hW hd
  exact ⟨(CFSG.SectionRank.Ccomm.elemAutEquivGL e).trans (gl2EquivSL d)⟩

theorem isSimpleGroup_mulAut (hW : ∀ w : W, w ^ 2 = 1) {d : ℕ} (hd : Nat.card W = 2 ^ d)
    (h3 : 3 ≤ d) : IsSimpleGroup (MulAut W) := by
  obtain ⟨f⟩ := nonempty_mulAut_equiv hW hd
  have := CFSG.QuasithinUnique.Bridge.isSimple_sl_zmod2 d h3
  exact f.isSimpleGroup

theorem even_card_sl (d : ℕ) (h3 : 3 ≤ d) :
    2 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) ∧
      2 < Nat.card (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) := by
  have : NeZero d := ⟨by omega⟩
  rw [CFSG.QuasithinUnique.Bridge.card_sl_two_field d (ZMod 2) (Nat.card_zmod 2)]
  have h1 : (⟨1, by omega⟩ : Fin d) ∈ Finset.univ := Finset.mem_univ _
  have h0 : (⟨0, by omega⟩ : Fin d) ∈ Finset.univ := Finset.mem_univ _
  have hd2 : 2 ^ 3 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) h3
  refine ⟨dvd_trans ?_ (Finset.dvd_prod_of_mem _ h1), ?_⟩
  · show 2 ∣ 2 ^ d - 2 ^ 1
    have : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
    omega
  · have hpos : ∀ i ∈ (Finset.univ : Finset (Fin d)), 1 ≤ 2 ^ d - 2 ^ (i : ℕ) := by
      intro i _
      have : 2 ^ (i : ℕ) < 2 ^ d := Nat.pow_lt_pow_right (by norm_num) i.2
      omega
    have hle := Finset.single_le_prod (f := fun i : Fin d => 2 ^ d - 2 ^ (i : ℕ)) hpos h0
    simp only at hle
    omega

theorem nonabelian_mulAut (hW : ∀ w : W, w ^ 2 = 1) {d : ℕ} (hd : Nat.card W = 2 ^ d)
    (h3 : 3 ≤ d) : ∃ a b : MulAut W, a * b ≠ b * a := by
  obtain ⟨f⟩ := nonempty_mulAut_equiv hW hd
  have hs := isSimpleGroup_mulAut hW hd h3
  by_contra hc
  push Not at hc
  let _ : CommGroup (MulAut W) := { (inferInstance : Group (MulAut W)) with mul_comm := hc }
  have hp : (Nat.card (MulAut W)).Prime := IsSimpleGroup.prime_card
  rw [Nat.card_congr f.toEquiv] at hp
  obtain ⟨h2, hgt⟩ := even_card_sl d h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
  omega

section Restrict

variable {V : Type} [CommGroup V]

@[expose] def g31Stab (S : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ v, v ∈ S ↔ g v ∈ S}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb v => (hb v).trans (ha (b v))
  inv_mem' := fun {a} ha v => by
    have h := ha (a⁻¹ v)
    rw [MulAut.apply_inv_self] at h
    exact h.symm

@[expose] def g31Restr (S : Subgroup V) : ↥(g31Stab S) →* MulAut ↥S where
  toFun g :=
    { toFun := fun v => ⟨(g : MulAut V) v, (g.2 v).1 v.2⟩
      invFun := fun v => ⟨(g : MulAut V)⁻¹ v, ((g31Stab S).inv_mem g.2 v).1 v.2⟩
      left_inv := fun v => Subtype.ext (MulAut.inv_apply_self V (g : MulAut V) (v : V))
      right_inv := fun v => Subtype.ext (MulAut.apply_inv_self V (g : MulAut V) (v : V))
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  map_one' := by ext v; rfl
  map_mul' := fun a b => by ext v; rfl

theorem g31Restr_apply (S : Subgroup V) (g : ↥(g31Stab S)) (v : ↥S) :
    ((g31Restr S g v : ↥S) : V) = (g : MulAut V) v := rfl

@[reducible] def setAction (Gm : Subgroup (MulAut V)) : MulAction ↥Gm (Set (Subgroup V)) where
  smul g S := (fun X => X.map (g : MulAut V).toMonoidHom) '' S
  one_smul S := by
    show (fun X => X.map ((1 : ↥Gm) : MulAut V).toMonoidHom) '' S = S
    have h : ∀ X : Subgroup V, X.map ((1 : ↥Gm) : MulAut V).toMonoidHom = X := fun X => by
      ext v
      simp
    simp only [h, Set.image_id']
  mul_smul g h S := by
    show (fun X => X.map ((g * h : ↥Gm) : MulAut V).toMonoidHom) '' S =
      (fun X => X.map (g : MulAut V).toMonoidHom) ''
        ((fun X => X.map (h : MulAut V).toMonoidHom) '' S)
    rw [Set.image_image]
    congr 1
    funext X
    exact (map_map_mulAut X (h : MulAut V) (g : MulAut V)).symm

end Restrict

namespace MulHyp

variable {V : Type} [CommGroup V]
variable {Gm : Subgroup (MulAut V)} {Δ₀ : Set (Subgroup V)} {s : ℕ} {Δ : Fin s → Set (Subgroup V)}

theorem g31G_le_g31G (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) : g31G Gm (Δ i) ≤ g31G Gm Δ₀ :=
  iSup₂_le fun X hX => le_iSup₂_of_le (f := fun Y (_ : Y ∈ Δ₀) => transvGroup Gm Y) X
    (hM.mem_of_mem hX) le_rfl

theorem map_g31V_le (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) {g : MulAut V} (hg : g ∈ g31G Gm Δ₀) :
    (g31V (Δ i)).map g.toMonoidHom ≤ g31V (Δ i) := by
  rw [g31V, Subgroup.map_iSup]
  refine iSup_le fun X => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hX => le_iSup₂_of_le (f := fun Y (_ : Y ∈ Δ i) => Y) (X.map g.toMonoidHom)
    (hM.ginv i X hX g hg) le_rfl

theorem g31G_le_stabSub (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) :
    g31G Gm Δ₀ ≤ g31Stab (g31V (Δ i)) := by
  intro g hg v
  constructor
  · intro hv
    exact hM.map_g31V_le i hg (Subgroup.mem_map_of_mem g.toMonoidHom hv)
  · intro hv
    have h := hM.map_g31V_le i ((g31G Gm Δ₀).inv_mem hg)
      (Subgroup.mem_map_of_mem g⁻¹.toMonoidHom hv)
    simpa using h

@[expose] def resHom (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) :
    ↥(g31G Gm (Δ i)) →* MulAut ↥(g31V (Δ i)) :=
  (g31Restr (g31V (Δ i))).comp
    (Subgroup.inclusion ((hM.g31G_le_g31G i).trans (hM.g31G_le_stabSub i)))

theorem resHom_apply (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) (g : ↥(g31G Gm (Δ i)))
    (v : ↥(g31V (Δ i))) : ((hM.resHom i g v : ↥(g31V (Δ i))) : V) = (g : MulAut V) v := rfl

theorem le_normalizer_g31G (hM : MulHyp Gm Δ₀ Δ) :
    Gm ≤ Subgroup.normalizer (g31G Gm Δ₀ : Set (MulAut V)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => conj_mem_g31G hM.inv hg hk, fun hk => ?_⟩
  have := conj_mem_g31G hM.inv (Gm.inv_mem hg) hk
  simpa [mul_assoc] using this

theorem iSup_g31G (hM : MulHyp Gm Δ₀ Δ) : (⨆ i, g31G Gm (Δ i)) = g31G Gm Δ₀ := by
  rw [← hM.union]
  exact (iSup_iUnion Δ fun X => transvGroup Gm X).symm

theorem g31G_le_normalizer [Finite V] [Module (ZMod 2) (Additive V)] (hM : MulHyp Gm Δ₀ Δ)
    (i : Fin s) : g31G Gm Δ₀ ≤ Subgroup.normalizer (g31G Gm (Δ i) : Set (MulAut V)) := by
  rw [← hM.iSup_g31G]
  refine iSup_le fun j => ?_
  by_cases hij : j = i
  · subst hij
    exact Subgroup.le_normalizer
  · intro a ha
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      fun b hb => (hM.commute_g31G hij ha hb).symm)

variable [Finite V] [Module (ZMod 2) (Additive V)]

theorem resHom_bijective (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) : Function.Bijective (hM.resHom i) := by
  refine ⟨?_, fun φ => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : (g : MulAut V) ∈
        g31G Gm (Δ i) ⊓ fixingSubgroup (MulAut V) (g31V (Δ i) : Set V) := by
      refine ⟨g.2, (mem_fixingSubgroup_iff (MulAut V)).2 fun v hv => ?_⟩
      have := congrArg (fun f : MulAut ↥(g31V (Δ i)) => ((f ⟨v, hv⟩ : ↥(g31V (Δ i))) : V)) hg
      simpa [resHom_apply] using this
    rw [hM.inf_fixing_eq_bot i, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  · obtain ⟨g, hg, hgv⟩ := hM.autAll i φ
    exact ⟨⟨g, hg⟩, MulEquiv.ext fun v => Subtype.ext (hgv v)⟩

noncomputable def equivAut (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) :
    ↥(g31G Gm (Δ i)) ≃* MulAut ↥(g31V (Δ i)) :=
  MulEquiv.ofBijective _ (hM.resHom_bijective i)

theorem exists_card_g31V (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) :
    ∃ d, 3 ≤ d ∧ Nat.card ↥(g31V (Δ i)) = 2 ^ d := by
  refine ⟨Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (vecs (Δ i))), ?_, hM.card_g31V i⟩
  have h8 := hM.eight_le i
  rw [hM.card_g31V i] at h8
  by_contra h
  push Not at h
  have : 2 ^ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (vecs (Δ i))) ≤ 2 ^ 2 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

omit [Finite V] [Module (ZMod 2) (Additive V)] in
theorem exp_g31V (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) : ∀ w : ↥(g31V (Δ i)), w ^ 2 = 1 :=
  fun w => Subtype.ext (by simpa using hM.exp w)

theorem isSimpleGroup (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) : IsSimpleGroup ↥(g31G Gm (Δ i)) := by
  obtain ⟨d, hd3, hd⟩ := hM.exists_card_g31V i
  have := isSimpleGroup_mulAut (hM.exp_g31V i) hd hd3
  exact (hM.equivAut i).isSimpleGroup

theorem nonabelian (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) :
    ∃ a b : ↥(g31G Gm (Δ i)), a * b ≠ b * a := by
  obtain ⟨d, hd3, hd⟩ := hM.exists_card_g31V i
  obtain ⟨a, b, hab⟩ := nonabelian_mulAut (hM.exp_g31V i) hd hd3
  refine ⟨(hM.equivAut i).symm a, (hM.equivAut i).symm b, fun h => hab ?_⟩
  have := congrArg (hM.equivAut i) h
  simpa using this

theorem commutator_top (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) :
    commutator ↥(g31G Gm (Δ i)) = ⊤ := by
  have := hM.isSimpleGroup i
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥(g31G Gm (Δ i))) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hM.nonabelian i
    apply hab
    have hc : ⁅a, b⁆ ∈ commutator ↥(g31G Gm (Δ i)) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · exact h

theorem perfect (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) :
    ⁅g31G Gm (Δ i), g31G Gm (Δ i)⁆ = g31G Gm (Δ i) :=
  Subgroup.isPerfect_iff.mp ⟨hM.commutator_top i⟩

theorem isQuasisimple (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) :
    CFSG.Open.IsQuasisimple ↥(g31G Gm (Δ i)) := by
  have hs := hM.isSimpleGroup i
  have hc : Subgroup.center ↥(g31G Gm (Δ i)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(g31G Gm (Δ i))) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hM.nonabelian i
      have ha : a ∈ Subgroup.center ↥(g31G Gm (Δ i)) := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  exact ⟨hM.commutator_top i,
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup⟩

theorem isComponentOf (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) :
    CFSG.Open.IsComponentOf (g31G Gm (Δ i)) Gm := by
  refine ⟨(hM.g31G_le_g31G i).trans (g31G_le Gm Δ₀), ?_, hM.isQuasisimple i⟩
  exact CFSG.Open.IsSubnormal.step (hM.g31G_le_g31G i)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (hM.g31G_le_g31G i)).mpr
      (hM.g31G_le_normalizer i))
    (CFSG.Open.IsSubnormal.step (g31G_le Gm Δ₀)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (g31G_le Gm Δ₀)).mpr hM.le_normalizer_g31G)
      (CFSG.Open.IsSubnormal.refl Gm))

theorem g31G_injective (hM : MulHyp Gm Δ₀ Δ) : Function.Injective fun i => g31G Gm (Δ i) := by
  intro i j hij
  by_contra hne
  have hd : Disjoint (g31G Gm (Δ i)) (g31G Gm (Δ j)) := hM.iSupIndep_g31G.pairwiseDisjoint hne
  simp only at hij
  rw [hij, disjoint_self] at hd
  obtain ⟨a, b, hab⟩ := hM.nonabelian j
  apply hab
  have ha : (a : MulAut V) = 1 := (Subgroup.eq_bot_iff_forall _).1 hd _ a.2
  have hb : (b : MulAut V) = 1 := (Subgroup.eq_bot_iff_forall _).1 hd _ b.2
  exact Subtype.ext (by simp [ha, hb])

omit [Finite V] [Module (ZMod 2) (Additive V)] in
theorem injective (hM : MulHyp Gm Δ₀ Δ) : Function.Injective Δ := by
  intro i j hij
  by_contra hne
  obtain ⟨X, hX⟩ := hM.ne i
  exact Set.disjoint_left.1 (hM.disj i j hne) hX (hij ▸ hX)

omit [Finite V] [Module (ZMod 2) (Additive V)] in
theorem image_eq (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) {g : MulAut V} (hg : g ∈ Gm) :
    ∃ j, (fun X => X.map g.toMonoidHom) '' Δ i = Δ j := by
  obtain ⟨X, hX⟩ := hM.ne i
  have hXg : X.map g.toMonoidHom ∈ Δ₀ := hM.inv X (hM.mem_of_mem hX) g hg
  rw [← hM.union, Set.mem_iUnion] at hXg
  obtain ⟨j, hj⟩ := hXg
  refine ⟨j, Set.Subset.antisymm ?_ fun Y hY => ?_⟩
  · rintro _ ⟨Y, hY, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hM.gtrans i X hX Y hY
    show (X.map a.toMonoidHom).map g.toMonoidHom ∈ Δ j
    have e : (X.map a.toMonoidHom).map g.toMonoidHom =
        (X.map g.toMonoidHom).map (g * a * g⁻¹).toMonoidHom := by
      rw [map_map_mulAut, map_map_mulAut, inv_mul_cancel_right]
    rw [e]
    exact hM.ginv j _ hj _ (conj_mem_g31G hM.inv hg ha)
  · obtain ⟨b, hb, rfl⟩ := hM.gtrans j _ hj Y hY
    refine ⟨X.map (g⁻¹ * b * g).toMonoidHom, hM.ginv i X hX _ ?_, ?_⟩
    · have := conj_mem_g31G hM.inv (Gm.inv_mem hg) hb
      rwa [inv_inv] at this
    · show (X.map (g⁻¹ * b * g).toMonoidHom).map g.toMonoidHom =
        (X.map g.toMonoidHom).map b.toMonoidHom
      rw [map_map_mulAut, map_map_mulAut]
      congr 2
      group

omit [Finite V] [Module (ZMod 2) (Additive V)] in
theorem odd (hM : MulHyp Gm Δ₀ Δ) {S : Subgroup (MulAut V)}
    (hodd : Odd (S.subgroupOf Gm).index) {i₀ : Fin s} {X₀ : Subgroup V} (h0 : X₀ ∈ Δ i₀)
    (hfix : ∀ g ∈ S, X₀.map (g : MulAut V).toMonoidHom = X₀) : Odd s := by
  let _ := setAction Gm
  have hsmul : ∀ (g : ↥Gm) (A : Set (Subgroup V)),
      g • A = (fun X => X.map (g : MulAut V).toMonoidHom) '' A := fun _ _ => rfl
  have horb : MulAction.orbit ↥Gm (Δ i₀) = Set.range Δ := by
    ext A
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨j, hj⟩ := hM.image_eq i₀ g.2
      exact ⟨j, by show Δ j = g • Δ i₀; rw [hsmul, hj]⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨Y, hY⟩ := hM.ne j
      obtain ⟨g, hg, hgY⟩ := hM.trans X₀ (hM.mem_of_mem h0) Y (hM.mem_of_mem hY)
      obtain ⟨j', hj'⟩ := hM.image_eq i₀ hg
      refine ⟨⟨g, hg⟩, ?_⟩
      show (⟨g, hg⟩ : ↥Gm) • Δ i₀ = Δ j
      rw [hsmul]
      show (fun X => X.map g.toMonoidHom) '' Δ i₀ = Δ j
      rw [hj']
      by_contra hne
      have hjj : j' ≠ j := fun h => hne (h ▸ rfl)
      have hYj' : Y ∈ Δ j' := hj' ▸ ⟨X₀, h0, hgY⟩
      exact Set.disjoint_left.1 (hM.disj j' j hjj) hYj' hY
  have hstab : S.subgroupOf Gm ≤ MulAction.stabilizer ↥Gm (Δ i₀) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff, hsmul]
    obtain ⟨j, hj⟩ := hM.image_eq i₀ g.2
    rw [hj]
    by_contra hne
    have hX : X₀ ∈ Δ j := hj ▸ ⟨X₀, h0, hfix _ (Subgroup.mem_subgroupOf.mp hg)⟩
    have hjj : j ≠ i₀ := fun h => hne (h ▸ rfl)
    exact Set.disjoint_left.1 (hM.disj j i₀ hjj) hX h0
  have hidx := MulAction.index_stabilizer ↥Gm (Δ i₀)
  rw [horb, Set.ncard_range_of_injective hM.injective, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hidx
  have hdvd := Subgroup.index_dvd_of_le hstab
  rw [hidx] at hdvd
  exact Odd.of_dvd_nat hodd hdvd

end MulHyp

end CFSG.Quasithin.G31
