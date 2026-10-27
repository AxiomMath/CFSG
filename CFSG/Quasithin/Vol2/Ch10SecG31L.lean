module

public import CFSG.Quasithin.Vol2.Ch10SecG31K
public import CFSG.Quasithin.Vol2.Ch10SecG31A
public import CFSG.Quasithin.Vol2.Ch10SecG31J

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G31

open Module CFSG.Open CFSG.Quasithin.ASInputs

variable {V : Type} [CommGroup V]

theorem map_mul_map (g h : MulAut V) (X : Subgroup V) :
    (X.map h.toMonoidHom).map g.toMonoidHom = X.map (g * h).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

namespace MulHyp

variable {Gm : Subgroup (MulAut V)} {Δ₀ : Set (Subgroup V)} {s : ℕ}
  {Δ : Fin s → Set (Subgroup V)}

theorem exists_conj (hM : MulHyp Gm Δ₀ Δ) (i j : Fin s) :
    ∃ g ∈ Gm, (g31V (Δ i)).map (g : MulAut V).toMonoidHom = g31V (Δ j) ∧
      (g31G Gm (Δ i)).map (MulAut.conj g).toMonoidHom = g31G Gm (Δ j) := by
  obtain ⟨X, hX⟩ := hM.ne i
  obtain ⟨Y, hY⟩ := hM.ne j
  obtain ⟨g, hg, hgXY⟩ := hM.trans X (hM.mem_of_mem hX) Y (hM.mem_of_mem hY)
  have hA : ∀ X' ∈ Δ i, X'.map g.toMonoidHom ∈ Δ j := by
    intro X' hX'
    obtain ⟨h, hh, rfl⟩ := hM.gtrans i X hX X' hX'
    rw [map_mul_map, show g * h = g * h * g⁻¹ * g by group, ← map_mul_map, hgXY]
    exact hM.ginv j Y hY _ (conj_mem_g31G hM.inv hg hh)
  have hB : ∀ Y' ∈ Δ j, ∃ X' ∈ Δ i, X'.map g.toMonoidHom = Y' := by
    intro Y' hY'
    obtain ⟨h, hh, rfl⟩ := hM.gtrans j Y hY Y' hY'
    refine ⟨X.map (g⁻¹ * h * g).toMonoidHom, hM.ginv i X hX _ ?_, ?_⟩
    · have := conj_mem_g31G hM.inv (Gm.inv_mem hg) hh
      rwa [inv_inv] at this
    · rw [map_mul_map, ← hgXY, map_mul_map, show g * (g⁻¹ * h * g) = h * g by group]
  refine ⟨g, hg, ?_, ?_⟩
  · have e : (g31V (Δ i)).map g.toMonoidHom = ⨆ X ∈ Δ i, X.map g.toMonoidHom := by
      simp_rw [g31V, Subgroup.map_iSup]
    rw [e]
    refine le_antisymm (iSup₂_le fun X hX => le_iSup₂_of_le (X.map g.toMonoidHom) (hA X hX)
      le_rfl) (iSup₂_le fun Y hY => ?_)
    obtain ⟨X, hX, rfl⟩ := hB Y hY
    exact le_iSup₂_of_le X hX le_rfl
  · have e : (g31G Gm (Δ i)).map (MulAut.conj g).toMonoidHom =
        ⨆ X ∈ Δ i, transvGroup Gm (X.map g.toMonoidHom) := by
      simp_rw [g31G, Subgroup.map_iSup, map_conj_transvGroup hg]
    rw [e]
    refine le_antisymm (iSup₂_le fun X hX => le_iSup₂_of_le (X.map g.toMonoidHom) (hA X hX)
      le_rfl) (iSup₂_le fun Y hY => ?_)
    obtain ⟨X, hX, rfl⟩ := hB Y hY
    exact le_iSup₂_of_le X hX le_rfl

variable [Finite V] [Module (ZMod 2) (Additive V)]

theorem linAutHom_mem_closure (hM : MulHyp Gm Δ₀ Δ) {i : Fin s} {g : MulAut V}
    (hg : g ∈ g31G Gm (Δ i)) :
    linAutHom g ∈ Subgroup.closure (gens (vecs (Δ i)) (forms Gm)) :=
  hM.map_g31G_i i ▸ ⟨g, hg, rfl⟩

theorem iSupIndep_g31V (hM : MulHyp Gm Δ₀ Δ) : iSupIndep fun i => g31V (Δ i) := by
  rw [← iSupIndep_map_orderIso_iff (subE (V := V))]
  have h : (subE ∘ fun i => g31V (Δ i)) = fun i => Submodule.span (ZMod 2) (vecs (Δ i)) :=
    funext fun i => subE_g31V hM.exp (hM.card_i i)
  rw [h]
  exact hM.orbHyp.iSupIndep_span

theorem iSupIndep_g31G (hM : MulHyp Gm Δ₀ Δ) : iSupIndep fun i => g31G Gm (Δ i) := by
  rw [iSupIndep_def]
  intro i
  rw [Subgroup.disjoint_def]
  intro g hg hg'
  have h2 : linAutHom g ∈
      ⨆ j, ⨆ (_ : j ≠ i), Subgroup.closure (gens (vecs (Δ j)) (forms Gm)) := by
    have e : (⨆ j, ⨆ (_ : j ≠ i), g31G Gm (Δ j)).map linAutHom =
        ⨆ j, ⨆ (_ : j ≠ i), Subgroup.closure (gens (vecs (Δ j)) (forms Gm)) := by
      rw [Subgroup.map_iSup]
      refine iSup_congr fun j => ?_
      rw [Subgroup.map_iSup]
      exact iSup_congr fun _ => hM.map_g31G_i j
    rw [← e]
    exact ⟨g, hg', rfl⟩
  have := Subgroup.disjoint_def.1 ((iSupIndep_def.1 hM.orbHyp.iSupIndep_closure) i)
    (hM.linAutHom_mem_closure hg) h2
  exact linAutHom_injective (by rw [this, map_one])

theorem commute_g31G (hM : MulHyp Gm Δ₀ Δ) {i j : Fin s} (hij : i ≠ j) {a b : MulAut V}
    (ha : a ∈ g31G Gm (Δ i)) (hb : b ∈ g31G Gm (Δ j)) : a * b = b * a :=
  linAutHom_injective (by
    rw [map_mul, map_mul]
    exact hM.orbHyp.commute_of_ne hij (hM.linAutHom_mem_closure ha)
      (hM.linAutHom_mem_closure hb))

theorem fix_g31G (hM : MulHyp Gm Δ₀ Δ) {i j : Fin s} (hij : i ≠ j) {a : MulAut V}
    (ha : a ∈ g31G Gm (Δ i)) {v : V} (hv : v ∈ g31V (Δ j)) : a v = v :=
  Additive.ofMul.injective (hM.orbHyp.fix_of_ne hij (hM.linAutHom_mem_closure ha)
    ((hM.mem_g31V_iff_i j).1 hv))

theorem inf_fixing_eq_bot (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) :
    g31G Gm (Δ i) ⊓ fixingSubgroup (MulAut V) (g31V (Δ i) : Set V) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  have h2 : linAutHom g = 1 := hM.orbHyp.eq_one_of_fix (hM.linAutHom_mem_closure hg.1)
    fun u hu => by
      have hv : Additive.toMul u ∈ g31V (Δ i) := (hM.mem_g31V_iff_i i).2 hu
      have := (mem_fixingSubgroup_iff (MulAut V)).1 hg.2 _ hv
      rw [linAutHom_apply]
      exact congrArg Additive.ofMul this
  exact linAutHom_injective (by rw [h2, map_one])

theorem autAll (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) (φ : ↥(g31V (Δ i)) ≃* ↥(g31V (Δ i))) :
    ∃ g ∈ g31G Gm (Δ i), ∀ v : ↥(g31V (Δ i)), g (v : V) = ((φ v : ↥(g31V (Δ i))) : V) := by
  have heq : subE (g31V (Δ i)) = Submodule.span (ZMod 2) (vecs (Δ i)) :=
    subE_g31V hM.exp (hM.card_i i)
  obtain ⟨k, hk, hkg⟩ := (hM.orbHyp.core_i i).2.1
    ((LinearEquiv.ofEq _ _ heq).symm.trans ((linEquivOf φ).trans (LinearEquiv.ofEq _ _ heq)))
  rw [← hM.map_g31G_i i] at hk
  obtain ⟨g, hg, rfl⟩ := hk
  refine ⟨g, hg, fun v => Additive.ofMul.injective ?_⟩
  exact hkg ⟨Additive.ofMul (v : V), (hM.mem_g31V_iff_i i).1 v.2⟩

theorem points (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) :
    Δ i = {X | X ≤ g31V (Δ i) ∧ Nat.card X = 2} := by
  ext X
  refine ⟨fun hX => ⟨le_iSup₂ (f := fun Y (_ : Y ∈ Δ i) => Y) X hX, hM.card_i i X hX⟩,
    fun ⟨hXV, hX2⟩ => ?_⟩
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card_two hX2
  have hxv : Additive.ofMul x ∈ Submodule.span (ZMod 2) (vecs (Δ i)) :=
    (hM.mem_g31V_iff_i i).1 (hXV hx)
  have := (hM.orbHyp.core_i i).1 _ hxv (by simpa using hx1)
  rw [eq_zpowers_of_card_two hM.exp hX2 hx hx1]
  exact this.2

omit [Module (ZMod 2) (Additive V)] in
theorem vec_mem (hM : MulHyp Gm Δ₀ Δ) {i : Fin s} {X : Subgroup V} (hX : X ∈ Δ i) {x : V}
    (hx : x ∈ X) (hx1 : x ≠ 1) : Additive.ofMul x ∈ vecs (Δ i) :=
  ⟨hx1, (eq_zpowers_of_card_two hM.exp (hM.card_i i X hX) hx hx1) ▸ hX⟩

theorem card_g31V (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) : Nat.card (g31V (Δ i)) =
    2 ^ finrank (ZMod 2) (Submodule.span (ZMod 2) (vecs (Δ i))) := by
  rw [← natCard_subE, subE_g31V hM.exp (hM.card_i i), natCard_eq_two_pow]

theorem card_formula (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) (d : ℕ)
    (hd : Nat.card (g31V (Δ i)) = 2 ^ d) (X : Subgroup V) (hX : X ∈ Δ i) :
    Nat.card (transvGroup Gm X) = 2 ^ (d - 1) * Nat.card ↥(transvGroup Gm X ⊓
      fixingSubgroup (MulAut V) (g31V (Δ i) : Set V)) := by
  have hbot : transvGroup Gm X ⊓ fixingSubgroup (MulAut V) (g31V (Δ i) : Set V) = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hM.inf_fixing_eq_bot i]
    exact inf_le_inf_right _ (le_iSup₂ (f := fun Y (_ : Y ∈ Δ i) => transvGroup Gm Y) X hX)
  rw [hbot, Subgroup.card_bot, mul_one]
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card_two (hM.card_i i X hX)
  rw [eq_zpowers_of_card_two hM.exp (hM.card_i i X hX) hx hx1, card_transvGroup hM.exp hx1]
  have h1 := (hM.orbHyp.core_i i).2.2 _ (hM.vec_mem hX hx hx1)
  have h2 := hM.card_g31V i
  rw [hd] at h2
  have h3 := Nat.pow_right_injective (le_refl 2) h2
  congr 1
  omega

theorem eight_le (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) : 8 ≤ Nat.card (g31V (Δ i)) := by
  obtain ⟨X, hX⟩ := hM.ne i
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card_two (hM.card_i i X hX)
  have h1 := (hM.orbHyp.core_i i).2.2 _ (hM.vec_mem hX hx hx1)
  have hr := hM.orbHyp.rank _ ((hM.orbHyp.subset i) (hM.vec_mem hX hx hx1))
  rw [hM.card_g31V i]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ finrank (ZMod 2) (Submodule.span (ZMod 2) (vecs (Δ i))) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

end MulHyp

theorem as_G_3_1_O2 : AS_G_3_1_O2 := by
  intro V _ _ hV Gm hO2 Δ₀ _ hcard hinv htrans hrel s hs Δ hdisj hunion hneΔ hGinv hGtrans
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (two_nsmul_eq_zero hV)
  have hM : MulHyp Gm Δ₀ Δ :=
    ⟨hV, hO2, hcard, hinv, htrans, hrel, hdisj, hunion, hneΔ, hGinv, hGtrans⟩
  refine ⟨⟨hM.iSupIndep_g31V, ?_, hM.iSupIndep_g31G, ?_,
    fun i j hij a ha b hb => hM.commute_g31G hij ha hb,
    fun i j hij a ha v hv => hM.fix_g31G hij ha hv, hM.exists_conj⟩,
    ⟨hM.autAll _, hM.points _, ?_, fun d hd X hX => hM.card_formula _ d hd X hX⟩,
    hM.eight_le _⟩
  · rw [← hunion]
    exact (iSup_iUnion Δ fun X => X).symm
  · rw [← hunion]
    exact (iSup_iUnion Δ fun X => transvGroup Gm X).symm
  · rw [hM.inf_fixing_eq_bot]
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
    · rw [Subgroup.mem_bot.1 ha, one_pow]

end CFSG.Quasithin.G31
