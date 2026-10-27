module

public import CFSG.GroupTheory.SteinbergBSSolvableSignalizer
public import CFSG.SignalizerFunctorTheorem.SolvableTheorem

public section

namespace CFSG.RankThree.Theta

open Subgroup CFSG.Open CFSG.GroupTheory.SteinbergBS

universe u v

theorem card_comap_mulEquiv {G₀ G : Type*} [Group G₀] [Group G] (e : G₀ ≃* G)
    (K : Subgroup G) : Nat.card (K.comap e.toMonoidHom) = Nat.card K := by
  have h := comap_equiv_eq_map_symm e K
  change K.comap e.toMonoidHom = K.map e.symm.toMonoidHom at h
  rw [h, card_map_of_injective e.symm.injective]

theorem glauberman_solvable_signalizer_functor_univ {G : Type u} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (A : Subgroup G) (hA : IsMulCommutative A) (hexp : ∀ a ∈ A, a ^ p = 1)
    (hrank : p ^ 3 ∣ Nat.card A) (θ : G → Subgroup G) (hθ : IsSolvableSignalizerFunctor p A θ) :
    let W : Subgroup G := ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), θ a
    Nat.Coprime p (Nat.card W) ∧ Group.IsSolvable W ∧
      ∀ a ∈ A, a ≠ 1 → θ a = W ⊓ centralizer {a} := by
  intro W
  let e : Shrink.{0} G ≃* G := Shrink.mulEquiv
  let A₀ : Subgroup (Shrink.{0} G) := A.comap e.toMonoidHom
  let θ₀ : Shrink.{0} G → Subgroup (Shrink.{0} G) := fun x => (θ (e x)).comap e.toMonoidHom
  have hmem : ∀ (K : Subgroup G) (y : Shrink.{0} G), y ∈ K.comap e.toMonoidHom ↔ e y ∈ K :=
    fun _ _ => Iff.rfl
  have hne : ∀ x : Shrink.{0} G, x ≠ 1 → e x ≠ 1 := fun x hx h => hx (e.map_eq_one_iff.1 h)
  have hcomm : ∀ x y : Shrink.{0} G, e x * e y = e y * e x → x * y = y * x := fun x y h =>
    e.injective (by rw [map_mul, map_mul, h])
  have hcen : ∀ x y : Shrink.{0} G, y ∈ centralizer ({x} : Set _) ↔
      e y ∈ centralizer ({e x} : Set G) := fun x y => by
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    exact ⟨fun h => by rw [← map_mul, ← map_mul, h], hcomm y x⟩
  have hA₀ : IsMulCommutative A₀ := ⟨⟨fun x y => Subtype.ext (hcomm _ _
    (congrArg Subtype.val (mul_comm' (⟨e x, x.2⟩ : A) ⟨e y, y.2⟩)))⟩⟩
  have hexp₀ : ∀ a ∈ A₀, a ^ p = 1 := fun a ha =>
    e.injective (by rw [map_pow, map_one]; exact hexp _ ha)
  have hrank₀ : p ^ 3 ∣ Nat.card A₀ := by
    rw [show Nat.card A₀ = Nat.card A from card_comap_mulEquiv e A]
    exact hrank
  have hθ₀ : IsSolvableSignalizerFunctor p A₀ θ₀ :=
    { le_centralizer := fun a ha ha1 y hy => (hcen a y).2
        (hθ.le_centralizer (e a) ((hmem _ _).1 ha) (hne a ha1) ((hmem _ _).1 hy))
      coprime := fun a ha ha1 => by
        change Nat.Coprime p (Nat.card ((θ (e a)).comap e.toMonoidHom))
        rw [card_comap_mulEquiv e]
        exact hθ.coprime (e a) ((hmem _ _).1 ha) (hne a ha1)
      invariant := fun a ha ha1 x hx => by
        ext y
        rw [mem_map_equiv, hmem, hmem, MulAut.conj_symm_apply]
        have hinv := hθ.invariant (e a) ((hmem _ _).1 ha) (hne a ha1) (e x) ((hmem _ _).1 hx)
        have h := congrArg (fun K : Subgroup G => e y ∈ K) hinv
        simp only [eq_iff_iff] at h
        rw [← h, mem_map_equiv, MulAut.conj_symm_apply, map_mul, map_mul, map_inv]
      balance := fun a ha ha1 b hb hb1 y hy =>
        hθ.balance (e a) ((hmem _ _).1 ha) (hne a ha1) (e b) ((hmem _ _).1 hb) (hne b hb1)
          ⟨(hmem _ _).1 hy.1, (hcen b y).1 hy.2⟩
      solvable := fun a ha ha1 => by
        have := hθ.solvable (e a) ((hmem _ _).1 ha) (hne a ha1)
        exact Group.isSolvable_of_isSolvable_injective
          (f := e.toMonoidHom.subgroupComap (θ (e a))) (fun x y h => Subtype.ext (e.injective
            (congrArg Subtype.val h))) }
  obtain ⟨hcop, hsolv, hcent⟩ := SignalizerFunctorTheorem.glauberman_solvable_signalizer_functor
    (Shrink.{0} G) p hp A₀ hA₀ hexp₀ hrank₀ θ₀ hθ₀
  set W₀ : Subgroup (Shrink.{0} G) := ⨆ (a : Shrink.{0} G) (_ : a ∈ A₀) (_ : a ≠ 1), θ₀ a
    with hW₀
  have hsymm : ∀ a : G, a ∈ A → a ≠ 1 → e.symm a ∈ A₀ ∧ e.symm a ≠ 1 := fun a ha ha1 =>
    ⟨(hmem _ _).2 (by rwa [MulEquiv.apply_symm_apply]),
      fun h => ha1 (by rw [← MulEquiv.apply_symm_apply e a, h, map_one])⟩
  have hWW : ∀ y : Shrink.{0} G, y ∈ W₀ ↔ e y ∈ W := by
    intro y
    constructor
    · intro hy
      have hle : W₀ ≤ W.comap e.toMonoidHom := by
        refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
        exact comap_mono (le_iSup_of_le (e a) (le_iSup_of_le ha (le_iSup_of_le (hne a ha1)
          le_rfl)))
      exact hle hy
    · intro hy
      have hle : W ≤ W₀.map e.toMonoidHom := by
        refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
        intro z hz
        refine ⟨e.symm z, ?_, by simp⟩
        have hθle : θ₀ (e.symm a) ≤ W₀ := le_iSup_of_le (e.symm a)
          (le_iSup_of_le (hsymm a ha ha1).1 (le_iSup_of_le (hsymm a ha ha1).2 le_rfl))
        refine hθle ?_
        change e (e.symm z) ∈ θ (e (e.symm a))
        rwa [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      obtain ⟨z, hz, hzy⟩ := hle hy
      rwa [show z = y from e.injective hzy] at hz
  have hWiso : W₀ ≃* W :=
    { toFun := fun z => ⟨e z, (hWW z).1 z.2⟩
      invFun := fun w => ⟨e.symm w, (hWW _).2 (by rw [MulEquiv.apply_symm_apply]; exact w.2)⟩
      left_inv := fun z => Subtype.ext (e.symm_apply_apply z)
      right_inv := fun w => Subtype.ext (e.apply_symm_apply w)
      map_mul' := fun z w => Subtype.ext (by simp) }
  refine ⟨?_, ?_, fun a ha ha1 => ?_⟩
  · rw [← Nat.card_congr hWiso.toEquiv]
    exact hcop
  · have := hsolv
    exact Group.isSolvable_of_isSolvable_injective (f := hWiso.symm.toMonoidHom)
      hWiso.symm.injective
  · obtain ⟨ha₀, ha₀1⟩ := hsymm a ha ha1
    have h := hcent _ ha₀ ha₀1
    ext y
    have hy := congrArg (fun K => e.symm y ∈ K) h
    simp only [eq_iff_iff] at hy
    rw [mem_inf, hWW, hcen, hmem, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hy
    rw [hy, mem_inf]

theorem solvable_signalizer_datum_complete {p : ℕ} {A : Type u} [Group A] {X : Type v} [Group X]
    {α : A →* MulAut X} {θ : A → Subgroup X} (hd : IsSolvableSignalizerDatum p A X α θ)
    (h3 : p ^ 3 ≤ Nat.card A) :
    let Θ : Subgroup X := ⨆ (a : A) (_ : a ≠ 1), θ a
    (∀ b : A, Θ.map (α b).toMonoidHom = Θ) ∧ Group.IsSolvable Θ ∧ Nat.Coprime p (Nat.card Θ) ∧
      ∀ a : A, a ≠ 1 → ∀ g ∈ Θ, α a g = g → g ∈ θ a := by
  intro Θ
  have hp := hd.prime
  have : Fact p.Prime := ⟨hp⟩
  have := hd.finite_actor
  have := hd.finite
  have hAel := hd.elementary
  have hinvΘ : ∀ b : A, Θ.map (α b).toMonoidHom = Θ := fun b => by
    simp only [Θ, Subgroup.map_iSup]
    exact iSup_congr fun a => iSup_congr fun ha => hd.invariant a ha b
  let S := X ⋊[α] A
  have : Finite S := Finite.of_equiv (X × A)
    { toFun := fun q => ⟨q.1, q.2⟩
      invFun := fun s => (s.left, s.right)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let A' : Subgroup S := (SemidirectProduct.inr : A →* S).range
  let θ' : S → Subgroup S := fun s =>
    (θ (SemidirectProduct.rightHom s)).map (SemidirectProduct.inl : X →* S)
  have hθ'inr : ∀ a : A, θ' (SemidirectProduct.inr a) = (θ a).map SemidirectProduct.inl :=
    fun a => by simp only [θ', SemidirectProduct.rightHom_inr]
  have hA'mem : ∀ s ∈ A', s ≠ 1 → ∃ a : A, a ≠ 1 ∧ s = SemidirectProduct.inr a := by
    rintro _ ⟨a, rfl⟩ hs
    exact ⟨a, fun h => hs (by rw [h, map_one]), rfl⟩
  have hfix : ∀ (a : A) (x : X), α a x = x ↔ (SemidirectProduct.inl x : S) *
      SemidirectProduct.inr a = SemidirectProduct.inr a * SemidirectProduct.inl x := fun a x => by
    rw [← (SemidirectProduct.inl_injective (φ := α)).eq_iff, SemidirectProduct.inl_aut,
      map_inv]
    set u : S := SemidirectProduct.inr a
    set v : S := SemidirectProduct.inl x
    constructor
    · intro h
      calc v * u = u * v * u⁻¹ * u := by rw [h]
        _ = u * v := inv_mul_cancel_right (u * v) u
    · intro h
      calc u * v * u⁻¹ = v * u * u⁻¹ := by rw [h]
        _ = v := mul_inv_cancel_right v u
  have hcommA : ∀ a b : A, a * b = b * a := fun a b => mul_comm' a b
  have hpowA : ∀ a : A, a ^ p = 1 := fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p p A) a
  have hA' : IsMulCommutative A' := ⟨⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact Subtype.ext (by simp only [coe_mul, ← map_mul, hcommA a b])⟩⟩
  have hexp' : ∀ s ∈ A', s ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, hpowA, map_one]
  have hcardA' : Nat.card A' = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective (SemidirectProduct.inr_injective (φ := α))).toEquiv).symm
  have hrank' : p ^ 3 ∣ Nat.card A' := by
    rw [hcardA']
    obtain ⟨k, hk⟩ := (CFSG.IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hk] at h3 ⊢
    exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).1 h3)
  have hθ' : IsSolvableSignalizerFunctor p A' θ' :=
    { le_centralizer := fun s hs hs1 => by
        obtain ⟨a, ha1, rfl⟩ := hA'mem s hs hs1
        rw [hθ'inr]
        rintro _ ⟨x, hx, rfl⟩
        rw [mem_centralizer_singleton_iff]
        exact (hfix a x).1 (hd.le_fixed a ha1 x hx)
      coprime := fun s hs hs1 => by
        obtain ⟨a, ha1, rfl⟩ := hA'mem s hs hs1
        rw [hθ'inr, card_map_of_injective SemidirectProduct.inl_injective]
        exact hd.coprime a ha1
      invariant := fun s hs hs1 t ht => by
        obtain ⟨a, ha1, rfl⟩ := hA'mem s hs hs1
        obtain ⟨b, rfl⟩ := ht
        rw [hθ'inr, map_map]
        have hcomp : (MulAut.conj (SemidirectProduct.inr b : S)).toMonoidHom.comp
            (SemidirectProduct.inl : X →* S) =
            (SemidirectProduct.inl : X →* S).comp (α b).toMonoidHom := MonoidHom.ext fun x => by
          rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
            MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SemidirectProduct.inl_aut, map_inv]
        rw [hcomp, ← map_map, hd.invariant a ha1 b]
      balance := fun s hs hs1 t ht ht1 => by
        obtain ⟨a, ha1, rfl⟩ := hA'mem s hs hs1
        obtain ⟨b, hb1, rfl⟩ := hA'mem t ht ht1
        rw [hθ'inr, hθ'inr]
        rintro _ ⟨⟨x, hx, rfl⟩, hxb⟩
        exact ⟨x, hd.balance a b ha1 hb1 x hx ((hfix b x).2
          (mem_centralizer_singleton_iff.1 hxb)), rfl⟩
      solvable := fun s hs hs1 => by
        obtain ⟨a, ha1, rfl⟩ := hA'mem s hs hs1
        rw [hθ'inr]
        have := hd.solvable a ha1
        let e := (θ a).equivMapOfInjective _ (SemidirectProduct.inl_injective (φ := α))
        exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom)
          e.symm.injective }
  obtain ⟨hcop, hsolv, hcent⟩ :=
    glauberman_solvable_signalizer_functor_univ hp A' hA' hexp' hrank' θ' hθ'
  set W' : Subgroup S := ⨆ (s : S) (_ : s ∈ A') (_ : s ≠ 1), θ' s with hW'
  have hWΘ : W' = Θ.map (SemidirectProduct.inl : X →* S) := by
    apply le_antisymm
    · refine iSup_le fun s => iSup_le fun hs => iSup_le fun hs1 => ?_
      obtain ⟨a, ha1, rfl⟩ := hA'mem s hs hs1
      rw [hθ'inr]
      exact map_mono (le_iSup_of_le a (le_iSup_of_le ha1 le_rfl))
    · simp only [Θ, Subgroup.map_iSup]
      refine iSup_le fun a => iSup_le fun ha1 => ?_
      rw [← hθ'inr]
      exact le_iSup_of_le (SemidirectProduct.inr a) (le_iSup_of_le ⟨a, rfl⟩
        (le_iSup_of_le (fun h => ha1 (SemidirectProduct.inr_injective (h.trans (map_one _).symm)))
          le_rfl))
  let eΘ := Θ.equivMapOfInjective _ (SemidirectProduct.inl_injective (φ := α))
  refine ⟨hinvΘ, ?_, ?_, fun a ha1 g hg hga => ?_⟩
  · have := hsolv
    rw [hWΘ] at this
    exact Group.isSolvable_of_isSolvable_injective (f := eΘ.toMonoidHom) eΘ.injective
  · rw [Nat.card_congr eΘ.toEquiv, ← hWΘ]
    exact hcop
  · have h := hcent (SemidirectProduct.inr a) ⟨a, rfl⟩
      (fun h => ha1 (SemidirectProduct.inr_injective (h.trans (map_one _).symm)))
    have hmem : SemidirectProduct.inl g ∈ W' ⊓ centralizer {SemidirectProduct.inr a} :=
      ⟨hWΘ ▸ mem_map_of_mem _ hg, mem_centralizer_singleton_iff.2 ((hfix a g).1 hga)⟩
    rw [← h, hθ'inr] at hmem
    obtain ⟨x, hx, hxg⟩ := hmem
    rwa [SemidirectProduct.inl_injective hxg] at hx

theorem prime_three_solvable_signalizer_completeness {A : Type*} [Group A] {X : Type*} [Group X]
    {α : A →* MulAut X} {γ : A → Subgroup X} (hd : IsSolvableSignalizerDatum 3 A X α γ)
    (hA : 27 ≤ Nat.card A) :
    let Θ : Subgroup X := ⨆ (a : A) (_ : a ≠ 1), γ a
    (∀ b : A, Θ.map (α b).toMonoidHom = Θ) ∧ Group.IsSolvable Θ ∧ Nat.Coprime 3 (Nat.card Θ) ∧
      ∀ a : A, a ≠ 1 → ∀ g ∈ Θ, α a g = g → g ∈ γ a :=
  solvable_signalizer_datum_complete hd (by norm_num; exact hA)

end CFSG.RankThree.Theta
