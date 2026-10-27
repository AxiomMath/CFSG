module

public import CFSG.RankThree.PartOne.S15K.ReflGroup
public import CFSG.RankThree.PartOne.S12.InvolAbelian
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.RankThree.PartOne.AUTSL.Four

open Equiv CFSG.RankThree.PartOne.S15K
open CFSG.RankThree.PartOne.Torsion37 (card_sup_of_commute_disjoint)

section Lines

variable {M : Type*} [CommGroup M] {p : ℕ} {ℓ : Fin 3 → Subgroup M}

structure ThreeLines (p : ℕ) (ℓ : Fin 3 → Subgroup M) : Prop where
  card : ∀ i, Nat.card ↥(ℓ i) = p
  top : ⨆ i, ℓ i = ⊤
  indep : ∀ i, ℓ i ⊓ ⨆ j, ⨆ (_ : j ≠ i), ℓ j = ⊥

@[expose] def lineHyp (ℓ : Fin 3 → Subgroup M) (k : Fin 3) : Subgroup M :=
  ⨆ j, ⨆ (_ : j ≠ k), ℓ j

theorem ThreeLines.le_hyp (_ : ThreeLines p ℓ) {i k : Fin 3} (h : i ≠ k) : ℓ i ≤ lineHyp ℓ k :=
  le_iSup₂_of_le (f := fun j (_ : j ≠ k) => ℓ j) i h le_rfl

theorem ThreeLines.inf_eq_bot (hℓ : ThreeLines p ℓ) {i k : Fin 3} (h : i ≠ k) : ℓ i ⊓ ℓ k = ⊥ := by
  rw [eq_bot_iff, ← hℓ.indep k, inf_comm]
  exact inf_le_inf_left _ (hℓ.le_hyp h)

theorem ThreeLines.ne (hp : p.Prime) (hℓ : ThreeLines p ℓ) {i k : Fin 3} (h : i ≠ k) :
    ℓ i ≠ ℓ k := by
  intro he
  have h1 := hℓ.inf_eq_bot h
  rw [he, inf_idem] at h1
  have h2 := hℓ.card k
  rw [h1, Subgroup.card_bot] at h2
  exact hp.one_lt.ne h2

theorem ThreeLines.injective (hp : p.Prime) (hℓ : ThreeLines p ℓ) : Function.Injective ℓ :=
  fun _ _ hij => by_contra fun h => hℓ.ne hp h hij

theorem ThreeLines.sup_hyp (hℓ : ThreeLines p ℓ) (k : Fin 3) : ℓ k ⊔ lineHyp ℓ k = ⊤ := by
  rw [lineHyp, ← iSup_split_single ℓ k, hℓ.top]

theorem ThreeLines.card_hyp (hp : p.Prime) (hℓ : ThreeLines p ℓ) (hM : Nat.card M = p ^ 3)
    (k : Fin 3) : Nat.card ↥(lineHyp ℓ k) = p ^ 2 := by
  have hdisj : Disjoint (ℓ k) (lineHyp ℓ k) := disjoint_iff.2 (hℓ.indep k)
  have h := card_sup_of_commute_disjoint (fun a _ b _ => mul_comm a b) hdisj
  rw [hℓ.sup_hyp k, Subgroup.card_top, hM, hℓ.card k] at h
  refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
  rw [← h]
  ring

@[expose] def LineMono (ℓ : Fin 3 → Subgroup M) (x : MulAut M) : Prop :=
  ∃ π : Perm (Fin 3), ∀ i, (ℓ i).map x.toMonoidHom = ℓ (π i)

theorem LineMono.fix_of_moved (hℓ : ThreeLines p ℓ) {x : MulAut M} (hx : LineMono ℓ x)
    {k : Fin 3} (hmov : ∀ e, x e * e⁻¹ ∈ ℓ k) {i : Fin 3} (hik : i ≠ k) {e : M} (he : e ∈ ℓ i) :
    x e = e := by
  obtain ⟨π, hπ⟩ := hx
  have hxe : x e ∈ ℓ (π i) := by
    have : x e ∈ (ℓ i).map x.toMonoidHom := Subgroup.mem_map_of_mem _ he
    rwa [hπ i] at this
  by_cases hπk : π i = k
  · rw [hπk] at hxe
    have h1 : e⁻¹ ∈ ℓ k := by
      have := (ℓ k).mul_mem ((ℓ k).inv_mem hxe) (hmov e)
      simpa [mul_assoc] using this
    have h2 : e ∈ ℓ k := by simpa using (ℓ k).inv_mem h1
    have h3 : e ∈ ℓ i ⊓ ℓ k := ⟨he, h2⟩
    rw [hℓ.inf_eq_bot hik, Subgroup.mem_bot] at h3
    rw [h3, map_one]
  · have h1 : x e ∈ lineHyp ℓ k := hℓ.le_hyp hπk hxe
    have h2 : e ∈ lineHyp ℓ k := hℓ.le_hyp hik he
    have h3 : x e * e⁻¹ ∈ ℓ k ⊓ lineHyp ℓ k :=
      ⟨hmov e, (lineHyp ℓ k).mul_mem h1 ((lineHyp ℓ k).inv_mem h2)⟩
    have hind : ℓ k ⊓ lineHyp ℓ k = ⊥ := hℓ.indep k
    rw [hind, Subgroup.mem_bot, mul_inv_eq_one] at h3
    exact h3

theorem LineMono.map_self (hp : p.Prime) (hℓ : ThreeLines p ℓ) {x : MulAut M} (hx : LineMono ℓ x)
    {k : Fin 3} (hmov : ∀ e, x e * e⁻¹ ∈ ℓ k) : (ℓ k).map x.toMonoidHom = ℓ k := by
  obtain ⟨π, hπ⟩ := hx
  have hfix : ∀ i, i ≠ k → π i = i := by
    intro i hik
    have h1 : (ℓ i).map x.toMonoidHom = ℓ i := by
      ext e
      constructor
      · rintro ⟨f, hf, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, LineMono.fix_of_moved hℓ ⟨π, hπ⟩ hmov hik hf]
        exact hf
      · intro he
        exact ⟨e, he, LineMono.fix_of_moved hℓ ⟨π, hπ⟩ hmov hik he⟩
    exact hℓ.injective hp ((hπ i).symm.trans h1)
  have hk : π k = k := by
    by_contra hne
    have h2 : π (π k) = π k := hfix _ hne
    exact hne (π.injective h2)
  rw [hπ k, hk]

theorem LineMono.comm (hp : p.Prime) (hℓ : ThreeLines p ℓ) {x y : MulAut M} (hx : LineMono ℓ x)
    (hy : LineMono ℓ y) {k j : Fin 3} (hkj : k ≠ j) (hmx : ∀ e, x e * e⁻¹ ∈ ℓ k)
    (hmy : ∀ e, y e * e⁻¹ ∈ ℓ j) : x * y = y * x := by
  have hxk : ∀ e ∈ ℓ k, x e ∈ ℓ k := fun e he => by
    have : x e ∈ (ℓ k).map x.toMonoidHom := Subgroup.mem_map_of_mem _ he
    rwa [LineMono.map_self hp hℓ hx hmx] at this
  have hyj : ∀ e ∈ ℓ j, y e ∈ ℓ j := fun e he => by
    have : y e ∈ (ℓ j).map y.toMonoidHom := Subgroup.mem_map_of_mem _ he
    rwa [LineMono.map_self hp hℓ hy hmy] at this
  have hle : ⨆ m, ℓ m ≤ MonoidHom.eqLocus (x * y).toMonoidHom (y * x).toMonoidHom := by
    refine iSup_le fun m e he => ?_
    show x (y e) = y (x e)
    by_cases hmk : m = k
    · subst hmk
      rw [LineMono.fix_of_moved hℓ hy hmy hkj he, LineMono.fix_of_moved hℓ hy hmy hkj (hxk e he)]
    · by_cases hmj : m = j
      · subst hmj
        rw [LineMono.fix_of_moved hℓ hx hmx (Ne.symm hkj) he,
          LineMono.fix_of_moved hℓ hx hmx (Ne.symm hkj) (hyj e he)]
      · rw [LineMono.fix_of_moved hℓ hx hmx hmk he, LineMono.fix_of_moved hℓ hy hmy hmj he,
          LineMono.fix_of_moved hℓ hx hmx hmk he]
  rw [hℓ.top] at hle
  exact MulEquiv.ext fun e => hle (Subgroup.mem_top e)

theorem comm_of_fix_lines (hp : p.Prime) (hℓ : ThreeLines p ℓ) {x y : MulAut M}
    (hx : ∀ i, (ℓ i).map x.toMonoidHom = ℓ i) (hy : ∀ i, (ℓ i).map y.toMonoidHom = ℓ i) :
    x * y = y * x := by
  have hxi : ∀ i, ∀ e ∈ ℓ i, x e ∈ ℓ i := fun i e he => by
    have : x e ∈ (ℓ i).map x.toMonoidHom := Subgroup.mem_map_of_mem _ he
    rwa [hx i] at this
  have hyi : ∀ i, ∀ e ∈ ℓ i, y e ∈ ℓ i := fun i e he => by
    have : y e ∈ (ℓ i).map y.toMonoidHom := Subgroup.mem_map_of_mem _ he
    rwa [hy i] at this
  have hle : ⨆ m, ℓ m ≤ MonoidHom.eqLocus (x * y).toMonoidHom (y * x).toMonoidHom := by
    refine iSup_le fun m e he => ?_
    show x (y e) = y (x e)
    have : Fact p.Prime := ⟨hp⟩
    have hcyc : IsCyclic ↥(ℓ m) := isCyclic_of_prime_card (hℓ.card m)
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hpow : ∀ z ∈ ℓ m, ∃ n : ℤ, z = (g : M) ^ n := fun z hz => by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨z, hz⟩)
      exact ⟨n, by simpa using (congrArg Subtype.val hn).symm⟩
    obtain ⟨a, ha⟩ := hpow (x g) (hxi m g g.2)
    obtain ⟨b, hb⟩ := hpow (y g) (hyi m g g.2)
    have hg0 : x (y g) = y (x g) := by
      rw [hb, ha, map_zpow, map_zpow, ha, hb, ← zpow_mul, ← zpow_mul, mul_comm]
    obtain ⟨n, rfl⟩ := hpow e he
    rw [map_zpow, map_zpow, map_zpow, map_zpow, hg0]
  rw [hℓ.top] at hle
  exact MulEquiv.ext fun e => hle (Subgroup.mem_top e)

theorem fixS_eq_lineHyp [Finite M] (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ThreeLines p ℓ)
    (hM : Nat.card M = p ^ 3) (hpow : ∀ a : M, a ^ p = 1) {x : MulAut M} (hx : LineMono ℓ x)
    (hx2 : x * x = 1) {k : Fin 3} (hmov : Invol.movedS x = ℓ k) :
    Invol.fixS x = lineHyp ℓ k := by
  have hm : ∀ e, x e * e⁻¹ ∈ ℓ k := fun e => hmov ▸ Subgroup.subset_closure ⟨e, rfl⟩
  have hle : lineHyp ℓ k ≤ Invol.fixS x := by
    refine iSup₂_le fun i hik e he => ?_
    exact LineMono.fix_of_moved hℓ hx hm hik he
  have hcard := Invol.card_eq_mul hp hp2 hpow hx2
  rw [hM, ← Invol.movedS_eq_invS hp hp2 hpow hx2, hmov, hℓ.card k] at hcard
  have hfix : Nat.card ↥(Invol.fixS x) = p ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
    rw [pow_succ'] at hcard
    rw [hcard]
    ring
  have := hℓ.card_hyp hp hM k
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hfix, this])).symm

end Lines

theorem r2_abelian_normal_card (N : Subgroup R2S4) [N.Normal]
    (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) : Nat.card ↥N ≤ 8 := by
  classical
  let S : Finset R2S4 := Finset.univ.filter fun x =>
    ∀ g : Perm (Fin 4), x * ((1, g) * x * (1, g)⁻¹) = ((1, g) * x * (1, g)⁻¹) * x
  have hS : S.card = 8 := by decide
  have hsub : ∀ x : ↥N, (x : R2S4) ∈ S := fun x => by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun g => ?_⟩
    exact hN _ x.2 _ (Subgroup.Normal.conj_mem inferInstance _ x.2 _)
  calc Nat.card ↥N ≤ Nat.card ↥S :=
        Nat.card_le_card_of_injective (fun x => ⟨x, hsub x⟩) fun a b h =>
          Subtype.ext (congrArg (fun z : ↥S => (z : R2S4)) h)
    _ = 8 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hS]

theorem card_r2s4 : Nat.card R2S4 = 48 := by
  have h1 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)]
    exact Nat.card_zmod 2
  rw [Nat.card_prod, Nat.card_perm, h1, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]
  rfl

section Hom

variable {M : Type*} [CommGroup M] {p : ℕ} {ℓ : Fin 3 → Subgroup M}

theorem perm_unique (hℓ : Function.Injective ℓ) {x : MulAut M} {π π' : Perm (Fin 3)}
    (h : ∀ i, (ℓ i).map x.toMonoidHom = ℓ (π i))
    (h' : ∀ i, (ℓ i).map x.toMonoidHom = ℓ (π' i)) : π = π' :=
  Equiv.ext fun i => hℓ ((h i).symm.trans (h' i))

theorem map_mul_eq (H : Subgroup M) (x y : MulAut M) :
    H.map (x * y).toMonoidHom = (H.map y.toMonoidHom).map x.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem map_one_eq (H : Subgroup M) : H.map (1 : MulAut M).toMonoidHom = H := by
  ext x
  simp

noncomputable def lineHomOn (hℓ : Function.Injective ℓ) (X : Subgroup (MulAut M))
    (hX : ∀ x ∈ X, LineMono ℓ x) : X →* Perm (Fin 3) where
  toFun x := Classical.choose (hX x x.2)
  map_one' := by
    refine perm_unique hℓ (x := ((1 : X) : MulAut M)) (Classical.choose_spec (hX _ (1 : X).2))
      (fun i => ?_)
    exact map_one_eq _
  map_mul' x y := by
    have hy := Classical.choose_spec (hX y y.2)
    have hx := Classical.choose_spec (hX x x.2)
    refine perm_unique hℓ (x := ((x * y : X) : MulAut M))
      (Classical.choose_spec (hX _ (x * y).2)) (fun i => ?_)
    show (ℓ i).map (x.1 * y.1).toMonoidHom = _
    rw [map_mul_eq, hy i, hx]
    rfl

theorem lineHomOn_spec (hℓ : Function.Injective ℓ) (X : Subgroup (MulAut M))
    (hX : ∀ x ∈ X, LineMono ℓ x) (x : X) (i : Fin 3) :
    (ℓ i).map (x : MulAut M).toMonoidHom = ℓ (lineHomOn hℓ X hX x i) :=
  Classical.choose_spec (hX x x.2) i

@[expose] def lineMonoSubgroup (ℓ : Fin 3 → Subgroup M) : Subgroup (MulAut M) where
  carrier := {x | LineMono ℓ x}
  one_mem' := ⟨1, fun i => by rw [map_one_eq]; rfl⟩
  mul_mem' := by
    rintro x y ⟨π, hπ⟩ ⟨σ, hσ⟩
    exact ⟨π * σ, fun i => by rw [map_mul_eq, hσ i, hπ]; rfl⟩
  inv_mem' := by
    rintro x ⟨π, hπ⟩
    refine ⟨π.symm, fun i => ?_⟩
    have h1 : (ℓ (π.symm i)).map x.toMonoidHom = ℓ i := by rw [hπ]; simp
    calc (ℓ i).map x⁻¹.toMonoidHom
        = ((ℓ (π.symm i)).map x.toMonoidHom).map x⁻¹.toMonoidHom := by rw [h1]
      _ = (ℓ (π.symm i)).map (x⁻¹ * x).toMonoidHom := (map_mul_eq _ _ _).symm
      _ = ℓ (π.symm i) := by rw [inv_mul_cancel, map_one_eq]

theorem exists_mem_map_eq (hp : p.Prime) (hℓ : ThreeLines p ℓ) (X : Subgroup (MulAut M))
    (hX : ∀ x ∈ X, LineMono ℓ x) (φ : X ≃* R2S4) (i j : Fin 3) :
    ∃ x ∈ X, (ℓ i).map x.toMonoidHom = ℓ j := by
  classical
  let f := lineHomOn (hℓ.injective hp) X hX
  have hfix : ∀ c : X, c ∈ f.ker → ∀ i, (ℓ i).map (c : MulAut M).toMonoidHom = ℓ i := by
    intro c hc i
    rw [lineHomOn_spec (hℓ.injective hp) X hX c i]
    have : f c = 1 := MonoidHom.mem_ker.1 hc
    rw [show lineHomOn (hℓ.injective hp) X hX c = 1 from this]
    rfl
  have hker : ∀ a ∈ f.ker, ∀ b ∈ f.ker, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (comm_of_fix_lines hp hℓ (hfix a ha) (hfix b hb))
  let N : Subgroup R2S4 := f.ker.map φ.toMonoidHom
  have : N.Normal := Subgroup.Normal.map f.normal_ker φ.toMonoidHom φ.surjective
  have hN : ∀ u ∈ N, ∀ v ∈ N, u * v = v * u := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul, hker a ha b hb]
  have hcardN := r2_abelian_normal_card N hN
  have hcardker : Nat.card N = Nat.card f.ker := Subgroup.card_map_of_injective φ.injective
  have hXcard : Nat.card X = 48 := (Nat.card_congr φ.toEquiv).trans card_r2s4
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hXcard] at h1
  have h6 : Nat.card (Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
    rfl
  have hle : Nat.card f.range ≤ 6 := h6 ▸ Subgroup.card_le_card_group f.range
  have hge : 6 ≤ Nat.card f.range := by
    by_contra hlt
    have : Nat.card f.range ≤ 5 := by omega
    have h8 : Nat.card f.ker ≤ 8 := hcardker ▸ hcardN
    nlinarith
  have htop : f.range = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, h6]
    omega
  have hmem : Equiv.swap i j ∈ f.range := by
    rw [htop]
    trivial
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, x.2, ?_⟩
  rw [lineHomOn_spec (hℓ.injective hp) X hX x i]
  have : lineHomOn (hℓ.injective hp) X hX x = Equiv.swap i j := hx
  rw [this, Equiv.swap_apply_left]

end Hom

end CFSG.RankThree.PartOne.AUTSL.Four
