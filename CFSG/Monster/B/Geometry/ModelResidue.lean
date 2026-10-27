module

public import CFSG.Monster.B.Geometry.Gallery
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W} {F : Type*}

inductive PathLE (r₁ r₂ : F → F → Prop) : ℕ → F → F → Prop
  | refl (n : ℕ) (a : F) : PathLE r₁ r₂ n a a
  | step {n : ℕ} {a b c : F} (h : r₁ a b ∨ r₂ a b) (h' : PathLE r₁ r₂ n b c) :
      PathLE r₁ r₂ (n + 1) a c

theorem PathLE.mono {r₁ r₂ : F → F → Prop} {m n : ℕ} {a b : F} (h : PathLE r₁ r₂ m a b)
    (hmn : m ≤ n) : PathLE r₁ r₂ n a b := by
  induction h generalizing n with
  | refl => exact .refl _ _
  | step h _ ih =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact .step h (ih (by omega))

theorem PathLE.swap {r₁ r₂ : F → F → Prop} {n : ℕ} {a b : F} (h : PathLE r₁ r₂ n a b) :
    PathLE r₂ r₁ n a b := by
  induction h with
  | refl => exact .refl _ _
  | step h _ ih => exact .step h.symm ih

variable (cs δ) in
@[expose] def IsModelResidue (r₁ r₂ : F → F → Prop) (i j : ι) (x : C) (f : C → F) : Prop :=
  Set.BijOn f (residue cs δ {i, j} x) Set.univ ∧
    ∀ y ∈ residue cs δ {i, j} x, ∀ z ∈ residue cs δ {i, j} x,
      (δ y z = cs.simple i ↔ y ≠ z ∧ r₁ (f y) (f z)) ∧
      (δ y z = cs.simple j ↔ y ≠ z ∧ r₂ (f y) (f z))

theorem IsModelResidue.swap {r₁ r₂ : F → F → Prop} {i j : ι} {x : C} {f : C → F}
    (hf : IsModelResidue cs δ r₁ r₂ i j x f) : IsModelResidue cs δ r₂ r₁ j i x f := by
  rw [IsModelResidue, Set.pair_comm]
  exact ⟨hf.1, fun y hy z hz => (hf.2 y (Set.pair_comm i j ▸ hy) z
    (Set.pair_comm i j ▸ hz)).symm⟩

variable (hδ : IsWeylDistanceBuilding cs δ)
include hδ

theorem IsModelResidue.length_le {r₁ r₂ : F → F → Prop} {i j : ι} {x : C} {f : C → F}
    (hf : IsModelResidue cs δ r₁ r₂ i j x f) {y z : C} (hy : y ∈ residue cs δ {i, j} x)
    (hz : z ∈ residue cs δ {i, j} x) {n : ℕ} (h : PathLE r₁ r₂ n (f y) (f z)) :
    cs.length (δ y z) ≤ n := by
  obtain ⟨a, ha⟩ : ∃ a, f y = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, f z = b := ⟨_, rfl⟩
  rw [ha, hb] at h
  induction h generalizing y with
  | refl n a =>
    rw [hf.1.injOn hy hz (ha.trans hb.symm), hδ.eq_one_self, cs.length_one]
    exact Nat.zero_le _
  | @step n a b c hab _ ih =>
    obtain ⟨y', hy', rfl⟩ := hf.1.surjOn (Set.mem_univ b)
    have h1 := ih hy' rfl hb
    have key : δ y y' = 1 ∨ δ y y' = cs.simple i ∨ δ y y' = cs.simple j := by
      by_cases e : y = y'
      · exact Or.inl (by rw [e, hδ.eq_one_self])
      · rcases hab with hab | hab
        · exact Or.inr (Or.inl (((hf.2 y hy y' hy').1).mpr ⟨e, ha ▸ hab⟩))
        · exact Or.inr (Or.inr (((hf.2 y hy y' hy').2).mpr ⟨e, ha ▸ hab⟩))
    have hsucc : ∀ k : ι, δ y y' = cs.simple k → cs.length (δ y z) ≤ n + 1 := by
      intro k hk
      have hk' := hδ.symm_of_eq_simple hk
      rcases (hδ.mul_simple z y' y k hk').1 with h | h
      · rw [dist_inv hδ z y, cs.length_inv, h, ← cs.length_inv, ← dist_inv hδ z y']
        omega
      · rw [dist_inv hδ z y, cs.length_inv, h]
        have := cs.length_mul_le (δ z y') (cs.simple k)
        have h2 : cs.length (δ z y') = cs.length (δ y' z) := by
          rw [dist_inv hδ y' z, cs.length_inv]
        rw [cs.length_simple] at this
        omega
    rcases key with h | h | h
    · rw [(hδ.eq_one_iff y y').mp h]
      omega
    · exact hsucc i h
    · exact hsucc j h

omit hδ in
theorem IsModelResidue.exists_perm {r₁ r₂ : F → F → Prop} {i j : ι} {x : C} {f : C → F}
    (hf : IsModelResidue cs δ r₁ r₂ i j x f) (hr₁ : ∀ a, r₁ a a) (hr₂ : ∀ a, r₂ a a)
    {g : C → C} (hg : IsTypeIso cs δ δ (residue cs δ {i, j} x) (residue cs δ {i, j} x) g) :
    ∃ G : Equiv.Perm F, (∀ y ∈ residue cs δ {i, j} x, G (f y) = f (g y)) ∧
      (∀ a b, r₁ (G a) (G b) ↔ r₁ a b) ∧ (∀ a b, r₂ (G a) (G b) ↔ r₂ a b) := by
  set R := residue cs δ {i, j} x
  let e : R ≃ F := (hf.1.equiv f).trans (Equiv.Set.univ F)
  have he : ∀ (y : C) (hy : y ∈ R), e ⟨y, hy⟩ = f y := fun _ _ => rfl
  let eg : R ≃ R := hg.1.equiv g
  have heg : ∀ (y : C) (hy : y ∈ R), (eg ⟨y, hy⟩ : C) = g y := fun _ _ => rfl
  let G : Equiv.Perm F := e.symm.trans (eg.trans e)
  have hG : ∀ y (hy : y ∈ R), G (f y) = f (g y) := by
    intro y hy
    change e (eg (e.symm (f y))) = f (g y)
    rw [← he y hy, Equiv.symm_apply_apply, he _ (eg ⟨y, hy⟩).2, heg]
  have hrel : ∀ (k : ι) (r : F → F → Prop), (∀ a, r a a) →
      (∀ y ∈ R, ∀ z ∈ R, (δ y z = cs.simple k ↔ y ≠ z ∧ r (f y) (f z))) →
      ∀ a b, r (G a) (G b) ↔ r a b := by
    intro k r hr hk a b
    obtain ⟨y, hy, rfl⟩ := hf.1.surjOn (Set.mem_univ a)
    obtain ⟨z, hz, rfl⟩ := hf.1.surjOn (Set.mem_univ b)
    rw [hG y hy, hG z hz]
    have hgy := hg.1.mapsTo hy
    have hgz := hg.1.mapsTo hz
    by_cases e : y = z
    · subst e
      exact ⟨fun _ => hr _, fun _ => hr _⟩
    · have e' : g y ≠ g z := fun h => e (hg.1.injOn hy hz h)
      have h1 := hk (g y) hgy (g z) hgz
      have h2 := hk y hy z hz
      have h3 := hg.2 y hy z hz k
      constructor
      · intro h
        exact (h2.mp (h3.mp (h1.mpr ⟨e', h⟩))).2
      · intro h
        exact (h1.mp (h3.mpr (h2.mpr ⟨e, h⟩))).2
  exact ⟨G, hG, hrel i r₁ hr₁ fun y hy z hz => (hf.2 y hy z hz).1,
    hrel j r₂ hr₂ fun y hy z hz => (hf.2 y hy z hz).2⟩

omit hδ in
variable (cs δ) in
@[expose] def residueStab (R : Set C) (y z : R) : Subgroup (Equiv.Perm R) where
  carrier := {g | g ∈ typeAut cs (fun u v : R => δ u v) ∧ g y = y ∧ g z = z}
  mul_mem' {g h} hg hh := ⟨mul_mem hg.1 hh.1, by simp [hh.2.1, hg.2.1], by simp [hh.2.2, hg.2.2]⟩
  one_mem' := ⟨one_mem _, rfl, rfl⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, by
    rw [Equiv.Perm.inv_eq_iff_eq]; exact hg.2.1.symm, by
    rw [Equiv.Perm.inv_eq_iff_eq]; exact hg.2.2.symm⟩

omit hδ in
theorem mem_residueStab {R : Set C} {y z : R} {g : Equiv.Perm R} :
    g ∈ residueStab cs δ R y z ↔
      g ∈ typeAut cs (fun u v : R => δ u v) ∧ g y = y ∧ g z = z :=
  Iff.rfl

theorem IsModelResidue.nat_card_residueStab {r₁ r₂ : F → F → Prop} {i j : ι} {x : C}
    {f : C → F} (hf : IsModelResidue cs δ r₁ r₂ i j x f) (hr₁ : ∀ a, r₁ a a) (hr₂ : ∀ a, r₂ a a)
    (y z : residue cs δ {i, j} x) :
    Nat.card (residueStab cs δ (residue cs δ {i, j} x) y z) =
      Nat.card {G : Equiv.Perm F // (∀ a b, r₁ (G a) (G b) ↔ r₁ a b) ∧
        (∀ a b, r₂ (G a) (G b) ↔ r₂ a b) ∧ G (f y) = f y ∧ G (f z) = f z} := by
  set R := residue cs δ {i, j} x
  let e : R ≃ F := (hf.1.equiv f).trans (Equiv.Set.univ F)
  have he : ∀ u : R, e u = f u := fun _ => rfl
  have hrel : ∀ (k : ι) (r : F → F → Prop), (∀ a, r a a) →
      (∀ y ∈ R, ∀ z ∈ R, (δ y z = cs.simple k ↔ y ≠ z ∧ r (f y) (f z))) →
      ∀ (g : Equiv.Perm R), (∀ u v : R, δ (g u) (g v) = cs.simple k ↔ δ u v = cs.simple k) →
        ∀ a b, r (e (g (e.symm a))) (e (g (e.symm b))) ↔ r a b := by
    intro k r hr hk g hg a b
    obtain ⟨u, rfl⟩ := e.surjective a
    obtain ⟨v, rfl⟩ := e.surjective b
    simp only [Equiv.symm_apply_apply]
    simp only [he]
    by_cases huv : u = v
    · subst huv
      exact ⟨fun _ => hr _, fun _ => hr _⟩
    · have huv' : (u : C) ≠ v := fun h => huv (Subtype.ext h)
      have hguv : ((g u : R) : C) ≠ g v := fun h => huv (g.injective (Subtype.ext h))
      have h1 := hk _ (g u).2 _ (g v).2
      have h2 := hk _ u.2 _ v.2
      constructor
      · intro h
        exact (h2.mp ((hg u v).mp (h1.mpr ⟨hguv, h⟩))).2
      · intro h
        exact (h1.mp ((hg u v).mpr (h2.mpr ⟨huv', h⟩))).2
  have hback : ∀ (G : Equiv.Perm F), (∀ a b, r₁ (G a) (G b) ↔ r₁ a b) →
      (∀ a b, r₂ (G a) (G b) ↔ r₂ a b) →
      e.trans (G.trans e.symm) ∈ typeAut cs (fun u v : R => δ u v) := by
    intro G h1 h2 u v k
    have hGu : e (e.trans (G.trans e.symm) u) = G (e u) := by simp
    have hGv : e (e.trans (G.trans e.symm) v) = G (e v) := by simp
    have hmem : ∀ a b : R, δ a b ∈ cs.parabolic {i, j} :=
      fun a b => mem_parabolic_of_mem_residue hδ a.2 b.2
    by_cases hk : k = i ∨ k = j
    · have hne : ∀ a b : R, (a : C) ≠ b ↔ e a ≠ e b := fun a b =>
        ⟨fun h h' => h (congrArg Subtype.val (e.injective h')),
          fun h h' => h (congrArg e (Subtype.ext h'))⟩
      rcases hk with rfl | rfl
      · rw [((hf.2 _ (e.trans (G.trans e.symm) u).2 _ (e.trans (G.trans e.symm) v).2).1),
          ((hf.2 _ u.2 _ v.2).1), hne, hne, ← he, ← he, hGu, hGv, ← he, ← he, G.injective.ne_iff,
          h1]
      · rw [((hf.2 _ (e.trans (G.trans e.symm) u).2 _ (e.trans (G.trans e.symm) v).2).2),
          ((hf.2 _ u.2 _ v.2).2), hne, hne, ← he, ← he, hGu, hGv, ← he, ← he, G.injective.ne_iff,
          h2]
    · push Not at hk
      have hnot : ∀ a b : R, δ a b ≠ cs.simple k := fun a b h => by
        have := hmem a b
        rw [h, simple_mem_parabolic_iff cs] at this
        rcases this with h' | h'
        · exact hk.1 h'
        · exact hk.2 (Set.mem_singleton_iff.mp h')
      exact ⟨fun h => absurd h (hnot _ _), fun h => absurd h (hnot _ _)⟩
  refine Nat.card_congr
    { toFun := fun g => ⟨e.symm.trans (g.1.trans e), hrel i r₁ hr₁
          (fun y hy z hz => (hf.2 y hy z hz).1) g.1 (fun u v => g.2.1 u v i),
        hrel j r₂ hr₂ (fun y hy z hz => (hf.2 y hy z hz).2) g.1 (fun u v => g.2.1 u v j),
        by simp [← he, g.2.2.1], by simp [← he, g.2.2.2]⟩
      invFun := fun G => ⟨e.trans (G.1.trans e.symm), hback G.1 G.2.1 G.2.2.1, by
          simp only [Equiv.trans_apply]
          rw [Equiv.symm_apply_eq, he, G.2.2.2.1], by
          simp only [Equiv.trans_apply]
          rw [Equiv.symm_apply_eq, he, G.2.2.2.2]⟩
      left_inv := fun g => by ext u; simp
      right_inv := fun G => by ext a; simp }

theorem fix_residue_of_commute {i j : ι} (hij : i ≠ j) (hM : M i j = 2) {a : C} {g : C → C}
    (hg : IsTypeIso cs δ δ (residue cs δ {i, j} a) (residue cs δ {i, j} a) g)
    (hfix : ∀ y ∈ panel cs δ i a ∪ panel cs δ j a, g y = y) :
    ∀ y ∈ residue cs δ {i, j} a, g y = y := by
  intro y hy
  have hmem : δ a y ∈ cs.parabolic {i, j} :=
    mem_parabolic_of_mem_residue hδ (self_mem_residue _ a) hy
  obtain ⟨ω, hω, hωJ, hωy⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hmem
  have hlen : ω.length ≤ 2 := by
    rw [← hω.eq, hωy, ← hM]
    exact length_le_of_mem_parabolic_pair (cs := cs) (by omega) hmem
  have hpanel : ∀ k ∈ ({i, j} : Set ι), ∀ w, δ a w = cs.simple k →
      w ∈ panel cs δ i a ∪ panel cs δ j a := by
    intro k hk w hw
    rcases hk with rfl | hk
    · exact Or.inl ((mem_panel_iff hδ).mpr (Or.inr hw))
    · rw [Set.mem_singleton_iff.mp hk] at hw
      exact Or.inr ((mem_panel_iff hδ).mpr (Or.inr hw))
  match ω, hω, hωJ, hωy, hlen with
  | [], _, _, hωy, _ =>
    rw [cs.wordProd_nil, eq_comm, hδ.eq_one_iff] at hωy
    rw [← hωy]
    exact hfix a (Or.inl (self_mem_residue _ a))
  | [k], _, hωJ, hωy, _ =>
    rw [cs.wordProd_singleton] at hωy
    exact hfix y (hpanel k (hωJ k (by simp)) y hωy.symm)
  | [k₁, k₂], hω, hωJ, hωy, _ =>
    have hk12 : k₁ ≠ k₂ := by
      have := hω.isChain_ne
      simpa using this
    have hk₁ := hωJ k₁ (by simp)
    have hk₂ := hωJ k₂ (by simp)
    have hcomm : cs.simple k₁ * cs.simple k₂ = cs.simple k₂ * cs.simple k₁ := by
      have hM' : M k₁ k₂ = 2 := by
        rcases hk₁ with rfl | hk₁ <;> rcases hk₂ with rfl | hk₂
        · exact absurd rfl hk12
        · rw [Set.mem_singleton_iff.mp hk₂]; exact hM
        · rw [Set.mem_singleton_iff.mp hk₁, M.symmetric]; exact hM
        · exact absurd ((Set.mem_singleton_iff.mp hk₁).trans
            (Set.mem_singleton_iff.mp hk₂).symm) hk12
      have h2 := cs.simple_mul_simple_pow k₁ k₂
      rw [hM', pow_two] at h2
      have := eq_inv_of_mul_eq_one_left h2
      rw [this, mul_inv_rev, cs.inv_simple, cs.inv_simple]
    have hω' : cs.IsReduced [k₂, k₁] := by
      rw [CoxeterSystem.IsReduced] at hω ⊢
      rw [show cs.wordProd [k₂, k₁] = cs.wordProd [k₁, k₂] by
        simp [cs.wordProd_cons, hcomm]]
      exact hω
    have hωy' : cs.wordProd [k₂, k₁] = δ a y := by
      rw [← hωy]
      simp [cs.wordProd_cons, hcomm]
    obtain ⟨γ, hγ, hγt, hγe⟩ := exists_strictGallery hδ hω hωy
    obtain ⟨γ', hγ', hγ't, hγ'e⟩ := exists_strictGallery hδ hω' hωy'
    match γ, hγ, hγt, hγe, γ', hγ', hγ't, hγ'e with
    | [p, q], hγ, hγt, hγe, [p', q'], hγ', hγ't, hγ'e =>
      simp only [galleryType_cons, galleryType_nil, List.cons.injEq, and_true] at hγt hγ't
      simp only [galleryEnd_cons, galleryEnd_nil] at hγe hγ'e
      obtain ⟨h1, h2, -⟩ := hγ
      obtain ⟨h1', h2', -⟩ := hγ'
      rw [hγt.1] at h1
      rw [hγt.2, hγe] at h2
      rw [hγ't.1] at h1'
      rw [hγ't.2, hγ'e] at h2'
      have hz := hfix p.2 (hpanel k₁ hk₁ p.2 h1)
      have hz' := hfix p'.2 (hpanel k₂ hk₂ p'.2 h1')
      have hzR : p.2 ∈ residue cs δ {i, j} a :=
        (mem_residue_iff_mem_parabolic hδ).mpr (h1 ▸ cs.simple_mem_parabolic hk₁)
      have hz'R : p'.2 ∈ residue cs δ {i, j} a :=
        (mem_residue_iff_mem_parabolic hδ).mpr (h1' ▸ cs.simple_mem_parabolic hk₂)
      have hgy : δ p.2 (g y) = cs.simple k₂ := by
        rw [← hz]
        exact (hg.2 _ hzR _ hy k₂).mpr h2
      have hgy' : δ p'.2 (g y) = cs.simple k₁ := by
        rw [← hz']
        exact (hg.2 _ hz'R _ hy k₁).mpr h2'
      by_contra hne
      have e1 := dist_eq_simple_of_eq_simple hδ (hδ.symm_of_eq_simple h2)
        (hδ.symm_of_eq_simple hgy) (Ne.symm hne)
      have e2 := dist_eq_simple_of_eq_simple hδ (hδ.symm_of_eq_simple h2')
        (hδ.symm_of_eq_simple hgy') (Ne.symm hne)
      exact hk12 (cs.simple_injective (e2.symm.trans e1))
  | _ :: _ :: _ :: _, _, _, _, hlen => simp at hlen

end CFSG.Monster.B.Geometry
