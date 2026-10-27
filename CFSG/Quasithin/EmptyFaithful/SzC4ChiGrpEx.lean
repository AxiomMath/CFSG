module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChiGrpDef

public section

namespace CFSG.Quasithin.SzC4

theorem isExpTwo_subgroup {X : Type} [Group X] (hX : IsExpTwo X) (H : Subgroup X) :
    IsExpTwo H := fun x => Subtype.ext (hX x)

@[expose] def subHom {X Y : Type} [Group X] [Group Y] (f : X →* Y) (H : Subgroup X)
    (H' : Subgroup Y) (h : ∀ x ∈ H, f x ∈ H') : H →* H' where
  toFun x := ⟨f x, h x x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp] theorem subHom_apply {X Y : Type} [Group X] [Group Y] (f : X →* Y) (H : Subgroup X)
    (H' : Subgroup Y) (h : ∀ x ∈ H, f x ∈ H') (x : H) : ((subHom f H H' h x : H') : Y) = f x :=
  rfl

theorem ker_invariant {X Y : Type} [Group X] [Group Y] (f : X →* Y) (φX : MulAut X)
    (φY : MulAut Y) (h1 : ∀ x, φY (f x) = f (φX x)) (x : X) : φX x ∈ f.ker ↔ x ∈ f.ker := by
  simp only [MonoidHom.mem_ker, ← h1, EmbeddingLike.map_eq_one_iff]

@[expose] def sqMapQ {X Y : Type} [Group X] [Group Y] (f : X →* Y) : X ⧸ sq X →* Y ⧸ sq Y :=
  QuotientGroup.map (sq X) (sq Y) f (Subgroup.map_le_iff_le_comap.1 (sq_map_le f))

@[simp] theorem sqMapQ_mk {X Y : Type} [Group X] [Group Y] (f : X →* Y) (x : X) :
    sqMapQ f (QuotientGroup.mk x) = QuotientGroup.mk (f x) := rfl

theorem sqMapQ_surjective {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) : Function.Surjective (sqMapQ f) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H y =>
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk x, rfl⟩

theorem sqMapQ_comm {X Y : Type} [Group X] [Group Y] (f : X →* Y) (φX : MulAut X)
    (φY : MulAut Y) (h : ∀ x, φY (f x) = f (φX x)) (q : X ⧸ sq X) :
    sqMapQ f (sqQuotAut φX q) = sqQuotAut φY (sqMapQ f q) := by
  induction q using QuotientGroup.induction_on with
  | H x => exact congrArg QuotientGroup.mk (h x).symm

theorem sqMapQ_range_eq_ker {A M B : Type} [Group A] [Group M] [Group B] (ι : A →* M)
    (π : M →* B) (hπ : Function.Surjective π) (hex : ι.range = π.ker) :
    (sqMapQ ι).range = (sqMapQ π).ker := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H m =>
    constructor
    · rintro ⟨x, hx⟩
      induction x using QuotientGroup.induction_on with
      | H a =>
        have hπι : π (ι a) = 1 := by
          have : ι a ∈ π.ker := hex ▸ ⟨a, rfl⟩
          exact this
        rw [MonoidHom.mem_ker, ← hx, sqMapQ_mk, sqMapQ_mk, hπι]
        rfl
    · intro hm
      have hm' : π m ∈ sq B := (QuotientGroup.eq_one_iff _).1 hm
      rw [← sq_map_eq π hπ] at hm'
      obtain ⟨s, hs, hsm⟩ := Subgroup.mem_map.1 hm'
      have hker : m * s⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hsm, mul_inv_cancel]
      rw [← hex] at hker
      obtain ⟨a, ha⟩ := hker
      refine ⟨QuotientGroup.mk a, ?_⟩
      show (QuotientGroup.mk (ι a) : M ⧸ sq M) = QuotientGroup.mk m
      rw [ha, QuotientGroup.eq]
      have : (m * s⁻¹)⁻¹ * m = s := by group
      rw [this]
      exact hs

theorem delta_four (D : DeltaAPI) {X Y Z : Type} [Group X] [Group Y] [Group Z] [Finite X]
    [Finite Y] [Finite Z] (hX : IsExpTwo X) (hY : IsExpTwo Y) (f : X →* Y) (g : Y →* Z)
    (hg : Function.Surjective g) (hfg : f.range = g.ker) (φX : MulAut X) (φY : MulAut Y)
    (φZ : MulAut Z) (hX7 : φX ^ 7 = 1) (hY7 : φY ^ 7 = 1) (h1 : ∀ x, φY (f x) = f (φX x))
    (h2 : ∀ y, g (φY y) = φZ (g y)) :
    D.delta Y φY + D.delta f.ker (restrictAut φX f.ker (ker_invariant f φX φY h1)) =
      D.delta X φX + D.delta Z φZ := by
  have hKinv : ∀ y, φY y ∈ g.ker ↔ y ∈ g.ker := ker_invariant g φY φZ fun y => (h2 y).symm
  have hA : D.delta Y φY =
      D.delta g.ker (restrictAut φY g.ker hKinv) + D.delta Z φZ :=
    D.delta_exact hY g.ker.subtype g Subtype.val_injective hg (Subgroup.range_subtype _) _ φY φZ
      hY7 (fun a => rfl) h2
  let f' : X →* g.ker := f.codRestrict g.ker fun x => by rw [← hfg]; exact ⟨x, rfl⟩
  have hf' : Function.Surjective f' := fun y => by
    have hy : (y : Y) ∈ f.range := by rw [hfg]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hker : f.ker.subtype.range = f'.ker := by
    ext x
    simp [f', MonoidHom.mem_ker]
  have hB : D.delta X φX =
      D.delta f.ker (restrictAut φX f.ker (ker_invariant f φX φY h1)) +
        D.delta g.ker (restrictAut φY g.ker hKinv) :=
    D.delta_exact hX f.ker.subtype f' Subtype.val_injective hf' hker _ φX _ hX7 (fun a => rfl)
      fun x => Subtype.ext (h1 x).symm
  omega

end CFSG.Quasithin.SzC4
