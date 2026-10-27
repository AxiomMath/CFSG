module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKLinHom
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKLinSpan
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKDefs

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix
open CFSG.Open hiding StatedSL
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Coords

variable {K Q : Subgroup G} {F : Type} [Field F]
  {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}

theorem memQ_conj_laMain (hco : CoordData K Q F α β) {a u : G} (ha : a ∈ K)
    (hu : u ∈ Q) : a * u * a⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (hco.KQ ha) u).mp hu

theorem comm_mem_Q_laMain (hco : CoordData K Q F α β) {a u : G} (ha : a ∈ K)
    (hu : u ∈ Q) : ⁅a, u⁆ ∈ Q := by
  rw [commutatorElement_def]
  exact Q.mul_mem (memQ_conj_laMain hco ha hu) (Q.inv_mem hu)

theorem coord_conj_laMain (hco : CoordData K Q F α β) {a : G} (ha : a ∈ K)
    {u v : ↥Q} (h : (v : G) = a * u * a⁻¹) (i : Fin 2) :
    coord β v i = (matOf (α ⟨a, ha⟩)).mulVec (coord β u i) :=
  hco.eq ⟨a, ha⟩ u v h i

theorem eq_of_coord_laMain (hco : CoordData K Q F α β) {u v : ↥Q}
    (h : ∀ i : Fin 2, coord β u i = coord β v i) : u = v :=
  hco.inj (Multiplicative.toAdd.injective (funext h))

theorem coord_mul_laMain (u v : ↥Q) (i : Fin 2) :
    coord β (u * v) i = coord β u i + coord β v i := by
  simp [coord, map_mul]

theorem coord_inv_laMain (u : ↥Q) (i : Fin 2) :
    coord β u⁻¹ i = -coord β u i := by
  simp [coord, map_inv]

theorem coord_one_laMain (i : Fin 2) : coord β (1 : ↥Q) i = 0 := by
  simp [coord, map_one]

theorem exists_coord_laMain (hco : CoordData K Q F α β) (y z : Fin 3 → F) :
    ∃ q : ↥Q, coord β q 0 = y ∧ coord β q 1 = z := by
  obtain ⟨q, hq⟩ := hco.surj (Multiplicative.ofAdd ![y, z])
  refine ⟨q, ?_, ?_⟩ <;> simp [coord, hq]

theorem exists_coord_ne_zero_laMain (hco : CoordData K Q F α β) {q : ↥Q} (hq : q ≠ 1) :
    ∃ i : Fin 2, coord β q i ≠ 0 := by
  by_contra h
  have h' : ∀ i : Fin 2, coord β q i = 0 := fun i => by
    by_contra hi
    exact h ⟨i, hi⟩
  exact hq (eq_of_coord_laMain hco (fun i => by rw [coord_one_laMain]; exact h' i))

theorem conj_fix_iff_laMain (hco : CoordData K Q F α β) {g : G} (hg : g ∈ K) (q : ↥Q) :
    g * (q : G) * g⁻¹ = (q : G) ↔
      ∀ i : Fin 2, (matOf (α ⟨g, hg⟩)).mulVec (coord β q i) = coord β q i := by
  constructor
  · intro h i
    exact (coord_conj_laMain hco hg (u := q) (v := q) h.symm i).symm
  · intro h
    have hmem : g * (q : G) * g⁻¹ ∈ Q := memQ_conj_laMain hco hg q.2
    have key : (⟨g * (q : G) * g⁻¹, hmem⟩ : ↥Q) = q := by
      apply eq_of_coord_laMain hco
      intro i
      rw [coord_conj_laMain hco hg (u := q) (v := ⟨g * (q : G) * g⁻¹, hmem⟩) rfl i, h i]
    exact congrArg Subtype.val key

theorem coord_comm_laMain (hco : CoordData K Q F α β) {t : G} (ht : t ∈ K) (q : ↥Q)
    (hc : ⁅t, (q : G)⁆ ∈ Q) (i : Fin 2) :
    coord β ⟨⁅t, (q : G)⁆, hc⟩ i = ((matOf (α ⟨t, ht⟩)) - 1).mulVec (coord β q i) := by
  have hX : (⟨⁅t, (q : G)⁆, hc⟩ : ↥Q) =
      (⟨t * (q : G) * t⁻¹, memQ_conj_laMain hco ht q.2⟩ : ↥Q) * q⁻¹ := by
    apply Subtype.ext
    show ⁅t, (q : G)⁆ = t * (q : G) * t⁻¹ * (q : G)⁻¹
    rw [commutatorElement_def]
  rw [hX, coord_mul_laMain, coord_inv_laMain,
    coord_conj_laMain hco ht (u := q) (v := ⟨t * (q : G) * t⁻¹, memQ_conj_laMain hco ht q.2⟩) rfl i,
    Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_add_neg]

@[expose] def fixSpace_laMain (M : Matrix (Fin 3) (Fin 3) F) : Submodule F (Fin 3 → F) where
  carrier := {x | M *ᵥ x = x}
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [Matrix.mulVec_add, hx, hy]
  zero_mem' := by simp
  smul_mem' := fun r x hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Matrix.mulVec_smul, hx]

theorem mem_fixSpace_laMain {M : Matrix (Fin 3) (Fin 3) F} {x : Fin 3 → F} :
    x ∈ fixSpace_laMain M ↔ M *ᵥ x = x := Iff.rfl

theorem mem_V_iff_laMain {V : Subgroup G} (hco : CoordData K Q F α β) {g₀ : G}
    (hg₀ : g₀ ∈ K) (hV : ∀ q ∈ Q, q ∈ V ↔ g₀ * q = q * g₀) (q : ↥Q) :
    (q : G) ∈ V ↔ ∀ i : Fin 2, coord β q i ∈ fixSpace_laMain (matOf (α ⟨g₀, hg₀⟩)) := by
  have h' : g₀ * (q : G) = (q : G) * g₀ ↔ g₀ * (q : G) * g₀⁻¹ = (q : G) :=
    mul_inv_eq_iff_eq_mul.symm
  rw [hV q q.2, h', conj_fix_iff_laMain hco hg₀ q]
  simp only [mem_fixSpace_laMain]

theorem finrank_fixSpace_laMain [Fintype F] (hco : CoordData K Q F α β) {V : Subgroup G}
    (hVQ : V ≤ Q) {ℓ : Submodule F (Fin 3 → F)}
    (hVℓ : ∀ q : ↥Q, (q : G) ∈ V ↔ ∀ i : Fin 2, coord β q i ∈ ℓ)
    (h2 : 2 ≤ Fintype.card F) (hcard : Nat.card V = Fintype.card F ^ 4) :
    Module.finrank F ℓ = 2 := by
  have hbij : Nat.card V = Nat.card (ℓ × ℓ) := by
    refine Nat.card_eq_of_bijective (fun q : V =>
      (⟨coord β (Subgroup.inclusion hVQ q) 0, (hVℓ (Subgroup.inclusion hVQ q)).mp q.2 0⟩,
       ⟨coord β (Subgroup.inclusion hVQ q) 1, (hVℓ (Subgroup.inclusion hVQ q)).mp q.2 1⟩)) ⟨?_, ?_⟩
    · intro q q' h
      have h0 := congrArg (fun p : ℓ × ℓ => (p.1 : Fin 3 → F)) h
      have h1 := congrArg (fun p : ℓ × ℓ => (p.2 : Fin 3 → F)) h
      have key := eq_of_coord_laMain hco (u := Subgroup.inclusion hVQ q)
        (v := Subgroup.inclusion hVQ q') (Fin.forall_fin_two.mpr ⟨h0, h1⟩)
      have hG : (Subgroup.inclusion hVQ q : G) = (Subgroup.inclusion hVQ q' : G) :=
        congrArg Subtype.val key
      exact Subtype.ext hG
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      obtain ⟨q, hq0, hq1⟩ := exists_coord_laMain hco x y
      have hqV : (q : G) ∈ V := (hVℓ q).mpr (Fin.forall_fin_two.mpr
        ⟨by rw [hq0]; exact hx, by rw [hq1]; exact hy⟩)
      refine ⟨⟨q, hqV⟩, ?_⟩
      exact Prod.ext (Subtype.ext hq0) (Subtype.ext hq1)
  rw [Nat.card_prod, Module.natCard_eq_pow_finrank (K := F) (V := ℓ),
    Nat.card_eq_fintype_card (α := F), hcard] at hbij
  rw [← pow_add] at hbij
  have h4 := Nat.pow_right_injective h2 hbij
  omega

end Coords

theorem matOf_equiv_laMain {F : Type} [Field F] (A : SpecialLinearGroup (Fin 3) F) :
    matOf (specialLinearGroupEquivStatedSL 3 F A) = (A : Matrix (Fin 3) (Fin 3) F) :=
  specialLinearGroupEquivStatedSL_coe 3 F A

theorem matOf_mul_laMain {F : Type} [Field F] (x y : ↥(StatedSL 3 F)) :
    matOf (x * y) = matOf x * matOf y :=
  Units.val_mul _ _

theorem coe_symm_laMain {F : Type} [Field F] (s : ↥(StatedSL 3 F)) :
    ((specialLinearGroupEquivStatedSL 3 F).symm s : Matrix (Fin 3) (Fin 3) F) = matOf s := by
  have h := specialLinearGroupEquivStatedSL_coe 3 F ((specialLinearGroupEquivStatedSL 3 F).symm s)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem mem_stabMap_iff_laMain {F : Type} [Field F] (w : Fin 3 → F)
    (s : ↥(StatedSL 3 F)) :
    s ∈ (stabVec w).map (specialLinearGroupEquivStatedSL 3 F :
      SpecialLinearGroup (Fin 3) F →* ↥(StatedSL 3 F)) ↔ (matOf s).mulVec w = w := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    have h := mem_stabVec.mp hg
    exact (matOf_equiv_laMain g).symm ▸ h
  · intro hs
    refine ⟨(specialLinearGroupEquivStatedSL 3 F).symm s, ?_, ?_⟩
    · exact mem_stabVec.mpr (by rw [coe_symm_laMain]; exact hs)
    · exact (specialLinearGroupEquivStatedSL 3 F).apply_symm_apply s

theorem exists_w0_laMain {F : Type} [Field F] (T : Matrix (Fin 3) (Fin 3) F)
    (ℓ : Submodule F (Fin 3 → F)) (hℓ : Module.finrank F ℓ = 2) (h2 : (2 : F) = 0)
    (hTℓ : ∀ x ∈ ℓ, T *ᵥ x ∈ ℓ) (hT2 : ∀ x ∈ ℓ, T *ᵥ (T *ᵥ x) = x)
    (hne : ∃ x ∈ ℓ, (T - 1) *ᵥ x ≠ 0) :
    ∃ w₀ : Fin 3 → F, w₀ ≠ 0 ∧ ∀ x ∈ ℓ, ∃ c : F, (T - 1) *ᵥ x = c • w₀ := by
  have hNℓ : ∀ x ∈ ℓ, (T - 1) *ᵥ x ∈ ℓ := fun x hx => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact ℓ.sub_mem (hTℓ x hx) hx
  have hNN : ∀ x ∈ ℓ, (T - 1) *ᵥ ((T - 1) *ᵥ x) = 0 := fun x hx => by
    have h1 : (T - 1) *ᵥ x = T *ᵥ x - x := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    have h3 : (T - 1) *ᵥ (T *ᵥ x) = x - T *ᵥ x := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hT2 x hx]
    rw [h1, Matrix.mulVec_sub, h3, h1]
    funext i
    simp only [Pi.sub_apply, Pi.zero_apply]
    linear_combination (x i - (T *ᵥ x) i) * h2
  let f : ℓ →ₗ[F] ℓ := (Matrix.toLin' (T - 1)).restrict hNℓ
  have hf : ∀ x : ℓ, ((f x : ℓ) : Fin 3 → F) = (T - 1) *ᵥ (x : Fin 3 → F) := fun x => rfl
  have hff : ∀ x : ℓ, f (f x) = 0 := fun x => Subtype.ext (by
    rw [hf, hf]
    exact hNN x x.2)
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℓ, f x₁ ≠ 0 := by
    obtain ⟨x, hx, hNx⟩ := hne
    refine ⟨⟨x, hx⟩, fun h => hNx ?_⟩
    have h' := congrArg Subtype.val h
    rw [hf] at h'
    exact h'
  have hrange_le : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨y, rfl⟩
    exact LinearMap.mem_ker.mpr (hff y)
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hle := Submodule.finrank_mono hrange_le
  have hpos : 0 < Module.finrank F (LinearMap.range f) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨f x₁, LinearMap.mem_range_self f x₁⟩, fun h => hx₁ (congrArg Subtype.val h)⟩
  have hr1 : Module.finrank F (LinearMap.range f) = 1 := by omega
  refine ⟨(T - 1) *ᵥ (x₁ : Fin 3 → F), fun h => hx₁ (Subtype.ext ?_), fun x hx => ?_⟩
  · rw [hf]
    exact h
  · have hv : (⟨f x₁, LinearMap.mem_range_self f x₁⟩ : LinearMap.range f) ≠ 0 :=
      fun h => hx₁ (congrArg Subtype.val h)
    have hiff := finrank_eq_one_iff_of_nonzero' (K := F) (V := LinearMap.range f) _ hv
    obtain ⟨c, hc⟩ := hiff.mp hr1 ⟨f ⟨x, hx⟩, LinearMap.mem_range_self f ⟨x, hx⟩⟩
    exact ⟨c, (congrArg (fun z : LinearMap.range f => ((z : ℓ) : Fin 3 → F)) hc).symm⟩

theorem perfect_image_laMain [Finite G] {K : Subgroup G} {F : Type} [Field F]
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) {H : Subgroup G} (hHK : H ≤ K)
    {S₀ : Subgroup ↥(StatedSL 3 F)} (hS₀ : ⁅S₀, S₀⁆ = S₀)
    (hH : ∀ k : ↥K, (k : G) ∈ H ↔ α k ∈ S₀) :
    (∀ b ∈ perfectCore H, ∃ hb : b ∈ K, α ⟨b, hb⟩ ∈ S₀) ∧
      (∀ s ∈ S₀, ∃ b ∈ perfectCore H, ∃ hb : b ∈ K, α ⟨b, hb⟩ = s) := by
  haveI : Finite ↥(StatedSL 3 F) := Finite.of_surjective α hα
  set Hk : Subgroup ↥K := H.subgroupOf K with hHk
  have hHkα : Hk.map α = S₀ := by
    ext s
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (hH k).mp (Subgroup.mem_subgroupOf.mp hk)
    · intro hs
      obtain ⟨k, rfl⟩ := hα s
      exact ⟨k, Subgroup.mem_subgroupOf.mpr ((hH k).mpr hs), rfl⟩
  have hHkK : Hk.map K.subtype = H := by
    rw [hHk, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHK]
  have hPk : (perfectCore Hk).map K.subtype = perfectCore H := by
    rw [map_perfectCore K.subtype Hk, hHkK]
  have hPkα : (perfectCore Hk).map α = S₀ := by
    rw [map_perfectCore α Hk, hHkα, perfectCore_eq_self_of_perfect hS₀]
  constructor
  · intro b hb
    have hb' : b ∈ (perfectCore Hk).map K.subtype := by
      rw [hPk]
      exact hb
    obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb'
    have hbK : b ∈ K := by
      rw [← hcb]
      exact c.2
    refine ⟨hbK, ?_⟩
    have hce : (⟨b, hbK⟩ : ↥K) = c := Subtype.ext hcb.symm
    rw [hce, ← hPkα]
    exact Subgroup.mem_map_of_mem α hc
  · intro s hs
    have hs' : s ∈ (perfectCore Hk).map α := by
      rw [hPkα]
      exact hs
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hs'
    refine ⟨(c : G), ?_, c.2, rfl⟩
    rw [← hPk]
    exact Subgroup.mem_map_of_mem K.subtype hc

theorem exists_rho_laMain {X : Type} [Group X] {F : Type} [Field F] [Fintype F]
    (h2 : (2 : F) = 0) {w₀ : Fin 3 → F} (hw₀ : w₀ ≠ 0) (φ : X →* ↥(StatedSL 3 F))
    (hφ : ∀ x : X, (matOf (φ x)).mulVec w₀ = w₀)
    (hran : ∀ s : ↥(StatedSL 3 F), (matOf s).mulVec w₀ = w₀ → ∃ x : X, φ x = s)
    (hsq : ∀ x : X, φ x * φ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    ∃ ρ : X →* ↥(StatedSL 2 F), Function.Surjective ρ ∧ IsPGroup 2 ρ.ker := by
  obtain ⟨ρ₀, hρ₀surj, hρ₀ker⟩ := exists_hom_stabVec h2 hw₀
  have hmem : ∀ x : X, (specialLinearGroupEquivStatedSL 3 F).symm (φ x) ∈ stabVec w₀ :=
    fun x => by
      rw [mem_stabVec, coe_symm_laMain]
      exact hφ x
  let Φ : X →* ↥(stabVec w₀) :=
    { toFun := fun x => ⟨(specialLinearGroupEquivStatedSL 3 F).symm (φ x), hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hΦsurj : ∀ g : ↥(stabVec w₀), ∃ x : X, Φ x = g := by
    intro g
    have hg : (matOf ((specialLinearGroupEquivStatedSL 3 F) (g : SpecialLinearGroup (Fin 3) F))).mulVec
        w₀ = w₀ := by
      rw [matOf_equiv_laMain]
      exact mem_stabVec.mp g.2
    obtain ⟨x, hx⟩ := hran _ hg
    refine ⟨x, Subtype.ext ?_⟩
    show (specialLinearGroupEquivStatedSL 3 F).symm (φ x) = (g : SpecialLinearGroup (Fin 3) F)
    rw [hx, MulEquiv.symm_apply_apply]
  refine ⟨(specialLinearGroupEquivStatedSL 2 F).toMonoidHom.comp (ρ₀.comp Φ), ?_, ?_⟩
  · intro s
    obtain ⟨g, hg⟩ := hρ₀surj ((specialLinearGroupEquivStatedSL 2 F).symm s)
    obtain ⟨x, hx⟩ := hΦsurj g
    refine ⟨x, ?_⟩
    show (specialLinearGroupEquivStatedSL 2 F) (ρ₀ (Φ x)) = s
    rw [hx, hg, MulEquiv.apply_symm_apply]
  · rintro ⟨x, hx⟩
    have hx' : (specialLinearGroupEquivStatedSL 2 F) (ρ₀ (Φ x)) = 1 := hx
    have h1 : ρ₀ (Φ x) = 1 := by
      apply (specialLinearGroupEquivStatedSL 2 F).injective
      rw [hx', map_one]
    have h2' : Φ x * Φ x = 1 := hρ₀ker (Φ x) (MonoidHom.mem_ker.mpr h1)
    have hΦx : (specialLinearGroupEquivStatedSL 3 F)
        ((Φ x : ↥(stabVec w₀)) : SpecialLinearGroup (Fin 3) F) = φ x := by
      show (specialLinearGroupEquivStatedSL 3 F) ((specialLinearGroupEquivStatedSL 3 F).symm (φ x))
        = φ x
      exact (specialLinearGroupEquivStatedSL 3 F).apply_symm_apply (φ x)
    have h3 : ((Φ x : ↥(stabVec w₀)) : SpecialLinearGroup (Fin 3) F) *
        ((Φ x : ↥(stabVec w₀)) : SpecialLinearGroup (Fin 3) F) = 1 := by
      have := congrArg Subtype.val h2'
      simpa using this
    have hφsq : φ x * φ x = 1 := by
      rw [← hΦx, ← map_mul, h3, map_one]
    obtain ⟨k, hk⟩ := hsq x hφsq
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hk


section Commutator

variable {K Q : Subgroup G} {F : Type} [Field F]
  {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}

theorem commutator_eq_laMain [Fintype F] {V P : Subgroup G}
    (hco : CoordData K Q F α β) (hVQ : V ≤ Q) (hPK : P ≤ K)
    {ℓ : Submodule F (Fin 3 → F)} (hℓ2 : Module.finrank F ℓ = 2)
    (hVℓ : ∀ q : ↥Q, (q : G) ∈ V ↔ ∀ i : Fin 2, coord β q i ∈ ℓ)
    {w₀ : Fin 3 → F} (hw₀ : w₀ ≠ 0) (h4 : 4 ≤ Fintype.card F)
    (hP : ∀ g ∈ stabVec w₀, ∃ b ∈ P, ∃ hb : b ∈ K,
      matOf (α ⟨b, hb⟩) = (g : Matrix (Fin 3) (Fin 3) F)) :
    ⁅V, P⁆ = Q := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv p hp
    rw [commutatorElement_def]
    have e : v * p * v⁻¹ * p⁻¹ = v * (p * v⁻¹ * p⁻¹) := by group
    rw [e]
    exact Q.mul_mem (hVQ hv) (memQ_conj_laMain hco (hPK hp) (Q.inv_mem (hVQ hv)))
  · have hWc : ∀ b ∈ P, ∀ v ∈ V, ⁅b, v⁆ ∈ ⁅V, P⁆ := fun b hb v hv => by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hb hv
    have hg0 : ∀ y ∈ {y : Fin 3 → F | ∃ g ∈ stabVec w₀, ∃ x ∈ ℓ,
        y = (g : Matrix (Fin 3) (Fin 3) F).mulVec x - x},
        ∃ q : ↥Q, (q : G) ∈ ⁅V, P⁆ ∧ coord β q 0 = y ∧ coord β q 1 = 0 := by
      rintro y ⟨g, hg, x, hx, rfl⟩
      obtain ⟨b, hbP, hbK, hbM⟩ := hP g hg
      obtain ⟨v, hv0, hv1⟩ := exists_coord_laMain hco x 0
      have hvV : (v : G) ∈ V := (hVℓ v).mpr (Fin.forall_fin_two.mpr
        ⟨by rw [hv0]; exact hx, by rw [hv1]; exact ℓ.zero_mem⟩)
      have hq : ⁅b, (v : G)⁆ ∈ Q := comm_mem_Q_laMain hco hbK v.2
      have hc := coord_comm_laMain hco hbK v hq
      rw [hbM] at hc
      refine ⟨⟨⁅b, (v : G)⁆, hq⟩, hWc b hbP v hvV, ?_, ?_⟩
      · rw [hc 0, Matrix.sub_mulVec, Matrix.one_mulVec, hv0]
      · rw [hc 1, Matrix.sub_mulVec, Matrix.one_mulVec, hv1, Matrix.mulVec_zero, sub_self]
    have hg1 : ∀ y ∈ {y : Fin 3 → F | ∃ g ∈ stabVec w₀, ∃ x ∈ ℓ,
        y = (g : Matrix (Fin 3) (Fin 3) F).mulVec x - x},
        ∃ q : ↥Q, (q : G) ∈ ⁅V, P⁆ ∧ coord β q 0 = 0 ∧ coord β q 1 = y := by
      rintro y ⟨g, hg, x, hx, rfl⟩
      obtain ⟨b, hbP, hbK, hbM⟩ := hP g hg
      obtain ⟨v, hv0, hv1⟩ := exists_coord_laMain hco 0 x
      have hvV : (v : G) ∈ V := (hVℓ v).mpr (Fin.forall_fin_two.mpr
        ⟨by rw [hv0]; exact ℓ.zero_mem, by rw [hv1]; exact hx⟩)
      have hq : ⁅b, (v : G)⁆ ∈ Q := comm_mem_Q_laMain hco hbK v.2
      have hc := coord_comm_laMain hco hbK v hq
      rw [hbM] at hc
      refine ⟨⟨⁅b, (v : G)⁆, hq⟩, hWc b hbP v hvV, ?_, ?_⟩
      · rw [hc 0, Matrix.sub_mulVec, Matrix.one_mulVec, hv0, Matrix.mulVec_zero, sub_self]
      · rw [hc 1, Matrix.sub_mulVec, Matrix.one_mulVec, hv1]
    have hspan := span_stabVec h4 hw₀ ℓ hℓ2
    let D0 : AddSubgroup (Fin 3 → F) :=
      { carrier := {y | ∃ q : ↥Q, (q : G) ∈ ⁅V, P⁆ ∧ coord β q 0 = y ∧ coord β q 1 = 0}
        add_mem' := fun {y₁ y₂} h₁ h₂ => by
          obtain ⟨q₁, hq₁, h₁0, h₁1⟩ := h₁
          obtain ⟨q₂, hq₂, h₂0, h₂1⟩ := h₂
          refine ⟨q₁ * q₂, Subgroup.mul_mem _ hq₁ hq₂, ?_, ?_⟩
          · rw [coord_mul_laMain, h₁0, h₂0]
          · rw [coord_mul_laMain, h₁1, h₂1, add_zero]
        zero_mem' := ⟨1, Subgroup.one_mem _, coord_one_laMain 0, coord_one_laMain 1⟩
        neg_mem' := fun {y} h => by
          obtain ⟨q, hq, h0, h1⟩ := h
          refine ⟨q⁻¹, Subgroup.inv_mem _ hq, ?_, ?_⟩
          · rw [coord_inv_laMain, h0]
          · rw [coord_inv_laMain, h1, neg_zero] }
    let D1 : AddSubgroup (Fin 3 → F) :=
      { carrier := {z | ∃ q : ↥Q, (q : G) ∈ ⁅V, P⁆ ∧ coord β q 0 = 0 ∧ coord β q 1 = z}
        add_mem' := fun {z₁ z₂} h₁ h₂ => by
          obtain ⟨q₁, hq₁, h₁0, h₁1⟩ := h₁
          obtain ⟨q₂, hq₂, h₂0, h₂1⟩ := h₂
          refine ⟨q₁ * q₂, Subgroup.mul_mem _ hq₁ hq₂, ?_, ?_⟩
          · rw [coord_mul_laMain, h₁0, h₂0, add_zero]
          · rw [coord_mul_laMain, h₁1, h₂1]
        zero_mem' := ⟨1, Subgroup.one_mem _, coord_one_laMain 0, coord_one_laMain 1⟩
        neg_mem' := fun {z} h => by
          obtain ⟨q, hq, h0, h1⟩ := h
          refine ⟨q⁻¹, Subgroup.inv_mem _ hq, ?_, ?_⟩
          · rw [coord_inv_laMain, h0, neg_zero]
          · rw [coord_inv_laMain, h1] }
    have hD0 : ∀ y : Fin 3 → F,
        ∃ q : ↥Q, (q : G) ∈ ⁅V, P⁆ ∧ coord β q 0 = y ∧ coord β q 1 = 0 := by
      intro y
      have hle : (⊤ : AddSubgroup (Fin 3 → F)) ≤ D0 := by
        rw [← hspan]
        exact (AddSubgroup.closure_le D0).mpr hg0
      exact hle (AddSubgroup.mem_top y)
    have hD1 : ∀ z : Fin 3 → F,
        ∃ q : ↥Q, (q : G) ∈ ⁅V, P⁆ ∧ coord β q 0 = 0 ∧ coord β q 1 = z := by
      intro z
      have hle : (⊤ : AddSubgroup (Fin 3 → F)) ≤ D1 := by
        rw [← hspan]
        exact (AddSubgroup.closure_le D1).mpr hg1
      exact hle (AddSubgroup.mem_top z)
    intro q hq
    obtain ⟨q₀, h₀W, h₀0, h₀1⟩ := hD0 (coord β ⟨q, hq⟩ 0)
    obtain ⟨q₁, h₁W, h₁0, h₁1⟩ := hD1 (coord β ⟨q, hq⟩ 1)
    have e0 : coord β (q₀ * q₁) 0 = coord β ⟨q, hq⟩ 0 := by
      rw [coord_mul_laMain, h₀0, h₁0, add_zero]
    have e1 : coord β (q₀ * q₁) 1 = coord β ⟨q, hq⟩ 1 := by
      rw [coord_mul_laMain, h₀1, h₁1, zero_add]
    have key : q₀ * q₁ = ⟨q, hq⟩ := eq_of_coord_laMain hco (Fin.forall_fin_two.mpr ⟨e0, e1⟩)
    have hmul : ((q₀ * q₁ : ↥Q) : G) ∈ ⁅V, P⁆ := Subgroup.mul_mem _ h₀W h₁W
    rw [key] at hmul
    exact hmul

end Commutator

end CFSG.Quasithin.H13.Ch4.CentK
