module

public import CFSG.Quasithin.Background.SmithC27RCaseIIStar
public import CFSG.Quasithin.Background.SmithC27RCaseIIPerm
public import CFSG.Quasithin.Background.SmithC27RCaseIIRad

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

section Transport

variable {Γ₀ Γ : Type} [Group Γ₀] [Group Γ] {X : Subgroup Γ₀} (ι : ↥X ≃* Γ)

@[expose] def trS (A : Subgroup Γ₀) : Subgroup Γ := (A.subgroupOf X).map ι.toMonoidHom

@[expose] def pullS (T : Subgroup Γ) : Subgroup Γ₀ := (T.map ι.symm.toMonoidHom).map X.subtype

theorem mem_trS_iff {A : Subgroup Γ₀} (g : ↥X) : ι g ∈ trS ι A ↔ (g : Γ₀) ∈ A := by
  unfold trS
  constructor
  · rintro ⟨g', hg', hgg'⟩
    rw [← ι.injective hgg']
    exact hg'
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem trS_mono {A B : Subgroup Γ₀} (h : A ≤ B) : trS ι A ≤ trS ι B :=
  Subgroup.map_mono fun _ hx => h hx

theorem pullS_le (T : Subgroup Γ) : pullS ι T ≤ X := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_pullS_iff {T : Subgroup Γ} (x : ↥X) : (x : Γ₀) ∈ pullS ι T ↔ ι x ∈ T := by
  constructor
  · rintro ⟨y, ⟨σ, hσ, rfl⟩, hy⟩
    have hy' : ι.symm σ = x := Subtype.ext hy
    rw [← hy', MulEquiv.apply_symm_apply]
    exact hσ
  · intro hx
    exact ⟨x, ⟨ι x, hx, by simp⟩, rfl⟩

theorem trS_pullS (T : Subgroup Γ) : trS ι (pullS ι T) = T := by
  ext σ
  obtain ⟨g, rfl⟩ := ι.surjective σ
  rw [mem_trS_iff, mem_pullS_iff]

theorem trS_self : trS ι X = ⊤ := by
  ext σ
  obtain ⟨g, rfl⟩ := ι.surjective σ
  rw [mem_trS_iff]
  exact ⟨fun _ => Subgroup.mem_top _, fun _ => g.2⟩

theorem trS_normalizer {A : Subgroup Γ₀} (hA : A ≤ X) :
    trS ι (Subgroup.normalizer (A : Set Γ₀)) = Subgroup.normalizer (trS ι A : Set Γ) := by
  ext σ
  obtain ⟨g, rfl⟩ := ι.surjective σ
  rw [mem_trS_iff, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg τ
    obtain ⟨t, rfl⟩ := ι.surjective τ
    rw [← map_mul, ← map_inv, ← map_mul, mem_trS_iff, mem_trS_iff]
    exact hg (t : Γ₀)
  · intro hg x
    constructor
    · intro hx
      have hxX : x ∈ X := hA hx
      have := (hg (ι ⟨x, hxX⟩)).1 ((mem_trS_iff ι _).2 hx)
      rw [← map_mul, ← map_inv, ← map_mul, mem_trS_iff] at this
      exact this
    · intro hx
      have hxX : x ∈ X := by
        have h1 := X.mul_mem (X.mul_mem (X.inv_mem g.2) (hA hx)) g.2
        simpa [mul_assoc] using h1
      have hgx : (g : Γ₀) * x * (g : Γ₀)⁻¹ ∈ A := hx
      have := (hg (ι ⟨x, hxX⟩)).2 (by
        rw [← map_mul, ← map_inv, ← map_mul, mem_trS_iff]
        exact hgx)
      exact (mem_trS_iff ι _).1 this

theorem isPGroup_trS {A : Subgroup Γ₀} (hA : IsPGroup 2 A) : IsPGroup 2 (trS ι A) := by
  have h1 : IsPGroup 2 (A.subgroupOf X) := by
    intro x
    obtain ⟨k, hk⟩ := hA ⟨((x : ↥X) : Γ₀), x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  exact h1.map _

theorem isSylowTwoOf_trS_iff {S Y : Subgroup Γ₀} (hSY : S ≤ Y) (hY : Y ≤ X) :
    IsSylowTwoOf S Y ↔ IsSylowTwoOf (trS ι S) (trS ι Y) := by
  constructor
  · intro h
    exact isSylowTwoOf_map' ι.toMonoidHom (isSylowTwoOf_subgroupOf h hY)
  · intro h
    have h1 := isSylowTwoOf_map' ι.symm.toMonoidHom h
    have hmap : ∀ A : Subgroup Γ₀, (trS ι A).map ι.symm.toMonoidHom = A.subgroupOf X := by
      intro A
      unfold trS
      rw [Subgroup.map_map]
      have hcomp : ι.symm.toMonoidHom.comp ι.toMonoidHom = MonoidHom.id _ :=
        MonoidHom.ext fun g => ι.symm_apply_apply g
      rw [hcomp, Subgroup.map_id]
    rw [hmap, hmap] at h1
    have h2 := isSylowTwoOf_map' X.subtype h1
    rwa [Subgroup.map_subgroupOf_eq_of_le (hSY.trans hY),
      Subgroup.map_subgroupOf_eq_of_le hY] at h2

end Transport

variable {G : Type} [Group G] [Finite G] {R K V : Subgroup G} {n : ℕ}

namespace CaseIICtx

variable (C : CaseIICtx R K V n)

omit [Finite G] in
theorem bar_eq_trS (Y : Subgroup G) : C.bar Y = trS C.ι (autOn Y V) := rfl

omit [Finite G] in
theorem isPGroup_bar_R (hs : StarHyp R K V) : IsPGroup 2 (C.bar R) :=
  isPGroup_trS C.ι (isPGroup_autOn hs.pgroup)

theorem isRadSig_bar_R (hR : IsTwoRadicalIn (K ⊔ R) R) (hs : StarHyp R K V) :
    IsRadSig (C.bar R) := by
  intro Y hY hN
  have hY'X := pullS_le C.ι Y
  have hY' : IsPGroup 2 (pullS C.ι Y) := (hY.map C.ι.symm.toMonoidHom).map _
  have hRX : autOn R V ≤ autOn (K ⊔ R) V := autOn_mono' le_sup_right
  have key : autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V)) ≤
      Subgroup.normalizer (pullS C.ι Y : Set (MulAut ↥V)) := by
    rintro x ⟨hxX, hxN⟩
    have h1 : C.ι ⟨x, hxX⟩ ∈ Subgroup.normalizer (C.bar R : Set (Perm (Fin n))) := by
      rw [C.bar_eq_trS, ← trS_normalizer C.ι hRX, mem_trS_iff]
      exact hxN
    have h2 := hN h1
    rw [← trS_pullS C.ι Y, ← trS_normalizer C.ι hY'X, mem_trS_iff] at h2
    exact h2
  have h3 := le_autOn_R_of_le_normalizer hR hs hY'X hY' key
  rw [← trS_pullS C.ι Y]
  exact trS_mono C.ι h3

omit [Finite G] in
theorem not_bar_R_le_alt (hs : StarHyp R K V) (hn : 2 ≤ n) :
    ¬ C.bar R ≤ alternatingGroup (Fin n) := by
  intro hle
  have hRX : autOn R V ≤ autOn (K ⊔ R) V := autOn_mono' le_sup_right
  have hRK : autOn R V ≤ autOn K V := by
    intro x hx
    have h1 : C.ι ⟨x, hRX hx⟩ ∈ C.bar R := (mem_trS_iff C.ι ⟨x, hRX hx⟩).2 hx
    exact (C.mem_K ⟨x, hRX hx⟩).2 (hle h1)
  have hX : autOn (K ⊔ R) V = autOn K V := by
    rw [hs.autOn_sup]
    exact sup_eq_left.2 hRK
  obtain ⟨x, hx⟩ := C.ι.surjective (swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)
  have h1 : (x : MulAut ↥V) ∈ autOn K V := by
    rw [← hX]
    exact x.2
  have h2 := (C.mem_K x).1 h1
  rw [hx, mem_alternatingGroup, sign_swap (by simp [Fin.ext_iff])] at h2
  exact absurd h2 (by decide)

omit [Finite G] in
theorem exists_sylow_star_of_bar {T : Subgroup (Perm (Fin n))} (hT : IsSylowTwoOf T ⊤)
    (hTN : T ≤ Subgroup.normalizer (C.bar R : Set (Perm (Fin n)))) :
    ∃ T' : Subgroup (MulAut ↥V), IsSylowTwoOf T' (autOn (K ⊔ R) V) ∧
      T' ≤ Subgroup.normalizer (autOn R V : Set (MulAut ↥V)) := by
  have hRX : autOn R V ≤ autOn (K ⊔ R) V := autOn_mono' le_sup_right
  refine ⟨pullS C.ι T, ?_, ?_⟩
  · rw [isSylowTwoOf_trS_iff C.ι (pullS_le C.ι T) le_rfl, trS_pullS, trS_self]
    exact hT
  · intro x hx
    have hxX := pullS_le C.ι T hx
    have h1 : C.ι ⟨x, hxX⟩ ∈ T := (mem_pullS_iff C.ι ⟨x, hxX⟩).1 hx
    have h2 := hTN h1
    rw [C.bar_eq_trS, ← trS_normalizer C.ι hRX] at h2
    exact (mem_trS_iff C.ι ⟨x, hxX⟩).1 h2

omit [Finite G] in
include C in
theorem self_normalizing_K (hn : n = 6 ∨ n = 8) :
    ∀ S : Subgroup (MulAut ↥V), IsSylowTwoOf S (autOn K V) →
      autOn K V ⊓ Subgroup.normalizer (S : Set (MulAut ↥V)) ≤ S := by
  intro S hS
  have hKX : autOn K V ≤ autOn (K ⊔ R) V := autOn_mono' le_sup_left
  have hSX : S ≤ autOn (K ⊔ R) V := hS.1.trans hKX
  have h1 : IsSylowTwoOf (trS C.ι S) (alternatingGroup (Fin n)) := by
    rw [← C.bar_K, C.bar_eq_trS]
    exact (isSylowTwoOf_trS_iff C.ι hS.1 hKX).1 hS
  have h2 := inf_normalizer_le_of_sylow_alt hn h1
  rintro x ⟨hxK, hxN⟩
  have hxX := hKX hxK
  have h3 : C.ι ⟨x, hxX⟩ ∈ alternatingGroup (Fin n) := (C.mem_K ⟨x, hxX⟩).1 hxK
  have h4 : C.ι ⟨x, hxX⟩ ∈ Subgroup.normalizer (trS C.ι S : Set (Perm (Fin n))) := by
    rw [← trS_normalizer C.ι hSX, mem_trS_iff]
    exact hxN
  exact (mem_trS_iff C.ι ⟨x, hxX⟩).1 (h2 ⟨h3, h4⟩)

omit [Finite G] in
include C in
theorem nonempty_equivK : Nonempty (↥(autOn K V) ≃* ↥(alternatingGroup (Fin n))) := by
  have hKX : autOn K V ≤ autOn (K ⊔ R) V := autOn_mono' le_sup_left
  have e₁ : ↥(autOn K V) ≃* ↥((autOn K V).subgroupOf (autOn (K ⊔ R) V)) :=
    (Subgroup.subgroupOfEquivOfLe hKX).symm
  have e₂ := Subgroup.equivMapOfInjective ((autOn K V).subgroupOf (autOn (K ⊔ R) V))
    C.ι.toMonoidHom C.ι.injective
  have h3 : ((autOn K V).subgroupOf (autOn (K ⊔ R) V)).map C.ι.toMonoidHom =
      alternatingGroup (Fin n) := C.bar_K
  exact ⟨(e₁.trans e₂).trans (MulEquiv.subgroupCongr h3)⟩

end CaseIICtx

end CFSG.Quasithin.SmithC27
