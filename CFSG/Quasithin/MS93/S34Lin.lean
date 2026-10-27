module

public import CFSG.Quasithin.MS93.S34Ext
public import CFSG.Quasithin.MS93.PUBase

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

variable {G : Type} [Group G]

section CoordMap

variable {V Z : Subgroup G} {ι : Type} {F : Type} [Field F]
  {β : ↥V →* Multiplicative (Fin 1 → ι → F)}

theorem mul_inv_mem_of_coord_eq (hβker : β.ker = Z.subgroupOf V) {u u' : ↥V}
    (h : Multiplicative.toAdd (β u) 0 = Multiplicative.toAdd (β u') 0) :
    ((u : G)⁻¹ * u') ∈ Z := by
  have hβ : β u = β u' := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [Subsingleton.elim i 0, h]
  have hk : u⁻¹ * u' ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβ, inv_mul_cancel]
  rw [hβker, Subgroup.mem_subgroupOf] at hk
  simpa using hk

theorem exists_isCoordAct (hβ : Function.Surjective β) (hβker : β.ker = Z.subgroupOf V)
    {g : G} (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    ∃ f : (ι → F) →+ (ι → F), IsCoordAct β g f := by
  choose s hs using exists_coord_eq hβ
  let c : ↥V → ↥V := fun u => ⟨g * u * g⁻¹, conj_mem_of_mem_normalizer hgV u⟩
  have hwd : ∀ u u' : ↥V, Multiplicative.toAdd (β u) 0 = Multiplicative.toAdd (β u') 0 →
      Multiplicative.toAdd (β (c u)) 0 = Multiplicative.toAdd (β (c u')) 0 := by
    intro u u' huu'
    have hz := mul_inv_mem_of_coord_eq hβker huu'
    have hz' : g * ((u : G)⁻¹ * u') * g⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 hgZ _).1 hz
    have hk : (c u)⁻¹ * c u' ∈ β.ker := by
      rw [hβker, Subgroup.mem_subgroupOf]
      convert hz' using 1
      simp only [c, Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev]
      group
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
    rw [hk]
  let f : (ι → F) → (ι → F) := fun x => Multiplicative.toAdd (β (c (s x))) 0
  have hf : ∀ u : ↥V, f (Multiplicative.toAdd (β u) 0) = Multiplicative.toAdd (β (c u)) 0 :=
    fun u => hwd _ _ (hs _)
  refine ⟨{ toFun := f, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · have := hf 1
    simp only [map_one, toAdd_one, Pi.zero_apply] at this
    have hc1 : c 1 = 1 := Subtype.ext (by simp [c])
    rw [this, hc1, map_one]
    rfl
  · intro x y
    have h1 : Multiplicative.toAdd (β (s x * s y)) 0 = x + y := by
      rw [map_mul, toAdd_mul, Pi.add_apply, hs, hs]
    rw [← h1, hf]
    have : c (s x * s y) = c (s x) * c (s y) :=
      Subtype.ext (by simp only [c, Subgroup.coe_mul]; group)
    rw [this, map_mul, toAdd_mul, Pi.add_apply]
  · intro u v huv
    have : v = c u := Subtype.ext huv
    rw [this]
    exact (hf u).symm

theorem exists_gl_of_isCoordAct [Fintype ι] [DecidableEq ι] (hβ : Function.Surjective β) {g : G}
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) {A B : Matrix ι ι F}
    (hA : IsCoordAct β g A.mulVec) (hB : IsCoordAct β g⁻¹ B.mulVec) :
    ∃ γ : GL ι F, IsCoordAct β g (γ : Matrix ι ι F).mulVec := by
  have hginv : g⁻¹ ∈ Subgroup.normalizer (V : Set G) := inv_mem hgV
  have h1 : IsCoordAct β 1 (A * B).mulVec := by
    have := hA.mul hginv hB
    rw [mul_inv_cancel] at this
    exact this.congr fun x => by simp [Matrix.mulVec_mulVec]
  have h2 : IsCoordAct β 1 (B * A).mulVec := by
    have := hB.mul hgV hA
    rw [inv_mul_cancel] at this
    exact this.congr fun x => by simp [Matrix.mulVec_mulVec]
  have hAB : A * B = 1 := IsCoordAct.matrix_eq hβ (one_mem _) h1 isCoordAct_one_mulVec
  have hBA : B * A = 1 := IsCoordAct.matrix_eq hβ (one_mem _) h2 isCoordAct_one_mulVec
  exact ⟨⟨A, B, hAB, hBA⟩, hA⟩

theorem exists_matrix_of_linear [Fintype ι] [DecidableEq ι] {g : G}
    {f : (ι → F) →+ (ι → F)} (hf : IsCoordAct β g f) (hlin : ∀ (c : F) x, f (c • x) = c • f x) :
    ∃ A : Matrix ι ι F, IsCoordAct β g A.mulVec := by
  let fl : (ι → F) →ₗ[F] (ι → F) :=
    { toFun := f, map_add' := map_add f, map_smul' := hlin }
  exact ⟨LinearMap.toMatrix' fl, hf.congr fun x => by
    rw [LinearMap.toMatrix'_mulVec]
    rfl⟩

theorem exists_gl_of_card_two [Fintype ι] [DecidableEq ι] [Fintype F]
    (hF : Fintype.card F = 2) (hβ : Function.Surjective β) (hβker : β.ker = Z.subgroupOf V)
    {g : G} (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    ∃ γ : GL ι F, IsCoordAct β g (γ : Matrix ι ι F).mulVec := by
  classical
  have hc : ∀ c : F, c = 0 ∨ c = 1 := by
    intro c
    by_contra hne
    push Not at hne
    have h3 : 3 ≤ Fintype.card F := by
      have : ({0, 1, c} : Finset F).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hne.1.symm, zero_ne_one]),
          Finset.card_pair (Ne.symm hne.2)]
      rw [← this]
      exact Finset.card_le_univ _
    omega
  have hlin : ∀ (f : (ι → F) →+ (ι → F)) (c : F) x, f (c • x) = c • f x := by
    intro f c x
    rcases hc c with rfl | rfl
    · simp
    · simp
  obtain ⟨f, hf⟩ := exists_isCoordAct hβ hβker hgV hgZ
  obtain ⟨f', hf'⟩ := exists_isCoordAct hβ hβker (inv_mem hgV) (inv_mem hgZ)
  obtain ⟨A, hA⟩ := exists_matrix_of_linear hf (hlin f)
  obtain ⟨B, hB⟩ := exists_matrix_of_linear hf' (hlin f')
  exact exists_gl_of_isCoordAct hβ hgV hA hB

theorem IsCoordAct.pow [Fintype ι] [DecidableEq ι] {g : G}
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) {γ : GL ι F}
    (hγ : IsCoordAct β g (γ : Matrix ι ι F).mulVec) (k : ℕ) :
    IsCoordAct β (g ^ k) ((γ ^ k : GL ι F) : Matrix ι ι F).mulVec := by
  induction k with
  | zero => simpa using (isCoordAct_one_mulVec (β := β))
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (ih.mul hgV hγ).congr fun x => by simp [Matrix.mulVec_mulVec]

theorem det_eq_one_of_isCoordAct [Fintype ι] [DecidableEq ι] [CharP F 2]
    (hβ : Function.Surjective β) {g : G} (hgV : g ∈ Subgroup.normalizer (V : Set G))
    {e : ℕ} (hge : g ^ 2 ^ e = 1) {γ : GL ι F} (hγ : IsCoordAct β g (γ : Matrix ι ι F).mulVec) :
    (γ : Matrix ι ι F).det = 1 := by
  have h := hγ.pow hgV (2 ^ e)
  rw [hge] at h
  have h1 : ((γ ^ 2 ^ e : GL ι F) : Matrix ι ι F) = 1 :=
    IsCoordAct.matrix_eq hβ (one_mem _) h isCoordAct_one_mulVec
  have hdet : (γ : Matrix ι ι F).det ^ 2 ^ e = 1 := by
    rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, h1, Matrix.det_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := sub_pow_char_pow (p := 2) (γ : Matrix ι ι F).det 1 e
  rw [hdet, one_pow, sub_self] at hs
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.1 hs)

end CoordMap

section CharCore

@[expose] def charCore (T K : Subgroup G) : Subgroup G :=
  (⨅ φ : MulAut ↥T, (K.subgroupOf T).map φ.toMonoidHom).map T.subtype

theorem charCore_subgroupOf (T K : Subgroup G) :
    (charCore T K).subgroupOf T = ⨅ φ : MulAut ↥T, (K.subgroupOf T).map φ.toMonoidHom :=
  PU.map_subtype_subgroupOf _

theorem charCore_le_self (T K : Subgroup G) : charCore T K ≤ T := Subgroup.map_subtype_le _

theorem charCore_le (T K : Subgroup G) : charCore T K ≤ K := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_iInf.1 hx) 1
  have hyx' : y = x := hyx
  have hy' : (y : G) ∈ K := hy
  rw [hyx'] at hy'
  exact hy'

theorem charCore_characteristic (T K : Subgroup G) :
    ((charCore T K).subgroupOf T).Characteristic := by
  rw [charCore_subgroupOf, Subgroup.characteristic_iff_map_le]
  intro ψ
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ ⨅ φ : MulAut ↥T, (K.subgroupOf T).map φ.toMonoidHom := hy
  rw [Subgroup.mem_iInf] at hy' ⊢
  intro φ
  obtain ⟨k, hk, hky⟩ := hy' (ψ⁻¹ * φ)
  refine ⟨k, hk, ?_⟩
  change φ k = ψ y
  have : ψ⁻¹ (φ k) = y := hky
  rw [← this]
  simp

theorem le_of_charCore_eq {T K : Subgroup G} (h : charCore T K = T) : T ≤ K :=
  h ▸ charCore_le T K

end CharCore

end CFSG.Quasithin.MS93
