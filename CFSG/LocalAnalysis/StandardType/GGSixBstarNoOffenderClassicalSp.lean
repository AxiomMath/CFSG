module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalCore
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSpFrame
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Symplectic
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

namespace NoOffenderClassical

section Mono

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem exists_perm_of_separating (A : GL ι K) {δ : κ → ι → K}
    (hsep : ∀ l l', l ≠ l' → ∃ k, δ k l ≠ δ k l')
    (hA : ∀ k, ∃ D : ι → K, (A : Matrix ι ι K) * diagonal (δ k) = diagonal D * (A : Matrix ι ι K)) :
    ∃ π : Equiv.Perm ι, ∀ u : ι → K,
      (A : Matrix ι ι K) * diagonal u = diagonal (u ∘ π) * (A : Matrix ι ι K) := by
  classical
  set M : Matrix ι ι K := (A : Matrix ι ι K) with hM
  set N : Matrix ι ι K := ((A⁻¹ : GL ι K) : Matrix ι ι K) with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : N * M = 1 := by rw [hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hrow : ∀ {k l l' : ι}, M k l ≠ 0 → M k l' ≠ 0 → l = l' := by
    intro k l l' hl hl'
    by_contra hne
    obtain ⟨k₀, hk₀⟩ := hsep l l' hne
    obtain ⟨D, hD⟩ := hA k₀
    have h1 := congrFun (congrFun hD k) l
    have h2 := congrFun (congrFun hD k) l'
    rw [mul_diagonal, diagonal_mul, mul_comm] at h1 h2
    exact hk₀ ((mul_right_cancel₀ hl h1).trans (mul_right_cancel₀ hl' h2).symm)
  have hex : ∀ k, ∃ l, M k l ≠ 0 := by
    intro k
    have h1 : (M * N) k k = 1 := by rw [hMN, one_apply_eq]
    rw [mul_apply] at h1
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1 ▸ one_ne_zero)
    exact ⟨l, left_ne_zero_of_mul hl⟩
  choose π₀ hπ₀ using hex
  have hsurj : Function.Surjective π₀ := by
    intro l
    have h1 : (N * M) l l = 1 := by rw [hNM, one_apply_eq]
    rw [mul_apply] at h1
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1 ▸ one_ne_zero)
    exact ⟨k, hrow (hπ₀ k) (right_ne_zero_of_mul hk)⟩
  have hbij : Function.Bijective π₀ := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  refine ⟨Equiv.ofBijective π₀ hbij, fun u => ?_⟩
  ext k l
  rw [mul_diagonal, diagonal_mul]
  by_cases h : M k l = 0
  · rw [h, zero_mul, mul_zero]
  · have hl : l = π₀ k := hrow h (hπ₀ k)
    simp only [Function.comp_apply, Equiv.ofBijective_apply]
    rw [← hl, mul_comm]

end Mono

namespace Sp

section Paired

variable {n : ℕ} {F : Type} [Field F]

@[expose] def idx : Fin n ⊕ Fin n → Fin n := Sum.elim id id

theorem pairedUnits_eq_one_iff (t : Fin n → Fˣ) (k : Fin n ⊕ Fin n) :
    TableBSymp.pairedUnits t k = 1 ↔ t (idx k) = 1 := by
  rcases k with i | i
  · rfl
  · change (t i)⁻¹ = 1 ↔ t i = 1
    exact inv_eq_one

theorem pairedUnits_mul_eq_one (t : Fin n → Fˣ) {k k' : Fin n ⊕ Fin n} (hne : k ≠ k')
    (hidx : idx k = idx k') : TableBSymp.pairedUnits t k * TableBSymp.pairedUnits t k' = 1 := by
  rcases k with i | i <;> rcases k' with j | j
  · exact absurd (by simpa [idx] using hidx) hne
  · change t i * (t j)⁻¹ = 1
    rw [show j = i from (by simpa [idx] using hidx : i = j).symm, mul_inv_cancel]
  · change (t i)⁻¹ * t j = 1
    rw [show j = i from (by simpa [idx] using hidx : i = j).symm, inv_mul_cancel]
  · exact absurd (by simpa [idx] using hidx) hne

end Paired

section Aut

variable {n : ℕ} {F : Type} [Field F] {G : Type} [Group G]

theorem exists_conj_field [Finite F] [CharP F 2] (hn : 3 ≤ n) {ψ : StatedSp n F →* G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {y : G}
    (hy : y ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ (A : gsp n F) (σ : F ≃+* F), ∀ u : StatedSp n F,
      y * ψ u * y⁻¹ = ψ (conjSp n F A (fieldSp n F σ u)) := by
  set φN := ψ.range.normalizerMonoidHom
  set Θ := AutPSp.projEquiv hker hC
  set α := (MulAut.congr Θ).symm (φN ⟨y, hy⟩) with hαdef
  obtain ⟨A, σ, hα⟩ := (automorphism_generation (K := F) hn).2 α
  refine ⟨A, σ, fun u => ?_⟩
  have key : Θ.symm (φN ⟨y, hy⟩ (Θ (proj n F u))) =
      proj n F (conjSp n F A (fieldSp n F σ u)) := by
    rw [← conjAut_proj, ← fieldAut_proj, ← MulAut.mul_apply, ← hα]
    rfl
  rw [MulEquiv.symm_apply_eq] at key
  exact congrArg Subtype.val key

end Aut

section Frame

variable {n : ℕ} {F : Type} [Field F] {G : Type} [Group G]

theorem frameDiag_mul (A₀ : StatedSp n F) (s t : Fin n → Fˣ) :
    RestSp.frameDiag A₀ (s * t) = RestSp.frameDiag A₀ s * RestSp.frameDiag A₀ t := by
  simp only [RestSp.frameDiag, map_mul]
  group

theorem frameDiag_one (A₀ : StatedSp n F) : RestSp.frameDiag A₀ 1 = 1 := by
  simp only [RestSp.frameDiag, map_one, mul_one, mul_inv_cancel]

theorem frameDiag_pow (A₀ : StatedSp n F) (t : Fin n → Fˣ) (k : ℕ) :
    RestSp.frameDiag A₀ t ^ k = RestSp.frameDiag A₀ (t ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, frameDiag_one]
  | succ k ih => rw [pow_succ, pow_succ, ih, frameDiag_mul]

theorem frameDiag_injective (A₀ : StatedSp n F) : Function.Injective (RestSp.frameDiag A₀) := by
  intro s t h
  have h1 : equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal s) =
      equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t) := by
    have h2 := congrArg (fun z => A₀⁻¹ * z * A₀) h
    simp only [RestSp.frameDiag] at h2
    simpa [mul_assoc] using h2
  exact TauCeti.GLSymplecticFin.diagonal_injective ((equivStatedSp n F).injective h1)

@[expose] noncomputable def frameCoord (ψ : StatedSp n F →* G) (A₀ : StatedSp n F) (b : G) :
    Fin n → Fˣ :=
  open Classical in
  if h : ∃ t, b = ψ (RestSp.frameDiag A₀ t) then Classical.choose h else 1

theorem frameCoord_eq {ψ : StatedSp n F →* G} (hψ : Function.Injective ψ) (A₀ : StatedSp n F)
    (t : Fin n → Fˣ) : frameCoord ψ A₀ (ψ (RestSp.frameDiag A₀ t)) = t := by
  have h : ∃ s, ψ (RestSp.frameDiag A₀ t) = ψ (RestSp.frameDiag A₀ s) := ⟨t, rfl⟩
  rw [frameCoord, dite_eq_left h]
  exact (frameDiag_injective A₀ (hψ (Classical.choose_spec h))).symm

theorem coords {ψ : StatedSp n F →* G} (hψ : Function.Injective ψ) {A₀ : StatedSp n F} {p : ℕ}
    {Bs : Subgroup G} (hfr : ∀ b ∈ Bs, ∃ t, b = ψ (RestSp.frameDiag A₀ t))
    (hΩ : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    Coords p Bs (frameCoord ψ A₀) where
  mul a ha b hb := by
    obtain ⟨s, rfl⟩ := hfr a ha
    obtain ⟨t, rfl⟩ := hfr b hb
    rw [← map_mul, ← frameDiag_mul, frameCoord_eq hψ, frameCoord_eq hψ, frameCoord_eq hψ]
  inj a ha b hb hab := by
    obtain ⟨s, rfl⟩ := hfr a ha
    obtain ⟨t, rfl⟩ := hfr b hb
    rw [frameCoord_eq hψ, frameCoord_eq hψ] at hab
    rw [hab]
  surj t ht := by
    refine ⟨ψ (RestSp.frameDiag A₀ t), hΩ _ ?_ ?_, frameCoord_eq hψ A₀ t⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨s, rfl⟩ := hfr b hb
      rw [← map_mul, ← map_mul, ← frameDiag_mul, ← frameDiag_mul, mul_comm]
    · rw [← map_pow, frameDiag_pow, show t ^ p = 1 from funext fun i => ht i, frameDiag_one,
        map_one]

end Frame

section Transport

variable {n : ℕ} {F : Type} [Field F] {G : Type} [Group G]

theorem coe_frameDiag (A₀ : StatedSp n F) (t : Fin n → Fˣ) :
    ((RestSp.frameDiag A₀ t : StatedSp n F) : GL (Fin n ⊕ Fin n) F) =
      (A₀ : GL (Fin n ⊕ Fin n) F) * TauCeti.diagGL (TableBSymp.pairedUnits t) *
        (A₀ : GL (Fin n ⊕ Fin n) F)⁻¹ := by
  simp only [RestSp.frameDiag, Subgroup.coe_mul, Subgroup.coe_inv, RestSp.coe_equiv_diagonal]

theorem coe_fieldSp_eq (σ : F ≃+* F) (g : StatedSp n F) :
    ((fieldSp n F σ g : StatedSp n F) : GL (Fin n ⊕ Fin n) F) =
      GeneralLinearGroup.map (σ : F →+* F) (g : GL (Fin n ⊕ Fin n) F) :=
  Units.ext (coe_fieldSp σ g)

theorem map_diagGL (σ : F ≃+* F) (u : Fin n ⊕ Fin n → Fˣ) :
    GeneralLinearGroup.map (σ : F →+* F) (TauCeti.diagGL u) =
      TauCeti.diagGL (fun k => Units.map (σ : F →* F) (u k)) := by
  apply Units.ext
  change (TauCeti.diagGL u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map σ = _
  rw [TauCeti.diagGL_coe, TauCeti.diagGL_coe, diagonal_map (map_zero σ)]
  rfl

theorem pairedUnits_map (σ : F ≃+* F) (t : Fin n → Fˣ) (k : Fin n ⊕ Fin n) :
    Units.map (σ : F →* F) (TableBSymp.pairedUnits t k) =
      TableBSymp.pairedUnits (fun i => Units.map (σ : F →* F) (t i)) k := by
  rcases k with i | i
  · rfl
  · change Units.map (σ : F →* F) (t i)⁻¹ = (Units.map (σ : F →* F) (t i))⁻¹
    rw [map_inv]

theorem exists_supp_perm [Finite F] [CharP F 2] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p) {ψ : StatedSp n F →* G}
    (hψ : Function.Injective ψ) (hker : ψ.ker ≤ Subgroup.center (StatedSp n F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {A₀ : StatedSp n F} {Bs : Subgroup G}
    (hfr : ∀ b ∈ Bs, ∃ t, b = ψ (RestSp.frameDiag A₀ t)) (hκ : Coords p Bs (frameCoord ψ A₀))
    {e : G} (heM : e ∈ Subgroup.normalizer (ψ.range : Set G))
    (heB : e ∈ Subgroup.normalizer (Bs : Set G)) :
    ∃ τ : Equiv.Perm (Fin n), ∀ b ∈ Bs, ∀ i,
      frameCoord ψ A₀ (e * b * e⁻¹) (τ i) = 1 ↔ frameCoord ψ A₀ b i = 1 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨A, σ, hAσ⟩ := exists_conj_field hn hker hC heM
  set κ := frameCoord ψ A₀ with hκdef
  have hconj : ∀ b ∈ Bs, e * b * e⁻¹ ∈ Bs := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp heB b).mp hb
  set σu : Fˣ →* Fˣ := Units.map (σ : F →* F) with hσu
  have hσu1 : ∀ x : Fˣ, σu x = 1 ↔ x = 1 := fun x => by
    constructor
    · intro h
      apply Units.ext
      have h1 := congrArg Units.val h
      rw [hσu, Units.coe_map, Units.val_one] at h1
      rw [Units.val_one]
      exact σ.injective (h1.trans (map_one σ).symm)
    · rintro rfl
      exact map_one σu
  obtain ⟨Aσ, hAσdef⟩ : ∃ Aσ : GL (Fin n ⊕ Fin n) F,
      Aσ = GeneralLinearGroup.map (σ : F →+* F) (A₀ : GL _ F) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin n ⊕ Fin n) F, P = (A₀ : GL _ F)⁻¹ * (A : GL _ F) * Aσ :=
    ⟨_, rfl⟩
  have hmat : ∀ b ∈ Bs, P * TauCeti.diagGL (TableBSymp.pairedUnits (fun i => σu (κ b i))) =
      TauCeti.diagGL (TableBSymp.pairedUnits (κ (e * b * e⁻¹))) * P := by
    intro b hb
    obtain ⟨t, rfl⟩ := hfr b hb
    obtain ⟨t', ht'⟩ := hfr _ (hconj _ hb)
    have h1 : RestSp.frameDiag A₀ t' = conjSp n F A (fieldSp n F σ (RestSp.frameDiag A₀ t)) := by
      apply hψ
      rw [← ht', ← hAσ]
    have h2 := congrArg (fun g : StatedSp n F => (g : GL (Fin n ⊕ Fin n) F)) h1
    simp only [coe_conjSp, coe_fieldSp_eq, coe_frameDiag, map_mul, map_inv, map_diagGL,
      pairedUnits_map, ← hAσdef] at h2
    rw [ht', hκdef, frameCoord_eq hψ, frameCoord_eq hψ]
    set D' := TauCeti.diagGL (TableBSymp.pairedUnits t') with hD'
    set Dσ := TauCeti.diagGL (TableBSymp.pairedUnits fun i => σu (t i)) with hDσ
    calc P * Dσ = (A₀ : GL _ F)⁻¹ * ((A : GL _ F) * (Aσ * Dσ * Aσ⁻¹) * (A : GL _ F)⁻¹) *
          ((A : GL _ F) * Aσ) := by rw [hP]; group
      _ = (A₀ : GL _ F)⁻¹ * ((A₀ : GL _ F) * D' * (A₀ : GL _ F)⁻¹) * ((A : GL _ F) * Aσ) := by
          rw [h2]
      _ = D' * P := by rw [hP]; group
  set ζu : Fˣ := (hζ.isUnit hp.ne_zero).unit with hζudef
  have hζu : (ζu : F) = ζ := IsUnit.unit_spec _
  have hζup : ζu ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, hζ.pow_eq_one, Units.val_one])
  have hζu1 : ζu ≠ 1 := fun h1 => hζ.ne_one hp.one_lt (by rw [← hζu, h1, Units.val_one])
  have haxis : ∀ i, ∃ b ∈ Bs, κ b = Pi.mulSingle i ζu := fun i => hκ.surj _ fun j => by
    by_cases hj : j = i
    · rw [hj, Pi.mulSingle_eq_same, hζup]
    · rw [Pi.mulSingle_eq_of_ne hj, one_pow]
  set δ : ↥Bs → Fin n ⊕ Fin n → F := fun b k =>
    ((TableBSymp.pairedUnits (fun i => σu (κ b i)) k : Fˣ) : F) with hδ
  have hsep : ∀ l l', l ≠ l' → ∃ b, δ b l ≠ δ b l' := by
    intro l l' hll'
    obtain ⟨b, hb, hbi⟩ := haxis (idx l)
    refine ⟨⟨b, hb⟩, fun heq => ?_⟩
    set w := TableBSymp.pairedUnits (fun i => σu (κ b i)) with hw
    have hwl : w l ≠ 1 := by
      intro h0
      rw [hw, pairedUnits_eq_one_iff, hσu1, hbi, Pi.mulSingle_eq_same] at h0
      exact hζu1 h0
    have hweq : w l = w l' := Units.ext heq
    by_cases hidx : idx l' = idx l
    · have h1 := pairedUnits_mul_eq_one (fun i => σu (κ b i)) hll' hidx.symm
      rw [← hw, ← hweq] at h1
      have hwp : w l ^ p = 1 := by
        have h2 : (fun i => σu (κ b i)) (idx l) ^ p = 1 := by
          simp only [hbi, Pi.mulSingle_eq_same, ← map_pow, hζup, map_one]
        rcases l with i | i
        · exact h2
        · change ((σu (κ b i))⁻¹) ^ p = 1
          rw [inv_pow]
          exact inv_eq_one.mpr h2
      have hw2 : w l ^ 2 = 1 := by rw [pow_two]; exact h1
      have hg := pow_gcd_eq_one.mpr ⟨hwp, hw2⟩
      rw [(Nat.coprime_primes hp Nat.prime_two).mpr hp2, pow_one] at hg
      exact hwl hg
    · have h1 : w l' = 1 := by
        rw [hw, pairedUnits_eq_one_iff, hσu1, hbi, Pi.mulSingle_eq_of_ne hidx]
      exact hwl (hweq.trans h1)
  obtain ⟨ρ, hρ⟩ := exists_perm_of_separating P hsep fun b => ⟨_, by
    have h1 := congrArg Units.val (hmat b b.2)
    rw [Units.val_mul, Units.val_mul, TauCeti.diagGL_coe, TauCeti.diagGL_coe] at h1
    exact h1⟩
  have hcoord : ∀ b ∈ Bs, ∀ k, TableBSymp.pairedUnits (κ (e * b * e⁻¹)) k =
      TableBSymp.pairedUnits (fun i => σu (κ b i)) (ρ k) := by
    intro b hb k
    have h1 := congrArg Units.val (hmat b hb)
    rw [Units.val_mul, Units.val_mul, TauCeti.diagGL_coe, TauCeti.diagGL_coe] at h1
    have h2 := hρ fun k => ((TableBSymp.pairedUnits (fun i => σu (κ b i)) k : Fˣ) : F)
    rw [h1] at h2
    have h3 := congrArg (· * ((P⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) F)) h2
    simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one] at h3
    have h4 := congrFun (congrFun h3 k) k
    rw [diagonal_apply_eq, diagonal_apply_eq] at h4
    exact Units.ext h4
  set π : Fin n → Fin n := fun i => idx (ρ (Sum.inl i)) with hπ
  have hπ1 : ∀ b ∈ Bs, ∀ i, κ (e * b * e⁻¹) i = 1 ↔ κ b (π i) = 1 := by
    intro b hb i
    have h1 := hcoord b hb (Sum.inl i)
    rw [show κ (e * b * e⁻¹) i = TableBSymp.pairedUnits (κ (e * b * e⁻¹)) (Sum.inl i) from rfl,
      h1, pairedUnits_eq_one_iff, hσu1]
  have hπinj : Function.Injective π := by
    intro i i' hii'
    by_contra hne
    obtain ⟨b₀, hb₀, hb₀i⟩ := haxis i
    have hb : e⁻¹ * b₀ * e ∈ Bs := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ heB) b₀).mp hb₀
      simpa using this
    have heb : e * (e⁻¹ * b₀ * e) * e⁻¹ = b₀ := by group
    have hkk : ρ (Sum.inl i) ≠ ρ (Sum.inl i') := fun h => hne (Sum.inl_injective (ρ.injective h))
    have h1 := pairedUnits_mul_eq_one (fun j => σu (κ (e⁻¹ * b₀ * e) j)) hkk hii'
    rw [← hcoord _ hb, ← hcoord _ hb, heb] at h1
    change κ b₀ i * κ b₀ i' = 1 at h1
    rw [hb₀i, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hne), mul_one] at h1
    exact hζu1 h1
  have hπbij : Function.Bijective π := ⟨hπinj, Finite.injective_iff_surjective.mp hπinj⟩
  refine ⟨(Equiv.ofBijective π hπbij).symm, fun b hb i => ?_⟩
  rw [hπ1 b hb, show π ((Equiv.ofBijective π hπbij).symm i) = i from
    Equiv.ofBijective_apply_symm_apply π hπbij i]

end Transport

end Sp

end NoOffenderClassical

section Family

theorem ggSixBstarNoOffenderOn_PSpSplit : GGSixBstarNoOffenderOn GGPSpSplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hp⟩ := hP
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hrk : 2 ≤ n := hctx.2.2.2.1.2
  have hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)) := hctx.2.2.2.2.1.2
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]
    exact hC
  have hpp := hctx.prime
  have hp2 := hctx.ne_two
  have hBs := hctx.bstar.2.1
  have hdiag : ∀ b ∈ Bs, GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ b :=
    fun b hb => hctx.2.2.2.2.2.2.1.2 b hb
  obtain ⟨A₀, hA₀⟩ := spFrame_core hf hrk ψ hker hCψ hpp hp2 hBs hdiag hp
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1
  have hr4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
  have hcard : p ^ 4 ≤ Nat.card Bs :=
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hpp.pos hr4
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBBs
  have hn4 : 4 ≤ n :=
    AutPSp.four_le_of_bstar (K := GaloisField 2 f) hrk ψ hker hCψ hpp hp2 hBs hcard hdiag
  have : NeZero n := ⟨by omega⟩
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : a ∈ Subgroup.center (StatedSp n (GaloisField 2 f)) := hker ha
    rw [AutPSp.center_eq_bot] at hz
    exact Subgroup.mem_bot.mp hz
  have : Fact p.Prime := ⟨hpp⟩
  have hpK : p ∣ Nat.card (GaloisField 2 f)ˣ := by
    rw [Nat.card_units, GaloisField.card 2 f (by omega)]
    exact hp
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 f)ˣ) p hpK
  have hζ : IsPrimitiveRoot (u : GaloisField 2 f) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu)
  have hκ := NoOffenderClassical.Sp.coords hψ hA₀ hctx.bstar.2.2.2 (p := p)
  intro E hEM hEN hE
  by_cases hEC : E ≤ Subgroup.centralizer (Bs : Set G)
  · exact Or.inl hEC
  right
  refine NoOffenderClassical.card_mul_lt_of_coords hpp hp2 hζ hκ hBs hE hEN (fun e he => ?_) hEC
  have heM : e ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hctx.range_eq]
    exact hEM he
  exact NoOffenderClassical.Sp.exists_supp_perm (by omega) hpp hp2 hζ hψ hker hCψ hA₀ hκ heM
    (hEN he)

theorem ggSixBstarNoOffenderAt_PSp_of_nonsplit (h : GGSixBstarNoOffenderOn GGPSpNonsplit) :
    GGSixBstarNoOffenderAt .PSp :=
  ggSixBstarNoOffenderAt_PSp_of_on ggSixBstarNoOffenderOn_PSpSplit h

end Family

end CFSG.StandardType
