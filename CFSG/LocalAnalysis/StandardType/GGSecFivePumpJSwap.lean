module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.SeitzReduction.LinearPilot

private theorem jswap_coe {m : ℕ} {F : Type} [Field F] [CharP F 2]
    (s : Equiv.Perm (Fin (m + 1))) (d : Fin (m + 1) → Fˣ) :
    ((ggPermSL s * InnerDiagA.conjSL (InnerDiagA.diagGL d) (ggPermSL s)⁻¹ :
      Matrix.SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.diagonal fun j => (d (s j) : F) * ((d j)⁻¹ : Fˣ) := by
  have hP : ∀ σ : Equiv.Perm (Fin (m + 1)),
      ((ggPermSL σ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) = σ.permMatrix F := fun _ => rfl
  rw [Matrix.SpecialLinearGroup.coe_mul, InnerDiagA.coe_conjSL, InnerDiagA.coe_diagGL_inv,
    InnerDiagA.coe_diagGL, ggPermSL_inv, hP, hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Equiv.Perm.permMatrix,
    PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.mul_diagonal, Matrix.diagonal_apply, Equiv.Perm.inv_def]
  · simp [Matrix.mul_diagonal, Matrix.diagonal_apply, Equiv.Perm.inv_def, hij]

private theorem jswap_conj {m : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G} {b : G} {D : GL (Fin (m + 1)) F}
    (hb : (b, D) ∈ LinFusion.ggInducedPairs ψ) (τ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    ψ τ * b * (ψ τ)⁻¹ = ψ (τ * InnerDiagA.conjSL D τ⁻¹) * b := by
  rw [map_mul, ← LinFusion.mem_ggInducedPairs.mp hb τ⁻¹, map_inv]
  group

private theorem jswap_mem {m : ℕ} {F : Type} [Field F] [CharP F 2] {G : Type} [Group G]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G} {p : ℕ} {Bs : Subgroup G}
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {δ : ↥Bs →* (Fin (m + 1) → Fˣ)}
    (hδ : ∀ b : ↥Bs, ((b : G), InnerDiagA.diagGL (δ b)) ∈ LinFusion.ggInducedPairs ψ)
    (hδp : ∀ (b : ↥Bs) j, δ b j ^ p = 1) (s : Equiv.Perm (Fin (m + 1))) (b : ↥Bs) :
    ψ (ggPermSL s * InnerDiagA.conjSL (InnerDiagA.diagGL (δ b)) (ggPermSL s)⁻¹) ∈ Bs := by
  have hu := jswap_coe (F := F) s (δ b)
  set u := ggPermSL s * InnerDiagA.conjSL (InnerDiagA.diagGL (δ b)) (ggPermSL s)⁻¹
  have hcomm : ∀ e : Fin (m + 1) → Fˣ, InnerDiagA.conjSL (InnerDiagA.diagGL e) u = u := by
    intro e
    apply Subtype.ext
    rw [InnerDiagA.coe_conjSL, hu, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL_inv]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij
      rw [mul_right_comm, Units.mul_inv, one_mul]
    · rw [zero_mul, zero_mul]
  have hδpF : ∀ (b : ↥Bs) j, ((δ b j : Fˣ) : F) ^ p = 1 := fun b j => by
    rw [← Units.val_pow_eq_pow_val, hδp, Units.val_one]
  have hup : u ^ p = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hu, Matrix.diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply, mul_pow, inv_pow, hδpF]
    · simp [Matrix.diagonal_apply, hij]
  refine hC3 _ (Subgroup.mem_centralizer_iff.mpr fun g hg => ?_) (by rw [← map_pow, hup, map_one])
  have h1 : g * ψ u * g⁻¹ = ψ u := by
    have h2 := LinFusion.mem_ggInducedPairs.mp (hδ ⟨g, hg⟩) u
    rwa [hcomm] at h2
  exact mul_inv_eq_iff_eq_mul.mp h1

private theorem jswap_fix {m : ℕ} {F : Type} [Field F] [CharP F 2] (hm : 2 ≤ m) {G : Type}
    [Group G] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {a c : Fin (m + 1)} (d : Fin (m + 1) → Fˣ) :
    ψ (ggPermSL (Equiv.swap a c) * InnerDiagA.conjSL (InnerDiagA.diagGL d)
      (ggPermSL (Equiv.swap a c))⁻¹) = 1 ↔ d a = d c := by
  have hu := jswap_coe (F := F) (Equiv.swap a c) d
  constructor
  · intro h1
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker h1)
    obtain ⟨k, hka, hkc⟩ := Fin.exists_ne_and_ne_of_two_lt a c (by omega)
    have hk := congrFun (congrFun hr k) k
    have ha := congrFun (congrFun hr a) a
    rw [hu, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
      Equiv.swap_apply_of_ne_of_ne hka hkc, Units.mul_inv] at hk
    rw [hu, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
      Equiv.swap_apply_left, hk, ← Units.val_mul, eq_comm, Units.val_eq_one,
      mul_inv_eq_one] at ha
    exact ha.symm
  · intro h
    have hsw : ∀ j, d (Equiv.swap a c j) = d j := by
      intro j
      by_cases hja : j = a
      · rw [hja, Equiv.swap_apply_left, h]
      by_cases hjc : j = c
      · rw [hjc, Equiv.swap_apply_right, h]
      · rw [Equiv.swap_apply_of_ne_of_ne hja hjc]
    have h1 : ggPermSL (Equiv.swap a c) * InnerDiagA.conjSL (InnerDiagA.diagGL d)
        (ggPermSL (Equiv.swap a c))⁻¹ = (1 : Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
      apply Subtype.ext
      rw [hu, Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
      congr 1
      funext j
      rw [hsw, Units.mul_inv]
    rw [h1, map_one]

private theorem jswap_index {m : ℕ} {F : Type} [Field F] {G : Type} [Group G] {p : ℕ}
    (hp : p.Prime) {Bs : Subgroup G} {δ : ↥Bs →* (Fin (m + 1) → Fˣ)}
    (hδp : ∀ (b : ↥Bs) j, δ b j ^ p = 1)
    (hfull : ∀ v : Fin (m + 1) → Fˣ, (∀ j, v j ^ p = 1) →
      ∃ (b : ↥Bs) (c : Fˣ), ∀ j, δ b j = c * v j)
    {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ p) {a c : Fin (m + 1)} (hac : a ≠ c) :
    Nat.card {b : ↥Bs // δ b a = δ b c} * p = Nat.card ↥Bs := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let χ : ↥Bs →* Fˣ :=
    (Pi.evalMonoidHom (fun _ => Fˣ) a).comp δ / (Pi.evalMonoidHom (fun _ => Fˣ) c).comp δ
  have hχ : ∀ b, χ b = δ b a / δ b c := fun _ => rfl
  have hle : χ.range ≤ rootsOfUnity p F := by
    rintro _ ⟨b, rfl⟩
    rw [mem_rootsOfUnity, hχ, div_pow, hδp, hδp, div_one]
  obtain ⟨b, r, hb⟩ := hfull (Pi.mulSingle a ζ) fun j => by
    by_cases hj : j = a
    · rw [hj, Pi.mulSingle_eq_same, hζ.pow_eq_one]
    · rw [Pi.mulSingle_eq_of_ne hj, one_pow]
  have hζr : ζ ∈ χ.range := ⟨b, by
    rw [hχ, hb, hb, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hac.symm, mul_one,
      mul_div_cancel_left]⟩
  haveI : Finite χ.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hcr : Nat.card χ.range = p := by
    refine le_antisymm ((Subgroup.card_le_of_le hle).trans (card_rootsOfUnity F p)) ?_
    have h1 := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hζr)
    rwa [Nat.card_zpowers, ← hζ.eq_orderOf] at h1
  have hker : Nat.card {b : ↥Bs // δ b a = δ b c} = Nat.card χ.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun b => by rw [MonoidHom.mem_ker, hχ, div_eq_one])
  rw [hker, ← hcr]
  exact Subgroup.card_ker_mul_card_range χ

theorem ggDk_swap_refl {m : ℕ} {F : Type} [Field F] [CharP F 2] (hm : 2 ≤ m) {G : Type}
    [Group G] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {p : ℕ} (hp : p.Prime) {Bs : Subgroup G}
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {δ : ↥Bs →* (Fin (m + 1) → Fˣ)}
    (hδ : ∀ b : ↥Bs, ((b : G), InnerDiagA.diagGL (δ b)) ∈ LinFusion.ggInducedPairs ψ)
    (hδp : ∀ (b : ↥Bs) j, δ b j ^ p = 1)
    (hfull : ∀ v : Fin (m + 1) → Fˣ, (∀ j, v j ^ p = 1) →
      ∃ (b : ↥Bs) (c : Fˣ), ∀ j, δ b j = c * v j)
    {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ p) {a c : Fin (m + 1)} (hac : a ≠ c) :
    ∃ hN : ψ (ggPermSL (Equiv.swap a c)) ∈ Subgroup.normalizer (Bs : Set G),
      GGIsReflection p (ggConjAut Bs hN) ∧ ∀ b : ↥Bs, ggConjAut Bs hN b = b ↔ δ b a = δ b c := by
  set τ : Matrix.SpecialLinearGroup (Fin (m + 1)) F := ggPermSL (Equiv.swap a c) with hτ
  have hττ : τ * τ = 1 :=
    mul_eq_one_iff_eq_inv.mpr (by rw [hτ, ggPermSL_inv, Equiv.swap_inv])
  have hxx : ψ τ * ψ τ = 1 := by rw [← map_mul, hττ, map_one]
  have hfwd : ∀ g ∈ Bs, ψ τ * g * (ψ τ)⁻¹ ∈ Bs := by
    intro g hg
    rw [jswap_conj (b := g) (hδ ⟨g, hg⟩) τ]
    exact Bs.mul_mem (jswap_mem hC3 hδ hδp _ ⟨g, hg⟩) hg
  have hN : ψ τ ∈ Subgroup.normalizer (Bs : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨hfwd g, fun h => ?_⟩
    have h1 := hfwd _ h
    rwa [show ψ τ * (ψ τ * g * (ψ τ)⁻¹) * (ψ τ)⁻¹ = (ψ τ * ψ τ) * g * (ψ τ * ψ τ)⁻¹ by group,
      hxx, one_mul, inv_one, mul_one] at h1
  have hfix : ∀ b : ↥Bs, ggConjAut Bs hN b = b ↔ δ b a = δ b c := by
    intro b
    rw [← jswap_fix hm hker (δ b), Subtype.ext_iff, ggConjAut_apply, jswap_conj (hδ b) τ]
    exact mul_eq_right
  have hsq : ggConjAut Bs hN ^ 2 = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_pow_apply, pow_two, hxx, one_mul, inv_one, mul_one, MulAut.one_apply]
  refine ⟨hN, ⟨hsq, ?_⟩, hfix⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hfix)]
  exact jswap_index hp hδp hfull hζ hac

theorem ggPermSL_swap_mem_blockSpecialLinear {m : ℕ} {F : Type} [Field F] [CharP F 2]
    {I : Finset (Fin (m + 1))} {a c : Fin (m + 1)} (ha : a ∈ I) (hc : c ∈ I) :
    ggPermSL (F := F) (Equiv.swap a c) ∈ blockSpecialLinear I := by
  have hP : ∀ (σ : Equiv.Perm (Fin (m + 1))) (i j : Fin (m + 1)),
      ((ggPermSL σ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = if σ i = j then 1 else 0 := by
    intro σ i j
    show (σ.toPEquiv.toMatrix : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = _
    rw [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [Option.mem_def, Option.some.injEq]
  rw [mem_blockSpecialLinear]
  intro i j hij
  rw [hP, Matrix.one_apply]
  rcases hij with hi | hj
  · rw [Equiv.swap_apply_of_ne_of_ne (fun h : i = a => hi (h ▸ ha))
      (fun h : i = c => hi (h ▸ hc))]
  · simp only [Equiv.apply_eq_iff_eq_symm_apply, Equiv.symm_swap,
      Equiv.swap_apply_of_ne_of_ne (fun h : j = a => hj (h ▸ ha)) (fun h : j = c => hj (h ▸ hc))]

end CFSG.StandardType

end
