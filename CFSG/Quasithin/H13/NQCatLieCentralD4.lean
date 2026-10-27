module

public import CFSG.Quasithin.H13.NQCatLieCentralCore
public import CFSG.Quasithin.H13.NQCatLieCartanD4
public import CFSG.Quasithin.Vol2.Ch7Sec77A23Stmts

public section

namespace CFSG.Quasithin.H13.NQCat.LieCentral.D4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
  CFSG.Quasithin.B42D4

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom

@[expose] noncomputable def traceHom (a : K) : K →+ trialityFixedField K τ₀ where
  toFun t := trialityTrace K τ₀ hσ3 (a * t)
  map_zero' := by
    apply Subtype.ext
    simp [trialityTrace]
  map_add' s t := by
    apply Subtype.ext
    simp only [trialityTrace, mul_add, map_add, Subfield.coe_add]
    ring

omit [Finite K] in
theorem traceHom_surjective {a : K} (ha : a ≠ 0) : Function.Surjective (traceHom σ hσ3 a) := by
  intro e
  refine ⟨a⁻¹ * e, ?_⟩
  change trialityTrace K τ₀ hσ3 (a * (a⁻¹ * e)) = e
  rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul, trace_fixed]

include hσ3 in
theorem ox₆_inv
    (f : trialityFixedField K τ₀) : (ox₆ σ f)⁻¹ = ox₆ σ f := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← ox₆_add σ hσ3,
    show f + f = 0 from Subtype.ext (show (f : K) + (f : K) = 0 from CharTwo.add_self_eq_zero _),
    ox₆_zero σ hσ3]

include hσ3 in
theorem ox₃_comm
    (a b : K) : Commute (ox₃ σ a) (ox₃ σ b) := by
  change ox₃ σ a * ox₃ σ b = ox₃ σ b * ox₃ σ a
  rw [← ox₃_add σ hσ3, ← ox₃_add σ hσ3, add_comm]

include hσ3 in
theorem ox₄_comm
    (a b : K) : Commute (ox₄ σ a) (ox₄ σ b) := by
  change ox₄ σ a * ox₄ σ b = ox₄ σ b * ox₄ σ a
  rw [← ox₄_add σ hσ3, ← ox₄_add σ hσ3, add_comm]

include hσ3 in
theorem ox₅_comm
    (a b : trialityFixedField K τ₀) : Commute (ox₅ σ a) (ox₅ σ b) := by
  change ox₅ σ a * ox₅ σ b = ox₅ σ b * ox₅ σ a
  rw [← ox₅_add σ hσ3, ← ox₅_add σ hσ3, add_comm]

include hσ3 in
theorem ox₆_comm
    (a b : trialityFixedField K τ₀) : Commute (ox₆ σ a) (ox₆ σ b) := by
  change ox₆ σ a * ox₆ σ b = ox₆ σ b * ox₆ σ a
  rw [← ox₆_add σ hσ3, ← ox₆_add σ hσ3, add_comm]

include hσ3 in
theorem b_eq_zero_of_commute
    {a c d : K} {b e f e' : trialityFixedField K τ₀} (he' : e' ≠ 0)
    (h : ox₅ σ e' * (ox₁ σ a * ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f) =
      ox₁ σ a * ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f * ox₅ σ e') : b = 0 := by
  have h1 : MulAut.conj (ox₁ σ a * ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f)
      (ox₅ σ e') = ox₅ σ e' := by
    rw [MulAut.conj_apply, ← h, mul_inv_cancel_right]
  simp only [map_mul, MulAut.mul_apply] at h1
  rw [conj_eq_of_commute (comm56 σ hσ3 e' f).symm, conj_eq_of_commute (ox₅_comm σ hσ3 e e'),
    conj_eq_of_commute (comm45 σ hσ3 d e'), conj_eq_of_commute (comm35 σ hσ3 c e'),
    conj_eq_of_commutator (rel25 σ hσ3 b e'), map_mul,
    conj_eq_of_commute (comm16 σ hσ3 a (b * e')), conj_eq_of_commute (comm15 σ hσ3 a e')] at h1
  have h3 : b * e' = 0 := ox₆_inj σ hσ3 ((mul_eq_right.1 h1).trans (ox₆_zero σ hσ3).symm)
  exact (mul_eq_zero.1 h3).resolve_right he'

include hσ3 in
theorem trace_eq_zero_of_commute_ox₄
    {a c d t : K} {b e f : trialityFixedField K τ₀}
    (h : ox₄ σ t * (ox₁ σ a * ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f) =
      ox₁ σ a * ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f * ox₄ σ t) :
    trialityTrace K τ₀ hσ3 (a * t) = 0 ∧ trialityTrace K τ₀ hσ3 (c * t) = 0 := by
  have h1 : MulAut.conj (ox₁ σ a * ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f)
      (ox₄ σ t) = ox₄ σ t := by
    rw [MulAut.conj_apply, ← h, mul_inv_cancel_right]
  simp only [map_mul, MulAut.mul_apply] at h1
  rw [conj_eq_of_commute (comm46 σ hσ3 t f).symm, conj_eq_of_commute (comm45 σ hσ3 t e).symm,
    conj_eq_of_commute (ox₄_comm σ hσ3 d t), conj_eq_of_commutator (rel34 σ hσ3 c t), map_mul,
    conj_eq_of_commute (comm26 σ hσ3 b _), conj_eq_of_commute (comm24 σ hσ3 b t), map_mul,
    conj_eq_of_commute (comm16 σ hσ3 a _), conj_eq_of_commutator (rel14 σ hσ3 a t)] at h1
  have h2 : ox₆ σ (trialityTrace K τ₀ hσ3 (c * t)) * ox₅ σ (trialityTrace K τ₀ hσ3 (a * t)) =
      1 := mul_eq_right.1 (by rw [mul_assoc]; exact h1)
  have h3 : ox₁ σ 0 * ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0 * ox₅ σ (trialityTrace K τ₀ hσ3 (a * t)) *
      ox₆ σ (trialityTrace K τ₀ hσ3 (c * t)) =
      ox₁ σ 0 * ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0 * ox₅ σ 0 * ox₆ σ 0 := by
    simp only [ox₁_zero σ hσ3, ox₂_zero σ hσ3, ox₃_zero σ hσ3, ox₄_zero σ hσ3, ox₅_zero σ hσ3,
      ox₆_zero σ hσ3, one_mul, mul_one]
    rw [(comm56 σ hσ3 _ _).eq]
    exact h2
  obtain ⟨-, -, -, -, h5, h6⟩ := coord_unique σ hσ3 h3
  exact ⟨h5, h6⟩

include hσ3 in
theorem trace_eq_zero_of_commute_ox₃
    {c d s : K} {b e f : trialityFixedField K τ₀}
    (h : ox₃ σ s * (ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f) =
      ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f * ox₃ σ s) :
    trialityTrace K τ₀ hσ3 (s * d) = 0 := by
  have h1 : MulAut.conj (ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f) (ox₃ σ s) =
      ox₃ σ s := by
    rw [MulAut.conj_apply, ← h, mul_inv_cancel_right]
  simp only [map_mul, MulAut.mul_apply] at h1
  rw [conj_eq_of_commute (comm36 σ hσ3 s f).symm, conj_eq_of_commute (comm35 σ hσ3 s e).symm,
    conj_eq_of_commutator' (rel34 σ hσ3 s d), ox₆_inv σ hσ3, map_mul,
    conj_eq_of_commute (comm36 σ hσ3 c _), conj_eq_of_commute (ox₃_comm σ hσ3 c s), map_mul,
    conj_eq_of_commute (comm26 σ hσ3 b _), conj_eq_of_commute (comm23 σ hσ3 b s)] at h1
  exact ox₆_inj σ hσ3 ((mul_eq_right.1 h1).trans (ox₆_zero σ hσ3).symm)

include hσ3 in
theorem e_eq_zero_of_commute
    {e f β : trialityFixedField K τ₀} (hβ : β ≠ 0)
    (h : ox₂ σ β * (ox₅ σ e * ox₆ σ f) = ox₅ σ e * ox₆ σ f * ox₂ σ β) : e = 0 := by
  have h1 : MulAut.conj (ox₅ σ e * ox₆ σ f) (ox₂ σ β) = ox₂ σ β := by
    rw [MulAut.conj_apply, ← h, mul_inv_cancel_right]
  simp only [map_mul, MulAut.mul_apply] at h1
  rw [conj_eq_of_commute (comm26 σ hσ3 β f).symm, conj_eq_of_commutator' (rel25 σ hσ3 β e),
    ox₆_inv σ hσ3] at h1
  have h3 := ox₆_inj σ hσ3 ((mul_eq_right.1 h1).trans (ox₆_zero σ hσ3).symm)
  exact (mul_eq_zero.1 h3).resolve_left hβ

include hσ3 in
theorem ox₆_mem_centralizer
    (f : trialityFixedField K τ₀) :
    ox₆ σ f ∈ Subgroup.centralizer
      (graphFixedPosUnipotent TwistTag.D4 K τ₀ : Set (ModGL TwistTag.D4.tag K)) := by
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  obtain ⟨a, b, c, d, e, f', rfl⟩ := coord_exists σ hσ3 hy
  exact ((((((comm16 σ hσ3 a f).mul_left (comm26 σ hσ3 b f)).mul_left
    (comm36 σ hσ3 c f)).mul_left (comm46 σ hσ3 d f)).mul_left (comm56 σ hσ3 e f)).mul_left
    (ox₆_comm σ hσ3 f' f)).eq

theorem centralIndex_d4
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    CentralIndex ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hσ3 : σ.toRingHom ^ 3 = 1 := sigma_cube hK σ hσ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hk := card_fixedField (by omega) hK σ hσ
  have hk4 : 4 ≤ Nat.card (trialityFixedField K τ₀) := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : IsSylowTwoOf (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  refine centralIndex_of_le hUC hUsyl fun x hx hidx => ?_
  obtain ⟨-, ⟨-, hm₂, hm₃, hm₄, hm₅, -⟩, -⟩ := ox_data σ hσ3
  let ψ₂ : Multiplicative (trialityFixedField K τ₀) →* ModGL TwistTag.D4.tag K :=
    { toFun := fun t => ox₂ σ (Multiplicative.toAdd t)
      map_one' := ox₂_zero σ hσ3
      map_mul' := fun s t => ox₂_add σ hσ3 _ _ }
  let ψ₃ : Multiplicative K →* ModGL TwistTag.D4.tag K :=
    { toFun := fun t => ox₃ σ (Multiplicative.toAdd t)
      map_one' := ox₃_zero σ hσ3
      map_mul' := fun s t => ox₃_add σ hσ3 _ _ }
  let ψ₄ : Multiplicative K →* ModGL TwistTag.D4.tag K :=
    { toFun := fun t => ox₄ σ (Multiplicative.toAdd t)
      map_one' := ox₄_zero σ hσ3
      map_mul' := fun s t => ox₄_add σ hσ3 _ _ }
  let ψ₅ : Multiplicative (trialityFixedField K τ₀) →* ModGL TwistTag.D4.tag K :=
    { toFun := fun t => ox₅ σ (Multiplicative.toAdd t)
      map_one' := ox₅_zero σ hσ3
      map_mul' := fun s t => ox₅_add σ hσ3 _ _ }
  obtain ⟨a, b, c, d, e, f, rfl⟩ := coord_exists σ hσ3 hx
  obtain ⟨e', he', h5⟩ := exists_ne_zero_commute_of_hom
    (P := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) ψ₅
    (fun s t hst => Multiplicative.toAdd.injective (ox₅_inj σ hσ3 hst)) (fun t => hm₅ _)
    (by omega) hidx
  have hb := b_eq_zero_of_commute σ hσ3 he' h5
  have ha : a = 0 := by
    by_contra ha
    have h1 := card_range_le_two_of_commute (P := graphFixedPosUnipotent TwistTag.D4 K τ₀) ψ₄
      (fun t => hm₄ _) (traceHom σ hσ3 a) hidx
      (fun t ht => (trace_eq_zero_of_commute_ox₄ σ hσ3 ht).1)
    rw [card_range_toMultiplicative_of_surjective (traceHom_surjective σ hσ3 ha)] at h1
    omega
  have hc : c = 0 := by
    by_contra hc
    have h1 := card_range_le_two_of_commute (P := graphFixedPosUnipotent TwistTag.D4 K τ₀) ψ₄
      (fun t => hm₄ _) (traceHom σ hσ3 c) hidx
      (fun t ht => (trace_eq_zero_of_commute_ox₄ σ hσ3 ht).2)
    rw [card_range_toMultiplicative_of_surjective (traceHom_surjective σ hσ3 hc)] at h1
    omega
  subst ha hb hc
  rw [ox₁_zero σ hσ3, one_mul] at hidx ⊢
  have hd : d = 0 := by
    by_contra hd
    have h1 := card_range_le_two_of_commute (P := graphFixedPosUnipotent TwistTag.D4 K τ₀) ψ₃
      (fun t => hm₃ _) (traceHom σ hσ3 d) hidx (fun s hs => by
        change trialityTrace K τ₀ hσ3 (d * s) = 0
        rw [mul_comm]
        exact trace_eq_zero_of_commute_ox₃ σ hσ3 hs)
    rw [card_range_toMultiplicative_of_surjective (traceHom_surjective σ hσ3 hd)] at h1
    omega
  subst hd
  rw [ox₂_zero σ hσ3, ox₃_zero σ hσ3, ox₄_zero σ hσ3, one_mul, one_mul, one_mul] at hidx ⊢
  obtain ⟨β, hβ, h2⟩ := exists_ne_zero_commute_of_hom
    (P := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) ψ₂
    (fun s t hst => Multiplicative.toAdd.injective (ox₂_inj σ hσ3 hst)) (fun t => hm₂ _)
    (by omega) hidx
  have he := e_eq_zero_of_commute σ hσ3 hβ h2
  subst he
  rw [ox₅_zero σ hσ3, one_mul]
  exact ox₆_mem_centralizer σ hσ3 f

end CFSG.Quasithin.H13.NQCat.LieCentral.D4
