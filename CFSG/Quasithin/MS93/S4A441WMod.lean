module

public import CFSG.Quasithin.Background.SL3SmallNat

public section

namespace CFSG.Quasithin.MS93.S4A.W441

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X7a
open scoped MatrixGroups commutatorElement

section Module

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private theorem natCard_eq_two_pow : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem two_mul_lt_finrank {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ}
    (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (ρ : Representation (ZMod 2) SL(3, F) W)
    (hirr : ρ.IsIrreducible) (hnt : ∃ g, ρ g ≠ 1) : 2 * f < Module.finrank (ZMod 2) W := by
  classical
  by_contra hdim
  push Not at hdim
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  obtain ⟨a, b, hne, hsum, W₀, ⟨e₀⟩⟩ :=
    B42SL3.exists_label hF hf ρ (Module.finBasis (ZMod 2) W) hirr hnt
  have hrank := SL3Small.two_mul_finrank_range_le ρ (SL3Small.up3_mul_self (F := F))
  rcases B42SL3.label_cases hf a b hne _ (fun c => dim_le_two_mul_rank_tensorRep c.1 c.2)
      hsum with ⟨hS, hH⟩ | ⟨-, -, hR⟩ | hR
  · obtain ⟨-, -, E, -⟩ := B42SL3.exists_natural_of_single hF ρ _ hirr hS hH W₀ e₀
    have h1 : Nat.card W = 2 ^ (3 * f) := by
      rw [Nat.card_congr E.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card, hF, Nat.card_fin,
        ← pow_mul, mul_comm]
    rw [natCard_eq_two_pow] at h1
    have := Nat.pow_right_injective le_rfl h1
    omega
  · omega
  · omega

end Module

section Descent

variable {K : Type} [Group K] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

private theorem eq_self_of_isPGroup [Finite W] {N : Subgroup K} [hN : N.Normal] (hN2 : IsPGroup 2 N)
    (ρ : Representation (ZMod 2) K W) (hirr : ρ.IsIrreducible) {k : K} (hk : k ∈ N) (w : W) :
    ρ k w = w := by
  obtain ⟨hnt, hU⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr
  set I := Representation.invariants (ρ.comp N.subtype) with hI
  have hmem : ∀ v, v ∈ I ↔ ∀ k ∈ N, ρ k v = v := fun v => by
    rw [hI, Representation.mem_invariants]
    exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k k.2⟩
  have hinv : ∀ g, ∀ v ∈ I, ρ g v ∈ I := by
    intro g v hv
    rw [hmem] at hv ⊢
    intro k hk
    have h1 : g⁻¹ * k * g ∈ N := by
      have := hN.conj_mem k hk g⁻¹
      rwa [inv_inv] at this
    have e : ρ g (ρ (g⁻¹ * k * g) v) = ρ k (ρ g v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
        show g * (g⁻¹ * k * g) = k * g by group]
    rw [← e, hv _ h1]
  rcases hU I hinv with hbot | htop
  · exfalso
    let _ : MulAction N W := MulAction.compHom W (ρ.comp N.subtype)
    have hcard : 2 ∣ Nat.card W := by
      rw [natCard_eq_two_pow]
      refine dvd_pow_self 2 fun h0 => ?_
      have h1 : Nat.card W = 1 := by rw [natCard_eq_two_pow, h0, pow_zero]
      have := Finite.one_lt_card_iff_nontrivial.mpr hnt
      omega
    have h0 : (0 : W) ∈ MulAction.fixedPoints N W := fun k => map_zero (ρ k)
    obtain ⟨b, hb, hb0⟩ := hN2.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hcard h0
    have hbI : b ∈ I := (hmem b).mpr fun k hk => hb ⟨k, hk⟩
    rw [hbot, Submodule.mem_bot] at hbI
    exact hb0 hbI.symm
  · exact (hmem w).mp (htop ▸ Submodule.mem_top) k hk

private theorem exists_desc {S : Type} [Group S] (θ : K →* S) (hθ : Function.Surjective θ)
    (ρ : Representation (ZMod 2) K W) (hker : ∀ k, θ k = 1 → ρ k = 1) :
    ∃ σ : Representation (ZMod 2) S W, ∀ k, σ (θ k) = ρ k := by
  have hle : θ.ker ≤ ρ.ker := fun k hk => hker k (MonoidHom.mem_ker.mp hk)
  let e := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  refine ⟨(QuotientGroup.lift θ.ker ρ hle).comp e.symm.toMonoidHom, fun k => ?_⟩
  have he : e.symm (θ k) = (k : K ⧸ θ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show QuotientGroup.lift θ.ker ρ hle (e.symm (θ k)) = ρ k
  rw [he, QuotientGroup.lift_mk]

private theorem isIrreducible_of_comp {S : Type} [Group S] {θ : K →* S}
    {σ : Representation (ZMod 2) S W} {ρ : Representation (ZMod 2) K W} (hσ : ∀ k, σ (θ k) = ρ k)
    (hirr : ρ.IsIrreducible) : σ.IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff] at hirr ⊢
  refine ⟨hirr.1, fun U hU => hirr.2 U fun k u hu => ?_⟩
  rw [← hσ k]
  exact hU (θ k) u hu

theorem eq_self_of_perfect [Finite K] (hK : commutator K = ⊤) {F : Type} [Field F] [Fintype F]
    [CharP F 2] {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (θ : K →* SL(3, F))
    (hθ : Function.Surjective θ) (hker : IsPGroup 2 θ.ker) [Finite W]
    (ρ : Representation (ZMod 2) K W) (hdim : Module.finrank (ZMod 2) W ≤ 2 * f) (k : K)
    (w : W) : ρ k w = w := by
  by_contra hne
  obtain ⟨U, U', hUU', hinv, hUtriv, hmax, g, v, hv, hvU⟩ :=
    SL3Small.exists_section hK ⟨k, w, hne⟩
  have hUinv : ∀ g, ∀ u ∈ U, ρ g u ∈ U := fun g u hu => (hUtriv g u hu).symm ▸ hu
  set σ := SL3Small.sectRep ρ hinv hUinv with hσ
  have hirr : σ.IsIrreducible := SL3Small.sectRep_isIrreducible ρ hinv hUinv hUU' hmax
  obtain ⟨τ, hτ⟩ := exists_desc θ hθ σ fun k hk =>
    LinearMap.ext (eq_self_of_isPGroup hker σ hirr (MonoidHom.mem_ker.mpr hk))
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have : Module.Finite (ZMod 2) ↥U' := Module.Finite.of_finite
  have : Finite (↥U' ⧸ U.comap U'.subtype) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective (U.comap U'.subtype))
  have hdim' : Module.finrank (ZMod 2) (↥U' ⧸ U.comap U'.subtype) ≤ 2 * f :=
    ((Submodule.finrank_quotient_le _).trans (Submodule.finrank_le U')).trans hdim
  refine absurd (two_mul_lt_finrank hF hf τ (isIrreducible_of_comp hτ hirr)
    ⟨θ g, fun h1 => hvU ?_⟩) (not_lt.mpr hdim')
  have h2 : σ g (Submodule.Quotient.mk ⟨v, hv⟩) = Submodule.Quotient.mk ⟨v, hv⟩ := by
    rw [← hτ g, h1, Module.End.one_apply]
  rw [hσ, SL3Small.sectRep_mk, Submodule.Quotient.eq, Submodule.mem_comap] at h2
  simpa [SL3Small.coe_resRep] using h2

end Descent

section Sec

variable {G : Type} [Group G] {K V Z : Subgroup G}

private theorem normal_subgroupOf_of_comm (hZV : Z ≤ V) (hVc : ∀ v ∈ V, ∀ w ∈ V, ⁅v, w⁆ ∈ Z) :
    (Z.subgroupOf V).Normal := ⟨fun z hz v => by
  rw [Subgroup.mem_subgroupOf] at hz ⊢
  have h := hVc v v.2 z (hZV hz)
  have he : ((v * z * v⁻¹ : ↥V) : G) = ⁅(v : G), (z : G)⁆ * z := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [he]
  exact Z.mul_mem h hz⟩

theorem commutator_mem_of_perfect [Finite K] [Finite V]
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hZV : Z ≤ V) (hVc : ∀ v ∈ V, ∀ w ∈ V, ⁅v, w⁆ ∈ Z) (hV2 : ∀ v ∈ V, v * v ∈ Z)
    (hK : ⁅K, K⁆ = K) {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ}
    (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (θ : ↥K →* SL(3, F))
    (hθ : Function.Surjective θ) (hker : IsPGroup 2 θ.ker)
    (hcard : Z.relIndex V ≤ Fintype.card F ^ 2) {k : G} (hk : k ∈ K) {v : G} (hv : v ∈ V) :
    ⁅k, v⁆ ∈ Z := by
  classical
  have hN : (Z.subgroupOf V).Normal := normal_subgroupOf_of_comm hZV hVc
  let _ : CommGroup (V ⧸ Z.subgroupOf V) :=
    { (QuotientGroup.Quotient.group (Z.subgroupOf V)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
              Subgroup.mem_subgroupOf]
            have h := hVc _ (V.inv_mem b.2) _ (V.inv_mem a.2)
            have he : (((a * b)⁻¹ * (b * a) : ↥V) : G) = ⁅((b : G))⁻¹, ((a : G))⁻¹⁆ := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
              group
            rw [he]
            exact h }
  have hmk : ∀ q : Additive (V ⧸ Z.subgroupOf V), ∃ v : ↥V,
      q = Additive.ofMul (v : V ⧸ Z.subgroupOf V) := fun q => by
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    exact ⟨v, by rw [hv]; rfl⟩
  have h2 : ∀ q : Additive (V ⧸ Z.subgroupOf V), 2 • q = 0 := by
    intro q
    obtain ⟨v, rfl⟩ := hmk q
    rw [← ofMul_pow, ← ofMul_one, ← QuotientGroup.mk_pow]
    congr 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, pow_two]
    exact hV2 _ v.2
  let _ : Module (ZMod 2) (Additive (V ⧸ Z.subgroupOf V)) := AddCommGroup.zmodModule h2
  have : Finite (Additive (V ⧸ Z.subgroupOf V)) :=
    Finite.of_surjective (fun v : ↥V => Additive.ofMul (v : V ⧸ Z.subgroupOf V)) fun q => by
      obtain ⟨v, rfl⟩ := hmk q
      exact ⟨v, rfl⟩
  let cj : ↥K → (↥V →* ↥V) := fun k =>
    { toFun := fun v => ⟨(k : G) * v * (k : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hKV k.2) v).mp v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hcj : ∀ (k : ↥K) (v : ↥V), ((cj k v : ↥V) : G) = (k : G) * v * (k : G)⁻¹ :=
    fun k v => rfl
  let cq : ↥K → (V ⧸ Z.subgroupOf V →* V ⧸ Z.subgroupOf V) := fun k =>
    QuotientGroup.map (Z.subgroupOf V) (Z.subgroupOf V) (cj k) (fun z hz => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hcj]
      exact (Subgroup.mem_normalizer_iff.mp (hKZ k.2) z).mp (Subgroup.mem_subgroupOf.mp hz))
  have hcq : ∀ (k : ↥K) (v : ↥V), cq k (v : V ⧸ Z.subgroupOf V) =
      ((cj k v : ↥V) : V ⧸ Z.subgroupOf V) := fun k v => rfl
  let act : ↥K →* (Additive (V ⧸ Z.subgroupOf V) →ₗ[ZMod 2] Additive (V ⧸ Z.subgroupOf V)) :=
    { toFun := fun k => (MonoidHom.toAdditive (cq k)).toZModLinearMap 2
      map_one' := by
        refine LinearMap.ext fun q => ?_
        obtain ⟨v, rfl⟩ := hmk q
        show Additive.ofMul (cq 1 (v : V ⧸ Z.subgroupOf V)) = Additive.ofMul _
        rw [hcq]
        congr 2
        exact Subtype.ext (by rw [hcj]; simp)
      map_mul' := fun k k' => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨v, rfl⟩ := hmk q
        show Additive.ofMul (cq (k * k') (v : V ⧸ Z.subgroupOf V)) =
          Additive.ofMul (cq k (cq k' (v : V ⧸ Z.subgroupOf V)))
        rw [hcq, hcq, hcq]
        congr 2
        exact Subtype.ext (by rw [hcj, hcj, hcj]; simp [mul_assoc]) }
  have hact : ∀ (k : ↥K) (v : ↥V), act k (Additive.ofMul (v : V ⧸ Z.subgroupOf V)) =
      Additive.ofMul ((cj k v : ↥V) : V ⧸ Z.subgroupOf V) := fun k v => rfl
  have hZconj : ∀ w ∈ V, ∀ z ∈ Z, w * z * w⁻¹ ∈ Z := by
    intro w hw z hz
    have e : w * z * w⁻¹ = ⁅w, z⁆ * z := by rw [commutatorElement_def]; group
    rw [e]
    exact Z.mul_mem (hVc w hw z (hZV hz)) hz
  have hfix : ∀ (k : ↥K) (v : ↥V), act k (Additive.ofMul (v : V ⧸ Z.subgroupOf V)) =
      Additive.ofMul (v : V ⧸ Z.subgroupOf V) → ⁅(k : G), (v : G)⁆ ∈ Z := by
    intro k v h
    rw [hact, Additive.ofMul.injective.eq_iff, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, Subgroup.coe_inv, hcj] at h
    have e : ⁅(k : G), (v : G)⁆ = (v : G) * (((k : G) * v * (k : G)⁻¹)⁻¹ * v)⁻¹ * (v : G)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact hZconj _ v.2 _ (Z.inv_mem h)
  have hdim : Module.finrank (ZMod 2) (Additive (V ⧸ Z.subgroupOf V)) ≤ 2 * f := by
    have h1 : Nat.card (Additive (V ⧸ Z.subgroupOf V)) = Z.relIndex V := rfl
    rw [natCard_eq_two_pow] at h1
    rw [hF, ← pow_mul, mul_comm f 2, ← h1] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  have hL : commutator ↥K = ⊤ := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hK)
  exact hfix ⟨k, hk⟩ ⟨v, hv⟩ (eq_self_of_perfect hL hF hf θ hθ hker act hdim _ _)

end Sec

end CFSG.Quasithin.MS93.S4A.W441
