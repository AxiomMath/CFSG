module

public import CFSG.Quasithin.Background.G105Struct
public import CFSG.Quasithin.Background.G10FourFive
public import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.Quasithin.G105

open CFSG.Open CFSG.Quasithin.G11 Equiv

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_zero' [Finite V] (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, zero_smul]

theorem not_dvd6_of_odd_ge4 {n : ℕ} (h : n ∣ 6) (ho : Odd n) (h4 : 4 ≤ n) : False := by
  have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) h
  obtain ⟨k, rfl⟩ := ho
  have hk1 : k ≤ 2 := by omega
  have hk2 : 2 ≤ k := by omega
  obtain rfl : k = 2 := by omega
  norm_num at h

theorem eq_nine_of_dvd36 {n : ℕ} (h : n ∣ 36) (ho : Odd n) (h4 : 4 ≤ n) : n = 9 := by
  have hle : n ≤ 36 := Nat.le_of_dvd (by norm_num) h
  obtain ⟨k, rfl⟩ := ho
  have hk1 : 2 ≤ k := by omega
  have hk2 : k ≤ 17 := by omega
  interval_cases k <;> omega

theorem inf_eq_bot_of_irr [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)}
    {v₁ : V} {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)}
    (hG : G101Hyp B Γ v₁ W X X₀) {U : Submodule (ZMod 2) V} (hUirr : IsIrr Γ U)
    (hU2 : Module.finrank (ZMod 2) U = 2) (hV4 : Module.finrank (ZMod 2) V = 4)
    (hO2 : pCoreOf 2 Γ = ⊥) : U ⊓ B.orthogonal U = ⊥ := by
  have hnd : B.Nondegenerate := hG.nondegenerate'
  have hrefl : B.IsRefl := hG.isRefl
  have hUinv : Invariant Γ U := hUirr.1
  have hU'inv : Invariant Γ (B.orthogonal U) :=
    Invariant.orthogonal (fun k hk v w => hG.isometry k hk v w) hUinv
  rcases hUirr.eq_bot_or_eq (hUinv.inf hU'inv) inf_le_left with h | h
  · exact h
  · exfalso
    have hle : U ≤ B.orthogonal U := inf_eq_left.1 h
    have hUU' : B.orthogonal U = U :=
      (Submodule.eq_of_le_of_finrank_eq hle (by
        rw [LinearMap.BilinForm.finrank_orthogonal hnd U, hV4, hU2])).symm
    have hfix : ∀ g ∈ Γ, (∀ u ∈ U, g u = u) → ∀ v, g v - v ∈ U := by
      intro g hg hgU v
      have h1 : g v - v ∈ B.orthogonal U := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro n hn
        have h2 : B n (g v) = B n v := by
          have := hG.isometry g hg n v
          rwa [hgU n hn] at this
        rw [map_sub, h2]
        exact sub_self _
      rwa [hUU'] at h1
    have hsq : ∀ g ∈ Γ, (∀ u ∈ U, g u = u) → ∀ v, g (g v) = v := by
      intro g hg hgU v
      have hw : g (g v - v) = g v - v := hgU _ (hfix g hg hgU v)
      rw [map_sub] at hw
      calc g (g v) = (g (g v) - g v) + g v := by abel
        _ = (g v - v) + g v := by rw [hw]
        _ = (g v + g v) - v := by abel
        _ = 0 - v := by rw [add_self_zero' (g v)]
        _ = v := by
          rw [← add_self_zero' v]
          abel
    have hNn : ∀ γ ∈ Γ, ∀ n ∈ centralizerOn Γ U, γ * n * γ⁻¹ ∈ centralizerOn Γ U := by
      intro γ hγ n hn
      rw [mem_centralizerOn] at hn ⊢
      refine ⟨Γ.mul_mem (Γ.mul_mem hγ hn.1) (Γ.inv_mem hγ), fun u hu => ?_⟩
      have h1 : γ⁻¹ u ∈ U := hUinv γ⁻¹ (Γ.inv_mem hγ) u hu
      have h2 : n (γ⁻¹ u) = γ⁻¹ u := hn.2 _ h1
      show γ (n (γ⁻¹ u)) = u
      rw [h2]
      exact γ.apply_symm_apply u
    have hN2 : ∀ n ∈ centralizerOn Γ U, n * n = 1 := by
      intro n hn
      rw [mem_centralizerOn] at hn
      apply LinearEquiv.ext
      intro v
      exact hsq n hn.1 hn.2 v
    have hkerN : ∀ n ∈ centralizerOn Γ U, n = 1 :=
      eq_one_of_sq_normal hO2 (fun n hn => (mem_centralizerOn.1 hn).1) hNn hN2
    have hinj : Function.Injective (restrictHom Γ U hUinv) := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have hgU : ∀ u ∈ U, (g : GLV V) u = u := restrictHom_eq_one_iff.1 hg
      have hg1 : (g : GLV V) = 1 := hkerN _ (mem_centralizerOn.2 ⟨g.2, hgU⟩)
      exact Subtype.ext hg1
    have hcard6 : Nat.card ↥Γ ∣ 6 := by
      have := Subgroup.card_dvd_of_injective (restrictHom Γ U hUinv) hinj
      rwa [CFSG.Quasithin.g10Four_card_linearEquiv_two U hU2] at this
    have hn1 : (MulAction.stabilizer Γ v₁).index ∣ 6 :=
      (Subgroup.index_dvd_card _).trans hcard6
    have hn2 : 4 ≤ (MulAction.stabilizer Γ v₁).index := by
      have := finrank_le_index hG
      rwa [hV4] at this
    exact not_dvd6_of_odd_ge4 hn1 hG.odd_index hn2

noncomputable def iotaOf [Finite V] {Γ : Subgroup (GLV V)} {U U' : Submodule (ZMod 2) V}
    (hU2 : Module.finrank (ZMod 2) U = 2) (hU'2 : Module.finrank (ZMod 2) U' = 2)
    (hUinv : Invariant Γ U) (hU'inv : Invariant Γ U') : ↥Γ →* G0 :=
  ((toPerm3 U hU2).prodMap (toPerm3 U' hU'2)).comp
    ((restrictHom Γ U hUinv).prod (restrictHom Γ U' hU'inv))

theorem iotaOf_injective [Finite V] {Γ : Subgroup (GLV V)} {U U' : Submodule (ZMod 2) V}
    (hU2 : Module.finrank (ZMod 2) U = 2) (hU'2 : Module.finrank (ZMod 2) U' = 2)
    (hUinv : Invariant Γ U) (hU'inv : Invariant Γ U') (hc : IsCompl U U') :
    Function.Injective (iotaOf hU2 hU'2 hUinv hU'inv) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : restrictHom Γ U hUinv g = 1 :=
    (toPerm3_injective U hU2) (by rw [map_one]; exact congrArg Prod.fst hg)
  have h2 : restrictHom Γ U' hU'inv g = 1 :=
    (toPerm3_injective U' hU'2) (by rw [map_one]; exact congrArg Prod.snd hg)
  have f1 := restrictHom_eq_one_iff.1 h1
  have f2 := restrictHom_eq_one_iff.1 h2
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ U ⊔ U' := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  show (g : GLV V) (u + w) = u + w
  rw [map_add, f1 u hu, f2 w hw]

theorem iotaOf_injective_prod [Finite V] {Γ : Subgroup (GLV V)} {U U' : Submodule (ZMod 2) V}
    (hU2 : Module.finrank (ZMod 2) U = 2) (hU'2 : Module.finrank (ZMod 2) U' = 2)
    (hUinv : Invariant Γ U) (hU'inv : Invariant Γ U') (hc : IsCompl U U') :
    Function.Injective ((restrictHom Γ U hUinv).prod (restrictHom Γ U' hU'inv)) := by
  intro a b hab
  apply iotaOf_injective hU2 hU'2 hUinv hU'inv hc
  show ((toPerm3 U hU2).prodMap (toPerm3 U' hU'2))
      ((restrictHom Γ U hUinv).prod (restrictHom Γ U' hU'inv) a) =
    ((toPerm3 U hU2).prodMap (toPerm3 U' hU'2))
      ((restrictHom Γ U hUinv).prod (restrictHom Γ U' hU'inv) b)
  rw [hab]

theorem pCore3_eq {Γ : Subgroup (GLV V)} (ι : ↥Γ →* G0) (hι : Function.Injective ι) :
    CFSG.pCore 3 ↥Γ = E9.comap ι := by
  apply le_antisymm
  · unfold CFSG.pCore
    refine sSup_le ?_
    rintro K ⟨-, hKp⟩ k hk
    obtain ⟨j, hj⟩ := hKp ⟨k, hk⟩
    have hk' : k ^ (3 ^ j) = 1 := by
      have := congrArg (fun x : K => (x : ↥Γ)) hj
      simpa using this
    have : ι k ^ (3 ^ j) = 1 := by
      rw [← map_pow, hk', map_one]
    exact mem_E9_of_pow_three_pow j this
  · have hnorm : (E9.comap ι).Normal := E9_normal.comap ι
    have hpg : IsPGroup 3 (E9.comap ι) := by
      intro k
      refine ⟨1, ?_⟩
      have hk : ι (k : ↥Γ) ∈ E9 := k.2
      rw [pow_one]
      apply Subtype.ext
      have h3 : ι ((k : ↥Γ) ^ 3) = ι 1 := by
        rw [map_pow, map_one]
        exact pow_three_of_mem_E9 hk
      have := hι h3
      simpa using this
    exact le_sSup ⟨hnorm, hpg⟩

theorem E9_le_range {Δ : Type} [Group Δ] [Finite Δ] (ι : Δ →* G0)
    (hι : Function.Injective ι) (h9 : 9 ∣ Nat.card Δ) : E9 ≤ ι.range := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hR : 3 ^ 2 ∣ Nat.card ι.range := by
    rw [Nat.card_congr (MonoidHom.ofInjective hι).toEquiv.symm]
    norm_num
    exact h9
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 hR
  have hP' : Nat.card (P.map ι.range.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hP]
    norm_num
  have hle : P.map ι.range.subtype ≤ E9 := by
    intro x hx
    obtain ⟨p, hpP, rfl⟩ := Subgroup.mem_map.1 hx
    apply mem_E9_of_pow_three_pow 2
    have h3 : (⟨p, hpP⟩ : P) ^ Nat.card P = 1 := pow_card_eq_one'
    have h4 : (p : ↥ι.range) ^ Nat.card P = 1 := congrArg (fun q : ↥P => (q : ↥ι.range)) h3
    have h2 : (ι.range.subtype p) ^ Nat.card P = 1 :=
      congrArg (fun q : ↥ι.range => (q : G0)) h4
    rw [hP] at h2
    exact h2
  have hcardE9 : Nat.card E9 ≤ Nat.card (P.map ι.range.subtype) := by
    rw [card_E9, hP']
  have heq : P.map ι.range.subtype = E9 := Subgroup.eq_of_le_of_card_ge hle hcardE9
  intro e he
  rw [← heq] at he
  obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.1 he
  exact p.2

theorem inducesTransvection_fst [Finite V] {Γ : Subgroup (GLV V)} {U U' : Submodule (ZMod 2) V}
    (hc : IsCompl U U') (hU2 : Module.finrank (ZMod 2) U = 2)
    (hU'2 : Module.finrank (ZMod 2) U' = 2) (hUinv : Invariant Γ U) (hU'inv : Invariant Γ U')
    {g : ↥Γ} {τ : Perm (Fin 3)} (hτ : Perm.sign τ = -1)
    (h : iotaOf hU2 hU'2 hUinv hU'inv g = (τ, 1)) :
    ∃ c : V, InducesTransvection (g : GLV V) ⊤ c := by
  have h1 : toPerm3 U hU2 (restrictHom Γ U hUinv g) = τ := congrArg Prod.fst h
  have h2 : toPerm3 U' hU'2 (restrictHom Γ U' hU'inv g) = 1 := congrArg Prod.snd h
  have hr2 : restrictHom Γ U' hU'inv g = 1 :=
    (toPerm3_injective U' hU'2) (by rw [h2, map_one])
  have hgU' : ∀ w ∈ U', (g : GLV V) w = w := restrictHom_eq_one_iff.1 hr2
  have hh2 : restrictHom Γ U hUinv g * restrictHom Γ U hUinv g = 1 :=
    (toPerm3_injective U hU2) (by rw [map_mul, map_one, h1]; exact perm3_sq_of_sign_neg hτ)
  have hh1 : restrictHom Γ U hUinv g ≠ 1 := by
    intro h'
    rw [h', map_one] at h1
    rw [← h1] at hτ
    exact absurd hτ (by decide)
  have hgh : ∀ u : U, (g : GLV V) (u : V) = ((restrictHom Γ U hUinv g u : U) : V) :=
    fun u => (coe_restrictHom g u).symm
  exact inducesTransvection_of_split hc hU2 hgU' hgh hh2 hh1

theorem inducesTransvection_snd [Finite V] {Γ : Subgroup (GLV V)} {U U' : Submodule (ZMod 2) V}
    (hc : IsCompl U U') (hU2 : Module.finrank (ZMod 2) U = 2)
    (hU'2 : Module.finrank (ZMod 2) U' = 2) (hUinv : Invariant Γ U) (hU'inv : Invariant Γ U')
    {g : ↥Γ} {τ : Perm (Fin 3)} (hτ : Perm.sign τ = -1)
    (h : iotaOf hU2 hU'2 hUinv hU'inv g = (1, τ)) :
    ∃ c : V, InducesTransvection (g : GLV V) ⊤ c := by
  have h1 : toPerm3 U hU2 (restrictHom Γ U hUinv g) = 1 := congrArg Prod.fst h
  have h2 : toPerm3 U' hU'2 (restrictHom Γ U' hU'inv g) = τ := congrArg Prod.snd h
  have hr1 : restrictHom Γ U hUinv g = 1 :=
    (toPerm3_injective U hU2) (by rw [h1, map_one])
  have hgU : ∀ u ∈ U, (g : GLV V) u = u := restrictHom_eq_one_iff.1 hr1
  have hh2 : restrictHom Γ U' hU'inv g * restrictHom Γ U' hU'inv g = 1 :=
    (toPerm3_injective U' hU'2) (by rw [map_mul, map_one, h2]; exact perm3_sq_of_sign_neg hτ)
  have hh1 : restrictHom Γ U' hU'inv g ≠ 1 := by
    intro h'
    rw [h', map_one] at h2
    rw [← h2] at hτ
    exact absurd hτ (by decide)
  have hgh : ∀ w : U', (g : GLV V) (w : V) = ((restrictHom Γ U' hU'inv g w : U') : V) :=
    fun w => (coe_restrictHom g w).symm
  exact inducesTransvection_of_split hc.symm hU'2 hgU hgh hh2 hh1

theorem closure_eq_of_iota [Finite V] {Γ : Subgroup (GLV V)} {U U' : Submodule (ZMod 2) V}
    (hc : IsCompl U U') (hU2 : Module.finrank (ZMod 2) U = 2)
    (hU'2 : Module.finrank (ZMod 2) U' = 2) (hUinv : Invariant Γ U) (hU'inv : Invariant Γ U')
    (hιinj : Function.Injective (iotaOf hU2 hU'2 hUinv hU'inv))
    (hιsurj : Function.Surjective (iotaOf hU2 hU'2 hUinv hU'inv)) :
    Γ = Subgroup.closure {g | g ∈ Γ ∧ ∃ c : V, InducesTransvection g ⊤ c} := by
  set ι := iotaOf hU2 hU'2 hUinv hU'inv with hι
  let e : ↥Γ ≃* G0 := MulEquiv.ofBijective ι ⟨hιinj, hιsurj⟩
  set S : Set (GLV V) := {g | g ∈ Γ ∧ ∃ c : V, InducesTransvection g ⊤ c} with hS
  let χ₁ : Perm (Fin 3) →* GLV V :=
    (Subgroup.subtype Γ).comp
      ((e.symm.toMonoidHom).comp (MonoidHom.inl (Perm (Fin 3)) (Perm (Fin 3))))
  let χ₂ : Perm (Fin 3) →* GLV V :=
    (Subgroup.subtype Γ).comp
      ((e.symm.toMonoidHom).comp (MonoidHom.inr (Perm (Fin 3)) (Perm (Fin 3))))
  have hχ₁ : ∀ τ : Perm (Fin 3), Perm.sign τ = -1 → χ₁ τ ∈ Subgroup.closure S := by
    intro τ hτ
    apply Subgroup.subset_closure
    have hι' : ι (e.symm (τ, 1)) = (τ, 1) := e.apply_symm_apply (τ, 1)
    obtain ⟨c, hc'⟩ := inducesTransvection_fst hc hU2 hU'2 hUinv hU'inv hτ hι'
    exact ⟨(e.symm (τ, 1)).2, c, hc'⟩
  have hχ₂ : ∀ τ : Perm (Fin 3), Perm.sign τ = -1 → χ₂ τ ∈ Subgroup.closure S := by
    intro τ hτ
    apply Subgroup.subset_closure
    have hι' : ι (e.symm (1, τ)) = (1, τ) := e.apply_symm_apply (1, τ)
    obtain ⟨c, hc'⟩ := inducesTransvection_snd hc hU2 hU'2 hUinv hU'inv hτ hι'
    exact ⟨(e.symm (1, τ)).2, c, hc'⟩
  have hK₁ : (⊤ : Subgroup (Perm (Fin 3))) ≤ (Subgroup.closure S).comap χ₁ := by
    rw [← Equiv.Perm.closure_isSwap]
    apply (Subgroup.closure_le _).2
    intro σ hσ
    exact hχ₁ σ (Equiv.Perm.IsSwap.sign_eq hσ)
  have hK₂ : (⊤ : Subgroup (Perm (Fin 3))) ≤ (Subgroup.closure S).comap χ₂ := by
    rw [← Equiv.Perm.closure_isSwap]
    apply (Subgroup.closure_le _).2
    intro σ hσ
    exact hχ₂ σ (Equiv.Perm.IsSwap.sign_eq hσ)
  have hsurj_all : ∀ γ : GLV V, γ ∈ Γ → γ ∈ Subgroup.closure S := by
    intro γ hγ
    have hfac : e.symm (((ι ⟨γ, hγ⟩).1, 1) : G0) * e.symm ((1, (ι ⟨γ, hγ⟩).2) : G0) =
        ⟨γ, hγ⟩ := by
      rw [← map_mul]
      have hpair : (((ι ⟨γ, hγ⟩).1, 1) * (1, (ι ⟨γ, hγ⟩).2) : G0) = ι ⟨γ, hγ⟩ :=
        Prod.ext (by simp) (by simp)
      rw [hpair]
      exact e.symm_apply_apply ⟨γ, hγ⟩
    have key : γ = χ₁ (ι ⟨γ, hγ⟩).1 * χ₂ (ι ⟨γ, hγ⟩).2 := by
      have h := congrArg Subtype.val hfac
      exact h.symm
    rw [key]
    exact Subgroup.mul_mem _ ((hK₁ (Subgroup.mem_top _)) : χ₁ _ ∈ Subgroup.closure S)
      ((hK₂ (Subgroup.mem_top _)) : χ₂ _ ∈ Subgroup.closure S)
  apply le_antisymm
  · intro γ hγ
    exact hsurj_all γ hγ
  · exact (Subgroup.closure_le _).2 fun g hg => hg.1

theorem caseB_conclusion [Finite V] {Γ : Subgroup (GLV V)} (ι : ↥Γ →* G0)
    (hιinj : Function.Injective ι) (hE9 : E9 ≤ ι.range)
    (hB : ∀ g : ↥Γ, Perm.sign (ι g).1 = Perm.sign (ι g).2)
    {y : GLV V} (hyΓ : y ∈ Γ) (hyy : y * y = 1) (hy1 : y ≠ 1)
    (hψ1 : Perm.sign (ι ⟨y, hyΓ⟩).1 = -1) (hψ2 : Perm.sign (ι ⟨y, hyΓ⟩).2 = -1) :
    IsElemAbelian 3 (pCoreOf 3 Γ) ∧ Nat.card ↥(pCoreOf 3 Γ) = 9 ∧
      ∃ t ∈ Γ, t * t = 1 ∧ t ≠ 1 ∧ Γ = pCoreOf 3 Γ ⊔ Subgroup.zpowers t ∧
        ∀ x ∈ pCoreOf 3 Γ, t * x * t⁻¹ = x⁻¹ := by
  have hcore : CFSG.pCore 3 ↥Γ = E9.comap ι := pCore3_eq ι hιinj
  have hmem : ∀ (g : GLV V) (hg : g ∈ Γ), g ∈ pCoreOf 3 Γ ↔ ι ⟨g, hg⟩ ∈ E9 := by
    intro g hg
    unfold pCoreOf
    rw [hcore, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxg⟩
      have hx' : x = ⟨g, hg⟩ := Subtype.ext hxg
      rw [hx'] at hx
      exact hx
    · intro h
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hsub : ∀ g : GLV V, g ∈ pCoreOf 3 Γ → g ∈ Γ := by
    intro g hg
    unfold pCoreOf at hg
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hg
    exact x.2
  have hcommute : ∀ a ∈ pCoreOf 3 Γ, ∀ b ∈ pCoreOf 3 Γ, a * b = b * a := by
    intro a ha b hb
    have ha' := (hmem a (hsub a ha)).1 ha
    have hb' := (hmem b (hsub b hb)).1 hb
    have h := mul_comm_of_mem_E9 ha' hb'
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (hιinj h)
  have hpow3 : ∀ a ∈ pCoreOf 3 Γ, a ^ 3 = 1 := by
    intro a ha
    have ha' := (hmem a (hsub a ha)).1 ha
    have h := hιinj (show ι (⟨a, hsub a ha⟩ ^ 3) = ι 1 by
      rw [map_pow, map_one]
      exact pow_three_of_mem_E9 ha')
    exact congrArg Subtype.val h
  have hcard : Nat.card ↥(pCoreOf 3 Γ) = 9 := by
    have hE' : Nat.card ↥(E9.comap ι) = 9 := by
      have hbij : Function.Bijective
          (fun x : ↥(E9.comap ι) => (⟨ι (x : ↥Γ), x.2⟩ : ↥E9)) := by
        constructor
        · intro x y hxy
          apply Subtype.ext
          apply hιinj
          exact congrArg Subtype.val hxy
        · intro e
          obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 (hE9 e.2)
          refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
          rw [Subgroup.mem_comap, hg]
          exact e.2
      rw [← card_E9]
      exact Nat.card_congr (Equiv.ofBijective _ hbij)
    have hmapcard : Nat.card ↥(pCoreOf 3 Γ) = Nat.card ↥(E9.comap ι) := by
      unfold pCoreOf
      rw [hcore]
      exact Subgroup.card_map_of_injective (Subgroup.subtype_injective Γ)
    rw [hmapcard, hE']
  have hΓ : Γ = pCoreOf 3 Γ ⊔ Subgroup.zpowers y := by
    apply le_antisymm
    · intro g hg
      have hs := hB ⟨g, hg⟩
      rcases sign_pair_cases (ι ⟨g, hg⟩) with h | h | h | h
      · exact Subgroup.mem_sup_left ((hmem g hg).2 (mem_E9.2 h))
      ·
        have hgy : g * y ∈ Γ := Γ.mul_mem hg hyΓ
        have hprod : ι ⟨g * y, hgy⟩ = ι ⟨g, hg⟩ * ι ⟨y, hyΓ⟩ := by
          rw [← map_mul]
          rfl
        have hE : ι ⟨g * y, hgy⟩ ∈ E9 := by
          rw [mem_E9, hprod, Prod.fst_mul, Prod.snd_mul, map_mul, map_mul, h.1, h.2, hψ1, hψ2]
          exact ⟨by decide, by decide⟩
        have hgy' : g * y ∈ pCoreOf 3 Γ := (hmem (g * y) hgy).2 hE
        have hmul := Subgroup.mul_mem_sup hgy' ((Subgroup.zpowers y).inv_mem
          (Subgroup.mem_zpowers y))
        rwa [mul_inv_cancel_right] at hmul
      · exact absurd hs (by rw [h.1, h.2]; decide)
      · exact absurd hs (by rw [h.1, h.2]; decide)
    · exact sup_le (fun g hg => hsub g hg) (Subgroup.zpowers_le.2 hyΓ)
  have hconj : ∀ x ∈ pCoreOf 3 Γ, y * x * y⁻¹ = x⁻¹ := by
    intro x hx
    have hx' := (hmem x (hsub x hx)).1 hx
    have key : ι (⟨y, hyΓ⟩ * ⟨x, hsub x hx⟩ * ⟨y, hyΓ⟩⁻¹) = ι (⟨x, hsub x hx⟩⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_inv]
      apply Prod.ext
      · simp only [Prod.fst_mul, Prod.fst_inv]
        exact perm3_conj_inv hψ1 (mem_E9.1 hx').1
      · simp only [Prod.snd_mul, Prod.snd_inv]
        exact perm3_conj_inv hψ2 (mem_E9.1 hx').2
    exact congrArg Subtype.val (hιinj key)
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hcommute a.1 a.2 b.1 b.2)⟩⟩, fun x hx => hpow3 x hx⟩,
    hcard, y, hyΓ, hyy, hy1, hΓ, hconj⟩

theorem ne_bot_of_proper [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)}
    {v₁ : V} {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)} (hG : G101Hyp B Γ v₁ W X X₀)
    {U : Submodule (ZMod 2) V} (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤) : Γ ≠ ⊥ := by
  intro hΓ
  have hle : Submodule.span (ZMod 2) (MulAction.orbit Γ v₁) ≤
      Submodule.span (ZMod 2) {v₁} := by
    apply Submodule.span_mono
    rintro _ ⟨γ, rfl⟩
    have h1 : (γ : GLV V) = 1 := (Subgroup.eq_bot_iff_forall Γ).1 hΓ γ.1 γ.2
    show (γ : GLV V) v₁ ∈ ({v₁} : Set V)
    rw [h1]
    exact Set.mem_singleton _
  rw [hG.span_orbit] at hle
  have h1 := Submodule.finrank_mono hle
  rw [finrank_top, finrank_span_singleton hG.point] at h1
  have h2 : 0 < Module.finrank (ZMod 2) U := by
    apply Module.finrank_pos_iff_exists_ne_zero.2
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    exact ⟨⟨u, hu⟩, fun h => hu0 (congrArg Subtype.val h)⟩
  have h3 : Module.finrank (ZMod 2) U < Module.finrank (ZMod 2) V := Submodule.finrank_lt hU1
  omega

theorem exists_irr_of_not_isIrr [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    {Γ : Subgroup (GLV V)} {v₁ : V} {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)}
    (hG : G101Hyp B Γ v₁ W X X₀) (hne : ¬ IsIrr Γ ⊤) :
    ∃ U : Submodule (ZMod 2) V, IsIrr Γ U ∧ U ≠ ⊤ := by
  by_contra hcon
  push Not at hcon
  apply hne
  have htop : (⊤ : Submodule (ZMod 2) V) ≠ ⊥ := by
    intro h
    apply hG.point
    have hv : v₁ ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← h]
      exact Submodule.mem_top
    exact (Submodule.mem_bot _).1 hv
  refine ⟨invariant_top Γ, bot_lt_iff_ne_bot.2 htop, fun J hJ hbot hJtop => ?_⟩
  by_contra hcon2
  push Not at hcon2
  obtain ⟨U, hUJ, hUirr⟩ := exists_isIrr_le hJ hcon2.1
  have hUne : U ≠ ⊤ := fun h => hcon2.2 (top_le_iff.1 (h ▸ hUJ))
  exact hUne (hcon U hUirr)

theorem g105_core [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)}
    {v₁ : V} {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)} (hG : G101Hyp B Γ v₁ W X X₀)
    {U : Submodule (ZMod 2) V} (hUirr : IsIrr Γ U) (hU2 : Module.finrank (ZMod 2) U = 2)
    (hV4 : Module.finrank (ZMod 2) V = 4) (hO2 : pCoreOf 2 Γ = ⊥) :
    (Nonempty (↥Γ ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
        Γ = Subgroup.closure {g | g ∈ Γ ∧ ∃ c : V, InducesTransvection g ⊤ c}) ∨
      (IsElemAbelian 3 (pCoreOf 3 Γ) ∧ Nat.card ↥(pCoreOf 3 Γ) = 9 ∧
        ∃ t ∈ Γ, t * t = 1 ∧ t ≠ 1 ∧ Γ = pCoreOf 3 Γ ⊔ Subgroup.zpowers t ∧
          ∀ x ∈ pCoreOf 3 Γ, t * x * t⁻¹ = x⁻¹) := by
  have hnd : B.Nondegenerate := hG.nondegenerate'
  have hrefl : B.IsRefl := hG.isRefl
  have hUinv : Invariant Γ U := hUirr.1
  have hU'inv : Invariant Γ (B.orthogonal U) :=
    Invariant.orthogonal (fun k hk v w => hG.isometry k hk v w) hUinv
  have hU'2 : Module.finrank (ZMod 2) (B.orthogonal U) = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd U, hV4, hU2]
  have hinf := inf_eq_bot_of_irr hG hUirr hU2 hV4 hO2
  have hc : IsCompl U (B.orthogonal U) := isCompl_orthogonal_of_inf hG hinf
  have hU_ne_top : U ≠ ⊤ := by
    intro h
    rw [h, finrank_top, hV4] at hU2
    norm_num at hU2
  have hU'_ne_top : B.orthogonal U ≠ ⊤ := by
    intro h
    rw [h, finrank_top, hV4] at hU'2
    norm_num at hU'2
  have hv1U : v₁ ∉ U := not_mem_of_invariant hG hUinv hU_ne_top
  have hv1U' : v₁ ∉ B.orthogonal U := not_mem_of_invariant hG hU'inv hU'_ne_top
  have hρinj := iotaOf_injective_prod hU2 hU'2 hUinv hU'inv hc
  have hιinj := iotaOf_injective hU2 hU'2 hUinv hU'inv hc
  have hdvd36 : Nat.card ↥Γ ∣ 36 := by
    have := Subgroup.card_dvd_of_injective _ hρinj
    rw [Nat.card_prod, CFSG.Quasithin.g10Four_card_linearEquiv_two U hU2,
      CFSG.Quasithin.g10Four_card_linearEquiv_two (B.orthogonal U) hU'2] at this
    exact this
  have h9 : 9 ∣ Nat.card ↥Γ := by
    have hn9 : (MulAction.stabilizer Γ v₁).index = 9 := by
      apply eq_nine_of_dvd36 ((Subgroup.index_dvd_card _).trans hdvd36) hG.odd_index
      have := finrank_le_index hG
      rwa [hV4] at this
    rw [← hn9]
    exact Subgroup.index_dvd_card _
  have hE9 : E9 ≤ (iotaOf hU2 hU'2 hUinv hU'inv).range := E9_le_range _ hιinj h9
  have hXne : X₀ ≠ X := by
    intro h
    have hr := hG.rank
    rw [h, Subgroup.relIndex_self, Nat.log_one_right] at hr
    have hW := hG.finrank_isotropic_le
    rw [hV4] at hW hr
    omega
  obtain ⟨y, hyX, hyX₀⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hG.X₀_le hXne)
  have hyΓ : y ∈ Γ := hG.X_le hyX
  have hyy : y * y = 1 := hG.X_sq y hyX
  have hy1 : y ≠ 1 := fun h => hyX₀ (h ▸ X₀.one_mem)
  have hψsq : (iotaOf hU2 hU'2 hUinv hU'inv ⟨y, hyΓ⟩) *
      (iotaOf hU2 hU'2 hUinv hU'inv ⟨y, hyΓ⟩) = 1 := by
    rw [← map_mul]
    have hyy' : (⟨y, hyΓ⟩ : ↥Γ) * ⟨y, hyΓ⟩ = 1 := Subtype.ext hyy
    rw [hyy', map_one]
  have hψ1sq := congrArg Prod.fst hψsq
  have hψ2sq := congrArg Prod.snd hψsq
  have hne1 : Perm.sign (iotaOf hU2 hU'2 hUinv hU'inv ⟨y, hyΓ⟩).1 ≠ 1 := by
    intro hs
    have h1 : (iotaOf hU2 hU'2 hUinv hU'inv ⟨y, hyΓ⟩).1 = 1 :=
      perm3_eq_one_of_sq hψ1sq hs
    have hres : restrictHom Γ U hUinv ⟨y, hyΓ⟩ = 1 :=
      (toPerm3_injective U hU2) (by rw [map_one]; exact h1)
    have hyU : ∀ u ∈ U, (y : GLV V) u = u := restrictHom_eq_one_iff.1 hres
    apply hv1U'
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact hrefl _ _ (hG.centralizer_le y hyX hyX₀ n (hyU n hn))
  have hne2 : Perm.sign (iotaOf hU2 hU'2 hUinv hU'inv ⟨y, hyΓ⟩).2 ≠ 1 := by
    intro hs
    have h2 : (iotaOf hU2 hU'2 hUinv hU'inv ⟨y, hyΓ⟩).2 = 1 :=
      perm3_eq_one_of_sq hψ2sq hs
    have hres : restrictHom Γ (B.orthogonal U) hU'inv ⟨y, hyΓ⟩ = 1 :=
      (toPerm3_injective (B.orthogonal U) hU'2) (by rw [map_one]; exact h2)
    have hyU' : ∀ w ∈ B.orthogonal U, (y : GLV V) w = w := restrictHom_eq_one_iff.1 hres
    apply hv1U
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl U,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact hrefl _ _ (hG.centralizer_le y hyX hyX₀ n (hyU' n hn))
  have hψ1 := (Int.units_eq_one_or _).resolve_left hne1
  have hψ2 := (Int.units_eq_one_or _).resolve_left hne2
  have hψR : iotaOf hU2 hU'2 hUinv hU'inv ⟨y, hyΓ⟩ ∈
      (iotaOf hU2 hU'2 hUinv hU'inv).range := MonoidHom.mem_range.2 ⟨_, rfl⟩
  rcases sign_split _ hE9 hψR hψ1 hψ2 with hB | hA
  · right
    exact caseB_conclusion (iotaOf hU2 hU'2 hUinv hU'inv) hιinj hE9
      (fun g => hB _ (MonoidHom.mem_range.2 ⟨g, rfl⟩)) hyΓ hyy hy1 hψ1 hψ2
  · left
    have hsurj : Function.Surjective (iotaOf hU2 hU'2 hUinv hU'inv) :=
      MonoidHom.range_eq_top.1 hA
    refine ⟨⟨MulEquiv.ofBijective _ ⟨hιinj, hsurj⟩⟩, ?_⟩
    exact closure_eq_of_iota hc hU2 hU'2 hUinv hU'inv hιinj hsurj

end CFSG.Quasithin.G105
