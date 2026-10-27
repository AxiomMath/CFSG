module

public import CFSG.Quasithin.Recognition.G112M13Defs
public import CFSG.Quasithin.Background.HM22Out
public import CFSG.Quasithin.Recognition.G112A2D12

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin.HatM22 CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem matrix_eq_of_mulVec_eq {M M' : Matrix (Fin 6) (Fin 6) FieldFour}
    (h : ∀ x : Fin 6 → FieldFour, M.mulVec x = M'.mulVec x) : M = M' := by
  have hL : Matrix.toLin' M = Matrix.toLin' M' := LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact h x
  exact Matrix.toLin'.injective hL

private def omegaScalar (ψ : V ≃ₗ[ZMod 2] (Fin 6 → FieldFour)) : V ≃ₗ[ZMod 2] V where
  toFun v := ψ.symm (ω • ψ v)
  invFun v := ψ.symm ((ω * ω) • ψ v)
  map_add' a b := by simp [smul_add]
  map_smul' c v := by
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl <;> simp
  left_inv v := by
    have h3 : ω * ω * ω = 1 := by decide
    show ψ.symm ((ω * ω) • ψ (ψ.symm (ω • ψ v))) = v
    rw [ψ.apply_symm_apply, smul_smul, h3, one_smul, ψ.symm_apply_apply]
  right_inv v := by
    have h3 : ω * (ω * ω) = 1 := by decide
    show ψ.symm (ω • ψ (ψ.symm ((ω * ω) • ψ v))) = v
    rw [ψ.apply_symm_apply, smul_smul, h3, one_smul, ψ.symm_apply_apply]

private theorem semilinear_of_omega (ψ : V ≃ₗ[ZMod 2] (Fin 6 → FieldFour)) (γ : V ≃ₗ[ZMod 2] V)
    (h : ∀ v : V, ψ (γ (ψ.symm (ω • ψ v))) = (ω * ω) • ψ (γ v)) :
    Semilinear ψ.toAddEquiv γ := by
  intro c v
  have hc : ∀ c : FieldFour, c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω * ω := by decide
  rcases hc c with rfl | rfl | rfl | rfl
  · simp
  · simp
  · exact h v
  · have hu : ψ (ψ.symm (ω • ψ v)) = ω • ψ v := ψ.apply_symm_apply _
    have e1 : ψ.symm ((ω * ω) • ψ v) = ψ.symm (ω • ψ (ψ.symm (ω • ψ v))) := by
      rw [hu, smul_smul]
    show ψ (γ (ψ.symm ((ω * ω) • ψ v))) = ((ω * ω) * (ω * ω)) • ψ (γ v)
    rw [e1, h (ψ.symm (ω • ψ v)), h v, smul_smul]

private theorem central_of_centralizes {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} [Finite V]
    (N : Subgroup ↥Γ) (hfin : Finite ↥N) (hd : Module.finrank (ZMod 2) V = 12)
    (hH : IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22)
    (t : V ≃ₗ[ZMod 2] V) (ht : ∀ n ∈ N.map Γ.subtype, n * t = t * n) :
    ∃ z : ↥N, z ∈ Subgroup.center ↥N ∧ ((z : ↥Γ) : V ≃ₗ[ZMod 2] V) = t := by
  have hqOpen : CFSG.Open.IsQuasisimple ↥N :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hH.1
  have hW : Nat.card (Multiplicative V) = 2 ^ 12 := by
    rw [CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.natCard_multiplicative, hd]
  have hW2 : ∀ w : Multiplicative V, w ^ 2 = 1 := fun w => by
    rw [pow_two]; exact CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.mul_self_eq_one_multiplicative w
  let ρ : ↥N →* MulAut (Multiplicative V) :=
    (CFSG.Quasithin.G11.linEquivMulAut.toMonoidHom).comp (Γ.subtype.comp N.subtype)
  have hρ : Function.Injective ρ :=
    CFSG.Quasithin.G11.linEquivMulAut.injective.comp
      ((Γ.subtype_injective).comp (N.subtype_injective))
  have key := CFSG.Quasithin.H.Mathieu.M22Link.kg82HatM22Twelve_holds ↥N hqOpen hH.2.1 hH.2.2
    (Multiplicative V) hW hW2 ρ hρ
  have hmem : CFSG.Quasithin.G11.linEquivMulAut t ∈
      Subgroup.centralizer (ρ.range : Set (MulAut (Multiplicative V))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := MonoidHom.mem_range.mp hx
    have hn : ((n : ↥Γ) : V ≃ₗ[ZMod 2] V) ∈ N.map Γ.subtype := Subgroup.mem_map_of_mem _ n.2
    show CFSG.Quasithin.G11.linEquivMulAut ((n : ↥Γ) : V ≃ₗ[ZMod 2] V) *
        CFSG.Quasithin.G11.linEquivMulAut t =
      CFSG.Quasithin.G11.linEquivMulAut t *
        CFSG.Quasithin.G11.linEquivMulAut ((n : ↥Γ) : V ≃ₗ[ZMod 2] V)
    rw [← map_mul, ← map_mul, ht _ hn]
  rw [key] at hmem
  obtain ⟨z, hz, hzt⟩ := Subgroup.mem_map.mp hmem
  exact ⟨z, hz, CFSG.Quasithin.G11.linEquivMulAut.injective hzt⟩

private def conjAutN {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (N : Subgroup ↥Γ) (hN : N.Normal) (g : ↥Γ) :
    MulAut ↥N where
  toFun n := ⟨g * (n : ↥Γ) * g⁻¹, hN.conj_mem _ n.2 g⟩
  invFun n := ⟨g⁻¹ * (n : ↥Γ) * g, hN.conj_mem _ n.2 g⁻¹⟩
  left_inv n := by ext; simp [mul_assoc]
  right_inv n := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

private theorem semilinear_of_outer {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} [Finite V]
    (N : Subgroup ↥Γ) (hN : N.Normal) (hfin : Finite ↥N) (hd : Module.finrank (ZMod 2) V = 12)
    (hH : IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22)
    (ψ : V ≃ₗ[ZMod 2] (Fin 6 → FieldFour))
    (hcomm : ∀ n ∈ N.map Γ.subtype, n * omegaScalar ψ = omegaScalar ψ * n)
    (g : ↥Γ) (hgN : g ∉ N) : Semilinear ψ.toAddEquiv (g : V ≃ₗ[ZMod 2] V) := by
  obtain ⟨z, hz, hzω⟩ := central_of_centralizes N hfin hd hH (omegaScalar ψ) hcomm
  have hqOpen : CFSG.Open.IsQuasisimple ↥N :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hH.1
  have hnon : ∀ k : ↥N, conjAutN N hN g ≠ MulAut.conj k := by
    intro k heq
    have hcent : ∀ n ∈ N.map Γ.subtype,
        n * ((((k : ↥Γ))⁻¹ * g : ↥Γ) : V ≃ₗ[ZMod 2] V) =
          ((((k : ↥Γ))⁻¹ * g : ↥Γ) : V ≃ₗ[ZMod 2] V) * n := by
      intro n hn
      obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.mp hn
      have e := DFunLike.congr_fun heq ⟨n', hn'⟩
      have e' : g * n' * g⁻¹ = (k : ↥Γ) * n' * (k : ↥Γ)⁻¹ :=
        congrArg (fun x : ↥N => (x : ↥Γ)) e
      have e2 : g * n' = (k : ↥Γ) * n' * (k : ↥Γ)⁻¹ * g := by
        rw [← e']; group
      have hcom : n' * ((k : ↥Γ)⁻¹ * g) = ((k : ↥Γ)⁻¹ * g) * n' := by
        calc n' * ((k : ↥Γ)⁻¹ * g) = (k : ↥Γ)⁻¹ * ((k : ↥Γ) * n' * (k : ↥Γ)⁻¹ * g) := by group
          _ = (k : ↥Γ)⁻¹ * (g * n') := by rw [e2]
          _ = ((k : ↥Γ)⁻¹ * g) * n' := by group
      have hcomG := congrArg (fun x : ↥Γ => (x : V ≃ₗ[ZMod 2] V)) hcom
      simpa using hcomG
    obtain ⟨z', hz', hz't⟩ := central_of_centralizes N hfin hd hH _ hcent
    have htN : (k : ↥Γ)⁻¹ * g ∈ N := by
      have : (k : ↥Γ)⁻¹ * g = (z' : ↥Γ) := Subtype.ext hz't.symm
      rw [this]
      exact z'.2
    apply hgN
    have : g = (k : ↥Γ) * ((k : ↥Γ)⁻¹ * g) := by group
    rw [this]
    exact N.mul_mem k.2 htN
  have hα := CFSG.Quasithin.H.Mathieu.M22Link.kg82HatM22Out_holds ↥N hqOpen hH.2.1 hH.2.2
    (conjAutN N hN g) hnon z hz
  have hconj : g * (z : ↥Γ) * g⁻¹ = (z : ↥Γ)⁻¹ := by
    have := congrArg (fun x : ↥N => (x : ↥Γ)) hα
    simpa [conjAutN] using this
  have hconjV : (g : V ≃ₗ[ZMod 2] V) * ((z : ↥Γ) : V ≃ₗ[ZMod 2] V) =
      (((z : ↥Γ) : V ≃ₗ[ZMod 2] V))⁻¹ * (g : V ≃ₗ[ZMod 2] V) := by
    have := congrArg (fun x : ↥Γ => (x : V ≃ₗ[ZMod 2] V)) hconj
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  rw [hzω] at hconjV
  have hsemi : ∀ v : V, ψ ((g : V ≃ₗ[ZMod 2] V) (ψ.symm (ω • ψ v))) =
      (ω * ω) • ψ ((g : V ≃ₗ[ZMod 2] V) v) := by
    intro v
    have hv' : (g : V ≃ₗ[ZMod 2] V) (ψ.symm (ω • ψ v)) =
        ψ.symm ((ω * ω) • ψ ((g : V ≃ₗ[ZMod 2] V) v)) :=
      congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hconjV
    rw [hv', ψ.apply_symm_apply]
  exact semilinear_of_omega ψ _ hsemi

theorem g112Concl13Mod_of_N {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} [Finite V]
    (h : G112Concl13ModN Γ) : G112Concl13Mod Γ := by
  obtain ⟨hd, N, hN, hi, hH, ψ, hψ⟩ := h
  obtain ⟨f⟩ := CFSG.Quasithin.HM22.nonempty_mulEquiv_hatM22Γ₀ hH
  have hcardG : Nat.card ↥hatM22Γ₀ = 1330560 :=
    CFSG.Quasithin.HM22.card_hatM22Γ₀.trans (by norm_num)
  have hcardN : Nat.card ↥N = 1330560 := by
    rw [← Nat.card_congr f.toEquiv, hcardG]
  have hcardΓ : Nat.card ↥Γ = 2661120 := by
    have hm := N.card_mul_index
    rw [hi, hcardN] at hm
    omega
  haveI : Finite ↥hatM22Γ₀ := Nat.finite_of_card_ne_zero (by rw [hcardG]; norm_num)
  haveI : Finite ↥N := Nat.finite_of_card_ne_zero (by rw [hcardN]; norm_num)
  have hsub : ∀ k : ↥N, ((k : ↥Γ) : V ≃ₗ[ZMod 2] V) ∈ N.map Γ.subtype :=
    fun k => Subgroup.mem_map_of_mem _ k.2
  let Fm : ↥N → ↥hatM22Γ₀ := fun k => (hψ _ (hsub k)).choose
  have hFm : ∀ (k : ↥N) (v : V), ψ (((k : ↥Γ) : V ≃ₗ[ZMod 2] V) v) =
      ((((Fm k : ↥hatM22Γ₀)) : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour).mulVec (ψ v) :=
    fun k v => (hψ _ (hsub k)).choose_spec v
  have huniq : ∀ (k : ↥N) (M : Matrix (Fin 6) (Fin 6) FieldFour),
      (∀ v : V, ψ (((k : ↥Γ) : V ≃ₗ[ZMod 2] V) v) = M.mulVec (ψ v)) →
        M = ((((Fm k : ↥hatM22Γ₀)) : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour) := by
    intro k M hM
    apply matrix_eq_of_mulVec_eq
    intro x
    have h1 := hM (ψ.symm x)
    have h2 := hFm k (ψ.symm x)
    rw [ψ.apply_symm_apply] at h1 h2
    exact h1.symm.trans h2
  have hmul : ∀ k₁ k₂ : ↥N, Fm (k₁ * k₂) = Fm k₁ * Fm k₂ := by
    intro k₁ k₂
    have hM : ∀ v : V, ψ ((((k₁ * k₂ : ↥N) : ↥Γ) : V ≃ₗ[ZMod 2] V) v) =
        ((((Fm k₁ * Fm k₂ : ↥hatM22Γ₀)) : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour).mulVec (ψ v) := by
      intro v
      show ψ (((k₁ : ↥Γ) : V ≃ₗ[ZMod 2] V) (((k₂ : ↥Γ) : V ≃ₗ[ZMod 2] V) v)) = _
      rw [hFm k₁ (((k₂ : ↥Γ) : V ≃ₗ[ZMod 2] V) v), hFm k₂ v, Matrix.mulVec_mulVec,
        Subgroup.coe_mul, Units.val_mul]
    have key := huniq (k₁ * k₂) ((((Fm k₁ * Fm k₂ : ↥hatM22Γ₀)) :
      Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour) hM
    apply Subtype.ext
    apply Units.ext
    exact key.symm
  let F : ↥N →* ↥hatM22Γ₀ := MonoidHom.mk' Fm hmul
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro k hk1
    have hk1' : Fm k = 1 := hk1
    have hM1 : ((((Fm k : ↥hatM22Γ₀)) : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour) = 1 := by
      rw [hk1']
      simp
    have hlin : ((k : ↥Γ) : V ≃ₗ[ZMod 2] V) = 1 := by
      apply LinearEquiv.ext
      intro v
      apply ψ.injective
      rw [hFm k v, hM1, Matrix.one_mulVec]
      rfl
    exact Subtype.ext (Subtype.ext hlin)
  have hsurj : Function.Surjective F :=
    (Function.Injective.bijective_of_nat_card_le hFinj (hcardG.trans hcardN.symm).le).2
  have hcomm : ∀ n ∈ N.map Γ.subtype, n * omegaScalar ψ = omegaScalar ψ * n := by
    intro n hn
    obtain ⟨γ', hγ'⟩ := hψ n hn
    apply LinearEquiv.ext
    intro v
    apply ψ.injective
    show ψ (n (ψ.symm (ω • ψ v))) = ψ (ψ.symm (ω • ψ (n v)))
    rw [hγ' (ψ.symm (ω • ψ v)), ψ.apply_symm_apply, ψ.apply_symm_apply, hγ' v,
      Matrix.mulVec_smul]
  have part1 : ∀ g ∈ hatM22Γ₀, ∃ γ ∈ Γ, ActsAs ψ.toAddEquiv γ
      ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour) := by
    intro g hg
    obtain ⟨k, hk⟩ := hsurj ⟨g, hg⟩
    have hk' : Fm k = ⟨g, hg⟩ := hk
    refine ⟨((k : ↥Γ) : V ≃ₗ[ZMod 2] V), (k : ↥Γ).2, fun v => ?_⟩
    have := hFm k v
    rw [hk'] at this
    exact this
  have part2 : ∀ γ ∈ Γ, (∃ g ∈ hatM22Γ₀, ActsAs ψ.toAddEquiv γ
      ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)) ∨
        Semilinear ψ.toAddEquiv γ := by
    intro γ hγΓ
    by_cases hγN : γ ∈ N.map Γ.subtype
    · obtain ⟨g', hg'⟩ := hψ γ hγN
      exact Or.inl ⟨g', g'.2, fun v => hg' v⟩
    · right
      have hgN : (⟨γ, hγΓ⟩ : ↥Γ) ∉ N := fun h => hγN (Subgroup.mem_map_of_mem _ h)
      exact semilinear_of_outer N hN inferInstance hd hH ψ hcomm ⟨γ, hγΓ⟩ hgN
  exact ⟨hd, hcardΓ, ψ.toAddEquiv, part1, part2⟩

end CFSG.Quasithin.G112A2
