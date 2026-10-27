module

public import CFSG.Quasithin.Vol2.KGNatComm
public import CFSG.Quasithin.Vol2.KGNatSemiLin
public import CFSG.Quasithin.MS93.S34Ext

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2 Matrix

variable {G : Type} [Group G]

section Conj

variable {A V : Subgroup G} {F : Type} [Field F] {α : ↥A →* ↥(StatedSL 3 F)}
  {β : ↥V →* Multiplicative (Fin 1 → Fin 3 → F)}

theorem coordMap_conj (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hβ : Function.Surjective β)
    (hβα : ∀ a : ↥A, IsCoordAct β a ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec)
    {t : G} (htV : t ∈ Subgroup.normalizer (V : Set G))
    (htA : t ∈ Subgroup.normalizer (A : Set G)) {f : (Fin 3 → F) → (Fin 3 → F)}
    (hf : IsCoordAct β t f) (a : ↥A) (x : Fin 3 → F) :
    f (((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) =
      ((α ⟨t * a * t⁻¹, (Subgroup.mem_normalizer_iff.1 htA a).1 a.2⟩ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ f x := by
  set a' : ↥A := ⟨t * a * t⁻¹, (Subgroup.mem_normalizer_iff.1 htA a).1 a.2⟩
  have h1 := hf.mul (hAV a.2) (hβα a)
  have h2 := (hβα a').mul htV hf
  have heq : (t : G) * a = (a' : G) * t := by simp [a']
  rw [heq] at h1
  have := IsCoordAct.unique hβ (mul_mem (hAV a'.2) htV) h1 h2
  exact congrFun this x

variable {f f' : (Fin 3 → F) → (Fin 3 → F)}

theorem coordMap_inv_comp (hβ : Function.Surjective β) {t : G}
    (htV : t ∈ Subgroup.normalizer (V : Set G)) (hf : IsCoordAct β t f)
    (hf' : IsCoordAct β t⁻¹ f') (x : Fin 3 → F) : f (f' x) = x ∧ f' (f x) = x := by
  have h1 := hf.mul (inv_mem htV) hf'
  have h2 := hf'.mul htV hf
  rw [mul_inv_cancel] at h1
  rw [inv_mul_cancel] at h2
  exact ⟨congrFun (IsCoordAct.unique hβ (one_mem _) h1 isCoordAct_one) x,
    congrFun (IsCoordAct.unique hβ (one_mem _) h2 isCoordAct_one) x⟩

theorem exists_semilinear (hα : Function.Surjective α)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hβ : Function.Surjective β)
    (hβα : ∀ a : ↥A, IsCoordAct β a ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec)
    {t : G} (htV : t ∈ Subgroup.normalizer (V : Set G))
    (htA : t ∈ Subgroup.normalizer (A : Set G)) {f : (Fin 3 → F) →+ (Fin 3 → F)}
    (hf : IsCoordAct β t f) {f' : (Fin 3 → F) →+ (Fin 3 → F)} (hf' : IsCoordAct β t⁻¹ f') :
    ∃ σ : F →+* F, ∀ (c : F) (x : Fin 3 → F), f (c • x) = σ c • f x := by
  have hinv := coordMap_inv_comp hβ htV hf hf'
  have hS : ∀ c : F, ∃ s : F, ∀ x : Fin 3 → F, f (c • f' x) = s • x := by
    intro c
    let S : (Fin 3 → F) →+ (Fin 3 → F) :=
      { toFun := fun x => f (c • f' x)
        map_zero' := by simp
        map_add' := fun x y => by simp [smul_add] }
    refine KGNat.commutant_statedSL (by norm_num) S fun γ x => ?_
    rw [KGNat.linModelNat_lin, KGNat.linModelNat_lin]
    obtain ⟨a, rfl⟩ := hα γ
    change f (c • f' (((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)) =
      ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f (c • f' x)
    have htA' : t⁻¹ ∈ Subgroup.normalizer (A : Set G) := inv_mem htA
    rw [coordMap_conj hAV hβ hβα (inv_mem htV) htA' hf' a x, ← Matrix.mulVec_smul,
      coordMap_conj hAV hβ hβα htV htA hf]
    congr 3
    apply Subtype.ext
    simp [mul_assoc]
  choose s hs using hS
  have hfs : ∀ c x, f (c • x) = s c • f x := fun c x => by
    have := hs c (f x)
    rwa [(hinv x).2] at this
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fin 3 → F, f x₀ ≠ 0 := by
    refine ⟨f' (Pi.single 0 1), ?_⟩
    rw [(hinv _).1]
    exact fun h => by simpa using congrFun h 0
  have hcancel : ∀ a b : F, a • f x₀ = b • f x₀ → a = b := fun a b h =>
    smul_left_injective F hx₀ h
  refine ⟨{ toFun := s, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    hfs⟩
  · exact hcancel _ _ (by rw [← hfs, one_smul, one_smul])
  · intro a b
    exact hcancel _ _ (by rw [← hfs, mul_smul, hfs, hfs, smul_smul])
  · exact hcancel _ _ (by rw [← hfs, zero_smul, zero_smul, map_zero])
  · intro a b
    exact hcancel _ _ (by rw [← hfs, add_smul, map_add, hfs, hfs, add_smul])

end Conj

section Semilinear

variable {F : Type} [Field F]

theorem ringHom_eq_id_of_fix {f : (Fin 3 → F) →+ (Fin 3 → F)} {σ : F →+* F}
    (hσ : ∀ (c : F) (x : Fin 3 → F), f (c • x) = σ c • f x) {x : Fin 3 → F} (hx : x ≠ 0)
    (hfix : ∀ c : F, f (c • x) = c • x) (c : F) : σ c = c := by
  have h1 := hσ c x
  rw [hfix, show f x = x by simpa using hfix 1] at h1
  have := sub_eq_zero.2 h1
  rw [← sub_smul] at this
  exact (sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hx)).symm

theorem eq_id_of_quadratic {f g : (Fin 3 → F) →+ (Fin 3 → F)} {σ : F →+* F}
    (hσ : ∀ (c : F) (x : Fin 3 → F), f (c • x) = σ c • f x) (hne : ∃ c : F, σ c ≠ c)
    (hg : ∀ (c : F) (x : Fin 3 → F), g (c • x) = c • g x)
    (hfg : ∀ x : Fin 3 → F, f (g x - x) = g x - x) (x : Fin 3 → F) : g x = x := by
  by_contra hx
  obtain ⟨c, hc⟩ := hne
  apply hc
  refine ringHom_eq_id_of_fix hσ (sub_ne_zero.2 hx) (fun d => ?_) c
  have : d • (g x - x) = g (d • x) - d • x := by rw [hg, smul_sub]
  rw [this, hfg]

end Semilinear

section Index

variable {F : Type} [Field F] [Fintype F]

omit [Field F] in
theorem card_fin3 : Nat.card (Fin 3 → F) = Fintype.card F ^ 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

theorem card_mul_le_of_linear {f : (Fin 3 → F) →+ (Fin 3 → F)}
    (hlin : ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x) (hne : ∃ x, f x ≠ x) :
    Nat.card (KGNat.fixAdd f) * Fintype.card F ≤ Fintype.card F ^ 3 := by
  let fl : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := f, map_add' := map_add f, map_smul' := hlin }
  set K := LinearMap.ker (fl - LinearMap.id) with hK
  have hKfix : ∀ x, x ∈ K ↔ x ∈ KGNat.fixAdd f := by
    intro x
    rw [hK, LinearMap.mem_ker, KGNat.mem_fixAdd, LinearMap.sub_apply, sub_eq_zero]
    rfl
  have hcard : Nat.card (KGNat.fixAdd f) = Nat.card K := by
    apply Nat.card_congr
    exact { toFun := fun x => ⟨x, (hKfix x).2 x.2⟩, invFun := fun x => ⟨x, (hKfix x).1 x.2⟩,
            left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hKne : K ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx⟩ := hne
    have : x ∈ K := htop ▸ Submodule.mem_top
    exact hx ((hKfix x).1 this)
  have hdim : Module.finrank F K ≤ 2 := by
    have h3 := Submodule.finrank_lt (s := K) hKne
    rw [Module.finrank_fin_fun] at h3
    omega
  rw [hcard, Module.natCard_eq_pow_finrank (K := F) (V := ↥K), Nat.card_eq_fintype_card]
  calc Fintype.card F ^ Module.finrank F K * Fintype.card F
      ≤ Fintype.card F ^ 2 * Fintype.card F :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hdim)
    _ = Fintype.card F ^ 3 := by ring

theorem four_le_index {f : (Fin 3 → F) →+ (Fin 3 → F)} {σ : F →+* F}
    (hσ : ∀ (c : F) (x : Fin 3 → F), f (c • x) = σ c • f x) (hF : 4 ≤ Fintype.card F)
    (hne : ∃ x, f x ≠ x) : Nat.card (KGNat.fixAdd f) * 4 ≤ Fintype.card F ^ 3 := by
  by_cases hlin : ∀ c : F, σ c = c
  · have hl : ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x := fun c x => by rw [hσ, hlin]
    have := card_mul_le_of_linear hl hne
    calc Nat.card (KGNat.fixAdd f) * 4 ≤ Nat.card (KGNat.fixAdd f) * Fintype.card F :=
          Nat.mul_le_mul_left _ hF
      _ ≤ _ := this
  · push Not at hlin
    have hsq : Nat.card (KGNat.fixAdd f) ^ 2 ≤ Nat.card (Fin 3 → F) := by
      by_contra h
      push Not at h
      obtain ⟨c, hc⟩ := hlin
      exact hc (KGNat.semilinear_eq_id_of_card_fix hσ h c)
    rw [card_fin3] at hsq
    set q := Fintype.card F
    set C := Nat.card (KGNat.fixAdd f)
    have hq3 : 16 ≤ q ^ 3 := by
      calc 16 ≤ 4 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hF 3
    by_contra hlt
    push Not at hlt
    have h1 : (q ^ 3) ^ 2 < (C * 4) ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
    have h2 : (C * 4) ^ 2 = 16 * C ^ 2 := by ring
    have h3 : 16 * C ^ 2 ≤ 16 * q ^ 3 := Nat.mul_le_mul_left _ hsq
    have h4 : 16 * q ^ 3 ≤ q ^ 3 * q ^ 3 := Nat.mul_le_mul_right _ hq3
    nlinarith

end Index

end CFSG.Quasithin.MS93.S33
