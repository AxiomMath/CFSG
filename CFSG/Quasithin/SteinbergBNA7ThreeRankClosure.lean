module

public import CFSG.Quasithin.SteinbergBNA7A3Actor
public import CFSG.Quasithin.SteinbergBNA7E6Word
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SteinbergBQRankOneNormalClosureSplit

public noncomputable section

namespace CFSG.Quasithin.SteinbergBN

open Subgroup CFSG.Open CFSG.QuasithinUnique Module
open scoped commutatorElement Pointwise

section Linearization

variable {G : Type*} [Group G] {V : Subgroup G} {M : Type*} [AddCommGroup M]
  [Module (ZMod 2) M]

@[expose] def transportAdd (ι : V ≃* Multiplicative M) (σ : MulAut V) : M →+ M where
  toFun m := Multiplicative.toAdd (ι (σ (ι.symm (Multiplicative.ofAdd m))))
  map_zero' := by simp
  map_add' m m' := by
    simp only [ofAdd_add, map_mul, toAdd_mul]

@[expose] def transportLin (ι : V ≃* Multiplicative M) (σ : MulAut V) : M →ₗ[ZMod 2] M :=
  (transportAdd ι σ).toZModLinearMap 2

theorem transportLin_apply (ι : V ≃* Multiplicative M) (σ : MulAut V) (m : M) :
    transportLin ι σ m = Multiplicative.toAdd (ι (σ (ι.symm (Multiplicative.ofAdd m)))) := rfl

theorem transportLin_mul (ι : V ≃* Multiplicative M) (σ τ : MulAut V) :
    transportLin ι (σ * τ) = transportLin ι σ * transportLin ι τ := by
  ext m
  simp [transportLin_apply, Module.End.mul_apply]

theorem transportLin_one (ι : V ≃* Multiplicative M) : transportLin ι 1 = 1 := by
  ext m
  simp [transportLin_apply]

@[expose] def linAut (ι : V ≃* Multiplicative M) :
    MulAut V →* LinearMap.GeneralLinearGroup (ZMod 2) M where
  toFun σ :=
    { val := transportLin ι σ
      inv := transportLin ι σ⁻¹
      val_inv := by rw [← transportLin_mul, mul_inv_cancel, transportLin_one]
      inv_val := by rw [← transportLin_mul, inv_mul_cancel, transportLin_one] }
  map_one' := Units.ext (transportLin_one ι)
  map_mul' σ τ := Units.ext (transportLin_mul ι σ τ)

theorem linAut_apply (ι : V ≃* Multiplicative M) (σ : MulAut V) (m : M) :
    (linAut ι σ : M →ₗ[ZMod 2] M) m =
      Multiplicative.toAdd (ι (σ (ι.symm (Multiplicative.ofAdd m)))) := rfl

theorem linAut_apply_ι (ι : V ≃* Multiplicative M) (σ : MulAut V) (v : V) :
    (linAut ι σ : M →ₗ[ZMod 2] M) (Multiplicative.toAdd (ι v)) =
      Multiplicative.toAdd (ι (σ v)) := by
  rw [linAut_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem linAut_injective (ι : V ≃* Multiplicative M) : Function.Injective (linAut ι) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine MulEquiv.ext fun v => ?_
  have h := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) M =>
    (g : M →ₗ[ZMod 2] M) (Multiplicative.toAdd (ι v))) hσ
  simp only [linAut_apply_ι, Units.val_one, Module.End.one_apply] at h
  have h2 := congrArg (fun m => ι.symm (Multiplicative.ofAdd m)) h
  simpa using h2

theorem linAut_comp_conj {X : Subgroup G} (ι : V ≃* Multiplicative M)
    (hXV : X ≤ normalizer (V : Set G))
    (ρ : X →* LinearMap.GeneralLinearGroup (ZMod 2) M)
    (hρ : ∀ (x : X) (v w : V), (w : G) = x * v * x⁻¹ →
      (ρ x : M →ₗ[ZMod 2] M) (Multiplicative.toAdd (ι v)) = Multiplicative.toAdd (ι w)) :
    ρ = (linAut ι).comp (V.normalizerMonoidHom.comp (Subgroup.inclusion hXV)) := by
  refine MonoidHom.ext fun x => Units.ext (LinearMap.ext fun m => ?_)
  have hm : m = Multiplicative.toAdd (ι (ι.symm (Multiplicative.ofAdd m))) := by simp
  rw [hm, hρ x _ ((V.normalizerMonoidHom.comp (Subgroup.inclusion hXV)) x
    (ι.symm (Multiplicative.ofAdd m))) rfl]
  simp only [MonoidHom.comp_apply, linAut_apply_ι]

@[expose] def linPre (ι : V ≃* Multiplicative M) (S : Submodule (ZMod 2) M) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ V, Multiplicative.toAdd (ι ⟨g, hg⟩) ∈ S}
  one_mem' := ⟨one_mem V, by
    have e : (⟨1, one_mem V⟩ : V) = 1 := rfl
    rw [e, map_one, toAdd_one]
    exact S.zero_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : (⟨a * b, mul_mem ha hb⟩ : V) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, toAdd_mul]
    exact S.add_mem ha' hb'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : (⟨a⁻¹, inv_mem ha⟩ : V) = (⟨a, ha⟩ : V)⁻¹ := rfl
    rw [e, map_inv, toAdd_inv]
    exact S.neg_mem ha'

theorem eq_top_of_le_linPre {ι : V ≃* Multiplicative M} {S : Submodule (ZMod 2) M}
    (h : V ≤ linPre ι S) : S = ⊤ := by
  rw [eq_top_iff]
  intro m _
  obtain ⟨_, hS⟩ := h (ι.symm (Multiplicative.ofAdd m)).2
  simpa using hS

theorem finrank_eq_two_of_card [Module.Finite (ZMod 2) M] {U : Subgroup G} (hUV : U ≤ V)
    (hU4 : Nat.card U = 4) (ι : V ≃* Multiplicative M) {S : Submodule (ZMod 2) M}
    (hS : ∀ m, m ∈ S ↔ ∃ u : V, (u : G) ∈ U ∧ Multiplicative.toAdd (ι u) = m) :
    finrank (ZMod 2) S = 2 := by
  have hcard : Nat.card S = Nat.card U := by
    refine (Nat.card_congr (Equiv.ofBijective (fun u : U =>
      (⟨Multiplicative.toAdd (ι ⟨u, hUV u.2⟩), (hS _).2 ⟨_, u.2, rfl⟩⟩ : S)) ⟨?_, ?_⟩)).symm
    · intro u u' h
      have h1 := congrArg Subtype.val h
      have h2 := ι.injective (Multiplicative.toAdd.injective h1)
      have h3 := Subtype.ext_iff.1 h2
      exact Subtype.ext h3
    · rintro ⟨m, hm⟩
      obtain ⟨u, hu, rfl⟩ := (hS m).1 hm
      exact ⟨⟨u, hu⟩, rfl⟩
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S)
  rw [hcard, hU4, Nat.card_zmod] at h
  have h2 : 2 ^ finrank (ZMod 2) S = 2 ^ 2 := by rw [← h]; norm_num
  exact Nat.pow_right_injective le_rfl h2

end Linearization

section Transport

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂] {φ : G₁ →* G₂}

theorem pCore_map_eq_bot (hφ : Function.Injective φ) {H : Subgroup G₁}
    (hH : pCoreOf 2 H = ⊥) : CFSG.pCore 2 ↥(H.map φ) = ⊥ := by
  have h1 : CFSG.Open.pCore 2 ↥H = ⊥ := by
    rw [pCoreOf] at hH
    exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).1 hH
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (H.equivMapOfInjective φ hφ), h1,
    Subgroup.map_bot]

theorem map_le_normalizer_map {S B : Subgroup G₁} (h : S ≤ normalizer (B : Set G₁)) :
    S.map φ ≤ normalizer ((B.map φ : Subgroup G₂) : Set G₂) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨s * b * s⁻¹, (mem_normalizer_iff.1 (h hs) b).1 hb, by simp⟩
  · rintro ⟨b, hb, he⟩
    refine ⟨s⁻¹ * b * s, ?_, ?_⟩
    · have := (mem_normalizer_iff.1 (h (inv_mem hs)) b).1 hb
      simpa using this
    · have : g = φ s⁻¹ * (φ s * g * (φ s)⁻¹) * φ s := by
        rw [map_inv]
        group
      rw [this, ← he]
      simp [map_mul, map_inv]

theorem map_le_inf_centralizer {S R : Subgroup G₁} (h : S ≤ R ⊓ centralizer (R : Set G₁)) :
    S.map φ ≤ R.map φ ⊓ centralizer ((R.map φ : Subgroup G₂) : Set G₂) := by
  rintro _ ⟨s, hs, rfl⟩
  refine mem_inf.2 ⟨mem_map_of_mem φ (mem_inf.1 (h hs)).1, ?_⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨r, hr, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (mem_inf.1 (h hs)).2 r hr]

end Transport

section Inverts

variable {Γ : Type*} [Group Γ]

theorem mem_of_conj_mem_of_inverts {N : Subgroup Γ} {t b : Γ} (hb : b * t * b⁻¹ ∈ N)
    (ht : t ∈ N) (hinv : t * b * t⁻¹ = b⁻¹) (hb3 : b ^ 3 = 1) : b ∈ N := by
  have h1 : t * b⁻¹ * t⁻¹ = b := by
    have h := congrArg (·⁻¹) hinv
    simpa [mul_assoc] using h
  have h2 : b * t * b⁻¹ * t⁻¹ = b ^ 2 := by
    calc b * t * b⁻¹ * t⁻¹ = b * (t * b⁻¹ * t⁻¹) := by group
      _ = b ^ 2 := by rw [h1, sq]
  have hb2 : b ^ 2 ∈ N := h2 ▸ mul_mem hb (inv_mem ht)
  have h4 : b = b ^ 2 * b ^ 2 := by
    calc b = b * b ^ 3 := by rw [hb3, mul_one]
      _ = b ^ 2 * b ^ 2 := by group
  rw [h4]
  exact mul_mem hb2 hb2

end Inverts

theorem injective_fin3 {W : Type*} {a b c : W} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

section Linear

variable {G : Type*} [Group G] [Finite G] {X T K A Q U V E : Subgroup G}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem range_inf_ker_eq_bot (b : LinearMap.GeneralLinearGroup (ZMod 2) M) (hb : b ^ 3 = 1) :
    LinearMap.range ((b : M →ₗ[ZMod 2] M) - 1) ⊓ LinearMap.ker ((b : M →ₗ[ZMod 2] M) - 1) =
      ⊥ := by
  have hb3 : ∀ y : M, (b : M →ₗ[ZMod 2] M) ((b : M →ₗ[ZMod 2] M) ((b : M →ₗ[ZMod 2] M) y)) =
      y := by
    intro y
    have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) M => (g : M →ₗ[ZMod 2] M) y)
      hb
    simpa [pow_succ, Module.End.mul_apply] using this
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨⟨w, hw⟩, hker⟩ := Submodule.mem_inf.1 hv
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hker
  rw [LinearMap.sub_apply, Module.End.one_apply] at hw
  rw [Submodule.mem_bot]
  have h1 : (b : M →ₗ[ZMod 2] M) ((b : M →ₗ[ZMod 2] M) v) + (b : M →ₗ[ZMod 2] M) v + v = 0 := by
    rw [← hw]
    simp only [map_sub]
    rw [hb3]
    abel
  rw [hker, hker, ZModModule.add_self, zero_add] at h1
  exact h1

theorem a3_linear_actor (hX : CharTwo X) (hT : IsSylowTwoOf T X) (hKX : K ≤ X)
    (hK : IsShort2 K) (hK3 : Nat.card (K ⧸ CFSG.pCore 2 K) = 3)
    (hTK : T ≤ normalizer (K : Set G)) (hQ : Q = blockQ X) (hU : U = blockQ K)
    (hV : V = conjJoin X U) (hAT : A ≤ T) (hAn : T ≤ normalizer (A : Set G)) (hAU : ⁅A, U⁆ ≠ ⊥)
    (hE : E = A ⊓ centralizer (U : Set G)) (hE2 : Nat.card E = 2)
    (ι : V ≃* Multiplicative M) (ρ : X →* LinearMap.GeneralLinearGroup (ZMod 2) M)
    (hρ : ∀ (x : X) (v w : V), (w : G) = x * v * x⁻¹ →
      (ρ x : M →ₗ[ZMod 2] M) (Multiplicative.toAdd (ι v)) = Multiplicative.toAdd (ι w)) :
    CFSG.pCore 2 ρ.range = ⊥ ∧ Nat.card ((K.subgroupOf X).map ρ) = 3 ∧
      (T.subgroupOf X).map ρ ≤ normalizer (((K.subgroupOf X).map ρ :
        Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M)) : Set _) ∧
      (∀ k : X, (k : G) ∈ K → ρ k ≠ 1 →
        (∀ m, m ∈ LinearMap.range ((ρ k : M →ₗ[ZMod 2] M) - 1) ↔
          ∃ u : V, (u : G) ∈ U ∧ Multiplicative.toAdd (ι u) = m) ∧
        finrank (ZMod 2) (LinearMap.range ((ρ k : M →ₗ[ZMod 2] M) - 1)) = 2) ∧
      ∃ a₁ : X, (a₁ : G) ∈ A ∧ (A.subgroupOf X).map ρ = zpowers (ρ a₁) ∧
        Nat.card ((A.subgroupOf X).map ρ) = 2 ∧
        (A.subgroupOf X).map ρ ≤ (T.subgroupOf X).map ρ ⊓
          centralizer (((T.subgroupOf X).map ρ :
            Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M)) : Set _) ∧
        ρ a₁ ≠ 1 ∧ (∀ b ∈ (K.subgroupOf X).map ρ, ρ a₁ * b * (ρ a₁)⁻¹ = b⁻¹) ∧
        finrank (ZMod 2) (LinearMap.range ((ρ a₁ : M →ₗ[ZMod 2] M) - 1)) = 1 ∧
        (⨆ h ∈ ρ.range, (LinearMap.range ((ρ a₁ : M →ₗ[ZMod 2] M) - 1)).map
          (h : M →ₗ[ZMod 2] M)) = ⊤ := by
  classical
  obtain ⟨⟨-, hU4⟩, -, -, hVK, ⟨-, hXV, -, -⟩, -, -, -, hVXE, hirr, -, hKU, -, hUV, -,
    hVcomm, -, -, -⟩ := a3_config_structure hX hT hKX hK hK3 hTK hQ hU hV hAT hAn hAU hE hE2
  have hlin := linAut_comp_conj ι hXV ρ hρ
  subst hlin
  set ρ' : X →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hXV)
  obtain ⟨hO2, -, hB3, hTstB, -, τ', hρAz, hρA2, hρAc, hτ1, ⟨w, hw1, hτw⟩, hτinv, -, hrangeE⟩ :=
    a3_config_action hX hT hKX hK hK3 hTK hQ hU hV hAT hAn hAU hE hE2 ρ' (fun x v => rfl) rfl
      rfl rfl
  have hinj := linAut_injective ι
  have hR : ((linAut ι).comp ρ').range = ρ'.range.map (linAut ι) := MonoidHom.range_comp _ _
  have hM : ∀ S : Subgroup X, S.map ((linAut ι).comp ρ') = (S.map ρ').map (linAut ι) :=
    fun S => (Subgroup.map_map S _ _).symm
  have hFin : Finite M := Finite.of_equiv V (ι.toEquiv.trans Multiplicative.toAdd)
  have hMfin : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have hsub1 : ∀ (σ : MulAut V) (v : V),
      ((linAut ι σ : M →ₗ[ZMod 2] M) - 1) (Multiplicative.toAdd (ι v)) =
        Multiplicative.toAdd (ι (σ v * v⁻¹)) := by
    intro σ v
    rw [LinearMap.sub_apply, Module.End.one_apply, linAut_apply_ι, map_mul, map_inv, toAdd_mul,
      toAdd_inv, sub_eq_add_neg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hR]
    exact pCore_map_eq_bot hinj hO2
  · rw [hM, card_map_of_injective hinj]
    exact hB3
  · rw [hM, hM]
    exact map_le_normalizer_map hTstB
  ·
    intro k hk hk1
    have hKV : ⁅K, V⁆ = U := by rw [Subgroup.commutator_comm]; exact hVK
    have hLU : ∀ v : V, ((ρ' k v * v⁻¹ : V) : G) ∈ U := by
      intro v
      rw [← hKV]
      have e : ((ρ' k v * v⁻¹ : V) : G) = ⁅(k : G), (v : G)⁆ := by
        rw [commutatorElement_def]
        rfl
      rw [e]
      exact Subgroup.commutator_mem_commutator hk v.2
    have hsub : ∀ y : M, ∃ u : V, (u : G) ∈ U ∧ Multiplicative.toAdd (ι u) =
        ((linAut ι (ρ' k) : M →ₗ[ZMod 2] M) - 1) y := by
      intro y
      refine ⟨ρ' k (ι.symm (Multiplicative.ofAdd y)) * (ι.symm (Multiplicative.ofAdd y))⁻¹,
        hLU _, ?_⟩
      rw [← hsub1]
      simp
    have hBc : ∀ k' : X, (k' : G) ∈ K → ρ' k' * ρ' k = ρ' k * ρ' k' := by
      intro k' hk'
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcyc : IsCyclic ((K.subgroupOf X).map ρ') := isCyclic_of_prime_card hB3
      have h := mul_comm' (⟨ρ' k', mem_map_of_mem _ hk'⟩ : (K.subgroupOf X).map ρ')
        ⟨ρ' k, mem_map_of_mem _ hk⟩
      exact congrArg Subtype.val h
    set L : M →ₗ[ZMod 2] M := (linAut ι (ρ' k) : M →ₗ[ZMod 2] M) - 1 with hL
    set R := linPre ι (LinearMap.range L)
    have hRK : K ≤ normalizer ((R ⊓ U : Subgroup G) : Set G) := by
      have key : ∀ k' ∈ K, ∀ g ∈ R ⊓ U, k' * g * k'⁻¹ ∈ R ⊓ U := by
        intro k' hk' g hg
        obtain ⟨⟨hgV, y, hy⟩, hgU⟩ := mem_inf.1 hg
        have hk'X : k' ∈ X := hKX hk'
        have hmV : k' * g * k'⁻¹ ∈ V := (mem_normalizer_iff.1 (hXV hk'X) g).1 hgV
        refine mem_inf.2 ⟨⟨hmV, ?_⟩, (mem_normalizer_iff.1 (hKU hk') g).1 hgU⟩
        have e : (⟨k' * g * k'⁻¹, hmV⟩ : V) = ρ' ⟨k', hk'X⟩ ⟨g, hgV⟩ := rfl
        rw [e, ← linAut_apply_ι, ← hy]
        refine ⟨(linAut ι (ρ' ⟨k', hk'X⟩) : M →ₗ[ZMod 2] M) y, ?_⟩
        have hc := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) M =>
          (g : M →ₗ[ZMod 2] M) y) (congrArg (linAut ι) (hBc ⟨k', hk'X⟩ hk'))
        simp only [map_mul, Units.val_mul, Module.End.mul_apply] at hc
        rw [hL, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply,
          Module.End.one_apply, map_sub, hc]
      intro k' hk'
      exact mem_normalizer_of_conj (key k' hk') fun g hg => by
        simpa using key k'⁻¹ (inv_mem hk') g hg
    have hRU : R ⊓ U = U := by
      rcases hirr _ inf_le_right hRK with h | h
      · exfalso
        apply hk1
        refine Units.ext (LinearMap.ext fun y => ?_)
        obtain ⟨u, hu, hLy⟩ := hsub y
        have huR : (u : G) ∈ R ⊓ U := mem_inf.2 ⟨⟨u.2, ⟨y, hLy.symm⟩⟩, hu⟩
        rw [h, mem_bot] at huR
        have hu1 : u = 1 := Subtype.ext huR
        rw [hu1, map_one, toAdd_one] at hLy
        rw [MonoidHom.comp_apply]
        have h0 := hLy.symm
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0
        exact h0
      · exact h
    have hiff : ∀ m, m ∈ LinearMap.range L ↔
        ∃ u : V, (u : G) ∈ U ∧ Multiplicative.toAdd (ι u) = m := by
      intro m
      constructor
      · rintro ⟨y, rfl⟩
        exact hsub y
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨_, hm⟩ := (mem_inf.1 (hRU.ge hu)).1
        exact hm
    rw [MonoidHom.comp_apply]
    exact ⟨hiff, finrank_eq_two_of_card hUV hU4 ι hiff⟩
  ·
    obtain ⟨a₁, ha₁, hτ'⟩ : τ' ∈ (A.subgroupOf X).map ρ' := hρAz ▸ mem_zpowers τ'
    have hρa : (linAut ι).comp ρ' a₁ = linAut ι τ' := by rw [MonoidHom.comp_apply, hτ']
    have hτm : ∀ m : M, ((linAut ι τ' : M →ₗ[ZMod 2] M) - 1) m = 0 ∨
        ((linAut ι τ' : M →ₗ[ZMod 2] M) - 1) m = Multiplicative.toAdd (ι w) := by
      intro m
      obtain ⟨v, rfl⟩ : ∃ v : V, Multiplicative.toAdd (ι v) = m :=
        ⟨ι.symm (Multiplicative.ofAdd m), by simp⟩
      rw [hsub1]
      rcases hτw v with h | h
      · left
        rw [h, mul_inv_cancel, map_one, toAdd_one]
      · right
        have hvw : v * w * v⁻¹ = w := Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [hVcomm v v.2 w w.2, mul_inv_cancel_right])
        rw [h, hvw]
    have heM : Multiplicative.toAdd (ι w) ≠ 0 := by
      intro h
      apply hw1
      have h1 : ι w = 1 := by
        rw [← ofAdd_toAdd (ι w), h, ofAdd_zero]
      exact (MulEquiv.map_eq_one_iff ι).1 h1
    obtain ⟨v₀, hv₀⟩ : ∃ v : V, τ' v ≠ v := by
      by_contra hcon
      push Not at hcon
      exact hτ1 (MulEquiv.ext hcon)
    have hrange : LinearMap.range ((linAut ι τ' : M →ₗ[ZMod 2] M) - 1) =
        Submodule.span (ZMod 2) {Multiplicative.toAdd (ι w)} := by
      apply le_antisymm
      · rintro _ ⟨m, rfl⟩
        rcases hτm m with h | h
        · rw [h]
          exact Submodule.zero_mem _
        · rw [h]
          exact Submodule.mem_span_singleton_self _
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        refine ⟨Multiplicative.toAdd (ι v₀), ?_⟩
        rcases hτm (Multiplicative.toAdd (ι v₀)) with h | h
        · exfalso
          apply hv₀
          rw [LinearMap.sub_apply, Module.End.one_apply, linAut_apply_ι, sub_eq_zero] at h
          exact ι.injective (Multiplicative.toAdd.injective h)
        · exact h
    have hwE : (w : G) ∈ E := by
      have h := (hτw v₀).resolve_left hv₀
      have hmem : ((τ' v₀ : V) : G) * (v₀ : G)⁻¹ ∈ (E : Set G) := hrangeE ▸ ⟨v₀, rfl⟩
      rw [h, Subgroup.coe_mul, hVcomm v₀ v₀.2 w w.2, mul_inv_cancel_right] at hmem
      exact hmem
    obtain ⟨e₀, -, -, hEe⟩ := exists_of_card_two hE2
    have hEw : ∀ e ∈ E, e = 1 ∨ e = w := by
      intro e he
      have hw' : (w : G) = e₀ := (hEe _ hwE).resolve_left fun h => hw1 (Subtype.ext h)
      rw [hw']
      exact hEe e he
    refine ⟨a₁, ha₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hM, hρAz, MonoidHom.map_zpowers, hρa]
    · rw [hM, card_map_of_injective hinj]
      exact hρA2
    · rw [hM, hM]
      exact map_le_inf_centralizer hρAc
    · rw [hρa]
      exact (map_ne_one_iff _ hinj).2 hτ1
    · intro b hb
      rw [hM] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      have h := congrArg (linAut ι) (hτinv b' hb')
      rw [map_mul, map_mul, map_inv, map_inv] at h
      rw [hρa]
      exact h
    · rw [hρa, hrange]
      exact finrank_span_singleton heM
    · rw [hρa, hrange]
      apply eq_top_of_le_linPre (ι := ι)
      refine hVXE.le.trans (conjJoin_le_of_conj fun x hx e he => ?_)
      rcases hEw e he with rfl | rfl
      · rw [mul_one, mul_inv_cancel]
        exact one_mem _
      · have hxw : x * w * x⁻¹ ∈ V := (mem_normalizer_iff.1 (hXV hx) w).1 w.2
        refine ⟨hxw, ?_⟩
        have e : (⟨x * w * x⁻¹, hxw⟩ : V) = ρ' ⟨x, hx⟩ w := rfl
        rw [e, ← linAut_apply_ι]
        refine Submodule.mem_iSup_of_mem ((linAut ι).comp ρ' ⟨x, hx⟩)
          (Submodule.mem_iSup_of_mem (MonoidHom.mem_range.2 ⟨_, rfl⟩) ?_)
        exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)

end Linear

section ThreeRank

variable {G : Type*} [Group G]

theorem pRank_three_le_two {X : Subgroup G}
    (h3 : ∀ E : Subgroup G, E ≤ X → CFSG.IsElementaryAbelian 3 E → Nat.card E ≤ 9) :
    CFSG.pRank 3 X ≤ 2 := by
  apply csSup_le'
  rintro r ⟨E, hE, hcard⟩
  have h9 := h3 (E.map X.subtype) (map_subtype_le E)
    (CFSG.QuasithinUnique.Setup.Lift.isElementaryAbelian_of_equiv
      (E.equivMapOfInjective X.subtype X.subtype_injective).symm hE)
  rw [card_map_of_injective X.subtype_injective, hcard] at h9
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (h9.trans (by norm_num))

theorem conj_closure_irreducible [Finite G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Nontrivial W] {X T : Subgroup G}
    (h3 : ∀ E : Subgroup G, E ≤ X → CFSG.IsElementaryAbelian 3 E → Nat.card E ≤ 9)
    (hT : IsSylowTwoOf T X) (φ : X →* LinearMap.GeneralLinearGroup (ZMod 2) W)
    (hirr : ∀ U : Submodule (ZMod 2) W, (∀ x : X, ∀ u ∈ U, (φ x : W →ₗ[ZMod 2] W) u ∈ U) →
      U = ⊥ ∨ U = ⊤)
    {a k : X} (hrank : finrank (ZMod 2) (LinearMap.range ((φ a : W →ₗ[ZMod 2] W) - 1)) = 1)
    (ha2 : φ a * φ a = 1) (hTa : ∀ x : X, (x : G) ∈ T → φ a * φ x = φ x * φ a)
    (hk : φ k ≠ 1) (hk3 : φ k ^ 3 = 1) (hak : φ a * φ k * (φ a)⁻¹ = (φ k)⁻¹)
    (U : Submodule (ZMod 2) W)
    (hU : ∀ x : X, ∀ u ∈ U, ((φ x * φ a * (φ x)⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) :
      W →ₗ[ZMod 2] W) u ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  have hHfin : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have hirr' : ∀ U : Submodule (ZMod 2) W,
      (∀ h ∈ φ.range, ∀ u ∈ U, (h : W →ₗ[ZMod 2] W) u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hirr U fun x => hU _ ⟨x, rfl⟩
  set t := φ a
  set b := φ k
  set N' := Subgroup.closure {x | ∃ h ∈ φ.range, x = h * t * h⁻¹} with hN'
  obtain ⟨s, hs, Wi, hint, hWne, hWinv, hWirr, -, -, hperm, htrans, hNi⟩ :=
    rank_one_normal_closure_splits_irreducible_summands φ.range hirr' ⟨a, rfl⟩ hrank hN'
  let Ni : Fin s → Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W) := fun i =>
    { carrier := {n | n ∈ N' ∧ ∀ j, j ≠ i → ∀ w ∈ Wi j, (n : W →ₗ[ZMod 2] W) w = w}
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨mul_mem hx hy, fun j hj w hw => ?_⟩
        rw [SteinbergBQ.RankOneHead.mul_apply', hy' j hj w hw, hx' j hj w hw]
      one_mem' := ⟨one_mem _, fun j _ w _ => rfl⟩
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨inv_mem hx, fun j hj w hw => ?_⟩
        rw [← hx' j hj w hw, SteinbergBQ.RankOne.inv_apply_apply, hx' j hj w hw] }
  obtain ⟨-, -, hindep, -, -, -, -, ht0, hconjN, htransN⟩ := hNi Ni fun i n => Iff.rfl
  set i₀ : Fin s := ⟨0, hs⟩
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, Units.val_one, sub_self, LinearMap.range_zero, finrank_bot] at hrank
    exact absurd hrank (by norm_num)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ha2
  have hgen : ∀ h ∈ φ.range, h * t * h⁻¹ ∈ N' := fun h hh => subset_closure ⟨h, hh, rfl⟩
  have htN : t ∈ N' := by simpa using hgen 1 (one_mem _)
  have hbN : b ∈ N' := mem_of_conj_mem_of_inverts (hgen b ⟨k, rfl⟩) htN hak hk3
  have hbW : ∀ y, (b : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) y)) = y := by
    intro y
    have h := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) W =>
      (g : W →ₗ[ZMod 2] W) y) hk3
    simpa [pow_succ, Module.End.mul_apply] using h
  have htW : ∀ y, (t : W →ₗ[ZMod 2] W) ((t : W →ₗ[ZMod 2] W) y) = y := by
    intro y
    have h := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) W =>
      (g : W →ₗ[ZMod 2] W) y) ha2
    simpa [Module.End.mul_apply] using h
  have htb : ∀ y, (t : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) y) =
      (b : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) ((t : W →ₗ[ZMod 2] W) y)) := by
    intro y
    have hb2 : b⁻¹ = b * b := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hk3)
    have h1 : t * b = b * b * t := by rw [mul_inv_eq_iff_eq_mul.1 hak, hb2]
    have h := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) W =>
      (g : W →ₗ[ZMod 2] W) y) h1
    simpa [Module.End.mul_apply] using h
  have hb0 : b ∈ Ni i₀ := by
    refine ⟨hbN, fun j hj w hw => ?_⟩
    have htw : ∀ y ∈ Wi j, (t : W →ₗ[ZMod 2] W) y = y := fun y hy => ht0.2 j hj y hy
    have hbw : (b : W →ₗ[ZMod 2] W) w ∈ Wi j := hWinv j b hbN w hw
    have h1 := htb w
    rw [htw w hw, htw _ hbw] at h1
    have h2 := congrArg (b : W →ₗ[ZMod 2] W) h1
    rw [hbW] at h2
    exact h1.trans h2
  have hs2 : s ≤ 2 := by
    by_contra hs3
    push Not at hs3
    have hbsub : ∀ y, (b : W →ₗ[ZMod 2] W) y - y ∈ Wi i₀ := by
      intro y
      have hy : y ∈ ⨆ i, Wi i := by
        rw [hint.submodule_iSup_eq_top]
        exact Submodule.mem_top
      refine Submodule.iSup_induction Wi (motive := fun y => (b : W →ₗ[ZMod 2] W) y - y ∈ Wi i₀)
        hy (fun j y hy => ?_) (by simp) (fun y y' h h' => ?_)
      · by_cases hj : j = i₀
        · rw [hj] at hy
          exact sub_mem (hWinv _ b hbN y hy) hy
        · rw [hb0.2 j hj y hy, sub_self]
          exact zero_mem _
      · rw [map_add, add_sub_add_comm]
        exact add_mem h h'
    obtain ⟨y₀, hy₀⟩ : ∃ y, (b : W →ₗ[ZMod 2] W) y - y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hk (Units.ext (LinearMap.ext fun y => sub_eq_zero.1 (hcon y)))
    have hmemP : ∀ y, (b : W →ₗ[ZMod 2] W) y - y ∈
        LinearMap.range ((b : W →ₗ[ZMod 2] W) - 1) :=
      fun y => ⟨y, by rw [LinearMap.sub_apply, Module.End.one_apply]⟩
    have hPW : ∀ v ∈ LinearMap.range ((b : W →ₗ[ZMod 2] W) - 1), v ∈ Wi i₀ := by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.sub_apply, Module.End.one_apply]
      exact hbsub y
    have hTP : ∀ v ∈ LinearMap.range ((b : W →ₗ[ZMod 2] W) - 1),
        (t : W →ₗ[ZMod 2] W) v ∈ LinearMap.range ((b : W →ₗ[ZMod 2] W) - 1) := by
      rintro _ ⟨y, rfl⟩
      refine ⟨(b : W →ₗ[ZMod 2] W) ((t : W →ₗ[ZMod 2] W) y) + (t : W →ₗ[ZMod 2] W) y, ?_⟩
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_add, map_sub, htb]
      abel
    have hPker : ∀ v ∈ LinearMap.range ((b : W →ₗ[ZMod 2] W) - 1),
        (b : W →ₗ[ZMod 2] W) v = v → v = 0 := by
      intro v hv hfix
      have hv' : v ∈ LinearMap.range ((b : W →ₗ[ZMod 2] W) - 1) ⊓
          LinearMap.ker ((b : W →ₗ[ZMod 2] W) - 1) :=
        Submodule.mem_inf.2 ⟨hv, by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hfix, sub_self]⟩
      rw [range_inf_ker_eq_bot b hk3] at hv'
      exact hv'
    obtain ⟨p, hpP, hp0, htp⟩ : ∃ p ∈ LinearMap.range ((b : W →ₗ[ZMod 2] W) - 1), p ≠ 0 ∧
        (t : W →ₗ[ZMod 2] W) p = p := by
      have key : ∀ v ∈ LinearMap.range ((b : W →ₗ[ZMod 2] W) - 1), v ≠ 0 →
          ∃ p ∈ LinearMap.range ((b : W →ₗ[ZMod 2] W) - 1), p ≠ 0 ∧
            (t : W →ₗ[ZMod 2] W) p = p := by
        intro v hv hv0
        by_cases hfix : (t : W →ₗ[ZMod 2] W) v = v
        · exact ⟨v, hv, hv0, hfix⟩
        · refine ⟨(t : W →ₗ[ZMod 2] W) v - v, sub_mem (hTP v hv) hv, sub_ne_zero.2 hfix, ?_⟩
          rw [map_sub, htW, ← neg_sub, ZModModule.neg_eq_self]
      exact key _ (hmemP y₀) hy₀
    have hbp : (b : W →ₗ[ZMod 2] W) p ≠ p := fun h => hp0 (hPker p hpP h)
    set X₀ : Fin 3 → W := ![p, (b : W →ₗ[ZMod 2] W) p,
      (b : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) p)]
    have hX₀ : Function.Injective X₀ := by
      refine injective_fin3 (fun h => hbp h.symm) (fun h => hbp ?_) (fun h => hbp ?_)
      · have h' := congrArg (b : W →ₗ[ZMod 2] W) h
        rw [hbW] at h'
        exact h'
      · exact (SteinbergBQ.RankOneHead.injective_apply b h).symm
    have hX₀W : ∀ m, X₀ m ∈ Wi i₀ := by
      have hp : p ∈ Wi i₀ := hPW p hpP
      have hbp' : (b : W →ₗ[ZMod 2] W) p ∈ Wi i₀ := hWinv i₀ b hbN p hp
      have hbbp : (b : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) p) ∈ Wi i₀ :=
        hWinv i₀ b hbN _ hbp'
      intro m
      fin_cases m
      exacts [hp, hbp', hbbp]
    have hs12 : ∀ m, (t : W →ₗ[ZMod 2] W) (X₀ m) = X₀ (Equiv.swap 1 2 m) := by
      intro m
      fin_cases m
      · show (t : W →ₗ[ZMod 2] W) p = X₀ (Equiv.swap 1 2 0)
        rw [show Equiv.swap (1 : Fin 3) 2 0 = 0 by decide]
        exact htp
      · show (t : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) p) = X₀ (Equiv.swap 1 2 1)
        rw [show Equiv.swap (1 : Fin 3) 2 1 = 2 by decide, htb, htp]
        rfl
      · show (t : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) p)) =
          X₀ (Equiv.swap 1 2 2)
        rw [show Equiv.swap (1 : Fin 3) 2 2 = 1 by decide, htb, htb, htp, hbW]
        rfl
    have hs02 : ∀ m, (t : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) (X₀ m)) =
        X₀ (Equiv.swap 0 2 m) := by
      intro m
      fin_cases m
      · show (t : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) p) = X₀ (Equiv.swap 0 2 0)
        rw [show Equiv.swap (0 : Fin 3) 2 0 = 2 by decide, htb, htp]
        rfl
      · show (t : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) p)) =
          X₀ (Equiv.swap 0 2 1)
        rw [show Equiv.swap (0 : Fin 3) 2 1 = 1 by decide, htb, htb, htp, hbW]
        rfl
      · show (t : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W) ((b : W →ₗ[ZMod 2] W)
          ((b : W →ₗ[ZMod 2] W) p))) = X₀ (Equiv.swap 0 2 2)
        rw [show Equiv.swap (0 : Fin 3) 2 2 = 0 by decide, hbW, htp]
        rfl
    choose hh hhH hhW hhN using htransN i₀
    let Xs : Fin s → Fin 3 → W := fun j m => (hh j : W →ₗ[ZMod 2] W) (X₀ m)
    have hXs : ∀ j, Function.Injective (Xs j) := fun j =>
      (SteinbergBQ.RankOneHead.injective_apply (hh j)).comp hX₀
    have hXsW : ∀ j m, Xs j m ∈ Wi j := fun j m => by
      rw [← hhW j]
      exact Submodule.mem_map_of_mem (hX₀W m)
    have hconjNi : ∀ j, ∀ g ∈ Ni i₀, hh j * g * (hh j)⁻¹ ∈ Ni j := fun j g hg => by
      rw [← hhN j]
      exact ⟨g, hg, rfl⟩
    have hconj_apply : ∀ j (g : LinearMap.GeneralLinearGroup (ZMod 2) W) (σ : Equiv.Perm (Fin 3)),
        (∀ m, (g : W →ₗ[ZMod 2] W) (X₀ m) = X₀ (σ m)) → ∀ m,
        ((hh j * g * (hh j)⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W)
          (Xs j m) = Xs j (σ m) := by
      intro j g σ hσ m
      show ((hh j * g * (hh j)⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W)
        ((hh j : W →ₗ[ZMod 2] W) (X₀ m)) = (hh j : W →ₗ[ZMod 2] W) (X₀ (σ m))
      rw [SteinbergBQ.RankOneHead.mul_apply', SteinbergBQ.RankOneHead.mul_apply',
        SteinbergBQ.RankOne.inv_apply_apply, hσ]
    have hinvol : ∀ j (g : LinearMap.GeneralLinearGroup (ZMod 2) W), g * g = 1 →
        hh j * g * (hh j)⁻¹ * (hh j * g * (hh j)⁻¹) = 1 := by
      intro j g hg
      calc hh j * g * (hh j)⁻¹ * (hh j * g * (hh j)⁻¹) = hh j * (g * g) * (hh j)⁻¹ := by group
        _ = 1 := by rw [hg, mul_one, mul_inv_cancel]
    have htb2 : t * b * (t * b) = 1 := by
      calc t * b * (t * b) = t * b * t⁻¹ * b := by rw [htinv]; group
        _ = 1 := by rw [hak, inv_mul_cancel]
    let S : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W) :=
      ⨅ j, MulAction.stabilizer (LinearMap.GeneralLinearGroup (ZMod 2) W) (Set.range (Xs j))
    let Θ : S →* (Fin s → Equiv.Perm (Fin 3)) := MonoidHom.pi fun j =>
      (tripleHom (Xs j) (hXs j)).comp (Subgroup.inclusion (iInf_le (fun j =>
        MulAction.stabilizer (LinearMap.GeneralLinearGroup (ZMod 2) W) (Set.range (Xs j))) j))
    let Y₀ : Subgroup X := S.comap φ
    let f : Y₀ →* (Fin s → Equiv.Perm (Fin 3)) := Θ.comp (φ.subgroupComap S)
    have hfval : ∀ (y : Y₀) (σ : Fin s → Equiv.Perm (Fin 3)),
        (∀ j m, (φ y : W →ₗ[ZMod 2] W) (Xs j m) = Xs j (σ j m)) → f y = σ := by
      intro y σ h
      funext j
      exact (tripleHom_eq_iff (Xs j) (hXs j) _ (σ j)).2 (h j)
    have hreal : ∀ j (g : LinearMap.GeneralLinearGroup (ZMod 2) W), g ∈ Ni i₀ → g * g = 1 →
        hh j * g * (hh j)⁻¹ ∈ φ.range → ∀ σ : Equiv.Perm (Fin 3),
        (∀ m, (g : W →ₗ[ZMod 2] W) (X₀ m) = X₀ (σ m)) →
          (Pi.mulSingle j σ : Fin s → Equiv.Perm (Fin 3)) ∈ f.range := by
      intro j g hg hg2 hgH σ hσ
      obtain ⟨y, hy⟩ := hgH
      have hgN := hconjNi j g hg
      have hgact : ∀ j' m, ((hh j * g * (hh j)⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) :
          W →ₗ[ZMod 2] W) (Xs j' m) =
            Xs j' ((Pi.mulSingle j σ : Fin s → Equiv.Perm (Fin 3)) j' m) := by
        intro j' m
        by_cases hj : j' = j
        · subst hj
          rw [Pi.mulSingle_eq_same]
          exact hconj_apply j' g σ hσ m
        · rw [Pi.mulSingle_eq_of_ne hj, Equiv.Perm.one_apply]
          exact hgN.2 j' hj _ (hXsW j' m)
      have hyS : φ y ∈ S := by
        rw [hy]
        exact mem_iInf.2 fun j' =>
          mem_stabilizer_range_of_involution (hinvol j g hg2) fun m => ⟨_, (hgact j' m)⟩
      refine ⟨⟨y, hyS⟩, hfval _ _ fun j' m => ?_⟩
      show ((φ y : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) (Xs j' m) = _
      rw [hy]
      exact hgact j' m
    have hf : Function.Surjective f := by
      intro σ
      refine Subgroup.pi_mem_of_mulSingle_mem (H := f.range) σ fun j => ?_
      have htH : t ∈ φ.range := ⟨a, rfl⟩
      have hbH : b ∈ φ.range := ⟨k, rfl⟩
      exact perm_three_mem_closure ((f.range).comap
        (MonoidHom.mulSingle (fun _ : Fin s => Equiv.Perm (Fin 3)) j))
        (hreal j t ht0 ha2 (mul_mem (mul_mem (hhH j) htH) (inv_mem (hhH j))) _ hs12)
        (hreal j (t * b) (mul_mem ht0 hb0) htb2
          (mul_mem (mul_mem (hhH j) (mul_mem htH hbH)) (inv_mem (hhH j))) _
          fun m => by rw [SteinbergBQ.RankOneHead.mul_apply']; exact hs02 m) (σ j)
    have h1 := CFSG.QuasithinUnique.Setup.Lift.sym_three_pow_section_forces_three_rank s Y₀ f hf
    have h2 := pRank_three_le_two h3
    omega
  have hWinj : ∀ i j, Wi i = Wi j → i = j := by
    intro i j hij
    by_contra hne
    have hd : Disjoint (Wi i) (Wi j) := hint.submodule_iSupIndep.pairwiseDisjoint hne
    rw [hij, disjoint_self] at hd
    exact hWne j hd
  have hs1 : s = 1 := by
    rcases (show s = 1 ∨ s = 2 by omega) with h | h
    · exact h
    exfalso
    set i₁ : Fin s := ⟨1, by omega⟩
    have hcases : ∀ j : Fin s, j = i₀ ∨ j = i₁ := by
      intro j
      rcases Nat.lt_or_ge (j : ℕ) 1 with h' | h'
      · left
        exact Fin.ext (by show (j : ℕ) = 0; omega)
      · right
        exact Fin.ext (by show (j : ℕ) = 1; have := j.2; omega)
    have hi01 : i₀ ≠ i₁ := fun h => absurd (congrArg Fin.val h) (by show (0 : ℕ) ≠ 1; norm_num)
    obtain ⟨x₁, hx₁⟩ : ∃ x₁ : X, (Wi i₀).map (φ x₁ : W →ₗ[ZMod 2] W) = Wi i₁ := by
      obtain ⟨g, ⟨x₁, rfl⟩, hg⟩ := htrans i₀ i₁
      exact ⟨x₁, hg⟩
    let Y₁ : Subgroup X :=
      { carrier := {x | (Wi i₀).map (φ x : W →ₗ[ZMod 2] W) = Wi i₀}
        mul_mem' := by
          intro x y hx hy
          simp only [Set.mem_ofPred_eq] at hx hy ⊢
          rw [map_mul, Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, hy, hx]
        one_mem' := by
          simp only [Set.mem_ofPred_eq, map_one, Units.val_one, Module.End.one_eq_id,
            Submodule.map_id]
        inv_mem' := by
          intro x hx
          simp only [Set.mem_ofPred_eq] at hx ⊢
          conv_lhs => rw [← hx]
          rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← Units.val_mul, ← map_mul,
            inv_mul_cancel, map_one, Units.val_one, Module.End.one_eq_id, Submodule.map_id] }
    have hY₁ : Y₁.index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨x₁, fun y => ?_⟩
      obtain ⟨j₀, hj₀⟩ := hperm (φ y) ⟨y, rfl⟩ i₀
      obtain ⟨j₁, hj₁⟩ := hperm (φ y) ⟨y, rfl⟩ i₁
      have hmul : (Wi i₀).map (φ (y * x₁) : W →ₗ[ZMod 2] W) = Wi j₁ := by
        rw [map_mul, Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, hx₁, hj₁]
      have hne : j₀ ≠ j₁ := by
        intro hj
        have h1 : (Wi i₀).map (φ y : W →ₗ[ZMod 2] W) = (Wi i₁).map (φ y : W →ₗ[ZMod 2] W) := by
          rw [hj₀, hj₁, hj]
        exact hi01 (hWinj _ _ (Submodule.map_injective_of_injective
          (SteinbergBQ.RankOneHead.injective_apply (φ y)) h1))
      change Xor ((Wi i₀).map (φ (y * x₁) : W →ₗ[ZMod 2] W) = Wi i₀)
        ((Wi i₀).map (φ y : W →ₗ[ZMod 2] W) = Wi i₀)
      rw [hmul, hj₀]
      by_cases h0 : j₀ = i₀
      · refine Or.inr ⟨by rw [h0], fun h => ?_⟩
        exact hne (h0.trans (hWinj _ _ h).symm)
      · refine Or.inl ⟨?_, fun h => h0 (hWinj _ _ h)⟩
        rcases hcases j₀ with h' | h'
        · exact absurd h' h0
        · rcases hcases j₁ with h'' | h''
          · rw [h'']
          · exact absurd (h'.trans h''.symm) hne
    have hTY : T.subgroupOf X ≤ Y₁ := by
      intro x hx
      change (Wi i₀).map (φ x : W →ₗ[ZMod 2] W) = Wi i₀
      obtain ⟨j, hj⟩ := hperm (φ x) ⟨x, rfl⟩ i₀
      rw [hj]
      by_contra hne
      have hji : i₀ ≠ j := fun h => hne (by rw [h])
      have h1 := hconjN (φ x) ⟨x, rfl⟩ i₀ j hj
      have h2 : t ∈ Ni j := by
        rw [← h1]
        refine ⟨t, ht0, ?_⟩
        change φ x * t * (φ x)⁻¹ = t
        rw [← hTa x hx, mul_inv_cancel_right]
      have hd : Disjoint (Ni i₀) (Ni j) := hindep.pairwiseDisjoint hji
      exact ht1 (Subgroup.disjoint_def.1 hd ht0 h2)
    have hdvd := Subgroup.index_dvd_of_le hTY
    rw [hY₁] at hdvd
    exact hT.2.2 hdvd
  have hall : ∀ j : Fin s, j = i₀ := fun j => Fin.ext (by show (j : ℕ) = 0; have := j.2; omega)
  have hW0 : Wi i₀ = ⊤ := by
    rw [← hint.submodule_iSup_eq_top]
    exact le_antisymm (le_iSup Wi i₀) (iSup_le fun j => by rw [hall j])
  have hUN : ∀ n ∈ N', ∀ u ∈ U, (n : W →ₗ[ZMod 2] W) u ∈ U := by
    intro n hn
    rw [hN'] at hn
    induction hn using Subgroup.closure_induction'' with
    | mem x hx =>
      obtain ⟨_, ⟨y, rfl⟩, rfl⟩ := hx
      exact hU y
    | inv_mem x hx =>
      obtain ⟨_, ⟨y, rfl⟩, rfl⟩ := hx
      have e : (φ y * t * (φ y)⁻¹)⁻¹ = φ y * t * (φ y)⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev, inv_inv, htinv]
        group
      rw [e]
      exact hU y
    | one =>
      intro u hu
      exact hu
    | mul x y _ _ hx hy =>
      intro u hu
      rw [SteinbergBQ.RankOneHead.mul_apply']
      exact hx _ (hy u hu)
  rcases hWirr i₀ U (by rw [hW0]; exact le_top) hUN with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hW0)

end ThreeRank

section Main

universe u v

theorem exists_linear_model {G : Type u} [Group G] {X V : Subgroup G}
    (hXV : X ≤ normalizer (V : Set G)) (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hV2 : ∀ v ∈ V, v * v = 1) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module (ZMod 2) M) (ι : V ≃* Multiplicative M)
      (ρ : X →* LinearMap.GeneralLinearGroup (ZMod 2) M), ∀ (x : X) (v w : V),
        (w : G) = x * v * x⁻¹ →
          (ρ x : M →ₗ[ZMod 2] M) (Multiplicative.toAdd (ι v)) = Multiplicative.toAdd (ι w) := by
  let instV : CommGroup V :=
    { (inferInstance : Group V) with mul_comm := fun a b => Subtype.ext (hVc a a.2 b b.2) }
  let instM : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    exact congrArg Additive.ofMul (Subtype.ext (hV2 _ (Additive.toMul x).2))
  let ι : V ≃* Multiplicative (Additive V) :=
    { toFun := fun v => Multiplicative.ofAdd (Additive.ofMul v)
      invFun := fun m => Additive.toMul (Multiplicative.toAdd m)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨Additive V, inferInstance, instM, ι,
    (linAut ι).comp (V.normalizerMonoidHom.comp (Subgroup.inclusion hXV)), fun x v w hw => ?_⟩
  rw [MonoidHom.comp_apply, linAut_apply_ι]
  have e : (V.normalizerMonoidHom.comp (Subgroup.inclusion hXV)) x v = w := Subtype.ext hw.symm
  rw [e]

variable {G : Type u} [Group G] [Finite G] {X T K A U V : Subgroup G}

theorem actual_A3_three_rank_irreducible_transvection_normal_closure (hX : CharTwo X)
    (hT : IsSylowTwoOf T X) (hKX : K ≤ X) (hK : IsShort2 K)
    (hK3 : Nat.card (K ⧸ CFSG.pCore 2 K) = 3) (hTK : T ≤ normalizer (K : Set G))
    (hAT : A ≤ T) (hAn : T ≤ normalizer (A : Set G)) (hU : U = blockQ K) (hAU : ⁅A, U⁆ ≠ ⊥)
    (hE2 : Nat.card ↥(A ⊓ centralizer (U : Set G)) = 2)
    (h3 : ∀ E : Subgroup G, E ≤ X → CFSG.IsElementaryAbelian 3 E → Nat.card E ≤ 9)
    (hV : V = conjJoin X U) :
    (∃ (M : Type u) (_ : AddCommGroup M) (_ : Module (ZMod 2) M) (ι : V ≃* Multiplicative M)
      (ρ : X →* LinearMap.GeneralLinearGroup (ZMod 2) M), ∀ (x : X) (v w : V),
        (w : G) = x * v * x⁻¹ →
          (ρ x : M →ₗ[ZMod 2] M) (Multiplicative.toAdd (ι v)) = Multiplicative.toAdd (ι w)) ∧
    ∀ (M : Type v) [AddCommGroup M] [Module (ZMod 2) M] (ι : V ≃* Multiplicative M)
      (ρ : X →* LinearMap.GeneralLinearGroup (ZMod 2) M),
      (∀ (x : X) (v w : V), (w : G) = x * v * x⁻¹ →
        (ρ x : M →ₗ[ZMod 2] M) (Multiplicative.toAdd (ι v)) = Multiplicative.toAdd (ι w)) →
      ∃ τ : ρ.range,
        (A.subgroupOf X).map ρ = zpowers (τ : LinearMap.GeneralLinearGroup (ZMod 2) M) ∧
        Nat.card ((A.subgroupOf X).map ρ) = 2 ∧
        (τ : LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ (T.subgroupOf X).map ρ ⊓
          centralizer (((T.subgroupOf X).map ρ :
            Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M)) : Set _) ∧
        finrank (ZMod 2) (LinearMap.range
          (((τ : LinearMap.GeneralLinearGroup (ZMod 2) M) : M →ₗ[ZMod 2] M) - 1)) = 1 ∧
        (∀ b ∈ (K.subgroupOf X).map ρ, (τ : LinearMap.GeneralLinearGroup (ZMod 2) M) * b *
          (τ : LinearMap.GeneralLinearGroup (ZMod 2) M)⁻¹ = b⁻¹) ∧
        Nat.card ((K.subgroupOf X).map ρ) = 3 ∧
        (T.subgroupOf X).map ρ ≤ normalizer (((K.subgroupOf X).map ρ :
          Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M)) : Set _) ∧
        CFSG.pCore 2 ρ.range = ⊥ ∧
        (∀ (N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M)) (C : Submodule (ZMod 2) M),
          N = Subgroup.closure {x | ∃ h ∈ ρ.range,
            x = h * (τ : LinearMap.GeneralLinearGroup (ZMod 2) M) * h⁻¹} →
          (∀ v, v ∈ C ↔ ∀ n ∈ N, (n : M →ₗ[ZMod 2] M) v = v) →
          N ≤ ρ.range ∧ ∃ ρW : ρ.range →* LinearMap.GeneralLinearGroup (ZMod 2) (M ⧸ C),
            (∀ (h : ρ.range) (v : M), (ρW h : (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) (C.mkQ v) =
              C.mkQ (((h : LinearMap.GeneralLinearGroup (ZMod 2) M) : M →ₗ[ZMod 2] M) v)) ∧
            Function.Injective ρW ∧ Nontrivial (M ⧸ C) ∧
            (∀ W : Submodule (ZMod 2) (M ⧸ C), (∀ h : ρ.range, ∀ w ∈ W,
              (ρW h : (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) w ∈ W) → W = ⊥ ∨ W = ⊤) ∧
            (∀ W : Submodule (ZMod 2) (M ⧸ C), (∀ h : ρ.range,
              (h : LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ N → ∀ w ∈ W,
                (ρW h : (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) w ∈ W) → W = ⊥ ∨ W = ⊤) ∧
            (K.subgroupOf X).map ρ ≤ N ∧
            finrank (ZMod 2) (LinearMap.range
              ((ρW τ : (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) - 1)) = 1 ∧
            ∀ b : ρ.range, (b : LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ (K.subgroupOf X).map ρ →
              b ≠ 1 →
              Set.InjOn C.mkQ {m | ∃ u : V, (u : G) ∈ U ∧ Multiplicative.toAdd (ι u) = m} ∧
              C.mkQ '' {m | ∃ u : V, (u : G) ∈ U ∧ Multiplicative.toAdd (ι u) = m} =
                (LinearMap.range ((ρW b : (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) - 1) : Set (M ⧸ C)) ∧
              finrank (ZMod 2) (LinearMap.range ((ρW b : (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) - 1)) =
                2) ∧
        ∀ (H₀ : Subgroup ρ.range) (f : H₀ →* (Fin 3 → Equiv.Perm (Fin 3))),
          ¬ Function.Surjective f := by
  classical
  obtain ⟨-, -, -, -, ⟨-, hXV, hVea, -⟩, -, -, -, -, -, -, -, -, -, -, hVcomm, -, -, -⟩ :=
    a3_config_structure hX hT hKX hK hK3 hTK rfl hU hV hAT hAn hAU rfl hE2
  refine ⟨exists_linear_model hXV hVcomm fun v hv => ?_, ?_⟩
  · have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hVea.2 ⟨v, hv⟩
    have h' := congrArg Subtype.val h
    simpa [sq] using h'
  intro M _ _ ι ρ hρ
  obtain ⟨hO2, hB3, hTstB, hUr, a₁, ha₁A, hρAz, hρA2, hρAc, -, hτinv, hrank, hspan⟩ :=
    a3_linear_actor hX hT hKX hK hK3 hTK rfl hU hV hAT hAn hAU rfl hE2 ι ρ hρ
  have hFin : Finite M := Finite.of_equiv V (ι.toEquiv.trans Multiplicative.toAdd)
  have hMfin : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have hHfin : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  set τ : ρ.range := ρ.rangeRestrict a₁
  have hτA : ρ a₁ ∈ (A.subgroupOf X).map ρ := mem_map_of_mem ρ ha₁A
  have hB3' : ∀ b ∈ (K.subgroupOf X).map ρ, b ^ 3 = 1 := fun b hb => by
    have h := Subgroup.orderOf_dvd_natCard _ hb
    rw [hB3] at h
    exact orderOf_dvd_iff_pow_eq_one.1 h
  have hτ2 : ρ a₁ * ρ a₁ = 1 := by
    have h := Nat.card_zpowers (ρ a₁)
    rw [← hρAz, hρA2] at h
    have h' := pow_orderOf_eq_one (ρ a₁)
    rw [← h, sq] at h'
    exact h'
  refine ⟨τ, hρAz, hρA2, hρAc hτA, hrank, hτinv, hB3, hTstB, hO2, ?_, ?_⟩
  · intro N C hN hC
    obtain ⟨-, -, -, -, ρW, hρW, hinjW, hnt, hirrW, -, hrkW⟩ :=
      rank_one_conjugate_span_faithful_irreducible_head (p := 2) ρ.range hO2 τ.2 hrank rfl hspan
        hN hC
    have hNgen : ∀ h ∈ ρ.range, h * ρ a₁ * h⁻¹ ∈ N := fun h hh => by
      rw [hN]
      exact subset_closure ⟨h, hh, rfl⟩
    have hτN : ρ a₁ ∈ N := by simpa using hNgen 1 (one_mem _)
    have hBN : (K.subgroupOf X).map ρ ≤ N := by
      rintro _ ⟨k, hk, rfl⟩
      exact mem_of_conj_mem_of_inverts (hNgen _ ⟨k, rfl⟩) hτN (hτinv _ (mem_map_of_mem ρ hk))
        (hB3' _ (mem_map_of_mem ρ hk))
    have hrkτ : finrank (ZMod 2) (LinearMap.range
        ((ρW τ : (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) - 1)) = 1 :=
      hrkW τ ⟨1, one_mem _, by simp⟩
    let φ : X →* LinearMap.GeneralLinearGroup (ZMod 2) (M ⧸ C) := ρW.comp ρ.rangeRestrict
    have hφ : ∀ x y : X, ρ x = ρ y → φ x = φ y := fun x y h => congrArg ρW (Subtype.ext h)
    have hφ1 : ∀ x : X, ρ x ≠ 1 → φ x ≠ 1 := fun x hx h => hx (by
      have h1 := hinjW (h.trans (map_one ρW).symm)
      exact congrArg Subtype.val h1)
    obtain ⟨k₀, hk₀K, hk₀⟩ : ∃ k₀ : X, (k₀ : G) ∈ K ∧ ρ k₀ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : (K.subgroupOf X).map ρ = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨k, hk, rfl⟩
        exact hcon k hk
      rw [hbot, Subgroup.card_bot] at hB3
      omega
    have hNirr : ∀ W : Submodule (ZMod 2) (M ⧸ C), (∀ h : ρ.range,
        (h : LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ N → ∀ w ∈ W,
          (ρW h : (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) w ∈ W) → W = ⊥ ∨ W = ⊤ := by
      intro W hW
      refine conj_closure_irreducible h3 hT φ ?_ (a := a₁) (k := k₀) hrkτ ?_ ?_ (hφ1 k₀ hk₀)
        ?_ ?_ W ?_
      · intro U' hU'
        refine hirrW U' fun h u hu => ?_
        obtain ⟨x, rfl⟩ := ρ.rangeRestrict_surjective h
        exact hU' x u hu
      · have h := hφ (a₁ * a₁) 1 (by rw [map_mul, map_one, hτ2])
        rwa [map_mul, map_one] at h
      · intro x hx
        have hc := mem_centralizer_iff.1 (mem_inf.1 (hρAc hτA)).2 (ρ x) (mem_map_of_mem ρ hx)
        have h := hφ (a₁ * x) (x * a₁) (by rw [map_mul, map_mul, hc])
        rwa [map_mul, map_mul] at h
      · have h := hφ (k₀ ^ 3) 1 (by rw [map_pow, map_one, hB3' _ (mem_map_of_mem ρ hk₀K)])
        rwa [map_pow, map_one] at h
      · have h := hφ (a₁ * k₀ * a₁⁻¹) k₀⁻¹ (by
          rw [map_mul, map_mul, map_inv, map_inv, hτinv _ (mem_map_of_mem ρ hk₀K)])
        rwa [map_mul, map_mul, map_inv, map_inv] at h
      · intro x u hu
        have hmem : ((ρ.rangeRestrict x * τ * (ρ.rangeRestrict x)⁻¹ : ρ.range) :
            LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ N := hNgen (ρ x) ⟨x, rfl⟩
        have h := hW _ hmem u hu
        rwa [map_mul, map_mul, map_inv] at h
    refine ⟨hN ▸ SteinbergBQ.RankOneHead.closure_conj_le τ.2, ρW, hρW, hinjW, hnt, hirrW, hNirr,
      hBN, hrkτ, fun b hbB hb1 => ?_⟩
    obtain ⟨k, hk, hbk⟩ := hbB
    have hk1 : ρ k ≠ 1 := fun h => hb1 (Subtype.ext (hbk.symm.trans h))
    obtain ⟨hiff, hfr⟩ := hUr k hk hk1
    have hkN : ρ k ∈ N := hBN (mem_map_of_mem ρ hk)
    have hCk : ∀ c ∈ C, (ρ k : M →ₗ[ZMod 2] M) c = c := fun c hc => (hC c).1 hc _ hkN
    have hRC : Disjoint (LinearMap.range ((ρ k : M →ₗ[ZMod 2] M) - 1)) C := by
      rw [Submodule.disjoint_def]
      intro m hm hmC
      have hm' : m ∈ LinearMap.range ((ρ k : M →ₗ[ZMod 2] M) - 1) ⊓
          LinearMap.ker ((ρ k : M →ₗ[ZMod 2] M) - 1) :=
        Submodule.mem_inf.2 ⟨hm, by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hCk m hmC, sub_self]⟩
      rw [range_inf_ker_eq_bot (ρ k) (hB3' _ (mem_map_of_mem ρ hk))] at hm'
      exact hm'
    have hUM : {m | ∃ u : V, (u : G) ∈ U ∧ Multiplicative.toAdd (ι u) = m} =
        (LinearMap.range ((ρ k : M →ₗ[ZMod 2] M) - 1) : Set M) := by
      ext m
      exact (hiff m).symm
    have hcomm : ∀ y : M, C.mkQ (((ρ k : M →ₗ[ZMod 2] M) - 1) y) =
        ((ρW b : (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) - 1) (C.mkQ y) := by
      intro y
      rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
        map_sub, hρW b y, ← hbk]
    have hrange : LinearMap.range ((ρW b : (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) - 1) =
        (LinearMap.range ((ρ k : M →ₗ[ZMod 2] M) - 1)).map C.mkQ := by
      ext z
      constructor
      · rintro ⟨z', rfl⟩
        obtain ⟨y, rfl⟩ := C.mkQ_surjective z'
        exact ⟨_, ⟨y, rfl⟩, hcomm y⟩
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨C.mkQ y, (hcomm y).symm⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hUM]
      intro m₁ hm₁ m₂ hm₂ h
      have h1 : m₁ - m₂ ∈ C := (Submodule.Quotient.eq C).1 h
      have h2 : m₁ - m₂ ∈ LinearMap.range ((ρ k : M →ₗ[ZMod 2] M) - 1) := sub_mem hm₁ hm₂
      exact sub_eq_zero.1 (Submodule.disjoint_def.1 hRC _ h2 h1)
    · rw [hUM, hrange, Submodule.map_coe]
    · rw [hrange, SteinbergBQ.RankOneHead.finrank_map_of_disjoint _ _
        (by rw [Submodule.ker_mkQ]; exact hRC)]
      exact hfr
  ·
    intro H₀ f hf
    let Y₀ : Subgroup X := H₀.comap ρ.rangeRestrict
    let f' : Y₀ →* (Fin 3 → Equiv.Perm (Fin 3)) := f.comp (ρ.rangeRestrict.subgroupComap H₀)
    have hf' : Function.Surjective f' := by
      intro σ
      obtain ⟨⟨h, hh⟩, rfl⟩ := hf σ
      obtain ⟨x, hx⟩ := ρ.rangeRestrict_surjective h
      have hxY : x ∈ Y₀ := by
        change ρ.rangeRestrict x ∈ H₀
        rw [hx]
        exact hh
      refine ⟨⟨x, hxY⟩, ?_⟩
      change f ⟨ρ.rangeRestrict x, _⟩ = f ⟨h, hh⟩
      congr 1
      exact Subtype.ext hx
    have h1 := CFSG.QuasithinUnique.Setup.Lift.sym_three_pow_section_forces_three_rank 3 Y₀ f' hf'
    have h2 := pRank_three_le_two h3
    omega

end Main

end CFSG.Quasithin.SteinbergBN
