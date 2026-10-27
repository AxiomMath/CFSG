module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGA
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGG
public import CFSG.Quasithin.Vol2.Ch11SecDFacts4
public import CFSG.Quasithin.Vol2.Ch11SecO1B
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA SecS SecS.C11P9A
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom torusHom_injective torus)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

@[expose] def pairHom (K : Type) [Field K] : Kˣ × Kˣ →* (Fin 2 → Kˣ) where
  toFun t := ![t.1, t.2]
  map_one' := by
    funext i
    fin_cases i <;> rfl
  map_mul' s t := by
    funext i
    fin_cases i <;> rfl

theorem pairHom_bijective (K : Type) [Field K] : Function.Bijective (pairHom K) := by
  refine ⟨fun s t h => Prod.ext (congrFun h 0) (congrFun h 1), fun t => ⟨(t 0, t 1), ?_⟩⟩
  funext i
  fin_cases i <;> rfl

omit [Finite G] in
theorem exists_elemAbelian_of_range {X V : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hXC : X ⊓ Subgroup.centralizer (V : Set G) = ⊥)
    {K : Type} [Field K] [Finite K] (φ : Kˣ × Kˣ →* MulAut ↥V) (hφ : Function.Injective φ)
    (hD : autOn X V = φ.range) {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card Kˣ) :
    ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpK
  set E₀ : Subgroup (Kˣ × Kˣ) := (Subgroup.zpowers ζ).prod (Subgroup.zpowers ζ)
  set c := conjHomL V X hXV
  have hc : Function.Injective c := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conjHomL, hXC]
    simp only [Subgroup.bot_subgroupOf]
  have hle : E₀.map φ ≤ c.range := by
    rw [range_conjHomL, hD]
    exact Subgroup.map_le_range φ E₀
  set E₁ := (E₀.map φ).comap c
  have hE₁ : E₁.map c = E₀.map φ := Subgroup.map_comap_eq_self hle
  have hmem : ∀ a ∈ E₁, ∃ e ∈ E₀, φ e = c a := fun a ha => ha
  refine ⟨E₁.map X.subtype, Subgroup.map_subtype_le _, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨⟨a, ha⟩, ha₁, rfl⟩ := a.2
    obtain ⟨⟨b, hb⟩, hb₁, rfl⟩ := b.2
    obtain ⟨e, -, he⟩ := hmem _ ha₁
    obtain ⟨e', -, he'⟩ := hmem _ hb₁
    have h1 : c (⟨a, ha⟩ * ⟨b, hb⟩) = c (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul, ← he, ← he', ← map_mul, ← map_mul, mul_comm]
    have h2 := congrArg Subtype.val (hc h1)
    exact Subtype.ext h2
  · obtain ⟨⟨y, hyX⟩, hy₁, rfl⟩ := hy
    obtain ⟨⟨e₁, e₂⟩, ⟨h₁, h₂⟩, he⟩ := hmem _ hy₁
    have hpow : ∀ e ∈ Subgroup.zpowers ζ, e ^ p = 1 := fun e he =>
      orderOf_dvd_iff_pow_eq_one.mp (hζ ▸ orderOf_dvd_of_mem_zpowers he)
    have hp1 : (e₁, e₂) ^ p = 1 :=
      Prod.ext (by simpa using hpow e₁ h₁) (by simpa using hpow e₂ h₂)
    have h2 : c (⟨y, hyX⟩ ^ p) = c 1 := by
      rw [map_pow, ← he, ← map_pow, hp1, map_one, map_one]
    exact congrArg Subtype.val (hc h2)
  · rw [Subgroup.card_map_of_injective X.subtype_injective,
      ← Subgroup.card_map_of_injective hc, hE₁, Subgroup.card_map_of_injective hφ,
      Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Nat.card_zpowers, hζ, sq]

theorem cartan_inf_sectionCentralizer (hS : SecD.NatSetting11 G T L I n)
    (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) {V₁ X : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hX : IsCartanX T L X) :
    X ⊓ Subgroup.centralizer (V₁ : Set G) ⊓
      sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁)) = ⊥ := by
  have := isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  have hXV : X ≤ Subgroup.normalizer (fsuV T I : Set G) := fun x hx => hS.le_normalizer (hX.1 hx).1
  have hXA : X ≤ Subgroup.normalizer (LOf L V₁ : Set G) := by
    refine le_trans ?_ (normalizer_le_normalizer_perfectCore _)
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hX.1 hx).1,
      Subgroup.le_normalizer (cartan_le_normalizer_Vi hS (Or.inl rfl) hV₁ hX hx)⟩
  have hpt :
      CartanPoint (autOn L (fsuV T I)) ⊥ (V₁.subgroupOf (fsuV T I)) (autOn X (fsuV T I)) := by
    rcases hk with hk | hk
    · obtain ⟨K, _, _, hK, π, hπ⟩ := exists_realizes_sl3 hS hk
      exact factCartanPointSL3_holds K n hn hK _ (sq_eq_one hS) _ _ π hπ _ (isSylowTwoOf_P hS) _
        (isFlagW_of_isVi hS hV₁) _ (isHall_autOn_cartan hS hX)
    · obtain ⟨K, _, _, hK, π, hπ⟩ := exists_realizes_sp4 hS hk
      exact factCartanPointSp4_holds K n hn hK _ (sq_eq_one hS) _ _ π hπ _ (isSylowTwoOf_P hS) _
        (isFlagW_of_isVi hS hV₁) _ (isHall_autOn_cartan hS hX)
  have hcent := autOn_xOne hS.le_normalizer hV₁V hXA (isPGroup_inf_centralizer hS)
  rw [eq_bot_iff]
  rintro y ⟨⟨hyX, hyC⟩, hyS⟩
  have hyV := hXV hyX
  have hd : conjV (fsuV T I) y hyV ∈
      centW (autOn X (fsuV T I)) (gammaW (autOn L (fsuV T I)) (V₁.subgroupOf (fsuV T I))) := by
    rw [← hcent]
    exact conjV_mem_autOn (L := xOne X (LOf L V₁)) (Subgroup.mem_inf.mpr ⟨hyX, hyS⟩) hyV
  have h1 := hpt _ hd fun u hu => by
    have hu' : (u : G) ∈ V₁ := hu
    have e : conjV (fsuV T I) y hyV u = u := by
      apply Subtype.ext
      rw [conjV_apply_coe, ← Subgroup.mem_centralizer_iff.mp hyC _ hu', mul_inv_cancel_right]
    rw [e, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hyc : y ∈ X ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    refine ⟨hyX, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h2 : y * v * y⁻¹ = v := by
      have := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) h1
      simpa [conjV_apply_coe] using this
    calc v * y = y * v * y⁻¹ * y := by rw [h2]
      _ = y * v := by group
  rw [cartan_inf_centralizer hS hX] at hyc
  exact hyc

theorem _root_.CFSG.Quasithin.Vol2.Ch11.SecD.cartanFact_holds : SecD.CartanFact := by
  intro G _ _ T L I n V₁ X hS hk hV₁ hX
  have := isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  refine ⟨cartan_inf_sectionCentralizer hS hk hV₁ hX, fun p hp hpq => ?_⟩
  have hXV : X ≤ Subgroup.normalizer (fsuV T I : Set G) := fun x hx => hS.le_normalizer (hX.1 hx).1
  have hD := isHall_autOn_cartan hS hX
  rcases hk with hk | hk
  · obtain ⟨K, _, _, hK, π, f, -, hf⟩ := exists_coord_sl3 hS hk
    have : CharP K 2 := charP_two_of_card (by omega) hK
    have hpK : p ∣ Nat.card Kˣ := by rwa [Nat.card_units, hK]
    obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf (isSylowTwoOf_P hS)
    rw [eq_map_psiW_of_sylow hg, inf_normalizer_eq hf g] at hD
    obtain ⟨x, -, hDx⟩ := exists_eq_map_torus3 hf g hD
    refine exists_elemAbelian_of_range hXV (cartan_inf_centralizer hS hX)
      ((psiW π (g * x)).comp tSL) ((psiW_injective hf (g * x)).comp tSL_injective) ?_ hp hpK
    rw [hDx, MonoidHom.range_comp]
  · obtain ⟨K, _, _, hK, π, f, -, hf⟩ := exists_coord_sp4 hS hk
    have : CharP K 2 := charP_two_of_card (by omega) hK
    have hpK : p ∣ Nat.card Kˣ := by rwa [Nat.card_units, hK]
    obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf (isSylowTwoOf_P hS)
    rw [eq_map_psiSp_of_sylow hg, inf_normalizer_eq_sp hf g] at hD
    obtain ⟨x, -, hDx⟩ := exists_eq_map_torus_sp hf g hD
    refine exists_elemAbelian_of_range hXV (cartan_inf_centralizer hS hX)
      (((psiSp π (g * x)).comp torusHom).comp (pairHom K))
      (((psiSp_injective hf (g * x)).comp torusHom_injective).comp (pairHom_bijective K).1) ?_ hp
      hpK
    rw [hDx, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (pairHom_bijective K).2,
      ← MonoidHom.range_eq_map, torus, MonoidHom.range_comp]

end CFSG.Quasithin.Vol2.Ch11.SecO1
