module

public import CFSG.Quasithin.EmptyFaithful.SzN8Decomp
public import CFSG.Quasithin.EmptyFaithful.SzN8Rank
public import CFSG.Quasithin.EmptyFaithful.SzN8A5
public import CFSG.Quasithin.EmptyFaithful.SzN7Setup
public import CFSG.Quasithin.EmptyFaithful.S153F17
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCZ

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.LocalAnalysis.ComponentInitial

section Generic

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

omit [Finite G] in
theorem szN8_oTwoUpper_idem (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) ?_
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hx.1 hx.2) hx.2

theorem szN8_ctx_decomp (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (ctx : Ctx15316 T Mc M V₁ V₂ Yp I L t)
    (hrank : ∀ E : Subgroup G, E ≤ L → IsPGroup 3 E → (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 3)
    (hZ : ∀ x ∈ L, (∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 L) → x ∈ pCoreOf 2 L)
    (hinner : ∀ y ∈ Yp, Odd (orderOf y) →
      ∃ x ∈ L, ∀ l ∈ L, l * (x⁻¹ * y) * l⁻¹ * (x⁻¹ * y)⁻¹ ∈ pCoreOf 2 L) :
    Yp = YL153 Yp L ⊔ YC153 Yp L ∧ IsElemAbelianOfRank 3 2 (OTwoQuot Yp) := by
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := ctx.ctx.hyp
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ ctx.conc.1
  have hYN : Yp ≤ Subgroup.normalizer (L : Set G) :=
    S153D.Yp_le_normalizer h37 h38 hh ctx.ctx.inH hLI
  have hY2 : oTwoUpper Yp = Yp := by
    rcases hh.cases with hY | ⟨-, hY⟩
    · rw [hY]
      exact szN8_oTwoUpper_idem _
    · rw [hY]
      exact szN8_oTwoUpper_idem _
  exact szN8_decomp hYN hY2 ctx.facts.struct_Yp ctx.c16.YL_ne hrank hZ hinner

end Generic

section Lin2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem szN8_lin2_hZ {L : Subgroup G} {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type L n) :
    ∀ x ∈ L, (∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 L) → x ∈ pCoreOf 2 L := by
  obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, -⟩ := hlin
  have hnat : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hnat
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  intro x hx hc
  have hx1 : α ⟨x, hx⟩ = 1 := by
    refine szN4_sl2_center_trivial h2 _ fun B => ?_
    obtain ⟨l, rfl⟩ := hαs B
    have hcl : (l * ⟨x, hx⟩ * l⁻¹ * ⟨x, hx⟩⁻¹ : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (szN4_mem_pCore_iff _).mpr (hc l l.2)
    rw [← hαk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hcl
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hcl)).symm
  have : (⟨x, hx⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← hαk]
    exact MonoidHom.mem_ker.mpr hx1
  exact (szN4_mem_pCore_iff _).mp this

theorem szN8_lin2_hrank (k17L : ThreeRankBlocks) {L : Subgroup G} {n : ℕ} (hlin : IsLin2Type L n) :
    ∀ E : Subgroup G, E ≤ L → IsPGroup 3 E → (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 3 := by
  intro E hEL hE3 hEe
  have hr : CFSG.Open.pRank 3 L = 1 := by
    refine (k17L G L).1 ?_
    obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, -⟩ := hlin
    exact ⟨n, F, hF, hFin, hcard, ⟨(QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)⟩⟩
  exact szN8_card_le_three_of_pRank hEL hE3 hEe hr

@[expose] def Lin2YInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
      ∀ y ∈ Yp, Odd (orderOf y) →
        ∃ x ∈ L, ∀ l ∈ L, l * (x⁻¹ * y) * l⁻¹ * (x⁻¹ * y)⁻¹ ∈ pCoreOf 2 L

theorem lin2SetupNoStar_of_inner (h37 : A37ForSQTK) (h38 : A38ForSQTK) (k17L : ThreeRankBlocks)
    (kI : Lin2YInner) : Lin2SetupNoStar := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hn
  obtain ⟨n, hn1, hlin⟩ := hn
  exact szN8_ctx_decomp h37 h38 c (szN8_lin2_hrank k17L hlin) (szN8_lin2_hZ hn1 hlin)
    (kI G T Mc M V₁ V₂ Yp I L t c ⟨n, hn1, hlin⟩)

end Lin2

section Alt5

variable {G : Type} [Group G] [Finite G]

theorem szN8_alt5_hrank {L : Subgroup G} (hA : IsAltType L 5) :
    ∀ E : Subgroup G, E ≤ L → IsPGroup 3 E → (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 3 := by
  obtain ⟨α, hαs, hαk, -⟩ := hA
  intro E hEL hE3 hEe
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : ↥E →* alternatingGroup (Fin 5) := α.comp (Subgroup.inclusion hEL)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : (Subgroup.inclusion hEL x : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← hαk]
      exact hx
    have h2 : ((x : G)) ∈ pCoreOf 2 L := (szN4_mem_pCore_iff _).mp h1
    exact Subgroup.mem_bot.mpr (Subtype.ext (szN8_eq_one_of_three hE3 x.2 h2))
  have hdvd : Nat.card ↥E ∣ Nat.card (alternatingGroup (Fin 5)) := Subgroup.card_dvd_of_injective f hf
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num
  rw [h60] at hdvd
  obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp hE3
  rw [hs] at hdvd ⊢
  by_contra h
  push Not at h
  have h2 : 2 ≤ s := by
    by_contra hs2
    push Not at hs2
    interval_cases s <;> simp at h
  have h9 : 3 ^ 2 ∣ 3 ^ s := pow_dvd_pow 3 h2
  have : 9 ∣ 60 := h9.trans hdvd
  omega

omit [Finite G] in
theorem szN8_alt5_hZ {L : Subgroup G} (hA : IsAltType L 5) :
    ∀ x ∈ L, (∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 L) → x ∈ pCoreOf 2 L := by
  obtain ⟨α, hαs, hαk, -⟩ := hA
  intro x hx hc
  have hx1 : α ⟨x, hx⟩ = 1 := by
    have hcen : α ⟨x, hx⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro B
      obtain ⟨l, rfl⟩ := hαs B
      have hcl : (l * ⟨x, hx⟩ * l⁻¹ * ⟨x, hx⟩⁻¹ : ↥L) ∈ CFSG.pCore 2 ↥L :=
        (szN4_mem_pCore_iff _).mpr (hc l l.2)
      rw [← hαk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hcl
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hcl)
    rw [alternatingGroup.center_eq_bot (by simp)] at hcen
    exact Subgroup.mem_bot.mp hcen
  have : (⟨x, hx⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← hαk]
    exact MonoidHom.mem_ker.mpr hx1
  exact (szN4_mem_pCore_iff _).mp this

@[expose] def A5IsShort : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsAltType L 5 → IsShort2 L

theorem a5SetupNoStar_of_short (h37 : A37ForSQTK) (h38 : A38ForSQTK) (kS : A5IsShort) :
    A5SetupNoStar := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hA
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1
  have hYN : Yp ≤ Subgroup.normalizer (L : Set G) := S153D.Yp_le_normalizer h37 h38 hh c.ctx.inH hLI
  obtain ⟨h1, h2⟩ := szN8_ctx_decomp h37 h38 c (szN8_alt5_hrank hA) (szN8_alt5_hZ hA)
    (fun y hy hyo => szN8_alt5_inner hA (hYN hy) hyo)
  exact ⟨h1, h2, CFSG.QuasithinUnique.AppC.blockZ_eq_bot_of_alt5
    (kS G T Mc M V₁ V₂ Yp I L t c hA) hA⟩

end Alt5

end CFSG.Quasithin
