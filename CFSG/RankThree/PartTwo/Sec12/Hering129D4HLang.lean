module

public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HNR
public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HTup
public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HHess

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.EvenF4QPlus CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartTwo.Sec19


theorem card_pair_eq_nine {G : Type} [Group G] {x₁ x₂ : G} (h12 : x₁ * x₂ = x₂ * x₁)
    (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hinj : ∀ v : Fin 2 → ZMod 3, Hering129KM2.pt x₁ x₂ v = 1 → v = 0) :
    Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) = 9 := by
  have hbij : Function.Bijective (Hering129KM2.ptHom h12 h1 h2) := by
    refine ⟨(injective_iff_map_eq_one _).2 fun v hv => ?_,
      Hering129KM2.ptHom_surjective h12 h1 h2⟩
    have := hinj v.toAdd (congrArg Subtype.val hv)
    exact toAdd_eq_zero.1 this
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  simp

section Frame

variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem exists_hessF_frame (P : D4Par n X σ) {L : Type} [Field L] [Algebra X L]
    [IsAlgClosure X L] [CharP L 2] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (2 ^ n)) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hqε : ((2 ^ n : ℕ) : ZMod 3) = (ε : ZMod 3)) {ζ : Lˣ}
    (hζ : orderOf ζ = 3) {g : ModGL TwistTag.D4.tag L} (hgG : g ∈ adjointGroup TwistTag.D4.tag L)
    (hFg : trialityFrob L Fr g = g * threeSixN L ε) :
    ∃ (c y : C0 σ) (F : Subgroup (C0 σ)), HessF c y F ∧
      threeSixEmb' L X σ g c = rootDiagUnit TwistTag.D4.tag (tup ζ gT) ∧
      threeSixEmb' L X σ g y = nw L wT := by
  classical
  haveI : Finite X := inferInstance
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed X
  have hζ3 : ζ ^ 3 = 1 := pow_three_of_orderOf hζ
  have hrange := range_threeSixEmb Nat.prime_two P.one_le P.card P.frob Fr hFr
  have hΦ := mem_range_threeSixEmb' (K := X) (σ := σ) hrange hgG hFg
  have hinj : Function.Injective (threeSixEmb' L X σ g) := threeSixEmb'_injective g
  have hex : ∀ u : ModGL TwistTag.D4.tag L, u ∈ adjointGroup TwistTag.D4.tag L →
      threeSixFrob L Fr ε u = u → ∃ x : C0 σ, threeSixEmb' L X σ g x = u :=
    fun u h1 h2 => (hΦ u).2 ⟨h1, h2⟩
  have hgT : gT = vecV 1 0 := by decide
  have hgT2 : gT2 = vecV 0 1 := by decide
  have hcT : rootDiagUnit TwistTag.D4.tag (tup ζ gT) ∈ threeSixTorus L Fr ε := by
    rw [hgT]
    exact mem_threeSixTorus_tup_vec hFr hε hqε hζ3 1 0
  have hbT : rootDiagUnit TwistTag.D4.tag (tup ζ gT2) ∈ threeSixTorus L Fr ε := by
    rw [hgT2]
    exact mem_threeSixTorus_tup_vec hFr hε hqε hζ3 0 1
  have hcG : rootDiagUnit TwistTag.D4.tag (tup ζ gT) ∈ torusGroup TwistTag.D4.tag L :=
    (Subgroup.mem_inf.1 hcT).1
  have hbG : rootDiagUnit TwistTag.D4.tag (tup ζ gT2) ∈ torusGroup TwistTag.D4.tag L :=
    (Subgroup.mem_inf.1 hbT).1
  obtain ⟨x₁, hx₁⟩ := hex _ (torusGroup_le_adjointGroup_D4 hcG) (Subgroup.mem_inf.1 hcT).2
  obtain ⟨x₂, hx₂⟩ := hex _ (torusGroup_le_adjointGroup_D4 hbG) (Subgroup.mem_inf.1 hbT).2
  have hfix : ∀ ω : List (Fin TwistTag.D4.tag.rank),
      (coxeterSystem TwistTag.D4.tag).wordProd (deltaW^[threeSixExp ε] ω) =
        (coxeterSystem TwistTag.D4.tag).wordProd ω →
      ∃ x : C0 σ, threeSixEmb' L X σ g x = nw L ω := fun ω h =>
    hex _ (nw_mem_adjointGroup ω) (threeSixFrob_nw_eq Fr ε ω h)
  have hfixT : (coxeterSystem TwistTag.D4.tag).wordProd (deltaW^[threeSixExp ε] wT) =
      (coxeterSystem TwistTag.D4.tag).wordProd wT := by
    rcases hε with rfl | rfl
    · exact wordProd_deltaW_pow_four_wT
    · exact wordProd_deltaW_pow_ten_wT
  have hfixS : (coxeterSystem TwistTag.D4.tag).wordProd (deltaW^[threeSixExp ε] wS) =
      (coxeterSystem TwistTag.D4.tag).wordProd wS := by
    rcases hε with rfl | rfl
    · exact wordProd_deltaW_pow_four_wS
    · exact wordProd_deltaW_pow_ten_wS
  obtain ⟨n₁, hn₁⟩ := hfix wS hfixS
  obtain ⟨t, ht⟩ := hfix wT hfixT
  set cE := rootDiagUnit TwistTag.D4.tag (tup ζ gT) with hcE
  set bE := rootDiagUnit TwistTag.D4.tag (tup ζ gT2) with hbE
  have h12 : x₁ * x₂ = x₂ * x₁ := hinj (by
    rw [map_mul, map_mul, hx₁, hx₂]
    exact CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.torusGroup_mul_comm hcG hbG)
  have h1 : x₁ ^ 3 = 1 := hinj (by
    rw [map_pow, hx₁, map_one, hcE, ← rootDiagUnit_pow', tup_pow_three hζ3, rootDiagUnit_one])
  have h2 : x₂ ^ 3 = 1 := hinj (by
    rw [map_pow, hx₂, map_one, hbE, ← rootDiagUnit_pow', tup_pow_three hζ3, rootDiagUnit_one])
  have hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹ := hinj (by
    rw [map_mul, map_mul, map_inv, map_inv, hn₁, hx₁, hx₂, hcE, hbE,
      nw_conj_rootDiagUnit hζ3, wordExp_wS_gT]
    exact rootDiagUnit_tup_neg hζ3 gT2)
  have hF2 : n₁ * x₂ * n₁⁻¹ = x₁ := hinj (by
    rw [map_mul, map_mul, map_inv, hn₁, hx₁, hx₂, hbE, hcE, nw_conj_rootDiagUnit hζ3,
      wordExp_wS_gT2])
  have ht1 : t * x₁ * t⁻¹ = x₁ := hinj (by
    rw [map_mul, map_mul, map_inv, ht, hx₁, hcE, nw_conj_rootDiagUnit hζ3, wordExp_wT_gT])
  have ht2 : t * x₂ * t⁻¹ = x₂ * x₁ := hinj (by
    rw [map_mul, map_mul, map_mul, map_inv, ht, hx₁, hx₂, hbE, hcE, nw_conj_rootDiagUnit hζ3,
      wordExp_wT_gT2]
    exact rootDiagUnit_tup_add hζ3 gT2 gT)
  have hcard : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup (C0 σ)) = 9 := by
    refine card_pair_eq_nine h12 h1 h2 fun v hv => ?_
    have hv' : cE ^ (((v 0).val : ℕ) : ℤ) * bE ^ (((v 1).val : ℕ) : ℤ) = 1 := by
      have := congrArg (threeSixEmb' L X σ g) hv
      rw [Hering129KM2.pt, map_mul, map_zpow, map_zpow, hx₁, hx₂, map_one] at this
      exact this
    rw [zpow_natCast, zpow_natCast, hcE, hbE, rootDiagUnit_tup_pow hζ3, rootDiagUnit_tup_pow hζ3,
      ← rootDiagUnit_tup_add hζ3, ← rootDiagUnit_one (τ := TwistTag.D4.tag),
      ← tup_zero_eq (ζ := ζ)] at hv'
    have h0 := tup_injective hζ (rootDiagUnit_injective hv')
    have key : ∀ a b : ZMod 3, a.val • gT + b.val • gT2 = 0 → a = 0 ∧ b = 0 := by
      decide
    obtain ⟨ha, hb⟩ := key (v 0) (v 1) h0
    funext i
    fin_cases i
    · exact ha
    · exact hb
  have hNR : ∀ m ∈ Subgroup.normalizer
      ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup (C0 σ)) : Set (C0 σ)),
      m * x₁ * m⁻¹ = x₁ → m * x₂ * m⁻¹ = x₂⁻¹ → False := by
    intro m _ hm1 hm2
    have hmG : threeSixEmb' L X σ g m ∈ adjointGroup TwistTag.D4.tag L :=
      ((hΦ _).1 ⟨m, rfl⟩).1
    refine noRefl_alg hζ hmG ?_ ?_
    · have := congrArg (threeSixEmb' L X σ g) hm1
      rwa [map_mul, map_mul, map_inv, hx₁] at this
    · have := congrArg (threeSixEmb' L X σ g) hm2
      rwa [map_mul, map_mul, map_inv, map_inv, hx₂] at this
  exact ⟨x₁, t, _, hessF_of_noRefl h12 h1 h2 hcard hF1 hF2 ht1 ht2 hNR, hx₁, ht⟩

end Frame

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
