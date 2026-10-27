module

public import CFSG.LocalAnalysis.StandardType.GGHalfBlockTorus
public import CFSG.Adapters.StatedSLTwoField
public import CFSG.RankThree.PartOne.TAIL.LSideOutAut
public import CFSG.CharacterTheory.Semidihedral.SemilinearOuterQuotient
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.TAIL.KSideCen

public section

namespace CFSG.StandardType.GGHalf

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix
open CFSG.RankThree.PartOne.TAIL

theorem exists_slLift_two {G : Type} [Group G] {H : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (hH : commutator H = ⊤)
    (hmod : StatedClassicalModel (H ⧸ Subgroup.center H) .PSL (m + 1 + 1 + 1) 2 1) :
    ∃ φ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G, φ.range = H ∧
      Function.Injective φ := by
  obtain ⟨θ⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hmod
  let π : ↥H →* SpecialLinearGroup (Fin (m + 1 + 1 + 1)) (ZMod 2) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥H))
  have hπ : Function.Surjective π := fun g => by
    obtain ⟨q, hq⟩ := θ.surjective g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨h, hq⟩
  have hker : ∀ h, π h = 1 → h ∈ Subgroup.center ↥H := fun h hh => by
    have h1 : θ (QuotientGroup.mk h) = 1 := hh
    have h2 := θ.injective (h1.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff _).mp h2
  obtain ⟨σ, hσ⟩ := CFSG.StandardType.TypeA.slHasSections_of_five_le
    (d := m + 1 + 1 + 1) (K := ZMod 2) (by omega) ↥H π hπ (fun h hh => hker h hh)
  let φ₀ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) (ZMod 2) →* G := H.subtype.comp σ
  have hinj₀ : Function.Injective φ₀ := by
    intro a b hab
    have hab' : σ a = σ b := Subtype.ext hab
    calc a = π (σ a) := (hσ a).symm
      _ = π (σ b) := by rw [hab']
      _ = b := hσ b
  have hdecomp : ∀ l : ↥H, (σ (π l))⁻¹ * l ∈ Subgroup.center ↥H := fun l => hker _ (by
    rw [map_mul, map_inv, hσ, inv_mul_cancel])
  have hrange : φ₀.range = H := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      exact (σ g).2
    · have hle : commutator ↥H ≤ σ.range := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        have ea : a = σ (π a) * ((σ (π a))⁻¹ * a) := by group
        have eb : b = σ (π b) * ((σ (π b))⁻¹ * b) := by group
        rw [ea, eb, commutatorElement_mul_mem_center (hdecomp a) (hdecomp b),
          ← map_commutatorElement]
        exact ⟨_, rfl⟩
      intro l hl
      have hmem : (⟨l, hl⟩ : ↥H) ∈ σ.range := hle (hH ▸ Subgroup.mem_top _)
      obtain ⟨g, hg⟩ := hmem
      exact ⟨g, congrArg Subtype.val hg⟩
  have : Fintype F2 := Fintype.ofFinite _
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  let ε : F2 ≃+* ZMod 2 :=
    FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hcard, ZMod.card])
  let μ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →*
      SpecialLinearGroup (Fin (m + 1 + 1 + 1)) (ZMod 2) := SpecialLinearGroup.map ε.toRingHom
  let μ' : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) (ZMod 2) →*
      SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := SpecialLinearGroup.map ε.symm.toRingHom
  have hμμ' : ∀ g, μ (μ' g) = g := by
    intro g
    ext i j
    simp [μ, μ']
  have hμ'μ : ∀ g, μ' (μ g) = g := by
    intro g
    ext i j
    simp [μ, μ']
  refine ⟨φ₀.comp μ, ?_, ?_⟩
  · have hsurj : Function.Surjective μ := fun g => ⟨μ' g, hμμ' g⟩
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, ← MonoidHom.range_eq_map]
    exact hrange
  · intro a b hab
    have h1 := hinj₀ hab
    calc a = μ' (μ a) := (hμ'μ a).symm
      _ = μ' (μ b) := by rw [h1]
      _ = b := hμ'μ b

theorem aut_sl_gf2 {d : ℕ} (hd : 3 ≤ d) (β : MulAut (SpecialLinearGroup (Fin d) F2)) :
    ∃ (g : SpecialLinearGroup (Fin d) F2) (ε : ℕ), ε ≤ 1 ∧
      β = MulAut.conj g *
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut d F2 ^ ε := by
  obtain ⟨A, σ, ε, hε, hβ⟩ := CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl hd β
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  have hg : Nat.gcd d (Nat.card F2 - 1) = 1 := by
    rw [hcard]
    simp
  obtain ⟨g, hgA⟩ := slConjugation_mem_inn hg A
  have h01 : ∀ z : F2, z = 0 ∨ z = 1 := by
    intro z
    by_cases hz : z = 0
    · exact Or.inl hz
    · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
      exact Or.inr ((huniq z hz).trans (huniq 1 one_ne_zero).symm)
  have hσ : σ = RingEquiv.refl F2 := by
    apply RingEquiv.ext
    intro z
    rcases h01 z with rfl | rfl
    · simp
    · simp
  refine ⟨g, ε, hε, ?_⟩
  rw [hβ, hσ, ← hgA]
  have h1 : CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin d) F2
      (RingEquiv.refl F2) = 1 :=
    map_one (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin d) F2)
  rw [h1, mul_one]

theorem sup_centralizer_of_odd_order {G : Type} [Group G] {L : Subgroup G} {d : ℕ} (hd : 3 ≤ d)
    (e : ↥L ≃* SpecialLinearGroup (Fin d) F2) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hodd : Odd (orderOf x)) :
    x ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  rw [mem_sup_centralizer_iff hx, mem_innK_congr e]
  set ρ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hx⟩ with hρ
  set α : MulAut (SpecialLinearGroup (Fin d) F2) := MulAut.congr e ρ with hα
  have hρk : ρ ^ (orderOf x) = 1 := by
    rw [hρ, ← map_pow]
    have : (⟨x, hx⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ orderOf x = 1 := by
      apply Subtype.ext
      simp
    rw [this, map_one]
  have hαk : α ^ (orderOf x) = 1 := by
    rw [hα, ← map_pow, hρk, map_one]
  obtain ⟨g, ε, hε, hαg⟩ := aut_sl_gf2 hd α
  set δ : MulAut (SpecialLinearGroup (Fin d) F2) :=
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut d F2 with hδ
  have hδ2 : δ * δ = 1 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.slGraph_mul_slGraph
  let q : MulAut (SpecialLinearGroup (Fin d) F2) →*
      MulAut (SpecialLinearGroup (Fin d) F2) ⧸ innK (SpecialLinearGroup (Fin d) F2) :=
    QuotientGroup.mk' _
  have hqg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
  have hq2 : q δ ^ 2 = 1 := by
    rw [← map_pow, pow_two, hδ2, map_one]
  have hqα : q α = q δ ^ ε := by
    rw [hαg, map_mul, hqg, one_mul, map_pow]
  have hqk : q α ^ (orderOf x) = 1 := by rw [← map_pow, hαk, map_one]
  obtain ⟨j, hj⟩ := hodd
  have hq1 : q α = 1 := by
    interval_cases ε
    · rw [hqα, pow_zero]
    · rw [hqα, pow_one] at hqk ⊢
      rw [hj, pow_succ, pow_mul, hq2, one_pow, one_mul] at hqk
      exact hqk
  exact (QuotientGroup.eq_one_iff _).1 hq1

end CFSG.StandardType.GGHalf

end
