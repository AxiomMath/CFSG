module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylB
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.CentralExt

section Lift

variable {n : ℕ} {K : Type} [Field K] {L : Type} [Group L]

theorem exists_spLift_of_mulEquiv [Finite K] [Finite L]
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSp n K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ σ : StatedSp n K →* E, ∀ g, π (σ g) = g)
    (hL : commutator L = ⊤) (θ : L ⧸ Subgroup.center L ≃* StatedProj (StatedSp n K)) :
    ∃ φ : StatedSp n K →* L, Function.Surjective φ ∧
      ∀ g, θ (QuotientGroup.mk (φ g)) = QuotientGroup.mk g := by
  obtain ⟨E, hE⟩ : ∃ E : Subgroup (L × StatedSp n K),
      E = MonoidHom.eqLocus
        ((θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).comp (MonoidHom.fst _ _))
        ((QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K))).comp
          (MonoidHom.snd _ _)) := ⟨_, rfl⟩
  have hmem : ∀ e : L × StatedSp n K,
      e ∈ E ↔ θ (QuotientGroup.mk e.1) = QuotientGroup.mk e.2 := by
    intro e
    rw [hE]
    rfl
  let π : E →* StatedSp n K := (MonoidHom.snd _ _).comp E.subtype
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (θ.symm (QuotientGroup.mk g))
    refine ⟨⟨(l, g), (hmem _).mpr ?_⟩, rfl⟩
    change θ (QuotientGroup.mk l) = QuotientGroup.mk g
    rw [hl, MulEquiv.apply_symm_apply]
  have hcen : π.ker ≤ Subgroup.center E := by
    intro e he
    have h2 : (e : L × StatedSp n K).2 = 1 := he
    have h1 : (e : L × StatedSp n K).1 ∈ Subgroup.center L := by
      have h := (hmem _).mp e.2
      rw [h2, QuotientGroup.mk_one, ← map_one θ] at h
      exact (QuotientGroup.eq_one_iff _).mp (θ.injective h)
    rw [Subgroup.mem_center_iff]
    intro e'
    apply Subtype.ext
    apply Prod.ext
    · exact (Subgroup.mem_center_iff.mp h1 _)
    · change (e' : L × StatedSp n K).2 * (e : L × StatedSp n K).2 =
        (e : L × StatedSp n K).2 * (e' : L × StatedSp n K).2
      rw [h2, one_mul, mul_one]
  obtain ⟨σ, hσ⟩ := hsplit E π hπ hcen
  let φ : StatedSp n K →* L := (MonoidHom.fst _ _).comp (E.subtype.comp σ)
  have hφθ : ∀ g, θ (QuotientGroup.mk (φ g)) = QuotientGroup.mk g := by
    intro g
    have h := (hmem _).mp (σ g).2
    have h' : ((σ g : E) : L × StatedSp n K).2 = g := hσ g
    rw [h'] at h
    exact h
  have hdecomp : ∀ l : L, ∃ g, (φ g)⁻¹ * l ∈ Subgroup.center L := by
    intro l
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (θ (QuotientGroup.mk l))
    refine ⟨g, (QuotientGroup.eq (s := Subgroup.center L)).mp (θ.injective ?_)⟩
    rw [hφθ, hg]
  refine ⟨φ, ?_, hφθ⟩
  have hle : commutator L ≤ φ.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨g₁, hg₁⟩ := hdecomp a
    obtain ⟨g₂, hg₂⟩ := hdecomp b
    have ea : a = φ g₁ * ((φ g₁)⁻¹ * a) := by group
    have eb : b = φ g₂ * ((φ g₂)⁻¹ * b) := by group
    rw [ea, eb, commutatorElement_mul_mem_center hg₁ hg₂, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  intro l
  exact (hle (hL ▸ Subgroup.mem_top l) : l ∈ φ.range)

theorem injective_of_spLift (hZ : (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) = ⊥)
    (θ : L ⧸ Subgroup.center L ≃* StatedProj (StatedSp n K)) {φ : StatedSp n K →* L}
    (hφθ : ∀ g, θ (QuotientGroup.mk (φ g)) = QuotientGroup.mk g) : Function.Injective φ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := hφθ g
  rw [hg, QuotientGroup.mk_one, map_one] at h
  have hg' : g ∈ (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) :=
    (QuotientGroup.eq_one_iff _).mp h.symm
  rw [hZ] at hg'
  exact hg'

end Lift

section Even

theorem statedScalars_subgroupOf_statedSp_eq_bot_of_card {n f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hn : 1 ≤ n) :
    (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  rw [CFSG.LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd K hn, hK]
  have hodd : Odd (2 ^ f - 1) := by
    have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    exact Nat.Even.sub_odd this (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  exact Nat.coprime_two_left.2 hodd


theorem sp_exists_section_even {n f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hn : 4 ≤ n) (E : Type) [Group E] [Finite E]
    (π : E →* StatedSp n K) (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : StatedSp n K →* E, ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf hK
  set Z := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars n K
  have hZc : Z ≤ Subgroup.center (StatedSp n K) :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center
  have : Group.IsPerfect (StatedSp n K) := SpClosed.isPerfect_statedSp' (by
    rcases Nat.lt_or_ge f 2 with h | h
    · right
      refine ⟨by rw [hK]; interval_cases f; rfl, by omega⟩
    · left
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h)
  exact CoverAssembly.exists_section_of_cover_and_coprime (p := 2)
    (θ := QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact hZc)
    (SpClosed.psp_two_cover_trivial hK hf (by omega) fun h => absurd h (by omega))
    (fun E _ _ π hπ hcen hc => SpClosed.sp_exists_section_of_coprime E π hπ hcen hc) E π hπ hcen

theorem ggSpLiftInput_holds : GGSpLiftInput := by
  intro G _ _ L n f hn hL hmod
  obtain ⟨⟨-, hf, -⟩, K', _, _, hK', ⟨e⟩⟩ := hmod
  obtain ⟨φ₀, hφ₀, hφθ⟩ := exists_spLift_of_mulEquiv (L := L)
    (sp_exists_section_even hK' hf hn) hL e
  have hinj₀ : Function.Injective φ₀ :=
    injective_of_spLift (statedScalars_subgroupOf_statedSp_eq_bot_of_card hK' hf (by omega)) e
      hφθ
  have : Fintype K' := Fintype.ofFinite K'
  have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 f) = Fintype.card K' := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, GaloisField.card 2 f (by omega), hK']
  let ε : GaloisField 2 f ≃+* K' := FiniteField.ringEquivOfCardEq hcard
  let μ := CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.statedSpCongr ε n
  refine ⟨L.subtype.comp (φ₀.comp μ.toMonoidHom), ?_, ?_⟩
  · exact L.subtype_injective.comp (hinj₀.comp μ.injective)
  · have hsurj : Function.Surjective (φ₀.comp μ.toMonoidHom) := hφ₀.comp μ.surjective
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]

end Even

end CFSG.StandardType
