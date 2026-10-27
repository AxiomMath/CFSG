module

public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLRound
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthLTwD
public import CFSG.LocalAnalysis.StandardType.GGAssemblyElevenDefs
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix

namespace NoTvAut

theorem ggNoTransvectionTorus_of_simFrame {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) {R : Type} [Group R]
    (e : R ≃* adjointGroup τ K) {I : Set (MulAut R)}
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥)
    (hfullp : ∀ b : Fin τ.rank → Kˣ, (∀ i, b i ^ p = 1) → rootDiagUnit τ b ∈ torusGroup τ K)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p))
    (hT : ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E → p ^ τ.rank ≤ Nat.card E →
      ∃ g : adjointGroup τ K, E.map (MulAut.conj g).toMonoidHom = TableBExc.torusPow τ K p)
    (hnf : ∀ α : MulAut (adjointGroup τ K), ∃ (a : adjointGroup τ K) (σ : K ≃+* K),
      ∀ v ∈ TableBExc.torusPow τ K p, ((α ^ 2) v : ModGL τ K) =
        (a : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (v : ModGL τ K) *
          (a : ModGL τ K)⁻¹) :
    GGNoTransvectionTorus p τ.rank R I := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  intro Eh hEhI hEhA hr _ a htv
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  set χ : adjointGroup τ K →* MulAut R :=
    (MulAut.conj : R →* MulAut R).comp e.symm.toMonoidHom with hχdef
  have hχ : Function.Injective χ := (OrthRest.conj_injective hZ).comp e.symm.injective
  have hχapp : ∀ x, χ x = MulAut.conj (e.symm x) := fun x => rfl
  have hEhR : Eh ≤ χ.range := by
    intro φ hφ
    obtain ⟨y, hy⟩ := hI φ (hEhI hφ) (hEhA.2 φ hφ)
    exact ⟨e y, by rw [hχapp, MulEquiv.symm_apply_apply, hy]⟩
  obtain ⟨c, hc⟩ := hT (Eh.comap χ) (ExcFrames.isElemAbelian_comap_frame χ hχ hEhA)
    (by rw [ExcFrames.card_comap_of_le_range χ hχ hEhR]; exact hr)
  have hBs : ∀ b, b ∈ Eh ↔ ∃ v ∈ TableBExc.torusPow τ K p, b = χ (c⁻¹ * v * c) := by
    intro b
    constructor
    · intro hb
      obtain ⟨x, rfl⟩ := hEhR hb
      refine ⟨c * x * c⁻¹, ?_, by rw [show c⁻¹ * (c * x * c⁻¹) * c = x by group]⟩
      rw [← hc]
      exact ⟨x, hb, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      rw [← hc] at hv
      obtain ⟨x, hx, rfl⟩ := hv
      have h1 : c⁻¹ * (MulAut.conj c).toMonoidHom x * c = x := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [h1]
      exact hx
  obtain ⟨ι, hι, hιB, hact⟩ := exists_simFrame hfullp hdet hζo χ hχ c hBs hnf
  have hNχ : (a : MulAut R) ∈ Subgroup.normalizer (χ.range : Set (MulAut R)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨e ((a : MulAut R) (e.symm x)), ?_⟩
      simp only [hχapp, MulEquiv.symm_apply_apply]
      exact (TableBOrth.mulAut_mul_conj_mul_inv _ _).symm
    · rintro ⟨x, hx⟩
      refine ⟨e ((a : MulAut R)⁻¹ (e.symm x)), ?_⟩
      have h1 : MulAut.conj (e.symm x) = (a : MulAut R) * h * (a : MulAut R)⁻¹ := by
        rw [← hχapp]
        exact hx
      simp only [hχapp, MulEquiv.symm_apply_apply]
      rw [← TableBOrth.mulAut_mul_conj_mul_inv, h1]
      group
  obtain ⟨w, m, hwm⟩ := hact (a : MulAut R) hNχ a.2
  have htv2 : GGIsTransvection p (Eh.normalizerMonoidHom (a ^ 2)) := by
    rw [map_pow]
    exact ggIsTransvection_pow_two hp hp2 hEhA htv
  set T : (Fin τ.rank → ZMod p) →+ (Fin τ.rank → ZMod p) :=
    AddMonoidHom.mk' (fun s => TableBExc.torusAct τ p w (m • s))
      (fun s s' => by rw [smul_add, torusAct_add]) with hTdef
  have hTapp : ∀ s, T s = TableBExc.torusAct τ p w (m • s) := fun s => rfl
  obtain ⟨hfix, hN⟩ := transvection_coords (t := T) hι hιB (fun b s hb => by
      show (a : MulAut R) ^ 2 * b * ((a : MulAut R) ^ 2)⁻¹ = ι (Multiplicative.ofAdd (T s))
      rw [hb, hwm s, hTapp]) htv2
  have hdet' : (cartanMod τ p).det ≠ 0 := by
    rw [det_cartanMod]
    exact hdet.ne_zero
  refine false_of_isTransvection_similitude hp2 cartanMod_transpose hdet' T ((m : ZMod p) ^ 2)
    (fun x y => ?_) hfix hN
  have hx : T x = m • TableBExc.torusAct τ p w x := by
    rw [hTapp, ← torusActHom_apply, map_nsmul, torusActHom_apply]
  have hy : T y = m • TableBExc.torusAct τ p w y := by
    rw [hTapp, ← torusActHom_apply, map_nsmul, torusActHom_apply]
  rw [hx, hy, mulVec_smul, smul_dotProduct, dotProduct_smul, torusAct_form, nsmul_eq_mul,
    nsmul_eq_mul]
  ring

theorem hnf_E7E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (p : ℕ) (α : MulAut (adjointGroup τ K)) :
    ∃ (a : adjointGroup τ K) (σ : K ≃+* K), ∀ v ∈ TableBExc.torusPow τ K p,
      ((α ^ 2) v : ModGL τ K) =
        (a : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (v : ModGL τ K) *
          (a : ModGL τ K)⁻¹ := by
  obtain ⟨hnf, -⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hnf (α ^ 2)
  exact ⟨g, σ, fun v _ => hgσ v⟩

theorem hnf_F4 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) (p : ℕ)
    (α : MulAut (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag K)) :
    ∃ (a : adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag K) (σ : K ≃+* K),
      ∀ v ∈ TableBExc.torusPow CFSG.LieType.Ree.ReeTag.F4.tag K p,
        ((α ^ 2) v : ModGL CFSG.LieType.Ree.ReeTag.F4.tag K) =
          (a : ModGL CFSG.LieType.Ree.ReeTag.F4.tag K) *
            Units.map (entrywiseHom σ.toRingHom) (v : ModGL CFSG.LieType.Ree.ReeTag.F4.tag K) *
              (a : ModGL CFSG.LieType.Ree.ReeTag.F4.tag K)⁻¹ := by
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  obtain ⟨-, hnf, ⟨Θ, hΘ, -, -⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g₁, k₁⟩, hgk₁, -⟩ := hnf α
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hnf (α ^ 2)
  dsimp only at hgk₁ hgk
  have h1 := hΘ _ g k hgk
  have h2 := hΘ _ g₁ k₁ hgk₁
  have h4 : (2 : ℕ) • (((k₁ : ℕ) : ZMod (2 * f))) = (((k : ℕ) : ZMod (2 * f))) :=
    Multiplicative.ofAdd.injective (by rw [ofAdd_nsmul, ← h2, ← map_pow, h1])
  have h5 : (k : ℕ) % (2 * f) = (2 * (k₁ : ℕ)) % (2 * f) := by
    rw [← ZMod.natCast_eq_natCast_iff', ← h4, nsmul_eq_mul]
    push_cast
    ring
  have hk : (k : ℕ) = 2 * ((k₁ : ℕ) % f) := by
    rw [Nat.mod_eq_of_lt k.isLt, Nat.mul_mod_mul_left] at h5
    exact h5
  refine ⟨g, ExcFrames.frobAut K ^ ((k₁ : ℕ) % f), fun v _ => ?_⟩
  rw [hgk, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, hk, finiteExceptionalAut_pow_two_mul,
    CFSG.LieType.Ree.ReeTag.coe_finiteFrobeniusAut_pow (σ := ExcFrames.frobAut K)
      ExcFrames.frobAut_apply]

theorem hnf_E6 {K : Type} [Field K] [Finite K] {p : ℕ} [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p)
    (α : MulAut (adjointGroup .E6 K)) :
    ∃ (a : adjointGroup .E6 K) (σ : K ≃+* K), ∀ v ∈ TableBExc.torusPow .E6 K p,
      ((α ^ 2) v : ModGL .E6 K) =
        (a : ModGL .E6 K) * Units.map (entrywiseHom σ.toRingHom) (v : ModGL .E6 K) *
          (a : ModGL .E6 K)⁻¹ := by
  obtain ⟨Θ, -, hΘ, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  obtain ⟨-, -, hall⟩ := ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K
  obtain ⟨g₁, b₁, σ₁, ε₁, hgε₁⟩ := hall α
  obtain ⟨g, b, σ, ε, hgε⟩ := hall (α ^ 2)
  have h1 := hΘ (α ^ 2) g b σ ε hgε
  rw [map_pow, hΘ α g₁ b₁ σ₁ ε₁ hgε₁] at h1
  have h3 : (2 : ℕ) • (((ε₁ : ℕ) : ZMod (exactE .E6))) = (((ε : ℕ) : ZMod (exactE .E6))) := by
    have h6 := congrArg Prod.snd h1
    simp only [Prod.pow_snd] at h6
    rw [← ofAdd_nsmul] at h6
    exact Multiplicative.ofAdd.injective h6
  have h5 : (ε : ℕ) % exactE .E6 = (2 * (ε₁ : ℕ)) % exactE .E6 := by
    rw [← ZMod.natCast_eq_natCast_iff', ← h3, nsmul_eq_mul]
    push_cast
    ring
  have h7 : (ε : ℕ) % 2 = (2 * (ε₁ : ℕ)) % 2 := h5
  have h8 : (ε : ℕ) < 2 := ε.isLt
  have hε : (ε : ℕ) = 0 := by omega
  refine ⟨g, σ, fun v hv => ?_⟩
  obtain ⟨m, hm⟩ := exists_units_map_eq_pow hζo σ.toRingHom
  have hσv : Units.map (entrywiseHom σ.toRingHom) (v : ModGL .E6 K) ∈ torusGroup .E6 K := by
    rw [units_map_entrywise_eq_pow σ.toRingHom hm (ExcFrames.mem_torusPow_iff_coe.mp hv)]
    exact pow_mem (ExcFrames.mem_torusPow_iff_coe.mp hv).1 m
  have hcomm := rootDiagUnit_mul_comm_of_mem_torusGroup b hσv
  rw [hgε v, hε]
  have hQ : exactQ Tag.E6 K 0 = 1 := pow_zero _
  rw [hQ, inv_one, mul_one, mul_one, mul_assoc (g : ModGL .E6 K) (rootDiagUnit .E6 b), hcomm]
  group

theorem ggNoTransvectionTorus_E7E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGNoTransvectionTorus p τ.rank (TableBExc.RecipeGroup τ K) (TableBExc.RecipeID τ K) := by
  have := Fact.mk hp
  have hinn : TableBExc.RecipeID τ K ⊆ Set.range (MulAut.conj : TableBExc.RecipeGroup τ K →*
      MulAut (TableBExc.RecipeGroup τ K)) := by
    rcases hτ with rfl | rfl
    · exact TableBExc.idImage_subset_inn_E7 K
    · exact TableBExc.idImage_subset_inn_E8 K
  exact ggNoTransvectionTorus_of_simFrame hp hp2 hpq (TableBExc.recipeEquiv τ K)
    (fun φ hφ _ => hinn hφ) (TableBExc.center_recipeGroup_eq_bot τ K)
    (fun b _ => TableBExc.full_of_E7_E8 hτ b)
    (ExcFrames.isUnit_det_symmetrizedCartan (Or.inr hτ) hp2)
    (fun E hE hc => IOneRest.ggExcToralRankInput_E7E8 hτ hp hp2 hpq E hE hc)
    (hnf_E7E8 hτ hf hK p)

theorem ggNoTransvectionTorus_F4 {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGNoTransvectionTorus p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  have := Fact.mk hp
  have hT : GGF4ToralRankInput K p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact TableBF4.ggF4ToralRankInput_three hpq
    · exact TableBF4.ggF4ToralRankInput_of_five_le hp (hp.five_le_of_ne_two_of_ne_three hp2 hp3)
        hpq
  exact ggNoTransvectionTorus_of_simFrame (τ := .F4) hp hp2 hpq (TableBF4.recipeEquiv K)
    (fun φ hφ _ => TableBF4.idImage_subset_inn K hφ) (TableBF4.center_recipeGroup_eq_bot K)
    (fun b _ => CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup b)
    (ExcFrames.isUnit_det_symmetrizedCartan (Or.inl rfl) hp2) (fun E hE hc => hT E hE hc)
    (fun α => hnf_F4 hf hK p α)

theorem det_symmetrizedCartan_E6 : Tag.E6.symmetrizedCartan.det = 3 := by
  rw [Tag.symmetrizedCartan, Matrix.det_mul, det_cartan_E6]
  change (1 : Matrix (Fin 6) (Fin 6) ℤ).det * 3 = 3
  rw [Matrix.det_one, one_mul]

theorem ggNoTransvectionTorus_E6 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1) :
    GGNoTransvectionTorus p 6 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hdet : IsUnit ((Tag.E6.symmetrizedCartan.det : ℤ) : ZMod p) := by
    rw [det_symmetrizedCartan_E6, isUnit_iff_ne_zero, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have h' : p ∣ 3 := by exact_mod_cast h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')
  exact ggNoTransvectionTorus_of_simFrame (τ := .E6) hp hp2 hpq (TableBExc.recipeEquiv .E6 K)
    (fun φ hφ hφp => mem_range_conj_of_mem_recipeID_E6 hp hp3 hφ hφp)
    (TableBExc.center_recipeGroup_eq_bot .E6 K) (fun b hb => TableBExc.fullp_E6 hp.one_lt hcop b hb)
    hdet (fun E hE hc => TableBExc.ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq E hE hc)
    (fun α => hnf_E6 hζo α)

end NoTvAut

open NoTvAut

section Drop

theorem ggExcSplitNoTransvectionInput_holds : GGExcSplitNoTransvectionInput := by
  intro K _ _ n p hK hp hpn
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have h1 := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨fun hp3 => ggNoTransvectionTorus_E6 hp hp2 hp3 hpq,
    ggNoTransvectionTorus_E7E8 (Or.inl rfl) hn hK hp hp2 hpq,
    ggNoTransvectionTorus_E7E8 (Or.inr rfl) hn hK hp hp2 hpq,
    ggNoTransvectionTorus_F4 hn hK hp hp2 hpq⟩

theorem ggLTransvectionCenterInputOn_rest3_of_tvRound12
    (h : GGLTransvectionCenterInputOn GGCorFourTwoOpenTvRound12Label) :
    GGLTransvectionCenterInputOn GGCorFourTwoOpenTvRest3Label :=
  ggLTransvectionCenterInputOn_rest3_of_round12 ggExcSplitNoTransvectionInput_holds h

end Drop

end CFSG.StandardType

end
