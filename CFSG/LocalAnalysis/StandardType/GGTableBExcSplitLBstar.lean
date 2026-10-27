module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLVac
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesFix
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace ExcSplitL

section Borel

variable {τ : Tag} {K : Type} [Field K]

theorem rootChar_mulSingle (j : Fin τ.rank) (ζ : Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (Pi.mulSingle j ζ) v = ζ ^ v j := by
  classical
  rw [rootChar, Finset.prod_eq_single j]
  · rw [Pi.mulSingle_eq_same]
  · intro i _ hij
    rw [Pi.mulSingle_eq_of_ne hij, one_zpow]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem rootDiagUnit_pow' {τ : Tag} {K : Type} [Field K] (b : Fin τ.rank → Kˣ) (n : ℕ) :
    rootDiagUnit τ b ^ n = rootDiagUnit τ (b ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ n ih => rw [pow_succ, ih, ← rootDiagUnit_mul, ← pow_succ]

theorem eq_one_of_mem_rootCharStabilizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Kˣ}
    (hζo : orderOf ζ = p) {w : WeylGroup τ}
    (hw : ∀ j, w ∈ rootCharStabilizer (Pi.mulSingle j ζ)) : w = 1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine NoOffExc.eq_one_of_torusAct hp2 fun x => ?_
  have hred : TableBExc.redMod τ p (w • TableBExc.liftMod τ p x) =
      TableBExc.redMod τ p (TableBExc.liftMod τ p x) := by
    funext j
    have h1 := hw j (TableBExc.liftMod τ p x)
    rw [rootChar_mulSingle, rootChar_mulSingle] at h1
    have h2 := zpow_eq_zpow_iff_modEq.mp h1
    rw [hζo] at h2
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr h2
  rw [TableBExc.torusAct, hred, TableBExc.redMod_liftMod]


theorem exists_eq_mul_of_commute_mulSingle {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Kˣ}
    (hζo : orderOf ζ = p) {z : ModGL τ K} (hzC : z ∈ adjointGroup τ K)
    (hz : ∀ j, rootDiagUnit τ (Pi.mulSingle j ζ) * z * (rootDiagUnit τ (Pi.mulSingle j ζ))⁻¹ = z) :
    ∃ h ∈ torusGroup τ K, ∃ u ∈ posUnipotent τ K, z = h * u := by
  obtain ⟨hX, huniq, -, -⟩ := Chevalley_toral_centralizer_Bruhat_factors τ K 1
  have hz1 : z ∈ toralCentralizer τ K 1 :=
    mem_toralCentralizer.2 ⟨hzC, by rw [rootDiagUnit_one, one_mul, inv_one, mul_one]⟩
  obtain ⟨w, -, h, hh, u, hu, v, hv, hzeq⟩ := hX z hz1
  have huU : u ∈ posUnipotent τ K := rootSpan_le_posUnipotent (fun α hα => hα.2) hu
  have hvI : v ∈ rootSpan τ K (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have hw1 : w = 1 := by
    refine eq_one_of_mem_rootCharStabilizer hp2 hζo fun j => ?_
    obtain ⟨hXj, -, -, -⟩ := Chevalley_toral_centralizer_Bruhat_factors τ K (Pi.mulSingle j ζ)
    obtain ⟨wj, hwj, hj, hhj, uj, huj, vj, hvj, hzj⟩ :=
      hXj z (mem_toralCentralizer.2 ⟨hzC, hz j⟩)
    have hujU : uj ∈ posUnipotent τ K := rootSpan_le_posUnipotent (fun α hα => hα.2) huj
    have hvjI : vj ∈ rootSpan τ K (inversionSet wj) := rootSpan_mono Set.inter_subset_right hvj
    obtain ⟨hww, -, -, -⟩ :=
      huniq w wj h hj u uj v vj hh hhj huU hujU hvI hvjI (hzeq.symm.trans hzj)
    exact hww ▸ hwj
  subst hw1
  have hv1 : v = 1 := by
    rw [inversionSet_one] at hvI
    have hbot : rootSpan τ K (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by simp [rootSpan]
    rw [hbot, Subgroup.mem_bot] at hvI
    exact hvI
  refine ⟨h, hh, u, huU, ?_⟩
  rw [hzeq, hv1, canonicalRep_one, mul_one, mul_one]

end Borel

section E78


theorem ggBstarElt_adjoint_of_nf {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hfull : ∀ b : Fin τ.rank → Kˣ, rootDiagUnit τ b ∈ torusGroup τ K)
    (hN : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard ≠ 0)
    (hT : ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E → p ^ τ.rank ≤ Nat.card E →
      ∃ g : adjointGroup τ K, E.map (MulAut.conj g).toMonoidHom = TableBExc.torusPow τ K p)
    (hnf : ∀ φ : MulAut (adjointGroup τ K), φ ^ p = 1 → ∃ (a : adjointGroup τ K) (σ : K ≃+* K),
      σ ^ p = 1 ∧ ∀ x : adjointGroup τ K, (φ x : ModGL τ K) =
        (a : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) *
          (a : ModGL τ K)⁻¹) :
    TableBOrth.GGBstarElt p τ.rank (adjointGroup τ K) := by
  have : Fact p.Prime := ⟨hp⟩
  intro E₀ hE₀ hr _ φ hφ hfix
  obtain ⟨g, hg⟩ := hT E₀ hE₀ hr
  set V := TableBExc.torusPow τ K p with hV
  set φ' : MulAut (adjointGroup τ K) := MulAut.conj g * φ * (MulAut.conj g)⁻¹ with hφ'
  have hφ'app : ∀ x, φ' x = g * φ (g⁻¹ * x * g) * g⁻¹ := fun x => by
    simp only [hφ', MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
  have hφapp : ∀ x, φ (g⁻¹ * x * g) = g⁻¹ * φ' x * g := fun x => by
    rw [hφ'app]
    group
  have hφ'p : φ' ^ p = 1 := by rw [hφ', conj_pow, hφ, mul_one, mul_inv_cancel]
  have hgV : ∀ e ∈ E₀, g * e * g⁻¹ ∈ V := fun e he => by
    rw [← hg]
    exact ⟨e, he, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hφ'V : ∀ v ∈ V, φ' v = v := by
    intro v hv
    rw [← hg] at hv
    obtain ⟨e, he, rfl⟩ := hv
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hφ'app,
      show g⁻¹ * (g * e * g⁻¹) * g = e by group, hfix e he]
  obtain ⟨a, σ, hσp, haσ⟩ := hnf φ' hφ'p
  have haV : ∀ v ∈ V, (a : ModGL τ K) * v * (a : ModGL τ K)⁻¹ = v := by
    intro v hv
    have h1 := haσ v
    rw [hφ'V v hv, ExcFrames.units_map_entrywise_eq_self hσp
      (ExcFrames.mem_torusPow_iff_coe.mp hv)] at h1
    exact h1.symm
  obtain ⟨ζ, hζo⟩ := @TableBSymp.exists_orderOf_eq_of_dvd K _ _ p ⟨hp⟩ hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hdV : ∀ j : Fin τ.rank, ∃ v ∈ V,
      (v : ModGL τ K) = rootDiagUnit τ (Pi.mulSingle j ζ) := by
    intro j
    have hH := hfull (Pi.mulSingle j ζ)
    refine ⟨⟨_, CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup hH⟩,
      ExcFrames.mem_torusPow_iff_coe.mpr ⟨hH, ?_⟩, rfl⟩
    rw [rootDiagUnit_pow', ← Pi.mulSingle_pow, hζ, Pi.mulSingle_one, rootDiagUnit_one]
  obtain ⟨h₀, hh₀, u₀, hu₀, hau⟩ := exists_eq_mul_of_commute_mulSingle hp2 hζo a.2 fun j => by
    obtain ⟨v, hv, hveq⟩ := hdV j
    have h1 := haV v hv
    rw [mul_inv_eq_iff_eq_mul] at h1
    rw [← hveq, mul_inv_eq_iff_eq_mul]
    exact h1.symm
  have hTB := triangular_borel_structure.{0, 0} τ K
  have hUC : posUnipotent τ K ≤ adjointGroup τ K :=
    le_sup_right.trans (hTB.2.2.2.2.2.2.2.2.2.2.2 K).1
  set U : Subgroup (adjointGroup τ K) := (posUnipotent τ K).comap (adjointGroup τ K).subtype
    with hUdef
  have hHN : ∀ t ∈ torusGroup τ K, ∀ x ∈ posUnipotent τ K, t * x * t⁻¹ ∈ posUnipotent τ K :=
    fun t ht x hx => (Subgroup.mem_normalizer_iff.mp (hTB.2.2.1 ht) x).mp hx
  have hφ'U : ∀ u ∈ U, φ' u ∈ U := by
    intro u hu
    show ((φ' u : adjointGroup τ K) : ModGL τ K) ∈ posUnipotent τ K
    rw [haσ u, hau]
    have hσu : Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K) ∈ posUnipotent τ K :=
      entrywise_mem_rootSpan hu
    have h1 : u₀ * Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K) * u₀⁻¹ ∈
        posUnipotent τ K := mul_mem (mul_mem hu₀ hσu) (inv_mem hu₀)
    have h2 := hHN h₀ hh₀ _ h1
    rw [show h₀ * u₀ * Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K) * (h₀ * u₀)⁻¹ =
      h₀ * (u₀ * Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K) * u₀⁻¹) * h₀⁻¹ by group]
    exact h2
  have hVU : ∀ v ∈ V, ∀ u ∈ U, v * u * v⁻¹ ∈ U := fun v hv u hu =>
    hHN _ (ExcFrames.mem_torusPow_iff_coe.mp hv).1 _ hu
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hcard := card_posUnipotent (τ := τ) (K := K)
    have hle : posUnipotent τ K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxU : (⟨x, hUC hx⟩ : adjointGroup τ K) ∈ U := hx
      rw [hbot, Subgroup.mem_bot] at hxU
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hxU
    rw [hle, Subgroup.card_bot] at hcard
    have hK2 : 1 < Nat.card K := Finite.one_lt_card
    have := Nat.one_lt_pow hN hK2
    omega
  have hU2 : IsPGroup 2 U :=
    (isPGroup_posUnipotent 2 τ).comap_of_injective _ (adjointGroup τ K).subtype_injective
  refine ⟨U.map (MulAut.conj g⁻¹).toMonoidHom, ?_, hU2.map _, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective]
    exact hUne
  · rintro e he _ ⟨u, hu, rfl⟩
    refine ⟨g * e * g⁻¹ * u * (g * e * g⁻¹)⁻¹, hVU _ (hgV e he) u hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨φ' u, hφ'U u hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hφapp]

theorem nf_E7E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (φ : MulAut (adjointGroup τ K)) (hφ : φ ^ p = 1) :
    ∃ (a : adjointGroup τ K) (σ : K ≃+* K), σ ^ p = 1 ∧ ∀ x : adjointGroup τ K,
      (φ x : ModGL τ K) = (a : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) *
        (a : ModGL τ K)⁻¹ := by
  obtain ⟨hnf, Θ, hΘ, -, -, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  obtain ⟨⟨a, σ⟩, haσ, -⟩ := hnf φ
  exact ⟨a, σ, by rw [← hΘ φ a σ haσ, ← map_pow, hφ, map_one], haσ⟩

theorem nf_F4 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (φ : MulAut (adjointGroup .F4 K)) (hφ : φ ^ p = 1) :
    ∃ (a : adjointGroup .F4 K) (σ : K ≃+* K), σ ^ p = 1 ∧ ∀ x : adjointGroup .F4 K,
      (φ x : ModGL .F4 K) = (a : ModGL .F4 K) *
        Units.map (entrywiseHom σ.toRingHom) (x : ModGL .F4 K) * (a : ModGL .F4 K)⁻¹ := by
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  obtain ⟨-, hnf, ⟨Θ, hΘ, -, -⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  set Θ' : MulAut (adjointGroup .F4 K) →* Multiplicative (ZMod (2 * f)) := Θ with hΘ'
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hnf φ
  dsimp only at hgk
  have hθ : Θ' φ = Multiplicative.ofAdd (((k : ℕ) : ZMod (2 * f))) := hΘ φ g k hgk
  have h0 : (((p * (k : ℕ) : ℕ)) : ZMod (2 * f)) = 0 := by
    have h1 : Θ' (φ ^ p) = 1 := by rw [hφ]; exact map_one Θ'
    rw [map_pow, hθ, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul] at h1
    exact_mod_cast h1
  have hdvd : 2 * f ∣ p * k := (ZMod.natCast_eq_zero_iff _ _).mp h0
  have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  obtain ⟨j, hj⟩ : 2 ∣ (k : ℕ) := h2p.dvd_of_dvd_mul_left ((dvd_mul_right 2 f).trans hdvd)
  have hfj : f ∣ p * j := by
    refine Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) ?_
    rw [show 2 * (p * j) = p * (k : ℕ) by rw [hj]; ring]
    exact hdvd
  obtain ⟨t, ht⟩ := hfj
  have hσjp : (ExcFrames.frobAut K ^ j) ^ p = 1 := by
    rw [← pow_mul, mul_comm, ht, pow_mul, ExcFrames.frobAut_pow_card hK, one_pow]
  refine ⟨g, ExcFrames.frobAut K ^ j, hσjp, fun x => ?_⟩
  have e : φ x = g * (CFSG.LieType.Ree.ReeTag.F4.finiteExceptionalAut K ^ (k : ℕ)) x * g⁻¹ := by
    rw [hgk]
    rfl
  rw [e, hj, finiteExceptionalAut_pow_two_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, CFSG.LieType.Ree.ReeTag.coe_finiteFrobeniusAut_pow
      (σ := ExcFrames.frobAut K) ExcFrames.frobAut_apply j x]
  rfl

end E78

section Recipe

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggInnerDiagBound_E7E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGInnerDiagBound p τ.rank (TableBExc.RecipeGroup τ K) (TableBExc.RecipeID τ K) := by
  have := TableBExc.finite_recipeGroup τ K
  have hinn : TableBExc.RecipeID τ K ⊆
      Set.range
        (MulAut.conj : TableBExc.RecipeGroup τ K →* MulAut (TableBExc.RecipeGroup τ K)) := by
    rcases hτ with rfl | rfl
    · exact TableBExc.idImage_subset_inn_E7 K
    · exact TableBExc.idImage_subset_inn_E8 K
  have hN : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard ≠ 0 := by
    rcases hτ with rfl | rfl
    · rw [CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E7]
      norm_num
    · rw [CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E8]
      norm_num
  exact CorFourTwoOpen.ggInnerDiagBound_of_elt hp hinn (TableBExc.center_recipeGroup_eq_bot τ K)
    (TableBOrth.ggBstarElt_of_mulEquiv (TableBExc.recipeEquiv τ K).symm
      (ggBstarElt_adjoint_of_nf hp hp2 hpq (TableBExc.full_of_E7_E8 hτ) hN
        (IOneRest.ggExcToralRankInput_E7E8 hτ hp hp2 hpq) fun φ hφ => nf_E7E8 hτ hf hK φ hφ))

theorem ggInnerDiagBound_F4 {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGInnerDiagBound p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  have := TableBF4.finite_recipeGroup (K := K)
  have hT : GGF4ToralRankInput K p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact TableBF4.ggF4ToralRankInput_three hpq
    · exact TableBF4.ggF4ToralRankInput_of_five_le hp (hp.five_le_of_ne_two_of_ne_three hp2 hp3)
        hpq
  exact CorFourTwoOpen.ggInnerDiagBound_of_elt hp (TableBF4.idImage_subset_inn K)
    (TableBF4.center_recipeGroup_eq_bot K)
    (TableBOrth.ggBstarElt_of_mulEquiv (TableBF4.recipeEquiv K).symm
      (ggBstarElt_adjoint_of_nf (τ := .F4) hp hp2 hpq
        (fun a => CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup a)
        (by rw [CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_F4]; norm_num) hT
        fun φ hφ => nf_F4 hf hK hp hp2 φ hφ))

end Recipe

end ExcSplitL

open ExcSplitL

@[expose] def GGExcLSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n - 1

section Labels


theorem largeEvenLabelAll_innerDiagBound_excLSplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGExcLSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag hpn hn
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  rcases htag with rfl | rfl | rfl <;> intro Q hQ <;> dsimp only [LargeEvenRawDatum] at hQ ⊢ <;>
    refine recipeChevalley_and (fun K _ _ hK => ?_) hQ <;>
    have : CharP K 2 := charP_two_of_card hK <;>
    have hpq : p ∣ Nat.card K - 1 := (by rw [hK]; exact hpn)
  · exact ⟨7, TableBExc.ggTorusLift_E7 hp hp2 hpq,
      ggInnerDiagBound_E7E8 (τ := .E7) (Or.inl rfl) hn hK hp hp2 hpq⟩
  · exact ⟨8, TableBExc.ggTorusLift_E8 hp hp2 hpq,
      ggInnerDiagBound_E7E8 (τ := .E8) (Or.inr rfl) hn hK hp hp2 hpq⟩
  · exact ⟨4, TableBF4.ggTorusLift_F4 hp hp2 hpq, ggInnerDiagBound_F4 hn hK hp hp2 hpq⟩

theorem ggBstarInnerDiagLInputOn_excLSplit (T : ℕ → LargeEvenLabel → Prop) :
    GGBstarInnerDiagLInputOn fun p lab => T p lab ∧ GGExcLSplitLabel p lab :=
  ggBstarInnerDiagLInputOn_of_labels' ggLNoncyclicInput_holds fun _ _ hp hlab h =>
    largeEvenLabelAll_innerDiagBound_excLSplit hp hlab h.2

end Labels

end CFSG.StandardType

end
