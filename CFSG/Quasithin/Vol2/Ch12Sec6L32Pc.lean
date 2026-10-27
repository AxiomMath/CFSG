module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32Pa
public import CFSG.Quasithin.Vol2.Ch12Sec6L32Pb
public import CFSG.Quasithin.Vol2.Ch11SecO8B
public import CFSG.Quasithin.Vol2.Ch5Sec1L34E54NoFF
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3Structure38Basic
public import CFSG.Quasithin.Background.L34OutFacts
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.H13.L1232

open CFSG.Open (pCoreOf quasithinGenFitting)
open CFSG.Quasithin CFSG.Quasithin.EmptyFaithfulMultiple CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank Matrix

variable {V : Type} [CommGroup V]

section Graph

variable {k : Type} [Field k] [Finite k] {L : Subgroup (MulAut V)} {U Z : Subgroup V}
  {π : ↥(StatedSL 3 k) →* ↥L} {s : MulAut V} {α : MulAut ↥(StatedSL 3 k)}

theorem not_isGraphType_of_natural_section
    (hπ : (FFModel.nat (StatedSL 3 k)).RealizesVia L U Z π) (hU : ∀ u ∈ U, s u ∈ U)
    (hU' : ∀ u ∈ U, s⁻¹ u ∈ U) (hZ : ∀ z ∈ Z, s z ∈ Z) (hZ' : ∀ z ∈ Z, s⁻¹ z ∈ Z)
    (hα : ∀ γ, ((π (α γ) : ↥L) : MulAut V) = s * (π γ : ↥L) * s⁻¹) :
    ¬ L34Out.IsGraphTypeStated α := fun hg =>
  L34Out.not_exists_equivariant_stated hg
    (exists_equivariant_of_natural_section hπ hU hU' hZ hZ' hα)

theorem not_isGraphType_of_two_natural {I : Fin 2 → Subgroup V}
    (hind : ∀ i, I i ⊓ (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ i), I j) = Z) (hsup : (Z ⊔ ⨆ i, I i) = U)
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 k)).RealizesVia L (I i) Z π) (hU : ∀ u ∈ U, s u ∈ U)
    (hU' : ∀ u ∈ U, s⁻¹ u ∈ U) (hZ : ∀ z ∈ Z, s z ∈ Z) (hZ' : ∀ z ∈ Z, s⁻¹ z ∈ Z)
    (hα : ∀ γ, ((π (α γ) : ↥L) : MulAut V) = s * (π γ : ↥L) * s⁻¹) :
    ¬ L34Out.IsGraphTypeStated α := fun hg =>
  L34Out.not_exists_equivariant_stated hg
    (exists_equivariant_of_two_natural hind hsup hreal hU hU' hZ hZ' hα)

end Graph

section Twist

variable {k : Type} [Field k] {L : Subgroup (MulAut V)} {π : ↥(StatedSL 3 k) →* ↥L}

@[expose] noncomputable def conjL {s : MulAut V}
    (hs : s ∈ Subgroup.normalizer (L : Set (MulAut V))) :
    ↥L ≃* ↥L :=
  (L.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective).trans
    (MulEquiv.subgroupCongr (A38.map_conj_eq_iff.2 hs))

theorem coe_conjL {s : MulAut V} (hs : s ∈ Subgroup.normalizer (L : Set (MulAut V))) (l : ↥L) :
    ((conjL hs l : ↥L) : MulAut V) = s * l * s⁻¹ := rfl

@[expose] noncomputable def twistAut (hπ : Function.Bijective π) {s : MulAut V}
    (hs : s ∈ Subgroup.normalizer (L : Set (MulAut V))) : MulAut ↥(StatedSL 3 k) :=
  ((MulEquiv.ofBijective π hπ).trans (conjL hs)).trans (MulEquiv.ofBijective π hπ).symm

theorem twistAut_spec (hπ : Function.Bijective π) {s : MulAut V}
    (hs : s ∈ Subgroup.normalizer (L : Set (MulAut V))) (γ : ↥(StatedSL 3 k)) :
    ((π (twistAut hπ hs γ) : ↥L) : MulAut V) = s * (π γ : ↥L) * s⁻¹ := by
  have : π (twistAut hπ hs γ) = conjL hs (π γ) :=
    (MulEquiv.ofBijective π hπ).apply_symm_apply _
  rw [this, coe_conjL]

theorem eq_twistAut (hπ : Function.Bijective π) {s : MulAut V}
    (hs : s ∈ Subgroup.normalizer (L : Set (MulAut V))) {β : MulAut ↥(StatedSL 3 k)}
    (hβ : ∀ γ, ((π (β γ) : ↥L) : MulAut V) = s * (π γ : ↥L) * s⁻¹) : β = twistAut hπ hs := by
  ext γ : 1
  apply hπ.1
  apply Subtype.ext
  rw [hβ, twistAut_spec]

theorem twistAut_pow_spec (hπ : Function.Bijective π) {s : MulAut V}
    (hs : s ∈ Subgroup.normalizer (L : Set (MulAut V))) (n : ℕ) (γ : ↥(StatedSL 3 k)) :
    ((π ((twistAut hπ hs ^ n) γ) : ↥L) : MulAut V) = s ^ n * (π γ : ↥L) * (s ^ n)⁻¹ := by
  induction n generalizing γ with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, twistAut_spec, pow_succ]
    group

theorem twistAut_mul_inv (hπ : Function.Bijective π) {s₁ s₂ : MulAut V}
    (hs₁ : s₁ ∈ Subgroup.normalizer (L : Set (MulAut V)))
    (hs₂ : s₂ ∈ Subgroup.normalizer (L : Set (MulAut V))) :
    twistAut hπ hs₁ * (twistAut hπ hs₂)⁻¹ =
      twistAut hπ (Subgroup.mul_mem _ hs₁ (Subgroup.inv_mem _ hs₂)) := by
  refine eq_twistAut hπ _ fun γ => ?_
  rw [MulAut.mul_apply, twistAut_spec]
  have h : ((π ((twistAut hπ hs₂)⁻¹ γ) : ↥L) : MulAut V) = s₂⁻¹ * (π γ : ↥L) * s₂ := by
    have := twistAut_spec hπ hs₂ ((twistAut hπ hs₂)⁻¹ γ)
    rw [MulAut.apply_inv_self] at this
    rw [this]
    group
  rw [h]
  group

theorem twistAut_mem_inn_of_mem (hπ : Function.Bijective π) {s : MulAut V}
    (hs : s ∈ Subgroup.normalizer (L : Set (MulAut V))) (hsL : s ∈ L) :
    twistAut hπ hs ∈ L34Out.innStated k := by
  obtain ⟨γ₀, hγ₀⟩ := hπ.2 ⟨s, hsL⟩
  refine ⟨γ₀, eq_twistAut hπ hs (β := MulAut.conj γ₀) fun γ => ?_⟩
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hγ₀]
  rfl

theorem twistAut_not_mem_inn (hπ : Function.Bijective π) {Γ : Subgroup (MulAut V)}
    (hLΓ : L ≤ Γ) (hCL : Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L) {s : MulAut V}
    (hsΓ : s ∈ Γ) (hs : s ∈ Subgroup.normalizer (L : Set (MulAut V))) (hsL : s ∉ L) :
    twistAut hπ hs ∉ L34Out.innStated k := by
  rintro ⟨γ₀, hγ₀⟩
  apply hsL
  set l₀ : MulAut V := ((π γ₀ : ↥L) : MulAut V) with hl₀
  have hl₀L : l₀ ∈ L := (π γ₀).2
  have hc : l₀⁻¹ * s ∈ Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) := by
    refine ⟨Γ.mul_mem (Γ.inv_mem (hLΓ hl₀L)) hsΓ, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨γ, hγ⟩ := hπ.2 ⟨y, hy⟩
    have h1 := twistAut_spec hπ hs γ
    rw [← hγ₀, MulAut.conj_apply, map_mul, map_mul, map_inv, hγ] at h1
    have h2 : l₀ * y * l₀⁻¹ = s * y * s⁻¹ := h1
    calc y * (l₀⁻¹ * s) = l₀⁻¹ * (l₀ * y * l₀⁻¹) * s := by group
      _ = l₀⁻¹ * (s * y * s⁻¹) * s := by rw [h2]
      _ = l₀⁻¹ * s * y := by group
  have := L.mul_mem hl₀L (hCL hc)
  simpa using this

end Twist

section B51

variable [Finite V] {J L : Subgroup (MulAut V)}

theorem eq_four_of_card_sl3 {q : ℕ} (h : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) = 60480) : q = 4 := by
  rcases Nat.lt_or_ge q 5 with hq | hq
  · interval_cases q <;> simp_all
  · exfalso
    have h1 : 125 ≤ q ^ 3 := by
      calc 125 = 5 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 24 ≤ q ^ 2 - 1 := by
      have : 25 ≤ q ^ 2 := by
        calc 25 = 5 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have h3 : 124 ≤ q ^ 3 - 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega

omit [Finite V] in
theorem card_eq_four_of_realizes {K' : Type} [Field K'] [Finite K'] {U Z : Subgroup V}
    {π : ↥(StatedSL 3 K') →* ↥L} (hπ : (FFModel.nat (StatedSL 3 K')).RealizesVia L U Z π)
    (hL : Nat.card ↥L = 60480) : Nat.card K' = 4 := by
  have := Fintype.ofFinite K'
  have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  have hc : Nat.card ↥L = Nat.card ↥(StatedSL 3 K') :=
    (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)).symm
  rw [FFL.card_statedSL_three, hL, ← Nat.card_eq_fintype_card] at hc
  exact eq_four_of_card_sl3 hc.symm

omit [Finite V] in
theorem false_of_realizes_sl_zmod {n : ℕ} (hn : n = 4 ∨ n = 5) {U Z : Subgroup V}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    (hπ : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia L U Z π)
    (hL : Nat.card ↥L = 60480) : False := by
  have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  have hc : Nat.card ↥L = Nat.card ↥(StatedSL n (ZMod 2)) :=
    (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)).symm
  rcases hn with rfl | rfl
  · rw [FFL.card_statedSL_four, hL] at hc
    omega
  · rw [FFL.card_statedSL_five, hL] at hc
    omega

theorem b51_cases_sl34 (hV : ∀ v : V, v ^ 2 = 1) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 4) (e : ↥L ≃* SpecialLinearGroup (Fin 3) k) (h1 : B51Part1 J L) :
    (∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 4 ∧
      ∃ π : ↥(StatedSL 3 K') →* ↥L,
        (FFModel.nat (StatedSL 3 K')).RealizesVia L (commV L) (fixV L ⊓ commV L) π) ∨
    (∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 4 ∧
      ∃ (I : Fin 2 → Subgroup V) (π : ↥(StatedSL 3 K') →* ↥L),
        (∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin 2) (_ : j ≠ i), I j) = ⊥) ∧ (⊥ ⊔ ⨆ i, I i) = commV L ∧
        ∀ i, (FFModel.nat (StatedSL 3 K')).RealizesVia L (I i) ⊥ π) := by
  have hL : Nat.card ↥L = 60480 := by
    have := Fintype.ofFinite k
    rw [Nat.card_congr (e.trans (specialLinearGroupEquivStatedSL 3 k)).toEquiv,
      FFL.card_statedSL_three, ← Nat.card_eq_fintype_card, hk]
    norm_num
  obtain ⟨-, h⟩ := h1
  rcases h with ⟨-, hB, -⟩ | ⟨-, n, K', _, _, hK', I, π, hind, hsup, hreal, -, -⟩ |
    ⟨n, -, hn, π, U₁, U₂, -, h₁, -⟩ | ⟨-, n, hn, m, hm1, -, I, π, -, -, -, hreal⟩
  · left
    obtain ⟨K', _, _, hK', π, hπ⟩ :=
      Vol2.Ch11.SecC.factB42SL3_holds k 2 le_rfl (by rw [hk]; norm_num) V hV L _ _ ⟨e⟩ hB
    exact ⟨K', inferInstance, inferInstance, by rw [hK']; norm_num, π, hπ⟩
  · right
    refine ⟨K', inferInstance, inferInstance, card_eq_four_of_realizes (hreal 0) hL, I, π,
      fun i => ?_, ?_, hreal⟩
    · rw [bot_sup_eq]
      exact disjoint_iff.mp (hind i)
    · rw [bot_sup_eq]
      exact hsup
  · exact (false_of_realizes_sl_zmod hn h₁ hL).elim
  · exact (false_of_realizes_sl_zmod hn (hreal ⟨0, hm1⟩) hL).elim

end B51

section Final

variable [Finite V] {Γ L : Subgroup (MulAut V)}

omit [Finite V] in
theorem fixV_commV_invariant {s : MulAut V} (hs : s ∈ Subgroup.normalizer (L : Set (MulAut V))) :
    (∀ z ∈ fixV L, s z ∈ fixV L) ∧ ∀ u ∈ commV L, s u ∈ commV L := by
  refine ⟨fun z hz l hl => ?_, fun u hu => ?_⟩
  · have hl' : s⁻¹ * l * s ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) l).mp hl
      simpa using this
    have h1 : (s⁻¹ * l * s) z = z := hz _ hl'
    have h2 : l (s z) = s ((s⁻¹ * l * s) z) := by simp [MulAut.mul_apply]
    rw [h2, h1]
  · induction hu using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨l, hl, v, rfl⟩ := hw
      refine Subgroup.subset_closure ⟨s * l * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs l).mp hl,
        s v, ?_⟩
      simp [MulAut.mul_apply]
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem false_of_ff_psl34 (h56 : AsB56) (hV : ∀ v : V, v ^ 2 = 1)
    (hQ : G64.IsQuotientOfSQTKCat ↥Γ) (hq : CFSG.IsQuasisimple ↥L) (hLΓ : L ≤ Γ)
    (hΓL : Γ ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hC : ∀ x ∈ Γ, x ∈ Subgroup.centralizer (L : Set (MulAut V)) → x ^ 2 = 1 → x = 1)
    (hoff : ∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 4) (e : ↥L ≃* StatedProj (StatedSL 3 k)) : False := by
  have hIs : IsPSL 3 2 2 ↥L :=
    ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, k, inferInstance,
      inferInstance, by rw [hk]; norm_num, ⟨e⟩⟩
  have hLie : CFSG.Blueprint.LieModel ↥L .PSL 3 2 2 := Or.inl ⟨by decide, hIs⟩
  have hc : 360 < Nat.card ↥L := by
    rw [H13.E54.card_of_lieModel hLie]
    norm_num
  obtain ⟨-, -, hconc⟩ := fstar_ffJ_eq h56 hV hQ hq hLΓ hΓL hC hc hoff
  exact H13.E54.false_of_b51Part1 hLie hconc.1

theorem false_of_ff_sl34 (h56 : AsB56) (hV : ∀ v : V, v ^ 2 = 1)
    (hQ : G64.IsQuotientOfSQTKCat ↥Γ) (hq : CFSG.IsQuasisimple ↥L) (hLΓ : L ≤ Γ)
    (hΓL : Γ ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hC : ∀ x ∈ Γ, x ∈ Subgroup.centralizer (L : Set (MulAut V)) → x ^ 2 = 1 → x = 1)
    (hCL : Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L)
    (hoff : ∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 4) (e : ↥L ≃* SpecialLinearGroup (Fin 3) k)
    (h2 : ∀ x ∈ Γ, ∃ m : ℕ, x ^ 2 ^ m ∈ L) {s₁ s₂ : MulAut V} (hs₁ : s₁ ∈ Γ) (hs₂ : s₂ ∈ Γ)
    (h₁ : s₁ ∉ L) (h₂ : s₂ ∉ L) (h₁₂ : s₁ * s₂⁻¹ ∉ L) : False := by
  have hc : 360 < Nat.card ↥L := by
    have := Fintype.ofFinite k
    rw [Nat.card_congr (e.trans (specialLinearGroupEquivStatedSL 3 k)).toEquiv,
      FFL.card_statedSL_three, ← Nat.card_eq_fintype_card, hk]
    norm_num
  obtain ⟨-, -, hconc⟩ := fstar_ffJ_eq h56 hV hQ hq hLΓ hΓL hC hc hoff
  have hn₁ := hΓL hs₁
  have hn₂ := hΓL hs₂
  have hn₁₂ := hΓL (Γ.mul_mem hs₁ (Γ.inv_mem hs₂))
  have hgraph : ∀ {K' : Type} [Field K'] [Finite K'], Nat.card K' = 4 →
      ∀ {π : ↥(StatedSL 3 K') →* ↥L} (hπ : Function.Bijective π),
        L34Out.IsGraphTypeStated (twistAut hπ hn₁) ∨
          L34Out.IsGraphTypeStated (twistAut hπ hn₂) := by
    intro K' _ _ hK' π hπ
    obtain ⟨m₁, hm₁⟩ := h2 s₁ hs₁
    obtain ⟨m₂, hm₂⟩ := h2 s₂ hs₂
    obtain ⟨m₃, hm₃⟩ := h2 _ (Γ.mul_mem hs₁ (Γ.inv_mem hs₂))
    have hpow : ∀ {s : MulAut V} (hs : s ∈ Subgroup.normalizer (L : Set (MulAut V))) {m : ℕ},
        s ^ 2 ^ m ∈ L → twistAut hπ hs ^ 2 ^ m ∈ L34Out.innStated K' := by
      intro s hs m hm
      have : twistAut hπ hs ^ 2 ^ m = twistAut hπ (Subgroup.pow_mem _ hs (2 ^ m)) :=
        eq_twistAut hπ _ fun γ => twistAut_pow_spec hπ hs _ γ
      rw [this]
      exact twistAut_mem_inn_of_mem hπ _ hm
    refine L34Out.isGraphTypeStated_or hK' (m₃ := m₃) (hpow hn₁ hm₁) (hpow hn₂ hm₂) ?_
      (twistAut_not_mem_inn hπ hLΓ hCL hs₁ hn₁ h₁) (twistAut_not_mem_inn hπ hLΓ hCL hs₂ hn₂ h₂) ?_
    · rw [twistAut_mul_inv hπ hn₁ hn₂]
      exact hpow _ hm₃
    · rw [twistAut_mul_inv hπ hn₁ hn₂]
      exact twistAut_not_mem_inn hπ hLΓ hCL (Γ.mul_mem hs₁ (Γ.inv_mem hs₂)) _ h₁₂
  have hinv : ∀ {s : MulAut V}, s ∈ Γ → (∀ u ∈ commV L, s u ∈ commV L) ∧
      (∀ u ∈ commV L, s⁻¹ u ∈ commV L) ∧ (∀ z ∈ fixV L ⊓ commV L, s z ∈ fixV L ⊓ commV L) ∧
      (∀ z ∈ fixV L ⊓ commV L, s⁻¹ z ∈ fixV L ⊓ commV L) := by
    intro s hs
    have h1 := fixV_commV_invariant (hΓL hs)
    have h2 := fixV_commV_invariant (hΓL (Γ.inv_mem hs))
    exact ⟨h1.2, h2.2, fun z hz => ⟨h1.1 z hz.1, h1.2 z hz.2⟩,
      fun z hz => ⟨h2.1 z hz.1, h2.2 z hz.2⟩⟩
  have hbot : ∀ {s : MulAut V}, (∀ z ∈ (⊥ : Subgroup V), s z ∈ (⊥ : Subgroup V)) := by
    intro s z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  rcases b51_cases_sl34 hV hk e hconc.1 with ⟨K', _, _, hK', π, hπ⟩ |
    ⟨K', _, _, hK', I, π, hind, hsup, hreal⟩
  · have hbij : Function.Bijective π :=
      ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ, hπ.1⟩
    rcases hgraph hK' hbij with hg | hg
    · obtain ⟨a, b, c, d⟩ := hinv hs₁
      exact not_isGraphType_of_natural_section hπ a b c d (twistAut_spec hbij hn₁) hg
    · obtain ⟨a, b, c, d⟩ := hinv hs₂
      exact not_isGraphType_of_natural_section hπ a b c d (twistAut_spec hbij hn₂) hg
  · have hbij : Function.Bijective π :=
      ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) (hreal 0), (hreal 0).1⟩
    rcases hgraph hK' hbij with hg | hg
    · obtain ⟨a, b, -, -⟩ := hinv hs₁
      exact not_isGraphType_of_two_natural hind hsup hreal a b hbot hbot
        (twistAut_spec hbij hn₁) hg
    · obtain ⟨a, b, -, -⟩ := hinv hs₂
      exact not_isGraphType_of_two_natural hind hsup hreal a b hbot hbot
        (twistAut_spec hbij hn₂) hg

end Final

end CFSG.Quasithin.H13.L1232
