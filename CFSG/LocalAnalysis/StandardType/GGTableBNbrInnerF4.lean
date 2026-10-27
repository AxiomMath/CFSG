module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerOrth
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Split

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB TableBSymp

section Refl

@[expose] def GGTorusReflElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    ∃ (d : ℕ) (e : Multiplicative (Fin d → ZMod p) →* R)
      (c : Fin d → (Fin d → ZMod p) →ₗ[ZMod p] ZMod p) (n : Fin d → R), e.range = E ∧
      (∀ i, c i (Pi.single i 1) = 2) ∧
      (∀ i v, n i * e (.ofAdd v) * (n i)⁻¹ = e (.ofAdd (v - c i v • Pi.single i 1))) ∧
      ∀ E' : Subgroup R, E' ≤ E → (∀ i, ∀ x ∈ E', n i * x * (n i)⁻¹ ∈ E') → E' = ⊥ ∨ E' = E

theorem ggTorusSecElt_of_reflElt {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    (h : GGTorusReflElt p r R) : GGTorusSecElt p r R := by
  intro E hE hr h3
  obtain ⟨d, e, c, n, heE, hc, hn, hirr⟩ := h E hE hr h3
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set τ := TableBF4.piTorus e with hτdef
  have hτE : τ.range = E := by rw [hτdef, TableBF4.range_piTorus, heE]
  refine ⟨d, τ, Set.range n, hτE, fun L' _ ψ hψ hker => ?_, ?_, fun E' hE' hinv => ?_⟩
  · have hcomm : ∀ x ∈ τ.range.comap ψ, ∀ y ∈ τ.range.comap ψ, x * y = y * x := by
      rw [hτdef, TableBF4.range_piTorus]
      exact CFSG.RankThree.CentralCover.reflection_comap_comm hψ hker hp hp2 e c hc n hn
    have hinvb : ∀ i : Fin d, ∃ w : R,
        w * TableBSymp.torusBasis τ i * w⁻¹ = (TableBSymp.torusBasis τ i)⁻¹ := by
      intro i
      refine ⟨n i, ?_⟩
      rw [hτdef, TableBF4.torusBasis_piTorus, hn, hc, ← map_inv, ← ofAdd_neg]
      congr 2
      rw [two_smul]
      abel
    exact TableBF4.exists_torus_section_of_comm hψ hker hodd τ hcomm hinvb
  · rintro _ ⟨i, rfl⟩ x hx
    rw [← heE] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    refine ⟨.ofAdd (Multiplicative.toAdd a - c i (Multiplicative.toAdd a) • Pi.single i 1), ?_⟩
    rw [← hn, ofAdd_toAdd]
  · exact hirr E' hE' fun i x hx => hinv (n i) ⟨i, rfl⟩ x hx

theorem ggTorusSecElt_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGTorusSecElt p r R') : GGTorusSecElt p r R := by
  intro E hE hr h3
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  obtain ⟨k, τ, W, hτE, hsec, hWE, hirr⟩ :=
    h (E.map e.toMonoidHom) (isElemAbelian_map hE _) (hcard ▸ hr) (hcard ▸ h3)
  have hmem : ∀ x : R, e x ∈ E.map e.toMonoidHom ↔ x ∈ E := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  refine ⟨k, e.symm.toMonoidHom.comp τ, e.symm '' W, ?_, fun L' _ ψ hψ hker => ?_, ?_,
    fun E' hE' hinv' => ?_⟩
  · ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      have : τ f ∈ τ.range := ⟨f, rfl⟩
      rw [hτE] at this
      rw [← hmem]
      simpa using this
    · intro hx
      have : e x ∈ τ.range := hτE ▸ (hmem x).mpr hx
      obtain ⟨f, hf⟩ := this
      exact ⟨f, by simp [hf]⟩
  · obtain ⟨σ, hσ⟩ := hsec L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) (fun l hl =>
      hker (by simpa [MonoidHom.mem_ker] using hl))
    refine ⟨σ, MonoidHom.ext fun f => ?_⟩
    have h1 := DFunLike.congr_fun hσ f
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1 ⊢
    rw [← h1, MulEquiv.symm_apply_apply]
  · rintro _ ⟨w, hw, rfl⟩ x hx
    rw [← hmem]
    simpa using hWE w hw (e x) ((hmem x).mpr hx)
  · have hle : E'.map e.toMonoidHom ≤ E.map e.toMonoidHom := Subgroup.map_mono hE'
    have hinv'' : ∀ w ∈ W, ∀ x ∈ E'.map e.toMonoidHom, w * x * w⁻¹ ∈ E'.map e.toMonoidHom := by
      rintro w hw _ ⟨y, hy, rfl⟩
      refine ⟨_, hinv' (e.symm w) ⟨w, hw, rfl⟩ y hy, ?_⟩
      simp
    rcases hirr _ hle hinv'' with h1 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have : e x ∈ E'.map e.toMonoidHom := ⟨x, hx, rfl⟩
      rw [h1, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at this
      exact this ▸ Subgroup.one_mem _
    · right
      refine le_antisymm hE' fun x hx => ?_
      have : e x ∈ E'.map e.toMonoidHom := h1 ▸ (hmem x).mpr hx
      obtain ⟨y, hy, hyx⟩ := this
      exact e.injective hyx ▸ hy

end Refl

section ReflF4

open CFSG.Blueprint.Chevalley CFSG.RankThree.CentralCover

theorem f4_fin_cases (j : Fin Tag.F4.rank) :
    j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ ∨ j = ⟨2, by decide⟩ ∨ j = ⟨3, by decide⟩ := by
  obtain ⟨k, hk⟩ := j
  have hk' : k < 4 := hk
  interval_cases k <;> simp

theorem f4_cartan_entry (i j : Fin Tag.F4.rank) :
    Tag.F4.cartan i j = 2 ∨ Tag.F4.cartan i j = 0 ∨ Tag.F4.cartan i j = -1 ∨
      Tag.F4.cartan i j = -2 := by
  rcases f4_fin_cases i with rfl | rfl | rfl | rfl <;>
    rcases f4_fin_cases j with rfl | rfl | rfl | rfl <;> decide

theorem f4_cartan_connected (S : Finset (Fin Tag.F4.rank)) (hS : S.Nonempty)
    (hcl : ∀ i ∈ S, ∀ j, Tag.F4.cartan i j ≠ 0 → j ∈ S) : S = Finset.univ := by
  have h01 := hcl ⟨0, by decide⟩
  have h10 := hcl ⟨1, by decide⟩
  have h21 := hcl ⟨2, by decide⟩
  have h32 := hcl ⟨3, by decide⟩
  have h0 : (⟨0, by decide⟩ : Fin Tag.F4.rank) ∈ S := by
    obtain ⟨i, hi⟩ := hS
    rcases f4_fin_cases i with rfl | rfl | rfl | rfl
    · exact hi
    · exact h10 hi _ (by decide)
    · exact h10 (h21 hi _ (by decide)) _ (by decide)
    · exact h10 (h21 (h32 hi _ (by decide)) _ (by decide)) _ (by decide)
  have h1 := h01 h0 ⟨1, by decide⟩ (by decide)
  have h2 := h10 h1 ⟨2, by decide⟩ (by decide)
  have h3 := h21 h2 ⟨3, by decide⟩ (by decide)
  rw [Finset.eq_univ_iff_forall]
  intro j
  rcases f4_fin_cases j with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

variable {p : ℕ} [NeZero p]

omit [NeZero p] in
theorem cartanFunctional_single_apply [NeZero p] (τ : Tag) (i j : Fin τ.rank) :
    cartanFunctional τ p j (Pi.single i 1) = (τ.cartan i j : ZMod p) := by
  classical
  rw [cartanFunctional_apply, Finset.sum_eq_single i (fun k _ hk => by
    rw [Pi.single_eq_of_ne hk, mul_zero]) (fun h => absurd (Finset.mem_univ i) h),
    Pi.single_eq_same, mul_one]

theorem eq_bot_or_eq_top_of_reflF4 (hp : p.Prime) (hp2 : p ≠ 2)
    (F : Subgroup (Multiplicative (Fin Tag.F4.rank → ZMod p)))
    (hinv : ∀ i v, Multiplicative.ofAdd v ∈ F →
      Multiplicative.ofAdd (v - cartanFunctional .F4 p i v • Pi.single i 1) ∈ F) :
    F = ⊥ ∨ F = ⊤ := by
  classical
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  by_cases hF : F = ⊥
  · exact Or.inl hF
  right
  have hsmul : ∀ (i : Fin Tag.F4.rank) (b : ZMod p), b ≠ 0 →
      Multiplicative.ofAdd (b • (Pi.single i 1 : Fin Tag.F4.rank → ZMod p)) ∈ F →
      ∀ a : ZMod p, Multiplicative.ofAdd (a • (Pi.single i 1 : Fin Tag.F4.rank → ZMod p)) ∈ F := by
    intro i b hb hbF a
    obtain ⟨n, hn⟩ := NbrOrth.exists_pow_eq_of_ne_one hp (a := Multiplicative.ofAdd b)
      (fun h => hb (by simpa using congrArg Multiplicative.toAdd h)) (Multiplicative.ofAdd a)
    have hnb : n • b = a := by simpa using congrArg Multiplicative.toAdd hn
    have h := F.pow_mem hbF n
    rwa [← ofAdd_nsmul, ← smul_assoc, hnb] at h
  have hsub : ∀ v w : Fin Tag.F4.rank → ZMod p, Multiplicative.ofAdd v ∈ F →
      Multiplicative.ofAdd w ∈ F → Multiplicative.ofAdd (v - w) ∈ F := fun v w hv hw => by
    rw [ofAdd_sub, div_eq_mul_inv]
    exact F.mul_mem hv (F.inv_mem hw)
  have hcancel : ∀ v w : Fin Tag.F4.rank → ZMod p, v - (v - w) = w := fun v w => by abel
  obtain ⟨⟨x, hxF⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF
  set v := Multiplicative.toAdd x with hv
  have hvF : Multiplicative.ofAdd v ∈ F := by rw [hv, ofAdd_toAdd]; exact hxF
  have hv0 : v ≠ 0 := by
    intro h
    apply hx1
    apply Subtype.ext
    change x = 1
    rw [← ofAdd_toAdd x, ← hv, h, ofAdd_zero]
  obtain ⟨i, hi⟩ : ∃ i, cartanFunctional .F4 p i v ≠ 0 := by
    by_contra h
    push Not at h
    apply hv0
    have hdet : ((Tag.F4.cartan.map (Int.castRingHom (ZMod p))).transpose).det ≠ 0 := by
      rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
        CFSG.LieType.Chevalley.det_cartan_F4, map_one]
      exact one_ne_zero
    have hmul : (Tag.F4.cartan.map (Int.castRingHom (ZMod p))).transpose.mulVec v = 0 := by
      funext j
      rw [Pi.zero_apply, ← h j, cartanFunctional_apply]
      simp [Matrix.mulVec, dotProduct]
    have := Fact.mk hp
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  have hiF : ∀ a : ZMod p,
      Multiplicative.ofAdd (a • (Pi.single i 1 : Fin Tag.F4.rank → ZMod p)) ∈ F := by
    refine hsmul i _ hi ?_
    have h := hsub v _ hvF (hinv i v hvF)
    rwa [hcancel] at h
  set S : Finset (Fin Tag.F4.rank) := Finset.univ.filter fun j =>
    ∀ a : ZMod p, Multiplicative.ofAdd (a • (Pi.single j 1 : Fin Tag.F4.rank → ZMod p)) ∈ F
    with hS
  have h2 : (2 : ZMod p) ≠ 0 := fun h2 => hp2 (by
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hSall : S = Finset.univ := by
    refine f4_cartan_connected S ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiF⟩⟩ ?_
    intro j hj k hjk
    have hjF := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsmul k (Tag.F4.cartan j k : ZMod p) ?_ ?_⟩
    · rcases f4_cartan_entry j k with h | h | h | h
      · rw [h]
        exact_mod_cast h2
      · exact absurd h hjk
      · rw [h]
        push_cast
        exact neg_ne_zero.mpr one_ne_zero
      · rw [h]
        push_cast
        exact neg_ne_zero.mpr h2
    · have h1 := hjF 1
      rw [one_smul] at h1
      have h := hsub _ _ h1 (hinv k _ h1)
      rwa [hcancel, cartanFunctional_single_apply] at h
  have hall : ∀ j (a : ZMod p),
      Multiplicative.ofAdd (a • (Pi.single j 1 : Fin Tag.F4.rank → ZMod p)) ∈ F := by
    intro j
    have hj : j ∈ S := hSall ▸ Finset.mem_univ j
    exact (Finset.mem_filter.mp hj).2
  rw [eq_top_iff]
  intro y _
  rw [← ofAdd_toAdd y, ← Finset.univ_sum_single (Multiplicative.toAdd y), ofAdd_sum]
  refine Subgroup.prod_mem _ fun j _ => ?_
  have := hall j (Multiplicative.toAdd y j)
  rwa [← Pi.single_smul', smul_eq_mul, mul_one] at this

end ReflF4

section F4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover

variable {K : Type} [Field K]

theorem range_chevTorus_eq_torusPow_of_prime [Finite K] {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    (chevTorus .F4 ζ hζ).range = TableBF4.torusPow K p := by
  have hdet : IsUnit ((Tag.F4.cartan.det : ℤ) : ZMod p) := by
    rw [det_cartan_F4, Int.cast_one]
    exact isUnit_one
  have hle : (chevTorus .F4 ζ hζ).range ≤ TableBF4.torusPow K p := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(torusCoordHom .F4 K (chevTorusExp .F4 ζ hζ x)).2, ?_⟩
    rw [← map_pow, pow_eq_one_of_zmod, map_one]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [TableBF4.card_torusPow hp hpq,
    ← Nat.card_congr (MonoidHom.ofInjective (chevTorus_injective hζo hζ hdet)).toEquiv,
    card_multiplicative_fin_zmod]
  rfl

theorem ggTorusReflElt_adjointF4 [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hT : GGF4ToralRankInput K p) :
    GGTorusReflElt p 4 (adjointGroup .F4 K) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := @TableBSymp.exists_orderOf_eq_of_dvd K _ _ p ⟨hp⟩ hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  intro E hE hr _
  obtain ⟨g, hg⟩ := hT E hE hr
  have hrange := range_chevTorus_eq_torusPow_of_prime hp hpq hζo hζ
  have hmemE : ∀ x, x ∈ E ↔ g * x * g⁻¹ ∈ (chevTorus .F4 ζ hζ).range := by
    intro x
    rw [hrange, ← hg]
    constructor
    · intro hx
      exact ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · rintro ⟨y, hy, hyx⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have : y = x := mul_left_cancel (mul_right_cancel hyx)
      exact this ▸ hy
  set e : Multiplicative (Fin Tag.F4.rank → ZMod p) →* adjointGroup .F4 K :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (chevTorus .F4 ζ hζ) with he
  have heapp : ∀ x, e x = g⁻¹ * chevTorus .F4 ζ hζ x * g := fun x => by
    rw [he, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  set n : Fin Tag.F4.rank → adjointGroup .F4 K := fun i =>
    g⁻¹ * ⟨weylElt .F4 K i 1, weylElt_mem_adjointGroup i 1⟩ * g with hn
  have hrefl : ∀ i v, n i * e (.ofAdd v) * (n i)⁻¹ =
      e (.ofAdd (v - cartanFunctional .F4 p i v • Pi.single i 1)) := by
    intro i v
    rw [heapp, heapp, ← weylElt_conj_chevTorus ζ hζ i v, hn]
    group
  have heE : e.range = E := by
    ext x
    rw [MonoidHom.mem_range, hmemE]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [heapp]; group⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [heapp, hy]; group⟩
  refine ⟨Tag.F4.rank, e, cartanFunctional .F4 p, n, heE, fun i => cartanFunctional_single i,
    hrefl, fun E' hE' hinv => ?_⟩
  have hinvF : ∀ i v, Multiplicative.ofAdd v ∈ E'.comap e →
      Multiplicative.ofAdd (v - cartanFunctional .F4 p i v • Pi.single i 1) ∈ E'.comap e := by
    intro i v hv
    rw [Subgroup.mem_comap, ← hrefl]
    exact hinv i _ hv
  have hEe : ∀ x ∈ E, ∃ y, e y = x := fun x hx => by
    rw [← heE] at hx
    exact hx
  rcases eq_bot_or_eq_top_of_reflF4 hp hp2 _ hinvF with hbot | htop
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hEe x (hE' hx)
    have hy : y ∈ E'.comap e := hx
    rw [hbot, Subgroup.mem_bot] at hy
    rw [hy, map_one]
    exact Subgroup.one_mem _
  · right
    refine le_antisymm hE' fun x hx => ?_
    obtain ⟨y, rfl⟩ := hEe x hx
    have hy : y ∈ E'.comap e := htop ▸ Subgroup.mem_top y
    exact hy

end F4

section Label


theorem ggTorusNbr_F4 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusNbr p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) :=
  ggTorusNbr_of_secElt hp (TableBF4.idImage_subset_inn K) (TableBF4.center_recipeGroup_eq_bot K)
    (ggTorusSecElt_of_mulEquiv (TableBF4.recipeEquiv K)
      (ggTorusSecElt_of_reflElt hp hp2 (ggTorusReflElt_adjointF4 hp hp2 hpq
        (ggF4ToralRankInput_of_three hp hp2 hpq fun _ => ggF4ThreeRankInput_holds))))

theorem recipeChevalleyF4_torusNbr {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ n) false Q) :
    LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusNbr p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 4, TableBF4.ggTorusLift_F4 hp hp2 hpq,
    ggTorusNbr_F4 hp hp2 hpq⟩

theorem largeEvenLabelAll_torusNbr_F4 {lab : LargeEvenLabel} (htag : lab.tag = .F4)
    (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  intro Q hQ
  exact recipeChevalleyF4_torusNbr hlab.1 hp hpn hQ

theorem ggTableBNbrInnerInputOn_F4 : GGTableBNbrInnerInputOn GGTableBF4Label :=
  ggTableBNbrInnerInputOn_of_labels fun _ _ hp hlab h =>
    largeEvenLabelAll_torusNbr_F4 h.1 hlab hp h.2

theorem ggTableBNbrInnerInput_of_rest_F4
    (h : GGTableBNbrInnerInputOn fun p lab => GGCorFourTwoRestLabel p lab ∧
      ¬ ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1) ∧
      ¬ ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) ∧
      ¬ GGTableBF4Label p lab) :
    GGTableBNbrInnerInput :=
  ((((ggTableBNbrInnerInputOn_typeA.or ggTableBNbrInnerInputOn_symplectic).or
      ggTableBNbrInnerInputOn_orthogonal).or ggTableBNbrInnerInputOn_F4).or h).of_cover
    fun p lab _ _ => by
      by_cases h1 : GGTypeALabel p lab
      · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
      · by_cases h2 : (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1
        · exact Or.inl (Or.inl (Or.inl (Or.inr h2)))
        · by_cases h3 : (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1
          · exact Or.inl (Or.inl (Or.inr h3))
          · by_cases h4 : GGTableBF4Label p lab
            · exact Or.inl (Or.inr h4)
            · exact Or.inr ⟨h1, h2, h3, h4⟩

end Label

end CFSG.StandardType

end
