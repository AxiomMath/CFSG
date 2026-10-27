module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofFlag
public import CFSG.RankThree.PartTwo.KFacts.K71G2
import CFSG.LieType.Chevalley.G2SolvableNormalTrivial
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

section Roots


theorem ncard_radical_compl (i : Fin Tag.G2.rank) :
    (parabolicRadicalRoots Tag.G2 ({i}ᶜ : Set (Fin Tag.G2.rank))).ncard = 5 := by
  have hset : parabolicRadicalRoots Tag.G2 ({i}ᶜ : Set (Fin Tag.G2.rank)) =
      {v | IsRoot Tag.G2 v ∧ (0 < height v ∧ v i ≠ 0)} := by
    ext v
    simp only [parabolicRadicalRoots, parabolicPosRoots, parabolicRoots, Set.mem_sdiff,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff, not_not]
    constructor
    · rintro ⟨⟨hr, hh⟩, hn⟩
      exact ⟨hr, hh, fun h0 => hn ⟨⟨hr, fun j hj => hj ▸ h0⟩, hr, hh⟩⟩
    · rintro ⟨hr, hh, hi⟩
      exact ⟨⟨hr, hh⟩, fun h => hi (h.1.2 i rfl)⟩
  rw [hset, CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and]
  clear hset
  revert i
  decide +kernel

theorem five_le_ncard_radical {J : Set (Fin Tag.G2.rank)} (hJ : J ≠ Set.univ) :
    5 ≤ (parabolicRadicalRoots Tag.G2 J).ncard := by
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  have hsub : parabolicRadicalRoots Tag.G2 ({i}ᶜ : Set (Fin Tag.G2.rank)) ⊆
      parabolicRadicalRoots Tag.G2 J := by
    rintro v ⟨hv, hn⟩
    refine ⟨hv, fun h => hn ⟨⟨h.1.1, fun j hj => h.1.2 j ?_⟩, h.2⟩⟩
    rw [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] at hj
    exact hj ▸ hi
  have hfin : (parabolicRadicalRoots Tag.G2 J).Finite := by
    refine (rootFinset Tag.G2).finite_toSet.subset ?_
    rintro v ⟨⟨hv, -⟩, -⟩
    exact mem_rootFinset.mpr hv
  rw [← ncard_radical_compl i]
  exact Set.ncard_le_ncard hsub hfin

end Roots

theorem false_of_dvd_ordG2 {q : ℕ} (hq : Even q) (hq1 : 1 ≤ q)
    (h : q ^ 7 ∣ CFSG.Open.ordG2 q) : False := by
  have hq0 : 0 < q ^ 6 := pow_pos (by omega) 6
  have hodd : Odd ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
    refine Odd.mul ?_ ?_
    · exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (Even.pow_of_ne_zero hq (by norm_num))
        odd_one
    · exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (Even.pow_of_ne_zero hq (by norm_num))
        odd_one
  rw [CFSG.Open.ordG2, mul_assoc, show q ^ 7 = q ^ 6 * q by ring] at h
  have h2 : q ∣ (q ^ 6 - 1) * (q ^ 2 - 1) := Nat.dvd_of_mul_dvd_mul_left hq0 h
  have h3 : 2 ∣ (q ^ 6 - 1) * (q ^ 2 - 1) := (even_iff_two_dvd.mp hq).trans h2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)

section Certs


theorem exists_conj_parabolic {τ : Tag} {K : Type} [Field K] [Finite K]
    {r : ℕ} [Fact r.Prime] [CharP K r] {P : Subgroup (adjointGroup τ K)} (hPtop : P ≠ ⊤)
    (S : Sylow r (adjointGroup τ K))
    (hSP : Subgroup.normalizer ((S : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) ≤ P) :
    ∃ (g : adjointGroup τ K) (J : Set (Fin τ.rank)), J ≠ Set.univ ∧
      (P.comap (MulAut.conj g).toMonoidHom).map (adjointGroup τ K).subtype =
        parabolicSubgroup τ K J := by
  classical
  have hfin : Finite (ModGL τ K) := finite_modGL
  have hUsyl := isPGroup_and_not_dvd_index r (posUnipotent_le_adjointGroup (τ := τ) (K := K))
    (card_posUnipotent (τ := τ) (K := K))
  set SU : Sylow r (adjointGroup τ K) := hUsyl.1.toSylow hUsyl.2 with hSU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup τ K) SU S
  have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  have hBN : borelGroup τ K ≤ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).1
      (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.1
  have hmem : ∀ z : adjointGroup τ K, z ∈ (S : Subgroup (adjointGroup τ K)) ↔
      g⁻¹ * z * g ∈ (SU : Subgroup (adjointGroup τ K)) := by
    intro z
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj_symm_apply]
  have hSUmem : ∀ z : adjointGroup τ K, z ∈ (SU : Subgroup (adjointGroup τ K)) ↔
      (z : ModGL τ K) ∈ posUnipotent τ K := fun z => Iff.rfl
  have hBP : ∀ b : adjointGroup τ K, (b : ModGL τ K) ∈ borelGroup τ K → g * b * g⁻¹ ∈ P := by
    intro b hb
    apply hSP
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmem, hmem]
    have e : g⁻¹ * (g * b * g⁻¹ * y * (g * b * g⁻¹)⁻¹) * g = b * (g⁻¹ * y * g) * b⁻¹ := by
      group
    rw [e, hSUmem, hSUmem]
    have := Subgroup.mem_normalizer_iff.1 (hBN hb) ((g⁻¹ * y * g : adjointGroup τ K) : ModGL τ K)
    simpa using this
  set P₀ : Subgroup (adjointGroup τ K) := P.comap (MulAut.conj g).toMonoidHom with hP₀
  have hP₀mem : ∀ y, y ∈ P₀ ↔ g * y * g⁻¹ ∈ P := fun y => by
    simp [hP₀, MulAut.conj_apply]
  have hP₀top : P₀ ≠ ⊤ := by
    intro h
    apply hPtop
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : g⁻¹ * y * g ∈ P₀ := h ▸ Subgroup.mem_top _
    rw [hP₀mem] at h1
    simpa [mul_assoc] using h1
  set A : Subgroup (ModGL τ K) := P₀.map (adjointGroup τ K).subtype with hA
  have hBA : borelGroup τ K ≤ A := fun b hb =>
    ⟨⟨b, borelGroup_le_adjointGroup' hb⟩, (hP₀mem _).2 (hBP _ hb), rfl⟩
  have hAC : A ≤ adjointGroup τ K := Subgroup.map_subtype_le _
  have hAJ := (borel_overgroup_classification τ K).1 A hBA hAC
  set J : Set (Fin τ.rank) := {i | weylElt τ K i 1 ∈ A} with hJ
  have hJne : J ≠ Set.univ := by
    intro hJu
    apply hP₀top
    have hAeq : A = adjointGroup τ K := by
      rw [hAJ, hJu]
      refine le_antisymm (parabolicSubgroup_le_adjointGroup τ K _) ?_
      rw [(borel_weyl_generation τ K).1]
      unfold parabolicSubgroup
      refine sup_le_sup_left (Subgroup.closure_mono ?_) _
      rintro _ ⟨i, rfl⟩
      exact ⟨i, Set.mem_univ i, rfl⟩
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : (y : ModGL τ K) ∈ A := by
      rw [hAeq]
      exact y.2
    obtain ⟨y', hy', hyy'⟩ := h1
    have h2 : y' = y := Subtype.ext hyy'
    rwa [← h2]
  exact ⟨g, J, hJne, hAJ⟩

theorem not_forall_fixed_mem_of_outer {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) {α : MulAut (adjointGroup Tag.G2 K)} (hα3 : α ^ 3 = 1)
    (hout : ¬ KFacts.IsInnerAut α) {Q : Subgroup (adjointGroup Tag.G2 K)}
    (hQ : IsProperParabolic Q) : ¬ ∀ z, α z = z → z ∈ Q := by
  intro hall
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by rw [hK2]; norm_num
  obtain ⟨σ, hσ3, k, hαk⟩ := KFacts.g2_order_three_field_descent hK3 hK4 hα3 hout
  set D : Subgroup (adjointGroup Tag.G2 K) := (KFacts.g2Incl σ).range with hD
  set Q₁ : Subgroup (adjointGroup Tag.G2 K) := Q.map (MulAut.conj k⁻¹).toMonoidHom with hQ₁def
  have hDQ₁ : D ≤ Q₁ := by
    intro x hx
    have hfx : KFacts.g2FieldHom K σ x = x := (KFacts.mem_range_g2Incl_iff hK2 σ x).mp hx
    have hfix : α (MulAut.conj k x) = MulAut.conj k x := by
      rw [hαk]
      change MulAut.conj k (KFacts.g2FieldHom K σ ((MulAut.conj k)⁻¹ (MulAut.conj k x))) = _
      rw [MulAut.inv_apply_self, hfx]
    refine ⟨MulAut.conj k x, hall _ hfix, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hQ₁ : IsProperParabolic Q₁ := isProperParabolic_map_equiv _ hQ
  obtain ⟨hQ₁top, T, hT⟩ := hQ₁
  obtain ⟨g, J, hJ, hA⟩ := exists_conj_parabolic hQ₁top T hT
  set φ : adjointGroup Tag.G2 (fixSubfield σ) →* ModGL Tag.G2 K :=
    (adjointGroup Tag.G2 K).subtype.comp
      ((MulAut.conj g⁻¹).toMonoidHom.comp (KFacts.g2Incl σ)) with hφ
  have hφinj : Function.Injective φ :=
    (adjointGroup Tag.G2 K).subtype_injective.comp
      ((MulAut.conj g⁻¹).injective.comp (KFacts.g2Incl_injective σ))
  set PJ := parabolicSubgroup Tag.G2 K J with hPJ
  have hφPJ : φ.range ≤ PJ := by
    rintro _ ⟨x, rfl⟩
    rw [← hA]
    refine ⟨(MulAut.conj g⁻¹) (KFacts.g2Incl σ x), ?_, rfl⟩
    change (MulAut.conj g) ((MulAut.conj g⁻¹) (KFacts.g2Incl σ x)) ∈ Q₁
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    exact hDQ₁ ⟨x, rfl⟩
  obtain ⟨hRP, -, -, -, -, -, -, -, -, -, -, -, hpg⟩ :=
    parabolic_root_radical_Levi_factors (τ := Tag.G2) (K := K) J
  obtain ⟨hRcard, hR2, -⟩ := hpg 2
  set R := parabolicRadical Tag.G2 K J with hR
  have hPJN : PJ ≤ Subgroup.normalizer (R : Set (ModGL Tag.G2 K)) :=
    parabolicSubgroup_le_normalizer_parabolicRadical J
  set N : Subgroup (adjointGroup Tag.G2 (fixSubfield σ)) := R.comap φ with hN
  have hNn : N.Normal := ⟨fun a ha b => by
    rw [hN, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hPJN (hφPJ ⟨b, rfl⟩)) (φ a)).mp ha⟩
  have hN2 : IsPGroup 2 N := hR2.comap_of_injective φ hφinj
  have hfin0 : Finite (ModGL Tag.G2 (fixSubfield σ)) := finite_modGL
  have hNsolv : Group.IsSolvable N := by
    have := hN2.isNilpotent
    infer_instance
  have hNbot : N = ⊥ := G2_solvable_normal_subgroups_trivial (fixSubfield σ) N hNsolv
  set R' : Subgroup PJ := R.subgroupOf PJ with hR'
  have hR'n : R'.Normal := by
    rw [hR']
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mpr hPJN
  set ψ : adjointGroup Tag.G2 (fixSubfield σ) →* PJ ⧸ R' :=
    (QuotientGroup.mk' R').comp (φ.codRestrict PJ fun x => hφPJ ⟨x, rfl⟩) with hψ
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (φ.codRestrict PJ fun x => hφPJ ⟨x, rfl⟩) x ∈ R' :=
      (QuotientGroup.eq_one_iff _).mp hx
    have h2 : x ∈ N := h1
    rw [hNbot, Subgroup.mem_bot] at h2
    exact h2
  have hdvd1 : Nat.card (adjointGroup Tag.G2 (fixSubfield σ)) ∣ Nat.card (PJ ⧸ R') :=
    Subgroup.card_dvd_of_injective ψ hψinj
  have hPJcard : Nat.card PJ = Nat.card (PJ ⧸ R') * Nat.card R :=
    by rw [R'.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRP).toEquiv]
  have hdvd2 : Nat.card (adjointGroup Tag.G2 (fixSubfield σ)) * Nat.card R ∣
      Nat.card (adjointGroup Tag.G2 K) := by
    refine (mul_dvd_mul_right hdvd1 _).trans ?_
    rw [← hPJcard]
    exact Subgroup.card_dvd_of_le (parabolicSubgroup_le_adjointGroup Tag.G2 K J)
  set q₀ := Nat.card (fixSubfield σ) with hq₀
  set q := Nat.card K with hq
  have hq₀q : q₀ ^ 3 = q := by
    have h := KFacts.card_fixSubfield_pow σ
    rwa [hσ3] at h
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hRcard,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2] at hdvd2
  have h6 : q ^ 2 ∣ CFSG.Open.ordG2 q₀ := by
    rw [← hq₀q, ← pow_mul, CFSG.Open.ordG2, mul_assoc]
    exact Dvd.intro _ rfl
  have h5 : q ^ 5 ∣ q ^ (parabolicRadicalRoots Tag.G2 J).ncard :=
    pow_dvd_pow q (five_le_ncard_radical hJ)
  have h7 : q ^ 7 ∣ CFSG.Open.ordG2 q := by
    refine dvd_trans ?_ hdvd2
    rw [show q ^ 7 = q ^ 2 * q ^ 5 by ring]
    exact mul_dvd_mul h6 h5
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hqn : q = 2 ^ (n : ℕ) := by rw [hq, Nat.card_eq_fintype_card, hn]
  have hqe : Even q := by
    rw [hqn]
    exact (Nat.even_pow' n.ne_zero).mpr even_two
  exact false_of_dvd_ordG2 hqe (by omega) h7

theorem not_forall_fixed_mem_of_outer_iso {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 2 ≤ n)
    (hY : Sec8.IsoGTwoEven Y n) {c : MulAut Y} (hc3 : c ^ 3 = 1)
    (hcI : c ∉ (MulAut.conj : Y →* MulAut Y).range) {P : Subgroup Y}
    (hP : IsProperParabolic P) : ¬ ∀ y : Y, c y = y → y ∈ P := by
  intro hfixP
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hY
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set α := MulAut.congr e c with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hc3, map_one]
  have hout : ¬ KFacts.IsInnerAut α := fun h => hcI ((KFacts.isInnerAut_congr e c).mp h)
  refine not_forall_fixed_mem_of_outer hK4 hα3 hout (isProperParabolic_map_equiv e hP) ?_
  intro z hz
  have hcz : c (e.symm z) = e.symm z := by
    have h1 : e (c (e.symm z)) = z := hz
    have h2 := congrArg e.symm h1
    rwa [MulEquiv.symm_apply_apply] at h2
  exact ⟨e.symm z, hfixP _ hcz, by simp⟩

end Certs

end CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof
