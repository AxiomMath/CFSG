module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsLieOrders
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitSp4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieD4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof (g2ShortSL2 g2LongSL2)

theorem le_of_isPerfect_of_commutators {G : Type*} [Group G] {H N K : Subgroup G}
    [hK : Group.IsPerfect K] (hKH : K ≤ H) (h : ∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ N) :
    K ≤ N := by
  intro k hk
  have h1 : (⟨k, hk⟩ : K) ∈ commutator K := by
    rw [Group.isPerfect_def.mp hK]
    exact Subgroup.mem_top _
  have h2 : k ∈ (commutator K).map K.subtype := ⟨⟨k, hk⟩, h1, rfl⟩
  rw [commutator_def, Subgroup.map_commutator] at h2
  have h3 : (⊤ : Subgroup K).map K.subtype ≤ H := by
    rintro _ ⟨x, -, rfl⟩
    exact hKH x.2
  have h4 := Subgroup.commutator_mono h3 h3 h2
  refine (Subgroup.commutator_le.mpr fun x hx y hy => ?_) h4
  rw [commutatorElement_def]
  exact h x hx y hy

theorem congr_conj_conj {G : Type*} [Group G] (g z : G) :
    MulAut.congr (MulAut.conj g) (MulAut.conj z) = MulAut.conj (g * z * g⁻¹) := by
  ext x
  show (MulAut.conj g) ((MulAut.conj z) ((MulAut.conj g).symm x)) = _
  rw [MulAut.conj_symm_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
  group

section G2


theorem isSimpleGroup_adjointGroup_of_perfect (τ : Tag) (k : Type) [Field k] [Finite k]
    (hperf : Group.IsPerfect (adjointGroup τ k)) : IsSimpleGroup (adjointGroup τ k) := by
  have hnc := (opposite_simple_root_noncommutativity τ k).2.2.1
  have : Nontrivial (adjointGroup τ k) := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨⟨a * b, b * a, hab⟩⟩
  have hZ : Subgroup.center (adjointGroup τ k) = ⊥ := center_adjointGroup_eq_bot
  refine IsSimpleGroup.mk fun M hM => ?_
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  · right
    have hnot : ¬ M ≤ Subgroup.center (adjointGroup τ k) := by
      rw [hZ]
      exact fun h => hbot (le_bot_iff.1 h)
    have hsolv := (noncentral_normal_solvable_quotient τ k M hnot).2.1
    by_contra htop
    have : Nontrivial (adjointGroup τ k ⧸ M) := by
      rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
      exact htop
    exact Group.IsPerfect.not_isSolvable _ hsolv

theorem CfgSEps.false_of_autFix_g2 {S : Type} [Group S] [Finite S] {A : Subgroup (MulAut S)}
    {σ : MulAut S} {K : Subgroup S} (hc : CfgSEps S A σ K) {k : Type} [Field k] [Finite k]
    {m : ℕ} (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m) (eC : autFix σ ≃* adjointGroup .G2 k) :
    False := by
  have hcardC : Nat.card (autFix σ) = (2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) := by
    rw [Nat.card_congr eC.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk,
      CFSG.Open.ordG2, mul_assoc]
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
  · have h1 := le_card_of_isTypeEpsCube (isTypeEpsCube_of_cfgSEps hc)
    have h2 : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card (autFix σ) :=
      (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hc.le_autFix)
    rw [hcardC] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    norm_num at this
    omega
  · have hk3 : 3 ≤ Nat.card k := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    haveI hCs : IsSimpleGroup (adjointGroup .G2 k) := isSimpleGroup_adjointGroup_of_perfect .G2 k
      (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card k hk3)
    have hna : ∃ a b : adjointGroup .G2 k, a * b ≠ b * a :=
      (opposite_simple_root_noncommutativity .G2 k).2.2.1
    obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna
    have hcube := hc.isTypeEpsCube_of_le hc.le_autFix le_rfl
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eC.symm hq) (center_eq_bot_of_mulEquiv eC hZ)
    exact not_isTypeEpsCube_of_card_g2_even hm hcardC hcube

theorem noCfgSEps_adjointG2 {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 2 ≤ n) : NoCfgSEps (adjointGroup Tag.G2 F) := by
  intro A α K hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcharP : CharP F 2 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
  have hchar : ringChar F = 2 := ringChar.eq F 2
  have hchar3 : ringChar F ≠ 3 := by rw [hchar]; norm_num
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hZT : Subgroup.center (adjointGroup Tag.G2 F) = ⊥ := center_adjointGroup_eq_bot
  have hα3 : α ^ 3 = 1 := hc.pow_three
  by_cases hin : IsInnerAut α
  · obtain ⟨z, rfl⟩ := hin
    have hinj := conj_injective_of_center_eq_bot hZT
    have hz3 : z ^ 3 = 1 := hinj (by rw [map_pow, hα3, map_one])
    have hz1 : z ≠ 1 := fun h => hc.ne_one (by rw [h, map_one])
    obtain ⟨g, hg⟩ := Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds F hchar3 h4 z hz3 hz1
    have hc' := hc.map (MulAut.conj g)
    rw [congr_conj_conj] at hc'
    set z' := g * z * g⁻¹ with hz'
    have hz'3 : z' ^ 3 = 1 := by rw [hz', conj_pow, hz3, mul_one, mul_inv_cancel]
    have hz'1 : z' ≠ 1 := fun h => hz1 (by
      have : g * z * g⁻¹ = g * 1 * g⁻¹ := by rw [← hz', h]; group
      simpa using this)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hz'o : orderOf z' = 3 := orderOf_eq_prime hz'3 hz'1
    have hfix : autFix (MulAut.conj z') = Subgroup.centralizer ({z'} : Set (adjointGroup Tag.G2 F)) :=
      RowV.autFix_conj_eq_centralizer z'
    haveI := hc'.isPerfect
    have hKC : K.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({z'} : Set (adjointGroup Tag.G2 F)) :=
      hfix ▸ hc'.le_autFix
    rcases hg with hS | hM
    ·
      obtain ⟨N, hNC, hcomm, hNq, x, hxN, hxc, hx1, hx3⟩ :=
        Sec11.KS11Lie7Proof.g2ThreeACent_holds F hchar3 h4 z' hS hz'3 hz'1
      have hKN := le_of_isPerfect_of_commutators hKC hcomm
      exact hc'.false_of_le_quasisimple_central hKN (hfix ▸ hNC) hNq hxN
        (fun n hn => (hxc n hn).symm) (orderOf_eq_prime hx3 hx1)
    ·
      obtain ⟨hcomm, -⟩ := Sec11.KS11Lie4Proof.g2ThreeBCent_holds F hchar3 h4 z' hM hz'3 hz'1
      have hKS := le_of_isPerfect_of_commutators hKC hcomm
      have hSC : g2ShortSL2 F ≤ autFix (MulAut.conj z') := by
        rw [hfix]
        intro s hs
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Sec11.KS11Lie4Proof.g2Short_commute_g2Long hs hM
      obtain ⟨ι⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := F)
      have hSq : IsQuasisimple (g2ShortSL2 F) :=
        Sec11.KS11Lie4Proof.isQuasisimple_g2ShortSL2 h4
      have hSZ : Subgroup.center (g2ShortSL2 F) = ⊥ :=
        center_eq_bot_of_mulEquiv ι.symm Sec19.Item19Res2Proof.center_sl2_eq_bot
      have hcube := hc'.isTypeEpsCube_of_le hKS hSC hSq hSZ
      refine not_isTypeEpsCube_of_card_sl2_even (n := n) (by omega) ?_ hcube
      rw [← Nat.card_congr ι.toEquiv, card_SL_two, hF]
  ·
    obtain ⟨φ, hφ, k, hαk⟩ := g2_order_three_field_descent hchar3 h4 hα3 hin
    obtain ⟨h3n, -⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (by omega) hF hφ
    obtain ⟨m, rfl⟩ := h3n
    have hcard : Nat.card (fixSubfield φ) = 2 ^ m := by
      have h := card_fixSubfield_pow φ
      rw [hφ, hF, show 2 ^ (3 * m) = (2 ^ m) ^ 3 by rw [← pow_mul, mul_comm]] at h
      exact Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) h
    have hfixeq : Sec4.autFix (g2FieldHom F φ) = (g2Incl φ).range := by
      ext h
      rw [Sec4.mem_autFix, mem_range_g2Incl_iff hchar φ]
    have eα : Sec4.autFix α ≃* adjointGroup Tag.G2 (fixSubfield φ) := by
      rw [hαk]
      exact ((autFixConjEquiv (MulAut.conj k) (g2FieldHom F φ)).trans
        (MulEquiv.subgroupCongr hfixeq)).trans
          (MonoidHom.ofInjective (g2Incl_injective φ)).symm
    exact hc.false_of_autFix_g2 hcard (by omega) eα

theorem rowSEpsOf_seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
      RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro q hq2 hq S _ _ hs hna ⟨e⟩
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hq).1
    simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
  obtain ⟨F, _, _, hF, ⟨eA⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hq hq2 e
  rw [hq2] at hF h3
  have hn : 2 ≤ q.exponent := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have eC : AdjointQuotient .G2 F ≃* adjointGroup .G2 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .G2) (K := F))).trans
      QuotientGroup.quotientBot
  haveI : Finite (adjointGroup .G2 F) := Finite.of_equiv _ (eA.trans eC).toEquiv
  exact (noCfgSEps_adjointG2 hF hn).of_mulEquiv (eA.trans eC)

end G2

end CFSG.RankThree.PartTwo.Sec4.RonanEps
