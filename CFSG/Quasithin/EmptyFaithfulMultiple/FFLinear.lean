module

public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearGroup
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearWedge
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearSp4
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearG2
public import CFSG.Quasithin.EmptyFaithfulMultiple.Facts15420Proof
public import CFSG.Quasithin.Background.G64ExtSq

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open (pCoreOf quasithinGenFitting quasithinG2)
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace FFL

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (h : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, h])

theorem one_le_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (h : Nat.card K = 2 ^ n) :
    1 ≤ n := by
  by_contra h0
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [h, show n = 0 by omega, pow_zero] at h1
  exact lt_irrefl _ h1

variable {V : Type} [CommGroup V] [Finite V]

theorem fix_of_nat (hV : ∀ v : V, v * v = 1) {L S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {π : ↥(StatedSL n K) →* ↥L}
    (hπ : (FFModel.nat (StatedSL n K)).RealizesVia L (commV L) (fixV L ⊓ commV L) π) :
    ∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v := by
  have hab : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  exact exists_fix_of_realizesVia hV hS hπ (isPGroup_unitri (by omega))
    (slGamma_pow_three hab) (fun h => slGamma_ne_one hab (hinj (h.trans (map_one π).symm)))
    (fixesFixed_nat hab (by simp) (by simp))

theorem fix_of_sp4 (hV : ∀ v : V, v * v = 1) {L S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) {K : Type} [Field K] [CharP K 2] {π : ↥(StatedSp 2 K) →* ↥L}
    (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia L (commV L) (fixV L ⊓ commV L) π) :
    ∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v := by
  have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  exact exists_fix_of_realizesVia hV hS hπ isPGroup_zpowers_spUElt spGamma_pow_three
    (fun h => spGamma_ne_one (hinj (h.trans (map_one π).symm))) fixesFixed_sp4

theorem fix_of_g2 (hV : ∀ v : V, v * v = 1) {L S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) {K : Type} [Field K] [CharP K 2] {π : ↥(quasithinG2 K) →* ↥L}
    (hπ : (FFModel.zornQ (quasithinG2 K)).RealizesVia L (commV L) (fixV L ⊓ commV L) π) :
    ∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v := by
  obtain ⟨m, hm, hγ⟩ := g2γ_moves (K := K)
  exact exists_fix_of_realizesVia hV hS hπ isPGroup_zpowers_g2u g2γ_pow_three
    (ne_one_of_realizesVia hπ hm hγ) fixesFixed_g2

theorem fix_of_extSq5 (hV : ∀ v : V, v * v = 1) {L S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) {π : ↥(StatedSL 5 (ZMod 2)) →* ↥L}
    (hπ : (FFModel.extSq (ZMod 2) 5).RealizesVia L (commV L) (fixV L ⊓ commV L) π) :
    ∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v := by
  have hinj := G64.RealizesVia.injective_of_faithful' (G64.extSq_faithful (by norm_num)) hπ
  exact exists_fix_of_realizesVia hV hS hπ (isPGroup_unitri (by norm_num))
    (slGamma_pow_three _) (fun h => slGamma_ne_one _ (hinj (h.trans (map_one π).symm)))
    fixesFixed_extSq5

theorem fix_of_extSq4 (hV : ∀ v : V, v * v = 1) {L S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) {π : ↥(StatedSL 4 (ZMod 2)) →* ↥L}
    (hπ : (FFModel.extSq (ZMod 2) 4).RealizesVia L (commV L) (fixV L ⊓ commV L) π) :
    ∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v := by
  have hinj := G64.RealizesVia.injective_of_faithful' (G64.extSq_faithful (by norm_num)) hπ
  exact exists_fix_of_realizesVia hV hS hπ (isPGroup_unitri (by norm_num))
    (slGamma_pow_three _) (fun h => slGamma_ne_one _ (hinj (h.trans (map_one π).symm)))
    fixesFixed_extSq4

omit [Finite V] in
theorem card_eq_of_realizesVia {D : FFModel} (hD : D.Faithful) {L : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : D.Gam →* ↥L} (hπ : D.RealizesVia L U Z π) :
    Nat.card ↥L = Nat.card D.Gam :=
  (Nat.card_congr (MulEquiv.ofBijective π
    ⟨G64.RealizesVia.injective_of_faithful' hD hπ, hπ.1⟩).toEquiv).symm

theorem card_alt {n : ℕ} (hn : 2 ≤ n) :
    Nat.card ↥(alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem fix_of_b42
    (hV : ∀ v : V, v * v = 1) {L S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) (hcard : IsFFLOrder (Nat.card L)) (hZ : Subgroup.center ↥L = ⊥)
    (hB : B42ModulePair L (commV L) (fixV L ⊓ commV L)) :
    ∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v := by
  rcases hB with ⟨m, K, _, _, hK, π, hπ⟩ | ⟨m, K, _, _, hK, π, hπ⟩ | ⟨m, K, _, _, hK, π, hπ⟩ |
    ⟨m, K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨α, π, hπ⟩ |
    ⟨K, _, _, Γ₀, -, -, hhat, -, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ |
    ⟨π, hπ⟩ | ⟨π, hπ⟩
  ·
    exfalso
    have : Fintype K := Fintype.ofFinite K
    have h1 := card_eq_of_realizesVia (FFModel.nat_faithful _) hπ
    change Nat.card ↥L = Nat.card ↥(StatedSL 2 K) at h1
    rw [card_statedSL_two, ← Nat.card_eq_fintype_card, hK] at h1
    exact hcard.ne_sl2 (one_le_of_card hK) h1
  · have := charP_two_of_card hK
    exact fix_of_nat hV hS le_rfl hπ
  · have := charP_two_of_card hK
    exact fix_of_sp4 hV hS hπ
  · have := charP_two_of_card hK
    exact fix_of_g2 hV hS hπ
  ·
    exfalso
    have := charP_two_of_card hK
    have hle : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
      Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
          (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    have h1 := card_eq_of_realizesVia (zornQ_faithful hle) hπ
    change Nat.card ↥L = Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ at h1
    rw [card_commutator_quasithinG2 (by simpa using hK)] at h1
    exact hcard.ne_small (by omega)
  · exfalso
    have h1 := card_eq_of_realizesVia (G64.altDn_faithful le_rfl) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 5)) at h1
    rw [card_alt (by norm_num)] at h1
    exact hcard.ne_small (by rw [h1]; decide)
  · exfalso
    have h1 := card_eq_of_realizesVia (G64.altDn_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 6)) at h1
    rw [card_alt (by norm_num)] at h1
    exact hcard.ne_small (by rw [h1]; decide)
  · exfalso
    have h1 := card_eq_of_realizesVia (G64.altDn_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 7)) at h1
    rw [card_alt (by norm_num)] at h1
    exact hcard.ne_small (by rw [h1]; decide)
  · exfalso
    have h1 := card_eq_of_realizesVia (G64.a7Four_faithful α) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 7)) at h1
    rw [card_alt (by norm_num)] at h1
    exact hcard.ne_small (by rw [h1]; decide)
  ·
    exfalso
    have e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π
      ⟨G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ, hπ.1⟩
    have h1 := Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rw [hhat.2.1, hZ, Subgroup.card_bot] at h1
    omega
  · have := charP_two_of_card hK
    exact fix_of_nat hV hS (by norm_num) hπ
  · have := charP_two_of_card hK
    exact fix_of_nat hV hS (by norm_num) hπ
  · exact fix_of_extSq4 hV hS hπ
  · exact fix_of_extSq5 hV hS hπ

omit [Finite V] in
theorem fix_nat_summand {L : Subgroup (MulAut V)} {n : ℕ} {K : Type} [Field K]
    {π : ↥(StatedSL n K) →* ↥L} {I : Subgroup V}
    (hπ : (FFModel.nat (StatedSL n K)).RealizesVia L I ⊥ π) {a b : Fin n} (hab : a ≠ b)
    (ha : (a : ℕ) ≠ 0) (hb : (b : ℕ) ≠ 0) :
    ∀ v ∈ I, (∀ t ∈ (L.subtype.comp π) '' (unitri n K : Set ↥(StatedSL n K)), t v = v) →
      (L.subtype.comp π) (slGamma hab) v = v := by
  intro v hv hT
  have h := mul_inv_mem_of_fixesFixed hπ (fixesFixed_nat hab ha hb) hv
    fun τ hτ => hT _ ⟨τ, hτ, rfl⟩
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h
  exact h

omit [Finite V] in
theorem fix_dualNat_summand {L : Subgroup (MulAut V)} {n : ℕ} {K : Type} [Field K]
    {π : ↥(StatedSL n K) →* ↥L} {I : Subgroup V}
    (hπ : (FFModel.dualNat (StatedSL n K)).RealizesVia L I ⊥ π) {a b : Fin n} (hab : a ≠ b)
    (ha : (a : ℕ) + 1 < n) (hb : (b : ℕ) + 1 < n) :
    ∀ v ∈ I, (∀ t ∈ (L.subtype.comp π) '' (unitri n K : Set ↥(StatedSL n K)), t v = v) →
      (L.subtype.comp π) (slGamma hab) v = v := by
  intro v hv hT
  have h := mul_inv_mem_of_fixesFixed hπ (fixesFixed_dualNat hab ha hb) hv
    fun τ hτ => hT _ ⟨τ, hτ, rfl⟩
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h
  exact h

theorem fix_of_sum {L S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S L) {n : ℕ} (hn : 3 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(StatedSL n K) →* ↥L}
    (hinj : Function.Injective π)
    (hfix : ∀ v ∈ commV L,
      (∀ t ∈ (L.subtype.comp π) '' (unitri n K : Set ↥(StatedSL n K)), t v = v) →
      (L.subtype.comp π) (slGamma (a := (⟨1, by omega⟩ : Fin n)) (b := ⟨2, by omega⟩)
        (by simp [Fin.ext_iff])) v = v) :
    ∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v := by
  have hψ : Function.Injective (L.subtype.comp π) := Subtype.val_injective.comp hinj
  refine exists_fix_of_hom hS (L.subtype.comp π) (fun x => (π x).2) (isPGroup_unitri (by omega))
    ((orderOf_injective _ hψ _).trans (orderOf_slGamma _)) fun v hv hT => hfix v hv ?_
  rintro _ ⟨τ, hτ, rfl⟩
  exact hT τ hτ

theorem fix_of_b51
    (hV : ∀ v : V, v * v = 1) {G L S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) (hcard : IsFFLOrder (Nat.card L)) (hZ : Subgroup.center ↥L = ⊥)
    (h : B51Part1 G L) : ∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v := by
  obtain ⟨-, h⟩ := h
  rcases h with ⟨-, hB, -⟩ | ⟨-, n, K, _, _, hK, I, π, hind, hsup, hreal, -, -⟩ |
    ⟨n, -, hn, π, U₁, U₂, ⟨hU, hU0⟩, h₁, h₂⟩ | ⟨-, n, hn, k, hk1, -, I, π, -, hind, hsup, hreal⟩
  · exact fix_of_b42 hV hS hcard hZ hB
  ·
    have := charP_two_of_card hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) (hreal 0)
    refine fix_of_sum hS le_rfl hinj fun v hv hT => ?_
    rw [← hsup] at hv
    refine fix_of_iSup I (fun i => disjoint_iff.mp (hind i)) (fun t ht i w hw => ?_)
      (fun i => fix_nat_summand (hreal i) _ (by simp) (by simp)) v hv hT
    obtain ⟨τ, -, rfl⟩ := ht
    exact (hreal i).2.2.2.1 (π τ) w hw
  ·
    have hn4 : 4 ≤ n := by omega
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) h₁
    refine fix_of_sum hS (by omega) hinj fun v hv hT => ?_
    rw [← hU] at hv
    refine fix_of_sup hU0 (fun t ht w hw => ?_) (fun t ht w hw => ?_)
      (fix_nat_summand h₁ _ (by simp) (by simp))
      (fix_dualNat_summand h₂ _ (by simp; omega) (by simp; omega)) v hv hT
    · obtain ⟨τ, -, rfl⟩ := ht
      exact h₁.2.2.2.1 (π τ) w hw
    · obtain ⟨τ, -, rfl⟩ := ht
      exact h₂.2.2.2.1 (π τ) w hw
  ·
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _)
      (hreal ⟨0, hk1⟩)
    refine fix_of_sum hS (by omega) hinj fun v hv hT => ?_
    rw [← hsup, bot_sup_eq] at hv
    refine fix_of_iSup I (fun i => by simpa using hind i) (fun t ht i w hw => ?_)
      (fun i => fix_nat_summand (hreal i) _ (by simp) (by simp)) v hv hT
    obtain ⟨τ, -, rfl⟩ := ht
    exact (hreal i).2.2.2.1 (π τ) w hw

end FFL

open FFL

theorem ffLinear_of_b56
    (h56 : AsB56) :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
    ∀ Γ L : Subgroup (MulAut V), G64.IsQuotientOfSQTKCat ↥Γ → L ≤ Γ →
      (L.subgroupOf Γ).Normal →
      Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) = ⊥ →
      ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
          Nonempty (↥L ≃* ↥(StatedSL 3 F))) ∨
        Nonempty (↥L ≃* ↥(StatedSL 4 (ZMod 2))) ∨ Nonempty (↥L ≃* ↥(StatedSL 5 (ZMod 2)))) →
      (∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) →
      ∀ S : Subgroup (MulAut V), IsSylowTwoOf S L →
        ∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v := by
  intro V _ _ hV Γ L hQ hLΓ hn hC htype hoff S hS
  have htype' : IsFFLType ↥L := htype
  have hq := htype'.isQuasisimple
  have hcard := htype'.card
  have hZ := center_eq_bot hLΓ hC
  obtain ⟨hLG, hB53⟩ := b53Hyp_ffJ hQ hq hZ hC hLΓ hn hoff
  have hL1 : L ≠ ⊥ := by
    intro h
    have : Nontrivial ↥L := nontrivial_of_isQuasisimple hq
    rw [h] at this
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
  have hG1 : ffJ Γ ≠ ⊥ := fun h => hL1 (le_bot_iff.mp (h ▸ hLG))
  have hΓL := le_normalizer_of_normal hLΓ hn
  have hdich : ∀ H ≤ ffJ Γ, ffJ Γ ≤ Subgroup.normalizer (H : Set (MulAut V)) →
      L ≤ H ∨ H = ⊥ := fun H hH hGH =>
    le_or_eq_bot hq hZ hC (hH.trans (ffJ_le Γ)) (hLG.trans hGH) ((hH.trans (ffJ_le Γ)).trans hΓL)
  have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => by rw [sq]; exact hV v
  rcases h56 V hV2 (ffJ Γ) hG1 hB53 with ⟨hqF, ⟨h1, -⟩, -⟩ | h2 | h3 | h4 | h5
  ·
    have hFL : quasithinGenFitting (ffJ Γ) = L := by
      have hF := quasithinGenFitting_le (ffJ Γ)
      have hGF : ffJ Γ ≤ Subgroup.normalizer (quasithinGenFitting (ffJ Γ) : Set (MulAut V)) :=
        Subgroup.le_normalizer.trans (normalizer_le_normalizer_quasithinGenFitting _)
      rcases hdich _ hF hGF with hLF | hb
      · exact eq_of_isQuasisimple hq hqF hLF ((hF.trans (ffJ_le Γ)).trans hΓL)
      · exfalso
        have := nontrivial_of_isQuasisimple hqF
        rw [hb] at this
        exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
    rw [hFL] at h1
    exact fix_of_b51 hV hS hcard hZ h1
  · exact (false_of_case2 hLG hcard.six_lt h2).elim
  · exact (false_of_case3 hL1 hdich h3).elim
  · exact (false_of_case4 hcard.six_lt hdich h4).elim
  · exact (false_of_case5 hL1 hdich h5).elim

theorem facts15420_holds
    (h56 : AsB56) (hHe : HeAutCentralizer) : Facts15420 :=
  facts15420_of_rest ⟨ffLinear_of_b56 h56, hHe⟩

end CFSG.Quasithin.EmptyFaithfulMultiple
