module

public import CFSG.RankThree.GF2n.Tim79aSec34Centre
public import CFSG.RankThree.GF2n.Tim79aCitedSp42
public import CFSG.RankThree.GF2n.Tim79a34TwStruct

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.LieType.Universal.Symplectic
open scoped commutatorElement
open Matrix

theorem tw22_spTrans_one {n : ℕ} (v : Fin n ⊕ Fin n → GaloisField 2 1) :
    spTrans v 1 = 1 + vecMulVec v (v ᵥ* (fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1))) := by
  simp [spTrans, spNil, spGram]

theorem card_statedSp_gf2f (f : ℕ) (hf : 1 ≤ f) (r : ℕ) :
    ∃ u : ℕ, Odd u ∧ Nat.card ↥(StatedSp r (GaloisField 2 f)) = 2 ^ (f * r ^ 2) * u := by
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨∏ j ∈ Finset.Icc 1 r, ((2 ^ f) ^ (2 * j) - 1), ?_, ?_⟩
  · refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hpos : 1 ≤ (2 ^ f) ^ (2 * j) := Nat.one_le_pow _ _ (by positivity)
    have heven : Even ((2 ^ f) ^ (2 * j)) := by
      rw [← pow_mul]
      exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩)
    exact Nat.Even.sub_odd hpos heven odd_one
  · rw [LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK, ← pow_mul]

theorem padicValNat_card_statedSp (f : ℕ) (hf : 1 ≤ f) (r : ℕ) :
    padicValNat 2 (Nat.card ↥(StatedSp r (GaloisField 2 f))) = f * r ^ 2 := by
  obtain ⟨u, hu, hcard⟩ := card_statedSp_gf2f f hf r
  have hu0 : u ≠ 0 := hu.pos.ne'
  have hnd : ¬ 2 ∣ u := fun h => (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)
  rw [hcard, padicValNat.mul (by positivity) hu0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hnd, add_zero]

theorem statedSp_rank_eq_of_iso {f n' n : ℕ} (hf : 1 ≤ f)
    (e : ↥(StatedSp n' (GaloisField 2 f)) ≃* ↥(StatedSp n (GaloisField 2 1))) :
    f * n' ^ 2 = n ^ 2 := by
  have h := Nat.card_congr e.toEquiv
  have h1 := padicValNat_card_statedSp f hf n'
  have h2 := padicValNat_card_statedSp 1 le_rfl n
  rw [h] at h1
  have h3 := h1.symm.trans h2
  simpa using h3

theorem rank_eq_of_eq {f n' n : ℕ} (hf : 1 ≤ f) (hn' : 2 ≤ n') (hn : n = 2 ∨ n = 3)
    (h : f * n' ^ 2 = n ^ 2) : n' = n ∧ f = 1 := by
  have h1 : n' ≤ 3 := by
    by_contra hcon
    push_neg at hcon
    have h4 : 4 ^ 2 ≤ n' ^ 2 := Nat.pow_le_pow_left hcon 2
    rcases hn with rfl | rfl <;> nlinarith
  rcases hn with rfl | rfl <;> interval_cases n' <;> simp at h <;> omega

theorem tw22_commutator_top {Γ : Type} [Group Γ] (φ : Γ →* ↥(StatedSp 3 (GaloisField 2 1)))
    (hsurj : Function.Surjective φ) (hker : φ.ker ≤ commutator Γ) : commutator Γ = ⊤ := by
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hperf := commutator_statedSp_eq_top (n := 3) (le_refl 3) hF2
  have hmap : (commutator Γ).map φ = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hsurj]
    exact hperf
  rw [eq_top_iff]
  intro g _
  have hg : φ g ∈ (commutator Γ).map φ := by rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp hg
  have hker' : c⁻¹ * g ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcg, inv_mul_cancel]
  have := Subgroup.mul_mem _ hc (hker hker')
  simpa using this

theorem sec34CentreSmall_transport {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}
    (hs : Sec3Setup M V Q P H) (h3 : Sec23Three V H) {n : ℕ} (hn : n = 2 ∨ n = 3)
    (e : ↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H) :
    ∃ φ₀ : Xbar V H →* ↥(StatedSp n (GaloisField 2 1)), Function.Surjective φ₀ ∧
      φ₀.ker = Subgroup.center (Xbar V H) ∧
      ∀ v : Fin n ⊕ Fin n → GaloisField 2 1, v ≠ 0 →
        ∃ d ∈ Dy V H, SpExtras.mat n (GaloisField 2 1) (φ₀ d) = spTrans v 1 := by
  obtain ⟨f, hf, hfq, hT⟩ := id h3
  obtain ⟨n', Φ, a, T, hn', hΦ, ha, hTa, hA⟩ :=
    exists_isTransGroup_of_transvConclusionSp_two hf hT (VZ_mem_rootClassZ V H)
  have hrank : f * n' ^ 2 = n ^ 2 :=
    statedSp_rank_eq_of_iso hf ((MulEquiv.ofBijective Φ hΦ).trans e.symm)
  obtain ⟨rfl, rfl⟩ := rank_eq_of_eq hf hn' hn hrank
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : Xbar V H →* StatedSp n' (GaloisField 2 1),
      ∀ x, φ₀ x = (MulEquiv.ofBijective Φ hΦ).symm (projZ V H x) :=
    ⟨(MulEquiv.ofBijective Φ hΦ).symm.toMonoidHom.comp (projZ V H), fun _ => rfl⟩
  have hkey : ∀ t : StatedSp n' (GaloisField 2 1),
      (MulEquiv.ofBijective Φ hΦ).symm (Φ t) = t := fun t =>
    (MulEquiv.ofBijective Φ hΦ).symm_apply_eq.2 rfl
  have hsurj : Function.Surjective φ₀ := by
    intro g
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Xbar V H)) (Φ g)
    have hy' : projZ V H y = Φ g := hy
    exact ⟨y, by rw [hφ₀, hy', hkey]⟩
  have hker : φ₀.ker = Subgroup.center (Xbar V H) := by
    ext x
    rw [MonoidHom.mem_ker, hφ₀, MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨dV, hdVV, hdVD, hdVne⟩ := (hs.setup.mc.toMinCex).exists_vy_mem_Dy hs.setup.data
  have hdVne' : projZ V H dV ≠ 1 := hdVne
  have hmemVZ : projZ V H dV ∈ VZ V H := Subgroup.mem_map_of_mem (projZ V H) hdVV
  rw [hA] at hmemVZ
  obtain ⟨t, htT, ht⟩ := Subgroup.mem_map.1 hmemVZ
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hdVne' (by rw [← ht, map_one])
  have hdVmat : SpExtras.mat n' (GaloisField 2 1) (φ₀ dV) = spTrans a 1 := by
    rw [hφ₀, ← ht, hkey]
    exact tw_mat_eq_spTrans_one hF2 hTa htT ht1
  have hDc : ∀ x ∈ Dy V H, ∀ g : Xbar V H, g * x * g⁻¹ ∈ Dy V H := by
    obtain ⟨d₀, hD⟩ := hs.setup.data.isClass
    intro x hx g
    rw [hD] at hx ⊢
    exact (show IsConj d₀ x from hx).trans (isConj_iff.2 ⟨g, rfl⟩)
  exact ⟨φ₀, hsurj, hker, tw_exists_mem_of_transvection hsurj hDc hdVD ha hdVmat⟩

theorem sec34CentreSmall_three (hGrE : GriessSpMultiplierExceptionStatement)
    (hS : Sp62CoverLiftStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
      Sec23Three V H → CentreClause V H →
      Nonempty (StatedSp 3 (GaloisField 2 1) ≃* XbarZ V H) →
      Subgroup.center (Xbar V H) = ⊥ := by
  intro G _ _ M V Q P H hs h3 hcc ⟨e⟩
  obtain ⟨φ₀, hsurj, hker, hD⟩ := sec34CentreSmall_transport hs h3 (Or.inr rfl) e
  obtain ⟨d, hdD, hdmat⟩ := hD (Pi.single (Sum.inl 0) 1) (by
    intro h
    have := congrFun h (Sum.inl 0)
    simp at this)
  by_contra hne
  have hZle : φ₀.ker ≤ Subgroup.center (Xbar V H) := hker.le
  have hZcomm : φ₀.ker ≤ commutator (Xbar V H) := by
    rw [hker]
    exact hcc
  have hcard_le : Nat.card φ₀.ker ≤ 2 :=
    (hGrE 3 1 (Or.inr (Or.inr rfl))).1 (Xbar V H) φ₀ hsurj hZle hZcomm
  have hgt : 1 < Nat.card φ₀.ker := (Subgroup.one_lt_card_iff_ne_bot _).2 (by rw [hker]; exact hne)
  have hcard : Nat.card φ₀.ker = 2 := by omega
  have hperf : commutator (Xbar V H) = ⊤ := tw22_commutator_top φ₀ hsurj hZcomm
  have hcond := hdmat.trans (tw22_spTrans_one _)
  have h4 : orderOf d = 4 :=
    (hS (Xbar V H) φ₀ hsurj hZle hcard hperf d d _ _ (by
      intro h
      have := congrFun h (Sum.inl 0)
      simp at this) (by
      intro h
      have := congrFun h (Sum.inl 0)
      simp at this) hcond hcond).1
  have h2 : orderOf d = 2 := hs.setup.data.root.1 d hdD
  omega

theorem sec34CentreSmall_two (hGrE : GriessSpMultiplierExceptionStatement)
    (hS : Sp42CoverLiftStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
      Sec23Three V H → CentreClause V H →
      Nonempty (StatedSp 2 (GaloisField 2 1) ≃* XbarZ V H) →
      Subgroup.center (Xbar V H) = ⊥ := by
  intro G _ _ M V Q P H hs h3 hcc ⟨e⟩
  obtain ⟨φ₀, hsurj, hker, hD⟩ := sec34CentreSmall_transport hs h3 (Or.inl rfl) e
  have hv : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → GaloisField 2 1) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl 0)
    simp at this
  have hw : (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → GaloisField 2 1) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl 1)
    simp at this
  have hvw : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → GaloisField 2 1) ≠
      Pi.single (Sum.inl 1) 1 := by
    intro h
    have := congrFun h (Sum.inl 0)
    simp at this
  have hB : spForm (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → GaloisField 2 1)
      (Pi.single (Sum.inl 1) 1) = 0 := by
    simp [spForm, spGram, dotProduct, Matrix.mulVec, Pi.single_apply, fromBlocks]
  obtain ⟨d, hdD, hdmat⟩ := hD _ hv
  obtain ⟨e', heD, hemat⟩ := hD _ hw
  by_contra hne
  have hZle : φ₀.ker ≤ Subgroup.center (Xbar V H) := hker.le
  have hZcomm : φ₀.ker ≤ commutator (Xbar V H) := by
    rw [hker]
    exact hcc
  have hcard_le : Nat.card φ₀.ker ≤ 2 :=
    (hGrE 2 1 (Or.inr (Or.inl rfl))).1 (Xbar V H) φ₀ hsurj hZle hZcomm
  have hgt : 1 < Nat.card φ₀.ker := (Subgroup.one_lt_card_iff_ne_bot _).2 (by rw [hker]; exact hne)
  have hcard : Nat.card φ₀.ker = 2 := by omega
  have hdd : d * d = 1 := by
    have h := pow_orderOf_eq_one d
    rw [hs.setup.data.root.1 d hdD] at h
    rwa [sq] at h
  have hee : e' * e' = 1 := by
    have h := pow_orderOf_eq_one e'
    rw [hs.setup.data.root.1 e' heD] at h
    rwa [sq] at h
  have hcd := hdmat.trans (tw22_spTrans_one _)
  have hce := hemat.trans (tw22_spTrans_one _)
  have hnc : d * e' ≠ e' * d := hS (Xbar V H) φ₀ hsurj hZle hZcomm hcard d e' _ _ hv hw hvw hB
    hcd hce hdd hee
  have hcommute : Commute (φ₀ d) (φ₀ e') := by
    show φ₀ d * φ₀ e' = φ₀ e' * φ₀ d
    apply SpExtras.mat_injective
    simp only [map_mul]
    rw [hdmat, hemat]
    exact CFSG.Timmesfeld.ARS.CaseM.spTrans_commute_of_spForm_eq_zero hB 1 1
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hei : e'⁻¹ = e' := inv_eq_of_mul_eq_one_right hee
  have hcom : ⁅d, e'⁆ = (d * e') * (d * e') := by
    rw [commutatorElement_def, hdi, hei]
    simp only [mul_assoc]
  have hker_mem : ⁅d, e'⁆ ∈ φ₀.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr hcommute
  have hne1 : ⁅d, e'⁆ ≠ 1 := fun h => hnc (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hsq : ⁅d, e'⁆ ^ 2 = 1 := by
    have h := pow_card_eq_one' (G := ↥φ₀.ker) (x := ⟨⁅d, e'⁆, hker_mem⟩)
    rw [hcard] at h
    simpa using congrArg Subtype.val h
  have hnot : ¬ (d * e') ^ (2 ^ 1) = 1 := by
    rw [pow_one, sq, ← hcom]
    exact hne1
  have hfin : (d * e') ^ (2 ^ (1 + 1)) = 1 := by
    have h2 : (d * e') ^ 2 = ⁅d, e'⁆ := by rw [sq, hcom]
    rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h2]
    exact hsq
  have h4 : orderOf (d * e') = 4 := (orderOf_eq_prime_pow hnot hfin).trans (by norm_num)
  exact hs.setup.degenerate d hdD e' heD h4

theorem sec34CentreSmallStatement_holds (hGrE : GriessSpMultiplierExceptionStatement)
    (hS3 : Sp62CoverLiftStatement) (hS2 : Sp42CoverLiftStatement) :
    Sec34CentreSmallStatement := by
  intro G _ _ M V Q P H hs h3 hcc n hn e
  rcases hn with rfl | rfl
  · exact sec34CentreSmall_two hGrE hS2 G M V Q P H hs h3 hcc e
  · exact sec34CentreSmall_three hGrE hS3 G M V Q P H hs h3 hcc e

end CFSG.RankThree.GF2n.Tim79a
