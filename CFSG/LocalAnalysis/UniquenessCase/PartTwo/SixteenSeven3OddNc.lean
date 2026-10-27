module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Ctx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def OddNcCore (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Prop :=
  ∃ p ∈ D.sig, ∃ X : Subgroup (MulAut (Vtil V₀ V hV)),
    X ≤ oddBar D.M V₀ V hV ∧ IsPGroup p X ∧ ¬ IsCyclic X

theorem s16c167_oddNcCore_of_fstarBar (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {p n : ℕ} (hp : p ∈ D.sig) (hn : 2 ≤ n)
    (h : IsElemAbelianOfRank p n ↥(fstarBar D.M V₀ V hV)) : OddNcCore D V₀ V hV := by
  have hpp : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨e⟩ := h
  have hcard : Nat.card ↥(fstarBar D.M V₀ V hV) = p ^ n := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card]
  refine ⟨p, hp, fstarBar D.M V₀ V hV, ?_, IsPGroup.of_card hcard, ?_⟩
  · refine le_sSup ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · show (Subgroup.comap (Mbar D.M V₀ V hV).subtype
        ((genFittingFStar ↥(Mbar D.M V₀ V hV)).map (Mbar D.M V₀ V hV).subtype)).Normal
      rw [Subgroup.comap_map_eq_self_of_injective (Mbar D.M V₀ V hV).subtype_injective]
      exact CFSG.ComponentClassification.GeneralizedFitting.normal _
    · rw [hcard]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hpp).2 (Ne.symm hp2))
  · intro hc
    have hc' : IsCyclic (Multiplicative (Fin n → ZMod p)) := e.isCyclic.1 hc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Multiplicative (Fin n → ZMod p))
    have hord : orderOf g = p ^ n := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
      simp
    have hg1 : g ^ p = 1 := by
      have h0 : p • (Multiplicative.toAdd g) = 0 := by
        funext i
        simp [nsmul_eq_mul]
      calc g ^ p = Multiplicative.ofAdd (p • Multiplicative.toAdd g) := rfl
        _ = 1 := by rw [h0]; rfl
    have hdvd : p ^ n ∣ p := hord ▸ orderOf_dvd_of_pow_eq_one hg1
    have hle : p ^ n ≤ p := Nat.le_of_dvd hpp.pos hdvd
    have h2 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hpp.pos hn
    have h3 := hpp.two_le
    nlinarith

theorem s16c167_oddNcCore_of_case168_8 (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : Case168_8 D V₀ V hV) : OddNcCore D V₀ V hV := by
  obtain ⟨h1, -, h3⟩ := h
  exact s16c167_oddNcCore_of_fstarBar D hV (p := 3) (by rw [h3]; exact Set.mem_singleton 3)
    le_rfl h1

theorem s16c167_oddNcCore_of_case168_10 (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {L : Subgroup G} (h : Case168_10 D V₀ V hV L) : OddNcCore D V₀ V hV := by
  obtain ⟨p, -, -, -, -, hsig, hF⟩ := h
  exact s16c167_oddNcCore_of_fstarBar D hV (p := p) (n := 3)
    (by rw [hsig]; exact Set.mem_singleton p) (by norm_num) hF

theorem s16c167_comm_wClos_of_forall {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hA : ∀ A ∈ E3.gammaSet V D.k D.T,
      ⁅oddBar D.M V₀ V h.isElemAbelian, barSub V₀ V h.isElemAbelian A⁆ = ⊥) :
    ⁅oddBar D.M V₀ V h.isElemAbelian,
      barSub V₀ V h.isElemAbelian (E3.wClos V D.k D.T)⁆ = ⊥ := by
  have hP := h.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  set Cbar : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)) :=
    Subgroup.centralizer
      (oddBar D.M V₀ V h.isElemAbelian : Set (MulAut (Vtil V₀ V h.isElemAbelian))) with hCbar
  have hle : E3.wClos V D.k D.T ≤ preBarSub D.M V₀ V h.isElemAbelian Cbar := by
    refine E3.wClos_le_of_forall fun A hAΓ g hg => ?_
    have hgM : g ∈ D.M := D.sylowM.le (hAΓ.1 hg)
    have hgst : g ∈ stabTil V₀ V := hMst hgM
    refine (mem_preBarSub _ _ _ _ _).2 ⟨hgM, hgst, ?_⟩
    have hmem := actTil_mem_barSub V₀ V h.isElemAbelian hg hgst
    rw [hCbar, Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : ⁅z, actTil V₀ V h.isElemAbelian ⟨g, hgst⟩⁆ ∈
        ⁅oddBar D.M V₀ V h.isElemAbelian, barSub V₀ V h.isElemAbelian A⁆ :=
      Subgroup.commutator_mem_commutator hz hmem
    rw [hA A hAΓ, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hb : barSub V₀ V h.isElemAbelian (E3.wClos V D.k D.T) ≤ Cbar := by
    have := barSub_mono V₀ V h.isElemAbelian hle
    rw [barSub_preBarSub] at this
    exact this.trans inf_le_left
  refine le_bot_iff.1 ?_
  rw [Subgroup.commutator_le]
  intro z hz y hy
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 (hb hy) z hz)

theorem s16c167_exists_pSub_lift {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {p : ℕ}
    [Fact p.Prime] {Xb : Subgroup (MulAut (Vtil V₀ V hV))} (hXb : Xb ≤ Mbar M V₀ V hV)
    (hp : IsPGroup p Xb) (hnc : ¬ IsCyclic Xb) :
    ∃ X : Subgroup G, X ≤ preBarSub M V₀ V hV Xb ∧ IsPGroup p X ∧ ¬ IsCyclic X := by
  set P : Subgroup G := preBarSub M V₀ V hV Xb with hPdef
  have hPst : P ≤ stabTil V₀ V := by
    intro g hg
    obtain ⟨-, h, -⟩ := (mem_preBarSub M V₀ V hV Xb).1 hg
    exact h
  let φ0 : ↥P →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hPst)
  have hφ0 : ∀ g : ↥P, φ0 g ∈ Xb := by
    intro g
    obtain ⟨-, h, hx⟩ := (mem_preBarSub M V₀ V hV Xb).1 g.2
    exact hx
  let φ : ↥P →* ↥Xb := φ0.codRestrict Xb hφ0
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨m, hmM, rfl⟩ := (mem_barSub V₀ V hV M y).1 (hXb hy)
    have hmP : (m : G) ∈ P := (mem_preBarSub M V₀ V hV Xb).2 ⟨hmM, m.2, hy⟩
    exact ⟨⟨m, hmP⟩, Subtype.ext rfl⟩
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow p ↥P))
  have hT : ((S₀.mapSurjective hφsurj : Sylow p ↥Xb) : Subgroup ↥Xb) = ⊤ := by
    have h1 := (S₀.mapSurjective hφsurj).not_dvd_index
    obtain ⟨n, hn⟩ := hp.index ((S₀.mapSurjective hφsurj : Sylow p ↥Xb) : Subgroup ↥Xb)
    rw [hn] at h1
    have h0 : n = 0 := by
      by_contra hne
      exact h1 (dvd_pow_self p hne)
    rw [h0, pow_zero] at hn
    exact Subgroup.index_eq_one.1 hn
  rw [Sylow.coe_mapSurjective] at hT
  refine ⟨(S₀ : Subgroup ↥P).map P.subtype, Subgroup.map_subtype_le _, S₀.2.map P.subtype, ?_⟩
  intro hXc
  have hS0c : IsCyclic ↥(S₀ : Subgroup ↥P) :=
    (Subgroup.equivMapOfInjective (S₀ : Subgroup ↥P) P.subtype P.subtype_injective).isCyclic.2 hXc
  have hρ : Function.Surjective (φ.comp (S₀ : Subgroup ↥P).subtype) := by
    intro y
    have hy : y ∈ (S₀ : Subgroup ↥P).map φ := hT ▸ Subgroup.mem_top y
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨⟨s, hs⟩, rfl⟩
  exact hnc (isCyclic_of_surjective (φ.comp (S₀ : Subgroup ↥P).subtype) hρ)

theorem s16c167_normalizes_fixV {M V W X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : M ≤ normalizer (V : Set G)) (hWM : W ≤ M)
    {Xb : Subgroup (MulAut (Vtil ⊥ V hV))} (hcomm : ⁅Xb, barSub ⊥ V hV W⁆ = ⊥)
    (hX : X ≤ preBarSub M ⊥ V hV Xb) :
    X ≤ normalizer ((V ⊓ centralizer (W : Set G) : Subgroup G) : Set G) := by
  have hbot : normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.2 inferInstance
  have hMst : M ≤ stabTil ⊥ V := le_stabTil hMV (hbot ▸ le_top)
  have key : ∀ x ∈ X, ∀ u ∈ V ⊓ centralizer (W : Set G),
      x * u * x⁻¹ ∈ V ⊓ centralizer (W : Set G) := by
    intro x hx u hu
    obtain ⟨hxM, hxst, hxXb⟩ := (mem_preBarSub M ⊥ V hV Xb).1 (hX hx)
    have hv : x * u * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hMV hxM) u).1 hu.1
    refine ⟨hv, ?_⟩
    show x * u * x⁻¹ ∈ centralizer (W : Set G)
    have hu2 : u ∈ centralizer (W : Set G) := hu.2
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwst : w ∈ stabTil ⊥ V := hMst (hWM hw)
    have hwbar : actTil ⊥ V hV ⟨w, hwst⟩ ∈ barSub ⊥ V hV W := actTil_mem_barSub ⊥ V hV hw hwst
    have hc1 : ⁅actTil ⊥ V hV ⟨x, hxst⟩, actTil ⊥ V hV ⟨w, hwst⟩⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hxXb hwbar
      rwa [hcomm, Subgroup.mem_bot] at this
    have hc2 : actTil ⊥ V hV ⁅(⟨w, hwst⟩ : ↥(stabTil ⊥ V)), ⟨x, hxst⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (commutatorElement_eq_one_iff_mul_comm.1 hc1).symm
    have hcoe : (((⁅(⟨w, hwst⟩ : ↥(stabTil ⊥ V)), ⟨x, hxst⟩⁆ : ↥(stabTil ⊥ V))) : G) =
        w * x * w⁻¹ * x⁻¹ := by
      simp [commutatorElement_def]
    have ha : ∀ v ∈ V, (w * x * w⁻¹ * x⁻¹) * v * (w * x * w⁻¹ * x⁻¹)⁻¹ = v := by
      intro v hvV
      have h1 := (actTil_eq_one_iff ⊥ V hV _).1 hc2 v hvV
      rw [hcoe, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact h1
    have hwu : w⁻¹ * u * w = u := by
      have h1 : w * u = u * w := Subgroup.mem_centralizer_iff.1 hu2 w hw
      calc w⁻¹ * u * w = w⁻¹ * (u * w) := by group
        _ = w⁻¹ * (w * u) := by rw [h1]
        _ = u := by group
    have h2 := ha _ hv
    have h3 : (w * x * w⁻¹ * x⁻¹) * (x * u * x⁻¹) * (w * x * w⁻¹ * x⁻¹)⁻¹ =
        w * (x * u * x⁻¹) * w⁻¹ := by
      calc (w * x * w⁻¹ * x⁻¹) * (x * u * x⁻¹) * (w * x * w⁻¹ * x⁻¹)⁻¹
          = w * x * (w⁻¹ * u * w) * x⁻¹ * w⁻¹ := by group
        _ = w * x * u * x⁻¹ * w⁻¹ := by rw [hwu]
        _ = w * (x * u * x⁻¹) * w⁻¹ := by group
    rw [h3] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2)
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => key x hx u hu, fun hu => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ hu
  simpa [mul_assoc] using this

theorem s16c167_fixV_wClos_ne_bot (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V) :
    V ⊓ centralizer (E3.wClos V D.k D.T : Set G) ≠ ⊥ := by
  have hP := h.pairFacts
  have hVT : V ≤ D.T := s15_13A_le_T h
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥D.T := hT2.isNilpotent
  have hTn : D.T ≤ normalizer (V : Set G) := D.sylowM.le.trans hP.le_normalizer
  have hnormal : (V.subgroupOf D.T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTn
  have hne : V.subgroupOf D.T ≠ ⊥ := by
    intro h0
    apply hP.ne_bot
    rw [← Subgroup.map_subgroupOf_eq_of_le hVT, h0, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ centralizer (D.T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  have hWT : E3.wClos V D.k D.T ≤ D.T := E3.wClos_le_of_forall fun A hA => hA.1
  intro hbot
  have hmem : (y : G) ∈ V ⊓ centralizer (E3.wClos V D.k D.T : Set G) :=
    ⟨hy.1, Subgroup.centralizer_le hWT hyC⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem s16c167_insp1613U_of_oddNc (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V)
    (hnc : OddNcCore D ⊥ V h.isElemAbelian)
    (hcomm : ⁅oddBar D.M ⊥ V h.isElemAbelian,
      barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)⁆ = ⊥) : Insp1613U D V := by
  obtain ⟨p, hp, Xb, hXb, hXp, hXc⟩ := hnc
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hXbM : Xb ≤ Mbar D.M ⊥ V h.isElemAbelian := hXb.trans (relPPrimeCore_le _)
  obtain ⟨X, hXpre, hXp', hXc'⟩ := s16c167_exists_pSub_lift h.isElemAbelian hXbM hXp hXc
  have hP := h.pairFacts
  have hWT : E3.wClos V D.k D.T ≤ D.T := E3.wClos_le_of_forall fun A hA => hA.1
  refine ⟨V ⊓ centralizer (E3.wClos V D.k D.T : Set G), s16c167_fixV_wClos_ne_bot D h,
    le_rfl, p, hp, X, le_inf (hXpre.trans inf_le_left) ?_, hXp', hXc'⟩
  exact s16c167_normalizes_fixV h.isElemAbelian hP.le_normalizer (hWT.trans D.sylowM.le)
    ((Subgroup.commutator_mono hXb le_rfl).trans hcomm.le |> le_bot_iff.1) hXpre

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
