module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMinParabolic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate7

public section

namespace CFSG.Quasithin.SteinbergBS.NormalSylowA3

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Wreath
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem odd_sup_sylow {T : Subgroup H} (hT : IsSylowTwoOf T ⊤) :
    oddOrderSubgroup (⊤ : Subgroup H) ⊔ T = ⊤ := by
  have h := CFSG.Quasithin.sup_twoResidual_eq hT
  rw [← oddOrderSubgroup_eq_twoResidual] at h
  rw [sup_comm]
  exact h

omit [Finite H] in
theorem odd_normalizer_eq_top :
    normalizer ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H) = ⊤ :=
  normalizer_eq_top_iff.mpr (WreathHyp.oddOrderSubgroup_top_normal (H := H))

theorem top_le_normalizer_odd_sup {T R : Subgroup H} (hT : IsSylowTwoOf T ⊤)
    (hRTn : T ≤ normalizer (R : Set H)) :
    ⊤ ≤ normalizer ((oddOrderSubgroup (⊤ : Subgroup H) ⊔ R : Subgroup H) : Set H) := by
  have hle : oddOrderSubgroup (⊤ : Subgroup H) ⊔ T ≤
      normalizer ((oddOrderSubgroup (⊤ : Subgroup H) ⊔ R : Subgroup H) : Set H) := by
    refine sup_le (fun n hn => Subgroup.le_normalizer (le_sup_left (b := R) hn)) fun t ht => ?_
    refine C1.mem_normalizer_sup ?_ (hRTn ht)
    rw [odd_normalizer_eq_top]
    exact Subgroup.mem_top t
  intro g _
  have hg : g ∈ oddOrderSubgroup (⊤ : Subgroup H) ⊔ T := by
    rw [odd_sup_sylow hT]
    exact Subgroup.mem_top g
  exact hle hg

theorem charTwo_odd_sup {T R : Subgroup H} (hchar : CharTwo (⊤ : Subgroup H))
    (hT : IsSylowTwoOf T ⊤) (hRTn : T ≤ normalizer (R : Set H)) :
    CharTwo (oddOrderSubgroup (⊤ : Subgroup H) ⊔ R) :=
  CharTwo.of_normal hchar le_top
    ((normal_subgroupOf_iff_le_normalizer le_top).2 (top_le_normalizer_odd_sup hT hRTn))

omit [Finite H] in
theorem isSolvable_autOn {P V : Subgroup H} (hPN : P ≤ normalizer (V : Set H))
    [Group.IsSolvable P] : Group.IsSolvable ↥(autOn P V) := by
  rw [← range_rho hPN]
  exact Group.isSolvable_of_surjective (rho V P hPN).rangeRestrict_surjective

theorem exists_block_family (hsolv : Group.IsSolvable H) (hchar : CharTwo (⊤ : Subgroup H))
    {T M R : Subgroup H} (hT : IsSylowTwoOf T ⊤) (hMlt : M < ⊤) (hTM : T ≤ M)
    (hmax : ∀ Y : Subgroup H, T ≤ Y → Y < ⊤ → Y ≤ M) (hR1 : R ≠ ⊥) (hRT : R ≤ T)
    (hRTn : T ≤ normalizer (R : Set H))
    (hRsyl : IsSylowTwoOf R (oddOrderSubgroup (⊤ : Subgroup H) ⊔ R))
    (hnoChar : NoCharNormal R ⊤) :
    ∃ (P : Subgroup H) (s : ℕ) (Y : Fin s → Subgroup H),
      R ≤ P ∧ P ≤ oddOrderSubgroup (⊤ : Subgroup H) ⊔ R ∧ P ⊔ T = ⊤ ∧ 1 ≤ s ∧
      (∀ i, IsBlock2 P (Y i)) ∧ R ⊔ ⨆ i, Y i = P ∧
      (∀ i, Y i ≤ oddOrderSubgroup (⊤ : Subgroup H)) ∧
      (∀ i, Nonempty (↥(Y i) ≃* alternatingGroup (Fin 4))) ∧
      (∀ i, Nat.card (↥(Y i) ⧸ CFSG.pCore 2 ↥(Y i)) = 3) ∧
      (∀ i, ⁅Y i, thompsonJ R⁆ = Y i) ∧
      ∀ i j, ∃ t ∈ R, (Y i).map (MulAut.conj t).toMonoidHom = Y j := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oddOrderSubgroup (⊤ : Subgroup H) with hK
  have hKT : K ⊔ T = ⊤ := odd_sup_sylow hT
  have hcharKR : CharTwo (K ⊔ R) := charTwo_odd_sup hchar hT hRTn
  obtain ⟨P, hPNR, hRPlt, -, hRPsyl, hPnn, ⟨hPMlt, hRPM, hPmax⟩, hPT, -, hPchar⟩ :=
    minimal_parabolic_subgroup_over_normal_Sylow_part (p := 2) hT hMlt hTM hmax le_top
      (by rw [odd_normalizer_eq_top]) hKT (hasNoTwoQuotient_oddOrderSubgroup _) hR1 hRT hRTn
      hRsyl hnoChar
  have hRP : R ≤ P := hRPlt.le
  have hRsylP : IsSylowTwoOf R P := hRPsyl
  have hQR : blockQ (K ⊔ R) ≤ R := hRsyl.pCoreOf_le
  have hcharP : CharTwo P :=
    charTwo_of_pCore_centralizer_le hcharKR hPNR fun x hx => hRP (hQR hx.1)
  set Z₀ := omegaOneCenterOf R with hZ₀
  set V := conjClosure Z₀ P with hV
  have hZne : Z₀ ≠ ⊥ := omegaOneCenterOf_ne_bot hRsylP.2.1 hR1
  have hZR : Z₀ ≤ R := omegaOneCenterOf_le R
  have hred : IsTwoReducedIn P V :=
    isTwoReducedIn_conjClosure_of_sylowIn hRsylP.1 hRsylP.2.1 hRsylP.2.2 hcharP
      (omegaOneCenterOf_eq R).le
  have hPN : P ≤ normalizer (V : Set H) := hred.2.1
  have hVP : V ≤ P := hred.1
  have hnc : ¬ P ≤ centralizer (V : Set H) := by
    intro hc
    refine hPchar Z₀ hZR hZne (characteristic_omegaOneCenterOf R) fun g hg => ?_
    exact centralizer_le_normalizer _ (centralizer_le (le_conjClosure Z₀ P) (hc hg))
  have : Group.IsSolvable ↥P := inferInstance
  obtain ⟨r, I, W, F, Pm, hw, Kf, -, -, -, hKf⟩ :=
    solvable_reduced_action_produces_A3_family (H := ↥P) (R := R.subgroupOf P)
      (M := (P ⊓ M).subgroupOf P) (V := V.subgroupOf P) (charTwo_top_of_charTwo hcharP)
      (Layer.isSylowTwoOf_subgroupOf_top' hRsylP)
      (fun hn => hPnn ((normal_subgroupOf_iff_le_normalizer hRP).mp hn))
      (fun x hx => mem_subgroupOf.mpr (hRPM (mem_subgroupOf.mp hx)))
      (by
        refine lt_top_iff_ne_top.mpr fun htop => ?_
        have hPK : P ≤ P ⊓ M := fun x hx => mem_subgroupOf.mp
          (show (⟨x, hx⟩ : ↥P) ∈ (P ⊓ M).subgroupOf P by rw [htop]; trivial)
        exact absurd hPK (not_le_of_gt hPMlt))
      (by
        intro Y hRY hY
        have hRY' : R ≤ Y.map P.subtype := by
          have := map_mono (f := P.subtype) hRY
          rwa [map_subgroupOf_eq_of_le hRP] at this
        have hYP : Y.map P.subtype < P := by
          refine lt_of_le_of_ne (Subgroup.map_subtype_le Y) fun heq => ?_
          apply (lt_top_iff_ne_top.mp hY)
          refine top_unique fun x _ => ?_
          have hx : (x : H) ∈ Y.map P.subtype := by rw [heq]; exact x.2
          obtain ⟨y, hy, hyx⟩ := hx
          have : y = x := Subtype.ext hyx
          rwa [this] at hy
        intro y hy
        exact mem_subgroupOf.mpr (hPmax _ hRY' hYP ⟨y, hy, rfl⟩))
      (noCharNormal_top_of hRP fun C hC0 hCR hCc => hPchar C hCR hC0 hCc)
      (isTwoReducedIn_top_of hred)
      (by
        intro htop
        apply hnc
        intro y hy
        exact (BlueprintB2.mem_centralizer_subgroupOf_iff hVP ⟨y, hy⟩).mp (htop (mem_top _)))
      (solvable_autOn_top hPN hVP (isSolvable_autOn hPN))
  have hf : Function.Injective P.subtype := P.subtype_injective
  have hK12 : ∀ i, Nat.card ↥(Kf i) = 12 := fun i => by
    obtain ⟨e⟩ := hKf.alt4 i
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  refine ⟨P, r, fun i => (Kf i).map P.subtype, hRP, hPNR, hPT, hw.r_pos, fun i => ?_, ?_,
    fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i j => ?_⟩
  ·
    have hc := hKf.chi0 i
    refine ⟨IsShort2.map_of_injective P.subtype hf hc.1.1, Subgroup.map_subtype_le _, ?_⟩
    have hsub := isSubnormal_map_injective P.subtype hf hc.1.2.2
    rw [Subgroup.map_top, Subgroup.range_subtype] at hsub
    exact hsub
  ·
    have h1 : oddOrderSubgroup (⊤ : Subgroup ↥P) ⊔ R.subgroupOf P = ⊤ := hKf.H_eq
    rw [hKf.N_eq] at h1
    have h2 := congrArg (Subgroup.map P.subtype) h1
    rw [Subgroup.map_sup, Subgroup.map_iSup, Subgroup.map_subgroupOf_eq_of_le hRP,
      Subgroup.map_top, Subgroup.range_subtype] at h2
    rw [sup_comm]
    exact h2
  ·
    have h1 := map_mono (f := P.subtype) (hKf.K_le_N i)
    rw [oddOrderSubgroup_top_map P] at h1
    exact h1.trans (closure_mono fun x hx => ⟨mem_top _, hx.2⟩)
  · obtain ⟨e⟩ := hKf.alt4 i
    exact ⟨((Kf i).equivMapOfInjective P.subtype hf).symm.trans e⟩
  · exact (card_quot_pCore_map_injective P.subtype hf (Kf i)).trans
      (card_quot_pCore_of_core (hKf.core i) (hw.I_card i) (hK12 i))
  · have hJ : (thompsonJ (R.subgroupOf P)).map P.subtype = thompsonJ R := by
      rw [← elemThompsonIn_two_eq, elemThompsonIn_subgroupOf_map_eq hRP]
    change ⁅(Kf i).map P.subtype, thompsonJ R⁆ = (Kf i).map P.subtype
    rw [← hJ, ← map_commutator, hKf.perfect_J i]
  · obtain ⟨t, ht, hj⟩ := hKf.transitive i j
    refine ⟨(t : H), mem_subgroupOf.1 ht, ?_⟩
    have := map_subtype_conj (P := P) t (Kf i)
    rw [hj] at this
    exact this

end CFSG.Quasithin.SteinbergBS.NormalSylowA3
