module

public import CFSG.Quasithin.EmptyFaithful.SzSurvLocZSNCrit
public import CFSG.Quasithin.EmptyFaithful.SzSurvLocZSNNorm
public import CFSG.Quasithin.Background.Harris.R1.QbetaKerS
public import CFSG.Quasithin.Recognition.SzR1MNU

public section

namespace CFSG.Quasithin.SzSurvLoc

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.Quasithin.F7 CFSG.Quasithin.F112W CFSG.Quasithin.SzR1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

theorem act_ker_le_pCore [Fintype Ω] (C : FamCtx K1 L2 S Zs Ω) (hodd : Odd (Fintype.card Ω))
    (hΩ : 2 ≤ Fintype.card Ω) (hsimple : IsSimpleGroup (OTwoQuot K1)) :
    ∀ k : ↥K1, C.D.act k = 1 → (k : G) ∈ pCoreOf 2 K1 := by
  classical
  intro k hk
  set O : Subgroup ↥K1 := CFSG.Open.pCore 2 ↥K1 with hO
  have hOn : O.Normal := CFSG.LieType.BorelTits.pCore_normal (r := 2) (G := ↥K1)
  have hO2 : IsPGroup 2 ↥O := CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥K1)
  set K0 : Subgroup ↥K1 := C.D.act.ker with hK0
  have hmapn : (K0.map (QuotientGroup.mk' O)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K0.map (QuotientGroup.mk' O)) with hb | ht
  · have hkmem : QuotientGroup.mk' O k ∈ K0.map (QuotientGroup.mk' O) :=
      Subgroup.mem_map_of_mem _ hk
    rw [hb, Subgroup.mem_bot] at hkmem
    exact (CFSG.Quasithin.Background.Harris.R1.SplitAux.mem_pCoreOf_iff_mem_pCore k).mpr
      ((QuotientGroup.eq_one_iff k).mp hkmem)
  · exfalso
    have hsup : K0 ⊔ O = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' O) K0
      rw [ht, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hOtrans : ∀ ω₁ ω₂ : Ω, ∃ o : ↥O, C.D.act (o : ↥K1) ω₁ = ω₂ := by
      intro ω₁ ω₂
      obtain ⟨a, ha⟩ := C.D.trans ω₁
      obtain ⟨b, hb'⟩ := C.D.trans ω₂
      have hmem : b * a⁻¹ ∈ K0 ⊔ O := by
        rw [hsup]
        exact Subgroup.mem_top _
      obtain ⟨k₀, hk₀, o, ho, hko⟩ := (Subgroup.mem_sup_of_normal_right (s := K0) (t := O)).mp hmem
      refine ⟨⟨o, ho⟩, ?_⟩
      have h1 : C.D.act (b * a⁻¹) ω₁ = ω₂ := by
        rw [map_mul, map_inv, Equiv.Perm.mul_apply]
        have h2 : (C.D.act a)⁻¹ ω₁ = C.D.pt := by
          rw [← ha]
          exact Equiv.symm_apply_apply _ _
        rw [h2, hb']
      have h3 : C.D.act k₀ = 1 := hk₀
      rw [← hko, map_mul, h3, one_mul] at h1
      exact h1
    let I : Subgroup (Equiv.Perm Ω) := O.map C.D.act
    have hI2 : IsPGroup 2 ↥I :=
      hO2.of_surjective (C.D.act.subgroupMap O) (C.D.act.subgroupMap_surjective O)
    have horb : MulAction.orbit ↥I C.D.pt = Set.univ := by
      ext ω
      simp only [Set.mem_univ, iff_true]
      obtain ⟨o, ho⟩ := hOtrans C.D.pt ω
      exact ⟨⟨C.D.act (o : ↥K1), Subgroup.mem_map_of_mem _ o.2⟩, by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using ho⟩
    obtain ⟨m, hm⟩ := hI2.card_orbit C.D.pt
    rw [horb, Nat.card_univ, Nat.card_eq_fintype_card] at hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, pow_zero] at hm
      omega
    · have hev : Even (2 ^ m) := (Nat.even_pow.mpr ⟨even_two, hpos.ne'⟩)
      rw [← hm] at hev
      exact (Nat.not_even_iff_odd.mpr hodd) hev

theorem famCtx_commutator_mem [Fintype Ω] (C : FamCtx K1 L2 S Zs Ω) (hΩ : 4 ≤ Fintype.card Ω)
    (hker : ∀ k : ↥K1, C.D.act k = 1 → (k : G) ∈ pCoreOf 2 K1) :
    ∀ s ∈ S, ∀ x ∈ omegaOneCenterOf (pCoreOf 2 (L2 ⊔ S)), s * x * s⁻¹ * x⁻¹ ∈ Zs := by
  classical
  obtain ⟨ω, hω⟩ := Fintype.exists_ne_of_one_lt_card (by omega) C.D.pt
  have hkerS : C.kerM ≤ S := CFSG.Quasithin.Background.Harris.R1.kerM_le_S C hker
  have hAker : ∀ x ∈ omegaOneCenterOf (pCoreOf 2 (L2 ⊔ S)), x ∈ C.kerM := by
    intro x hx
    obtain ⟨hxQ, hxc, -⟩ := SzR1.MNU.mem_omegaOneCenterOf_iff.mp hx
    refine C.mem_kerM_of_mem_pCore hΩ hω hxQ ?_
    intro w hw
    have h1 := hxc w hw.2
    have h2 : x * w * x⁻¹ * w⁻¹ = 1 := by
      calc x * w * x⁻¹ * w⁻¹ = (w * x) * x⁻¹ * w⁻¹ := by rw [h1]
        _ = 1 := by group
    rw [h2]
    exact Zs.one_mem
  set k : G := (C.D.kf ω : G) with hk
  have hkK : k ∈ K1 ⊔ S := Subgroup.mem_sup_left (C.D.kf ω).2
  have hAk : ∀ a ∈ omegaOneCenterOf (pCoreOf 2 (L2 ⊔ S)), k⁻¹ * a * k ∈ S := by
    intro a ha
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (C.sup_le_normalizer_kerM ((K1 ⊔ S).inv_mem hkK)) a).mp (hAker a ha)
    have h2 : k⁻¹ * a * k⁻¹⁻¹ ∈ S := hkerS h1
    simpa using h2
  have hV : conjClosure Zs L2 ≤ omegaOneCenterOf (pCoreOf 2 (L2 ⊔ S)) :=
    SzR1.MNU.V_le_omegaOneCenter_pCore C.h C.hR
  have hvA : C.zf C.D.pt ∈ omegaOneCenterOf (pCoreOf 2 (L2 ⊔ S)) := by
    apply hV
    have h1 := C.zf_mem C.D.pt
    rwa [C.Vf_pt] at h1
  have hzk : C.zf ω ∈ conjSub (C.D.kf ω : G) (conjClosure Zs L2) := C.zf_mem ω
  have hyV : k⁻¹ * C.zf ω * k ∈ conjClosure Zs L2 := mem_conjSub.mp hzk
  have hyA : k⁻¹ * C.zf ω * k ∈ omegaOneCenterOf (pCoreOf 2 (L2 ⊔ S)) := hV hyV
  have hx : C.zf ω = k * (k⁻¹ * C.zf ω * k) * k⁻¹ := by group
  have hxS : C.zf ω ∈ S := C.vBeta_le_S (C.zf_mem_U ω)
  have hxQ : C.zf ω ∉ pCoreOf 2 (L2 ⊔ S) := C.not_zf_mem_pCore hω
  have hcm : C.cm C.D.pt ω ≠ 1 := C.cm_ne_one hω.symm
  have hvx : C.zf C.D.pt * C.zf ω ≠ C.zf ω * C.zf C.D.pt := by
    intro h
    apply hcm
    show C.zf C.D.pt * C.zf ω * (C.zf C.D.pt)⁻¹ * (C.zf ω)⁻¹ = 1
    rw [h]
    group
  have hAQ : ∀ q ∈ pCoreOf 2 (L2 ⊔ S), ∀ a ∈ omegaOneCenterOf (pCoreOf 2 (L2 ⊔ S)),
      q * a = a * q := fun q hq a ha =>
    ((SzR1.MNU.mem_omegaOneCenterOf_iff.mp ha).2.1 q hq).symm
  exact commutator_mem_of_critical_pair (SzR1.MNU.relIndex_pCore_S_of_setting C.h C.hR) hAQ hAk
    hvA hyA hx hxS hxQ hvx (C.cm_mem C.D.pt ω)

theorem hZS_of_famCtx [Fintype Ω] (C : FamCtx K1 L2 S Zs Ω) (hΩ : 4 ≤ Fintype.card Ω)
    (hker : ∀ k : ↥K1, C.D.act k = 1 → (k : G) ∈ pCoreOf 2 K1)
    (hKZ : K1 ≤ Subgroup.centralizer (omegaOneCenterOf S : Set G)) :
    ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs := by
  intro u huS hu2 huc
  have hQn : L2 ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 (L2 ⊔ S) : Set G) :=
    le_normalizer_pCoreOf 2 (L2 ⊔ S)
  have huQ : u ∈ pCoreOf 2 (L2 ⊔ S) := SzR1.MNU.mem_pCore_of_central C.h C.hR huS huc
  have huA : u ∈ omegaOneCenterOf (pCoreOf 2 (L2 ⊔ S)) :=
    SzR1.MNU.mem_omegaOneCenterOf_iff.mpr ⟨huQ, fun y hy => huc y (C.pCore_le_S hy), hu2⟩
  refine mem_of_central_involution_of_commutator (P := L2 ⊔ S) (S := S)
    (Q := pCoreOf 2 (L2 ⊔ S)) (A := omegaOneCenterOf (pCoreOf 2 (L2 ⊔ S))) (K1 := K1) (Zs := Zs)
    le_sup_right (SzR1.MNU.relIndex_S_P_of_setting C.h C.hR) C.amalgamHypV.sylow₁.2.1
    C.pCore_le_S (SzR1.MNU.relIndex_pCore_S_of_setting C.h C.hR) hQn
    (fun g hg => A4.normalizer_le_normalizer_omegaOneCenterOf _ (hQn hg))
    (fun x hx => C.pCore_le_S (SzR1.MNU.mem_omegaOneCenterOf_iff.mp hx).1)
    (fun a ha b hb => (SzR1.MNU.mem_omegaOneCenterOf_iff.mp ha).2.1 b
      (SzR1.MNU.mem_omegaOneCenterOf_iff.mp hb).1)
    (fun a ha => (SzR1.MNU.mem_omegaOneCenterOf_iff.mp ha).2.2)
    (fun a ha q hq => (SzR1.MNU.mem_omegaOneCenterOf_iff.mp ha).2.1 q hq)
    (famCtx_commutator_mem C hΩ hker) ?_ ?_ huA huc
  · intro n hnS hn2 hnc k hk
    have hnZ : n ∈ omegaOneCenterOf S := SzR1.MNU.mem_omegaOneCenterOf_iff.mpr ⟨hnS, hnc, hn2⟩
    exact (Subgroup.mem_centralizer_iff.mp (hKZ hk) n hnZ).symm
  · intro N hN2 hNS hN
    have hNG : N ≤ K1 ⊔ L2 ⊔ S := hNS.trans le_sup_right
    have hGN : K1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (N : Set G) := by
      rw [sup_assoc]
      exact hN
    have hle := le_pCoreOf_of_le_normalizer 2 hNG hGN hN2
    rw [C.h.hyp.o2] at hle
    exact le_bot_iff.mp hle

end CFSG.Quasithin.SzSurvLoc
