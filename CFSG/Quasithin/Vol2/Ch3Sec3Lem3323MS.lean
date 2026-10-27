module

public import CFSG.Quasithin.Background.S1567V4
public import CFSG.Quasithin.Background.C134L32Corr
public import CFSG.Quasithin.Background.B1ChiefCount
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328Pre
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement Pointwise

namespace MS3323

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

omit [Finite G] in
theorem le_centralizer_vPlus (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hLZ : L ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    L ≤ Subgroup.centralizer (vPlus L T : Set G) := by
  have hVZ : vPlus L T ≤ quasithinOmegaOneCenter T := by
    show conjClosure (quasithinOmegaOneCenter T) (conjClosure L T) ≤ _
    rw [show conjClosure L T = L from Hyp331.mPlus_eq_of_le hTL]
    unfold conjClosure
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, z, hz, rfl⟩
    have hzl : l * z = z * l := (Subgroup.mem_centralizer_iff.mp (hLZ hl) z hz).symm
    rw [hzl, mul_inv_cancel_right]
    exact hz
  exact hLZ.trans (Subgroup.centralizer_le hVZ)

theorem false_of_le_center
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hZ : omegaOneCenterOf T ≤ centerOf (L ⊔ T)) : False := by
  apply h.not_L_le_centralizer h38 h39
  refine le_centralizer_vPlus hTL fun l hl => Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  exact (Subgroup.mem_centralizer_iff.mp (hZ hz).2 l (Subgroup.mem_sup_left hl)).symm

omit [Finite G] in
theorem inf_centralizer_eq (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    (L ⊔ T) ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set G) =
      L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T := by
  have hTZ : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  rw [omegaOneCenterOf_eq]
  apply le_antisymm
  · rintro x ⟨hx, hxZ⟩
    obtain ⟨l, hl, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTL).mp hx
    have hlZ : l ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      have := Subgroup.mul_mem _ hxZ (Subgroup.inv_mem _ (hTZ ht))
      simpa using this
    exact Subgroup.mul_mem_sup ⟨hl, hlZ⟩ ht
  · exact sup_le (inf_le_inf_right _ le_sup_left) (le_inf le_sup_right hTZ)

theorem lt_sup
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T < L ⊔ T := by
  set N := L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hN
  have hTZ : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := fun t ht =>
    ChiefCount.mem_normalizer_inf (hTL ht) (Subgroup.le_normalizer (hTZ ht))
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  refine lt_of_le_of_ne (sup_le_sup_right inf_le_left T) fun heq => ?_
  apply h.not_L_le_centralizer h38 h39
  refine le_centralizer_vPlus hTL ?_
  rw [← CFSG.Quasithin.C2Nine.oTwoUpper_eq_of_perfect h.toSetup331.perfect]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxL, hxo⟩
  have hxH : x ∈ N ⊔ T := heq ▸ Subgroup.mem_sup_left hxL
  obtain ⟨n, hn, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTN).mp hxH
  obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
  have ha' : t ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hstep : ∀ m : ℕ, ∃ n' ∈ N, (n * t) ^ m = n' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨n', hn', e⟩ := ih
      refine ⟨n' * (t ^ m * n * (t ^ m)⁻¹), N.mul_mem hn' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hTN (T.pow_mem ht m)) n).mp hn
      · rw [pow_succ, e]
        group
  obtain ⟨n', hn', e⟩ := hstep (2 ^ a)
  rw [ha', mul_one] at e
  have hxN : n * t ∈ N := Lem3328.mem_of_pow_odd hxo (by rw [pow_orderOf_eq_one]; exact N.one_mem)
    (e ▸ hn')
  exact hxN.2

theorem not_two_dvd_relIndex (h : Hyp331 G T M L D) :
    ¬ 2 ∣ (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T).relIndex (L ⊔ T) :=
  fun h2 => h.toSetup331.isSylowTwoOf.2.2
    (h2.trans (Subgroup.relIndex_dvd_of_le_left _ le_sup_right))

theorem exists_char
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hC34 : CFSG.Quasithin.C134L32Corr) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα : IsModO2Surj L α)
    (hinner : ∀ t ∈ T, ∃ l ∈ L, ∃ c ∈ qL L T, t = l * c) (hNC : HasNoncentralTwoChief L 2) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧
      C ≤ pCoreOf 2 (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T) ∧
      L ⊔ T ≤ Subgroup.normalizer (C : Set G) ∧
      Subgroup.normalizer ((pCoreOf 2
        (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T) : Subgroup G) :
          Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T with hH
  set R := pCoreOf 2 H with hR
  have hTH : T ≤ H := le_sup_right
  have hHLT : H ≤ L ⊔ T := sup_le_sup_right inf_le_left T
  have hsylT : IsSylowTwoOf T (L ⊔ T) := h.toSetup331.isSylowTwoOf
  have hsylH : IsSylowTwoOf T H := ⟨hTH, hsylT.2.1, fun h2 =>
    hsylT.2.2 (h2.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex T H (L ⊔ T) hTH hHLT)))⟩
  have hRT : R ≤ T := pCoreOf_le_of_isSylowTwoOf hsylH
  have hQR : qL L T ≤ R := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le_of_isSylowTwoOf hsylT).trans hTH) (fun x hx =>
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) (hHLT hx))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hset : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T hTL
  have hset' : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (R : Set G) := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [hset] at hx
      obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hx
      obtain ⟨l', hl', c, hc, rfl⟩ := hinner t ht
      exact Set.mem_mul.mpr ⟨l * l', L.mul_mem hl hl', c, hQR hc, by group⟩
    · rintro _ ⟨l, hl, r, hr, rfl⟩
      exact Subgroup.mul_mem_sup hl (hRT hr)
  have hr2 := CFSG.Quasithin.S1567.isRankTwoLie2Derived_of_modO2 α hα.1 hα.2
  have hcomp := h.toSetup331.mem_cComp
  have hMST : IsMSPair (L ⊔ T) T := h.isMSPair h38 h39 hr2 hTL
  by_cases hMS3 : ∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → (C.subgroupOf R).Characteristic →
      ¬ L ⊔ T ≤ Subgroup.normalizer (C : Set G)
  · exfalso
    have hMSR : IsMSPair (L ⊔ T) R :=
      ⟨⟨hMST.1.1, hMST.1.2.1, L, hcomp, hset', hr2⟩,
        Or.inl ⟨H, lt_sup h h38 h39 hTL, not_two_dvd_relIndex h, rfl⟩, hMS3⟩
    obtain ⟨i, hi⟩ := hC34 G (L ⊔ T) R L hMSR hcomp hset'
      ⟨ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩
    have hRZ : R = pCoreOf 2 ((L ⊔ T) ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set G)) := by
      rw [inf_centralizer_eq hTL]
    match i, hi with
    | 0, hi => exact hi.elim
    | 1, hi => exact Lem3328.not_hasNoncentralTwoChief_two_of_isShort2 hi.1.1 hNC
    | 2, hi => exact hi.2 T hsylT hRT hRZ
    | 3, hi => exact hi.2 T hsylT hRT hRZ
    | 4, hi => exact hi.2 T hsylT hRT hRZ
    | 5, hi => exact false_of_le_center h h38 h39 hTL (hi.2 T hsylT hRT).1
    | n + 6, hi => exact hi.elim
  · push Not at hMS3
    obtain ⟨C, hCR, hC1, hchar, hLTC⟩ := hMS3
    exact ⟨C, hC1, hCR, hLTC, Hyp331.normalizer_le_normalizer_of_characteristic hCR hchar⟩

end MS3323

end CFSG.Quasithin.H13
