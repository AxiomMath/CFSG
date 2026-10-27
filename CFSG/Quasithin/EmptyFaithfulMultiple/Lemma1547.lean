module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Two
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits L1547

theorem stmt1547_of (hGN : InputGNC128Solv) (h1391 : Input1391)
    (hI41 : InputI41Two) {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h2 : Stmt1542Two G T) : Stmt1547 G T := by
  intro hZ2
  by_cases hLA : IsLThreeTwoOrASix G
  · exact Or.inr hLA
  left
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := hyp.simple
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  obtain ⟨C₁, C₂, hC₁ne, hC₁Z, -, hC₂ne, hC₂S, hC₂char, hC128⟩ :=
    hGN G S hyp.simple hyp.qtke hyp.sylow (sylow_ne_bot hyp.nonabelian S)
  have hEven := hyp.qtke.2.1
  have hC₁eq : C₁ = quasithinOmegaOneCenter (S : Subgroup G) := by
    refine Subgroup.eq_of_le_of_card_ge hC₁Z ?_
    rw [hZ2]
    have hdvd : Nat.card C₁ ∣ 2 := hZ2 ▸ Subgroup.card_dvd_of_le hC₁Z
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hC₁ne
    · exact h1.ge
  have hTC₂ : (S : Subgroup G) ≤ Subgroup.normalizer (C₂ : Set G) :=
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum _)).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hC₂S hC₂char)
  have hstar : ∀ M : Subgroup G, InM (S : Subgroup G) M → ∀ m ∈ M,
      ∃ n ∈ M ⊓ Subgroup.normalizer (C₂ : Set G),
        ∃ c ∈ M ⊓ Subgroup.centralizer (VZ (S : Subgroup G) M : Set G), m = n * c := by
    intro M hM
    have hTM : (S : Subgroup G) ≤ M := hM.2
    have hF : CharTwo M := hEven M hM.1.1 ⟨S, hTM⟩
    set V : Subgroup G := VZ (S : Subgroup G) M with hVdef
    have hred : IsTwoReducedIn M V := isTwoReducedIn_conjClosure M S hTM hF le_rfl
    have hMV : M ≤ Subgroup.normalizer (V : Set G) := hred.2.1
    set C : Subgroup G := M ⊓ Subgroup.centralizer (V : Set G) with hCdef
    have hMC : M ≤ Subgroup.normalizer (C : Set G) := fun m hm =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hm, normalizer_le_normalizer_centralizer V (hMV hm)⟩
    have hfac_of_le : M ≤ (M ⊓ Subgroup.normalizer (C₂ : Set G)) ⊔ C →
        ∀ m ∈ M, ∃ n ∈ M ⊓ Subgroup.normalizer (C₂ : Set G), ∃ c ∈ C, m = n * c := by
      intro hle m hm
      have hm' : m ∈ (((M ⊓ Subgroup.normalizer (C₂ : Set G)) ⊔ C : Subgroup G) : Set G) :=
        hle hm
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ C (inf_le_left.trans hMC)] at hm'
      obtain ⟨n, hn, c, hc, hnc⟩ := hm'
      exact ⟨n, hn, c, hc, hnc.symm⟩
    by_cases hJ : thompsonJ (S : Subgroup G) ≤ Subgroup.centralizer (V : Set G)
    ·
      have hJ' : thompsonJ (S : Subgroup G) ≤ M ⊓ Subgroup.centralizer (V : Set G) :=
        le_inf ((thompsonJ_le_self _).trans hTM) hJ
      set R : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) with hRdef
      have hRC : R ≤ C := inf_le_inf_right _ hTM
      have hRp : IsPGroup 2 R := S.isPGroup'.to_le inf_le_left
      have hRodd : ¬ 2 ∣ R.relIndex C := by
        have h1 := not_two_dvd_relIndex_inf_of_normalizer (S := (S : Subgroup G)) (D := C)
          (K := M) hTM inf_le_left (isSylowTwoOf_of_sylow S hTM).2.2 (hTM.trans hMC)
        have h2 : (S : Subgroup G) ⊓ C = R := by
          rw [hCdef, hRdef, ← inf_assoc, inf_eq_left.mpr hTM]
        rwa [h2] at h1
      have hfrat := exists_mul_of_sylow inf_le_left hMC hRC hRp hRodd
      have hbaum : baum (S : Subgroup G) = baum R := (lemma_14_1_2_one S hTM hred hJ').2
      have hNR : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C₂ : Set G) :=
        (normalizer_le_normalizer_baum R).trans (hbaum ▸
          normalizer_le_normalizer_of_characteristic_subgroupOf hC₂S hC₂char)
      intro m hm
      obtain ⟨n, hn, c, hc, rfl⟩ := hfrat m hm
      exact ⟨n, ⟨hn.1, hNR hn.2⟩, c, hc, rfl⟩
    ·
      by_contra hfail
      have hsolv := h2 M hM
      obtain ⟨hstab, hcases⟩ :=
        mbar_structure S hTM hF hsolv hM.1.1 hyp.qtke.2.2 hZ2 hJ
      have hM0 : (M ⊓ Subgroup.centralizer (C₁ : Set G)) ⊔
          (M ⊓ Subgroup.normalizer (C₂ : Set G)) ≤ (M ⊓ Subgroup.normalizer (C₂ : Set G)) ⊔ C := by
        refine sup_le ?_ le_sup_left
        rw [hC₁eq]
        intro m hm
        obtain ⟨c, hc, t, ht, rfl⟩ := hstab m hm.1 hm.2
        have hcm : c * t = t * (t⁻¹ * c * t) := by group
        rw [hcm]
        refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hTM ht, hTC₂ ht⟩)
          (Subgroup.mem_sup_right ?_)
        have := (Subgroup.mem_normalizer_iff.mp (hMC (M.inv_mem (hTM ht))) c).mp hc
        simpa using this
      have hcore : perfectCore M ≤ Subgroup.centralizer (VZ (S : Subgroup G) M : Set G) := by
        rw [(isSolvable_iff_perfectCore_eq_bot M).mp hsolv]
        exact bot_le
      rcases hC128 M hM hcore with hM0eq | ⟨s, L, -, -, hL, hMeq⟩
      · exact hfail (hfac_of_le (hM0eq.le.trans hM0))
      obtain ⟨i, hi⟩ : ∃ i, ¬ L i ≤ C := by
        by_contra hall
        push Not at hall
        exact hfail (hfac_of_le (hMeq.le.trans
          (sup_le hM0 (iSup_le fun i => (hall i).trans le_sup_right))))
      obtain ⟨hchi, -⟩ := hL i
      have hXalt := isAltType_three_of_isChiBlock hchi hsolv
      have hX := isA4_of_isAltType hchi.1.1 hXalt
      have hXM : L i ≤ M := hchi.1.2.1
      have hXs : ((L i).subgroupOf M).IsSubnormal := hchi.1.2.2
      have hXV : ¬ L i ≤ Subgroup.centralizer (V : Set G) := fun h => hi (le_inf hXM h)
      rcases hcases with hV4 | ⟨V₁, V₂, hV₁V, hV₂V, hV₁4, hV₂4, hV12, hV12', hswap, hperm,
        hodd, h8⟩
      · exact hLA (isLThreeTwoOrASix_of_card_four hI41 hyp.nonabelian hEven S hTM hF hZ2 hV4
          hJ hX hXM hXs hXV)
      · exact false_of_wreath h1391 hyp.nonabelian hyp.qtke S hM hF hZ2 hV₁V hV₂V hV₁4 hV₂4
          hV12 hV12' hswap hperm hodd h8 hX hXM hXs hXV
  have hC₂2 : IsPGroup 2 C₂ :=
    S.isPGroup'.to_le (hC₂S.trans inf_le_left)
  obtain ⟨Mf, hMf, hNMf⟩ :=
    exists_maxTwoLocal_ge (H := Subgroup.normalizer (C₂ : Set G)) ⟨C₂, hC₂ne, hC₂2, rfl⟩
  have hMfT : InM (S : Subgroup G) Mf := ⟨hMf, hTC₂.trans hNMf⟩
  have hle : ∀ M : Subgroup G, InM (S : Subgroup G) M → ∀ M' : Subgroup G,
      Subgroup.normalizer (C₂ : Set G) ≤ M' → OrdLE (S : Subgroup G) M M' := by
    intro M hM M' hM' m hm
    obtain ⟨n, hn, c, hc, rfl⟩ := hstar M hM m hm
    exact ⟨n, ⟨hn.1, hM' hn.2⟩, c, hc, rfl⟩
  refine ⟨C₂, Mf, hC₂ne, hC₂S, hC₂char, ⟨⟨hMf, hNMf⟩, fun M' hM' => ?_⟩, hMfT,
    fun M hM => hle M hM Mf hNMf⟩
  have hM'T : InM (S : Subgroup G) M' := ⟨hM'.1, hTC₂.trans hM'.2⟩
  exact eq_of_ordLE_antisymm (isHv_of_inM hEven S hM'T) (isHv_of_inM hEven S hMfT)
    (hle M' hM'T Mf hNMf) (hle Mf hMfT M' hM'.2)

end CFSG.Quasithin.EmptyFaithfulMultiple
