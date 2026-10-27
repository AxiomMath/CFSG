module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_18_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_19
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section12_not_mem_beta_of_not_mem_sigma_of_dvd_card_current
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {q : Nat.Primes}
    (hqM : q.val ∣ Nat.card M) (hqσ : q ∉ section10SigmaPrimes M) :
    q ∉ section10BetaPrimes M := by
  classical
  intro hqβ
  let A : Subgroup M := section10MalphaSubgroup M
  let S : Subgroup M := section10MsigmaSubgroup M
  have hAHall : IsHallSubgroup (section10AlphaPrimes M) A := by
    simpa [A] using (theorem_10_2_a (G := G) hM).2
  have hAS : A ≤ S := by
    simpa [A, S] using (theorem_10_2_c (G := G) hM).1
  have hSHall : IsHallSubgroup (section10SigmaPrimes M) S := by
    simpa [S] using (theorem_10_2_b (G := G) hM).2
  have hq_not_A_index : ¬ q.val ∣ A.index := by
    intro hqidx
    exact (hAHall.p_in_pi_of_p_dvd_index q hqidx) hqβ.1
  have hcardM : Nat.card M = Nat.card A * A.index := by
    rw [A.card_mul_index]
  have hq_prod : q.val ∣ Nat.card A * A.index := by
    rw [← hcardM]
    exact hqM
  have hqA : q.val ∣ Nat.card A := by
    rcases q.property.dvd_or_dvd hq_prod with hqA | hqidx
    · exact hqA
    · exact False.elim (hq_not_A_index hqidx)
  have hqS : q.val ∣ Nat.card S :=
    hqA.trans (Subgroup.card_dvd_of_le hAS)
  exact hqσ (hSHall.p_in_pi_of_p_dvd_card q hqS)

private theorem CFSG.section12_isInvariant_of_le_fixedPointSubgroup_current
    {A R : Type*} [Group A] [Group R] [MulDistribMulAction A R]
    {H : Subgroup R} (hH : H ≤ fixedPointSubgroup A R) :
    IsInvariant A R H := by
  have htriv : ActsTriviallyOnSubgroup (A := A) (G := R) H :=
    actsTriviallyOnSubgroup_of_le_fixedPointSubgroup (A := A) (G := R) hH
  refine ⟨?_⟩
  intro a x
  constructor
  · intro hx
    simpa [htriv a x hx] using hx
  · intro hax
    have hfix : a⁻¹ • (a • x) = a • x := htriv a⁻¹ (a • x) hax
    have hx_eq : x = a • x := by
      simpa [inv_smul_smul] using hfix
    rw [hx_eq]
    exact hax

private theorem CFSG.section12_exists_hall_betaCompl_fixed_by_sylow_derivedE
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    [Subgroup.Normalizes (ambientDerivedSubgroup E) (section10Msigma M)]
    {q : Nat.Primes} (Q : Sylow q.val (ambientDerivedSubgroup E))
    (hqD : q.val ∣ Nat.card (ambientDerivedSubgroup E)) :
    ∃ H : Subgroup (section10Msigma M),
      IsHallSubgroup (section10BetaPrimes M)ᶜ H ∧
        H ≤ fixedPointSubgroup (Q : Subgroup (ambientDerivedSubgroup E)) (section10Msigma M) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup E
  let S : Subgroup G := section10Msigma M
  let X : Subgroup G := (Q : Subgroup D).map D.subtype
  have hD_le_E : D ≤ E := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (E := E))
  have hD_le_M : D ≤ M := hD_le_E.trans hE.1.2.1
  have hX_le_D : X ≤ D := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hX_le_M : X ≤ M := hX_le_D.trans hD_le_M
  have hD_le_Mder : D ≤ ambientDerivedSubgroup M := by
    simpa [D] using section12_ambientDerivedSubgroup_mono (G := G) hE.1.2.1
  have hX_le_Mder : X ≤ ambientDerivedSubgroup M := hX_le_D.trans hD_le_Mder
  have hXq : IsPGroup q.val X := by
    simpa [X] using
      IsPGroup.map (p := q.val) (H := (Q : Subgroup D)) Q.isPGroup' D.subtype
  have hqM_dvd : q.val ∣ Nat.card M :=
    hqD.trans (Subgroup.card_dvd_of_le hD_le_M)
  have hDπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ D := by
    simpa [D] using section12_ambientDerivedSubgroup_sigma_compl (G := G) hM hE.1
  have hq_not_sigma : q ∉ section10SigmaPrimes M := by
    exact hDπ q hqD
  have hqβ : q ∉ section10BetaPrimes M :=
    section12_not_mem_beta_of_not_mem_sigma_of_dvd_card_current
      (G := G) hM hqM_dvd hq_not_sigma
  let C : Subgroup S := fixedPointSubgroup (Q : Subgroup D) S
  have hC_index_no_betaCompl :
      ∀ p : Nat.Primes, p ∈ (section10BetaPrimes M)ᶜ → ¬ p.val ∣ C.index := by
    intro p hpβ hpidx
    let _ : Fact p.val.Prime := ⟨p.property⟩
    have hpS_dvd : p.val ∣ Nat.card S := by
      have hcardS : Nat.card S = Nat.card C * C.index := by
        rw [C.card_mul_index]
      rw [hcardS]
      exact dvd_mul_of_dvd_right hpidx (Nat.card C)
    have hpM : p ∈ subgroupPrimeSet M := by
      have hpS_amb : p.val ∣ Nat.card (section10Msigma M) := by
        simpa [S] using hpS_dvd
      exact section8_subgroupPrimeSet_mono (section12_Msigma_le (G := G) M) hpS_amb
    have hpσ : p ∈ section10SigmaPrimes M := by
      have hpS_amb : p.val ∣ Nat.card (section10Msigma M) := by
        simpa [S] using hpS_dvd
      exact (theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_card p hpS_amb
    have hpq : p ≠ q := by
      intro hpq
      exact hq_not_sigma (by simpa [hpq] using hpσ)
    obtain ⟨Pσ, hPσcent⟩ :=
      corollary_10_9_a_1
        (G := G) (M := M) (X := X) (p := p) (q := q)
        hM hpM (by simpa [subgroupPrimeSet] using hqM_dvd)
        (by simpa using hpβ) hqβ hpq hX_le_M hXq (Or.inl hX_le_Mder)
    have hP_le_C : (Pσ : Subgroup S) ≤ C := by
      intro y hy
      change y ∈ fixedPointSubgroup (Q : Subgroup D) S
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro a
      apply Subtype.ext
      have hyAmb : ((y : S) : G) ∈ section10AmbientSylowSubgroup S Pσ :=
        ⟨y, hy, rfl⟩
      have hyCent : ((y : S) : G) ∈ Subgroup.centralizer (X : Set G) :=
        hPσcent hyAmb
      have haX : (((a : (Q : Subgroup D)) : D) : G) ∈ X := by
        exact Subgroup.mem_map.mpr ⟨(a : (Q : Subgroup D)), a.property, rfl⟩
      have hcomm :=
        (Subgroup.mem_centralizer_iff.mp hyCent) (((a : (Q : Subgroup D)) : D) : G) haX
      have hconj :
          (((a : (Q : Subgroup D)) : D) : G) * ((y : S) : G) *
              (((a : (Q : Subgroup D)) : D) : G)⁻¹ = ((y : S) : G) := by
        have := congrArg (fun z : G => z * (((a : (Q : Subgroup D)) : D) : G)⁻¹) hcomm
        simpa [mul_assoc] using this
      change (((a : (Q : Subgroup D)) : D) : G) * ((y : S) : G) *
          (((a : (Q : Subgroup D)) : D) : G)⁻¹ = ((y : S) : G)
      exact hconj
    exact Pσ.not_dvd_index (hpidx.trans (Subgroup.index_dvd_of_le hP_le_C))
  have hSproper : S ≠ ⊤ := by
    intro htop
    have hMtop : M = ⊤ := by
      apply eq_top_iff.2
      rw [← htop]
      exact section12_Msigma_le (G := G) M
    exact hM.1 hMtop
  have hSsolv : Group.IsSolvable S :=
    IsMinCE.proper_subgroups_solvable S (lt_top_iff_ne_top.2 hSproper)
  have hCsolv : Group.IsSolvable C := by
    let : Group.IsSolvable S := hSsolv
    infer_instance
  let _ : MulDistribMulAction PUnit.{1} C := {
    smul := fun _ x => x
    one_smul := by intro x; rfl
    mul_smul := by intro a b x; rfl
    smul_mul := by intro a x y; rfl
    smul_one := by intro a; rfl }
  obtain ⟨HC, hHCHall, _hHCinv⟩ :=
    exists_isHallSubgroup_isInvariant
      (G := C) (A := PUnit.{1}) hCsolv (by simp) (section10BetaPrimes M)ᶜ
  let H : Subgroup S := HC.map C.subtype
  have hHHall : IsHallSubgroup (section10BetaPrimes M)ᶜ H := by
    refine isHallSubgroup_of (G := S) (π := (section10BetaPrimes M)ᶜ) (H := H) ?_ ?_
    · intro p hpH
      have hcard : Nat.card H = Nat.card HC := by
        simpa [H] using
          (Subgroup.card_map_of_injective (K := HC) (f := C.subtype) C.subtype_injective)
      exact hHCHall.p_in_pi_of_p_dvd_card p (by simpa [hcard] using hpH)
    · intro p hpπ hpidx
      have hidx : H.index = HC.index * C.index := by
        simpa [H] using (Subgroup.index_map_subtype (H := C) (K := HC))
      have hp_prod : p.val ∣ HC.index * C.index := by
        simpa [hidx] using hpidx
      rcases p.property.dvd_or_dvd hp_prod with hpHC | hpC
      · exact (hHCHall.p_in_pi_of_p_dvd_index p hpHC) hpπ
      · exact hC_index_no_betaCompl p hpπ hpC
  have hHfix : H ≤ fixedPointSubgroup (Q : Subgroup D) S := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
    exact z.property
  exact ⟨H, hHHall, hHfix⟩

private theorem CFSG.section12_invariant_hall_fixed_by_ambientDerivedSubgroup
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    [Subgroup.Normalizes (ambientDerivedSubgroup E) (section10Msigma M)]
    {H : Subgroup (section10Msigma M)}
    (hHHall : IsHallSubgroup (section10BetaPrimes M)ᶜ H)
    (hHinv : IsInvariant (ambientDerivedSubgroup E) (section10Msigma M) H) :
    H ≤ fixedPointSubgroup (ambientDerivedSubgroup E) (section10Msigma M) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup E
  let S : Subgroup G := section10Msigma M
  have hSproper : S ≠ ⊤ := by
    intro htop
    have hMtop : M = ⊤ := by
      apply eq_top_iff.2
      rw [← htop]
      exact section12_Msigma_le (G := G) M
    exact hM.1 hMtop
  have hSsolv : Group.IsSolvable S :=
    IsMinCE.proper_subgroups_solvable S (lt_top_iff_ne_top.2 hSproper)
  have hDπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ D := by
    simpa [D] using section12_ambientDerivedSubgroup_sigma_compl (G := G) hM hE.1
  have hSπ : IsPiSubgroup (G := G) (section10SigmaPrimes M) S := by
    intro p hp
    exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card p
      (by simpa [S] using hp)
  have hσdisj : Disjoint ((section10SigmaPrimes M)ᶜ : Set Nat.Primes)
      (section10SigmaPrimes M) := by
    rw [Set.disjoint_left]
    intro p hp_not hp
    exact hp_not hp
  have hSylow_fixed :
      ∀ (q : ℕ) (hq : q ∈ (Nat.card D).primeFactors),
        H ≤ fixedPointSubgroup
          (((default : Sylow q D) : Subgroup D)) S := by
    intro q hq
    have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    let _ : Fact q.Prime := ⟨hqprime⟩
    let q' : Nat.Primes := ⟨q, hqprime⟩
    let Q : Sylow q D := default
    have hqD : q'.val ∣ Nat.card D := by
      simpa [q'] using Nat.dvd_of_mem_primeFactors hq
    obtain ⟨L, hLHall, hLfix⟩ :=
      section12_exists_hall_betaCompl_fixed_by_sylow_derivedE
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hE (q := q') Q hqD
    let X : Subgroup G := ((Q : Subgroup D).map D.subtype)
    have hX_le_D : X ≤ D := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hXπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ X :=
      IsPiSubgroup.of_le hX_le_D hDπ
    have hcopX : Nat.Coprime (Nat.card X) (Nat.card S) :=
      section12_coprime_card_of_isPiSubgroup_disjoint_primes_current
        (G := G) hXπ hSπ hσdisj
    have hXcard : Nat.card X = Nat.card (Q : Subgroup D) := by
      simpa [X] using
        (Subgroup.card_map_of_injective
          (K := (Q : Subgroup D)) (f := D.subtype) D.subtype_injective)
    have hcop : Nat.Coprime (Nat.card (Q : Subgroup D)) (Nat.card S) := by
      simpa [hXcard] using hcopX
    let _ : IsInvariant D S H := hHinv
    have hHinvQ : IsInvariant (Q : Subgroup D) S H := by
      refine ⟨?_⟩
      intro a y
      change y ∈ H ↔ (a : D) • y ∈ H
      exact IsInvariant.invariant (A := D) (G := S) (H := H) (a : D) y
    have hLinvQ : IsInvariant (Q : Subgroup D) S L :=
      section12_isInvariant_of_le_fixedPointSubgroup_current hLfix
    obtain ⟨g, hgfix, hH_eq⟩ :=
      proposition_1_5_c
        (G := S) (A := (Q : Subgroup D)) hSsolv hcop
        (section10BetaPrimes M)ᶜ L H hLHall hHHall hLinvQ hHinvQ
    rw [hH_eq]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyL, rfl⟩
    have hyfix : y ∈ fixedPointSubgroup (Q : Subgroup D) S := hLfix hyL
    exact (fixedPointSubgroup (Q : Subgroup D) S).mul_mem
      ((fixedPointSubgroup (Q : Subgroup D) S).mul_mem hgfix hyfix)
      ((fixedPointSubgroup (Q : Subgroup D) S).inv_mem hgfix)
  intro x hxH
  change x ∈ fixedPointSubgroup D S
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  intro d
  let F : Subgroup D := fixingSubgroupOf D S (H : Set S)
  have htop_le_F : (⊤ : Subgroup D) ≤ F := by
    rw [← Sylow.iSup_sylow_eq_top (G := D)]
    refine iSup₂_le ?_
    intro q hq
    have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    let _ : Fact q.Prime := ⟨hqprime⟩
    let Q : Sylow q D := default
    intro a ha
    change a ∈ fixingSubgroupOf D S (H : Set S)
    rw [fixingSubgroupOf, mem_fixingSubgroup_iff]
    intro y hyH
    have hyfix : y ∈ fixedPointSubgroup (Q : Subgroup D) S :=
      hSylow_fixed q hq hyH
    have hya : (⟨a, ha⟩ : (Q : Subgroup D)) • y = y := by
      simpa [fixedPointSubgroup] using hyfix ⟨a, ha⟩
    simpa using hya
  have hdF : d ∈ F := htop_le_F trivial
  exact (mem_fixingSubgroup_iff (M := D) (s := (H : Set S))).1 hdF x hxH

private theorem CFSG.section12_exists_invariant_hall_betaCompl_msigma
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    [Subgroup.Normalizes (ambientDerivedSubgroup E) (section10Msigma M)] :
    ∃ H : Subgroup (section10Msigma M),
      IsHallSubgroup (section10BetaPrimes M)ᶜ H ∧
        IsInvariant (ambientDerivedSubgroup E) (section10Msigma M) H := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup E
  let S : Subgroup G := section10Msigma M
  have hD_le_E : D ≤ E := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (E := E))
  have hD_norm_S : D ≤ Subgroup.normalizer (S : Set G) := by
    exact hD_le_E.trans (hE.1.2.1.trans (by simpa [S] using section12_le_normalizer_msigma (M := M)))
  let _ : Subgroup.Normalizes D S := ⟨hD_norm_S⟩
  have hS_le_M : S ≤ M := by
    simpa [S] using section12_Msigma_le (G := G) M
  have hSproper : S ≠ ⊤ := by
    intro htop
    have hMtop : M = ⊤ := by
      exact eq_top_iff.2 (by simpa [htop] using hS_le_M)
    exact hM.1 hMtop
  have hSsolv : Group.IsSolvable S :=
    IsMinCE.proper_subgroups_solvable S (lt_top_iff_ne_top.2 hSproper)
  have hDπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ D := by
    simpa [D] using section12_ambientDerivedSubgroup_sigma_compl (G := G) hM hE.1
  have hSπ : IsPiSubgroup (G := G) (section10SigmaPrimes M) S := by
    intro p hp
    exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card p
      (by simpa [S] using hp)
  have hσdisj : Disjoint ((section10SigmaPrimes M)ᶜ : Set Nat.Primes)
      (section10SigmaPrimes M) := by
    rw [Set.disjoint_left]
    intro p hp_not hp
    exact hp_not hp
  have hcop : Nat.Coprime (Nat.card D) (Nat.card S) :=
    section12_coprime_card_of_isPiSubgroup_disjoint_primes_current
      (G := G) hDπ hSπ hσdisj
  simpa [D, S] using
    exists_isHallSubgroup_isInvariant
      (G := S) (A := D) hSsolv hcop (section10BetaPrimes M)ᶜ

/-- Lemma 12.19. -/
public theorem CFSG.lemma_12_19
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    ∃ H : Subgroup G,
      section12HallSubgroupIn (section10BetaPrimes M)ᶜ H (section10Msigma M) ∧
        H ≤ Subgroup.centralizer (ambientDerivedSubgroup E : Set G) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup E
  let S : Subgroup G := section10Msigma M
  have hD_le_E : D ≤ E := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (E := E))
  have hD_norm_S : D ≤ Subgroup.normalizer (S : Set G) := by
    exact hD_le_E.trans (hE.1.2.1.trans (by
      simpa [S] using section12_le_normalizer_msigma (M := M)))
  let _ : Subgroup.Normalizes D S := ⟨hD_norm_S⟩
  obtain ⟨Hloc, hHlocHall, hHlocInv⟩ :=
    section12_exists_invariant_hall_betaCompl_msigma
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE
  have hHlocFix :
      Hloc ≤ fixedPointSubgroup D S :=
    section12_invariant_hall_fixed_by_ambientDerivedSubgroup
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE hHlocHall hHlocInv
  let H : Subgroup G := Hloc.map S.subtype
  refine ⟨H, ?_, ?_⟩
  · simpa [H, S] using section12HallSubgroupIn_map_subtype (G := G) hHlocHall
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro d hdD
    rcases Subgroup.mem_map.mp hx with ⟨y, hyH, rfl⟩
    have hyfix : y ∈ fixedPointSubgroup D S := hHlocFix hyH
    have hact : (⟨d, by simpa [D] using hdD⟩ : D) • y = y := by
      simpa [fixedPointSubgroup] using hyfix ⟨d, by simpa [D] using hdD⟩
    have hconj : d * ((y : S) : G) * d⁻¹ = ((y : S) : G) := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, D, S] using
        congrArg Subtype.val hact
    have := congrArg (fun z : G => z * d) hconj
    simpa [mul_assoc] using this

end Section12
