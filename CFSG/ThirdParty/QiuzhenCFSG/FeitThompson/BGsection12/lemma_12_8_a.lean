module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_7_e

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
public theorem CFSG.section12_eq_top_of_sylow_le_pre
    {R : Type*} [Group R] [Finite R] {L : Subgroup R}
    (hSyl : ∀ (q : ℕ) [Fact q.Prime] (P : Sylow q R), (P : Subgroup R) ≤ L) :
    L = ⊤ := by
  classical
  apply Subgroup.index_eq_one.mp
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro q hqprime hqidx
  have : Fact q.Prime := ⟨hqprime⟩
  let P : Sylow q R := Classical.choice (Sylow.nonempty (p := q) (G := R))
  exact P.not_dvd_index (hqidx.trans (Subgroup.index_dvd_of_le (hSyl q P)))

omit [IsMinCE G] in
public theorem CFSG.section12_nilpotent_le_centralizer_of_pSubgroup_pre
    {R : Type*} [Group R] [Finite R] {A : Subgroup R} {p : Nat.Primes}
    (hnil : Group.IsNilpotent R) (hAp : IsPGroup p.val A)
    (hSylow_comm :
      ∀ P : Sylow p.val R, A ≤ (P : Subgroup R) → IsMulCommutative (P : Subgroup R)) :
    (⊤ : Subgroup R) ≤ Subgroup.centralizer (A : Set R) := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  obtain ⟨P₀, hA_le_P₀⟩ := IsPGroup.exists_le_sylow (G := R) (p := p.val) hAp
  have hP₀_norm : (P₀ : Subgroup R).Normal :=
    Group.IsNilpotent.sylow_normal hnil p.val P₀
  have hP₀_comm : IsMulCommutative (P₀ : Subgroup R) :=
    hSylow_comm P₀ hA_le_P₀
  have hCent_top : Subgroup.centralizer (A : Set R) = ⊤ := by
    apply section12_eq_top_of_sylow_le_pre
    intro q hqprime Q
    by_cases hqp : q = p.val
    · subst q
      have : Unique (Sylow p.val R) := Sylow.unique_of_normal P₀ hP₀_norm
      have hQeq : Q = P₀ := Subsingleton.elim Q P₀
      rw [hQeq]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (setLike_mul_comm
        (s := (P₀ : Subgroup R)) hx (hA_le_P₀ ha)).symm
    · have hQ_norm : (Q : Subgroup R).Normal :=
        Group.IsNilpotent.sylow_normal hnil q Q
      have hdis : Disjoint (Q : Subgroup R) (P₀ : Subgroup R) :=
        IsPGroup.disjoint_of_ne q p.val hqp (Q : Subgroup R) (P₀ : Subgroup R)
          Q.isPGroup' P₀.isPGroup'
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.commute_of_normal_of_disjoint
        (Q : Subgroup R) (P₀ : Subgroup R) hQ_norm hP₀_norm hdis
        x a hx (hA_le_P₀ ha)).eq.symm
  rw [hCent_top]


omit [IsMinCE G] in
public theorem CFSG.section12_fitting_le_centralizer_of_normal_pSubgroup_abelian_sylow_pre
    {H A : Subgroup G} {p : Nat.Primes}
    (hAnorm : section10NormalIn A H)
    (hAp : IsPGroup p.val A)
    (hSylow_comm : ∀ P : Sylow p.val G, IsMulCommutative (P : Subgroup G)) :
    section8FittingSubgroup H ≤ Subgroup.centralizer (A : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  let F : Subgroup G := section8FittingSubgroup H
  have hA_le_F : A ≤ F := by
    have hA_nil : Group.IsNilpotent A := hAp.isNilpotent
    simpa [F, section8FittingSubgroup] using
      section12_le_fittingSubgroupOf_of_normalIn_nilpotent
        (G := G) (H := H) (N := A) hAnorm.1 hAnorm.2 hA_nil
  let A0 : Subgroup F := A.subgroupOf F
  have hA0p : IsPGroup p.val A0 :=
    hAp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := F) hA_le_F).symm
  have hSylow_comm_F :
      ∀ P : Sylow p.val F, A0 ≤ (P : Subgroup F) →
        IsMulCommutative (P : Subgroup F) := by
    intro P _hA0P
    let Pamb : Subgroup G := (P : Subgroup F).map F.subtype
    have hPamb_p : IsPGroup p.val Pamb := by
      simpa [Pamb] using IsPGroup.map P.isPGroup' F.subtype
    obtain ⟨S, hPamb_le_S⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hPamb_p
    have hScomm : IsMulCommutative (S : Subgroup G) := hSylow_comm S
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    have hxPamb : ((x : F) : G) ∈ Pamb :=
      Subgroup.mem_map.mpr ⟨(x : F), x.property, rfl⟩
    have hyPamb : ((y : F) : G) ∈ Pamb :=
      Subgroup.mem_map.mpr ⟨(y : F), y.property, rfl⟩
    exact setLike_mul_comm
      (s := (S : Subgroup G)) (hPamb_le_S hxPamb) (hPamb_le_S hyPamb)
  have hF_cent_A0 : (⊤ : Subgroup F) ≤ Subgroup.centralizer (A0 : Set F) :=
    section12_nilpotent_le_centralizer_of_pSubgroup_pre
      (R := F) (A := A0) (p := p)
      (by simpa [F] using section8FittingSubgroup_isNilpotent H)
      hA0p hSylow_comm_F
  intro x hxF
  rw [Subgroup.mem_centralizer_iff]
  intro a haA
  let xF : F := ⟨x, hxF⟩
  let aF : F := ⟨a, hA_le_F haA⟩
  have hxCent : xF ∈ Subgroup.centralizer (A0 : Set F) := hF_cent_A0 trivial
  have haA0 : aF ∈ A0 := by
    simpa [A0, aF, Subgroup.mem_subgroupOf] using haA
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxCent aF haA0)

omit [IsMinCE G] in
public theorem CFSG.section12_fitting_le_centralizer_of_pSubgroup_le_fitting_abelian_sylow_pre
    {H A : Subgroup G} {p : Nat.Primes}
    (hA_le_F : A ≤ section8FittingSubgroup H)
    (hAp : IsPGroup p.val A)
    (hSylow_comm : ∀ P : Sylow p.val G, IsMulCommutative (P : Subgroup G)) :
    section8FittingSubgroup H ≤ Subgroup.centralizer (A : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  let F : Subgroup G := section8FittingSubgroup H
  let A0 : Subgroup F := A.subgroupOf F
  have hA0p : IsPGroup p.val A0 :=
    hAp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := F) (by simpa [F] using hA_le_F)).symm
  have hSylow_comm_F :
      ∀ P : Sylow p.val F, A0 ≤ (P : Subgroup F) →
        IsMulCommutative (P : Subgroup F) := by
    intro P _hA0P
    let Pamb : Subgroup G := (P : Subgroup F).map F.subtype
    have hPamb_p : IsPGroup p.val Pamb := by
      simpa [Pamb] using IsPGroup.map P.isPGroup' F.subtype
    obtain ⟨S, hPamb_le_S⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hPamb_p
    have hScomm : IsMulCommutative (S : Subgroup G) := hSylow_comm S
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    have hxPamb : ((x : F) : G) ∈ Pamb :=
      Subgroup.mem_map.mpr ⟨(x : F), x.property, rfl⟩
    have hyPamb : ((y : F) : G) ∈ Pamb :=
      Subgroup.mem_map.mpr ⟨(y : F), y.property, rfl⟩
    exact setLike_mul_comm
      (s := (S : Subgroup G)) (hPamb_le_S hxPamb) (hPamb_le_S hyPamb)
  have hF_cent_A0 : (⊤ : Subgroup F) ≤ Subgroup.centralizer (A0 : Set F) :=
    section12_nilpotent_le_centralizer_of_pSubgroup_pre
      (R := F) (A := A0) (p := p)
      (by simpa [F] using section8FittingSubgroup_isNilpotent H)
      hA0p hSylow_comm_F
  intro x hxF
  rw [Subgroup.mem_centralizer_iff]
  intro a haA
  let xF : F := ⟨x, by simpa [F] using hxF⟩
  let aF : F := ⟨a, by simpa [F] using hA_le_F haA⟩
  have hxCent : xF ∈ Subgroup.centralizer (A0 : Set F) := hF_cent_A0 trivial
  have haA0 : aF ∈ A0 := by
    simpa [A0, aF, F, Subgroup.mem_subgroupOf] using haA
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxCent aF haA0)

public theorem CFSG.section12_rankTwo_ne_top_of_minCE_pre
    {H A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p H) :
    A ≠ ⊤ := by
  intro htop
  have : Fact p.val.Prime := ⟨p.2⟩
  have hElem := (section12_rankTwo_elementary hA).2
  have : IsElementaryAbelian p.val A := hElem
  have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
  have htop_p : IsPGroup p.val (⊤ : Subgroup G) :=
    hAp.of_equiv (MulEquiv.subgroupCongr htop)
  have hGp : IsPGroup p.val G :=
    htop_p.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
  have : Group.IsNilpotent G :=
    IsPGroup.isNilpotent (p := p.val) (G := G) (h := hGp)
  exact IsMinCE.not_solvable (G := G) (inferInstance : Group.IsSolvable G)

omit [IsMinCE G] in
public theorem CFSG.section12_all_sylow_comm_of_one_pre
    {p : Nat.Primes} {S : Sylow p.val G}
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    ∀ P : Sylow p.val G, IsMulCommutative (P : Subgroup G) := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  intro P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  have hconj_comm :
      IsMulCommutative ((g • S : Sylow p.val G) : Subgroup G) := by
    let : IsMulCommutative (S : Subgroup G) := hScomm
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.map_isMulCommutative
      (f := (MulAut.conj g).toMonoidHom) (H := (S : Subgroup G))
  rw [← hg]
  exact hconj_comm

omit [IsMinCE G] in
public theorem CFSG.section12_sylow_subgroupOf_normalizer_isHall_pre
    {p : Nat.Primes} (P : Sylow p.val G) :
    IsHallSubgroup ({p} : Set Nat.Primes)
      ((P : Subgroup G).subgroupOf
        (Subgroup.normalizer (((P : Subgroup G) : Set G)))) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let N : Subgroup G := Subgroup.normalizer (((P : Subgroup G) : Set G))
  let Psub : Subgroup N := (P : Subgroup G).subgroupOf N
  let PN : Sylow p.val N := P.subtype (by
    simpa [N] using (Subgroup.le_normalizer : (P : Subgroup G) ≤
      Subgroup.normalizer (((P : Subgroup G) : Set G))))
  have hPsub_eq : Psub = (PN : Subgroup N) := by
    ext x
    simp [Psub, PN, Sylow.subtype, N, Subgroup.mem_subgroupOf]
  refine isHallSubgroup_of (G := N) (π := ({p} : Set Nat.Primes)) (H := Psub) ?_ ?_
  · intro q hq_dvd
    have hPsubp : IsPGroup p.val Psub := by
      rw [hPsub_eq]
      exact PN.isPGroup'
    exact section8_isPiSubgroup_singleton_of_isPGroup hPsubp q hq_dvd
  · intro q hq_mem hq_dvd_index
    have hq_eq : q = p := by simpa using hq_mem
    subst q
    exact PN.not_dvd_index (by simpa [hPsub_eq] using hq_dvd_index)

omit [IsMinCE G] in
public theorem CFSG.section12_exists_complementInNormalizer_pre
    {p : Nat.Primes} (P : Sylow p.val G) :
    ∃ V : Subgroup G, section10ComplementInNormalizer P V := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let N : Subgroup G := Subgroup.normalizer (((P : Subgroup G) : Set G))
  let Psub : Subgroup N := (P : Subgroup G).subgroupOf N
  have hHall : IsHallSubgroup ({p} : Set Nat.Primes) Psub := by
    simpa [Psub, N] using section12_sylow_subgroupOf_normalizer_isHall_pre (G := G) P
  obtain ⟨Vsub, hVsub⟩ :=
    Subgroup.exists_right_complement'_of_coprime
      (N := Psub) hHall.card_coprime_index
  refine ⟨Vsub.map N.subtype, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  · have hVsub_eq : ((Vsub.map N.subtype).subgroupOf N) = Vsub := by
      simpa [N] using (subgroupOf_map_subtype_eq (K := N) Vsub)
    change Psub.IsComplement' ((Vsub.map N.subtype).subgroupOf N)
    rw [hVsub_eq]
    exact hVsub

public theorem CFSG.section12_lemma_12_8_c_core_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G)) (hScomm : IsMulCommutative (S : Subgroup G)) :
    (S : Subgroup G) ≤ ambientDerivedSubgroup (Subgroup.normalizer ((S : Subgroup G) : Set G)) ∧
      ambientDerivedSubgroup (Subgroup.normalizer ((S : Subgroup G) : Set G)) ≤
        section8FittingSubgroup E ∧
      section8FittingSubgroup E ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
      Subgroup.centralizer ((S : Subgroup G) : Set G) ≤ E := by
  classical
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hAnormE : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).1
  have hC_le_E : Subgroup.centralizer (A : Set G) ≤ E := by
    have h6 :=
      corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
    intro x hx
    simpa [h6.2.1] using h6.1 hx
  have hAp : IsPGroup p.val A := by
    have hElem := (section12_rankTwo_elementary hA).2
    have : IsElementaryAbelian p.val A := hElem
    exact IsElementaryAbelian.isPGroup p.val A
  have hSylow_comm_all : ∀ P : Sylow p.val G, IsMulCommutative (P : Subgroup G) :=
    section12_all_sylow_comm_of_one_pre (G := G) (p := p) (S := S) hScomm
  let NA : Subgroup G := Subgroup.normalizer (A : Set G)
  have hA_le_NA : A ≤ NA := by
    simpa [NA] using (Subgroup.le_normalizer : A ≤ Subgroup.normalizer (A : Set G))
  have hAnormNA : section10NormalIn A NA := by
    refine ⟨hA_le_NA, ?_⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hA_le_NA).2 (by simp [NA])
  have hFNA_le_CA :
      section8FittingSubgroup NA ≤ Subgroup.centralizer (A : Set G) :=
    section12_fitting_le_centralizer_of_normal_pSubgroup_abelian_sylow_pre
      (G := G) (H := NA) (A := A) (p := p) hAnormNA hAp hSylow_comm_all
  have hFNA_le_E : section8FittingSubgroup NA ≤ E := hFNA_le_CA.trans hC_le_E
  have hE_le_NA : E ≤ NA := by
    simpa [NA] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAnormE.1).1 hAnormE.2
  have hE_le_norm_FNA :
      E ≤ Subgroup.normalizer (section8FittingSubgroup NA : Set G) :=
    hE_le_NA.trans (section10_le_normalizer_fitting (G := G) NA)
  have hFNA_normE : section10NormalIn (section8FittingSubgroup NA) E := by
    refine ⟨hFNA_le_E, ?_⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hFNA_le_E).2 hE_le_norm_FNA
  have hFNA_le_FE : section8FittingSubgroup NA ≤ section8FittingSubgroup E := by
    simpa [section8FittingSubgroup] using
      section12_le_fittingSubgroupOf_of_normalIn_nilpotent
        (G := G) (H := E) (N := section8FittingSubgroup NA)
        hFNA_normE.1 hFNA_normE.2 (section8FittingSubgroup_isNilpotent NA)
  have hNA_ne_top : NA ≠ ⊤ := by
    simpa [NA] using
      section12_normalizer_ne_top_of_ne_bot_ne_top_pre
        (G := G) (Q := A) (section12_rankTwo_ne_bot hA)
        (section12_rankTwo_ne_top_of_minCE_pre hA)
  have hNAsolv : Group.IsSolvable NA :=
    IsMinCE.proper_subgroups_solvable NA (lt_top_iff_ne_top.2 hNA_ne_top)
  have hNAodd : Odd (Nat.card NA) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card NA)
  have hFNA_rank : groupRank (fittingSubgroup NA) ≤ 2 := by
    let FNA : Subgroup G := section8FittingSubgroup NA
    let eFNA : fittingSubgroup NA ≃* FNA :=
      (MulEquiv.subgroupCongr (section8FittingSubgroup_subgroupOf_eq NA).symm).trans
        (Subgroup.subgroupOfEquivOfLe (H := FNA) (K := NA)
          (section8FittingSubgroup_le NA))
    let FNAE : Subgroup E := FNA.subgroupOf E
    let eFNAE : FNAE ≃* FNA := Subgroup.subgroupOfEquivOfLe (H := FNA) (K := E)
      (by simpa [FNA] using hFNA_le_E)
    have hFNA_rank_le_E : groupRank FNA ≤ groupRank E :=
      (section12_groupRank_le_of_equiv eFNAE).trans
        (section8_groupRank_le_of_subgroup FNAE)
    exact (section12_groupRank_le_of_equiv eFNA.symm).trans
      (hFNA_rank_le_E.trans (section12_groupRank_E_le_two hM hE.1))
  have hDerNA_nil : Group.IsNilpotent (derivedSubgroup NA) :=
    theorem_4_20_a (G := NA) hNAsolv hNAodd (Or.inr hFNA_rank)
  have hDerNA_le_FNA : ambientDerivedSubgroup NA ≤ section8FittingSubgroup NA := by
    have hDer_le_fit : derivedSubgroup NA ≤ fittingSubgroup NA :=
      le_sSup ⟨inferInstance, hDerNA_nil⟩
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyF : y ∈ fittingSubgroup NA := hDer_le_fit hy
    have hyFsub : y ∈ (section8FittingSubgroup NA).subgroupOf NA := by
      simpa [section8FittingSubgroup_subgroupOf_eq NA] using hyF
    exact hyFsub
  have hDerNA_le_FE : ambientDerivedSubgroup NA ≤ section8FittingSubgroup E :=
    hDerNA_le_FNA.trans hFNA_le_FE
  have hSleE : (S : Subgroup G) ≤ E := by
    intro s hs
    exact hC_le_E (by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (setLike_mul_comm
        (s := (S : Subgroup G)) hs (hAS ha)).symm)
  have hSleM : (S : Subgroup G) ≤ M := hSleE.trans hE.1.2.1
  let SM : Sylow p.val M := S.subtype hSleM
  have hSM_eq_S : section10AmbientSylowSubgroup M SM = (S : Subgroup G) := by
    simpa [SM, section10AmbientSylowSubgroup] using
      (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := (S : Subgroup G)) (K := M)
        hSleM)
  have hA_le_SM : A ≤ section10AmbientSylowSubgroup M SM := by
    simpa [hSM_eq_S] using hAS
  have hOmegaS :
      section12OmegaOneSubgroup p (S : Subgroup G) = A := by
    have hOmega :=
      (theorem_12_5_b (G := G) (M := M) (A := A) (p := p)
        hM hp hA_M).2 SM hA_le_SM
    simpa [hSM_eq_S] using hOmega.1
  have hNS_le_NA :
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ NA := by
    have hΩchar :
        (omega₁ (G := (S : Subgroup G)) (p := p.val)).Characteristic :=
      omega₁_characteristic (G := (S : Subgroup G)) (p := p.val)
    have hleΩ :
        Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
          Subgroup.normalizer
            (((omega₁ (G := (S : Subgroup G)) (p := p.val)).map
              (S : Subgroup G).subtype : Subgroup G) : Set G) :=
      section8_normalizer_map_subtype_le_of_characteristic
        (H := (S : Subgroup G))
        (K := omega₁ (G := (S : Subgroup G)) (p := p.val))
    have hΩset_eq :
        (((omega₁ (G := (S : Subgroup G)) (p := p.val)).map
          (S : Subgroup G).subtype : Subgroup G) : Set G) = (A : Set G) := by
      simpa [section12OmegaOneSubgroup] using
        congrArg (fun K : Subgroup G => (K : Set G)) hOmegaS
    simpa [NA, hΩset_eq] using hleΩ
  obtain ⟨V, hVcomp⟩ := section12_exists_complementInNormalizer_pre (G := G) S
  have hS_le_der :
      (S : Subgroup G) ≤ ambientDerivedSubgroup
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) :=
    (corollary_10_7_a (G := G) S hVcomp).1
  have hDerNS_le_FE :
      ambientDerivedSubgroup (Subgroup.normalizer ((S : Subgroup G) : Set G)) ≤
        section8FittingSubgroup E :=
    (section12_ambientDerivedSubgroup_mono hNS_le_NA).trans hDerNA_le_FE
  have hS_le_FE : (S : Subgroup G) ≤ section8FittingSubgroup E :=
    hS_le_der.trans hDerNS_le_FE
  have hFE_le_CS :
      section8FittingSubgroup E ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
    section12_fitting_le_centralizer_of_pSubgroup_le_fitting_abelian_sylow_pre
      (G := G) (H := E) (A := (S : Subgroup G)) (p := p)
      hS_le_FE S.isPGroup' hSylow_comm_all
  have hCS_le_E : Subgroup.centralizer ((S : Subgroup G) : Set G) ≤ E :=
    (Subgroup.centralizer_le (show (A : Set G) ⊆ ((S : Subgroup G) : Set G) from hAS)).trans
      hC_le_E
  exact ⟨hS_le_der, hDerNS_le_FE, hFE_le_CS, hCS_le_E⟩


public theorem CFSG.section12_isMulCommutative_of_nilpotent_of_sylow_pre_pre
    {K : Type*} [Group K] [Finite K]
    (hnil : Group.IsNilpotent K)
    (hSyl : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p K),
      IsMulCommutative (P : Subgroup K)) :
    IsMulCommutative K := by
  classical
  let e : (∀ p : (Nat.card K).primeFactors, ∀ P : Sylow p.val K, P) ≃* K :=
    Sylow.directProductOfNormal (G := K) (fun {p} [hp : Fact p.Prime] (P : Sylow p K) =>
      Group.IsNilpotent.sylow_normal hnil p P)
  refine ⟨⟨fun x y => ?_⟩⟩
  let x' := e.symm x
  let y' := e.symm y
  have hxy' : x' * y' = y' * x' := by
    funext p P
    have : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    have hcomm : IsMulCommutative (P : Subgroup K) := hSyl p.val P
    exact Subtype.ext <|
      setLike_mul_comm (s := (P : Subgroup K))
        (x' p P).property (y' p P).property
  have hxy := congrArg e hxy'
  simpa [x', y'] using hxy

public theorem CFSG.section12_tau2_core_fitting_eq_E2_of_abelian_sylow_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G)) (hScomm : IsMulCommutative (S : Subgroup G)) :
    piCoreIn (section12Tau2Primes M) (section8FittingSubgroup E) = E₂ := by
  classical
  let π : Set Nat.Primes := section12Tau2Primes M
  let F : Subgroup G := section8FittingSubgroup E
  let K : Subgroup G := piCoreIn π F
  have hHallE2 :
      IsHallSubgroup π E₂ := by
    simpa [π] using
      section12_E2_global_hall_of_abelian_sylow_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
        hM hE hp hA hAS hScomm
  have hK_le_F : K ≤ F := by
    simpa [K] using piCoreIn_le (G := G) π F
  have hFnil : Group.IsNilpotent F := by
    simpa [F] using section8FittingSubgroup_isNilpotent E
  have hKHallF : IsHallSubgroup π (K.subgroupOf F) := by
    have hcoreHall : IsHallSubgroup π (piCore π F) :=
      section12_piCore_isHallSubgroup_of_nilpotent hFnil
    simpa [K, piCore_map_subtype_subgroupOf] using hcoreHall
  have hKHall : IsHallSubgroup π K := by
    refine isHallSubgroup_of (G := G) π K ?_ ?_
    · intro q hq
      exact (piCoreIn_isPiSubgroup (G := G) π F) q
        (by simpa [K] using hq)
    · intro q hqπ hqidx
      have hidx_eq : K.relIndex F * F.index = K.index :=
        Subgroup.relIndex_mul_index hK_le_F
      have hqprod : q.val ∣ K.relIndex F * F.index := by
        simpa [hidx_eq] using hqidx
      rcases q.2.dvd_mul.mp hqprod with hqrel | hqFidx
      · exact (hKHallF.p_in_pi_of_p_dvd_index q
          (by simpa [Subgroup.relIndex] using hqrel)) hqπ
      · obtain ⟨B, hB⟩ :=
          section12_exists_rankTwo_in_E_of_tau2
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE (by simpa [π] using hqπ)
        have : Fact q.val.Prime := ⟨q.2⟩
        have hBq : IsPGroup q.val B := by
          have hElem := (section12_rankTwo_elementary hB).2
          have : IsElementaryAbelian q.val B := hElem
          exact IsElementaryAbelian.isPGroup q.val B
        obtain ⟨Q, hB_le_Q⟩ :=
          IsPGroup.exists_le_sylow (G := G) (p := q.val) hBq
        have hQcomm : IsMulCommutative (Q : Subgroup G) :=
          section12_tau2_sylow_comm_of_abelian_sylow_pre
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A)
            (p := p) (q := q) (S := S) Q
            hM hE hp hA hAS hScomm (by simpa [π] using hqπ)
        have hQ_le_F : (Q : Subgroup G) ≤ F := by
          have hcore :=
            section12_lemma_12_8_c_core_pre
              (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
              (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := B)
              (p := q) (S := Q)
              hM hE (by simpa [π] using hqπ) hB hB_le_Q hQcomm
          simpa [F] using hcore.1.trans hcore.2.1
        exact Q.not_dvd_index (hqFidx.trans (Subgroup.index_dvd_of_le hQ_le_F))
  have hE2HallIn :
      section12HallSubgroupIn π E₂ E := by
    simpa [π] using section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
  rcases hE2HallIn with ⟨hE2E, hHallE2E⟩
  have hK_le_E : K ≤ E :=
    hK_le_F.trans (by simpa [F] using section8FittingSubgroup_le E)
  have hE_norm_K : E ≤ Subgroup.normalizer (K : Set G) := by
    simpa [K, F] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (G := G) (π := π) (H := F) (P := E)
        (by simpa [F] using section10_le_normalizer_fitting (G := G) E)
  have hK_normE : (K.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK_le_E).2 hE_norm_K
  have hKπE : IsPiSubgroup (G := E) π (K.subgroupOf E) := by
    intro q hqcard
    have hcard : Nat.card (K.subgroupOf E) = Nat.card K :=
      natCard_subgroupOf_eq K E hK_le_E
    exact (piCoreIn_isPiSubgroup (G := G) π F) q (by simpa [K, hcard] using hqcard)
  have : (K.subgroupOf E).Normal := hK_normE
  have hK_le_E2 : K ≤ E₂ := by
    have hKsub_le_E2sub : K.subgroupOf E ≤ E₂.subgroupOf E :=
      section12_normal_piSubgroup_le_hall
        (R := E) (π := π) (K := K.subgroupOf E) (L := E₂.subgroupOf E)
        hKπE hHallE2E
    intro x hxK
    let xE : E := ⟨x, hK_le_E hxK⟩
    have hxKsub : xE ∈ K.subgroupOf E := by
      simpa [xE, Subgroup.mem_subgroupOf] using hxK
    have hxE2sub : xE ∈ E₂.subgroupOf E := hKsub_le_E2sub hxKsub
    simpa [xE, Subgroup.mem_subgroupOf] using hxE2sub
  have hKE2 : K = E₂ := hKHall.eq_of_le hHallE2 hK_le_E2
  simpa [K, F] using hKE2

/-- Lemma 12.8(a). -/
public theorem CFSG.lemma_12_8_a
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G)) (hScomm : IsMulCommutative (S : Subgroup G)) :
    IsMulCommutative E₂ ∧ section10NormalIn E₂ E := by
  classical
  have hC_le_E : Subgroup.centralizer (A : Set G) ≤ E := by
    have h6 :=
      corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
    intro x hx
    simpa [h6.2.1] using h6.1 hx
  have hSleE : (S : Subgroup G) ≤ E := by
    intro s hs
    exact hC_le_E (by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (setLike_mul_comm
        (s := (S : Subgroup G)) hs (hAS ha)).symm)
  have hHallE2 :
      IsHallSubgroup (section12Tau2Primes M) E₂ :=
    section12_E2_global_hall_of_abelian_sylow_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm
  let F : Subgroup G := section8FittingSubgroup E
  let K : Subgroup G := piCoreIn (section12Tau2Primes M) F
  have hK_eq_E₂ : K = E₂ := by
    simpa [K, F] using
      section12_tau2_core_fitting_eq_E2_of_abelian_sylow_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
        hM hE hp hA hAS hScomm
  have hE2_le_F : E₂ ≤ F := by
    rw [← hK_eq_E₂]
    exact piCoreIn_le (G := G) (section12Tau2Primes M) F
  have hE_norm_K : E ≤ Subgroup.normalizer (K : Set G) := by
    simpa [K, F] using
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (G := G) (π := section12Tau2Primes M) (H := F) (P := E)
        (by simpa [F] using section10_le_normalizer_fitting (G := G) E)
  have hE2norm : section10NormalIn E₂ E := by
    have hE2HallIn :
        section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
      section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
    rcases hE2HallIn with ⟨hE2E, _hHallE2E⟩
    refine ⟨hE2E, ?_⟩
    have hE_norm_E2 : E ≤ Subgroup.normalizer (E₂ : Set G) := by
      simpa [hK_eq_E₂] using hE_norm_K
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hE2E).2 hE_norm_E2
  have hE2nil : Group.IsNilpotent E₂ := by
    have : Group.IsNilpotent F := by
      simpa [F] using section8FittingSubgroup_isNilpotent E
    have hsubnil : Group.IsNilpotent (E₂.subgroupOf F) := by
      infer_instance
    exact Group.nilpotent_of_mulEquiv
      (G := E₂.subgroupOf F) (G' := E₂)
      (Subgroup.subgroupOfEquivOfLe (H := E₂) (K := F) hE2_le_F)
  have hE2comm : IsMulCommutative E₂ :=
    section12_isMulCommutative_of_nilpotent_of_sylow_pre_pre hE2nil
      (fun q hqprime P => by
        classical
        by_cases hPbot : (P : Subgroup E₂) = ⊥
        · rw [hPbot]
          infer_instance
        · let q' : Nat.Primes := ⟨q, hqprime.out⟩
          have hq_dvd_P : q ∣ Nat.card (P : Subgroup E₂) := by
            rcases P.isPGroup'.card_eq_or_dvd with hcard | hdiv
            · exact False.elim
                (hPbot ((Subgroup.card_eq_one (H := (P : Subgroup E₂))).mp hcard))
            · exact hdiv
          have hq_dvd_E2 : q ∣ Nat.card E₂ :=
            hq_dvd_P.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup E₂))
          have hqτ2 : q' ∈ section12Tau2Primes M :=
            hHallE2.p_in_pi_of_p_dvd_card q' (by simpa [q'] using hq_dvd_E2)
          let Pamb : Subgroup G := (P : Subgroup E₂).map E₂.subtype
          have hPamb_p : IsPGroup q Pamb := by
            simpa [Pamb] using IsPGroup.map P.isPGroup' E₂.subtype
          obtain ⟨Q, hPamb_le_Q⟩ :=
            IsPGroup.exists_le_sylow (G := G) (p := q) hPamb_p
          have hQcomm : IsMulCommutative (Q : Subgroup G) :=
            section12_tau2_sylow_comm_of_abelian_sylow_pre
              (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
              (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
              (A := A) (p := p) (q := q') (S := S) Q
              hM hE hp hA hAS hScomm hqτ2
          refine ⟨⟨fun x y => ?_⟩⟩
          apply Subtype.ext
          apply Subtype.ext
          have hxPamb : (((x : (P : Subgroup E₂)) : E₂) : G) ∈ Pamb :=
            Subgroup.mem_map.mpr ⟨((x : (P : Subgroup E₂)) : E₂), x.property, rfl⟩
          have hyPamb : (((y : (P : Subgroup E₂)) : E₂) : G) ∈ Pamb :=
            Subgroup.mem_map.mpr ⟨((y : (P : Subgroup E₂)) : E₂), y.property, rfl⟩
          exact setLike_mul_comm
            (s := (Q : Subgroup G)) (hPamb_le_Q hxPamb) (hPamb_le_Q hyPamb))
  exact ⟨hE2comm, hE2norm⟩


end Section12
