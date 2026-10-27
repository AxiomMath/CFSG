module

public import CFSG.RankThree.PartOne.K1510R.ZGen
public import CFSG.RankThree.PartOne.K1510R.Syl
public import CFSG.RankThree.PartOne.N143.Sec159FiveList
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne.K1510R

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne StrongP CFSG.RankThree.PartOne.Sec159Cfg
  CFSG.RankThree.PartOne.Sec159Five

theorem core_reg
    (h154 : Node154) (h155 : Node155) (h158E3 : S15K.Node158E3) (hSLB : N143.SectionListBound)
    (hZ : KF159ZFiveGen) (hExt : N143.ExtFiveList) {G : Type} [Group G] [Finite G] {p : ℕ}
    {A : Subgroup G} {c : G} {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hout : Outcome152Five p E A (lieGenerated p E))
    (hNn : ∀ B : Subgroup G, B ≤ E → ¬ IsCyclic ↥B →
      Subgroup.normalizer (B : Set G) ≤ lieNormalizer p E)
    {x : G} (hxE : x ∈ E) (hx1 : x ≠ 1) {X : Subgroup G} (hXx : X ∈ thetaComponentsAt p x) :
    X ≤ lieNormalizer p E := by
  classical
  by_contra hXN
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 := h.three_lt
    by_contra hlt
    have h4 : p = 4 := by omega
    exact absurd (h4 ▸ hp) (by norm_num)
  have hout' : Outcome152 p E A (lieGenerated p E) := Or.inr (Or.inr (Or.inr (Or.inr hout)))
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEp : IsPGroup p ↥E := hEel.isPGroup p ↥E
  have hEcard : Nat.card ↥E = p ^ 4 := by
    obtain ⟨-, -, -, -, -, hc, -⟩ := hout
    exact hc
  have hexp : ∀ e ∈ E, e ^ p = 1 := fun e he =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
  have hnonab : ∃ a b : G, a * b ≠ b * a := h.setup.2.1
  have hKP : IsKProper G := h.setup.2.2.1
  have hsimple : IsSimpleGroup G := h.setup.1
  have hrk3 : CFSG.twoLocalOddRank G ≤ 3 := h.setup.2.2.2.2.1.le
  have hordx : orderOf x = p := orderOf_eq_prime (hexp x hxE) hx1
  obtain ⟨A₃, hA₃card, hxA₃, hA₃E⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp
    (H := Subgroup.zpowers x) (L := E) (n := 3)
    (by rw [Nat.card_zpowers, hordx]; exact dvd_pow_self p (by norm_num))
    (by rw [hEcard]; exact pow_dvd_pow p (by norm_num)) (Subgroup.zpowers_le.2 hxE)
  have hxA₃' : x ∈ A₃ := hxA₃ (Subgroup.mem_zpowers x)
  have hA₃el : IsElementaryAbelian p ↥A₃ := Sec159.isElementaryAbelian_of_le hEel hA₃E
  have hNA : ∀ B : Subgroup G, B ≤ A₃ → ¬ IsCyclic ↥B →
      Subgroup.normalizer (B : Set G) ≤ lieNormalizer p E := fun B hBA hBcyc =>
    hNn B (hBA.trans hA₃E) hBcyc
  have hEX : E ≤ Subgroup.normalizer (X : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components hxE hXx
  have hXC : X ≤ Subgroup.centralizer ({x} : Set G) := (mem_thetaComponentsAt_iff.1 hXx).1
  have hxX : ∀ y ∈ X, x * y = y * x := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hXC hy)).symm
  have hXtop : X ≠ ⊤ := by
    intro htop
    exact EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab hx1
      (eq_top_iff.2 (htop ▸ hXC))
  have hKX : CFSG.IsKGroup ↥X := hKP X hXtop
  obtain ⟨V, hVdef⟩ : ∃ V : Subgroup G, V = inSubgroup (aschbacherSolvableCore p) X := ⟨_, rfl⟩
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVdef]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (theta_le_and_normal p X).1).1
      (theta_le_and_normal p X).2
  have hVp : ¬ p ∣ Nat.card ↥V := by
    rw [hVdef]; exact (theta_solvable_and_not_dvd hp X).2
  have hEV : E ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVdef]; exact le_normalizer_theta_of_le_normalizer hp hEX
  have hVN : V ≤ lieNormalizer p E :=
    Sec159.le_of_pPrime_normalized hp hA₃el hA₃card hNA (fun a ha => hEV (hA₃E ha)) hVp
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup G, U = thetaQuotientCentralizer p E X := ⟨_, rfl⟩
  have hUmem : ∀ u, u ∈ U ↔ u ∈ E ∧ u ∈ Subgroup.normalizer (X : Set G) ∧
      ∀ k ∈ X, u * k * u⁻¹ * k⁻¹ ∈ V := by
    intro u; rw [hUdef, hVdef]; exact mem_thetaQuotientCentralizer_iff
  have hxU : x ∈ U := by
    refine (hUmem x).2 ⟨hxE, hEX hxE, fun k hk => ?_⟩
    have : x * k * x⁻¹ * k⁻¹ = 1 := by rw [hxX k hk]; group
    rw [this]; exact V.one_mem
  have hUle : U ≤ E := fun u hu => ((hUmem u).1 hu).1
  have hUcyc : IsCyclic ↥U := by
    by_contra hnc
    exact hXN (Sec159Node.le_of_acts_trivially (p := p) hUle hEp hVp
      (fun u hu => hEV (hUle hu)) hXV hVN
      (fun u hu k hk => ((hUmem u).1 hu).2.2 k hk) (hNn U hUle hnc))
  have hUx : U = Subgroup.zpowers x := by
    have hdvd := Sec159Node.card_dvd_of_isCyclic_exp hUcyc (fun u hu => hexp u (hUle hu))
    have hle : Subgroup.zpowers x ≤ U := Subgroup.zpowers_le.2 hxU
    have hcard : Nat.card ↥U ≤ Nat.card ↥(Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, hordx]; exact Nat.le_of_dvd hp.pos hdvd
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hZp := hZ G p A c L E h15 hF hout x hxE hx1 X hXx
  have hRk := (N143.theoremThreeListHyp_simpleQuot_of_mem_thetaComponentsAt hSLB hKP hrk3 hp hXx
    hXtop).onList
  have hθp : ¬ p ∣ Nat.card ↥(aschbacherSolvableCore p ↥X) :=
    (solvable_prime_complement_core_characterization (H := ↥X) hp).2.2.1
  have hxnot : x ∉ X := not_mem_of_central hp hθp hZp (hexp x hxE) hx1 hxX
  obtain ⟨P, hPsyl, hEP, hPW, hPΩ⟩ :=
    exists_sylow5' hp h155 h15 hF hout hxE hx1 hxX hxnot hEX
  have hWN : torusNormalizer E ≤ lieNormalizer p E := torusNormalizer_le_lieNormalizer hp E
  obtain ⟨W₀, hW⟩ := h154 G p A c L E h15 hF hout'
  have hbound := Sec159Aut.torusImage_bound120 hp hexp hxE hx1 hxX hW hW.2.2.1
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : Subgroup G, M₀ = X ⊔ E := ⟨_, rfl⟩
  have hXM : X ≤ M₀ := hM₀ ▸ le_sup_left
  have hEM : E ≤ M₀ := hM₀ ▸ le_sup_right
  have hAM : A₃ ≤ M₀ := hA₃E.trans hEM
  have hM₀N : M₀ ≤ Subgroup.normalizer (X : Set G) := hM₀ ▸ sup_le Subgroup.le_normalizer hEX
  have hPsyl' : IsSylowOf p P M₀ := hM₀ ▸ hPsyl
  have hX'n : (X.subgroupOf M₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hM₀N
  let e : ↥(X.subgroupOf M₀) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXM
  have hθ' : (aschbacherSolvableCore p ↥X).map e.symm.toMonoidHom =
      aschbacherSolvableCore p ↥(X.subgroupOf M₀) :=
    CFSG.RankThree.PartOne.aschbacherSolvableCore_map_mulEquiv hp e.symm
  let ε : (↥X ⧸ aschbacherSolvableCore p ↥X) ≃*
      (↥(X.subgroupOf M₀) ⧸ aschbacherSolvableCore p ↥(X.subgroupOf M₀)) :=
    QuotientGroup.congr _ _ e.symm hθ'
  have hkerU : ∀ a' : ↥M₀, (a' : G) ∈ E →
      (∀ y ∈ X.subgroupOf M₀, a' * y * a'⁻¹ * y⁻¹ ∈
        (aschbacherSolvableCore p ↥(X.subgroupOf M₀)).map (X.subgroupOf M₀).subtype) →
      (a' : G) ∈ Subgroup.zpowers x := by
    intro a' haE hcomm'
    have hG : ∀ k ∈ X, (a' : G) * k * (a' : G)⁻¹ * k⁻¹ ∈ V := by
      intro k hk
      have hkX' : (⟨k, hXM hk⟩ : ↥M₀) ∈ X.subgroupOf M₀ := hk
      obtain ⟨t, ht, hteq⟩ := hcomm' _ hkX'
      rw [← hθ'] at ht
      obtain ⟨s, hs, hst⟩ := ht
      have h2 := congrArg (fun z : ↥M₀ => (z : G)) hteq
      refine hVdef ▸ ⟨s, hs, ?_⟩
      rw [← hst] at h2
      have h2' : (((e.symm s : ↥(X.subgroupOf M₀)) : ↥M₀) : G) =
          (a' : G) * k * (a' : G)⁻¹ * k⁻¹ := by simpa using h2
      exact h2'
    have hmemU : (a' : G) ∈ U := (hUmem _).2 ⟨haE, hEX haE, hG⟩
    rwa [hUx] at hmemU
  have hcfg : Cfg5 p (X.subgroupOf M₀) (E.subgroupOf M₀) (A₃.subgroupOf M₀) (P.subgroupOf M₀)
      ((lieNormalizer p E).subgroupOf M₀) (aschbacherSolvableCore p ↥(X.subgroupOf M₀))
      (⟨x, hAM hxA₃'⟩ : ↥M₀) :=
    { prime := hp
      p5 := hp5
      sup := by rw [← Subgroup.subgroupOf_sup hXM hEM, ← hM₀, Subgroup.subgroupOf_self]
      Eel := Sec159Tr.isElementaryAbelian_subgroupOf hEel
      Ecard := (Sec159Tr.card_subgroupOf hEM).trans hEcard
      AE := fun y hy => Subgroup.mem_subgroupOf.2 (hA₃E (Subgroup.mem_subgroupOf.1 hy))
      Acard := (Sec159Tr.card_subgroupOf hAM).trans hA₃card
      θp := (solvable_prime_complement_core_characterization hp).2.2.1
      quasi := CFSG.LocalCores.isQuasisimple_of_mulEquiv ε
        (isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hXx)
      Zp := fun hdvd => hZp (by rwa [Nat.card_congr (Subgroup.centerCongr ε).toEquiv])
      xA := Subgroup.mem_subgroupOf.2 hxA₃'
      x1 := fun h1 => hx1 (congrArg Subtype.val h1)
      xX := fun y hy => Subtype.ext (hxX y.1 (Subgroup.mem_subgroupOf.1 hy))
      hA := by
        intro a' ha' hcomm'
        have hmem := hkerU a' (hA₃E (Subgroup.mem_subgroupOf.1 ha')) hcomm'
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
        exact Subgroup.mem_zpowers_iff.2 ⟨j, Subtype.ext (by simpa using hj)⟩
      Psyl := by
        refine ⟨le_top, hPsyl'.2.1.comap_subtype, ?_⟩
        rw [Subgroup.relIndex_top_right]
        exact hPsyl'.2.2
      EP := fun y hy => Subgroup.mem_subgroupOf.2 (hEP (Subgroup.mem_subgroupOf.1 hy))
      PN := fun y hy => Subgroup.mem_subgroupOf.2 (hWN (hPW (Subgroup.mem_subgroupOf.1 hy)))
      Pomega := by
        apply le_antisymm
        · refine (Subgroup.closure_le _).2 ?_
          rintro y ⟨hyP, hy1⟩
          have hyP' : (y : G) ∈ P := Subgroup.mem_subgroupOf.1 hyP
          have hy1' : (y : G) ^ p = 1 := by simpa using congrArg Subtype.val hy1
          have : (y : G) ∈ omegaOne p P := Subgroup.subset_closure ⟨hyP', hy1'⟩
          exact Subgroup.mem_subgroupOf.2 (hPΩ ▸ this)
        · intro y hy
          refine Subgroup.subset_closure ⟨Subgroup.mem_subgroupOf.2
            (hEP (Subgroup.mem_subgroupOf.1 hy)), ?_⟩
          exact Subtype.ext (hexp y (Subgroup.mem_subgroupOf.1 hy))
      normA := by
        intro B hBA hBcyc
        have hBA' : B.map M₀.subtype ≤ A₃ := by
          rintro _ ⟨b, hb, rfl⟩
          exact Subgroup.mem_subgroupOf.1 (hBA hb)
        have hBcyc' : ¬ IsCyclic ↥(B.map M₀.subtype) := by
          intro hc
          apply hBcyc
          let eB := B.equivMapOfInjective M₀.subtype M₀.subtype_injective
          exact isCyclic_of_surjective eB.symm.toMonoidHom eB.symm.surjective
        exact Sec159Tr.normalizer_subgroupOf_le (hNA _ hBA' hBcyc')
      normE := by
        intro R hRE hR
        have hRE' : R.map M₀.subtype ≤ E := by
          rintro _ ⟨b, hb, rfl⟩
          exact Subgroup.mem_subgroupOf.1 (hRE hb)
        have hRcard : p ^ 3 ≤ Nat.card ↥(R.map M₀.subtype) := by
          rw [Subgroup.card_map_of_injective M₀.subtype_injective]; exact hR
        exact Sec159Tr.normalizer_subgroupOf_le (h158E3 G p A c L E h15 hF hout _ hRE' hRcard)
      XN := fun hle => hXN (fun y hy =>
        Subgroup.mem_subgroupOf.1 (hle (show (⟨y, hXM hy⟩ : ↥M₀) ∈ X.subgroupOf M₀ from hy))) }
  have hKX' : CFSG.IsKGroup ↥(X.subgroupOf M₀) :=
    Sec159Cfg.isKGroup_of_surjective hKX e.symm.toMonoidHom e.symm.surjective
  have hrk' : Census3.TheoremThreeList
      ((↥(X.subgroupOf M₀) ⧸ aschbacherSolvableCore p ↥(X.subgroupOf M₀)) ⧸
        Subgroup.center (↥(X.subgroupOf M₀) ⧸ aschbacherSolvableCore p ↥(X.subgroupOf M₀))) :=
    Census3.TheoremThreeList.of_mulEquiv
      (QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)) hRk
  obtain ⟨f, hkerf⟩ := Sec159Tr.exists_aut_hom (M₀ := M₀) (X := X) (E := E) hEM
  have hA120 : Nat.card ↥(torusImage E X) ∣ 120 := hbound.1
  have hA6 : ∀ a : ↥(torusImage E X), orderOf a ≤ 6 := fun a => by
    rw [← Subgroup.orderOf_coe]; exact hbound.2 a a.2
  have hU1 : Nat.card ↥((actQ (X.subgroupOf M₀)
      (aschbacherSolvableCore p ↥(X.subgroupOf M₀))).ker ⊓ E.subgroupOf M₀ : Subgroup ↥M₀) = p := by
    rcases hcfg.card_U_cases with hU1 | hU2
    · exact hU1
    · exfalso
      have hle : ((actQ (X.subgroupOf M₀)
          (aschbacherSolvableCore p ↥(X.subgroupOf M₀))).ker ⊓ E.subgroupOf M₀ :
            Subgroup ↥M₀).map M₀.subtype ≤ Subgroup.zpowers x := by
        rintro _ ⟨a', ha', rfl⟩
        exact hkerU a' (Subgroup.mem_subgroupOf.1 ha'.2) (mem_ker_actQ.1 ha'.1)
      have h1 := Subgroup.card_le_of_le hle
      rw [Subgroup.card_map_of_injective M₀.subtype_injective, hU2, Nat.card_zpowers, hordx] at h1
      have h2 : p < p ^ 2 := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
  exact N143.cfg5_false_of_five_list hExt hcfg hU1 hKX' hrk' f hA120 hA6 hkerf

end CFSG.RankThree.PartOne.K1510R
