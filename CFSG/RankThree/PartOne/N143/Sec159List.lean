module

public import CFSG.RankThree.PartOne.N143.SectionListConsumers
public import CFSG.RankThree.PartOne.N143.ExtSPEList
public import CFSG.RankThree.PartOne.N143.AutList
public import CFSG.RankThree.PartOne.S12.Sec159Node
public import CFSG.RankThree.PartOne.S12.Sec159Fin
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.RankThree.PartOne.S12.Sec158Defs
public import CFSG.RankThree.PartOne.S12.Sec159Defs
public import CFSG.RankThree.PartOne.S12.Sec159Tr

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne StrongP CFSG.RankThree.PartOne.Sec159Cfg
open scoped commutatorElement

theorem spe_aut_false_list (hSPE : ExtSPEList) (hAut : KF159AutList) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {H : Type} [Group H] [Finite H] {S : Subgroup H} (hS : S.Normal)
    (hS3 : TheoremThreeListHyp ↥S) (hC : Subgroup.centralizer (S : Set H) = ⊥)
    {Y : Subgroup H} (hY : IsStronglyPEmbedded p Y) {P : Subgroup H} (hP : IsSylowOf p P ⊤)
    (hΩ : IsElementaryAbelian p (omegaOne p P)) (hΩcard : Nat.card (omegaOne p P) = p ^ 2)
    (hAutom : Nat.card ↥(torusImage (omegaOne p P) S) ∣ 24 ∧
      ∀ g ∈ torusImage (omegaOne p P) S, orderOf g ≤ 4) : False :=
  hAut p hp hp5 H S hS hS3 hC P hP hΩ hΩcard
    (hSPE p hp hp5 H S hS hS3 hC Y hY P hP hΩ (Or.inl hΩcard)) hAutom

section Cfg

variable {p : ℕ} {M : Type} [Group M] [Finite M] {X E P N : Subgroup M} [X.Normal]
  {θ : Subgroup ↥X} [θ.Characteristic] {b : M}

theorem cfg159_listHyp (h : Cfg159 p X E P N θ b) (hKX : CFSG.IsKGroup ↥X)
    (hlist : Census3.TheoremThreeList ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ))) :
    TheoremThreeListHyp ↥(X.map (QuotientGroup.mk' (actQ X θ).ker)) := by
  obtain ⟨hperf, hsimple, hnonab⟩ := h.quasi
  let e := sIso X θ
  have : IsSimpleGroup ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ)) := hsimple
  refine ⟨e.symm.isSimpleGroup, ?_, ?_, ?_⟩
  · obtain ⟨a, c, hac⟩ := hnonab
    exact ⟨e a, e c, fun hc => hac (e.injective (by simpa [map_mul] using hc))⟩
  · have h0 : CFSG.IsKGroup ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ)) :=
      isKGroup_of_surjective hKX
        ((QuotientGroup.mk' (Subgroup.center (↥X ⧸ θ))).comp (QuotientGroup.mk' θ))
        ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
    exact isKGroup_of_surjective h0 e.toMonoidHom e.surjective
  · exact Census3.TheoremThreeList.of_mulEquiv e hlist

theorem config_false_list (hSPE : ExtSPEList) (hAut : KF159AutList) (h : Cfg159 p X E P N θ b)
    (hKX : CFSG.IsKGroup ↥X)
    (hlist : Census3.TheoremThreeList ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ)))
    {A₀ : Type} [Group A₀] (f : ↥(X ⊓ Subgroup.normalizer (E : Set M)) →* A₀)
    (hA : Nat.card A₀ ∣ 24) (hA' : ∀ a : A₀, orderOf a ≤ 4)
    (hker : ∀ n : ↥(X ⊓ Subgroup.normalizer (E : Set M)), f n = 1 → ∀ e ∈ E,
      (n : M) * e = e * n) : False := by
  have hSN : (X.map (QuotientGroup.mk' (actQ X θ).ker)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  refine spe_aut_false_list hSPE hAut h.prime h.p5 hSN (cfg159_listHyp h hKX hlist) h.centralizer_eq_bot
    h.stronglyPEmbedded_map h.isSylowOf_map ?_ ?_ ?_
  · rw [h.omegaOne_map]
    exact Equivariance.isElementaryAbelian_map h.Eel _
  · rw [h.omegaOne_map]
    exact h.card_map_E
  · rw [h.omegaOne_map]
    exact h.automizer f hA hA' hker

end Cfg

theorem node159Even_of_list (h154 : Node154) (h155 : Node155) (h158 : Node158) (h156 : KF156')
    (hZ : KF159Z) (hList : KF159List) (hSPE : ExtSPEList) (hAut : KF159AutList) :
    Node159Even := by
  classical
  intro G _ _ p A c L E h15 hF hout hEA X hX0
  by_contra hXN
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 := h.three_lt
    by_contra hlt
    have h4 : p = 4 := by omega
    exact absurd (h4 ▸ hp) (by norm_num)
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEcard : Nat.card ↥E = p ^ 3 := hEA ▸ h.A_card
  have hexp : ∀ e ∈ E, e ^ p = 1 := fun e he =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
  have hnonab : ∃ a b : G, a * b ≠ b * a := h.setup.2.1
  have hKP : IsKProper G := h.setup.2.2.1
  have hsimple : IsSimpleGroup G := h.setup.1
  have hN : ∀ B : Subgroup G, B ≤ E → ¬ IsCyclic ↥B →
      Subgroup.normalizer (B : Set G) ≤ lieNormalizer p E := fun B hBE hBcyc =>
    h158 G p A c L E h15 hF hout B (hEA ▸ hBE) hBcyc
  have hx0 : ∃ x ∈ E, x ≠ 1 ∧ X ∈ thetaComponentsAt p x := by
    obtain ⟨B, hB, hXB⟩ := hX0
    obtain ⟨hBE, -, hBcard, -⟩ := hB
    have hBeq : B = E := Subgroup.eq_of_le_of_card_ge hBE (by rw [hEcard, hBcard])
    rw [hBeq] at hXB
    obtain ⟨x, hxE, hx1, hXx⟩ := mem_thetaComponentFamily_iff.1 hXB
    exact ⟨x, hxE, hx1, hXx⟩
  obtain ⟨x, hxE, hx1, hXx⟩ := hx0
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
  have hVN : V ≤ lieNormalizer p E := Sec159.le_of_pPrime_normalized hp hEel hEcard hN hEV hVp
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup G, U = thetaQuotientCentralizer p E X := ⟨_, rfl⟩
  have hUmem : ∀ u, u ∈ U ↔ u ∈ E ∧ u ∈ Subgroup.normalizer (X : Set G) ∧
      ∀ k ∈ X, u * k * u⁻¹ * k⁻¹ ∈ V := by
    intro u; rw [hUdef, hVdef]; exact mem_thetaQuotientCentralizer_iff
  have hUE : U ≤ E := fun u hu => ((hUmem u).1 hu).1
  have hxU : x ∈ U := by
    refine (hUmem x).2 ⟨hxE, hEX hxE, fun k hk => ?_⟩
    have : x * k * x⁻¹ * k⁻¹ = 1 := by rw [hxX k hk]; group
    rw [this]; exact V.one_mem
  have hUcyc : IsCyclic ↥U := by
    by_contra hnc
    exact hXN (Sec159Node.le_of_acts_trivially (p := p) hUE (hEel.isPGroup p ↥E) hVp
      (hUE.trans hEV) hXV hVN (fun u hu k hk => ((hUmem u).1 hu).2.2 k hk) (hN U hUE hnc))
  have hordx : orderOf x = p := orderOf_eq_prime (hexp x hxE) hx1
  have hUx : U = Subgroup.zpowers x := by
    have hdvd := Sec159Node.card_dvd_of_isCyclic_exp hUcyc (fun u hu => hexp u (hUE hu))
    have hle : Subgroup.zpowers x ≤ U := Subgroup.zpowers_le.2 hxU
    have hcard : Nat.card ↥U ≤ Nat.card ↥(Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, hordx]; exact Nat.le_of_dvd hp.pos hdvd
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hL0 : X ∉ thetaCompZeroE p E := fun h0 =>
    hXN ((h156 G p A c L E h15 hF hout X h0).trans Subgroup.le_normalizer)
  have hZp := hZ G p A c L E h15 hF hout hEA X hX0 hL0
  have hRk := hList G p A c L E h15 hF hout hEA X hX0
  obtain ⟨P, hPsyl, hEP, hPW, hPΩ⟩ := Sec159Node.exists_sylow hp h155 (X := X) h15 hF hout hEA
  have hWN : torusNormalizer E ≤ lieNormalizer p E := torusNormalizer_le_lieNormalizer hp E
  obtain ⟨W₀, hW⟩ := h154 G p A c L E h15 hF hout
  have hW4 := Sec159Node.weyl154_perm_four hEA hout hW
  have hbound := Sec159Aut.torusImage_bound hp hexp hxE hx1 hxX hW hW4
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : Subgroup G, M₀ = X ⊔ E := ⟨_, rfl⟩
  have hXM : X ≤ M₀ := hM₀ ▸ le_sup_left
  have hEM : E ≤ M₀ := hM₀ ▸ le_sup_right
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
  have hcfg : Sec159Cfg.Cfg159 p (X.subgroupOf M₀) (E.subgroupOf M₀) (P.subgroupOf M₀)
      ((lieNormalizer p E).subgroupOf M₀) (aschbacherSolvableCore p ↥(X.subgroupOf M₀))
      (⟨x, hEM hxE⟩ : ↥M₀) :=
    { prime := hp
      p5 := hp5
      sup := by rw [← Subgroup.subgroupOf_sup hXM hEM, ← hM₀, Subgroup.subgroupOf_self]
      Eel := Sec159Tr.isElementaryAbelian_subgroupOf hEel
      Ecard := (Sec159Tr.card_subgroupOf hEM).trans hEcard
      θp := (solvable_prime_complement_core_characterization hp).2.2.1
      quasi := CFSG.LocalCores.isQuasisimple_of_mulEquiv ε
        (isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hXx)
      Zp := fun hdvd => hZp (by rwa [Nat.card_congr (Subgroup.centerCongr ε).toEquiv])
      bE := Subgroup.mem_subgroupOf.2 hxE
      b1 := fun h1 => hx1 (congrArg Subtype.val h1)
      bX := fun y hy => Subtype.ext (hxX y.1 (Subgroup.mem_subgroupOf.1 hy))
      hU := by
        intro e' he' hcomm'
        have heE : (e' : G) ∈ E := Subgroup.mem_subgroupOf.1 he'
        have hG : ∀ k ∈ X, (e' : G) * k * (e' : G)⁻¹ * k⁻¹ ∈ V := by
          intro k hk
          have hkX' : (⟨k, hXM hk⟩ : ↥M₀) ∈ X.subgroupOf M₀ := hk
          obtain ⟨t, ht, hteq⟩ := hcomm' _ hkX'
          rw [← hθ'] at ht
          obtain ⟨s, hs, hst⟩ := ht
          have h2 := congrArg (fun z : ↥M₀ => (z : G)) hteq
          refine hVdef ▸ ⟨s, hs, ?_⟩
          rw [← hst] at h2
          have h2' : (((e.symm s : ↥(X.subgroupOf M₀)) : ↥M₀) : G) =
              (e' : G) * k * (e' : G)⁻¹ * k⁻¹ := by simpa using h2
          exact h2'
        have hmemU : (e' : G) ∈ U :=
          (hUmem _).2 ⟨heE, hEX heE, hG⟩
        rw [hUx] at hmemU
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmemU
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
      norm2 := by
        intro B hBE hBcyc
        have hBE' : B.map M₀.subtype ≤ E := by
          rintro _ ⟨b, hb, rfl⟩
          exact Subgroup.mem_subgroupOf.1 (hBE hb)
        have hBcyc' : ¬ IsCyclic ↥(B.map M₀.subtype) := by
          intro hc
          apply hBcyc
          let eB := B.equivMapOfInjective M₀.subtype M₀.subtype_injective
          exact isCyclic_of_surjective eB.symm.toMonoidHom eB.symm.surjective
        exact Sec159Tr.normalizer_subgroupOf_le (hN _ hBE' hBcyc')
      XN := fun hle => hXN (fun y hy =>
        Subgroup.mem_subgroupOf.1 (hle (show (⟨y, hXM hy⟩ : ↥M₀) ∈ X.subgroupOf M₀ from hy))) }
  have hKX' : CFSG.IsKGroup ↥(X.subgroupOf M₀) :=
    Sec159Cfg.isKGroup_of_surjective hKX e.symm.toMonoidHom e.symm.surjective
  have hrk' : Census3.TheoremThreeList
      ((↥(X.subgroupOf M₀) ⧸ aschbacherSolvableCore p ↥(X.subgroupOf M₀)) ⧸
        Subgroup.center (↥(X.subgroupOf M₀) ⧸ aschbacherSolvableCore p ↥(X.subgroupOf M₀))) :=
    Census3.TheoremThreeList.of_mulEquiv (QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)) hRk
  obtain ⟨f, hkerf⟩ := Sec159Tr.exists_aut_hom (M₀ := M₀) (X := X) (E := E) hEM
  have hA : Nat.card ↥(torusImage E X) ∣ 24 := hbound.1
  have hA' : ∀ a : ↥(torusImage E X), orderOf a ≤ 4 := fun a => by
    rw [← Subgroup.orderOf_coe]; exact hbound.2 a a.2
  exact config_false_list hSPE hAut hcfg hKX' hrk' f hA hA' hkerf

end CFSG.RankThree.PartOne.N143
