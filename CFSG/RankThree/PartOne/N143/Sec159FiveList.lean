module

public import CFSG.RankThree.PartOne.N143.SectionListConsumers
public import CFSG.RankThree.PartOne.N143.ExtSPEList
public import CFSG.RankThree.PartOne.N143.ExtFiveList
public import CFSG.RankThree.PartOne.N143.AutList
public import CFSG.RankThree.PartOne.S12.Sec159FiveSyl
public import CFSG.RankThree.PartOne.S12.Sec159FiveAut
public import CFSG.RankThree.PartOne.S12.Sec159Node
public import CFSG.RankThree.PartOne.S15K.Node158E3
public import CFSG.RankThree.PartOne.S12.Sec159FiveFin
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
public import CFSG.RankThree.PartOne.S12.Sec159FiveDefs

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne StrongP CFSG.RankThree.PartOne.Sec159Cfg
  CFSG.RankThree.PartOne.Sec159Five

section Cfg

variable {p : ℕ} {M : Type} [Group M] [Finite M] {X E A P N : Subgroup M} [X.Normal]
  {θ : Subgroup ↥X} [θ.Characteristic] {x : M}

theorem cfg5_listHyp (h : Cfg5 p X E A P N θ x) (hKX : CFSG.IsKGroup ↥X)
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

theorem cfg5_false_of_spe_list (hSPE : ExtSPEList) (hAut : KF159Aut5List) (h : Cfg5 p X E A P N θ x)
    (hU : Nat.card ↥((actQ X θ).ker ⊓ E : Subgroup M) = p ^ 2)
    (hKX : CFSG.IsKGroup ↥X)
    (hlist : Census3.TheoremThreeList ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ)))
    {A₀ : Type} [Group A₀] (f : ↥(X ⊓ Subgroup.normalizer (E : Set M)) →* A₀)
    (hA : Nat.card A₀ ∣ 120) (hA' : ∀ a : A₀, orderOf a ≤ 6)
    (hker : ∀ n : ↥(X ⊓ Subgroup.normalizer (E : Set M)), f n = 1 → ∀ e ∈ E,
      (n : M) * e = e * n)
    (hSz : Census3.IsoLie ↥(X.map (QuotientGroup.mk' (actQ X θ).ker)) (.suzuki 2) → False) :
    False := by
  have hSN : (X.map (QuotientGroup.mk' (actQ X θ).ker)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hS3 := cfg5_listHyp h hKX hlist
  have hΩel : IsElementaryAbelian p (omegaOne p (P.map (QuotientGroup.mk' (actQ X θ).ker))) := by
    rw [h.omegaOne_map]
    exact Equivariance.isElementaryAbelian_map h.Eel _
  have hΩcard : Nat.card (omegaOne p (P.map (QuotientGroup.mk' (actQ X θ).ker))) = p ^ 2 := by
    rw [h.omegaOne_map]
    have h1 := h.card_map_E
    rw [hU] at h1
    have : Nat.card ↥(E.map (QuotientGroup.mk' (actQ X θ).ker)) * p ^ 2 = p ^ 2 * p ^ 2 := by
      rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos h.prime.pos 2) this
  have hbound : Nat.card ↥(torusImage (omegaOne p (P.map (QuotientGroup.mk' (actQ X θ).ker)))
        (X.map (QuotientGroup.mk' (actQ X θ).ker))) ∣ 120 ∧
      ∀ g ∈ torusImage (omegaOne p (P.map (QuotientGroup.mk' (actQ X θ).ker)))
        (X.map (QuotientGroup.mk' (actQ X θ).ker)), orderOf g ≤ 6 := by
    rw [h.omegaOne_map]
    exact h.automizer f hA hA' hker
  have hlist := hSPE p h.prime h.p5 _ _ hSN hS3 h.centralizer_eq_bot _
    (h.stronglyPEmbedded_map hU) _ h.isSylowOf_map hΩel (Or.inl hΩcard)
  rcases hlist with hL2 | ⟨hp5, hA10 | htits | hsz⟩
  · exact hAut p h.prime h.p5 _ _ hSN hS3 h.centralizer_eq_bot _ h.isSylowOf_map hΩel hΩcard
      (Or.inl hL2) hbound
  · exact hAut p h.prime h.p5 _ _ hSN hS3 h.centralizer_eq_bot _ h.isSylowOf_map hΩel hΩcard
      (Or.inr ⟨hp5, Or.inl hA10⟩) hbound
  · exact hAut p h.prime h.p5 _ _ hSN hS3 h.centralizer_eq_bot _ h.isSylowOf_map hΩel hΩcard
      (Or.inr ⟨hp5, Or.inr htits⟩) hbound
  · exact hSz hsz

theorem cfg5_false_of_five_list (hExt : ExtFiveList) (h : Cfg5 p X E A P N θ x)
    (hU : Nat.card ↥((actQ X θ).ker ⊓ E : Subgroup M) = p)
    (hKX : CFSG.IsKGroup ↥X)
    (hlist : Census3.TheoremThreeList ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ)))
    {A₀ : Type} [Group A₀] (f : ↥(X ⊓ Subgroup.normalizer (E : Set M)) →* A₀)
    (hA : Nat.card A₀ ∣ 120) (hA' : ∀ a : A₀, orderOf a ≤ 6)
    (hker : ∀ n : ↥(X ⊓ Subgroup.normalizer (E : Set M)), f n = 1 → ∀ e ∈ E,
      (n : M) * e = e * n) :
    False := by
  have : Fact p.Prime := ⟨h.prime⟩
  set K := (actQ X θ).ker with hK
  set π := QuotientGroup.mk' K with hπ
  have hSN : (X.map π).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hS3 := cfg5_listHyp h hKX hlist
  have hΩel : IsElementaryAbelian p (omegaOne p (P.map π)) := by
    rw [h.omegaOne_map]
    exact Equivariance.isElementaryAbelian_map h.Eel _
  have hΩcard : Nat.card (omegaOne p (P.map π)) = p ^ 3 := by
    rw [h.omegaOne_map]
    have h1 := h.card_map_E
    rw [hU] at h1
    have : Nat.card ↥(E.map π) * p = p ^ 3 * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right h.prime.pos this
  have hbound : Nat.card ↥(torusImage (omegaOne p (P.map π)) (X.map π)) ∣ 120 ∧
      ∀ g ∈ torusImage (omegaOne p (P.map π)) (X.map π), orderOf g ≤ 6 := by
    rw [h.omegaOne_map]
    exact h.automizer f hA hA' hker
  have hAcard : Nat.card ↥(A.map π) = p ^ 2 := h.card_map_A
  have hAΩ : A.map π ≤ omegaOne p (P.map π) := by
    rw [h.omegaOne_map]; exact Subgroup.map_mono h.AE
  have hgen := hExt p h.prime h.p5 _ _ hSN hS3 h.centralizer_eq_bot _ h.isSylowOf_map hΩel hΩcard
    hbound (A.map π) hAΩ hAcard
  have hSle : X.map π ≤ N.map π := by
    refine hgen.symm.le.trans ((Subgroup.closure_le _).2 ?_)
    rintro s ⟨hsS, F', hF'A, hF'1, hF'c⟩
    have hsn : s ∈ Subgroup.normalizer (F' : Set (M ⧸ K)) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hF'c)
    exact h.normalizer_le hF'A hF'1 hsn
  have hXN : X ≤ N := by
    intro y hy
    have h1 : π y ∈ N.map π := hSle ⟨y, hy, rfl⟩
    have h2 : y ∈ (N.map π).comap π := h1
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
    exact (sup_le le_rfl h.ker_le_N) h2
  exact h.XN hXN

end Cfg

theorem node159Five_core_of_list
    (h154 : Node154) (h155 : Node155) (h158 : Node158) (h158E3 : S15K.Node158E3) (h156 : KF156')
    (hZ : KF159ZFive) (hList : KF159ListFive) (hSPE : ExtSPEList) (hAut : KF159Aut5List)
    (hSz : KF159Sz) (hExt : ExtFiveList) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
      ∀ X ∈ thetaComponentFamily p A, X ≤ lieNormalizer p E := by
  classical
  intro G _ _ p A c L E h15 hF hout X hXA
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
  have hAE : A ≤ E := h.A_le_E
  have hAel : IsElementaryAbelian p ↥A := h.A_elem
  have hAcard : Nat.card ↥A = p ^ 3 := h.A_card
  have hexp : ∀ e ∈ E, e ^ p = 1 := fun e he =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
  have hnonab : ∃ a b : G, a * b ≠ b * a := h.setup.2.1
  have hKP : IsKProper G := h.setup.2.2.1
  have hsimple : IsSimpleGroup G := h.setup.1
  have hNA : ∀ B : Subgroup G, B ≤ A → ¬ IsCyclic ↥B →
      Subgroup.normalizer (B : Set G) ≤ lieNormalizer p E := fun B hBA hBcyc =>
    h158 G p A c L E h15 hF hout' B hBA hBcyc
  obtain ⟨x, hxA, hx1, hXx⟩ := mem_thetaComponentFamily_iff.1 hXA
  have hxE : x ∈ E := hAE hxA
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
    Sec159.le_of_pPrime_normalized hp hAel hAcard hNA (fun a ha => hEV (hAE ha)) hVp
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup G, U = thetaQuotientCentralizer p E X := ⟨_, rfl⟩
  have hUmem : ∀ u, u ∈ U ↔ u ∈ E ∧ u ∈ Subgroup.normalizer (X : Set G) ∧
      ∀ k ∈ X, u * k * u⁻¹ * k⁻¹ ∈ V := by
    intro u; rw [hUdef, hVdef]; exact mem_thetaQuotientCentralizer_iff
  have hxU : x ∈ U := by
    refine (hUmem x).2 ⟨hxE, hEX hxE, fun k hk => ?_⟩
    have : x * k * x⁻¹ * k⁻¹ = 1 := by rw [hxX k hk]; group
    rw [this]; exact V.one_mem
  have hUAle : A ⊓ U ≤ E := inf_le_left.trans hAE
  have hUAcyc : IsCyclic ↥(A ⊓ U) := by
    by_contra hnc
    exact hXN (Sec159Node.le_of_acts_trivially (p := p) hUAle hEp hVp
      (fun u hu => hEV (hUAle hu)) hXV hVN
      (fun u hu k hk => ((hUmem u).1 hu.2).2.2 k hk) (hNA (A ⊓ U) inf_le_left hnc))
  have hordx : orderOf x = p := orderOf_eq_prime (hexp x hxE) hx1
  have hUAx : A ⊓ U = Subgroup.zpowers x := by
    have hdvd := Sec159Node.card_dvd_of_isCyclic_exp hUAcyc (fun u hu => hexp u (hUAle hu))
    have hle : Subgroup.zpowers x ≤ A ⊓ U := Subgroup.zpowers_le.2 ⟨hxA, hxU⟩
    have hcard : Nat.card ↥(A ⊓ U) ≤ Nat.card ↥(Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, hordx]; exact Nat.le_of_dvd hp.pos hdvd
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hX0 : X ∈ thetaCompE p E := by
    refine ⟨A, ⟨hAE, hAel, hAcard, ?_⟩, hXA⟩
    exact h.setup.2.2.2.2.2.2.2.2.1
  have hL0 : X ∉ thetaCompZeroE p E := fun h0 =>
    hXN ((h156 G p A c L E h15 hF hout' X h0).trans Subgroup.le_normalizer)
  have hZp := hZ G p A c L E h15 hF hout X hX0 hL0
  have hRk := hList G p A c L E h15 hF hout X hX0
  have hθp : ¬ p ∣ Nat.card ↥(aschbacherSolvableCore p ↥X) :=
    (solvable_prime_complement_core_characterization (H := ↥X) hp).2.2.1
  have hxnot : x ∉ X := not_mem_of_central hp hθp hZp (hexp x hxE) hx1 hxX
  obtain ⟨P, hPsyl, hEP, hPW, hPΩ⟩ :=
    exists_sylow5 hp h155 h15 hF hout hxA hx1 hxX hxnot hEX
  have hWN : torusNormalizer E ≤ lieNormalizer p E := torusNormalizer_le_lieNormalizer hp E
  obtain ⟨W₀, hW⟩ := h154 G p A c L E h15 hF hout'
  have hbound := Sec159Aut.torusImage_bound120 hp hexp hxE hx1 hxX hW hW.2.2.1
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : Subgroup G, M₀ = X ⊔ E := ⟨_, rfl⟩
  have hXM : X ≤ M₀ := hM₀ ▸ le_sup_left
  have hEM : E ≤ M₀ := hM₀ ▸ le_sup_right
  have hAM : A ≤ M₀ := hAE.trans hEM
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
  have hVθ : ∀ (g : ↥M₀), (∀ k ∈ X, (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ V) →
      g ∈ (Sec159Cfg.actQ (X.subgroupOf M₀) (aschbacherSolvableCore p ↥(X.subgroupOf M₀))).ker := by
    intro g hg
    rw [Sec159Cfg.mem_ker_actQ]
    intro z' hz'
    have hzX : (z' : G) ∈ X := Subgroup.mem_subgroupOf.1 hz'
    have hmem := hg (z' : G) hzX
    rw [hVdef] at hmem
    obtain ⟨t, ht, hteq⟩ := hmem
    refine ⟨e.symm t, ?_, ?_⟩
    · rw [← hθ']; exact Subgroup.mem_map_of_mem _ ht
    · apply Subtype.ext
      show (((e.symm t : ↥(X.subgroupOf M₀)) : ↥M₀) : G) = ((g * z' * g⁻¹ * z'⁻¹ : ↥M₀) : G)
      have h1 : (((e.symm t : ↥(X.subgroupOf M₀)) : ↥M₀) : G) = ((t : ↥X) : G) := rfl
      rw [h1]
      have h3 : ((t : ↥X) : G) = (g : G) * (z' : G) * (g : G)⁻¹ * (z' : G)⁻¹ := hteq
      rw [h3]
      simp
  have hcfg : Cfg5 p (X.subgroupOf M₀) (E.subgroupOf M₀) (A.subgroupOf M₀) (P.subgroupOf M₀)
      ((lieNormalizer p E).subgroupOf M₀) (aschbacherSolvableCore p ↥(X.subgroupOf M₀))
      (⟨x, hAM hxA⟩ : ↥M₀) :=
    { prime := hp
      p5 := hp5
      sup := by rw [← Subgroup.subgroupOf_sup hXM hEM, ← hM₀, Subgroup.subgroupOf_self]
      Eel := Sec159Tr.isElementaryAbelian_subgroupOf hEel
      Ecard := (Sec159Tr.card_subgroupOf hEM).trans hEcard
      AE := fun y hy => Subgroup.mem_subgroupOf.2 (hAE (Subgroup.mem_subgroupOf.1 hy))
      Acard := (Sec159Tr.card_subgroupOf hAM).trans hAcard
      θp := (solvable_prime_complement_core_characterization hp).2.2.1
      quasi := CFSG.LocalCores.isQuasisimple_of_mulEquiv ε
        (isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hXx)
      Zp := fun hdvd => hZp (by rwa [Nat.card_congr (Subgroup.centerCongr ε).toEquiv])
      xA := Subgroup.mem_subgroupOf.2 hxA
      x1 := fun h1 => hx1 (congrArg Subtype.val h1)
      xX := fun y hy => Subtype.ext (hxX y.1 (Subgroup.mem_subgroupOf.1 hy))
      hA := by
        intro a' ha' hcomm'
        have haA : (a' : G) ∈ A := Subgroup.mem_subgroupOf.1 ha'
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
        have hmemU : (a' : G) ∈ U :=
          (hUmem _).2 ⟨hAE haA, hEX (hAE haA), hG⟩
        have hmemAU : (a' : G) ∈ A ⊓ U := ⟨haA, hmemU⟩
        rw [hUAx] at hmemAU
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmemAU
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
        have hBA' : B.map M₀.subtype ≤ A := by
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
    Census3.TheoremThreeList.of_mulEquiv (QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)) hRk
  obtain ⟨f, hkerf⟩ := Sec159Tr.exists_aut_hom (M₀ := M₀) (X := X) (E := E) hEM
  have hA120 : Nat.card ↥(torusImage E X) ∣ 120 := hbound.1
  have hA6 : ∀ a : ↥(torusImage E X), orderOf a ≤ 6 := fun a => by
    rw [← Subgroup.orderOf_coe]; exact hbound.2 a a.2
  rcases hcfg.card_U_cases with hU1 | hU2
  · exact cfg5_false_of_five_list hExt hcfg hU1 hKX' hrk' f hA120 hA6 hkerf
  · refine cfg5_false_of_spe_list hSPE hAut hcfg hU2 hKX' hrk' f hA120 hA6 hkerf ?_
    intro hiso
    have hisoG : Census3.IsoLie ((↥X ⧸ aschbacherSolvableCore p ↥X) ⧸
        Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X)) (.suzuki 2) := by
      have e2 := QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)
      obtain ⟨hv, ⟨φ⟩⟩ := hiso
      exact ⟨hv, ⟨(e2.trans (Sec159Cfg.sIso (X.subgroupOf M₀)
        (aschbacherSolvableCore p ↥(X.subgroupOf M₀)))).trans φ⟩⟩
    have hinn := hSz G p A c L E h15 hF hout X hX0 hisoG
    refine hcfg.false_of_sz hU2 ?_ hiso
    intro e' he'
    obtain ⟨y, hy, hyC⟩ := hinn e' (Subgroup.mem_subgroupOf.1 he')
    have hyC' := mem_thetaQuotientCentralizer_iff.1 hyC
    set y' : ↥M₀ := ⟨y, hXM hy⟩ with hy'
    have hy'X : y' ∈ X.subgroupOf M₀ := Subgroup.mem_subgroupOf.2 hy
    have hker : y'⁻¹ * e' ∈
        (Sec159Cfg.actQ (X.subgroupOf M₀) (aschbacherSolvableCore p ↥(X.subgroupOf M₀))).ker := by
      apply hVθ
      intro k hk
      have := hyC'.2.2 k hk
      rw [← hVdef] at this
      simpa using this
    have := Subgroup.mul_mem_sup hy'X hker
    simpa using this

end CFSG.RankThree.PartOne.N143
