module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Normal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Quot
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.GroupTheory.IsCyclicOfPRankLeOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

private theorem r925_isElemAbelian_card_three {G : Type} [Group G] [Finite G] {D : Subgroup G}
    (hD : Nat.card D = 3) : CFSG.Open.IsElemAbelian 3 D := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic ↥D := isCyclic_of_prime_card hD
  refine ⟨inferInstance, fun x hx => ?_⟩
  have h1 : orderOf x ∣ 3 := by
    rw [← hD]
    exact Subgroup.orderOf_dvd_natCard D hx
  exact orderOf_dvd_iff_pow_eq_one.mp h1

private theorem r925_pPrimeCore_modO3p_eq_bot {Γ : Type} [Group Γ] [Finite Γ] :
    CFSG.pPrimeCore 3 (ModO3p Γ) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3

private theorem r925_eq_of_card_prime_of_isCyclic {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {S : Subgroup G} (hcyc : IsCyclic ↥S)
    {H₁ H₂ : Subgroup G} (h₁ : H₁ ≤ S) (h₂ : H₂ ≤ S)
    (hc₁ : Nat.card H₁ = p) (hc₂ : Nat.card H₂ = p) : H₁ = H₂ := by
  have hsub : H₁.subgroupOf S = H₂.subgroupOf S := by
    rw [IsCyclic.subgroup_eq_iff_card_eq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁).toEquiv).trans
      (hc₁.trans ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₂).toEquiv).trans hc₂).symm)
  have hmap := congrArg (Subgroup.map S.subtype) hsub
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h₁,
       Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h₂] at hmap

private theorem r925_exists_smul_conj_of_card_prime_of_pRank_le_one
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 1)
    {H₁ H₂ : Subgroup G} (hc₁ : Nat.card H₁ = p) (hc₂ : Nat.card H₂ = p) :
    ∃ g : G, H₂ = MulAut.conj g • H₁ := by
  have hP₁ : IsPGroup p H₁ := IsPGroup.of_card (n := 1) (by rw [hc₁, pow_one])
  have hP₂ : IsPGroup p H₂ := IsPGroup.of_card (n := 1) (by rw [hc₂, pow_one])
  obtain ⟨P₁, hH₁P₁⟩ := hP₁.exists_le_sylow
  obtain ⟨P₂, hH₂P₂⟩ := hP₂.exists_le_sylow
  have hp : p.Prime := Fact.out
  have hcyc₁ : IsCyclic ↥P₁ := by
    refine CFSG.isCyclic_of_pRank_le_one hp hp2 P₁.isPGroup' ?_
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (P₁ : Subgroup G)]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hrank
  have hcyc₂ : IsCyclic ↥P₂ := by
    refine CFSG.isCyclic_of_pRank_le_one hp hp2 P₂.isPGroup' ?_
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (P₂ : Subgroup G)]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hrank
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₁ P₂
  refine ⟨g, ?_⟩
  have hPmap : MulAut.conj g • (P₁ : Subgroup G) = (P₂ : Subgroup G) := by
    have h := congrArg (fun S : Sylow p G => (S : Subgroup G)) hg
    rwa [Sylow.coe_subgroup_smul] at h
  have hle : MulAut.conj g • H₁ ≤ P₂ := by
    rw [← hPmap]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hH₁P₁
  have hcard : Nat.card (MulAut.conj g • H₁ : Subgroup G) = p := by
    change Nat.card (↥(H₁.map (MulAut.conj g : G →* G))) = p
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc₁]
  exact r925_eq_of_card_prime_of_isCyclic (p := p) hcyc₂ hH₂P₂ hle hc₂ hcard

private theorem r925_normalizer_le_normalizer_of_isCyclic_card_prime
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P D : Subgroup G}
    (hcyc : IsCyclic ↥P) (hDP : D ≤ P) (hD : Nat.card D = p) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (D : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
  have hDP' : D.map (MulAut.conj x : G →* G) ≤ P := by
    rw [← hx]
    exact Subgroup.map_mono hDP
  have hcard : Nat.card (D.map (MulAut.conj x : G →* G)) = p := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hD]
  exact r925_eq_of_card_prime_of_isCyclic (p := p) hcyc hDP' hDP hcard hD

private theorem r925_closure_orderOf_dvd_of_normalClosure {G : Type} [Group G] {T : Set G}
    (hord : ∀ x ∈ T, orderOf x ∣ 3) :
    Subgroup.closure {x : G | x ∈ Subgroup.normalClosure T ∧ orderOf x ∣ 3} =
      Subgroup.normalClosure T := by
  apply le_antisymm
  · exact (Subgroup.closure_le (Subgroup.normalClosure T)).mpr fun x hx => hx.1
  · change Subgroup.closure (Group.conjugatesOfSet T) ≤
      Subgroup.closure {x : G | x ∈ Subgroup.normalClosure T ∧ orderOf x ∣ 3}
    apply Subgroup.closure_mono
    intro x hx
    refine ⟨Subgroup.conjugatesOfSet_subset_normalClosure hx, ?_⟩
    obtain ⟨a, haT, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, hc⟩ := hconj
    rw [← SemiconjBy.orderOf_eq (c : G) hc]
    exact hord a haT

theorem R925Ctx.normal_k {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) : K.Normal := by
  rw [h.k_eq]
  infer_instance

theorem R925Ctx.y_le_k {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) : Y ≤ K := by
  rw [h.k_eq]
  exact Subgroup.le_normalClosure

theorem R925Ctx.perfect_k {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) : commutator ↥K = ⊤ := by
  rw [h.k_eq]
  exact commutator_normalClosure h.y_cover.1

theorem R925Ctx.threeGen_k {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) : IsThreeGen K := by
  rw [h.k_eq]
  exact h.y_cover.isThreeGen.normalClosure

private theorem r925_kbar_pRank_aux {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) : CFSG.Open.pRank 3 (K.map (toModO3p Γ)) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ : ∀ x ∈ CFSG.pPrimeCore 3 Γ, ¬ 3 ∣ orderOf x := r925_pPrimeCore_orderOf
  refine le_antisymm ?_ ?_
  · calc CFSG.Open.pRank 3 (K.map (toModO3p Γ))
        ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (ModO3p Γ)) :=
          CFSG.SectionRank.pRank_mono (by norm_num) le_top
      _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Γ) := r925_pRank_quotient_le _ Nat.prime_three hJ
      _ ≤ 1 := h.rank_three
  · obtain ⟨D, hDY, hD3⟩ := h.y_cover.exists_subgroup_card_three
    have hcard : Nat.card (D.map (toModO3p Γ)) = 3 := r925_card_map_eq_three hJ hD3
    have hel : CFSG.Open.IsElemAbelian 3 (D.map (toModO3p Γ)) :=
      r925_isElemAbelian_card_three hcard
    have hle : D.map (toModO3p Γ) ≤ K.map (toModO3p Γ) :=
      Subgroup.map_mono (hDY.trans h.y_le_k)
    have := CFSG.SectionRank.le_pRank (p := 3) (G := ModO3p Γ) (H := K.map (toModO3p Γ))
      (E := D.map (toModO3p Γ)) (by norm_num) hle hel (k := 1) (by rw [hcard, pow_one])
    simpa using this

theorem r925_sup_eq_top {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) : K ⊔ M = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hKn : K.Normal := h.normal_k
  obtain ⟨D, hDY, hD3⟩ := h.y_cover.exists_subgroup_card_three
  have hDM : D ≤ M := hDY.trans h.y_le
  have hDK : D ≤ K := hDY.trans h.y_le_k
  let DK : Subgroup ↥K := D.subgroupOf K
  have hDKcard : Nat.card DK = 3 := by
    change Nat.card (D.subgroupOf K) = 3
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv).trans hD3
  have hDKgroup : IsPGroup 3 DK := IsPGroup.of_card (n := 1) (by rw [hDKcard, pow_one])
  obtain ⟨P, hDKP⟩ := hDKgroup.exists_le_sylow
  have hKrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans h.rank_three
  have hPrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥P) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (P : Subgroup ↥K)]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans hKrank
  have hcycP : IsCyclic ↥P :=
    CFSG.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) P.isPGroup' hPrank
  have hDleP' : D ≤ P.map K.subtype := by
    have hle := Subgroup.map_mono (f := K.subtype) hDKP
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDK] at hle
  have hcycP' : IsCyclic ↥(P.map K.subtype) :=
    isCyclic_of_surjective
      (Subgroup.equivMapOfInjective P K.subtype K.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective P K.subtype K.subtype_injective).surjective
  have hnorm : Subgroup.normalizer (P.map K.subtype : Set Γ) ≤ M :=
    (r925_normalizer_le_normalizer_of_isCyclic_card_prime (p := 3) hcycP' hDleP' hD3).trans
      (h.m_normalizer D hDM hD3)
  have hfrattini : Subgroup.normalizer (P.map K.subtype : Set Γ) ⊔ K = ⊤ :=
    Sylow.normalizer_sup_eq_top (p := 3) (N := K) P
  have htop : M ⊔ K = ⊤ := by
    apply le_antisymm le_top
    rw [← hfrattini]
    exact sup_le_sup_right hnorm K
  rwa [sup_comm] at htop

theorem r925_kbar_simple {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) : IsSimpleGroup ↥(K.map (toModO3p Γ)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Kb : Subgroup (ModO3p Γ) := K.map (toModO3p Γ)
  have hKbNormal : Kb.Normal := h.normal_k.map _ (QuotientGroup.mk'_surjective _)
  haveI : Kb.Normal := hKbNormal
  have hJ : ∀ x ∈ CFSG.pPrimeCore 3 Γ, ¬ 3 ∣ orderOf x := r925_pPrimeCore_orderOf
  let S : Set ↥Y := {y : ↥Y | orderOf y = 3}
  let T : Set Γ := Y.subtype '' S
  have hS : Subgroup.closure S = ⊤ := h.y_cover.closure_orderOf_three
  have hYgen : Y = Subgroup.closure T := by
    change Y = Subgroup.closure (Y.subtype '' S)
    calc Y = (⊤ : Subgroup ↥Y).map Y.subtype := by
            rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (Subgroup.closure S).map Y.subtype := by rw [hS]
      _ = Subgroup.closure (Y.subtype '' S) := MonoidHom.map_closure Y.subtype S
  have hKgen : K = Subgroup.normalClosure T := by
    calc K = Subgroup.normalClosure (Y : Set Γ) := h.k_eq
      _ = Subgroup.normalClosure (Subgroup.closure T) := by rw [hYgen]
      _ = Subgroup.normalClosure T := Subgroup.normalClosure_closure_eq_normalClosure
  have hTord : ∀ x ∈ (toModO3p Γ) '' T, orderOf x ∣ 3 := by
    rintro x ⟨y, hy, rfl⟩
    dsimp only [T] at hy
    obtain ⟨z, hzS, rfl⟩ := hy
    have hzS' : orderOf z = 3 := hzS
    exact (orderOf_map_dvd (toModO3p Γ) ((z : ↥Y) : Γ)).trans
      (by rw [Subgroup.orderOf_coe z, hzS'])
  have hKb_eq : Kb = Subgroup.normalClosure ((toModO3p Γ) '' T) := by
    change K.map (toModO3p Γ) = _
    rw [hKgen, Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _)]
  have hgen : Subgroup.closure {x : ModO3p Γ | x ∈ Kb ∧ orderOf x ∣ 3} = Kb := by
    rw [hKb_eq]
    exact r925_closure_orderOf_dvd_of_normalClosure hTord
  have hO : CFSG.pPrimeCore 3 ↥Kb = ⊥ := by
    have hcop : Nat.Coprime 3 (Nat.card ↥(CFSG.pPrimeCore 3 ↥Kb)) := CFSG.pPrimeCore_coprime_card
    have hle : (CFSG.pPrimeCore 3 ↥Kb).map Kb.subtype ≤ CFSG.pPrimeCore 3 (ModO3p Γ) := by
      change _ ≤ sSup {K : Subgroup (ModO3p Γ) | K.Normal ∧ Nat.Coprime 3 (Nat.card K)}
      exact le_sSup ⟨inferInstance, by
        rw [Subgroup.card_map_of_injective Kb.subtype_injective]; exact hcop⟩
    rw [r925_pPrimeCore_modO3p_eq_bot] at hle
    have hbot : (CFSG.pPrimeCore 3 ↥Kb).map Kb.subtype = ⊥ := le_bot_iff.mp hle
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : Kb.subtype x ∈ (CFSG.pPrimeCore 3 ↥Kb).map Kb.subtype :=
      Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subtype.ext (by simpa using hx')
  obtain ⟨D, hDY, hD3⟩ := h.y_cover.exists_subgroup_card_three
  have hDbar_card : Nat.card (D.map (toModO3p Γ)) = 3 := r925_card_map_eq_three hJ hD3
  have hKb_ne_bot : Kb ≠ ⊥ := by
    have hle : D.map (toModO3p Γ) ≤ Kb := Subgroup.map_mono (hDY.trans h.y_le_k)
    intro hbot
    rw [hbot] at hle
    have hDbot : D.map (toModO3p Γ) = ⊥ := le_bot_iff.mp hle
    rw [hDbot, Subgroup.card_bot] at hDbar_card
    omega
  haveI : Nontrivial ↥Kb := (Subgroup.nontrivial_iff_ne_bot Kb).mpr hKb_ne_bot
  have hrankKb : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Kb) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup Kb]
    exact le_of_eq (r925_kbar_pRank_aux h)
  refine (isSimpleGroup_iff ↥Kb).mpr ⟨inferInstance, fun N hN => ?_⟩
  by_cases h3N : 3 ∣ Nat.card ↥N
  · right
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3N
    let wK : ↥Kb := (w : ↥Kb)
    have hwK : wK ∈ N := w.2
    let DN : Subgroup ↥Kb := Subgroup.zpowers wK
    have hwKord : orderOf wK = 3 := (Subgroup.orderOf_coe w).trans hw
    have hDNcard : Nat.card DN = 3 := by
      change Nat.card (Subgroup.zpowers wK) = 3
      rw [Nat.card_zpowers, hwKord]
    have hDNle : DN ≤ N := Subgroup.zpowers_le.mpr hwK
    have hmemN : ∀ x : ↥Kb, orderOf x ∣ 3 → x ∈ N := by
      intro x hx3
      rcases (Nat.dvd_prime Nat.prime_three).mp hx3 with h1 | h3
      · rw [orderOf_eq_one_iff.mp h1]; exact N.one_mem
      · have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, h3]
        obtain ⟨g, hg⟩ := r925_exists_smul_conj_of_card_prime_of_pRank_le_one (G := ↥Kb)
          (p := 3) (by norm_num) hrankKb hDNcard hxcard
        have hle : Subgroup.zpowers x ≤ N := by
          rw [hg, ← Subgroup.Normal.conj_smul_eq_self g N]
          exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hDNle
        exact hle (Subgroup.mem_zpowers x)
    have himage : Kb ≤ N.map Kb.subtype := by
      calc Kb = Subgroup.closure {x : ModO3p Γ | x ∈ Kb ∧ orderOf x ∣ 3} := hgen.symm
        _ ≤ N.map Kb.subtype := by
              apply (Subgroup.closure_le (N.map Kb.subtype)).mpr
              intro x hx
              exact Subgroup.mem_map_of_mem Kb.subtype
                (hmemN ⟨x, hx.1⟩
                  (by rw [← Subgroup.orderOf_coe (⟨x, hx.1⟩ : ↥Kb)]; exact hx.2))
    rw [eq_top_iff]
    intro x _
    have hxmem : (x : ModO3p Γ) ∈ N.map Kb.subtype := himage x.2
    obtain ⟨n, hnN, hn⟩ := Subgroup.mem_map.mp hxmem
    have hnx : n = x := Subtype.ext hn
    rw [hnx] at hnN
    exact hnN
  · left
    have hcop : Nat.Coprime 3 (Nat.card ↥N) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3N
    have hle : N ≤ CFSG.pPrimeCore 3 ↥Kb := by
      change N ≤ sSup {K : Subgroup ↥Kb | K.Normal ∧ Nat.Coprime 3 (Nat.card K)}
      exact le_sSup ⟨hN, hcop⟩
    rw [hO] at hle
    exact le_bot_iff.mp hle

theorem r925_kbar_nonabelian {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) : ∃ a b : ↥(K.map (toModO3p Γ)), a * b ≠ b * a := by
  by_contra hc
  have hcomm : ∀ a b : ↥(K.map (toModO3p Γ)), a * b = b * a := by
    intro a b
    by_contra hab
    exact hc ⟨a, b, hab⟩
  haveI : IsMulCommutative ↥(K.map (toModO3p Γ)) := IsMulCommutative.of_comm hcomm
  haveI hperfK : Group.IsPerfect ↥K := ⟨h.perfect_k⟩
  haveI : Group.IsPerfect ↥(K.map (toModO3p Γ)) :=
    Group.IsPerfect.ofSurjective (f := (toModO3p Γ).subgroupMap K)
      (MonoidHom.subgroupMap_surjective _ _)
  haveI : Subsingleton ↥(K.map (toModO3p Γ)) :=
    Group.IsPerfect.subsingleton_of_isMulCommutative
  obtain ⟨D, hDY, hD3⟩ := h.y_cover.exists_subgroup_card_three
  have hcard : Nat.card (D.map (toModO3p Γ)) = 3 :=
    r925_card_map_eq_three r925_pPrimeCore_orderOf hD3
  have hle : D.map (toModO3p Γ) ≤ K.map (toModO3p Γ) :=
    Subgroup.map_mono (hDY.trans h.y_le_k)
  have hne : D.map (toModO3p Γ) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1 : (⟨(y : ModO3p Γ), hle y.2⟩ : ↥(K.map (toModO3p Γ))) = 1 :=
    Subsingleton.elim _ _
  have hval : (y : ModO3p Γ) = 1 := by
    have := congrArg (fun z : ↥(K.map (toModO3p Γ)) => (z : ModO3p Γ)) hx1
    simpa using this
  exact hy1 (Subtype.ext hval)

theorem r925_kbar_pRank {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) : CFSG.Open.pRank 3 (K.map (toModO3p Γ)) = 1 :=
  r925_kbar_pRank_aux h

theorem r925_kbar_kgroup {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) : CFSG.Open.IsKGroup ↥(K.map (toModO3p Γ)) :=
  CFSG.Open.IsKGroup.of_surjective (h.kgroup.subgroup K) ((toModO3p Γ).subgroupMap K)
    (MonoidHom.subgroupMap_surjective _ _)

theorem r925_kbar_centralizer {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) :
    ∀ x : ModO3p Γ, (∀ k ∈ K.map (toModO3p Γ), x * k = k * x) → x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx
  let Kb : Subgroup (ModO3p Γ) := K.map (toModO3p Γ)
  have hKbNormal : Kb.Normal := h.normal_k.map _ (QuotientGroup.mk'_surjective _)
  haveI : Kb.Normal := hKbNormal
  haveI : IsSimpleGroup ↥Kb := r925_kbar_simple h
  let C : Subgroup (ModO3p Γ) := Subgroup.centralizer (Kb : Set (ModO3p Γ))
  have hCNormal : C.Normal := inferInstance
  have hxC : x ∈ C := by
    change x ∈ Subgroup.centralizer (Kb : Set (ModO3p Γ))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hx y (by simpa [Kb] using hy)).symm
  have hcent : Subgroup.center ↥Kb = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥Kb) with hc | hc
    · exact hc
    · exfalso
      obtain ⟨a, b, hab⟩ := r925_kbar_nonabelian h
      haveI : IsMulCommutative ↥Kb := Subgroup.center_eq_top_iff.mp hc
      exact hab (mul_comm' a b)
  have hle_center : (C ⊓ Kb).subgroupOf Kb ≤ Subgroup.center ↥Kb := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    have hyC : (y : ModO3p Γ) ∈ C := (Subgroup.mem_subgroupOf.mp hy).1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hyC (z : ModO3p Γ) z.2
  have hCinf : C ⊓ Kb = ⊥ := by
    have hsub_bot : (C ⊓ Kb).subgroupOf Kb = ⊥ :=
      le_bot_iff.mp (hle_center.trans (le_of_eq hcent))
    have hd : (C ⊓ Kb) ⊓ Kb = ⊥ := disjoint_iff.mp ((Subgroup.subgroupOf_eq_bot).mp hsub_bot)
    rwa [inf_eq_left.mpr inf_le_right] at hd
  have hCbot : C = ⊥ := by
    have h3not : ¬ 3 ∣ Nat.card ↥C := by
      intro h3
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3
      have hwΛ : (w : ModO3p Γ) ∈ C := w.2
      have hw_notKb : (w : ModO3p Γ) ∉ Kb := by
        intro hwKb
        have hmem : (⟨(w : ModO3p Γ), hwKb⟩ : ↥Kb) ∈ (C ⊓ Kb).subgroupOf Kb := by
          rw [Subgroup.mem_subgroupOf]
          exact ⟨hwΛ, hwKb⟩
        rw [hCinf] at hmem
        have hmem' : (w : ModO3p Γ) ∈ (⊥ : Subgroup (ModO3p Γ)) :=
          Subgroup.mem_subgroupOf.mp hmem
        rw [Subgroup.mem_bot] at hmem'
        have hw1 : (w : ModO3p Γ) = 1 := hmem'
        have hord : orderOf (w : ModO3p Γ) = 3 := (Subgroup.orderOf_coe w).trans hw
        rw [hw1, orderOf_one] at hord
        omega
      obtain ⟨D, hDY, hD3⟩ := h.y_cover.exists_subgroup_card_three
      have hDbar_card : Nat.card (D.map (toModO3p Γ)) = 3 :=
        r925_card_map_eq_three r925_pPrimeCore_orderOf hD3
      have hDbar_ne_bot : D.map (toModO3p Γ) ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hDbar_card
        omega
      obtain ⟨d, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDbar_ne_bot
      have hdv : (d : ModO3p Γ) ≠ 1 := fun h => hd1 (Subtype.ext h)
      obtain ⟨e, heD, heq⟩ := Subgroup.mem_map.mp d.2
      have hevd : orderOf e ∣ 3 := hD3 ▸ Subgroup.orderOf_dvd_natCard D heD
      have he3 : e ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hevd
      have hd3 : (d : ModO3p Γ) ^ 3 = 1 := by
        rw [← heq, ← map_pow, he3, map_one]
      have hdKb : (d : ModO3p Γ) ∈ Kb := Subgroup.map_mono (hDY.trans h.y_le_k) d.2
      have hd_le : Subgroup.zpowers (d : ModO3p Γ) ≤ Kb := Subgroup.zpowers_le.mpr hdKb
      have hw3 : (w : ModO3p Γ) ^ 3 = 1 := by
        have hpow := pow_orderOf_eq_one ((w : ↥C) : ModO3p Γ)
        rwa [Subgroup.orderOf_coe w, hw] at hpow
      have hwd : (w : ModO3p Γ) ∉ Subgroup.zpowers (d : ModO3p Γ) :=
        fun hmem => hw_notKb (hd_le hmem)
      have hcomm : (d : ModO3p Γ) * (w : ModO3p Γ) = (w : ModO3p Γ) * (d : ModO3p Γ) :=
        Subgroup.mem_centralizer_iff.mp hwΛ (d : ModO3p Γ) hdKb
      have hE9 := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers (p := 3)
        Nat.prime_three hd3 hw3 hdv hwd hcomm
      have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (ModO3p Γ)) :=
        CFSG.SectionRank.le_pRank (p := 3) (G := ModO3p Γ) (H := ⊤)
          (E := Subgroup.zpowers (d : ModO3p Γ) ⊔ Subgroup.zpowers (w : ModO3p Γ))
          (by norm_num) le_top hE9.1 (k := 2) hE9.2
      have hle := r925_pRank_quotient_le (CFSG.pPrimeCore 3 Γ) Nat.prime_three
        r925_pPrimeCore_orderOf
      have hrank := h.rank_three
      omega
    have hcop : Nat.Coprime 3 (Nat.card ↥C) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3not
    have hle : C ≤ CFSG.pPrimeCore 3 (ModO3p Γ) := by
      change C ≤ sSup {K : Subgroup (ModO3p Γ) | K.Normal ∧ Nat.Coprime 3 (Nat.card K)}
      exact le_sSup ⟨hCNormal, hcop⟩
    rw [r925_pPrimeCore_modO3p_eq_bot] at hle
    exact le_bot_iff.mp hle
  rw [hCbot, Subgroup.mem_bot] at hxC
  exact hxC

theorem r925_le_of_normal {Λ : Type} [Group Λ] {B N : Subgroup Λ} [B.Normal] [N.Normal]
    (hs : IsSimpleGroup ↥B) (hc : ∀ x : Λ, (∀ k ∈ B, x * k = k * x) → x = 1) (hN : N ≠ ⊥) :
    B ≤ N := by
  rcases hs.eq_bot_or_eq_top_of_normal ((N ⊓ B).subgroupOf B) with hbot | htop
  · exfalso
    have hNBot : N ⊓ B = ⊥ := by
      have hd : (N ⊓ B) ⊓ B = ⊥ := disjoint_iff.mp ((Subgroup.subgroupOf_eq_bot).mp hbot)
      rwa [inf_eq_left.mpr inf_le_right] at hd
    have hdisj : Disjoint N B := disjoint_iff.mpr hNBot
    apply hN
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    exact hc n fun k hk =>
      (Subgroup.commute_of_normal_of_disjoint N B inferInstance inferInstance hdisj n k hn hk).eq
  · exact (Subgroup.subgroupOf_eq_top).mp htop |>.trans inf_le_left

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
