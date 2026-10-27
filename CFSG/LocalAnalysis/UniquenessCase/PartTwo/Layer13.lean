module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.RankThree.PartOne (pElementSubgroup)

open scoped commutatorElement

@[expose] def s13_NormalSimple (Q : Type) [Group Q] : Prop :=
  ∀ J : Subgroup Q, CFSG.IsComponent J → J.Normal ∧ IsSimpleGroup ↥J

open Classical in
@[expose] noncomputable def s13_compsP (Q : Type) [Group Q] [Finite Q] (p : ℕ) :
    Finset (Subgroup Q) :=
  (Set.toFinite {J : Subgroup Q | CFSG.IsComponent J ∧ p ∣ Nat.card J}).toFinset

variable {Q : Type} [Group Q] [Finite Q]

theorem s13_mem_compsP {p : ℕ} {J : Subgroup Q} :
    J ∈ s13_compsP Q p ↔ CFSG.IsComponent J ∧ p ∣ Nat.card J := by
  simp [s13_compsP]

theorem s13_Layer13_component_not_commutative {J : Subgroup Q} (hJ : CFSG.IsComponent J) :
    ∃ x y : J, x * y ≠ y * x := by
  obtain ⟨-, -, a, b, hab⟩ := hJ.1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) b
  exact ⟨x, y, fun h => hab (by rw [← map_mul, ← map_mul, h])⟩

noncomputable def s13_Layer13_comps (Q : Type) [Group Q] [Finite Q] : Finset (Subgroup Q) :=
  (Set.toFinite {J : Subgroup Q | CFSG.IsComponent J}).toFinset

theorem s13_Layer13_mem_comps {J : Subgroup Q} :
    J ∈ s13_Layer13_comps Q ↔ CFSG.IsComponent J := by
  simp [s13_Layer13_comps]

theorem s13_Layer13_layer_eq_iSup :
    CFSG.layer Q = ⨆ J ∈ s13_Layer13_comps Q, J := by
  rw [CFSG.layer.eq_sSup, sSup_eq_iSup]
  unfold s13_Layer13_comps
  rw [← Finset.iSup_coe, Set.Finite.coe_toFinset]

theorem s13_components_commute (hns : s13_NormalSimple Q) {J K : Subgroup Q}
    (hJ : CFSG.IsComponent J) (hK : CFSG.IsComponent K) (hne : J ≠ K) :
    J ≤ Subgroup.centralizer (K : Set Q) := by
  rcases CFSG.LocalCores.distinct_components_commute hJ hK with h | h
  · exact absurd h hne
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

theorem s13_inf_iSup_eq_bot (hns : s13_NormalSimple Q) {J : Subgroup Q} (hJ : CFSG.IsComponent J)
    (S : Finset (Subgroup Q)) (hS : ∀ K ∈ S, CFSG.IsComponent K ∧ K ≠ J) :
    J ⊓ ⨆ K ∈ S, K = ⊥ := by
  set P : Subgroup Q := ⨆ K ∈ S, K with hP
  have hPc : P ≤ Subgroup.centralizer (J : Set Q) := by
    rw [hP]
    exact iSup₂_le fun K hK =>
      s13_components_commute hns (hS K hK).1 hJ (hS K hK).2
  set N : Subgroup Q := J ⊓ P with hN
  have hNnorm : (N.subgroupOf J).Normal := by
    refine Subgroup.normal_of_le_center fun n hn => ?_
    rw [Subgroup.mem_center_iff]
    intro m
    have hnP : (n : Q) ∈ P := (Subgroup.mem_subgroupOf.mp hn).2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hPc hnP) m m.2)
  have hNbot : N = ⊥ := by
    haveI : IsSimpleGroup ↥J := (hns J hJ).2
    haveI : (N.subgroupOf J).Normal := hNnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf J) with hbot | htop
    · rw [Subgroup.subgroupOf_eq_bot] at hbot
      exact hbot.eq_bot_of_le inf_le_left
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at htop
      obtain ⟨x, y, hxy⟩ := s13_Layer13_component_not_commutative hJ
      have hJc : J ≤ Subgroup.centralizer (J : Set Q) := htop.trans (inf_le_right.trans hPc)
      have hxc : (x : Q) ∈ Subgroup.centralizer (J : Set Q) := hJc x.2
      exact hxy (Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc y y.2).symm)
  show J ⊓ P = ⊥
  rw [← hN]
  exact hNbot

theorem s13_exists_mul_of_inner (hns : s13_NormalSimple Q) {x : Q}
    (hx : ∀ J : Subgroup Q, CFSG.IsComponent J → x ∈ J ⊔ Subgroup.centralizer (J : Set Q)) :
    ∃ e ∈ CFSG.layer Q, ∃ c ∈ Subgroup.centralizer (CFSG.layer Q : Set Q), x = e * c := by
  classical
  have claim : ∀ S : Finset (Subgroup Q), (∀ K ∈ S, CFSG.IsComponent K) →
      ∃ e ∈ ⨆ K ∈ S, K, ∀ K ∈ S, e⁻¹ * x ∈ Subgroup.centralizer (K : Set Q) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, ?_, ?_⟩
      · simp
      · intro K hK
        exact absurd hK (Finset.notMem_empty K)
    | insert a S ha ih =>
      intro hS
      have haC : CFSG.IsComponent a := hS a (Finset.mem_insert_self a S)
      have hSC : ∀ K ∈ S, CFSG.IsComponent K := fun K hK => hS K (Finset.mem_insert_of_mem hK)
      obtain ⟨e', he', hcent'⟩ := ih hSC
      have haN : a.Normal := (hns a haC).1
      obtain ⟨u, hu, c, hc, hux⟩ := (Subgroup.mem_sup_of_normal_left (s := a)
        (t := Subgroup.centralizer (a : Set Q))).mp (hx a haC)
      have he'c : e' ∈ Subgroup.centralizer (a : Set Q) := by
        have hle : (⨆ K ∈ S, K) ≤ Subgroup.centralizer (a : Set Q) :=
          iSup₂_le fun K hK =>
            s13_components_commute hns (hSC K hK) haC (fun h => ha (h ▸ hK))
        exact hle he'
      refine ⟨u * e', ?_, ?_⟩
      · rw [Finset.iSup_insert]
        exact Subgroup.mul_mem_sup hu he'
      · intro K hK
        rw [Finset.mem_insert] at hK
        rcases hK with rfl | hKS
        · have huinvx : u⁻¹ * x = c := by rw [← hux]; group
          have hstep : (u * e')⁻¹ * x = e'⁻¹ * c := by
            rw [mul_inv_rev, mul_assoc, huinvx]
          rw [hstep]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ he'c) hc
        · have hKc : CFSG.IsComponent K := hSC K hKS
          have hne : K ≠ a := fun h => ha (h ▸ hKS)
          have haK : a ≤ Subgroup.centralizer (K : Set Q) :=
            s13_components_commute hns haC hKc (Ne.symm hne)
          have huc : u ∈ Subgroup.centralizer (K : Set Q) := haK hu
          have hue : e'⁻¹ * u⁻¹ = u⁻¹ * e'⁻¹ := by
            have h1 : u * e' = e' * u := Subgroup.mem_centralizer_iff.mp he'c u hu
            rw [← mul_inv_rev, h1, mul_inv_rev]
          have hstep : (u * e')⁻¹ * x = u⁻¹ * (e'⁻¹ * x) := by
            rw [mul_inv_rev, hue, mul_assoc]
          rw [hstep]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ huc) (hcent' K hKS)
  obtain ⟨e, he, hcent⟩ := claim (s13_Layer13_comps Q)
    (fun K hK => s13_Layer13_mem_comps.mp hK)
  refine ⟨e, ?_, e⁻¹ * x, ?_, (mul_inv_cancel_left e x).symm⟩
  · rw [s13_Layer13_layer_eq_iSup]
    exact he
  · have hcomm : ∀ K : Subgroup Q, CFSG.IsComponent K →
        K ≤ Subgroup.centralizer ({e⁻¹ * x} : Set Q) := by
      intro K hK
      have hcK : e⁻¹ * x ∈ Subgroup.centralizer (K : Set Q) :=
        hcent K (s13_Layer13_mem_comps.mpr hK)
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.mp hcK k hk).symm
    have hlayer : CFSG.layer Q ≤ Subgroup.centralizer ({e⁻¹ * x} : Set Q) := by
      rw [CFSG.layer.eq_sSup]
      exact sSup_le hcomm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.mp (hlayer hh) (e⁻¹ * x) (by simp)).symm

theorem s13_commutator_le_sup_centralizer (J : Subgroup Q) [J.Normal]
    (hOut : ∀ σ τ : MulAut ↥J, ∃ y : ↥J, σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj y) :
    commutator Q ≤ J ⊔ Subgroup.centralizer (J : Set Q) := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  obtain ⟨y, hy⟩ := hOut (MulAut.conjNormal g₁) (MulAut.conjNormal g₂)
  let d : Q := ⁅g₁, g₂⁆ * (y : Q)⁻¹
  have hmap : MulAut.conjNormal (H := J) d = 1 := by
    change MulAut.conjNormal (H := J) (⁅g₁, g₂⁆ * (y : Q)⁻¹) = 1
    rw [commutatorElement_def]
    simp only [map_mul, map_inv]
    rw [MulAut.conjNormal_val, hy, mul_inv_cancel]
  have hd : d ∈ Subgroup.centralizer (J : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : d * (h : Q) * d⁻¹ = (h : Q) := by
      simpa using congrArg (fun f : MulAut ↥J => (f ⟨h, hh⟩ : Q)) hmap
    have h2 : d * (h : Q) = (h : Q) * d := by
      calc d * (h : Q) = (d * (h : Q) * d⁻¹) * d := by group
        _ = (h : Q) * d := by rw [h1]
    exact h2.symm
  have hdmy : d * (y : Q) = ⁅g₁, g₂⁆ := by simp [d]
  rw [sup_comm, ← hdmy]
  exact Subgroup.mul_mem_sup hd y.2

theorem s13_prime_dvd_card_of_mem_sup_centralizer (J : Subgroup Q) {y : Q}
    (hy : y ∈ J ⊔ Subgroup.centralizer (J : Set Q))
    (hyc : y ∉ Subgroup.centralizer (J : Set Q)) {r : ℕ} (hr : r.Prime) (hyr : y ^ r = 1) :
    r ∣ Nat.card J := by
  by_contra hnot
  have hLC : J ≤ Subgroup.normalizer (Subgroup.centralizer (J : Set Q) : Set Q) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLC] at hy
  obtain ⟨k, hk, c, hc, rfl⟩ := hy
  have hcomm : Commute k c := (Subgroup.mem_centralizer_iff.mp hc k hk)
  have h1 : k ^ r * c ^ r = 1 := by
    rw [← hcomm.mul_pow, hyr]
  have hkr_mem : k ^ r ∈ Subgroup.centralizer (J : Set Q) := by
    rw [eq_inv_of_mul_eq_one_left h1]
    exact Subgroup.inv_mem _ (pow_mem hc r)
  have hrk : r.Coprime (orderOf k) := by
    rw [Nat.Prime.coprime_iff_not_dvd hr]
    intro hrd
    exact hnot (hrd.trans (Subgroup.orderOf_dvd_natCard J hk))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hrk
  have hkC : k ∈ Subgroup.centralizer (J : Set Q) := by
    have h := pow_mem hkr_mem m
    rwa [hm] at h
  exact hyc (Subgroup.mul_mem _ hkC hc)

theorem s13_pElementSubgroup_layer_eq (hns : s13_NormalSimple Q) {p : ℕ} (hp : p.Prime) :
    pElementSubgroup p (CFSG.layer Q) = ⨆ J ∈ s13_compsP Q p, J := by
  classical
  have claim : ∀ S : Finset (Subgroup Q), (∀ J ∈ S, CFSG.IsComponent J) →
      ∀ x ∈ ⨆ J ∈ S, J, (∃ k, x ^ p ^ k = 1) →
        x ∈ ⨆ J ∈ S.filter (fun J : Subgroup Q => p ∣ Nat.card J), J := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ x hx _
      simp at hx
      rw [hx]
      exact Subgroup.one_mem _
    | insert a S ha ih =>
      intro hS x hx hxpow
      have haC : CFSG.IsComponent a := hS a (Finset.mem_insert_self a S)
      have hSC : ∀ K ∈ S, CFSG.IsComponent K := fun K hK => hS K (Finset.mem_insert_of_mem hK)
      haveI : a.Normal := (hns a haC).1
      rw [Finset.iSup_insert] at hx
      obtain ⟨u, hu, v, hv, huv⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := a) (t := ⨆ K ∈ S, K)).mp hx
      have hSc : (⨆ K ∈ S, K) ≤ Subgroup.centralizer (a : Set Q) :=
        iSup₂_le fun K hK => s13_components_commute hns (hSC K hK) haC (fun h => ha (h ▸ hK))
      have hv_c : v ∈ Subgroup.centralizer (a : Set Q) := hSc hv
      have hcomm_uv : Commute u v := Subgroup.mem_centralizer_iff.mp hv_c u hu
      obtain ⟨k, hxpow⟩ := hxpow
      have hx' : (u * v) ^ p ^ k = 1 := by rw [huv]; exact hxpow
      have hprod : u ^ p ^ k * v ^ p ^ k = 1 := by rw [← hcomm_uv.mul_pow, hx']
      have hu_one : u ^ p ^ k = 1 := by
        have hmem : u ^ p ^ k ∈ a ⊓ ⨆ K ∈ S, K := by
          refine ⟨pow_mem hu _, ?_⟩
          rw [eq_inv_of_mul_eq_one_left hprod]
          exact Subgroup.inv_mem _ (pow_mem hv _)
        rw [s13_inf_iSup_eq_bot hns haC S (fun K hK => ⟨hSC K hK, fun h => ha (h ▸ hK)⟩)] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hv_one : v ^ p ^ k = 1 := by
        rw [hu_one, one_mul] at hprod
        exact hprod
      by_cases hpa : p ∣ Nat.card a
      · have hmem_a : a ∈ (insert a S).filter (fun J : Subgroup Q => p ∣ Nat.card J) :=
          Finset.mem_filter.mpr ⟨Finset.mem_insert_self a S, hpa⟩
        have hu_mem : u ∈ ⨆ J ∈ (insert a S).filter (fun J : Subgroup Q => p ∣ Nat.card J), J :=
          (le_iSup₂
            (f := fun J (_ : J ∈ (insert a S).filter
              (fun J : Subgroup Q => p ∣ Nat.card J)) => J)
            a hmem_a) hu
        have hv_mem_S : v ∈ ⨆ J ∈ S.filter (fun J : Subgroup Q => p ∣ Nat.card J), J :=
          ih hSC v hv ⟨k, hv_one⟩
        have hv_mem : v ∈ ⨆ J ∈ (insert a S).filter (fun J : Subgroup Q => p ∣ Nat.card J), J := by
          have hle : (⨆ K ∈ S.filter (fun J : Subgroup Q => p ∣ Nat.card J), K) ≤
              ⨆ J ∈ (insert a S).filter (fun J : Subgroup Q => p ∣ Nat.card J), J :=
            iSup₂_le fun K hK => by
              rw [Finset.mem_filter] at hK
              exact le_iSup₂
                (f := fun J (_ : J ∈ (insert a S).filter
                  (fun J : Subgroup Q => p ∣ Nat.card J)) => J)
                K (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hK.1, hK.2⟩)
          exact hle hv_mem_S
        rw [show x = u * v from huv.symm]
        exact Subgroup.mul_mem _ hu_mem hv_mem
      · have hu1 : u = 1 := by
          have hpua : ¬ p ∣ orderOf u :=
            fun h => hpa (h.trans (Subgroup.orderOf_dvd_natCard a hu))
          have hdvd : orderOf u ∣ p ^ k := orderOf_dvd_of_pow_eq_one hu_one
          obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
          have hj0 : j = 0 := by
            by_contra hj0
            exact hpua (by rw [hj]; exact dvd_pow_self p hj0)
          have : orderOf u = 1 := by rw [hj, hj0, pow_zero]
          exact orderOf_eq_one_iff.mp this
        rw [show x = v by rw [← huv, hu1, one_mul], Finset.filter_insert, if_neg hpa]
        exact ih hSC v hv ⟨k, hv_one⟩
  refine le_antisymm ?_ ?_
  · rw [pElementSubgroup, Subgroup.closure_le]
    rintro x ⟨hxl, k, hk⟩
    have hxpow : x ^ p ^ k = 1 := by rw [← hk, pow_orderOf_eq_one]
    have hxmem : x ∈ ⨆ J ∈ s13_Layer13_comps Q, J := by
      rw [← s13_Layer13_layer_eq_iSup]
      exact hxl
    have hres := claim (s13_Layer13_comps Q)
      (fun J hJ => s13_Layer13_mem_comps.mp hJ) x hxmem ⟨k, hxpow⟩
    have hfilter : (s13_Layer13_comps Q).filter
        (fun J : Subgroup Q => p ∣ Nat.card J) = s13_compsP Q p := by
      ext J
      simp only [Finset.mem_filter, s13_Layer13_mem_comps, s13_mem_compsP]
    rw [hfilter] at hres
    exact hres
  · refine iSup₂_le fun J hJ => ?_
    have hJc : CFSG.IsComponent J := (s13_mem_compsP.mp hJ).1
    have hpJ : p ∣ Nat.card J := (s13_mem_compsP.mp hJ).2
    have hJN : J.Normal := (hns J hJc).1
    have hNnorm : (pElementSubgroup p J).Normal := by
      rw [Subgroup.normal_iff_map_conj_eq]
      intro w
      change CFSG.RankThree.PartOne.conjBy w (pElementSubgroup p J) = pElementSubgroup p J
      rw [← CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy p w J]
      congr 1
      haveI : J.Normal := hJN
      exact Subgroup.Normal.map_conj_eq (H := J) w
    have hNJ : pElementSubgroup p J ≤ J := by
      unfold pElementSubgroup
      exact (Subgroup.closure_le J).mpr fun x hx => hx.1
    have hNnontriv : pElementSubgroup p J ≠ ⊥ := by
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) p hpJ
      have hsmem : (s : Q) ∈ pElementSubgroup p J :=
        Subgroup.subset_closure ⟨s.2, ⟨1, by rw [pow_one, Subgroup.orderOf_coe, hs]⟩⟩
      have hsne : (s : Q) ≠ 1 := by
        intro h
        have hs1 : s = 1 := Subtype.ext h
        rw [hs1, orderOf_one] at hs
        exact hp.ne_one hs.symm
      intro hbot
      rw [hbot] at hsmem
      exact hsne (Subgroup.mem_bot.mp hsmem)
    have hsub : (pElementSubgroup p J).subgroupOf J = ⊤ := by
      haveI : IsSimpleGroup ↥J := (hns J hJc).2
      haveI : ((pElementSubgroup p J).subgroupOf J).Normal := hNnorm.subgroupOf J
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pElementSubgroup p J).subgroupOf J) with
        h | h
      · exfalso
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact hNnontriv (h.eq_bot_of_le hNJ)
      · exact h
    have hJle : J ≤ pElementSubgroup p J := by
      rw [← Subgroup.subgroupOf_eq_top]
      exact hsub
    refine hJle.trans ?_
    unfold pElementSubgroup
    refine Subgroup.closure_mono ?_
    intro x hx
    refine ⟨?_, hx.2⟩
    have hJlayer : J ≤ CFSG.layer Q := by
      rw [CFSG.layer.eq_sSup]
      exact le_sSup hJc
    exact hJlayer hx.1

theorem s13_pRank_pElementSubgroup_layer {p ℓ : ℕ} (hns : s13_NormalSimple Q) (hp : p.Prime)
    (hℓ : ℓ.Prime) :
    CFSG.Open.pRank ℓ (pElementSubgroup p (CFSG.layer Q)) =
      ∑ J ∈ s13_compsP Q p, CFSG.Open.pRank ℓ J := by
  classical
  rw [s13_pElementSubgroup_layer_eq hns hp]
  refine s13_pRank_iSup_eq_sum hℓ (s13_compsP Q p) (fun J => J) ?_ ?_
  · intro i hi j hj hij
    exact s13_components_commute hns (s13_mem_compsP.mp hi).1 (s13_mem_compsP.mp hj).1 hij
  · intro i hi
    refine s13_inf_iSup_eq_bot hns (s13_mem_compsP.mp hi).1 ((s13_compsP Q p).erase i) ?_
    intro K hK
    rw [Finset.mem_erase] at hK
    exact ⟨(s13_mem_compsP.mp hK.2).1, hK.1⟩

theorem s13_pRank_pElementSubgroup_layer_le {p r : ℕ} (hns : s13_NormalSimple Q) (hp : p.Prime)
    (hr : r.Prime)
    (hcomp : ∀ J : Subgroup Q, CFSG.IsComponent J → p ∣ Nat.card J →
      CFSG.Open.pRank p J ≤ CFSG.Open.pRank r J) :
    CFSG.Open.pRank p (pElementSubgroup p (CFSG.layer Q)) ≤
      CFSG.Open.pRank r (pElementSubgroup p (CFSG.layer Q)) := by
  rw [s13_pRank_pElementSubgroup_layer hns hp hp,
    s13_pRank_pElementSubgroup_layer hns hp hr]
  exact Finset.sum_le_sum fun J hJ =>
    hcomp J (s13_mem_compsP.mp hJ).1 (s13_mem_compsP.mp hJ).2

theorem s13_le_centralizer_pElementSubgroup_layer (hns : s13_NormalSimple Q) {p : ℕ}
    (hp : p.Prime) {J : Subgroup Q} (hJ : CFSG.IsComponent J) (hpJ : ¬ p ∣ Nat.card J) :
    J ≤ Subgroup.centralizer (pElementSubgroup p (CFSG.layer Q) : Set Q) := by
  have hEp : pElementSubgroup p (CFSG.layer Q) ≤ Subgroup.centralizer (J : Set Q) := by
    rw [s13_pElementSubgroup_layer_eq hns hp]
    refine iSup₂_le fun K hK => ?_
    have hKc : CFSG.IsComponent K := (s13_mem_compsP.mp hK).1
    have hpK : p ∣ Nat.card K := (s13_mem_compsP.mp hK).2
    exact s13_components_commute hns hKc hJ (fun h => hpJ (h ▸ hpK))
  exact Subgroup.le_centralizer_iff.mpr hEp

theorem s13_Layer13_inf_centralizer_eq_bot (hns : s13_NormalSimple Q) {J : Subgroup Q}
    (hJ : CFSG.IsComponent J) : J ⊓ Subgroup.centralizer (J : Set Q) = ⊥ := by
  set N : Subgroup Q := J ⊓ Subgroup.centralizer (J : Set Q) with hN
  have hNnorm : (N.subgroupOf J).Normal := by
    refine Subgroup.normal_of_le_center fun n hn => ?_
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hn).2 m m.2)
  have hNbot : N = ⊥ := by
    haveI : IsSimpleGroup ↥J := (hns J hJ).2
    haveI : (N.subgroupOf J).Normal := hNnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf J) with hbot | htop
    · rw [Subgroup.subgroupOf_eq_bot] at hbot
      exact hbot.eq_bot_of_le inf_le_left
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at htop
      obtain ⟨x, y, hxy⟩ := s13_Layer13_component_not_commutative hJ
      have hxc : (x : Q) ∈ Subgroup.centralizer (J : Set Q) :=
        inf_le_right (a := J) (b := Subgroup.centralizer (J : Set Q)) (htop x.2)
      exact hxy (Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc y y.2).symm)
  show J ⊓ Subgroup.centralizer (J : Set Q) = ⊥
  rw [← hN]
  exact hNbot

theorem s13_inf_centralizer_eq_bot (hns : s13_NormalSimple Q) {p : ℕ} (hp : p.Prime) :
    pElementSubgroup p (CFSG.layer Q) ⊓
      Subgroup.centralizer (pElementSubgroup p (CFSG.layer Q) : Set Q) = ⊥ := by
  classical
  have claim : ∀ S : Finset (Subgroup Q), (∀ J ∈ S, CFSG.IsComponent J) →
      ∀ z ∈ ⨆ J ∈ S, J, (∀ J ∈ S, z ∈ Subgroup.centralizer (J : Set Q)) → z = 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ z hz _
      simp at hz
      exact hz
    | insert a S ha ih =>
      intro hS z hz hcent
      have haC : CFSG.IsComponent a := hS a (Finset.mem_insert_self a S)
      have hSC : ∀ K ∈ S, CFSG.IsComponent K := fun K hK => hS K (Finset.mem_insert_of_mem hK)
      haveI : a.Normal := (hns a haC).1
      rw [Finset.iSup_insert] at hz
      obtain ⟨u, hu, v, hv, huv⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := a) (t := ⨆ K ∈ S, K)).mp hz
      have hSc : (⨆ K ∈ S, K) ≤ Subgroup.centralizer (a : Set Q) :=
        iSup₂_le fun K hK => s13_components_commute hns (hSC K hK) haC (fun h => ha (h ▸ hK))
      have hv_c : v ∈ Subgroup.centralizer (a : Set Q) := hSc hv
      have hu_c : u ∈ Subgroup.centralizer (a : Set Q) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hz_c : z ∈ Subgroup.centralizer (a : Set Q) := hcent a (Finset.mem_insert_self a S)
        have hz_c' : y * z = z * y := Subgroup.mem_centralizer_iff.mp hz_c y hy
        have hv_y : v * y = y * v := (Subgroup.mem_centralizer_iff.mp hv_c y hy).symm
        have h1 : y * u * v = u * y * v := by
          calc y * u * v = y * (u * v) := by group
            _ = y * z := by rw [huv]
            _ = z * y := hz_c'
            _ = u * v * y := by rw [huv]
            _ = u * (v * y) := by group
            _ = u * (y * v) := by rw [hv_y]
            _ = u * y * v := by group
        exact mul_right_cancel h1
      have hu_inf : u ∈ a ⊓ Subgroup.centralizer (a : Set Q) := ⟨hu, hu_c⟩
      have hu1 : u = 1 := by
        rw [s13_Layer13_inf_centralizer_eq_bot hns haC] at hu_inf
        exact Subgroup.mem_bot.mp hu_inf
      have hz_eq : z = v := by rw [← huv, hu1, one_mul]
      have hv_cent : ∀ K ∈ S, v ∈ Subgroup.centralizer (K : Set Q) := by
        intro K hK
        have hz_cK : z ∈ Subgroup.centralizer (K : Set Q) := hcent K (Finset.mem_insert_of_mem hK)
        have hu_cK : u ∈ Subgroup.centralizer (K : Set Q) :=
          s13_components_commute hns haC (hSC K hK) (fun h => ha (h.symm ▸ hK)) hu
        have hv_eq : v = u⁻¹ * z := by rw [← huv]; group
        rw [hv_eq]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hu_cK) hz_cK
      rw [hz_eq]
      exact ih hSC v hv hv_cent
  rw [s13_pElementSubgroup_layer_eq hns hp]
  refine le_antisymm ?_ bot_le
  intro z hz
  obtain ⟨hzE, hzC⟩ := hz
  have hcent : ∀ J ∈ s13_compsP Q p, z ∈ Subgroup.centralizer (J : Set Q) := by
    intro J hJ
    have hJE : J ≤ ⨆ K ∈ s13_compsP Q p, K :=
      le_iSup₂ (f := fun K (_ : K ∈ s13_compsP Q p) => K) J hJ
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp hzC y (hJE hy)
  exact Subgroup.mem_bot.mpr
    (claim (s13_compsP Q p) (fun J hJ => (s13_mem_compsP.mp hJ).1) z hzE hcent)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
