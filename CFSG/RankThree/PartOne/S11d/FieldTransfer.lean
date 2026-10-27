module

public import CFSG.RankThree.PartOne.S11c.Sec66Glue
public import CFSG.RankThree.PartOne.S11d.FixedFacts

public section

namespace CFSG.RankThree.PartOne.FieldFix

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.RankThreeCoreUniqueness.Helpers (finite_perfectResidual_map_eq)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)

theorem mem_perfectResidual_of_map {C F : Type*} [Group C] [Group F] [Finite C] [Finite F]
    {θ : C →* F} (hsurj : Function.Surjective θ) (hcent : θ.ker ≤ Subgroup.center C) {p k : ℕ}
    (hker : ∀ z ∈ θ.ker, Nat.Coprime (orderOf z) p) {g : C} (hgk : g ^ (p ^ k) = 1)
    (h : θ g ∈ perfectResidual F) : g ∈ perfectResidual C := by
  have hmap : (perfectResidual C).map θ = perfectResidual F :=
    finite_perfectResidual_map_eq θ hsurj
  rw [← hmap] at h
  obtain ⟨e, he, heq⟩ := h
  have hz : e⁻¹ * g ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
  set z := e⁻¹ * g with hzdef
  have hzc : Commute e z := Subgroup.mem_center_iff.mp (hcent hz) e
  have hgz : g = e * z := by rw [hzdef, mul_inv_cancel_left]
  have hzpow : z ^ (p ^ k) = (e ^ (p ^ k))⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hzc.mul_pow, ← hgz]
    exact hgk
  have hmem : z ^ (p ^ k) ∈ perfectResidual C := by
    rw [hzpow]
    exact (perfectResidual C).inv_mem ((perfectResidual C).pow_mem he _)
  have hzmem : z ∈ perfectResidual C := by
    have hcop : Nat.Coprime (p ^ k) (orderOf z) := Nat.Coprime.pow_left k (hker z hz).symm
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact (perfectResidual C).pow_mem hmem m
  rw [hgz]
  exact (perfectResidual C).mul_mem he hzmem

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem fieldAutT_of_inducesFieldAut {p : ℕ} (hp : p.Prime) {J : Subgroup G}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) {u : G}
    (hu : u ∈ Subgroup.normalizer (J : Set G)) (hup : u ^ p = 1) (h : InducesFieldAut p u J) :
    FieldAutT p (centerQuotientConj J ⟨u, hu⟩) := by
  obtain ⟨-, -, -, t, n, f, hf, hmodelJ, hfix⟩ := h
  obtain ⟨θ, hsurj, hker, -⟩ := exists_fixed_hom hp hZ hu hup
  obtain ⟨e⟩ := nonempty_centerQuotient_perfectResidual_equiv
    (J ⊓ Subgroup.centralizer ({u} : Set G)) (fixSub (centerQuotientConj J ⟨u, hu⟩)) θ hsurj hker
  refine ⟨t, n, f, hf, hmodelJ, ?_⟩
  rcases hfix with h | ⟨ht, hn, hf1, h⟩
  · exact Or.inl (lieModel_of_mulEquiv e h)
  · exact Or.inr ⟨ht, hn, hf1, lieModel_of_mulEquiv e h⟩

omit [Finite G] in
theorem centerQuotientConj_coset_rel {J : Subgroup G} {u d : G}
    (hu : u ∈ Subgroup.normalizer (J : Set G)) (hdJ : d ∈ J) (hud : u * d = d * u) (s : ℤ)
    (hv : u ^ s * d ∈ Subgroup.normalizer (J : Set G)) :
    centerQuotientConj J ⟨u ^ s * d, hv⟩ * (centerQuotientConj J ⟨u, hu⟩ ^ s)⁻¹ ∈
      innerAut (↥J ⧸ Subgroup.center ↥J) := by
  set α₀ := centerQuotientConj J ⟨u, hu⟩ with hα₀
  set dd : ↥J := ⟨d, hdJ⟩ with hdd
  have h1 : (⟨u ^ s * d, hv⟩ : Subgroup.normalizer (J : Set G)) =
      ⟨u, hu⟩ ^ s * ⟨d, Subgroup.le_normalizer hdJ⟩ := Subtype.ext (by simp)
  rw [h1, map_mul, map_zpow]
  have h2 : centerQuotientConj J ⟨d, Subgroup.le_normalizer hdJ⟩ =
      MulAut.conj (dd : ↥J ⧸ Subgroup.center ↥J) := centerQuotientConj_of_mem dd
  rw [h2]
  have hfix : α₀ (dd : ↥J ⧸ Subgroup.center ↥J) = (dd : ↥J ⧸ Subgroup.center ↥J) := by
    have : α₀ (dd : ↥J ⧸ Subgroup.center ↥J) = ((⟨u * (dd : G) * u⁻¹,
        (Subgroup.mem_normalizer_iff.mp hu (dd : G)).mp dd.2⟩ : J) : ↥J ⧸ Subgroup.center ↥J) :=
      rfl
    rw [this]
    congr 1
    apply Subtype.ext
    show u * d * u⁻¹ = d
    rw [hud]
    group
  have hc : Commute α₀ (MulAut.conj (dd : ↥J ⧸ Subgroup.center ↥J)) := by
    refine MulEquiv.ext fun x => ?_
    change α₀ ((dd : ↥J ⧸ Subgroup.center ↥J) * x * (dd : ↥J ⧸ Subgroup.center ↥J)⁻¹) =
      (dd : ↥J ⧸ Subgroup.center ↥J) * α₀ x * (dd : ↥J ⧸ Subgroup.center ↥J)⁻¹
    rw [map_mul, map_mul, map_inv, hfix]
  have hcs := (Commute.zpow_left hc s).eq
  rw [hcs, mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨_, rfl⟩

theorem fixedFacts_of_setting (hT : ∀ t, TagFixedFacts t) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {J : Subgroup G} (hq : CFSG.IsQuasisimple ↥J) (hZ : ¬ p ∣ Nat.card (Subgroup.center J))
    (he : evenRank G ≤ 3) {u v c : G} (hfa : InducesFieldAut p u J) (hup : u ^ p = 1)
    (hv : v ∈ Subgroup.normalizer (J : Set G)) (hvp : v ^ p = 1)
    (hvJ : v ∉ J ⊔ Subgroup.centralizer (J : Set G))
    (hcC : c ∈ Subgroup.centralizer (J : Set G)) (hc1 : c ≠ 1) (hcp : c ^ p = 1)
    (huc : u * c = c * u) (hvc : v * c = c * v)
    (hrel : ∃ (s : ℤ) (d : G), ¬ (p : ℤ) ∣ s ∧ d ∈ J ∧ u * d = d * u ∧ v = u ^ s * d) :
    FixedFacts p (centerQuotientConj J ⟨v, hv⟩) := by
  have hp2 : p ≠ 2 := by omega
  have hu : u ∈ Subgroup.normalizer (J : Set G) := hfa.1
  have huJ : u ∉ J ⊔ Subgroup.centralizer (J : Set G) := hfa.2.1
  have hinn : ∀ {w : G} (hw : w ∈ Subgroup.normalizer (J : Set G)),
      w ∉ J ⊔ Subgroup.centralizer (J : Set G) →
      centerQuotientConj J ⟨w, hw⟩ ∉ innerAut (↥J ⧸ Subgroup.center ↥J) := by
    intro w hw hwJ
    rintro ⟨q, hq'⟩
    exact hwJ (mem_sup_of_inner hq.1 hw hq'.symm)
  obtain ⟨t, n, f₀, hf₀, hM, hX⟩ := fieldAutT_of_inducesFieldAut hp hZ hu hup hfa
  obtain ⟨s, d, hs, hdJ, hud, hvd⟩ := hrel
  have hvd' : u ^ s * d ∈ Subgroup.normalizer (J : Set G) := hvd ▸ hv
  refine hT t _ p hp hp5 (localRankLeTwo_of_evenRank he hp hp2 hZ hcC hc1 hcp) n f₀ hf₀ hM
    _ (centerQuotientConj_pow hu hup) (hinn hu huJ)
    (localRankAut_of_evenRank he hp hp2 hZ hu hup huJ hcC hc1 hcp huc) hX _
    (centerQuotientConj_pow hv hvp) (hinn hv hvJ)
    (localRankAut_of_evenRank he hp hp2 hZ hv hvp hvJ hcC hc1 hcp hvc) ⟨s, hs, ?_⟩
  subst hvd
  exact centerQuotientConj_coset_rel hu hdJ hud s hv

end Transfer

section Back

variable {G : Type} [Group G] [Finite G] {p : ℕ} {J : Subgroup G} {u : G}

omit [Finite G] in
theorem orderOf_dvd_card_center_of_mem_ker {hu : u ∈ Subgroup.normalizer (J : Set G)}
    {θ : ↥(J ⊓ Subgroup.centralizer ({u} : Set G)) →* ↥(fixSub (centerQuotientConj J ⟨u, hu⟩))}
    (hθ : ∀ x : ↥(J ⊓ Subgroup.centralizer ({u} : Set G)),
      ((θ x : ↥(fixSub (centerQuotientConj J ⟨u, hu⟩))) : ↥J ⧸ Subgroup.center ↥J) =
        ((⟨(x : G), x.2.1⟩ : J) : ↥J ⧸ Subgroup.center ↥J))
    (z : ↥(J ⊓ Subgroup.centralizer ({u} : Set G))) (hz : z ∈ θ.ker) :
    orderOf z ∣ Nat.card (Subgroup.center J) := by
  have hπ : ((⟨(z : G), z.2.1⟩ : J) : ↥J ⧸ Subgroup.center ↥J) = 1 := by
    rw [← hθ z, MonoidHom.mem_ker.mp hz]
    rfl
  have hc : (⟨(z : G), z.2.1⟩ : J) ∈ Subgroup.center J := (QuotientGroup.eq_one_iff _).mp hπ
  have h1 : orderOf (⟨(z : G), z.2.1⟩ : J) = orderOf z :=
    orderOf_injective
      (Subgroup.inclusion (inf_le_left : J ⊓ Subgroup.centralizer ({u} : Set G) ≤ J))
      (Subgroup.inclusion_injective _) z
  have h2 := orderOf_dvd_natCard (⟨(⟨(z : G), z.2.1⟩ : J), hc⟩ : Subgroup.center J)
  rwa [Subgroup.orderOf_mk, h1] at h2

omit [Finite G] in
theorem inSubgroup_perfectResidual_le_self (X : Subgroup G) : inSubgroup perfectResidual X ≤ X :=
  Subgroup.map_subtype_le _

theorem exists_preimage_of_mem_fixRes (hp : p.Prime) (hZ : ¬ p ∣ Nat.card (Subgroup.center J))
    (hu : u ∈ Subgroup.normalizer (J : Set G)) (hup : u ^ p = 1)
    {x : ↥J ⧸ Subgroup.center ↥J} (hx : x ∈ fixRes (centerQuotientConj J ⟨u, hu⟩)) :
    ∃ (e : G) (he : e ∈ inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G))),
      ((⟨e, (inSubgroup_perfectResidual_le_self _ he).1⟩ : J) : ↥J ⧸ Subgroup.center ↥J) = x := by
  obtain ⟨θ, hsurj, -, hθ⟩ := exists_fixed_hom hp hZ hu hup
  obtain ⟨y, hy, hyx⟩ := hx
  have hmap : (perfectResidual ↥(J ⊓ Subgroup.centralizer ({u} : Set G))).map θ =
      perfectResidual ↥(fixSub (centerQuotientConj J ⟨u, hu⟩)) :=
    finite_perfectResidual_map_eq θ hsurj
  rw [← hmap] at hy
  obtain ⟨c, hc, hcy⟩ := hy
  refine ⟨(c : G), ⟨c, hc, rfl⟩, ?_⟩
  rw [← hyx, ← hcy]
  exact (hθ c).symm

theorem pElement_mem_perfectResidual_of_fixedFacts (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) (hu : u ∈ Subgroup.normalizer (J : Set G))
    (hup : u ^ p = 1) (hF : FixedFacts p (centerQuotientConj J ⟨u, hu⟩)) {g : G}
    (hg : g ∈ J ⊓ Subgroup.centralizer ({u} : Set G)) (hgp : ∃ k : ℕ, orderOf g = p ^ k) :
    g ∈ inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G)) := by
  obtain ⟨θ, hsurj, hker, hθ⟩ := exists_fixed_hom hp hZ hu hup
  obtain ⟨k, hk⟩ := hgp
  let gC : ↥(J ⊓ Subgroup.centralizer ({u} : Set G)) := ⟨g, hg⟩
  have hgCk : gC ^ (p ^ k) = 1 := by
    apply Subtype.ext
    show g ^ (p ^ k) = 1
    rw [← hk]
    exact pow_orderOf_eq_one g
  have hθp : ∃ j : ℕ, orderOf ((θ gC : ↥(fixSub (centerQuotientConj J ⟨u, hu⟩))) :
      ↥J ⧸ Subgroup.center ↥J) = p ^ j := by
    have h1 : orderOf (θ gC) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hgCk, map_one])
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h1
    exact ⟨j, by rw [Subgroup.orderOf_coe]; exact hj⟩
  have hmem := hF.pElements _ (θ gC).2 hθp
  have hres : θ gC ∈ perfectResidual ↥(fixSub (centerQuotientConj J ⟨u, hu⟩)) := by
    obtain ⟨y, hy, hyeq⟩ := hmem
    have : y = θ gC := Subtype.ext hyeq
    rw [← this]
    exact hy
  have hkerp : ∀ z ∈ θ.ker, Nat.Coprime (orderOf z) p := fun z hz =>
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (fun h => hZ (h.trans (orderOf_dvd_card_center_of_mem_ker hθ z hz))))
  exact ⟨gC, mem_perfectResidual_of_map hsurj hker hkerp hgCk hres, rfl⟩

theorem central_of_fixedFacts (hp : p.Prime) (hZ : ¬ p ∣ Nat.card (Subgroup.center J))
    (hu : u ∈ Subgroup.normalizer (J : Set G)) (hup : u ^ p = 1)
    (hF : FixedFacts p (centerQuotientConj J ⟨u, hu⟩)) (g : ↥J)
    (hg : ∀ e ∈ inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G)),
      (g : G) * e = e * (g : G)) : g ∈ Subgroup.center ↥J := by
  by_contra hgc
  set gbar : ↥J ⧸ Subgroup.center ↥J := (g : ↥J ⧸ Subgroup.center ↥J) with hgbar
  have hgbar1 : gbar ≠ 1 := fun h => hgc ((QuotientGroup.eq_one_iff g).mp h)
  have hcomm : ∀ x ∈ fixRes (centerQuotientConj J ⟨u, hu⟩), x * gbar = gbar * x := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := exists_preimage_of_mem_fixRes hp hZ hu hup hx
    have h1 := hg e he
    have h2 : (⟨e, (inSubgroup_perfectResidual_le_self _ he).1⟩ : J) * g =
        g * ⟨e, (inSubgroup_perfectResidual_le_self _ he).1⟩ :=
      Subtype.ext (by simpa using h1.symm)
    rw [hgbar, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h2]
  have hsolv : Group.IsSolvable ↥(Subgroup.zpowers gbar) := by
    have : IsCyclic ↥(Subgroup.zpowers gbar) := inferInstance
    have : CommGroup ↥(Subgroup.zpowers gbar) := IsCyclic.commGroup
    infer_instance
  refine hF.nonLocalized (Subgroup.zpowers gbar) (fun h => hgbar1 (Subgroup.zpowers_eq_bot.mp h))
    hsolv ?_
  intro x hx
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_left (show Commute gbar x from (hcomm x hx).symm) i).eq

theorem commutator_eq_bot_of_fixedFacts (hp : p.Prime) (hZ : ¬ p ∣ Nat.card (Subgroup.center J))
    (hu : u ∈ Subgroup.normalizer (J : Set G)) (hup : u ^ p = 1)
    (hF : FixedFacts p (centerQuotientConj J ⟨u, hu⟩)) (S : Subgroup G) (hSJ : S ≤ J)
    (hS2 : IsPGroup 2 S)
    (hS : inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G)) ≤
      Subgroup.normalizer (S : Set G)) :
    ⁅S, inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G))⁆ = ⊥ := by
  set π : ↥J →* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.mk' (Subgroup.center ↥J) with hπ
  set Sbar : Subgroup (↥J ⧸ Subgroup.center ↥J) := (S.subgroupOf J).map π with hSbar
  have hSbar2 : IsPGroup 2 Sbar := (hS2.comap_subtype).map _
  have hsolv : Group.IsSolvable ↥Sbar := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent ↥Sbar := hSbar2.isNilpotent
    infer_instance
  have hnorm : fixRes (centerQuotientConj J ⟨u, hu⟩) ≤ Subgroup.normalizer (Sbar : Set _) := by
    refine le_normalizer_of_conj_mem _ _ ?_
    intro x hx y hy
    obtain ⟨e, he, rfl⟩ := exists_preimage_of_mem_fixRes hp hZ hu hup hx
    set eJ : ↥J := ⟨e, (inSubgroup_perfectResidual_le_self _ he).1⟩ with heJ
    obtain ⟨sJ, hsJ, rfl⟩ := hy
    have hs : (sJ : G) ∈ S := Subgroup.mem_subgroupOf.mp hsJ
    have h1 := (Subgroup.mem_normalizer_iff.mp (hS he) (sJ : G)).mp hs
    refine ⟨eJ * sJ * eJ⁻¹, Subgroup.mem_subgroupOf.mpr (by simpa [heJ] using h1), ?_⟩
    show π (eJ * sJ * eJ⁻¹) =
      (eJ : ↥J ⧸ Subgroup.center ↥J) * π sJ * (eJ : ↥J ⧸ Subgroup.center ↥J)⁻¹
    rw [map_mul, map_mul, map_inv]
    rfl
  have hbot : Sbar = ⊥ := by
    by_contra hne
    exact hF.nonLocalized Sbar hne hsolv hnorm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hsbar : π ⟨s, hSJ hs⟩ ∈ Sbar := ⟨⟨s, hSJ hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hsbar
  have hsc : (⟨s, hSJ hs⟩ : J) ∈ Subgroup.center J := (QuotientGroup.eq_one_iff _).mp hsbar
  have heJ : e ∈ J := (inSubgroup_perfectResidual_le_self _ he).1
  have := Subgroup.mem_center_iff.mp hsc ⟨e, heJ⟩
  exact congrArg Subtype.val this

end Back

section Coset

variable {G : Type} [Group G] [Finite G]

theorem inducesFieldAut_coset_of_tags (hT : ∀ t, TagFixedFacts t) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {J : Subgroup G} (hq : CFSG.IsQuasisimple ↥J)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) (he : evenRank G ≤ 3) {a c d : G}
    (hfa : InducesFieldAut p a J) (hap : a ^ p = 1)
    (hcC : c ∈ Subgroup.centralizer (J : Set G)) (hc1 : c ≠ 1) (hcp : c ^ p = 1)
    (hac : a * c = c * a) (hdJ : d ∈ J) (hdp : d ^ p = 1) (had : a * d = d * a) (s : ℤ)
    (hs : ¬ (p : ℤ) ∣ s) : InducesFieldAut p (a ^ s * d) J := by
  have ha : a ∈ Subgroup.normalizer (J : Set G) := hfa.1
  have hdN : d ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hdJ
  have hv : a ^ s * d ∈ Subgroup.normalizer (J : Set G) :=
    Subgroup.mul_mem _ (Subgroup.zpow_mem _ ha s) hdN
  have hcad : Commute (a ^ s) d := Commute.zpow_left (show Commute a d from had) s
  have hvp : (a ^ s * d) ^ p = 1 := by
    rw [hcad.mul_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap,
      one_zpow, hdp, one_mul]
  have hvJ : a ^ s * d ∉ J ⊔ Subgroup.centralizer (J : Set G) := by
    intro hmem
    have hd' : d ∈ J ⊔ Subgroup.centralizer (J : Set G) := Subgroup.mem_sup_left hdJ
    have h1 : a ^ s ∈ J ⊔ Subgroup.centralizer (J : Set G) := by
      have := Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hd')
      simpa using this
    exact hfa.2.1 ((Subgroup.zpowers_le.mpr h1) (mem_zpowers_zpow_of_pow_eq_one hp hap hs))
  have hvc : (a ^ s * d) * c = c * (a ^ s * d) := by
    have h1 : Commute (a ^ s) c := Commute.zpow_left (show Commute a c from hac) s
    have h2 : Commute d c := (Subgroup.mem_centralizer_iff.mp hcC) d hdJ
    exact (h1.mul_left h2).eq
  have hFF := fixedFacts_of_setting hT hp hp5 hq hZ he hfa hap hv hvp hvJ hcC hc1 hcp hac hvc
    ⟨s, d, hs, hdJ, had, rfl⟩
  exact inducesFieldAut_of_fieldAutT hp hZ hv hvp hvJ hFF.fieldAutT

end Coset

end CFSG.RankThree.PartOne.FieldFix
