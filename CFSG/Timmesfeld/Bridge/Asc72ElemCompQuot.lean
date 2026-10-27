module

public import CFSG.Timmesfeld.Bridge.Asc72ElemComp
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FWN2

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Open (IsElemAbelian)

theorem otg2_eq_one_of_odd_sq {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : Odd (Nat.card K)) {x : G} (hx : x ∈ K) (hx2 : x * x = 1) : x = 1 := by
  have hodd : Odd (orderOf (⟨x, hx⟩ : K)) := hK.of_dvd_nat (orderOf_dvd_natCard _)
  have hdvd2 : orderOf (⟨x, hx⟩ : K) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, sq]; exact hx2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
  · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  · rw [h2] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega

theorem otg2_odd_orderOf {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : Odd (Nat.card K)) {x : G} (hx : x ∈ K) : Odd (orderOf x) := by
  have h : orderOf x = orderOf (⟨x, hx⟩ : K) := Subgroup.orderOf_coe (⟨x, hx⟩ : K)
  rw [h]
  exact hK.of_dvd_nat (orderOf_dvd_natCard _)

theorem otg2_isMulCommutative {G : Type} [Group G] {H : Subgroup G}
    (h : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) : IsMulCommutative H :=
  ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩

theorem otg2_isElemAbelian_map {G H : Type} [Group G] [Group H] (φ : G →* H) {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : IsElemAbelian 2 (E.map φ) := by
  refine ⟨otg2_isMulCommutative ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, (commute_of_mem_isElemAbelian hE ha hb).eq]
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hE.2 a ha, map_one]

theorem otg2_mem_of_sq_mem {G : Type} [Group G] {Z : Subgroup G} {w : G} (hw : w * w ∈ Z)
    (hodd : Odd (orderOf w)) : w ∈ Z := by
  obtain ⟨k, hk⟩ := hodd
  have hpow : w ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one w
  have h2 : (w * w) ^ (k + 1) = w := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hpow, one_mul]
  rw [← h2]
  exact Z.pow_mem hw (k + 1)

theorem otg2_mem_centralizer_singleton {G : Type} [Group G] {g k : G} :
    k ∈ Subgroup.centralizer ({g} : Set G) ↔ Commute g k := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact h g (Set.mem_singleton g)
  · intro h y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact h

theorem otg2_mul_conj_mem_oddCore {G : Type} [Group G] {D : Set G} (hS : Setup G D) {b h : G}
    (hb : b ∈ D) (hh : h ∈ CFSG.oddCore G) : b * (h * b * h⁻¹) ∈ CFSG.oddCore G := by
  have h1 : b * h * b⁻¹ ∈ CFSG.oddCore G :=
    (inferInstance : (CFSG.oddCore G).Normal).conj_mem h hh b
  have h2 : b * h * b⁻¹ * h⁻¹ ∈ CFSG.oddCore G :=
    (CFSG.oddCore G).mul_mem h1 ((CFSG.oddCore G).inv_mem hh)
  have heq : b * (h * b * h⁻¹) = b * h * b⁻¹ * h⁻¹ := by
    rw [hS.oddT.inv_eq hb]
    group
  rw [heq]
  exact h2

theorem otg2_exists_commute_pair {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    (hns : ¬ Group.IsSolvable G) : ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ Commute a b := by
  by_contra hcon
  obtain ⟨d, hd⟩ := hS.nonempty
  letI : Fintype G := Fintype.ofFinite G
  have hd1 : d ≠ 1 := hS.oddT.ne_one hd
  have hdd : d * d = 1 := hS.oddT.mul_self_eq_one hd
  have hiso : ∀ g : G, (g * d * g⁻¹) * d = d * (g * d * g⁻¹) → g * d * g⁻¹ = d := by
    intro g hc
    by_contra hne
    exact hcon ⟨g * d * g⁻¹, hS.conj_mem g hd, d, hd, hne, hc⟩
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G d hd1 hdd hiso
  haveI := hNn
  have hxN : ∀ x ∈ D, x⁻¹ * d ∈ N := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.mp (hS.isConj hd hx)
    have h1 := hN c
    rw [hc, hS.oddT.inv_eq hd] at h1
    rw [hS.oddT.inv_eq hx]
    exact h1
  have hall : ∀ x : G, (QuotientGroup.mk x : G ⧸ N) ∈
      Subgroup.closure {(QuotientGroup.mk d : G ⧸ N)} := by
    intro x
    have hle : Subgroup.closure D ≤
        (Subgroup.closure {(QuotientGroup.mk d : G ⧸ N)}).comap (QuotientGroup.mk' N) := by
      rw [Subgroup.closure_le]
      intro y hy
      refine Subgroup.mem_comap.mpr ?_
      have hyd : (QuotientGroup.mk y : G ⧸ N) = QuotientGroup.mk d :=
        QuotientGroup.eq.mpr (hxN y hy)
      rw [QuotientGroup.mk'_apply, hyd]
      exact Subgroup.subset_closure (Set.mem_singleton _)
    have hx : x ∈ Subgroup.closure D := by
      rw [hS.gen]
      exact Subgroup.mem_top x
    exact Subgroup.mem_comap.mp (hle hx)
  have hcomm : ∀ a b : G ⧸ N, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    refine (commute_of_mem_closure (S := {(QuotientGroup.mk d : G ⧸ N)})
      (T := {(QuotientGroup.mk d : G ⧸ N)}) ?_ (hall x) (hall y)).eq
    intro u hu v hv
    rw [Set.mem_singleton_iff.mp hu, Set.mem_singleton_iff.mp hv]
  haveI : Group.IsSolvable (G ⧸ N) := Group.isSolvable_of_comm hcomm
  haveI : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  exact hns (Group.isSolvable_of_subgroup_quotient N)

theorem otg2_commute_of_mem_oddCore {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d}))
    {a b h : G} (ha : a ∈ D) (hb : b ∈ D) (hab : Commute a b) (hh : h ∈ CFSG.oddCore G)
    (hha : Commute h a) : Commute h b := by
  by_contra hnc
  have hb' : h * b * h⁻¹ ∈ D := hS.conj_mem h hb
  have hbne : h * b * h⁻¹ ≠ b := fun heq => hnc (mul_inv_eq_iff_eq_mul.mp heq)
  have hfix : h * a * h⁻¹ = a := by
    rw [hha.eq, mul_inv_cancel_right]
  have hb'a : Commute (h * b * h⁻¹) a := by
    have := Commute.map hab.symm (MulAut.conj h)
    rw [MulAut.conj_apply, MulAut.conj_apply, hfix] at this
    exact this
  have hbb' : Commute b (h * b * h⁻¹) :=
    commute_of_mem_isElemAbelian (hE a ha)
      (Subgroup.subset_closure (show b ∈ {e | e ∈ D ∧ Commute e a} from ⟨hb, hab.symm⟩))
      (Subgroup.subset_closure (show h * b * h⁻¹ ∈ {e | e ∈ D ∧ Commute e a} from ⟨hb', hb'a⟩))
  have hxO := otg2_mul_conj_mem_oddCore hS hb hh
  have hx2 : (b * (h * b * h⁻¹)) * (b * (h * b * h⁻¹)) = 1 := by
    calc (b * (h * b * h⁻¹)) * (b * (h * b * h⁻¹))
        = b * ((h * b * h⁻¹) * b) * (h * b * h⁻¹) := by group
      _ = b * (b * (h * b * h⁻¹)) * (h * b * h⁻¹) := by rw [← hbb'.eq]
      _ = (b * b) * ((h * b * h⁻¹) * (h * b * h⁻¹)) := by group
      _ = 1 := by
        rw [hS.oddT.mul_self_eq_one hb, hS.oddT.mul_self_eq_one hb', one_mul]
  have hx1 := otg2_eq_one_of_odd_sq
    (CFSG.ABGLocalTools.odd_card_oddCore : Odd (Nat.card (CFSG.oddCore G))) hxO hx2
  apply hbne
  have hinv := eq_inv_of_mul_eq_one_right hx1
  rw [hinv, hS.oddT.inv_eq hb]

theorem otg2_mul_centralizes_oddCore {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d}))
    {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hne : a ≠ b) (hab : Commute a b) :
    ∀ x ∈ CFSG.oddCore G, Commute x (a * b) := by
  have hO : Odd (Nat.card (CFSG.oddCore G)) := CFSG.ABGLocalTools.odd_card_oddCore
  have hnorm : ∀ x : G, x ∈ Subgroup.normalizer ((CFSG.oddCore G : Subgroup G) : Set G) := by
    intro x
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  have hsub := CFSG.ComponentClassification.GrSLit.FW.le_sup_inf_centralizer_of_four hO
    (hS.oddT.mul_self_eq_one ha) (hS.oddT.mul_self_eq_one hb) hab.eq (hS.oddT.ne_one ha)
    (hS.oddT.ne_one hb) hne (hnorm a) (hnorm b)
  have hY : (CFSG.oddCore G ⊓ Subgroup.centralizer {a}) ⊔
      (CFSG.oddCore G ⊓ Subgroup.centralizer {b}) ⊔
      (CFSG.oddCore G ⊓ Subgroup.centralizer {a * b}) ≤
      CFSG.oddCore G ⊓ Subgroup.centralizer {a * b} := by
    refine sup_le (sup_le ?_ ?_) le_rfl
    · rintro g ⟨hgO, hga⟩
      have hga' : Commute g a := (otg2_mem_centralizer_singleton.mp hga).symm
      have hgb := otg2_commute_of_mem_oddCore hS hE ha hb hab hgO hga'
      exact ⟨hgO, otg2_mem_centralizer_singleton.mpr (hga'.mul_right hgb).symm⟩
    · rintro g ⟨hgO, hgb⟩
      have hgb' : Commute g b := (otg2_mem_centralizer_singleton.mp hgb).symm
      have hga := otg2_commute_of_mem_oddCore hS hE hb ha hab.symm hgO hgb'
      exact ⟨hgO, otg2_mem_centralizer_singleton.mpr (hga.mul_right hgb').symm⟩
  intro x hx
  exact (otg2_mem_centralizer_singleton.mp (hY (hsub hx)).2).symm

theorem otg2_commute_of_mem_oddCore_mul {G : Type} [Group G] [Finite G] {D : Set G}
    (hS : Setup G D) {a b h : G} (ha : a ∈ D) (hb : b ∈ D) (hne : a ≠ b) (hab : Commute a b)
    (hO_ab : ∀ x ∈ CFSG.oddCore G, Commute x (a * b)) (hh : h ∈ CFSG.oddCore G) :
    Commute h b := by
  by_contra hnc
  have hb' : h * b * h⁻¹ ∈ D := hS.conj_mem h hb
  have hbne : h * b * h⁻¹ ≠ b := fun heq => hnc (mul_inv_eq_iff_eq_mul.mp heq)
  have hxO := otg2_mul_conj_mem_oddCore hS hb hh
  have hx1 : b * (h * b * h⁻¹) ≠ 1 := by
    intro h1
    apply hbne
    rw [eq_inv_of_mul_eq_one_right h1, hS.oddT.inv_eq hb]
  have hodd_x : Odd (orderOf (b * (h * b * h⁻¹))) :=
    otg2_odd_orderOf (CFSG.ABGLocalTools.odd_card_oddCore : Odd (Nat.card (CFSG.oddCore G))) hxO
  have hord_ab : orderOf (a * b) = 2 := hS.oddT.orderOf_mul_eq_two ha hb hne hab
  have hcop : Nat.Coprime (orderOf (a * b)) (orderOf (b * (h * b * h⁻¹))) := by
    rw [hord_ab]
    exact Nat.coprime_two_left.mpr hodd_x
  have hord : orderOf (a * b * (b * (h * b * h⁻¹))) = 2 * orderOf (b * (h * b * h⁻¹)) := by
    rw [(hO_ab _ hxO).symm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hord_ab]
  have hbx : a * (h * b * h⁻¹) = a * b * (b * (h * b * h⁻¹)) := by
    calc a * (h * b * h⁻¹) = a * (b * b) * (h * b * h⁻¹) := by
          rw [hS.oddT.mul_self_eq_one hb, mul_one]
      _ = a * b * (b * (h * b * h⁻¹)) := by group
  have hodd_or := hS.oddT.2 a ha (h * b * h⁻¹) hb'
  rw [hbx, hord] at hodd_or
  rcases hodd_or with hdvd | hodd
  · have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hne1 : orderOf (b * (h * b * h⁻¹)) ≠ 1 := fun h1 => hx1 (orderOf_eq_one_iff.mp h1)
    obtain ⟨j, hj⟩ := hodd_x
    omega
  · obtain ⟨k, hk⟩ := hodd
    omega

theorem otg2_oddCore_le_center {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d}))
    {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hne : a ≠ b) (hab : Commute a b) :
    CFSG.oddCore G ≤ Subgroup.center G := by
  have hO_ab := otg2_mul_centralizes_oddCore hS hE ha hb hne hab
  have hb_cent : ∀ h ∈ CFSG.oddCore G, Commute h b := fun h hh =>
    otg2_commute_of_mem_oddCore_mul hS ha hb hne hab hO_ab hh
  have hD : ∀ d ∈ D, ∀ x ∈ CFSG.oddCore G, Commute d x := by
    intro d hd x hx
    obtain ⟨c, hc⟩ := isConj_iff.mp (hS.isConj hb hd)
    have hx' : c⁻¹ * x * c ∈ CFSG.oddCore G := by
      have := (inferInstance : (CFSG.oddCore G).Normal).conj_mem x hx c⁻¹
      rwa [inv_inv] at this
    have hbx : Commute (c⁻¹ * x * c) b := hb_cent _ hx'
    show d * x = x * d
    rw [← hc]
    show c * b * c⁻¹ * x = x * (c * b * c⁻¹)
    calc c * b * c⁻¹ * x = c * (b * (c⁻¹ * x * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * x * c) * b) * c⁻¹ := by rw [hbx.symm.eq]
      _ = x * (c * b * c⁻¹) := by group
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure D := by
    rw [hS.gen]
    exact Subgroup.mem_top g
  exact (commute_of_mem_closure (S := D) (T := {x})
    (fun u hu v hv => by
      rw [Set.mem_singleton_iff.mp hv]
      exact hD u hu x hx) hg (Subgroup.subset_closure (Set.mem_singleton x))).eq

theorem otg2_solvableRadical_le_center {G : Type} [Group G] [Finite G]
    (hO2 : CFSG.pCore 2 G ≤ Subgroup.center G) (hO : CFSG.oddCore G ≤ Subgroup.center G) :
    CFSG.solvableRadical G ≤ Subgroup.center G := by
  haveI hSn : (CFSG.solvableRadical G).Normal := Subgroup.sSup_normal _ fun _ hN => hN.1
  haveI hSs : Group.IsSolvable (CFSG.solvableRadical G) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hF : CFSG.fittingSubgroupOf (CFSG.solvableRadical G) ≤ Subgroup.center G := by
    refine le_trans (CFSG.fittingSubgroupOf_le_fittingSubgroup _ hSn) ?_
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    by_cases hp : p.1.1 = 2
    · rw [hp]
      exact hO2
    · have hodd : Odd (Nat.card (CFSG.pCore p.1.1 G)) := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := p.1.1) (G := G))
        rw [hn]
        exact Odd.pow ((Nat.prime_of_mem_primeFactors p.1.2).odd_of_ne_two hp)
      exact le_trans (le_sSup ⟨CFSG.pCore_normal, hodd⟩ : CFSG.pCore p.1.1 G ≤ CFSG.oddCore G) hO
  intro s hs
  have hcent := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
    (G := ↥(CFSG.solvableRadical G)) hSs
  have ht : (⟨s, hs⟩ : ↥(CFSG.solvableRadical G)) ∈
      Subgroup.centralizer
        ((CFSG.fittingSubgroup ↥(CFSG.solvableRadical G) :
          Subgroup ↥(CFSG.solvableRadical G)) : Set ↥(CFSG.solvableRadical G)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkZ : ((k : ↥(CFSG.solvableRadical G)) : G) ∈ Subgroup.center G :=
      hF (Subgroup.mem_map_of_mem (CFSG.solvableRadical G).subtype hk)
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp hkZ s).symm
  exact hF (Subgroup.mem_map_of_mem (CFSG.solvableRadical G).subtype (hcent ht))

theorem otg2_center_le_solvableRadical {G : Type} [Group G] :
    Subgroup.center G ≤ CFSG.solvableRadical G := by
  have hs : Group.IsSolvable (Subgroup.center G) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  exact le_sSup ⟨inferInstance, hs⟩

section Certified


theorem otg2_isBender_quotient {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d}))
    (hns : ¬ Group.IsSolvable G) (hSZ : CFSG.solvableRadical G ≤ Subgroup.center G) :
    CFSG.BenderSuzuki.IsBenderGroup (G ⧸ Subgroup.center G) := by
  haveI hZs : Group.IsSolvable (Subgroup.center G) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  obtain ⟨b₀, hb₀⟩ := hS.nonempty
  have hnotcen : ∀ d ∈ D, d ∉ Subgroup.center G := by
    intro d hd hdZ
    apply hns
    have hDZ : D ⊆ (Subgroup.center G : Set G) := by
      intro x hx
      obtain ⟨c, hc⟩ := isConj_iff.mp (hS.isConj hd hx)
      have hcd : c * d * c⁻¹ = d := by
        rw [Subgroup.mem_center_iff.mp hdZ c]
        group
      rw [← hc, hcd]
      exact hdZ
    have hle : Subgroup.closure D ≤ Subgroup.center G := by
      rw [Subgroup.closure_le]
      exact hDZ
    rw [hS.gen] at hle
    refine Group.isSolvable_of_comm fun a b => ?_
    exact (Subgroup.mem_center_iff.mp (hle (Subgroup.mem_top a)) b).symm
  have hφ : ∀ d ∈ D, (QuotientGroup.mk' (Subgroup.center G)) d ≠ 1 := by
    intro d hd h1
    exact hnotcen d hd ((QuotientGroup.eq_one_iff d).mp h1)
  have hS' : Setup (G ⧸ Subgroup.center G) ((QuotientGroup.mk' (Subgroup.center G)) '' D) := by
    refine ⟨⟨(QuotientGroup.mk' (Subgroup.center G)) b₀, ?_⟩,
      hS.oddT.image (QuotientGroup.mk' (Subgroup.center G)) hφ, ?_⟩
    · ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Set.mem_setOf_eq]
        obtain ⟨c, hc⟩ := isConj_iff.mp (hS.isConj hb₀ hx)
        refine isConj_iff.mpr ⟨(QuotientGroup.mk' (Subgroup.center G)) c, ?_⟩
        rw [← hc]
        simp
      · intro hg
        have hg' : IsConj ((QuotientGroup.mk' (Subgroup.center G)) b₀) g := hg
        obtain ⟨cb, hcb⟩ := isConj_iff.mp hg'
        obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) cb
        refine ⟨c * b₀ * c⁻¹, hS.conj_mem c hb₀, ?_⟩
        rw [← hcb]
        simp
    · rw [eq_top_iff]
      intro y _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
      have hx : x ∈ Subgroup.closure D := by
        rw [hS.gen]
        exact Subgroup.mem_top x
      have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center G)) hx
      rwa [MonoidHom.map_closure] at hmem
  have hrad' : ∀ N : Subgroup (G ⧸ Subgroup.center G), N.Normal → Group.IsSolvable N → N = ⊥ := by
    intro N hN hNs
    haveI := hN
    haveI := hNs
    have hcomap : Group.IsSolvable (N.comap (QuotientGroup.mk' (Subgroup.center G))) :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_comap_mk'
    have hle : N.comap (QuotientGroup.mk' (Subgroup.center G)) ≤ CFSG.solvableRadical G :=
      le_sSup ⟨Subgroup.Normal.comap hN _, hcomap⟩
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
    have hx : x ∈ CFSG.solvableRadical G := hle hy
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hSZ hx
  have hE' : ∀ dh ∈ (QuotientGroup.mk' (Subgroup.center G)) '' D,
      IsElemAbelian 2 (Subgroup.closure
        {e | e ∈ (QuotientGroup.mk' (Subgroup.center G)) '' D ∧ Commute e dh}) := by
    rintro _ ⟨d, hd, rfl⟩
    have hset : {e | e ∈ (QuotientGroup.mk' (Subgroup.center G)) '' D ∧
        Commute e ((QuotientGroup.mk' (Subgroup.center G)) d)} =
        (QuotientGroup.mk' (Subgroup.center G)) '' {e | e ∈ D ∧ Commute e d} := by
      ext eh
      constructor
      · rintro ⟨⟨e, he, rfl⟩, hc⟩
        rcases hS.oddT.commute_or_odd hd he with hdc | hodd
        · exact ⟨e, ⟨he, hdc.symm⟩, rfl⟩
        · have h1 : (QuotientGroup.mk' (Subgroup.center G)) (d * e) =
              (QuotientGroup.mk' (Subgroup.center G)) (e * d) := by
            rw [map_mul, map_mul]
            exact hc.symm.eq
          have hee : (d * e) * (e * d) = 1 := by
            calc (d * e) * (e * d) = d * (e * e) * d := by group
              _ = 1 := by
                rw [hS.oddT.mul_self_eq_one he, mul_one, hS.oddT.mul_self_eq_one hd]
          have h2 : (QuotientGroup.mk' (Subgroup.center G)) ((d * e) * (d * e)) = 1 := by
            rw [map_mul]
            calc (QuotientGroup.mk' (Subgroup.center G)) (d * e) *
                (QuotientGroup.mk' (Subgroup.center G)) (d * e)
                = (QuotientGroup.mk' (Subgroup.center G)) (d * e) *
                  (QuotientGroup.mk' (Subgroup.center G)) (e * d) := by rw [← h1]
              _ = (QuotientGroup.mk' (Subgroup.center G)) ((d * e) * (e * d)) :=
                (map_mul _ _ _).symm
              _ = 1 := by
                rw [hee, map_one]
          have hsq : (d * e) * (d * e) ∈ Subgroup.center G := (QuotientGroup.eq_one_iff _).mp h2
          have hw : d * e ∈ Subgroup.center G := otg2_mem_of_sq_mem hsq hodd
          refine ⟨d, ⟨hd, Commute.refl d⟩, ?_⟩
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
            hS.oddT.inv_eq hd]
          exact hw
      · rintro ⟨e, ⟨he, hc⟩, rfl⟩
        exact ⟨⟨e, he, rfl⟩, hc.map _⟩
    rw [hset, ← MonoidHom.map_closure]
    exact otg2_isElemAbelian_map _ (hE d hd)
  have hdisc' : Disconnected ((QuotientGroup.mk' (Subgroup.center G)) '' D) := by
    by_contra hnd
    apply hns
    have hall : ∀ x ∈ (QuotientGroup.mk' (Subgroup.center G)) '' D,
        ∀ y ∈ (QuotientGroup.mk' (Subgroup.center G)) '' D, Commute x y := by
      intro x hx y hy
      by_contra hxy
      exact hnd (disconnected_of_not_commute_of_elemAbelian hE' hx hy hxy)
    have hcomm : ∀ x y : G ⧸ Subgroup.center G, x * y = y * x := by
      intro x y
      have hx : x ∈ Subgroup.closure ((QuotientGroup.mk' (Subgroup.center G)) '' D) := by
        rw [hS'.gen]
        exact Subgroup.mem_top x
      have hy : y ∈ Subgroup.closure ((QuotientGroup.mk' (Subgroup.center G)) '' D) := by
        rw [hS'.gen]
        exact Subgroup.mem_top y
      exact (commute_of_mem_closure hall hx hy).eq
    haveI : Group.IsSolvable (G ⧸ Subgroup.center G) := Group.isSolvable_of_comm hcomm
    exact Group.isSolvable_of_subgroup_quotient (Subgroup.center G)
  exact isBenderGroup_of_elemComponents hS' hrad' hdisc' hE'

theorem isBenderGroup_center_quot_of_elemComponents {R : Type} [Group R] [Finite R] {D : Set R}
    (hS : Setup R D)
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d}))
    (hO2 : CFSG.pCore 2 R ≤ Subgroup.center R) (hns : ¬ Group.IsSolvable R) :
    CFSG.solvableRadical R = Subgroup.center R ∧
      CFSG.BenderSuzuki.IsBenderGroup (R ⧸ Subgroup.center R) := by
  obtain ⟨a, ha, b, hb, hne, hab⟩ := otg2_exists_commute_pair hS hns
  have hOZ : CFSG.oddCore R ≤ Subgroup.center R := otg2_oddCore_le_center hS hE ha hb hne hab
  have hSZ : CFSG.solvableRadical R ≤ Subgroup.center R := otg2_solvableRadical_le_center hO2 hOZ
  exact ⟨le_antisymm hSZ otg2_center_le_solvableRadical, otg2_isBender_quotient hS hE hns hSZ⟩

end Certified

end CFSG.Timmesfeld.Bridge.Asc72
