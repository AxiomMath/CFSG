module

public import CFSG.RankThree.GF2n.Parrott.SylowHFacts
public import CFSG.RankThree.GF2n.Parrott.CentralizerOrders
public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.RankThree.GF2n.Parrott.Section3Commutator
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.RankThree.GF2n.Parrott.CommutatorExtraspecial

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]

@[expose] def O3subA : Subgroup QA45.originalSubgroup :=
  O3sub.subgroupOf QA45.originalSubgroup

theorem O3sub_le_QA45 : O3sub ≤ QA45.originalSubgroup := by
  intro x hx
  rw [mem_iff_sift QA45 QA45_ok x]
  exact List.all_eq_true.1 Certificates.certificate946016.O3_le_QA45 x hx

theorem card_O3subA : Nat.card O3subA = 27 := by
  change Nat.card ↥(O3sub.subgroupOf QA45.originalSubgroup) = 27
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe O3sub_le_QA45).toEquiv,
    card_O3sub]

theorem O3subA_le_centralizer :
    O3subA ≤ Subgroup.centralizer
      ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  have hcomm : ((x : QA45.originalSubgroup) : Equiv.Perm (Fin 45)) * sigma1 =
      sigma1 * ((x : QA45.originalSubgroup) : Equiv.Perm (Fin 45)) := by
    exact of_decide_eq_true
      (List.all_eq_true.1 Certificates.certificate946016.O3_le_centralizer_sigma1
        ((x : QA45.originalSubgroup) : Equiv.Perm (Fin 45)) hx)
  simpa using hcomm

@[expose] noncomputable def K (D : QuotientData (z := z) hN) : Subgroup ↥(H z) :=
  Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))

theorem card_K (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    Nat.card (K D) = 10368 :=
  card_centralizer_sigma1Nine (z := z) D h

@[expose] noncomputable def phiC (D : QuotientData (z := z) hN) : K D →* QA45.originalSubgroup :=
  (qH D).comp (K D).subtype

@[simp] theorem phi_apply (D : QuotientData (z := z) hN) (x : K D) :
    phiC D x = qH D (x : H z) := rfl

theorem sigma1Nine_mem_K (D : QuotientData (z := z) hN) :
    sigma1Nine (z := z) D ∈ K D := by
  rw [K, Subgroup.mem_centralizer_singleton_iff]

theorem qH_sigma1Nine_mem_O3subA (D : QuotientData (z := z) hN) :
    phiC D ⟨sigma1Nine (z := z) D, sigma1Nine_mem_K (z := z) D⟩ ∈ O3subA := by
  change qH D (sigma1Nine (z := z) D) ∈ O3subA
  rw [qH_sigma1Nine]
  change sigma1 ∈ O3 ()
  exact Certificates.certificate946016.sigma1_mem_O3

theorem sigma1Nine_mem_comap (D : QuotientData (z := z) hN) :
    (⟨sigma1Nine (z := z) D, sigma1Nine_mem_K (z := z) D⟩ : K D) ∈
      O3subA.comap (phiC D) :=
  Subgroup.mem_comap.mpr (qH_sigma1Nine_mem_O3subA (z := z) D)

theorem ker_phi (D : QuotientData (z := z) hN) :
    (phiC D).ker = ((J z).subgroupOf (H z)).subgroupOf (K D) := by
  ext x
  rw [MonoidHom.mem_ker]
  change qH D (x : H z) = 1 ↔ ((x : H z) ∈ (J z).subgroupOf (H z))
  rw [J_mem_iff]

theorem card_ker_phi (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    Nat.card (phiC D).ker = 16 := by
  have hsub : ((J z).subgroupOf (H z)).subgroupOf (K D) =
      (((J z).subgroupOf (H z)) ⊓ K D).subgroupOf (K D) := by
    ext x
    exact ⟨fun hx => ⟨hx, x.2⟩, fun hx => hx.1⟩
  rw [ker_phi, hsub,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : ((J z).subgroupOf (H z)) ⊓ K D ≤ K D)).toEquiv]
  have hcomm : ((J z).subgroupOf (H z)) ⊓ K D =
      K D ⊓ ((J z).subgroupOf (H z)) := inf_comm _ _
  rw [hcomm]
  change Nat.card ↥(Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z)) ⊓
    (J z).subgroupOf (H z)) = 16
  rw [card_centralizer_inf_J_subgroupOf (z := z) (x := sigma1Nine (z := z) D)]
  exact card_centralizerJ_sigma1Nine h D

theorem range_phi (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    (phiC D).range =
      Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup) := by
  have hcard := Subgroup.card_ker_mul_card_range (phiC D)
  rw [card_ker_phi h D, card_K h D] at hcard
  have hrange : Nat.card (phiC D).range = 648 := by omega
  apply Subgroup.eq_of_le_of_card_ge
  · rintro y ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx : (x : H z) * sigma1Nine (z := z) D =
        sigma1Nine (z := z) D * (x : H z) :=
      Subgroup.mem_centralizer_singleton_iff.mp x.2
    calc phiC D x * (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)
        = qH D (x : H z) * qH D (sigma1Nine (z := z) D) := by
          rw [phi_apply, qH_sigma1Nine (z := z) (D := D)]
      _ = qH D ((x : H z) * sigma1Nine (z := z) D) := (map_mul _ _ _).symm
      _ = qH D (sigma1Nine (z := z) D * (x : H z)) := by rw [hx]
      _ = qH D (sigma1Nine (z := z) D) * qH D (x : H z) := map_mul _ _ _
      _ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) * phiC D x := by
          rw [qH_sigma1Nine (z := z) (D := D), phi_apply]
  · rw [hrange, card_centralizer_sigma1_QA45]

theorem O3subA_le_range_phi (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    O3subA ≤ (phiC D).range := by
  rw [range_phi h D]
  exact O3subA_le_centralizer

theorem card_comap_phiA (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    Nat.card (O3subA.comap (phiC D)) = 432 := by
  have hker_le : (phiC D).ker ≤ O3subA.comap (phiC D) := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : phiC D x = 1 := MonoidHom.mem_ker.mp hx
    rw [hx1]
    exact O3subA.one_mem

  have hrangeRestrict : (O3subA.comap (phiC D).range.subtype).comap
      (phiC D).rangeRestrict = O3subA.comap (phiC D) := by
    rw [Subgroup.comap_comap]
    rw [MonoidHom.subtype_comp_rangeRestrict]
  have hmain := CFSG.GroupTheory.card_comap_eq_card_ker_mul_card
    (phiC D).rangeRestrict (phiC D).rangeRestrict_surjective
    (O3subA.comap (phiC D).range.subtype)
  rw [hrangeRestrict] at hmain
  rw [MonoidHom.ker_rangeRestrict, card_ker_phi h D] at hmain
  have hsub : Nat.card (O3subA.comap (phiC D).range.subtype) = 27 := by
    rw [show O3subA.comap (phiC D).range.subtype =
        O3subA.subgroupOf (phiC D).range from rfl,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (O3subA_le_range_phi h D)).toEquiv,
      card_O3subA]
  rw [hsub] at hmain
  rw [hmain]

noncomputable abbrev s1K (D : QuotientData (z := z) hN) : K D :=
  ⟨sigma1Nine (z := z) D, sigma1Nine_mem_K (z := z) D⟩

noncomputable abbrev s1Comap (D : QuotientData (z := z) hN) :
    ↥(O3subA.comap (phiC D)) :=
  ⟨s1K D, sigma1Nine_mem_comap (z := z) D⟩

theorem orderOf_s1Comap (D : QuotientData (z := z) hN) :
    orderOf (s1Comap D) = 3 := by
  change orderOf (⟨s1K D, sigma1Nine_mem_comap (z := z) D⟩ :
    ↥(O3subA.comap (phiC D))) = 3
  rw [Subgroup.orderOf_mk]
  change orderOf (⟨sigma1Nine (z := z) D, sigma1Nine_mem_K (z := z) D⟩ : K D) = 3
  rw [Subgroup.orderOf_mk]
  exact sigma1Nine_order (z := z) D

theorem isPGroup_zpowers_s1Comap (D : QuotientData (z := z) hN) :
    IsPGroup 3 (Subgroup.zpowers (s1Comap D)) := by
  apply IsPGroup.of_card (n := 1)
  rw [Nat.card_zpowers, orderOf_s1Comap]
  norm_num

@[expose] noncomputable def O3Sylow (D : QuotientData (z := z) hN) :
    Sylow 3 ↥(O3subA.comap (phiC D)) :=
  Classical.choose (isPGroup_zpowers_s1Comap (z := z) D).exists_le_sylow

theorem le_O3Sylow (D : QuotientData (z := z) hN) :
    Subgroup.zpowers (s1Comap D) ≤ (O3Sylow D : Subgroup ↥(O3subA.comap (phiC D))) :=
  Classical.choose_spec (isPGroup_zpowers_s1Comap (z := z) D).exists_le_sylow

@[expose] noncomputable def toH (D : QuotientData (z := z) hN) :
    ↥(O3subA.comap (phiC D)) →* ↥(H z) :=
  (K D).subtype.comp (O3subA.comap (phiC D)).subtype

@[expose] noncomputable def O3H (D : QuotientData (z := z) hN) : Subgroup ↥(H z) :=
  ((O3Sylow D : Subgroup ↥(O3subA.comap (phiC D)))).map (toH D)

theorem O3H_le_K (D : QuotientData (z := z) hN) : O3H D ≤ K D := by
  intro x hx
  rw [O3H] at hx
  obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact u.1.2

theorem card_O3Sylow (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    Nat.card ↥(O3Sylow D : Subgroup ↥(O3subA.comap (phiC D))) = 27 := by
  have hfac : (Nat.card ↥(O3subA.comap (phiC D))).factorization 3 = 3 := by
    rw [card_comap_phiA h D]
    have h432 : 432 = 2 ^ 4 * 3 ^ 3 := by norm_num
    rw [h432, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2 ^ 4),
      Nat.factorization_pow_self Nat.prime_three, zero_add]
  rw [Sylow.card_eq_multiplicity, hfac]
  norm_num

theorem card_O3H (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    Nat.card (O3H D) = 27 := by
  rw [O3H,
    Subgroup.card_map_of_injective
      (K := (O3Sylow D : Subgroup ↥(O3subA.comap (phiC D))))
      (f := toH D)
      ((Subgroup.subtype_injective (K D)).comp
        (Subgroup.subtype_injective (O3subA.comap (phiC D))))]
  exact card_O3Sylow h D

theorem isPGroup_O3H (D : QuotientData (z := z) hN) : IsPGroup 3 (O3H D) := by
  rw [O3H]
  exact IsPGroup.map (O3Sylow D).isPGroup' (toH D)

theorem sigma1Nine_mem_O3H (D : QuotientData (z := z) hN) :
    sigma1Nine (z := z) D ∈ O3H D := by
  rw [O3H]
  refine Subgroup.mem_map.mpr ⟨s1Comap D, ?_, ?_⟩
  · exact le_O3Sylow (z := z) D (Subgroup.mem_zpowers (s1Comap D))
  · rfl

theorem ker_phi_le_comap (D : QuotientData (z := z) hN) :
    (phiC D).ker ≤ O3subA.comap (phiC D) := by
  intro x hx
  rw [Subgroup.mem_comap]
  have hx1 : phiC D x = 1 := MonoidHom.mem_ker.mp hx
  rw [hx1]
  exact O3subA.one_mem

theorem map_O3Sylow_phi (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    ((O3Sylow D : Subgroup ↥(O3subA.comap (phiC D)))).map
      ((phiC D).comp (O3subA.comap (phiC D)).subtype) = O3subA := by
  have hker_f : ((phiC D).comp (O3subA.comap (phiC D)).subtype).ker =
      (phiC D).ker.subgroupOf (O3subA.comap (phiC D)) := by
    change ((phiC D).domRestrict (O3subA.comap (phiC D))).ker =
      (phiC D).ker.subgroupOf (O3subA.comap (phiC D))
    exact MonoidHom.ker_domRestrict (K := O3subA.comap (phiC D)) (phiC D)
  have hcomapKer : Nat.card ((phiC D).ker.subgroupOf
      (O3subA.comap (phiC D))) = 16 := by
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (ker_phi_le_comap (z := z) D)).toEquiv,
      card_ker_phi h D]
  have hdisj : (O3Sylow D : Subgroup ↥(O3subA.comap (phiC D))) ⊓
      ((phiC D).comp (O3subA.comap (phiC D)).subtype).ker = ⊥ := by
    have hdvd1 : Nat.card ↥((O3Sylow D : Subgroup ↥(O3subA.comap (phiC D))) ⊓
        ((phiC D).comp (O3subA.comap (phiC D)).subtype).ker) ∣ 27 := by
      have := Subgroup.card_dvd_of_le (inf_le_left :
        (O3Sylow D : Subgroup ↥(O3subA.comap (phiC D))) ⊓
          ((phiC D).comp (O3subA.comap (phiC D)).subtype).ker ≤
          (O3Sylow D : Subgroup ↥(O3subA.comap (phiC D))))
      rwa [card_O3Sylow h D] at this
    have hdvd2 : Nat.card ↥((O3Sylow D : Subgroup ↥(O3subA.comap (phiC D))) ⊓
        ((phiC D).comp (O3subA.comap (phiC D)).subtype).ker) ∣ 16 := by
      have := Subgroup.card_dvd_of_le (inf_le_right :
        (O3Sylow D : Subgroup ↥(O3subA.comap (phiC D))) ⊓
          ((phiC D).comp (O3subA.comap (phiC D)).subtype).ker ≤
          ((phiC D).comp (O3subA.comap (phiC D)).subtype).ker)
      rw [hker_f, hcomapKer] at this
      exact this
    have hcard1 : Nat.card ↥((O3Sylow D : Subgroup ↥(O3subA.comap (phiC D))) ⊓
        ((phiC D).comp (O3subA.comap (phiC D)).subtype).ker) = 1 := by
      have h := Nat.dvd_gcd hdvd1 hdvd2
      rw [show Nat.gcd 27 16 = 1 by norm_num] at h
      exact Nat.dvd_one.mp h
    exact Subgroup.eq_bot_of_card_eq
      (H := (O3Sylow D : Subgroup ↥(O3subA.comap (phiC D))) ⊓
        ((phiC D).comp (O3subA.comap (phiC D)).subtype).ker) hcard1
  have hmap_card : Nat.card ↥(((O3Sylow D : Subgroup ↥(O3subA.comap (phiC D)))).map
      ((phiC D).comp (O3subA.comap (phiC D)).subtype)) = 27 := by
    rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot
      ((phiC D).comp (O3subA.comap (phiC D)).subtype) hdisj, card_O3Sylow h D]
  apply Subgroup.eq_of_le_of_card_ge
  · intro y hy
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_comap.mp u.2
  · rw [hmap_card, card_O3subA]

@[expose] noncomputable def eHom (D : QuotientData (z := z) hN) :
    ↥(O3H D) →* ↥O3sub where
  toFun x := ⟨qH D (x : H z), by
    have hx : (x : H z) ∈ ((O3Sylow D : Subgroup ↥(O3subA.comap (phiC D)))).map
        (toH D) := by
      rw [← O3H]
      exact x.2
    obtain ⟨u, -, hux⟩ := Subgroup.mem_map.mp hx
    rw [← hux]
    exact Subgroup.mem_comap.mp u.2⟩
  map_one' := by ext; simp
  map_mul' := by intro x y; ext; simp

@[simp] theorem eHom_val (D : QuotientData (z := z) hN) (x : ↥(O3H D)) :
    ((eHom D x : ↥O3sub) : Equiv.Perm (Fin 45)) = qH D (x : H z) := rfl

theorem eHom_surjective (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    Function.Surjective (eHom D) := by
  intro y
  have hyA : (⟨(y : Equiv.Perm (Fin 45)), O3sub_le_QA45 y.2⟩ :
      QA45.originalSubgroup) ∈ O3subA := y.2
  rw [← map_O3Sylow_phi h D] at hyA
  obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.mp hyA
  refine ⟨⟨toH D u, ?_⟩, ?_⟩
  · rw [O3H]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  · apply Subtype.ext
    rw [eHom_val]
    have hval : ((phiC D) u.1 : Equiv.Perm (Fin 45)) =
        (y : Equiv.Perm (Fin 45)) := congrArg Subtype.val huy
    change qH D (u.1 : H z) = (y : Equiv.Perm (Fin 45))
    simpa [phi_apply] using hval

theorem eHom_bijective (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    Function.Bijective (eHom D) :=
  (Nat.bijective_iff_surjective_and_card (eHom D)).mpr
    ⟨eHom_surjective h D, by rw [card_O3H h D, card_O3sub]⟩

@[expose] noncomputable def eO3H (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) : ↥(O3H D) ≃* ↥O3sub :=
  MulEquiv.ofBijective (eHom D) (eHom_bijective h D)

@[simp] theorem eO3H_apply (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) (x : ↥(O3H D)) :
    eO3H h D x = eHom D x := rfl

theorem eO3H_s1 (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    eO3H h D ⟨sigma1Nine (z := z) D, sigma1Nine_mem_O3H (z := z) D⟩ = s1sub := by
  rw [eO3H_apply]
  apply Subtype.ext
  rw [eHom_val, qH_sigma1Nine]
  rfl

theorem map_O3H (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    (O3H D).map (qH D) = O3subA := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (((qH D x : QA45.originalSubgroup) : Equiv.Perm (Fin 45)) ∈ O3sub)
    simpa [eHom_val] using (eHom D ⟨x, hx⟩).2
  · intro hy
    obtain ⟨x, hx⟩ := eHom_surjective h D (⟨y.1, hy⟩ : ↥O3sub)
    refine ⟨x.1, x.2, Subtype.ext ?_⟩
    have hval := congrArg (fun z : ↥O3sub => (z : Equiv.Perm (Fin 45))) hx
    simpa [eHom_val] using hval

theorem zpowers_sigma1Nine_le_center (D : QuotientData (z := z) hN) :
    Subgroup.zpowers (⟨sigma1Nine (z := z) D,
      sigma1Nine_mem_O3H (z := z) D⟩ : ↥(O3H D)) ≤ Subgroup.center (O3H D) := by
  rw [Subgroup.zpowers_le]
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hyK : (y : H z) ∈ K D := O3H_le_K (z := z) D y.2
  exact Subgroup.mem_centralizer_singleton_iff.mp hyK

theorem center_le_zpowers_sigma1Nine (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) :
    Subgroup.center (O3H D) ≤ Subgroup.zpowers (⟨sigma1Nine (z := z) D,
      sigma1Nine_mem_O3H (z := z) D⟩ : ↥(O3H D)) := by
  intro c hc
  have hc' : eO3H h D c ∈ Subgroup.center ↥O3sub := by
    rw [← Subgroup.map_center_eq (eO3H h D)]
    exact Subgroup.mem_map_of_mem (eO3H h D).toMonoidHom hc
  rw [center_O3sub] at hc'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc'
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  apply (eO3H h D).injective
  rw [map_zpow, eO3H_s1 h D, hk]

theorem center_O3H (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    Subgroup.center (O3H D) = Subgroup.zpowers (⟨sigma1Nine (z := z) D,
      sigma1Nine_mem_O3H (z := z) D⟩ : ↥(O3H D)) :=
  le_antisymm (center_le_zpowers_sigma1Nine h D)
    (zpowers_sigma1Nine_le_center D)

theorem isHeisenberg_O3H (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    (∀ x : ↥(O3H D), x ^ 3 = 1) ∧
      ∃ x y : ↥(O3H D), x * y ≠ y * x := by
  constructor
  · intro x
    apply (eO3H h D).injective
    rw [map_pow, map_one]
    have hx : ((eO3H h D x : ↥O3sub) : Equiv.Perm (Fin 45)) ∈ O3 () :=
      (eO3H h D x).2
    have h3 : ((eO3H h D x : ↥O3sub) : Equiv.Perm (Fin 45)) ^ 3 = 1 :=
      of_decide_eq_true
        (List.all_eq_true.1 Certificates.certificate946016.isHeisenberg_O3.1 _ hx)
    apply Subtype.ext
    simpa using h3
  · have hany := Certificates.certificate946016.isHeisenberg_O3.2
    obtain ⟨a, ha, hany2⟩ := List.any_eq_true.mp hany
    obtain ⟨b, hb, hne⟩ := List.any_eq_true.mp hany2
    have hne' : a * b ≠ b * a := of_decide_eq_true hne
    obtain ⟨x, hx⟩ := eHom_surjective h D (⟨a, ha⟩ : ↥O3sub)
    obtain ⟨y, hy⟩ := eHom_surjective h D (⟨b, hb⟩ : ↥O3sub)
    refine ⟨x, y, ?_⟩
    intro hxy
    have h := congrArg (eO3H h D) hxy
    rw [map_mul, map_mul] at h
    exact hne' (congrArg Subtype.val (by simpa [eO3H_apply, hx, hy] using h))

@[expose] noncomputable def conjV_O3H (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) : ↥(O3H D) →* MulAut (QuotientV.V z) :=
  (conjV h).comp (O3H D).subtype

@[simp] theorem conjV_O3H_apply (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) (x : ↥(O3H D)) :
    conjV_O3H h D x = conjV h (x : H z) := rfl

end CFSG.RankThree.GF2n.Parrott
