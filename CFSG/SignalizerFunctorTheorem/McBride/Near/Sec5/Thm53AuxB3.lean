module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxB1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxB2
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm52AuxQuot

public section

open CFSG.Open
open scoped commutatorElement Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53B

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem hfix_of_near
    (hp : p.Prime) {X : Subgroup G} (hnear : signalizerNearPSolvable p ↥X)
    {b : G} (hbp : b ^ p = 1) :
    ∀ J ∈ lcal X, b ∈ Subgroup.normalizer (J : Set G) → ¬ J ≤ Subgroup.centralizer {b} →
      Group.IsSolvable ↥(J ⊓ Subgroup.centralizer {b}) := by
  intro J hJ hbJ hnc
  obtain ⟨hJX, -, hs, hJnc⟩ := mem_lcal_iff.mp hJ
  have hnc' : ∃ x y : ↥J, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    exact hJnc (isMulCommutative_iff.mpr hcon)
  have hsec : IsSectionOf ↥J ↥X := isSectionOf_of_le hJX (IsSectionOf.refl ↥J)
  obtain ⟨hcopY, hmodel⟩ := signalizerNearPSolvable_iff.mp hnear
  have hcop : Nat.Coprime p (Nat.card J) :=
    hcopY.coprime_dvd_right (Subgroup.card_dvd_of_le hJX)
  exact Thm52Aux.isSolvable_inf_centralizer_of_model hp (hmodel ↥J hsec hnc') hcop hbJ hbp hnc

section Bot

variable (hb : BotData p A θ)

include hb

theorem fixData_of_cset
    {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) {b : G} (hbA : b ∈ A) :
    FixData p X (dsub A θ ⊔ A) b where
  prime := hb.nearFunctor.prime
  sol_eq := sol_eq_bot_of_mem_cset hb hX
  coprime := hX.1.1.2.1
  Q_le := sup_le (hX.1.2.trans Subgroup.le_normalizer) hX.1.1.1
  trans := fun _ hJ _ hJ' => exists_conj_eq_of_mem_lcal hb hX hJ hJ'
  b_mem := hX.1.1.1 hbA
  b_pow := hb.nearFunctor.elemAbelian.2 b hbA
  b_comm := by
    have hθ := hb.nearFunctor
    have hDb : dsub A θ ≤ Subgroup.centralizer {b} :=
      (dsub_le_centralizer hθ).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA))
    have hAb : A ≤ Subgroup.centralizer {b} := fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem hθ.elemAbelian.1 hg hbA)
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp ((sup_le hDb hAb) hg)
  hfix := hfix_of_near hb.nearFunctor.prime hX.1.1.2.2.2.1
    (hb.nearFunctor.elemAbelian.2 b hbA)

omit [Finite G] hb in
theorem admits_thetaM (Y X : Subgroup G) : Admits A (thetaM p A θ Y X) :=
  Admits.iSup fun _ => Admits.iSup fun hP => hP.1.1.1.1.1


theorem key_le {S : Subgroup G}
    (hSmax : ∀ Q ∈ mhat p A θ, Group.IsSolvable ↥Q → Q ≤ S) {X : Subgroup G}
    (hX : X ∈ cset p A θ ⊥) {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1) :
    kOf X ⊓ Subgroup.centralizer {b} ≤ (S ⊓ θ b) ⊔ thetaM p A θ ⊥ (θ b) := by
  have hθ := hb.nearFunctor
  have H := fixData_of_cset hb hX hbA
  have hXm : X ∈ mtil p A θ := hX.1
  have hθb : θ b ∈ mtil p A θ := apply_mem_mtil hθ hbA hb1
  have hDb : dsub A θ ≤ Subgroup.centralizer {b} :=
    (dsub_le_centralizer hθ).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA))
  have hAb : A ≤ Subgroup.centralizer {b} := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem hθ.elemAbelian.1 hg hbA)
  have hKadm : Admits (dsub A θ ⊔ A) (kOf X) :=
    sup_le (hXm.2.trans (Thm41Aux.le_normalizer_kOf X)) (Thm41Aux.admits_kOf hXm.1.1)
  have hUadm : Admits (dsub A θ ⊔ A) (kOf X ⊓ Subgroup.centralizer {b}) :=
    hKadm.inf (admits_centralizer_singleton (sup_le hDb hAb))
  have hUθ : kOf X ⊓ Subgroup.centralizer {b} ≤ θ b :=
    (inf_le_inf_right _ (kOf_le X)).trans (hXm.1.2.2.1 b hbA hb1)
  have hmin : ∀ N : Subgroup G, N ≤ kOf X → (N.subgroupOf (kOf X)).Normal →
      Admits (dsub A θ ⊔ A) N → N = ⊥ ∨ N = kOf X := by
    intro N hNK hNn hNQ
    have hch := isChiefFactorOf_kOf hb hX
    have hKN : kOf X ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hNn
    exact hch.2.2.2 N ⟨hNK.trans (le_sup_left.trans le_sup_left),
      sup_le (sup_le hKN (le_sup_left.trans hNQ)) (le_sup_right.trans hNQ)⟩ bot_le hNK
  rcases H.dichotomy hmin with hsolv | ⟨hns, hminU, hcent⟩
  · have hUm : kOf X ⊓ Subgroup.centralizer {b} ∈ mhat p A θ :=
      mem_mhat_of_le_mtil hθ.prime hθb hUθ hUadm
    exact le_sup_of_le_left (le_inf (hSmax _ hUm hsolv) hUθ)
  · set U : Subgroup G := kOf X ⊓ Subgroup.centralizer {b} with hU
    have hUbot : U ≠ ⊥ := fun h0 => hns (by rw [h0]; infer_instance)
    have hDU : dsub A θ ≤ Subgroup.normalizer (U : Set G) := le_sup_left.trans hUadm
    have hAU : A ≤ Subgroup.normalizer (U : Set G) := le_sup_right.trans hUadm
    have hHN : U ⊔ dsub A θ ⊔ A ≤ Subgroup.normalizer (U : Set G) :=
      sup_le (sup_le Subgroup.le_normalizer hDU) hAU
    have hbotN : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    have hch : IsChiefFactorOf (U ⊔ dsub A θ ⊔ A) U ⊥ := by
      refine ⟨⟨bot_le, by rw [hbotN]; exact le_top⟩, ⟨le_sup_left.trans le_sup_left, hHN⟩,
        bot_lt_iff_ne_bot.mpr hUbot, fun K' hK' _ hK'U => ?_⟩
      have hUK' : U ≤ Subgroup.normalizer (K' : Set G) :=
        (le_sup_left.trans le_sup_left).trans hK'.2
      have hnorm : (K'.subgroupOf U).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hK'U).mpr hUK'
      exact hminU K' hK'U hnorm
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right |>.trans hK'.2)
    have hsec : ¬ IsSolvableSection U ⊥ := fun hsec =>
      hns (Thm53A.isSolvable_of_isSolvableSection bot_le (by rw [hbotN]; exact le_top) hsec
        inferInstance)
    have hP := Thm53A.pair_of_chief hθ hθb hUθ hch hsec
    set C : Subgroup G := secCenIn (U ⊔ dsub A θ) U ⊥ with hC
    have hCUD : C ≤ U ⊔ dsub A θ := inf_le_left
    have hDC : C ⊓ dsub A θ = ⊥ := by
      rw [eq_bot_iff]
      rintro d ⟨hdC, hdD⟩
      have hdsc : d ∈ sectionCentralizer ⊥ U := (Subgroup.mem_inf.mp hdC).2
      have hdU : ∀ y ∈ U, d * y = y * d := by
        intro y hy
        have h1 := (mem_sectionCentralizer_iff.mp hdsc).2.2 y hy
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
      have hdQ : d ∈ dsub A θ ⊔ A := Subgroup.mem_sup_left hdD
      have hordd : Nat.Coprime p (orderOf d) :=
        (hθ.isFunctor.coprime b hbA hb1).coprime_dvd_right
          (Subgroup.orderOf_dvd_natCard _ (dsub_le_apply hbA hb1 hdD))
      have hcd := hcent d hdQ hordd hdU
      have hdmem : d ∈ dsub A θ ⊓ Subgroup.centralizer (kOf X : Set G) :=
        ⟨hdD, Subgroup.mem_centralizer_iff.mpr fun x hx => (hcd x hx).symm⟩
      rw [dsub_inf_centralizer_kOf hb hX] at hdmem
      exact hdmem
    have hCθ : U ⊔ C ≤ θ b := sup_le hUθ (hCUD.trans (sup_le hUθ (dsub_le_apply hbA hb1)))
    have hPYX : (U ⊔ C, C) ∈ pairsYX p A θ ⊥ (θ b) := ⟨⟨hP, hDC⟩, hCθ⟩
    have hle : U ⊔ C ≤ thetaM p A θ ⊥ (θ b) :=
      le_iSup₂_of_le (f := fun P (_ : P ∈ pairsYX p A θ ⊥ (θ b)) => P.1) (U ⊔ C, C) hPYX le_rfl
    exact le_sup_of_le_right (le_sup_left.trans hle)


@[expose] def theta1 (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (S : Subgroup G) :
    G → Subgroup G :=
  fun a => (S ⊓ θ a) ⊔ thetaM p A θ ⊥ (θ a)

omit [Finite G] hb in
theorem thetaM_le (Y X : Subgroup G) : thetaM p A θ Y X ≤ X :=
  iSup₂_le fun _ hP => hP.2

omit [Finite G] hb in
theorem theta1_le (S : Subgroup G) (a : G) : theta1 p A θ S a ≤ θ a :=
  sup_le inf_le_right (thetaM_le _ _)

omit [Finite G] hb in
theorem thetaM_eq_bot_of_not_mem {X : Subgroup G} (hXm : X ∈ mtil p A θ)
    (hX : X ∉ cset p A θ ⊥) : thetaM p A θ ⊥ X = ⊥ :=
  iSup₂_eq_bot.mpr fun P hP => (hX ⟨hXm, P, hP⟩).elim

omit [Finite G] in
theorem admits_theta1 {S : Subgroup G} (hS : S ∈ mhat p A θ) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) : Admits A (theta1 p A θ S a) :=
  Admits.sup (Admits.inf hS.1.1 (hb.nearFunctor.isFunctor.normalized a ha ha1))
    (admits_thetaM _ _)

theorem theta1_balance
    {S : Subgroup G} (hS : S ∈ mhat p A θ)
    (hSmax : ∀ Q ∈ mhat p A θ, Group.IsSolvable ↥Q → Q ≤ S) {a b : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) (hbA : b ∈ A) (hb1 : b ≠ 1) :
    theta1 p A θ S a ⊓ Subgroup.centralizer {b} ≤ theta1 p A θ S b := by
  have hθ := hb.nearFunctor
  intro x hx
  obtain ⟨hxθ, hxC⟩ := Subgroup.mem_inf.mp hx
  have hSθ : ∀ s ∈ S ⊓ θ a, s ∈ Subgroup.centralizer {b} → s ∈ theta1 p A θ S b := by
    intro s hs hsC
    refine Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hs.1, ?_⟩)
    exact hθ.isFunctor.balance a ha ha1 b hbA hb1 ⟨hs.2, hsC⟩
  by_cases hX : θ a ∈ cset p A θ ⊥
  · have hKeq : thetaM p A θ ⊥ (θ a) = kOf (θ a) := thetaM_bot_eq_kOf hb hX
    have hset : ((theta1 p A θ S a : Subgroup G) : Set G) =
        ((S ⊓ θ a : Subgroup G) : Set G) * (thetaM p A θ ⊥ (θ a) : Set G) := by
      refine Subgroup.coe_mul_of_left_le_normalizer_right _ _ ?_
      rw [hKeq]
      exact inf_le_right.trans (Thm41Aux.le_normalizer_kOf (θ a))
    have hxmul : x ∈ ((S ⊓ θ a : Subgroup G) : Set G) * (thetaM p A θ ⊥ (θ a) : Set G) := by
      rw [← hset]
      exact hxθ
    have hbp : b ^ p = 1 := hθ.elemAbelian.2 b hbA
    have hzb : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.mpr hbA
    have hxz : x ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
      rw [Thm52Aux.centralizer_zpowers_eq]
      exact hxC
    obtain ⟨s, hs, k, hk, rfl⟩ := exists_mul_of_mem_centralizer hθ.prime
      (Thm52Aux.isPGroup_zpowers hbp)
      (hS.1.2.1.coprime_dvd_right (Subgroup.card_dvd_of_le (inf_le_left : S ⊓ θ a ≤ S)))
      (hzb.trans (Admits.inf hS.1.1 (hθ.isFunctor.normalized a ha ha1)))
      (hzb.trans (admits_thetaM ⊥ (θ a))) hxmul hxz
    rw [Thm52Aux.centralizer_zpowers_eq] at hs hk
    have hsmem : s ∈ theta1 p A θ S b := hSθ s hs.1 hs.2
    have hkmem : k ∈ theta1 p A θ S b := by
      have hk' : k ∈ kOf (θ a) ⊓ Subgroup.centralizer {b} := by
        rw [← hKeq]
        exact hk
      exact key_le hb hSmax hX hbA hb1 hk'
    exact mul_mem hsmem hkmem
  · have hθam : θ a ∈ mtil p A θ := apply_mem_mtil hθ ha ha1
    have hKbot := thetaM_eq_bot_of_not_mem hθam hX
    have hxS : x ∈ S ⊓ θ a := by
      have : x ∈ (S ⊓ θ a) ⊔ ⊥ := by
        simpa [theta1, hKbot] using hxθ
      simpa using this
    exact hSθ x hxS hxC


theorem theta1_isFunctor
    {S : Subgroup G} (hS : S ∈ mhat p A θ)
    (hSmax : ∀ Q ∈ mhat p A θ, Group.IsSolvable ↥Q → Q ≤ S) :
    IsFunctor p A (theta1 p A θ S) where
  le_centralizer a ha ha1 :=
    (theta1_le S a).trans (hb.nearFunctor.isFunctor.le_centralizer a ha ha1)
  coprime a ha ha1 := (hb.nearFunctor.isFunctor.coprime a ha ha1).coprime_dvd_right
    (Subgroup.card_dvd_of_le (theta1_le S a))
  normalized _ ha ha1 := admits_theta1 hb hS ha ha1
  balance _ ha ha1 _ hbA hb1 := theta1_balance hb hS hSmax ha ha1 hbA hb1

theorem theta1_nearHyp
    (hhyp : NearHyp p A θ) {S : Subgroup G} (hS : S ∈ mhat p A θ)
    (hSmax : ∀ Q ∈ mhat p A θ, Group.IsSolvable ↥Q → Q ≤ S) :
    NearHyp p A (theta1 p A θ S) where
  prime := hhyp.prime
  odd := hhyp.odd
  elemAbelian := hhyp.elemAbelian
  card := hhyp.card
  isFunctor := theta1_isFunctor hb hS hSmax
  near := fun a ha ha1 => nearASolvable_of_le hhyp.prime (hhyp.near a ha ha1) (theta1_le S a)
    (admits_theta1 hb hS ha ha1)

theorem not_isCompleteIn_theta1
    {S : Subgroup G}
    (hSmax : ∀ Q ∈ mhat p A θ, Group.IsSolvable ↥Q → Q ≤ S)
    (hMG : thetaMG p A θ ⊥ ∉ assoc p A θ) :
    ¬ IsCompleteIn (signalizers p A (theta1 p A θ S) (NearASolvable p A)) := by
  have hθ := hb.nearFunctor
  rintro ⟨T, hT, hTmax⟩
  apply hMG
  have hle : thetaMG p A θ ⊥ ≤ T := by
    refine iSup₂_le fun X hX => ?_
    apply hTmax
    rw [thetaM_bot_eq_kOf hb hX]
    refine ⟨Thm41Aux.admits_kOf hX.1.1.1, hX.1.1.2.1.coprime_dvd_right
      (Subgroup.card_dvd_of_le (kOf_le X)), fun a ha ha1 => key_le hb hSmax hX ha ha1,
      nearASolvable_of_le hθ.prime hX.1.1.2.2.2 (kOf_le X) (Thm41Aux.admits_kOf hX.1.1.1)⟩
  have hTassoc : T ∈ assoc p A θ :=
    signalizers_mono_functor (fun a _ _ => theta1_le _ a) hT
  have hadm : Admits A (thetaMG p A θ ⊥) :=
    Admits.iSup fun X => Admits.iSup fun _ => admits_thetaM ⊥ X
  exact mem_assoc_of_le hθ.prime hTassoc hle hadm

theorem theta1_eq
    (h : Counterexample p A θ) {S : Subgroup G} (hS : S ∈ mhat p A θ)
    (hSmax : ∀ Q ∈ mhat p A θ, Group.IsSolvable ↥Q → Q ≤ S)
    (hMG : thetaMG p A θ ⊥ ∉ assoc p A θ) :
    ∀ a ∈ A, a ≠ 1 → theta1 p A θ S a = θ a := by
  by_contra hcon
  push Not at hcon
  have hnc := not_isCompleteIn_theta1 hb hSmax hMG
  have hlt : size A (theta1 p A θ S) < size A θ :=
    size_lt_size (fun a _ _ => theta1_le S a) hcon
  exact absurd (h.minimal _ (theta1_nearHyp hb h.hyp hS hSmax) hnc) (not_le.mpr hlt)

end Bot

end Thm53B

end CFSG.SignalizerFunctorTheorem.McBride.Near
