module

public import CFSG.RankThree.PartOne.S12.Sec15Lemmas
import CFSG.RankThree.PartOne.S12.Sec15FA
import CFSG.RankThree.PartOne.S12.Sec12FusSyl
import CFSG.RankThree.PartOne.S12.Sec12FusChoice
public import CFSG.RankThree.PartOne.S12.Sec15Items

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

structure U5Config {G : Type} [Group G] (p : ℕ) (A E T B : Subgroup G) : Prop where
  sylow : IsSylowOf 2 T (lieNormalizer p E)
  A_le_Y : A ≤ (lieGenerated p E ⊔ E) ⊓ Subgroup.centralizer (omegaOneCenterIn T : Set G)
  B_le_E : B ≤ E
  B_le_X : B ≤ (lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G)
  B_elem : IsElementaryAbelian p B
  B_card : Nat.card B = p ^ 2

@[expose] def KF1515U5Faithful : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E T B : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    U5Config p A E T B →
    ∃ b ∈ B, b ≠ 1 ∧
      b ∈ Subgroup.centralizer (((Subgroup.center ↥(pushingUpS T)).map (pushingUpS T).subtype :
        Subgroup G) : Set G) ∧
      ∀ R : Subgroup G, R ≤ pushingUpS T →
        (lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) ≤
          Subgroup.normalizer (R : Set G) →
        R ≠ pushingUpS T → b ∈ Subgroup.centralizer (R : Set G)

@[expose] def KF1515U5Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E T B : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    U5Config p A E T B →
    ∀ M ∈ CFSG.maximalTwoLocalsContaining
      (((lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) : Subgroup G) :
        Set G),
      inSubgroup (CFSG.pCore 2) M ≤ pushingUpS T

@[expose] def KF1515U5Syl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E T B : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    U5Config p A E T B →
    ∀ P : Subgroup G, IsSylowOf p P (lieNormalizer p E ⊓ Subgroup.centralizer
      (((Subgroup.center ↥(pushingUpS T)).map (pushingUpS T).subtype : Subgroup G) : Set G)) →
      IsCyclic ↥P


namespace Sec1515U5

open Sec15FA (exists_conj_of_isSylowOf le_of_isSylowOf_of_isPGroup)

variable {G : Type} [Group G]

theorem mem_zpowers_of_cyclic [Finite G] {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    (hP : IsCyclic ↥P) {x y : G} (hx : x ∈ P) (hy : y ∈ P) (hxo : orderOf x = p)
    (hyo : orderOf y = p) : y ∈ Subgroup.zpowers x := by
  classical
  have : Fintype ↥P := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥P) hp.pos
  have hxo' : orderOf (⟨x, hx⟩ : ↥P) = p := by
    rw [← hxo, ← Subgroup.orderOf_coe]
  have hyp : (⟨y, hy⟩ : ↥P) ^ p = 1 := by
    apply Subtype.ext
    have h1 := pow_orderOf_eq_one y
    rw [hyo] at h1
    simpa using h1
  have hsub : (Subgroup.zpowers (⟨x, hx⟩ : ↥P) : Set ↥P).toFinset ⊆
      Finset.univ.filter (fun a : ↥P => a ^ p = 1) := by
    intro a ha
    rw [Set.mem_toFinset, SetLike.mem_coe] at ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo', pow_orderOf_eq_one,
      one_zpow]
  have hcard : (Subgroup.zpowers (⟨x, hx⟩ : ↥P) : Set ↥P).toFinset.card = p := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    show Nat.card (Subgroup.zpowers (⟨x, hx⟩ : ↥P)) = p
    rw [Nat.card_zpowers]
    exact hxo'
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
  have hymem : (⟨y, hy⟩ : ↥P) ∈ (Subgroup.zpowers (⟨x, hx⟩ : ↥P) : Set ↥P).toFinset := by
    rw [heq]
    simp [hyp]
  rw [Set.mem_toFinset, SetLike.mem_coe] at hymem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hymem
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩


theorem orderOf_conj' (g b : G) : orderOf (g⁻¹ * b * g) = orderOf b := by
  have h : g⁻¹ * b * g = (MulAut.conj g⁻¹) b := by
    simp
  rw [h, MulEquiv.orderOf_eq]

theorem exists_conj_of_cyclic_sylow [Finite G] {p : ℕ} (hp : p.Prime) {C P : Subgroup G}
    (hPC : IsSylowOf p P C) (hcyc : IsCyclic ↥P) {b b' : G} (hb : b ∈ C) (hb' : b' ∈ C)
    (hbo : orderOf b = p) (hb'o : orderOf b' = p) :
    ∃ c ∈ C, c * b * c⁻¹ ∈ Subgroup.zpowers b' := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hbp : IsPGroup p (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  have hb'p : IsPGroup p (Subgroup.zpowers b') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb'o, pow_one])
  obtain ⟨P₁, hP₁, hbP₁⟩ :=
    Sec12Fus.exists_isSylowOf_ge (p := p) (K := C) (Subgroup.zpowers_le.2 hb) hbp
  obtain ⟨P₂, hP₂, hb'P₂⟩ :=
    Sec12Fus.exists_isSylowOf_ge (p := p) (K := C) (Subgroup.zpowers_le.2 hb') hb'p
  obtain ⟨g₁, hg₁C, hg₁⟩ := exists_conj_of_isSylowOf hp hPC hP₁
  obtain ⟨g₂, hg₂C, hg₂⟩ := exists_conj_of_isSylowOf hp hPC hP₂
  have hu : g₁⁻¹ * b * g₁ ∈ P := (hg₁ b).1 (hbP₁ (Subgroup.mem_zpowers b))
  have hv : g₂⁻¹ * b' * g₂ ∈ P := (hg₂ b').1 (hb'P₂ (Subgroup.mem_zpowers b'))
  have hu_mem : g₁⁻¹ * b * g₁ ∈ Subgroup.zpowers (g₂⁻¹ * b' * g₂) :=
    mem_zpowers_of_cyclic hp hcyc hv hu (by rw [orderOf_conj', hb'o]) (by rw [orderOf_conj', hbo])
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hu_mem
  refine ⟨g₂ * g₁⁻¹, C.mul_mem hg₂C (C.inv_mem hg₁C), ?_⟩
  refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
  have h1 : (g₂⁻¹ * b' * g₂) ^ j = g₂⁻¹ * b' ^ j * g₂ := by
    rw [show g₂⁻¹ * b' * g₂ = g₂⁻¹ * b' * g₂⁻¹⁻¹ by simp, conj_zpow]
    simp
  rw [h1] at hj
  have h2 : b = g₁ * (g₂⁻¹ * b' ^ j * g₂) * g₁⁻¹ := by
    rw [hj]
    group
  calc b' ^ j = (g₂ * g₁⁻¹) * (g₁ * (g₂⁻¹ * b' ^ j * g₂) * g₁⁻¹) * (g₂ * g₁⁻¹)⁻¹ := by group
    _ = (g₂ * g₁⁻¹) * b * (g₂ * g₁⁻¹)⁻¹ := by rw [← h2]


theorem le_of_cyclic_sylow [Finite G] {p : ℕ} (hp : p.Prime) {N V M : Subgroup G} {b : G}
    (hbo : orderOf b = p) (hbN : b ∈ N) (hbV : b ∈ Subgroup.centralizer (V : Set G))
    (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hCN : Subgroup.centralizer (V : Set G) ≤ N)
    (hNb : Subgroup.normalizer (Subgroup.zpowers b : Set G) ≤ N)
    (hsyl : ∀ P : Subgroup G, IsSylowOf p P (N ⊓ Subgroup.centralizer (V : Set G)) →
      IsCyclic ↥P) : M ≤ N := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hbp : IsPGroup p (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  have hzNC : Subgroup.zpowers b ≤ N ⊓ Subgroup.centralizer (V : Set G) :=
    Subgroup.zpowers_le.2 ⟨hbN, hbV⟩
  obtain ⟨PV, hPV, hbPV⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hzNC hbp
  have hcyc : IsCyclic ↥PV := hsyl PV hPV
  have hbPVmem : b ∈ PV := hbPV (Subgroup.mem_zpowers b)
  have hPVC : IsSylowOf p PV (Subgroup.centralizer (V : Set G)) := by
    have hPVle : PV ≤ Subgroup.centralizer (V : Set G) := hPV.1.trans inf_le_right
    obtain ⟨P', hP', hPVP'⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hPVle hPV.2.1
    have hQ : ∀ q ∈ P' ⊓ Subgroup.normalizer (PV : Set G),
        q ∈ N ⊓ Subgroup.centralizer (V : Set G) := by
      intro q hq
      have hqC : q ∈ Subgroup.centralizer (V : Set G) := hP'.1 hq.1
      have hqb : q * b * q⁻¹ ∈ PV := (Subgroup.mem_normalizer_iff.1 hq.2 b).1 hbPVmem
      have hqo : orderOf (q * b * q⁻¹) = p := by
        have h : q * b * q⁻¹ = (MulAut.conj q) b := by simp
        rw [h, MulEquiv.orderOf_eq, hbo]
      have hqz : q * b * q⁻¹ ∈ Subgroup.zpowers b :=
        mem_zpowers_of_cyclic hp hcyc hbPVmem hqb hbo hqo
      exact ⟨hNb (Sec12Fus.mem_normalizer_zpowers_of_conj hqz), hqC⟩
    have hQp : IsPGroup p ↥(P' ⊓ Subgroup.normalizer (PV : Set G)) :=
      hP'.2.1.to_le inf_le_left
    have hQle : (P' ⊓ Subgroup.normalizer (PV : Set G)) ≤ PV :=
      le_of_isSylowOf_of_isPGroup hPV hQp (le_inf hPVP' Subgroup.le_normalizer) (fun q hq => hQ q hq)
    have hP'eq : PV = P' := by
      by_contra hne
      obtain ⟨y, hyP', hyPV, hyN⟩ :=
        Sec12Fus.exists_mem_normalizer_sdiff hPVP' hP'.2.1 hne
      exact hyPV (hQle ⟨hyP', hyN⟩)
    rw [hP'eq]
    exact hP'
  intro m hm
  have hm' : m⁻¹ ∈ M := M.inv_mem hm
  have hb'C : m * b * m⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : m⁻¹ * v * m ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (hMV hm') v).1 hv
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.1 hbV _ h1
    calc v * (m * b * m⁻¹) = m * ((m⁻¹ * v * m) * b) * m⁻¹ := by group
      _ = m * (b * (m⁻¹ * v * m)) * m⁻¹ := by rw [h2]
      _ = (m * b * m⁻¹) * v := by group
  have hb'o : orderOf (m * b * m⁻¹) = p := by
    have h : m * b * m⁻¹ = (MulAut.conj m) b := by simp
    rw [h, MulEquiv.orderOf_eq, hbo]
  obtain ⟨c, hcC, hc⟩ := exists_conj_of_cyclic_sylow hp hPVC hcyc hbV hb'C hbo hb'o
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hmc : m⁻¹ * c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    apply Sec12Fus.mem_normalizer_zpowers_of_conj
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have h1 : (m * b * m⁻¹) ^ k = m * b ^ k * m⁻¹ := conj_zpow
    have h2 : m * b ^ k * m⁻¹ = c * b * c⁻¹ := by rw [← h1]; exact hk
    calc b ^ k = m⁻¹ * (m * b ^ k * m⁻¹) * m := by group
      _ = m⁻¹ * (c * b * c⁻¹) * m := by rw [h2]
      _ = (m⁻¹ * c) * b * (m⁻¹ * c)⁻¹ := by group
  have hcN : c ∈ N := hCN hcC
  have hmcN : m⁻¹ * c ∈ N := hNb hmc
  have : m = c * (m⁻¹ * c)⁻¹ := by group
  rw [this]
  exact N.mul_mem hcN (N.inv_mem hmcN)


theorem omegaOneCenterIn_le_center (T : Subgroup G) :
    omegaOneCenterIn T ≤ (Subgroup.center ↥(pushingUpS T)).map (pushingUpS T).subtype := by
  unfold omegaOneCenterIn omegaOne
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨⟨z, hz, rfl⟩, -⟩
  have hzS : (z : G) ∈ pushingUpS T := by
    refine ⟨z.2, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
    have hwT : w ∈ T := Subgroup.map_subtype_le _ hw
    exact congrArg (fun y : ↥T => (y : G)) (Subgroup.mem_center_iff.1 hz ⟨w, hwT⟩)
  refine ⟨⟨(z : G), hzS⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro s
  apply Subtype.ext
  exact congrArg (fun y : ↥T => (y : G)) (Subgroup.mem_center_iff.1 hz ⟨s, s.2.1⟩)

theorem omegaOneCenterIn_ne_bot [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    omegaOneCenterIn T ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hT1
  have hZ : Nontrivial ↥(Subgroup.center ↥T) := hT.center_nontrivial
  have hZp : IsPGroup 2 ↥(Subgroup.center ↥T) := hT.to_subgroup _
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : Nat.card ↥(Subgroup.center ↥T) = 1 := by simpa using hk
    exact (Finite.one_lt_card_iff_nontrivial.2 hZ).ne' (by simpa [Nat.card_eq_fintype_card] using this)
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥T) := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hz2 : (z : ↥T) ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have hz1 : (z : ↥T) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    omega
  intro hbot
  have hmem : (((z : ↥T) : G)) ∈ omegaOneCenterIn T :=
    Subgroup.subset_closure ⟨⟨z, z.2, rfl⟩, by simpa using congrArg Subtype.val hz2⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1 (Subtype.ext hmem)

end Sec1515U5

open Sec1515U5 in
theorem node1515U5_of_kfacts (h1510 : Node1510) (h1511 : Node1511) (hFa : KF1515U5Faithful)
    (hCo : KF1515U5Core) (hSy : KF1515U5Syl) : Node1515U5 := by
  classical
  intro G _ _ p A c L E h15 hF12 hout T hT hAY hB M hM
  obtain ⟨B, hBE, hBX, hBel, hBcard⟩ := hB
  have hcfg : U5Config p A E T B := ⟨hT, hAY, hBE, hBX, hBel, hBcard⟩
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  have hout' : Outcome152 p E A (lieGenerated p E) :=
    Or.inr (Or.inr (Or.inr (Or.inr hout)))
  obtain ⟨b, hbB, hb1, hbV, hfaith⟩ := hFa G p A c L E T B h15 hF12 hout hcfg
  have hcore := hCo G p A c L E T B h15 hF12 hout hcfg M hM
  have hsyl := hSy G p A c L E T B h15 hF12 hout hcfg
  have hAel : IsElementaryAbelian p B := hBel
  have hbo : orderOf b = p :=
    orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := B) b hbB) hb1
  have hbE : b ∈ E := hBE hbB
  have hbX : b ∈ (lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) := hBX hbB
  have hbM : b ∈ M := hM.2 hbX
  have hT1 : T ≠ ⊥ := by
    intro hTbot
    obtain ⟨f, -, -, -, -, -, -, hev⟩ := hout
    have h2N : 2 ∣ Nat.card (lieNormalizer p E) :=
      (even_iff_two_dvd.1 hev).trans (Subgroup.card_dvd_of_le Subgroup.le_normalizer)
    have h1 := (T.subgroupOf (lieNormalizer p E)).index_mul_card
    have hcardT : Nat.card (T.subgroupOf (lieNormalizer p E)) = 1 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv, hTbot, Subgroup.card_bot]
    rw [hcardT, mul_one] at h1
    exact hT.2.2 (by
      show 2 ∣ (T.subgroupOf (lieNormalizer p E)).index
      rw [h1]
      exact h2N)
  have hU1 : omegaOneCenterIn T ≠ ⊥ := omegaOneCenterIn_ne_bot hT.2.1 hT1
  have hUT : omegaOneCenterIn T ≤ T := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨⟨z, -, rfl⟩, -⟩
    exact z.2
  have hU2 : IsPGroup 2 (omegaOneCenterIn T) := hT.2.1.to_le hUT
  have hNU : Subgroup.normalizer (omegaOneCenterIn T : Set G) ≤ lieNormalizer p E := by
    refine Sec15Final.normalizer_le_of_forall_maximal
      (X := (lieGenerated p E ⊔ E) ⊓ Subgroup.centralizer (omegaOneCenterIn T : Set G)) hU1 hU2 ?_ ?_
    · intro y hy
      exact Subgroup.centralizer_le_normalizer _ hy.2
    · intro M' hM'
      exact h1511 G p A c L E h15 hF12 hout' A le_rfl (Or.inr ⟨hout, rfl⟩) M'
        ⟨hM'.1, fun a ha => hM'.2 (hAY ha)⟩
  have hCN : Subgroup.centralizer (((Subgroup.center ↥(pushingUpS T)).map
      (pushingUpS T).subtype : Subgroup G) : Set G) ≤ lieNormalizer p E := fun x hx =>
    hNU (Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (omegaOneCenterIn_le_center T) hx))
  have hMR : M ≤ Subgroup.normalizer ((inSubgroup (CFSG.pCore 2) M : Subgroup G) : Set G) :=
    Subgroup.le_normalizer.trans
      (Sec15Final.normalizer_le_normalizer_map_subtype_of_characteristic inferInstance)
  have hSR : inSubgroup (CFSG.pCore 2) M = pushingUpS T := by
    by_contra hne
    have hXR : (lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) ≤
        Subgroup.normalizer ((inSubgroup (CFSG.pCore 2) M : Subgroup G) : Set G) :=
      fun x hx => hMR (hM.2 hx)
    have hbC := hfaith _ hcore hXR hne
    have hMloc : IsPLocal 2 M := hM.1.1
    have hchar : IsCharacteristicPType G 2 := h.setup.2.2.2.1
    have hcent : (⟨b, hbM⟩ : ↥M) ∈ Subgroup.centralizer ((CFSG.pCore 2 ↥M : Subgroup ↥M) : Set ↥M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzR : (z : G) ∈ inSubgroup (CFSG.pCore 2) M := ⟨z, hz, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hbC (z : G) hzR)
    have hbcore : (⟨b, hbM⟩ : ↥M) ∈ CFSG.pCore 2 ↥M := hchar M hMloc hcent
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨_, hbcore⟩
    have hbk : b ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val (congrArg Subtype.val hk)
    have hdvd : p ∣ 2 ^ k := hbo ▸ orderOf_dvd_of_pow_eq_one hbk
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  have hMS : M ≤ Subgroup.normalizer (pushingUpS T : Set G) := hSR ▸ hMR
  have hMV : M ≤ Subgroup.normalizer (((Subgroup.center ↥(pushingUpS T)).map
      (pushingUpS T).subtype : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · exact fun hv => Sec12Fus.conj_mem_center_map (hMS hm) hv
    · intro hv
      have := Sec12Fus.conj_mem_center_map (P := pushingUpS T)
        ((Subgroup.normalizer (pushingUpS T : Set G)).inv_mem (hMS hm)) hv
      simpa [mul_assoc] using this
  have hNb : Subgroup.normalizer (Subgroup.zpowers b : Set G) ≤ lieNormalizer p E :=
    h1510 G p A c L E h15 hF12 hout' (Subgroup.zpowers b) (Subgroup.zpowers_le.2 hbE)
      (fun h0 => hb1 (Subgroup.zpowers_eq_bot.1 h0))
  have hbN : b ∈ lieNormalizer p E :=
    torusNormalizer_le_lieNormalizer hp E (Subgroup.le_normalizer hbE)
  exact le_of_cyclic_sylow hp hbo hbN hbV hMV hCN hNb hsyl

end CFSG.RankThree.PartOne
