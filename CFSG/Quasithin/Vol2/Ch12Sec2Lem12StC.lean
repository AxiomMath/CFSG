module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12StA
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

namespace Lem12St

open G6 in
@[expose] def pairing {n : ℕ} (m x : PermMod n) : ZMod 2 :=
  ∑ i, Multiplicative.toAdd m i * Multiplicative.toAdd x i

open G6 in
theorem pairing_mul {n : ℕ} (m x y : PermMod n) :
    pairing m (x * y) = pairing m x + pairing m y := by
  simp only [pairing, toAdd_mul, Pi.add_apply, mul_add, Finset.sum_add_distrib]

open G6 in
theorem pairing_comm {n : ℕ} (m x : PermMod n) : pairing m x = pairing x m := by
  simp only [pairing, mul_comm]

open G6 in
theorem pairing_one {n : ℕ} (m : PermMod n) : pairing m 1 = 0 := by
  simp [pairing]

open G6 in
theorem pairing_mul_left {n : ℕ} (m a x : PermMod n) :
    pairing (m * a) x = pairing m x + pairing a x := by
  simp only [pairing, toAdd_mul, Pi.add_apply, add_mul, Finset.sum_add_distrib]

open G6 in
theorem pairing_allOnes_zpow {n : ℕ} (k : ℤ) (x : PermMod n) :
    pairing (allOnes n ^ k) x = (k : ZMod 2) * ∑ i, Multiplicative.toAdd x i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp [allOnes, toAdd_zpow]

open G6 in
theorem pairing_permAct {n : ℕ} (σ : Equiv.Perm (Fin n)) (m x : PermMod n) :
    pairing m (permAct n σ x) = pairing (permAct n σ⁻¹ m) x := by
  unfold pairing
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [permAct_apply, inv_inv]
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]

open G6 in
theorem permAct_allOnes {n : ℕ} (σ : Equiv.Perm (Fin n)) : permAct n σ (allOnes n) = allOnes n :=
  rfl

open G6 in
theorem pairing_permAct_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (m x : PermMod n)
    (hσ : m⁻¹ * permAct n σ⁻¹ m ∈ Subgroup.zpowers (allOnes n)) (hx : x ∈ coreMod n) :
    pairing m (permAct n σ x) = pairing m x := by
  rw [pairing_permAct]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hσ
  have hm : permAct n σ⁻¹ m = m * allOnes n ^ k := by
    rw [hk]
    exact (mul_inv_cancel_left m _).symm
  have hx' : ∑ i, Multiplicative.toAdd x i = 0 := hx
  rw [hm, pairing_mul_left, pairing_allOnes_zpow, hx', mul_zero, add_zero]

open G6 in
theorem rel_inv {n : ℕ} {σ : Equiv.Perm (Fin n)} {m : PermMod n}
    (h : m⁻¹ * permAct n σ m ∈ Subgroup.zpowers (allOnes n)) :
    m⁻¹ * permAct n σ⁻¹ m ∈ Subgroup.zpowers (allOnes n) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have h1 : permAct n σ m = m * allOnes n ^ k := by
    rw [hk]
    exact (mul_inv_cancel_left m _).symm
  have h2 : m = permAct n σ⁻¹ m * allOnes n ^ k := by
    have := congrArg (permAct n σ⁻¹) h1
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply, map_mul,
      map_zpow, permAct_allOnes] at this
    exact this
  have hp : permAct n σ⁻¹ m = m * (allOnes n ^ k)⁻¹ := eq_mul_inv_of_mul_eq h2.symm
  have h3 : m⁻¹ * permAct n σ⁻¹ m = (allOnes n ^ k)⁻¹ := by
    rw [hp]
    exact inv_mul_cancel_left m _
  rw [h3]
  exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers _ _)

open G6 in
theorem altDn_realizes {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {n : ℕ} (h : AlternatingNatural H U Z n) :
    ∃ (π : ↥(alternatingGroup (Fin n)) →* ↥H)
      (β : ↥U →* ↥(coreMod n) ⧸ (Subgroup.zpowers (allOnes n) ⊓ coreMod n).subgroupOf
        (coreMod n)),
      Function.Surjective π ∧
      (∀ σ : ↥(alternatingGroup (Fin n)), ∀ m ∈ coreMod n,
        permAct n (σ : Equiv.Perm (Fin n)) m ∈ coreMod n) ∧
      Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (σ : ↥(alternatingGroup (Fin n))) (u : ↥U) (m : ↥(coreMod n))
        (hu : ((π σ : ↥H) : MulAut V) (u : V) ∈ U)
        (hm : permAct n (σ : Equiv.Perm (Fin n)) (m : PermMod n) ∈ coreMod n),
        β u = QuotientGroup.mk m →
          β ⟨((π σ : ↥H) : MulAut V) (u : V), hu⟩ =
            QuotientGroup.mk ⟨permAct n (σ : Equiv.Perm (Fin n)) (m : PermMod n), hm⟩ := by
  obtain ⟨π, hπs, -, -, -, -, hsec, -, β, hβs, hβ1, hβeq⟩ := h
  exact ⟨π, β, hπs, hsec, hβs, hβ1, hβeq⟩

variable {G : Type} [Group G] [Finite G] {L V : Subgroup G} [IsMulCommutative ↥V]

theorem simple_case_alt (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hirr : ∀ J : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ J → J ≤ V →
      L ≤ Subgroup.normalizer (J : Set G) →
        J = V ⊓ Subgroup.centralizer (L : Set G) ∨ J = V)
    {n : ℕ} (halt : AlternatingNatural (autOn L V) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) n)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hK2 : pCoreOf 2 (autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) = ⊥)
    (hVL : V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))⁆) :
    IsSimpleGroup ↥(autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) := by
  by_cases hvL : v ∈ Subgroup.centralizer (L : Set G)
  · exact isSimpleGroup_of_mem_centralizer hLV hV2 hq hO2 hirr hv hv1 hvL hK2 hVL
  exfalso
  obtain ⟨π, β, hπs, hsec, hβs, hβ1, hβeq⟩ := altDn_realizes halt
  let kerQ := (Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n).subgroupOf (G6.coreMod n)
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨⟨v, hv⟩, trivial⟩)
  have hPker : ∀ y : ↥(G6.coreMod n), y ∈ kerQ →
      pairing (m : G6.PermMod n) (y : G6.PermMod n) = 0 := by
    intro y hy
    have hy' := (Subgroup.mem_subgroupOf.mp hy).1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
    have hmc : ∑ i, Multiplicative.toAdd (m : G6.PermMod n) i = 0 := m.2
    rw [← hk, pairing_comm, pairing_allOnes_zpow, hmc, mul_zero]
  let P' : ↥(G6.coreMod n) →* Multiplicative (ZMod 2) :=
    { toFun := fun y => Multiplicative.ofAdd
        (pairing (m : G6.PermMod n) (y : G6.PermMod n))
      map_one' := by
        show Multiplicative.ofAdd (pairing _ 1) = 1
        rw [pairing_one]
        rfl
      map_mul' := fun y z => by
        show Multiplicative.ofAdd (pairing _ ((y : G6.PermMod n) * (z : G6.PermMod n))) = _
        rw [pairing_mul, ofAdd_add] }
  have hP'ker : kerQ ≤ P'.ker := fun y hy => by
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd
      (pairing (m : G6.PermMod n) (y : G6.PermMod n)) = 1
    rw [hPker y hy, ofAdd_zero]
  let Pq : ↥(G6.coreMod n) ⧸ kerQ →* Multiplicative (ZMod 2) :=
    QuotientGroup.lift kerQ P' hP'ker
  let ψ : ↥V →* Multiplicative (ZMod 2) := Pq.comp (β.comp Subgroup.topEquiv.symm.toMonoidHom)
  have hψ : ∀ (x : ↥V) (y : ↥(G6.coreMod n)), β ⟨x, trivial⟩ = QuotientGroup.mk y →
      ψ x = Multiplicative.ofAdd
        (pairing (m : G6.PermMod n) (y : G6.PermMod n)) := by
    intro x y hxy
    change Pq (β ⟨x, trivial⟩) = _
    rw [hxy]
    rfl
  have hψl : ∀ (l : G) (hl : l ∈ oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) (x : ↥V),
      ψ (A4.actionOn V L hLV ⟨l, ((oTwoUpper_le _).trans inf_le_left) hl⟩ x) = ψ x := by
    intro l hl x
    have hlL : l ∈ L := ((oTwoUpper_le _).trans inf_le_left) hl
    obtain ⟨γ, hγ⟩ := hπs ⟨A4.actionOn V L hLV ⟨l, hlL⟩, (A4.mem_autOn_iff hLV).mpr ⟨_, rfl⟩⟩
    have hγv : ((π γ : ↥(autOn L V)) : MulAut ↥V) ⟨v, hv⟩ = ⟨v, hv⟩ := by
      rw [hγ]
      apply Subtype.ext
      change ((A4.actionOn V L hLV ⟨l, hlL⟩ ⟨v, hv⟩ : ↥V) : G) = v
      rw [A4.actionOn_apply_coe]
      have hc := Subgroup.mem_centralizer_singleton_iff.mp ((oTwoUpper_le _) hl).2
      rw [hc, mul_inv_cancel_right]
    have hγm := hβeq γ ⟨⟨v, hv⟩, trivial⟩ m trivial (hsec γ m m.2) hm.symm
    have hγm'' : β ⟨⟨v, hv⟩, trivial⟩ =
        QuotientGroup.mk ⟨G6.permAct n (γ : Equiv.Perm (Fin n)) (m : G6.PermMod n),
          hsec γ m m.2⟩ := by
      have : (⟨((π γ : ↥(autOn L V)) : MulAut ↥V) ⟨v, hv⟩, trivial⟩ : ↥(⊤ : Subgroup ↥V)) =
          ⟨⟨v, hv⟩, trivial⟩ := Subtype.ext hγv
      rw [← this]
      exact hγm
    have hγm' : (QuotientGroup.mk m : ↥(G6.coreMod n) ⧸ kerQ) =
        QuotientGroup.mk ⟨G6.permAct n (γ : Equiv.Perm (Fin n)) (m : G6.PermMod n),
          hsec γ m m.2⟩ := hm.trans hγm''
    have hrel : (m : G6.PermMod n)⁻¹ * G6.permAct n (γ : Equiv.Perm (Fin n)) m ∈
        Subgroup.zpowers (G6.allOnes n) := by
      have := QuotientGroup.eq.mp hγm'
      exact (Subgroup.mem_subgroupOf.mp this).1
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (β ⟨x, trivial⟩)
    have hγx := hβeq γ ⟨x, trivial⟩ y trivial (hsec γ y y.2) hy.symm
    have h1 : ψ x = Multiplicative.ofAdd (pairing (m : G6.PermMod n) (y : G6.PermMod n)) :=
      hψ x y hy.symm
    have h2 : ψ (((π γ : ↥(autOn L V)) : MulAut ↥V) x) = Multiplicative.ofAdd
        (pairing (m : G6.PermMod n)
          (G6.permAct n (γ : Equiv.Perm (Fin n)) (y : G6.PermMod n))) := hψ _ _ hγx
    rw [hγ] at h2
    rw [h2, h1]
    congr 1
    exact pairing_permAct_eq (γ : Equiv.Perm (Fin n)) m y (rel_inv hrel) y.2
  have hker' : ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))⁆ ≤ (ψ.ker).map V.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    have hlL : l ∈ L := ((oTwoUpper_le _).trans inf_le_left) hl
    refine ⟨⟨x, hx⟩ * (A4.actionOn V L hLV ⟨l, hlL⟩ ⟨x, hx⟩)⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hψl l hl]
      exact mul_inv_cancel _
    · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        A4.actionOn_apply_coe, commutatorElement_def]
      group
  have hker : V ≤ (ψ.ker).map V.subtype := hVL.le.trans hker'
  have hvZ : β ⟨⟨v, hv⟩, trivial⟩ ≠ 1 := fun h => hvL (Subgroup.mem_subgroupOf.mp
    ((hβ1 ⟨⟨v, hv⟩, trivial⟩).mp h))
  rw [← hm] at hvZ
  have hmker : m ∉ kerQ := fun h => hvZ ((QuotientGroup.eq_one_iff m).mpr h)
  have ha : ∃ a, Multiplicative.toAdd (m : G6.PermMod n) a = 1 := by
    by_contra hcon
    push Not at hcon
    apply hmker
    have h0 : (m : G6.PermMod n) = 1 := by
      apply Multiplicative.toAdd.injective
      funext a
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (Multiplicative.toAdd (m : G6.PermMod n) a)
        with h | h
      · rw [h]; rfl
      · exact absurd h (hcon a)
    rw [show m = 1 from Subtype.ext h0]
    exact Subgroup.one_mem _
  have hb : ∃ b, Multiplicative.toAdd (m : G6.PermMod n) b = 0 := by
    by_contra hcon
    push Not at hcon
    apply hmker
    rw [Subgroup.mem_subgroupOf]
    refine ⟨⟨1, ?_⟩, m.2⟩
    show G6.allOnes n ^ (1 : ℤ) = (m : G6.PermMod n)
    rw [zpow_one]
    apply Multiplicative.toAdd.injective
    funext b
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (Multiplicative.toAdd (m : G6.PermMod n) b)
      with h | h
    · exact absurd h (hcon b)
    · rw [h]
      rfl
  obtain ⟨a, hma⟩ := ha
  obtain ⟨b, hmb⟩ := hb
  have hab : a ≠ b := fun h => by rw [h, hmb] at hma; exact zero_ne_one hma
  set y₀ : G6.PermMod n :=
    Multiplicative.ofAdd (Pi.single a (1 : ZMod 2) + Pi.single b (1 : ZMod 2)) with hy₀
  have hy₀c : y₀ ∈ G6.coreMod n := by
    show ∑ i, Multiplicative.toAdd y₀ i = 0
    simp only [hy₀, toAdd_ofAdd, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
      Finset.mem_univ, ite_true]
    decide
  have hPy : pairing (m : G6.PermMod n) y₀ = 1 := by
    simp only [pairing, hy₀, toAdd_ofAdd, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi])
      (fun h => absurd (Finset.mem_univ a) h), Finset.sum_eq_single b
      (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ b) h)]
    simp [hma, hmb]
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨y₀, hy₀c⟩)
  have hψu : ψ (u : ↥V) = Multiplicative.ofAdd 1 := by
    rw [hψ (u : ↥V) ⟨y₀, hy₀c⟩ (show β ⟨(u : ↥V), trivial⟩ = _ from hu), hPy]
  obtain ⟨w, hw, hwu⟩ := hker (u : ↥V).2
  have hw' : w = (u : ↥V) := Subtype.ext hwu
  have hw2 : ψ (u : ↥V) = 1 := by
    rw [← hw']
    exact hw
  rw [hψu] at hw2
  exact absurd hw2 (by decide)

end Lem12St

end CFSG.Quasithin.H13
