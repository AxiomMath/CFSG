module

public import CFSG.RankThree.PartOne.S11c.HNFiveCoverage
public import CFSG.RankThree.PartOne.S11c.HNInvQ6
public import CFSG.Sporadic.HNOddCore.FusB
public import CFSG.Sporadic.HNOddCore.Five

public noncomputable section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG CFSG.Assembly.LowTwoRank

section Transport

theorem exists_hom_of_isConj {G Q : Type*} [Group G] [Group Q] {a t : G} (hconj : IsConj a t)
    (q₀ : centralizer ({a} : Set G) →* Q)
    (hq₀ : ∀ x : centralizer ({a} : Set G), q₀ x = 1 → (x : G) = 1 ∨ (x : G) = a) :
    ∃ q : centralizer ({t} : Set G) →* Q,
      ∀ x : centralizer ({t} : Set G), q x = 1 → (x : G) = 1 ∨ (x : G) = t := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  let φ : centralizer ({t} : Set G) →* centralizer ({a} : Set G) :=
    { toFun := fun x => ⟨c⁻¹ * x * c, by
        rw [mem_centralizer_singleton_iff]
        have h1 : (x : G) * (c * a * c⁻¹) = (c * a * c⁻¹) * x := by
          rw [hc]
          exact mem_centralizer_singleton_iff.1 x.2
        calc c⁻¹ * x * c * a = c⁻¹ * (x * (c * a * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * a * c⁻¹) * x) * c := by rw [h1]
          _ = a * (c⁻¹ * x * c) := by group⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  refine ⟨q₀.comp φ, fun x hx => ?_⟩
  rcases hq₀ (φ x) hx with h | h
  · left
    have h1 : c⁻¹ * x * c = 1 := h
    calc (x : G) = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · right
    have h1 : c⁻¹ * x * c = a := h
    calc (x : G) = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = t := by rw [h1, hc]

theorem exists_hom_of_mulEquiv {G H Q : Type*} [Group G] [Group H] [Group Q] (e : G ≃* H)
    {a : G} {b : H} (hb : e a = b) (q₀ : centralizer ({b} : Set H) →* Q)
    (hq₀ : ∀ x : centralizer ({b} : Set H), q₀ x = 1 → (x : H) = 1 ∨ (x : H) = b) :
    ∃ q : centralizer ({a} : Set G) →* Q,
      ∀ x : centralizer ({a} : Set G), q x = 1 → (x : G) = 1 ∨ (x : G) = a := by
  subst hb
  let φ : centralizer ({a} : Set G) →* centralizer ({e a} : Set H) :=
    { toFun := fun x => ⟨e x, by
        rw [mem_centralizer_singleton_iff]
        have h1 : (x : G) * a = a * x := mem_centralizer_singleton_iff.1 x.2
        rw [← map_mul, ← map_mul, h1]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  refine ⟨q₀.comp φ, fun x hx => ?_⟩
  rcases hq₀ (φ x) hx with h | h
  · left
    have h1 : e x = 1 := h
    exact e.injective (by rw [h1, map_one])
  · right
    have h1 : e x = e a := h
    exact e.injective h1

end Transport

section Witness

theorem exists_zpow_mul_of_mem_sup {G : Type*} [Group G] (f : G) (K : Subgroup G)
    (hK : ∀ k ∈ K, f * k = k * f) :
    ∀ x ∈ zpowers f ⊔ K, ∃ (i : ℤ) (k : G), k ∈ K ∧ x = f ^ i * k := by
  have hfz : ∀ (k : G), k ∈ K → ∀ i : ℤ, f ^ i * k = k * f ^ i := fun k hk i =>
    (Commute.zpow_left (show Commute f k from hK k hk) i).eq
  intro x hx
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ⟨i, 1, K.one_mem, by simp⟩
    · exact ⟨0, x, hx, by simp⟩
  | one => exact ⟨0, 1, K.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, k, hk, rfl⟩ := hx
    obtain ⟨j, k', hk', rfl⟩ := hy
    refine ⟨i + j, k * k', K.mul_mem hk hk', ?_⟩
    calc f ^ i * k * (f ^ j * k') = f ^ i * (k * f ^ j) * k' := by group
      _ = f ^ i * (f ^ j * k) * k' := by rw [hfz k hk j]
      _ = f ^ (i + j) * (k * k') := by rw [zpow_add]; group
  | inv x _ hx =>
    obtain ⟨i, k, hk, rfl⟩ := hx
    refine ⟨-i, k⁻¹, K.inv_mem hk, ?_⟩
    calc (f ^ i * k)⁻¹ = k⁻¹ * f ^ (-i) := by group
      _ = f ^ (-i) * k⁻¹ := (hfz k⁻¹ (K.inv_mem hk) (-i)).symm

theorem mem_of_sq_eq_one_of_mem_sup {G : Type*} [Group G] {f : G} {K : Subgroup G}
    (hf5 : orderOf f = 5) (hinf : zpowers f ⊓ K = ⊥) (hK : ∀ k ∈ K, f * k = k * f) {x : G}
    (hx : x ∈ zpowers f ⊔ K) (hx2 : x ^ 2 = 1) : x ∈ K := by
  obtain ⟨i, k, hk, rfl⟩ := exists_zpow_mul_of_mem_sup f K hK x hx
  have hcomm : f ^ i * k = k * f ^ i := (Commute.zpow_left (show Commute f k from hK k hk) i).eq
  have h1 : f ^ (2 * i) * k ^ 2 = 1 := by
    have e1 : f ^ (2 * i) = f ^ i * f ^ i := by rw [two_mul, zpow_add]
    have e2 : (f ^ i * k) ^ 2 = f ^ i * k * (f ^ i * k) := sq _
    calc f ^ (2 * i) * k ^ 2 = f ^ i * f ^ i * (k * k) := by rw [e1, sq]
      _ = f ^ i * (f ^ i * k) * k := by simp only [mul_assoc]
      _ = f ^ i * (k * f ^ i) * k := by rw [← hcomm]
      _ = f ^ i * k * (f ^ i * k) := by simp only [mul_assoc]
      _ = (f ^ i * k) ^ 2 := e2.symm
      _ = 1 := hx2
  have h2 : f ^ (2 * i) ∈ zpowers f ⊓ K := by
    refine ⟨mem_zpowers_iff.2 ⟨2 * i, rfl⟩, ?_⟩
    have : f ^ (2 * i) = (k ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact K.inv_mem (K.pow_mem hk 2)
  rw [hinf] at h2
  have h3 : f ^ (2 * i) = 1 := h2
  have h4 : (orderOf f : ℤ) ∣ 2 * i := orderOf_dvd_iff_zpow_eq_one.2 h3
  rw [hf5] at h4
  have h5 : (orderOf f : ℤ) ∣ i := by rw [hf5]; omega
  have h6 : f ^ i = 1 := orderOf_dvd_iff_zpow_eq_one.1 h5
  rw [h6, one_mul]
  exact hk

theorem isConj_of_witness {G : Type} [Group G] [Finite G] (hcov : SevenCommuteConj G)
    (f₀ : G) (hf₀ : orderOf f₀ = 5) (hf₀u : ∃ u : G, orderOf u = 7 ∧ f₀ * u = u * f₀)
    (hc₀ : Nat.card (centralizer ({f₀} : Set G)) = 630000) (s₀ : G) (hs₀ : orderOf s₀ = 2)
    (hs₀f : f₀ * s₀ = s₀ * f₀) {f t : G} {K Y : Subgroup G} (hw : IsNativeWitness f t K Y) :
    IsConj t s₀ := by
  obtain ⟨hC1, -⟩ := fiveCoverage_of_data hcov f₀ hf₀ hf₀u hc₀ hw
  obtain ⟨hf5, hKf, -, hinf, -, -, hKmod, hYK, -, htY, ht2, -⟩ := hw
  have hfu := exists_order_seven_commute hKf hKmod
  obtain ⟨g, a, hga⟩ := hcov f₀ f hf₀ hf5 hf₀u hfu
  have hsf : f * (g * s₀ * g⁻¹) = (g * s₀ * g⁻¹) * f := by
    have h1 : f₀ ^ a * s₀ = s₀ * f₀ ^ a := (Commute.pow_left (show Commute f₀ s₀ from hs₀f) a).eq
    rw [hga]
    calc g * f₀ ^ a * g⁻¹ * (g * s₀ * g⁻¹) = g * (f₀ ^ a * s₀) * g⁻¹ := by group
      _ = g * (s₀ * f₀ ^ a) * g⁻¹ := by rw [h1]
      _ = g * s₀ * g⁻¹ * (g * f₀ ^ a * g⁻¹) := by group
  have hs2 : orderOf (g * s₀ * g⁻¹) = 2 := by
    have h1 : orderOf (g * s₀ * g⁻¹) = orderOf s₀ :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective s₀
    rw [h1, hs₀]
  have hsC : g * s₀ * g⁻¹ ∈ centralizer ({f} : Set G) :=
    mem_centralizer_singleton_iff.2 hsf.symm
  have hsK : g * s₀ * g⁻¹ ∈ K :=
    mem_of_sq_eq_one_of_mem_sup hf5 hinf
      (fun k hk => (mem_centralizer_singleton_iff.1 (hKf hk)).symm) (hC1 hsC)
      (by rw [← orderOf_dvd_iff_pow_eq_one, hs2])
  have htK : t ∈ K := hYK htY
  have hconj := (CFSG.RankThree.Classical.unitary_three_five_model K hKmod).2.2.2
    ⟨t, htK⟩ ⟨g * s₀ * g⁻¹, hsK⟩ (by rw [Subgroup.orderOf_mk]; exact ht2)
    (by rw [Subgroup.orderOf_mk]; exact hs2)
  have h1 : IsConj t (g * s₀ * g⁻¹) := by
    have := (Subgroup.subtype K).map_isConj hconj
    simpa using this
  have h2 : IsConj (g * s₀ * g⁻¹) s₀ := (isConj_iff.2 ⟨g, rfl⟩).symm
  exact h1.trans h2

end Witness

section Abstract

theorem nativeInvolution_of_equiv {G H Q : Type} [Group G] [Group H] [Group Q] [Finite H]
    (e : G ≃* H) (hcov : SevenCommuteConj H) (f₀ : H) (hf₀ : orderOf f₀ = 5)
    (hf₀u : ∃ u : H, orderOf u = 7 ∧ f₀ * u = u * f₀)
    (hc₀ : Nat.card (centralizer ({f₀} : Set H)) = 630000) (s₀ : H) (hs₀ : orderOf s₀ = 2)
    (hs₀f : f₀ * s₀ = s₀ * f₀) (a₀ : H) (hconj : IsConj s₀ a₀)
    (q₀ : centralizer ({a₀} : Set H) →* Q)
    (hq₀ : ∀ x : centralizer ({a₀} : Set H), q₀ x = 1 → (x : H) = 1 ∨ (x : H) = a₀)
    {f t : G} {K Y : Subgroup G} (hw : IsNativeWitness f t K Y) :
    ∃ q : centralizer ({t} : Set G) →* Q,
      ∀ x : centralizer ({t} : Set G), q x = 1 → (x : G) = 1 ∨ (x : G) = t := by
  have hfin : Finite G := Finite.of_equiv H e.symm.toEquiv
  obtain ⟨hf₁, hf₁u, hc₁⟩ := coverage_data_of_mulEquiv e hf₀ hf₀u hc₀
  have hs₁ : orderOf (e.symm s₀) = 2 := by rw [MulEquiv.orderOf_eq]; exact hs₀
  have hs₁f : e.symm f₀ * e.symm s₀ = e.symm s₀ * e.symm f₀ := by
    rw [← map_mul, ← map_mul, hs₀f]
  have hc : IsConj t (e.symm s₀) :=
    isConj_of_witness (sevenCommuteConj_of_mulEquiv e hcov) (e.symm f₀) hf₁ hf₁u hc₁ (e.symm s₀)
      hs₁ hs₁f hw
  have hconj' : IsConj (e.symm s₀) (e.symm a₀) := e.symm.toMonoidHom.map_isConj hconj
  obtain ⟨q₁, hq₁⟩ := exists_hom_of_mulEquiv e (a := e.symm a₀) (b := a₀)
    (MulEquiv.apply_symm_apply e a₀) q₀ hq₀
  exact exists_hom_of_isConj (hc.trans hconj').symm q₁ hq₁

end Abstract

section JSide

open Equiv CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native

@[expose] def sig57 : Perm (Fin 12) := swap 5 6 * swap 7 8

theorem sig57_mem : sig57 ∈ alternatingGroup (Fin 12) := by
  rw [Perm.mem_alternatingGroup, sig57]
  decide

theorem sig57_sq : sig57 ^ 2 = 1 := by unfold sig57; decide

theorem sig57_ne_one : sig57 ≠ 1 := by unfold sig57; decide

theorem sig57_type : sig57.cycleType = Multiset.replicate 2 2 :=
  cycleType_of_sq sig57_sq (by unfold sig57; decide)

theorem sig57_fix : ∀ i : Fin 12, i.val < 5 → sig57 i = i := by
  unfold sig57
  decide

theorem orderOf_sig57 : orderOf sig57 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime sig57_sq sig57_ne_one

@[expose] def s57H :
    HJ := thetaJ.symm ⟨sig57, sig57_mem⟩

theorem thetaJ_s57H :
    (thetaJ s57H : Perm (Fin 12)) = sig57 := by
  rw [s57H, MulEquiv.apply_symm_apply]

theorem s57H_mem_AH :
    s57H ∈ AH := by
  rw [AH, Subgroup.mem_comap, mem_alt5]
  intro i hi
  have h : (((thetaJ : HJ →* alternatingGroup (Fin 12)) s57H : alternatingGroup (Fin 12)) :
      Perm (Fin 12)) = sig57 := thetaJ_s57H
  rw [h]
  exact sig57_fix i hi

theorem exists_s₀ :
    ∃ s₀ : JH, orderOf s₀ = 2 ∧ fJ * s₀ = s₀ * fJ ∧ IsConj s₀ aJ := by
  obtain ⟨hcomm, -⟩ := ctuc_hn_five_centralizer_perfect_factor
  refine ⟨(s57H : JH), ?_, ?_, ?_⟩
  · refine orderOf_coe_of_equiv thetaJ s57H ?_
    rw [← Subgroup.orderOf_coe, thetaJ_s57H, orderOf_sig57]
  · have hmem : (s57H : JH) ∈ IJ := AJ_le_IJ ⟨s57H, s57H_mem_AH, rfl⟩
    exact hcomm fJ (mem_zpowers fJ) _ hmem
  · have h1 : IsConj (t2H : JH) (s57H : JH) := isConj_HJ_of_cycleType
      (by rw [thetaJ_t2H]; exact sig2_sq) (by rw [thetaJ_t2H]; unfold sig2; decide)
      (by rw [thetaJ_t2H, thetaJ_s57H, sig2_type, sig57_type])
    exact h1.symm.trans isConj_t2_aJ

end JSide

section Main

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem hnNativeInvolution_holds :
    HNNativeInvolution := by
  intro f t K Y hw
  have hcovJ : SevenCommuteConj JH := fun _ _ hf hw hfu hwu =>
    exists_conj_pow_of_commute_seven_JH hf hw hfu hwu
  obtain ⟨hcomm, -, -, hfJ5, hcardC, hcardI, -⟩ := ctuc_hn_five_centralizer_perfect_factor
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := IJ) 7 (by rw [hcardI]; norm_num)
  have hfJu : ∃ u : JH, orderOf u = 7 ∧ fJ * u = u * fJ :=
    ⟨(x : JH), by rw [Subgroup.orderOf_coe]; exact hx, hcomm fJ (mem_zpowers fJ) x x.2⟩
  obtain ⟨s₀, hs₀, hs₀f, hs₀c⟩ := exists_s₀
  obtain ⟨q₆, hq₆⟩ := exists_q6
  exact @nativeInvolution_of_equiv (Carrier .HN) (↥JH) (MulAut (Carrier .HS))
    (CFSG.Blueprint.NativeSporadic.carrierGroup .HN) inferInstance inferInstance inferInstance
    hnEquivJ hcovJ fJ hfJ5 hfJu hcardC s₀ hs₀ hs₀f aJ hs₀c q₆ hq₆ f t K Y hw

end Main

end CFSG.RankThree.PartOne.HNRed
