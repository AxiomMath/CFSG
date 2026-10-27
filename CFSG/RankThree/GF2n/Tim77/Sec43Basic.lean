module

public import CFSG.RankThree.GF2n.Tim77.Sec32a
public import CFSG.RankThree.GF2n.Tim77.Sec41
public import CFSG.RankThree.GF2n.Tim77.Sec34
public import CFSG.RankThree.GF2n.Tim77.Sec21
public import CFSG.RankThree.GF2n.Tim77.DihFixed
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped commutatorElement

section Count

variable {G : Type} [Group G] [Finite G]

theorem sa_card_mul_le_sup {X Y : Subgroup G} (hXY : X ⊓ Y = ⊥) :
    Nat.card X * Nat.card Y ≤ Nat.card (X ⊔ Y : Subgroup G) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun q : X × Y => (⟨q.1 * q.2, Subgroup.mul_mem_sup q.1.2 q.2.2⟩ : ↥(X ⊔ Y))) ?_
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
  have h' : a * b = a' * b' := congrArg Subtype.val hab
  have hm : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h']
      _ = b' * b⁻¹ := by group
  have hmem : a'⁻¹ * a ∈ X ⊓ Y :=
    ⟨X.mul_mem (X.inv_mem ha') ha, hm ▸ Y.mul_mem hb' (Y.inv_mem hb)⟩
  rw [hXY, Subgroup.mem_bot] at hmem
  obtain rfl : a' = a := inv_mul_eq_one.mp hmem
  obtain rfl : b = b' := mul_left_cancel h'
  rfl

theorem sa_card_sup_le {X Y : Subgroup G} (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    Nat.card (X ⊔ Y : Subgroup G) ≤ Nat.card X * Nat.card Y := by
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) :=
    CFSG.RankThree.GF2n.le_normalizer_of_comm fun y hy x hx => (hc x hx y hy).symm
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective
    (fun q : X × Y => (⟨q.1 * q.2, Subgroup.mul_mem_sup q.1.2 q.2.2⟩ : ↥(X ⊔ Y))) fun x => ?_
  obtain ⟨u, hu, v, hv, huv⟩ := CFSG.RankThree.GF2n.exists_mul_of_mem_sup hYX x.2
  exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), Subtype.ext huv.symm⟩

theorem sa_card_subgroupOf {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem sa_count {V P Q T : Subgroup G} {s : G} (hV : IsElemAbelian 2 V)
    (hsV : ∀ v ∈ V, s * v * s⁻¹ ∈ V) (hss : s * s ∈ V) (hPV : P ≤ V) (hQV : Q ≤ V)
    (hTV : T ≤ V) (hgen : V = P ⊔ Q ⊔ conjSubgroup s Q) (hP : ∀ p ∈ P, s * p * s⁻¹ = p)
    (hQQ : Q ⊓ conjSubgroup s Q = ⊥) (hPQ : Nat.card Q = Nat.card P)
    (hT : ∀ t ∈ T, s * t * s⁻¹ = t) (hTc : Nat.card P ^ 2 ≤ Nat.card T) :
    Nat.card P ^ 3 ≤ Nat.card V ∧ ∀ q ∈ Q, q * (s * q * s⁻¹) ∈ T := by
  have hcomm : IsMulCommutative ↥V := hV.1
  have hc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    rw [← sq]
    exact hV.2 v hv
  let δ : ↥V →* ↥V := MonoidHom.mk'
    (fun v => ⟨(v : G) * (s * (v : G) * s⁻¹), V.mul_mem v.2 (hsV v v.2)⟩) (by
      intro a b
      apply Subtype.ext
      show (a : G) * (b : G) * (s * ((a : G) * (b : G)) * s⁻¹) =
        ((a : G) * (s * (a : G) * s⁻¹)) * ((b : G) * (s * (b : G) * s⁻¹))
      have hcom := hc (s * (a : G) * s⁻¹) (hsV a a.2) (b : G) b.2
      calc (a : G) * (b : G) * (s * ((a : G) * (b : G)) * s⁻¹)
          = (a : G) * ((b : G) * (s * (a : G) * s⁻¹)) * (s * (b : G) * s⁻¹) := by group
        _ = (a : G) * ((s * (a : G) * s⁻¹) * (b : G)) * (s * (b : G) * s⁻¹) := by rw [← hcom]
        _ = ((a : G) * (s * (a : G) * s⁻¹)) * ((b : G) * (s * (b : G) * s⁻¹)) := by group)
  have hδ : ∀ v : ↥V, ((δ v : ↥V) : G) = (v : G) * (s * (v : G) * s⁻¹) := fun v => rfl
  have hσσ : ∀ v ∈ V, s * (s * v * s⁻¹) * s⁻¹ = v := by
    intro v hv
    have := hc (s * s) hss v hv
    calc s * (s * v * s⁻¹) * s⁻¹ = (s * s) * v * (s * s)⁻¹ := by group
      _ = v * (s * s) * (s * s)⁻¹ := by rw [this]
      _ = v := by group
  have hker : ∀ v : ↥V, v ∈ δ.ker ↔ s * (v : G) * s⁻¹ = (v : G) := by
    intro v
    rw [MonoidHom.mem_ker]
    have hvv := hsq v v.2
    have hww := hsq (s * (v : G) * s⁻¹) (hsV v v.2)
    constructor
    · intro h1
      have h2 : (v : G) * (s * (v : G) * s⁻¹) = 1 := congrArg Subtype.val h1
      calc s * (v : G) * s⁻¹ = (v : G)⁻¹ * ((v : G) * (s * (v : G) * s⁻¹)) := by group
        _ = (v : G)⁻¹ := by rw [h2, mul_one]
        _ = (v : G) := inv_eq_of_mul_eq_one_right hvv
    · intro h1
      apply Subtype.ext
      show (v : G) * (s * (v : G) * s⁻¹) = 1
      rw [h1]
      exact hvv
  have hTker : T.subgroupOf V ≤ δ.ker := by
    intro t ht
    rw [hker]
    exact hT t (Subgroup.mem_subgroupOf.mp ht)
  have hQr : Nat.card Q ≤ Nat.card δ.range := by
    refine Nat.card_le_card_of_injective
      (fun q : Q => (⟨δ ⟨(q : G), hQV q.2⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ : ↥δ.range)) ?_
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have h1 : (a : G) * (s * a * s⁻¹) = (b : G) * (s * b * s⁻¹) :=
      congrArg (fun x : ↥δ.range => ((x : ↥V) : G)) hab
    have haV := hQV ha
    have hbV := hQV hb
    have hbb := hsq b hbV
    have ha'a' : (s * a * s⁻¹) * (s * a * s⁻¹) = 1 := hsq _ (hsV a haV)
    have hb'b' : (s * b * s⁻¹) * (s * b * s⁻¹) = 1 := hsq _ (hsV b hbV)
    have hw : s * (a * b) * s⁻¹ = a * b := by
      have e : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
      rw [e]
      calc (s * a * s⁻¹) * (s * b * s⁻¹)
          = a * (a * (s * a * s⁻¹)) * (s * b * s⁻¹) := by rw [← mul_assoc a a, hsq a haV, one_mul]
        _ = a * (b * (s * b * s⁻¹)) * (s * b * s⁻¹) := by rw [h1]
        _ = a * b * ((s * b * s⁻¹) * (s * b * s⁻¹)) := by group
        _ = a * b := by rw [hb'b', mul_one]
    have hwQ : (a : G) * b ∈ Q := Q.mul_mem ha hb
    have hwQ' : (a : G) * b ∈ conjSubgroup s Q := by
      have e : s⁻¹ * (a * b) * s = a * b := by
        calc s⁻¹ * (a * b) * s = s⁻¹ * (s * (a * b) * s⁻¹) * s := by rw [hw]
          _ = a * b := by group
      rw [mem_conjSubgroup, e]
      exact hwQ
    have h1' : (a : G) * b = 1 := by
      have : (a : G) * b ∈ Q ⊓ conjSubgroup s Q := ⟨hwQ, hwQ'⟩
      rw [hQQ, Subgroup.mem_bot] at this
      exact this
    apply Subtype.ext
    show (a : G) = b
    calc (a : G) = a * b * b := by rw [mul_assoc, hbb, mul_one]
      _ = b := by rw [h1', one_mul]
  have hQ'V : conjSubgroup s Q ≤ V := by
    rw [hgen]
    exact le_sup_right
  have hVc : Nat.card V ≤ Nat.card P ^ 3 := by
    calc Nat.card V = Nat.card (P ⊔ Q ⊔ conjSubgroup s Q : Subgroup G) := by rw [← hgen]
      _ ≤ Nat.card (P ⊔ Q : Subgroup G) * Nat.card (conjSubgroup s Q) :=
          sa_card_sup_le fun x hx y hy => hc x (sup_le hPV hQV hx) y (hQ'V hy)
      _ ≤ (Nat.card P * Nat.card Q) * Nat.card (conjSubgroup s Q) :=
          Nat.mul_le_mul_right _ (sa_card_sup_le fun x hx y hy => hc x (hPV hx) y (hQV hy))
      _ = Nat.card P ^ 3 := by
          rw [CFSG.RankThree.GF2n.card_conjSubgroup, hPQ]
          ring
  have hcpos : 0 < Nat.card P := Nat.card_pos
  have hkr := Subgroup.card_ker_mul_card_range δ
  have hTq : Nat.card P ^ 2 ≤ Nat.card (T.subgroupOf V) := by
    rw [sa_card_subgroupOf hTV]
    exact hTc
  have hTk : Nat.card (T.subgroupOf V) ≤ Nat.card δ.ker := Subgroup.card_le_of_le hTker
  have hQrP : Nat.card P ≤ Nat.card δ.range := hPQ ▸ hQr
  have hkc : Nat.card δ.ker ≤ Nat.card P ^ 2 := by
    have h1 : Nat.card δ.ker * Nat.card P ≤ Nat.card P ^ 2 * Nat.card P := by
      calc Nat.card δ.ker * Nat.card P ≤ Nat.card δ.ker * Nat.card δ.range :=
            Nat.mul_le_mul_left _ hQrP
        _ = Nat.card V := hkr
        _ ≤ Nat.card P ^ 3 := hVc
        _ = Nat.card P ^ 2 * Nat.card P := by ring
    exact Nat.le_of_mul_le_mul_right h1 hcpos
  have hkerT : T.subgroupOf V = δ.ker := Subgroup.eq_of_le_of_card_ge hTker (hkc.trans hTq)
  refine ⟨?_, ?_⟩
  · calc Nat.card P ^ 3 = Nat.card P ^ 2 * Nat.card P := by ring
      _ ≤ Nat.card δ.ker * Nat.card δ.range := Nat.mul_le_mul (hTq.trans hTk) hQrP
      _ = Nat.card V := hkr
  · intro q hq
    have hqV := hQV hq
    have hmem : δ ⟨q, hqV⟩ ∈ δ.ker := by
      rw [hker]
      show s * (q * (s * q * s⁻¹)) * s⁻¹ = q * (s * q * s⁻¹)
      calc s * (q * (s * q * s⁻¹)) * s⁻¹ = (s * q * s⁻¹) * (s * (s * q * s⁻¹) * s⁻¹) := by group
        _ = (s * q * s⁻¹) * q := by rw [hσσ q hqV]
        _ = q * (s * q * s⁻¹) := hc _ (hsV q hqV) q hqV
    rw [← hkerT] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem

end Count

section SA

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G} {s : G}

theorem sa_A0_le_N : Section3.A0 A Abar ≤ Section3.N A Abar s := by
  unfold Section3.N
  exact le_sup_left.trans le_sup_left

theorem sa_Abar0_le_N : Section3.Abar0 A Abar ≤ Section3.N A Abar s := by
  unfold Section3.N
  exact le_sup_right.trans le_sup_left

theorem sa_conj_Abar0_le_N : conjSubgroup s (Section3.Abar0 A Abar) ≤ Section3.N A Abar s := by
  unfold Section3.N
  exact le_sup_right

theorem sa_A_le_Y : A ≤ Section3.Y A Abar s := by
  unfold Section3.Y
  exact le_sup_left.trans le_sup_left

theorem sa_Abar_le_Y : Abar ≤ Section3.Y A Abar s := by
  unfold Section3.Y
  exact le_sup_right.trans le_sup_left

theorem sa_conj_Abar_le_Y : conjSubgroup s Abar ≤ Section3.Y A Abar s := by
  unfold Section3.Y
  exact le_sup_right

theorem sa_sq_of_mem_B (h : Sec3Ctx A Abar S₀ B) {b : G} (hb : b ∈ B) : b * b = 1 := by
  obtain ⟨g, hg⟩ := h.nota.conj
  rw [← sq]
  exact (isElemAbelian_conj h.hyp.elemAbelian g).2 b (hg ▸ hb)

theorem sa_comm_A (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s) {a : G}
    (ha : a ∈ A) : s * a = a * s :=
  (sec32a_s_facts h hs).2 a ha

theorem sa_sq_mem_N (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s) :
    s * s ∈ Section3.N A Abar s := by
  obtain ⟨b, hb, -, hdisj⟩ := hs
  have hbb := sa_sq_of_mem_B h hb
  rcases hdisj with ⟨-, rfl⟩ | ⟨-, x, hx, -, hsx, -, -, -, -, hord⟩
  · rw [hbb]
    exact Subgroup.one_mem _
  · have hxx : x * x = 1 := h.setup.sq_Ab (h.setup.Lb_le hx)
    have hxN : x ∈ Section3.N A Abar s := sa_Abar0_le_N hx
    have hxsN : s * x * s⁻¹ ∈ Section3.N A Abar s :=
      sa_conj_Abar0_le_N (mem_conjSubgroup.mpr
        (by rw [show s⁻¹ * (s * x * s⁻¹) * s = x by group]; exact hx))
    rcases sec34_closure_pair hxx hbb hsx with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hxs : x * s * x = s⁻¹ := by
        rw [hi, sec34_conj_zpow hxx hbb i, zpow_neg]
      have e1 : s * x * s⁻¹ = s * s * x := by
        calc s * x * s⁻¹ = s * x * (x * s * x) := by rw [hxs]
          _ = s * (x * x) * s * x := by group
          _ = s * s * x := by rw [hxx, mul_one]
      have e : s * s = (s * x * s⁻¹) * x := by
        rw [e1, mul_assoc (s * s) x x, hxx, mul_one]
      rw [e]
      exact Subgroup.mul_mem _ hxsN hxN
    · exfalso
      have hs' : s = (x * b) ^ i * x := by
        rw [← hi, mul_assoc, hxx, mul_one]
      have h1 : s * s = 1 := by
        rw [hs']
        calc (x * b) ^ i * x * ((x * b) ^ i * x)
            = (x * b) ^ i * (x * (x * b) ^ i * x) := by group
          _ = (x * b) ^ i * (x * b) ^ (-i) := by rw [sec34_conj_zpow hxx hbb i]
          _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
      have h2 : s ^ 2 = 1 := by rw [sq]; exact h1
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hord] at h3
      norm_num at h3

theorem sa_conj_mem_N (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    {v : G} (hv : v ∈ Section3.N A Abar s) : s * v * s⁻¹ ∈ Section3.N A Abar s := by
  obtain ⟨-, -, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  have hss := sa_sq_mem_N h hs
  have hA0 : ∀ p ∈ Section3.A0 A Abar, s * p * s⁻¹ ∈ Section3.N A Abar s := by
    intro p hp
    have : s * p * s⁻¹ = p := by rw [sa_comm_A h hs (h.setup.L_le hp)]; group
    rw [this]
    exact sa_A0_le_N hp
  have hAb0 : ∀ q ∈ Section3.Abar0 A Abar, s * q * s⁻¹ ∈ Section3.N A Abar s := by
    intro q hq
    exact sa_conj_Abar0_le_N (mem_conjSubgroup.mpr
      (by rw [show s⁻¹ * (s * q * s⁻¹) * s = q by group]; exact hq))
  have hcAb0 : ∀ z ∈ conjSubgroup s (Section3.Abar0 A Abar),
      s * z * s⁻¹ ∈ Section3.N A Abar s := by
    intro z hz
    have hq : s⁻¹ * z * s ∈ Section3.Abar0 A Abar := mem_conjSubgroup.mp hz
    have hqN : s⁻¹ * z * s ∈ Section3.N A Abar s := sa_Abar0_le_N hq
    have hc := hNab.1.is_comm.comm (⟨s * s, hss⟩ : ↥(Section3.N A Abar s)) ⟨s⁻¹ * z * s, hqN⟩
    have hc' : (s * s) * (s⁻¹ * z * s) = (s⁻¹ * z * s) * (s * s) := congrArg Subtype.val hc
    have e : s * z * s⁻¹ = s⁻¹ * z * s := by
      calc s * z * s⁻¹ = (s * s) * (s⁻¹ * z * s) * (s * s)⁻¹ := by group
        _ = (s⁻¹ * z * s) * (s * s) * (s * s)⁻¹ := by rw [hc']
        _ = s⁻¹ * z * s := by group
    rw [e]
    exact hqN
  have hP := sec32a_conj_mem_of_sup (P := Section3.A0 A Abar ⊔ Section3.Abar0 A Abar)
    (Q := conjSubgroup s (Section3.Abar0 A Abar)) (N := Section3.N A Abar s) (x := s)
    (sec32a_conj_mem_of_sup (P := Section3.A0 A Abar) (Q := Section3.Abar0 A Abar) hA0 hAb0)
    hcAb0
  exact hP v hv

theorem sa_mem_normalizer_of_forall {K : Subgroup G} {g : G} (hK : ∀ y ∈ K, g * y * g⁻¹ ∈ K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  have hle : K ≤ conjSubgroup g⁻¹ K := fun y hy => by
    rw [mem_conjSubgroup, inv_inv]
    exact hK y hy
  have h2 : conjSubgroup g⁻¹ K = K := conjSubgroup_eq_of_ge hle
  have h3 : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_conjSubgroup_eq h2
  simpa using (Subgroup.normalizer (K : Set G)).inv_mem h3

theorem sa_conj_mem_Y (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    {y : G} (hy : y ∈ Section3.Y A Abar s) : s * y * s⁻¹ ∈ Section3.Y A Abar s := by
  obtain ⟨hNY, -, -⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  have hss := sa_sq_mem_N h hs
  have hA : ∀ a ∈ A, s * a * s⁻¹ ∈ Section3.Y A Abar s := by
    intro a ha
    have : s * a * s⁻¹ = a := by rw [sa_comm_A h hs ha]; group
    rw [this]
    exact sa_A_le_Y ha
  have hAb : ∀ x ∈ Abar, s * x * s⁻¹ ∈ Section3.Y A Abar s := by
    intro x hx
    exact sa_conj_Abar_le_Y (mem_conjSubgroup.mpr
      (by rw [show s⁻¹ * (s * x * s⁻¹) * s = x by group]; exact hx))
  have hcAb : ∀ z ∈ conjSubgroup s Abar, s * z * s⁻¹ ∈ Section3.Y A Abar s := by
    intro z hz
    have hx : s⁻¹ * z * s ∈ Abar := mem_conjSubgroup.mp hz
    have e : s * z * s⁻¹ = (s * s) * (s⁻¹ * z * s) * (s * s)⁻¹ := by group
    rw [e]
    exact (Section3.Y A Abar s).mul_mem ((Section3.Y A Abar s).mul_mem (hNY hss)
      (sa_Abar_le_Y hx)) ((Section3.Y A Abar s).inv_mem (hNY hss))
  have hP := sec32a_conj_mem_of_sup (P := A ⊔ Abar) (Q := conjSubgroup s Abar)
    (N := Section3.Y A Abar s) (x := s) (sec32a_conj_mem_of_sup (P := A) (Q := Abar) hA hAb) hcAb
  exact hP y hy

theorem sa_mem_normalizer_Y (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s) :
    s ∈ normalizer (Section3.Y A Abar s : Set G) :=
  sa_mem_normalizer_of_forall fun _ hy => sa_conj_mem_Y h hs hy

theorem sa_conj_D (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s) {d : G}
    (hd : d ∈ Section4.D A Abar s) : s * d * s⁻¹ ∈ Section4.D A Abar s := by
  obtain ⟨y, hy, a, ha, haA₀, rfl⟩ := sec41_mem_D.mp hd
  refine sec41_mem_D.mpr ⟨s * y * s⁻¹, sa_conj_mem_Y h hs hy, a, ha, haA₀, ?_⟩
  have hsa : s * a * s⁻¹ = a := by rw [sa_comm_A h hs ha]; group
  calc s * (y * a * y⁻¹) * s⁻¹ = (s * y * s⁻¹) * (s * a * s⁻¹) * (s * y * s⁻¹)⁻¹ := by group
    _ = (s * y * s⁻¹) * a * (s * y * s⁻¹)⁻¹ := by rw [hsa]

theorem sa_exists_k (h : Sec3Ctx A Abar S₀ B) :
    ∃ k ∈ A ⊔ Abar, Abar = conjSubgroup k A ∧
      Section3.Abar0 A Abar = conjSubgroup k (Section3.A0 A Abar) := by
  obtain ⟨k, hk, hAk⟩ := h.setup.exists_conj_eq
  have hne : conjSubgroup k A ≠ A := by
    rw [← hAk]
    exact h.setup.Ab_ne
  refine ⟨k, hk, hAk, ?_⟩
  have h1 := (h.setup.setup_conj hk hne).hLb
  calc Section3.Abar0 A Abar = Abar ⊓ normalizer (A : Set G) := h.abar0_eq
    _ = conjSubgroup k A ⊓ normalizer (A : Set G) := by rw [← hAk]
    _ = conjSubgroup k (Section3.A0 A Abar) := h1.symm

theorem sa_centralizes_N (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    {g : G} (_hg : g ∈ normalizer (Section3.Y A Abar s : Set G))
    (hgA : g ∈ centralizer (Section3.A0 A Abar : Set G))
    (hgY : ∀ y ∈ Section3.Y A Abar s, g * y * g⁻¹ * y⁻¹ ∈ Section3.N A Abar s) :
    g ∈ centralizer (Section3.N A Abar s : Set G) := by
  obtain ⟨-, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  have hNc : ∀ x ∈ Section3.N A Abar s, ∀ w ∈ Section3.N A Abar s, x * w = w * x :=
    fun x hx w hw => congrArg Subtype.val (hNab.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)
  have key : ∀ y ∈ Section3.Y A Abar s, ∀ c ∈ Section3.A0 A Abar,
      g * (y * c * y⁻¹) = (y * c * y⁻¹) * g := by
    intro y hy c hc
    have hn := hgY y hy
    have hu : y * c * y⁻¹ ∈ Section3.N A Abar s :=
      (Subgroup.mem_normalizer_iff.mp (hYN y hy) c).mp (sa_A0_le_N hc)
    have hcg : g * c * g⁻¹ = c := by
      rw [← Subgroup.mem_centralizer_iff.mp hgA c hc]
      group
    have e1 : g * (y * c * y⁻¹) * g⁻¹ =
        (g * y * g⁻¹ * y⁻¹ * y) * c * (g * y * g⁻¹ * y⁻¹ * y)⁻¹ := by
      calc g * (y * c * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * (g * c * g⁻¹) * (g * y * g⁻¹)⁻¹ := by group
        _ = (g * y * g⁻¹ * y⁻¹ * y) * c * (g * y * g⁻¹ * y⁻¹ * y)⁻¹ := by rw [hcg]; group
    have e2 : g * (y * c * y⁻¹) * g⁻¹ = y * c * y⁻¹ := by
      rw [e1]
      calc (g * y * g⁻¹ * y⁻¹ * y) * c * (g * y * g⁻¹ * y⁻¹ * y)⁻¹
          = (g * y * g⁻¹ * y⁻¹) * (y * c * y⁻¹) * (g * y * g⁻¹ * y⁻¹)⁻¹ := by group
        _ = y * c * y⁻¹ := by rw [hNc _ hn _ hu, mul_inv_cancel_right]
    calc g * (y * c * y⁻¹) = (g * (y * c * y⁻¹) * g⁻¹) * g := by group
      _ = (y * c * y⁻¹) * g := by rw [e2]
  have hmem : ∀ K : Subgroup G, (∀ u ∈ K, g * u = u * g) → K ≤ centralizer ({g} : Set G) := by
    intro K hK u hu
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hK u hu
  obtain ⟨k, hk, -, hAbk⟩ := sa_exists_k h
  have hkY : k ∈ Section3.Y A Abar s := by
    have : A ⊔ Abar ≤ Section3.Y A Abar s := by
      unfold Section3.Y
      exact le_sup_left
    exact this hk
  have hsk : s * k * s⁻¹ ∈ Section3.Y A Abar s := sa_conj_mem_Y h hs hkY
  have h1 : Section3.A0 A Abar ≤ centralizer ({g} : Set G) := by
    refine hmem _ fun u hu => ?_
    have := key 1 (Subgroup.one_mem _) u hu
    simpa using this
  have h2 : Section3.Abar0 A Abar ≤ centralizer ({g} : Set G) := by
    refine hmem _ fun u hu => ?_
    rw [hAbk] at hu
    obtain ⟨c, hc, rfl⟩ : ∃ c ∈ Section3.A0 A Abar, u = k * c * k⁻¹ :=
      ⟨k⁻¹ * u * k, mem_conjSubgroup.mp hu, by group⟩
    exact key k hkY c hc
  have h3 : conjSubgroup s (Section3.Abar0 A Abar) ≤ centralizer ({g} : Set G) := by
    refine hmem _ fun u hu => ?_
    have hq : s⁻¹ * u * s ∈ Section3.Abar0 A Abar := mem_conjSubgroup.mp hu
    rw [hAbk] at hq
    obtain ⟨c, hc, hcq⟩ : ∃ c ∈ Section3.A0 A Abar, s⁻¹ * u * s = k * c * k⁻¹ :=
      ⟨k⁻¹ * (s⁻¹ * u * s) * k, mem_conjSubgroup.mp hq, by group⟩
    have hsc : s * c * s⁻¹ = c := by rw [sa_comm_A h hs (h.setup.L_le hc)]; group
    have hu' : u = (s * k * s⁻¹) * c * (s * k * s⁻¹)⁻¹ := by
      calc u = s * (s⁻¹ * u * s) * s⁻¹ := by group
        _ = s * (k * c * k⁻¹) * s⁻¹ := by rw [hcq]
        _ = (s * k * s⁻¹) * (s * c * s⁻¹) * (s * k * s⁻¹)⁻¹ := by group
        _ = (s * k * s⁻¹) * c * (s * k * s⁻¹)⁻¹ := by rw [hsc]
    rw [hu']
    exact key _ hsk c hc
  intro n hn
  have hN : Section3.N A Abar s ≤ centralizer ({g} : Set G) := by
    unfold Section3.N
    exact sup_le (sup_le h1 h2) h3
  have := Subgroup.mem_centralizer_iff.mp (hN hn) g (Set.mem_singleton g)
  exact this.symm

end SA

section SA5

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G} {s : G}

theorem sa_field_contra (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hne : conjSubgroup s Abar ≠ Abar) {h₀ : G} (hh₀ : h₀ ∈ Section3.Y A Abar s)
    (hsh : s * h₀ * s⁻¹ * h₀⁻¹ ∈ Section3.N A Abar s)
    (hnc : ¬ ∀ x ∈ A, ∀ w ∈ conjSubgroup h₀ A, x * w = w * x) : False := by
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  have hNc : ∀ x ∈ Section3.N A Abar s, ∀ w ∈ Section3.N A Abar s, x * w = w * x :=
    fun x hx w hw => congrArg Subtype.val (hNab.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)
  have hsA : ∀ a ∈ A, s * a * s⁻¹ = a := fun a ha => by rw [sa_comm_A h hs ha]; group
  have hsA0 : ∀ c ∈ Section3.A0 A Abar, s * c * s⁻¹ = c := fun c hc => hsA c (h.setup.L_le hc)
  have hnc' : ¬ ∀ x ∈ conjSubgroup 1 A, ∀ w ∈ conjSubgroup h₀ A, x * w = w * x := by
    rw [conjSubgroup_one]
    exact hnc
  have S12 := sec41_prop24 h hYN hNc (Subgroup.one_mem _) hh₀ hnc'
  rw [conjSubgroup_one, conjSubgroup_one] at S12
  have hT₀N : conjSubgroup h₀ (Section3.A0 A Abar) ≤ Section3.N A Abar s :=
    sec41_conj_le (hYN h₀ hh₀) sa_A0_le_N
  have hsT₀ : ∀ u ∈ conjSubgroup h₀ (Section3.A0 A Abar), s * u * s⁻¹ = u := by
    intro u hu
    obtain ⟨c, hc, rfl⟩ : ∃ c ∈ Section3.A0 A Abar, u = h₀ * c * h₀⁻¹ :=
      ⟨h₀⁻¹ * u * h₀, mem_conjSubgroup.mp hu, by group⟩
    obtain ⟨n, hn⟩ : ∃ n, n = s * h₀ * s⁻¹ * h₀⁻¹ := ⟨_, rfl⟩
    have hnN : n ∈ Section3.N A Abar s := hn ▸ hsh
    have hnh : n * h₀ = s * h₀ * s⁻¹ := by rw [hn]; group
    calc s * (h₀ * c * h₀⁻¹) * s⁻¹
        = (s * h₀ * s⁻¹) * (s * c * s⁻¹) * (s * h₀ * s⁻¹)⁻¹ := by group
      _ = (n * h₀) * c * (n * h₀)⁻¹ := by rw [hsA0 c hc, hnh]
      _ = n * (h₀ * c * h₀⁻¹) * n⁻¹ := by group
      _ = h₀ * c * h₀⁻¹ := by rw [hNc n hnN _ (hT₀N hu), mul_inv_cancel_right]
  have hFix : Section3.A0 A Abar ⊔ conjSubgroup h₀ (Section3.A0 A Abar) ≤
      centralizer ({s} : Set G) := by
    have hmem : ∀ K : Subgroup G, (∀ u ∈ K, s * u * s⁻¹ = u) → K ≤ centralizer ({s} : Set G) := by
      intro K hK u hu
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      have := hK u hu
      calc s * u = s * u * s⁻¹ * s := by group
        _ = u * s := by rw [this]
    exact sup_le (hmem _ hsA0) (hmem _ hsT₀)
  have hT : ∀ t ∈ Section3.A0 A Abar ⊔ conjSubgroup h₀ (Section3.A0 A Abar), s * t * s⁻¹ = t := by
    intro t ht
    have := Subgroup.mem_centralizer_iff.mp (hFix ht) s (Set.mem_singleton s)
    calc s * t * s⁻¹ = t * s * s⁻¹ := by rw [this]
      _ = t := by group
  have hQQ : Section3.Abar0 A Abar ⊓ conjSubgroup s (Section3.Abar0 A Abar) = ⊥ := by
    have h1 := inf_conjSubgroup_eq_bot_of_isTI h.setup.ti_Ab hne
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hx3 : x ∈ Abar ⊓ conjSubgroup s Abar :=
      ⟨h.setup.Lb_le hx1, mem_conjSubgroup.mpr (h.setup.Lb_le (mem_conjSubgroup.mp hx2))⟩
    rw [h1] at hx3
    exact hx3
  have hTc : Nat.card (Section3.A0 A Abar) ^ 2 ≤
      Nat.card (Section3.A0 A Abar ⊔ conjSubgroup h₀ (Section3.A0 A Abar) : Subgroup G) := by
    have hinf : Section3.A0 A Abar ⊓ conjSubgroup h₀ (Section3.A0 A Abar) = ⊥ := by
      refine eq_bot_iff.mpr fun x hx => ?_
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      have hx3 : x ∈ A ⊓ conjSubgroup h₀ A :=
        ⟨h.setup.L_le hx1, mem_conjSubgroup.mpr (h.setup.L_le (mem_conjSubgroup.mp hx2))⟩
      rw [S12.inf_eq_bot] at hx3
      exact hx3
    have := sa_card_mul_le_sup hinf
    rw [CFSG.RankThree.GF2n.card_conjSubgroup] at this
    rwa [sq]
  obtain ⟨hc3, hδ⟩ := sa_count (V := Section3.N A Abar s) (P := Section3.A0 A Abar)
    (Q := Section3.Abar0 A Abar) (T := Section3.A0 A Abar ⊔ conjSubgroup h₀ (Section3.A0 A Abar))
    (s := s) hNab (fun v hv => sa_conj_mem_N h hs hv) (sa_sq_mem_N h hs) sa_A0_le_N
    sa_Abar0_le_N (sup_le sa_A0_le_N hT₀N) (by unfold Section3.N; rfl) hsA0 hQQ
    h.setup.card_Lb_eq hT hTc
  have hcA : ∀ y ∈ Section3.Abar0 A Abar, ∀ a ∈ A,
      a * (y * (s * y * s⁻¹)) = (y * (s * y * s⁻¹)) * a := by
    intro y hy a ha
    obtain ⟨c, hc⟩ : ∃ c, c = a * y * a⁻¹ * y⁻¹ := ⟨_, rfl⟩
    have hcA₀ : c ∈ Section3.A0 A Abar := hc ▸ h.setup.commutator_mem_L ha hy
    have hcc : c * c = 1 := h.setup.sq_A (h.setup.L_le hcA₀)
    have hcy : c * y = y * c := hNc c (sa_A0_le_N hcA₀) y (sa_Abar0_le_N hy)
    have hay : a * y * a⁻¹ = c * y := by rw [hc]; group
    have hsa := hsA a ha
    have hsa' := hsA a⁻¹ (A.inv_mem ha)
    have has : a * (s * y * s⁻¹) * a⁻¹ = c * (s * y * s⁻¹) := by
      calc a * (s * y * s⁻¹) * a⁻¹
          = (s * a * s⁻¹) * (s * y * s⁻¹) * (s * a⁻¹ * s⁻¹) := by rw [hsa, hsa']
        _ = s * (a * y * a⁻¹) * s⁻¹ := by group
        _ = s * (c * y) * s⁻¹ := by rw [hay]
        _ = (s * c * s⁻¹) * (s * y * s⁻¹) := by group
        _ = c * (s * y * s⁻¹) := by rw [hsA0 c hcA₀]
    have e : a * (y * (s * y * s⁻¹)) * a⁻¹ = y * (s * y * s⁻¹) := by
      calc a * (y * (s * y * s⁻¹)) * a⁻¹ = (a * y * a⁻¹) * (a * (s * y * s⁻¹) * a⁻¹) := by group
        _ = (c * y) * (c * (s * y * s⁻¹)) := by rw [hay, has]
        _ = c * (y * c) * (s * y * s⁻¹) := by group
        _ = c * (c * y) * (s * y * s⁻¹) := by rw [← hcy]
        _ = (c * c) * y * (s * y * s⁻¹) := by group
        _ = y * (s * y * s⁻¹) := by rw [hcc, one_mul]
    calc a * (y * (s * y * s⁻¹)) = (a * (y * (s * y * s⁻¹)) * a⁻¹) * a := by group
      _ = (y * (s * y * s⁻¹)) * a := by rw [e]
  obtain ⟨t, htA, htL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h.setup.L_le h.setup.ne)
  have hyA₀ : ∀ y ∈ Section3.Abar0 A Abar, y * (s * y * s⁻¹) ∈ Section3.A0 A Abar := by
    intro y hy
    have hm : y * (s * y * s⁻¹) ∈
        Section3.A0 A Abar ⊔ conjSubgroup h₀ (Section3.A0 A Abar) := hδ y hy
    have hM : y * (s * y * s⁻¹) ∈
        Section3.A0 A Abar ⊔ conjSubgroup h₀ (Section3.A0 A Abar) := hm
    exact S12.mem_L_of_commute_M htA htL hM (hcA y hy t htA)
  have hsle : conjSubgroup s (Section3.Abar0 A Abar) ≤
      Section3.A0 A Abar ⊔ Section3.Abar0 A Abar := by
    intro z hz
    have hy : s⁻¹ * z * s ∈ Section3.Abar0 A Abar := mem_conjSubgroup.mp hz
    have hm := hyA₀ _ hy
    rw [show s * (s⁻¹ * z * s) * s⁻¹ = z by group] at hm
    have key : (s⁻¹ * z * s)⁻¹ * ((s⁻¹ * z * s) * z) ∈
        Section3.Abar0 A Abar ⊔ Section3.A0 A Abar :=
      Subgroup.mul_mem_sup ((Section3.Abar0 A Abar).inv_mem hy) hm
    rw [inv_mul_cancel_left] at key
    rw [sup_comm]
    exact key
  have hN_le : Section3.N A Abar s ≤ Section3.A0 A Abar ⊔ Section3.Abar0 A Abar := by
    unfold Section3.N
    exact sup_le le_rfl hsle
  have hcard : Nat.card (Section3.N A Abar s) ≤ Nat.card (Section3.A0 A Abar) ^ 2 := by
    calc Nat.card (Section3.N A Abar s)
        ≤ Nat.card (Section3.A0 A Abar ⊔ Section3.Abar0 A Abar : Subgroup G) :=
          Subgroup.card_le_of_le hN_le
      _ ≤ Nat.card (Section3.A0 A Abar) * Nat.card (Section3.Abar0 A Abar) :=
          sa_card_sup_le fun x hx y hy => hNc x (sa_A0_le_N hx) y (sa_Abar0_le_N hy)
      _ = Nat.card (Section3.A0 A Abar) ^ 2 := by rw [h.setup.card_Lb_eq, sq]
  have hc1 : 1 < Nat.card (Section3.A0 A Abar) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr h.a0_ne_bot
  have h32 := hc3.trans hcard
  have h23 : Nat.card (Section3.A0 A Abar) ^ 2 < Nat.card (Section3.A0 A Abar) ^ 3 :=
    Nat.pow_lt_pow_right hc1 (by norm_num)
  omega

end SA5

section SA6

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G} {s : G}

theorem sa_phi (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    [((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal] :
    ∃ φ : MulAut (↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)),
      φ * φ = 1 ∧
      ∀ (y : ↥(Section3.Y A Abar s)) (hy : s * (y : G) * s⁻¹ ∈ Section3.Y A Abar s),
        φ (QuotientGroup.mk y) = QuotientGroup.mk ⟨s * y * s⁻¹, hy⟩ := by
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  have hss := sa_sq_mem_N h hs
  let ψ : MulAut ↥(Section3.Y A Abar s) :=
    (Section3.Y A Abar s).normalizerMonoidHom ⟨s, sa_mem_normalizer_Y h hs⟩
  have hψ : ∀ y : ↥(Section3.Y A Abar s), (ψ y : G) = s * y * s⁻¹ := fun y => rfl
  have hle : ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).map (ψ : _ →* _) ≤
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    show ((ψ x : ↥(Section3.Y A Abar s)) : G) ∈ Section3.N A Abar s
    rw [hψ]
    exact sa_conj_mem_N h hs hx
  have hmap : ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).map (ψ : _ →* _) =
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s) :=
    Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective ψ.injective).ge
  let φ := QuotientGroup.congr ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))
    ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ψ hmap
  have hφ : ∀ y : ↥(Section3.Y A Abar s), φ (QuotientGroup.mk y) = QuotientGroup.mk (ψ y) :=
    fun y => rfl
  refine ⟨φ, ?_, ?_⟩
  · refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.mul_apply, hφ, hφ, MulAut.one_apply]
    refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    have e : (((ψ (ψ y))⁻¹ * y : ↥(Section3.Y A Abar s)) : G) =
        (s * s) * ((y : G)⁻¹ * (s * s)⁻¹ * y) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψ, mul_inv_rev, inv_inv, mul_assoc]
    rw [e]
    refine (Section3.N A Abar s).mul_mem hss ?_
    have := (Subgroup.mem_normalizer_iff.mp (hYN _ (y⁻¹).2) ((s * s)⁻¹)).mp
      ((Section3.N A Abar s).inv_mem hss)
    simpa using this
  · intro y hy
    rfl

theorem sa_lift_fixed (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    [((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal]
    (φ : MulAut (↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)))
    (hφ : ∀ (y : ↥(Section3.Y A Abar s)) (hy : s * (y : G) * s⁻¹ ∈ Section3.Y A Abar s),
      φ (QuotientGroup.mk y) = QuotientGroup.mk ⟨s * y * s⁻¹, hy⟩)
    {x : ↥(Section3.Y A Abar s) ⧸ (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)}
    (hx : φ x = x) :
    ∃ y : ↥(Section3.Y A Abar s), QuotientGroup.mk y = x ∧
      s * (y : G) * s⁻¹ * (y : G)⁻¹ ∈ Section3.N A Abar s := by
  obtain ⟨-, hYN, -⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨y, rfl, ?_⟩
  have hy := sa_conj_mem_Y h hs y.2
  rw [hφ y hy] at hx
  have h1 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hx)
  have hn : (s * (y : G) * s⁻¹)⁻¹ * y ∈ Section3.N A Abar s := by simpa using h1
  have hconj := (Subgroup.mem_normalizer_iff.mp (hYN y y.2) _).mp
    ((Section3.N A Abar s).inv_mem hn)
  have e : s * (y : G) * s⁻¹ * (y : G)⁻¹ =
      (y : G) * ((s * (y : G) * s⁻¹)⁻¹ * y)⁻¹ * (y : G)⁻¹ := by
    group
  rw [e]
  exact hconj

end SA6

section SA7

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G} {s : G}

theorem sa_mul_mem_of_index_two {T T₀ : Subgroup G} (hidx : T₀.relIndex T = 2) {x t : G}
    (hx : x ∈ T) (ht : t ∈ T) (hxN : x ∉ T₀) (htN : t ∉ T₀) : x * t ∈ T₀ := by
  have h := (Subgroup.mul_mem_iff_of_index_two (H := T₀.subgroupOf T) hidx
    (a := (⟨x, hx⟩ : ↥T)) (b := ⟨t, ht⟩)).mpr
    ⟨fun h => absurd (Subgroup.mem_subgroupOf.mp h) hxN,
      fun h => absurd (Subgroup.mem_subgroupOf.mp h) htN⟩
  exact Subgroup.mem_subgroupOf.mp h

theorem sa_closure_top (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hq : Section3.q A Abar = 2)
    [((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal]
    {a β γ : ↥(Section3.Y A Abar s)} (haA : (a : G) ∈ A) (haN : (a : G) ∉ Section3.A0 A Abar)
    (hβA : (β : G) ∈ Abar) (hβN : (β : G) ∉ Section3.Abar0 A Abar)
    (hγ : (γ : G) = s * β * s⁻¹) :
    Subgroup.closure ({QuotientGroup.mk a, QuotientGroup.mk β, QuotientGroup.mk γ} :
      Set (↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))) = ⊤ := by
  have hqAb : (Section3.Abar0 A Abar).relIndex Abar = 2 := by
    unfold Section3.q at hq
    exact hq
  have hqA : (Section3.A0 A Abar).relIndex A = 2 := by
    rw [← h.setup.relIndex_Lb]
    exact hqAb
  set K := (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s) with hK
  set Cl := Subgroup.closure ({QuotientGroup.mk a, QuotientGroup.mk β, QuotientGroup.mk γ} :
    Set (↥(Section3.Y A Abar s) ⧸ K)) with hCl
  have hNmk : ∀ x : ↥(Section3.Y A Abar s), (x : G) ∈ Section3.N A Abar s →
      (QuotientGroup.mk x : ↥(Section3.Y A Abar s) ⧸ K) = 1 := fun x hx =>
    (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr hx)
  have hma : (QuotientGroup.mk a : ↥(Section3.Y A Abar s) ⧸ K) ∈ Cl :=
    Subgroup.subset_closure (by simp)
  have hmβ : (QuotientGroup.mk β : ↥(Section3.Y A Abar s) ⧸ K) ∈ Cl :=
    Subgroup.subset_closure (by simp)
  have hmγ : (QuotientGroup.mk γ : ↥(Section3.Y A Abar s) ⧸ K) ∈ Cl :=
    Subgroup.subset_closure (by simp)
  have hinv : ∀ x t : ↥(Section3.Y A Abar s),
      (QuotientGroup.mk t : ↥(Section3.Y A Abar s) ⧸ K) ∈ Cl →
      (x : G) * t ∈ Section3.N A Abar s →
      (QuotientGroup.mk x : ↥(Section3.Y A Abar s) ⧸ K) ∈ Cl := by
    intro x t ht hxt
    have h1 : (QuotientGroup.mk x : ↥(Section3.Y A Abar s) ⧸ K) * QuotientGroup.mk t = 1 := by
      rw [← QuotientGroup.mk_mul]
      exact hNmk (x * t) hxt
    rw [eq_inv_of_mul_eq_one_left h1]
    exact Cl.inv_mem ht
  let P : Subgroup ↥(Section3.Y A Abar s) := Cl.comap (QuotientGroup.mk' K)
  have hAle : A ≤ P.map (Section3.Y A Abar s).subtype := by
    intro x hx
    refine ⟨⟨x, sa_A_le_Y hx⟩, ?_, rfl⟩
    show (QuotientGroup.mk ⟨x, sa_A_le_Y hx⟩ : ↥(Section3.Y A Abar s) ⧸ K) ∈ Cl
    by_cases hx0 : x ∈ Section3.A0 A Abar
    · rw [hNmk _ (sa_A0_le_N hx0)]
      exact Cl.one_mem
    · exact hinv _ a hma (sa_A0_le_N (sa_mul_mem_of_index_two hqA hx haA hx0 haN))
  have hAble : Abar ≤ P.map (Section3.Y A Abar s).subtype := by
    intro x hx
    refine ⟨⟨x, sa_Abar_le_Y hx⟩, ?_, rfl⟩
    show (QuotientGroup.mk ⟨x, sa_Abar_le_Y hx⟩ : ↥(Section3.Y A Abar s) ⧸ K) ∈ Cl
    by_cases hx0 : x ∈ Section3.Abar0 A Abar
    · rw [hNmk _ (sa_Abar0_le_N hx0)]
      exact Cl.one_mem
    · exact hinv _ β hmβ (sa_Abar0_le_N (sa_mul_mem_of_index_two hqAb hx hβA hx0 hβN))
  have hAsle : conjSubgroup s Abar ≤ P.map (Section3.Y A Abar s).subtype := by
    intro z hz
    refine ⟨⟨z, sa_conj_Abar_le_Y hz⟩, ?_, rfl⟩
    show (QuotientGroup.mk ⟨z, sa_conj_Abar_le_Y hz⟩ : ↥(Section3.Y A Abar s) ⧸ K) ∈ Cl
    have hw : s⁻¹ * z * s ∈ Abar := mem_conjSubgroup.mp hz
    by_cases hw0 : s⁻¹ * z * s ∈ Section3.Abar0 A Abar
    · rw [hNmk _ (sa_conj_Abar0_le_N (mem_conjSubgroup.mpr hw0))]
      exact Cl.one_mem
    · refine hinv _ γ hmγ (sa_conj_Abar0_le_N (mem_conjSubgroup.mpr ?_))
      have := sa_mul_mem_of_index_two hqAb hw hβA hw0 hβN
      rw [hγ]
      simpa [mul_assoc] using this
  have hYle : Section3.Y A Abar s ≤ P.map (Section3.Y A Abar s).subtype := by
    unfold Section3.Y
    exact sup_le (sup_le hAle hAble) hAsle
  rw [eq_top_iff]
  intro r _
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective r
  obtain ⟨y', hy', hyy⟩ := hYle y.2
  have : y' = y := Subtype.ext hyy
  subst this
  exact hy'

theorem sa_aut_eq_one (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hq : Section3.q A Abar = 2)
    [((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal]
    {a β γ : ↥(Section3.Y A Abar s)} (haA : (a : G) ∈ A) (haN : (a : G) ∉ Section3.A0 A Abar)
    (hβA : (β : G) ∈ Abar) (hβN : (β : G) ∉ Section3.Abar0 A Abar)
    (hγ : (γ : G) = s * β * s⁻¹)
    (ψ : MulAut (↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)))
    (h1 : ψ (QuotientGroup.mk a) = QuotientGroup.mk a)
    (h2 : ψ (QuotientGroup.mk β) = QuotientGroup.mk β)
    (h3 : ψ (QuotientGroup.mk γ) = QuotientGroup.mk γ) : ψ = 1 := by
  have hcl := sa_closure_top h hs hq haA haN hβA hβN hγ
  have key : ∀ x : ↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s), ψ x = x := by
    intro x
    have hx : x ∈ Subgroup.closure ({QuotientGroup.mk a, QuotientGroup.mk β,
        QuotientGroup.mk γ} : Set (↥(Section3.Y A Abar s) ⧸
          (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))) := by
      rw [hcl]
      exact Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
    | one => exact map_one ψ
    | mul a b _ _ iha ihb => rw [map_mul, iha, ihb]
    | inv a _ iha => rw [map_inv, iha]
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.one_apply]
  exact key x

theorem sa_Y_eq_X_of_comm (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    {a : G} (ha : a ∈ A)
    (hgY : ∀ y ∈ Section3.Y A Abar s,
      (a * s) * y * (a * s)⁻¹ * y⁻¹ ∈ Section3.N A Abar s) :
    Section3.Y A Abar s = Section3.X A Abar := by
  have hg : a * s ∈ normalizer (Section3.Y A Abar s : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer (sa_A_le_Y ha)) (sa_mem_normalizer_Y h hs)
  have hgA : a * s ∈ centralizer (Section3.A0 A Abar : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcA := h.setup.L_le hc
    calc c * (a * s) = (c * a) * s := by group
      _ = (a * c) * s := by rw [h.setup.comm_A hcA ha]
      _ = a * (c * s) := by group
      _ = a * (s * c) := by rw [← sa_comm_A h hs hcA]
      _ = (a * s) * c := by group
  have hgN := sa_centralizes_N h hs hg hgA hgY
  obtain ⟨x₀, hx₀, hx₀1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot h.setup.Lb_ne_bot
  have hcomm : (a * s) * x₀ = x₀ * (a * s) :=
    (Subgroup.mem_centralizer_iff.mp hgN x₀ (sa_Abar0_le_N hx₀)).symm
  have hgAb : a * s ∈ normalizer (Abar : Set G) :=
    mem_normalizer_of_commute_of_isTI h.setup.ti_Ab (h.setup.Lb_le hx₀) hx₀1 hcomm
  have hconj : conjSubgroup s Abar ≤ A ⊔ Abar := by
    have e : conjSubgroup s Abar = conjSubgroup a⁻¹ Abar := by
      calc conjSubgroup s Abar = conjSubgroup (a⁻¹ * (a * s)) Abar := by rw [inv_mul_cancel_left]
        _ = conjSubgroup a⁻¹ (conjSubgroup (a * s) Abar) := conjSubgroup_mul _ _ _
        _ = conjSubgroup a⁻¹ Abar := by rw [conjSubgroup_eq_self_iff.mpr hgAb]
    rw [e]
    intro z hz
    have hz' : a * z * a⁻¹ ∈ Abar := by
      have := mem_conjSubgroup.mp hz
      simpa using this
    have e2 : z = a⁻¹ * (a * z * a⁻¹) * a := by group
    rw [e2]
    exact (A ⊔ Abar).mul_mem ((A ⊔ Abar).mul_mem ((A ⊔ Abar).inv_mem (Subgroup.mem_sup_left ha))
      (Subgroup.mem_sup_right hz')) (Subgroup.mem_sup_left ha)
  refine le_antisymm ?_ ?_
  · unfold Section3.Y Section3.X
    exact sup_le le_rfl hconj
  · unfold Section3.Y Section3.X
    exact le_sup_left

end SA7

section SA9

theorem sa_odd_card_fusionOddCore (Q : Type) [Group Q] [Finite Q] :
    Odd (Nat.card (fusionOddCore Q)) := by
  have h : fusionOddCore Q = CFSG.pPrimeCore 2 Q := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := Q))

theorem sa_eq_one_of_mem_oddCore {Q : Type} [Group Q] [Finite Q] {q : Q}
    (hq : q ∈ fusionOddCore Q) (h2 : q * q = 1) : q = 1 := by
  have hodd : Odd (Nat.card (fusionOddCore Q)) := sa_odd_card_fusionOddCore Q
  have hdvd1 : orderOf (⟨q, hq⟩ : fusionOddCore Q) ∣ Nat.card (fusionOddCore Q) :=
    orderOf_dvd_natCard _
  have hdvd2 : orderOf (⟨q, hq⟩ : fusionOddCore Q) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [pow_two, h2]))
  have h1 : orderOf (⟨q, hq⟩ : fusionOddCore Q) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hodd) hdvd2 hdvd1
  have := congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  simpa using this

theorem sa_mul_mem_of_conj {R : Type} [Group R] [Finite R] (O : Subgroup R) [O.Normal]
    (hcent : ∀ q : R ⧸ O, QuotientGroup.mk' (fusionOddCore (R ⧸ O)) q ∈
      Subgroup.center ((R ⧸ O) ⧸ fusionOddCore (R ⧸ O)))
    {d e : R} (hd2 : d * d = 1) (he2 : e * e = 1) (hed : e * d = d * e) {y : R}
    (hy : y * d * y⁻¹ = e) : d * e ∈ O := by
  have hF : ∀ a g : R, QuotientGroup.mk' (fusionOddCore (R ⧸ O))
      (QuotientGroup.mk' O (a * g * a⁻¹)) =
        QuotientGroup.mk' (fusionOddCore (R ⧸ O)) (QuotientGroup.mk' O g) := by
    intro a g
    have hc := Subgroup.mem_center_iff.mp (hcent (QuotientGroup.mk' O a))
      (QuotientGroup.mk' (fusionOddCore (R ⧸ O)) (QuotientGroup.mk' O g))
    simp only [map_mul, map_inv]
    rw [← hc, mul_inv_cancel_right]
  have h1 : QuotientGroup.mk' (fusionOddCore (R ⧸ O)) (QuotientGroup.mk' O e) =
      QuotientGroup.mk' (fusionOddCore (R ⧸ O)) (QuotientGroup.mk' O d) := by
    rw [← hy]
    exact hF y d
  have hψ : QuotientGroup.mk' (fusionOddCore (R ⧸ O)) (QuotientGroup.mk' O (d * e)) = 1 := by
    calc QuotientGroup.mk' (fusionOddCore (R ⧸ O)) (QuotientGroup.mk' O (d * e))
        = QuotientGroup.mk' (fusionOddCore (R ⧸ O)) (QuotientGroup.mk' O d) *
            QuotientGroup.mk' (fusionOddCore (R ⧸ O)) (QuotientGroup.mk' O e) := by
          simp only [map_mul]
      _ = QuotientGroup.mk' (fusionOddCore (R ⧸ O)) (QuotientGroup.mk' O d) *
            QuotientGroup.mk' (fusionOddCore (R ⧸ O)) (QuotientGroup.mk' O d) := by
          rw [h1]
      _ = QuotientGroup.mk' (fusionOddCore (R ⧸ O)) (QuotientGroup.mk' O (d * d)) := by
          simp only [map_mul]
      _ = 1 := by simp [hd2]
  have hprod : d * e * (d * e) = 1 := by
    calc d * e * (d * e) = d * (e * d) * e := by simp only [mul_assoc]
      _ = d * (d * e) * e := by rw [hed]
      _ = d * d * (e * e) := by simp only [mul_assoc]
      _ = 1 := by rw [hd2, he2, one_mul]
  have hmem : QuotientGroup.mk' O (d * e) ∈ fusionOddCore (R ⧸ O) :=
    (QuotientGroup.eq_one_iff (QuotientGroup.mk' O (d * e))).mp hψ
  have hsq : QuotientGroup.mk' O (d * e) * QuotientGroup.mk' O (d * e) = 1 := by
    rw [← map_mul, hprod, map_one]
  have h1' : QuotientGroup.mk' O (d * e) = 1 := sa_eq_one_of_mem_oddCore hmem hsq
  exact (QuotientGroup.eq_one_iff (d * e)).mp h1'

theorem sa_eq_of_commute {R : Type} [Group R] [Finite R] {D : Set R}
    (hS : CFSG.Timmesfeld.Bridge.Asc72.Setup R D) (hsolv : Group.IsSolvable R)
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d}))
    (hO2 : CFSG.pCore 2 R ≤ Subgroup.center R)
    (hinj : ∀ d ∈ D, ∀ z ∈ Subgroup.center R, z ≠ 1 → d * z ∉ D)
    {d e : R} (hd : d ∈ D) (he : e ∈ D) (hde : Commute d e) : d = e := by
  haveI : (CFSG.pCore 2 R).Normal := CFSG.pCore_normal
  have hRI : CFSG.Timmesfeld.IsRootInvolutionSet D := by
    refine ⟨hS.oddT.1, fun x hx y hy => ?_, fun x hx y hy h4 => ?_⟩
    · rcases hS.oddT.2 x hx y hy with h2 | hodd
      · rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
        · exact Or.inr (Or.inr (h1 ▸ odd_one))
        · exact Or.inl h1
      · exact Or.inr (Or.inr hodd)
    · exfalso
      rcases hS.oddT.2 x hx y hy with h2 | hodd
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
      · rw [h4] at hodd
        exact absurd hodd (by decide)
  have hZ : ZStarCase (R ⧸ CFSG.pCore 2 R) :=
    tim77Lemma21_holds R D hRI hS.isClass hS.gen hsolv fun d hd => (hE d hd).1
  have hcent : ∀ q : R ⧸ CFSG.pCore 2 R,
      QuotientGroup.mk' (fusionOddCore (R ⧸ CFSG.pCore 2 R)) q ∈
        Subgroup.center ((R ⧸ CFSG.pCore 2 R) ⧸ fusionOddCore (R ⧸ CFSG.pCore 2 R)) := by
    intro q
    have hq : q ∈ fusionZStar (R ⧸ CFSG.pCore 2 R) := by
      rw [show fusionZStar (R ⧸ CFSG.pCore 2 R) = ⊤ from hZ]
      exact Subgroup.mem_top q
    exact hq
  obtain ⟨y, hy⟩ := isConj_iff.mp (hS.isConj hd he)
  have hdd : d * d = 1 := hS.oddT.mul_self_eq_one hd
  have hee : e * e = 1 := hS.oddT.mul_self_eq_one he
  have hO : d * e ∈ CFSG.pCore 2 R :=
    sa_mul_mem_of_conj (CFSG.pCore 2 R) hcent hdd hee hde.symm.eq hy
  by_cases hz1 : d * e = 1
  · exact hS.oddT.eq_of_mul_eq_one hd hz1
  · exfalso
    have he' : d * (d * e) ∈ D := by
      rw [← mul_assoc, hdd, one_mul]
      exact he
    exact hinj d hd (d * e) (hO2 hO) hz1 he'

theorem sa_dichotomy {R : Type} [Group R] [Finite R] {D : Set R}
    (hS : CFSG.Timmesfeld.Bridge.Asc72.Setup R D) (hsolv : Group.IsSolvable R)
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d}))
    (hO2 : CFSG.pCore 2 R ≤ Subgroup.center R)
    (hinj : ∀ d ∈ D, ∀ z ∈ Subgroup.center R, z ≠ 1 → d * z ∉ D)
    (φ : MulAut R) (hφφ : φ * φ = 1) {a β : R} (ha : a ∈ D) (hβ : β ∈ D) (hγ : φ β ∈ D)
    (hφa : φ a = a)
    (hgen : ∀ ψ : MulAut R, ψ a = a → ψ β = β → ψ (φ β) = φ β → ψ = 1) :
    (∀ x : R, φ x = a⁻¹ * x * a) ∨ ∃ ρ ∈ D, φ ρ = ρ ∧ ¬ Commute a (ρ * a * ρ⁻¹) := by
  have hcomm_eq : ∀ d ∈ D, ∀ e ∈ D, Commute d e → d = e :=
    fun d hd e he hc => sa_eq_of_commute hS hsolv hE hO2 hinj hd he hc
  have haa : a * a = 1 := hS.oddT.mul_self_eq_one ha
  have hββ : β * β = 1 := hS.oddT.mul_self_eq_one hβ
  have hγγ : φ β * φ β = 1 := hS.oddT.mul_self_eq_one hγ
  have hodd : Odd (orderOf (β * φ β)) := by
    rcases hS.oddT.commute_or_odd hβ hγ with hc | hodd
    · have := hcomm_eq _ hβ _ hγ hc
      rw [← this, hββ, orderOf_one]
      exact odd_one
    · exact hodd
  obtain ⟨ρ, -, hρρ, hρβρ, hφρ, g, hg, hρg⟩ :=
    dih_fixed_reflection hββ hγγ hodd φ hφφ rfl
  have hρD : ρ ∈ D := by
    rw [hρg]
    exact hS.conj_mem g hβ
  have hρρ' : ρ * ρ = 1 := hρρ
  have hρi : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρρ'
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  by_cases hρa : ρ = a
  · left
    have hρβρ' : a * β * a = φ β := hρa ▸ hρβρ
    have hφφβ : φ (φ β) = β := by
      have := congrArg (fun ψ : MulAut R => ψ β) hφφ
      simpa [MulAut.mul_apply] using this
    have hψ : (MulAut.conj a * φ) = 1 := by
      refine hgen _ ?_ ?_ ?_
      · rw [MulAut.mul_apply, hφa, MulAut.conj_apply, mul_inv_cancel_right]
      · rw [MulAut.mul_apply, MulAut.conj_apply, ← hρβρ']
        calc a * (a * β * a) * a⁻¹ = (a * a) * β * (a * a⁻¹) := by group
          _ = β := by rw [haa, one_mul, mul_inv_cancel, mul_one]
      · rw [MulAut.mul_apply, MulAut.conj_apply, hφφβ, ← hρβρ', hai]
    intro x
    have h1 := congrArg (fun ψ : MulAut R => ψ x) hψ
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h1
    calc φ x = a⁻¹ * (a * φ x * a⁻¹) * a := by group
      _ = a⁻¹ * x * a := by rw [h1]
  · right
    refine ⟨ρ, hρD, hφρ, fun hc => ?_⟩
    have hnc : ¬ Commute a ρ := fun hc' => hρa (hcomm_eq _ hρD _ ha hc'.symm)
    have hodd' : Odd (orderOf (a * ρ)) := hS.oddT.odd_of_not_commute ha hρD hnc
    rw [hρi] at hc
    have hvv : (ρ * a * ρ) * (ρ * a * ρ) = 1 := by
      calc (ρ * a * ρ) * (ρ * a * ρ) = ρ * a * (ρ * ρ) * a * ρ := by group
        _ = ρ * (a * a) * ρ := by rw [hρρ', mul_one]; group
        _ = 1 := by rw [haa, mul_one, hρρ']
    have h4 := (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one haa hvv).mp hc
    have h4' : (a * ρ) ^ 4 = 1 := by
      have e1 : a * (ρ * a * ρ) = (a * ρ) ^ 2 := by
        rw [sq]
        group
      rw [e1, ← pow_mul] at h4
      exact h4
    have hdvd : orderOf (a * ρ) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h4')
    have h1 : orderOf (a * ρ) = 1 := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rcases i with _ | i
      · simpa using hi
      · rw [hi, pow_succ] at hodd'
        exact absurd hodd' (by simp [Nat.not_odd_iff_even])
    rw [orderOf_eq_one_iff] at h1
    exact hnc (hS.oddT.eq_of_mul_eq_one ha h1 ▸ Commute.refl a)

end SA9

end CFSG.RankThree.GF2n.Tim77
