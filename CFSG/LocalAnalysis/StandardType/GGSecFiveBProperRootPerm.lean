module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly
open SpCoord Multiplicative

open scoped BigOperators

private lemma congr_apply_eta {G : Type} [Group G] {p n : ℕ} {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (τ : MulAut ↥Bs) (b : ↥Bs) :
    MulAut.congr eta τ (eta b) = eta (τ b) := by
  rw [MulAut.congr_apply]
  simp

private lemma card_fix_congr {G : Type} [Group G] {p n : ℕ} {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (τ : MulAut ↥Bs) :
    Nat.card {f : Fin n → Multiplicative (ZMod p) // MulAut.congr eta τ f = f} =
      Nat.card {b : ↥Bs // τ b = b} := by
  let e : {b : ↥Bs // τ b = b} ≃
      {f : Fin n → Multiplicative (ZMod p) // MulAut.congr eta τ f = f} :=
    { toFun := fun x => ⟨eta x.1, by rw [congr_apply_eta eta τ x.1, x.2]⟩
      invFun := fun x => ⟨eta.symm x.1, by
        apply eta.injective
        rw [← congr_apply_eta eta τ (eta.symm x.1)]
        simpa using x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  exact Nat.card_congr e.symm

private lemma prod_mulSingle_coord {n p : ℕ} (i : Fin n) (x : Multiplicative (ZMod p)) :
    ∏ k, (Pi.mulSingle i x : Fin n → Multiplicative (ZMod p)) k = x := by
  simp

private lemma prod_eq_of_mem_aPermutationFull {n p : ℕ}
    (u : MulAut (Fin n → Multiplicative (ZMod p))) (hu : u ∈ aPermutationFull n p) :
    ∀ f : Fin n → Multiplicative (ZMod p), ∏ k, u f k = ∏ k, f k := by
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
      intro f
      obtain ⟨a, b, _, rfl⟩ := hu
      simpa only [permAut_apply, Function.comp_apply] using
        Equiv.prod_comp (Equiv.swap a b)⁻¹ f
  | one =>
      intro f
      simp
  | mul u v _ _ ihu ihv =>
      intro f
      rw [MulAut.mul_apply, ihu (v f), ihv f]
  | inv u _ ihu =>
      intro f
      have h := ihu (u⁻¹ f)
      rw [MulAut.apply_inv_self] at h
      exact h.symm

private lemma prod_sgnAut_mulSingle_self {n p : ℕ} (i : Fin n) :
    ∏ k, sgnAut i (Pi.mulSingle i (ofAdd (1 : ZMod p))) k = ofAdd (-1) := by
  rw [sgnAut_mulSingle_self, ← Pi.mulSingle_inv, prod_mulSingle_coord, ← ofAdd_neg]

private lemma negTrans_mulSingle_self {n p : ℕ} (a b : Fin n) (hab : a ≠ b) :
    ((sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ :
        MulAut (Fin n → Multiplicative (ZMod p)))
        (Pi.mulSingle a (ofAdd (1 : ZMod p)))) =
      Pi.mulSingle b (ofAdd (-1 : ZMod p)) := by
  funext k
  rw [negTrans_apply a b hab]
  by_cases hka : k = a
  · rw [if_pos hka, hka, Pi.mulSingle_eq_of_ne (Ne.symm hab), Pi.mulSingle_eq_of_ne hab]
    simp
  · rw [if_neg hka]
    by_cases hkb : k = b
    · rw [if_pos hkb, hkb, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, ← ofAdd_neg]
    · rw [if_neg hkb, Pi.mulSingle_eq_of_ne hka, Pi.mulSingle_eq_of_ne hkb]

private lemma prod_negTrans_mulSingle_self {n p : ℕ} (a b : Fin n) (hab : a ≠ b) :
    ∏ k, ((sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ :
        MulAut (Fin n → Multiplicative (ZMod p)))
      (Pi.mulSingle a (ofAdd (1 : ZMod p)))) k = ofAdd (-1) := by
  rw [negTrans_mulSingle_self a b hab, prod_mulSingle_coord]

private lemma ofAdd_neg_one_ne_ofAdd_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (ofAdd (-1 : ZMod p) : Multiplicative (ZMod p)) ≠ ofAdd (1 : ZMod p) := by
  have h2 : 2 < p := by
    have := hp.two_le
    omega
  intro h
  exact @ZMod.neg_one_ne_one p ⟨h2⟩ (by simpa using congrArg Multiplicative.toAdd h)

private lemma prod_sgnAut_mulSingle_ne {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i : Fin n) :
    ∏ k, sgnAut i (Pi.mulSingle i (ofAdd (1 : ZMod p))) k ≠
      ∏ k, (Pi.mulSingle i (ofAdd (1 : ZMod p)) : Fin n → Multiplicative (ZMod p)) k := by
  rw [prod_sgnAut_mulSingle_self, prod_mulSingle_coord]
  exact ofAdd_neg_one_ne_ofAdd_one hp hp2

private lemma prod_negTrans_mulSingle_ne {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a b : Fin n)
    (hab : a ≠ b) :
    ∏ k, ((sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ :
        MulAut (Fin n → Multiplicative (ZMod p)))
      (Pi.mulSingle a (ofAdd (1 : ZMod p)))) k ≠
      ∏ k, (Pi.mulSingle a (ofAdd (1 : ZMod p)) : Fin n → Multiplicative (ZMod p)) k := by
  rw [prod_negTrans_mulSingle_self a b hab, prod_mulSingle_coord]
  exact ofAdd_neg_one_ne_ofAdd_one hp hp2

private lemma permAut_swap_eq_self_iff {n p : ℕ} {a b : Fin n} (hab : a ≠ b)
    (f : Fin n → Multiplicative (ZMod p)) :
    permAut (Equiv.swap a b) f = f ↔ f a = f b := by
  constructor
  · intro h
    have h' := congrArg (fun g : Fin n → Multiplicative (ZMod p) => g a) h
    rw [permAut_apply] at h'
    change f (Equiv.swap a b a) = f a at h'
    rw [Equiv.swap_apply_left] at h'
    exact h'.symm
  · intro h
    funext k
    rw [permAut_apply]
    change f (Equiv.swap a b k) = f k
    by_cases hka : k = a
    · subst hka
      rw [Equiv.swap_apply_left]
      exact h.symm
    · by_cases hkb : k = b
      · subst hkb
        rw [Equiv.swap_apply_right]
        exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]

private theorem card_eq_prime_mul_card_of_le {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B Bs : Subgroup G} (hBBs : B ≤ Bs) (hBs : IsElemAbelian p Bs)
    (hcard : Nat.card Bs ≤ p * Nat.card B) (hne : B ≠ Bs) :
    Nat.card Bs = p * Nat.card B := by
  classical
  let B' : Subgroup ↥Bs := B.subgroupOf Bs
  have hB'card : Nat.card ↥B' = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBBs).toEquiv
  have hB'index_le : B'.index ≤ p := by
    have h1 : Nat.card ↥B' * B'.index ≤ Nat.card ↥B' * p := by
      rw [Subgroup.card_mul_index, hB'card]
      calc Nat.card Bs ≤ p * Nat.card B := hcard
        _ = Nat.card B * p := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h1 (Nat.card_pos (α := ↥B'))
  have hB'ne_top : B' ≠ ⊤ := by
    intro h
    have h' : B.subgroupOf Bs = ⊤ := h
    exact hne (le_antisymm hBBs (Subgroup.subgroupOf_eq_top.mp h'))
  have hB'index_ne_one : B'.index ≠ 1 := by
    intro h
    exact hB'ne_top (Subgroup.index_eq_one.mp h)
  obtain ⟨n, hn⟩ :=
    isPGroup_iff_card_dvd_pow.mp (CFSG.Open.IsElemAbelian.isPGroup hBs)
  have hidx_dvd : B'.index ∣ p ^ n :=
    (Subgroup.index_dvd_card (H := B')).trans hn
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hidx_dvd
  have hk0 : k ≠ 0 := by
    intro h0
    exact hB'index_ne_one (by rw [hk, h0, pow_zero])
  have hp_le : p ≤ B'.index := by
    rw [hk]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
  have hB'index : B'.index = p := le_antisymm hB'index_le hp_le
  calc Nat.card Bs = Nat.card ↥B' * B'.index := (Subgroup.card_mul_index (H := B')).symm
    _ = Nat.card B * p := by rw [hB'card, hB'index]
    _ = p * Nat.card B := Nat.mul_comm _ _

variable {G : Type} [Group G]

theorem exists_swap_of_isReflection_of_mem_aPermutationFull {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {τ : MulAut ↥Bs}
    (hτ : MulAut.congr eta τ ∈ aPermutationFull n p) (hτr : GGIsReflection p τ) :
    ∃ i j : Fin n, i ≠ j ∧ ∀ b : ↥Bs, (τ b = b ↔ eta b i = eta b j) := by
  let u : MulAut (Fin n → Multiplicative (ZMod p)) := MulAut.congr eta τ
  have hu : u ∈ aPermutationFull n p := hτ
  have hu2 : u ^ 2 = 1 := by
    rw [show u = MulAut.congr eta τ from rfl, ← map_pow, hτr.1, map_one]
  have hfixu : Nat.card {f // u f = f} * p =
      Nat.card (Fin n → Multiplicative (ZMod p)) := by
    rw [show Nat.card {f // u f = f} = Nat.card {b : ↥Bs // τ b = b} from
      card_fix_congr eta τ, hτr.2]
    exact Nat.card_congr eta.toEquiv
  rcases eq_sgnAut_or_swap_of_isRefl hp hp2 (aPermutationFull_le_bSignedFull hu) hu2 hfixu with
    ⟨i, hi⟩ | ⟨a, b, hab, hi | hi⟩
  · exact absurd (prod_eq_of_mem_aPermutationFull u hu
      (Pi.mulSingle i (ofAdd (1 : ZMod p)))) (by
        rw [hi]
        exact prod_sgnAut_mulSingle_ne hp hp2 i)
  · refine ⟨a, b, hab, fun c => ?_⟩
    have hc : u (eta c) = eta (τ c) := congr_apply_eta eta τ c
    rw [hi] at hc
    have hswap := permAut_swap_eq_self_iff hab (eta c)
    constructor
    · intro h
      exact hswap.mp (by rw [hc, h])
    · intro h
      apply eta.injective
      rw [← hc]
      exact hswap.mpr h
  · exact absurd (prod_eq_of_mem_aPermutationFull u hu
      (Pi.mulSingle a (ofAdd (1 : ZMod p)))) (by
        rw [hi]
        exact prod_negTrans_mulSingle_ne hp hp2 a b hab)

theorem fix_iff_mem_of_le_of_ne_one [Finite G] {p : ℕ} (hp : p.Prime) {B Bs : Subgroup G}
    (hBBs : B ≤ Bs) (hBs : IsElemAbelian p Bs) (hcard : Nat.card Bs ≤ p * Nat.card B)
    (hne : B ≠ Bs) {τ : MulAut ↥Bs} (hτ1 : τ ≠ 1) (hfix : ∀ b : ↥Bs, (b : G) ∈ B → τ b = b) :
    ∀ b : ↥Bs, ((b : G) ∈ B ↔ τ b = b) := by
  intro b
  let B' : Subgroup ↥Bs := B.subgroupOf Bs
  let H : Subgroup ↥Bs := ggFixSub τ
  have hB'card : Nat.card ↥B' = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBBs).toEquiv
  have hB'le : B' ≤ H := by
    intro x hx
    exact hfix x (Subgroup.mem_subgroupOf.mp hx)
  have hcardBs : Nat.card Bs = p * Nat.card B :=
    card_eq_prime_mul_card_of_le hp hBBs hBs hcard hne
  have hB'index : B'.index = p := by
    have h1 : B'.index * Nat.card B = p * Nat.card B := by
      rw [← hcardBs, ← hB'card, Subgroup.index_mul_card]
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥B)) h1
  have hHne_top : H ≠ ⊤ := by
    intro htop
    apply hτ1
    refine MulEquiv.ext fun x => ?_
    have hx : x ∈ H := by rw [htop]; exact Subgroup.mem_top x
    simpa using mem_ggFixSub.mp hx
  have hHidx_dvd : H.index ∣ p := by
    have hmul := Subgroup.relIndex_mul_relIndex (H := B') (K := H) (L := ⊤) hB'le le_top
    rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right, hB'index] at hmul
    exact dvd_of_mul_left_eq (B'.relIndex H) hmul
  have hHindex : H.index = p := by
    rcases (Nat.dvd_prime hp).mp hHidx_dvd with h1 | h1
    · exact absurd h1 (fun h => hHne_top (Subgroup.index_eq_one.mp h))
    · exact h1
  have hB'relH : B'.relIndex H = 1 := by
    have hmul := Subgroup.relIndex_mul_relIndex (H := B') (K := H) (L := ⊤) hB'le le_top
    rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right, hB'index, hHindex] at hmul
    have h1 : B'.relIndex H * p = 1 * p := by simpa using hmul
    exact Nat.mul_right_cancel hp.pos h1
  have hH_eq : H = B' := le_antisymm (Subgroup.relIndex_eq_one.mp hB'relH) hB'le
  change (b : G) ∈ B ↔ τ b = b
  rw [← Subgroup.mem_subgroupOf (H := B) (K := Bs)]
  change b ∈ B' ↔ τ b = b
  rw [← hH_eq]
  exact mem_ggFixSub

theorem isReflection_of_fix_iff_mem [Finite G] {p : ℕ} (hp : p.Prime) {B Bs : Subgroup G}
    (hBBs : B ≤ Bs) (hBs : IsElemAbelian p Bs) (hcard : Nat.card Bs ≤ p * Nat.card B)
    (hne : B ≠ Bs) {τ : MulAut ↥Bs} (hτ2 : τ ^ 2 = 1)
    (hiff : ∀ b : ↥Bs, ((b : G) ∈ B ↔ τ b = b)) :
    GGIsReflection p τ := by
  have hcardBs : Nat.card Bs = p * Nat.card B :=
    card_eq_prime_mul_card_of_le hp hBBs hBs hcard hne
  have hfixcard : Nat.card {b : ↥Bs // τ b = b} = Nat.card B :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), (hiff x.1).mpr x.2⟩
        invFun := fun g => ⟨⟨(g : G), hBBs g.2⟩, (hiff ⟨(g : G), hBBs g.2⟩).mp g.2⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun g => Subtype.ext rfl }
  refine ⟨hτ2, ?_⟩
  calc Nat.card {b : ↥Bs // τ b = b} * p = Nat.card B * p := by rw [hfixcard]
    _ = p * Nat.card B := Nat.mul_comm _ _
    _ = Nat.card ↥Bs := hcardBs.symm

theorem exists_root_hyperplane_of_involution [Finite G] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B Bs L : Subgroup G} (hBBs : B ≤ Bs) (hBs : IsElemAbelian p Bs)
    (hcard : Nat.card Bs ≤ p * Nat.card B) (hne : B ≠ Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {τ : MulAut ↥Bs} (hτL : τ ∈ ggAutomizer L Bs) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hfix : ∀ b : ↥Bs, (b : G) ∈ B → τ b = b) :
    ∃ i j : Fin n, i ≠ j ∧ ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = eta b j) := by
  have hiff := fix_iff_mem_of_le_of_ne_one hp hBBs hBs hcard hne hτ1 hfix
  have href := isReflection_of_fix_iff_mem hp hBBs hBs hcard hne hτ2 hiff
  have hu : MulAut.congr eta τ ∈ aPermutationFull n p := by
    rw [← hL]
    exact Subgroup.mem_map_of_mem _ hτL
  obtain ⟨i, j, hij, hswap⟩ :=
    exists_swap_of_isReflection_of_mem_aPermutationFull hp hp2 eta hu href
  exact ⟨i, j, hij, fun b => (hiff b).trans (hswap b)⟩

end CFSG.StandardType

end
