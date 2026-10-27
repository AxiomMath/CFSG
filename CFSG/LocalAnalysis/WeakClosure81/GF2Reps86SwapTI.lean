module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTenAlg
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Statement
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Tools
import CFSG.LocalAnalysis.OddStandard.AltStdSecGenPerm

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.OddStandard.AltStdSec Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive (altPre mem_altPre_iff)

@[expose] noncomputable def autRep {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]
    (H : Subgroup (MulAut V)) : Representation (ZMod 2) ↥H (Additive V) where
  toFun h := AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (h : MulAut V).toMonoidHom)
  map_one' := LinearMap.ext fun _ => Additive.toMul.injective rfl
  map_mul' _ _ := LinearMap.ext fun _ => Additive.toMul.injective rfl

theorem autRep_apply {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]
    {H : Subgroup (MulAut V)} (h : ↥H) (x : Additive V) :
    autRep H h x = Additive.ofMul ((h : MulAut V) (Additive.toMul x)) :=
  rfl

theorem surjective_of_isSwap {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ}
    {ψ : ↥H →* Perm (Fin n)} (hA : alternatingGroup (Fin n) ≤ ψ.range) {τ : ↥H}
    (hτ : (ψ τ).IsSwap) : Function.Surjective ψ := by
  intro σ
  rcases Int.units_eq_one_or (sign σ) with h | h
  · exact hA (mem_alternatingGroup.2 h)
  · obtain ⟨x, hx⟩ := hA (show σ * ψ τ ∈ alternatingGroup (Fin n) from by
      rw [mem_alternatingGroup, Perm.sign_mul, h, hτ.sign_eq]
      decide)
    exact ⟨x * τ⁻¹, by rw [map_mul, map_inv, hx, mul_inv_cancel_right]⟩

section Aux

variable {V : Type} [CommGroup V]

private theorem mem_range_autRep_sub_one_iff [Finite V] [Module (ZMod 2) (Additive V)]
    {H : Subgroup (MulAut V)} (g : ↥H) (x : Additive V) :
    x ∈ LinearMap.range (autRep H g - 1) ↔
      Additive.toMul x ∈ commV (Subgroup.zpowers (g : MulAut V)) := by
  rw [commV_zpowers_eq_map, Subgroup.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨Additive.toMul y, Subgroup.mem_top _, ?_⟩
    simp [autRep_apply, commHom_apply, div_eq_mul_inv]
  · rintro ⟨v, -, hv⟩
    refine ⟨Additive.ofMul v, Additive.toMul.injective ?_⟩
    simp [autRep_apply, ← hv, commHom_apply, div_eq_mul_inv]

private theorem index_fixV_swap_le {n : ℕ} (R : Perm (Fin n) →* MulAut V) {a₀ b₀ : Fin n}
    (h₀ : a₀ ≠ b₀) (hidx : (fixV (Subgroup.zpowers (R (swap a₀ b₀)))).index ≤ 8)
    {a b : Fin n} (hab : a ≠ b) : (fixV (Subgroup.zpowers (R (swap a b)))).index ≤ 8 := by
  obtain ⟨π, hπ⟩ := isConj_iff.1 (isConj_swap h₀ hab)
  rw [← hπ, map_mul, map_mul, map_inv, FixVLat.index_fixV_zpowers_conj]
  exact hidx

private def stabAct {n : ℕ} (R : Perm (Fin n) →* MulAut V) (v : V) : Subgroup (Perm (Fin n)) :=
  (MulAction.stabilizer (MulAut V) v).comap R

private theorem mem_stabAct {n : ℕ} {R : Perm (Fin n) →* MulAut V} {v : V} {σ : Perm (Fin n)} :
    σ ∈ stabAct R v ↔ R σ v = v :=
  Iff.rfl

private theorem card_altSub_five {n : ℕ} {S : Finset (Fin n)} (hS : S.card = 5) :
    Nat.card (altSub S) = 60 := by
  have h := Nat.card_congr (altSubEquiv S).toEquiv
  have : Nontrivial (Fin S.card) := by
    rw [hS]
    infer_instance
  rw [h, nat_card_alternatingGroup]
  simp [hS, Nat.factorial]

private theorem isSimpleGroup_altSub_five {n : ℕ} {S : Finset (Fin n)} (hS : S.card = 5) :
    IsSimpleGroup (altSub S) := by
  have : IsSimpleGroup (alternatingGroup (Fin S.card)) :=
    alternatingGroup.isSimpleGroup (by simp [hS])
  exact (altSubEquiv S).isSimpleGroup

private theorem altSub_comm_swap {n : ℕ} {S : Finset (Fin n)} {a b : Fin n} (ha : a ∉ S)
    (hb : b ∉ S) {e : Perm (Fin n)} (he : e ∈ altSub S) : e * swap a b = swap a b * e := by
  refine (Perm.Disjoint.commute fun w => ?_).eq
  by_cases hw : w ∈ S
  · right
    exact swap_apply_of_ne_of_ne (fun h => ha (h ▸ hw)) (fun h => hb (h ▸ hw))
  · left
    exact (mem_altSub.1 he).2 w hw

private theorem altSub_compl_le_stabAct [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ}
    (hn : 7 ≤ n) (R : Perm (Fin n) →* MulAut V) {a b : Fin n} (hab : a ≠ b)
    (hidx : (fixV (Subgroup.zpowers (R (swap a b)))).index ≤ 8) {v : V}
    (hv : v ∈ commV (Subgroup.zpowers (R (swap a b)))) :
    altSub (({a, b} : Finset (Fin n))ᶜ) ≤ stabAct R v := by
  have hc : R (swap a b) ^ 2 = 1 := by rw [← map_pow, pow_two, swap_mul_self, map_one]
  refine altSub_le_of_cyc3 fun x y z hx hy hz hxy hyz hxz => ?_
  have hsub : ({x, y, z} : Finset (Fin n)) ⊆ ({a, b} : Finset (Fin n))ᶜ := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hcard : 5 ≤ (({a, b} : Finset (Fin n))ᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
    omega
  obtain ⟨S, hxyz, hST, hS5⟩ := Finset.exists_subsuperset_card_eq hsub
    (le_trans Finset.card_le_three (by norm_num)) hcard
  have hxS : x ∈ S := hxyz (by simp)
  have hyS : y ∈ S := hxyz (by simp)
  have hzS : z ∈ S := hxyz (by simp)
  have haS : a ∉ S := fun h => by simpa using hST h
  have hbS : b ∉ S := fun h => by simpa using hST h
  have : IsSimpleGroup (altSub S) := isSimpleGroup_altSub_five hS5
  have hcomm : ∀ e : ↥(altSub S), (R.comp (altSub S).subtype) e * R (swap a b) =
      R (swap a b) * (R.comp (altSub S).subtype) e := fun e => by
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, ← map_mul]
    rw [altSub_comm_swap haS hbS e.2]
  refine mem_stabAct.2 (centralizes_commV_of_simple hV
    (by rw [card_altSub_five hS5]; norm_num) (R.comp (altSub S).subtype) hc hcomm hidx
    ⟨cyc3 x y z, cyc3_mem_altSub hxS hyS hzS hxy hyz hxz⟩ hv)

private theorem three_le_card_inter_compl {n : ℕ} (hn : 7 ≤ n) {s t : Finset (Fin n)}
    (hs : s.card ≤ 2) (ht : t.card ≤ 2) : 3 ≤ (sᶜ ∩ tᶜ).card := by
  rw [← Finset.compl_union, Finset.card_compl, Fintype.card_fin]
  have := Finset.card_union_le s t
  omega

private theorem alternatingGroup_le_altSub_univ {n : ℕ} :
    alternatingGroup (Fin n) ≤ altSub (Finset.univ : Finset (Fin n)) := fun _ hσ =>
  mem_altSub.2 ⟨mem_alternatingGroup.1 hσ, fun i hi => absurd (Finset.mem_univ i) hi⟩

private theorem swap_conj_mem_altSub {n : ℕ} {p q : Fin n} (hpq : p ≠ q) {σ : Perm (Fin n)}
    (hσ : σ ∈ altSub (({q} : Finset (Fin n))ᶜ)) :
    swap p q * σ * (swap p q)⁻¹ ∈ altSub (({p} : Finset (Fin n))ᶜ) := by
  obtain ⟨hs, hfix⟩ := mem_altSub.1 hσ
  refine mem_altSub.2 ⟨?_, fun i hi => ?_⟩
  · rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hs, Perm.sign_swap hpq]
    decide
  · have hip : i = p := by simpa using hi
    subst hip
    have hq : σ q = q := hfix q (by simp)
    simp [swap_inv, hq]

private theorem alternatingGroup_le_of_shared {n : ℕ} (hn : 7 ≤ n) {K : Subgroup (Perm (Fin n))}
    {p q r : Fin n} (hpq : p ≠ q) (hqr : q ≠ r) (hs : swap p q ∈ K)
    (h1 : altSub (({p, q} : Finset (Fin n))ᶜ) ≤ K) (h2 : altSub (({p, r} : Finset (Fin n))ᶜ) ≤ K) :
    alternatingGroup (Fin n) ≤ K := by
  have hp : altSub (({p} : Finset (Fin n))ᶜ) ≤ K := by
    have := altSub_sup_altSub (S := ({p, q} : Finset (Fin n))ᶜ) (T := ({p, r} : Finset (Fin n))ᶜ)
      (three_le_card_inter_compl hn Finset.card_le_two Finset.card_le_two)
    have hU : ({p, q} : Finset (Fin n))ᶜ ∪ ({p, r} : Finset (Fin n))ᶜ =
        ({p} : Finset (Fin n))ᶜ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
      grind
    rw [hU] at this
    rw [← this]
    exact sup_le h1 h2
  have hq : altSub (({q} : Finset (Fin n))ᶜ) ≤ K := by
    intro σ hσ
    have h := hp (swap_conj_mem_altSub hpq hσ)
    have := K.mul_mem (K.mul_mem (K.inv_mem hs) h) hs
    simpa [mul_assoc, swap_inv] using this
  have := altSub_sup_altSub (S := ({p} : Finset (Fin n))ᶜ) (T := ({q} : Finset (Fin n))ᶜ)
    (three_le_card_inter_compl hn (by simp) (by simp))
  have hU : ({p} : Finset (Fin n))ᶜ ∪ ({q} : Finset (Fin n))ᶜ = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_singleton, Finset.mem_univ,
      iff_true]
    grind
  rw [hU] at this
  exact alternatingGroup_le_altSub_univ.trans (this ▸ sup_le hp hq)

private theorem exists_pair_eq {α : Type*} [DecidableEq α] {a b p : α} (hab : a ≠ b)
    (hp : p ∈ ({a, b} : Finset α)) :
    ∃ q, p ≠ q ∧ ({a, b} : Finset α) = {p, q} ∧ swap a b = swap p q := by
  rcases Finset.mem_insert.1 hp with rfl | hp
  · exact ⟨b, hab, rfl, rfl⟩
  · obtain rfl := Finset.mem_singleton.1 hp
    exact ⟨a, hab.symm, Finset.pair_comm _ _, swap_comm _ _⟩

private theorem alternatingGroup_le_of_swaps {n : ℕ} (hn : 7 ≤ n) {K : Subgroup (Perm (Fin n))}
    {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (hne : swap a b ≠ swap c d)
    (hs : swap a b ∈ K) (h1 : altSub (({a, b} : Finset (Fin n))ᶜ) ≤ K)
    (h2 : altSub (({c, d} : Finset (Fin n))ᶜ) ≤ K) : alternatingGroup (Fin n) ≤ K := by
  by_cases hdisj : Disjoint ({a, b} : Finset (Fin n)) {c, d}
  · have := altSub_sup_altSub (S := ({a, b} : Finset (Fin n))ᶜ) (T := ({c, d} : Finset (Fin n))ᶜ)
      (three_le_card_inter_compl hn Finset.card_le_two Finset.card_le_two)
    have hU : ({a, b} : Finset (Fin n))ᶜ ∪ ({c, d} : Finset (Fin n))ᶜ = Finset.univ := by
      rw [← Finset.compl_inter, Finset.disjoint_iff_inter_eq_empty.1 hdisj, Finset.compl_empty]
    rw [hU] at this
    exact alternatingGroup_le_altSub_univ.trans (this ▸ sup_le h1 h2)
  · obtain ⟨p, hp1, hp2⟩ := Finset.not_disjoint_iff.1 hdisj
    obtain ⟨q, hpq, hq, hsq⟩ := exists_pair_eq hab hp1
    obtain ⟨r, -, hr, hsr⟩ := exists_pair_eq hcd hp2
    rw [hq] at h1
    rw [hr] at h2
    rw [hsq] at hs
    rw [hsq, hsr] at hne
    exact alternatingGroup_le_of_shared hn hpq (fun h => hne (by rw [h])) hs h1 h2

private theorem inf_commV_eq_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 7 ≤ n)
    (R : Perm (Fin n) →* MulAut V)
    (hidx : ∀ a b : Fin n, a ≠ b → (fixV (Subgroup.zpowers (R (swap a b)))).index ≤ 8)
    (hfix : ∀ w : V, (∀ σ ∈ alternatingGroup (Fin n), R σ w = w) → w = 1)
    {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (hne : swap a b ≠ swap c d) :
    commV (Subgroup.zpowers (R (swap a b))) ⊓ commV (Subgroup.zpowers (R (swap c d))) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
  have hc : ∀ x y : Fin n, R (swap x y) ^ 2 = 1 := fun x y => by
    rw [← map_pow, pow_two, swap_mul_self, map_one]
  have hK : alternatingGroup (Fin n) ≤ stabAct R w :=
    alternatingGroup_le_of_swaps hn hab hcd hne
      (apply_eq_of_mem_commV_zpowers hV (hc a b) hw1)
      (altSub_compl_le_stabAct hV hn R hab (hidx a b hab) hw1)
      (altSub_compl_le_stabAct hV hn R hcd (hidx c d hcd) hw2)
  exact Subgroup.mem_bot.2 (hfix w fun σ hσ => mem_stabAct.1 (hK hσ))

end Aux

theorem swapDisjoint_autRep {V : Type} [CommGroup V] [Finite V] [Module (ZMod 2) (Additive V)]
    (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}
    (hn : 7 ≤ n) (hψ : Function.Injective ψ) (hψs : Function.Surjective ψ)
    (hfix : fixV (altPre ψ) = ⊥) {τ : ↥H} (hτ : (ψ τ).IsSwap)
    (hidx : (fixV (Subgroup.zpowers (τ : MulAut V))).index ≤ 8) :
    CFSG.LocalAnalysis.WeakClosure81.SwapDisjoint ψ (autRep H) := by
  let e : ↥H ≃* Perm (Fin n) := MulEquiv.ofBijective ψ ⟨hψ, hψs⟩
  let R : Perm (Fin n) →* MulAut V := H.subtype.comp e.symm.toMonoidHom
  have hRψ : ∀ h : ↥H, R (ψ h) = (h : MulAut V) := fun h => by
    change ((e.symm (e h) : ↥H) : MulAut V) = h
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨a₀, b₀, h₀, hτ₀⟩ := hτ
  have hidx' : ∀ a b : Fin n, a ≠ b → (fixV (Subgroup.zpowers (R (swap a b)))).index ≤ 8 := by
    intro a b hab
    refine index_fixV_swap_le R h₀ ?_ hab
    rw [← hτ₀, hRψ]
    exact hidx
  have hfix' : ∀ w : V, (∀ σ ∈ alternatingGroup (Fin n), R σ w = w) → w = 1 := by
    intro w hw
    have hmem : w ∈ fixV (altPre ψ) := by
      intro x hx
      obtain ⟨hxH, hxA⟩ := mem_altPre_iff.1 hx
      have := hw _ hxA
      rwa [hRψ ⟨x, hxH⟩] at this
    rw [hfix] at hmem
    exact Subgroup.mem_bot.1 hmem
  refine ⟨fun g hg => ?_, fun g h hg hh hne => ?_⟩
  · have : g = 1 := hψ (hg.trans (map_one ψ).symm)
    rw [this, map_one]
  · obtain ⟨a, b, hab, hgab⟩ := hg
    obtain ⟨c, d, hcd, hhcd⟩ := hh
    have hgR : (g : MulAut V) = R (swap a b) := by rw [← hgab, hRψ]
    have hhR : (h : MulAut V) = R (swap c d) := by rw [← hhcd, hRψ]
    have hne' : swap a b ≠ swap c d := by rwa [hgab, hhcd] at hne
    have key := inf_commV_eq_bot hV hn R hidx' hfix' hab hcd hne'
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    rw [mem_range_autRep_sub_one_iff, hgR] at hx1
    rw [mem_range_autRep_sub_one_iff, hhR] at hx2
    have h1 : Additive.toMul x ∈ (⊥ : Subgroup V) := key ▸ Subgroup.mem_inf.2 ⟨hx1, hx2⟩
    exact (Submodule.mem_bot _).2 (Additive.toMul.injective (Subgroup.mem_bot.1 h1))

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
