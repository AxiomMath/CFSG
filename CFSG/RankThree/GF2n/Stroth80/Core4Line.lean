module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec97F3D

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem le_QB_of_conj_le_QB (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M)
    (hFB : conjSubgroup h B ≤ QB B) (hne : conjSubgroup h B ≠ B) :
    B ≤ QB (conjSubgroup h B) := by
  obtain ⟨gB, hgB⟩ := hc.conj
  obtain ⟨gF, hgF⟩ := (hc.conj_of_mem hh).conj
  exact (hc.hyp.le_QB_iff_le_QB ⟨gB, hgB⟩ ⟨gF, hgF⟩ (Ne.symm hne)).mpr hFB

theorem conjSubgroup_inv_conj_self (h : G) (B : Subgroup G) :
    conjSubgroup h⁻¹ (conjSubgroup h B) = B := by
  rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]

theorem lineGeom_swap (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) (hFB : conjSubgroup h B ≤ QB B)
    (hne : conjSubgroup h B ≠ B) : LineGeom M Q Z (conjSubgroup h B) h⁻¹ := by
  have hBF : B ≤ QB (conjSubgroup h B) := le_QB_of_conj_le_QB hc hh hFB hne
  refine lineGeom_of_QB (hc.conj_of_mem hh) (M.inv_mem hh) ?_
  rw [conjSubgroup_inv_conj_self]
  exact hBF

theorem mem_LB_of_mem_conj_swap (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M)
    (hFB : conjSubgroup h B ≤ QB B) (hne : conjSubgroup h B ≠ B) {y : G} (hy : y ∈ LB M Q B)
    (hyN : conjSubgroup y (LB M Q (conjSubgroup h B)) ≠ LB M Q (conjSubgroup h B)) {z : G}
    (hzF : z ∈ LB M Q (conjSubgroup h B)) (hzy : z ∈ conjSubgroup y (LB M Q (conjSubgroup h B))) :
    z ∈ LB M Q B := by
  have hcF := hc.conj_of_mem hh
  have hline := lineGeom_swap hc hh hFB hne
  have hy' : y ∈ LB M Q (conjSubgroup h B) ⊔ LB M Q (conjSubgroup h⁻¹ (conjSubgroup h B)) := by
    rw [conjSubgroup_inv_conj_self]
    exact Subgroup.mem_sup_right hy
  rcases line_orbit_of_geom hcF (M.inv_mem hh) hline y hy' with h1 | ⟨ε, hε, h2⟩
  · exact absurd h1 hyN
  · rw [conjSubgroup_inv_conj_self] at h2
    rw [h2] at hzy
    have h3 : ε⁻¹ * z * ε ∈ LB M Q B := mem_conjSubgroup.mp hzy
    have hc1 : ⁅z⁻¹, ε⁻¹⁆ ∈ Q :=
      hcF.commutator_LB_le_Q (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hzF)
        (Subgroup.inv_mem _ hε))
    have e : z = (ε⁻¹ * z * ε) * ⁅z⁻¹, ε⁻¹⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (LB M Q B).mul_mem h3 ((LB M Q B).inv_mem (Subgroup.mem_sup_left hc1))

theorem relIndex_Q_LB (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs5 : Sec5Hyp hc n t) : Q.relIndex (LB M Q B) = Nat.card Z ^ (n - 1) := by
  have hcard := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.2.1
  have hQL : Q ≤ LB M Q B := le_sup_left
  have h5 := Subgroup.relIndex_mul_card (H := Q) (K := LB M Q B)
  rw [inf_eq_left.mpr hQL, hcard] at h5
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h5, mul_comm])

theorem exists_mem_E_not_Q (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y) : ∃ x ∈ LB M Q B ⊓ X, x ∉ Q := by
  by_contra hall
  push Not at hall
  have hQX : Q ≤ X := hsplit.1.1
  have hQE : Q ≤ LB M Q B ⊓ X := le_inf le_sup_left hQX
  have hEQ : LB M Q B ⊓ X ≤ Q := fun x hx => hall x hx
  have hEeq : LB M Q B ⊓ X = Q := le_antisymm hEQ hQE
  have h1 := relIndex_LB_inf_X hc hsplit h4
  have h2 := relIndex_Q_LB h34 hc hs.toSec5
  rw [hEeq] at h1
  have hn4 : 4 ≤ n := HS6.four_le_of_omegaPlus_two h34 hc hs.toSec5 hs.plus4
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  rw [h1] at h2
  have h3 : Nat.card Z ^ 1 = Nat.card Z ^ (n - 1) := by rw [pow_one]; exact h2
  have := Nat.pow_right_injective (by omega : 2 ≤ Nat.card Z) h3
  omega

theorem conj_LB_eq_of_mem_kappaBar (hc : Ctx M Q Z B) {X : Subgroup G} {h : G} (hh : h ∈ M)
    (hFB : conjSubgroup h B ≤ QB B)
    (hhard : ∀ x ∈ LB M Q B ⊓ X, x ∉ Q → x ∉ conjSubgroup h (LB M Q B))
    (hex : ∃ x ∈ LB M Q B ⊓ X, x ∉ Q) {k : G}
    (hk1 : k ∈ conjSubgroup h (LB M Q B ⊓ X))
    (hk2 : conjSubgroup k (LB M Q B ⊓ X) = LB M Q B ⊓ X) :
    conjSubgroup k (LB M Q B) = LB M Q B := by
  have hline := lineGeom_of_QB hc hh hFB
  have hLF : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hkLF : k ∈ conjSubgroup h (LB M Q B) := Subgroup.map_mono inf_le_left hk1
  have hkΛ : k ∈ LB M Q B ⊔ LB M Q (conjSubgroup h B) := by
    rw [hLF]
    exact Subgroup.mem_sup_right hkLF
  rcases line_orbit_of_geom hc hh hline k hkΛ with h1 | ⟨ε, hε, h2⟩
  · exact h1
  · exfalso
    obtain ⟨x, hxE, hxQ⟩ := hex
    have hx1 : x ∈ conjSubgroup k (LB M Q B ⊓ X) := by
      rw [hk2]
      exact hxE
    have hx2 : x ∈ conjSubgroup k (LB M Q B) := Subgroup.map_mono inf_le_left hx1
    rw [h2] at hx2
    have h3 : ε⁻¹ * x * ε ∈ LB M Q (conjSubgroup h B) := mem_conjSubgroup.mp hx2
    have hc1 : ⁅x⁻¹, ε⁻¹⁆ ∈ Q :=
      hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hxE.1)
        (Subgroup.inv_mem _ hε))
    have e : x = (ε⁻¹ * x * ε) * ⁅x⁻¹, ε⁻¹⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    have hxF : x ∈ LB M Q (conjSubgroup h B) := by
      rw [e]
      exact (LB M Q (conjSubgroup h B)).mul_mem h3
        ((LB M Q (conjSubgroup h B)).inv_mem (Subgroup.mem_sup_left hc1))
    rw [hLF] at hxF
    exact hhard x hxE hxQ hxF

theorem conj_Y_eq_of_normalizes_E (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h1 : OneConcl hc X Y)
    (hex : ∃ x ∈ LB M Q B ⊓ X, x ∉ Q) {k : G} (hkM : k ∈ M)
    (hk : conjSubgroup k (LB M Q B ⊓ X) = LB M Q B ⊓ X) : conjSubgroup k Y = Y := by
  obtain ⟨x, hxE, hxQ⟩ := hex
  refine conj_Y_eq_of_conj_mem hc hsplit h1 hxE hxQ hkM ?_
  have : k * x * k⁻¹ ∈ conjSubgroup k (LB M Q B ⊓ X) :=
    ⟨x, hxE, by simp [MulAut.conj_apply]⟩
  rwa [hk] at this

theorem conjSubgroup_inf_of_eq {k : G} {A C : Subgroup G} (hA : conjSubgroup k A = A)
    (hC : conjSubgroup k C = C) : conjSubgroup k (A ⊓ C) = A ⊓ C := by
  have h : conjSubgroup k (A ⊓ C) = conjSubgroup k A ⊓ conjSubgroup k C :=
    Subgroup.map_inf A C _ (MulAut.conj k).injective
  rw [h, hA, hC]

theorem relIndex_le_of_commutator_injective {R K Q S : Subgroup G} (y : G)
    (hmap : ∀ k ∈ K, ⁅y, k⁆ ∈ S)
    (hcongr : ∀ k ∈ K, ∀ r ∈ R, ⁅y, k⁆⁻¹ * ⁅y, k * r⁆ ∈ Q)
    (hinj : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ⁅y, k₁⁆⁻¹ * ⁅y, k₂⁆ ∈ Q → k₁⁻¹ * k₂ ∈ R) :
    R.relIndex K ≤ Q.relIndex S := by
  classical
  let f₀ : ↥K → ↥S ⧸ Q.subgroupOf S := fun k => QuotientGroup.mk ⟨⁅y, (k : G)⁆, hmap k k.2⟩
  have hf₀ : ∀ a b : ↥K, (QuotientGroup.leftRel (R.subgroupOf K)) a b → f₀ a = f₀ b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
    have hq : (a : G)⁻¹ * (b : G) ∈ R := by simpa using hab
    have h1 := hcongr a a.2 _ hq
    rw [show (a : G) * ((a : G)⁻¹ * (b : G)) = b by group] at h1
    show (QuotientGroup.mk ⟨⁅y, (a : G)⁆, hmap a a.2⟩ : ↥S ⧸ Q.subgroupOf S) =
      QuotientGroup.mk ⟨⁅y, (b : G)⁆, hmap b b.2⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact h1
  let f : ↥K ⧸ R.subgroupOf K → ↥S ⧸ Q.subgroupOf S := Quotient.lift f₀ hf₀
  have hinjf : Function.Injective f := by
    intro a b
    refine Quotient.inductionOn₂ a b (fun a b hab => ?_)
    have hab' : f₀ a = f₀ b := hab
    have h1 : (QuotientGroup.mk ⟨⁅y, (a : G)⁆, hmap a a.2⟩ : ↥S ⧸ Q.subgroupOf S) =
        QuotientGroup.mk ⟨⁅y, (b : G)⁆, hmap b b.2⟩ := hab'
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have h2 := hinj a a.2 b b.2 h1
    apply Quotient.sound
    exact (QuotientGroup.leftRel_apply (s := R.subgroupOf K)).mpr
      (Subgroup.mem_subgroupOf.mpr (by simpa using h2))
  exact Nat.card_le_card_of_injective f hinjf

theorem relIndex_pos' (H K : Subgroup G) : 0 < H.relIndex K := by
  unfold Subgroup.relIndex
  exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

theorem relIndex_kappaBar_ge (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y) (h2 : TwoConcl M Q B X) {h : G} (hh : h ∈ M)
    (hα : (Subgroup.normalizer (LB M Q B : Set G)).relIndex (LB M Q (conjSubgroup h B)) ≤
      Nat.card Z) :
    Nat.card Z ^ (n - 3) ≤ Q.relIndex (conjSubgroup h (LB M Q B ⊓ X) ⊓
      Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G)) := by
  classical
  set L := LB M Q B with hL
  set E := L ⊓ X with hE
  set E1 := conjSubgroup h E with hE1
  set N := Subgroup.normalizer (L : Set G) with hN
  set K := E1 ⊓ Subgroup.normalizer (E : Set G) with hK
  have hLF : LB M Q (conjSubgroup h B) = conjSubgroup h L := hc.LB_conj hh
  have hQX : Q ≤ X := hsplit.1.1
  have hQL : Q ≤ L := le_sup_left
  have hQE : Q ≤ E := le_inf hQL hQX
  have hQh : conjSubgroup h Q = Q := hc.conj_Q_eq hh
  have hqq : 0 < Nat.card Z := Nat.card_pos
  have hn3 : 3 ≤ n := hs.toSec5.n_gt
  have hQLF : Q.relIndex (conjSubgroup h L) = Nat.card Z ^ (n - 1) := by
    have h3 := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj h).toMonoidHom)
      Q L (MulAut.conj h).injective
    have e1 : Q.map (MulAut.conj h).toMonoidHom = Q := hQh
    rw [e1] at h3
    exact h3.trans (relIndex_Q_LB h34 hc hs.toSec5)
  have hE1LF : E1.relIndex (conjSubgroup h L) = Nat.card Z := by
    have h3 := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj h).toMonoidHom)
      E L (MulAut.conj h).injective
    exact h3.trans (relIndex_LB_inf_X hc hsplit h4)
  have hNLF : N.relIndex (conjSubgroup h L) ≤ Nat.card Z := by
    rw [← hLF]
    exact hα
  have hE1le : E1 ≤ conjSubgroup h L := Subgroup.map_mono inf_le_left
  have hLFM : conjSubgroup h L ≤ M := by
    rw [← hLF]
    exact (hc.conj_of_mem hh).LB_le_M
  have hEN : E1 ⊓ N ≤ K := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hxM : x ∈ M := hLFM (hE1le hx.1)
    have hxL : conjSubgroup x L = L := conjSubgroup_eq_self_iff.mpr hx.2
    exact conjSubgroup_eq_self_iff.mp (conj_E_eq_of_normalizes_LB h2 hxM hxL)
  have hQEN : Q ≤ E1 ⊓ N := by
    refine le_inf ?_ (hQL.trans Subgroup.le_normalizer)
    rw [← hQh]
    exact Subgroup.map_mono hQE
  have hdec : Q.relIndex (E1 ⊓ N) * (E1 ⊓ N).relIndex (conjSubgroup h L) =
      Nat.card Z ^ (n - 1) := by
    rw [Subgroup.relIndex_mul_relIndex Q (E1 ⊓ N) _ hQEN (inf_le_left.trans hE1le), hQLF]
  have hb : (E1 ⊓ N).relIndex (conjSubgroup h L) ≤ Nat.card Z * Nat.card Z := by
    refine (Subgroup.relIndex_inf_le (H := E1) (K := N) (L := conjSubgroup h L)).trans ?_
    rw [hE1LF]
    exact Nat.mul_le_mul_left _ hNLF
  have hpow : Nat.card Z ^ (n - 1) = Nat.card Z ^ (n - 3) * (Nat.card Z * Nat.card Z) := by
    rw [← pow_two, ← pow_add]
    congr 1
    omega
  have ha : Nat.card Z ^ (n - 3) ≤ Q.relIndex (E1 ⊓ N) := by
    by_contra hlt
    push Not at hlt
    have h5 : Q.relIndex (E1 ⊓ N) * (E1 ⊓ N).relIndex (conjSubgroup h L) <
        Nat.card Z ^ (n - 3) * (Nat.card Z * Nat.card Z) :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ hb)
        (Nat.mul_lt_mul_of_pos_right hlt (Nat.mul_pos hqq hqq))
    rw [hdec, hpow] at h5
    exact lt_irrefl _ h5
  have hmul : Q.relIndex (E1 ⊓ N) * (E1 ⊓ N).relIndex K = Q.relIndex K :=
    Subgroup.relIndex_mul_relIndex Q (E1 ⊓ N) K hQEN hEN
  calc Nat.card Z ^ (n - 3) ≤ Q.relIndex (E1 ⊓ N) := ha
    _ ≤ Q.relIndex (E1 ⊓ N) * (E1 ⊓ N).relIndex K :=
        Nat.le_mul_of_pos_right _ (relIndex_pos' _ _)
    _ = Q.relIndex K := hmul

theorem S_normalizes_LF (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) (hn5 : 5 ≤ n) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) (h1 : OneConcl hc X Y)
    (h2 : TwoConcl M Q B X) {h : G} (hh : h ∈ M) (hFB : conjSubgroup h B ≤ QB B)
    (hhard : ∀ x ∈ LB M Q B ⊓ X, x ∉ Q →
      h * x * h⁻¹ ∉ LB M Q B ∧ x ∉ conjSubgroup h (LB M Q B))
    (hα : (Subgroup.normalizer (LB M Q B : Set G)).relIndex (LB M Q (conjSubgroup h B)) ≤
      Nat.card Z) :
    ∀ y ∈ LB M Q B ⊓ Y,
      conjSubgroup y (LB M Q (conjSubgroup h B)) = LB M Q (conjSubgroup h B) := by
  classical
  intro y hy
  by_contra hyN
  have hLF : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hQh : conjSubgroup h Q = Q := hc.conj_Q_eq hh
  have hLM : LB M Q B ≤ M := hc.LB_le_M
  have hLFM : conjSubgroup h (LB M Q B) ≤ M := by
    rw [← hLF]
    exact (hc.conj_of_mem hh).LB_le_M
  have hex := exists_mem_E_not_Q h34 hc hs hsplit h4
  have hne : conjSubgroup h B ≠ B := by
    intro heq
    obtain ⟨x, hxE, hxQ⟩ := hex
    apply (hhard x hxE hxQ).1
    have hmem : h * x * h⁻¹ ∈ conjSubgroup h (LB M Q B) :=
      ⟨x, hxE.1, by simp [MulAut.conj_apply]⟩
    rw [← hLF, heq] at hmem
    exact hmem
  have hyM : y ∈ M := hLM hy.1
  have hKnorm : ∀ k ∈ conjSubgroup h (LB M Q B ⊓ X) ⊓
      Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G),
      conjSubgroup k (LB M Q B ⊓ Y) = LB M Q B ⊓ Y := by
    intro k hk
    have hkM : k ∈ M := hLFM (Subgroup.map_mono inf_le_left hk.1)
    have hkE : conjSubgroup k (LB M Q B ⊓ X) = LB M Q B ⊓ X := conjSubgroup_eq_self_iff.mpr hk.2
    exact conjSubgroup_inf_of_eq
      (conj_LB_eq_of_mem_kappaBar hc hh hFB (fun x hx hxQ => (hhard x hx hxQ).2) hex hk.1 hkE)
      (conj_Y_eq_of_normalizes_E hc hsplit h1 hex hkM hkE)
  have hmap : ∀ k ∈ conjSubgroup h (LB M Q B ⊓ X) ⊓
      Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G), ⁅y, k⁆ ∈ LB M Q B ⊓ Y := by
    intro k hk
    have hmem : k * y⁻¹ * k⁻¹ ∈ conjSubgroup k (LB M Q B ⊓ Y) :=
      ⟨y⁻¹, (LB M Q B ⊓ Y).inv_mem hy, by simp [MulAut.conj_apply]⟩
    rw [hKnorm k hk] at hmem
    have e : ⁅y, k⁆ = y * (k * y⁻¹ * k⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (LB M Q B ⊓ Y).mul_mem hy hmem
  have hcongr : ∀ k ∈ conjSubgroup h (LB M Q B ⊓ X) ⊓
      Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G), ∀ q ∈ Q,
      ⁅y, k⁆⁻¹ * ⁅y, k * q⁆ ∈ Q := by
    intro k hk q hq
    have hkM : k ∈ M := hLFM (Subgroup.map_mono inf_le_left hk.1)
    have e : ⁅y, k⁆⁻¹ * ⁅y, k * q⁆ = k * ⁅y, q⁆ * k⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have hyq : ⁅y, q⁆ ∈ Q := by
      have h5 := (Subgroup.mem_normalizer_iff.mp (hQn hyM) q).mp hq
      have e5 : ⁅y, q⁆ = (y * q * y⁻¹) * q⁻¹ := by
        simp only [commutatorElement_def]
      rw [e5]
      exact Q.mul_mem h5 (Q.inv_mem hq)
    exact (Subgroup.mem_normalizer_iff.mp (hQn hkM) _).mp hyq
  have hinj : ∀ k₁ ∈ conjSubgroup h (LB M Q B ⊓ X) ⊓
      Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G),
      ∀ k₂ ∈ conjSubgroup h (LB M Q B ⊓ X) ⊓
        Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G),
      ⁅y, k₁⁆⁻¹ * ⁅y, k₂⁆ ∈ Q → k₁⁻¹ * k₂ ∈ Q := by
    intro k₁ hk₁ k₂ hk₂ hc12
    have hkK : k₁⁻¹ * k₂ ∈ conjSubgroup h (LB M Q B ⊓ X) ⊓
        Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G) :=
      (conjSubgroup h (LB M Q B ⊓ X) ⊓
        Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G)).mul_mem
        (Subgroup.inv_mem _ hk₁) hk₂
    have hk₁M : k₁ ∈ M := hLFM (Subgroup.map_mono inf_le_left hk₁.1)
    have e : ⁅y, k₁⁆⁻¹ * ⁅y, k₂⁆ = k₁ * ⁅y, k₁⁻¹ * k₂⁆ * k₁⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e] at hc12
    have hycomm : ⁅y, k₁⁻¹ * k₂⁆ ∈ Q := by
      have h5 := (Subgroup.mem_normalizer_iff.mp (hQn (M.inv_mem hk₁M)) _).mp hc12
      simpa [mul_assoc] using h5
    set k := k₁⁻¹ * k₂ with hkdef
    have hkLF : k ∈ LB M Q (conjSubgroup h B) := by
      rw [hLF]
      exact Subgroup.map_mono inf_le_left hkK.1
    have hyk : y * k * y⁻¹ ∈ conjSubgroup y (LB M Q (conjSubgroup h B)) :=
      ⟨k, hkLF, by simp [MulAut.conj_apply]⟩
    have hykF : y * k * y⁻¹ ∈ LB M Q (conjSubgroup h B) := by
      have e2 : y * k * y⁻¹ = ⁅y, k⁆ * k := by
        simp only [commutatorElement_def]
        group
      rw [e2]
      exact (LB M Q (conjSubgroup h B)).mul_mem (Subgroup.mem_sup_left hycomm) hkLF
    have hykL := mem_LB_of_mem_conj_swap hc hh hFB hne hy.1 hyN hykF hyk
    have hkL : k ∈ LB M Q B := by
      have e3 : k = y⁻¹ * (y * k * y⁻¹) * y := by group
      rw [e3]
      exact (LB M Q B).mul_mem ((LB M Q B).mul_mem ((LB M Q B).inv_mem hy.1) hykL) hy.1
    by_contra hkQ
    have hxE : h⁻¹ * k * h ∈ LB M Q B ⊓ X := mem_conjSubgroup.mp hkK.1
    have hxQ : h⁻¹ * k * h ∉ Q := by
      intro hxQ'
      apply hkQ
      have : h * (h⁻¹ * k * h) * h⁻¹ ∈ conjSubgroup h Q := ⟨_, hxQ', by simp [MulAut.conj_apply]⟩
      rw [hQh, show h * (h⁻¹ * k * h) * h⁻¹ = k by group] at this
      exact this
    apply (hhard _ hxE hxQ).1
    rw [show h * (h⁻¹ * k * h) * h⁻¹ = k by group]
    exact hkL
  have hle := relIndex_le_of_commutator_injective (R := Q) (Q := Q) y hmap hcongr hinj
  have hge := relIndex_kappaBar_ge h34 hc hs hsplit h4 h2 hh hα
  have hSrel : Q.relIndex (LB M Q B ⊓ Y) = Nat.card Z := h4.2.1
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hpow : Nat.card Z ^ 2 ≤ Nat.card Z ^ (n - 3) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : Nat.card Z ^ (n - 3) ≤ Nat.card Z := hge.trans (hle.trans hSrel.le)
  nlinarith

theorem conj_LB_eq_of_comm_mem_Z (hc : Ctx M Q Z B) {x p : G} (hxM : x ∈ M) (hpB : p ∈ B)
    (hp1 : p ≠ 1) (hxp : ⁅x, p⁆ ∈ Z) : conjSubgroup x (LB M Q B) = LB M Q B := by
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  obtain ⟨q, hq, hqe⟩ := exists_conj_eq_mul hc hxp hpB hp1
  have hqM : q ∈ M := hQM hq
  have hxe : x * p * x⁻¹ = ⁅x, p⁆ * p := by
    simp only [commutatorElement_def]
    group
  have hxmem : ⁅x, p⁆ * p ∈ conjSubgroup x B := ⟨p, hpB, by simp [MulAut.conj_apply, hxe]⟩
  have hqmem : ⁅x, p⁆ * p ∈ conjSubgroup q B := ⟨p, hpB, by simp [MulAut.conj_apply, ← hqe]⟩
  have hne1 : ⁅x, p⁆ * p ≠ 1 := by
    intro h1
    apply hp1
    rw [← hxe] at h1
    have : p = x⁻¹ * (x * p * x⁻¹) * x := by group
    rw [this, h1]
    group
  have hne : conjSubgroup x B ⊓ conjSubgroup q B ≠ ⊥ := by
    intro h0
    have hmem : ⁅x, p⁆ * p ∈ conjSubgroup x B ⊓ conjSubgroup q B := ⟨hxmem, hqmem⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact hne1 hmem
  obtain ⟨gx, hgx⟩ := (hc.conj_of_mem hxM).conj
  obtain ⟨gq, hgq⟩ := (hc.conj_of_mem hqM).conj
  have heq : conjSubgroup x B = conjSubgroup q B :=
    eq_of_inf_ne_bot_conj hc.hyp.ti ⟨gx, hgx⟩ ⟨gq, hgq⟩ hne
  have hle : conjSubgroup x B ≤ B ⊔ Z := by
    rw [heq]
    have h1 : conjSubgroup q (Z ⊔ B) = Z ⊔ B :=
      conjSubgroup_eq_self_iff.mpr (Smith81.Ctx.Q_le_normalizer_ZB hc hq)
    calc conjSubgroup q B ≤ conjSubgroup q (Z ⊔ B) := Subgroup.map_mono le_sup_right
      _ = Z ⊔ B := h1
      _ = B ⊔ Z := sup_comm _ _
  exact hc.conj_LB_eq_of_le_sup_Z hxM hle

theorem relIndex_normalizer_LB_le (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M)
    (hFB : conjSubgroup h B ≤ QB B) :
    (Subgroup.normalizer (LB M Q (conjSubgroup h B) : Set G)).relIndex (LB M Q B) ≤
      Nat.card Z := by
  classical
  have hcF : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  obtain ⟨f₀, hf₀F, hf₀1⟩ := exists_ne_one_mem hcF
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hZn : M ≤ Subgroup.normalizer (Z : Set G) := hc.hyp.Z_normal.2
  have hLM : LB M Q B ≤ M := hc.LB_le_M
  have hf₀QB : f₀ ∈ Q ⊓ QB B := ⟨hcF.le hf₀F, hFB hf₀F⟩
  let K₁ : Subgroup G :=
    { carrier := {x | x ∈ LB M Q B ∧ ⁅x, f₀⁆ ∈ Z}
      mul_mem' := by
        rintro x y ⟨hx, hxf⟩ ⟨hy, hyf⟩
        refine ⟨(LB M Q B).mul_mem hx hy, ?_⟩
        have e : ⁅x * y, f₀⁆ = (x * ⁅y, f₀⁆ * x⁻¹) * ⁅x, f₀⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hZn (hLM hx)) _).mp hyf) hxf
      one_mem' := ⟨(LB M Q B).one_mem, by simpa [commutatorElement_def] using Z.one_mem⟩
      inv_mem' := by
        rintro x ⟨hx, hxf⟩
        refine ⟨(LB M Q B).inv_mem hx, ?_⟩
        have e : ⁅x⁻¹, f₀⁆ = x⁻¹ * ⁅x, f₀⁆⁻¹ * x := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have h5 := (Subgroup.mem_normalizer_iff.mp (hZn (M.inv_mem (hLM hx))) _).mp
          (Z.inv_mem hxf)
        simpa using h5 }
  have hK₁N : K₁ ≤ Subgroup.normalizer (LB M Q (conjSubgroup h B) : Set G) := fun x hx =>
    conjSubgroup_eq_self_iff.mp (conj_LB_eq_of_comm_mem_Z hcF (hLM hx.1) hf₀F hf₀1 hx.2)
  have hmap : ∀ x ∈ LB M Q B, ⁅f₀, x⁆ ∈ Z ⊔ B := by
    intro x hx
    have h1 : ⁅x, f₀⁆ ∈ Z ⊔ B := hc.comm_LB_inf_QB_mem_sup hx hf₀QB
    have e : ⁅f₀, x⁆ = ⁅x, f₀⁆⁻¹ := by rw [commutatorElement_inv]
    rw [e]
    exact (Z ⊔ B).inv_mem h1
  have hcongr : ∀ x ∈ LB M Q B, ∀ r ∈ K₁, ⁅f₀, x⁆⁻¹ * ⁅f₀, x * r⁆ ∈ Z := by
    intro x hx r hr
    have e : ⁅f₀, x⁆⁻¹ * ⁅f₀, x * r⁆ = x * ⁅f₀, r⁆ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have e2 : ⁅f₀, r⁆ = ⁅r, f₀⁆⁻¹ := by rw [commutatorElement_inv]
    rw [e2]
    exact (Subgroup.mem_normalizer_iff.mp (hZn (hLM hx)) _).mp (Z.inv_mem hr.2)
  have hinj : ∀ x₁ ∈ LB M Q B, ∀ x₂ ∈ LB M Q B, ⁅f₀, x₁⁆⁻¹ * ⁅f₀, x₂⁆ ∈ Z →
      x₁⁻¹ * x₂ ∈ K₁ := by
    intro x₁ hx₁ x₂ hx₂ h12
    refine ⟨(LB M Q B).mul_mem ((LB M Q B).inv_mem hx₁) hx₂, ?_⟩
    have e : ⁅f₀, x₁⁆⁻¹ * ⁅f₀, x₂⁆ = x₁ * ⁅f₀, x₁⁻¹ * x₂⁆ * x₁⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e] at h12
    have h5 := (Subgroup.mem_normalizer_iff.mp (hZn (M.inv_mem (hLM hx₁))) _).mp h12
    have h6 : ⁅f₀, x₁⁻¹ * x₂⁆ ∈ Z := by simpa [mul_assoc] using h5
    have e2 : ⁅x₁⁻¹ * x₂, f₀⁆ = ⁅f₀, x₁⁻¹ * x₂⁆⁻¹ := by rw [commutatorElement_inv]
    rw [e2]
    exact Z.inv_mem h6
  have hcount : K₁.relIndex (LB M Q B) ≤ Z.relIndex (Z ⊔ B) :=
    relIndex_le_of_commutator_injective (R := K₁) (K := LB M Q B) (Q := Z) (S := Z ⊔ B) f₀ hmap
      hcongr hinj
  have hBn : B ≤ Subgroup.normalizer (Z : Set G) := fun b hb => hZn (hQM (hc.le hb))
  have hZB : Z.relIndex (Z ⊔ B) = Nat.card Z := by
    rw [sup_comm, relIndex_sup_right_of_le_normalizer hBn]
    have h7 := Subgroup.relIndex_mul_card (H := Z) (K := B)
    rw [hc.inf_eq_bot, Subgroup.card_bot, mul_one] at h7
    rw [h7]
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg, card_conjSubgroup]
  have hdvd := Subgroup.relIndex_dvd_of_le_left (LB M Q B) hK₁N
  rw [hZB] at hcount
  exact (Nat.le_of_dvd (relIndex_pos' _ _) hdvd).trans hcount

theorem relIndex_normalizer_LB_le_swap (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M)
    (hFB : conjSubgroup h B ≤ QB B) (hne : conjSubgroup h B ≠ B) :
    (Subgroup.normalizer (LB M Q B : Set G)).relIndex (LB M Q (conjSubgroup h B)) ≤
      Nat.card Z := by
  have hBF : B ≤ QB (conjSubgroup h B) := le_QB_of_conj_le_QB hc hh hFB hne
  have h1 := relIndex_normalizer_LB_le (hc.conj_of_mem hh) (M.inv_mem hh)
    (by rw [conjSubgroup_inv_conj_self]; exact hBF)
  rwa [conjSubgroup_inv_conj_self] at h1

theorem conj_ne_of_hard (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y) {h : G} (hh : h ∈ M)
    (hhard : ∀ x ∈ LB M Q B ⊓ X, x ∉ Q →
      h * x * h⁻¹ ∉ LB M Q B ∧ x ∉ conjSubgroup h (LB M Q B)) :
    conjSubgroup h B ≠ B := by
  intro heq
  obtain ⟨x, hxE, hxQ⟩ := exists_mem_E_not_Q h34 hc hs hsplit h4
  apply (hhard x hxE hxQ).1
  have hmem : h * x * h⁻¹ ∈ conjSubgroup h (LB M Q B) :=
    ⟨x, hxE.1, by simp [MulAut.conj_apply]⟩
  rw [← hc.LB_conj hh, heq] at hmem
  exact hmem

theorem S_normalizes_LF_of_hard (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) (hn5 : 5 ≤ n) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) (h1 : OneConcl hc X Y)
    (h2 : TwoConcl M Q B X) {h : G} (hh : h ∈ M) (hFB : conjSubgroup h B ≤ QB B)
    (hhard : ∀ x ∈ LB M Q B ⊓ X, x ∉ Q →
      h * x * h⁻¹ ∉ LB M Q B ∧ x ∉ conjSubgroup h (LB M Q B)) :
    ∀ y ∈ LB M Q B ⊓ Y,
      conjSubgroup y (LB M Q (conjSubgroup h B)) = LB M Q (conjSubgroup h B) :=
  S_normalizes_LF h34 hc hs hn5 hsplit h4 h1 h2 hh hFB hhard
    (relIndex_normalizer_LB_le_swap hc hh hFB (conj_ne_of_hard h34 hc hs hsplit h4 hh hhard))

end HS9

end CFSG.RankThree.GF2n.Stroth80
