module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]

namespace IsoAux

abbrev sg (c x : G) : G := c * x * c⁻¹

abbrev pim (c x : G) : G := x * sg c x * sg c (sg c x)

lemma sg_mem {S : Subgroup G} {c : G} (hc : c ∈ Subgroup.normalizer (S : Set G)) {x : G}
    (hx : x ∈ S) : sg c x ∈ S :=
  (Subgroup.mem_normalizer_iff.1 hc x).1 hx

lemma sg_mul (c x y : G) : sg c (x * y) = sg c x * sg c y := by
  simp only [sg]; group

lemma sg_three {c : G} (hc : c ^ 3 = 1) (x : G) : sg c (sg c (sg c x)) = x := by
  have hc' : c * c * c = 1 := by simpa [pow_succ] using hc
  have h : sg c (sg c (sg c x)) = c * c * c * x * (c * c * c)⁻¹ := by simp only [sg]; group
  rw [h, hc']; simp

lemma comm3 {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {a b d : G} (ha : a ∈ S)
    (hb : b ∈ S) (hd : d ∈ S) : a * b * d = b * d * a := by
  rw [hcm a ha b hb, mul_assoc, hcm a ha d hd, ← mul_assoc]

lemma pim_mem {S : Subgroup G} {c : G} (hc : c ∈ Subgroup.normalizer (S : Set G)) {x : G}
    (hx : x ∈ S) : pim c x ∈ S :=
  mul_mem (mul_mem hx (sg_mem hc hx)) (sg_mem hc (sg_mem hc hx))

lemma pim_fix {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {c : G}
    (hc : c ∈ Subgroup.normalizer (S : Set G)) (hc3 : c ^ 3 = 1) {x : G} (hx : x ∈ S) :
    sg c (pim c x) = pim c x := by
  have h1 : sg c (pim c x) = sg c x * sg c (sg c x) * sg c (sg c (sg c x)) := by
    simp only [pim, sg]; group
  have hs1 := sg_mem hc hx
  have hs2 := sg_mem hc hs1
  rw [h1, sg_three hc3]
  exact (comm3 hcm hx hs1 hs2).symm

lemma phi_mul {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {c : G}
    (hc : c ∈ Subgroup.normalizer (S : Set G)) {x y : G} (hx : x ∈ S) (hy : y ∈ S) :
    (x * y)⁻¹ * sg c (x * y) = (x⁻¹ * sg c x) * (y⁻¹ * sg c y) := by
  have hx' : x⁻¹ ∈ S := inv_mem hx
  have hy' : y⁻¹ ∈ S := inv_mem hy
  have hsx := sg_mem hc hx
  have hsy := sg_mem hc hy
  rw [mul_inv_rev, sg_mul]
  calc y⁻¹ * x⁻¹ * (sg c x * sg c y) = x⁻¹ * y⁻¹ * (sg c x * sg c y) := by
        rw [hcm _ hy' _ hx']
    _ = x⁻¹ * (y⁻¹ * sg c x) * sg c y := by simp only [mul_assoc]
    _ = x⁻¹ * (sg c x * y⁻¹) * sg c y := by rw [hcm _ hy' _ hsx]
    _ = (x⁻¹ * sg c x) * (y⁻¹ * sg c y) := by simp only [mul_assoc]

noncomputable def phiHom (S : Subgroup G) (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {c : G}
    (hc : c ∈ Subgroup.normalizer (S : Set G)) : S →* G where
  toFun x := (x : G)⁻¹ * sg c x
  map_one' := by simp [sg]
  map_mul' x y := phi_mul hcm hc x.2 y.2

lemma phiHom_apply {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {c : G}
    (hc : c ∈ Subgroup.normalizer (S : Set G)) (x : S) :
    phiHom S hcm hc x = (x : G)⁻¹ * sg c x := by
  simp only [phiHom, MonoidHom.coe_mk, OneHom.coe_mk]

lemma phiHom_eq_one_iff {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {c : G}
    (hc : c ∈ Subgroup.normalizer (S : Set G)) (x : S) :
    phiHom S hcm hc x = 1 ↔ c * (x : G) = (x : G) * c := by
  rw [phiHom_apply, inv_mul_eq_one, sg, eq_comm, mul_inv_eq_iff_eq_mul]

lemma sg2_eq {c : G} (hcc : c * c * c = 1) (s : G) : sg c (sg c s) = c⁻¹ * s * c := by
  have hcinv : c⁻¹ = c * c := (eq_inv_of_mul_eq_one_left hcc).symm
  have hc2 : c⁻¹ * c⁻¹ = c := by
    rw [hcinv]
    calc c * c * (c * c) = (c * c * c) * c := by group
      _ = c := by rw [hcc, one_mul]
  simp only [sg]
  calc c * (c * s * c⁻¹) * c⁻¹ = c * c * s * (c⁻¹ * c⁻¹) := by group
    _ = c⁻¹ * s * c := by rw [hc2, hcinv]

lemma comm_c {S : Subgroup G} (hsq : ∀ x ∈ S, x * x = 1) {c : G} {s : G} (hs : s ∈ S) :
    s * c * s⁻¹ * c⁻¹ = s⁻¹ * sg c s := by
  have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (hsq s hs)
  rw [hinv]
  simp only [sg]
  group

lemma comm_cinv {S : Subgroup G} (hsq : ∀ x ∈ S, x * x = 1) {c : G} (hcc : c * c * c = 1)
    {s : G} (hs : s ∈ S) :
    s * c⁻¹ * s⁻¹ * c⁻¹⁻¹ = s * sg c (sg c s) := by
  have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (hsq s hs)
  rw [inv_inv, hinv, sg2_eq hcc]
  group

lemma phi_comm_t {S : Subgroup G} (hsq : ∀ x ∈ S, x * x = 1) {c : G}
    (hc : c ∈ Subgroup.normalizer (S : Set G)) {s : G} (hs : s ∈ S) :
    (s * sg c s)⁻¹ * sg c (s * sg c s) = s * sg c (sg c s) := by
  have hu : sg c s ∈ S := sg_mem hc hs
  have ht : s * sg c s ∈ S := mul_mem hs hu
  have huu : sg c s * (sg c s * sg c (sg c s)) = sg c (sg c s) := by
    rw [← mul_assoc, hsq _ hu, one_mul]
  rw [inv_eq_of_mul_eq_one_right (hsq _ ht), sg_mul, mul_assoc s (sg c s), huu]

lemma range_le_comm {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c : G} (hc : c ∈ Subgroup.normalizer (S : Set G)) :
    (phiHom S hcm hc).range ≤ ⁅S, Subgroup.zpowers c⁆ := by
  rintro _ ⟨t, rfl⟩
  have ht : (t : G) ∈ S := t.2
  rw [phiHom_apply, ← comm_c hsq ht]
  exact Subgroup.commutator_mem_commutator ht (Subgroup.mem_zpowers c)

lemma comm_mem_range {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c : G} (hc : c ∈ Subgroup.normalizer (S : Set G))
    (hc3 : c ^ 3 = 1) {s : G} (hs : s ∈ S) {g : G} (hg : g ∈ Subgroup.zpowers c) :
    s * g * s⁻¹ * g⁻¹ ∈ (phiHom S hcm hc).range := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have hcc : c * c * c = 1 := by simpa [pow_succ] using hc3
  have h3 : c ^ (3 : ℤ) = 1 := by simpa using hc3
  rw [zpow_eq_zpow_emod k h3]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h <;> rw [h]
  · simp
  · rw [zpow_one]
    exact ⟨⟨s, hs⟩, by rw [phiHom_apply]; exact (comm_c hsq hs).symm⟩
  · have h2 : c ^ (2 : ℤ) = c⁻¹ := by
      rw [zpow_ofNat, pow_two]
      exact eq_inv_of_mul_eq_one_left hcc
    rw [h2]
    refine ⟨⟨s * sg c s, mul_mem hs (sg_mem hc hs)⟩, ?_⟩
    rw [phiHom_apply]
    exact (phi_comm_t hsq hc hs).trans (comm_cinv hsq hcc hs).symm

lemma commutator_zpowers_eq_range {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c : G} (hc : c ∈ Subgroup.normalizer (S : Set G))
    (hc3 : c ^ 3 = 1) :
    ⁅S, Subgroup.zpowers c⁆ = (phiHom S hcm hc).range :=
  le_antisymm
    (Subgroup.commutator_le.2 fun _ hg₁ _ hg₂ => comm_mem_range hcm hsq hc hc3 hg₁ hg₂)
    (range_le_comm hcm hsq hc)

lemma ker_map_eq {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {c : G}
    (hc : c ∈ Subgroup.normalizer (S : Set G)) :
    (phiHom S hcm hc).ker.map S.subtype = S ⊓ Cen c := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : phiHom S hcm hc y = 1 := hy
    rw [phiHom_eq_one_iff hcm hc] at hy'
    exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.2 hy'.symm⟩
  · rintro ⟨hxS, hxc⟩
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    show phiHom S hcm hc ⟨x, hxS⟩ = 1
    rw [phiHom_eq_one_iff hcm hc]
    exact (Subgroup.mem_centralizer_singleton_iff.1 hxc).symm

lemma card_comm_mul {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c : G} (hc : c ∈ Subgroup.normalizer (S : Set G))
    (hc3 : c ^ 3 = 1) :
    Nat.card ↥(⁅S, Subgroup.zpowers c⁆) * Nat.card ↥(S ⊓ Cen c) = Nat.card S := by
  have hker : Nat.card (phiHom S hcm hc).ker = Nat.card ↥(S ⊓ Cen c) := by
    rw [← ker_map_eq hcm hc]
    exact (Subgroup.card_map_of_injective S.subtype_injective).symm
  rw [commutator_zpowers_eq_range hcm hsq hc hc3, ← hker, mul_comm]
  exact Subgroup.card_ker_mul_card_range (phiHom S hcm hc)

lemma perm_aux {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {x y p q r s : G}
    (hx : x ∈ S) (hy : y ∈ S) (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) (hs : s ∈ S) :
    x * y * (p * r) * (q * s) = x * p * q * (y * r * s) := by
  have sw : ∀ {a b : G}, a ∈ S → b ∈ S → ∀ X : G, a * (b * X) = b * (a * X) := by
    intro a b ha hb X
    rw [← mul_assoc, hcm a ha b hb, mul_assoc]
  calc x * y * (p * r) * (q * s) = x * (y * (p * (r * (q * s)))) := by simp only [mul_assoc]
    _ = x * (p * (y * (r * (q * s)))) := by rw [sw hy hp]
    _ = x * (p * (r * (y * (q * s)))) := by rw [sw hy hr]
    _ = x * (p * (r * (q * (y * s)))) := by rw [sw hy hq]
    _ = x * (p * (q * (r * (y * s)))) := by rw [sw hr hq]
    _ = x * (p * (q * (y * (r * s)))) := by rw [sw hr hy]
    _ = x * p * q * (y * r * s) := by simp only [mul_assoc]

lemma pim_mul {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {c : G}
    (hc : c ∈ Subgroup.normalizer (S : Set G)) {x y : G} (hx : x ∈ S) (hy : y ∈ S) :
    pim c (x * y) = pim c x * pim c y := by
  have hp := sg_mem hc hx
  have hq := sg_mem hc hp
  have hr := sg_mem hc hy
  have hs := sg_mem hc hr
  have e1 : pim c (x * y) = x * y * (sg c x * sg c y) * (sg c (sg c x) * sg c (sg c y)) := by
    show (x * y) * sg c (x * y) * sg c (sg c (x * y)) = _
    rw [sg_mul, sg_mul]
  rw [e1]
  exact perm_aux hcm hx hy hp hq hr hs

lemma commute_sg {d e x : G} (hde : Commute d e) (hdx : Commute d x) :
    Commute d (sg e x) :=
  (hde.mul_right hdx).mul_right hde.inv_right

lemma pim_commute {d e x : G} (hde : Commute d e) (hdx : Commute d x) :
    Commute d (pim e x) :=
  (hdx.mul_right (commute_sg hde hdx)).mul_right (commute_sg hde (commute_sg hde hdx))

lemma commute_of_sg {e y : G} (h : e * y * e⁻¹ = y) : Commute e y := by
  show e * y = y * e
  calc e * y = e * y * e⁻¹ * e := by group
    _ = y * e := by rw [h]

lemma commute_of_mem_cen {c x : G} (h : x ∈ Cen c) : Commute c x :=
  (Subgroup.mem_centralizer_singleton_iff.1 h).symm

lemma pim_of_fix {S : Subgroup G} (hsq : ∀ x ∈ S, x * x = 1) {c y : G} (hy : y ∈ S)
    (h : sg c y = y) : pim c y = y := by
  show y * sg c y * sg c (sg c y) = y
  rw [h, h, hsq y hy, one_mul]

lemma pim_ker {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c x : G} (hc : c ∈ Subgroup.normalizer (S : Set G))
    (hx : x ∈ S) (h : pim c x = 1) : x ∈ ⁅S, Subgroup.zpowers c⁆ := by
  have hsx := sg_mem hc hx
  have hinv : (sg c x)⁻¹ = sg c x := inv_eq_of_mul_eq_one_right (hsq _ hsx)
  have hx2 : sg c x * sg c (sg c x) = x := by
    have h' : x * (sg c x * sg c (sg c x)) = 1 := by
      rw [← mul_assoc]
      exact h
    exact (inv_eq_of_mul_eq_one_right h').symm.trans (inv_eq_of_mul_eq_one_right (hsq x hx))
  refine range_le_comm hcm hsq hc (MonoidHom.mem_range.2 ⟨⟨sg c x, hsx⟩, ?_⟩)
  rw [phiHom_apply]
  show (sg c x)⁻¹ * sg c (sg c x) = x
  rw [hinv, hx2]

lemma pim_cancel {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {c : G}
    (hc : c ∈ Subgroup.normalizer (S : Set G)) {x y : G} (hx : x ∈ S) (hy : y ∈ S)
    (hfy : pim c y = y) (hxy : pim c x = y) : pim c (x * y⁻¹) = 1 := by
  have hy' : y⁻¹ ∈ S := inv_mem hy
  have hxy' : x * y⁻¹ ∈ S := mul_mem hx hy'
  have h1 := pim_mul hcm hc hxy' hy
  rw [inv_mul_cancel_right, hxy, hfy] at h1
  exact mul_right_cancel (by rw [one_mul]; exact h1.symm)

lemma closure_commute {A : Set G} {w : G} (h : ∀ g ∈ A, Commute g w) :
    ∀ g ∈ Subgroup.closure A, Commute g w := by
  intro g hg
  have hle : Subgroup.closure A ≤ Subgroup.centralizer {w} := by
    rw [Subgroup.closure_le]
    intro g' hg'
    exact Subgroup.mem_centralizer_singleton_iff.2 (h g' hg')
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

lemma cen_of_gen {B : Subgroup G} {b b₁ b₂ y : G} (hB : B = Subgroup.closure {b, b₁, b₂})
    (h : ∀ g ∈ ({b, b₁, b₂} : Set G), Commute g y) : y ∈ CenS B := by
  show y ∈ Subgroup.centralizer (B : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [hB] at hg
  exact closure_commute h g hg

lemma inter_le_W {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c d e : G} (hen : e ∈ Subgroup.normalizer (S : Set G))
    (he3 : e ^ 3 = 1) (hce : Commute c e) (hde : Commute d e)
    (hfix : ∀ y ∈ S, Commute c y → Commute d y → Commute e y → y = 1)
    {x : G} (hx : x ∈ S) (hcx : Commute c x) (hdx : Commute d x) :
    x ∈ ⁅S, Subgroup.zpowers e⁆ := by
  have hy : pim e x ∈ S := pim_mem hen hx
  have hey : Commute e (pim e x) := commute_of_sg (pim_fix hcm hen he3 hx)
  have h1 : pim e x = 1 :=
    hfix _ hy (pim_commute hce hcx) (pim_commute hde hdx) hey
  exact pim_ker hcm hsq hen hx h1

lemma sg_of_commute {c x : G} (h : Commute c x) : sg c x = x := by
  show c * x * c⁻¹ = x
  calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [h.eq]
    _ = x := by group

lemma cardW {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c : G} (hc : c ∈ Subgroup.normalizer (S : Set G))
    (hc3 : c ^ 3 = 1) (hcc : Nat.card ↥(S ⊓ Cen c) = 16) (hS : Nat.card S = 64) :
    Nat.card ↥⁅S, Subgroup.zpowers c⁆ = 4 := by
  have h := card_comm_mul hcm hsq hc hc3
  rw [hcc, hS] at h
  omega

lemma W_le_S {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c : G} (hc : c ∈ Subgroup.normalizer (S : Set G))
    (hc3 : c ^ 3 = 1) : ⁅S, Subgroup.zpowers c⁆ ≤ S := by
  rw [commutator_zpowers_eq_range hcm hsq hc hc3]
  rintro _ ⟨t, rfl⟩
  rw [phiHom_apply]
  exact mul_mem (inv_mem t.2) (sg_mem hc t.2)

lemma inter_eq_W {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c d e : G} (hen : e ∈ Subgroup.normalizer (S : Set G))
    (he3 : e ^ 3 = 1) (hce : Commute c e) (hde : Commute d e)
    (hfix : ∀ y ∈ S, Commute c y → Commute d y → Commute e y → y = 1)
    (hWe : Nat.card ↥⁅S, Subgroup.zpowers e⁆ = 4) (hc : Nat.card ↥(S ⊓ Cen c) = 16)
    (hd : Nat.card ↥(S ⊓ Cen d) = 16) (hS : Nat.card S = 64) :
    (S ⊓ Cen c) ⊓ (S ⊓ Cen d) = ⁅S, Subgroup.zpowers e⁆ := by
  have hle : (S ⊓ Cen c) ⊓ (S ⊓ Cen d) ≤ ⁅S, Subgroup.zpowers e⁆ := by
    intro x hx
    exact inter_le_W hcm hsq hen he3 hce hde hfix hx.1.1 (commute_of_mem_cen hx.1.2)
      (commute_of_mem_cen hx.2.2)
  have hA := Subgroup.relIndex_mul_card (H := S ⊓ Cen c) (K := S)
  have hcS : (S ⊓ Cen c) ⊓ S = S ⊓ Cen c := inf_eq_left.2 inf_le_left
  rw [hcS, hc, hS] at hA
  have hrel1 : (S ⊓ Cen c).relIndex S = 4 := by omega
  have hA' := Subgroup.relIndex_mul_card (H := S ⊓ Cen d) (K := S)
  have hdS : (S ⊓ Cen d) ⊓ S = S ⊓ Cen d := inf_eq_left.2 inf_le_left
  rw [hdS, hd, hS] at hA'
  have hrel2 : (S ⊓ Cen d).relIndex S = 4 := by omega
  have hA2 := Subgroup.relIndex_inf_le (H := S ⊓ Cen c) (K := S ⊓ Cen d) (L := S)
  rw [hrel1, hrel2] at hA2
  have hB2 := Subgroup.relIndex_mul_card (H := (S ⊓ Cen c) ⊓ (S ⊓ Cen d)) (K := S)
  have hsub2 : ((S ⊓ Cen c) ⊓ (S ⊓ Cen d)) ⊓ S = (S ⊓ Cen c) ⊓ (S ⊓ Cen d) :=
    inf_eq_left.2 (inf_le_left.trans inf_le_left)
  rw [hsub2, hS] at hB2
  have hk : 4 ≤ Nat.card ↥((S ⊓ Cen c) ⊓ (S ⊓ Cen d)) := by
    by_contra hk
    have hk3 : Nat.card ↥((S ⊓ Cen c) ⊓ (S ⊓ Cen d)) ≤ 3 := by omega
    have hmul := Nat.mul_le_mul hA2 hk3
    rw [hB2] at hmul
    norm_num at hmul
  have hWle : Nat.card ↥⁅S, Subgroup.zpowers e⁆ ≤ Nat.card ↥((S ⊓ Cen c) ⊓ (S ⊓ Cen d)) := by
    rw [hWe]
    exact hk
  exact Subgroup.eq_of_le_of_card_ge hle hWle

lemma fix_of_B {S B : Subgroup G} {b b₁ b₂ : G} (hC : S ⊓ CenS B = ⊥)
    (hgen : B = Subgroup.closure {b, b₁, b₂}) {y : G} (hy : y ∈ S)
    (h : ∀ g ∈ ({b, b₁, b₂} : Set G), Commute g y) : y = 1 := by
  have hm : y ∈ S ⊓ CenS B := ⟨hy, cen_of_gen hgen h⟩
  rw [hC] at hm
  exact Subgroup.mem_bot.1 hm

lemma join_mem {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {b b₁ b₂ : G} (hb : b ∈ Subgroup.normalizer (S : Set G))
    (hb1 : b₁ ∈ Subgroup.normalizer (S : Set G)) (hb3 : b ^ 3 = 1) (hb13 : b₁ ^ 3 = 1)
    (hbb1 : Commute b b₁) (hb2b1 : Commute b₂ b₁) (hb2b : Commute b₂ b)
    (hfix1 : ∀ y ∈ S, Commute b y → Commute b₂ y → Commute b₁ y → y = 1) :
    ∀ z ∈ S, Commute b₂ z → z ∈ ⁅S, Subgroup.zpowers b⁆ ⊔ ⁅S, Subgroup.zpowers b₁⁆ := by
  intro z hz hzc
  have hw1S : pim b z ∈ S := pim_mem hb hz
  have hbw : Commute b (pim b z) := commute_of_sg (pim_fix hcm hb hb3 hz)
  have hb2w : Commute b₂ (pim b z) := pim_commute hb2b hzc
  have hw1 : pim b z ∈ ⁅S, Subgroup.zpowers b₁⁆ :=
    inter_le_W hcm hsq hb1 hb13 hbb1 hb2b1 hfix1 hw1S hbw hb2w
  have hfixw : pim b (pim b z) = pim b z := pim_of_fix hsq hw1S (sg_of_commute hbw)
  have hcancel : pim b (z * (pim b z)⁻¹) = 1 := pim_cancel hcm hb hz hw1S hfixw rfl
  have hw0 : z * (pim b z)⁻¹ ∈ ⁅S, Subgroup.zpowers b⁆ :=
    pim_ker hcm hsq hb (mul_mem hz (inv_mem hw1S)) hcancel
  have key := Subgroup.mul_mem _ (Subgroup.mem_sup_left hw0) (Subgroup.mem_sup_right hw1)
  have e : z * (pim b z)⁻¹ * pim b z = z := by group
  rw [e] at key
  exact key

end IsoAux

open IsoAux

theorem B_isotypic {S B : Subgroup G} {b b₁ b₂ : G} (hS : IsElemAb 2 6 S) (hB : IsElemAb 3 3 B)
    (hBS : B ≤ Nor S) (hgen : B = Subgroup.closure {b, b₁, b₂})
    (h₀ : Nat.card ↥(S ⊓ Cen b) = 16) (h₁ : Nat.card ↥(S ⊓ Cen b₁) = 16)
    (h₂ : Nat.card ↥(S ⊓ Cen b₂) = 16) (hC : S ⊓ CenS B = ⊥) :
    Nat.card ↥⁅S, Subgroup.zpowers b⁆ = 4 ∧ Nat.card ↥⁅S, Subgroup.zpowers b₁⁆ = 4 ∧
      Nat.card ↥⁅S, Subgroup.zpowers b₂⁆ = 4 ∧
      ⁅S, Subgroup.zpowers b⁆ ⊔ ⁅S, Subgroup.zpowers b₁⁆ ⊔ ⁅S, Subgroup.zpowers b₂⁆ = S ∧
      ⁅S, Subgroup.zpowers b⁆ ≤ CenS (Subgroup.closure {b₁, b₂}) ∧
      ⁅S, Subgroup.zpowers b₁⁆ ≤ CenS (Subgroup.closure {b, b₂}) ∧
      ⁅S, Subgroup.zpowers b₂⁆ ≤ CenS (Subgroup.closure {b, b₁}) := by
  obtain ⟨hEA, hScard⟩ := hS
  obtain ⟨hBEA, -⟩ := hB
  have hS64 : Nat.card S = 64 := by rw [hScard]; norm_num
  haveI := hEA
  haveI := hBEA
  have hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : S) ⟨y, hy⟩)
  have hsq : ∀ x ∈ S, x * x = 1 := fun x hx => by
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := S) x hx
    rwa [pow_two] at h
  have hBcm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hcube : ∀ g ∈ B, g ^ 3 = 1 := fun g hg =>
    elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := B) g hg
  have hmemB : ∀ g ∈ ({b, b₁, b₂} : Set G), g ∈ B := by
    intro g hg
    rw [hgen]
    exact Subgroup.subset_closure hg
  have hbB : b ∈ B := hmemB b (by simp)
  have hb1B : b₁ ∈ B := hmemB b₁ (by simp)
  have hb2B : b₂ ∈ B := hmemB b₂ (by simp)
  have hn0 : b ∈ Nor S := hBS hbB
  have hn1 : b₁ ∈ Nor S := hBS hb1B
  have hn2 : b₂ ∈ Nor S := hBS hb2B
  have hb3 : b ^ 3 = 1 := hcube b hbB
  have hb13 : b₁ ^ 3 = 1 := hcube b₁ hb1B
  have hb23 : b₂ ^ 3 = 1 := hcube b₂ hb2B
  have hbb1 : Commute b b₁ := hBcm b hbB b₁ hb1B
  have hbb2 : Commute b b₂ := hBcm b hbB b₂ hb2B
  have hb1b2 : Commute b₁ b₂ := hBcm b₁ hb1B b₂ hb2B
  have hb1b : Commute b₁ b := hbb1.symm
  have hb2b : Commute b₂ b := hbb2.symm
  have hb2b1 : Commute b₂ b₁ := hb1b2.symm
  have hfix0 : ∀ y ∈ S, Commute b₁ y → Commute b₂ y → Commute b y → y = 1 := fun y hy h1 h2 h3 =>
    fix_of_B hC hgen hy (by intro g hg; rcases hg with rfl | rfl | rfl <;> assumption)
  have hfix1 : ∀ y ∈ S, Commute b y → Commute b₂ y → Commute b₁ y → y = 1 := fun y hy h1 h2 h3 =>
    fix_of_B hC hgen hy (by intro g hg; rcases hg with rfl | rfl | rfl <;> assumption)
  have hfix2 : ∀ y ∈ S, Commute b y → Commute b₁ y → Commute b₂ y → y = 1 := fun y hy h1 h2 h3 =>
    fix_of_B hC hgen hy (by intro g hg; rcases hg with rfl | rfl | rfl <;> assumption)
  have cW0 : Nat.card ↥⁅S, Subgroup.zpowers b⁆ = 4 := cardW hcm hsq hn0 hb3 h₀ hS64
  have cW1 : Nat.card ↥⁅S, Subgroup.zpowers b₁⁆ = 4 := cardW hcm hsq hn1 hb13 h₁ hS64
  have cW2 : Nat.card ↥⁅S, Subgroup.zpowers b₂⁆ = 4 := cardW hcm hsq hn2 hb23 h₂ hS64
  have hEq0 : (S ⊓ Cen b₁) ⊓ (S ⊓ Cen b₂) = ⁅S, Subgroup.zpowers b⁆ :=
    inter_eq_W hcm hsq hn0 hb3 hb1b hb2b hfix0 cW0 h₁ h₂ hS64
  have hEq1 : (S ⊓ Cen b) ⊓ (S ⊓ Cen b₂) = ⁅S, Subgroup.zpowers b₁⁆ :=
    inter_eq_W hcm hsq hn1 hb13 hbb1 hb2b1 hfix1 cW1 h₀ h₂ hS64
  have hEq2 : (S ⊓ Cen b) ⊓ (S ⊓ Cen b₁) = ⁅S, Subgroup.zpowers b₂⁆ :=
    inter_eq_W hcm hsq hn2 hb23 hbb2 hb1b2 hfix2 cW2 h₀ h₁ hS64
  have hjoin : ∀ x ∈ S, x ∈ (⁅S, Subgroup.zpowers b⁆ ⊔ ⁅S, Subgroup.zpowers b₁⁆) ⊔
      ⁅S, Subgroup.zpowers b₂⁆ := by
    intro x hx
    have hy : pim b₂ x ∈ S := pim_mem hn2 hx
    have hfy : sg b₂ (pim b₂ x) = pim b₂ x := pim_fix hcm hn2 hb23 hx
    have hy1 := join_mem hcm hsq hn0 hn1 hb3 hb13 hbb1 hb2b1 hb2b hfix1 (pim b₂ x) hy
      (commute_of_sg hfy)
    have hcan : pim b₂ (x * (pim b₂ x)⁻¹) = 1 :=
      pim_cancel hcm hn2 hx hy (pim_of_fix hsq hy hfy) rfl
    have hw2S : x * (pim b₂ x)⁻¹ ∈ S := mul_mem hx (inv_mem hy)
    have hw2 : x * (pim b₂ x)⁻¹ ∈ ⁅S, Subgroup.zpowers b₂⁆ := pim_ker hcm hsq hn2 hw2S hcan
    have hcomm' : x * (pim b₂ x)⁻¹ * pim b₂ x = pim b₂ x * (x * (pim b₂ x)⁻¹) :=
      hcm _ hw2S _ hy
    have hxe : x = pim b₂ x * (x * (pim b₂ x)⁻¹) := by
      rw [← hcomm']
      group
    have key := Subgroup.mul_mem _ (Subgroup.mem_sup_left hy1) (Subgroup.mem_sup_right hw2)
    rw [← hxe] at key
    exact key
  have hW0S := W_le_S hcm hsq hn0 hb3
  have hW1S := W_le_S hcm hsq hn1 hb13
  have hW2S := W_le_S hcm hsq hn2 hb23
  refine ⟨cW0, cW1, cW2, le_antisymm (sup_le (sup_le hW0S hW1S) hW2S) hjoin, ?_, ?_, ?_⟩
  · intro w hw
    rw [← hEq0] at hw
    show w ∈ Subgroup.centralizer ((Subgroup.closure ({b₁, b₂} : Set G) : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    refine closure_commute (A := ({b₁, b₂} : Set G)) (w := w) ?_
    intro g hg
    rcases hg with rfl | rfl
    · exact commute_of_mem_cen hw.1.2
    · exact commute_of_mem_cen hw.2.2
  · intro w hw
    rw [← hEq1] at hw
    show w ∈ Subgroup.centralizer ((Subgroup.closure ({b, b₂} : Set G) : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    refine closure_commute (A := ({b, b₂} : Set G)) (w := w) ?_
    intro g hg
    rcases hg with rfl | rfl
    · exact commute_of_mem_cen hw.1.2
    · exact commute_of_mem_cen hw.2.2
  · intro w hw
    rw [← hEq2] at hw
    show w ∈ Subgroup.centralizer ((Subgroup.closure ({b, b₁} : Set G) : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    refine closure_commute (A := ({b, b₁} : Set G)) (w := w) ?_
    intro g hg
    rcases hg with rfl | rfl
    · exact commute_of_mem_cen hw.1.2
    · exact commute_of_mem_cen hw.2.2

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
