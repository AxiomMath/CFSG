module

public import CFSG.RankThree.PartOne.F106.NoQD32NAOrb

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement

variable {X : Type} [Group X]

section Faithful

theorem quotient_center_comm {Y : Subgroup X}
    (hYcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1) :
    ∀ u v : ↥Y ⧸ Subgroup.center ↥Y, u * v = v * u := by
  intro u v
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective v
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_center_iff]
  intro g
  have h := hYcl (b : X)⁻¹ (Y.inv_mem b.2) (a : X)⁻¹ (Y.inv_mem a.2) g g.2
  have h' := commutatorElement_eq_one_iff_mul_comm.mp h
  have e : ((a : X) * b)⁻¹ * ((b : X) * a) = ⁅(b : X)⁻¹, (a : X)⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e]
  exact h'.symm

theorem quotient_center_exp {q : ℕ} {Y : Subgroup X} (hYexp : ∀ y ∈ Y, y ^ q = 1) :
    ∀ v : ↥Y ⧸ Subgroup.center ↥Y, v ^ q = 1 := by
  intro v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
  rw [← QuotientGroup.mk_pow]
  have : y ^ q = 1 := Subtype.ext (by simpa using hYexp y y.2)
  rw [this]
  rfl

theorem exists_faithful_actV {Y R : Subgroup X} (hRN : R ≤ normalizer (Y : Set X))
    (ψ : ↥R →* QD32) (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : X) ∈ centralizer (Y : Set X))
    (hB : ∀ r : ↥R, (∀ y ∈ Y, (r : X) * y * (r : X)⁻¹ * y⁻¹ ∈ centralizer (Y : Set X)) →
      (r : X) ∈ centralizer (Y : Set X)) :
    ∃ f : QD32 →* MulAut (↥Y ⧸ Subgroup.center ↥Y), Function.Injective f ∧
      ∀ r : ↥R, f (ψ r) = actV hRN r := by
  have hker : ψ.ker ≤ (actV hRN).ker := fun r hr => (mem_ker_actV hRN r).mpr (fun y hy => by
    have h0 : (r : X) ∈ centralizer (Y : Set X) := (hψc r).mp hr
    have h1 := Subgroup.mem_centralizer_iff.mp h0 y hy
    have h2 : (r : X) * y * (r : X)⁻¹ * y⁻¹ = 1 := by
      rw [← h1]
      group
    rw [h2]
    exact Subgroup.one_mem _)
  let f : QD32 →* MulAut (↥Y ⧸ Subgroup.center ↥Y) :=
    ψ.liftOfRightInverse (Function.surjInv hψs) (Function.rightInverse_surjInv hψs)
      ⟨actV hRN, hker⟩
  refine ⟨f, ?_, fun r => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨r, rfl⟩ := hψs x
    have hr : r ∈ (actV hRN).ker := by
      rw [MonoidHom.mem_ker]
      simpa [f] using hx
    exact (hψc r).mpr (hB r ((mem_ker_actV hRN r).mp hr))
  · simp [f]

theorem card_quotient_pow_four [Finite X] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Y R : Subgroup X}
    (hYexp : ∀ y ∈ Y, y ^ q = 1) (hYcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (hRN : R ≤ normalizer (Y : Set X)) (ψ : ↥R →* QD32) (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : X) ∈ centralizer (Y : Set X))
    (hB : ∀ r : ↥R, (∀ y ∈ Y, (r : X) * y * (r : X)⁻¹ * y⁻¹ ∈ centralizer (Y : Set X)) →
      (r : X) ∈ centralizer (Y : Set X)) :
    q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y) := by
  obtain ⟨f, hf, -⟩ := exists_faithful_actV hRN ψ hψs hψc hB
  exact card_ge_pow_four_of_qd32 hq hq2 (quotient_center_comm hYcl) (quotient_center_exp hYexp) f hf

end Faithful

section Normalizer

@[expose] noncomputable def actN (Y : Subgroup X) :
    ↥(normalizer (Y : Set X)) →* MulAut (↥Y ⧸ Subgroup.center ↥Y) :=
  (inducedAutCenter ↥Y).comp Y.normalizerMonoidHom

theorem actN_mk (Y : Subgroup X) (n : ↥(normalizer (Y : Set X))) (y : ↥Y) :
    actN Y n (QuotientGroup.mk y) = QuotientGroup.mk (Y.normalizerMonoidHom n y) := rfl

theorem actN_mk_coe (Y : Subgroup X) (n : ↥(normalizer (Y : Set X))) (y : ↥Y) :
    (((Y.normalizerMonoidHom n y : ↥Y)) : X) = (n : X) * (y : X) * (n : X)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe Y n y

theorem actV_conj {Y R : Subgroup X} (hRN : R ≤ normalizer (Y : Set X))
    (n : ↥(normalizer (Y : Set X))) (hnR : ∀ r ∈ R, (n : X) * r * (n : X)⁻¹ ∈ R) (r : ↥R) :
    actV hRN ⟨(n : X) * (r : X) * (n : X)⁻¹, hnR r r.2⟩ =
      actN Y n * actV hRN r * (actN Y n)⁻¹ := by
  apply MulEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective v
  rw [MulAut.mul_apply, MulAut.mul_apply, ← map_inv, actN_mk]
  change QuotientGroup.mk _ = actN Y n (actV hRN r (QuotientGroup.mk _))
  change _ = actN Y n (QuotientGroup.mk _)
  rw [actN_mk]
  congr 1
  apply Subtype.ext
  have e1 := actY_apply_coe hRN ⟨(n : X) * (r : X) * (n : X)⁻¹, hnR r r.2⟩ w
  have e2 := actY_apply_coe hRN r (Y.normalizerMonoidHom n⁻¹ w)
  have e3 := actN_mk_coe Y n⁻¹ w
  have e4 := actN_mk_coe Y n (actY hRN r (Y.normalizerMonoidHom n⁻¹ w))
  show ((((actY hRN ⟨(n : X) * (r : X) * (n : X)⁻¹, hnR r r.2⟩) w : ↥Y)) : X) =
    ((((Y.normalizerMonoidHom n) ((actY hRN r) ((Y.normalizerMonoidHom n⁻¹) w))) : ↥Y) : X)
  rw [e1, e4, e2, e3]
  simp only [InvMemClass.coe_inv]
  group

theorem actN_ne_one {Y R : Subgroup X} (hRN : R ≤ normalizer (Y : Set X))
    (n : ↥(normalizer (Y : Set X))) (hnR : ∀ r ∈ R, (n : X) * r * (n : X)⁻¹ ∈ R)
    (hB : ∀ r : ↥R, (∀ y ∈ Y, (r : X) * y * (r : X)⁻¹ * y⁻¹ ∈ centralizer (Y : Set X)) →
      (r : X) ∈ centralizer (Y : Set X))
    (hnt : ∃ r ∈ R, (n : X) * r * (n : X)⁻¹ * r⁻¹ ∉ centralizer (Y : Set X)) :
    actN Y n ≠ 1 := by
  intro h1
  obtain ⟨r, hr, hnt'⟩ := hnt
  have hsR : (n : X) * r * (n : X)⁻¹ * r⁻¹ ∈ R := R.mul_mem (hnR r hr) (R.inv_mem hr)
  apply hnt'
  have key : actV hRN ⟨(n : X) * r * (n : X)⁻¹ * r⁻¹, hsR⟩ = 1 := by
    have h2 : (⟨(n : X) * r * (n : X)⁻¹ * r⁻¹, hsR⟩ : ↥R) =
        ⟨(n : X) * r * (n : X)⁻¹, hnR r hr⟩ * (⟨r, hr⟩ : ↥R)⁻¹ := rfl
    rw [h2, map_mul, map_inv, actV_conj hRN n hnR ⟨r, hr⟩, h1]
    simp
  exact hB ⟨_, hsR⟩ ((mem_ker_actV hRN ⟨_, hsR⟩).mp (MonoidHom.mem_ker.mpr key))

end Normalizer

section ASet

variable (Y : Subgroup X) (pr : X → Prop)

def Qset : Set ↥Y := {y | ∀ c ∈ Subgroup.center ↥Y, ¬ pr ((y * c : ↥Y) : X)}

def Aset : Set (↥Y ⧸ Subgroup.center ↥Y) := QuotientGroup.mk '' Qset Y pr

variable {Y pr}

theorem mem_Qset {y : ↥Y} :
    y ∈ Qset Y pr ↔ ∀ c ∈ Subgroup.center ↥Y, ¬ pr ((y * c : ↥Y) : X) := Iff.rfl

theorem mul_mem_Qset_iff {y z : ↥Y} (hz : z ∈ Subgroup.center ↥Y) :
    y * z ∈ Qset Y pr ↔ y ∈ Qset Y pr := by
  constructor
  · intro h c hc
    have := h (z⁻¹ * c) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hz) hc)
    simpa [mul_assoc] using this
  · intro h c hc
    have := h (z * c) (Subgroup.mul_mem _ hz hc)
    simpa [mul_assoc] using this

theorem preimage_Aset : (QuotientGroup.mk ⁻¹' Aset Y pr : Set ↥Y) = Qset Y pr := by
  ext y
  constructor
  · rintro ⟨y₀, hy₀, hy⟩
    have h1 : y₀⁻¹ * y ∈ Subgroup.center ↥Y := QuotientGroup.eq.mp hy
    have h2 : y = y₀ * (y₀⁻¹ * y) := by group
    rw [h2]
    exact (mul_mem_Qset_iff h1).mpr hy₀
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem card_Qset [Finite X] :
    Nat.card (Qset Y pr) = Nat.card (Subgroup.center ↥Y) * Nat.card (Aset Y pr) := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ?_
  exact (Equiv.subtypeEquivRight
    (fun y => (Set.ext_iff.mp (preimage_Aset (Y := Y) (pr := pr)) y).symm)).trans
    (QuotientGroup.preimageMkEquivSubgroupProdSet (Subgroup.center ↥Y) (Aset Y pr))

end ASet

section Invariance

theorem mulEquiv_mem_center_iff {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {c : G} :
    φ c ∈ Subgroup.center H ↔ c ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply φ.injective
    rw [map_mul, map_mul]
    exact h (φ g)
  · intro h b
    obtain ⟨g, rfl⟩ := φ.surjective b
    rw [← map_mul, ← map_mul, h g]

theorem card_Qset_congr {X' : Type} [Group X'] {Y : Subgroup X} {Y' : Subgroup X'}
    {pr : X → Prop} {pr' : X' → Prop} (φ : ↥Y ≃* ↥Y')
    (hpr : ∀ y : ↥Y, pr (y : X) ↔ pr' ((φ y : ↥Y') : X')) :
    Nat.card (Qset Y pr) = Nat.card (Qset Y' pr') := by
  refine Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun y => ?_)
  constructor
  · intro hy c' hc'
    obtain ⟨c, rfl⟩ := φ.surjective c'
    have h := hy c ((mulEquiv_mem_center_iff φ).mp hc')
    have e : φ.toEquiv y * φ c = φ (y * c) := by rw [map_mul]; rfl
    rw [e]
    exact fun h' => h ((hpr (y * c)).mpr h')
  · intro hy c hc
    have h := hy (φ c) ((mulEquiv_mem_center_iff φ).mpr hc)
    have e : φ.toEquiv y * φ c = φ (y * c) := by rw [map_mul]; rfl
    rw [e] at h
    exact fun h' => h ((hpr (y * c)).mp h')

theorem card_center_congr {G H : Type*} [Group G] [Group H] (φ : G ≃* H) :
    Nat.card (Subgroup.center G) = Nat.card (Subgroup.center H) :=
  Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun _ => (mulEquiv_mem_center_iff φ).symm)

variable {Y : Subgroup X} {pr : X → Prop}

theorem one_not_mem_Aset (h1 : pr 1) : (1 : ↥Y ⧸ Subgroup.center ↥Y) ∉ Aset Y pr := by
  rintro ⟨y, hy, hy1⟩
  have hc : y ∈ Subgroup.center ↥Y := (QuotientGroup.eq_one_iff y).mp hy1
  exact hy y⁻¹ (Subgroup.inv_mem _ hc) (by simpa using h1)

theorem actN_mem_Aset (a : X) (ha : a ∈ normalizer (Y : Set X))
    (hconj : ∀ x, pr (a * x * a⁻¹) ↔ pr x) {v : ↥Y ⧸ Subgroup.center ↥Y} (hv : v ∈ Aset Y pr) :
    actN Y ⟨a, ha⟩ v ∈ Aset Y pr := by
  obtain ⟨y, hy, rfl⟩ := hv
  set σ : MulAut ↥Y := Y.normalizerMonoidHom ⟨a, ha⟩ with hσ
  have hσc : ∀ w : ↥Y, ((σ w : ↥Y) : X) = a * (w : X) * a⁻¹ := fun w =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨a, ha⟩ w
  refine ⟨σ y, ?_, (actN_mk Y ⟨a, ha⟩ y).symm⟩
  intro c hc hpr
  have hc' : σ.symm c ∈ Subgroup.center ↥Y := (mulEquiv_mem_center_iff σ.symm).mpr hc
  apply hy (σ.symm c) hc'
  have e1 : σ y * c = σ (y * σ.symm c) := by rw [map_mul, MulEquiv.apply_symm_apply]
  rw [e1, hσc] at hpr
  exact (hconj _).mp hpr

theorem actN_pow_eq_one (a : X) (ha : a ∈ normalizer (Y : Set X)) {n : ℕ}
    (hn : (MulAut.conj a) ^ n = 1) : (actN Y ⟨a, ha⟩) ^ n = 1 := by
  rw [← map_pow]
  apply MulEquiv.ext
  intro v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
  rw [actN_mk]
  change QuotientGroup.mk _ = QuotientGroup.mk y
  congr 1
  apply Subtype.ext
  rw [actN_mk_coe]
  have h := congrArg (fun m : MulAut X => m (y : X)) hn
  simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h
  exact h

theorem one_not_mem_Aset_of_central (h : ∃ c ∈ Subgroup.center ↥Y, pr (c : X)) :
    (1 : ↥Y ⧸ Subgroup.center ↥Y) ∉ Aset Y pr := by
  rintro ⟨y, hy, hy1⟩
  have hc : y ∈ Subgroup.center ↥Y := (QuotientGroup.eq_one_iff y).mp hy1
  obtain ⟨c, hcz, hcp⟩ := h
  apply mem_Qset.mp hy (y⁻¹ * c) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hcz)
  simpa using hcp

end Invariance

section Orbit

theorem actV_eq_actN {Y R : Subgroup X} (hRN : R ≤ normalizer (Y : Set X)) (r : ↥R) :
    actV hRN r = actN Y ⟨(r : X), hRN r.2⟩ := by
  apply MulEquiv.ext
  intro v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
  rw [actN_mk]
  change QuotientGroup.mk (actY hRN r y) = _
  congr 1

theorem false_of_Aset [Finite X] {Y R : Subgroup X} (hYexp : ∀ y ∈ Y, y ^ 3 = 1)
    (hYcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (hRN : R ≤ normalizer (Y : Set X)) (ψ : ↥R →* QD32) (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : X) ∈ centralizer (Y : Set X))
    (hB : ∀ r : ↥R, (∀ y ∈ Y, (r : X) * y * (r : X)⁻¹ * y⁻¹ ∈ centralizer (Y : Set X)) →
      (r : X) ∈ centralizer (Y : Set X))
    (hV : Nat.card (↥Y ⧸ Subgroup.center ↥Y) = 3 ^ 4)
    (pr : X → Prop) (hconj : ∀ r ∈ R, ∀ x, pr (r * x * r⁻¹) ↔ pr x)
    (h1 : (1 : ↥Y ⧸ Subgroup.center ↥Y) ∉ Aset Y pr) {N : ℕ} (hN : ¬ 16 ∣ N)
    (hcard : Nat.card (Aset Y pr) = N) : False := by
  classical
  obtain ⟨f, hf, hfr⟩ := exists_faithful_actV hRN ψ hψs hψc hB
  have : Fintype (↥Y ⧸ Subgroup.center ↥Y) := Fintype.ofFinite _
  let A : Finset (↥Y ⧸ Subgroup.center ↥Y) := Finset.univ.filter fun v => v ∈ Aset Y pr
  have hAc : A.card = N := by
    have h : A.card = Nat.card {v : ↥Y ⧸ Subgroup.center ↥Y // v ∈ Aset Y pr} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h]
    exact hcard
  have hinv : ∀ g : QD32, ∀ v ∈ A, f g v ∈ A := by
    intro g v hv
    obtain ⟨r, rfl⟩ := hψs g
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rw [hfr r, actV_eq_actN hRN r]
    exact actN_mem_Aset (pr := pr) (r : X) (hRN r.2) (hconj r r.2) hv
  have h16 := qd32_dvd_card_of_invariant_nonzero Nat.prime_three (by norm_num)
    (quotient_center_comm hYcl) (quotient_center_exp hYexp) f hf (by rw [hV]; norm_num) A
    (by simpa [A] using h1) hinv
  rw [hAc] at h16
  exact hN h16

end Orbit

end CFSG.RankThree.PartOne.F106
