module

public import CFSG.RankThree.GF2n.Tim79Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

open CFSG.GH74.GLS.Bg.TwoGroups in
theorem n12_ut3_commutator {R : Type*} [CommRing R] (x y : UT3 R) :
    ⁅x, y⁆ = ⟨0, 0, x.a * y.b - y.a * x.b⟩ := by
  rw [commutatorElement_def]
  ext <;> simp only [UT3.mul_def, UT3.inv_def] <;> ring

open CFSG.GH74.GLS.Bg.TwoGroups in
theorem n12_ut3_nondeg {F : Type*} [Field F] (μ : F →+ ZMod 2) (hμ : μ ≠ 0) (x : UT3 F)
    (h : ∀ y : UT3 F, μ (x.a * y.b - y.a * x.b) = 0) : x.a = 0 ∧ x.b = 0 := by
  refine ⟨?_, ?_⟩ <;> by_contra hne <;> apply hμ <;> ext t
  · have e : x.a * (t / x.a) - 0 * x.b = t := by rw [zero_mul, sub_zero, mul_div_cancel₀ t hne]
    simpa only [e, AddMonoidHom.zero_apply] using h ⟨0, t / x.a, 0⟩
  · have e : x.a * 0 - (-(t / x.b)) * x.b = t := by
      rw [mul_zero, zero_sub, neg_mul, neg_neg, div_mul_cancel₀ t hne]
    simpa only [e, AddMonoidHom.zero_apply] using h ⟨-(t / x.b), 0, 0⟩

open CFSG.GH74.GLS.Bg.TwoGroups in
theorem n12_factor_mem {G : Type} [Group G] {D Z : Subgroup G} {n : ℕ}
    (e : ↥D ≃* UT3 (GaloisField 2 n)) (hDZ : (Subgroup.center ↥D).map D.subtype = Z)
    (lam : ↥Z →* Multiplicative (ZMod 2)) (hlam : lam ≠ 1) {a : G} (ha : a ∈ D)
    (hcomm : ∀ y ∈ D, ∃ h : ⁅a, y⁆ ∈ Z, lam ⟨⁅a, y⁆, h⟩ = 1) : a ∈ Z := by
  have hcen : ∀ u ∈ Subgroup.center (UT3 (GaloisField 2 n)), e.symm u ∈ Subgroup.center ↥D :=
    fun u hu => Subgroup.mem_center_iff.2 fun g => e.injective (by
      rw [map_mul, map_mul, e.apply_symm_apply]; exact Subgroup.mem_center_iff.1 hu (e g))
  let z : GaloisField 2 n → G := fun c => (e.symm ⟨0, 0, c⟩ : G)
  have hz : ∀ c, z c ∈ Z := fun c => by
    rw [← hDZ]; exact ⟨_, hcen _ ((Tim79.ut3_mem_center_iff _).2 ⟨rfl, rfl⟩), rfl⟩
  have hz0 : (⟨z 0, hz 0⟩ : ↥Z) = 1 := Subtype.ext (by
    show ((e.symm ⟨0, 0, 0⟩ : ↥D) : G) = 1
    rw [← UT3.one_def, map_one]; rfl)
  have hzadd : ∀ c c', (⟨z (c + c'), hz _⟩ : ↥Z) = ⟨z c, hz c⟩ * ⟨z c', hz c'⟩ := fun c c' =>
    Subtype.ext (by
      show ((e.symm ⟨0, 0, c + c'⟩ : ↥D) : G) = (e.symm ⟨0, 0, c⟩ : ↥D) * (e.symm ⟨0, 0, c'⟩ : ↥D)
      rw [← Subgroup.coe_mul, ← map_mul]
      congr 2
      ext <;> simp [UT3.mul_def])
  let μ : GaloisField 2 n →+ ZMod 2 :=
    { toFun := fun c => Multiplicative.toAdd (lam ⟨z c, hz c⟩)
      map_zero' := by simp only [hz0, map_one, toAdd_one]
      map_add' := fun c c' => by simp only [hzadd, map_mul, toAdd_mul] }
  have hμ : μ ≠ 0 := by
    obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hlam
    obtain ⟨d, hd, hdw⟩ : (w : G) ∈ (Subgroup.center ↥D).map D.subtype := by
      rw [hDZ]; exact w.2
    obtain ⟨h1, h2⟩ := (Tim79.ut3_mem_center_iff _).1 (by
      refine Subgroup.mem_center_iff.2 fun g => ?_
      obtain ⟨g, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hd g] : e d ∈ Subgroup.center _)
    intro h0
    apply hw
    have hzw : (⟨z (e d).c, hz _⟩ : ↥Z) = w := Subtype.ext (by
      show ((e.symm ⟨0, 0, (e d).c⟩ : ↥D) : G) = w
      rw [← hdw]
      congr 1
      apply e.injective
      rw [e.apply_symm_apply]
      ext <;> simp [h1, h2])
    have := DFunLike.congr_fun h0 (e d).c
    simp only [AddMonoidHom.zero_apply] at this
    rw [← hzw]
    exact toAdd_eq_zero.1 this
  set a' : ↥D := ⟨a, ha⟩
  obtain ⟨h1, h2⟩ := n12_ut3_nondeg μ hμ (e a') fun y => by
    obtain ⟨h, hl⟩ := hcomm _ (e.symm y).2
    have key : ⁅a, ((e.symm y : ↥D) : G)⁆ = z ((e a').a * y.b - y.a * (e a').b) := by
      show ((⁅a', e.symm y⁆ : ↥D) : G) = _
      congr 1
      apply e.injective
      rw [map_commutatorElement, e.apply_symm_apply, e.apply_symm_apply, n12_ut3_commutator]
    show Multiplicative.toAdd (lam ⟨z _, hz _⟩) = 0
    have hs : (⟨z ((e a').a * y.b - y.a * (e a').b), hz _⟩ : ↥Z) = ⟨_, h⟩ :=
      Subtype.ext key.symm
    rw [hs, hl, toAdd_one]
  have hca : a' ∈ Subgroup.center ↥D := by
    have := hcen (e a') ((Tim79.ut3_mem_center_iff _).2 ⟨h1, h2⟩)
    rwa [e.symm_apply_apply] at this
  rw [← hDZ]
  exact ⟨a', hca, rfl⟩

theorem n12_mem_of_lam_comm_trivial {G : Type} [Group G] {Q Z : Subgroup G} {n k : ℕ}
    (hcp : Tim79.IsCentralProductOfL3 Q Z n k)
    (lam : ↥Z →* Multiplicative (ZMod 2)) (hlam : lam ≠ 1)
    {x : G} (hx : x ∈ Q)
    (hcomm : ∀ y ∈ Q, ∃ h : ⁅x, y⁆ ∈ Z, lam ⟨⁅x, y⁆, h⟩ = 1) : x ∈ Z := by
  classical
  obtain ⟨-, D, hDQ, hDL, hDZ, hDc, hDsup⟩ := hcp
  have hc : Pairwise fun i j => ∀ x y : G, x ∈ D i → y ∈ D j → Commute x y :=
    fun i j hij x y hx hy => hDc i j hij x hx y hy
  rw [← hDsup, ← Subgroup.noncommPiCoprod_range (hcomm := hc)] at hx
  obtain ⟨u, rfl⟩ := hx
  have hdec : ∀ j, ∃ r : G, Subgroup.noncommPiCoprod hc u = u j * r ∧
      ∀ y ∈ D j, r * y = y * r := by
    intro j
    rw [Subgroup.noncommPiCoprod_apply]
    refine ⟨_, (Finset.mul_noncommProd_erase _ (Finset.mem_univ j) _ _).symm, fun y hy => ?_⟩
    exact (Finset.noncommProd_commute _ _ _ y fun i hi =>
      hDc j i (Finset.ne_of_mem_erase hi).symm y hy (u i) (u i).2).eq.symm
  rw [Subgroup.noncommPiCoprod_apply]
  refine Subgroup.noncommProd_mem _ _ fun j _ => ?_
  obtain ⟨e⟩ := hDL j
  obtain ⟨r, hr, hry⟩ := hdec j
  refine n12_factor_mem e (hDZ j) lam hlam (u j).2 fun y hy => ?_
  have key : ⁅Subgroup.noncommPiCoprod hc u, y⁆ = ⁅(u j : G), y⁆ := by
    rw [hr, commutatorElement_def, commutatorElement_def, mul_inv_rev,
      show (u j : G) * r * y = u j * y * r by rw [mul_assoc, hry y hy, ← mul_assoc]]
    group
  obtain ⟨h, hl⟩ := hcomm y (hDQ j hy)
  exact ⟨key ▸ h, by convert hl using 3; exact key.symm⟩

end CFSG.RankThree.GF2n.Stroth80
