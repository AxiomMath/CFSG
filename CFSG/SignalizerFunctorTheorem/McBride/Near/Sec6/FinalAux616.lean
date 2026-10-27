module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.FinalAuxStar
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KOfKHat

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S33

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem mem_kOf_of_acts_inner {H : Subgroup G} (hsol : sol H = ⊥) {c : G} (hcH : c ∈ H)
    (hc : ∀ J ∈ lcal H, ∃ y ∈ J, ∀ j ∈ J, c * j * c⁻¹ = y * j * y⁻¹) : c ∈ kOf H := by
  classical
  have hK := isDirectProduct_lcal_kOf hsol
  choose! y hyJ hy using hc
  let z : (J : lcal H) → (J : Subgroup G) := fun J => ⟨y J.1, hyJ J.1 J.2⟩
  set k : kOf H := hK.equiv z with hkdef
  have hcoord : ∀ (J : Subgroup G) (hJ : J ∈ lcal H),
      hK.coord hJ k = (⟨y J, hyJ J hJ⟩ : J) := by
    intro J hJ
    exact hK.coord_equiv hJ z
  have hw : ∀ (J : Subgroup G) (hJ : J ∈ lcal H),
      (k : G)⁻¹ * y J ∈ sSup (lcal H \ {J}) := by
    intro J hJ
    have hyK : y J ∈ kOf H := hK.le hJ (hyJ J hJ)
    have key : hK.coord hJ (k⁻¹ * ⟨y J, hyK⟩) = 1 := by
      rw [map_mul, map_inv, hcoord J hJ]
      have : hK.coord hJ ⟨y J, hyK⟩ = (⟨y J, hyJ J hJ⟩ : J) :=
        Subtype.ext (hK.coord_of_mem hJ (hyJ J hJ))
      rw [this, inv_mul_cancel]
    exact (hK.coord_eq_one_iff hJ _).mp key
  set g : G := (k : G)⁻¹ * c with hg
  have hkH : (k : G) ∈ H := kOf_le H k.2
  have hgH : g ∈ H := mul_mem (inv_mem hkH) hcH
  have hgc : g ∈ Subgroup.centralizer (kOf H : Set G) := by
    have h1 : kOf H ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [← hK.sSup_eq]
      refine sSup_le fun J hJ j hj => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : Commute j ((k : G)⁻¹ * y J) :=
        hK.commute_sSup_diff hJ j hj _ (hw J hJ)
      have e1 : c * j * c⁻¹ = y J * j * (y J)⁻¹ := hy J hJ j hj
      have e2 : g * j * g⁻¹ = j := by
        have : g * j * g⁻¹ = ((k : G)⁻¹ * y J) * j * ((k : G)⁻¹ * y J)⁻¹ := by
          calc g * j * g⁻¹ = (k : G)⁻¹ * (c * j * c⁻¹) * (k : G) := by simp [hg, mul_assoc]
            _ = (k : G)⁻¹ * (y J * j * (y J)⁻¹) * (k : G) := by rw [e1]
            _ = ((k : G)⁻¹ * y J) * j * ((k : G)⁻¹ * y J)⁻¹ := by simp [mul_assoc]
        rw [this]
        have := hcomm.symm.eq
        rw [this, mul_assoc, mul_inv_cancel, mul_one]
      have e3 : j * g = g * j := by
        have := congrArg (· * g) e2
        simp only [mul_assoc, inv_mul_cancel, mul_one] at this
        exact this.symm
      exact e3
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hx)
  have hg1 : g = 1 := by
    have : g ∈ H ⊓ Subgroup.centralizer (kOf H : Set G) := ⟨hgH, hgc⟩
    rw [centralizer_kOf_eq_bot hsol, Subgroup.mem_bot] at this
    exact this
  have : c = (k : G) := by
    have h2 : (k : G) * g = c := by simp [hg]
    rw [← h2, hg1, mul_one]
  rw [this]
  exact k.2

theorem sol_apply_eq_bot
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hns : ¬ Group.IsSolvable (θ a)) : sol (θ a) = ⊥ := by
  have hF := h.hyp.isFunctor
  have hz1 : Subgroup.zpowers a ≠ ⊥ := fun hbot => ha1 (Subgroup.zpowers_eq_bot.mp hbot)
  have := h.sol_thetaOf_eq_bot hz1 (Subgroup.zpowers_le.mpr ha)
    (by rwa [hF.thetaOf_zpowers ha ha1])
  rwa [hF.thetaOf_zpowers ha ha1] at this

theorem mem_normalizer_of_mem_theta
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) (hns : ¬ Group.IsSolvable (θ a)) {x : G} (hx : x ∈ θ a) :
    ∀ J ∈ lcal (θ a), x ∈ Subgroup.normalizer (J : Set G) := by
  have hθ := h.hyp.nearFunctor
  have hF := hθ.isFunctor
  have hzR : Subgroup.zpowers a ∈ rSet p A θ := by
    refine h.mem_rSet_iff.mpr ⟨fun hbot => ha1 (Subgroup.zpowers_eq_bot.mp hbot),
      Subgroup.zpowers_le.mpr ha, ?_⟩
    rwa [hF.thetaOf_zpowers ha ha1]
  have hsol : sol (θ a) = ⊥ := sol_apply_eq_bot h ha ha1 hns
  have hEq := h.perfRes_thetaOf_eq_kOf (fun hbot => ha1 (Subgroup.zpowers_eq_bot.mp hbot))
    (Subgroup.zpowers_le.mpr ha) (by rwa [hF.thetaOf_zpowers ha ha1])
  rw [hF.thetaOf_zpowers ha ha1] at hEq
  have h614 := (h.lemma614 hzR).2
  rw [hF.thetaOf_zpowers ha ha1] at h614
  have hstar := thetaStarFun_eq_apply h ha ha1
  have hkh : x ∈ khat (θ a) := by
    rw [← hstar] at hx
    refine (sup_le (a := perfRes (θ a)) (b := θ a ⊓ sTwo p A θ) (c := khat (θ a)) ?_ h614) hx
    rw [hEq]
    exact Nonsolv.kOf_le_khat_of_sol_eq_bot hsol
  exact Lemma216.normalizer_of_mem_khat hsol hkh

theorem pow_six_mem_kOf
    (h : Counterexample p A θ) {a : G}
    (ha : Subgroup.zpowers a ∈ rSetN p A θ 1) {x : G} (hx : x ∈ θ a) : x ^ 6 ∈ kOf (θ a) := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨haA, ha1, hns⟩ := (h.zpowers_mem_rSetN_one_iff).mp ha
  have hzR : Subgroup.zpowers a ∈ rSet p A θ := ha.1
  have hsol : sol (θ a) = ⊥ := sol_apply_eq_bot h haA ha1 hns
  have hnorm := mem_normalizer_of_mem_theta h haA ha1 hns hx
  have hnear : signalizerNearPSolvable p ↥(θ a) := (h.hyp.near a haA ha1).1
  have hcop : Nat.Coprime p (Nat.card (θ a)) := hθ.isFunctor.coprime a haA ha1
  refine mem_kOf_of_acts_inner hsol (pow_mem hx 6) fun J hJ => ?_
  obtain ⟨hJH, -, hJs, hJnc⟩ := mem_lcal_iff.mp hJ
  have hNS : NearSimple p ↥J :=
    ⟨hθ.prime, hJs, exists_mul_ne_of_not_isMulCommutative hJnc,
      signalizerNearPSolvable_of_le hJH hnear⟩
  have hxJ : x ∈ Subgroup.normalizer (J : Set G) := hnorm J hJ
  let φ : MulAut ↥J := J.normalizerMonoidHom ⟨x, hxJ⟩
  have hφ : ∀ t : J, ((φ t : J) : G) = x * t * x⁻¹ := fun t =>
    Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨x, hxJ⟩ t
  have hordφ : orderOf φ ∣ orderOf x := by
    have h1 : orderOf φ ∣ orderOf (⟨x, hxJ⟩ : Subgroup.normalizer (J : Set G)) :=
      orderOf_map_dvd J.normalizerMonoidHom _
    rwa [Subgroup.orderOf_mk] at h1
  have hordx : orderOf x ∣ Nat.card (θ a) := Subgroup.orderOf_dvd_natCard _ hx
  have hcopφ : Nat.Coprime p (orderOf φ) :=
    hcop.coprime_dvd_right (hordφ.trans hordx)
  obtain ⟨y', hy'⟩ := NearSimple.outer_coprime_pow_six_mem_inner hNS φ hcopφ
  refine ⟨(y' : G), y'.2, fun j hj => ?_⟩
  have hφ6 : ∀ t : J, ((φ ^ 6) t : J) = ⟨x ^ 6 * t * (x ^ 6)⁻¹, by
      have := hnorm J hJ
      have hx6 : x ^ 6 ∈ Subgroup.normalizer (J : Set G) := pow_mem this 6
      exact (Subgroup.mem_normalizer_iff.mp hx6 t).mp t.2⟩ := by
    intro t
    have hx6 : x ^ 6 ∈ Subgroup.normalizer (J : Set G) := pow_mem hxJ 6
    have : φ ^ 6 = J.normalizerMonoidHom ⟨x ^ 6, hx6⟩ := by
      rw [← map_pow]
      rfl
    rw [this]
    exact Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨x ^ 6, hx6⟩ t)
  have h1 := congrArg (fun m : MulAut ↥J => ((m ⟨j, hj⟩ : J) : G)) hy'
  simp only [hφ6, MulAut.conj_apply] at h1
  exact h1.symm

end Sec6S33

end CFSG.SignalizerFunctorTheorem.McBride.Near
