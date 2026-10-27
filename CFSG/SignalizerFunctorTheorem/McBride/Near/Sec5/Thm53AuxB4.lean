module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxB3
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA5

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53B

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

omit [Finite G] in
theorem isSolvableSection_of_eq_sup {X K R : Subgroup G} (hRX : R ≤ X) (hKX : K ≤ X)
    (hKn : X ≤ Subgroup.normalizer (K : Set G)) (hR : Group.IsSolvable ↥R)
    (hX : X = K ⊔ R) : IsSolvableSection X K := by
  have hKnorm : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hKn
  refine Thm53A.isSolvableSection_of_isSolvable_quotient ?_
  let φ : ↥R →* ↥X ⧸ K.subgroupOf X :=
    (QuotientGroup.mk' (K.subgroupOf X)).comp (Subgroup.inclusion hRX)
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf X) q
    have hx' : x ∈ K ⊔ R := hX ▸ hx
    obtain ⟨k, hk, r, hr, hkr⟩ :=
      (Thm53A.mem_sup_iff_mul (H := K) (K := R) (fun r hr => hKn (hRX hr))).mp hx'
    refine ⟨⟨r, hr⟩, ?_⟩
    show QuotientGroup.mk' (K.subgroupOf X) ⟨r, hRX hr⟩ =
      QuotientGroup.mk' (K.subgroupOf X) ⟨x, hx⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have : r⁻¹ * x = r⁻¹ * (k * r) := by rw [hkr]
    have hmem : ((⟨r, hRX hr⟩ : ↥X)⁻¹ * ⟨x, hx⟩ : ↥X) =
        ⟨r⁻¹ * x, X.mul_mem (X.inv_mem (hRX hr)) hx⟩ := rfl
    rw [hmem]
    show r⁻¹ * x ∈ K
    rw [this]
    have h2 := (Subgroup.mem_normalizer_iff.mp (hKn (inv_mem (hRX hr))) k).mp hk
    simpa [mul_assoc] using h2
  have := hR
  exact Group.isSolvable_of_surjective hφ

omit [Finite G] in
theorem isSolvableSection_of_le {X K M₁ M₂ : Subgroup G} (hsec : IsSolvableSection X K)
    (hM₁ : M₁ ≤ X) (hKM₂ : K ≤ M₂) : IsSolvableSection M₁ M₂ := by
  obtain ⟨n, hn⟩ := hsec
  refine ⟨n, fun x hx => ?_⟩
  have h1 : (Subgroup.inclusion hM₁) x ∈ derivedSeries ↥X n :=
    map_derivedSeries_le_derivedSeries (Subgroup.inclusion hM₁) n ⟨x, hx, rfl⟩
  have h2 := hn h1
  exact hKM₂ h2


section Bot

variable (hb : BotData p A θ)

include hb

theorem dset_subset_bot
    (hcard : Nat.card A = p ^ 3) {S : Subgroup G}
    (hSsol : Group.IsSolvable ↥S)
    (heq : ∀ a ∈ A, a ≠ 1 → theta1 p A θ S a = θ a) {Y : Subgroup G} (hY : Y ∈ dset p A θ) :
    Y = ⊥ := by
  have hθ := hb.nearFunctor
  obtain ⟨Z₁, Z₂, B, hZ, hBA, hcyc, hZB⟩ := Thm53A.exists_pair_centralized hθ hY
  have hBcard : p ^ 2 ≤ Nat.card B := by
    have h1 := Thm53A.card_le_of_cyclicMod hθ.elemAbelian hθ.prime hBA hcyc
    rw [hcard] at h1
    have h2 : p ^ 3 = p ^ 2 * p := pow_succ p 2
    rw [h2] at h1
    exact Nat.le_of_mul_le_mul_right h1 hθ.prime.pos
  obtain ⟨e, heB, he1⟩ : ∃ e ∈ B, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
    rw [hbot, Subgroup.card_bot] at hBcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hθ.prime.one_lt
    omega
  have heA : e ∈ A := hBA heB
  have hXm : θ e ∈ mtil p A θ := apply_mem_mtil hθ heA he1
  have hZ1e : Z₁ ≤ θ e := by
    have := hZ.1.1.1.2.2.1 e heA he1
    exact fun z hz => this ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hZB hz) e heB |>.symm)⟩
  have hcY : θ e ∈ cset p A θ Y := ⟨hXm, (Z₁, Z₂), hZ, hZ1e⟩
  have hns : ¬ Group.IsSolvable (θ e) := not_isSolvable_of_mem_cset hθ hcY
  have hcbot : θ e ∈ cset p A θ ⊥ := by
    by_contra hX'
    apply hns
    have h1 := heq e heA he1
    have h2 : thetaM p A θ ⊥ (θ e) = ⊥ := thetaM_eq_bot_of_not_mem hXm hX'
    have h3 : θ e ≤ S := by
      have h4 : θ e = (S ⊓ θ e) ⊔ ⊥ := by
        conv_lhs => rw [← h1]
        simp only [theta1, h2]
      rw [h4]
      simp
    have := hSsol
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h3)
  have hKeq : thetaM p A θ ⊥ (θ e) = kOf (θ e) := thetaM_bot_eq_kOf hb hcbot
  have hXK : θ e = kOf (θ e) ⊔ (S ⊓ θ e) := by
    have h1 := heq e heA he1
    simp only [theta1, hKeq] at h1
    rw [sup_comm]
    exact h1.symm
  have hRsol : Group.IsSolvable ↥(S ⊓ θ e) := by
    have := hSsol
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : S ⊓ θ e ≤ S))
  have hsecXK : IsSolvableSection (θ e) (kOf (θ e)) :=
    isSolvableSection_of_eq_sup inf_le_right (kOf_le _) (Thm41Aux.le_normalizer_kOf _) hRsol hXK
  have hPYX := thetaM_thetaL_mem_pairsYX hθ hY hcY
  have hKM : kOf (θ e) ≤ thetaM p A θ Y (θ e) := kOf_le_thetaM hθ hY hcY
  have hiP : (thetaM p A θ Y (θ e), thetaL p A θ Y (θ e)) ∈ iPairs A (θ e) := by
    have : (thetaM p A θ Y (θ e), thetaL p A θ Y (θ e)) ∈ iPairsY A (θ e) Y := by
      rw [← pairsYX_eq_iPairsY hθ hXm]
      exact hPYX
    exact this.1
  obtain ⟨⟨hP, hM₂D⟩, hM₁X⟩ := hPYX
  set M₁ := thetaM p A θ Y (θ e) with hM₁
  set M₂ := thetaL p A θ Y (θ e) with hM₂
  have hchK := isChiefFactorOf_kOf hb hcbot
  have hHle : kOf (θ e) ⊔ dsub A θ ⊔ A ≤ M₁ ⊔ dsub A θ ⊔ A :=
    sup_le_sup_right (sup_le_sup_right hKM _) _
  have hM₂N : M₁ ⊔ dsub A θ ⊔ A ≤ Subgroup.normalizer (M₂ : Set G) := hP.2.2.1.1.2
  have hM₂M₁ : M₂ ≤ M₁ := hP.2.2.1.2.2.1.le
  have hnK : IsNormalIn (kOf (θ e) ⊓ M₂) (kOf (θ e) ⊔ dsub A θ ⊔ A) :=
    ⟨inf_le_left.trans (le_sup_left.trans le_sup_left),
      Thm53A.le_normalizer_inf hchK.2.1.2 (hHle.trans hM₂N)⟩
  rcases hchK.2.2.2 (kOf (θ e) ⊓ M₂) hnK bot_le inf_le_left with h0 | h1
  · have hM₂C : M₂ ≤ Subgroup.centralizer (kOf (θ e) : Set G) := by
      intro m hm
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hmN : m ∈ Subgroup.normalizer (kOf (θ e) : Set G) :=
        Thm41Aux.le_normalizer_kOf (θ e) (hM₁X (hM₂M₁ hm))
      have hM₁H : M₁ ≤ M₁ ⊔ dsub A θ ⊔ A := le_sup_left.trans le_sup_left
      have hkN : k ∈ Subgroup.normalizer (M₂ : Set G) := hM₂N (hM₁H (hKM hk))
      have h1 : m * k * m⁻¹ * k⁻¹ ∈ kOf (θ e) ⊓ M₂ := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact mul_mem ((Subgroup.mem_normalizer_iff.mp hmN k).mp hk) (inv_mem hk)
        · have h2 := (Subgroup.mem_normalizer_iff.mp hkN m⁻¹).mp (inv_mem hm)
          have e : m * k * m⁻¹ * k⁻¹ = m * (k * m⁻¹ * k⁻¹) := by group
          rw [e]
          exact mul_mem hm h2
      rw [h0, Subgroup.mem_bot] at h1
      have h3 : k * m = m * k := by
        calc k * m = (m * k * m⁻¹ * k⁻¹)⁻¹ * (m * k) := by group
          _ = m * k := by rw [h1]; simp
      exact h3
    rw [eq_bot_iff]
    intro y hy
    have hyM₂ : y ∈ M₂ ⊓ dsub A θ := by rw [hM₂D]; exact hy
    have : y ∈ dsub A θ ⊓ Subgroup.centralizer (kOf (θ e) : Set G) :=
      ⟨hyM₂.2, hM₂C hyM₂.1⟩
    rw [dsub_inf_centralizer_kOf hb hcbot] at this
    exact this
  · exact absurd (isSolvableSection_of_le hsecXK hM₁X (inf_eq_left.mp h1))
      (Thm33a.not_isSolvableSection_of_mem_iPairs hiP)

end Bot

end Thm53B

end CFSG.SignalizerFunctorTheorem.McBride.Near
