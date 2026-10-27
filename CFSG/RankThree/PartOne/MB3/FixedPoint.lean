module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_14
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup

section Holomorph

instance instFiniteMulAutFixed (X : Type) [Group X] [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun α : MulAut X => (α : X → X)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem isNilpotent_of_fixedPointFree_prime {X : Type} [Group X] [Finite X] (α : MulAut X)
    (hα : (orderOf α).Prime) (hfix : ∀ x : X, α x = x → x = 1) : Group.IsNilpotent X := by
  classical
  let H := SemidirectProduct X (MulAut X) (MonoidHom.id (MulAut X))
  have : Finite H := Finite.of_equiv (X × MulAut X) SemidirectProduct.equivProd.symm
  let Q : Subgroup H := (SemidirectProduct.inl : X →* H).range
  let P : Subgroup H := Subgroup.zpowers (SemidirectProduct.inr α : H)
  have hconj : ∀ (β : MulAut X) (n : X), (SemidirectProduct.inr β : H) * SemidirectProduct.inl n *
      (SemidirectProduct.inr β : H)⁻¹ = SemidirectProduct.inl (β n) := fun β n =>
    by simpa using (SemidirectProduct.inl_aut (φ := MonoidHom.id (MulAut X)) β n).symm
  have hnorm : P ≤ Subgroup.normalizer (Q : Set H) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨α n, (hconj α n).symm⟩
    · rintro ⟨m, hm⟩
      refine ⟨α⁻¹ m, ?_⟩
      have h1 : (SemidirectProduct.inr α : H) * h * (SemidirectProduct.inr α : H)⁻¹ =
          SemidirectProduct.inl m := hm.symm
      have h2 : h = (SemidirectProduct.inr α : H)⁻¹ * SemidirectProduct.inl m *
          (SemidirectProduct.inr α : H) := by
        rw [← h1]
        group
      rw [h2]
      have := hconj α⁻¹ m
      rw [map_inv, inv_inv] at this
      exact this.symm
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα
    exact Nat.not_prime_one hα
  have hP1 : ∃ x : H, x ∈ P ∧ x ≠ 1 := ⟨SemidirectProduct.inr α, Subgroup.mem_zpowers _, fun h =>
    hα1 (SemidirectProduct.inr_injective (φ := MonoidHom.id (MulAut X)) (by
      rw [h, map_one]))⟩
  have hfixed : ∀ x : H, x ∈ P → x ≠ 1 → Subgroup.centralizer ({x} : Set H) ⊓ Q = ⊥ := by
    intro x hx hx1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← map_zpow] at hx1 ⊢
    have hαk : α ^ k ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hpk : ¬ (orderOf α : ℤ) ∣ k := fun h => hαk (orderOf_dvd_iff_zpow_eq_one.mp h)
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyC, m, rfl⟩ := Subgroup.mem_inf.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC
    have h1 : (SemidirectProduct.inl ((α ^ k) m) : H) = SemidirectProduct.inl m := by
      rw [← hconj (α ^ k) m, mul_inv_eq_iff_eq_mul]
      exact hyC.symm
    have h2 : (α ^ k) m = m := SemidirectProduct.inl_injective h1
    have hprime : Prime (orderOf α : ℤ) := Nat.prime_iff_prime_int.mp hα
    obtain ⟨v, u, huv⟩ : ∃ v u : ℤ, v * (orderOf α : ℤ) + u * k = 1 :=
      (Prime.coprime_iff_not_dvd hprime).mpr hpk
    have hstab : α ∈ MulAction.stabilizer (MulAut X) m := by
      have hk : α ^ k ∈ MulAction.stabilizer (MulAut X) m := h2
      have hαu : α = (α ^ k) ^ u := by
        calc α = α ^ (v * (orderOf α : ℤ) + u * k) := by rw [huv, zpow_one]
          _ = (α ^ (orderOf α : ℤ)) ^ v * (α ^ k) ^ u := by
            rw [zpow_add, mul_comm v, zpow_mul, mul_comm u k, zpow_mul]
          _ = (α ^ k) ^ u := by
            rw [zpow_natCast, pow_orderOf_eq_one, one_zpow, one_mul]
      rw [hαu]
      exact Subgroup.zpow_mem _ hk u
    have hαm : α m = m := hstab
    exact (Subgroup.mem_bot.mpr (by rw [hfix m hαm, map_one]))
  have hQ := CFSG.BenderSuzuki.External.thompson_fixedPointFree_conjugation_nilpotent_subgroup
    Q P hnorm hP1 hfixed
  have e : X ≃* Q := MonoidHom.ofInjective (f := (SemidirectProduct.inl : X →* H))
    (SemidirectProduct.inl_injective (φ := MonoidHom.id (MulAut X)))
  have : Group.IsNilpotent Q := hQ
  exact Group.nilpotent_of_mulEquiv e.symm

end Holomorph

section Main

theorem map_center_eq_of_mulEquiv {K : Type} [Group K] (e : K ≃* K) :
    (Subgroup.center K).map e.toMonoidHom = Subgroup.center K := by
  have key : ∀ e : K ≃* K, ∀ z ∈ Subgroup.center K, e z ∈ Subgroup.center K := by
    intro e z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have h := Subgroup.mem_center_iff.mp hz (e.symm w)
    have := congrArg e h
    simpa using this
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact key e z hz
  · intro z hz
    exact ⟨e.symm z, key e.symm z hz, by simp⟩

theorem exists_fixed_in_coset {K : Type} [Group K] [Finite K]
    (hZ : ¬ 7 ∣ Nat.card (Subgroup.center K)) (α : MulAut K) (hα7 : ∀ k : K, (α ^ 7) k = k)
    (k z₀ : K) (hz₀ : z₀ ∈ Subgroup.center K) (hk : α k = k * z₀) :
    ∃ w : K, k⁻¹ * w ∈ Subgroup.center K ∧ α w = w := by
  classical
  have hcenter : ∀ z ∈ Subgroup.center K, α z ∈ Subgroup.center K := fun z hz => by
    have := map_center_eq_of_mulEquiv (K := K) α
    rw [← this]
    exact ⟨z, hz, rfl⟩
  let Ω := {w : K // k⁻¹ * w ∈ Subgroup.center K}
  have hΩ : ∀ w : Ω, k⁻¹ * α w.1 ∈ Subgroup.center K := by
    rintro ⟨w, hw⟩
    have h1 : α w = k * z₀ * α (k⁻¹ * w) := by
      have : w = k * (k⁻¹ * w) := by group
      calc α w = α (k * (k⁻¹ * w)) := by rw [← this]
        _ = α k * α (k⁻¹ * w) := map_mul _ _ _
        _ = k * z₀ * α (k⁻¹ * w) := by rw [hk]
    have h2 : k⁻¹ * α w = z₀ * α (k⁻¹ * w) := by
      rw [h1]
      group
    show k⁻¹ * α w ∈ Subgroup.center K
    rw [h2]
    exact Subgroup.mul_mem _ hz₀ (hcenter _ hw)
  let f : Function.End Ω := fun w => ⟨α w.1, hΩ w⟩
  have hfn : ∀ n : ℕ, ∀ w : Ω, ((f ^ n) w).1 = (α ^ n) w.1 := by
    intro n
    induction n with
    | zero => intro w; simp; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, pow_succ]
      show ((f ^ n) (f w)).1 = (α ^ n) (α w.1)
      exact ih (f w)
  have hf7 : f ^ 7 ^ 1 = 1 := by
    funext w
    apply Subtype.ext
    rw [pow_one, hfn]
    exact hα7 w.1
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have : Fintype Ω := Fintype.ofFinite Ω
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) hf7
  have hcard : Fintype.card Ω = Nat.card (Subgroup.center K) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun w => ⟨k⁻¹ * w.1, w.2⟩
        invFun := fun z => ⟨k * z.1, by simp⟩
        left_inv := fun w => by ext; simp
        right_inv := fun z => by ext; simp }
  by_contra hnone
  have hfix0 : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨w, hw⟩ => hnone ⟨w.1, w.2, ?_⟩⟩
    have := congrArg Subtype.val hw
    exact this
  rw [hfix0, hcard] at hmod
  exact hZ ((Nat.modEq_zero_iff_dvd).mp hmod)

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_noncentral {K : Subgroup G} {c : G} (hK : CFSG.IsQuasisimple K)
    (hZ : ¬ 7 ∣ Nat.card (Subgroup.center K)) (hc : c ∈ Subgroup.normalizer (K : Set G))
    (hc7 : c ^ 7 = 1) :
    ∃ k : K, (k : G) * c = c * (k : G) ∧ k ∉ Subgroup.center K := by
  by_contra hno
  push Not at hno
  obtain ⟨-, hsimple, a, b, hab⟩ := hK
  let α : MulAut K := K.normalizerMonoidHom ⟨c, hc⟩
  have hα : ∀ k : K, ((α k : K) : G) = c * k * c⁻¹ := fun k => rfl
  have hα7 : α ^ 7 = 1 := by
    rw [← map_pow]
    have : (⟨c, hc⟩ : Subgroup.normalizer (K : Set G)) ^ 7 = 1 := Subtype.ext hc7
    rw [this, map_one]
  let ᾱ : MulAut (K ⧸ Subgroup.center K) :=
    QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) α
      (map_center_eq_of_mulEquiv (K := K) α)
  have hᾱ : ∀ k : K, ᾱ (k : K ⧸ Subgroup.center K) = ((α k : K) : K ⧸ Subgroup.center K) :=
    fun k => QuotientGroup.congr_mk _ _ α _ k
  have hᾱn : ∀ n : ℕ, ∀ k : K, (ᾱ ^ n) (k : K ⧸ Subgroup.center K) =
      (((α ^ n) k : K) : K ⧸ Subgroup.center K) := by
    intro n
    induction n with
    | zero => intro k; rfl
    | succ n ih =>
      intro k
      rw [pow_succ, pow_succ]
      show (ᾱ ^ n) (ᾱ k) = _
      rw [hᾱ k]
      exact ih (α k)
  have hfix : ∀ x : K ⧸ Subgroup.center K, ᾱ x = x → x = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hᾱ k, QuotientGroup.eq] at hx
    have hx' : k⁻¹ * α k ∈ Subgroup.center K := by
      have := Subgroup.inv_mem _ hx
      simpa using this
    obtain ⟨w, hw, hαw⟩ := exists_fixed_in_coset hZ α (fun k => by rw [hα7]; rfl) k
      (k⁻¹ * α k) hx' (by group)
    have hwc : (w : G) * c = c * (w : G) := by
      have := congrArg (fun y : K => (y : G)) hαw
      simp only [hα] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have hw1 : w ∈ Subgroup.center K := hno w hwc
    have h3 : (w : K ⧸ Subgroup.center K) = 1 := (QuotientGroup.eq_one_iff w).mpr hw1
    have h2 : ((k : K ⧸ Subgroup.center K)) = (w : K ⧸ Subgroup.center K) :=
      (QuotientGroup.eq).mpr hw
    rw [h2]
    exact h3
  have hne : ᾱ ≠ 1 := by
    intro h1
    apply hab
    have ha : a = 1 := hfix a (by rw [h1]; rfl)
    rw [ha]
    simp
  have hα7' : ᾱ ^ 7 = 1 := by
    ext x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hᾱn 7 k, hα7]
    rfl
  have hord : (orderOf ᾱ).Prime := by
    have hdvd : orderOf ᾱ ∣ 7 := orderOf_dvd_of_pow_eq_one hα7'
    rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · rw [h]
      decide
  have hnil := isNilpotent_of_fixedPointFree_prime ᾱ hord hfix
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hsimple
  have hle := Group.nilpotencyClass_le_one_of_isSimple_of_isNilpotent (G := K ⧸ Subgroup.center K)
  have hcomm := (Group.IsNilpotent.nilpotencyClass_le_one_iff).mp hle
  exact hab (hcomm.is_comm.comm a b)

end Main

end CFSG.RankThree.PartOne.MB3
