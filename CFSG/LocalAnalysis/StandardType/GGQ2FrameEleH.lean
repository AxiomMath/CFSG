module

public import CFSG.Open.LocalVocabulary
import CFSG.CGT.PushingUpLit.CGT6X.End4Cover

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG.Open (IsElemAbelian)

private theorem eleH_centralizer_three_eq_one {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) {g : G}
    (hg : g ∈ Subgroup.centralizer (H : Set G)) (hg3 : g ^ 3 = 1) : g = 1 := by
  by_contra hg1
  have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  exact hC3 (hord ▸ Subgroup.orderOf_dvd_natCard (Subgroup.centralizer (H : Set G)) hg)

private theorem eleH_ker_three_eq_one {G R : Type} [Group G] [Finite G] {H : Subgroup G}
    [Group R] {π : ↥H →* R}
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)))
    (hker : π.ker ≤ Subgroup.center ↥H) {z : ↥H} (hz : z ∈ π.ker) (hz3 : z ^ 3 = 1) :
    z = 1 := by
  apply Subtype.ext
  refine eleH_centralizer_three_eq_one hC3 ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp (hker hz) ⟨g, hg⟩)
  · simpa using congrArg Subtype.val hz3

theorem le_of_cover_intertwine {G R : Type} [Group G] [Finite G] [Group R] {H E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H) (ρ : ↥E →* R)
    (hint : ∀ (b : ↥E) (h : ↥H),
      π (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h) = ρ b * π h * (ρ b)⁻¹)
    (hHp : commutator H = ⊤) (hEab : IsElemAbelian 3 E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) : E ≤ H := by
  intro b hb
  have : Group.IsPerfect ↥H := ⟨hHp⟩
  let bE : ↥E := ⟨b, hb⟩
  have hint' : ∀ h' : ↥H,
      π (H.normalizerMonoidHom ⟨b, hEN hb⟩ h') = ρ bE * π h' * (ρ bE)⁻¹ :=
    fun h' => hint bE h'
  let T : R := ρ bE
  have hbE3 : bE ^ 3 = 1 := by
    apply Subtype.ext
    exact hEab.2 b hb
  have hT3 : T ^ 3 = 1 := by
    show ρ bE ^ 3 = 1
    rw [← map_pow, hbE3, map_one]
  obtain ⟨x, hx⟩ := hπ T
  have hx3ker : x ^ 3 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx, hT3]
  let n : ℕ := orderOf (x ^ 3)
  have hnpos : 0 < n := orderOf_pos _
  have h3n : ¬ 3 ∣ n := by
    intro hdvd
    have hord3 : orderOf ((x ^ 3) ^ (n / 3)) = 3 := by
      refine orderOf_pow_orderOf_div (x := x ^ 3) (n := 3) ?_ ?_
      · exact ne_of_gt hnpos
      · exact hdvd
    have hne : (x ^ 3) ^ (n / 3) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord3
      norm_num at hord3
    have hmem : (x ^ 3) ^ (n / 3) ∈ π.ker :=
      Subgroup.pow_mem π.ker hx3ker (n / 3)
    have hcube : ((x ^ 3) ^ (n / 3)) ^ 3 = 1 := by
      rw [← pow_mul, Nat.div_mul_cancel hdvd]
      simp [n]
    exact hne (eleH_ker_three_eq_one hC3 hker hmem hcube)
  let k : ℕ := n % 3
  have hk : k = n % 3 := rfl
  have hmodnk : n * k % 3 = 1 := by
    have hmodne : k ≠ 0 := by
      intro hk0
      exact h3n (Nat.dvd_of_mod_eq_zero (by simpa [hk] using hk0))
    have hlt : k < 3 := by
      rw [hk]
      exact Nat.mod_lt n (by norm_num : 0 < 3)
    have hcases : k = 1 ∨ k = 2 := by omega
    rcases hcases with h1 | h2
    · rw [Nat.mul_mod, ← hk, h1]
    · rw [Nat.mul_mod, ← hk, h2]
  have hnk : n * k ≡ 1 [MOD 3] := by
    show n * k % 3 = 1 % 3
    rw [hmodnk]
  let h : ↥H := x ^ (n * k)
  have hh3 : h ^ 3 = 1 := by
    have hx3n : (x ^ 3) ^ n = 1 := by
      simp [n]
    calc h ^ 3 = (x ^ 3) ^ (n * k) := by
          show (x ^ (n * k)) ^ 3 = (x ^ 3) ^ (n * k)
          rw [← pow_mul, Nat.mul_comm (n * k) 3, pow_mul]
      _ = ((x ^ 3) ^ n) ^ k := by rw [pow_mul]
      _ = 1 := by rw [hx3n, one_pow]
  have hπh : π h = T := by
    show π (x ^ (n * k)) = T
    rw [map_pow, hx]
    simpa using pow_eq_pow_of_modEq hnk hT3
  let y : ↥H := H.normalizerMonoidHom ⟨b, hEN hb⟩ h
  have hyπ : π y = T := by
    rw [show y = H.normalizerMonoidHom ⟨b, hEN hb⟩ h from rfl, hint' h, hπh]
    change T * T * T⁻¹ = T
    group
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    have hcoe : (y : G) = b * (h : G) * b⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨b, hEN hb⟩ h
    have hh3G : (h : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hh3
    change (y : G) ^ 3 = 1
    rw [hcoe, conj_pow, hh3G]
    simp
  let z : ↥H := h⁻¹ * y
  have hzker : z ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    show π (h⁻¹ * y) = 1
    rw [map_mul, map_inv, hπh, hyπ]
    exact inv_mul_cancel T
  have hzcenter : z ∈ Subgroup.center ↥H := hker hzker
  have hzy : y = h * z := by
    show y = h * (h⁻¹ * y)
    exact (mul_inv_cancel_left h y).symm
  have hcommhz : Commute h z := Subgroup.mem_center_iff.mp hzcenter h
  have hy3z : y ^ 3 = z ^ 3 := by
    rw [hzy, Commute.mul_pow hcommhz, hh3, one_mul]
  have hz3 : z ^ 3 = 1 := by
    rw [← hy3z]
    exact hy3
  have hz1 : z = 1 := eleH_ker_three_eq_one hC3 hker hzker hz3
  have hyh : y = h := by
    rw [hzy, hz1, mul_one]
  have hcoe_y : (y : G) = b * (h : G) * b⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨b, hEN hb⟩ h
  have hbh : b * (h : G) = (h : G) * b := by
    have h1 : b * (h : G) * b⁻¹ = (h : G) := by
      calc b * (h : G) * b⁻¹ = (y : G) := hcoe_y.symm
        _ = (h : G) := congrArg Subtype.val hyh
    calc b * (h : G) = (b * (h : G) * b⁻¹) * b := by group
      _ = (h : G) * b := by rw [h1]
  let f₁ : ↥H →* ↥H := H.normalizerMonoidHom ⟨b, hEN hb⟩
  let f₂ : ↥H →* ↥H :=
    H.normalizerMonoidHom ⟨(h : G), Subgroup.le_normalizer h.2⟩
  have hf1 : ∀ h' : ↥H, π (f₁ h') = T * π h' * T⁻¹ := by
    intro h'
    simpa [f₁, T] using hint' h'
  have hf2 : ∀ h' : ↥H, π (f₂ h') = T * π h' * T⁻¹ := by
    intro h'
    have hcoe : ((f₂ h' : ↥H) : G) = (h : G) * (h' : G) * (h : G)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe H
        ⟨(h : G), Subgroup.le_normalizer h.2⟩ h'
    have hf2eq : f₂ h' = h * h' * h⁻¹ := Subtype.ext hcoe
    calc π (f₂ h') = π (h * h' * h⁻¹) := by rw [hf2eq]
      _ = π h * π h' * (π h)⁻¹ := by simp only [map_mul, map_inv]
      _ = T * π h' * T⁻¹ := by rw [hπh]
  have hcentral : ∀ h' : ↥H, f₁ h' * (f₂ h')⁻¹ ∈ Subgroup.center ↥H := by
    intro h'
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hf1 h', hf2 h']
    exact mul_inv_cancel _
  have hfeq : f₁ = f₂ :=
    CFSG.CGT.PushingUpLit.CGT6X.End4.hom_eq_of_central f₁ f₂ hcentral
  let c : G := (h : G)⁻¹ * b
  have hc : c ∈ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    let g' : ↥H := ⟨g, hg⟩
    have hfg : f₁ g' = f₂ g' := by rw [hfeq]
    have hcoe1 : ((f₁ g' : ↥H) : G) = b * g * b⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨b, hEN hb⟩ g'
    have hcoe2 : ((f₂ g' : ↥H) : G) = (h : G) * g * (h : G)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe H
        ⟨(h : G), Subgroup.le_normalizer h.2⟩ g'
    have hbg : b * g * b⁻¹ = (h : G) * g * (h : G)⁻¹ := by
      rw [← hcoe1, ← hcoe2, hfg]
    show g * c = c * g
    have hconj : (h : G)⁻¹ * b * g = g * ((h : G)⁻¹ * b) := by
      calc (h : G)⁻¹ * b * g = (h : G)⁻¹ * (b * g) := by group
        _ = (h : G)⁻¹ * (b * g * b⁻¹ * b) := by group
        _ = (h : G)⁻¹ * ((h : G) * g * (h : G)⁻¹ * b) := by rw [hbg]
        _ = g * ((h : G)⁻¹ * b) := by group
    exact hconj.symm
  have hb3 : b ^ 3 = 1 := hEab.2 b hb
  have hh3G : (h : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hh3
  have hcomm_c : Commute ((h : G)⁻¹) b := by
    have hcomm_bh : Commute b (h : G) := hbh
    exact hcomm_bh.inv_right.symm
  have hc3 : c ^ 3 = 1 := by
    show ((h : G)⁻¹ * b) ^ 3 = 1
    rw [Commute.mul_pow hcomm_c, inv_pow, hh3G, inv_one, hb3, one_mul]
  have hc1 : c = 1 := eleH_centralizer_three_eq_one hC3 hc hc3
  have hb_eq : b = (h : G) := by
    have h1 : (h : G) * c = b := by
      show (h : G) * ((h : G)⁻¹ * b) = b
      exact mul_inv_cancel_left _ _
    rw [hc1, mul_one] at h1
    exact h1.symm
  rw [hb_eq]
  exact h.2

end CFSG.StandardType.GGQ2Frame
