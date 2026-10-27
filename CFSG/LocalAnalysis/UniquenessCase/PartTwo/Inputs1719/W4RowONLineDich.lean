module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Extra


public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Dickson.I271 (SevenLine)

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] {w : X} {F : Subgroup X}

omit [Finite X] in
private theorem mulAut_apply_apply_of_mul_self {α : MulAut X} (hα2 : α * α = 1) (x : X) :
    α (α x) = x := by
  have := congrArg (fun β : MulAut X => β x) hα2
  simpa using this

omit [Finite X] in
private theorem mulAut_fix_zpowers_of_fix {α : MulAut X} {w : X} (hαw : α w = w) :
    ∀ x ∈ Subgroup.zpowers w, α x = x := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [map_zpow, hαw]

omit [Finite X] [Fact p.Prime] in
private theorem sevenLine_pow_card_eq_one (h : SevenLine p w F) {x : X} (hx : x ∈ F) :
    x ^ (p ^ 3) = 1 := by
  have h1 : (⟨x, hx⟩ : F) ^ Nat.card F = 1 := pow_card_eq_one'
  rw [h.card_eq] at h1
  simpa using congrArg Subtype.val h1

omit [Finite X] [Fact p.Prime] in
private theorem sevenLine_map_mem (h : SevenLine p w F) {α : MulAut X} (hαw : α w = w) :
    ∀ f ∈ F, α f ∈ F := by
  intro f hf
  have hC : α f ∈ Subgroup.centralizer ({w} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc α f * w = α f * α w := by rw [hαw]
      _ = α (f * w) := (map_mul α f w).symm
      _ = α (w * f) := by rw [h.comm_w hf]
      _ = w * α f := by rw [map_mul, hαw]
  refine h.syl (α f) hC ⟨3, ?_⟩
  rw [← map_pow, sevenLine_pow_card_eq_one h hf, map_one]

omit [Finite X] [Fact p.Prime] in
private theorem sevenLine_zpowers_comm (h : SevenLine p w F) {c z : X}
    (hc : c ∈ Subgroup.zpowers w) (hz : z ∈ F) : c * z = z * c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  exact ((show Commute w z from h.comm_w hz).zpow_left k).eq

private theorem sevenLine_commute_of_involution_data (h : SevenLine p w F) (hp2 : p ≠ 2)
    {α : MulAut X} (hαw : α w = w) {u v c₀ : X} (huF : u ∈ F) (hvF : v ∈ F)
    (hc₀Z : c₀ ∈ Subgroup.zpowers w) (hαu : α u = u * c₀) (hαv : α v = v⁻¹) :
    u * v = v * u := by
  have hp := (Fact.out : p.Prime)
  have hfixZ := mulAut_fix_zpowers_of_fix hαw
  obtain ⟨d, hdZ, hd⟩ := h.comm_mem huF hvF
  have hleft : α (u * v * u⁻¹) = v⁻¹ * d⁻¹ := by
    rw [map_mul, map_mul, map_inv, hαu, hαv]
    have hc₀v : c₀ * v⁻¹ = v⁻¹ * c₀ :=
      (Commute.inv_right (sevenLine_zpowers_comm h hc₀Z hvF)).eq
    calc (u * c₀) * v⁻¹ * (u * c₀)⁻¹ = u * (c₀ * v⁻¹ * c₀⁻¹) * u⁻¹ := by group
      _ = u * v⁻¹ * u⁻¹ := by
            rw [show c₀ * v⁻¹ * c₀⁻¹ = v⁻¹ by rw [hc₀v]; group]
      _ = (u * v * u⁻¹)⁻¹ := by group
      _ = (v * d)⁻¹ := by rw [hd]
      _ = v⁻¹ * d⁻¹ := by
            rw [mul_inv_rev]
            exact (Commute.inv_inv (sevenLine_zpowers_comm h hdZ hvF)).eq
  have hright : α (v * d) = v⁻¹ * d := by
    rw [map_mul, hαv, hfixZ d hdZ]
  have heq : v⁻¹ * d⁻¹ = v⁻¹ * d := by rw [← hleft, ← hright]; exact congrArg α hd
  have hd2 : d⁻¹ = d := mul_left_cancel heq
  have hdd : d ^ 2 = 1 := by
    rw [pow_two]
    have hh := inv_mul_cancel d
    rwa [hd2] at hh
  have hdp : d ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hdZ
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.pow_eq, one_zpow]
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.2 (hp.odd_of_ne_two hp2)
  have hdvd : orderOf d ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hdd) (orderOf_dvd_of_pow_eq_one hdp)
  have hd1 : d = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)
  calc u * v = (u * v * u⁻¹) * u := by group
    _ = (v * d) * u := by rw [hd]
    _ = v * u := by rw [hd1, mul_one]

private theorem sevenLine_closure_pair_eq_cent (h : SevenLine p w F) {u : X} (huF : u ∈ F)
    (hu_not : u ∉ Subgroup.zpowers w) :
    Subgroup.closure ({u, w} : Set X) = F ⊓ Subgroup.centralizer ({u} : Set X) := by
  have hp := (Fact.out : p.Prime)
  set H : Subgroup X := F ⊓ Subgroup.centralizer ({u} : Set X) with hH
  set K : Subgroup X := Subgroup.closure ({u, w} : Set X) with hK
  have hHcard : Nat.card H ≤ p ^ 2 := by
    rw [hH]
    exact h.card_cent_le huF hu_not
  have huK : u ∈ K := by rw [hK]; exact Subgroup.subset_closure (by simp)
  have hwK : w ∈ K := by rw [hK]; exact Subgroup.subset_closure (by simp)
  have hzwK : Subgroup.zpowers w ≤ K := (Subgroup.zpowers_le).2 hwK
  have hkc : Nat.card (Subgroup.zpowers w) = p := by rw [Nat.card_zpowers, h.orderOf_w]
  have hKF : K ≤ F := by
    rw [hK, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact huF
    · exact h.mem
  have hKH : K ≤ H := by
    rw [hK, hH, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨huF, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
    · exact ⟨h.mem, Subgroup.mem_centralizer_singleton_iff.2 (h.comm_w huF)⟩
  have hdvd : Nat.card K ∣ p ^ 3 := by
    rw [← h.card_eq]
    exact Subgroup.card_dvd_of_le hKF
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hk1 : 1 ≤ k := by
    by_contra hk0
    push Not at hk0
    have hk0' : k = 0 := by omega
    have hKone : Nat.card K = 1 := by rw [hk, hk0']; simp
    have hle := Subgroup.card_le_of_le hzwK
    rw [hKone, hkc] at hle
    exact absurd hle (not_le.2 hp.one_lt)
  have hk2 : 2 ≤ k := by
    by_contra hklt
    push Not at hklt
    have hk1' : k = 1 := by omega
    have hKeq : Subgroup.zpowers w = K := Subgroup.eq_of_le_of_card_ge hzwK (by
      rw [hk, hk1', hkc]; simp)
    have huK' : u ∈ Subgroup.zpowers w := by rw [hKeq]; exact huK
    exact hu_not huK'
  have hKle : Nat.card K ≤ p ^ 2 := le_trans (Subgroup.card_le_of_le hKH) hHcard
  have hk2eq : k = 2 := by
    have hk_le : k ≤ 2 := by
      by_contra hkgt
      push Not at hkgt
      rw [hk] at hKle
      have h3 : p ^ 3 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
      exact absurd (le_trans h3 hKle)
        (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
    omega
  have hKcard : Nat.card K = p ^ 2 := by rw [hk, hk2eq]
  have hKeq : K = H := Subgroup.eq_of_le_of_card_ge hKH (by rw [hKcard]; exact hHcard)
  simpa [hK, hH] using hKeq

private theorem sevenLine_mem_closure_pair (h : SevenLine p w F) {u v : X} (huF : u ∈ F)
    (hu_not : u ∉ Subgroup.zpowers w) (hvF : v ∈ F) (huv : u * v = v * u) :
    v ∈ Subgroup.closure ({u, w} : Set X) := by
  rw [sevenLine_closure_pair_eq_cent h huF hu_not]
  exact ⟨hvF, Subgroup.mem_centralizer_singleton_iff.2 huv.symm⟩

omit [Finite X] in
private theorem sevenLine_mem_zpowers_of_inv_data (h : SevenLine p w F) (hp2 : p ≠ 2)
    {α : MulAut X} (hαw : α w = w) {u v c₀ : X} (huF : u ∈ F) (hvF : v ∈ F)
    (huw : u * w = w * u) (hc₀Z : c₀ ∈ Subgroup.zpowers w)
    (hvK : v ∈ Subgroup.closure ({u, w} : Set X)) (hαu : α u = u * c₀)
    (hαv : α v = v⁻¹) : v ∈ Subgroup.zpowers w := by
  obtain ⟨m, n, hmn⟩ :=
    CFSG.GH74.GLS.Layer3.mem_closure_pair_of_commute huw hvK
  have hcu : Commute u c₀ := (sevenLine_zpowers_comm h hc₀Z huF).symm
  have hcw : Commute c₀ w := sevenLine_zpowers_comm h hc₀Z h.mem
  have hαv_expr : α v = v * c₀ ^ m := by
    rw [hmn, map_mul, map_zpow, map_zpow, hαu, hαw, hcu.mul_zpow]
    calc u ^ m * c₀ ^ m * w ^ n = u ^ m * (c₀ ^ m * w ^ n) := by group
      _ = u ^ m * (w ^ n * c₀ ^ m) := by rw [(hcw.zpow_zpow m n).eq]
      _ = u ^ m * w ^ n * c₀ ^ m := by group
  have hαv_inv : v * c₀ ^ m = v⁻¹ := by rw [← hαv_expr, hαv]
  have hvv : v * v * c₀ ^ m = 1 := by
    have hh := congrArg (fun x => v * x) hαv_inv
    rwa [← mul_assoc, mul_inv_cancel] at hh
  have hv2 : v ^ 2 = c₀ ^ (-m) := by
    rw [pow_two, eq_inv_of_mul_eq_one_left hvv, ← zpow_neg]
  have hv2Z : v ^ 2 ∈ Subgroup.zpowers w := by
    rw [hv2]
    exact Subgroup.zpow_mem _ hc₀Z (-m)
  have hp := (Fact.out : p.Prime)
  have hvpow : v ^ (p ^ 3) = 1 := sevenLine_pow_card_eq_one h hvF
  have hdvdv : orderOf v ∣ p ^ 3 := orderOf_dvd_of_pow_eq_one hvpow
  have hcop2p : Nat.Coprime 2 (p ^ 3) :=
    Nat.coprime_two_left.2 ((hp.odd_of_ne_two hp2).pow)
  have hcop2v : Nat.Coprime 2 (orderOf v) := hcop2p.coprime_dvd_right hdvdv
  obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime (x := v) hcop2v
  rw [← hr]
  exact Subgroup.pow_mem _ hv2Z r

theorem sevenLine_fix_or_inv_mod (h : SevenLine p w F) (hp2 : p ≠ 2) {α : MulAut X}
    (hα2 : α * α = 1) (hαw : α w = w) :
    (∀ f ∈ F, α f * f⁻¹ ∈ Subgroup.zpowers w) ∨ (∀ f ∈ F, α f * f ∈ Subgroup.zpowers w) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨f₁, hf₁, hv_not⟩, ⟨f₂, hf₂, hu_not⟩⟩ := hcon
  have hαα := mulAut_apply_apply_of_mul_self hα2
  set u : X := α f₂ * f₂ with hu_def
  set v : X := α f₁ * f₁⁻¹ with hv_def
  have huF : u ∈ F := by
    rw [hu_def]
    exact mul_mem (sevenLine_map_mem h hαw f₂ hf₂) hf₂
  have hvF : v ∈ F := by
    rw [hv_def]
    exact mul_mem (sevenLine_map_mem h hαw f₁ hf₁) (inv_mem hf₁)
  have hαu_eq : α u = f₂ * u * f₂⁻¹ := by
    rw [hu_def, map_mul, hαα f₂]
    group
  obtain ⟨c₀, hc₀Z, hc₀eq⟩ := h.comm_mem hf₂ huF
  have hαu : α u = u * c₀ := by rw [hαu_eq, hc₀eq]
  have hαv : α v = v⁻¹ := by
    rw [hv_def, map_mul, map_inv, hαα f₁]
    group
  have huv : u * v = v * u :=
    sevenLine_commute_of_involution_data h hp2 hαw huF hvF hc₀Z hαu hαv
  have hvK : v ∈ Subgroup.closure ({u, w} : Set X) :=
    sevenLine_mem_closure_pair h huF hu_not hvF huv
  have huw : u * w = w * u := (h.comm_w huF).symm
  have hvZ : v ∈ Subgroup.zpowers w :=
    sevenLine_mem_zpowers_of_inv_data h hp2 hαw huF hvF huw hc₀Z hvK hαu hαv
  exact hv_not hvZ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
