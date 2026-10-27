module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts
public import CFSG.RankThree.Asc83Table.E9

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

section Dihedral

variable {Y : Type*} [Group Y]

@[expose] def dihedralSixLift (s ρ : Y) : DihedralGroup 6 → Y
  | .r i => ρ ^ i.val
  | .sr i => s * ρ ^ i.val

theorem pow_val_add_six {ρ : Y} (hρ : ρ ^ 6 = 1) (i j : ZMod 6) :
    ρ ^ (i + j).val = ρ ^ i.val * ρ ^ j.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hρ]

theorem pow_val_sub_six {ρ : Y} (hρ : ρ ^ 6 = 1) (i j : ZMod 6) :
    ρ ^ (j - i).val = (ρ ^ i.val)⁻¹ * ρ ^ j.val := by
  have h : ρ ^ (j - i).val * ρ ^ i.val = ρ ^ j.val := by
    rw [← pow_val_add_six hρ, sub_add_cancel]
  rw [eq_inv_mul_iff_mul_eq, ← h, ← pow_add, ← pow_add, add_comm]

theorem conj_pow_of_inv {s ρ : Y} (hs : s * s = 1) (hsρ : s * ρ * s = ρ⁻¹) (k : ℕ) :
    s * ρ ^ k * s = (ρ ^ k)⁻¹ := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have h : (s * ρ * s⁻¹) ^ k = s * ρ ^ k * s⁻¹ := conj_pow
  rw [hsi, hsρ, inv_pow] at h
  exact h.symm

theorem dihedralSixLift_mul {s ρ : Y} (hs : s * s = 1) (hρ : ρ ^ 6 = 1)
    (hsρ : s * ρ * s = ρ⁻¹) (x y : DihedralGroup 6) :
    dihedralSixLift s ρ (x * y) = dihedralSixLift s ρ x * dihedralSixLift s ρ y := by
  have hc : ∀ k : ℕ, ρ ^ k * s = s * (ρ ^ k)⁻¹ := fun k => by
    rw [← conj_pow_of_inv hs hsρ k, ← mul_assoc, ← mul_assoc, hs, one_mul]
  rcases x with i | i <;> rcases y with j | j
  · simp only [DihedralGroup.r_mul_r, dihedralSixLift]
    exact pow_val_add_six hρ i j
  · simp only [DihedralGroup.r_mul_sr, dihedralSixLift]
    rw [pow_val_sub_six hρ, ← mul_assoc (ρ ^ i.val) s, hc, mul_assoc]
  · simp only [DihedralGroup.sr_mul_r, dihedralSixLift]
    rw [pow_val_add_six hρ, mul_assoc]
  · simp only [DihedralGroup.sr_mul_sr, dihedralSixLift]
    rw [pow_val_sub_six hρ, ← mul_assoc, mul_assoc s, hc, ← mul_assoc, hs, one_mul]

@[expose] def dihedralSixHom {s ρ : Y} (hs : s * s = 1) (hρ : ρ ^ 6 = 1)
    (hsρ : s * ρ * s = ρ⁻¹) : DihedralGroup 6 →* Y :=
  MonoidHom.mk' (dihedralSixLift s ρ) (dihedralSixLift_mul hs hρ hsρ)

theorem dihedralSixHom_injective {s ρ : Y} (hs : s * s = 1) (hρ : ρ ^ 6 = 1)
    (hsρ : s * ρ * s = ρ⁻¹) (hord : orderOf ρ = 6) :
    Function.Injective (dihedralSixHom hs hρ hsρ) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) hx
  · have h1 : ρ ^ i.val = 1 := hx
    have h2 : orderOf ρ ∣ i.val := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h2
    have h3 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt i)
    rw [ZMod.val_eq_zero] at h3
    rw [h3]
    rfl
  · exfalso
    have h1 : s * ρ ^ i.val = 1 := hx
    have hs' : s = (ρ ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hcomm : s * ρ = ρ * s := by
      rw [hs']
      exact ((Commute.refl ρ).pow_left i.val).inv_left.eq
    have hρ2 : ρ ^ 2 = 1 := by
      have h := hsρ
      rw [hcomm, mul_assoc, hs, mul_one] at h
      rw [sq]
      calc ρ * ρ = ρ⁻¹ * ρ := by rw [← h]
        _ = 1 := inv_mul_cancel ρ
    have h2 := orderOf_dvd_of_pow_eq_one hρ2
    rw [hord] at h2
    omega

end Dihedral

section Pair

variable {X : Type} [Group X]

theorem conj_mul_eq (g x y : X) : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by
  group

theorem conj_inv_eq (g x : X) : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by
  group

theorem conj_conj_eq (g h x : X) : g * h * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by
  group

theorem mem_normalizer_of_conj_mem [Finite X] {D : Subgroup X} {c d g : X}
    (hgen : Subgroup.closure ({c, d} : Set X) = D) (hc : g * c * g⁻¹ ∈ D)
    (hd : g * d * g⁻¹ ∈ D) : g ∈ Subgroup.normalizer (D : Set X) := by
  have hle : D.map (MulAut.conj g).toMonoidHom ≤ D := by
    rw [← hgen, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | hx
    · rw [hgen]
      exact hc
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [hgen]
      exact hd
  have heq : D.map (MulAut.conj g).toMonoidHom = D :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := (MulAut.conj g).injective hyx
    rw [← this]
    exact hy

end Pair

section Automizer

variable {X : Type} [Group X] [Finite X] {D : Subgroup X} {c d : X} {K : Subgroup X}

theorem closure_pair_eq_of_config (h : InnerConfig424 X D c d K) :
    Subgroup.closure ({c, d} : Set X) = D := by
  have hDe := h.maximal.prop
  have hc3 : c ^ 3 = 1 := hDe.2 c h.c_mem
  have hd3 : d ^ 3 = 1 := hDe.2 d h.d_mem
  have hcd : Commute c d := by
    have h1 := hDe.1.is_comm.comm ⟨c, h.c_mem⟩ ⟨d, h.d_mem⟩
    exact congrArg Subtype.val h1
  have hcard := CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hc3 hd3 hcd h.c_ne_one
    h.d_not_mem
  have hle : Subgroup.closure ({c, d} : Set X) ≤ D := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨h.c_mem, h.d_mem⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h.card_eq])

theorem mulAut_ext_of_config (h : InnerConfig424 X D c d K) {φ ψ : MulAut D}
    (h1 : φ ⟨c, h.c_mem⟩ = ψ ⟨c, h.c_mem⟩) (h2 : φ ⟨d, h.d_mem⟩ = ψ ⟨d, h.d_mem⟩) : φ = ψ := by
  have hgen : Subgroup.closure ({⟨c, h.c_mem⟩, ⟨d, h.d_mem⟩} : Set D) = ⊤ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, Set.image_pair]
    exact closure_pair_eq_of_config h
  have hle : Subgroup.closure ({⟨c, h.c_mem⟩, ⟨d, h.d_mem⟩} : Set D) ≤
      (φ : D →* D).eqLocus (ψ : D →* D) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact h1
    · exact h2
  rw [hgen] at hle
  exact MulEquiv.ext fun x => hle (Subgroup.mem_top x)

theorem c_not_mem_zpowers_d (h : InnerConfig424 X D c d K) : c ∉ Subgroup.zpowers d := by
  have hDe := h.maximal.prop
  have hc3 : c ^ 3 = 1 := hDe.2 c h.c_mem
  rintro ⟨k, hk⟩
  apply h.d_not_mem
  change d ^ k = c at hk
  have hd3 : d ^ 3 = 1 := hDe.2 d h.d_mem
  have hk3 : ¬ (3 : ℤ) ∣ k := by
    rintro ⟨m, rfl⟩
    apply h.c_ne_one
    rw [← hk, zpow_mul, zpow_ofNat, hd3, one_zpow]
  refine ⟨k, ?_⟩
  change c ^ k = d
  rw [← hk, ← zpow_mul]
  have hkk : k * k % 3 = 1 := by
    have h1 : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> rw [Int.mul_emod, h1] <;> norm_num
  rw [zpow_eq_zpow_emod' (k * k) hd3]
  push_cast
  rw [hkk, zpow_one]

theorem card_autIn_le_twelve (h : InnerConfig424 X D c d K) :
    Nat.card (autIn (⊤ : Subgroup X) D) ≤ 12 := by
  classical
  have hDe := h.maximal.prop
  set c' : D := ⟨c, h.c_mem⟩
  set d' : D := ⟨d, h.d_mem⟩
  have hd3 : d' ^ 3 = 1 := Subtype.ext (hDe.2 d h.d_mem)
  have hd1 : d' ≠ 1 := by
    intro h1
    apply h.d_not_mem
    rw [show d = 1 from congrArg Subtype.val h1]
    exact Subgroup.one_mem _
  have hcd : c' ∉ Subgroup.zpowers d' := by
    rintro ⟨k, hk⟩
    exact c_not_mem_zpowers_d h ⟨k, by simpa using congrArg Subtype.val hk⟩
  have key : ∀ σ ∈ autIn (⊤ : Subgroup X) D, σ d' ∈ Subgroup.zpowers d' := by
    intro σ hσ
    obtain ⟨g, hN, -, rfl⟩ := mem_autIn_iff.mp hσ
    have hgd := h.normalizer_le hN
    have h1 : g * d * g⁻¹ ∈ Subgroup.zpowers d :=
      (Subgroup.mem_normalizer_iff.mp hgd d).mp (Subgroup.mem_zpowers d)
    obtain ⟨k, hk⟩ := h1
    change d ^ k = g * d * g⁻¹ at hk
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_zpow]
    rw [normalizerMonoidHom_apply_coe]
    exact hk
  have hval : ∀ σ ∈ autIn (⊤ : Subgroup X) D, σ c' ∉ Subgroup.zpowers d' ∧
      (σ d' = d' ∨ σ d' = d'⁻¹) := by
    intro σ hσ
    refine ⟨fun hc => hcd ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hc
      change d' ^ k = σ c' at hk
      have hσi := key σ⁻¹ (inv_mem hσ)
      obtain ⟨m, hm⟩ := hσi
      change d' ^ m = σ⁻¹ d' at hm
      refine ⟨m * k, ?_⟩
      change d' ^ (m * k) = c'
      have e1 : c' = σ⁻¹ (σ c') := by simp
      rw [e1, ← hk, map_zpow, ← hm, zpow_mul]
    · obtain ⟨k, hk⟩ := key σ hσ
      change d' ^ k = σ d' at hk
      have hσ1 : σ d' ≠ 1 := fun h1 => hd1 (σ.injective (h1.trans (map_one σ).symm))
      have hkd : d' ^ k = d' ^ (k % 3) := by
        rw [zpow_eq_zpow_emod' k hd3]
        push_cast
        rfl
      have hkmod : k % 3 = 1 ∨ k % 3 = 2 := by
        have h0 : k % 3 ≠ 0 := by
          intro h0
          apply hσ1
          rw [← hk, hkd, h0, zpow_zero]
        omega
      rcases hkmod with h1 | h1
      · left
        rw [← hk, hkd, h1, zpow_one]
      · right
        rw [← hk, hkd, h1, eq_inv_iff_mul_eq_one, ← zpow_add_one]
        exact (zpow_natCast d' 3).trans hd3
  let f : autIn (⊤ : Subgroup X) D → {x : D // x ∉ Subgroup.zpowers d'} × Bool :=
    fun σ => (⟨(σ : MulAut D) c', (hval σ σ.2).1⟩, decide ((σ : MulAut D) d' = d'))
  have hf : Function.Injective f := by
    intro σ τ hστ
    have h1 : (σ : MulAut D) c' = (τ : MulAut D) c' := congrArg (fun p => (p.1 : D)) hστ
    have h2 : decide ((σ : MulAut D) d' = d') = decide ((τ : MulAut D) d' = d') :=
      congrArg Prod.snd hστ
    have h2' : (σ : MulAut D) d' = (τ : MulAut D) d' := by
      rcases (hval σ σ.2).2 with hs | hs <;> rcases (hval τ τ.2).2 with ht | ht
      · rw [hs, ht]
      · exfalso
        rw [hs, ht] at h2
        have hne : d'⁻¹ ≠ d' := by
          intro he
          apply hd1
          have : d' ^ 2 = 1 := by rw [sq]; nth_rewrite 1 [← he]; exact inv_mul_cancel d'
          have h3 : d' = d' ^ 3 * (d' ^ 2)⁻¹ := by group
          rw [h3, hd3, this, inv_one, one_mul]
        simp [hne] at h2
      · exfalso
        rw [hs, ht] at h2
        have hne : d'⁻¹ ≠ d' := by
          intro he
          apply hd1
          have : d' ^ 2 = 1 := by rw [sq]; nth_rewrite 1 [← he]; exact inv_mul_cancel d'
          have h3 : d' = d' ^ 3 * (d' ^ 2)⁻¹ := by group
          rw [h3, hd3, this, inv_one, one_mul]
        simp [hne] at h2
      · rw [hs, ht]
    exact Subtype.ext (mulAut_ext_of_config h h1 h2')
  have hcard := Nat.card_le_card_of_injective f hf
  have hC : Nat.card {x : D // x ∉ Subgroup.zpowers d'} = 6 := by
    have : Fintype D := Fintype.ofFinite D
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, h.card_eq]
    have hz : Nat.card {x : D // x ∈ Subgroup.zpowers d'} = 3 := by
      have h1 := Nat.card_zpowers d'
      rw [orderOf_eq_prime hd3 hd1] at h1
      exact h1
    rw [hz]
  have hb : Nat.card Bool = 2 := by simp
  rw [Nat.card_prod, hC, hb] at hcard
  exact hcard

omit [Finite X] in
theorem normalizerMonoidHom_pow_apply {g : X} (hN : g ∈ Subgroup.normalizer (D : Set X))
    (k : ℕ) (x : D) :
    (((D.normalizerMonoidHom ⟨g, hN⟩ ^ k) x : D) : X) = g ^ k * x * (g ^ k)⁻¹ := by
  rw [← map_pow]
  rfl

theorem nonempty_autIn_dihedral_of_borel (h : InnerConfig424 X D c d K) {a b t : X}
    (ha : a * d * a⁻¹ = d⁻¹ ∧ a * c * a⁻¹ = c) (hb : b * d * b⁻¹ = d ∧ b * c * b⁻¹ = c⁻¹)
    (ht : t * d * t⁻¹ = d ∧ t * c * t⁻¹ = c * d) :
    Nonempty (autIn (⊤ : Subgroup X) D ≃* DihedralGroup 6) := by
  classical
  have hDe := h.maximal.prop
  have hc3 : c ^ 3 = 1 := hDe.2 c h.c_mem
  have hd3 : d ^ 3 = 1 := hDe.2 d h.d_mem
  have hcd : c * d = d * c :=
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨c, h.c_mem⟩ ⟨d, h.d_mem⟩)
  have hgen := closure_pair_eq_of_config h
  have hd1 : d ≠ 1 := fun h1 => h.d_not_mem (h1 ▸ Subgroup.one_mem _)
  have hcdi : d⁻¹ * c⁻¹ = c⁻¹ * d⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hcd]
  set r := a * b * t with hr
  have hr_d : r * d * r⁻¹ = d⁻¹ := by
    rw [hr, conj_conj_eq, ht.1, conj_conj_eq, hb.1, ha.1]
  have hr_c : r * c * r⁻¹ = c⁻¹ * d⁻¹ := by
    rw [hr, conj_conj_eq, ht.2, conj_mul_eq, conj_conj_eq, conj_conj_eq, hb.2, hb.1, conj_inv_eq,
      ha.2, ha.1]
  clear_value r
  have hr2_c : r ^ 2 * c * (r ^ 2)⁻¹ = d * c * d :=
    calc r ^ 2 * c * (r ^ 2)⁻¹ = r * (r * c * r⁻¹) * r⁻¹ := by
          rw [sq, mul_inv_rev]; simp only [mul_assoc]
      _ = r * (c⁻¹ * d⁻¹) * r⁻¹ := by rw [hr_c]
      _ = (r * c * r⁻¹)⁻¹ * (r * d * r⁻¹)⁻¹ := by group
      _ = (c⁻¹ * d⁻¹)⁻¹ * (d⁻¹)⁻¹ := by rw [hr_c, hr_d]
      _ = d * c * d := by group
  have hr3_c : r ^ 3 * c * (r ^ 3)⁻¹ = c⁻¹ :=
    calc r ^ 3 * c * (r ^ 3)⁻¹ = r * (r ^ 2 * c * (r ^ 2)⁻¹) * r⁻¹ := by
          rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
      _ = r * (d * c * d) * r⁻¹ := by rw [hr2_c]
      _ = (r * d * r⁻¹) * (r * c * r⁻¹) * (r * d * r⁻¹) := by group
      _ = d⁻¹ * (c⁻¹ * d⁻¹) * d⁻¹ := by rw [hr_d, hr_c]
      _ = (d⁻¹ * c⁻¹) * d⁻¹ * d⁻¹ := by group
      _ = c⁻¹ * (d ^ 3)⁻¹ := by rw [hcdi]; group
      _ = c⁻¹ := by rw [hd3, inv_one, mul_one]
  have hr3_d : r ^ 3 * d * (r ^ 3)⁻¹ = d⁻¹ :=
    calc r ^ 3 * d * (r ^ 3)⁻¹ = r * (r * (r * d * r⁻¹) * r⁻¹) * r⁻¹ := by
          rw [pow_succ', sq, mul_inv_rev, mul_inv_rev]; simp only [mul_assoc]
      _ = r * (r * d⁻¹ * r⁻¹) * r⁻¹ := by rw [hr_d]
      _ = r * (r * d * r⁻¹)⁻¹ * r⁻¹ := by group
      _ = r * d⁻¹⁻¹ * r⁻¹ := by rw [hr_d]
      _ = d⁻¹ := by rw [inv_inv, hr_d]
  have hw_c : (a * r * a * r) * c * (a * r * a * r)⁻¹ = c :=
    calc (a * r * a * r) * c * (a * r * a * r)⁻¹ =
          a * (r * (a * (r * c * r⁻¹) * a⁻¹) * r⁻¹) * a⁻¹ := by group
      _ = a * (r * (a * (c⁻¹ * d⁻¹) * a⁻¹) * r⁻¹) * a⁻¹ := by rw [hr_c]
      _ = a * (r * ((a * c * a⁻¹)⁻¹ * (a * d * a⁻¹)⁻¹) * r⁻¹) * a⁻¹ := by group
      _ = a * (r * (c⁻¹ * (d⁻¹)⁻¹) * r⁻¹) * a⁻¹ := by rw [ha.2, ha.1]
      _ = a * ((r * c * r⁻¹)⁻¹ * (r * d * r⁻¹)) * a⁻¹ := by group
      _ = a * ((c⁻¹ * d⁻¹)⁻¹ * d⁻¹) * a⁻¹ := by rw [hr_c, hr_d]
      _ = (a * d * a⁻¹) * (a * c * a⁻¹) * (a * d * a⁻¹)⁻¹ := by group
      _ = d⁻¹ * (c * d) := by rw [ha.1, ha.2]; group
      _ = c := by rw [hcd]; group
  have hw_d : (a * r * a * r) * d * (a * r * a * r)⁻¹ = d :=
    calc (a * r * a * r) * d * (a * r * a * r)⁻¹ =
          a * (r * (a * (r * d * r⁻¹) * a⁻¹) * r⁻¹) * a⁻¹ := by group
      _ = a * (r * (a * d⁻¹ * a⁻¹) * r⁻¹) * a⁻¹ := by rw [hr_d]
      _ = a * (r * (a * d * a⁻¹)⁻¹ * r⁻¹) * a⁻¹ := by group
      _ = a * (r * d * r⁻¹) * a⁻¹ := by rw [ha.1, inv_inv]
      _ = (a * d * a⁻¹)⁻¹ := by rw [hr_d]; group
      _ = d := by rw [ha.1, inv_inv]
  have haN : a ∈ Subgroup.normalizer (D : Set X) :=
    mem_normalizer_of_conj_mem hgen (by rw [ha.2]; exact h.c_mem)
      (by rw [ha.1]; exact inv_mem h.d_mem)
  have hrc_mem : r * c * r⁻¹ ∈ D := by
    rw [hr_c]
    exact mul_mem (inv_mem h.c_mem) (inv_mem h.d_mem)
  have hrd_mem : r * d * r⁻¹ ∈ D := by
    rw [hr_d]
    exact inv_mem h.d_mem
  have hrN : r ∈ Subgroup.normalizer (D : Set X) :=
    mem_normalizer_of_conj_mem hgen hrc_mem hrd_mem
  set sA : MulAut D := D.normalizerMonoidHom ⟨a, haN⟩ with hsA
  set sR : MulAut D := D.normalizerMonoidHom ⟨r, hrN⟩ with hsR
  have hsAm : sA ∈ autIn (⊤ : Subgroup X) D := mem_autIn_iff.mpr ⟨a, haN, Subgroup.mem_top a, rfl⟩
  have hsRm : sR ∈ autIn (⊤ : Subgroup X) D := mem_autIn_iff.mpr ⟨r, hrN, Subgroup.mem_top r, rfl⟩
  set G := autIn (⊤ : Subgroup X) D
  set S' : G := ⟨sA, hsAm⟩
  set R' : G := ⟨sR, hsRm⟩
  set c' : D := ⟨c, h.c_mem⟩
  set d' : D := ⟨d, h.d_mem⟩
  have hvA : ∀ x : D, ((sA x : D) : X) = a * x * a⁻¹ := fun x =>
    normalizerMonoidHom_apply_coe haN x
  have hvR : ∀ (k : ℕ) (x : D), ((sR ^ k) x : X) = r ^ k * x * (r ^ k)⁻¹ := fun k x =>
    normalizerMonoidHom_pow_apply hrN k x
  have hsA2 : sA * sA = 1 := by
    refine mulAut_ext_of_config h (Subtype.ext ?_) (Subtype.ext ?_)
    · change ((sA (sA c') : D) : X) = c
      rw [hvA, hvA]
      change a * (a * c * a⁻¹) * a⁻¹ = c
      rw [ha.2, ha.2]
    · change ((sA (sA d') : D) : X) = d
      rw [hvA, hvA]
      change a * (a * d * a⁻¹) * a⁻¹ = d
      rw [ha.1, conj_inv_eq, ha.1, inv_inv]
  have hr6_c : r ^ 6 * c * (r ^ 6)⁻¹ = c :=
    calc r ^ 6 * c * (r ^ 6)⁻¹ = r ^ 3 * (r ^ 3 * c * (r ^ 3)⁻¹) * (r ^ 3)⁻¹ := by
          rw [show r ^ 6 = r ^ 3 * r ^ 3 by rw [← pow_add], mul_inv_rev]; simp only [mul_assoc]
      _ = r ^ 3 * c⁻¹ * (r ^ 3)⁻¹ := by rw [hr3_c]
      _ = (r ^ 3 * c * (r ^ 3)⁻¹)⁻¹ := by group
      _ = c := by rw [hr3_c, inv_inv]
  have hr6_d : r ^ 6 * d * (r ^ 6)⁻¹ = d :=
    calc r ^ 6 * d * (r ^ 6)⁻¹ = r ^ 3 * (r ^ 3 * d * (r ^ 3)⁻¹) * (r ^ 3)⁻¹ := by
          rw [show r ^ 6 = r ^ 3 * r ^ 3 by rw [← pow_add], mul_inv_rev]; simp only [mul_assoc]
      _ = r ^ 3 * d⁻¹ * (r ^ 3)⁻¹ := by rw [hr3_d]
      _ = (r ^ 3 * d * (r ^ 3)⁻¹)⁻¹ := by group
      _ = d := by rw [hr3_d, inv_inv]
  have hsR6 : sR ^ 6 = 1 := by
    refine mulAut_ext_of_config h (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [hvR]
      exact hr6_c
    · rw [hvR]
      exact hr6_d
  have hsR2 : sR ^ 2 ≠ 1 := by
    intro h1
    have h2 := congrArg (fun φ : MulAut D => ((φ c' : D) : X)) h1
    rw [hvR, hr2_c] at h2
    change d * c * d = c at h2
    apply hd1
    have h3 : d * d = 1 :=
      calc d * d = c⁻¹ * (c * d * d) := by group
        _ = c⁻¹ * (d * c * d) := by rw [hcd]
        _ = 1 := by rw [h2, inv_mul_cancel]
    calc d = d ^ 3 * (d * d)⁻¹ := by group
      _ = 1 := by rw [hd3, h3, inv_one, one_mul]
  have hsR3 : sR ^ 3 ≠ 1 := by
    intro h1
    have h2 := congrArg (fun φ : MulAut D => ((φ c' : D) : X)) h1
    rw [hvR, hr3_c] at h2
    change c⁻¹ = c at h2
    apply h.c_ne_one
    have h3 : c * c = 1 := by
      calc c * c = c⁻¹ * c := by rw [h2]
        _ = 1 := inv_mul_cancel c
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [hc3, h3, inv_one, one_mul]
  have hw : sA * sR * sA * sR = 1 := by
    have e : sA * sR * sA * sR = D.normalizerMonoidHom
        (⟨a, haN⟩ * ⟨r, hrN⟩ * ⟨a, haN⟩ * ⟨r, hrN⟩) := by
      simp only [map_mul, hsA, hsR]
    rw [e]
    refine mulAut_ext_of_config h (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [normalizerMonoidHom_apply_coe]
      exact hw_c
    · rw [normalizerMonoidHom_apply_coe]
      exact hw_d
  set G := autIn (⊤ : Subgroup X) D
  set S' : G := ⟨sA, hsAm⟩
  set R' : G := ⟨sR, hsRm⟩
  have hS2 : S' * S' = 1 := Subtype.ext hsA2
  have hR6 : R' ^ 6 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hsR6)
  have hSR : S' * R' * S' = R'⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul]
    exact eq_inv_of_mul_eq_one_left hw
  have hord : orderOf R' = 6 := by
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) hR6 fun p hp hpd => ?_
    have hp6 : p = 2 ∨ p = 3 := by
      have hle := Nat.le_of_dvd (by norm_num) hpd
      interval_cases p
      · exact absurd hp Nat.not_prime_zero
      · exact absurd hp Nat.not_prime_one
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hpd (by decide)
      · exact absurd hpd (by decide)
      · norm_num at hp
    rcases hp6 with rfl | rfl
    · intro h1
      apply hsR3
      have := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow] at this
    · intro h1
      apply hsR2
      have := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow] at this
  have hinj := dihedralSixHom_injective hS2 hR6 hSR hord
  have : Fintype G := Fintype.ofFinite G
  have hcardle := card_autIn_le_twelve h
  have hbij : Function.Bijective (dihedralSixHom hS2 hR6 hSR) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, le_antisymm (Fintype.card_le_of_injective _ hinj) ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, DihedralGroup.nat_card]
    exact hcardle
  exact ⟨(MulEquiv.ofBijective _ hbij).symm⟩

end Automizer

end CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof
