module

public import CFSG.CGT.T75N.PpdCyclic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13

namespace Lem22

section Fpf

variable {W : Type*} [Group W] [Finite W]

theorem card_modEq_one_of_fpf {z : MulAut W} (hz3 : z ^ 3 = 1) (hz : ∀ w : W, z w = w → w = 1)
    {K : Subgroup W} (hzK : ∀ k ∈ K, z k ∈ K) : Nat.card K ≡ 1 [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzK' : ∀ n : ℕ, ∀ k ∈ K, (z ^ n) k ∈ K := by
    intro n
    induction n with
    | zero => intro k hk; simpa using hk
    | succ n ih =>
      intro k hk
      rw [pow_succ', MulAut.mul_apply]
      exact hzK _ (ih k hk)
  have hzinv : ∀ k ∈ K, z⁻¹ k ∈ K := by
    intro k hk
    have e : z⁻¹ = z ^ 2 := by
      calc z⁻¹ = z ^ 3 * z⁻¹ := by rw [hz3, one_mul]
        _ = z ^ 2 := by rw [pow_succ, mul_inv_cancel_right]
    rw [e]
    exact hzK' 2 k hk
  have hzZ : ∀ n : ℤ, ∀ k ∈ K, (z ^ n) k ∈ K := by
    intro n
    induction n using Int.induction_on with
    | zero => intro k hk; simpa using hk
    | succ n ih =>
      intro k hk
      rw [zpow_add_one, MulAut.mul_apply]
      exact ih _ (hzK k hk)
    | pred n ih =>
      intro k hk
      rw [zpow_sub_one, MulAut.mul_apply]
      exact ih _ (hzinv k hk)
  let A : SubMulAction (Subgroup.zpowers z) W :=
    { carrier := K
      smul_mem' := by
        rintro ⟨g, hg⟩ k hk
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        exact hzZ n k hk }
  have hG : IsPGroup 3 ↥(Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := if orderOf z = 1 then 0 else 1) ?_
    rw [Nat.card_zpowers]
    have h1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2 <;> simp [h2]
  have h1 := hG.card_modEq_card_fixedPoints (α := A)
  have hcardA : Nat.card A = Nat.card K := rfl
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers z) A) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨⟨1, K.one_mem⟩, fun g => ?_⟩, ?_⟩
    · apply Subtype.ext
      obtain ⟨g, hg⟩ := g
      show g (1 : W) = 1
      exact map_one g
    · rintro ⟨⟨k, hk⟩, hkfix⟩
      have h2 := hkfix ⟨z, Subgroup.mem_zpowers z⟩
      have h3 : z k = k := congrArg Subtype.val h2
      have h4 := hz k h3
      apply Subtype.ext
      apply Subtype.ext
      exact h4
  rw [hcardA, hfix] at h1
  exact h1

theorem card_eq_of_fpf (hW16 : Nat.card W = 16) {z : MulAut W} (hz3 : z ^ 3 = 1)
    (hz : ∀ w : W, z w = w → w = 1) {K : Subgroup W} (hzK : ∀ k ∈ K, z k ∈ K) :
    Nat.card K = 1 ∨ Nat.card K = 4 ∨ Nat.card K = 16 := by
  have h1 := card_modEq_one_of_fpf hz3 hz hzK
  have h2 : Nat.card K ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hW16]
    exact Subgroup.card_subgroup_dvd_card K
  obtain ⟨k, hk, hKk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  rw [hKk] at h1 ⊢
  interval_cases k <;> simp_all [Nat.ModEq]


@[expose] def fixSub (g : MulAut W) : Subgroup W where
  carrier := {w | g w = w}
  one_mem' := map_one g
  mul_mem' := fun {a b} ha hb => by
    show g (a * b) = a * b
    rw [map_mul, show g a = a from ha, show g b = b from hb]
  inv_mem' := fun {a} ha => by
    show g a⁻¹ = a⁻¹
    rw [map_inv, show g a = a from ha]

@[expose] def fixedSub (R : Subgroup (MulAut W)) : Subgroup W where
  carrier := {w | ∀ r ∈ R, r w = w}
  one_mem' := fun r _ => map_one r
  mul_mem' := fun {a b} ha hb r hr => by rw [map_mul, ha r hr, hb r hr]
  inv_mem' := fun {a} ha r hr => by rw [map_inv, ha r hr]

omit [Finite W] in
theorem mem_fixedSub {R : Subgroup (MulAut W)} {w : W} : w ∈ fixedSub R ↔ ∀ r ∈ R, r w = w :=
  Iff.rfl

theorem fixedSub_ne_bot {R : Subgroup (MulAut W)} (hR2 : IsPGroup 2 ↥R)
    (hW : 2 ∣ Nat.card W) : fixedSub R ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb, hb1⟩ := hR2.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := W) hW
    (a := (1 : W)) (fun r => map_one (r : MulAut W))
  intro h0
  apply hb1
  have hbC : b ∈ fixedSub R := fun r hr => hb ⟨r, hr⟩
  rw [h0, Subgroup.mem_bot] at hbC
  exact hbC.symm

omit [Finite W] in
theorem fixedSub_inv {R : Subgroup (MulAut W)} {z : MulAut W}
    (hzR : ∀ r ∈ R, z⁻¹ * r * z ∈ R) : ∀ w ∈ fixedSub R, z w ∈ fixedSub R := by
  intro w hw r hr
  have h1 := mem_fixedSub.mp hw _ (hzR r hr)
  have h2 : (z⁻¹ * r * z) w = z⁻¹ (r (z w)) := rfl
  rw [h2] at h1
  have h3 := congrArg z h1
  simpa using h3

theorem trivial_mod_fixedSub (hWc : ∀ a b : W, a * b = b * a) (hW16 : Nat.card W = 16)
    {z : MulAut W} (hz3 : z ^ 3 = 1) (hz : ∀ w : W, z w = w → w = 1)
    {R : Subgroup (MulAut W)} (hR2 : IsPGroup 2 ↥R) (hzR : ∀ r ∈ R, z⁻¹ * r * z ∈ R)
    (hC4 : Nat.card (fixedSub R) = 4) : ∀ r ∈ R, ∀ w : W, r w * w⁻¹ ∈ fixedSub R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := fixedSub R with hCdef
  have hzC := fixedSub_inv hzR
  have hCn : C.Normal := ⟨fun a ha g => by rw [hWc g a, mul_inv_cancel_right]; exact ha⟩
  have hmapC : ∀ r ∈ R, C ≤ C.comap (r : MulAut W).toMonoidHom := fun r hr w hw => by
    show r w ∈ C
    rw [mem_fixedSub.mp hw r hr]
    exact hw
  let act : ↥R → W ⧸ C → W ⧸ C := fun r =>
    QuotientGroup.map C C (r : MulAut W).toMonoidHom (hmapC r r.2)
  have hact : ∀ (r : ↥R) (w : W), act r (w : W ⧸ C) = ((r : MulAut W) w : W ⧸ C) :=
    fun r w => rfl
  let _ : MulAction ↥R (W ⧸ C) :=
    { smul := act
      one_smul := fun q => by
        induction q using QuotientGroup.induction_on with
        | H w => exact hact 1 w
      mul_smul := fun r r' q => by
        induction q using QuotientGroup.induction_on with
        | H w => exact hact (r * r') w }
  have hcardQ : Nat.card (W ⧸ C) = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup C
    rw [hW16, hC4] at h1
    omega
  obtain ⟨c, hc, hc1⟩ := hR2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := W ⧸ C) (by rw [hcardQ]; norm_num) (a := (1 : W ⧸ C))
    (fun r => by
      show act r ((1 : W) : W ⧸ C) = 1
      rw [hact, map_one]
      rfl)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
  have huC : u ∉ C := fun h0 => hc1 (by
    rw [eq_comm, QuotientGroup.eq_one_iff]
    exact h0)
  let F : Subgroup W :=
    { carrier := {w | ∀ r ∈ R, (r : MulAut W) w * w⁻¹ ∈ C}
      one_mem' := fun r _ => by rw [map_one, one_mul, inv_one]; exact C.one_mem
      mul_mem' := fun {a b} ha hb r hr => by
        have e : r (a * b) * (a * b)⁻¹ = (r a * a⁻¹) * (r b * b⁻¹) := by
          rw [map_mul, mul_inv_rev]
          calc r a * r b * (b⁻¹ * a⁻¹) = r a * (r b * b⁻¹) * a⁻¹ := by group
            _ = r a * (a⁻¹ * (r b * b⁻¹)) := by rw [mul_assoc, hWc (r b * b⁻¹) a⁻¹]
            _ = (r a * a⁻¹) * (r b * b⁻¹) := by group
        rw [e]
        exact C.mul_mem (ha r hr) (hb r hr)
      inv_mem' := fun {a} ha r hr => by
        have e : r a⁻¹ * a⁻¹⁻¹ = (r a * a⁻¹)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv_rev, inv_inv, hWc]
        rw [e]
        exact C.inv_mem (ha r hr) }
  have hFmem : ∀ w, w ∈ F ↔ ∀ r ∈ R, (r : MulAut W) w * w⁻¹ ∈ C := fun w => Iff.rfl
  have hzF : ∀ w ∈ F, z w ∈ F := by
    intro w hw r hr
    have h1 := (hFmem w).mp hw _ (hzR r hr)
    have h2 : (z⁻¹ * r * z) w = z⁻¹ (r (z w)) := rfl
    rw [h2] at h1
    have h3 := hzC _ h1
    have e : z (z⁻¹ (r (z w)) * w⁻¹) = r (z w) * (z w)⁻¹ := by
      rw [map_mul, map_inv, MulAut.apply_inv_self]
    rw [← e]
    exact h3
  have hCF : C ≤ F := fun w hw r hr => by
    rw [mem_fixedSub.mp hw r hr, mul_inv_cancel]
    exact C.one_mem
  have huF : u ∈ F := by
    intro r hr
    have h2 : act ⟨r, hr⟩ (u : W ⧸ C) = (u : W ⧸ C) := hc ⟨r, hr⟩
    rw [hact, QuotientGroup.eq] at h2
    have h3 := C.inv_mem h2
    rw [mul_inv_rev, inv_inv, hWc] at h3
    exact h3
  have hFtop : F = ⊤ := by
    rcases card_eq_of_fpf hW16 hz3 hz hzF with hF | hF | hF
    · exfalso
      have h1 := Subgroup.card_le_of_le hCF
      rw [hF, hC4] at h1
      omega
    · exfalso
      have hCeq : C = F := Subgroup.eq_of_le_of_card_ge hCF (by rw [hC4, hF])
      exact huC (hCeq ▸ huF)
    · exact Subgroup.eq_top_of_card_eq F (by rw [hF, hW16])
  intro r hr w
  exact (hFmem w).mp (hFtop ▸ Subgroup.mem_top w) r hr

omit [Finite W] in
theorem eq_one_of_fix_closure {g : MulAut W} {S : Set W} (hS : Subgroup.closure S = ⊤)
    (hgS : ∀ s ∈ S, g s = s) : g = 1 := by
  have hle : Subgroup.closure S ≤ fixSub g := by
    rw [Subgroup.closure_le]
    exact hgS
  rw [hS] at hle
  ext w
  exact (hle (Subgroup.mem_top w) : g w = w)

theorem card_le_of_two {R : Subgroup (MulAut W)} {C : Subgroup W}
    (hRC : ∀ r ∈ R, ∀ w ∈ C, r w = w) (hRW : ∀ r ∈ R, ∀ w : W, r w * w⁻¹ ∈ C) {u₁ u₂ : W}
    (hgen : Subgroup.closure ((C : Set W) ∪ {u₁, u₂}) = ⊤) :
    Nat.card R ≤ Nat.card C * Nat.card C := by
  have hinj : Function.Injective (fun r : ↥R =>
      ((⟨(r : MulAut W) u₁ * u₁⁻¹, hRW r r.2 u₁⟩ : ↥C),
        (⟨(r : MulAut W) u₂ * u₂⁻¹, hRW r r.2 u₂⟩ : ↥C))) := by
    intro r r' h0
    have h1 : (r : MulAut W) u₁ = (r' : MulAut W) u₁ := by
      have := congrArg (fun x => (x.1 : W)) h0
      simpa using this
    have h2 : (r : MulAut W) u₂ = (r' : MulAut W) u₂ := by
      have := congrArg (fun x => (x.2 : W)) h0
      simpa using this
    have hg := eq_one_of_fix_closure (g := (r : MulAut W)⁻¹ * (r' : MulAut W)) hgen (by
      intro s hs
      show (r : MulAut W)⁻¹ ((r' : MulAut W) s) = s
      rcases hs with hs | hs
      · rw [hRC r' r'.2 s hs]
        calc (r : MulAut W)⁻¹ s = (r : MulAut W)⁻¹ ((r : MulAut W) s) := by
              rw [hRC r r.2 s hs]
          _ = s := by simp
      · rcases hs with rfl | hs
        · rw [← h1]; simp
        · rw [Set.mem_singleton_iff] at hs
          rw [hs, ← h2]
          simp)
    apply Subtype.ext
    rw [inv_mul_eq_one] at hg
    exact hg
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod] at this

theorem exists_gen_of_card_four (hW16 : Nat.card W = 16) {C : Subgroup W}
    (hC4 : Nat.card C = 4) : ∃ u₁ u₂ : W, Subgroup.closure ((C : Set W) ∪ {u₁, u₂}) = ⊤ := by
  have hCtop : C ≠ ⊤ := fun h0 => by
    rw [h0, Subgroup.card_top, hW16] at hC4
    norm_num at hC4
  obtain ⟨u₁, -, hu₁⟩ := IsConcreteLE.not_le_iff_exists.mp (fun h0 => hCtop (top_le_iff.mp h0))
  set K₁ := Subgroup.closure ((C : Set W) ∪ {u₁}) with hK₁
  have hCK₁ : C < K₁ := lt_of_le_of_ne (fun w hw => Subgroup.subset_closure (Or.inl hw))
    fun h0 => hu₁ (h0 ▸ Subgroup.subset_closure (Or.inr rfl))
  by_cases hK₁top : K₁ = ⊤
  · refine ⟨u₁, u₁, ?_⟩
    rw [Set.pair_eq_singleton]
    exact hK₁top
  · obtain ⟨u₂, -, hu₂⟩ := IsConcreteLE.not_le_iff_exists.mp
      (fun h0 => hK₁top (top_le_iff.mp h0))
    refine ⟨u₁, u₂, ?_⟩
    set K₂ := Subgroup.closure ((C : Set W) ∪ {u₁, u₂}) with hK₂
    have hK₁K₂ : K₁ < K₂ := lt_of_le_of_ne
      (Subgroup.closure_mono (Set.union_subset_union_right _ (by simp)))
      fun h0 => hu₂ (h0 ▸ Subgroup.subset_closure (Or.inr (by simp)))
    have h3 : Nat.card K₂ ∣ 16 := hW16 ▸ Subgroup.card_subgroup_dvd_card K₂
    have h4 : Nat.card K₁ ∣ Nat.card K₂ := Subgroup.card_dvd_of_le hK₁K₂.le
    have h5 : Nat.card C ∣ Nat.card K₁ := Subgroup.card_dvd_of_le hCK₁.le
    have h6 := Subgroup.card_lt_of_lt hCK₁
    have h7 := Subgroup.card_lt_of_lt hK₁K₂
    rw [hC4] at h5 h6
    obtain ⟨a, ha⟩ := h5
    obtain ⟨b, hb⟩ := h4
    have ha2 : 2 ≤ a := by
      by_contra h
      push Not at h
      interval_cases a <;> omega
    have hb2 : 2 ≤ b := by
      by_contra h
      push Not at h
      interval_cases b <;> omega
    have hK₂16 : 16 ≤ Nat.card K₂ := by
      rw [hb, ha]
      calc 16 = 4 * 2 * 2 := by norm_num
        _ ≤ 4 * a * b := Nat.mul_le_mul (Nat.mul_le_mul_left _ ha2) hb2
    exact Subgroup.eq_top_of_card_eq _ (le_antisymm (Nat.le_of_dvd (by norm_num) h3)
      (hW16 ▸ hK₂16) |>.trans hW16.symm)

theorem card_le_sixteen_of_fpf (hWc : ∀ a b : W, a * b = b * a) (hW16 : Nat.card W = 16)
    {z : MulAut W} (hz3 : z ^ 3 = 1) (hz : ∀ w : W, z w = w → w = 1)
    {R : Subgroup (MulAut W)} (hR2 : IsPGroup 2 ↥R) (hzR : ∀ r ∈ R, z⁻¹ * r * z ∈ R) :
    Nat.card R ≤ 16 := by
  have hC1 := fixedSub_ne_bot hR2 (by rw [hW16]; norm_num)
  rcases card_eq_of_fpf hW16 hz3 hz (fixedSub_inv hzR) with hC | hC | hC
  · exact absurd (Subgroup.card_eq_one.mp hC) hC1
  · obtain ⟨u₁, u₂, hgen⟩ := exists_gen_of_card_four hW16 hC
    have h1 := card_le_of_two (fun r hr w hw => mem_fixedSub.mp hw r hr)
      (trivial_mod_fixedSub hWc hW16 hz3 hz hR2 hzR hC) hgen
    rw [hC] at h1
    exact h1
  · have hCtop : fixedSub R = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hC, hW16])
    have hR1 : R = ⊥ := by
      rw [eq_bot_iff]
      intro r hr
      rw [Subgroup.mem_bot]
      ext w
      exact mem_fixedSub.mp (hCtop ▸ Subgroup.mem_top w) r hr
    rw [hR1, Subgroup.card_bot]
    norm_num

end Fpf

end Lem22

end CFSG.Quasithin.H13
