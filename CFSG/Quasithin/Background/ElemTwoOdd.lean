module

public import CFSG.RankThree.GroupTheory.SteinbergBMQD32SmallOddRepresentation

public section

namespace CFSG.Quasithin.ElemTwoOdd

open CFSG.Open
open scoped Pointwise IsMulCommutative

section Eigen

variable {Q : Type} [CommGroup Q] {p : ℕ}

theorem exists_eigen {ι : Type} (hp2 : Odd p) (W : Subgroup Q) (hW : ∀ w ∈ W, w ^ p = 1)
    (s : Finset ι) (f : ι → Q →* Q) (hsW : ∀ i ∈ s, ∀ w ∈ W, f i w ∈ W)
    (hsc : ∀ i ∈ s, ∀ j ∈ s, ∀ x, f i (f j x) = f j (f i x))
    (hs2 : ∀ i ∈ s, ∀ x, f i (f i x) = x) {q₀ : Q} (hq₀ : q₀ ∈ W) (hq₀1 : q₀ ≠ 1) :
    ∃ q ∈ W, q ≠ 1 ∧ ∀ i ∈ s, f i q = q ∨ f i q = q⁻¹ := by
  classical
  have hsq : ∀ q ∈ W, q ≠ 1 → q * q ≠ 1 := by
    intro q hq hq1 h0
    apply hq1
    obtain ⟨m, hm⟩ := hp2
    have h1 : q ^ p = 1 := hW q hq
    rw [hm, pow_succ, pow_mul, pow_two, h0, one_pow, one_mul] at h1
    exact h1
  induction s using Finset.induction_on with
  | empty => exact ⟨q₀, hq₀, hq₀1, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert i s his ih =>
    obtain ⟨q, hqW, hq1, hqS⟩ := ih (fun j hj => hsW j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hsc j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      (fun j hj => hs2 j (Finset.mem_insert_of_mem hj))
    have hii : ∀ x : Q, f i (f i x) = x := hs2 i (Finset.mem_insert_self i s)
    have hiW : f i q ∈ W := hsW i (Finset.mem_insert_self i s) q hqW
    have hcomm : ∀ j ∈ s, ∀ x : Q, f j (f i x) = f i (f j x) := fun j hj x =>
      hsc j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i s) x
    have key : ∀ r : Q, r ∈ W → r ≠ 1 → (f i r = r ∨ f i r = r⁻¹) →
        (∀ j ∈ s, f j r = r ∨ f j r = r⁻¹) → ∃ q ∈ W, q ≠ 1 ∧ ∀ j ∈ insert i s,
          f j q = q ∨ f j q = q⁻¹ := by
      intro r hr hr1 hir hjr
      refine ⟨r, hr, hr1, fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact hir
      · exact hjr j hjs
    by_cases hplus : q * f i q = 1
    · have hminus : q * (f i q)⁻¹ ≠ 1 := by
        intro h0
        apply hsq q hqW hq1
        calc q * q = (q * f i q) * (q * (f i q)⁻¹) := by
              rw [mul_mul_mul_comm, mul_inv_cancel, mul_one]
          _ = 1 := by rw [hplus, h0, one_mul]
      refine key _ (W.mul_mem hqW (W.inv_mem hiW)) hminus (Or.inr ?_) ?_
      · rw [map_mul, map_inv, hii, mul_inv, inv_inv, mul_comm]
      · intro j hj
        rcases hqS j hj with h | h
        · left
          rw [map_mul, map_inv, hcomm j hj, h]
        · right
          rw [map_mul, map_inv, hcomm j hj, h, map_inv, mul_inv, inv_inv]
    · refine key _ (W.mul_mem hqW hiW) hplus (Or.inl ?_) ?_
      · rw [map_mul, hii, mul_comm]
      · intro j hj
        rcases hqS j hj with h | h
        · left
          rw [map_mul, hcomm j hj, h]
        · right
          rw [map_mul, hcomm j hj, h, map_inv, mul_inv]

end Eigen

section Linear

variable {V : Type} [CommGroup V] [Finite V] {p : ℕ}

@[expose] def linHom [Module (ZMod p) (Additive V)] :
    MulAut V →* (Additive V ≃ₗ[ZMod p] Additive V) where
  toFun g := (MulEquiv.toAdditive g).toLinearEquiv (ZMod.map_smul (MulEquiv.toAdditive g))
  map_one' := by ext v; rfl
  map_mul' g h := by ext v; rfl

omit [Finite V] in
theorem linHom_injective [Module (ZMod p) (Additive V)] :
    Function.Injective (linHom (V := V) (p := p)) := by
  intro g h hgh
  ext v
  exact Additive.ofMul.injective (LinearEquiv.congr_fun hgh (Additive.ofMul v))

theorem card_le_of_faithful_elem (hp : p.Prime) (hp2 : p ≠ 2)
    [hM : Module (ZMod p) (Additive V)]
    {Γ : Type} [Group Γ] [Finite Γ] (σ : Γ →* MulAut V) (hσ : Function.Injective σ)
    (hc : ∀ a b : Γ, a * b = b * a) (h2 : ∀ a : Γ, a * a = 1) :
    ∃ d : ℕ, Nat.card V = p ^ d ∧ Nat.card Γ ≤ 2 ^ d := by
  have : Fact p.Prime := ⟨hp⟩
  have : Module.Finite (ZMod p) (Additive V) := Module.Finite.of_finite
  let ρ : Γ →* LinearMap.GeneralLinearGroup (ZMod p) (Additive V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive V)).symm.toMonoidHom.comp
      (linHom.comp σ)
  have hρinj : Function.Injective ρ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive V)).symm.injective.comp
      (linHom_injective.comp hσ)
  have h2p : (2 : ZMod p) ≠ 0 := by
    intro h0
    have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hfinr : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  have hbound := CFSG.RankThree.GroupTheory.SteinbergBM.card_le_two_pow_finrank_of_sq_eq_one
    h2p (Module.finrank (ZMod p) (Additive V)) rfl ρ.range hfinr
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, hc a b])
    (by
      rintro _ ⟨a, rfl⟩
      rw [← map_mul, h2 a, map_one])
  have hcardΓ : Nat.card ρ.range = Nat.card Γ :=
    Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv.symm
  refine ⟨Module.finrank (ZMod p) (Additive V), ?_, hcardΓ ▸ hbound⟩
  have h3 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V)
  rw [Nat.card_zmod] at h3
  exact h3

end Linear

section Main

variable {X : Type} [Group X] [Finite X] {p : ℕ}

omit [Finite X] in
theorem eq_one_of_mul_self (hp2 : Odd p) {P : Subgroup X} (hP : IsPGroup p P) {w : X}
    (hw : w ∈ P) (h : w * w = 1) : w = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨w, hw⟩
  have hk' : w ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : w ^ 2 = 1 := by rw [pow_two]; exact h
  have hcop : Nat.Coprime 2 (p ^ k) := Nat.Coprime.pow_right _ (Nat.coprime_two_left.mpr hp2)
  have h3 := pow_gcd_eq_one.mpr ⟨h2, hk'⟩
  rwa [hcop.gcd_eq_one, pow_one] at h3

theorem mem_normalizer_of_conj_le {H : Subgroup X} {m : X} (h : ∀ a ∈ H, m * a * m⁻¹ ∈ H) :
    m ∈ Subgroup.normalizer (H : Set X) := by
  have hle : H.map (MulAut.conj m).toMonoidHom ≤ H := by
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have heq : H.map (MulAut.conj m).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj m).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨h a, fun ha => ?_⟩
  rw [← heq] at ha
  obtain ⟨b, hb, hba⟩ := ha
  have : b = a := by
    have h1 : m * b * m⁻¹ = m * a * m⁻¹ := hba
    simpa using h1
  rwa [← this]

omit [Finite X] in
theorem centralizes_of_selfCentralizing (hp2 : Odd p) {P A : Subgroup X} (hP : IsPGroup p P)
    (hPA : P ≤ Subgroup.normalizer (A : Set X))
    (hC : P ⊓ Subgroup.centralizer (A : Set X) ≤ A) {f : X} (hf2 : f * f = 1)
    (hfP : f ∈ Subgroup.normalizer (P : Set X)) (hfA : ∀ a ∈ A, f * a * f⁻¹ = a) :
    ∀ z ∈ P, f * z * f⁻¹ = z := by
  intro z hz
  set w := z⁻¹ * (f * z * f⁻¹) with hw
  have hfz : f * z * f⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hfP z).mp hz
  have hwP : w ∈ P := P.mul_mem (P.inv_mem hz) hfz
  have hwC : w ∈ Subgroup.centralizer (A : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hza : z * a * z⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hPA hz) a).mp ha
    have hfb : f * (z * a * z⁻¹) = (z * a * z⁻¹) * f := by
      calc f * (z * a * z⁻¹) = (f * (z * a * z⁻¹) * f⁻¹) * f := by group
        _ = (z * a * z⁻¹) * f := by rw [hfA _ hza]
    have hfa : a * f⁻¹ = f⁻¹ * a := by
      calc a * f⁻¹ = f⁻¹ * (f * a * f⁻¹) := by group
        _ = f⁻¹ * a := by rw [hfA a ha]
    calc a * w = z⁻¹ * ((z * a * z⁻¹) * f) * z * f⁻¹ := by rw [hw]; group
      _ = z⁻¹ * (f * (z * a * z⁻¹)) * z * f⁻¹ := by rw [hfb]
      _ = z⁻¹ * f * z * (a * f⁻¹) := by group
      _ = z⁻¹ * f * z * (f⁻¹ * a) := by rw [hfa]
      _ = w * a := by rw [hw]; group
  have hwA : w ∈ A := hC ⟨hwP, hwC⟩
  have hfw : f * w * f⁻¹ = w := hfA w hwA
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
  have hww : w * w = 1 := by
    have e1 : f * z * f⁻¹ = z * w := by rw [hw]; group
    have e2 : z = f * (f * z * f⁻¹) * f⁻¹ := by
      calc z = (f * f) * z * (f * f)⁻¹ := by rw [hf2]; group
        _ = f * (f * z * f⁻¹) * f⁻¹ := by group
    have e3 : z = z * (w * w) := by
      calc z = f * (f * z * f⁻¹) * f⁻¹ := e2
        _ = f * (z * w) * f⁻¹ := by rw [e1]
        _ = (f * z * f⁻¹) * (f * w * f⁻¹) := by group
        _ = z * (w * w) := by rw [e1, hfw, mul_assoc]
    calc w * w = z⁻¹ * (z * (w * w)) := by group
      _ = 1 := by rw [← e3, inv_mul_cancel]
  have hw1 := eq_one_of_mul_self hp2 hP hwP hww
  calc f * z * f⁻¹ = z * w := by rw [hw]; group
    _ = z := by rw [hw1, mul_one]

@[expose] def Adm (P E : Subgroup X) (B : Subgroup X) : Prop :=
  B ≤ P ∧ P ≤ Subgroup.normalizer (B : Set X) ∧ E ≤ Subgroup.normalizer (B : Set X) ∧
    ∀ a ∈ B, ∀ b ∈ B, a * b = b * a

theorem centralizer_le_of_maximal (hp : p.Prime) (hp2 : Odd p) {P E : Subgroup X}
    (hP : IsPGroup p P) (hEP : E ≤ Subgroup.normalizer (P : Set X))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ e ∈ E, e * e = 1) {A : Subgroup X}
    (hA : Maximal (Adm P E) A) : P ⊓ Subgroup.centralizer (A : Set X) ≤ A := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hAP, hPA, hEA, hAc⟩, hmax⟩ := hA
  by_contra hnot
  obtain ⟨c, ⟨hcP, hcC⟩, hcA⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  let Y : Subgroup X :=
    { carrier := {y | (y ∈ P ∧ y ∈ Subgroup.centralizer (A : Set X)) ∧
        ∀ g ∈ P, y * g * y⁻¹ * g⁻¹ ∈ A}
      one_mem' := ⟨⟨P.one_mem, Subgroup.one_mem _⟩, fun g _ => by simp [A.one_mem]⟩
      mul_mem' := fun {a b} ha hb => by
        refine ⟨⟨P.mul_mem ha.1.1 hb.1.1, Subgroup.mul_mem _ ha.1.2 hb.1.2⟩, fun g hg => ?_⟩
        have h1 := hb.2 g hg
        have h2 := ha.2 g hg
        have h3 : a * (b * g * b⁻¹ * g⁻¹) * a⁻¹ = b * g * b⁻¹ * g⁻¹ := by
          have hc : a * (b * g * b⁻¹ * g⁻¹) = (b * g * b⁻¹ * g⁻¹) * a :=
            ((Subgroup.mem_centralizer_iff.mp ha.1.2) _ h1).symm
          rw [hc]
          group
        have e1 : a * b * g * (a * b)⁻¹ * g⁻¹ =
            (a * (b * g * b⁻¹ * g⁻¹) * a⁻¹) * (a * g * a⁻¹ * g⁻¹) := by group
        rw [e1, h3]
        exact A.mul_mem h1 h2
      inv_mem' := fun {a} ha => by
        refine ⟨⟨P.inv_mem ha.1.1, Subgroup.inv_mem _ ha.1.2⟩, fun g hg => ?_⟩
        have h1 := ha.2 g hg
        have h2 : a⁻¹ * (a * g * a⁻¹ * g⁻¹)⁻¹ * a = (a * g * a⁻¹ * g⁻¹)⁻¹ := by
          have hc : (a * g * a⁻¹ * g⁻¹)⁻¹ * a = a * (a * g * a⁻¹ * g⁻¹)⁻¹ :=
            (Subgroup.mem_centralizer_iff.mp ha.1.2) _ (A.inv_mem h1)
          rw [mul_assoc, hc]
          group
        have e1 : a⁻¹ * g * a⁻¹⁻¹ * g⁻¹ = a⁻¹ * (a * g * a⁻¹ * g⁻¹)⁻¹ * a := by group
        rw [e1, h2]
        exact A.inv_mem h1 }
  have hYP : Y ≤ P := fun y hy => hy.1.1
  have hAY : A ≤ Y := by
    intro a ha
    refine ⟨⟨hAP ha, Subgroup.mem_centralizer_iff.mpr fun b hb => hAc b hb a ha⟩,
      fun g hg => ?_⟩
    have h1 : g * a⁻¹ * g⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hPA hg) a⁻¹).mp (A.inv_mem ha)
    have e1 : a * g * a⁻¹ * g⁻¹ = a * (g * a⁻¹ * g⁻¹) := by group
    rw [e1]
    exact A.mul_mem ha h1
  have hNC : ∀ {V : Subgroup X} {g : X}, g ∈ Subgroup.normalizer (V : Set X) →
      g ∈ Subgroup.normalizer ((Subgroup.centralizer (V : Set X) : Subgroup X) : Set X) := by
    intro V g hg
    refine mem_normalizer_of_conj_le fun c hc => ?_
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) v).mp hv
      simpa using this
    have h1 := hc _ hv'
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * v := by group
  have hNY : ∀ g, g ∈ Subgroup.normalizer (P : Set X) → g ∈ Subgroup.normalizer (A : Set X) →
      g ∈ Subgroup.normalizer (Y : Set X) := by
    intro g hgP hgA
    refine mem_normalizer_of_conj_le fun y hy => ⟨⟨(Subgroup.mem_normalizer_iff.mp hgP y).mp
      hy.1.1, (Subgroup.mem_normalizer_iff.mp (hNC hgA) y).mp hy.1.2⟩, fun h hh => ?_⟩
    have hh' : g⁻¹ * h * g ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgP) h).mp hh
      simpa using this
    have h1 := hy.2 _ hh'
    have h2 := (Subgroup.mem_normalizer_iff.mp hgA _).mp h1
    convert h2 using 1
    group
  obtain ⟨c₀, hc₀Y, hc₀A⟩ : ∃ c₀ ∈ Y, c₀ ∉ A := by
    have : (A.subgroupOf P).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mpr hPA
    have hQp : IsPGroup p (↥P ⧸ A.subgroupOf P) := hP.to_quotient _
    have : Group.IsNilpotent (↥P ⧸ A.subgroupOf P) := hQp.isNilpotent
    set C := P ⊓ Subgroup.centralizer (A : Set X) with hCdef
    have hPC : P ≤ Subgroup.normalizer (C : Set X) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hNC (hPA hg)⟩
    have : (C.subgroupOf P).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hPC
    have : ((C.subgroupOf P).map (QuotientGroup.mk' (A.subgroupOf P))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    have hN1 : (C.subgroupOf P).map (QuotientGroup.mk' (A.subgroupOf P)) ≠ ⊥ := by
      intro h0
      apply hcA
      have h1 : QuotientGroup.mk' (A.subgroupOf P) ⟨c, hcP⟩ ∈
          (C.subgroupOf P).map (QuotientGroup.mk' (A.subgroupOf P)) :=
        ⟨⟨c, hcP⟩, Subgroup.mem_subgroupOf.mpr ⟨hcP, hcC⟩, rfl⟩
      rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    obtain ⟨⟨z, hzN, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hN1)
    obtain ⟨⟨c₀, hc₀P⟩, hc₀C, rfl⟩ := hzN
    replace hc₀C := Subgroup.mem_subgroupOf.mp hc₀C
    refine ⟨c₀, ⟨hc₀C, fun g hg => ?_⟩, fun h0 => hz1 ?_⟩
    · have h1 := (Subgroup.mem_center_iff.mp hzZ) (QuotientGroup.mk' (A.subgroupOf P) ⟨g, hg⟩)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at h1
      have h2 := Subgroup.mem_subgroupOf.mp h1
      have h3 := (Subgroup.mem_normalizer_iff.mp (hPA (P.mul_mem hg hc₀P)) _).mp h2
      convert h3 using 1
      simp only [Subgroup.coe_inv, MulMemClass.coe_mul]
      group
    · exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h0))
  have : (A.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAY).mpr (hYP.trans hPA)
  have hQcomm : ∀ a b : ↥Y ⧸ A.subgroupOf Y, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H y₁ =>
      induction b using QuotientGroup.induction_on with
      | H y₂ =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have h1 := y₂.2.2 y₁ (hYP y₁.2)
        have h2 := (Subgroup.mem_normalizer_iff.mp
          (hPA (P.inv_mem (P.mul_mem (hYP y₁.2) (hYP y₂.2)))) _).mp h1
        convert h2 using 1
        simp only [Subgroup.coe_inv, MulMemClass.coe_mul]
        group
  let _ : CommGroup (↥Y ⧸ A.subgroupOf Y) :=
    { (inferInstance : Group (↥Y ⧸ A.subgroupOf Y)) with mul_comm := hQcomm }
  have hEY : ∀ e ∈ E, ∀ y ∈ Y, e * y * e⁻¹ ∈ Y := fun e he y hy =>
    (Subgroup.mem_normalizer_iff.mp (hNY e (hEP he) (hEA he)) y).mp hy
  let cY : ↥E → (↥Y →* ↥Y) := fun e =>
    { toFun := fun y => ⟨e * y * e⁻¹, hEY e e.2 y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show (e : X) * (a * b) * (e : X)⁻¹ = (e * a * (e : X)⁻¹) * (e * b * (e : X)⁻¹)
        group) }
  have hcYA : ∀ e : ↥E, A.subgroupOf Y ≤ (A.subgroupOf Y).comap (cY e) := by
    intro e y hy
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hy
    exact (Subgroup.mem_normalizer_iff.mp (hEA e.2) _).mp hy
  let f : ↥E → (↥Y ⧸ A.subgroupOf Y →* ↥Y ⧸ A.subgroupOf Y) := fun e =>
    QuotientGroup.map _ _ (cY e) (hcYA e)
  have hfmk : ∀ (e : ↥E) (y : ↥Y), f e (y : ↥Y ⧸ A.subgroupOf Y) =
      ((⟨e * y * e⁻¹, hEY e e.2 y y.2⟩ : ↥Y) : ↥Y ⧸ A.subgroupOf Y) := fun _ _ => rfl
  have hfc : ∀ e₁ e₂ : ↥E, ∀ q, f e₁ (f e₂ q) = f e₂ (f e₁ q) := by
    intro e₁ e₂ q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [hfmk, hfmk, hfmk, hfmk]
      congr 1
      apply Subtype.ext
      show (e₁ : X) * ((e₂ : X) * y * (e₂ : X)⁻¹) * (e₁ : X)⁻¹ =
        (e₂ : X) * ((e₁ : X) * y * (e₁ : X)⁻¹) * (e₂ : X)⁻¹
      have h12 := hEc e₁ e₁.2 e₂ e₂.2
      calc (e₁ : X) * ((e₂ : X) * y * (e₂ : X)⁻¹) * (e₁ : X)⁻¹ =
            ((e₁ : X) * e₂) * y * ((e₁ : X) * e₂)⁻¹ := by group
        _ = ((e₂ : X) * e₁) * y * ((e₂ : X) * e₁)⁻¹ := by rw [h12]
        _ = _ := by group
  have hf2 : ∀ e : ↥E, ∀ q, f e (f e q) = q := by
    intro e q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [hfmk, hfmk]
      congr 1
      apply Subtype.ext
      show (e : X) * ((e : X) * y * (e : X)⁻¹) * (e : X)⁻¹ = y
      have h1 := hE2 e e.2
      calc (e : X) * ((e : X) * y * (e : X)⁻¹) * (e : X)⁻¹ =
            ((e : X) * e) * y * ((e : X) * e)⁻¹ := by group
        _ = y := by rw [h1]; group
  let W : Subgroup (↥Y ⧸ A.subgroupOf Y) :=
    { carrier := {q | q ^ p = 1}
      one_mem' := one_pow p
      mul_mem' := fun {a b} ha hb => by
        show (a * b) ^ p = 1
        rw [mul_pow, ha, hb, one_mul]
      inv_mem' := fun {a} ha => by
        show a⁻¹ ^ p = 1
        rw [inv_pow, ha, inv_one] }
  have hQp : IsPGroup p (↥Y ⧸ A.subgroupOf Y) := (hP.to_le hYP).to_quotient _
  have hQnt : Nontrivial (↥Y ⧸ A.subgroupOf Y) := by
    refine ⟨⟨((⟨c₀, hc₀Y⟩ : ↥Y) : ↥Y ⧸ A.subgroupOf Y), 1, fun h0 => hc₀A ?_⟩⟩
    rw [QuotientGroup.eq_one_iff] at h0
    exact Subgroup.mem_subgroupOf.mp h0
  obtain ⟨n, hn, hcard⟩ := hQp.nontrivial_iff_card.mp hQnt
  obtain ⟨q₀, hq₀⟩ := exists_prime_orderOf_dvd_card' p
    (hcard ▸ dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn))
  have hq₀W : q₀ ∈ W := by
    show q₀ ^ p = 1
    rw [← hq₀]
    exact pow_orderOf_eq_one q₀
  have hq₀1 : q₀ ≠ 1 := by
    intro h0
    rw [h0, orderOf_one] at hq₀
    exact hp.one_lt.ne hq₀
  have : Fintype ↥E := Fintype.ofFinite _
  obtain ⟨q, hqW, hq1, hqe⟩ := exists_eigen hp2 W (fun w hw => hw) Finset.univ f
    (fun e _ w hw => by
      show (f e w) ^ p = 1
      rw [← map_pow]
      have : w ^ p = 1 := hw
      rw [this, map_one])
    (fun e₁ _ e₂ _ q => hfc e₁ e₂ q) (fun e _ q => hf2 e q) hq₀W hq₀1
  obtain ⟨⟨x, hxY⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hxA : x ∉ A := by
    intro h0
    apply hq1
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h0)
  have hxP : x ∈ P := hYP hxY
  have hxC : ∀ a ∈ A, x * a = a * x := fun a ha =>
    ((Subgroup.mem_centralizer_iff.mp hxY.1.2) a ha).symm
  have hex : ∀ e ∈ E, x⁻¹ * (e * x * e⁻¹) ∈ A ∨ x * (e * x * e⁻¹) ∈ A := by
    intro e he
    rcases hqe ⟨e, he⟩ (Finset.mem_univ _) with h | h
    · left
      rw [hfmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      have h2 := A.inv_mem h
      convert h2 using 1
      simp only [Subgroup.coe_inv, MulMemClass.coe_mul]
      group
    · right
      rw [hfmk, ← QuotientGroup.mk_inv, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      have h2 := A.inv_mem h
      convert h2 using 1
      simp only [Subgroup.coe_inv, MulMemClass.coe_mul]
      group
  set B := A ⊔ Subgroup.zpowers x with hB
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (A : Set X) :=
    (Subgroup.zpowers_le).mpr (hPA hxP)
  have hBset : (B : Set X) = (A : Set X) * (Subgroup.zpowers x : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A (Subgroup.zpowers x) hxN
  have hmemB : ∀ b ∈ B, ∃ a ∈ A, ∃ k : ℤ, b = a * x ^ k := by
    intro b hb
    have hb' : b ∈ (B : Set X) := hb
    rw [hBset] at hb'
    obtain ⟨a, ha, y, hy, rfl⟩ := hb'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨a, ha, k, rfl⟩
  have hxB : x ∈ B := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hconjB : ∀ g, (∀ a ∈ A, g * a * g⁻¹ ∈ A) → g * x * g⁻¹ ∈ B → ∀ b ∈ B, g * b * g⁻¹ ∈ B := by
    intro g hgA hgx b hb
    have hb' : g * b * g⁻¹ ∈ B.map (MulAut.conj g).toMonoidHom := ⟨b, hb, by simp⟩
    rw [hB, Subgroup.map_sup, MonoidHom.map_zpowers] at hb'
    have hle : A.map (MulAut.conj g).toMonoidHom ⊔
        Subgroup.zpowers ((MulAut.conj g).toMonoidHom x) ≤ B := by
      refine sup_le ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact Subgroup.mem_sup_left (by simpa using hgA a ha)
      · rw [Subgroup.zpowers_le]
        simpa using hgx
    exact hle hb'
  have hBadm : Adm P E B := by
    refine ⟨sup_le hAP ((Subgroup.zpowers_le).mpr hxP), fun g hg => ?_, fun e he => ?_, ?_⟩
    · refine mem_normalizer_of_conj_le (hconjB g
        (fun a ha => (Subgroup.mem_normalizer_iff.mp (hPA hg) a).mp ha) ?_)
      have h1 := hxY.2 g hg
      have e1 : g * x * g⁻¹ = (x * g * x⁻¹ * g⁻¹)⁻¹ * x := by group
      rw [e1]
      exact B.mul_mem (Subgroup.mem_sup_left (A.inv_mem h1)) hxB
    · refine mem_normalizer_of_conj_le (hconjB e
        (fun a ha => (Subgroup.mem_normalizer_iff.mp (hEA he) a).mp ha) ?_)
      rcases hex e he with h | h
      · have e1 : e * x * e⁻¹ = x * (x⁻¹ * (e * x * e⁻¹)) := by group
        rw [e1]
        exact B.mul_mem hxB (Subgroup.mem_sup_left h)
      · have e1 : e * x * e⁻¹ = x⁻¹ * (x * (e * x * e⁻¹)) := by group
        rw [e1]
        exact B.mul_mem (B.inv_mem hxB) (Subgroup.mem_sup_left h)
    · intro b₁ hb₁ b₂ hb₂
      obtain ⟨a₁, ha₁, k₁, rfl⟩ := hmemB b₁ hb₁
      obtain ⟨a₂, ha₂, k₂, rfl⟩ := hmemB b₂ hb₂
      have hc₁ : Commute (x ^ k₁) a₂ := Commute.zpow_left (hxC a₂ ha₂) k₁
      have hc₂ : Commute (x ^ k₂) a₁ := Commute.zpow_left (hxC a₁ ha₁) k₂
      calc a₁ * x ^ k₁ * (a₂ * x ^ k₂) = a₁ * (x ^ k₁ * a₂) * x ^ k₂ := by group
        _ = a₁ * (a₂ * x ^ k₁) * x ^ k₂ := by rw [hc₁.eq]
        _ = (a₁ * a₂) * (x ^ k₁ * x ^ k₂) := by group
        _ = (a₂ * a₁) * (x ^ k₂ * x ^ k₁) := by
          rw [hAc a₁ ha₁ a₂ ha₂, ← zpow_add, ← zpow_add, add_comm]
        _ = a₂ * (x ^ k₂ * a₁) * x ^ k₁ := by rw [hc₂.eq]; group
        _ = a₂ * x ^ k₂ * (a₁ * x ^ k₁) := by group
  exact hxA (hmax hBadm le_sup_left hxB)

theorem centralizes_of_omega (hp : p.Prime) (hp2 : Odd p) {A : Subgroup X} (hA : IsPGroup p A)
    {f : X} (hf2 : f * f = 1)
    (hfA : f ∈ Subgroup.normalizer (A : Set X))
    (hf1 : ∀ a ∈ A, a ^ p = 1 → f * a * f⁻¹ = a) : ∀ a ∈ A, f * a * f⁻¹ = a := by
  have : Fact p.Prime := ⟨hp⟩
  intro a ha
  have hfa : f * a * f⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hfA a).mp ha
  set b := a⁻¹ * (f * a * f⁻¹) with hb
  have hbA : b ∈ A := A.mul_mem (A.inv_mem ha) hfa
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
  have hfb : f * b * f⁻¹ = b⁻¹ := by
    have hff : f⁻¹ * f⁻¹ = 1 := by rw [← mul_inv_rev, hf2, inv_one]
    calc f * b * f⁻¹ = f * a⁻¹ * f * a * (f⁻¹ * f⁻¹) := by rw [hb]; group
      _ = f * a⁻¹ * f * a := by rw [hff, mul_one]
      _ = (f * a * f⁻¹)⁻¹ * (f * f) * a := by group
      _ = (f * a * f⁻¹)⁻¹ * a := by rw [hf2, mul_one]
      _ = b⁻¹ := by rw [hb]; group
  by_contra hne
  have hb1 : b ≠ 1 := by
    intro h0
    apply hne
    calc f * a * f⁻¹ = a * b := by rw [hb]; group
      _ = a := by rw [h0, mul_one]
  have hbp : IsPGroup p (Subgroup.zpowers b) := hA.to_le ((Subgroup.zpowers_le).mpr hbA)
  have hnt : Nontrivial (Subgroup.zpowers b) :=
    ⟨⟨⟨b, Subgroup.mem_zpowers b⟩, 1, fun h0 => hb1 (congrArg Subtype.val h0)⟩⟩
  obtain ⟨n, hn, hcard⟩ := hbp.nontrivial_iff_card.mp hnt
  obtain ⟨⟨c, hc⟩, hcord⟩ := exists_prime_orderOf_dvd_card' p
    (hcard ▸ dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn))
  rw [Subgroup.orderOf_mk] at hcord
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hcA : b ^ k ∈ A := A.zpow_mem hbA k
  have hcp : (b ^ k) ^ p = 1 := by rw [← hcord]; exact pow_orderOf_eq_one _
  have h1 := hf1 _ hcA hcp
  have h2 : f * b ^ k * f⁻¹ = (b ^ k)⁻¹ := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hfb, inv_zpow]
  rw [h1] at h2
  have h3 : b ^ k * b ^ k = 1 := by
    calc b ^ k * b ^ k = b ^ k * (b ^ k)⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel _
  have h4 := eq_one_of_mul_self hp2 hA hcA h3
  rw [h4, orderOf_one] at hcord
  exact hp.one_lt.ne hcord

theorem exists_elemAbelian_of_faithful (hp : p.Prime) (hp2 : p ≠ 2) {P E : Subgroup X}
    (hP : IsPGroup p P) (hEP : E ≤ Subgroup.normalizer (P : Set X))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ e ∈ E, e * e = 1)
    (hfaith : ∀ e ∈ E, (∀ z ∈ P, e * z * e⁻¹ = z) → e = 1) :
    ∃ (B : Subgroup X) (d : ℕ), B ≤ P ∧ IsElemAbelian p B ∧ Nat.card B = p ^ d ∧
      Nat.card E ≤ 2 ^ d := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hbot : Adm P E ⊥ :=
    ⟨bot_le, fun g _ => mem_normalizer_of_conj_le fun a ha => by
      rw [Subgroup.mem_bot] at ha ⊢; rw [ha]; group,
      fun g _ => mem_normalizer_of_conj_le fun a ha => by
      rw [Subgroup.mem_bot] at ha ⊢; rw [ha]; group,
      fun a ha b hb => by rw [Subgroup.mem_bot] at ha hb; rw [ha, hb]⟩
  obtain ⟨A, -, hAmax⟩ := Finite.exists_le_maximal (p := Adm P E) hbot
  have hC := centralizer_le_of_maximal hp hodd hP hEP hEc hE2 hAmax
  obtain ⟨hAP, hPA, hEA, hAc⟩ := hAmax.1
  have hAp : IsPGroup p A := hP.to_le hAP
  let A₁ : Subgroup X :=
    { carrier := {a | a ∈ A ∧ a ^ p = 1}
      one_mem' := ⟨A.one_mem, one_pow p⟩
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (hAc a ha.1 b hb.1)), ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hA₁A : A₁ ≤ A := fun a ha => ha.1
  have hfaith₁ : ∀ e ∈ E, (∀ a ∈ A₁, e * a * e⁻¹ = a) → e = 1 := by
    intro e he h1
    apply hfaith e he
    refine centralizes_of_selfCentralizing hodd hP hPA hC (hE2 e he) (hEP he) ?_
    exact centralizes_of_omega hp hodd hAp (hE2 e he) (hEA he) fun a ha hap => h1 a ⟨ha, hap⟩
  have hEA₁ : ∀ e ∈ E, ∀ a ∈ A₁, e * a * e⁻¹ ∈ A₁ := fun e he a ha =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hEA he) a).mp ha.1, by
      rw [← MulAut.conj_apply, ← map_pow, ha.2, map_one]⟩
  have : IsMulCommutative ↥A₁ := ⟨⟨fun a b => Subtype.ext (hAc a a.2.1 b b.2.1)⟩⟩
  let σ : ↥E →* MulAut ↥A₁ :=
    { toFun := fun e =>
        { toFun := fun a => ⟨e * a * e⁻¹, hEA₁ e e.2 a a.2⟩
          invFun := fun a => ⟨e⁻¹ * a * e⁻¹⁻¹, hEA₁ e⁻¹ (E.inv_mem e.2) a a.2⟩
          left_inv := fun a => Subtype.ext (by simp [mul_assoc])
          right_inv := fun a => Subtype.ext (by simp [mul_assoc])
          map_mul' := fun a b => Subtype.ext (by
            show (e : X) * (a * b) * (e : X)⁻¹ = (e * a * (e : X)⁻¹) * (e * b * (e : X)⁻¹)
            group) }
      map_one' := MulEquiv.ext fun a => Subtype.ext (by
        show ((1 : ↥E) : X) * a * ((1 : ↥E) : X)⁻¹ = a
        simp)
      map_mul' := fun e₁ e₂ => MulEquiv.ext fun a => Subtype.ext (by
        show ((e₁ * e₂ : ↥E) : X) * a * ((e₁ * e₂ : ↥E) : X)⁻¹ =
          (e₁ : X) * ((e₂ : X) * a * (e₂ : X)⁻¹) * (e₁ : X)⁻¹
        push_cast
        group) }
  have hσinj : Function.Injective σ := by
    rw [injective_iff_map_eq_one]
    intro e he
    apply Subtype.ext
    apply hfaith₁ e e.2
    intro a ha
    have h1 := congrArg (fun g : MulAut ↥A₁ => ((g ⟨a, ha⟩ : ↥A₁) : X)) he
    exact h1
  have hnsmul : ∀ x : Additive ↥A₁, p • x = 0 := fun x =>
    Additive.toMul.injective (Subtype.ext (by
      show ((Additive.toMul x : ↥A₁) : X) ^ p = 1
      exact (Additive.toMul x).2.2))
  obtain ⟨d, hd, hdE⟩ := card_le_of_faithful_elem (hM := AddCommGroup.zmodModule hnsmul) hp hp2 σ
    hσinj (fun a b => Subtype.ext (hEc (a : X) a.2 (b : X) b.2))
    (fun a => Subtype.ext (hE2 (a : X) a.2))
  exact ⟨A₁, d, hA₁A.trans hAP, ⟨⟨⟨fun a b => Subtype.ext (hAc a a.2.1 b b.2.1)⟩⟩,
    fun a ha => ha.2⟩, hd, hdE⟩

end Main

end CFSG.Quasithin.ElemTwoOdd
