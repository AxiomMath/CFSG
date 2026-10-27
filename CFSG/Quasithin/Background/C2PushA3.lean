module

public import CFSG.Quasithin.Background.C2PushY

public section

namespace CFSG.Quasithin.C2Push

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

section Abstract

variable {X : Type*} [Group X] [Finite X]

theorem exists_threePrime_threePart (g : X) :
    ∃ a b : X, a * b = g ∧ Commute a b ∧ ¬ 3 ∣ orderOf a ∧
      ∀ x ∈ Subgroup.zpowers b, ∃ k : ℕ, x ^ 3 ^ k = 1 := by
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  have hcop : Nat.Coprime (3 ^ e) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm)
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hcop : IsCoprime ((3 ^ e : ℕ) : ℤ) (m : ℤ))
  have hgn : g ^ (3 ^ e * m) = 1 := by rw [← hn]; exact pow_orderOf_eq_one g
  refine ⟨g ^ (u * ((3 ^ e : ℕ) : ℤ)), g ^ (v * (m : ℤ)), ?_, ?_, ?_, ?_⟩
  · rw [← zpow_add]
    have : u * ((3 ^ e : ℕ) : ℤ) + v * (m : ℤ) = 1 := by linarith
    rw [this, zpow_one]
  · exact Commute.zpow_zpow_self g _ _
  · have h1 : (g ^ (u * ((3 ^ e : ℕ) : ℤ))) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : u * ((3 ^ e : ℕ) : ℤ) * (m : ℤ) = ((3 ^ e * m : ℕ) : ℤ) * u := by push_cast; ring
      rw [this, zpow_mul, zpow_natCast, hgn, one_zpow]
    intro h3
    exact hm (h3.trans (orderOf_dvd_of_pow_eq_one h1))
  · rintro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨e, ?_⟩
    rw [← zpow_natCast, ← zpow_mul, ← zpow_mul]
    have : v * (m : ℤ) * (k * ((3 ^ e : ℕ) : ℤ)) = ((3 ^ e * m : ℕ) : ℤ) * (v * k) := by
      push_cast; ring
    rw [this, zpow_mul, zpow_natCast, hgn, one_zpow]

theorem closure_not_dvd_three_eq_top {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q) :
    Subgroup.closure {x : Q | ¬ 3 ∣ orderOf x} = ⊤ := by
  set S : Set Q := {x : Q | ¬ 3 ∣ orderOf x} with hS
  have hNn : (Subgroup.closure S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    refine Subgroup.closure_induction (p := fun n _ => g * n * g⁻¹ ∈ Subgroup.closure S) ?_ ?_ ?_ ?_ hn
    · intro x hx
      apply Subgroup.subset_closure
      show ¬ 3 ∣ orderOf (g * x * g⁻¹)
      have := (MulAut.conj g).orderOf_eq x
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hx
    · simp
    · intro x y _ _ hx hy
      simpa [mul_assoc] using mul_mem hx hy
    · intro x _ hx
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hx
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hNn with h | h
  · exact h
  · exfalso
    have hcent : ∀ x : Q, ¬ 3 ∣ orderOf x → x ∈ Subgroup.center Q := fun x hx =>
      h (Subgroup.subset_closure hx)
    have h3 : IsPGroup 3 (Q ⧸ Subgroup.center Q) := by
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨a, b, hab, -, ha, hb⟩ := exists_threePrime_threePart g
      obtain ⟨k, hk⟩ := hb b (Subgroup.mem_zpowers b)
      refine ⟨k, ?_⟩
      have h1 : (QuotientGroup.mk a : Q ⧸ Subgroup.center Q) = 1 :=
        (QuotientGroup.eq_one_iff a).mpr (hcent a ha)
      have h2 : (QuotientGroup.mk g : Q ⧸ Subgroup.center Q) = QuotientGroup.mk b := by
        rw [← hab, QuotientGroup.mk_mul, h1, one_mul]
      rw [h2, ← QuotientGroup.mk_pow, hk]
      rfl
    obtain ⟨hp, hs, a, b, hab⟩ := hQ
    have : Nontrivial (Q ⧸ Subgroup.center Q) := hs.toNontrivial
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcn := h3.center_nontrivial
    have := hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ Subgroup.center Q)) with
      h0 | h0
    · exact (Subgroup.nontrivial_iff_ne_bot _).mp hcn h0
    · exact hab (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top a) b).symm

omit [Finite X] in
theorem mem_zpowers_mul_inv_of_commute {x f : X} (hc : Commute x f) (hx : ¬ 3 ∣ orderOf x)
    (hf : ∃ k : ℕ, f ^ 3 ^ k = 1) : x ∈ Subgroup.zpowers (x * f⁻¹) := by
  obtain ⟨k, hk⟩ := hf
  have hcop : Nat.Coprime (3 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hx)
  obtain ⟨s, t, hst⟩ := (Nat.isCoprime_iff_coprime.mpr hcop :
    IsCoprime ((3 ^ k : ℕ) : ℤ) (orderOf x : ℤ))
  have h1 : (x * f⁻¹) ^ (3 ^ k) = x ^ (3 ^ k) := by
    rw [(hc.symm.inv_left.symm).mul_pow, inv_pow, hk, inv_one, mul_one]
  have h2 : x = (x ^ (3 ^ k)) ^ s := by
    have h3 : x ^ (s * ((3 ^ k : ℕ) : ℤ) + t * (orderOf x : ℤ)) = x := by rw [hst, zpow_one]
    calc x = x ^ (s * ((3 ^ k : ℕ) : ℤ) + t * (orderOf x : ℤ)) := h3.symm
      _ = x ^ (s * ((3 ^ k : ℕ) : ℤ)) * x ^ (t * (orderOf x : ℤ)) := zpow_add _ _ _
      _ = (x ^ (3 ^ k)) ^ s := by
        rw [mul_comm s, zpow_mul, zpow_natCast, mul_comm t, zpow_mul, zpow_natCast,
          pow_orderOf_eq_one, one_zpow, mul_one]
  have h5 : ((x * f⁻¹) ^ 3 ^ k) ^ s ∈ Subgroup.zpowers (x * f⁻¹) :=
    Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _) _
  rwa [h1, ← h2] at h5

theorem le_of_forall_eq_mul_prod_of_isPGroup_three {K M₀ : Subgroup X} (hK : CFSG.IsComponent K)
    {r : ℕ} (B : Fin r → Subgroup X) (hB3 : ∀ i, IsPGroup 3 (B i))
    (hBsub : ∀ i, (B i).IsSubnormal)
    (hx : ∀ x ∈ K, ∃ m ∈ M₀, ∃ b : Fin r → X, (∀ i, b i ∈ B i) ∧ x = m * (List.ofFn b).prod) :
    K ≤ M₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBP : ∀ i, B i ≤ pCoreOf 3 (⊤ : Subgroup X) := by
    intro i
    have hsub : IsSubnormal (B i) ⊤ := A3.subnormal_top_iff.mpr (hBsub i)
    have h1 : B i ≤ pCoreOf 3 (B i) :=
      le_pCoreOf_of_le_normalizer 3 le_rfl Subgroup.le_normalizer (hB3 i)
    exact h1.trans (A4.pCoreOf_le_of_subnormal 3 hsub)
  have hcomm : ∀ i, ∀ x ∈ K, ∀ y ∈ B i, Commute x y := by
    intro i x hx y hy
    have : Group.IsSolvable ↥(B i) := by
      have : Group.IsNilpotent ↥(B i) := (hB3 i).isNilpotent
      infer_instance
    have hc := (CFSG.LocalCores.component_solvable_centralizer this (hBsub i)).1 K hK
    have := Subgroup.commutator_mem_commutator hx hy
    rw [hc, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hK3 := closure_not_dvd_three_eq_top hK.1
  have hle : Subgroup.closure {x : ↥K | ¬ 3 ∣ orderOf x} ≤ M₀.subgroupOf K := by
    rw [Subgroup.closure_le]
    intro x hx3
    have hx3' : ¬ 3 ∣ orderOf (x : X) := by
      rwa [Subgroup.orderOf_coe]
    obtain ⟨m, hm, b, hb, hxm⟩ := hx (x : X) x.2
    set f : X := (List.ofFn b).prod with hf
    have hfP : f ∈ pCoreOf 3 (⊤ : Subgroup X) :=
      Subgroup.list_prod_mem _ fun y hy => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
        exact hBP i (hb i)
    have hfk : ∃ k : ℕ, f ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 3 (⊤ : Subgroup X)) ⟨f, hfP⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have hfc : Commute (x : X) f :=
      Commute.list_prod_right _ _ fun y hy => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
        exact hcomm i (x : X) x.2 (b i) (hb i)
    have hm' : m = (x : X) * f⁻¹ := by rw [hxm]; group
    have := mem_zpowers_mul_inv_of_commute hfc hx3' hfk
    rw [← hm'] at this
    exact Subgroup.zpowers_le.mpr hm this
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥K) ∈ Subgroup.closure {x : ↥K | ¬ 3 ∣ orderOf x} := hK3 ▸ Subgroup.mem_top _
  exact hle hy'

end Abstract

variable {G : Type} [Group G] [Finite G]

theorem le_of_isBlock2_card_three {M R H L : Subgroup G} (hL : L ∈ cComp M)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hRM : R ≤ M)
    (hsyl : IsSylowTwoOf R (conjClosure L R ⊔ R)) (hRH : R ≤ H) {r : ℕ} (Lb : Fin r → Subgroup G)
    (hLb : ∀ i, IsBlock2 (conjClosure L R ⊔ R) (Lb i) ∧
      Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3)
    (hprod : ∀ h ∈ conjClosure L R ⊔ R, ∃ m ∈ (conjClosure L R ⊔ R) ⊓ H, ∃ x : Fin r → G,
      (∀ i, x i ∈ Lb i) ∧ h = m * (List.ofFn x).prod) : L ≤ H := by
  set Y : Subgroup G := conjClosure L R ⊔ R with hY
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hYM : Y ≤ M := conjClosure_sup_le hRM hLM
  have hRY : R ≤ Y := le_sup_right
  have hLY : L ≤ Y := (le_conjClosure L R).trans le_sup_left
  have hLY' : L ∈ cComp Y := cComp_mem_of_le hL hLY hYM
  have hKc : CFSG.IsComponent (imageOTwoQuot Y L) := isComponent_imageOTwoQuot hLY' hLq
  have hOR : pCoreOf 2 Y ≤ R := B6.pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hOY : pCoreOf 2 Y ≤ Y ⊓ H := le_inf (hOR.trans hRY) (hOR.trans hRH)
  have hB3 : ∀ i, IsPGroup 3 (imageOTwoQuot Y (Lb i)) := by
    intro i
    obtain ⟨e⟩ := nonempty_mulEquiv_pCore_quotient_imageOTwoQuot (IsBlock2.isSubnormal (hLb i).1)
    have hcard : Nat.card ↥(imageOTwoQuot Y (Lb i)) = 3 ^ 1 :=
      ((Nat.card_congr e.toEquiv).symm.trans (hLb i).2).trans (pow_one 3).symm
    exact IsPGroup.of_card hcard
  have hBsub : ∀ i, (imageOTwoQuot Y (Lb i)).IsSubnormal := fun i =>
    (hLb i).1.2.2.map (QuotientGroup.mk'_surjective _)
  have hx : ∀ x ∈ imageOTwoQuot Y L, ∃ m ∈ imageOTwoQuot Y (Y ⊓ H),
      ∃ b : Fin r → OTwoQuot Y, (∀ i, b i ∈ imageOTwoQuot Y (Lb i)) ∧
        x = m * (List.ofFn b).prod := by
    intro x hx
    obtain ⟨l, hl, hlL, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
    obtain ⟨m, hm, xs, hxs, hlm⟩ := hprod l (hLY hlL)
    have hxsY : ∀ i, xs i ∈ Y := fun i => (hLb i).1.2.1 (hxs i)
    refine ⟨QuotientGroup.mk ⟨m, hm.1⟩, mem_imageOTwoQuot_iff.mpr ⟨m, hm.1, hm, rfl⟩,
      fun i => QuotientGroup.mk ⟨xs i, hxsY i⟩,
      fun i => mem_imageOTwoQuot_iff.mpr ⟨xs i, hxsY i, hxs i, rfl⟩, ?_⟩
    have h1 : (⟨l, hl⟩ : ↥Y) =
        ⟨m, hm.1⟩ * (List.ofFn fun i => (⟨xs i, hxsY i⟩ : ↥Y)).prod := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, SubmonoidClass.coe_list_prod, List.map_ofFn]
      exact hlm
    rw [h1, QuotientGroup.mk_mul]
    congr 1
    have := map_list_prod (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))
      (List.ofFn fun i => (⟨xs i, hxsY i⟩ : ↥Y))
    rw [List.map_ofFn] at this
    exact this
  have hle := le_of_forall_eq_mul_prod_of_isPGroup_three hKc (fun i => imageOTwoQuot Y (Lb i))
    hB3 hBsub hx
  intro l hl
  have hlY : l ∈ Y := hLY hl
  exact (mem_of_mk_mem_imageOTwoQuot hOY
    (hle (mem_imageOTwoQuot_iff.mpr ⟨l, hlY, hl, rfl⟩) : (QuotientGroup.mk ⟨l, hlY⟩ : OTwoQuot Y) ∈
      imageOTwoQuot Y (Y ⊓ H))).2

end CFSG.Quasithin.C2Push
