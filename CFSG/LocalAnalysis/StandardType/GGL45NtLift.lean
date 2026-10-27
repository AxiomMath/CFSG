module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggL45Nt_centerQuotAut_mk_congr {K : Type*} [Group K] (a : MulAut K) {x y : K}
    (h : (x : K ⧸ Subgroup.center K) = (y : K ⧸ Subgroup.center K)) :
    (a x : K ⧸ Subgroup.center K) = (a y : K ⧸ Subgroup.center K) := by
  rw [← centerQuotAut_mk (H := K) a x, ← centerQuotAut_mk (H := K) a y, h]

private theorem ggL45Nt_inducedAut_conj {K : Type*} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (k : K) :
    ggInducedAut θ (MulAut.conj k) = MulAut.conj (θ (k : K ⧸ Subgroup.center K)) := by
  ext r
  obtain ⟨z, rfl⟩ := θ.surjective r
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  simp [ggInducedAut_apply, MulAut.conj_apply]

theorem ggL45Nt_eq_one_of_forall_commute {K R : Type*} [Group K] [Group R] (hK : commutator K = ⊤)
    (θ : K ⧸ Subgroup.center K ≃* R) {r : R} (hr : ∀ s : R, s * r = r * s) : r = 1 := by
  haveI : Group.IsPerfect K := ⟨hK⟩
  have hbot : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot K
  have hmem : θ.symm r ∈ Subgroup.center (K ⧸ Subgroup.center K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg θ.symm (hr (θ x))
    simpa using h
  have h1 : θ.symm r = 1 := by
    rw [hbot] at hmem
    simpa using hmem
  simpa using congrArg θ h1

theorem ggL45Nt_isPGroup_closure_insert {p : ℕ} {K : Type*} [Group K] {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) {ψ : MulAut K} (hψ : ψ ^ p = 1) (hEψ : ∀ e ∈ E, e * ψ = ψ * e) :
    IsPGroup p (Subgroup.closure (insert ψ (E : Set (MulAut K)))) := by
  set A := Subgroup.closure (insert ψ (E : Set (MulAut K))) with hAdef
  have hEpair : (E : Set (MulAut K)).Pairwise Commute := by
    intro a ha b hb _
    exact Subtype.ext_iff.mp ((isMulCommutative_iff.mp hE.1) ⟨a, ha⟩ ⟨b, hb⟩)
  have hpair : (insert ψ (E : Set (MulAut K))).Pairwise Commute := by
    rw [Set.pairwise_insert_of_symm]
    exact ⟨hEpair, fun b hb _ => (hEψ b hb).symm⟩
  have hAcomm : IsMulCommutative A := by
    rw [hAdef]
    exact Subgroup.isMulCommutative_closure hpair
  let T : Subgroup (MulAut K) :=
    { carrier := {x | x ∈ A ∧ x ^ p = 1}
      one_mem' := ⟨A.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxA, hxp⟩ ⟨hyA, hyp⟩
        refine ⟨A.mul_mem hxA hyA, ?_⟩
        have hxy : Commute x y := by
          have h := (isMulCommutative_iff.mp hAcomm) ⟨x, hxA⟩ ⟨y, hyA⟩
          exact Subtype.ext_iff.mp h
        rw [hxy.mul_pow, hxp, hyp, mul_one]
      inv_mem' := by
        rintro x ⟨hxA, hxp⟩
        exact ⟨A.inv_mem hxA, by rw [inv_pow, hxp, inv_one]⟩ }
  have hAT : A ≤ T := by
    rw [hAdef, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hxE
    · exact ⟨Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl)), hψ⟩
    · exact ⟨Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr hxE)), hE.2 x hxE⟩
  intro x
  exact ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using (hAT x.2).2)⟩

theorem ggL45Nt_exists_fixed_pElt_lift {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) (A : Subgroup (MulAut K)) (hA : IsPGroup p A)
    {k₀ : K} (hk₀ : ∃ m : ℕ, k₀ ^ p ^ m ∈ Subgroup.center K)
    (hfix : ∀ a ∈ A, ((a k₀ : K) : K ⧸ Subgroup.center K) = (k₀ : K ⧸ Subgroup.center K)) :
    ∃ k : K, (k : K ⧸ Subgroup.center K) = (k₀ : K ⧸ Subgroup.center K) ∧ GGL45IsPElt p k ∧
      ∀ a ∈ A, a k = k := by
  classical
  let Z := Subgroup.center K
  haveI : Fact p.Prime := ⟨hp⟩
  let C := {k : K // (k : K ⧸ Z) = (k₀ : K ⧸ Z)}
  have hCinv : ∀ (a : A) (c : C), ((a : MulAut K) c.1 : K ⧸ Z) = (k₀ : K ⧸ Z) := by
    intro a c
    rw [ggL45Nt_centerQuotAut_mk_congr (a : MulAut K) c.2, hfix (a : MulAut K) a.2]
  letI : MulAction A C :=
    { smul := fun a c => ⟨(a : MulAut K) c.1, hCinv a c⟩
      one_smul := fun c => Subtype.ext rfl
      mul_smul := fun a b c => Subtype.ext rfl }
  have hcardC : Nat.card C = Nat.card Z := by
    have hf : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
    calc Nat.card C = Nat.card ((QuotientGroup.mk' Z) ⁻¹' {(k₀ : K ⧸ Z)}) := rfl
      _ = Nat.card (QuotientGroup.mk' Z).ker :=
          Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hf _)
      _ = Nat.card Z := by rw [QuotientGroup.ker_mk']
  have hnotdvd : ¬ p ∣ Nat.card C := by rw [hcardC]; exact hZ
  obtain ⟨c₁, hc₁⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hA C hnotdvd
  have hc₁fix : ∀ a : A, (a : MulAut K) c₁.1 = c₁.1 := by
    intro a
    exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hc₁ a)
  let k₁ := c₁.1
  have hk₁Z : (k₁ : K ⧸ Z) = (k₀ : K ⧸ Z) := c₁.2
  have hk₁fix : ∀ a ∈ A, a k₁ = k₁ := fun a ha => hc₁fix ⟨a, ha⟩
  obtain ⟨m, hk₀m⟩ := hk₀
  have hbar : (k₁ : K ⧸ Z) ^ p ^ m = 1 := by
    rw [hk₁Z, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk₀m
  have hN : orderOf k₁ ≠ 0 := (orderOf_pos k₁).ne'
  obtain ⟨e, n', hn'p, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hp.ne_one
  have hcop : p.Coprime n' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hn'p
  have hc : (p ^ m).Coprime n' := (hcop.symm.pow_right m).symm
  obtain ⟨t, ht⟩ := Nat.chineseRemainder hc 1 0
  have ht1 : t ≡ 1 [MOD p ^ m] := ht.1
  have ht0 : t ≡ 0 [MOD n'] := ht.2
  refine ⟨k₁ ^ t, ?_, ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, pow_eq_pow_of_modEq ht1 hbar, pow_one]
    exact hk₁Z
  · obtain ⟨q, hq⟩ := Nat.modEq_zero_iff_dvd.mp ht0
    refine ⟨e, ?_⟩
    have hNpow : k₁ ^ (p ^ e * n') = 1 := by rw [← hN, pow_orderOf_eq_one]
    calc (k₁ ^ t) ^ p ^ e = k₁ ^ (t * p ^ e) := by rw [pow_mul]
      _ = k₁ ^ (n' * q * p ^ e) := by rw [hq]
      _ = k₁ ^ (q * (p ^ e * n')) := by congr 1; ring
      _ = (k₁ ^ (p ^ e * n')) ^ q := by rw [← pow_mul]; congr 1; ring
      _ = 1 := by rw [hNpow, one_pow]
  · intro a ha
    rw [map_pow, hk₁fix a ha]

theorem ggL45Nt_satR_of_satK {p : ℕ} (hp : p.Prime) {K : Type} [Group K] [Finite K] {R : Type}
    [Group R] (θ : K ⧸ Subgroup.center K ≃* R) (hZ : ¬ p ∣ Nat.card (Subgroup.center K))
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) {ψ : MulAut K} (hψ : ψ ^ p = 1)
    (hEψ : ∀ e ∈ E, e * ψ = ψ * e)
    (hsat : ∀ k : K, k ^ p = 1 → (∀ e ∈ E, e k = k) → ψ k = k → MulAut.conj k ∈ E) :
    ∀ r : R, r ^ p = 1 → (∀ e ∈ E.map (ggInducedAut θ), e r = r) →
      ggInducedAut θ ψ r = r → MulAut.conj r ∈ E.map (ggInducedAut θ) := by
  classical
  intro r hrp hrE hrψ
  let Z := Subgroup.center K
  obtain ⟨z, hz⟩ := θ.surjective r
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective z
  have hk₀θ : r = θ (k₀ : K ⧸ Z) := hz.symm
  have hk0p : k₀ ^ p ∈ Z := by
    rw [← QuotientGroup.eq_one_iff]
    apply θ.injective
    rw [map_one, QuotientGroup.mk_pow, map_pow, hz, hrp]
  let A := Subgroup.closure (insert ψ (E : Set (MulAut K)))
  have hAp : IsPGroup p A := ggL45Nt_isPGroup_closure_insert hE hψ hEψ
  let S : Subgroup (MulAut K) :=
    { carrier := {a | ((a k₀ : K) : K ⧸ Z) = (k₀ : K ⧸ Z)}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [MulAut.mul_apply]
        rw [ggL45Nt_centerQuotAut_mk_congr a hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        simpa using (ggL45Nt_centerQuotAut_mk_congr a⁻¹ ha).symm }
  have hSA : A ≤ S := by
    change Subgroup.closure (insert ψ (E : Set (MulAut K))) ≤ S
    rw [Subgroup.closure_le]
    intro b hb
    simp only [Set.mem_insert_iff] at hb
    rcases hb with hb_eq | hbE
    · rw [hb_eq]
      show ((ψ k₀ : K) : K ⧸ Z) = (k₀ : K ⧸ Z)
      have h := hrψ
      rw [hk₀θ] at h
      rw [ggInducedAut_apply] at h
      exact θ.injective h
    · show ((b k₀ : K) : K ⧸ Z) = (k₀ : K ⧸ Z)
      have hmem : ggInducedAut θ b ∈ E.map (ggInducedAut θ) :=
        Subgroup.mem_map.mpr ⟨b, hbE, rfl⟩
      have h := hrE (ggInducedAut θ b) hmem
      rw [hk₀θ] at h
      rw [ggInducedAut_apply] at h
      exact θ.injective h
  have hfixA : ∀ a ∈ A, ((a k₀ : K) : K ⧸ Z) = (k₀ : K ⧸ Z) := fun a ha => hSA ha
  obtain ⟨k, hkZ, hkP, hkfix⟩ :=
    ggL45Nt_exists_fixed_pElt_lift hp hZ A hAp ⟨1, by simpa using hk0p⟩ hfixA
  have hkE : ∀ e ∈ E, e k = k := by
    intro e he
    exact hkfix e (Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr he)))
  have hkψ : ψ k = k :=
    hkfix ψ (Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl)))
  have hkpZ : k ^ p ∈ Z := by
    rw [← QuotientGroup.eq_one_iff]
    rw [QuotientGroup.mk_pow, hkZ, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk0p
  have hordZ : orderOf (k ^ p) ∣ Nat.card Z := by
    have h := orderOf_dvd_natCard (⟨k ^ p, hkpZ⟩ : Z)
    rw [← Subgroup.orderOf_coe] at h
    simpa using h
  have hpdvd : ¬ p ∣ orderOf (k ^ p) := fun hd => hZ (dvd_trans hd hordZ)
  have hkp : k ^ p = 1 := by
    obtain ⟨n, hn⟩ := hkP
    rcases n with _ | n'
    · simp at hn
      rw [hn]; simp
    · have hpow : orderOf (k ^ p) ∣ p ^ n' := by
        rw [orderOf_dvd_iff_pow_eq_one]
        rw [← pow_mul, Nat.mul_comm p (p ^ n'), ← pow_succ]
        exact hn
      have hcopn : (orderOf (k ^ p)).Coprime (p ^ n') :=
        (Nat.Coprime.pow_right n' ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpdvd).symm)
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcopn hpow)
  have hconj : MulAut.conj k ∈ E := hsat k hkp hkE hkψ
  have hrk : r = θ (k : K ⧸ Z) := by rw [hkZ]; exact hk₀θ
  rw [hrk, ← ggL45Nt_inducedAut_conj θ k]
  exact Subgroup.mem_map.mpr ⟨MulAut.conj k, hconj, rfl⟩

end CFSG.StandardType
