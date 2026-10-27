module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofInner
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofRed
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofCube
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction

public section

namespace CFSG.RankThree.PartTwo.Sec14.ONLoc

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem le_of_forall_mem
    {A L : Subgroup Γ} {e : Γ} (hA : Late.IsE27 A) (heA : e ∈ A) (he1 : e ≠ 1)
    (hLe : L ≤ Subgroup.centralizer ({e} : Set Γ)) (hAL : A ≤ Subgroup.normalizer (L : Set Γ))
    (hLq : IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hON3 : Sec4.IsTripleCover (↥L ⧸ aschbacherSolvableCore 3 ↥L)
      CFSG.Blueprint.NativeSporadic.ON)
    (hmax : ∀ x : Γ, x ^ 3 = 1 → (∀ a ∈ A, a * x = x * a) → x ∈ A) : A ≤ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := ↥L ⧸ aschbacherSolvableCore 3 ↥L with hXdef
  have hZ3 : Nat.card (Subgroup.center X) = 3 := hON3.1
  obtain ⟨ψ⟩ := hON3.2
  obtain ⟨ψM⟩ := Sec13.ON134.nonempty_equiv_model hLq.1 hON3
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  set σ := thetaQuotientAction 3 hAL with hσdef
  have hσ3 : ∀ a : ↥A, σ a ^ 3 = 1 := fun a => by
    rw [← map_pow, show a ^ 3 = 1 from Subtype.ext (hA3 a a.2), map_one]
  have hinner : ∀ a : ↥A, ∃ x : X, σ a = MulAut.conj x := fun a =>
    Res9ON.exists_conj_of_pow_three_ON hLq hON3 (σ a) (hσ3 a)
  have hle : σ.range ≤ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := hinner a
    exact ⟨x, hx.symm⟩
  set P : Subgroup X := σ.range.comap (MulAut.conj : X →* MulAut X) with hPdef
  have hZP : Subgroup.center X ≤ P := fun z hz => by
    show MulAut.conj z ∈ σ.range
    rw [Res9ON.conj_eq_one_of_mem_center hz]
    exact σ.range.one_mem
  have hPcard : Nat.card P = 3 * Nat.card σ.range := by
    set ι := (MulAut.conj : X →* MulAut X).domRestrict P with hιdef
    have hιrange : ι.range = σ.range := by
      rw [hιdef, MonoidHom.domRestrict_range, hPdef, Subgroup.map_comap_eq_self hle]
    have hιker : Nat.card ι.ker = 3 := by
      have hk : ι.ker = (Subgroup.center X).subgroupOf P := by
        ext x
        rw [hιdef, MonoidHom.ker_domRestrict, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
          MonoidHom.mem_ker]
        exact ⟨Res9ON.mem_center_of_conj_eq_one, Res9ON.conj_eq_one_of_mem_center⟩
      rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ3]
    rw [Res9ON.card_eq_card_ker_mul_card_range ι, hιker, hιrange]
  have hσx : ∀ (x : ↥L) (hx : (x : Γ) ∈ A), σ ⟨(x : Γ), hx⟩ = MulAut.conj ((x : ↥L) : X) := by
    intro x hx
    ext q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [Res9ON.thetaQuotientAction_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
  set α : ↥A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL) with hαdef
  have hαθ : ∀ a : ↥A, ∀ n ∈ aschbacherSolvableCore 3 ↥L,
      α a n ∈ aschbacherSolvableCore 3 ↥L := by
    intro a n hn
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (aschbacherSolvableCore 3 ↥L).Characteristic) (α a)
    rw [← hmap]
    exact ⟨n, hn, rfl⟩
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hliftA := Semidihedral.Principal.coprime_fixed_point_lifting 3 hA.isPGroup α
    (aschbacherSolvableCore 3 ↥L) hαθ hθ3
  have hlift : ∀ r : X, r ^ 3 = 1 → r ≠ 1 → (∀ a : ↥A, σ a r = r) →
      ∃ x₀ : ↥L, (x₀ : Γ) ∈ A ∧ ∃ m : ℕ, ¬ 3 ∣ m ∧ ((x₀ : ↥L) : X) = r ^ m := by
    intro r hr3 hr1 hrfix
    have hrmem : r ∈ {q : X | ∀ a : ↥A,
        Semidihedral.Principal.CoprimeFixedPoint.quotientAction α
          (aschbacherSolvableCore 3 ↥L) hαθ a q = q} := by
      intro a
      have hq : ∀ q : X, Semidihedral.Principal.CoprimeFixedPoint.quotientAction α
          (aschbacherSolvableCore 3 ↥L) hαθ a q = σ a q := by
        intro q
        induction q using QuotientGroup.induction_on with
        | H y => rfl
      rw [hq]
      exact hrfix a
    rw [hliftA] at hrmem
    obtain ⟨c, hcfix, hcr⟩ := hrmem
    have hcA : ∀ a ∈ A, a * (c : Γ) = c * a := by
      intro a ha
      have h1 : a * (c : Γ) * a⁻¹ = c := congrArg Subtype.val (hcfix ⟨a, ha⟩)
      calc a * (c : Γ) = a * c * a⁻¹ * a := by group
        _ = c * a := by rw [h1]
    obtain ⟨k, m, hm3, hn⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' 3 (by norm_num)
    set x₀ : ↥L := c ^ m with hx₀def
    have hx₀k : x₀ ^ 3 ^ k = 1 := by
      rw [hx₀def, ← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
    have hmkx₀ : ((x₀ : ↥L) : X) = r ^ m := by
      rw [hx₀def, QuotientGroup.mk_pow, ← hcr]
      rfl
    have hro : orderOf r = 3 := orderOf_eq_prime hr3 hr1
    have hrm : r ^ m ≠ 1 := fun h => hm3 (hro ▸ orderOf_dvd_of_pow_eq_one h)
    have hx₀3 : x₀ ^ 3 = 1 := by
      have h1 : x₀ ^ 3 ∈ aschbacherSolvableCore 3 ↥L := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmkx₀, ← pow_mul, mul_comm,
          pow_mul, hr3, one_pow]
      have h2 : orderOf (x₀ ^ 3) ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
        Subgroup.orderOf_dvd_natCard _ h1
      have h3 : orderOf (x₀ ^ 3) ∣ 3 ^ k :=
        orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, hx₀k, one_pow])
      have h4 : Nat.Coprime (orderOf (x₀ ^ 3)) (Nat.card (aschbacherSolvableCore 3 ↥L)) :=
        Nat.Coprime.coprime_dvd_left h3
          (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3))
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h4 h2)
    have hx₀1 : x₀ ≠ 1 := fun h => hrm (by rw [← hmkx₀, h]; rfl)
    have hxA : (x₀ : Γ) ∈ A := by
      refine hmax _ (by rw [← Subgroup.coe_pow, hx₀3, Subgroup.coe_one]) fun a ha => ?_
      have hx : (x₀ : Γ) = (c : Γ) ^ m := by rw [hx₀def, Subgroup.coe_pow]
      rw [hx]
      exact (Commute.pow_right (hcA a ha) m).eq
    exact ⟨x₀, hxA, m, hm3, hmkx₀⟩
  have hcube : ∀ x : X, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ^ 3 = 1 := fun x ⟨k, hk⟩ =>
    Sec13.ON134.pow_three_eq_one ψM hk
  have hkey : ∀ r : X, r ^ 3 = 1 → (∀ x ∈ P, x * r = r * x) → r ∈ P := by
    intro r hr3 hrP
    by_cases hr1 : r = 1
    · rw [hr1]; exact P.one_mem
    have hrfix : ∀ a : ↥A, σ a r = r := by
      intro a
      obtain ⟨x, hx⟩ := hinner a
      have hxP : x ∈ P := by
        show MulAut.conj x ∈ σ.range
        rw [← hx]
        exact ⟨a, rfl⟩
      rw [hx, MulAut.conj_apply, hrP x hxP, mul_inv_cancel_right]
    obtain ⟨x₀, hx₀A, m, hm3, hx₀r⟩ := hlift r hr3 hr1 hrfix
    have hrmP : r ^ m ∈ P := by
      show MulAut.conj (r ^ m) ∈ σ.range
      rw [← hx₀r, ← hσx x₀ hx₀A]
      exact ⟨_, rfl⟩
    have hcop : m.gcd (orderOf r) = 1 := by
      rw [orderOf_eq_prime hr3 hr1]
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3).symm
    exact Subgroup.zpowers_le.mpr hrmP (mem_zpowers_pow_iff.mpr hcop)
  have heker : (⟨e, heA⟩ : ↥A) ∈ σ.ker := by
    rw [mem_ker_thetaQuotientAction_iff]
    intro y hy
    have hey : e * y = y * e := (Subgroup.mem_centralizer_singleton_iff.mp (hLe hy)).symm
    rw [show e * y * e⁻¹ * y⁻¹ = 1 by rw [hey, mul_inv_cancel_right, mul_inv_cancel]]
    exact one_mem _
  have hrange : Nat.card σ.range ∣ 9 := by
    have h1 := Res9ON.card_eq_card_ker_mul_card_range σ
    rw [hA.2] at h1
    have h3 : 3 ∣ Nat.card σ.ker := by
      have h4 : orderOf (⟨e, heA⟩ : ↥A) = 3 := by
        rw [← Subgroup.orderOf_coe]
        exact orderOf_eq_prime (hA3 e heA) he1
      have h5 := Subgroup.orderOf_dvd_natCard σ.ker heker
      rwa [h4] at h5
    obtain ⟨t, ht⟩ := h3
    refine ⟨t, ?_⟩
    have h6 : 3 * 9 = 3 * (Nat.card σ.range * t) := by
      rw [show (3 : ℕ) * 9 = 27 by rfl, h1, ht]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h6
  have hP3 : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    refine hcube x ⟨3, ?_⟩
    have h1 : orderOf x ∣ 27 := by
      have h2 := Subgroup.orderOf_dvd_natCard P hx
      rw [hPcard] at h2
      exact h2.trans (Nat.mul_dvd_mul_left 3 hrange)
    exact orderOf_dvd_iff_pow_eq_one.mp (by norm_num at h1 ⊢; exact h1)
  have hr9 : Nat.card σ.range = 9 := by
    rcases (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card σ.range ∣ 3 ^ 2 from hrange)
      with ⟨j, hj, hj'⟩
    interval_cases j
    ·
      exfalso
      have hPZ : P = Subgroup.center X := by
        refine (Subgroup.eq_of_le_of_card_ge hZP ?_).symm
        rw [hPcard, hj', hZ3]
        norm_num
      obtain ⟨S, -, hS81, hSel⟩ := Res9ON.exists_elemAbelian_le_ON ψ (IsPGroup.of_bot (p := 3))
      obtain ⟨s, hsS, hs1⟩ : ∃ s ∈ S, s ≠ 1 := by
        by_contra hno
        push Not at hno
        have hbot : S = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hno
        rw [hbot, Subgroup.card_bot] at hS81
        omega
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
      have hy3 : y ^ 3 = 1 := by
        refine hcube y ⟨2, ?_⟩
        have h1 : y ^ 3 ∈ Subgroup.center X := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
          exact hSel.2 _ hsS
        have h2 : (⟨y ^ 3, h1⟩ : Subgroup.center X) ^ Nat.card (Subgroup.center X) = 1 :=
          pow_card_eq_one'
        rw [hZ3] at h2
        have h3 := congrArg Subtype.val h2
        simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at h3
        rw [← pow_mul] at h3
        exact h3
      have hyP : y ∈ P := hkey y hy3 fun x hx => by
        rw [hPZ] at hx
        exact (Subgroup.mem_center_iff.mp hx y).symm
      rw [hPZ] at hyP
      exact hs1 ((QuotientGroup.eq_one_iff y).mpr hyP)
    ·
      exfalso
      have hP9 : Nat.card P = 9 := by rw [hPcard, hj']; norm_num
      obtain ⟨ℓ, hℓP, hℓZ⟩ : ∃ ℓ ∈ P, ℓ ∉ Subgroup.center X := by
        by_contra hno
        push Not at hno
        have h1 : P ≤ Subgroup.center X := hno
        have h2 := Subgroup.card_le_of_le h1
        rw [hP9, hZ3] at h2
        omega
      obtain ⟨r, hr3, hrℓ, hrn⟩ := Sec13.ON134.exists_centralizer ψM (hP3 ℓ hℓP) hℓZ
      have hPeq : P = Subgroup.zpowers ℓ ⊔ Subgroup.center X := by
        have hle' : Subgroup.zpowers ℓ ⊔ Subgroup.center X ≤ P :=
          sup_le (Subgroup.zpowers_le.mpr hℓP) hZP
        refine (Subgroup.eq_of_le_of_card_ge hle' ?_).symm
        rw [hP9]
        have hZlt : Subgroup.center X < Subgroup.zpowers ℓ ⊔ Subgroup.center X :=
          lt_of_le_of_ne le_sup_right fun h => hℓZ (h ▸ Subgroup.mem_sup_left
            (Subgroup.mem_zpowers ℓ))
        have h1 : Nat.card (Subgroup.center X) ∣ Nat.card ↥(Subgroup.zpowers ℓ ⊔
            Subgroup.center X) := Subgroup.card_dvd_of_le le_sup_right
        have h2 : Nat.card ↥(Subgroup.zpowers ℓ ⊔ Subgroup.center X) ∣ 9 :=
          hP9 ▸ Subgroup.card_dvd_of_le hle'
        have h3 : Nat.card (Subgroup.center X) < Nat.card ↥(Subgroup.zpowers ℓ ⊔
            Subgroup.center X) := Subgroup.card_lt_of_lt hZlt
        rw [hZ3] at h3
        obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
          (show Nat.card ↥(Subgroup.zpowers ℓ ⊔ Subgroup.center X) ∣ 3 ^ 2 from h2)
        rw [hj'] at h3 ⊢
        interval_cases j <;> first | (norm_num at h3; done) | norm_num
      have hrP : r ∈ P := by
        refine hkey r hr3 fun x hx => ?_
        have hC : Subgroup.zpowers ℓ ⊔ Subgroup.center X ≤
            Subgroup.centralizer ({r} : Set X) := by
          refine sup_le (Subgroup.zpowers_le.mpr ?_) fun z hz => ?_
          · exact Subgroup.mem_centralizer_singleton_iff.mpr hrℓ.symm
          · exact Subgroup.mem_centralizer_singleton_iff.mpr
              (Subgroup.mem_center_iff.mp hz r).symm
        rw [hPeq] at hx
        exact Subgroup.mem_centralizer_singleton_iff.mp (hC hx)
      rw [hPeq] at hrP
      exact hrn hrP
    · rw [hj']; norm_num
  have hP27 : Nat.card P = 27 := by rw [hPcard, hr9]
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    by_contra hno
    push Not at hno
    obtain ⟨x₁, hx₁, x₂, hx₂, h12⟩ := hno
    set π := QuotientGroup.mk' (Subgroup.center X) with hπdef
    have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
    obtain ⟨T, hPT, hT81, hTel⟩ := Res9ON.exists_elemAbelian_le_ON ψ (hPp.map π)
    set S := T.comap π with hSdef
    have hPS : P ≤ S := fun x hx => hPT ⟨x, hx, rfl⟩
    have hZS : Subgroup.center X ≤ S := fun z hz => by
      show π z ∈ T
      rw [hπdef, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz]
      exact T.one_mem
    have hS243 : Nat.card S = 243 := by
      set ι := π.domRestrict S with hιdef
      have hιrange : ι.range = T := by
        rw [hιdef, MonoidHom.domRestrict_range, hSdef,
          Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
      have hιker : Nat.card ι.ker = 3 := by
        have hk : ι.ker = (Subgroup.center X).subgroupOf S := by
          rw [hιdef, MonoidHom.ker_domRestrict, hπdef, QuotientGroup.ker_mk']
        rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv, hZ3]
      rw [Res9ON.card_eq_card_ker_mul_card_range ι, hιker, hιrange, hT81]
    have hScomm : ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ Subgroup.center X := by
      intro s hs t ht
      have hst : π s * π t = π t * π s :=
        congrArg Subtype.val (hTel.1.is_comm.comm ⟨π s, hs⟩ ⟨π t, ht⟩)
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπdef, map_mul, map_mul,
        map_mul, map_inv, map_inv, hst]
      group
    have hS3 : ∀ s ∈ S, s ^ 3 ∈ Subgroup.center X := by
      intro s hs
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπdef, map_pow]
      exact hTel.2 _ hs
    obtain ⟨r, -, hr3, hrP, hrc⟩ := Res9ON.exists_pow_three_eq_one_centralizes le_rfl hZ3 hZP
      hP27 hx₁ hx₂ h12 hPS hS243 hScomm hS3
    exact hrP (hkey r hr3 hrc)
  set Abar : Subgroup X := (A.subgroupOf L).map (QuotientGroup.mk' _) with hAbardef
  have hPA : P ≤ Abar := by
    intro p hp
    by_cases hp1 : p = 1
    · rw [hp1]; exact Abar.one_mem
    have hpfix : ∀ a : ↥A, σ a p = p := by
      intro a
      obtain ⟨x, hx⟩ := hinner a
      have hxP : x ∈ P := by
        show MulAut.conj x ∈ σ.range
        rw [← hx]
        exact ⟨a, rfl⟩
      rw [hx, MulAut.conj_apply, hPab x hxP p hp, mul_inv_cancel_right]
    obtain ⟨x₀, hx₀A, m, hm3, hx₀p⟩ := hlift p (hP3 p hp) hp1 hpfix
    have hx₀mem : ((x₀ : ↥L) : X) ∈ Abar :=
      ⟨x₀, Subgroup.mem_subgroupOf.mpr hx₀A, rfl⟩
    rw [hx₀p] at hx₀mem
    have hcop : m.gcd (orderOf p) = 1 := by
      rw [orderOf_eq_prime (hP3 p hp) hp1]
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3).symm
    exact Subgroup.zpowers_le.mpr hx₀mem (mem_zpowers_pow_iff.mpr hcop)
  have hcardAL : 27 ≤ Nat.card ↥(A ⊓ L) := by
    have h1 : Nat.card P ≤ Nat.card Abar := Subgroup.card_le_of_le hPA
    have h2 : Nat.card Abar ≤ Nat.card (A.subgroupOf L) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    have h3 : Nat.card (A.subgroupOf L) = Nat.card ↥(A ⊓ L) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective L.subtype_injective]
    rw [hP27] at h1
    omega
  have hAL' : A ⊓ L = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hA.2]; exact hcardAL)
  exact inf_eq_left.mp hAL'

theorem inf_theta_eq_bot {A L : Subgroup Γ} (hA : IsPGroup 3 A) :
    A ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθ3 : ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L) := by
    rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hA ⟨x, hx.1⟩
  have h1 : orderOf x ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L) :=
    Subgroup.orderOf_dvd_natCard _ hx.2
  have h2 : orderOf x = 3 ^ n := by rw [← hn, Subgroup.orderOf_mk]
  rcases n with _ | n
  · rw [pow_zero] at h2
    exact orderOf_eq_one_iff.mp h2
  · exfalso
    apply hθ3
    rw [h2] at h1
    exact (dvd_pow_self 3 (by omega)).trans h1

end CFSG.RankThree.PartTwo.Sec14.ONLoc
