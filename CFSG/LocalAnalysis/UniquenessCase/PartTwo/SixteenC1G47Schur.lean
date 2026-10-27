module

public import Mathlib.GroupTheory.IsPerfect
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

private lemma s16c1_G47_schur16_map_self_of_mapsTo {F : Type*} [Group F] [Finite F] (e : MulAut F)
    (H : Subgroup F) (he : ∀ x ∈ H, e x ∈ H) : H.map (e : F →* F) = H := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact he y hy
  · exact (Subgroup.card_map_of_injective (f := (e : F →* F)) e.injective).ge

private noncomputable def s16c1_G47_schur16_restrictMulAut {F : Type*} [Group F] [Finite F]
    (e : MulAut F) (H : Subgroup F) (he : ∀ x ∈ H, e x ∈ H) : MulAut H :=
  (e.subgroupMap H).trans
    (MulEquiv.subgroupCongr (s16c1_G47_schur16_map_self_of_mapsTo e H he))

@[simp]
private lemma s16c1_G47_schur16_restrictMulAut_apply {F : Type*} [Group F] [Finite F]
    (e : MulAut F) (H : Subgroup F) (he : ∀ x ∈ H, e x ∈ H) (x : H) :
    (((s16c1_G47_schur16_restrictMulAut e H he) x : H) : F) = e x := by
  simp [s16c1_G47_schur16_restrictMulAut]

private lemma s16c1_G47_schur16_restrictMulAut_mul {F : Type*} [Group F] [Finite F]
    (e₁ e₂ : MulAut F) (H : Subgroup F) (h₁ : ∀ x ∈ H, e₁ x ∈ H)
    (h₂ : ∀ x ∈ H, e₂ x ∈ H) (h : ∀ x ∈ H, (e₁ * e₂) x ∈ H) :
    s16c1_G47_schur16_restrictMulAut (e₁ * e₂) H h =
      s16c1_G47_schur16_restrictMulAut e₁ H h₁ *
        s16c1_G47_schur16_restrictMulAut e₂ H h₂ := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  simp only [s16c1_G47_schur16_restrictMulAut_apply, MulAut.mul_apply]

private lemma s16c1_G47_schur16_restrictMulAut_pow_apply {F : Type*} [Group F] [Finite F]
    (e : MulAut F) (H : Subgroup F) (he : ∀ x ∈ H, e x ∈ H) (n : ℕ) (x : H) :
    (((s16c1_G47_schur16_restrictMulAut e H he) ^ n) x : F) = (e ^ n) (x : F) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih (s16c1_G47_schur16_restrictMulAut e H he x),
      s16c1_G47_schur16_restrictMulAut_apply, pow_succ, MulAut.mul_apply]

private lemma s16c1_G47_schur16_fixedPoints_card {E : Type*} [Group E] (σ : MulAut E)
    (hfix : ∀ x : E, σ x = x → x = 1) :
    Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) E) = 1 := by
  classical
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · refine ⟨fun x y => ?_⟩
    have hx : (x : E) = 1 := hfix (x : E) (by
      have hmem := x.2 ⟨σ, Subgroup.mem_zpowers σ⟩
      simpa [MulAut.smul_def, Subgroup.smul_def] using hmem)
    have hy : (y : E) = 1 := hfix (y : E) (by
      have hmem := y.2 ⟨σ, Subgroup.mem_zpowers σ⟩
      simpa [MulAut.smul_def, Subgroup.smul_def] using hmem)
    exact Subtype.ext (by rw [hx, hy])
  · exact ⟨1, by
      rw [MulAction.mem_fixedPoints]
      intro g
      simp [MulAut.smul_def, Subgroup.smul_def]⟩

private lemma s16c1_G47_schur16_card_modEq {E : Type*} [Group E] [Finite E] (σ : MulAut E)
    {q : ℕ} (hq : q.Prime) (hσ : σ ^ q = 1) (hfix : ∀ x : E, σ x = x → x = 1) :
    Nat.card E ≡ 1 [MOD q] := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q ↥(Subgroup.zpowers σ) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [pow_one, Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hσ
  have hcard := s16c1_G47_schur16_fixedPoints_card σ hfix
  have hmod := hG.card_modEq_card_fixedPoints E
  rwa [hcard] at hmod

theorem s16c1_G47_schur16 {Hs F : Type} [Group Hs] [Group F] [Finite F] (ρ : Hs →* MulAut F)
    (hF : ∀ e : F, e * e = 1) {D₀ : Subgroup F} (hD : Nat.card ↥D₀ = 16)
    {Xs : Subgroup Hs} (hX : Group.IsPerfect Xs)
    (hDX : ∀ x ∈ Xs, ∀ d ∈ D₀, ρ x d ∈ D₀)
    (hirr : ∀ S : Subgroup F, S ≤ D₀ → (∀ x ∈ Xs, ∀ s ∈ S, ρ x s ∈ S) → S = ⊥ ∨ S = D₀)
    {c : Hs} {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hcq : c ^ q = 1)
    (hcX : ∀ x ∈ Xs, c * x = x * c) (hcD : ∀ d ∈ D₀, ρ c d ∈ D₀) :
    ∀ d ∈ D₀, ρ c d = d := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let σ : MulAut ↥D₀ := s16c1_G47_schur16_restrictMulAut (ρ c) D₀ hcD
  have hσ_apply : ∀ x : ↥D₀, ((σ x : ↥D₀) : F) = ρ c (x : F) :=
    fun x => s16c1_G47_schur16_restrictMulAut_apply (ρ c) D₀ hcD x
  have hσq : σ ^ q = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [s16c1_G47_schur16_restrictMulAut_pow_apply, ← map_pow, hcq, map_one]
    simp
  let Fix : Subgroup F := MonoidHom.eqLocus (ρ c : F →* F) (MonoidHom.id F) ⊓ D₀
  have mem_Fix : ∀ d : F, d ∈ Fix ↔ d ∈ D₀ ∧ ρ c d = d := by
    intro d
    change d ∈ (MonoidHom.eqLocus (ρ c : F →* F) (MonoidHom.id F) ⊓ D₀) ↔
      d ∈ D₀ ∧ ρ c d = d
    rw [Subgroup.mem_inf]
    change (ρ c d = d ∧ d ∈ D₀) ↔ d ∈ D₀ ∧ ρ c d = d
    tauto
  have hFix_le : Fix ≤ D₀ := inf_le_right
  have hFix_inv : ∀ x ∈ Xs, ∀ d ∈ Fix, ρ x d ∈ Fix := by
    intro x hx d hd
    rw [mem_Fix] at hd ⊢
    obtain ⟨hdD, hdc⟩ := hd
    refine ⟨hDX x hx d hdD, ?_⟩
    calc ρ c (ρ x d) = (ρ c * ρ x) d := by rw [MulAut.mul_apply]
      _ = ρ (c * x) d := by rw [← map_mul]
      _ = ρ (x * c) d := by rw [hcX x hx]
      _ = (ρ x * ρ c) d := by rw [map_mul]
      _ = ρ x (ρ c d) := by rw [MulAut.mul_apply]
      _ = ρ x d := by rw [hdc]
  rcases or_comm.mp (hirr Fix hFix_le hFix_inv) with hFix_top | hFix_bot
  ·
    intro d hd
    exact (mem_Fix d).mp (by rw [hFix_top]; exact hd) |>.2
  ·
    exfalso
    have hfix1 : ∀ d : F, d ∈ D₀ → ρ c d = d → d = 1 := by
      intro d hd hdc
      have hmem : d ∈ Fix := (mem_Fix d).mpr ⟨hd, hdc⟩
      rw [hFix_bot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hfixD : ∀ x : ↥D₀, σ x = x → x = 1 := by
      intro x hx
      refine Subtype.ext (hfix1 (x : F) x.2 ?_)
      have h2 := congrArg (fun y : ↥D₀ => (y : F)) hx
      rwa [hσ_apply x] at h2
    have hmodD : Nat.card ↥D₀ ≡ 1 [MOD q] :=
      s16c1_G47_schur16_card_modEq σ hq hσq hfixD
    rw [hD] at hmodD
    have h15 : q ∣ 15 := by
      have := (Nat.modEq_iff_dvd' (show 1 ≤ 16 by norm_num)).mp hmodD.symm
      norm_num at this ⊢
      exact this
    have hq5 : q = 5 := by
      have h' : q ∣ 15 := h15
      rw [show (15 : ℕ) = 3 * 5 by norm_num] at h'
      rcases (hq.dvd_mul).mp h' with h | h
      · have : q ≤ 3 := Nat.le_of_dvd (by norm_num) h
        omega
      · have : q ≤ 5 := Nat.le_of_dvd (by norm_num) h
        omega
    have hnt : Nontrivial ↥D₀ := by
      rw [← Finite.one_lt_card_iff_nontrivial, hD]
      norm_num
    obtain ⟨a, ha1⟩ := exists_ne (1 : ↥D₀)
    let T : Set ↥D₀ := Set.range fun i : ℕ => (σ ^ i) a
    let S : Subgroup ↥D₀ := Subgroup.closure T
    have ha_mem : a ∈ S := Subgroup.subset_closure ⟨0, by simp⟩
    have hSinv : ∀ s ∈ S, σ s ∈ S := by
      intro s hs
      exact Subgroup.closure_induction (p := fun x _ => σ x ∈ S)
        (fun y hy => by
          obtain ⟨i, rfl⟩ := hy
          have hgen : (σ ^ (i + 1)) a ∈ S := Subgroup.subset_closure ⟨i + 1, rfl⟩
          simpa [pow_succ', MulAut.mul_apply] using hgen)
        (by simpa using Subgroup.one_mem S)
        (fun x y hx hy hx' hy' => by
          rw [map_mul]
          exact S.mul_mem hx' hy')
        (fun x hx hx' => by
          rw [map_inv]
          exact S.inv_mem hx') hs
    have hSfix : ∀ x : ↥S,
        s16c1_G47_schur16_restrictMulAut σ S hSinv x = x → x = 1 := by
      intro x hx
      have hx' : σ (x : ↥D₀) = (x : ↥D₀) := by
        have h2 := congrArg (fun y : ↥S => (y : ↥D₀)) hx
        rwa [s16c1_G47_schur16_restrictMulAut_apply] at h2
      exact Subtype.ext (hfixD (x : ↥D₀) hx')
    have hSq : s16c1_G47_schur16_restrictMulAut σ S hSinv ^ q = 1 := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [s16c1_G47_schur16_restrictMulAut_pow_apply, hσq]
      simp
    have hmodS : Nat.card ↥S ≡ 1 [MOD q] :=
      s16c1_G47_schur16_card_modEq (s16c1_G47_schur16_restrictMulAut σ S hSinv) hq hSq hSfix
    have hSdvd : Nat.card ↥S ∣ 16 := by
      have := Subgroup.card_subgroup_dvd_card S
      rwa [hD] at this
    have hSne : Nat.card ↥S ≠ 1 := by
      intro h1
      have hsub : Subsingleton ↥S := (Nat.card_eq_one_iff_unique.mp h1).1
      have : (⟨a, ha_mem⟩ : ↥S) = 1 := Subsingleton.elim _ _
      exact ha1 (Subtype.ext_iff.mp this)
    have hS16 : Nat.card ↥S = 16 := by
      have hSdvd2 : Nat.card ↥S ∣ 2 ^ 4 := by
        simpa [show (2 : ℕ) ^ 4 = 16 by norm_num] using hSdvd
      obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hSdvd2
      have hmod5 : (2 : ℕ) ^ k ≡ 1 [MOD 5] := by
        have hh : Nat.card ↥S ≡ 1 [MOD 5] := by rwa [hq5] at hmodS
        rwa [hk] at hh
      interval_cases k
      · exfalso
        exact hSne (by rw [hk, pow_zero])
      · exfalso
        have h : (2 : ℕ) % 5 = 1 % 5 := hmod5
        norm_num at h
      · exfalso
        have h : (4 : ℕ) % 5 = 1 % 5 := hmod5
        norm_num at h
      · exfalso
        have h : (8 : ℕ) % 5 = 1 % 5 := hmod5
        norm_num at h
      · rw [hk]
        norm_num
    have hStop : S = ⊤ := Subgroup.eq_top_of_card_eq S (by rw [hS16, hD])
    let C : Subgroup (MulAut ↥D₀) := Subgroup.centralizer ({σ} : Set (MulAut ↥D₀))
    have hinj : Function.Injective (fun φ : ↥C => (φ.1 : MulAut ↥D₀) a) := by
      intro φ₁ φ₂ h
      have hcomm : ∀ φ : ↥C, Commute φ.1 σ := by
        intro φ
        have hmem := Subgroup.mem_centralizer_iff.mp φ.2
        exact (hmem σ (Set.mem_singleton σ)).symm
      have hkey : ∀ (φ : ↥C) (i : ℕ), φ.1 ((σ ^ i) a) = (σ ^ i) (φ.1 a) := by
        intro φ i
        calc φ.1 ((σ ^ i) a) = (φ.1 * σ ^ i) a := by rw [MulAut.mul_apply]
          _ = (σ ^ i * φ.1) a := by rw [(hcomm φ).pow_right i]
          _ = (σ ^ i) (φ.1 a) := by rw [MulAut.mul_apply]
      have hab : φ₁.1 a = φ₂.1 a := h
      apply Subtype.ext
      apply MulEquiv.ext
      intro y
      have hE : Subgroup.closure T ≤
          MonoidHom.eqLocus (φ₁.1 : ↥D₀ →* ↥D₀) (φ₂.1 : ↥D₀ →* ↥D₀) := by
        rw [Subgroup.closure_le]
        intro z hz
        obtain ⟨i, rfl⟩ := hz
        change φ₁.1 ((σ ^ i) a) = φ₂.1 ((σ ^ i) a)
        rw [hkey φ₁ i, hkey φ₂ i, hab]
      have hy : y ∈ MonoidHom.eqLocus (φ₁.1 : ↥D₀ →* ↥D₀) (φ₂.1 : ↥D₀ →* ↥D₀) :=
        hE (by change y ∈ S; rw [hStop]; exact Subgroup.mem_top y)
      change φ₁.1 y = φ₂.1 y at hy
      exact hy
    have hCcard : Nat.card ↥C ≤ 16 := by
      have := Nat.card_le_card_of_injective
        (fun φ : ↥C => (φ.1 : MulAut ↥D₀) a) hinj
      rwa [hD] at this
    let θ : ↥Xs →* MulAut ↥D₀ :=
      { toFun := fun x => s16c1_G47_schur16_restrictMulAut (ρ x.1) D₀ (hDX x.1 x.2)
        map_one' := by
          apply MulEquiv.ext
          intro y
          apply Subtype.ext
          simp [s16c1_G47_schur16_restrictMulAut_apply]
        map_mul' := by
          intro x y
          apply MulEquiv.ext
          intro d
          apply Subtype.ext
          simp only [s16c1_G47_schur16_restrictMulAut_apply, MulAut.mul_apply]
          rw [show ρ (x * y).1 = ρ x.1 * ρ y.1 from map_mul ρ x.1 y.1]
          rfl }
    have hθ_apply : ∀ (x : ↥Xs) (y : ↥D₀), (((θ x) y : ↥D₀) : F) = ρ x.1 (y : F) :=
      fun x y => s16c1_G47_schur16_restrictMulAut_apply (ρ x.1) D₀ (hDX x.1 x.2) y
    have hσθ : ∀ x : ↥Xs, σ * θ x = θ x * σ := by
      intro x
      apply MulEquiv.ext
      intro d
      apply Subtype.ext
      rw [MulAut.mul_apply, MulAut.mul_apply]
      rw [hσ_apply ((θ x) d), hθ_apply x d, hθ_apply x (σ d), hσ_apply d]
      have hcx : ρ c * ρ x.1 = ρ x.1 * ρ c := by
        have := congrArg (fun z : Hs => ρ z) (hcX x.1 x.2)
        simpa only [map_mul] using this
      have hd := congrArg (fun e : MulAut F => e (d : F)) hcx
      simpa only [MulAut.mul_apply] using hd
    have hθC : θ.range ≤ C := by
      intro y hy
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact hσθ x
    have hrange_le : Nat.card θ.range ≤ Nat.card ↥C :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hθC) (Subgroup.inclusion_injective hθC)
    have hrange16 : Nat.card θ.range ≤ 16 := le_trans hrange_le hCcard
    haveI : Group.IsPerfect ↥Xs := hX
    haveI : Group.IsPerfect θ.range := Group.IsPerfect.range θ
    have hsolv : Group.IsSolvable θ.range :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable (G := ↥θ.range) (by omega)
    have htriv : Subsingleton θ.range := by
      by_contra hns
      haveI : Nontrivial θ.range := not_subsingleton_iff_nontrivial.mp hns
      exact Group.IsPerfect.not_isSolvable (G := θ.range) hsolv
    have hθ1 : ∀ x : ↥Xs, θ x = 1 := by
      intro x
      have h1 : (⟨θ x, x, rfl⟩ : θ.range) = 1 := Subsingleton.elim _ _
      simpa using congrArg Subtype.val h1
    have htrivD : ∀ x ∈ Xs, ∀ d ∈ D₀, ρ x d = d := by
      intro x hx d hd
      have h1 := congrArg (fun e : MulAut ↥D₀ => e ⟨d, hd⟩) (hθ1 ⟨x, hx⟩)
      have h2 : (((θ ⟨x, hx⟩) ⟨d, hd⟩ : ↥D₀) : F) = ((⟨d, hd⟩ : ↥D₀) : F) :=
        congrArg (fun y : ↥D₀ => (y : F)) h1
      rw [hθ_apply ⟨x, hx⟩ ⟨d, hd⟩] at h2
      simpa using h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2dvd : 2 ∣ Nat.card ↥D₀ := by rw [hD]; norm_num
    obtain ⟨s, hs2⟩ := exists_prime_orderOf_dvd_card' (G := ↥D₀) 2 h2dvd
    let S₂ : Subgroup F := Subgroup.zpowers ((s : ↥D₀) : F)
    have hS₂le : S₂ ≤ D₀ := Subgroup.zpowers_le.mpr (s : ↥D₀).2
    have hS₂card : Nat.card ↥S₂ = 2 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hs2]
    have hS₂inv : ∀ x ∈ Xs, ∀ y ∈ S₂, ρ x y ∈ S₂ := by
      intro x hx y hy
      rw [htrivD x hx y (hS₂le hy)]
      exact hy
    rcases hirr S₂ hS₂le hS₂inv with h | h
    · have hmem : ((s : ↥D₀) : F) ∈ S₂ := Subgroup.mem_zpowers _
      rw [h] at hmem
      have hs1 : (s : ↥D₀) = 1 := Subtype.ext (Subgroup.mem_bot.mp hmem)
      rw [hs1] at hs2
      simp only [orderOf_one] at hs2
      omega
    · have h16 : Nat.card ↥S₂ = 16 := by rw [h]; exact hD
      omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
