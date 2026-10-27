module

public import CFSG.LocalAnalysis.StandardType.GGL45NtClBlocks
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldDefs

public section

namespace CFSG.HardMathSupport.C14Cl

open CFSG CFSG.Open CFSG.StandardType

@[expose] def CentPAbs (p : ℕ) {H : Type*} [Group H] (E₀ : Subgroup H) (x : H) : Prop :=
  (∀ e ∈ E₀, x * e = e * x) ∧ ∃ k : ℕ, x ^ p ^ k = 1

@[expose] def ClCoreConcl (p : ℕ) {H : Type*} [Group H] (E₀ : Subgroup H) (α : H →* H) : Prop :=
  ∃ s : ℕ, 2 ≤ s ∧ ∃ k : ℕ, ¬ p ∣ k ∧
    (∀ x y : H, CentPAbs p E₀ x → CentPAbs p E₀ y → x * y = y * x) ∧
    (∀ x : H, CentPAbs p E₀ x → x ^ p ^ s = 1 ∧ α x = x ^ (1 + (p : ℤ) ^ (s - 1) * k)) ∧
    (∀ x : H, CentPAbs p E₀ x → ∀ w : H, (∀ e ∈ E₀, w * e = e * w) → w * x = x * w) ∧
    ∃ a₁ a₂ : H, CentPAbs p E₀ a₁ ∧ CentPAbs p E₀ a₂ ∧
      a₁ ^ p ^ (s - 1) ∈ E₀ ∧ a₂ ^ p ^ (s - 1) ∈ E₀ ∧
      ∀ i j : ℕ, (a₁ ^ p ^ (s - 1)) ^ i * (a₂ ^ p ^ (s - 1)) ^ j = 1 → p ∣ i ∧ p ∣ j

@[expose] noncomputable def ClSetting.sigmaOn {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (S : ClSetting K ι) {H : Subgroup (GL ι K)} (hH : S.GoodGroup H) :
    ↥H →* ↥H where
  toFun x := ⟨S.σGL (x : GL ι K), hH.sigma x x.2⟩
  map_one' := Subtype.ext (map_one S.σGL)
  map_mul' x y := Subtype.ext (map_mul S.σGL (x : GL ι K) (y : GL ι K))

private lemma cT0_centP_of_centPAbs {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ClSetting K ι) {H : Subgroup (GL ι K)} (hH : S.GoodGroup H)
    (hEH : ∀ e ∈ S.E₀, e ∈ H) {x : ↥H}
    (h : CentPAbs S.p (S.E₀.subgroupOf H) x) : S.CentP H (x : GL ι K) := by
  unfold CentPAbs at h
  unfold ClSetting.CentP ClSetting.Cent
  refine ⟨x.2, ⟨hH.cent x x.2, ?_⟩, ?_⟩
  · intro e he
    have hmem : (⟨e, hEH e he⟩ : ↥H) ∈ S.E₀.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]; exact he
    have h' := h.1 ⟨e, hEH e he⟩ hmem
    simpa [Subgroup.coe_mul] using congrArg (fun g : ↥H => (g : GL ι K)) h'
  · obtain ⟨m, hm⟩ := h.2
    refine ⟨m, ?_⟩
    rw [← Subgroup.coe_pow, hm]
    simp

private lemma cT0_centPAbs_of_centP {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ClSetting K ι) {H : Subgroup (GL ι K)} {x : ↥H}
    (h : S.CentP H (x : GL ι K)) : CentPAbs S.p (S.E₀.subgroupOf H) x := by
  unfold ClSetting.CentP ClSetting.Cent at h
  unfold CentPAbs
  refine ⟨?_, ?_⟩
  · intro e he
    have h' := h.2.1.2 (e : GL ι K) (Subgroup.mem_subgroupOf.1 he)
    exact Subtype.ext (by simpa [Subgroup.coe_mul] using h')
  · obtain ⟨m, hm⟩ := h.2.2
    refine ⟨m, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow]
    simpa using hm

theorem ClSetting.clCoreConcl {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ClSetting K ι) [Fintype K] [CharP K 2] {H : Subgroup (GL ι K)} (hH : S.GoodGroup H)
    (hSat : S.Sat H) (hEH : ∀ e ∈ S.E₀, e ∈ H) (hcard : S.p ^ 2 ≤ Nat.card S.E₀) :
    ClCoreConcl S.p (S.E₀.subgroupOf H) (S.sigmaOn hH) := by
  unfold ClCoreConcl
  obtain ⟨s, hs2, k, hk, hcomm, hexp, hcen, a₁, a₂, ha₁, ha₂, ha₁E, ha₂E, hindep⟩ :=
    S.matrix_core hH hSat hEH hcard
  unfold ClSetting.CentP ClSetting.Cent at ha₁ ha₂
  refine ⟨s, hs2, k, hk, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    exact Subtype.ext (by
      simpa [Subgroup.coe_mul] using
        hcomm (x : GL ι K) (y : GL ι K) (cT0_centP_of_centPAbs S hH hEH hx)
          (cT0_centP_of_centPAbs S hH hEH hy))
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hexp (x : GL ι K) (cT0_centP_of_centPAbs S hH hEH hx)
    refine ⟨?_, ?_⟩
    · refine Subtype.ext ?_
      rw [Subgroup.coe_pow]
      simpa using hx1
    · refine Subtype.ext ?_
      change S.σGL (x : GL ι K) = (x : GL ι K) ^ (1 + (S.p : ℤ) ^ (s - 1) * k)
      exact hx2
  · intro x hx w hw
    have hw' : S.Cent (w : GL ι K) := by
      unfold ClSetting.Cent
      refine ⟨hH.cent w w.2, ?_⟩
      intro e he
      have hmem : (⟨e, hEH e he⟩ : ↥H) ∈ S.E₀.subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]; exact he
      have h' := hw ⟨e, hEH e he⟩ hmem
      simpa [Subgroup.coe_mul] using congrArg (fun g : ↥H => (g : GL ι K)) h'
    exact Subtype.ext (by
      simpa [Subgroup.coe_mul] using
        hcen (x : GL ι K) (cT0_centP_of_centPAbs S hH hEH hx) (w : GL ι K) w.2 hw')
  · refine ⟨⟨a₁, ha₁.1⟩, ⟨a₂, ha₂.1⟩, cT0_centPAbs_of_centP S ha₁,
      cT0_centPAbs_of_centP S ha₂, ?_, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 (by simpa [Subgroup.coe_pow] using ha₁E)
    · exact Subgroup.mem_subgroupOf.2 (by simpa [Subgroup.coe_pow] using ha₂E)
    · intro i j hij
      refine hindep i j ?_
      have h' := congrArg (fun g : ↥H => (g : GL ι K)) hij
      simpa [Subgroup.coe_mul, Subgroup.coe_pow] using h'

theorem exists_pElt_lift {p : ℕ} (hp : p.Prime) {H M : Type*} [Group H] [Group M] (q : H →* M)
    {h : H} (hh : IsOfFinOrder h) {k : ℕ} (hk : q h ^ p ^ k = 1) :
    ∃ h' : H, (∃ n : ℕ, h' = h ^ n) ∧ (∃ j : ℕ, h' ^ p ^ j = 1) ∧ q h' = q h := by
  have hn : orderOf h ≠ 0 := hh.orderOf_pos.ne'
  obtain ⟨a, m, hm, hn_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hcop : (p ^ a).Coprime m := (hp.coprime_iff_not_dvd.mpr hm).pow_left a
  obtain ⟨t, ht1, ht0⟩ := Nat.chineseRemainder hcop 1 0
  refine ⟨h ^ t, ⟨t, rfl⟩, ?_, ?_⟩
  ·
    refine ⟨a, ?_⟩
    have hdvd : orderOf h ∣ t * p ^ a := by
      rw [hn_eq]
      exact hcop.mul_dvd_of_dvd_of_dvd (dvd_mul_left (p ^ a) t)
        (dvd_mul_of_dvd_left (Nat.modEq_zero_iff_dvd.mp ht0) (p ^ a))
    rw [← pow_mul]
    exact (orderOf_dvd_iff_pow_eq_one).mp hdvd
  ·
    rw [map_pow]
    have hd : orderOf (q h) ∣ p ^ a := by
      have hdvd1 : orderOf (q h) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
      have hdvd2 : orderOf (q h) ∣ p ^ a * m := by
        rw [← hn_eq]
        exact orderOf_map_dvd q h
      exact (((hp.coprime_iff_not_dvd.mpr hm).pow_left k).coprime_dvd_left hdvd1).dvd_of_dvd_mul_right
        hdvd2
    have hmod : t ≡ 1 [MOD orderOf (q h)] := Nat.ModEq.of_dvd hd ht1
    simpa using (pow_eq_pow_iff_modEq (x := q h) (n := t) (m := 1)).mpr hmod

private lemma cT3_centPAbs_map {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    {Ebar : Subgroup (MulAut R)} {H : Type*} [Group H] (q : H →* MulAut R) (E₀ : Subgroup H)
    (hIp : ∀ h : H, (∃ k : ℕ, h ^ p ^ k = 1) → q h ∈ I)
    (hE₀ : ∀ e, e ∈ Ebar ↔ ∃ x ∈ E₀, q x = e) (h : H) (hh : CentPAbs p E₀ h) :
    GGL45NtCIp p I Ebar (q h) := by
  obtain ⟨hc, hp⟩ := hh
  refine ⟨hIp h hp, ?_, ?_⟩
  · intro e he
    obtain ⟨x, hx, rfl⟩ := (hE₀ e).mp he
    calc q h * q x = q (h * x) := (map_mul q h x).symm
      _ = q (x * h) := by rw [hc x hx]
      _ = q x * q h := map_mul q x h
  · obtain ⟨n, hn⟩ := hp
    exact ⟨n, by rw [← map_pow, hn, map_one]⟩

theorem coreConcl_transfer {p : ℕ} (hp : p.Prime) {R : Type} [Group R] (I : Set (MulAut R))
    (Ebar : Subgroup (MulAut R)) (f : MulAut R) {H : Type*} [Group H] [Finite H]
    (q : H →* MulAut R) (α : H →* H) (hα : ∀ h, q (α h) = f * q h * f⁻¹) (E₀ : Subgroup H)
    (hqinj : ∀ x ∈ E₀, ∀ y ∈ E₀, q x = q y → x = y)
    (hE₀ : ∀ e, e ∈ Ebar ↔ ∃ x ∈ E₀, q x = e)
    (hI : ∀ w ∈ I, ∃ h : H, q h = w) (hIp : ∀ h : H, (∃ k : ℕ, h ^ p ^ k = 1) → q h ∈ I)
    (hcomm : ∀ h : H, (∀ e ∈ E₀, q h * q e = q e * q h) → ∀ e ∈ E₀, h * e = e * h)
    (hcore : ClCoreConcl p E₀ α) :
    ∃ s : ℕ, 2 ≤ s ∧ ∃ (c : ℤ) (k : ℕ), ¬ p ∣ k ∧
      c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s] ∧
      (∀ u v : MulAut R, GGL45NtCIp p I Ebar u → GGL45NtCIp p I Ebar v → u * v = v * u) ∧
      (∀ u : MulAut R, GGL45NtCIp p I Ebar u → u ^ p ^ s = 1 ∧ f * u * f⁻¹ = u ^ c) ∧
      (∀ u : MulAut R, GGL45NtCIp p I Ebar u → ∀ w ∈ I, (∀ e ∈ Ebar, w * e = e * w) →
        w * u = u * w) ∧
      ∃ a₁ a₂ : MulAut R, GGL45NtCIp p I Ebar a₁ ∧ GGL45NtCIp p I Ebar a₂ ∧
        ∀ i j : ℕ, (a₁ ^ p ^ (s - 1)) ^ i * (a₂ ^ p ^ (s - 1)) ^ j = 1 → p ∣ i ∧ p ∣ j := by
  obtain ⟨s, hs, k, hk, hcommute, hpow, hcentral, a₁, a₂, ha₁, ha₂, ha₁E, ha₂E, hindep⟩ := hcore
  have hlift : ∀ u : MulAut R, GGL45NtCIp p I Ebar u → ∃ h : H, q h = u ∧ CentPAbs p E₀ h := by
    intro u hu
    obtain ⟨huI, hucomm, huP⟩ := hu
    obtain ⟨h₀, hqh0⟩ := hI u huI
    have hcomm₀ : ∀ e ∈ E₀, h₀ * e = e * h₀ :=
      hcomm h₀ (fun e he => by
        have h1 := hucomm (q e) ((hE₀ (q e)).mpr ⟨e, he, rfl⟩)
        rwa [← hqh0] at h1)
    obtain ⟨k', hk'⟩ := huP
    have hk'' : q h₀ ^ p ^ k' = 1 := by rwa [← hqh0] at hk'
    obtain ⟨h', ⟨n, hn⟩, ⟨j, hj⟩, hqh'⟩ := exists_pElt_lift hp q (isOfFinOrder_of_finite h₀) hk''
    exact ⟨h', by rw [hqh', hqh0],
      (fun e he => by
        rw [hn]
        exact (show Commute h₀ e from hcomm₀ e he).pow_left n), ⟨j, hj⟩⟩
  refine ⟨s, hs, 1 + (p : ℤ) ^ (s - 1) * k, k, hk, Int.ModEq.refl _, ?_, ?_, ?_, ?_⟩
  · intro u v hu hv
    obtain ⟨x, hqx, hx⟩ := hlift u hu
    obtain ⟨y, hqy, hy⟩ := hlift v hv
    calc u * v = q x * q y := by rw [hqx, hqy]
      _ = q (x * y) := (map_mul q x y).symm
      _ = q (y * x) := by rw [hcommute x y hx hy]
      _ = q y * q x := map_mul q y x
      _ = v * u := by rw [hqy, hqx]
  · intro u hu
    obtain ⟨x, hqx, hx⟩ := hlift u hu
    obtain ⟨hxs, hxα⟩ := hpow x hx
    constructor
    · calc u ^ p ^ s = q x ^ p ^ s := by rw [hqx]
        _ = q (x ^ p ^ s) := (map_pow q x (p ^ s)).symm
        _ = 1 := by rw [hxs, map_one]
    · calc f * u * f⁻¹ = f * q x * f⁻¹ := by rw [hqx]
        _ = q (α x) := (hα x).symm
        _ = q (x ^ (1 + (p : ℤ) ^ (s - 1) * k)) := by rw [hxα]
        _ = (q x) ^ (1 + (p : ℤ) ^ (s - 1) * k) := map_zpow q x _
        _ = u ^ (1 + (p : ℤ) ^ (s - 1) * k) := by rw [hqx]
  · intro u hu w hw hwcomm
    obtain ⟨x, hqx, hx⟩ := hlift u hu
    obtain ⟨h, hqh⟩ := hI w hw
    have hhE : ∀ e ∈ E₀, h * e = e * h :=
      hcomm h (fun e he => by
        have h1 := hwcomm (q e) ((hE₀ (q e)).mpr ⟨e, he, rfl⟩)
        rwa [← hqh] at h1)
    calc w * u = q h * q x := by rw [hqh, hqx]
      _ = q (h * x) := (map_mul q h x).symm
      _ = q (x * h) := by rw [hcentral x hx h hhE]
      _ = q x * q h := map_mul q x h
      _ = u * w := by rw [hqx, hqh]
  · refine ⟨q a₁, q a₂, ?_, ?_, ?_⟩
    · exact cT3_centPAbs_map q E₀ hIp hE₀ a₁ ha₁
    · exact cT3_centPAbs_map q E₀ hIp hE₀ a₂ ha₂
    · intro i j hij
      have hmem : (a₁ ^ p ^ (s - 1)) ^ i * (a₂ ^ p ^ (s - 1)) ^ j ∈ E₀ :=
        E₀.mul_mem (Subgroup.pow_mem E₀ ha₁E i) (Subgroup.pow_mem E₀ ha₂E j)
      have heq : q ((a₁ ^ p ^ (s - 1)) ^ i * (a₂ ^ p ^ (s - 1)) ^ j) = q 1 := by
        simpa only [map_mul, map_pow, map_one] using hij
      exact hindep i j (hqinj _ hmem _ E₀.one_mem heq)

private lemma isElemAbelian_map_mulEquiv {G G' : Type*} [Group G] [Group G'] {p : ℕ}
    {E : Subgroup G} (hE : IsElemAbelian p E) (f : G ≃* G') :
    IsElemAbelian p (E.map (f : G →* G')) := by
  haveI := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, hax⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨z, hz, hbz⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    change (a : G') * b = b * a
    rw [← hax, ← hbz, ← map_mul, ← map_mul]
    exact congrArg (fun w : E => f w) (mul_comm' (⟨x, hx⟩ : E) ⟨z, hz⟩)
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow, hE.2 x hx, map_one]

private lemma ntCIp_map_mulEquiv {R Γ : Type} [Group R] [Group Γ] {p : ℕ}
    (ψ : MulAut R ≃* MulAut Γ) (I : Set (MulAut R)) (Ebar : Subgroup (MulAut R))
    (u : MulAut R) :
    GGL45NtCIp p I Ebar u ↔
      GGL45NtCIp p (ψ '' I) (Ebar.map (ψ : MulAut R →* MulAut Γ)) (ψ u) := by
  unfold GGL45NtCIp
  constructor
  · rintro ⟨huI, hcomm, hpe⟩
    refine ⟨Set.mem_image_of_mem ψ huI, ?_, ?_⟩
    · rintro e' ⟨e, he, rfl⟩
      change ψ u * ψ e = ψ e * ψ u
      rw [← map_mul, ← map_mul, hcomm e he]
    · obtain ⟨k, hk⟩ := hpe
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  · rintro ⟨huI, hcomm, hpe⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Set.mem_image] at huI
      obtain ⟨y, hy, hyu⟩ := huI
      have : y = u := ψ.injective hyu
      simpa [this] using hy
    · intro e he
      exact ψ.injective (by
        simpa only [map_mul] using hcomm (ψ e) ⟨e, he, rfl⟩)
    · obtain ⟨k, hk⟩ := hpe
      exact ⟨k, ψ.injective (by simpa only [map_pow, map_one] using hk)⟩

theorem ntCore_of_mulEquiv {p : ℕ} {R Γ : Type} [Group R] [Group Γ] (Θ : R ≃* Γ)
    (I F : Set (MulAut R))
    (h : GGL45NtCore p Γ ((MulAut.congr Θ) '' I) ((MulAut.congr Θ) '' F)) :
    GGL45NtCore p R I F := by
  intro hRsimple hRnonab Ebar f' hEab hcard hEbarI hf'p hconj hcomm hSat
  haveI : IsSimpleGroup R := hRsimple
  let ψ : MulAut R ≃* MulAut Γ := MulAut.congr Θ
  have hΓsimple : IsSimpleGroup Γ := MulEquiv.isSimpleGroup Θ.symm
  have hΓnonab : ∃ a b : Γ, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hRnonab
    exact ⟨Θ a, Θ b, fun hh => hab (Θ.injective (by simpa only [map_mul] using hh))⟩
  have hEab' : IsElemAbelian p (Ebar.map (ψ : MulAut R →* MulAut Γ)) :=
    isElemAbelian_map_mulEquiv hEab ψ
  have hcard' : p ^ 2 ≤ Nat.card (Ebar.map (ψ : MulAut R →* MulAut Γ)) := by
    rw [Subgroup.card_map_of_injective (K := Ebar) (f := (ψ : MulAut R →* MulAut Γ))
      ψ.injective]
    exact hcard
  have hEbarI' : ∀ e ∈ Ebar.map (ψ : MulAut R →* MulAut Γ), e ∈ ψ '' I := by
    rintro e ⟨e₀, he₀, rfl⟩
    exact Set.mem_image_of_mem ψ (hEbarI e₀ he₀)
  have hf'p' : (ψ f') ^ p = 1 := by
    rw [← map_pow, hf'p, map_one]
  have hconj' : ∃ f ∈ ψ '' F, ∃ u ∈ ψ '' I, orderOf f = p ∧ ψ f' = u * f * u⁻¹ := by
    obtain ⟨f, hfF, u, huI, hford, hf'eq⟩ := hconj
    refine ⟨ψ f, Set.mem_image_of_mem ψ hfF, ψ u, Set.mem_image_of_mem ψ huI, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq ψ f, hford]
    · rw [hf'eq]
      simp only [map_mul, map_inv]
  have hcomm' : ∀ e ∈ Ebar.map (ψ : MulAut R →* MulAut Γ), e * ψ f' = ψ f' * e := by
    rintro e ⟨e₀, he₀, rfl⟩
    change ψ e₀ * ψ f' = ψ f' * ψ e₀
    rw [← map_mul, ← map_mul, hcomm e₀ he₀]
  have hSat' : ∀ r' : Γ, r' ^ p = 1 →
      (∀ e ∈ Ebar.map (ψ : MulAut R →* MulAut Γ), e r' = r') →
      (ψ f') r' = r' →
      MulAut.conj r' ∈ Ebar.map (ψ : MulAut R →* MulAut Γ) := by
    intro r' hr'p hfix hfixf
    let r : R := Θ.symm r'
    have hΘr : Θ r = r' := Θ.apply_symm_apply r'
    have hrp : r ^ p = 1 := by
      apply Θ.injective
      rw [map_pow, hΘr, hr'p, map_one]
    have hfixr : ∀ e ∈ Ebar, e r = r := by
      intro e he
      apply Θ.injective
      have h1 : (MulAut.congr Θ e) r' = r' := hfix (ψ e) ⟨e, he, rfl⟩
      have h2 : Θ (e r) = r' := by
        simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
          using h1
      rw [h2, hΘr]
    have hfixfr : f' r = r := by
      apply Θ.injective
      have h1 : (MulAut.congr Θ f') r' = r' := hfixf
      have h2 : Θ (f' r) = r' := by
        simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
          using h1
      rw [h2, hΘr]
    have hconjr : MulAut.conj r ∈ Ebar := hSat r hrp hfixr hfixfr
    have hconjrr : MulAut.conj r' = ψ (MulAut.conj r) := by
      rw [← hΘr, ← mulAut_congr_conj Θ r]
    rw [hconjrr]
    exact ⟨MulAut.conj r, hconjr, rfl⟩
  obtain ⟨s, hs, c, k, hk, hmod, hcommute, hexp, hcentral, ha⟩ :=
    h hΓsimple hΓnonab (Ebar.map (ψ : MulAut R →* MulAut Γ)) (ψ f') hEab' hcard' hEbarI'
      hf'p' hconj' hcomm' hSat'
  refine ⟨s, hs, c, k, hk, hmod, ?_, ?_, ?_, ?_⟩
  · intro u v hu hv
    exact ψ.injective (by
      rw [map_mul, map_mul]
      exact hcommute (ψ u) (ψ v) ((ntCIp_map_mulEquiv ψ I Ebar u).mp hu)
        ((ntCIp_map_mulEquiv ψ I Ebar v).mp hv))
  · intro u hu
    obtain ⟨h1, h2⟩ := hexp (ψ u) ((ntCIp_map_mulEquiv ψ I Ebar u).mp hu)
    constructor
    · exact ψ.injective (by simpa only [map_pow, map_one] using h1)
    · exact ψ.injective (by simpa only [map_mul, map_inv, map_zpow] using h2)
  · intro u hu w hw hwcomm
    exact ψ.injective (by
      rw [map_mul, map_mul]
      exact hcentral (ψ u) ((ntCIp_map_mulEquiv ψ I Ebar u).mp hu) (ψ w)
        (Set.mem_image_of_mem ψ hw) (by
          rintro e ⟨e₀, he₀, rfl⟩
          change ψ w * ψ e₀ = ψ e₀ * ψ w
          rw [← map_mul, ← map_mul, hwcomm e₀ he₀]))
  · obtain ⟨a₁', a₂', h1', h2', hind'⟩ := ha
    refine ⟨ψ.symm a₁', ψ.symm a₂', ?_, ?_, ?_⟩
    · exact (ntCIp_map_mulEquiv ψ I Ebar (ψ.symm a₁')).mpr (by
        simpa only [ψ.apply_symm_apply] using h1')
    · exact (ntCIp_map_mulEquiv ψ I Ebar (ψ.symm a₂')).mpr (by
        simpa only [ψ.apply_symm_apply] using h2')
    · intro i j hij
      exact hind' i j (by
        have h1 := congrArg ψ hij
        simpa only [map_mul, map_pow, map_one, ψ.apply_symm_apply] using h1)

end CFSG.HardMathSupport.C14Cl
