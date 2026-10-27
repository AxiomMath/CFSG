module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTwo
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup


private theorem s1614e3_inv_eq_self {T : Type*} [CommGroup T] (hT : ∀ t : T, t ^ 2 = 1)
    (t : T) : t⁻¹ = t := by
  have h := hT t
  rw [pow_two, mul_eq_one_iff_eq_inv] at h
  exact h.symm

private def s1614e3_norm {T : Type*} [CommGroup T] (a : MulAut T) : T →* T where
  toFun t := t * a t * a (a t)
  map_one' := by simp
  map_mul' s t := by
    show s * t * a (s * t) * a (a (s * t)) =
      (s * a s * a (a s)) * (t * a t * a (a t))
    simp only [map_mul]
    ac_rfl

private theorem s1614e3_norm_apply {T : Type*} [CommGroup T] (a : MulAut T) (t : T) :
    s1614e3_norm a t = t * a t * a (a t) := rfl

private theorem s1614e3_norm_mem_fixV {T : Type*} [CommGroup T] {a : MulAut T}
    (ha : a ^ 3 = 1) (t : T) : s1614e3_norm a t ∈ fixV (Subgroup.zpowers a) := by
  rw [mem_fixV_zpowers_iff_apply, s1614e3_norm_apply]
  have h3 : a (a (a t)) = t := by
    have h : (a ^ 3) t = t := by rw [ha]; rfl
    simpa [pow_three', MulAut.mul_apply] using h
  simp only [map_mul, h3]
  ac_rfl

private theorem s1614e3_norm_eq_self {T : Type*} [CommGroup T] (hT : ∀ t : T, t ^ 2 = 1)
    {a : MulAut T} {t : T} (ht : a t = t) : s1614e3_norm a t = t := by
  rw [s1614e3_norm_apply]
  simp only [ht]
  have h2 : t * t = 1 := by rw [← pow_two]; exact hT t
  rw [h2, one_mul]

private theorem s1614e3_norm_idem {T : Type*} [CommGroup T] (hT : ∀ t : T, t ^ 2 = 1)
    {a : MulAut T} (ha : a ^ 3 = 1) (t : T) :
    s1614e3_norm a (s1614e3_norm a t) = s1614e3_norm a t :=
  s1614e3_norm_eq_self hT (mem_fixV_zpowers_iff_apply.mp (s1614e3_norm_mem_fixV ha t))

private theorem s1614e3_norm_smul {T : Type*} [CommGroup T] {a : MulAut T} (ha : a ^ 3 = 1)
    (t : T) : s1614e3_norm a (a t) = s1614e3_norm a t := by
  change a t * a (a t) * a (a (a t)) = t * a t * a (a t)
  have h3 : a (a (a t)) = t := by
    have h : (a ^ 3) t = t := by rw [ha]; rfl
    simpa [pow_three', MulAut.mul_apply] using h
  rw [h3]
  ac_rfl

private theorem s1614e3_map_norm_eq {T : Type*} [CommGroup T] (hT : ∀ t : T, t ^ 2 = 1)
    {a : MulAut T} (ha : a ^ 3 = 1) :
    (⊤ : Subgroup T).map (s1614e3_norm a) = fixV (Subgroup.zpowers a) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, -, rfl⟩
    exact s1614e3_norm_mem_fixV ha x
  · intro hy
    exact ⟨y, Subgroup.mem_top y, s1614e3_norm_eq_self hT (mem_fixV_zpowers_iff_apply.mp hy)⟩

private def s1614e3_psi {T : Type*} [CommGroup T] (a : MulAut T) : T →* T where
  toFun t := t * s1614e3_norm a t
  map_one' := by simp
  map_mul' s t := by
    show s * t * s1614e3_norm a (s * t) =
      (s * s1614e3_norm a s) * (t * s1614e3_norm a t)
    rw [map_mul]
    ac_rfl

private theorem s1614e3_psi_apply {T : Type*} [CommGroup T] (a : MulAut T) (t : T) :
    s1614e3_psi a t = t * s1614e3_norm a t := rfl

private theorem s1614e3_psi_ker_le {T : Type*} [CommGroup T] (hT : ∀ t : T, t ^ 2 = 1)
    {a : MulAut T} (ha : a ^ 3 = 1) : (s1614e3_psi a).ker ≤ fixV (Subgroup.zpowers a) := by
  intro x hx
  rw [MonoidHom.mem_ker, s1614e3_psi_apply] at hx
  have hx' : s1614e3_norm a x = x := by
    have h : s1614e3_norm a x = x⁻¹ := eq_inv_of_mul_eq_one_right hx
    rw [h, s1614e3_inv_eq_self hT x]
  rw [← hx']
  exact s1614e3_norm_mem_fixV ha x

private theorem s1614e3_kpow_apply_of_fixed {T : Type*} [CommGroup T] {k : MulAut T} {x : T}
    (hx : k x = x) (n : ℕ) : (k ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hx, ih]

private theorem s1614e3_e_apply_fixed {T : Type*} [CommGroup T] {κ k : MulAut T} {i j : ℕ}
    {x : T} (hx : k x = x) : (κ ^ i * k ^ j) x = (κ ^ i) x := by
  show (κ ^ i) ((k ^ j) x) = (κ ^ i) x
  rw [s1614e3_kpow_apply_of_fixed hx j]

private theorem s1614e3_t_apply_k {T : Type*} [CommGroup T] {k t : MulAut T} (hk : k ^ 3 = 1)
    (htk : t * k * t⁻¹ = k⁻¹) (x : T) : t (k x) = k (k (t x)) := by
  have hkinv : k⁻¹ = k * k := inv_eq_of_mul_eq_one_right (by rw [← pow_three, hk])
  have h1 : t * k = k⁻¹ * t := by rw [← htk]; group
  calc t (k x) = (t * k) x := rfl
    _ = (k⁻¹ * t) x := by rw [h1]
    _ = k⁻¹ (t x) := rfl
    _ = (k * k) (t x) := by rw [hkinv]
    _ = k (k (t x)) := rfl

private theorem s1614e3_t_apply_k2 {T : Type*} [CommGroup T] {k t : MulAut T} (hk : k ^ 3 = 1)
    (htk : t * k * t⁻¹ = k⁻¹) (x : T) : t (k (k x)) = k (t x) := by
  have h1 : t * k = k⁻¹ * t := by rw [← htk]; group
  have hkinv2 : (k * k)⁻¹ = k :=
    inv_eq_of_mul_eq_one_right (by rw [mul_assoc, ← pow_three, hk])
  have hkk : k⁻¹ * k⁻¹ = k := by rw [← mul_inv_rev, hkinv2]
  have h2 : t * (k * k) = k * t := by
    calc t * (k * k) = (t * k) * k := (mul_assoc t k k).symm
      _ = (k⁻¹ * t) * k := by rw [h1]
      _ = k⁻¹ * (t * k) := mul_assoc k⁻¹ t k
      _ = k⁻¹ * (k⁻¹ * t) := by rw [h1]
      _ = (k⁻¹ * k⁻¹) * t := (mul_assoc k⁻¹ k⁻¹ t).symm
      _ = k * t := by rw [hkk]
  calc t (k (k x)) = (t * (k * k)) x := rfl
    _ = (k * t) x := by rw [h2]
    _ = k (t x) := rfl

private theorem s1614e3_norm_t {T : Type*} [CommGroup T] {k t : MulAut T} (hk : k ^ 3 = 1)
    (htk : t * k * t⁻¹ = k⁻¹) (x : T) :
    t (s1614e3_norm k x) = s1614e3_norm k (t x) := by
  change t (x * k x * k (k x)) = t x * k (t x) * k (k (t x))
  rw [map_mul, map_mul, s1614e3_t_apply_k hk htk x, s1614e3_t_apply_k2 hk htk x]
  ac_rfl

private theorem s1614e3_pow_eq_pow_mod {T : Type*} [CommGroup T] {κ : MulAut T}
    (hκ : κ ^ 3 = 1) (i : ℕ) : κ ^ i = κ ^ (i % 3) := by
  nth_rewrite 1 [← Nat.mod_add_div i 3]
  rw [pow_add, pow_mul, hκ, one_pow, mul_one]

private theorem s1614e3_fixed_of_efixed {T : Type*} [CommGroup T]
    {κ k : MulAut T} (hκ : κ ^ 3 = 1)
    (hfix : ∀ x : T, κ x = x → k x = x → x = 1) {i j : ℕ}
    (hne : ∃ y : T, k y = y ∧ (κ ^ i * k ^ j) y ≠ y) :
    ∀ y : T, k y = y → (κ ^ i * k ^ j) y = y → y = 1 := by
  intro y hy hye
  have hye' : (κ ^ i) y = y := by
    rw [s1614e3_e_apply_fixed hy] at hye
    exact hye
  have h3i : ¬ 3 ∣ i := by
    intro hd
    obtain ⟨m, hm⟩ := hd
    have hki : κ ^ i = 1 := by rw [hm, pow_mul, hκ, one_pow]
    obtain ⟨y0, hy0, hy0ne⟩ := hne
    apply hy0ne
    rw [s1614e3_e_apply_fixed hy0, hki]
    rfl
  have hmod : i % 3 = 1 ∨ i % 3 = 2 := by
    have hlt : i % 3 < 3 := Nat.mod_lt i (by norm_num)
    have hne0 : i % 3 ≠ 0 := fun h0 => h3i (Nat.dvd_of_mod_eq_zero h0)
    omega
  rcases hmod with h1 | h2
  · have hki : κ ^ i = κ := by rw [s1614e3_pow_eq_pow_mod hκ i, h1]; rfl
    rw [hki] at hye'
    exact hfix y hye' hy
  · have hki : κ ^ i = κ ^ 2 := by rw [s1614e3_pow_eq_pow_mod hκ i, h2]
    rw [hki] at hye'
    have hye2 : κ (κ y) = y := hye'
    have h3y : κ (κ (κ y)) = y := by
      have h : (κ ^ 3) y = y := by rw [hκ]; rfl
      simpa [pow_three', MulAut.mul_apply] using h
    have hky : κ y = y := by
      have h1' : κ (κ (κ y)) = κ y := congrArg κ hye2
      rw [← h1', h3y]
    exact hfix y hky hy

theorem s1614e3_row8_core {T : Type} [CommGroup T] [Finite T] (hT : ∀ x : T, x ^ 2 = 1)
    (hrk : rk (⊤ : Subgroup T) = 8) {κ k t : MulAut T} (hκ : κ ^ 3 = 1) (hk : k ^ 3 = 1)
    (hκk : κ * k = k * κ) (htκ : t * κ = κ * t) (htk : t * k * t⁻¹ = k⁻¹) (ht2 : t * t = 1)
    (hfix : ∀ x : T, κ x = x → k x = x → x = 1) {W : Subgroup T}
    (hW : W ≤ fixV (Subgroup.zpowers t)) (hWr : rkIdx W ≤ 3) {e : MulAut T}
    (he : ∃ i j : ℕ, e = κ ^ i * k ^ j) :
    ∃ Z : Subgroup T, Z ≠ ⊥ ∧ Z ≤ W ∧ Z.map e.toMonoidHom = Z := by
  classical
  obtain ⟨i, j, rfl⟩ := he
  have hkT : rk T = 8 := by rw [← rk_top]; exact hrk
  let T1 : Subgroup T := fixV (Subgroup.zpowers k)
  have hmemT1 : ∀ x : T, x ∈ T1 ↔ k x = x := fun x => mem_fixV_zpowers_iff_apply
  let C2 : Subgroup T := (s1614e3_norm k).ker ⊓ fixV (Subgroup.zpowers t)
  let R : Subgroup T := W ⊓ T1
  have hmap_norm : (⊤ : Subgroup T).map (s1614e3_norm k) = T1 :=
    s1614e3_map_norm_eq hT hk
  have hrank_split : rk ↥T1 + rk (s1614e3_norm k).ker = 8 := by
    have h := rk_map_add_rk_inf_ker (s1614e3_norm k) (⊤ : Subgroup T)
    rw [hmap_norm, top_inf_eq, rk_top] at h
    omega
  have hpsimap : W.map (s1614e3_psi k) ≤ C2 := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hxW, rfl⟩ := hy
    refine ⟨?_, ?_⟩
    · change s1614e3_psi k x ∈ (s1614e3_norm k).ker
      rw [MonoidHom.mem_ker]
      rw [s1614e3_psi_apply, map_mul, s1614e3_norm_idem hT hk x, ← pow_two]
      exact hT (s1614e3_norm k x)
    · change s1614e3_psi k x ∈ fixV (Subgroup.zpowers t)
      rw [mem_fixV_zpowers_iff_apply]
      rw [s1614e3_psi_apply, map_mul, s1614e3_norm_t hk htk x]
      have htx : t x = x := mem_fixV_zpowers_iff_apply.mp (hW hxW)
      rw [htx]
  have hstep2 : rk ↥W ≤ rk ↥C2 + rk ↥R := by
    have h1 := rk_map_add_rk_inf_ker (s1614e3_psi k) W
    have h2 : rk ↥(W.map (s1614e3_psi k)) ≤ rk ↥C2 := rk_mono hpsimap
    have h3 : rk ↥(W ⊓ (s1614e3_psi k).ker) ≤ rk ↥R := by
      apply rk_mono
      exact inf_le_inf_left W (show (s1614e3_psi k).ker ≤ T1 from s1614e3_psi_ker_le hT hk)
    omega
  have hmapk_le : C2.map k.toMonoidHom ≤ (s1614e3_norm k).ker := by
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [MonoidHom.mem_ker]
    change s1614e3_norm k (k y) = 1
    rw [s1614e3_norm_smul hk y]
    exact MonoidHom.mem_ker.mp hy.1
  have hdisj : C2 ⊓ C2.map k.toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzC2, hzmap⟩
    change z ∈ C2.map k.toMonoidHom at hzmap
    rw [Subgroup.mem_map] at hzmap
    obtain ⟨y, hyC2, rfl⟩ := hzmap
    have hty : t y = y := mem_fixV_zpowers_iff_apply.mp hyC2.2
    have htz : t (k y) = k y := mem_fixV_zpowers_iff_apply.mp hzC2.2
    have h1 : t (k y) = k (k (t y)) := s1614e3_t_apply_k hk htk y
    rw [hty] at h1
    have hkky : k (k y) = k y := by rw [← h1, htz]
    have hzT1 : k y ∈ T1 := (hmemT1 (k y)).mpr hkky
    have hzker : s1614e3_norm k (k y) = 1 := MonoidHom.mem_ker.mp hzC2.1
    have hzself : s1614e3_norm k (k y) = k y :=
      s1614e3_norm_eq_self hT ((hmemT1 (k y)).mp hzT1)
    have hz1 : k y = 1 := by rw [← hzself]; exact hzker
    exact Subgroup.mem_bot.mpr hz1
  have hstep3 : 2 * rk ↥C2 ≤ rk (s1614e3_norm k).ker := by
    have hsup := rk_sup_add_rk_inf C2 (C2.map k.toMonoidHom)
    have hmap_rk : rk ↥(C2.map k.toMonoidHom) = rk ↥C2 := s16n9b_rk_map k C2
    rw [hdisj, rk_bot, hmap_rk] at hsup
    have hle : rk ↥(C2 ⊔ C2.map k.toMonoidHom) ≤ rk (s1614e3_norm k).ker :=
      rk_mono (sup_le inf_le_left hmapk_le)
    omega
  have hW5 : 5 ≤ rk ↥W := by
    have h := rk_add_rkIdx W
    omega
  have h2R : 2 + rk ↥T1 ≤ 2 * rk ↥R := by omega
  have hek : Commute (κ ^ i * k ^ j) k :=
    Commute.mul_left (Commute.pow_left hκk i) ((Commute.refl k).pow_left j)
  have he3 : (κ ^ i * k ^ j) ^ 3 = 1 := by
    have hc : Commute (κ ^ i) (k ^ j) := (Commute.pow_left hκk i).pow_right j
    rw [hc.mul_pow 3]
    have h1 : (κ ^ i) ^ 3 = 1 := by
      rw [← pow_mul, Nat.mul_comm i 3, pow_mul, hκ, one_pow]
    have h2 : (k ^ j) ^ 3 = 1 := by
      rw [← pow_mul, Nat.mul_comm j 3, pow_mul, hk, one_pow]
    rw [h1, h2, mul_one]
  have he_pres : ∀ x : T, x ∈ T1 → (κ ^ i * k ^ j) x ∈ T1 := by
    intro x hx
    rw [hmemT1] at hx ⊢
    calc k ((κ ^ i * k ^ j) x) = (k * (κ ^ i * k ^ j)) x := rfl
      _ = ((κ ^ i * k ^ j) * k) x := by rw [hek.eq.symm]
      _ = (κ ^ i * k ^ j) (k x) := rfl
      _ = (κ ^ i * k ^ j) x := by rw [hx]
  have heinv_pres : ∀ x : T, x ∈ T1 → (κ ^ i * k ^ j)⁻¹ x ∈ T1 := by
    intro x hx
    rw [hmemT1] at hx ⊢
    have hc : Commute (κ ^ i * k ^ j)⁻¹ k := hek.inv_left
    calc k ((κ ^ i * k ^ j)⁻¹ x) = (k * (κ ^ i * k ^ j)⁻¹) x := rfl
      _ = ((κ ^ i * k ^ j)⁻¹ * k) x := by rw [hc.eq.symm]
      _ = (κ ^ i * k ^ j)⁻¹ (k x) := rfl
      _ = (κ ^ i * k ^ j)⁻¹ x := by rw [hx]
  have hcomap_le : R.comap (κ ^ i * k ^ j).toMonoidHom ≤ T1 := by
    intro z hz
    rw [Subgroup.mem_comap] at hz
    have hzT1 : (κ ^ i * k ^ j) z ∈ T1 := by
      have h := hz
      change (κ ^ i * k ^ j) z ∈ W ⊓ T1 at h
      exact h.2
    have hzz : z = (κ ^ i * k ^ j)⁻¹ ((κ ^ i * k ^ j) z) :=
      (MulEquiv.symm_apply_apply (κ ^ i * k ^ j) z).symm
    rw [hzz]
    exact heinv_pres ((κ ^ i * k ^ j) z) hzT1
  have hcomap_rk : rk ↥(R.comap (κ ^ i * k ^ j).toMonoidHom) = rk ↥R := by
    have heq : R.comap (κ ^ i * k ^ j).toMonoidHom =
        R.map (κ ^ i * k ^ j)⁻¹.toMonoidHom := by
      ext z
      rw [Subgroup.mem_comap, Subgroup.mem_map]
      constructor
      · intro hz
        exact ⟨(κ ^ i * k ^ j) z, hz, MulEquiv.symm_apply_apply (κ ^ i * k ^ j) z⟩
      · rintro ⟨r, hr, hrz⟩
        show (κ ^ i * k ^ j) z ∈ R
        rw [← hrz]
        simpa using hr
    rw [heq, s16n9b_rk_map]
  let Z : Subgroup T := R ⊓ R.comap (κ ^ i * k ^ j).toMonoidHom
  have hZleR : Z ≤ R := inf_le_left
  have hZleW : Z ≤ W := hZleR.trans (show R ≤ W from inf_le_left)
  have hZrk : 2 ≤ rk ↥Z := by
    have hsup := rk_sup_add_rk_inf R (R.comap (κ ^ i * k ^ j).toMonoidHom)
    have hsuple : rk ↥(R ⊔ R.comap (κ ^ i * k ^ j).toMonoidHom) ≤ rk ↥T1 :=
      rk_mono (sup_le (show R ≤ T1 from inf_le_right) hcomap_le)
    rw [hcomap_rk] at hsup
    show 2 ≤ rk ↥(R ⊓ R.comap (κ ^ i * k ^ j).toMonoidHom)
    omega
  have hmape_le : Z.map (κ ^ i * k ^ j).toMonoidHom ≤ Z := by
    rintro y ⟨x, hxZ, rfl⟩
    have hxZ' : x ∈ R ⊓ R.comap (κ ^ i * k ^ j).toMonoidHom := hxZ
    have hxR : x ∈ R := hxZ'.1
    have hxcomap : (κ ^ i * k ^ j) x ∈ R := hxZ'.2
    have hxT1 : x ∈ T1 := by
      have h := hxR
      change x ∈ W ⊓ T1 at h
      exact h.2
    show (κ ^ i * k ^ j) x ∈ R ⊓ R.comap (κ ^ i * k ^ j).toMonoidHom
    refine ⟨hxcomap, ?_⟩
    show (κ ^ i * k ^ j) ((κ ^ i * k ^ j) x) ∈ R
    by_cases htriv : ∀ y : T, y ∈ T1 → (κ ^ i * k ^ j) y = y
    · rw [htriv ((κ ^ i * k ^ j) x) (he_pres x hxT1)]
      exact hxcomap
    · have hne : ∃ y : T, ∃ _ : y ∈ T1, (κ ^ i * k ^ j) y ≠ y := by
        simpa only [not_forall, not_imp] using htriv
      obtain ⟨y0, hy0T1, hy0ne⟩ := hne
      have hA : ∀ y : T, k y = y → (κ ^ i * k ^ j) y = y → y = 1 :=
        s1614e3_fixed_of_efixed hκ hfix ⟨y0, (hmemT1 y0).mp hy0T1, hy0ne⟩
      have hxB : (κ ^ i * k ^ j) x ∈ T1 := he_pres x hxT1
      have heexT1 : (κ ^ i * k ^ j) ((κ ^ i * k ^ j) x) ∈ T1 := he_pres _ hxB
      have hyB : x * (κ ^ i * k ^ j) x * (κ ^ i * k ^ j) ((κ ^ i * k ^ j) x) ∈ T1 :=
        T1.mul_mem (T1.mul_mem hxT1 hxB) heexT1
      have he3x : (κ ^ i * k ^ j) ((κ ^ i * k ^ j) ((κ ^ i * k ^ j) x)) = x := by
        have h : ((κ ^ i * k ^ j) ^ 3) x = x := by rw [he3]; rfl
        simpa [pow_three', MulAut.mul_apply] using h
      have heyB : (κ ^ i * k ^ j)
          (x * (κ ^ i * k ^ j) x * (κ ^ i * k ^ j) ((κ ^ i * k ^ j) x)) =
          x * (κ ^ i * k ^ j) x * (κ ^ i * k ^ j) ((κ ^ i * k ^ j) x) := by
        rw [map_mul, map_mul, he3x]
        ac_rfl
      have hyB1 : x * (κ ^ i * k ^ j) x *
          (κ ^ i * k ^ j) ((κ ^ i * k ^ j) x) = 1 :=
        hA _ ((hmemT1 _).mp hyB) heyB
      have heex : (κ ^ i * k ^ j) ((κ ^ i * k ^ j) x) = (x * (κ ^ i * k ^ j) x)⁻¹ :=
        eq_inv_of_mul_eq_one_right hyB1
      rw [heex]
      exact R.inv_mem (R.mul_mem hxR hxcomap)
  refine ⟨Z, ?_, hZleW, ?_⟩
  · intro hbot
    have h0 : rk ↥Z = 0 := by rw [hbot]; exact rk_bot
    omega
  · exact Subgroup.eq_of_le_of_card_ge hmape_le
      (Subgroup.card_map_of_injective (κ ^ i * k ^ j).injective).ge

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
