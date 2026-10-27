module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.Witness
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.CentralExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {Y : Type} [Group Y] [Finite Y]

private noncomputable def liftQuotientSubgroup (K : Subgroup Y) [K.Normal]
    (H : Subgroup (↥K ⧸ Subgroup.center ↥K)) : Subgroup Y :=
  (H.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map K.subtype

private noncomputable def liftCenter (K : Subgroup Y) : Subgroup Y :=
  (Subgroup.center ↥K).map K.subtype

private noncomputable def conjCenterQuotAut (K : Subgroup Y) [K.Normal]
    (s : Subgroup.normalizer (K : Set Y)) :
    MulAut (↥K ⧸ Subgroup.center ↥K) :=
  QuotientGroup.congr _ _ (K.normalizerMonoidHom s) (Subgroup.map_center_eq _)

private theorem conjCenterQuotAut_mk (K : Subgroup Y) [K.Normal]
    (s : Subgroup.normalizer (K : Set Y)) (x : ↥K) :
    conjCenterQuotAut K s (QuotientGroup.mk x) =
      QuotientGroup.mk (K.normalizerMonoidHom s x) :=
  QuotientGroup.congr_mk _ _ _ _ x

private theorem map_comap_eq_self_of_conjCenterQuotAut (K : Subgroup Y) [K.Normal]
    {H : Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (s : Subgroup.normalizer (K : Set Y))
    (hH : H.map (conjCenterQuotAut K s).toMonoidHom = H) :
    (H.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map
        (K.normalizerMonoidHom s).toMonoidHom =
      H.comap (QuotientGroup.mk' (Subgroup.center ↥K)) := by
  set π : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' _
  have hiff : ∀ y : ↥K, π (K.normalizerMonoidHom s y) ∈ H ↔ π y ∈ H := by
    intro y
    have h1 : conjCenterQuotAut K s (π y) ∈ H ↔ π y ∈ H := by
      have h2 := Subgroup.mem_map_equiv (f := conjCenterQuotAut K s) (K := H)
        (x := conjCenterQuotAut K s (π y))
      rw [hH, MulEquiv.symm_apply_apply] at h2
      exact h2
    have h3 : conjCenterQuotAut K s (π y) = π (K.normalizerMonoidHom s y) := by
      rw [show π y = QuotientGroup.mk y from QuotientGroup.mk'_apply _ _,
        conjCenterQuotAut_mk]
      exact (QuotientGroup.mk'_apply _ _).symm
    rwa [h3] at h1
  ext q
  rw [Subgroup.mem_map_equiv, Subgroup.mem_comap, Subgroup.mem_comap]
  have h2 := hiff ((K.normalizerMonoidHom s).symm q)
  rw [MulEquiv.apply_symm_apply] at h2
  exact h2.symm

private theorem map_subtype_conj_eq_of_map_eq_self (K : Subgroup Y) [K.Normal]
    (s : Subgroup.normalizer (K : Set Y)) {L : Subgroup ↥K}
    (hL : L.map (K.normalizerMonoidHom s).toMonoidHom = L) :
    (L.map K.subtype).map (MulAut.conj (s : Y)).toMonoidHom = L.map K.subtype := by
  have hcomp : (MulAut.conj (s : Y)).toMonoidHom.comp K.subtype =
      K.subtype.comp (K.normalizerMonoidHom s).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
  calc
    (L.map K.subtype).map (MulAut.conj (s : Y)).toMonoidHom =
        L.map ((MulAut.conj (s : Y)).toMonoidHom.comp K.subtype) := by
      rw [Subgroup.map_map]
    _ = L.map (K.subtype.comp (K.normalizerMonoidHom s).toMonoidHom) := by rw [hcomp]
    _ = (L.map (K.normalizerMonoidHom s).toMonoidHom).map K.subtype := by
      rw [Subgroup.map_map]
    _ = L.map K.subtype := by rw [hL]

private theorem map_image_comap_eq_self (K : Subgroup Y) [K.Normal]
    (s : Subgroup.normalizer (K : Set Y)) {U' : Subgroup ↥K}
    (hU' : U'.map (K.normalizerMonoidHom s).toMonoidHom = U') :
    (U'.map (QuotientGroup.mk' (Subgroup.center ↥K))).map
        (conjCenterQuotAut K s).toMonoidHom =
      U'.map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
  have hcomp : (conjCenterQuotAut K s).toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center ↥K)) =
      (QuotientGroup.mk' (Subgroup.center ↥K)).comp
        (K.normalizerMonoidHom s).toMonoidHom := by
    ext x
    change conjCenterQuotAut K s (QuotientGroup.mk' (Subgroup.center ↥K) x) =
      QuotientGroup.mk' (Subgroup.center ↥K) (K.normalizerMonoidHom s x)
    rw [show QuotientGroup.mk' (Subgroup.center ↥K) x = QuotientGroup.mk x from
      QuotientGroup.mk'_apply _ _, conjCenterQuotAut_mk, QuotientGroup.mk'_apply]
  calc
    (U'.map (QuotientGroup.mk' (Subgroup.center ↥K))).map
        (conjCenterQuotAut K s).toMonoidHom =
        U'.map ((conjCenterQuotAut K s).toMonoidHom.comp
          (QuotientGroup.mk' (Subgroup.center ↥K))) := by
      rw [Subgroup.map_map]
    _ = U'.map ((QuotientGroup.mk' (Subgroup.center ↥K)).comp
          (K.normalizerMonoidHom s).toMonoidHom) := by rw [hcomp]
    _ = (U'.map (K.normalizerMonoidHom s).toMonoidHom).map
          (QuotientGroup.mk' (Subgroup.center ↥K)) := by
      rw [Subgroup.map_map]
    _ = U'.map (QuotientGroup.mk' (Subgroup.center ↥K)) := by rw [hU']

private theorem subgroupOf_inf_map_normalizerMonoidHom_eq (K S : Subgroup Y) [K.Normal]
    (s : Subgroup.normalizer (K : Set Y)) (hs : (s : Y) ∈ S) :
    ((S ⊓ K).subgroupOf K).map (K.normalizerMonoidHom s).toMonoidHom =
      (S ⊓ K).subgroupOf K := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro u ⟨v, hv, rfl⟩
    exact ⟨S.mul_mem (S.mul_mem hs hv.1) (S.inv_mem hs),
      (inferInstance : K.Normal).conj_mem (v : Y) hv.2 (s : Y)⟩
  · rw [Subgroup.card_map_of_injective
      (f := (K.normalizerMonoidHom s).toMonoidHom) (K := (S ⊓ K).subgroupOf K)
      (K.normalizerMonoidHom s).injective]

private theorem map_eq_self_of_two_pow_mem {G : Type*} [Group G] [Finite G]
    {X R : Subgroup G} (hRX : R ≤ X) (hR2 : IsPGroup 2 R)
    (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (h3 : ∀ x ∈ X, x ^ 3 ∈ R)
    (φ : MulAut G) (hφ : X.map φ.toMonoidHom = X) :
    R.map φ.toMonoidHom = R := by
  have hmem : ∀ y ∈ X, (∃ n, y ^ 2 ^ n = 1) → y ∈ R := by
    intro y hy ⟨n, hn⟩
    have hnorm : (R.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXR
    let π : X →* (X ⧸ R.subgroupOf X) := QuotientGroup.mk' _
    have hcube : (π ⟨y, hy⟩) ^ 3 = 1 := by
      rw [← map_pow]
      rw [show QuotientGroup.mk' (R.subgroupOf X)
          ((⟨y, hy⟩ : X) ^ 3) = QuotientGroup.mk ((⟨y, hy⟩ : X) ^ 3) from
        QuotientGroup.mk'_apply _ _, QuotientGroup.eq_one_iff]
      exact h3 y hy
    have hpow : (π ⟨y, hy⟩) ^ 2 ^ n = 1 := by
      rw [← map_pow]
      rw [show (⟨y, hy⟩ : X) ^ 2 ^ n = 1 by
        apply Subtype.ext
        exact hn, map_one]
    have hdvd3 : orderOf (π ⟨y, hy⟩) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hcube
    have hdvd2 : orderOf (π ⟨y, hy⟩) ∣ 2 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hpow
    have hcop : (orderOf (π ⟨y, hy⟩)).Coprime (2 ^ n) :=
      (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)).coprime_dvd_left hdvd3
    have hone : orderOf (π ⟨y, hy⟩) = 1 := hcop.eq_one_of_dvd hdvd2
    have hker : (⟨y, hy⟩ : X) ∈ π.ker :=
      MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp hone)
    rw [show π.ker = R.subgroupOf X from QuotientGroup.ker_mk' _,
      Subgroup.mem_subgroupOf] at hker
    exact hker
  have hle : R.map φ.toMonoidHom ≤ R := by
    rintro y ⟨r, hr, rfl⟩
    obtain ⟨n, hn⟩ := IsPGroup.exists_pow_pow_eq_one hR2 (⟨r, hr⟩ : ↥R)
    have hn' : r ^ 2 ^ n = 1 := by
      have := congrArg (fun z : ↥R => (z : G)) hn
      simpa using this
    refine hmem (φ r) ?_ ⟨n, ?_⟩
    · rw [← hφ]
      exact Subgroup.mem_map_of_mem φ.toMonoidHom (hRX hr)
    · rw [← map_pow, hn', map_one]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective φ.injective]

private theorem card_comap_map_eq_mul_card_center (K : Subgroup Y) [K.Normal]
    (H : Subgroup (↥K ⧸ Subgroup.center ↥K)) :
    Nat.card ((H.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map K.subtype) =
      Nat.card H * Nat.card (Subgroup.center ↥K) := by
  rw [Subgroup.card_map_of_injective K.subtype_injective, mul_comm]
  exact QuotientGroup.card_preimage_mk _ (H : Set (↥K ⧸ Subgroup.center ↥K))

private theorem conj_mem_comap_map
    (K : Subgroup Y) [K.Normal]
    {H X : Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (hXH : X ≤ Subgroup.normalizer (H : Set (↥K ⧸ Subgroup.center ↥K)))
    {xk : ↥K} (hxk : xk ∈ X.comap (QuotientGroup.mk' (Subgroup.center ↥K)))
    {r : Y} (hr : r ∈ (H.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map K.subtype) :
    K.subtype xk * r * (K.subtype xk)⁻¹ ∈
      (H.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map K.subtype := by
  obtain ⟨rk, hrk, rfl⟩ := hr
  refine ⟨K.normalizerMonoidHom ⟨xk, Subgroup.le_normalizer xk.2⟩ rk, ?_, ?_⟩
  · refine Subgroup.mem_comap.mpr ?_
    have hmem := (Subgroup.mem_normalizer_iff.mp (hXH hxk))
      (QuotientGroup.mk' (Subgroup.center ↥K) rk)
    have hconj : QuotientGroup.mk' (Subgroup.center ↥K) xk *
        QuotientGroup.mk' (Subgroup.center ↥K) rk *
        (QuotientGroup.mk' (Subgroup.center ↥K) xk)⁻¹ ∈ H :=
      hmem.mp (Subgroup.mem_comap.mp hrk)
    have hψ : xk * rk * xk⁻¹ =
        K.normalizerMonoidHom ⟨xk, Subgroup.le_normalizer xk.2⟩ rk := by
      apply Subtype.ext
      exact (Subgroup.normalizerMonoidHom_apply_apply_coe K
        ⟨xk, Subgroup.le_normalizer xk.2⟩ rk).symm
    have heq : QuotientGroup.mk' (Subgroup.center ↥K)
        (K.normalizerMonoidHom ⟨xk, Subgroup.le_normalizer xk.2⟩ rk) =
        QuotientGroup.mk' (Subgroup.center ↥K) xk *
          QuotientGroup.mk' (Subgroup.center ↥K) rk *
          (QuotientGroup.mk' (Subgroup.center ↥K) xk)⁻¹ := by
      rw [← hψ]
      simp [map_mul, map_inv]
    rwa [heq]
  · exact Subgroup.normalizerMonoidHom_apply_apply_coe K
      ⟨xk, Subgroup.le_normalizer xk.2⟩ rk

private theorem mem_normalizer_comap_map_of_le_normalizer
    (K : Subgroup Y) [K.Normal]
    {H X : Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (hXH : X ≤ Subgroup.normalizer (H : Set (↥K ⧸ Subgroup.center ↥K)))
    {x : Y} (hx : x ∈ (X.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map K.subtype) :
    x ∈ Subgroup.normalizer
      (((H.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map K.subtype) : Set Y) := by
  obtain ⟨xk, hxk, rfl⟩ := hx
  refine Subgroup.mem_normalizer_iff.mpr fun r => ⟨?_, ?_⟩
  · intro hr
    exact conj_mem_comap_map K hXH hxk hr
  · intro hr
    have hx' : xk⁻¹ ∈ X.comap (QuotientGroup.mk' (Subgroup.center ↥K)) :=
      (X.comap (QuotientGroup.mk' (Subgroup.center ↥K))).inv_mem hxk
    have hc := conj_mem_comap_map K hXH hx' hr
    simpa [mul_assoc] using hc

private theorem le_normalizer_liftQuotientSubgroup
    (K S : Subgroup Y) [K.Normal]
    {Ubar : Sylow 2 (↥K ⧸ Subgroup.center ↥K)}
    (hUbar : (Ubar : Subgroup (↥K ⧸ Subgroup.center ↥K)) =
      ((S ⊓ K).subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)))
    {Xbar Rbar : Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (hfix : ∀ φ : MulAut (↥K ⧸ Subgroup.center ↥K),
      (Ubar : Subgroup (↥K ⧸ Subgroup.center ↥K)).map φ.toMonoidHom =
        (Ubar : Subgroup (↥K ⧸ Subgroup.center ↥K)) →
      Xbar.map φ.toMonoidHom = Xbar)
    (hRX : Rbar ≤ Xbar) (hR2 : IsPGroup 2 Rbar)
    (hXnorm : Xbar ≤ Subgroup.normalizer (Rbar : Set (↥K ⧸ Subgroup.center ↥K)))
    (hexp : ∀ x ∈ Xbar, x ^ 3 ∈ Rbar) :
    S ≤ Subgroup.normalizer (liftQuotientSubgroup K Xbar : Set Y) ∧
      S ≤ Subgroup.normalizer (liftQuotientSubgroup K Rbar : Set Y) := by
  have hInv : ∀ s ∈ S, s ∈ Subgroup.normalizer (liftQuotientSubgroup K Xbar : Set Y) ∧
      s ∈ Subgroup.normalizer (liftQuotientSubgroup K Rbar : Set Y) := by
    intro s hs
    let sN : Subgroup.normalizer (K : Set Y) :=
      ⟨s, by rw [Subgroup.normalizer_eq_top K]; exact Subgroup.mem_top s⟩
    have hU' := subgroupOf_inf_map_normalizerMonoidHom_eq K S sN hs
    have hUbar_map : (Ubar : Subgroup (↥K ⧸ Subgroup.center ↥K)).map
        (conjCenterQuotAut K sN).toMonoidHom =
          (Ubar : Subgroup (↥K ⧸ Subgroup.center ↥K)) := by
      rw [hUbar]
      exact map_image_comap_eq_self K sN hU'
    have hXbar : Xbar.map (conjCenterQuotAut K sN).toMonoidHom = Xbar := hfix _ hUbar_map
    have hL : (Xbar.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map
        (K.normalizerMonoidHom sN).toMonoidHom =
          Xbar.comap (QuotientGroup.mk' (Subgroup.center ↥K)) :=
      map_comap_eq_self_of_conjCenterQuotAut K sN hXbar
    have hXmap : (liftQuotientSubgroup K Xbar).map (MulAut.conj s).toMonoidHom =
        liftQuotientSubgroup K Xbar := by
      change Subgroup.map (MulAut.conj s).toMonoidHom
        (Subgroup.map K.subtype
          (Subgroup.comap (QuotientGroup.mk' (Subgroup.center ↥K)) Xbar)) =
          Subgroup.map K.subtype
            (Subgroup.comap (QuotientGroup.mk' (Subgroup.center ↥K)) Xbar)
      exact map_subtype_conj_eq_of_map_eq_self K sN hL
    have hRbar : Rbar.map (conjCenterQuotAut K sN).toMonoidHom = Rbar :=
      map_eq_self_of_two_pow_mem hRX hR2 hXnorm hexp _ hXbar
    have hLr : (Rbar.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map
        (K.normalizerMonoidHom sN).toMonoidHom =
          Rbar.comap (QuotientGroup.mk' (Subgroup.center ↥K)) :=
      map_comap_eq_self_of_conjCenterQuotAut K sN hRbar
    have hRmap : (liftQuotientSubgroup K Rbar).map (MulAut.conj s).toMonoidHom =
        liftQuotientSubgroup K Rbar := by
      change Subgroup.map (MulAut.conj s).toMonoidHom
        (Subgroup.map K.subtype
          (Subgroup.comap (QuotientGroup.mk' (Subgroup.center ↥K)) Rbar)) =
          Subgroup.map K.subtype
            (Subgroup.comap (QuotientGroup.mk' (Subgroup.center ↥K)) Rbar)
      exact map_subtype_conj_eq_of_map_eq_self K sN hLr
    exact ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr hXmap,
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hRmap⟩
  exact ⟨fun s hs => (hInv s hs).1, fun s hs => (hInv s hs).2⟩

private theorem lift_basic_hypotheses
    (K : Subgroup Y) [K.Normal] (hodd : Odd (Nat.card (Subgroup.center ↥K)))
    {Xbar Rbar : Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (hRX : Rbar ≤ Xbar)
    (hXnorm : Xbar ≤ Subgroup.normalizer (Rbar : Set (↥K ⧸ Subgroup.center ↥K))) :
    liftQuotientSubgroup K Rbar ≤ liftQuotientSubgroup K Xbar ∧
      liftQuotientSubgroup K Xbar ≤
        Subgroup.normalizer (liftQuotientSubgroup K Rbar : Set Y) ∧
      liftCenter K ≤ liftQuotientSubgroup K Rbar ∧
      (∀ z ∈ liftCenter K, ∀ x ∈ liftQuotientSubgroup K Xbar, z * x = x * z) ∧
      Odd (Nat.card (liftCenter K)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change Subgroup.map K.subtype
        (Subgroup.comap (QuotientGroup.mk' (Subgroup.center ↥K)) Rbar) ≤
      Subgroup.map K.subtype
        (Subgroup.comap (QuotientGroup.mk' (Subgroup.center ↥K)) Xbar)
    exact Subgroup.map_mono (Subgroup.comap_mono hRX)
  · intro x hx
    exact mem_normalizer_comap_map_of_le_normalizer K hXnorm hx
  · intro z hz
    change z ∈ (Subgroup.center ↥K).map K.subtype at hz
    obtain ⟨zk, hzk, rfl⟩ := hz
    refine ⟨zk, Subgroup.mem_comap.mpr ?_, rfl⟩
    have hzk1 : (QuotientGroup.mk' (Subgroup.center ↥K)) zk = 1 := by
      rw [show QuotientGroup.mk' (Subgroup.center ↥K) zk = QuotientGroup.mk zk from
        QuotientGroup.mk'_apply _ _, QuotientGroup.eq_one_iff]
      exact hzk
    rw [hzk1]
    exact Rbar.one_mem
  · intro z hz x hx
    change z ∈ (Subgroup.center ↥K).map K.subtype at hz
    change x ∈ (Xbar.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map K.subtype at hx
    obtain ⟨zk, hzk, rfl⟩ := hz
    obtain ⟨xk, hxk, rfl⟩ := hx
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp hzk xk).symm
  · change Odd (Nat.card ((Subgroup.center ↥K).map K.subtype))
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hodd

private theorem lift_power_hypotheses
    (K : Subgroup Y) [K.Normal]
    {Xbar Rbar : Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (hR2 : IsPGroup 2 Rbar)
    (hexp : ∀ x ∈ Xbar, x ^ 3 ∈ Rbar)
    (hcomm : ∀ x ∈ Xbar, ∀ y ∈ Xbar, x * y * x⁻¹ * y⁻¹ ∈ Rbar)
    (hcard : 9 * Nat.card Rbar ≤ Nat.card Xbar) :
    (∀ r ∈ liftQuotientSubgroup K Rbar, ∃ n : ℕ, r ^ 2 ^ n ∈ liftCenter K) ∧
    (∀ x ∈ liftQuotientSubgroup K Xbar, x ^ 3 ∈ liftQuotientSubgroup K Rbar) ∧
    (∀ x ∈ liftQuotientSubgroup K Xbar, ∀ y ∈ liftQuotientSubgroup K Xbar,
      x * y * x⁻¹ * y⁻¹ ∈ liftQuotientSubgroup K Rbar) ∧
    9 * Nat.card (liftQuotientSubgroup K Rbar) ≤
      Nat.card (liftQuotientSubgroup K Xbar) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    change r ∈ (Rbar.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map K.subtype at hr
    obtain ⟨rk, hrk, rfl⟩ := hr
    obtain ⟨n, hn⟩ := IsPGroup.exists_pow_pow_eq_one hR2
      (⟨QuotientGroup.mk' (Subgroup.center ↥K) rk, hrk⟩ : ↥Rbar)
    have hn' : (QuotientGroup.mk' (Subgroup.center ↥K) rk) ^ 2 ^ n = 1 := by
      have := congrArg (fun z : ↥Rbar => (z : ↥K ⧸ Subgroup.center ↥K)) hn
      simpa using this
    refine ⟨n, ⟨rk ^ 2 ^ n, ?_, by rw [map_pow]⟩⟩
    have hker : rk ^ 2 ^ n ∈ (QuotientGroup.mk' (Subgroup.center ↥K)).ker := by
      rw [MonoidHom.mem_ker, map_pow, hn']
    rwa [QuotientGroup.ker_mk'] at hker
  · intro x hx
    change x ∈ (Xbar.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map K.subtype at hx
    obtain ⟨xk, hxk, rfl⟩ := hx
    refine ⟨xk ^ 3, Subgroup.mem_comap.mpr ?_, by rw [map_pow]⟩
    rw [map_pow (QuotientGroup.mk' (Subgroup.center ↥K)) xk 3]
    exact hexp _ hxk
  · intro x hx y hy
    change x ∈ (Xbar.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map K.subtype at hx
    change y ∈ (Xbar.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map K.subtype at hy
    obtain ⟨xk, hxk, rfl⟩ := hx
    obtain ⟨yk, hyk, rfl⟩ := hy
    refine ⟨xk * yk * xk⁻¹ * yk⁻¹, Subgroup.mem_comap.mpr ?_, ?_⟩
    · simp only [map_mul, map_inv]
      exact hcomm _ hxk _ hyk
    · rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  · change 9 * Nat.card ((Rbar.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map
        K.subtype) ≤ Nat.card ((Xbar.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map
        K.subtype)
    rw [card_comap_map_eq_mul_card_center K Rbar,
      card_comap_map_eq_mul_card_center K Xbar]
    calc
      9 * (Nat.card Rbar * Nat.card (Subgroup.center ↥K)) =
          (9 * Nat.card Rbar) * Nat.card (Subgroup.center ↥K) := by ring
      _ ≤ Nat.card Xbar * Nat.card (Subgroup.center ↥K) :=
        Nat.mul_le_mul_right _ hcard

theorem exists_permutes_of_permWitness {K : Subgroup Y} (hK : K.Normal)
    (hodd : Odd (Nat.card (Subgroup.center ↥K)))
    (hW : PermWitness (↥K ⧸ Subgroup.center ↥K)) {S : Subgroup Y}
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ Permutes E S := by
  classical
  letI : K.Normal := hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U' : Subgroup ↥K := (S ⊓ K).subgroupOf K
  let UK : Sylow 2 ↥K := (hS.inf_normal (N := K) le_top (hK.subgroupOf ⊤)).toSylow
  let Ubar : Sylow 2 (↥K ⧸ Subgroup.center ↥K) :=
    UK.mapSurjective (QuotientGroup.mk'_surjective _)
  have hUK : (UK : Subgroup ↥K) = U' := CFSG.Quasithin.IsSylowIn.coe_toSylow _
  have hUbar : (Ubar : Subgroup (↥K ⧸ Subgroup.center ↥K)) = U'.map
      (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    rw [show Ubar = UK.mapSurjective (QuotientGroup.mk'_surjective _) from rfl,
      Sylow.coe_mapSurjective, hUK]
  obtain ⟨Xbar, Rbar, hfix, hRU, hRX, hXnorm, hR2, hexp, hcomm, hcard⟩ := hW Ubar
  have hInv := le_normalizer_liftQuotientSubgroup K S hUbar hfix hRX hR2 hXnorm hexp
  have hbasic := lift_basic_hypotheses K hodd hRX hXnorm
  have hpow := lift_power_hypotheses K hR2 hexp hcomm hcard
  obtain ⟨hRX', hXR, hZR, hZc, hZodd⟩ := hbasic
  obtain ⟨hR2', hexp', hcomm', hcard'⟩ := hpow
  obtain ⟨E, hEX, hEne, hE3, hEexp, hEcyc, hperm⟩ :=
    exists_permutes_of_centralExt (S := S) (X := liftQuotientSubgroup K Xbar)
      (R₀ := liftQuotientSubgroup K Rbar) (Z := liftCenter K)
      hS hInv.1 hInv.2 hRX' hXR hZR hZc hZodd hR2' hexp' hcomm' hcard'
  exact ⟨E, hEX.trans (Subgroup.map_subtype_le (H := K) (K := Xbar.comap
    (QuotientGroup.mk' (Subgroup.center ↥K)))), hEne, hE3, hEexp, hEcyc, hperm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
