module

public import CFSG.Quasithin.H13.A5SitY
public import CFSG.Quasithin.Background.A1bGroups

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5 (Hstar piQ piQ_surjective piQ_eq_one_iff piQ_eq_iff)

namespace A5Sit

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  (S : A5Sit G T V V₁ V₃ L₁ H)
include S

theorem comm_pCore_of_ne_three (hF956 : A5.StmtF956i) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {a : Hstar H} (ha : a ∈ CFSG.Open.pCore p (Hstar H)) {v : G} (hv : v ∈ V) :
    a * piQ H ⟨v, S.V_le_H hv⟩ = piQ H ⟨v, S.V_le_H hv⟩ * a := by
  have : Fact p.Prime := ⟨hp⟩
  have hVH := S.V_le_H
  by_cases hp2 : p = 2
  · subst hp2
    rw [S.pCore_two_Hstar, Subgroup.mem_bot] at ha
    rw [ha, one_mul, mul_one]
  by_contra hne
  obtain ⟨x, rfl⟩ := piQ_surjective H a
  set b := piQ H ⟨v, hVH hv⟩ with hbdef
  have hb2 : b * b = 1 := by
    rw [hbdef, ← map_mul, piQ_eq_one_iff]
    show v * v ∈ pCoreOf 2 H
    rw [S.sq_eq_one_of_mem_V hv]
    exact Subgroup.one_mem _
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb2
  have hv'I : (x : G)⁻¹ * v * x ∈ conjSub (x : G)⁻¹ V := by
    rw [mem_conjSub, inv_inv]
    simpa [mul_assoc] using hv
  set y : G := v * ((x : G)⁻¹ * v * x) with hydef
  have hyI : y ∈ V ⊔ conjSub (x : G)⁻¹ V :=
    Subgroup.mul_mem _ (le_sup_left (a := V) hv) (le_sup_right (b := conjSub (x : G)⁻¹ V) hv'I)
  have hyH : y ∈ H := H.mul_mem (hVH hv)
    (H.mul_mem (H.mul_mem (H.inv_mem x.2) (hVH hv)) x.2)
  have hπy : piQ H ⟨y, hyH⟩ = b * (piQ H x)⁻¹ * b * piQ H x := by
    rw [hbdef, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [hydef, mul_assoc]
  have hPn : (CFSG.Open.pCore p (Hstar H)).Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hyP : piQ H ⟨y, hyH⟩ ∈ CFSG.Open.pCore p (Hstar H) := by
    rw [hπy]
    have h1 : b * (piQ H x)⁻¹ * b⁻¹ ∈ CFSG.Open.pCore p (Hstar H) :=
      hPn.conj_mem _ (Subgroup.inv_mem _ ha) b
    rw [hbinv] at h1
    exact Subgroup.mul_mem _ h1 ha
  have hy1 : piQ H ⟨y, hyH⟩ ≠ 1 := by
    intro h
    rw [hπy] at h
    apply hne
    have h1 : b * (piQ H x)⁻¹ * b = (piQ H x)⁻¹ := by
      calc b * (piQ H x)⁻¹ * b = b * (piQ H x)⁻¹ * b * piQ H x * (piQ H x)⁻¹ := by group
        _ = (piQ H x)⁻¹ := by rw [h, one_mul]
    have h2 : (piQ H x)⁻¹ * b = b * (piQ H x)⁻¹ := by
      calc (piQ H x)⁻¹ * b = b * (b * (piQ H x)⁻¹ * b) := by
            rw [← mul_assoc, ← mul_assoc, hb2, one_mul]
        _ = b * (piQ H x)⁻¹ := by rw [h1]
    have h3 := congrArg (·⁻¹) h2
    simp only [mul_inv_rev, inv_inv, hbinv] at h3
    exact h3.symm
  have hPp : IsPGroup p (CFSG.Open.pCore p (Hstar H)) := CFSG.LieType.BorelTits.pCore_isPGroup p
  obtain ⟨k, hk⟩ := hPp ⟨_, hyP⟩
  have hk' : piQ H ⟨y, hyH⟩ ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hI : ¬ ∀ z ∈ V ⊔ conjSub (x : G)⁻¹ V, ∃ n : ℕ, z ^ 2 ^ n ∈ pCoreOf 2 H := by
    intro hall
    obtain ⟨n, hn⟩ := hall y hyI
    have h1 : piQ H ⟨y, hyH⟩ ^ 2 ^ n = 1 := by
      rw [← map_pow, piQ_eq_one_iff]
      simpa using hn
    have h2 : orderOf (piQ H ⟨y, hyH⟩) ∣ Nat.gcd (2 ^ n) (p ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hk')
    have h3 : Nat.gcd (2 ^ n) (p ^ k) = 1 :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    rw [h3, Nat.dvd_one, orderOf_eq_one_iff] at h2
    exact hy1 h2
  have hodd : Odd (p ^ k) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hyk : y ^ p ^ k ∈ pCoreOf 2 H := by
    have := (piQ_eq_one_iff (⟨y, hyH⟩ ^ p ^ k)).1 (by rw [map_pow]; exact hk')
    simpa using this
  have hy3 := S.cube_mem_of_odd hF956 x.2 hI hyI hodd hyk
  have h1 : piQ H ⟨y, hyH⟩ ^ 3 = 1 := by
    rw [← map_pow, piQ_eq_one_iff]
    simpa using hy3
  have h2 : orderOf (piQ H ⟨y, hyH⟩) ∣ Nat.gcd 3 (p ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hk')
  have h3 : Nat.gcd 3 (p ^ k) = 1 :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
  rw [h3, Nat.dvd_one, orderOf_eq_one_iff] at h2
  exact hy1 h2

theorem piQ_v_sq {v : G} (hv : v ∈ V) : piQ H ⟨v, S.V_le_H hv⟩ * piQ H ⟨v, S.V_le_H hv⟩ = 1 := by
  rw [← map_mul, piQ_eq_one_iff]
  show v * v ∈ pCoreOf 2 H
  rw [S.sq_eq_one_of_mem_V hv]
  exact Subgroup.one_mem _

theorem comm_pCore_three_of_centralizes {Y : Subgroup G} (SY : A5SitY S Y)
    (h1519 : V ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G)))
    (hA : ∀ r (hr : r ∈ pCoreOf 2 Y), ∀ w ∈ CFSG.Open.pCore 3 (Hstar H),
      piQ H ⟨r, SY.Y_le_H (pCoreOf_le 2 Y hr)⟩ * w =
        w * piQ H ⟨r, SY.Y_le_H (pCoreOf_le 2 Y hr)⟩)
    {a : Hstar H} (ha : a ∈ CFSG.Open.pCore 3 (Hstar H)) {v : G} (hv : v ∈ V) :
    a * piQ H ⟨v, S.V_le_H hv⟩ = piQ H ⟨v, S.V_le_H hv⟩ * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYH := SY.Y_le_H
  set P := CFSG.Open.pCore 3 (Hstar H) with hPdef
  have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal 3
  have hPp : IsPGroup 3 P := CFSG.LieType.BorelTits.pCore_isPGroup 3
  set b := piQ H ⟨v, S.V_le_H hv⟩ with hbdef
  set c := piQ H ⟨SY.c, hYH SY.c_mem⟩ with hcdef
  have hbc : b * c = c * b := S.piQ_V_comm_Y SY hv SY.c_mem
  have hc3 : c ^ 3 = 1 := SY.piQ_c_cube
  have hb2 : b * b = 1 := S.piQ_v_sq hv
  have hAB : ∀ w : ↥P, MulAut.conjNormal c w = w → MulAut.conjNormal b w = w := by
    intro w hw
    have hwc : (w : Hstar H) * c = c * w := by
      have h0 : c * (w : Hstar H) * c⁻¹ = w := by
        have := congrArg Subtype.val hw
        rwa [MulAut.conjNormal_apply] at this
      calc (w : Hstar H) * c = c * w * c⁻¹ * c := by rw [h0]
        _ = c * w := by group
    have hwc_c : Commute (w : Hstar H) c := hwc
    have hcomm_r : ∀ r (hr : r ∈ pCoreOf 2 Y),
        Commute (w : Hstar H) (piQ H ⟨r, hYH (pCoreOf_le 2 Y hr)⟩) :=
      fun r hr => (hA r hr w w.2).symm
    have hwL : ∀ l (hl : l ∈ Y), (w : Hstar H) * piQ H ⟨l, hYH hl⟩ =
        piQ H ⟨l, hYH hl⟩ * w := by
      intro l hl
      rcases SY.decomp l hl with h | h | h
      · exact (hcomm_r l h).eq
      · have e : piQ H ⟨l, hYH hl⟩ =
            c⁻¹ * c⁻¹ * piQ H ⟨_, hYH (pCoreOf_le 2 Y h)⟩ := by
          rw [hcdef, ← map_inv, ← map_mul, ← map_mul]
          congr 1
          apply Subtype.ext
          simp [mul_assoc]
        rw [e]
        exact ((hwc_c.inv_right.mul_right hwc_c.inv_right).mul_right (hcomm_r _ h)).eq
      · have e : piQ H ⟨l, hYH hl⟩ = c⁻¹ * piQ H ⟨_, hYH (pCoreOf_le 2 Y h)⟩ := by
          rw [hcdef, ← map_inv, ← map_mul]
          congr 1
          apply Subtype.ext
          simp
        rw [e]
        exact (hwc_c.inv_right.mul_right (hcomm_r _ h)).eq
    obtain ⟨g, hg⟩ := piQ_surjective H (w : Hstar H)
    have hgN := S.mem_normalizer_Y_of_comm SY g.2 (fun l hl => by
      have := hwL l hl
      rw [← hg] at this
      exact this)
    have hgH1 : (g : G) ∈ H ⊓ Subgroup.normalizer (Y : Set G) := ⟨g.2, hgN⟩
    have hcomm2 : (g : G) * v * (g : G)⁻¹ * v⁻¹ ∈
        pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G)) := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hgH1) v).mp
        (h1519 hv)
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (h1519 hv))
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 (H ⊓ Subgroup.normalizer (Y : Set G)) ⟨_, hcomm2⟩
    have hn' : ((g : G) * v * (g : G)⁻¹ * v⁻¹) ^ 2 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    have hdP : (w : Hstar H) * b * (w : Hstar H)⁻¹ * b⁻¹ ∈ P := by
      have h1 : b * (w : Hstar H)⁻¹ * b⁻¹ ∈ P := hPn.conj_mem _ (P.inv_mem w.2) b
      have := P.mul_mem w.2 h1
      simpa [mul_assoc] using this
    have hd2 : ((w : Hstar H) * b * (w : Hstar H)⁻¹ * b⁻¹) ^ 2 ^ n = 1 := by
      have e : (w : Hstar H) * b * (w : Hstar H)⁻¹ * b⁻¹ = piQ H (g * ⟨v, S.V_le_H hv⟩ *
          g⁻¹ * ⟨v, S.V_le_H hv⟩⁻¹) := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg]
      rw [e, ← map_pow, piQ_eq_one_iff]
      have : ((g * ⟨v, S.V_le_H hv⟩ * g⁻¹ * ⟨v, S.V_le_H hv⟩⁻¹) ^ 2 ^ n : ↥H) = 1 :=
        Subtype.ext (by simpa using hn')
      rw [this]
      exact Subgroup.one_mem _
    obtain ⟨m, hm⟩ := hPp ⟨_, hdP⟩
    have hm' : ((w : Hstar H) * b * (w : Hstar H)⁻¹ * b⁻¹) ^ 3 ^ m = 1 := by
      simpa using congrArg Subtype.val hm
    have hd1 : (w : Hstar H) * b * (w : Hstar H)⁻¹ * b⁻¹ = 1 := by
      have h1 : orderOf ((w : Hstar H) * b * (w : Hstar H)⁻¹ * b⁻¹) ∣ Nat.gcd (2 ^ n) (3 ^ m) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hd2) (orderOf_dvd_of_pow_eq_one hm')
      have h2 : Nat.gcd (2 ^ n) (3 ^ m) = 1 := Nat.Coprime.pow _ _ (by decide)
      rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
      exact h1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have h1 : (w : Hstar H) * b = b * w := by
      calc (w : Hstar H) * b = (w * b * (w : Hstar H)⁻¹ * b⁻¹) * b * w := by group
        _ = b * w := by rw [hd1, one_mul]
    calc b * (w : Hstar H) * b⁻¹ = w * b * b⁻¹ := by rw [h1]
      _ = w := by group
  have hcommAB : ∀ a' ∈ Subgroup.zpowers b, ∀ b' ∈ Subgroup.zpowers c,
      (MulAut.conjNormal a' : MulAut ↥P) * MulAut.conjNormal b' =
        MulAut.conjNormal b' * MulAut.conjNormal a' := by
    intro a' ha' b' hb'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Commute.zpow_zpow hbc i j).eq
  have hZc : IsPGroup 3 (Subgroup.zpowers c) := by
    rintro ⟨y, hy⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨1, Subtype.ext ?_⟩
    show (c ^ j) ^ 3 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm j, zpow_mul, zpow_natCast, hc3, one_zpow]
  have hAres : opResidual 3 (Subgroup.zpowers b) = Subgroup.zpowers b := by
    refine le_antisymm (opResidual_le 3 _) ?_
    rw [Subgroup.zpowers_le]
    refine Subgroup.subset_closure ⟨Subgroup.mem_zpowers b, ?_⟩
    have hb2' : b ^ 2 = 1 := by rw [pow_two]; exact hb2
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hb2') (by decide)
  have hfix : ∀ a' ∈ Subgroup.zpowers b, ∀ x : ↥P,
      (∀ b' ∈ Subgroup.zpowers c, (MulAut.conjNormal b' : MulAut ↥P) x = x) →
        (MulAut.conjNormal a' : MulAut ↥P) x = x := by
    intro a' ha' x hx
    have hbx : (MulAut.conjNormal b : MulAut ↥P) x = x := hAB x (hx c (Subgroup.mem_zpowers c))
    have hle : Subgroup.zpowers b ≤
        (MulAction.stabilizer (MulAut ↥P) x).comap (MulAut.conjNormal (H := P)) :=
      Subgroup.zpowers_le.mpr hbx
    exact hle ha'
  have hρb := thompson_AxB_one hPp (MulAut.conjNormal (H := P)) hcommAB (hZc.map _) hAres hfix b
    (Subgroup.mem_zpowers b)
  have h1 : (MulAut.conjNormal b : MulAut ↥P) ⟨a, ha⟩ = ⟨a, ha⟩ := by rw [hρb]; rfl
  have h2 := congrArg Subtype.val h1
  rw [MulAut.conjNormal_apply] at h2
  calc a * b = (b * a * b⁻¹) * b := by rw [h2]
    _ = b * a := by group

end A5Sit

end CFSG.Quasithin.H13
