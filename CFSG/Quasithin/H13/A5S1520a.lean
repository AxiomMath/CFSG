module

public import CFSG.Quasithin.H13.A5L1
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.H13.A5HBar
public import CFSG.Quasithin.H13.A5S1519

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem V_le_H (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz) : V ≤ H :=
  (S.hypF91 h1323 hH).V_le_H

theorem sq_eq_one_of_mem_V {v : G} (hv : v ∈ V) : v * v = 1 := by
  rw [← pow_two]
  exact S.elemAbelian_V.2 v hv

theorem comm_V_L1_mem_Q (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz) {v l : G}
    (hv : v ∈ V) (hl : l ∈ S.L1) : v * l * v⁻¹ * l⁻¹ ∈ pCoreOf 2 H := by
  have h := Subgroup.commutator_mem_commutator hv hl
  rw [S.commutator_V_L1, commutatorElement_def] at h
  exact (S.hypF91 h1323 hH).conjClosure_Vp_le_pCoreOf (le_conjClosure _ _ h)

theorem piQ_V_comm_L1 (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz) {v l : G}
    (hv : v ∈ V) (hl : l ∈ S.L1) :
    piQ H ⟨v, S.V_le_H h1323 hH hv⟩ * piQ H ⟨l, S.L1_le_H hH hl⟩ =
      piQ H ⟨l, S.L1_le_H hH hl⟩ * piQ H ⟨v, S.V_le_H h1323 hH hv⟩ := by
  rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
    ← map_mul, piQ_eq_one_iff]
  exact S.comm_V_L1_mem_Q h1323 hH hv hl

theorem comm_pCore_of_ne_three (h1323 : Input1323Two) (h1326 : Input1326Two)
    (h1336 : Input1336) (hF956 : StmtF956i) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {a : Hstar H} (ha : a ∈ CFSG.Open.pCore p (Hstar H)) {v : G} (hv : v ∈ V) :
    a * piQ H ⟨v, S.V_le_H h1323 hH hv⟩ = piQ H ⟨v, S.V_le_H h1323 hH hv⟩ * a := by
  have : Fact p.Prime := ⟨hp⟩
  have hVH := S.V_le_H h1323 hH
  by_cases hp2 : p = 2
  · subst hp2
    rw [S.pCore_two_Hstar h1323 hH, Subgroup.mem_bot] at ha
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
  have hy3 := S.cube_mem_of_odd h1323 h1326 h1336 hF956 hH hna x.2 hI hyI hodd hyk
  have h1 : piQ H ⟨y, hyH⟩ ^ 3 = 1 := by
    rw [← map_pow, piQ_eq_one_iff]
    simpa using hy3
  have h2 : orderOf (piQ H ⟨y, hyH⟩) ∣ Nat.gcd 3 (p ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hk')
  have h3 : Nat.gcd 3 (p ^ k) = 1 :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
  rw [h3, Nat.dvd_one, orderOf_eq_one_iff] at h2
  exact hy1 h2

theorem mem_normalizer_L1_of_comm {H : Subgroup G} (hH : H ∈ S.Hz) {g : G} (hg : g ∈ H)
    (hcomm : ∀ l (hl : l ∈ S.L1), piQ H ⟨g, hg⟩ * piQ H ⟨l, S.L1_le_H hH hl⟩ =
      piQ H ⟨l, S.L1_le_H hH hl⟩ * piQ H ⟨g, hg⟩) :
    g ∈ Subgroup.normalizer (S.L1 : Set G) := by
  have hL1H := S.L1_le_H hH
  set K := S.L1 ⊔ pCoreOf 2 H
  have key : ∀ h (hh : h ∈ H), (∀ l (hl : l ∈ S.L1), piQ H ⟨h, hh⟩ * piQ H ⟨l, hL1H hl⟩ =
      piQ H ⟨l, hL1H hl⟩ * piQ H ⟨h, hh⟩) → ∀ y ∈ K, h * y * h⁻¹ ∈ K := by
    intro h hh hc y hy
    have hmap : K.map (MulAut.conj h).toMonoidHom ≤ K := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨l, hl, rfl⟩
        have h1 := hc l hl
        rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← map_inv, ← map_inv, ← map_mul,
          ← map_mul, ← map_mul, piQ_eq_one_iff] at h1
        have h2 : (MulAut.conj h).toMonoidHom l =
            (h * l * h⁻¹ * l⁻¹) * l := by
          show h * l * h⁻¹ = _
          group
        rw [h2]
        exact Subgroup.mul_mem _ (le_sup_right (a := S.L1) h1) (le_sup_left (a := S.L1) hl)
      · rintro _ ⟨q, hq, rfl⟩
        exact le_sup_right (a := S.L1)
          ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) q).mp hq)
    exact hmap ⟨y, hy, rfl⟩
  have hginv : ∀ l (hl : l ∈ S.L1), piQ H ⟨g⁻¹, H.inv_mem hg⟩ * piQ H ⟨l, hL1H hl⟩ =
      piQ H ⟨l, hL1H hl⟩ * piQ H ⟨g⁻¹, H.inv_mem hg⟩ := by
    intro l hl
    have := hcomm l hl
    have e : piQ H ⟨g⁻¹, H.inv_mem hg⟩ = (piQ H ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e]
    calc (piQ H ⟨g, hg⟩)⁻¹ * piQ H ⟨l, hL1H hl⟩ =
        (piQ H ⟨g, hg⟩)⁻¹ * (piQ H ⟨l, hL1H hl⟩ * piQ H ⟨g, hg⟩) * (piQ H ⟨g, hg⟩)⁻¹ := by
          group
      _ = (piQ H ⟨g, hg⟩)⁻¹ * (piQ H ⟨g, hg⟩ * piQ H ⟨l, hL1H hl⟩) * (piQ H ⟨g, hg⟩)⁻¹ := by
          rw [this]
      _ = piQ H ⟨l, hL1H hl⟩ * (piQ H ⟨g, hg⟩)⁻¹ := by group
  have hgK : g ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key g hg hcomm y, fun hy => ?_⟩
    have := key g⁻¹ (H.inv_mem hg) hginv _ hy
    simpa [mul_assoc] using this
  exact S.mem_normalizer_L1_of_mem_normalizer_sup hH hgK

theorem comm_pCore_three_of_centralizes (h1323 : Input1323Two)
    (hcon : ∀ H' ∈ S.Hz, ¬ IsElemAbelian 2 (conjClosure S.V3 H') →
      ¬ H' ≤ Subgroup.normalizer (S.L1 : Set G))
    {H : Subgroup G} (hH : H ∈ S.Hz)
    (hA : ∀ r (hr : r ∈ pCoreOf 2 S.L1), ∀ w ∈ CFSG.Open.pCore 3 (Hstar H),
      piQ H ⟨r, S.L1_le_H hH (pCoreOf_le 2 S.L1 hr)⟩ * w =
        w * piQ H ⟨r, S.L1_le_H hH (pCoreOf_le 2 S.L1 hr)⟩)
    {a : Hstar H} (ha : a ∈ CFSG.Open.pCore 3 (Hstar H)) {v : G} (hv : v ∈ V) :
    a * piQ H ⟨v, S.V_le_H h1323 hH hv⟩ = piQ H ⟨v, S.V_le_H h1323 hH hv⟩ * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1H := S.L1_le_H hH
  set P := CFSG.Open.pCore 3 (Hstar H) with hPdef
  have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal 3
  have hPp : IsPGroup 3 P := CFSG.LieType.BorelTits.pCore_isPGroup 3
  set b := piQ H ⟨v, S.V_le_H h1323 hH hv⟩ with hbdef
  set c := piQ H ⟨S.cL1, hL1H S.cL1_mem⟩ with hcdef
  have hbc : b * c = c * b := S.piQ_V_comm_L1 h1323 hH hv S.cL1_mem
  have hc3 : c ^ 3 = 1 := by
    rw [hcdef, ← map_pow, piQ_eq_one_iff]
    have : ((⟨S.cL1, hL1H S.cL1_mem⟩ : ↥H) ^ 3 : ↥H) = 1 := Subtype.ext (by simpa using S.cL1_cube)
    rw [this]
    exact Subgroup.one_mem _
  have hb2 : b * b = 1 := by
    rw [hbdef, ← map_mul, piQ_eq_one_iff]
    show v * v ∈ pCoreOf 2 H
    rw [S.sq_eq_one_of_mem_V hv]
    exact Subgroup.one_mem _
  have hAB : ∀ w : ↥P, MulAut.conjNormal c w = w → MulAut.conjNormal b w = w := by
    intro w hw
    have hwc : (w : Hstar H) * c = c * w := by
      have h0 : c * (w : Hstar H) * c⁻¹ = w := by
        have := congrArg Subtype.val hw
        rwa [MulAut.conjNormal_apply] at this
      calc (w : Hstar H) * c = c * w * c⁻¹ * c := by rw [h0]
        _ = c * w := by group
    have hwc_c : Commute (w : Hstar H) c := hwc
    have hcomm_r : ∀ r (hr : r ∈ pCoreOf 2 S.L1),
        Commute (w : Hstar H) (piQ H ⟨r, hL1H (pCoreOf_le 2 S.L1 hr)⟩) :=
      fun r hr => (hA r hr w w.2).symm
    have hwL : ∀ l (hl : l ∈ S.L1), (w : Hstar H) * piQ H ⟨l, hL1H hl⟩ =
        piQ H ⟨l, hL1H hl⟩ * w := by
      intro l hl
      rcases S.L1_decomp hl with h | h | h
      · exact (hcomm_r l h).eq
      · have e : piQ H ⟨l, hL1H hl⟩ =
            c⁻¹ * c⁻¹ * piQ H ⟨_, hL1H (pCoreOf_le 2 S.L1 h)⟩ := by
          rw [hcdef, ← map_inv, ← map_mul, ← map_mul]
          congr 1
          apply Subtype.ext
          simp [mul_assoc]
        rw [e]
        exact ((hwc_c.inv_right.mul_right hwc_c.inv_right).mul_right (hcomm_r _ h)).eq
      · have e : piQ H ⟨l, hL1H hl⟩ = c⁻¹ * piQ H ⟨_, hL1H (pCoreOf_le 2 S.L1 h)⟩ := by
          rw [hcdef, ← map_inv, ← map_mul]
          congr 1
          apply Subtype.ext
          simp
        rw [e]
        exact (hwc_c.inv_right.mul_right (hcomm_r _ h)).eq
    obtain ⟨g, hg⟩ := piQ_surjective H (w : Hstar H)
    have hgN := S.mem_normalizer_L1_of_comm hH g.2 (fun l hl => by
      have := hwL l hl
      rw [← hg] at this
      exact this)
    have hgH1 : (g : G) ∈ H ⊓ Subgroup.normalizer (S.L1 : Set G) := ⟨g.2, hgN⟩
    have hVO := S.lemma_13_5_19_two h1323 hcon hH
    have hcomm2 : (g : G) * v * (g : G)⁻¹ * v⁻¹ ∈
        pCoreOf 2 (H ⊓ Subgroup.normalizer (S.L1 : Set G)) := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hgH1) v).mp (hVO hv)
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hVO hv))
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 (H ⊓ Subgroup.normalizer (S.L1 : Set G)) ⟨_, hcomm2⟩
    have hn' : ((g : G) * v * (g : G)⁻¹ * v⁻¹) ^ 2 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    have hdP : (w : Hstar H) * b * (w : Hstar H)⁻¹ * b⁻¹ ∈ P := by
      have h1 : b * (w : Hstar H)⁻¹ * b⁻¹ ∈ P := hPn.conj_mem _ (P.inv_mem w.2) b
      have := P.mul_mem w.2 h1
      simpa [mul_assoc] using this
    have hd2 : ((w : Hstar H) * b * (w : Hstar H)⁻¹ * b⁻¹) ^ 2 ^ n = 1 := by
      have e : (w : Hstar H) * b * (w : Hstar H)⁻¹ * b⁻¹ = piQ H (g * ⟨v, S.V_le_H h1323 hH hv⟩ *
          g⁻¹ * ⟨v, S.V_le_H h1323 hH hv⟩⁻¹) := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg]
      rw [e, ← map_pow, piQ_eq_one_iff]
      have : ((g * ⟨v, S.V_le_H h1323 hH hv⟩ * g⁻¹ * ⟨v, S.V_le_H h1323 hH hv⟩⁻¹) ^ 2 ^ n : ↥H) =
          1 := Subtype.ext (by simpa using hn')
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

end Setting

end CFSG.Quasithin.H13.A5
