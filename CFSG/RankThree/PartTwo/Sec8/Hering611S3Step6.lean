module

import CFSG.LieType.BorelTits.Basic
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
import CFSG.LocalAnalysis.ComponentClassification.CoprimeAutomorphisms
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open scoped Bracket commutatorElement

variable {G : Type*} [Group G] [Finite G]

private theorem s6_conj_mem {S : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G))
    {s : G} (hs : s ∈ S) : g * s * g⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.mp hg s).mp hs

private theorem s6_inv_conj_mem {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) {s : G} (hs : s ∈ S) : g⁻¹ * s * g ∈ S :=
  (Subgroup.mem_normalizer_iff''.mp hg s).mp hs

private theorem s6_comm_conj {U V : Subgroup G} {g y : G}
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgU : ∀ u ∈ U, g⁻¹ * u * g ∈ U)
    (hy : ∀ u ∈ U, ⁅y, u⁆ ∈ V) : ∀ u ∈ U, ⁅g * y * g⁻¹, u⁆ ∈ V := by
  intro u hu
  have e : ⁅g * y * g⁻¹, u⁆ = g * ⁅y, g⁻¹ * u * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact s6_conj_mem hgV (hy _ (hgU u hu))

private theorem s6_comm_mul {U V : Subgroup G} {a b : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G)) (hb : ∀ u ∈ U, ⁅b, u⁆ ∈ V)
    (ha' : ∀ u ∈ U, ⁅a, u⁆ ∈ V) : ∀ u ∈ U, ⁅a * b, u⁆ ∈ V := by
  intro u hu
  have e : ⁅a * b, u⁆ = a * ⁅b, u⁆ * a⁻¹ * ⁅a, u⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact V.mul_mem (s6_conj_mem ha (hb u hu)) (ha' u hu)

private theorem s6_comm_inv {U V : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (V : Set G)) (hy : ∀ u ∈ U, ⁅n, u⁆ ∈ V) :
    ∀ u ∈ U, ⁅n⁻¹, u⁆ ∈ V := by
  intro u hu
  have e : ⁅n⁻¹, u⁆ = n⁻¹ * (⁅n, u⁆)⁻¹ * n := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact s6_inv_conj_mem hn (V.inv_mem (hy u hu))

private theorem s6_conj_mem_centralizer {V : Subgroup G} {m n : G}
    (hm : m ∈ Subgroup.normalizer (V : Set G)) (hn : n ∈ Subgroup.centralizer (V : Set G)) :
    m * n * m⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hc := Subgroup.mem_centralizer_iff.mp hn _ (s6_inv_conj_mem hm hv)
  have e1 : v * (m * n * m⁻¹) = m * ((m⁻¹ * v * m) * n) * m⁻¹ := by group
  have e2 : m * n * m⁻¹ * v = m * (n * (m⁻¹ * v * m)) * m⁻¹ := by group
  rw [e1, e2, hc]

private theorem s6_perfect_map {H Q : Type*} [Group H] [Group.IsPerfect H] [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (f : H →* Q) (h : H) : f h = 1 := by
  by_contra hne
  haveI : Nontrivial f.range :=
    ⟨⟨f h, MonoidHom.mem_range.mpr ⟨h, rfl⟩⟩, 1, fun e => hne (congrArg Subtype.val e)⟩
  haveI : Group.IsPerfect f.range := Group.IsPerfect.range f
  exact Group.IsPerfect.not_isNilpotent (↥f.range) ((hQ.to_subgroup f.range).isNilpotent)

private theorem s6_claimJ (hchar : CFSG.Assembly.IsCharTwoType G) {V : Subgroup G}
    (hV2 : IsPGroup 2 V) (hV1 : V ≠ ⊥) {x : G} (hx : x ∈ Subgroup.centralizer (V : Set G))
    (hxU : ∀ u ∈ CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V : Set G)), x * u = u * x)
    {r : ℕ} (hr : Odd r) (hxr : x ^ r = 1) : x = 1 := by
  set N := Subgroup.centralizer (V : Set G) with hNdef
  set M := Subgroup.normalizer (V : Set G) with hMdef
  set U := CFSG.Assembly.pCoreOf 2 N with hUdef
  set O := CFSG.Assembly.pCoreOf 2 M with hOdef
  have hNM : N ≤ M := Subgroup.centralizer_le_normalizer _
  have hxM : x ∈ M := hNM hx
  have hM2 : CFSG.Assembly.IsTwoLocal M := ⟨V, hV1, hV2, rfl⟩
  have hMN : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N :=
    fun m hm n hn => s6_conj_mem_centralizer hm hn
  have hOM : ∀ m ∈ M, ∀ o ∈ O, m * o * m⁻¹ ∈ O :=
    fun m hm o ho => s6_conj_mem (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm) ho
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hOM' : O ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hON : O ⊓ N ≤ U := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right ?_ hO2.to_inf_left
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    rw [Subgroup.mem_inf] at hh ⊢
    exact ⟨hOM k (hNM hk) h hh.1, hMN k (hNM hk) h hh.2⟩
  have hOU : ∀ o ∈ O, ⁅o, x⁆ ∈ U := by
    intro o ho
    apply hON
    rw [Subgroup.mem_inf]
    have hoM : o ∈ M := hOM' ho
    refine ⟨?_, ?_⟩
    · have h1 : x * o⁻¹ * x⁻¹ ∈ O := hOM x hxM o⁻¹ (O.inv_mem ho)
      have e : ⁅o, x⁆ = o * (x * o⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact O.mul_mem ho h1
    · have h2 : o * x * o⁻¹ ∈ N := hMN o hoM x hx
      have e : ⁅o, x⁆ = o * x * o⁻¹ * x⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact N.mul_mem h2 (N.inv_mem hx)
  have hxU' : ∀ o ∈ O, Commute x ⁅o, x⁆ := fun o ho => hxU _ (hOU o ho)
  have hAO : Subgroup.zpowers x ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.zpowers_le.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hxM)
  have hodd : Odd (orderOf x) := Odd.of_dvd_nat hr (orderOf_dvd_of_pow_eq_one hxr)
  obtain ⟨k0, hk0⟩ := (IsPGroup.iff_card).mp hO2
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers x)) (Nat.card O) := by
    rw [Nat.card_zpowers, hk0]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have hcomm := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_coprime
    hAO hcop
  have hCA : ⁅O, Subgroup.zpowers x⁆ ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.commutator_le]
    intro o ho a ha
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff a x).mp (mem_powers_iff_mem_zpowers.mpr ha)
    have key : ∀ j : ℕ, Commute x ⁅o, x ^ j⁆ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have e : ⁅o, x ^ (j + 1)⁆ = ⁅o, x ^ j⁆ * (x ^ j * ⁅o, x⁆ * (x ^ j)⁻¹) := by
          simp only [commutatorElement_def, pow_succ]; group
        rw [e]
        have hj : Commute x (x ^ j) := (Commute.refl x).pow_right j
        exact ih.mul_right ((hj.mul_right (hxU' o ho)).mul_right hj.inv_right)
    rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
    exact (key k).symm
  have hCC : ⁅⁅O, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro c hc a ha
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff a x).mp (mem_powers_iff_mem_zpowers.mpr ha)
    rw [← hk]
    have hcx : Commute c x := Subgroup.mem_centralizer_singleton_iff.mp (hCA hc)
    exact hcx.pow_right k
  have hOA : ⁅O, Subgroup.zpowers x⁆ = ⊥ := by
    rw [hCC] at hcomm
    exact hcomm.symm
  have hxC : x ∈ Subgroup.centralizer (O : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have h1 : ⁅o, x⁆ ∈ ⁅O, Subgroup.zpowers x⁆ :=
      Subgroup.commutator_mem_commutator ho (Subgroup.mem_zpowers x)
    rw [hOA, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hxO : x ∈ O := hchar M hM2 ⟨hxM, hxC⟩
  obtain ⟨j, hj⟩ := hO2 ⟨x, hxO⟩
  have hxj : x ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have h1 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hxj
  have h2 : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one hxr
  have hcop2 : Nat.Coprime (2 ^ j) r := Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hr)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop2 h1 h2)

private def s6_conjAut {U : Subgroup G} {n : G} (h1 : ∀ u ∈ U, n * u * n⁻¹ ∈ U)
    (h2 : ∀ u ∈ U, n⁻¹ * u * n ∈ U) : MulAut U where
  toFun u := ⟨n * u * n⁻¹, h1 u u.2⟩
  invFun u := ⟨n⁻¹ * u * n, h2 u u.2⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' u v := Subtype.ext (by simp [mul_assoc])

private theorem s6_conjAut_pow {U : Subgroup G} {n : G} (h1 : ∀ u ∈ U, n * u * n⁻¹ ∈ U)
    (h2 : ∀ u ∈ U, n⁻¹ * u * n ∈ U) (k : ℕ) : ∀ u : U,
    (((s6_conjAut h1 h2) ^ k) u : G) = n ^ k * (u : G) * (n ^ k)⁻¹ := by
  induction k with
  | zero => intro u; simp
  | succ k ih =>
    intro u
    rw [pow_succ, MulAut.mul_apply, ih]
    show n ^ k * (n * (u : G) * n⁻¹) * (n ^ k)⁻¹ = n ^ (k + 1) * (u : G) * (n ^ (k + 1))⁻¹
    simp only [pow_succ]
    group

private theorem s6_conjAut_pow_eq_one {U : Subgroup G} {n : G} (h1 : ∀ u ∈ U, n * u * n⁻¹ ∈ U)
    (h2 : ∀ u ∈ U, n⁻¹ * u * n ∈ U) {r : ℕ} (hnr : n ^ r = 1) :
    (s6_conjAut h1 h2) ^ r = 1 := by
  ext u
  rw [s6_conjAut_pow, hnr]
  simp

private theorem s6_claimK (hchar : CFSG.Assembly.IsCharTwoType G) {V : Subgroup G}
    (hV2 : IsPGroup 2 V) (hV1 : V ≠ ⊥) {n : G} (hn : n ∈ Subgroup.centralizer (V : Set G))
    (hnU : ∀ u ∈ CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V : Set G)), ⁅n, u⁆ ∈ V)
    {r : ℕ} (hr : Odd r) (hnr : n ^ r = 1) : n = 1 := by
  set N := Subgroup.centralizer (V : Set G) with hNdef
  set U := CFSG.Assembly.pCoreOf 2 N with hUdef
  have hU2 : IsPGroup 2 U := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hUN : U ≤ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N
  have hNM : N ≤ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _
  have hNU : N ≤ Subgroup.normalizer (U : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
  have hn1 : ∀ u ∈ U, n * u * n⁻¹ ∈ U := fun u hu => s6_conj_mem (hNU hn) hu
  have hn2 : ∀ u ∈ U, n⁻¹ * u * n ∈ U := fun u hu => s6_inv_conj_mem (hNU hn) hu
  have hpow : (s6_conjAut hn1 hn2) ^ r = 1 := s6_conjAut_pow_eq_one hn1 hn2 hnr
  have hVU2 : IsPGroup 2 ↥(V.subgroupOf U) := hU2.to_subgroup (V.subgroupOf U)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hVU2
  have hcop : Nat.Coprime r (Nat.card (V.subgroupOf U)) := by
    rw [hj]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hr)
  have hfixed : ∀ e ∈ V.subgroupOf U, s6_conjAut hn1 hn2 e = e := by
    intro e he
    have heV : (e : G) ∈ V := Subgroup.mem_subgroupOf.mp he
    apply Subtype.ext
    show n * (e : G) * n⁻¹ = (e : G)
    have hc : (e : G) * n = n * (e : G) := Subgroup.mem_centralizer_iff.mp hn _ heV
    rw [← hc, mul_inv_cancel_right]
  have hdisp : ∀ e : U, e⁻¹ * s6_conjAut hn1 hn2 e ∈ V.subgroupOf U := by
    intro e
    rw [Subgroup.mem_subgroupOf]
    show (e : G)⁻¹ * (n * (e : G) * n⁻¹) ∈ V
    have he : (e : G) ∈ Subgroup.normalizer (V : Set G) := hNM (hUN e.2)
    have hw : ⁅n, (e : G)⁆ ∈ V := hnU _ e.2
    have e1 : (e : G)⁻¹ * (n * (e : G) * n⁻¹) = (e : G)⁻¹ * ⁅n, (e : G)⁆ * (e : G) := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact s6_inv_conj_mem he hw
  have hφ1 : s6_conjAut hn1 hn2 = 1 :=
    CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_fixed_displacement
      (V.subgroupOf U) (s6_conjAut hn1 hn2) r hpow hcop hfixed hdisp
  have hcent : ∀ u ∈ U, n * u = u * n := by
    intro u hu
    have h := DFunLike.congr_fun hφ1 ⟨u, hu⟩
    have h' : n * u * n⁻¹ = u := congrArg Subtype.val h
    calc n * u = n * u * n⁻¹ * n := by group
      _ = u * n := by rw [h']
  exact s6_claimJ hchar hV2 hV1 hn hcent hr hnr

private def s6_kerSet (V : Subgroup G) : Subgroup G where
  carrier := {n | n ∈ Subgroup.centralizer (V : Set G) ∧
    ∀ u ∈ CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V : Set G)), ⁅n, u⁆ ∈ V}
  one_mem' := ⟨(Subgroup.centralizer (V : Set G)).one_mem, fun u _ => by
    rw [commutatorElement_one_left]; exact V.one_mem⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨(Subgroup.centralizer (V : Set G)).mul_mem ha.1 hb.1,
      s6_comm_mul (Subgroup.centralizer_le_normalizer _ ha.1) hb.2 ha.2⟩
  inv_mem' := fun {a} ha =>
    ⟨(Subgroup.centralizer (V : Set G)).inv_mem ha.1,
      s6_comm_inv (Subgroup.centralizer_le_normalizer _ ha.1) ha.2⟩

private theorem s6_mem_kerSet {V : Subgroup G} {n : G} :
    n ∈ s6_kerSet V ↔ n ∈ Subgroup.centralizer (V : Set G) ∧
      ∀ u ∈ CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V : Set G)), ⁅n, u⁆ ∈ V :=
  Iff.rfl

private theorem s6_kerSet_le (hchar : CFSG.Assembly.IsCharTwoType G) {V : Subgroup G}
    (hV2 : IsPGroup 2 V) (hV1 : V ≠ ⊥) :
    s6_kerSet V ≤ CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V : Set G)) := by
  set N := Subgroup.centralizer (V : Set G) with hNdef
  have hKN : s6_kerSet V ≤ N := fun n hn => (s6_mem_kerSet.mp hn).1
  have hnormal : ((s6_kerSet V).subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKN]
    intro h k hh hk
    obtain ⟨hhN, hhU⟩ := s6_mem_kerSet.mp hh
    refine s6_mem_kerSet.mpr ⟨s6_conj_mem_centralizer (Subgroup.centralizer_le_normalizer _ hk) hhN,
      ?_⟩
    exact s6_comm_conj (Subgroup.centralizer_le_normalizer _ hk)
      (fun u hu => s6_inv_conj_mem (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N hk) hu) hhU
  have hp : IsPGroup 2 (s6_kerSet V) := by
    rw [IsPGroup.iff_card]
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos.ne') ?_⟩
    intro d hd hdvd
    by_contra hd2
    haveI := Fact.mk hd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' d hdvd
    have hyd : y ^ d = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    have hyd' : (y : G) ^ d = 1 := by
      have := congrArg Subtype.val hyd
      simpa using this
    have hy1 : (y : G) = 1 :=
      s6_claimK hchar hV2 hV1 (s6_mem_kerSet.mp y.2).1 (s6_mem_kerSet.mp y.2).2
        (Nat.Prime.odd_of_ne_two hd hd2) hyd'
    have hy0 : y = 1 := Subtype.ext hy1
    rw [hy0, orderOf_one] at hy
    exact hd.ne_one hy.symm
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 hKN hnormal hp

private def s6_prodSet (X U : Subgroup G) (hUX : ∀ u ∈ U, ∀ x ∈ X, u * x * u⁻¹ ∈ X) :
    Subgroup G where
  carrier := {z | ∃ x ∈ X, ∃ u ∈ U, z = x * u}
  one_mem' := ⟨1, X.one_mem, 1, U.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro a b ⟨x₁, hx₁, u₁, hu₁, rfl⟩ ⟨x₂, hx₂, u₂, hu₂, rfl⟩
    exact ⟨x₁ * (u₁ * x₂ * u₁⁻¹), X.mul_mem hx₁ (hUX u₁ hu₁ x₂ hx₂), u₁ * u₂,
      U.mul_mem hu₁ hu₂, by group⟩
  inv_mem' := by
    rintro a ⟨x, hx, u, hu, rfl⟩
    refine ⟨u⁻¹ * x⁻¹ * u, ?_, u⁻¹, U.inv_mem hu, by group⟩
    have h := hUX u⁻¹ (U.inv_mem hu) x⁻¹ (X.inv_mem hx)
    rwa [inv_inv] at h

theorem step6_normalizes (hchar : CFSG.Assembly.IsCharTwoType G) {V X : Subgroup G}
    (hV2 : IsPGroup 2 V) (hV1 : V ≠ ⊥) (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hX : Group.IsPerfect X) (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hVX : V ≤ X)
    (hUX : ⁅CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V : Set G)), X⁆ ≤ V) :
    ∀ x ∈ Subgroup.centralizer (V : Set G), ∀ y ∈ X, x * y * x⁻¹ ∈ X := by
  intro g hg y hy
  set N := Subgroup.centralizer (V : Set G) with hNdef
  set U := CFSG.Assembly.pCoreOf 2 N with hUdef
  have hgM : g ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hg
  have hNU : N ≤ Subgroup.normalizer (U : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
  have hU2 : IsPGroup 2 U := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hXP : ∀ x ∈ X, ∀ u ∈ U, ⁅x, u⁆ ∈ V := by
    intro x hx u hu
    have h1 : ⁅u, x⁆ ∈ V := hUX (Subgroup.commutator_mem_commutator hu hx)
    have e : ⁅x, u⁆ = ⁅u, x⁆⁻¹ := by rw [commutatorElement_inv]
    rw [e]
    exact V.inv_mem h1
  have hXconj : ∀ u ∈ U, ∀ x ∈ X, u * x * u⁻¹ ∈ X := by
    intro u hu x hx
    have h1 : ⁅u, x⁆ ∈ V := hUX (Subgroup.commutator_mem_commutator hu hx)
    have e : u * x * u⁻¹ = ⁅u, x⁆ * x := by simp only [commutatorElement_def]; group
    rw [e]
    exact X.mul_mem (hVX h1) hx
  set Z := s6_prodSet X U hXconj with hZdef
  have hXZ : X ≤ Z := fun x hx => ⟨x, hx, 1, U.one_mem, by simp⟩
  have hgXZ : ∀ x ∈ X, g * x * g⁻¹ ∈ Z := by
    intro x hx
    have hxM : x ∈ Subgroup.normalizer (V : Set G) := hXN hx
    have hgU : ∀ u ∈ U, g⁻¹ * u * g ∈ U := fun u hu => s6_inv_conj_mem (hNU hg) hu
    have hb : ∀ u ∈ U, ⁅g * x * g⁻¹, u⁆ ∈ V := s6_comm_conj hgM hgU (hXP x hx)
    have hu : x⁻¹ * (g * x * g⁻¹) ∈ s6_kerSet V := by
      refine s6_mem_kerSet.mpr ⟨?_, ?_⟩
      · have h1 : x⁻¹ * g * x ∈ N := by
          have := s6_conj_mem_centralizer (inv_mem hxM) hg
          rwa [inv_inv] at this
        have e : x⁻¹ * (g * x * g⁻¹) = (x⁻¹ * g * x) * g⁻¹ := by group
        rw [e]
        exact N.mul_mem h1 (N.inv_mem hg)
      · exact s6_comm_mul (inv_mem hxM) hb (hXP x⁻¹ (X.inv_mem hx))
    exact ⟨x, hx, x⁻¹ * (g * x * g⁻¹), s6_kerSet_le hchar hV2 hV1 hu, by group⟩
  haveI hK : (X.subgroupOf Z).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hXZ]
    intro h k hh hk
    obtain ⟨x', hx', u, hu, rfl⟩ := hk
    have h1 := hXconj u hu h hh
    have e : x' * u * h * (x' * u)⁻¹ = x' * (u * h * u⁻¹) * x'⁻¹ := by group
    rw [e]
    exact X.mul_mem (X.mul_mem hx' h1) (X.inv_mem hx')
  have hQ : IsPGroup 2 (↥Z ⧸ X.subgroupOf Z) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro w
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨x', hx', u, hu, hzu⟩ := z.2
    have huZ : u ∈ Z := ⟨1, X.one_mem, u, hu, by simp⟩
    have hz : (QuotientGroup.mk z : ↥Z ⧸ X.subgroupOf Z) = QuotientGroup.mk (⟨u, huZ⟩ : ↥Z) := by
      have hzeq : z = ⟨x', hXZ hx'⟩ * ⟨u, huZ⟩ := Subtype.ext (by simp [hzu])
      rw [hzeq, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.mem_subgroupOf.mpr hx'), one_mul]
    obtain ⟨k, hk⟩ := hU2 ⟨u, hu⟩
    have hz1 : (⟨u, huZ⟩ : ↥Z) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨k, ?_⟩
    rw [hz, ← QuotientGroup.mk_pow, hz1, QuotientGroup.mk_one]
  let f : ↥X →* (↥Z ⧸ X.subgroupOf Z) :=
    { toFun := fun x => QuotientGroup.mk ⟨g * (x : G) * g⁻¹, hgXZ x x.2⟩
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).mpr
        rw [Subgroup.mem_subgroupOf]
        simp
      map_mul' := fun a b => by
        rw [← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_mk]
        group }
  have hfy : (QuotientGroup.mk (⟨g * y * g⁻¹, hgXZ y hy⟩ : ↥Z) : ↥Z ⧸ X.subgroupOf Z) = 1 :=
    s6_perfect_map hQ f ⟨y, hy⟩
  have hmem : (⟨g * y * g⁻¹, hgXZ y hy⟩ : ↥Z) ∈ X.subgroupOf Z :=
    (QuotientGroup.eq_one_iff _).mp hfy
  exact Subgroup.mem_subgroupOf.mp hmem

end CFSG.RankThree.PartTwo.Sec8.Hering611
