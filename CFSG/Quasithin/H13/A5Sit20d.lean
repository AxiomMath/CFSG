module

public import CFSG.Quasithin.H13.A5Sit20
public import CFSG.Quasithin.H13.A5Sit20c
public import CFSG.Quasithin.H13.A5S1520d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5 (Hstar piQ piQ_surjective piQ_eq_one_iff caseB_core)
open CFSG.SectionRank.Ccomm

namespace A5Sit

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  (S : A5Sit G T V V₁ V₃ L₁ H)
include S

omit S in
theorem pow_two_pow_of_mem_pCoreOf {Y : Subgroup G} {l : G} (hl : l ∈ pCoreOf 2 Y) :
    ∃ k : ℕ, (⟨l, pCoreOf_le 2 Y hl⟩ : ↥Y) ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Y ⟨l, hl⟩
  exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

theorem hom_trivial_of_c {Y : Subgroup G} (SY : A5SitY S Y) {M : Type*} [Group M]
    (Ψ : ↥Y →* M) (hΨc : Ψ ⟨SY.c, SY.c_mem⟩ = 1) (l : G) (hl : l ∈ Y) : Ψ ⟨l, hl⟩ = 1 := by
  have h2' : ∀ l (hl : l ∈ Y), ∃ k : ℕ, Ψ ⟨l, hl⟩ ^ 2 ^ k = 1 := by
    intro l hl
    rcases SY.decomp _ hl with h | h | h
    · obtain ⟨k, hk⟩ := pow_two_pow_of_mem_pCoreOf h
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    · obtain ⟨k, hk⟩ := pow_two_pow_of_mem_pCoreOf h
      refine ⟨k, ?_⟩
      have e : (⟨_, pCoreOf_le 2 Y h⟩ : ↥Y) =
          ⟨SY.c, SY.c_mem⟩ * ⟨SY.c, SY.c_mem⟩ * ⟨l, hl⟩ := rfl
      have := congrArg Ψ hk
      rw [map_pow, e, map_mul, map_mul, hΨc, one_mul, one_mul, map_one] at this
      exact this
    · obtain ⟨k, hk⟩ := pow_two_pow_of_mem_pCoreOf h
      refine ⟨k, ?_⟩
      have e : (⟨_, pCoreOf_le 2 Y h⟩ : ↥Y) = ⟨SY.c, SY.c_mem⟩ * ⟨l, hl⟩ := rfl
      have := congrArg Ψ hk
      rw [map_pow, e, map_mul, hΨc, one_mul, map_one] at this
      exact this
  have hodd : ∀ y (hy : y ∈ Y), (∃ m, Odd m ∧ y ^ m = 1) → Ψ ⟨y, hy⟩ = 1 := by
    rintro y hy ⟨m, hm, hym⟩
    obtain ⟨k, hk⟩ := h2' y hy
    have h1 : Ψ ⟨y, hy⟩ ^ m = 1 := by
      have : (⟨y, hy⟩ : ↥Y) ^ m = 1 := Subtype.ext (by simpa using hym)
      rw [← map_pow, this, map_one]
    have h3 : orderOf (Ψ ⟨y, hy⟩) ∣ Nat.gcd m (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hk)
    rw [Nat.Coprime.gcd_eq_one ((Nat.coprime_two_right.mpr hm).pow_right k), Nat.dvd_one,
      orderOf_eq_one_iff] at h3
    exact h3
  have hle : oTwoRes Y ≤ (Ψ.ker).map Y.subtype := by
    rw [oTwoRes, Subgroup.closure_le]
    rintro y ⟨hy, m, hm, hym⟩
    exact ⟨⟨y, hy⟩, hodd y hy ⟨m, hm, hym⟩, rfl⟩
  obtain ⟨l', hl', hll⟩ := hle (by rw [SY.oTwoRes_eq]; exact hl)
  subst hll
  exact hl'

theorem exists_c_nontriv {Y : Subgroup G} (SY : A5SitY S Y)
    [(CFSG.Open.pCore 3 (Hstar H)).Normal]
    (X : Subgroup ↥(CFSG.Open.pCore 3 (Hstar H))) [X.Characteristic]
    (hfaith : ∀ α : MulAut ↥(CFSG.Open.pCore 3 (Hstar H)), (orderOf α).Coprime 3 →
      (∀ x ∈ X, x⁻¹ * α x ∈ frattiniIn X) → α = 1)
    (hB : ∃ r, ∃ hr : r ∈ pCoreOf 2 Y, ∃ w ∈ CFSG.Open.pCore 3 (Hstar H),
      piQ H ⟨r, SY.Y_le_H (pCoreOf_le 2 Y hr)⟩ * w ≠
        w * piQ H ⟨r, SY.Y_le_H (pCoreOf_le 2 Y hr)⟩) :
    ∃ x ∈ X, x⁻¹ * MulAut.conjNormal (piQ H ⟨SY.c, SY.Y_le_H SY.c_mem⟩) x ∉
      frattiniIn X := by
  have hYH := SY.Y_le_H
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  let φ : ↥Y →* MulAut ↥(CFSG.Open.pCore 3 (Hstar H)) :=
    MulAut.conjNormal.comp ((piQ H).comp (Subgroup.inclusion hYH))
  have hY := S.hom_trivial_of_c SY ((frattiniAction X).comp φ)
    ((mem_ker_frattiniAction_iff X _).2 hc)
  obtain ⟨r, hr, w, hw, hne⟩ := hB
  have hrL := pCoreOf_le 2 Y hr
  obtain ⟨k, hk⟩ := pow_two_pow_of_mem_pCoreOf hr
  have hα : φ ⟨r, hrL⟩ = 1 := by
    refine hfaith _ ?_ ((mem_ker_frattiniAction_iff X _).1 (hY r hrL))
    have hk' : φ ⟨r, hrL⟩ ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk')
      (Nat.Coprime.pow_left k (by decide))
  apply hne
  have h1 := congrArg (fun α : MulAut ↥(CFSG.Open.pCore 3 (Hstar H)) =>
    ((α ⟨w, hw⟩ : ↥(CFSG.Open.pCore 3 (Hstar H))) : Hstar H)) hα
  simp only [φ, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply] at h1
  have h1' : piQ H ⟨r, hYH hrL⟩ * w * (piQ H ⟨r, hYH hrL⟩)⁻¹ = w := h1
  calc piQ H ⟨r, hYH hrL⟩ * w =
      piQ H ⟨r, hYH hrL⟩ * w * (piQ H ⟨r, hYH hrL⟩)⁻¹ * piQ H ⟨r, hYH hrL⟩ := by group
    _ = w * piQ H ⟨r, hYH hrL⟩ := by rw [h1']

theorem comm_pCore_three_of_not_centralizes {Y : Subgroup G} (SY : A5SitY S Y)
    (hB : ∃ r, ∃ hr : r ∈ pCoreOf 2 Y, ∃ w ∈ CFSG.Open.pCore 3 (Hstar H),
      piQ H ⟨r, SY.Y_le_H (pCoreOf_le 2 Y hr)⟩ * w ≠
        w * piQ H ⟨r, SY.Y_le_H (pCoreOf_le 2 Y hr)⟩)
    {a : Hstar H} (ha : a ∈ CFSG.Open.pCore 3 (Hstar H)) {v : G} (hv : v ∈ V) :
    a * piQ H ⟨v, S.V_le_H hv⟩ = piQ H ⟨v, S.V_le_H hv⟩ * a := by
  have hVH := S.V_le_H
  by_cases hvQ : v ∈ pCoreOf 2 H
  · have : piQ H ⟨v, hVH hv⟩ = 1 := (piQ_eq_one_iff _).2 hvQ
    rw [this, mul_one, one_mul]
  by_contra hab
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPn : (CFSG.Open.pCore 3 (Hstar H)).Normal := CFSG.LieType.BorelTits.pCore_normal 3
  have hPp : IsPGroup 3 (CFSG.Open.pCore 3 (Hstar H)) := CFSG.LieType.BorelTits.pCore_isPGroup 3
  have hnt : Nontrivial ↥(CFSG.Open.pCore 3 (Hstar H)) := by
    refine ⟨⟨⟨a, ha⟩, 1, fun h => hab ?_⟩⟩
    have : a = 1 := congrArg Subtype.val h
    rw [this, one_mul, mul_one]
  obtain ⟨X, hXs, hfaith⟩ := exists_isSupercritical_faithful (by norm_num) hPp
  have := hXs.characteristic
  have hb2 : piQ H ⟨v, hVH hv⟩ * piQ H ⟨v, hVH hv⟩ = 1 := by
    rw [← map_mul, piQ_eq_one_iff]
    show v * v ∈ pCoreOf 2 H
    rw [S.sq_eq_one_of_mem_V hv]
    exact Subgroup.one_mem _
  have hc3 : piQ H ⟨SY.c, SY.Y_le_H SY.c_mem⟩ ^ 3 = 1 := by
    rw [← map_pow, piQ_eq_one_iff]
    have : ((⟨SY.c, SY.Y_le_H SY.c_mem⟩ : ↥H) ^ 3 : ↥H) = 1 :=
      Subtype.ext (by simpa using SY.c_cube)
    rw [this]
    exact Subgroup.one_mem _
  have hbc := S.piQ_V_comm_Y SY hv SY.c_mem
  have hβ : ∃ x ∈ X, x⁻¹ * MulAut.conjNormal (piQ H ⟨v, hVH hv⟩) x ∉ frattiniIn X := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hord : (orderOf (MulAut.conjNormal (H := CFSG.Open.pCore 3 (Hstar H))
        (piQ H ⟨v, hVH hv⟩))).Coprime 3 := by
      have h2 : (MulAut.conjNormal (H := CFSG.Open.pCore 3 (Hstar H)) (piQ H ⟨v, hVH hv⟩)) ^ 2
          = 1 := by
        rw [← map_pow, pow_two, hb2, map_one]
      exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2) (by decide)
    have h1 := hfaith _ hord h
    apply hab
    have h3 := congrArg (fun α : MulAut ↥(CFSG.Open.pCore 3 (Hstar H)) =>
      ((α ⟨a, ha⟩ : ↥(CFSG.Open.pCore 3 (Hstar H))) : Hstar H)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    calc a * piQ H ⟨v, hVH hv⟩ =
        piQ H ⟨v, hVH hv⟩ * a * (piQ H ⟨v, hVH hv⟩)⁻¹ * piQ H ⟨v, hVH hv⟩ := by rw [h3]
      _ = piQ H ⟨v, hVH hv⟩ * a := by group
  exact caseB_core hPp (S.pRank_Hstar_le_two) hXs hb2 hc3 hbc hβ
    (S.exists_c_nontriv SY X hfaith hB)
    (fun x y hx hy hxy hbx hby hx1 hy1 hxy1 hxy2 =>
      S.not_e9_inverted hv hvQ hx hy hxy hbx hby hx1 hy1 hxy1 hxy2)

theorem lemma_13_5_20 (hF956 : A5.StmtF956i) {Y : Subgroup G} (SY : A5SitY S Y)
    (h1519 : V ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G))) {p : ℕ} (hp : p.Prime)
    {a : Hstar H} (ha : a ∈ CFSG.Open.pCore p (Hstar H)) {v : G} (hv : v ∈ V) :
    a * piQ H ⟨v, S.V_le_H hv⟩ = piQ H ⟨v, S.V_le_H hv⟩ * a := by
  by_cases hp3 : p = 3
  · subst hp3
    by_cases hA : ∀ r (hr : r ∈ pCoreOf 2 Y), ∀ w ∈ CFSG.Open.pCore 3 (Hstar H),
        piQ H ⟨r, SY.Y_le_H (pCoreOf_le 2 Y hr)⟩ * w =
          w * piQ H ⟨r, SY.Y_le_H (pCoreOf_le 2 Y hr)⟩
    · exact S.comm_pCore_three_of_centralizes SY h1519 hA ha hv
    · simp only [not_forall, exists_prop] at hA
      exact S.comm_pCore_three_of_not_centralizes SY hA ha hv
  · exact S.comm_pCore_of_ne_three hF956 hp hp3 ha hv

end A5Sit

end CFSG.Quasithin.H13
