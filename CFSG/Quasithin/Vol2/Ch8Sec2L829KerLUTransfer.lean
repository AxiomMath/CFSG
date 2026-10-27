module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin.H13

open scoped IsMulCommutative commutatorElement

theorem central_pow_index_eq_one_klu {E : Type} [Group E] [Finite E] [Group.IsPerfect E]
    (A : Subgroup E) [IsMulCommutative A] {z : E} (hz : ∀ g : E, g * z = z * g) (hzA : z ∈ A) :
    z ^ A.index = 1 := by
  classical
  have hT : ∀ g : E, MonoidHom.transfer (MonoidHom.id A) g = 1 := by
    intro g
    have h1 : commutator E ≤ (MonoidHom.transfer (MonoidHom.id A)).ker := by
      refine Subgroup.commutator_le.mpr (fun a _ b _ => ?_)
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    rw [Group.IsPerfect.commutator_eq_top, top_le_iff] at h1
    have hg : g ∈ (MonoidHom.transfer (MonoidHom.id A)).ker := by
      rw [h1]
      exact Subgroup.mem_top g
    exact MonoidHom.mem_ker.mp hg
  have key : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ A → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : Commute (z ^ k) g₀ := Commute.pow_left (show Commute z g₀ from (hz g₀).symm) k
    rw [mul_assoc, hc.eq, inv_mul_cancel_left]
  have hidx := MonoidHom.transfer_eq_pow (MonoidHom.id A) z key
  rw [hT z] at hidx
  have h2 := congrArg Subtype.val hidx
  simpa using h2.symm

theorem isMulCommutative_map_mk_klu {Γ : Type} [Group Γ] (P : Subgroup Γ) [P.Normal]
    (M K : Subgroup Γ) (c : Γ) (hK : ∀ g : Γ, ∀ k ∈ K, ⁅g, k⁆ ∈ P)
    (hdec : ∀ y ∈ M, ∃ j : ℤ, ∃ k ∈ K, y = c ^ j * k) :
    IsMulCommutative (M.map (QuotientGroup.mk' P)) := by
  have hcen : ∀ k ∈ K, ∀ g : Γ ⧸ P, g * QuotientGroup.mk' P k = QuotientGroup.mk' P k * g := by
    intro k hk g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective P g
    rw [← map_mul, ← map_mul]
    apply QuotientGroup.eq.mpr
    have h2 : (g * k)⁻¹ * (k * g) = k⁻¹ * ⁅g⁻¹, k⁆ * k := by
      simp only [commutatorElement_def, inv_inv]
      group
    rw [h2]
    have h3 : ⁅g⁻¹, k⁆ ∈ P := hK g⁻¹ k hk
    have h4 := Subgroup.Normal.conj_mem (inferInstance : P.Normal) _ h3 k⁻¹
    rwa [inv_inv] at h4
  refine ⟨⟨fun a b => ?_⟩⟩
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  obtain ⟨y1, hy1, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y2, hy2, rfl⟩ := Subgroup.mem_map.mp hb
  obtain ⟨j1, k1, hk1, rfl⟩ := hdec y1 hy1
  obtain ⟨j2, k2, hk2, rfl⟩ := hdec y2 hy2
  apply Subtype.ext
  simp only [Subgroup.coe_mul, map_mul, map_zpow]
  have hu : Commute (QuotientGroup.mk' P c ^ j1) (QuotientGroup.mk' P c ^ j2) :=
    Commute.zpow_zpow_self _ j1 j2
  have hA : Commute (QuotientGroup.mk' P c ^ j1)
      (QuotientGroup.mk' P c ^ j2 * QuotientGroup.mk' P k2) :=
    Commute.mul_right hu (hcen k2 hk2 (QuotientGroup.mk' P c ^ j1))
  have hB : Commute (QuotientGroup.mk' P k1)
      (QuotientGroup.mk' P c ^ j2 * QuotientGroup.mk' P k2) :=
    Commute.mul_right (hcen k1 hk1 (QuotientGroup.mk' P c ^ j2)).symm
      (hcen k2 hk2 (QuotientGroup.mk' P k1))
  exact (Commute.mul_left hA hB).eq


theorem mk_central_klu {Γ : Type} [Group Γ] (P : Subgroup Γ) [P.Normal] (K : Subgroup Γ)
    (hK : ∀ g : Γ, ∀ k ∈ K, ⁅g, k⁆ ∈ P) :
    ∀ k ∈ K, ∀ g : Γ ⧸ P, g * QuotientGroup.mk' P k = QuotientGroup.mk' P k * g := by
  intro k hk g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective P g
  rw [← map_mul, ← map_mul]
  apply QuotientGroup.eq.mpr
  have h2 : (g * k)⁻¹ * (k * g) = k⁻¹ * ⁅g⁻¹, k⁆ * k := by
    simp only [commutatorElement_def, inv_inv]
    group
  rw [h2]
  have h3 : ⁅g⁻¹, k⁆ ∈ P := hK g⁻¹ k hk
  have h4 := Subgroup.Normal.conj_mem (inferInstance : P.Normal) _ h3 k⁻¹
  rwa [inv_inv] at h4

theorem map_two_trivial_klu {Γ : Type} [Group Γ] [Finite Γ] (P : Subgroup Γ) [P.Normal]
    (hP : IsPGroup 2 P) {Hs : Type} [Group Hs] [Finite Hs] [IsSimpleGroup Hs]
    (hHs : Nat.card Hs = 60) (Φ : Γ →* Hs) (hΦ : Function.Surjective Φ) :
    ∀ y ∈ P, Φ y = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card Hs := by
    rw [hHs]
    norm_num
  obtain ⟨hh, hhp⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hN : (P.map Φ).Normal := Subgroup.Normal.map inferInstance Φ hΦ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map Φ) with hb | ht
  · intro y hy
    have hmem : Φ y ∈ P.map Φ := Subgroup.mem_map_of_mem Φ hy
    rw [hb] at hmem
    exact Subgroup.mem_bot.mp hmem
  · exfalso
    have hP' : IsPGroup 2 (P.map Φ) := hP.map Φ
    obtain ⟨k, hk⟩ := hP' ⟨hh, by rw [ht]; exact Subgroup.mem_top hh⟩
    have hk' : hh ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd : 3 ∣ 2 ^ k := by
      rw [← hhp]
      exact orderOf_dvd_of_pow_eq_one hk'
    have hd2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega

theorem index_zpowers_klu {Hs : Type} [Group Hs] [Finite Hs] (hHs : Nat.card Hs = 60)
    {p : ℕ} (hp : p = 3 ∨ p = 5) (h : Hs) (hh : orderOf h = p) :
    (Subgroup.zpowers h).index * p = 60 ∧ Nat.Coprime (Subgroup.zpowers h).index p := by
  have hm : (Subgroup.zpowers h).index * p = 60 := by
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers h)
    rw [Nat.card_zpowers, hh, hHs] at h1
    rw [mul_comm]
    exact h1
  refine ⟨hm, ?_⟩
  rcases hp with rfl | rfl
  · have h20 : (Subgroup.zpowers h).index = 20 := by omega
    rw [h20]
    decide
  · have h12 : (Subgroup.zpowers h).index = 12 := by omega
    rw [h12]
    decide

theorem eq_one_of_perfect_ext_klu {Γ : Type} [Group Γ] [Finite Γ] [Group.IsPerfect Γ]
    (P : Subgroup Γ) [P.Normal] (hP : IsPGroup 2 P)
    {Hs : Type} [Group Hs] [Finite Hs] [IsSimpleGroup Hs] (hHs : Nat.card Hs = 60)
    (Φ : Γ →* Hs) (hΦ : Function.Surjective Φ)
    (hcent : ∀ g k : Γ, Φ k = 1 → ⁅g, k⁆ ∈ P)
    {p : ℕ} (hp : p = 3 ∨ p = 5) (x : Γ) (hΦx : Φ x = 1) (hxp : x ^ p = 1) : x = 1 := by
  have hpprime : p.Prime := by
    rcases hp with rfl | rfl
    · exact Nat.prime_three
    · exact Nat.prime_five
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hpdvd : p ∣ Nat.card Hs := by
    rw [hHs]
    rcases hp with rfl | rfl <;> norm_num
  obtain ⟨hh, hhp⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hPker : ∀ y ∈ P, Φ y = 1 := map_two_trivial_klu P hP hHs Φ hΦ
  obtain ⟨c, hc⟩ := hΦ hh
  set M : Subgroup Γ := (Subgroup.zpowers hh).comap Φ with hMdef
  have hdec : ∀ y ∈ M, ∃ j : ℤ, ∃ k ∈ MonoidHom.ker Φ, y = c ^ j * k := by
    intro y hy
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hy)
    refine ⟨j, (c ^ j)⁻¹ * y, ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hc, hj, inv_mul_cancel]
  have hPM : P ≤ M := fun y hy => Subgroup.mem_comap.mpr (by
    rw [hPker y hy]
    exact Subgroup.one_mem _)
  have hxK : x ∈ MonoidHom.ker Φ := MonoidHom.mem_ker.mpr hΦx
  have hxM : x ∈ M := Subgroup.mem_comap.mpr (by
    rw [hΦx]
    exact Subgroup.one_mem _)
  have hcenK : ∀ g k : Γ, k ∈ MonoidHom.ker Φ → ⁅g, k⁆ ∈ P :=
    fun g k hk => hcent g k (MonoidHom.mem_ker.mp hk)
  have hmapC : IsMulCommutative (M.map (QuotientGroup.mk' P)) :=
    isMulCommutative_map_mk_klu P M (MonoidHom.ker Φ) c hcenK hdec
  set Hb : Subgroup (Γ ⧸ P) := M.map (QuotientGroup.mk' P) with hHbdef
  have hz : ∀ g : Γ ⧸ P, g * QuotientGroup.mk' P x = QuotientGroup.mk' P x * g :=
    mk_central_klu P (MonoidHom.ker Φ) hcenK x hxK
  have hzH : QuotientGroup.mk' P x ∈ Hb := Subgroup.mem_map_of_mem _ hxM
  have htr : QuotientGroup.mk' P x ^ Hb.index = 1 :=
    central_pow_index_eq_one_klu Hb hz hzH
  have hcomap : Hb.comap (QuotientGroup.mk' P) = M := by
    rw [hHbdef, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hPM]
  have hidxH : Hb.index = M.index := by
    have h := Subgroup.index_comap_of_surjective Hb (QuotientGroup.mk'_surjective P)
    rw [hcomap] at h
    exact h.symm
  have hidxM : M.index = (Subgroup.zpowers hh).index :=
    Subgroup.index_comap_of_surjective (Subgroup.zpowers hh) hΦ
  have hcop : Nat.Coprime Hb.index p := by
    rw [hidxH, hidxM]
    exact (index_zpowers_klu hHs hp hh hhp).2
  have hzp : QuotientGroup.mk' P x ^ p = 1 := by
    rw [← map_pow, hxp, map_one]
  have hz1 : QuotientGroup.mk' P x = 1 := by
    have h1 := (pow_gcd_eq_one (a := QuotientGroup.mk' P x) (m := Hb.index) (n := p)).mpr
      ⟨htr, hzp⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
  have hxP : x ∈ P := (QuotientGroup.eq_one_iff x).mp hz1
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hcop2 : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hpprime).mpr (by
      rcases hp with rfl | rfl <;> norm_num))
  have hord : orderOf x ∣ Nat.gcd (2 ^ k) p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hxp)
  rw [Nat.Coprime.gcd_eq_one hcop2] at hord
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)

end CFSG.Quasithin.H13
