module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Cent
public import CFSG.LocalAnalysis.StandardType.FS81.RowCent
public import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

theorem exists_mul_eq_of_mem_centralizer_inf_centralizer {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) {y : G}
    (hy : y ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer ({B.b 2} : Set G)) :
    ∃ d ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G),
      ∃ k ∈ K ⊓ Subgroup.centralizer ({B.b 2} : Set G), y = d * k := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({b₀} : Set G)
  let D : Subgroup G := C ⊓ Subgroup.centralizer (K : Set G)
  have hsup : C = K ⊔ D := centralizer_eq_sup_of_recOutTwD5 hstd hB hrec
  obtain ⟨_, hHyp, _⟩ := hstd
  obtain ⟨_, hKC, _, _, _, _, _, _, _, _, _, _⟩ := hHyp
  have hb₂K : B.b 2 ∈ K := hB.2.2 2 (by decide)
  have hcomm : ∀ k ∈ K, ∀ d ∈ D, Commute k d := by
    intro k hk d hd
    exact Subgroup.mem_centralizer_iff.mp hd.2 k hk
  have hyKD : y ∈ K ⊔ D := by rw [← hsup]; exact hy.1
  obtain ⟨k, hkK, d, hdD, hkd⟩ := (mem_sup_of_commute hcomm).mp hyKD
  have hkd' : Commute k d := hcomm k hkK d hdD
  have hdC₂ : d ∈ Subgroup.centralizer ({B.b 2} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hdD.2 (B.b 2) hb₂K).symm
  have hk_eq : k = y * d⁻¹ := by
    rw [← hkd, mul_assoc, mul_inv_cancel, mul_one]
  have hkC₂ : k ∈ Subgroup.centralizer ({B.b 2} : Set G) := by
    rw [hk_eq]
    exact Subgroup.mul_mem _ hy.2 (Subgroup.inv_mem _ hdC₂)
  exact ⟨d, hdD, k, ⟨hkK, hkC₂⟩, hkd.symm.trans hkd'.eq⟩

theorem mem_zpowers_of_mem_inf_centralizer_of_pow_eq_one {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀) {d : G}
    (hd : d ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)) {m : ℕ}
    (hdm : d ^ 3 ^ m = 1) :
    d ∈ Subgroup.zpowers b₀ := by
  classical
  have hout : Subgroup.centralizer ({b₀} : Set G) =
      K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)) :=
    centralizer_eq_sup_of_recOutTwD5 hstd hB hrec
  obtain ⟨_, hHyp, hCanon⟩ := hstd
  obtain ⟨hb₀, hKC, hKn, _, _, hcyc, _, _, hEmax, _, _, _⟩ := hHyp
  obtain ⟨_, hsupEK, _, _, hself⟩ := hCanon
  have hE : IsElemAbelian 3 E := hEmax.2.1
  have hnot9D : ¬ 9 ∣ Nat.card ↥(Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G)) :=
    not_nine_dvd_card_inf_centralizer hb₀ hKC hKn hcyc hE hsupEK hself
      (hB.1 ▸ hfus.1) hout
  set D : Subgroup G := Subgroup.centralizer ({b₀} : Set G) ⊓
    Subgroup.centralizer (K : Set G) with hDdef
  have hb₀D : b₀ ∈ D := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
  let S : Subgroup G := Subgroup.zpowers d ⊔ Subgroup.zpowers b₀
  have hSleD : S ≤ D :=
    sup_le (Subgroup.zpowers_le.mpr hd) (Subgroup.zpowers_le.mpr hb₀D)
  have hSdvd : Nat.card S ∣ Nat.card D := Subgroup.card_dvd_of_le hSleD
  have hcommdb : Commute d b₀ := Subgroup.mem_centralizer_singleton_iff.mp hd.1
  have hPd : IsPGroup 3 (Subgroup.zpowers d) := by
    rw [isPGroup_iff_card_dvd_pow]
    refine ⟨m, ?_⟩
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hdm
  have hPb : IsPGroup 3 (Subgroup.zpowers b₀) := by
    rw [isPGroup_iff_card_dvd_pow]
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers, hb₀]
    exact dvd_rfl
  have hPnorm : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    refine (Subgroup.centralizer_le_normalizer (Subgroup.zpowers b₀ : Set G)) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (hcommdb.zpow_right i).eq.symm
  have hPS : IsPGroup 3 S := by
    rw [show S = Subgroup.zpowers d ⊔ Subgroup.zpowers b₀ from rfl]
    exact IsPGroup.to_sup_of_normal_right' hPd hPb hPnorm
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := @IsPGroup.exists_card_eq 3 S _ hfact _ hPS
  have hnle : n ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ n := by omega
    have h9dvd : 9 ∣ 3 ^ n := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact pow_dvd_pow 3 h2
    exact hnot9D (h9dvd.trans (hn ▸ hSdvd))
  have hSle3 : Nat.card S ≤ 3 := by
    rw [hn]
    calc 3 ^ n ≤ 3 ^ 1 := pow_le_pow_right' (by norm_num) hnle
      _ = 3 := by norm_num
  have hleS : Subgroup.zpowers b₀ ≤ S := by
    rw [show S = Subgroup.zpowers d ⊔ Subgroup.zpowers b₀ from rfl]
    exact le_sup_right
  have h3leS : 3 ≤ Nat.card S := by
    have h := Subgroup.card_le_of_le hleS
    rwa [Nat.card_zpowers, hb₀] at h
  have hS_eq : S = Subgroup.zpowers b₀ :=
    (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers b₀) (K := S) hleS
      (by rw [Nat.card_zpowers, hb₀]; exact hSle3)).symm
  have hdS : d ∈ S := by
    rw [show S = Subgroup.zpowers d ⊔ Subgroup.zpowers b₀ from rfl]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  rwa [hS_eq] at hdS

theorem commutator_mem_gLAPPrimeCoreOf_of_mem_sup {G : Type} [Group G] {p : ℕ}
    {C J : Subgroup G} (hJ : J ≤ C) {q : G} (hq : q ∈ C)
    (hqJ : ∀ x ∈ J, q * x * q⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p C) {w : G}
    (hw : w ∈ J ⊔ GLAPPrimeCoreOf p C) :
    q * w * q⁻¹ * w⁻¹ ∈ GLAPPrimeCoreOf p C := by
  classical
  let O : Subgroup G := GLAPPrimeCoreOf p C
  have hOleC : O ≤ C := Subgroup.map_subtype_le _
  have hOnormal : (O.subgroupOf C).Normal := gLAPPrimeCoreOf_normal p C
  have hconj : ∀ c ∈ C, ∀ o ∈ O, c * o * c⁻¹ ∈ O :=
    fun c hc o ho => (Subgroup.normal_subgroupOf_iff hOleC).mp hOnormal o c ho hc
  let H : Subgroup G :=
    { carrier := {w | w ∈ C ∧ q * w * q⁻¹ * w⁻¹ ∈ O}
      one_mem' := by
        refine ⟨C.one_mem, ?_⟩
        simp
      mul_mem' := by
        intro a b ha hb
        obtain ⟨haC, haO⟩ := ha
        obtain ⟨hbC, hbO⟩ := hb
        refine ⟨C.mul_mem haC hbC, ?_⟩
        have hkey : q * (a * b) * q⁻¹ * (a * b)⁻¹ =
            (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹) * a⁻¹) := by
          group
        rw [hkey]
        exact O.mul_mem haO (hconj a haC _ hbO)
      inv_mem' := by
        intro a ha
        obtain ⟨haC, haO⟩ := ha
        refine ⟨C.inv_mem haC, ?_⟩
        have hkey : q * a⁻¹ * q⁻¹ * (a⁻¹)⁻¹ =
            a⁻¹ * (q * a * q⁻¹ * a⁻¹)⁻¹ * a := by
          group
        rw [hkey]
        simpa only [inv_inv] using hconj a⁻¹ (C.inv_mem haC) _ (O.inv_mem haO) }
  have hJH : J ≤ H := fun x hx => ⟨hJ hx, hqJ x hx⟩
  have hOH : O ≤ H := by
    intro x hx
    refine ⟨hOleC hx, ?_⟩
    exact O.mul_mem (hconj q hq x hx) (O.inv_mem hx)
  exact (sup_le hJH hOH) hw |>.2

end CFSG.StandardType.FrameRoute.FS81

end
