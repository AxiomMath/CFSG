module

public import CFSG.RankThree.PartOne.Q1327T.Item7U5
public import CFSG.RankThree.PartOne.Q1327T.Item7U3
public import CFSG.RankThree.PartOne.FOC.SU5Cen
public import CFSG.RankThree.PartOne.Q1327C.BU5Ab
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.RankThree.PartOne.Q1327T

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
  CFSG.Assembly.LowTwoRank

section Center

variable {Q : Type} [Group Q] [Finite Q]

theorem card_center_dvd_multiplier
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hqs : CFSG.IsQuasisimple Q) {t : StatedLieTag} {n f : ℕ}
    (hm : Models.LieModel (Q ⧸ Subgroup.center Q) t n 2 f) :
    Nat.card (Subgroup.center Q) ∣ Nat.card (Blueprint.Multiplier.generic t n 2 f ×
      Blueprint.Multiplier.exceptional t n 2 f) := by
  obtain ⟨hperfT, hcard⟩ := card_hopfMultiplier_of_model hGA hm
  have hdvd := card_ker_dvd_card_hopfMultiplier hperfT hqs.1 (QuotientGroup.mk' (Subgroup.center Q))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le
  rw [hcard, QuotientGroup.ker_mk'] at hdvd
  exact hdvd

theorem card_sup_le_of_central (Ē : Subgroup Q) :
    Nat.card ↥(Ē ⊔ Subgroup.center Q) ≤ Nat.card Ē * Nat.card (Subgroup.center Q) := by
  have hcomm : ∀ (a : Ē) (b : Subgroup.center Q),
      Commute (Ē.subtype a) ((Subgroup.center Q).subtype b) :=
    fun a b => Subgroup.mem_center_iff.1 b.2 (a : Q)
  let φ : Ē × Subgroup.center Q →* Q := Ē.subtype.noncommCoprod (Subgroup.center Q).subtype hcomm
  have hrange : φ.range = Ē ⊔ Subgroup.center Q := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have h1 : Nat.card φ.range ≤ Nat.card (Ē × Subgroup.center Q) :=
    Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
  rw [hrange, Nat.card_prod] at h1
  exact h1

end Center

section Diag

variable {Q : Type} [Group Q] [Finite Q] {K : Type} [Field K] {p f n : ℕ}

open CFSG.RankThree.PartOne.KFU CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

theorem false_of_unitary_diag_center (hp : p.Prime) (hn : 5 ≤ n) (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hpq : p ∣ 2 ^ f + 1) (π : unitarySU 2 f K n →* Q)
    (hπ : Function.Surjective π) (hker : ¬ p ∣ Nat.card π.ker)
    (hZc : Nat.card (Subgroup.center Q) ≤ p) {Ē : Subgroup Q} (hE : IsElementaryAbelian p Ē)
    (hcard : Nat.card Ē = p ^ 2)
    (hmax : ∀ F : Subgroup Q, IsElementaryAbelian p F → F ≤ Subgroup.centralizer (Ē : Set Q) →
      Ē ≤ F → F ≤ Ē ⊔ Subgroup.center Q) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hU : UnitaryFieldData 2 f K := unitaryFieldData_two hK hf
  have hfinK : Finite K := hU.finite
  obtain ⟨E₀, hE₀, hE₀card, hE₀map⟩ := exists_lift_elementaryAbelian π hp hker Ē
    (fun y _ => hπ y) hcard
  have hE₀exp : ∀ x ∈ E₀, x ^ p = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (A := E₀) x hx
  have hE₀comm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy => by
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := E₀)).comm ⟨x, hx⟩ ⟨y, hy⟩)
    simpa using this
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU hp hpq (MulEquiv.refl _) E₀ hE₀exp hE₀comm
  have hrK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      zify [Nat.one_le_pow 2 (2 ^ f) (by omega), h1]
      ring
    rw [hfac]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hTle : torusSU p (m + 1) K ≤ unitarySU 2 f K (m + 1) := torusSU_le_unitarySU hU hpq
  let T : Subgroup (unitarySU 2 f K (m + 1)) := (torusSU p (m + 1) K).subgroupOf _
  have hTmem : ∀ g : unitarySU 2 f K (m + 1), g ∈ T ↔ (g : GL (Fin (m + 1)) K) ∈ torusSU p _ K :=
    fun g => Iff.rfl
  have hTcard : p ^ m ≤ Nat.card T := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]
    exact pow_le_card_torusSU hp hrK m
  have hTel : IsElementaryAbelian p T := isElementaryAbelian_torusSU_subgroupOf _
  let Eplus : Subgroup (unitarySU 2 f K (m + 1)) := T.map ψ.toMonoidHom
  have hEel : IsElementaryAbelian p Eplus := IsElementaryAbelian.map ψ.toMonoidHom
  have hE₀le : E₀ ≤ Eplus := by
    intro x hx
    exact ⟨ψ.symm x, (hTmem _).2 (hψ _ (by simpa using hx)), by simp⟩
  have hEcard : p ^ m ≤ Nat.card Eplus := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact hTcard
  let P' : Subgroup Q := Eplus.map π
  have hP'el : IsElementaryAbelian p P' := IsElementaryAbelian.map π
  have hEP : Ē ≤ P' := by
    rw [← hE₀map]
    exact Subgroup.map_mono hE₀le
  have hP'card : Nat.card P' = Nat.card Eplus := by
    have hdis := N143.disjoint_ker_of_isPGroup π hp (IsElementaryAbelian.isPGroup p Eplus) hker
    exact N143.card_map_of_disjoint_ker π hdis
  have hC : P' ≤ Subgroup.centralizer (Ē : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := P')).comm ⟨a, hEP ha⟩ ⟨y, hy⟩)
    simpa using this
  have hle := hmax P' hP'el hC hEP
  have h1 : Nat.card P' ≤ Nat.card ↥(Ē ⊔ Subgroup.center Q) := Subgroup.card_le_of_le hle
  have h2 := card_sup_le_of_central Ē
  rw [hP'card] at h1
  have h3 : p ^ m ≤ p ^ 2 * p := by
    calc p ^ m ≤ Nat.card Eplus := hEcard
      _ ≤ Nat.card ↥(Ē ⊔ Subgroup.center Q) := h1
      _ ≤ Nat.card Ē * Nat.card (Subgroup.center Q) := h2
      _ ≤ p ^ 2 * p := by
          rw [hcard]
          exact Nat.mul_le_mul_left _ hZc
  have h4 : p ^ 2 * p < p ^ m := by
    have : p ^ 2 * p = p ^ 3 := by ring
    rw [this]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

end Diag

section Pow5

variable {K : Type} [Field K]

open Polynomial in
theorem eq_one_of_pow_five_scalar {x : GL (Fin 5) K} (hdet : (x : Matrix (Fin 5) (Fin 5) K).det = 1)
    {ω : K} (hx : (x : Matrix (Fin 5) (Fin 5) K) ^ 5 = Matrix.scalar (Fin 5) ω)
    (hb : ¬ ∃ b : K, b ^ 5 = ω) : ω = 1 := by
  set A : Matrix (Fin 5) (Fin 5) K := (x : Matrix (Fin 5) (Fin 5) K) with hA
  have hirr : Irreducible (X ^ 5 - C ω : K[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_five (fun b hb' => hb ⟨b, hb'⟩)
  have hmon : (X ^ 5 - C ω : K[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hzero : aeval A (X ^ 5 - C ω : K[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C, hx]
    rw [Matrix.algebraMap_eq_diagonal]
    simp [Matrix.scalar_apply]
  have hmin : minpoly K A = X ^ 5 - C ω :=
    (minpoly.eq_of_irreducible_of_monic hirr hzero hmon).symm
  have hdvd : minpoly K A ∣ A.charpoly := minpoly.dvd K A (Matrix.aeval_self_charpoly A)
  have hdeg : A.charpoly.natDegree ≤ (minpoly K A).natDegree := by
    rw [hmin, natDegree_X_pow_sub_C, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hchar : A.charpoly = minpoly K A :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (Matrix.isIntegral A))
      (Matrix.charpoly_monic A) hdvd hdeg
  rw [hmin] at hchar
  have h1 := Matrix.det_eq_sign_charpoly_coeff A
  rw [hchar, hdet, Fintype.card_fin] at h1
  simp [coeff_sub, coeff_X_pow, coeff_C] at h1
  linear_combination -h1

end Pow5

section Shift

variable {K : Type} [Field K] {f : ℕ}

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem comm_centralizer_of_shift (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    {ct g : StatedSU 5 (2 ^ f) K} {c w : Kˣ} (hc : c ^ (2 ^ f + 1) = 1)
    (hct5 : (ct : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c)
    (hw5 : w ^ 5 = 1) (hw1 : w ≠ 1)
    (hg : (g : GL (Fin 5) K) * (ct : GL (Fin 5) K) * (g : GL (Fin 5) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 5) w * (ct : GL (Fin 5) K)) :
    ∀ a ∈ Subgroup.centralizer ({ct} : Set (StatedSU 5 (2 ^ f) K)),
      ∀ b ∈ Subgroup.centralizer ({ct} : Set (StatedSU 5 (2 ^ f) K)), a * b = b * a := by
  have hmemG : ∀ y : StatedSU 5 (2 ^ f) K, (y : GL (Fin 5) K) ∈ gramSU hU (idGram K 5) :=
    fun y => (SetLike.ext_iff.1 (unitarySU_eq_gramSU hU 5) (y : GL (Fin 5) K)).1 y.2
  have hmemP : ∀ y : StatedSU 5 (2 ^ f) K, (y : GL (Fin 5) K) ∈ unit5 hU := fun y =>
    ((mem_gramSU_iff_unitary hU).1 (hmemG y)).1
  have key := FOC.su5_comm_of_shift (h := hU) h5 (P := (⟨ct, hmemP ct⟩ : unit5 hU)) hc hct5
    (g := ⟨g, hmemG g⟩) hw5 hw1 hg
  intro a ha b hb
  have ha' : (⟨(a : GL (Fin 5) K), hmemG a⟩ : gramSU hU (idGram K 5)) ∈
      FOC.cenSU hU 5 (ct : GL (Fin 5) K) := by
    rw [FOC.mem_cenSU]
    have := Subgroup.mem_centralizer_singleton_iff.1 ha
    exact congrArg (fun x : StatedSU 5 (2 ^ f) K => (x : GL (Fin 5) K)) this
  have hb' : (⟨(b : GL (Fin 5) K), hmemG b⟩ : gramSU hU (idGram K 5)) ∈
      FOC.cenSU hU 5 (ct : GL (Fin 5) K) := by
    rw [FOC.mem_cenSU]
    have := Subgroup.mem_centralizer_singleton_iff.1 hb
    exact congrArg (fun x : StatedSU 5 (2 ^ f) K => (x : GL (Fin 5) K)) this
  have := key _ _ ha' hb'
  exact Subtype.ext (congrArg (fun x : gramSU hU (idGram K 5) => (x : GL (Fin 5) K)) this)

end Shift

section Big

variable {K : Type} [Field K] {f : ℕ}

open CFSG.RankThree.PartOne.KFU CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

abbrev ZSU5' (f : ℕ) (K : Type) [Field K] : Subgroup ↥(StatedSU 5 (2 ^ f) K) :=
  (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ f) K)

theorem exists_big_elementary_five (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {Y : Type}
    [Group Y] (πY : ↥(StatedSU 5 (2 ^ f) K) →* Y) (hker : πY.ker = ZSU5' f K)
    (hZMcard : Nat.card (ZSU5' f K) = 5) {E : Subgroup Y}
    (hexp : ∀ x ∈ E.comap πY, x ^ 5 = 1)
    (hab : ∀ x ∈ E.comap πY, ∀ y ∈ E.comap πY, x * y = y * x) :
    ∃ V : Subgroup Y, (∀ v ∈ V, v ^ 5 = 1) ∧ (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧
      (E.comap πY).map πY ≤ V ∧ 5 ^ 2 < Nat.card V := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hfin : Finite K := hU.finite
  set Ft : Subgroup ↥(StatedSU 5 (2 ^ f) K) := E.comap πY with hFt
  have hrK : 5 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hU.card, two_mul, pow_add]
    have h3 : 2 ^ f * 2 ^ f - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (2 ^ f) 1
      simpa using this
    rw [h3]
    exact Dvd.dvd.mul_right h5 _
  obtain ⟨P, β, hβP, hβ⟩ := exists_diag_conj hU Nat.prime_five h5 Ft hexp hab
  have hTle : torusSU 5 5 K ≤ unitarySU 2 f K 5 := torusSU_le_unitarySU hU h5
  let T : Subgroup ↥(StatedSU 5 (2 ^ f) K) := (torusSU 5 5 K).subgroupOf (StatedSU 5 (2 ^ f) K)
  have hTel : IsElementaryAbelian 5 T := isElementaryAbelian_torusSU_subgroupOf _
  have hTcard : 5 ^ 4 ≤ Nat.card T := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]
    exact pow_le_card_torusSU Nat.prime_five hrK 4
  let Vt : Subgroup ↥(StatedSU 5 (2 ^ f) K) := T.map β.symm.toMonoidHom
  have hVtel : IsElementaryAbelian 5 Vt := IsElementaryAbelian.map β.symm.toMonoidHom
  have hFtV : Ft ≤ Vt := by
    intro x hx
    refine ⟨β x, ?_, by simp⟩
    obtain ⟨d, hd⟩ := exists_diagU_of_isDiag (hβ x hx)
    have hx5 : ((β x : ↥(StatedSU 5 (2 ^ f) K)) : GL (Fin 5) K) ^ 5 = 1 := by
      have : (β x) ^ 5 = 1 := by rw [← map_pow, hexp x hx, map_one]
      have h2 := congrArg (fun y : ↥(StatedSU 5 (2 ^ f) K) => (y : GL (Fin 5) K)) this
      simpa using h2
    have hd5 : ∀ i, d i ^ 5 = 1 := by
      intro i
      have h1 : diagU (d ^ 5) = 1 := by rw [← diagU_pow, hd, hx5]
      have h2 : d ^ 5 = 1 := diagU_injective (h1.trans diagU_one.symm)
      exact congrFun h2 i
    have hdprod : ∏ i, d i = 1 := by
      have hdet := ((mem_unitarySU_iff hU).mp (β x).2).1
      rw [← hd, det_diagU] at hdet
      exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact hdet)
    exact Subgroup.mem_subgroupOf.2 ⟨d, ⟨hd5, hdprod⟩, hd⟩
  have hVtcard : 5 ^ 4 ≤ Nat.card Vt := by
    rw [Subgroup.card_map_of_injective β.symm.injective]
    exact hTcard
  refine ⟨Vt.map πY, ?_, ?_, Subgroup.map_mono hFtV, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have := elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := Vt) x hx
    rw [this, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := Vt)).comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [show x * y = y * x from by simpa using this]
  · have h1 := Subgroup.card_ker_mul_card_range (πY.comp Vt.subtype)
    have hrange : (πY.comp Vt.subtype).range = Vt.map πY := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange] at h1
    have hkerle : Nat.card (πY.comp Vt.subtype).ker ≤ 5 := by
      have hinj : Function.Injective (fun x : (πY.comp Vt.subtype).ker =>
          (⟨((x : ↥Vt) : ↥(StatedSU 5 (2 ^ f) K)), by
            have := x.2
            rw [MonoidHom.mem_ker] at this
            rw [← hker]
            exact this⟩ : ZSU5' f K)) := by
        intro x y hxy
        have h := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext h)
      calc Nat.card (πY.comp Vt.subtype).ker ≤ Nat.card (ZSU5' f K) :=
            Nat.card_le_card_of_injective _ hinj
        _ = 5 := hZMcard
    have h2 : 5 ^ 4 ≤ 5 * Nat.card (Vt.map πY) := by
      calc 5 ^ 4 ≤ Nat.card Vt := hVtcard
        _ = Nat.card (πY.comp Vt.subtype).ker * Nat.card (Vt.map πY) := h1.symm
        _ ≤ 5 * Nat.card (Vt.map πY) := Nat.mul_le_mul_right _ hkerle
    omega

end Big

section Lifts

variable {M Q : Type} [Group M] [Group Q]

theorem comap_commutative {π : M →* Q} (hkerc : π.ker ≤ Subgroup.center M) {c x : Q}
    (hcx : c * x = x * c) {ct xt : M} (hct : π ct = c) (hxt : π xt = x)
    (hcomm : ct * xt = xt * ct) {Ē : Subgroup Q}
    (hgen : Ē = Subgroup.zpowers c ⊔ Subgroup.zpowers x) :
    ∀ y ∈ Ē.comap π, ∀ z ∈ Ē.comap π, y * z = z * y := by
  have hdec : ∀ y ∈ Ē.comap π, ∃ (i j : ℤ) (u : M), u ∈ π.ker ∧ y = ct ^ i * xt ^ j * u := by
    intro y hy
    have hy' : π y ∈ Ē := hy
    rw [hgen] at hy'
    obtain ⟨s, hs, t, ht, hst⟩ := KLR.exists_mul_of_mem_sup_of_commute
      (A := Subgroup.zpowers c) (B := Subgroup.zpowers x) (fun a ha b hb => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_zpow (show Commute c x from hcx) i j).eq) hy'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    refine ⟨i, j, (ct ^ i * xt ^ j)⁻¹ * y, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_zpow, map_zpow, hct, hxt, ← hst]
    group
  have hc : Commute ct xt := hcomm
  intro y hy z hz
  obtain ⟨i, j, u, hu, rfl⟩ := hdec y hy
  obtain ⟨i', j', u', hu', rfl⟩ := hdec z hz
  have hZu : ∀ g : M, Commute u g := fun g => (Subgroup.mem_center_iff.1 (hkerc hu) g).symm
  have hZu' : ∀ g : M, Commute u' g := fun g => (Subgroup.mem_center_iff.1 (hkerc hu') g).symm
  have h1 : Commute (ct ^ i * xt ^ j) (ct ^ i' * xt ^ j') :=
    ((Commute.zpow_zpow_self ct i i').mul_right (Commute.zpow_zpow hc i j')).mul_left
      ((Commute.zpow_zpow hc.symm j i').mul_right (Commute.zpow_zpow_self xt j j'))
  have h2 : Commute (ct ^ i * xt ^ j * u) (ct ^ i' * xt ^ j' * u') :=
    Commute.mul_left (h1.mul_right (hZu' _).symm) (hZu _)
  exact h2.eq

end Lifts

section ShiftCase

open scoped commutatorElement

variable {M Q : Type} [Group M] [Group Q]

theorem false_of_commutative_cen {π : M →* Q} (hπ : Function.Surjective π)
    (hkerc : π.ker ≤ Subgroup.center M) {ct : M}
    (hcomm5 : ∀ a ∈ Subgroup.centralizer ({ct} : Set M),
      ∀ b ∈ Subgroup.centralizer ({ct} : Set M), a * b = b * a) {Kb : Subgroup Q}
    (hKbc : Kb ≤ Subgroup.centralizer ({π ct} : Set Q)) (hKbp : ⁅Kb, Kb⁆ = Kb)
    (hKb1 : Kb ≠ ⊥) : False := by
  have hZc : ∀ z ∈ π.ker, ∀ g : M, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.1 (hkerc hz) g
  have hcen : ∀ a₀ : M, π a₀ ∈ Kb → ∃ u ∈ π.ker, a₀ * ct * a₀⁻¹ = u * ct := by
    intro a₀ ha₀
    have h1 : π a₀ * π ct = π ct * π a₀ := Subgroup.mem_centralizer_singleton_iff.1 (hKbc ha₀)
    refine ⟨a₀ * ct * a₀⁻¹ * ct⁻¹, ?_, by group⟩
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [h1]
    group
  have hconj : ∀ (g z x : M), z ∈ π.ker → g * (z * x) * g⁻¹ = z * (g * x * g⁻¹) := by
    intro g z x hz
    have := hZc z hz g
    calc g * (z * x) * g⁻¹ = (g * z) * x * g⁻¹ := by group
      _ = (z * g) * x * g⁻¹ := by rw [this]
      _ = z * (g * x * g⁻¹) := by group
  have hA : ∀ a ∈ Kb, ∀ b ∈ Kb, ⁅a, b⁆ ∈ (Subgroup.centralizer ({ct} : Set M)).map π := by
    intro a ha b hb
    obtain ⟨a₀, rfl⟩ := hπ a
    obtain ⟨b₀, rfl⟩ := hπ b
    obtain ⟨u, hu, hu'⟩ := hcen a₀ ha
    obtain ⟨v, hv, hv'⟩ := hcen b₀ hb
    have e1 : b₀⁻¹ * ct * b₀ = v⁻¹ * ct := by
      have h := congrArg (fun g => b₀⁻¹ * g * b₀) hv'
      have h2 : b₀⁻¹ * (v * ct) * b₀ = v * (b₀⁻¹ * ct * b₀) := by
        have := hZc v hv b₀⁻¹
        calc b₀⁻¹ * (v * ct) * b₀ = (b₀⁻¹ * v) * ct * b₀ := by group
          _ = (v * b₀⁻¹) * ct * b₀ := by rw [this]
          _ = v * (b₀⁻¹ * ct * b₀) := by group
      rw [h2] at h
      have h3 : b₀⁻¹ * (b₀ * ct * b₀⁻¹) * b₀ = ct := by group
      rw [h3] at h
      exact eq_inv_mul_of_mul_eq h.symm
    have e2 : a₀⁻¹ * ct * a₀ = u⁻¹ * ct := by
      have h := congrArg (fun g => a₀⁻¹ * g * a₀) hu'
      have h2 : a₀⁻¹ * (u * ct) * a₀ = u * (a₀⁻¹ * ct * a₀) := by
        have := hZc u hu a₀⁻¹
        calc a₀⁻¹ * (u * ct) * a₀ = (a₀⁻¹ * u) * ct * a₀ := by group
          _ = (u * a₀⁻¹) * ct * a₀ := by rw [this]
          _ = u * (a₀⁻¹ * ct * a₀) := by group
      rw [h2] at h
      have h3 : a₀⁻¹ * (a₀ * ct * a₀⁻¹) * a₀ = ct := by group
      rw [h3] at h
      exact eq_inv_mul_of_mul_eq h.symm
    have hui : u⁻¹ ∈ π.ker := inv_mem hu
    have hvi : v⁻¹ ∈ π.ker := inv_mem hv
    have key : (a₀ * b₀ * a₀⁻¹ * b₀⁻¹) * ct * (a₀ * b₀ * a₀⁻¹ * b₀⁻¹)⁻¹ = ct := by
      calc (a₀ * b₀ * a₀⁻¹ * b₀⁻¹) * ct * (a₀ * b₀ * a₀⁻¹ * b₀⁻¹)⁻¹
          = a₀ * (b₀ * (a₀⁻¹ * (b₀⁻¹ * ct * b₀) * a₀) * b₀⁻¹) * a₀⁻¹ := by group
        _ = a₀ * (b₀ * (a₀⁻¹ * (v⁻¹ * ct) * a₀) * b₀⁻¹) * a₀⁻¹ := by rw [e1]
        _ = a₀ * (b₀ * (v⁻¹ * (a₀⁻¹ * ct * a₀)) * b₀⁻¹) * a₀⁻¹ := by
            have h0 := hconj a₀⁻¹ v⁻¹ ct hvi
            rw [inv_inv] at h0
            rw [h0]
        _ = a₀ * (b₀ * (v⁻¹ * (u⁻¹ * ct)) * b₀⁻¹) * a₀⁻¹ := by rw [e2]
        _ = a₀ * (v⁻¹ * (b₀ * (u⁻¹ * ct) * b₀⁻¹)) * a₀⁻¹ := by rw [hconj b₀ v⁻¹ _ hvi]
        _ = a₀ * (v⁻¹ * (u⁻¹ * (b₀ * ct * b₀⁻¹))) * a₀⁻¹ := by rw [hconj b₀ u⁻¹ ct hui]
        _ = a₀ * (v⁻¹ * (u⁻¹ * (v * ct))) * a₀⁻¹ := by rw [hv']
        _ = a₀ * (u⁻¹ * ct) * a₀⁻¹ := by
            have h1 := hZc v hv u⁻¹
            calc a₀ * (v⁻¹ * (u⁻¹ * (v * ct))) * a₀⁻¹
                = a₀ * (v⁻¹ * ((u⁻¹ * v) * ct)) * a₀⁻¹ := by group
              _ = a₀ * (v⁻¹ * ((v * u⁻¹) * ct)) * a₀⁻¹ := by rw [← h1]
              _ = a₀ * (u⁻¹ * ct) * a₀⁻¹ := by group
        _ = u⁻¹ * (a₀ * ct * a₀⁻¹) := by rw [hconj a₀ u⁻¹ ct hui]
        _ = ct := by rw [hu']; group
    refine ⟨a₀ * b₀ * a₀⁻¹ * b₀⁻¹, ?_, by simp [commutatorElement_def]⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.1 key
  have hAcomm : ∀ x ∈ (Subgroup.centralizer ({ct} : Set M)).map π,
      ∀ y ∈ (Subgroup.centralizer ({ct} : Set M)).map π, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm5 a ha b hb]
  apply hKb1
  rw [← hKbp, eq_bot_iff]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  have hKA : ∀ y ∈ Kb, y ∈ (Subgroup.centralizer ({ct} : Set M)).map π := fun y hy => by
    have : y ∈ ⁅Kb, Kb⁆ := by rw [hKbp]; exact hy
    exact (Subgroup.commutator_le.2 hA) this
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_commute.2 (hAcomm a (hKA a ha) b (hKA b hb))

end ShiftCase

section Main

theorem scalars_subgroupOf_le_center5 {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (M : Subgroup (GL ι K)) : (StatedScalars ι K).subgroupOf M ≤ Subgroup.center M :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _

theorem dvd_of_fifth_power {f : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2)
    (h5 : 5 ∣ 2 ^ f + 1) {ω : Kˣ} (hω5 : ω ^ 5 = 1) (hω1 : ω ≠ 1) (b : K) (hb : b ^ 5 = ω) :
    25 ∣ 2 ^ f + 1 := by
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hb
    exact ω.ne_zero hb.symm
  let β : Kˣ := Units.mk0 b hb0
  have hβ5 : β ^ 5 = ω := Units.ext (by simpa [β] using hb)
  have hn1 : ¬ β ^ (5 ^ 1) = 1 := by
    rw [pow_one, hβ5]
    exact hω1
  have hn2 : β ^ (5 ^ (1 + 1)) = 1 := by
    rw [show 5 ^ (1 + 1) = 5 * 5 by norm_num, pow_mul, hβ5, hω5]
  have hord : orderOf β = 5 ^ (1 + 1) := orderOf_eq_prime_pow hn1 hn2
  have h25 : 25 ∣ Nat.card Kˣ := by
    have := orderOf_dvd_natCard β
    rw [hord] at this
    simpa using this
  rw [Nat.card_units, hK] at h25
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    zify [Nat.one_le_pow 2 (2 ^ f) (by omega), h1]
    ring
  rw [hfac] at h25
  have hcop : Nat.Coprime 25 (2 ^ f - 1) := by
    have h5n : ¬ 5 ∣ 2 ^ f - 1 := by
      intro hd
      have h2 : 5 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h5 hd
      have h3 : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
      rw [h3] at h2
      omega
    have : Nat.Coprime 5 (2 ^ f - 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5n
    simpa using Nat.Coprime.pow_left 2 this
  exact hcop.dvd_of_dvd_mul_right h25

end Main

section Final

open CFSG.RankThree.PartOne.KFU CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

theorem u5Five_false
    (hGA : CFSG.Open.GriessAllModelsStatement) {Q : Type}
    [Group Q] [Finite Q] {g : ℕ} {Ē : Subgroup Q} {f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) (h : Row8Conf 5 g Q Ē)
    (e : (Q ⧸ Subgroup.center Q) ≃* StatedProj (StatedSU 5 (2 ^ f) K)) : False := by
  classical
  have hp : (5 : ℕ).Prime := Nat.prime_five
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  have hU : UnitaryFieldData 2 f K := unitaryFieldData_two hK hf
  have : Finite K := hU.finite
  have := h.elem
  have hadm : StatedLieAdmissible .PSU 5 2 f := ⟨Nat.prime_two, hf, by norm_num, by simp⟩
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSU 5 2 f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  have hdvd := card_center_dvd_multiplier hGA h.quasisimple (t := .PSU) (n := 5) (f := f)
    ⟨hadm, Or.inl hmod⟩
  rw [card_multiplier_psu_eq (Or.inl ⟨by norm_num, by norm_num⟩), Nat.gcd_eq_left h5] at hdvd
  have hZcases : Nat.card (Subgroup.center Q) = 1 ∨ Nat.card (Subgroup.center Q) = 5 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h.center_p
    rw [hk] at hdvd ⊢
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k <;> simp
    · exfalso
      have h1 := Nat.pow_le_pow_right (show 0 < 5 by norm_num) hk2
      have h2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
  rcases hZcases with hZ1 | hZ5
  ·
    have hZ : Subgroup.center Q = ⊥ := Subgroup.card_eq_one.1 hZ1
    obtain ⟨π, hπ, hπk⟩ := exists_cover_unitary hZ e
    have hπk' : π.ker = ZSU5' f K := hπk
    have hZMcard : Nat.card (ZSU5' f K) = 5 := by
      rw [show ZSU5' f K = (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ f) K) from rfl,
        (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK
          (by norm_num : 1 ≤ 5)).2.2, Nat.gcd_eq_left h5]
    have hkerc : π.ker ≤ Subgroup.center (StatedSU 5 (2 ^ f) K) := by
      rw [hπk']
      exact scalars_subgroupOf_le_center5 _
    obtain ⟨c, hcE, hc1, Kb, x, hKbc, hKbN, hmodKb, hxK, hxo, hgen⟩ := h.conf
    have hKbq := S15K.isQuasisimple_of_model hmodKb
    have hKbp : ⁅Kb, Kb⁆ = Kb := commutator_eq_self_of_perfect hKbq.1
    have hKb1 : Kb ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.mem_bot] at hxK
      rw [hxK, orderOf_one] at hxo
      exact hp.ne_one hxo.symm
    have hxE : x ∈ Ē := by
      rw [hgen]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have hcx : c * x = x * c :=
      congrArg Subtype.val (h.elem.is_comm.comm ⟨c, hcE⟩ ⟨x, hxE⟩)
    have hfinal : ∀ V : Subgroup Q, (∀ v ∈ V, v ^ 5 = 1) → (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) →
        Ē ≤ V → 5 ^ 2 < Nat.card V → False := by
      intro V hV5 hVc hEV hVcard
      have hVel : IsElementaryAbelian 5 V := by
        refine { is_comm := ⟨fun a b => ?_⟩, exponent_dvd_p := ?_ }
        · exact Subtype.ext (hVc _ a.2 _ b.2)
        · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun v => Subtype.ext (hV5 _ v.2)
      have hC : V ≤ Subgroup.centralizer (Ē : Set Q) := by
        intro v hv
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact hVc a (hEV ha) v hv
      have hle := h.max V hVel hC hEV
      rw [hZ, sup_bot_eq] at hle
      have := Subgroup.card_le_of_le hle
      rw [h.card] at this
      omega
    obtain ⟨ct, hct⟩ := hπ c
    obtain ⟨xt, hxt⟩ := hπ x
    have hE5 : ∀ y ∈ Ē, y ^ 5 = 1 := fun y hy =>
      elemPow_eq_one_of_isElementaryAbelian (A := Ē) y hy
    have hωk : xt * ct * xt⁻¹ * ct⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hct, hxt]
      rw [← hcx]
      group
    by_cases hω : xt * ct * xt⁻¹ * ct⁻¹ = 1
    ·
      have hcomm : ct * xt = xt * ct := by
        rw [← commutatorElement_def] at hω
        exact ((commutatorElement_eq_one_iff_commute.1 hω).eq).symm
      have hab := comap_commutative hkerc hcx hct hxt hcomm hgen
      have hEV : Ē ≤ (Ē.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπ Ē).ge
      by_cases h25 : 25 ∣ 2 ^ f + 1
      · obtain ⟨V, hV5, hVc, hEV', hVcard⟩ := Q1327C.exists_big_elementary hU h25 π hπk
          hZMcard (E := Ē) hE5 hab
        exact hfinal V hV5 hVc (hEV.trans hEV') (by omega)
      · have hexp : ∀ y ∈ Ē.comap π, y ^ 5 = 1 := by
          intro y hy
          have hy5k : y ^ 5 ∈ π.ker := by
            rw [MonoidHom.mem_ker, map_pow]
            exact hE5 _ hy
          rw [hπk'] at hy5k
          obtain ⟨ω', hω'⟩ := Subgroup.mem_subgroupOf.1 hy5k
          have hω'mem : (Matrix.GeneralLinearGroup.scalar (Fin 5) ω' : GL (Fin 5) K) ∈
              StatedSU 5 (2 ^ f) K := by
            rw [hω']
            exact (y ^ 5).2
          obtain ⟨hω'5, -⟩ := ((CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK
            (by norm_num : 1 ≤ 5)).2.1 ω').1 hω'mem
          by_contra hy1
          have hω'1 : ω' ≠ 1 := by
            intro h1
            apply hy1
            apply Subtype.ext
            rw [← hω', h1, map_one]
            rfl
          have hdet := ((mem_unitarySU_iff hU).mp y.2).1
          have hxm : ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ 5 =
              Matrix.scalar (Fin 5) (ω' : K) := by
            have h1 : ((y : GL (Fin 5) K)) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) ω' := by
              rw [hω']
              rfl
            have h2 := congrArg (fun z : GL (Fin 5) K => (z : Matrix (Fin 5) (Fin 5) K)) h1
            simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h2
          have hroot : ¬ ∃ b : K, b ^ 5 = (ω' : K) := fun ⟨b, hb⟩ =>
            h25 (dvd_of_fifth_power hK h5 hω'5 hω'1 b hb)
          have := eq_one_of_pow_five_scalar hdet hxm hroot
          exact hω'1 (Units.ext this)
        obtain ⟨V, hV5, hVc, hEV', hVcard⟩ := exists_big_elementary_five hU h5 π hπk' hZMcard
          (E := Ē) hexp hab
        exact hfinal V hV5 hVc (hEV.trans hEV') hVcard
    ·
      have hωk' := hωk
      rw [hπk'] at hωk'
      obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.1 hωk'
      have hwmem : (Matrix.GeneralLinearGroup.scalar (Fin 5) w : GL (Fin 5) K) ∈
          StatedSU 5 (2 ^ f) K := by
        rw [hw]
        exact (xt * ct * xt⁻¹ * ct⁻¹).2
      obtain ⟨hw5, -⟩ := ((CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK
        (by norm_num : 1 ≤ 5)).2.1 w).1 hwmem
      have hw1 : w ≠ 1 := by
        intro h1
        apply hω
        apply Subtype.ext
        rw [← hw, h1, map_one]
        rfl
      have hct5k : ct ^ 5 ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_pow, hct]
        exact hE5 _ hcE
      have hct5k' := hct5k
      rw [hπk'] at hct5k'
      obtain ⟨c', hc'⟩ := Subgroup.mem_subgroupOf.1 hct5k'
      have hc'mem : (Matrix.GeneralLinearGroup.scalar (Fin 5) c' : GL (Fin 5) K) ∈
          StatedSU 5 (2 ^ f) K := by
        rw [hc']
        exact (ct ^ 5).2
      obtain ⟨-, hcq⟩ := ((CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK
        (by norm_num : 1 ≤ 5)).2.1 c').1 hc'mem
      have hct5 : (ct : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c' := by
        rw [hc']
        rfl
      have hg : (xt : GL (Fin 5) K) * (ct : GL (Fin 5) K) * (xt : GL (Fin 5) K)⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 5) w * (ct : GL (Fin 5) K) := by
        rw [hw]
        have : xt * ct * xt⁻¹ = (xt * ct * xt⁻¹ * ct⁻¹) * ct := by group
        exact congrArg (fun z : StatedSU 5 (2 ^ f) K => (z : GL (Fin 5) K)) this
      have hcomm5 := comm_centralizer_of_shift hU h5 hcq hct5 hw5 hw1 hg
      exact false_of_commutative_cen hπ hkerc hcomm5 (by rw [hct]; exact hKbc) hKbp hKb1
  ·
    have : Group.IsPerfect Q := h.quasisimple.1
    obtain ⟨-, ⟨ψ⟩⟩ := KFSU5.exists_su5_iso (Lg := Q) hZ5 hf hK e
    have hker : ¬ 5 ∣ Nat.card ψ.toMonoidHom.ker := by
      rw [(MonoidHom.ker_eq_bot_iff _).2 ψ.injective, Subgroup.card_bot]
      norm_num
    exact false_of_unitary_diag_center hp (le_refl 5) hf hK h5 ψ.toMonoidHom ψ.surjective hker
      (by omega) h.elem h.card h.max

theorem u5Five_holds : U5Five := by
  intro hGA Q _ _ g Ē f K _ hK hf h5 h e
  exact u5Five_false hGA hK hf h5 h e

theorem row8U3At_leaf7_seven
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf7 7) :=
  row8U3At_leaf7_seven_of_five hGA u5Five_holds

end Final

end CFSG.RankThree.PartOne.Q1327T
