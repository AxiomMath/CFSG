module

public import CFSG.Quasithin.H13.L32NLem14331h
public import CFSG.Quasithin.H13.A5S1327g
public import CFSG.Quasithin.H13.L32NLem14331g

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14331

variable {G : Type} [Group G]

abbrev kT (T V : Subgroup G) (l e : G) : Subgroup G := kA T V (l⁻¹ * e * l) ⊔ T

abbrev iKP (T L V : Subgroup G) (l e : G) : Subgroup G := kT T V l e ⊔ p128 T L V

abbrev dQ (T L V : Subgroup G) (l e : G) : Type :=
  ↥(iKP T L V l e) ⧸ CFSG.pPrimeCore 3 ↥(iKP T L V l e)

abbrev piQ (T L V : Subgroup G) (l e : G) : ↥(iKP T L V l e) →* dQ T L V l e :=
  QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(iKP T L V l e))

abbrev g1bar (T L V : Subgroup G) (l e : G) : Subgroup (dQ T L V l e) :=
  ((kT T V l e).subgroupOf (iKP T L V l e)).map (piQ T L V l e)

abbrev g2bar (T L V : Subgroup G) (l e : G) : Subgroup (dQ T L V l e) :=
  ((p128 T L V).subgroupOf (iKP T L V l e)).map (piQ T L V l e)

theorem w_mem_oTwoUpper {Q : Type} [Group Q] [Finite Q] {a u₁ u₂ : Q} (ha : a ^ 3 = 1)
    (h21 : u₂ = a * u₁ * a⁻¹) : u₂ * u₁⁻¹ ∈ oTwoUpper (⊤ : Subgroup Q) := by
  have hodd : ∀ w : Q, w ^ 3 = 1 → w ∈ oTwoUpper (⊤ : Subgroup Q) :=
    fun w hw => mem_oTwoUpper_of_odd (Subgroup.mem_top w)
      (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hw))
  have e1 : u₂ * u₁⁻¹ = a * (u₁ * a⁻¹ * u₁⁻¹) := by rw [h21]; group
  rw [e1]
  refine Subgroup.mul_mem _ (hodd _ ha) (hodd _ ?_)
  rw [conj_pow, inv_pow, ha, inv_one, mul_one, mul_inv_cancel]

theorem eq_one_of_comm_w {Q : Type} [Group Q] {a u₁ u₂ : Q} (ha : a ^ 3 = 1)
    (h21 : u₂ = a * u₁ * a⁻¹) (hc : a * (u₂ * u₁⁻¹) = (u₂ * u₁⁻¹) * a) {k : ℕ}
    (hk : (u₂ * u₁⁻¹) ^ 2 ^ k = 1) : u₂ * u₁⁻¹ = 1 := by
  set w := u₂ * u₁⁻¹ with hw
  have hcw : a * w * a⁻¹ = w := by rw [hc, mul_inv_cancel_right]
  have hcu : a * u₁ * a⁻¹ = w * u₁ := by rw [hw, ← h21, inv_mul_cancel_right]
  have h3 := L14332.pow_conj_eq hcw hcu 3
  rw [ha, one_mul, inv_one, mul_one] at h3
  have hw3 : w ^ 3 = 1 := by
    have : u₁ * u₁⁻¹ = w ^ 3 * u₁ * u₁⁻¹ := by rw [← h3]
    simpa using this.symm
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
    (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hw3))

end L14331

namespace L14328

open L14331

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx

variable {g z b l : G} (C : Ctx G T L V V₂ g z b l) (D : HatModelU (fsuU T V)) {e : G}
include C

theorem caseI_pCoreOf_le (X : CaseI T L V g D e) :
    pCoreOf 2 (iKP T L V l e) ≤ pCoreOf 2 (p128 T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htriple := (C.caseI_triple D X).subgroupOf
  have hPI : p128 T L V ≤ iKP T L V l e := le_sup_right
  have h2 := F6.inf_pPrimeCore_eq_pCore_right htriple
  have hle : pCoreOf 2 (iKP T L V l e) ≤ p128 T L V := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← h2] at hx
    exact Subgroup.mem_subgroupOf.mp hx.1
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle
    (hPI.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem caseI_comm_ne (X : CaseI T L V g D e) {y u : G} (hyK : y ∈ kA T V (l⁻¹ * e * l))
    (hu : u ∈ fsuU T V) (hyu : y * u * y⁻¹ * u⁻¹ ∉ Subgroup.centralizer (V₂ : Set G))
    (hI : y * u * y⁻¹ * u⁻¹ ∈ iKP T L V l e) :
    piQ T L V l e ⟨y * u * y⁻¹ * u⁻¹, hI⟩ ≠ 1 := by
  intro h1
  apply hyu
  have htriple := (C.caseI_triple D X).subgroupOf
  have h3 : (⟨y * u * y⁻¹ * u⁻¹, hI⟩ : ↥(iKP T L V l e)) ∈ CFSG.pPrimeCore 3 ↥(iKP T L V l e) := by
    rwa [MonoidHom.mem_ker.symm, QuotientGroup.ker_mk'] at h1
  have hKT : y * u * y⁻¹ * u⁻¹ ∈ kT T V l e := by
    have huT : u ∈ kT T V l e := Subgroup.mem_sup_right (C.U_T hu)
    have hyT : y ∈ kT T V l e := Subgroup.mem_sup_left hyK
    exact (kT T V l e).mul_mem ((kT T V l e).mul_mem ((kT T V l e).mul_mem hyT huT)
      ((kT T V l e).inv_mem hyT)) ((kT T V l e).inv_mem huT)
  have h4 : (⟨y * u * y⁻¹ * u⁻¹, hI⟩ : ↥(iKP T L V l e)) ∈ CFSG.Open.pCore 2 ↥(iKP T L V l e) := by
    rw [← F6.inf_pPrimeCore_eq_pCore_left htriple]
    exact ⟨Subgroup.mem_subgroupOf.mpr hKT, h3⟩
  have h5 : y * u * y⁻¹ * u⁻¹ ∈ pCoreOf 2 (iKP T L V l e) := ⟨_, h4, rfl⟩
  have h6 := C.caseI_pCoreOf_le D X h5
  rw [← L128P.oTwoUpper_sup_eq C.setting.hyp] at h6
  exact L128P.pCoreOf_le_centralizer X.h1222 C.setting.hyp C.setting.v1 C.setting.v2
    C.setting.le h6

theorem caseI_exists_ubar (X : CaseI T L V g D e) :
    ∃ y ∈ kA T V (l⁻¹ * e * l), ∃ hyI : y ∈ iKP T L V l e, ∃ u₁ u₂ : dQ T L V l e,
      (piQ T L V l e ⟨y, hyI⟩) ^ 3 = 1 ∧ u₁ ∈ g1bar T L V l e ⊓ g2bar T L V l e ∧
      u₂ ∈ g1bar T L V l e ⊓ g2bar T L V l e ∧
      u₂ = piQ T L V l e ⟨y, hyI⟩ * u₁ * (piQ T L V l e ⟨y, hyI⟩)⁻¹ ∧ u₂ * u₁⁻¹ ≠ 1 ∧
      ∃ x ∈ fsuU T V, ∃ hx : x ∈ iKP T L V l e, piQ T L V l e ⟨x, hx⟩ = u₂ * u₁⁻¹ := by
  obtain ⟨y, hyK, hy3, -, -, ⟨u, hu, hyu⟩, -⟩ := C.caseI_exists_y D X
  have hKT : ∀ {x : G}, x ∈ fsuU T V → x ∈ kT T V l e := fun hx =>
    Subgroup.mem_sup_right (C.U_T hx)
  have hP : ∀ {x : G}, x ∈ fsuU T V → x ∈ p128 T L V := fun hx => L128P.le_p128 (C.U_T hx)
  have hI : ∀ {x : G}, x ∈ fsuU T V → x ∈ iKP T L V l e := fun hx =>
    Subgroup.mem_sup_left (hKT hx)
  have hyH := C.caseI_K_H D X hyK
  have hyuU : y * u * y⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp (L14332.l32nH_le_normalizer_fsuU T V hyH) u).mp hu
  have hcU : y * u * y⁻¹ * u⁻¹ ∈ fsuU T V := (fsuU T V).mul_mem hyuU ((fsuU T V).inv_mem hu)
  have hne := C.caseI_comm_ne D X hyK hu hyu (hI hcU)
  have hyI : y ∈ iKP T L V l e := Subgroup.mem_sup_left (Subgroup.mem_sup_left hyK)
  have hmem : ∀ {x : G} (hx : x ∈ fsuU T V),
      piQ T L V l e ⟨x, hI hx⟩ ∈ g1bar T L V l e ⊓ g2bar T L V l e := fun hx =>
    ⟨⟨⟨_, hI hx⟩, Subgroup.mem_subgroupOf.mpr (hKT hx), rfl⟩,
      ⟨⟨_, hI hx⟩, Subgroup.mem_subgroupOf.mpr (hP hx), rfl⟩⟩
  refine ⟨y, hyK, hyI, piQ T L V l e ⟨u, hI hu⟩, piQ T L V l e ⟨y * u * y⁻¹, hI hyuU⟩,
    ?_, hmem hu, hmem hyuU, ?_, ?_, y * u * y⁻¹ * u⁻¹, hcU, hI hcU, ?_⟩
  · rw [← map_pow]
    have : (⟨y, hyI⟩ : ↥(iKP T L V l e)) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  · rw [← map_inv, ← map_mul]
    exact hne
  · rw [← map_inv, ← map_mul]
    rfl

theorem caseI_w_two_pow {x : G} (hxU : x ∈ fsuU T V)
    (hxI : x ∈ iKP T L V l e) : ∃ k : ℕ, (piQ T L V l e ⟨x, hxI⟩) ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := C.S.hH.sylow.1 ⟨x, C.U_T hxU⟩
  refine ⟨k, ?_⟩
  rw [← map_pow]
  have : (⟨x, hxI⟩ : ↥(iKP T L V l e)) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  rw [this, map_one]

theorem caseI_not_caseOne (X : CaseI T L V g D e) :
    ¬ F6.IsF618CaseOne (g1bar T L V l e) (g2bar T L V l e) ∧
      ¬ F6.IsF618CaseOne (g2bar T L V l e) (g1bar T L V l e) := by
  obtain ⟨y, -, hyI, u₁, u₂, -, h1, h2, h21, hne, -⟩ := C.caseI_exists_ubar D X
  set ybar := piQ T L V l e ⟨y, hyI⟩ with hybar
  have hu₁1 : u₁ ≠ 1 := by
    intro h
    apply hne
    rw [h21, h, mul_one, mul_inv_cancel, inv_one, mul_one]
  have hu₂1 : u₂ ≠ 1 := by
    intro h
    apply hu₁1
    calc u₁ = ybar⁻¹ * (ybar * u₁ * ybar⁻¹) * ybar := by group
      _ = 1 := by rw [← h21, h]; group
  have key : ∀ A : Subgroup (dQ T L V l e), u₁ ∈ A → u₂ ∈ A → Nat.card A ≠ 2 := by
    intro A hA1 hA2 hA
    rcases eq_one_or_eq_of_card_two hA hA1 hu₁1 hA2 with h | h
    · exact hu₂1 h
    · exact hne (by rw [h, mul_inv_cancel])
  constructor
  · rintro ⟨⟨φ⟩, -⟩
    exact key _ h1 h2 (by rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card])
  · rintro ⟨⟨φ⟩, -⟩
    rw [inf_comm] at h1 h2
    exact key _ h1 h2 (by rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card])

theorem caseI_not_caseTwo (X : CaseI T L V g D e) : ¬ F6.IsF618CaseTwo (dQ T L V l e) := by
  intro h2
  have h3 := A5.isPGroup_oTwoUpper_of_caseTwo h2
  obtain ⟨y, -, hyI, u₁, u₂, hy3, -, -, h21, hne, x, hxU, hxI, hx⟩ := C.caseI_exists_ubar D X
  have hw := w_mem_oTwoUpper hy3 h21
  obtain ⟨n, hn⟩ := h3 ⟨_, hw⟩
  have hn' : (u₂ * u₁⁻¹) ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨k, hk⟩ := C.caseI_w_two_pow hxU hxI
  rw [hx] at hk
  apply hne
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow k n (by norm_num : Nat.Coprime 2 3))
    (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hn'))

end Ctx

end L14328

end CFSG.Quasithin.H13
