module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.H13.L32AC47k
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)

namespace A6L32

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_eq_three_of_decomp {N : Subgroup G} {c : G} (hc : c ∈ N) (hc3 : c ^ 3 = 1)
    (hcO : c ∉ pCoreOf 2 N)
    (hdec : ∀ x ∈ N, x ∈ pCoreOf 2 N ∨ c * c * x ∈ pCoreOf 2 N ∨ c * x ∈ pCoreOf 2 N) :
    (pCoreOf 2 N).relIndex N = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (pCoreOf 2 N).subgroupOf N with hP
  have hPn : P.Normal := by
    rw [hP, L32A.C.subgroupOf_pCoreOf_eq_pCore]
    exact CFSG.pCore_normal
  set q : ↥N ⧸ P := QuotientGroup.mk (⟨c, hc⟩ : ↥N) with hq
  have hq1 : q ≠ 1 := by
    rw [hq, Ne, QuotientGroup.eq_one_iff, hP, Subgroup.mem_subgroupOf]
    exact hcO
  have hq3 : q ^ 3 = 1 := by
    have h1 : (⟨c, hc⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [hq, ← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
  have hord : orderOf q = 3 := orderOf_eq_prime hq3 hq1
  have hmk : ∀ x (hx : x ∈ N), (x ∈ pCoreOf 2 N → (QuotientGroup.mk (⟨x, hx⟩ : ↥N) : ↥N ⧸ P) = 1) :=
    fun x hx h => (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h)
  have htop : Subgroup.zpowers q = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective y
    rcases hdec x hx with h | h | h
    · rw [hmk x hx h]
      exact Subgroup.one_mem _
    · have h1 := hmk _ (N.mul_mem (N.mul_mem hc hc) hx) h
      have e : (QuotientGroup.mk (⟨c * c * x, N.mul_mem (N.mul_mem hc hc) hx⟩ : ↥N) :
          ↥N ⧸ P) = q * q * QuotientGroup.mk (⟨x, hx⟩ : ↥N) := rfl
      rw [e] at h1
      rw [eq_inv_of_mul_eq_one_right h1]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mem_zpowers q)
        (Subgroup.mem_zpowers q))
    · have h1 := hmk _ (N.mul_mem hc hx) h
      have e : (QuotientGroup.mk (⟨c * x, N.mul_mem hc hx⟩ : ↥N) : ↥N ⧸ P) =
          q * QuotientGroup.mk (⟨x, hx⟩ : ↥N) := rfl
      rw [e] at h1
      rw [eq_inv_of_mul_eq_one_right h1]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers q)
  show Nat.card (↥N ⧸ P) = 3
  calc Nat.card (↥N ⧸ P) = Nat.card (⊤ : Subgroup (↥N ⧸ P)) := Subgroup.card_top.symm
    _ = Nat.card (Subgroup.zpowers q) := by rw [htop]
    _ = 3 := by rw [Nat.card_zpowers, hord]

theorem comm_of_not_le {H K T X : Subgroup G} (hKc : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hTsylH : IsSylowTwoOf T H)
    (hP : IsPSL 3 2 1 (L32A.cStar K))
    (h3 : (pCoreOf 2 (oTwoUpper X)).relIndex (oTwoUpper X) = 3) (hXH : oTwoUpper X ≤ H)
    (hTX : T ≤ Subgroup.normalizer (oTwoUpper X : Set G)) (hnot : ¬ oTwoUpper X ≤ K) :
    ∀ x ∈ oTwoUpper X, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  obtain ⟨φ⟩ := isPSL_three_two_iff.mp hP
  set π₀ : ↥K →* SL3.S := φ.toMonoidHom.comp (QuotientGroup.mk' _) with hπ₀def
  have hπ₀ : Function.Surjective π₀ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ∀ k : ↥K, π₀ k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπ₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hTsyl : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTsylH hKH hKn
  have hS2 : IsPGroup 2 (T.subgroupOf K) :=
    hTsylH.2.1.comap_of_injective K.subtype K.subtype_injective
  have hSi : ¬ 2 ∣ (T.subgroupOf K).index := Subgroup.inf_subgroupOf_right T K ▸ hTsyl.2.2
  obtain ⟨h, hhD⟩ := L32A.C.exists_conj_map_eq_of_sylow π₀ hπ₀ hS2 hSi SL3.P0_sylow.1
    SL3.P0_sylow.2
  set π : ↥K →* SL3.S := (MulAut.conj h⁻¹).toMonoidHom.comp π₀ with hπdef
  have hπ : Function.Surjective π := (MulAut.conj h⁻¹).surjective.comp hπ₀
  have hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hker₀]
  have hD : (T.subgroupOf K).map π = SL3.P0 := by
    rw [← hhD, Subgroup.map_map]
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  set β := L32A.C.indHom π hπ hker hKn hHN with hβdef
  have hβ : ∀ (y : ↥H) (k : ↥K), β y (π k) = π (conjK (hKn y.2) k) :=
    L32A.C.indHom_apply π hπ hker hKn hHN
  have hgen : ∀ y (hy : y ∈ X ∧ Odd (orderOf y)),
      β ⟨y, hXH (Subgroup.subset_closure hy)⟩ = 1 := by
    intro y hy
    have hyl1 : y ∈ oTwoUpper X := Subgroup.subset_closure hy
    have hyH : y ∈ H := hXH hyl1
    have hodd : Odd (orderOf (β ⟨y, hyH⟩)) :=
      Odd.of_dvd_nat (by rw [Subgroup.orderOf_mk]; exact hy.2) (orderOf_map_dvd β _)
    obtain ⟨g, hg⟩ := L32A.C.mem_inner_of_odd_orderOf L32A.C.sl3_outer hodd
    by_contra hne
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hne (by rw [← hg, map_one])
    have hog : orderOf g = orderOf (β ⟨y, hyH⟩) := by
      rw [← hg, orderOf_injective _ L32A.C.sl3_conj_injective]
    obtain ⟨s, hs, hw⟩ := L32A.C.sl3_comm_fact g hg1 (L32A.C.sl3_pow_21_of_odd (hog ▸ hodd))
    have hsP : s ∈ (T.subgroupOf K).map π := hD ▸ SL3.P0list_mem le_rfl s hs
    obtain ⟨s', hs'T, rfl⟩ := hsP
    have hs'T' : (s' : G) ∈ T := hs'T
    set yH : ↥H := ⟨y, hyH⟩ with hyHdef
    set s₀ : G := (s' : G) with hs₀
    have huK : y⁻¹ * (s₀ * y * s₀⁻¹) ∈ K := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hKn (H.inv_mem hyH)) s₀).mp s'.2
      have e : y⁻¹ * (s₀ * y * s₀⁻¹) = (y⁻¹ * s₀ * y⁻¹⁻¹) * s₀⁻¹ := by group
      rw [e]
      exact K.mul_mem h1 (K.inv_mem s'.2)
    have hul1 : y⁻¹ * (s₀ * y * s₀⁻¹) ∈ oTwoUpper X :=
      (oTwoUpper X).mul_mem ((oTwoUpper X).inv_mem hyl1)
        ((Subgroup.mem_normalizer_iff.mp (hTX hs'T') y).mp hyl1)
    have hπu : π ⟨_, huK⟩ = g⁻¹ * π s' * g * (π s')⁻¹ := by
      have e1 : (⟨y⁻¹ * (s₀ * y * s₀⁻¹), huK⟩ : ↥K) = conjK (hKn yH⁻¹.2) s' * s'⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply, hyHdef, hs₀]
        group
      rw [e1, map_mul, map_inv, ← hβ, map_inv, ← hg]
      simp [mul_assoc]
    have hu2 : y⁻¹ * (s₀ * y * s₀⁻¹) ∉ pCoreOf 2 (oTwoUpper X) := by
      intro hmem
      obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (oTwoUpper X)) ⟨_, hmem⟩
      have hun : (⟨_, huK⟩ : ↥K) ^ 2 ^ n = 1 := Subtype.ext (by
        have := congrArg Subtype.val hn
        simpa using this)
      have hπn : (π ⟨_, huK⟩) ^ 2 ^ n = 1 := by rw [← map_pow, hun, map_one]
      exact hw (hπu ▸ L32A.C.sl3_pow_four_of_two_pow hπn)
    exact hnot (L32A.C.oTwoUpper_le_of_mem h3 hXH hKH hKn hul1 huK hu2)
  have hNβ : ∀ x (hx : x ∈ oTwoUpper X), β ⟨x, hXH hx⟩ = 1 := by
    have hle : oTwoUpper X ≤ β.ker.map H.subtype :=
      (Subgroup.closure_le _).2 fun y hy =>
        ⟨⟨y, hXH (Subgroup.subset_closure hy)⟩, hgen y hy, rfl⟩
    intro x hx
    obtain ⟨x', hx'k, hx'⟩ := hle hx
    have e : (⟨x, hXH hx⟩ : ↥H) = x' := Subtype.ext hx'.symm
    rw [e]
    exact hx'k
  intro x hx k hk
  have h1 := hβ ⟨x, hXH hx⟩ ⟨k, hk⟩
  rw [hNβ x hx, MulAut.one_apply] at h1
  have h2 : π (conjK (hKn (hXH hx)) ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← h1, mul_inv_cancel]
  exact (hker _).mp h2

end A6L32

end CFSG.Quasithin.H13.A6
