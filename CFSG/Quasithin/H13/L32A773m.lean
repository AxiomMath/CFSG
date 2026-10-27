module

public import CFSG.Quasithin.H13.L32A773l

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Group G] [Finite G] in
theorem mem_of_ncard_four {α : Type} [Finite α] {M : Set α} (hM : M.ncard = 4) {o a b c : α}
    (h : ∀ g ∈ M, g = o ∨ g = a ∨ g = b ∨ g = c) : a ∈ M := by
  by_contra ha
  have hsub : M ⊆ {o, b, c} := fun g hg => by
    rcases h g hg with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hg ha
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({o, b, c} : Set α).ncard ≤ 3 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    have := Set.ncard_insert_le b ({c} : Set α)
    rw [Set.ncard_singleton] at this
    omega
  omega

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem theta_mem_u {θ : ↥L →* H6.Γ} (hθs : Function.Surjective θ)
    (hθk : θ.ker = (sL T L V).subgroupOf L)
    (hθLl : ∀ l : ↥L, θ l ∈ H6.Ll ↔ (l : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G))
    {X : Subgroup G} (hXQ : X ≤ pCoreOf 2 (hz T V)) (hX4 : (sL T L V).relIndex X = 4) :
    (∃ q : ↥L, (q : G) ∈ X ∧ θ q = stU1) ∧ (∃ q : ↥L, (q : G) ∈ X ∧ θ q = stU2) := by
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hXL : X ≤ L := hXQ.trans ((pCoreOf_le_of_le C.hyp hTH).trans C.T_le_L)
  set Xθ := (X.subgroupOf L).map θ with hXθ
  have hXθ4 : Nat.card ↥Xθ = 4 := by
    rw [hXθ, ← Subgroup.relIndex_ker, hθk, Subgroup.relIndex_subgroupOf hXL, hX4]
  have hXθmem : ∀ g ∈ (Xθ : Set H6.Γ), g = 1 ∨ g = stU1 ∨ g = stU2 ∨ g = stU1 * stU2 := by
    rintro _ ⟨q, hq, rfl⟩
    exact C.theta_QH_mem hθs hθLl q (hXQ (Subgroup.mem_subgroupOf.mp hq))
  have hXθc : (Xθ : Set H6.Γ).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hXθ4
  have hu1 : stU1 ∈ (Xθ : Set H6.Γ) := mem_of_ncard_four hXθc hXθmem
  have hu2 : stU2 ∈ (Xθ : Set H6.Γ) := mem_of_ncard_four hXθc fun g hg => by
    rcases hXθmem g hg with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  obtain ⟨q₁, hq₁, hθq₁⟩ := hu1
  obtain ⟨q₂, hq₂, hθq₂⟩ := hu2
  exact ⟨⟨q₁, Subgroup.mem_subgroupOf.mp hq₁, hθq₁⟩, ⟨q₂, Subgroup.mem_subgroupOf.mp hq₂, hθq₂⟩⟩

theorem exists_theta_chi : ∃ (θ : ↥L →* H6.Γ)
    (χ : ↥(sL T L V) →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))),
    Function.Surjective θ ∧ θ.ker = (sL T L V).subgroupOf L ∧
    (∀ l : ↥L, θ l ∈ H6.Ll ↔ (l : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G)) ∧
    χ.ker = V.subgroupOf (sL T L V) ∧
    (∀ s, RuType.IsTraceZero (Multiplicative.toAdd (χ s))) ∧
    (∀ A, RuType.IsTraceZero A → ∃ s, χ s = Multiplicative.ofAdd A) ∧
    (∀ (l : ↥L) (s t : ↥(sL T L V)), (t : G) = l * s * (l : G)⁻¹ →
      χ t = Multiplicative.ofAdd (RuType.stAct (θ l) (Multiplicative.toAdd (χ s)))) ∧
    (∀ A, A.trace = 0 → IsStC A → ∃ s : ↥(sL T L V), (s : G) ∈ fsuU T V ∧
      χ s = Multiplicative.ofAdd A) ∧
    ∀ s : ↥(sL T L V), (s : G) ∈ pCoreOf 2 (hz T V) → IsStW (Multiplicative.toAdd (χ s)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ, hθs, hθk, hθLl⟩ := C.exists_theta1
  obtain ⟨χ, hχk, hχt, hχs, hχe⟩ :=
    C.isSteinbergSection C.u0_eq C.vh63 C.vh65 C.l71 θ hθs hθk
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hQT : pCoreOf 2 (hz T V) ≤ T := pCoreOf_le_of_le C.hyp hTH
  have hQL : pCoreOf 2 (hz T V) ≤ L := hQT.trans C.T_le_L
  have hSH : sL T L V ≤ hz T V := C.sL_le_kz.trans (oTwoUpper_le _)
  have hχ1 : ∀ s : ↥(sL T L V), χ s = 1 ↔ (s : G) ∈ V := fun s => by
    rw [← MonoidHom.mem_ker, hχk, Subgroup.mem_subgroupOf]
  have hcommS : ∀ q ∈ pCoreOf 2 (hz T V), ∀ s ∈ sL T L V, q * s * q⁻¹ * s⁻¹ ∈ sL T L V := by
    intro q hq s hs
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (C.T_le_normalizer_sL (hQT hq)) s).mp hs)
      (inv_mem hs)
  have hcommQ : ∀ q ∈ pCoreOf 2 (hz T V), ∀ s ∈ sL T L V,
      q * s * q⁻¹ * s⁻¹ ∈ pCoreOf 2 (hz T V) := by
    intro q hq s hs
    rw [show q * s * q⁻¹ * s⁻¹ = q * (s * q⁻¹ * s⁻¹) by group]
    exact mul_mem hq ((Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (hz T V) (hSH hs)) _).mp (inv_mem hq))
  obtain ⟨⟨q₁, hq₁, hθq₁⟩, ⟨q₂, hq₂, hθq₂⟩⟩ := C.theta_mem_u hθs hθk hθLl le_rfl (by
    have h1 := Subgroup.relIndex_mul_card (sL T L V) (pCoreOf 2 (hz T V))
    rw [C.card_sL_inf_QH, C.card_QH] at h1
    omega)
  have hcomm : ∀ (q : ↥L), (q : G) ∈ pCoreOf 2 (hz T V) → ∀ s : ↥(sL T L V),
      ∃ w : ↥(sL T L V), (w : G) = q * s * (q : G)⁻¹ * (s : G)⁻¹ ∧
        (w : G) ∈ pCoreOf 2 (hz T V) ∧ Multiplicative.toAdd (χ w) =
          RuType.stAct (θ q) (Multiplicative.toAdd (χ s)) - Multiplicative.toAdd (χ s) :=
    fun q hq s => ⟨⟨_, hcommS _ hq _ s.2⟩, rfl, hcommQ _ hq _ s.2,
      chi_comm hχe q s (hcommS _ hq _ s.2)⟩
  have hAS : sL T L V ⊓ pCoreOf 2 (hz T V) ≤ sL T L V := inf_le_left
  set χA := ((sL T L V ⊓ pCoreOf 2 (hz T V)).subgroupOf (sL T L V)).map χ with hχA
  have hχA64 : Nat.card ↥χA = 64 := by
    rw [hχA, ← Subgroup.relIndex_ker, hχk, Subgroup.relIndex_subgroupOf hAS]
    have hVA : V ≤ sL T L V ⊓ pCoreOf 2 (hz T V) :=
      le_inf v_le_sL (v_le_fsuU.trans fun u hu => (Subgroup.mem_inf.mp (C.fsuU_le_CU hu)).1)
    have h1 := Subgroup.relIndex_mul_card V (sL T L V ⊓ pCoreOf 2 (hz T V))
    rw [inf_eq_left.mpr hVA, C.card_v, C.card_sL_inf_QH] at h1
    omega
  set Wm : Set (Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) :=
    {x | (Multiplicative.toAdd x).trace = 0 ∧ IsStW (Multiplicative.toAdd x)} with hWm
  have hWm64 : Wm.ncard = 64 := by
    have e : Wm = Multiplicative.ofAdd '' ((Finset.univ.filter fun A : Matrix (Fin 3) (Fin 3)
        (ZMod 2) => A.trace = 0 ∧ IsStW A : Finset _) : Set (Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
      ext x
      simp only [hWm, Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ,
        true_and]
      exact ⟨fun h => ⟨_, h, ofAdd_toAdd x⟩, by rintro ⟨A, hA, rfl⟩; exact hA⟩
    rw [e, Set.ncard_image_of_injective _ Multiplicative.ofAdd.injective, Set.ncard_coe_finset,
      st_card_W]
  have hWsub : Wm ⊆ (χA : Set _) := by
    intro x hx
    obtain ⟨htr, hW⟩ := hx
    obtain ⟨hB, hCc, hdec⟩ := st_W_decomp _ htr hW
    obtain ⟨sB, hsB⟩ := hχs _ hB
    obtain ⟨sC, hsC⟩ := hχs _ hCc
    obtain ⟨w₁, -, hw₁Q, hw₁⟩ := hcomm q₁ hq₁ sB
    obtain ⟨w₂, -, hw₂Q, hw₂⟩ := hcomm q₂ hq₂ sC
    refine ⟨w₁ * w₂, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
      ⟨(w₁ * w₂).2, by simpa using mul_mem hw₁Q hw₂Q⟩), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [map_mul, toAdd_mul, hw₁, hw₂, hθq₁, hθq₂, hsB, hsC, toAdd_ofAdd, toAdd_ofAdd]
    exact hdec.symm
  have hWeq : Wm = (χA : Set _) := Set.eq_of_subset_of_ncard_le hWsub
    (by rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hχA64, hWm64]) (Set.toFinite _)
  have hUS : fsuU T V ≤ sL T L V := le_conjClosure _ _
  set χU := ((fsuU T V).subgroupOf (sL T L V)).map χ with hχU
  have hχU4 : Nat.card ↥χU = 4 := by
    rw [hχU, ← Subgroup.relIndex_ker, hχk, Subgroup.relIndex_subgroupOf hUS]
    have h1 := Subgroup.relIndex_mul_card V (fsuU T V)
    rw [inf_eq_left.mpr v_le_fsuU, C.card_v, C.card_fsuU] at h1
    omega
  set Cm : Set (Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) :=
    {x | (Multiplicative.toAdd x).trace = 0 ∧ IsStC (Multiplicative.toAdd x)} with hCm
  have hCm4 : Cm.ncard = 4 := by
    have e : Cm = Multiplicative.ofAdd '' ((Finset.univ.filter fun A : Matrix (Fin 3) (Fin 3)
        (ZMod 2) => A.trace = 0 ∧ IsStC A : Finset _) : Set (Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
      ext x
      simp only [hCm, Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ,
        true_and]
      exact ⟨fun h => ⟨_, h, ofAdd_toAdd x⟩, by rintro ⟨A, hA, rfl⟩; exact hA⟩
    rw [e, Set.ncard_image_of_injective _ Multiplicative.ofAdd.injective, Set.ncard_coe_finset,
      st_card_C]
  have hfixU : ∀ (q : ↥L), (q : G) ∈ pCoreOf 2 (hz T V) → ∀ u : ↥(sL T L V),
      (u : G) ∈ fsuU T V → RuType.stAct (θ q) (Multiplicative.toAdd (χ u)) =
        Multiplicative.toAdd (χ u) := by
    intro q hq u hu
    obtain ⟨w, hw, -, hwχ⟩ := hcomm q hq u
    have hwV : (w : G) ∈ V := by
      rw [hw]
      exact (Subgroup.mem_inf.mp (C.comm_mem_fsuV1 hq hu)).1
    rw [(hχ1 w).mpr hwV, toAdd_one] at hwχ
    exact (sub_eq_zero.mp hwχ.symm)
  have hUsub : (χU : Set _) ⊆ Cm := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨hχt u, ?_, ?_⟩
    · rw [← hθq₁]
      exact hfixU q₁ hq₁ u (Subgroup.mem_subgroupOf.mp hu)
    · rw [← hθq₂]
      exact hfixU q₂ hq₂ u (Subgroup.mem_subgroupOf.mp hu)
  have hUeq : (χU : Set _) = Cm := Set.eq_of_subset_of_ncard_le hUsub
    (by rw [hCm4, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hχU4]) (Set.toFinite _)
  refine ⟨θ, χ, hθs, hθk, hθLl, hχk, hχt, hχs, hχe, fun A hA hC => ?_, fun s hs => ?_⟩
  · have : Multiplicative.ofAdd A ∈ Cm := ⟨by simpa using hA, by simpa using hC⟩
    rw [← hUeq] at this
    obtain ⟨u, hu, hux⟩ := this
    exact ⟨u, Subgroup.mem_subgroupOf.mp hu, hux⟩
  · have : χ s ∈ Wm := by
      rw [hWeq]
      exact ⟨s, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨s.2, hs⟩), rfl⟩
    exact this.2

theorem comm_mem_fsuU_QH {b a : G} (hb : b ∈ pCoreOf 2 (hz T V))
    (ha : a ∈ sL T L V ⊓ pCoreOf 2 (hz T V)) : b * a * b⁻¹ * a⁻¹ ∈ fsuU T V := by
  obtain ⟨θ, χ, hθs, -, hθLl, hχk, hχt, -, hχe, hχU, hχW⟩ := C.exists_theta_chi
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hQT : pCoreOf 2 (hz T V) ≤ T := pCoreOf_le_of_le C.hyp hTH
  have hQL : pCoreOf 2 (hz T V) ≤ L := hQT.trans C.T_le_L
  obtain ⟨haS, haQ⟩ := Subgroup.mem_inf.mp ha
  have hw : b * a * b⁻¹ * a⁻¹ ∈ sL T L V :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (C.T_le_normalizer_sL (hQT hb)) a).mp haS)
      (inv_mem haS)
  have hwχ := chi_comm hχe ⟨b, hQL hb⟩ ⟨a, haS⟩ hw
  have haW := hχW ⟨a, haS⟩ haQ
  have hwC : IsStC (Multiplicative.toAdd (χ ⟨_, hw⟩)) := by
    rw [hwχ]
    rcases C.theta_QH_mem hθs hθLl ⟨b, hQL hb⟩ hb with h | h | h | h
    · rw [h]
      have : RuType.stAct 1 (Multiplicative.toAdd (χ ⟨a, haS⟩)) =
          Multiplicative.toAdd (χ ⟨a, haS⟩) := by simp [RuType.stAct]
      rw [this, sub_self]
      exact st_C_zero
    · rw [h]; exact haW.1
    · rw [h]; exact haW.2
    · rw [h]; exact st_W_u12 _ haW
  obtain ⟨u, hu, hux⟩ := hχU _ (hχt _) hwC
  have hk : (u⁻¹ * ⟨_, hw⟩ : ↥(sL T L V)) ∈ χ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hux, ofAdd_toAdd]
    exact inv_mul_cancel _
  rw [hχk, Subgroup.mem_subgroupOf] at hk
  have e : b * a * b⁻¹ * a⁻¹ = (u : G) * ((u⁻¹ * ⟨_, hw⟩ : ↥(sL T L V)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact mul_mem hu (v_le_fsuU hk)

end Ctx73

end CFSG.Quasithin.H13.L32A
