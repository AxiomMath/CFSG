module

public import CFSG.Quasithin.Background.SmithC27RCaseIIEightBY
public import CFSG.Quasithin.Background.C1PackC127Aux

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

namespace CaseIICtx

variable (C : CaseIICtx R K V 8) (hs : StarHyp R K V)

theorem exists_rho_mem_block (h : Hyp27 H R M K) {L : Subgroup G}
    (hL : IsChi0Block (C.yB8 hs) L) :
    ∃ ρ ∈ L, ∃ hρ : ρ ∈ K,
      C.phiB8 hs.le_normalizer_V ⟨ρ, Subgroup.mem_sup_left hρ⟩ = c3B8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := C.isAltType_three_B8 hs hL
  obtain ⟨-, -, -, -, -, -, c, hcL, hc3, -⟩ := hL.1.1.alt3_structure h3
  have hcX : c ∈ K ⊔ R := (hL.1.2.1.trans (C.yB8_le hs)) hcL
  have hcK : c ∈ K := by
    obtain ⟨k, hk⟩ := h.exists_pow_mem hcX
    have hcop : (2 ^ k).gcd (orderOf c) = 1 := by
      rw [hc3]
      exact Nat.Coprime.pow_left k (by decide)
    exact (Subgroup.zpowers_le.2 hk) (mem_zpowers_pow_iff.2 hcop)
  have hcS : C.phiB8 hs.le_normalizer_V ⟨c, hcX⟩ ∈ s3B8 :=
    ((C.mem_yB8_iff hs).1 (hL.1.2.1 hcL)).2
  have hc3' : (C.phiB8 hs.le_normalizer_V ⟨c, hcX⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have hpow : (⟨c, hcX⟩ : ↥(K ⊔ R)) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hc3, pow_orderOf_eq_one]
      rfl
    rw [hpow, map_one]
  rcases s3B8_pow_three hcS hc3' with h1 | h1 | h1
  · exfalso
    have hcC := (C.phiB8_eq_one_iff hs.le_normalizer_V ⟨c, hcX⟩).1 h1
    have hcQ : c ∈ pCoreOf 2 (K ⊔ R) := by
      rw [← C.inf_centralizer_eq_B8 hs]
      exact ⟨hcX, hcC⟩
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ R) ⟨c, hcQ⟩
    have hdvd : orderOf c ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    rw [hc3] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  · exact ⟨c, hcL, hcK, h1⟩
  · refine ⟨c⁻¹, L.inv_mem hcL, K.inv_mem hcK, ?_⟩
    have hinv : (⟨c⁻¹, Subgroup.mem_sup_left (K.inv_mem hcK)⟩ : ↥(K ⊔ R)) =
        (⟨c, hcX⟩ : ↥(K ⊔ R))⁻¹ := rfl
    rw [hinv, map_inv, h1, inv_inv]

theorem exists_rho_B8 (hC129 : ASC129Statement G) (h : Hyp27 H R M K)
    (hR : C.bar R = Subgroup.zpowers (swap 0 1)) :
    ∃ ρ : G, ∃ hρ : ρ ∈ K,
      C.phiB8 hs.le_normalizer_V ⟨ρ, Subgroup.mem_sup_left hρ⟩ = c3B8 ∧
      ∀ q ∈ pCoreOf 2 (K ⊔ R), ∃ v ∈ V, q * ρ * q⁻¹ * ρ⁻¹ = v * ρ * v⁻¹ * ρ⁻¹ := by
  classical
  obtain ⟨L, hL⟩ := C.exists_chi0Block_B8 hs hC129 h hR
  obtain ⟨ρ, hρL, hρK, hρφ⟩ := C.exists_rho_mem_block hs h hL
  refine ⟨ρ, hρK, hρφ, ?_⟩
  obtain ⟨hQU, hU4, -⟩ := hL.1.1.alt3_structure (C.isAltType_three_B8 hs hL)
  have hL4 : Nat.card (pCoreOf 2 L) = 4 := by
    have hQ : blockQ L = pCoreOf 2 L := rfl
    rw [← hQ, hQU, hU4]
  have hQY := C.pCore_le_pCore_yB8 hs hR
  have hcomm : ∀ q ∈ pCoreOf 2 (K ⊔ R), q * ρ * q⁻¹ * ρ⁻¹ ∈ pCoreOf 2 L := fun q hq =>
    C1Pack.commutator_mem_pCoreOf_block hL.1 (hQY hq) hρL
  have hVQ : V ≤ pCoreOf 2 (K ⊔ R) := C124.le_pCoreOf_of_reduced hs.red
  set gX : ↥(autOn (K ⊔ R) V) := starB8 hs.le_normalizer_V ⟨ρ, Subgroup.mem_sup_left hρK⟩
    with hgX
  have hιg : C.ι gX = c3B8 := hρφ
  set gI : MulAut (IntMod V C.hV) := ((gX : MulAut ↥V) : MulAut (IntMod V C.hV)) with hgI
  have hgN : gI ∈ Subgroup.normalizer (autI C.hV K : Set (MulAut (IntMod V C.hV))) :=
    C124.YZ.autI_normalizes C.hV hs.le_normalizer gX.2
  have hmem : ∀ u : ↥(commV (autI C.hV K)), gI (u : IntMod V C.hV) ∈ commV (autI C.hV K) :=
    fun u => C124.YZ.apply_mem_commV hgN u.2
  let E : ↥(commV (autI C.hV K)) → ↥(commV (autI C.hV K)) := fun u => u * (⟨_, hmem u⟩)⁻¹
  have hEβ : ∀ u, C.β (E u) = C.β u * (C124.YZ.dAct 8 c3B8 (C.β u))⁻¹ := by
    intro u
    have he : C.β ⟨gI (u : IntMod V C.hV), hmem u⟩ = C124.YZ.dAct 8 c3B8 (C.β u) := by
      rw [← hιg]
      exact C.β_equiv gX u (hmem u)
    show C.β (u * (⟨_, hmem u⟩)⁻¹) = _
    rw [map_mul, map_inv, he]
  have hEval : ∀ u, ((E u : ↥(commV (autI C.hV K))) : IntMod V C.hV).val =
      (u : IntMod V C.hV).val * ρ * ((u : IntMod V C.hV).val)⁻¹ * ρ⁻¹ := by
    intro u
    have hg : (gI (u : IntMod V C.hV)).val = ρ * (u : IntMod V C.hV).val * ρ⁻¹ :=
      convI_apply_val C.hV ⟨ρ, hs.le_normalizer_V (Subgroup.mem_sup_left hρK)⟩ _
    show (u : IntMod V C.hV).val * (gI (u : IntMod V C.hV)).val⁻¹ = _
    rw [hg]
    group
  have hEmul : ∀ u₁ u₂, E (u₁ * u₂) = E u₁ * E u₂ := by
    intro u₁ u₂
    apply Subtype.ext
    show ((u₁ : IntMod V C.hV) * (u₂ : IntMod V C.hV)) *
        (gI ((u₁ : IntMod V C.hV) * (u₂ : IntMod V C.hV)))⁻¹ =
      ((u₁ : IntMod V C.hV) * (gI (u₁ : IntMod V C.hV))⁻¹) *
        ((u₂ : IntMod V C.hV) * (gI (u₂ : IntMod V C.hV))⁻¹)
    rw [map_mul, mul_inv, mul_mul_mul_comm]
  obtain ⟨u₁, hu₁⟩ := C.β_surj (C124.YZ.pairQ 0 3)
  obtain ⟨u₂, hu₂⟩ := C.β_surj (C124.YZ.pairQ 1 3)
  obtain ⟨hw₁, hw₂, hw₁₂⟩ := dm8_c3_facts
  have hβ₁ := hEβ u₁
  have hβ₂ := hEβ u₂
  rw [hu₁] at hβ₁
  rw [hu₂] at hβ₂
  have hβ₃ : C.β (E (u₁ * u₂)) = C.β (E u₁) * C.β (E u₂) := by rw [hEmul, map_mul]
  have hne : ∀ e e' : ↥(commV (autI C.hV K)), C.β e ≠ C.β e' →
      ((e : IntMod V C.hV)).val ≠ ((e' : IntMod V C.hV)).val := by
    intro e e' hβ hval
    exact hβ (congrArg C.β (Subtype.ext (IntMod.val_injective hval)))
  have h1v : ((1 : ↥(commV (autI C.hV K))) : IntMod V C.hV).val = 1 := rfl
  have hinv₂ := inv_eq_of_mul_eq_one_right (dm8_mul_self (C.β (E u₂)))
  have h01 := hne 1 (E u₁) (by rw [map_one, hβ₁]; exact hw₁.symm)
  have h02 := hne 1 (E u₂) (by rw [map_one, hβ₂]; exact hw₂.symm)
  have h03 := hne 1 (E (u₁ * u₂)) (by
    rw [map_one, hβ₃]
    intro h3
    exact hw₁₂ (by rw [← hβ₁, ← hβ₂, eq_inv_of_mul_eq_one_left h3.symm, hinv₂]))
  have h12 := hne (E u₁) (E u₂) (by rw [hβ₁, hβ₂]; exact hw₁₂)
  have h13 := hne (E u₁) (E (u₁ * u₂)) (by
    rw [hβ₃]
    intro h3
    exact hw₂ (by rw [← hβ₂]; exact (mul_eq_left.1 h3.symm)))
  have h23 := hne (E u₂) (E (u₁ * u₂)) (by
    rw [hβ₃]
    intro h3
    exact hw₁ (by rw [← hβ₁]; exact (mul_eq_right.1 h3.symm)))
  rw [h1v] at h01 h02 h03
  set b₁ := ((E u₁ : ↥(commV (autI C.hV K))) : IntMod V C.hV).val with hb₁
  set b₂ := ((E u₂ : ↥(commV (autI C.hV K))) : IntMod V C.hV).val with hb₂
  set b₃ := ((E (u₁ * u₂) : ↥(commV (autI C.hV K))) : IntMod V C.hV).val with hb₃
  have hcard : ({1, b₁, b₂, b₃} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h23]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h12, h13⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h01, h02, h03⟩
  have hbL : ∀ u, ((E u : ↥(commV (autI C.hV K))) : IntMod V C.hV).val ∈ pCoreOf 2 L := by
    intro u
    rw [hEval]
    exact hcomm _ (hVQ (IntMod.val_mem _))
  have hsub : (({1, b₁, b₂, b₃} : Finset G) : Set G) ⊆ (pCoreOf 2 L : Set G) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (pCoreOf 2 L).one_mem
    · exact hbL u₁
    · exact hbL u₂
    · exact hbL (u₁ * u₂)
  have hEq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_coe_finset, hcard, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hL4])
    (Set.toFinite _)
  intro q hq
  have hqS : q * ρ * q⁻¹ * ρ⁻¹ ∈ (({1, b₁, b₂, b₃} : Finset G) : Set G) := by
    rw [hEq]
    exact hcomm q hq
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hqS
  rcases hqS with h0 | h1 | h2 | h3
  · exact ⟨1, V.one_mem, by rw [h0]; group⟩
  · exact ⟨_, IntMod.val_mem _, h1.trans (hEval u₁)⟩
  · exact ⟨_, IntMod.val_mem _, h2.trans (hEval u₂)⟩
  · exact ⟨_, IntMod.val_mem _, h3.trans (hEval (u₁ * u₂))⟩

end CaseIICtx

end CFSG.Quasithin.SmithC27
