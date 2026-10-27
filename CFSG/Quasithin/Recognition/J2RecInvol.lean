module

public import CFSG.Quasithin.Recognition.J2RecCzAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.LieType.BorelTits J2Cz J2Cz.QM
open scoped Pointwise

theorem J2Cz.QM.exists_conj_signed : ∀ k : Fin 5, ∀ a b : QM, (a = x k ∨ a = z * x k) →
    (b = x k ∨ b = z * x k) → ∃ q : QM, q * a * q⁻¹ = b := by
  decide +kernel

theorem exists_alt_apply_eq : ∀ j k : Fin 5,
    ∃ π : Perm (Fin 5), Perm.sign π = 1 ∧ π j = k := by
  decide +kernel

namespace IsTypeH2

variable {G : Type} [Group G] {z : G}

theorem exists_conj_of_noncentral (h : IsTypeH2 G z) {y y' : G}
    (hy : y ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hy2 : y * y = 1)
    (hy1 : y ≠ 1) (hyz : y ≠ z)
    (hy' : y' ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hy'2 : y' * y' = 1)
    (hy'1 : y' ≠ 1) (hy'z : y' ≠ z) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), c * y * c⁻¹ = y' := by
  obtain ⟨χ, hχz⟩ := h.exists_equiv_QM
  have hsigned : ∀ {w : G} (hw : w ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))),
      w * w = 1 → w ≠ 1 → w ≠ z → ∃ j, χ ⟨w, hw⟩ = x j ∨ χ ⟨w, hw⟩ = J2Cz.QM.z * x j := by
    intro w hw hw2 hw1 hwz
    refine eq_x_of_sq _ ?_ ?_ ?_
    · rw [← map_mul]
      have : (⟨w, hw⟩ * ⟨w, hw⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) = 1 :=
        Subtype.ext hw2
      rw [this, map_one]
    · intro h1
      apply hw1
      have : (⟨w, hw⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) = 1 :=
        χ.injective (h1.trans (map_one χ).symm)
      exact congrArg Subtype.val this
    · intro h1
      apply hwz
      rw [← hχz, ← h1, MulEquiv.symm_apply_apply]
  obtain ⟨j, hj⟩ := hsigned hy hy2 hy1 hyz
  obtain ⟨k, hk⟩ := hsigned hy' hy'2 hy'1 hy'z
  obtain ⟨π, hπ, hπj⟩ := exists_alt_apply_eq j k
  obtain ⟨g, hg⟩ := h.exists_linePerm_eq χ (Perm.mem_alternatingGroup.mpr hπ)
  have h1 := signed_map (czAct χ g) hj
  rw [hg, hπj] at h1
  obtain ⟨q, hq⟩ := exists_conj_signed k _ _ h1 hk
  set n := χ.symm q with hn
  have hnH : (n : G) ∈ Subgroup.centralizer ({z} : Set G) := pCoreOf_le 2 _ n.2
  refine ⟨n * g, mul_mem hnH g.2, ?_⟩
  have h2 : (g : G) * y * (g : G)⁻¹ =
      ((χ.symm (czAct χ g (χ ⟨y, hy⟩)) : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) :
        G) := by
    rw [czAct_apply, MulEquiv.symm_apply_apply]
  have h3 : y' = ((χ.symm (q * czAct χ g (χ ⟨y, hy⟩) * q⁻¹) :
      ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) : G) := by
    rw [hq, MulEquiv.symm_apply_apply]
  rw [h3, map_mul, map_mul, map_inv, ← hn]
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  rw [← h2]
  group

theorem isConj_of_mem_pCoreOf (h : IsTypeH2 G z) {y : G}
    (hy : y ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hy2 : y * y = 1)
    (hy1 : y ≠ 1) : IsConj z y := by
  by_cases hyz : y = z
  · rw [hyz]
  obtain ⟨g, hgQ, hgz⟩ := h.notWeaklyClosed
  have hz2 : z * z = 1 := by
    have := h.sq
    rwa [pow_two] at this
  have hg2 : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hg1 : g * z * g⁻¹ ≠ 1 := fun h1 => h.ne_one (by
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨c, -, hc⟩ := h.exists_conj_of_noncentral hgQ hg2 hg1 hgz hy hy2 hy1 hyz
  refine isConj_iff.mpr ⟨c * g, ?_⟩
  rw [← hc]
  group

theorem exists_not_isConj (h : IsTypeH2 G z) (hcount : involutionClassCount G = 2) :
    ∃ s : G, s ^ 2 = 1 ∧ s ≠ 1 ∧ ¬ IsConj z s := by
  by_contra hne
  push Not at hne
  have hset : {c : ConjClasses G | ∃ x : G, x ^ 2 = 1 ∧ x ≠ 1 ∧ ConjClasses.mk x = c} =
      {ConjClasses.mk z} := by
    ext c
    constructor
    · rintro ⟨x, hx2, hx1, rfl⟩
      exact Set.mem_singleton_iff.mpr (ConjClasses.mk_eq_mk_iff_isConj.mpr (hne x hx2 hx1)).symm
    · intro hc
      rw [Set.mem_singleton_iff.mp hc]
      exact ⟨z, h.sq, h.ne_one, rfl⟩
  rw [involutionClassCount, hset, Set.ncard_singleton] at hcount
  omega

theorem exists_involution_not_mem [Finite G] (h : IsTypeH2 G z)
    (hcount : involutionClassCount G = 2) :
    ∃ t ∈ Subgroup.centralizer ({z} : Set G), t * t = 1 ∧
      t ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs2, hs1, hsz⟩ := h.exists_not_isConj hcount
  set C := Subgroup.centralizer ({z} : Set G) with hC
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 2 ↥C))
  set S := (S₀ : Subgroup ↥C).map C.subtype with hS
  have hSsub : S.subgroupOf C = S₀ := by
    rw [hS, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
  have hSC : IsSylowTwoOf S C :=
    ⟨Subgroup.map_subtype_le _, S₀.isPGroup'.map _, by rw [hSsub]; exact S₀.not_dvd_index⟩
  obtain ⟨-, hS2, hSidx⟩ := h.isSylowTwoOf_top hSC
  have hSidx' : ¬ 2 ∣ S.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hSidx
  set P : Sylow 2 G := hS2.toSylow hSidx' with hP
  have hsp : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hs2 hs1, pow_one])
  obtain ⟨T, hT⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T P
  have h1 : MulAut.conj g s ∈ MulAut.conj g • (T : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hT (Subgroup.mem_zpowers s))
  rw [← Sylow.coe_subgroup_smul, hg, hP, IsPGroup.toSylow_coe] at h1
  have hgs : g * s * g⁻¹ ∈ S := by simpa [MulAut.conj_apply] using h1
  have hss : s * s = 1 := by rwa [pow_two] at hs2
  refine ⟨g * s * g⁻¹, hSC.1 hgs, ?_, fun hQ => hsz ?_⟩
  · calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      _ = 1 := by rw [hss]; group
  · have h2 := h.isConj_of_mem_pCoreOf hQ
      (by calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
            _ = 1 := by rw [hss]; group)
      (fun h3 => hs1 (by
        calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
          _ = 1 := by rw [h3]; group))
    exact h2.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)

end IsTypeH2

end CFSG.Quasithin
