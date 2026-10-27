module

public import CFSG.Quasithin.H13.L32AL24

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups commutatorElement

@[expose] def Remark14_7_64 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    ⁅fsuU T V, pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)⁆ ⊔ fsuV1 T V = V ⊔ L32A.u0 T V ∧
    (∀ s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), s ∉ pCoreOf 2 (L32A.hz T V) →
      ∀ u ∈ fsuU T V, u * s * u⁻¹ * s⁻¹ ∈ L32A.u0 T V → u * s * u⁻¹ * s⁻¹ ∈ fsuV1 T V) ∧
    Nat.card ↥(L32A.u0 T V) ≤ 8 ∧
    (Nat.card ↥(L32A.u0 T V) = 8 →
      (∀ s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), s ∉ pCoreOf 2 (L32A.hz T V) →
        ∀ u ∈ fsuU T V, u * s * u⁻¹ * s⁻¹ ∈ V → u * s * u⁻¹ * s⁻¹ ∈ fsuV1 T V) ∧
      ∀ f ∈ V ⊔ L32A.u0 T V, f ∈ V ∨ f ∈ L32A.u0 T V ∨
        ∃ s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), s ∉ pCoreOf 2 (L32A.hz T V) ∧
          ∃ u ∈ fsuU T V, f * (u * s * u⁻¹ * s⁻¹)⁻¹ ∈ fsuV1 T V) ∧
    (Nat.card ↥(L32A.u0 T V) = 4 →
      (∀ s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), s ∉ pCoreOf 2 (L32A.hz T V) →
        (∃ u ∈ fsuU T V, u * s * u⁻¹ * s⁻¹ ∈ V ∧ u * s * u⁻¹ * s⁻¹ ∉ fsuV1 T V) ∧
        ∀ u₁ ∈ fsuU T V, ∀ u₂ ∈ fsuU T V, u₁ * s * u₁⁻¹ * s⁻¹ ∈ V →
          u₂ * s * u₂⁻¹ * s⁻¹ ∈ V → u₁ * s * u₁⁻¹ * s⁻¹ ∈ fsuV1 T V ∨
            u₂ * s * u₂⁻¹ * s⁻¹ ∈ fsuV1 T V ∨
            (u₁ * s * u₁⁻¹ * s⁻¹) * (u₂ * s * u₂⁻¹ * s⁻¹)⁻¹ ∈ fsuV1 T V) ∧
      ∀ f ∈ V ⊔ L32A.u0 T V, f ∈ L32A.u0 T V ∨
        ∃ s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), s ∉ pCoreOf 2 (L32A.hz T V) ∧
          ∃ u ∈ fsuU T V, f * (u * s * u⁻¹ * s⁻¹)⁻¹ ∈ fsuV1 T V)

namespace L32A

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem commutator_sup_le {U V₁ X Q : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V₁ : Set G))
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hQ : ∀ q ∈ Q, ∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ V₁) : ⁅U, X ⊔ Q⁆ ≤ ⁅U, X⁆ ⊔ V₁ := by
  rw [Subgroup.commutator_le]
  intro u hu y hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXQ] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy
  have h1 : u * b * u⁻¹ * b⁻¹ ∈ V₁ := by
    have := inv_mem (hQ b hb u hu)
    rwa [show (b * u * b⁻¹ * u⁻¹)⁻¹ = u * b * u⁻¹ * b⁻¹ by group] at this
  have h2 : a * (u * b * u⁻¹ * b⁻¹) * a⁻¹ ∈ V₁ :=
    (Subgroup.mem_normalizer_iff.mp (hXV ha) _).mp h1
  rw [show ⁅u, a * b⁆ = ⁅u, a⁆ * (a * (u * b * u⁻¹ * b⁻¹) * a⁻¹) by
    simp only [commutatorElement_def]; group]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu ha))
    (Subgroup.mem_sup_right h2)

theorem sl24_fix_comm_exists : ∀ A : SL(2, F4), A ^ 2 = 1 → A ≠ 1 → ∀ w : Fin 2 → F4,
    (A : Matrix (Fin 2) (Fin 2) F4).mulVec w = w →
      ∃ v, (A : Matrix (Fin 2) (Fin 2) F4).mulVec v + v = w := by
  decide +kernel

theorem f4_key3 : ∀ a v : Fin 2 → F4, a + v + -(a + -v) = 0 := by
  decide

theorem pCoreOf_hz_le_R1 (h : Hyp147 G T L V) (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) :
    pCoreOf 2 (hz T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ hz T V := hF.T_le_H
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_of_le h hTH).trans le_sup_right)
    (hF.L₁T_le_H.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem mem_sup_u0_of_comm_mem (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {s : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) {u : G} (hu : u ∈ fsuU T V)
    (hus : s * u * s⁻¹ * u⁻¹ ∈ fsuV1 T V) : u ∈ V ⊔ u0 T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  obtain ⟨hR1KQ, -⟩ := R1_le_kz_sup S0 hF h63 h1222 h1332 h1334
  obtain ⟨hKU, π, β, -, hπk, hβs, hβk, hβe⟩ := isL24Section_u0 h hMod h63
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hV1U0 := fsuV1_le_u0 h hMod
  have hHV1 : hz T V ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  have hQR := pCoreOf_hz_le_R1 h hF
  have hKQ : kz T V ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    (oTwoUpper_le _).trans (le_normalizer_pCoreOf 2 _)
  have hs' := hR1KQ hs
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKQ] at hs'
  obtain ⟨k, hk, q, hq, rfl⟩ := hs'
  have hkH : k ∈ hz T V := oTwoUpper_le _ hk
  have hqC : q ∈ centralizerMod (fsuV1 T V) (hz T V) (conjClosure V (hz T V)) := by
    rw [← hF.pCoreOf_eq_centralizerMod]
    exact hq
  have hUeq : fsuU T V = conjClosure V (hz T V) := fsuU_eq_conjClosure_hz hMod h
  have hqu : q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V := hqC.2.2 u (hUeq ▸ hu)
  have hku : k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V := by
    have h1 : k * (q * u * q⁻¹ * u⁻¹) * k⁻¹ ∈ fsuV1 T V :=
      (Subgroup.mem_normalizer_iff.mp (hHV1 hkH) _).mp hqu
    rw [show k * u * k⁻¹ * u⁻¹ = (k * (q * u * q⁻¹ * u⁻¹) * k⁻¹)⁻¹ *
      (k * q * u * (k * q)⁻¹ * u⁻¹) by group]
    exact mul_mem (inv_mem h1) hus
  have hkR : k ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    rw [show k = k * q * q⁻¹ by group]
    exact mul_mem hs (inv_mem (hQR hq))
  have hπ2 : π ⟨k, hk⟩ ^ 2 = 1 := by
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (L₁Of L (fsuV1 T V) ⊔ T)) ⟨k, hkR⟩
    have hk2 : k ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine sl24_sq_of_two_pow _ n ?_
    rw [← map_pow]
    have : (⟨k, hk⟩ : ↥(kz T V)) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hk2)
    rw [this, map_one]
  have hπ1 : π ⟨k, hk⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨k, hk⟩ : ↥(kz T V)) ∈ π.ker := h1
    rw [hπk, Subgroup.mem_subgroupOf] at h2
    have hkQ : k ∈ pCoreOf 2 (hz T V) :=
      A4.pCoreOf_le_of_subnormal 2 (A4.subnormal_of_normal (oTwoUpper_le _)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le _)).mpr
          (le_normalizer_oTwoUpper _))) h2
    exact hsQ (mul_mem hkQ hq)
  have hku' : k * u * k⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp (hKU hk) u).mp hu
  have hfix : (π ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) F4).mulVec
      (Multiplicative.toAdd (β ⟨u, hu⟩)) = Multiplicative.toAdd (β ⟨u, hu⟩) := by
    have e1 := hβe ⟨k, hk⟩ ⟨u, hu⟩ ⟨_, hku'⟩ rfl
    have hc : (⟨k * u * k⁻¹, hku'⟩ : ↥(fsuU T V)) =
        ⟨k * u * k⁻¹ * u⁻¹, hU0U (hV1U0 hku)⟩ * ⟨u, hu⟩ := Subtype.ext (by simp)
    have hc1 : β ⟨k * u * k⁻¹ * u⁻¹, hU0U (hV1U0 hku)⟩ = 1 :=
      (l24_ker_iff hβk _).mpr (hV1U0 hku)
    rw [hc, map_mul, hc1, one_mul] at e1
    have := congrArg Multiplicative.toAdd e1
    rw [toAdd_ofAdd] at this
    exact this.symm
  obtain ⟨v, hv⟩ := sl24_fix_comm_exists _ hπ2 hπ1 _ hfix
  obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd v)
  have hkw' : k * (w : G) * k⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp (hKU hk) w).mp w.2
  have hcomm : k * (w : G) * k⁻¹ * (w : G)⁻¹ ∈ V ⊔ u0 T V := by
    have h1 := commutator_le_sup_u0 h hMod h63 hF h1222 h1332 h1334
      (Subgroup.commutator_mem_commutator w.2 hkR)
    have h2 := inv_mem h1
    rwa [commutatorElement_def, show ((w : G) * k * (w : G)⁻¹ * k⁻¹)⁻¹ =
      k * (w : G) * k⁻¹ * (w : G)⁻¹ by group] at h2
  have hmem : u * (k * (w : G) * k⁻¹ * (w : G)⁻¹)⁻¹ ∈ fsuU T V :=
    mul_mem hu (inv_mem (mul_mem hkw' (inv_mem w.2)))
  have h0 : u * (k * (w : G) * k⁻¹ * (w : G)⁻¹)⁻¹ ∈ u0 T V := by
    refine (l24_ker_iff hβk ⟨_, hmem⟩).mp ?_
    have e2 := hβe ⟨k, hk⟩ w ⟨_, hkw'⟩ rfl
    have e3 : (⟨u * (k * (w : G) * k⁻¹ * (w : G)⁻¹)⁻¹, hmem⟩ : ↥(fsuU T V)) =
        ⟨u, hu⟩ * (⟨_, hkw'⟩ * w⁻¹)⁻¹ := Subtype.ext (by simp)
    rw [e3, map_mul, map_inv, map_mul, map_inv, e2, hw]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_one]
    rw [← hv]
    exact f4_key3 _ _
  rw [show u = (u * (k * (w : G) * k⁻¹ * (w : G)⁻¹)⁻¹) * (k * (w : G) * k⁻¹ * (w : G)⁻¹) by
    group]
  exact mul_mem (Subgroup.mem_sup_right h0) hcomm

end L32A

end CFSG.Quasithin.H13
