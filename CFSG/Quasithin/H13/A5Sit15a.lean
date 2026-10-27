module

public import CFSG.Quasithin.H13.A5Sit

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5 (exists_not_isPGroup_mod_of_not_mem le_normalizer_commutator
  perm3_normal_pgroup_eq_bot)

namespace A5Sit

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  (S : A5Sit G T V V₁ V₃ L₁ H)
include S

theorem commutator_UH_L1 (hn : H ≤ Subgroup.normalizer (L₁ : Set G)) :
    ⁅conjClosure V₃ H, L₁⁆ = conjClosure V₃ H := by
  have hL1H : L₁ ≤ H := S.L1_le_H
  have hUN : H ≤ Subgroup.normalizer (conjClosure V₃ H : Set G) := le_normalizer_conjClosure _ _
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro u hu l hl
    have : l * u⁻¹ * l⁻¹ ∈ conjClosure V₃ H :=
      (Subgroup.mem_normalizer_iff.mp (hUN (hL1H hl)) _).mp (Subgroup.inv_mem _ hu)
    rw [commutatorElement_def]
    have e : u * l * u⁻¹ * l⁻¹ = u * (l * u⁻¹ * l⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hu this
  · have hN := le_normalizer_commutator (A := conjClosure V₃ H) (B := L₁) hUN hn
    refine conjClosure_le fun h hh x hx => ?_
    have hx' : x ∈ ⁅conjClosure V₃ H, L₁⁆ :=
      Subgroup.commutator_mono (le_conjClosure _ _) le_rfl (S.commutator_V3_L1.ge hx)
    exact (Subgroup.mem_normalizer_iff.mp (hN hh) x).mp hx'

theorem UH_le_L1 (hn : H ≤ Subgroup.normalizer (L₁ : Set G)) : conjClosure V₃ H ≤ L₁ := by
  rw [← S.commutator_UH_L1 hn, Subgroup.commutator_le]
  intro u hu l hl
  have huN : u ∈ Subgroup.normalizer (L₁ : Set G) :=
    hn ((S.U_le_Q.trans (pCoreOf_le 2 H)) hu)
  have : u * l * u⁻¹ ∈ L₁ := (Subgroup.mem_normalizer_iff.mp huN l).mp hl
  rw [commutatorElement_def]
  exact L₁.mul_mem this (L₁.inv_mem hl)

theorem pCoreOf_L1_le (hn : H ≤ Subgroup.normalizer (L₁ : Set G)) :
    pCoreOf 2 L₁ ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans S.L1_le_H)
    (hn.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem F956_data (hF956 : A5.StmtF956i) :
    ∃ h ∈ H, IsQ8Sq ↥(V₃ ⊔ conjSub h⁻¹ V₃) ∧
      (∃ _ : ((pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V)).Normal,
        Nonempty (↥(V ⊔ conjSub h⁻¹ V) ⧸ (pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V) ≃*
          Equiv.Perm (Fin 3))) ∧
      (V ⊔ conjSub h⁻¹ V) ⊓ pCoreOf 2 H = V₃ ⊔ conjSub h⁻¹ V₃ := by
  have hV := S.not_V_le
  obtain ⟨v, hvV, hvQ⟩ := IsConcreteLE.not_le_iff_exists.1 hV
  obtain ⟨g, hgH, y, hy, hyQ⟩ :=
    exists_not_isPGroup_mod_of_not_mem (S.V_le_H hvV) (S.elemAbelian_V.2 v hvV) hvQ
  have hcl : Subgroup.closure ({v, g * v * g⁻¹} : Set G) ≤ V ⊔ conjSub (g⁻¹)⁻¹ V := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_sup_left hvV
    · refine Subgroup.mem_sup_right ?_
      rw [inv_inv, mem_conjSub]
      simpa [mul_assoc] using hvV
  have hI : ¬ (∀ x ∈ V ⊔ conjSub (g⁻¹)⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H) := by
    intro hall
    obtain ⟨n, hn⟩ := hall y (hcl hy)
    exact hyQ n hn
  obtain ⟨hQ8, hS3⟩ := S.F956 hF956 (H.inv_mem hgH) hI
  exact ⟨g⁻¹, H.inv_mem hgH, hQ8, hS3, S.hF.F95_UI_eq S.relIndex_V3 hV (H.inv_mem hgH)⟩

omit [Finite G] S in
theorem UI_le_UH {h : G} (hh : h ∈ H) : V₃ ⊔ conjSub h⁻¹ V₃ ≤ conjClosure V₃ H := by
  refine sup_le (le_conjClosure _ _) fun x hx => ?_
  rw [mem_conjSub, inv_inv] at hx
  have := mem_conjClosure (H.inv_mem hh) hx
  simpa [mul_assoc] using this

theorem I_data (hUQ8 : IsQ8Sq ↥(conjClosure V₃ H)) {h : G} (hh : h ∈ H)
    (hQ8 : IsQ8Sq ↥(V₃ ⊔ conjSub h⁻¹ V₃))
    (hS3 : ∃ _ : ((pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V)).Normal,
      Nonempty (↥(V ⊔ conjSub h⁻¹ V) ⧸ (pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V) ≃*
        Equiv.Perm (Fin 3)))
    (hUI : (V ⊔ conjSub h⁻¹ V) ⊓ pCoreOf 2 H = V₃ ⊔ conjSub h⁻¹ V₃) :
    V₃ ⊔ conjSub h⁻¹ V₃ = conjClosure V₃ H ∧
      pCoreOf 2 (V ⊔ conjSub h⁻¹ V) = conjClosure V₃ H ∧
      Nat.card (pCoreOf 2 (V ⊔ conjSub h⁻¹ V)) = 32 ∧
      Nonempty (oTwoQuot ↥(V ⊔ conjSub h⁻¹ V) ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := V ⊔ conjSub h⁻¹ V with hIdef
  have hUIeq : V₃ ⊔ conjSub h⁻¹ V₃ = conjClosure V₃ H :=
    Subgroup.eq_of_le_of_card_ge (UI_le_UH hh) (by rw [hQ8.1, hUQ8.1])
  have hIH : I ≤ H := sup_le S.V_le_H (S.hF.conjSub_inv_le_H hh)
  have hO2 : pCoreOf 2 I = I ⊓ pCoreOf 2 H := by
    apply le_antisymm
    ·
      obtain ⟨hNorm, ⟨e⟩⟩ := hS3
      have hP :
          (CFSG.Open.pCore 2 ↥I).map (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)) = ⊥ := by
        have hnorm : ((CFSG.Open.pCore 2 ↥I).map
            (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I))).Normal :=
          Subgroup.Normal.map (CFSG.LieType.BorelTits.pCore_normal 2) _
            (QuotientGroup.mk'_surjective _)
        have hpg : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥I).map
            (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I))) :=
          (CFSG.LieType.BorelTits.pCore_isPGroup 2).map _
        have h1 : ((CFSG.Open.pCore 2 ↥I).map
            (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I))).map e.toMonoidHom = ⊥ := by
          have : ((((CFSG.Open.pCore 2 ↥I).map
              (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I))).map e.toMonoidHom)).Normal :=
            Subgroup.Normal.map hnorm _ e.surjective
          exact perm3_normal_pgroup_eq_bot _ (hpg.map _)
        rw [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h1
        exact h1
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      have hx1 : (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)) x = 1 := by
        have : (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)) x ∈
            (CFSG.Open.pCore 2 ↥I).map (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)) :=
          ⟨x, hx, rfl⟩
        rw [hP, Subgroup.mem_bot] at this
        exact this
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx1
      exact hx1
    · refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxI, hxQ⟩
        exact ⟨I.mul_mem (I.mul_mem hy hxI) (I.inv_mem hy),
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hIH hy)) x).mp hxQ⟩
      · rintro ⟨hxI, hxQ⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hIH hy)) x).mpr
          hxQ⟩
        have := I.mul_mem (I.mul_mem (I.inv_mem hy) hxI) hy
        simpa [mul_assoc] using this
  have hO2' : pCoreOf 2 I = conjClosure V₃ H := by rw [hO2, hUI, hUIeq]
  refine ⟨hUIeq, hO2', by rw [hO2', hUQ8.1], ?_⟩
  obtain ⟨hNorm, ⟨e⟩⟩ := hS3
  have hsub : CFSG.Open.pCore 2 ↥I = (pCoreOf 2 H).subgroupOf I := by
    have h1 : (pCoreOf 2 I).subgroupOf I = CFSG.Open.pCore 2 ↥I := by
      show ((CFSG.Open.pCore 2 ↥I).map I.subtype).subgroupOf I = _
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective I.subtype_injective]
    rw [← h1, hO2]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hsub).trans e⟩

end A5Sit

end CFSG.Quasithin.H13
