module

public import CFSG.Milestones.ASVolI.F7

public section

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7

abbrev HypF_8_1 {G : Type} [Group G] (T V L V₁ H : Subgroup G) : Prop := HypF81 T V L V₁ H

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7
open CFSG.ASVolI.ChF
open scoped Pointwise

@[expose] def F_8_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ H : Subgroup G), HypF_8_1 T V L V₁ H →
    AlmostSpecialHyp V V₁ L T H ∧
    ((conjClosure V H ≤ pCoreOf 2 H ∧
        (∀ u ∈ conjClosure V H, ∀ q ∈ pCoreOf 2 H, u * q * u⁻¹ * q⁻¹ ∈ V₁) ∧
        ∀ u ∈ conjClosure V H, u ^ 2 ∈ V₁) ∧
      (∀ D : Subgroup G, D ≤ H → H ≤ Subgroup.normalizer (D : Set G) →
        (∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ centralizerMod V₁ H (conjClosure V H)) →
          D ≤ centralizerMod V₁ H (conjClosure V H)) ∧
      IsPGroup 2 (conjClosure V H)) ∧
    frattiniOf (conjClosure V H) ≤ V₁ ∧
    pCoreOf 2 H = centralizerMod V₁ H (conjClosure V H)

theorem as_F_8_2 : F_8_2 := by
  intro G _ _ T V L V₁ H h
  have h' : HypF81 T V L V₁ H := h
  exact ⟨h'.almostSpecialHyp, ⟨⟨h'.F82_1.1, h'.F82_1.2.1, h'.F82_1.2.2⟩,
    fun D hDH hHD hD => h'.F82_1_reduced hDH hHD hD, h'.isPGroup_conjClosure⟩,
    h'.F82_2, h'.F82_3⟩

@[expose] def F_8_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ H : Subgroup G), HypF_8_1 T V L V₁ H →
    HypF_7_6 ((L ⊔ T) ⊔ H) (L ⊔ T) H T V ∧ (L ⊔ T) ⊓ H = L₁Of L V₁ ⊔ T

theorem as_F_8_3 : F_8_3 := by
  intro G _ _ T V L V₁ H h
  have h' : HypF81 T V L V₁ H := h
  have hyp := h'.amalgamHypV
  have hyp1 : HypF_7_1 ((L ⊔ T) ⊔ H) (L ⊔ T) H T :=
    { finite₁ := inferInstance
      finite₂ := inferInstance
      charTwo := hyp.charTwo
      sylow_inf := AmalgamHyp.sylow_inf hyp.toAmalgamHyp
      sylow₁ := hyp.sylow₁
      sylow₂ := hyp.sylow₂
      gen := hyp.gen
      o2_trivial := hyp.o2_trivial }
  exact ⟨{ toHypF_7_1 := hyp1, reduced := hyp.reduced, cT := hyp.cT }, h'.LT_inf_H⟩

@[expose] def F_8_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ H : Subgroup G), HypF_8_1 T V L V₁ H →
    conjClosure V H = Vv V (F8.γ₁ T L H) ∧
    (∃ γ : F8.Geom T L H, IsCriticalVertex ((L ⊔ T) ⊔ H) (L ⊔ T) H V γ) ∧
    ∃ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g

theorem as_F_8_4 : F_8_4 := by
  intro G _ _ T V L V₁ H h
  have h' : HypF81 T V L V₁ H := h
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex h'.amalgamHypV (F8.V_ne_bot h')
  exact ⟨F8.conjClosure_eq_Vv_γ₁ h', ⟨γ, hγ⟩, F8.exists_F8Setup h'⟩

@[expose] def F_8_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ H : Subgroup G), HypF_8_1 T V L V₁ H →
    (3 ≤ F8.b T V L H ∧ Odd (F8.b T V L H)) ∧
    IsElemAbelian 2 (conjClosure V H)

theorem as_F_8_5 : F_8_5 := by
  intro G _ _ T V L V₁ H h
  exact ⟨F8.three_le_b_and_odd h, F8.isElemAbelian_conjClosure h⟩

@[expose] def F_8_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ H : Subgroup G) (γ γ' : F8.Geom T L H)
    (g : ↥((L ⊔ T) ⊔ H)), HypF_8_1 T V L V₁ H → F8Setup T V L H γ γ' g →
      conjSub (g : G) (L₁Of L V₁) = oTwoRes (stab γ' ⊓ stab γ)

private theorem f86_oTwoRes_mono {G : Type} [Group G] {A B : Subgroup G} (h : A ≤ B) :
    oTwoRes A ≤ oTwoRes B :=
  (Subgroup.closure_le _).mpr fun _ hx => Subgroup.subset_closure ⟨h hx.1, hx.2⟩

private theorem f86_oTwoRes_oTwoRes {G : Type} [Group G] (X : Subgroup G) :
    oTwoRes (oTwoRes X) = oTwoRes X :=
  le_antisymm (oTwoRes_le _) ((Subgroup.closure_le _).mpr fun x hx =>
    Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2⟩)

private theorem f86_oTwoRes_sup_le {G : Type} [Group G] [Finite G] {N T : Subgroup G}
    (hT : IsPGroup 2 T) (hTN : T ≤ Subgroup.normalizer (N : Set G)) :
    oTwoRes (N ⊔ T) ≤ N := by
  have hdec : ∀ x ∈ N ⊔ T, ∃ n ∈ N, ∃ t ∈ T, x = n * t := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro x (hx | hx)
      · exact ⟨x, hx, 1, T.one_mem, by simp⟩
      · exact ⟨1, N.one_mem, x, hx, by simp⟩
    · exact ⟨1, N.one_mem, 1, T.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨n₁, hn₁, t₁, ht₁, rfl⟩ ⟨n₂, hn₂, t₂, ht₂, rfl⟩
      refine ⟨n₁ * (t₁ * n₂ * t₁⁻¹), N.mul_mem hn₁ ?_, t₁ * t₂, T.mul_mem ht₁ ht₂, by group⟩
      exact (Subgroup.mem_normalizer_iff.mp (hTN ht₁) n₂).mp hn₂
    · rintro _ _ ⟨n, hn, t, ht, rfl⟩
      refine ⟨t⁻¹ * n⁻¹ * t⁻¹⁻¹, ?_, t⁻¹, T.inv_mem ht, by group⟩
      exact (Subgroup.mem_normalizer_iff.mp (hTN (T.inv_mem ht)) n⁻¹).mp (N.inv_mem hn)
  have hpow : ∀ (n t : G), n ∈ N → t ∈ T → ∀ j : ℕ, ∃ n' ∈ N, (n * t) ^ j = n' * t ^ j := by
    intro n t hn ht j
    induction j with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨n', hn', hj⟩ := ih
      refine ⟨n' * (t ^ j * n * (t ^ j)⁻¹), N.mul_mem hn' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hTN (T.pow_mem ht j)) n).mp hn
      · rw [pow_succ (n * t) j, hj]
        group
  unfold oTwoRes
  refine (Subgroup.closure_le N).mpr fun x hx => ?_
  obtain ⟨hxX, m, hm, hxm⟩ := hx
  obtain ⟨n, hn, t, ht, rfl⟩ := hdec x hxX
  obtain ⟨n', hn', hpowm⟩ := hpow n t hn ht m
  have htm : t ^ m ∈ N := by
    have h1 : n' * t ^ m = 1 := by rw [← hpowm]; exact hxm
    rw [eq_inv_of_mul_eq_one_right h1]
    exact N.inv_mem hn'
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem hT ht
  have hcop : Nat.Coprime m (orderOf t) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk)
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm))
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  have htN : t ∈ N := by
    have := N.pow_mem htm j
    rwa [hj] at this
  exact N.mul_mem hn htN

private theorem f86_le_normalizer_L₁Of {G : Type} [Group G] {L V₁ T : Subgroup G}
    (hL : T ≤ Subgroup.normalizer (L : Set G)) (hV₁ : T ≤ Subgroup.normalizer (V₁ : Set G)) :
    T ≤ Subgroup.normalizer (L₁Of L V₁ : Set G) := by
  intro t ht
  apply mem_normalizer_of_conjSub_eq
  unfold L₁Of
  rw [conjSub_oTwoRes]
  congr 1
  rw [conjSub_inf, conjSub_eq_of_mem_normalizer (hL ht), ← conjSub_normalizer,
    conjSub_eq_of_mem_normalizer (hV₁ ht)]

private theorem f86_oTwoRes_sup_L₁Of {G : Type} [Group G] [Finite G] {L V₁ T : Subgroup G}
    (hT : IsPGroup 2 T) (hL : T ≤ Subgroup.normalizer (L : Set G))
    (hV₁ : T ≤ Subgroup.normalizer (V₁ : Set G)) :
    oTwoRes (L₁Of L V₁ ⊔ T) = L₁Of L V₁ := by
  have hsub : L₁Of L V₁ ≤ oTwoRes (L₁Of L V₁) :=
    le_of_eq (f86_oTwoRes_oTwoRes (L ⊓ Subgroup.normalizer (V₁ : Set G))).symm
  exact le_antisymm (f86_oTwoRes_sup_le hT (f86_le_normalizer_L₁Of hL hV₁))
    (hsub.trans (f86_oTwoRes_mono le_sup_left))

theorem as_F_8_6 : F_8_6 := by
  intro G _ _ T V L V₁ H γ γ' g h s
  have h' : HypF81 T V L V₁ H := h
  have hyp := h'.amalgamHypV
  have hstab : stab γ' ⊓ stab γ = conjSub (g : G) (L₁Of L V₁ ⊔ T) := by
    rw [← s.edge₀, ← s.edge₁, stab_smul, stab_smul, stab_γ₀ hyp.le₁, stab_γ₁ hyp.le₂,
      ← conjSub_inf, h'.LT_inf_H]
  have hkey : oTwoRes (L₁Of L V₁ ⊔ T) = L₁Of L V₁ :=
    f86_oTwoRes_sup_L₁Of h'.sylow.2.1 h'.normalizes_L h'.T_normalizes_V₁
  rw [hstab, ← conjSub_oTwoRes, hkey]

@[expose] def F_8_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ H : Subgroup G) (γ γ' : F8.Geom T L H)
    (g : ↥((L ⊔ T) ⊔ H)), HypF_8_1 T V L V₁ H → F8Setup T V L H γ γ' g →
      stab (F8.γ₀ T L H) ⊓ stab (F8.γ₁ T L H) = L₁Of L V₁ ⊔ T ∧
      (conjClosure V H ≤ pCoreOf 2 (stab γ' ⊓ stab γ) ∧
        ∀ γ₂ ∈ nbrs (F8.γ₁ T L H), CosetGeom.dist γ γ₂ + 2 = F8.b T V L H →
          F8.Uγ V H (g : G) ≤ pCoreOf 2 (stab (F8.γ₁ T L H) ⊓ stab γ₂)) ∧
      ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ ≤ conjClosure V H ⊓ F8.Uγ V H (g : G) ∧
      F8.Uγ V H (g : G) ≤ Subgroup.normalizer (Vv V (F8.γ₁ T L H) : Set G) ∧
      (¬ ⁅F8.Uγ V H (g : G), V⁆ ≤ F8.A₁ V₁ (g : G) ∧ V₁ ⊓ F8.A₁ V₁ (g : G) = ⊥) ∧
      (⁅F8.Uγ V H (g : G), F8.DH V V₁ H (g : G)⁆ ≤ F8.A₁ V₁ (g : G) ∧
        ⁅conjClosure V H, F8.Dγ V V₁ H (g : G)⁆ ≤ V₁) ∧
      ⁅F8.DH V V₁ H (g : G), F8.Dγ V V₁ H (g : G)⁆ = ⊥

theorem as_F_8_7 : F_8_7 := by
  intro G _ _ T V L V₁ H γ γ' g h s
  have h' : HypF81 T V L V₁ H := h
  refine ⟨F8.F87_1 h', F8.F87_2 h' s, F8.F87_3 h' s, ?_, ⟨F8.F87_5a h' s, F8.F87_5b h' s⟩,
    F8.F87_6 V V₁ H (g : G), F8.F87_7 h' s⟩
  have h4 := F8.F87_4 h' s
  rwa [F8.conjClosure_eq_Vv_γ₁ h'] at h4

end CFSG.ASVolI
