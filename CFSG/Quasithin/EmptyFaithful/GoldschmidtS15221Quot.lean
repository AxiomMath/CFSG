module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221S4
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.Quasithin.S15221

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type*} [Group G] [Finite G] {Γ : Type*} [Group Γ]

abbrev imgOf {C : Subgroup G} (σ : ↥C →* Γ) (X : Subgroup G) : Subgroup Γ :=
  (X.subgroupOf C).map σ

theorem imgOf_oTwoUpper {C : Subgroup G} {σ : ↥C →* Γ} (hσ : Function.Surjective σ) :
    imgOf σ (oTwoUpper C) = oTwoUpper (⊤ : Subgroup Γ) := by
  have h1 : (oTwoUpper C).subgroupOf C = oTwoUpper (⊤ : Subgroup ↥C) := by
    rw [← Subgroup.subgroupOf_self C, ← A4.oTwoUpper_subgroupOf (le_refl C)]
  show ((oTwoUpper C).subgroupOf C).map σ = _
  rw [h1, ← oTwoUpper_map, Subgroup.map_top_of_surjective σ hσ]

section Aux

variable {C : Subgroup G} {σ : ↥C →* Γ} {V : Subgroup Γ}

abbrev wOf (σ : ↥C →* Γ) (V : Subgroup Γ) : Subgroup G := (V.comap σ).map C.subtype

omit [Finite G] in
theorem mem_wOf {x : G} : x ∈ wOf σ V ↔ ∃ h : x ∈ C, σ ⟨x, h⟩ ∈ V := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, hc⟩
  · rintro ⟨h, hv⟩
    exact ⟨⟨x, h⟩, hv, rfl⟩

omit [Finite G] in
theorem isPGroup_wOf (hker : IsPGroup 2 σ.ker) (hV2 : IsPGroup 2 V) : IsPGroup 2 (wOf σ V) :=
  (hV2.comap_of_ker_isPGroup σ hker).map _

theorem pCoreOf_oTwoUpper_eq (hσ : Function.Surjective σ) (hker : IsPGroup 2 σ.ker)
    (hVn : V.Normal) (hV2 : IsPGroup 2 V)
    (hA : ∀ N : Subgroup Γ, N ≤ oTwoUpper (⊤ : Subgroup Γ) → IsPGroup 2 N → N ≤ V) :
    pCoreOf 2 (oTwoUpper C) = oTwoUpper C ⊓ wOf σ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYC : oTwoUpper C ≤ C := oTwoUpper_le C
  have hW2 := isPGroup_wOf hker hV2
  apply le_antisymm
  · intro n hn
    have hnY : n ∈ oTwoUpper C := pCoreOf_le 2 _ hn
    have hnC : n ∈ C := hYC hnY
    refine ⟨hnY, mem_wOf.mpr ⟨hnC, ?_⟩⟩
    have hsub : imgOf σ (pCoreOf 2 (oTwoUpper C)) ≤ oTwoUpper (⊤ : Subgroup Γ) := by
      rw [← imgOf_oTwoUpper hσ]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono C (pCoreOf_le 2 _))
    have hp2 : IsPGroup 2 (imgOf σ (pCoreOf 2 (oTwoUpper C))) := by
      intro g
      obtain ⟨c, hc, hcg⟩ := g.2
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (oTwoUpper C) ⟨c.1, hc⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : c ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      show (g : Γ) ^ 2 ^ k = 1
      rw [← hcg, ← map_pow, h1, map_one]
    exact hA _ hsub hp2 ⟨⟨n, hnC⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
  · refine le_pCoreOf 2 inf_le_left ?_ (hW2.to_le inf_le_right)
    refine ⟨fun x hx h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxC, hxv⟩ := mem_wOf.mp hx.2
    have hhC : (h : G) ∈ C := hYC h.2
    refine ⟨(oTwoUpper C).mul_mem ((oTwoUpper C).mul_mem h.2 hx.1) ((oTwoUpper C).inv_mem h.2),
      mem_wOf.mpr ⟨C.mul_mem (C.mul_mem hhC hxC) (C.inv_mem hhC), ?_⟩⟩
    have hconj : σ ⟨((h * x * h⁻¹ : ↥(oTwoUpper C)) : G),
        C.mul_mem (C.mul_mem hhC hxC) (C.inv_mem hhC)⟩ =
        σ ⟨h, hhC⟩ * σ ⟨x, hxC⟩ * (σ ⟨h, hhC⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hconj]
    exact hVn.conj_mem _ hxv _

theorem relIndex_pCoreOf_oTwoUpper (hσ : Function.Surjective σ) (hker : IsPGroup 2 σ.ker)
    (hVn : V.Normal) (hV2 : IsPGroup 2 V)
    (hA : ∀ N : Subgroup Γ, N ≤ oTwoUpper (⊤ : Subgroup Γ) → IsPGroup 2 N → N ≤ V)
    (hidx : V.relIndex (oTwoUpper (⊤ : Subgroup Γ)) = 3) :
    (pCoreOf 2 (oTwoUpper C)).relIndex (oTwoUpper C) = 3 := by
  have hYC : oTwoUpper C ≤ C := oTwoUpper_le C
  rw [pCoreOf_oTwoUpper_eq hσ hker hVn hV2 hA, inf_comm, Subgroup.inf_relIndex_right]
  calc (wOf σ V).relIndex (oTwoUpper C)
      = (wOf σ V).relIndex (((oTwoUpper C).subgroupOf C).map C.subtype) := by
        rw [Subgroup.map_subgroupOf_eq_of_le hYC]
    _ = (V.comap σ).relIndex ((oTwoUpper C).subgroupOf C) :=
        Subgroup.relIndex_map_map_of_injective _ _ C.subtype_injective
    _ = V.relIndex (((oTwoUpper C).subgroupOf C).map σ) := Subgroup.relIndex_comap V σ _
    _ = 3 := by
        rw [show ((oTwoUpper C).subgroupOf C).map σ = oTwoUpper (⊤ : Subgroup Γ) from
          imgOf_oTwoUpper hσ]
        exact hidx

theorem pCoreOf_oTwoUpper_ne_bot (hσ : Function.Surjective σ) (hker : IsPGroup 2 σ.ker)
    (hVn : V.Normal) (hV2 : IsPGroup 2 V)
    (hA : ∀ N : Subgroup Γ, N ≤ oTwoUpper (⊤ : Subgroup Γ) → IsPGroup 2 N → N ≤ V)
    (hVA : V ≤ oTwoUpper (⊤ : Subgroup Γ)) (hcard : Nat.card V = 4) :
    pCoreOf 2 (oTwoUpper C) ≠ ⊥ := by
  rw [pCoreOf_oTwoUpper_eq hσ hker hVn hV2 hA]
  intro hbot
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra h
    push Not at h
    have hVbot : V = ⊥ := by
      rw [eq_bot_iff]
      exact fun v hv => Subgroup.mem_bot.mpr (h v hv)
    rw [hVbot, Subgroup.card_bot] at hcard
    omega
  have hvA : v ∈ imgOf σ (oTwoUpper C) := by
    rw [imgOf_oTwoUpper hσ]
    exact hVA hv
  obtain ⟨y, hy, hyv⟩ := hvA
  have hyW : (y : G) ∈ wOf σ V := mem_wOf.mpr ⟨y.2, by simpa [hyv] using hv⟩
  have hyY : (y : G) ∈ oTwoUpper C := Subgroup.mem_subgroupOf.mp hy
  have hy1 : (y : G) = 1 := by
    have : (y : G) ∈ oTwoUpper C ⊓ wOf σ V := ⟨hyY, hyW⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  have : y = 1 := Subtype.ext hy1
  rw [this, map_one] at hyv
  exact hv1 hyv.symm

theorem exists_commutator_not_mem (hσ : Function.Surjective σ) (hker : IsPGroup 2 σ.ker)
    (hVn : V.Normal) (hV2 : IsPGroup 2 V)
    (hA : ∀ N : Subgroup Γ, N ≤ oTwoUpper (⊤ : Subgroup Γ) → IsPGroup 2 N → N ≤ V)
    (hcard : Nat.card V = 4)
    (hc : ∀ a b : Γ, a ∉ V → (∃ k : ℕ, a ^ 2 ^ k = 1) → b ∈ oTwoUpper (⊤ : Subgroup Γ) →
      b ∉ V → a * b * a⁻¹ * b⁻¹ ∉ V)
    (hsyl : ∀ P : Subgroup Γ, IsPGroup 2 P → ¬ 2 ∣ P.index → 8 ≤ Nat.card P)
    {D : Subgroup G} (hDC : D ≤ C) (hD2 : IsPGroup 2 D) (hDi : ¬ 2 ∣ (D.subgroupOf C).index) :
    ∃ d ∈ D, ∀ y ∈ oTwoUpper C, y ∉ pCoreOf 2 (oTwoUpper C) →
      d * y * d⁻¹ * y⁻¹ ∉ pCoreOf 2 (oTwoUpper C) := by
  have hYC : oTwoUpper C ≤ C := oTwoUpper_le C
  have hDg2 : IsPGroup 2 (D.subgroupOf C) := hD2.of_equiv (Subgroup.subgroupOfEquivOfLe hDC).symm
  have h8 : 8 ≤ Nat.card (imgOf σ D) :=
    hsyl _ (hDg2.map σ) fun h => hDi (h.trans (Subgroup.index_map_dvd (D.subgroupOf C) hσ))
  have hVfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have hnot : ¬ imgOf σ D ≤ V := fun hle => by
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨p, hp, hpV⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨dc, hdc, hdp⟩ := hp
  have hdD : (dc : G) ∈ D := Subgroup.mem_subgroupOf.mp hdc
  refine ⟨dc, hdD, fun y hy hyN hcomm => ?_⟩
  have hNeq := pCoreOf_oTwoUpper_eq hσ hker hVn hV2 hA (C := C)
  rw [hNeq] at hyN hcomm
  have hyC : y ∈ C := hYC hy
  have hyV : σ ⟨y, hyC⟩ ∉ V := fun h => hyN ⟨hy, mem_wOf.mpr ⟨hyC, h⟩⟩
  have hyA : σ ⟨y, hyC⟩ ∈ oTwoUpper (⊤ : Subgroup Γ) := by
    rw [← imgOf_oTwoUpper hσ]
    exact ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  obtain ⟨k, hk⟩ := hD2 ⟨dc, hdD⟩
  have hk' : p ^ 2 ^ k = 1 := by
    rw [← hdp, ← map_pow]
    have : dc ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have h1 := hc p (σ ⟨y, hyC⟩) hpV ⟨k, hk'⟩ hyA hyV
  apply h1
  obtain ⟨hcommC, hcommV⟩ := mem_wOf.mp hcomm.2
  have hcalc : σ ⟨dc * y * dc⁻¹ * y⁻¹, hcommC⟩ = p * σ ⟨y, hyC⟩ * p⁻¹ * (σ ⟨y, hyC⟩)⁻¹ := by
    rw [← hdp, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [← hcalc]
  exact hcommV

end Aux

theorem s4Quot_oTwoUpper (hΓ : S4Like Γ) {C : Subgroup G} (σ : ↥C →* Γ)
    (hσ : Function.Surjective σ) (hker : IsPGroup 2 σ.ker) :
    (pCoreOf 2 (oTwoUpper C)).relIndex (oTwoUpper C) = 3 ∧ pCoreOf 2 (oTwoUpper C) ≠ ⊥ ∧
      ∀ D : Subgroup G, D ≤ C → IsPGroup 2 D → ¬ 2 ∣ (D.subgroupOf C).index →
        ∃ d ∈ D, ∀ y ∈ oTwoUpper C, y ∉ pCoreOf 2 (oTwoUpper C) →
          d * y * d⁻¹ * y⁻¹ ∉ pCoreOf 2 (oTwoUpper C) := by
  obtain ⟨V, hVn, hV2, hVA, hidx, -, hA, hc, -, hcard, hsyl⟩ := hΓ.exists_V
  exact ⟨relIndex_pCoreOf_oTwoUpper hσ hker hVn hV2 hA hidx,
    pCoreOf_oTwoUpper_ne_bot hσ hker hVn hV2 hA hVA hcard,
    fun _ hDC hD2 hDi => exists_commutator_not_mem hσ hker hVn hV2 hA hcard hc hsyl hDC hD2 hDi⟩

end CFSG.Quasithin.S15221
