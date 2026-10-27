module

public import CFSG.Milestones.ASVolI.A1
public import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.ASVolI

open CFSG.Open
open CFSG.ASVolI.ChA

namespace ChA

section A5Vocabulary

variable {G : Type} [Group G]

@[expose] def InHT (T H : Subgroup G) : Prop :=
  T ≤ H ∧ pCoreOf 2 H ≠ ⊥

@[expose] def InMT (T M : Subgroup G) : Prop :=
  IsMaxTwoLocalSubgroup M ∧ T ≤ M

@[expose] def VZ (T H : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ h ∈ H, ∃ z ∈ omegaOne 2 (centerOf T), x = h * z * h⁻¹}

@[expose] def OrdLE (T H₁ H₂ : Subgroup G) : Prop :=
  H₁ = (H₁ ⊓ H₂) ⊔ (H₁ ⊓ centralizerOf (VZ T H₁))

@[expose] def InHvT (T H : Subgroup G) : Prop :=
  InHT T H ∧ H = ChA.normalizerOf (VZ T H)

@[expose] def IsUniqueMaxTwoLocalOver (X M : Subgroup G) : Prop :=
  IsMaxTwoLocalSubgroup M ∧ X ≤ M ∧ ∀ M' : Subgroup G, IsMaxTwoLocalSubgroup M' → X ≤ M' → M' = M

end A5Vocabulary

end ChA

@[expose] def A_5_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → ∀ H : Subgroup G, InHT T H → IsTwoReduced H (VZ T H)

section Bridge

variable {G : Type} [Group G]

private theorem a5_closure_conj_eq (Z H : Subgroup G) :
    Subgroup.closure {x | ∃ h ∈ H, ∃ z ∈ Z, x = h * z * h⁻¹} =
      CFSG.Quasithin.conjClosure Z H := by
  unfold CFSG.Quasithin.conjClosure
  congr 1
  ext x
  constructor <;> rintro ⟨h, hh, z, hz, rfl⟩ <;> exact ⟨h, hh, z, hz, rfl⟩

private theorem a5_vz_eq (T H : Subgroup G) : VZ T H = CFSG.Quasithin.VZ T H :=
  a5_closure_conj_eq (omegaOne 2 (centerOf T)) H

private theorem a5_le_normalizer_inf {S A B : Subgroup G} (hA : S ≤ Subgroup.normalizer (A : Set G))
    (hB : S ≤ Subgroup.normalizer (B : Set G)) :
    S ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hA hg) x,
    Subgroup.mem_normalizer_iff.mp (hB hg) x]

private theorem a5_le_normalizer_centralizer {S V : Subgroup G}
    (h : S ≤ Subgroup.normalizer (V : Set G)) :
    S ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  intro g hg
  have key : ∀ g ∈ S, ∀ c ∈ Subgroup.centralizer (V : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ V := (Subgroup.mem_normalizer_iff''.mp (h hg) s).mp hs
    have h2 := hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h2]
      _ = g * c * g⁻¹ * s := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨fun hc => key g hg c hc, fun hc => by simpa [mul_assoc] using key g⁻¹ (S.inv_mem hg) _ hc⟩

open scoped Pointwise in
private theorem a5_exists_mul_of_eq_sup {X B M : Subgroup G} (hXM : X ≤ M)
    (hBN : M ≤ Subgroup.normalizer (B : Set G)) (h : M = X ⊔ B) :
    ∀ m ∈ M, ∃ x ∈ X, ∃ c ∈ B, m = x * c := by
  intro m hm
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right X B (hXM.trans hBN)
  have hm' : m ∈ (X : Set G) * (B : Set G) := by
    rw [← hmul]
    exact h.le hm
  obtain ⟨x, hx, c, hc, rfl⟩ := hm'
  exact ⟨x, hx, c, hc, rfl⟩

private theorem a5_ordLE_iff (T H₁ H₂ : Subgroup G) :
    OrdLE T H₁ H₂ ↔ CFSG.Quasithin.OrdLE T H₁ H₂ := by
  unfold OrdLE CFSG.Quasithin.OrdLE
  rw [a5_vz_eq]
  have hN : H₁ ≤ Subgroup.normalizer
      ((H₁ ⊓ centralizerOf (CFSG.Quasithin.VZ T H₁) : Subgroup G) : Set G) :=
    a5_le_normalizer_inf Subgroup.le_normalizer
      (a5_le_normalizer_centralizer (CFSG.Quasithin.le_normalizer_conjClosure _ _))
  constructor
  · intro h x hx
    obtain ⟨a, ha, c, hc, rfl⟩ := a5_exists_mul_of_eq_sup inf_le_left hN h x hx
    exact ⟨a, ha, c, hc, rfl⟩
  · intro h
    refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left inf_le_left)
    obtain ⟨a, ha, c, hc, rfl⟩ := h x hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hc)

private theorem a5_inHvT_iff (T H : Subgroup G) : InHvT T H ↔ CFSG.Quasithin.InHv T H := by
  unfold InHvT CFSG.Quasithin.InHv CFSG.Quasithin.IsHv
  rw [a5_vz_eq]
  exact Iff.rfl

private theorem a5_isUniqueMaxTwoLocalOver_iff (X M : Subgroup G) :
    IsUniqueMaxTwoLocalOver X M ↔ CFSG.Quasithin.IsUniqueM X M :=
  ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, fun M' hM' => h3 M' hM'.1 hM'.2⟩,
    fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, fun M' h4 h5 => h3 M' ⟨h4, h5⟩⟩⟩

private theorem a5_exists_sylow {T : Subgroup G} (hT : IsSylowIn 2 T ⊤) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  have hidx : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
  exact ⟨hT.2.1.toSylow hidx, IsPGroup.toSylow_coe _ _⟩

private theorem a5_even [Finite G] (hEC : CFSG.IsEvenCharacteristic G) :
    quasithinEvenCharacteristic G :=
  fun H hH hS => CFSG.Quasithin.CT.charTwo_iff_internal.mpr (hEC H hH hS)

private theorem a5_isTwoReduced {H V : Subgroup G} (h : CFSG.Quasithin.IsTwoReducedIn H V) :
    IsTwoReduced H V := by
  obtain ⟨hVH, hHN, hel, hD⟩ := h
  refine ⟨hVH, (Subgroup.normal_subgroupOf_iff_le_normalizer hVH).mpr hHN, hel, ?_⟩
  intro N _ hNH hNn hN
  have hHNN : H ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hNn
  exact le_inf hNH (hD N hNH hHNN fun d hd => (hN d hd).imp fun k hk => hk.2)

private theorem a5_conjAct_apply_coe (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (v
    : V) :
    ((CFSG.Quasithin.conjAct V g v : V) : G) = g * v * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v

private theorem a5_exists_of_autOn_eq {M N V : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V :
    Set G))
    (h : CFSG.Quasithin.autOn M V = CFSG.Quasithin.autOn N V) :
    ∀ m ∈ M, ∃ n ∈ N, ∀ v ∈ V, m * v * m⁻¹ = n * v * n⁻¹ := by
  intro m hm
  have hmem : CFSG.Quasithin.conjAct V ⟨m, hMV hm⟩ ∈ CFSG.Quasithin.autOn M V :=
    Subgroup.mem_map.mpr ⟨⟨m, hMV hm⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
  rw [h] at hmem
  obtain ⟨g, hg, hgeq⟩ := Subgroup.mem_map.mp hmem
  refine ⟨(g : G), Subgroup.mem_subgroupOf.mp hg, fun v hv => ?_⟩
  have h1 := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) hgeq
  simp only [a5_conjAct_apply_coe] at h1
  exact h1.symm

end Bridge

theorem as_A_5_1 : A_5_1 := by
  intro G _ _ _ hEC T hT H hH
  obtain ⟨S, rfl⟩ := a5_exists_sylow hT
  have hEven : quasithinEvenCharacteristic G := by
    first | exact a5_even hEC | exact a5_even_cha hEC
  rw [a5_vz_eq]
  exact a5_isTwoReduced (CFSG.Quasithin.isTwoReducedIn_conjClosure H S hH.1
    (CFSG.Quasithin.charTwo_of_inH hEven S hH) le_rfl)

@[expose] def A_5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ →
      (∀ H : Subgroup G, InHT T H → OrdLE T H H) ∧
      (∀ H₁ H₂ : Subgroup G, InHT T H₁ → InHT T H₂ → H₁ ≤ H₂ → OrdLE T H₁ H₂) ∧
      (∀ M : Subgroup G, InMT T M → InHvT T M)

theorem as_A_5_2 : A_5_2 := by
  intro G _ _ _ hEC T hT
  obtain ⟨S, rfl⟩ := a5_exists_sylow hT
  have hEven : quasithinEvenCharacteristic G := by
    first | exact a5_even hEC | exact a5_even_cha hEC
  refine ⟨fun H _ => (a5_ordLE_iff _ _ _).mpr (CFSG.Quasithin.ordLE_refl _ _),
    fun H₁ H₂ _ _ h => (a5_ordLE_iff _ _ _).mpr (CFSG.Quasithin.ordLE_of_le h), fun M hM => ?_⟩
  exact (a5_inHvT_iff _ _).mpr ⟨CFSG.Quasithin.inH_of_inM hM, CFSG.Quasithin.isHv_of_inM hEven S hM⟩

@[expose] def A_5_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → ∀ H₁ H₂ : Subgroup G, InHT T H₁ → InHT T H₂ →
      OrdLE T H₁ H₂ →
      VZ T H₁ ≤ VZ T H₂ ∧
      H₂ ⊓ centralizerOf (VZ T H₂) ≤ H₂ ⊓ centralizerOf (VZ T H₁) ∧
      (InHvT T H₁ → H₂ ⊓ centralizerOf (VZ T H₂) ≤ H₁ ⊓ centralizerOf (VZ T H₁))

theorem as_A_5_3 : A_5_3 := by
  intro G _ _ _ _ T _ H₁ H₂ _ _ hle
  have hle' := (a5_ordLE_iff T H₁ H₂).mp hle
  refine ⟨?_, ?_, fun hv => ?_⟩
  · rw [a5_vz_eq, a5_vz_eq]
    exact CFSG.Quasithin.VZ_le_of_ordLE hle'
  · rw [a5_vz_eq, a5_vz_eq]
    exact CFSG.Quasithin.centralizer_VZ_le_of_ordLE hle'
  · rw [a5_vz_eq, a5_vz_eq]
    exact CFSG.Quasithin.centralizer_VZ_le_of_ordLE_of_isHv hle' ((a5_inHvT_iff T H₁).mp hv).2

@[expose] def A_5_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → ∀ H₁ H₂ : Subgroup G, InHvT T H₁ → InHvT T H₂ →
      (H₁ = H₂ ↔ VZ T H₁ = VZ T H₂) ∧ (VZ T H₁ = VZ T H₂ ↔ (OrdLE T H₁ H₂ ∧ OrdLE T H₂ H₁))

theorem as_A_5_4 : A_5_4 := by
  intro G _ _ _ _ T _ H₁ H₂ h₁ h₂
  have h₁' := ((a5_inHvT_iff T H₁).mp h₁).2
  have h₂' := ((a5_inHvT_iff T H₂).mp h₂).2
  refine ⟨?_, ?_⟩
  · rw [a5_vz_eq, a5_vz_eq]
    exact ⟨fun h => by rw [h], CFSG.Quasithin.eq_of_VZ_eq h₁' h₂'⟩
  · rw [a5_vz_eq, a5_vz_eq, a5_ordLE_iff, a5_ordLE_iff]
    refine ⟨fun h => ?_, fun h => le_antisymm (CFSG.Quasithin.VZ_le_of_ordLE h.1)
      (CFSG.Quasithin.VZ_le_of_ordLE h.2)⟩
    obtain rfl := CFSG.Quasithin.eq_of_VZ_eq h₁' h₂' h
    exact ⟨CFSG.Quasithin.ordLE_refl _ _, CFSG.Quasithin.ordLE_refl _ _⟩

@[expose] def A_5_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ →
      (∀ H : Subgroup G, InHvT T H → OrdLE T H H) ∧
      (∀ H₁ H₂ : Subgroup G, InHvT T H₁ → InHvT T H₂ → OrdLE T H₁ H₂ → OrdLE T H₂ H₁ → H₁ = H₂) ∧
      (∀ H₁ H₂ H₃ : Subgroup G, InHvT T H₁ → InHvT T H₂ → InHvT T H₃ →
        OrdLE T H₁ H₂ → OrdLE T H₂ H₃ → OrdLE T H₁ H₃) ∧
      (∀ M : Subgroup G, InMT T M → InHvT T M)

theorem as_A_5_5 : A_5_5 := by
  intro G _ _ _ hEC T hT
  obtain ⟨S, rfl⟩ := a5_exists_sylow hT
  have hEven : quasithinEvenCharacteristic G := by
    first | exact a5_even hEC | exact a5_even_cha hEC
  refine ⟨fun H _ => (a5_ordLE_iff _ _ _).mpr (CFSG.Quasithin.ordLE_refl _ _),
    fun H₁ H₂ h₁ h₂ h₁₂ h₂₁ => CFSG.Quasithin.eq_of_ordLE_antisymm ((a5_inHvT_iff _ _).mp h₁).2
      ((a5_inHvT_iff _ _).mp h₂).2 ((a5_ordLE_iff _ _ _).mp h₁₂) ((a5_ordLE_iff _ _ _).mp h₂₁),
    fun H₁ H₂ H₃ h₁ _ _ h₁₂ h₂₃ => (a5_ordLE_iff _ _ _).mpr
      (CFSG.Quasithin.ordLE_trans ((a5_inHvT_iff _ _).mp h₁).2 ((a5_ordLE_iff _ _ _).mp h₁₂)
        ((a5_ordLE_iff _ _ _).mp h₂₃)),
    fun M hM => ?_⟩
  exact (a5_inHvT_iff _ _).mpr ⟨CFSG.Quasithin.inH_of_inM hM, CFSG.Quasithin.isHv_of_inM hEven S hM⟩

@[expose] def A_5_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → ∀ H M : Subgroup G, InHT T H → InMT T M →
      OrdLE T H M →
      ∀ V : Subgroup G, V ≠ ⊥ →
        V = Subgroup.closure {x | ∃ h ∈ H ⊓ M, ∃ z ∈ V ⊓ omegaOne 2 (centerOf T), x = h * z * h⁻¹} →
        (V.subgroupOf M).Normal → V ≤ M → H ≤ M

theorem as_A_5_6 : A_5_6 := by
  intro G _ _ _ hEC T hT H M _ hM hle V hV hgen hVn hVM
  obtain ⟨S, rfl⟩ := a5_exists_sylow hT
  have hEven : quasithinEvenCharacteristic G := by
    first | exact a5_even hEC | exact a5_even_cha hEC
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    CFSG.Quasithin.charTwo_of_inH hEven S ⟨hM.2, CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal hM.1.1⟩
  have hgen' : V = CFSG.Quasithin.conjClosure (V ⊓ quasithinOmegaOneCenter (S : Subgroup G))
      (H ⊓ M) := hgen.trans (a5_closure_conj_eq _ _)
  obtain ⟨-, hel⟩ := CFSG.Quasithin.conjClosure_le_centerOf_pCoreOf M S hM.2 hF
    (Z := V ⊓ quasithinOmegaOneCenter (S : Subgroup G)) inf_le_right
  have hVle : V ≤ CFSG.Quasithin.conjClosure (V ⊓ quasithinOmegaOneCenter (S : Subgroup G)) M :=
    hgen'.le.trans (CFSG.Quasithin.conjClosure_mono le_rfl inf_le_right)
  have hV2 : IsPGroup 2 V := fun g => ⟨1, Subtype.ext (by simpa using hel.2 (g : G) (hVle g.2))⟩
  exact CFSG.Quasithin.le_of_ordLE_of_normal hM.1 ((a5_ordLE_iff _ _ _).mp hle) hV hV2
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mp hVn) hgen'

@[expose] def A_5_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ →
      (∀ M : Subgroup G, InMT T M → (∀ M' : Subgroup G, InMT T M' → OrdLE T M M' → M' = M) →
        (∀ X : Subgroup G, InHT T X → X ≤ M → M = X ⊔ (M ⊓ centralizerOf (VZ T M)) →
          IsUniqueMaxTwoLocalOver X M) ∧
        (∀ V : Subgroup G,
          (V = VZ T M ∨
            (V = Subgroup.closure {x | ∃ m ∈ M, ∃ z ∈ V ⊓ omegaOne 2 (centerOf T), x = m * z * m⁻¹} ∧
              (∀ M' : Subgroup G, InMT T M' →
                (∀ M'' : Subgroup G, InMT T M'' → OrdLE T M' M'' → M'' = M') → M' = M))) →
          quasithinGenFitting (M ⊓ ChA.normalizerOf (T ⊓ centralizerOf V)) = T ⊓ centralizerOf V ∧
            IsTwoReduced (M ⊓ ChA.normalizerOf (T ⊓ centralizerOf V)) V ∧
            (∀ m ∈ M, ∃ n ∈ M ⊓ ChA.normalizerOf (T ⊓ centralizerOf V), ∀ v ∈ V, m * v * m⁻¹ = n * v * n⁻¹) ∧
            (V ≠ ⊥ → IsUniqueMaxTwoLocalOver (M ⊓ ChA.normalizerOf (T ⊓ centralizerOf V)) M))) ∧
      (∀ H : Subgroup G, InHT T H →
        ((InHvT T H ∧ ∀ H' : Subgroup G, InHvT T H' → OrdLE T H H' → H' = H) ↔
          (InMT T H ∧ ∀ M' : Subgroup G, InMT T M' → OrdLE T H M' → M' = H)))

theorem as_A_5_7 : A_5_7 := by
  intro G _ _ _ hEC T hT
  obtain ⟨S, rfl⟩ := a5_exists_sylow hT
  have hEven : quasithinEvenCharacteristic G := by
    first | exact a5_even hEC | exact a5_even_cha hEC
  refine ⟨fun M hM hmax => ?_, fun H hH => ?_⟩
  · have hmax' : CFSG.Quasithin.IsOrdMaximalIn (S : Subgroup G) (CFSG.Quasithin.InM S) M :=
      ⟨hM, fun M' hM' hle => hmax M' hM' ((a5_ordLE_iff _ _ _).mpr hle)⟩
    refine ⟨fun X hX hXM hcov => ?_, fun V hV => ?_⟩
    ·
      rw [a5_vz_eq] at hcov
      exact (a5_isUniqueMaxTwoLocalOver_iff _ _).mpr
        (CFSG.Quasithin.isUniqueM_of_isOrdMaximalIn hmax' hX hXM
          (a5_exists_mul_of_eq_sup hXM
            (a5_le_normalizer_inf Subgroup.le_normalizer
              (a5_le_normalizer_centralizer (CFSG.Quasithin.le_normalizer_conjClosure _ _))) hcov))
    ·
      have hV' : CFSG.Quasithin.A57.CaseA (S : Subgroup G) M V ∨
          CFSG.Quasithin.A57.CaseB (S : Subgroup G) M V := by
        rcases hV with h | ⟨h1, h2⟩
        · exact Or.inl (h.trans (a5_vz_eq _ _))
        · refine Or.inr ⟨?_, fun M' hM' => h2 M' hM'.1 fun M'' hM'' hle =>
            hM'.2 M'' hM'' ((a5_ordLE_iff _ _ _).mp hle)⟩
          rw [inf_comm]
          exact h1.trans (a5_closure_conj_eq _ _)
      have hVn : M ≤ Subgroup.normalizer (V : Set G) := by
        rcases hV' with h | h
        · rw [h]
          exact CFSG.Quasithin.le_normalizer_conjClosure _ _
        · have := CFSG.Quasithin.le_normalizer_conjClosure
            (quasithinOmegaOneCenter (S : Subgroup G) ⊓ V) M
          rwa [← h.1] at this
      obtain ⟨hpc, hct⟩ := CFSG.Quasithin.A57.eq_pCoreOf_and_charTwo hEven S hM hV'
      refine ⟨?_, a5_isTwoReduced (CFSG.Quasithin.A57.isTwoReducedIn_normalizer hEven S hM hV'),
        a5_exists_of_autOn_eq hVn (CFSG.Quasithin.A57.autOn_eq hEven S hM hV'), fun hVne => ?_⟩
      · exact ((CFSG.Quasithin.quasithinGenFitting_eq_pCoreOf_iff _ 2).mpr hct).trans hpc
      · exact (a5_isUniqueMaxTwoLocalOver_iff _ _).mpr
          (CFSG.Quasithin.A57.isUniqueM hEven S hmax' (hV'.imp_right fun h => ⟨hVne, h⟩))
  ·
    have key := CFSG.Quasithin.isOrdMaximalIn_inHv_iff hEven S (H := H)
    constructor
    · rintro ⟨hHv, hmax⟩
      have h := key.mp ⟨(a5_inHvT_iff _ _).mp hHv, fun H' hH' hle =>
        hmax H' ((a5_inHvT_iff _ _).mpr hH') ((a5_ordLE_iff _ _ _).mpr hle)⟩
      exact ⟨h.1, fun M' hM' hle => h.2 M' hM' ((a5_ordLE_iff _ _ _).mp hle)⟩
    · rintro ⟨hM, hmax⟩
      have h := key.mpr ⟨hM, fun M' hM' hle => hmax M' hM' ((a5_ordLE_iff _ _ _).mpr hle)⟩
      exact ⟨(a5_inHvT_iff _ _).mpr h.1, fun H' hH' hle =>
        h.2 H' ((a5_inHvT_iff _ _).mp hH') ((a5_ordLE_iff _ _ _).mp hle)⟩

@[expose] def A_5_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → ∀ H K : Subgroup G, InHT T H → InHT T K →
      (H ≤ K → OrdLE T H K) ∧ (OrdLE T H K → OrdLE T K H → VZ T H = VZ T K)

theorem as_A_5_9 : A_5_9 := by
  intro G _ _ _ _ T _ H K _ _
  refine ⟨fun hHK => (a5_ordLE_iff T H K).mpr (CFSG.Quasithin.ordLE_of_le hHK),
    fun h₁ h₂ => ?_⟩
  rw [a5_vz_eq, a5_vz_eq]
  exact CFSG.Quasithin.VZ_eq_of_ordLE_of_ordLE ((a5_ordLE_iff _ _ _).mp h₁)
    ((a5_ordLE_iff _ _ _).mp h₂)

@[expose] def A_5_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → ∀ H K : Subgroup G, InHT T H → InHT T K →
      (∀ H' : Subgroup G, InHT T H' → VZ T H ≤ VZ T H' → VZ T H' = VZ T H) →
      (VZ T H ≤ VZ T K → K ≤ ChA.normalizerOf (VZ T H)) ∧
      (OrdLE T H K → K ≤ ChA.normalizerOf (VZ T H)) ∧
      IsUniqueMaxTwoLocalOver H (ChA.normalizerOf (VZ T H)) ∧
      (InMT T (ChA.normalizerOf (VZ T H)) ∧
        ∀ M' : Subgroup G, InMT T M' → OrdLE T (ChA.normalizerOf (VZ T H)) M' →
          M' = ChA.normalizerOf (VZ T H))

theorem as_A_5_10 : A_5_10 := by
  intro G _ _ _ hEC T hT H K hH hK hmax
  obtain ⟨S, rfl⟩ := a5_exists_sylow hT
  have hEven : quasithinEvenCharacteristic G := by
    first | exact a5_even hEC | exact a5_even_cha hEC
  have hmax' : Maximal (· ∈ CFSG.Quasithin.VFamily (S : Subgroup G)) (CFSG.Quasithin.VZ S H) := by
    refine ⟨CFSG.Quasithin.VZ_mem_VFamily hH, fun W hW hle => ?_⟩
    obtain ⟨H', hH', rfl⟩ := hW
    have h1 := hmax H' hH' (by rw [a5_vz_eq, a5_vz_eq]; exact hle)
    rw [a5_vz_eq, a5_vz_eq] at h1
    exact h1.le
  have h3 := CFSG.Quasithin.A510.isUniqueM_normalizer hEven S hH hmax'
  have h4 := CFSG.Quasithin.A510.isOrdMaximalIn_normalizer hEven S hH hmax'
  simp only [a5_vz_eq]
  refine ⟨fun h => CFSG.Quasithin.A510.le_normalizer_of_le hK hmax' h,
    fun h => CFSG.Quasithin.A510.le_normalizer_of_ordLE hK hmax' ((a5_ordLE_iff _ _ _).mp h),
    (a5_isUniqueMaxTwoLocalOver_iff _ _).mpr h3, h4.1,
    fun M' hM' hle => h4.2 M' hM' ((a5_ordLE_iff _ _ _).mp hle)⟩

end CFSG.ASVolI
