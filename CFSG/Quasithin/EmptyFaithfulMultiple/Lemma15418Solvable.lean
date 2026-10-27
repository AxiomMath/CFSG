module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15418Triple
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section General

variable {G : Type*} [Group G]

theorem commutator_le_right_of_le_normalizer {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) : ⁅A, B⁆ ≤ B := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (h ha) b).mp hb) (B.inv_mem hb)

variable [Finite G]

theorem charTwo_of_isSolvable_of_oddCoreIn_eq_bot {I : Subgroup G} (hsolv : Group.IsSolvable ↥I)
    (hO : oddCoreIn I = ⊥) : CharTwo I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : fusionOddCore ↥I = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ I.subtype_injective).mp hO
  have hcore : CFSG.pPrimeCore 2 ↥I = ⊥ := by
    rw [← h1]
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]
  have hlayer : CFSG.layer ↥I = ⊥ := by
    rw [CFSG.layer_eq_componentClassification]
    have : Group.IsPerfect (CFSG.ComponentClassification.Layer.subgroup ↥I) :=
      CFSG.ComponentClassification.Layer.perfect ↥I
    have : Subsingleton (CFSG.ComponentClassification.Layer.subgroup ↥I) :=
      CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
    exact Subgroup.eq_bot_of_subsingleton _
  have hc := CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot ↥I 2 hcore hlayer
  rw [charTwo_iff_internal]
  exact hc

theorem isSolvable_of_commutator_le {I S : Subgroup G} (hS : IsSylowTwoOf S I)
    (hN : I ⊓ Subgroup.normalizer (S : Set G) ≤ S) (hab : ⁅S, S⁆ ≤ pCoreOf 2 I) :
    Group.IsSolvable ↥I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := Open.pCore 2 ↥I
  have hOn : O.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  set π := QuotientGroup.mk' O
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  set S' : Sylow 2 ↥I := A4.toSylow hS
  have hS'eq : (S' : Subgroup ↥I) = S.subgroupOf I := A4.toSylow_coe hS
  set P : Sylow 2 (↥I ⧸ O) := S'.mapSurjective hπ
  have hPeq : (P : Subgroup (↥I ⧸ O)) = (S' : Subgroup ↥I).map π := Sylow.coe_mapSurjective _ _
  have hOS : O ≤ (S' : Subgroup ↥I) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup 2).le_sylow_of_normal S'
  have hcomap : ((S' : Subgroup ↥I).map π).comap π = (S' : Subgroup ↥I) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hOS]
  have hPab : ∀ a ∈ (P : Subgroup (↥I ⧸ O)), ∀ b ∈ (P : Subgroup (↥I ⧸ O)), a * b = b * a := by
    intro a ha b hb
    rw [hPeq] at ha hb
    obtain ⟨s₁, hs₁, rfl⟩ := ha
    obtain ⟨s₂, hs₂, rfl⟩ := hb
    rw [hS'eq] at hs₁ hs₂
    have hc : (s₁ * s₂ * s₁⁻¹ * s₂⁻¹ : ↥I) ∈ O := by
      have hmem : ((s₁ * s₂ * s₁⁻¹ * s₂⁻¹ : ↥I) : G) ∈ pCoreOf 2 I := by
        apply hab
        have := Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hs₁)
          (Subgroup.mem_subgroupOf.mp hs₂)
        simpa [commutatorElement_def] using this
      obtain ⟨o, ho, hoe⟩ := hmem
      rwa [← Subtype.ext hoe]
    have h1 : π (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hc
    simp only [map_mul, map_inv] at h1
    calc π s₁ * π s₂ = π s₁ * π s₂ * (π s₁)⁻¹ * (π s₂)⁻¹ * (π s₂ * π s₁) := by group
      _ = π s₂ * π s₁ := by rw [h1, one_mul]
  have hNP : Subgroup.normalizer ((P : Subgroup (↥I ⧸ O)) : Set (↥I ⧸ O)) ≤ P := by
    intro q hq
    obtain ⟨g, rfl⟩ := hπ q
    have hgN : g ∈ Subgroup.normalizer ((S' : Subgroup ↥I) : Set ↥I) := by
      have key : ∀ h : ↥I, π h ∈ Subgroup.normalizer ((P : Subgroup (↥I ⧸ O)) : Set (↥I ⧸ O)) →
          ∀ s ∈ (S' : Subgroup ↥I), h * s * h⁻¹ ∈ (S' : Subgroup ↥I) := by
        intro h hh s hs
        rw [← hcomap, Subgroup.mem_comap, map_mul, map_mul, map_inv, ← hPeq]
        exact (Subgroup.mem_normalizer_iff.mp hh (π s)).mp (hPeq ▸ ⟨s, hs, rfl⟩)
      rw [Subgroup.mem_normalizer_iff]
      intro s
      refine ⟨key g hq s, fun h => ?_⟩
      have := key g⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hq) _ h
      simpa [mul_assoc] using this
    have hgG : (g : G) ∈ Subgroup.normalizer (S : Set G) := by
      have : g ∈ (Subgroup.normalizer (S : Set G)).subgroupOf I := by
        rw [Subgroup.subgroupOf_normalizer_eq hS.1, ← hS'eq]
        exact hgN
      exact Subgroup.mem_subgroupOf.mp this
    have hgS : g ∈ (S' : Subgroup ↥I) := by
      rw [hS'eq, Subgroup.mem_subgroupOf]
      exact hN ⟨g.2, hgG⟩
    rw [hPeq]
    exact ⟨g, hgS, rfl⟩
  have hPC : Subgroup.normalizer ((P : Subgroup (↥I ⧸ O)) : Set (↥I ⧸ O)) ≤
      Subgroup.centralizer ((P : Subgroup (↥I ⧸ O)) : Set (↥I ⧸ O)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hPab y hy x (hNP hx)
  set K := (MonoidHom.transferSylow P hPC).ker
  have hK : ¬ 2 ∣ Nat.card K := MonoidHom.not_dvd_card_ker_transferSylow P hPC
  have hKsolv : Group.IsSolvable K :=
    CFSG.Milestones.odd_order_solvable (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hK))
  have hPsolv : Group.IsSolvable ↥(P : Subgroup (↥I ⧸ O)) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hPab a a.2 b b.2)
  have hQsolv : Group.IsSolvable (↥I ⧸ O) :=
    Group.isSolvable_of_ker_le_range K.subtype (MonoidHom.transferSylow P hPC)
      (by rw [Subgroup.range_subtype])
  have hOsolv : Group.IsSolvable O := by
    have := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥I) 2).isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range O.subtype π
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end General

section Product

variable {K : Type*} [Group K]

theorem mul_comm_of_mem_oTwoUpper_biSup (𝓘 : Finset (Subgroup K))
    (hcomm : ∀ L ∈ 𝓘, ∀ L' ∈ 𝓘, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hA : ∀ L ∈ 𝓘, ∃ g ∈ L, (∀ x ∈ L, x ^ 2 ∈ Subgroup.zpowers g) ∧
      ∀ x ∈ L, ∀ y ∈ L, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers g)
    {x y : K} (hx : x ∈ oTwoUpper (⨆ L ∈ 𝓘, L)) (hy : y ∈ oTwoUpper (⨆ L ∈ 𝓘, L)) :
    x * y = y * x := by
  classical
  choose! g hgL hsq hcm using hA
  set J := ⨆ L ∈ 𝓘, L
  set A := ⨆ L ∈ 𝓘, Subgroup.zpowers (g L)
  have hLJ : ∀ L ∈ 𝓘, L ≤ J := fun L hL =>
    le_iSup₂_of_le (f := fun (L' : Subgroup K) (_ : L' ∈ 𝓘) => L') L hL le_rfl
  have hZA : ∀ L ∈ 𝓘, Subgroup.zpowers (g L) ≤ A := fun L hL =>
    le_iSup₂_of_le (f := fun (L' : Subgroup K) (_ : L' ∈ 𝓘) => Subgroup.zpowers (g L')) L hL
      le_rfl
  have hzL : ∀ L ∈ 𝓘, Subgroup.zpowers (g L) ≤ L := fun L hL =>
    Subgroup.zpowers_le.mpr (hgL L hL)
  have hgcomm : ∀ L ∈ 𝓘, ∀ L' ∈ 𝓘, ∀ a ∈ Subgroup.zpowers (g L),
      ∀ b ∈ Subgroup.zpowers (g L'), a * b = b * a := by
    intro L hL L' hL' a ha b hb
    by_cases h : L = L'
    · subst h
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self (g L) m n).eq
    · exact hcomm L hL L' hL' h a (hzL L hL ha) b (hzL L' hL' hb)
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    refine B1.iSup₂_induction_finset 𝓘 (fun L => Subgroup.zpowers (g L))
      (C := fun a => ∀ b ∈ A, a * b = b * a) ha ?_ ?_ ?_ b hb
    · intro L hL a ha b hb
      refine B1.iSup₂_induction_finset 𝓘 (fun L => Subgroup.zpowers (g L))
        (C := fun b => a * b = b * a) hb ?_ ?_ ?_
      · intro L' hL' b hb
        exact hgcomm L hL L' hL' a ha b hb
      · simp
      · intro b c hb hc
        rw [← mul_assoc, hb, mul_assoc, hc, mul_assoc]
    · intro b _
      simp
    · intro a₁ a₂ h₁ h₂ b hb
      rw [mul_assoc, h₂ b hb, ← mul_assoc, h₁ b hb, mul_assoc]
  have hgen : ∀ L ∈ 𝓘, ∀ x ∈ L, ∀ a ∈ A, x * a * x⁻¹ ∈ A := by
    intro L hL x hx a ha
    refine B1.iSup₂_induction_finset 𝓘 (fun L => Subgroup.zpowers (g L))
      (C := fun a => x * a * x⁻¹ ∈ A) ha ?_ ?_ ?_
    · intro L' hL' a ha
      by_cases h : L = L'
      · subst h
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        have hxg : x * g L * x⁻¹ ∈ Subgroup.zpowers (g L) := by
          have h1 := hcm L hL x hx (g L) (hgL L hL)
          have e : x * g L * x⁻¹ = (x * g L * x⁻¹ * (g L)⁻¹) * g L := by group
          rw [e]
          exact Subgroup.mul_mem _ h1 (Subgroup.mem_zpowers _)
        rw [← conj_zpow]
        exact hZA L hL (Subgroup.zpow_mem _ hxg n)
      · rw [hcomm L hL L' hL' h x hx a (hzL L' hL' ha), mul_inv_cancel_right]
        exact hZA L' hL' ha
    · simp
    · intro a b ha hb
      have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [e]
      exact A.mul_mem ha hb
  have hconj : ∀ x ∈ J, ∀ a ∈ A, x * a * x⁻¹ ∈ A := by
    intro x hx
    refine B1.iSup₂_induction_finset 𝓘 (fun L => L)
      (C := fun x => ∀ a ∈ A, x * a * x⁻¹ ∈ A) hx (fun L hL x hx => hgen L hL x hx) ?_ ?_
    · intro a ha
      simpa using ha
    · intro x₁ x₂ h₁ h₂ a ha
      have e : x₁ * x₂ * a * (x₁ * x₂)⁻¹ = x₁ * (x₂ * a * x₂⁻¹) * x₁⁻¹ := by group
      rw [e]
      exact h₁ _ (h₂ a ha)
  have hcomJ : ∀ x ∈ J, ∀ y ∈ J, x * y * x⁻¹ * y⁻¹ ∈ A := by
    intro x hx
    refine B1.iSup₂_induction_finset 𝓘 (fun L => L)
      (C := fun x => x ∈ J ∧ ∀ y ∈ J, x * y * x⁻¹ * y⁻¹ ∈ A) hx ?_ ?_ ?_ |>.2
    · intro L hL x hx
      refine ⟨hLJ L hL hx, fun y hy => ?_⟩
      refine B1.iSup₂_induction_finset 𝓘 (fun L => L)
        (C := fun y => y ∈ J ∧ x * y * x⁻¹ * y⁻¹ ∈ A) hy ?_ ?_ ?_ |>.2
      · intro L' hL' y hy
        refine ⟨hLJ L' hL' hy, ?_⟩
        by_cases h : L = L'
        · subst h
          exact hZA L hL (hcm L hL x hx y hy)
        · rw [hcomm L hL L' hL' h x hx y hy]
          simp
      · exact ⟨J.one_mem, by simp⟩
      · rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
        refine ⟨J.mul_mem hy₁ hy₂, ?_⟩
        have e : x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ =
            (x * y₁ * x⁻¹ * y₁⁻¹) * (y₁ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
        rw [e]
        exact A.mul_mem h₁ (hconj y₁ hy₁ _ h₂)
    · exact ⟨J.one_mem, fun y _ => by simp⟩
    · rintro x₁ x₂ ⟨hx₁, h₁⟩ ⟨hx₂, h₂⟩
      refine ⟨J.mul_mem hx₁ hx₂, fun y hy => ?_⟩
      have e : x₁ * x₂ * y * (x₁ * x₂)⁻¹ * y⁻¹ =
          (x₁ * (x₂ * y * x₂⁻¹ * y⁻¹) * x₁⁻¹) * (x₁ * y * x₁⁻¹ * y⁻¹) := by group
      rw [e]
      exact A.mul_mem (hconj x₁ hx₁ _ (h₂ y hy)) (h₁ y hy)
  have hsqJ : ∀ x ∈ J, x ^ 2 ∈ A := by
    intro x hx
    refine B1.iSup₂_induction_finset 𝓘 (fun L => L)
      (C := fun x => x ∈ J ∧ x ^ 2 ∈ A) hx ?_ ?_ ?_ |>.2
    · intro L hL x hx
      exact ⟨hLJ L hL hx, hZA L hL (hsq L hL x hx)⟩
    · exact ⟨J.one_mem, by simp⟩
    · rintro x₁ x₂ ⟨hx₁, h₁⟩ ⟨hx₂, h₂⟩
      refine ⟨J.mul_mem hx₁ hx₂, ?_⟩
      have e : (x₁ * x₂) ^ 2 = x₁ ^ 2 * (x₁⁻¹ * x₂ * x₁⁻¹⁻¹ * x₂⁻¹) * x₂ ^ 2 := by
        simp only [sq]
        group
      rw [e]
      exact A.mul_mem (A.mul_mem h₁ (hcomJ _ (J.inv_mem hx₁) _ hx₂)) h₂
  have hle : oTwoUpper J ≤ A := by
    refine (Subgroup.closure_le A).mpr fun z hz => ?_
    have hcop : Nat.Coprime 2 (orderOf z) := Nat.coprime_two_left.mpr hz.2
    exact (Subgroup.zpowers_le.mpr (hsqJ z hz.1)) (A4.mem_zpowers_pow_of_coprime hcop)
  exact hAcomm x (hle hx) y (hle hy)

end Product

@[expose] def sl22Three : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  ⟨!![0, 1; 1, 1], by decide⟩

theorem sl22_sq_cases : ∀ x : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    x ^ 2 = 1 ∨ x ^ 2 = sl22Three ∨ x ^ 2 = sl22Three ^ 2 := by decide

theorem sl22_commutator_cases : ∀ x y : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = sl22Three ∨
      x * y * x⁻¹ * y⁻¹ = sl22Three ^ 2 := by decide

theorem exists_zpowers_of_mulEquiv {K : Type*} [Group K] {L : Subgroup K}
    (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    ∃ g ∈ L, (∀ x ∈ L, x ^ 2 ∈ Subgroup.zpowers g) ∧
      ∀ x ∈ L, ∀ y ∈ L, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers g := by
  set g : K := ((e.symm sl22Three : L) : K)
  have key : ∀ z : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      z = 1 ∨ z = sl22Three ∨ z = sl22Three ^ 2 →
        ((e.symm z : L) : K) ∈ Subgroup.zpowers g := by
    rintro z (rfl | rfl | rfl)
    · simp
    · exact Subgroup.mem_zpowers _
    · rw [map_pow, Subgroup.coe_pow]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  refine ⟨g, (e.symm sl22Three).2, fun x hx => ?_, fun x hx y hy => ?_⟩
  · have h := key _ (sl22_sq_cases (e ⟨x, hx⟩))
    rwa [map_pow, MulEquiv.symm_apply_apply, Subgroup.coe_pow] at h
  · have h := key _ (sl22_commutator_cases (e ⟨x, hx⟩) (e ⟨y, hy⟩))
    rwa [← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul, MulEquiv.symm_apply_apply]
      at h

theorem autI_eq_oTwoUpper {G : Type*} [Group G] [Finite G] {V Y : Subgroup G}
    (hV : IsElemAbelian 2 V) (hYN : Y ≤ Subgroup.normalizer (V : Set G)) (hY : Y = oTwoUpper Y) :
    autI hV Y = oTwoUpper (autI hV Y) := by
  have hsub : oTwoUpper (Y.subgroupOf (Subgroup.normalizer (V : Set G))) =
      Y.subgroupOf (Subgroup.normalizer (V : Set G)) := by
    apply Subgroup.map_injective (Subgroup.normalizer (V : Set G)).subtype_injective
    rw [← oTwoUpper_map, Subgroup.map_subgroupOf_eq_of_le hYN]
    exact hY.symm
  unfold autI
  rw [oTwoUpper_map, hsub]


namespace Config15418

variable {G : Type} [Group G] [Finite G] {T : Subgroup G} (c : Config15418 G T)
  (H : Hyp15418 G T)
include H

theorem not_Y_le_baum : ¬ c.Y ≤ baum T := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY2 : IsPGroup 2 c.Y := H.hyp.sylow.1.to_le (h.trans inf_le_left)
  have hO : pCoreOf 2 c.Y = c.Y :=
    le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 c.Y)
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hY2)
  have h3 := c.three
  rw [hO, Subgroup.relIndex_self] at h3
  omega

theorem false_of_isSolvable (hsolv : Group.IsSolvable ↥c.I) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : CharTwo c.I := charTwo_of_isSolvable_of_oddCoreIn_eq_bot hsolv (c.oddCoreIn_I_eq_bot H)
  have hT := c.isSylowTwoOf_I H
  have hTp : IsPGroup 2 T := H.hyp.sylow.1
  obtain ⟨hU, hred, hcase, -⟩ := B2_16 hsolv hF hT rfl
  set V := conjClosure (quasithinOmegaOneCenter (baum T)) c.I
  have hIV : c.I ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure _ _
  have hZV : quasithinOmegaOneCenter T ≤ V := by
    intro z hz
    have hz' : z ∈ quasithinOmegaOneCenter (baum T) := by
      obtain ⟨hzT, hzC, hz2⟩ := mem_quasithinOmegaOneCenter_iff.mp hz
      refine mem_quasithinOmegaOneCenter_iff.mpr ⟨(omegaOneCenter_le_eOf' T).trans
        (eOf_le_baum T) hz, Subgroup.centralizer_le
          (SetLike.coe_subset_coe.mpr inf_le_left) hzC, hz2⟩
    have := mem_conjClosure (Z := quasithinOmegaOneCenter (baum T)) (Subgroup.one_mem c.I) hz'
    simp only [one_mul, inv_one, mul_one] at this
    exact this
  set K := c.I ⊓ Subgroup.centralizer (V : Set G)
  have hKS : K ≤ baum T := by
    refine le_trans ?_ (c.I_inf_centralizer_Z H).le
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZV))
  have hIK : c.I ≤ Subgroup.normalizer (K : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      B2F.normalizer_le_normalizer_centralizer V (hIV hx)⟩
  have hY : c.Y = ⁅c.Y, thompsonJ (baum T)⁆ := by
    have h := c.thompson₁ H
    rw [c.oTwoUpper_G₁ hTp] at h
    exact h.symm
  have hX₁ : c.X₁ = ⁅c.X₁, thompsonJ (baum T)⁆ := by
    have h := c.thompson₂ H
    rw [c.oTwoUpper_G₂ hTp] at h
    exact h.symm
  rcases hcase with ⟨hJ, -⟩ | ⟨-, 𝓘, -, hJeq, hcomm, -, hnat, -⟩
  ·
    apply c.not_Y_le_baum H
    refine le_trans ?_ hKS
    rw [hY]
    refine (Subgroup.commutator_mono le_rfl (le_inf ((thompsonJ_le_self _).trans c.baum_le_I)
      hJ)).trans ?_
    exact commutator_le_right_of_le_normalizer (c.Y_le_I.trans hIK)
  ·
    have hJI : ∀ W : Subgroup G, W ≤ c.I → W = ⁅W, thompsonJ (baum T)⁆ →
        W ≤ thompsonJ c.I := by
      intro W hW hWJ
      rw [hWJ]
      refine (Subgroup.commutator_mono le_rfl (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)).trans ?_
      refine commutator_le_right_of_le_normalizer (hW.trans ?_)
      exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ c.I)
    have hA : ∀ L ∈ 𝓘, ∃ g ∈ L, (∀ x ∈ L, x ^ 2 ∈ Subgroup.zpowers g) ∧
        ∀ x ∈ L, ∀ y ∈ L, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers g := by
      intro L hL
      obtain ⟨e, -⟩ := hnat L hL
      exact exists_zpowers_of_mulEquiv e
    have hmem : ∀ W : Subgroup G, W ≤ c.I → W = ⁅W, thompsonJ (baum T)⁆ → W = oTwoUpper W →
        autI hU W ≤ oTwoUpper (⨆ L ∈ 𝓘, L) := by
      intro W hW hWJ hWO
      rw [autI_eq_oTwoUpper hU (hW.trans hIV) hWO, ← hJeq]
      exact oTwoUpper_mono (autI_mono hU (hJI W hW hWJ))
    have hYm := hmem c.Y c.Y_le_I hY c.famY.eq_oTwoUpper
    have hXm := hmem c.X₁ c.X₁_le_I hX₁ c.dataX.2.1
    have hcomm' : ∀ x ∈ c.X₁, ∀ y ∈ c.Y, x * y * x⁻¹ * y⁻¹ ∈ K := by
      intro x hx y hy
      have hxN := hIV (c.X₁_le_I hx)
      have hyN := hIV (c.Y_le_I hy)
      have h := mul_comm_of_mem_oTwoUpper_biSup 𝓘 hcomm hA
        (hXm (convI_mem_autI hU hx hxN)) (hYm (convI_mem_autI hU hy hyN))
      have h1 : convI hU (⟨x, hxN⟩ * ⟨y, hyN⟩ * ⟨x, hxN⟩⁻¹ * ⟨y, hyN⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
        group
      have h2 := (convI_eq_one_iff hU _).mp h1
      refine ⟨c.I.mul_mem (c.I.mul_mem (c.I.mul_mem (c.X₁_le_I hx) (c.Y_le_I hy))
        (c.I.inv_mem (c.X₁_le_I hx))) (c.I.inv_mem (c.Y_le_I hy)), ?_⟩
      simpa using h2
    have hKY : K ≤ Subgroup.normalizer (c.Y : Set G) := hKS.trans c.baum_le_normalizer_Y
    have hXN : c.X₁ ≤ Subgroup.normalizer ((c.Y ⊔ K : Subgroup G) : Set G) := by
      intro x hx
      have hle : (c.Y ⊔ K).map (MulAut.conj x).toMonoidHom ≤ c.Y ⊔ K := by
        rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hIK (c.X₁_le_I hx))]
        refine sup_le ?_ le_sup_right
        rintro _ ⟨w, hw, rfl⟩
        have e : (MulAut.conj x).toMonoidHom w = (x * w * x⁻¹ * w⁻¹) * w := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcomm' x hx w hw))
          (Subgroup.mem_sup_left hw)
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])
    have hO : oTwoUpper (c.Y ⊔ K) = c.Y :=
      oTwoUpper_sup_eq_of_isPGroup' (hTp.to_le (hKS.trans inf_le_left)) hKY c.famY.eq_oTwoUpper
    have hXY : c.X₁ ≤ Subgroup.normalizer (c.Y : Set G) := by
      rw [← hO]
      exact hXN.trans (normalizer_le_normalizer_oTwoUpper _)
    have hM := c.not_X₁_le_M₁ H
    rw [c.M₁_eq H] at hM
    exact hM hXY

include c in
theorem false_of_inspection (hInsp : Inspection15418) : False := by
  have hab := hInsp G c.I c.G₁ c.G₂ (baum T) T (quasithinOmegaOneCenter T) (c.inspectionData H)
  exact c.false_of_isSolvable H
    (isSolvable_of_commutator_le (c.isSylowTwoOf_I H) (c.normalizer_le H) hab)

end Config15418

end CFSG.Quasithin.EmptyFaithfulMultiple
