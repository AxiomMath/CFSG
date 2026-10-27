module

public import CFSG.Quasithin.H13.NQBlockResidualBar
public import CFSG.Quasithin.H13.NQBlockResidualSupplement
public import CFSG.Quasithin.H13.NQBlockSinglePrime
public import CFSG.Quasithin.H13.NQBlockCentralRadical
public import CFSG.Quasithin.H13.NQBlockEscapingComponent
public import CFSG.Quasithin.H13.NQBlockRadicalSylow

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup

theorem isSylowOf_map' {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup X} (h : CFSG.ABGLocalTools.IsSylowOf p P K) (f : X →* Y) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem bar_residual_facts
    {E : Type*} [Group E] [Finite E] {Lb Kb Nb Sb : Subgroup E}
    (hSQT : CFSG.IsStronglyQuasithin Lb) (hO2 : CFSG.pCore 2 Lb = ⊥)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup Lb)) (hq : ¬ CFSG.IsQuasisimple Lb)
    (hRad : CFSG.solvableRadical Lb = Nb.subgroupOf Lb)
    (hKL : Kb ≤ Lb) (hNL : Nb ≤ Lb) (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 Sb Nb)
    (hKperf : ⁅Kb, Kb⁆ = Kb) (hKS : Kb ≤ normalizer (Sb : Set E)) (hNK : Nb ⊔ Kb = Lb) :
    Nat.card Sb = 2 ∧ CFSG.IsQuasisimple Kb ∧
      Lb = (CFSG.fittingSubgroup Lb).map Lb.subtype ⊔ Kb ∧
      (CFSG.fittingSubgroup Lb).map Lb.subtype ⊓ Kb = ⊥ ∧
      (center Kb).map Kb.subtype = Sb ∧ (CFSG.pCore 2 Kb).map Kb.subtype = Sb ∧
      Kb ⊓ Nb = Sb ∧
      ∃ (s : ℕ) (_ : Fact s.Prime), 5 ≤ s ∧ Nonempty (Lb ⧸ CFSG.solvableRadical Lb ≃*
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 (ZMod s)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSN : Sb ≤ Nb := ((CFSG.ABGLocalTools.isSylowOf_iff).mp hSyl).1
  have hSL : Sb ≤ Lb := hSN.trans hNL
  obtain ⟨-, -, hsL, hall⟩ :=
    two_core_free_radical_Sylow_involution_has_central_radical_centralizer hSQT hO2 hLC hq
  have hS'map : (Sb.subgroupOf Lb).map Lb.subtype = Sb := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hSL]
  have hSyl' : CFSG.ABGLocalTools.IsSylowOf 2 (Sb.subgroupOf Lb) (CFSG.solvableRadical Lb) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff Lb, hS'map, hRad, subgroupOf_map_subtype,
      inf_eq_left.mpr hNL]
    exact hSyl
  obtain ⟨hS2, hT⟩ := hall _ hSyl'
  have hcardS : Nat.card Sb = 2 := by
    rw [← hS'map, card_map_of_injective Lb.subtype_injective]
    exact hS2
  have : Nontrivial (Sb.subgroupOf Lb) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hS2]; norm_num)
  obtain ⟨⟨t, ht⟩, ht1⟩ := exists_ne (1 : Sb.subgroupOf Lb)
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  obtain ⟨hSt, -, -, -, -, -, -, -, hJall⟩ := hT t ht ht1'
  have hot : orderOf t = 2 := by
    rw [← Nat.card_zpowers, ← hSt, hS2]
  have hS'elt : ∀ y ∈ Sb.subgroupOf Lb, y = 1 ∨ y = t := by
    intro y hy
    rw [hSt, mem_zpowers_iff_mem_range_orderOf, hot] at hy
    simp only [Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    interval_cases k
    · left
      exact pow_zero t
    · right
      exact pow_one t
  have hJmap : (Kb.subgroupOf Lb).map Lb.subtype = Kb := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hKL]
  have hJperf : Group.IsPerfect (Kb.subgroupOf Lb) := by
    rw [Subgroup.isPerfect_iff]
    apply map_injective Lb.subtype_injective
    rw [map_commutator, hJmap, hKperf]
  have hJt : Kb.subgroupOf Lb ≤ centralizer ({t} : Set Lb) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxN : x ∈ normalizer ((Sb.subgroupOf Lb : Subgroup Lb) : Set Lb) := by
      rw [← subgroupOf_normalizer_eq hSL]
      exact hKS hx
    have hxt : x * t * x⁻¹ ∈ Sb.subgroupOf Lb := (mem_normalizer_iff.mp hxN t).mp ht
    rcases hS'elt _ hxt with h | h
    · exfalso
      apply ht1'
      have : t = x⁻¹ * (x * t * x⁻¹) * x := by group
      rw [this, h]
      group
    · calc x * t = x * t * x⁻¹ * x := by group
        _ = t * x := by rw [h]
  have hRJ : CFSG.solvableRadical Lb ⊔ Kb.subgroupOf Lb = ⊤ := by
    rw [hRad]
    apply map_injective Lb.subtype_injective
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr hNL, hJmap, hNK,
      ← MonoidHom.range_eq_map, range_subtype]
  obtain ⟨hFJ, hJF, hJq, hJR, hZJ, hSO, -, -, -⟩ := hJall _ hJperf hJt hRJ
  set e : Kb.subgroupOf Lb ≃* Kb := subgroupOfEquivOfLe hKL with he
  have hcomp : Kb.subtype.comp e.toMonoidHom = Lb.subtype.comp (Kb.subgroupOf Lb).subtype := by
    ext x
    rfl
  have hcomp' : Kb.subtype.comp (e : Kb.subgroupOf Lb →* Kb) =
      Lb.subtype.comp (Kb.subgroupOf Lb).subtype := by
    ext x
    rfl
  have hZ : (center Kb).map Kb.subtype = Sb := by
    rw [← map_center_eq e, map_map, hcomp', ← map_map, hZJ, hS'map]
  have hO : (CFSG.pCore 2 Kb).map Kb.subtype = Sb := by
    rw [← CFSG.LieType.SteinbergBR.pCore_map_equiv 2 e, map_map, hcomp, ← map_map, ← hSO,
      hS'map]
  refine ⟨hcardS, CFSG.LocalCores.isQuasisimple_of_mulEquiv e hJq, ?_, ?_, hZ, hO, ?_, hsL⟩
  · have h := congrArg (Subgroup.map Lb.subtype) hFJ
    rwa [Subgroup.map_sup, hJmap, ← MonoidHom.range_eq_map, range_subtype, eq_comm] at h
  · have h := congrArg (Subgroup.map Lb.subtype) hJF
    rwa [map_inf_eq _ _ _ Lb.subtype_injective, hJmap, Subgroup.map_bot, inf_comm] at h
  · have h := congrArg (Subgroup.map Lb.subtype) hJR
    rwa [map_inf_eq _ _ _ Lb.subtype_injective, hJmap, hRad, subgroupOf_map_subtype,
      inf_eq_left.mpr hNL, hZJ, hS'map] at h

theorem map_pCore_le_of_surjective {X Y : Type*} [Group X] [Group Y] {p : ℕ} (f : X →* Y)
    (hf : Function.Surjective f) : (CFSG.pCore p X).map f ≤ CFSG.pCore p Y :=
  CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup
    ((inferInstance : (CFSG.pCore p X).Normal).map f hf) (CFSG.pCore_isPGroup.map f)

theorem residual_two_core {B E : Type*} [Group B] [Finite B] [Group E] (π : B →* E)
    {K N Q : Subgroup B} {Sb : Subgroup E} [N.Normal] (hker : π.ker = Q) (hQN : Q ≤ N)
    (hQ2 : IsPGroup 2 Q) (hO : (CFSG.pCore 2 (K.map π)).map (K.map π).subtype = Sb)
    (hKN : K.map π ⊓ N.map π = Sb) (hS2 : IsPGroup 2 Sb) :
    K ⊓ N = (CFSG.pCore 2 K).map K.subtype ∧ K ⊓ Q ≤ (CFSG.pCore 2 K).map K.subtype ∧
      ((CFSG.pCore 2 K).map K.subtype).map π = Sb := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomap : (N.map π).comap π = N := by rw [comap_map_eq, hker, sup_eq_left.mpr hQN]
  let φ : K →* (K.map π) := (π.comp K.subtype).codRestrict _ fun k => mem_map_of_mem π k.2
  have hφs : Function.Surjective φ := by
    rintro ⟨_, k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  have hK₂map : ((CFSG.pCore 2 K).map K.subtype).map π =
      ((CFSG.pCore 2 K).map φ).map (K.map π).subtype := by
    rw [map_map, map_map]
    rfl
  have hK₂S : ((CFSG.pCore 2 K).map K.subtype).map π ≤ Sb := by
    rw [hK₂map, ← hO]
    exact map_mono (map_pCore_le_of_surjective φ hφs)
  have hSK : Sb ≤ K.map π := hKN ▸ inf_le_left
  have hSN : Sb ≤ N.map π := hKN ▸ inf_le_right
  have hK₂N : (CFSG.pCore 2 K).map K.subtype ≤ N := by
    intro x hx
    rw [← hcomap]
    exact hSN (hK₂S (mem_map_of_mem π hx))
  have hKN2 : IsPGroup 2 (K ⊓ N : Subgroup B) := by
    intro x
    have hxS : π x ∈ Sb :=
      hKN.le (mem_inf.mpr ⟨mem_map_of_mem π (mem_inf.mp x.2).1,
        mem_map_of_mem π (mem_inf.mp x.2).2⟩)
    obtain ⟨a, ha⟩ := hS2 ⟨π x, hxS⟩
    have ha' : π ((x : B) ^ 2 ^ a) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val ha
    have hxa : (x : B) ^ 2 ^ a ∈ Q := by
      rw [← hker]
      exact ha'
    obtain ⟨b, hb⟩ := hQ2 ⟨_, hxa⟩
    have hb' : ((x : B) ^ 2 ^ a) ^ 2 ^ b = 1 := congrArg Subtype.val hb
    refine ⟨a + b, Subtype.ext ?_⟩
    rw [coe_pow, coe_one, pow_add, pow_mul, hb']
  have hKNle : K ⊓ N ≤ (CFSG.pCore 2 K).map K.subtype := by
    have hp : IsPGroup 2 ((K ⊓ N).subgroupOf K) :=
      hKN2.of_equiv (subgroupOfEquivOfLe inf_le_left).symm
    have hn : ((K ⊓ N).subgroupOf K).Normal := by
      rw [inf_subgroupOf_left]
      infer_instance
    have h2 := map_mono (f := K.subtype)
      (CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup hn hp)
    rwa [subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left] at h2
  have hKNeq : K ⊓ N = (CFSG.pCore 2 K).map K.subtype :=
    le_antisymm hKNle (le_inf (map_subtype_le _) hK₂N)
  refine ⟨hKNeq, (inf_le_inf_left K hQN).trans hKNle, le_antisymm hK₂S fun s hs => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hSK hs
  have hkN : k ∈ N := by
    rw [← hcomap]
    exact hSN hs
  exact mem_map_of_mem π (hKNle (mem_inf.mpr ⟨hk, hkN⟩))

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL) in
theorem radical_Sylow_normalizer_residual_is_common_simple_two_core_supplement
    {B : Type*}
    [Group B] [Finite B] (L : Subgroup B) [L.Normal] (T : Sylow 2 B)
    (hBLT : L ⊔ (T : Subgroup B) = ⊤) (hSQT : CFSG.IsStronglyQuasithin L)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup L)) (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L))
    (N C R A K : Subgroup B) (hN : N = (CFSG.solvableRadical L).map L.subtype)
    (hC : ∀ b : B, b ∈ C ↔ ∀ x ∈ L, x⁻¹ * (b * x * b⁻¹) ∈ N)
    (hR : R = (T : Subgroup B) ⊓ C) (hA : A = L ⊓ normalizer (R : Set B))
    (hK : K = (CFSG.perfectResidual A).map A.subtype) :
    (CFSG.pCore 2 L).map L.subtype ≤ R ∧
    K ≠ ⊥ ∧ ⁅K, K⁆ = K ∧ (T : Subgroup B) ≤ normalizer (K : Set B) ∧ L = N ⊔ K ∧
    CFSG.IsCComponent (K.subgroupOf (K ⊔ T)) ∧ R ≤ K ⊔ T ∧ (R.subgroupOf (K ⊔ T)).Normal ∧
    Nat.card ((R ⊓ L).map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))) = 2 ∧
    CFSG.IsQuasisimple (K.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))) ∧
    L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)) =
      (CFSG.fittingSubgroup (L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)))).map
        (L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))).subtype ⊔
      K.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)) ∧
    (CFSG.fittingSubgroup (L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)))).map
        (L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))).subtype ⊓
      K.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)) = ⊥ ∧
    (center (K.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)))).map
        (K.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))).subtype =
      (R ⊓ L).map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)) ∧
    (CFSG.pCore 2 (K.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)))).map
        (K.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))).subtype =
      (R ⊓ L).map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)) ∧
    K ⊓ N = (CFSG.pCore 2 K).map K.subtype ∧
    K ⊓ (CFSG.pCore 2 L).map L.subtype ≤ (CFSG.pCore 2 K).map K.subtype ∧
    Nonempty (((CFSG.pCore 2 K).map K.subtype : Subgroup B) ⧸
        ((CFSG.pCore 2 L).map L.subtype).subgroupOf ((CFSG.pCore 2 K).map K.subtype) ≃*
      (R ⊓ L).map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))) ∧
    (∃ e : K ⧸ CFSG.pCore 2 K ≃* L ⧸ CFSG.solvableRadical L,
      ∀ (k : K) (hk : (k : B) ∈ L), e (QuotientGroup.mk k) = QuotientGroup.mk (⟨k, hk⟩ : L)) ∧
    (∃ (s : ℕ) (_ : Fact s.Prime), 5 ≤ s ∧
      Nonempty (L ⧸ CFSG.solvableRadical L ≃* projectiveSL 2 (ZMod s))) ∧
    ∀ L₁ : Subgroup B, L₁ ≤ L → (T : Subgroup B) ≤ normalizer (L₁ : Set B) → L = N ⊔ L₁ →
      L₁ = (L₁ ⊓ N) ⊔ (L₁ ⊓ normalizer (R : Set B)) ∧ L₁ = (L₁ ⊓ N) ⊔ K ∧
      (CFSG.perfectResidual ↥(L₁ ⊓ normalizer (R : Set B))).map
        (L₁ ⊓ normalizer (R : Set B)).subtype = K ∧ K ≤ L₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimple, hnab⟩ := simple_radical_quotient_of_isCComponent_top hLC
  obtain ⟨h1, h2, ⟨S, hS⟩, -, h5, h6, -, -, -, h10, h11, h12, -, h14, h15, -, -, h18, h19, h20⟩ :=
    radical_Sylow_normalizer_perfect_residual_supplement L T hBLT hsimple hnab N C R A K hN hC hR
      hA hK
  obtain ⟨hRadchar, hRadsolv, hRadmax, -⟩ :=
    CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L
  have hNn : N.Normal := by
    rw [hN]
    infer_instance
  have hNL : N ≤ L := hN ▸ map_subtype_le _
  have hRT : R ≤ T := hR ▸ inf_le_left
  have hRC : R ≤ C := hR ▸ inf_le_right
  have hNC : N ≤ C := h2 ▸ le_sup_left
  have hCn : C.Normal := h1 ▸ CFSG.ABGLocalTools.solvableRadical_normal
  have hCs : Group.IsSolvable C := h1 ▸ CFSG.ABGLocalTools.solvableRadical_isSolvable
  have hQ2 : IsPGroup 2 ((CFSG.pCore 2 L).map L.subtype) := CFSG.pCore_isPGroup.map _
  have hQN : (CFSG.pCore 2 L).map L.subtype ≤ N := by
    rw [hN]
    refine map_mono (hRadmax _ inferInstance ?_)
    have := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 L)).isNilpotent
    infer_instance
  have hQR : (CFSG.pCore 2 L).map L.subtype ≤ R :=
    (CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup inferInstance hQ2).trans h5
  have hTNR : (T : Subgroup B) ≤ normalizer (R : Set B) := h6 ▸ le_sup_right
  have hTK : (T : Subgroup B) ≤ normalizer (K : Set B) :=
    hTNR.trans ((normal_subgroupOf_iff_le_normalizer h14).mp h15)
  have hCL : C ⊓ L = N := by
    refine le_antisymm (fun x hx => ?_) (le_inf hNC hNL)
    have hsub : ((C ⊓ L).subgroupOf L) ≤ CFSG.solvableRadical L := by
      refine hRadmax _ inferInstance ?_
      let f : ((C ⊓ L).subgroupOf L) →* C :=
        { toFun := fun y => ⟨((y : L) : B), (mem_inf.mp (mem_subgroupOf.mp y.2)).1⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      refine Group.isSolvable_of_isSolvable_injective (f := f) fun y z h => ?_
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    rw [hN]
    exact ⟨⟨x, (mem_inf.mp hx).2⟩, hsub (mem_subgroupOf.mpr hx), rfl⟩
  have hRL : R ⊓ L = R ⊓ N := le_antisymm (le_inf inf_le_left (hCL ▸ inf_le_inf_right L hRC))
    (inf_le_inf_left R hNL)
  have hSylRC : CFSG.ABGLocalTools.IsSylowOf 2 R C := h1 ▸ ⟨S, hS⟩
  have hSylN : CFSG.ABGLocalTools.IsSylowOf 2 (R ⊓ N) N :=
    hSylRC.inf_of_le_normalizer hNC (by rw [normalizer_eq_top_iff.mpr hNn]; exact le_top)
  have hKL : K ≤ L := hK ▸ (map_subtype_le _).trans (hA ▸ inf_le_left)
  obtain ⟨hSQTb, hO2b, hLCb, hqb, hRadb⟩ := bar_setting L hSQT hLC hq
  rw [← hN] at hRadb
  have hSylb := isSylowOf_map' hSylN (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))
  rw [← hRL] at hSylb
  have hKbperf : ⁅K.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)),
      K.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))⁆ =
      K.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)) := by
    rw [← map_commutator, h12]
  have hKRL : K ≤ normalizer ((R ⊓ L : Subgroup B) : Set B) := fun k hk =>
    mem_normalizer_inf (h14 hk) (by rw [normalizer_eq_top_iff.mpr inferInstance]; exact mem_top k)
  have hKbS : K.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)) ≤
      normalizer (((R ⊓ L).map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)) :
        Subgroup (B ⧸ (CFSG.pCore 2 L).map L.subtype)) :
          Set (B ⧸ (CFSG.pCore 2 L).map L.subtype)) :=
    (map_mono hKRL).trans (le_normalizer_map _)
  have hNK : N.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)) ⊔
      K.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)) =
      L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)) := by
    rw [← Subgroup.map_sup, ← h10]
  obtain ⟨hS2, hKbq, hLFK, hFK, hZ, hO, hKbN, ⟨s, hsF, hs5, ⟨eS⟩⟩⟩ :=
    bar_residual_facts hSQTb hO2b hLCb hqb hRadb (map_mono hKL) (map_mono hNL) hSylb hKbperf hKbS
      hNK
  have hSb2 : IsPGroup 2 ((R ⊓ L).map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))) :=
    (T.isPGroup'.to_le (inf_le_left.trans hRT)).map _
  obtain ⟨hKNO, hKQO, hO2map⟩ := residual_two_core
    (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)) (QuotientGroup.ker_mk' _) hQN hQ2 hO
    hKbN hSb2
  have hO2KT : (CFSG.pCore 2 K).map K.subtype ≤ (T : Subgroup B) := by
    refine le_of_isSylowOf_of_normalizes ((CFSG.pCore_isPGroup).map _)
      ((map_subtype_le _).trans le_sup_left) (sup_le (fun k hk => ?_) (fun t ht => ?_))
      ((isSylowOf_top T).of_le le_sup_right le_top)
    · exact mem_normalizer_map_of_characteristic (CFSG.pCore 2 K) (le_normalizer hk)
    · exact mem_normalizer_map_of_characteristic (CFSG.pCore 2 K) (hTK ht)
  have hKNR : K ⊓ N ≤ R := by
    rw [hKNO, hR]
    exact le_inf hO2KT ((hKNO ▸ inf_le_right : (CFSG.pCore 2 K).map K.subtype ≤ N).trans hNC)
  have hiso : ∃ e : K ⧸ CFSG.pCore 2 K ≃* L ⧸ CFSG.solvableRadical L,
      ∀ (k : K) (hk : (k : B) ∈ L), e (QuotientGroup.mk k) = QuotientGroup.mk (⟨k, hk⟩ : L) := by
    let ψ : K →* L ⧸ CFSG.solvableRadical L :=
      (QuotientGroup.mk' (CFSG.solvableRadical L)).comp (inclusion hKL)
    have hψs : Function.Surjective ψ := by
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
      have hy : (y : B) ∈ ((N ⊔ K : Subgroup B) : Set B) := by
        rw [← h10]
        exact y.2
      rw [coe_mul_of_right_le_normalizer_left _ _ (by
        rw [normalizer_eq_top_iff.mpr hNn]; exact le_top), Set.mem_mul] at hy
      obtain ⟨n, hn, k, hk, hnk⟩ := hy
      refine ⟨⟨k, hk⟩, ?_⟩
      change QuotientGroup.mk' _ (inclusion hKL ⟨k, hk⟩) = QuotientGroup.mk' _ y
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have hmem : (((inclusion hKL ⟨k, hk⟩)⁻¹ * y : L) : B) ∈ N := by
        change (k : B)⁻¹ * y ∈ N
        rw [← hnk, show k⁻¹ * (n * k) = k⁻¹ * n * k⁻¹⁻¹ by group]
        exact hNn.conj_mem n hn k⁻¹
      rw [hN] at hmem
      exact (mem_map_iff_mem L.subtype_injective).mp hmem
    have hker : ψ.ker = CFSG.pCore 2 K := by
      ext k
      rw [MonoidHom.mem_ker]
      change QuotientGroup.mk' _ (inclusion hKL k) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        ← mem_map_iff_mem L.subtype_injective, ← hN]
      change (k : B) ∈ N ↔ k ∈ CFSG.pCore 2 K
      rw [← mem_map_iff_mem K.subtype_injective (x := k), ← hKNO]
      exact ⟨fun h => mem_inf.mpr ⟨k.2, h⟩, fun h => (mem_inf.mp h).2⟩
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs), fun k hk => rfl⟩
  have hLs : Nonempty (L ⧸ CFSG.solvableRadical L ≃* projectiveSL 2 (ZMod s)) :=
    ⟨(CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.solQuotEquiv
      (barRestrict_surjective L) (isSolvable_barRestrict_ker L)).trans eS⟩
  have hKcore : K = CFSG.Quasithin.perfectCore (L ⊓ normalizer (R : Set B)) := by
    rw [hK, hA, CFSG.Quasithin.perfectCore_eq_map_perfectResidual]
  have hRc : ∀ r ∈ R, ∀ l ∈ L, l * r * l⁻¹ * r⁻¹ ∈ N := by
    intro r hr l hl
    have h := (hC r).mp (hRC hr) l⁻¹ (inv_mem hl)
    rwa [inv_inv, ← mul_assoc, ← mul_assoc] at h
  have hTNR' : (T : Subgroup B) ⊓ N ≤ R := by
    rw [hR]
    exact inf_le_inf_left _ hNC
  refine ⟨hQR, h11, h12, hTK, h10, h18, h19, h20, hS2, hKbq, hLFK, hFK, hZ, hO, hKNO, ?_, ?_,
    hiso, ⟨s, hsF, hs5, hLs⟩, fun L₁ hL₁L hTL₁ hLNL₁ => ?_⟩
  · exact (inf_le_inf_left K hQN).trans hKNO.le
  · refine nonempty_quotient_mulEquiv (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))
      hO2map _ ?_
    rw [subgroupOf_map_subtype, QuotientGroup.ker_mk', inf_comm]
  · obtain ⟨e1, e2, e3, e4⟩ := supplement_residual_eq T hRT hTNR' hRc hKcore h10 h12 hKNR hL₁L
      hTL₁ hLNL₁
    refine ⟨e1, e4, ?_, e3⟩
    rw [← CFSG.Quasithin.perfectCore_eq_map_perfectResidual]
    exact e2

end CFSG.Quasithin.H13.NQBlock
