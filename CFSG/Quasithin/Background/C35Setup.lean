module

public import CFSG.Quasithin.Background.C31BasicPf
public import CFSG.Quasithin.Background.C35Insp
public import CFSG.Quasithin.Background.C48Asm

public section

namespace CFSG.Quasithin.C35

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

omit [Finite G] in
theorem conj_mem_centerOf {g z : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hz : z ∈ centerOf K) : g * z * g⁻¹ ∈ centerOf K := by
  obtain ⟨hzK, hzC⟩ := hz
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzK, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro k hk
  have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) k).mp hk
  have hc := Subgroup.mem_centralizer_iff.mp hzC _ hk'
  calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g⁻¹⁻¹) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * k * g⁻¹⁻¹)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * k := by group

omit [Finite G] in
theorem normalizer_le_normalizer_centerOf (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (centerOf K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨conj_mem_centerOf hg, fun hz => ?_⟩
  have := conj_mem_centerOf (Subgroup.inv_mem _ hg) hz
  simpa [mul_assoc] using this

theorem pCoreOf_eq_centerOf (hK : CFSG.Open.IsComponentOf K H) (hZ : IsPGroup 2 ↥(centerOf K)) :
    pCoreOf 2 K = centerOf K := by
  refine le_antisymm
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K) (C31B.pCoreOf_le_centralizer hK)) ?_
  exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (centerOf K) K inf_le_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_centerOf K))) hZ

theorem centerOf_le_inf (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (hHN : H ≤ Subgroup.normalizer (K : Set G)) (hZ : IsPGroup 2 ↥(centerOf K)) :
    centerOf K ≤ R ⊓ K := by
  refine le_inf ?_ inf_le_left
  refine le_trans ?_ (c2_1_pCore_le (c2_9_two h).2)
  exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (centerOf K) H
    (inf_le_left.trans hK.1)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans hK.1)).mpr
      (hHN.trans (normalizer_le_normalizer_centerOf K))) hZ

theorem V_le_R (h : HypC28 H R M L V) : V ≤ R := by
  refine le_trans ?_ (C48.pCoreOf_conjClosure_le h)
  refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 V _ h.V_le
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h.V_le).mpr
      (C48Spor.M0_le_normalizer_V h)) ?_
  intro x
  exact ⟨1, Subtype.ext (by simpa using h.V_elem.2 x x.2)⟩

theorem V_le_centerOf (h : HypC28 H R M L V) (hb : C31Basic H R M L V K) :
    V ≤ centerOf (R ⊓ K) := by
  refine le_inf (le_inf (V_le_R h) (h.V_le.trans hb.1)) ?_
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (C48.le_centralizer_V h hx.1) v hv).symm

theorem le_Y (h : HypC28 H R M L V) (hb : C31Basic H R M L V K) :
    conjClosure L M ≤ K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) :=
  le_inf hb.1 fun _ hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨(c2_9_two h).1 hx, Subgroup.le_normalizer (hb.1 hx)⟩

omit [Finite G] in
theorem normalizer_le_normalizer_normalizer (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx) (Subgroup.inv_mem _ hg)
  · intro hx
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hx) hg
    simpa [mul_assoc] using this

theorem R_le_normalizer_Y (h : HypC28 H R M L V) (hb : C31Basic H R M L V K) :
    R ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  intro r hr
  have hrK : r ∈ Subgroup.normalizer (K : Set G) := hb.2.1 (h.le_M hr)
  have hrRK : r ∈ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hr, hrK⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hrK, normalizer_le_normalizer_normalizer _ hrRK⟩

theorem pCoreOf_Y (h22 : ASC22Two G) (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H) :
    pCoreOf 2 (K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G)) = R ⊓ K :=
  (h22 H R K h.sqtk (c2_9_two h).2 (F918V3S3.mem_cComp_of_isComponentOf hK)).2.1.symm

theorem Y_ne (h22 : ASC22Two G) (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (hb : C31Basic H R M L V K) :
    K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) ≠ K := by
  intro hY
  have hRK : R ⊓ K = pCoreOf 2 K := by rw [← pCoreOf_Y h22 h hK, hY]
  have hVZ : V ≤ Subgroup.centralizer (K : Set G) :=
    (le_inf (V_le_R h) (h.V_le.trans hb.1)).trans
      (hRK.le.trans (C31B.pCoreOf_le_centralizer hK))
  apply h.V_ne
  rw [← h.V_comm, eq_bot_iff, Subgroup.commutator_le]
  intro v hv m hm
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.mp (hVZ hv) m (hb.1 hm)).symm

omit [Finite G] in
theorem isParabolic2_of_map {P : Subgroup G} (hPK : P ≤ K) (hO : pCoreOf 2 K ≤ P)
    (hpar : IsParabolic2 (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))
      ((P.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))) :
    IsParabolic2 K P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hρdef
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 ↥ρ.ker := by
    rw [hρdef, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hkP : ρ.ker ≤ P.subgroupOf K := by
    rw [hρdef, QuotientGroup.ker_mk']
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hO ⟨x, hx, rfl⟩)
  obtain ⟨-, U, hU, hNU⟩ := hpar
  have hS : IsSylowTwoOf (U.comap ρ) ⊤ := by
    refine ⟨le_top, hU.2.1.comap_of_ker_isPGroup ρ hk, ?_⟩
    have h1 : ((U.comap ρ).subgroupOf ⊤).index = (U.comap ρ).index :=
      Subgroup.relIndex_top_right _
    rw [h1, Subgroup.index_comap_of_surjective _ hρ]
    have h2 := hU.2.2
    rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at h2
  have hkS : ρ.ker ≤ U.comap ρ := Subgroup.ker_le_comap ρ U
  have hmapU : (U.comap ρ).map ρ = U := Subgroup.map_comap_eq_self_of_surjective hρ U
  have htop : IsParabolic2 (⊤ : Subgroup ↥K) (P.subgroupOf K) := by
    refine ⟨le_top, U.comap ρ, hS, fun x hx => ?_⟩
    have h1 : ρ x ∈ Subgroup.normalizer (((U.comap ρ).map ρ : Subgroup _) : Set _) := by
      rw [Subgroup.mem_normalizer_iff]
      intro m
      obtain ⟨g, rfl⟩ := hρ m
      have hmem : ∀ g : ↥K, g ∈ U.comap ρ ↔ ρ g ∈ (U.comap ρ).map ρ := fun g => by
        rw [← Subgroup.mem_comap, Subgroup.comap_map_eq_self hkS]
      rw [← hmem g, ← map_inv, ← map_mul, ← map_mul, ← hmem (x * g * x⁻¹)]
      exact Subgroup.mem_normalizer_iff.mp hx.2 g
    rw [hmapU] at h1
    obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp (hNU ⟨Subgroup.mem_top _, h1⟩)
    have hker : p⁻¹ * x ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, inv_mul_cancel]
    have := (P.subgroupOf K).mul_mem hp (hkP hker)
    rwa [mul_inv_cancel_left] at this
  have := (A312.isParabolic2_top_iff K (P.subgroupOf K)).mp htop
  rwa [Subgroup.map_subgroupOf_eq_of_le hPK] at this

theorem evenLieType_or_alt_six {S : Type} [Group S]
    (ht : C31Lie2Types S) : CFSG.Blueprint.EvenLieType S ∨ IsAlt 6 S := by
  unfold C31Lie2Types at ht
  rcases ht with h5 | h6 | h8 | (⟨f, ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ |
      ⟨-, -, h⟩ | ⟨hf, hf3, h⟩⟩ | h) | ⟨n, -, h⟩
  · have h' := C126.isPSL_two_two_two_of_alternating_five S h5
    exact Or.inl ⟨.PSL, 2, 2, h'.1, Or.inl ⟨by decide, h'⟩⟩
  · exact Or.inr h6
  · have hm := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff S).2 h8
    exact Or.inl ⟨.PSL, 4, 1, ⟨Nat.prime_two, le_rfl, by decide⟩, hm⟩
  · exact Or.inl ⟨.PSL, 2, f, h.1, Or.inl ⟨by decide, h⟩⟩
  · exact Or.inl ⟨.PSL, 3, f, h.1, Or.inl ⟨by decide, h⟩⟩
  · exact Or.inl ⟨.PSU, 3, f, h.1, Or.inl ⟨by decide, h⟩⟩
  · exact Or.inl ⟨.PSp, 2, f, h.1, Or.inl ⟨by decide, h⟩⟩
  · exact Or.inl ⟨.G2, 0, f, h.1, Or.inr (Or.inl ⟨rfl, by decide, h⟩)⟩
  · exact Or.inl ⟨.trialityD4, 0, f, h.1, Or.inr (Or.inl ⟨rfl, by decide, h⟩)⟩
  · exact Or.inl ⟨.twistedF4, 0, f, h.1, Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩))⟩
  · exact Or.inl ⟨.twistedB2, 0, f, ⟨Nat.prime_two, by omega, rfl, rfl, hf, hf3⟩,
      Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩))⟩
  · exact Or.inl ⟨.Tits, 0, 1, h.1, Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩))⟩
  · exact Or.inl ⟨.PSL, n, 1, h.1, Or.inl ⟨by decide, h⟩⟩

omit [Finite G] in
theorem map_center_eq_centerOf (K : Subgroup G) :
    (Subgroup.center ↥K).map K.subtype = centerOf K := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  · rintro ⟨hxK, hx⟩
    refine ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hx y y.2

theorem pCore_eq_center (hK : CFSG.Open.IsComponentOf K H) (hZ : IsPGroup 2 ↥(centerOf K)) :
    CFSG.pCore 2 ↥K = Subgroup.center ↥K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [map_center_eq_centerOf]
  exact pCoreOf_eq_centerOf hK hZ

theorem asc22FourHyp_of (hK : CFSG.Open.IsComponentOf K H)
    (hZ : IsPGroup 2 ↥(centerOf K)) (ht : C31Lie2Types (↥K ⧸ Subgroup.center ↥K)) :
    CFSG.Blueprint.EvenLieType
        ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ∨
      IsAlt 6 ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ∨
      IsPSU 3 3 1 ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  have hq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  let e₁ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.quotientMulEquivOfEq (pCore_eq_center hK hZ)
  have hZ' : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ :=
    CFSG.LieType.CurtisTits.center_quotient_center_eq_bot_of_isQuasisimple hq
  have hZ1 : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e₁ z ∈ Subgroup.center (↥K ⧸ Subgroup.center ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e₁.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [hZ', Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.mpr (e₁.injective (hz'.trans e₁.map_one.symm))
  let e : (↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
      ↥K ⧸ Subgroup.center ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ1).trans (QuotientGroup.quotientBot.trans e₁)
  rcases evenLieType_or_alt_six ht with ⟨t, n, f, hadm, hm⟩ | h6
  · exact Or.inl ⟨t, n, f, hadm, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm⟩
  · obtain ⟨e6⟩ := h6
    exact Or.inr (Or.inl ⟨e.trans e6⟩)

theorem isParabolic2_Y (h22 : ASC22Four G) (h : HypC28 H R M L V)
    (hK : CFSG.Open.IsComponentOf K H) (hHN : H ≤ Subgroup.normalizer (K : Set G))
    (hb : C31Basic H R M L V K) (ht : C31Lie2Types (↥K ⧸ Subgroup.center ↥K)) :
    IsParabolic2 K (K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G)) := by
  refine isParabolic2_of_map inf_le_left ?_ (h22 H R K h.sqtk (c2_9_two h).2
    (F918V3S3.mem_cComp_of_isComponentOf hK) (asc22FourHyp_of hK hb.2.2 ht))
  rw [pCoreOf_eq_centerOf hK hb.2.2]
  exact (centerOf_le_inf h hK hHN hb.2.2).trans (le_inf inf_le_right Subgroup.le_normalizer)

theorem isSylowTwoOf_Y (h22 : ASC22Two G) (h : HypC28 H R M L V)
    (hK : CFSG.Open.IsComponentOf K H) (hHN : H ≤ Subgroup.normalizer (K : Set G)) :
    IsSylowTwoOf (pCoreOf 2 (K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G)))
      (centralizerSection K (conjClosure L M) (pCoreOf 2 (conjClosure L M))) := by
  rw [pCoreOf_Y h22 h hK]
  have hR := c2_10_three h
  have hCK : centralizerSection K (conjClosure L M) (pCoreOf 2 (conjClosure L M)) =
      centralizerSection H (conjClosure L M) (pCoreOf 2 (conjClosure L M)) ⊓ K := by
    ext x
    constructor
    · rintro ⟨hxK, h1, h2, h3⟩
      exact ⟨⟨hK.1 hxK, h1, h2, h3⟩, hxK⟩
    · rintro ⟨⟨-, h1, h2, h3⟩, hxK⟩
      exact ⟨hxK, h1, h2, h3⟩
  have hnorm : centralizerSection H (conjClosure L M) (pCoreOf 2 (conjClosure L M)) ≤
      Subgroup.normalizer ((centralizerSection H (conjClosure L M)
        (pCoreOf 2 (conjClosure L M)) ⊓ K : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hHN hx.1⟩
  have h1 := A4.isSylowTwoOf_inf_normal hR inf_le_left hnorm
  rw [hCK]
  rwa [← inf_assoc, inf_eq_left.mpr hR.1] at h1

theorem c35Data_of (h22two : ASC22Two G) (h22four : ASC22Four G)
    (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (hHN : H ≤ Subgroup.normalizer (K : Set G)) (hb : C31Basic H R M L V K)
    (ht : C31Lie2Types (↥K ⧸ Subgroup.center ↥K))
    (hM0 : conjClosure L M =
      perfectCore (K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G))) :
    C35Data K (K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G)) (conjClosure L M) V where
  quasisimple := hK.2.2
  center := hb.2.2
  parabolic := isParabolic2_Y h22four h hK hHN hb ht
  ne_top := Y_ne h22two h hK hb
  normalizer_eq := by rw [pCoreOf_Y h22two h hK]
  center_le := by
    rw [pCoreOf_Y h22two h hK]
    exact centerOf_le_inf h hK hHN hb.2.2
  eq_perfectCore := hM0
  ne_bot := fun h0 => h.V_ne (eq_bot_iff.mpr (h0 ▸ h.V_le))
  sylow := isSylowTwoOf_Y h22two h hK hHN
  V_le := h.V_le
  V_le_center := by
    rw [pCoreOf_Y h22two h hK]
    exact V_le_centerOf h hb
  V_elem := h.V_elem
  V_comm := h.V_comm
  V_ne := h.V_ne

end CFSG.Quasithin.C35
