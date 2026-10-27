module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26Interfaces
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatOutput
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.F53Push
open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_top_eq (H : Type) [Group H] :
    pCoreOf 2 (⊤ : Subgroup H) = CFSG.Open.pCore 2 H := by
  have := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H)
  unfold pCoreOf
  rw [← this]
  rfl

omit [Finite G] in
theorem mem_pCoreOf_iff {X : Subgroup G} (x : ↥X) :
    (x : G) ∈ pCoreOf 2 X ↔ x ∈ CFSG.Open.pCore 2 ↥X := CFSG.mem_openPCoreOf_iff_open x

omit [Finite G] in
theorem charTwo_top_of_pushHyp {X P Z : Subgroup G} (h : PushHyp X P Z) :
    CharTwo (⊤ : Subgroup ↥X) := by
  rw [CharTwo, pCoreOf_top_eq]
  rintro y ⟨-, hy⟩
  have hZX : Z ≤ X := h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  have : (y : G) ∈ pCoreOf 2 X := by
    refine h.mem_core_of_centralizes y.2 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : (⟨z, hZX hz⟩ : ↥X) ∈ CFSG.Open.pCore 2 ↥X := (mem_pCoreOf_iff _).mp (h.le_core hz)
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy _ hz')
  exact (mem_pCoreOf_iff y).mp this

omit [Finite G] in
theorem noCharNormal_subgroupOf {X P : Subgroup G} (hPX : P ≤ X) (hnc : NoCharNormal P X) :
    NoCharNormal (P.subgroupOf X) (⊤ : Subgroup ↥X) := by
  intro C hCR hC0 hCchar hN
  set C' : Subgroup G := C.map X.subtype with hC'
  have hC'P : C' ≤ P := by
    rintro _ ⟨c, hc, rfl⟩
    exact hCR hc
  have hC'0 : C' ≠ ⊥ := fun hb =>
    hC0 ((Subgroup.map_eq_bot_iff_of_injective C X.subtype_injective).mp hb)
  let e : ↥(P.subgroupOf X) ≃* ↥P := Subgroup.subgroupOfEquivOfLe hPX
  have hkey : ∀ y : ↥P, (y : G) ∈ C' ↔ e.symm y ∈ C.subgroupOf (P.subgroupOf X) := by
    intro y
    rw [Subgroup.mem_subgroupOf, hC']
    constructor
    · rintro ⟨c, hc, hcy⟩
      have : c = ((e.symm y : ↥(P.subgroupOf X)) : ↥X) := Subtype.ext hcy
      rwa [this] at hc
    · intro hy
      exact ⟨_, hy, rfl⟩
  have hchar : (C'.subgroupOf P).Characteristic := by
    refine ⟨fun φ => ?_⟩
    ext y
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show ((φ y : ↥P) : G) ∈ C' ↔ (y : G) ∈ C'
    rw [hkey, hkey]
    have h1 := hCchar.fixed (e.trans (φ.trans e.symm))
    have h2 : e.symm (φ y) = (e.trans (φ.trans e.symm)) (e.symm y) := by simp
    rw [h2]
    have h3 := congrArg (fun K => (e.symm y) ∈ K) h1
    simpa using h3
  refine hnc C' hC'P hC'0 hchar ?_
  intro x hx
  have hx' := hN (Subgroup.mem_top (⟨x, hx⟩ : ↥X))
  rw [Subgroup.mem_normalizer_iff] at hx' ⊢
  intro y
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, (hx' c).mp hc, rfl⟩
  · rintro ⟨c, hc, hcy⟩
    have hyX : y ∈ X := by
      have : y = x⁻¹ * (c : G) * x := by
        have h1 : (c : G) = x * y * x⁻¹ := hcy
        rw [h1]; group
      rw [this]
      exact X.mul_mem (X.mul_mem (X.inv_mem hx) c.2) hx
    refine ⟨⟨y, hyX⟩, (hx' ⟨y, hyX⟩).mpr ?_, rfl⟩
    have : (⟨x, hx⟩ : ↥X) * ⟨y, hyX⟩ * ⟨x, hx⟩⁻¹ = c := Subtype.ext (by simpa using hcy.symm)
    rw [this]
    exact hc

theorem elemThompsonIn_subgroupOf_map {X P : Subgroup G} (hPX : P ≤ X) :
    (elemThompsonIn 2 (P.subgroupOf X)).map X.subtype = thompsonJ P := by
  rw [← elemThompsonIn_map_of_injective 2 X.subtype X.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hPX]
  exact elemThompson_map_subtype_eq_thompsonJ P

theorem commutator_J_ne_bot {X P Z : Subgroup G} (h : PushHyp X P Z) (hP : P ≠ ⊥)
    (hnc : NoCharNormal P X) :
    ⁅elemThompsonIn 2 (P.subgroupOf X), Z.subgroupOf X⁆ ≠ ⊥ := by
  intro hbot
  have hPX : P ≤ X := h.sylow.1
  refine not_le_core_of_noCharNormal h hP hnc ?_
  rw [← elemThompsonIn_subgroupOf_map hPX]
  rintro _ ⟨j, hj, rfl⟩
  refine h.mem_core_of_centralizes j.2 ?_
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzX : z ∈ X := h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X) hz
  have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hj
  have := Subgroup.mem_centralizer_iff.mp hc ⟨z, hzX⟩ (Subgroup.mem_subgroupOf.mpr hz)
  exact congrArg Subtype.val this

omit [Finite G] in
theorem mem_oddOrderSubgroup_top_of_mem_oTwoUpper {X : Subgroup G} {n : G} (hn : n ∈ oTwoUpper X) :
    ∃ hnX : n ∈ X, (⟨n, hnX⟩ : ↥X) ∈ CFSG.QuasithinUnique.Setup.oddOrderSubgroup (⊤ : Subgroup ↥X) := by
  unfold oTwoUpper at hn
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    refine ⟨hx.1, Subgroup.subset_closure ⟨Subgroup.mem_top _, ?_⟩⟩
    rw [Subgroup.orderOf_mk]
    exact hx.2
  | one => exact ⟨X.one_mem, Subgroup.one_mem _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨hxX, hx⟩ := hx
    obtain ⟨hyX, hy⟩ := hy
    exact ⟨X.mul_mem hxX hyX, Subgroup.mul_mem _ hx hy⟩
  | inv x _ hx =>
    obtain ⟨hxX, hx⟩ := hx
    exact ⟨X.inv_mem hxX, Subgroup.inv_mem _ hx⟩


open CFSG.QuasithinUnique.Setup in
theorem commutator_mem_of_natQuotSetting {H : Type} [Group H] [Finite H] {k : Type}
    [Field k] [Finite k] [CharP k 2] {R M V : Subgroup H} {ρ : H →* Gamma k}
    {φ : ↥V →* Multiplicative (Fin 2 → k)} (hs : IsNatQuotSetting R M V ρ φ)
    (hchar : CharTwo (⊤ : Subgroup H)) (hnc : NoCharNormal R ⊤)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) {q : H} (hq : q ∈ CFSG.Open.pCore 2 H)
    (hqL : q ∈ oddOrderSubgroup (⊤ : Subgroup H)) {u : H} (hu : Odd (orderOf u)) :
    ⁅q, u⁆ ∈ V := by
  obtain ⟨-, -, -, h4, -, h6, -⟩ := hs.actual_Campbell_natural_minimal_parabolic_output hchar hnc hJ
  set G' := baumannOvergroup R with hG'
  have hLG : oddOrderSubgroup (⊤ : Subgroup H) ≤ G' := le_sup_left
  have huL : u ∈ oddOrderSubgroup (⊤ : Subgroup H) :=
    Subgroup.subset_closure ⟨Subgroup.mem_top _, hu⟩
  have hu' : (⟨u, hLG huL⟩ : ↥G') ∈ Kodd ↥G' := by
    refine mem_pPrimeGen_of_coprime (Subgroup.mem_top _) ?_
    rw [Subgroup.orderOf_mk]
    exact Nat.coprime_two_right.mpr hu
  have hNn : (CFSG.Open.pCore 2 H ⊓ oddOrderSubgroup (⊤ : Subgroup H)).Normal := by
    have := hs.normal_L
    have : (CFSG.Open.pCore 2 H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    infer_instance
  have hq' : (⟨q, hLG hqL⟩ : ↥G') ∈ CFSG.pCore 2 ↥G' := by
    refine CFSG.LieType.BorelTits.le_pCore 2 (N := (CFSG.Open.pCore 2 H ⊓
      oddOrderSubgroup (⊤ : Subgroup H)).subgroupOf G') ?_ ?_ (Subgroup.mem_subgroupOf.mpr ⟨hq, hqL⟩)
    · have := hNn
      infer_instance
    · intro g
      obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCore_isPGroup (G := H) 2
        ⟨(g : H), (Subgroup.mem_subgroupOf.mp g.2).1⟩
      exact ⟨m, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hm))⟩
  have hmem := Subgroup.commutator_mem_commutator hq' hu'
  rw [h6, h4] at hmem
  have := hs.normal_V
  have hle : ⁅V.subgroupOf G', Kodd ↥G'⁆ ≤ V.subgroupOf G' := Subgroup.commutator_le_left _ _
  have := Subgroup.mem_subgroupOf.mp (hle hmem)
  simpa [commutatorElement_def] using this


theorem baumannC_of_natQuotSetting {X P Z : Subgroup G} (h : PushHyp X P Z)
    (hnc : NoCharNormal P X) {k : Type} [Field k] [Finite k] [CharP k 2]
    {M : Subgroup ↥X} {ρ : ↥X →* Gamma k}
    {φ : ↥(Z.subgroupOf X) →* Multiplicative (Fin 2 → k)}
    (hs : IsNatQuotSetting (P.subgroupOf X) M (Z.subgroupOf X) ρ φ) : BaumannC X Z := by
  have hPX : P ≤ X := h.sylow.1
  have hP : P ≠ ⊥ := by
    rintro rfl
    apply hs.nonnormal
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  have hkey : ∀ q ∈ pCoreOf 2 X ⊓ oTwoUpper X, ∀ u ∈ X, Odd (orderOf u) → ⁅q, u⁆ ∈ Z := by
    intro q hq u huX hu
    obtain ⟨hqX, hqL⟩ := mem_oddOrderSubgroup_top_of_mem_oTwoUpper hq.2
    have hqc : (⟨q, hqX⟩ : ↥X) ∈ CFSG.Open.pCore 2 ↥X := (mem_pCoreOf_iff _).mp hq.1
    have := commutator_mem_of_natQuotSetting hs (charTwo_top_of_pushHyp h)
      (noCharNormal_subgroupOf hPX hnc) (commutator_J_ne_bot h hP hnc) hqc hqL
      (u := ⟨u, huX⟩) (by rwa [Subgroup.orderOf_mk])
    have h2 := Subgroup.mem_subgroupOf.mp this
    simpa [commutatorElement_def] using h2
  have hZX : Z ≤ X := h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  have hZn : ∀ x ∈ X, ∀ z ∈ Z, x * z * x⁻¹ ∈ Z := fun x hx z hz =>
    (Subgroup.mem_normalizer_iff.mp (h.normal hx) z).mp hz
  have hQX : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hLX : X ≤ Subgroup.normalizer (oTwoUpper X : Set G) := by
    rw [oTwoUpper_eq_pResidualOf]
    exact le_normalizer_pResidualOf X
  have hQn : ∀ x ∈ X, ∀ q ∈ pCoreOf 2 X, x * q * x⁻¹ ∈ pCoreOf 2 X := fun x hx q hq =>
    (Subgroup.mem_normalizer_iff.mp (hQX hx) q).mp hq
  have hLn : ∀ x ∈ X, ∀ l ∈ oTwoUpper X, x * l * x⁻¹ ∈ oTwoUpper X := fun x hx l hl =>
    (Subgroup.mem_normalizer_iff.mp (hLX hx) l).mp hl
  have hZnorm : Z ≤ Subgroup.normalizer ((pCoreOf 2 X ⊓ oTwoUpper X : Subgroup G) : Set G) := by
    intro z hz
    have hzX := hZX hz
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨hQn z hzX y hy1, hLn z hzX y hy2⟩
    · rintro ⟨hy1, hy2⟩
      have a1 := hQn z⁻¹ (X.inv_mem hzX) _ hy1
      have a2 := hLn z⁻¹ (X.inv_mem hzX) _ hy2
      simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at a1 a2
      constructor
      · simpa [mul_assoc] using a1
      · simpa [mul_assoc] using a2
  have hodd : ∀ x ∈ X, Odd (orderOf x) → ∀ q ∈ pCoreOf 2 X, ⁅q, x⁆ ∈ Z := by
    intro x hxX hx q hq
    have hxL : x ∈ oTwoUpper X := Subgroup.subset_closure ⟨hxX, hx⟩
    have hUQ : (pCoreOf 2 X ⊓ oTwoUpper X) ⊔ Z ≤ pCoreOf 2 X := sup_le inf_le_left h.le_core
    have hcop : Nat.Coprime (orderOf x) (Nat.card ↥((pCoreOf 2 X ⊓ oTwoUpper X) ⊔ Z)) := by
      have h2 : IsPGroup 2 ↥((pCoreOf 2 X ⊓ oTwoUpper X) ⊔ Z) :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le hUQ
      obtain ⟨m, hm⟩ := h2.exists_card_eq
      rw [hm]
      exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hx)
    have hxU : ∀ u ∈ (pCoreOf 2 X ⊓ oTwoUpper X) ⊔ Z, x * u * x⁻¹ * u⁻¹ ∈ Z := by
      intro u hu
      obtain ⟨n, hn, z, hz, rfl⟩ := mem_sup_of_le_normalizer hZnorm hu
      have hnX : n ∈ X := (CFSG.LieType.BorelTits.pCoreOf_le 2 X) hn.1
      have h1 : x * n * x⁻¹ * n⁻¹ ∈ Z := by
        have e : x * n * x⁻¹ * n⁻¹ = ⁅n, x⁆⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Z.inv_mem (hkey n hn x hxX hx)
      have h2 : x * z * x⁻¹ * z⁻¹ ∈ Z := Z.mul_mem (hZn x hxX z hz) (Z.inv_mem hz)
      have h3 := hZn n hnX _ h2
      have : x * (n * z) * x⁻¹ * (n * z)⁻¹ = (x * n * x⁻¹ * n⁻¹) * (n * (x * z * x⁻¹ * z⁻¹) * n⁻¹) := by
        group
      rw [this]
      exact Z.mul_mem h1 h3
    have hxQ' : ∀ q ∈ pCoreOf 2 X, x * q * x⁻¹ * q⁻¹ ∈ (pCoreOf 2 X ⊓ oTwoUpper X) ⊔ Z := by
      intro q hq
      refine Subgroup.mem_sup_left ⟨?_, ?_⟩
      · exact (pCoreOf 2 X).mul_mem (hQn x hxX q hq) ((pCoreOf 2 X).inv_mem hq)
      · have hqX := (CFSG.LieType.BorelTits.pCoreOf_le 2 X) hq
        have := hLn q hqX x⁻¹ ((oTwoUpper X).inv_mem hxL)
        have h5 := (oTwoUpper X).mul_mem hxL this
        simpa [mul_assoc] using h5
    have hWQ : ∀ q ∈ pCoreOf 2 X, ∀ w ∈ Z, q * w * q⁻¹ ∈ Z := fun q hq w hw =>
      hZn q ((CFSG.LieType.BorelTits.pCoreOf_le 2 X) hq) w hw
    have := coprime_conj_mem (Q := pCoreOf 2 X) (U := (pCoreOf 2 X ⊓ oTwoUpper X) ⊔ Z) (W := Z)
      (x := x) hUQ le_sup_right hWQ hxU hxQ' hcop q hq
    have h6 : ⁅q, x⁆ = (x * q * x⁻¹ * q⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h6]
    exact Z.inv_mem this
  rw [BaumannC, Subgroup.commutator_le]
  intro q hq l hl
  rw [← oTwoUpper_eq_pResidualOf] at hl
  suffices hsuff : l ∈ X ∧ ⁅q, l⁆ ∈ Z from hsuff.2
  unfold oTwoUpper at hl
  induction hl using Subgroup.closure_induction with
  | mem x hx => exact ⟨hx.1, hodd x hx.1 hx.2 q hq⟩
  | one => exact ⟨X.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨hxX, hx⟩ := hx
    obtain ⟨hyX, hy⟩ := hy
    refine ⟨X.mul_mem hxX hyX, ?_⟩
    have : ⁅q, x * y⁆ = ⁅q, x⁆ * (x * ⁅q, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact Z.mul_mem hx (hZn x hxX _ hy)
  | inv x _ hx =>
    obtain ⟨hxX, hx⟩ := hx
    refine ⟨X.inv_mem hxX, ?_⟩
    have : ⁅q, x⁻¹⁆ = x⁻¹ * ⁅q, x⁆⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [this]
    have := hZn x⁻¹ (X.inv_mem hxX) _ (Z.inv_mem hx)
    simpa [mul_assoc] using this

end CFSG.Quasithin.F53Push
