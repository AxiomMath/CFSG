module

public import CFSG.LocalAnalysis.WeakClosure81.W172OrbitDefs
public import CFSG.LocalAnalysis.WeakClosure81.W172OrbitN
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qr
public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightTwoB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsSetting

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem w172_commutator_mul_eq_mul_commutator {V V₀ : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V) {u n n' : G} (hn : n ∈ V) (hn' : n' ∈ V)
    (hnt : ⁅n, u⁆ ∈ V₀) (hn't : ⁅n', u⁆ ∈ V₀) :
    ⁅n * n', u⁆ = ⁅n, u⁆ * ⁅n', u⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hcomm : n * ⁅n', u⁆ * n⁻¹ = ⁅n', u⁆ := by
    have h1 : n * ⁅n', u⁆ = ⁅n', u⁆ * n := hV.comm hn (hV₀ hn't)
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
  rw [hcomm]
  exact (hV.comm (hV₀ hnt) (hV₀ hn't)).symm

private theorem w172_commutator_mul_right_eq_mul_commutator {V₀ : Subgroup G} {u u' n : G}
    (hcent : ∀ w ∈ V₀, u * w * u⁻¹ = w) (hnt' : ⁅n, u'⁆ ∈ V₀) :
    ⁅n, u * u'⁆ = ⁅n, u⁆ * ⁅n, u'⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h := congrArg (fun z => ⁅n, u⁆ * z) (hcent _ hnt')
  simpa [mul_assoc] using h

private theorem w172s_span_range_eq_top {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    {ι : Type*} (f : ι → Module.Dual (ZMod 2) E) [FiniteDimensional (ZMod 2) E]
    (hf : ⨅ i, LinearMap.ker (f i) = ⊥) :
    Submodule.span (ZMod 2) (Set.range f) = ⊤ := by
  rw [eq_top_iff]
  intro K _
  refine FiniteDimensional.mem_span_of_iInf_ker_le_ker ?_
  rw [hf]; exact bot_le

private theorem w172s_smulRight_mem_span {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    {ι M₁ : Type*} [AddCommGroup M₁] [Module (ZMod 2) M₁]
    (f : ι → Module.Dual (ZMod 2) E) [FiniteDimensional (ZMod 2) E]
    (hf : ⨅ i, LinearMap.ker (f i) = ⊥) (z : M₁) (g : Module.Dual (ZMod 2) E) :
    g.smulRight z ∈ Submodule.span (ZMod 2) (Set.range fun i => (f i).smulRight z) := by
  have hg : g ∈ Submodule.span (ZMod 2) (Set.range f) := by
    rw [w172s_span_range_eq_top f hf]; exact Submodule.mem_top
  let T : Module.Dual (ZMod 2) E →ₗ[ZMod 2] (E →ₗ[ZMod 2] M₁) :=
    { toFun := fun f => f.smulRight z
      map_add' := fun a b => by ext x; simp [add_smul]
      map_smul' := fun c a => by
        ext x
        show (c • a) x • z = c • (a x • z)
        rw [LinearMap.smul_apply, smul_eq_mul, mul_smul] }
  have hmap : T g ∈ Submodule.map T (Submodule.span (ZMod 2) (Set.range f)) :=
    ⟨g, hg, rfl⟩
  rw [Submodule.map_span] at hmap
  have hset : T '' Set.range f = Set.range (fun i => (f i).smulRight z) := by
    ext m; constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨f i, ⟨i, rfl⟩, rfl⟩
  rw [hset] at hmap
  exact hmap

private theorem w172s_span_smulRight_eq_top {N M₁ : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    [AddCommGroup M₁] [Module (ZMod 2) M₁] [FiniteDimensional (ZMod 2) M₁]
    {ι : Type*} (f : ι → Module.Dual (ZMod 2) N)
    [FiniteDimensional (ZMod 2) N] (hf : ⨅ i, LinearMap.ker (f i) = ⊥) :
    Submodule.span (ZMod 2)
      {g : N →ₗ[ZMod 2] M₁ | ∃ i z, g = (f i).smulRight z} = ⊤ := by
  rw [eq_top_iff]
  intro φ _
  suffices H : ∀ r, ∀ φ : N →ₗ[ZMod 2] M₁,
      Module.finrank (ZMod 2) (LinearMap.range φ) = r →
      φ ∈ Submodule.span (ZMod 2) {g : N →ₗ[ZMod 2] M₁ | ∃ i z, g = (f i).smulRight z} by
    exact H _ φ rfl
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro φ hr
    by_cases hφ : φ = 0
    · rw [hφ]; exact Submodule.zero_mem _
    · have hrange : LinearMap.range φ ≠ ⊥ := by
        intro h
        exact hφ (LinearMap.range_eq_bot.mp h)
      obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hrange
      obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hz0
      set ψ : N →ₗ[ZMod 2] M₁ := φ - (lam.comp φ).smulRight z with hψ
      have hψrange : LinearMap.range ψ ≤ LinearMap.range φ ⊓ LinearMap.ker lam := by
        rintro _ ⟨x, rfl⟩
        refine ⟨?_, ?_⟩
        · simp only [hψ, LinearMap.sub_apply, LinearMap.smulRight_apply]
          exact Submodule.sub_mem _ ⟨x, rfl⟩ (Submodule.smul_mem _ _ hz)
        · show lam (ψ x) = 0
          rw [hψ, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.comp_apply, map_sub,
            map_smul, hlam, smul_eq_mul, mul_one]
          exact sub_self _
      have hproper : LinearMap.range φ ⊓ LinearMap.ker lam < LinearMap.range φ := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro heq
        have hz_in : z ∈ LinearMap.range φ ⊓ LinearMap.ker lam := by rw [heq]; exact hz
        have hz_ker : z ∈ LinearMap.ker lam := hz_in.2
        rw [LinearMap.mem_ker, hlam] at hz_ker
        exact one_ne_zero hz_ker
      have hfin : Module.finrank (ZMod 2) (LinearMap.range ψ) < r := by
        rw [← hr]
        exact lt_of_le_of_lt (Submodule.finrank_mono hψrange)
          (Submodule.finrank_lt_finrank_of_lt hproper)
      have hψspan : ψ ∈ Submodule.span (ZMod 2)
          {g : N →ₗ[ZMod 2] M₁ | ∃ i z, g = (f i).smulRight z} :=
        ih _ hfin ψ rfl
      have hf₀span : (lam.comp φ).smulRight z ∈ Submodule.span (ZMod 2)
          {g : N →ₗ[ZMod 2] M₁ | ∃ i z, g = (f i).smulRight z} := by
        refine Submodule.span_mono ?_ (w172s_smulRight_mem_span (E := N) f hf z (lam.comp φ))
        rintro _ ⟨i, rfl⟩
        exact ⟨i, z, rfl⟩
      have : φ = ψ + (lam.comp φ).smulRight z := by rw [hψ]; abel
      rw [this]
      exact Submodule.add_mem _ hψspan hf₀span

private theorem w172s_eq_top_of_smulRight_mem {N M₁ : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    [FiniteDimensional (ZMod 2) N] [AddCommGroup M₁] [Module (ZMod 2) M₁]
    [FiniteDimensional (ZMod 2) M₁] {ι : Type*} (f : ι → Module.Dual (ZMod 2) N)
    (hf : ⨅ i, LinearMap.ker (f i) = ⊥) (Φ : Submodule (ZMod 2) (N →ₗ[ZMod 2] M₁))
    (hΦ : ∀ (i : ι) (z : M₁), (f i).smulRight z ∈ Φ) : Φ = ⊤ := by
  rw [eq_top_iff, ← w172s_span_smulRight_eq_top (M₁ := M₁) f hf, Submodule.span_le]
  rintro _ ⟨i, z, rfl⟩
  exact hΦ i z

private abbrev w172s_E (V : Subgroup G) (hV : IsElemAbelian 2 V) := Additive (IntMod V hV)

private noncomputable instance w172s_instModuleE (V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Module (ZMod 2) (w172s_E V hV) :=
  AddCommGroup.zmodModule (by
    intro x
    apply Additive.toMul.injective
    show Additive.toMul (2 • x) = Additive.toMul 0
    rw [two_nsmul, toMul_add, toMul_zero, ← pow_two]
    exact IntMod.sq_eq_one (Additive.toMul x))

private def w172s_ev {V : Subgroup G} {hV : IsElemAbelian 2 V} (x : w172s_E V hV) : G :=
  (Additive.toMul x : IntMod V hV).val

private theorem w172s_ev_mem {V : Subgroup G} {hV : IsElemAbelian 2 V} (x : w172s_E V hV) :
    w172s_ev x ∈ V := IntMod.val_mem _

private theorem w172s_ev_add {V : Subgroup G} {hV : IsElemAbelian 2 V} (x y : w172s_E V hV) :
    w172s_ev (x + y) = w172s_ev x * w172s_ev y := rfl

private theorem w172s_ev_zero {V : Subgroup G} {hV : IsElemAbelian 2 V} :
    w172s_ev (0 : w172s_E V hV) = 1 := rfl

private theorem w172s_ev_injective {V : Subgroup G} {hV : IsElemAbelian 2 V} :
    Function.Injective (w172s_ev : w172s_E V hV → G) :=
  fun _ _ h => Additive.toMul.injective (IntMod.val_injective h)

private def w172s_ofG {V : Subgroup G} (hV : IsElemAbelian 2 V) (v : G) (hv : v ∈ V) :
    w172s_E V hV := Additive.ofMul (IntMod.mk hV ⟨v, hv⟩)

private theorem w172s_ev_ofG {V : Subgroup G} {hV : IsElemAbelian 2 V} {v : G} (hv : v ∈ V) :
    w172s_ev (w172s_ofG hV v hv) = v := rfl

private noncomputable def w172s_cLin {V : Subgroup G} (hV : IsElemAbelian 2 V) (g : G)
    (hg : g ∈ Subgroup.normalizer (V : Set G)) : w172s_E V hV →ₗ[ZMod 2] w172s_E V hV :=
  AddMonoidHom.toZModLinearMap 2
    (AddMonoidHom.mk'
      (fun x => w172s_ofG hV (g * w172s_ev x * g⁻¹)
        ((Subgroup.mem_normalizer_iff.1 hg _).1 (w172s_ev_mem x)))
      (fun x y => w172s_ev_injective (by
        simp only [w172s_ev_ofG, w172s_ev_add]
        group)))

private theorem w172s_ev_cLin {V : Subgroup G} {hV : IsElemAbelian 2 V} {g : G}
    {hg : g ∈ Subgroup.normalizer (V : Set G)} (x : w172s_E V hV) :
    w172s_ev (w172s_cLin hV g hg x) = g * w172s_ev x * g⁻¹ := rfl

open Classical in
private noncomputable def w172s_fW {V : Subgroup G} (hV : IsElemAbelian 2 V) (W : Subgroup G)
    (hW : W.relIndex V = 2) : Module.Dual (ZMod 2) (w172s_E V hV) where
  toFun x := if w172s_ev x ∈ W then 0 else 1
  map_add' x y := by
    have hxy : w172s_ev x * w172s_ev y ∈ W ↔ (w172s_ev x ∈ W ↔ w172s_ev y ∈ W) :=
      Subgroup.mul_mem_iff_of_index_two (H := W.subgroupOf V) hW
        (a := ⟨w172s_ev x, w172s_ev_mem x⟩) (b := ⟨w172s_ev y, w172s_ev_mem y⟩)
    show (if w172s_ev (x + y) ∈ W then (0 : ZMod 2) else 1) =
      (if w172s_ev x ∈ W then 0 else 1) + (if w172s_ev y ∈ W then 0 else 1)
    rw [w172s_ev_add]
    by_cases hx : w172s_ev x ∈ W <;> by_cases hy : w172s_ev y ∈ W
    · rw [if_pos (hxy.2 (iff_of_true hx hy)), if_pos hx, if_pos hy]; decide
    · rw [if_neg (fun h => hy ((hxy.1 h).1 hx)), if_pos hx, if_neg hy]; decide
    · rw [if_neg (fun h => hx ((hxy.1 h).2 hy)), if_neg hx, if_pos hy]; decide
    · rw [if_pos (hxy.2 (iff_of_false hx hy)), if_neg hx, if_neg hy]; decide
  map_smul' c x := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · show (if w172s_ev ((0 : ZMod 2) • x) ∈ W then (0 : ZMod 2) else 1) = 0 * _
      rw [zero_smul, w172s_ev_zero, if_pos W.one_mem, zero_mul]
    · show (if w172s_ev ((1 : ZMod 2) • x) ∈ W then (0 : ZMod 2) else 1) = 1 * _
      rw [one_smul, one_mul]

private theorem w172s_fW_of_mem {V : Subgroup G} {hV : IsElemAbelian 2 V} {W : Subgroup G}
    {hW : W.relIndex V = 2} {x : w172s_E V hV} (h : w172s_ev x ∈ W) :
    w172s_fW hV W hW x = 0 := if_pos h

private theorem w172s_fW_of_not_mem {V : Subgroup G} {hV : IsElemAbelian 2 V} {W : Subgroup G}
    {hW : W.relIndex V = 2} {x : w172s_E V hV} (h : w172s_ev x ∉ W) :
    w172s_fW hV W hW x = 1 := if_neg h

private theorem w172_comm_conj_eq (n b g : G) :
    ⁅n, g⁻¹ * b * g⁆ = g⁻¹ * ⁅g * n * g⁻¹, b⁆ * g := by
  simp only [commutatorElement_def]
  group

private theorem w172_mem_conj_P {D : Data G} {V₀ V : Subgroup G} {x : G}
    (h : Hyp64 1 D.M V₀ V x) :
    D.M ≤ Subgroup.normalizer
      ((F11.CTilde D.M V₀ V ⊓ Subgroup.centralizer (V₀ : Set G) : Subgroup G) : Set G) := by
  have hV : IsElemAbelian 2 V := h.elemAbelian
  have hMle : D.M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hMle₀ : D.M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  have hconj : ∀ m ∈ D.M,
      ∀ c ∈ F11.CTilde D.M V₀ V ⊓ Subgroup.centralizer (V₀ : Set G),
        m * c * m⁻¹ ∈ F11.CTilde D.M V₀ V ⊓ Subgroup.centralizer (V₀ : Set G) := by
    intro m hm c hc
    refine Subgroup.mem_inf.2 ⟨uc22p22q_ctilde_conj_mem hMle hMle₀ hm hc.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvm : m⁻¹ * v * m ∈ V₀ := by
      have h1 := (((Subgroup.mem_normalizer_iff.1 (hMle₀ (D.M.inv_mem hm))) v).1) hv
      simpa using h1
    have h2 : c * (m⁻¹ * v * m) = (m⁻¹ * v * m) * c :=
      ((Subgroup.mem_centralizer_iff.1 hc.2) _ hvm).symm
    calc v * (m * c * m⁻¹) = m * ((m⁻¹ * v * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * v * m)) * m⁻¹ := by rw [← h2]
      _ = (m * c * m⁻¹) * v := by group
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨hconj m hm c, fun hc => ?_⟩
  have h := hconj m⁻¹ (D.M.inv_mem hm) (m * c * m⁻¹) hc
  rwa [show m⁻¹ * (m * c * m⁻¹) * m⁻¹⁻¹ = c by group] at h

private theorem w172_mem_comm_P {D : Data G} {V₀ V : Subgroup G} {x : G}
    (h : Hyp64 1 D.M V₀ V x) {N : Subgroup G} (hNV : N ≤ V) {u : G}
    (hu : u ∈ F11.CTilde D.M V₀ V ⊓ Subgroup.centralizer (V₀ : Set G)) {n : G} (hn : n ∈ N) :
    ⁅n, u⁆ ∈ V₀ := by
  have hV : IsElemAbelian 2 V := h.elemAbelian
  have hMle : D.M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  obtain ⟨huCT, -⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨-, hs, hact⟩ := (mem_cTilde_iff hV hMle).1 huCT
  have h1 : u * n * u⁻¹ * n⁻¹ ∈ V₀ :=
    (actTil_eq_one_iff V₀ V hV ⟨u, hs⟩).1 hact n (hNV hn)
  rw [← commutatorElement_inv u n]
  exact V₀.inv_mem h1

private theorem w172_centralizes_of_mem_P {D : Data G} {V₀ V : Subgroup G} {x : G}
    (h : Hyp64 1 D.M V₀ V x) {u : G}
    (hu : u ∈ F11.CTilde D.M V₀ V ⊓ Subgroup.centralizer (V₀ : Set G)) :
    ∀ w ∈ V₀, u * w * u⁻¹ = w := by
  intro w hw
  have h1 : w * u = u * w := (Subgroup.mem_centralizer_iff.1 hu.2) w hw
  rw [← h1, mul_assoc, mul_inv_cancel, mul_one]

private theorem w172_V0_le_U {D : Data G} {V₀ V : Subgroup G} {x : G}
    (h : Hyp64 1 D.M V₀ V x) : V₀ ≤ UOf D.M V x := by
  have hV : IsElemAbelian 2 V := h.elemAbelian
  have hindex : (UOf D.M V x).relIndex V = 2 := Hyp64.w172_relIndex_uOf h
  have hgen : GenHyp D.M V x := genHyp_of_relIndex_two h hindex
  have hMle : D.M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hBM : BOf D.M V x ≤ D.M := inf_le_right
  have hBne : barSub V₀ V hV (BOf D.M V x) ≠ ⊥ := barSub_BOf_ne_bot h hgen
  have hDbar : ¬ BOf D.M V x ≤ F11.CTilde D.M V₀ V := fun hle =>
    hBne ((barSub_eq_bot_iff hV hMle h.le_normalizer₀ hBM).2 hle)
  have hCV : V ⊓ Subgroup.centralizer (BOf D.M V x : Set G) = NOf D.M V x ⊔ V₀ :=
    six_four_four_centralizer_V h
  have hCU : V ⊓ Subgroup.centralizer (BOf D.M V x : Set G) ≤ UOf D.M V x :=
    (six_four_three_of_relIndex_two (D := BOf D.M V x) h hindex le_rfl hDbar).1
  intro v hv
  apply hCU
  rw [hCV]
  exact Subgroup.mem_sup_right hv

private theorem w172_V0_inf_Vx_eq_bot {D : Data G} {V₀ V : Subgroup G} {x : G}
    (h : Hyp64 1 D.M V₀ V x) : V₀ ⊓ conjSubgroup V x = ⊥ := by
  have hVM : V ≤ D.M := by rw [← h.normalizer_eq]; exact Subgroup.le_normalizer
  have hN : NOf D.M V x ⊓ V₀ = ⊥ := NOf_inf_eq_bot h
  rw [NOf_eq D.M V x hVM] at hN
  refine le_bot_iff.1 fun z hz => ?_
  have hz2 : z ∈ (V ⊓ conjSubgroup V x) ⊓ V₀ := ⟨⟨h.le hz.1, hz.2⟩, hz.1⟩
  rwa [hN] at hz2

private theorem w172_U_le_normalizer_Vx {D : Data G} {V₀ V : Subgroup G} {x : G}
    (h : Hyp64 1 D.M V₀ V x) :
    UOf D.M V x ≤ Subgroup.normalizer (conjSubgroup V x : Set G) := by
  intro u hu
  have huM : u ∈ conjSubgroup D.M x := hu.2
  rw [mem_conjSubgroup_iff] at huM
  rw [← E3.conjSubgroup_normalizer V x]
  rw [mem_conjSubgroup_iff]
  rwa [h.normalizer_eq]

private theorem w172_V0x_centralizes_V0 {D : Data G} {V₀ V : Subgroup G} {x : G}
    (h : Hyp64 1 D.M V₀ V x) (hV0U : V₀ ≤ UOf D.M V x) :
    ∀ b ∈ conjSubgroup V₀ x, ∀ v ∈ V₀, b * v = v * b := by
  obtain ⟨-, -, -, -, -, -, hV0comm, -, -⟩ := h.inCalOStar
  have hV0Vx : V₀ ⊓ conjSubgroup V x = ⊥ := w172_V0_inf_Vx_eq_bot h
  have hUnorm : UOf D.M V x ≤ Subgroup.normalizer (conjSubgroup V x : Set G) :=
    w172_U_le_normalizer_Vx h
  intro b hb v hv
  rw [← commutatorElement_eq_one_iff_mul_comm]
  have hbVx : b ∈ conjSubgroup V x := conjSubgroup_mono h.le x hb
  have h1 : ⁅b, v⁆ ∈ V₀ := hV0comm (Subgroup.commutator_mem_commutator hb (h.le hv))
  have h2 : ⁅b, v⁆ ∈ conjSubgroup V x := by
    have hvNorm := hUnorm (hV0U hv)
    have h3 : v * b⁻¹ * v⁻¹ ∈ conjSubgroup V x :=
      (Subgroup.mem_normalizer_iff.1 hvNorm b⁻¹).1 ((conjSubgroup V x).inv_mem hbVx)
    rw [commutatorElement_def,
      show b * v * b⁻¹ * v⁻¹ = b * (v * b⁻¹ * v⁻¹) by group]
    exact (conjSubgroup V x).mul_mem hbVx h3
  have h3 : ⁅b, v⁆ ∈ (⊥ : Subgroup G) := by
    rw [← hV0Vx]; exact ⟨h1, h2⟩
  rwa [Subgroup.mem_bot] at h3

private theorem w172_comm_mem_V₀ {D : Data G} {V₀ V : Subgroup G} {x : G}
    (h : Hyp64 1 D.M V₀ V x) {b : G} (hb : b ∈ conjSubgroup V₀ x) {u : G} (hu : u ∈ V) :
    ⁅u, b⁆ ∈ V₀ := by
  obtain ⟨-, -, -, -, -, -, hV0comm, -, -⟩ := h.inCalOStar
  have h1 : ⁅b, u⁆ ∈ V₀ := hV0comm (Subgroup.commutator_mem_commutator hb hu)
  rw [← commutatorElement_inv b u]
  exact V₀.inv_mem h1

private theorem w172_comm_U_eq_one {D : Data G} {V₀ V : Subgroup G} {x : G}
    (h : Hyp64 1 D.M V₀ V x) (hV0U : V₀ ≤ UOf D.M V x) {b : G}
    (hb : b ∈ conjSubgroup V₀ x) {u : G} (hu : u ∈ UOf D.M V x) : ⁅u, b⁆ = 1 := by
  have hmem : ⁅u, b⁆ ∈ V₀ ⊓ conjSubgroup V x := by
    refine ⟨w172_comm_mem_V₀ h hb hu.1, ?_⟩
    have hbVx : b ∈ conjSubgroup V x := conjSubgroup_mono h.le x hb
    have huNorm := w172_U_le_normalizer_Vx h hu
    have h3 : u * b * u⁻¹ ∈ conjSubgroup V x :=
      (Subgroup.mem_normalizer_iff.1 huNorm b).1 hbVx
    rw [commutatorElement_def,
      show u * b * u⁻¹ * b⁻¹ = (u * b * u⁻¹) * b⁻¹ by group]
    exact (conjSubgroup V x).mul_mem h3 ((conjSubgroup V x).inv_mem hbVx)
  rw [w172_V0_inf_Vx_eq_bot h] at hmem
  exact Subgroup.mem_bot.1 hmem

private theorem w172_comm_of_not_mem_U {D : Data G} {V₀ V : Subgroup G} {x : G}
    (h : Hyp64 1 D.M V₀ V x) (hV0U : V₀ ≤ UOf D.M V x) {b : G}
    (hb : b ∈ conjSubgroup V₀ x) {v₀ u : G} (hv₀ : v₀ ∈ V) (hv₀U : v₀ ∉ UOf D.M V x)
    (hu : u ∈ V) (huU : u ∉ UOf D.M V x) : ⁅u, b⁆ = ⁅v₀, b⁆ := by
  have hV : IsElemAbelian 2 V := h.elemAbelian
  have hindex : (UOf D.M V x).relIndex V = 2 := Hyp64.w172_relIndex_uOf h
  have huv₀ : u * v₀ ∈ UOf D.M V x := by
    have h1 := (Subgroup.mul_mem_iff_of_index_two (H := (UOf D.M V x).subgroupOf V) hindex
      (a := ⟨u, hu⟩) (b := ⟨v₀, hv₀⟩)).2 (iff_of_false huU hv₀U)
    exact h1
  have hu_eq : u = v₀ * (u * v₀) := by
    have hcomm : v₀ * u = u * v₀ := IsElemAbelian.comm hV hv₀ hu
    have hvv : v₀ * v₀ = 1 := IsElemAbelian.mul_self_eq_one hV hv₀
    rw [← hcomm, ← mul_assoc, hvv, one_mul]
  rw [hu_eq, commutatorElement_mul_left_eq_conj_mul,
    w172_comm_U_eq_one h hV0U hb huv₀]
  group

private theorem w172_V0x_le_P {D : Data G} {V₀ V : Subgroup G} {x : G}
    (h : Hyp64 1 D.M V₀ V x) :
    conjSubgroup V₀ x ≤ F11.CTilde D.M V₀ V ⊓ Subgroup.centralizer (V₀ : Set G) := by
  have hindex : (UOf D.M V x).relIndex V = 2 := Hyp64.w172_relIndex_uOf h
  have hCB := six_four_four_centralizer_B_of_relIndex_two h hindex
  have hV0U : V₀ ≤ UOf D.M V x := w172_V0_le_U h
  intro b hb
  have hbB : b ∈ BOf D.M V x ⊓ F11.CTilde D.M V₀ V := by
    rw [hCB]
    exact Subgroup.mem_sup_right hb
  exact ⟨hbB.2,
    Subgroup.mem_centralizer_iff.2 fun v hv =>
      (w172_V0x_centralizes_V0 h hV0U b hb v hv).symm⟩

private theorem w172_exists_comm_b_of_mem {D : Data G} {V₀ V : Subgroup G} {x : G}
    (h : Hyp64 1 D.M V₀ V x) (hV0U : V₀ ≤ UOf D.M V x) {v₀ : G} (hv₀ : v₀ ∈ V)
    (hv₀U : v₀ ∉ UOf D.M V x) {w : G} (hw : w ∈ V₀) :
    ∃ b ∈ conjSubgroup V₀ x, ⁅v₀, b⁆ = w := by
  classical
  let φb : ↥(conjSubgroup V₀ x) →* ↥V₀ :=
  { toFun := fun b => ⟨⁅v₀, (b : G)⁆, w172_comm_mem_V₀ h b.2 hv₀⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro b₁ b₂
      apply Subtype.ext
      show ⁅v₀, (b₁ : G) * (b₂ : G)⁆ = ⁅v₀, (b₁ : G)⁆ * ⁅v₀, (b₂ : G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hcent := w172_V0x_centralizes_V0 h hV0U (b₁ : G) b₁.2
      have hmem : ⁅v₀, (b₂ : G)⁆ ∈ V₀ := w172_comm_mem_V₀ h b₂.2 hv₀
      have hcx : (b₁ : G) * ⁅v₀, (b₂ : G)⁆ * (b₁ : G)⁻¹ = ⁅v₀, (b₂ : G)⁆ := by
        have h := hcent _ hmem
        rw [h, mul_assoc, mul_inv_cancel, mul_one]
      have h := congrArg (fun z => ⁅v₀, (b₁ : G)⁆ * z) hcx
      simpa [mul_assoc] using h }
  have hφb_inj : Function.Injective φb := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    by_contra hb1
    have hbv : ⁅v₀, (b : G)⁆ = 1 := by
      have h := hb
      rw [MonoidHom.mem_ker] at h
      exact congrArg Subtype.val h
    have hcomm : v₀ * (b : G) = (b : G) * v₀ :=
      (commutatorElement_eq_one_iff_mul_comm).1 hbv
    have hcen : v₀ ∈ Subgroup.centralizer ({(b : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hcomm.symm
    have hle : Subgroup.centralizer ({(b : G)} : Set G) ≤ conjSubgroup D.M x :=
      conjSubgroup_V₀_centralizer_le h b.2 hb1
    have hU : v₀ ∈ UOf D.M V x := ⟨hv₀, hle hcen⟩
    exact hv₀U hU
  have hsurj : Function.Surjective φb := by
    haveI : Fintype ↥(conjSubgroup V₀ x) := Fintype.ofFinite _
    haveI : Fintype ↥V₀ := Fintype.ofFinite _
    have hcard : Fintype.card ↥(conjSubgroup V₀ x) = Fintype.card ↥V₀ := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact E3.card_conjSubgroup V₀ x
    exact (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)).1 hφb_inj
  obtain ⟨b, hb⟩ := hsurj ⟨w, hw⟩
  exact ⟨b, b.2, by simpa [φb] using congrArg Subtype.val hb⟩

private noncomputable def w172s_toE {V N : Subgroup G} (hV : IsElemAbelian 2 V)
    (hN : IsElemAbelian 2 N) (hNV : N ≤ V) : w172s_E N hN →ₗ[ZMod 2] w172s_E V hV :=
  AddMonoidHom.toZModLinearMap 2
    (AddMonoidHom.mk'
      (fun x => w172s_ofG hV ((Additive.toMul x : IntMod N hN).val)
        (hNV (IntMod.val_mem _)))
      (fun x y => w172s_ev_injective (by
        rw [w172s_ev_ofG, w172s_ev_add, w172s_ev_ofG, w172s_ev_ofG]
        rw [show (Additive.toMul (x + y) : IntMod N hN).val =
          (Additive.toMul x : IntMod N hN).val *
            (Additive.toMul y : IntMod N hN).val from rfl])))

private theorem w172s_ev_toE {V N : Subgroup G} {hV : IsElemAbelian 2 V}
    {hN : IsElemAbelian 2 N} {hNV : N ≤ V} (x : w172s_E N hN) :
    w172s_ev (w172s_toE hV hN hNV x) = (Additive.toMul x : IntMod N hN).val := rfl

private noncomputable def w172s_phiP {V N V₀ : Subgroup G} (hV : IsElemAbelian 2 V)
    (hN : IsElemAbelian 2 N) (hV₀ : IsElemAbelian 2 V₀) (hV₀le : V₀ ≤ V) (hNV : N ≤ V)
    (P : Subgroup G) (hP : ∀ u ∈ P, ∀ n ∈ N, ⁅n, u⁆ ∈ V₀) (t : ↥P) :
    w172s_E N hN →ₗ[ZMod 2] w172s_E V₀ hV₀ :=
  AddMonoidHom.toZModLinearMap 2
    (AddMonoidHom.mk'
      (fun x => w172s_ofG hV₀ ⁅(Additive.toMul x : IntMod N hN).val, (t : G)⁆
        (hP (t : G) t.2 _ (IntMod.val_mem _)))
      (fun x y => w172s_ev_injective (by
        rw [w172s_ev_ofG, w172s_ev_add, w172s_ev_ofG, w172s_ev_ofG]
        rw [show (Additive.toMul (x + y) : IntMod N hN).val =
          (Additive.toMul x : IntMod N hN).val *
            (Additive.toMul y : IntMod N hN).val from rfl]
        exact w172_commutator_mul_eq_mul_commutator hV hV₀le (hNV (IntMod.val_mem _))
          (hNV (IntMod.val_mem _)) (hP (t : G) t.2 _ (IntMod.val_mem _))
          (hP (t : G) t.2 _ (IntMod.val_mem _)))))

private theorem w172s_ev_phiP {V N V₀ : Subgroup G} {hV : IsElemAbelian 2 V}
    {hN : IsElemAbelian 2 N} {hV₀ : IsElemAbelian 2 V₀} {hV₀le : V₀ ≤ V} {hNV : N ≤ V}
    {P : Subgroup G} {hP : ∀ u ∈ P, ∀ n ∈ N, ⁅n, u⁆ ∈ V₀} (t : ↥P) (x : w172s_E N hN) :
    w172s_ev (w172s_phiP hV hN hV₀ hV₀le hNV P hP t x) =
      ⁅(Additive.toMul x : IntMod N hN).val, (t : G)⁆ := rfl

private noncomputable def w172s_fLin {N V₀ : Subgroup G} (hN : IsElemAbelian 2 N)
    (hV₀ : IsElemAbelian 2 V₀) (f : ↥N →* ↥V₀) :
    w172s_E N hN →ₗ[ZMod 2] w172s_E V₀ hV₀ :=
  AddMonoidHom.toZModLinearMap 2
    (AddMonoidHom.mk'
      (fun x => w172s_ofG hV₀
        ((f ⟨(Additive.toMul x : IntMod N hN).val, IntMod.val_mem _⟩ : ↥V₀).val)
        (f ⟨(Additive.toMul x : IntMod N hN).val, IntMod.val_mem _⟩).2)
      (fun x y => w172s_ev_injective (by
        rw [w172s_ev_ofG, w172s_ev_add, w172s_ev_ofG, w172s_ev_ofG]
        have harg : (⟨(Additive.toMul (x + y) : IntMod N hN).val,
              IntMod.val_mem _⟩ : ↥N) =
            ⟨(Additive.toMul x : IntMod N hN).val, IntMod.val_mem _⟩ *
              ⟨(Additive.toMul y : IntMod N hN).val, IntMod.val_mem _⟩ := by
          apply Subtype.ext
          rfl
        rw [harg, map_mul]
        rfl)))

private theorem w172s_ev_fLin {N V₀ : Subgroup G} {hN : IsElemAbelian 2 N}
    {hV₀ : IsElemAbelian 2 V₀} (f : ↥N →* ↥V₀) (x : w172s_E N hN) :
    w172s_ev (w172s_fLin hN hV₀ f x) =
      (f ⟨(Additive.toMul x : IntMod N hN).val, IntMod.val_mem _⟩ : ↥V₀).val := rfl

theorem w172_exists_comm_eq {D : Data G} {V₀ V : Subgroup G} (hW : WeakClosureSetting D V₀ V)
    (hV₀ : V₀ ≠ ⊥) {x : G} (h : Hyp64 1 D.M V₀ V x) {N : Subgroup G} (hNV : N ≤ V)
    (hN : N ⊓ V₀ = ⊥) (f : ↥N →* ↥V₀) :
    ∃ t ∈ F11.CTilde D.M V₀ V ⊓ Subgroup.centralizer (V₀ : Set G),
      ∀ n : ↥N, ⁅(n : G), t⁆ = (f n : G) := by
  classical
  have hV : IsElemAbelian 2 V := h.elemAbelian
  have hV₀ab : IsElemAbelian 2 V₀ :=
    ⟨⟨⟨fun a b => Subtype.ext (hV.comm (h.le a.2) (h.le b.2))⟩⟩,
      fun x hx => hV.2 x (h.le hx)⟩
  have hNab : IsElemAbelian 2 N :=
    ⟨⟨⟨fun a b => Subtype.ext (hV.comm (hNV a.2) (hNV b.2))⟩⟩,
      fun x hx => hV.2 x (hNV hx)⟩
  have hMle : D.M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hUrel : (UOf D.M V x).relIndex V = 2 := Hyp64.w172_relIndex_uOf h
  have hV0U : V₀ ≤ UOf D.M V x := w172_V0_le_U h
  set P : Subgroup G := F11.CTilde D.M V₀ V ⊓ Subgroup.centralizer (V₀ : Set G) with hPdef
  have hPcomm : ∀ u ∈ P, ∀ n ∈ N, ⁅n, u⁆ ∈ V₀ := fun u hu n hn => w172_mem_comm_P h hNV hu hn
  have hPcent : ∀ u ∈ P, ∀ w ∈ V₀, u * w * u⁻¹ = w := fun u hu w hw =>
    w172_centralizes_of_mem_P h hu w hw
  have hgen : ConjGenerated D.M V₀ V := fun v hv hv0 => (hW.gen hV₀ v hv hv0).symm
  let fFam : ↥D.M → Module.Dual (ZMod 2) (w172s_E N hNab) := fun g =>
    (w172s_fW hV (UOf D.M V x) hUrel).comp
      ((w172s_cLin hV (g : G) (hMle g.2)).comp (w172s_toE hV hNab hNV))
  let K : Subgroup G :=
    { carrier := {z | z ∈ V ∧ ∀ g ∈ D.M, g * z * g⁻¹ ∈ UOf D.M V x}
      mul_mem' := by
        rintro z z' ⟨hzV, hz⟩ ⟨hz'V, hz'⟩
        refine ⟨V.mul_mem hzV hz'V, fun g hg => ?_⟩
        have h1 : g * (z * z') * g⁻¹ = (g * z * g⁻¹) * (g * z' * g⁻¹) := by group
        rw [h1]
        exact (UOf D.M V x).mul_mem (hz g hg) (hz' g hg)
      one_mem' := ⟨V.one_mem, fun g _ => by simpa using (UOf D.M V x).one_mem⟩
      inv_mem' := by
        rintro z ⟨hzV, hz⟩
        refine ⟨V.inv_mem hzV, fun g hg => ?_⟩
        have h1 : g * z⁻¹ * g⁻¹ = (g * z * g⁻¹)⁻¹ := by group
        rw [h1]
        exact (UOf D.M V x).inv_mem (hz g hg) }
  have hKleV : K ≤ V := fun _ hz => hz.1
  have hKU : K ≤ UOf D.M V x := fun z hz => by simpa using hz.2 1 D.M.one_mem
  have hMK : D.M ≤ Subgroup.normalizer (K : Set G) := by
    have key : ∀ m ∈ D.M, ∀ z ∈ K, m * z * m⁻¹ ∈ K := by
      intro m hm z hz
      refine ⟨(Subgroup.mem_normalizer_iff.1 (hMle hm) z).1 hz.1, fun g hg => ?_⟩
      have h1 := hz.2 (g * m) (D.M.mul_mem hg hm)
      have e : g * (m * z * m⁻¹) * g⁻¹ = (g * m) * z * (g * m)⁻¹ := by group
      rw [e]
      exact h1
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨key m hm z, fun h => ?_⟩
    have h1 := key m⁻¹ (D.M.inv_mem hm) (m * z * m⁻¹) h
    rwa [show m⁻¹ * (m * z * m⁻¹) * m⁻¹⁻¹ = z by group] at h1
  have hUneV : ¬ V ≤ UOf D.M V x := fun hle => by
    have h1 : (UOf D.M V x).relIndex V = 1 := Subgroup.relIndex_eq_one.2 hle
    rw [hUrel] at h1
    norm_num at h1
  have hKV₀ : K ≤ V₀ := by
    by_contra hnot
    have hKV : K = V := eq_of_normalizer_of_not_le_of_conjGenerated hgen hKleV hMK hnot
    exact hUneV (hKV ▸ hKU)
  have hfker : ⨅ g : ↥D.M, LinearMap.ker (fFam g) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Submodule.mem_bot]
    have ha' : ∀ g : ↥D.M, fFam g a = 0 := by
      intro g
      rw [Submodule.mem_iInf] at ha
      exact LinearMap.mem_ker.1 (ha g)
    let v : G := (Additive.toMul a : IntMod N hNab).val
    have hvN : v ∈ N := IntMod.val_mem _
    have hvV : v ∈ V := hNV hvN
    have hvK : v ∈ K := by
      refine ⟨hvV, fun g hg => ?_⟩
      have h0 : w172s_ev
          (w172s_cLin hV g (hMle hg) (w172s_toE hV hNab hNV a)) ∈ UOf D.M V x := by
        by_contra hnot
        have h1 : fFam ⟨g, hg⟩ a = 1 := w172s_fW_of_not_mem (hW := hUrel) hnot
        have h2 := ha' ⟨g, hg⟩
        rw [h1] at h2
        exact one_ne_zero h2
      have h0' : (g : G) * v * (g : G)⁻¹ ∈ UOf D.M V x := by
        simpa only [w172s_ev_cLin, w172s_ev_toE, v] using h0
      exact h0'
    have hv0 : v = 1 := by
      have h : v ∈ N ⊓ V₀ := ⟨hvN, hKV₀ hvK⟩
      rwa [hN] at h
    apply w172s_ev_injective
    rw [show w172s_ev a = v from rfl, hv0, w172s_ev_zero]
  let Φ : Submodule (ZMod 2) (w172s_E N hNab →ₗ[ZMod 2] w172s_E V₀ hV₀ab) :=
    { carrier := {φ | ∃ t : ↥P, φ = w172s_phiP hV hNab hV₀ab h.le hNV P hPcomm t}
      zero_mem' := by
        refine ⟨1, ?_⟩
        ext a
        apply w172s_ev_injective
        show w172s_ev ((0 : w172s_E N hNab →ₗ[ZMod 2] w172s_E V₀ hV₀ab) a) =
          w172s_ev (w172s_phiP hV hNab hV₀ab h.le hNV P hPcomm 1 a)
        rw [LinearMap.zero_apply, w172s_ev_phiP, w172s_ev_zero, Subgroup.coe_one,
          commutatorElement_one_right]
      add_mem' := by
        rintro φ ψ ⟨t, rfl⟩ ⟨t', rfl⟩
        refine ⟨t * t', ?_⟩
        ext a
        apply w172s_ev_injective
        show w172s_ev (w172s_phiP hV hNab hV₀ab h.le hNV P hPcomm t a +
            w172s_phiP hV hNab hV₀ab h.le hNV P hPcomm t' a) =
          w172s_ev (w172s_phiP hV hNab hV₀ab h.le hNV P hPcomm (t * t') a)
        rw [w172s_ev_add, w172s_ev_phiP, w172s_ev_phiP, w172s_ev_phiP]
        exact (w172_commutator_mul_right_eq_mul_commutator (hPcent (t : G) t.2)
          (hPcomm (t' : G) t'.2 _ (IntMod.val_mem _))).symm
      smul_mem' := by
        intro c φ hφ
        obtain ⟨t, rfl⟩ := hφ
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
        · refine ⟨1, ?_⟩
          ext a
          apply w172s_ev_injective
          show w172s_ev (((0 : ZMod 2) •
              w172s_phiP hV hNab hV₀ab h.le hNV P hPcomm t) a) =
            w172s_ev (w172s_phiP hV hNab hV₀ab h.le hNV P hPcomm 1 a)
          rw [zero_smul, LinearMap.zero_apply, w172s_ev_phiP, w172s_ev_zero,
            Subgroup.coe_one, commutatorElement_one_right]
        · exact ⟨t, by rw [one_smul]⟩ }
  have hΦ : ∀ (g : ↥D.M) (z : w172s_E V₀ hV₀ab),
      (fFam g).smulRight z ∈ Φ := by
    intro g z
    obtain ⟨v₀, hv₀V, hv₀U⟩ : ∃ v, v ∈ V ∧ v ∉ UOf D.M V x := by
      by_contra hcon
      apply hUneV
      intro v hv
      by_contra hvU
      exact hcon ⟨v, hv, hvU⟩
    let z₀ : G := (Additive.toMul z : IntMod V₀ hV₀ab).val
    have hz₀ : z₀ ∈ V₀ := IntMod.val_mem _
    have hwV₀ : (g : G) * z₀ * (g : G)⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.1 (h.le_normalizer₀ g.2) z₀).1 hz₀
    obtain ⟨b, hb, hbv₀⟩ := w172_exists_comm_b_of_mem h hV0U hv₀V hv₀U hwV₀
    have hbP : b ∈ P := w172_V0x_le_P h hb
    have htP : (g : G)⁻¹ * b * (g : G) ∈ P := by
      have h := (Subgroup.mem_normalizer_iff.1
        (w172_mem_conj_P h (D.M.inv_mem g.2)) b).1 hbP
      simpa only [inv_inv] using h
    refine ⟨⟨(g : G)⁻¹ * b * (g : G), htP⟩, ?_⟩
    ext a
    apply w172s_ev_injective
    show w172s_ev ((fFam g).smulRight z a) =
      w172s_ev (w172s_phiP hV hNab hV₀ab h.le hNV P hPcomm
        ⟨(g : G)⁻¹ * b * (g : G), htP⟩ a)
    by_cases hU : (g : G) * (Additive.toMul a : IntMod N hNab).val * (g : G)⁻¹ ∈ UOf D.M V x
    · have hf0 : fFam g a = 0 := by
        apply w172s_fW_of_mem (hW := hUrel)
        simpa only [LinearMap.comp_apply, w172s_ev_cLin, w172s_ev_toE] using hU
      rw [LinearMap.smulRight_apply, hf0, zero_smul, w172s_ev_zero, w172s_ev_phiP]
      have h1 : ⁅(Additive.toMul a : IntMod N hNab).val, (g : G)⁻¹ * b * (g : G)⁆ = 1 := by
        rw [w172_comm_conj_eq]
        rw [w172_comm_U_eq_one h hV0U hb hU]
        group
      rw [h1]
    · have hf1 : fFam g a = 1 := by
        apply w172s_fW_of_not_mem (hW := hUrel)
        simpa only [LinearMap.comp_apply, w172s_ev_cLin, w172s_ev_toE] using hU
      rw [LinearMap.smulRight_apply, hf1, one_smul, w172s_ev_phiP]
      have huV : (g : G) * (Additive.toMul a : IntMod N hNab).val * (g : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 (hMle g.2) _).1 (hNV (IntMod.val_mem _))
      have h1 : ⁅(Additive.toMul a : IntMod N hNab).val, (g : G)⁻¹ * b * (g : G)⁆ = z₀ := by
        rw [w172_comm_conj_eq]
        rw [w172_comm_of_not_mem_U h hV0U hb hv₀V hv₀U huV hU, hbv₀]
        group
      rw [show w172s_ev z = z₀ from rfl, h1]
  have hfLin : w172s_fLin hNab hV₀ab f ∈ Φ := by
    rw [w172s_eq_top_of_smulRight_mem (f := fFam) hfker Φ hΦ]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := hfLin
  refine ⟨(t : G), t.2, fun n => ?_⟩
  let x : w172s_E N hNab := Additive.ofMul (n : IntMod N hNab)
  have hx := congrArg
    (fun (φ : w172s_E N hNab →ₗ[ZMod 2] w172s_E V₀ hV₀ab) => w172s_ev (φ x)) ht
  rw [w172s_ev_fLin, w172s_ev_phiP] at hx
  exact hx.symm

theorem w172_exists_comm_eq_R {D : Data G} {V₀ V : Subgroup G} (hW : WeakClosureSetting D V₀ V)
    (hV₀ : V₀ ≠ ⊥) {x : G} (h : Hyp64 1 D.M V₀ V x) {N : Subgroup G} (hNV : N ≤ V)
    (hN : N ⊓ V₀ = ⊥) (f : ↥N →* ↥V₀) :
    ∃ t ∈ w172R D V₀ V, ∀ n : ↥N, ⁅(n : G), t⁆ = (f n : G) := by
  classical
  obtain ⟨t, htP, ht⟩ := w172_exists_comm_eq hW hV₀ h hNV hN f
  set P : Subgroup G := F11.CTilde D.M V₀ V ⊓ Subgroup.centralizer (V₀ : Set G) with hPdef
  have hV : IsElemAbelian 2 V := h.elemAbelian
  have hV₀le : V₀ ≤ V := h.le
  have hMle : D.M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hMle₀ : D.M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  have hV₀ab : IsElemAbelian 2 V₀ :=
    ⟨⟨⟨fun a b => Subtype.ext (hV.comm (hV₀le a.2) (hV₀le b.2))⟩⟩,
      fun x hx => hV.2 x (hV₀le hx)⟩
  have hmemV₀ : ∀ u ∈ P, ∀ n ∈ N, ⁅(n : G), u⁆ ∈ V₀ := by
    intro u hu n hn
    obtain ⟨huCT, -⟩ := Subgroup.mem_inf.1 hu
    obtain ⟨-, hs, hact⟩ := (mem_cTilde_iff hV hMle).1 huCT
    have h1 : u * (n : G) * u⁻¹ * (n : G)⁻¹ ∈ V₀ :=
      (actTil_eq_one_iff V₀ V hV ⟨u, hs⟩).1 hact (n : G) (hNV hn)
    rw [← commutatorElement_inv u (n : G)]
    exact V₀.inv_mem h1
  have hcentV₀ : ∀ u ∈ P, ∀ w ∈ V₀, u * w * u⁻¹ = w := by
    intro u hu w hw
    have h1 : w * u = u * w := (Subgroup.mem_centralizer_iff.1 hu.2) w hw
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  let ψ : ↥P →* (↥N → ↥V₀) :=
  { toFun := fun u n => ⟨⁅(n : G), (u : G)⁆, hmemV₀ (u : G) u.2 (n : G) n.2⟩
    map_one' := by
      funext n
      apply Subtype.ext
      show ⁅(n : G), ((1 : ↥P) : G)⁆ = (1 : G)
      rw [Subgroup.coe_one, commutatorElement_one_right]
    map_mul' := by
      intro u u'
      funext n
      apply Subtype.ext
      show ⁅(n : G), ((u : G) * (u' : G))⁆ =
        ⁅(n : G), (u : G)⁆ * ⁅(n : G), (u' : G)⁆
      exact w172_commutator_mul_right_eq_mul_commutator (hcentV₀ (u : G) u.2)
        (hmemV₀ (u' : G) u'.2 (n : G) n.2) }
  have hconj_mem : ∀ m ∈ D.M, ∀ c ∈ P, m * c * m⁻¹ ∈ P := by
    intro m hm c hc
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact uc22p22q_ctilde_conj_mem hMle hMle₀ hm hc.1
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hvm : m⁻¹ * v * m ∈ V₀ := by
        have h := (((Subgroup.mem_normalizer_iff.1 (hMle₀ (D.M.inv_mem hm))) v).1) hv
        simpa using h
      have h2 : c * (m⁻¹ * v * m) = (m⁻¹ * v * m) * c :=
        ((Subgroup.mem_centralizer_iff.1 hc.2) _ hvm).symm
      calc v * (m * c * m⁻¹) = m * ((m⁻¹ * v * m) * c) * m⁻¹ := by group
        _ = m * (c * (m⁻¹ * v * m)) * m⁻¹ := by rw [← h2]
        _ = (m * c * m⁻¹) * v := by group
  have hPleM : P ≤ D.M := fun x hx => (mem_cTilde_iff hV hMle).1 hx.1 |>.1
  have hPnorm : (P.subgroupOf D.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPleM]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨hconj_mem m hm c, fun hc => ?_⟩
    have hm' : m⁻¹ ∈ D.M := D.M.inv_mem hm
    have h := hconj_mem m⁻¹ hm' (m * c * m⁻¹) hc
    rwa [show m⁻¹ * (m * c * m⁻¹) * m⁻¹⁻¹ = c by group] at h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
  have hTP : IsSylowIn 2 (D.T ⊓ P) P := hT.inf_normal hPleM hPnorm
  set A : Subgroup ↥P := (D.T ⊓ P).subgroupOf P with hAdef
  have hA : IsSylowIn 2 A ⊤ := by
    have h := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := D.T ⊓ P) (K := P) (H := P)
      inf_le_right le_rfl).mpr hTP
    rwa [Subgroup.subgroupOf_self] at h
  have hAodd : ¬ 2 ∣ A.relIndex ⊤ := hA.not_dvd_relIndex
  let K : Subgroup ↥P := ψ.ker
  have hKrel : K.relIndex ⊤ = Nat.card ψ.range := by
    rw [Subgroup.relIndex_ker, ← MonoidHom.range_eq_map]
  have hP2range : IsPGroup 2 ψ.range := by
    rw [isPGroup_iff_pow_pow_eq_one]
    rintro ⟨g, hg⟩
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hg
    refine ⟨1, ?_⟩
    rw [show (2 : ℕ) ^ 1 = 2 by norm_num, pow_two]
    apply Subtype.ext
    change ψ u * ψ u = 1
    ext n
    exact IsElemAbelian.mul_self_eq_one hV₀ab (hmemV₀ (u : G) u.2 (n : G) n.2)
  obtain ⟨n₂, hn₂⟩ := IsPGroup.iff_card.mp hP2range
  let L : Subgroup ↥P := K ⊔ A
  have hLdvd_K : L.relIndex ⊤ ∣ K.relIndex ⊤ :=
    Subgroup.relIndex_dvd_of_le_left (H := K) (K := L) (L := ⊤) le_sup_left
  have hdvd_pow : L.relIndex ⊤ ∣ 2 ^ n₂ := by
    refine hLdvd_K.trans ?_
    rw [hKrel, hn₂]
  have hLodd : ¬ 2 ∣ L.relIndex ⊤ := fun h2 =>
    hAodd (h2.trans (Subgroup.relIndex_dvd_of_le_left (H := A) (K := L) (L := ⊤)
      le_sup_right))
  have hone : L.relIndex ⊤ = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd_pow
    rcases j with _ | j
    · simpa using hj
    · exfalso
      apply hLodd
      refine ⟨2 ^ j, ?_⟩
      rw [hj, pow_succ, Nat.mul_comm]
  have hLtop : L = ⊤ := le_antisymm le_top (Subgroup.relIndex_eq_one.1 hone)
  let tP : ↥P := ⟨t, htP⟩
  have htL : tP ∈ L := by rw [hLtop]; exact Subgroup.mem_top tP
  obtain ⟨k, hkK, a, haA, hka⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := K) (t := A) (x := tP)).1 htL
  have hψa : ψ a = ψ tP := by
    rw [← hka, map_mul, MonoidHom.mem_ker.1 hkK, one_mul]
  have haMem : (a : G) ∈ D.T ⊓ P := Subgroup.mem_subgroupOf.1 haA
  refine ⟨(a : G), ?_, ?_⟩
  · rw [w172R, inf_assoc]
    exact ⟨haMem.1, haMem.2⟩
  · intro n
    have h1 : ((ψ a) n : G) = ((ψ tP) n : G) := by rw [hψa]
    change ((ψ a) n : G) = ((f n : ↥V₀) : G)
    rw [h1]
    exact ht n

end CFSG.LocalAnalysis.WeakClosure81

end
