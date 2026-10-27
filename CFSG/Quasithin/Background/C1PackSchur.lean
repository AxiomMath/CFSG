module

public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem schur_perfect_trivial {P : Type*} [CommGroup P] [Finite P] (Zq : Subgroup P)
    {SG TG : Type*} [Group SG] [Group TG] (σ : SG →* MulAut P) (τ : TG →* MulAut P)
    (hσ : ∀ s x, x ∈ Zq ↔ σ s x ∈ Zq) (hτ : ∀ t x, x ∈ Zq ↔ τ t x ∈ Zq)
    (hne : Zq ≠ ⊤)
    (hirr : ∀ J : Subgroup P, Zq ≤ J → (∀ s : SG, ∀ x ∈ J, σ s x ∈ J) → J = Zq ∨ J = ⊤)
    (hcomm : ∀ s t x, σ s (τ t x) * (τ t (σ s x))⁻¹ ∈ Zq)
    (hperf : commutator TG = ⊤) :
    ∀ t x, τ t x * x⁻¹ ∈ Zq := by
  classical
  have hmap : ∀ φ : MulAut P, (∀ x, x ∈ Zq ↔ φ x ∈ Zq) →
      Zq.map (φ : P ≃* P).toMonoidHom = Zq := by
    intro φ hφ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hφ x).1 hx
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      exact (hφ _).2 (by simpa using hy)
  let σ' : SG →* MulAut (P ⧸ Zq) :=
    { toFun := fun s => QuotientGroup.congr Zq Zq (σ s) (hmap (σ s) (hσ s))
      map_one' := by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          show (↑((σ 1) x) : P ⧸ Zq) = ↑x
          rw [map_one]; rfl
      map_mul' := fun s s' => by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          show (↑((σ (s * s')) x) : P ⧸ Zq) = ↑((σ s) ((σ s') x))
          rw [map_mul]; rfl }
  let τ' : TG →* MulAut (P ⧸ Zq) :=
    { toFun := fun t => QuotientGroup.congr Zq Zq (τ t) (hmap (τ t) (hτ t))
      map_one' := by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          show (↑((τ 1) x) : P ⧸ Zq) = ↑x
          rw [map_one]; rfl
      map_mul' := fun t t' => by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          show (↑((τ (t * t')) x) : P ⧸ Zq) = ↑((τ t) ((τ t') x))
          rw [map_mul]; rfl }
  have hnt : Nontrivial (P ⧸ Zq) := by
    obtain ⟨x, hx⟩ : ∃ x : P, x ∉ Zq := by
      by_contra h
      push Not at h
      exact hne (eq_top_iff.2 fun x _ => h x)
    exact ⟨⟨QuotientGroup.mk x, 1, fun h => hx ((QuotientGroup.eq_one_iff x).1 h)⟩⟩
  have hirr' : XMod.IsIrrSec ↥(σ'.range) (⊥ : Subgroup (P ⧸ Zq)) ⊤ := by
    refine ⟨bot_lt_top, fun J hJ _ _ => ?_⟩
    have hZJ : Zq ≤ J.comap (QuotientGroup.mk' Zq) := fun x hx => by
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact J.one_mem
    have hJσ : ∀ s : SG, ∀ x ∈ J.comap (QuotientGroup.mk' Zq),
        σ s x ∈ J.comap (QuotientGroup.mk' Zq) := by
      intro s x hx
      exact hJ ⟨σ' s, ⟨s, rfl⟩⟩ (QuotientGroup.mk x) hx
    rcases hirr _ hZJ hJσ with h | h
    · left
      refine (Subgroup.eq_bot_iff_forall J).2 fun q hq => ?_
      induction q using QuotientGroup.induction_on with
      | H x =>
        have : x ∈ J.comap (QuotientGroup.mk' Zq) := hq
        rw [h] at this
        exact (QuotientGroup.eq_one_iff x).2 this
    · right
      refine eq_top_iff.2 fun q _ => ?_
      induction q using QuotientGroup.induction_on with
      | H x =>
        have : x ∈ J.comap (QuotientGroup.mk' Zq) := by rw [h]; trivial
        exact this
  have hcomm' : ∀ s ∈ σ'.range, ∀ t ∈ τ'.range, s * t = t * s := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      show (↑((σ s) ((τ t) x)) : P ⧸ Zq) = ↑((τ t) ((σ s) x))
      exact (QuotientGroup.eq_iff_div_mem).2 (by simpa [div_eq_mul_inv] using hcomm s t x)
  have hab := A37.commute_of_irreducible (σ'.range) (τ'.range) hirr' hcomm'
  have hker : τ'.ker = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hperf, _root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hab _ ⟨x, rfl⟩ _ ⟨y, rfl⟩)
  intro t x
  have h1 : τ' t = 1 := by
    have : t ∈ τ'.ker := by rw [hker]; trivial
    exact this
  have h2 : τ' t (QuotientGroup.mk x) = QuotientGroup.mk x := by rw [h1]; rfl
  have h3 : (QuotientGroup.mk (τ t x) : P ⧸ Zq) = QuotientGroup.mk x := h2
  simpa [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem).1 h3


variable {G : Type} [Group G] [Finite G]

theorem block_perfect_acts_trivially {L A : Subgroup G} (hL : IsShort2 L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA : ⁅A, A⁆ = A)
    (hcomm : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ blockU L) :
    ∀ a ∈ A, ∀ u ∈ blockU L, a * u * a⁻¹ * u⁻¹ ∈ blockZ L := by
  classical
  have hV : IsElemAbelian 2 (blockU L) := C5.isElemAbelian_two_iff.2 (C1.elemAb2_blockU hL)
  let Zq : Subgroup (IntMod (blockU L) hV) :=
    { carrier := {v | v.val ∈ blockZ L}
      mul_mem' := fun {a b} ha hb => by
        show (a * b).val ∈ blockZ L
        rw [IntMod.val_mul]
        exact mul_mem ha hb
      one_mem' := by
        show (1 : IntMod (blockU L) hV).val ∈ blockZ L
        rw [IntMod.val_one]
        exact one_mem _
      inv_mem' := fun {a} ha => by
        show (a⁻¹).val ∈ blockZ L
        rw [IntMod.val_inv]
        exact inv_mem ha }
  have hmemZq : ∀ v : IntMod (blockU L) hV, v ∈ Zq ↔ v.val ∈ blockZ L := fun v => Iff.rfl
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) := C1.le_normalizer_blockU L
  have hAU : A ≤ Subgroup.normalizer (blockU L : Set G) := fun a ha =>
    C1.mem_normalizer_blockU (hAN ha)
  let σ : ↥L →* MulAut (IntMod (blockU L) hV) := (convI hV).comp (Subgroup.inclusion hLU)
  let τ : ↥A →* MulAut (IntMod (blockU L) hV) := (convI hV).comp (Subgroup.inclusion hAU)
  have hσval : ∀ (s : ↥L) (x : IntMod (blockU L) hV),
      (σ s x).val = (s : G) * x.val * (s : G)⁻¹ := fun s x => convI_apply_val hV _ x
  have hτval : ∀ (t : ↥A) (x : IntMod (blockU L) hV),
      (τ t x).val = (t : G) * x.val * (t : G)⁻¹ := fun t x => convI_apply_val hV _ x
  have hσ : ∀ (s : ↥L) x, x ∈ Zq ↔ σ s x ∈ Zq := by
    intro s x
    rw [hmemZq, hmemZq, hσval]
    exact Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockZ (Subgroup.le_normalizer s.2))
      x.val
  have hτ : ∀ (t : ↥A) x, x ∈ Zq ↔ τ t x ∈ Zq := by
    intro t x
    rw [hmemZq, hmemZq, hτval]
    exact Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockZ (hAN t.2)) x.val
  have hne : Zq ≠ ⊤ := by
    intro htop
    obtain ⟨u, hu, huZ⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp hL.2.2.2.2.1).2
    have : IntMod.mk hV ⟨u, hu⟩ ∈ Zq := by rw [htop]; trivial
    exact huZ this
  let valHom : IntMod (blockU L) hV →* G :=
    { toFun := IntMod.val, map_one' := IntMod.val_one, map_mul' := IntMod.val_mul }
  have hirr : ∀ J : Subgroup (IntMod (blockU L) hV), Zq ≤ J → (∀ s : ↥L, ∀ x ∈ J, σ s x ∈ J) →
      J = Zq ∨ J = ⊤ := by
    intro J hZJ hJσ
    set W : Subgroup G := J.map valHom with hW
    have hZW : blockZ L ≤ W := by
      intro z hz
      have hzU : z ∈ blockU L := hz.1
      exact ⟨IntMod.mk hV ⟨z, hzU⟩, hZJ (hmemZq _ |>.2 hz), rfl⟩
    have hWU : W ≤ blockU L := by
      rintro _ ⟨v, -, rfl⟩
      exact v.val_mem
    have hfwd : ∀ l ∈ L, ∀ h ∈ W, l * h * l⁻¹ ∈ W := by
      rintro l hl _ ⟨v, hv, rfl⟩
      refine ⟨σ ⟨l, hl⟩ v, hJσ ⟨l, hl⟩ v hv, ?_⟩
      show (σ ⟨l, hl⟩ v).val = _
      rw [hσval]
      rfl
    have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact fun hx => hfwd l hl x hx
      · intro hx
        have := hfwd l⁻¹ (inv_mem hl) _ hx
        simpa [mul_assoc] using this
    rcases hL.2.2.2.2.2 W hZW hWU hLW with h | h
    · left
      refine le_antisymm (fun v hv => ?_) hZJ
      have : v.val ∈ W := ⟨v, hv, rfl⟩
      rw [h] at this
      exact (hmemZq v).2 this
    · right
      refine eq_top_iff.2 fun v _ => ?_
      have : v.val ∈ W := by rw [h]; exact v.val_mem
      obtain ⟨v', hv', hv'v⟩ := this
      have : v' = v := IntMod.val_injective hv'v
      rw [← this]
      exact hv'
  have hcomm' : ∀ (s : ↥L) (t : ↥A) x, σ s (τ t x) * (τ t (σ s x))⁻¹ ∈ Zq := by
    intro s t x
    have hxU : x.val ∈ blockU L := x.val_mem
    have hcU : (s : G) * (t : G) * (s : G)⁻¹ * (t : G)⁻¹ ∈ blockU L := by
      have := inv_mem (hcomm t t.2 s s.2)
      simpa [mul_assoc] using this
    have h1 : (t : G) * (s * x.val * (s : G)⁻¹) * (t : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (hAN t.2))
        _).mp ((Subgroup.mem_normalizer_iff.mp (hLU s.2) _).mp hxU)
    have heq : σ s (τ t x) = τ t (σ s x) := by
      refine IntMod.val_injective ?_
      rw [hσval, hτval, hτval, hσval]
      set c := (s : G) * (t : G) * (s : G)⁻¹ * (t : G)⁻¹ with hc
      have hcomm2 : (t : G) * ((s : G) * x.val * (s : G)⁻¹) * (t : G)⁻¹ * c =
          c * ((t : G) * ((s : G) * x.val * (s : G)⁻¹) * (t : G)⁻¹) :=
        (C1.blockU_comm hL _ h1 c (C1.blockU_le_blockQ hL hcU))
      have e : (s : G) * ((t : G) * x.val * (t : G)⁻¹) * (s : G)⁻¹ =
          c * ((t : G) * ((s : G) * x.val * (s : G)⁻¹) * (t : G)⁻¹) * c⁻¹ := by
        rw [hc]; group
      rw [e, ← hcomm2]
      group
    rw [heq, mul_inv_cancel]
    exact Zq.one_mem
  have hperf : commutator ↥A = ⊤ := (Subgroup.isPerfect_iff.2 hA).commutator_eq_top
  have key := schur_perfect_trivial Zq σ τ hσ hτ hne hirr hcomm' hperf
  intro a ha u hu
  have := key ⟨a, ha⟩ (IntMod.mk hV ⟨u, hu⟩)
  rw [hmemZq, IntMod.val_mul, IntMod.val_inv, hτval] at this
  exact this

end CFSG.Quasithin.C1Pack
