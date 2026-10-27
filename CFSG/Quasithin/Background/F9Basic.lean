module

public import CFSG.Quasithin.Background.F8Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

variable {G : Type*} [Group G]

theorem normalizer_eq_centralizer_of_card_eq_two {V₁ : Subgroup G} (h : Nat.card V₁ = 2) :
    Subgroup.normalizer (V₁ : Set G) = Subgroup.centralizer (V₁ : Set G) := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    by_cases hv1 : v = 1
    · subst hv1; simp
    · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥V₁)).mp h
      have hgv : g * v * g⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp hg v).mp hv
      have h1 : (⟨v, hv⟩ : V₁) = y := huniq _ (fun e => hv1 (by simpa using congrArg Subtype.val e))
      have h2 : (⟨g * v * g⁻¹, hgv⟩ : V₁) = y := huniq _ (fun e => hv1 (by
        have := congrArg Subtype.val e
        have e2 : g * v * g⁻¹ = 1 := by simpa using this
        have := congrArg (fun x => g⁻¹ * x * g) e2
        simpa [mul_assoc] using this))
      have h3 : g * v * g⁻¹ = v := by
        have := congrArg Subtype.val (h2.trans h1.symm)
        simpa using this
      have : g * v = v * g := by rw [mul_inv_eq_iff_eq_mul] at h3; exact h3
      exact this.symm
  · exact Subgroup.centralizer_le_normalizer _

theorem L₁Of_eq_oTwoRes_centralizer (L : Subgroup G) {V₁ : Subgroup G} (h : Nat.card V₁ = 2) :
    L₁Of L V₁ = oTwoRes (L ⊓ Subgroup.centralizer (V₁ : Set G)) := by
  unfold L₁Of
  rw [normalizer_eq_centralizer_of_card_eq_two h]

structure HypF91 (T V L V₁ Vp H : Subgroup G) : Prop where
  sylow : IsSylowTwoOf T ⊤
  elemAbelian : IsElemAbelian 2 V
  normalizes_L : T ≤ Subgroup.normalizer (L : Set G)
  oTwoRes_eq : oTwoRes L = L
  charTwo_L : CharTwo L
  reduced : IsTwoReducedIn (L ⊔ T) V
  cT : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T)
  card_V₁ : Nat.card V₁ = 2
  V₁_lt_Vp : V₁ < Vp
  Vp_le_V : Vp ≤ V
  T_normalizes_V₁ : T ≤ Subgroup.normalizer (V₁ : Set G)
  H_le_centralizer : H ≤ Subgroup.centralizer (V₁ : Set G)
  L₁T_le_H : L₁Of L V₁ ⊔ T ≤ H
  charTwo_H : CharTwo H
  ker_le : coreIn (centralizerMod V₁ H Vp) H ≤ pCoreOf 2 H
  L₁T_normalizes_Vp : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (Vp : Set G)
  irred : ∀ W : Subgroup G, V₁ ≤ W → W ≤ Vp → L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (W : Set G) →
    W = V₁ ∨ W = Vp
  normalizer_le : H ⊓ Subgroup.normalizer (Vp : Set G) ≤ Subgroup.normalizer (V : Set G)
  o2_trivial : pCoreOf 2 ((L ⊔ T) ⊔ H) = ⊥
  weak_e : ∀ g ∈ H, ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V → ⁅Vp, conjSub g⁻¹ V⁆ ≤ V₁ →
    ⁅conjSub g⁻¹ Vp, V⁆ ≤ V₁ → ⁅Vp, conjSub g⁻¹ V⁆ = ⊥ ∧ ⁅conjSub g⁻¹ Vp, V⁆ = ⊥

namespace HypF91

variable {T V L V₁ Vp H : Subgroup G}

theorem V₁_le_Vp (h : HypF91 T V L V₁ Vp H) : V₁ ≤ Vp := h.V₁_lt_Vp.le

theorem V₁_le_V (h : HypF91 T V L V₁ Vp H) : V₁ ≤ V := h.V₁_le_Vp.trans h.Vp_le_V

theorem V₁_ne_bot (h : HypF91 T V L V₁ Vp H) : V₁ ≠ ⊥ := by
  intro hbot
  have := h.card_V₁
  rw [hbot] at this
  simp at this

theorem elemAbelian_Vp (h : HypF91 T V L V₁ Vp H) : IsElemAbelian 2 Vp :=
  isElemAbelian_mono h.elemAbelian h.Vp_le_V

theorem isPGroup_V (h : HypF91 T V L V₁ Vp H) : IsPGroup 2 V :=
  isPGroup_of_isElemAbelian h.elemAbelian

theorem isPGroup_Vp (h : HypF91 T V L V₁ Vp H) : IsPGroup 2 Vp :=
  isPGroup_of_isElemAbelian h.elemAbelian_Vp

theorem V_le_pCoreOf_LT (h : HypF91 T V L V₁ Vp H) : V ≤ pCoreOf 2 (L ⊔ T) :=
  le_pCoreOf_of_le_normalizer 2 h.reduced.1 h.reduced.2.1 h.isPGroup_V

theorem V_le_T (h : HypF91 T V L V₁ Vp H) : V ≤ T := by
  have := h.V_le_pCoreOf_LT
  rw [← h.cT] at this
  exact this.trans inf_le_left

theorem Vp_le_T (h : HypF91 T V L V₁ Vp H) : Vp ≤ T := h.Vp_le_V.trans h.V_le_T

theorem T_le_H (h : HypF91 T V L V₁ Vp H) : T ≤ H := le_sup_right.trans h.L₁T_le_H

theorem V_le_H (h : HypF91 T V L V₁ Vp H) : V ≤ H := h.V_le_T.trans h.T_le_H

theorem Vp_le_H (h : HypF91 T V L V₁ Vp H) : Vp ≤ H := h.Vp_le_T.trans h.T_le_H

theorem sylow_H (h : HypF91 T V L V₁ Vp H) : IsSylowTwoOf T H :=
  isSylowTwoOf_mono_right h.sylow h.T_le_H le_top

theorem sylow_LT (h : HypF91 T V L V₁ Vp H) : IsSylowTwoOf T (L ⊔ T) :=
  isSylowTwoOf_mono_right h.sylow le_sup_right le_top

theorem H_normalizes_V₁ (h : HypF91 T V L V₁ Vp H) : H ≤ Subgroup.normalizer (V₁ : Set G) := by
  rw [normalizer_eq_centralizer_of_card_eq_two h.card_V₁]
  exact h.H_le_centralizer

theorem T_normalizes_Vp (h : HypF91 T V L V₁ Vp H) : T ≤ Subgroup.normalizer (Vp : Set G) :=
  le_sup_right.trans h.L₁T_normalizes_Vp

theorem T_normalizes_V (h : HypF91 T V L V₁ Vp H) : T ≤ Subgroup.normalizer (V : Set G) :=
  le_sup_right.trans h.reduced.2.1

theorem L₁T_normalizes_V (h : HypF91 T V L V₁ Vp H) :
    L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
  (L₁Of_sup_le L V₁ T).trans h.reduced.2.1

theorem V₁_le_pCoreOf (h : HypF91 T V L V₁ Vp H) : V₁ ≤ pCoreOf 2 H :=
  le_pCoreOf_of_le_normalizer 2 (h.V₁_le_V.trans h.V_le_H) h.H_normalizes_V₁
    (h.isPGroup_V.to_le h.V₁_le_V)

end HypF91

section F92

variable [Finite G]

namespace HypF91

variable {T V L V₁ Vp H : Subgroup G}

theorem Vp_le_pCoreOf_and_commutator_le (h : HypF91 T V L V₁ Vp H) :
    Vp ≤ pCoreOf 2 H ∧ ∀ v ∈ Vp, ∀ q ∈ pCoreOf 2 H, v * q * v⁻¹ * q⁻¹ ∈ V₁ :=
  CFSG.Quasithin.V_le_pCoreOf_and_commutator_le h.sylow_H h.Vp_le_T h.elemAbelian_Vp h.V₁_le_Vp
    h.T_normalizes_V₁ h.T_normalizes_Vp h.H_normalizes_V₁ h.charTwo_H h.L₁T_le_H
    h.L₁T_normalizes_Vp h.irred

theorem conjClosure_Vp_le_pCoreOf (h : HypF91 T V L V₁ Vp H) : conjClosure Vp H ≤ pCoreOf 2 H := by
  obtain ⟨hVQ, -⟩ := h.Vp_le_pCoreOf_and_commutator_le
  refine conjClosure_le fun x hx v hv => ?_
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hx) v).mp (hVQ hv)

theorem commutator_conjClosure_le (h : HypF91 T V L V₁ Vp H) :
    ∀ u ∈ conjClosure Vp H, ∀ q ∈ pCoreOf 2 H, u * q * u⁻¹ * q⁻¹ ∈ V₁ := by
  obtain ⟨-, hcomm⟩ := h.Vp_le_pCoreOf_and_commutator_le
  have hQN := le_normalizer_pCoreOf 2 H
  have hHC : H ≤ Subgroup.normalizer (centralizerMod V₁ ⊤ (pCoreOf 2 H) : Set G) :=
    le_normalizer_centralizerMod h.H_normalizes_V₁ (fun x _ => by
      rw [Subgroup.mem_normalizer_iff]; intro y; simp) hQN
  have : conjClosure Vp H ≤ centralizerMod V₁ ⊤ (pCoreOf 2 H) := by
    refine conjClosure_le fun x hx v hv => ?_
    have hvC : v ∈ centralizerMod V₁ ⊤ (pCoreOf 2 H) :=
      ⟨Subgroup.mem_top _, h.T_normalizes_V₁ (h.Vp_le_T hv), fun q hq => hcomm v hv q hq⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHC hx) v).mp hvC
  exact fun u hu q hq => (this hu).2.2 q hq

theorem sq_mem_conjClosure (h : HypF91 T V L V₁ Vp H) : ∀ u ∈ conjClosure Vp H, u ^ 2 ∈ V₁ := by
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hcomm := h.commutator_conjClosure_le
  intro u hu
  have hu' : u ∈ Subgroup.closure {x | ∃ k ∈ H, ∃ z ∈ Vp, k * z * k⁻¹ = x} := hu
  clear hu
  induction hu' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, z, hz, rfl⟩ := hx
    have e : (k * z * k⁻¹) ^ 2 = k * z ^ 2 * k⁻¹ := conj_pow
    rw [e, isElemAbelian_pow_eq_one h.elemAbelian_Vp hz]
    simp
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxU : x ∈ conjClosure Vp H := hx
    have hyU : y ∈ conjClosure Vp H := hy
    have hc : y * x * y⁻¹ * x⁻¹ ∈ V₁ := hcomm y hyU x (hUQ hxU)
    have hxN : x ∈ Subgroup.normalizer (V₁ : Set G) :=
      h.H_normalizes_V₁ (pCoreOf_le 2 H (hUQ hxU))
    have h1 : x * (y * x * y⁻¹ * x⁻¹) * x⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp hxN _).mp hc
    have e : (x * y) ^ 2 = (x * (y * x * y⁻¹ * x⁻¹) * x⁻¹) * x ^ 2 * y ^ 2 := by
      rw [pow_two]; group
    rw [e]
    exact V₁.mul_mem (V₁.mul_mem h1 ihx) ihy
  | inv x hx ih =>
    rw [inv_pow]
    exact V₁.inv_mem ih

theorem F92_1 (h : HypF91 T V L V₁ Vp H) :
    conjClosure Vp H ≤ pCoreOf 2 H ∧
      (∀ u ∈ conjClosure Vp H, ∀ q ∈ pCoreOf 2 H, u * q * u⁻¹ * q⁻¹ ∈ V₁) ∧
      ∀ u ∈ conjClosure Vp H, u ^ 2 ∈ V₁ :=
  ⟨h.conjClosure_Vp_le_pCoreOf, h.commutator_conjClosure_le, h.sq_mem_conjClosure⟩

theorem isPGroup_conjClosure (h : HypF91 T V L V₁ Vp H) : IsPGroup 2 (conjClosure Vp H) :=
  (pCoreOf_isPGroup 2 H).to_le h.conjClosure_Vp_le_pCoreOf

theorem F92_2 (h : HypF91 T V L V₁ Vp H) :
    (frattini (conjClosure Vp H)).map (conjClosure Vp H).subtype ≤ V₁ :=
  frattini_map_le_of_forall h.isPGroup_conjClosure
    (fun x hx y hy => h.commutator_conjClosure_le x hx y (h.conjClosure_Vp_le_pCoreOf hy))
    h.sq_mem_conjClosure

theorem pCoreOf_eq_centralizerMod (h : HypF91 T V L V₁ Vp H) :
    pCoreOf 2 H = centralizerMod V₁ H (conjClosure Vp H) := by
  apply le_antisymm
  · intro q hq
    refine ⟨pCoreOf_le 2 H hq, h.H_normalizes_V₁ (pCoreOf_le 2 H hq), fun u hu => ?_⟩
    have := V₁.inv_mem (h.commutator_conjClosure_le u hu q hq)
    have e : (u * q * u⁻¹ * q⁻¹)⁻¹ = q * u * q⁻¹ * u⁻¹ := by group
    rwa [e] at this
  · have hHC : H ≤ Subgroup.normalizer (centralizerMod V₁ H (conjClosure Vp H) : Set G) :=
      le_normalizer_centralizerMod h.H_normalizes_V₁ Subgroup.le_normalizer
        (le_normalizer_conjClosure Vp H)
    have hle : centralizerMod V₁ H (conjClosure Vp H) ≤ coreIn (centralizerMod V₁ H Vp) H :=
      le_coreIn (centralizerMod_le_left _ _ _) hHC
        (centralizerMod_anti_right H (le_conjClosure Vp H))
    exact hle.trans h.ker_le

omit [Finite G] in
theorem centralizerMod_le_normalizer_Vp (h : HypF91 T V L V₁ Vp H) :
    centralizerMod V₁ H Vp ≤ H ⊓ Subgroup.normalizer (Vp : Set G) := by
  intro x hx
  have key : ∀ y ∈ centralizerMod V₁ H Vp, ∀ v ∈ Vp, y * v * y⁻¹ ∈ Vp := by
    intro y hy v hv
    have h1 := hy.2.2 v hv
    have e : y * v * y⁻¹ = (y * v * y⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact Vp.mul_mem (h.V₁_le_Vp h1) hv
  refine ⟨hx.1, Subgroup.mem_normalizer_iff.mpr fun v => ⟨key x hx v, fun hv => ?_⟩⟩
  have := key x⁻¹ ((centralizerMod V₁ H Vp).inv_mem hx) _ hv
  simpa [mul_assoc] using this

theorem F92_3 (h : HypF91 T V L V₁ Vp H) :
    pCoreOf 2 H = centralizerMod V₁ H (conjClosure Vp H) ∧
      centralizerMod V₁ H (conjClosure Vp H) ≤ centralizerMod V₁ H Vp ∧
      centralizerMod V₁ H Vp ≤ H ⊓ Subgroup.normalizer (V : Set G) :=
  ⟨h.pCoreOf_eq_centralizerMod, centralizerMod_anti_right H (le_conjClosure Vp H),
    fun _ hx => ⟨hx.1, h.normalizer_le (h.centralizerMod_le_normalizer_Vp hx)⟩⟩


theorem F92_1_reduced (h : HypF91 T V L V₁ Vp H) {D : Subgroup G} (hDH : D ≤ H)
    (hHD : H ≤ Subgroup.normalizer (D : Set G))
    (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ centralizerMod V₁ H (conjClosure Vp H)) :
    D ≤ centralizerMod V₁ H (conjClosure Vp H) := by
  have htop : ∀ K : Subgroup G, K ≤ Subgroup.normalizer ((⊤ : Subgroup G) : Set G) :=
    fun K x _ => by rw [Subgroup.mem_normalizer_iff]; intro y; simp
  have hHC : H ≤ Subgroup.normalizer (centralizerMod V₁ H (conjClosure Vp H) : Set G) :=
    le_normalizer_centralizerMod h.H_normalizes_V₁ Subgroup.le_normalizer
      (le_normalizer_conjClosure Vp H)
  have hXH : L₁Of L V₁ ⊔ T ≤ H := h.L₁T_le_H
  have hXV : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (Vp : Set G) := h.L₁T_normalizes_Vp
  have hXV₁ : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (V₁ : Set G) := hXH.trans h.H_normalizes_V₁
  have hW : Vp ≤ conjClosure (Vp ⊓ centralizerMod V₁ ⊤ T) (L₁Of L V₁ ⊔ T) ⊔ V₁ := by
    have hWV : conjClosure (Vp ⊓ centralizerMod V₁ ⊤ T) (L₁Of L V₁ ⊔ T) ⊔ V₁ ≤ Vp :=
      sup_le (conjClosure_le fun x hx z hz =>
        (Subgroup.mem_normalizer_iff.mp (hXV hx) z).mp hz.1) h.V₁_le_Vp
    have hXW : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer
        ((conjClosure (Vp ⊓ centralizerMod V₁ ⊤ T) (L₁Of L V₁ ⊔ T) ⊔ V₁ : Subgroup G) : Set G) :=
      (le_inf (le_normalizer_conjClosure _ _) hXV₁).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    by_cases hEq : V₁ = Vp
    · exact hEq ▸ le_sup_right
    · have hlt := lt_of_le_of_ne h.V₁_le_Vp hEq
      obtain ⟨z, hzV, hzV₁, hz⟩ := exists_fixed_mod h.sylow.2.1 h.Vp_le_T hlt h.T_normalizes_Vp
        h.T_normalizes_V₁
      have hzZ : z ∈ Vp ⊓ centralizerMod V₁ ⊤ T :=
        ⟨hzV, Subgroup.mem_top _, h.T_normalizes_V₁ (h.Vp_le_T hzV), fun t ht => by
          have := V₁.inv_mem (hz t ht)
          have e : (t * z * t⁻¹ * z⁻¹)⁻¹ = z * t * z⁻¹ * t⁻¹ := by group
          rwa [e] at this⟩
      rcases h.irred _ le_sup_right hWV hXW with hEq' | hEq'
      · exact absurd (hEq' ▸ Subgroup.mem_sup_left (le_conjClosure _ _ hzZ)) hzV₁
      · exact hEq'.symm.le
  have hDsyl : IsSylowTwoOf (T ⊓ D) D :=
    isSylowTwoOf_inf_normal h.sylow_H hDH (h.T_le_H.trans hHD)
  have hDle := isSylowTwoOf_le_sup_of_two_power hDsyl (hDH.trans hHC) hD
  have hZU : Vp ⊓ centralizerMod V₁ ⊤ T ≤ conjClosure Vp H := inf_le_left.trans (le_conjClosure Vp H)
  have hC'C : centralizerMod V₁ H (conjClosure Vp H) ≤ centralizerMod V₁ ⊤ (Vp ⊓ centralizerMod V₁ ⊤ T) :=
    (centralizerMod_anti_right H hZU).trans (centralizerMod_mono_left _ le_top)
  have hC'T : T ⊓ D ≤ centralizerMod V₁ ⊤ (Vp ⊓ centralizerMod V₁ ⊤ T) := by
    rintro t ⟨ht, -⟩
    refine ⟨Subgroup.mem_top _, h.T_normalizes_V₁ ht, fun z hz => ?_⟩
    have := V₁.inv_mem (hz.2.2.2 t ht)
    have e : (z * t * z⁻¹ * t⁻¹)⁻¹ = t * z * t⁻¹ * z⁻¹ := by group
    rwa [e] at this
  have hDC' : D ≤ centralizerMod V₁ ⊤ (Vp ⊓ centralizerMod V₁ ⊤ T) :=
    hDle.trans (sup_le hC'C hC'T)
  have hSgen : conjClosure (Vp ⊓ centralizerMod V₁ ⊤ T) (L₁Of L V₁ ⊔ T) ≤
      centralizerMod V₁ ⊤ D := by
    refine conjClosure_le fun x hx z hz => ?_
    refine ⟨Subgroup.mem_top _, ?_, fun d hd => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hXV₁ hx) hz.2.2.1)
        (Subgroup.inv_mem _ (hXV₁ hx))
    · have hd' : x⁻¹ * d * x⁻¹⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (hHD (H.inv_mem (hXH hx))) d).mp hd
      have h1 := (hDC' hd').2.2 z hz
      have h2 : x * ((x⁻¹ * d * x⁻¹⁻¹) * z * (x⁻¹ * d * x⁻¹⁻¹)⁻¹ * z⁻¹) * x⁻¹ ∈ V₁ :=
        (Subgroup.mem_normalizer_iff.mp (hXV₁ hx) _).mp h1
      have h3 := V₁.inv_mem h2
      have e : (x * ((x⁻¹ * d * x⁻¹⁻¹) * z * (x⁻¹ * d * x⁻¹⁻¹)⁻¹ * z⁻¹) * x⁻¹)⁻¹ =
          (x * z * x⁻¹) * d * (x * z * x⁻¹)⁻¹ * d⁻¹ := by group
      rwa [e] at h3
  have hV₁S : V₁ ≤ centralizerMod V₁ ⊤ D := by
    intro v hv
    refine ⟨Subgroup.mem_top _, Subgroup.le_normalizer hv, fun d hd => ?_⟩
    have h1 : d * v⁻¹ * d⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (h.H_normalizes_V₁ (hDH hd)) v⁻¹).mp (V₁.inv_mem hv)
    have e : v * d * v⁻¹ * d⁻¹ = v * (d * v⁻¹ * d⁻¹) := by group
    rw [e]; exact V₁.mul_mem hv h1
  have hVS : Vp ≤ centralizerMod V₁ ⊤ D := hW.trans (sup_le hSgen hV₁S)
  have hHS : H ≤ Subgroup.normalizer (centralizerMod V₁ ⊤ D : Set G) :=
    le_normalizer_centralizerMod h.H_normalizes_V₁ (htop H) hHD
  have hUS : conjClosure Vp H ≤ centralizerMod V₁ ⊤ D :=
    conjClosure_le fun x hx v hv => (Subgroup.mem_normalizer_iff.mp (hHS hx) v).mp (hVS hv)
  intro d hd
  refine ⟨hDH hd, h.H_normalizes_V₁ (hDH hd), fun u hu => ?_⟩
  have := V₁.inv_mem ((hUS hu).2.2 d hd)
  have e : (u * d * u⁻¹ * d⁻¹)⁻¹ = d * u * d⁻¹ * u⁻¹ := by group
  rwa [e] at this

theorem charTwo_LT (h : HypF91 T V L V₁ Vp H) : CharTwo (L ⊔ T) :=
  charTwo_sup_of_normalizes h.sylow.2.1 h.normalizes_L h.charTwo_L

theorem pCoreOf_LT_eq (h : HypF91 T V L V₁ Vp H) :
    pCoreOf 2 (L ⊔ T) = pCoreOf 2 ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
  have h1 : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) := by
    refine h.reduced.2.2.2 (pCoreOf 2 (L ⊔ T)) (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _) ?_
    intro d hd
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (L ⊔ T) ⟨d, hd⟩
    have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact ⟨k, by rw [this]; exact Subgroup.one_mem _⟩
  apply le_antisymm
  · exact le_pCoreOf_of_le_normalizer 2 (le_inf (pCoreOf_le 2 _) h1)
      (inf_le_left.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  · exact pCoreOf_mono_of_le_normalizer inf_le_left
      (le_normalizer_inf Subgroup.le_normalizer
        (h.reduced.2.1.trans (normalizer_le_normalizer_centralizer V)))

theorem amalgamHypV (h : HypF91 T V L V₁ Vp H) : AmalgamHypV ((L ⊔ T) ⊔ H) (L ⊔ T) H T V :=
  { gen := rfl
    charTwo := h.charTwo_LT
    sylow₁ := h.sylow_LT
    sylow₂ := h.sylow_H
    o2_trivial := h.o2_trivial
    reduced := h.reduced
    cT := h.cT.trans h.pCoreOf_LT_eq }

theorem LT_inf_H (h : HypF91 T V L V₁ Vp H) : (L ⊔ T) ⊓ H = L₁Of L V₁ ⊔ T := by
  apply le_antisymm
  · rintro x ⟨hxLT, hxH⟩
    have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * T :=
      Subgroup.coe_mul_of_right_le_normalizer_left L T h.normalizes_L
    obtain ⟨l, hl, t, ht, rfl⟩ : x ∈ (L : Set G) * T := by rw [← hmul]; exact hxLT
    have hlN : l ∈ Subgroup.normalizer (V₁ : Set G) := by
      have := Subgroup.mul_mem _ (h.H_normalizes_V₁ hxH)
        (Subgroup.inv_mem _ (h.T_normalizes_V₁ ht))
      simpa using this
    have hsyl : IsSylowTwoOf (T ⊓ L) (L ⊓ Subgroup.normalizer (V₁ : Set G)) :=
      isSylowTwoOf_mono_right (isSylowTwoOf_inf_normal h.sylow (le_top : L ≤ ⊤) h.normalizes_L)
        (le_inf inf_le_right (inf_le_left.trans h.T_normalizes_V₁)) inf_le_left
    have hl' := le_oTwoRes_sup_of_isSylowTwoOf hsyl ⟨hl, hlN⟩
    have hle : oTwoRes (L ⊓ Subgroup.normalizer (V₁ : Set G)) ⊔ (T ⊓ L) ≤ L₁Of L V₁ ⊔ T :=
      sup_le_sup le_rfl inf_le_left
    exact Subgroup.mul_mem _ (hle hl') (le_sup_right (a := L₁Of L V₁) ht)
  · exact le_inf (L₁Of_sup_le L V₁ T) h.L₁T_le_H

omit [Finite G] in
theorem conjSub_le_conjClosure {Z H : Subgroup G} {k : G} (hk : k ∈ H) :
    conjSub k Z ≤ conjClosure Z H := by
  intro x hx
  rw [mem_conjSub] at hx
  have := mem_conjClosure hk hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem le_normalizer_of_isElemAbelian_le {V V₁ : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : V₁ ≤ V) : V ≤ Subgroup.normalizer (V₁ : Set G) := by
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have key : ∀ y ∈ V₁, v * y * v⁻¹ = y := fun y hy => by
    have := isElemAbelian_comm hV hv (h hy)
    rw [this]; group
  constructor
  · intro hy; rw [key y hy]; exact hy
  · intro hy
    have hm := isElemAbelian_comm hV hv (h hy)
    have e : v * y * v⁻¹ = y := by
      calc v * y * v⁻¹ = v⁻¹ * (v * (v * y * v⁻¹)) := by group
        _ = v⁻¹ * ((v * y * v⁻¹) * v) := by rw [hm]
        _ = y := by group
    rw [e] at hy
    exact hy

omit [Finite G] in
theorem conjSub_le_pCoreOf (_h : HypF91 T V L V₁ Vp H) (hVQ : V ≤ pCoreOf 2 H) {k : G}
    (hk : k ∈ H) : conjSub k V ≤ pCoreOf 2 H := by
  have hkQ : conjSub k (pCoreOf 2 H) = pCoreOf 2 H :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hk)
  have := conjSub_mono k hVQ
  rwa [hkQ] at this

omit [Finite G] in
theorem V_le_normalizer_V₁ (h : HypF91 T V L V₁ Vp H) : V ≤ Subgroup.normalizer (V₁ : Set G) :=
  le_normalizer_of_isElemAbelian_le h.elemAbelian h.V₁_le_V

theorem commutator_conjSub_le_of_le_pCoreOf (h : HypF91 T V L V₁ Vp H) (hVQ : V ≤ pCoreOf 2 H)
    {k : G} (hk : k ∈ H) : ⁅V, conjSub k V⁆ ≤ V ⊓ conjSub k V := by
  have hQT := isSylowTwoOf_pCoreOf_le h.sylow_H
  have hVk : conjSub k V ≤ pCoreOf 2 H := h.conjSub_le_pCoreOf hVQ hk
  have hSyl : IsSylowTwoOf (conjSub k T) H := by
    have := isSylowTwoOf_conj h.sylow_H k
    rwa [F7.conjSub_eq_of_mem hk] at this
  have hQTk := isSylowTwoOf_pCoreOf_le hSyl
  refine commutator_le_inf_of_normalizes ?_ ?_
  · exact hVQ.trans (hQTk.trans (conjSub_le_normalizer h.T_normalizes_V))
  · exact hVk.trans (hQT.trans h.T_normalizes_V)

theorem F93 (h : HypF91 T V L V₁ Vp H) :
    List.TFAE [V ≤ pCoreOf 2 H, V ≤ H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G),
      V ≤ centralizerMod V₁ H (conjClosure Vp H)] := by
  have hQ := h.pCoreOf_eq_centralizerMod
  have hcomm := h.commutator_conjClosure_le
  tfae_have 1 ↔ 3 := by rw [hQ]
  tfae_have 2 → 3 := by
    intro hV v hv
    refine ⟨(hV hv).1, h.V_le_normalizer_V₁ hv, fun u hu => ?_⟩
    have hc := Subgroup.mem_centralizer_iff.mp (hV hv).2 u hu
    have e : v * u * v⁻¹ * u⁻¹ = 1 := by rw [← hc]; group
    rw [e]
    exact V₁.one_mem
  tfae_have 1 → 2 := by
    intro hVQ
    have key : ∀ k ∈ H, conjSub k Vp ≤ Subgroup.centralizer (V : Set G) := by
      intro k hk
      have hg := h.weak_e k⁻¹ (H.inv_mem hk)
      simp only [inv_inv] at hg
      have h1 := h.commutator_conjSub_le_of_le_pCoreOf hVQ hk
      have h2 : ⁅Vp, conjSub k V⁆ ≤ V₁ := by
        refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
        exact hcomm x (le_conjClosure Vp H hx) y (h.conjSub_le_pCoreOf hVQ hk hy)
      have h3 : ⁅conjSub k Vp, V⁆ ≤ V₁ := by
        refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
        exact hcomm x (conjSub_le_conjClosure hk hx) y (hVQ hy)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hg h1 h2 h3).2
    have hUC : conjClosure Vp H ≤ Subgroup.centralizer (V : Set G) :=
      conjClosure_le fun k hk z hz => key k hk (mul_mem_conjSub hz)
    have hbot : ⁅conjClosure Vp H, V⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUC
    rw [Subgroup.commutator_comm] at hbot
    exact fun v hv => ⟨h.V_le_H hv, Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hv⟩
  tfae_finish

theorem le_pCoreOf_iff_le_centralizer (h : HypF91 T V L V₁ Vp H) :
    V ≤ pCoreOf 2 H ↔ V ≤ H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G) :=
  h.F93.out 1 2

theorem le_pCoreOf_iff_le_centralizerMod (h : HypF91 T V L V₁ Vp H) :
    V ≤ pCoreOf 2 H ↔ V ≤ centralizerMod V₁ H (conjClosure Vp H) :=
  h.F93.out 1 3

omit [Finite G] in
theorem isElemAbelian_conjClosure_of_forall {Z H : Subgroup G} (hZ : IsElemAbelian 2 Z)
    (hH : ∀ k ∈ H, Z ≤ Subgroup.centralizer (conjSub k Z : Set G)) :
    IsElemAbelian 2 (conjClosure Z H) := by
  rw [conjClosure]
  refine F7.isElemAbelian_closure _ ?_ ?_
  · rintro _ ⟨k, hk, z, hz, rfl⟩ _ ⟨k', hk', z', hz', rfl⟩
    obtain ⟨m, hmH, rfl⟩ : ∃ m ∈ H, k = k' * m :=
      ⟨k'⁻¹ * k, H.mul_mem (H.inv_mem hk') hk, by group⟩
    have hc := Subgroup.mem_centralizer_iff.mp (hH m hmH hz') (m * z * m⁻¹) (mul_mem_conjSub hz)
    calc k' * m * z * (k' * m)⁻¹ * (k' * z' * k'⁻¹)
        = k' * ((m * z * m⁻¹) * z') * k'⁻¹ := by group
      _ = k' * (z' * (m * z * m⁻¹)) * k'⁻¹ := by rw [hc]
      _ = k' * z' * k'⁻¹ * (k' * m * z * (k' * m)⁻¹) := by group
  · rintro _ ⟨k, hk, z, hz, rfl⟩
    have e : (k * z * k⁻¹) ^ 2 = k * z ^ 2 * k⁻¹ := conj_pow
    rw [e, isElemAbelian_pow_eq_one hZ hz]
    simp

omit [Finite G] in
theorem isElemAbelian_conjClosure_of_le_centralizer (h : HypF91 T V L V₁ Vp H)
    (hV : V ≤ H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G)) :
    IsElemAbelian 2 (conjClosure Vp H) := by
  refine isElemAbelian_conjClosure_of_forall h.elemAbelian_Vp fun k hk z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_iff.mp (hV (h.Vp_le_V hz)).2 y (conjSub_le_conjClosure hk hy)

theorem F94_1 (h : HypF91 T V L V₁ Vp H) (hV : V ≤ pCoreOf 2 H) :
    IsElemAbelian 2 (conjClosure Vp H) :=
  h.isElemAbelian_conjClosure_of_le_centralizer (h.le_pCoreOf_iff_le_centralizer.mp hV)

theorem F94_2 (h : HypF91 T V L V₁ Vp H)
    (hcomm : ⁅V, (H ⊓ Subgroup.centralizer (Vp : Set G)) ⊓
      (H ⊓ Subgroup.normalizer (V : Set G))⁆ ≤ V₁)
    (hab : ∀ x ∈ conjClosure Vp H, ∀ y ∈ conjClosure Vp H, x * y = y * x) :
    V ≤ pCoreOf 2 H := by
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hU : conjClosure Vp H ≤ (H ⊓ Subgroup.centralizer (Vp : Set G)) ⊓
      (H ⊓ Subgroup.normalizer (V : Set G)) := by
    intro u hu
    refine ⟨⟨pCoreOf_le 2 H (hUQ hu), Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩,
      pCoreOf_le 2 H (hUQ hu), ?_⟩
    · exact hab z (le_conjClosure Vp H hz) u hu
    · have hq : u ∈ centralizerMod V₁ H Vp :=
        h.F92_3.2.1 (h.pCoreOf_eq_centralizerMod ▸ hUQ hu)
      exact (h.F92_3.2.2 hq).2
  have hVC : V ≤ centralizerMod V₁ H (conjClosure Vp H) := by
    intro v hv
    refine ⟨h.V_le_H hv, h.V_le_normalizer_V₁ hv, fun u hu => ?_⟩
    have hc := hcomm (Subgroup.commutator_mem_commutator hv (hU hu))
    exact hc
  exact h.le_pCoreOf_iff_le_centralizerMod.mpr hVC

theorem F94_3 (h : HypF91 T V L V₁ Vp H)
    (hC : (H ⊓ Subgroup.centralizer (Vp : Set G)) ⊓ (H ⊓ Subgroup.normalizer (V : Set G)) =
      H ⊓ Subgroup.centralizer (V : Set G)) :
    List.TFAE [V ≤ pCoreOf 2 H, IsElemAbelian 2 (conjClosure Vp H),
      IsElemAbelian 2 (conjClosure V H)] := by
  have hUV : conjClosure Vp H ≤ conjClosure V H :=
    conjClosure_le fun k hk z hz => mem_conjClosure hk (h.Vp_le_V hz)
  have hC' : H ⊓ Subgroup.centralizer (Vp : Set G) = H ⊓ Subgroup.centralizer (V : Set G) := by
    rw [← hC]
    exact (inf_eq_left.mpr fun x hx =>
      ⟨hx.1, h.normalizer_le ⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩⟩).symm
  tfae_have 1 → 2 := h.F94_1
  tfae_have 3 → 1 := by
    intro hVH
    refine h.le_pCoreOf_iff_le_centralizer.mpr fun v hv => ⟨h.V_le_H hv, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    exact (isElemAbelian_comm hVH (hUV hu) (le_conjClosure V H hv))
  tfae_have 2 → 3 := by
    intro hUel
    refine isElemAbelian_conjClosure_of_forall h.elemAbelian fun k hk v hv => ?_
    have hVp : conjSub k Vp ≤ H ⊓ Subgroup.centralizer (Vp : Set G) := by
      refine fun y hy => ⟨?_, ?_⟩
      · have := conjSub_le_conjClosure (Z := Vp) hk hy
        exact pCoreOf_le 2 H (h.conjClosure_Vp_le_pCoreOf this)
      · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
        exact isElemAbelian_comm hUel (le_conjClosure Vp H hz) (conjSub_le_conjClosure hk hy)
    have hV1 : conjSub k Vp ≤ Subgroup.centralizer (V : Set G) := fun y hy => (hC' ▸ hVp hy).2
    have hVk : V ≤ H ⊓ Subgroup.centralizer (conjSub k Vp : Set G) := by
      refine fun x hx => ⟨h.V_le_H hx, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact (Subgroup.mem_centralizer_iff.mp (hV1 hy) x hx).symm
    have hconj : H ⊓ Subgroup.centralizer (conjSub k Vp : Set G) =
        H ⊓ Subgroup.centralizer (conjSub k V : Set G) := by
      have := congrArg (conjSub k) hC'
      rw [conjSub_inf, conjSub_inf, F7.conjSub_eq_of_mem hk, ← conjSub_centralizer,
        ← conjSub_centralizer] at this
      exact this
    exact (hconj ▸ hVk hv).2
  tfae_finish

end HypF91

end F92

structure HypF98 (T V L V₁ Vp H : Subgroup G) : Prop extends HypF91 T V L V₁ Vp H where
  weak_f : ∀ g : G, V₁ ≤ conjSub g⁻¹ V → ⁅V, conjSub g⁻¹ V⁆ = ⊥
  case_g : ⁅V, H ⊓ Subgroup.centralizer (Vp : Set G)⁆ ≤ V₁ ∨
    ∀ x ∈ H ⊓ Subgroup.centralizer (Vp : Set G), ⁅V, Subgroup.zpowers x⁆ ≠ ⊥ →
      ∀ g : G, conjSub g⁻¹ V ≤ Subgroup.normalizer ((⁅V, Subgroup.zpowers x⁆ : Subgroup G) : Set G) →
        conjSub g⁻¹ V ≤ Subgroup.centralizer (V : Set G)

theorem le_of_card_eq_two_of_inf_ne_bot {V₁ X : Subgroup G} (h : Nat.card V₁ = 2)
    (hne : V₁ ⊓ X ≠ ⊥) : V₁ ≤ X := by
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥V₁)).mp h
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]; exact X.one_mem
  · have h1 : (⟨v, hv⟩ : V₁) = y := huniq _ (fun e => hv1 (by simpa using congrArg Subtype.val e))
    have h2 : (⟨x, hx.1⟩ : V₁) = y := huniq _ (fun e => hx1 (by
      apply Subtype.ext; simpa using congrArg Subtype.val e))
    have : v = x := by
      have := congrArg Subtype.val (h1.trans h2.symm)
      simpa using this
    rw [this]; exact hx.2

section F99

variable {T V L V₁ Vp H : Subgroup G}

theorem HypF81.toHypF98 [Finite G] (h : HypF81 T V L V₁ H) (hc : Nat.card V₁ = 2) :
    HypF98 T V L V₁ V H := by
  have hV₁ : V₁ ≠ ⊥ := h.V₁_ne_bot
  refine
    { sylow := h.sylow, elemAbelian := h.elemAbelian, normalizes_L := h.normalizes_L,
      oTwoRes_eq := h.oTwoRes_eq, charTwo_L := h.charTwo_L, reduced := h.reduced, cT := h.cT,
      card_V₁ := hc, V₁_lt_Vp := h.V₁_lt_V, Vp_le_V := le_rfl,
      T_normalizes_V₁ := h.T_normalizes_V₁,
      H_le_centralizer := by
        rw [← normalizer_eq_centralizer_of_card_eq_two hc]; exact h.H_normalizes_V₁,
      L₁T_le_H := h.L₁T_le_H, charTwo_H := h.charTwo_H, ker_le := h.ker_le,
      L₁T_normalizes_Vp := h.L₁T_normalizes_V, irred := h.irred,
      normalizer_le := inf_le_right, o2_trivial := h.o2_trivial,
      weak_e := fun g _ hVV hVV₁ _ => ?_, weak_f := fun g hg => ?_,
      case_g := Or.inl ?_ }
  ·
    have hcomm : ⁅V, conjSub g⁻¹ V⁆ = ⊥ := by
      by_cases hb : ⁅V, conjSub g⁻¹ V⁆ = ⊥
      · exact hb
      · refine h.weak_a g fun hbot => hb ?_
        have hne : V₁ ⊓ ⁅V, conjSub g⁻¹ V⁆ ≠ ⊥ := by
          rwa [inf_eq_right.mpr hVV₁]
        have h1 : V₁ ≤ ⁅V, conjSub g⁻¹ V⁆ := le_of_card_eq_two_of_inf_ne_bot hc hne
        exfalso
        have h2 : V₁ ≤ conjSub g⁻¹ V := h1.trans (hVV.trans inf_le_right)
        rw [inf_eq_left.mpr h2] at hbot
        exact hV₁ hbot
    exact ⟨hcomm, by rw [Subgroup.commutator_comm]; exact hcomm⟩
  · exact h.weak_a g (fun hbot => hV₁ (by rwa [inf_eq_left.mpr hg] at hbot))
  · have : ⁅V, H ⊓ Subgroup.centralizer (V : Set G)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun v hv =>
        Subgroup.mem_centralizer_iff.mpr fun x hx =>
          (Subgroup.mem_centralizer_iff.mp hx.2 v hv).symm
    rw [this]; exact bot_le

theorem HypF98.toHypF81 [Finite G] (h : HypF98 T V L V₁ V H) : HypF81 T V L V₁ H :=
  { sylow := h.sylow, elemAbelian := h.elemAbelian, normalizes_L := h.normalizes_L,
    oTwoRes_eq := h.oTwoRes_eq, charTwo_L := h.charTwo_L, reduced := h.reduced, cT := h.cT,
    V₁_ne_bot := h.V₁_ne_bot, V₁_le_V := h.V₁_le_Vp, T_normalizes_V₁ := h.T_normalizes_V₁,
    weak_a := fun g hne => h.weak_f g (le_of_card_eq_two_of_inf_ne_bot h.card_V₁ hne),
    V₁_lt_V := h.V₁_lt_Vp, irred := h.irred, H_normalizes_V₁ := h.H_normalizes_V₁,
    L₁T_le_H := h.L₁T_le_H, charTwo_H := h.charTwo_H, ker_le := h.ker_le,
    o2_trivial := h.o2_trivial }

namespace HypF98

theorem eq_bot_or_eq_of_card_eq_two {A X : Subgroup G} (h : Nat.card A = 2) (hX : X ≤ A) :
    X = ⊥ ∨ X = A := by
  by_cases hb : X = ⊥
  · exact Or.inl hb
  · right
    refine le_antisymm hX (le_of_card_eq_two_of_inf_ne_bot h ?_)
    rwa [inf_eq_right.mpr hX]

theorem F911_2 (h : HypF98 T V L V₁ Vp H) : IsElemAbelian 2 (conjClosure V H) := by
  refine HypF91.isElemAbelian_conjClosure_of_forall h.elemAbelian fun k hk => ?_
  have h1 : V₁ ≤ conjSub k V := by
    rw [le_conjSub_iff, F7.conjSub_eq_of_mem_normalizer (inv_mem (h.H_normalizes_V₁ hk))]
    exact h.V₁_le_V
  have := h.weak_f k⁻¹ (by rwa [inv_inv])
  rw [inv_inv] at this
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp this

theorem F911_3 (h : HypF98 T V L V₁ Vp H) : IsElemAbelian 2 (conjClosure Vp H) :=
  isElemAbelian_mono h.F911_2 (conjClosure_le fun _ hk _ hz => mem_conjClosure hk (h.Vp_le_V hz))

end HypF98

end F99

end CFSG.Quasithin
