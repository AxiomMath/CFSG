module

public import CFSG.Quasithin.H13.A6S1384b
public import CFSG.Quasithin.H13.A6S1384a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

@[expose] def HypList : List (Perm (Fin 6)) :=
  [1, swap 3 4 * swap 4 5, swap 3 5 * swap 5 4, swap 2 3 * swap 3 4, swap 2 3 * swap 3 5,
    swap 2 4 * swap 4 3, swap 2 4 * swap 4 5, swap 2 4 * swap 3 5,
    swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5, swap 1 2 * swap 2 3 * swap 3 5 * swap 5 4,
    swap 1 2 * swap 2 4 * swap 4 3 * swap 3 5, swap 1 3 * swap 3 5 * swap 5 2 * swap 2 4,
    swap 1 4 * swap 4 5 * swap 5 3 * swap 3 2, swap 1 4 * swap 4 2,
    swap 1 4 * swap 4 3 * swap 3 5 * swap 5 2, swap 1 4 * swap 4 2 * swap 2 5 * swap 5 3,
    swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4, swap 0 1 * swap 1 2 * swap 2 3 * swap 3 5,
    swap 0 1 * swap 1 2 * swap 2 4 * swap 3 5, swap 0 1 * swap 1 3 * swap 3 5 * swap 2 4,
    swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5, swap 0 4 * swap 4 3 * swap 3 2 * swap 2 1,
    swap 0 4 * swap 4 5 * swap 5 2 * swap 2 1, swap 0 4 * swap 4 2 * swap 2 1 * swap 3 5,
    swap 0 4 * swap 4 3 * swap 3 1 * swap 2 5, swap 0 4 * swap 4 2 * swap 1 5 * swap 5 3]

theorem hypList_mem : ∀ σ ∈ HypList, σ ∈ alternatingGroup (Fin 6) := by
  intro σ hσ
  rw [Equiv.Perm.mem_alternatingGroup]
  revert σ
  decide +kernel

theorem hyp_check : ∀ c : Fin 4 → ZMod 2, c ≠ 0 → ∃ σ ∈ HypList, ∀ x : P6, InW4 x →
    (InW3 (act4f σ⁻¹ x) ↔ c 0 * Multiplicative.toAdd x 1 + c 1 * Multiplicative.toAdd x 2 +
      c 2 * Multiplicative.toAdd x 3 + c 3 * Multiplicative.toAdd x 4 = 0) := by
  decide +kernel

@[expose] def b4 : Fin 4 → P6 := ![dv 0 1, dv 0 2, dv 0 3, dv 0 4]

theorem b4_mem : ∀ i, b4 i ∈ W4 := by
  decide +kernel

@[expose] def pw4 (b : ↥W4) (s : ZMod 2) : ↥W4 := if s = 1 then b else 1

theorem w4_decomp : ∀ y : ↥W4,
    y = pw4 ⟨b4 0, b4_mem 0⟩ (Multiplicative.toAdd (y : P6) 1) *
      pw4 ⟨b4 1, b4_mem 1⟩ (Multiplicative.toAdd (y : P6) 2) *
      pw4 ⟨b4 2, b4_mem 2⟩ (Multiplicative.toAdd (y : P6) 3) *
      pw4 ⟨b4 3, b4_mem 3⟩ (Multiplicative.toAdd (y : P6) 4) := by
  decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_L_conj_V3 {W : Subgroup G} (hWV : W ≤ V) (hW : W.relIndex V = 2) :
    ∃ l ∈ L, conjSub l S.V3 = W := by
  classical
  have hidx : (W.subgroupOf V).index = 2 := hW
  set χ : ↥W4 → ZMod 2 := fun y => if S.frame.ψ.symm y ∈ W.subgroupOf V then 0 else 1
    with hχ
  have hχmul : ∀ a b, χ (a * b) = χ a + χ b := by
    intro a b
    have h := Subgroup.mul_mem_iff_of_index_two hidx (a := S.frame.ψ.symm a)
      (b := S.frame.ψ.symm b)
    rw [← map_mul] at h
    simp only [hχ]
    by_cases ha : S.frame.ψ.symm a ∈ W.subgroupOf V <;>
      by_cases hb : S.frame.ψ.symm b ∈ W.subgroupOf V <;> simp only [ha, hb] at h ⊢ <;>
      simp only [h, iff_true, iff_false, ↓reduceIte, not_true_eq_false] <;> decide
  have hχ1 : χ 1 = 0 := by
    simp only [hχ, map_one]
    simp
  have hpw : ∀ b s, χ (pw4 b s) = s * χ b := by
    intro b s
    rcases (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) s with rfl | rfl
    · simp [pw4, hχ1]
    · simp [pw4]
  set c : Fin 4 → ZMod 2 := fun i => χ ⟨b4 i, b4_mem i⟩ with hc
  have hlin : ∀ y : ↥W4, χ y = c 0 * Multiplicative.toAdd (y : P6) 1 +
      c 1 * Multiplicative.toAdd (y : P6) 2 + c 2 * Multiplicative.toAdd (y : P6) 3 +
        c 3 * Multiplicative.toAdd (y : P6) 4 := by
    intro y
    conv_lhs => rw [w4_decomp y]
    rw [hχmul, hχmul, hχmul, hpw, hpw, hpw, hpw]
    simp only [hc]
    ring
  have hχW : ∀ v (hv : v ∈ V), χ (S.frame.ψ ⟨v, hv⟩) = 0 ↔ v ∈ W := by
    intro v hv
    simp only [hχ, MulEquiv.symm_apply_apply]
    by_cases h : (⟨v, hv⟩ : ↥V) ∈ W.subgroupOf V
    · simp only [h, ↓reduceIte, true_iff]
      exact Subgroup.mem_subgroupOf.mp h
    · simp only [h, ↓reduceIte, one_ne_zero, false_iff]
      exact fun hw => h (Subgroup.mem_subgroupOf.mpr hw)
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : W.relIndex V = 1 := by
      rw [Subgroup.relIndex_eq_one]
      intro v hv
      refine (hχW v hv).1 ?_
      rw [hlin, h0]
      simp
    omega
  obtain ⟨σ, hσ, hσx⟩ := hyp_check c hc0
  obtain ⟨l, hlL, hρl⟩ := (S.frame.image_L σ).2 (hypList_mem σ hσ)
  refine ⟨l, hlL, ?_⟩
  have hkey : ∀ v (hv : v ∈ V), (l : G)⁻¹ * v * (l : G) ∈ S.V3 ↔ v ∈ W := by
    intro v hv
    have hm : (l : G)⁻¹ * v * (l : G) ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (l⁻¹).2 v).mp hv
      simpa using this
    have hψ := S.psi_conj l⁻¹ ⟨v, hv⟩
    have e : (⟨((l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) * v *
        ((l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (l⁻¹).2 v).mp hv⟩ : ↥V) = ⟨_, hm⟩ := by
      apply Subtype.ext
      simp
    rw [e, map_inv, hρl] at hψ
    rw [show S.V3 = S.pre W3sub from rfl, S.mem_pre]
    constructor
    · rintro ⟨hm', h3⟩
      have h3' : InW3 ((S.frame.ψ ⟨_, hm⟩ : ↥W4) : P6) := h3
      rw [hψ, act4_coe] at h3'
      exact (hχW v hv).1 (by rw [hlin]; exact (hσx _ (S.frame.ψ ⟨v, hv⟩).2).1 h3')
    · intro hvW
      refine ⟨hm, ?_⟩
      show InW3 ((S.frame.ψ ⟨_, hm⟩ : ↥W4) : P6)
      rw [hψ, act4_coe]
      refine (hσx _ (S.frame.ψ ⟨v, hv⟩).2).2 ?_
      rw [← hlin]
      exact (hχW v hv).2 hvW
  ext v
  rw [mem_conjSub]
  constructor
  · intro hv
    have hvV : v ∈ V := by
      have h1 := S.V3_le_V hv
      have := (Subgroup.mem_normalizer_iff.mp l.2 _).mp h1
      simpa [mul_assoc] using this
    exact (hkey v hvV).1 hv
  · intro hv
    exact (hkey v (hWV hv)).2 hv

theorem not_Vγ_le_QH_case1 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz)
    (hab : IsMulCommutative ↥(conjClosure V S.G1)) (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
    {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
    (hUU : ⁅conjClosure S.V3 S.G1, F8.Uγ S.V3 S.G1 (g : G)⁆ = ⊥)
    (htr : IsTransvectionGroupOn V (F8.Uγ S.V3 S.G1 (g : G)) (fsuV1 T V)) :
    ¬ F8.Uγ V S.G1 (g : G) ≤ pCoreOf 2 S.G1 := by
  intro hVQ
  have h5b := hF.F913_5b s
  have hstab : stab γ = conjSub (g : G) S.G1 := by
    rw [← s.edge₁, stab_smul, stab_γ₁ hF.amalgamHypV.le₂]
  have hUst : conjClosure S.V3 S.G1 ≤ stab γ :=
    (conjClosure_mono S.V3_le_V le_rfl).trans ((hF.F913_2 s).1.trans ((pCoreOf_le 2 _).trans
      inf_le_right))
  have hcomm : ∀ u ∈ conjClosure S.V3 S.G1, ∀ w ∈ F8.Uγ V S.G1 (g : G),
      w * u * w⁻¹ * u⁻¹ = 1 := by
    intro u hu w hw
    have h1 : w * u * w⁻¹ * u⁻¹ ∈ fsuV1 T V := by
      have := hVQ hw
      rw [hF.toHypF91.pCoreOf_eq_centralizerMod] at this
      exact this.2.2 u hu
    have hxG : (g : G)⁻¹ * u * (g : G) ∈ S.G1 := by
      have := hUst hu
      rw [hstab, mem_conjSub] at this
      exact this
    have hxC : (g : G)⁻¹ * u * (g : G) ∈ Subgroup.centralizer (conjClosure S.V3 S.G1 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u' hu'
      have hu'γ : (g : G) * u' * (g : G)⁻¹ ∈ F8.Uγ S.V3 S.G1 (g : G) := mul_mem_conjSub hu'
      have hc : ⁅u, (g : G) * u' * (g : G)⁻¹⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator hu hu'γ
        rw [hUU] at this
        exact (Subgroup.mem_bot).1 this
      rw [commutatorElement_def] at hc
      have e : u * ((g : G) * u' * (g : G)⁻¹) = ((g : G) * u' * (g : G)⁻¹) * u := by
        calc u * ((g : G) * u' * (g : G)⁻¹) = (u * ((g : G) * u' * (g : G)⁻¹) * u⁻¹ *
            ((g : G) * u' * (g : G)⁻¹)⁻¹) * (((g : G) * u' * (g : G)⁻¹) * u) := by group
          _ = _ := by rw [hc, one_mul]
      calc u' * ((g : G)⁻¹ * u * (g : G)) =
          (g : G)⁻¹ * (((g : G) * u' * (g : G)⁻¹) * u) * (g : G) := by group
        _ = (g : G)⁻¹ * (u * ((g : G) * u' * (g : G)⁻¹)) * (g : G) := by rw [e]
        _ = ((g : G)⁻¹ * u * (g : G)) * u' := by group
    have hxQ : (g : G)⁻¹ * u * (g : G) ∈ pCoreOf 2 S.G1 := by
      rw [hF.toHypF91.pCoreOf_eq_centralizerMod]
      refine ⟨hxG, hF.H_normalizes_V₁ hxG, fun u' hu' => ?_⟩
      rw [← Subgroup.mem_centralizer_iff.mp hxC u' hu', mul_inv_cancel_right, mul_inv_cancel]
      exact (fsuV1 T V).one_mem
    have hy : (g : G)⁻¹ * w * (g : G) ∈ conjClosure V S.G1 := mem_conjSub.mp hw
    have h3 := S.comm_VH_HC hNS h13315 h1356two hG1 hxQ hxC hy
    have h2 : w * u * w⁻¹ * u⁻¹ ∈ F8.A₁ (fsuV1 T V) (g : G) := by
      rw [F8.A₁, mem_conjSub]
      have e : (g : G)⁻¹ * (w * u * w⁻¹ * u⁻¹) * (g : G) =
          ((g : G)⁻¹ * w * (g : G)) * ((g : G)⁻¹ * u * (g : G)) * ((g : G)⁻¹ * w * (g : G))⁻¹ *
            ((g : G)⁻¹ * u * (g : G))⁻¹ := by group
      rw [e]
      exact h3
    have h4 : w * u * w⁻¹ * u⁻¹ ∈ fsuV1 T V ⊓ F8.A₁ (fsuV1 T V) (g : G) := ⟨h1, h2⟩
    rw [h5b] at h4
    exact (Subgroup.mem_bot).1 h4
  obtain ⟨h, hh, t, ht, v, hv, hne⟩ : ∃ h ∈ S.G1, ∃ t ∈ S.V3, ∃ v ∈ V,
      v * ((g : G) * h * t * ((g : G) * h)⁻¹) * v⁻¹ * ((g : G) * h * t * ((g : G) * h)⁻¹)⁻¹ ≠
        1 := by
    by_contra hcon
    push Not at hcon
    have hle : F8.Uγ S.V3 S.G1 (g : G) ≤ Subgroup.centralizer (V : Set G) := by
      rw [show F8.Uγ S.V3 S.G1 (g : G) = conjSub (g : G) (conjClosure S.V3 S.G1) from rfl,
        conjSub_le_iff]
      refine conjClosure_le fun k hk t ht => ?_
      rw [mem_conjSub, inv_inv, Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hcon k hk t ht y hy
      have e : (g : G) * (k * t * k⁻¹) * (g : G)⁻¹ = (g : G) * k * t * ((g : G) * k)⁻¹ := by
        group
      rw [e]
      calc y * ((g : G) * k * t * ((g : G) * k)⁻¹) =
          (y * ((g : G) * k * t * ((g : G) * k)⁻¹) * y⁻¹ * ((g : G) * k * t * ((g : G) * k)⁻¹)⁻¹) *
            (((g : G) * k * t * ((g : G) * k)⁻¹) * y) := by group
        _ = _ := by rw [h1, one_mul]
    have hc : ⁅V, F8.Uγ S.V3 S.G1 (g : G)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hle
    rw [htr.2.2] at hc
    exact hF.toHypF91.V₁_ne_bot hc
  set x : G := (g : G) * h with hx
  have hVxγ : conjSub x V ≤ F8.Uγ V S.G1 (g : G) := by
    rw [hx, conjSub_mul]
    refine conjSub_mono _ fun w hw => ?_
    have h1 := mem_conjSub.mp hw
    have e : w = h * (h⁻¹ * w * h) * h⁻¹ := by group
    rw [e]
    exact mem_conjClosure hh h1
  have hVxC3 : conjSub x V ≤ Subgroup.centralizer (S.V3 : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro t' ht'
    have h1 := hcomm t' (le_conjClosure S.V3 S.G1 ht') w (hVxγ hw)
    calc t' * w = (w * t' * w⁻¹ * t'⁻¹)⁻¹ * (w * t') := by group
      _ = w * t' := by rw [h1, inv_one, one_mul]
  have hVxN : conjSub x V ≤ Subgroup.normalizer (V : Set G) :=
    hVxC3.trans (S.centralizer_V3_le h13315)
  have hC3V1 : ⁅V, Subgroup.centralizer (S.V3 : Set G)⁆ ≤ fsuV1 T V := by
    classical
    let X : Subgroup G := if IsHatA6 L then oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆ else L₁Of L S.V2
    have hX₁ : IsHatA6 L → X = oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆ := fun h => by simp [X, h]
    have hX₂ : ¬ IsHatA6 L → X = L₁Of L S.V2 := fun h => by simp [X, h]
    obtain ⟨-, -, -, -, -, -, -, -, h9⟩ := h13315 G T L V S.V2 X _ S.h13 S.irr S.zv S.isV2
      S.not_iso_a5 hX₁ hX₂ rfl
    exact (h9 S.V3 S.V2_le_V3 S.V3_le_V S.T_le_normalizer_V3 S.card_V3).2 S.not_lieModel_psu33
  have hVxV1 : ⁅V, conjSub x V⁆ ≤ fsuV1 T V :=
    (Subgroup.commutator_mono le_rfl hVxC3).trans hC3V1
  have hxt : x * t * x⁻¹ ∈ conjSub x V := mul_mem_conjSub (S.V3_le_V ht)
  have hVxne : ⁅V, conjSub x V⁆ ≠ ⊥ := by
    intro hb
    apply hne
    have h1 := Subgroup.commutator_mem_commutator hv hxt
    rw [hb, commutatorElement_def] at h1
    exact (Subgroup.mem_bot).1 h1
  let φ : ↥(conjSub x V) →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion hVxN)
  have hφr : ∀ w : ↥(conjSub x V), φ w = 1 ∨ φ w = swap 4 5 := fun w =>
    fixW3_iff _ (S.fixW3_of_centralizer (x := ⟨w, hVxN w.2⟩) (hVxC3 w.2))
  have hφk : φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf (conjSub x V) := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact S.rho_eq_one_iff _
  have hrange : Nat.card φ.range ≤ 2 := by
    let F : Finset (Perm (Fin 6)) := {1, swap 4 5}
    let f : ↥φ.range → ↥F := fun m => ⟨m, by
      obtain ⟨w, hw⟩ := m.2
      rw [← hw]
      rcases hφr w with h1 | h1 <;> simp [F, h1]⟩
    have hf : Function.Injective f := fun m₁ m₂ he =>
      Subtype.ext (congrArg (fun y : ↥F => (y : Perm (Fin 6))) he)
    calc Nat.card φ.range ≤ Nat.card ↥F := Nat.card_le_card_of_injective f hf
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; decide
  have hrel2 : (conjSub x V ⊓ Subgroup.centralizer (V : Set G)).relIndex (conjSub x V) = 2 := by
    have h1 : (conjSub x V ⊓ Subgroup.centralizer (V : Set G)).relIndex (conjSub x V) =
        Nat.card φ.range := by
      rw [Subgroup.inf_relIndex_left, Subgroup.relIndex, ← hφk, Subgroup.index_ker]
    have h2 : (conjSub x V ⊓ Subgroup.centralizer (V : Set G)).relIndex (conjSub x V) ≠ 1 := by
      intro h1'
      rw [Subgroup.relIndex_eq_one] at h1'
      apply hVxne
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (h1'.trans inf_le_right)
    have h0 := relIndex_ne_zero' (conjSub x V ⊓ Subgroup.centralizer (V : Set G)) (conjSub x V)
    omega
  have hWV : conjSub x⁻¹ (conjSub x V ⊓ Subgroup.centralizer (V : Set G)) ≤ V := by
    rw [conjSub_inf, conjSub_conjSub_inv]
    exact inf_le_left
  have hW2 : (conjSub x⁻¹ (conjSub x V ⊓ Subgroup.centralizer (V : Set G))).relIndex V = 2 := by
    have h1 := F9.relIndex_conjSub x⁻¹ (conjSub x V ⊓ Subgroup.centralizer (V : Set G))
      (conjSub x V)
    rw [conjSub_conjSub_inv] at h1
    rw [h1]
    exact hrel2
  obtain ⟨l, hlL, hlW⟩ := S.exists_L_conj_V3 hWV hW2
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hlL
  have hC3 : conjSub (x * l) S.V3 = conjSub x V ⊓ Subgroup.centralizer (V : Set G) := by
    rw [conjSub_mul, hlW, conjSub_inv_conjSub]
  have hVxl : conjSub (x * l) V = conjSub x V := by
    rw [conjSub_mul, F7.conjSub_eq_of_mem_normalizer hlN]
  have hVN : V ≤ Subgroup.normalizer (conjSub x V : Set G) := by
    have h1 : V ≤ Subgroup.centralizer (conjSub (x * l) S.V3 : Set G) := by
      rw [hC3]
      intro v' hv'
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (Subgroup.mem_centralizer_iff.mp hw.2 v' hv').symm
    rw [conjSub_centralizer] at h1
    have h2 := conjSub_le_normalizer (g := x * l) (S.centralizer_V3_le h13315)
    rw [hVxl] at h2
    exact h1.trans h2
  have hcomm2 : ⁅V, conjSub x V⁆ ≤ V ⊓ conjSub x V :=
    F7.commutator_le_inf_of_normalizes hVN hVxN
  have hV1le : fsuV1 T V ≤ ⁅V, conjSub x V⁆ := by
    refine le_of_card_eq_two_of_inf_ne_bot hF.card_V₁ fun hb => hVxne ?_
    rwa [inf_eq_right.2 hVxV1] at hb
  have hV1x : fsuV1 T V ≤ conjSub x⁻¹⁻¹ V := by
    rw [inv_inv]
    exact hV1le.trans (hcomm2.trans inf_le_right)
  have hbot := S.comm_conjSub_V_eq_bot hab hV1x
  rw [inv_inv] at hbot
  exact hVxne hbot

@[expose] def Struct13827Main (S : Setting4 G T L V) : Prop :=
  ∃ K : Subgroup G, S.G1 ≤ Subgroup.normalizer (K : Set G) ∧ K ⊔ T = S.G1 ∧ S.L1 ≤ K ∧
    (∀ h ∈ S.G1, (∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 S.G1) → h ∈ pCoreOf 2 S.G1) ∧
    ((¬ IsHatA6 L ∧ ∃ ρ : ↥S.G1 →* Perm (Fin 6),
        (∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1) ∧
        (∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6)) ∧
        (∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ) ∧
        ((∃ β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6),
            Function.Surjective β ∧
            (∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
            ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
              ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) =
                Multiplicative.toAdd (β u) →
                (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) =
                  Multiplicative.toAdd (β v)) ∨
          (∃ β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6),
            Function.Surjective β ∧
            (∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
            ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
              Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u))))) ∨
      (IsHatA6 L ∧ ∃ ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2),
        Function.Surjective ρ ∧ (∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1) ∧
        ∃ β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2),
          Function.Surjective β ∧
          (∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
          ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
            Multiplicative.toAdd (β v) =
              ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
                Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (β u))))

@[expose] def Struct13827Three (S : Setting4 G T L V) : Prop :=
  ∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
    (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G) ∨
      F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1) →
    F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1 ∧
      F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G) ∧
      IsTransvectionGroupOn V (F8.Uγ S.V3 S.G1 (g : G)) (fsuV1 T V) ∧
      fsuV1 T V ≤ F8.Uγ S.V3 S.G1 (g : G) ∧ ¬ F8.Uγ V S.G1 (g : G) ≤ pCoreOf 2 S.G1

omit S in
theorem struct13827_of {S : Setting4 G T L V} (h12 : S.Struct13827Main)
    (h3 : S.Struct13827Three) : S.Struct13827 := by
  obtain ⟨K, h1, h2, h3', h4, h5⟩ := h12
  exact ⟨K, h1, h2, h3', h4, h5, h3⟩

end Setting4

@[expose] def Ident13827 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → S.G1 ∈ S.Hz →
    IsMulCommutative ↥(conjClosure V S.G1) → HypF98 T V L (fsuV1 T V) S.V3 S.G1 →
      S.Struct13827Main

@[expose] def Lem13827ThreeDD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → S.G1 ∈ S.Hz →
    IsMulCommutative ↥(conjClosure V S.G1) → HypF98 T V L (fsuV1 T V) S.V3 S.G1 →
      S.Struct13827Main →
      ∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
        (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G) ∨
          F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1) →
        F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1 ∧
          F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G)

theorem input13827Six_of (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (hId : Ident13827) (hDD : Lem13827ThreeDD) : Input13827Six := by
  intro G _ _ T L V S hNS hNU hG1 hab hF
  have hM := hId G T L V S hNS hNU hG1 hab hF
  refine Setting4.struct13827_of hM fun γ γ' g s hcase => ?_
  obtain ⟨hDH, hDγ⟩ := hDD G T L V S hNS hNU hG1 hab hF hM γ γ' g s hcase
  rcases hF.F916_1 s hDγ.symm with ⟨hlt, -⟩ | ⟨-, hUU, htr⟩
  · exact absurd hDH (ne_of_lt hlt)
  have hV1 : fsuV1 T V ≤ F8.Uγ S.V3 S.G1 (g : G) := by
    rw [← htr.2.2, Subgroup.commutator_le]
    intro v hv u hu
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (htr.1 hv) u).mp hu)
      (Subgroup.inv_mem _ hu)
  exact ⟨hDH, hDγ, htr, hV1,
    S.not_Vγ_le_QH_case1 hNS h13315 h1356two hG1 hab hF s hUU htr⟩


end CFSG.Quasithin.H13.A6
