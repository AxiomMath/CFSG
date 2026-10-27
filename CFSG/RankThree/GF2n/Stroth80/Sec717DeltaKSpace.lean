module

public import CFSG.RankThree.GF2n.Stroth80.Sec717Layers
import CFSG.RankThree.GF2n.Stroth80.Sec714ModelLin

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup
open scoped commutatorElement

variable {K E X : Type} [Field K] [AddCommGroup E] [Module K E] [Group X]
  {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V Nb Rb : Subgroup X}
  {T : Submodule K E}

namespace Sec717LayerData

private theorem isom_add (D : Sec717LayerData B φ V Nb Rb T) (n : X) (x y : E) :
    B (x + opm (φ n) x) (y + opm (φ n) y) = B x y := by
  have e : ∀ z, z + opm (φ n) z = φ n z := fun z => by rw [opm_apply]; abel
  rw [e, e]
  exact D.isom n x y

private theorem TP_orth (_ : Sec717LayerData B φ V Nb Rb T) {v w : E} (hv : v ∈ T)
    (hw : w ∈ B.orthogonal T) : B v w = 0 :=
  (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) v hv

private theorem bilin_right_P (D : Sec717LayerData B φ V Nb Rb T) {n : X} (hn : n ∈ Nb)
    {u : E} (hu : u ∈ B.orthogonal T) (y : E) :
    B u (opm (φ n) y) = -B (opm (φ n) u) y := by
  rw [S714.bilin_D_left (D.isom_add n) (D.Nb_low n hn).top (D.Nb_low n hn).mid
    (fun v hv w hw => D.TP_orth hv hw) hu y, neg_neg]

private theorem opm_comm (D : Sec717LayerData B φ V Nb Rb T) {n m : X} (hn : n ∈ Nb)
    (hm : m ∈ Nb) (x : E) :
    opm (φ ⁅n, m⁆) x = opm (φ n) (opm (φ m) x) - opm (φ m) (opm (φ n) x) := by
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact opm_commutator_of_lowering (D.Nb_low n hn) (D.Nb_low m hm) x

private theorem comm_mem (D : Sec717LayerData B φ V Nb Rb T) {n m : X} (hn : n ∈ Nb)
    (hm : m ∈ Nb) : ⁅n, m⁆ ∈ V := by
  have hmem : ⁅n, m⁆ ∈ Nb := by
    rw [commutatorElement_def]
    exact Nb.mul_mem (Nb.mul_mem (Nb.mul_mem hn hm) (Nb.inv_mem hn)) (Nb.inv_mem hm)
  refine D.corner_mem _ hmem ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [D.opm_comm hn hm]
    exact T.sub_mem ((D.Nb_low n hn).mid _ ((D.Nb_low m hm).top x))
      ((D.Nb_low m hm).mid _ ((D.Nb_low n hn).top x))
  · rw [D.opm_comm hn hm, (D.Nb_low n hn).bot _ ((D.Nb_low m hm).mid x hx),
      (D.Nb_low m hm).bot _ ((D.Nb_low n hn).mid x hx), sub_zero]

private theorem mem_of_opm_P_eq_zero [FiniteDimensional K E] (D : Sec717LayerData B φ V Nb Rb T)
    {x : X} (hx : x ∈ Nb) (h0 : ∀ w ∈ B.orthogonal T, opm (φ x) w = 0) : x ∈ V := by
  refine D.corner_mem x hx ⟨fun y => ?_, h0⟩
  rw [← LinearMap.BilinForm.orthogonal_orthogonal D.nondeg D.refl T,
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  show B w (opm (φ x) y) = 0
  rw [D.bilin_right_P hx hw, h0 w hw, map_zero, LinearMap.zero_apply, neg_zero]

private theorem comm_comb (D : Sec717LayerData B φ V Nb Rb T) {n₁ n₂ n₃ m : X}
    (h₁ : n₁ ∈ Nb) (h₂ : n₂ ∈ Nb) (h₃ : n₃ ∈ Nb) (hm : m ∈ Nb) {k₁ k₂ : K}
    (hk : ∀ w ∈ B.orthogonal T, opm (φ n₃) w = k₁ • opm (φ n₁) w + k₂ • opm (φ n₂) w)
    (x y : E) :
    B (opm (φ ⁅n₃, m⁆) x) y =
      k₁ * B (opm (φ ⁅n₁, m⁆) x) y + k₂ * B (opm (φ ⁅n₂, m⁆) x) y := by
  have hpc : ∀ {n : X}, n ∈ Nb → B (opm (φ ⁅n, m⁆) x) y =
      B (opm (φ n) x) (opm (φ m) y) - B (opm (φ m) x) (opm (φ n) y) := fun hn =>
    S714.pair_comm (D.opm_comm hn hm) (D.isom_add _) (D.isom_add _) (D.Nb_low _ hn).top
      (D.Nb_low m hm).top (D.Nb_low _ hn).mid (D.Nb_low m hm).mid
      (fun v hv w hw => D.TP_orth hv hw) x y
  have hl := S714.bilin_comb (D.isom_add n₁) (D.isom_add n₂) (D.isom_add n₃)
    (D.Nb_low n₁ h₁).top (D.Nb_low n₂ h₂).top (D.Nb_low n₃ h₃).top (D.Nb_low n₁ h₁).mid
    (D.Nb_low n₂ h₂).mid (D.Nb_low n₃ h₃).mid (fun w hw v hv => D.refl _ _ (D.TP_orth hv hw)) hk
    x ((D.Nb_low m hm).top y)
  have hu := (D.Nb_low m hm).top x
  have hr : B (opm (φ m) x) (opm (φ n₃) y) =
      k₁ * B (opm (φ m) x) (opm (φ n₁) y) + k₂ * B (opm (φ m) x) (opm (φ n₂) y) := by
    rw [D.bilin_right_P h₃ hu, D.bilin_right_P h₁ hu, D.bilin_right_P h₂ hu, hk _ hu, map_add,
      map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul]
    ring
  rw [hpc h₃, hpc h₁, hpc h₂, hl, hr]
  ring

theorem exists_delta_smul_of_comm [Finite K] [Finite X] [FiniteDimensional K E]
    (D : Sec717LayerData B φ V Nb Rb T) (hVN : V ≤ Nb) {a₀ : X} (ha₀ : a₀ ∈ V) (ha₀1 : a₀ ≠ 1)
    (hroot : ∀ a ∈ V, ∃ c : K, opm (φ a) = c • opm (φ a₀))
    (hS : ∀ n ∈ Nb, ∀ c : K, ∃ n' ∈ Nb, ∀ w ∈ B.orthogonal T,
      opm (φ n') w = c • opm (φ n) w)
    (hZN : ∀ n ∈ Nb, (∀ m ∈ Nb, n * m = m * n) → n ∈ V)
    (hNcard : Nat.card Nb = Nat.card K ^ 8 * Nat.card V) {L : Subgroup X} (hLN : L ≤ Nb)
    (hVL : V ≤ L) (hLab : ∀ l ∈ L, ∀ l' ∈ L, l * l' = l' * l)
    (hLcard : Nat.card L = Nat.card K ^ 4 * Nat.card V) :
    ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w := by
  classical
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, opm (φ a₀) x₀ ≠ 0 := by
    by_contra! h
    have h6 := D.finrank_T
    rw [← D.range_V a₀ ha₀ ha₀1, LinearMap.range_eq_bot.mpr (LinearMap.ext h), finrank_bot] at h6
    exact absurd h6 (by norm_num)
  obtain ⟨y₁, hy₁⟩ : ∃ y, B (opm (φ a₀) x₀) y ≠ 0 := by
    by_contra! h; exact hx₀ (D.nondeg.1 _ h)
  set y₀ := (B (opm (φ a₀) x₀) y₁)⁻¹ • y₁ with hy₀
  have hxy : B (opm (φ a₀) x₀) y₀ = 1 := by rw [hy₀, map_smul, smul_eq_mul, inv_mul_cancel₀ hy₁]
  set ω₀ : X → X → K := fun n m => B (opm (φ ⁅n, m⁆) x₀) y₀ with hω₀
  have hω₀one : ∀ n m : X, n * m = m * n → ω₀ n m = 0 := fun n m h => by
    show B (opm (φ ⁅n, m⁆) x₀) y₀ = 0
    rw [commutatorElement_eq_one_iff_mul_comm.mpr h, map_one]
    simp [opm_apply]
  have hcomm0 : ∀ n ∈ Nb, ∀ m ∈ Nb, ω₀ n m = 0 → n * m = m * n := by
    intro n hn m hm h0
    obtain ⟨c, hc⟩ := hroot _ (D.comm_mem hn hm)
    have hc0 : c = 0 := by
      rw [← h0]; show c = B (opm (φ ⁅n, m⁆) x₀) y₀
      rw [hc, LinearMap.smul_apply, LinearMap.BilinForm.smul_left, hxy, mul_one]
    have h1 : φ ⁅n, m⁆ = 1 := eq_one_of_opm_eq_zero fun x => by
      rw [hc, hc0, zero_smul, LinearMap.zero_apply]
    exact commutatorElement_eq_one_iff_mul_comm.mp (D.inj (h1.trans (map_one φ).symm))
  have hanti : ∀ n ∈ Nb, ∀ m ∈ Nb, ω₀ m n = -ω₀ n m := by
    intro n hn m hm
    have hc := D.V_corner _ (D.comm_mem hn hm)
    simp only [hω₀, ← commutatorElement_inv n m, map_inv]
    rw [opm_inv_apply_of_lowering (hc.isLayerLowering D.T_le), hc.mid _ (D.T_le (hc.top x₀)),
      add_zero, map_neg, LinearMap.neg_apply]
  let Δ : X → (↥(B.orthogonal T) →ₗ[K] E) := fun n => (opm (φ n)).domRestrict _
  have hΔmul : ∀ n ∈ Nb, ∀ m ∈ Nb, Δ (n * m) = Δ n + Δ m := fun n hn m hm =>
    LinearMap.ext fun w => by
      show opm (φ (n * m)) w = opm (φ n) w + opm (φ m) w
      rw [map_mul, opm_mul_apply_layer, (D.Nb_low n hn).bot _ ((D.Nb_low m hm).mid w w.2),
        add_zero]
  have hΔone : Δ 1 = 0 := LinearMap.ext fun w => by simp [Δ, opm_apply]
  let S : Submodule K (↥(B.orthogonal T) →ₗ[K] E) :=
    { carrier := {f | ∃ n ∈ Nb, Δ n = f}
      add_mem' := by
        rintro _ _ ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
        exact ⟨n * m, Nb.mul_mem hn hm, hΔmul n hn m hm⟩
      zero_mem' := ⟨1, Nb.one_mem, hΔone⟩
      smul_mem' := by
        rintro c _ ⟨n, hn, rfl⟩
        obtain ⟨n', hn', h⟩ := hS n hn c
        exact ⟨n', hn', LinearMap.ext fun w => h w w.2⟩ }
  haveI : Finite ↥S := Module.finite_of_finite K
  have hmemS : ∀ n ∈ Nb, Δ n ∈ S := fun n hn => ⟨n, hn, rfl⟩
  have hrep : ∀ f : S, ∃ n ∈ Nb, Δ n = f := fun f => f.2
  choose rep hrepN hrepΔ using hrep
  have hΔzero : ∀ n ∈ Nb, Δ n = 0 → n ∈ V := fun n hn h =>
    D.mem_of_opm_P_eq_zero hn fun w hw => LinearMap.congr_fun h ⟨w, hw⟩
  have hlin : ∀ (f₁ f₂ f₃ : S) (k₁ k₂ : K), (f₃ : ↥(B.orthogonal T) →ₗ[K] E) =
      k₁ • (f₁ : ↥(B.orthogonal T) →ₗ[K] E) + k₂ • (f₂ : ↥(B.orthogonal T) →ₗ[K] E) →
      ∀ m ∈ Nb, ω₀ (rep f₃) m = k₁ * ω₀ (rep f₁) m + k₂ * ω₀ (rep f₂) m := by
    intro f₁ f₂ f₃ k₁ k₂ h m hm
    refine D.comm_comb (hrepN f₁) (hrepN f₂) (hrepN f₃) hm (fun w hw => ?_) x₀ y₀
    have e := LinearMap.congr_fun h ⟨w, hw⟩
    rw [← hrepΔ f₃, ← hrepΔ f₁, ← hrepΔ f₂] at e
    exact e
  have hlinR : ∀ (f₁ f₂ f₃ : S) (k₁ k₂ : K), (f₃ : ↥(B.orthogonal T) →ₗ[K] E) =
      k₁ • (f₁ : ↥(B.orthogonal T) →ₗ[K] E) + k₂ • (f₂ : ↥(B.orthogonal T) →ₗ[K] E) →
      ∀ n ∈ Nb, ω₀ n (rep f₃) = k₁ * ω₀ n (rep f₁) + k₂ * ω₀ n (rep f₂) := by
    intro f₁ f₂ f₃ k₁ k₂ h n hn
    rw [hanti _ (hrepN f₃) n hn, hlin f₁ f₂ f₃ k₁ k₂ h n hn, hanti _ (hrepN f₁) n hn,
      hanti _ (hrepN f₂) n hn]
    ring
  let ω : LinearMap.BilinForm K S := LinearMap.mk₂ K (fun f g => ω₀ (rep f) (rep g))
    (fun f f' g => by simpa using hlin f f' (f + f') 1 1 (by simp) (rep g) (hrepN g))
    (fun c f g => by simpa using hlin f f (c • f) c 0 (by simp) (rep g) (hrepN g))
    (fun f g g' => by simpa using hlinR g g' (g + g') 1 1 (by simp) (rep f) (hrepN f))
    (fun c f g => by simpa using hlinR g g (c • g) c 0 (by simp) (rep f) (hrepN f))
  have hωrefl : ω.IsRefl := fun f g h =>
    hω₀one _ _ (hcomm0 _ (hrepN f) _ (hrepN g) h).symm
  have hsepL : ∀ f : S, (∀ g : S, ω f g = 0) → f = 0 := by
    intro f hf
    have hfV : rep f ∈ V := hZN _ (hrepN f) fun m hm => by
      refine hcomm0 _ (hrepN f) _ hm ?_
      have e2 : ω₀ (rep f) m = ω₀ (rep f) (rep ⟨Δ m, hmemS m hm⟩) := by
        rw [hanti _ hm _ (hrepN f), hanti _ (hrepN ⟨Δ m, hmemS m hm⟩) _ (hrepN f)]
        congr 1
        have h3 := D.comm_comb (hrepN ⟨Δ m, hmemS m hm⟩) (hrepN ⟨Δ m, hmemS m hm⟩) hm
          (hrepN f) (k₁ := 1) (k₂ := 0) (fun w hw => by
            rw [one_smul, zero_smul, add_zero]
            exact (LinearMap.congr_fun (hrepΔ ⟨Δ m, hmemS m hm⟩) ⟨w, hw⟩).symm) x₀ y₀
        rw [one_mul, zero_mul, add_zero] at h3
        exact h3
      rw [e2]
      exact hf ⟨Δ m, hmemS m hm⟩
    apply Subtype.ext
    rw [← hrepΔ f]
    exact LinearMap.ext fun w => (D.V_corner _ hfV).mid _ w.2
  have hωnd : ω.Nondegenerate := ⟨hsepL, fun g hg => hsepL g fun f => hωrefl _ _ (hg f)⟩
  let Δh : ↥Nb →* Multiplicative ↥S :=
    MonoidHom.mk' (fun n => Multiplicative.ofAdd (⟨Δ n, hmemS n n.2⟩ : S)) fun n m => by
      apply Multiplicative.toAdd.injective
      exact Subtype.ext (hΔmul n n.2 m m.2)
  have hcardV : ∀ H : Subgroup ↥Nb, V.subgroupOf Nb ≤ H →
      Nat.card ↥(Δh.comp H.subtype).ker = Nat.card V := by
    intro H hVH
    have e : (Δh.comp H.subtype).ker = (V.subgroupOf Nb).subgroupOf H := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact ⟨fun h => hΔzero _ (x : ↥Nb).2 (congrArg Subtype.val (congrArg Multiplicative.toAdd h)),
        fun h => Multiplicative.toAdd.injective (Subtype.ext (LinearMap.ext fun w =>
          (D.V_corner _ h).mid _ w.2))⟩
    rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv]
  have hfinS : Module.finrank K ↥S = 8 := by
    have h := Subgroup.card_ker_mul_card_range (Δh.comp (⊤ : Subgroup ↥Nb).subtype)
    rw [hcardV ⊤ le_top, Subgroup.card_top] at h
    have hr : (Δh.comp (⊤ : Subgroup ↥Nb).subtype).range = ⊤ := MonoidHom.range_eq_top.mpr
      fun y => ⟨⟨⟨rep (Multiplicative.toAdd y), hrepN _⟩, Subgroup.mem_top _⟩,
        Multiplicative.toAdd.injective (Subtype.ext (hrepΔ _))⟩
    rw [hr, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, hNcard,
      Module.natCard_eq_pow_finrank (K := K) (V := ↥S), Nat.mul_comm] at h
    exact Nat.pow_right_injective hq (Nat.eq_of_mul_eq_mul_right Nat.card_pos h)
  let A : Set ↥S := {f | ∃ l ∈ L, (f : ↥(B.orthogonal T) →ₗ[K] E) = Δ l}
  have hAL : ∀ f ∈ A, rep f ∈ L := by
    rintro f ⟨l, hl, hfl⟩
    have h : Δ (l⁻¹ * rep f) = 0 := by
      have h1 : Δ l⁻¹ + Δ l = 0 := by
        rw [← hΔmul _ (Nb.inv_mem (hLN hl)) _ (hLN hl), inv_mul_cancel, hΔone]
      rw [hΔmul _ (Nb.inv_mem (hLN hl)) _ (hrepN f), hrepΔ f, hfl, h1]
    have e : rep f = l * (l⁻¹ * rep f) := by group
    rw [e]
    exact L.mul_mem hl (hVL (hΔzero _ (Nb.mul_mem (Nb.inv_mem (hLN hl)) (hrepN f)) h))
  let W := Submodule.span K A
  have hiso : ∀ f ∈ W, ∀ g ∈ W, ω f g = 0 := by
    intro f hf g hg
    induction hf using Submodule.span_induction with
    | mem f hf =>
      induction hg using Submodule.span_induction with
      | mem g hg => exact hω₀one _ _ (hLab _ (hAL f hf) _ (hAL g hg))
      | zero => exact map_zero (ω f)
      | add g g' _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
      | smul c g _ h => rw [map_smul, h, smul_zero]
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add f f' _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply, h₁, h₂, add_zero]
    | smul c f _ h => rw [map_smul, LinearMap.smul_apply, h, smul_zero]
  have hcardW : Nat.card ↥W ≤ Nat.card K ^ 4 := by
    have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal hωrefl W
    rw [LinearMap.BilinForm.orthogonal_top_eq_bot hωnd, inf_bot_eq, finrank_bot, add_zero,
      hfinS] at h1
    have h2 := Submodule.finrank_mono (show W ≤ ω.orthogonal W from fun g hg =>
      LinearMap.BilinForm.mem_orthogonal_iff.mpr fun f hf => hiso f hf g hg)
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥W)]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  let Lhat : Subgroup ↥Nb := (AddSubgroup.toSubgroup W.toAddSubgroup).comap Δh
  have hLle : L.subgroupOf Nb ≤ Lhat := fun n hn =>
    show (⟨Δ n, hmemS n n.2⟩ : S) ∈ W from
      Submodule.subset_span ⟨n, Subgroup.mem_subgroupOf.mp hn, rfl⟩
  have hLeq : Lhat = L.subgroupOf Nb := by
    refine (Subgroup.eq_of_le_of_card_ge hLle ?_).symm
    have h := Subgroup.card_ker_mul_card_range (Δh.comp Lhat.subtype)
    rw [hcardV Lhat (fun x hx => hLle (Subgroup.mem_subgroupOf.mpr
      (hVL (Subgroup.mem_subgroupOf.mp hx))))] at h
    have hrange : Nat.card ↥(Δh.comp Lhat.subtype).range ≤ Nat.card ↥W := by
      have hle : (Δh.comp Lhat.subtype).range ≤ AddSubgroup.toSubgroup W.toAddSubgroup := by
        rintro _ ⟨n, rfl⟩
        exact n.2
      exact (Subgroup.card_le_of_le hle).trans
        (le_of_eq (Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun x => Iff.rfl)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv, hLcard, ← h, Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (hrange.trans hcardW)
  intro l hl c
  set f := c • (⟨Δ l, hmemS l (hLN hl)⟩ : S)
  have hn : (⟨rep f, hrepN f⟩ : ↥Nb) ∈ Lhat := by
    show (⟨Δ (rep f), hmemS _ (hrepN f)⟩ : S) ∈ W
    rw [show (⟨Δ (rep f), hmemS _ (hrepN f)⟩ : S) = f from Subtype.ext (hrepΔ f)]
    exact W.smul_mem c (Submodule.subset_span ⟨l, hl, rfl⟩)
  rw [hLeq] at hn
  exact ⟨rep f, Subgroup.mem_subgroupOf.mp hn, fun w hw =>
    LinearMap.congr_fun (hrepΔ f) ⟨w, hw⟩⟩

end Sec717LayerData

end CFSG.RankThree.GF2n.Stroth80
