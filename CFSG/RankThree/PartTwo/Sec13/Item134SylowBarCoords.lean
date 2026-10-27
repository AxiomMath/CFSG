module

public import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
public import CFSG.RankThree.PartTwo.Sec12.Coordinates
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec12
open CFSG.ABGLocalTools (IsSylowOf)
open Module
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

section Coords

variable {A : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  (f : Multiplicative V ≃* A)

omit [Finite G] in
theorem coe_wAction_coordVec (w : Subgroup.normalizer (A : Set G)) (a : A) :
    ((f (Multiplicative.ofAdd (wAction f w (coordVec f a))) : A) : G) =
      (w : G) * a * (w : G)⁻¹ := by
  rw [wAction_apply]
  simp [coordVec]

omit [Finite G] in
theorem wAction_coordVec_eq_iff (w : Subgroup.normalizer (A : Set G)) (a : A) :
    wAction f w (coordVec f a) = coordVec f a ↔ (w : G) * a * (w : G)⁻¹ = a := by
  constructor
  · intro h
    rw [← coe_wAction_coordVec f w a, h]
    simp [coordVec]
  · intro h
    have h1 := coe_wAction_coordVec f w a
    rw [h] at h1
    have h2 : f (Multiplicative.ofAdd (wAction f w (coordVec f a))) = a := Subtype.ext h1
    have h3 := congrArg (fun y => Multiplicative.toAdd (f.symm y)) h2
    simpa [coordVec] using h3

omit [Finite G] in
theorem conj_eq_of_wAction_eq {w w' : Subgroup.normalizer (A : Set G)}
    (h : wAction f w = wAction f w') (a : G) (ha : a ∈ A) :
    (w : G) * a * (w : G)⁻¹ = (w' : G) * a * (w' : G)⁻¹ := by
  rw [← coe_wAction_coordVec f w ⟨a, ha⟩, ← coe_wAction_coordVec f w' ⟨a, ha⟩, h]

omit [Finite G] in
theorem wAction_eq_of_conj_eq {w w' : Subgroup.normalizer (A : Set G)}
    (h : ∀ a ∈ A, (w : G) * a * (w : G)⁻¹ = (w' : G) * a * (w' : G)⁻¹) :
    wAction f w = wAction f w' := by
  ext v
  have h1 := coe_wAction_coordVec f w (f (Multiplicative.ofAdd v))
  have h2 := coe_wAction_coordVec f w' (f (Multiplicative.ofAdd v))
  rw [h _ (f (Multiplicative.ofAdd v)).2, ← h2] at h1
  have h3 := congrArg (fun y => Multiplicative.toAdd (f.symm y)) (Subtype.ext h1 :
    f (Multiplicative.ofAdd (wAction f w (coordVec f (f (Multiplicative.ofAdd v))))) =
      f (Multiplicative.ofAdd (wAction f w' (coordVec f (f (Multiplicative.ofAdd v))))))
  simpa [coordVec] using h3

end Coords

section Linear

theorem matrix_two_eq_of_mul_self {M : Matrix (Fin 2) (Fin 2) (ZMod 3)} (hdet : M.det = 1)
    (hM : M * M = 1) : M = 1 ∨ M = -1 := by
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  have h10 := congrFun (congrFun hM 1) 0
  have h11 := congrFun (congrFun hM 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  rw [Matrix.det_fin_two] at hdet
  have key : ∀ a b c d : ZMod 3, a * d - b * c = 1 → a * a + b * c = 1 → a * b + b * d = 0 →
      c * a + d * c = 0 → c * b + d * d = 1 →
      (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = -1 ∧ b = 0 ∧ c = 0 ∧ d = -1) := by decide
  rcases key (M 0 0) (M 0 1) (M 1 0) (M 1 1) hdet h00 h01 h10 h11 with
    ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem sl2_three_eq_of_mul_self {g h : SL(2, ZMod 3)} (hg : g * g = 1) (hg1 : g ≠ 1)
    (hh : h * h = 1) (hh1 : h ≠ 1) : g = h := by
  have key : ∀ x : SL(2, ZMod 3), x * x = 1 → x ≠ 1 →
      (x : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1 := by
    intro x hx hx1
    have hM : (x : Matrix (Fin 2) (Fin 2) (ZMod 3)) * x = 1 := by
      simpa using congrArg Subtype.val hx
    rcases matrix_two_eq_of_mul_self x.2 hM with h1 | h1
    · exact absurd (Subtype.ext h1) hx1
    · exact h1
  exact Subtype.ext ((key g hg hg1).trans (key h hh hh1).symm)

theorem sl2_three_exists_involution : ∃ z : SL(2, ZMod 3), z * z = 1 ∧ z ≠ 1 := by
  have hdet : (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
    rw [Matrix.det_fin_two]
    simp
  refine ⟨⟨-1, hdet⟩, Subtype.ext ?_, fun h => ?_⟩
  · show (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (-1) = 1
    simp
  have := congrArg (fun g : SL(2, ZMod 3) => (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0) h
  simp at this
  revert this
  decide

theorem oPrimeResidual_three_normal (X : Type*) [Group X] :
    (CFSG.GH74.GLS.oPrimeResidual 3 X).Normal := by
  constructor
  intro n hn g
  unfold CFSG.GH74.GLS.oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨k, ?_⟩
    rw [conj_pow, hk]
    group
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem det_eq_one_of_pow {g : V ≃ₗ[ZMod 3] V} {k : ℕ} (hg : g ^ 3 ^ k = 1) :
    LinearEquiv.det g = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : LinearEquiv.det g ^ 3 ^ k = 1 := by rw [← map_pow, hg, map_one]
  have h2 : LinearEquiv.det g ^ 2 = 1 := ZMod.units_pow_card_sub_one_eq_one 3 _
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  rw [hm, pow_succ, pow_mul, h2, one_pow, one_mul] at h1
  exact h1

theorem det_eq_one_of_mem_oPrimeResidual {X : Subgroup (V ≃ₗ[ZMod 3] V)} {x : X}
    (hx : x ∈ CFSG.GH74.GLS.oPrimeResidual 3 X) : LinearEquiv.det (x : V ≃ₗ[ZMod 3] V) = 1 := by
  unfold CFSG.GH74.GLS.oPrimeResidual at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := hy
    exact det_eq_one_of_pow (k := k) (by rw [← Subgroup.coe_pow, hk, Subgroup.coe_one])
  | one => simp
  | mul a b _ _ ha hb => rw [Subgroup.coe_mul, map_mul, ha, hb, one_mul]
  | inv a _ ha => rw [Subgroup.coe_inv, map_inv, ha, inv_one]

theorem det_ne_one_of_neg (hV : finrank (ZMod 3) V = 3) {g : V ≃ₗ[ZMod 3] V}
    (hg : ∀ v, g v = -v) : LinearEquiv.det g ≠ 1 := by
  intro h
  have h1 : (g : V →ₗ[ZMod 3] V) = (-1 : ZMod 3) • LinearMap.id := by
    ext v
    simp [hg v]
  have h2 : LinearMap.det (g : V →ₗ[ZMod 3] V) = 1 := by
    rw [← LinearEquiv.coe_det, h, Units.val_one]
  rw [h1, LinearMap.det_smul, LinearMap.det_id, hV] at h2
  revert h2
  decide

end Linear

namespace Base

variable {A L K : Subgroup G} {c d : G}

theorem exists_moved (H : Base A c L d K) {S : Subgroup G} (hSD : SylowData A L d K S) :
    ∃ s₀ ∈ S, ∃ a₀ ∈ A, s₀ * a₀ * s₀⁻¹ ≠ a₀ := by
  by_contra hcon
  push Not at hcon
  have hle : A ⊓ L ≤ Subgroup.zpowers d := by
    intro e he
    refine hSD.mem_zpowers_of_central e (hSD.inf_le he) fun s hs => ?_
    have h1 := hcon s hs e he.1
    calc e * s = s * e * s⁻¹ * s := by rw [h1]
      _ = s * e := by group
  have := Subgroup.card_le_of_le hle
  rw [H.card_inf, Nat.card_zpowers, H.orderOf_d] at this
  norm_num at this

theorem card_B (H : Base A c L d K) :
    Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) = 9 := by
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers d, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute c d from H.comm_cd) i j).eq
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [zpowers_inf_eq_bot H.c_pow H.c_not_mem_zpowers_d, Subgroup.card_bot, mul_one,
    H.data.card_zpowers, Nat.card_zpowers, H.orderOf_d] at hcard
  exact hcard

theorem sup_zpowers_eq (H : Base A c L d K) {a₀ : G} (ha₀ : a₀ ∈ A)
    (ha₀B : a₀ ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d) :
    Subgroup.zpowers c ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a₀ = A := by
  have ha₀3 : a₀ ^ 3 = 1 := H.data.isElemAbelian.2 a₀ ha₀
  have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a₀ ≤ A :=
    sup_le H.B_le (Subgroup.zpowers_le.mpr ha₀)
  have hcomm : ∀ x ∈ Subgroup.zpowers a₀,
      ∀ y ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d, x * y = y * x := fun x hx y hy =>
    H.data.commute ((Subgroup.zpowers_le.mpr ha₀) hx) (H.B_le hy)
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [zpowers_inf_eq_bot ha₀3 ha₀B, Subgroup.card_bot, mul_one, H.card_B,
    Nat.card_zpowers, orderOf_eq_prime ha₀3 (fun h => ha₀B (h ▸ one_mem _))] at hcard
  rw [sup_comm] at hcard
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [H.data.card_eq, hcard])

theorem exists_pow_conj_eq (H : Base A c L d K) {S T : Subgroup G} (hTD : TData A c L d S T)
    {s₀ a₀ : G} (hs₀ : s₀ ∈ T) (ha₀ : a₀ ∈ A) (hmove : s₀ * a₀ * s₀⁻¹ ≠ a₀) {τ : G}
    (hτ : τ ∈ T) : ∃ k : ℕ, ∀ a ∈ A, τ * a * τ⁻¹ = s₀ ^ k * a * (s₀ ^ k)⁻¹ := by
  set δ₀ := s₀ * a₀ * s₀⁻¹ * a₀⁻¹ with hδ₀
  have hδ₀d : δ₀ ∈ Subgroup.zpowers d := hTD.conj_mem s₀ hs₀ a₀ ha₀
  have hδ₀1 : δ₀ ≠ 1 := by
    intro h
    apply hmove
    rw [hδ₀, mul_inv_eq_one] at h
    exact h
  have hδ₀3 : δ₀ ^ 3 = 1 := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hδ₀d
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, H.d_pow, one_zpow]
  have hzz : Subgroup.zpowers δ₀ = Subgroup.zpowers d :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hδ₀d) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, H.orderOf_d, orderOf_eq_prime hδ₀3 hδ₀1])
  have hδ : τ * a₀ * τ⁻¹ * a₀⁻¹ ∈ Subgroup.zpowers δ₀ := hzz ▸ hTD.conj_mem τ hτ a₀ ha₀
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hδ)
  have hs₀d : ∀ x ∈ Subgroup.zpowers d, s₀ * x = x * s₀ := by
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hTD.le_d hs₀)) j).eq
  have hpow : ∀ n : ℕ, s₀ ^ n * a₀ * (s₀ ^ n)⁻¹ = δ₀ ^ n * a₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : s₀ * δ₀ ^ n * s₀⁻¹ = δ₀ ^ n := by
        rw [hs₀d _ (pow_mem hδ₀d n), mul_inv_cancel_right]
      calc s₀ ^ (n + 1) * a₀ * (s₀ ^ (n + 1))⁻¹ = s₀ * (s₀ ^ n * a₀ * (s₀ ^ n)⁻¹) * s₀⁻¹ := by
            rw [pow_succ']; group
        _ = (s₀ * δ₀ ^ n * s₀⁻¹) * (s₀ * a₀ * s₀⁻¹) := by rw [ih]; group
        _ = δ₀ ^ (n + 1) * a₀ := by rw [h1, pow_succ, hδ₀]; group
  set ρ := (s₀ ^ k)⁻¹ * τ with hρ
  have hρa₀ : ρ * a₀ = a₀ * ρ := by
    have h1 : τ * a₀ * τ⁻¹ = s₀ ^ k * a₀ * (s₀ ^ k)⁻¹ := by
      rw [hpow k, hk]
      group
    calc ρ * a₀ = (s₀ ^ k)⁻¹ * (τ * a₀ * τ⁻¹) * τ := by rw [hρ]; group
      _ = a₀ * ρ := by rw [h1, hρ]; group
  have hρc : ρ * c = c * ρ := by
    have h1 : s₀ ^ k * c = c * s₀ ^ k :=
      (Commute.pow_left (Subgroup.mem_centralizer_singleton_iff.mp (hTD.le_c hs₀)) k).eq
    have h2 : τ * c = c * τ := Subgroup.mem_centralizer_singleton_iff.mp (hTD.le_c hτ)
    have h3 : (s₀ ^ k)⁻¹ * c = c * (s₀ ^ k)⁻¹ := (Commute.inv_left (show Commute _ c from h1)).eq
    rw [hρ, mul_assoc, h2, ← mul_assoc, h3, mul_assoc]
  have hρd : ρ * d = d * ρ := by
    have h1 : s₀ ^ k * d = d * s₀ ^ k :=
      (Commute.pow_left (Subgroup.mem_centralizer_singleton_iff.mp (hTD.le_d hs₀)) k).eq
    have h2 : τ * d = d * τ := Subgroup.mem_centralizer_singleton_iff.mp (hTD.le_d hτ)
    have h3 : (s₀ ^ k)⁻¹ * d = d * (s₀ ^ k)⁻¹ := (Commute.inv_left (show Commute _ d from h1)).eq
    rw [hρ, mul_assoc, h2, ← mul_assoc, h3, mul_assoc]
  have ha₀B : a₀ ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    intro hB
    apply hmove
    have hT := Subgroup.mem_centralizer_iff.mp
      (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun τ hτ =>
        Subgroup.mem_centralizer_singleton_iff.mp (hTD.le_c hτ)))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun τ hτ =>
        Subgroup.mem_centralizer_singleton_iff.mp (hTD.le_d hτ))) hB) s₀ hs₀
    rw [hT, mul_inv_cancel_right]
  have hAρ : A ≤ Subgroup.centralizer ({ρ} : Set G) := by
    rw [← H.sup_zpowers_eq ha₀ ha₀B]
    refine sup_le (sup_le ?_ ?_) ?_ <;>
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    · exact hρc.symm
    · exact hρd.symm
    · exact hρa₀.symm
  refine ⟨k, fun a ha => ?_⟩
  have h1 : ρ * a = a * ρ := (Subgroup.mem_centralizer_singleton_iff.mp (hAρ ha)).symm
  calc τ * a * τ⁻¹ = s₀ ^ k * (ρ * a) * ρ⁻¹ * (s₀ ^ k)⁻¹ := by rw [hρ]; group
    _ = s₀ ^ k * a * (s₀ ^ k)⁻¹ := by rw [h1]; group

end Base

namespace Hyp

variable {A L K : Subgroup G} {c d : G}

theorem exists_coords_sl2 (H : Hyp A c L d K) {S T : Subgroup G}
    (hSD : SylowData A L d K S) (hTD : TData A c L d S T) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (f : Multiplicative V ≃* A),
      finrank (ZMod 3) V = 3 ∧
      Nonempty (CFSG.GH74.GLS.oPrimeResidual 3 (wAction (G := G) f).range ≃* SL(2, ZMod 3)) ∧
      ∃ w₀ : Subgroup.normalizer (A : Set G),
        LinearMap.range ((wAction f w₀ : V →ₗ[ZMod 3] V) - 1) =
          Submodule.span (ZMod 3) {coordVec f ⟨d, H.mem_A⟩} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s₀, hs₀S, a₀, ha₀A, hmove⟩ := H.exists_moved hSD
  have hs₀T := hTD.S_le hs₀S
  have hs₀W : s₀ ∈ Subgroup.normalizer (A : Set G) := H.S_le_normalizer hSD hs₀S
  have hA27 : Nat.card A = 3 ^ 3 := by rw [H.data.card_eq]; norm_num
  obtain ⟨V, _, _, hV, ⟨f⟩⟩ := exists_coords_module H.data.isElemAbelian hA27
  set d' : A := ⟨d, H.mem_A⟩ with hd'
  have hd'1 : d' ≠ 1 := fun h => H.ne_one (congrArg Subtype.val h)
  set U := Submodule.span (ZMod 3) {coordVec f d'} with hU
  set W := Subgroup.normalizer (A : Set G) with hW
  set ψ := wAction (G := G) f with hψ
  set w₀ : W := ⟨s₀, hs₀W⟩ with hw₀
  set σ₀ := A.normalizerMonoidHom w₀ with hσ₀
  have hσ : σ₀ ∈ transvectionGroup A d' := by
    refine ⟨Subtype.ext ?_, fun a => ?_⟩
    · show s₀ * d * s₀⁻¹ = d
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hTD.le_d hs₀T), mul_inv_cancel_right]
    · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hTD.conj_mem s₀ hs₀T a a.2)
      refine Subgroup.mem_zpowers_iff.mpr ⟨j, Subtype.ext ?_⟩
      rw [Subgroup.coe_zpow, hj]
      rfl
  have hσ1 : σ₀ ≠ 1 := by
    intro h
    apply hmove
    have := congrArg (fun φ : MulAut A => ((φ ⟨a₀, ha₀A⟩ : A) : G)) h
    simp only [MulAut.one_apply] at this
    exact this
  obtain ⟨hrt, hrU⟩ := coordHom_isTransvection f hd'1 hσ hσ1
  set r := ψ w₀ with hr
  have hrσ : r = coordHom f σ₀ := rfl
  rw [← hrσ] at hrt hrU
  have hTW : T ≤ W := fun τ hτ => (hTD.isSylowOf.le hτ).1
  have hTstar : (T.subgroupOf W).map ψ = Subgroup.zpowers r := by
    apply le_antisymm
    · rintro _ ⟨τ, hτ, rfl⟩
      obtain ⟨k, hk⟩ := H.exists_pow_conj_eq hTD hs₀T ha₀A hmove (Subgroup.mem_subgroupOf.mp hτ)
      have h1 : ψ τ = ψ (w₀ ^ k) := wAction_eq_of_conj_eq f fun a ha => by
        rw [hk a ha, Subgroup.coe_pow]
      rw [h1, map_pow]
      exact Subgroup.npow_mem_zpowers r k
    · rw [Subgroup.zpowers_le]
      exact ⟨w₀, Subgroup.mem_subgroupOf.mpr hs₀T, rfl⟩
  have hT' : IsSylowOf 3 T (W ⊓ Subgroup.centralizer ({d} : Set G)) :=
    hTD.isSylowOf.of_le (le_inf hTW hTD.le_d)
      (inf_le_inf_left _ fun x hx => mem_normalizer_zpowers_of_mem_centralizer hx)
  have hT'W : IsSylowOf 3 (T.subgroupOf W)
      ((W ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf W) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff W, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTW, inf_eq_left.mpr inf_le_left]
    exact hT'
  have himage : ((W ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf W).map ψ =
      ψ.range ⊓ fixingSubgroup (V ≃ₗ[ZMod 3] V) (U : Set V) := by
    ext g
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨⟨w, rfl⟩, Sec3.mem_fixingSubgroup_span_iff.mpr ?_⟩
      have hwd : (w : G) * d * (w : G)⁻¹ = d := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hw).2,
          mul_inv_cancel_right]
      exact (wAction_coordVec_eq_iff f w d').mpr hwd
    · rintro ⟨⟨w, rfl⟩, hfix⟩
      have h1 := (wAction_coordVec_eq_iff f w d').mp (Sec3.mem_fixingSubgroup_span_iff.mp hfix)
      refine ⟨w, Subgroup.mem_subgroupOf.mpr ⟨w.2, ?_⟩, rfl⟩
      show (w : G) ∈ Subgroup.centralizer ({d} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (w : G) * d = (w : G) * d * (w : G)⁻¹ * w := by group
        _ = d * w := by rw [h1]
  have hsyl : IsSylowOf 3 (Subgroup.zpowers r)
      (ψ.range ⊓ fixingSubgroup (V ≃ₗ[ZMod 3] V) (U : Set V)) := by
    rw [← hTstar, ← himage]
    exact CFSG.RankThree.PartTwo.Sec12.IsSylowOf.map hT'W ψ
  have : FiniteDimensional (ZMod 3) V := FiniteDimensional.of_finrank_pos (by omega)
  rcases Sec3.rank3II_3_14 hV ψ.range ⟨w₀, rfl⟩ hrt hrU.symm hsyl with hN | hSL
  · exfalso
    apply H.not_le
    intro w hw
    exact mem_normalizer_zpowers_of_map_eq f d' ⟨w, hw⟩ (hN _ ⟨⟨w, hw⟩, rfl⟩)
  · exact ⟨V, inferInstance, inferInstance, f, hV, hSL, w₀, hrU⟩

theorem exists_central_involution (H : Hyp A c L d K) {S T : Subgroup G}
    (hSD : SylowData A L d K S) (hTD : TData A c L d S T) :
    ∃ x₀ ∈ Subgroup.normalizer (A : Set G),
      x₀ ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) ∧
      (∀ a ∈ A, (x₀ * x₀) * a * (x₀ * x₀)⁻¹ = a) ∧
      (∃ a ∈ A, x₀ * a * x₀⁻¹ ≠ a) ∧
      (∃ a ∈ A, x₀ * a * x₀⁻¹ ≠ a⁻¹) ∧
      ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ a ∈ A,
        (w * x₀ * w⁻¹) * a * (w * x₀ * w⁻¹)⁻¹ = x₀ * a * x₀⁻¹ := by
  obtain ⟨V, _, _, f, hV, ⟨e⟩, w₀, hrU⟩ := H.exists_coords_sl2 hSD hTD
  set ψ := wAction (G := G) f with hψ
  set O := CFSG.GH74.GLS.oPrimeResidual 3 ↥ψ.range with hO
  have hOn : O.Normal := oPrimeResidual_three_normal _
  obtain ⟨z, hz, hz1⟩ := sl2_three_exists_involution
  set xb₀ : O := e.symm z with hxb₀
  have hxb₀sq : xb₀ * xb₀ = 1 := by rw [hxb₀, ← map_mul, hz, map_one]
  have hxb₀1 : xb₀ ≠ 1 := fun h => hz1 (by rw [← e.apply_symm_apply z, ← hxb₀, h, map_one])
  set xb₁ : ↥ψ.range := (xb₀ : ↥ψ.range) with hxb₁
  have hxb₁sq : xb₁ * xb₁ = 1 := by
    rw [hxb₁, ← Subgroup.coe_mul, hxb₀sq, Subgroup.coe_one]
  have hxb₁1 : xb₁ ≠ 1 := fun h => hxb₀1 (Subtype.ext h)
  have hcent : ∀ g : ↥ψ.range, g * xb₁ * g⁻¹ = xb₁ := by
    intro g
    have hmem : g * xb₁ * g⁻¹ ∈ O := hOn.conj_mem _ xb₀.2 g
    set y₀ : O := ⟨g * xb₁ * g⁻¹, hmem⟩ with hy₀
    have hy₀sq : y₀ * y₀ = 1 := by
      apply Subtype.ext
      change g * xb₁ * g⁻¹ * (g * xb₁ * g⁻¹) = 1
      calc g * xb₁ * g⁻¹ * (g * xb₁ * g⁻¹) = g * (xb₁ * xb₁) * g⁻¹ := by group
        _ = 1 := by rw [hxb₁sq]; group
    have hy₀1 : y₀ ≠ 1 := by
      intro h
      apply hxb₁1
      have h1 : g * xb₁ * g⁻¹ = 1 := congrArg Subtype.val h
      calc xb₁ = g⁻¹ * (g * xb₁ * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have hey : e y₀ = z := sl2_three_eq_of_mul_self (by rw [← map_mul, hy₀sq, map_one])
      (fun h => hy₀1 (e.injective (h.trans (map_one e).symm))) hz hz1
    have hyx : y₀ = xb₀ := by rw [hxb₀, ← hey, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val hyx
  obtain ⟨x₀', hx₀'⟩ := xb₁.2
  set xb : V ≃ₗ[ZMod 3] V := (xb₁ : V ≃ₗ[ZMod 3] V) with hxb
  have hψx : ψ x₀' = xb := hx₀'
  refine ⟨x₀', x₀'.2, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hcomm : xb * ψ w₀ * xb⁻¹ = ψ w₀ := by
      have h1 := hcent ⟨ψ w₀, ⟨w₀, rfl⟩⟩
      have h2 : ψ w₀ * xb * (ψ w₀)⁻¹ = xb := congrArg Subtype.val h1
      calc xb * ψ w₀ * xb⁻¹ = xb * (ψ w₀ * xb * (ψ w₀)⁻¹)⁻¹ * ψ w₀ := by group
        _ = ψ w₀ := by rw [h2]; group
    have h1 := range_conj_sub_one xb (ψ w₀)
    rw [hcomm, hrU] at h1
    exact mem_normalizer_zpowers_of_map_eq f ⟨d, H.mem_A⟩ x₀' (by rw [hψx]; exact h1.symm)
  ·
    intro a ha
    have h1 : ψ (x₀' * x₀') = ψ 1 := by
      rw [map_mul, hψx, map_one]
      exact congrArg Subtype.val hxb₁sq
    have h2 := conj_eq_of_wAction_eq f h1 a ha
    simpa using h2
  ·
    by_contra hcon
    push Not at hcon
    apply hxb₁1
    have h1 : ψ x₀' = ψ 1 := wAction_eq_of_conj_eq f fun a ha => by simpa using hcon a ha
    rw [map_one, hψx] at h1
    exact Subtype.ext h1
  ·
    by_contra hcon
    push Not at hcon
    have hneg : ∀ v, xb v = -v := by
      intro v
      set a := f (Multiplicative.ofAdd v) with ha
      have h1 := coe_wAction_coordVec f x₀' a
      rw [hcon a a.2, hψx] at h1
      have hcv : coordVec f a = v := by simp [coordVec, ha]
      rw [hcv] at h1
      have h2 : f (Multiplicative.ofAdd (xb v)) = f (Multiplicative.ofAdd (-v)) := by
        apply Subtype.ext
        rw [h1, ofAdd_neg, map_inv, Subgroup.coe_inv]
      exact Multiplicative.ofAdd.injective (f.injective h2)
    exact det_ne_one_of_neg hV hneg (det_eq_one_of_mem_oPrimeResidual xb₀.2)
  ·
    intro w hw a ha
    have h1 : ψ (⟨w, hw⟩ * x₀' * ⟨w, hw⟩⁻¹) = ψ x₀' := by
      rw [map_mul, map_mul, map_inv, hψx]
      have h2 := hcent ⟨ψ ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩⟩
      exact congrArg Subtype.val h2
    have h2 := conj_eq_of_wAction_eq f h1 a ha
    simpa using h2

end Hyp

end CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof
