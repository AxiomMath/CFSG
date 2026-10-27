module

public import CFSG.Quasithin.Vol2.Ch11SecBK6I
public import CFSG.Quasithin.Vol2.Ch11SecBK6C
public import CFSG.Quasithin.Vol2.Ch11SecBK6H

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL coe_uSL)
open scoped commutatorElement

namespace BK6

theorem sl3_act_formula {K : Type} [Field K] {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H}
    {f : W → (Fin 3 → K)} (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K) (b c : K) (w : W) :
    ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        f (((rho3 π (g * uSL 0 b c * g⁻¹) : ↥H) : MulAut W) w) =
      ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w +
        (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w) 2 •
          ![b, c, 0] := by
  rw [hf.act3, gconj_mulVec, ginv_g_mulVec, coe_uSL, uMat_mulVec]
  refine KGNat.vec3_eq ?_ ?_ ?_ <;> simp <;> ring

section Tools

variable {G : Type} [Group G] {V : Subgroup G}

theorem coord_mul_inv {M : Type*} [AddGroup M] {x : ↥V → M}
    (hmul : ∀ u u' : ↥V, x (u * u') = x u + x u') (u v : ↥V) :
    x (u * v⁻¹) = x u - x v := by
  rw [eq_sub_iff_add_eq, ← hmul, inv_mul_cancel_right]

theorem exists_line_subgroup (K : Type*) {M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {x : ↥V → M} (hmul : ∀ u u' : ↥V, x (u * u') = x u + x u') (d : M) :
    ∃ P : Subgroup G, P ≤ V ∧ ∀ w : ↥V, (w : G) ∈ P ↔ ∃ μ : K, x w = μ • d := by
  have h1 : x 1 = 0 := by
    have h := hmul 1 1
    rwa [mul_one, left_eq_add] at h
  let Q : Subgroup ↥V :=
    { carrier := {w | ∃ μ : K, x w = μ • d}
      mul_mem' := fun {u u'} ⟨μ, hμ⟩ ⟨μ', hμ'⟩ => ⟨μ + μ', by rw [hmul, hμ, hμ', add_smul]⟩
      one_mem' := ⟨0, by rw [h1, zero_smul]⟩
      inv_mem' := fun {u} ⟨μ, hμ⟩ => ⟨-μ, by
        rw [← one_mul u⁻¹, coord_mul_inv hmul, h1, hμ, zero_sub, neg_smul]⟩ }
  refine ⟨Q.map V.subtype, Subgroup.map_subtype_le Q, fun w => ⟨?_, fun h => ⟨w, h, rfl⟩⟩⟩
  rintro ⟨w', hw', he⟩
  rwa [Subtype.ext he] at hw'

theorem relIndex_eq_card_of_hom {M : Type*} [AddCommGroup M] {C : Subgroup G} (φ : ↥V → M)
    (hφ : ∀ u u' : ↥V, φ (u * u') = φ u + φ u') (hsurj : Function.Surjective φ)
    (hC : ∀ w : ↥V, (w : G) ∈ C ↔ φ w = 0) : C.relIndex V = Nat.card M := by
  have h1 : φ 1 = 0 := by
    have h := hφ 1 1
    rwa [mul_one, left_eq_add] at h
  let χ : ↥V →* Multiplicative M :=
    { toFun := fun v => Multiplicative.ofAdd (φ v)
      map_one' := by rw [h1]; rfl
      map_mul' := fun a b => by rw [hφ]; rfl }
  have hker : χ.ker = C.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hC]
    exact ofAdd_eq_one
  have hsurj' : Function.Surjective χ := fun t => by
    obtain ⟨w, hw⟩ := hsurj (Multiplicative.toAdd t)
    exact ⟨w, by change Multiplicative.ofAdd (φ w) = t; rw [hw]; rfl⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj',
    Subgroup.card_top]
  rfl

theorem conjV_eq_self {a : G} (ha : a ∈ Subgroup.normalizer (V : Set G)) {v : ↥V}
    (hv : a * v = v * a) : SecA.conjV V a ha v = v :=
  Subtype.ext (by rw [SecA.conjV_apply_coe, hv, mul_inv_cancel_right])

theorem mul_comm_of_conjV_eq {a : G} (ha : a ∈ Subgroup.normalizer (V : Set G)) {v : ↥V}
    (h : SecA.conjV V a ha v = v) : a * v = v * a := by
  have h1 := congrArg Subtype.val h
  rw [SecA.conjV_apply_coe] at h1
  calc a * (v : G) = a * v * a⁻¹ * a := by group
    _ = v * a := by rw [h1]

end Tools

section CoordSL3

variable {G : Type} [Group G] {L V A V₂ : Subgroup G} {K : Type} [Field K]
  {x : ↥V → (Fin 3 → K)}

theorem coord_comm {hAV : A ≤ Subgroup.normalizer (V : Set G)} {b c : ↥A → K}
    (hmul : ∀ u u' : ↥V, x (u * u') = x u + x u')
    (hact : ∀ (a : ↥A) (w : ↥V),
      x (SecA.conjV V a (hAV a.2) w) = x w + x w 2 • ![b a, c a, 0]) (a : ↥A) (w : ↥V) :
    x (w * (SecA.conjV V a (hAV a.2) w)⁻¹) = (-x w 2) • ![b a, c a, 0] := by
  rw [coord_mul_inv hmul, hact, sub_add_cancel_left, neg_smul]

theorem inf_centralizer_eq_of_coord {hAV : A ≤ Subgroup.normalizer (V : Set G)} {b c : ↥A → K}
    (hact : ∀ (a : ↥A) (w : ↥V),
      x (SecA.conjV V a (hAV a.2) w) = x w + x w 2 • ![b a, c a, 0])
    (hV₂ : ∀ w : ↥V, (w : G) ∈ V₂ ↔ x w 2 = 0)
    (hV₂C : V₂ ≤ V ⊓ Subgroup.centralizer (A : Set G)) {a₀ : ↥A}
    (h₀ : (![b a₀, c a₀, 0] : Fin 3 → K) ≠ 0) :
    V ⊓ Subgroup.centralizer (A : Set G) = V₂ := by
  refine le_antisymm (fun v hv => ?_) hV₂C
  obtain ⟨hvV, hvA⟩ := Subgroup.mem_inf.mp hv
  have hfix : SecA.conjV V a₀ (hAV a₀.2) ⟨v, hvV⟩ = ⟨v, hvV⟩ := by
    apply Subtype.ext
    rw [SecA.conjV_apply_coe]
    change (a₀ : G) * v * (a₀ : G)⁻¹ = v
    rw [Subgroup.mem_centralizer_iff.mp hvA a₀ a₀.2, mul_inv_cancel_right]
  have h := hact a₀ ⟨v, hvV⟩
  rw [hfix, left_eq_add, smul_eq_zero] at h
  exact (hV₂ ⟨v, hvV⟩).mpr (h.resolve_right h₀)

theorem sup_comm_eq_plane {hAV : A ≤ Subgroup.normalizer (V : Set G)} {b c : ↥A → K}
    (hmul : ∀ u u' : ↥V, x (u * u') = x u + x u')
    (hker : ∀ u : ↥V, x u = 0 ↔ (u : G) ∈ Subgroup.centralizer (L : Set G))
    (hsurj : Function.Surjective x)
    (hact : ∀ (a : ↥A) (w : ↥V),
      x (SecA.conjV V a (hAV a.2) w) = x w + x w 2 • ![b a, c a, 0])
    (hV₂V : V₂ ≤ V) (hV₂ : ∀ w : ↥V, (w : G) ∈ V₂ ↔ x w 2 = 0) {a₁ a₂ : ↥A}
    (hΔ : b a₁ * c a₂ - b a₂ * c a₁ ≠ 0) :
    ⁅V, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V₂ := by
  refine sup_commutator_eq_of (fun v hv => ?_) (fun v hv a ha => ?_) (fun q hq => ?_)
  · obtain ⟨hvV, hvL⟩ := Subgroup.mem_inf.mp hv
    refine (hV₂ ⟨v, hvV⟩).mpr ?_
    rw [(hker ⟨v, hvV⟩).mpr hvL]
    rfl
  · rw [commutatorElement_eq (hAV ha) ⟨v, hv⟩, hV₂, coord_comm hmul hact ⟨a, ha⟩ ⟨v, hv⟩]
    simp
  · have hu2 : x ⟨q, hV₂V hq⟩ 2 = 0 := (hV₂ ⟨q, hV₂V hq⟩).mp hq
    obtain ⟨l₁, l₂, h₁, h₂⟩ : ∃ l₁ l₂ : K, l₁ * b a₁ + l₂ * b a₂ = x ⟨q, hV₂V hq⟩ 0 ∧
        l₁ * c a₁ + l₂ * c a₂ = x ⟨q, hV₂V hq⟩ 1 :=
      ⟨(x ⟨q, hV₂V hq⟩ 0 * c a₂ - x ⟨q, hV₂V hq⟩ 1 * b a₂) / (b a₁ * c a₂ - b a₂ * c a₁),
        (x ⟨q, hV₂V hq⟩ 1 * b a₁ - x ⟨q, hV₂V hq⟩ 0 * c a₁) / (b a₁ * c a₂ - b a₂ * c a₁),
        by linear_combination x ⟨q, hV₂V hq⟩ 0 * inv_mul_cancel₀ hΔ,
        by linear_combination x ⟨q, hV₂V hq⟩ 1 * inv_mul_cancel₀ hΔ⟩
    obtain ⟨w₁, hw₁⟩ := hsurj ![0, 0, -l₁]
    obtain ⟨w₂, hw₂⟩ := hsurj ![0, 0, -l₂]
    refine ⟨((w₁ * (SecA.conjV V a₁ (hAV a₁.2) w₁)⁻¹ *
      (w₂ * (SecA.conjV V a₂ (hAV a₂.2) w₂)⁻¹) : ↥V) : G), ?_, ?_⟩
    · rw [Subgroup.coe_mul, ← commutatorElement_eq, ← commutatorElement_eq]
      exact mul_mem (Subgroup.commutator_mem_commutator w₁.2 a₁.2)
        (Subgroup.commutator_mem_commutator w₂.2 a₂.2)
    · have h0 : x (⟨q, hV₂V hq⟩ * (w₁ * (SecA.conjV V a₁ (hAV a₁.2) w₁)⁻¹ *
          (w₂ * (SecA.conjV V a₂ (hAV a₂.2) w₂)⁻¹))⁻¹) = 0 := by
        rw [coord_mul_inv hmul, hmul, coord_comm hmul hact, coord_comm hmul hact, hw₁, hw₂,
          sub_eq_zero]
        refine funext fun i => ?_
        fin_cases i <;> simp [hu2]
        · linear_combination h₁.symm
        · linear_combination h₂.symm
      exact Subgroup.mem_inf.mpr ⟨mul_mem (hV₂V hq) (inv_mem (SetLike.coe_mem _)), (hker _).mp h0⟩

theorem sup_comm_eq_line {hAV : A ≤ Subgroup.normalizer (V : Set G)} {b c : ↥A → K}
    (hmul : ∀ u u' : ↥V, x (u * u') = x u + x u')
    (hker : ∀ u : ↥V, x u = 0 ↔ (u : G) ∈ Subgroup.centralizer (L : Set G))
    (hsurj : Function.Surjective x)
    (hact : ∀ (a : ↥A) (w : ↥V),
      x (SecA.conjV V a (hAV a.2) w) = x w + x w 2 • ![b a, c a, 0]) {a₀ : ↥A}
    (hd : ∀ a : ↥A, ∃ t : K, (![b a, c a, 0] : Fin 3 → K) = t • ![b a₀, c a₀, 0])
    {P : Subgroup G} (hPV : P ≤ V)
    (hP : ∀ w : ↥V, (w : G) ∈ P ↔ ∃ μ : K, x w = μ • ![b a₀, c a₀, 0]) :
    ⁅V, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = P := by
  refine sup_commutator_eq_of (fun v hv => ?_) (fun v hv a ha => ?_) (fun q hq => ?_)
  · obtain ⟨hvV, hvL⟩ := Subgroup.mem_inf.mp hv
    exact (hP ⟨v, hvV⟩).mpr ⟨0, by rw [(hker ⟨v, hvV⟩).mpr hvL, zero_smul]⟩
  · obtain ⟨t, ht⟩ := hd ⟨a, ha⟩
    rw [commutatorElement_eq (hAV ha) ⟨v, hv⟩, hP, coord_comm hmul hact ⟨a, ha⟩ ⟨v, hv⟩, ht,
      smul_smul]
    exact ⟨_, rfl⟩
  · obtain ⟨μ, hμ⟩ := (hP ⟨q, hPV hq⟩).mp hq
    obtain ⟨w, hw⟩ := hsurj ![0, 0, -μ]
    refine ⟨((w * (SecA.conjV V a₀ (hAV a₀.2) w)⁻¹ : ↥V) : G), ?_, ?_⟩
    · rw [← commutatorElement_eq]
      exact Subgroup.commutator_mem_commutator w.2 a₀.2
    · have h0 : x (⟨q, hPV hq⟩ * (w * (SecA.conjV V a₀ (hAV a₀.2) w)⁻¹)⁻¹) = 0 := by
        rw [coord_mul_inv hmul, coord_comm hmul hact, hw, hμ, sub_eq_zero]
        simp
      exact Subgroup.mem_inf.mpr ⟨mul_mem (hPV hq) (inv_mem (SetLike.coe_mem _)), (hker _).mp h0⟩

theorem relIndex_le_of_line [Finite K] {hAV : A ≤ Subgroup.normalizer (V : Set G)}
    {b c : ↥A → K} (hsurj : Function.Surjective x)
    (hact : ∀ (a : ↥A) (w : ↥V),
      x (SecA.conjV V a (hAV a.2) w) = x w + x w 2 • ![b a, c a, 0]) {a₀ : ↥A}
    (h₀ : b a₀ ≠ 0 ∨ c a₀ ≠ 0)
    (hd : ∀ a : ↥A, ∃ t : K, (![b a, c a, 0] : Fin 3 → K) = t • ![b a₀, c a₀, 0])
    (hone : ∀ a : ↥A, b a = 0 → c a = 0 → (a : G) ∈ Subgroup.centralizer (V : Set G)) :
    (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ Nat.card K := by
  obtain ⟨w, hw⟩ := hsurj ![0, 0, 1]
  have hadd : ∀ a a' : ↥A, b (a * a') = b a + b a' ∧ c (a * a') = c a + c a' := by
    intro a a'
    have h1 := hact (a * a') w
    rw [show SecA.conjV V ((a * a' : ↥A) : G) (hAV (a * a').2) =
        SecA.conjV V a (hAV a.2) * SecA.conjV V a' (hAV a'.2) from SecA.conjV_mul V _ _,
      MulAut.mul_apply, hact, hact, hw] at h1
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    simp at e0 e1
    exact ⟨by linear_combination -e0, by linear_combination -e1⟩
  obtain ⟨u, v, huv⟩ : ∃ u v : K, u * b a₀ + v * c a₀ = 1 := by
    rcases h₀ with h | h
    · exact ⟨(b a₀)⁻¹, 0, by rw [zero_mul, add_zero, inv_mul_cancel₀ h]⟩
    · exact ⟨0, (c a₀)⁻¹, by rw [zero_mul, zero_add, inv_mul_cancel₀ h]⟩
  refine relIndex_le_of_hom (fun a => u * b a + v * c a)
    (fun a a' => by rw [(hadd a a').1, (hadd a a').2]; ring) (fun a ha => ?_)
  obtain ⟨t, ht⟩ := hd a
  have hb : b a = t * b a₀ := by simpa using congrFun ht 0
  have hc : c a = t * c a₀ := by simpa using congrFun ht 1
  have ht0 : t = 0 := by
    have h : u * b a + v * c a = t := by rw [hb, hc]; linear_combination t * huv
    rw [← h]
    exact ha
  exact Subgroup.mem_inf.mpr ⟨a.2, hone a (by rw [hb, ht0, zero_mul])
    (by rw [hc, ht0, zero_mul])⟩

end CoordSL3

end BK6

end CFSG.Quasithin.Vol2.Ch11.SecB
