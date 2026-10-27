module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem11
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem12

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section Field

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem sub_mem_of_not_mem {H : AddSubgroup K} {α : K} (hcos : ∀ x, x ∈ H ∨ x + α ∈ H)
    {x x' : K} (hx : x ∉ H) (hx' : x' ∉ H) : x - x' ∈ H := by
  have h1 := (hcos x).resolve_left hx
  have h2 := (hcos x').resolve_left hx'
  have e : x - x' = (x + α) - (x' + α) := by ring
  rw [e]
  exact H.sub_mem h1 h2

theorem exists_mul_not_mem {H : AddSubgroup K} {α : K} (hα : α ∉ H)
    (hcos : ∀ x, x ∈ H ∨ x + α ∈ H) {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ∃ h ∈ H, c * h ∉ H := by
  by_contra hcon
  push Not at hcon
  have key : ∀ d : K, d ≠ 0 → (∀ h ∈ H, d * h ∈ H) → d * α ∈ H → False := by
    intro d hd hdH hdα
    have hall : ∀ x, d * x ∈ H := by
      intro x
      rcases hcos x with hx | hx
      · exact hdH x hx
      · have e : d * x = d * (x + α) - d * α := by ring
        rw [e]
        exact H.sub_mem (hdH _ hx) hdα
    apply hα
    have := hall (d⁻¹ * α)
    rwa [← mul_assoc, mul_inv_cancel₀ hd, one_mul] at this
  by_cases hcα : c * α ∈ H
  · exact key c hc0 hcon hcα
  · have h1 : c * α + α ∈ H := (hcos (c * α)).resolve_left hcα
    have hd : c + 1 ≠ 0 := by
      intro h0
      apply hc1
      have : c = -1 := eq_neg_of_add_eq_zero_left h0
      rw [this, CharTwo.neg_eq]
    refine key (c + 1) hd (fun h hh => ?_) (by rw [add_mul, one_mul]; exact h1)
    rw [add_mul, one_mul]
    exact H.add_mem (hcon h hh) hh

end Field

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem sq_mem_centralizer (h : Hyp611Nat G T M L V n) {s : G} (hs : s ∈ ch6S T L V) :
    s ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
  have := charP_two_of_two_dvd h.two_dvd_card_K
  obtain ⟨v, hv, hle⟩ := h.exists_line
  obtain ⟨A, hA, hAeq⟩ := h.exists_stab_of_mem_S hv hle hs
  set m : Subgroup.normalizer (V : Set G) := ⟨s, h.toHyp611.T_le_normalizer hs.1⟩ with hm
  have hmm := h.data.mem_centralizer_of_conj_eq (m * m) fun w => by
    rw [h.data.conj_mul, hAeq, hAeq]
    obtain ⟨c, hc⟩ := sub_mem_line_of_mem_sl2Stab hv hA w
    have hAw : (A : Matrix (Fin 2) (Fin 2) h.data.K).mulVec w = w + c • v := by
      rw [← hc]; abel
    rw [hAw, Matrix.mulVec_add, Matrix.mulVec_smul, mem_sl2Stab.mp hA, hAw, add_assoc,
      ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  have e : ((m * m : Subgroup.normalizer (V : Set G)) : G) = s ^ 2 := by
    rw [Subgroup.coe_mul, hm, pow_two]
  rwa [e] at hmm

theorem commutator_zpowers_eq (h : Hyp611Nat G T M L V n) {s : G} (hs : s ∈ ch6S T L V)
    (hsV : s ∉ Subgroup.centralizer (V : Set G)) :
    ⁅V, Subgroup.zpowers s⁆ = ch6ZS T L V := by
  refine le_antisymm ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hs)).trans
    h.commutator_V_S_le) fun z hz => ?_
  obtain ⟨x, hx, hxz⟩ := h.exists_commutator_eq hs hsV hz
  rw [← hxz]
  exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers s)

theorem card_commutator_mul (h : Hyp611Nat G T M L V n) {s : G} (hs : s ∈ ch6S T L V)
    (hsV : s ∉ Subgroup.centralizer (V : Set G)) {Y : Subgroup G} (hZY : ch6ZS T L V ≤ Y)
    (hYV : Y ≤ V) :
    Nat.card ↥⁅Y, Subgroup.zpowers s⁆ * Nat.card (ch6ZS T L V) = Nat.card Y := by
  have hV := h.toHyp611.isElemAbelian
  have hsN : s ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.T_le_normalizer hs.1
  have hs2 := h.sq_mem_centralizer hs
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    B2F.isElemAbelian_comm hV hx hy
  have hconjV : ∀ y ∈ V, s * y⁻¹ * s⁻¹ ∈ V := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hsN _).mp (V.inv_mem hy)
  let φ : ↥Y →* G := MonoidHom.mk' (fun y => ⁅(y : G), s⁆) (by
    intro a b
    have ha := hYV a.2
    have hb := hYV b.2
    simp only [Subgroup.coe_mul, commutatorElement_def]
    calc (a : G) * b * s * ((a : G) * b)⁻¹ * s⁻¹ =
        a * ((b * (s * (b : G)⁻¹ * s⁻¹)) * (s * (a : G)⁻¹ * s⁻¹)) := by group
      _ = a * ((s * (a : G)⁻¹ * s⁻¹) * (b * (s * (b : G)⁻¹ * s⁻¹))) := by
        rw [hcomm _ (V.mul_mem hb (hconjV _ hb)) _ (hconjV _ ha)]
      _ = a * s * (a : G)⁻¹ * s⁻¹ * (b * s * (b : G)⁻¹ * s⁻¹) := by group)
  have hφ : ∀ y : ↥Y, φ y = ⁅(y : G), s⁆ := fun y => rfl
  have hrange : φ.range = ⁅Y, Subgroup.zpowers s⁆ := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      exact Subgroup.commutator_mem_commutator y.2 (Subgroup.mem_zpowers s)
    · rw [Subgroup.commutator_le]
      intro y hy g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hyV := hYV hy
      obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
      · have hc : s ^ (2 * j) ∈ Subgroup.centralizer (V : Set G) := by
          rw [zpow_mul]
          exact Subgroup.zpow_mem _ (by rw [zpow_ofNat]; exact hs2) j
        have e : ⁅y, s ^ (2 * j)⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact Subgroup.mem_centralizer_iff.mp hc y hyV
        rw [e]
        exact φ.range.one_mem
      · have hc : s ^ (2 * j) ∈ Subgroup.centralizer (V : Set G) := by
          rw [zpow_mul]
          exact Subgroup.zpow_mem _ (by rw [zpow_ofNat]; exact hs2) j
        refine ⟨⟨y, hy⟩, ?_⟩
        rw [hφ]
        show ⁅y, s⁆ = ⁅y, s ^ (2 * j + 1)⁆
        have hcy : s ^ (2 * j) * y = y * s ^ (2 * j) :=
          (Subgroup.mem_centralizer_iff.mp hc y hyV).symm
        have hcw : s ^ (2 * j) * (s * y⁻¹ * s⁻¹) = (s * y⁻¹ * s⁻¹) * s ^ (2 * j) :=
          (Subgroup.mem_centralizer_iff.mp hc _ (hconjV y hyV)).symm
        rw [zpow_add, zpow_one, commutatorElement_def, commutatorElement_def]
        calc y * s * y⁻¹ * s⁻¹ = y * (s * y⁻¹ * s⁻¹) := by group
          _ = y * ((s * y⁻¹ * s⁻¹) * s ^ (2 * j)) * (s ^ (2 * j))⁻¹ := by group
          _ = y * (s ^ (2 * j) * (s * y⁻¹ * s⁻¹)) * (s ^ (2 * j))⁻¹ := by rw [hcw]
          _ = y * (s ^ (2 * j) * s) * y⁻¹ * (s ^ (2 * j) * s)⁻¹ := by group
  have hker : φ.ker = (ch6ZS T L V).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, hφ, commutatorElement_eq_one_iff_mul_comm, Subgroup.mem_subgroupOf,
      ← h.centralizer_singleton_eq_ZS hs hsV]
    constructor
    · intro hy
      refine ⟨hYV y.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      rw [Set.mem_singleton_iff.mp hx]
      exact hy.symm
    · rintro ⟨-, hy⟩
      exact (Subgroup.mem_centralizer_iff.mp hy s rfl).symm
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY).toEquiv] at h1
  exact h1.symm

theorem exists_transvection (h : Hyp611Nat G T M L V n) {v : Fin 2 → h.data.K} (hv : v ≠ 0)
    (hle : h.rhoTL ≤ sl2Stab v) {B : Matrix.SpecialLinearGroup (Fin 2) h.data.K}
    (hB : (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec ![1, 0] = v) {s : G}
    (hs : s ∈ ch6S T L V) :
    ∃ b : h.data.K, ∀ w, h.data.conj ⟨s, h.toHyp611.T_le_normalizer hs.1⟩ w =
      w + (b * ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
        Matrix (Fin 2) (Fin 2) h.data.K).mulVec w 1) • v := by
  obtain ⟨A, hA, hAeq⟩ := h.exists_stab_of_mem_S hv hle hs
  obtain ⟨b, rfl⟩ := (mem_sl2Stab_iff hB A).mp hA
  refine ⟨b, fun w => ?_⟩
  rw [hAeq, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  set u := ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
    Matrix (Fin 2) (Fin 2) h.data.K).mulVec w with hu
  have hw : (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec u = w := mulVec_inv_mulVec B w
  have hX : (sl2X b : Matrix (Fin 2) (Fin 2) h.data.K).mulVec u = u + (b * u 1) • ![1, 0] := by
    rw [sl2X_mulVec]
    funext i
    fin_cases i <;> simp
  rw [hX, Matrix.mulVec_add, Matrix.mulVec_smul, hB, hw]

theorem toAdd_E_commutator (h : Hyp611Nat G T M L V n) {v : Fin 2 → h.data.K}
    {f : (Fin 2 → h.data.K) →+ h.data.K} {s : G} (hs : s ∈ ch6S T L V) {b : h.data.K}
    (hb : ∀ w, h.data.conj ⟨s, h.toHyp611.T_le_normalizer hs.1⟩ w = w + (b * f w) • v)
    {y : G} (hy : y ∈ V) (hyc : ⁅y, s⁆ ∈ V) :
    Multiplicative.toAdd (h.data.E ⟨⁅y, s⁆, hyc⟩) =
      (b * f (Multiplicative.toAdd (h.data.E ⟨y, hy⟩))) • v := by
  have : CharP h.data.K 2 := charP_two_of_two_dvd h.two_dvd_card_K
  have hsN : s ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.T_le_normalizer hs.1
  have hy' : s * y⁻¹ * s⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hsN _).mp (V.inv_mem hy)
  have hsplit : (⟨⁅y, s⁆, hyc⟩ : ↥V) = ⟨y, hy⟩ * ⟨s * y⁻¹ * s⁻¹, hy'⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def]
    group
  have hconj : Multiplicative.toAdd (h.data.E ⟨s * y⁻¹ * s⁻¹, hy'⟩) =
      h.data.conj ⟨s, hsN⟩ (Multiplicative.toAdd (h.data.E ⟨y⁻¹, V.inv_mem hy⟩)) := by
    rw [h.data.conj_apply]
    congr 2
  have hinv : Multiplicative.toAdd (h.data.E ⟨y⁻¹, V.inv_mem hy⟩) =
      -Multiplicative.toAdd (h.data.E ⟨y, hy⟩) := by
    rw [show (⟨y⁻¹, V.inv_mem hy⟩ : ↥V) = (⟨y, hy⟩ : ↥V)⁻¹ from rfl, map_inv]
    rfl
  rw [hsplit, map_mul, toAdd_mul, hconj, hinv, hb, map_neg, mul_neg, neg_smul]
  have e : ∀ x : Fin 2 → h.data.K, -x = x := fun x => by
    funext i
    exact CharTwo.neg_eq (x i)
  rw [e, e]
  have e2 : ∀ x y : Fin 2 → h.data.K, x + (x + y) = y := fun x y => by
    rw [← add_assoc, show x + x = 0 from by funext i; exact CharTwo.add_self_eq_zero (x i),
      zero_add]
  exact e2 _ _

theorem ZS_le_commutator_of_ne (h : Hyp611Nat G T M L V n) {Y : Subgroup G}
    (hZY : ch6ZS T L V ≤ Y) (hY2 : Y.relIndex V = 2) {S₀ : Subgroup G}
    (hS₀ : S₀ ≤ ch6S T L V) {g₁ g₂ : Subgroup.normalizer (V : Set G)} (hg₁S₀ : (g₁ : G) ∈ S₀)
    (hg₂S₀ : (g₂ : G) ∈ S₀) (ha₁1 : conjAct V g₁ ≠ 1) (ha₂1 : conjAct V g₂ ≠ 1)
    (ha₁₂ : conjAct V g₁ ≠ conjAct V g₂) : ch6ZS T L V ≤ ⁅Y, S₀⁆ := by
  have : CharP h.data.K 2 := charP_two_of_two_dvd h.two_dvd_card_K
  have hconj1 : ∀ g : Subgroup.normalizer (V : Set G),
      (g : G) ∈ Subgroup.centralizer (V : Set G) → conjAct V g = 1 := by
    intro g hg
    ext x
    rw [conjAct_apply_coe]
    have := Subgroup.mem_centralizer_iff.mp hg x x.2
    calc (g : G) * x * (g : G)⁻¹ = x * g * (g : G)⁻¹ := by rw [this]
      _ = x := by group
  have hg₁V : (g₁ : G) ∉ Subgroup.centralizer (V : Set G) := fun hc => ha₁1 (hconj1 g₁ hc)
  have hg₂V : (g₂ : G) ∉ Subgroup.centralizer (V : Set G) := fun hc => ha₂1 (hconj1 g₂ hc)
  have hg₁S := hS₀ hg₁S₀
  have hg₂S := hS₀ hg₂S₀
  obtain ⟨v, hv, hle⟩ := h.exists_line
  obtain ⟨B, hB⟩ := exists_sl2_mulVec_single v hv
  set f : (Fin 2 → h.data.K) →+ h.data.K :=
    { toFun := fun w => ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
        Matrix (Fin 2) (Fin 2) h.data.K).mulVec w 1
      map_zero' := by simp
      map_add' := fun x y => by simp [Matrix.mulVec_add] } with hf
  have hfv : ∀ w, f w = ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
      Matrix (Fin 2) (Fin 2) h.data.K).mulVec w 1 := fun w => rfl
  obtain ⟨b₁, hb₁⟩ := h.exists_transvection hv hle hB hg₁S
  obtain ⟨b₂, hb₂⟩ := h.exists_transvection hv hle hB hg₂S
  have hb₁' : ∀ w, h.data.conj g₁ w = w + (b₁ * f w) • v := hb₁
  have hb₂' : ∀ w, h.data.conj g₂ w = w + (b₂ * f w) • v := hb₂
  have hb₁0 : b₁ ≠ 0 := by
    rintro rfl
    exact hg₁V (h.data.mem_centralizer_of_conj_eq _ fun w => by rw [hb₁']; simp)
  have hb₂0 : b₂ ≠ 0 := by
    rintro rfl
    exact hg₂V (h.data.mem_centralizer_of_conj_eq _ fun w => by rw [hb₂']; simp)
  have hb₁₂ : b₁ ≠ b₂ := by
    rintro rfl
    apply ha₁₂
    refine MulEquiv.ext fun x => ?_
    apply h.data.E.injective
    apply Multiplicative.toAdd.injective
    rw [h.data.toAdd_E_conj, h.data.toAdd_E_conj, hb₁', hb₂']
  let H : AddSubgroup h.data.K :=
    { carrier := {x | ∃ y : ↥V, (y : G) ∈ Y ∧ f (Multiplicative.toAdd (h.data.E y)) = x}
      zero_mem' := ⟨1, Y.one_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
        exact ⟨y₁ * y₂, Y.mul_mem hy₁ hy₂, by rw [map_mul, toAdd_mul, map_add]⟩
      neg_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨y⁻¹, Y.inv_mem hy, by rw [map_inv, toAdd_inv, map_neg]⟩ }
  have hker : ∀ y : ↥V, f (Multiplicative.toAdd (h.data.E y)) = 0 → (y : G) ∈ Y := by
    intro y hy0
    refine hZY ((h.mem_ZS_iff_line hv hle y).mpr ?_)
    set w := Multiplicative.toAdd (h.data.E y) with hw
    set u := ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
      Matrix (Fin 2) (Fin 2) h.data.K).mulVec w with hu
    have hu1 : u 1 = 0 := (hfv w).symm.trans hy0
    refine ⟨u 0, ?_⟩
    have hu' : u = u 0 • ![1, 0] := by
      funext i
      fin_cases i
      · simp
      · simp [hu1]
    calc w = (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec u := (mulVec_inv_mulVec B w).symm
      _ = (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec (u 0 • ![1, 0]) := by rw [← hu']
      _ = u 0 • v := by rw [Matrix.mulVec_smul, hB]
  have hrel : (Y.subgroupOf V).index = 2 := hY2
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hrel
  have haY : (a : G) ∉ Y := by
    have := ha 1
    simp only [one_mul] at this
    rcases this with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact absurd (Subgroup.one_mem _) h2
    · exact h2
  set α := f (Multiplicative.toAdd (h.data.E a)) with hα
  have hαH : α ∉ H := by
    rintro ⟨y, hy, hyα⟩
    apply haY
    have h0 : f (Multiplicative.toAdd (h.data.E (a * y⁻¹))) = 0 := by
      rw [map_mul, toAdd_mul, map_add, map_inv, toAdd_inv, map_neg, hyα, ← hα, add_neg_cancel]
    have h1 := hker _ h0
    have e : (a : G) = ((a * y⁻¹ : ↥V) : G) * y := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]
    exact Y.mul_mem h1 hy
  have hcos : ∀ x, x ∈ H ∨ x + α ∈ H := by
    intro x
    set y₀ : ↥V := h.data.E.symm (Multiplicative.ofAdd
      ((B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec ![0, x])) with hy₀
    have hfy₀ : f (Multiplicative.toAdd (h.data.E y₀)) = x := by
      rw [hy₀, MulEquiv.apply_symm_apply, toAdd_ofAdd, hfv, inv_mulVec_mulVec]
      simp
    rcases ha y₀ with ⟨h1, -⟩ | ⟨h1, -⟩
    · right
      refine ⟨y₀ * a, h1, ?_⟩
      rw [map_mul, toAdd_mul, map_add, hfy₀]
    · left
      exact ⟨y₀, h1, hfy₀⟩
  have hc0 : b₂ / b₁ ≠ 0 := div_ne_zero hb₂0 hb₁0
  have hc1 : b₂ / b₁ ≠ 1 := fun h1 => hb₁₂ ((div_eq_one_iff_eq hb₁0).mp h1).symm
  obtain ⟨h₂, hh₂, hch₂⟩ := exists_mul_not_mem hαH hcos hc0 hc1
  have hsum : ∀ μ : h.data.K, ∃ x₁ ∈ H, ∃ x₂ ∈ H, b₁ * x₁ + b₂ * x₂ = μ := by
    intro μ
    by_cases hμ : μ / b₁ ∈ H
    · exact ⟨μ / b₁, hμ, 0, H.zero_mem, by field_simp; ring⟩
    · refine ⟨μ / b₁ - b₂ / b₁ * h₂, sub_mem_of_not_mem hcos hμ hch₂, h₂, hh₂, ?_⟩
      field_simp
      ring
  intro z hz
  obtain ⟨μ, hμ⟩ := (h.mem_ZS_iff_line hv hle ⟨z, hz.1⟩).mp hz
  obtain ⟨x₁, ⟨y₁, hy₁, rfl⟩, x₂, ⟨y₂, hy₂, rfl⟩, hxμ⟩ := hsum μ
  have hc₁ : ⁅(y₁ : G), (g₁ : G)⁆ ∈ V :=
    h.ZS_le (h.commutator_V_S_le (Subgroup.commutator_mem_commutator y₁.2 hg₁S))
  have hc₂ : ⁅(y₂ : G), (g₂ : G)⁆ ∈ V :=
    h.ZS_le (h.commutator_V_S_le (Subgroup.commutator_mem_commutator y₂.2 hg₂S))
  have hE₁ := h.toAdd_E_commutator (f := f) hg₁S hb₁' y₁.2 hc₁
  have hE₂ := h.toAdd_E_commutator (f := f) hg₂S hb₂' y₂.2 hc₂
  have hmem : ⁅(y₁ : G), (g₁ : G)⁆ * ⁅(y₂ : G), (g₂ : G)⁆ ∈ ⁅Y, S₀⁆ :=
    Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hy₁ hg₁S₀)
      (Subgroup.commutator_mem_commutator hy₂ hg₂S₀)
  have heq : (⟨⁅(y₁ : G), (g₁ : G)⁆ * ⁅(y₂ : G), (g₂ : G)⁆, V.mul_mem hc₁ hc₂⟩ : ↥V) =
      ⟨z, hz.1⟩ := by
    apply h.data.E.injective
    apply Multiplicative.toAdd.injective
    rw [show (⟨⁅(y₁ : G), (g₁ : G)⁆ * ⁅(y₂ : G), (g₂ : G)⁆, V.mul_mem hc₁ hc₂⟩ : ↥V) =
      ⟨⁅(y₁ : G), (g₁ : G)⁆, hc₁⟩ * ⟨⁅(y₂ : G), (g₂ : G)⁆, hc₂⟩ from rfl, map_mul, toAdd_mul,
      hE₁, hE₂, hμ, ← add_smul, hxμ]
  have hz' : ⁅(y₁ : G), (g₁ : G)⁆ * ⁅(y₂ : G), (g₂ : G)⁆ = z := congrArg Subtype.val heq
  rw [← hz']
  exact hmem

theorem ZS_eq_commutator (h : Hyp611Nat G T M L V n) {Y : Subgroup G}
    (hZY : ch6ZS T L V ≤ Y) (hYV : Y ≤ V) (hY2 : Y.relIndex V = 2) {S₀ : Subgroup G}
    (hS₀ : S₀ ≤ ch6S T L V) (hnc : ¬ IsCyclic ↥(autOn S₀ V)) : ch6ZS T L V = ⁅Y, S₀⁆ := by
  refine le_antisymm ?_ ((Subgroup.commutator_mono hYV hS₀).trans h.commutator_V_S_le)
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁1, ha₂1, ha₁₂⟩ : ∃ a₁ ∈ autOn S₀ V, ∃ a₂ ∈ autOn S₀ V,
      a₁ ≠ 1 ∧ a₂ ≠ 1 ∧ a₁ ≠ a₂ := by
    by_contra hcon
    push Not at hcon
    apply hnc
    by_cases hex : ∃ a ∈ autOn S₀ V, a ≠ 1
    · obtain ⟨a, ha, ha1⟩ := hex
      refine ⟨⟨⟨a, ha⟩, fun x => ?_⟩⟩
      by_cases hx : (x : MulAut ↥V) = 1
      · refine ⟨0, ?_⟩
        show (⟨a, ha⟩ : ↥(autOn S₀ V)) ^ (0 : ℤ) = x
        rw [zpow_zero]
        exact Subtype.ext hx.symm
      · refine ⟨1, ?_⟩
        show (⟨a, ha⟩ : ↥(autOn S₀ V)) ^ (1 : ℤ) = x
        rw [zpow_one]
        exact Subtype.ext (hcon a ha x x.2 ha1 hx)
    · push Not at hex
      refine ⟨⟨1, fun x => ⟨0, ?_⟩⟩⟩
      show (1 : ↥(autOn S₀ V)) ^ (0 : ℤ) = x
      rw [zpow_zero]
      exact Subtype.ext (hex x x.2).symm
  obtain ⟨g₁, hg₁S₀, rfl⟩ := mem_autOn_iff.mp ha₁
  obtain ⟨g₂, hg₂S₀, rfl⟩ := mem_autOn_iff.mp ha₂
  exact h.ZS_le_commutator_of_ne hZY hY2 hS₀ hg₁S₀ hg₂S₀ ha₁1 ha₂1 ha₁₂

end Hyp611Nat

end CFSG.Quasithin.H13
