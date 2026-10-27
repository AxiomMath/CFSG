module

public import CFSG.Quasithin.Vol2.Ch9Sec3LSide
public import CFSG.Quasithin.Vol2.Ch9Sec3Borel

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem conjugate_L_eq (h37 : A37ForSQTK) (h38 : A38ForSQTK) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {z : G} (hz : z ∈ fsuM T L)
    (hzn : z ∉ Subgroup.normalizer (L : Set G)) : CFSG.conjugate L z = CFSG.conjugate L t := by
  rcases conjugate_eq_or_of_mem h37 h38 S.hyp.fsu (fun h => htn (h ht)) ht htn hz with h | h
  · exact absurd (Vol2.Ch10.SecA.conjugate_eq_self_iff.mp h) hzn
  · exact h

theorem mul_inv_mem_normalizer_L (h37 : A37ForSQTK) (h38 : A38ForSQTK) {x y : G}
    (hx : x ∈ fsuM T L) (hy : y ∈ fsuM T L) (hxn : x ∉ Subgroup.normalizer (L : Set G))
    (hyn : y ∉ Subgroup.normalizer (L : Set G)) : x * y⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨t, ht, htn⟩ := S.exists_not_mem_normalizer
  exact Vol2.Ch10.SecA.mul_inv_mem_normalizer_of_conjugate_eq
    ((S.conjugate_L_eq h37 h38 ht htn hx hxn).trans (S.conjugate_L_eq h37 h38 ht htn hy hyn).symm)

theorem le_normalizer_inf_normalizer_L (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    fsuM T L ≤ Subgroup.normalizer
      ((fsuM T L ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) : Set G) := by
  set N := Subgroup.normalizer (L : Set G) with hN
  have hfwd : ∀ m ∈ fsuM T L, ∀ x ∈ fsuM T L ⊓ N, m * x * m⁻¹ ∈ fsuM T L ⊓ N := by
    intro m hm x hx
    refine ⟨(fsuM T L).mul_mem ((fsuM T L).mul_mem hm hx.1) ((fsuM T L).inv_mem hm), ?_⟩
    by_cases hmN : m ∈ N
    · exact N.mul_mem (N.mul_mem hmN hx.2) (N.inv_mem hmN)
    · have hmx : m * x ∉ N := fun h => hmN (by simpa using N.mul_mem h (N.inv_mem hx.2))
      exact S.mul_inv_mem_normalizer_L h37 h38 ((fsuM T L).mul_mem hm hx.1) hm hmx hmN
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hfwd m hm x, fun h => ?_⟩
  have h1 := hfwd m⁻¹ ((fsuM T L).inv_mem hm) _ h
  have e : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem isSylowTwoOf_inf_normalizer_L (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (fsuM T L ⊓ Subgroup.normalizer (L : Set G)) := by
  have hTM : IsSylowTwoOf T (fsuM T L) :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow Setup.T_le_fsuM
  have h := A4.isSylowTwoOf_inf_normal hTM inf_le_left (S.le_normalizer_inf_normalizer_L h37 h38)
  have e : T ⊓ (fsuM T L ⊓ Subgroup.normalizer (L : Set G)) =
      T ⊓ Subgroup.normalizer (L : Set G) := by
    rw [← inf_assoc, inf_eq_left.mpr Setup.T_le_fsuM]
  rwa [e] at h

theorem lem934 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h3108 : Stmt3_2_10_eight) {X : Subgroup G} (hLX : L ≤ X)
    (hT₁X : T ⊓ Subgroup.normalizer (L : Set G) ≤ X) (hXO : pCoreOf 2 X ≠ ⊥)
    (hXM : ¬ X ≤ fsuM T L) : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G)) X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  set M := fsuM T L with hM
  set N := Subgroup.normalizer (L : Set G) with hN
  set T₁ := T ⊓ N with hT₁
  have hTM : T ≤ M := Setup.T_le_fsuM
  have hT₁2 : IsPGroup 2 T₁ := hfsu.sylow.1.to_le inf_le_left
  obtain ⟨t, ht, htn⟩ := S.exists_not_mem_normalizer
  obtain ⟨F, _, _, _, e, ψ, hc⟩ := S.exists_isCoord
  have hJT₁ : thompsonJ T ≤ T₁ := by
    refine le_inf (thompsonJ_le_self T) fun j hj => ?_
    exact hc.r0_le_normalizer_L h37 h38 h37c h38c
      (Subgroup.mem_sup_right ⟨thompsonJ_le_self T hj, S.hJ hj⟩)
  have hVp : IsVplus T L I (fsuV T I) := by
    by_cases hc' : L ≠ conjClosure L T ∧ Case326VM T L I
    · exact Or.inl ⟨hc'.1, hc'.2, S.hVM⟩
    · exact Or.inr ⟨hc', rfl⟩
  obtain ⟨T₀, hT₀, hT₁T₀⟩ := A4.exists_isSylowTwoOf_ge hT₁X hT₁2
  have hT₀M : T₀ ≤ M := Subgroup.le_normalizer.trans
    (h3108 G T L I (fsuV T I) hfsu hVp S.hJ T₀ hT₀.2.1 (hJT₁.trans hT₁T₀)).2
  have hsylL := S.isSylowTwoOf_inf_normalizer_L h37 h38
  have hT₀L : T₀ ⊓ N ≤ T₁ := KStar.le_of_isSylowTwoOf_of_le hsylL (hT₀.2.1.to_le inf_le_left)
    (le_inf hT₁T₀ inf_le_right) (inf_le_inf_right _ hT₀M)
  by_cases hT₀N : T₀ ≤ N
  · have hT₀T₁ : T₀ = T₁ := le_antisymm ((le_inf le_rfl hT₀N).trans hT₀L) hT₁T₀
    rw [← hT₀T₁]
    exact hT₀
  exfalso
  obtain ⟨y, hyT₀, hyn⟩ := Set.not_subset.mp hT₀N
  have hyX : y ∈ X := hT₀.1 hyT₀
  have hyM : y ∈ M := hT₀M hyT₀
  have hTsyl : IsSylowTwoOf T M :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTM
  obtain ⟨S', hS', hT₀S'⟩ := A4.exists_isSylowTwoOf_ge hT₀M hT₀.2.1
  obtain ⟨h, hhM, hhS'⟩ := A4.exists_conj_of_isSylowTwoOf hTsyl hS'
  have hS'L : S' ⊓ N ≤ T₁ := KStar.le_of_isSylowTwoOf_of_le hsylL (hS'.2.1.to_le inf_le_left)
    (le_inf (hT₁T₀.trans hT₀S') inf_le_right) (inf_le_inf_right _ hS'.1)
  have hS'X : S' ≤ X := by
    intro z hz
    by_cases hzn : z ∈ N
    · exact hT₁X (hS'L ⟨hz, hzn⟩)
    · have h1 : y⁻¹ * z ∈ N := by
        have h0 := S.mul_inv_mem_normalizer_L h37 h38 (M.inv_mem hyM) (M.inv_mem (hS'.1 hz))
          (fun h' => hyn (by simpa using N.inv_mem h'))
          (fun h' => hzn (by simpa using N.inv_mem h'))
        simpa using h0
      have h2 : y⁻¹ * z ∈ S' := S'.mul_mem (S'.inv_mem (hT₀S' hyT₀)) hz
      have h3 := hT₁X (hS'L ⟨h2, h1⟩)
      have e' : z = y * (y⁻¹ * z) := by group
      rw [e']
      exact X.mul_mem hyX h3
  have hconjX : ∀ g ∈ L ⊔ T, h * g * h⁻¹ ∈ X := by
    have hle : L ⊔ T ≤ X.comap (MulAut.conj h).toMonoidHom := by
      refine sup_le (fun l hl => ?_) (fun s hs => ?_)
      · show h * l * h⁻¹ ∈ X
        have hmem : h * l * h⁻¹ ∈ CFSG.conjugate L h⁻¹ := by
          rw [Vol2.Ch10.SecA.mem_conjugate_iff]
          have e' : h⁻¹ * (h * l * h⁻¹) * h⁻¹⁻¹ = l := by group
          rw [e']
          exact hl
        by_cases hhN : h⁻¹ ∈ N
        · rw [Vol2.Ch10.SecA.conjugate_eq_self_iff.mpr hhN] at hmem
          exact hLX hmem
        · rw [S.conjugate_L_eq h37 h38 ht htn (M.inv_mem hhM) hhN,
            ← S.conjugate_L_eq h37 h38 ht htn hyM hyn, Vol2.Ch10.SecA.mem_conjugate_iff] at hmem
          have h1 := X.mul_mem (X.mul_mem (X.inv_mem hyX) (hLX hmem)) hyX
          have e' : y⁻¹ * (y * (h * l * h⁻¹) * y⁻¹) * y = h * l * h⁻¹ := by group
          rwa [e'] at h1
      · show h * s * h⁻¹ ∈ X
        refine hS'X ((hhS' _).mpr ?_)
        have e' : h⁻¹ * (h * s * h⁻¹) * h = s := by group
        rw [e']
        exact hs
    exact fun g hg => hle hg
  set C := pCoreOf 2 X with hC
  set C' := CFSG.conjugate C h with hC'
  have hXN : X ≤ Subgroup.normalizer (C : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hNC' : ∀ g : G, h * g * h⁻¹ ∈ X → g ∈ Subgroup.normalizer (C' : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro a
    rw [Vol2.Ch10.SecA.mem_conjugate_iff, Vol2.Ch10.SecA.mem_conjugate_iff]
    have e' : h * (g * a * g⁻¹) * h⁻¹ = (h * g * h⁻¹) * (h * a * h⁻¹) * (h * g * h⁻¹)⁻¹ := by
      group
    rw [e']
    exact Subgroup.mem_normalizer_iff.mp (hXN hg) _
  have hC'2 : IsPGroup 2 C' := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).map _
  have hC'1 : C' ≠ ⊥ := by
    intro h0
    apply hXO
    have h1 := congrArg (fun Y => CFSG.conjugate Y h⁻¹) h0
    simp only [hC', Vol2.Ch10.SecA.conjugate_conjugate, mul_inv_cancel,
      Vol2.Ch10.SecA.conjugate_one] at h1
    rw [h1, Vol2.Ch10.SecA.conjugate_eq_map, Subgroup.map_bot]
  have hle := S.normalizer_le_of_le hC'2 hC'1 fun g hg => hNC' g (hconjX g hg)
  apply hXM
  intro x hx
  have h1 : h⁻¹ * x * h ∈ M := hle (hNC' _ (by
    have e' : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rw [e']
    exact hx))
  have e' : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  rw [e']
  exact M.mul_mem (M.mul_mem hhM h1) (M.inv_mem hhM)

end Setup

end CFSG.Quasithin.H13.Ch9
