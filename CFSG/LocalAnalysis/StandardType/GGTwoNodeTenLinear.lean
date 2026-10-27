module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeTenCore
import CFSG.LocalAnalysis.StandardType.GGTwoNodeTenLinearAux1

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTenLinear {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) : Prop :=
  ∃ (ΛL : Type) (_ : Fintype ΛL) (_ : DecidableEq ΛL) (ML : CoxeterMatrix ΛL) (CL : Matrix ΛL ΛL ℤ)
    (hL : ΛL → V) (aL : ΛL → Module.Dual (ZMod 3) V) (rL : ΛL → (V ≃ₗ[ZMod 3] V))
    (hK : Fin 8 → V) (aK : Fin 8 → Module.Dual (ZMod 3) V) (rK : Fin 8 → (V ≃ₗ[ZMod 3] V)) (x : V),
    Fintype.card ΛL = 9 ∧ GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧
      (∀ i j, aL i (hL j) = (CL i j : ZMod 3)) ∧ (∀ i v, rL i v = v - aL i v • hL i) ∧
      (∃ fL : ML.Group ≃* ↥(Subgroup.closure (Set.range rL)),
        ∀ i, (fL (ML.simple i) : V ≃ₗ[ZMod 3] V) = rL i) ∧
      (∀ i j, aK i (hK j) = (CartanMatrix.A 8 i j : ZMod 3)) ∧
      (∀ i v, rK i v = v - aK i v • hK i) ∧
      x ≠ 0 ∧ (∀ v, (∀ i, aL i v = 0) → v ∈ Submodule.span (ZMod 3) {x}) ∧
      (∃ t ∈ Subgroup.closure (Set.range rK), GGLinRefl t ∧ t x ≠ x) ∧
      (∃ a ∈ Subgroup.closure (Set.range rL) ⊓ Subgroup.closure (Set.range rK),
        ∃ b ∈ Subgroup.closure (Set.range rL) ⊓ Subgroup.closure (Set.range rK), a * b ≠ b * a) ∧
      A = Subgroup.closure (Set.range rL) ⊔ Subgroup.closure (Set.range rK) ∧
      (∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
      Nat.card ↥(A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) x) ≤
        (3 - 1) * 6 * Nat.card ↥(Subgroup.closure (Set.range rL))

theorem ggTen_core_hyps
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (hdim : Module.finrank (ZMod 3) V = 10) (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hA : GGTenLinear A) :
    ∃ (ι : Type) (_ : Fintype ι) (h : ι → V) (α : ι → Module.Dual (ZMod 3) V)
      (r : ι → (V ≃ₗ[ZMod 3] V)),
      (∀ i, α i (h i) = 2) ∧ (∀ i v, r i v = v - α i v • h i) ∧ A = Subgroup.closure (Set.range r) ∧
      (∀ i j, Relation.ReflTransGen (fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) i j) ∧
      (∀ v, (∀ i, α i v = 0) → v = 0) ∧
      (∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
      9 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) ∧
      Module.finrank (ZMod 3) V ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) + 1 ∧
      8 * Nat.card A < 3 ^ (Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) *
        (Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) - 1) / 2) := by
  classical
  unfold GGTenLinear at hA
  obtain ⟨ΛL, iΛL, dΛL, ML, CL, hL, aL, rL, hK, aK, rK, x, hcardL, hWeyl, hCartan, hpairL,
    hrL, ⟨fL, hfL⟩, hpairK, hrK, hx, hkerL, ht, hab, hAeq, hnt, hstab⟩ := hA
  letI := iΛL
  letI := dΛL
  let h : ΛL ⊕ Fin 8 → V := Sum.elim hL hK
  let α : ΛL ⊕ Fin 8 → Module.Dual (ZMod 3) V := Sum.elim aL aK
  let r : ΛL ⊕ Fin 8 → (V ≃ₗ[ZMod 3] V) := Sum.elim rL rK
  have hα : ∀ i : ΛL ⊕ Fin 8, α i (h i) = 2 := by
    intro i
    rcases i with i | j
    · change aL i (hL i) = 2
      rw [hpairL i i, hCartan.1 i]; norm_num
    · change aK j (hK j) = 2
      rw [hpairK j j]; simp [CartanMatrix.A]
  have hr : ∀ i : ΛL ⊕ Fin 8, ∀ v, r i v = v - α i v • h i := by
    intro i v
    rcases i with i | j
    · change rL i v = v - aL i v • hL i
      exact hrL i v
    · change rK j v = v - aK j v • hK j
      exact hrK j v
  have hAr : A = Subgroup.closure (Set.range r) := by
    change A = Subgroup.closure (Set.range (Sum.elim rL rK))
    rw [hAeq, Set.Sum.elim_range, Subgroup.closure_union]
  have hziff := tenLinAux_zero_iff h α r A hα hr hAr hnt
  have hLinInd : LinearIndependent (ZMod 3) hL :=
    ggMaxRank_nine_indep (p := 3) rfl hcardL hWeyl hCartan hL aL (fun i j => hpairL i j)
  have hdim_spanL : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range hL)) = 9 := by
    rw [finrank_span_eq_card hLinInd, hcardL]
  have hspan_le : Submodule.span (ZMod 3) (Set.range hL) ≤
      Submodule.span (ZMod 3) (Set.range h) := by
    apply Submodule.span_mono
    rw [Set.range_subset_iff]
    intro i
    exact ⟨Sum.inl i, by simp [h]⟩
  haveI : Module.Finite (ZMod 3) ↥(Submodule.span (ZMod 3) (Set.range h)) :=
    Module.Finite.of_finite
  have hd : 9 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) := by
    have hle := Submodule.finrank_mono hspan_le
    rw [hdim_spanL] at hle
    exact hle
  have hL0 : Nat.card ↥(Subgroup.closure (Set.range rL)) ≤ 185794560 := by
    have hcard_eq : Nat.card ↥(Subgroup.closure (Set.range rL)) = Nat.card ML.Group :=
      (Nat.card_congr fL.toEquiv).symm
    rw [hcard_eq]
    have hr8 : 8 ≤ Fintype.card ΛL := by rw [hcardL]; norm_num
    rcases ggRC_card_weyl_le ML hWeyl hr8 with hle | ⟨h8, -⟩
    · calc Nat.card ML.Group ≤ 2 ^ Fintype.card ΛL * (Fintype.card ΛL).factorial := hle
        _ = 185794560 := by rw [hcardL]; norm_num
    · omega
  have hstab_card := tenLinAux_stabilizer_card A x
  have horbit := tenLinAux_orbit_le hdim A x
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun a b h => LinearEquiv.ext (congrFun h))
  haveI : Fintype ↥A := Fintype.ofFinite ↥A
  haveI : Fintype ↑(MulAction.orbit ↥A x) := Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.stabilizer ↥A x) := Fintype.ofFinite _
  have hOS : Nat.card (MulAction.orbit ↥A x) * Nat.card (MulAction.stabilizer ↥A x) =
      Nat.card ↥A := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥A x
  have hA_le : Nat.card A ≤ 3 ^ 10 * (12 * 185794560) := by
    calc Nat.card A = Nat.card (MulAction.orbit ↥A x) * Nat.card (MulAction.stabilizer ↥A x) :=
          hOS.symm
      _ ≤ 3 ^ 10 * Nat.card (MulAction.stabilizer ↥A x) := Nat.mul_le_mul_right _ horbit
      _ = 3 ^ 10 * Nat.card ↥(A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) x) := by
          rw [hstab_card]
      _ ≤ 3 ^ 10 * (12 * Nat.card ↥(Subgroup.closure (Set.range rL))) :=
          Nat.mul_le_mul_left _ hstab
      _ ≤ 3 ^ 10 * (12 * 185794560) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hL0)
  have h36 : 36 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) *
      (Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) - 1) / 2 := by
    have h1 : 8 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) - 1 := by
      omega
    have h2 : 72 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) *
        (Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) - 1) :=
      Nat.mul_le_mul hd h1
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  have hlt : 8 * Nat.card A < 3 ^ 36 := by
    have h1 : 8 * Nat.card A ≤ 8 * (3 ^ 10 * (12 * 185794560)) := Nat.mul_le_mul_left _ hA_le
    have h2 : 8 * (3 ^ 10 * (12 * 185794560)) < 3 ^ 36 := by norm_num
    exact lt_of_le_of_lt h1 h2
  refine ⟨ΛL ⊕ Fin 8, inferInstance, h, α, r, hα, hr, hAr, ?_, ?_, hnt, hd, ?_, ?_⟩
  ·
    obtain ⟨C, hTree, hCbond⟩ := ggFLW_cartanTree_bonds (ι := ΛL) hWeyl
    have hLtree : ∀ a b : ΛL, Relation.ReflTransGen (fun x y : ΛL => C x y ≠ 0) a b :=
      tenLinAux_tree_conn C hTree
    have hLconn : ∀ a b : ΛL,
        Relation.ReflTransGen (fun x y : ΛL ⊕ Fin 8 => α x (h y) ≠ 0)
          (Sum.inl a) (Sum.inl b) := by
      intro a b
      refine tenLinAux_reflTransGen_lift (F := Sum.inl) (h := ?_) (hLtree a b)
      intro x y hxy
      change aL x (hL y) ≠ 0
      rw [hpairL x y]
      by_cases hxy' : x = y
      · subst hxy'; rw [hCartan.1 x]; decide
      · exact (tenLinAux_off_cast hcardL hWeyl hCartan hxy').mpr ((hCbond x y hxy').mp hxy)
    have hKtree : ∀ a b : Fin 8,
        Relation.ReflTransGen (fun x y : Fin 8 => CartanMatrix.A 8 x y ≠ 0) a b :=
      tenLinAux_tree_conn (CartanMatrix.A 8) (SecFiveRootRefl.cartanTree_A 8 (by norm_num))
    have hKconn : ∀ a b : Fin 8,
        Relation.ReflTransGen (fun x y : ΛL ⊕ Fin 8 => α x (h y) ≠ 0)
          (Sum.inr a) (Sum.inr b) := by
      intro a b
      refine tenLinAux_reflTransGen_lift (F := Sum.inr) (h := ?_) (hKtree a b)
      intro x y hxy
      change aK x (hK y) ≠ 0
      rw [hpairK x y]
      exact (tenLinAux_A8_cast x y).mpr hxy
    have hcross : ∃ i : ΛL, ∃ j : Fin 8,
        α (Sum.inl i) (h (Sum.inr j)) ≠ 0 ∧ α (Sum.inr j) (h (Sum.inl i)) ≠ 0 := by
      by_contra hcon
      have hcon' : ∀ i j, α (Sum.inl i) (h (Sum.inr j)) ≠ 0 →
          α (Sum.inr j) (h (Sum.inl i)) = 0 := by
        intro i j hne
        by_contra hne'
        exact hcon ⟨i, j, hne, hne'⟩
      have hcomm : ∀ i j, rL i * rK j = rK j * rL i := by
        intro i j
        have hz : aL i (hK j) = 0 := by
          by_contra hne
          exact hne ((hziff (Sum.inl i) (Sum.inr j)).mpr (hcon' i j hne))
        have hz' : aK j (hL i) = 0 := (hziff (Sum.inl i) (Sum.inr j)).mp hz
        exact tenLinAux_comm_of_zero h α r hr (a := Sum.inl i) (b := Sum.inr j) hz hz'
      have hall := tenLinAux_closure_comm hcomm
      obtain ⟨a, ha, b, hb, hne⟩ := hab
      exact hne (hall a ha.1 b hb.2)
    obtain ⟨i0, j0, hcij, hcji⟩ := hcross
    have hsingleij : Relation.ReflTransGen (fun a b => α a (h b) ≠ 0)
        (Sum.inl i0) (Sum.inr j0) := Relation.ReflTransGen.single hcij
    have hsingleji : Relation.ReflTransGen (fun a b => α a (h b) ≠ 0)
        (Sum.inr j0) (Sum.inl i0) := Relation.ReflTransGen.single hcji
    have hEconn : ∀ p q : ΛL ⊕ Fin 8,
        Relation.ReflTransGen (fun a b => α a (h b) ≠ 0) p q := by
      intro p q
      rcases p with a | i <;> rcases q with b | j
      · exact hLconn a b
      · exact (hLconn a i0).trans (hsingleij.trans (hKconn j0 j))
      · exact (hKconn i j0).trans (hsingleji.trans (hLconn i0 b))
      · exact hKconn i j
    intro p q
    exact tenLinAux_reflTransGen_imp (r := fun a b => α a (h b) ≠ 0)
      (s := fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0)
      (fun a b hab' => And.intro hab' (fun h0 => hab' ((hziff a b).mpr h0)))
      (hEconn p q)
  ·
    intro v hv
    have hvL : ∀ i : ΛL, aL i v = 0 := fun i => hv (Sum.inl i)
    have hvK : ∀ j : Fin 8, aK j v = 0 := fun j => hv (Sum.inr j)
    obtain ⟨c, hc⟩ : ∃ c : ZMod 3, v = c • x := by
      have hmem := hkerL v hvL
      rw [Submodule.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      exact ⟨c, hc.symm⟩
    obtain ⟨t, htmem, -, htx⟩ := ht
    have hfix_t : t v = v := by
      have hle : Subgroup.closure (Set.range rK) ≤
          MulAction.stabilizer (V ≃ₗ[ZMod 3] V) v := by
        rw [Subgroup.closure_le]
        rintro g ⟨j, rfl⟩
        refine (MulAction.mem_stabilizer_iff).mpr ?_
        rw [LinearEquiv.smul_def, hrK j, hvK j, zero_smul, sub_zero]
      have hmem : t ∈ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) v := hle htmem
      exact (MulAction.mem_stabilizer_iff).mp hmem
    have hcs : c • (t x - x) = 0 := by
      have h1 : c • t x = c • x := by
        calc c • t x = t (c • x) := by rw [map_smul]
          _ = t v := by rw [hc]
          _ = v := hfix_t
          _ = c • x := hc
      rw [smul_sub, h1, sub_self]
    by_cases hc0 : c = 0
    · rw [hc, hc0, zero_smul]
    · exfalso
      have hzero : t x - x = 0 := by
        rcases smul_eq_zero.mp hcs with h | h
        · exact absurd h hc0
        · exact h
      exact htx (sub_eq_zero.mp hzero)
  ·
    rw [hdim]
    omega
  ·
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num : 0 < 3) h36)


theorem ggTen_linear
    (hKG : GGReflClassLargeInput') {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Finite V] (hdim : Module.finrank (ZMod 3) V = 10)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hA : GGTenLinear A) : ZS.LinWeyl 3 A := by
  obtain ⟨ι, hι, h, α, r, hα, hr, hAr, hconn, hker, hnt, hd, hV, hcard⟩ :=
    ggTen_core_hyps hdim A hA
  letI := hι
  exact ggTen_core hKG h α hα r hr A hAr hconn hker hnt hd hV hcard

end CFSG.StandardType

end
