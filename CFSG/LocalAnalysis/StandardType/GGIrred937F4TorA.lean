module

public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Base
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4TorAStab
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3

private theorem exists_conj_mem_torusGroup_of_mem_monomial_familyCentralizer_pow
    {τ : Tag} {p : ℕ} [Fact p.Prime]
    (hmon : MonomialToralAt τ p) {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ p)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hstab : ∀ w : WeylGroup τ, w ^ p = 1 → (∀ i, w ∈ rootCharStabilizer (a i)) →
      w ∈ kernelWeylGroup (familyChar a))
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hna : ∀ i, rootDiagUnit τ (a i) * n = n * rootDiagUnit τ (a i)) (hp : n ^ p = 1) :
    ∃ g ∈ adjointGroup τ L, (∀ i, rootDiagUnit τ (a i) * g = g * rootDiagUnit τ (a i)) ∧
      g * n * g⁻¹ ∈ torusGroup τ L := by
  obtain ⟨w, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hn
  subst e
  have hπ : weylQuotientHom τ L ⟨_, hn⟩ = w := weylQuotientHom_torus_mul hk w hn
  have hw : ∀ i, w ∈ rootCharStabilizer (a i) := by
    intro i
    rw [← conj_canonicalRep_eq_iff]
    have hdk : rootDiagUnit τ (a i) * k = k * rootDiagUnit τ (a i) :=
      rootDiagUnit_mul_comm_of_mem_torusGroup (a i) hk
    have h1 : rootDiagUnit τ (a i) * canonicalRep (coxeterSystem τ) L w =
        canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ (a i) := by
      have e1 : rootDiagUnit τ (a i) * canonicalRep (coxeterSystem τ) L w =
          k⁻¹ * (rootDiagUnit τ (a i) * (k * canonicalRep (coxeterSystem τ) L w)) := by
        rw [← mul_assoc (rootDiagUnit τ (a i)) k, hdk]
        group
      rw [e1, hna i]
      group
    rw [h1, mul_inv_cancel_right]
  have hwS : weylQuotientHom τ L ⟨_, hn⟩ ∈ kernelWeylGroup (familyChar a) := by
    rw [hπ]
    exact hstab w (by rw [← hπ]; exact weylQuotientHom_pow_eq_one hn hp) hw
  obtain ⟨g, hg, hgn⟩ := hmon L hL (ι → Lˣ) (familyChar a) _ hn hwS
    (weylQuotientHom_pow_eq_one hn hp)
  refine ⟨g, rootSpan_le_adjointGroup L _ hg, fun i => ?_, hgn⟩
  have hgc : g ∈ Subgroup.centralizer {rootDiagUnit τ (a i)} := by
    refine rootSpan_le_centralizer (a i) (S := kernelRoots (familyChar a)) (fun α hα => ?_) hg
    rw [kernelRoots_familyChar] at hα
    exact ⟨hα.1, hα.2 i⟩
  exact (Subgroup.mem_centralizer_singleton_iff.1 hgc).symm

theorem f4ThreeEighteenToral_holds :
    F4ThreeEighteenToral := by
  intro K _ _ hK3 A hA hAfin hcomm hexp g hg a ha h18 hga
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ℓ, hℓK⟩ := CharP.exists K
  have hℓp : ℓ.Prime := CharP.char_is_prime K ℓ
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 3
    apply hK3
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 3 n.ne_zero
  have hL3 : ringChar (AlgebraicClosure K) ≠ 3 := by
    rw [ringChar.eq (AlgebraicClosure K) ℓ]
    exact hℓ3
  have hmon : MonomialToralAt Tag.F4 3 := monomialToralAt_three_of_block a2BlockToral_F4
  let A' : Subgroup (ModGL Tag.F4 (AlgebraicClosure K)) :=
    A.map (MulAut.conj g⁻¹).toMonoidHom
  have hmemA' : ∀ x : ModGL Tag.F4 (AlgebraicClosure K),
      x ∈ A' ↔ g * x * g⁻¹ ∈ A := by
    intro x
    change x ∈ A.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ A
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g * (MulAut.conj g⁻¹) y * g⁻¹ ∈ A
      have e : g * (MulAut.conj g⁻¹) y * g⁻¹ = y := by
        rw [MulAut.conj_apply]
        group
      rwa [e]
    · intro hx
      refine ⟨g * x * g⁻¹, hx, ?_⟩
      change (MulAut.conj g⁻¹) (g * x * g⁻¹) = x
      rw [MulAut.conj_apply]
      group
  have hA'le : A' ≤ adjointGroup Tag.F4 (AlgebraicClosure K) := by
    intro x hx
    have hx' := ((hmemA' x).1 hx)
    have hG : g⁻¹ * (g * x * g⁻¹) * g ∈ adjointGroup Tag.F4 (AlgebraicClosure K) :=
      mul_mem (mul_mem (inv_mem hg) (hA hx')) hg
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at hG
  have hA'exp : ∀ x ∈ A', x ^ 3 = 1 := by
    intro x hx
    have hx' := ((hmemA' x).1 hx)
    have h := conj_pow_eq_one' g⁻¹ (hexp (g * x * g⁻¹) hx')
    rwa [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x by group] at h
  have hA'comm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    have hx' := ((hmemA' x).1 hx)
    have hy' := ((hmemA' y).1 hy)
    have h := hcomm (g * x * g⁻¹) hx' (g * y * g⁻¹) hy'
    apply (MulAut.conj g).injective
    rw [map_mul, map_mul]
    have hx'' : (MulAut.conj g) x = g * x * g⁻¹ := by
      rw [MulAut.conj_apply]
    have hy'' : (MulAut.conj g) y = g * y * g⁻¹ := by
      rw [MulAut.conj_apply]
    rw [hx'', hy'']
    exact h
  have hdaA' : rootDiagUnit Tag.F4 a ∈ A' := by
    rw [hmemA']
    exact hga
  have hA'fin : Finite A' := by
    change Finite ↥(A.map (MulAut.conj g⁻¹).toMonoidHom)
    exact Finite.Set.finite_image _ _
  haveI : Fintype A' := Fintype.ofFinite A'
  have claim : ∀ S : Finset A',
      ∃ C ∈ adjointGroup Tag.F4 (AlgebraicClosure K),
        C * rootDiagUnit Tag.F4 a * C⁻¹ = rootDiagUnit Tag.F4 a ∧
        ∀ y ∈ S, C * (y : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹ ∈
          torusGroup Tag.F4 (AlgebraicClosure K) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        refine ⟨1, one_mem _, by group, ?_⟩
        intro y hy
        simp at hy
    | insert x S hx ih =>
        obtain ⟨C, hC, hCd, hCS⟩ := ih
        have hexpDiag : ∀ (c y : ModGL Tag.F4 (AlgebraicClosure K)), y ∈ A' →
            ∀ b : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ,
              c * y * c⁻¹ = rootDiagUnit Tag.F4 b → ∀ i, b i ^ 3 = 1 := by
          intro c y hy b hb i
          have h : rootDiagUnit Tag.F4 (b ^ 3) = rootDiagUnit Tag.F4 1 := by
            rw [rootDiagUnit_pow', rootDiagUnit_one, ← hb,
              conj_pow_eq_one' c (hA'exp y hy)]
          have := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) i
          simpa using this
        have hchoose : ∀ y : {y : A' // y ∈ S},
            ∃ b : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ,
              C * (y.1 : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹ =
                rootDiagUnit Tag.F4 b :=
          fun y => exists_rootDiagUnit_eq_of_mem_torusGroup (hCS y.1 y.2)
        let aS : {y : A' // y ∈ S} → Fin Tag.F4.rank → (AlgebraicClosure K)ˣ :=
          fun y => Classical.choose (hchoose y)
        have haS : ∀ y : {y : A' // y ∈ S},
            C * (y.1 : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹ =
              rootDiagUnit Tag.F4 (aS y) :=
          fun y => Classical.choose_spec (hchoose y)
        let aFam : Option {y : A' // y ∈ S} →
            Fin Tag.F4.rank → (AlgebraicClosure K)ˣ := fun o => o.elim a aS
        have haFam : ∀ (s : Option {y : A' // y ∈ S}) (i : Fin Tag.F4.rank),
            aFam s i ^ 3 = 1 := by
          intro s i
          cases s with
          | none => simpa [aFam] using ha i
          | some y =>
              simpa [aFam] using
                hexpDiag C (y.1 : ModGL Tag.F4 (AlgebraicClosure K)) y.1.2
                  (aS y) (haS y) i
        have hFam18 : (rootCharKernel (τ := Tag.F4)
            (aFam (none : Option {y : A' // y ∈ S}))).ncard = 18 := by
          simpa [aFam] using h18
        have hstab : ∀ w : WeylGroup Tag.F4, w ^ 3 = 1 →
            (∀ s, w ∈ rootCharStabilizer (aFam s)) →
            w ∈ kernelWeylGroup (familyChar aFam) :=
          fun w hw3 hw => f4_hstab3_of_eighteen (AlgebraicClosure K) aFam none haFam hFam18
            w hw3 hw
        set B : Subgroup (ModGL Tag.F4 (AlgebraicClosure K)) :=
          A'.map (MulAut.conj C).toMonoidHom with hB
        have hBle : B ≤ adjointGroup Tag.F4 (AlgebraicClosure K) := by
          rintro _ ⟨y, hy, rfl⟩
          exact mul_mem (mul_mem hC (hA'le hy)) (inv_mem hC)
        have hA'finSet : (A' : Set (ModGL Tag.F4 (AlgebraicClosure K))).Finite :=
          Set.toFinite _
        have hBfin : (B : Set (ModGL Tag.F4 (AlgebraicClosure K))).Finite := by
          rw [hB]
          exact Set.Finite.image _ hA'finSet
        have hcommConj : ∀ (D x₁ : ModGL Tag.F4 (AlgebraicClosure K)), x₁ ∈ A' →
            ∀ x ∈ A', (D * x₁ * D⁻¹) * (D * x * D⁻¹) = (D * x * D⁻¹) * (D * x₁ * D⁻¹) := by
          intro D x₁ hx₁ x hx
          calc
            (D * x₁ * D⁻¹) * (D * x * D⁻¹) = D * (x₁ * x) * D⁻¹ := by group
            _ = D * (x * x₁) * D⁻¹ := by rw [hA'comm x₁ hx₁ x hx]
            _ = (D * x * D⁻¹) * (D * x₁ * D⁻¹) := by group
        have hBa : ∀ y ∈ B,
            rootDiagUnit Tag.F4 a * y = y * rootDiagUnit Tag.F4 a := by
          rintro y ⟨z, hz, rfl⟩
          change rootDiagUnit Tag.F4 a * (C * (z : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) =
            (C * (z : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) * rootDiagUnit Tag.F4 a
          rw [← hCd]
          exact hcommConj C (rootDiagUnit Tag.F4 a) hdaA'
            (z : ModGL Tag.F4 (AlgebraicClosure K)) hz
        have hBy : ∀ (y : {y : A' // y ∈ S}), ∀ z ∈ B,
            rootDiagUnit Tag.F4 (aS y) * z = z * rootDiagUnit Tag.F4 (aS y) := by
          intro y z hz
          rcases hz with ⟨w, hw, rfl⟩
          change rootDiagUnit Tag.F4 (aS y) *
              (C * (w : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) =
            (C * (w : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) *
              rootDiagUnit Tag.F4 (aS y)
          rw [← haS y]
          exact hcommConj C (y.1 : ModGL Tag.F4 (AlgebraicClosure K)) y.1.2
            (w : ModGL Tag.F4 (AlgebraicClosure K)) hw
        have hBaFam : ∀ z ∈ B, ∀ s,
            rootDiagUnit Tag.F4 (aFam s) * z = z * rootDiagUnit Tag.F4 (aFam s) := by
          intro z hz s
          cases s with
          | none => simpa [aFam] using hBa z hz
          | some y => simpa [aFam] using hBy y z hz
        have hBexp : ∀ y ∈ B, y ^ 3 = 1 := by
          rintro y ⟨z, hz, rfl⟩
          change (C * (z : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) ^ 3 = 1
          exact conj_pow_eq_one' C (hA'exp (z : ModGL Tag.F4 (AlgebraicClosure K)) hz)
        obtain ⟨z, hz, hzd, hzN⟩ :=
          exists_conj_le_monomial_familyCentralizer_bar (τ := Tag.F4) (p := 3) hℓ3
            (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) aFam hBle hBfin hBaFam hBexp
        set n : ModGL Tag.F4 (AlgebraicClosure K) :=
          z * (C * (x : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) * z⁻¹ with hn
        have hxB : C * (x : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹ ∈ B :=
          ⟨x, x.2, rfl⟩
        have hnN : n ∈ monomialSubgroup Tag.F4 (AlgebraicClosure K) := by
          rw [hn]
          exact hzN _ hxB
        have hzd' : ∀ s,
            rootDiagUnit Tag.F4 (aFam s) * z⁻¹ = z⁻¹ * rootDiagUnit Tag.F4 (aFam s) := by
          intro s
          calc
            rootDiagUnit Tag.F4 (aFam s) * z⁻¹ =
                z⁻¹ * (z * rootDiagUnit Tag.F4 (aFam s)) * z⁻¹ := by group
            _ = z⁻¹ * (rootDiagUnit Tag.F4 (aFam s) * z) * z⁻¹ := by rw [hzd s]
            _ = z⁻¹ * rootDiagUnit Tag.F4 (aFam s) := by group
        have hn_a : ∀ s,
            rootDiagUnit Tag.F4 (aFam s) * n = n * rootDiagUnit Tag.F4 (aFam s) := by
          intro s
          have h1 : rootDiagUnit Tag.F4 (aFam s) *
              (C * (x : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) =
              (C * (x : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) *
                rootDiagUnit Tag.F4 (aFam s) := hBaFam _ hxB s
          calc
            rootDiagUnit Tag.F4 (aFam s) * n =
                (rootDiagUnit Tag.F4 (aFam s) * z) *
                  (C * (x : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) * z⁻¹ := by
              rw [hn]; group
            _ = z * (rootDiagUnit Tag.F4 (aFam s) *
                  (C * (x : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹)) * z⁻¹ := by
              rw [hzd s]; group
            _ = z * (C * (x : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) *
                  (rootDiagUnit Tag.F4 (aFam s) * z⁻¹) := by
              rw [h1]; group
            _ = n * rootDiagUnit Tag.F4 (aFam s) := by
              rw [hzd' s, hn]; group
        have hnp : n ^ 3 = 1 := conj_pow_eq_one' z (hBexp _ hxB)
        obtain ⟨g', hg', hg'd, hg'n⟩ :=
          exists_conj_mem_torusGroup_of_mem_monomial_familyCentralizer_pow
            (τ := Tag.F4) (p := 3) hmon hL3 hstab hnN hn_a hnp
        set C' : ModGL Tag.F4 (AlgebraicClosure K) := g' * z * C with hC'
        have hC'G : C' ∈ adjointGroup Tag.F4 (AlgebraicClosure K) := by
          rw [hC']
          exact mul_mem (mul_mem hg' hz) hC
        have hzda' : rootDiagUnit Tag.F4 a * z = z * rootDiagUnit Tag.F4 a := by
          simpa [aFam] using hzd none
        have hzda : z * rootDiagUnit Tag.F4 a * z⁻¹ = rootDiagUnit Tag.F4 a := by
          rw [← hzda', mul_inv_cancel_right]
        have hg'da' : rootDiagUnit Tag.F4 a * g' = g' * rootDiagUnit Tag.F4 a := by
          simpa [aFam] using hg'd none
        have hg'da : g' * rootDiagUnit Tag.F4 a * g'⁻¹ = rootDiagUnit Tag.F4 a := by
          rw [← hg'da', mul_inv_cancel_right]
        have hC'd : C' * rootDiagUnit Tag.F4 a * C'⁻¹ = rootDiagUnit Tag.F4 a := by
          rw [hC']
          calc
            (g' * z * C) * rootDiagUnit Tag.F4 a * (g' * z * C)⁻¹ =
                g' * (z * (C * rootDiagUnit Tag.F4 a * C⁻¹) * z⁻¹) * g'⁻¹ := by group
            _ = g' * (z * rootDiagUnit Tag.F4 a * z⁻¹) * g'⁻¹ := by rw [hCd]
            _ = g' * rootDiagUnit Tag.F4 a * g'⁻¹ := by rw [hzda]
            _ = rootDiagUnit Tag.F4 a := hg'da
        have hC'S : ∀ y ∈ S,
            C' * (y : ModGL Tag.F4 (AlgebraicClosure K)) * C'⁻¹ ∈
              torusGroup Tag.F4 (AlgebraicClosure K) := by
          intro y hy
          have hzdS : rootDiagUnit Tag.F4 (aS ⟨y, hy⟩) * z =
              z * rootDiagUnit Tag.F4 (aS ⟨y, hy⟩) := by
            simpa [aFam] using hzd (some ⟨y, hy⟩)
          have hg'dS : rootDiagUnit Tag.F4 (aS ⟨y, hy⟩) * g' =
              g' * rootDiagUnit Tag.F4 (aS ⟨y, hy⟩) := by
            simpa [aFam] using hg'd (some ⟨y, hy⟩)
          have hzy : z * (C * (y : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) * z⁻¹ =
              C * (y : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹ := by
            rw [haS ⟨y, hy⟩]
            rw [← hzdS, mul_inv_cancel_right]
          have hg'y : g' * (C * (y : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) * g'⁻¹ =
              C * (y : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹ := by
            rw [haS ⟨y, hy⟩]
            rw [← hg'dS, mul_inv_cancel_right]
          have e : C' * (y : ModGL Tag.F4 (AlgebraicClosure K)) * C'⁻¹ =
              rootDiagUnit Tag.F4 (aS ⟨y, hy⟩) := by
            calc
              C' * (y : ModGL Tag.F4 (AlgebraicClosure K)) * C'⁻¹ =
                  g' * (z * (C * (y : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) * z⁻¹) *
                    g'⁻¹ := by rw [hC']; group
              _ = g' * (C * (y : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹) * g'⁻¹ := by
                rw [hzy]
              _ = C * (y : ModGL Tag.F4 (AlgebraicClosure K)) * C⁻¹ := hg'y
              _ = rootDiagUnit Tag.F4 (aS ⟨y, hy⟩) := haS ⟨y, hy⟩
          rw [e]
          exact rootDiagUnit_mem_torusGroup _
        have hC'x : C' * (x : ModGL Tag.F4 (AlgebraicClosure K)) * C'⁻¹ ∈
            torusGroup Tag.F4 (AlgebraicClosure K) := by
          have e : C' * (x : ModGL Tag.F4 (AlgebraicClosure K)) * C'⁻¹ =
              g' * n * g'⁻¹ := by
            rw [hC', hn]
            group
          rw [e]
          exact hg'n
        refine ⟨C', hC'G, hC'd, ?_⟩
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hyS
        · exact hC'x
        · exact hC'S y hyS
  obtain ⟨C₁, hC₁, hC₁d, hC₁T⟩ := claim Finset.univ
  refine ⟨g * C₁⁻¹, mul_mem hg (inv_mem hC₁), ?_⟩
  intro x hx
  have hyA' : g⁻¹ * x * g ∈ A' := by
    rw [hmemA']
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e]
  have hyT : C₁ * (g⁻¹ * x * g) * C₁⁻¹ ∈
      torusGroup Tag.F4 (AlgebraicClosure K) :=
    hC₁T ⟨g⁻¹ * x * g, hyA'⟩ (Finset.mem_univ _)
  have e : (g * C₁⁻¹)⁻¹ * x * (g * C₁⁻¹) =
      C₁ * (g⁻¹ * x * g) * C₁⁻¹ := by group
  rwa [e]

end Irred937

end CFSG.StandardType

end
