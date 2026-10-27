module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs
public import CFSG.LocalAnalysis.StandardType.GGA11TorusModel
public import CFSG.LocalAnalysis.StandardType.GGA11GraphAut
public import CFSG.LocalAnalysis.StandardType.GGA8NbrTorusNorm
public import CFSG.LocalAnalysis.StandardType.GGSL9TwoProj
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartOne.TAIL.KSideOutLin
public import CFSG.RankThree.PartOne.TAIL.KSideCen

public section

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.A8Coord Matrix

namespace CFSG.StandardType.A11

private theorem a11lb_card_f2 : Nat.card F2 = 2 := by
  rw [GaloisField.card 2 1 (by norm_num)]
  norm_num

private theorem a11lb_ringEquiv_f2_eq_one (σ : F2 ≃+* F2) : σ = 1 := by
  haveI : Fintype F2 := Fintype.ofFinite F2
  ext x
  have hx : x ^ 2 = x := by
    have h := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, a11lb_card_f2] at h
    exact h
  have hx01 : x = 0 ∨ x = 1 := by
    have h : x * (x - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_two, hx, sub_self]
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  rcases hx01 with rfl | rfl
  · simp
  · simp

private theorem a11lb_aut_sl9 (β : MulAut (SL 9)) :
    ∃ (g : SL 9) (ε : ℕ), ε ≤ 1 ∧
      β = MulAut.conj g * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 9 F2 ^ ε := by
  obtain ⟨A, σ, ε, hε, hβ⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl (n := 9) (K := F2) (by norm_num) β
  have hσ : σ = 1 := a11lb_ringEquiv_f2_eq_one σ
  have hfield : CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 9) F2 σ = 1 := by
    rw [hσ, map_one]
  have hgcd : Nat.gcd 9 (Nat.card F2 - 1) = 1 := by
    rw [a11lb_card_f2]; norm_num
  obtain ⟨g, hgA⟩ :=
    CFSG.RankThree.PartOne.TAIL.slConjugation_mem_inn (F := F2) (n := 9) hgcd A
  refine ⟨g, ε, hε, ?_⟩
  rw [hβ, hfield, mul_one, ← hgA]

private theorem a11lb_conj_conj {S : Type} [Group S] (g : MulAut S) (C : S) :
    g * MulAut.conj C * g⁻¹ = MulAut.conj (g C) := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul]

private theorem a11lb_aut_decomp {S : Type} [Group S]
    (g δ : MulAut S) (hg2 : g ^ 2 = 1)
    (hout : ¬ ∃ A : S, δ = MulAut.conj A)
    (hclass : ∀ β : MulAut S, ∃ (A : S) (ε : ℕ), ε ≤ 1 ∧ β = MulAut.conj A * g ^ ε) :
    ∃ B : S, g = MulAut.conj B * δ ∧
      ∀ β : MulAut S, ∃ A : S, β = MulAut.conj A ∨ β = MulAut.conj A * δ := by
  have hgδ : ∃ C : S, g * δ⁻¹ = MulAut.conj C := by
    obtain ⟨C, ε, hε, hC⟩ := hclass (g * δ⁻¹)
    interval_cases ε
    · exact ⟨C, hC⟩
    · exfalso
      apply hout
      rw [pow_one] at hC
      have hgg : g * g = 1 := by rw [← pow_two]; exact hg2
      have h1 : g * δ⁻¹ * g = MulAut.conj C := by
        rw [hC, mul_assoc, hgg, mul_one]
      have h2 : δ⁻¹ = MulAut.conj (g C) := by
        rw [← a11lb_conj_conj g C, ← h1]
        rw [show g * (g * δ⁻¹ * g) * g⁻¹ = (g * g) * δ⁻¹ * (g * g⁻¹) by group]
        rw [hgg, mul_inv_cancel]
        group
      refine ⟨(g C)⁻¹, ?_⟩
      have h3 : δ = (MulAut.conj (g C))⁻¹ := by
        rw [← h2, inv_inv]
      rw [h3]
      ext x
      simp [MulAut.conj_apply]
  obtain ⟨B, hB⟩ := hgδ
  have hg : g = MulAut.conj B * δ := by
    rw [← hB, mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨B, hg, ?_⟩
  intro β
  obtain ⟨A, ε, hε, hA⟩ := hclass β
  interval_cases ε
  · exact ⟨A, Or.inl hA⟩
  · refine ⟨A * B, Or.inr ?_⟩
    rw [hA, pow_one, hg, map_mul]
    rfl

private theorem a11lb_tC_neg (c : Fin 3 → ZMod 7) : tC (-c) = (tC c)⁻¹ := by
  rw [tC, tC, ← map_inv]
  rfl

private theorem a11lb_tC_injective : Function.Injective tC := by
  intro c d h
  exact Multiplicative.ofAdd.injective (ggSL9TorusCoord_injective h)

private theorem a11lb_mem_torus_iff {x : GGSL9V ≃ₗ[ZMod 2] GGSL9V} :
    x ∈ ggSL9Torus ↔ ∃ c : Fin 3 → ZMod 7, tC c = x := by
  rw [← range_ggSL9TorusCoord, MonoidHom.mem_range]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨Multiplicative.toAdd f, by rw [tC]; rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩

private theorem a11lb_two_pow_k_ne_neg_one : ∀ k : ZMod 3,
    (2 : ZMod 7) ^ k.val ≠ -1 := by decide

private theorem a11lb_delta_inverts (Θ : SL 9 ≃* GLV) (γ : MulAut GLV)
    (hΘ : ∀ i : Fin 3, Θ (T9 i) = tC (Pi.single i 1))
    (hγ : ∀ c : Fin 3 → ZMod 7, γ (tC c) = tC (-c)) :
    ∀ i : Fin 3, MulAut.congr Θ.symm γ (T9 i) = (T9 i)⁻¹ := by
  intro i
  change Θ.symm (γ (Θ (T9 i))) = (T9 i)⁻¹
  rw [hΘ i, hγ, a11lb_tC_neg, ← hΘ i, map_inv, MulEquiv.symm_apply_apply]

private theorem a11lb_delta_outer (Θ : SL 9 ≃* GLV) (γ : MulAut GLV)
    (hΘ : ∀ i : Fin 3, Θ (T9 i) = tC (Pi.single i 1))
    (hγ : ∀ c : Fin 3 → ZMod 7, γ (tC c) = tC (-c)) :
    ¬ ∃ A : SL 9, MulAut.congr Θ.symm γ = MulAut.conj A := by
  rintro ⟨A, hA⟩
  set n : GGSL9V ≃ₗ[ZMod 2] GGSL9V := Θ A with hn
  have hnx : ∀ x : GGSL9V ≃ₗ[ZMod 2] GGSL9V, n * x * n⁻¹ = γ x := by
    intro x
    obtain ⟨y, rfl⟩ := Θ.surjective x
    have h := congrArg (fun β : MulAut (SL 9) => β y) hA
    change Θ.symm (γ (Θ y)) = A * y * A⁻¹ at h
    have h2 : γ (Θ y) = n * Θ y * n⁻¹ := by
      have := congrArg Θ h
      rw [hn]
      simpa using this
    exact h2.symm
  have hn : n ∈ Subgroup.normalizer (ggSL9Torus : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hnx]
      obtain ⟨c, rfl⟩ := (a11lb_mem_torus_iff).mp hx
      rw [hγ]
      exact (a11lb_mem_torus_iff).mpr ⟨-c, rfl⟩
    · intro hy
      rw [hnx] at hy
      obtain ⟨c, hc⟩ := (a11lb_mem_torus_iff).mp hy
      refine (a11lb_mem_torus_iff).mpr ⟨-c, ?_⟩
      have hcc : γ (tC (-c)) = tC c := by
        rw [hγ]
        congr 1
        exact neg_neg c
      calc tC (-c) = γ.symm (γ (tC (-c))) := (MulEquiv.symm_apply_apply γ _).symm
        _ = γ.symm (tC c) := by rw [hcc]
        _ = γ.symm (γ x) := by rw [← hc]
        _ = x := MulEquiv.symm_apply_apply γ x
  obtain ⟨π, k, hk⟩ := ggSL9_normalizer_torus hn
  have hcoord := hk (Pi.single (0 : Fin 3) 1)
  have heq : tC (-(Pi.single (0 : Fin 3) 1)) =
      tC (vecMul (Pi.single (0 : Fin 3) 1) (a8MonK3 π k)) := by
    rw [← hγ, ← hnx]
    exact hcoord
  have hvec : -(Pi.single (0 : Fin 3) 1) =
      vecMul (Pi.single (0 : Fin 3) 1) (a8MonK3 π k) := a11lb_tC_injective heq
  have h00 : (a8MonK3 π k) 0 0 = -1 := by
    have h := congrFun hvec 0
    simpa [Matrix.vecMul, Pi.single_eq_same] using h.symm
  by_cases hπ : π 0 = 0
  · have : (2 : ZMod 7) ^ (k 0).val = -1 := by
      simpa [a8MonK3, hπ] using h00
    exact a11lb_two_pow_k_ne_neg_one (k 0) this
  · simp [a8MonK3, hπ] at h00
    exact absurd h00 (by decide)

private noncomputable def a11lb_fPowHom {C : Type*} [CommGroup C] (v : Fin 4 → C)
    (hv : ∀ i, v i ^ 7 = 1) : Multiplicative (Fin 4 → ZMod 7) →* C where
  toFun a := ∏ i, v i ^ (Multiplicative.toAdd a i).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]

private theorem a11lb_card_multiplicative_four :
    Nat.card (Multiplicative (Fin 4 → ZMod 7)) = 7 ^ 4 := by
  have h : Nat.card (Fin 4 → ZMod 7) = 7 ^ 4 := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  simpa using h

private theorem a11lb_fPow_injective {G : Type} [Group G] (f : Fin 4 → G) (Bs : Subgroup G)
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hcomm : ∀ i j, f i * f j = f j * f i) (hord : ∀ i, f i ^ 7 = 1)
    (hcard : Nat.card Bs = 7 ^ 4) :
    Function.Injective (fPow f) := by
  set C := Subgroup.closure (Set.range f) with hC
  haveI : IsMulCommutative C := Subgroup.isMulCommutative_closure (fun x hx y hy => by
    rcases hx with ⟨i, rfl⟩
    rcases hy with ⟨j, rfl⟩
    intro _
    exact hcomm i j)
  letI : CommGroup C := IsMulCommutative.instCommGroup
  let v : Fin 4 → C := fun i => ⟨f i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hv : ∀ i, v i ^ 7 = 1 := fun i => Subtype.ext (by simpa [v] using hord i)
  let φ : Multiplicative (Fin 4 → ZMod 7) →* G := C.subtype.comp (a11lb_fPowHom v hv)
  have hφ : ∀ w : Fin 4 → ZMod 7, φ (Multiplicative.ofAdd w) = fPow f w := by
    intro w
    have h1 : a11lb_fPowHom v hv (Multiplicative.ofAdd w) =
        v 0 ^ (w 0).val * v 1 ^ (w 1).val * v 2 ^ (w 2).val * v 3 ^ (w 3).val := by
      simp only [a11lb_fPowHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
      rw [Fin.prod_univ_four]
    show C.subtype (a11lb_fPowHom v hv (Multiplicative.ofAdd w)) = fPow f w
    rw [h1]
    rfl
  have hfi : ∀ i, f i ∈ φ.range := by
    intro i
    refine ⟨Multiplicative.ofAdd (Pi.single i 1), ?_⟩
    rw [hφ]
    have h1 : (1 : ZMod 7).val = 1 := by decide
    fin_cases i <;> simp [fPow, Pi.single_apply, h1]
  have hrange : φ.range = Bs := by
    apply le_antisymm
    · rintro y ⟨a, rfl⟩
      show (a11lb_fPowHom v hv a : G) ∈ Bs
      rw [← hBs]
      exact (a11lb_fPowHom v hv a).2
    · rw [← hBs, Subgroup.closure_le]
      rintro y ⟨i, rfl⟩
      exact hfi i
  have hker : φ.ker = ⊥ := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hrange, hcard, a11lb_card_multiplicative_four] at h
    have hk : Nat.card φ.ker = 1 :=
      Nat.eq_of_mul_eq_mul_right (show 0 < 7 ^ 4 by norm_num) (by rw [one_mul]; exact h)
    exact Subgroup.card_eq_one.mp hk
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  intro v' w' h
  have h' : φ (Multiplicative.ofAdd v') = φ (Multiplicative.ofAdd w') := by
    rw [hφ v', hφ w', h]
  exact Multiplicative.ofAdd.injective (hinj h')

private def a11lb_rho (j : Fin 4) (i : Fin 3) : Fin 4 := Equiv.swap j 3 i.castSucc

private def a11lb_rhoInv (j : Fin 4) (k : Fin 4) (hk : k ≠ j) : Fin 3 :=
  ⟨(Equiv.swap j 3 k).val, by
    have h1 : (Equiv.swap j 3 k).val < 4 := (Equiv.swap j 3 k).isLt
    have h2 : Equiv.swap j 3 k ≠ (3 : Fin 4) := by
      intro h
      apply hk
      have := congrArg (Equiv.swap j 3) h
      simpa using this
    have h3 : (Equiv.swap j 3 k).val ≠ 3 := fun h => h2 (Fin.ext h)
    omega⟩

private theorem a11lb_rho_ne (j : Fin 4) (i : Fin 3) : a11lb_rho j i ≠ j := by
  intro h
  have h' : i.castSucc = (3 : Fin 4) := by
    simpa [a11lb_rho] using congrArg (Equiv.swap j 3) h
  have : i.castSucc.val = 3 := congrArg Fin.val h'
  simp at this
  omega

private theorem a11lb_rho_swap (j : Fin 4) (i : Fin 3) :
    Equiv.swap j 3 (a11lb_rho j i) = i.castSucc := by
  simp [a11lb_rho]

private theorem a11lb_rho_inv_left (j : Fin 4) (k : Fin 4) (hk : k ≠ j) :
    a11lb_rho j (a11lb_rhoInv j k hk) = k := by
  apply Equiv.swap j 3 |>.injective
  rw [a11lb_rho_swap]
  exact Fin.ext (by simp [a11lb_rhoInv])

private theorem a11lb_rho_inv_right (j : Fin 4) (i : Fin 3) :
    a11lb_rhoInv j (a11lb_rho j i) (a11lb_rho_ne j i) = i := by
  apply Fin.ext
  simp [a11lb_rhoInv, a11lb_rho]

private theorem a11lb_T9'_castSucc (i : Fin 3) : T9' (i.castSucc : Fin 4) = T9 i := by
  simp [T9', i.isLt]

private theorem a11lb_Phi_T9 {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G) (f : Fin 4 → G)
    (hΦval : ∀ l k : Fin 4, k ≠ l → Φ l (T9' (Equiv.swap l 3 k)) = f k) (j : Fin 4)
    (i : Fin 3) : Φ j (T9 i) = f (a11lb_rho j i) := by
  have h := hΦval j (a11lb_rho j i) (a11lb_rho_ne j i)
  rw [a11lb_rho, Equiv.swap_apply_self, a11lb_T9'_castSucc] at h
  exact h

private theorem a11lb_fPow_single_smul {G : Type} [Group G] (f : Fin 4 → G) (u : ZMod 7)
    (k : Fin 4) : fPow f (u • ev k) = f k ^ u.val := by
  fin_cases k <;> simp [fPow, ev, Pi.smul_apply, Pi.single_apply]

private theorem a11lb_rho_surj (j : Fin 4) (k : Fin 4) (hk : k ≠ j) :
    ∃ i : Fin 3, a11lb_rho j i = k := ⟨a11lb_rhoInv j k hk, a11lb_rho_inv_left j k hk⟩

private theorem a11lb_center_eq_bot_of_equiv {G : Type} [Group G] {Kj : Subgroup G}
    (Ψ : ↥Kj ≃* GLV) : Subgroup.center ↥Kj = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : Ψ z ∈ Subgroup.center GLV := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨v, rfl⟩ := Ψ.surjective w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz v]
  rw [center_ggSL9_eq_bot, Subgroup.mem_bot] at hz'
  exact Ψ.injective (by rw [hz', map_one])

private theorem a11lb_zpowers_inf_eq_bot {G : Type} [Group G] {Kj : Subgroup G} {f : Fin 4 → G}
    {j : Fin 4} (hKj : CFSG.Assembly.IsComponentOf Kj (Subgroup.centralizer ({f j} : Set G)))
    (hZ : Subgroup.center ↥Kj = ⊥) :
    Subgroup.zpowers (f j) ⊓ Kj = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [Subgroup.mem_bot]
  have hxZ : (⟨x, hx2⟩ : ↥Kj) ∈ Subgroup.center ↥Kj := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx1
    have hc := Subgroup.mem_centralizer_iff.mp (hKj.1 z.2)
    have hcomm : Commute (f j) (z : G) := hc (f j) rfl
    simpa using (hcomm.zpow_left a).eq.symm
  have hx1' : (⟨x, hx2⟩ : ↥Kj) = 1 := by
    have := hxZ
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  exact congrArg Subtype.val hx1'

private theorem a11lb_ggSL9Torus_eq_closure :
    ggSL9Torus = Subgroup.closure (Set.range (fun i : Fin 3 => tC (Pi.single i 1))) := by
  rw [← range_ggSL9TorusCoord]
  apply le_antisymm
  · rintro y ⟨f, rfl⟩
    have hf : f ∈ Subgroup.closure (Set.range (fun i : Fin 3 =>
        Multiplicative.ofAdd (Pi.single i 1 : Fin 3 → ZMod 7))) := by
      have hprod : (∏ i : Fin 3,
            (Multiplicative.ofAdd (Pi.single i 1 : Fin 3 → ZMod 7)) ^
              ((Multiplicative.toAdd f) i).val)
          = Multiplicative.ofAdd (∑ i : Fin 3,
              ((Multiplicative.toAdd f) i).val • (Pi.single i 1 : Fin 3 → ZMod 7)) := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_ofAdd]
        induction (Finset.univ : Finset (Fin 3)) using Finset.induction with
        | empty => simp
        | insert i s hi ih =>
          rw [Finset.prod_insert hi, Finset.sum_insert hi, toAdd_mul, toAdd_pow, toAdd_ofAdd, ih]
      have hsum : (∑ i : Fin 3,
            ((Multiplicative.toAdd f) i).val • (Pi.single i 1 : Fin 3 → ZMod 7)) =
            Multiplicative.toAdd f := by
        funext j
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply]
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hbj
          rw [Pi.single_eq_of_ne (Ne.symm hbj)]
          simp
        · intro hj; exact absurd (Finset.mem_univ j) hj
      rw [← ofAdd_toAdd f]
      rw [← hsum, ← hprod]
      refine Subgroup.prod_mem _ (fun i _ => ?_)
      refine Subgroup.pow_mem _ ?_ _
      exact Subgroup.subset_closure (Set.mem_range_self i)
    have hle : Subgroup.closure (Set.range (fun i : Fin 3 =>
        Multiplicative.ofAdd (Pi.single i 1 : Fin 3 → ZMod 7))) ≤
        (Subgroup.closure (Set.range (fun i : Fin 3 => tC (Pi.single i 1)))).comap
          ggSL9TorusCoord := by
      apply (Subgroup.closure_le ((Subgroup.closure (Set.range (fun i : Fin 3 =>
        tC (Pi.single i 1)))).comap ggSL9TorusCoord)).mpr
      rintro z ⟨i, rfl⟩
      show tC (Pi.single i 1) ∈ Subgroup.closure (Set.range (fun i : Fin 3 => tC (Pi.single i 1)))
      exact Subgroup.subset_closure ⟨i, rfl⟩
    exact hle hf
  · apply (Subgroup.closure_le ggSL9TorusCoord.range).mpr
    rintro y ⟨i, rfl⟩
    exact ⟨Multiplicative.ofAdd (Pi.single i 1), rfl⟩

private noncomputable def a11lb_permExtend (j : Fin 4) (π : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 4) where
  toFun i := if hi : i = j then j else a11lb_rho j (π (a11lb_rhoInv j i hi))
  invFun i := if hi : i = j then j else a11lb_rho j (π.symm (a11lb_rhoInv j i hi))
  left_inv i := by
    by_cases hi : i = j
    · subst hi; simp
    · have hne : a11lb_rho j (π (a11lb_rhoInv j i hi)) ≠ j := a11lb_rho_ne j _
      dsimp only
      rw [dif_neg hi, dif_neg hne, a11lb_rho_inv_right, Equiv.symm_apply_apply,
        a11lb_rho_inv_left]
  right_inv i := by
    by_cases hi : i = j
    · subst hi; simp
    · have hne : a11lb_rho j (π.symm (a11lb_rhoInv j i hi)) ≠ j := a11lb_rho_ne j _
      dsimp only
      rw [dif_neg hi, dif_neg hne, a11lb_rho_inv_right, Equiv.apply_symm_apply,
        a11lb_rho_inv_left]

private theorem a11lb_permExtend_fix (j : Fin 4) (π : Equiv.Perm (Fin 3)) :
    a11lb_permExtend j π j = j := by
  simp [a11lb_permExtend]

private theorem a11lb_permExtend_rho (j : Fin 4) (π : Equiv.Perm (Fin 3)) (i : Fin 3) :
    a11lb_permExtend j π (a11lb_rho j i) = a11lb_rho j (π i) := by
  have hne : a11lb_rho j i ≠ j := a11lb_rho_ne j i
  change (if hi : a11lb_rho j i = j then j
    else a11lb_rho j (π (a11lb_rhoInv j (a11lb_rho j i) hi))) = a11lb_rho j (π i)
  rw [dif_neg hne, a11lb_rho_inv_right]

private theorem a11lb_two_pow_val_mem : ∀ km : ZMod 3,
    (2 : ZMod 7) ^ km.val = 1 ∨ (2 : ZMod 7) ^ km.val = 2 ∨ (2 : ZMod 7) ^ km.val = 4 :=
  by decide

private theorem a11lb_neg_mul_two_pow_val_mem : ∀ km : ZMod 3,
    (-1 : ZMod 7) * (2 : ZMod 7) ^ km.val = 3 ∨
      (-1 : ZMod 7) * (2 : ZMod 7) ^ km.val = 5 ∨
      (-1 : ZMod 7) * (2 : ZMod 7) ^ km.val = 6 :=
  by decide

private theorem a11lb_fPow_ev {G : Type} [Group G] (f : Fin 4 → G) (i : Fin 4) :
    fPow f (ev i) = f i := by
  have h1 : (1 : ZMod 7).val = 1 := by decide
  have := a11lb_fPow_single_smul f 1 i
  simpa [h1] using this

private theorem a11lb_vecMul_single_monK3 (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3)
    (m : Fin 3) : Matrix.vecMul (Pi.single m 1) (a8MonK3 π k) =
      (2 : ZMod 7) ^ (k m).val • Pi.single (π m) 1 := by
  funext i
  rw [Matrix.vecMul, dotProduct]
  simp only [Pi.smul_apply]
  rw [Finset.sum_eq_single m]
  · by_cases h : π m = i
    · simp [a8MonK3, h]
    · simp [a8MonK3, h, Pi.single_eq_of_ne (Ne.symm h)]
  · intro b _ hbm
    rw [Pi.single_eq_of_ne hbm, zero_mul]
  · intro hm; exact absurd (Finset.mem_univ m) hm

private theorem a11lb_tC_smul (u : ZMod 7) (c : Fin 3 → ZMod 7) :
    tC (u • c) = (tC c) ^ u.val := by
  simp only [tC]
  rw [show Multiplicative.ofAdd (u • c) = (Multiplicative.ofAdd c) ^ u.val from ?_, map_pow]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_pow, toAdd_ofAdd]
  funext i
  simp only [Pi.smul_apply, Pi.mul_apply]
  rw [← ZMod.natCast_zmod_val u]
  simp

private theorem a11lb_theta_symm_tC_single (Θ : SL 9 ≃* GLV)
    (hΘ : ∀ i : Fin 3, Θ (T9 i) = tC (Pi.single i 1)) (i : Fin 3) (u : ZMod 7) :
    Θ.symm (tC (u • Pi.single i 1)) = (T9 i) ^ u.val := by
  rw [a11lb_tC_smul, ← hΘ i, ← map_pow, MulEquiv.symm_apply_apply]

private theorem a11lb_finish {G : Type} [Group G]
    (f : Fin 4 → G) (h : G) (j : Fin 4) (Φ : Fin 4 → SL 9 →* G) (Θ : SL 9 ≃* GLV)
    (hΘ : ∀ i : Fin 3, Θ (T9 i) = tC (Pi.single i 1))
    (e : SL 9 ≃* ↥((Φ j).range))
    (a : MulAut ↥((Φ j).range)) (β : MulAut (SL 9))
    (hae : ∀ x : SL 9, a (e x) = e (β x))
    (ha : ∀ x : ↥((Φ j).range), (a x : G) = h * (x : G) * h⁻¹)
    (hΦval : ∀ l k : Fin 4, k ≠ l → Φ l (T9' (Equiv.swap l 3 k)) = f k)
    (hf_eq_e : ∀ i : Fin 3, (e (T9 i) : G) = f (a11lb_rho j i))
    {M : Certificates.A8Nbr476.M4} (hM : ConjMat f h M)
    (hfpow_inj : Function.Injective (fPow f)) (hfix : h * f j * h⁻¹ = f j)
    (D : Certificates.A8Nbr476.M3) (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3)
    (hD : D = a8MonK3 π k)
    (s : ZMod 7) (hs : s = 1 ∨ s = -1)
    (hact : ∀ c : Fin 3 → ZMod 7,
      β (Θ.symm (tC c)) = Θ.symm (tC (s • vecMul c D))) :
    Good9B j M := by
  have hrowj : vecMul (ev j) M = ev j := by
    apply hfpow_inj
    rw [← hM (ev j), a11lb_fPow_ev, hfix]
  have hrow : ∀ m : Fin 3, vecMul (ev (a11lb_rho j m)) M =
      (s * (2 : ZMod 7) ^ (k m).val) • ev (a11lb_rho j (π m)) := by
    intro m
    apply hfpow_inj
    set u : ZMod 7 := s * (2 : ZMod 7) ^ (k m).val with hu
    have hleft : fPow f (vecMul (ev (a11lb_rho j m)) M) =
        f (a11lb_rho j (π m)) ^ u.val := by
      have h1 : fPow f (vecMul (ev (a11lb_rho j m)) M) = h * f (a11lb_rho j m) * h⁻¹ := by
        rw [← hM (ev (a11lb_rho j m)), a11lb_fPow_ev]
      have h2 : h * f (a11lb_rho j m) * h⁻¹ = (e (β (T9 m)) : G) := by
        calc h * f (a11lb_rho j m) * h⁻¹
            = h * (e (T9 m) : G) * h⁻¹ := by rw [hf_eq_e m]
          _ = (a (e (T9 m)) : G) := (ha (e (T9 m))).symm
          _ = (e (β (T9 m)) : G) := by rw [hae]
      rw [h1, h2]
      have hT9m : T9 m = Θ.symm (tC (Pi.single m 1)) := by
        rw [← hΘ m, MulEquiv.symm_apply_apply]
      have hβm : β (T9 m) = Θ.symm (tC (u • Pi.single (π m) 1)) := by
        rw [hT9m, hact, hD, a11lb_vecMul_single_monK3, smul_smul, ← hu]
      rw [hβm, a11lb_theta_symm_tC_single Θ hΘ (π m) u]
      rw [show (e ((T9 (π m)) ^ u.val) : G) = f (a11lb_rho j (π m)) ^ u.val from by
        rw [map_pow, Subgroup.coe_pow, hf_eq_e]]
    rw [hleft, a11lb_fPow_single_smul]
  refine ⟨hrowj, a11lb_permExtend j π,
    (fun i => if hi : i = j then 1 else s * (2 : ZMod 7) ^ (k (a11lb_rhoInv j i hi)).val),
    a11lb_permExtend_fix j π, ?_, ?_⟩
  · intro i hi
    have h1 := hrow (a11lb_rhoInv j i hi)
    rw [a11lb_rho_inv_left j i hi] at h1
    rw [h1]
    simp only [dif_neg hi]
    congr 1
    congr 1
    conv_rhs => rw [← a11lb_rho_inv_left j i hi]
    rw [a11lb_permExtend_rho]
  · rcases hs with rfl | rfl
    · left; intro i hi
      simpa [dif_neg hi] using a11lb_two_pow_val_mem (k (a11lb_rhoInv j i hi))
    · right; intro i hi
      simpa [dif_neg hi] using a11lb_neg_mul_two_pow_val_mem (k (a11lb_rhoInv j i hi))

theorem a11Lemma89BInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
      (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
      (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
      ∀ (h : G) (j : Fin 4), h ∈ Subgroup.normalizer (Bs : Set G) → h * f j * h⁻¹ = f j →
        ∀ M : Certificates.A8Nbr476.M4, ConjMat f h M → Good9B j M := by
  intro G _inst _fin B Bs x L D J y K φ₃ f n Φ ρ hctx h j hN hfix M hM
  haveI : Finite (SL 9) := by infer_instance
  obtain ⟨-, -, hFrame, hExtra, hCoh, -⟩ := hctx
  obtain ⟨hGlue, hφ₃K, hNbr, hBs, hx, hy, hD, hnL, hJK, hJ9⟩ := hFrame
  obtain ⟨hφ₃inj, hfT9, hfcomm, hforder, hfcard, hn3, hnconj, hKcomp⟩ := hGlue
  obtain ⟨-, hExtraClause⟩ := hExtra
  obtain ⟨hΦ3, hΦinj, hΦrange, hΦval, hCohClause⟩ := hCoh
  have hf7 : ∀ i, f i ^ 7 = 1 := fun i => by rw [← hforder i]; exact pow_orderOf_eq_one _
  have hfcardBs : Nat.card Bs = 7 ^ 4 := hBs ▸ hfcard
  have hfpow_inj : Function.Injective (fPow f) :=
    a11lb_fPow_injective f Bs hBs hfcomm hf7 hfcardBs
  let Kj : Subgroup G := (Φ j).range
  have hKj : CFSG.Assembly.IsComponentOf Kj (Subgroup.centralizer ({f j} : Set G)) := by
    have hfj : n j * f 3 * (n j)⁻¹ = f j := by simpa using hnconj j 3
    have h1 : CFSG.Assembly.IsComponentOf (φ₃.range.map (MulAut.conj (n j)).toMonoidHom)
        (Subgroup.centralizer ({f j} : Set G)) := by
      have h2 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hKcomp (n j)
      rwa [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton, hfj] at h2
    dsimp only [Kj]
    rwa [hΦrange j]
  have hZj : Subgroup.center ↥Kj = ⊥ := by
    obtain ⟨Θ, hΘ⟩ := a11TorusModelInput_holds
    let e : SL 9 ≃* ↥Kj := MonoidHom.ofInjective (hΦinj j)
    exact a11lb_center_eq_bot_of_equiv (e.symm.trans Θ)
  have hzj : Subgroup.zpowers (f j) ⊓ Kj = ⊥ := a11lb_zpowers_inf_eq_bot hKj hZj
  let Tj : Subgroup G := Subgroup.closure {z : G | ∃ i : Fin 4, i ≠ j ∧ z = f i}
  have hTj_le_Kj : Tj ≤ Kj := by
    apply (Subgroup.closure_le Kj).mpr
    rintro z ⟨i, hi, rfl⟩
    obtain ⟨m, rfl⟩ := a11lb_rho_surj j i hi
    rw [← a11lb_Phi_T9 Φ f hΦval j m]
    exact ⟨T9 m, rfl⟩
  have hBs_eq_Tj : Bs = Subgroup.zpowers (f j) ⊔ Tj := by
    rw [← hBs]
    have hrange : Set.range f = insert (f j) {z : G | ∃ i : Fin 4, i ≠ j ∧ z = f i} := by
      ext z; constructor
      · rintro ⟨i, rfl⟩
        by_cases hi : i = j
        · subst hi; exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩
      · intro hz
        rcases hz with hz | hz
        · exact ⟨j, hz.symm⟩
        · rcases hz with ⟨i, hi, rfl⟩; exact ⟨i, rfl⟩
    rw [hrange, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
  have hTj_le_Bs : Tj ≤ Bs := hBs_eq_Tj ▸ le_sup_right
  have hcomm_sup : ∀ x ∈ Subgroup.zpowers (f j), ∀ y ∈ Tj, x * y = y * x := by
    intro x hx y hy
    have hxcomm : Tj ≤ Subgroup.centralizer ({x} : Set G) := by
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      change Subgroup.closure {z : G | ∃ i : Fin 4, i ≠ j ∧ z = f i} ≤
        Subgroup.centralizer ({f j ^ a} : Set G)
      rw [Subgroup.closure_le]
      rintro z ⟨i, hi, rfl⟩
      change f i ∈ Subgroup.centralizer ({f j ^ a} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have hcomm : Commute (f j) (f i) := hfcomm j i
      exact (hcomm.zpow_left a).eq
    have hmem : y ∈ Subgroup.centralizer ({x} : Set G) := hxcomm hy
    exact Subgroup.mem_centralizer_iff.mp hmem x rfl
  have hcard_formula :=
    CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers (f j)) Tj hcomm_sup
  have hinf : Subgroup.zpowers (f j) ⊓ Tj = ⊥ := by
    rw [eq_bot_iff]
    calc Subgroup.zpowers (f j) ⊓ Tj ≤ Subgroup.zpowers (f j) ⊓ Kj := inf_le_inf_left _ hTj_le_Kj
      _ = ⊥ := hzj
  have hTj_card : Nat.card Tj = 7 ^ 3 := by
    have h := hcard_formula.1
    rw [← hBs_eq_Tj, hinf, hfcardBs, Nat.card_zpowers, hforder j] at h
    simp only [Subgroup.card_bot, mul_one] at h
    have h7 : (7 : ℕ) * 7 ^ 3 = 7 ^ 4 := by norm_num
    rw [← h7] at h
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h).symm
  have hCbs : Bs ⊓ Subgroup.centralizer (Kj : Set G) = Subgroup.zpowers (f j) := by
    apply le_antisymm
    · intro b hb
      rw [Subgroup.mem_inf] at hb
      obtain ⟨hbBs, hbC⟩ := hb
      have hset := hcard_formula.2
      have hbmem : b ∈ ((Subgroup.zpowers (f j) ⊔ Tj : Subgroup G) : Set G) := by
        rw [← hBs_eq_Tj]; exact hbBs
      rw [hset, Set.mem_mul] at hbmem
      obtain ⟨a, ha, t, ht, hat⟩ := hbmem
      have haC : a ∈ Subgroup.centralizer (Kj : Set G) := by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hcz : Commute (f j) (z : G) := (Subgroup.mem_centralizer_iff.mp (hKj.1 hz)) (f j) rfl
        exact (hcz.zpow_left m).eq.symm
      have htC : t ∈ Subgroup.centralizer (Kj : Set G) := by
        have htb : t = a⁻¹ * b := by rw [← hat]; group
        rw [htb]
        exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem haC) hbC
      have htZ : (⟨t, hTj_le_Kj ht⟩ : ↥Kj) ∈ Subgroup.center ↥Kj := by
        rw [Subgroup.mem_center_iff]
        intro z
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp htC z z.2
      have ht1 : t = 1 := by
        have := htZ
        rw [hZj, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      rw [← hat, ht1, mul_one]
      exact ha
    · intro b hb
      rw [Subgroup.mem_inf]
      constructor
      · rw [hBs_eq_Tj]; exact Subgroup.mem_sup_left hb
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        have hcz : Commute (f j) (z : G) := (Subgroup.mem_centralizer_iff.mp (hKj.1 hz)) (f j) rfl
        exact (hcz.zpow_left m).eq.symm
  have hKjN : h ∈ Subgroup.normalizer (Kj : Set G) := by
    by_contra hnot
    have hhH : h ∈ Subgroup.centralizer ({f j} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      calc f j * h = (h * f j * h⁻¹) * h := by rw [hfix]
        _ = h * f j := by group
    have hKjh : CFSG.Assembly.IsComponentOf (Kj.map (MulAut.conj h).toMonoidHom)
        (Subgroup.centralizer ({f j} : Set G)) := by
      have h2 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hKj h
      rwa [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton, hfix] at h2
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hKjh hKj with heq | hcom
    · exact hnot (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
    · have hle : Kj.map (MulAut.conj h).toMonoidHom ≤ Subgroup.centralizer (Kj : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcom
      have hTjh_le_Bs : Tj.map (MulAut.conj h).toMonoidHom ≤ Bs := by
        rw [Subgroup.map_le_iff_le_comap]
        intro z hz
        exact (Subgroup.mem_normalizer_iff.mp hN z).mp (hTj_le_Bs hz)
      have hTjh_le_C : Tj.map (MulAut.conj h).toMonoidHom ≤ Subgroup.centralizer (Kj : Set G) :=
        (Subgroup.map_mono hTj_le_Kj).trans hle
      have hTjh_le : Tj.map (MulAut.conj h).toMonoidHom ≤ Subgroup.zpowers (f j) := by
        rw [← hCbs]
        exact le_inf hTjh_le_Bs hTjh_le_C
      have hcard_map : Nat.card (Tj.map (MulAut.conj h).toMonoidHom) = 7 ^ 3 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hTj_card]
      have hle7 : Nat.card (Tj.map (MulAut.conj h).toMonoidHom) ≤ 7 := by
        have h1 : Nat.card (Tj.map (MulAut.conj h).toMonoidHom) ≤
            Nat.card (Subgroup.zpowers (f j)) :=
          Nat.card_le_card_of_injective (Subgroup.inclusion hTjh_le)
            (Subgroup.inclusion_injective _)
        rw [Nat.card_zpowers, hforder j] at h1
        exact h1
      omega
  let e : SL 9 ≃* ↥Kj := MonoidHom.ofInjective (hΦinj j)
  let a : MulAut ↥Kj := Kj.normalizerMonoidHom ⟨h, hKjN⟩
  let β : MulAut (SL 9) := (MulAut.congr e).symm a
  have hae : ∀ x : SL 9, a (e x) = e (β x) := by
    intro x
    have hβa : MulAut.congr e β = a := MulEquiv.apply_symm_apply (MulAut.congr e) a
    rw [← hβa]
    show (MulAut.congr e β) (e x) = e (β x)
    rw [MulAut.congr_apply]
    simp
  have hf_eq_e : ∀ i : Fin 3, (e (T9 i) : G) = f (a11lb_rho j i) := by
    intro i
    change Φ j (T9 i) = f (a11lb_rho j i)
    exact a11lb_Phi_T9 Φ f hΦval j i
  obtain ⟨Θ, hΘ⟩ := a11TorusModelInput_holds
  obtain ⟨γ, hγ⟩ := a11GraphAutInput_holds
  let δ : MulAut (SL 9) := MulAut.congr Θ.symm γ
  have hδ2 : (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 9 F2) ^ 2 = 1 :=
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_sq 9 F2
  have hδout : ¬ ∃ A : SL 9, δ = MulAut.conj A :=
    a11lb_delta_outer Θ γ hΘ hγ
  obtain ⟨B, hBg, hdecomp⟩ :=
    a11lb_aut_decomp (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 9 F2) δ
      hδ2 hδout (fun β' => a11lb_aut_sl9 β')
  let T9torus : Subgroup (SL 9) := Subgroup.closure (Set.range T9)
  have hTj_eq : Tj = T9torus.map (Φ j) := by
    change Subgroup.closure {z : G | ∃ i : Fin 4, i ≠ j ∧ z = f i} = _
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨m, hm⟩ := a11lb_rho_surj j i hi
      rw [← hm]
      exact ⟨T9 m, Set.mem_range_self m, a11lb_Phi_T9 Φ f hΦval j m⟩
    · rintro ⟨y, hy, hzy⟩
      obtain ⟨m, hm⟩ := Set.mem_range.mp hy
      exact ⟨a11lb_rho j m, a11lb_rho_ne j m,
        by rw [← hzy, ← hm, a11lb_Phi_T9 Φ f hΦval j m]⟩
  have hTj_eq_inf : Tj = Kj ⊓ Bs := by
    apply le_antisymm
    · exact le_inf hTj_le_Kj hTj_le_Bs
    · intro b hb
      rw [Subgroup.mem_inf] at hb
      obtain ⟨hbK, hbB⟩ := hb
      have hbmem : b ∈ ((Subgroup.zpowers (f j) ⊔ Tj : Subgroup G) : Set G) := by
        rw [← hBs_eq_Tj]; exact hbB
      rw [hcard_formula.2, Set.mem_mul] at hbmem
      obtain ⟨a, ha, t, ht, hat⟩ := hbmem
      have haK : a ∈ Kj := by
        have : a = b * t⁻¹ := by rw [← hat]; group
        rw [this]
        exact Kj.mul_mem hbK (Kj.inv_mem (hTj_le_Kj ht))
      have haz : a ∈ Subgroup.zpowers (f j) ⊓ Kj := ⟨ha, haK⟩
      rw [hzj, Subgroup.mem_bot] at haz
      rw [← hat, haz, one_mul]
      exact ht
  have hNTj : h ∈ Subgroup.normalizer (Tj : Set G) := by
    rw [hTj_eq_inf, Subgroup.mem_normalizer_iff]
    intro x; constructor
    · intro hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨(Subgroup.mem_normalizer_iff.mp hKjN x).mp hx.1,
             (Subgroup.mem_normalizer_iff.mp hN x).mp hx.2⟩
    · intro hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨(Subgroup.mem_normalizer_iff.mp hKjN x).mpr hx.1,
             (Subgroup.mem_normalizer_iff.mp hN x).mpr hx.2⟩
  have hβT0 : ∀ x ∈ T9torus, β x ∈ T9torus := by
    intro x hx
    have hxTj : (e x : G) ∈ Tj := by
      rw [hTj_eq]; exact ⟨x, hx, rfl⟩
    have hhx : h * (e x : G) * h⁻¹ ∈ Tj :=
      (Subgroup.mem_normalizer_iff.mp hNTj (e x)).mp hxTj
    rw [hTj_eq] at hhx
    obtain ⟨y, hy, hyx⟩ := hhx
    have hβx : β x = y := by
      apply e.injective
      apply Subtype.ext
      rw [← hae x, Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact hyx.symm
    rw [hβx]; exact hy
  have hβMap : T9torus.map (β : SL 9 →* SL 9) = T9torus := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.map_le_iff_le_comap]; exact hβT0
    · rw [Subgroup.card_map_of_injective β.injective]
  have hδt9 : ∀ c : Fin 3 → ZMod 7, δ (Θ.symm (tC c)) = Θ.symm (tC (-c)) := by
    intro c
    change Θ.symm (γ (Θ (Θ.symm (tC c)))) = Θ.symm (tC (-c))
    rw [MulEquiv.apply_symm_apply, hγ]
    try rfl
  have hδT : ∀ x ∈ T9torus, δ x ∈ T9torus := by
    have hle : Subgroup.closure (Set.range T9) ≤ T9torus.comap (δ : SL 9 →* SL 9) := by
      apply (Subgroup.closure_le (T9torus.comap (δ : SL 9 →* SL 9))).mpr
      rintro z ⟨i, rfl⟩
      show δ (T9 i) ∈ T9torus
      rw [a11lb_delta_inverts Θ γ hΘ hγ i]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i, rfl⟩)
    intro x hx
    exact hle hx
  have hδMap : T9torus.map (δ : SL 9 →* SL 9) = T9torus := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.map_le_iff_le_comap]; exact hδT
    · rw [Subgroup.card_map_of_injective δ.injective]
  have hδinvT : ∀ x ∈ T9torus, δ⁻¹ x ∈ T9torus := by
    intro x hx
    have hx' : x ∈ T9torus.map (δ : SL 9 →* SL 9) := by rw [hδMap]; exact hx
    rcases hx' with ⟨y, hy, hyx⟩
    rw [← hyx]; simpa using hy
  have hδinvMap : T9torus.map ((δ⁻¹ : MulAut (SL 9)) : SL 9 →* SL 9) = T9torus := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.map_le_iff_le_comap]; exact hδinvT
    · rw [Subgroup.card_map_of_injective (δ⁻¹).injective]
  have hΘT : T9torus.map (Θ : SL 9 →* GLV) =
      Subgroup.closure (Set.range (fun i : Fin 3 => tC (Pi.single i 1))) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext y; constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨i, rfl⟩ := hx
      exact ⟨i, (hΘ i).symm.trans hxy⟩
    · rintro ⟨i, rfl⟩
      exact ⟨T9 i, Set.mem_range_self i, hΘ i⟩
  have hNA : ∀ A : SL 9, A ∈ Subgroup.normalizer (T9torus : Set (SL 9)) →
      Θ A ∈ Subgroup.normalizer (ggSL9Torus : Set GLV) := by
    intro A hA
    rw [a11lb_ggSL9Torus_eq_closure, ← hΘT, Subgroup.mem_normalizer_iff]
    intro y; constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨A * z * A⁻¹, (Subgroup.mem_normalizer_iff.mp hA z).mp hz,
        by rw [map_mul, map_mul, map_inv]; rfl⟩
    · rintro ⟨w, hw, hwy⟩
      refine ⟨A⁻¹ * w * A, ?_, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hA) w).mp hw
      rw [map_mul, map_mul, map_inv]
      rw [hwy]
      change (Θ A)⁻¹ * (Θ A * y * (Θ A)⁻¹) * Θ A = y
      group
  have ha_coe : ∀ x : ↥Kj, (a x : G) = h * (x : G) * h⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ ⟨h, hKjN⟩ x
  rcases hdecomp β with ⟨Aβ, hAβ | hAβ⟩
  · have hAβN : Aβ ∈ Subgroup.normalizer (T9torus : Set (SL 9)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      rw [show MulAut.conj Aβ = β from hAβ.symm]
      simpa using hβMap
    have hn := hNA Aβ hAβN
    obtain ⟨π, k, hk⟩ := ggSL9_normalizer_torus hn
    let D : Certificates.A8Nbr476.M3 := a8MonK3 π k
    have hD : D = a8MonK3 π k := rfl
    have ht9pow : ∀ c, Θ (Θ.symm (tC c)) = tC c := fun c => MulEquiv.apply_symm_apply Θ _
    have hact : ∀ c : Fin 3 → ZMod 7,
        β (Θ.symm (tC c)) = Θ.symm (tC ((1 : ZMod 7) • vecMul c D)) := by
      intro c
      rw [one_smul]
      apply Θ.injective
      calc Θ (β (Θ.symm (tC c)))
          = Θ Aβ * tC c * (Θ Aβ)⁻¹ := by
            rw [hAβ, MulAut.conj_apply]
            simp only [map_mul, map_mul, map_inv, ht9pow]
        _ = tC (vecMul c D) := by rw [hD]; exact hk c
        _ = Θ (Θ.symm (tC (vecMul c D))) := (ht9pow _).symm
    exact a11lb_finish f h j Φ Θ hΘ e a β hae ha_coe hΦval hf_eq_e hM hfpow_inj hfix
      D π k hD 1 (Or.inl rfl) hact
  · have hAβN : Aβ ∈ Subgroup.normalizer (T9torus : Set (SL 9)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have h1 : MulAut.conj Aβ = β * δ⁻¹ := by rw [hAβ]; group
      rw [h1]
      rw [show ((β * δ⁻¹ : MulAut (SL 9)) : SL 9 →* SL 9) =
        (β : SL 9 →* SL 9).comp ((δ⁻¹ : MulAut (SL 9)) : SL 9 →* SL 9) from rfl]
      rw [← Subgroup.map_map, hδinvMap, hβMap]
    have hn := hNA Aβ hAβN
    obtain ⟨π, k, hk⟩ := ggSL9_normalizer_torus hn
    let D : Certificates.A8Nbr476.M3 := a8MonK3 π k
    have hD : D = a8MonK3 π k := rfl
    have ht9pow : ∀ c, Θ (Θ.symm (tC c)) = tC c := fun c => MulEquiv.apply_symm_apply Θ _
    have hact : ∀ c : Fin 3 → ZMod 7,
        β (Θ.symm (tC c)) = Θ.symm (tC ((-1 : ZMod 7) • vecMul c D)) := by
      intro c
      apply Θ.injective
      calc Θ (β (Θ.symm (tC c)))
          = Θ Aβ * tC (-c) * (Θ Aβ)⁻¹ := by
            rw [hAβ, MulAut.mul_apply, MulAut.conj_apply]
            simp only [map_mul, map_mul, map_inv, ht9pow, hδt9]
        _ = tC (vecMul (-c) D) := by rw [hD]; exact hk (-c)
        _ = tC ((-1 : ZMod 7) • vecMul c D) := by
            congr 1
            funext m
            simp only [Matrix.vecMul, dotProduct, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
            calc ∑ x, (-c x) * D x m = ∑ x, -(c x * D x m) :=
                  Finset.sum_congr rfl (fun i _ => neg_mul (c i) (D i m))
              _ = -(∑ x, c x * D x m) := Finset.sum_neg_distrib (fun x => c x * D x m)
              _ = -1 * ∑ x, c x * D x m := (neg_one_mul _).symm
        _ = Θ (Θ.symm (tC ((-1 : ZMod 7) • vecMul c D))) := (ht9pow _).symm
    exact a11lb_finish f h j Φ Θ hΘ e a β hae ha_coe hΦval hf_eq_e hM hfpow_inj hfix
      D π k hD (-1) (Or.inr rfl) hact

end CFSG.StandardType.A11

end
