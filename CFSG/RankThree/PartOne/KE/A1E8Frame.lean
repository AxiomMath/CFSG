module

public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.Lattice.SteinbergBIE8OrderSeven
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers
public import CFSG.RankThree.PartOne.KE.CTStatement

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LieType.Steinberg.Adjoint (iform iform_self_of_isRoot)
open CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

section General

variable {τ : Tag} {L : Type} [Field L]

theorem rootSL2_WSL_mem_monomial_gen {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ h : rootSL2 τ L β WSL ∈ monomialSubgroup τ L,
      weylQuotientHom τ L ⟨_, h⟩ = rootReflection β := by
  obtain ⟨hn, hπ⟩ := (exceptional_Lang_root_rank_one_torus_transport τ L hβ).2.2.1 1
  have e : rootWeylSL2 τ L β 1 = rootSL2 τ L β WSL := by
    rw [rootWeylSL2, nSL_one]
  rw [e] at hn
  refine ⟨hn, ?_⟩
  rw [← hπ]
  congr 1

theorem iform_eq_dotProduct (hsym : τ.symmetrizer = 1) (x y : Fin τ.rank → ℤ) :
    iform x y = x ⬝ᵥ (τ.cartan *ᵥ y) := by
  have h : τ.symmetrizedCartan = τ.cartan := by
    rw [Tag.symmetrizedCartan, hsym, one_mul]
  simp only [iform, h, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem rootReflection_smul_eq_rootReflMat (hsym : τ.symmetrizer = 1) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (v : Fin τ.rank → ℤ) :
    rootReflection β • v = rootReflMat τ β *ᵥ v := by
  have hββ : iform β β = 2 := by
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hβ
    have : τ.symmetrizer j j = 1 := by rw [hsym]; simp
    rw [hj, this]
    ring
  rw [((exceptional_Lang_root_rank_one_torus_transport τ ℚ hβ).2.2.2.1 v).1, hββ]
  have h1 : 2 * iform β v / 2 = iform β v := by omega
  rw [h1]
  ext i
  have h2 : (Matrix.vecMulVec β (Matrix.vecMul β τ.cartan) *ᵥ v) i = β i * iform β v := by
    rw [Matrix.vecMulVec_mulVec, ← Matrix.dotProduct_mulVec, ← iform_eq_dotProduct hsym]
    simp
  simp only [rootReflMat, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, h2, mul_comm]

theorem list_prod_rootReflection_smul (hsym : τ.symmetrizer = 1)
    (l : List (Fin τ.rank → ℤ)) (hl : ∀ γ ∈ l, IsRoot τ γ) (v : Fin τ.rank → ℤ) :
    (l.map rootReflection).prod • v = (l.map (rootReflMat τ)).prod *ᵥ v := by
  induction l generalizing v with
  | nil => simp
  | cons γ l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, mul_smul,
      ih (fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)),
      rootReflection_smul_eq_rootReflMat hsym (hl γ List.mem_cons_self), Matrix.mulVec_mulVec]

end General

section E8

@[expose] def e8Frame (i : Fin 8) : Fin Tag.E8.rank → ℤ := e8O7Frame i

theorem e8Frame_isRoot (i : Fin 8) : IsRoot .E8 (e8Frame i) :=
  E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame.2.2.2.2.2.2.2.2.2.2.1 i

theorem e8Frame_prod :
    (List.ofFn fun i : Fin 8 => rootReflMat .E8 (e8Frame i)).prod = -1 :=
  E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame.2.2.2.2.2.2.2.2.2.2.2.2

theorem e8Frame_zero : e8Frame 0 = e8O7Theta := by
  unfold e8Frame
  rw [e8O7Frame_eq, e8O7Theta_eq]
  decide +kernel

theorem e8Frame_orth : ∀ i j : Fin 8, i ≠ j → iform (e8Frame i) (e8Frame j) = 0 := by
  unfold e8Frame
  decide +kernel

@[expose] def e8N0 (L : Type) [Field L] : ModGL .E8 L :=
  (List.ofFn fun i : Fin 8 => rootSL2 .E8 L (e8Frame i) WSL).prod

@[expose] def e8W : WeylGroup .E8 := (coxeterSystem .E8).wordProd [0, 2, 3, 4, 5, 6]

theorem e8_hsym : Tag.E8.symmetrizer = 1 := rfl

variable {L : Type} [Field L]

theorem e8N0_mem_monomial : e8N0 L ∈ monomialSubgroup .E8 L := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
  exact (rootSL2_WSL_mem_monomial_gen (L := L) (e8Frame_isRoot i)).1

theorem e8N0_weylImage :
    weylQuotientHom .E8 L ⟨e8N0 L, e8N0_mem_monomial⟩ =
      (List.ofFn fun i : Fin 8 => rootReflection (e8Frame i)).prod := by
  have hfm : ∀ i : Fin 8, rootSL2 .E8 L (e8Frame i) WSL ∈ monomialSubgroup .E8 L :=
    fun i => (rootSL2_WSL_mem_monomial_gen (L := L) (e8Frame_isRoot i)).1
  have h2 : (⟨e8N0 L, e8N0_mem_monomial⟩ : monomialSubgroup .E8 L) =
      (List.ofFn fun i : Fin 8 =>
        (⟨rootSL2 .E8 L (e8Frame i) WSL, hfm i⟩ : monomialSubgroup .E8 L)).prod := by
    apply Subtype.ext
    simp [e8N0]
  rw [h2, map_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  exact (rootSL2_WSL_mem_monomial_gen (L := L) (e8Frame_isRoot i)).choose_spec

theorem e8Frame_reflection_smul (u : Fin Tag.E8.rank → ℤ) :
    (List.ofFn fun i : Fin 8 => rootReflection (e8Frame i)).prod • u = -u := by
  have hroots : ∀ γ ∈ List.ofFn e8Frame, IsRoot .E8 γ := fun γ hγ => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hγ
    exact e8Frame_isRoot i
  have h := list_prod_rootReflection_smul e8_hsym (List.ofFn e8Frame) hroots u
  rw [List.map_ofFn, List.map_ofFn] at h
  rw [Function.comp_def] at h
  change (List.ofFn fun i : Fin 8 => rootReflection (e8Frame i)).prod • u =
    (List.ofFn fun i : Fin 8 => rootReflMat .E8 (e8Frame i)).prod *ᵥ u at h
  rw [h, e8Frame_prod, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem e8W_centralizes (L : Type) [Field L] :
    canonicalRep (coxeterSystem .E8) L e8W ∈
      Subgroup.centralizer (rootRankOneGroup .E8 L e8O7Theta : Set (ModGL .E8 L)) := by
  have hθ : IsRoot .E8 e8O7Theta := E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame.1
  have hsl : ∀ j : Fin Tag.E8.rank, Tag.E8.symmetrizer j j = 1 := by decide
  set J : Set (Fin Tag.E8.rank) := {i | i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6} with hJ
  have hJorth : ∀ i ∈ J, iform (Pi.single i 1 : Fin Tag.E8.rank → ℤ) e8O7Theta = 0 := by
    intro i hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have hwJ : e8W ∈ parabolicWeylGroup .E8 J := by
    refine wordProd_mem_parabolicWeylGroup (fun i hi => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact hi
  exact canonicalRep_mem_centralizer_rootRankOneGroup hsl hθ hJorth hwJ

theorem e8_negative_data :
    ∃ hn : canonicalRep (coxeterSystem .E8) L e8W * e8N0 L ∈ monomialSubgroup .E8 L,
      (∀ u, weylQuotientHom .E8 L ⟨_, hn⟩ • u = -(e8O7W *ᵥ u)) ∧
      ∀ B : SL2 L, (canonicalRep (coxeterSystem .E8) L e8W * e8N0 L) *
          rootSL2 .E8 L e8O7Theta B * (canonicalRep (coxeterSystem .E8) L e8W * e8N0 L)⁻¹ =
        rootSL2 .E8 L e8O7Theta (WSL * B * WSL⁻¹) := by
  have hθ : IsRoot .E8 e8O7Theta := E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame.1
  have hcm : canonicalRep (coxeterSystem .E8) L e8W ∈ monomialSubgroup .E8 L :=
    canonicalRep_mem_monomialSubgroup L e8W
  have hnm := mul_mem hcm (e8N0_mem_monomial (L := L))
  refine ⟨hnm, fun u => ?_, fun B => ?_⟩
  ·
    have himg : weylQuotientHom .E8 L ⟨_, hnm⟩ =
        e8W * (List.ofFn fun i : Fin 8 => rootReflection (e8Frame i)).prod := by
      have h1 : (⟨_, hnm⟩ : monomialSubgroup .E8 L) =
          ⟨canonicalRep (coxeterSystem .E8) L e8W, hcm⟩ * ⟨e8N0 L, e8N0_mem_monomial⟩ := rfl
      rw [h1, map_mul, e8N0_weylImage]
      congr 1
      exact weylQuotientHom_eq (mapsRootLines_canonicalRep e8W)
    have hw : e8W • u = e8O7W *ᵥ u := wordProd_smul_eq_wordMat_mulVec .E8 [0, 2, 3, 4, 5, 6] u
    rw [himg, mul_smul, e8Frame_reflection_smul, smul_neg, hw]
  ·
    set c := canonicalRep (coxeterSystem .E8) L e8W with hc
    set ρ := rootSL2 .E8 L e8O7Theta with hρ
    have hsl : ∀ j : Fin Tag.E8.rank, Tag.E8.symmetrizer j j = 1 := by decide
    have hcC : c ∈ Subgroup.centralizer (rootRankOneGroup .E8 L e8O7Theta : Set (ModGL .E8 L)) :=
      e8W_centralizes L
    set R : ModGL .E8 L :=
      (List.ofFn fun i : Fin 7 => rootSL2 .E8 L (e8Frame i.succ) WSL).prod with hR
    have hn0eq : e8N0 L = ρ WSL * R := by
      unfold e8N0
      rw [List.ofFn_succ, List.prod_cons, e8Frame_zero]
    have hRC : R ∈ Subgroup.centralizer (rootRankOneGroup .E8 L e8O7Theta : Set (ModGL .E8 L)) := by
      refine Subgroup.list_prod_mem _ fun g hg => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      have h0 : iform (e8Frame i.succ) e8O7Theta = 0 := by
        rw [← e8Frame_zero]
        exact e8Frame_orth _ _ (Fin.succ_ne_zero i)
      obtain ⟨hp, hm⟩ := not_isRoot_add_sub_of_iform_eq_zero hsl (e8Frame_isRoot i.succ) hθ h0
      have hcomm := exceptional_Lang_strongly_orthogonal_root_rank_one_commutation .E8 L
        (e8Frame_isRoot i.succ) hθ h0 hp hm
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (hcomm _ ⟨WSL, rfl⟩ q hq).symm
    have hx : ρ B ∈ rootRankOneGroup .E8 L e8O7Theta := ⟨B, rfl⟩
    have hy : ρ (WSL * B * WSL⁻¹) ∈ rootRankOneGroup .E8 L e8O7Theta := ⟨_, rfl⟩
    have hRx : R * ρ B * R⁻¹ = ρ B := by
      have h := Subgroup.mem_centralizer_iff.1 hRC (ρ B) hx
      rw [← h, mul_inv_cancel_right]
    have hcy : c * ρ (WSL * B * WSL⁻¹) * c⁻¹ = ρ (WSL * B * WSL⁻¹) := by
      have h := Subgroup.mem_centralizer_iff.1 hcC (ρ (WSL * B * WSL⁻¹)) hy
      rw [← h, mul_inv_cancel_right]
    calc c * e8N0 L * ρ B * (c * e8N0 L)⁻¹
        = c * (ρ WSL * (R * ρ B * R⁻¹) * (ρ WSL)⁻¹) * c⁻¹ := by rw [hn0eq]; group
      _ = c * (ρ WSL * ρ B * (ρ WSL)⁻¹) * c⁻¹ := by rw [hRx]
      _ = c * ρ (WSL * B * WSL⁻¹) * c⁻¹ := by rw [← map_mul, ← map_inv, ← map_mul]
      _ = ρ (WSL * B * WSL⁻¹) := hcy

end E8

end CFSG.RankThree.PartOne.KE
