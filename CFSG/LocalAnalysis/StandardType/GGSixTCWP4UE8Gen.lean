module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrame
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UEig
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UGram
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UExc
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.PartOne.KE
open Polynomial
open scoped Matrix

section Matrix

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

noncomputable def rhoMatrixOfSetup
    (S : LangSetup .E8 L p₀) :
    Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  LinearMap.toMatrix' (rhoLinMap S)

theorem rhoMatrixOfSetup_mulVec
    (S : LangSetup .E8 L p₀) (x : Fin Tag.E8.rank → ℤ) :
    rhoMatrixOfSetup S *ᵥ x = S.ρ x := by
  rw [rhoMatrixOfSetup, LinearMap.toMatrix'_mulVec]
  rfl

theorem rhoMatrixOfSetup_apply
    (S : LangSetup .E8 L p₀) (i j : Fin Tag.E8.rank) :
    rhoMatrixOfSetup S i j = S.ρ (Pi.single j 1) i := by
  rw [rhoMatrixOfSetup, LinearMap.toMatrix'_apply]
  rfl

theorem exists_pow_rhoLin_eq_one
    (S : LangSetup .E8 L p₀) :
    ∃ N : ℕ, 0 < N ∧ rhoLinMap S ^ N = 1 := by
  classical
  let RT := {γ : Fin Tag.E8.rank → ℤ // IsRoot .E8 γ}
  have hfin : Finite RT := by
    have : Set.Finite {γ : Fin Tag.E8.rank → ℤ | IsRoot .E8 γ} :=
      (rootFinset .E8).finite_toSet.subset fun γ hγ => mem_rootFinset.2 hγ
    exact this.to_subtype
  let σ : Equiv.Perm RT :=
    S.ρ.subtypePerm (p := fun γ => IsRoot .E8 γ) fun γ => S.frob.isRoot_iff γ
  refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
  have hσ : σ ^ orderOf σ = 1 := pow_orderOf_eq_one σ
  have hiter : ∀ (n : ℕ) (γ : RT), ((σ ^ n) γ).1 = S.ρ^[n] γ.1 := by
    intro n
    induction n with
    | zero => intro γ; rfl
    | succ n ih =>
      intro γ
      rw [pow_succ, Equiv.Perm.mul_apply, Function.iterate_succ_apply, ih (σ γ)]
      rfl
  refine (Pi.basisFun ℤ (Fin Tag.E8.rank)).ext fun i => ?_
  have h1 := hiter (orderOf σ) ⟨Pi.single i 1, isRoot_single .E8 i⟩
  rw [hσ] at h1
  rw [Pi.basisFun_apply, Module.End.one_apply, Module.End.pow_apply]
  exact h1.symm

theorem rhoMatrixOfSetup_pow_eq_one
    (S : LangSetup .E8 L p₀) :
    ∃ N : ℕ, 0 < N ∧ rhoMatrixOfSetup S ^ N = 1 := by
  obtain ⟨N, hN, h⟩ := exists_pow_rhoLin_eq_one S
  refine ⟨N, hN, ?_⟩
  have := congrArg (LinearMap.toMatrixAlgEquiv' (R := ℤ) (n := Fin Tag.E8.rank)) h
  rw [map_pow, map_one] at this
  exact this

end Matrix

section Group

theorem le_finrank_eigenspace_of_subgroup
    {K : Type} [Field K] [Finite K] [CharP K 2] {p₀ : ℕ}
    (S : LangSetup .E8 (AlgebraicClosure K) p₀) {f p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hq : S.D.q = 2 ^ f) {n : ℕ}
    {B₁ : Subgroup (ModGL .E8 (AlgebraicClosure K))} (hB₁T : B₁ ≤ S.D.torus)
    (hB₁el : CFSG.Open.IsElemAbelian p B₁) (hcard : p ^ n ≤ Nat.card B₁) :
    n ≤ Module.finrank (ZMod p)
      (Module.End.eigenspace
        (Matrix.mulVecLin (((rhoMatrixOfSetup S).map (Int.castRingHom (ZMod p)))ᵀ))
          ((2 : ZMod p) ^ f)) := by
  classical
  have : NeZero (p : K) := ⟨fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1
    ((CharP.cast_eq_zero_iff K 2 p).1 h)).symm⟩
  have : NeZero p := ⟨hp.out.ne_zero⟩
  set L := AlgebraicClosure K with hL
  have hcyc : IsCyclic (rootsOfUnity p L) := inferInstance
  have hcard' : Nat.card (rootsOfUnity p L) = p := HasEnoughRootsOfUnity.natCard_rootsOfUnity L p
  let eμ : rootsOfUnity p L ≃* Multiplicative (ZMod p) :=
    (zmodCyclicMulEquiv hcyc).symm.trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard').toAddEquiv)
  have hpar : ∀ d : ↥B₁, ∃ c : Fin Tag.E8.rank → Lˣ,
      (d : ModGL .E8 L) = rootDiagUnit .E8 c ∧ ∀ j, c j ^ p = 1 := fun d =>
    exists_param_of_torus (hB₁T d.2).1 (hB₁el.2 _ d.2)
  choose c hc hcp using hpar
  have hmem : ∀ d j, c d j ∈ rootsOfUnity p L := fun d j => (mem_rootsOfUnity p _).2 (hcp d j)
  let x : ↥B₁ → Fin Tag.E8.rank → rootsOfUnity p L := fun d j => ⟨c d j, hmem d j⟩
  let ex : ↥B₁ → (Fin Tag.E8.rank → ZMod p) := fun d j => Multiplicative.toAdd (eμ (x d j))
  let Rp : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod p) :=
    (rhoMatrixOfSetup S).map (Int.castRingHom (ZMod p))
  have hkey : ∀ d i, ∑ j, Rp j i * ex d j = (2 : ZMod p) ^ f * ex d i := by
    intro d i
    have haT : rootDiagUnit .E8 (c d) ∈ S.D.torus := (hc d) ▸ hB₁T d.2
    have h1 := S.frob.rootChar_eq (c d) haT (Pi.single i 1) (isRoot_single .E8 i)
    rw [rootChar_single, hq] at h1
    have h2 : rootChar (c d) (S.ρ (Pi.single i 1)) =
        ((∏ j, x d j ^ (rhoMatrixOfSetup S j i) : rootsOfUnity p L) : Lˣ) := by
      rw [rootChar, SubmonoidClass.coe_finsetProd]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Subgroup.coe_zpow, rhoMatrixOfSetup_apply]
    have h3 : (x d i ^ (2 ^ f) : rootsOfUnity p L) = ∏ j, x d j ^ (rhoMatrixOfSetup S j i) := by
      apply Subtype.ext
      rw [← h2, h1]
      rfl
    have h4 := congrArg (fun y => Multiplicative.toAdd (eμ y)) h3
    simp only [map_pow, map_prod, map_zpow, toAdd_pow, toAdd_prod, toAdd_zpow, nsmul_eq_mul,
      zsmul_eq_mul] at h4
    simpa [Rp, ex, Matrix.map_apply] using h4.symm
  have hmemE : ∀ d, ex d ∈ Module.End.eigenspace (Matrix.mulVecLin Rpᵀ) ((2 : ZMod p) ^ f) := by
    intro d
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
    exact hkey d i
  have hinj : Function.Injective ex := by
    intro d d' h
    have hx : ∀ j, x d j = x d' j := fun j =>
      eμ.injective (Multiplicative.toAdd.injective (congrFun h j))
    have hcc : c d = c d' := funext fun j => congrArg Subtype.val (hx j)
    apply Subtype.ext
    rw [hc d, hc d', hcc]
  let E := Module.End.eigenspace (Matrix.mulVecLin Rpᵀ) ((2 : ZMod p) ^ f)
  have hle : Nat.card B₁ ≤ Nat.card E :=
    Nat.card_le_card_of_injective (fun d => (⟨ex d, hmemE d⟩ : E))
      (fun d d' h => hinj (congrArg Subtype.val h))
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := E), Nat.card_zmod] at hle
  exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 (hcard.trans hle)

end Group

theorem iform_self_eq_two_of_mem_e8 : ∀ x ∈ rootFinset .E8, iform x x = 2 := by
  decide +kernel

section Contradiction

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem iform_zero_right_of_zero_left
    (x : Fin Tag.E8.rank → ℤ) :
    iform x (0 : Fin Tag.E8.rank → ℤ) = 0 := by
  have := iform_smul_right (0 : ℤ) x x
  simpa using this

theorem iform_ne_zero_of_cyclotomic
    (S : LangSetup .E8 L p₀) {c : ℕ} (hc : c = 3 ∨ c = 6)
    (hR : aeval (rhoMatrixOfSetup S) (cyclotomic c ℤ) = 0) {α : Fin Tag.E8.rank → ℤ}
    (hα : IsRoot .E8 α) : iform α (S.ρ α) ≠ 0 := by
  intro h0
  have hnα : iform α α = 2 := iform_self_eq_two_of_mem_e8 α (mem_rootFinset.2 hα)
  have hu : iform (S.ρ α) (S.ρ α) = 2 := by rw [S.frob.iform_eq]; exact hnα
  have hw : iform (S.ρ (S.ρ α)) (S.ρ (S.ρ α)) = 2 := by rw [S.frob.iform_eq]; exact hu
  have hR2 : (rhoMatrixOfSetup S ^ 2) *ᵥ α = S.ρ (S.ρ α) := by
    rw [pow_two, ← Matrix.mulVec_mulVec, rhoMatrixOfSetup_mulVec, rhoMatrixOfSetup_mulVec]
  obtain ⟨ε, hε, hrel⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      S.ρ (S.ρ α) + ε • S.ρ α + α = 0 := by
    rcases hc with rfl | rfl
    · have h : (rhoMatrixOfSetup S ^ 2 + rhoMatrixOfSetup S + 1) *ᵥ α = 0 := by
        have h1 : aeval (rhoMatrixOfSetup S) (cyclotomic 3 ℤ) =
            rhoMatrixOfSetup S ^ 2 + rhoMatrixOfSetup S + 1 := by
          simp [cyclotomic_three]
        rw [← h1, hR]
        exact Matrix.zero_mulVec _
      rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hR2,
        rhoMatrixOfSetup_mulVec] at h
      exact ⟨1, Or.inl rfl, by simpa using h⟩
    · have h : (rhoMatrixOfSetup S ^ 2 - rhoMatrixOfSetup S + 1) *ᵥ α = 0 := by
        have h1 : aeval (rhoMatrixOfSetup S) (cyclotomic 6 ℤ) =
            rhoMatrixOfSetup S ^ 2 - rhoMatrixOfSetup S + 1 := by
          simp [cyclotomic_six]
        rw [← h1, hR]
        exact Matrix.zero_mulVec _
      rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hR2,
        rhoMatrixOfSetup_mulVec] at h
      refine ⟨-1, Or.inr rfl, ?_⟩
      rw [neg_smul, one_smul, ← sub_eq_add_neg]
      exact h
  set u := S.ρ α with hu_def
  set w := S.ρ u with hw_def
  have hαw : iform α w = -2 := by
    have h := congrArg (fun v => iform α v) hrel
    simp only [iform_add_right, iform_smul_right, iform_zero_right_of_zero_left, h0, hnα] at h
    omega
  have hwα : iform (w + α) (w + α) = 0 := by
    simp only [iform_add_left, iform_add_right]
    rw [iform_comm w α, hαw, hw, hnα]
    ring
  have hw0 : w + α = 0 := vec_eq_zero_of_iform_self_eq_zero hwα
  have hεu : ε • u = 0 := by
    have : ε • u = (w + ε • u + α) - (w + α) := by abel
    rw [this, hrel, hw0, sub_zero]
  have hu0 : u = 0 := by
    rcases hε with rfl | rfl <;> simpa using hεu
  have h00 : iform u u = 0 := by
    rw [hu0]
    have := iform_smul_left (0 : ℤ) (0 : Fin Tag.E8.rank → ℤ) (0 : Fin Tag.E8.rank → ℤ)
    simpa using this
  omega

end Contradiction

section Leaf

open CFSG.Open CFSG.Blueprint

theorem seven_le_of_three_dvd_sub_one {p : ℕ} (hp : p.Prime) (h : 3 ∣ p - 1) : 7 ≤ p := by
  by_contra h7
  push Not at h7
  have h2 := hp.two_le
  interval_cases p <;> simp_all (config := {decide := true})

theorem upper_E8_gen_of_inputs
    (hR : LangFamilyCompFieldSL)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .E8 n f).K →* X} (h : GGTCHyp .E8 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .E8 f) (hc1 : orderOf ((2 : ZMod p) ^ f) ≠ 1)
    (hc2 : orderOf ((2 : ZMod p) ^ f) ≠ 2) (hc4 : orderOf ((2 : ZMod p) ^ f) ≠ 4) :
    Nat.card B ≤ p ^ 3 := by
  have hp := h.prime
  have hp2 := h.ne_two
  by_cases hc36 : orderOf ((2 : ZMod p) ^ f) = 3 ∨ orderOf ((2 : ZMod p) ^ f) = 6
  swap
  · push Not at hc36
    exact (upper_E8_gen_ne h hc1 hc2 hc36.1 hc4 hc36.2).trans
      (Nat.pow_le_pow_right hp.pos (by norm_num))
  by_contra hlt
  push Not at hlt
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : (2 : ZMod p) ^ f ≠ 0 := by
    refine pow_ne_zero _ fun h2 => hp2 ?_
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
  have hdvd : orderOf ((2 : ZMod p) ^ f) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hq0
  have hp7 : 7 ≤ p := by
    refine seven_le_of_three_dvd_sub_one hp ?_
    rcases hc36 with hc | hc
    · rwa [hc] at hdvd
    · rw [hc] at hdvd
      exact (dvd_trans (by norm_num : 3 ∣ 6) hdvd)
  have hpg : IsPGroup p B := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext ((Subgroup.coe_pow _ g p).trans (h.b_elem.2 g g.2))⟩
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hk4 : 4 ≤ k := by
    by_contra hk3
    push Not at hk3
    have := Nat.pow_le_pow_right hp.pos (by omega : k ≤ 3)
    omega
  have hcard4 : p ^ 4 ≤ Nat.card B := by
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos hk4
  have hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E8 (2 ^ f) :=
    ((LieModel.chevalleyExceptional_iff (by decide)).1 h.model).2.2
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hTor : UToralAt .E8 p (Nat.card B) :=
    utoralAt_of_nonTorsion hp hp2 (fun _ => by omega) (fun _ => by omega) hBpos
  obtain ⟨t', m, f', hflt, hm, -⟩ := hF
  obtain ⟨K, instF, instFin, instChar, S, hq, ⟨fr⟩⟩ :=
    exists_uframe (Or.inr (Or.inr (Or.inr rfl))) hp hp2 hmod h.b_norm h.inner_E8 h.b_faithful
      h.b_elem h.d_le h.d_card
  obtain ⟨S₁, hq₁, fr₁, hBT⟩ :=
    exists_torus_uframe (Or.inr (Or.inr (Or.inr rfl))) hp hp2 S fr
      h.b_elem hTor
  obtain ⟨Ψ, hΨ, horth, hcard, -⟩ := uframe_conclude (uFieldInput_of_SL hR (Or.inr (Or.inr rfl)))
    hp hp2 S₁ (hq₁.trans hq) fr₁ hBT h.b_elem h.d_le h.d_card
    (h.j_comp.1.trans inf_le_left) (Assembly.isComponentOf_iff_open.1 h.j_comp) h.j_cent
    ⟨t', m, f', hflt, hm⟩
  have hBel₁ := fr₁.isElemAbelian_BLang h.b_elem
  have hcard₁ : p ^ 4 ≤ Nat.card fr₁.BLang := by
    rw [fr₁.card_BLang]
    exact hcard4
  have hdim := le_finrank_eigenspace_of_subgroup S₁ hp2 (hq₁.trans hq) hBT hBel₁ hcard₁
  obtain ⟨N, hN, hRN⟩ := rhoMatrixOfSetup_pow_eq_one S₁
  have hι : Fintype.card (Fin Tag.E8.rank) = 8 := by
    rw [Fintype.card_fin]
    rfl
  have hcyc := cyclotomic_aeval_eq_zero hp7 hc36 rfl hι (rhoMatrixOfSetup S₁) hN hRN hdim
  have hr : 2 ≤ Module.finrank ℤ (Submodule.span ℤ Ψ) := by
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hcard4.trans hcard)
    omega
  obtain ⟨α, hα⟩ : Ψ.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Submodule.span_empty, finrank_bot] at hr
    omega
  exact iform_ne_zero_of_cyclotomic S₁ hc36 hcyc (hΨ.isRoot α hα)
    (horth α hα (S₁.ρ α) ⟨α, hα, rfl⟩).1

end Leaf

end CFSG.StandardType.TableCRes
