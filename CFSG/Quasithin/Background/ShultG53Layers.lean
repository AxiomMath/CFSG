module

public import CFSG.Quasithin.Background.ShultG53Chain
public import CFSG.Quasithin.Background.ShultG53Data

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.Quasithin.H13.A6 CFSG.Quasithin.RonanG51 Equiv

@[expose] def x0 : Fin 2 → V4
  | 0 => ![1, 0, 1, 0]
  | 1 => ![1, 0, 0, 0]

@[expose] def U0gen (k : Fin 2) : Fn := fun w => if w = 0 ∨ w = x0 k then 0 else 1

@[expose] def U2gen : Fin 2 → Fn
  | 0 => fun w => if w = 0 ∨ w = ![1, 0, 0, 0] ∨ w = ![0, 0, 1, 0] ∨ w = ![1, 0, 1, 0]
      then 0 else 1
  | 1 => fun w => if w = 0 ∨ w = ![1, 0, 0, 0] ∨ w = ![0, 0, 1, 1] ∨ w = ![1, 0, 1, 1]
      then 0 else 1

@[expose] def FixList (k : Fin 2) (u : Fn) (L : List (Perm (Fin 6))) : Prop :=
  ∀ σ ∈ L, Perm.sign σ = 1 ∧ ∀ w : V4, u (Matrix.mulVec (Rm k σ⁻¹) w) = u w

instance (k : Fin 2) (u : Fn) (L : List (Perm (Fin 6))) : Decidable (FixList k u L) :=
  inferInstanceAs (Decidable (∀ σ ∈ L, Perm.sign σ = 1 ∧
    ∀ w : V4, u (Matrix.mulVec (Rm k σ⁻¹) w) = u w))

theorem fixed_of_list {k j : Fin 2} {u : Fn} {L : List (Perm (Fin 6))} (hL : FixList k u L)
    {m : V4} (hm : ∀ h : ↥(alternatingGroup (Fin 6)), permRep (Mk k) h u = u → ρk j h m = m) :
    ∀ σ ∈ L, Matrix.mulVec (Rm j σ) m = m := by
  intro σ hσ
  obtain ⟨hs, hu⟩ := hL σ hσ
  have hA : σ ∈ alternatingGroup (Fin 6) := Perm.mem_alternatingGroup.mpr hs
  have h1 : permRep (Mk k) ⟨σ, hA⟩ u = u := by
    funext w
    show u (ρk k (⟨σ, hA⟩ : ↥(alternatingGroup (Fin 6)))⁻¹ w) = u w
    rw [ρk_apply]
    exact hu w
  have := hm ⟨σ, hA⟩ h1
  rwa [ρk_apply] at this

theorem le_closure_of_indep (k : Fin 2) {d : ℕ} {N : AddSubgroup Fn}
    (hN : InvSub (permAct (Mk k)) N) {u : Fn} (hu : u ∈ N) (hcard : Nat.card N ≤ 2 ^ d)
    (g : Fin d → Perm (Fin 6)) (hg : ∀ i, Perm.sign (g i) = 1) (y : Fin d → V4)
    (Minv : Matrix (Fin d) (Fin d) (ZMod 2))
    (hM : (Matrix.of fun i j => u (Matrix.mulVec (Rm k (g i)⁻¹) (y j))) * Minv = 1) :
    ∀ n ∈ N, n ∈ AddSubgroup.closure
      (Set.range fun h : ↥(alternatingGroup (Fin 6)) => permRep (Mk k) h u) := by
  let S := AddSubgroup.closure
    (Set.range fun h : ↥(alternatingGroup (Fin 6)) => permRep (Mk k) h u)
  have hSN : S ≤ N := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨h, rfl⟩
    exact hN h u hu
  let ge : Fin d → ↥(alternatingGroup (Fin 6)) :=
    fun i => ⟨g i, Perm.mem_alternatingGroup.mpr (hg i)⟩
  let φ : (Fin d → ZMod 2) →+ Fn :=
    { toFun := fun c => ∑ i, c i • permAct (Mk k) (ge i) u
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib] }
  have hφS : ∀ c, φ c ∈ S := by
    intro c
    show ∑ i, c i • permAct (Mk k) (ge i) u ∈ S
    refine AddSubgroup.sum_mem S fun i _ => ?_
    have h1 : permAct (Mk k) (ge i) u ∈ S := AddSubgroup.subset_closure ⟨ge i, rfl⟩
    exact (AddSubgroup.toZModSubmodule 2 S).smul_mem (c i) h1
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : ∀ j, ∑ i, c i * u (Matrix.mulVec (Rm k (g i)⁻¹) (y j)) = 0 := by
      intro j
      have := congrFun (show ∑ i, c i • permAct (Mk k) (ge i) u = 0 from hc) (y j)
      simpa [Finset.sum_apply, permAct_apply, ρk_apply, ge] using this
    have h2 : Matrix.vecMul c (Matrix.of fun i j =>
        u (Matrix.mulVec (Rm k (g i)⁻¹) (y j))) = 0 := by
      funext j
      simpa [Matrix.vecMul, dotProduct] using h1 j
    calc c = Matrix.vecMul c 1 := (Matrix.vecMul_one c).symm
      _ = Matrix.vecMul c ((Matrix.of fun i j => u (Matrix.mulVec (Rm k (g i)⁻¹) (y j))) *
          Minv) := by rw [hM]
      _ = Matrix.vecMul (Matrix.vecMul c (Matrix.of fun i j =>
          u (Matrix.mulVec (Rm k (g i)⁻¹) (y j)))) Minv := (Matrix.vecMul_vecMul _ _ _).symm
      _ = 0 := by rw [h2]; simp
  have hle : 2 ^ d ≤ Nat.card S := by
    have h1 : Nat.card (Fin d → ZMod 2) ≤ Nat.card S :=
      Nat.card_le_card_of_injective (fun c => (⟨φ c, hφS c⟩ : S)) (fun a b hab =>
        hinj (congrArg Subtype.val hab))
    simpa [Nat.card_fun, Nat.card_zmod] using h1
  have hSeq : S = N := AddSubgroup.eq_of_le_of_card_ge hSN (hcard.trans hle)
  intro n hn
  rw [← hSeq] at hn
  exact hn

theorem no_trivial_quot (k : Fin 2) {N : AddSubgroup Fn} (hN : InvSub (permAct (Mk k)) N)
    {u : Fn} (hu : u ∈ N)
    (hgen : ∀ n ∈ N, n ∈ AddSubgroup.closure
      (Set.range fun h : ↥(alternatingGroup (Fin 6)) => permRep (Mk k) h u))
    {r : ℕ} (hr : Odd r) (ge : Fin r → ↥(alternatingGroup (Fin 6)))
    (hsum : ∑ i, permAct (Mk k) (ge i) u = 0) :
    ∀ ψ : ↥N →+ D 0, Function.Surjective ψ →
      ¬ ∀ (h : ↥(alternatingGroup (Fin 6))) (n : ↥N),
        ψ ⟨permRep (Mk k) h n, hN h n n.2⟩ = a6BinaryRep 0 h (ψ n) := by
  intro ψ hs he
  have hc : ∀ i, ψ ⟨permAct (Mk k) (ge i) u, hN _ _ hu⟩ = ψ ⟨u, hu⟩ := by
    intro i
    have h1 := he (ge i) ⟨u, hu⟩
    rw [a6_trivial] at h1
    exact h1
  have hsumN : ∑ i, (⟨permAct (Mk k) (ge i) u, hN _ _ hu⟩ : ↥N) = 0 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    exact hsum
  have h2 : ∑ i, ψ ⟨permAct (Mk k) (ge i) u, hN _ _ hu⟩ = 0 := by
    rw [← map_sum, hsumN, map_zero]
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h2
  have hdbl : ∀ c : D 0, c + c = 0 := by decide
  have hodd : ∀ (t : ℕ) (c : D 0), (2 * t + 1) • c = c := by
    intro t c
    induction t with
    | zero => simp
    | succ t ih =>
      have : 2 * (t + 1) + 1 = (2 * t + 1) + 2 := by ring
      rw [this, add_nsmul, ih, two_nsmul, hdbl, add_zero]
  have h3 : ψ ⟨u, hu⟩ = 0 := by
    obtain ⟨t, rfl⟩ := hr
    rw [hodd] at h2
    exact h2
  have hzero : ψ = 0 := by
    refine hom_eq_of_cyclic (permRep (Mk k)) (fun g m => a6BinaryRep 0 g m) hN hu hgen ψ 0 he
      (fun g n => by rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, map_zero]) ?_
    rw [AddMonoidHom.zero_apply]
    exact h3
  obtain ⟨hnt, -⟩ := a6_irred 0
  haveI := hnt
  obtain ⟨d, hd⟩ := exists_ne (0 : D 0)
  obtain ⟨n, rfl⟩ := hs d
  exact hd (by rw [hzero]; rfl)

@[expose] def StabSet (k : Fin 2) (u : Fn) : Set ↥(alternatingGroup (Fin 6)) :=
  {h | permRep (Mk k) h u = u}

theorem hfixA_of {k j : Fin 2} {u : Fn} {L : List (Perm (Fin 6))} (hL : FixList k u L)
    (m₀ : V4) (hA : ∀ m : V4, m ≠ 0 → (∀ σ ∈ L, Matrix.mulVec (Rm j σ) m = m) → m = m₀) :
    ∀ m : V4, m ≠ 0 → (∀ h ∈ StabSet k u, ρk j h m = m) → m = m₀ :=
  fun m hm hfix => hA m hm (fixed_of_list hL (fun h hh => hfix h hh))

theorem hfixB_of {k : Fin 2} {u : Fn} {L : List (Perm (Fin 6))} (hL : FixList k u L)
    (i₀ : Fin 4)
    (hB1 : i₀ ≠ 1 → ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ L, Matrix.mulVec (Rm 0 σ) m = m)
    (hB2 : i₀ ≠ 2 → ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ L, Matrix.mulVec (Rm 1 σ) m = m) :
    ∀ i : Fin 4, i ≠ 3 → i ≠ i₀ → i ≠ 0 → ∀ m : D i, m ≠ 0 →
      ¬ ∀ h ∈ StabSet k u, a6BinaryRep i h m = m := by
  intro i h3 hi0 h0 m hm hfix
  match i, h3, hi0, h0, m, hm, hfix with
  | 0, _, _, h0, _, _, _ => exact absurd rfl h0
  | 3, h3, _, _, _, _, _ => exact absurd rfl h3
  | 1, _, hi0, _, m, hm, hfix =>
    exact hB1 (Ne.symm hi0) m hm (fixed_of_list hL (j := 0) (fun h hh => hfix h hh))
  | 2, _, hi0, _, m, hm, hfix =>
    exact hB2 (Ne.symm hi0) m hm (fixed_of_list hL (j := 1) (fun h hh => hfix h hh))

theorem hfixA_triv : ∀ m : D 0, m ≠ 0 → m = fun _ => 1 := by decide +kernel

theorem U0gen_aux : ∀ k : Fin 2, U0gen k 0 = 0 ∧ ∑ w : V4, U0gen k w = 0 := by
  decide +kernel

theorem U2gen_aux : ∀ k : Fin 2, (U2gen k 0 = 0 ∧ ∑ w : V4, U2gen k w = 0) ∧
    (∑ w : V4, U2gen k w • w = 0) ∧ (∑ w : V4, U2gen k w * Qf w = 0) := by
  decide +kernel

theorem U0gen_mem (k : Fin 2) : U0gen k ∈ Nk k 0 :=
  (mem_permCore k _).mpr (U0gen_aux k)

theorem U1gen_mem (k : Fin 2) : U1gen ∈ Nk k 1 := by
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := U1gen_aux
  exact AddSubgroup.mem_inf.mpr ⟨(mem_permCore k _).mpr ⟨h1, h2⟩, AddMonoidHom.mem_ker.mpr h3⟩

theorem U2gen_mem (k : Fin 2) : U2gen k ∈ Nk k 2 := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := U2gen_aux k
  exact AddSubgroup.mem_inf.mpr ⟨AddSubgroup.mem_inf.mpr
    ⟨(mem_permCore k _).mpr ⟨h1, h2⟩, AddMonoidHom.mem_ker.mpr h3⟩, AddMonoidHom.mem_ker.mpr h4⟩

theorem Qfun_mem_N3 (k : Fin 2) : Qfun ∈ Nk k 3 := ⟨(1, 0), by simp [Q3, Cf_zero]⟩

theorem hsum_of (k : Fin 2) {r : ℕ} (σ : Fin r → Perm (Fin 6)) (hs : ∀ i, Perm.sign (σ i) = 1)
    (u : Fn) (h : ∀ w : V4, ∑ i, u (Matrix.mulVec (Rm k (σ i)⁻¹) w) = 0) :
    ∑ i, permAct (Mk k) ⟨σ i, Perm.mem_alternatingGroup.mpr (hs i)⟩ u = 0 := by
  funext w
  rw [Finset.sum_apply]
  simp only [permAct_apply, ρk_apply]
  exact h w

theorem N0_inv (k : Fin 2) : InvSub (permAct (Mk k)) (Nk k 0) := permCore_inv k

theorem hS_0_0 : ∀ i, Perm.sign (gP_0_0 i) = 1 := by decide +kernel

theorem hM_0_0 : (Matrix.of fun i j => (U0gen 0) (Matrix.mulVec (Rm 0 (gP_0_0 i)⁻¹) (yP_0_0 j))) *
    MP_0_0 = 1 := by decide +kernel

theorem hL_0_0 : FixList 0 (U0gen 0) LS_0_0 := by decide +kernel

theorem hA_0_0 : ∀ m : V4, m ≠ 0 → (∀ σ ∈ LS_0_0, Matrix.mulVec (Rm 0 σ) m = m) →
    m = x0 0 := by decide +kernel

theorem hB2_0_0 : ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ LS_0_0, Matrix.mulVec (Rm 1 σ) m = m := by
  decide +kernel

theorem hRSs_0_0 : ∀ i, Perm.sign (RS0_0 i) = 1 := by decide +kernel

theorem hRSsum_0_0 : ∀ w : V4,
    ∑ i : Fin 15, (U0gen 0) (Matrix.mulVec (Rm 0 (RS0_0 i)⁻¹) w) = 0 := by
  decide +kernel

theorem layer0_0 : IsTop (permAct (Mk 0)) (Nk 0 0) (Nk 0 1) := by
  have hlt : Nk 0 1 < Nk 0 0 := lt_of_le_of_ne (N1_le_N0 0) (fun h => by
    have := card_N0 0
    rw [← h, card_N1] at this
    omega)
  have hgen := le_closure_of_indep 0 (N0_inv 0) (U0gen_mem 0) (card_N0 0).le gP_0_0 hS_0_0
    yP_0_0 MP_0_0 hM_0_0
  exact isTop_of_cyclic (permRep (Mk 0)) (N0_inv 0) (N1_inv 0) hlt 1 (x0 0)
    (by rw [card_N0, card_N1, card_D]; decide) (U0gen_mem 0) hgen
    (StabSet 0 (U0gen 0)) (fun h hh => hh) (by rw [card_N0]; norm_num)
    (hfixA_of hL_0_0 (x0 0) hA_0_0)
    (hfixB_of hL_0_0 1 (fun h => absurd rfl h) (fun _ => hB2_0_0))
    (fun _ ψ hs => no_trivial_quot 0 (N0_inv 0) (U0gen_mem 0) hgen (r := 15) ⟨7, rfl⟩
      (fun i => ⟨RS0_0 i, Perm.mem_alternatingGroup.mpr (hRSs_0_0 i)⟩)
      (hsum_of 0 RS0_0 hRSs_0_0 (U0gen 0) hRSsum_0_0) ψ hs)

theorem hS_0_1 : ∀ i, Perm.sign (gP_0_1 i) = 1 := by decide +kernel

theorem hM_0_1 : (Matrix.of fun i j => (U0gen 1) (Matrix.mulVec (Rm 1 (gP_0_1 i)⁻¹) (yP_0_1 j))) *
    MP_0_1 = 1 := by decide +kernel

theorem hL_0_1 : FixList 1 (U0gen 1) LS_0_1 := by decide +kernel

theorem hA_0_1 : ∀ m : V4, m ≠ 0 → (∀ σ ∈ LS_0_1, Matrix.mulVec (Rm 1 σ) m = m) →
    m = x0 1 := by decide +kernel

theorem hB1_0_1 : ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ LS_0_1, Matrix.mulVec (Rm 0 σ) m = m := by
  decide +kernel

theorem hRSs_0_1 : ∀ i, Perm.sign (RS0_1 i) = 1 := by decide +kernel

theorem hRSsum_0_1 : ∀ w : V4,
    ∑ i : Fin 15, (U0gen 1) (Matrix.mulVec (Rm 1 (RS0_1 i)⁻¹) w) = 0 := by
  decide +kernel

theorem layer0_1 : IsTop (permAct (Mk 1)) (Nk 1 0) (Nk 1 1) := by
  have hlt : Nk 1 1 < Nk 1 0 := lt_of_le_of_ne (N1_le_N0 1) (fun h => by
    have := card_N0 1
    rw [← h, card_N1] at this
    omega)
  have hgen := le_closure_of_indep 1 (N0_inv 1) (U0gen_mem 1) (card_N0 1).le gP_0_1 hS_0_1
    yP_0_1 MP_0_1 hM_0_1
  exact isTop_of_cyclic (permRep (Mk 1)) (N0_inv 1) (N1_inv 1) hlt 2 (x0 1)
    (by rw [card_N0, card_N1, card_D]; decide) (U0gen_mem 1) hgen
    (StabSet 1 (U0gen 1)) (fun h hh => hh) (by rw [card_N0]; norm_num)
    (hfixA_of hL_0_1 (x0 1) hA_0_1)
    (hfixB_of hL_0_1 2 (fun _ => hB1_0_1) (fun h => absurd rfl h))
    (fun _ ψ hs => no_trivial_quot 1 (N0_inv 1) (U0gen_mem 1) hgen (r := 15) ⟨7, rfl⟩
      (fun i => ⟨RS0_1 i, Perm.mem_alternatingGroup.mpr (hRSs_0_1 i)⟩)
      (hsum_of 1 RS0_1 hRSs_0_1 (U0gen 1) hRSsum_0_1) ψ hs)

theorem hS_1_0 : ∀ i, Perm.sign (gP_1_0 i) = 1 := by decide +kernel

theorem hM_1_0 : (Matrix.of fun i j => (U1gen) (Matrix.mulVec (Rm 0 (gP_1_0 i)⁻¹) (yP_1_0 j))) *
    MP_1_0 = 1 := by decide +kernel

theorem hL_1_0 : FixList 0 (U1gen) LS_1_0 := by decide +kernel

theorem hB1_1_0 : ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ LS_1_0, Matrix.mulVec (Rm 0 σ) m = m := by
  decide +kernel

theorem hB2_1_0 : ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ LS_1_0, Matrix.mulVec (Rm 1 σ) m = m := by
  decide +kernel

theorem layer1_0 : IsTop (permAct (Mk 0)) (Nk 0 1) (Nk 0 2) := by
  have hlt : Nk 0 2 < Nk 0 1 := lt_of_le_of_ne (N2_le_N1 0) (fun h => by
    have := card_N1 0
    rw [← h, card_N2] at this
    omega)
  have hgen := le_closure_of_indep 0 (N1_inv 0) (U1gen_mem 0) (card_N1 0).le gP_1_0 hS_1_0
    yP_1_0 MP_1_0 hM_1_0
  exact isTop_of_cyclic (permRep (Mk 0)) (N1_inv 0) (N2_inv 0) hlt 0 (fun _ => 1)
    (by rw [card_N1, card_N2, card_D]; decide) (U1gen_mem 0) hgen
    (StabSet 0 (U1gen)) (fun h hh => hh) (by rw [card_N1]; norm_num)
    (fun m hm _ => hfixA_triv m hm)
    (hfixB_of hL_1_0 0 (fun _ => hB1_1_0) (fun _ => hB2_1_0))
    (fun h => absurd rfl h)

theorem hS_1_1 : ∀ i, Perm.sign (gP_1_1 i) = 1 := by decide +kernel

theorem hM_1_1 : (Matrix.of fun i j => (U1gen) (Matrix.mulVec (Rm 1 (gP_1_1 i)⁻¹) (yP_1_1 j))) *
    MP_1_1 = 1 := by decide +kernel

theorem hL_1_1 : FixList 1 (U1gen) LS_1_1 := by decide +kernel

theorem hB1_1_1 : ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ LS_1_1, Matrix.mulVec (Rm 0 σ) m = m := by
  decide +kernel

theorem hB2_1_1 : ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ LS_1_1, Matrix.mulVec (Rm 1 σ) m = m := by
  decide +kernel

theorem layer1_1 : IsTop (permAct (Mk 1)) (Nk 1 1) (Nk 1 2) := by
  have hlt : Nk 1 2 < Nk 1 1 := lt_of_le_of_ne (N2_le_N1 1) (fun h => by
    have := card_N1 1
    rw [← h, card_N2] at this
    omega)
  have hgen := le_closure_of_indep 1 (N1_inv 1) (U1gen_mem 1) (card_N1 1).le gP_1_1 hS_1_1
    yP_1_1 MP_1_1 hM_1_1
  exact isTop_of_cyclic (permRep (Mk 1)) (N1_inv 1) (N2_inv 1) hlt 0 (fun _ => 1)
    (by rw [card_N1, card_N2, card_D]; decide) (U1gen_mem 1) hgen
    (StabSet 1 (U1gen)) (fun h hh => hh) (by rw [card_N1]; norm_num)
    (fun m hm _ => hfixA_triv m hm)
    (hfixB_of hL_1_1 0 (fun _ => hB1_1_1) (fun _ => hB2_1_1))
    (fun h => absurd rfl h)

theorem hS_2_0 : ∀ i, Perm.sign (gP_2_0 i) = 1 := by decide +kernel

theorem hM_2_0 : (Matrix.of fun i j => (U2gen 0) (Matrix.mulVec (Rm 0 (gP_2_0 i)⁻¹) (yP_2_0 j))) *
    MP_2_0 = 1 := by decide +kernel

theorem hL_2_0 : FixList 0 (U2gen 0) LS_2_0 := by decide +kernel

theorem hA_2_0 : ∀ m : V4, m ≠ 0 → (∀ σ ∈ LS_2_0, Matrix.mulVec (Rm 1 σ) m = m) →
    m = x0 1 := by decide +kernel

theorem hB1_2_0 : ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ LS_2_0, Matrix.mulVec (Rm 0 σ) m = m := by
  decide +kernel

theorem hRSs_2_0 : ∀ i, Perm.sign (RS2_0 i) = 1 := by decide +kernel

theorem hRSsum_2_0 : ∀ w : V4, ∑ i : Fin 5, (U2gen 0) (Matrix.mulVec (Rm 0 (RS2_0 i)⁻¹) w) = 0 := by
  decide +kernel

theorem layer2_0 : IsTop (permAct (Mk 0)) (Nk 0 2) (Nk 0 3) := by
  have hlt : Nk 0 3 < Nk 0 2 := lt_of_le_of_ne (N3_le_N2 0) (fun h => by
    have := card_N2 0
    rw [← h, card_N3] at this
    omega)
  have hgen := le_closure_of_indep 0 (N2_inv 0) (U2gen_mem 0) (card_N2 0).le gP_2_0 hS_2_0
    yP_2_0 MP_2_0 hM_2_0
  exact isTop_of_cyclic (permRep (Mk 0)) (N2_inv 0) (N3_inv 0) hlt 2 (x0 1)
    (by rw [card_N2, card_N3, card_D]; decide) (U2gen_mem 0) hgen
    (StabSet 0 (U2gen 0)) (fun h hh => hh) (by rw [card_N2]; norm_num)
    (hfixA_of hL_2_0 (x0 1) hA_2_0)
    (hfixB_of hL_2_0 2 (fun _ => hB1_2_0) (fun h => absurd rfl h))
    (fun _ ψ hs => no_trivial_quot 0 (N2_inv 0) (U2gen_mem 0) hgen (r := 5) ⟨2, rfl⟩
      (fun i => ⟨RS2_0 i, Perm.mem_alternatingGroup.mpr (hRSs_2_0 i)⟩)
      (hsum_of 0 RS2_0 hRSs_2_0 (U2gen 0) hRSsum_2_0) ψ hs)

theorem hS_2_1 : ∀ i, Perm.sign (gP_2_1 i) = 1 := by decide +kernel

theorem hM_2_1 : (Matrix.of fun i j => (U2gen 1) (Matrix.mulVec (Rm 1 (gP_2_1 i)⁻¹) (yP_2_1 j))) *
    MP_2_1 = 1 := by decide +kernel

theorem hL_2_1 : FixList 1 (U2gen 1) LS_2_1 := by decide +kernel

theorem hA_2_1 : ∀ m : V4, m ≠ 0 → (∀ σ ∈ LS_2_1, Matrix.mulVec (Rm 0 σ) m = m) →
    m = x0 0 := by decide +kernel

theorem hB2_2_1 : ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ LS_2_1, Matrix.mulVec (Rm 1 σ) m = m := by
  decide +kernel

theorem hRSs_2_1 : ∀ i, Perm.sign (RS2_1 i) = 1 := by decide +kernel

theorem hRSsum_2_1 : ∀ w : V4, ∑ i : Fin 5, (U2gen 1) (Matrix.mulVec (Rm 1 (RS2_1 i)⁻¹) w) = 0 := by
  decide +kernel

theorem layer2_1 : IsTop (permAct (Mk 1)) (Nk 1 2) (Nk 1 3) := by
  have hlt : Nk 1 3 < Nk 1 2 := lt_of_le_of_ne (N3_le_N2 1) (fun h => by
    have := card_N2 1
    rw [← h, card_N3] at this
    omega)
  have hgen := le_closure_of_indep 1 (N2_inv 1) (U2gen_mem 1) (card_N2 1).le gP_2_1 hS_2_1
    yP_2_1 MP_2_1 hM_2_1
  exact isTop_of_cyclic (permRep (Mk 1)) (N2_inv 1) (N3_inv 1) hlt 1 (x0 0)
    (by rw [card_N2, card_N3, card_D]; decide) (U2gen_mem 1) hgen
    (StabSet 1 (U2gen 1)) (fun h hh => hh) (by rw [card_N2]; norm_num)
    (hfixA_of hL_2_1 (x0 0) hA_2_1)
    (hfixB_of hL_2_1 1 (fun h => absurd rfl h) (fun _ => hB2_2_1))
    (fun _ ψ hs => no_trivial_quot 1 (N2_inv 1) (U2gen_mem 1) hgen (r := 5) ⟨2, rfl⟩
      (fun i => ⟨RS2_1 i, Perm.mem_alternatingGroup.mpr (hRSs_2_1 i)⟩)
      (hsum_of 1 RS2_1 hRSs_2_1 (U2gen 1) hRSsum_2_1) ψ hs)

theorem hS_3_0 : ∀ i, Perm.sign (gP_3_0 i) = 1 := by decide +kernel

theorem hM_3_0 : (Matrix.of fun i j => (Qfun) (Matrix.mulVec (Rm 0 (gP_3_0 i)⁻¹) (yP_3_0 j))) *
    MP_3_0 = 1 := by decide +kernel

theorem hL_3_0 : FixList 0 (Qfun) LS_3_0 := by decide +kernel

theorem hB1_3_0 : ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ LS_3_0, Matrix.mulVec (Rm 0 σ) m = m := by
  decide +kernel

theorem hB2_3_0 : ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ LS_3_0, Matrix.mulVec (Rm 1 σ) m = m := by
  decide +kernel

theorem layer3_0 : IsTop (permAct (Mk 0)) (Nk 0 3) (Nk 0 4) := by
  have hlt : Nk 0 4 < Nk 0 3 := lt_of_le_of_ne (N4_le_N3 0) (fun h => by
    have := card_N3 0
    rw [← h, card_N4] at this
    omega)
  have hgen := le_closure_of_indep 0 (N3_inv 0) (Qfun_mem_N3 0) (card_N3 0).le gP_3_0 hS_3_0
    yP_3_0 MP_3_0 hM_3_0
  exact isTop_of_cyclic (permRep (Mk 0)) (N3_inv 0) (N4_inv 0) hlt 0 (fun _ => 1)
    (by rw [card_N3, card_N4, card_D]; decide) (Qfun_mem_N3 0) hgen
    (StabSet 0 (Qfun)) (fun h hh => hh) (by rw [card_N3]; norm_num)
    (fun m hm _ => hfixA_triv m hm)
    (hfixB_of hL_3_0 0 (fun _ => hB1_3_0) (fun _ => hB2_3_0))
    (fun h => absurd rfl h)

theorem hS_3_1 : ∀ i, Perm.sign (gP_3_1 i) = 1 := by decide +kernel

theorem hM_3_1 : (Matrix.of fun i j => (Qfun) (Matrix.mulVec (Rm 1 (gP_3_1 i)⁻¹) (yP_3_1 j))) *
    MP_3_1 = 1 := by decide +kernel

theorem hL_3_1 : FixList 1 (Qfun) LS_3_1 := by decide +kernel

theorem hB1_3_1 : ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ LS_3_1, Matrix.mulVec (Rm 0 σ) m = m := by
  decide +kernel

theorem hB2_3_1 : ∀ m : V4, m ≠ 0 → ¬ ∀ σ ∈ LS_3_1, Matrix.mulVec (Rm 1 σ) m = m := by
  decide +kernel

theorem layer3_1 : IsTop (permAct (Mk 1)) (Nk 1 3) (Nk 1 4) := by
  have hlt : Nk 1 4 < Nk 1 3 := lt_of_le_of_ne (N4_le_N3 1) (fun h => by
    have := card_N3 1
    rw [← h, card_N4] at this
    omega)
  have hgen := le_closure_of_indep 1 (N3_inv 1) (Qfun_mem_N3 1) (card_N3 1).le gP_3_1 hS_3_1
    yP_3_1 MP_3_1 hM_3_1
  exact isTop_of_cyclic (permRep (Mk 1)) (N3_inv 1) (N4_inv 1) hlt 0 (fun _ => 1)
    (by rw [card_N3, card_N4, card_D]; decide) (Qfun_mem_N3 1) hgen
    (StabSet 1 (Qfun)) (fun h hh => hh) (by rw [card_N3]; norm_num)
    (fun m hm _ => hfixA_triv m hm)
    (hfixB_of hL_3_1 0 (fun _ => hB1_3_1) (fun _ => hB2_3_1))
    (fun h => absurd rfl h)

theorem ρk_irred (k : Fin 2) : ∀ S : AddSubgroup V4,
    (∀ (g : ↥(alternatingGroup (Fin 6))) (m : V4), m ∈ S → ρk k g m ∈ S) → S = ⊥ ∨ S = ⊤ := by
  fin_cases k
  · exact (a6_irred 1).2
  · exact (a6_irred 2).2

theorem layer4 (k : Fin 2) : IsTop (permAct (Mk k)) (Nk k 4) (Nk k 5) := by
  have hNb : (⊥ : AddSubgroup Fn) < Nk k 4 := lt_of_le_of_ne bot_le (fun h => by
    have := card_N4 k
    rw [← h] at this
    simp at this)
  refine isTop_bot_of_simple (fun g => rfl) hNb ?_
  intro S hS hSN hne
  let S' : AddSubgroup V4 := S.comap Cadd
  have hinv : ∀ (g : ↥(alternatingGroup (Fin 6))) (m : V4), m ∈ S' → ρk k g m ∈ S' := by
    intro g m hm
    have h1 : Cf m ∈ S := hm
    have h2 := hS g _ h1
    rw [permAct_Cf] at h2
    exact h2
  rcases ρk_irred k S' hinv with h | h
  · refine (AddSubgroup.eq_bot_iff_forall S).mpr fun u hu => ?_
    obtain ⟨x, rfl⟩ := hSN hu
    have hx : x ∈ S' := hu
    rw [h, AddSubgroup.mem_bot] at hx
    rw [hx]
    exact Cf_zero
  · exfalso
    apply hne
    refine le_antisymm hSN ?_
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ S' := by rw [h]; exact AddSubgroup.mem_top x
    exact hx

theorem chain_isTop (k : Fin 2) :
    ∀ n < 5, IsTop (permAct (Mk k)) (Nk k n) (Nk k (n + 1)) := by
  intro n hn
  fin_cases k
  · interval_cases n
    exacts [layer0_0, layer1_0, layer2_0, layer3_0, layer4 0]
  · interval_cases n
    exacts [layer0_1, layer1_1, layer2_1, layer3_1, layer4 1]

theorem Nk_five (k : Fin 2) : Nk k 5 = ⊥ := rfl

theorem jradPow_Mk (k : Fin 2) :
    ∀ n ≤ 5, jradPow (permAct (Mk k)) n (permCore (Mk k)) = Nk k n :=
  jradPow_eq_chain (Nk k) (chain_isTop k)

end CFSG.Quasithin.ShultG53
