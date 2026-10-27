module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08A6Defs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem a6_cartan_entry {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {e : Fin 5 ≃ M.Λ}
    (he : M.coxeter = (CoxeterMatrix.A 5).reindex e) :
    ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A 5 i j := by
  have hA : GGIntCartan M.coxeter (Matrix.reindex e e (CartanMatrix.A 5)) := by
    rw [he]
    exact GGIntCartan.reindex e (ggIntCartan_A 5)
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [M.isCartan.1, (ggIntCartan_A 5).1]
  · have hle : M.coxeter (e i) (e j) ≤ 3 := by
      rw [he]
      simp only [CoxeterMatrix.reindex_apply, CoxeterMatrix.A, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    have h := (GGIntCartan.pair (M := M.coxeter) M.isCartan hA (e.injective.ne hij)).2 hle
    simpa [Matrix.reindex_apply] using h.1

theorem ggQ2s08a6_coords {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA) {e : Fin 5 ≃ M.Λ}
    (he : M.coxeter = (CoxeterMatrix.A 5).reindex e) :
    ∃ κ : M.V ≃ₗ[ZMod 3] A6.V6, κ M.xV = A6.one6 ∧
      ∀ (k : Fin 5) (v : A6.V6), κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) =
        A6.perm6 (Equiv.swap k.castSucc k.succ) v := by
  classical
  obtain ⟨hxL, hcoroot, hxVmem, hfinrank, hsurj⟩ := hShape
  have hcardΛ : Fintype.card M.Λ = 5 :=
    (Fintype.card_congr e).symm.trans (Fintype.card_fin 5)
  have hdim : Module.finrank (ZMod 3) M.V = 6 := by rw [hfinrank, hcardΛ]
  have hentry : ∀ i j : Fin 5, M.cartan (e i) (e j) = CartanMatrix.A 5 i j :=
    a6_cartan_entry M he
  obtain ⟨v₀, hv₀⟩ := hsurj (Pi.single (e 0) (1 : ZMod 3))
  have hv₀root : ∀ i : Fin 5, M.root (e i) v₀ = if i = 0 then 1 else 0 := by
    intro i
    have h := congrFun hv₀ (e i)
    simpa [GGQ2LDatum.rootMap, LinearMap.pi_apply, Pi.single_apply, e.injective.eq_iff,
      eq_comm] using h
  let h : Fin 5 → M.V := fun l => M.coroot (e l)
  let f : Fin 6 → M.V :=
    ![v₀, v₀ - h 0, v₀ - h 0 - h 1, v₀ - h 0 - h 1 - h 2,
      v₀ - h 0 - h 1 - h 2 - h 3, v₀ - h 0 - h 1 - h 2 - h 3 - h 4]
  have hfstep : ∀ k : Fin 5, f k.succ = f k.castSucc - h k := by
    intro k
    fin_cases k <;> simp [f]
  have hfroot : ∀ (i : Fin 5) (j : Fin 6),
      M.root (e i) (f j) = (if j = i.castSucc then (1 : ZMod 3) else 0) -
        (if j = i.succ then 1 else 0) := by
    intro i
    refine Fin.induction ?base ?step
    · rw [show f 0 = v₀ from rfl, hv₀root i]
      fin_cases i <;> norm_num
    · intro k ih
      rw [hfstep k, map_sub, ih, M.pairing, hentry]
      fin_cases i <;> fin_cases k <;> norm_num [CartanMatrix.A] <;> decide
  have hli_h : LinearIndependent (ZMod 3) h := by
    simpa [h, Function.comp_def] using hcoroot.comp e e.injective
  have hgroup : ∑ j : Fin 6, f j =
      (6 : ℤ) • v₀ - (5 : ℤ) • h 0 - (4 : ℤ) • h 1 - (3 : ℤ) • h 2 -
        (2 : ℤ) • h 3 - (1 : ℤ) • h 4 := by
    simp [Fin.sum_univ_six, f]
    abel
  have hsum_ne : (∑ j : Fin 6, f j) ≠ 0 := by
    rw [hgroup]
    intro hz
    have h6v : (6 : ℤ) • v₀ = 0 := by
      rw [← Int.cast_smul_eq_zsmul (ZMod 3) 6 v₀]
      rw [show ((6 : ℤ) : ZMod 3) = 0 by decide, zero_smul]
    rw [h6v, zero_sub] at hz
    have hz' : (5 : ℤ) • h 0 + (4 : ℤ) • h 1 + (3 : ℤ) • h 2 + (2 : ℤ) • h 3 +
        (1 : ℤ) • h 4 = 0 := by
      have h : -((5 : ℤ) • h 0 + (4 : ℤ) • h 1 + (3 : ℤ) • h 2 + (2 : ℤ) • h 3 +
          (1 : ℤ) • h 4) = 0 := by
        rw [← hz]
        abel
      exact neg_eq_zero.mp h
    have hrel : ∑ l : Fin 5, (![2, 1, 0, 2, 1] : Fin 5 → ZMod 3) l • h l = 0 := by
      simp only [Fin.sum_univ_five] at hz' ⊢
      rw [← Int.cast_smul_eq_zsmul (ZMod 3) 5 (h 0),
        ← Int.cast_smul_eq_zsmul (ZMod 3) 4 (h 1),
        ← Int.cast_smul_eq_zsmul (ZMod 3) 3 (h 2),
        ← Int.cast_smul_eq_zsmul (ZMod 3) 2 (h 3),
        ← Int.cast_smul_eq_zsmul (ZMod 3) 1 (h 4)] at hz'
      have e5 : (5 : ZMod 3) = 2 := rfl
      have e4 : (4 : ZMod 3) = 1 := rfl
      have e3 : (3 : ZMod 3) = 0 := rfl
      have e2 : (2 : ZMod 3) = 2 := rfl
      have e1 : (1 : ZMod 3) = 1 := rfl
      simpa [e5, e4, e3, e2, e1] using hz'
    have hcoef := (Fintype.linearIndependent_iff.mp hli_h)
      (![2, 1, 0, 2, 1] : Fin 5 → ZMod 3) hrel 0
    exact (by decide : ((![2, 1, 0, 2, 1] : Fin 5 → ZMod 3) 0) ≠ 0) hcoef
  have hli_f : LinearIndependent (ZMod 3) f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hdiff : ∀ i : Fin 5, c i.castSucc = c i.succ := by
      intro i
      have hmap := congrArg (M.root (e i)) hc
      simp only [map_sum, map_smul, map_zero] at hmap
      have hsum_eval : ∑ j : Fin 6, c j •
          ((if j = i.castSucc then (1 : ZMod 3) else 0) -
            (if j = i.succ then 1 else 0)) = c i.castSucc - c i.succ := by
        fin_cases i <;> simp [Fin.sum_univ_six] <;> ring
      have hmap' : ∑ j : Fin 6, c j •
          ((if j = i.castSucc then (1 : ZMod 3) else 0) -
            (if j = i.succ then 1 else 0)) = 0 := by
        simpa only [hfroot i] using hmap
      rw [hsum_eval] at hmap'
      exact sub_eq_zero.mp hmap'
    have h01 : c 0 = c 1 := by simpa using hdiff 0
    have h12 : c 1 = c 2 := by simpa using hdiff 1
    have h23 : c 2 = c 3 := by simpa using hdiff 2
    have h34 : c 3 = c 4 := by simpa using hdiff 3
    have h45 : c 4 = c 5 := by simpa using hdiff 4
    have hall : ∀ j : Fin 6, c j = c 0 := by
      intro j
      fin_cases j <;> simp_all
    have hsum : ∑ j : Fin 6, c j • f j = c 0 • ∑ j : Fin 6, f j := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hall j]
    have hc0 : c 0 = 0 := by
      rw [hsum] at hc
      exact (smul_eq_zero.mp hc).resolve_right hsum_ne
    intro j
    rw [hall j, hc0]

  let b : Module.Basis (Fin 6) (ZMod 3) M.V :=
    basisOfLinearIndependentOfCardEqFinrank hli_f (by rw [hdim]; exact Fintype.card_fin 6)
  have hb : ⇑b = f := coe_basisOfLinearIndependentOfCardEqFinrank hli_f _
  have hswap_f : ∀ (k : Fin 5) (j : Fin 6),
      ggLin (p := 3) M.model (M.simple (e k)) (f j) =
        f (Equiv.swap k.castSucc k.succ j) := by
    intro k j
    rw [M.simple_apply (e k) (f j), hfroot k j]
    by_cases h1 : j = k.castSucc
    · subst h1
      rw [if_pos rfl, if_neg (Fin.castSucc_lt_succ.ne), Equiv.swap_apply_left]
      rw [hfstep k]
      module
    · by_cases h2 : j = k.succ
      · subst h2
        rw [if_neg (Fin.castSucc_lt_succ.ne.symm), if_pos rfl, Equiv.swap_apply_right]
        rw [hfstep k]
        module
      · rw [if_neg h1, if_neg h2, sub_self, zero_smul, sub_zero,
            Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hswap_b : ∀ (k : Fin 5) (j : Fin 6),
      ggLin (p := 3) M.model (M.simple (e k)) (b j) =
        b (Equiv.swap k.castSucc k.succ j) := by
    intro k j
    rw [congrFun hb j, congrFun hb (Equiv.swap k.castSucc k.succ j)]
    exact hswap_f k j
  have hxV_mem : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [M.fixed_x]
    exact Submodule.mem_span_singleton_self M.xV
  have hxV_fixed : ∀ k : Fin 5,
      ggLin (p := 3) M.model (M.simple (e k)) M.xV = M.xV := by
    intro k
    have hmem : M.simple (e k) ∈ ggAutomizer L Bs := by
      rw [M.automizer_L]
      exact Subgroup.subset_closure (Set.mem_range_self (e k))
    exact (mem_ggFixedSubmodule_iff.mp hxV_mem) (M.simple (e k)) hmem
  have hb_e6 : ∀ i : Fin 6, b.equivFun (b i) = A6.e6 i := by
    intro i
    funext j
    rw [Module.Basis.equivFun_self]
    simp [A6.e6, Pi.single_apply, eq_comm]
  have hperm_e6 : ∀ (σ : Equiv.Perm (Fin 6)) (i : Fin 6),
      A6.perm6 σ (A6.e6 i) = A6.e6 (σ i) := by
    intro σ i
    funext j
    rw [A6.perm6_apply]
    simp [A6.e6, Pi.single_apply, Equiv.symm_apply_eq]
  have hbact : ∀ k : Fin 5,
      (b.equivFun : M.V →ₗ[ZMod 3] A6.V6).comp
          ((ggLin (p := 3) M.model (M.simple (e k)) : M.V ≃ₗ[ZMod 3] M.V) :
            M.V →ₗ[ZMod 3] M.V) =
        (A6.perm6 (Equiv.swap k.castSucc k.succ) : A6.V6 →ₗ[ZMod 3] A6.V6).comp
          (b.equivFun : M.V →ₗ[ZMod 3] A6.V6) := by
    intro k
    refine b.ext fun j => ?_
    simp only [LinearMap.comp_apply]
    erw [hswap_b k j]
    erw [hb_e6 (Equiv.swap k.castSucc k.succ j), hb_e6 j,
      hperm_e6 (Equiv.swap k.castSucc k.succ) j]
  let w : A6.V6 := b.equivFun M.xV
  have hw_fixed : ∀ k : Fin 5,
      A6.perm6 (Equiv.swap k.castSucc k.succ) w = w := by
    intro k
    have h := congrArg (fun T : M.V →ₗ[ZMod 3] A6.V6 => T M.xV) (hbact k)
    simp only [LinearMap.comp_apply] at h
    erw [hxV_fixed k] at h
    simpa [w] using h.symm
  have hw_adj : ∀ k : Fin 5, w k.castSucc = w k.succ := by
    intro k
    have h := congrFun (hw_fixed k) k.castSucc
    rw [A6.perm6_apply] at h
    simpa [Equiv.swap_apply_left] using h.symm
  have h01 : w 0 = w 1 := by simpa using hw_adj 0
  have h12 : w 1 = w 2 := by simpa using hw_adj 1
  have h23 : w 2 = w 3 := by simpa using hw_adj 2
  have h34 : w 3 = w 4 := by simpa using hw_adj 3
  have h45 : w 4 = w 5 := by simpa using hw_adj 4
  have hw_eq : ∀ j : Fin 6, w j = w 0 := by
    intro j
    fin_cases j <;> simp_all
  have hxV_eq : M.xV = w 0 • ∑ j : Fin 6, b j := by
    calc M.xV = ∑ j : Fin 6, w j • b j := by
          rw [← b.sum_repr M.xV]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show w j = b.equivFun M.xV j from rfl, Module.Basis.equivFun_apply]
      _ = ∑ j : Fin 6, w 0 • b j :=
          Finset.sum_congr rfl fun j _ => by rw [hw_eq j]
      _ = w 0 • ∑ j : Fin 6, b j := by rw [Finset.smul_sum]
  have hsum_b_mem : (∑ j : Fin 6, b j) ∈
      ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [mem_ggFixedSubmodule_iff]
    intro φ hφ
    rw [M.automizer_L] at hφ
    refine Subgroup.closure_induction ?mem ?one ?mul ?inv hφ
    · rintro ψ ⟨k', rfl⟩
      rw [show k' = e (e.symm k') from (Equiv.apply_symm_apply e k').symm]
      rw [map_sum]
      rw [show (∑ j : Fin 6,
            ggLin (p := 3) M.model (M.simple (e (e.symm k'))) (b j)) =
          ∑ j : Fin 6, b (Equiv.swap (e.symm k').castSucc (e.symm k').succ j) from
        Finset.sum_congr rfl fun j _ => hswap_b (e.symm k') j]
      exact Equiv.sum_comp _ _
    · simp
    · intro x y hx hy ihx ihy
      rw [map_mul, LinearEquiv.mul_apply, ihy, ihx]
    · intro x hx ih
      rw [map_inv]
      calc ((ggLin (p := 3) M.model x) : M.V ≃ₗ[ZMod 3] M.V)⁻¹ (∑ j : Fin 6, b j)
          = ((ggLin (p := 3) M.model x) : M.V ≃ₗ[ZMod 3] M.V)⁻¹
              ((ggLin (p := 3) M.model x) (∑ j : Fin 6, b j)) := by rw [ih]
        _ = ∑ j : Fin 6, b j := LinearEquiv.symm_apply_apply _ _
  have hsum_b_ne : (∑ j : Fin 6, b j) ≠ 0 := by
    intro hzero
    have h1 := congrFun (congrArg (fun v => b.equivFun v) hzero) 0
    simp [map_sum, Finset.sum_apply] at h1
  have hw0 : w 0 ≠ 0 := by
    intro h0
    have hxV_zero : M.xV = 0 := by rw [hxV_eq, h0, zero_smul]
    have hfix : ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) = ⊥ := by
      rw [M.fixed_x]
      change Submodule.span (ZMod 3) {M.xV} = ⊥
      rw [hxV_zero, Submodule.span_singleton_eq_bot.mpr rfl]
    have hsum_zero : (∑ j : Fin 6, b j) = 0 := by
      have hmem := hsum_b_mem
      rw [hfix] at hmem
      simpa [Submodule.mem_bot] using hmem
    exact hsum_b_ne hsum_zero
  let u : (ZMod 3)ˣ := Units.mk0 (w 0) hw0
  let g : Module.Basis (Fin 6) (ZMod 3) M.V := b.unitsSMul (fun _ => u)
  let κ : M.V ≃ₗ[ZMod 3] A6.V6 := g.equivFun
  have hg : ∀ j, g j = (u : ZMod 3) • b j := fun j => by
    rw [Module.Basis.unitsSMul_apply]
    rfl
  have hswap_g : ∀ (k : Fin 5) (j : Fin 6),
      ggLin (p := 3) M.model (M.simple (e k)) (g j) =
        g (Equiv.swap k.castSucc k.succ j) := by
    intro k j
    rw [hg j, hg (Equiv.swap k.castSucc k.succ j), map_smul, hswap_b k j]
  have hκg : ∀ j, κ (g j) = A6.e6 j := by
    intro j
    funext i
    rw [Module.Basis.equivFun_self]
    simp [A6.e6, Pi.single_apply, eq_comm]
  have hsum_g : (∑ j : Fin 6, g j) = M.xV := by
    calc ∑ j : Fin 6, g j = ∑ j : Fin 6, u • b j :=
          Finset.sum_congr rfl fun j _ => hg j
      _ = u • ∑ j : Fin 6, b j := by rw [Finset.smul_sum]
      _ = w 0 • ∑ j : Fin 6, b j := by
        change (u : ZMod 3) • ∑ j : Fin 6, b j = w 0 • ∑ j : Fin 6, b j
        rw [show (u : ZMod 3) = w 0 from Units.val_mk0 hw0]
      _ = M.xV := hxV_eq.symm
  have hsum_e6 : ∀ v : A6.V6, (∑ j : Fin 6, v j • A6.e6 j) = v := by
    intro v
    funext i
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp [A6.e6]
    · intro j _ hj
      simp [A6.e6, hj]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  refine ⟨κ, ?_, ?_⟩
  · rw [← hsum_g, map_sum]
    rw [Finset.sum_congr rfl fun j _ => hκg j]
    funext i
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp [A6.e6, A6.one6]
    · intro j _ hj
      simp [A6.e6, hj]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  · intro k v
    have hκsymm : ∀ j, κ.symm (A6.e6 j) = g j := by
      intro j
      rw [← hκg j, LinearEquiv.symm_apply_apply]
    have hκv : κ.symm v = ∑ j : Fin 6, v j • g j := by
      conv_lhs => rw [← hsum_e6 v]
      rw [map_sum]
      simp [map_smul, hκsymm]
    have hlin : ggLin (p := 3) M.model (M.simple (e k)) (∑ j : Fin 6, v j • g j) =
        ∑ j : Fin 6, v j • g (Equiv.swap k.castSucc k.succ j) := by
      rw [map_sum]
      simp [map_smul, hswap_g k]
    have hκsum : κ (∑ j : Fin 6, v j • g (Equiv.swap k.castSucc k.succ j)) =
        ∑ j : Fin 6, v j • A6.e6 (Equiv.swap k.castSucc k.succ j) := by
      rw [map_sum]
      simp [map_smul, hκg]
    have hpermv : A6.perm6 (Equiv.swap k.castSucc k.succ) v =
        ∑ j : Fin 6, v j • A6.e6 (Equiv.swap k.castSucc k.succ j) := by
      conv_lhs => rw [← hsum_e6 v]
      rw [map_sum]
      simp [map_smul, hperm_e6]
    rw [hκv, hlin, hκsum, hpermv]

end CFSG.StandardType

end
