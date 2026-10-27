module

public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU
public import CFSG.LocalAnalysis.StandardType.GGQ2InLCoverFrame
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.Mathlib.Perm.ChainSwap

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace UnitRaw

@[expose] noncomputable def permHomQ (N : ℕ) : Equiv.Perm (Fin N) →* (Vfull N ≃ₗ[F] Vfull N) where
  toFun := permEquivQ N
  map_one' := by
    apply LinearEquiv.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H w =>
      rw [← Submodule.mkQ_apply (oneLine N)]
      change (permEquivQ N 1) ((oneLine N).mkQ w) = (oneLine N).mkQ w
      rw [permEquivQ_mk N 1 w]
      congr 1
  map_mul' := by
    intro σ τ
    apply LinearEquiv.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H w =>
      rw [← Submodule.mkQ_apply (oneLine N), LinearEquiv.mul_apply]
      rw [permEquivQ_mk N (σ * τ) w, permEquivQ_mk N τ w,
        permEquivQ_mk N σ (fun i => w (τ.symm i))]
      congr 1

theorem coe_permEquivH (N : ℕ) (σ : Equiv.Perm (Fin N)) (v : ↥(heart N)) :
    ((permEquivH N σ v : ↥(heart N)) : Vfull N) = permEquivQ N σ v :=
  LinearEquiv.ofSubmodules_apply (permEquivQ N σ) (map_heart_permEquivQ N σ) v

@[expose] noncomputable def permHomH (N : ℕ) :
    Equiv.Perm (Fin N) →* (↥(heart N) ≃ₗ[F] ↥(heart N)) where
  toFun := permEquivH N
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    rw [coe_permEquivH N 1 v]
    change (permHomQ N 1) (v : Vfull N) = (v : Vfull N)
    rw [map_one]
    rfl
  map_mul' := by
    intro σ τ
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    rw [LinearEquiv.mul_apply, coe_permEquivH N (σ * τ) v,
      coe_permEquivH N σ ((permEquivH N τ) v), coe_permEquivH N τ v]
    change (permHomQ N (σ * τ)) (v : Vfull N) =
      (permHomQ N σ) ((permHomQ N τ) (v : Vfull N))
    rw [map_mul, LinearEquiv.mul_apply]

theorem permHomQ_apply (N : ℕ) (σ : Equiv.Perm (Fin N)) : permHomQ N σ = permEquivQ N σ := rfl

theorem permHomH_apply (N : ℕ) (σ : Equiv.Perm (Fin N)) : permHomH N σ = permEquivH N σ := rfl

theorem mkQ_single_sub_single_mem_heart (N : ℕ) (i j : Fin N) :
    (oneLine N).mkQ (Pi.single i 1 - Pi.single j 1) ∈ heart N := by
  rw [heart, Submodule.mem_map]
  refine ⟨Pi.single i 1 - Pi.single j 1, ?_, rfl⟩
  rw [LinearMap.mem_ker, sumFun_apply]
  simp [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single']

end UnitRaw

private theorem gcca_exists_perm_two {α : Type*} [DecidableEq α] {a b x y : α}
    (hab : a ≠ b) (hxy : x ≠ y) : ∃ σ : Equiv.Perm α, σ a = x ∧ σ b = y := by
  refine ⟨Equiv.swap (Equiv.swap a x b) y * Equiv.swap a x, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne ?_ hxy
    by_cases hb : b = x
    · rw [← hb, Equiv.swap_apply_right]
      exact fun h => hab h.symm
    · rw [Equiv.swap_apply_of_ne_of_ne hab.symm hb]
      exact fun h => hb h.symm
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

private theorem gcca_reindex_refl {ι : Type*} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private theorem gcca_chain_const {m : ℕ} {α : Type*} {d : Fin (m + 1) → α} {w : α → UnitRaw.F}
    (h : ∀ κ : Fin m, w (d κ.castSucc) = w (d κ.succ)) (p q : Fin (m + 1)) :
    w (d p) = w (d q) := by
  have key : ∀ (a n : ℕ) (ha : a < m + 1) (han : a + n < m + 1),
      w (d ⟨a, ha⟩) = w (d ⟨a + n, han⟩) := by
    intro a n
    induction n with
    | zero =>
      intro ha han
      rw [show (⟨a, ha⟩ : Fin (m + 1)) = ⟨a + 0, han⟩ from Fin.ext (by simp)]
    | succ n ih =>
      intro ha han
      have hstep : w (d ⟨a + n, by omega⟩) = w (d ⟨a + n + 1, han⟩) := by
        have := h ⟨a + n, by omega⟩
        simpa using this
      rw [ih ha (by omega), hstep]
      rw [show (⟨a + n + 1, han⟩ : Fin (m + 1)) = ⟨a + (n + 1), han⟩ from Fin.ext (by simp; omega)]
  rcases le_total (p : ℕ) (q : ℕ) with hpq | hpq
  · have hq : (⟨(p : ℕ) + ((q : ℕ) - (p : ℕ)), by omega⟩ : Fin (m + 1)) = q :=
      Fin.ext (by simp; omega)
    have := key (p : ℕ) ((q : ℕ) - (p : ℕ)) p.isLt (by omega)
    rwa [hq] at this
  · have hp : (⟨(q : ℕ) + ((p : ℕ) - (q : ℕ)), by omega⟩ : Fin (m + 1)) = p :=
      Fin.ext (by simp; omega)
    have := key (q : ℕ) ((p : ℕ) - (q : ℕ)) q.isLt (by omega)
    rw [hp] at this
    exact this.symm

private theorem gcca_kernel_chain {N m : ℕ} {e : Fin (m + 1) → Fin N} {S : Finset (Fin N)}
    (himg : Finset.univ.image e = S) (w : UnitRaw.Vfull N) :
    (∀ κ : Fin m, UnitRaw.diffFun N (e κ.castSucc) (e κ.succ) w = 0) ↔
      w ∈ UnitRaw.cent S := by
  obtain ⟨w0, hw0⟩ := Submodule.mkQ_surjective (UnitRaw.oneLine N) w
  constructor
  · intro h
    rw [UnitRaw.mem_cent_iff]
    refine ⟨w0, hw0, ?_⟩
    intro i hi j hj
    have hi' : i ∈ Finset.univ.image e := by rw [himg]; exact hi
    have hj' : j ∈ Finset.univ.image e := by rw [himg]; exact hj
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hi'
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hj'
    rw [← ha, ← hb]
    refine gcca_chain_const (fun κ => ?_) a b
    have := h κ
    rw [← hw0, UnitRaw.diffFun_mk, sub_eq_zero] at this
    exact this
  · intro hv
    obtain ⟨w', hw', hconst⟩ := (UnitRaw.mem_cent_iff S w).mp hv
    intro κ
    rw [← hw', UnitRaw.diffFun_mk, sub_eq_zero]
    exact hconst _ (by rw [← himg]; exact Finset.mem_image.mpr ⟨κ.castSucc, Finset.mem_univ _, rfl⟩)
      _ (by rw [← himg]; exact Finset.mem_image.mpr ⟨κ.succ, Finset.mem_univ _, rfl⟩)

private theorem gcca_forall_succ_iff {n : ℕ} {P : Fin (n + 1) → Prop} :
    (∀ i : Fin (n + 1), i ≠ 0 → P i) ↔ (∀ κ : Fin n, P κ.succ) := by
  constructor
  · intro h κ
    exact h κ.succ (Fin.succ_ne_zero κ)
  · intro h i hi
    obtain ⟨κ, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
    exact h κ

private theorem gcca_forall_castSucc_iff {n : ℕ} {P : Fin (n + 1) → Prop} :
    (∀ i : Fin (n + 1), i ≠ Fin.last n → P i) ↔ (∀ κ : Fin n, P κ.castSucc) := by
  constructor
  · intro h κ
    exact h κ.castSucc (Fin.castSucc_ne_last κ)
  · intro h i hi
    obtain ⟨κ, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    exact h κ

private theorem gcca_image_succ_erase {n : ℕ} (c : Equiv.Perm (Fin (n + 2)))
    (m : Fin (n + 2)) (hc0 : c 0 = m) :
    Finset.univ.image (c ∘ Fin.succ) = Finset.univ.erase m := by
  change Finset.univ.image (fun j : Fin (n + 1) => c j.succ) = Finset.univ.erase m
  have hsub : Finset.univ.image (fun j : Fin (n + 1) => c j.succ) ⊆
      Finset.univ.erase m := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, -, hj⟩ := hx
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ x⟩
    intro hxm
    have hc : c j.succ = c 0 := by rw [hj, hxm, hc0]
    exact Fin.succ_ne_zero j (c.injective hc)
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [Finset.card_image_of_injective (s := Finset.univ) (f := fun j : Fin (n + 1) => c j.succ)
      (fun a b h => Fin.succ_injective (n + 1) (c.injective h)),
    Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fin]
  omega

private theorem gcca_image_castSucc_erase {n : ℕ} (c : Equiv.Perm (Fin (n + 2)))
    (m' : Fin (n + 2)) (hclast : c (Fin.last (n + 1)) = m') :
    Finset.univ.image (c ∘ Fin.castSucc) = Finset.univ.erase m' := by
  change Finset.univ.image (fun j : Fin (n + 1) => c j.castSucc) = Finset.univ.erase m'
  have hsub : Finset.univ.image (fun j : Fin (n + 1) => c j.castSucc) ⊆
      Finset.univ.erase m' := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, -, hj⟩ := hx
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ x⟩
    intro hxm
    have hc : c j.castSucc = c (Fin.last (n + 1)) := by rw [hj, hxm, hclast]
    exact Fin.castSucc_ne_last j (c.injective hc)
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [Finset.card_image_of_injective (s := Finset.univ) (f := fun j : Fin (n + 1) => c j.castSucc)
      (fun a b h => Fin.castSucc_injective (n + 1) (c.injective h)),
    Finset.card_erase_of_mem (Finset.mem_univ m'), Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fin]
  omega

private theorem gcca_chain_closure {N m : ℕ} {V : Type} [AddCommGroup V] [Module UnitRaw.F V]
    (ρ : Equiv.Perm (Fin N) →* (V ≃ₗ[UnitRaw.F] V))
    {e : Fin (m + 1) → Fin N} {S : Finset (Fin N)}
    (he : Function.Injective e) (himg : Finset.univ.image e = S) :
    Subgroup.closure (Set.range fun κ : Fin m =>
      ρ (Equiv.swap (e κ.castSucc) (e κ.succ))) =
      Subgroup.closure {T | ∃ i ∈ S, ∃ j ∈ S, T = ρ (Equiv.swap i j)} := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro T ⟨κ, rfl⟩
    refine Subgroup.subset_closure ⟨e κ.castSucc, ?_, e κ.succ, ?_, rfl⟩
    · rw [← himg]
      exact Finset.mem_image.mpr ⟨κ.castSucc, Finset.mem_univ _, rfl⟩
    · rw [← himg]
      exact Finset.mem_image.mpr ⟨κ.succ, Finset.mem_univ _, rfl⟩
  · rw [Subgroup.closure_le]
    rintro T ⟨i, hi, j, hj, rfl⟩
    rw [← himg] at hi hj
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hi
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hj
    rw [← hp, ← hq]
    have h := CFSG.Perm.map_swap_mem_closure_chainSwap ρ he p q
    simpa using h

private theorem gcca_cartanA_entry (m : ℕ) (i j : Fin m) :
    CartanMatrix.A m i j =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 :=
  rfl

private theorem gcca_finCartan (n : ℕ) (i j : Fin (n + 1)) :
    ((if i.castSucc = j.castSucc then (1 : UnitRaw.F) else 0) -
        (if i.castSucc = j.succ then 1 else 0)) -
      ((if i.succ = j.castSucc then 1 else 0) - (if i.succ = j.succ then 1 else 0)) =
      ((CartanMatrix.A (n + 1) i j : ℤ) : UnitRaw.F) := by
  simp only [Fin.castSucc_inj, Fin.succ_inj]
  rw [gcca_cartanA_entry]
  by_cases hij : i = j
  · subst hij
    have h1 : ¬ (i.castSucc = i.succ) := (Fin.castSucc_lt_succ).ne
    have h2 : ¬ (i.succ = i.castSucc) := fun h => h1 h.symm
    simp [h1, h2]
    norm_num
  · rw [if_neg hij]
    by_cases hadj : (i : ℕ) + 1 = j.val ∨ (j : ℕ) + 1 = i.val
    · rw [if_pos hadj]
      rcases hadj with h | h
      · have h2 : i.succ = j.castSucc := by ext; simp [Fin.val_succ]; omega
        have h1 : ¬ (i.castSucc = j.succ) := by
          intro hh
          have := congrArg Fin.val hh
          simp [Fin.val_succ] at this
          omega
        simp [hij, h1, h2]
      · have h1 : i.castSucc = j.succ := by ext; simp [Fin.val_succ]; omega
        have h2 : ¬ (i.succ = j.castSucc) := by
          intro hh
          have := congrArg Fin.val hh
          simp [Fin.val_succ] at this
          omega
        simp [hij, h1, h2]
    · rw [if_neg hadj]
      have h1 : ¬ (i.castSucc = j.succ) := by
        intro hh
        have := congrArg Fin.val hh
        simp [Fin.val_succ] at this
        omega
      have h2 : ¬ (i.succ = j.castSucc) := by
        intro hh
        have := congrArg Fin.val hh
        simp [Fin.val_succ] at this
        omega
      simp [hij, h1, h2]

private theorem gcca_pairing {N n : ℕ} {d : Fin (n + 2) → Fin N} (hd : Function.Injective d)
    (i j : Fin (n + 1)) :
    UnitRaw.diffFun N (d i.castSucc) (d i.succ)
      ((UnitRaw.oneLine N).mkQ
        (Pi.single (d j.castSucc) 1 - Pi.single (d j.succ) 1)) =
      ((CartanMatrix.A (n + 1) i j : ℤ) : UnitRaw.F) := by
  rw [UnitRaw.diffFun_mk]
  simp only [Pi.sub_apply, Pi.single_apply, hd.eq_iff]
  exact gcca_finCartan n i j

private theorem gcca_refl_eq {N n : ℕ} {d : Fin (n + 2) → Fin N}
    (hd : Function.Injective d) (i : Fin (n + 1)) (u : UnitRaw.Vfull N) :
    u - UnitRaw.diffFun N (d i.castSucc) (d i.succ) u •
      ((UnitRaw.oneLine N).mkQ
        (Pi.single (d i.castSucc) 1 - Pi.single (d i.succ) 1)) =
      UnitRaw.permEquivQ N (Equiv.swap (d i.castSucc) (d i.succ)) u := by
  induction u using Submodule.Quotient.induction_on with
  | H w =>
    have hmk : (Submodule.Quotient.mk w : UnitRaw.Vfull N) =
        (UnitRaw.oneLine N).mkQ w := (Submodule.mkQ_apply _ _).symm
    rw [hmk, UnitRaw.permEquivQ_mk, Equiv.symm_swap (d i.castSucc) (d i.succ)]
    change (UnitRaw.oneLine N).mkQ w -
        UnitRaw.diffFun N (d i.castSucc) (d i.succ)
          ((UnitRaw.oneLine N).mkQ w) •
        ((UnitRaw.oneLine N).mkQ
          (Pi.single (d i.castSucc) 1 - Pi.single (d i.succ) 1)) =
      (UnitRaw.oneLine N).mkQ
        (fun k => w ((Equiv.swap (d i.castSucc) (d i.succ)) k))
    rw [UnitRaw.diffFun_mk, ← LinearMap.map_smul, ← LinearMap.map_sub]
    congr 1
    funext k
    by_cases hk : k = d i.castSucc
    · subst hk
      have hne : d i.castSucc ≠ d i.succ := by
        intro h
        exact (Fin.castSucc_lt_succ).ne (hd h)
      simp [Pi.sub_apply, hne, Equiv.swap_apply_left, Pi.smul_apply, smul_eq_mul]
    · by_cases hk2 : k = d i.succ
      · subst hk2
        have hne : d i.succ ≠ d i.castSucc := by
          intro h
          exact (Fin.castSucc_lt_succ).ne (hd h.symm)
        simp [Pi.sub_apply, hne, Equiv.swap_apply_right, Pi.smul_apply, smul_eq_mul]
      · have hk' : k ≠ d i.castSucc := hk
        have hk'' : k ≠ d i.succ := hk2
        rw [Equiv.swap_apply_of_ne_of_ne hk' hk'']
        simp [Pi.sub_apply, hk', hk'', Pi.smul_apply, smul_eq_mul]

theorem chainA_model {N n : ℕ} (hn : 1 ≤ n) {V : Type} [AddCommGroup V] [Module UnitRaw.F V]
    (π : V →ₗ[UnitRaw.F] UnitRaw.Vfull N) (hπ : Function.Injective π)
    (ρ : Equiv.Perm (Fin N) →* (V ≃ₗ[UnitRaw.F] V))
    (hρ : ∀ σ v, π (ρ σ v) = UnitRaw.permEquivQ N σ (π v))
    {d : Fin (n + 2) → Fin N} (hd : Function.Injective d) (h : Fin (n + 1) → V)
    (hh : ∀ i, π (h i) = (UnitRaw.oneLine N).mkQ
      (Pi.single (d i.castSucc) 1 - Pi.single (d i.succ) 1)) :
    ∃ W : GGQ2LinOn 3 V,
      W.toLin.parab {i | i ≠ W.a} = Subgroup.closure
        {T | ∃ i ∈ Finset.univ.image (d ∘ Fin.succ), ∃ j ∈ Finset.univ.image (d ∘ Fin.succ),
          T = ρ (Equiv.swap i j)} ∧
      W.toLin.parab {i | i ≠ W.b} = Subgroup.closure
        {T | ∃ i ∈ Finset.univ.image (d ∘ Fin.castSucc),
          ∃ j ∈ Finset.univ.image (d ∘ Fin.castSucc), T = ρ (Equiv.swap i j)} ∧
      (∀ v, (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔
        π v ∈ UnitRaw.cent (Finset.univ.image (d ∘ Fin.succ))) ∧
      (∀ v, (∀ i ∈ {i | i ≠ W.b}, W.root i v = 0) ↔
        π v ∈ UnitRaw.cent (Finset.univ.image (d ∘ Fin.castSucc))) ∧
      ∃! c, c ≠ W.b ∧ W.cartan W.b c ≠ 0 := by
  classical
  let dA : Fin (n + 1) → Fin N := fun j => d j.succ
  let dB : Fin (n + 1) → Fin N := fun j => d j.castSucc
  have hdA : Function.Injective dA :=
    fun a b hab => Fin.succ_injective (n + 1) (hd hab)
  have hdB : Function.Injective dB :=
    fun a b hab => Fin.castSucc_injective (n + 1) (hd hab)
  let W : GGQ2LinOn 3 V :=
    { ι := Fin (n + 1)
      coxeter := CoxeterMatrix.A (n + 1)
      cartan := CartanMatrix.A (n + 1)
      coroot := h
      root := fun i => (UnitRaw.diffFun N (d i.castSucc) (d i.succ)).comp π
      a := 0
      b := Fin.last n
      a_ne_b := by
        intro hab
        have := congrArg Fin.val hab
        simp [Fin.val_last] at this
        omega
      a_leaf := by
        refine ⟨⟨1, by omega⟩, ⟨by simp, ?_⟩, ?_⟩
        · rw [gcca_cartanA_entry]
          have h0 : ¬ ((0 : Fin (n + 1)) = ⟨1, by omega⟩) := by simp
          rw [if_neg h0]
          have hcond : ((0 : Fin (n + 1)) : ℕ) + 1 =
                ((⟨1, by omega⟩ : Fin (n + 1)) : ℕ) ∨
              ((⟨1, by omega⟩ : Fin (n + 1)) : ℕ) + 1 = ((0 : Fin (n + 1)) : ℕ) := by
            left
            simp
          rw [if_pos hcond]
          norm_num
        · intro y hy
          rw [gcca_cartanA_entry] at hy
          have hy0 : y ≠ (0 : Fin (n + 1)) := fun hab => hy.1 hab
          rw [if_neg (show ¬ ((0 : Fin (n + 1)) = y) from fun hab => hy0 hab.symm)] at hy
          have hcond : ((0 : Fin (n + 1)) : ℕ) + 1 = (y : ℕ) ∨
              (y : ℕ) + 1 = ((0 : Fin (n + 1)) : ℕ) := by
            by_contra hc
            rw [if_neg hc] at hy
            exact hy.2 rfl
          have hy1 : (y : ℕ) = 1 := by
            rcases hcond with h | h
            · simpa [Fin.val_zero] using h.symm
            · exfalso
              simp only [Fin.val_zero] at h
              omega
          exact Fin.ext (by simpa using hy1)
      isWeyl := Or.inl ⟨n + 1, Equiv.refl _, by omega,
        Or.inl (gcca_reindex_refl (CoxeterMatrix.A (n + 1))).symm⟩
      isCartan := ggIntCartan_A (n + 1)
      pairing := fun i j => by
        change UnitRaw.diffFun N (d i.castSucc) (d i.succ) (π (h j)) = _
        rw [hh j]
        exact gcca_pairing hd i j }
  have hrefl : ∀ i : Fin (n + 1),
      W.toLin.simpleRefl i = ρ (Equiv.swap (d i.castSucc) (d i.succ)) := by
    intro i
    apply LinearEquiv.ext
    intro v
    apply hπ
    rw [hρ]
    rw [GGQ2Lin.simpleRefl, Module.reflection_apply]
    change π (v - W.root i v • h i) =
      UnitRaw.permEquivQ N (Equiv.swap (d i.castSucc) (d i.succ)) (π v)
    rw [map_sub, map_smul, hh i]
    change π v - UnitRaw.diffFun N (d i.castSucc) (d i.succ) (π v) •
      ((UnitRaw.oneLine N).mkQ
        (Pi.single (d i.castSucc) 1 - Pi.single (d i.succ) 1)) =
      UnitRaw.permEquivQ N (Equiv.swap (d i.castSucc) (d i.succ)) (π v)
    exact gcca_refl_eq hd i (π v)
  have hsetA : W.toLin.simpleRefl '' {i : Fin (n + 1) | i ≠ W.a} =
      Set.range (fun κ : Fin n =>
        ρ (Equiv.swap (dA κ.castSucc) (dA κ.succ))) := by
    have ha : W.a = (0 : Fin (n + 1)) := rfl
    rw [ha]
    ext T
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨κ, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
      refine ⟨κ, ?_⟩
      simp only [dA]
      rw [hrefl, Fin.castSucc_succ]
    · rintro ⟨κ, rfl⟩
      refine ⟨κ.succ, Fin.succ_ne_zero κ, ?_⟩
      simp only [dA]
      rw [hrefl, Fin.castSucc_succ]
  have hsetB : W.toLin.simpleRefl '' {i : Fin (n + 1) | i ≠ W.b} =
      Set.range (fun κ : Fin n =>
        ρ (Equiv.swap (dB κ.castSucc) (dB κ.succ))) := by
    have hb : W.b = (Fin.last n : Fin (n + 1)) := rfl
    rw [hb]
    ext T
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨κ, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      refine ⟨κ, ?_⟩
      simp only [dB]
      rw [hrefl, ← Fin.castSucc_succ κ]
    · rintro ⟨κ, rfl⟩
      refine ⟨κ.castSucc, Fin.castSucc_ne_last κ, ?_⟩
      simp only [dB]
      rw [hrefl, ← Fin.castSucc_succ κ]
  have hparabA : W.toLin.parab {i | i ≠ W.a} =
      Subgroup.closure {T | ∃ i ∈ Finset.univ.image (d ∘ Fin.succ),
        ∃ j ∈ Finset.univ.image (d ∘ Fin.succ), T = ρ (Equiv.swap i j)} := by
    rw [GGQ2Lin.parab, hsetA]
    exact gcca_chain_closure (m := n) (e := d ∘ Fin.succ)
      (S := Finset.univ.image (d ∘ Fin.succ)) ρ hdA rfl
  have hparabB : W.toLin.parab {i | i ≠ W.b} =
      Subgroup.closure {T | ∃ i ∈ Finset.univ.image (d ∘ Fin.castSucc),
        ∃ j ∈ Finset.univ.image (d ∘ Fin.castSucc), T = ρ (Equiv.swap i j)} := by
    rw [GGQ2Lin.parab, hsetB]
    exact gcca_chain_closure (m := n) (e := d ∘ Fin.castSucc)
      (S := Finset.univ.image (d ∘ Fin.castSucc)) ρ hdB rfl
  have hkerA : ∀ v, (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔
      π v ∈ UnitRaw.cent (Finset.univ.image (d ∘ Fin.succ)) := by
    intro v
    change (∀ i : Fin (n + 1), i ≠ (0 : Fin (n + 1)) → W.root i v = 0) ↔
      π v ∈ UnitRaw.cent (Finset.univ.image (d ∘ Fin.succ))
    rw [gcca_forall_succ_iff]
    have hroot : ∀ κ : Fin n, W.root κ.succ v =
        UnitRaw.diffFun N ((d ∘ Fin.succ) κ.castSucc) ((d ∘ Fin.succ) κ.succ) (π v) := by
      intro κ
      change UnitRaw.diffFun N (d (κ.succ).castSucc) (d (κ.succ).succ) (π v) =
        UnitRaw.diffFun N (d (κ.castSucc).succ) (d (κ.succ).succ) (π v)
      rw [Fin.castSucc_succ]
    simp only [hroot]
    exact gcca_kernel_chain rfl (π v)
  have hkerB : ∀ v, (∀ i ∈ {i | i ≠ W.b}, W.root i v = 0) ↔
      π v ∈ UnitRaw.cent (Finset.univ.image (d ∘ Fin.castSucc)) := by
    intro v
    change (∀ i : Fin (n + 1), i ≠ Fin.last n → W.root i v = 0) ↔
      π v ∈ UnitRaw.cent (Finset.univ.image (d ∘ Fin.castSucc))
    rw [gcca_forall_castSucc_iff]
    have hroot : ∀ κ : Fin n, W.root κ.castSucc v =
        UnitRaw.diffFun N ((d ∘ Fin.castSucc) κ.castSucc)
          ((d ∘ Fin.castSucc) κ.succ) (π v) := by
      intro κ
      change UnitRaw.diffFun N (d (κ.castSucc).castSucc) (d (κ.castSucc).succ) (π v) =
        UnitRaw.diffFun N (d (κ.castSucc).castSucc) (d (κ.succ).castSucc) (π v)
      rw [← Fin.castSucc_succ κ]
    simp only [hroot]
    exact gcca_kernel_chain rfl (π v)
  have hleaf : ∃! c, c ≠ W.b ∧ W.cartan W.b c ≠ 0 := by
    refine ⟨⟨n - 1, by omega⟩, ⟨?_, ?_⟩, ?_⟩
    · change (⟨n - 1, by omega⟩ : Fin (n + 1)) ≠ Fin.last n
      intro hab
      have := congrArg Fin.val hab
      simp only [Fin.val_last] at this
      omega
    · change CartanMatrix.A (n + 1) (Fin.last n) (⟨n - 1, by omega⟩ : Fin (n + 1)) ≠ 0
      rw [gcca_cartanA_entry]
      have h1 : ¬ ((Fin.last n : Fin (n + 1)) = ⟨n - 1, by omega⟩) := by
        intro hab
        have := congrArg Fin.val hab
        simp only [Fin.val_last] at this
        omega
      rw [if_neg h1]
      have hcond : ((Fin.last n : Fin (n + 1)) : ℕ) + 1 =
            ((⟨n - 1, by omega⟩ : Fin (n + 1)) : ℕ) ∨
          ((⟨n - 1, by omega⟩ : Fin (n + 1)) : ℕ) + 1 =
            ((Fin.last n : Fin (n + 1)) : ℕ) := by
        right
        simp only [Fin.val_last]
        omega
      rw [if_pos hcond]
      norm_num
    · intro y hy
      change y ≠ Fin.last n ∧ CartanMatrix.A (n + 1) (Fin.last n) y ≠ 0 at hy
      rw [gcca_cartanA_entry] at hy
      have h1 : ¬ ((Fin.last n : Fin (n + 1)) = y) := fun hab => hy.1 hab.symm
      rw [if_neg h1] at hy
      have hcond : ((Fin.last n : Fin (n + 1)) : ℕ) + 1 = (y : ℕ) ∨
          (y : ℕ) + 1 = ((Fin.last n : Fin (n + 1)) : ℕ) := by
        by_contra hc
        rw [if_neg hc] at hy
        exact hy.2 rfl
      have hy1 : (y : ℕ) + 1 = n := by
        rcases hcond with h | h
        · simp only [Fin.val_last] at h
          omega
        · simpa only [Fin.val_last] using h
      exact Fin.ext (by
        change (y : ℕ) = n - 1
        omega)
  exact ⟨W, hparabA, hparabB, hkerA, hkerB, hleaf⟩

theorem unitFull_inLLeafAt_erase {n : ℕ} (hn : 1 ≤ n) {m m' : Fin (n + 2)} (hmm' : m ≠ m')
    {vx z : UnitRaw.Vfull (n + 2)}
    (hA : UnitRaw.cent (Finset.univ.erase m) = Submodule.span UnitRaw.F {vx})
    (hB : UnitRaw.cent (Finset.univ.erase m') = Submodule.span UnitRaw.F {z}) :
    InLLeafAt (unitFullEntry (n + 2)) vx z (Finset.univ.erase m) (Finset.univ.erase m') := by
  classical
  have h0last : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro hab
    have := congrArg Fin.val hab
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  obtain ⟨c, hc0, hclast⟩ := gcca_exists_perm_two (a := (0 : Fin (n + 2)))
    (b := Fin.last (n + 1)) (x := m) (y := m') h0last hmm'
  have himgA : Finset.univ.image (c ∘ Fin.succ) = Finset.univ.erase m :=
    gcca_image_succ_erase c m hc0
  have himgB : Finset.univ.image (c ∘ Fin.castSucc) = Finset.univ.erase m' :=
    gcca_image_castSucc_erase c m' hclast
  let h : Fin (n + 1) → UnitRaw.Vfull (n + 2) := fun i =>
    (UnitRaw.oneLine (n + 2)).mkQ
      (Pi.single (c i.castSucc) 1 - Pi.single (c i.succ) 1)
  have hh : ∀ i, (LinearMap.id : UnitRaw.Vfull (n + 2) →ₗ[UnitRaw.F] UnitRaw.Vfull (n + 2))
      (h i) = (UnitRaw.oneLine (n + 2)).mkQ
        (Pi.single (c i.castSucc) 1 - Pi.single (c i.succ) 1) := fun i => rfl
  have hρ : ∀ σ v, (LinearMap.id : UnitRaw.Vfull (n + 2) →ₗ[UnitRaw.F] UnitRaw.Vfull (n + 2))
      (UnitRaw.permHomQ (n + 2) σ v) =
      UnitRaw.permEquivQ (n + 2) σ
        ((LinearMap.id : UnitRaw.Vfull (n + 2) →ₗ[UnitRaw.F] UnitRaw.Vfull (n + 2)) v) := by
    intro σ v
    rw [UnitRaw.permHomQ_apply]
    rfl
  obtain ⟨W, hparabA, hparabB, hkerA, hkerB, hleaf⟩ :=
    @chainA_model (n + 2) n hn ((unitFullEntry (n + 2)).V)
      ((unitFullEntry (n + 2)).instAddCommGroup) ((unitFullEntry (n + 2)).instModule)
      (LinearMap.id) (fun a b hab => hab) (UnitRaw.permHomQ (n + 2)) hρ c c.injective h hh
  refine ⟨W, ?_, ?_, ?_, ?_, hleaf⟩
  · change W.toLin.parab {i | i ≠ W.a} = UnitRaw.normalizerOf (Finset.univ.erase m)
    rw [UnitRaw.normalizerOf]
    have h := hparabA
    rw [himgA] at h
    change W.toLin.parab {i | i ≠ W.a} = Subgroup.closure
      {T | ∃ i ∈ Finset.univ.erase m, ∃ j ∈ Finset.univ.erase m,
        T = UnitRaw.permHomQ (n + 2) (Equiv.swap i j)}
    exact h
  · change W.toLin.parab {i | i ≠ W.b} = UnitRaw.normalizerOf (Finset.univ.erase m')
    rw [UnitRaw.normalizerOf]
    have h := hparabB
    rw [himgB] at h
    change W.toLin.parab {i | i ≠ W.b} = Subgroup.closure
      {T | ∃ i ∈ Finset.univ.erase m', ∃ j ∈ Finset.univ.erase m',
        T = UnitRaw.permHomQ (n + 2) (Equiv.swap i j)}
    exact h
  · intro v
    change (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔
      v ∈ Submodule.span UnitRaw.F {vx}
    rw [← hA, ← himgA]
    exact hkerA v
  · intro v
    change (∀ i ∈ {i | i ≠ W.b}, W.root i v = 0) ↔
      v ∈ Submodule.span UnitRaw.F {z}
    rw [← hB, ← himgB]
    exact hkerB v

theorem unitHeart_inLLeafAt_compl {n : ℕ} (hn : 1 ≤ n) {m₁ m₂ m₃ : Fin (n + 3)}
    (h12 : m₁ ≠ m₂) (h13 : m₁ ≠ m₃) (h23 : m₂ ≠ m₃) {vx z : ↥(UnitRaw.heart (n + 3))}
    (hA : UnitRaw.centH ({m₁, m₂}ᶜ : Finset (Fin (n + 3))) = Submodule.span UnitRaw.F {vx})
    (hB : UnitRaw.centH ({m₂, m₃}ᶜ : Finset (Fin (n + 3))) = Submodule.span UnitRaw.F {z}) :
    InLLeafAt (unitHeartEntry (n + 3)) vx z ({m₁, m₂}ᶜ : Finset (Fin (n + 3)))
      ({m₂, m₃}ᶜ : Finset (Fin (n + 3))) := by
  classical
  obtain ⟨p₁, hp1⟩ := Fin.exists_succAbove_eq (x := m₁) (y := m₂) h12
  obtain ⟨p₃, hp3⟩ := Fin.exists_succAbove_eq (x := m₃) (y := m₂) h23.symm
  have hp13 : p₁ ≠ p₃ := by
    intro hab
    rw [hab] at hp1
    exact h13 (hp1.symm.trans hp3)
  have h0last : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro hab
    have := congrArg Fin.val hab
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  obtain ⟨σ, hσ0, hσlast⟩ := gcca_exists_perm_two (a := (0 : Fin (n + 2)))
    (b := Fin.last (n + 1)) (x := p₁) (y := p₃) h0last hp13
  let d : Fin (n + 2) → Fin (n + 3) := fun j => m₂.succAbove (σ j)
  have hd : Function.Injective d := fun a b hab =>
    σ.injective (Fin.succAbove_right_injective hab)
  have himage_succ_univ :
      Finset.image (Fin.succ : Fin (n + 1) → Fin (n + 2)) Finset.univ =
        Finset.univ.erase 0 := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨a, rfl⟩
      simp
    · intro hx
      obtain ⟨a, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hx.1
      exact ⟨a, rfl⟩
  have himage_castSucc_univ :
      Finset.image (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) Finset.univ =
        Finset.univ.erase (Fin.last (n + 1)) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨a, rfl⟩
      simp
    · intro hx
      obtain ⟨a, rfl⟩ := Fin.eq_castSucc_of_ne_last hx.1
      exact ⟨a, rfl⟩
  have himage_univ : Finset.image σ Finset.univ = Finset.univ := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => σ.surjective x⟩
  have himage_σ_succ : Finset.image (σ ∘ Fin.succ) Finset.univ = Finset.univ.erase p₁ := by
    rw [Finset.image_comp, himage_succ_univ, Finset.image_erase σ.injective, himage_univ, hσ0]
  have himage_σ_castSucc : Finset.image (σ ∘ Fin.castSucc) Finset.univ =
      Finset.univ.erase p₃ := by
    rw [Finset.image_comp, himage_castSucc_univ, Finset.image_erase σ.injective, himage_univ,
      hσlast]
  have himgA : Finset.univ.image (d ∘ Fin.succ) = ({m₁, m₂}ᶜ : Finset (Fin (n + 3))) := by
    have hcomp : d ∘ Fin.succ = (fun x => m₂.succAbove x) ∘ (σ ∘ Fin.succ) := rfl
    rw [hcomp, Finset.image_comp, himage_σ_succ]
    rw [Finset.image_erase (Fin.succAbove_right_injective (p := m₂)),
      Fin.image_succAbove_univ m₂, hp1]
    ext x
    simp only [Finset.mem_erase, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have himgB : Finset.univ.image (d ∘ Fin.castSucc) = ({m₂, m₃}ᶜ : Finset (Fin (n + 3))) := by
    have hcomp : d ∘ Fin.castSucc = (fun x => m₂.succAbove x) ∘ (σ ∘ Fin.castSucc) := rfl
    rw [hcomp, Finset.image_comp, himage_σ_castSucc]
    rw [Finset.image_erase (Fin.succAbove_right_injective (p := m₂)),
      Fin.image_succAbove_univ m₂, hp3]
    ext x
    simp only [Finset.mem_erase, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
    tauto
  let h : Fin (n + 1) → ↥(UnitRaw.heart (n + 3)) := fun i =>
    ⟨(UnitRaw.oneLine (n + 3)).mkQ
        (Pi.single (d i.castSucc) 1 - Pi.single (d i.succ) 1),
      UnitRaw.mkQ_single_sub_single_mem_heart (n + 3) (d i.castSucc) (d i.succ)⟩
  have hh : ∀ i, (UnitRaw.heart (n + 3)).subtype (h i) =
      (UnitRaw.oneLine (n + 3)).mkQ
        (Pi.single (d i.castSucc) 1 - Pi.single (d i.succ) 1) := fun i => rfl
  have hπ : Function.Injective (UnitRaw.heart (n + 3)).subtype :=
    fun a b hab => Subtype.ext hab
  have hρ : ∀ σ v, (UnitRaw.heart (n + 3)).subtype (UnitRaw.permHomH (n + 3) σ v) =
      UnitRaw.permEquivQ (n + 3) σ ((UnitRaw.heart (n + 3)).subtype v) := by
    intro σ v
    rw [UnitRaw.permHomH_apply]
    exact UnitRaw.coe_permEquivH (n + 3) σ v
  obtain ⟨W, hparabA, hparabB, hkerA, hkerB, hleaf⟩ :=
    @chainA_model (n + 3) n hn ((unitHeartEntry (n + 3)).V)
      ((unitHeartEntry (n + 3)).instAddCommGroup) ((unitHeartEntry (n + 3)).instModule)
      (UnitRaw.heart (n + 3)).subtype hπ (UnitRaw.permHomH (n + 3)) hρ d hd h hh
  refine ⟨W, ?_, ?_, ?_, ?_, hleaf⟩
  · change W.toLin.parab {i | i ≠ W.a} =
      UnitRaw.normalizerOfH ({m₁, m₂}ᶜ : Finset (Fin (n + 3)))
    rw [UnitRaw.normalizerOfH]
    have h := hparabA
    rw [himgA] at h
    change W.toLin.parab {i | i ≠ W.a} = Subgroup.closure
      {T | ∃ i ∈ ({m₁, m₂}ᶜ : Finset (Fin (n + 3))),
        ∃ j ∈ ({m₁, m₂}ᶜ : Finset (Fin (n + 3))),
        T = UnitRaw.permHomH (n + 3) (Equiv.swap i j)}
    exact h
  · change W.toLin.parab {i | i ≠ W.b} =
      UnitRaw.normalizerOfH ({m₂, m₃}ᶜ : Finset (Fin (n + 3)))
    rw [UnitRaw.normalizerOfH]
    have h := hparabB
    rw [himgB] at h
    change W.toLin.parab {i | i ≠ W.b} = Subgroup.closure
      {T | ∃ i ∈ ({m₂, m₃}ᶜ : Finset (Fin (n + 3))),
        ∃ j ∈ ({m₂, m₃}ᶜ : Finset (Fin (n + 3))),
        T = UnitRaw.permHomH (n + 3) (Equiv.swap i j)}
    exact h
  · intro v
    let v' : ↥(UnitRaw.heart (n + 3)) := v
    change (∀ i ∈ {i | i ≠ W.a}, W.root i v' = 0) ↔
      v' ∈ Submodule.span UnitRaw.F {vx}
    have h1 : (v' ∈ UnitRaw.centH ({m₁, m₂}ᶜ : Finset (Fin (n + 3)))) ↔
        v' ∈ Submodule.span UnitRaw.F {vx} := by
      rw [← hA]
    have h2 : (v' ∈ UnitRaw.centH ({m₁, m₂}ᶜ : Finset (Fin (n + 3)))) ↔
        (v' : UnitRaw.Vfull (n + 3)) ∈
          UnitRaw.cent (Finset.univ.image (d ∘ Fin.succ)) := by
      rw [UnitRaw.mem_centH_iff, ← himgA]
    exact (hkerA v').trans (h2.symm.trans h1)
  · intro v
    let v' : ↥(UnitRaw.heart (n + 3)) := v
    change (∀ i ∈ {i | i ≠ W.b}, W.root i v' = 0) ↔
      v' ∈ Submodule.span UnitRaw.F {z}
    have h1 : (v' ∈ UnitRaw.centH ({m₂, m₃}ᶜ : Finset (Fin (n + 3)))) ↔
        v' ∈ Submodule.span UnitRaw.F {z} := by
      rw [← hB]
    have h2 : (v' ∈ UnitRaw.centH ({m₂, m₃}ᶜ : Finset (Fin (n + 3)))) ↔
        (v' : UnitRaw.Vfull (n + 3)) ∈
          UnitRaw.cent (Finset.univ.image (d ∘ Fin.castSucc)) := by
      rw [UnitRaw.mem_centH_iff, ← himgB]
    exact (hkerB v').trans (h2.symm.trans h1)

theorem unitFullChainLeaf_holds :
    ∀ (n : ℕ), 1 ≤ n → ∀ (m m' : Fin (n + 2)), m ≠ m' → ∀ vx z : UnitRaw.Vfull (n + 2),
      UnitRaw.cent (Finset.univ.erase m) = Submodule.span UnitRaw.F {vx} →
      UnitRaw.cent (Finset.univ.erase m') = Submodule.span UnitRaw.F {z} →
      InLLeafAt (unitFullEntry (n + 2)) vx z (Finset.univ.erase m) (Finset.univ.erase m') := by
  intro n hn m m' hmm' vx z hA hB
  exact unitFull_inLLeafAt_erase hn hmm' hA hB

theorem unitHeartChainLeaf_holds :
    ∀ (n : ℕ), 1 ≤ n → ∀ (m₁ m₂ m₃ : Fin (n + 3)), m₁ ≠ m₂ → m₁ ≠ m₃ → m₂ ≠ m₃ →
      ∀ vx z : ↥(UnitRaw.heart (n + 3)),
      UnitRaw.centH ({m₁, m₂}ᶜ : Finset (Fin (n + 3))) = Submodule.span UnitRaw.F {vx} →
      UnitRaw.centH ({m₂, m₃}ᶜ : Finset (Fin (n + 3))) = Submodule.span UnitRaw.F {z} →
      InLLeafAt (unitHeartEntry (n + 3)) vx z ({m₁, m₂}ᶜ : Finset (Fin (n + 3)))
        ({m₂, m₃}ᶜ : Finset (Fin (n + 3))) := by
  intro n hn m₁ m₂ m₃ h12 h13 h23 vx z hA hB
  exact unitHeart_inLLeafAt_compl hn h12 h13 h23 hA hB

theorem unitFull_commonWitness_erase {n : ℕ} (hn : 1 ≤ n) {m m' : Fin (n + 2)} (hmm' : m ≠ m')
    {vx z : UnitRaw.Vfull (n + 2)}
    (hA : UnitRaw.cent (Finset.univ.erase m) = Submodule.span UnitRaw.F {vx})
    (hB : UnitRaw.cent (Finset.univ.erase m') = Submodule.span UnitRaw.F {z}) :
    CommonWitness (unitFullEntry (n + 2)) vx z (Finset.univ.erase m) (Finset.univ.erase m') := by
  obtain ⟨W, h1, h2, h3, h4, -⟩ := unitFull_inLLeafAt_erase hn hmm' hA hB
  exact ⟨W, h1, h2, h3, h4⟩

theorem unitHeart_commonWitness_compl {n : ℕ} (hn : 1 ≤ n) {m₁ m₂ m₃ : Fin (n + 3)}
    (h12 : m₁ ≠ m₂) (h13 : m₁ ≠ m₃) (h23 : m₂ ≠ m₃) {vx z : ↥(UnitRaw.heart (n + 3))}
    (hA : UnitRaw.centH ({m₁, m₂}ᶜ : Finset (Fin (n + 3))) = Submodule.span UnitRaw.F {vx})
    (hB : UnitRaw.centH ({m₂, m₃}ᶜ : Finset (Fin (n + 3))) = Submodule.span UnitRaw.F {z}) :
    CommonWitness (unitHeartEntry (n + 3)) vx z ({m₁, m₂}ᶜ : Finset (Fin (n + 3)))
      ({m₂, m₃}ᶜ : Finset (Fin (n + 3))) := by
  obtain ⟨W, h1, h2, h3, h4, -⟩ := unitHeart_inLLeafAt_compl hn h12 h13 h23 hA hB
  exact ⟨W, h1, h2, h3, h4⟩

end CFSG.StandardType.GGQ2Frame

end
