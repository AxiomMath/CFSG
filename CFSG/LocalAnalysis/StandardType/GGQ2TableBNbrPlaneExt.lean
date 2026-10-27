module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogue
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChainGroups
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneCutThree
import CFSG.Mathlib.Perm.ChainSwap

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private theorem tbnpe_four_le_card {t : ℕ} (k : PlaneRaw.PlaneKind) {e : PlaneRaw.V t}
    (he : e ≠ 0)
    (hcod : 3 + Module.finrank (ZMod 3) (PlaneRaw.cent k (PlaneRaw.Code.extension e)) ≤
      Module.finrank (ZMod 3) (PlaneRaw.V t)) :
    4 ≤ (PlaneRaw.Code.extSupport e).card := by
  have hV : Module.finrank (ZMod 3) (PlaneRaw.V t) = t := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [hV, PlaneRaw.finrank_cent_extension k e he] at hcod
  have hle := Finset.card_le_univ (PlaneRaw.Code.extSupport e)
  omega

private theorem tbnpe_sq {a : PlaneRaw.F} (ha : a ≠ 0) : a * a = 1 := by
  revert a
  decide

private theorem tbnpe_castSucc_ne_succ {n : ℕ} (i : Fin n) : i.castSucc ≠ i.succ := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at h'
  omega

private theorem tbnpe_chain_const {n : ℕ} {α : Type*} {c : Fin (n + 1) → α}
    {w : α → PlaneRaw.F} (h : ∀ κ : Fin n, w (c κ.castSucc) = w (c κ.succ))
    (p q : Fin (n + 1)) : w (c p) = w (c q) := by
  have h0 : ∀ p : Fin (n + 1), w (c p) = w (c 0) := by
    intro p
    induction p using Fin.induction with
    | zero => rfl
    | succ i ih => rw [← h i, ih]
  rw [h0 p, h0 q]

private def tbnpeCoroot (t n : ℕ) (e : PlaneRaw.V t) (c : Fin (n + 1) → Fin t) :
    Fin n → PlaneRaw.V t := fun x =>
  e (c x.castSucc) • Pi.single (c x.castSucc) 1 -
    e (c x.succ) • Pi.single (c x.succ) 1

private def tbnpeRoot (t n : ℕ) (e : PlaneRaw.V t) (c : Fin (n + 1) → Fin t) :
    Fin n → Dual (ZMod 3) (PlaneRaw.V t) := fun x =>
  e (c x.castSucc) • PlaneRaw.coordProj (c x.castSucc) -
    e (c x.succ) • PlaneRaw.coordProj (c x.succ)

private theorem tbnpeCoroot_apply {t n : ℕ} {e : PlaneRaw.V t} {c : Fin (n + 1) → Fin t}
    (y : Fin n) (i : Fin t) :
    tbnpeCoroot t n e c y i =
      (if i = c y.castSucc then e (c y.castSucc) else 0) -
        (if i = c y.succ then e (c y.succ) else 0) := by
  by_cases ha : i = c y.castSucc <;> by_cases hb : i = c y.succ <;>
    simp [tbnpeCoroot, ha, hb, Pi.single_apply]

private theorem tbnpeRoot_apply {t n : ℕ} {e : PlaneRaw.V t} {c : Fin (n + 1) → Fin t}
    (x : Fin n) (v : PlaneRaw.V t) :
    tbnpeRoot t n e c x v =
      e (c x.castSucc) * v (c x.castSucc) - e (c x.succ) * v (c x.succ) := by
  simp [tbnpeRoot, PlaneRaw.coordProj_apply, smul_eq_mul]

private theorem tbnpe_pairing {t n : ℕ} {e : PlaneRaw.V t} {c : Fin (n + 1) → Fin t}
    (hc : Function.Injective c) (he : ∀ κ, e (c κ) ≠ 0) (x y : Fin n) :
    tbnpeRoot t n e c x (tbnpeCoroot t n e c y) = (CartanMatrix.A n x y : PlaneRaw.F) := by
  have hcc : (c x.castSucc = c y.castSucc) ↔ x = y := by
    rw [hc.eq_iff, Fin.castSucc_inj]
  have hss : (c x.succ = c y.succ) ↔ x = y := by
    rw [hc.eq_iff, Fin.succ_inj]
  have hsc : (c x.succ = c y.castSucc) ↔ x.val + 1 = y.val := by
    rw [hc.eq_iff, Fin.ext_iff]
    simp only [Fin.val_succ, Fin.val_castSucc]
  have hcs : (c x.castSucc = c y.succ) ↔ y.val + 1 = x.val := by
    rw [hc.eq_iff, Fin.ext_iff]
    simp only [Fin.val_succ, Fin.val_castSucc]
    constructor <;> omega
  rw [tbnpeRoot_apply, tbnpeCoroot_apply, tbnpeCoroot_apply]
  simp only [hcc, hss, hsc, hcs]
  rcases lt_trichotomy (x : ℕ) (y : ℕ) with hlt | heq | hgt
  · have hxy : x ≠ y := fun h => by have := congrArg Fin.val h; omega
    have hcsf : ¬ (y.val + 1 = x.val) := by omega
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with hsucc | hsucc
    · have hsucc' : x.val + 1 = y.val := hsucc
      have hsc' : c y.castSucc = c x.succ := by
        rw [hc.eq_iff, Fin.ext_iff]
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      simp [CartanMatrix.A, hxy, hsucc', hcsf, hsc', tbnpe_sq (he x.succ)]
    · have hscf : ¬ (x.val + 1 = y.val) := by omega
      simp [CartanMatrix.A, hxy, hscf, hcsf]
  · have hxy : x = y := Fin.ext heq
    subst hxy
    simp [CartanMatrix.A, tbnpe_sq (he x.castSucc), tbnpe_sq (he x.succ)]
    norm_num
  · have hxy : x ≠ y := fun h => by have := congrArg Fin.val h; omega
    have hscf : ¬ (x.val + 1 = y.val) := by omega
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with hsucc | hsucc
    · have hsucc' : y.val + 1 = x.val := hsucc
      have hcs' : c y.succ = c x.castSucc := by
        rw [hc.eq_iff, Fin.ext_iff]
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      simp [CartanMatrix.A, hxy, hsucc', hscf, hcs', tbnpe_sq (he x.castSucc)]
    · have hcsf : ¬ (y.val + 1 = x.val) := by omega
      simp [CartanMatrix.A, hxy, hscf, hcsf]

private theorem tbnpe_refl_apply {t n : ℕ} {e : PlaneRaw.V t} {c : Fin (n + 1) → Fin t}
    (hc : Function.Injective c) (he : ∀ κ, e (c κ) ≠ 0) (x : Fin n) (v : PlaneRaw.V t) :
    PlaneRaw.swapTwist t e (c x.castSucc) (c x.succ) v =
      v - tbnpeRoot t n e c x v • tbnpeCoroot t n e c x := by
  have hne : c x.castSucc ≠ c x.succ := fun h => tbnpe_castSucc_ne_succ x (hc h)
  ext k
  rw [PlaneRaw.swapTwist_apply (he x.castSucc) (he x.succ), Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, tbnpeRoot_apply, tbnpeCoroot_apply]
  by_cases hka : k = c x.castSucc
  · subst hka
    simp only [if_neg hne, if_true]
    ring_nf
    rw [pow_two, tbnpe_sq (he x.castSucc)]
    ring
  · by_cases hkb : k = c x.succ
    · subst hkb
      simp only [if_neg hka, if_true]
      ring_nf
      rw [pow_two, tbnpe_sq (he x.succ)]
      ring
    · simp only [if_neg hka, if_neg hkb]
      ring

private theorem tbnpe_root_zero_iff {t n : ℕ} {e : PlaneRaw.V t} {c : Fin (n + 1) → Fin t}
    (hrange : ∀ i : Fin t, (∃ κ, c κ = i) ↔ i ∈ PlaneRaw.Code.extSupport e)
    (v : PlaneRaw.V t) :
    (∀ x : Fin n, tbnpeRoot t n e c x v = 0) ↔ v ∈ PlaneRaw.centExt e := by
  constructor
  · intro h i hi j hj
    obtain ⟨p, rfl⟩ := (hrange i).mpr (by simpa using hi)
    obtain ⟨q, rfl⟩ := (hrange j).mpr (by simpa using hj)
    have hstep : ∀ κ : Fin n,
        e (c κ.castSucc) * v (c κ.castSucc) = e (c κ.succ) * v (c κ.succ) := by
      intro κ
      have := h κ
      rw [tbnpeRoot_apply] at this
      exact sub_eq_zero.mp this
    exact tbnpe_chain_const (c := c) (w := fun i => e i * v i) hstep p q
  · intro hv x
    rw [tbnpeRoot_apply, sub_eq_zero]
    exact (PlaneRaw.mem_centExt e v).mp hv _ ((hrange _).mp ⟨x.castSucc, rfl⟩)
      _ ((hrange _).mp ⟨x.succ, rfl⟩)

private theorem tbnpe_funCongrLeft_mul (t : ℕ) (σ τ : Equiv.Perm (Fin t)) :
    LinearEquiv.funCongrLeft PlaneRaw.F PlaneRaw.F (σ * τ) =
      LinearEquiv.funCongrLeft PlaneRaw.F PlaneRaw.F τ *
        LinearEquiv.funCongrLeft PlaneRaw.F PlaneRaw.F σ := by
  ext v i
  simp [LinearEquiv.mul_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Equiv.Perm.mul_def]

private def tbnpe_permHom (t : ℕ) (e : PlaneRaw.V t) :
    Equiv.Perm (Fin t) →* (PlaneRaw.V t ≃ₗ[PlaneRaw.F] PlaneRaw.V t) where
  toFun σ := (PlaneRaw.orientEquiv t e)⁻¹ *
    LinearEquiv.funCongrLeft PlaneRaw.F PlaneRaw.F σ⁻¹ * PlaneRaw.orientEquiv t e
  map_one' := by
    rw [inv_one, show (1 : Equiv.Perm (Fin t)) = Equiv.refl (Fin t) from rfl,
      LinearEquiv.funCongrLeft_id]
    rw [show LinearEquiv.refl PlaneRaw.F (Fin t → PlaneRaw.F) = 1 from rfl]
    group
  map_mul' σ τ := by
    rw [show (σ * τ)⁻¹ = τ⁻¹ * σ⁻¹ from mul_inv_rev σ τ, tbnpe_funCongrLeft_mul]
    group

private theorem tbnpe_permHom_swap (t : ℕ) (e : PlaneRaw.V t) (i j : Fin t) :
    tbnpe_permHom t e (Equiv.swap i j) = PlaneRaw.swapTwist t e i j := by
  simp [tbnpe_permHom, PlaneRaw.swapTwist, PlaneRaw.swapEquiv, Equiv.swap_inv]

private theorem tbnpe_closure_chainTwist {t n : ℕ} {e : PlaneRaw.V t}
    {c : Fin (n + 1) → Fin t} (hc : Function.Injective c)
    (hrange : ∀ i : Fin t, (∃ κ, c κ = i) ↔ i ∈ PlaneRaw.Code.extSupport e) :
    Subgroup.closure (Set.range fun κ : Fin n =>
      PlaneRaw.swapTwist t e (c κ.castSucc) (c κ.succ)) =
      PlaneRaw.twistedPermGroupOn t e := by
  have he : ∀ κ, e (c κ) ≠ 0 := fun κ =>
    (PlaneRaw.mem_extSupport e (c κ)).mp ((hrange _).mp ⟨κ, rfl⟩)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨κ, rfl⟩
    exact Subgroup.subset_closure ⟨_, _, he _, he _, rfl⟩
  · rw [PlaneRaw.twistedPermGroupOn, Subgroup.closure_le]
    rintro _ ⟨i, j, hi, hj, rfl⟩
    obtain ⟨p, rfl⟩ := (hrange i).mpr (by simpa using hi)
    obtain ⟨q, rfl⟩ := (hrange j).mpr (by simpa using hj)
    have h := CFSG.Perm.map_swap_mem_closure_chainSwap (tbnpe_permHom t e) hc p q
    have hset : (Set.range fun κ : Fin n =>
        tbnpe_permHom t e (Equiv.swap (c κ.castSucc) (c κ.succ))) =
        Set.range fun κ : Fin n => PlaneRaw.swapTwist t e (c κ.castSucc) (c κ.succ) := by
      ext σ
      simp only [Set.mem_range]
      constructor
      · rintro ⟨κ, rfl⟩
        exact ⟨κ, (tbnpe_permHom_swap t e _ _).symm⟩
      · rintro ⟨κ, rfl⟩
        exact ⟨κ, tbnpe_permHom_swap t e _ _⟩
    rw [hset] at h
    exact h

private theorem tbnpe_datum_A (k : PlaneRaw.PlaneKind) (t : ℕ) (e : PlaneRaw.V t)
    (hm : 4 ≤ (PlaneRaw.Code.extSupport e).card) :
    Nonempty (CodeWeylDatum (planeEntry k t) (PlaneRaw.Code.extension e)) := by
  classical
  let T := PlaneRaw.Code.extSupport e
  have hm' : 4 ≤ T.card := hm
  let n := T.card - 1
  have hn1 : 1 ≤ n := by omega
  have hcard : n + 1 = T.card := by omega
  let c : Fin (n + 1) → Fin t := fun i => T.orderEmbOfFin rfl (Fin.cast hcard i)
  have hc : Function.Injective c := by
    intro i j hij
    have h1 : Fin.cast hcard i = Fin.cast hcard j := (T.orderEmbOfFin rfl).injective hij
    exact Fin.cast_injective hcard h1
  have hrange : ∀ i : Fin t, (∃ κ, c κ = i) ↔ i ∈ T := by
    intro i
    constructor
    · rintro ⟨κ, rfl⟩
      exact T.orderEmbOfFin_mem rfl _
    · intro hi
      have hmem : i ∈ Set.range (T.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin T rfl]
        exact hi
      obtain ⟨a, rfl⟩ := hmem
      refine ⟨Fin.cast hcard.symm a, ?_⟩
      have hcast : Fin.cast hcard (Fin.cast hcard.symm a) = a := by
        ext
        simp
      show T.orderEmbOfFin rfl (Fin.cast hcard (Fin.cast hcard.symm a)) =
        T.orderEmbOfFin rfl a
      rw [hcast]
  have hcne : ∀ κ : Fin (n + 1), e (c κ) ≠ 0 := fun κ =>
    (PlaneRaw.mem_extSupport e (c κ)).mp ((hrange (c κ)).mp ⟨κ, rfl⟩)
  refine ⟨{ ι := Fin n
            coxeter := CoxeterMatrix.A n
            cartan := CartanMatrix.A n
            coroot := tbnpeCoroot t n e c
            root := tbnpeRoot t n e c
            isWeyl := Or.inl ⟨n, Equiv.refl _, hn1, Or.inl rfl⟩
            isCartan := ggIntCartan_A n
            pairing := fun x y => tbnpe_pairing hc hcne x y
            refl := fun x => PlaneRaw.swapTwist t e (c x.castSucc) (c x.succ)
            refl_apply := fun x v => tbnpe_refl_apply hc hcne x v
            closure_refl := tbnpe_closure_chainTwist hc hrange
            ker_iff := fun v => tbnpe_root_zero_iff hrange v }⟩

theorem planeExt_codeWeylDatum (k : PlaneRaw.PlaneKind) (t : ℕ) (e : PlaneRaw.V t)
    (hadm : (planeEntry k t).admissible (PlaneRaw.Code.extension e))
    (hcod : 3 + finrank (ZMod 3) ((planeEntry k t).cent (PlaneRaw.Code.extension e)) ≤
      finrank (ZMod 3) (planeEntry k t).V) :
    Nonempty (CodeWeylDatum (planeEntry k t) (PlaneRaw.Code.extension e)) := by
  have he : e ≠ 0 := hadm.2.1
  unfold planeEntry at hcod
  change 3 + Module.finrank (ZMod 3) (PlaneRaw.cent k (PlaneRaw.Code.extension e)) ≤
    Module.finrank (ZMod 3) (PlaneRaw.V t) at hcod
  exact tbnpe_datum_A k t e (tbnpe_four_le_card k he hcod)

end

end CFSG.StandardType.GGQ2Frame

end
