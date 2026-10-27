module

public import CFSG.RankThree.CentralLiftSO.SymplecticTriangular
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.RankThree.CentralLift.LinearSplitting

public section

namespace CFSG.RankThree.CentralLift

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.CentralExt
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (liftTorus liftWeyl sLift hLift
  lamLift lam signedPermGroup IsLinePerm isLinePerm_signedPerm)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent borelSubgroup flagOrder
  mem_borelSubgroup_iff_reindex dotW coe_dotW)
open CFSG.RankThree.CentralLiftSO.Sp (LargeHyp etaS etaSLift xPlus xMinus dLift simpleKer
  simpleKer_le_unipotent isPGroup_unipotent weylHom isLinePerm_weylHom weylHom_surjective
  ker_weylHom normal_liftTorus_subgroupOf
  odd_symplectic_cross_characteristic_central_prime_triangular_factorization)
open CFSG.LieType.Chevalley (uSL vSL)
open scoped Pointwise

variable {r : ℕ} {k : Type} [Field k]

theorem eq_one_of_isLinePerm_of_mem_borel {g : StatedSp r k} {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (hσ : IsLinePerm σ ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k))
    (hg : g ∈ borelSubgroup r k) : σ = 1 := by
  have hup := mem_borelSubgroup_iff_reindex.1 hg
  have hle : ∀ x, flagOrder r (σ x) ≤ flagOrder r x := by
    intro x
    by_contra hlt
    apply hσ.apply_ne_zero x
    have h0 := hup (not_le.1 hlt)
    simpa only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply] using h0
  have h1 : ((flagOrder r).symm.trans σ).trans (flagOrder r) = 1 :=
    LinearRoots.perm_eq_one_of_forall_le fun a => by
      have := hle ((flagOrder r).symm a)
      simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using this
  ext x
  have h2 := congrArg (fun τ : Equiv.Perm (Fin (2 * r)) => τ (flagOrder r x)) h1
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.one_apply] at h2
  rw [Equiv.Perm.one_apply, (flagOrder r).injective h2]

theorem mem_borel_of_isLinePerm_one {g : StatedSp r k}
    (hg : IsLinePerm 1 ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)) :
    g ∈ borelSubgroup r k := by
  rw [mem_borelSubgroup_iff_reindex]
  intro i j hij
  simp only [reindex_apply, submatrix_apply]
  refine hg.apply_eq_zero ?_
  rw [Equiv.Perm.one_apply]
  intro h
  exact hij.ne' ((flagOrder r).symm.injective h)

variable [Finite k] {E : Type*} [Group E] [Finite E] {π : E →* StatedSp r k}

@[expose] noncomputable def vSLHom : Multiplicative k →* SpecialLinearGroup (Fin 2) k where
  toFun a := vSL a.toAdd
  map_one' := CFSG.RankThree.CentralLiftSO.Sp.vSL_zero
  map_mul' a b := CFSG.RankThree.CentralLiftSO.Sp.vSL_add a.toAdd b.toAdd

theorem sup_map_eq_top (hS : LargeHyp π) {B : Subgroup E} (hBmap : B.map π = borelSubgroup r k) :
    B.map π ⊔ (liftWeyl π).map π = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨w, hw⟩ := (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.symplectic_bruhat
    (r := r) (K := k)).1 g
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hw
  obtain ⟨n, hn⟩ := weylHom_surjective hS w
  have hσn := isLinePerm_weylHom hS n
  rw [hn] at hσn
  have hσw : IsLinePerm (w : Equiv.Perm (Fin r ⊕ Fin r))
      (((dotW k w : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := by
    rw [coe_dotW]
    exact isLinePerm_signedPerm _ fun x =>
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.dotSign_ne_zero _ x
  have hd : (dotW k w)⁻¹ * π n ∈ borelSubgroup r k := by
    refine mem_borel_of_isLinePerm_one ?_
    have h := (hσw.inv).mul hσn
    rw [inv_mul_cancel] at h
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    exact h
  have he : dotW k w = π n * ((dotW k w)⁻¹ * π n)⁻¹ := by group
  refine mul_mem (mul_mem (Subgroup.mem_sup_left (hBmap ▸ hb₁)) ?_)
    (Subgroup.mem_sup_left (hBmap ▸ hb₂))
  rw [he]
  exact mul_mem (Subgroup.mem_sup_right ⟨n, n.2, rfl⟩)
    (inv_mem (Subgroup.mem_sup_left (hBmap ▸ hd)))

theorem symplectic_cross_splitting {p ℓ f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hpℓ : p ≠ ℓ) (_hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f) (hr : 1 ≤ r)
    (π : E →* StatedSp r k) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup p π.ker) :
    (∃! s : StatedSp r k →* E, π.comp s = MonoidHom.id _) ∧
      ∀ s : StatedSp r k →* E, π.comp s = MonoidHom.id _ →
        ∃ e : π.ker × s.range ≃* E, ∀ c g, e (c, g) = (c : E) * g := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP k ℓ := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hk])
  have hchar : ringChar k = ℓ := ringChar.eq k ℓ
  have hk2 : ringChar k ≠ 2 := by
    rw [hchar]
    exact hℓodd.ne_two_of_dvd_nat (dvd_refl ℓ)
  have : Fact (ringChar k).Prime := ⟨hchar ▸ hℓ⟩
  have hpℓ' : p ≠ ringChar k := hchar ▸ hpℓ
  have hS : LargeHyp π := ⟨hk2, ⟨hπ, hC, ⟨p, hp, hp3, hCp⟩⟩⟩
  have hCℓ : ¬ringChar k ∣ Nat.card π.ker := by
    obtain ⟨m, hm⟩ := hCp.exists_card_dvd_pow
    intro hdvd
    exact hpℓ' ((Nat.prime_dvd_prime_iff_eq (hchar ▸ hℓ) hp).1
      ((hchar ▸ hℓ).dvd_of_dvd_pow (hdvd.trans hm))).symm
  obtain ⟨-, hTN, hBmem, hBmap, hBinj, hsimple⟩ :=
    odd_symplectic_cross_characteristic_central_prime_triangular_factorization hk2 hr hp hp3 hpℓ'
      hπ hC hCp
  set U := liftSubgroup (ringChar k) π (unipotent r k) with hU
  set B := U ⊔ liftTorus π with hBdef
  let Xp : Fin r → Subgroup E := fun i => ((etaSLift π i).comp LinearRoots.uSLHom).range
  let Xm : Fin r → Subgroup E := fun i => ((etaSLift π i).comp vSLHom).range
  let Ui : Fin r → Subgroup E := fun i => liftSubgroup (ringChar k) π (simpleKer r k i)
  have hmemXp : ∀ i x, x ∈ Xp i ↔ ∃ t : k, xPlus π i t = x := fun i x =>
    ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
  have hmemXm : ∀ i x, x ∈ Xm i ↔ ∃ t : k, xMinus π i t = x := fun i x =>
    ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
  have hBset : (B : Set E) = (U : Set E) * (liftTorus π : Set E) := by
    ext x
    rw [SetLike.mem_coe, hBmem x, Set.mem_mul]
    constructor
    · rintro ⟨u, hu, h, hh, rfl⟩
      exact ⟨u, hu, h, hh, rfl⟩
    · rintro ⟨u, hu, h, hh, rfl⟩
      exact ⟨u, hu, h, hh, rfl⟩
  have hInj : Set.InjOn π (B : Set E) := fun x hx y hy hxy =>
    congrArg Subtype.val (hBinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hfact : ∀ i, (B : Set E) = (Xp i : Set E) * (Ui i : Set E) * (liftTorus π : Set E) := by
    intro i
    ext x
    rw [SetLike.mem_coe, ((hsimple i).2.2.2.2.1) x]
    constructor
    · rintro ⟨t, u, hu, h, hh, rfl⟩
      exact ⟨_, ⟨_, (hmemXp i _).2 ⟨t, rfl⟩, u, hu, rfl⟩, h, hh, rfl⟩
    · rintro ⟨_, ⟨y, hy, u, hu, rfl⟩, h, hh, rfl⟩
      obtain ⟨t, rfl⟩ := (hmemXp i y).1 hy
      exact ⟨t, u, hu, h, hh, rfl⟩
  have hXpU : ∀ i, Xp i ≤ U := fun i x hx => by
    obtain ⟨t, rfl⟩ := (hmemXp i x).1 hx
    exact CFSG.RankThree.CentralLiftSO.Sp.xPlus_mem_liftUnipotent hS i t
  have hUiU : ∀ i, Ui i ≤ U := fun i =>
    CFSG.RankThree.CentralLiftSO.Sp.liftSubgroup_mono hC isPGroup_unipotent
      (simpleKer_le_unipotent i)
  have hconj : ∀ i, ∀ u ∈ Ui i, (sLift π i)⁻¹ * u * sLift π i ∈ U := by
    intro i u hu
    have hn := (hsimple i).2.2.2.2.2.1
    have hn' : (sLift π i)⁻¹ ∈ Subgroup.normalizer (Ui i : Set E) := inv_mem hn
    have h := (Subgroup.mem_normalizer_iff.1 hn' u).1 hu
    rw [inv_inv] at h
    exact hUiU i h
  have hrew : ∀ i, ∀ x ∈ Xp i, x ≠ 1 → x * sLift π i ∈
      (Xm i : Set E) * (liftTorus π : Set E) * (Xp i : Set E) := by
    intro i x hx hx1
    obtain ⟨t, rfl⟩ := (hmemXp i x).1 hx
    have ht : t ≠ 0 := by
      rintro rfl
      apply hx1
      change etaSLift π i (uSL 0) = 1
      rw [LinearRoots.uSL_zero, map_one]
    rw [(hsimple i).2.2.2.2.2.2.2.1 t ht]
    exact ⟨_, ⟨_, (hmemXm i _).2 ⟨t⁻¹, rfl⟩, _, (hsimple i).2.2.2.2.2.2.2.2.1 _, rfl⟩, _,
      (hmemXp i _).2 ⟨-t⁻¹, rfl⟩, rfl⟩
  have hsign : ∀ n ∈ liftWeyl π, ∀ i, (∀ x ∈ Xp i, n * x * n⁻¹ ∈ U) ∨
      (∀ y ∈ Xm i, n * y * n⁻¹ ∈ U) := by
    intro n hn i
    rcases (hsimple i).2.2.2.2.2.2.2.2.2 n hn with h | h
    · left
      intro x hx
      obtain ⟨t, rfl⟩ := (hmemXp i x).1 hx
      exact h t
    · right
      intro y hy
      obtain ⟨t, rfl⟩ := (hmemXm i y).1 hy
      exact h t
  have hBN : ∀ n ∈ liftWeyl π, π n ∈ B.map π → n ∈ liftTorus π := by
    intro n hn hnB
    rw [hBmap] at hnB
    have h1 := eq_one_of_isLinePerm_of_mem_borel (isLinePerm_weylHom hS ⟨n, hn⟩) hnB
    have h2 : (⟨n, hn⟩ : liftWeyl π) ∈ (weylHom hS).ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h1
    rw [ker_weylHom hS] at h2
    exact Subgroup.mem_subgroupOf.1 h2
  have hgen := sup_map_eq_top hS hBmap
  obtain ⟨-, -, σ, hσ⟩ :=
    CFSG.RankThree.CentralExtension.central_extension_faithful_bruhat_lift_splitting π hC hBset
      hInj (normal_liftTorus_subgroupOf hS) (sLift π) rfl
      (CFSG.RankThree.CentralLiftSO.Sp.sLift_sq_mem hS) Xp Xm Ui hXpU hfact hconj hrew hsign hBN
      hgen
  refine ⟨⟨σ, hσ, fun σ' hσ' => ?_⟩, fun s hs => LinearRoots.exists_mulEquiv_prod_of_section hC hs⟩
  have hlift : ∀ τ : StatedSp r k →* E, π.comp τ = MonoidHom.id _ →
      ∀ α : SpecialLinearGroup (Fin 2) k →* StatedSp r k, τ.comp α = sl2Lift π α := fun τ hτ α =>
    eq_sl2Lift_large hk2 hS.ext (by rw [← MonoidHom.comp_assoc, hτ, MonoidHom.id_comp])
  have hagree : ⊤ ≤ MonoidHom.eqLocus σ' σ := by
    rw [← hgen]
    refine sup_le ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      have hb' : b ∈ (B : Set E) := hb
      rw [hBset] at hb'
      obtain ⟨u, hu, h, hh, rfl⟩ := hb'
      rw [map_mul]
      refine mul_mem ?_ ?_
      ·
        have hux := (mem_liftSubgroup_iff hC isPGroup_unipotent).1 hu
        have hord : ∀ τ : StatedSp r k →* E, π.comp τ = MonoidHom.id _ →
            ∃ n : ℕ, orderOf (τ (π u)) = ringChar k ^ n := by
          intro τ _
          obtain ⟨n, hn⟩ := hux.2
          exact exists_orderOf_eq_pow_of_pow_eq_one (n := n) (by
            rw [← map_pow, ← map_pow, ← hn, pow_orderOf_eq_one, map_one, map_one])
        exact eq_of_pElement hC hCℓ (by
          rw [← MonoidHom.comp_apply π σ', ← MonoidHom.comp_apply π σ, hσ', hσ])
          (hord σ' hσ') (hord σ hσ)
      ·
        have hle : (liftTorus π).map π ≤ MonoidHom.eqLocus σ' σ := by
          rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.liftTorus,
            MonoidHom.map_closure, Subgroup.closure_le]
          rintro _ ⟨_, ⟨⟨i, a⟩, rfl⟩, rfl⟩
          change σ' (π (lamLift π i _)) = σ (π (lamLift π i _))
          rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.lamLift,
            map_sl2Lift_large hk2 hS.ext]
          rw [← MonoidHom.comp_apply σ' (lam i), ← MonoidHom.comp_apply σ (lam i),
            hlift σ' hσ', hlift σ hσ]
        exact hle ⟨h, hh, rfl⟩
    · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.liftWeyl, MonoidHom.map_closure,
        Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with hx | ⟨i, rfl⟩
      · have hle : (liftTorus π).map π ≤ MonoidHom.eqLocus σ' σ := by
          rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.liftTorus,
            MonoidHom.map_closure, Subgroup.closure_le]
          rintro _ ⟨_, ⟨⟨i, a⟩, rfl⟩, rfl⟩
          change σ' (π (lamLift π i _)) = σ (π (lamLift π i _))
          rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.lamLift,
            map_sl2Lift_large hk2 hS.ext]
          rw [← MonoidHom.comp_apply σ' (lam i), ← MonoidHom.comp_apply σ (lam i),
            hlift σ' hσ', hlift σ hσ]
        exact hle ⟨x, hx, rfl⟩
      · change σ' (π (sLift π i)) = σ (π (sLift π i))
        rw [CFSG.RankThree.CentralLiftSO.Sp.sLift_eq_etaSLift, etaSLift,
          map_sl2Lift_large hk2 hS.ext, ← MonoidHom.comp_apply σ' (etaS k i),
          ← MonoidHom.comp_apply σ (etaS k i), hlift σ' hσ', hlift σ hσ]
  exact MonoidHom.ext fun x => hagree (Subgroup.mem_top x)

end CFSG.RankThree.CentralLift
