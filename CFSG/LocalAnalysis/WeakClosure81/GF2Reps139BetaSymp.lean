module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139BetaE1
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139HAlt
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139HNorm

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {M : Type} [CommGroup M]

private noncomputable def w1369_bilinFormM [Module (ZMod 2) (Additive M)]
    (β : M → M → ZMod 2) (hl : ∀ x x' y, β (x * x') y = β x y + β x' y)
    (hr : ∀ x y y', β x (y * y') = β x y + β x y') :
    LinearMap.BilinForm (ZMod 2) (Additive M) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun u => AddMonoidHom.toZModLinearMap 2
        (AddMonoidHom.mk' (fun v => β u.toMul v.toMul) fun _ _ => hr _ _ _)
      map_zero' := by
        ext v
        change β 1 v.toMul = 0
        have h := hl 1 1 v.toMul
        rw [mul_one] at h
        linear_combination -h
      map_add' := fun _ _ => by
        ext v
        exact hl _ _ _ }

private theorem w1369_perfect_of_isQuasisimple {K : Subgroup (MulAut M)}
    (hKq : IsQuasisimple ↥K) : ⁅K, K⁆ = K := by
  rw [← Subgroup.map_subtype_commutator (H := K), Group.isPerfect_def.mp hKq.1,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem w1369_ne_bot_of_isQuasisimple {K : Subgroup (MulAut M)}
    (hKq : IsQuasisimple ↥K) : K ≠ ⊥ := by
  intro hbot
  have hle : K ≤ ⊥ := le_of_eq hbot
  have hsub : Subsingleton ↥K := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    have ha : (a : MulAut M) = 1 := Subgroup.mem_bot.mp (hle a.2)
    have hb : (b : MulAut M) = 1 := Subgroup.mem_bot.mp (hle b.2)
    rw [ha, hb]
  haveI : Subsingleton (↥K ⧸ Subgroup.center ↥K) := by
    have hc : Subgroup.center ↥K = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subsingleton.elim _ _
    rw [hc]
    exact QuotientGroup.subsingleton_quotient_top
  exact (not_subsingleton_iff_nontrivial.mpr hKq.2.1.toNontrivial) inferInstance

theorem beta_core_no_sympform {M : Type} [CommGroup M] [Finite M]
    (hM2 : ∀ m : M, m ^ 2 = 1) {K D : Subgroup (MulAut M)} (hKq : IsQuasisimple ↥K)
    (hKirr : IsIrrOn K ⊤ ⊥) (hDnorm : ∀ e ∈ D, K.map (MulAut.conj e).toMonoidHom = K)
    (hDel : IsElemAbelian2 D) (hD4 : 4 ≤ Nat.card D) (A : Subgroup M) (hA : rkIdx A = 1)
    (hDtv : ∀ e ∈ D, e ≠ 1 → fixV (Subgroup.zpowers e) = A ∧
      rk ↥(commSub ⊤ (Subgroup.zpowers e)) = 1)
    (hn3 : 3 ≤ rk M) (hB : HasSympForm K) : False := by
  classical
  have hDne : D ≠ ⊥ := fun h => by rw [h] at hD4; simp at hD4
  obtain ⟨e0, he0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have he0mem : (e0 : MulAut M) ∈ D := e0.2
  have he0ne' : (e0 : MulAut M) ≠ 1 := fun h => he0ne (Subtype.ext h)
  have he0_2 : (e0 : MulAut M) ^ 2 = 1 := hDel.2 (e0 : MulAut M) he0mem
  have hN0 : K.map (MulAut.conj (e0 : MulAut M)).toMonoidHom = K :=
    hDnorm (e0 : MulAut M) he0mem
  have hcost0 : rk ↥(commSub ⊤ (Subgroup.zpowers (e0 : MulAut M))) = 1 :=
    (hDtv (e0 : MulAut M) he0mem he0ne').2
  have hKperf : ⁅K, K⁆ = K := w1369_perfect_of_isQuasisimple hKq
  have hK1 : K ≠ ⊥ := w1369_ne_bot_of_isQuasisimple hKq
  letI : Module (ZMod 2) (Additive M) := CFSG.Quasithin.H13.Mult.zmodModuleW hM2
  haveI : Module.Finite (ZMod 2) (Additive M) := Module.Finite.of_finite
  let eL : MulAut M ≃* (Additive M ≃ₗ[ZMod 2] Additive M) :=
    CFSG.Quasithin.H13.Mult.linEquiv
  let Kb : Subgroup (Additive M ≃ₗ[ZMod 2] Additive M) := K.map eL.toMonoidHom
  obtain ⟨B, hBnd, hBalt, hBinv⟩ := hB
  let β : M → M → ZMod 2 := fun x y => (B x y).toAdd
  have hl : ∀ x x' y, β (x * x') y = β x y + β x' y := by
    intro x x' y
    show (B (x * x') y).toAdd = (B x y).toAdd + (B x' y).toAdd
    have h : B (x * x') y = B x y * B x' y := by rw [map_mul B x x']; rfl
    rw [h, toAdd_mul]
  have hr : ∀ x y y', β x (y * y') = β x y + β x y' := by
    intro x y y'
    show (B x (y * y')).toAdd = (B x y).toAdd + (B x y').toAdd
    rw [map_mul (B x) y y', toAdd_mul]
  let b : LinearMap.BilinForm (ZMod 2) (Additive M) := w1369_bilinFormM β hl hr
  have hb_apply : ∀ u v : Additive M, b u v = β u.toMul v.toMul := fun u v => rfl
  have halt : b.IsAlt := by
    intro u
    rw [hb_apply]
    simp only [β]
    rw [hBalt u.toMul, toAdd_one]
  have hrefl : b.IsRefl := halt.isRefl
  have hsep : b.SeparatingLeft := by
    intro u hu
    have h : ∀ y : M, B u.toMul y = 1 := by
      intro y
      have hy := hu (Additive.ofMul y)
      rw [hb_apply] at hy
      have hy' : (B u.toMul y).toAdd = 0 := by simpa [β] using hy
      exact Multiplicative.toAdd.injective (by rw [hy', toAdd_one])
    exact Additive.toMul.injective (by simpa using hBnd u.toMul h)
  have hb : b.Nondegenerate := hrefl.nondegenerate_iff_separatingLeft.mpr hsep
  have hirr : ∀ S : Submodule (ZMod 2) (Additive M),
      (∀ k ∈ Kb, ∀ x ∈ S, k x ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    let J : Subgroup M := (CFSG.Quasithin.H13.Mult.toSubIso).symm S
    have hJeq : CFSG.Quasithin.H13.Mult.toSub J = S := OrderIso.apply_symm_apply _ _
    have hJmem : ∀ x : M, x ∈ J ↔ Additive.ofMul x ∈ S := by
      intro x
      rw [← hJeq]
      exact (CFSG.Quasithin.H13.Mult.mem_toSub (K := J)).symm
    have hJ : StableUnder K J := by
      intro k hk x hx
      rw [hJmem]
      have hxS : Additive.ofMul x ∈ S := (hJmem x).mp hx
      have hkKb : eL k ∈ Kb := Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
      have hmem := hS (eL k) hkKb (Additive.ofMul x) hxS
      have h1 : eL k (Additive.ofMul x) = Additive.ofMul (k x) :=
        CFSG.Quasithin.H13.Mult.linEquiv_apply k (Additive.ofMul x)
      rwa [h1] at hmem
    rcases hKirr.2.2.2 J hJ bot_le le_top with hJbot | hJtop
    · left
      rw [← hJeq, hJbot]
      exact OrderIso.map_bot CFSG.Quasithin.H13.Mult.toSubIso
    · right
      rw [← hJeq, hJtop]
      exact OrderIso.map_top CFSG.Quasithin.H13.Mult.toSubIso
  have habs : ∀ f : Additive M →ₗ[ZMod 2] Additive M,
      (∀ k ∈ Kb, ∀ x, f (k x) = k (f x)) → ∃ c : ZMod 2, ∀ x, f x = c • x := by
    intro f hf
    have hkerinv : ∀ k ∈ Kb, ∀ x ∈ LinearMap.ker f, k x ∈ LinearMap.ker f := by
      intro k hk x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hf k hk x, hx, map_zero]
    rcases hirr (LinearMap.ker f) hkerinv with hker | hker
    · have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
      have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.mp hinj
      let g : Additive M ≃ₗ[ZMod 2] Additive M := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
      let c : MulAut M := eL.symm g
      have hcg : eL c = g := MulEquiv.apply_symm_apply eL g
      have hc_cent : c ∈ Subgroup.centralizer (K : Set (MulAut M)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        apply eL.injective
        rw [map_mul, map_mul, hcg]
        ext x
        change eL k (f x) = f (eL k x)
        exact (hf (eL k) (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩) x).symm
      have hc1 : c = 1 := by
        have hbot := centralizer_eq_bot_of_cost_one hM2 hKperf hK1 hKirr he0_2 hN0 hcost0
        rw [hbot] at hc_cent
        exact Subgroup.mem_bot.mp hc_cent
      refine ⟨1, fun x => ?_⟩
      have hg1 : g = 1 := by
        have h : eL c = eL 1 := by rw [hc1]
        rwa [hcg, map_one] at h
      have hfx : f x = x := by
        change g x = x
        rw [hg1]
        rfl
      rw [hfx, one_smul]
    · refine ⟨0, fun x => ?_⟩
      have hx : x ∈ LinearMap.ker f := by rw [hker]; exact Submodule.mem_top
      rw [LinearMap.mem_ker] at hx
      rw [hx, zero_smul]
  let A' : Submodule (ZMod 2) (Additive M) := CFSG.Quasithin.H13.Mult.toSub A
  have hfinrank : Module.finrank (ZMod 2) (Additive M) = rk M := by
    have h1 : 2 ^ Module.finrank (ZMod 2) (Additive M) = Nat.card M := by
      have h : Nat.card (Additive M) = 2 ^ Module.finrank (ZMod 2) (Additive M) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive M), Nat.card_zmod]
      rw [← h]
      exact (Nat.card_congr (Additive.ofMul (α := M))).symm
    have h2 : 2 ^ rk M = Nat.card M := by
      simpa [Subgroup.card_top, rk_top] using (card_eq_two_pow hM2 ⊤).symm
    exact Nat.pow_right_injective le_rfl (h1.trans h2.symm)
  have hfinA : Module.finrank (ZMod 2) A' = rk ↥A := by
    have h1 : 2 ^ Module.finrank (ZMod 2) A' = Nat.card A := by
      have h : Nat.card A' = 2 ^ Module.finrank (ZMod 2) A' := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A'), Nat.card_zmod]
      rw [← h]
      exact CFSG.Quasithin.H13.Mult.card_toSub (K := A)
    have h2 : 2 ^ rk ↥A = Nat.card A := (card_eq_two_pow hM2 A).symm
    exact Nat.pow_right_injective le_rfl (h1.trans h2.symm)
  have hA' : Module.finrank (ZMod 2) A' + 1 = Module.finrank (ZMod 2) (Additive M) := by
    rw [hfinA, hfinrank]
    have := rk_add_rkIdx A
    omega
  have hdim : 3 ≤ Module.finrank (ZMod 2) (Additive M) := by rw [hfinrank]; exact hn3
  have hnorm : ∀ e ∈ D, ∀ k ∈ Kb, eL e * k * (eL e)⁻¹ ∈ Kb := by
    intro e he k hk
    obtain ⟨k', hk', hk_eq⟩ := Subgroup.mem_map.mp hk
    rw [← hk_eq]
    change eL.toMonoidHom e * eL.toMonoidHom k' * (eL.toMonoidHom e)⁻¹ ∈ Kb
    rw [← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map.mpr ⟨e * k' * e⁻¹, ?_, rfl⟩
    have hmem : MulAut.conj e k' ∈ K.map (MulAut.conj e).toMonoidHom := ⟨k', hk', rfl⟩
    rw [hDnorm e he] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hmemA : ∀ e ∈ D, ∀ v : Additive M, eL e v - v ∈ A' := by
    intro e he v
    by_cases he1 : e = 1
    · rw [he1]; simp
    · change (eL e v - v).toMul ∈ A
      have toMul_sub : ∀ u w : Additive M, (u - w).toMul = u.toMul * (w.toMul)⁻¹ := by
        intro u w
        rw [sub_eq_add_neg, toMul_add, toMul_neg]
      have hsub : (eL e v - v).toMul = e v.toMul * (v.toMul)⁻¹ := by
        rw [toMul_sub, show eL e v = Additive.ofMul (e v.toMul) from
          CFSG.Quasithin.H13.Mult.linEquiv_apply e v]
        rfl
      rw [hsub, ← (hDtv e he he1).1]
      rw [mem_fixV]
      intro x hx
      rcases w1369_mem_zpowers_two (hDel.2 e he) hx with hx1 | hxe
      · rw [hx1]; rfl
      · rw [hxe]
        have hee : e * e = 1 := by rw [← pow_two]; exact hDel.2 e he
        have hee' : e (e v.toMul) = v.toMul := by
          have := congrArg (fun f : MulAut M => f v.toMul) hee
          simpa using this
        rw [map_mul, map_inv, hee', inv_eq_self_of_sq_eq_one hM2 (e v.toMul),
          inv_eq_self_of_sq_eq_one hM2 v.toMul]
        exact mul_comm _ _
  have hfixA : ∀ e ∈ D, ∀ a ∈ A', eL e a = a := by
    intro e he a ha
    have haA : a.toMul ∈ A := CFSG.Quasithin.H13.Mult.mem_toSub.mp ha
    by_cases he1 : e = 1
    · rw [he1]; simp
    · have hfa : a.toMul ∈ fixV (Subgroup.zpowers e) := by
        rw [(hDtv e he he1).1]; exact haA
      have hefix : e a.toMul = a.toMul := mem_fixV.mp hfa e (Subgroup.mem_zpowers e)
      rw [CFSG.Quasithin.H13.Mult.linEquiv_apply, hefix]
      rfl
  have hinv : ∀ k ∈ Kb, ∀ x y, b (k x) (k y) = b x y := by
    intro k hk x y
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
    rw [hb_apply, hb_apply]
    show β (eL k' x).toMul (eL k' y).toMul = β x.toMul y.toMul
    rw [CFSG.Quasithin.H13.Mult.linEquiv_apply, CFSG.Quasithin.H13.Mult.linEquiv_apply]
    simp only [β, toMul_ofMul]
    rw [hBinv k' hk']
  have hpres : ∀ e ∈ D, ∃ l : ZMod 2, l ≠ 0 ∧ ∀ x y,
      b (eL e x) (eL e y) = l * b x y :=
    fun e he => normalizer_preserves_alt Kb hirr habs b hb hinv (eL e) (hnorm e he)
  let Sset : Set (Additive M ≃ₗ[ZMod 2] Additive M) :=
    {g | (∀ v, g v - v ∈ A') ∧ (∀ a ∈ A', g a = a) ∧
      ∃ l : ZMod 2, l ≠ 0 ∧ ∀ x y, b (g x) (g y) = l * b x y}
  have hbound : Nat.card Sset ≤ 2 := by
    have h := lemmaH_alt hdim A' hA' b hb halt
    simpa only [Nat.card_zmod, Sset] using h
  haveI : Finite (Additive M ≃ₗ[ZMod 2] Additive M) :=
    Finite.of_injective (fun g : Additive M ≃ₗ[ZMod 2] Additive M =>
        (g : Additive M → Additive M))
      (fun g h hgh => LinearEquiv.ext (fun x => congrFun hgh x))
  haveI : Finite Sset := Set.finite_univ.subset (Set.subset_univ Sset)
  let φ : D → Sset := fun e => ⟨eL (e : MulAut M), hmemA e e.2, hfixA e e.2, hpres e e.2⟩
  have hφinj : Function.Injective φ := by
    intro e1 e2 h
    have hval : eL (e1 : MulAut M) = eL (e2 : MulAut M) := congrArg Subtype.val h
    exact Subtype.ext (eL.injective hval)
  have hcard : Nat.card D ≤ Nat.card Sset := Nat.card_le_card_of_injective φ hφinj
  omega

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
