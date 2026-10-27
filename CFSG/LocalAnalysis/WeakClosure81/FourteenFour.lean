module

public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryComplements
public import CFSG.LocalAnalysis.WeakClosure81.FourteenSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

variable {C V : Type*}

theorem finset_prod_monoidHom_apply {M N ι : Type*} [MulOneClass M] [CommMonoid N]
    (s : Finset ι) (f : ι → M →* N) (x : M) :
    (∏ i ∈ s, f i) x = ∏ i ∈ s, f i x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, MonoidHom.mul_apply, ih]

theorem pow_eq_self_of_odd_of_sq_eq_one {V : Type*} [CommGroup V] {v : V} (hv : v ^ 2 = 1)
    {n : ℕ} (hn : Odd n) : v ^ n = v := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ]
  rw [show v ^ (2 * k) = (v ^ 2) ^ k by rw [pow_mul]]
  rw [hv, one_pow, one_mul]

theorem exists_invariant_complement_of_odd_index
    [Group C] [Finite C] [CommGroup V]
    (hV2 : ∀ v : V, v ^ 2 = 1)
    (ρ : C →* MulAut V) {R : Subgroup C} (hR : Odd R.index)
    {V₀ : Subgroup V} (hV₀ : ∀ c : C, ∀ v ∈ V₀, ρ c v ∈ V₀)
    {W : Subgroup V} (hW : V₀.IsComplement' W)
    (hWR : ∀ r : R, ∀ w ∈ W, ρ (r : C) w ∈ W) :
    ∃ U : Subgroup V, V₀.IsComplement' U ∧ ∀ c : C, ∀ u ∈ U, ρ c u ∈ U := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  letI : Fintype (C ⧸ R) := Fintype.ofFinite _
  let projFun : V → V₀ := fun v => (hW.equiv v).1
  have hprojFun_mul : ∀ a b : V, projFun (a * b) = projFun a * projFun b := by
    intro a b
    have hmain : hW.equiv (a * b) =
        ((hW.equiv a).1 * (hW.equiv b).1, (hW.equiv a).2 * (hW.equiv b).2) := by
      rw [← Equiv.eq_symm_apply]
      simp only [IsComplement.equiv_symm_apply]
      change a * b = ((hW.equiv a).1 : V) * ((hW.equiv b).1 : V) *
        (((hW.equiv a).2 : V) * ((hW.equiv b).2 : V))
      rw [mul_mul_mul_comm]
      rw [IsComplement.equiv_fst_mul_equiv_snd hW a,
          IsComplement.equiv_fst_mul_equiv_snd hW b]
    exact congrArg Prod.fst hmain
  let proj : V →* V₀ :=
    { toFun := projFun
      map_one' := by
        have hmain : hW.equiv 1 = ((1 : V₀), (1 : W)) := by
          rw [← Equiv.eq_symm_apply]
          simp only [IsComplement.equiv_symm_apply]
          simp
        exact congrArg Prod.fst hmain
      map_mul' := hprojFun_mul }
  have hproj_inv_mul : ∀ v : V, (proj v : V)⁻¹ * v ∈ W := by
    intro v
    set a := (hW.equiv v).1 with ha
    set b := (hW.equiv v).2 with hb
    have h : (a : V) * (b : V) = v := by
      rw [ha, hb]
      exact IsComplement.equiv_fst_mul_equiv_snd hW v
    have hval : (proj v : V)⁻¹ * v = (b : V) := by
      change (a : V)⁻¹ * v = (b : V)
      rw [← h, inv_mul_cancel_left]
    rw [hval]
    exact b.2
  have hproj_fix : ∀ v (hv : v ∈ V₀), proj v = ⟨v, hv⟩ :=
    fun v hv => IsComplement.equiv_fst_eq_self_of_mem_of_one_mem hW W.one_mem hv
  have hproj_eq_of_mem : ∀ {a v : V}, a ∈ V₀ → a⁻¹ * v ∈ W → a = proj v := by
    intro a v ha h
    have hv : hW.equiv.symm (⟨a, ha⟩, (⟨a⁻¹ * v, h⟩ : W)) = v := by
      rw [IsComplement.equiv_symm_apply]
      show a * (a⁻¹ * v) = v
      group
    have h2 : hW.equiv v = (⟨a, ha⟩, (⟨a⁻¹ * v, h⟩ : W)) := by
      rw [← Equiv.eq_symm_apply]
      exact hv.symm
    have h3 : proj v = ⟨a, ha⟩ := by
      change (hW.equiv v).1 = ⟨a, ha⟩
      exact congrArg Prod.fst h2
    exact (Subtype.ext_iff.mp h3).symm
  have hproj_equiv : ∀ (r : R) (v : V), proj (ρ (r : C) v) = ρ (r : C) (proj v) := by
    intro r v
    have hmem : (ρ (r : C) (proj v)) ∈ V₀ := hV₀ (r : C) (proj v) (proj v).2
    have hWmem : (ρ (r : C) (proj v))⁻¹ * (ρ (r : C) v) ∈ W := by
      have h1 : ρ (r : C) ((proj v : V)⁻¹ * v) ∈ W :=
        hWR r ((proj v : V)⁻¹ * v) (hproj_inv_mul v)
      simpa only [map_mul, MulEquiv.map_inv] using h1
    exact (hproj_eq_of_mem hmem hWmem).symm
  let π : V →* V := V₀.subtype.comp proj
  have hπ_val : ∀ v : V, π v = (proj v : V) := fun v => rfl
  have hπ_equiv : ∀ (r : R) (v : V), π (ρ (r : C) v) = ρ (r : C) (π v) := by
    intro r v
    change (proj (ρ (r : C) v) : V) = ρ (r : C) ((proj v : V))
    rw [hproj_equiv]
  let ψ : C ⧸ R → (V →* V) := fun q =>
    ((ρ q.out).toMonoidHom).comp (π.comp ((ρ q.out)⁻¹).toMonoidHom)
  let φ : V →* V := ∏ q : C ⧸ R, ψ q
  have hφ_apply : ∀ v : V, φ v = ∏ q : C ⧸ R, ψ q v := by
    intro v
    exact finset_prod_monoidHom_apply Finset.univ ψ v
  have hstep : ∀ (c : C) (v : V) (q : C ⧸ R),
      ρ c (ψ q v) = ψ (c • q) (ρ c v) := by
    intro c v q
    have hc : (QuotientGroup.mk (c * q.out) : C ⧸ R) = c • (q : C ⧸ R) := by
      have h := MulAction.Quotient.mk_smul_out (b := c) (q := q)
      simpa only [smul_eq_mul] using h
    have hout : (QuotientGroup.mk ((c • q).out) : C ⧸ R) = c • (q : C ⧸ R) := by
      have h := MulAction.Quotient.mk_smul_out (b := (1 : C)) (q := c • q)
      simpa using h
    have heq : (QuotientGroup.mk (c * q.out) : C ⧸ R) =
        (QuotientGroup.mk ((c • q).out) : C ⧸ R) := by
      rw [hc, hout]
    have hmem : ((c * q.out)⁻¹ * (c • q).out) ∈ R := QuotientGroup.eq.mp heq
    obtain ⟨z, hz, hzq⟩ : ∃ z ∈ R, (c • q).out = (c * q.out) * z :=
      ⟨_, hmem, by group⟩
    have hkey : (ρ (c * q.out))⁻¹ (ρ c v) = (ρ q.out)⁻¹ v := by
      rw [map_mul, mul_inv_rev, MulAut.mul_apply]
      simp
    have hL : ρ c (ψ q v) = ρ (c * q.out) (π ((ρ q.out)⁻¹ v)) := by
      simp only [ψ, MonoidHom.comp_apply]
      show (ρ c) ((ρ q.out) (π ((ρ q.out)⁻¹ v))) = (ρ (c * q.out)) (π ((ρ q.out)⁻¹ v))
      rw [← MulAut.mul_apply]
      congr 1
      exact (map_mul ρ c q.out).symm
    have hR : ψ (c • q) (ρ c v) = ρ (c * q.out) (π ((ρ q.out)⁻¹ v)) := by
      have hzπ : (ρ z) (π ((ρ z)⁻¹ ((ρ q.out)⁻¹ v))) = π ((ρ q.out)⁻¹ v) := by
        have h := hπ_equiv ⟨z, hz⟩ ((ρ (⟨z, hz⟩ : R))⁻¹ ((ρ q.out)⁻¹ v))
        simpa only [MulAut.inv_apply, MulEquiv.apply_symm_apply] using h.symm
      simp only [ψ, MonoidHom.comp_apply, hzq]
      show (ρ ((c * q.out) * z)) (π (((ρ ((c * q.out) * z))⁻¹) (ρ c v))) = _
      rw [show ρ ((c * q.out) * z) = ρ (c * q.out) * ρ z from map_mul ρ (c * q.out) z]
      rw [mul_inv_rev]
      simp only [MulAut.mul_apply]
      rw [hkey, hzπ]
    rw [hL, hR]
  have hφ_fix : ∀ v ∈ V₀, φ v = v := by
    intro v hv
    rw [hφ_apply]
    have hterm : ∀ q : C ⧸ R, ψ q v = v := by
      intro q
      have hmem : (ρ q.out)⁻¹ v ∈ V₀ := by
        simpa only [map_inv] using hV₀ (q.out)⁻¹ v hv
      have hfix : proj ((ρ q.out)⁻¹ v) = ⟨(ρ q.out)⁻¹ v, hmem⟩ := hproj_fix _ hmem
      have : ψ q v = (ρ q.out) ((ρ q.out)⁻¹ v) := by
        change (ρ q.out) (π ((ρ q.out)⁻¹ v)) = (ρ q.out) ((ρ q.out)⁻¹ v)
        rw [hπ_val, hfix]
      rw [this]
      exact MulEquiv.apply_symm_apply (ρ q.out) v
    rw [show (∏ q : C ⧸ R, ψ q v) = ∏ _q : C ⧸ R, v from
      Finset.prod_congr rfl (fun q _ => hterm q)]
    rw [Finset.prod_const, Finset.card_univ]
    exact pow_eq_self_of_odd_of_sq_eq_one (hV2 v) (by
      rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
      exact hR)
  have hφ_mem : ∀ v : V, φ v ∈ V₀ := by
    intro v
    rw [hφ_apply]
    refine prod_mem fun q _ => ?_
    exact hV₀ q.out (π ((ρ q.out)⁻¹ v)) (by
      rw [hπ_val]
      exact (proj ((ρ q.out)⁻¹ v)).2)
  have hφ_comm : ∀ (c : C) (v : V), φ (ρ c v) = ρ c (φ v) := by
    intro c v
    rw [hφ_apply]
    have hR' : ρ c (φ v) = ∏ q : C ⧸ R, ρ c (ψ q v) := by
      rw [hφ_apply v]
      exact map_prod (ρ c).toMonoidHom (fun q => ψ q v) Finset.univ
    rw [hR']
    refine Fintype.prod_equiv (MulAction.toPerm c⁻¹)
      (fun q => ψ q (ρ c v)) (fun q => ρ c (ψ q v)) (fun q => ?_)
    rw [MulAction.toPerm_apply]
    simpa only [smul_inv_smul] using (hstep c v (c⁻¹ • q)).symm
  refine ⟨φ.ker, ?_, ?_⟩
  · refine CFSG.SignalizerFunctor.Helpers.isComplement'_of_isCompl_commutative ⟨?_, ?_⟩
    · rw [disjoint_iff_inf_le]
      intro x hx
      have hx1 : x ∈ V₀ := hx.1
      have hx2 : φ x = 1 := hx.2
      have hx_eq : x = 1 := by
        rw [← hφ_fix x hx1]
        exact hx2
      exact Subgroup.mem_bot.mpr hx_eq
    · rw [codisjoint_iff_le_sup]
      intro x _
      have hmem : φ x ∈ V₀ := hφ_mem x
      have hker : (φ x)⁻¹ * x ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have hfix : φ (φ x) = φ x := hφ_fix (φ x) hmem
        rw [hfix, inv_mul_cancel]
      have hx : x = (φ x) * ((φ x)⁻¹ * x) := by group
      rw [hx]
      exact Subgroup.mul_mem_sup hmem hker
  · intro c u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [hφ_comm, hu, map_one]

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_mul_of_isSylowIn
    {C M R : Subgroup G} (hCM : C ≤ M) (hMC : M ≤ Subgroup.normalizer (C : Set G))
    (hR : CFSG.Quasithin.IsSylowIn 2 R C) :
    ∀ m ∈ M, ∃ n ∈ M ⊓ Subgroup.normalizer (R : Set G), ∃ c ∈ C, m = c * n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro m hm
  let φ : MulAut ↥C := (Subgroup.normalizerMonoidHom C) ⟨m, hMC hm⟩
  have hφ : ∀ x : ↥C, (φ x : G) = m * (x : G) * m⁻¹ := by
    intro x
    rfl
  let Q : Sylow 2 ↥C := φ • hR.toSylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (M := ↥C) Q hR.toSylow
  let ψ : MulAut ↥C := MulAut.conj c * φ
  have hψ : ∀ x : ↥C, (ψ x : G) = (c : G) * m * (x : G) * ((c : G) * m)⁻¹ := by
    intro x
    have h1 : (ψ x : G) = (c : G) * (φ x : G) * (c : G)⁻¹ := by
      simp only [ψ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1, hφ x]
    group
  have h_eq : (R.subgroupOf C).map ψ.toMonoidHom = R.subgroupOf C := by
    have h2 : (((c : ↥C) • Q : Sylow 2 ↥C) : Subgroup ↥C) = R.subgroupOf C := by
      rw [hc, CFSG.Quasithin.IsSylowIn.coe_toSylow]
    have h3 : (((c : ↥C) • Q : Sylow 2 ↥C) : Subgroup ↥C) =
        (Q : Subgroup ↥C).map (MulAut.conj c).toMonoidHom := rfl
    have h4 : (Q : Subgroup ↥C) = (R.subgroupOf C).map φ.toMonoidHom := rfl
    calc (R.subgroupOf C).map ψ.toMonoidHom
        = ((R.subgroupOf C).map φ.toMonoidHom).map (MulAut.conj c).toMonoidHom := by
          rw [Subgroup.map_map]
          rfl
      _ = (((c : ↥C) • Q : Sylow 2 ↥C) : Subgroup ↥C) := by rw [← h4, ← h3]
      _ = R.subgroupOf C := h2
  have hnorm : ((c : G) * m) ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcomp : (MulAut.conj ((c : G) * m)).toMonoidHom.comp C.subtype =
        C.subtype.comp ψ.toMonoidHom := by
      ext x
      exact (hψ x).symm
    calc R.map (MulAut.conj ((c : G) * m)).toMonoidHom
        = ((R.subgroupOf C).map C.subtype).map (MulAut.conj ((c : G) * m)).toMonoidHom := by
          rw [Subgroup.map_subgroupOf_eq_of_le hR.le]
      _ = (R.subgroupOf C).map ((MulAut.conj ((c : G) * m)).toMonoidHom.comp C.subtype) := by
          rw [Subgroup.map_map]
      _ = (R.subgroupOf C).map (C.subtype.comp ψ.toMonoidHom) := by rw [hcomp]
      _ = ((R.subgroupOf C).map ψ.toMonoidHom).map C.subtype := by rw [Subgroup.map_map]
      _ = (R.subgroupOf C).map C.subtype := by rw [h_eq]
      _ = R := Subgroup.map_subgroupOf_eq_of_le hR.le
  refine ⟨(c : G) * m, ⟨M.mul_mem (hCM c.2) hm, hnorm⟩, (c : G)⁻¹, C.inv_mem c.2, ?_⟩
  group

variable {G : Type} [Group G] [Finite G]

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem cTilde_le_M (M V₀ V : Subgroup G) : F11.CTilde M V₀ V ≤ M := by
  intro g hg
  rw [F11.CTilde] at hg
  exact (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg 1) V.one_mem).1

noncomputable def actMTil {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G)) (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G)) :
    ↥M →* MulAut (Vtil V₀ V hV) :=
  (actTil V₀ V hV).comp (Subgroup.inclusion (le_stabTil hM hM₀))

theorem cTilde_subgroupOf_eq_ker {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G)) (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G)) :
    (F11.CTilde M V₀ V).subgroupOf M = (actMTil hV hM hM₀).ker := by
  ext m
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, mem_cTilde_iff hV hM]
  constructor
  · rintro ⟨-, h, h1⟩
    show actTil V₀ V hV (Subgroup.inclusion (le_stabTil hM hM₀) m) = 1
    have : (Subgroup.inclusion (le_stabTil hM hM₀) m : stabTil V₀ V) = ⟨m, h⟩ :=
      Subtype.ext rfl
    rw [this]
    exact h1
  · intro h
    exact ⟨m.2, le_stabTil hM hM₀ m.2, h⟩

theorem cTilde_subgroupOf_normal {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G)) (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G)) :
    ((F11.CTilde M V₀ V).subgroupOf M).Normal := by
  rw [cTilde_subgroupOf_eq_ker hV hM hM₀]
  infer_instance

theorem mem_cTilde_mul_inv {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G)) {c x : G}
    (hc : c ∈ F11.CTilde M V₀ V) (hx : x ∈ V) :
    c * x * c⁻¹ * x⁻¹ ∈ V₀ := by
  obtain ⟨-, h, h1⟩ := (mem_cTilde_iff hV hM).1 hc
  exact (actTil_eq_one_iff V₀ V hV ⟨c, h⟩).1 h1 x hx

theorem cTilde_le_normalizer₀ {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G)) :
    F11.CTilde M V₀ V ≤ Subgroup.normalizer (V₀ : Set G) := by
  intro c hc
  obtain ⟨-, h, -⟩ := (mem_cTilde_iff hV hM).1 hc
  exact h.2

theorem exists_invariant_complement_of_odd_index_subgroup
    {V₀ V C R W : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀le : V₀ ≤ V) (hWle : W ≤ V)
    (hC : C ≤ Subgroup.normalizer (V : Set G))
    (hC₀ : C ≤ Subgroup.normalizer (V₀ : Set G))
    (hRC : R ≤ C) (hRodd : Odd (R.subgroupOf C).index)
    (hWinf : V₀ ⊓ W = ⊥) (hWsup : V₀ ⊔ W = V)
    (hWinv : ∀ r ∈ R, ∀ w ∈ W, r * w * r⁻¹ ∈ W) :
    ∃ U : Subgroup G, U ≤ V ∧ V₀ ⊓ U = ⊥ ∧ V₀ ⊔ U = V ∧
      (∀ c ∈ C, ∀ u ∈ U, c * u * c⁻¹ ∈ U) := by
  letI : CommGroup ↥V := commGroupOfElemAbelian hV
  let V₀' : Subgroup ↥V := V₀.subgroupOf V
  let W' : Subgroup ↥V := W.subgroupOf V
  let ρ : ↥C →* MulAut ↥V := (convI hV).comp (Subgroup.inclusion hC)
  have hρ_val : ∀ (c : ↥C) (v : ↥V), (ρ c v).val = (c : G) * v.val * (c : G)⁻¹ :=
    fun c v => convI_apply_val hV (Subgroup.inclusion hC c) v
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => IntMod.sq_eq_one (hV := hV) v
  have hV₀'inv : ∀ c : ↥C, ∀ v ∈ V₀', ρ c v ∈ V₀' := by
    intro c v hv
    have hv' : v.val ∈ V₀ := hv
    show (ρ c v).val ∈ V₀
    rw [hρ_val]
    exact (Subgroup.mem_normalizer_iff.1 (hC₀ c.2) v.val).1 hv'
  have hW'inv : ∀ r : R.subgroupOf C, ∀ w ∈ W', ρ r w ∈ W' := by
    intro r w hw
    have hw' : w.val ∈ W := hw
    show (ρ r w).val ∈ W
    rw [hρ_val]
    exact hWinv (r : G) r.2 w.val hw'
  have hW'compl : V₀'.IsComplement' W' := by
    have hinf : V₀' ⊓ W' = ⊥ := by
      have hiff : V₀' ⊓ W' = (V₀ ⊓ W).subgroupOf V := by
        show V₀.subgroupOf V ⊓ W.subgroupOf V = (V₀ ⊓ W).subgroupOf V
        ext x
        simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact hiff.trans ((congrArg (fun H : Subgroup G => H.subgroupOf V) hWinf).trans
        (bot_subgroupOf V))
    have hsup : V₀' ⊔ W' = ⊤ := by
      have hiff : V₀' ⊔ W' = (V₀ ⊔ W).subgroupOf V := by
        show V₀.subgroupOf V ⊔ W.subgroupOf V = (V₀ ⊔ W).subgroupOf V
        rw [Subgroup.subgroupOf_sup hV₀le hWle]
      exact hiff.trans ((congrArg (fun H : Subgroup G => H.subgroupOf V) hWsup).trans
        (Subgroup.subgroupOf_self V))
    exact CFSG.SignalizerFunctor.Helpers.isComplement'_of_isCompl_commutative
      (isCompl_iff.mpr ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩)
  obtain ⟨U', hU'compl, hU'inv⟩ :=
    exists_invariant_complement_of_odd_index (V := ↥V) (C := ↥C) hV2 ρ hRodd hV₀'inv hW'compl hW'inv
  refine ⟨U'.map V.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy.2
    have hzV₀ : z ∈ V₀' := hy.1
    have hzbot : z ∈ V₀' ⊓ U' := ⟨hzV₀, hz⟩
    rw [hU'compl.isCompl.inf_eq_bot] at hzbot
    rw [Subgroup.mem_bot.mp hzbot]
    exact Subgroup.mem_bot.mpr rfl
  · have htop : (⊤ : Subgroup ↥V).map V.subtype = V :=
      (Subgroup.map_top V.subtype).trans (Subgroup.range_subtype V)
    have h2 : V₀ ⊔ U'.map V.subtype = V := by
      have hmap : (V₀' ⊔ U').map V.subtype = V := by
        rw [hU'compl.sup_eq_top, htop]
      rw [Subgroup.map_sup] at hmap
      simpa only [V₀', Subgroup.map_subgroupOf_eq_of_le hV₀le] using hmap
    exact h2
  · intro c hc u hu
    obtain ⟨z, hz, rfl⟩ := hu
    exact ⟨ρ ⟨c, hc⟩ z, hU'inv ⟨c, hc⟩ z hz, hρ_val ⟨c, hc⟩ z⟩

theorem fourteen_four
    {V V₀ M : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G))
    (hV₀le : V₀ ≤ V)
    (hgen : ConjGenerated M V₀ V)
    (hCeven : ¬ F11.CTilde M V₀ V ≤ Subgroup.centralizer (V : Set G))
    {R : Subgroup G} (hR : IsSylowIn 2 R (F11.CTilde M V₀ V)) :
    V ⊓ Subgroup.centralizer (R : Set G) ≤ V₀ := by
  intro x hx
  by_contra hx0
  have hxV : x ∈ V := hx.1
  have hxR : x ∈ Subgroup.centralizer (R : Set G) := hx.2
  have hxR' : ∀ r ∈ R, r * x = x * r := Subgroup.mem_centralizer_iff.1 hxR
  let Cg : Subgroup G := F11.CTilde M V₀ V
  let Nn : Subgroup G := M ⊓ Subgroup.normalizer (R : Set G)
  let E : Subgroup G := Subgroup.closure {y : G | ∃ n ∈ Nn, y = n * x * n⁻¹}
  have hMCg : M ≤ Subgroup.normalizer (Cg : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M M V₀ V)).mp
      (cTilde_subgroupOf_normal hV hM hM₀)
  have hfratt : ∀ m ∈ M, ∃ n ∈ Nn, ∃ c ∈ Cg, m = c * n := by
    intro m hm
    obtain ⟨n, hn, c, hc, hmn⟩ := exists_mem_normalizer_mul_of_isSylowIn
      (C := Cg) (M := M) (R := R) (cTilde_le_M M V₀ V) hMCg hR m hm
    exact ⟨n, hn, c, hc, hmn⟩
  have hE_le_V : E ≤ V := by
    refine (Subgroup.closure_le V).2 ?_
    rintro y ⟨n, hn, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hM hn.1) x).1 hxV
  have hE_le_R : E ≤ Subgroup.centralizer (R : Set G) := by
    refine (Subgroup.closure_le (Subgroup.centralizer (R : Set G))).2 ?_
    rintro y ⟨n, hn, rfl⟩
    change n * x * n⁻¹ ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : n⁻¹ * r * n ∈ R := (Subgroup.mem_normalizer_iff''.1 hn.2 r).1 hr
    have hxr : x * (n⁻¹ * r * n) = (n⁻¹ * r * n) * x := (hxR' _ hr').symm
    calc r * (n * x * n⁻¹) = n * ((n⁻¹ * r * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * r * n)) * n⁻¹ := by rw [← hxr]
      _ = (n * x * n⁻¹) * r := by group
  have hEsup : E ⊔ V₀ = V := by
    refine le_antisymm (sup_le hE_le_V hV₀le) ?_
    have hgenx : V = Subgroup.closure {y : G | ∃ m ∈ M, y = m * x * m⁻¹} := by
      exact (hgen : ∀ v ∈ V, v ∉ V₀ →
        V = Subgroup.closure {y : G | ∃ m ∈ M, y = m * v * m⁻¹}) x hxV hx0
    rw [hgenx]
    refine (Subgroup.closure_le (E ⊔ V₀)).2 ?_
    rintro y ⟨m, hm, rfl⟩
    obtain ⟨n, hn, c, hc, hmn⟩ := hfratt m hm
    have hnv : n * x * n⁻¹ ∈ E := Subgroup.subset_closure ⟨n, hn, rfl⟩
    have hcv : c * (n * x * n⁻¹) * c⁻¹ ∈ E ⊔ V₀ := by
      have h1 : c * (n * x * n⁻¹) * c⁻¹ * (n * x * n⁻¹)⁻¹ ∈ V₀ :=
        mem_cTilde_mul_inv hV hM hc (hE_le_V hnv)
      have h2 : c * (n * x * n⁻¹) * c⁻¹ =
          (c * (n * x * n⁻¹) * c⁻¹ * (n * x * n⁻¹)⁻¹) * (n * x * n⁻¹) := by group
      rw [h2]
      have hmem := Subgroup.mul_mem_sup h1 hnv
      rwa [sup_comm] at hmem
    rw [hmn]
    have hcv' : c * n * x * (c * n)⁻¹ = c * (n * x * n⁻¹) * c⁻¹ := by group
    rwa [hcv']
  have hE_elem : IsElemAbelian 2 E :=
    ⟨⟨⟨fun a b => Subtype.ext (by
        have hc := congrArg Subtype.val
          (hV.1.is_comm.comm (⟨(a : G), hE_le_V a.2⟩ : V) ⟨(b : G), hE_le_V b.2⟩)
        simpa using hc)⟩⟩,
      fun x hx => hV.2 x (hE_le_V hx)⟩
  letI : CommGroup ↥E := commGroupOfElemAbelian hE_elem
  obtain ⟨W'', hW''⟩ := CFSG.SignalizerFunctor.Helpers.elementary_abelian_complement_exists
    2 Nat.prime_two ↥E (fun y => Subtype.ext (by
      show (y : G) ^ 2 = 1
      exact hV.2 (y : G) (hE_le_V y.2))) (V₀.subgroupOf E)
  let W : Subgroup G := W''.map E.subtype
  have hW_le_E : W ≤ E := Subgroup.map_subtype_le _
  have hEeq : E = (V₀ ⊓ E) ⊔ W := by
    have h3 : ((V₀.subgroupOf E : Subgroup ↥E) ⊔ W'') = ⊤ := hW''.isCompl.sup_eq_top
    have h4 : (((V₀.subgroupOf E : Subgroup ↥E) ⊔ W'').map E.subtype) = E := by
      rw [h3, Subgroup.map_top, Subgroup.range_subtype]
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype] at h4
    exact h4.symm
  have hWinf : V₀ ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy.2
    have hzV : z ∈ V₀.subgroupOf E := hy.1
    have hz1 : z ∈ (V₀.subgroupOf E : Subgroup ↥E) ⊓ W'' := ⟨hzV, hz⟩
    rw [hW''.isCompl.inf_eq_bot] at hz1
    rw [Subgroup.mem_bot.mp hz1]
    exact Subgroup.mem_bot.mpr (map_one E.subtype)
  have hWsup : V₀ ⊔ W = V := by
    rw [← hEsup, hEeq, sup_assoc, sup_eq_right.mpr (le_trans inf_le_left le_sup_right), sup_comm]
  have hRodd : Odd (R.subgroupOf Cg).index := by
    rw [show (R.subgroupOf Cg).index = R.relIndex Cg from rfl]
    exact Nat.not_even_iff_odd.mp fun h => hR.not_dvd_relIndex (even_iff_two_dvd.mp h)
  have hWinv : ∀ r ∈ R, ∀ w ∈ W, r * w * r⁻¹ ∈ W := by
    intro r hr w hw
    have hwr : w ∈ Subgroup.centralizer (R : Set G) := hE_le_R (hW_le_E hw)
    have hcomm : r * w = w * r := (Subgroup.mem_centralizer_iff.1 hwr) r hr
    rw [show r * w * r⁻¹ = w from by rw [hcomm]; group]
    exact hw
  obtain ⟨U, hU_le_V, hUinf, hUsup, hUinv⟩ :=
    exists_invariant_complement_of_odd_index_subgroup (V₀ := V₀) (V := V) (C := Cg) (R := R) (W := W)
      hV hV₀le (hW_le_E.trans hE_le_V) ((cTilde_le_M M V₀ V).trans hM)
      (cTilde_le_normalizer₀ hV hM) hR.le hRodd hWinf hWsup hWinv
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hx0
    have hVeq : V = V₀ := by rw [← hUsup, hbot, sup_bot_eq]
    rw [← hVeq]
    exact hxV
  obtain ⟨u, huU, hu_ne⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra h
    apply hUne
    rw [eq_bot_iff]
    intro y hy
    by_contra hy0
    exact h ⟨y, hy, hy0⟩
  have huV : u ∈ V := hU_le_V huU
  have hu0 : u ∉ V₀ := by
    intro huV₀
    have : u ∈ V₀ ⊓ U := ⟨huV₀, huU⟩
    rw [hUinf] at this
    exact hu_ne (Subgroup.mem_bot.mp this)
  have hCg_cent_u : ∀ c ∈ Cg, c * u = u * c := by
    intro c hc
    have h1 : c * u * c⁻¹ ∈ U := hUinv c hc u huU
    have h2 : c * u * c⁻¹ * u⁻¹ ∈ V₀ := mem_cTilde_mul_inv hV hM hc huV
    have h3 : c * u * c⁻¹ * u⁻¹ ∈ U ⊓ V₀ :=
      ⟨U.mul_mem h1 (U.inv_mem huU), h2⟩
    rw [inf_comm, hUinf] at h3
    have h4 : c * u * c⁻¹ * u⁻¹ = 1 := Subgroup.mem_bot.mp h3
    have h5 : c * u * c⁻¹ = u := mul_inv_eq_one.mp h4
    calc c * u = (c * u * c⁻¹) * c := by group
      _ = u * c := by rw [h5]
  have hgenu : V = Subgroup.closure {y : G | ∃ m ∈ M, y = m * u * m⁻¹} :=
    (hgen : ∀ v ∈ V, v ∉ V₀ → V = Subgroup.closure {y : G | ∃ m ∈ M, y = m * v * m⁻¹}) u huV hu0
  apply hCeven
  intro c hc
  rw [hgenu, Subgroup.mem_centralizer_iff]
  intro y hy
  have hcl : Subgroup.closure {y : G | ∃ m ∈ M, y = m * u * m⁻¹} ≤
      Subgroup.centralizer (Cg : Set G) := by
    refine (Subgroup.closure_le (Subgroup.centralizer (Cg : Set G))).2 ?_
    rintro y ⟨m, hm, rfl⟩
    change m * u * m⁻¹ ∈ Subgroup.centralizer (Cg : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro c' hc'
    have hcinv : m⁻¹ * c' * m ∈ Cg := (Subgroup.mem_normalizer_iff''.1 (hMCg hm) c').1 hc'
    have hcent := hCg_cent_u (m⁻¹ * c' * m) hcinv
    calc c' * (m * u * m⁻¹) = m * ((m⁻¹ * c' * m) * u) * m⁻¹ := by group
      _ = m * (u * (m⁻¹ * c' * m)) * m⁻¹ := by rw [hcent]
      _ = (m * u * m⁻¹) * c' := by group
  exact (Subgroup.mem_centralizer_iff.1 (hcl hy) c hc).symm

end CFSG.LocalAnalysis.WeakClosure81
