module

public import CFSG.OddTranspositions.O4Minus5Pair
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.L2.Lemma12hc
public import CFSG.GH74.GLS.IVK.L2.Lemma13
public import CFSG.GH74.GLS.IVK.Lifted.SolvAut

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem not_A5_le_of_isDihedralOrder {Y : Type} [Group Y] {d : ℕ} (hY : IsDihedralOrder Y d)
    {X : Subgroup Y} (hX : Nonempty (X ≃* alternatingGroup (Fin 5))) : False := by
  obtain ⟨k, -, hk, ⟨φ⟩⟩ := hY
  obtain ⟨eX⟩ := hX
  haveI : NeZero k := ⟨by omega⟩
  haveI := CFSG.GH74.GLS.IVK.Lifted.isSolvable_dihedral' k
  haveI : Group.IsSolvable Y := solvable_of_solvable_injective (f := φ.toMonoidHom) φ.injective
  haveI : Group.IsSolvable (alternatingGroup (Fin 5)) :=
    solvable_of_solvable_injective (f := eX.symm.toMonoidHom) eX.symm.injective
  have hc := (IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (Fin 5))).mpr
    inferInstance
  have hnc : ¬ ∀ a b : alternatingGroup (Fin 5), a * b = b * a := by decide +kernel
  exact hnc hc

theorem l2Field_K25 : L2Field K25 := by
  refine ⟨?_, ?_⟩ <;> rw [card_K25] <;> decide

theorem ringAut_K25_cases (σ : K25 ≃+* K25) : σ = 1 ∨ σ = frob25 := by
  classical
  haveI : Finite (K25 ≃+* K25) := Nat.finite_of_card_ne_zero (by rw [card_ringAut]; norm_num)
  letI := Fintype.ofFinite (K25 ≃+* K25)
  by_contra h
  push Not at h
  have h1 : (1 : K25 ≃+* K25) ≠ frob25 := frob25_ne_one.symm
  have : 3 ≤ Nat.card (K25 ≃+* K25) := by
    rw [Nat.card_eq_fintype_card]
    have hs : ({1, frob25, σ} : Finset (K25 ≃+* K25)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h.2)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1, Ne.symm h.1⟩
    rw [← hs]; exact Finset.card_le_univ _
  rw [card_ringAut] at this; omega

theorem eq_of_conjNormal_eq {L : Subgroup G} [L.Normal]
    (hCL : Subgroup.centralizer (L : Set G) = ⊥) {g h : G}
    (hgh : (MulAut.conjNormal g : MulAut L) = MulAut.conjNormal h) : g = h := by
  have hc : h⁻¹ * g ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro ℓ hℓ
    have := congrArg (fun σ : MulAut L => ((σ ⟨ℓ, hℓ⟩ : L) : G)) hgh
    simp only [MulAut.conjNormal_apply] at this
    calc ℓ * (h⁻¹ * g) = h⁻¹ * (h * ℓ * h⁻¹) * g := by group
      _ = h⁻¹ * (g * ℓ * g⁻¹) * g := by rw [this]
      _ = h⁻¹ * g * ℓ := by group
  rw [hCL, Subgroup.mem_bot] at hc
  calc g = h * (h⁻¹ * g) := by group
    _ = h := by rw [hc, mul_one]

theorem isO4Minus5Pair_of_mulEquiv_psl225 {L : Subgroup G} [hLn : L.Normal] (hL2 : L.index = 2)
    (eL : L ≃* PSL225) (hCL : Subgroup.centralizer (L : Set G) = ⊥) {z : G} (hz2 : z * z = 1)
    (hzL : z ∉ L) {X : Subgroup G} (hXL : X ≤ L) (hX : Nonempty (X ≃* alternatingGroup (Fin 5)))
    (hXz : X ≤ Subgroup.centralizer ({z} : Set G)) {D : Set G}
    (hcls : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hinv : ∀ d ∈ D, d * d = 1)
    (hDL : ∀ d ∈ D, d ∉ L) : IsO4Minus5Pair G D := by
  classical
  obtain ⟨d, rfl⟩ := hcls
  have hd : d ∈ {g | IsConj d g} := IsConj.refl d
  have hd2 := hinv d hd
  have hdL := hDL d hd
  have hF := l2Field_K25
  let e₀ : L ≃* L2 K25 := eL.trans (L2.equivPSL K25).symm
  obtain ⟨e, N, -⟩ :=
    ivk_1_2a_exists K25 hF L e₀ (inferInstance : Nonempty (Sylow 2 (MulAut L))).some
  set yz : MulAut L := MulAut.conjNormal z with hyz
  set yd : MulAut L := MulAut.conjNormal d with hyd
  have hz1 : z ≠ 1 := fun h => hzL (h ▸ L.one_mem)
  have hyzInn : yz ∉ innAut L := by
    rintro ⟨u, hu⟩
    apply hzL
    have : z = u := eq_of_conjNormal_eq hCL (by rw [← hyz, ← hu, MulAut.conjNormal_val])
    rw [this]; exact u.2
  have hyz2 : yz ^ 2 = 1 := by rw [hyz, ← map_pow, pow_two, hz2, map_one]
  have hyz1 : yz ≠ 1 := fun h => hz1 (eq_of_conjNormal_eq hCL (by rw [← hyz, h, map_one]))
  have hyzo : orderOf yz = 2 := orderOf_eq_prime hyz2 hyz1
  have hyzD : yz ∉ innDiagSub e := by
    intro hD
    have h25 : (Nat.card K25 : ℤ) ≡ 1 [ZMOD 4] := by rw [card_K25]; decide
    have h26 : ((26 : ℕ) : ℤ) = Nat.card K25 + 1 := by rw [card_K25]; norm_num
    have hdih := (ivk_1_3b K25 hF L e 1 (Or.inl rfl) h25 26 h26 yz hD hyzInn hyzo).2.1
    obtain ⟨eX⟩ := hX
    have hXF : X.subgroupOf L ≤ fixedSubgroup L yz := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      show yz x = x
      apply Subtype.ext
      rw [hyz, MulAut.conjNormal_apply]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hXz hx)
      rw [← this]; group
    exact not_A5_le_of_isDihedralOrder hdih (X := (X.subgroupOf L).subgroupOf _)
      ⟨((Subgroup.subgroupOfEquivOfLe hXF).trans (Subgroup.subgroupOfEquivOfLe hXL)).trans eX⟩
  have hdz : d * z⁻¹ ∈ L := by
    rw [Subgroup.mul_mem_iff_of_index_two hL2]
    exact iff_of_false hdL (fun h => hzL (by simpa using L.inv_mem h))
  have hydD : yd ∉ innDiagSub e := by
    intro hD
    apply hyzD
    have h1 : (MulAut.conjNormal (d * z⁻¹) : MulAut L) ∈ innDiagSub e := by
      apply innAut_le_innDiagSub e
      exact ⟨⟨_, hdz⟩, by rw [← MulAut.conjNormal_val]⟩
    have : yz = (MulAut.conjNormal (d * z⁻¹))⁻¹ * yd := by
      rw [hyz, hyd, ← map_inv, ← map_mul]; congr 1; group
    rw [this]
    exact (innDiagSub e).mul_mem ((innDiagSub e).inv_mem h1) hD
  have hyInn : yd ∉ innAut L := fun h => hydD (innAut_le_innDiagSub e h)
  have hyd2 : yd ^ 2 = 1 := by rw [hyd, ← map_pow, pow_two, hd2, map_one]
  obtain ⟨g, hg, hyg⟩ := fieldAutHom_fieldProj_mul e yd
  have hσ1 : fieldProj e yd ≠ 1 := fun h => hydD ((mem_innDiagSub_iff e yd).2 h)
  have hσ2 : fieldProj e yd ^ 2 = 1 := by rw [← map_pow, hyd2, map_one]
  have hσo : orderOf (fieldProj e yd) = 2 := orderOf_eq_prime hσ2 hσ1
  have hf1 : fieldAutHom e (fieldProj e yd) ≠ 1 := fun h =>
    hσ1 (fieldAutHom_injective e (h.trans (map_one _).symm))
  have hf2 : fieldAutHom e (fieldProj e yd) ^ 2 = 1 := by rw [← map_pow, hσ2, map_one]
  have hfo : orderOf (fieldAutHom e (fieldProj e yd)) = 2 := orderOf_eq_prime hf2 hf1
  have hfF : fieldAutHom e (fieldProj e yd) ∈ fieldAutSub e := ⟨_, rfl⟩
  have hfT : fieldAutHom e (fieldProj e yd) ∈ (N.T : Subgroup (MulAut L)) := by
    have hP : IsPGroup 2 ↥(Subgroup.zpowers (fieldAutHom e (fieldProj e yd))) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hfo]; norm_num)
    have h1 := hP.inf_normalizer_sylow N.T
    have h2 : fieldAutHom e (fieldProj e yd) ∈
        Subgroup.zpowers (fieldAutHom e (fieldProj e yd)) ⊓
          Subgroup.normalizer (N.T : Set (MulAut L)) :=
      ⟨Subgroup.mem_zpowers _, N.T_inv hfF⟩
    rw [h1] at h2
    exact h2.2
  have hyo : orderOf (g * fieldAutHom e (fieldProj e yd)) = 2 := by
    rw [← hyg]
    exact orderOf_eq_prime hyd2 (fun h => hyInn (by rw [h]; exact one_mem _))
  obtain ⟨α, -, hay⟩ := ivk_1_2h_c K25 hF L e N _ ⟨hfT, hfF⟩ hfo g hg hyo
  rw [← hyg] at hay
  have hσ : fieldProj e yd = frob25 := (ringAut_K25_cases _).resolve_left hσ1
  rw [hσ] at hay
  set ψ : L ≃* PSL225 := α.trans (toPSL e) with hψdef
  have hψ : ∀ ℓ : L, ψ (yd ℓ) = psl2FieldAut K25 frob25 (ψ ℓ) := by
    intro ℓ
    have h1 : α (yd ℓ) = fieldAutHom e frob25 (α ℓ) := by
      rw [← hay]; simp
    simp only [hψdef, MulEquiv.trans_apply, h1, fieldAutHom, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.congr_symm_apply, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply]
  let fg : (K25 ≃+* K25) →* G :=
    { toFun := fun σ => if σ = 1 then 1 else d
      map_one' := if_pos rfl
      map_mul' := by
        intro σ τ
        rcases ringAut_K25_cases σ with rfl | rfl <;> rcases ringAut_K25_cases τ with rfl | rfl
        · simp
        · simp [frob25_ne_one]
        · simp [frob25_ne_one]
        · rw [frob25_mul_self]; simp [frob25_ne_one, hd2] }
  have hfg1 : fg 1 = 1 := map_one fg
  have hfgf : fg frob25 = d := if_neg frob25_ne_one
  let fn : PSL225 →* G := L.subtype.comp ψ.symm.toMonoidHom
  have hcompat : ∀ σ, fn.comp (psl2FieldAut K25 σ).toMonoidHom =
      (MulAut.conj (fg σ)).toMonoidHom.comp fn := by
    intro σ
    refine MonoidHom.ext fun m => ?_
    rcases ringAut_K25_cases σ with rfl | rfl
    · simp [hfg1]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hfgf]
      obtain ⟨ℓ, rfl⟩ := ψ.surjective m
      rw [← hψ ℓ]
      simp [fn, hyd, MulAut.conjNormal_apply]
  let Ψ : PSigmaL225 →* G := SemidirectProduct.lift fn fg hcompat
  have hΨd : Ψ (SemidirectProduct.inr frob25) = d := by
    simp [Ψ, SemidirectProduct.lift_inr, hfgf]
  have hΨinj : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : fn x.left * fg x.right = 1 := hx
    rw [Subgroup.mem_bot]
    rcases ringAut_K25_cases x.right with h | h
    · rw [h, hfg1, mul_one] at hx'
      have : ψ.symm x.left = 1 := Subtype.ext hx'
      have hl : x.left = 1 := by simpa using this
      exact SemidirectProduct.ext hl h
    · rw [h, hfgf] at hx'
      exfalso
      apply hdL
      have : d = (fn x.left)⁻¹ := eq_inv_of_mul_eq_one_right hx'
      rw [this]
      exact L.inv_mem (ψ.symm x.left).2
  have hcard : Nat.card G ≤ Nat.card PSigmaL225 := by
    rw [card_PSigmaL225_mul, card_ringAut, ← Nat.card_congr eL.toEquiv, ← L.index_mul_card, hL2,
      mul_comm]
  have hΨbij : Function.Bijective Ψ := by
    refine ⟨hΨinj, ?_⟩
    have := (Function.Injective.bijective_of_nat_card_le hΨinj hcard)
    exact this.2
  let E : G ≃* PSigmaL225 := (MulEquiv.ofBijective Ψ hΨbij).symm
  have hEd : E d = SemidirectProduct.inr frob25 := by
    apply (MulEquiv.ofBijective Ψ hΨbij).injective
    simp [E, hΨd]
  refine ⟨E, ?_⟩
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hg
    show IsConj (SemidirectProduct.inr frob25) (E g)
    rw [← hEd]
    exact isConj_iff.mpr ⟨E c, by rw [← hc]; simp⟩
  · intro hx
    obtain ⟨c, hc⟩ := isConj_iff.mp (show IsConj (SemidirectProduct.inr frob25) x from hx)
    refine ⟨E.symm x, isConj_iff.mpr ⟨E.symm c, ?_⟩, by simp⟩
    rw [← hc, ← hEd]; simp


end CFSG.OddTranspositions.QZ
