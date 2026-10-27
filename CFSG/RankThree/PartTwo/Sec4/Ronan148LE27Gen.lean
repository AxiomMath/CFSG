module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LU45

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.DFT

section Count

variable (N : ℕ) [NeZero N]

theorem card_three_torsion_le : Nat.card {c : ZMod N // 3 • c = 0} ≤ 3 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert IsAddCyclic.card_nsmul_eq_zero_le (α := ZMod N) (n := 3) (by norm_num)

@[expose] def torsEquiv :
    {v : Fin 3 → ZMod N // 3 • v = 0} ≃ (Fin 3 → {c : ZMod N // 3 • c = 0}) where
  toFun v i := ⟨v.1 i, by simpa using congrFun v.2 i⟩
  invFun w := ⟨fun i => (w i).1, funext fun i => by simpa using (w i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_torsion_le : Nat.card {v : Fin 3 → ZMod N // 3 • v = 0} ≤ 27 := by
  rw [Nat.card_congr (torsEquiv N), Nat.card_fun, Nat.card_fin]
  calc Nat.card {c : ZMod N // 3 • c = 0} ^ 3 ≤ 3 ^ 3 :=
        Nat.pow_le_pow_left (card_three_torsion_le N) 3
    _ = 27 := by norm_num

theorem card_fix_torsion_le :
    Nat.card {u : Fin 3 → ZMod N // rot3 u = u ∧ 3 • u = 0} ≤ 3 := by
  refine le_trans (Nat.card_le_card_of_injective (fun u =>
    (⟨u.1 0, by simpa using congrFun u.2.2 0⟩ : {c : ZMod N // 3 • c = 0})) ?_)
    (card_three_torsion_le N)
  intro u v huv
  apply Subtype.ext
  rw [rot3_fixed u.2.1, rot3_fixed v.2.1]
  exact congrArg (fun c => fun _ : Fin 3 => c) (congrArg Subtype.val huv)

end Count

section Torus

variable {F : Type} [Field F]

@[expose] noncomputable def τ4 {ω : Fˣ} (hω3 : ω ^ 3 = 1) :
    Multiplicative (Fin 3 → ZMod 3) →* GL (Fin 4) F :=
  emb4G.comp (tau3 hω3)

section Omega

variable {ω : Fˣ} (hω3 : ω ^ 3 = 1)

theorem τ4_injective (hω : orderOf ω = 3) : Function.Injective (τ4 hω3) :=
  emb4G_injective.comp (tau3_injective hω3 hω)

theorem coe_τ4 (v : Fin 3 → ZMod 3) :
    ((τ4 hω3 (.ofAdd v) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal fun i => ((expHom ω hω3 (.ofAdd (Sec21.TablesL44.ext v i)) : Fˣ) : F) := by
  change blk4G (tau3 hω3 (.ofAdd v)) = _
  rw [tau3_apply, blk4G_diagGL]
  congr 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · show ((((ω ^ (v 0).val) * (ω ^ (v 1).val) * (ω ^ (v 2).val))⁻¹ : Fˣ) : F) =
      ((expHom ω hω3 (.ofAdd (-(v 0 + v 1 + v 2))) : Fˣ) : F)
    congr 1
    rw [ofAdd_neg, map_inv, ofAdd_add, ofAdd_add, map_mul, map_mul]
    rfl

theorem conj_permMat_τ4 {n : GL (Fin 4) F} {σ : Equiv.Perm (Fin 4)}
    (hn : (n : Matrix (Fin 4) (Fin 4) F) = σ.toPEquiv.toMatrix) (v : Fin 3 → ZMod 3) :
    n * τ4 hω3 (.ofAdd v) * n⁻¹ =
      τ4 hω3 (.ofAdd (Sec21.TablesL44.res (Sec21.TablesL44.ext v ∘ σ))) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_τ4, coe_τ4, hn]
  have hsum : ∑ i, (Sec21.TablesL44.ext v ∘ σ) i = 0 := by
    change ∑ i, Sec21.TablesL44.ext v (σ i) = 0
    rw [Equiv.sum_comp σ (Sec21.TablesL44.ext v)]
    exact Sec21.TablesL44.sum_ext v
  rw [Sec21.TablesL44.ext_res hsum, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp only [submatrix_apply, diagonal_apply, Function.comp_apply, id]
  by_cases h : σ i = j
  · subst h
    simp
  · have h' : ¬ i = σ.symm j := fun h' => h (by rw [h', Equiv.apply_symm_apply])
    simp [h, h']

theorem τ4_comm_neg (v : Multiplicative (Fin 3 → ZMod 3)) :
    emb4G (TauCeti.diagGL ![-1, -1, 1]) * τ4 hω3 v =
      τ4 hω3 v * emb4G (TauCeti.diagGL ![-1, -1, 1]) := by
  change emb4G (TauCeti.diagGL ![-1, -1, 1]) * emb4G (tau3 hω3 v) =
    emb4G (tau3 hω3 v) * emb4G (TauCeti.diagGL ![-1, -1, 1])
  rw [← map_mul, ← map_mul]
  congr 1
  change TauCeti.diagGL ![-1, -1, 1] * TauCeti.diagGL (powVec ω hω3 v) =
    TauCeti.diagGL (powVec ω hω3 v) * TauCeti.diagGL ![-1, -1, 1]
  rw [← map_mul, ← map_mul, mul_comm (![-1, -1, 1] : Fin 3 → Fˣ)]

end Omega

variable {N : ℕ} [NeZero N] {ζ : Fˣ} (hζ : ζ ^ N = 1)

@[expose] noncomputable def τN : Multiplicative (Fin 3 → ZMod N) →* GL (Fin 4) F :=
  emb4G.comp (TauCeti.diagGL.comp (powVec ζ hζ))

theorem τN_apply (v : Multiplicative (Fin 3 → ZMod N)) :
    τN hζ v = emb4G (TauCeti.diagGL (powVec ζ hζ v)) := rfl

theorem τN_injective (hζo : orderOf ζ = N) : Function.Injective (τN hζ) :=
  emb4G_injective.comp (TauCeti.diagGL_injective.comp (powVec_injective hζ hζo))

theorem permGL3_τN (v : Fin 3 → ZMod N) :
    emb4G permGL3 * τN hζ (.ofAdd v) = τN hζ (.ofAdd (rot3 v)) * emb4G permGL3 := by
  rw [τN_apply, τN_apply, ← map_mul, ← map_mul, permGL3_mul_diagGL]
  congr 3
  funext i
  fin_cases i <;> rfl

theorem τN_eq_τ4 {a : ℕ} {ζ : Fˣ} (hζ : ζ ^ (3 ^ (a + 1)) = 1) (hω3 : (ζ ^ 3 ^ a) ^ 3 = 1)
    (k : Fin 3 → ZMod 3) :
    τN hζ (.ofAdd fun i => ((3 ^ a * (k i).val : ℕ) : ZMod (3 ^ (a + 1)))) =
      τ4 hω3 (.ofAdd k) := by
  rw [τN_apply]
  change emb4G (TauCeti.diagGL (powVec ζ hζ _)) = emb4G (tau3 hω3 (.ofAdd k))
  rw [tau3_apply]
  congr 2
  funext i
  have hlt : 3 ^ a * (k i).val < 3 ^ (a + 1) := by
    have h3 := ZMod.val_lt (k i)
    calc 3 ^ a * (k i).val < 3 ^ a * 3 := Nat.mul_lt_mul_of_pos_left h3 (by positivity)
      _ = 3 ^ (a + 1) := by rw [pow_succ]
  rw [powVec_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, pow_mul]

end Torus

section Move

variable {F : Type} [Field F] [Finite F] {G : Subgroup (GL (Fin 4) F)}

theorem e27Move_of_torus4 {a k : ℕ} {ζ : Fˣ} (hζo : orderOf ζ = 3 ^ (a + 1))
    (hT : ∀ t : Fin 3 → Fˣ, (∀ i, t i ^ (3 ^ (a + 1)) = 1) → emb4G (TauCeti.diagGL t) ∈ G)
    (hw : emb4G permGL3 ∈ G)
    (hP : ∀ σ : Equiv.Perm (Fin 4), Equiv.Perm.sign σ = 1 →
      ∃ n ∈ G, (n : Matrix (Fin 4) (Fin 4) F) = σ.toPEquiv.toMatrix)
    (hcard : Nat.card G = 3 ^ (3 * (a + 1) + 1) * k) (hk : ¬ 3 ∣ k) : E27Move G := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (1 < 3 ^ (a + 1)) := ⟨Nat.one_lt_pow (by omega) (by norm_num)⟩
  have hζ : ζ ^ (3 ^ (a + 1)) = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hmem : ∀ v, τN hζ v ∈ G := by
    intro v
    rw [τN_apply]
    refine hT _ fun i => ?_
    obtain ⟨u, rfl⟩ := Multiplicative.ofAdd.surjective v
    rw [powVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  let τ : Multiplicative (Fin 3 → ZMod (3 ^ (a + 1))) →* G := (τN hζ).codRestrict G hmem
  have hτ : Function.Injective τ := fun x y h => τN_injective hζ hζo (congrArg Subtype.val h)
  let w : G := ⟨emb4G permGL3, hw⟩
  have hw3 : w ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    change emb4G permGL3 ^ 3 = 1
    rw [← map_pow, permGL3_pow_three, map_one]
  have hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (rot3 v)) * w := fun v =>
    Subtype.ext (permGL3_τN hζ v)
  have hV : Nat.card (Fin 3 → ZMod (3 ^ (a + 1))) = 3 ^ (3 * (a + 1)) := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul, mul_comm]
  obtain ⟨P₀, hP₀⟩ := exists_sylow_torusExt hτ hw3 hwτ rot3_ne hV hcard hk
  set ω : Fˣ := ζ ^ 3 ^ a with hωdef
  have hωo : orderOf ω = 3 := by
    rw [hωdef, orderOf_pow_of_dvd (by positivity)
      (by rw [hζo]; exact pow_dvd_pow 3 (Nat.le_succ a)), hζo, pow_succ,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hω3 : ω ^ 3 = 1 := by rw [← hωo]; exact pow_orderOf_eq_one ω
  have hmem4 : ∀ v, τ4 hω3 v ∈ G := by
    intro v
    obtain ⟨u, rfl⟩ := Multiplicative.ofAdd.surjective v
    rw [← τN_eq_τ4 hζ hω3 u]
    exact hmem _
  let τ₃ : Multiplicative (Fin 3 → ZMod 3) →* G := (τ4 hω3).codRestrict G hmem4
  have hτ₃ : Function.Injective τ₃ := fun x y h =>
    τ4_injective hω3 hωo (congrArg Subtype.val h)
  set E₀ := torusOmega τ₃ with hE₀def
  have hE₀card : Nat.card E₀ = 27 := by
    rw [hE₀def, card_torusOmega hτ₃, card_V3_three]
    norm_num
  have hE₀T : E₀ ≤ torusOmega τ := by
    rintro _ ⟨u, -, rfl⟩
    refine ⟨fun i => ((3 ^ a * (u i).val : ℕ) : ZMod (3 ^ (a + 1))), ?_, ?_⟩
    · funext i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [← Nat.cast_mul, ← mul_assoc, ← pow_succ', ZMod.natCast_eq_zero_iff]
      exact Dvd.intro _ rfl
    · exact Subtype.ext (τN_eq_τ4 hζ hω3 u)
  have hTcard : Nat.card (torusOmega τ) ≤ 27 :=
    (card_torusOmega hτ).trans_le (card_torsion_le (3 ^ (a + 1)))
  have hE₀eq : E₀ = torusOmega τ :=
    Subgroup.eq_of_le_of_card_ge hE₀T (by rw [hE₀card]; exact hTcard)
  have hconj : ∀ E : Subgroup G, Late.IsE27 E →
      ∃ x : G, E.map (MulAut.conj x).toMonoidHom = E₀ := by
    intro E hE
    have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [hE.2]; norm_num)
    obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P₀ Q
    have hle : E.map (MulAut.conj h⁻¹).toMonoidHom ≤ P₀ := map_conj_inv_le hh hEQ
    rw [hP₀] at hle
    have hfix : 3 * Nat.card {u : Fin 3 → ZMod (3 ^ (a + 1)) // rot3 u = u ∧ 3 • u = 0} <
        Nat.card (torusOmega τ) := by
      have := card_fix_torsion_le (3 ^ (a + 1))
      rw [← hE₀eq, hE₀card]
      omega
    have hN : ∀ v : Fin 3 → ZMod (3 ^ (a + 1)), v + rot3 v + rot3 (rot3 v) = 0 →
        ∃ s c, v = rot3 s - s + c ∧ rot3 c = c ∧ 3 • c = 0 :=
      fun v hv => ⟨![0, -v 1, v 0], 0, by rw [add_zero]; exact rot3_norm v hv, map_zero _,
        smul_zero _⟩
    obtain ⟨-, heq⟩ := card_le_of_le_torusExt hτ hw3 hwτ hN hfix (isElemAbelian_map _ hE.1) hle
    refine ⟨h⁻¹, ?_⟩
    rw [hE₀eq]
    apply heq
    rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, hE.2, ← hE₀eq, hE₀card]
  have hmv : ∀ s ∈ E₀, s ≠ 1 → ∃ n ∈ Subgroup.normalizer (E₀ : Set G),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set G) := by
    rintro _ ⟨u, -, rfl⟩ hs1
    have hu : u ≠ 0 := fun h => hs1 (by rw [h, ofAdd_zero, map_one])
    obtain ⟨σ, hσs, hσ⟩ := move_U45 u hu
    obtain ⟨n, hnG, hn⟩ := hP σ hσs
    have hconjτ : ∀ b : Fin 3 → ZMod 3, (⟨n, hnG⟩ : G) * τ₃ (.ofAdd b) * (⟨n, hnG⟩ : G)⁻¹ =
        τ₃ (.ofAdd (Sec21.TablesL44.res (Sec21.TablesL44.ext b ∘ σ))) := fun b =>
      Subtype.ext (conj_permMat_τ4 hω3 hn b)
    have hE : E₀.map (MulAut.conj (⟨n, hnG⟩ : G)).toMonoidHom = E₀ := by
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
        refine ⟨Sec21.TablesL44.res (Sec21.TablesL44.ext b ∘ σ),
          KFacts.KS21.L44.three_smul_V3 _, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hconjτ b]
      · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
    have hns : (⟨n, hnG⟩ : G) * τ₃ (.ofAdd u) * (⟨n, hnG⟩ : G)⁻¹ ∉
        Subgroup.zpowers (τ₃ (.ofAdd u)) := by
      rw [hconjτ u]
      intro hz
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← map_zpow] at hj
      have h2 := congrArg Multiplicative.toAdd (hτ₃ hj)
      rw [toAdd_zpow_zmod, toAdd_ofAdd] at h2
      exact hσ (j : ZMod 3) h2.symm
    exact ⟨_, (mover_of_conj hE hns).1, (mover_of_conj hE hns).2⟩
  exact e27Move_of_conj hconj hmv

end Move

section Proj

variable {F : Type} [Field F] {G : Subgroup (GL (Fin 4) F)}

@[expose] noncomputable def piG (G : Subgroup (GL (Fin 4) F)) :
    G →* CFSG.Assembly.RankThreeEven.projImage G :=
  ProjGenLinGroup.mk.subgroupMap G

theorem piG_surjective : Function.Surjective (piG G) := MonoidHom.subgroupMap_surjective _ _

theorem exists_scalar_of_mem_ker_piG {z : G} (hz : z ∈ (piG G).ker) :
    ∃ c : Fˣ, GeneralLinearGroup.scalar (Fin 4) c = (z : GL (Fin 4) F) := by
  rw [MonoidHom.mem_ker] at hz
  have h : ProjGenLinGroup.mk (z : GL (Fin 4) F) = 1 := congrArg Subtype.val hz
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  exact h

theorem piG_ker (hG : G ≤ CFSG.Open.StatedSL 4 F) (z : G) (hz : z ∈ (piG G).ker)
    (hz3 : z ^ 3 = 1) : z = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_ker_piG hz
  have hdet : GeneralLinearGroup.det (z : GL (Fin 4) F) = 1 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply, Units.val_one]
                  exact CFSG.Open.StatedAPI.det_of_mem_statedSL (hG z.2))
  rw [← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hc3 : c ^ 3 = 1 := by
    have h := congrArg Subtype.val hz3
    rw [Subgroup.coe_pow, ← hc, ← map_pow] at h
    apply Units.ext
    have := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) 0 0) h
    simpa [GeneralLinearGroup.scalar, diagonal_pow] using this
  have hc1 : c = 1 := by
    have h4 : c ^ 4 = c ^ 3 * c := pow_succ c 3
    rw [hdet, hc3, one_mul] at h4
    exact h4.symm
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem piG_injOn (hG : G ≤ CFSG.Open.StatedSL 4 F) {B : Subgroup G}
    (hB : ∀ x ∈ B, x ^ 3 = 1) : Function.Injective ((piG G).comp B.subtype) := by
  intro x y hxy
  have h1 : (x : G) * (y : G)⁻¹ ∈ (piG G).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    exact mul_inv_eq_one.mpr hxy
  have h2 := piG_ker hG _ h1 (hB _ (B.mul_mem x.2 (B.inv_mem y.2)))
  exact Subtype.ext (mul_inv_eq_one.mp h2)

theorem card_map_piG (hG : G ≤ CFSG.Open.StatedSL 4 F) {B : Subgroup G}
    (hB : ∀ x ∈ B, x ^ 3 = 1) : Nat.card (B.map (piG G)) = Nat.card B := by
  have hr : ((piG G).comp B.subtype).range = B.map (piG G) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective (piG_injOn hG hB)).toEquiv]

theorem e27Move_projImage [Finite F] (hG : G ≤ CFSG.Open.StatedSL 4 F) (h : E27Move G) :
    E27Move (CFSG.Assembly.RankThreeEven.projImage G) :=
  E27Move.of_surjective (piG G) piG_surjective (piG_ker hG) h

variable {ω : Fˣ} (hω3 : ω ^ 3 = 1)

theorem exists_e27_projImage (hG : G ≤ CFSG.Open.StatedSL 4 F) (hω : orderOf ω = 3)
    (hmem4 : ∀ v, τ4 hω3 v ∈ G) :
    ∃ E : Subgroup (CFSG.Assembly.RankThreeEven.projImage G), Late.IsE27 E := by
  let τ₃ : Multiplicative (Fin 3 → ZMod 3) →* G := (τ4 hω3).codRestrict G hmem4
  have hτ₃ : Function.Injective τ₃ := fun x y h =>
    τ4_injective hω3 hω (congrArg Subtype.val h)
  have hTe : CFSG.Assembly.IsElemAbelian 3 (torusOmega τ₃) := isElemAbelian_torusOmega _
  refine ⟨(torusOmega τ₃).map (piG G), isElemAbelian_map _ hTe, ?_⟩
  rw [card_map_piG hG fun x hx => hTe.2 x hx, card_torusOmega hτ₃, card_V3_three]
  norm_num

theorem invE9_projImage (hG : G ≤ CFSG.Open.StatedSL 4 F) (hω : orderOf ω = 3)
    (hmem4 : ∀ v, τ4 hω3 v ∈ G) (ht : emb4G (TauCeti.diagGL ![-1, -1, 1]) ∈ G)
    (h2 : (2 : F) ≠ 0) :
    InvE9 (CFSG.Assembly.RankThreeEven.projImage G) := by
  let τ₃ : Multiplicative (Fin 3 → ZMod 3) →* G := (τ4 hω3).codRestrict G hmem4
  have hτ₃ : Function.Injective τ₃ := fun x y h =>
    τ4_injective hω3 hω (congrArg Subtype.val h)
  set T := torusOmega τ₃ with hT
  set F₀ : Subgroup G := (τ₃.comp incl2).range with hF₀
  have hF₀T : F₀ ≤ T := by
    rintro _ ⟨v, rfl⟩
    exact ⟨Multiplicative.toAdd (incl2 v), KFacts.KS21.L44.three_smul_V3 _, rfl⟩
  have hTe : CFSG.Assembly.IsElemAbelian 3 T := isElemAbelian_torusOmega _
  have hT3 : ∀ x ∈ T, x ^ 3 = 1 := fun x hx => hTe.2 x hx
  have hF₀e : CFSG.Assembly.IsElemAbelian 3 F₀ := isElemAbelian_mono hF₀T hTe
  have hTc : Nat.card T = 27 := by
    rw [hT, card_torusOmega hτ₃, card_V3_three]
    norm_num
  have hF₀c : Nat.card F₀ = 9 := by
    rw [hF₀, ← Nat.card_congr (MonoidHom.ofInjective (f := τ₃.comp incl2)
      (fun x y h => incl2_injective (hτ₃ h))).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
    norm_num
  let t : G := ⟨emb4G (TauCeti.diagGL ![-1, -1, 1]), ht⟩
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    change emb4G (TauCeti.diagGL ![-1, -1, 1]) ^ 2 = 1
    rw [← map_pow, ← map_pow]
    have : (![-1, -1, 1] : Fin 3 → Fˣ) ^ 2 = 1 := by
      funext i
      fin_cases i <;> simp
    rw [this, map_one, map_one]
  have ht1 : piG G t ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := exists_scalar_of_mem_ker_piG (G := G) (z := t)
      (by rw [MonoidHom.mem_ker]; exact h)
    have h0 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) 0 0) hc
    have h3 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) 3 3) hc
    change _ = blk4G (TauCeti.diagGL ![-1, -1, 1]) 0 0 at h0
    change _ = blk4G (TauCeti.diagGL ![-1, -1, 1]) 3 3 at h3
    rw [blk4G_diagGL] at h0 h3
    simp [GeneralLinearGroup.scalar] at h0 h3
    have hm : ((-1 : Fˣ) : F) = 1 := by rw [← h0, h3, Units.val_one]
    apply h2
    simp only [Units.val_neg, Units.val_one] at hm
    linear_combination -hm
  refine ⟨F₀.map (piG G), T.map (piG G), Subgroup.map_mono hF₀T, isElemAbelian_map _ hF₀e,
    by rw [card_map_piG hG fun x hx => hT3 x (hF₀T hx), hF₀c],
    ⟨isElemAbelian_map _ hTe, by rw [card_map_piG hG hT3, hTc]⟩, piG G t, ht1,
    by rw [← map_pow, ht2, map_one], ?_⟩
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (τ4_comm_neg hω3 _)

end Proj

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
