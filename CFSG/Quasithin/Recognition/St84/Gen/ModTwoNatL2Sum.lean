module

public import CFSG.Timmesfeld.RankOne.Defs
import CFSG.RankThree.GF2n.NaturalDecomp
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule
open scoped MatrixGroups

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [DistribMulAction SL(2, F) V]

private def fixUpper (F V : Type) [Field F] [AddCommGroup V] [DistribMulAction SL(2, F) V] :
    AddSubgroup V where
  carrier := {v | ∀ a ∈ upperUnipotent F, a • v = v}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun hx hy a ha => by rw [smul_add, hx a ha, hy a ha]
  neg_mem' := fun hx a ha => by rw [smul_neg, hx a ha]

private theorem mem_fixUpper_iff {v : V} :
    v ∈ fixUpper F V ↔ ∀ t : F, upperElt F t • v = v := by
  refine ⟨fun hv t => hv _ ((mem_upperUnipotent_iff F).2 ⟨t, rfl⟩), fun hv a ha => ?_⟩
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff F).1 ha
  exact hv t

private theorem forall_smul_eq_of_upper_lower {v : V}
    (hu : ∀ t : F, upperElt F t • v = v) (hl : ∀ t : F, lowerElt F t • v = v) :
    ∀ g : SL(2, F), g • v = v :=
  sl2_induction (P := fun g => g • v = v) (one_smul _ v)
    (fun x y hx hy => by rw [mul_smul, hy, hx]) (fun x hx => inv_smul_eq_iff.mpr hx.symm) hu hl

private theorem smul_sub_mem_of_fixUpper_le [CharP F 2]
    (hquad : ∀ a ∈ upperUnipotent F, ∀ a' ∈ upperUnipotent F, ∀ v : V,
      a' • (a • v - v) = a • v - v)
    {U : AddSubgroup V} (hU : ∀ g : SL(2, F), ∀ v ∈ U, g • v ∈ U) (hAU : fixUpper F V ≤ U)
    (g : SL(2, F)) (v : V) : g • v - v ∈ U := by
  have hup : ∀ (t : F) (v : V), upperElt F t • v - v ∈ U := fun t v =>
    hAU fun a ha => hquad _ ((mem_upperUnipotent_iff F).2 ⟨t, rfl⟩) a ha v
  revert v
  refine sl2_induction (P := fun g => ∀ v : V, g • v - v ∈ U) (fun v => ?_)
    (fun x y hx hy v => ?_) (fun x hx v => ?_) hup (fun t v => ?_) g
  · rw [one_smul, sub_self]
    exact U.zero_mem
  · have h : (x * y) • v - v = x • (y • v - v) + (x • v - v) := by
      rw [mul_smul, smul_sub]
      abel
    rw [h]
    exact U.add_mem (hU x _ (hy v)) (hx v)
  · have h : x⁻¹ • v - v = -(x • (x⁻¹ • v) - x⁻¹ • v) := by
      rw [smul_inv_smul]
      abel
    rw [h]
    exact U.neg_mem (hx _)
  · have h : lowerElt F t • v - v =
        weylElt F • (upperElt F t • weylElt F • v - weylElt F • v) := by
      rw [lowerElt_smul, smul_sub, weylElt_smul_weylElt_smul]
    rw [h]
    exact hU _ _ (hup t _)

private theorem mem_fixUpper_of_diag [Finite F] [CharP F 2] {y : V}
    (hy : ∀ c : Fˣ, diagElt c • y = y) (h1 : upperElt F 1 • y = y) : y ∈ fixUpper F V := by
  refine mem_fixUpper_iff.2 fun t => ?_
  by_cases ht : t = 0
  · rw [ht, upperElt_zero, one_smul]
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' t
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact ht (by rw [hs, mul_zero])
  obtain ⟨c, hc⟩ : ∃ c : Fˣ, (c : F) = s := ⟨Units.mk0 s hs0, rfl⟩
  have e : upperElt F t = diagElt c * upperElt F 1 * (diagElt c)⁻¹ := by
    rw [diagElt_mul_upperElt, mul_assoc, mul_inv_cancel, mul_one, mul_one, hc, hs, sq]
  rw [e, mul_smul, mul_smul, inv_smul_eq_iff.mpr (hy c).symm, h1, hy]

private theorem card_le_card_mul_card_fixUpper [Finite F] [CharP F 2] [Module (ZMod 2) V]
    [Finite V]
    (hquad : ∀ a ∈ upperUnipotent F, ∀ a' ∈ upperUnipotent F, ∀ v : V,
      a' • (a • v - v) = a • v - v)
    {U : AddSubgroup V} (hU : ∀ g : SL(2, F), ∀ v ∈ U, g • v ∈ U) (hAU : fixUpper F V ≤ U) :
    Nat.card V ≤ Nat.card U * Nat.card (fixUpper F V) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h2 : 2 ∣ Fintype.card F :=
    (CharP.cast_eq_zero_iff F 2 _).mp (FiniteField.cast_card_eq_zero F)
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hodd : ((Fintype.card Fˣ : ℕ) : ZMod 2) = 1 := by
    rw [Fintype.card_units, ← ZMod.natCast_mod (Fintype.card F - 1) 2,
      show (Fintype.card F - 1) % 2 = 1 by omega, Nat.cast_one]
  let av : V →+ V :=
    { toFun := fun v => ∑ c : Fˣ, diagElt c • v
      map_zero' := by simp
      map_add' := fun v w => by simp [smul_add, Finset.sum_add_distrib] }
  have hav_apply : ∀ v, av v = ∑ c : Fˣ, diagElt c • v := fun _ => rfl
  have hav : ∀ (d : Fˣ) (v : V), diagElt d • av v = av v := by
    intro d v
    rw [hav_apply, Finset.smul_sum]
    simp_rw [← mul_smul, diagElt_mul_diagElt]
    exact Fintype.sum_equiv (Equiv.mulLeft d) _ _ fun c => rfl
  have hsub : ∀ v : V, av v - v ∈ U := by
    intro v
    have h : av v - v = ∑ c : Fˣ, (diagElt c • v - v) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hav_apply,
        ← Nat.cast_smul_eq_nsmul (ZMod 2), hodd, one_smul]
    rw [h]
    exact U.sum_mem fun c _ => smul_sub_mem_of_fixUpper_le hquad hU hAU _ v
  let Ψ : V →+ V :=
    { toFun := fun v => upperElt F 1 • av v - av v
      map_zero' := by simp
      map_add' := fun v w => by
        rw [map_add, smul_add]
        abel }
  have hrange : Ψ.range ≤ fixUpper F V := by
    rintro _ ⟨v, rfl⟩ a ha
    exact hquad _ ((mem_upperUnipotent_iff F).2 ⟨1, rfl⟩) a ha (av v)
  have hker : Ψ.ker ≤ U := by
    intro v hv
    have h1 : upperElt F 1 • av v = av v := sub_eq_zero.mp (AddMonoidHom.mem_ker.mp hv)
    have h := U.sub_mem (hAU (mem_fixUpper_of_diag (hav · v) h1)) (hsub v)
    rwa [sub_sub_cancel] at h
  rw [← AddSubgroup.card_ker_mul_card_range Ψ]
  exact Nat.mul_le_mul (AddSubgroup.card_le_of_le hker) (AddSubgroup.card_le_of_le hrange)

private theorem card_fixUpper_mul_self_le [CharP F 2] [Finite V]
    (hfix : ∀ v : V, (∀ x : SL(2, F), x • v = v) → v = 0)
    {U : AddSubgroup V} (hU : ∀ g : SL(2, F), ∀ v ∈ U, g • v ∈ U) (hAU : fixUpper F V ≤ U) :
    Nat.card (fixUpper F V) * Nat.card (fixUpper F V) ≤ Nat.card U := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p => (⟨(p.1 : V) + weylElt F • (p.2 : V),
    U.add_mem (hAU p.1.2) (hU _ _ (hAU p.2.2))⟩ : U)) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 : (a : V) + weylElt F • (b : V) = a' + weylElt F • (b' : V) := congrArg Subtype.val h
  have hz : (a : V) - a' = weylElt F • ((b' : V) - b) := by
    rw [smul_sub, sub_eq_sub_iff_add_eq_add, h1, add_comm]
  have hz0 : (a : V) - a' = 0 := by
    refine hfix _ (forall_smul_eq_of_upper_lower (fun t => ?_) (fun t => ?_))
    · exact mem_fixUpper_iff.1 ((fixUpper F V).sub_mem a.2 a'.2) t
    · rw [hz, lowerElt_smul, weylElt_smul_weylElt_smul,
        mem_fixUpper_iff.1 ((fixUpper F V).sub_mem b'.2 b.2) t]
  have hb : (b' : V) - b = 0 := by
    rw [hz0] at hz
    rw [← weylElt_smul_weylElt_smul (K := F) ((b' : V) - b), ← hz, smul_zero]
  exact Prod.ext (Subtype.ext (sub_eq_zero.mp hz0)) (Subtype.ext (sub_eq_zero.mp hb).symm)

private theorem card_sup_eq_mul_of_disjoint {M : Type*} [AddCommGroup M] {A B : AddSubgroup M}
    (h : Disjoint A B) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective (fun p : A × B => (⟨(p.1 : M) + p.2,
    AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left p.1.2)
      (AddSubgroup.mem_sup_right p.2.2)⟩ : ↥(A ⊔ B))) ⟨?_, ?_⟩)).symm
  · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 : (a : M) + b = a' + b' := congrArg Subtype.val hab
    have h3 : (a : M) - a' = b' - b := sub_eq_sub_iff_add_eq_add.2 (h1.trans (add_comm _ _))
    have h2 : (a : M) - a' ∈ A ⊓ B := ⟨A.sub_mem a.2 a'.2, by rw [h3]; exact B.sub_mem b'.2 b.2⟩
    rw [disjoint_iff.mp h, AddSubgroup.mem_bot, sub_eq_zero] at h2
    rw [h2, add_right_inj] at h1
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h1)
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

private theorem card_finsetSup_eq_prod {M : Type*} [AddCommGroup M]
    [DecidableEq (AddSubgroup M)] (s : Finset (AddSubgroup M)) (hs : s.SupIndep id) :
    Nat.card (s.sup id : AddSubgroup M) = ∏ W ∈ s, Nat.card W := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs2 : Disjoint a (s.sup id) := by
      have := Finset.supIndep_iff_disjoint_erase.mp hs a (Finset.mem_insert_self a s)
      rwa [Finset.erase_insert ha] at this
    rw [Finset.sup_insert, Finset.prod_insert ha, id, card_sup_eq_mul_of_disjoint hs2,
      ih (hs.subset (Finset.subset_insert a s))]

theorem exists_addEquiv_matrix_of_quadratic [Finite F] [CharP F 2] [Module (ZMod 2) V] [Finite V]
    (hfix : ∀ v : V, (∀ x : SL(2, F), x • v = v) → v = 0)
    (hquad : ∀ a ∈ upperUnipotent F, ∀ a' ∈ upperUnipotent F, ∀ v : V,
      a' • (a • v - v) = a • v - v)
    (hcard : Nat.card V = Nat.card F ^ 4) :
    ∃ φ : V ≃+ Matrix (Fin 2) (Fin 2) F, ∀ (g : SL(2, F)) (v : V),
      φ (g • v) = (g : Matrix (Fin 2) (Fin 2) F) * φ v := by
  classical
  have hq : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨W, hWinv, hAW, hWmin⟩ : ∃ W : AddSubgroup V, (∀ g : SL(2, F), ∀ v ∈ W, g • v ∈ W) ∧
      fixUpper F V ≤ W ∧ ∀ U : AddSubgroup V, (∀ g : SL(2, F), ∀ v ∈ U, g • v ∈ U) →
        fixUpper F V ≤ U → W ≤ U := by
    refine ⟨sInf {U | (∀ g : SL(2, F), ∀ v ∈ U, g • v ∈ U) ∧ fixUpper F V ≤ U}, ?_,
      le_sInf fun U hU => hU.2, fun U h1 h2 => sInf_le ⟨h1, h2⟩⟩
    intro g v hv
    rw [AddSubgroup.mem_sInf] at hv ⊢
    exact fun U hU => hU.1 g v (hv U hU)
  letI : DistribMulAction SL(2, F) W :=
    { smul := fun g w => ⟨g • (w : V), hWinv g w w.2⟩
      one_smul := fun w => Subtype.ext (one_smul _ (w : V))
      mul_smul := fun g g' w => Subtype.ext (mul_smul g g' (w : V))
      smul_zero := fun g => Subtype.ext (smul_zero g)
      smul_add := fun g w w' => Subtype.ext (smul_add g (w : V) w') }
  have hfixW : ∀ w : W, (∀ x : SL(2, F), x • w = w) → w = 0 := fun w hw =>
    Subtype.ext (hfix w fun x => congrArg Subtype.val (hw x))
  have hquadW : ∀ a ∈ upperUnipotent F, ∀ a' ∈ upperUnipotent F, ∀ w : W,
      a' • (a • w - w) = a • w - w := fun a ha a' ha' w =>
    Subtype.ext (hquad a ha a' ha' w)
  have hLW : ∀ w ∈ (fixUpper F V).comap W.subtype, ∀ a ∈ upperUnipotent F, a • w = w :=
    fun w hw a ha => Subtype.ext (hw a ha)
  have hgenW : ∀ U : AddSubgroup W, (∀ g : SL(2, F), ∀ v ∈ U, g • v ∈ U) →
      (fixUpper F V).comap W.subtype ≤ U → U = ⊤ := by
    intro U hU hLU
    have hle : W ≤ U.map W.subtype := by
      refine hWmin _ ?_ fun v hv => ⟨⟨v, hAW hv⟩,
        hLU (show (⟨v, hAW hv⟩ : W) ∈ (fixUpper F V).comap W.subtype from hv), rfl⟩
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨g • w, hU g w hw, rfl⟩
    rw [eq_top_iff]
    intro w _
    obtain ⟨w', hw', he⟩ := hle w.2
    rwa [Subtype.ext he] at hw'
  obtain ⟨s, hs, hsup, hsW⟩ :=
    CFSG.RankThree.GF2n.exists_supIndep_natural hfixW hquadW hLW hgenW
  have hcardW : Nat.card W = (Nat.card F ^ 2) ^ s.card := by
    rw [← AddSubgroup.card_top (G := W), ← hsup, card_finsetSup_eq_prod s hs,
      ← Finset.prod_const]
    refine Finset.prod_congr rfl fun W' hW' => ?_
    obtain ⟨-, -, -, θ, hinj, hrange, -⟩ := hsW W' hW'
    have h := (Nat.card_congr (Equiv.ofInjective θ hinj)).symm
    rw [Nat.card_fun, Nat.card_fin] at h
    rw [← hrange]
    exact h
  have h1 := card_le_card_mul_card_fixUpper hquad hWinv hAW
  have h2 := card_fixUpper_mul_self_le hfix hWinv hAW
  have h3 : Nat.card W ≤ Nat.card V := AddSubgroup.card_le_card_addGroup W
  rw [hcardW, hcard, ← pow_mul] at h3
  have hk2 : s.card ≤ 2 := by
    have := (Nat.pow_le_pow_iff_right hq).mp h3
    omega
  have hk : s.card = 2 := by
    by_contra hk
    have hW2 : Nat.card W ≤ Nat.card F * Nat.card F := by
      rw [hcardW]
      calc (Nat.card F ^ 2) ^ s.card ≤ (Nat.card F ^ 2) ^ 1 :=
            Nat.pow_le_pow_right (by positivity) (by omega)
        _ = Nat.card F * Nat.card F := by ring
    have hc : Nat.card (fixUpper F V) ≤ Nat.card F :=
      Nat.mul_self_le_mul_self_iff.mp (h2.trans hW2)
    have h4 : Nat.card V ≤ Nat.card F * Nat.card F * Nat.card F :=
      h1.trans (Nat.mul_le_mul hW2 hc)
    have h5 : Nat.card F ^ 3 < Nat.card F ^ 4 := Nat.pow_lt_pow_right hq (by norm_num)
    rw [hcard, show Nat.card F * Nat.card F * Nat.card F = Nat.card F ^ 3 by ring] at h4
    exact absurd h4 (not_le.mpr h5)
  obtain ⟨W₁, W₂, hne, rfl⟩ := Finset.card_eq_two.mp hk
  have hdis : Disjoint W₁ W₂ := (Finset.supIndep_pair hne).mp hs
  obtain ⟨-, -, -, θ₁, hinj₁, hrange₁, hθ₁⟩ := hsW W₁ (Finset.mem_insert_self _ _)
  obtain ⟨-, -, -, θ₂, hinj₂, hrange₂, hθ₂⟩ :=
    hsW W₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  let col : Fin 2 → Matrix (Fin 2) (Fin 2) F →+ (Fin 2 → F) := fun j =>
    { toFun := fun M i => M i j
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let Φ : Matrix (Fin 2) (Fin 2) F →+ V :=
    W.subtype.comp (θ₁.comp (col 0) + θ₂.comp (col 1))
  have hΦ : ∀ M, Φ M = ((θ₁ (fun i => M i 0) + θ₂ (fun i => M i 1) : W) : V) := fun _ => rfl
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun M hM => ?_
    have hM' : θ₁ (fun i => M i 0) + θ₂ (fun i => M i 1) = 0 := Subtype.ext hM
    have hmem : θ₁ (fun i => M i 0) ∈ W₁ ⊓ W₂ := by
      refine ⟨hrange₁ ▸ ⟨_, rfl⟩, ?_⟩
      rw [eq_neg_of_add_eq_zero_left hM']
      exact W₂.neg_mem (hrange₂ ▸ ⟨_, rfl⟩)
    rw [disjoint_iff.mp hdis, AddSubgroup.mem_bot] at hmem
    rw [hmem, zero_add] at hM'
    have hc₀ : (fun i => M i 0) = 0 := hinj₁ (hmem.trans (map_zero θ₁).symm)
    have hc₁ : (fun i => M i 1) = 0 := hinj₂ (hM'.trans (map_zero θ₂).symm)
    ext i j
    fin_cases j
    · exact congrFun hc₀ i
    · exact congrFun hc₁ i
  have hcardM : Nat.card (Matrix (Fin 2) (Fin 2) F) = Nat.card F ^ 4 := by
    show Nat.card (Fin 2 → Fin 2 → F) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul]
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le (by rw [hcard, hcardM])
  have hΦsmul : ∀ (g : SL(2, F)) (M : Matrix (Fin 2) (Fin 2) F),
      Φ ((g : Matrix (Fin 2) (Fin 2) F) * M) = g • Φ M := by
    intro g M
    show ((θ₁ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ fun i => M i 0) +
      θ₂ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ fun i => M i 1) : W) : V) = g • Φ M
    rw [hθ₁, hθ₂, ← smul_add, hΦ]
    rfl
  refine ⟨(AddEquiv.ofBijective Φ hbij).symm, fun g v => hbij.1 ?_⟩
  have hv : Φ ((AddEquiv.ofBijective Φ hbij).symm v) = v :=
    (AddEquiv.ofBijective Φ hbij).apply_symm_apply v
  rw [hΦsmul, hv]
  exact (AddEquiv.ofBijective Φ hbij).apply_symm_apply (g • v)

end CFSG.Quasithin.F112R.St84

end
