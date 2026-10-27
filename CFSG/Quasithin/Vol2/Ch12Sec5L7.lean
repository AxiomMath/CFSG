module

public import CFSG.Quasithin.Vol2.Ch12Sec5L7m
public import CFSG.Quasithin.Vol2.Ch12Sec5L6
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Lower
public import CFSG.Quasithin.Background.B3Four2
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B3Q

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St Matrix
open scoped IsMulCommutative commutatorElement

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
local notation "W10" => Fin 10 → ZMod 2

namespace S125L7

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] noncomputable def psiL (F : Frame125 T L V) : SL5 →* MulAut ↥V :=
  (autOn L V).subtype.comp F.γ.symm.toMonoidHom

omit [Finite G] in
theorem psiL_injective (F : Frame125 T L V) : Function.Injective (psiL F) :=
  Subtype.val_injective.comp F.γ.symm.injective

omit [Finite G] in
theorem range_psiL (F : Frame125 T L V) : (psiL F).range = autOn L V := by
  ext a
  constructor
  · rintro ⟨u, rfl⟩
    exact (F.γ.symm u).2
  · intro ha
    refine ⟨F.γ ⟨a, ha⟩, ?_⟩
    change ((F.γ.symm (F.γ ⟨a, ha⟩) : ↥(autOn L V)) : MulAut ↥V) = a
    rw [MulEquiv.symm_apply_apply]

omit [Finite G] in
theorem e_psiL (F : Frame125 T L V) (u : SL5) (v : ↥V) :
    Multiplicative.toAdd (F.e (psiL F u v)) =
      JonesParshall.wedgeRep u (Multiplicative.toAdd (F.e v)) := by
  change Multiplicative.toAdd (F.e (((F.γ.symm u : ↥(autOn L V)) : MulAut ↥V) v)) = _
  rw [F.wedge, MulEquiv.apply_symm_apply, toAdd_ofAdd]

omit [Finite G] in
theorem psiL_fix_iff (F : Frame125 T L V) (u : SL5) (v : ↥V) :
    psiL F u v = v ↔ JonesParshall.wedgeRep u (Multiplicative.toAdd (F.e v)) =
      Multiplicative.toAdd (F.e v) := by
  rw [← e_psiL, Multiplicative.toAdd.injective.eq_iff, F.e.injective.eq_iff]

@[expose] noncomputable def psiI (F : Frame125 T L V) (hV : IsElemAbelian 2 V) :
    SL5 →* MulAut (IntMod V hV) :=
  psiL F

omit [Finite G] in
theorem psiI_injective (F : Frame125 T L V) (hV : IsElemAbelian 2 V) :
    Function.Injective (psiI F hV) :=
  psiL_injective F

omit [Finite G] in
theorem psiI_fix_iff (F : Frame125 T L V) (hV : IsElemAbelian 2 V) (u : SL5) (v : IntMod V hV) :
    psiI F hV u v = v ↔ JonesParshall.wedgeRep u (Multiplicative.toAdd (F.e v)) =
      Multiplicative.toAdd (F.e v) :=
  psiL_fix_iff F u v

theorem padicValNat_lt_three {n : ℕ} (h0 : n ≠ 0) (h4 : n ≤ 4) : padicValNat 2 n < 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  interval_cases n
  · exact absurd rfl h0
  · simp
  · simp
  · rw [padicValNat.eq_zero_of_not_dvd (by norm_num)]
    norm_num
  · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    norm_num

omit [Finite G] in
theorem eq_map_urad (F : Frame125 T L V) (hV : IsElemAbelian 2 V) {K : Subgroup G}
    (hKT : K ≤ T) (hA : autI hV K ∈ E3.aSet 3 (autI hV ⊤)) :
    autOn K V = S125L7m.Urad.map (psiL F) := by
  obtain ⟨-, hA1, hAel, hAfix⟩ := hA
  have hAL : autOn K V ≤ autOn L V := (A4.autOn_mono hKT).trans (S125St.autOn_T_le F)
  set E : Subgroup SL5 := (autOn K V).comap (psiL F) with hE
  have hEA : E.map (psiL F) = autOn K V := by
    rw [hE, Subgroup.map_comap_eq, range_psiL, inf_of_le_right hAL]
  have h1 : ∀ u ∈ E, IsUpperTri u := by
    intro u hu
    have hmem : psiL F u ∈ autOn T V := A4.autOn_mono hKT hu
    obtain ⟨t, htN, htT, hta⟩ := mem_autOn_iff_exists.mp hmem
    obtain ⟨u', hu', hact⟩ := F.borel t htT
    have heq : psiL F u' = psiL F u := by
      rw [← hta]
      refine MulEquiv.ext fun v => F.e.injective (Multiplicative.toAdd.injective ?_)
      rw [e_psiL, hact v (conjAct V ⟨t, htN⟩ v) rfl, toAdd_ofAdd]
    rw [← psiL_injective F heq]
    exact hu'
  have h2 : ∀ u ∈ E, u * u = 1 := by
    intro u hu
    have hsq : psiL F u ^ 2 = 1 := hAel.2 (psiL F u) hu
    apply psiL_injective F
    rw [map_mul, map_one, ← pow_two]
    exact hsq
  have h3 : E ≠ ⊥ := by
    intro h
    apply hA1
    change autOn K V = ⊥
    rw [← hEA, h, Subgroup.map_bot]
  have h4 : ∀ B : Subgroup SL5, B ≤ E → B.relIndex E ≤ 4 → ∀ x : W10,
      (∀ u ∈ B, JonesParshall.wedgeRep u x = x) → ∀ u ∈ E, JonesParshall.wedgeRep u x = x := by
    intro B hBE hBi x hx u hu
    have hBA : B.map (psiL F) ≤ autOn K V := hEA ▸ Subgroup.map_mono hBE
    have hrel : (B.map (psiL F)).relIndex (autOn K V) = B.relIndex E := by
      rw [← hEA]
      exact Subgroup.relIndex_map_map_of_injective _ _ (psiL_injective F)
    have hm : E3.mQuot (autOn K V) (B.map (psiL F)) < 3 := by
      unfold E3.mQuot
      rw [hrel]
      exact padicValNat_lt_three (Subgroup.index_ne_zero_of_finite) hBi
    have hfixB := hAfix (B.map (psiL F)) hBA hm
    set v : ↥V := F.e.symm (Multiplicative.ofAdd x) with hvdef
    have hvx : Multiplicative.toAdd (F.e v) = x := by
      rw [hvdef, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have hvB : (show IntMod V hV from v) ∈ fixV (V := IntMod V hV) (B.map (psiL F)) := by
      rintro _ ⟨w, hw, rfl⟩
      change psiL F w v = v
      rw [psiL_fix_iff, hvx]
      exact hx w hw
    rw [hfixB] at hvB
    have h5 : psiL F u v = v := hvB (psiL F u) hu
    rwa [psiL_fix_iff, hvx] at h5
  rw [← hEA, S125L7m.eq_urad h1 h2 h3 h4]

omit [Finite G] in
theorem card_map_urad (F : Frame125 T L V) : Nat.card (S125L7m.Urad.map (psiL F)) = 16 := by
  rw [Subgroup.card_map_of_injective (psiL_injective F), S125L7m.card_Urad]

@[expose] def fixSub (u : SL5) : Subgroup (Multiplicative W10) where
  carrier := {y | JonesParshall.wedgeRep u (Multiplicative.toAdd y) = Multiplicative.toAdd y}
  one_mem' := by
    change JonesParshall.wedgeRep u 0 = 0
    rw [map_zero]
  mul_mem' := fun {a b} ha hb => by
    change JonesParshall.wedgeRep u (Multiplicative.toAdd a + Multiplicative.toAdd b) =
      Multiplicative.toAdd a + Multiplicative.toAdd b
    rw [map_add, show JonesParshall.wedgeRep u (Multiplicative.toAdd a) = _ from ha,
      show JonesParshall.wedgeRep u (Multiplicative.toAdd b) = _ from hb]
  inv_mem' := fun {a} ha => by
    change JonesParshall.wedgeRep u (-Multiplicative.toAdd a) = -Multiplicative.toAdd a
    rw [map_neg, show JonesParshall.wedgeRep u (Multiplicative.toAdd a) = _ from ha]

theorem coordSub_le_fixSub (b : Fin 4 → ZMod 2) :
    coordSub {0, 1, 2, 4, 5, 7} ≤ fixSub (S125L7m.Ub b) := by
  refine S125Ir.coordSub_le fun l hl => ?_
  change JonesParshall.wedgeRep (S125L7m.Ub b) (Pi.single l 1) = Pi.single l 1
  rw [S125ZV.wedgeRep_apply]
  refine S125L7m.ub_fix_V6 b l ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  tauto

omit [Finite G] in
theorem gammaCheck_eq_top (F : Frame125 T L V) (hV : IsElemAbelian 2 V) {K : Subgroup G}
    (hAeq : autOn K V = S125L7m.Urad.map (psiL F)) :
    E3.gammaCheck 3 (autI hV K) = ⊤ := by
  have hAeq' : autI hV K = S125L7m.Urad.map (psiI F hV) := hAeq
  have hcardA : Nat.card (autI hV K) = 16 := by
    rw [hAeq', Subgroup.card_map_of_injective (psiI_injective F hV), S125L7m.card_Urad]
  have hX : ∀ b : Fin 4 → ZMod 2, b ≠ 0 →
      fixV (Subgroup.zpowers (psiI F hV (S125L7m.Ub b))) ≤ E3.gammaCheck 3 (autI hV K) := by
    intro b hb
    have hmem : psiI F hV (S125L7m.Ub b) ∈ autI hV K :=
      hAeq' ▸ Subgroup.mem_map_of_mem _ (S125L7m.Ub_mem b)
    have hle : Subgroup.zpowers (psiI F hV (S125L7m.Ub b)) ≤ autI hV K :=
      (Subgroup.zpowers_le (G := MulAut (IntMod V hV))).2 hmem
    have hz : Nat.card (Subgroup.zpowers (psiI F hV (S125L7m.Ub b))) = 2 := by
      rw [Nat.card_zpowers, orderOf_injective _ (psiI_injective F hV), S125L7m.orderOf_Ub hb]
    have hrel : (Subgroup.zpowers (psiI F hV (S125L7m.Ub b))).relIndex (autI hV K) = 8 := by
      have := Subgroup.relIndex_mul_card (H := Subgroup.zpowers (psiI F hV (S125L7m.Ub b)))
        (K := autI hV K)
      rw [inf_of_le_left hle, hz, hcardA] at this
      omega
    have hm : E3.mQuot (autI hV K) (Subgroup.zpowers (psiI F hV (S125L7m.Ub b))) ≤ 3 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      unfold E3.mQuot
      rw [hrel, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
    unfold E3.gammaCheck
    exact le_iSup_of_le (Subgroup.zpowers (psiI F hV (S125L7m.Ub b)))
      (le_iSup_of_le hle (le_iSup_of_le hm le_rfl))
  rw [eq_top_iff]
  intro v _
  set x := Multiplicative.toAdd (F.e v) with hx
  set c : Fin 4 → ZMod 2 := ![x 3, x 6, x 8, x 9] with hc
  set lam : W10 := x - S125L7m.xb c with hlam
  have hlamS : Multiplicative.ofAdd lam ∈ coordSub {0, 1, 2, 4, 5, 7} := by
    intro k hk
    rw [toAdd_ofAdd, hlam, Pi.sub_apply]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    fin_cases k <;> simp_all [S125L7m.xb]
  set v₁ : ↥V := F.e.symm (Multiplicative.ofAdd lam) with hv₁def
  set v₂ : ↥V := F.e.symm (Multiplicative.ofAdd (S125L7m.xb c)) with hv₂def
  have hv : (v : ↥V) = v₁ * v₂ := by
    apply F.e.injective
    rw [map_mul, hv₁def, hv₂def, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      ← ofAdd_add, hlam, sub_add_cancel, hx, ofAdd_toAdd]
  have hv' : v = IntMod.mk hV v₁ * IntMod.mk hV v₂ := hv
  have hb₀ : (![1, 0, 0, 0] : Fin 4 → ZMod 2) ≠ 0 := fun h => by
    have := congrFun h 0
    simp at this
  have hv₁ : IntMod.mk hV v₁ ∈
      fixV (Subgroup.zpowers (psiI F hV (S125L7m.Ub ![1, 0, 0, 0]))) := by
    refine S125L6a.mem_fixV_zpowers_iff.2 ((psiI_fix_iff F hV _ _).2 ?_)
    change JonesParshall.wedgeRep _ (Multiplicative.toAdd (F.e v₁)) = Multiplicative.toAdd (F.e v₁)
    rw [hv₁def, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    exact coordSub_le_fixSub _ hlamS
  have hv₂ : IntMod.mk hV v₂ ∈ E3.gammaCheck 3 (autI hV K) := by
    by_cases hc0 : c = 0
    · have h1 : v₂ = 1 := by
        apply F.e.injective
        rw [hv₂def, MulEquiv.apply_symm_apply, map_one, hc0]
        have : S125L7m.xb 0 = 0 := by decide
        rw [this, ofAdd_zero]
      have h1' : IntMod.mk hV v₂ = 1 := h1
      rw [h1']
      exact Subgroup.one_mem _
    · refine hX c hc0 (S125L6a.mem_fixV_zpowers_iff.2 ((psiI_fix_iff F hV _ _).2 ?_))
      change JonesParshall.wedgeRep _ (Multiplicative.toAdd (F.e v₂)) =
        Multiplicative.toAdd (F.e v₂)
      rw [hv₂def, MulEquiv.apply_symm_apply, toAdd_ofAdd, S125ZV.wedgeRep_apply]
      exact S125L7m.ub_fix_xb c
  rw [hv']
  exact Subgroup.mul_mem _ (hX _ hb₀ hv₁) hv₂

omit [Finite G] in
theorem commutator_eq_V6 (F : Frame125 T L V) {K : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hAeq : autOn K V = S125L7m.Urad.map (psiL F)) :
    ⁅V, K⁆ = F.V6 := by
  have hcomm : ∀ (v : ↥V) (k : G) (hk : k ∈ K),
      ((v * (conjAct V ⟨k, hKN hk⟩ v)⁻¹ : ↥V) : G) = ⁅(v : G), k⁆ := by
    intro v k hk
    change (v : G) * (k * (v : G) * k⁻¹)⁻¹ = (v : G) * k * (v : G)⁻¹ * k⁻¹
    group
  have hcoords : ∀ (v : ↥V) (u : SL5), Multiplicative.toAdd (F.e (v * (psiL F u v)⁻¹)) =
      Multiplicative.toAdd (F.e v) - JonesParshall.wedgeRep u (Multiplicative.toAdd (F.e v)) := by
    intro v u
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, e_psiL, sub_eq_add_neg]
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g hg k hk
    have hmem : conjAct V ⟨k, hKN hk⟩ ∈ autOn K V :=
      mem_autOn_iff_exists.mpr ⟨k, hKN hk, hk, rfl⟩
    rw [hAeq] at hmem
    obtain ⟨u, ⟨b, hb⟩, hu⟩ := hmem
    set v : ↥V := ⟨g, hg⟩
    rw [show g = (v : G) from rfl, ← hcomm v k hk, ← hu]
    refine (mem_sub_iff F _ _).2 fun j hj => ?_
    rw [hcoords, S125ZV.wedgeRep_apply, hb]
    have hrow := congrArg (fun M => M *ᵥ Multiplicative.toAdd (F.e v)) (S125L7m.ub_rows b)
    rw [← Matrix.mulVec_mulVec] at hrow
    have hj' := congrFun hrow j
    rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal] at hj'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    have hmask : (![0, 0, 0, 1, 0, 0, 1, 0, 1, 1] : W10) j = 1 := by
      fin_cases j <;> simp_all
    rw [hmask, one_mul, one_mul] at hj'
    rw [Pi.sub_apply, hj', sub_self]
  · have hV6 : F.V6 ≤ V := Subgroup.map_subtype_le _
    rw [← S125Ir.coordOf_le_iff F hV6, Frame125.V6, S125Ir.coordOf_sub]
    refine S125Ir.coordSub_le fun l hl => ?_
    rw [S125Ir.mem_coordOf]
    have hmem : psiL F (S125L7m.Ub (S125L7m.bsrc l)) ∈ autOn K V :=
      hAeq ▸ Subgroup.mem_map_of_mem _ (S125L7m.Ub_mem _)
    obtain ⟨k, hkN, hk, hku⟩ := mem_autOn_iff_exists.mp hmem
    set v₀ : ↥V := F.e.symm (Multiplicative.ofAdd (Pi.single (S125L7m.src l) 1))
    have he : F.e.symm (Multiplicative.ofAdd (Pi.single l 1)) =
        v₀ * (psiL F (S125L7m.Ub (S125L7m.bsrc l)) v₀)⁻¹ := by
      apply F.e.injective
      apply Multiplicative.toAdd.injective
      rw [hcoords, MulEquiv.apply_symm_apply, toAdd_ofAdd, MulEquiv.apply_symm_apply, toAdd_ofAdd,
        S125ZV.wedgeRep_apply]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      exact S125L7m.single_eq_comm l hl
    rw [he, ← hku, hcomm v₀ k hk]
    exact Subgroup.commutator_mem_commutator v₀.2 hk

omit [Finite G] in
theorem commutator_le_left' {H K : Subgroup G} (hK : K ≤ Subgroup.normalizer (H : Set G)) :
    ⁅H, K⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro h hh k hk
  have h1 : k * h⁻¹ * k⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 (hK hk) h⁻¹).1 (H.inv_mem hh)
  rw [commutatorElement_def, show h * k * h⁻¹ * k⁻¹ = h * (k * h⁻¹ * k⁻¹) by group]
  exact H.mul_mem hh h1

omit [Finite G] in
theorem commutator_le_right' {H K : Subgroup G} (hH : H ≤ Subgroup.normalizer (K : Set G)) :
    ⁅H, K⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro h hh k hk
  have h1 : h * k * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hH hh) k).1 hk
  rw [commutatorElement_def]
  exact K.mul_mem h1 (K.inv_mem hk)

omit [Finite G] in
theorem V6_ne_bot (F : Frame125 T L V) : F.V6 ≠ ⊥ := by
  intro h
  have hmem : ((F.e.symm (Multiplicative.ofAdd (Pi.single 0 1)) : ↥V) : G) ∈ F.V6 := by
    refine (mem_sub_iff F _ _).2 fun k hk => ?_
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
    exact Pi.single_eq_of_ne (fun h0 => hk (by rw [h0]; simp)) _
  rw [h, Subgroup.mem_bot] at hmem
  have h1 : F.e.symm (Multiplicative.ofAdd (Pi.single 0 1)) = 1 := Subtype.ext hmem
  have h2 := congrArg (fun w => Multiplicative.toAdd (F.e w) 0) h1
  simp at h2

theorem key (h1222 : Stmt12_2_2) (hH : Hyp125 G T L V) (F : Frame125 T L V)
    (hV : IsElemAbelian 2 V) (h6 : Concl12_5_6 L V) {g : G} (hgT : conjSubgroup V g ≤ T)
    (hne : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) ∧ ⁅V, conjSubgroup V g⁆ = F.V6 := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hKN : conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) := hgT.trans hf.T_le
  have hKinf : conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) = conjSubgroup V g :=
    inf_of_le_left hKN
  obtain ⟨hr, -, hs⟩ := h6 hV
  have hb : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) <
      E3.sParam hV := by
    rw [hKinf, E3.mQuot_self, hs]
    norm_num
  have hA := E3.e3_10_two hV hb hne
  rw [hKinf, E3.mQuot_self, hs, Nat.sub_zero] at hA
  have hAeq := eq_map_urad F hV hgT hA
  refine ⟨?_, commutator_eq_V6 F hKN hAeq⟩
  have hw0 : E3.wParam T V = 0 := by
    have h0 : ¬ E3.wClos V 0 T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
      intro hle
      apply hne
      have hKW : conjSubgroup V g ≤ E3.wClos V 0 T :=
        le_iSup₂_of_le (f := fun A (_ : A ∈ E3.gammaSet V 0 T) => A) (conjSubgroup V g)
          ⟨hgT, g, le_rfl, E3.mQuot_self _⟩ le_rfl
      have hKC : conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) :=
        (hKW.trans hle).trans inf_le_right
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (Subgroup.le_centralizer_iff.2 hKC)
    have h1 : E3.wParam T V ≤ ((0 : ℕ) : ℕ∞) := iInf₂_le (f := fun j (_ : j ∈ {j : ℕ |
      ¬ E3.wClos V j T ≤ T ⊓ Subgroup.centralizer (V : Set G)}) => (j : ℕ∞)) 0 h0
    rw [Nat.cast_zero] at h1
    exact nonpos_iff_eq_zero.1 h1
  have hoff : E3.IsWOffenderAt T V g := ⟨hne, by rw [hw0, hKinf, E3.mQuot_self]; rfl⟩
  have hk : ((3 : ℕ) : ℕ∞) + E3.wParam T V + 1 ≤ E3.rParam V := by
    rw [hw0, add_zero, Nat.cast_ofNat]
    exact Order.add_one_le_of_lt hr
  have h32 := E3.e3_32 hV hoff hk
  rw [hKinf, gammaCheck_eq_top F hV hAeq] at h32
  intro v hv
  exact (h32 ⟨IntMod.mk hV ⟨v, hv⟩, trivial, rfl⟩).2

theorem comm_eq_bot (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (hH : Hyp125 G T L V) (F : Frame125 T L V)
    (hV : IsElemAbelian 2 V)
    (h4 : Subgroup.normalizer (F.V6 : Set G) ≤ Subgroup.normalizer (L : Set G))
    (h6 : Concl12_5_6 L V) {g : G}
    (hgT : conjSubgroup V g ≤ T) : ⁅V, conjSubgroup V g⁆ = ⊥ := by
  by_contra hne
  have hf := S125Ex.Facts125.of h1222 hH
  have hyp := hH.hyp
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hE : E6.HypE61 T M V :=
    S125L6a.hypE61_of_hyp h331 h1222 h323 h3228 hyp hV hyp.irrPlus.2.1 hf.le_T hf.T_le
      hf.normalizes
  obtain ⟨hVN, hc⟩ := key h1222 hH F hV h6 hgT hne
  have hA'N : B3.cj g V ≤ Subgroup.normalizer (V : Set G) := by
    rintro _ ⟨v, hv, rfl⟩
    have hvN := hVN hv
    rw [Subgroup.mem_normalizer_iff] at hvN ⊢
    intro z
    have h1 := hvN (g⁻¹ * z * g)
    rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff] at h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    convert h1 using 2 <;> group
  have hA'p : IsPGroup 2 (B3.cj g V) := hE.isPGroup_V.map _
  have hidx : ¬ 2 ∣ (T.subgroupOf (Subgroup.normalizer (V : Set G))).index := by
    intro h2
    apply hyp.sylow.2
    rw [← Subgroup.relIndex_mul_index hf.T_le]
    exact Dvd.dvd.mul_right h2 _
  obtain ⟨m, hmN, hm⟩ := B3.exists_conj_le_sylow_sub hf.T_le hyp.sylow.1 hidx hA'N hA'p
  have hVh : conjSubgroup V (m * g)⁻¹ = B3.cj m (B3.cj g V) := by
    ext x
    rw [mem_conjSubgroup_iff, B3.mem_cj, B3.mem_cj]
    constructor <;> intro hx <;> convert hx using 1 <;> group
  have hgT' : conjSubgroup V (m * g)⁻¹ ≤ T := hVh ▸ hm
  have hcomm' : ⁅V, conjSubgroup V (m * g)⁻¹⁆ = B3.cj (m * g) ⁅V, conjSubgroup V g⁆ := by
    have e1 : B3.cj (m * g) V = conjSubgroup V (m * g)⁻¹ := by
      ext x
      rw [mem_conjSubgroup_iff, B3.mem_cj]
      constructor <;> intro hx <;> convert hx using 1 <;> group
    have e2 : B3.cj (m * g) (conjSubgroup V g) = V := by
      ext x
      rw [B3.mem_cj, mem_conjSubgroup_iff]
      have h1 : g * ((m * g)⁻¹ * x * (m * g)) * g⁻¹ = m⁻¹ * x * m := by group
      rw [h1]
      have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hmN) x)
      rw [inv_inv] at h2
      exact h2.symm
    rw [B3.cj, Subgroup.map_commutator, ← B3.cj, ← B3.cj, e1, e2, Subgroup.commutator_comm]
  have hne' : ⁅V, conjSubgroup V (m * g)⁻¹⁆ ≠ ⊥ := by
    rw [hcomm', hc]
    intro h
    apply V6_ne_bot F
    rw [B3.cj] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj (m * g)).injective).1 h
  obtain ⟨-, hc'⟩ := key h1222 hH F hV h6 hgT' hne'
  have hfix : B3.cj (m * g) F.V6 = F.V6 := by
    calc B3.cj (m * g) F.V6 = B3.cj (m * g) ⁅V, conjSubgroup V g⁆ := by rw [hc]
      _ = ⁅V, conjSubgroup V (m * g)⁻¹⁆ := hcomm'.symm
      _ = F.V6 := hc'
  have hmgN : m * g ∈ Subgroup.normalizer (F.V6 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    conv_rhs => rw [← hfix]
    rw [B3.mem_cj, show (m * g)⁻¹ * (m * g * z * (m * g)⁻¹) * (m * g) = z by group]
  have hmgM : m * g ∈ M := h4 hmgN
  have hmM : m ∈ M := hE.normalizer_le hmN
  have hgM : g ∈ M := by
    have := M.mul_mem (M.inv_mem hmM) hmgM
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  have hgNV : g ∈ Subgroup.normalizer (V : Set G) := by
    by_contra hgN
    have hTI := hE.tiSet.2 g hgM hgN
    apply V6_ne_bot F
    rw [eq_bot_iff, ← hTI, ← hc]
    exact le_inf (commutator_le_left' (hgT.trans hf.T_le)) (commutator_le_right' hVN)
  apply hne
  have hVg : conjSubgroup V g = V := by
    ext x
    rw [mem_conjSubgroup_iff]
    exact ((Subgroup.mem_normalizer_iff.1 hgNV x)).symm
  rw [hVg]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hE.le_inf_centralizer.trans inf_le_right)

end S125L7

open S125L7

theorem lemma12_5_7_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (h4 : Lemma12_5_4six) (h6 : Lemma12_5_6) : Lemma12_5_7 := by
  intro G _ _ T L V hH
  obtain ⟨F⟩ := frame125Exists_of h1222 G T L V hH
  have hf := S125Ex.Facts125.of h1222 hH
  have hyp := hH.hyp
  have hV : IsElemAbelian 2 V := ⟨hf.comm, hf.sq⟩
  have hE : E6.HypE61 T (Subgroup.normalizer (L : Set G)) V :=
    S125L6a.hypE61_of_hyp h331 h1222 h323 h3228 hyp hV hyp.irrPlus.2.1 hf.le_T hf.T_le
      hf.normalizes
  have hW : E3.wClos V 0 T ≤ Subgroup.centralizer (V : Set G) := by
    unfold E3.wClos
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, g, hAg, hA0⟩ := hA
    have hVg2 : IsPGroup 2 (conjSubgroup V g) := hE.isPGroup_V.map _
    have hAeq : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hVg2 hAg).1 hA0
    subst hAeq
    have h1 := comm_eq_bot h331 h1222 h323 h3228 hH F hV (h4 G T L V F hH) (h6 G T L V hH) hAT
    exact Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1)
  have hWT : E3.wClos V 0 T ≤ T := iSup₂_le fun A hA => hA.1
  have hw : 0 < E3.wParam T V := by
    have h1 : (1 : ℕ∞) ≤ E3.wParam T V := by
      unfold E3.wParam
      refine le_iInf₂ fun j hj => ?_
      have hj0 : j ≠ 0 := by
        rintro rfl
        exact hj (le_inf hWT hW)
      exact_mod_cast Nat.one_le_iff_ne_zero.2 hj0
    exact lt_of_lt_of_le zero_lt_one h1
  refine ⟨hW, hw, ?_⟩
  have hrk : 0 < rk ↥V := by
    rw [rk, hf.card, padicValNat.prime_pow]
    norm_num
  exact (E3.e3_34_two hV hE.hyp322 hE.isUniqueM_normalizer_Q hrk (by exact_mod_cast hw)).1

end CFSG.Quasithin.H13
