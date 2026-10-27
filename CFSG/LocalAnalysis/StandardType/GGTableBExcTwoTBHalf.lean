module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBFull
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBLang
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalfE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalfE8
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBToral
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8
public import CFSG.RankThree.PartOne.KE.E7FiveBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableBExc TableBExc.Three TableBExcTwo TableBExcTwoFusion ExcFrameIso
  CFSG.HardMathSupport.Timmesfeld.CrossChar

namespace TableBExcTwoTB

section Transport

private theorem conj_transport_eq {G : Type*} [Group G] (a b c d : G) :
    (c⁻¹ * b * a⁻¹)⁻¹ * d * (c⁻¹ * b * a⁻¹) =
      a * (b⁻¹ * (c * d * c⁻¹) * b) * a⁻¹ := by
  group

end Transport

section Half


section Generic

variable {τ : Tag} {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem toral_of_card_of_weylX (hτ : τ = .E7 ∨ τ = .E8) (F : OrthFrame τ d)
    (hd : d + 1 = τ.rank)
    (hw : ∀ v : Fin τ.rank → ℤ, (List.ofFn fun i => rootReflection (F.root i)).prod • v = -v)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod 3))
    (hV : Nat.card (torusPow τ (FiniteField.Extension K 2 2) 3) = 3 ^ τ.rank)
    {S : Subgroup (WeylGroup τ)} (hidx : ¬ 3 ∣ (weylX τ (FiniteField.Extension K 2 2) S).index)
    (hhalf : HalfOffender τ S) (hmon : MonomialToralAt τ 3) (hK : Nat.card K = 2)
    {E : Subgroup (adjointGroup τ K)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ (τ.rank - 1) ≤ Nat.card E) :
    ∃ g ∈ adjointGroup τ (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : adjointGroup τ K) : ModGL τ K) *
        g ∈ torusGroup τ (AlgebraicClosure K) := by
  classical
  set L := FiniteField.Extension K 2 2 with hL
  have := Fact.mk Nat.prime_three
  have h3 := three_dvd_natCard_ext_sub_one hK
  obtain ⟨ω, hωo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) (p := 3) h3
  set g := langElt F hωo with hg
  set j := adjointMap τ (algebraMap K L) with hj
  have hjinj : Function.Injective j := adjointMap_injective _
  have : Finite (adjointGroup τ L) := generated_group_finite τ L
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  have hdesc : ∀ m : adjointGroup τ L, (m : ModGL τ L) ∈ monomialSubgroup τ L →
      ∃ m₀ : adjointGroup τ K, j m₀ = g * m * g⁻¹ := fun m hm =>
    exists_adjointMap_eq_of_frob hτ (adjointMap_frob_conj_langElt hK F hw hsymm hdet hV hωo hm)
  set X := weylX τ L S with hX
  have hXj : X.map (MulAut.conj g).toMonoidHom ≤ j.range := by
    rintro _ ⟨m, hmX, rfl⟩
    obtain ⟨m₀, hm₀⟩ := hdesc m (mem_weylX.mp hmX).1
    exact ⟨m₀, hm₀⟩
  set Y := (X.map (MulAut.conj g).toMonoidHom).comap j with hY
  have hYidx : ¬ 3 ∣ Y.index := fun h => hidx (h.trans (index_comap_dvd hjinj g hXj))
  obtain ⟨x, hx⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three hYidx
    (TableB.isPGroup_of_isElemAbelian hE)
  set E' := ((E.map (MulAut.conj x).toMonoidHom).map j).map (MulAut.conj g⁻¹).toMonoidHom with
    hE'def
  have hE'X : E' ≤ X := by
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    obtain ⟨m, hmX, hm⟩ := hx hb
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hm, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    have e : g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m := by group
    rw [e]
    exact hmX
  have hE' : IsElemAbelian 3 E' :=
    TableB.isElemAbelian_map (TableB.isElemAbelian_map (TableB.isElemAbelian_map hE _) _) _
  have hcard' : Nat.card E' = Nat.card E := by
    rw [hE'def, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      Subgroup.card_map_of_injective hjinj,
      Subgroup.card_map_of_injective (MulAut.conj x).injective]
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let ψ : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  have hcomp : ψ.toRingHom.comp (algebraMap K L) = algebraMap K (AlgebraicClosure K) :=
    RingHom.ext fun a => ψ.commutes a
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hchar : ringChar (AlgebraicClosure K) ≠ 3 := by
    rw [ringChar.eq (AlgebraicClosure K) 2]
    norm_num
  obtain ⟨h, hh, hconj⟩ :=
    exists_conj_toral_of_le_weylX (τ := τ) hmon hchar ψ.toRingHom hdet hsymm hV h3 hhalf hE' hE'X
      (hcard'.symm ▸ hcard)
  set XK : adjointGroup τ (AlgebraicClosure K) :=
    adjointMap τ (algebraMap K (AlgebraicClosure K)) x with hXK
  set ψg : adjointGroup τ (AlgebraicClosure K) := adjointMap τ ψ.toRingHom g with hψg
  refine ⟨(XK : ModGL τ (AlgebraicClosure K))⁻¹ * (ψg : ModGL τ (AlgebraicClosure K)) * h⁻¹,
    mul_mem (mul_mem (inv_mem XK.2) ψg.2) (inv_mem hh), ?_⟩
  intro e he
  have he'coe : (((g⁻¹ * j (x * e * x⁻¹) * g : adjointGroup τ L)) : ModGL τ L)
      = (g : ModGL τ L)⁻¹ * baseChangeGL (algebraMap K L)
          ((x : ModGL τ K) * (e : ModGL τ K) * (x : ModGL τ K)⁻¹) * (g : ModGL τ L) := by
    simp only [hj, Subgroup.coe_mul, Subgroup.coe_inv, coe_adjointMap]
  have he'mem : g⁻¹ * j (x * e * x⁻¹) * g ∈ E' := by
    rw [hE'def]
    refine ⟨j (x * e * x⁻¹), ⟨x * e * x⁻¹, ⟨e, he, ?_⟩, rfl⟩, ?_⟩
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hbc : baseChangeGL ψ.toRingHom
        (((g⁻¹ * j (x * e * x⁻¹) * g : adjointGroup τ L)) : ModGL τ L)
      = (ψg : ModGL τ (AlgebraicClosure K))⁻¹ *
          ((XK : ModGL τ (AlgebraicClosure K)) *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) ((e : adjointGroup τ K) : ModGL τ K) *
            (XK : ModGL τ (AlgebraicClosure K))⁻¹) *
          (ψg : ModGL τ (AlgebraicClosure K)) := by
    rw [he'coe, map_mul, map_mul, map_inv, baseChangeGL_baseChangeGL, hcomp, map_mul, map_mul,
      map_inv, ← coe_adjointMap ψ.toRingHom g,
      ← coe_adjointMap (algebraMap K (AlgebraicClosure K)) x, hψg, hXK]
  have hh' := hconj (g⁻¹ * j (x * e * x⁻¹) * g) he'mem
  rw [hbc] at hh'
  rw [conj_transport_eq]
  exact hh'

end Generic

section E7


section K

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem toral_of_card_E7 (hK : Nat.card K = 2) {E : Subgroup (adjointGroup .E7 K)}
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 6 ≤ Nat.card E) :
    ∃ g ∈ adjointGroup .E7 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .E7 K) : ModGL .E7 K) * g ∈ torusGroup .E7 (AlgebraicClosure K) := by
  have h3 := three_dvd_natCard_ext_sub_one hK
  exact toral_of_card_of_weylX (hτ := Or.inl rfl) (F := frameE7) (hd := rfl)
    (hw := frameE7_reflections) (hsymm := cartan_symm_E7)
    (hdet := isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E7 (by norm_num))
    (hV := card_torusPow_E7 (K := FiniteField.Extension K 2 2) Nat.prime_three h3)
    (S := modelHomE7.range) (hidx := not_three_dvd_index_E7 h3)
    (hhalf := halfOffender_E7) (hmon := monomialToralAt_three_of_block a2BlockToral_E7)
    (hK := hK) (E := E) (hE := hE) (hcard := hcard)

theorem exists_conj_frame_of_card_half_E7 (hK : Nat.card K = 2)
    {E : Subgroup (adjointGroup .E7 K)} (hE : IsElemAbelian 3 E) (hcard : 3 ^ 6 ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .E7 K)), x ^ 3 = 1 → x ∈ E) :
    ∃ c : adjointGroup .E7 K, E = (tE K frameE7).range.map (MulAut.conj c).toMonoidHom := by
  have hge : 3 ^ 7 ≤ Nat.card E :=
    ExcFramesHalf.card_ge_of_toral' (Or.inl rfl) Nat.prime_three (by norm_num)
      (ExcFramesHalf.halfMaxFixedRoot_E7_E8 (Or.inl rfl) Nat.prime_three (by norm_num)) K
      (by rw [hK]) E hE (toral_of_card_E7 hK hE hcard) hcard hSC
  exact exists_conj_frame_of_card_E7 hK hE hge

theorem ggE7TwoSCToral_holds (hK : Nat.card K = 2) : GGE7TwoSCToral K := by
  unfold GGE7TwoSCToral
  intro E hE hcard hSC
  have hSC' : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .E7 K)), x ^ 3 = 1 → x ∈ E :=
    fun x hx hx3 => hSC x hx3 (fun e he => (Subgroup.mem_centralizer_iff.mp hx e he).symm)
  exact exists_conj_frame_of_card_half_E7 hK hE hcard hSC'

end K

theorem ggE7TwoSCToralInput_holds : GGE7TwoSCToralInput := by
  unfold GGE7TwoSCToralInput
  intro K' _ _ _ hK'
  exact ggE7TwoSCToral_holds (K := K') hK'

end E7

section E8


section K

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem toral_of_card_E8 (hK : Nat.card K = 2) {E : Subgroup (adjointGroup .E8 K)}
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 7 ≤ Nat.card E) :
    ∃ g ∈ adjointGroup .E8 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .E8 K) : ModGL .E8 K) * g ∈ torusGroup .E8 (AlgebraicClosure K) := by
  have h3 := three_dvd_natCard_ext_sub_one hK
  exact toral_of_card_of_weylX (hτ := Or.inr rfl) (F := frameE8) (hd := rfl)
    (hw := frameE8_reflections) (hsymm := cartan_symm_E8)
    (hdet := isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E8 (by norm_num))
    (hV := card_torusPow_E8 (K := FiniteField.Extension K 2 2) Nat.prime_three h3)
    (S := modelHomE8.range) (hidx := not_three_dvd_index_E8 h3)
    (hhalf := halfOffender_E8) (hmon := monomialToralAt_three_of_block a2BlockToral_E8)
    (hK := hK) (E := E) (hE := hE) (hcard := hcard)

theorem exists_conj_frame_of_card_half_E8 (hK : Nat.card K = 2)
    {E : Subgroup (adjointGroup .E8 K)} (hE : IsElemAbelian 3 E) (hcard : 3 ^ 7 ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .E8 K)), x ^ 3 = 1 → x ∈ E) :
    ∃ c : adjointGroup .E8 K, E = (tE K frameE8).range.map (MulAut.conj c).toMonoidHom := by
  have hge : 3 ^ 8 ≤ Nat.card E :=
    ExcFramesHalf.card_ge_of_toral' (Or.inr rfl) Nat.prime_three (by norm_num)
      (ExcFramesHalf.halfMaxFixedRoot_E7_E8 (Or.inr rfl) Nat.prime_three (by norm_num)) K
      (by rw [hK]) E hE (toral_of_card_E8 hK hE hcard) hcard hSC
  exact exists_conj_frame_of_card_E8 hK hE hge

theorem ggE8TwoSCToral_holds (hK : Nat.card K = 2) : GGE8TwoSCToral K := by
  unfold GGE8TwoSCToral
  intro E hE hcard hSC
  have hSC' : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .E8 K)), x ^ 3 = 1 → x ∈ E :=
    fun x hx hx3 => hSC x hx3 (fun e he => (Subgroup.mem_centralizer_iff.mp hx e he).symm)
  exact exists_conj_frame_of_card_half_E8 hK hE hcard hSC'

end K

theorem ggE8TwoSCToralInput_holds : GGE8TwoSCToralInput := by
  unfold GGE8TwoSCToralInput
  intro K' _ _ _ hK'
  exact ggE8TwoSCToral_holds (K := K') hK'

end E8

end Half

end TableBExcTwoTB

end CFSG.StandardType

end
