module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBE7E8
public import CFSG.LocalAnalysis.StandardType.GGExcFrameLang
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE8
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxCount
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxFixedRoot
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableBExc TableBExc.Three TableBExcTwo TableBExcTwoFusion ExcFrameIso

namespace TableBExcTwoTB

private theorem map_conj_inv_map_conj {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    (H.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = H := by
  have h : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      MonoidHom.id G := by
    ext y
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    group
  rw [Subgroup.map_map, h, Subgroup.map_id]

section Full

variable
  {τ : Tag} {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem langElt_conj_frame_eq_torusPow (hτ : τ = .E7 ∨ τ = .E8) (F : OrthFrame τ d)
    (hd : d + 1 = τ.rank)
    (hV : Nat.card (torusPow τ (FiniteField.Extension K 2 2) 3) = 3 ^ τ.rank)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) :
    ((tE K F).range.map (adjointMap τ (algebraMap K (FiniteField.Extension K 2 2)))).map
        (MulAut.conj (langElt F hω)⁻¹).toMonoidHom =
      torusPow τ (FiniteField.Extension K 2 2) 3 := by
  classical
  set L := FiniteField.Extension K 2 2 with hL
  set G := langElt F hω with hG
  set ι := adjointMap τ (algebraMap K L) with hι
  have hfull := full_of_E7_E8 (K := L) hτ
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hsym := F.symm_one
  set D : (Fin τ.rank → ZMod 3) → adjointGroup τ L := fun s =>
    ⟨ExcFrames.frameDiag ω hω3 s, ExcFrames.frameDiag_mem_adjointGroup hfull ω hω3 s⟩ with hD
  have hKI : ∀ v, ι (tE K F (Multiplicative.ofAdd v)) = G * D (frameCoordHom F v) * G⁻¹ :=
    fun v => adjointMap_tE_eq hsym F hω hω3 hfull v
  set T := (tE K F).range with hT
  have hTcard : Nat.card T = 3 ^ τ.rank := by
    have e : Multiplicative (Fin (d + 1) → ZMod 3) ≃ T :=
      (MonoidHom.ofInjective (tE_injective F)).toEquiv
    rw [← hd, ← Nat.card_congr e, Nat.card_congr (Multiplicative.toAdd),
      Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  set T' : Subgroup (adjointGroup τ L) := (T.map ι).map (MulAut.conj G⁻¹).toMonoidHom with hT'
  have hT'le : T' ≤ torusPow τ L 3 := by
    rintro _ ⟨_, ⟨y, ⟨u, rfl⟩, rfl⟩, rfl⟩
    have hu : ι (tE K F u) = G * D (frameCoordHom F (Multiplicative.toAdd u)) * G⁻¹ := by
      have := hKI (Multiplicative.toAdd u)
      rwa [ofAdd_toAdd] at this
    have e : (MulAut.conj G⁻¹).toMonoidHom (ι (tE K F u)) =
        D (frameCoordHom F (Multiplicative.toAdd u)) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu]
      group
    rw [e]
    exact ExcFrames.mem_torusPow_iff_coe.mpr (ExcFrames.frameDiag_mem hfull ω hω3 _)
  have hT'eq : T' = torusPow τ L 3 :=
    Subgroup.eq_of_le_of_card_ge hT'le (by
      rw [hV, hT', Subgroup.card_map_of_injective (MulAut.conj G⁻¹).injective,
        Subgroup.card_map_of_injective (adjointMap_injective _), hTcard])
  exact hT'eq

theorem exists_conj_frame_of_card_of_weylX (hτ : τ = .E7 ∨ τ = .E8) (F : OrthFrame τ d)
    (hd : d + 1 = τ.rank)
    (hw : ∀ v : Fin τ.rank → ℤ, (List.ofFn fun i => rootReflection (F.root i)).prod • v = -v)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod 3))
    (hV : Nat.card (torusPow τ (FiniteField.Extension K 2 2) 3) = 3 ^ τ.rank)
    {S : Subgroup (WeylGroup τ)} (hidx : ¬ 3 ∣ (weylX τ (FiniteField.Extension K 2 2) S).index)
    (hS : ∀ A : Subgroup (WeylGroup τ), A ≤ S → IsElemAbelian 3 A → A ≠ ⊥ →
      Nat.card A * Nat.card {x : Fin τ.rank → ZMod 3 // ∀ a ∈ A, torusAct τ 3 a x = x} <
        3 ^ τ.rank)
    (hK : Nat.card K = 2) {E : Subgroup (adjointGroup τ K)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ τ.rank ≤ Nat.card E) :
    ∃ c : adjointGroup τ K, E = (tE K F).range.map (MulAut.conj c).toMonoidHom := by
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
  obtain ⟨A, hAS, hA, hA1, hEA⟩ := card_le_mul_card_fix_of_le_weylX Nat.prime_three h3 hdet hV
    hsymm hE' hE'X
  have hEV : E' = torusPow τ L 3 := by
    by_cases hbot : A = ⊥
    · exact Subgroup.eq_of_le_of_card_ge (hA1 hbot) (by rw [hV, hcard']; exact hcard)
    · have := hS A hAS hA hbot
      omega
  have hTj : ((tE K F).range.map j).map (MulAut.conj g⁻¹).toMonoidHom = torusPow τ L 3 :=
    langElt_conj_frame_eq_torusPow hτ F hd hV hωo
  have hEq : ((E.map (MulAut.conj x).toMonoidHom).map j).map
      (MulAut.conj g⁻¹).toMonoidHom =
      ((tE K F).range.map j).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← hE'def, hEV, ← hTj]
  have hEeq : E.map (MulAut.conj x).toMonoidHom = (tE K F).range :=
    Subgroup.map_injective hjinj
      (Subgroup.map_injective (MulAut.conj g⁻¹).injective hEq)
  refine ⟨x⁻¹, ?_⟩
  have h := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hEeq
  rwa [map_conj_inv_map_conj E x] at h

theorem exists_conj_frame_of_card_E7 (hK : Nat.card K = 2) {E : Subgroup (adjointGroup .E7 K)}
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 7 ≤ Nat.card E) :
    ∃ c : adjointGroup .E7 K, E = (tE K frameE7).range.map (MulAut.conj c).toMonoidHom := by
  have h3 := three_dvd_natCard_ext_sub_one hK
  exact exists_conj_frame_of_card_of_weylX (hτ := Or.inl rfl) (F := frameE7) (hd := rfl)
    (hw := frameE7_reflections) (hsymm := cartan_symm_E7)
    (hdet := isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E7 (by norm_num))
    (hV := card_torusPow_E7 (K := FiniteField.Extension K 2 2) Nat.prime_three h3)
    (S := modelHomE7.range) (hidx := not_three_dvd_index_E7 h3) (hS := noOffender_E7)
    (hK := hK) (E := E) (hE := hE) (hcard := hcard)

theorem exists_conj_frame_of_card_E8 (hK : Nat.card K = 2) {E : Subgroup (adjointGroup .E8 K)}
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 8 ≤ Nat.card E) :
    ∃ c : adjointGroup .E8 K, E = (tE K frameE8).range.map (MulAut.conj c).toMonoidHom := by
  have h3 := three_dvd_natCard_ext_sub_one hK
  exact exists_conj_frame_of_card_of_weylX (hτ := Or.inr rfl) (F := frameE8) (hd := rfl)
    (hw := frameE8_reflections) (hsymm := cartan_symm_E8)
    (hdet := isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E8 (by norm_num))
    (hV := card_torusPow_E8 (K := FiniteField.Extension K 2 2) Nat.prime_three h3)
    (S := modelHomE8.range) (hidx := not_three_dvd_index_E8 h3) (hS := noOffender_E8)
    (hK := hK) (E := E) (hE := hE) (hcard := hcard)

end Full

end TableBExcTwoTB

end CFSG.StandardType

end
