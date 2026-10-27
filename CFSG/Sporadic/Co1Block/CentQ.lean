module

public import CFSG.Sporadic.Co1Block.Cent
public import CFSG.Sporadic.Co1Block.Tools

public noncomputable section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative Matrix

variable {tR : Native.Rows} {t : GL24} {d₁ d₂ : List (List ℤ)} {bidx : List ℕ}
  {base : List ℕ} {vgens : List (List ℕ)} {vsizes : List ℕ}
  {Qg : List Native.Rows} {cap : ℕ} {roots : List Native.Rows} {gens : List (List ℕ)}
  {sizes : List ℕ} {qgs : ℕ → GL24}

@[expose] def qSub (qgs : ℕ → GL24) (m : ℕ) : Subgroup GL24 := Subgroup.closure (qgs '' {l | l < m})

abbrev strongRows (tR : Native.Rows) (d₁ : List (List ℤ)) (bidx : List ℕ) (d₂ : List (List ℤ)) :
    List Native.Rows :=
  (CFSG.Sporadic.Co1Schreier.Native.dag (Native.brayElts (Native.brayRows tR d₁) bidx) d₂).1

theorem qCheck_parts
    (h : Native.qCheckOf tR d₁ bidx d₂ Qg cap roots gens sizes = true) :
    gtOK Qg.toArray (gtBFS Qg.toArray cap) = true ∧
    (∀ r ∈ roots, (gtBFS Qg.toArray cap).pts.contains r = true) ∧
    (∀ i < roots.length,
      Native.conjLevelOK (strongRows tR d₁ bidx d₂) roots gens sizes i = true) ∧
    (∀ g ∈ Native.brayElts (Native.brayRows tR d₁) bidx,
      CFSG.Sporadic.Co1Schreier.Native.mul g (CFSG.Sporadic.Co1Schreier.Native.inv g) =
        CFSG.Sporadic.Co1Schreier.Native.one ∧
      ∀ q ∈ Qg, (gtBFS Qg.toArray cap).pts.contains
        (conjRows g (CFSG.Sporadic.Co1Schreier.Native.inv g) q) = true) := by
  simp only [Native.qCheckOf, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

@[expose] def QRep (Qg : List Native.Rows) (qgs : ℕ → GL24) : Prop :=
  ∀ l < Qg.length, MRep (Qg.getD l CFSG.Sporadic.Co1Schreier.Native.one) (qgs l)

theorem rowsMatrix_getElem!_toArray {L : List Native.Rows} {l : ℕ} (hl : l < L.length) :
    rowsMatrix 24 L.toArray[l]! =
      rowsMatrix 24 (L.getD l CFSG.Sporadic.Co1Schreier.Native.one) := by
  rw [getElem!_pos L.toArray l (by simpa using hl), List.getElem_toArray,
    List.getD_eq_getElem _ _ hl]

theorem qRep_arr (hQ : QRep Qg qgs) :
    ∀ l < Qg.toArray.size, valHom (qgs l) = rowsMatrix 24 Qg.toArray[l]! := by
  intro l hl
  have hl' : l < Qg.length := by simpa using hl
  rw [rowsMatrix_getElem!_toArray hl']
  exact (hQ l hl').symm

theorem qSub_eq : qSub qgs Qg.length = Subgroup.closure (qgs '' {l | l < Qg.toArray.size}) := by
  rw [qSub]
  simp

theorem card_Q (hQ : QRep Qg qgs)
    (h : Native.qCheckOf tR d₁ bidx d₂ Qg cap roots gens sizes = true) :
    Nat.card (qSub qgs Qg.length) = (gtBFS Qg.toArray cap).pts.size := by
  rw [qSub_eq]
  exact prodTree_card valHom valHom_injective (qCheck_parts h).1 qgs (qRep_arr hQ)

theorem mem_Q_of_contains (hQ : QRep Qg qgs)
    (h : Native.qCheckOf tR d₁ bidx d₂ Qg cap roots gens sizes = true) {r : Native.Rows}
    (hr : (gtBFS Qg.toArray cap).pts.contains r = true) {y : GL24} (hy : MRep r y) :
    y ∈ qSub qgs Qg.length := by
  rw [Array.contains_iff_mem, Array.mem_iff_getElem] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  rw [qSub_eq]
  refine mem_closure_of_prodTree valHom valHom_injective (qCheck_parts h).1 qgs (qRep_arr hQ) hi ?_
  rw [getElem!_pos _ i hi]
  exact hy.symm

theorem exists_mem_Q_of_contains (hQ : QRep Qg qgs)
    (h : Native.qCheckOf tR d₁ bidx d₂ Qg cap roots gens sizes = true) {r : Native.Rows}
    (hr : (gtBFS Qg.toArray cap).pts.contains r = true) :
    ∃ y ∈ qSub qgs Qg.length, MRep r y := by
  obtain ⟨f, hf, -, heq⟩ := prodTree_closure_eq valHom valHom_injective (qCheck_parts h).1 qgs
    (qRep_arr hQ)
  rw [Array.contains_iff_mem, Array.mem_iff_getElem] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  refine ⟨f i, ?_, ?_⟩
  · rw [qSub_eq]
    have : f i ∈ ((Subgroup.closure (qgs '' {l | l < Qg.toArray.size}) : Subgroup GL24) :
        Set GL24) := by
      rw [heq]
      exact ⟨i, hi, rfl⟩
    exact this
  · have := hf i hi
    unfold MRep
    rw [← getElem!_pos _ i hi]
    exact this.symm

theorem exists_roots (hQ : QRep Qg qgs)
    (h : Native.qCheckOf tR d₁ bidx d₂ Qg cap roots gens sizes = true) :
    ∃ b : ℕ → GL24, ∀ i < roots.length, b i ∈ qSub qgs Qg.length ∧
      MRep (roots.getD i CFSG.Sporadic.Co1Schreier.Native.one) (b i) := by
  have hroot : ∀ i < roots.length, ∃ y ∈ qSub qgs Qg.length,
      MRep (roots.getD i CFSG.Sporadic.Co1Schreier.Native.one) y := fun i hi =>
    exists_mem_Q_of_contains hQ h ((qCheck_parts h).2.1 _ (by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi))
  choose! b hb using hroot
  exact ⟨b, hb⟩

theorem bray_conj_mem_Q (ht : MRep tR t)
    (hc : Native.centCheckOf tR d₁ bidx d₂ base vgens vsizes = true) (hQ : QRep Qg qgs)
    (h : Native.qCheckOf tR d₁ bidx d₂ Qg cap roots gens sizes = true) :
    ∀ g ∈ brayEltsG t d₁ bidx, ∀ l < Qg.length, g * qgs l * g⁻¹ ∈ qSub qgs Qg.length := by
  intro g hg l hl
  obtain ⟨r, hr, hrg⟩ := forall₂_mem_left (rep_brayElts ht (centCheck_parts hc).1) hg
  obtain ⟨hinv, hconj⟩ := (qCheck_parts h).2.2.2 r hr
  have hri := hrg.inv hinv
  have hq := hQ l hl
  refine mem_Q_of_contains hQ h (hconj (Qg.getD l CFSG.Sporadic.Co1Schreier.Native.one) ?_) ?_
  · rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  · exact (hrg.mul hq).mul hri

theorem conj_mem_qSub_of_gens {g : GL24} {m : ℕ}
    (hg : ∀ l < m, g * qgs l * g⁻¹ ∈ qSub qgs m) : ∀ q ∈ qSub qgs m, g * q * g⁻¹ ∈ qSub qgs m := by
  intro q hq
  set K := qSub qgs m
  have hle : K ≤ K.comap (MulAut.conj g).toMonoidHom := by
    conv_lhs => rw [show K = Subgroup.closure (qgs '' {l | l < m}) from rfl]
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hg l hl
  have := hle hq
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem brayE_conj_mem_Q (ht : MRep tR t)
    (hc : Native.centCheckOf tR d₁ bidx d₂ base vgens vsizes = true) (hQ : QRep Qg qgs)
    (h : Native.qCheckOf tR d₁ bidx d₂ Qg cap roots gens sizes = true) :
    ∀ g ∈ brayE t d₁ bidx, ∀ q ∈ qSub qgs Qg.length, g * q * g⁻¹ ∈ qSub qgs Qg.length := by
  have hfin : Finite (qSub qgs Qg.length : Set GL24) := Set.toFinite _
  have hle : brayE t d₁ bidx ≤ Subgroup.normalizer (qSub qgs Qg.length : Set GL24) := by
    rw [brayE, Subgroup.closure_le]
    intro g hg
    exact Subgroup.mem_normalizer_fintype fun q hq =>
      conj_mem_qSub_of_gens (bray_conj_mem_Q ht hc hQ h g hg) q hq
  intro g hg q hq
  exact (Subgroup.mem_normalizer_iff.1 (hle hg) q).1 hq

theorem getElem!_toArray_map {α β : Type*} [Inhabited β] (f : α → β) (js : List α) {l : ℕ}
    (hl : l < js.length) : (js.map f).toArray[l]! = f js[l] := by
  rw [getElem!_pos _ l (by simpa using hl)]
  simp

theorem conjLevel_parts {S : List Native.Rows} {i : ℕ}
    (h : Native.conjLevelOK S roots gens sizes i = true) :
    (∀ j ∈ gens.getD i [], j < S.length ∧ ∀ l < i,
      CFSG.Sporadic.Co1Schreier.Native.mul (S.getD j CFSG.Sporadic.Co1Schreier.Native.one)
        (roots.getD l CFSG.Sporadic.Co1Schreier.Native.one) =
      CFSG.Sporadic.Co1Schreier.Native.mul (roots.getD l CFSG.Sporadic.Co1Schreier.Native.one)
        (S.getD j CFSG.Sporadic.Co1Schreier.Native.one)) ∧
    (∀ l < ((gens.getD i []).map fun j => S.getD j CFSG.Sporadic.Co1Schreier.Native.one).length,
      CFSG.Sporadic.Co1Schreier.Native.mul
        (((gens.getD i []).map fun j => S.getD j CFSG.Sporadic.Co1Schreier.Native.one).toArray[l]!)
        ((((gens.getD i []).map fun j => S.getD j CFSG.Sporadic.Co1Schreier.Native.one).toArray.map
          CFSG.Sporadic.Co1Schreier.Native.inv)[l]!) = CFSG.Sporadic.Co1Schreier.Native.one) ∧
    Native.conjAtLeast
      ((gens.getD i []).map fun j => S.getD j CFSG.Sporadic.Co1Schreier.Native.one).toArray
      (((gens.getD i []).map fun j => S.getD j CFSG.Sporadic.Co1Schreier.Native.one).toArray.map
        CFSG.Sporadic.Co1Schreier.Native.inv)
      (roots.getD i CFSG.Sporadic.Co1Schreier.Native.one) (sizes.getD i 0) = true := by
  simp only [Native.conjLevelOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, beq_iff_eq, List.size_toArray] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem card_mul_card_towerStab_brayE_le (ht : MRep tR t)
    (hc : Native.centCheckOf tR d₁ bidx d₂ base vgens vsizes = true)
    (h : Native.qCheckOf tR d₁ bidx d₂ Qg cap roots gens sizes = true) {b : ℕ → GL24}
    (hb : ∀ i < roots.length, MRep (roots.getD i CFSG.Sporadic.Co1Schreier.Native.one) (b i)) :
    (∏ i ∈ Finset.range roots.length, sizes.getD i 0) *
      Nat.card (towerStab (brayE t d₁ bidx) b roots.length) ≤ Nat.card (brayE t d₁ bidx) := by
  have hrep := rep_strongDag ht hc
  set S := strongRows tR d₁ bidx d₂
  set L : ℕ → GL24 := fun j => (strongDagG t d₁ bidx d₂).getD j 1
  have hL : ∀ j, MRep (S.getD j CFSG.Sporadic.Co1Schreier.Native.one) (L j) :=
    fun j => getD_rep hrep MRep.one j
  refine card_mul_card_towerStab_le (brayE t d₁ bidx) b
    (fun i => L '' {j | j ∈ gens.getD i []}) (fun i => sizes.getD i 0) roots.length ?_ ?_
  · rintro i hi _ ⟨j, hj, rfl⟩
    obtain ⟨hcomm, -, -⟩ := conjLevel_parts ((qCheck_parts h).2.2.1 i hi)
    refine ⟨getD_mem_of_forall strongDag_mem j, fun l hl => ?_⟩
    have e := (hcomm j hj).2 l hl
    exact ((hL j).mul (hb l (by omega))).eq (by rw [e]; exact (hb l (by omega)).mul (hL j))
  · intro i hi
    obtain ⟨-, hinv, hcheck⟩ := conjLevel_parts ((qCheck_parts h).2.2.1 i hi)
    set js := gens.getD i []
    simp only [Native.conjAtLeast, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    obtain ⟨hct, hsize⟩ := hcheck
    have hG : ∀ l < (js.map fun j => S.getD j CFSG.Sporadic.Co1Schreier.Native.one).toArray.size,
        valHom (L (js.getD l 0)) = rowsMatrix 24
          (js.map fun j => S.getD j CFSG.Sporadic.Co1Schreier.Native.one).toArray[l]! := by
      intro l hl
      have hl' : l < js.length := by simpa using hl
      rw [getElem!_toArray_map _ _ hl', List.getD_eq_getElem _ _ hl']
      exact (hL _).symm
    have hGi : ∀ l < (js.map fun j => S.getD j CFSG.Sporadic.Co1Schreier.Native.one).toArray.size,
        mulRows 24 (js.map fun j => S.getD j CFSG.Sporadic.Co1Schreier.Native.one).toArray[l]!
          ((js.map fun j => S.getD j CFSG.Sporadic.Co1Schreier.Native.one).toArray.map
            CFSG.Sporadic.Co1Schreier.Native.inv)[l]! = idRows 24 := by
      intro l hl
      exact hinv l (by simpa using hl)
    obtain ⟨f, hf, hinj⟩ := conjTree_sound valHom hct (fun l => L (js.getD l 0))
      hG hGi (b i) (hb i hi).symm
    set c := conjBFS (js.map fun j => S.getD j CFSG.Sporadic.Co1Schreier.Native.one).toArray
      ((js.map fun j => S.getD j CFSG.Sporadic.Co1Schreier.Native.one).toArray.map
        CFSG.Sporadic.Co1Schreier.Native.inv) (roots.getD i CFSG.Sporadic.Co1Schreier.Native.one)
      (sizes.getD i 0)
    have hsub : f '' Set.Iio c.pts.size ⊆
        conjOrbit (Subgroup.closure (L '' {j | j ∈ js})) (b i) := by
      rintro _ ⟨k, hk, rfl⟩
      obtain ⟨⟨x, hx, hxe⟩, -⟩ := hf k hk
      refine ⟨x, ?_, hxe.symm⟩
      refine (Subgroup.closure_mono ?_) hx
      rintro _ ⟨l, hl, rfl⟩
      have hl' : l < js.length := by simpa using hl
      exact ⟨js.getD l 0, by rw [List.getD_eq_getElem _ _ hl']; exact List.getElem_mem hl', rfl⟩
    calc sizes.getD i 0 ≤ c.pts.size := hsize
      _ = (f '' Set.Iio c.pts.size).ncard := by
          have hinj' : Set.InjOn f (Set.Iio c.pts.size) := fun x hx y hy e => hinj x hx y hy e
          rw [hinj'.ncard_image, Set.ncard_Iio_nat]
      _ ≤ (conjOrbit (Subgroup.closure (L '' {j | j ∈ js})) (b i)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)

end CFSG.Sporadic.Co1Block
