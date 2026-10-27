module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofRed
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.Quasithin.Background.F918V5GComp
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcStd
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Descent
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Remainder
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd

public section

namespace CFSG.StandardType

namespace QTwoExcSix

open CFSG.Open CFSG.Assembly Multiplicative

variable {G : Type} [Group G] {Bs L : Subgroup G}

abbrev exv (i : Fin 6) : Fin 6 → Multiplicative (ZMod 3) := Pi.mulSingle i (ofAdd 1)

theorem exv_swap (i j k : Fin 6) : exv i (Equiv.swap i j k) = exv j k := by
  simp only [exv, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

theorem mem_of_prod_eq_one (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod 3)))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 6 3)
    {v : Fin 6 → Multiplicative (ZMod 3)} (hv : ∏ i, v i = 1) : ((eta.symm v : ↥Bs) : G) ∈ L := by
  classical
  let H : Subgroup (Fin 6 → Multiplicative (ZMod 3)) :=
    L.comap (Bs.subtype.comp eta.symm.toMonoidHom)
  have hdiff : ∀ i j : Fin 6, i ≠ j → exv i / exv j ∈ H := by
    intro i j hij
    obtain ⟨g, hgL, hg, hgτ⟩ := exists_mem_conjAut_eq_permAut_swap (X := L) (eta := eta) hA hij
    have h1 : ggConjAut Bs hg (eta.symm (exv i)) = eta.symm (exv j) := by
      apply eta.injective
      rw [MulEquiv.apply_symm_apply]
      funext k
      have h := eta_ggConjAut_apply_of_permAut hg hgτ (eta.symm (exv i)) (Equiv.swap i j k)
      rw [Equiv.swap_apply_self, MulEquiv.apply_symm_apply, exv_swap] at h
      exact h
    have h2 : ((eta.symm (exv i / exv j) : ↥Bs) : G) =
        ((eta.symm (exv i) : ↥Bs) : G) * g * ((eta.symm (exv i) : ↥Bs) : G)⁻¹ * g⁻¹ := by
      rw [map_div, ← h1, Subgroup.coe_div, ggConjAut_apply, div_eq_mul_inv]
      group
    change ((eta.symm (exv i / exv j) : ↥Bs) : G) ∈ L
    rw [h2]
    have hb : ((eta.symm (exv i) : ↥Bs) : G) * g * ((eta.symm (exv i) : ↥Bs) : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hN (eta.symm (exv i)).2) g).mp hgL
    exact L.mul_mem hb (L.inv_mem hgL)
  have hsingle : ∀ (i : Fin 6) (c : Multiplicative (ZMod 3)),
      Pi.mulSingle i c / Pi.mulSingle 5 c ∈ H := by
    intro i c
    by_cases hi : i = 5
    · subst hi
      rw [div_self']
      exact H.one_mem
    · have hc : c = ofAdd 1 ^ (toAdd c).val := by
        rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
      rw [hc, Pi.mulSingle_pow, Pi.mulSingle_pow, ← div_pow]
      exact H.pow_mem (hdiff i 5 hi) _
  have hv' : v = ∏ i, (Pi.mulSingle i (v i) / Pi.mulSingle 5 (v i)) := by
    rw [Finset.prod_div_distrib, Finset.univ_prod_mulSingle]
    have h5 : (∏ x, (Pi.mulSingle (5 : Fin 6) (v x) : Fin 6 → Multiplicative (ZMod 3))) = 1 := by
      have := map_prod (MonoidHom.mulSingle (fun _ : Fin 6 => Multiplicative (ZMod 3)) 5) v
        Finset.univ
      simp only [MonoidHom.mulSingle_apply] at this
      rw [← this, hv, Pi.mulSingle_one]
    rw [h5, div_one]
  change v ∈ H
  rw [hv']
  exact H.prod_mem fun i _ => hsingle i (v i)

abbrev bv (eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod 3))) (v : Fin 6 → Multiplicative (ZMod 3)) :
    G :=
  ((eta.symm v : ↥Bs) : G)

theorem bv_mul (eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod 3)))
    (v w : Fin 6 → Multiplicative (ZMod 3)) : bv eta (v * w) = bv eta v * bv eta w := by
  simp [bv, map_mul]

theorem bv_comm (eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod 3)))
    (v w : Fin 6 → Multiplicative (ZMod 3)) : bv eta v * bv eta w = bv eta w * bv eta v := by
  rw [← bv_mul, ← bv_mul, mul_comm]

theorem bv_injective (eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod 3))) :
    Function.Injective (bv eta) := fun _ _ h =>
  eta.symm.injective (Subtype.ext h)

theorem eta_eq_const_of_commute (eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod 3)))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 6 3)
    (b : ↥Bs) (hb : ∀ l ∈ L, (b : G) * l = l * b) (i j : Fin 6) : eta b i = eta b j := by
  by_cases hij : i = j
  · rw [hij]
  obtain ⟨g, hgL, hg, hgτ⟩ := exists_mem_conjAut_eq_permAut_swap (X := L) (eta := eta) hA hij
  have h1 : ggConjAut Bs hg b = b := by
    apply Subtype.ext
    rw [ggConjAut_apply, ← hb g hgL, mul_inv_cancel_right]
  have h := eta_ggConjAut_apply_of_permAut hg hgτ b j
  rwa [h1, Equiv.swap_apply_right] at h

abbrev sgn345 : MulAut (Fin 6 → Multiplicative (ZMod 3)) :=
  SpCoord.sgnAut 3 * SpCoord.sgnAut 4 * SpCoord.sgnAut 5

theorem sgn345_mem : sgn345 ∈ bSignedFull 6 3 :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (sgnAut_mem_bSignedFull 3) (sgnAut_mem_bSignedFull 4))
    (sgnAut_mem_bSignedFull 5)

theorem sgn345_apply (v : Fin 6 → Multiplicative (ZMod 3)) (k : Fin 6) :
    sgn345 v k = if k.val < 3 then v k else (v k)⁻¹ := by
  fin_cases k <;> simp [sgn345, SpCoord.sgnAut_apply]

theorem sgn345_sgn345 (v : Fin 6 → Multiplicative (ZMod 3)) : sgn345 (sgn345 v) = v := by
  funext k
  rw [sgn345_apply, sgn345_apply]
  split_ifs <;> simp

theorem mem_zpowers_of_isCyclic [Finite G] {S : Subgroup G} (hS : IsCyclic S) {y c : G}
    (hy : y ∈ S) (hc : c ∈ S) (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1) (hc3 : c ^ 3 = 1) :
    c ∈ Subgroup.zpowers y := by
  classical
  by_contra hcy
  have : Fintype S := Fintype.ofFinite S
  have hle := IsCyclic.card_pow_eq_one_le (α := S) (n := 3) (by norm_num)
  let Y : S := ⟨y, hy⟩
  let C : S := ⟨c, hc⟩
  have hval : ∀ a b : S, (a : G) ≠ b → a ≠ b := fun a b h h' => h (congrArg Subtype.val h')
  have hy2 : y ^ 2 ≠ 1 := by
    intro h
    apply hy1
    calc y = y ^ 3 * (y ^ 2)⁻¹ := by group
      _ = 1 := by rw [hy3, h]; group
  have hyy2 : y ≠ y ^ 2 := by
    intro h
    apply hy1
    calc y = y ^ 2 * y⁻¹ := by group
      _ = 1 := by rw [← h]; group
  have hc1 : c ≠ 1 := fun h => hcy (h ▸ Subgroup.one_mem _)
  have hcy1 : c ≠ y := fun h => hcy (h ▸ Subgroup.mem_zpowers y)
  have hcy2 : c ≠ y ^ 2 := fun h => hcy (h ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers y) 2)
  have hsub : ({1, Y, Y ^ 2, C} : Finset S) ⊆ Finset.univ.filter (fun a : S => a ^ 3 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl | rfl
    · exact one_pow 3
    · exact Subtype.ext (by simpa [Y] using hy3)
    · exact Subtype.ext (by
        show (y ^ 2) ^ 3 = 1
        rw [← pow_mul, mul_comm, pow_mul, hy3, one_pow])
    · exact Subtype.ext (by simpa [C] using hc3)
  have hcard : ({1, Y, Y ^ 2, C} : Finset S).card = 4 := by
    have h1Y : (1 : S) ≠ Y := hval _ _ (Ne.symm hy1)
    have h1Y2 : (1 : S) ≠ Y ^ 2 := hval _ _ (by simpa [Y] using Ne.symm hy2)
    have h1C : (1 : S) ≠ C := hval _ _ (Ne.symm hc1)
    have hYY2 : Y ≠ Y ^ 2 := hval _ _ (by simpa [Y] using hyy2)
    have hYC : Y ≠ C := hval _ _ (Ne.symm hcy1)
    have hY2C : Y ^ 2 ≠ C := hval _ _ (by simpa [Y, C] using Ne.symm hcy2)
    rw [Finset.card_insert_of_notMem (by simp [h1Y, h1Y2, h1C]),
      Finset.card_insert_of_notMem (by simp [hYY2, hYC]), Finset.card_pair hY2C]
  have := Finset.card_le_card hsub
  omega

theorem prod_exv_div {i j : Fin 6} : ∏ k, (exv i / exv j) k = 1 := by
  simp only [Pi.div_apply, Finset.prod_div_distrib, exv, Fintype.prod_pi_mulSingle', div_self']

theorem prod_inv_exv_div {i j : Fin 6} : ∏ k, ((exv i / exv j)⁻¹) k = 1 := by
  simp only [Pi.inv_apply, Finset.prod_inv_distrib, prod_exv_div, inv_one]

theorem sgn345_exv01 : sgn345 (exv 0 / exv 1) = exv 0 / exv 1 := by
  funext k
  fin_cases k <;> simp [sgn345_apply, exv]

theorem sgn345_exv12 : sgn345 (exv 1 / exv 2) = exv 1 / exv 2 := by
  funext k
  fin_cases k <;> simp [sgn345_apply, exv]

theorem sgn345_exv34 : sgn345 (exv 3 / exv 4) = (exv 3 / exv 4)⁻¹ := by
  funext k
  fin_cases k <;> simp [sgn345_apply, exv]

theorem sgn345_exv03 : sgn345 (exv 0 / exv 3) = exv 0 * exv 3 := by
  funext k
  fin_cases k <;> simp [sgn345_apply, exv]

theorem prod_sgn345_const (c : Multiplicative (ZMod 3)) : ∏ k, sgn345 (fun _ => c) k = 1 := by
  rw [Fin.prod_univ_six]
  show c * c * c * c⁻¹ * c⁻¹ * c⁻¹ = 1
  group

theorem conj_mem_twoCenter [Finite G] {n z : G} (hn : n ∈ Subgroup.normalizer (L : Set G))
    (hz : z ∈ Line63.H5.twoCenter L) : n * z * n⁻¹ ∈ Line63.H5.twoCenter L := by
  have hzN : z ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hz.1
  have h := (Line63.H5.twoCenter_normal L).conj_mem ⟨z, hzN⟩
    (Subgroup.mem_subgroupOf.mpr hz) ⟨n, hn⟩
  exact Subgroup.mem_subgroupOf.mp h

theorem false_of_twoCenter_ne_bot_of_sstar [Finite G] {B : Subgroup G} {x : G}
    (hBs : IsElemAbelian 3 Bs) (hxBs : x ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hS : LargeEvenSStar 3 B x L)
    (hB : B = Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod 3)))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 6 3)
    (t : G) (ht : t ∈ Subgroup.normalizer (Bs : Set G))
    (hteta : ∀ b : ↥Bs, eta (ggConjAut Bs ht b) = sgn345 (eta b))
    (hZ : Line63.H5.twoCenter L ≠ ⊥)
    (hfix : ∀ z ∈ Line63.H5.twoCenter L, bv eta (exv 0) * z = z * bv eta (exv 0) → z = 1)
    (hcent : ∀ l ∈ L, l * bv eta (exv 0 / exv 1) = bv eta (exv 0 / exv 1) * l →
      l * bv eta (exv 1 / exv 2) = bv eta (exv 1 / exv 2) * l →
      l * bv eta (exv 3 / exv 4) = bv eta (exv 3 / exv 4) * l →
      ∃ v : Fin 6 → Multiplicative (ZMod 3), ∏ i, v i = 1 ∧
        ∃ c ∈ L, (∀ m ∈ L, c * m = m * c) ∧ l = bv eta v * c) :
    False := by
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
      IsCyclic S := hS.2.2.2.2
  have hx1 : x ≠ 1 := hS.2.2.1
  have hA0 : ∀ v : Fin 6 → Multiplicative (ZMod 3), ∏ i, v i = 1 → bv eta v ∈ L :=
    fun v hv => mem_of_prod_eq_one hN eta hA hv
  have hcube : ∀ g ∈ Bs, g ^ 3 = 1 := hBs.2
  have hbvcube : ∀ v, bv eta v ^ 3 = 1 := fun v => hcube _ (eta.symm v).2
  have hBsp : IsPGroup 3 Bs := fun g => ⟨1, Subtype.ext (by simpa using hcube g g.2)⟩
  have hxL : ∀ l ∈ L, x * l = l * x := fun l hl =>
    Subgroup.mem_centralizer_iff.mp (hLx hl) x (Set.mem_singleton x)
  have hconst : ∀ i, eta ⟨x, hxBs⟩ i = eta ⟨x, hxBs⟩ 0 := fun i =>
    eta_eq_const_of_commute eta hA ⟨x, hxBs⟩ hxL i 0
  have htc : ∀ v, t * bv eta v * t⁻¹ = bv eta (sgn345 v) := by
    intro v
    have h := hteta (eta.symm v)
    rw [MulEquiv.apply_symm_apply] at h
    have h' : ggConjAut Bs ht (eta.symm v) = eta.symm (sgn345 v) := by
      rw [← h, MulEquiv.symm_apply_apply]
    simpa [bv, ggConjAut_apply] using congrArg Subtype.val h'
  have htc' : ∀ v, t⁻¹ * bv eta v * t = bv eta (sgn345 v) := by
    intro v
    have h := htc (sgn345 v)
    rw [sgn345_sgn345] at h
    rw [← h]
    group
  have htB : t ∈ Subgroup.normalizer (B : Set G) := hB ▸ ht
  have hSa := largeEvenSStar_map_conj_of_mem_normalizer hS htB
  have hxv : eta ⟨x, hxBs⟩ = fun _ => eta ⟨x, hxBs⟩ 0 := funext hconst
  have ha : t * x * t⁻¹ = bv eta (sgn345 (eta ⟨x, hxBs⟩)) := by
    have h := htc (eta ⟨x, hxBs⟩)
    simpa [bv] using h
  have haL : t * x * t⁻¹ ∈ L := by
    rw [ha]
    refine hA0 _ ?_
    rw [hxv]
    exact prod_sgn345_const _
  have hM : ∀ w, ∏ i, sgn345 w i = 1 → bv eta w ∈ L.map (MulAut.conj t).toMonoidHom := by
    intro w hw
    refine ⟨bv eta (sgn345 w), hA0 _ hw, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [htc, sgn345_sgn345]
  let E : Subgroup G := Subgroup.closure {bv eta (exv 0 / exv 1), bv eta (exv 3 / exv 4)}
  have hEM : E ≤ L.map (MulAut.conj t).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr (Set.insert_subset_iff.mpr ⟨hM _ ?_, ?_⟩)
    · rw [sgn345_exv01]; exact prod_exv_div
    · refine Set.singleton_subset_iff.mpr (hM _ ?_)
      rw [sgn345_exv34]; exact prod_inv_exv_div
  have hEL : E ≤ L := (Subgroup.closure_le _).mpr
    (Set.insert_subset_iff.mpr ⟨hA0 _ prod_exv_div, Set.singleton_subset_iff.mpr
      (hA0 _ prod_exv_div)⟩)
  have hEBs : E ≤ Bs := (Subgroup.closure_le _).mpr
    (Set.insert_subset_iff.mpr ⟨(eta.symm _).2, Set.singleton_subset_iff.mpr (eta.symm _).2⟩)
  have hEc : ¬ IsCyclic E := by
    intro hcE
    have h01 : bv eta (exv 0 / exv 1) ≠ 1 := by
      intro h
      have h' : exv 0 / exv 1 = 1 := bv_injective eta (by rw [h]; simp [bv])
      have := congrFun h' 0
      simp [exv] at this
    have hmem := mem_zpowers_of_isCyclic hcE (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) h01 (hbvcube _) (hbvcube _)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : (exv 0 / exv 1) ^ k = exv 3 / exv 4 := by
      apply bv_injective eta
      simp only [bv, map_zpow, Subgroup.coe_zpow] at hk ⊢
      exact hk
    have := congrFun hk' 3
    simp [exv] at this
    exact absurd this.symm (by decide)
  have hEp : IsPGroup 3 E := hBsp.to_le hEBs
  have hzM : ∀ z ∈ Line63.H5.twoCenter L,
      z ∈ Subgroup.normalizer ((L.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
    intro z hz
    refine mem_normalizer_of_isComponentOf_of_not_isCyclic hSa.2.2.2.1 hSa.2.2.2.2 hEM hEp hEc
      ?_ fun e he => hz.2.1 e (hEL he)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (hz.2.1 _ haL).symm
  have hzero : ∀ z ∈ Line63.H5.twoCenter L, z = 1 := by
    intro z hz
    have hzL : ∀ l ∈ L, z * l = l * z := hz.2.1
    have hz'N : ∀ l ∈ L, (t⁻¹ * z * t) * l * (t⁻¹ * z * t)⁻¹ ∈ L := by
      intro l hl
      have hm : t * l * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom := ⟨l, hl, rfl⟩
      obtain ⟨l', hl', he⟩ := (Subgroup.mem_normalizer_iff.mp (hzM z hz) (t * l * t⁻¹)).mp hm
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
      have h : (t⁻¹ * z * t) * l * (t⁻¹ * z * t)⁻¹ = l' := by
        calc (t⁻¹ * z * t) * l * (t⁻¹ * z * t)⁻¹ = t⁻¹ * (z * (t * l * t⁻¹) * z⁻¹) * t := by
              group
          _ = t⁻¹ * (t * l' * t⁻¹) * t := by rw [he]
          _ = l' := by group
      rw [h]
      exact hl'
    have hz'c : ∀ w, ∏ i, sgn345 w i = 1 → Commute (t⁻¹ * z * t) (bv eta w) := by
      intro w hw
      show (t⁻¹ * z * t) * bv eta w = bv eta w * (t⁻¹ * z * t)
      have h2 : z * bv eta (sgn345 w) = bv eta (sgn345 w) * z := hzL _ (hA0 _ hw)
      calc (t⁻¹ * z * t) * bv eta w = t⁻¹ * (z * (t * bv eta w * t⁻¹)) * t := by group
        _ = t⁻¹ * (bv eta (sgn345 w) * z) * t := by rw [htc, h2]
        _ = (t⁻¹ * bv eta (sgn345 w) * t) * (t⁻¹ * z * t) := by group
        _ = bv eta w * (t⁻¹ * z * t) := by rw [htc', sgn345_sgn345]
    have ha₀L : bv eta (exv 0 / exv 3) ∈ L := hA0 _ prod_exv_div
    have hlL : (t⁻¹ * z * t) * bv eta (exv 0 / exv 3) * (t⁻¹ * z * t)⁻¹ ∈ L := hz'N _ ha₀L
    have hlc : ∀ w, ∏ i, sgn345 w i = 1 →
        (t⁻¹ * z * t) * bv eta (exv 0 / exv 3) * (t⁻¹ * z * t)⁻¹ * bv eta w =
          bv eta w * ((t⁻¹ * z * t) * bv eta (exv 0 / exv 3) * (t⁻¹ * z * t)⁻¹) := by
      intro w hw
      have h1 := hz'c w hw
      have h2 : Commute (bv eta (exv 0 / exv 3)) (bv eta w) := bv_comm eta _ _
      exact ((h1.mul_left h2).mul_left h1.inv_left).eq
    obtain ⟨v, hv, c, hcL, hcc, hlv⟩ := hcent _ hlL
      (hlc _ (by rw [sgn345_exv01]; exact prod_exv_div))
      (hlc _ (by rw [sgn345_exv12]; exact prod_exv_div))
      (hlc _ (by rw [sgn345_exv34]; exact prod_inv_exv_div))
    have hvL : bv eta v ∈ L := hA0 v hv
    have hl3 : ((t⁻¹ * z * t) * bv eta (exv 0 / exv 3) * (t⁻¹ * z * t)⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hbvcube, mul_one, mul_inv_cancel]
    have hc3 : c ^ 3 = 1 := by
      have hcomm : Commute (bv eta v) c := (hcc _ hvL).symm
      have h := hl3
      rw [hlv, hcomm.mul_pow, hbvcube, one_mul] at h
      exact h
    have hxc : x * c = c * x := hxL c hcL
    have hx3 : x ^ 3 = 1 := hcube x hxBs
    have hSC : Subgroup.zpowers x ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer (L : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact (hxL l hl).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact (hcc l hl).symm
    have hzp3 : ∀ g : G, g ^ 3 = 1 → IsPGroup 3 (Subgroup.zpowers g) := by
      intro g hg y
      refine ⟨1, Subtype.ext ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
      rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hg, one_zpow, Subgroup.coe_one]
    have hSp : IsPGroup 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers c) := by
      refine IsPGroup.to_sup_of_normal_right' (hzp3 x hx3) (hzp3 c hc3) ?_
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      have hxcomm : Commute x c := hxc
      intro g
      constructor
      · intro hg
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        rw [(hxcomm.zpow_right k).eq, mul_inv_cancel_right]
        exact hg
      · intro hg
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
        have hg' : g = c ^ k := by
          have h := (hxcomm.zpow_right k).inv_left.eq
          calc g = x⁻¹ * (x * g * x⁻¹) * x := by group
            _ = x⁻¹ * c ^ k * x := by rw [hk]
            _ = c ^ k * x⁻¹ * x := by rw [h]
            _ = c ^ k := by group
        rw [hg']
        exact Subgroup.zpow_mem_zpowers c k
    have hcx : c ∈ Subgroup.zpowers x :=
      mem_zpowers_of_isCyclic (hcyc _ hSC hSp) (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)) hx1 hx3 hc3
    have hlB : (t⁻¹ * z * t) * bv eta (exv 0 / exv 3) * (t⁻¹ * z * t)⁻¹ ∈ Bs := by
      rw [hlv]
      exact Bs.mul_mem (eta.symm v).2 (Subgroup.zpowers_le.mpr hxBs hcx)
    have ha₁ : t * bv eta (exv 0 / exv 3) * t⁻¹ = bv eta (exv 0 * exv 3) := by
      rw [htc, sgn345_exv03]
    have ha₁B : bv eta (exv 0 * exv 3) ∈ Bs := (eta.symm _).2
    have hza₁ : z * bv eta (exv 0 * exv 3) * z⁻¹ =
        t * ((t⁻¹ * z * t) * bv eta (exv 0 / exv 3) * (t⁻¹ * z * t)⁻¹) * t⁻¹ := by
      rw [← ha₁]
      group
    have hcomm1 : z * bv eta (exv 0 * exv 3) * z⁻¹ * (bv eta (exv 0 * exv 3))⁻¹ ∈ Bs := by
      refine Bs.mul_mem ?_ (Bs.inv_mem ha₁B)
      rw [hza₁]
      exact (Subgroup.mem_normalizer_iff.mp ht _).mp hlB
    have hcomm2 : z * bv eta (exv 0 * exv 3) * z⁻¹ * (bv eta (exv 0 * exv 3))⁻¹ ∈
        Line63.H5.twoCenter L := by
      rw [mul_assoc, mul_assoc]
      refine (Line63.H5.twoCenter L).mul_mem hz ?_
      rw [← mul_assoc]
      exact conj_mem_twoCenter (hN ha₁B) ((Line63.H5.twoCenter L).inv_mem hz)
    have hone := Line63.eq_one_of_cube (Line63.H5.isPGroup_twoCenter L) hcomm2 (hcube _ hcomm1)
    have hza₁' : Commute z (bv eta (exv 0 * exv 3)) := by
      have h := hone
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
      exact h
    have hza₀ : Commute z (bv eta (exv 0 / exv 3)) := hzL _ ha₀L
    have hprod : (bv eta (exv 0 * exv 3) * bv eta (exv 0 / exv 3)) ^ 2 = bv eta (exv 0) := by
      have hv2 : (exv 0 * exv 3) * (exv 0 / exv 3) = exv 0 ^ 2 := by
        rw [div_eq_mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one, sq]
      have hbvpow : ∀ (w : Fin 6 → Multiplicative (ZMod 3)) (n : ℕ),
          bv eta (w ^ n) = bv eta w ^ n := by
        intro w n
        simp [bv, map_pow]
      rw [← bv_mul, hv2, hbvpow, ← pow_mul]
      calc bv eta (exv 0) ^ (2 * 2) = bv eta (exv 0) ^ 3 * bv eta (exv 0) := by
            rw [← pow_succ]
        _ = bv eta (exv 0) := by rw [hbvcube, one_mul]
    apply hfix z hz
    have hc := (hza₁'.mul_right hza₀).pow_right 2
    rw [hprod] at hc
    exact hc.eq.symm
  exact hZ ((Subgroup.eq_bot_iff_forall _).mpr hzero)

theorem false_of_twoCenter_ne_bot [Finite G] {B : Subgroup G} {x : G} {D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hC : GGConfig 3 B Bs x L D J) (hB : B = Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod 3)))
    (hJoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 6 3)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 6 3)
    (hZ : Line63.H5.twoCenter L ≠ ⊥)
    (hfix : ∀ z ∈ Line63.H5.twoCenter L, bv eta (exv 0) * z = z * bv eta (exv 0) → z = 1)
    (hcent : ∀ l ∈ L, l * bv eta (exv 0 / exv 1) = bv eta (exv 0 / exv 1) * l →
      l * bv eta (exv 1 / exv 2) = bv eta (exv 1 / exv 2) * l →
      l * bv eta (exv 3 / exv 4) = bv eta (exv 3 / exv 4) * l →
      ∃ v : Fin 6 → Multiplicative (ZMod 3), ∏ i, v i = 1 ∧
        ∃ c ∈ L, (∀ m ∈ L, c * m = m * c) ∧ l = bv eta v * c) :
    False := by
  obtain ⟨-, hBs, hxBs, hLx, -⟩ := hC.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hC.1.2.2.2.2.2.2.1
  obtain ⟨t, ht, -, hteta⟩ := exists_ggConjAut_eq_of_mem_bSignedFull eta hJoin sgn345_mem
  exact false_of_twoCenter_ne_bot_of_sstar hBs hxBs hLx hS hB hN eta hA t ht hteta hZ hfix hcent

end QTwoExcSix

end CFSG.StandardType

end
