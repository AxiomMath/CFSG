module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitConj
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitShared
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux5
import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmPair
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDeleteA

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

open scoped Matrix

variable {G : Type} [Group G] [Finite G]


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}

theorem ggQTwoDUnit_mem_B {a b c : Fin m} (hca : c ≠ a) (hcb : c ≠ b) (hBBs : B ≤ Bs)
    (hshape : B = Bs ∨ ∀ s : ↥Bs,
      ((s : G) ∈ B ↔ βL (Additive.ofMul s) a = βL (Additive.ofMul s) b))
    {b' : ↥Bs} (hb' : βL (Additive.ofMul b') = Pi.single c 1) : (b' : G) ∈ B := by
  rcases hshape with h | h
  · rw [h]
    exact b'.2
  · rw [h b', hb']
    simp [Pi.single_eq_of_ne (Ne.symm hca), Pi.single_eq_of_ne (Ne.symm hcb)]

private theorem qtwoDB12_const_of_mem_centralizer (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hm : 5 ≤ m) {c : Fin m} {s : ↥Bs}
    (hs : (s : G) ∈ Subgroup.centralizer
        (((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ : Subgroup G) : Set G)) :
    ∀ i ∈ Finset.univ.erase c, ∀ j ∈ Finset.univ.erase c,
      βL (Additive.ofMul s) i = βL (Additive.ofMul s) j := by
  intro i hi j hj
  by_contra hne
  let v : DVec m := βL (Additive.ofMul s)
  let cfun : Fin m → F0ˣ := fun k => ω ^ (v k).val
  have hcfun_ne : cfun i ≠ cfun j := qtwoDB12_pow_val_ne hcoords.ω_order hne
  have hs_ind : qTwoChartTwoThree_induces ψ (s : G) cfun := hcoords.induces s
  have hij : i ≠ j := fun h => hne (by rw [h])
  let u : Su F0 2 1 m := ggPermSU (K := F0) (f := 1) (Equiv.swap i j)
  have hu_pair : u ∈ coordBlockSU F0 2 1 ({i, j} : Finset (Fin m)) :=
    qtwoDB12_permSU_mem_coordBlockSU (K := F0) hij
  have hsub : ({i, j} : Finset (Fin m)) ⊆ Finset.univ.erase c := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hi
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact hj
  have hu_mem : u ∈ coordBlockSU F0 2 1 (Finset.univ.erase c) :=
    qTwoS34_coordBlockSU_mono hsub hu_pair
  obtain ⟨u', hu'mat, hu'ψ⟩ := hs_ind u
  have hJ : ψ u ∈ ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ : Subgroup G) :=
    Subgroup.mem_map.mpr ⟨u, hu_mem, rfl⟩
  have hsu : ψ u * (s : G) = (s : G) * ψ u :=
    (Subgroup.mem_centralizer_iff.mp hs) (ψ u) hJ
  have hconj : (s : G) * ψ u * (s : G)⁻¹ = ψ u := by
    rw [← hsu]
    group
  have hψu' : ψ u' = ψ u := by
    rw [hu'ψ, hconj]
  have hz : u' * u⁻¹ ∈ Subgroup.center (Su F0 2 1 m) := by
    apply hbase.hyp.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψu', mul_inv_cancel]
  exact hcfun_ne (qtwoDB12_diag_eq_of_conj_permSU hbase.card_field (by omega) hu'mat hz)

theorem ggQTwoDUnit_cent_J (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) {c : Fin m} {b' : ↥Bs}
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) :
    Bs ⊓ Subgroup.centralizer
        (((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ : Subgroup G) : Set G) =
      Subgroup.closure {x, (b' : G)} := by
  apply le_antisymm
  · intro s hs
    rw [Subgroup.mem_inf] at hs
    obtain ⟨hsBs, hscen⟩ := hs
    let s' : ↥Bs := ⟨s, hsBs⟩
    have hscen' : (s' : G) ∈ Subgroup.centralizer
        (((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ : Subgroup G) : Set G) := hscen
    have hconst := qtwoDB12_const_of_mem_centralizer hbase hcoords hm hscen'
    obtain ⟨c0, hc0⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) c
    exact qtwoDB12_mem_closure_of_const hbase.x_mem (hcoords.x_coord hbase.x_mem) hc0 hb' hconst
  · rw [Subgroup.closure_le]
    rintro z (hx | hb)
    · rw [hx]
      refine Subgroup.mem_inf.mpr ⟨hbase.x_mem, ?_⟩
      have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
        have hx' : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
          rw [hbase.cent]
          exact Subgroup.mem_zpowers x
        exact (Subgroup.mem_inf.mp hx').2
      have hJ1L : ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ : Subgroup G) ≤ L := by
        rw [← hbase.range]
        exact Subgroup.map_le_range ψ _
      exact Subgroup.centralizer_le hJ1L hxL
    · rw [Set.mem_singleton_iff] at hb
      rw [hb]
      refine Subgroup.mem_inf.mpr ⟨b'.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
      let cfun : Fin m → F0ˣ := fun k => ω ^ (βL (Additive.ofMul b') k).val
      have hcfun_const : ∀ p ∈ Finset.univ.erase c, ∀ q ∈ Finset.univ.erase c,
          (cfun p : F0) = (cfun q : F0) := by
        intro p hp q hq
        have hp' : cfun p = 1 := by
          rw [Finset.mem_erase] at hp
          simp only [cfun, hb', Pi.single_eq_of_ne hp.1, ZMod.val_zero, pow_zero]
        have hq' : cfun q = 1 := by
          rw [Finset.mem_erase] at hq
          simp only [cfun, hb', Pi.single_eq_of_ne hq.1, ZMod.val_zero, pow_zero]
        rw [hp', hq']
      have hcomm : qTwoChartTwoThree_diag cfun * (u : GL (Fin m) F0) =
          (u : GL (Fin m) F0) * qTwoChartTwoThree_diag cfun := by
        apply Units.ext
        change Matrix.diagonal (fun i => (cfun i : F0)) *
            ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
          ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
            Matrix.diagonal (fun i => (cfun i : F0))
        exact diagonal_mul_comm_of_mem_coordBlockSU hu hcfun_const
      obtain ⟨u', hu'mat, hu'ψ⟩ := hcoords.induces b' u
      have hu'u : (u' : GL (Fin m) F0) = (u : GL (Fin m) F0) := by
        rw [hu'mat]
        calc qTwoChartTwoThree_diag cfun * (u : GL (Fin m) F0) *
              (qTwoChartTwoThree_diag cfun)⁻¹
            = (u : GL (Fin m) F0) * qTwoChartTwoThree_diag cfun *
                (qTwoChartTwoThree_diag cfun)⁻¹ := by rw [hcomm]
          _ = (u : GL (Fin m) F0) := by group
      have hconj : (b' : G) * ψ u * (b' : G)⁻¹ = ψ u := by
        have hu'u' : u' = u := Subtype.ext hu'u
        rw [← hu'ψ, hu'u']
      have hcomm : (b' : G) * ψ u = ψ u * (b' : G) := by
        calc (b' : G) * ψ u = (b' : G) * ψ u * (b' : G)⁻¹ * (b' : G) := by group
          _ = ψ u * (b' : G) := by rw [hconj]
      exact hcomm.symm

theorem ggQTwoDUnit_J_iso (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε) (c : Fin m)
    (g : G) :
    ∃ θ : Su F0 2 1 (m - 1) →* G, Function.Injective θ ∧
      θ.range = (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ ∧
      ((MulAut.conj g).toMonoidHom.comp θ).range =
        ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ).map (MulAut.conj g).toMonoidHom := by
  classical
  let S : Finset (Fin m) := Finset.univ.erase c
  have hcard : S.card = m - 1 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  have hcS : c ∉ S := by
    dsimp [S]
    exact Finset.notMem_erase c Finset.univ
  let e : Su F0 2 1 (m - 1) ≃* Su F0 2 1 S.card :=
    (MulEquiv.cast (M := fun n => Su F0 2 1 n) hcard).symm
  have hcomp_inj : Function.Injective (ψ.comp (blockSUOn F0 2 1 S)) := by
    intro u v huv
    have hmemu : blockSUOn F0 2 1 S u ∈ coordBlockSU F0 2 1 S := ⟨u, rfl⟩
    have hmemv : blockSUOn F0 2 1 S v ∈ coordBlockSU F0 2 1 S := ⟨v, rfl⟩
    have huv' : (fun w : ↥(coordBlockSU F0 2 1 S) => ψ (w : Su F0 2 1 m))
        ⟨blockSUOn F0 2 1 S u, hmemu⟩ =
        (fun w : ↥(coordBlockSU F0 2 1 S) => ψ (w : Su F0 2 1 m))
          ⟨blockSUOn F0 2 1 S v, hmemv⟩ := huv
    have hEq := qtwoDB12_injective_block hbase hcS huv'
    exact blockSUOn_injective S (Subtype.ext_iff.mp hEq)
  have hrange : ((ψ.comp (blockSUOn F0 2 1 S)).comp e.toMonoidHom).range =
      (coordBlockSU F0 2 1 S).map ψ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective,
      ← MonoidHom.range_eq_map, MonoidHom.range_comp]
    rfl
  refine ⟨(ψ.comp (blockSUOn F0 2 1 S)).comp e.toMonoidHom, hcomp_inj.comp e.injective,
    hrange, ?_⟩
  rw [MonoidHom.range_comp, hrange]

theorem ggQTwoDUnit_common (hEA : GGQTwoEdgeAmbientInput) (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hm : 7 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e') (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) {a b c : Fin m} (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign m a b (βL (Additive.ofMul s))) {g : G}
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) :
    (coordBlockSU F0 2 1 ((Finset.univ.erase c) \ {a, b})).map ψ ≤
        (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ ∧
      (coordBlockSU F0 2 1 ((Finset.univ.erase c) \ {a, b})).map ψ ≤
        ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ).map (MulAut.conj g).toMonoidHom ∧
      ⁅(coordBlockSU F0 2 1 ((Finset.univ.erase c) \ {a, b})).map ψ,
        (coordBlockSU F0 2 1 ((Finset.univ.erase c) \ {a, b})).map ψ⁆ =
        (coordBlockSU F0 2 1 ((Finset.univ.erase c) \ {a, b})).map ψ ∧
      3 ∣ Nat.card ↥((coordBlockSU F0 2 1 ((Finset.univ.erase c) \ {a, b})).map ψ) := by
  classical
  set S : Finset (Fin m) := Finset.univ.erase c with hS
  set T : Finset (Fin m) := S \ {a, b} with hT
  have hcardS : S.card = m - 1 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  have hcardT : T.card = m - 3 := by
    have h1 : T.card = S.card - ({a, b} : Finset (Fin m)).card := by
      have hinter : ({a, b} : Finset (Fin m)) ∩ S = {a, b} := by
        apply Finset.ext
        intro y
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hy, _⟩
          exact hy
        · intro hy
          refine ⟨hy, ?_⟩
          rw [hS, Finset.mem_erase]
          rcases hy with hya | hyb
          · rw [hya]
            exact ⟨hca.symm, Finset.mem_univ a⟩
          · rw [hyb]
            exact ⟨hcb.symm, Finset.mem_univ b⟩
      rw [hT, Finset.card_sdiff, hinter]
    rw [h1, hcardS, Finset.card_insert_of_notMem (by simpa using hab),
      Finset.card_singleton]
    omega
  have hcardT3 : 3 ≤ T.card := by rw [hcardT]; omega
  have haT : a ∉ T := by rw [hT]; simp
  have hbT : b ∉ T := by rw [hT]; simp
  have hTS : T ⊆ S := by rw [hT]; exact Finset.sdiff_subset
  have hshared := ggQTwoDUnit_shared hEA hcfg e' hm hM hbase hcoords hab hα hgN hg
    (T := T) hcardT3 haT hbT
  have hP1 : (coordBlockSU F0 2 1 T).map ψ ≤ (coordBlockSU F0 2 1 S).map ψ :=
    Subgroup.map_mono (qTwoS34_coordBlockSU_mono hTS)
  refine ⟨hP1, ?_, ?_, ?_⟩
  · exact hshared ▸ Subgroup.map_mono hP1
  · haveI : Group.IsPerfect ↥((coordBlockSU F0 2 1 T).map ψ) := by
      haveI : Group.IsPerfect ↥(coordBlockSU F0 2 1 T) := by
        haveI : Group.IsPerfect (Su F0 2 1 T.card) :=
          isPerfect_Su hbase.card_field (by rw [hcardT]; omega)
        exact Group.IsPerfect.range (blockSUOn F0 2 1 T)
      exact Group.IsPerfect.map (f := ψ)
    exact Subgroup.commutator_eq_self
  · obtain ⟨s, hsT, hscard⟩ := Finset.exists_subset_card_eq (show 3 ≤ T.card by rw [hcardT]; omega)
    have hle : (coordBlockSU F0 2 1 s).map ψ ≤ (coordBlockSU F0 2 1 T).map ψ :=
      Subgroup.map_mono (qTwoS34_coordBlockSU_mono hsT)
    have hdvd : 3 ∣ Nat.card ↥((coordBlockSU F0 2 1 s).map ψ) := by
      obtain ⟨a', b', c', hab', hac', hbc', rfl⟩ := Finset.card_eq_three.mp hscard
      rw [qtwoDB12_card_map_coordBlockSU_three hbase (by omega) hab' hbc' hac']
      norm_num
    exact dvd_trans hdvd (Subgroup.card_dvd_of_le hle)

end CFSG.StandardType.QTwo

end
