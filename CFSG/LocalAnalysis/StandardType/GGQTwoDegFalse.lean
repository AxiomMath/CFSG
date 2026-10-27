module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDegDefs
import CFSG.LocalAnalysis.StandardType.GGTypeAFiveProof
import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentLift
import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

section Perm

private lemma qTwoDegFalse_val_ofNat_lt (n : ℕ) [NeZero n] (m : ℕ) (hm : m < n) :
    (Fin.ofNat n m).val = m := by
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt hm]

private lemma qTwoDegFalse_ofNat_ne (n : ℕ) [NeZero n] (a b : ℕ) (ha : a < n) (hb : b < n)
    (hab : a ≠ b) : Fin.ofNat n a ≠ Fin.ofNat n b := by
  intro h
  have h' := congrArg Fin.val h
  rw [qTwoDegFalse_val_ofNat_lt n a ha, qTwoDegFalse_val_ofNat_lt n b hb] at h'
  exact hab h'

variable {n : ℕ} [NeZero n]

private lemma qTwoDegFalse_support_cyc3_subset {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) :
    (Equiv.swap a b * Equiv.swap a c).support ⊆ ({a, b, c} : Finset (Fin n)) := by
  refine (Equiv.Perm.support_mul_le _ _).trans ?_
  rw [Equiv.Perm.support_swap hab, Equiv.Perm.support_swap hac]
  intro x hx
  rw [Finset.sup_eq_union] at hx
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

private lemma qTwoDegFalse_cyc3_mem_support_left {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : a ∈ (Equiv.swap a b * Equiv.swap a c).support := by
  rw [Equiv.Perm.mem_support, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]
  exact Ne.symm hac

private lemma qTwoDegFalse_not_mem_triple {a b c x : Fin n} (hxa : x ≠ a) (hxb : x ≠ b)
    (hxc : x ≠ c) : x ∉ ({a, b, c} : Finset (Fin n)) := by
  intro h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  tauto

private lemma qTwoDegFalse_disjoint_triples {a b c d e f : Fin n}
    (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f) :
    Disjoint ({a, b, c} : Finset (Fin n)) ({d, e, f} : Finset (Fin n)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals tauto

private lemma qTwoDegFalse_exists_noncyclic_perm (n : ℕ) (hn : 6 ≤ n) :
    ∃ P : Subgroup (Equiv.Perm (Fin n)), IsPGroup 3 P ∧ ¬ IsCyclic P := by
  haveI : NeZero n := ⟨by omega⟩
  set x : Equiv.Perm (Fin n) := Equiv.swap 0 1 * Equiv.swap 0 2 with hx
  set y : Equiv.Perm (Fin n) := Equiv.swap 3 4 * Equiv.swap 3 5 with hy
  have hx3 : x.IsThreeCycle := by
    rw [hx]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same
      (qTwoDegFalse_ofNat_ne n 0 1 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 0 2 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 1 2 (by omega) (by omega) (by norm_num))
  have hy3 : y.IsThreeCycle := by
    rw [hy]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same
      (qTwoDegFalse_ofNat_ne n 3 4 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 3 5 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 4 5 (by omega) (by omega) (by norm_num))
  have hx_pow : x ^ 3 = 1 := by
    rw [← hx3.orderOf]
    exact pow_orderOf_eq_one x
  have hy_pow : y ^ 3 = 1 := by
    rw [← hy3.orderOf]
    exact pow_orderOf_eq_one y
  have hx1 : x ≠ 1 := hx3.ne_one
  have hx_supp : x.support ⊆ ({0, 1, 2} : Finset (Fin n)) := by
    rw [hx]
    exact qTwoDegFalse_support_cyc3_subset
      (qTwoDegFalse_ofNat_ne n 0 1 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 0 2 (by omega) (by omega) (by norm_num))
  have hy_supp : y.support ⊆ ({3, 4, 5} : Finset (Fin n)) := by
    rw [hy]
    exact qTwoDegFalse_support_cyc3_subset
      (qTwoDegFalse_ofNat_ne n 3 4 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 3 5 (by omega) (by omega) (by norm_num))
  have hdisj : x.Disjoint y := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support]
    exact Disjoint.mono hx_supp hy_supp (qTwoDegFalse_disjoint_triples
      (qTwoDegFalse_ofNat_ne n 0 3 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 0 4 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 0 5 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 1 3 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 1 4 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 1 5 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 2 3 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 2 4 (by omega) (by omega) (by norm_num))
      (qTwoDegFalse_ofNat_ne n 2 5 (by omega) (by omega) (by norm_num)))
  have hxy : Commute x y := hdisj.commute
  have hyx : y ∉ Subgroup.zpowers x := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have h3y : (3 : Fin n) ∈ y.support := by
      rw [hy]
      exact qTwoDegFalse_cyc3_mem_support_left
        (qTwoDegFalse_ofNat_ne n 3 4 (by omega) (by omega) (by norm_num))
        (qTwoDegFalse_ofNat_ne n 3 5 (by omega) (by omega) (by norm_num))
        (qTwoDegFalse_ofNat_ne n 4 5 (by omega) (by omega) (by norm_num))
    have h3x : (3 : Fin n) ∉ x.support := fun hmem =>
      qTwoDegFalse_not_mem_triple
        (qTwoDegFalse_ofNat_ne n 3 0 (by omega) (by omega) (by norm_num))
        (qTwoDegFalse_ofNat_ne n 3 1 (by omega) (by omega) (by norm_num))
        (qTwoDegFalse_ofNat_ne n 3 2 (by omega) (by omega) (by norm_num))
        (hx_supp hmem)
    have hsub : y.support ⊆ x.support := by
      rw [← hk]
      exact Equiv.Perm.support_zpow_le _ _
    exact h3x (hsub h3y)
  obtain ⟨hPp, hPnc⟩ :=
    CFSG.AGLEmbedding.ToralCensus.not_isCyclic_closure_pair hxy hx_pow hy_pow hx1 hyx
  exact ⟨Subgroup.closure {x, y}, hPp, hPnc⟩

end Perm

theorem qTwoDegFalse_exists_noncyclic {Bs L : Subgroup G} {m : ℕ} (hm : 6 ≤ m)
    (hW : GGWeylOfType 3 (CoxeterMatrix.A (m - 1)) (ggAutomizer L Bs)) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  obtain ⟨eL, -⟩ := hW
  obtain ⟨e0, -⟩ := ggCoxeterA_mulEquivPerm (m - 1)
  obtain ⟨P, hPp, hPnc⟩ := qTwoDegFalse_exists_noncyclic_perm (m - 1 + 1) (by omega)
  let eA : ↥(ggAutomizer L Bs) ≃* Equiv.Perm (Fin (m - 1 + 1)) := eL.symm.trans e0
  let Q : Subgroup ↥(ggAutomizer L Bs) := P.map eA.symm.toMonoidHom
  have hQp : IsPGroup 3 Q := hPp.map eA.symm.toMonoidHom
  have hQnc : ¬ IsCyclic Q := fun hc =>
    hPnc ((P.equivMapOfInjective eA.symm.toMonoidHom eA.symm.injective).isCyclic.mpr hc)
  obtain ⟨QSyl, hQle⟩ := IsPGroup.exists_le_sylow hQp
  have hQSyl_nc : ¬ IsCyclic ↥(QSyl : Subgroup ↥(ggAutomizer L Bs)) := by
    intro hcyc
    haveI := hcyc
    exact hQnc (Subgroup.isCyclic_of_le hQle)
  let H : Subgroup G := L ⊓ Subgroup.normalizer (Bs : Set G)
  let f : ↥H →* ↥(ggAutomizer L Bs) :=
    { toFun := fun g => ⟨ggConjAut Bs g.2.2, ggConjAut_mem_ggAutomizer g.2.1 g.2.2⟩
      map_one' := Subtype.ext (by ext b; simp [ggConjAut_apply])
      map_mul' := fun a b => Subtype.ext (by
        ext x
        simp only [MulAut.mul_apply, ggConjAut_apply, Subgroup.coe_mul]
        group) }
  have hf_surj : Function.Surjective f := by
    rintro ⟨φ, hφmem⟩
    obtain ⟨g, hgL, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hφmem
    refine ⟨⟨g, Subgroup.mem_inf.mpr ⟨hgL, hgN⟩⟩, ?_⟩
    apply Subtype.ext
    show ggConjAut Bs hgN = φ
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply]
    exact (hgφ b).symm
  obtain ⟨PSyl, hPSyl⟩ := Sylow.mapSurjective_surjective (f := f) hf_surj 3 QSyl
  have hmap : (PSyl : Subgroup ↥H).map f = (QSyl : Subgroup ↥(ggAutomizer L Bs)) := by
    rw [← hPSyl, Sylow.coe_mapSurjective]
  have hPSyl_nc : ¬ IsCyclic ↥(PSyl : Subgroup ↥H) := by
    intro hcyc
    haveI := hcyc
    apply hQSyl_nc
    have hsurj : Function.Surjective
        ((f.comp (PSyl : Subgroup ↥H).subtype).codRestrict
          (QSyl : Subgroup ↥(ggAutomizer L Bs)) (fun x => by
            rw [← hmap]
            exact Subgroup.mem_map_of_mem f x.2)) := by
      intro y
      have hy : (y : ↥(ggAutomizer L Bs)) ∈ (PSyl : Subgroup ↥H).map f := by
        rw [hmap]
        exact y.2
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact isCyclic_of_surjective _ hsurj
  let S : Subgroup G := (PSyl : Subgroup ↥H).map (Subgroup.subtype H)
  have hSL : S ≤ L := by
    rintro g ⟨x, hx, rfl⟩
    exact x.2.1
  have hSp : IsPGroup 3 S := (PSyl.isPGroup').map (Subgroup.subtype H)
  have hSnc : ¬ IsCyclic S := by
    intro hcyc
    haveI := hcyc
    exact hPSyl_nc (isCyclic_of_surjective
      ((PSyl : Subgroup ↥H).equivMapOfInjective (Subgroup.subtype H)
        (Subgroup.subtype_injective H)).symm (MulEquiv.surjective _))
  exact ⟨S, hSL, hSp, hSnc⟩

theorem qTwoDegFalse_centralizer_le_normalizer {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S) :
    Subgroup.centralizer (Bs : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  have hS : CFSG.Assembly.LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hDJ : CFSG.Assembly.LargeEvenStdSubPre 3 B x L D J := hcfg.2.2.1
  have hCB : Subgroup.centralizer (Bs : Set G) ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.centralizer_le hcfg.2.1.1
  have hCx : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hS.2.1)
  have hCD : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.centralizer_le hDJ.1
  rw [hDJ.2.2.2.2.1]
  exact le_normalizer_of_map_conj_le fun g hg => map_conj_largeEvenLayer_le
    (mem_normalizer_inf_centralizer (mem_normalizer_of_sstar hS hnc (hCx (hCB hg)))
      (hCD (hCB hg)))

open scoped commutatorElement in
theorem qTwoDeg_false_of_equal_degree
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {k : QTwoRowKind} {m d c : ℕ} (hrow : QTwoRowData k m d c Bs L x) (hm : 5 ≤ m)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    {N : ℕ} (hN : 6 ≤ N) {e' : Fin (N - 1) ≃ ι}
    (hM : M = (CoxeterMatrix.A (N - 1)).reindex e')
    (hNm : N = m)
    (hrm : ∀ (y : G) (K' : Subgroup G), GGNbr 3 B x D J y K' →
      ggAutomizer K' Bs ≤ ggAutomizer L Bs)
    (hgn : ∀ (y : G) (K' : Subgroup G), GGNbr 3 B x D J y K' →
      ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 →
      K' ≤ ⨆ (n : G) (_ : n ∈ K') (_ : ∃ φ : MulAut ↥Bs,
          n ∈ Subgroup.normalizer (Bs : Set G) ∧
            ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹),
        J.map (MulAut.conj n).toMonoidHom) :
    False := by
  have hcfg0 : GGConfig 3 B Bs x L D J := hcfg.1.1
  have hnc := qTwoDegFalse_exists_noncyclic (Bs := Bs) (L := L) (m := m) (by omega) hrow.weyl
  have hJN := qTwoDegFalse_centralizer_le_normalizer hcfg0 hnc
  obtain ⟨y, K, hK⟩ := exists_ggNbr hcfg0.1.2.2.2.2.2.2.2 hcfg0.2.2
  have hA : ggAutomizer K Bs ≤ ggAutomizer L Bs := hrm y K hK
  have hgen := hgn y K hK (hA.trans le_sup_left)
  have hgen' : K ≤ ⨆ (g : G) (_ : g ∈ K ⊓ Subgroup.normalizer (Bs : Set G)),
      J.map (MulAut.conj g).toMonoidHom := by
    refine hgen.trans (iSup₂_le fun n hn => iSup_le fun hφ => ?_)
    obtain ⟨φ, hnN, -⟩ := hφ
    exact le_iSup₂_of_le n ⟨hn, hnN⟩ le_rfl
  have hKL : K ≤ L := le_of_ggAutomizer_le_of_conjGen hcfg0.stdSub_le hJN hgen' hA
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg0.1.2.2.2.2.2.2.1.2.2.2.1.1
  refine hK.2.2.2 (Subgroup.commutator_le.mpr fun k hk z hz => ?_)
  have hkx : k * x = x * k := Subgroup.mem_centralizer_singleton_iff.mp (hLx (hKL hk))
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have h1 : ⁅k, x ^ n⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_commute]
    exact Commute.zpow_right (show Commute k x from hkx) n
  rw [h1]
  exact Subgroup.one_mem _

end CFSG.StandardType.QTwo

end
