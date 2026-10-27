module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.GH74.GLS.Stage4.SDWLayerFieldU
public import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.L2.SylowAux
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.GH74.GLS.Stage4.RestP93
public import CFSG.GH74.GLS.Stage4.T2Defs
public import CFSG.GH74.GLS.Stage4.T2SL2C
public import CFSG.GH74.GLS.Stage4.T2Sylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldLang

private theorem ggK1A_fixSub_conj_eq_centralizer {R : Type} [Group R] (r : R) :
    ggFixSub (MulAut.conj r) = Subgroup.centralizer ({r} : Set R) := by
  ext l
  rw [mem_ggFixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    have h1 : r * l = l * r := by
      calc r * l = r * l * r⁻¹ * r := by group
        _ = l * r := by rw [h]
    exact h1.symm
  · intro h
    calc r * l * r⁻¹ = l * r * r⁻¹ := by rw [← h]
      _ = l := by group

private theorem ggK1A_core_quasisimple {R L' : Type} [Group L'] [Group R]
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {K : Subgroup R} (hKperf : commutator ↥K = ⊤)
    (hKsimple : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K)) :
    CFSG.Assembly.IsQuasisimple ↥(⁅K.comap ψ, K.comap ψ⁆) := by
  let f : ↥(K.comap ψ) →* ↥K :=
    { toFun := fun x => ⟨ψ (x : L'), Subgroup.mem_comap.mp x.2⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun x y => Subtype.ext (map_mul ψ (x : L') (y : L')) }
  have hfsurj : Function.Surjective f := by
    rintro ⟨k, hk⟩
    obtain ⟨l, rfl⟩ := hψ k
    exact ⟨⟨l, hk⟩, rfl⟩
  have hfker : f.ker ≤ Subgroup.center ↥(K.comap ψ) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxψ : ψ (x : L') = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      simpa [f] using this
    exact Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hxψ)) (y : L')
  have hKqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).mp
      ⟨hKperf, hKsimple⟩
  have hHq : CFSG.IsQuasisimple (commutator ↥(K.comap ψ)) :=
    CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective f hfsurj hfker hKqs
  let e : (commutator ↥(K.comap ψ)) ≃*
      ↥((commutator ↥(K.comap ψ)).map (K.comap ψ).subtype) :=
    Subgroup.equivMapOfInjective _ (K.comap ψ).subtype (K.comap ψ).subtype_injective
  have hHq' : CFSG.IsQuasisimple
      ↥((commutator ↥(K.comap ψ)).map (K.comap ψ).subtype) :=
    CFSG.IsQuasisimple.of_mulEquiv e.symm hHq
  have hQqsNative : CFSG.IsQuasisimple ↥(⁅K.comap ψ, K.comap ψ⁆) := by
    rw [Subgroup.map_subtype_commutator] at hHq'
    exact hHq'
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
    ↥(⁅K.comap ψ, K.comap ψ⁆)).mpr hQqsNative


private theorem ggK1A_isComponentOf_comap_commutator {R L' : Type} [Group L'] [Group R]
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (e : MulAut L') (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) {K : Subgroup R}
    (hK : CFSG.Assembly.IsComponentOf K (ggFixSub φ)) :
    CFSG.Assembly.IsComponentOf ⁅K.comap ψ, K.comap ψ⁆ (ggFixSub e) ∧
      (⁅K.comap ψ, K.comap ψ⁆).map ψ = K := by
  obtain ⟨hKle, hKsub, hKperf, hKsimple⟩ := hK
  have hKperfSet : ⁅K, K⁆ = K := by
    rw [← Subgroup.map_subtype_commutator K, hKperf, Subgroup.map_top,
      Subgroup.range_subtype]
  have hQperfect := ggPerfectCore ψ hψ hker K hKperfSet
  have hQmap : (⁅K.comap ψ, K.comap ψ⁆).map ψ = K := hQperfect.1
  have hQcomm : ⁅⁅K.comap ψ, K.comap ψ⁆, ⁅K.comap ψ, K.comap ψ⁆⁆ = ⁅K.comap ψ, K.comap ψ⁆ :=
    hQperfect.2
  have hQqs := ggK1A_core_quasisimple ψ hψ hker hKperf hKsimple
  have hQleC' : ⁅K.comap ψ, K.comap ψ⁆ ≤ ggFixSub e :=
    ggFixes_core ψ hker e φ (fun l => (hφ l).symm) (K.comap ψ)
      (fun _ hl => mem_ggFixSub.mp (hKle (Subgroup.mem_comap.mp hl)))
  have hC'le : ggFixSub e ≤ (ggFixSub φ).comap ψ := by
    intro l hl
    rw [Subgroup.mem_comap, mem_ggFixSub]
    rw [hφ l, mem_ggFixSub.1 hl]
  have hPsub : CFSG.Assembly.IsSubnormal (K.comap ψ) ((ggFixSub φ).comap ψ) :=
    hKsub.comap ψ
  have hsub1 : CFSG.Assembly.IsSubnormal ((K.comap ψ) ⊓ ggFixSub e) (ggFixSub e) := by
    have h := hPsub.inf (ggFixSub e)
    rwa [inf_eq_right.2 hC'le] at h
  have hQleP : ⁅K.comap ψ, K.comap ψ⁆ ≤ K.comap ψ := Subgroup.commutator_le_self _
  have hQnormal : ((⁅K.comap ψ, K.comap ψ⁆).subgroupOf ((K.comap ψ) ⊓ ggFixSub e)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_inf hQleP hQleC')).2
      (inf_le_left.trans (Subgroup.normalizer_commutator_ge_left _ _))
  have hsubQ : CFSG.Assembly.IsSubnormal ⁅K.comap ψ, K.comap ψ⁆ (ggFixSub e) :=
    CFSG.Assembly.IsSubnormal.step (le_inf hQleP hQleC') hQnormal hsub1
  exact ⟨⟨hQleC', hsubQ, hQqs⟩, hQmap⟩

private lemma ggMultDatumA_orbits (p nf d : ℕ) (tw : Bool) (m : List ℕ) :
    (ggMultDatumA p nf d tw m).orbits =
      (let H := (p - 1) / 2
       let trivial := (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2)
       if trivial then
         ((List.range p).filter (fun j => decide (2 ≤ m.getD j 0))).map
           (fun j => ggMultBlockA (m.getD j 0 - 1) nf d)
       else
         (if 2 ≤ m.headD 0 then
           let r := m.headD 0 - 1
           if tw = false then [⟨⟨.A, r, nf⟩, decide (¬ (r = 1 ∧ nf = 1))⟩]
           else [ggMultBlockA r nf 2]
         else []) ++
         ((List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0))).map
           (fun j => ⟨⟨.A, m.getD j 0 - 1, 2 * nf⟩, true⟩)) := by
  simp only [ggMultDatumA]
  split_ifs <;> rfl

private lemma kindOrbit_sl_one (nf n : ℕ) (h2n : 2 ≤ n) :
    ggK1ACo_kindOrbit nf (.sl n 1) =
      ⟨⟨.A, n - 1, nf⟩, decide (¬ (n - 1 = 1 ∧ nf = 1))⟩ := by
  unfold ggK1ACo_kindOrbit
  split
  · rename_i e heq
    simp only [ggK1ACo_Kind.sl.injEq] at heq
    omega
  · simp_all
  · rename_i m e hne heq
    simp only [ggK1ACo_Kind.sl.injEq] at heq
    obtain ⟨hm, he⟩ := heq
    subst hm; subst he
    simp [ggMultBlockA]
  · simp_all

private lemma kindOrbit_su_one (nf n : ℕ) (h2n : 2 ≤ n) :
    ggK1ACo_kindOrbit nf (.su n 1) = ggMultBlockA (n - 1) nf 2 := by
  unfold ggK1ACo_kindOrbit
  split
  · simp_all
  · rename_i e heq
    simp only [ggK1ACo_Kind.su.injEq] at heq
    omega
  · simp_all
  · rename_i m e hne heq
    simp only [ggK1ACo_Kind.su.injEq] at heq
    obtain ⟨hm, he⟩ := heq
    subst hm; subst he
    simp

private lemma kindOrbit_sl_two (nf n : ℕ) (h2n : 2 ≤ n) :
    ggK1ACo_kindOrbit nf (.sl n 2) =
      ⟨⟨.A, n - 1, 2 * nf⟩, decide (¬ (n - 1 = 1 ∧ 2 * nf = 1))⟩ := by
  unfold ggK1ACo_kindOrbit
  split
  · rename_i e heq
    simp only [ggK1ACo_Kind.sl.injEq] at heq
    omega
  · simp_all
  · rename_i m e hne heq
    simp only [ggK1ACo_Kind.sl.injEq] at heq
    obtain ⟨hm, he⟩ := heq
    subst hm; subst he
    simp [ggMultBlockA]
  · simp_all

private lemma hasOrbit_sl_one_of_two (n : ℕ) (h2 : 2 ≤ n) :
    ggK1ACo_Kind.hasOrbit (.sl n 1) = true := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rfl

private lemma hasOrbit_su_one_of_two (n : ℕ) (h2 : 2 ≤ n) :
    ggK1ACo_Kind.hasOrbit (.su n 1) = true := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rfl

private lemma hasOrbit_sl_two_of_two (n : ℕ) (h2 : 2 ≤ n) :
    ggK1ACo_Kind.hasOrbit (.sl n 2) = true := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rfl

private lemma orbit_tail (nf : ℕ) (m : List ℕ) (L : List ℕ) :
    (List.filter (fun k => ggK1ACo_Kind.hasOrbit k)
      (List.map (fun j => ggK1ACo_Kind.sl (m.getD j 0) 2)
        (List.filter (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0)) L))).map
      (ggK1ACo_kindOrbit nf)
    = (List.filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0)) L).map
       (fun j => (⟨⟨.A, m.getD j 0 - 1, 2 * nf⟩, true⟩ : GGKacOrbit)) := by
  rw [List.filter_map, List.map_map, List.filter_filter]
  have hflt : List.filter (fun j => (ggK1ACo_Kind.sl (m.getD j 0) 2).hasOrbit &&
      decide (1 ≤ j ∧ 0 < m.getD j 0)) L =
      List.filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0)) L := by
    apply List.filter_congr
    intro j hj
    change (ggK1ACo_Kind.hasOrbit (ggK1ACo_Kind.sl (m[j]?.getD 0) 2) &&
      decide (1 ≤ j ∧ 0 < m[j]?.getD 0)) = decide (1 ≤ j ∧ 2 ≤ m[j]?.getD 0)
    by_cases h2 : 2 ≤ m[j]?.getD 0
    · rw [hasOrbit_sl_two_of_two _ h2]
      simp only [Bool.true_and, decide_eq_decide]
      omega
    · have hle : m[j]?.getD 0 ≤ 1 := by omega
      obtain h0 | h1 : m[j]?.getD 0 = 0 ∨ m[j]?.getD 0 = 1 := by omega
      · rw [h0]
        simp [ggK1ACo_Kind.hasOrbit]
      · rw [h1]
        simp [ggK1ACo_Kind.hasOrbit]
  simp only [Function.comp_apply]
  rw [hflt]
  apply List.map_congr_left
  intro j hj
  have h2 : 2 ≤ m[j]?.getD 0 := by
    simp only [List.mem_filter, decide_eq_true_eq] at hj
    exact hj.2.2
  change ggK1ACo_kindOrbit nf (ggK1ACo_Kind.sl (m[j]?.getD 0) 2) =
    (⟨⟨.A, m[j]?.getD 0 - 1, 2 * nf⟩, true⟩ : GGKacOrbit)
  rw [kindOrbit_sl_two nf _ h2]
  congr 1
  simp only [decide_eq_true_eq]
  intro h; rw [Nat.two_mul] at h; omega

private lemma orbit_trivial_false (nf p : ℕ) (m : List ℕ) :
    (List.filter (fun k => ggK1ACo_Kind.hasOrbit k)
      (List.map (fun j => ggK1ACo_Kind.sl (m.getD j 0) 1)
        (List.filter (fun j => decide (0 < m.getD j 0)) (List.range p)))).map
      (ggK1ACo_kindOrbit nf)
    = (List.filter (fun j => decide (2 ≤ m.getD j 0)) (List.range p)).map
       (fun j => ggMultBlockA (m.getD j 0 - 1) nf 1) := by
  rw [List.filter_map, List.map_map, List.filter_filter]
  have hflt : List.filter (fun j => (ggK1ACo_Kind.sl (m.getD j 0) 1).hasOrbit &&
      decide (0 < m.getD j 0)) (List.range p) =
      List.filter (fun j => decide (2 ≤ m.getD j 0)) (List.range p) := by
    apply List.filter_congr
    intro j hj
    change (ggK1ACo_Kind.hasOrbit (ggK1ACo_Kind.sl (m[j]?.getD 0) 1) &&
      decide (0 < m[j]?.getD 0)) = decide (2 ≤ m[j]?.getD 0)
    by_cases h2 : 2 ≤ m[j]?.getD 0
    · rw [hasOrbit_sl_one_of_two _ h2]
      simp only [Bool.true_and, decide_eq_decide]
      omega
    · have hle : m[j]?.getD 0 ≤ 1 := by omega
      obtain h0 | h1 : m[j]?.getD 0 = 0 ∨ m[j]?.getD 0 = 1 := by omega
      · rw [h0]
        simp [ggK1ACo_Kind.hasOrbit]
      · rw [h1]
        simp [ggK1ACo_Kind.hasOrbit]
  simp only [Function.comp_apply]
  rw [hflt]
  apply List.map_congr_left
  intro j hj
  have h2 : 2 ≤ m[j]?.getD 0 := by
    simp only [List.mem_filter, decide_eq_true_eq] at hj
    exact hj.2
  change ggK1ACo_kindOrbit nf (ggK1ACo_Kind.sl (m[j]?.getD 0) 1) =
    ggMultBlockA (m[j]?.getD 0 - 1) nf 1
  rw [kindOrbit_sl_one nf _ h2]
  simp [ggMultBlockA]

private lemma orbit_trivial_true (nf p : ℕ) (m : List ℕ) :
    (List.filter (fun k => ggK1ACo_Kind.hasOrbit k)
      (List.map (fun j => ggK1ACo_Kind.su (m.getD j 0) 1)
        (List.filter (fun j => decide (0 < m.getD j 0)) (List.range p)))).map
      (ggK1ACo_kindOrbit nf)
    = (List.filter (fun j => decide (2 ≤ m.getD j 0)) (List.range p)).map
       (fun j => ggMultBlockA (m.getD j 0 - 1) nf 2) := by
  rw [List.filter_map, List.map_map, List.filter_filter]
  have hflt : List.filter (fun j => (ggK1ACo_Kind.su (m.getD j 0) 1).hasOrbit &&
      decide (0 < m.getD j 0)) (List.range p) =
      List.filter (fun j => decide (2 ≤ m.getD j 0)) (List.range p) := by
    apply List.filter_congr
    intro j hj
    change (ggK1ACo_Kind.hasOrbit (ggK1ACo_Kind.su (m[j]?.getD 0) 1) &&
      decide (0 < m[j]?.getD 0)) = decide (2 ≤ m[j]?.getD 0)
    by_cases h2 : 2 ≤ m[j]?.getD 0
    · rw [hasOrbit_su_one_of_two _ h2]
      simp only [Bool.true_and, decide_eq_decide]
      omega
    · have hle : m[j]?.getD 0 ≤ 1 := by omega
      obtain h0 | h1 : m[j]?.getD 0 = 0 ∨ m[j]?.getD 0 = 1 := by omega
      · rw [h0]
        simp [ggK1ACo_Kind.hasOrbit]
      · rw [h1]
        simp [ggK1ACo_Kind.hasOrbit]
  simp only [Function.comp_apply]
  rw [hflt]
  apply List.map_congr_left
  intro j hj
  have h2 : 2 ≤ m[j]?.getD 0 := by
    simp only [List.mem_filter, decide_eq_true_eq] at hj
    exact hj.2
  change ggK1ACo_kindOrbit nf (ggK1ACo_Kind.su (m[j]?.getD 0) 1) =
    ggMultBlockA (m[j]?.getD 0 - 1) nf 2
  rw [kindOrbit_su_one nf _ h2]

private lemma orbit_head_false (nf : ℕ) (m0 : ℕ) :
    (List.filter (fun k => ggK1ACo_Kind.hasOrbit k)
      (if 0 < m0 then [ggK1ACo_Kind.sl m0 1] else [])).map (ggK1ACo_kindOrbit nf)
    = (if 2 ≤ m0 then [⟨⟨.A, m0 - 1, nf⟩, decide (¬ (m0 - 1 = 1 ∧ nf = 1))⟩]
        else []) := by
  by_cases h0 : 0 < m0
  · by_cases h2 : 2 ≤ m0
    · have hm1 : m0 ≠ 1 := by omega
      simp only [h0, h2, if_true, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil]
      rw [if_pos (by simp [ggK1ACo_Kind.hasOrbit, hm1])]
      change [ggK1ACo_kindOrbit nf (ggK1ACo_Kind.sl m0 1)] = _
      rw [kindOrbit_sl_one nf _ h2]
    · have hm1 : m0 = 1 := by omega
      subst hm1
      simp [ggK1ACo_Kind.hasOrbit]
  · have h2 : ¬ 2 ≤ m0 := by omega
    simp [h0, h2]

private lemma orbit_head_true (nf : ℕ) (m0 : ℕ) :
    (List.filter (fun k => ggK1ACo_Kind.hasOrbit k)
      (if 0 < m0 then [ggK1ACo_Kind.su m0 1] else [])).map (ggK1ACo_kindOrbit nf)
    = (if 2 ≤ m0 then [ggMultBlockA (m0 - 1) nf 2] else []) := by
  by_cases h0 : 0 < m0
  · by_cases h2 : 2 ≤ m0
    · have hm1 : m0 ≠ 1 := by omega
      simp only [h0, h2, if_true, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil]
      rw [if_pos (by simp [ggK1ACo_Kind.hasOrbit, hm1])]
      change [ggK1ACo_kindOrbit nf (ggK1ACo_Kind.su m0 1)] = _
      rw [kindOrbit_su_one nf _ h2]
    · have hm1 : m0 = 1 := by omega
      subst hm1
      simp [ggK1ACo_Kind.hasOrbit]
  · have h2 : ¬ 2 ≤ m0 := by omega
    simp [h0, h2]

private lemma orbitList_false_one (p nf : ℕ) (m : List ℕ) (hd : ggMultOrd p nf = 1) :
    ((ggK1ACo_orbitKindList p nf false m).map (ggK1ACo_kindOrbit nf)) =
      (ggMultDatumA p nf 1 false m).orbits := by
  rw [ggMultDatumA_orbits]
  simp only [ggK1ACo_orbitKindList, ggK1ACo_expectedKindList, hd, Bool.false_eq_true,
    if_true, if_false, List.filter_append, List.map_append]
  exact orbit_trivial_false nf p m

private lemma orbitList_false_ne_one (p nf : ℕ) (m : List ℕ) (hd : ggMultOrd p nf ≠ 1) :
    ((ggK1ACo_orbitKindList p nf false m).map (ggK1ACo_kindOrbit nf)) =
      (ggMultDatumA p nf (ggMultOrd p nf) false m).orbits := by
  rw [ggMultDatumA_orbits]
  simp only [ggK1ACo_orbitKindList, ggK1ACo_expectedKindList, hd, Bool.false_eq_true,
    if_true, if_false, List.filter_append, List.map_append]
  have hcond : ¬ (True ∧ False ∨ False ∧ ggMultOrd p nf = 2) := by simp
  simp only [if_neg hcond, List.filter_append, List.map_append]
  exact congrArg₂ (· ++ ·) (orbit_head_false nf (m.headD 0))
    (orbit_tail nf m (List.range ((p - 1) / 2 + 1)))

private lemma orbitList_true_two (p nf : ℕ) (m : List ℕ) (hd : ggMultOrd p nf = 2) :
    ((ggK1ACo_orbitKindList p nf true m).map (ggK1ACo_kindOrbit nf)) =
      (ggMultDatumA p nf 2 true m).orbits := by
  rw [ggMultDatumA_orbits]
  simp only [ggK1ACo_orbitKindList, ggK1ACo_expectedKindList, hd, Bool.true_eq_false,
    if_true, if_false, List.filter_append, List.map_append]
  exact orbit_trivial_true nf p m

private lemma orbitList_true_ne_two (p nf : ℕ) (m : List ℕ) (hd : ggMultOrd p nf ≠ 2) :
    ((ggK1ACo_orbitKindList p nf true m).map (ggK1ACo_kindOrbit nf)) =
      (ggMultDatumA p nf (ggMultOrd p nf) true m).orbits := by
  rw [ggMultDatumA_orbits]
  simp only [ggK1ACo_orbitKindList, ggK1ACo_expectedKindList, hd, Bool.true_eq_false,
    if_true, if_false, List.filter_append, List.map_append]
  have hcond : ¬ (False ∧ ggMultOrd p nf = 1 ∨ True ∧ False) := by simp
  simp only [if_neg hcond, List.filter_append, List.map_append]
  exact congrArg₂ (· ++ ·) (orbit_head_true nf (m.headD 0))
    (orbit_tail nf m (List.range ((p - 1) / 2 + 1)))

private lemma orbitList_eq (p nf : ℕ) (tw : Bool) (m : List ℕ) :
    ((ggK1ACo_orbitKindList p nf tw m).map (ggK1ACo_kindOrbit nf)) =
      (ggMultDatumA p nf (ggMultOrd p nf) tw m).orbits := by
  cases tw
  · by_cases hd : ggMultOrd p nf = 1
    · rw [hd]
      exact orbitList_false_one p nf m hd
    · exact orbitList_false_ne_one p nf m hd
  · by_cases hd : ggMultOrd p nf = 2
    · rw [hd]
      exact orbitList_true_two p nf m hd
    · exact orbitList_true_ne_two p nf m hd



private lemma kindOrbit_sl_of_two (nf m e : ℕ) (hm : 2 ≤ m) :
    ggK1ACo_kindOrbit nf (.sl m e) = ggMultBlockA (m - 1) (e * nf) 1 := by
  unfold ggK1ACo_kindOrbit
  split
  · rename_i e' heq
    simp only [ggK1ACo_Kind.sl.injEq] at heq
    omega
  · simp_all
  · rename_i m' e' hne heq
    simp only [ggK1ACo_Kind.sl.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl
  · simp_all

private lemma kindOrbit_su_of_two (nf m e : ℕ) (hm : 2 ≤ m) :
    ggK1ACo_kindOrbit nf (.su m e) = ggMultBlockA (m - 1) (e * nf) 2 := by
  unfold ggK1ACo_kindOrbit
  split
  · simp_all
  · rename_i e' heq
    simp only [ggK1ACo_Kind.su.injEq] at heq
    omega
  · simp_all
  · rename_i m' e' hne heq
    simp only [ggK1ACo_Kind.su.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl

private lemma kindOrbit_sl_qs_of_two (nf m e : ℕ) (hm : 2 ≤ m) :
    (ggK1ACo_kindOrbit nf (.sl m e)).qs = decide (¬ (m = 2 ∧ e * nf = 1)) := by
  rw [kindOrbit_sl_of_two nf m e hm]
  simp only [ggMultBlockA, if_pos rfl, if_true, decide_eq_decide]
  constructor
  · rintro h ⟨h1, h2⟩; exact h ⟨by omega, h2⟩
  · rintro h ⟨h1, h2⟩; exact h ⟨by omega, h2⟩

private lemma kindOrbit_su_two_qs (nf e : ℕ) :
    (ggK1ACo_kindOrbit nf (.su 2 e)).qs = decide (e * nf ≠ 1) := by
  rw [kindOrbit_su_of_two nf 2 e (by norm_num)]
  simp only [ggMultBlockA, if_neg (by norm_num : ¬ (2 = 1)),
    if_neg (by norm_num : ¬ 2 ≤ 2 - 1), if_false, decide_eq_decide]

private lemma kindOrbit_su_three_qs (nf m e : ℕ) (hm : 3 ≤ m) :
    (ggK1ACo_kindOrbit nf (.su m e)).qs = decide (¬ (m = 3 ∧ e * nf = 1)) := by
  rw [kindOrbit_su_of_two nf m e (by omega)]
  simp only [ggMultBlockA, if_neg (by norm_num : ¬ (2 = 1)),
    if_pos (by omega : 2 ≤ m - 1), if_true, decide_eq_decide]
  constructor
  · rintro h ⟨h1, h2⟩; exact h ⟨by omega, h2⟩
  · rintro h ⟨h1, h2⟩; exact h ⟨by omega, h2⟩



private lemma subsingleton_statedSL_one (K : Type) [Field K] : Subsingleton ↥(StatedSL 1 K) := by
  haveI : Subsingleton (Fin 1) := inferInstance
  rw [StatedAPI.statedSL_eq_range_toGL]
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp a.2
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp b.2
  exact Subtype.ext (by rw [← hx, ← hy, Subsingleton.elim x y])

private lemma solvable_sl_two_card_two {E : Type} [Field E] [Finite E] (hE : Nat.card E = 2) :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) E) := by
  haveI : Fintype E := Fintype.ofFinite E
  have hq : Fintype.card E = 2 := by rw [← Nat.card_eq_fintype_card]; exact hE
  have h6 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) E) = 6 := by
    rw [Matrix.card_SL_field (n := 2) (𝔽 := E)]
    simp [hq]
  exact CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [h6]; norm_num)

private lemma solvable_su_two_four {E : Type} [Field E] [Finite E] (hE : Nat.card E = 4) :
    Group.IsSolvable ↥(StatedSU 2 2 E) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : Nat.card E = (2 ^ 1) ^ 2 := by norm_num; exact hE
  haveI : Fintype E := Fintype.ofFinite E
  have hE' : Fintype.card E = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hE]; norm_num
  haveI : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) hE'
  obtain ⟨e⟩ := CFSG.GH74.GLS.Stage4.Rest.FieldU3.sdwU_nonempty_sl2_mulEquiv_statedSU_two
    (F := E) (r := 2) (f := 1) h4
  have hk : Nat.card ↥(CFSG.LieType.Steinberg.fixedSubfield E 2 1) = 2 := by
    simpa using CFSG.LieType.Steinberg.card_fixedSubfield (F := E) (p := 2) (f := 1) h4
  have hsolv : Group.IsSolvable
      (Matrix.SpecialLinearGroup (Fin 2) ↥(CFSG.LieType.Steinberg.fixedSubfield E 2 1)) :=
    solvable_sl_two_card_two hk
  haveI := hsolv
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

private lemma solvable_su_three_four {E : Type} [Field E] [Finite E] (hE : Nat.card E = 4) :
    Group.IsSolvable ↥(StatedSU 3 2 E) :=
  CFSG.Quasithin.isSolvable_statedSU_one (F := E) hE


private theorem ggK1A_isQuasisimple_map {G R : Type} [Group G] [Group R] (π : G →* R)
    (hker : π.ker ≤ Subgroup.center G) {H : Subgroup G} (hH : CFSG.IsQuasisimple ↥H) :
    CFSG.IsQuasisimple ↥(H.map π) := by
  have hf : Function.Surjective (π.subgroupMap H) := π.subgroupMap_surjective H
  have hk : (π.subgroupMap H).ker ≤ Subgroup.center ↥H := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxπ : π (x : G) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      simpa using this
    exact Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hxπ)) (y : G)
  exact CFSG.LocalCores.isQuasisimple_of_surjective hH (π.subgroupMap H) hf hk

private theorem ggK1A_isSolvable_map {G R : Type} [Group G] [Group R] (π : G →* R)
    {H : Subgroup G} (hH : Group.IsSolvable ↥H) : Group.IsSolvable ↥(H.map π) := by
  haveI := hH
  exact Group.isSolvable_of_surjective (f := π.subgroupMap H) (π.subgroupMap_surjective H)

private theorem ggK1A_not_isSolvable_of_isQuasisimple {Q : Type} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) : ¬ Group.IsSolvable Q := by
  haveI : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  haveI : Group.IsPerfect Q := hQ.1
  exact Group.IsPerfect.not_isSolvable Q

private lemma hasOrbit_of_kindOrbit_qs_true {nf : ℕ} {k : ggK1ACo_Kind}
    (h : (ggK1ACo_kindOrbit nf k).qs = true) : ggK1ACo_Kind.hasOrbit k = true := by
  cases k with
  | sl m e =>
    by_cases hm : 2 ≤ m
    · have hne : m ≠ 1 := by omega
      simp [ggK1ACo_Kind.hasOrbit, hne]
    · have hmle : m ≤ 1 := by omega
      interval_cases m
      · simp [ggK1ACo_Kind.hasOrbit]
      · simp [ggK1ACo_kindOrbit] at h
  | su m e =>
    by_cases hm : 2 ≤ m
    · have hne : m ≠ 1 := by omega
      simp [ggK1ACo_Kind.hasOrbit, hne]
    · have hmle : m ≤ 1 := by omega
      interval_cases m
      · simp [ggK1ACo_Kind.hasOrbit]
      · simp [ggK1ACo_kindOrbit] at h

private lemma exists_equiv_of_multiset_map_eq {α β γ : Type*} [Fintype α] [Fintype β]
    {f : α → γ} {g : β → γ}
    (h : (Finset.univ.val.map f) = (Finset.univ.val.map g)) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a := by
  classical
  have hcount : ∀ c : γ, Fintype.card {a : α // f a = c} =
      Fintype.card {b : β // g b = c} := by
    intro c
    have h1 : Fintype.card {a : α // f a = c} = Multiset.count c (Finset.univ.val.map f) := by
      rw [Fintype.card_subtype, Multiset.count_map, ← Finset.filter_val]
      congr 1
      ext a
      simp [eq_comm]
    have h2 : Fintype.card {b : β // g b = c} = Multiset.count c (Finset.univ.val.map g) := by
      rw [Fintype.card_subtype, Multiset.count_map, ← Finset.filter_val]
      congr 1
      ext a
      simp [eq_comm]
    rw [h1, h2, h]
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hcount c)), ?_⟩
  exact fun a => Equiv.ofFiberEquiv_map _ a



private lemma fin_filter_map_eq {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun k : Fin l.length => p l[k])).val.map (fun k => l[k]) =
      (↑(l.filter p) : Multiset α) := by
  calc (Finset.univ.filter (fun k : Fin l.length => p l[k])).val.map (fun k => l[k])
      = (Multiset.map (fun k : Fin l.length => l[k]) Finset.univ.val).filter p := by
        rw [Finset.filter_val, Multiset.filter_map]
        simp only [Function.comp_apply]
    _ = (↑l : Multiset α).filter p := by
        rw [show (Finset.univ : Finset (Fin l.length)).val.map (fun k => l[k]) =
          (↑l : Multiset α) by simp]
    _ = (↑(l.filter p) : Multiset α) := by
        rw [Multiset.filter_coe]

private noncomputable def statedProjEquivLargeEvenProj (m : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL m K) ≃* Assembly.LargeEvenProj (Assembly.LargeEvenSLGroup (Fin m) K) := by
  rw [show StatedSL m K = Assembly.LargeEvenSLGroup (Fin m) K from
    CFSG.Open.StatedAPI.statedSL_eq_ker_det m K]

private noncomputable def slCenterQuotEquivLargeEvenProj (m : ℕ) (K : Type) [Field K] :
    (Matrix.SpecialLinearGroup (Fin m) K ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K)) ≃*
      Assembly.LargeEvenProj (Assembly.LargeEvenSLGroup (Fin m) K) :=
  (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m K).trans
    (statedProjEquivLargeEvenProj m K)

private noncomputable def suCenterQuotEquivLargeEvenProj (m q : ℕ) (K : Type) [Field K]
    (hZ : Subgroup.center ↥(StatedSU m q K) =
      (StatedScalars (Fin m) K).subgroupOf (StatedSU m q K)) :
    (↥(StatedSU m q K) ⧸ Subgroup.center ↥(StatedSU m q K)) ≃*
      Assembly.LargeEvenProj (Assembly.LargeEvenSUGroup (Fin m) K q) := by
  refine (QuotientGroup.quotientMulEquivOfEq hZ).trans ?_
  exact MulEquiv.refl _


private lemma solvable_sl_le_one (m : ℕ) (hm : m ≤ 1) (E : Type) [Field E] :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin m) E) := by
  interval_cases m <;> infer_instance

private lemma solvable_su_le_one (m q : ℕ) (hm : m ≤ 1) (E : Type) [Field E] :
    Group.IsSolvable ↥(StatedSU m q E) := by
  interval_cases m
  · haveI : Subsingleton (GL (Fin 0) E) := inferInstance
    haveI : Subsingleton ↥(StatedSU 0 q E) := inferInstance
    infer_instance
  · haveI : Subsingleton ↥(StatedSL 1 E) := subsingleton_statedSL_one E
    haveI : Subsingleton ↥(StatedSU 1 q E) :=
      (Subgroup.inclusion_injective (StatedAPI.statedSU_le_statedSL 1 q E)).subsingleton
    infer_instance
private lemma ggK1A_kindOrbit_qs_false_of_not_quasisimple {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    (h : ¬ CFSG.IsQuasisimple ↥(B.A i)) :
    (ggK1ACo_kindOrbit nf (B.kind i)).qs = false := by
  cases hq : (ggK1ACo_kindOrbit nf (B.kind i)).qs
  · rfl
  · exact absurd ((B.hqsKind i).mpr hq) h

private lemma ggK1A_solvable_sl_of_le_one {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    {m' e : ℕ} (hk : B.kind i = ggK1ACo_Kind.sl m' e) (hm : m' ≤ 1) :
    Group.IsSolvable ↥(B.A i) := by
  have hmodel := B.hmodel i
  rw [hk] at hmodel
  obtain ⟨E, hfield, _, _, ⟨eiso⟩⟩ := hmodel
  letI := hfield
  haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin m') E) :=
    solvable_sl_le_one m' hm E
  exact Group.isSolvable_of_surjective (f := eiso.symm.toMonoidHom) eiso.symm.surjective

private lemma ggK1A_solvable_sl_two_two {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    {e : ℕ} (hk : B.kind i = ggK1ACo_Kind.sl 2 e)
    (horb : (ggK1ACo_kindOrbit nf (.sl 2 e)).qs = false) :
    Group.IsSolvable ↥(B.A i) := by
  have hmodel := B.hmodel i
  rw [hk] at hmodel
  obtain ⟨E, hfield, hfinite, hcard, ⟨eiso⟩⟩ := hmodel
  letI := hfield
  letI := hfinite
  have hfe : e * nf = 1 := by
    by_contra hne
    rw [kindOrbit_sl_qs_of_two nf 2 e (by norm_num)] at horb
    simpa [hne] using horb
  have h2 : Nat.card E = 2 := by
    rw [Nat.card_eq_fintype_card, hcard, ← pow_mul]
    rw [Nat.mul_comm nf e, hfe, pow_one]
  haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) E) :=
    solvable_sl_two_card_two h2
  exact Group.isSolvable_of_surjective (f := eiso.symm.toMonoidHom) eiso.symm.surjective

private lemma ggK1A_solvable_sl_large {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) {m' e : ℕ}
    (horb : (ggK1ACo_kindOrbit nf (.sl m' e)).qs = false) (hm3 : 3 ≤ m') :
    False := by
  have hqsT : (ggK1ACo_kindOrbit nf (.sl m' e)).qs = true := by
    rw [kindOrbit_sl_qs_of_two nf m' e (by omega)]
    have hne : m' ≠ 2 := by omega
    simp [hne]
  rw [hqsT] at horb
  exact absurd horb (by decide)

private lemma ggK1A_solvable_of_sl {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    {m' e : ℕ} (hk : B.kind i = ggK1ACo_Kind.sl m' e)
    (h : ¬ CFSG.IsQuasisimple ↥(B.A i)) : Group.IsSolvable ↥(B.A i) := by
  have horb := ggK1A_kindOrbit_qs_false_of_not_quasisimple B i h
  rw [hk] at horb
  by_cases hm3 : 3 ≤ m'
  · exact absurd (ggK1A_solvable_sl_large B horb hm3) (by simp)
  · have hmle : m' ≤ 2 := by omega
    interval_cases m'
    · exact ggK1A_solvable_sl_of_le_one B i hk (by omega)
    · exact ggK1A_solvable_sl_of_le_one B i hk (by omega)
    · exact ggK1A_solvable_sl_two_two B i hk horb

private lemma ggK1A_solvable_su_of_le_one {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    {m' e : ℕ} (hk : B.kind i = ggK1ACo_Kind.su m' e) (hm : m' ≤ 1) :
    Group.IsSolvable ↥(B.A i) := by
  have hmodel := B.hmodel i
  rw [hk] at hmodel
  obtain ⟨E, hfield, _, _, ⟨eiso⟩⟩ := hmodel
  letI := hfield
  haveI : Group.IsSolvable ↥(StatedSU m' ((2 ^ nf) ^ e) E) :=
    solvable_su_le_one m' ((2 ^ nf) ^ e) hm E
  exact Group.isSolvable_of_surjective (f := eiso.symm.toMonoidHom) eiso.symm.surjective

private lemma ggK1A_solvable_su_two {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    {e : ℕ} (hk : B.kind i = ggK1ACo_Kind.su 2 e)
    (horb : (ggK1ACo_kindOrbit nf (.su 2 e)).qs = false) :
    Group.IsSolvable ↥(B.A i) := by
  have hmodel := B.hmodel i
  rw [hk] at hmodel
  obtain ⟨E, hfield, hfinite, hcard, ⟨eiso⟩⟩ := hmodel
  letI := hfield
  letI := hfinite
  have hfe : e * nf = 1 := by
    by_contra hne
    rw [kindOrbit_su_two_qs nf e] at horb
    simpa [hne] using horb
  have hfe' : nf * e = 1 := by rw [Nat.mul_comm]; exact hfe
  have h4 : Nat.card E = 4 := by
    rw [Nat.card_eq_fintype_card, hcard, ← pow_mul]
    rw [show nf * (2 * e) = 2 * (nf * e) by ring, hfe', mul_one, pow_two]
    norm_num
  haveI : Group.IsSolvable ↥(StatedSU 2 2 E) := solvable_su_two_four h4
  have hq : (2 ^ nf) ^ e = 2 := by
    rw [← pow_mul, Nat.mul_comm nf e, hfe, pow_one]
  rw [hq] at eiso
  exact Group.isSolvable_of_surjective (f := eiso.symm.toMonoidHom) eiso.symm.surjective

private lemma ggK1A_solvable_su_three {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    {e : ℕ} (hk : B.kind i = ggK1ACo_Kind.su 3 e)
    (horb : (ggK1ACo_kindOrbit nf (.su 3 e)).qs = false) :
    Group.IsSolvable ↥(B.A i) := by
  have hmodel := B.hmodel i
  rw [hk] at hmodel
  obtain ⟨E, hfield, hfinite, hcard, ⟨eiso⟩⟩ := hmodel
  letI := hfield
  letI := hfinite
  have hfe : e * nf = 1 := by
    by_contra hne
    rw [kindOrbit_su_three_qs nf 3 e (by norm_num)] at horb
    simpa [hne] using horb
  have hfe' : nf * e = 1 := by rw [Nat.mul_comm]; exact hfe
  have h4 : Nat.card E = 4 := by
    rw [Nat.card_eq_fintype_card, hcard, ← pow_mul]
    rw [show nf * (2 * e) = 2 * (nf * e) by ring, hfe', mul_one, pow_two]
    norm_num
  haveI : Group.IsSolvable ↥(StatedSU 3 2 E) := solvable_su_three_four h4
  have hq : (2 ^ nf) ^ e = 2 := by
    rw [← pow_mul, Nat.mul_comm nf e, hfe, pow_one]
  rw [hq] at eiso
  exact Group.isSolvable_of_surjective (f := eiso.symm.toMonoidHom) eiso.symm.surjective

private lemma ggK1A_solvable_su_large {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) {m' e : ℕ}
    (horb : (ggK1ACo_kindOrbit nf (.su m' e)).qs = false) (hm4 : 4 ≤ m') :
    False := by
  have hqsT : (ggK1ACo_kindOrbit nf (.su m' e)).qs = true := by
    rw [kindOrbit_su_three_qs nf m' e (by omega)]
    have hne : m' ≠ 3 := by omega
    simp [hne]
  rw [hqsT] at horb
  exact absurd horb (by decide)

private lemma ggK1A_solvable_of_su {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    {m' e : ℕ} (hk : B.kind i = ggK1ACo_Kind.su m' e)
    (h : ¬ CFSG.IsQuasisimple ↥(B.A i)) : Group.IsSolvable ↥(B.A i) := by
  have horb := ggK1A_kindOrbit_qs_false_of_not_quasisimple B i h
  rw [hk] at horb
  by_cases hm4 : 4 ≤ m'
  · exact absurd (ggK1A_solvable_su_large B horb hm4) (by simp)
  · have hmle : m' ≤ 3 := by omega
    interval_cases m'
    · exact ggK1A_solvable_su_of_le_one B i hk (by omega)
    · exact ggK1A_solvable_su_of_le_one B i hk (by omega)
    · exact ggK1A_solvable_su_two B i hk horb
    · exact ggK1A_solvable_su_three B i hk horb

private lemma ggK1A_solvable_of_not_quasisimple {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    (h : ¬ CFSG.IsQuasisimple ↥(B.A i)) : Group.IsSolvable ↥(B.A i) := by
  cases hk : B.kind i with
  | sl m' e => exact ggK1A_solvable_of_sl B i hk h
  | su m' e => exact ggK1A_solvable_of_su B i hk h

private def ggK1A_datum (p nf : ℕ) (tw : Bool) (m : List ℕ) : GGKacDatum :=
  ggMultDatumA p nf (ggMultOrd p nf) tw m

private noncomputable def ggK1A_image {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    {R : Type} [Group R] (π : G →* R)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) : B.ι → Subgroup R :=
  fun i => (B.A i).map π

private def ggK1A_blk {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) : B.ι → GGKacOrbit :=
  fun i => ggK1ACo_kindOrbit nf (B.kind i)

private theorem ggK1A_image_quasisimple_iff {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι) :
    CFSG.IsQuasisimple ↥(ggK1A_image π B i) ↔ CFSG.IsQuasisimple ↥(B.A i) := by
  constructor
  · intro hq
    by_contra hB
    have hsolv := ggK1A_isSolvable_map π (ggK1A_solvable_of_not_quasisimple B i hB)
    exact ggK1A_not_isSolvable_of_isQuasisimple hq hsolv
  · exact fun hB => ggK1A_isQuasisimple_map π hker hB

private theorem ggK1A_image_hqs {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι) :
    CFSG.IsQuasisimple ↥(ggK1A_image π B i) ↔ (ggK1A_blk B i).qs = true :=
  (ggK1A_image_quasisimple_iff π hker B i).trans (B.hqsKind i)

private theorem ggK1A_conj_induced {G R : Type} [Group G] [Group R] (π : G →* R) (xhat : G) :
    ∀ l : G, MulAut.conj (π xhat) (π l) = π (MulAut.conj xhat l) := by
  intro l
  simp [MulAut.conj_apply, map_mul]

private noncomputable def ggK1A_central_quotient_iso {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    (hBq : CFSG.IsQuasisimple ↥(B.A i)) :
    (ggK1A_image π B i ⧸ Subgroup.center ↥(ggK1A_image π B i)) ≃*
      (B.A i ⧸ Subgroup.center ↥(B.A i)) := by
  classical
  obtain ⟨-, hne⟩ := TCJ.ggTCJ_descent π hπ hker (MulAut.conj xhat)
    (MulAut.conj (π xhat)) (ggK1A_conj_induced π xhat) (B.A i) (B.hfactor i hBq)
  exact (Classical.choice hne).symm

private theorem ggK1A_image_hcomm {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (B : ggK1ACo_Blocks p nf tw K N G xhat m) :
    ∀ i j : B.ι, i ≠ j → ∀ a ∈ ggK1A_image π B i, ∀ b ∈ ggK1A_image π B j, Commute a b := by
  intro i j hij a ha b hb
  simp only [ggK1A_image, Subgroup.mem_map] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  exact (B.hcomm i j hij a' ha' b' hb').map π

private theorem ggK1A_image_htame {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι) :
    CFSG.IsQuasisimple ↥(ggK1A_image π B i) ∨ Group.IsSolvable ↥(ggK1A_image π B i) := by
  by_cases hB : CFSG.IsQuasisimple ↥(B.A i)
  · exact Or.inl (ggK1A_isQuasisimple_map π hker hB)
  · exact Or.inr (ggK1A_isSolvable_map π (ggK1A_solvable_of_not_quasisimple B i hB))

private lemma ggK1A_kind_mem_expected {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι) :
    B.kind i ∈ ggK1ACo_expectedKindList p nf tw m := by
  have h := Multiset.mem_map_of_mem B.kind (@Finset.mem_univ B.ι B.fintype i)
  have h' : B.kind i ∈ ggK1ACo_expectedKinds p nf tw m := by
    rw [← B.kind_multiset]
    exact h
  simpa only [ggK1ACo_expectedKinds, Multiset.mem_coe] using h'

private lemma ggK1A_blk_mem_orbits {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    (hqs : (ggK1A_blk B i).qs = true) :
    ggK1A_blk B i ∈ (ggK1A_datum p nf tw m).orbits := by
  have hmemKind : B.kind i ∈ ggK1ACo_orbitKindList p nf tw m := by
    rw [ggK1ACo_orbitKindList, List.mem_filter]
    exact ⟨ggK1A_kind_mem_expected B i, hasOrbit_of_kindOrbit_qs_true hqs⟩
  have hmemMap : ggK1A_blk B i ∈
      (ggK1ACo_orbitKindList p nf tw m).map (ggK1ACo_kindOrbit nf) := by
    simpa [ggK1A_blk] using List.mem_map_of_mem hmemKind
  rwa [orbitList_eq p nf tw m] at hmemMap

private lemma ggK1A_image_hmem {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    (hi : CFSG.IsQuasisimple ↥(ggK1A_image π B i)) :
    ggK1A_blk B i ∈ (ggK1A_datum p nf tw m).orbits :=
  ggK1A_blk_mem_orbits B i ((ggK1A_image_hqs π hker B i).mp hi)

private lemma ggK1A_sl_two_le {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    {m' e : ℕ} (hk : B.kind i = ggK1ACo_Kind.sl m' e)
    (hBq : CFSG.IsQuasisimple ↥(B.A i)) : 2 ≤ m' := by
  have hmodel := B.hmodel i
  rw [hk] at hmodel
  obtain ⟨E, hfield, _, _, ⟨eiso⟩⟩ := hmodel
  letI := hfield
  by_contra h
  have hmle : m' ≤ 1 := by omega
  haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin m') E) :=
    solvable_sl_le_one m' hmle E
  have hsolvB : Group.IsSolvable ↥(B.A i) :=
    Group.isSolvable_of_surjective (f := eiso.symm.toMonoidHom) eiso.symm.surjective
  exact ggK1A_not_isSolvable_of_isQuasisimple hBq hsolvB

private lemma ggK1A_su_two_le {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    {m' e : ℕ} (hk : B.kind i = ggK1ACo_Kind.su m' e)
    (hBq : CFSG.IsQuasisimple ↥(B.A i)) : 2 ≤ m' := by
  have hmodel := B.hmodel i
  rw [hk] at hmodel
  obtain ⟨E, hfield, _, _, ⟨eiso⟩⟩ := hmodel
  letI := hfield
  by_contra h
  have hmle : m' ≤ 1 := by omega
  haveI : Group.IsSolvable ↥(StatedSU m' ((2 ^ nf) ^ e) E) :=
    solvable_su_le_one m' ((2 ^ nf) ^ e) hmle E
  have hsolvB : Group.IsSolvable ↥(B.A i) :=
    Group.isSolvable_of_surjective (f := eiso.symm.toMonoidHom) eiso.symm.surjective
  exact ggK1A_not_isSolvable_of_isQuasisimple hBq hsolvB

private lemma ggK1A_label_sl {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    (hBq : CFSG.IsQuasisimple ↥(B.A i))
    {m' e : ℕ} (hk : B.kind i = ggK1ACo_Kind.sl m' e) (h2m : 2 ≤ m') :
    GGHasLabel (ggK1A_blk B i).lab
      (ggK1A_image π B i ⧸ Subgroup.center ↥(ggK1A_image π B i)) := by
  have hcompIso := ggK1A_central_quotient_iso π hπ hker B i hBq
  have hmodel := B.hmodel i
  rw [hk] at hmodel
  obtain ⟨E, hfield, hfinite, hcard, ⟨eiso⟩⟩ := hmodel
  letI := hfield
  haveI : Finite E := Finite.of_fintype E
  have hcardNat : Nat.card E = 2 ^ (e * nf) := by
    rw [Nat.card_eq_fintype_card, hcard, ← pow_mul, Nat.mul_comm nf e]
  have hblk : ggK1A_blk B i = ggMultBlockA (m' - 1) (e * nf) 1 := by
    simp only [ggK1A_blk]
    rw [hk]
    exact kindOrbit_sl_of_two nf m' e h2m
  have hlabEq : (ggK1A_blk B i).lab = ⟨.A, m' - 1, e * nf⟩ := by
    rw [hblk]
    rfl
  rw [hlabEq]
  simp only [GGHasLabel, Assembly.LargeEvenRawDatum, Assembly.LargeEvenRecipeLinear]
  refine ⟨E, hfield, Finite.of_fintype E, hcardNat, ?_⟩
  rw [show m' - 1 + 1 = m' by omega]
  exact ⟨(hcompIso.trans (QuotientGroup.congr _ _ eiso (Subgroup.map_center_eq eiso))).trans
    (slCenterQuotEquivLargeEvenProj m' E)⟩

private lemma ggK1A_su_two_hfe {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    {e : ℕ} (hk : B.kind i = ggK1ACo_Kind.su 2 e)
    (hqsT : (ggK1A_blk B i).qs = true) : e * nf ≠ 1 := by
  intro h1
  have hqsF : (ggK1ACo_kindOrbit nf (.su 2 e)).qs = false := by
    rw [kindOrbit_su_two_qs nf e]
    simp [h1]
  have hqsT' : (ggK1ACo_kindOrbit nf (.su 2 e)).qs = true := by
    simpa only [ggK1A_blk, hk] using hqsT
  rw [hqsF] at hqsT'
  exact absurd hqsT' (by decide)

private lemma ggK1A_label_su_two {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    (hBq : CFSG.IsQuasisimple ↥(B.A i))
    {e : ℕ} (hk : B.kind i = ggK1ACo_Kind.su 2 e)
    (hqsT : (ggK1A_blk B i).qs = true) :
    GGHasLabel (ggK1A_blk B i).lab
      (ggK1A_image π B i ⧸ Subgroup.center ↥(ggK1A_image π B i)) := by
  have hcompIso := ggK1A_central_quotient_iso π hπ hker B i hBq
  have hmodel := B.hmodel i
  rw [hk] at hmodel
  obtain ⟨E, hfield, hfinite, hcard, ⟨eiso⟩⟩ := hmodel
  letI := hfield
  haveI : Finite E := Finite.of_fintype E
  have hq : (2 ^ nf) ^ e = 2 ^ (e * nf) := by
    rw [← pow_mul, Nat.mul_comm nf e]
  have hcardNat : Nat.card E = (2 ^ (e * nf)) ^ 2 := by
    rw [Nat.card_eq_fintype_card, hcard, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hfe : e * nf ≠ 1 := ggK1A_su_two_hfe B i hk hqsT
  have hblk : ggK1A_blk B i = ggMultBlockA 1 (e * nf) 2 := by
    simp only [ggK1A_blk]
    rw [hk]
    exact kindOrbit_su_of_two nf 2 e (by norm_num)
  have hlabEq : (ggK1A_blk B i).lab = ⟨.A, 1, e * nf⟩ := by
    rw [hblk]
    simp [ggMultBlockA]
  rw [hlabEq]
  simp only [GGHasLabel, Assembly.LargeEvenRawDatum, Assembly.LargeEvenRecipeLinear]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card E = (2 ^ (e * nf)) ^ 2 := hcardNat
  rw [hq] at eiso
  have hEfin : Fintype.card E = 2 ^ (2 * (e * nf)) := by
    rw [← Nat.card_eq_fintype_card, hcardNat, ← pow_mul]
    congr 1
    ring
  haveI : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * (e * nf)) hEfin
  obtain ⟨e2⟩ := CFSG.GH74.GLS.Stage4.Rest.FieldU3.sdwU_nonempty_sl2_mulEquiv_statedSU_two
    (F := E) (r := 2) (f := e * nf) hcardF
  have hcardFix : Nat.card ↥(CFSG.LieType.Steinberg.fixedSubfield E 2 (e * nf)) =
      2 ^ (e * nf) :=
    CFSG.LieType.Steinberg.card_fixedSubfield (F := E) (p := 2) (f := e * nf) hcardF
  refine ⟨↥(CFSG.LieType.Steinberg.fixedSubfield E 2 (e * nf)), inferInstance, inferInstance,
    hcardFix, ?_⟩
  refine ⟨(hcompIso.trans (QuotientGroup.congr _ _ (eiso.trans e2.symm)
    (Subgroup.map_center_eq _))).trans (slCenterQuotEquivLargeEvenProj 2 _)⟩

private lemma ggK1A_su_large_pair {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    {m' e : ℕ} (hk : B.kind i = ggK1ACo_Kind.su m' e)
    (hqsT : (ggK1A_blk B i).qs = true) : (m', 2 ^ (e * nf)) ≠ (3, 2) := by
  intro h
  have hm : m' = 3 := congrArg Prod.fst h
  have hpow : 2 ^ (e * nf) = 2 := congrArg Prod.snd h
  rw [hm] at hk
  have hfe : e * nf = 1 := by
    have h2 : 2 ^ (e * nf) = 2 ^ 1 := by simpa using hpow
    have := Nat.pow_right_injective (le_refl 2) h2
    simpa using this
  have hqsF : (ggK1ACo_kindOrbit nf (.su 3 e)).qs = false := by
    rw [kindOrbit_su_three_qs nf 3 e (by norm_num)]
    simp [hfe]
  have hqsT' : (ggK1ACo_kindOrbit nf (.su 3 e)).qs = true := by
    simpa only [ggK1A_blk, hk] using hqsT
  rw [hqsF] at hqsT'
  exact absurd hqsT' (by decide)

private lemma ggK1A_label_su_large {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    (hBq : CFSG.IsQuasisimple ↥(B.A i))
    {m' e : ℕ} (hk : B.kind i = ggK1ACo_Kind.su m' e) (h2m : 2 ≤ m') (hm3 : 3 ≤ m')
    (hpair : (m', 2 ^ (e * nf)) ≠ (3, 2)) :
    GGHasLabel (ggK1A_blk B i).lab
      (ggK1A_image π B i ⧸ Subgroup.center ↥(ggK1A_image π B i)) := by
  have hcompIso := ggK1A_central_quotient_iso π hπ hker B i hBq
  have hmodel := B.hmodel i
  rw [hk] at hmodel
  obtain ⟨E, hfield, hfinite, hcard, ⟨eiso⟩⟩ := hmodel
  letI := hfield
  haveI : Finite E := Finite.of_fintype E
  have hcardNat : Nat.card E = (2 ^ (e * nf)) ^ 2 := by
    rw [Nat.card_eq_fintype_card, hcard, ← pow_mul, ← pow_mul]
    congr 1
    ring
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := e * nf) (F := E) hcardNat hm3 hpair).2
  have hblk : ggK1A_blk B i = ggMultBlockA (m' - 1) (e * nf) 2 := by
    simp only [ggK1A_blk]
    rw [hk]
    exact kindOrbit_su_of_two nf m' e h2m
  have hlabEq : (ggK1A_blk B i).lab = ⟨.twA, m' - 1, e * nf⟩ := by
    rw [hblk]
    simp only [ggMultBlockA, if_neg (by norm_num : ¬ (2 = 1)),
      if_pos (by omega : 2 ≤ m' - 1)]
  rw [hlabEq]
  simp only [GGHasLabel, Assembly.LargeEvenRawDatum, Assembly.LargeEvenRecipeUnitary]
  have hq : (2 ^ nf) ^ e = 2 ^ (e * nf) := by
    rw [← pow_mul, Nat.mul_comm nf e]
  rw [hq] at eiso
  refine ⟨E, hfield, Finite.of_fintype E, hcardNat, ?_⟩
  rw [show m' - 1 + 1 = m' by omega]
  exact ⟨(hcompIso.trans (QuotientGroup.congr _ _ eiso (Subgroup.map_center_eq eiso))).trans
    (suCenterQuotEquivLargeEvenProj m' (2 ^ (e * nf)) E hZ)⟩

private lemma ggK1A_label_su {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    (hBq : CFSG.IsQuasisimple ↥(B.A i))
    {m' e : ℕ} (hk : B.kind i = ggK1ACo_Kind.su m' e)
    (hqsT : (ggK1A_blk B i).qs = true) :
    GGHasLabel (ggK1A_blk B i).lab
      (ggK1A_image π B i ⧸ Subgroup.center ↥(ggK1A_image π B i)) := by
  have h2m : 2 ≤ m' := ggK1A_su_two_le B i hk hBq
  by_cases hm2 : m' = 2
  · subst hm2
    exact ggK1A_label_su_two π hπ hker B i hBq hk hqsT
  · have hm3 : 3 ≤ m' := by omega
    exact ggK1A_label_su_large π hπ hker B i hBq hk h2m hm3
      (ggK1A_su_large_pair B i hk hqsT)

private lemma ggK1A_image_hlab {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    (hi : CFSG.IsQuasisimple ↥(ggK1A_image π B i)) :
    GGHasLabel (ggK1A_blk B i).lab
      (ggK1A_image π B i ⧸ Subgroup.center ↥(ggK1A_image π B i)) := by
  have hqsT : (ggK1A_blk B i).qs = true := (ggK1A_image_hqs π hker B i).mp hi
  have hBq : CFSG.IsQuasisimple ↥(B.A i) := (B.hqsKind i).mpr hqsT
  cases hk : B.kind i with
  | sl m' e => exact ggK1A_label_sl π hπ hker B i hBq hk (ggK1A_sl_two_le B i hk hBq)
  | su m' e => exact ggK1A_label_su π hπ hker B i hBq hk hqsT

private lemma ggK1A_image_hreal {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (o : GGKacOrbit)
    (ho : o ∈ (ggK1A_datum p nf tw m).orbits) (hqo : o.qs = true) :
    ∃ i : B.ι, CFSG.IsQuasisimple ↥(ggK1A_image π B i) ∧ ggK1A_blk B i = o := by
  simp only [ggK1A_datum] at ho
  have hmemMap : o ∈ (ggK1ACo_orbitKindList p nf tw m).map (ggK1ACo_kindOrbit nf) := by
    rwa [← orbitList_eq] at ho
  obtain ⟨k, hkList, hko⟩ := List.mem_map.mp hmemMap
  have hkExp : k ∈ ggK1ACo_expectedKinds p nf tw m := by
    rw [ggK1ACo_expectedKinds]
    exact (List.mem_filter.mp hkList).1
  have hkMap : k ∈ (@Finset.univ B.ι B.fintype).val.map B.kind := by
    rw [B.kind_multiset]
    exact hkExp
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hkMap
  refine ⟨i, ?_, ?_⟩
  · apply (ggK1A_image_hqs π hker B i).mpr
    show (ggK1ACo_kindOrbit nf (B.kind i)).qs = true
    rw [hi, hko]
    exact hqo
  · show ggK1ACo_kindOrbit nf (B.kind i) = o
    rw [hi, hko]

private lemma ggK1A_filter_expected_eq (p nf : ℕ) (tw : Bool) (m : List ℕ) :
    (ggK1ACo_expectedKindList p nf tw m).filter
        (fun k => decide ((ggK1ACo_kindOrbit nf k).qs = true)) =
      (ggK1ACo_orbitKindList p nf tw m).filter
        (fun k => decide ((ggK1ACo_kindOrbit nf k).qs = true)) := by
  rw [ggK1ACo_orbitKindList, List.filter_filter]
  apply List.filter_congr
  intro k hk
  by_cases hq : (ggK1ACo_kindOrbit nf k).qs = true
  · have hh : ggK1ACo_Kind.hasOrbit k = true := hasOrbit_of_kindOrbit_qs_true hq
    simp [hq, hh]
  · have hq' : (ggK1ACo_kindOrbit nf k).qs = false := by
      cases h : (ggK1ACo_kindOrbit nf k).qs <;> simp_all
    simp [hq']

private lemma ggK1A_filter_expected_multiset (p nf : ℕ) (tw : Bool) (m : List ℕ) :
    Multiset.filter (fun k => (ggK1ACo_kindOrbit nf k).qs = true)
        (↑(ggK1ACo_expectedKindList p nf tw m) : Multiset ggK1ACo_Kind) =
      Multiset.filter (fun k => (ggK1ACo_kindOrbit nf k).qs = true)
        (↑(ggK1ACo_orbitKindList p nf tw m) : Multiset ggK1ACo_Kind) := by
  rw [Multiset.filter_coe, Multiset.filter_coe, ggK1A_filter_expected_eq]

private lemma ggK1A_blk_multiset_filter {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {tw : Bool} {xhat : G} {m : List ℕ}
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) :
    ((@Finset.univ B.ι B.fintype).filter (fun i => (ggK1A_blk B i).qs = true)).val.map
        (ggK1A_blk B) =
      (↑(((ggK1A_datum p nf tw m).orbits).filter (fun o => o.qs = true)) :
        Multiset GGKacOrbit) := by
  have hmap : Multiset.map (fun i => ggK1ACo_kindOrbit nf (B.kind i))
      (@Finset.univ B.ι B.fintype).val =
      Multiset.map (fun k => ggK1ACo_kindOrbit nf k)
        (↑(ggK1ACo_expectedKindList p nf tw m) : Multiset ggK1ACo_Kind) := by
    rw [show (fun i => ggK1ACo_kindOrbit nf (B.kind i)) =
      (ggK1ACo_kindOrbit nf) ∘ B.kind from rfl]
    rw [← Multiset.map_map]
    exact congrArg (Multiset.map (ggK1ACo_kindOrbit nf)) B.kind_multiset
  calc ((@Finset.univ B.ι B.fintype).filter (fun i => (ggK1A_blk B i).qs = true)).val.map
        (ggK1A_blk B)
      = Multiset.filter (fun o => o.qs = true)
          (Multiset.map (fun i => ggK1ACo_kindOrbit nf (B.kind i))
            (@Finset.univ B.ι B.fintype).val) := by
        rw [Finset.filter_val]
        rw [show Multiset.filter (fun i => (ggK1A_blk B i).qs = true)
            (@Finset.univ B.ι B.fintype).val =
          Multiset.filter ((fun o => o.qs = true) ∘ ggK1A_blk B)
            (@Finset.univ B.ι B.fintype).val from rfl]
        rw [← Multiset.filter_map]
        rfl
    _ = Multiset.filter (fun o => o.qs = true)
          (Multiset.map (fun k => ggK1ACo_kindOrbit nf k)
            (↑(ggK1ACo_expectedKindList p nf tw m) : Multiset ggK1ACo_Kind)) := by
        rw [hmap]
    _ = Multiset.map (fun k => ggK1ACo_kindOrbit nf k)
          (Multiset.filter (fun k => (ggK1ACo_kindOrbit nf k).qs = true)
            (↑(ggK1ACo_expectedKindList p nf tw m) : Multiset ggK1ACo_Kind)) := by
        rw [Multiset.filter_map]
        simp only [Function.comp_apply]
    _ = Multiset.map (fun k => ggK1ACo_kindOrbit nf k)
          (Multiset.filter (fun k => (ggK1ACo_kindOrbit nf k).qs = true)
            (↑(ggK1ACo_orbitKindList p nf tw m) : Multiset ggK1ACo_Kind)) := by
        rw [ggK1A_filter_expected_multiset]
    _ = Multiset.filter (fun o => o.qs = true)
          (Multiset.map (fun k => ggK1ACo_kindOrbit nf k)
            (↑(ggK1ACo_orbitKindList p nf tw m) : Multiset ggK1ACo_Kind)) := by
        rw [show Multiset.filter (fun k => (ggK1ACo_kindOrbit nf k).qs = true)
            (↑(ggK1ACo_orbitKindList p nf tw m) : Multiset ggK1ACo_Kind) =
            Multiset.filter ((fun o => o.qs = true) ∘ (fun k => ggK1ACo_kindOrbit nf k))
              (↑(ggK1ACo_orbitKindList p nf tw m) : Multiset ggK1ACo_Kind) from rfl]
        rw [← Multiset.filter_map]
    _ = Multiset.filter (fun o => o.qs = true) (↑(ggK1A_datum p nf tw m).orbits :
          Multiset GGKacOrbit) := by
        rw [show Multiset.map (fun k => ggK1ACo_kindOrbit nf k)
            (↑(ggK1ACo_orbitKindList p nf tw m) : Multiset ggK1ACo_Kind) =
            (↑(ggK1A_datum p nf tw m).orbits : Multiset GGKacOrbit) by
          rw [Multiset.map_coe, ggK1A_datum, orbitList_eq p nf tw m]]
    _ = (↑(((ggK1A_datum p nf tw m).orbits).filter (fun o => o.qs = true)) :
        Multiset GGKacOrbit) := by
        rw [Multiset.filter_coe]

private lemma ggK1A_image_hbij {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) :
    ∃ g : {i : B.ι // CFSG.IsQuasisimple ↥(ggK1A_image π B i)} ≃
        {k : Fin (ggK1A_datum p nf tw m).orbits.length //
          (ggK1A_datum p nf tw m).orbits[k].qs = true},
      ∀ i, (ggK1A_datum p nf tw m).orbits[(g i).1] = ggK1A_blk B i.1 := by
  classical
  letI : Fintype B.ι := B.fintype
  let D : GGKacDatum := ggK1A_datum p nf tw m
  let P : B.ι → Prop := fun i => CFSG.IsQuasisimple ↥(ggK1A_image π B i)
  let Q : Fin D.orbits.length → Prop := fun k => D.orbits[k].qs = true
  have hP : (Finset.univ.filter P) =
      (Finset.univ.filter (fun i => (ggK1A_blk B i).qs = true)) := by
    apply Finset.filter_congr
    intro i _
    exact ggK1A_image_hqs π hker B i
  have hmain : (Finset.univ.filter (fun i => (ggK1A_blk B i).qs = true)).val.map
        (ggK1A_blk B) =
      (↑(D.orbits.filter (fun o => o.qs = true)) : Multiset GGKacOrbit) := by
    simpa only [D] using ggK1A_blk_multiset_filter (p := p) (nf := nf) (tw := tw) B
  have hRHS : (Finset.univ.filter Q).val.map (fun k => D.orbits[k]) =
      (↑(D.orbits.filter (fun o => o.qs = true)) : Multiset GGKacOrbit) :=
    fin_filter_map_eq D.orbits (fun o => o.qs = true)
  have hmultEq : (Finset.univ.val.map (fun i : {i // P i} => ggK1A_blk B i.1)) =
      (Finset.univ.val.map (fun k : {k // Q k} => D.orbits[k.1])) := by
    rw [show (fun i : {i // P i} => ggK1A_blk B i.1) =
        Subtype.restrict P (ggK1A_blk B) from rfl,
      Finset.univ_val_map_subtype_restrict]
    rw [show (fun k : {k // Q k} => D.orbits[k.1]) =
        Subtype.restrict Q (fun k : Fin D.orbits.length => D.orbits[k]) from rfl,
      Finset.univ_val_map_subtype_restrict]
    rw [hP, hmain, hRHS]
  obtain ⟨e, he⟩ := exists_equiv_of_multiset_map_eq hmultEq
  exact ⟨e, he⟩

private lemma ggK1A_image_hcomp {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (J : Subgroup R)
    (hJ : CFSG.Assembly.IsComponentOf J (ggFixSub (MulAut.conj (π xhat)))) :
    ∃ i : B.ι, CFSG.IsQuasisimple ↥(ggK1A_image π B i) ∧ J = ggK1A_image π B i := by
  obtain ⟨hQcomp, hQmap⟩ := ggK1A_isComponentOf_comap_commutator π hπ hker
    (MulAut.conj xhat) (MulAut.conj (π xhat)) (ggK1A_conj_induced π xhat) (K := J) hJ
  obtain ⟨i, hiA⟩ := B.hcomp ⁅J.comap π, J.comap π⁆ hQcomp
  have hBq : CFSG.IsQuasisimple ↥(B.A i) := by
    rw [← hiA] at hQcomp
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
      ↥(B.A i)).mp hQcomp.2.2
  refine ⟨i, (ggK1A_image_quasisimple_iff π hker B i).mpr hBq, ?_⟩
  rw [← hQmap, ← hiA]
  rfl

private lemma ggK1A_image_hfactor {p nf N : ℕ} {K : Type} [Field K]
    {G : Type} [Group G] {R : Type} [Group R] {tw : Bool} {xhat : G} {m : List ℕ}
    (π : G →* R) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) (i : B.ι)
    (hi : CFSG.IsQuasisimple ↥(ggK1A_image π B i)) :
    CFSG.Assembly.IsComponentOf (ggK1A_image π B i) (ggFixSub (MulAut.conj (π xhat))) := by
  have hqsT : (ggK1A_blk B i).qs = true := (ggK1A_image_hqs π hker B i).mp hi
  have hBq : CFSG.IsQuasisimple ↥(B.A i) := (B.hqsKind i).mpr hqsT
  have hcomp := (TCJ.ggTCJ_descent π hπ hker (MulAut.conj xhat)
    (MulAut.conj (π xhat)) (ggK1A_conj_induced π xhat) (B.A i) (B.hfactor i hBq)).1
  simpa [ggK1A_image, ggK1A_fixSub_conj_eq_centralizer] using hcomp

theorem ggK1A_transport {p nf N : ℕ} {K : Type} [Field K] {G : Type} [Group G] [Finite G]
    {R : Type} [Group R] (π : G →* R) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G)
    {tw : Bool} {xhat : G} {m : List ℕ}
    (hnoglue : Subgroup.centralizer ({π xhat} : Set R) =
      (Subgroup.centralizer ({xhat} : Set G)).map π)
    (B : ggK1ACo_Blocks p nf tw K N G xhat m) :
    Nonempty (ggK1ACo_Family p R (π xhat) (ggMultDatumA p nf (ggMultOrd p nf) tw m)) := by
  classical
  letI : Fintype B.ι := B.fintype
  haveI : Finite B.ι := Finite.of_fintype B.ι
  change Nonempty (ggK1ACo_Family p R (π xhat) (ggK1A_datum p nf tw m))
  refine ⟨B.ι, ggK1A_image π B, ggK1A_blk B, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ggK1A_image_hcomm π B
  · exact ggK1A_image_htame π hker B
  · exact ggK1A_image_hmem π hker B
  · intro i hi
    exact (ggK1A_image_hqs π hker B i).mp hi
  · exact ggK1A_image_hlab π hπ hker B
  · exact ggK1A_image_hreal π hker B
  · exact ggK1A_image_hbij π hker B
  · exact ggK1A_image_hcomp π hπ hker B
  · exact ggK1A_image_hfactor π hπ hker B



theorem ggK1ACo_component_inj {p : ℕ} {R : Type} [Group R] {x : R} {D : GGKacDatum}
    (F : ggK1ACo_Family p R x D) {i j : F.ι}
    (hi : CFSG.IsQuasisimple ↥(F.A i)) (hj : CFSG.IsQuasisimple ↥(F.A j))
    (h : F.A i = F.A j) : i = j := by
  by_contra hij
  have hcomm : ∀ a b : ↥(F.A i), a * b = b * a := by
    intro a b
    exact Subtype.ext (F.hcomm i j hij a.1 a.2 b.1 (h ▸ b.2))
  obtain ⟨-, -, a, b, hab⟩ := hi
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by simpa using congrArg (QuotientGroup.mk' (Subgroup.center ↥(F.A i))) (hcomm a' b'))


end CFSG.StandardType

end
