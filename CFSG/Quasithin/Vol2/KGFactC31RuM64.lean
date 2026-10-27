module

public import Certificates.Certificate7234
public import CFSG.Quasithin.Vol2.KGFactC31RuImg
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Quasithin.Recognition.CertU33Pres
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuBigZBase
public import CFSG.Quasithin.Vol2.KGFactC31RuRefKBase
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public import Certificates.Certificate7233Base

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31 CFSG.CosetTable

@[expose] noncomputable def m64G : List (Equiv.Perm (Fin 4060)) := wsG strongM64W

@[expose] noncomputable def M64 : Subgroup (Equiv.Perm (Fin 4060)) :=
  Subgroup.closure {g | g ∈ m64G}

noncomputable abbrev u33G : Fin 5 → Equiv.Perm (Fin 4060) := vOf u33W 5

noncomputable abbrev t64 : Equiv.Perm (Fin 4060) := wG t64W

theorem m64S_size : m64S.size = 5 := by simp [m64S, strongM64W]

theorem m64G_length : m64G.length = 5 := by simp [m64G, wsG, strongM64W]

theorem m64S_mem {i : ℕ} (hi : i < 5) : m64S[i]! ∈ m64S.toList := by
  rw [getElem!_pos m64S i (by rw [m64S_size]; exact hi)]
  exact Array.getElem_mem_toList _

theorem m64G_mem : ∀ g ∈ m64G, g ∈ ruP := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact wG_mem w

theorem M64_le_ruP : M64 ≤ ruP := by
  rw [M64, Subgroup.closure_le]
  exact m64G_mem

theorem rep_getD_of_forall₂ {S : Array (Array ℕ)} {gens : List (Equiv.Perm (Fin 4060))}
    (h : List.Forall₂ (Rep 4060) S.toList gens) :
    ∀ i < gens.length, Rep 4060 S[i]! (gens.getD i 1) := by
  intro i hi
  have hl : S.toList.length = gens.length := h.length_eq
  have hiS : i < S.size := by rw [← Array.length_toList, hl]; exact hi
  rw [getElem!_pos S i hiS, List.getD_eq_getElem _ _ hi]
  have := (List.forall₂_iff_get.mp h).2 i (by rw [Array.length_toList]; exact hiS) hi
  simpa using this

section Reps

theorem forall₂_m64S : List.Forall₂ (Rep 4060) m64S.toList m64G := by
  rw [show m64S.toList = wsA strongM64W by simp [m64S, wsA], m64G]
  exact forall₂_wsA (List.all_eq_true.mp (by decide : strongM64W.all (lettersOK 6) = true))

theorem rep_m64S {j : ℕ} (hj : j < 5) : Rep 4060 m64S[j]! (m64G.getD j 1) :=
  rep_getD_of_forall₂ forall₂_m64S j (by rw [m64G_length]; exact hj)

theorem rep_m64SI {j : ℕ} (hj : j < 5) : Rep 4060 (m64S.map ruInv)[j]! (m64G.getD j 1)⁻¹ := by
  rw [map_getElem! _ _ (by rw [m64S_size]; exact hj)]
  exact rep_ruInv' (rep_m64S hj)

theorem forall₂_u33A : List.Forall₂ (Rep 4060) u33A.toList (List.ofFn u33G) := by
  rw [show u33A.toList = wsA u33W by simp [u33A, wsA]]
  exact forall₂_vOf rfl (List.all_eq_true.mp (by decide : u33W.all (lettersOK 6) = true))

theorem rep_u33A (i : Fin 5) : Rep 4060 u33A[i.val]! (u33G i) := by
  have h := rep_getD_of_forall₂ forall₂_u33A i.val (by simp)
  rwa [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn] at h

theorem rep_wM {w : List ℤ} (hw : lettersOK 5 w = true) : Rep 4060 (wM w) (evalSigned m64G w) :=
  rep_wordA_evalSigned (fun _ hh => rep_m64S hh) (fun _ hh => rep_m64SI hh) w hw

theorem rep_t64 : Rep 4060 t64A t64 := rep_wA (by decide)

end Reps

theorem evalSigned_m64G_mem (w : List ℤ) : evalSigned m64G w ∈ M64 :=
  evalSigned_mem (fun _ hg => Subgroup.subset_closure hg) w

section Chain

theorem m64Parts :
    rawChainOK 4060 (arrO m64S 5) m64S (arrBase m64B) noDer5 4 = true ∧
    ((rawOrbitSizes 4060 m64S (arrBase m64B)).prod == 387072) = true ∧
    (m64S.toList.all fun s => normsA s (ruInv s) b64A sp64) = true ∧
    b64A.all m64Sift = true ∧ u33A.toList.all m64Sift = true ∧
    (u33PresRels.all fun r => inA sp64 (relA r)) = true ∧
    ((List.range 5).all fun j =>
      eqA 4060 (wordA 4060 uGens (uGens.map ruInv) (strongInU33W.getD j [])) m64S[j]!) = true ∧
    (sp64.all fun v => eqA 4060 v (idA 4060) ||
      conjT64W.any fun w => eqA 4060 (cjA (wM w) (ruInv (wM w)) t64A) v) = true := by
  have h := Certificates.certificate7234
  simp only [m64Checks, Bool.and_eq_true, and_assoc] at h
  exact h

@[expose] noncomputable def m64Chain : RawSchreierDatum 4060 :=
  arrChain (by norm_num) m64S 5 m64S_size.ge m64B (by decide) noDer5

theorem m64Chain_arrays :
    ChainArrays m64Chain (arrO m64S 5) m64S (arrBase m64B) noDer5 :=
  arrChainArrays _ _ _ (chainCheckFacts m64Parts.1)

theorem m64Chain_eq : m64Chain.originalSubgroup = M64 := by
  rw [m64Chain, arrChain_originalSubgroup, M64]
  congr 1
  have hperm : ∀ i < 5, permOfArr 4060 m64S[i]! = m64G.getD i 1 := by
    intro i hi
    have hF := chainCheckFacts m64Parts.1
    have h := hF.strong_inv i (by rw [m64S_size]; exact hi)
    rw [rawInvs, map_getElem! _ _ (by rw [m64S_size]; exact hi)] at h
    exact Rep.unique (rep_permOfArr h).1 (rep_m64S hi)
  ext g
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [hperm i hi, List.getD_eq_getElem _ _ (by rw [m64G_length]; exact hi)]
    exact List.getElem_mem _
  · intro hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have hi5 : i < 5 := by rwa [m64G_length] at hi
    exact ⟨i, hi5, by rw [hperm i hi5, List.getD_eq_getElem _ _ hi]⟩

theorem card_M64 : Nat.card M64 = 387072 := by
  rw [← m64Chain_eq, m64Chain, card_arrChain _ _ _ (by norm_num) m64Parts.1]
  exact beq_iff_eq.mp m64Parts.2.1

theorem mem_M64_of_sift {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (h : m64Sift t = true) : g ∈ M64 := by
  rw [← m64Chain_eq]
  exact (siftA_iff_mem_originalSubgroup m64Chain_arrays (by norm_num) m64Parts.1 ht).mp h

theorem M64_le_normalizer : M64 ≤ Subgroup.normalizer (u64 : Set (Equiv.Perm (Fin 4060))) := by
  rw [M64, Subgroup.closure_le]
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hi5 : i < 5 := by rwa [m64G_length] at hi
  have hrep := rep_m64S hi5
  rw [List.getD_eq_getElem _ _ hi] at hrep
  have h := List.all_eq_true.mp m64Parts.2.2.1 _ (m64S_mem hi5)
  exact mem_normalizer_of_normsA hb64 hv64 hrep (rep_ruInv' hrep) h

theorem u64_le_M64 : u64 ≤ M64 :=
  refSub_le_of_forall (forall_of_all hb64 (fun _ _ ht h => mem_M64_of_sift ht h)
    m64Parts.2.2.2.1)

theorem u33A_mem (i : Fin 5) : u33A[i.val]! ∈ u33A.toList := by
  rw [getElem!_pos u33A i.val (by simp [u33A, u33W])]
  exact Array.getElem_mem_toList _

theorem u33G_mem_M64 (i : Fin 5) : u33G i ∈ M64 :=
  mem_M64_of_sift (rep_u33A i) (List.all_eq_true.mp m64Parts.2.2.2.2.1 _ (u33A_mem i))

@[expose] noncomputable def uG : List (Equiv.Perm (Fin 4060)) := List.ofFn u33G ++ List.ofFn v64

theorem uG_length : uG.length = 11 := by simp [uG]

theorem uGens_size : uGens.size = 11 := by simp [uGens, u33A, u33W, b64A, wsA, basis64W]

theorem forall₂_uGens : List.Forall₂ (Rep 4060) uGens.toList uG := by
  rw [show uGens.toList = u33A.toList ++ b64A by simp [uGens], uG]
  exact List.rel_append forall₂_u33A hb64

theorem rep_uGens : ∀ h < 11, Rep 4060 uGens[h]! (uG.getD h 1) := fun h hh =>
  rep_getD_of_forall₂ forall₂_uGens h (by rw [uG_length]; exact hh)

theorem rep_uGensI : ∀ h < 11, Rep 4060 (uGens.map ruInv)[h]! (uG.getD h 1)⁻¹ := by
  intro h hh
  rw [map_getElem! _ _ (by rw [uGens_size]; exact hh)]
  exact rep_ruInv' (rep_uGens h hh)

theorem uG_mem : ∀ g ∈ uG, g ∈ Subgroup.closure (Set.range u33G ∪ Set.range v64) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

theorem M64_eq_closure : M64 = Subgroup.closure (Set.range u33G ∪ Set.range v64) := by
  refine le_antisymm ?_ ?_
  · rw [M64, Subgroup.closure_le]
    intro g hg
    obtain ⟨j, hj, hjg⟩ : ∃ j < 5, m64G.getD j 1 = g := by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have hj5 : j < 5 := by rwa [m64G_length] at hj
      exact ⟨j, hj5, List.getD_eq_getElem _ _ hj⟩
    subst hjg
    have h1 := List.all_eq_true.mp m64Parts.2.2.2.2.2.2.1 j (List.mem_range.mpr hj)
    have hlet : lettersOK 11 (strongInU33W.getD j []) = true := by
      have : strongInU33W.all (lettersOK 11) = true := by decide
      exact List.all_eq_true.mp this _ (by
        rw [List.getD_eq_getElem _ _ (by simpa [strongInU33W] using hj)]
        exact List.getElem_mem _)
    have h2 := eq_of_eqA (rep_wordA_evalSigned rep_uGens rep_uGensI _ hlet) (rep_m64S hj) h1
    rw [← h2]
    exact evalSigned_mem uG_mem _
  · rw [Subgroup.closure_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact u33G_mem_M64 i
    · exact u64_le_M64 (Subgroup.subset_closure ⟨i, rfl⟩)

instance u64_normal_M64 : (u64.subgroupOf M64).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (M64_le_normalizer g.2) x).mp hx⟩

theorem card_quot64 : Nat.card (↥M64 ⧸ u64.subgroupOf M64) = 6048 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (u64.subgroupOf M64)
  rw [card_subgroupOf_of_le u64_le_M64, card_refSub hv64, card_M64] at h
  omega

@[expose] noncomputable def u33M (i : Fin 5) : ↥M64 := ⟨u33G i, u33G_mem_M64 i⟩

theorem rep_relA_foldl (r : List (Fin 5 × Bool)) : ∀ (acc : Array ℕ) (g : Equiv.Perm (Fin 4060)),
    Rep 4060 acc g → Rep 4060 (r.foldl (fun acc l => compA 4060 acc
      (if l.2 then u33A[l.1.val]! else ruInv u33A[l.1.val]!)) acc)
      (g * (r.map fun x => cond x.2 (u33G x.1) (u33G x.1)⁻¹).prod) := by
  induction r with
  | nil => intro acc g h; simpa using h
  | cons x r ih =>
    intro acc g h
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    refine ih _ _ (rep_compA h ?_)
    cases hx : x.2
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.cond_false]
      exact rep_ruInv' (rep_u33A x.1)
    · simp only [↓reduceIte, Bool.cond_true]
      exact rep_u33A x.1

theorem rep_relA (r : List (Fin 5 × Bool)) :
    Rep 4060 (relA r) ((r.map fun x => cond x.2 (u33G x.1) (u33G x.1)⁻¹).prod) := by
  have := rep_relA_foldl r (idA 4060) 1 rep_idA
  rwa [one_mul] at this

theorem u33_rels : ∀ r ∈ {r : FreeGroup (Fin 5) | r ∈ u33PresRels.map FreeGroup.mk},
    FreeGroup.lift (fun i => (QuotientGroup.mk (u33M i) : ↥M64 ⧸ u64.subgroupOf M64)) r = 1 := by
  rintro _ hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  have hf : FreeGroup.lift (fun i => (QuotientGroup.mk (u33M i) : ↥M64 ⧸ u64.subgroupOf M64)) =
      (QuotientGroup.mk' (u64.subgroupOf M64)).comp (FreeGroup.lift u33M) :=
    FreeGroup.ext_hom _ _ fun a => by simp
  have hg : M64.subtype.comp (FreeGroup.lift u33M) = FreeGroup.lift u33G :=
    FreeGroup.ext_hom _ _ fun a => by simp [u33M]
  rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  have h1 : ((FreeGroup.lift u33M (FreeGroup.mk w) : ↥M64) : Equiv.Perm (Fin 4060)) =
      FreeGroup.lift u33G (FreeGroup.mk w) := by
    rw [← hg]; rfl
  rw [h1, FreeGroup.lift_mk]
  exact mem_refSub_of_inA hb64 hv64 (rep_relA w) (List.all_eq_true.mp m64Parts.2.2.2.2.2.1 w hw)

@[expose] noncomputable def u33Hom : PG 5 u33PresRels →* ↥M64 ⧸ u64.subgroupOf M64 :=
  PresentedGroup.toGroup u33_rels

theorem u33Hom_surjective : Function.Surjective u33Hom := by
  set H := (u33Hom.range).comap (QuotientGroup.mk' (u64.subgroupOf M64)) with hH
  have hgen : Set.range u33G ∪ Set.range v64 ⊆ (H.map M64.subtype : Set _) := by
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · refine ⟨u33M i, ⟨PresentedGroup.of i, ?_⟩, rfl⟩
      rw [u33Hom, PresentedGroup.toGroup.of]
      rfl
    · have hv : v64 i ∈ M64 := u64_le_M64 (Subgroup.subset_closure ⟨i, rfl⟩)
      refine ⟨⟨v64 i, hv⟩, ⟨1, ?_⟩, rfl⟩
      rw [map_one, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      exact Subgroup.subset_closure ⟨i, rfl⟩
  have hle : M64 ≤ H.map M64.subtype := by
    have h1 : Subgroup.closure (Set.range u33G ∪ Set.range v64) ≤ H.map M64.subtype := by
      rw [Subgroup.closure_le]
      exact hgen
    rwa [← M64_eq_closure] at h1
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy

theorem isPSU_M64 :
    IsPSU 3 3 1 (↥M64 ⧸ u64.subgroupOf M64) := by
  obtain ⟨hfin, hle⟩ := u33Pres_finite_card_le
  have hbij : Function.Bijective u33Hom :=
    u33Hom_surjective.bijective_of_nat_card_le (by rw [card_quot64]; exact hle)
  obtain ⟨e1⟩ := u33Pres_mulEquiv_PSU3
  obtain ⟨e2⟩ := CFSG.Timmesfeld.Final.nonempty_statedProj_statedSU_equiv_PSU3
  exact ⟨⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩, GaloisField 3 (2 * 1), inferInstance,
    inferInstance, CFSG.Timmesfeld.Final.GF9.card,
    ⟨((MulEquiv.ofBijective u33Hom hbij).symm.trans e1).trans e2.symm⟩⟩

theorem exists_conj_t64 {u : Equiv.Perm (Fin 4060)} (hu : u ∈ u64) (h1 : u ≠ 1) :
    ∃ m ∈ M64, m * t64 * m⁻¹ = u := by
  obtain ⟨v, hv, hvu⟩ := exists_rep_of_mem_refSub hb64 hv64 hu
  have h := List.all_eq_true.mp m64Parts.2.2.2.2.2.2.2 v hv
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact absurd (eq_of_eqA hvu rep_idA h) h1
  · obtain ⟨w, hw, he⟩ := List.any_eq_true.mp h
    have hlet : lettersOK 5 w = true := by
      have : conjT64W.all (lettersOK 5) = true := by decide
      exact List.all_eq_true.mp this w hw
    have hr := rep_wM hlet
    exact ⟨_, evalSigned_m64G_mem w, eq_of_eqA (rep_cjA hr (rep_ruInv' hr) rep_t64) hvu he⟩

end Chain

end CFSG.Quasithin.KGC31.Ru

end
