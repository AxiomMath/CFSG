module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Defs
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenE6Components
import CFSG.Dihedral.DisconnectedInvolutionGraph.SubgroupConjugationAction
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2Conj
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.CentralSplitTransfer
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.B1Restrict
import CFSG.Quasithin.Background.B4Statement
import CFSG.Quasithin.Background.F6GoldschmidtList
import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType

variable {G : Type} [Group G] [Finite G]

theorem exists_twoSub_normalized_of_component {p : ℕ}
    [Fact p.Prime] {A C Q : Subgroup G} (hA : IsPGroup p A)
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) (hQ : IsComponentOf Q C)
    (hpQ : ¬ p ∣ Nat.card Q) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ C ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
      ¬ S ≤ Subgroup.centralizer (Q : Set G) := by
  classical
  let N : Subgroup G := A ⊓ Subgroup.normalizer (Q : Set G)
  have hNA : N ≤ A := inf_le_left
  have hNQ : N ≤ Subgroup.normalizer (Q : Set G) := inf_le_right
  have hNp : IsPGroup p N := hA.to_le hNA
  letI : MulDistribMulAction N G :=
    CFSG.DisconnectedInvolutionGraph.Helpers.subgroupConjugationAction N
  have hInvQ : CFSG.DisconnectedInvolutionGraph.Helpers.InvariantSubgroup (A := N) Q :=
    CFSG.DisconnectedInvolutionGraph.Helpers.subgroup_conjugation_invariant_of_le_normalizer
      Q N hNQ
  letI : MulDistribMulAction N Q :=
    CFSG.DisconnectedInvolutionGraph.Helpers.invariantSubgroupAction Q hInvQ
  obtain ⟨T₀, hT₀⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.coprime_pgroup_exists_invariant_sylow
      (A := N) (G := Q) p 2 hNp hpQ
  have hfix_mem : ∀ (n : N) (q : Q), q ∈ (T₀ : Subgroup Q) → n • q ∈ (T₀ : Subgroup Q) :=
    fun n q hq => hT₀ n q hq
  have hfix_val : ∀ (n : N) (q : Q),
      ((n • q : Q) : G) = (n : G) * (q : G) * (n : G)⁻¹ := fun _ _ => rfl
  let T : Subgroup G := (T₀ : Subgroup Q).map Q.subtype
  have hT2 : IsPGroup 2 T := T₀.isPGroup'.map Q.subtype
  have hTleQ : T ≤ Q := Subgroup.map_subtype_le _
  have hT_not_cent : ¬ T ≤ Subgroup.centralizer (Q : Set G) := by
    intro hTcent
    have hT0_le_center : (T₀ : Subgroup Q) ≤ Subgroup.center Q := by
      intro q hq
      rw [Subgroup.mem_center_iff]
      intro g
      have hqT : (q : G) ∈ T := Subgroup.mem_map_of_mem _ hq
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hTcent hqT)) (g : G) g.2)
    have hT0_index : ¬ 2 ∣ (T₀ : Subgroup Q).index := Sylow.not_dvd_index T₀
    have hcenter_index : ¬ 2 ∣ (Subgroup.center Q).index := by
      intro h2
      apply hT0_index
      have hmul := Subgroup.relIndex_mul_index hT0_le_center
      rw [← hmul]
      exact dvd_mul_of_dvd_right h2 _
    have hodd : Odd (Nat.card (Q ⧸ Subgroup.center Q)) := by
      rw [← Subgroup.index_eq_card]
      exact Nat.not_even_iff_odd.mp (by
        simpa [Nat.even_iff, Nat.dvd_iff_mod_eq_zero] using hcenter_index)
    have hsol : Group.IsSolvable (Q ⧸ Subgroup.center Q) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    haveI : Group.IsPerfect Q := Group.isPerfect_def.mpr hQ.2.2.1
    haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2.2.2
    exact (Group.IsPerfect.not_isSolvable (Q ⧸ Subgroup.center Q)) hsol
  let Qa : A → Subgroup G := fun a => Q.map (MulAut.conj (a : G)).toMonoidHom
  let Tf : A → Subgroup G := fun a => T.map (MulAut.conj (a : G)).toMonoidHom
  have mem_Qa : ∀ (a : A) (g : G),
      g ∈ Qa a ↔ ∃ q : Q, g = (a : G) * (q : G) * (a : G)⁻¹ := by
    intro a g
    change g ∈ Subgroup.map (MulAut.conj (a : G)).toMonoidHom Q ↔
      ∃ q : Q, g = (a : G) * (q : G) * (a : G)⁻¹
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, by simp [MulAut.conj_apply]⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.2, by simp [MulAut.conj_apply]⟩
  have mem_Tf : ∀ (a : A) (g : G),
      g ∈ Tf a ↔ ∃ q : Q, q ∈ (T₀ : Subgroup Q) ∧
        g = (a : G) * (q : G) * (a : G)⁻¹ := by
    intro a g
    change g ∈ Subgroup.map (MulAut.conj (a : G)).toMonoidHom
      (Subgroup.map Q.subtype (T₀ : Subgroup Q)) ↔
      ∃ q : Q, q ∈ (T₀ : Subgroup Q) ∧ g = (a : G) * (q : G) * (a : G)⁻¹
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨q, hq, by simp [MulAut.conj_apply]⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(q : G), Subgroup.mem_map_of_mem _ hq, by simp [MulAut.conj_apply]⟩
  have hQa_comp : ∀ a : A, IsComponentOf (Qa a) C := by
    intro a
    have hnorm : Subgroup.map (MulAut.conj (a : G)).toMonoidHom C = C :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAC a.2)
    have hmap := isComponentOf_map_of_injective (MulAut.conj (a : G)).toMonoidHom
      (MulAut.conj (a : G)).injective hQ
    rw [hnorm] at hmap
    simpa only [Qa] using hmap
  have hQa_leC : ∀ a : A, Qa a ≤ C := fun a => (hQa_comp a).1
  have hnative : ∀ {K : Subgroup G}, IsComponentOf K C → CFSG.IsComponent (K.subgroupOf C) := by
    intro K hK
    refine (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native
      (K.subgroupOf C)).mp ?_
    have h := ggIsComponentOf_subgroupOf_of_le C hK.1 hK
    simpa using h
  have hpair : ∀ a b : A, Qa a = Qa b ∨
      ∀ x ∈ Qa a, ∀ y ∈ Qa b, x * y = y * x := by
    intro a b
    by_cases h : Qa a = Qa b
    · exact Or.inl h
    · exact Or.inr (CFSG.GroupTheory.commute_of_isComponent_subgroupOf (X := C)
        (K := Qa a) (K' := Qa b) (hQa_leC a) (hQa_leC b)
        (hnative (hQa_comp a)) (hnative (hQa_comp b)) h)
  have hTf_eq_of_Qa_eq : ∀ a b : A, Qa a = Qa b → Tf a = Tf b := by
    intro a b hQab
    let nG : G := (a : G)⁻¹ * (b : G)
    have hnNQ : nG ∈ Subgroup.normalizer (Q : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hQab' : Subgroup.map (MulAut.conj (a : G)).toMonoidHom Q =
          Subgroup.map (MulAut.conj (b : G)).toMonoidHom Q := hQab
      have h := congrArg
        (fun S : Subgroup G => S.map (MulAut.conj ((a : G)⁻¹)).toMonoidHom) hQab'
      rw [Subgroup.map_map, Subgroup.map_map] at h
      have h1 : (MulAut.conj ((a : G)⁻¹)).toMonoidHom.comp
          (MulAut.conj (a : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      have h2 : (MulAut.conj ((a : G)⁻¹)).toMonoidHom.comp
          (MulAut.conj (b : G)).toMonoidHom = (MulAut.conj nG).toMonoidHom := by
        ext x
        simp [nG, MulAut.conj_apply, mul_assoc]
      rw [h1, h2, Subgroup.map_id] at h
      exact h.symm
    have hnN : nG ∈ N :=
      ⟨A.mul_mem (A.inv_mem a.2) b.2, hnNQ⟩
    apply le_antisymm
    · rintro g hg
      rw [mem_Tf] at hg ⊢
      obtain ⟨q, hq, rfl⟩ := hg
      refine ⟨(⟨nG⁻¹, N.inv_mem hnN⟩ : N) • q, hfix_mem _ q hq, ?_⟩
      rw [hfix_val]
      simp only [nG] at *
      group
    · rintro g hg
      rw [mem_Tf] at hg ⊢
      obtain ⟨q, hq, rfl⟩ := hg
      refine ⟨(⟨nG, hnN⟩ : N) • q, hfix_mem _ q hq, ?_⟩
      rw [hfix_val]
      simp only [nG] at *
      group
  have hTf2 : ∀ a : A, IsPGroup 2 (Tf a) := fun a => hT2.map _
  have hTf_le_Qa : ∀ a : A, Tf a ≤ Qa a := fun a => Subgroup.map_mono hTleQ
  have hTf_normalizes : ∀ a b : A, Tf a ≤ Subgroup.normalizer (Tf b : Set G) := by
    intro a b
    rcases hpair a b with hEq | hComm
    · rw [hTf_eq_of_Qa_eq a b hEq]
      exact Subgroup.le_normalizer
    · have hQaCentQb : Qa a ≤ Subgroup.centralizer (Qa b : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hComm x hx y hy).symm
      have hTfCent : Tf a ≤ Subgroup.centralizer (Tf b : Set G) :=
        (hTf_le_Qa a).trans (hQaCentQb.trans
          (Subgroup.centralizer_le fun y hy => hTf_le_Qa b hy))
      exact hTfCent.trans (Subgroup.centralizer_le_normalizer _)
  have hnormalizes_sup : ∀ (s : Finset A) (a : A),
      Tf a ≤ Subgroup.normalizer ((s.sup Tf : Subgroup G) : Set G) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro a
        rw [Finset.sup_empty, Subgroup.normalizer_eq_top]
        exact le_top
    | insert b s hb ih =>
        intro a
        rw [Finset.sup_insert]
        exact (le_inf (hTf_normalizes a b) (ih a)).trans
          (Subgroup.inf_normalizer_le_normalizer_sup (Tf b) (s.sup Tf))
  have hmain : ∀ s : Finset A, IsPGroup 2 (s.sup Tf : Subgroup G) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.sup_empty]
        exact IsPGroup.of_bot
    | insert a s ha ih =>
        rw [Finset.sup_insert]
        exact IsPGroup.to_sup_of_normal_right' (hTf2 a) ih (hnormalizes_sup s a)
  letI : Fintype A := Fintype.ofFinite A
  refine ⟨⨆ a : A, Tf a, ?_, ?_, ?_, ?_⟩
  · have h := hmain Finset.univ
    rw [Finset.sup_univ_eq_iSup] at h
    exact h
  · exact iSup_le fun a => (hTf_le_Qa a).trans (hQa_leC a)
  · intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmap : Subgroup.map (MulAut.conj a).toMonoidHom (⨆ b : A, Tf b) =
        ⨆ b : A, Tf ((⟨a, ha⟩ : A) * b) := by
      rw [Subgroup.map_iSup]
      congr 1
      funext b
      change Subgroup.map (MulAut.conj a).toMonoidHom (Tf b) = Tf (⟨a, ha⟩ * b)
      change Subgroup.map (MulAut.conj a).toMonoidHom
        (Subgroup.map (MulAut.conj (b : G)).toMonoidHom T) = Tf (⟨a, ha⟩ * b)
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    change Subgroup.map (MulAut.conj a).toMonoidHom (⨆ b : A, Tf b) = ⨆ b : A, Tf b
    rw [hmap]
    apply le_antisymm
    · exact iSup_le fun b => le_iSup Tf ((⟨a, ha⟩ : A) * b)
    · refine iSup_le fun b => ?_
      have hb : (⟨a, ha⟩ : A) * ((⟨a, ha⟩ : A)⁻¹ * b) = b := by group
      rw [← hb]
      exact le_iSup (fun c : A => Tf ((⟨a, ha⟩ : A) * c)) ((⟨a, ha⟩ : A)⁻¹ * b)
  · intro hS
    have hTS : T ≤ ⨆ a : A, Tf a := by
      have h1 : Tf 1 = T := by
        change Subgroup.map (MulAut.conj (((1 : A) : G))).toMonoidHom T = T
        rw [show MulAut.conj (((1 : A) : G)) = 1 by simp]
        exact Subgroup.map_id T
      rw [← h1]
      exact le_iSup Tf 1
    exact hT_not_cent (hTS.trans hS)

theorem excTwE6_isComponentOf_L {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G)) (hx : x ∈ Bs) :
    IsComponentOf (L.subgroupOf (ggG0 3 B x L D J))
      (ggAutFixedSubgroup (ggGamma (ggG0 3 B x L D J) hN ⟨x, hx⟩)) := by
  have hstar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  obtain ⟨-, hx', hxne, hLcomp, hcyc⟩ := hstar
  have hLG0 : L ≤ ggG0 3 B x L D J := le_sup_left
  have hmap := ggIsComponentOf_subgroupOf_of_le (ggG0 3 B x L D J) hLG0 hLcomp
  have hfixed : (Subgroup.centralizer ({x} : Set G)).subgroupOf (ggG0 3 B x L D J) =
      ggAutFixedSubgroup (ggGamma (ggG0 3 B x L D J) hN ⟨x, hx⟩) := by
    ext l
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      mem_ggAutFixedSubgroup]
    constructor
    · intro h
      apply Subtype.ext
      rw [ggGamma_coe, ← h, mul_assoc, mul_inv_cancel, mul_one]
    · intro h
      have h' : x * (l : G) * x⁻¹ = (l : G) := by
        have := congrArg Subtype.val h
        rwa [ggGamma_coe] at this
      calc (l : G) * x = (x * (l : G) * x⁻¹) * x := by rw [h']
        _ = x * (l : G) := by group
  rwa [hfixed] at hmap

theorem excTwE6_component_unique {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G)) (hx : x ∈ Bs)
    (hNo : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ ggG0 3 B x L D J →
      Bs ≤ Subgroup.normalizer (S : Set G) →
      ¬ S ≤ Subgroup.centralizer (ggG0 3 B x L D J : Set G) → False)
    (Q : Subgroup ↥(ggG0 3 B x L D J))
    (hQ : IsComponentOf Q (ggAutFixedSubgroup (ggGamma (ggG0 3 B x L D J) hN ⟨x, hx⟩))) :
    Q = L.subgroupOf (ggG0 3 B x L D J) := by
  classical
  by_contra hne
  let G₀ : Subgroup G := ggG0 3 B x L D J
  let C' : Subgroup ↥G₀ := ggAutFixedSubgroup (ggGamma G₀ hN ⟨x, hx⟩)
  have hC'_eq : C' = (Subgroup.centralizer ({x} : Set G)).subgroupOf G₀ := by
    ext l
    rw [mem_ggAutFixedSubgroup, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : x * (l : G) * x⁻¹ = (l : G) := by
        have := congrArg Subtype.val h
        rwa [ggGamma_coe] at this
      calc (l : G) * x = (x * (l : G) * x⁻¹) * x := by rw [h']
        _ = x * (l : G) := by group
    · intro h
      apply Subtype.ext
      rw [ggGamma_coe, ← h, mul_assoc, mul_inv_cancel, mul_one]
  let C : Subgroup G := G₀ ⊓ Subgroup.centralizer ({x} : Set G)
  have hCeq : C'.map G₀.subtype = C := by
    rw [hC'_eq, Subgroup.subgroupOf_map_subtype]
    exact inf_comm ..
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hstar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  obtain ⟨-, -, -, hLcomp, hcyc⟩ := hstar
  obtain ⟨-, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hxord : orderOf x = 3 := hcfg.orderOf_x
  have hLG0 : L ≤ G₀ := le_sup_left
  let Q' : Subgroup G := Q.map G₀.subtype
  have hQ'leG0 : Q' ≤ G₀ := Subgroup.map_subtype_le _
  have hQ'comp : IsComponentOf Q' C := by
    have hmap := isComponentOf_map_of_injective G₀.subtype G₀.subtype_injective hQ
    rw [hCeq] at hmap
    simpa only [Q'] using hmap
  have hL'comp : IsComponentOf L C :=
    IsComponentOf.of_le_of_le hLcomp (le_inf hLG0 hLx) inf_le_right
  have hQ'ne : Q' ≠ L := by
    intro h
    apply hne
    have h1 : Q'.subgroupOf G₀ = Q := by
      change Subgroup.comap G₀.subtype Q' = Q
      exact Subgroup.comap_map_eq_self_of_injective G₀.subtype_injective Q
    rw [h] at h1
    exact h1.symm
  have hnative : ∀ {K : Subgroup G}, IsComponentOf K C → CFSG.IsComponent (K.subgroupOf C) := by
    intro K hK
    refine (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native
      (K.subgroupOf C)).mp ?_
    have h := ggIsComponentOf_subgroupOf_of_le C hK.1 hK
    simpa using h
  have hcomm : ∀ q ∈ Q', ∀ l ∈ L, q * l = l * q :=
    CFSG.GroupTheory.commute_of_isComponent_subgroupOf (X := C) (K := Q') (K' := L)
      hQ'comp.1 hL'comp.1 (hnative hQ'comp) (hnative hL'comp) hQ'ne
  have hQ'leCentL : Q' ≤ Subgroup.centralizer (L : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (hcomm q hq l hl).symm
  have hQ'leCentx : Q' ≤ Subgroup.centralizer ({x} : Set G) :=
    hQ'comp.1.trans inf_le_right
  have hxCentL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hperfQ' : commutator Q' = ⊤ := hQ'comp.2.2.1
  by_cases h3 : 3 ∣ Nat.card Q'
  ·
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let P : Sylow 3 Q' := Sylow.nonempty.some
    have hPcard : 3 ∣ Nat.card ↥P := by
      have hPcard_eq : Nat.card ↥P = 3 ^ (Nat.card Q').factorization 3 :=
        P.card_eq_multiplicity
      rw [hPcard_eq]
      have hfac : 1 ≤ (Nat.card Q').factorization 3 :=
        (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three (Nat.card_pos.ne')).mp h3
      exact dvd_pow_self 3 (Nat.one_le_iff_ne_zero.mp hfac)
    obtain ⟨p3, hp3ord⟩ := exists_prime_orderOf_dvd_card' 3 hPcard
    let P' : Subgroup G := (P : Subgroup Q').map Q'.subtype
    have hP'3 : IsPGroup 3 P' := P.isPGroup'.map Q'.subtype
    have hP'leQ : P' ≤ Q' := Subgroup.map_subtype_le _
    have hP'leCentL : P' ≤ Subgroup.centralizer (L : Set G) := hP'leQ.trans hQ'leCentL
    have hP'leCentx : P' ≤ Subgroup.centralizer ({x} : Set G) := hP'leQ.trans hQ'leCentx
    have hx3 : IsPGroup 3 (Subgroup.zpowers x) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hxord]
      norm_num
    have hxP'norm : Subgroup.zpowers x ≤ Subgroup.normalizer (P' : Set G) := by
      refine (Subgroup.zpowers_le.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hP'leCentx hy)
    let H : Subgroup G := Subgroup.zpowers x ⊔ P'
    have hH3 : IsPGroup 3 H := IsPGroup.to_sup_of_normal_right' hx3 hP'3 hxP'norm
    have hHcentL : H ≤ Subgroup.centralizer (L : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr hxCentL) hP'leCentL
    have hHcyc : IsCyclic H := hcyc H hHcentL hH3
    have hxH : x ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    have hp3H : ((p3 : Q') : G) ∈ H :=
      Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ p3.2)
    have hp3Gord : orderOf ((p3 : Q') : G) = 3 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hp3ord
    have hp3Hord : orderOf (⟨((p3 : Q') : G), hp3H⟩ : H) = 3 := by
      rw [← Subgroup.orderOf_coe (⟨((p3 : Q') : G), hp3H⟩ : H)]
      exact hp3Gord
    have hxHord : orderOf (⟨x, hxH⟩ : H) = 3 := by
      rw [← Subgroup.orderOf_coe (⟨x, hxH⟩ : H)]
      exact hxord
    have hzpowers_eq : Subgroup.zpowers (⟨x, hxH⟩ : H) =
        Subgroup.zpowers (⟨((p3 : Q') : G), hp3H⟩ : H) := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
        hxHord, hp3Hord]
    have hxP' : x ∈ P' := by
      have hxZ : (⟨x, hxH⟩ : H) ∈
          Subgroup.zpowers (⟨((p3 : Q') : G), hp3H⟩ : H) := by
        rw [← hzpowers_eq]
        exact Subgroup.mem_zpowers _
      have hle : Subgroup.zpowers (⟨((p3 : Q') : G), hp3H⟩ : H) ≤ P'.subgroupOf H := by
        rw [Subgroup.zpowers_le]
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ p3.2)
      exact Subgroup.mem_subgroupOf.mp (hle hxZ)
    have hxQ' : x ∈ Q' := hP'leQ hxP'
    have hxZQ' : (⟨x, hxQ'⟩ : Q') ∈ Subgroup.center Q' := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hQ'leCentx g.2))
    have hxordQ' : orderOf (⟨x, hxQ'⟩ : Q') = 3 := by
      rw [← Subgroup.orderOf_coe (⟨x, hxQ'⟩ : Q')]
      exact hxord
    haveI : IsCyclic H := hHcyc
    have hP'cyc : IsCyclic ↥P' := Subgroup.isCyclic_of_le (le_sup_right : P' ≤ H)
    have hP'cyc' : IsCyclic ↥((P : Subgroup Q').map Q'.subtype) := hP'cyc
    haveI : IsCyclic ↥((P : Subgroup Q').map Q'.subtype) := hP'cyc'
    have hPcyc : IsCyclic ↥P :=
      isCyclic_of_injective
        (Subgroup.equivMapOfInjective (P : Subgroup Q') Q'.subtype Q'.subtype_injective).toMonoidHom
        (Subgroup.equivMapOfInjective (P : Subgroup Q') Q'.subtype
          Q'.subtype_injective).injective
    haveI : IsCyclic ↥P := hPcyc
    haveI : IsMulCommutative ↥P := IsCyclic.isMulCommutative
    exact (CFSG.GroupTheory.not_mem_commutator_of_mem_center P
      (inferInstance : IsMulCommutative ↥P) hxZQ' hxordQ') (by
        rw [hperfQ']
        exact Subgroup.mem_top _)
  ·
    have hA3 : IsPGroup 3 Bs := hBs.isPGroup
    have hBsCentx : Bs ≤ Subgroup.centralizer ({x} : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hBs.1.is_comm.comm ⟨x, hxBs⟩ ⟨b, hb⟩).symm
    have hAC : Bs ≤ Subgroup.normalizer (C : Set G) :=
      (le_inf hN (hBsCentx.trans Subgroup.le_normalizer)).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := G₀)
          (K := Subgroup.centralizer ({x} : Set G)))
    obtain ⟨S, hS2, hSC, hBS, hSnotCent⟩ :=
      exists_twoSub_normalized_of_component (p := 3) hA3 hAC hQ'comp h3
    have hSG0 : S ≤ G₀ := hSC.trans inf_le_left
    have hSnotCentG0 : ¬ S ≤ Subgroup.centralizer (G₀ : Set G) := by
      intro hScent
      apply hSnotCent
      exact hScent.trans (Subgroup.centralizer_le fun q hq => hQ'leG0 hq)
    exact hNo S hS2 hSG0 hBS hSnotCentG0

end CFSG.StandardType.GGQ2Frame.ExcPlacement
