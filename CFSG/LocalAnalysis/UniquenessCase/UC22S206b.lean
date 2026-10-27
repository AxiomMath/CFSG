module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S206a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i
public import CFSG.Quasithin.H13.A7BlkAct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup Equiv
open scoped Pointwise
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.Quasithin.H13.A7Blk (permAct permAct_spec exists_fixed ptPre ptPre_le mem_ptPre ptCore
  mem_normalizer_ptCore nonempty_quot_ptCore stabEquiv isSimpleGroup_stabilizer)

variable {G : Type} [Group G] {n : ℕ}

theorem uc22s206b_simpSec_iso {X S Λ : Type} [Group X] [Finite X] [Group S] [IsSimpleGroup S]
    [Group Λ] (φ : X →* S) (hφ : Function.Surjective φ) (hk : IsPGroup 2 φ.ker)
    (hnc : ∃ a b : Λ, a * b ≠ b * a) (h : uc22p20bSimpSec X Λ) : Nonempty (S ≃* Λ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases uc22p20b_simpSec_restrict φ.ker h with h1 | h2
  · exfalso
    haveI : Group.IsSolvable ↥φ.ker := by
      have := hk.isNilpotent
      infer_instance
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (uc22p20b_simpSec_comm h1 a b)
  · have e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
    exact uc22p20b_simpSec_simple hnc
      (uc22p20b_simpSec_of_surjective e.symm.toMonoidHom e.symm.surjective h2)

theorem uc22s206b_simpSec_sup {L B : Subgroup G} (hB : B ≤ normalizer (L : Set G))
    (hBs : Group.IsSolvable ↥B) {Λ : Type} [Group Λ] (hnc : ∃ a b : Λ, a * b ≠ b * a)
    (h : uc22p20bSimpSec ↥(L ⊔ B) Λ) : uc22p20bSimpSec ↥L Λ := by
  have hLX : L ≤ L ⊔ B := le_sup_left
  haveI : (L.subgroupOf (L ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 (sup_le Subgroup.le_normalizer hB)
  rcases uc22p20b_simpSec_restrict (L.subgroupOf (L ⊔ B)) h with h1 | h2
  · exact uc22p20b_simpSec_of_surjective (Subgroup.subgroupOfEquivOfLe hLX).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hLX).symm.surjective h1
  · exfalso
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' (L.subgroupOf (L ⊔ B))).comp
          (Subgroup.inclusion (le_sup_right : B ≤ L ⊔ B))) := by
      intro q
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf (L ⊔ B)) q
      have hx' : x ∈ ((L ⊔ B : Subgroup G) : Set G) := hx
      rw [Subgroup.coe_mul_of_right_le_normalizer_left L B hB] at hx'
      obtain ⟨l, hl, b, hb, rfl⟩ := hx'
      refine ⟨⟨b, hb⟩, ?_⟩
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [mul_assoc] using (Subgroup.mem_normalizer_iff''.1 (hB hb) l).1 hl
    haveI : Group.IsSolvable ↥B := hBs
    haveI : Group.IsSolvable (↥(L ⊔ B) ⧸ L.subgroupOf (L ⊔ B)) :=
      Group.isSolvable_of_surjective hsurj
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (uc22p20b_simpSec_comm h2 a b)

@[expose] noncomputable def uc22s206bAlpha {L : Subgroup G}
    (e : Bar2 L ≃* alternatingGroup (Fin n)) : ↥L →* alternatingGroup (Fin n) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))

theorem uc22s206bAlpha_surjective {L : Subgroup G} (e : Bar2 L ≃* alternatingGroup (Fin n)) :
    Function.Surjective (uc22s206bAlpha e) := by
  intro y
  obtain ⟨q, rfl⟩ := e.surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) q
  exact ⟨x, rfl⟩

theorem uc22s206bAlpha_ker {L : Subgroup G} (e : Bar2 L ≃* alternatingGroup (Fin n)) :
    (uc22s206bAlpha e).ker = CFSG.pCore 2 ↥L := by
  ext x
  rw [MonoidHom.mem_ker]
  show e (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem uc22s206b_mem_normalizer_ptPre {K : Subgroup G} (α : ↥K →* alternatingGroup (Fin n))
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) (hn : 5 ≤ n) (hn6 : n ≠ 6)
    {i : Fin n} {g : G} (hg : g ∈ normalizer (K : Set G))
    (hgi : permAct α hα hker hn hn6 ⟨g, hg⟩ i = i) : g ∈ normalizer (ptPre α i : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  set σ := permAct α hα hker hn hn6 ⟨g, hg⟩ with hσ
  have hσi : σ⁻¹ i = i := by rw [Perm.inv_eq_iff_eq, hgi]
  have key : ∀ hx : x ∈ K, ∀ hgx : g * x * g⁻¹ ∈ K,
      (α ⟨g * x * g⁻¹, hgx⟩ : Perm (Fin n)) = σ * α ⟨x, hx⟩ * σ⁻¹ := by
    intro hx hgx
    rw [← permAct_spec α hα hker hn hn6]
    congr 2
  rw [mem_ptPre, mem_ptPre]
  constructor
  · rintro ⟨hx, hxi⟩
    have hgx : g * x * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    refine ⟨hgx, ?_⟩
    rw [key hx hgx, Perm.mul_apply, Perm.mul_apply, hσi, hxi, hgi]
  · rintro ⟨hgx, hxi⟩
    have hx : x ∈ K := (Subgroup.mem_normalizer_iff.mp hg x).mpr hgx
    refine ⟨hx, ?_⟩
    rw [key hx hgx, Perm.mul_apply, Perm.mul_apply, hσi] at hxi
    exact σ.injective (hxi.trans hgi.symm)

@[expose] noncomputable def uc22s206bPtPreHom {K : Subgroup G}
    (α : ↥K →* alternatingGroup (Fin n)) (i : Fin n) :
    ↥(ptPre α i) →* ↥(MulAction.stabilizer (alternatingGroup (Fin n)) i) :=
  (α.comp (Subgroup.inclusion (ptPre_le α i))).codRestrict _ fun x => by
    obtain ⟨h, hx⟩ := (mem_ptPre α).mp x.2
    exact hx

theorem uc22s206bPtPreHom_surjective {K : Subgroup G} (α : ↥K →* alternatingGroup (Fin n))
    (hα : Function.Surjective α) (i : Fin n) : Function.Surjective (uc22s206bPtPreHom α i) := by
  rintro ⟨s, hs⟩
  obtain ⟨k, rfl⟩ := hα s
  exact ⟨⟨k, (mem_ptPre α).mpr ⟨k.2, hs⟩⟩, Subtype.ext rfl⟩

theorem uc22s206bPtPreHom_isPGroup_ker {K : Subgroup G} (α : ↥K →* alternatingGroup (Fin n))
    (hker : α.ker = CFSG.pCore 2 ↥K) (i : Fin n) :
    IsPGroup 2 (uc22s206bPtPreHom α i).ker := by
  rintro ⟨x, hx⟩
  have hx1 : α ⟨x, ptPre_le α i x.2⟩ = 1 :=
    congrArg Subtype.val ((uc22s206bPtPreHom α i).mem_ker.mp hx)
  have hxk : (⟨x, ptPre_le α i x.2⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := hker ▸ hx1
  obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup ⟨_, hxk⟩
  refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun y : ↥(CFSG.pCore 2 ↥K) => ((y : ↥K) : G)) hm
  simpa using this

theorem uc22s206b_isSolvable_T [Finite G] (D : Data G) : Group.IsSolvable ↥D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := D.sylowM.isPGroup.isNilpotent
  infer_instance

theorem uc22s206b_k_two [Finite G] (D : Data G) (hO : LieOrderFormulasInput)
    (hB : ListBNonabelian) (h1930 : H1930 D) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) : D.k = 2 := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 9)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hk2 : IsPGroup 2 α.ker := by
    rw [hker]
    exact CFSG.pCore_isPGroup
  have hSE : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    intro hSE
    obtain ⟨Λ, _, hcf, hA⟩ := (h1930 _ hL.2.2.1).2 hSE
    have hnc := hB Λ (listA_le_listB Λ hA)
    have h1 : uc22p20bSimpSec ↥L Λ :=
      uc22s206b_simpSec_sup hL.1 (uc22s206b_isSolvable_T D) hnc (uc22p20b_simpSec_of_cf hcf)
    obtain ⟨e⟩ := uc22s206b_simpSec_iso α hα hk2 hnc h1
    exact uc22s206a_not_listA_alt9 hO e.symm hA
  show kParam D.M = 2
  rw [kParam, if_neg hSE]

theorem uc22s206b_le_M [Finite G] (D : Data G) (hO : LieOrderFormulasInput)
    (hB : ListBNonabelian) (h1930 : H1930 D) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9}
    (hi : ∀ (t : G) (ht : t ∈ D.T),
      permAct α hα hker (by norm_num) (by norm_num) ⟨t, hL.1 ht⟩ i = i) :
    ptPre α i ⊔ D.T ≤ D.M := by
  haveI := isSimpleGroup_stabilizer (n := 9) (by norm_num) i
  by_contra hY
  have hP : ptPre α i ⊔ D.T ∈ hSet D.T D.M :=
    uc22p20b_mem_hSet D hL.2.2.1 le_sup_right (sup_le_sup_right (ptPre_le α i) _) hY
  obtain ⟨Λ, _, hcf, hLB⟩ := (h1930 _ hP).1
  have hnc := hB Λ hLB
  have hTN : D.T ≤ normalizer (ptPre α i : Set G) := fun t ht =>
    uc22s206b_mem_normalizer_ptPre α hα hker (by norm_num) (by norm_num) (hL.1 ht) (hi t ht)
  have h1 : uc22p20bSimpSec ↥(ptPre α i) Λ :=
    uc22s206b_simpSec_sup hTN (uc22s206b_isSolvable_T D) hnc (uc22p20b_simpSec_of_cf hcf)
  obtain ⟨e⟩ := uc22s206b_simpSec_iso (uc22s206bPtPreHom α i)
    (uc22s206bPtPreHom_surjective α hα i) (uc22s206bPtPreHom_isPGroup_ker α hker i) hnc h1
  exact uc22s206a_not_listB_alt8 hO (e.symm.trans (stabEquiv i)) hLB

theorem uc22s206b_inf_eq [Finite G] (D : Data G) (hO : LieOrderFormulasInput)
    (hB : ListBNonabelian) (h1930 : H1930 D) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9}
    (hi : ∀ (t : G) (ht : t ∈ D.T),
      permAct α hα hker (by norm_num) (by norm_num) ⟨t, hL.1 ht⟩ i = i) :
    L ⊓ D.M = ptPre α i := by
  have hPM : ptPre α i ≤ D.M :=
    le_sup_left.trans (uc22s206b_le_M D hO hB h1930 hL α hα hker hi)
  refine le_antisymm ?_ (le_inf (ptPre_le α i) hPM)
  have hstab : MulAction.stabilizer (alternatingGroup (Fin 9)) i ≤
      ((L ⊓ D.M).subgroupOf L).map α := by
    intro s hs
    obtain ⟨k, rfl⟩ := hα s
    have hkP : (k : G) ∈ ptPre α i := (mem_ptPre α).mpr ⟨k.2, hs⟩
    exact ⟨k, Subgroup.mem_subgroupOf.mpr ⟨k.2, hPM hkP⟩, rfl⟩
  rcases (uc22s206a_isCoatom_stabilizer i).le_iff.mp hstab with h | h
  · exfalso
    apply hL.2.2.1.2.1
    refine sup_le ?_ D.sylowM.le
    intro l hl
    have hmem : α ⟨l, hl⟩ ∈ ((L ⊓ D.M).subgroupOf L).map α := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨m, hm, hml⟩ := hmem
    have hz : m⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hml, inv_mul_cancel]
    have hzT : ((m⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ D.T :=
      (uc22p20i_pCoreOf_le D hL (Subgroup.mem_map_of_mem L.subtype hz)).1
    have hmM : (m : G) ∈ D.M := (Subgroup.mem_subgroupOf.mp hm).2
    have key : (m : G) * ((m⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ D.M :=
      D.M.mul_mem hmM (D.sylowM.le hzT)
    simpa using key
  · intro x hx
    have hxS : α ⟨x, hx.1⟩ ∈ ((L ⊓ D.M).subgroupOf L).map α :=
      ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [h] at hxS
    exact (mem_ptPre α).mpr ⟨hx.1, hxS⟩

theorem uc22s206b_by1930 [Finite G] (D : Data G) (hO : LieOrderFormulasInput)
    (hB : ListBNonabelian) (h1930 : H1930 D) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    (h9 : IsAlt (Bar2 L) 9) :
    D.k = 2 ∧ ∃ (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
      (hker : α.ker = CFSG.pCore 2 ↥L) (i : Fin 9),
      (∀ (t : G) (ht : t ∈ D.T),
        permAct α hα hker (by norm_num) (by norm_num) ⟨t, hL.1 ht⟩ i = i) ∧
      L ⊓ D.M = ptPre α i ∧ D.T ≤ normalizer (ptCore α i : Set G) ∧
      Nonempty (↥(ptCore α i) ⧸ CFSG.pCore 2 ↥(ptCore α i) ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨e⟩ := h9
  have hα := uc22s206bAlpha_surjective e
  have hker := uc22s206bAlpha_ker e
  obtain ⟨i, hi⟩ := exists_fixed (uc22s206bAlpha e) hα hker (by norm_num) (by norm_num)
    ⟨4, rfl⟩ hL.1 D.sylowM.isPGroup
  refine ⟨uc22s206b_k_two D hO hB h1930 hL _ hα hker, uc22s206bAlpha e, hα, hker, i, hi,
    uc22s206b_inf_eq D hO hB h1930 hL _ hα hker hi, fun t ht => ?_, ?_⟩
  · exact mem_normalizer_ptCore _ hα hker (by norm_num) (by norm_num) (hL.1 ht) (hi t ht)
  · exact nonempty_quot_ptCore _ hα hker (by norm_num) i

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
