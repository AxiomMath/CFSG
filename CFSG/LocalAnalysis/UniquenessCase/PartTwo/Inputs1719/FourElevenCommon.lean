module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourElevenDefs
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenBasic
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupLargeMembers
public import CFSG.RankThree.GF2n.Tim79a34ResidualSylow
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.CGT.PushingUpLit.LIT.Foote.GroupAux
public import CFSG.GH74.Generic.BProg.B2.FixFourS3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {p : ℕ}

theorem map_conj_of_subgroupOf_conj {Q : Type} [Group Q] {L A A₀ : Subgroup Q}
    (hA : A ≤ L) (hA₀ : A₀ ≤ L) {g : ↥L}
    (h : A₀.subgroupOf L = (A.subgroupOf L).map (MulAut.conj g).toMonoidHom) :
    A₀ = A.map (MulAut.conj (g : Q)).toMonoidHom := by
  calc
    A₀ = (A₀.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hA₀).symm
    _ = ((A.subgroupOf L).map (MulAut.conj g).toMonoidHom).map L.subtype := by rw [h]
    _ = (A.subgroupOf L).map (((MulAut.conj (g : Q)).toMonoidHom).comp L.subtype) := by
          rw [Subgroup.map_map]
          congr 1
    _ = ((A.subgroupOf L).map L.subtype).map (MulAut.conj (g : Q)).toMonoidHom := by
          rw [← Subgroup.map_map]
    _ = A.map (MulAut.conj (g : Q)).toMonoidHom := by
          rw [Subgroup.map_subgroupOf_eq_of_le hA]

theorem FourElevenSetting.centralizer_eq_bot (h : FourElevenSetting Q L p) :
    centralizer (L : Set Q) = ⊥ := by
  have hsimple : IsSimpleGroup ↥L := by
    rcases h.isL3 with hL | hL
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
  exact CFSG.LocalAnalysis.WeakClosure81.centralizer_eq_bot_of_fstar_top_eq
    h.fstar_eq hsimple h.nonabelian

theorem FourElevenSetting.pCoreOf_two_top (h : FourElevenSetting Q L p) :
    pCoreOf 2 (⊤ : Subgroup Q) = ⊥ := by
  have hsimple : IsSimpleGroup ↥L := by
    rcases h.isL3 with hL | hL
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
  exact CFSG.LocalAnalysis.WeakClosure81.pCoreOf_top_eq_bot_of_almostSimple
    h.normal hsimple h.nonabelian h.centralizer_eq_bot

theorem FourElevenSetting.isPGroup_quotient [L.Normal] (h : FourElevenSetting Q L p) :
    IsPGroup 2 (Q ⧸ L) := by
  obtain ⟨T, hT, hLT⟩ := h.sup_eq_top
  refine hT.isPGroup.of_surjective ((QuotientGroup.mk' L).comp T.subtype) ?_
  intro y
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
  have hq : q ∈ L ⊔ T := hLT ▸ Subgroup.mem_top q
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hq
  obtain ⟨l, hl, t, ht, rfl⟩ := hq
  refine ⟨⟨t, ht⟩, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    QuotientGroup.mk'_apply, QuotientGroup.mk_mul]
  rw [(QuotientGroup.eq_one_iff l).mpr hl, one_mul]

theorem FourElevenSetting.index_le_two [L.Normal] (h : FourElevenSetting Q L p) :
    L.index ≤ 2 :=
  CFSG.LocalAnalysis.WeakClosure81.FourEleven.index_le_two h.prime h.ne_two
    h.centralizer_eq_bot h.isPGroup_quotient h.isL3

theorem FourElevenSetting.sup_eq_top_of_isSylowIn (h : FourElevenSetting Q L p) {T : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) : L ⊔ T = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : L.Normal := h.normal
  have hmain := CFSG.RankThree.GF2n.Tim79a.sup_eq_top_of_sylow
    (G := Q) (G₀ := L) h.isPGroup_quotient
    (hT.isPGroup.toSylow (by simpa [Subgroup.relIndex_top_right] using hT.not_dvd_relIndex))
  simpa using hmain

theorem FourElevenSetting.exists_central_involution (h : FourElevenSetting Q L p)
    {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) :
    ∃ z ∈ L, orderOf z = 2 ∧ ∀ t ∈ T, t * z = z * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup ↥L := by
    rcases h.isL3 with hL | hL
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
  have := hsimple
  have hnc : ¬ IsMulCommutative ↥L := by
    intro hcomm
    obtain ⟨a, b, hab⟩ := h.nonabelian
    exact hab ((isMulCommutative_iff.mp hcomm) a b)
  have hperf : Group.IsPerfect ↥L :=
    Group.IsPerfect.mk (CFSG.GroupTheory.commutator_eq_top_of_isSimpleGroup hsimple hnc)
  have heven : Even (Nat.card ↥L) :=
    Nat.not_odd_iff_even.mp
      (CFSG.CGT.PushingUpLit.LIT.Foote.not_odd_card_of_perfect (Q := ↥L))
  have h2dvd : 2 ∣ Nat.card ↥L := even_iff_two_dvd.mp heven
  have hSyl : IsSylowIn 2 (T ⊓ L) L :=
    hT.inf_normal (N := L) le_top (h.normal.subgroupOf (⊤ : Subgroup Q))
  have hv : 1 ≤ (Nat.card ↥L).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two (Nat.card_pos.ne')).mp h2dvd
  have hSne : Nat.card ↥(T ⊓ L) ≠ 1 := by
    rw [hSyl.card_eq]
    exact ne_of_gt (lt_of_lt_of_le (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) hv))
  have hNcard : Nat.card ↥(L.subgroupOf T) = Nat.card ↥(T ⊓ L) := by
    rw [show L.subgroupOf T = (T ⊓ L).subgroupOf T by
      ext x
      simp]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : T ⊓ L ≤ T))
  have hNnt : Nontrivial (L.subgroupOf T) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hNcard]
    exact lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne')) hSne.symm
  have hNnorm : (L.subgroupOf T).Normal := h.normal.subgroupOf T
  have : Fact (IsPGroup 2 T) := ⟨hT.isPGroup⟩
  obtain ⟨x, hx1, hxcenter⟩ :=
    CFSG.exists_nontrivial_center_mem_normal (N := L.subgroupOf T) (p := 2)
  let zT : T := (x : T)
  let z : Q := (zT : Q)
  have hzL : z ∈ L := Subgroup.mem_subgroupOf.mp x.2
  have hz1 : z ≠ 1 := by
    intro hz
    apply hx1
    apply Subtype.ext
    apply Subtype.ext
    exact hz
  have hzT : ∀ t ∈ T, z * t = t * z := by
    intro t ht
    have hct : (⟨t, ht⟩ : T) * zT = zT * (⟨t, ht⟩ : T) :=
      (Subgroup.mem_center_iff.mp hxcenter) ⟨t, ht⟩
    exact (congrArg (fun y : T => (y : Q)) hct).symm
  obtain ⟨k, hk⟩ := hT.isPGroup.exists_orderOf_eq_pow zT
  have hkz : orderOf z = 2 ^ k := by
    change orderOf (zT : Q) = 2 ^ k
    rw [Subgroup.orderOf_coe zT, hk]
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    have hone : orderOf z = 1 := by rw [hkz, hk0', pow_zero]
    exact hz1 (orderOf_eq_one_iff.mp hone)
  let w : Q := z ^ (orderOf z / 2)
  have hwL : w ∈ L := Subgroup.pow_mem (K := L) hzL _
  have hword : orderOf w = 2 := by
    have h2k : 2 ∣ orderOf z := by
      rw [hkz]
      exact dvd_pow_self 2 (by omega)
    have hpos : orderOf z ≠ 0 := by rw [hkz]; exact pow_ne_zero k (by norm_num)
    simpa [w] using orderOf_pow_orderOf_div (x := z) (n := 2) hpos h2k
  refine ⟨w, hwL, hword, ?_⟩
  intro t ht
  exact ((show Commute z t from hzT t ht).pow_left _).eq.symm

theorem FourElevenSetting.eq_top_of_le (h : FourElevenSetting Q L p) {T : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) {j : ℕ} {Ω : Set (Subgroup Q)} (hLK : L ≤ genEi j T Ω ⊔ T) :
    genEi j T Ω ⊔ T = ⊤ := by
  have htop : L ⊔ T = ⊤ := h.sup_eq_top_of_isSylowIn hT
  refine le_antisymm le_top ?_
  calc (⊤ : Subgroup Q) = L ⊔ T := htop.symm
    _ ≤ genEi j T Ω ⊔ T := by
          simpa [sup_assoc] using sup_le_sup_right hLK T

omit [Finite Q] in
theorem iSup_calEi_one_le_genEi {T A : Subgroup Q} {Ω : Set (Subgroup Q)} (hAΩ : A ∈ Ω)
    (hAT : A ≤ T) {j : ℕ} (hj : 1 ≤ j) :
    (⨆ J ∈ {J : Subgroup Q | InCalEi 1 T A J}, J) ≤ genEi j T Ω :=
  iSup₂_le fun _ hJ =>
    CFSG.LocalAnalysis.WeakClosure81.le_genEi_of_inCalEi hAΩ hAT ⟨hJ.1, hJ.2.trans hj⟩

omit [Finite Q] in
theorem FourElevenSetting.exists_conj_of_model_four {M : Type} [Group M] [Finite M]
    (e : ↥L ≃* M)
    (hconj : ∀ D D' : Subgroup M, CFSG.IsElementaryAbelian 2 D → Nat.card D = 4 →
      CFSG.IsElementaryAbelian 2 D' → Nat.card D' = 4 →
      ∃ y : M, D' = D.map (MulAut.conj y).toMonoidHom)
    {A₀ A : Subgroup Q} (hA₀L : A₀ ≤ L) (hAL : A ≤ L)
    (hA₀el : CFSG.IsElementaryAbelian 2 A₀) (hA₀4 : Nat.card A₀ = 4)
    (hAel : CFSG.IsElementaryAbelian 2 A) (hA4 : Nat.card A = 4) :
    ∃ gL : ↥L, A = A₀.map (MulAut.conj (gL : Q)).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D : Subgroup M := (A₀.subgroupOf L).map e.toMonoidHom
  let D' : Subgroup M := (A.subgroupOf L).map e.toMonoidHom
  have hDel : CFSG.IsElementaryAbelian 2 D := by
    have h1 : CFSG.IsElementaryAbelian 2 (A₀.subgroupOf L) := by
      have : CFSG.IsElementaryAbelian 2 A₀ := hA₀el
      exact CFSG.IsElementaryAbelian.subgroupOf hA₀L
    exact CFSG.IsElementaryAbelian.subgroup_map h1 e.toMonoidHom
  have hDcard : Nat.card D = 4 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀L).toEquiv).trans hA₀4
  have hD'el : CFSG.IsElementaryAbelian 2 D' := by
    have h1 : CFSG.IsElementaryAbelian 2 (A.subgroupOf L) := by
      have : CFSG.IsElementaryAbelian 2 A := hAel
      exact CFSG.IsElementaryAbelian.subgroupOf hAL
    exact CFSG.IsElementaryAbelian.subgroup_map h1 e.toMonoidHom
  have hD'card : Nat.card D' = 4 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv).trans hA4
  obtain ⟨y, hy⟩ := hconj D D' hDel hDcard hD'el hD'card
  refine ⟨e.symm y, ?_⟩
  exact map_conj_of_subgroupOf_conj hA₀L hAL
    (CFSG.GH74.Generic.BProg.B2.FixFourS3.map_conj_transport e hy)

theorem FourElevenSetting.mem_of_four (h : FourElevenSetting Q L p) {Ω : Set (Subgroup Q)}
    (hΩ : IsOmegaColl Ω) {A₀ A : Subgroup Q} (hA₀ : A₀ ∈ Ω) (hA₀L : A₀ ≤ L)
    (hA₀4 : Nat.card A₀ = 4) (hAL : A ≤ L) (hA : IsElemAbelian 2 A) (hA4 : Nat.card A = 4) :
    A ∈ Ω := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hA0el : CFSG.IsElementaryAbelian 2 A₀ :=
    (hΩ.elemAbelian A₀ hA₀).isElementaryAbelian
  have hAel : CFSG.IsElementaryAbelian 2 A := hA.isElementaryAbelian
  obtain ⟨gL, hgL⟩ : ∃ gL : ↥L, A = A₀.map (MulAut.conj (gL : Q)).toMonoidHom := by
    rcases h.isL3 with hPSL | hPSU
    · obtain ⟨K, _hKfield, _hKfin, hKcard, ⟨e⟩⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
          hPSL
      have hK2 : ringChar K ≠ 2 :=
        CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow h.prime h.ne_two hKcard
      exact FourElevenSetting.exists_conj_of_model_four e
        (fun D D' hD hDc hD' hD'c => by
          obtain ⟨s, hs⟩ :=
            CFSG.GH74.Generic.BProg.B2.FixFourS3.exists_conj_four_projectiveSL3
              hK2 hD hDc hD' hD'c
          exact ⟨LinearFlag.proj 3 K s, hs⟩)
        hA₀L hAL hA0el hA₀4 hAel hA4
    · have hPSU' : CFSG.Quasithin.IsPSU 3 p 1 ↥L :=
        CFSG.Blueprint.LieModel.statedClassicalModel hPSU (by decide)
      obtain ⟨F, _hFfield, _hFfin, hFcard, ⟨e⟩⟩ :=
        CFSG.Quasithin.E2P.Asc80.exists_equiv_psu3 hPSU'
      exact FourElevenSetting.exists_conj_of_model_four e
        (fun D D' hD hDc hD' hD'c => by
          obtain ⟨s, hs⟩ :=
            CFSG.GH74.Generic.BProg.B2.FixFourS3.exists_conj_four_statedSU3
              (p := p) (f := 1) (K := F) h.prime h.ne_two (by simpa using hFcard)
              hD hDc hD' hD'c
          exact ⟨QuotientGroup.mk s, hs⟩)
        hA₀L hAL hA0el hA₀4 hAel hA4
  have hconj : conjSubgroup A₀ ((gL : Q)⁻¹) = A := by
    rw [conjSubgroup, inv_inv]
    exact hgL.symm
  have hmem := hΩ.conj A₀ hA₀ ((gL : Q)⁻¹)
  rwa [hconj] at hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
