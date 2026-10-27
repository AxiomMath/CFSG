module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93a
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABDA1A
public import CFSG.GroupTheory.PElementSubgroup
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

structure R920Cfg (D : Data G) (L D₃ A : Subgroup G) : Prop where
  mem : L ∈ calC D.M
  le_M : L ≤ D.M
  isL2 : IsL2 (Bar2 L) 3
  ne_bot : pCoreOf 2 L ≠ ⊥
  D₃_le : D₃ ≤ L
  D₃_card : Nat.card D₃ = 3
  D₃_mem : D₃ ∈ uniqueSet D.M
  A_le : A ≤ L
  A_card : Nat.card A = 7
  A_mem : A ∈ uniqueSet D.M

namespace R920Cfg

variable {D : Data G} {L D₃ A : Subgroup G}

private theorem r920cfg_mem_uniqueSet_of_card_eq_prime (c : R920Cfg D L D₃ A) {p : ℕ}
    (hp : p.Prime) {X E : Subgroup G} (hXL : X ≤ L) (hXc : Nat.card X = p)
    (hXmem : X ∈ uniqueSet D.M) (hcyc : ∀ T : Sylow p ↥L, IsCyclic T) (hEL : E ≤ L)
    (hE : Nat.card E = p) : E ∈ uniqueSet D.M := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := CFSG.AGLEmbeddingD2.exists_eq_map_conj_of_isCyclic (J := ↥L) (p := p)
    hcyc (Y₀ := X.subgroupOf L) (Y₁ := E.subgroupOf L)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv, hXc])
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE])
  have heq : E = X.map (MulAut.conj (j : G)).toMonoidHom := by
    ext y
    constructor
    · intro hy
      have hy' : (⟨y, hEL hy⟩ : ↥L) ∈ E.subgroupOf L := hy
      rw [hj, Subgroup.mem_map] at hy'
      obtain ⟨d, hd, hdy⟩ := hy'
      exact Subgroup.mem_map.2 ⟨d, hd,
        by simpa [MulAut.conj_apply] using congrArg Subtype.val hdy⟩
    · intro hy
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hy
      have hd' : (⟨d, hXL hd⟩ : ↥L) ∈ X.subgroupOf L := hd
      have := Subgroup.mem_map_of_mem (MulAut.conj j).toMonoidHom hd'
      rw [← hj] at this
      simpa [MulAut.conj_apply] using Subgroup.mem_subgroupOf.1 this
  rw [heq]
  exact conj_mem_uniqueSet hXmem (c.le_M j.2)

theorem opp_eq (c : R920Cfg D L D₃ A) : Opp 3 L = L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup ↥L := CFSG.pCore 2 ↥L
  haveI hKnorm : K.Normal := CFSG.pCore_normal
  haveI hsimple : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) c.isL2
  set N' : Subgroup ↥L := (Opp 3 L).subgroupOf L with hN'def
  haveI hN'norm : N'.Normal := by rw [hN'def]; exact F09.normal_opp_subgroupOf 3 L
  have hπsurj : Function.Surjective (QuotientGroup.mk' K) := QuotientGroup.mk'_surjective K
  have hmapnorm : (N'.map (QuotientGroup.mk' K)).Normal := hN'norm.map _ hπsurj
  haveI := hmapnorm
  rcases hsimple.eq_bot_or_eq_top_of_normal (N'.map (QuotientGroup.mk' K)) with hbot | htop
  ·
    exfalso
    have hN'leK : N' ≤ K := by
      intro x hx
      have h1 : (QuotientGroup.mk' K) x = 1 := by
        have h2 : (QuotientGroup.mk' K) x ∈ N'.map (QuotientGroup.mk' K) :=
          Subgroup.mem_map_of_mem _ hx
        rw [hbot] at h2
        simpa using h2
      exact (QuotientGroup.eq_one_iff x).mp h1
    have hD3p : IsPGroup 3 D₃ := IsPGroup.of_card (n := 1) (by rw [c.D₃_card, pow_one])
    have hD3leOpp : D₃ ≤ Opp 3 L :=
      CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_three hD3p c.D₃_le
    have hD3sub : D₃.subgroupOf L ≤ N' :=
      Subgroup.subgroupOf_mono L hD3leOpp
    have h3dvd : 3 ∣ Nat.card N' := by
      have hc : Nat.card (D₃.subgroupOf L) = 3 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.D₃_le).toEquiv, c.D₃_card]
      rw [← hc]
      exact Subgroup.card_dvd_of_le hD3sub
    have hKpg : IsPGroup 2 K := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hKpg
    have h3dvdK : 3 ∣ Nat.card K := h3dvd.trans (Subgroup.card_dvd_of_le hN'leK)
    have h32 : 3 ∣ 2 ^ k := hk ▸ h3dvdK
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h32) (by norm_num)
  ·
    have hsup : N' ⊔ K = ⊤ := by
      have htop' : N'.map (QuotientGroup.mk' K) =
          (⊤ : Subgroup ↥L).map (QuotientGroup.mk' K) := by
        rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
        exact htop
      have h1 : (⊤ : Subgroup ↥L) = N' ⊔ (QuotientGroup.mk' K).ker :=
        s16h_top_eq_sup_ker_of_map_eq (QuotientGroup.mk' K) N' htop'
      rw [QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hsurj : Function.Surjective ((QuotientGroup.mk' N').comp K.subtype) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N' y
      have hx : x ∈ N' ⊔ K := by rw [hsup]; trivial
      obtain ⟨n, hn, k, hk, hnk⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := N') (t := K)).1 hx
      refine ⟨⟨k, hk⟩, ?_⟩
      show (QuotientGroup.mk' N') k = (QuotientGroup.mk' N') x
      rw [← hnk, map_mul,
        show (QuotientGroup.mk' N') n = 1 from (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    have hKpg : IsPGroup 2 K := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hKpg
    have hdiv : Nat.card (↥L ⧸ N') ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.card_dvd_of_surjective hsurj
    have hP : IsPGroup 2 (↥L ⧸ N') := isPGroup_iff_card_dvd_pow.mpr ⟨k, hdiv⟩
    haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr c.mem.2.1
    have hNil : Group.IsNilpotent (↥L ⧸ N') := IsPGroup.isNilpotent hP
    have hsub : Subsingleton (↥L ⧸ N') := by
      by_contra h
      haveI : Nontrivial (↥L ⧸ N') := not_subsingleton_iff_nontrivial.mp h
      exact Group.IsPerfect.not_isNilpotent (↥L ⧸ N') hNil
    have hNtop : N' = ⊤ := QuotientGroup.subsingleton_iff.mp hsub
    have hNtop2 : (Opp 3 L).subgroupOf L = ⊤ := by rw [← hN'def]; exact hNtop
    exact le_antisymm (F09.opp_le_self 3 L) (Subgroup.subgroupOf_eq_top.mp hNtop2)

theorem isCyclic_sylow_three (c : R920Cfg D L D₃ A) (T : Sylow 3 ↥L) :
    IsCyclic ↥(T : Subgroup ↥L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : CFSG.Open.pRank 3 L ≤ 1 := by
    rw [← pRank_bar2_eq_of_odd (Y := L) Nat.prime_three (by norm_num)]
    exact pRank_le_one_of_isL2_or_isSz (Or.inl c.isL2) Nat.prime_three (by norm_num)
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L]
    exact h3
  exact CFSG.LocalAnalysis.UniquenessCase.UCK.K31.isCyclic_of_pRank_le_one Nat.prime_three
    (by norm_num) T.isPGroup' ((CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num)
      le_top).trans htop)

theorem mem_uniqueSet_of_card_three (c : R920Cfg D L D₃ A) {E : Subgroup G} (hEL : E ≤ L)
    (hE : Nat.card E = 3) : E ∈ uniqueSet D.M :=
  r920cfg_mem_uniqueSet_of_card_eq_prime c Nat.prime_three c.D₃_le c.D₃_card c.D₃_mem
    (fun T => c.isCyclic_sylow_three T) hEL hE

theorem mem_uniqueSet_of_card_seven (c : R920Cfg D L D₃ A) {E : Subgroup G} (hEL : E ≤ L)
    (hE : Nat.card E = 7) : E ∈ uniqueSet D.M := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  refine r920cfg_mem_uniqueSet_of_card_eq_prime c Nat.prime_seven c.A_le c.A_card c.A_mem
    ?_ hEL hE
  intro T
  have h7 : CFSG.Open.pRank 7 L ≤ 1 := by
    rw [← pRank_bar2_eq_of_odd (Y := L) Nat.prime_seven (by norm_num)]
    exact pRank_le_one_of_isL2_or_isSz (Or.inl c.isL2) Nat.prime_seven (by norm_num)
  have htop : CFSG.Open.pRank 7 (⊤ : Subgroup ↥L) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 7) L]
    exact h7
  exact CFSG.LocalAnalysis.UniquenessCase.UCK.K31.isCyclic_of_pRank_le_one Nat.prime_seven
    (by norm_num) T.isPGroup' ((CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 7 (by norm_num)
      le_top).trans htop)

theorem pRank_le_one_of_maxTwoLocal (c : R920Cfg D L D₃ A) (h61 : UC6.R6_1 D) (h3 : 3 ∈ D.sig)
    {N : Subgroup G} (hN : rankThreeIsMaxTwoLocal N) (hLN : L ≤ N) (hNM : N ≠ D.M) :
    CFSG.Open.pRank 3 N ≤ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD3N : D₃ ≤ N := c.D₃_le.trans hLN
  have hD3card : Nat.card (D₃.subgroupOf N) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD3N).toEquiv, c.D₃_card]
  have hD3p : IsPGroup 3 (D₃.subgroupOf N) :=
    IsPGroup.of_card (n := 1) (by rw [hD3card, pow_one])
  obtain ⟨Q, hDQ⟩ := hD3p.exists_le_sylow
  have hQcyc : IsCyclic ↥(Q : Subgroup ↥N) := by
    let Q' : Subgroup G := (Q : Subgroup ↥N).map N.subtype
    have hQ'pg : IsPGroup 3 Q' := Q.isPGroup'.map N.subtype
    have hD3Q' : D₃ ≤ Q' := by
      intro d hd
      exact Subgroup.mem_map.2 ⟨⟨d, hD3N hd⟩, hDQ (Subgroup.mem_subgroupOf.2 hd), rfl⟩
    have hQ'M : Q' ≤ D.M :=
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup
        D.maxLocal c.D₃_mem hD3Q' hQ'pg
    have hQ'cyc : IsCyclic Q' := by
      by_contra hnc
      have huniq : calMOf Q' = {D.M} := h61 3 h3 Q' hQ'M hQ'pg hnc
      have hNmem : N ∈ calMOf Q' := ⟨hN, Subgroup.map_subtype_le _⟩
      have hNDM : N = D.M := by
        have h1 : N ∈ ({D.M} : Set (Subgroup G)) := by rw [← huniq]; exact hNmem
        simpa using h1
      exact hNM hNDM
    exact (MulEquiv.isCyclic ((Q : Subgroup ↥N).equivMapOfInjective N.subtype
      N.subtype_injective)).mpr hQ'cyc
  refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) ?_
  intro E hEN hEab
  have hEp : IsPGroup 3 (E.subgroupOf N) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using hEab.2 ((x : ↥(E.subgroupOf N)) : G) (Subgroup.mem_subgroupOf.mp x.2)
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (↥N) Q P
  have hPmap : (P : Subgroup ↥N) = (Q : Subgroup ↥N).map (MulAut.conj n).toMonoidHom := by
    rw [← hn, Sylow.coe_subgroup_smul]; rfl
  have hPcyc : IsCyclic ↥(P : Subgroup ↥N) := by
    rw [hPmap]
    exact (MulEquiv.isCyclic ((Q : Subgroup ↥N).equivMapOfInjective _
      (MulAut.conj n).injective)).mp hQcyc
  haveI : IsCyclic ↥(P : Subgroup ↥N) := hPcyc
  haveI hEsub : IsCyclic ↥(E.subgroupOf N) := Subgroup.isCyclic_of_le hEP
  have hEcyc : IsCyclic ↥E :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hEN)).mp hEsub
  haveI : IsCyclic ↥E := hEcyc
  have hexp : Monoid.exponent ↥E ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun x => Subtype.ext (hEab.2 (x : G) x.2))
  have hcard : Nat.card ↥E ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    exact hexp
  simpa using Nat.le_of_dvd (by norm_num) hcard

end R920Cfg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
