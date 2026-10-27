module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.K318

open Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {L : Type} [Group L] [Finite L]

theorem eq_top_of_isSolvable_quotient [Group.IsPerfect L] (N : Subgroup L) [N.Normal]
    (h : Group.IsSolvable (L ⧸ N)) : N = ⊤ := by
  by_contra hN
  obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hN)
  have : Nontrivial (L ⧸ N) := ⟨⟨(g : L ⧸ N), 1, fun h1 => hg ((QuotientGroup.eq_one_iff g).1 h1)⟩⟩
  exact Group.IsPerfect.not_isSolvable (L ⧸ N) h

theorem le_or_eq_top_of_normal [Group.IsPerfect L] {Y : Subgroup L} [Y.Normal]
    (hYs : Group.IsSolvable Y) (hs : IsSimpleGroup (L ⧸ Y)) (N : Subgroup L) [N.Normal] :
    N ≤ Y ∨ N = ⊤ := by
  haveI : (N.map (QuotientGroup.mk' Y)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Y)
  rcases hs.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Y)) with h | h
  · left
    intro x hx
    have hx' : QuotientGroup.mk' Y x ∈ N.map (QuotientGroup.mk' Y) := mem_map_of_mem _ hx
    rw [h, mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff x).1 hx'
  · right
    apply eq_top_of_isSolvable_quotient
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp Y.subtype) := by
      intro z
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
      have hg : QuotientGroup.mk' Y g ∈ N.map (QuotientGroup.mk' Y) := by
        rw [h]
        exact mem_top _
      obtain ⟨n, hn, hng⟩ := mem_map.1 hg
      have hy : n⁻¹ * g ∈ Y := QuotientGroup.eq.1 hng
      refine ⟨⟨n⁻¹ * g, hy⟩, ?_⟩
      show ((n⁻¹ * g : L) : L ⧸ N) = (g : L ⧸ N)
      rw [QuotientGroup.eq]
      have e : (n⁻¹ * g)⁻¹ * g = g⁻¹ * n * g⁻¹⁻¹ := by group
      rw [e]
      exact Normal.conj_mem inferInstance n hn g⁻¹
    haveI := hYs
    exact solvable_of_surjective hsurj

theorem exists_pCore_not_le_centralizer {Y : Subgroup L} (hYs : Group.IsSolvable Y)
    (hcent : centralizer (Y : Set L) ≤ Y) (hY : Y ≠ ⊤) :
    ∃ q ∈ (Nat.card Y).primeFactors, ¬ (⊤ : Subgroup L) ≤
      centralizer (((CFSG.pCore q Y).map Y.subtype : Subgroup L) : Set L) := by
  by_contra hall
  push Not at hall
  apply hY
  have hF : (⊤ : Subgroup L) ≤
      centralizer (((CFSG.fittingSubgroup Y).map Y.subtype : Subgroup L) : Set L) := by
    rw [CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
    exact CFSG.subgroup_le_centralizer_iSup_of_le_centralizer _ (fun q => hall q.1.1 q.1.2)
  have hYF : ∀ y : Y, y ∈ CFSG.fittingSubgroup Y := by
    intro y
    apply CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hYs
    rw [mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    exact mem_centralizer_iff.1 (hF (mem_top (y : L))) (f : L) (mem_map_of_mem _ hf)
  rw [eq_top_iff]
  intro g _
  apply hcent
  rw [mem_centralizer_iff]
  intro y hy
  exact mem_centralizer_iff.1 (hF (mem_top g)) y (mem_map.2 ⟨⟨y, hy⟩, hYF ⟨y, hy⟩, rfl⟩)

theorem le_centralizer_of_isPGroup_range [Group.IsPerfect L] {q : ℕ} [Fact q.Prime]
    {Q : Subgroup L} [Q.Normal]
    (h : IsPGroup q (MulAut.conjNormal (H := Q) : L →* MulAut Q).range) :
    (⊤ : Subgroup L) ≤ centralizer (Q : Set L) := by
  set c : L →* MulAut Q := MulAut.conjNormal with hc
  have : Group.IsPerfect c.range := Group.IsPerfect.range c
  have hc1 : c.range = ⊥ := by
    by_contra hne
    have : Nontrivial c.range := (nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isNilpotent c.range h.isNilpotent
  intro g _
  rw [mem_centralizer_iff]
  intro x hx
  have hcg : c g = 1 := by
    have hmem : c g ∈ c.range := ⟨g, rfl⟩
    rw [hc1, mem_bot] at hmem
    exact hmem
  have h2 := congrArg (fun σ : MulAut Q => ((σ ⟨x, hx⟩ : Q) : L)) hcg
  simp only [hc, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc x * g = g * x * g⁻¹ * g := by rw [h2]
    _ = g * x := by group

theorem pRank_le_of_le {q : ℕ} (hq : 1 < q) {Q Y : Subgroup L} (hQY : Q ≤ Y) (D : Subgroup Q) :
    CFSG.pRank q D ≤ CFSG.Open.pRank q Y := by
  rw [pRank_eq_open_pRank_top]
  have hf : Function.Injective (Q.subtype.comp D.subtype) :=
    Q.subtype_injective.comp D.subtype_injective
  refine (pRank_le_map hq _ hf ⊤).trans (pRank_mono hq ?_)
  rintro _ ⟨d, -, rfl⟩
  exact hQY (d : Q).2

theorem le_four_of_card_frattini {q : ℕ} [Fact q.Prime] {D : Type*} [Group D] [Finite D]
    (hD : IsPGroup q D) (hexp : ∀ x : D, x ^ q = 1) (hclass : commutator D ≤ center D)
    (hrank : CFSG.pRank q D ≤ 3) {k : ℕ} (hk : Nat.card (D ⧸ frattini D) = q ^ k) : k ≤ 4 := by
  have hΦ : frattini D = commutator D := frattini_eq_commutator hD hexp
  rw [hΦ] at hk
  have h1 := (quotient_commutator_rank Fact.out hexp hk).2
  have h2 := (class_two_small_rank_order_bounds hD hexp hclass).2.2 hrank
  omega

theorem exists_linear_section [Group.IsPerfect L] (Y : Subgroup L) [Y.Normal]
    (hYs : Group.IsSolvable Y) (hYodd : Odd (Nat.card Y))
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q Y ≤ 3)
    (hcent : centralizer (Y : Set L) ≤ Y) (hs : IsSimpleGroup (L ⧸ Y)) :
    ∃ q : ℕ, q.Prime ∧ q ∣ Nat.card Y ∧ ∃ d : ℕ, d ≤ 4 ∧
      ∃ φ : L →* GL (Fin d) (ZMod q), φ.ker ≤ Y := by
  classical
  have hYtop : Y ≠ ⊤ := by
    intro hY
    obtain ⟨a, b, hab⟩ := (IsSimpleGroup.toNontrivial : Nontrivial (L ⧸ Y)).exists_pair_ne
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [QuotientGroup.eq, hY]
    exact mem_top _
  obtain ⟨q, hqY, hnc⟩ := exists_pCore_not_le_centralizer hYs hcent hYtop
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqY
  have hqdvd : q ∣ Nat.card Y := Nat.dvd_of_mem_primeFactors hqY
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hYodd) (even_iff_two_dvd.2 hqdvd)
  haveI : Fact q.Prime := ⟨hq⟩
  let Q : Subgroup L := (CFSG.pCore q Y).map Y.subtype
  haveI : Q.Normal := ConjAct.normal_of_characteristic_of_normal
  have hQp : IsPGroup q Q := (CFSG.pCore_isPGroup (p := q) (G := Y)).map Y.subtype
  have hQY : Q ≤ Y := map_subtype_le _
  have hQnt : Nontrivial Q := by
    rw [nontrivial_iff_ne_bot]
    intro hbot
    apply hnc
    intro g _
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : x ∈ Q := hx
    rw [hbot, mem_bot] at hx'
    rw [hx', one_mul, mul_one]
  obtain ⟨D, hDc, -, hDp, hDZ, -, hker⟩ := supercritical_witness hq2 hQp
  set α : L →* MulAut (D ⧸ frattini D) :=
    (frattiniAction D).comp (MulAut.conjNormal (H := Q)) with hα
  have hαY : α.ker ≤ Y := by
    rcases le_or_eq_top_of_normal hYs hs α.ker with h | h
    · exact h
    exfalso
    apply hnc
    apply le_centralizer_of_isPGroup_range (q := q)
    refine hker.to_le ?_
    rintro _ ⟨g, rfl⟩
    have hg : α g = 1 := MonoidHom.mem_ker.1 (h ▸ mem_top g)
    exact MonoidHom.mem_ker.2 hg
  have hDq : IsPGroup q D := hQp.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDq
  obtain ⟨k, hk⟩ := (hDq.to_quotient (frattini D)).exists_card_eq
  have hexp : ∀ x : D, x ^ q = 1 := fun x => Subtype.ext (by simpa using hDp x x.2)
  have hclass : commutator D ≤ center D := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    rw [mem_center_iff]
    intro z
    have hab : ⁅(a : Q), (b : Q)⁆ ∈ centralizer (D : Set Q) :=
      (hDZ (commutator_mem_commutator a.2 (mem_top (b : Q)))).2
    apply Subtype.ext
    have h1 := mem_centralizer_iff.1 hab (z : Q) z.2
    simpa [commutatorElement_def] using h1
  have hk4 : k ≤ 4 :=
    le_four_of_card_frattini hDq hexp hclass
      ((pRank_le_of_le hq.one_lt hQY D).trans (hrank q hq hq2)) hk
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hk
  refine ⟨q, hq, hqdvd, k, hk4, (elemAutEquivGL e).toMonoidHom.comp α, ?_⟩
  intro g hg
  apply hαY
  rw [MonoidHom.mem_ker] at hg ⊢
  apply (elemAutEquivGL e).injective
  rw [map_one]
  exact hg

end CFSG.LocalAnalysis.UniquenessCase.UC6.K318
