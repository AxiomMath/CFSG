module

public import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofFactors
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
import CFSG.GroupTheory.LocalCores.MinimalNormal
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof

open Subgroup CFSG.Blueprint


theorem isSolvable_of_le_closure_pow_three {Y : Type} [Group Y] [Finite Y]
    (hK : CFSG.IsKGroup Y)
    (h5 : ∀ (V : Subgroup Y) (M : Subgroup V) [M.Normal], CFSG.layer (V ⧸ M) = ⊤ →
      CFSG.Open.pRank 5 (⊤ : Subgroup (V ⧸ M)) ≤ 2)
    {D U : Subgroup Y} [hUn : U.Normal] (hDp : Group.IsPerfect D)
    (hU3 : ¬ 3 ∣ Nat.card U)
    (hUO : U ≤ closure {x | x ∈ D ∧ ∃ k : ℕ, x ^ 3 ^ k = 1}) : Group.IsSolvable U := by
  classical
  by_contra hns
  obtain ⟨V, ⟨hVn, hVU, hVs⟩, hVmin⟩ :=
    (Set.toFinite {W : Subgroup Y | W.Normal ∧ W ≤ U ∧ ¬ Group.IsSolvable W}).exists_minimal
      ⟨U, hUn, le_rfl, hns⟩
  have hbelow : ∀ W : Subgroup Y, W.Normal → W < V → Group.IsSolvable W := by
    intro W hW hlt
    by_contra h
    exact hlt.not_ge (hVmin ⟨hW, hlt.le.trans hVU, h⟩ hlt.le)
  have hV1 : V ≠ ⊥ := by
    rintro rfl
    exact hVs inferInstance
  obtain ⟨M, ⟨hMn, hMV⟩, hMmax⟩ :=
    (Set.toFinite {W : Subgroup Y | W.Normal ∧ W < V}).exists_maximal
      ⟨⊥, inferInstance, bot_lt_iff_ne_bot.mpr hV1⟩
  have hMs : Group.IsSolvable M := hbelow M hMn hMV
  have : M.Normal := hMn
  have hMV' : M ≤ V := hMV.le
  set π : Y →* Y ⧸ M := QuotientGroup.mk' M with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective M
  have hπker : π.ker = M := QuotientGroup.ker_mk' M
  set Vb : Subgroup (Y ⧸ M) := V.map π with hVb
  have hVbn : Vb.Normal := hVn.map π hπs
  have hcomap : Vb.comap π = V := by
    rw [hVb, Subgroup.comap_map_eq, hπker, sup_eq_left.mpr hMV']
  have hVb1 : Vb ≠ ⊥ := by
    intro h
    apply hMV.not_ge
    intro v hv
    have h1 : π v ∈ Vb := mem_map_of_mem π hv
    rw [h, mem_bot, ← MonoidHom.mem_ker, hπker] at h1
    exact h1
  have hVbmin : ∀ W : Subgroup (Y ⧸ M), W.Normal → W ≤ Vb → W = ⊥ ∨ W = Vb := by
    intro W hW hWV
    have hMW : M ≤ W.comap π := fun m hm => by
      have h1 : π m = 1 := MonoidHom.mem_ker.mp (by rw [hπker]; exact hm)
      rw [mem_comap, h1]
      exact one_mem W
    have hWV' : W.comap π ≤ V := hcomap ▸ comap_mono hWV
    rcases eq_or_lt_of_le hWV' with h | h
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective hπs W, h]
    · left
      have h1 : W.comap π ≤ M := hMmax ⟨hW.comap π, h⟩ hMW
      rw [← Subgroup.map_comap_eq_self_of_surjective hπs W, Subgroup.map_eq_bot_iff, hπker]
      exact h1
  have hVbs : ¬ Group.IsSolvable Vb := by
    intro hs
    apply hVs
    let ψ : V →* Vb := (π.domRestrict V).codRestrict Vb fun v => mem_map_of_mem π v.2
    have hMs' : Group.IsSolvable (M.subgroupOf V) :=
      Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hMV').toMonoidHom)
        (subgroupOfEquivOfLe hMV').injective
    refine Group.isSolvable_of_ker_le_range (M.subgroupOf V).subtype ψ ?_
    intro v hv
    rw [range_subtype, mem_subgroupOf, ← hπker, MonoidHom.mem_ker]
    exact congrArg Subtype.val ((MonoidHom.mem_ker).mp hv)
  obtain ⟨r, S, -, hSV, hSs, hSconj, hSn, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hVbn hVb1 hVbmin
  have hSnab : ∀ i, ∃ a b : S i, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    obtain ⟨i₀, hi₀⟩ := hab
    have hall : ∀ j, ∀ a b : S j, a * b = b * a := by
      intro j a b
      obtain ⟨g, hg⟩ := hSconj i₀ j
      have ha : (a : Y ⧸ M) ∈ conjugate (S i₀) g := hg ▸ a.2
      have hb : (b : Y ⧸ M) ∈ conjugate (S i₀) g := hg ▸ b.2
      obtain ⟨a', ha', ha''⟩ := ha
      obtain ⟨b', hb', hb''⟩ := hb
      apply Subtype.ext
      have h1 := congrArg Subtype.val (hi₀ ⟨a', ha'⟩ ⟨b', hb'⟩)
      simp only [Subgroup.coe_mul] at h1
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha'', ← hb'', ← map_mul, ← map_mul, h1]
    apply hVbs
    refine Group.isSolvable_of_comm fun x y => ?_
    apply e.symm.injective
    rw [map_mul, map_mul]
    funext j
    exact hall j _ _
  have hP : IsSimpleProduct Vb S := isSimpleProduct_of_mulEquiv hSV hSs hSnab hSn e he
  have hS3 : ∀ i, ¬ 3 ∣ Nat.card (S i) := by
    intro i h3
    apply hU3
    exact h3.trans ((Subgroup.card_dvd_of_le (hSV i)).trans
      ((Subgroup.card_map_dvd V π).trans (Subgroup.card_dvd_of_le hVU)))
  have hSz : ∀ i, ∃ q f : ℕ, SuzukiModel (S i) q f := by
    intro i
    have := hSs i
    have hsurj : Function.Surjective
        ((π.domRestrict ((S i).comap π)).codRestrict (S i) fun x => x.2) := by
      intro s
      obtain ⟨y, hy⟩ := hπs (s : Y ⧸ M)
      refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
      rw [mem_comap, hy]
      exact s.2
    have hcat := CFSG.ComponentClassification.CatalogueKProper.simple_quotient_of_isKGroup hK
      ((S i).comap π) (S i) _ hsurj
    obtain ⟨f, hf⟩ :=
      KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd (S i) (hSnab i) hcat (hS3 i)
    exact ⟨2, f, hf⟩
  have hr : r ≤ 2 := by
    let ψ : V →* Y ⧸ M := π.domRestrict V
    have hker : ψ.ker = M.subgroupOf V := by
      rw [MonoidHom.ker_domRestrict, hπker]
    have hrange : ψ.range = Vb := MonoidHom.domRestrict_range V π
    let e₁ : V ⧸ M.subgroupOf V ≃* ((i : Fin r) → S i) :=
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange ψ)).trans
        ((MulEquiv.subgroupCongr hrange).trans e.symm)
    have : ∀ i, IsSimpleGroup (S i) := hSs
    have hlayer : CFSG.layer (V ⧸ M.subgroupOf V) = ⊤ :=
      CFSG.LocalCores.layer_eq_top_of_mulEquiv_pi hSnab e₁
    have h1 := h5 V (M.subgroupOf V) hlayer
    have h2 := le_pRank_five (S := fun i => (S i : Type)) hSz
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e₁] at h2
    exact h2.trans h1
  have hfix : ∀ (d : D) (i : Fin r),
      (S i).map (MulAut.conj ((π.comp D.subtype) d)).toMonoidHom = S i :=
    fun d i => hP.map_conj_eq_of_isPerfect hVbn hr hDp (π.comp D.subtype) d i
  have hcent : ∀ x ∈ D, (∃ k : ℕ, x ^ 3 ^ k = 1) → ∀ v ∈ Vb, π x * v = v * π x := by
    rintro x hxD ⟨k, hk⟩ v hv
    have hk' : (⟨x, hxD⟩ : D) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    exact hP.commute_of_pow_three_pow hSz hDp (π.comp D.subtype) hfix hk' v hv
  have hOc : (closure {x | x ∈ D ∧ ∃ k : ℕ, x ^ 3 ^ k = 1}).map π ≤
      centralizer (Vb : Set (Y ⧸ M)) := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, ⟨hxD, hx3⟩, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro v hv
    exact (hcent x hxD hx3 v hv).symm
  apply hVbs
  refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
  have hb' : (b : Y ⧸ M) ∈ (closure {x | x ∈ D ∧ ∃ k : ℕ, x ^ 3 ^ k = 1}).map π :=
    map_mono (hVU.trans hUO) b.2
  exact mem_centralizer_iff.mp (hOc hb') a a.2

end CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof
