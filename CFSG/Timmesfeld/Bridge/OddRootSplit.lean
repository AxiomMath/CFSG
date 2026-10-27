module

public import CFSG.Timmesfeld.Bridge.OddRootChief
import CFSG.Timmesfeld.Bridge.SL2FactsCoord
import CFSG.Timmesfeld.Bridge.SL2FactsComplement

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki CFSG.Timmesfeld.Bridge.RootClosure
open scoped commutatorElement

variable {H : Type} [Group H]

theorem isOddTransp_quotSetN {F : Set H} (hF : IsOddTransp F) (M : Subgroup H) [M.Normal] :
    IsOddTransp (quotSetN F M) := by
  have hdvd : ∀ g : H, orderOf (g : H ⧸ M) ∣ orderOf g := fun g =>
    orderOf_map_dvd (QuotientGroup.mk' M) g
  refine ⟨?_, ?_⟩
  · rintro _ ⟨c, ⟨hc, hcM⟩, rfl⟩
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ← hF.1 c hc, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h1
      exact hcM ((QuotientGroup.eq_one_iff c).1 h1)
  · rintro _ ⟨c, ⟨hc, -⟩, rfl⟩ _ ⟨c', ⟨hc', -⟩, rfl⟩
    rw [← QuotientGroup.mk_mul]
    rcases hF.2 c hc c' hc' with h | ho
    · exact Or.inl ((hdvd (c * c')).trans h)
    · exact Or.inr (ho.of_dvd_nat (hdvd (c * c')))

theorem isNormalSet_quotSetN {F : Set H} (hF : IsNormalSet F) (M : Subgroup H) [M.Normal] :
    IsNormalSet (quotSetN F M) := by
  rintro k _ ⟨c, ⟨hc, hcM⟩, rfl⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
  refine ⟨g * c * g⁻¹, ⟨hF g c hc, ?_⟩, by simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
  intro hconj
  apply hcM
  have h1 := (inferInstance : M.Normal).conj_mem (g * c * g⁻¹) hconj g⁻¹
  convert h1 using 1
  group

private theorem a_not_mem_of_isBender {Y : Type} [Group Y] [Finite Y] {a b y : Y}
    (hcb : IsConj a b) (hcy : IsConj a y) (hgen : Subgroup.closure {y, a, b} = ⊤)
    (N : Subgroup Y) [N.Normal] {n : ℕ} (hn : 2 ≤ n) (e : Y ⧸ N ≃* PSL2Model n) :
    a ∉ N := by
  intro haN'
  have hconjN : ∀ g, IsConj a g → g ∈ N := fun g hg => by
    obtain ⟨k, rfl⟩ := isConj_iff.1 hg
    exact (inferInstance : N.Normal).conj_mem a haN' k
  have htop : N = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact hconjN _ hcy
    · exact haN'
    · exact hconjN _ hcb
  obtain ⟨u, w, huw⟩ := IsBenderGroup.exists_not_commute
    (IsBenderGroup.isPSL2 n hn e : IsBenderGroup (Y ⧸ N))
  apply huw
  obtain ⟨u₀, rfl⟩ := QuotientGroup.mk_surjective u
  have hu : (u₀ : Y ⧸ N) = 1 :=
    (QuotientGroup.eq_one_iff u₀).2 (htop ▸ Subgroup.mem_top u₀)
  rw [hu]
  exact Commute.one_left _

private theorem minimal_normal_map {Y : Type} [Group Y] {M N : Subgroup Y} [M.Normal]
    [N.Normal] (hMN : M ≤ N)
    (hmax : ∀ W : Subgroup Y, W.Normal → W ≤ N → M ≤ W → W = M ∨ W = N)
    {W : Subgroup (Y ⧸ M)} (hWn : W.Normal) (hWV : W ≤ N.map (QuotientGroup.mk' M)) :
    W = ⊥ ∨ W = N.map (QuotientGroup.mk' M) := by
  let ι := QuotientGroup.mk' M
  have hcomap : (N.map ι).comap ι = N := by
    rw [Subgroup.comap_map_eq, show ι.ker = M from QuotientGroup.ker_mk' M,
      sup_eq_left.2 hMN]
  have hMW : M ≤ W.comap ι := by
    intro m hm
    show ι m ∈ W
    rw [show ι m = 1 from (QuotientGroup.eq_one_iff m).2 hm]
    exact W.one_mem
  have hWN : W.comap ι ≤ N := by
    rw [← hcomap]
    exact Subgroup.comap_mono hWV
  by_cases hWeq : W.comap ι = N
  · right
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) W, hWeq]
  · left
    rcases hmax (W.comap ι) (hWn.comap ι) hWN hMW with h | h
    · rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) W, h,
        Subgroup.map_eq_bot_iff]
      simpa [ι] using QuotientGroup.ker_mk' M
    · exact absurd h hWeq

theorem eq_bot_of_quotient_psl2 {Y : Type} [Group Y] [Finite Y]
    {D : Set Y} (hD : IsOddTransp D) (hN : IsNormalSet D) {a b y : Y} (ha : a ∈ D)
    (hb : b ∈ D) (hab : a * b ∈ D) (hy : y ∈ D) (hc : Commute a b)
    (hcb : IsConj a b) (hcab : IsConj a (a * b)) (hcy : IsConj a y)
    (hgen : Subgroup.closure {y, a, b} = ⊤) (N : Subgroup Y) [N.Normal] (hN2 : IsPGroup 2 N)
    {n : ℕ} (hn : 2 ≤ n) (e : Y ⧸ N ≃* PSL2Model n) : N = ⊥ := by
  by_contra hNne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haN : a ∉ N := a_not_mem_of_isBender hcb hcy hgen N hn e
  have hnotN : ∀ g, IsConj a g → g ∉ N := by
    intro g hg hgN
    obtain ⟨k, rfl⟩ := isConj_iff.1 hg
    apply haN
    have h' := (inferInstance : N.Normal).conj_mem _ hgN k⁻¹
    convert h' using 1
    group
  have : Finite (Subgroup Y) := Finite.of_injective (fun M : Subgroup Y => (M : Set Y))
    SetLike.coe_injective
  obtain ⟨M, -, hMax⟩ := Finite.exists_le_maximal (α := Subgroup Y)
    (p := fun M => M.Normal ∧ M < N) (a := ⊥) ⟨inferInstance, bot_lt_iff_ne_bot.2 hNne⟩
  have hMn : M.Normal := hMax.prop.1
  have hMN : M < N := hMax.prop.2
  letI : M.Normal := hMn
  set ι := QuotientGroup.mk' M with hι
  set V : Subgroup (Y ⧸ M) := N.map ι with hV
  have hVn : V.Normal := (inferInstance : N.Normal).map ι (QuotientGroup.mk'_surjective M)
  haveI : V.Normal := hVn
  have hmax : ∀ W : Subgroup Y, W.Normal → W ≤ N → M ≤ W → W = M ∨ W = N := by
    intro W hWn hWN hMW
    by_cases hWeq : W = N
    · exact Or.inr hWeq
    · exact Or.inl (le_antisymm (hMax.le_of_ge ⟨hWn, lt_of_le_of_ne hWN hWeq⟩ hMW) hMW)
  have hnotM : ∀ g, g ∉ N → g ∉ M := fun g hg hgM => hg (hMN.le hgM)
  have hmemQ : ∀ g ∈ D, g ∉ N → (g : Y ⧸ M) ∈ quotSetN D M := fun g hg hgN =>
    ⟨g, ⟨hg, hnotM g hgN⟩, rfl⟩
  have hOdd : OddRootChief (quotSetN D M) V (y : Y ⧸ M) (a : Y ⧸ M) (b : Y ⧸ M) n := by
    refine
      { oddT := isOddTransp_quotSetN hD M
        normal := isNormalSet_quotSetN hN M
        x_mem := hmemQ y hy (hnotN y hcy)
        a_mem := hmemQ a ha haN
        b_mem := hmemQ b hb (hnotN b hcb)
        ab_mem := ?_
        comm := hc.map (QuotientGroup.mk' M)
        conj_b := (QuotientGroup.mk' M).map_isConj hcb
        conj_ab := ?_
        conj_x := (QuotientGroup.mk' M).map_isConj hcy
        gen := ?_
        two := hN2.map ι
        ne_bot := ?_
        min := fun W hWn hWV => minimal_normal_map hMN.le hmax hWn hWV
        two_le := hn
        iso := ⟨(QuotientGroup.quotientQuotientEquivQuotient M N hMN.le).trans e⟩ }
    · rw [← QuotientGroup.mk_mul]
      exact hmemQ _ hab (hnotN _ hcab)
    · rw [← QuotientGroup.mk_mul]
      exact (QuotientGroup.mk' M).map_isConj hcab
    · have h' := congrArg (Subgroup.map ι) hgen
      rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective M)] at h'
      rw [← h']
      simp only [Set.image_insert_eq, Set.image_singleton, hι, QuotientGroup.mk'_apply]
    · intro h0
      rw [hV, Subgroup.map_eq_bot_iff, hι, QuotientGroup.ker_mk'] at h0
      exact lt_irrefl _ (lt_of_lt_of_le hMN h0)
  exact hOdd.false psl2SylowCoordStmt naturalComplementStmt

end CFSG.Timmesfeld.Bridge.OddRoot
