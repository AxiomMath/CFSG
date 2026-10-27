module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.LocalAnalysis.SectionRank.QTK.Witness3

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)

private theorem exists_orderOf_five_of_isTripleCover {X : Type*} [Group X] [Finite X]
    (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) : ∃ f : X, orderOf f = 5 := by
  obtain ⟨hZ, ⟨e⟩⟩ := hX
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  refine exists_prime_orderOf_dvd_card' 5 ?_
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hZ,
    Nat.card_congr e.toEquiv, h360]
  norm_num

private theorem isElemAbelian_sup_zpowers_card {Y : Type*} [Group Y] {p k : ℕ} (hp : p.Prime)
    {E : Subgroup Y} (hE : CFSG.Open.IsElemAbelian p E) (hk : Nat.card E = p ^ k) {z : Y}
    (hz : z ^ p = 1) (hzE : z ∉ E) (hc : ∀ e ∈ E, e * z = z * e) :
    CFSG.Open.IsElemAbelian p (E ⊔ Subgroup.zpowers z) ∧
      Nat.card (E ⊔ Subgroup.zpowers z : Subgroup Y) = p ^ (k + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hz1 : z ≠ 1 := fun h => hzE (h ▸ E.one_mem)
  have hcard : Nat.card (Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hz hz1]
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (E : Set Y) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hc)
  have hdisj : Disjoint E (Subgroup.zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro g hgE hgz
    haveI : Fact (Nat.card (Subgroup.zpowers z)).Prime := ⟨by rw [hcard]; exact hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (E.subgroupOf (Subgroup.zpowers z)) with h | h
    · have hg : (⟨g, hgz⟩ : Subgroup.zpowers z) ∈ E.subgroupOf (Subgroup.zpowers z) := hgE
      rw [h] at hg
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hg)
    · exact absurd (show (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∈
          E.subgroupOf (Subgroup.zpowers z) by rw [h]; trivial) hzE
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute hE (CFSG.Open.isElemAbelian_zpowers hz) ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (hc a ha) n).eq
  · rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E _ hnorm hdisj, hk,
      hcard, pow_succ]

theorem rank5_of_localRank {Q : Type} [Group Q] [Finite Q] {J K : Subgroup Q}
    (hJ : CFSG.IsComponent J) (hK : CFSG.IsComponent K)
    (hJK : J ≤ Subgroup.centralizer (K : Set Q)) (hK3 : Nat.card (Subgroup.center ↥K) = 3)
    (hK5 : ∃ f : ↥K, orderOf f = 5) (hrank : localRank 5 ↥(CFSG.layer Q) < 3) :
    ∀ E R : Subgroup ↥J, Nat.card E = 25 → (∀ x ∈ E, x ^ 5 = 1) → IsPGroup 2 R → R ≠ ⊥ →
      E ≤ Subgroup.normalizer (R : Set ↥J) → False := by
  intro E R hEc hE5 hR2 hR0 hER
  obtain ⟨f, hf⟩ := hK5
  have hJX : J ≤ CFSG.layer Q := CFSG.LocalCores.component_le_layer hJ
  have hKX : K ≤ CFSG.layer Q := CFSG.LocalCores.component_le_layer hK
  have hf' : orderOf (f : Q) = 5 := (Subgroup.orderOf_coe f).trans hf
  have hf5 : (f : Q) ^ 5 = 1 := by rw [← hf']; exact pow_orderOf_eq_one _
  have hcent : ∀ x ∈ J, ∀ w ∈ K, w * x = x * w := fun x hx w hw =>
    Subgroup.mem_centralizer_iff.1 (hJK hx) w hw
  have hcommf : ∀ x ∈ J, x * (f : Q) = (f : Q) * x := fun x hx => (hcent x hx f f.2).symm
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hE : CFSG.Open.IsElemAbelian 5 E :=
    ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (by rw [hEc]; norm_num), hE5⟩
  have hE₀ : CFSG.Open.IsElemAbelian 5 (E.map J.subtype) := hE.map J.subtype
  have hE₀c : Nat.card (E.map J.subtype) = 5 ^ 2 := by
    rw [Subgroup.card_map_of_injective J.subtype_injective, hEc]
    norm_num
  have hfE : (f : Q) ∉ E.map J.subtype := by
    intro hmem
    have hfJ : (f : Q) ∈ J := Subgroup.map_subtype_le E hmem
    have hfZ : f ∈ Subgroup.center ↥K :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcent _ hfJ g g.2)
    have hd := Subgroup.orderOf_dvd_natCard _ hfZ
    rw [hK3, hf] at hd
    omega
  obtain ⟨hE', hE'c⟩ := isElemAbelian_sup_zpowers_card Nat.prime_five hE₀ hE₀c hf5 hfE
    fun e he => hcommf e (Subgroup.map_subtype_le E he)
  have hPJ : R.map J.subtype ≤ J := Subgroup.map_subtype_le R
  have hnorm : E.map J.subtype ⊔ Subgroup.zpowers (f : Q) ≤
      Subgroup.normalizer ((R.map J.subtype : Subgroup Q) : Set Q) := by
    refine sup_le ((Subgroup.map_mono hER).trans (Subgroup.le_normalizer_map J.subtype)) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx =>
      hcommf x (hPJ hx))
  have h3 := CFSG.SectionRank.QTK.le_localRank_of_le (H := CFSG.layer Q) Nat.prime_five
    (hPJ.trans hJX)
    (sup_le ((Subgroup.map_subtype_le E).trans hJX) (Subgroup.zpowers_le.2 (hKX f.2)))
    (fun h => hR0 ((Subgroup.map_eq_bot_iff_of_injective R J.subtype_injective).1 h))
    (hR2.map J.subtype) hE' hE'c hnorm
  omega

theorem Res3Q.rank5 {Q : Type} [Group Q] [Finite Q] {c d g : Q} {A B₀ K V₀ U : Subgroup Q}
    (h : Res3Q c d g A B₀ K V₀ U) (hC : Res3QCompFacts c d A B₀ K) {J : Subgroup Q}
    (hJ : CFSG.IsComponent J) (hJK : J ≠ K) :
    ∀ E R : Subgroup ↥J, Nat.card E = 25 → (∀ x ∈ E, x ^ 5 = 1) → IsPGroup 2 R → R ≠ ⊥ →
      E ≤ Subgroup.normalizer (R : Set ↥J) → False :=
  rank5_of_localRank hJ ⟨h.K_quasi, h.K_subnormal⟩ (hC.le_centralizer J hJ hJK) h.K_cover.1
    (exists_orderOf_five_of_isTripleCover h.K_cover)
    (h.rank (CFSG.layer Q) CFSG.WholeGroup.layer_layer_eq_top 5 Nat.prime_five (by norm_num))

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
