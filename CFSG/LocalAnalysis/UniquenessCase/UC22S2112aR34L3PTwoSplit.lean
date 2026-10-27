module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PSplitDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3POdd
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PRoot
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aULift
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P21b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112l3p_three_five_dvd {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    (hn3 : 3 ≤ c.n) (hn2 : IsPowTwo c.n) :
    3 ∣ Nat.card ↥c.B0 ∧ 5 ∣ Nat.card ↥c.B0 := by
  obtain ⟨k, hk⟩ := hn2
  have hk2 : 2 ≤ k := by
    by_contra h
    have h3k : 3 ≤ 2 ^ k := hk ▸ hn3
    interval_cases k <;> norm_num at h3k
  have h4 : 4 ∣ c.n := hk ▸ (pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)
  obtain ⟨m, hm⟩ := h4
  have h15 : 15 ∣ 2 ^ c.n - 1 := by
    have h : 2 ^ 4 - 1 ∣ (2 ^ 4) ^ m - 1 ^ m := Nat.sub_dvd_pow_sub_pow _ _ _
    rw [one_pow, ← pow_mul, ← hm] at h
    exact h
  have hmem : ∀ q : ℕ, q.Prime → q ∣ 15 → q ∣ Nat.card ↥c.B0 := fun q hq hq15 => by
    have : q ∈ piSet c.B0 := by
      rw [c.hpi]
      exact ⟨hq, hq15.trans h15⟩
    exact this.2
  exact ⟨hmem 3 Nat.prime_three (by norm_num), hmem 5 (by norm_num) (by norm_num)⟩

theorem uc22s2112l3p_false_of_invertSplit (hIS : L3InvertSplit) {D : Data G} (h149 : R149L3P D)
    (hH : H1930 D) (c : Ctx21 D (Choice214U D)) (hn3 : 3 ≤ c.n) (hn2 : IsPowTwo c.n)
    {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1)
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    (hMN : D.M ≤ normalizer (L : Set G)) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ D.M := hL.1.le
  have hBM : c.B0 ≤ D.M := c.hBM
  have hTM : D.T ≤ D.M := D.sylowM.le
  obtain ⟨-, hBab, -, -, -, -, -, -, -, hBT, -, -⟩ := c.hB0
  have hBT' : (c.B0 : Set G) * (D.T : Set G) = (D.T : Set G) * (c.B0 : Set G) := hBT
  have hBo : Odd (Nat.card ↥c.B0) := ch214_odd_card c.hpi
  obtain ⟨h3, h5⟩ := uc22s2112l3p_three_five_dvd c hn3 hn2
  have hB0ne : c.B0 ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at h3
    exact absurd (Nat.le_of_dvd one_pos h3) (by norm_num)
  let θ : ↥D.M →* MulAut (BarInf L) := (inducedBarInfAutHom L).comp (Subgroup.inclusion hMN)
  let B' : Subgroup ↥D.M := c.B0.subgroupOf D.M
  let T' : Subgroup ↥D.M := D.T.subgroupOf D.M
  have hfθ : ∀ b ∈ B', θ b = 1 → b = 1 := fun b hb h1 => Subtype.ext
    (hfaith b hb (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 (hMN b.2) h1))
  have hinj : Function.Injective (θ.domRestrict B') := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hfθ x x.2 hx)
  have hT'2 : IsPGroup 2 ↥T' :=
    D.sylowM.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
  have hB'o : Odd (Nat.card ↥B') := by
    rw [show Nat.card ↥B' = Nat.card ↥c.B0 from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv]
    exact hBo
  have hperm' : (B' : Set ↥D.M) * (T' : Set ↥D.M) = (T' : Set ↥D.M) * (B' : Set ↥D.M) := by
    ext x
    simp only [Set.mem_mul]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      have h : (a : G) * b ∈ (c.B0 : Set G) * (D.T : Set G) := Set.mul_mem_mul ha hb
      rw [hBT'] at h
      obtain ⟨t, ht, b', hb', he⟩ := h
      exact ⟨⟨t, hTM ht⟩, ht, ⟨b', hBM hb'⟩, hb', Subtype.ext he⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      have h : (a : G) * b ∈ (D.T : Set G) * (c.B0 : Set G) := Set.mul_mem_mul ha hb
      rw [← hBT'] at h
      obtain ⟨b', hb', t, ht, he⟩ := h
      exact ⟨⟨b', hBM hb'⟩, hb', ⟨t, hTM ht⟩, ht, Subtype.ext he⟩
  have hInn : (MulAut.conj : BarInf L →* MulAut (BarInf L)).range ≤ θ.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨⟨l, hLM l.2⟩, uc22s2113_inducedBarInfAutHom_of_mem l.2⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T'.map θ) θ.range := by
    have hT : CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ := by
      rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff D.M, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hTM, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact D.sylowM
    have h := PartTwo.s16c7_isSylowOf_map hT θ
    rwa [← MonoidHom.range_eq_map] at h
  have hBab' : IsMulCommutative ↥(B'.map θ) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨x', hx', hx⟩ := x.2
    obtain ⟨y', hy', hy⟩ := y.2
    apply Subtype.ext
    change (x : MulAut (BarInf L)) * y = y * x
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have h := congrArg Subtype.val (hBab.is_comm.comm ⟨(x' : G), hx'⟩ ⟨(y' : G), hy'⟩)
    exact h
  have hcard : Nat.card ↥(B'.map θ) = Nat.card ↥c.B0 := by
    rw [← MonoidHom.restrict_range B' θ, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
  have hperm : ((B'.map θ : Subgroup _) : Set (MulAut (BarInf L))) *
      ((T'.map θ : Subgroup _) : Set (MulAut (BarInf L))) =
      ((T'.map θ : Subgroup _) : Set (MulAut (BarInf L))) *
        ((B'.map θ : Subgroup _) : Set (MulAut (BarInf L))) := by
    rw [Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm', Set.image_mul]
  have hfin : (∃ s ∈ T'.map θ, ∀ b ∈ B'.map θ, s * b * s⁻¹ = b⁻¹) → False := by
    rintro ⟨_, ⟨τ, hτ, rfl⟩, hs⟩
    obtain ⟨t, htT, ht⟩ := uc22s2112u_lift_inv θ hT'2 hB'o hperm' hfθ hτ
      (fun b hb => hs (θ b) (mem_map_of_mem θ hb))
    have hinvG : ∀ b ∈ c.B0, (t : G) * b * (t : G)⁻¹ = b⁻¹ := fun b hb =>
      congrArg Subtype.val (ht ⟨b, hBM hb⟩ hb)
    obtain ⟨hi, -⟩ := c.hch
    exact hi hB0ne (t : G) htT (uc22s2112u_mem_normalizer_of_inv hinvG) hinvG
  refine hfin (hIS (BarInf L) p hp hp2 hX θ.range (T'.map θ) (B'.map θ)
    hInn hSyl (Subgroup.map_le_range (f := θ) B') hBab' (by rw [hcard]; exact hBo)
    (by rw [hcard]; exact h3) (by rw [hcard]; exact h5) hperm ?_)
  intro K hKperf hKcard d hdB hdp hdK
  obtain ⟨d₀, hd₀B, rfl⟩ := hdB
  have hd₀B' : (d₀ : G) ∈ c.B0 := hd₀B
  have hord : orderOf (d₀ : G) = orderOf (θ d₀) := by
    calc orderOf (d₀ : G) = orderOf d₀ := Subgroup.orderOf_coe d₀
      _ = orderOf (⟨d₀, hd₀B⟩ : ↥B') := (Subgroup.orderOf_mk d₀ hd₀B).symm
      _ = orderOf (θ.domRestrict B' ⟨d₀, hd₀B⟩) := (orderOf_injective _ hinj _).symm
      _ = orderOf (θ d₀) := rfl
  have hd₀p : (orderOf (d₀ : G)).Prime := by rw [hord]; exact hdp
  have hd₀2 : orderOf (d₀ : G) ≠ 2 := fun h2 => by
    have hdvd : orderOf (d₀ : G) ∣ Nat.card ↥c.B0 :=
      Subgroup.orderOf_dvd_natCard c.B0 hd₀B'
    rw [h2] at hdvd
    exact (Nat.not_even_iff_odd.2 hBo) (even_iff_two_dvd.2 hdvd)
  have hdvdK := uc22s2112l3p_card_dvd_of_fixes hL.2.2 (hMN d₀.2) hd₀p hd₀2 hKperf hdK
  obtain ⟨r, hr, hrd, hrM⟩ := h149 L hL p hp hp2 hX
  haveI : Fact r.Prime := ⟨hr⟩
  have hdvd' : r ∣ Nat.card ↥(L ⊓ centralizer ({(d₀ : G)} : Set G)) :=
    hrd.trans (by rw [← hKcard]; exact hdvdK)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hdvd'
  have hyo : orderOf (y : G) = r := by rw [Subgroup.orderOf_coe, hy]
  have hyL := mem_inf.1 y.2
  have hX0 : zpowers (y : G) ≠ ⊥ := fun h => by
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hyo
    exact hr.one_lt.ne hyo
  have hX0p : IsPGroup r (zpowers (y : G)) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  have hX0U := mem_uniqueSet_of_isStronglyPEmbedded hr hrM (zpowers_le.2 (hLM hyL.1)) hX0 hX0p
  obtain ⟨-, -, hCN, -⟩ := uc22s2112r2_normalizer hH c hLM hd₀B' hd₀p
  have hb0 : zpowers (d₀ : G) ≠ ⊥ := fun h => by
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hd₀p
    exact Nat.not_prime_one hd₀p
  let c₀ : Ctx21 D (Choice214U D) := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  obtain ⟨m, hm, hminv⟩ := s21_10 D (Choice214U D) hH c₀ (zpowers (d₀ : G)) hb0
    (zpowers_le.2 hd₀B') (zpowers (y : G)) hX0 ⟨r, hr, hX0p⟩ (zpowers_le.2 (hCN hyL.2)) hX0U
  have hmd : m * (d₀ : G) * m⁻¹ = (d₀ : G)⁻¹ := hminv _ (mem_zpowers _)
  refine ⟨θ ⟨m, hm⟩, ⟨⟨m, hm⟩, rfl⟩, ?_⟩
  rw [← map_mul, ← map_inv, ← map_mul, ← map_inv]
  congr 1
  exact Subtype.ext hmd

theorem s21_12aFR34L3PTwo_of_invertSplit (hIS : L3InvertSplit) {D : Data G} (h149 : R149L3P D)
    (hMN : ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
      (LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1) →
        D.M ≤ normalizer (L : Set G)) :
    S21_12aFR34L3PTwo D (Choice214U D) := by
  intro hH c hn3 hn2 L hL p hp hp2 hX _ hfaith
  exact (uc22s2112l3p_false_of_invertSplit hIS h149 hH c hn3 hn2 hL hp hp2 hX hfaith
    (hMN L hL p hp hp2 hX)).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
