module

public import CFSG.RankThree.PartTwo.Sec5.Items52
import CFSG.RankThree.PartTwo.Sec5.Faithful
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
import CFSG.RankThree.PartTwo.Source.OrderThreeMinimalTwoGroup

public section

namespace CFSG.RankThree.PartTwo.Sec5

open CFSG
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem rank3II_5_5 {A S : Subgroup G} (h : SectionFiveHyp A S)
    {B : Subgroup G} (hBA : B ≤ A) (hB : Nat.card B = 9) :
    CFSG.Assembly.pRank 2 (S ⊓ Subgroup.centralizer (B : Set G)) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hlt
  obtain ⟨V, hVSB, hV, hVcard⟩ := exists_elemAbelian_le_of_le_pRank Nat.prime_two
    (X := S ⊓ Subgroup.centralizer (B : Set G)) (k := 3) (by omega)
  set P := CFSG.pCore 3 G with hPdef
  have hP3 : IsPGroup 3 P := CFSG.pCore_isPGroup
  have hNP : ∀ g : G, g ∈ Subgroup.normalizer (P : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  have hfaith : S ⊓ Subgroup.centralizer (P : Set G) = ⊥ := rank3II_5_3 h
  have hBel : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_of_le h.elemAbelian hBA
  have hB3' : IsPGroup 3 B := isPGroup_of_isElemAbelian hBel
  have hBcen : B ≤ Subgroup.centralizer (B : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun c hc =>
      congrArg Subtype.val (hBel.1.is_comm.comm ⟨c, hc⟩ ⟨b, hb⟩)
  set Q := (P ⊓ Subgroup.centralizer (B : Set G)) ⊔ B with hQdef
  have hBnorm : B ≤ Subgroup.normalizer
      ((P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hNP b, normalizer_le_normalizer_centralizer B (Subgroup.le_normalizer hb)⟩
  have hQ3 : IsPGroup 3 Q := IsPGroup.to_sup_of_normal_left' (hP3.to_le inf_le_left) hB3' hBnorm
  have hQB : Q ≤ Subgroup.centralizer (B : Set G) := sup_le inf_le_right hBcen
  obtain ⟨D, hBD, hDQ, hD3, hDnorm, hDfaith⟩ :=
    exists_faithful_exponent_three hQ3 le_sup_right hQB hBel.2
  have hD3' : IsPGroup 3 D := hQ3.to_le hDQ
  have hSBQ : S ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
    intro s hs
    have hsB : s ∈ Subgroup.normalizer (B : Set G) := Subgroup.centralizer_le_normalizer _ hs.2
    exact Subgroup.inf_normalizer_le_normalizer_sup _ B
      ⟨Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hNP s, normalizer_le_normalizer_centralizer B hsB⟩, hsB⟩
  have hSBD : S ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (D : Set G) :=
    fun s hs => hDnorm s (hSBQ hs) hs.2
  have hfaithQ : ∀ K : Subgroup G, K ≤ S ⊓ Subgroup.centralizer (B : Set G) →
      K ≤ Subgroup.centralizer (Q : Set G) → K = ⊥ := by
    intro K hKS hKQ
    have hK3 : ¬ 3 ∣ Nat.card K :=
      Source.not_three_dvd_card_of_isPGroup_two (h.isPGroup.to_le (hKS.trans inf_le_left))
    have hPB3 : IsPGroup 3 ((P ⊔ B : Subgroup G)) :=
      IsPGroup.to_sup_of_normal_left' hP3 hB3' (fun b _ => hNP b)
    have hKT : K ≤ Subgroup.normalizer ((P ⊔ B : Subgroup G) : Set G) := fun k hk =>
      Subgroup.inf_normalizer_le_normalizer_sup P B
        ⟨hNP k, Subgroup.centralizer_le_normalizer _ (hKS hk).2⟩
    have hKP := Source.le_centralizer_of_le_centralizer_inf_centralizer hPB3 hK3 le_sup_right hKT
      (hKS.trans inf_le_right)
      (hKQ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
        (sup_inf_centralizer_le (fun b _ => hNP b) hBcen))))
    have hKC : K ≤ S ⊓ Subgroup.centralizer (P : Set G) :=
      le_inf (hKS.trans inf_le_left)
        (hKP.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)))
    rw [hfaith] at hKC
    exact le_bot_iff.mp hKC
  have hfaithD : ∀ K : Subgroup G, K ≤ S ⊓ Subgroup.centralizer (B : Set G) →
      K ≤ Subgroup.centralizer (D : Set G) → K = ⊥ := fun K hKS hKD =>
    hfaithQ K hKS (hDfaith K (Source.not_three_dvd_card_of_isPGroup_two
      (h.isPGroup.to_le (hKS.trans inf_le_left))) (hKS.trans hSBQ) hKD)
  have hcopD : Nat.Coprime 2 (Nat.card D) := by
    obtain ⟨k, hk⟩ := hD3'.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hVD : V ≤ Subgroup.normalizer (D : Set G) := hVSB.trans hSBD
  obtain ⟨U, hUV, hU4, x, hxX, hxB⟩ : ∃ U : Subgroup G, U ≤ V ∧ Nat.card U = 4 ∧
      ∃ x ∈ D ⊓ Subgroup.centralizer (U : Set G), x ∉ B := by
    by_contra hno
    push Not at hno
    have hDB : D ≤ B := le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_two hV
      (by rw [hVcard]) hVD hcopD fun U hUV hU x hx => hno U hUV (by rw [hU]; norm_num) x hx
    have hVc : V ≤ Subgroup.centralizer (D : Set G) :=
      (hVSB.trans inf_le_right).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hDB))
    have hVbot := hfaithD V hVSB hVc
    rw [hVbot, Subgroup.card_bot] at hVcard
    norm_num at hVcard
  set X := D ⊓ Subgroup.centralizer (U : Set G) with hXdef
  have hUel : CFSG.Assembly.IsElemAbelian 2 U := isElemAbelian_of_le hV hUV
  have hUB : U ≤ Subgroup.centralizer (B : Set G) := (hUV.trans hVSB).trans inf_le_right
  have hBX : B ≤ X := le_inf hBD (Subgroup.le_centralizer_iff.mp hUB)
  have hXU : U ≤ Subgroup.centralizer (X : Set G) :=
    Subgroup.le_centralizer_iff.mp inf_le_right
  have hstep7 : ∀ v ∈ U, v ≠ 1 →
      (D ⊓ Subgroup.centralizer ({v} : Set G)) ⊓ Subgroup.centralizer (X : Set G) ≤ X := by
    intro v hv hv1 y hy
    by_contra hyX
    have hx3 : x ^ 3 = 1 := hD3 x hxX.1
    obtain ⟨hE₀, hE₀card⟩ := isElemAbelian_sup_zpowers hBel hxB hx3
      (fun b hb => Subgroup.mem_centralizer_iff.mp (hQB (hDQ hxX.1)) b hb)
    have hE₀X : B ⊔ Subgroup.zpowers x ≤ X := sup_le hBX (Subgroup.zpowers_le.mpr hxX)
    have hyE₀ : y ∉ B ⊔ Subgroup.zpowers x := fun hy' => hyX (hE₀X hy')
    obtain ⟨hE, hEcard⟩ := isElemAbelian_sup_zpowers hE₀ hyE₀ (hD3 y hy.1.1)
      (fun a ha => Subgroup.mem_centralizer_iff.mp hy.2 a (hE₀X ha))
    have hv2 : v ^ 2 = 1 := hUel.2 v hv
    have hEv : (B ⊔ Subgroup.zpowers x) ⊔ Subgroup.zpowers y ≤
        Subgroup.centralizer ({v} : Set G) := by
      refine sup_le (sup_le ?_ ?_) (Subgroup.zpowers_le.mpr hy.1.2)
      · intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hUB hv) b hb
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hxX.2 v hv).symm
    have hle := card_le_of_le_centralizer_involution h.evenRank_eq hv1 hv2 hE hEv
    rw [hEcard, hE₀card, hB] at hle
    norm_num at hle
  have hstep8 : ∀ v ∈ U, v ≠ 1 → D ⊓ Subgroup.centralizer ({v} : Set G) ≤ X := by
    intro v hv hv1
    have hU3 : ¬ 3 ∣ Nat.card U := by rw [hU4]; norm_num
    have hXT : X ≤ D ⊓ Subgroup.centralizer ({v} : Set G) :=
      inf_le_inf_left D (Subgroup.centralizer_le (by simpa using hv))
    have hUT : U ≤ Subgroup.normalizer
        ((D ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) := by
      intro w hw
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hVD (hUV hw), ?_⟩
      refine Subgroup.le_normalizer ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hUel.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
    have hcent := Source.le_centralizer_of_le_centralizer_inf_centralizer
      (hD3'.to_le inf_le_left) hU3 hXT hUT hXU
      (Subgroup.le_centralizer_iff.mp ((hstep7 v hv hv1).trans
        (Subgroup.le_centralizer_iff.mp hXU)))
    exact le_inf inf_le_left (Subgroup.le_centralizer_iff.mp hcent)
  have hDX : D ≤ X := le_of_forall_inf_centralizer_le Nat.prime_two hUel (by rw [hU4]; norm_num)
    ((hUV.trans hVSB).trans hSBD) hcopD hstep8
  have hUD : U ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.le_centralizer_iff.mp (hDX.trans inf_le_right)
  have hUbot := hfaithD U (hUV.trans hVSB) hUD
  rw [hUbot, Subgroup.card_bot] at hU4
  norm_num at hU4

end CFSG.RankThree.PartTwo.Sec5
