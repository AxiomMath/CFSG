module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107E3Syl
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107E3Pair
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107E3Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z7
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Odd
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251c
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddPair
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Fusion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (Standing Setup uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Sec7Core4 StronglyEmbeddedFive)

variable {G : Type} [Group G]

private theorem mem_centralizer_zpowers_of_mul_eq_mul {a b : G} (h : a * b = b * a) :
    b ∈ centralizer ((zpowers a : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨k, rfl⟩
  exact ((show Commute a b from h).zpow_left k).eq

variable [Finite G]

theorem exists_orderOf_mem_centralizer_of_dvd {L P₁ P₂ : Subgroup G} (hP₁ : IsPGroup 3 P₁)
    (hP₂ : IsPGroup 3 P₂) (h₁₂ : P₂ ≤ centralizer (P₁ : Set G))
    (hP₁L : P₁ ≤ CFSG.Quasithin.centralizerMod (pCoreOf 2 L) (normalizer (L : Set G)) L)
    (hP₂L : P₂ ≤ CFSG.Quasithin.centralizerMod (pCoreOf 2 L) (normalizer (L : Set G)) L)
    {q : ℕ} (hq : q.Prime) (hqL : q ∣ Nat.card (Bar2 L)) :
    ∃ x ∈ L, orderOf x = q ∧ x ∈ centralizer (P₁ : Set G) ⊓ centralizer (P₂ : Set G) := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨xb, hxb⟩ := exists_prime_orderOf_dvd_card' (G := Bar2 L) q hqL
  obtain ⟨⟨b, hbL⟩, rfl⟩ := QuotientGroup.mk_surjective xb
  obtain ⟨c, hbc, hcC⟩ := P2251c.exists_mem_centralizer_of_coset (by norm_num) (by norm_num)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hP₁ hP₂ h₁₂ (fun u hu => (hP₁L hu).2.1)
    (fun v hv => (hP₂L hv).2.1)
    (fun u hu => P2251c.inv_mul_conj_mem_of_mem_centralizerMod (hP₁L hu) hbL)
    (fun v hv => P2251c.inv_mul_conj_mem_of_mem_centralizerMod (hP₂L hv) hbL)
  have hcL : c ∈ L := by
    simpa using mul_mem hbL (CFSG.LieType.BorelTits.pCoreOf_le 2 L hbc)
  have hmem : (⟨b, hbL⟩ : ↥L)⁻¹ * ⟨c, hcL⟩ ∈ CFSG.pCore 2 ↥L := by
    have h : L.subtype ((⟨b, hbL⟩ : ↥L)⁻¹ * ⟨c, hcL⟩) ∈ pCoreOf 2 L := hbc
    exact (mem_map_iff_mem L.subtype_injective).1 h
  have hbc' : ((⟨b, hbL⟩ : ↥L) : Bar2 L) = ((⟨c, hcL⟩ : ↥L) : Bar2 L) := QuotientGroup.eq.2 hmem
  have hqc : q ∣ orderOf c := by
    have hdvd := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨c, hcL⟩
    rwa [QuotientGroup.mk'_apply, Subgroup.orderOf_mk, ← hbc', hxb] at hdvd
  exact ⟨c ^ (orderOf c / q), pow_mem hcL _, orderOf_pow_orderOf_div (orderOf_pos c).ne' hqc,
    pow_mem hcC _⟩

theorem exists_not_mem_commute_of_normalizer_not_le (hSE : StronglyEmbeddedFive)
    (hS : Standing G) (S : Setup G) {p : ℕ} (hp : p ∈ (PartTwo.Three.dataOfSetup hS S).sig)
    (hp5 : 5 ≤ p) (hsp : IsStronglyPEmbedded p S.M) {R : Subgroup G} {x z : G} {ℓ : ℕ}
    (hR : R ≠ ⊥) (hRM : R ≤ S.M) (hN : ¬ normalizer (R : Set G) ≤ S.M)
    (hrank : 2 ≤ CFSG.Open.pRank p (S.M ⊓ normalizer (R : Set G)))
    (hxN : x ∈ normalizer (R : Set G) ⊓ S.M) (hzN : z ∈ normalizer (R : Set G) ⊓ S.M)
    (hx : orderOf x = p) (hxz : x * z = z * x) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ≠ p)
    (hz : orderOf z = ℓ) : ∃ j : G, j ∉ S.M ∧ j * z = z * j := by
  obtain ⟨hpp, hp2⟩ := (PartTwo.Three.dataOfSetup hS S).sig_prime p hp
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal p hpp hp2 hsp
    (PartTwo.Three.normalizer_le_of_mem_sigmaOf S hp)
  have hxp : IsPGroup k.p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one]; rfl)
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  exact k.exists_not_mem_commute_of_prime (k.step75 hp5 hSE) k.step72L
    (k.step76C_of_kIDExcluded hp5 (k.kIDExcluded_of_evenRank_le_three (le_of_eq hS.rank)) hSE)
    (k.config_normalizer hR hRM hrank hN) hxN hzN hxp hx1 (by rw [hz]; exact hℓ)
    (by rw [hz]; exact hℓ2) (by rw [hz]; exact hℓp) hxz

theorem mem_uniqueSet_of_cubesInner (hSE : StronglyEmbeddedFive) (hS : Standing G)
    (S : Setup G) (hSg : UC6S846.SigmaStd (PartTwo.Three.dataOfSetup hS S))
    (h82 : F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (h847 : R847OrderThree (PartTwo.Three.dataOfSetup hS S))
    (h76 : F07.R76Sig (PartTwo.Three.dataOfSetup hS S))
    (h614 : UC6.R6_14 (PartTwo.Three.dataOfSetup hS S)) (hnsp : ¬ IsStronglyPEmbedded 3 S.M)
    {L₁ L₂ : Subgroup G} (hL₁ : L₁ ∈ calC S.M) (hL₂ : L₂ ∈ calC S.M) (h12 : L₁ ≠ L₂)
    (r₁ : CFSG.Open.pRank 3 L₁ = 1) (r₂ : CFSG.Open.pRank 3 L₂ = 1)
    (hs₁ : F08.Thin8 L₁ ∨ ∃ n : ℕ, IsU3 (Bar2 L₁) n)
    (hs₂ : F08.Thin8 L₂ ∨ ∃ n : ℕ, IsU3 (Bar2 L₂) n)
    (hZ₁ : center (Bar2 L₁) = ⊥) (hZ₂ : center (Bar2 L₂) = ⊥)
    (hloss₁ : ∀ p : ℕ, p.Prime → 5 ≤ p → R8107Loss.LossAt (Bar2 L₁) p)
    (hloss₂ : ∀ p : ℕ, p.Prime → 5 ≤ p → R8107Loss.LossAt (Bar2 L₂) p) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R S.M) (hI₁ : CubesInner R L₁)
    (hI₂ : CubesInner R L₂) {a₁ a₂ : G} (ha₁ : a₁ ∈ L₁ ⊓ R) (ha₂ : a₂ ∈ L₂ ⊓ R)
    (ho₁ : orderOf a₁ = 3) (ho₂ : orderOf a₂ = 3) {p : ℕ}
    (hp : p ∈ (PartTwo.Three.dataOfSetup hS S).sig) {y : G} (hy : orderOf y = p)
    (hy₁ : y * a₁ = a₁ * y) (hy₂ : y * a₂ = a₂ * y) :
    zpowers a₁ ∈ uniqueSet S.M ∧ zpowers a₂ ∈ uniqueSet S.M := by
  obtain ⟨hpp, hp2⟩ := (PartTwo.Three.dataOfSetup hS S).sig_prime p hp
  have hp5 : 5 ≤ p := five_le_of_mem_sig hSg hnsp hL₁ hp
  have hp3 : p ≠ 3 := by omega
  have hsp : IsStronglyPEmbedded p S.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL₁) hp
  have hR3 := hR.isPGroup
  have hRodd : Odd (Nat.card R) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR3
    rw [hn]
    exact (Nat.prime_three.odd_of_ne_two (by norm_num)).pow
  obtain ⟨h₁₂, a₀, ha₀R, ha₀3, h₀₁, h₀₂, ha₀C₁, ha₀C₂, -, hdec⟩ :=
    omega_of_cubesInner hL₁ hL₂ h12 r₁ r₂ hZ₁ hZ₂ (pRank_three_le_three_of_not_sp hSg hnsp hL₁)
      hR (R8107Odd.le_normalizer_of_odd h82 hnsp hL₁ r₁ hR.le hRodd)
      (R8107Odd.le_normalizer_of_odd h82 hnsp hL₂ r₂ hR.le hRodd) hI₁ hI₂ ha₁ ha₂ ho₁ ho₂
  have hdvd := dvd_card_bar2_of_loss hSg h82 h76 h614 hnsp hL₁ hL₂ h12 r₁ r₂ hZ₁ hloss₁ hloss₂ hp
  have hL₂C₁ := P2251c.le_centralizerMod_of_ne hL₁ hL₂ h12
  have hL₁C₂ := P2251c.le_centralizerMod_of_ne hL₂ hL₁ h12.symm
  have hz : ∀ {a : G}, a ∈ R → IsPGroup 3 (zpowers a) := fun ha => hR3.to_le (zpowers_le.2 ha)
  have hcomm : ∀ {x a : G}, x ∈ centralizer ((zpowers a : Subgroup G) : Set G) →
      x * a = a * x := fun hx => (mem_centralizer_iff.1 hx _ (mem_zpowers _)).symm
  obtain ⟨x₂, hx₂L, hx₂o, hx₂C⟩ := exists_orderOf_mem_centralizer_of_dvd (hz ha₀R) (hz ha₁.2)
    (zpowers_le.2 (mem_centralizer_zpowers_of_mul_eq_mul h₀₁)) (zpowers_le.2 ha₀C₂)
    (zpowers_le.2 (hL₁C₂ ha₁.1)) hpp hdvd.2
  obtain ⟨x₁, hx₁L, hx₁o, hx₁C⟩ := exists_orderOf_mem_centralizer_of_dvd (hz ha₀R) (hz ha₂.2)
    (zpowers_le.2 (mem_centralizer_zpowers_of_mul_eq_mul h₀₂)) (zpowers_le.2 ha₀C₁)
    (zpowers_le.2 (hL₂C₁ ha₂.1)) hpp hdvd.1
  have hN₁ : normalizer ((zpowers a₁ : Subgroup G) : Set G) ≤ S.M :=
    h847 L₁ hL₁ r₁ _ (zpowers_le.2 ha₁.1) (by rw [Nat.card_zpowers, ho₁]) p hp hp3 hs₁
  have hN₂ : normalizer ((zpowers a₂ : Subgroup G) : Set G) ≤ S.M :=
    h847 L₂ hL₂ r₂ _ (zpowers_le.2 ha₂.1) (by rw [Nat.card_zpowers, ho₂]) p hp hp3 hs₂
  have hnorm : ∀ {x : G}, x * a₀ = a₀ * x →
      x ∈ normalizer ((zpowers a₀ : Subgroup G) : Set G) :=
    fun h => centralizer_le_normalizer _ (mem_centralizer_zpowers_of_mul_eq_mul h.symm)
  have hN₀ : a₀ ≠ 1 → normalizer ((zpowers a₀ : Subgroup G) : Set G) ≤ S.M := by
    intro ha₀1
    by_contra hN
    obtain ⟨j, hjM, hj⟩ := exists_not_mem_commute_of_normalizer_not_le hSE hS S hp hp5 hsp
      (zpowers_ne_bot.2 ha₀1) (zpowers_le.2 (hR.le ha₀R)) hN
      (PartOne.Section9.two_le_pRank_of_pair hpp hp2 hL₁ hL₂ h12 hZ₁ inf_le_left hx₁L hx₂L
        ⟨hL₁.1.le hx₁L, hnorm (hcomm hx₁C.1)⟩ ⟨hL₂.1.le hx₂L, hnorm (hcomm hx₂C.1)⟩ hx₁o hx₂o)
      ⟨hnorm (hcomm hx₂C.1), hL₂.1.le hx₂L⟩ ⟨hnorm h₀₁.symm, hR.le ha₁.2⟩ hx₂o (hcomm hx₂C.2)
      Nat.prime_three (by norm_num) (Ne.symm hp3) ho₁
    exact hjM (hN₁ (centralizer_le_normalizer _ (mem_centralizer_zpowers_of_mul_eq_mul hj.symm)))
  have h₁3 : a₁ ^ 3 = 1 := by rw [← ho₁]; exact pow_orderOf_eq_one a₁
  have h₂3 : a₂ ^ 3 = 1 := by rw [← ho₂]; exact pow_orderOf_eq_one a₂
  have hAel : IsElemAbelian 3 (zpowers a₀ ⊔ zpowers a₁ ⊔ zpowers a₂) := by
    refine ((isElemAbelian_zpowers ha₀3).sup_of_commute (isElemAbelian_zpowers h₁3)
      ?_).sup_of_commute (isElemAbelian_zpowers h₂3) fun u hu v hv => ?_
    · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      exact ((show Commute a₀ a₁ from h₀₁).zpow_zpow m n).eq
    · have hle : zpowers a₀ ⊔ zpowers a₁ ≤ centralizer ((zpowers a₂ : Subgroup G) : Set G) :=
        sup_le (zpowers_le.2 (mem_centralizer_zpowers_of_mul_eq_mul h₀₂.symm))
          (zpowers_le.2 (mem_centralizer_zpowers_of_mul_eq_mul h₁₂.symm))
      exact (mem_centralizer_iff.1 (hle hu) v hv).symm
  have h₀A : zpowers a₀ ≤ zpowers a₀ ⊔ zpowers a₁ ⊔ zpowers a₂ := le_sup_left.trans le_sup_left
  have h₁A : zpowers a₁ ≤ zpowers a₀ ⊔ zpowers a₁ ⊔ zpowers a₂ := le_sup_right.trans le_sup_left
  have h₂A : zpowers a₂ ≤ zpowers a₀ ⊔ zpowers a₁ ⊔ zpowers a₂ := le_sup_right
  have hAR : zpowers a₀ ⊔ zpowers a₁ ⊔ zpowers a₂ ≤ R :=
    sup_le (sup_le (zpowers_le.2 ha₀R) (zpowers_le.2 ha₁.2)) (zpowers_le.2 ha₂.2)
  have hΩ : ∀ x ∈ R, x ^ 3 = 1 → x ∈ zpowers a₀ ⊔ zpowers a₁ ⊔ zpowers a₂ := by
    intro x hx hx3
    obtain ⟨i, j, k, rfl⟩ := hdec x hx hx3
    exact mul_mem (mul_mem (pow_mem (h₀A (mem_zpowers a₀)) i) (pow_mem (h₁A (mem_zpowers a₁)) j))
      (pow_mem (h₂A (mem_zpowers a₂)) k)
  have hn₁₂ : a₂ ∉ zpowers a₁ := fun h =>
    P2251c.not_mem_of_orderOf_eq_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁) ho₂
      (P2251c.mem_pCoreOf_of_mem_centralizerMod hZ₁ (zpowers_le.2 ha₁.1 h) (hL₂C₁ ha₂.1))
  have hyM : y ∈ S.M :=
    hN₁ (centralizer_le_normalizer _ (mem_centralizer_zpowers_of_mul_eq_mul hy₁.symm))
  have hNA := normalizer_le_of_axes hsp ha₀3 h₁3 h₂3 h₀₁ h₀₂ h₁₂ hn₁₂ (h₁A (mem_zpowers a₁))
    (h₂A (mem_zpowers a₂)) (fun x hx => hdec x (hAR hx) (hAel.2 x hx)) hN₁ hN₂ hN₀
    ⟨y, hyM, hy, hy₁, hy₂⟩
    (fun _ => ⟨x₂, hL₂.1.le hx₂L, hx₂o, hcomm hx₂C.1, hcomm hx₂C.2⟩)
    (fun _ => ⟨x₁, hL₁.1.le hx₁L, hx₁o, hcomm hx₁C.1, hcomm hx₁C.2⟩)
  exact ⟨AGL81TheoremCD.Section8.mem_uniqueSet_of_normalizer_le_of_omega hR hAR hAel hΩ hNA h₁A
      hN₁,
    AGL81TheoremCD.Section8.mem_uniqueSet_of_normalizer_le_of_omega hR hAR hAel hΩ hNA h₂A hN₂⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3

end
