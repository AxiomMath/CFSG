module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3
public import CFSG.GroupTheory.PCore.Construction
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndAction
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.GroupTheory.ElemAbelianRank
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Fischer.Classification.Unitary.Coords
import CFSG.LargeExtraspecial.AS35QThModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open scoped commutatorElement
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.ABGLocalTools (IsSylowOf)

variable {X : Type} [Group X] [Finite X]

private lemma pRank_normalClosure_eq_one (hK332 : UCK.K332ThreeAb)
    (hK : CFSG.Open.IsKGroup X) {S Z : Subgroup X} (hS : IsSylowOf 3 S ⊤)
    (hSe : CFSG.Open.IsElemAbelian 3 S) (hS27 : Nat.card S = 27) (hZS : Z ≤ S)
    (hZ : Nat.card Z = 3) (hw : IsWeaklyClosedIn Z S) :
    CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set X)) = 1 := by
  have hΩ : ∀ x ∈ S, x ^ 3 = 1 → ∀ y ∈ S, y ^ 3 = 1 → x * y = y * x :=
    fun x hx _ y hy _ => hSe.comm hx hy
  have hrank : CFSG.Open.pRank 3 S ≤ 3 := by
    have h := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (p := 3)
      Nat.prime_three hSe
    rw [hS27] at h
    refine (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 3)).1 ?_
    rw [← h]
    norm_num
  exact hK332 X hK S hS hΩ hrank Z hZS hZ hw

lemma inf_normalClosure_eq_of_pRank_eq_one {S Z : Subgroup X}
    (hSe : CFSG.Open.IsElemAbelian 3 S) (hZS : Z ≤ S) (hZ : Nat.card Z = 3)
    (hrank : CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set X)) = 1) :
    S ⊓ Subgroup.normalClosure (Z : Set X) = Z := by
  set N : Subgroup X := Subgroup.normalClosure (Z : Set X)
  have hZle : Z ≤ S ⊓ N := le_inf hZS Subgroup.le_normalClosure
  have hcard : Nat.card ↥(S ⊓ N) ≤ Nat.card Z := by
    have hel : CFSG.Open.IsElemAbelian 3 (S ⊓ N) := hSe.mono inf_le_left
    have hc := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (p := 3)
      Nat.prime_three hel
    have hmono : CFSG.Open.pRank 3 (S ⊓ N) ≤ 1 :=
      (CFSG.SectionRank.pRank_mono (by norm_num : (1 : ℕ) < 3) inf_le_right).trans
        (le_of_eq hrank)
    calc Nat.card ↥(S ⊓ N)
        = 3 ^ CFSG.Open.pRank 3 (S ⊓ N) := hc
      _ ≤ 3 ^ 1 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 3)).2 hmono
      _ = Nat.card Z := by rw [hZ]; norm_num
  exact (Subgroup.eq_of_le_of_card_ge hZle hcard).symm

private lemma inf_le_pPrimeCore_of_inf_sylow {S Z₁ Z₂ N₁ N₂ : Subgroup X}
    (hS : IsSylowOf 3 S ⊤) (hN₁ : N₁.Normal) (hN₂ : N₂.Normal)
    (hZ₁ : Nat.card Z₁ = 3) (hZ₂ : Nat.card Z₂ = 3) (hZ₁₂ : Z₁ ≠ Z₂)
    (h₁ : S ⊓ N₁ = Z₁) (h₂ : S ⊓ N₂ = Z₂) : N₁ ⊓ N₂ ≤ CFSG.pPrimeCore 3 X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : N₁.Normal := hN₁
  haveI : N₂.Normal := hN₂
  have hdisj : Z₁ ⊓ Z₂ = ⊥ := by
    have hdvd : Nat.card ↥(Z₁ ⊓ Z₂) ∣ 3 := by
      rw [← hZ₁]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card ↥(Z₁ ⊓ Z₂) ≠ 3 := by
      intro hc
      have heq : Z₁ ⊓ Z₂ = Z₁ := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [hc, hZ₁]
      have hle : Z₁ ≤ Z₂ := heq ▸ inf_le_right
      exact hZ₁₂ (Subgroup.eq_of_le_of_card_ge hle (by rw [hZ₁, hZ₂]))
    have h1 : Nat.card ↥(Z₁ ⊓ Z₂) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact h
      · exact absurd h hne
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hbot : S ⊓ (N₁ ⊓ N₂) = ⊥ := by
    refine le_bot_iff.mp ?_
    intro x hx
    have hx₁ : x ∈ Z₁ := by rw [← h₁]; exact ⟨hx.1, hx.2.1⟩
    have hx₂ : x ∈ Z₂ := by rw [← h₂]; exact ⟨hx.1, hx.2.2⟩
    have hxinf : x ∈ Z₁ ⊓ Z₂ := ⟨hx₁, hx₂⟩
    rwa [hdisj] at hxinf
  have hSyl : IsSylowOf 3 (S ⊓ (N₁ ⊓ N₂)) (N₁ ⊓ N₂) :=
    hS.inf_of_le_normalizer (K := ⊤) (N := N₁ ⊓ N₂) le_top
      (le_of_eq (Subgroup.normalizer_eq_top (H := N₁ ⊓ N₂)).symm)
  have hcard := hSyl.card_eq
  rw [hbot, Subgroup.card_bot] at hcard
  have hfac : (Nat.card ↥(N₁ ⊓ N₂)).factorization 3 = 0 := by
    by_contra hne
    have hlt : 1 < 3 ^ (Nat.card ↥(N₁ ⊓ N₂)).factorization 3 :=
      Nat.one_lt_pow hne (by norm_num)
    omega
  have hcop : Nat.Coprime 3 (Nat.card ↥(N₁ ⊓ N₂)) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hdvd
    have hpos := Nat.Prime.factorization_pos_of_dvd Nat.prime_three
      (Nat.card_pos.ne') hdvd
    omega
  exact CFSG.le_pPrimeCore_of_normal_coprime inferInstance hcop

lemma le_centralizer_sup_pPrimeCore_of_commutator_le {M N Z : Subgroup X}
    (hZN : Z ≤ N) (hZ3 : IsPGroup 3 Z) (hcomm : ⁅N, M⁆ ≤ CFSG.pPrimeCore 3 X) :
    M ≤ Subgroup.centralizer (Z : Set X) ⊔ CFSG.pPrimeCore 3 X := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup X := CFSG.pPrimeCore 3 X
  let f : X →* X ⧸ O := QuotientGroup.mk' O
  have hker : f.ker = O := QuotientGroup.ker_mk' O
  have hf : Nat.Coprime (Nat.card f.ker) 3 := by
    rw [hker]
    exact (CFSG.pPrimeCore_coprime_card (p := 3) (G := X)).symm
  have hmap := CoprimeImage.map_inf_centralizer_of_coprime_ker (p := 3) Nat.prime_three f hf
    (X := ⊤) (B := Z) hZ3 le_top
  rw [Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective O), top_inf_eq,
    top_inf_eq] at hmap
  intro m hm
  have hmcent : f m ∈ Subgroup.centralizer ((Z.map f : Subgroup (X ⧸ O)) :
      Set (X ⧸ O)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨z, hz, rfl⟩
    have hmem : ⁅z, m⁆ ∈ O := hcomm (Subgroup.commutator_mem_commutator (hZN hz) hm)
    have h1 : ⁅f z, f m⁆ = 1 := by
      rw [← map_commutatorElement (f := f)]
      exact MonoidHom.mem_ker.mp (by rwa [hker])
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hmcent' : f m ∈ (Subgroup.centralizer (Z : Set X)).map f := by
    rw [hmap]
    exact hmcent
  obtain ⟨c, hc, hcf⟩ := Subgroup.mem_map.mp hmcent'
  have hO : c⁻¹ * m ∈ O := by
    rw [← hker]
    exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hcf]; simp)
  have hmul : c * (c⁻¹ * m) = m := by group
  rw [← hmul]
  exact Subgroup.mul_mem_sup hc hO

private lemma normalizer_sup_of_normal_eq_top {S N₀ : Subgroup X} (hS : IsSylowOf 3 S ⊤)
    (hN₀ : N₀.Normal) (hSN : S ≤ N₀) :
    Subgroup.normalizer (S : Set X) ⊔ N₀ = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : N₀.Normal := hN₀
  have hSyl : IsSylowOf 3 S N₀ := by
    have h := hS.inf_of_le_normalizer (K := ⊤) (N := N₀) le_top
      (le_of_eq (Subgroup.normalizer_eq_top (H := N₀)).symm)
    rwa [inf_eq_left.mpr hSN] at h
  obtain ⟨P, hP⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hPmap : (P : Subgroup ↥N₀).map N₀.subtype = S := by
    rw [hP, Subgroup.map_subgroupOf_eq_of_le hSN]
  have h := Sylow.normalizer_sup_eq_top P
  rwa [hPmap] at h

theorem top_le_sup_pPrimeCore_of_weaklyClosed {X : Type} [Group X] [Finite X]
    (hK332 : UCK.K332ThreeAb) (hK : CFSG.Open.IsKGroup X) {S Z₁ Z₂ B Y : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤) (hSe : CFSG.Open.IsElemAbelian 3 S)
    (hS27 : Nat.card S = 27) (hZ₁S : Z₁ ≤ S) (hZ₂S : Z₂ ≤ S) (hZ₁ : Nat.card Z₁ = 3)
    (hZ₂ : Nat.card Z₂ = 3) (hZ₁₂ : Z₁ ≠ Z₂) (hw₁ : IsWeaklyClosedIn Z₁ S)
    (hw₂ : IsWeaklyClosedIn Z₂ S) (hB : B ≤ Subgroup.center X) (hgen : S ≤ Z₁ ⊔ Z₂ ⊔ B)
    (hC₁ : Subgroup.centralizer (Z₁ : Set X) ≤ Y)
    (hC₂ : Subgroup.centralizer (Z₂ : Set X) ≤ Y)
    (hN : Subgroup.normalizer (S : Set X) ≤ Y) :
    (⊤ : Subgroup X) ≤ Y ⊔ CFSG.pPrimeCore 3 X := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N₁ : Subgroup X := Subgroup.normalClosure (Z₁ : Set X)
  set N₂ : Subgroup X := Subgroup.normalClosure (Z₂ : Set X)
  haveI hN₁norm : N₁.Normal := Subgroup.normalClosure_normal
  haveI hN₂norm : N₂.Normal := Subgroup.normalClosure_normal
  haveI hBnorm : B.Normal := Subgroup.normal_of_le_center hB
  haveI hOnorm : (CFSG.pPrimeCore 3 X).Normal := CFSG.pPrimeCore_normal
  have hr₁ : CFSG.Open.pRank 3 N₁ = 1 :=
    pRank_normalClosure_eq_one hK332 hK hS hSe hS27 hZ₁S hZ₁ hw₁
  have hr₂ : CFSG.Open.pRank 3 N₂ = 1 :=
    pRank_normalClosure_eq_one hK332 hK hS hSe hS27 hZ₂S hZ₂ hw₂
  have h₁ : S ⊓ N₁ = Z₁ := inf_normalClosure_eq_of_pRank_eq_one hSe hZ₁S hZ₁ hr₁
  have h₂ : S ⊓ N₂ = Z₂ := inf_normalClosure_eq_of_pRank_eq_one hSe hZ₂S hZ₂ hr₂
  have hO : N₁ ⊓ N₂ ≤ CFSG.pPrimeCore 3 X :=
    inf_le_pPrimeCore_of_inf_sylow hS hN₁norm hN₂norm hZ₁ hZ₂ hZ₁₂ h₁ h₂
  have hcomm : ⁅N₁, N₂⁆ ≤ CFSG.pPrimeCore 3 X :=
    (Subgroup.commutator_le_inf N₁ N₂).trans hO
  have hZ₁3 : IsPGroup 3 Z₁ := IsPGroup.of_card (n := 1) (by rw [hZ₁]; norm_num)
  have hZ₂3 : IsPGroup 3 Z₂ := IsPGroup.of_card (n := 1) (by rw [hZ₂]; norm_num)
  have hN₂le : N₂ ≤ Subgroup.centralizer (Z₁ : Set X) ⊔ CFSG.pPrimeCore 3 X :=
    le_centralizer_sup_pPrimeCore_of_commutator_le (M := N₂) (N := N₁) (Z := Z₁)
      Subgroup.le_normalClosure hZ₁3 hcomm
  have hcomm' : ⁅N₂, N₁⁆ ≤ CFSG.pPrimeCore 3 X := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  have hN₁le : N₁ ≤ Subgroup.centralizer (Z₂ : Set X) ⊔ CFSG.pPrimeCore 3 X :=
    le_centralizer_sup_pPrimeCore_of_commutator_le (M := N₁) (N := N₂) (Z := Z₂)
      Subgroup.le_normalClosure hZ₂3 hcomm'
  set N₀ : Subgroup X := ((N₁ ⊔ N₂) ⊔ B) ⊔ CFSG.pPrimeCore 3 X with hN₀
  haveI hN₀norm : N₀.Normal := hN₀.symm ▸ inferInstance
  have hSN₀ : S ≤ N₀ := by
    have hZN : Z₁ ⊔ Z₂ ≤ N₁ ⊔ N₂ := sup_le
      (Subgroup.le_normalClosure.trans le_sup_left)
      (Subgroup.le_normalClosure.trans le_sup_right)
    have hZB : Z₁ ⊔ Z₂ ⊔ B ≤ (N₁ ⊔ N₂) ⊔ B := sup_le_sup_right hZN B
    rw [hN₀]
    exact hgen.trans (hZB.trans le_sup_left)
  have hN₀le : N₀ ≤ Y ⊔ CFSG.pPrimeCore 3 X := by
    rw [hN₀]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) le_sup_right
    · exact hN₁le.trans (sup_le_sup_right hC₂ _)
    · exact hN₂le.trans (sup_le_sup_right hC₁ _)
    · exact ((hB.trans (Subgroup.center_le_centralizer (Z₁ : Set X))).trans hC₁).trans
        le_sup_left
  have hfratt : Subgroup.normalizer (S : Set X) ⊔ N₀ = ⊤ :=
    normalizer_sup_of_normal_eq_top hS hN₀norm hSN₀
  rw [← hfratt]
  exact sup_le (hN.trans le_sup_left) hN₀le

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
