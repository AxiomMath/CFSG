module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WA5Normal
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PImg
import CFSG.CharacterTheory.Burnside
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155NO

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem img148_eq_bot_of_le_pPrimeCore {A M X : Subgroup G} [(ker148 A M).Normal]
    (hX : X ≤ pPrimeCoreOf 3 M) : img148 A M X = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr (hX (Subgroup.mem_subgroupOf.mp hx))

theorem img148_deltaZero_eq {A M : Subgroup G} [(ker148 A M).Normal] {e : G}
    (hdec : deltaZero A (lB A) M = pPrimeCoreOf 3 (deltaZero A (lB A) M) ⊔
      deltaZero A (lB A) (M ⊓ Subgroup.centralizer ({e} : Set G)))
    (hN : Ronan148W.NoNormal3 ↥(img148 A M (deltaZero A (lB A) M))) :
    img148 A M (deltaZero A (lB A) (M ⊓ Subgroup.centralizer ({e} : Set G))) =
      img148 A M (deltaZero A (lB A) M) := by
  have hO : pPrimeCoreOf 3 (deltaZero A (lB A) M) ≤ pPrimeCoreOf 3 M :=
    Proof155P.pPrimeCoreOf_deltaZero_le hN
  have hbot : img148 A M (pPrimeCoreOf 3 (deltaZero A (lB A) M)) = ⊥ :=
    img148_eq_bot_of_le_pPrimeCore hO
  have hDM : deltaZero A (lB A) M ≤ M := deltaZero_le M
  have hcM : deltaZero A (lB A) (M ⊓ Subgroup.centralizer ({e} : Set G)) ≤ M :=
    (deltaZero_le _).trans inf_le_left
  have h1 : pPrimeCoreOf 3 (deltaZero A (lB A) M) ≤ M ⊔ A :=
    ((pPrimeCoreOf_le 3 _).trans hDM).trans le_sup_left
  have h2 : deltaZero A (lB A) (M ⊓ Subgroup.centralizer ({e} : Set G)) ≤ M ⊔ A :=
    hcM.trans le_sup_left
  have h3 := img148_sup (A := A) (Y := M) h1 h2
  rw [← hdec, hbot, bot_sup_eq] at h3
  exact h3.symm

theorem desc143_of_three_dvd {A : Subgroup G} (h143 : Ronan148Q.Item143Q A (lB A)) {e : G}
    (heA : e ∈ A) (he1 : e ≠ 1) (heΩ : Subgroup.zpowers e ∉ omegaA A) {H : Subgroup G}
    (hH : H ≤ delta A (lB A) (Subgroup.centralizer ({e} : Set G))) (h3 : 3 ∣ Nat.card H) :
    Ronan148Q.Desc143Case2QAt A (lB A) e := by
  obtain ⟨Q, hQ⟩ := maxInvariantPiSubgroups_nonempty
    (delta A (lB A) (Subgroup.centralizer ({e} : Set G))) A (piCompl 3)
  obtain ⟨-, hcase⟩ := h143 e heA he1 heΩ Q hQ
  rcases hcase with h1 | h2
  · exfalso
    have hN₁ : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G))) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
    have hN₂ : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
    have hN₂C : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
        Subgroup.centralizer ({e} : Set G) :=
      (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heA))
    have hCN₁ : Subgroup.centralizer ({e} : Set G) ≤
        Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) : Set G) :=
      le_normalizer_pPrimeCoreOf 3 _
    rw [h1] at hH
    have hd := card_sup_dvd_card_mul (hN₂C.trans hCN₁)
    rw [sup_comm] at hd
    have h3' := h3.trans ((Subgroup.card_dvd_of_le hH).trans hd)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3' with h | h
    · exact hN₂ h
    · exact hN₁ h
  · exact h2

omit [Finite G] in
private theorem relIndex_dvd_relIndex_of_le_normalizer {H S Y : Subgroup G} (hHS : H ≤ S)
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) : Y.relIndex H ∣ Y.relIndex S := by
  haveI : (Y.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hSY
  rw [← Subgroup.relIndex_subgroupOf hHS]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

theorem le_normalizer_of_desc {A : Subgroup G} {e d : G} (heA : e ∈ A) {X H : Subgroup G}
    (hΔ : delta A (lB A) (Subgroup.centralizer ({e} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X)
    (hinv : Ronan148Q.Inv143Q A e d X)
    (hH : H ≤ delta A (lB A) (Subgroup.centralizer ({e} : Set G))) :
    H ≤ Subgroup.normalizer
        ((pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) ⊔ X : Subgroup G) : Set G) ∧
      ¬ 3 ∣ ((pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) ⊔ X).subgroupOf H).index := by
  set Y : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) ⊔ X
  set D : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  have hΔ' : delta A (lB A) (Subgroup.centralizer ({e} : Set G)) = D ⊔ Y := by
    rw [hΔ, sup_right_comm, sup_comm]
  have hDN : D ≤ Subgroup.normalizer (Y : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (hinv.centralizer_le heA)
  have hSN : D ⊔ Y ≤ Subgroup.normalizer (Y : Set G) := sup_le hDN Subgroup.le_normalizer
  have hHS : H ≤ D ⊔ Y := hΔ' ▸ hH
  refine ⟨hHS.trans hSN, ?_⟩
  have h1 : Y.relIndex H ∣ Y.relIndex (D ⊔ Y) :=
    relIndex_dvd_relIndex_of_le_normalizer hHS hSN
  have h2 : Y.relIndex (D ⊔ Y) ∣ Nat.card D := by
    have hmul : Y.relIndex (D ⊔ Y) * Nat.card ↥(Y ⊓ (D ⊔ Y)) = Nat.card ↥(D ⊔ Y) :=
      Subgroup.relIndex_mul_card _ _
    rw [inf_eq_left.mpr le_sup_right] at hmul
    have hc := card_sup_dvd_card_mul hDN
    rw [← hmul] at hc
    exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hc
  have hD3 : ¬ 3 ∣ Nat.card D :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  exact fun h3 => hD3 (h3.trans (h1.trans h2))

private theorem isSolvable_of_primes_two_five {K : Type*} [Group K] [Finite K]
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card K → p = 2 ∨ p = 5) : Group.IsSolvable K := by
  haveI := Fintype.ofFinite K
  have hn0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hsupp : (Nat.card K).factorization.support ⊆ ({2, 5} : Finset ℕ) := by
    rw [Nat.support_factorization]
    intro p hp
    simpa using h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hprod := Nat.factorization_prod_pow_eq_self hn0
  rw [Finsupp.prod_of_support_subset _ hsupp _ (by simp), Finset.prod_pair (by norm_num)] at hprod
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    (by norm_num : Nat.Prime 5) (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hprod.symm)

theorem img148_inf_eq {A M H Y : Subgroup G} [(ker148 A M).Normal] (hHM : H ≤ M)
    (hperf : Group.IsPerfect ↥(img148 A M H))
    (hpr : ∀ p : ℕ, p.Prime → p ∣ Nat.card (img148 A M H) → p = 2 ∨ p = 3 ∨ p = 5)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (hind : ¬ 3 ∣ (Y.subgroupOf H).index) :
    img148 A M (H ⊓ Y) = img148 A M H := by
  have hNP : img148 A M (H ⊓ Y) ≤ img148 A M H := img148_mono inf_le_left
  have hHN : H ≤ Subgroup.normalizer ((H ⊓ Y : Subgroup G) : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hh, hHY hh⟩
  haveI hnorm : ((img148 A M (H ⊓ Y)).subgroupOf (img148 A M H)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (img148_le_normalizer hHN)
  haveI := hperf
  set P := img148 A M H
  set N' := (img148 A M (H ⊓ Y)).subgroupOf P with hN'
  let f : ↥H →* ↥(M ⊔ A) ⧸ ker148 A M :=
    (QuotientGroup.mk' (ker148 A M)).comp (Subgroup.inclusion (hHM.trans le_sup_left))
  have hrange : f.range = P := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  let φ : ↥H →* ↥P := f.codRestrict P fun h => by
    rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨h, rfl⟩
  have hφ : Function.Surjective φ := by
    intro p
    have hp : (p : ↥(M ⊔ A) ⧸ ker148 A M) ∈ f.range := by
      rw [hrange]
      exact p.2
    obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp hp
    exact ⟨h, Subtype.ext hh⟩
  let χ : ↥H →* ↥P ⧸ N' := (QuotientGroup.mk' N').comp φ
  have hχ : Function.Surjective χ := (QuotientGroup.mk'_surjective N').comp hφ
  have hker : Y.subgroupOf H ≤ χ.ker := by
    intro h hh
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' N' (φ h) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
    exact mem_img148_iff.mpr ⟨(h : G), (hHM.trans le_sup_left) h.2,
      ⟨h.2, Subgroup.mem_subgroupOf.mp hh⟩, rfl⟩
  have hdiv : Nat.card (↥P ⧸ N') ∣ (Y.subgroupOf H).index := by
    have h1 : χ.ker.index = Nat.card (↥P ⧸ N') := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective χ hχ, Subgroup.card_top]
    rw [← h1]
    exact Subgroup.index_dvd_of_le hker
  have hKP : Nat.card (↥P ⧸ N') ∣ Nat.card P := Subgroup.card_quotient_dvd_card N'
  have h3 : ¬ 3 ∣ Nat.card (↥P ⧸ N') := fun h => hind (h.trans hdiv)
  have hsolv : Group.IsSolvable (↥P ⧸ N') := by
    refine isSolvable_of_primes_two_five fun p hp hpd => ?_
    rcases hpr p hp (hpd.trans hKP) with h | h | h
    · exact Or.inl h
    · subst h
      exact absurd hpd h3
    · exact Or.inr h
  have hsub : Subsingleton (↥P ⧸ N') := by
    by_contra hns
    haveI : Nontrivial (↥P ⧸ N') := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable (↥P ⧸ N') hsolv
  have hidx : N'.index = 1 := Nat.card_of_subsingleton (1 : ↥P ⧸ N')
  exact le_antisymm hNP (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp hidx))

end CFSG.RankThree.PartTwo.Sec15.Sylow155NO
