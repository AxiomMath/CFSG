module

public import CFSG.RankThree.PartTwo.Sec21.Item2129Res2ProofS
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQTools
import CFSG.RankThree.PartTwo.Sec21.Item2119End2Proof2128
import CFSG.RankThree.PartTwo.Sec21.Item2119End5Proof2127C
import CFSG.ThirdParty.BrauerInduction.Background.Group.PDecomposition

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2129Res2Proof

open CFSG.ABGLocalTools (IsSylowOf)

namespace Loc2129

variable {G : Type} [Group G] [Finite G] {F H Q Y : Subgroup G} {e d : G}

omit [Finite G] in
theorem conj_mem_centralizer (hL : Loc2129 F H Q Y e d) {y x : G} (hy : y ∈ Y)
    (hx : x ∈ Subgroup.centralizer (H : Set G)) :
    y * x * y⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have h1 : y⁻¹ * h * y ∈ H := by
    have h2 := hL.conj_mem_H (Y.inv_mem hy) hh
    rwa [inv_inv] at h2
  have h2 := Subgroup.mem_centralizer_iff.mp hx _ h1
  calc h * (y * x * y⁻¹) = y * ((y⁻¹ * h * y) * x) * y⁻¹ := by group
    _ = y * (x * (y⁻¹ * h * y)) * y⁻¹ := by rw [h2]
    _ = y * x * y⁻¹ * h := by group

theorem card_inf_centralizer_Q (hL : Loc2129 F H Q Y e d) :
    81 ≤ Nat.card (Q ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha, had⟩ := hL.exists_mem_H_not_mem
  have hdQ : d ∈ Q := hL.le_F_Q (hL.le_H hL.mem_d)
  have hd3 : d ^ 3 = 1 := hL.pow_H d hL.mem_d
  have hcomm := Item2119End2Proof.comm_mem_zpowers hL.extra_Q hdQ hL.ne_one_d hd3 hL.conj_d
  have haQ : a ∈ Q := hL.le_F_Q (hL.le_H ha)
  have hzc : ∀ z ∈ Subgroup.zpowers d, ∀ q ∈ Q, q * z * q⁻¹ = z := by
    intro z hz q hq
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hL.conj_d q hq]
  let μ : Q →* G :=
    { toFun := fun q => a⁻¹ * ((q : G) * a * (q : G)⁻¹)
      map_one' := by simp
      map_mul' := fun q q' => by
        simp only [Subgroup.coe_mul]
        have hm : a⁻¹ * ((q' : G) * a * (q' : G)⁻¹) ∈ Subgroup.zpowers d := hcomm a haQ q' q'.2
        have hq := hzc _ hm q q.2
        calc a⁻¹ * ((q : G) * q' * a * ((q : G) * q')⁻¹)
            = a⁻¹ * ((q : G) * a * (q : G)⁻¹) *
              ((q : G) * (a⁻¹ * ((q' : G) * a * (q' : G)⁻¹)) * (q : G)⁻¹) := by group
          _ = a⁻¹ * ((q : G) * a * (q : G)⁻¹) * (a⁻¹ * ((q' : G) * a * (q' : G)⁻¹)) := by
            rw [hq] }
  have hμ : ∀ q : Q, μ q = a⁻¹ * ((q : G) * a * (q : G)⁻¹) := fun q => rfl
  have h1 := Item2119End6Proof.card_eq_card_ker_mul_card_range μ
  have h2 : Nat.card μ.range ≤ 3 := by
    have hle : μ.range ≤ Subgroup.zpowers d := by
      rintro _ ⟨q, rfl⟩
      rw [hμ]
      exact hcomm a haQ q q.2
    have h3 := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, orderOf_eq_prime hd3 hL.ne_one_d] at h3
  have hker : μ.ker.map Q.subtype ≤ Q ⊓ Subgroup.centralizer (H : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    have hq1 : a⁻¹ * ((q : G) * a * (q : G)⁻¹) = 1 := by rw [← hμ]; exact hq
    have hqa : (q : G) * a = a * q := (kap_eq_one_iff (e := a)).mp hq1
    have hqd : (q : G) * d = d * q := by
      calc (q : G) * d = q * d * (q : G)⁻¹ * q := by group
        _ = d * q := by rw [hL.conj_d q q.2]
    exact ⟨q.2, hL.mem_centralizer_H ha had hqa hqd⟩
  have h4 := Subgroup.card_le_of_le hker
  rw [Subgroup.card_map_of_injective Q.subtype_injective] at h4
  rw [hL.card_Q] at h1
  have h5 : 81 ≤ Nat.card μ.ker := by
    by_contra hlt
    push Not at hlt
    have : Nat.card μ.ker * Nat.card μ.range ≤ 80 * 3 := Nat.mul_le_mul (by omega) h2
    omega
  omega

theorem exists_kap_eq_of_cent (hL : Loc2129 F H Q Y e d) {h : G} (hh : h ∈ H) :
    ∃ x ∈ Y ⊓ Subgroup.centralizer (H : Set G), e⁻¹ * (x * e * x⁻¹) = h := by
  by_cases h1 : h = 1
  · exact ⟨1, (Y ⊓ Subgroup.centralizer (H : Set G)).one_mem, by rw [h1]; group⟩
  obtain ⟨q, ⟨hqQ, hqH⟩, hqF⟩ : ∃ q ∈ Q ⊓ Subgroup.centralizer (H : Set G), q ∉ F := by
    by_contra hall
    push Not at hall
    have h2 := Subgroup.card_le_of_le
      (show Q ⊓ Subgroup.centralizer (H : Set G) ≤ F from fun q hq => hall q hq)
    rw [hL.card_F] at h2
    have h3 := hL.card_inf_centralizer_Q
    omega
  have hqY : q ∈ Y := hL.le_Q hqQ
  have hκq : e⁻¹ * (q * e * q⁻¹) ≠ 1 := by
    intro hq1
    apply hqF
    have hqC := hL.mem_centralizer_F hqH (kap_eq_one_iff.mp hq1)
    exact hL.le_F _ (isPGroup_zpowers (n := 1) (by simpa using hL.pow_Q q hqQ))
      (Subgroup.zpowers_le.mpr hqC) (Subgroup.mem_zpowers q)
  obtain ⟨m, hmY, -, hm⟩ := hL.trans _ (hL.kap_mem hqY) _ hh hκq h1
  refine ⟨m * q * m⁻¹, ⟨Y.mul_mem (Y.mul_mem hmY hqY) (Y.inv_mem hmY),
    hL.conj_mem_centralizer hmY hqH⟩, ?_⟩
  rw [hL.kap_conj hqY hqH hmY, hm]

theorem exists_R (hL : Loc2129 F H Q Y e d)
    (hB : ∀ x ∈ Y ⊓ Subgroup.centralizer (H : Set G),
      ∀ o ∈ Y ⊓ Subgroup.centralizer (F : Set G),
        (∃ n : ℕ, x ^ 3 ^ n = 1) → Nat.Coprime (orderOf o) 3 → x * o = o * x) :
    ∃ R : Subgroup G, IsR2129 H Y R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKY : Y ⊓ Subgroup.centralizer (H : Set G) ≤ Y := inf_le_left
  have hKH : Y ⊓ Subgroup.centralizer (H : Set G) ≤ Subgroup.centralizer (H : Set G) :=
    inf_le_right
  have hFK : F ≤ Y ⊓ Subgroup.centralizer (H : Set G) := le_inf hL.le_F_Y hL.le_F_centralizer
  obtain ⟨P, hP, hFP⟩ := Item2119End5Proof.exists_isSylowOf_ge hFK hL.isPGroup_F
  have hPK : P ≤ Y ⊓ Subgroup.centralizer (H : Set G) := hP.le
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hPY : P ≤ Y := hPK.trans hKY
  have hPH : P ≤ Subgroup.centralizer (H : Set G) := hPK.trans hKH
  have hsurj : Function.Surjective (hL.kapHom _ hKY hKH) := by
    intro h
    obtain ⟨x, hxK, hxh⟩ := hL.exists_kap_eq_of_cent h.2
    exact ⟨⟨x, hxK⟩, Subtype.ext (by rw [hL.kapHom_apply]; exact hxh)⟩
  have hPsurj : ∀ h ∈ H, ∃ p ∈ P, e⁻¹ * (p * e * p⁻¹) = h := by
    have hidx := Subgroup.index_map_dvd
      (H := P.subgroupOf (Y ⊓ Subgroup.centralizer (H : Set G))) hsurj
    have hnd : ¬ 3 ∣ (P.subgroupOf (Y ⊓ Subgroup.centralizer (H : Set G))).index :=
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hP).2.2
    have hdvd9 : ((P.subgroupOf (Y ⊓ Subgroup.centralizer (H : Set G))).map
        (hL.kapHom _ hKY hKH)).index ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hL.card_H]
      exact Subgroup.index_dvd_card (G := H) (H := _)
    obtain ⟨k, hk, hke⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd9
    have hk0 : k = 0 := by
      by_contra hk0
      apply hnd
      rw [hke] at hidx
      exact (dvd_pow_self 3 hk0).trans hidx
    rw [hk0, pow_zero, Subgroup.index_eq_one] at hke
    intro h hh
    have hmem : (⟨h, hh⟩ : H) ∈ (P.subgroupOf (Y ⊓ Subgroup.centralizer (H : Set G))).map
        (hL.kapHom _ hKY hKH) := by
      rw [hke]
      exact Subgroup.mem_top _
    obtain ⟨p, hp, hph⟩ := hmem
    refine ⟨p, Subgroup.mem_subgroupOf.mp hp, ?_⟩
    have h2 := congrArg Subtype.val hph
    rw [hL.kapHom_apply] at h2
    exact h2
  have hPnK : ∀ g ∈ Y ⊓ Subgroup.centralizer (H : Set G), ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    intro g hg x hx
    obtain ⟨p, hpP, hpg⟩ := hPsurj _ (hL.kap_mem (hKY hg))
    have hpK := hPK hpP
    have hcK : p⁻¹ * g ∈ Y ⊓ Subgroup.centralizer (H : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hpK) hg
    have hκc : e⁻¹ * (p⁻¹ * g * e * (p⁻¹ * g)⁻¹) = 1 := by
      have h1 : hL.kapHom _ hKY hKH ⟨p, hpK⟩ = hL.kapHom _ hKY hKH ⟨g, hg⟩ :=
        Subtype.ext (by rw [hL.kapHom_apply, hL.kapHom_apply, hpg])
      have h2 : hL.kapHom _ hKY hKH ((⟨p, hpK⟩ : (Y ⊓ Subgroup.centralizer (H : Set G) :
          Subgroup G))⁻¹ * ⟨g, hg⟩) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      have h3 := hL.kapHom_apply hKY hKH ((⟨p, hpK⟩ : (Y ⊓ Subgroup.centralizer (H : Set G) :
          Subgroup G))⁻¹ * ⟨g, hg⟩)
      rw [h2, Subgroup.coe_one] at h3
      exact h3.symm
    have hcC : p⁻¹ * g ∈ Subgroup.centralizer (F : Set G) :=
      hL.mem_centralizer_F (hKH hcK) (kap_eq_one_iff.mp hκc)
    have hcYF : p⁻¹ * g ∈ Y ⊓ Subgroup.centralizer (F : Set G) := ⟨hKY hcK, hcC⟩
    have hfin : IsOfFinOrder (p⁻¹ * g) := isOfFinOrder_of_finite _
    have hdec : Group.pRegular 3 (p⁻¹ * g) * Group.pSingular 3 (p⁻¹ * g) = p⁻¹ * g :=
      Group.pDecomp' 3 hfin
    have hcr_mem : Group.pRegular 3 (p⁻¹ * g) ∈ Subgroup.zpowers (p⁻¹ * g) := by
      unfold Group.pRegular
      exact Subgroup.zpow_mem_zpowers _ _
    have hcs_mem : Group.pSingular 3 (p⁻¹ * g) ∈ Subgroup.zpowers (p⁻¹ * g) := by
      unfold Group.pSingular
      exact Subgroup.zpow_mem_zpowers _ _
    have hcrYF := Subgroup.zpowers_le.mpr hcYF hcr_mem
    have hcsYF := Subgroup.zpowers_le.mpr hcYF hcs_mem
    have hcr3 : Nat.Coprime (orderOf (Group.pRegular 3 (p⁻¹ * g))) 3 :=
      Group.isPRegular_pRegular 3 hfin
    obtain ⟨n, hn⟩ := Group.isPSingular_pSingular 3 (p⁻¹ * g)
    have hcs3 : Group.pSingular 3 (p⁻¹ * g) ^ 3 ^ n = 1 := by
      rw [← hn]
      exact pow_orderOf_eq_one _
    have hcsF : Group.pSingular 3 (p⁻¹ * g) ∈ F :=
      hL.le_F _ (isPGroup_zpowers hcs3) (Subgroup.zpowers_le.mpr hcsYF.2)
        (Subgroup.mem_zpowers _)
    have hcsP := hFP hcsF
    set cr := Group.pRegular 3 (p⁻¹ * g) with hcr
    set cs := Group.pSingular 3 (p⁻¹ * g) with hcs
    have hx'P : cs * x * cs⁻¹ ∈ P := P.mul_mem (P.mul_mem hcsP hx) (P.inv_mem hcsP)
    obtain ⟨k, hk⟩ := hP3 ⟨cs * x * cs⁻¹, hx'P⟩
    have hx'3 : (cs * x * cs⁻¹) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcomm := hB (cs * x * cs⁻¹) (hPK hx'P) cr hcrYF ⟨k, hx'3⟩ hcr3
    have hg' : g = p * (cr * cs) := by rw [hdec]; group
    have e1 : p * (cr * cs) * x * (p * (cr * cs))⁻¹ =
        p * (cr * (cs * x * cs⁻¹) * cr⁻¹) * p⁻¹ := by group
    have e2 : cr * (cs * x * cs⁻¹) * cr⁻¹ = cs * x * cs⁻¹ := by
      rw [← hcomm]
      group
    rw [hg', e1, e2]
    exact P.mul_mem (P.mul_mem hpP hx'P) (P.inv_mem hpP)
  have hPnY : Y ≤ Subgroup.normalizer (P : Set G) := by
    intro y hy
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hxK := hPK hx
    have hyxK : y * x * y⁻¹ ∈ Y ⊓ Subgroup.centralizer (H : Set G) :=
      ⟨Y.mul_mem (Y.mul_mem hy (hKY hxK)) (Y.inv_mem hy),
        hL.conj_mem_centralizer hy (hKH hxK)⟩
    obtain ⟨k, hk⟩ := hP3 ⟨x, hx⟩
    have hx3 : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hyx3 : (y * x * y⁻¹) ^ 3 ^ k = 1 := by
      rw [conj_pow, hx3]
      group
    have hZN : Subgroup.zpowers (y * x * y⁻¹) ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype fun z hz => hPnK _ hyxK z hz)
    have hsup3 : IsPGroup 3 (Subgroup.zpowers (y * x * y⁻¹) ⊔ P : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers hyx3) hP3 hZN
    have heq := hP.eq_of_le le_sup_right (sup_le (Subgroup.zpowers_le.mpr hyxK) hPK) hsup3
    rw [← heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hP243 : Nat.card P = 243 := by
    have h1 := Item2119End6Proof.card_eq_card_ker_mul_card_range (hL.kapHom P hPY hPH)
    have hrange : (hL.kapHom P hPY hPH).range = ⊤ := by
      rw [MonoidHom.range_eq_top]
      intro h
      obtain ⟨p, hp, hph⟩ := hPsurj h h.2
      exact ⟨⟨p, hp⟩, Subtype.ext (by rw [hL.kapHom_apply]; exact hph)⟩
    have hker : Nat.card (hL.kapHom P hPY hPH).ker = 27 := by
      have heq : (hL.kapHom P hPY hPH).ker.map P.subtype = F := by
        apply le_antisymm
        · rintro _ ⟨p, hp, rfl⟩
          have hp1 : hL.kapHom P hPY hPH p = 1 := hp
          have hp2 : e⁻¹ * ((p : G) * e * (p : G)⁻¹) = 1 := by
            rw [← hL.kapHom_apply hPY hPH p, hp1, Subgroup.coe_one]
          have hpC := hL.mem_centralizer_F (hPH p.2) (kap_eq_one_iff.mp hp2)
          exact hL.le_F _ (hP3.to_le (Subgroup.zpowers_le.mpr p.2))
            (Subgroup.zpowers_le.mpr hpC) (Subgroup.mem_zpowers _)
        · intro f hf
          refine ⟨⟨f, hFP hf⟩, ?_, rfl⟩
          show hL.kapHom P hPY hPH ⟨f, hFP hf⟩ = 1
          apply Subtype.ext
          rw [hL.kapHom_apply, Subgroup.coe_one]
          exact kap_eq_one_iff.mpr (hL.comm_F f hf e hL.mem_e)
      calc Nat.card (hL.kapHom P hPY hPH).ker
          = Nat.card ((hL.kapHom P hPY hPH).ker.map P.subtype) :=
            (Subgroup.card_map_of_injective P.subtype_injective).symm
        _ = Nat.card F := by rw [heq]
        _ = 27 := hL.card_F
    calc Nat.card P = Nat.card (hL.kapHom P hPY hPH).ker *
          Nat.card (hL.kapHom P hPY hPH).range := h1
      _ = 27 * 9 := by rw [hker, hrange, Subgroup.card_top, hL.card_H]
      _ = 243 := by norm_num
  exact ⟨P, ⟨hPY, hPnY, hP3, hP243, hPH⟩⟩

end Loc2129

end CFSG.RankThree.PartTwo.Sec21.Item2129Res2Proof
