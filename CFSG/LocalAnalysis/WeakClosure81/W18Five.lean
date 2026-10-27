module

public import CFSG.LocalAnalysis.WeakClosure81.W18Borel
public import CFSG.LocalAnalysis.WeakClosure81.W18Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (relPPrimeCore_le relPPrimeCore_normal)

variable {G : Type} [Group G] [Finite G]

@[expose] def Shape185 {Q : Type} [Group Q] [Finite Q] (H : Subgroup Q) : Prop :=
  Shape512 H ∧ ¬ Shape512Four H

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem coprime_card_kerMV (c : MinCex183 D V₀ V H i)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) :
    Nat.Coprime 3 (Nat.card ↥(kerMV V H)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcop
  have h3 : 3 ∣ Nat.card ↥(kerMV V H) := by
    by_contra hn
    exact hcop (Nat.prime_three.coprime_iff_not_dvd.mpr hn)
  have hKH : kerMV V H ≤ H := kerMV_le_self V H
  have hHnormK : H ≤ normalizer (kerMV V H : Set G) :=
    Subgroup.le_normalizer_iff.mpr fun x hx y hy => conj_mem_kerMV hx hy
  have hKn : ((kerMV V H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHnormK
  have hKM : kerMV V H ≤ D.M := by
    rw [← c.hyp.setting.normalizer_eq]
    exact kerMV_le_normalizer V H
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(kerMV V H)) 3 h3
  have hxG : orderOf (x : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  have hxK : Subgroup.zpowers (x : G) ≤ kerMV V H := by
    rw [Subgroup.zpowers_le]
    exact x.2
  have hPcard : Nat.card (Subgroup.zpowers (x : G)) = 3 ^ 1 := by
    rw [Nat.card_zpowers, hxG, pow_one]
  have hP : IsPGroup 3 (Subgroup.zpowers (x : G)) := IsPGroup.of_card hPcard
  obtain ⟨S, hS, hxS⟩ := exists_isSylowIn_ge 3 hxK hP
  have h3S : 3 ∣ Nat.card S := by
    have h1 : Nat.card (Subgroup.zpowers (x : G)) ∣ Nat.card S :=
      Subgroup.card_dvd_of_le hxS
    rw [hPcard] at h1
    simpa using h1
  have hNM : ∀ n ∈ normalizer (S : Set G), n ∈ D.M := by
    intro n hn
    by_contra hnM
    apply hsp.2.2 n hnM
    have hSle : S ≤ D.M ⊓ D.M.map (MulAut.conj n).toMonoidHom := by
      intro s hs
      refine ⟨hKM (hS.le hs), Subgroup.mem_map.mpr ⟨n⁻¹ * s * n, ?_, ?_⟩⟩
      · apply hKM (hS.le _)
        have := (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * s * n)).mpr
        apply this
        simpa [mul_assoc] using hs
      · simp [MulAut.conj_apply, mul_assoc]
    exact h3S.trans (Subgroup.card_dvd_of_le hSle)
  apply c.hyp.notLe
  intro h hh
  obtain ⟨k, hk, n, hn, rfl⟩ := frattini_argument hKH hKn hS hh
  exact D.M.mul_mem (hKM hk) (hNM n hn.2)

theorem kerMV_eq_relPPrimeCore (c : MinCex183 D V₀ V H i)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hQM : relPPrimeCore 3 H ≤ D.M) : kerMV V H = relPPrimeCore 3 H := by
  have hKH : kerMV V H ≤ H := kerMV_le_self V H
  have hHnormK : H ≤ normalizer (kerMV V H : Set G) :=
    Subgroup.le_normalizer_iff.mpr fun x hx y hy => conj_mem_kerMV hx hy
  have hKn : ((kerMV V H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHnormK
  apply le_antisymm
  · exact le_sSup ⟨hKH, hKn, c.coprime_card_kerMV hsp⟩
  · have hHnormQ : H ≤ normalizer (relPPrimeCore 3 H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (relPPrimeCore_le H)).mp
        (relPPrimeCore_normal (p := 3) (by norm_num) H)
    refine le_kerMV_of_normal (relPPrimeCore_le H) (fun h hh n hn => ?_)
      (by rw [c.hyp.setting.normalizer_eq]; exact hQM)
    exact (Subgroup.mem_normalizer_iff.mp (hHnormQ hh) n).mp hn

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
