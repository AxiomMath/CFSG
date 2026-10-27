module

public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofCent
import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def autQuotTwo {G : Type} [Group G] (Y₀ : Subgroup G) :
    ↥(Subgroup.normalizer (Y₀ : Set G)) →* MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) :=
  (Proof1517.quotAut (CFSG.pCore 2 ↥Y₀)).comp Y₀.normalizerMonoidHom

@[expose] noncomputable def Step1519HessE9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y → (∀ X ∈ scriptY2 A, ¬ L ≤ X) →
      IsSimpleGroup ↥L →
      ∀ m p : ℕ, Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m →
        (1 ≤ m → ¬ 3 ∣ m) → IsChoice1519 m p → 3 < p →
        ∀ Y₀ ∈ scriptY0 A (lB A), p ∣ Nat.card (MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) →
          ∃ E : Subgroup G, E ≤ A ∧ Nat.card E = 9 ∧
            ∀ e : ↥(Subgroup.normalizer (Y₀ : Set G)), (e : G) ∈ E → (e : G) ≠ 1 →
              ¬ p ∣ Nat.card (Subgroup.centralizer
                ({autQuotTwo Y₀ e} : Set (MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))))

namespace Proof1518R2

theorem mem_sectionCentralizer_of_autQuotTwo_eq_one {G : Type} [Group G] {Y₀ : Subgroup G}
    (g : ↥(Subgroup.normalizer (Y₀ : Set G))) (h1 : autQuotTwo Y₀ g = 1) :
    (g : G) ∈ Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
      (CFSG.Open.pCoreOf 2 Y₀) := by
  refine ⟨g.2, fun y hy => ?_⟩
  set N := CFSG.pCore 2 ↥Y₀ with hN
  have h2 := congrArg (fun φ : MulAut (↥Y₀ ⧸ N) => φ ((⟨y, hy⟩ : ↥Y₀) : ↥Y₀ ⧸ N)) h1
  simp only [MulAut.one_apply] at h2
  set z : ↥Y₀ := Y₀.normalizerMonoidHom g ⟨y, hy⟩ with hz
  have hzv : (z : G) = g * y * g⁻¹ := Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have h3 : ((z : ↥Y₀) : ↥Y₀ ⧸ N) = ((⟨y, hy⟩ : ↥Y₀) : ↥Y₀ ⧸ N) := h2
  have h4 : z⁻¹ * ⟨y, hy⟩ ∈ N := QuotientGroup.eq.mp h3
  have h5 : z * (⟨y, hy⟩ : ↥Y₀)⁻¹ ∈ N := by
    have hnorm : N.Normal := inferInstance
    have := hnorm.conj_mem _ (N.inv_mem h4) ⟨y, hy⟩
    simpa [mul_assoc] using this
  have h6 : ((z * (⟨y, hy⟩ : ↥Y₀)⁻¹ : ↥Y₀) : G) ∈ CFSG.Open.pCoreOf 2 Y₀ := by
    refine ⟨z * (⟨y, hy⟩ : ↥Y₀)⁻¹, ?_, rfl⟩
    exact h5
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hzv] at h6
  exact h6

end Proof1518R2

open Proof1518R2

theorem step1519CentAut_of (hE : Step1519HessE9) : Step1519CentAut := by
  intro G _ _ A c L h Y hctx hno hs m p hiso h3m hch hp3 Y₀ hY₀ hdvd R hR
  obtain ⟨E, hEA, hE9, hEact⟩ := hE G A c L h Y hctx hno hs m p hiso h3m hch hp3 Y₀ hY₀ hdvd
  have hp : p.Prime := hch.1
  have : Fact p.Prime := ⟨hp⟩
  set N := Subgroup.normalizer (Y₀ : Set G) with hNdef
  have hRN : R ≤ N := hR.1.2
  have hRp : IsPGroup p ↥R := (isPiSubgroup_piOf_iff hp R).mp hR.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hR.1.1.1.2.2
  have hAN : A ≤ N := hY₀.1.1.2
  have hAel : CFSG.Assembly.IsElemAbelian 3 A := h.toSec13Data.isElemAbelian
  have hEel : CFSG.Assembly.IsElemAbelian 3 E :=
    ⟨⟨⟨fun x y => Subtype.ext (by
      have h' := congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hEA x.2⟩ ⟨y, hEA y.2⟩)
      simpa using h')⟩⟩, fun x hx => hAel.2 x (hEA hx)⟩
  set ρ := autQuotTwo Y₀ with hρ
  have hR'p : IsPGroup p ↥(R.subgroupOf N) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm
  have hE'el : CFSG.Open.IsElemAbelian 3 (E.subgroupOf N) :=
    let h' := Proof1520.isElemAbelian_subgroupOf N hEel
    ⟨h'.1, h'.2⟩
  have hE'9 : 3 ^ (1 + 1) ≤ Nat.card ↥(E.subgroupOf N) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEA.trans hAN)).toEquiv, hE9]
    norm_num
  have hE'R' : E.subgroupOf N ≤ Subgroup.normalizer ((R.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    intro x hx
    have hxR : (x : G) ∈ Subgroup.normalizer (R : Set G) :=
      hAR (hEA (Subgroup.mem_subgroupOf.mp hx))
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp hxR (y : G))
  have hcop : Nat.Coprime 3 (Nat.card ↥(R.subgroupOf N)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR'p
    rw [hk]
    refine Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp).mpr ?_)
    omega
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three (E.subgroupOf N) (R.subgroupOf N) hE'el hE'9 hE'R' hcop
  have hker : R.subgroupOf N ≤ ρ.ker := by
    rw [← hgen]
    refine iSup₂_le fun S hS => ?_
    obtain ⟨hSE, hS3⟩ := hS
    have hSnt : Nontrivial ↥S := by
      rw [← Finite.one_lt_card_iff_nontrivial, hS3]
      norm_num
    obtain ⟨⟨s, hsS⟩, hs1⟩ := exists_ne (1 : ↥S)
    have hs1' : s ≠ 1 := fun h0 => hs1 (Subtype.ext h0)
    have hsE : ((s : ↥N) : G) ∈ E := Subgroup.mem_subgroupOf.mp (hSE hsS)
    have hsG : ((s : ↥N) : G) ≠ 1 := fun h0 => hs1' (Subtype.ext h0)
    have hnd := hEact s hsE hsG
    intro x hx
    obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxs : s * x = x * s := Subgroup.mem_centralizer_iff.mp hxC s hsS
    have hρx : ρ x ∈ Subgroup.centralizer ({ρ s} : Set (MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxs]
    obtain ⟨k, hk⟩ := hR'p ⟨x, hxR⟩
    have hxk : x ^ p ^ k = 1 := congrArg Subtype.val hk
    have ho1 : orderOf (ρ x) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxk, map_one])
    have ho2 : orderOf (ρ x) ∣ Nat.card (Subgroup.centralizer
        ({ρ s} : Set (MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)))) := by
      have := orderOf_dvd_natCard (⟨ρ x, hρx⟩ : ↥(Subgroup.centralizer
        ({ρ s} : Set (MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)))))
      rwa [Subgroup.orderOf_mk] at this
    have hcop' : Nat.Coprime (p ^ k) (Nat.card (Subgroup.centralizer
        ({ρ s} : Set (MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))))) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
    exact MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop' ho1 ho2))
  intro r hr
  have h1 : ρ ⟨r, hRN hr⟩ = 1 := hker (Subgroup.mem_subgroupOf.mpr hr)
  exact mem_sectionCentralizer_of_autQuotTwo_eq_one ⟨r, hRN hr⟩ h1

end CFSG.RankThree.PartTwo.Sec15
