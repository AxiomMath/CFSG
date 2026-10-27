module

public import CFSG.RankThree.PartOne.S11b.Sec109
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionRank
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore
public import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.ComponentClassification

namespace Sec109

@[expose] def Sec65LnTwo : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (n p : ℕ), StatedClassicalModel L .PSL n 2 1 → p.Prime →
    5 ≤ p → evenRank L ≤ 3 → 2 ≤ localRank p L → p = 7 ∧ (n = 6 ∨ n = 7)

@[expose] def LnTwoOuter : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (n : ℕ), StatedClassicalModel L .PSL n 2 1 →
    Subgroup.center L = ⊥ ∧ Nat.card (OuterAutomorphisms.Outer L) ≤ 2

@[expose] def LnTwoSylowSeven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L B : Subgroup G) (n : ℕ), (n = 6 ∨ n = 7) →
    StatedClassicalModel ↥L .PSL n 2 1 → B ≤ L → IsElementaryAbelian 7 B → Nat.card B = 49 →
    StructureB L B

theorem inner_of_pow_prime_eq_one {T : Type*} [Group T] [Finite T]
    (hout : Nat.card (OuterAutomorphisms.Outer T) ≤ 4) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {α : MulAut T} (hα : α ^ p = 1) : ∃ t : T, MulAut.conj t = α := by
  set q := QuotientGroup.mk' (OuterAutomorphisms.inner T) α
  have hqp : orderOf q ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hα, map_one])
  have hqle : orderOf q ≤ 4 :=
    (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard q)).trans hout
  have hq1 : orderOf q = 1 := by
    rcases (Nat.dvd_prime hp).mp hqp with h | h
    · exact h
    · omega
  exact (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp hq1)

theorem setup_of_inspections (hS : SchreierFor InCatalog) (h65 : Sec65LnTwo)
    (hout : LnTwoOuter) (hsyl : LnTwoSylowSeven) : Setup := by
  classical
  intro G _ _ p A h L hL n hmodel
  have hp := sectionTenSetup_prime h
  have hp3 := sectionTenSetup_three_lt h
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by decide)
  obtain ⟨c, hcA, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp
    ((sectionTenZeroStar_subset p A).2.2.1 hL.2)
  obtain ⟨hq, hAL, hker⟩ := moving_maximal_data_at hS h hL hcA hc1 hLc
  obtain ⟨hZ, hOutL⟩ := hout ↥L n hmodel
  have hAe : IsElementaryAbelian p A := h.2.2.2.2.2.2.1
  have hAcard : Nat.card A = p ^ 3 := h.2.2.2.2.2.2.2.1
  have hApow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (A := A) a ha
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨-, S0, hS0L, hS01, hS02, hAS0, -⟩ := hL.1
  have hevG : localRank p G ≤ 3 :=
    (CFSG.RankThree.OddKernel.localRank_le_evenRank hp (by omega)).trans
      (sectionTenSetup_evenRank_eq h).le
  have hevL : evenRank ↥L ≤ 3 := (Sec9A.evenRank_subgroup_le L).trans
    (sectionTenSetup_evenRank_eq h).le
  have hθ : aschbacherSolvableCore p L = ⊥ := by
    have := theta_le_center_of_quasisimple hp hq
    rw [hZ] at this
    exact le_bot_iff.mp this
  have hθ' : inSubgroup (aschbacherSolvableCore p) L = ⊥ := by
    rw [inSubgroup, hθ, Subgroup.map_bot]
  have hinjconj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
    intro l l' hll'
    have h1 : ∀ y : L, l * y * l⁻¹ = l' * y * l'⁻¹ := fun y => by
      have := congrArg (fun φ : MulAut L => φ y) hll'
      simpa [MulAut.conj_apply] using this
    have hmem : l'⁻¹ * l ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := h1 y
      calc y * (l'⁻¹ * l) = l'⁻¹ * (l' * y * l'⁻¹) * l := by group
        _ = l'⁻¹ * (l * y * l⁻¹) * l := by rw [← this]
        _ = l'⁻¹ * l * y := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm
  let α : A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
  have hα : ∀ (a : A) (l : L), ((α a l : L) : G) = (a : G) * (l : G) * (a : G)⁻¹ := by
    intro a l
    change ((L.normalizerMonoidHom ⟨(a : G), hAL a.2⟩ l : L) : G) = _
    exact coe_normalizerMonoidHom_apply ⟨(a : G), hAL a.2⟩ l
  have hin : ∀ a : A, ∃ l : L, MulAut.conj l = α a := by
    intro a
    refine inner_of_pow_prime_eq_one (by omega) hp hp5 ?_
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (hApow a a.2)
    rw [this, map_one]
  have hactG : ∀ (a : A) (l : L), MulAut.conj l = α a → ∀ y : L,
      (l : G) * (y : G) * (l : G)⁻¹ = (a : G) * (y : G) * (a : G)⁻¹ := by
    intro a l hl y
    have h1 : ((MulAut.conj l y : L) : G) = ((α a y : L) : G) := by rw [hl]
    rw [MulAut.conj_apply, hα] at h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hdec : ∀ a : A, ∃ l : L, ∃ z : G, (a : G) = l * z ∧ (∀ y : L, z * y = y * z) ∧
      MulAut.conj l = α a := by
    intro a
    obtain ⟨l, hl⟩ := hin a
    refine ⟨l, (l : G)⁻¹ * (a : G), by group, fun y => ?_, hl⟩
    have h1 := hactG a l hl y
    calc (l : G)⁻¹ * (a : G) * (y : G) = (l : G)⁻¹ * ((a : G) * (y : G) * (a : G)⁻¹) * (a : G) := by
          group
      _ = (l : G)⁻¹ * ((l : G) * (y : G) * (l : G)⁻¹) * (a : G) := by rw [← h1]
      _ = (y : G) * ((l : G)⁻¹ * (a : G)) := by group
  set E : Subgroup L := α.range.comap (MulAut.conj : ↥L →* MulAut ↥L) with hE
  have hEmem : ∀ l : L, l ∈ E ↔ ∃ a : A, α a = MulAut.conj l := by
    intro l
    rw [hE, Subgroup.mem_comap, MonoidHom.mem_range]
  have hEcomm : ∀ l ∈ E, ∀ l' ∈ E, l * l' = l' * l := by
    intro l hl l' hl'
    obtain ⟨a, ha⟩ := (hEmem l).mp hl
    obtain ⟨a', ha'⟩ := (hEmem l').mp hl'
    apply hinjconj
    rw [map_mul, map_mul, ← ha, ← ha', ← map_mul, ← map_mul, hAe.is_comm.comm a a']
  have hEpow : ∀ l ∈ E, l ^ p = 1 := by
    intro l hl
    obtain ⟨a, ha⟩ := (hEmem l).mp hl
    apply hinjconj
    have : a ^ p = 1 := Subtype.ext (hApow a a.2)
    rw [map_pow, ← ha, ← map_pow, this, map_one, map_one]
  have hEN : ∀ l ∈ E, (l : G) ∈ normalizer (S0 : Set G) := by
    intro l hl
    obtain ⟨a, ha⟩ := (hEmem l).mp hl
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have haN := Subgroup.mem_normalizer_iff.mp (hAS0 a.2) g
    constructor
    · intro hg
      have hgL : g ∈ L := hS0L hg
      rw [hactG a l ha.symm ⟨g, hgL⟩]
      exact haN.mp hg
    · intro hg
      have hgL : g ∈ L := by
        have h1 : (l : G)⁻¹ * ((l : G) * g * (l : G)⁻¹) * (l : G) ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem l.2) (hS0L hg)) l.2
        simpa [mul_assoc] using h1
      rw [hactG a l ha.symm ⟨g, hgL⟩] at hg
      exact haN.mpr hg
  have hEA : ∀ l ∈ E, ∀ a' ∈ A, (l : G) * a' = a' * l := by
    intro l hl a' ha'
    obtain ⟨l', z, hdecomp, hz, hl'⟩ := hdec ⟨a', ha'⟩
    have hl'E : l' ∈ E := (hEmem l').mpr ⟨⟨a', ha'⟩, hl'.symm⟩
    have hcomm' : (l : G) * l' = l' * l := congrArg Subtype.val (hEcomm l hl l' hl'E)
    calc (l : G) * a' = (l : G) * (l' * z) := by rw [← hdecomp]
      _ = ((l : G) * l') * z := by rw [mul_assoc]
      _ = (l' * (l : G)) * z := by rw [hcomm']
      _ = l' * ((l : G) * z) := by rw [mul_assoc]
      _ = l' * (z * (l : G)) := by rw [← hz l]
      _ = (l' * z) * l := by rw [mul_assoc]
      _ = a' * l := by rw [← hdecomp]
  have : Fact p.Prime := ⟨hp⟩
  have hEleA : ∀ l ∈ E, (l : G) ∈ A := by
    intro l hl
    by_contra hnA
    have hlcomm : ∀ s ∈ ((A : Set G) ∪ {(l : G)}), ∀ t ∈ ((A : Set G) ∪ {(l : G)}),
        Commute s t := by
      intro s hs t ht
      rcases hs with hs | hs <;> rcases ht with ht | ht
      · exact hAcomm s hs t ht
      · rw [Set.mem_singleton_iff] at ht
        subst ht
        exact (hEA l hl s hs).symm
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact hEA l hl t ht
      · rw [Set.mem_singleton_iff] at hs ht
        subst hs
        subst ht
        exact Commute.refl _
    have hlpow : (l : G) ^ p = 1 := by simpa using congrArg Subtype.val (hEpow l hl)
    have hgen : ∀ s ∈ ((A : Set G) ∪ {(l : G)}), s ^ p = 1 := by
      rintro s (hs | hs)
      · exact hApow s hs
      · rw [Set.mem_singleton_iff] at hs
        rw [hs]
        exact hlpow
    set X : Subgroup G := Subgroup.closure ((A : Set G) ∪ {(l : G)}) with hX
    have hXc : IsMulCommutative X := ⟨⟨fun x y => Subtype.ext
      (CFSG.RankThree.CentralCover.commute_of_mem_closure hlcomm x.2 y.2).eq⟩⟩
    have hXpow : ∀ x ∈ X, x ^ p = 1 := fun x hx =>
      CFSG.RankThree.CentralCover.pow_eq_one_of_mem_closure hlcomm hgen hx
    have hXp : IsPGroup p X := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hXpow x x.2)⟩
    obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hXp
    have hAX : A ≤ X := fun a ha => Subgroup.subset_closure (Or.inl ha)
    have hlX : (l : G) ∈ X := Subgroup.subset_closure (Or.inr rfl)
    have hr4 : 4 ≤ r := by
      by_contra hr3
      have hdvd := Subgroup.card_dvd_of_le hAX
      rw [hAcard, hr] at hdvd
      have h3 : 3 ≤ r := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
      have hr3'' : r = 3 := by omega
      have hAXeq : A = X := Subgroup.eq_of_le_of_card_ge hAX (by rw [hAcard, hr, hr3''])
      exact hnA (hAXeq ▸ hlX)
    have hXU : X ≤ normalizer (S0 : Set G) := (Subgroup.closure_le _).mpr (by
      rintro s (hs | hs)
      · exact hAS0 hs
      · rw [Set.mem_singleton_iff] at hs
        rw [hs]
        exact hEN l hl)
    have := Sec9Excl.le_localRank_of_normalizes hp.one_lt hS01 hS02 hXc hXpow hr hXU
    omega
  have hBE : E.map L.subtype = A ⊓ L := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨hEleA l hl, l.2⟩
    · rintro ⟨hxA, hxL⟩
      refine ⟨⟨x, hxL⟩, (hEmem ⟨x, hxL⟩).mpr ⟨⟨x, hxA⟩, ?_⟩, rfl⟩
      ext y
      rw [hα, MulAut.conj_apply]
      simp
  have hcord : orderOf c = p := orderOf_eq_prime (hApow c hcA) hc1
  have hkerE : α.ker.map A.subtype = zpowers c := by
    rw [← hker]
    ext x
    rw [mem_thetaQuotientCentralizer_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, hAL a.2, fun k hk => ?_⟩
      rw [hθ', Subgroup.mem_bot]
      have h1 : α a ⟨k, hk⟩ = ⟨k, hk⟩ := by
        have := MonoidHom.mem_ker.mp ha
        rw [this]
        rfl
      have h2 := congrArg Subtype.val h1
      rw [hα] at h2
      change (a : G) * k * (a : G)⁻¹ * k⁻¹ = 1
      simp only at h2
      rw [h2]
      group
    · rintro ⟨hxA, -, hxk⟩
      refine ⟨⟨x, hxA⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      ext y
      rw [hα]
      have := hxk y y.2
      rw [hθ', Subgroup.mem_bot] at this
      simp only [MulAut.one_apply]
      calc (x : G) * (y : G) * (x : G)⁻¹ = (x * (y : G) * x⁻¹ * (y : G)⁻¹) * (y : G) := by group
        _ = (y : G) := by rw [this, one_mul]
  have hkercard : Nat.card α.ker = p := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, hkerE, Nat.card_zpowers, hcord]
  have hEcard : Nat.card E = p ^ 2 := by
    have hrange : α.range ≤ (MulAut.conj : ↥L →* MulAut ↥L).range := by
      rintro _ ⟨a, rfl⟩
      obtain ⟨l, hl⟩ := hin a
      exact ⟨l, hl⟩
    have h2 : E.map (MulAut.conj : ↥L →* MulAut ↥L) = α.range := by
      rw [hE, Subgroup.map_comap_eq, inf_of_le_right hrange]
    have h1 : Nat.card E = Nat.card α.range := by
      rw [← h2, Subgroup.card_map_of_injective hinjconj]
    have h3 := Subgroup.card_ker_mul_card_range α
    rw [hkercard, hAcard] at h3
    have hp0 : 0 < p := hp.pos
    have : p * Nat.card α.range = p * p ^ 2 := by rw [h3]; ring
    rw [h1]
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  have hrank : 2 ≤ localRank p ↥L := by
    have hU : S0.subgroupOf L ≠ ⊥ := by
      intro hbot
      apply hS01
      rw [← Subgroup.map_subgroupOf_eq_of_le hS0L, hbot, Subgroup.map_bot]
    have hU2 : IsPGroup 2 (S0.subgroupOf L) := hS02.comap_subtype
    have hEc : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hEcomm a.1 a.2 b.1 b.2)⟩⟩
    have hEU : E ≤ normalizer ((S0.subgroupOf L : Subgroup L) : Set L) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro u
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have := Subgroup.mem_normalizer_iff.mp (hEN l hl) (u : G)
      simpa using this
    exact Sec9Excl.le_localRank_of_normalizes hp.one_lt hU hU2 hEc hEpow hEcard hEU
  obtain ⟨hp7, hn⟩ := h65 ↥L n p hmodel hp hp5 hevL hrank
  subst hp7
  have hBcard : Nat.card (A ⊓ L : Subgroup G) = 49 := by
    rw [← hBE, Subgroup.card_map_of_injective L.subtype_injective, hEcard]
    norm_num
  have hBe : IsElementaryAbelian 7 (A ⊓ L : Subgroup G) := by
    have hc : IsMulCommutative (A ⊓ L : Subgroup G) :=
      ⟨⟨fun x y => Subtype.ext (hAcomm x.1 x.2.1 y.1 y.2.1)⟩⟩
    refine { toIsMulCommutative := hc, exponent_dvd_p := ?_ }
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hApow x.1 x.2.1)
  have hABc : A = (A ⊓ L) ⊔ zpowers c := by
    apply le_antisymm
    · intro a ha
      obtain ⟨l, z, hdecomp, hz, hl⟩ := hdec ⟨a, ha⟩
      have hdecomp' : a = (l : G) * z := hdecomp
      have hlE : l ∈ E := (hEmem l).mpr ⟨⟨a, ha⟩, hl.symm⟩
      have hlA : (l : G) ∈ A := hEleA l hlE
      have hlmem : (l : G) ∈ A ⊓ L := ⟨hlA, l.2⟩
      have hzeq : z = (l : G)⁻¹ * a := by rw [hdecomp']; group
      have hzA : z ∈ A := by
        rw [hzeq]
        exact A.mul_mem (A.inv_mem hlA) ha
      have hzc : z ∈ zpowers c := by
        rw [← hker, mem_thetaQuotientCentralizer_iff]
        refine ⟨hzA, ?_, fun k hk => ?_⟩
        · refine Subgroup.centralizer_le_normalizer (L : Set G) ?_
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          exact (hz ⟨g, hg⟩).symm
        · rw [hθ', Subgroup.mem_bot]
          have := hz ⟨k, hk⟩
          calc z * k * z⁻¹ * k⁻¹ = (z * k) * z⁻¹ * k⁻¹ := rfl
            _ = (k * z) * z⁻¹ * k⁻¹ := by rw [this]
            _ = 1 := by group
      rw [hdecomp']
      exact Subgroup.mul_mem_sup hlmem hzc
    · exact sup_le inf_le_left ((Subgroup.zpowers_le).mpr hcA)
  exact ⟨c, A ⊓ L, ⟨h, rfl, hn, hmodel, hcA, hc1, ⟨hL, hLc⟩, rfl, hBcard, hABc,
    hsyl G L (A ⊓ L) n hn hmodel inf_le_right hBe hBcard⟩⟩

end Sec109

end CFSG.RankThree.PartOne
