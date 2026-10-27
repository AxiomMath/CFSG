module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2014a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p2014c_inf_W_le {H C : Subgroup G} (hC : C ∈ CFSG.Quasithin.cComp H) :
    C ⊓ uc22p20eW H C ≤ CFSG.Quasithin.solvRad H := by
  have hCn : C ≤ normalizer ((C ⊓ uc22p20eW H C : Subgroup G) : Set G) := fun c hc => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hc) y
    have h2 := Subgroup.mem_normalizer_iff.1
      (uc22p20e_W_normalized hC (CFSG.Quasithin.le_cCompSpan hC hc)) y
    exact ⟨fun hy => ⟨h1.1 hy.1, h2.1 hy.2⟩, fun hy => ⟨h1.2 hy.1, h2.2 hy.2⟩⟩
  refine (CFSG.Quasithin.le_solvRad_of_subnormal_lt hC
    (CFSG.Quasithin.A3.subnormal_of_normal inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hCn))
    (lt_of_le_of_ne inf_le_left fun h => ?_)).trans
    (CFSG.Quasithin.solvRad_le_solvRad_of_subnormal (CFSG.Quasithin.subnormal_of_mem_cComp hC))
  have hCW : C ≤ uc22p20eW H C := (le_inf_iff.1 h.ge).2
  have hCR : C ≤ CFSG.Quasithin.solvRad H := by
    rw [← CFSG.Quasithin.perfect_of_mem_cComp hC, Subgroup.commutator_le]
    intro a ha b hb
    exact (hCW hb).1.2 a ha
  haveI : Group.IsSolvable ↥(CFSG.Quasithin.solvRad H) := CFSG.Quasithin.solvRad_isSolvable H
  exact CFSG.Quasithin.not_isSolvable_of_mem_cComp hC
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hCR)
      (Subgroup.inclusion_injective hCR))

theorem uc22p2014c_two_le_pRank {p : ℕ} (hp : p.Prime) {H : Subgroup G} {a c : G} (haH : a ∈ H)
    (hcH : c ∈ H) (hap : a ^ p = 1) (hcp : c ^ p = 1) (ha1 : a ≠ 1) (hca : c ∉ zpowers a)
    (hac : a * c = c * a) : 2 ≤ CFSG.Open.pRank p H := by
  have hc1 : c ≠ 1 := fun h => hca (h ▸ (zpowers a).one_mem)
  have hcomm : ∀ x ∈ zpowers a, ∀ y ∈ zpowers c, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow (hac : Commute a c) i j).eq
  have hdisj : Disjoint (zpowers a) (zpowers c) :=
    (uc22p20d_disjoint_zpowers p hp c hcp hc1 _ hca).symm
  have hpair : ({a, c} : Set G).Pairwise Commute := Set.pairwise_pair.2 fun _ => ⟨hac, hac.symm⟩
  haveI hEc : IsMulCommutative (closure ({a, c} : Set G)) := isMulCommutative_closure hpair
  have hE : closure ({a, c} : Set G) = zpowers a ⊔ zpowers c := by
    rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
  refine CFSG.SectionRank.le_pRank hp.one_lt (k := 2) ?_ ⟨hEc, fun y hy => ?_⟩ ?_
  · rw [hE]
    exact sup_le (zpowers_le.2 haH) (zpowers_le.2 hcH)
  · induction hy using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · exact hap
      · exact hcp
    | one => exact one_pow p
    | mul x y hx hy ihx ihy =>
      rw [(show Commute x y from setLike_mul_comm hx hy).mul_pow, ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  · rw [hE, uc22p20d_card_sup _ _ hcomm hdisj, uc22p20d_card_zpowers p hp a hap ha1,
      uc22p20d_card_zpowers p hp c hcp hc1, sq]

theorem uc22p2014c_eq_of_dvd_card (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    (h66 : UC6.R6_6 D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hsp : IsStronglyPEmbedded p D.M)
    {H : Subgroup G} (hH : H ∈ hSet D.T D.M) {C C' : Subgroup G}
    (hC : C ∈ CFSG.Quasithin.cComp H) (hC' : C' ∈ CFSG.Quasithin.cComp H)
    (hpC : p ∣ Nat.card C) (hpC' : p ∣ Nat.card C') : C = C' := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hne
  set R := CFSG.Quasithin.solvRad H with hRdef
  have hR : ¬ p ∣ Nat.card R := uc22p2014a_not_dvd_card_solvRad D hB h1930 hsp hH
  have hHR : H ≤ normalizer (R : Set G) := uc22p2014a_le_normalizer_solvRad H
  have hRH : R ≤ H := CFSG.Quasithin.solvRad_le H
  have hCH : C ≤ H := CFSG.Quasithin.le_of_mem_cComp hC
  have hC'H : C' ≤ H := CFSG.Quasithin.le_of_mem_cComp hC'
  have hcomm : ⁅C, C'⁆ ≤ R := uc22p20e_comm_le_solvRad hC hC' hne
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := C) p hpC
  obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := C') p hpC'
  rw [← Subgroup.orderOf_coe] at ha hl
  obtain ⟨r, hr, hlr⟩ := uc22p2014a_exists_mul_mem_centralizer hp hR ha (hHR (hCH a.2))
    (hHR (hC'H l.2)) (hcomm (Subgroup.commutator_mem_commutator a.2 l.2))
  have hpow : ∀ n : ℕ, ∃ r' ∈ R, ((l : G) * r) ^ n = (l : G) ^ n * r' := by
    intro n
    induction n with
    | zero => exact ⟨1, R.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨r', hr', e⟩ := ih
      refine ⟨(l : G)⁻¹ * r' * l * r, R.mul_mem ?_ hr, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.1 (hHR (H.inv_mem (hC'H l.2))) r').1 hr'
      · rw [pow_succ, e, pow_succ]
        group
  obtain ⟨r₁, hr₁, hc1⟩ := hpow (Nat.card R)
  obtain ⟨r₂, hr₂, hc2⟩ := hpow p
  have hlp : (l : G) ^ p = 1 := by rw [← hl]; exact pow_orderOf_eq_one _
  have hbp : ((l : G) * r) ^ p ∈ R := by rw [hc2, hlp, one_mul]; exact hr₂
  have hcp : (((l : G) * r) ^ Nat.card R) ^ p = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    have h : ((⟨_, hbp⟩ : R) ^ Nat.card R : R) = 1 := pow_card_eq_one'
    exact (SubmonoidClass.coe_pow _ _).symm.trans (congrArg Subtype.val h)
  have hcR : ((l : G) * r) ^ Nat.card R ∉ R := by
    intro hcR
    have hlm : (l : G) ^ Nat.card R ∈ R := by
      have e : (l : G) ^ Nat.card R = ((l : G) * r) ^ Nat.card R * r₁⁻¹ := by rw [hc1]; group
      rw [e]
      exact R.mul_mem hcR (R.inv_mem hr₁)
    have hcop : (orderOf (l : G)).Coprime (Nat.card R) := by
      rw [hl]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 hR
    have h1 : orderOf ((l : G) ^ Nat.card R) = p := by rw [hcop.orderOf_pow, hl]
    exact hR (h1 ▸ Subgroup.orderOf_dvd_natCard R hlm)
  have hcH : ((l : G) * r) ^ Nat.card R ∈ H := H.pow_mem (H.mul_mem (hC'H l.2) (hRH hr)) _
  have hca : ((l : G) * r) ^ Nat.card R ∉ zpowers (a : G) := by
    intro hca
    apply hcR
    have hcC : ((l : G) * r) ^ Nat.card R ∈ C := zpowers_le.2 a.2 hca
    refine uc22p2014c_inf_W_le hC ⟨hcC, ?_, CFSG.Quasithin.le_cCompSpan hC hcC⟩
    rw [hc1]
    refine (uc22p20eCentMod H C).mul_mem ⟨H.pow_mem (hC'H l.2) _, fun a' ha' =>
      hcomm (Subgroup.commutator_mem_commutator ha' (C'.pow_mem l.2 _))⟩ ⟨hRH hr₁, fun a' ha' => ?_⟩
    rw [commutatorElement_def]
    exact R.mul_mem ((Subgroup.mem_normalizer_iff.1 (hHR (hCH ha')) r₁).1 hr₁) (R.inv_mem hr₁)
  have hap : (a : G) ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one _
  have ha1 : (a : G) ≠ 1 := fun h => by
    rw [h, orderOf_one] at ha
    exact hp.one_lt.ne ha
  have hac : (a : G) * ((l : G) * r) ^ Nat.card R = ((l : G) * r) ^ Nat.card R * a :=
    Subgroup.mem_centralizer_iff.1 ((centralizer _).pow_mem hlr _) a (Set.mem_singleton _)
  have h2 := uc22p2014c_two_le_pRank hp (hCH a.2) hcH hap hcp ha1 hca hac
  have h1 := uc22p2014a_pRank_le_one D h66 hp hp2 hsp hH
  omega

theorem uc22p2014c_le_normalizer_of_dvd_card (D : Data G) (hB : ListBNonabelian)
    (h1930 : H1930 D) (h66 : UC6.R6_6 D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsp : IsStronglyPEmbedded p D.M) {H : Subgroup G} (hH : H ∈ hSet D.T D.M) {C : Subgroup G}
    (hC : C ∈ CFSG.Quasithin.cComp H) (hpC : p ∣ Nat.card C) : H ≤ normalizer (C : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcard : Nat.card (uc22p20bCj h C) = Nat.card C :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  exact (uc22p2014c_eq_of_dvd_card D hB h1930 h66 hp hp2 hsp hH hC (uc22p20b_cj_mem_cComp hC hh)
    hpC (hcard ▸ hpC)).symm

theorem uc22p2014c_mem_cComp_of_isQuasisimple (D : Data G) {H L : Subgroup G}
    (hL : L ∈ calLOf D.T D.M H) (hq : CFSG.Open.IsQuasisimple (Bar2 L)) :
    L ∈ CFSG.Quasithin.cComp H :=
  CFSG.Quasithin.cComp_mem_of_subnormal hL.2
    (uc22p20e_cComp_of_calC ⟨CFSG.Open.IsSubnormal.refl L, hL.1.2.1, hq⟩)

theorem uc22p2014c_exists_calLOf (D : Data G) (h204 : S20_4 D) (h1930 : H1930 D)
    {H : Subgroup G} (hH : H ∈ hSet D.T D.M) : ∃ L, L ∈ calLOf D.T D.M H := by
  by_contra hne
  push Not at hne
  have hbot : (⨆ L ∈ calLOf D.T D.M H, L : Subgroup G) = ⊥ :=
    iSup₂_eq_bot.2 fun L hL => (hne L hL).elim
  have e := h204 h1930 H hH
  rw [hbot] at e
  refine hH.2.1 fun h hh => ?_
  have hh' : h ∈ ((⊥ : Subgroup G) : Set G) * ((H ⊓ D.M : Subgroup G) : Set G) := by
    rw [e]
    exact hh
  obtain ⟨u, hu, v, hv, rfl⟩ := hh'
  rw [SetLike.mem_coe, Subgroup.mem_bot] at hu
  simpa [hu] using hv.2

end CFSG.LocalAnalysis.UniquenessCase.UC22
