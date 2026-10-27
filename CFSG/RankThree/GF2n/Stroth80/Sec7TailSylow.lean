module

public import CFSG.RankThree.GF2n.Stroth80.SylowTransitive
public import CFSG.RankThree.GF2n.Stroth80.Sec4Model
public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem mk_mem_normalizer_bar_of_normalizer [(Q.subgroupOf M).Normal] {S : Subgroup G}
    (hQS : Q ≤ S) (y : M) (hy : (y : G) ∈ Subgroup.normalizer (S : Set G)) :
    QuotientGroup.mk' (Q.subgroupOf M) y ∈ Subgroup.normalizer (bar M Q S : Set (Mbar M Q)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) n
  rw [← map_inv, ← map_mul, ← map_mul, mk_mem_bar_iff_sec4 hQS, mk_mem_bar_iff_sec4 hQS]
  exact Subgroup.mem_normalizer_iff.mp hy (z : G)

theorem mem_normalizer_of_mk_mem_normalizer_bar [(Q.subgroupOf M).Normal] {L : Subgroup G}
    (hQL : Q ≤ L) (hLM : L ≤ M) (y : M)
    (hN : QuotientGroup.mk' (Q.subgroupOf M) y ∈
      Subgroup.normalizer (bar M Q L : Set (Mbar M Q))) :
    (y : G) ∈ Subgroup.normalizer (L : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have h1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨z, hLM hz⟩ : M) ∈ bar M Q L :=
    (mk_mem_bar_iff_sec4 hQL _).mpr hz
  have h2 := (Subgroup.mem_normalizer_iff.mp hN _).mp h1
  rw [← map_inv, ← map_mul, ← map_mul] at h2
  exact (mk_mem_bar_iff_sec4 hQL _).mp h2

theorem sylow_le_normalizer_bar_Z0 [(Q.subgroupOf M).Normal] {L Z0 : Subgroup G}
    (hQL : Q ≤ L) (hLM : L ≤ M) (hQZ : Q ≤ Z0)
    (hN : ∀ ν ∈ M, ν ∈ Subgroup.normalizer (L : Set G) → ν ∈ Subgroup.normalizer (Z0 : Set G))
    {P : Subgroup (Mbar M Q)} (hP : P ≤ Subgroup.normalizer (bar M Q L : Set (Mbar M Q))) :
    P ≤ Subgroup.normalizer (bar M Q Z0 : Set (Mbar M Q)) := by
  intro p hp
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) p
  exact mk_mem_normalizer_bar_of_normalizer hQZ y
    (hN y y.2 (mem_normalizer_of_mk_mem_normalizer_bar hQL hLM y (hP hp)))

theorem Z0_normalizes_of_nat (hNR : Sec7NormZ0Statement) (hZV : Sec7ZVStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
      (t : G), Sec7Hyp hc n t → ¬ OmegaMinusNat hc t 2 →
      ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
        g ∈ Subgroup.normalizer (Z0 : Set G) := by
  intro G _ _ M Q Z B hc n t hs hnom Z0 hZ0 g hg u hu huQ hgu
  have hgN : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 (M.inv_mem hg)
  have huQ' : g * u * g⁻¹ ∉ Q := by
    intro h
    apply huQ
    have h4 := (Subgroup.mem_normalizer_iff.mp hgN (g * u * g⁻¹)).mp h
    have h3 : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
    rwa [h3] at h4
  have hZu : Ut Q Z u = Vt M (LB M Q B) B Z t := hZV G M Q Z B hc n t hs Z0 hZ0 u hu huQ
  have hZu' : Ut Q Z (g * u * g⁻¹) = Vt M (LB M Q B) B Z t :=
    hZV G M Q Z B hc n t hs Z0 hZ0 (g * u * g⁻¹) hgu huQ'
  have hconj := Ut_conj_of_normalizes (hc.conj_Q_eq hg) (hc.conj_Z_eq hg) u
  have hgV : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    ((congrArg (conjSubgroup g) hZu).symm.trans hconj.symm).trans hZu'
  exact hNR G M Q Z B hc n t hs hnom Z0 hZ0 g hg (conjSubgroup_eq_self_iff.mp hgV)

theorem exists_sylow_Z0_of_trans [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hno : ¬ Conc71abcd hc n t) (hZc : Sec7CentreMpStatement)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hTr : Stroth73bTransStatement)
    (hSyl : ∃ P : Sylow 2 (Mbar M Q), P.toSubgroup ≤
      Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q))) :
    ∃ P : Sylow 2 (Mbar M Q),
      P.toSubgroup ≤ Subgroup.normalizer (bar M Q Z0 : Set (Mbar M Q)) := by
  obtain ⟨P, hP⟩ := hSyl
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htQ : t ∉ Q := hs.toSec5.notQ
  have htM : t ∈ M := hc.LB_le_M ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZL : Z0 ≤ LB M Q B := fun z hz => (hZc G M Q Z B hc n t hs Z0 hZ0 z hz).1
  have hZM : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQF : Q ≤ Fgen M Q (LB M Q B) Z0 := Q_le_Fgen sec39_Q_le_LB hc.hyp.Q_normal.1
  have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
  have hPF : P.toSubgroup ≤
      Subgroup.normalizer (bar M Q (Fgen M Q (LB M Q B) Z0) : Set (Mbar M Q)) := by
    intro p hp
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) p
    have hyL := mem_normalizer_of_mk_mem_normalizer_bar hQL hc.LB_le_M y (hP hp)
    refine mk_mem_normalizer_bar_of_normalizer hQF y
      (Subgroup.mem_normalizer_fintype fun x hx => ?_)
    exact Fgen_conj_mem hc y.2 hyL hx
  by_cases hF : Fgen M Q (LB M Q B) Z0 = Z0
  · exact ⟨P, by rw [← hF]; exact hPF⟩
  · have hZF : Z0 ≤ Fgen M Q (LB M Q B) Z0 := Z0_le_Fgen hZL hZM Q
    refine exists_sylow_normalizer_of_trans (bar M Q (Fgen M Q (LB M Q B) Z0)) (bar M Q Z0) ?_ ?_
      (s := QuotientGroup.mk' (Q.subgroupOf M) ⟨t, htM⟩) ?_ ?_ ?_ ?_ P hPF
    · intro x hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
      exact (mk_mem_bar_iff_sec4 hQF y).mpr (hZF ((mk_mem_bar_iff_sec4 hQZ0 y).mp hx))
    · intro x hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
      have hyF := (mk_mem_bar_iff_sec4 hQF y).mp hx
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (y ^ 2)).mpr
        (hc.sq_mem_Q_of_mem_LB (Fgen_le M Q (LB M Q B) Z0 hyF))
    · exact (mk_mem_bar_iff_sec4 hQZ0 ⟨t, htM⟩).mpr htZ0
    · intro h
      exact htQ ((QuotientGroup.eq_one_iff (⟨t, htM⟩ : M)).mp h)
    · intro g u hu hu1 hgu
      obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) g
      obtain ⟨u', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) u
      have hu'Z := (mk_mem_bar_iff_sec4 hQZ0 u').mp hu
      have hu'Q : (u' : G) ∉ Q := fun h => hu1 ((QuotientGroup.eq_one_iff u').mpr h)
      rw [← map_inv, ← map_mul, ← map_mul, mk_mem_bar_iff_sec4 hQZ0] at hgu
      exact mk_mem_normalizer_bar_of_normalizer hQZ0 g' (hTI g' g'.2 u' hu'Z hu'Q hgu)
    · intro a ha ha1
      obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) a
      have ha'F := (mk_mem_bar_iff_sec4 hQF a').mp ha
      have ha'Q : (a' : G) ∉ Q := fun h => ha1 ((QuotientGroup.eq_one_iff a').mpr h)
      have htF : t ∈ Fgen M Q (LB M Q B) Z0 :=
        Subgroup.subset_closure ⟨ht, t, htZ0, ConjMod.of_mem htM⟩
      obtain ⟨g, hgM, hgF, hq⟩ := hTr G M Q Z B hc n t hs hno Z0 hZ0 hF t htF a' ha'F htQ ha'Q
      refine ⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨g, hgM⟩,
        mk_mem_normalizer_bar_of_normalizer hQF ⟨g, hgM⟩ hgF, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      refine QuotientGroup.eq_iff_div_mem.mpr (Subgroup.mem_subgroupOf.mpr ?_)
      have h1 := Q.inv_mem hq
      simpa [div_eq_mul_inv, mul_assoc] using h1

end CFSG.RankThree.GF2n.Stroth80
