module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIConfig
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1617
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailSylow
public import CFSG.RankThree.GF2n.Stroth80.Sec712Normalizes
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z1
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsCentre

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem exists_pre (hQM : Q ≤ M) (A' : Subgroup (Mbar M Q)) :
    ∃ A : Subgroup G, Q ≤ A ∧ A ≤ M ∧ bar M Q A = A' := by
  refine ⟨(A'.comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype, ?_, ?_, ?_⟩
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hQM hx⟩, ?_, rfl⟩
    show QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hQM hx⟩ ∈ A'
    have : QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hQM hx⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx)
    rw [this]; exact A'.one_mem
  · rintro x ⟨y, -, rfl⟩; exact y.2
  · have h1 : ((A'.comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype).subgroupOf M =
        A'.comap (QuotientGroup.mk' (Q.subgroupOf M)) :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    unfold bar
    rw [h1]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) A'

theorem bar_NormH0_eq (hc : Ctx M Q Z B) {Z0 : Subgroup G} (hQZ0 : Q ≤ Z0) (hZ0M : Z0 ≤ M) :
    bar M Q (NormH0 M Z Z0) = NormIn (bar M Q (H0 M Z)) (bar M Q Z0) := by
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQN : Q ≤ NormH0 M Z Z0 := fun q hq =>
    Subgroup.mem_inf.mpr ⟨hQH hq, Subgroup.le_normalizer (hQZ0 hq)⟩
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
  constructor
  · intro hx
    have hy : (y : G) ∈ NormH0 M Z Z0 := (mk_mem_bar_iff_sec4 hQN y).mp hx
    exact ⟨(mk_mem_bar_iff_sec4 hQH y).mpr (Subgroup.mem_inf.mp hy).1,
      mk_mem_normalizer_bar_of_normalizer hQZ0 y (Subgroup.mem_inf.mp hy).2⟩
  · rintro ⟨hx1, hx2⟩
    have hy1 : (y : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH y).mp hx1
    have hy2 : (y : G) ∈ Subgroup.normalizer (Z0 : Set G) :=
      mem_normalizer_of_mk_mem_normalizer_bar hQZ0 hZ0M y hx2
    exact (mk_mem_bar_iff_sec4 hQN y).mpr (Subgroup.mem_inf.mpr ⟨hy1, hy2⟩)

theorem le_of_normal_nilpotent_of_fstar {Y : Type*} [Group Y] [Finite Y] {P N' : Subgroup Y}
    [P.Normal] (hP : Group.IsNilpotent P) (hF : generalizedFitting Y = N') : P ≤ N' := by
  rw [← hF]
  have hPF : P ≤ generalizedFitting Y := by
    rw [generalizedFitting.eq_sup]
    exact le_sup_of_le_left (le_sSup ⟨inferInstance, hP⟩)
  exact hPF

theorem bar_mono' {S T : Subgroup G} (h : S ≤ T) : bar M Q S ≤ bar M Q T :=
  Subgroup.map_mono fun x hx => h hx

theorem Ctx.tiConfig (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hN2 : IsPGroup 2 ↥(bar M Q (hc.CN t)))
    (hMA : IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
      g ∈ Subgroup.normalizer (Z0 : Set G))
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))) :
    TIConfig (bar M Q (H0 M Z)) (bar M Q Z0) (bar M Q (hc.CN t)) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  have hZ0N : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hnormR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hRK : Rt M (LB M Q B) t ≤ NormH0 M Z Z0 := fun ρ hρ =>
    Subgroup.mem_inf.mpr ⟨hc.Rt_le_H0 t hρ, IsCentrePre.mem_normalizer hZ0 hnormR hρ⟩
  have hNK : hc.CN t ≤ NormH0 M Z Z0 := hNR.trans hRK
  have hQN : Q ≤ NormH0 M Z Z0 := fun q hq =>
    Subgroup.mem_inf.mpr ⟨hQH hq, Subgroup.le_normalizer (hQZ0 hq)⟩
  have hNM : hc.CN t ≤ M := fun x hx => hc.Rt_le_M t (hNR hx)
  have hKbar := bar_NormH0_eq hc hQZ0 hZ0M
  have hcommZ : ∀ a b : M, (a : G) ∈ Z0 → (b : G) ∈ Rt M (LB M Q B) t →
      QuotientGroup.mk' (Q.subgroupOf M) a * QuotientGroup.mk' (Q.subgroupOf M) b =
        QuotientGroup.mk' (Q.subgroupOf M) b * QuotientGroup.mk' (Q.subgroupOf M) a :=
    fun a b ha hb => step716_mk_mul_comm (hZ0.comm_mem ha hb)
  refine
    { V_le := bar_mono' hZ0H0
      V_ne_bot := ?_
      V_pgroup := hN2.to_le (bar_mono' hZ0N)
      V_comm := ?_
      ti := ?_
      N_le := ?_
      N_normal := ?_
      N_pgroup := hN2
      pcore_le := ?_
      cent_le := ?_
      VN_comm := ?_
      maxAb := ?_ }
  · obtain ⟨s, hsZ, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
    intro hbot
    have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hZ0M hsZ⟩ ∈ bar M Q Z0 :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hsZ)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hsQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hmem))
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    exact hcommZ a b (Subgroup.mem_subgroupOf.mp ha) (hZ0.le (Subgroup.mem_subgroupOf.mp hb))
  · intro g x hx hx1 hgx
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) g
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
    have hx'Z : (x' : G) ∈ Z0 := (mk_mem_bar_iff_sec4 hQZ0 x').mp hx
    have hx'Q : (x' : G) ∉ Q := fun h => hx1 ((QuotientGroup.eq_one_iff x').mpr h)
    rw [← map_inv, ← map_mul, ← map_mul, mk_mem_bar_iff_sec4 hQZ0] at hgx
    exact mk_mem_normalizer_bar_of_normalizer hQZ0 g' (hTI g' g'.2 x' hx'Z hx'Q hgx)
  · rw [← hKbar]
    exact bar_mono' hNK
  · intro k hk
    rw [← hKbar] at hk
    obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) k
    have hk' : (k' : G) ∈ NormH0 M Z Z0 := (mk_mem_bar_iff_sec4 hQN k').mp hk
    have hcn := sec7_conj_CN_eq hZt hZcard hc hs hZ0 hk'
    have hQCN : Q ≤ hc.CN t := hc.Q_le_CN' ht
    exact mk_mem_normalizer_bar_of_normalizer hQCN k' (conjSubgroup_eq_self_iff.mp hcn)
  · intro P hP hPn hP2
    rw [← hKbar] at hP hPn
    have hPnorm : (P.subgroupOf (bar M Q (NormH0 M Z Z0))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hP).mpr fun k hk => hPn k hk
    have hPnil : Group.IsNilpotent ↥(P.subgroupOf (bar M Q (NormH0 M Z Z0))) :=
      ((hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hP).symm)).isNilpotent
    have := le_of_normal_nilpotent_of_fstar hPnil hF
    intro x hx
    have hx' := this (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hP hx⟩ : bar M Q (NormH0 M Z Z0)) ∈
      P.subgroupOf (bar M Q (NormH0 M Z Z0)))
    exact Subgroup.mem_subgroupOf.mp hx'
  · intro k hk hkc
    rw [← hKbar] at hk
    have hcent : (⟨k, hk⟩ : bar M Q (NormH0 M Z Z0)) ∈
        Subgroup.centralizer (generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) :
          Set ↥(bar M Q (NormH0 M Z Z0))) := by
      rw [hF]
      intro y hy
      have hy' : (y : Mbar M Q) ∈ bar M Q (hc.CN t) := Subgroup.mem_subgroupOf.mp hy
      exact Subtype.ext (hkc y hy').symm
    have h2 := CFSG.centralizer_generalizedFitting_le _ hcent
    rw [hF] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  · intro x hx n hn
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hn
    exact hcommZ a b (Subgroup.mem_subgroupOf.mp ha) (hNR (Subgroup.mem_subgroupOf.mp hb))
  · intro A' hVA hAK hAn hAab
    rw [← hKbar] at hAK hAn
    obtain ⟨A, hQA, hAM, hbarA⟩ := exists_pre hQM A'
    have hZ0A : Z0 ≤ A := by
      intro x hx
      have : QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hZ0M hx⟩ ∈ A' := hVA
        (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx))
      rw [← hbarA] at this
      exact (mk_mem_bar_iff_sec4 hQA _).mp this
    have hAKe : A ≤ NormH0 M Z Z0 := by
      intro x hx
      have : QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hAM hx⟩ ∈ bar M Q (NormH0 M Z Z0) :=
        hAK (hbarA ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx))
      exact (mk_mem_bar_iff_sec4 hQN _).mp this
    have hAkn : ∀ k ∈ NormH0 M Z Z0, conjSubgroup k A = A := by
      intro k hk
      have hkM : k ∈ M := hk.1.1
      have hmk : QuotientGroup.mk' (Q.subgroupOf M) ⟨k, hkM⟩ ∈ bar M Q (NormH0 M Z Z0) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
      have hn := hAn _ hmk
      rw [← hbarA] at hn
      exact conjSubgroup_eq_self_iff.mpr
        (mem_normalizer_of_mk_mem_normalizer_bar hQA hAM ⟨k, hkM⟩ hn)
    have hAab' : ∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ ∈ Q := by
      intro x hx y hy
      have hx' : QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hAM hx⟩ ∈ A' :=
        hbarA ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
      have hy' : QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hAM hy⟩ ∈ A' :=
        hbarA ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)
      have hc' := hAab _ hx' _ hy'
      have h1 : QuotientGroup.mk' (Q.subgroupOf M)
          ⁅(⟨x, hAM hx⟩ : M), (⟨y, hAM hy⟩ : M)⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hc'
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    have hAeq := hMA.2.2.2 A hZ0A hAKe hAkn hAab'
    rw [← hbarA, hAeq]

end CFSG.RankThree.GF2n.Stroth80
