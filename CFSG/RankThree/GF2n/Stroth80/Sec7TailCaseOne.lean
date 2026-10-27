module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseOneBar
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseOneAbstract
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailElemAbelianSq
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveYBase

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem sec717CaseOne_of_inputs
    (h34 : Stroth34Statement) (h311a : Stroth311aStatement) (h51 : Stroth51Statement)
    (hA : Sec7AExistsStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hZc : Sec7CentreMpStatement) (h78 : Stroth78Statement) (hCN : Sec7CommNStatement)
    (hY : Sec713YStatement) (hCor2 : Tim77Cor2Statement)
    (hOut : OutSolvableListStatement) (hOutA : OutSolvableAlphaStatement)
    (hRank : TwoRankSporadicAltStatement) (hBorel : BorelRankOneSolvableStatement)
    (hArtin : ArtinLinearOrdersStatement) (hRad : RadicalTwoSubgroupLinearStatement)
    (hRad2 : RadicalTwoSubgroupRankTwoStatement) : Sec717CaseOneStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZNc hTI hF hC L hL hLn hcase1
  have hbase := Ctx.yBase h34 h311a hZt hZcard hZc h78 hc hs hp3 hZ0 hZNc hTI hL hLn
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hnormR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hRK : Rt M (LB M Q B) t ≤ NormH0 M Z Z0 := fun ρ hρ =>
    Subgroup.mem_inf.mpr ⟨hc.Rt_le_H0 t hρ, IsCentrePre.mem_normalizer hZ0 hnormR hρ⟩
  have hQK : Q ≤ NormH0 M Z Z0 := fun q hq =>
    Subgroup.mem_inf.mpr ⟨hQH hq, Subgroup.le_normalizer (hQZ0 hq)⟩
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  have hZ0N : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  have hQL : Q ≤ L := hL.1
  have hLN : L ≤ hc.CN t := hL.2.1
  have hZ0L : Z0 ≤ L := hL.2.2.2.2.2
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hHM : H0 M Z ≤ M := fun x hx => hx.1
  have hKbar := bar_NormH0_eq hc hQZ0 hZ0M
  have hN2 := sec7_CN_pgroup_bar h34 h311a hc hs
  have hconf := hc.tiConfigC hs hZ0 hZt hZcard hN2 hTI hC
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ g : ℕ, Nat.card Z = 2 ^ g := by
    obtain ⟨g, k, hg, -⟩ := hc.hyp.cp
    exact ⟨g, hg⟩
  set Hb : Subgroup (Mbar M Q) := bar M Q (H0 M Z) with hHb
  have hO2y : ∀ P : Subgroup ↥Hb, P.Normal → IsPGroup 2 P → P = ⊥ := by
    intro P hP hP2
    have hle : P ≤ pCore 2 ↥Hb := le_sSup ⟨hP, hP2⟩
    rw [pCore_two_bar_H0_eq_bot hc] at hle
    exact le_bot_iff.mp hle
  have hOy : ∀ P : Subgroup ↥Hb, P.Normal → Odd (Nat.card P) → P = ⊥ := by
    intro P hP hPodd
    have hPn : ∀ h ∈ Hb, h ∈ Subgroup.normalizer ((P.map Hb.subtype : Subgroup (Mbar M Q)) :
        Set (Mbar M Q)) := fun h hh => mem_normalizer_map_of_normal P hh
    have hodd' : Odd (Nat.card ↥(P.map Hb.subtype)) := by
      rw [← Nat.card_congr (P.equivMapOfInjective Hb.subtype Hb.subtype_injective).toEquiv]
      exact hPodd
    have := Ctx.recog_odd_normal_bot h34 h311a hc hs hZ0 hZt hZcard hZc hTI hF hC
      (Subgroup.map_subtype_le P) hPn hodd'
    exact (Subgroup.map_eq_bot_iff_of_injective P Hb.subtype_injective).mp this
  have hCy : ∀ X : Subgroup ↥Hb, X.Normal → (bar M Q Z0).subgroupOf Hb ≤ X →
      ∀ c : ↥Hb, (∀ x ∈ X, c * x = x * c) → c = 1 := by
    intro X hX hVX c hcX
    have hX' : X.map Hb.subtype ≤ Hb := Subgroup.map_subtype_le X
    have hn : ∀ h ∈ Hb, h ∈ Subgroup.normalizer ((X.map Hb.subtype : Subgroup (Mbar M Q)) :
        Set (Mbar M Q)) := fun h hh => mem_normalizer_map_of_normal X hh
    have hV' : bar M Q Z0 ≤ X.map Hb.subtype := by
      intro v hv
      have hvH : v ∈ Hb := bar_mono' hZ0H0 hv
      exact ⟨⟨v, hvH⟩, hVX (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
    have hbot := Ctx.recog_centralizer_normal_bot h34 h311a hc hs hZ0 hZt hZcard hZc hTI hF hC
      hX' hn hV'
    have hc' : (c : Mbar M Q) ∈ Subgroup.centralizer ((X.map Hb.subtype : Subgroup (Mbar M Q)) :
        Set (Mbar M Q)) ⊓ Hb := by
      refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, c.2⟩
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hcX x hx).symm
    rw [hbot, Subgroup.mem_bot] at hc'
    exact Subtype.ext hc'
  set Vy : Subgroup ↥Hb := (bar M Q Z0).subgroupOf Hb with hVy
  set Ly : Subgroup ↥Hb := (bar M Q L).subgroupOf Hb with hLy
  set Ny : Subgroup ↥Hb := (bar M Q (hc.CN t)).subgroupOf Hb with hNy
  set Ry : Subgroup ↥Hb := (bar M Q (Rt M (LB M Q B) t)).subgroupOf Hb with hRy
  set Ky : Subgroup ↥Hb := (bar M Q (NormH0 M Z Z0)).subgroupOf Hb with hKy
  have hNH : bar M Q (hc.CN t) ≤ Hb := bar_mono' (hNR.trans hRH)
  have hKH : bar M Q (NormH0 M Z Z0) ≤ Hb :=
    bar_mono' (S := NormH0 M Z Z0) (T := H0 M Z) (fun x hx => hx.1)
  have hNK : bar M Q (hc.CN t) ≤ bar M Q (NormH0 M Z Z0) := bar_mono' (hNR.trans hRK)
  have hKy : Ky = Subgroup.normalizer (Vy : Set ↥Hb) := hbase.K_eq
  have hRH' : bar M Q (Rt M (LB M Q B) t) ≤ Hb := bar_mono' hRH
  have hVH : bar M Q Z0 ≤ Hb := bar_mono' hZ0H0
  have hpcy : ∀ P : Subgroup ↥Hb, P ≤ Ky → (∀ k ∈ Ky, k ∈ Subgroup.normalizer (P : Set ↥Hb)) →
      IsPGroup 2 P → P ≤ Ny := by
    intro P hPK hPn hP2
    have hPK' : P.map Hb.subtype ≤ bar M Q (NormH0 M Z Z0) := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hPK hx)
    have hPn' : ∀ k ∈ bar M Q (NormH0 M Z Z0), k ∈ Subgroup.normalizer
        ((P.map Hb.subtype : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := by
      intro k hk
      have hkH : k ∈ Hb := bar_mono' (S := NormH0 M Z Z0) (T := H0 M Z) (fun x hx => hx.1) hk
      have hkn := Subgroup.mem_normalizer_iff.mp
        (hPn ⟨k, hkH⟩ (Subgroup.mem_subgroupOf.mpr hk))
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨⟨k, hkH⟩ * x * ⟨k, hkH⟩⁻¹, (hkn x).mp hx, rfl⟩
    have h1 := Ctx.recog_pcore_le hc hF _ hPK' hPn' (hP2.map Hb.subtype)
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (h1 ⟨x, hx, rfl⟩)
  have hCKN := Ctx.yCKN hc hF hNK hKH
  have hSyl : ∃ S : Sylow 2 ↥Hb, (S : Subgroup ↥Hb) ≤ Subgroup.normalizer (Vy : Set ↥Hb) := by
    obtain ⟨S, hS⟩ := Ctx.ySylow hc hs hZ0 hZt hZcard hN2 hTI hC
    exact ⟨S, by rw [← hKy]; exact hS⟩
  have hsq1 : ∀ a b : ↥Hb, a * a = 1 → b * b = 1 → (a * b) * (a * b) = 1 → a * b = b * a := by
    intro a b ha hb hab
    calc a * b = a * (a * b * a * b) * b := by
          rw [show a * b * a * b = 1 from by simpa [mul_assoc] using hab]
          simp
      _ = (a * a) * b * a * (b * b) := by group
      _ = b * a := by rw [ha, hb]; simp
  have hVab : IsElemAbelian 2 Vy := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      exact hsq1 a b (hbase.Vsq a a.2) (hbase.Vsq b b.2) (hbase.Vsq (a * b) (Vy.mul_mem a.2 b.2))
    · have := hbase.Vsq x hx
      simpa [sq] using this
  have hti : IsTI Vy := by
    intro g
    by_cases hg : g ∈ Subgroup.normalizer (Vy : Set ↥Hb)
    · right
      have : conjSubgroup g Vy = Vy := conjSubgroup_eq_self_iff.mpr hg
      rw [this, inf_idem]
    · left
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨haV, hagV⟩ := ha
      by_contra hne
      have ha1 : a ≠ 1 := fun h => hne (by rw [h]; exact Subgroup.one_mem _)
      have hagV' : g⁻¹ * a * g ∈ Vy := mem_conjSubgroup.mp hagV
      have h1 := hbase.ti g⁻¹ a haV ha1 (by simpa using hagV')
      exact hg (by simpa using (Subgroup.normalizer (Vy : Set ↥Hb)).inv_mem h1)
  have hconj : ∀ g : ↥Hb, conjSubgroup g Vy ≤ Subgroup.normalizer (Vy : Set ↥Hb) →
      conjSubgroup g Vy ≤ Ny := by
    intro g hg
    have hg' : conjSubgroup g Vy ≤ Ky := by rw [hKy]; exact hg
    exact Ctx.yConj hc ht hZ0 hcase1 g hg'
  have hNcomm : ∀ x ∈ hc.CN t, ∀ y ∈ hc.CN t, ⁅x, y⁆ ∈ Z0 := fun x hx y hy =>
    hCN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator hx hy)
  have hWAC : ⁅WAC Vy, WAC Vy⁆ ≤ Vy := wac_commutator_le hconj (Ctx.yComm hc hNcomm hNH)
  have hLsq : ∀ x ∈ Ly, x * x ∈ Vy := Ctx.ySq h51 hA hc hs hZ0 hL
  obtain ⟨D, hVD, hDL, hDab, hD64, hDn⟩ := exists_elemAbelian_of_sq_le Vy Ly (Nat.card Z) hq4
    hbase.VL hbase.Vcard hbase.Lcard hbase.Lcomm hLsq hbase.Vsq
  obtain ⟨K₀, hKf, hKfin, hK₀, hnormN, hquot⟩ := Ctx.recog_quot_equiv hc hp3
  haveI := hnormN
  obtain ⟨hnormY, hquotY⟩ := nonempty_quot_equiv_bar (M := M) (Q := Q) (H := H0 M Z) hQN hNR
    hRH hHM hquot
  obtain ⟨y, hyR, hyQ, hy3, hyC⟩ := hY G M Q Z B hc n t hs Z0 hZ0
  have hyM : y ∈ M := hc.Rt_le_M t hyR
  have hybR : QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ ∈ bar M Q (Rt M (LB M Q B) t) :=
    (mk_mem_bar_iff_sec4 hQR ⟨y, hyM⟩).mpr hyR
  have hybH : QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ ∈ Hb := hRH' hybR
  have hyy : ∃ y' ∈ Ry, orderOf y' = 3 ∧ ∀ x ∈ Ny, y' * x = x * y' → x ∈ Vy := by
    refine ⟨⟨_, hybH⟩, Subgroup.mem_subgroupOf.mpr hybR, ?_, ?_⟩
    · have h3 : (⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩, hybH⟩ : ↥Hb) ^ 3 = 1 := by
        apply Subtype.ext
        show (QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩) ^ 3 = 1
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hy3))
      have hne : (⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩, hybH⟩ : ↥Hb) ≠ 1 := by
        intro h
        have h' := congrArg Subtype.val h
        exact hyQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h'))
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime h3 hne
    · intro x hx hxc
      obtain ⟨x0, hx0⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
      have hx0N : (x0 : G) ∈ hc.CN t :=
        (mk_mem_bar_iff_sec4 hQN x0).mp (hx0 ▸ Subgroup.mem_subgroupOf.mp hx)
      have hcomm : ⁅y, (x0 : G)⁆ ∈ Q := by
        refine mem_Q_of_mk_mul_comm (a := ⟨y, hyM⟩) (b := x0) ?_
        have h1 := congrArg Subtype.val hxc
        simp only [Subgroup.coe_mul] at h1
        rw [← hx0] at h1
        exact h1
      have hx0Z : (x0 : G) ∈ Z0 := hyC _ hx0N hcomm
      exact Subgroup.mem_subgroupOf.mpr
        (by rw [← hx0]; exact (mk_mem_bar_iff_sec4 hQZ0 x0).mpr hx0Z)
  obtain ⟨K₁, hKf1, hKfin1, hK1, ⟨e⟩⟩ := caseOne_abstract hCor2 hOut hOutA hRank hBorel hArtin
    hRad hRad2 (Nat.card Z) hq4 hq2 Vy D Ny Ry Ky hO2y hOy hCy
    (fun g hg => by rw [hKy]; exact hg) (fun k hk => by rw [← hKy]; exact hk) hVD
    (hDL.trans hbase.LN) hbase.NR hbase.RK hbase.N2 hpcy hbase.Nn hbase.Rn
    (fun k hk => hDn k (hbase.Ln k hk)) hCKN hbase.ZN hbase.Vc hbase.Vcard hbase.Ncard hD64 hDab
    hVab hti hWAC hSyl K₀ hK₀ ⟨hnormY, hquotY⟩ hyy
  exact ⟨K₁, hKf1, hKfin1, hK1, ⟨e⟩⟩

end CFSG.RankThree.GF2n.Stroth80
