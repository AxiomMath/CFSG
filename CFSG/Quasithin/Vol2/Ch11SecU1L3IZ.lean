module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IY
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IP
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IH
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem1
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Main
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IU
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin.A38c15
open scoped MatrixGroups

section Model

variable {p : ℕ} [Fact p.Prime]

theorem orderOf_zc (hp2 : p ≠ 2) : orderOf (zc p) = 2 := by
  have h1 : ofSL2 p (-1) = zc p := by
    rw [ofSL2_eq_leviPsi, ← leviPsi_neg_one]
    congr 1
    apply Units.ext
    simp
  rw [← h1, orderOf_injective (ofSL2 p) ofSL2_injective]
  apply orderOf_eq_prime
  · exact neg_one_sq
  · intro h
    have h0 := congrArg (fun A : SL(2, ZMod p) => (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h0
    exact two_ne_zero_zmod hp2 (by linear_combination -h0)

theorem exists_ne_comm_psl3 : ∃ a b : PSL3 p, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have := CFSG.LinearGroups.linear_projective_perfect (K := ZMod p) (n := 3) (by norm_num)
    (Or.inl le_rfl)
  exact Group.IsPerfect.not_isMulCommutative (PSL3 p) ⟨⟨h⟩⟩

end Model

variable {G : Type} [Group G] [Finite G]

theorem settingL3_of_psl3
    (hirr : SL3OddIrr) {p : ℕ}
    [Fact p.Prime] (hp7 : 7 ≤ p) (hp4 : p % 4 = 3)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (e : ↥(CFSG.generalizedFitting G) ≃* PSL3 p)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hFT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (hTL : ¬ T ≤ CFSG.generalizedFitting G) : SettingL3 (CFSG.generalizedFitting G) := by
  set L := CFSG.generalizedFitting G with hLdef
  have hp2 : p ≠ 2 := by omega
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_ne_comm_psl3 (p := p)
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h1 := congrArg e h
    simpa using h1
  have hAS := SecE3.almostSimple_generalizedFitting hs hnab hT hFT
  have hLn := hAS.normal
  have hGL : ∃ t : G, t ∉ L := by
    obtain ⟨t, -, ht⟩ := IsConcreteLE.not_le_iff_exists.mp hTL
    exact ⟨t, ht⟩
  have ho : ∀ (x : G) (hx : x ∈ L), orderOf x = 2 → orderOf (e ⟨x, hx⟩) = 2 := fun x hx h => by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, h]
  refine ⟨hAS, ?_, fun x hx y hy hx2 hy2 => ?_, fun x hx hx2 =>
    isCoatom_centralizer_L3 hirr hp2 hAS e hGL hx hx2, fun x hx hx2 => ?_,
    fun x hx y hy hx2 hy2 hxy hc Q hQ hQC => ?_, fun b hbL hb2 =>
    sigmaFacts_L3 (by omega) hAS.centralizer_eq e hbL hb2,
    fun t₁ t₂ h₁ h₂ o₁ o₂ hc => outer_pair_L3 hp2 hAS.centralizer_eq e h₁ h₂ o₁ o₂ hc⟩
  · rw [Nat.card_congr e.toEquiv, ← orderOf_zc hp2]
    exact orderOf_dvd_natCard _
  · obtain ⟨c, hc⟩ := isConj_iff.mp ((isConj_zc hp2 (ho x hx hx2)).trans
      (isConj_zc hp2 (ho y hy hy2)).symm)
    refine ⟨e.symm c, (e.symm c).2, ?_⟩
    have h1 := congrArg (fun w => ((e.symm w : ↥L) : G)) hc
    simpa using h1
  · obtain ⟨Y, -, hYC, hYn, ⟨eY⟩, hCs, -⟩ := exists_levi_data_L3 (by omega) hp4 e hx hx2
    exact nParam_centralizer_le_one_of_sl2 hAS hp7 hYC hYn eY hCs
  · obtain ⟨Y, hYL, hYC, hYn, ⟨eY⟩, -, hY⟩ := exists_levi_data_L3 (by omega) hp4 e hy hy2
    exact inner_torus_of_sl2 (by omega) hYL hYC hYn eY hx hx2 hc (hY x hx hx2 hc hxy) hQ hQC

theorem nParam_le_one_of_psl3_outer
    (hirr : SL3OddIrr) {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hp4 : p % 4 = 3)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G))
    (hF : IsPSL 3 p 1 ↥(CFSG.generalizedFitting G)) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) (hTL : ¬ T ≤ CFSG.generalizedFitting G) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := E2P.Asc80.exists_equiv_psl3 hF
  exact nParam_le_one_of_settingL3 torusMember_holds componentMember_holds
    (settingL3_of_psl3 hirr hp7 hp4 hs e hT hFT hTL)

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
