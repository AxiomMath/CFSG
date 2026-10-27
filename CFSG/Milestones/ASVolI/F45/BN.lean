module

public import CFSG.Quasithin.Vol2.GoldschmidtF431BNBase
public import CFSG.Milestones.ASVolI.F4

public noncomputable section

namespace CFSG.ASVolI

open CFSG.GH74.BNPair CFSG.Open CFSG.Quasithin.H13.F431.BN
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {n : ℕ} (D : RankTwoSystem X n) {p : ℕ}

omit [Finite X] in
theorem burnsideF45_bn_not_dvd_index (hU : ChF.IsSylowOf p D.U ⊤) : ¬ p ∣ D.U.index := by
  rw [← Subgroup.relIndex_top_right]
  exact hU.2.2

theorem burnsideF45_bn_pCore_le_U (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool) :
    pCoreOf p (P D i) ≤ D.U := by
  haveI : Fact p.Prime := ⟨hp⟩
  let S : Sylow p X := hU.2.1.toSylow (burnsideF45_bn_not_dvd_index D hU)
  have hQp : IsPGroup p (pCoreOf p (P D i)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup p (P D i)
  have hnorm : P D i ≤ Subgroup.normalizer (pCoreOf p (P D i) : Set X) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf p (P D i)
  have hUQ : D.U ≤ Subgroup.normalizer (pCoreOf p (P D i) : Set X) :=
    (D.U_le_B.trans (B_le_P D i)).trans hnorm
  have hsup : IsPGroup p (pCoreOf p (P D i) ⊔ D.U : Subgroup X) :=
    hQp.to_sup_of_normal_left' hU.2.1 hUQ
  have := S.is_maximal' hsup (le_sup_right : D.U ≤ pCoreOf p (P D i) ⊔ D.U)
  exact le_sup_left.trans this.le

omit [Finite X] in
theorem burnsideF45_bn_Uplus_le_pCore (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool) :
    Uplus D i ≤ pCoreOf p (P D i) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p (Uplus_le_P D i)
    (P_le_normalizer_Uplus D i) (hU.2.1.to_le (Uplus_le_U D i))

theorem burnsideF45_bn_pCore_le_Uplus (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool) :
    pCoreOf p (P D i) ≤ Uplus D i := by
  intro x hx
  have hm : mi D i ∈ Subgroup.normalizer (pCoreOf p (P D i) : Set X) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf p (P D i) (mi_mem_P D i)
  exact ⟨burnsideF45_bn_pCore_le_U D hp hU i hx,
    burnsideF45_bn_pCore_le_U D hp hU i ((Subgroup.mem_normalizer_iff.1 hm x).1 hx)⟩

theorem burnsideF45_bn_pCore_eq (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool) :
    pCoreOf p (CFSG.Quasithin.H13.F431.BN.P D i) = CFSG.Quasithin.H13.F431.BN.Uplus D i :=
  le_antisymm (burnsideF45_bn_pCore_le_Uplus D hp hU i) (burnsideF45_bn_Uplus_le_pCore D hU i)

theorem burnsideF45_bn_pCore_le_B (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool) :
    pCoreOf p (CFSG.Quasithin.H13.F431.BN.P D i) ≤ D.B :=
  (burnsideF45_bn_pCore_le_U D hp hU i).trans D.U_le_B

theorem burnsideF45_bn_pCore_eq_UwMinus (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool) :
    pCoreOf p (P D i) = D.UwMinusSub (D.lift (wS D i)) :=
  (SetLike.coe_injective ((coe_UwMinus_wS D i).trans
    (congrArg _ (burnsideF45_bn_pCore_eq D hp hU i).symm))).symm

theorem burnsideF45_bn_mem_pCore_iff_UwMinus (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤)
    (i : Bool) {x : X} : x ∈ pCoreOf p (P D i) ↔ x ∈ D.UwMinus (D.lift (wS D i)) := by
  rw [burnsideF45_bn_pCore_eq_UwMinus D hp hU i]
  rfl

theorem burnsideF45_bn_cell_trans (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool)
    {b c : CFSG.Quasithin.H13.F431.BN.V D}
    (hb : (CFSG.Quasithin.H13.F431.BN.Γ D).dist (CFSG.Quasithin.H13.F431.BN.v D i) b = n)
    (hc : (CFSG.Quasithin.H13.F431.BN.Γ D).dist (CFSG.Quasithin.H13.F431.BN.v D i) c = n) :
    ∃ q ∈ pCoreOf p (CFSG.Quasithin.H13.F431.BN.P D i), q • b = c := by
  obtain ⟨y, hy, rfl⟩ := exists_cell_rep D i hb
  obtain ⟨z, hz, rfl⟩ := exists_cell_rep D i hc
  obtain ⟨b₁, hb₁, u, hu, rfl⟩ := (D.mem_dc_iff_coord (D.lift (wS D i)) (D.lift_mk _)).1 hy
  obtain ⟨b₂, hb₂, u', hu', rfl⟩ := (D.mem_dc_iff_coord (D.lift (wS D i)) (D.lift_mk _)).1 hz
  refine ⟨u'⁻¹ * u, ?_, ?_⟩
  · rw [burnsideF45_bn_mem_pCore_iff_UwMinus D hp hU]
    exact (D.UwMinusSub (D.lift (wS D i))).mul_mem
      ((D.UwMinusSub (D.lift (wS D i))).inv_mem hu') hu
  · rw [smul_vt, vt_eq_vt_iff]
    have e : b₁ * (D.lift (wS D i) : X) * u * (u'⁻¹ * u)⁻¹ *
        (b₂ * (D.lift (wS D i) : X) * u')⁻¹ = b₁ * b₂⁻¹ := by group
    rw [e]
    exact D.rank2.B_le_pgen _ (D.B.mul_mem hb₁ (D.B.inv_mem hb₂))

theorem burnsideF45_bn_cell_free (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool)
    {b : CFSG.Quasithin.H13.F431.BN.V D}
    (hb : (CFSG.Quasithin.H13.F431.BN.Γ D).dist (CFSG.Quasithin.H13.F431.BN.v D i) b = n)
    {q : X} (hq : q ∈ pCoreOf p (CFSG.Quasithin.H13.F431.BN.P D i)) (hqb : q • b = b) :
    q = 1 := by
  obtain ⟨y, hy, rfl⟩ := exists_cell_rep D i hb
  have hqU : q ∈ D.UwMinus (D.lift (wS D i)) :=
    (burnsideF45_bn_mem_pCore_iff_UwMinus D hp hU i).1 hq
  obtain ⟨b₁, hb₁, u, hu, rfl⟩ := (D.mem_dc_iff_coord (D.lift (wS D i)) (D.lift_mk _)).1 hy
  rw [smul_vt, vt_eq_vt_iff] at hqb
  have huq : u * q⁻¹ ∈ D.UwMinus (D.lift (wS D i)) :=
    (D.UwMinusSub (D.lift (wS D i))).mul_mem hu ((D.UwMinusSub (D.lift (wS D i))).inv_mem hqU)
  have hy' : b₁ * (D.lift (wS D i) : X) * (u * q⁻¹) ∈ dc D.B D.N (wS D i) :=
    (D.mem_dc_iff_coord (D.lift (wS D i)) (D.lift_mk _)).2 ⟨b₁, hb₁, u * q⁻¹, huq, rfl⟩
  have hbB := same_cell_eq_of_ascent D.rank2 (altStar_ascent D.rank2 i rfl) hy hy'
    (by simpa [mul_assoc] using hqb)
  have := D.coord_unique (D.lift (wS D i)) (b := b₁)
    (b' := (b₁ * (D.lift (wS D i) : X) * (u * q⁻¹) *
      (b₁ * (D.lift (wS D i) : X) * u)⁻¹) * b₁) hb₁ (D.B.mul_mem hbB hb₁) huq hu (by group)
  simpa using this

theorem burnsideF45_bn_qfix (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool)
    {w : CFSG.Quasithin.H13.F431.BN.V D}
    (h : (CFSG.Quasithin.H13.F431.BN.Γ D).Adj (CFSG.Quasithin.H13.F431.BN.v D i) w) {q : X}
    (hq : q ∈ pCoreOf p (CFSG.Quasithin.H13.F431.BN.P D i)) : q • w = w := by
  obtain ⟨z, hz, rfl⟩ := exists_nbr D i h
  rw [smul_vt, vt_eq_vt_iff]
  have e : z * q⁻¹ * z⁻¹ = (z * q * z⁻¹)⁻¹ := by group
  rw [e]
  have hzq : z * q * z⁻¹ ∈ pCoreOf p (P D i) :=
    (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p (P D i) hz) q).1 hq
  exact (P D (!i)).inv_mem (B_le_P D (!i) (burnsideF45_bn_pCore_le_B D hp hU i hzq))

theorem burnsideF45_bn_modelBase (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool) :
    CFSG.Quasithin.H13.F431.F45.ModelBase (CFSG.Quasithin.H13.F431.BN.Γ D) n
      (CFSG.Quasithin.H13.F431.BN.v D i)
      (pCoreOf p (MulAction.stabilizer X (CFSG.Quasithin.H13.F431.BN.v D i))) := by
  have hQ : pCoreOf p (MulAction.stabilizer X (v D i)) = pCoreOf p (P D i) := by
    rw [stabilizer_v_eq]
  rw [hQ]
  refine ⟨fun w hw q hq => burnsideF45_bn_qfix D hp hU i hw hq,
    fun b c hb hc => burnsideF45_bn_cell_trans D hp hU i hb hc,
    fun b hb q hq hqb => burnsideF45_bn_cell_free D hp hU i hb hq hqb, ?_⟩
  intro b c b' c' hb hc hbc hb' hc' hbc'
  obtain ⟨z₁, h₁, rfl⟩ := exists_nbr D i hb
  obtain ⟨z₂, h₂, rfl⟩ := exists_nbr D i hc
  obtain ⟨z₁', h₁', rfl⟩ := exists_nbr D i hb'
  obtain ⟨z₂', h₂', rfl⟩ := exists_nbr D i hc'
  obtain ⟨g, hg, hg1, hg2⟩ := two_trans D i h₁ h₂ h₁' h₂' hbc hbc'
  refine ⟨g, ?_, hg1, hg2⟩
  rw [← MulAction.mem_stabilizer_iff, stabilizer_v_eq]
  exact hg

end CFSG.ASVolI
