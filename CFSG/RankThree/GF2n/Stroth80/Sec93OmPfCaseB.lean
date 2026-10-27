module

public import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfCentre
public import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfWComm
public import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfNormCN
public import CFSG.RankThree.GF2n.Stroth80.Sec92Holds
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreX

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem false_of_inf_CN_le_Q (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hsc : StronglyClosedMod M Z0 (LB M Q B))
    {x : G} (hxL : x ∈ LB M Q B) (hxQ : x ∉ Q) (hP4 : OmegaPlusNat hc x 2)
    (hB : Z0 ⊓ hc.CN x ≤ Q) : False := by
  classical
  have hs5 := hs.toSec5
  have hsx : Sec9Hyp hc n x :=
    ⟨⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hxL, hxQ⟩, hP4, hs.large⟩
  have hsx5 := hsx.toSec5
  have hcen := step95Centre_of h34 h311a h311bComm h311bCard G M Q Z B hc n t hs Z0 hZ0
  have hZ0L : Z0 ≤ LB M Q B := hcen.1.trans inf_le_left
  have htL : t ∈ LB M Q B := hs5.mem
  have htQ : t ∉ Q := hs5.notQ
  have htZ : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) htL hZ0
  have htN : t ∉ hc.CN x := fun ht => htQ (hB (Subgroup.mem_inf.mpr ⟨htZ, ht⟩))
  have hUt : Nat.card ↥(Ut Q Z t) = Nat.card ↥(Vt M (LB M Q B) B Z x) := by
    have h1 : Ut Q Z t = Vt M (LB M Q B) B Z t := hcen.2.2 t htZ htQ
    rw [h1, hs.card_V, hsx.card_V]
  have hW := comm_Wt_le_Vt_of_card h34 hsx htL htN hUt
  have h92 := stroth92_of_34 h34 h311a h311bComm h311bCard
  obtain ⟨⟨Y, hY, -⟩, -⟩ := h92 G M Q Z B hc n x hsx _ _ rfl rfl t htL htN hW
  obtain ⟨hQR₀, hR₀R, hQY, hYR, hsup, -, hcommY⟩ := hY
  obtain ⟨Z0x, hZ0x⟩ := exists_isCentrePre (Q := Q) (hc.Q_le_Rt hxL)
  have hcenx := step95Centre_of h34 h311a h311bComm h311bCard G M Q Z B hc n x hsx Z0x hZ0x
  have hZ0xL : Z0x ≤ LB M Q B := hcenx.1.trans inf_le_left
  have hQn : ∀ ρ ∈ Rt M (LB M Q B) x, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M x hρ)) y).mp hy
  have hQZ0x : Q ≤ Z0x := hZ0x.Q_le (hc.Q_le_Rt hxL) hQn
  have hZnorm : ∀ ρ ∈ Rt M (LB M Q B) x, ∀ z ∈ Z0x, ρ * z * ρ⁻¹ ∈ Z0x := fun ρ hρ z hz =>
    (Subgroup.mem_normalizer_iff.mp (hZ0x.mem_normalizer hQn hρ) z).mp hz
  have hT : ∀ a, a ∈ Z0x ↔ a ∈ LB M Q B ∧ ∀ r ∈ Rt M (LB M Q B) x, ⁅r, a⁆ ∈ Q := by
    intro a
    constructor
    · intro ha
      refine ⟨hZ0xL ha, fun ρ hρ => ?_⟩
      rw [← commutatorElement_inv]
      exact Q.inv_mem (hZ0x.comm_mem ha hρ)
    · rintro ⟨haL, haQ⟩
      refine hZ0x.mem_iff.mpr ⟨le_Rt (M := M) (LB M Q B) hxL haL, fun ρ hρ => ?_⟩
      rw [← commutatorElement_inv]
      exact Q.inv_mem (haQ ρ hρ)
  have hcommCN : ⁅hc.CN x, hc.CN x⁆ ≤ Z0x :=
    h311bComm G M Q Z B hc n hsx5.width hsx5.n_gt hsx5.noA2 hsx5.gen x hxL hsx5.notQ
      (sec9_Rt_ne_LB h34 hsx) (sec9_not_SLNat hsx) Z0x hT
  have hZcomm : ∀ z ∈ Z0, ∀ f ∈ hc.CN x, ⁅z, f⁆ ∈ Q := fun z hz f hf =>
    hB (comm_mem_inf_CN hxL hZ0L hsc hz hf)
  let C₂ : Subgroup G :=
    { carrier := {r | r ∈ Rt M (LB M Q B) x ∧ ∀ f ∈ hc.CN x, ⁅f, r⁆ ∈ Z0x}
      mul_mem' := by
        rintro a b ⟨haR, ha⟩ ⟨hbR, hb⟩
        refine ⟨(Rt M (LB M Q B) x).mul_mem haR hbR, fun f hf => ?_⟩
        have e : ⁅f, a * b⁆ = ⁅f, a⁆ * (a * ⁅f, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Z0x.mul_mem (ha f hf) (hZnorm a haR _ (hb f hf))
      one_mem' := ⟨(Rt M (LB M Q B) x).one_mem, fun f _ => by
        rw [show ⁅f, (1 : G)⁆ = 1 by simp [commutatorElement_def]]
        exact Z0x.one_mem⟩
      inv_mem' := by
        rintro a ⟨haR, ha⟩
        refine ⟨(Rt M (LB M Q B) x).inv_mem haR, fun f hf => ?_⟩
        have e : ⁅f, a⁻¹⁆ = a⁻¹ * ⁅f, a⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        have h5 := hZnorm a⁻¹ ((Rt M (LB M Q B) x).inv_mem haR) _ (Z0x.inv_mem (ha f hf))
        simpa using h5 }
  have hC₂mem : ∀ r, r ∈ C₂ ↔ r ∈ Rt M (LB M Q B) x ∧ ∀ f ∈ hc.CN x, ⁅f, r⁆ ∈ Z0x :=
    fun r => Iff.rfl
  have hNR : hc.CN x ≤ Rt M (LB M Q B) x := sec9_CN_le_Rt hc x
  have hN₂ : hc.CN x ≤ C₂ := fun f' hf' =>
    (hC₂mem f').mpr ⟨hNR hf', fun f hf => hcommCN (Subgroup.commutator_mem_commutator hf hf')⟩
  have hR₀ : Sec9R0 hc x t ≤ C₂ := by
    refine sup_le hN₂ ?_
    refine iSup₂_le fun ρ hρ => ?_
    rw [Subgroup.zpowers_le]
    refine (hC₂mem _).mpr ⟨(Rt M (LB M Q B) x).mul_mem ((Rt M (LB M Q B) x).mul_mem hρ
      (le_Rt (M := M) (LB M Q B) hxL htL)) ((Rt M (LB M Q B) x).inv_mem hρ), fun f hf => ?_⟩
    have e : ⁅f, ρ * t * ρ⁻¹⁆ = ρ * ⁅ρ⁻¹ * f * ρ, t⁆ * ρ⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hf1 : ρ⁻¹ * f * ρ ∈ hc.CN x := by
      have := hc.CN_conj_mem hxL ((Rt M (LB M Q B) x).inv_mem hρ) hf
      simpa using this
    have h6 : ⁅ρ⁻¹ * f * ρ, t⁆ ∈ Q := by
      rw [← commutatorElement_inv]
      exact Q.inv_mem (hZcomm t htZ _ hf1)
    exact hQZ0x (hQn ρ hρ _ h6)
  have hYC : Y ≤ C₂ := fun y hy => (hC₂mem y).mpr ⟨hYR hy, fun f hf =>
    hQZ0x (hcommY f (le_sup_left (a := hc.CN x) hf) y hy)⟩
  have hall : Rt M (LB M Q B) x ≤ C₂ := by
    rw [← hsup]
    exact sup_le hR₀ hYC
  exact false_of_comm_CN_le_centre h34 h311a h311bComm h311bCard hsx hZ0x
    fun f hf ρ hρ => ((hC₂mem ρ).mp (hall hρ)).2 f hf

end HS9

end CFSG.RankThree.GF2n.Stroth80
