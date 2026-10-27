module

public import CFSG.RankThree.GF2n.Stroth80.Sec7LinAlg
public import CFSG.RankThree.GF2n.Stroth80.Sec7IsometryFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec711Step6
public import CFSG.RankThree.GF2n.Stroth80.Sec12Decomp
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsAux
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_card_inf_conj_of_tame (h34 : Stroth34Statement) (hZV : Sec7ZVStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (h4 : OmegaPlusNat hc t 4)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : G} (hg : g ∈ M)
    (htame : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g * t * g⁻¹, w⁆ ∈ Vt M (LB M Q B) B Z t) :
    Nat.card Z ^ 5 ≤
      Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) := by
  classical
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hxM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  have hxZ : ∀ z ∈ Z, (g * t * g⁻¹) * z * (g * t * g⁻¹)⁻¹ = z := by
    intro z hz
    have hz' : g⁻¹ * z * g ∈ Z := by simpa using hZn g⁻¹ (M.inv_mem hg) z hz
    have h1 := hc.LB_centralizes_Z ht _ hz'
    calc (g * t * g⁻¹) * z * (g * t * g⁻¹)⁻¹ = g * (t * (g⁻¹ * z * g) * t⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h1]
      _ = z := by group
  have hxC : g * t * g⁻¹ ∈ Subgroup.centralizer (Z : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz => (mul_inv_eq_iff_eq_mul.mp (hxZ z hz)).symm
  have hxH : g * t * g⁻¹ ∈ H0 M Z := ⟨hxM, hxC⟩
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS⟩ := tensorSetup_of_34 h34 G M Q Z B hc n hs5.width
    hs5.n_gt hs5.noA2 hs5.gen
  set x : G := g * t * g⁻¹ with hxdef
  have hζH : (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hxH, rfl⟩
  let T : M₀.E ≃ₗ[K] M₀.E := AddEquiv.toLinearEquiv
    (ρ (QuotientGroup.mk (⟨x, hxM⟩ : ↥M))).toAdd (hS.lin _ hζH)
  have hT : ∀ y ∈ Q, M₀.π (x * y * x⁻¹) = T (M₀.π y) := fun y hy => hS.conj ⟨x, hxM⟩ y hy
  have hiso : ∀ e e', M₀.B (T e) (T e') = M₀.B e e' := hS.iso _ hζH
  have ha : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hxM).1
  have ha' : ∀ y ∈ Q, x⁻¹ * y * x ∈ Q := fun y hy => by
    have := (hc.conj_mem_Q_of_mem_M (M.inv_mem hxM)).1 y hy
    simpa using this
  have hrange := mem_img_comm_zpowers_sup_iff M₀ hS.model.reg T ha ha' hT
  have hVU : Ut Q Z t = Vt M (LB M Q B) B Z t :=
    hZV G M Q Z B hc n t hs Z0 hZ0 t htZ0 hs5.notQ
  have hUtx : Ut Q Z x = conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    rw [hxdef, Ut_conj_of_normalizes (hc.conj_Q_eq hg) (hc.conj_Z_eq hg) t, hVU]
  have hKZ : Nat.card K = Nat.card Z := hS.card
  have hK2 : 2 ≤ Nat.card K := by
    rw [hKZ]
    have := hc.hyp.q4
    omega
  have hcard := card_comm_zpowers_sup M₀ hS.model.reg T ha ha' hT
  have hVc := n12N_card_V hc t 4 (by norm_num) (Or.inl h4)
  have hf : Module.finrank K (LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) = 8 := by
    have h1 : Nat.card ↥(⁅Q, Subgroup.zpowers x⁆ ⊔ Z) = Nat.card ↥(Vt M (LB M Q B) B Z t) := by
      have e : (⁅Q, Subgroup.zpowers x⁆ ⊔ Z) = conjSubgroup g (Vt M (LB M Q B) B Z t) := hUtx
      rw [e, card_conjSubgroup]
    rw [h1, hVc, ← hKZ] at hcard
    have hpos : 0 < Nat.card K := Nat.card_pos
    have h2 : Nat.card K ^ (2 * 4) = Nat.card K ^ Module.finrank K
        (LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) :=
      Nat.eq_of_mul_eq_mul_left hpos hcard
    have h3 := Nat.pow_right_injective hK2 h2
    omega
  have hB : M₀.B.Nondegenerate := modelB_nondegenerate M₀
  have hr : M₀.B.IsRefl := LinearMap.IsAlt.isRefl (fun e => M₀.alt e)
  have hker := sec7_ker_sub_one_eq_perp_range M₀.B hB hr T hiso
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  let U : Submodule K M₀.E := imgSub M₀ (Vt M (LB M Q B) B Z t) (hc.smul_mem_img_Vt hS.model t)
  have hkey := sec7_finrank_map_orthogonal M₀.B hB hr ((T : M₀.E →ₗ[K] M₀.E) - 1) hker U
  have hle : (M₀.B.orthogonal U).map ((T : M₀.E →ₗ[K] M₀.E) - 1) ≤
      U ⊓ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Submodule.mem_map.mp he
    refine ⟨?_, LinearMap.mem_range_self _ e'⟩
    have he'W : e' ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) := by
      rw [mem_img_Wt_iff M₀ hS.model.reg hVQ]
      intro v hv
      have h1 : M₀.B v e' = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp he') v hv
      rw [Tim79.QuadModel.B_comm, h1, neg_zero]
    obtain ⟨w, hwW, hwQ, rfl⟩ := he'W
    have hxwQ : x * w * x⁻¹ ∈ Q := ha w hwQ
    have hcomm : ⁅x, w⁆ = (x * w * x⁻¹) * w⁻¹ := by rw [commutatorElement_def]
    have hcQ : ⁅x, w⁆ ∈ Q := by
      rw [hcomm]
      exact Q.mul_mem hxwQ (Q.inv_mem hwQ)
    have hπ : M₀.π ⁅x, w⁆ = ((T : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π w) := by
      rw [hcomm, M₀.π_mul _ hxwQ _ (Q.inv_mem hwQ), Tim79.QuadModel.pi_inv M₀ hwQ, hT w hwQ]
      simp [sub_eq_add_neg]
    rw [← hπ]
    exact mem_imgSub.mpr (M₀.pi_mem_img (htame w hwW) hcQ)
  have hmono := Submodule.finrank_mono hle
  rw [hkey, hf] at hmono
  have hd4 : 4 ≤ Module.finrank K ↥(U ⊓ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) := by
    omega
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    le_inf sec39_Z_le_Vt (hc.Z_le_conjSubgroup sec39_Z_le_Vt hg)
  have hcardInf := M₀.card_eq (inf_le_left.trans hVQ) hZV'
  have himg : ∀ e, e ∈ M₀.img (Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) ↔
      e ∈ U ⊓ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) := by
    intro e
    constructor
    · rintro ⟨y, hyS, hyQ, rfl⟩
      have hyU : y ∈ Ut Q Z x := by
        rw [hUtx]
        exact hyS.2
      exact ⟨mem_imgSub.mpr (M₀.pi_mem_img hyS.1 hyQ), (hrange _).mp (M₀.pi_mem_img hyU hyQ)⟩
    · rintro ⟨hU', hR⟩
      obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
      have hyV : y ∈ Vt M (LB M Q B) B Z t :=
        (M₀.mem_img_iff sec39_Z_le_Vt hyQ).mp (mem_imgSub.mp hU')
      have hyU : y ∈ Ut Q Z x :=
        (M₀.mem_img_iff (le_sup_right : Z ≤ ⁅Q, Subgroup.zpowers x⁆ ⊔ Z) hyQ).mp
          ((hrange _).mpr hR)
      rw [hUtx] at hyU
      exact M₀.pi_mem_img ⟨hyV, hyU⟩ hyQ
  have hcardImg : Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t ⊓
      conjSubgroup g (Vt M (LB M Q B) B Z t))) =
      Nat.card ↥(U ⊓ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) :=
    Nat.card_congr (Equiv.subtypeEquivRight himg)
  have hpowU := Module.natCard_eq_pow_finrank (K := K)
    (V := ↥(U ⊓ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)))
  rw [hcardInf, hcardImg, hpowU, ← hKZ]
  calc Nat.card K ^ 5 = Nat.card K * Nat.card K ^ 4 := by ring
    _ ≤ Nat.card K * Nat.card K ^ Module.finrank K
        ↥(U ⊓ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hd4)

end CFSG.RankThree.GF2n.Stroth80
