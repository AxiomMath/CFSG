module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93XH
public import CFSG.RankThree.GF2n.Stroth80.CarterSec93Omega
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAbsorb
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseA
public import CFSG.RankThree.GF2n.Stroth80.Sec7CommN
public import CFSG.RankThree.GF2n.Stroth80.Sec85Comm
public import CFSG.RankThree.GF2n.Stroth80.Sec86IrredCentral

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem Sec9Hyp.sec7Hyp_of_omegaNat {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    {hc : Ctx M Q Z B} {n : ℕ} {t x : G} (hs : Sec9Hyp hc n t)
    (hxL : x ∈ LB M Q B) (hxQ : x ∉ Q) (hΩ : OmegaNat hc x) (h4 : ¬ OmegaPlusNat hc x 2) :
    Sec7Hyp hc n x := by
  obtain ⟨K, fK, finK, hK, hplus | hminus⟩ := hΩ
  · obtain ⟨m, hm3, hnat⟩ := hplus
    exact Sec7Hyp.mk
      (Sec5Hyp.mk hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen hxL hxQ)
      h4 ⟨m, by omega, Or.inl ⟨K, fK, finK, hK, hnat⟩⟩ (hs.large x hxL hxQ)
  · obtain ⟨m, b, c, hm2, hirr, hnat⟩ := hminus
    exact Sec7Hyp.mk
      (Sec5Hyp.mk hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen hxL hxQ)
      h4 ⟨m, hm2, Or.inr ⟨K, fK, finK, hK, b, c, hirr, hnat⟩⟩ (hs.large x hxL hxQ)

theorem Sec9Hyp.sec8Hyp_of_spNat {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    {hc : Ctx M Q Z B} {n : ℕ} {t x : G} (hs : Sec9Hyp hc n t)
    (hxL : x ∈ LB M Q B) (hxQ : x ∉ Q) (hsp : SpNat hc x) : Sec8Hyp hc n x := by
  obtain ⟨K, fK, finK, hK, m, hm, hnat⟩ := hsp
  exact ⟨⟨hs.toSec5.width, hs.toSec5.n_gt, hs.toSec5.noA2, hs.toSec5.gen, hxL, hxQ⟩,
    ⟨m, hm, K, fK, finK, hK, hnat⟩⟩

theorem spMNat_iff_of_rt_vt {G : Type} [Group G] [Finite G] {M Q Z B B' : Subgroup G}
    (hc : Ctx M Q Z B) (hc' : Ctx M Q Z B') {t s : G}
    (hR : Rt M (LB M Q B') s = Rt M (LB M Q B) t)
    (hV : Vt M (LB M Q B') B' Z s = Vt M (LB M Q B) B Z t) (k : ℕ) :
    SpMNat hc' s k ↔ SpMNat hc t k := by
  unfold SpMNat
  rw [hR, hV, CN_eq_of_rt_vt hc hc' hR hV]

theorem Sec8Hyp.conjBase {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    {hc : Ctx M Q Z B} {n : ℕ} {x m : G} (hs : Sec8Hyp hc n x)
    (hm : m ∈ M) (hx : x ∈ conjSubgroup m (LB M Q B)) : Sec8Hyp (hc.conj_of_mem hm) n x := by
  obtain ⟨k, hk, hsp⟩ := hs.sp
  obtain ⟨hR, hV⟩ := rt_vt_conj hc hm x
  exact ⟨sec5Hyp_conj hc hm hs.toSec5 hx,
    ⟨k, hk, (spMNat_iff_of_rt_vt hc (hc.conj_of_mem hm) hR hV k).mpr hsp⟩⟩

namespace S93O

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G} {h : G}

private theorem centre_le_inf (hZc : Sec7CentreMpStatement) (hZt : Sec7ZtStatement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxH : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hx7 : Sec7Hyp hc n x)
    {Z0x : Subgroup G} (hZ0x : IsCentrePre Z0x (Rt M (LB M Q B) x) Q) :
    Z0x ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B) := by
  have hxL : x ∈ LB M Q B := (Subgroup.mem_inf.mp hxH).1
  have hxL' : x ∈ conjSubgroup h (LB M Q B) := (Subgroup.mem_inf.mp hxH).2
  have hxZ : x ∈ Z0x := IsCentrePre.mem_of_mem_LB (hc := hc) hxL hZ0x
  have hxQ : x ∉ Q := hx7.toSec5.notQ
  have hL : Z0x ≤ LB M Q B := by
    simpa [conjSubgroup_one] using
      centre_le_conj_LB hZc hZt hc hx7 hZ0x (m := 1) (s := x) M.one_mem hxZ hxQ
        (by simpa [conjSubgroup_one] using hxL)
  have hL' : Z0x ≤ conjSubgroup h (LB M Q B) :=
    centre_le_conj_LB hZc hZt hc hx7 hZ0x (m := h) (s := x) cfg.hh hxZ hxQ hxL'
  exact le_inf hL hL'

private theorem mem_centre_of_centralizes (h711 : Stroth711StrongStatement)
    {x : G} (hx7 : Sec7Hyp hc n x) {Z0x : Subgroup G}
    (hZ0x : IsCentrePre Z0x (Rt M (LB M Q B) x) Q)
    (hirr : IsIrredModule (Rt M (LB M Q B) x) (hc.CN x) Z0x) :
    ∀ a ∈ hc.CN x, (∀ b ∈ hc.CN x, ⁅a, b⁆ ∈ Q) → a ∈ Z0x := by
  have hxL : x ∈ LB M Q B := hx7.toSec5.mem
  have hQn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) q).mp hq
  have hRM : Rt M (LB M Q B) x ≤ M := hc.Rt_le_M x
  have hNR : hc.CN x ≤ Rt M (LB M Q B) x := fun y hy => (Ctx.mem_CN.1 hy).1
  have hNn : ∀ ρ ∈ Rt M (LB M Q B) x, ∀ y ∈ hc.CN x, ρ * y * ρ⁻¹ ∈ hc.CN x :=
    fun ρ hρ y hy => hc.CN_conj_mem hxL hρ hy
  have hZN : Z0x ≤ hc.CN x := sec7ctr_Z0_le_CN hc hx7 hZ0x
  exact sec85_centre_le hQn hRM hNR hNn hZN
    (fun z hz b hb => hZ0x.comm_mem hz (hNR hb)) hirr.2.2.2
    (h711 G M Q Z B hc n x hx7)

private theorem CN_conj_BZ {x : G} (hxL : x ∈ LB M Q B) {y : G} (hy : y ∈ hc.CN x) :
    conjSubgroup y B ⊔ Z = B ⊔ Z := by
  have hyM : y ∈ M := hc.Rt_le_M x (Ctx.mem_CN.mp hy).1
  have hyV : ∀ v ∈ Vt M (LB M Q B) B Z x, ⁅y, v⁆ ∈ Z := (Ctx.mem_CN.mp hy).2
  have hB : B ≤ Vt M (LB M Q B) B Z x := by
    simpa [conjSubgroup_one] using
      sec39_conjB_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) (t := x) (m := 1)
        M.one_mem (by simpa [conjSubgroup_one] using hxL)
  have hcomm : ∀ b ∈ B, ⁅y, b⁆ ∈ Z := fun b hb => hyV b (hB hb)
  have hYZ : conjSubgroup y Z = Z := hc.conj_Z_eq hyM
  have hcard : Nat.card ↥(conjSubgroup y B ⊔ Z) = Nat.card ↥(B ⊔ Z) := by
    calc Nat.card ↥(conjSubgroup y B ⊔ Z)
        = Nat.card ↥(conjSubgroup y B ⊔ conjSubgroup y Z) := by rw [hYZ]
      _ = Nat.card ↥(conjSubgroup y (B ⊔ Z)) := by rw [← conjSubgroup_sup']
      _ = Nat.card ↥(B ⊔ Z) := card_conjSubgroup y (B ⊔ Z)
  have hle : conjSubgroup y B ⊔ Z ≤ B ⊔ Z := by
    refine sup_le (fun z hz => ?_) le_sup_right
    rw [mem_conjSubgroup] at hz
    have hbz : z = y * (y⁻¹ * z * y) * y⁻¹ := by group
    have e : y * (y⁻¹ * z * y) * y⁻¹ = ⁅y, y⁻¹ * z * y⁆ * (y⁻¹ * z * y) := by
      simp only [commutatorElement_def]; group
    rw [hbz, e]
    exact (B ⊔ Z).mul_mem (Subgroup.mem_sup_right (hcomm _ hz)) (Subgroup.mem_sup_left hz)
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

private theorem CN_conj_LB {x : G} (hxL : x ∈ LB M Q B) {y : G} (hy : y ∈ hc.CN x) :
    conjSubgroup y (LB M Q B) = LB M Q B := by
  have hyM : y ∈ M := hc.Rt_le_M x (Ctx.mem_CN.mp hy).1
  have := hc.conj_LB_eq_of_conj_BZ hyM M.one_mem (by
    simpa [conjSubgroup_one] using CN_conj_BZ hxL hy)
  simpa [conjSubgroup_one] using this

private theorem CN_le_normalizer_Z0 (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxL : x ∈ LB M Q B) (hZ0L : Z0 ≤ LB M Q B) {y : G} (hy : y ∈ hc.CN x) :
    y ∈ Subgroup.normalizer (Z0 : Set G) := by
  have hCBL : conjSubgroup y (LB M Q B) = LB M Q B := CN_conj_LB hxL hy
  have hyM : y ∈ M := hc.Rt_le_M x (Ctx.mem_CN.mp hy).1
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hzL : z ∈ LB M Q B := hZ0L hz
  have hconj : y * z * y⁻¹ ∈ conjSubgroup y (LB M Q B) := by
    rw [mem_conjSubgroup]
    have e : y⁻¹ * (y * z * y⁻¹) * y = z := by group
    rw [e]
    exact hzL
  rw [hCBL] at hconj
  exact cfg.hsc z hz y hyM hconj

theorem Rt_ne_LB (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxL' : x ∈ conjSubgroup h (LB M Q B)) :
    Rt M (LB M Q B) x ≠ LB M Q B := by
  intro hR
  have hsup : conjSubgroup h (LB M Q B) ≤ Rt M (LB M Q B) x :=
    le_iSup_of_le h (le_iSup_of_le cfg.hh (le_iSup_of_le hxL' le_rfl))
  have hle : conjSubgroup h (LB M Q B) ≤ LB M Q B := by
    rwa [hR] at hsup
  have heq : conjSubgroup h (LB M Q B) = LB M Q B :=
    Subgroup.eq_of_le_of_card_ge hle (card_conjSubgroup h (LB M Q B)).ge
  exact cfg.hne heq.symm

private theorem centre_char {x : G} (hx7 : Sec7Hyp hc n x) {Z0x : Subgroup G}
    (hZ0x : IsCentrePre Z0x (Rt M (LB M Q B) x) Q) (hZ0L : Z0x ≤ LB M Q B) :
    ∀ a, a ∈ Z0x ↔ a ∈ LB M Q B ∧ ∀ ρ ∈ Rt M (LB M Q B) x, ⁅ρ, a⁆ ∈ Q := by
  intro a
  constructor
  · intro ha
    exact ⟨hZ0L ha, fun ρ hρ => by
      rw [← commutatorElement_inv]
      exact Q.inv_mem (hZ0x.comm_mem ha hρ)⟩
  · rintro ⟨haL, haQ⟩
    refine hZ0x.mem_iff.mpr ⟨le_Rt (LB M Q B) hx7.toSec5.mem haL, fun ρ hρ => ?_⟩
    rw [← commutatorElement_inv]
    exact Q.inv_mem (haQ ρ hρ)

private theorem commutator_CN_le (h311bComm : Stroth311bCommStatement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxL' : x ∈ conjSubgroup h (LB M Q B)) (hx7 : Sec7Hyp hc n x)
    {Z0x : Subgroup G}
    (hZ0x : IsCentrePre Z0x (Rt M (LB M Q B) x) Q) (hZ0L : Z0x ≤ LB M Q B) :
    ⁅hc.CN x, hc.CN x⁆ ≤ Z0x := by
  have hxL : x ∈ LB M Q B := hx7.toSec5.mem
  have hRne : Rt M (LB M Q B) x ≠ LB M Q B := Rt_ne_LB cfg hxL'
  have hT := centre_char hx7 hZ0x hZ0L
  exact h311bComm G M Q Z B hc n hx7.toSec5.width hx7.toSec5.n_gt hx7.toSec5.noA2
    hx7.toSec5.gen x hxL hx7.toSec5.notQ hRne hx7.not_slNat Z0x hT

private theorem Z0_inf_CN_eq (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G} (hxL : x ∈ LB M Q B) {Z0x : Subgroup G}
    (hZH : Z0x ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B))
    (hcent : ∀ a ∈ hc.CN x, (∀ b ∈ hc.CN x, ⁅a, b⁆ ∈ Q) → a ∈ Z0x)
    (hcommCN : ⁅hc.CN x, hc.CN x⁆ ≤ Z0x) :
    Z0 ⊓ hc.CN x = Q := by
  have hZ0L : Z0 ≤ LB M Q B := sec93Omega_Z0_le_LB h34 h311a h311bComm cfg.hs cfg.hr cfg.hZ0
  have hNnorm : ∀ y ∈ hc.CN x, y ∈ Subgroup.normalizer (Z0 : Set G) :=
    fun y hy => CN_le_normalizer_Z0 cfg hxL hZ0L hy
  refine le_antisymm (fun d hd => ?_)
    (le_inf (hc.Q_le_centre cfg.hs.mem cfg.hZ0) (sec8_Q_le_CN hc hxL))
  obtain ⟨hdZ0, hdN⟩ := Subgroup.mem_inf.mp hd
  have hmemZ0x : d ∈ Z0x := by
    refine hcent d hdN (fun b hb => ?_)
    have h1 : ⁅d, b⁆ ∈ Z0 := by
      have hnb : b * d * b⁻¹ ∈ Z0 :=
        (Subgroup.mem_normalizer_iff.mp (hNnorm b hb) d).mp hdZ0
      have e : ⁅d, b⁆ = (b * d * b⁻¹ * d⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Z0.inv_mem (Z0.mul_mem hnb (Z0.inv_mem hdZ0))
    have h2 : ⁅d, b⁆ ∈ Z0x := hcommCN (Subgroup.commutator_mem_commutator hdN hb)
    have h3 : ⁅d, b⁆ ∈ Z0 ⊓ (LB M Q B ⊓ conjSubgroup h (LB M Q B)) :=
      Subgroup.mem_inf.mpr ⟨h1, hZH h2⟩
    rwa [cfg.hZQ] at h3
  have h4 : d ∈ Z0 ⊓ (LB M Q B ⊓ conjSubgroup h (LB M Q B)) :=
    Subgroup.mem_inf.mpr ⟨hdZ0, hZH hmemZ0x⟩
  rwa [cfg.hZQ] at h4

private theorem commutator_Z0_CN_le (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G} (hxL : x ∈ LB M Q B) {Z0x : Subgroup G}
    (hZH : Z0x ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B))
    (hcent : ∀ a ∈ hc.CN x, (∀ b ∈ hc.CN x, ⁅a, b⁆ ∈ Q) → a ∈ Z0x)
    (hcommCN : ⁅hc.CN x, hc.CN x⁆ ≤ Z0x) :
    ⁅Z0, hc.CN x⁆ ≤ Q := by
  have hZ0L : Z0 ≤ LB M Q B := sec93Omega_Z0_le_LB h34 h311a h311bComm cfg.hs cfg.hr cfg.hZ0
  have hNnorm : ∀ y ∈ hc.CN x, y ∈ Subgroup.normalizer (Z0 : Set G) :=
    fun y hy => CN_le_normalizer_Z0 cfg hxL hZ0L hy
  have hZQ := Z0_inf_CN_eq h34 h311a h311bComm cfg hxL hZH hcent hcommCN
  refine Subgroup.commutator_le.mpr fun z hz y hy => ?_
  have hzR : z ∈ Rt M (LB M Q B) x := le_Rt (LB M Q B) hxL (hZ0L hz)
  have hyR : y ∈ Rt M (LB M Q B) x := (Ctx.mem_CN.mp hy).1
  have h1 : ⁅z, y⁆ ∈ Z0 := by
    have hyz : y * z * y⁻¹ ∈ Z0 :=
      (Subgroup.mem_normalizer_iff.mp (hNnorm y hy) z).mp hz
    have e : ⁅z, y⁆ = (y * z * y⁻¹ * z⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Z0.inv_mem (Z0.mul_mem hyz (Z0.inv_mem hz))
  have h2 : ⁅z, y⁆ ∈ hc.CN x := by
    have hzy : z * y * z⁻¹ ∈ hc.CN x := hc.CN_conj_mem hxL hzR hy
    have e : ⁅z, y⁆ = (z * y * z⁻¹) * y⁻¹ := by
      simp only [commutatorElement_def]
    rw [e]
    exact (hc.CN x).mul_mem hzy ((hc.CN x).inv_mem hy)
  have h3 : ⁅z, y⁆ ∈ Z0 ⊓ hc.CN x := Subgroup.mem_inf.mpr ⟨h1, h2⟩
  rwa [hZQ] at h3

private theorem exists_centralizer {x : G} (hxL : x ∈ LB M Q B)
    (hZ0L : Z0 ≤ LB M Q B) (hZcomm : ⁅Z0, hc.CN x⁆ ≤ Q) :
    ∃ C : Subgroup G, C ≤ Rt M (LB M Q B) x ∧
      (∀ ρ ∈ Rt M (LB M Q B) x, ∀ c ∈ C, ρ * c * ρ⁻¹ ∈ C) ∧ Z0 ≤ C ∧
      ∀ c ∈ C, ∀ y ∈ hc.CN x, ⁅c, y⁆ ∈ Q := by
  have hLR : LB M Q B ≤ Rt M (LB M Q B) x := le_Rt (LB M Q B) hxL
  let C : Subgroup G :=
    { carrier := {c | c ∈ Rt M (LB M Q B) x ∧ ∀ y ∈ hc.CN x, ⁅c, y⁆ ∈ Q}
      mul_mem' := by
        rintro a b ⟨haR, ha⟩ ⟨hbR, hb⟩
        refine ⟨(Rt M (LB M Q B) x).mul_mem haR hbR, fun y hy => ?_⟩
        have haM : a ∈ M := hc.Rt_le_M x haR
        have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Q.mul_mem
          ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 haM) _).mp (hb y hy))
          (ha y hy)
      one_mem' := ⟨(Rt M (LB M Q B) x).one_mem, fun y _ => by
        rw [show ⁅(1 : G), y⁆ = 1 by simp [commutatorElement_def]]
        exact Q.one_mem⟩
      inv_mem' := by
        rintro a ⟨haR, ha⟩
        refine ⟨(Rt M (LB M Q B) x).inv_mem haR, fun y hy => ?_⟩
        have haM : a⁻¹ ∈ M := M.inv_mem (hc.Rt_le_M x haR)
        have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        simpa using
          (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 haM) _).mp (Q.inv_mem (ha y hy)) }
  have hCR : C ≤ Rt M (LB M Q B) x := fun c hc => hc.1
  have hCmem : ∀ c, c ∈ C ↔ c ∈ Rt M (LB M Q B) x ∧
      ∀ y ∈ hc.CN x, ⁅c, y⁆ ∈ Q := fun c => Iff.rfl
  refine ⟨C, hCR, ?_, ?_, fun c hc => ((hCmem c).mp hc).2⟩
  · intro g hg c hcC
    have hgcR : g * c * g⁻¹ ∈ Rt M (LB M Q B) x :=
      (Rt M (LB M Q B) x).mul_mem ((Rt M (LB M Q B) x).mul_mem hg hcC.1)
        ((Rt M (LB M Q B) x).inv_mem hg)
    refine (hCmem _).mpr ⟨hgcR, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ hc.CN x := by
      simpa using hc.CN_conj_mem hxL ((Rt M (LB M Q B) x).inv_mem hg) hy
    have e : ⁅g * c * g⁻¹, y⁆ = g * ⁅c, g⁻¹ * y * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp
      (hc.hyp.Q_normal.2 (hc.Rt_le_M x hg)) _).mp (hcC.2 _ hy')
  · intro z hz
    exact (hCmem z).mpr ⟨hLR (hZ0L hz),
      fun y hy => Subgroup.commutator_le.mp hZcomm z hz y hy⟩

private theorem transfer_of_simple {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {x : G} (hxL : x ∈ LB M Q B) {C : Subgroup G}
    {φ : ↥(Rt M (LB M Q B) x) →* GL ι K}
    (hker : φ.ker = (hc.CN x).subgroupOf (Rt M (LB M Q B) x))
    (hsimple : IsSimpleGroup ↥φ.range) (hCR : C ≤ Rt M (LB M Q B) x)
    (hCnorm : ∀ ρ ∈ Rt M (LB M Q B) x, ∀ c ∈ C, ρ * c * ρ⁻¹ ∈ C)
    {Z0 : Subgroup G} (hZ0C : Z0 ≤ C) (htZ : t ∈ Z0) (htN : t ∉ hc.CN x) :
    ∀ r ∈ Rt M (LB M Q B) x, ∃ c ∈ C, c⁻¹ * r ∈ hc.CN x := by
  haveI := hsimple
  have hNR : hc.CN x ≤ Rt M (LB M Q B) x := fun y hy => (Ctx.mem_CN.mp hy).1
  have hkerc : φ.rangeRestrict.ker = (hc.CN x).subgroupOf (Rt M (LB M Q B) x) := by
    rw [MonoidHom.ker_rangeRestrict, hker]
  have hkercond : ∀ r : ↥(Rt M (LB M Q B) x),
      φ.rangeRestrict r = 1 ↔ (r : G) ∈ hc.CN x := by
    intro r
    rw [← MonoidHom.mem_ker, hkerc, Subgroup.mem_subgroupOf]
  have hdich := simpleDichotomy_holds G (Rt M (LB M Q B) x) (hc.CN x) C ↥φ.range
    φ.rangeRestrict hNR φ.rangeRestrict_surjective hkercond hCnorm
  rcases hdich with hleft | hright
  · exfalso
    have htR : t ∈ Rt M (LB M Q B) x := hCR (hZ0C htZ)
    exact htN (hleft (Subgroup.mem_inf.mpr ⟨hZ0C htZ, htR⟩))
  · intro r hrR
    have hLE : (C ⊓ Rt M (LB M Q B) x : Subgroup G) ≤
        Subgroup.normalizer (hc.CN x : Set G) := by
      intro y hy
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      exact hc.CN_conj_mem hxL hy.2 hn
    have hmem : r ∈ (↑((C ⊓ Rt M (LB M Q B) x) ⊔ hc.CN x) : Set G) := hright hrR
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (C ⊓ Rt M (LB M Q B) x)
      (hc.CN x) hLE] at hmem
    obtain ⟨c, hcC, y, hyN, hcy⟩ := Set.mem_mul.mp hmem
    refine ⟨c, hcC.1, ?_⟩
    have e : c⁻¹ * r = y := by rw [← hcy]; group
    rw [e]
    exact hyN

open CFSG.ComponentClassification.RankTwoClassical.ORigid in
private theorem centralizer_transfer {x : G} (hx7 : Sec7Hyp hc n x) {C : Subgroup G}
    (hCR : C ≤ Rt M (LB M Q B) x)
    (hCnorm : ∀ ρ ∈ Rt M (LB M Q B) x, ∀ c ∈ C, ρ * c * ρ⁻¹ ∈ C)
    (hZ0C : Z0 ≤ C) (htZ : t ∈ Z0) (htN : t ∉ hc.CN x) :
    ∀ r ∈ Rt M (LB M Q B) x, ∃ c ∈ C, c⁻¹ * r ∈ hc.CN x := by
  obtain ⟨m, hm, hor⟩ := hx7.orth
  rcases hor with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  · have hm3 : 3 ≤ m := by
      rcases Nat.lt_or_ge m 3 with hlt | hge
      · have hm2 : m = 2 := by omega
        subst hm2
        exact absurd ⟨K, fK, finK, hK, hnat⟩ hx7.notPlus4
      · exact hge
    obtain ⟨φ, hrange, hker, -⟩ := hnat
    haveI : CharP K 2 := by
      obtain ⟨n, -, hn, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans hn)
    have hsimple : IsSimpleGroup ↥φ.range := by
      rw [hrange]
      exact (endg_omegaPlus_facts (by rw [hK]; exact hc.hyp.q4) hm3).1
    exact transfer_of_simple hx7.toSec5.mem hker hsimple hCR hCnorm hZ0C htZ htN
  · obtain ⟨φ, hrange, hker, -⟩ := hnat
    haveI : CharP K 2 := by
      obtain ⟨n, -, hn, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans hn)
    have hsimple : IsSimpleGroup ↥φ.range := by
      rw [hrange]
      exact isSimpleGroup_statedOmega_quadMinus_of_two_le hm hirr
    exact transfer_of_simple hx7.toSec5.mem hker hsimple hCR hCnorm hZ0C htZ htN

private theorem centralizer_transfer_sp {x : G} (hs8 : Sec8Hyp hc n x) {C : Subgroup G}
    (hCR : C ≤ Rt M (LB M Q B) x)
    (hCnorm : ∀ ρ ∈ Rt M (LB M Q B) x, ∀ c ∈ C, ρ * c * ρ⁻¹ ∈ C)
    (hZ0C : Z0 ≤ C) (htZ : t ∈ Z0) (htN : t ∉ hc.CN x) :
    ∀ r ∈ Rt M (LB M Q B) x, ∃ c ∈ C, c⁻¹ * r ∈ hc.CN x := by
  obtain ⟨m, hm, K, fK, finK, hK, φ, hrange, hker, -⟩ := hs8.sp
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hsimple : IsSimpleGroup ↥φ.range := by
    rw [hrange]
    exact (endg_sp_facts (by rw [hK]; exact hc.hyp.q4) hm).1
  exact transfer_of_simple hs8.toSec5.mem hker hsimple hCR hCnorm hZ0C htZ htN

private theorem commutator_R_CN_le (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G} (hxL : x ∈ LB M Q B) {Z0x : Subgroup G}
    (hZ0x : IsCentrePre Z0x (Rt M (LB M Q B) x) Q)
    (hZH : Z0x ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B))
    (hcent : ∀ a ∈ hc.CN x, (∀ b ∈ hc.CN x, ⁅a, b⁆ ∈ Q) → a ∈ Z0x)
    (hcommCN : ⁅hc.CN x, hc.CN x⁆ ≤ Z0x)
    (htransfer : ∀ C : Subgroup G, C ≤ Rt M (LB M Q B) x →
      (∀ ρ ∈ Rt M (LB M Q B) x, ∀ c ∈ C, ρ * c * ρ⁻¹ ∈ C) → Z0 ≤ C →
      ∀ r ∈ Rt M (LB M Q B) x, ∃ c ∈ C, c⁻¹ * r ∈ hc.CN x) :
    ∀ r ∈ Rt M (LB M Q B) x, ∀ n ∈ hc.CN x, ⁅n, r⁆ ∈ Z0x := by
  have hZ0L : Z0 ≤ LB M Q B := sec93Omega_Z0_le_LB h34 h311a h311bComm cfg.hs cfg.hr cfg.hZ0
  have hZQ := Z0_inf_CN_eq h34 h311a h311bComm cfg hxL hZH hcent hcommCN
  have hZcomm : ⁅Z0, hc.CN x⁆ ≤ Q :=
    commutator_Z0_CN_le h34 h311a h311bComm cfg hxL hZH hcent hcommCN
  obtain ⟨C, hCR, hCnorm, hZ0C, hCcomm⟩ := exists_centralizer hxL hZ0L hZcomm
  have htZ : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) cfg.hs.mem cfg.hZ0
  have htN : t ∉ hc.CN x := by
    intro ht
    have h : t ∈ Z0 ⊓ hc.CN x := Subgroup.mem_inf.mpr ⟨htZ, ht⟩
    rw [hZQ] at h
    exact cfg.hs.notQ h
  have htransferC := htransfer C hCR hCnorm hZ0C
  have hQn : ∀ ρ ∈ Rt M (LB M Q B) x, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M x hρ)) y).mp hy
  have hQZ0x : Q ≤ Z0x := hZ0x.Q_le (hc.Q_le_Rt hxL) hQn
  intro r hrR n hnN
  obtain ⟨c, hcC, hyN⟩ := htransferC r hrR
  have h1 : ⁅n, c⁆ ∈ Q := by
    have h := hCcomm c hcC n hnN
    rw [show ⁅n, c⁆ = ⁅c, n⁆⁻¹ by
      simp only [commutatorElement_def]; group]
    exact Q.inv_mem h
  have h2 : ⁅n, c⁻¹ * r⁆ ∈ Z0x := hcommCN (Subgroup.commutator_mem_commutator hnN hyN)
  have h3 : c * ⁅n, c⁻¹ * r⁆ * c⁻¹ ∈ Z0x :=
    (Subgroup.mem_normalizer_iff.mp
      (hZ0x.mem_normalizer hQn (hCR hcC)) _).mp h2
  have hsum : ⁅n, c * (c⁻¹ * r)⁆ = ⁅n, c⁆ * (c * ⁅n, c⁻¹ * r⁆ * c⁻¹) := by
    simp only [commutatorElement_def]; group
  have hr : r = c * (c⁻¹ * r) := by group
  rw [hr, hsum]
  exact Z0x.mul_mem (hQZ0x h1) h3

private theorem card_CN_of_conc78 {m : ℕ} (h : Conc78 hc n t m) :
    ∃ k : ℕ, 9 ≤ k ∧ Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ k := by
  rcases h with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩
  · exact ⟨9, le_rfl, h⟩
  · exact ⟨17, by norm_num, h⟩
  · exact ⟨9, le_rfl, h⟩
  · exact ⟨17, by norm_num, h⟩
  · exact ⟨33, by norm_num, h⟩

private theorem card_CN_lt (h78 : Stroth78Statement) (h311bCard : Stroth311bCardStatement)
    (hZc : Sec7CentreMpStatement) (hZt : Sec7ZtStatement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxH : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hx7 : Sec7Hyp hc n x)
    {Z0x : Subgroup G} (hZ0x : IsCentrePre Z0x (Rt M (LB M Q B) x) Q) :
    2 * Nat.card ↥Z0x < Nat.card ↥(hc.CN x) := by
  have hxL : x ∈ LB M Q B := hx7.toSec5.mem
  have hxL' : x ∈ conjSubgroup h (LB M Q B) := (Subgroup.mem_inf.mp hxH).2
  have hZ0xL : Z0x ≤ LB M Q B :=
    (centre_le_inf hZc hZt cfg hxH hx7 hZ0x).trans inf_le_left
  have hRne : Rt M (LB M Q B) x ≠ LB M Q B := Rt_ne_LB cfg hxL'
  have hT := centre_char hx7 hZ0x hZ0xL
  have hcardZ0x : Nat.card ↥Z0x ≤ Nat.card Q * Nat.card Z :=
    h311bCard G M Q Z B hc n hx7.toSec5.width hx7.toSec5.n_gt hx7.toSec5.noA2
      hx7.toSec5.gen x hxL hx7.toSec5.notQ hRne hx7.not_slNat Z0x hT
  obtain ⟨m, hm, hor⟩ := hx7.orth
  have hconc : Conc78 hc n x m :=
    h78 G M Q Z B hc n x hx7.toSec5 hx7.large hx7.notPlus4 m hm hor
  obtain ⟨k, hk, hcardN⟩ := card_CN_of_conc78 hconc
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hZpos : 0 < Nat.card Z := by have := hc.hyp.q4; omega
  have h8 : 2 < Nat.card Z ^ 8 := by
    calc 2 < 4 ^ 2 := by norm_num
      _ ≤ (Nat.card Z) ^ 2 := Nat.pow_le_pow_left hc.hyp.q4 2
      _ ≤ (Nat.card Z) ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2 : 2 * Nat.card Z < Nat.card Z ^ 9 := by
    calc 2 * Nat.card Z < (Nat.card Z) ^ 8 * Nat.card Z :=
        Nat.mul_lt_mul_of_pos_right h8 hZpos
      _ = (Nat.card Z) ^ 9 := by ring
  have hmid : 2 * (Nat.card Q * Nat.card Z) < Nat.card Q * Nat.card Z ^ 9 := by
    rw [show 2 * (Nat.card Q * Nat.card Z) = Nat.card Q * (2 * Nat.card Z) by ring]
    exact Nat.mul_lt_mul_of_pos_left h2 hQpos
  calc 2 * Nat.card ↥Z0x
      ≤ 2 * (Nat.card Q * Nat.card Z) := Nat.mul_le_mul_left 2 hcardZ0x
    _ < Nat.card Q * Nat.card Z ^ 9 := hmid
    _ ≤ Nat.card Q * Nat.card Z ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZpos hk)
    _ = Nat.card ↥(hc.CN x) := hcardN.symm

private theorem not_central_of_min {R N Zc : Subgroup G}
    (hsq : ∀ y ∈ N, y ^ 2 ∈ Zc) (hlt : Zc < N) (hNR : N ≤ R)
    (hNinv : ∀ r ∈ R, conjSubgroup r N = N)
    (hZR : ∀ r ∈ R, conjSubgroup r Zc = Zc)
    (hmin : ∀ A : Subgroup G, Zc ≤ A → A ≤ N → (∀ r ∈ R, conjSubgroup r A = A) → A ≠ Zc →
      2 * Nat.card ↥Zc < Nat.card ↥A) :
    ¬ ∀ r ∈ R, ∀ n ∈ N, ⁅n, r⁆ ∈ Zc := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  haveI : WellFoundedLT (Subgroup G) := Finite.to_wellFoundedLT
  intro hall
  let S : Set (Subgroup G) := {A | Zc < A ∧ A ≤ N ∧ ∀ r ∈ R, conjSubgroup r A = A}
  have hNS : N ∈ S := ⟨hlt, le_rfl, hNinv⟩
  obtain ⟨A₀, hA₀S, hA₀min⟩ := (wellFounded_lt (α := Subgroup G)).has_min S ⟨N, hNS⟩
  have hA₀S' : Zc < A₀ ∧ A₀ ≤ N ∧ ∀ r ∈ R, conjSubgroup r A₀ = A₀ := hA₀S
  obtain ⟨hZcA₀, hA₀N, hA₀inv⟩ := hA₀S'
  have hirr : IsIrredModule R A₀ Zc := by
    refine ⟨?_, ?_, hZcA₀, ?_⟩
    · intro a ha b hb
      have h := hall a (hNR (hA₀N ha)) b (hA₀N hb)
      rw [show ⁅a, b⁆ = ⁅b, a⁆⁻¹ by simp only [commutatorElement_def]; group]
      exact Zc.inv_mem h
    · intro a ha
      exact hsq a (hA₀N ha)
    · intro U hZcU hUA₀ hUinv
      by_cases hUZ : U = Zc
      · exact Or.inl hUZ
      · right
        have hUS : U ∈ S := ⟨lt_of_le_of_ne hZcU (Ne.symm hUZ), hUA₀.trans hA₀N, hUinv⟩
        by_contra hne
        exact hA₀min U hUS (lt_of_le_of_ne hUA₀ hne)
  have hcomm : ∀ r ∈ R, ∀ n ∈ A₀, ⁅n, r⁆ ∈ Zc := fun r hr n hn => hall r hr n (hA₀N hn)
  exact (not_central_of_irred hirr (hA₀N.trans hNR) hZR
    (hmin A₀ hZcA₀.le hA₀N hA₀inv (ne_of_gt hZcA₀))) hcomm

private theorem two_mul_card_lt_of_card_pow_le {Z0x A : Subgroup G} {k : ℕ}
    (hZ : 4 ≤ Nat.card Z) (hk : 1 ≤ k) (h : Nat.card ↥Z0x * Nat.card Z ^ k ≤ Nat.card ↥A) :
    2 * Nat.card ↥Z0x < Nat.card ↥A := by
  have hZpos : 0 < Nat.card Z := lt_of_lt_of_le (by norm_num) hZ
  have h2 : 2 < Nat.card Z ^ k := by
    calc 2 < Nat.card Z := lt_of_lt_of_le (by norm_num) hZ
      _ = Nat.card Z ^ 1 := (pow_one _).symm
      _ ≤ Nat.card Z ^ k := Nat.pow_le_pow_right hZpos hk
  have hZ0pos : 0 < Nat.card ↥Z0x := Nat.card_pos
  calc 2 * Nat.card ↥Z0x = Nat.card ↥Z0x * 2 := by ring
    _ < Nat.card ↥Z0x * Nat.card Z ^ k := Nat.mul_lt_mul_of_pos_left h2 hZ0pos
    _ ≤ Nat.card ↥A := h

private theorem centre_data (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (hZc : Sec7CentreMpStatement) (hZt : Sec7ZtStatement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxH : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hx7 : Sec7Hyp hc n x)
    {Z0x : Subgroup G} (hZ0x : IsCentrePre Z0x (Rt M (LB M Q B) x) Q)
    (hcent : ∀ a ∈ hc.CN x, (∀ b ∈ hc.CN x, ⁅a, b⁆ ∈ Q) → a ∈ Z0x) :
    Z0x ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B) ∧ ⁅hc.CN x, hc.CN x⁆ ≤ Z0x ∧
      Z0x < hc.CN x ∧
      ∀ C : Subgroup G, C ≤ Rt M (LB M Q B) x →
        (∀ ρ ∈ Rt M (LB M Q B) x, ∀ c ∈ C, ρ * c * ρ⁻¹ ∈ C) → Z0 ≤ C →
        ∀ r ∈ Rt M (LB M Q B) x, ∃ c ∈ C, c⁻¹ * r ∈ hc.CN x := by
  have hZH := centre_le_inf hZc hZt cfg hxH hx7 hZ0x
  have hcommCN := commutator_CN_le h311bComm cfg hxH.2 hx7 hZ0x (hZH.trans inf_le_left)
  have hZNx : Z0x ≤ hc.CN x := sec7ctr_Z0_le_CN hc hx7 hZ0x
  have hcardZ0x : Nat.card ↥Z0x ≤ Nat.card Q * Nat.card Z := by
    have hRne : Rt M (LB M Q B) x ≠ LB M Q B := Rt_ne_LB cfg hxH.2
    exact h311bCard G M Q Z B hc n hx7.toSec5.width hx7.toSec5.n_gt hx7.toSec5.noA2
      hx7.toSec5.gen x hx7.toSec5.mem hx7.toSec5.notQ hRne hx7.not_slNat Z0x
      (centre_char hx7 hZ0x (hZH.trans inf_le_left))
  have hlt : Z0x < hc.CN x := by
    refine lt_of_le_of_ne hZNx ?_
    intro heq
    rw [heq] at hcardZ0x
    exact absurd hcardZ0x (not_le.mpr hx7.large)
  have hZQ := Z0_inf_CN_eq h34 h311a h311bComm cfg hx7.toSec5.mem hZH hcent hcommCN
  have htZ : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) cfg.hs.mem cfg.hZ0
  have htN : t ∉ hc.CN x := by
    intro ht
    have h : t ∈ Z0 ⊓ hc.CN x := Subgroup.mem_inf.mpr ⟨htZ, ht⟩
    rw [hZQ] at h
    exact cfg.hs.notQ h
  exact ⟨hZH, hcommCN, hlt,
    fun C hCR hCnorm hZ0C => centralizer_transfer hx7 hCR hCnorm hZ0C htZ htN⟩

private theorem false_of_core (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G} (hxL : x ∈ LB M Q B) {Z0x : Subgroup G}
    (hZ0x : IsCentrePre Z0x (Rt M (LB M Q B) x) Q)
    (hZH : Z0x ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B))
    (hcent : ∀ a ∈ hc.CN x, (∀ b ∈ hc.CN x, ⁅a, b⁆ ∈ Q) → a ∈ Z0x)
    (hcommCN : ⁅hc.CN x, hc.CN x⁆ ≤ Z0x)
    (htransfer : ∀ C : Subgroup G, C ≤ Rt M (LB M Q B) x →
      (∀ ρ ∈ Rt M (LB M Q B) x, ∀ c ∈ C, ρ * c * ρ⁻¹ ∈ C) → Z0 ≤ C →
      ∀ r ∈ Rt M (LB M Q B) x, ∃ c ∈ C, c⁻¹ * r ∈ hc.CN x)
    (hsq : ∀ y ∈ hc.CN x, y ^ 2 ∈ Z0x) (hlt : Z0x < hc.CN x)
    (hmin : ∀ A : Subgroup G, Z0x ≤ A → A ≤ hc.CN x →
      (∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r A = A) → A ≠ Z0x →
      2 * Nat.card ↥Z0x < Nat.card ↥A) : False := by
  have hcomm := commutator_R_CN_le h34 h311a h311bComm cfg hxL hZ0x hZH hcent hcommCN htransfer
  have hQn : ∀ ρ ∈ Rt M (LB M Q B) x, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M x hρ)) y).mp hy
  have hZR : ∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r Z0x = Z0x := fun r hr =>
    conjSubgroup_eq_self_iff.mpr (hZ0x.mem_normalizer hQn hr)
  have hNinv : ∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r (hc.CN x) = hc.CN x := by
    intro r hr
    refine conjSubgroup_eq_self_iff.mpr (Subgroup.mem_normalizer_fintype fun y hy => ?_)
    exact hc.CN_conj_mem hxL hr hy
  have hNR : hc.CN x ≤ Rt M (LB M Q B) x := fun y hy => (Ctx.mem_CN.mp hy).1
  exact (not_central_of_min hsq hlt hNR hNinv hZR hmin) hcomm

theorem false_of_irred (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h78 : Stroth78Statement) (h711 : Stroth711StrongStatement)
    (hZc : Sec7CentreMpStatement) (hZt : Sec7ZtStatement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxH : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hx7 : Sec7Hyp hc n x)
    {Z0x : Subgroup G} (hZ0x : IsCentrePre Z0x (Rt M (LB M Q B) x) Q)
    (hirr : IsIrredModule (Rt M (LB M Q B) x) (hc.CN x) Z0x) : False := by
  have hcent := mem_centre_of_centralizes h711 hx7 hZ0x hirr
  obtain ⟨hZH, hcommCN, -, htransfer⟩ :=
    centre_data h34 h311a h311bComm h311bCard hZc hZt cfg hxH hx7 hZ0x hcent
  have hmin : ∀ A : Subgroup G, Z0x ≤ A → A ≤ hc.CN x →
      (∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r A = A) → A ≠ Z0x →
      2 * Nat.card ↥Z0x < Nat.card ↥A := by
    intro A hZA hAN hinv hne
    rcases hirr.2.2.2 A hZA hAN hinv with h | h
    · exact absurd h hne
    · rw [h]
      exact card_CN_lt h78 h311bCard hZc hZt cfg hxH hx7 hZ0x
  exact false_of_core h34 h311a h311bComm cfg hx7.toSec5.mem hZ0x hZH hcent hcommCN htransfer
    hirr.2.1 hirr.2.2.1 hmin

theorem false_of_omegaPlus3 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hZc : Sec7CentreMpStatement) (hZt : Sec7ZtStatement)
    (hMin : Sec79MinOrderStatement) (hZN : Sec717ZNStatement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxH : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hx7 : Sec7Hyp hc n x)
    (hP3 : OmegaPlusNat hc x 3) : False := by
  obtain ⟨Z0x, hZ0x⟩ := Ctx.exists_centre hc hx7.toSec5.mem
  haveI := hc.normal_Q_in_M
  have hcent : ∀ a ∈ hc.CN x, (∀ b ∈ hc.CN x, ⁅a, b⁆ ∈ Q) → a ∈ Z0x :=
    fun a ha hb => (hZN G M Q Z B hc n x hx7 hP3 Z0x hZ0x a).mpr ⟨ha, hb⟩
  obtain ⟨hZH, hcommCN, hlt, htransfer⟩ :=
    centre_data h34 h311a h311bComm h311bCard hZc hZt cfg hxH hx7 hZ0x hcent
  obtain ⟨r', hr'⟩ := hA G M Q Z B hc n x hx7
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hx7.toSec5 (Or.inr hx7.omegaNat) hr' hZ0x
    (sec7ctr_Z0_le_CN hc hx7 hZ0x)
  have hsq : ∀ y ∈ hc.CN x, y ^ 2 ∈ Z0x := hopp.2.2.2.2.2.2.2.1
  have hmin : ∀ A : Subgroup G, Z0x ≤ A → A ≤ hc.CN x →
      (∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r A = A) → A ≠ Z0x →
      2 * Nat.card ↥Z0x < Nat.card ↥A := by
    intro A hZA hAN hinv hne
    have h := (hMin G M Q Z B hc n x hx7 Z0x hZ0x A hZA hAN hinv hne 3
      (by norm_num)).2 hP3 (by norm_num)
    exact two_mul_card_lt_of_card_pow_le hc.hyp.q4 (by norm_num) h
  exact false_of_core h34 h311a h311bComm cfg hx7.toSec5.mem hZ0x hZH hcent hcommCN htransfer
    hsq hlt hmin

theorem false_of_omegaPlus4 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hZc : Sec7CentreMpStatement) (hZt : Sec7ZtStatement)
    (hMin : Sec79MinOrderStatement) (h715 : Step715ZNStatement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxH : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hx7 : Sec7Hyp hc n x)
    (hP4 : OmegaPlusNat hc x 4) : False := by
  obtain ⟨Z0x, hZ0x⟩ := Ctx.exists_centre hc hx7.toSec5.mem
  have hcent : ∀ a ∈ hc.CN x, (∀ b ∈ hc.CN x, ⁅a, b⁆ ∈ Q) → a ∈ Z0x :=
    fun a ha hb => (h715 G M Q Z B hc n x hx7 hP4 Z0x hZ0x a).mpr ⟨ha, hb⟩
  obtain ⟨hZH, hcommCN, hlt, htransfer⟩ :=
    centre_data h34 h311a h311bComm h311bCard hZc hZt cfg hxH hx7 hZ0x hcent
  obtain ⟨r', hr'⟩ := hA G M Q Z B hc n x hx7
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hx7.toSec5 (Or.inr hx7.omegaNat) hr' hZ0x
    (sec7ctr_Z0_le_CN hc hx7 hZ0x)
  have hsq : ∀ y ∈ hc.CN x, y ^ 2 ∈ Z0x := hopp.2.2.2.2.2.2.2.1
  have hmin : ∀ A : Subgroup G, Z0x ≤ A → A ≤ hc.CN x →
      (∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r A = A) → A ≠ Z0x →
      2 * Nat.card ↥Z0x < Nat.card ↥A := by
    intro A hZA hAN hinv hne
    have h := (hMin G M Q Z B hc n x hx7 Z0x hZ0x A hZA hAN hinv hne 4
      (by norm_num)).2 hP4 (by norm_num)
    exact two_mul_card_lt_of_card_pow_le hc.hyp.q4 (by norm_num) h
  exact false_of_core h34 h311a h311bComm cfg hx7.toSec5.mem hZ0x hZH hcent hcommCN htransfer
    hsq hlt hmin

theorem false_of_sec7Hyp (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (h78 : Stroth78Statement) (h79 : Stroth79Statement) (h711 : Stroth711StrongStatement)
    (hZc : Sec7CentreMpStatement) (hZt : Sec7ZtStatement)
    (hMin : Sec79MinOrderStatement) (hZN : Sec717ZNStatement) (h715 : Step715ZNStatement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxH : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hx7 : Sec7Hyp hc n x) : False := by
  rcases h79 G M Q Z B hc n x hx7.toSec5 hx7.large hx7.notPlus4 hx7.orth with
    ⟨Z0x, hZ0x, hirr⟩ | h3 | ⟨h4, -⟩
  · exact false_of_irred h34 h311a h311bComm h311bCard h78 h711 hZc hZt cfg hxH hx7 hZ0x hirr
  · exact false_of_omegaPlus3 h34 h311a h311bComm h311bCard h51 hA hZc hZt hMin hZN cfg hxH hx7 h3
  · exact false_of_omegaPlus4 h34 h311a h311bComm h311bCard h51 hA hZc hZt hMin h715 cfg hxH hx7 h4

theorem false_of_omegaNat (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (h78 : Stroth78Statement) (h79 : Stroth79Statement) (h711 : Stroth711StrongStatement)
    (hZc : Sec7CentreMpStatement) (hZt : Sec7ZtStatement)
    (hMin : Sec79MinOrderStatement) (hZN : Sec717ZNStatement) (h715 : Step715ZNStatement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxH : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hxQ : x ∉ Q) (hΩ : OmegaNat hc x)
    (h4 : ¬ OmegaPlusNat hc x 2) : False :=
  false_of_sec7Hyp h34 h311a h311bComm h311bCard h51 hA h78 h79 h711 hZc hZt hMin hZN h715
    cfg hxH (cfg.hs.sec7Hyp_of_omegaNat hxH.1 hxQ hΩ h4)

theorem false_of_spNat (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement)
    (h51 : Stroth51Statement) (hA8 : Sec8AExistsStatement) (h83 : Stroth83Statement)
    (h84 : Stroth84Statement)
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxH : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hxQ : x ∉ Q) (hsp : SpNat hc x) :
    False := by
  have hMin8 : Sec86MinOrderStatement := sec86MinOrder_of h51 hA8 (sec5NatPointsSp_of_34 h34)
  have hIrr8 : Sec86IrredStatement := sec86Irred_of_inputs h83 h51 hA8 hMin8
  have hs8 : Sec8Hyp hc n x := cfg.hs.sec8Hyp_of_spNat hxH.1 hxQ hsp
  obtain ⟨Z0x, hZ0x⟩ := Ctx.exists_centre hc hs8.toSec5.mem
  have hirr := hIrr8 G M Q Z B hc n x hs8 Z0x hZ0x
  have hRc := (rt_vt_conj hc cfg.hh x).1
  have hZ0x' : IsCentrePre Z0x (Rt M (LB M Q (conjSubgroup h B)) x) Q := by
    rw [hRc]; exact hZ0x
  have hZH' : Z0x ≤ LB M Q (conjSubgroup h B) :=
    sec8_Z0_le_LB h51 hA8 (hc.conj_of_mem cfg.hh) (hs8.conjBase cfg.hh hxH.2) hZ0x'
  have hZH : Z0x ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B) :=
    le_inf (sec8_Z0_le_LB h51 hA8 hc hs8 hZ0x) (by rwa [hc.LB_conj cfg.hh] at hZH')
  have hQn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) q).mp hq
  have hRM : Rt M (LB M Q B) x ≤ M := hc.Rt_le_M x
  have hNR : hc.CN x ≤ Rt M (LB M Q B) x := fun y hy => (Ctx.mem_CN.1 hy).1
  have hNn : ∀ ρ ∈ Rt M (LB M Q B) x, ∀ y ∈ hc.CN x, ρ * y * ρ⁻¹ ∈ hc.CN x :=
    fun ρ hρ y hy => hc.CN_conj_mem hs8.toSec5.mem hρ hy
  have hZN : Z0x ≤ hc.CN x := sec8_Z0_le_CN hc hs8 hZ0x
  have hcent : ∀ a ∈ hc.CN x, (∀ b ∈ hc.CN x, ⁅a, b⁆ ∈ Q) → a ∈ Z0x :=
    sec85_centre_le hQn hRM hNR hNn hZN (fun z hz b hb => hZ0x.comm_mem hz (hNR hb))
      hirr.2.2.2 (h84 G M Q Z B hc n x hs8)
  have hcommCN : ⁅hc.CN x, hc.CN x⁆ ≤ Z0x := Subgroup.commutator_le.mpr hirr.1
  have hZQ := Z0_inf_CN_eq h34 h311a h311bComm cfg hs8.toSec5.mem hZH hcent hcommCN
  have htZ : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) cfg.hs.mem cfg.hZ0
  have htN : t ∉ hc.CN x := by
    intro ht
    have h : t ∈ Z0 ⊓ hc.CN x := Subgroup.mem_inf.mpr ⟨htZ, ht⟩
    rw [hZQ] at h
    exact cfg.hs.notQ h
  have htransfer : ∀ C : Subgroup G, C ≤ Rt M (LB M Q B) x →
      (∀ ρ ∈ Rt M (LB M Q B) x, ∀ c ∈ C, ρ * c * ρ⁻¹ ∈ C) → Z0 ≤ C →
      ∀ r ∈ Rt M (LB M Q B) x, ∃ c ∈ C, c⁻¹ * r ∈ hc.CN x :=
    fun C hCR hCnorm hZ0C => centralizer_transfer_sp hs8 hCR hCnorm hZ0C htZ htN
  obtain ⟨m, hm, hspm⟩ := hs8.sp
  have hmin : ∀ A : Subgroup G, Z0x ≤ A → A ≤ hc.CN x →
      (∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r A = A) → A ≠ Z0x →
      2 * Nat.card ↥Z0x < Nat.card ↥A := by
    intro A hZA hAN hinv hne
    have h := hMin8 G M Q Z B hc n x hs8 Z0x hZ0x A hZA hAN hinv hne m hm hspm
    exact two_mul_card_lt_of_card_pow_le hc.hyp.q4 (Nat.one_le_pow m 2 (by norm_num)) h
  exact false_of_core h34 h311a h311bComm cfg hs8.toSec5.mem hZ0x hZH hcent hcommCN htransfer
    hirr.2.1 hirr.2.2.1 hmin

end S93O

end CFSG.RankThree.GF2n.Stroth80
