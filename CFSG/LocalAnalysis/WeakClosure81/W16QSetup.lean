module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDefs
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFam
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIa
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem w16q_normalizer_le_normalizer_centralizer (V : Subgroup G) :
    normalizer (V : Set G) ≤ normalizer (centralizer (V : Set G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := centralizer (V : Set G)) (K := normalizer (V : Set G))
      (Subgroup.centralizer_le_normalizer (V : Set G))).mp
    (inferInstance : ((centralizer (V : Set G)).subgroupOf
      (normalizer (V : Set G))).Normal)

structure Cfg1616 (M V₀ V U S H : Subgroup G) : Prop where
  std : Std15 G
  one : W16One G
  five : W16Five G
  fifteen : W16Fifteen G
  cex : Cex16 M V₀ V U S
  min : IsMinFam16 M U S H
  not_le : ¬ V ≤ pCoreOf 2 H

namespace Cfg1616

variable {M V₀ V U S H : Subgroup G}

theorem sup_eq (c : Cfg1616 M V₀ V U S H) : S ⊔ conjClosure V H = H :=
  IsMinFam16.sup_conjClosure_eq c.one c.std c.cex c.min c.not_le

theorem conjClosure_le_H (c : Cfg1616 M V₀ V U S H) : conjClosure V H ≤ H :=
  CFSG.Quasithin.conjClosure_le fun _ hh _ hv =>
    H.mul_mem (H.mul_mem hh (c.min.fam16.1 (c.cex.V_le_S hv))) (H.inv_mem hh)

theorem not_conjClosure_le (c : Cfg1616 M V₀ V U S H) : ¬ conjClosure V H ≤ M := by
  intro hK
  exact c.min.fam16.2.2 (c.sup_eq ▸ sup_le c.cex.S_le_M hK)

theorem conjClosure_le_centralizer (c : Cfg1616 M V₀ V U S H) :
    conjClosure V H ≤ centralizer (U : Set G) :=
  c.conjClosure_le_H.trans c.min.fam16.2.1

theorem inf_centralizer_eq_bot (c : Cfg1616 M V₀ V U S H) :
    V₀ ⊓ centralizer (conjClosure V H : Set G) = ⊥ := by
  by_contra hne
  obtain ⟨⟨w, hwV, hwC⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  refine c.not_conjClosure_le fun x hx => c.cex.hyp.centralizer_le hwV
    (fun h1 => hw1 (Subtype.ext h1)) ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.1 hwC x hx

theorem le_iSub16 (c : Cfg1616 M V₀ V U S H) : U ⊔ V₀ ≤ iSub16 V H := by
  rw [← Cex16.inf_pCoreOf_eq c.one c.five c.std c.cex c.min.fam16 c.not_le]
  exact le_conjClosure _ _

theorem iSub16_eq (c : Cfg1616 M V₀ V U S H) : iSub16 V H = conjClosure (U ⊔ V₀) H := by
  rw [iSub16, Cex16.inf_pCoreOf_eq c.one c.five c.std c.cex c.min.fam16 c.not_le]

theorem iSub16_le_conjClosure (c : Cfg1616 M V₀ V U S H) : iSub16 V H ≤ conjClosure V H :=
  conjClosure_mono inf_le_left le_rfl

theorem V_le_tSub16 (c : Cfg1616 M V₀ V U S H) : V ≤ tSub16 V₀ S :=
  le_inf c.cex.V_le_S fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw =>
    (B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian (c.cex.hyp.h6.le hw) hv)

theorem iSub16_le_tSub16 (c : Cfg1616 M V₀ V U S H) : iSub16 V H ≤ tSub16 V₀ S := by
  refine le_inf ((Cex16.iSub16_le_pCoreOf c.cex c.min.fam16).trans
    (c.cex.pCoreOf_le_S c.one c.std c.min.fam16)) fun i hi => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact B2F.isElemAbelian_comm (Cex16.isElemAbelian_iSub16 c.one c.std c.cex c.min.fam16)
    (c.le_iSub16 (Subgroup.mem_sup_right hw)) hi

theorem sup_le_H (c : Cfg1616 M V₀ V U S H) : conjClosure V H ⊔ tSub16 V₀ S ≤ H :=
  sup_le c.conjClosure_le_H (inf_le_left.trans c.min.fam16.1)

private theorem w16q_s_le_normalizer_tSub16 (c : Cfg1616 M V₀ V U S H) :
    S ≤ normalizer (tSub16 V₀ S : Set G) := by
  have hSN : S ≤ normalizer (centralizer (V₀ : Set G) : Set G) :=
    (c.cex.S_le_M.trans c.cex.hyp.h6.le_normalizer₀).trans
      (w16q_normalizer_le_normalizer_centralizer V₀)
  have hle : S ≤ normalizer (S : Set G) ⊓
      normalizer (centralizer (V₀ : Set G) : Set G) :=
    le_inf (le_normalizer (H := S)) hSN
  have := hle.trans (inf_normalizer_le_normalizer_inf (H := S)
    (K := centralizer (V₀ : Set G)))
  simpa [tSub16] using this

private theorem w16q_conj_mem_sup_tSub16 (c : Cfg1616 M V₀ V U S H)
    {g : G} (hg : g ∈ conjClosure V H) {t : G} (ht : t ∈ tSub16 V₀ S) :
    g * t * g⁻¹ ∈ conjClosure V H ⊔ tSub16 V₀ S := by
  have hTS : tSub16 V₀ S ≤ S := inf_le_left
  have htH : t ∈ H := c.min.fam16.1 (hTS ht)
  have htN : t ∈ normalizer (conjClosure V H : Set G) :=
    le_normalizer_conjClosure V H htH
  have htg : t * g⁻¹ * t⁻¹ ∈ conjClosure V H := by
    have h := (conjClosure V H).inv_mem ((Subgroup.mem_normalizer_iff.mp htN g).1 hg)
    rwa [show (t * g * t⁻¹)⁻¹ = t * g⁻¹ * t⁻¹ by group] at h
  have hd : g * t * g⁻¹ * t⁻¹ ∈ conjClosure V H := by
    have h := (conjClosure V H).mul_mem hg htg
    rwa [show g * (t * g⁻¹ * t⁻¹) = g * t * g⁻¹ * t⁻¹ by group] at h
  have hsplit : g * t * g⁻¹ = (g * t * g⁻¹ * t⁻¹) * t := by group
  rw [hsplit]
  exact (conjClosure V H ⊔ tSub16 V₀ S).mul_mem (Subgroup.mem_sup_left hd)
    (Subgroup.mem_sup_right ht)

private theorem w16q_conjClosure_le_normalizer_sup_tSub16 (c : Cfg1616 M V₀ V U S H) :
    conjClosure V H ≤
      normalizer ((conjClosure V H ⊔ tSub16 V₀ S : Subgroup G) : Set G) := by
  have hTK : tSub16 V₀ S ≤ normalizer (conjClosure V H : Set G) :=
    ((inf_le_left : tSub16 V₀ S ≤ S).trans c.min.fam16.1).trans
      (le_normalizer_conjClosure V H)
  have hconjK : ∀ g ∈ conjClosure V H, ∀ a ∈ conjClosure V H,
      g * a * g⁻¹ ∈ conjClosure V H := by
    intro g hg a ha
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure V H (c.conjClosure_le_H hg)) a).1 ha
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    change x ∈ ((conjClosure V H ⊔ tSub16 V₀ S : Subgroup G) : Set G) at hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (conjClosure V H) (tSub16 V₀ S) hTK,
      Set.mem_mul] at hx
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    have hstep : g * (a * t) * g⁻¹ = (g * a * g⁻¹) * (g * t * g⁻¹) := by group
    rw [hstep]
    exact (conjClosure V H ⊔ tSub16 V₀ S).mul_mem
      (Subgroup.mem_sup_left (hconjK g hg a ha))
      (w16q_conj_mem_sup_tSub16 c hg ht)
  · intro hx
    change g * x * g⁻¹ ∈ ((conjClosure V H ⊔ tSub16 V₀ S : Subgroup G) : Set G) at hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (conjClosure V H) (tSub16 V₀ S) hTK,
      Set.mem_mul] at hx
    obtain ⟨a, ha, t, ht, hxeq⟩ := hx
    have hg' : g⁻¹ ∈ conjClosure V H := (conjClosure V H).inv_mem hg
    have hstep : (g⁻¹ * a * g) * (g⁻¹ * t * g) = x := by
      calc (g⁻¹ * a * g) * (g⁻¹ * t * g) = g⁻¹ * (a * t) * g := by group
        _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hxeq]
        _ = x := by group
    rw [← hstep]
    exact (conjClosure V H ⊔ tSub16 V₀ S).mul_mem
      (Subgroup.mem_sup_left (by simpa only [inv_inv] using hconjK g⁻¹ hg' a ha))
      (by simpa only [inv_inv] using w16q_conj_mem_sup_tSub16 c hg' ht)

theorem le_normalizer_qSub16 (c : Cfg1616 M V₀ V U S H) :
    H ≤ normalizer (qSub16 V₀ V S H : Set G) := by
  have hNKT' : S ⊔ conjClosure V H ≤
      normalizer ((conjClosure V H ⊔ tSub16 V₀ S : Subgroup G) : Set G) := by
    have hSK : S ≤ normalizer (conjClosure V H : Set G) := by
      have h : S ⊔ conjClosure V H ≤ normalizer (conjClosure V H : Set G) := by
        rw [c.sup_eq]
        exact le_normalizer_conjClosure V H
      exact le_sup_left.trans h
    have hS : S ≤ normalizer
        ((conjClosure V H ⊔ tSub16 V₀ S : Subgroup G) : Set G) :=
      (le_inf hSK (w16q_s_le_normalizer_tSub16 c)).trans
        (inf_normalizer_le_normalizer_sup _ _)
    exact sup_le hS (w16q_conjClosure_le_normalizer_sup_tSub16 c)
  have hNKT : H ≤ normalizer ((conjClosure V H ⊔ tSub16 V₀ S : Subgroup G) : Set G) := by
    rwa [c.sup_eq] at hNKT'
  have hgoal : H ≤ normalizer
      (pCoreOf 2 (conjClosure V H ⊔ tSub16 V₀ S) : Set G) :=
    hNKT.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
      (conjClosure V H ⊔ tSub16 V₀ S))
  exact hgoal

theorem iSub16_le_qSub16 (c : Cfg1616 M V₀ V U S H) : iSub16 V H ≤ qSub16 V₀ V S H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  show iSub16 V H ≤ pCoreOf 2 (conjClosure V H ⊔ tSub16 V₀ S)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
  · exact c.iSub16_le_conjClosure.trans le_sup_left
  · exact c.sup_le_H.trans (le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H)
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le
      (Cex16.iSub16_le_pCoreOf c.cex c.min.fam16)

theorem qSub16_le_pCoreOf (c : Cfg1616 M V₀ V U S H) : qSub16 V₀ V S H ≤ pCoreOf 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  show pCoreOf 2 (conjClosure V H ⊔ tSub16 V₀ S) ≤ pCoreOf 2 H
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
  · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans c.sup_le_H
  · exact c.le_normalizer_qSub16
  · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem qSub16_le_centralizer (c : Cfg1616 M V₀ V U S H)
    (hQT : qSub16 V₀ V S H ≤ tSub16 V₀ S) :
    qSub16 V₀ V S H ≤ centralizer (iSub16 V H : Set G) := by
  refine Subgroup.le_centralizer_iff.2 ?_
  rw [c.iSub16_eq]
  refine conjClosure_le ?_
  intro h hh z hz
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨u, hu, w, hw, rfl⟩ := Cex16.exists_mul_of_mem_sup c.cex hz
  have hhu : h * u = u * h :=
    (Subgroup.mem_centralizer_iff.mp (c.min.fam16.2.1 hh) u hu).symm
  have huH : h * u * h⁻¹ = u := by rw [hhu]; group
  have hqh_mem : h⁻¹ * q * h ∈ qSub16 V₀ V S H :=
    (Subgroup.mem_normalizer_iff''.mp (c.le_normalizer_qSub16 hh) q).1 hq
  have hqh_cV₀ : h⁻¹ * q * h ∈ centralizer (V₀ : Set G) := (hQT hqh_mem).2
  have hqw : (h⁻¹ * q * h) * w = w * (h⁻¹ * q * h) :=
    (Subgroup.mem_centralizer_iff.mp hqh_cV₀ w hw).symm
  have hq_hw : q * (h * w * h⁻¹) = (h * w * h⁻¹) * q := by
    have hconj : h * (h⁻¹ * q * h) * h⁻¹ = q := by group
    calc q * (h * w * h⁻¹)
        = (h * (h⁻¹ * q * h) * h⁻¹) * (h * w * h⁻¹) := by rw [hconj]
      _ = h * ((h⁻¹ * q * h) * w) * h⁻¹ := by group
      _ = h * (w * (h⁻¹ * q * h)) * h⁻¹ := by rw [hqw]
      _ = (h * w * h⁻¹) * (h * (h⁻¹ * q * h) * h⁻¹) := by group
      _ = (h * w * h⁻¹) * q := by rw [hconj]
  have hq_u : q * u = u * q :=
    (Subgroup.mem_centralizer_iff.mp (c.cex.S_le_centralizer (hQT hq).1) u hu).symm
  have huw : h * (u * w) * h⁻¹ = u * (h * w * h⁻¹) := by
    calc h * (u * w) * h⁻¹ = (h * u * h⁻¹) * (h * w * h⁻¹) := by group
      _ = u * (h * w * h⁻¹) := by rw [huH]
  rw [huw]
  calc q * (u * (h * w * h⁻¹)) = (q * u) * (h * w * h⁻¹) := by group
    _ = (u * q) * (h * w * h⁻¹) := by rw [hq_u]
    _ = u * (q * (h * w * h⁻¹)) := by group
    _ = u * ((h * w * h⁻¹) * q) := by rw [hq_hw]
    _ = (u * (h * w * h⁻¹)) * q := by group

end Cfg1616

namespace Cex16

variable {M V₀ V U S : Subgroup G}

private theorem w16q_le_of_isSylowIn_of_le {H S T : Subgroup G} (hS : IsSylowIn 2 S H)
    (hST : S ≤ T) (hTH : T ≤ H) (hT : IsPGroup 2 T) : T ≤ S := by
  have h1 : S.relIndex T * T.relIndex H = S.relIndex H :=
    Subgroup.relIndex_mul_relIndex S T H hST hTH
  have hodd : ¬ 2 ∣ S.relIndex T := fun hd =>
    hS.not_dvd_relIndex (h1 ▸ Dvd.dvd.mul_right hd _)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hT
  have hdvd : S.relIndex T ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card (H := S) (K := T)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact hodd (hk ▸ dvd_pow_self 2 hk0)
  exact Subgroup.relIndex_eq_one.1 (by rw [hk, hk0, pow_zero])

private theorem w16q_conj_mem_sup_UV₀ (h : Cex16 M V₀ V U S) {R : Subgroup G}
    (hRC : R ≤ F11.CTilde M V₀ V) {r : G} (hr : r ∈ R) {x : G} (hx : x ∈ U ⊔ V₀) :
    r * x * r⁻¹ ∈ U ⊔ V₀ := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Cex16.exists_mul_of_mem_sup h hx
  have hcomm : r * u * r⁻¹ * u⁻¹ ∈ V₀ :=
    (FourteenTwo.mem_cTilde_iff_comm.mp (hRC hr)).2.2 u (h.le hu)
  have hru : r * u * r⁻¹ ∈ U ⊔ V₀ := by
    have hsplit : r * u * r⁻¹ = (r * u * r⁻¹ * u⁻¹) * u := by group
    rw [hsplit]
    exact (U ⊔ V₀).mul_mem (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left hu)
  have hrw : r * w * r⁻¹ ∈ V₀ :=
    (Subgroup.mem_normalizer_iff.mp
      (FourteenTwo.mem_cTilde_iff_comm.mp (hRC hr)).2.1 w).1 hw
  have hstep : r * (u * w) * r⁻¹ = (r * u * r⁻¹) * (r * w * r⁻¹) := by group
  rw [hstep]
  exact (U ⊔ V₀).mul_mem hru (Subgroup.mem_sup_right hrw)

theorem le_normalizer_tSub16 (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (hRC : R ≤ F11.CTilde M V₀ V) (hSR : S ≤ R) :
    R ≤ normalizer (tSub16 V₀ S : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : IsSylowIn 2 S (centralizer (U : Set G)) := h.isSylowIn_centralizer h1 hS
  have hRUC : R ⊓ centralizer (U : Set G) ≤ S :=
    w16q_le_of_isSylowIn_of_le hSyl (le_inf hSR h.S_le_centralizer) inf_le_right
      (hR2.to_le inf_le_left)
  have hSRUC : S = R ⊓ centralizer (U : Set G) :=
    le_antisymm (le_inf hSR h.S_le_centralizer) hRUC
  have hRNW : R ≤ normalizer (U ⊔ V₀ : Subgroup G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact w16q_conj_mem_sup_UV₀ h hRC hr hx
    · intro hx
      have h := w16q_conj_mem_sup_UV₀ h hRC (R.inv_mem hr) hx
      rwa [show r⁻¹ * (r * x * r⁻¹) * (r⁻¹)⁻¹ = x by group] at h
  have hCW : centralizer ((U ⊔ V₀ : Subgroup G) : Set G) =
      centralizer (U : Set G) ⊓ centralizer (V₀ : Set G) := by
    refine le_antisymm (le_inf
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))) ?_
    intro g hg
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hg ⊢
    intro z hz
    obtain ⟨u, hu, w, hw, rfl⟩ :=
      CFSG.LocalAnalysis.WeakClosure81.exists_mul_of_mem_sup h.le h.hyp.h6.le
        (fun x hx y hy => B2F.isElemAbelian_comm h.hyp.h6.elemAbelian hx hy) hz
    calc (u * w) * g = u * (w * g) := by group
      _ = u * (g * w) := by rw [hg.2 w hw]
      _ = (u * g) * w := by group
      _ = (g * u) * w := by rw [hg.1 u hu]
      _ = g * (u * w) := by group
  have hT_eq : tSub16 V₀ S = R ⊓ centralizer ((U ⊔ V₀ : Subgroup G) : Set G) := by
    show S ⊓ centralizer (V₀ : Set G) =
      R ⊓ centralizer ((U ⊔ V₀ : Subgroup G) : Set G)
    rw [hCW, hSRUC, inf_assoc]
  have hconjCW : ∀ r ∈ R, ∀ x ∈ centralizer ((U ⊔ V₀ : Subgroup G) : Set G),
      r * x * r⁻¹ ∈ centralizer ((U ⊔ V₀ : Subgroup G) : Set G) := by
    intro r hr x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro w hw
    have hrw : r⁻¹ * w * r ∈ U ⊔ V₀ :=
      (Subgroup.mem_normalizer_iff''.mp (hRNW hr) w).1 hw
    have hxw : (r⁻¹ * w * r) * x = x * (r⁻¹ * w * r) := hx (r⁻¹ * w * r) hrw
    calc w * (r * x * r⁻¹) = r * ((r⁻¹ * w * r) * x) * r⁻¹ := by group
      _ = r * (x * (r⁻¹ * w * r)) * r⁻¹ := by rw [hxw]
      _ = (r * x * r⁻¹) * w := by group
  rw [hT_eq]
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxR, hxC⟩
    exact ⟨R.mul_mem (R.mul_mem hr hxR) (R.inv_mem hr), hconjCW r hr x hxC⟩
  · rintro ⟨hxR, hxC⟩
    refine ⟨?_, ?_⟩
    · have h := R.mul_mem (R.inv_mem hr) (R.mul_mem hxR hr)
      rwa [show r⁻¹ * (r * x * r⁻¹ * r) = x by group] at h
    · have h := hconjCW r⁻¹ (R.inv_mem hr) (r * x * r⁻¹) hxC
      rwa [show r⁻¹ * (r * x * r⁻¹) * (r⁻¹)⁻¹ = x by group] at h

theorem isSylowIn_tSub16_inf (h : Cex16 M V₀ V U S) :
    IsSylowIn 2 (tSub16 V₀ S ⊓ centralizer (V : Set G)) (M ⊓ centralizer (V : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := M ⊓ centralizer (V : Set G) with hNdef
  have hNH : N ≤ M ⊓ centralizer (U : Set G) := by
    rw [hNdef]
    exact le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le h.le))
  have hnorm : M ⊓ centralizer (U : Set G) ≤ normalizer (N : Set G) := by
    rw [hNdef]
    have hMCV : M ≤ normalizer (M ⊓ centralizer (V : Set G) : Set G) :=
      (le_inf (le_normalizer (H := M))
        (h.hyp.h6.normalizer_eq ▸ w16q_normalizer_le_normalizer_centralizer V)).trans
        (inf_normalizer_le_normalizer_inf (H := M) (K := centralizer (V : Set G)))
    exact inf_le_left.trans hMCV
  have hNnorm : (N.subgroupOf (M ⊓ centralizer (U : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 hnorm
  have hD : tSub16 V₀ S ⊓ centralizer (V : Set G) = S ⊓ N := by
    have hCVU : centralizer (V : Set G) ≤ centralizer (V₀ : Set G) :=
      Subgroup.centralizer_le h.hyp.h6.le
    show (S ⊓ centralizer (V₀ : Set G)) ⊓ centralizer (V : Set G) = S ⊓ N
    rw [hNdef]
    show (S ⊓ centralizer (V₀ : Set G)) ⊓ centralizer (V : Set G) =
      S ⊓ (M ⊓ centralizer (V : Set G))
    rw [inf_assoc, inf_eq_right.2 hCVU, ← inf_assoc, inf_eq_left.2 h.S_le_M]
  rw [hD]
  exact h.sylow.inf_normal hNH hNnorm

end Cex16

end CFSG.LocalAnalysis.WeakClosure81

end
