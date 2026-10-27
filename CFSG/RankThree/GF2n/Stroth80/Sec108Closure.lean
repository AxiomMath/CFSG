module

public import CFSG.RankThree.GF2n.Stroth80.Sec108ConjLB
public import CFSG.RankThree.GF2n.Stroth80.Sec108Fix
import CFSG.RankThree.GF2n.Stroth80.HeringSec65NBar
import CFSG.RankThree.GF2n.Stroth80.Sec108Norm
import CFSG.ClassicalGroups.SpecialLinear.Transitive
import CFSG.RankThree.GF2n.Stroth80.Sec7StepsBasic
import CFSG.RankThree.GF2n.Stroth80.Sec78ConjFrame
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.RankThree.GF2n.Smith81.EStmt
public import CFSG.RankThree.GF2n.Smith81.LinRestCore
public import CFSG.RankThree.GF2n.Smith81.OrthE2Layer
public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime
public import CFSG.RankThree.GF2n.Smith81.Sec220Defs
public import CFSG.RankThree.GF2n.Smith81.Sec220Local
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC
public import CFSG.RankThree.GF2n.Stroth80.Sec10Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec1110ModuleDual
public import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec12Aniso
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVICoord
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stab
public import CFSG.RankThree.GF2n.Stroth80.Sec310Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClMain
public import CFSG.RankThree.GF2n.Stroth80.Sec311Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsSylow
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69
public import CFSG.RankThree.GF2n.Stroth80.SpHomTrivial

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G} [(Q.subgroupOf M).Normal]

private theorem Sec108Data.bar_CN_le_normalizer_bar_LB (D : Sec108Data hc t Y) :
    bar M Q (hc.CN t) ≤
      Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  have h35 := (stroth_3_5 D.h34 hc D.hyp.width D.hyp.n_gt D.hyp.noA2 D.hyp.gen).2.1
  intro g hg
  obtain ⟨n, hn, hnM, rfl⟩ := (HS6.mem_bar (M := M) (Q := Q) g).mp hg
  have hnN : n ∈ Subgroup.normalizer (LB M Q B : Set G) := by
    have h := hc.CN_normalizes_conj_LB h35 D.good.1.mem_LB
      (Rt M (LB M Q B) t).one_mem hn
    rwa [conjSubgroup_one] at h
  exact HS6.piM_mem_normalizer hc.hyp.Q_normal.1 hnM (conjSubgroup_eq_self_iff.mpr hnN)

private theorem Sec108Data.isPGroup_bar_CN_sup_bar_LB (D : Sec108Data hc t Y) :
    IsPGroup 2 ↥(bar M Q (hc.CN t) ⊔ bar M Q (LB M Q B)) :=
  IsPGroup.to_sup_of_normal_right' D.isElemAbelian_bar_CN.isPGroup
    hc.isElemAbelian_bar_LB.isPGroup D.bar_CN_le_normalizer_bar_LB

private theorem Sec108Data.conj_bar_LB_eq_of_le_normalizer (D : Sec108Data hc t Y)
    {g : Mbar M Q}
    (h : conjSubgroup g (bar M Q (LB M Q B)) ≤
      Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q))) :
    conjSubgroup g (bar M Q (LB M Q B)) = bar M Q (LB M Q B) := by
  obtain ⟨m, hmM, hpm⟩ := HS6.exists_piM (M := M) (Q := Q) g
  rw [← hpm] at h ⊢
  rw [HS6.conj_bar hc.hyp.Q_normal.1 hmM] at h ⊢
  have hsub : conjSubgroup m (LB M Q B) ≤ Subgroup.normalizer (LB M Q B : Set G) := by
    intro x hx
    have hxM : x ∈ M := by
      have hmem := (mem_conjSubgroup (g := m) (T := LB M Q B) (x := x)).mp hx
      rw [show x = m * (m⁻¹ * x * m) * m⁻¹ by group]
      exact M.mul_mem (M.mul_mem hmM (hc.LB_le_M hmem)) (M.inv_mem hmM)
    have hxnorm : HS6.piM M Q x ∈
        Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) :=
      h (HS6.piM_mem_bar hx hxM)
    have hQS : Q ≤ Subgroup.normalizer (LB M Q B : Set G) ⊓ M :=
      le_inf (le_sup_left.trans Subgroup.le_normalizer) hc.hyp.Q_normal.1
    have hxN : x ∈ Subgroup.normalizer (LB M Q B : Set G) ⊓ M := by
      refine (HS6.piM_mem_bar_iff (S := Subgroup.normalizer (LB M Q B : Set G) ⊓ M)
        hQS hxM).mp ?_
      rwa [HS6.bar_normalizer (N := LB M Q B) hc.hyp.Q_normal.1
        (le_sup_left : Q ≤ LB M Q B) hc.LB_le_M]
    exact hxN.1
  rw [(stroth_3_5 D.h34 hc D.hyp.width D.hyp.n_gt D.hyp.noA2 D.hyp.gen).1 m hmM hsub]

private theorem Sec108Data.exists_sylow_of_le_normalizer (D : Sec108Data hc t Y) :
    ∃ S : Sylow 2 (Mbar M Q),
      (bar M Q (hc.CN t) ⊔ bar M Q (LB M Q B)) ≤ (S : Subgroup (Mbar M Q)) ∧
      (S : Subgroup (Mbar M Q)) ≤
        Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  set N : Subgroup (Mbar M Q) :=
    Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) with hN
  set S0 : Subgroup (Mbar M Q) := bar M Q (hc.CN t) ⊔ bar M Q (LB M Q B) with hS0
  have hS0N : S0 ≤ N := sup_le D.bar_CN_le_normalizer_bar_LB Subgroup.le_normalizer
  have hS0p : IsPGroup 2 ↥S0 := D.isPGroup_bar_CN_sup_bar_LB
  obtain ⟨T, ⟨hTN, hTp, hS0T⟩, hTmax⟩ : ∃ T : Subgroup (Mbar M Q),
      (T ≤ N ∧ IsPGroup 2 T ∧ S0 ≤ T) ∧
        ∀ S : Subgroup (Mbar M Q), S ≤ N → IsPGroup 2 S → S0 ≤ S → T ≤ S → S = T := by
    obtain ⟨T, hT, hmin⟩ := wellFounded_gt.has_min
      {S : Subgroup (Mbar M Q) | S ≤ N ∧ IsPGroup 2 S ∧ S0 ≤ S} ⟨S0, hS0N, hS0p, le_rfl⟩
    exact ⟨T, hT, fun S hSN hSp hS0S hTS => by
      by_contra hne
      exact hmin S ⟨hSN, hSp, hS0S⟩ (lt_of_le_of_ne hTS (Ne.symm hne))⟩
  have hN' : Subgroup.normalizer (T : Set (Mbar M Q)) ≤ N := by
    intro g hg
    have hgT : conjSubgroup g T = T := conjSubgroup_eq_self_iff.mpr hg
    have hle : conjSubgroup g (bar M Q (LB M Q B)) ≤ N := by
      calc conjSubgroup g (bar M Q (LB M Q B)) ≤ conjSubgroup g T :=
            Subgroup.map_mono (le_sup_right.trans hS0T)
        _ = T := hgT
        _ ≤ N := hTN
    exact conjSubgroup_eq_self_iff.mp (D.conj_bar_LB_eq_of_le_normalizer hle)
  have hmax : ∀ S : Subgroup (Mbar M Q), S ≤ N → IsPGroup 2 S → T ≤ S → S ≤ T :=
    fun S hSN hSp hTS => (hTmax S hSN hSp (hS0T.trans hTS) hTS).le
  obtain ⟨P, hP⟩ := exists_sylow_two_of_normalizer_le hTp hTN hmax hN'
  exact ⟨P, hP ▸ hS0T, hP ▸ hTN⟩

theorem Sec108Data.exists_sylow_le_normalizer (D : Sec108Data hc t Y) :
    ∃ S : Sylow 2 (Mbar M Q), bar M Q (hc.CN t) ≤ (S : Subgroup (Mbar M Q)) ∧
      bar M Q (LB M Q B) ≤ (S : Subgroup (Mbar M Q)) ∧
      (S : Subgroup (Mbar M Q)) ≤ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  obtain ⟨S, hS0, hSN⟩ := D.exists_sylow_of_le_normalizer
  exact ⟨S, le_sup_left.trans hS0, le_sup_right.trans hS0, hSN⟩


private theorem Sec108Data.conj_B_le_Vt (D : Sec108Data hc t Y) {m y : G} (hm : m ∈ M)
    (hy : y ∈ Y) (hy1 : y ≠ 1) (hx : m⁻¹ * y * m ∈ LB M Q B) :
    conjSubgroup m B ≤ Vt M (LB M Q B) B Z t := by
  have hBx : B ≤ Vt M (LB M Q B) B Z (m⁻¹ * y * m) := by
    have h := sec39_conjB_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z)
      (t := m⁻¹ * y * m) (m := 1) M.one_mem (by simpa [conjSubgroup_one] using hx)
    rwa [conjSubgroup_one] at h
  have h1 : conjSubgroup m (Vt M (LB M Q B) B Z (m⁻¹ * y * m)) =
      Vt M (conjSubgroup m (LB M Q B)) (conjSubgroup m B) Z y := by
    have h := Vt_conjG m M (LB M Q B) B Z (m⁻¹ * y * m)
    rw [show m * (m⁻¹ * y * m) * m⁻¹ = y by group,
      conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hm), hc.conj_Z_eq hm] at h
    exact h.symm
  have h2 : Vt M (conjSubgroup m (LB M Q B)) (conjSubgroup m B) Z y =
      Vt M (LB M Q B) B Z y :=
    sec7ctr_Vt_conj_frame (M := M) (Z := Z) (L := LB M Q B) (B' := B) hm y
  have h3 : Vt M (LB M Q B) B Z y = Vt M (LB M Q B) B Z t :=
    D.good.1.Vt_eq_of_mem_root D.h34 D.hspread D.hyp D.sit hy hy1
  calc conjSubgroup m B ≤ conjSubgroup m (Vt M (LB M Q B) B Z (m⁻¹ * y * m)) :=
        Subgroup.map_mono hBx
    _ = Vt M (conjSubgroup m (LB M Q B)) (conjSubgroup m B) Z y := h1
    _ = Vt M (LB M Q B) B Z y := h2
    _ = Vt M (LB M Q B) B Z t := h3

private theorem Sec108Data.exists_coord_conj_B (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {m y : G} (hm : m ∈ M) (hy : y ∈ Y)
    (hy1 : y ≠ 1) (hx : m⁻¹ * y * m ∈ LB M Q B) :
    ∃ c : Fin 3 → AM.K, c ≠ 0 ∧
      (∑ i, c i • (D.bV AM i : AM.M₀.E)) ∈ AM.Vsp hc t ∧
      (∀ x ∈ conjSubgroup m B, ∃ s : AM.K,
        AM.M₀.π x = s • (∑ i, c i • (D.bV AM i : AM.M₀.E))) ∧
      (∀ s : AM.K, ∃ x ∈ conjSubgroup m B,
        AM.M₀.π x = s • (∑ i, c i • (D.bV AM i : AM.M₀.E))) := by
  obtain ⟨b, hb0, -, hbline, -, -⟩ := Ctx.dictB (hc.conj_of_mem hm) AM.glob
  have hbBm : b ∈ AM.M₀.img (conjSubgroup m B) := (hbline b).mpr ⟨1, (one_smul _ b).symm⟩
  have hbV : b ∈ AM.Vsp hc t :=
    mem_imgSub.mpr (AM.M₀.img_mono (D.conj_B_le_Vt hm hy hy1 hx) hbBm)
  let c : Fin 3 → AM.K := (D.bV AM).repr ⟨b, hbV⟩
  have hsum : ∑ i, c i • (D.bV AM i : AM.M₀.E) = b := by
    have h := (D.bV AM).sum_repr ⟨b, hbV⟩
    have h' : ((∑ i, (D.bV AM).repr ⟨b, hbV⟩ i • D.bV AM i : ↥(AM.Vsp hc t)) :
        AM.M₀.E) = b := by rw [h]
    simpa only [c, Submodule.coe_sum, Submodule.coe_smul, Subtype.coe_mk] using h'
  have hc0 : c ≠ 0 := by
    intro hc
    apply hb0
    rw [← hsum, hc]
    simp
  refine ⟨c, hc0, ?_, ?_, ?_⟩
  · rw [hsum]; exact hbV
  · intro x hx
    have hmem := (mem_conjSubgroup (g := m) (T := B) (x := x)).mp hx
    have hxQ : x ∈ Q := by
      rw [show x = m * (m⁻¹ * x * m) * m⁻¹ by group]
      exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) (m⁻¹ * x * m)).mp
        (hc.le hmem)
    obtain ⟨s, hs⟩ := (hbline (AM.M₀.π x)).mp (AM.M₀.pi_mem_img hx hxQ)
    exact ⟨s, by rw [hs, hsum]⟩
  · intro s
    obtain ⟨x, hx, hxQ, hxπ⟩ := (AM.M₀.mem_img (S := conjSubgroup m B)).mp
      ((hbline (s • b)).mpr ⟨s, rfl⟩)
    exact ⟨x, hx, by rw [hxπ, hsum]⟩



private theorem Sec108Data.phi_bV_eq_of_mulVec (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {c β : Fin 3 → AM.K} {A : GL (Fin 3) AM.K}
    {r : G} (hrH : r ∈ H0 M Z)
    (hr : ∀ j, AM.φ ⟨r, hrH⟩ (D.bV AM j : AM.M₀.E) =
      ∑ i, (A : Matrix (Fin 3) (Fin 3) AM.K) i j • (D.bV AM i : AM.M₀.E))
    (hAc : (A : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ c = β) :
    AM.φ ⟨r, hrH⟩ (∑ i, c i • (D.bV AM i : AM.M₀.E)) =
      ∑ i, β i • (D.bV AM i : AM.M₀.E) := by
  calc AM.φ ⟨r, hrH⟩ (∑ i, c i • (D.bV AM i : AM.M₀.E))
      = ∑ i, c i • AM.φ ⟨r, hrH⟩ (D.bV AM i : AM.M₀.E) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    _ = ∑ i, c i • ∑ j, (A : Matrix (Fin 3) (Fin 3) AM.K) j i •
          (D.bV AM j : AM.M₀.E) := by
        exact Finset.sum_congr rfl fun i _ => by rw [hr i]
    _ = ∑ i, ∑ j, c i • ((A : Matrix (Fin 3) (Fin 3) AM.K) j i •
          (D.bV AM j : AM.M₀.E)) := by
        exact Finset.sum_congr rfl fun i _ => Finset.smul_sum
    _ = ∑ j, ∑ i, c i • ((A : Matrix (Fin 3) (Fin 3) AM.K) j i •
          (D.bV AM j : AM.M₀.E)) := Finset.sum_comm
    _ = ∑ j, (∑ i, (A : Matrix (Fin 3) (Fin 3) AM.K) j i * c i) •
          (D.bV AM j : AM.M₀.E) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [smul_smul]
        rw [← Finset.sum_smul]
        congr 1
        exact Finset.sum_congr rfl fun i _ => mul_comm (c i) _
    _ = ∑ i, β i • (D.bV AM i : AM.M₀.E) := by
        rw [← hAc]
        rfl

private theorem Sec108Data.mem_Q_of_mem_conj_B (D : Sec108Data hc t Y) {m z : G}
    (hm : m ∈ M) (hz : z ∈ conjSubgroup m B) : z ∈ Q := by
  have hmem := (mem_conjSubgroup (g := m) (T := B) (x := z)).mp hz
  rw [show z = m * (m⁻¹ * z * m) * m⁻¹ by group]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) (m⁻¹ * z * m)).mp
    (hc.le hmem)

private theorem Sec108Data.mem_Q_of_mem_conj_conj_B (D : Sec108Data hc t Y) {m r x : G}
    (hm : m ∈ M) (hr : r ∈ M) (hx : x ∈ conjSubgroup r (conjSubgroup m B)) : x ∈ Q := by
  have hz := (mem_conjSubgroup (g := r) (T := conjSubgroup m B) (x := x)).mp hx
  rw [show x = r * (r⁻¹ * x * r) * r⁻¹ by group]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hr) (r⁻¹ * x * r)).mp
    (D.mem_Q_of_mem_conj_B hm hz)

private theorem Sec108Data.phi_conj_B_le_Bsp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {m y : G} (hm : m ∈ M) (hy : y ∈ Y)
    (hy1 : y ≠ 1) (hx : m⁻¹ * y * m ∈ LB M Q B) {c β : Fin 3 → AM.K} {r : G}
    (hrH : r ∈ H0 M Z)
    (hline : ∀ x ∈ conjSubgroup m B, ∃ s : AM.K,
      AM.M₀.π x = s • (∑ i, c i • (D.bV AM i : AM.M₀.E)))
    (hφb : AM.φ ⟨r, hrH⟩ (∑ i, c i • (D.bV AM i : AM.M₀.E)) =
      ∑ i, β i • (D.bV AM i : AM.M₀.E))
    (hβB : (∑ i, β i • (D.bV AM i : AM.M₀.E)) ∈ D.Bsp AM) :
    ∀ z ∈ conjSubgroup m B, AM.M₀.π (r * z * r⁻¹) ∈ AM.M₀.img B := by
  intro z hz
  obtain ⟨s, hs⟩ := hline z hz
  rw [AM.φ_π ⟨r, hrH⟩ z (D.mem_Q_of_mem_conj_B hm hz), hs, map_smul, hφb]
  exact (D.mem_Bsp AM).mp ((D.Bsp AM).smul_mem s hβB)

private theorem Sec108Data.sup_conj_B_le (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {m y : G} (hm : m ∈ M) (hy : y ∈ Y)
    (hy1 : y ≠ 1) (hx : m⁻¹ * y * m ∈ LB M Q B) {r : G}
    (hrR : r ∈ Rt M (LB M Q B) t)
    (hπ : ∀ z ∈ conjSubgroup m B, AM.M₀.π (r * z * r⁻¹) ∈ AM.M₀.img B) :
    conjSubgroup r (conjSubgroup m B) ⊔ Z ≤ B ⊔ Z := by
  refine sup_le ?_ le_sup_right
  intro x hx
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hz : r⁻¹ * x * r ∈ conjSubgroup m B :=
    (mem_conjSubgroup (g := r) (T := conjSubgroup m B) (x := x)).mp hx
  have hxr := hπ _ hz
  rw [show r * (r⁻¹ * x * r) * r⁻¹ = x by group] at hxr
  exact (AM.M₀.mem_img_iff (le_sup_right : Z ≤ B ⊔ Z)
    (D.mem_Q_of_mem_conj_conj_B hm hrM hx)).mp
    (AM.M₀.img_mono (le_sup_left : B ≤ B ⊔ Z) hxr)

private theorem Sec108Data.bV_sum_ne_zero (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K} (hβ : β ≠ 0) :
    (∑ i, β i • (D.bV AM i : AM.M₀.E)) ≠ 0 := by
  intro h0
  apply hβ
  have hsum : (∑ i, β i • D.bV AM i : ↥(AM.Vsp hc t)) = 0 := by
    apply Subtype.ext
    have h0' : (∑ i, β i • (D.bV AM i : AM.M₀.E)) = 0 := h0
    simpa using h0'
  funext i
  exact Fintype.linearIndependent_iff.mp (D.bV AM).linearIndependent β hsum i

private theorem Sec108Data.le_sup_conj_B (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {m y : G} (hm : m ∈ M) (hy : y ∈ Y)
    (hy1 : y ≠ 1) (hx : m⁻¹ * y * m ∈ LB M Q B) {c β : Fin 3 → AM.K} (hc0 : c ≠ 0)
    (hβ : β ≠ 0)
    (hline : ∀ x ∈ conjSubgroup m B, ∃ s : AM.K,
      AM.M₀.π x = s • (∑ i, c i • (D.bV AM i : AM.M₀.E)))
    (hsurj : ∀ s : AM.K, ∃ x ∈ conjSubgroup m B,
      AM.M₀.π x = s • (∑ i, c i • (D.bV AM i : AM.M₀.E)))
    {r : G} (hrR : r ∈ Rt M (LB M Q B) t) (hrH : r ∈ H0 M Z)
    (hφb : AM.φ ⟨r, hrH⟩ (∑ i, c i • (D.bV AM i : AM.M₀.E)) =
      ∑ i, β i • (D.bV AM i : AM.M₀.E))
    (hβB : (∑ i, β i • (D.bV AM i : AM.M₀.E)) ∈ D.Bsp AM) :
    B ⊔ Z ≤ conjSubgroup r (conjSubgroup m B) ⊔ Z := by
  have hβne : (∑ i, β i • (D.bV AM i : AM.M₀.E)) ≠ 0 := D.bV_sum_ne_zero AM hβ
  have hspan : D.Bsp AM = Submodule.span AM.K {(∑ i, β i • (D.bV AM i : AM.M₀.E))} := by
    refine (Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_).symm
    · simpa using hβB
    · rw [finrank_span_singleton hβne, D.finrank_Bsp AM]
  refine sup_le ?_ le_sup_right
  intro x hx
  have hxQ : x ∈ Q := hc.le hx
  have hxImg : AM.M₀.π x ∈ AM.M₀.img B := AM.M₀.pi_mem_img hx hxQ
  have hxspan : AM.M₀.π x ∈
      Submodule.span AM.K {(∑ i, β i • (D.bV AM i : AM.M₀.E))} := by
    rw [← hspan]
    exact (D.mem_Bsp AM).mpr hxImg
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hxspan
  obtain ⟨z, hz, hzπ⟩ := hsurj s
  have hzQ : z ∈ Q := D.mem_Q_of_mem_conj_B hm hz
  have hmemW : r * z * r⁻¹ ∈ conjSubgroup r (conjSubgroup m B) := by
    rw [mem_conjSubgroup]
    rwa [show r⁻¹ * (r * z * r⁻¹) * r = z by group]
  have hπeq : AM.M₀.π (r * z * r⁻¹) = AM.M₀.π x := by
    rw [AM.φ_π ⟨r, hrH⟩ z hzQ, hzπ, map_smul, hφb, hs]
  have hximg : AM.M₀.π x ∈ AM.M₀.img (conjSubgroup r (conjSubgroup m B)) := by
    rw [← hπeq]
    exact AM.M₀.pi_mem_img hmemW (D.mem_Q_of_mem_conj_conj_B hm (hc.Rt_le_M t hrR) hmemW)
  exact (AM.M₀.mem_img_iff
    (le_sup_right : Z ≤ conjSubgroup r (conjSubgroup m B) ⊔ Z) hxQ).mp
    (AM.M₀.img_mono (le_sup_left : conjSubgroup r (conjSubgroup m B) ≤
      conjSubgroup r (conjSubgroup m B) ⊔ Z) hximg)

private theorem Sec108Data.exists_normalizer_BZ (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {m y : G} (hm : m ∈ M) (hy : y ∈ Y)
    (hy1 : y ≠ 1) (hx : m⁻¹ * y * m ∈ LB M Q B) :
    ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup (r * m) B ⊔ Z = B ⊔ Z := by
  obtain ⟨β, hβ, hβB⟩ := D.exists_coord_Bsp AM
  obtain ⟨c, hc0, hcV, hline, hsurj⟩ := D.exists_coord_conj_B AM hm hy hy1 hx
  obtain ⟨A, hA, hAc⟩ :=
    CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq (m := 3) (by norm_num) hc0 hβ
  have hAdet : (A : Matrix (Fin 3) (Fin 3) AM.K).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSL hA
  let ASL : Matrix.SpecialLinearGroup (Fin 3) AM.K := ⟨(A : Matrix (Fin 3) (Fin 3) AM.K), hAdet⟩
  obtain ⟨r, ⟨hrR, hrt⟩, hrH, hr⟩ := D.bV_spec AM ASL
  have hφb : AM.φ ⟨r, hrH⟩ (∑ i, c i • (D.bV AM i : AM.M₀.E)) =
      ∑ i, β i • (D.bV AM i : AM.M₀.E) := D.phi_bV_eq_of_mulVec AM hrH hr hAc
  have hπ := D.phi_conj_B_le_Bsp AM hm hy hy1 hx hrH hline hφb hβB
  refine ⟨r, hrR, ?_⟩
  rw [conjSubgroup_mul]
  exact le_antisymm (D.sup_conj_B_le AM hm hy hy1 hx hrR hπ)
    (D.le_sup_conj_B AM hm hy hy1 hx hc0 hβ hline hsurj hrR hrH hφb hβB)

private theorem Sec108Data.bar_sup_Q_eq (D : Sec108Data hc t Y) :
    bar M Q (Y ⊔ Q) = bar M Q Y := by
    refine le_antisymm ?_ (HS6.bar_mono (le_sup_left : Y ≤ Y ⊔ Q))
    intro z hz
    obtain ⟨x, hx, -, rfl⟩ := (HS6.mem_bar (M := M) (Q := Q) z).mp hz
    obtain ⟨y', hy', w, hw, hyw⟩ := D.exists_root_mul hx
    rw [← hyw, HS6.piM_mul (((smith_1_12 D.sit).1.trans inf_le_left) hy') (hc.hyp.Q_normal.1 hw),
      (HS6.piM_eq_one_iff (hc.hyp.Q_normal.1 hw)).mpr hw, mul_one]
    exact HS6.piM_mem_bar hy' (((smith_1_12 D.sit).1.trans inf_le_left) hy')

private theorem Sec108Data.mem_normalizer_root_of_conj_mem_LB (D : Sec108Data hc t Y)
    (hN : Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ≤
      Subgroup.normalizer (bar M Q Y : Set (Mbar M Q)))
    {m y : G} (hm : m ∈ M) (hy : y ∈ Y) (hy1 : y ≠ 1) (hx : m⁻¹ * y * m ∈ LB M Q B) :
    m ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) := by
  obtain ⟨AM⟩ := Smith81.Smith23E1.ActionModel.nonempty hc.hyp
  obtain ⟨r, hrR, heq⟩ := D.exists_normalizer_BZ AM hm hy hy1 hx
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hrmM : r * m ∈ M := M.mul_mem hrM hm
  have hZ : conjSubgroup (r * m) Z = Z := hc.conj_Z_eq hrmM
  have hsup : conjSubgroup (r * m) (B ⊔ Z) =
      conjSubgroup (r * m) B ⊔ conjSubgroup (r * m) Z := by
    change ((B ⊔ Z).map (MulAut.conj (r * m)).toMonoidHom) =
      (B.map (MulAut.conj (r * m)).toMonoidHom) ⊔ (Z.map (MulAut.conj (r * m)).toMonoidHom)
    rw [Subgroup.map_sup]
  have hrmN : r * m ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
    rw [← conjSubgroup_eq_self_iff, hsup, hZ, heq]
  have hrmLB : r * m ∈ Subgroup.normalizer (LB M Q B : Set G) :=
    (stroth_11_1a hc D.hyp.width D.hyp.n_gt hrmM).mp hrmN
  have hpiN : HS6.piM M Q (r * m) ∈
      Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) :=
    HS6.piM_mem_normalizer hc.hyp.Q_normal.1 hrmM (conjSubgroup_eq_self_iff.mpr hrmLB)
  have hpiY : HS6.piM M Q (r * m) ∈
      Subgroup.normalizer (bar M Q Y : Set (Mbar M Q)) := hN hpiN
  have hbarEQ : bar M Q (Y ⊔ Q) = bar M Q Y := D.bar_sup_Q_eq
  have hQS : Q ≤ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) ⊓ M :=
    le_inf (le_sup_right.trans Subgroup.le_normalizer) hc.hyp.Q_normal.1
  have hrmY : r * m ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) := by
    have hbarN : HS6.piM M Q (r * m) ∈
        Subgroup.normalizer (bar M Q (Y ⊔ Q) : Set (Mbar M Q)) := by
      rwa [hbarEQ]
    have hmem := (HS6.piM_mem_bar_iff
      (S := Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) ⊓ M) hQS hrmM).mp ?_
    · exact hmem.1
    · rwa [HS6.bar_normalizer (N := Y ⊔ Q) hc.hyp.Q_normal.1
        (le_sup_right : Q ≤ Y ⊔ Q)
        (sup_le ((smith_1_12 D.sit).1.trans inf_le_left) hc.hyp.Q_normal.1)]
  have hrY : r ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) :=
    D.Rt_le_normalizer_root hrR
  have hmY : m ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hrY) hrmY
    rwa [show r⁻¹ * (r * m) = m by group] at h
  exact hmY

theorem Sec108Data.stronglyClosed_bar_LB (D : Sec108Data hc t Y)
    (hN : Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ≤
      Subgroup.normalizer (bar M Q Y : Set (Mbar M Q))) :
    ∀ a ∈ bar M Q Y, ∀ g : Mbar M Q, g⁻¹ * a * g ∈ bar M Q (LB M Q B) →
      g⁻¹ * a * g ∈ bar M Q Y := by
  intro a ha g hg
  obtain ⟨y, hy, hyM, hya⟩ := (HS6.mem_bar (M := M) (Q := Q) a).mp ha
  obtain ⟨m, hmM, hgm⟩ := HS6.exists_piM (M := M) (Q := Q) g
  have hxM : m⁻¹ * y * m ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hmM) hyM) hmM
  have hmemg : g⁻¹ * a * g = HS6.piM M Q (m⁻¹ * y * m) := by
    rw [← hya, ← hgm, ← HS6.piM_inv hmM,
      ← HS6.piM_mul (M.inv_mem hmM) hyM,
      ← HS6.piM_mul (M.mul_mem (M.inv_mem hmM) hyM) hmM]
  rw [hmemg] at hg ⊢
  by_cases hy1 : y = 1
  · rw [hy1, mul_one, inv_mul_cancel, HS6.piM_one]
    exact Subgroup.one_mem _
  · have hxLB : m⁻¹ * y * m ∈ LB M Q B :=
      (HS6.piM_mem_bar_iff (S := LB M Q B) (le_sup_left : Q ≤ LB M Q B) hxM).mp
        (hmemg ▸ hg)
    have hmN := D.mem_normalizer_root_of_conj_mem_LB hN hmM hy hy1 hxLB
    have hxYQ : m⁻¹ * y * m ∈ Y ⊔ Q := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmN) y).mp
        (Subgroup.mem_sup_left hy)
    obtain ⟨y', hy', w, hw, hyw⟩ := D.exists_root_mul hxYQ
    rw [← hyw, HS6.piM_mul (((smith_1_12 D.sit).1.trans inf_le_left) hy') (hc.hyp.Q_normal.1 hw),
      (HS6.piM_eq_one_iff (hc.hyp.Q_normal.1 hw)).mpr hw, mul_one]
    exact HS6.piM_mem_bar hy' (((smith_1_12 D.sit).1.trans inf_le_left) hy')

private theorem Sec108Data.bar_root_centralizes_Rt (D : Sec108Data hc t Y) :
    bar M Q Y ≤
      Subgroup.centralizer (bar M Q (Rt M (LB M Q B) t) : Set (Mbar M Q)) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨y0, hy0, hy0M, rfl⟩ := (HS6.mem_bar (M := M) (Q := Q) y).mp hy
  obtain ⟨x0, hx0, hx0M, rfl⟩ := (HS6.mem_bar (M := M) (Q := Q) x).mp hx
  exact HS6.piM_comm_of_comm_mem hx0M hy0M (D.comm_Rt_root_mem x0 hx0 y0 hy0)

theorem Sec108Data.stronglyClosed_bar_Rt (D : Sec108Data hc t Y)
    (hN : Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ≤
      Subgroup.normalizer (bar M Q Y : Set (Mbar M Q))) :
    ∀ a ∈ bar M Q Y, ∀ g : Mbar M Q, g⁻¹ * a * g ∈ bar M Q (Rt M (LB M Q B) t) →
      g⁻¹ * a * g ∈ bar M Q Y := by
  intro a ha g hg
  have ha2 : a * a = 1 := by
    have h := hc.isElemAbelian_bar_LB.2 a (HS6.bar_mono (D.root_le_LB) ha)
    rwa [pow_two] at h
  have hx2 : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [ha2]; group
  obtain ⟨i, hiR, hiM, hii⟩ := (HS6.mem_bar (M := M) (Q := Q) (g⁻¹ * a * g)).mp hg
  have hi2Q : i ^ 2 ∈ Q := by
    have h1 : HS6.piM M Q (i ^ 2) = 1 := by
      rw [pow_two, HS6.piM_mul hiM hiM, hii]
      exact hx2
    exact (HS6.piM_eq_one_iff (M := M) (Q := Q) (M.pow_mem hiM 2)).mp h1
  obtain ⟨r, hrR, hriLB⟩ := D.exists_conj_mem_LB hiR hi2Q
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hriM : r * i * r⁻¹ ∈ M := M.mul_mem (M.mul_mem hrM hiM) (M.inv_mem hrM)
  set h : Mbar M Q := HS6.piM M Q r with hh
  have hhR : h ∈ bar M Q (Rt M (LB M Q B) t) := HS6.piM_mem_bar hrR hrM
  have hpi : h * (g⁻¹ * a * g) * h⁻¹ = HS6.piM M Q (r * i * r⁻¹) := by
    rw [hh, ← hii, HS6.piM_mul (M.mul_mem hrM hiM) (M.inv_mem hrM),
      HS6.piM_inv hrM, HS6.piM_mul hrM hiM]
  have hriBar : h * (g⁻¹ * a * g) * h⁻¹ ∈ bar M Q (LB M Q B) := by
    rw [hpi]
    exact HS6.piM_mem_bar hriLB hriM
  have hu : h * (g⁻¹ * a * g) * h⁻¹ ∈ bar M Q Y := by
    have hres := D.stronglyClosed_bar_LB hN (a := a) ha (g := g * h⁻¹)
      (by rwa [show (g * h⁻¹)⁻¹ * a * (g * h⁻¹) = h * (g⁻¹ * a * g) * h⁻¹ by group])
    rwa [show (g * h⁻¹)⁻¹ * a * (g * h⁻¹) = h * (g⁻¹ * a * g) * h⁻¹ by group] at hres
  have hcomm : h * (h * (g⁻¹ * a * g) * h⁻¹) =
      (h * (g⁻¹ * a * g) * h⁻¹) * h :=
    Subgroup.mem_centralizer_iff.mp (D.bar_root_centralizes_Rt hu) h hhR
  have hxu : g⁻¹ * a * g = h * (g⁻¹ * a * g) * h⁻¹ := by
    have h1 : h * (g⁻¹ * a * g) = h * (h * (g⁻¹ * a * g) * h⁻¹) := by
      rw [hcomm]
      group
    exact mul_left_cancel h1
  rw [hxu]
  exact hu


private theorem Sec108Data.exists_lift_H0_normalizer_root (D : Sec108Data hc t Y)
    {x : Mbar M Q} (hxH : x ∈ bar M Q (H0 M Z))
    (hxN : x ∈ Subgroup.normalizer (bar M Q Y : Set (Mbar M Q))) :
    ∃ d : G, d ∈ H0 M Z ∧
      d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) ∧ HS6.piM M Q d = x := by
  have hxN' : x ∈ Subgroup.normalizer (bar M Q (Y ⊔ Q) : Set (Mbar M Q)) := by
    rwa [D.bar_sup_Q_eq]
  have hbarNorm := HS6.bar_normalizer (N := Y ⊔ Q) hc.hyp.Q_normal.1
    (le_sup_right : Q ≤ Y ⊔ Q)
    (sup_le ((smith_1_12 D.sit).1.trans inf_le_left) hc.hyp.Q_normal.1)
  have hxS : x ∈ bar M Q (Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) ⊓ M) := by
    rwa [hbarNorm]
  obtain ⟨d, hdS, hdM, hdx⟩ := (HS6.mem_bar (M := M) (Q := Q) x).mp hxS
  obtain ⟨d0, hd0H, hd0M, hd0x⟩ := (HS6.mem_bar (M := M) (Q := Q) x).mp hxH
  have hq : d0⁻¹ * d ∈ Q := (HS6.piM_eq_iff hd0M hdM).mp (by rw [hd0x, hdx])
  have hdH : d ∈ H0 M Z := by
    rw [show d = d0 * (d0⁻¹ * d) by group]
    exact (H0 M Z).mul_mem hd0H (hc.Q_le_H0 hq)
  exact ⟨d, hdH, hdS.1, hdx⟩

theorem Sec108Data.exists_sylow_stronglyClosed (D : Sec108Data hc t Y)
    (hN : Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ≤
      Subgroup.normalizer (bar M Q Y : Set (Mbar M Q))) :
    ∃ S : Sylow 2 (Mbar M Q), bar M Q Y ≤ (S : Subgroup (Mbar M Q)) ∧
      ∀ a ∈ bar M Q Y, ∀ g : Mbar M Q, g⁻¹ * a * g ∈ (S : Subgroup (Mbar M Q)) →
        g⁻¹ * a * g ∈ bar M Q Y := by
  obtain ⟨S, hCN, hLB, hSN⟩ := D.exists_sylow_le_normalizer
  refine ⟨S, (HS6.bar_mono D.root_le_LB).trans hLB, ?_⟩
  intro a ha g hxS
  set x : Mbar M Q := g⁻¹ * a * g with hx
  have hxH : x ∈ bar M Q (H0 M Z) := by
    have haH : a ∈ bar M Q (H0 M Z) :=
      HS6.bar_mono ((smith_1_12 D.sit).1 : Y ≤ H0 M Z) ha
    haveI : (bar M Q (H0 M Z)).Normal := hc.normal_bar_H0
    have hconj := Subgroup.Normal.conj_mem inferInstance a haH g⁻¹
    simpa [hx] using hconj
  have hxN : x ∈ Subgroup.normalizer (bar M Q Y : Set (Mbar M Q)) := hN (hSN hxS)
  obtain ⟨d, hdH, hdY, hdx⟩ := D.exists_lift_H0_normalizer_root hxH hxN
  have hdM : d ∈ M := hdH.1
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_pow_pow_eq_one ⟨x, hxS⟩
  have hxk : x ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hpi_pow : HS6.piM M Q (d ^ 2 ^ k) = (HS6.piM M Q d) ^ 2 ^ k := by
    clear hxk hk
    induction 2 ^ k with
    | zero => rw [pow_zero, pow_zero, HS6.piM_one]
    | succ n ih =>
        rw [pow_succ, pow_succ, HS6.piM_mul (M.pow_mem hdM n) hdM, ih]
  have hdQ : d ^ 2 ^ k ∈ Q := by
    refine (HS6.piM_eq_one_iff (M := M) (Q := Q) (M.pow_mem hdM (2 ^ k))).mp ?_
    rw [hpi_pow, hdx, hxk]
  have hdR : d ∈ Rt M (LB M Q B) t := D.twoElt_mem_Rt hdH hdY hdQ
  have hxR : g⁻¹ * a * g ∈ bar M Q (Rt M (LB M Q B) t) := by
    rw [← hx, ← hdx]
    exact HS6.piM_mem_bar hdR (hc.Rt_le_M t hdR)
  have hres := D.stronglyClosed_bar_Rt hN a ha g hxR
  rwa [← hx] at hres

end CFSG.RankThree.GF2n.Stroth80
