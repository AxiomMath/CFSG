module

public import CFSG.RankThree.PartOne.SP4GA.Coords
public import CFSG.RankThree.PartOne.SP4GA.Lift
public import CFSG.RankThree.PartOne.SP4GA.Irred
public import CFSG.RankThree.PartOne.SP4GA.RSide
public import CFSG.RankThree.PartOne.SP4C.InvReduce

public section

namespace CFSG.RankThree.PartOne.SP4GA

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.Blueprint
open CFSG.RankThree.PartOne.K1214
open CFSG.RankThree.PartOne.S12K (LieRigidity3)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {b : G} {K I X P Q : Subgroup G}

theorem no_inverting_element
    (h112 : InSec11Two) (hRig : LieRigidity3) (hKR : KFixedRes) (hU5 : KF1214U5)
    (hZ : KF1214ZRow 7) (hFix : FieldFixedPElements) (ctx : Fus12Ctx G p A c L E)
    (hL : Layer1212 p A c L E b K I) (hC : Choice1212 p E b I X P Q)
    (hF : Field1213 p A c L b K I) (hout : Out1214 p c L E I P Q) (h7 : RowModel p L 7) :
    ¬ ∃ g ∈ torusNormalizer E, g * c * g⁻¹ = c⁻¹ := by
  classical
  rintro ⟨n₀, hn₀, hn₀c⟩
  obtain ⟨hp, hp5⟩ := prime_five_le ctx
  have : Fact p.Prime := ⟨hp⟩
  have hE3 : Nat.card E = p ^ 3 := by
    obtain ⟨K', hKf, hKfin, hζ, ⟨S⟩⟩ := SP4C.exists_r7ctx_core ctx.table_core h7
    have h1 := KFU.D8Ctx.card_F S hp.pos hζ
    rw [ctx.ten.2.1, h1]
    ring
  obtain ⟨e, x, y, hfr⟩ := exists_frame h112 hRig hKR hU5 hZ ctx h7 hL hC hF hout hE3
    (c_not_centralize_R h112 hRig hKR hFix ctx hL hC hF)
  have hPE : P ≤ Subgroup.normalizer (E : Set G) := P_le_normalizer_of_omega hout.omega
  have hnH := not_dvd_torusImage ctx (hU5 G p A c L E ctx)
  have hcE : c ∈ E := c_mem_E ctx
  have S := hfr.setup
  obtain ⟨w, hwL, hwE, hwnot⟩ :=
    exists_not_invariant ctx S.βb_mem S.βb_ne_one S.βK_mem S.βK_not_mem_zpowers
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, hL'⟩ := ctx.hyp.L_mem.2
    rw [← hL']
    exact Subgroup.map_subtype_le _
  have hwc : w * c = c * w := Subgroup.mem_centralizer_singleton_iff.1 (hLc hwL)
  have hwcw : w * c * w⁻¹ = c := by rw [hwc]; group
  obtain ⟨n₁, hn₁P, hn₁E, hn₁mod, hn₁fix⟩ := exists_lift ctx hnH hC hPE hwE
  obtain ⟨β₁, hβ₁, hn₁c⟩ : ∃ β₁ ∈ E ⊓ L, n₁ * c * n₁⁻¹ = c * β₁ := by
    have h1 := hn₁mod c hcE
    rw [hwcw] at h1
    refine ⟨n₁ * c * n₁⁻¹ * c⁻¹, h1, ?_⟩
    have h2 := S.B_central _ h1 c S.c_mem
    calc n₁ * c * n₁⁻¹ = (n₁ * c * n₁⁻¹ * c⁻¹) * c := by group
      _ = c * (n₁ * c * n₁⁻¹ * c⁻¹) := (mul_inv_eq_iff_eq_mul.1 h2).symm
  have hβbw : w * y ^ (p ^ (e - 1)) * w⁻¹ ∈ E ⊓ L := by
    have hb := S.βb_mem
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hwE _).1 (Subgroup.mem_inf.1 hb).1,
      L.mul_mem (L.mul_mem hwL (Subgroup.mem_inf.1 hb).2) (L.inv_mem hwL)⟩
  have hnot : n₁ * y ^ (p ^ (e - 1)) * n₁⁻¹ ∉ Subgroup.zpowers (y ^ (p ^ (e - 1))) := by
    rw [hn₁fix _ S.βb_mem hβbw]
    exact hwnot
  obtain ⟨n₂, hn₂P, hn₂E, hn₂mod, -⟩ := exists_lift ctx hnH hC hPE hn₀
  obtain ⟨β₂, hβ₂, hn₂c⟩ : ∃ β₂ ∈ E ⊓ L, n₂ * c * n₂⁻¹ = c⁻¹ * β₂ := by
    have h1 := hn₂mod c hcE
    rw [hn₀c, inv_inv] at h1
    refine ⟨n₂ * c * n₂⁻¹ * c, h1, ?_⟩
    have h2 := S.B_central _ h1 c⁻¹ (P.inv_mem S.c_mem)
    calc n₂ * c * n₂⁻¹ = (n₂ * c * n₂⁻¹ * c) * c⁻¹ := by group
      _ = c⁻¹ * (n₂ * c * n₂⁻¹ * c) := (mul_inv_eq_iff_eq_mul.1 h2).symm
  obtain ⟨a₁, a₁', b₁, b₁', hx₁, hy₁⟩ := hfr.coords hn₁P
  obtain ⟨a₂, a₂', b₂, b₂', hx₂, hy₂⟩ := hfr.coords hn₂P
  obtain ⟨r, hr, hrp⟩ := hfr.hr
  obtain ⟨r', hr'⟩ := hfr.hr'
  exact S.contradiction_of_lifts hrp hr hr' hβ₁ hn₁c
    (fun u hu => (Subgroup.mem_normalizer_iff.1 hn₁P u).1 hu) hx₁ hy₁ hnot hβ₂ hn₂c
    (fun u hu => (Subgroup.mem_normalizer_iff.1 hn₂P u).1 hu) hx₂ hy₂

theorem kf1215Sp4InvCore_of_inputs_row
    (h112 : InSec11Two) (hRig : LieRigidity3) (hKR : KFixedRes) (hU5 : KF1214U5)
    (hZ : KF1214ZRow 7) (hFix : FieldFixedPElements) : SP4C.KF1215Sp4InvCore := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF hout hsyl h7 g hg hginv _ _
  exact absurd ⟨g, hg, hginv⟩
    (no_inverting_element h112 hRig hKR hU5 hZ hFix ctx hL hC hF hout h7)

end CFSG.RankThree.PartOne.SP4GA
