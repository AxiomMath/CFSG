module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Spure
public import CFSG.RankThree.GF2n.Stroth80.Sec39
public import CFSG.RankThree.GF2n.Stroth80.Sec57D

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.LB_hom_inj_of_card (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hD : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1)) {l : G} (hl : l ∈ QB B ⊓ M)
    (hlD : ∀ d ∈ Q ⊓ QB B, ⁅l, d⁆ ∈ Z) : l ∈ Q := by
  obtain ⟨g, hg⟩ := hc.conj
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  obtain ⟨K, _, _, _, γ, M₀, hGM⟩ := stroth_globalModelData hc.hyp
  have hK2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have hKV : Nat.card K = Nat.card (conjSubgroup g Z) := by
    rw [card_conjSubgroup, hGM.card]
  have hw' : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hw
  have hQF : Nat.card (conjSubgroup g Q) = Nat.card (conjSubgroup g Z) ^ (2 * n + 1) := by
    rw [card_conjSubgroup, card_conjSubgroup, hw']
  have R' := Tim79.GammaReg.conj hGM.reg g
  have hE := Stroth57D.finrank_of_card (M₀.conj g) R' hKV hQF
  have hDQF : Q ⊓ QB B ≤ conjSubgroup g Q := fun x hx => by
    rw [← hQB]
    exact (Subgroup.mem_inf.mp hx).2
  have hVD : conjSubgroup g Z ≤ Q ⊓ QB B := by
    rw [← hg]
    exact le_inf hc.le hc.B_le_QB
  have hDc : ∀ x ∈ Q ⊓ QB B, ∀ y ∈ Q ⊓ QB B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hc).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDcard : Nat.card ↥(Q ⊓ QB B) = Nat.card K ^ (n + 1) := by
    rw [hD, hGM.card]
  have hl' : l ∈ conjSubgroup g Q := by
    rw [← hQB]
    exact (Subgroup.mem_inf.mp hl).1
  have hcomm : ∀ d ∈ Q ⊓ QB B, l * d = d * l := by
    intro d hd
    have h2 : ⁅l, d⁆ ∈ B := by
      rw [hg]
      exact (M₀.conj g).comm_mem l hl' d (hDQF hd)
    have h3 : ⁅l, d⁆ ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨hlD d hd, h2⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  exact (Subgroup.mem_inf.mp (Stroth57D.mem_of_comm (M₀.conj g) R' hK2 hKV hE hDQF hVD hDc
    hDcard hl' hcomm)).1

variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.LB_act_fix_line (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) {r : G} (hr : r ∈ LB M Q B)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ x ∈ Q, M₀.π (r * x * r⁻¹) = T (M₀.π x)) :
    T b = b ∧ ∀ e ∈ M₀.img (Q ⊓ QB B), ∃ c : K, T e - e = c • b := by
  have hrM : r ∈ M := hc.LB_le_M hr
  have hTb : T b = b := by
    obtain ⟨u, huB, huQ, hu⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul K b).symm⟩
    rw [← hu, ← hT u huQ]
    exact (M₀.comm_mem_iff huQ ((hc.conj_mem_Q_of_mem_M hrM).1 u huQ)).mp
      (hc.comm_B_mem_Z hr huB)
  have hBZ : ∀ x ∈ (B ⊔ Z : Subgroup G), x ∈ Q ∧ M₀.π x ∈ M₀.img B := by
    intro x hx
    have hle : (B ⊔ Z : Subgroup G) ≤ M₀.lift (M₀.img B) := by
      refine sup_le (fun u hu => ⟨hc.le hu, M₀.pi_mem_img hu (hc.le hu)⟩) (fun z hz => ?_)
      refine ⟨h.reg.V_le hz, ?_⟩
      rw [(M₀.π_ker z (h.reg.V_le hz)).mpr hz]
      exact AddSubgroup.zero_mem _
    exact ⟨(hle hx).1, (hle hx).2⟩
  have hcomm_BZ : ∀ d ∈ Q ⊓ QB B, ⁅r, d⁆ ∈ (B ⊔ Z : Subgroup G) := by
    intro d hd
    obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB hr
    have hsZ : ∀ z ∈ Z, s * z * s⁻¹ ∈ Z := fun z hz =>
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hs.2) z).mp hz
    have hyd : ⁅y, d⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hy (Subgroup.mem_inf.mp hd).1
    have e : ⁅s * y, d⁆ = (s * ⁅y, d⁆ * s⁻¹) * ⁅s, d⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (B ⊔ Z : Subgroup G).mul_mem (Subgroup.mem_sup_right (hsZ _ hyd))
      (Subgroup.mem_sup_left (hc.comm_QB_le_B hs.1 (Subgroup.mem_inf.mp hd).2))
  have hii : ∀ e ∈ M₀.img (Q ⊓ QB B), ∃ c : K, T e - e = c • b := by
    rintro _ ⟨d, hd, hdQ, rfl⟩
    obtain ⟨c, hcs⟩ := (hB _).mp (hBZ _ (hcomm_BZ d hd)).2
    refine ⟨c, ?_⟩
    have hkQ : ⁅r, d⁆ ∈ Q := (hBZ _ (hcomm_BZ d hd)).1
    have hkd : ⁅r, d⁆ * d = r * d * r⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [← hT d hdQ, ← hkd, M₀.π_mul _ hkQ _ hdQ, add_sub_cancel_right, hcs]
  exact ⟨hTb, hii⟩

end CFSG.RankThree.GF2n.Stroth80
