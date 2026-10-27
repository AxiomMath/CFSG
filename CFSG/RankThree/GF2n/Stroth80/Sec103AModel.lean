module

public import CFSG.RankThree.GF2n.Stroth80.Sec34CaseB
public import CFSG.RankThree.GF2n.Stroth80.Sec56Frame
public import CFSG.RankThree.GF2n.Stroth80.Sec103Root

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem smul_mem_img_inf_QB_of_globalModel {K : Type} [Field K] [Finite K] [CharP K 2]
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) {s : K} {e : M₀.E}
    (he : e ∈ M₀.img (Q ⊓ QB B)) : s • e ∈ M₀.img (Q ⊓ QB B) := by
  obtain ⟨W, hW, -, -, -⟩ := hc.lagr H.width H.n_gt H.noA2 hD
  exact (hW (s • e)).mpr (W.smul_mem s ((hW e).mp he))

private theorem comm_eq_one_of_mem_inf_QB_inf_QB (hc : Ctx M Q Z B) {W : Subgroup G}
    (hW : ∃ w : G, W = conjSubgroup w Z) (hWB : W ≠ B) {l a : G}
    (hl : l ∈ QB B ⊓ QB W ⊓ M) (ha : a ∈ Q ⊓ QB W ⊓ QB B) : ⁅l, a⁆ = 1 := by
  obtain ⟨w, rfl⟩ := hW
  have hWhyp : StrothHyp (Subgroup.normalizer (conjSubgroup w Z))
      (QB (conjSubgroup w Z)) (conjSubgroup w Z) := by
    rw [Smith81.QB_conj_eq hc.hyp w, Smith81.normalizer_conj_eq hc.hyp w]
    exact hc.hyp.conj w
  have hWmem : ⁅l, a⁆ ∈ conjSubgroup w Z := Smith81.comm_mem_Z hWhyp hl.1.2 ha.1.2
  have hBmem : ⁅l, a⁆ ∈ B := hc.QB_comm_mem hl.1.1 ha.2
  by_contra hne
  obtain ⟨g, hg⟩ := hc.conj
  rw [hg] at hBmem
  exact hWB ((conjSubgroup_eq_of_mem_ne_one hc.hyp hne hWmem hBmem).trans hg.symm)

private theorem comm_mem_Z_of_smul_pi {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) {W : Subgroup G} (hW : ∃ w : G, W = conjSubgroup w Z)
    (hWB : W ≠ B) {s : K} {l a d : G} (hl : l ∈ QB B ⊓ QB W ⊓ M)
    (ha : a ∈ Q ⊓ QB W ⊓ QB B) (hdQ : d ∈ Q) (hde : M₀.π d = s • M₀.π a) :
    ⁅l, d⁆ ∈ Z := by
  have hla : ⁅l, a⁆ = 1 := comm_eq_one_of_mem_inf_QB_inf_QB hc hW hWB hl ha
  have hlM : l ∈ M := hl.2
  have hlLB : l ∈ LB M Q B := Subgroup.mem_sup_right ⟨hl.1.1, hlM⟩
  obtain ⟨T, hTπ, -, -⟩ := hD.linear_of_centralizes hlM (hc.LB_centralizes_Z hlLB)
  have hfix : l * a * l⁻¹ = a := by
    rw [commutatorElement_eq_one_iff_mul_comm.mp hla]
    group
  have hldQ : l * d * l⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) d).mp hdQ
  refine (M₀.comm_mem_iff hdQ hldQ).mpr ?_
  rw [hTπ d hdQ, hde, map_smul, ← hTπ a ha.1.1, hfix]

private theorem card_le_card_inf_QB (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {W : Subgroup G} (hW : ∃ w : G, W = conjSubgroup w Z) (hWB : W ≠ B) (hBW : B ≤ QB W) :
    Nat.card Z ^ n * Nat.card ↥((QB B ⊓ QB W ⊓ M) ⊓ Q) ≤
      Nat.card ↥(Q ⊓ QB W ⊓ QB B) * Nat.card ↥(QB B ⊓ QB W ⊓ M) := by
  obtain ⟨w, rfl⟩ := hW
  rw [show (QB B ⊓ QB (conjSubgroup w Z) ⊓ M) ⊓ Q =
      Q ⊓ QB (conjSubgroup w Z) ⊓ QB B from hc.inf_Lambda_Q,
    Nat.mul_comm (Nat.card Z ^ n)]
  exact Nat.mul_le_mul_left _ (hc.pow_le_card_Lambda h34 H.width H.n_gt H.noA2 H.gen
    (H.rootTrans h34 hspread) (Y := conjSubgroup w Z) (h := w) rfl hWB hBW)

private theorem mem_sup_of_comm_mem_inf_QB (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {W : Subgroup G} (hW : ∃ w : G, W = conjSubgroup w Z) (hWB : W ≠ B)
    (hBW : B ≤ QB W) (hZW : Z ⊓ QB W = ⊥) {d : G} (hdS : d ∈ Q ⊓ QB B)
    (hld : ∀ l ∈ QB B ⊓ QB W ⊓ M, ⁅l, d⁆ ∈ Z) :
    d ∈ (Q ⊓ QB W ⊓ QB B) ⊔ Z := by
  obtain ⟨w, rfl⟩ := hW
  have hΛle : (QB B ⊓ QB (conjSubgroup w Z) ⊓ M) ≤ QB B ⊓ M := fun x hx =>
    ⟨hx.1.1, hx.2⟩
  have hAle : (Q ⊓ QB (conjSubgroup w Z) ⊓ QB B) ≤ Q ⊓ QB B := fun x hx =>
    ⟨hx.1.1, hx.2⟩
  have hAZ : (Q ⊓ QB (conjSubgroup w Z) ⊓ QB B) ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h2 : x ∈ Z ⊓ QB (conjSubgroup w Z) := ⟨hx.2, hx.1.1.2⟩
    rwa [hZW, Subgroup.mem_bot] at h2
  have hcomm : ∀ l ∈ QB B ⊓ QB (conjSubgroup w Z) ⊓ M,
      ∀ a ∈ Q ⊓ QB (conjSubgroup w Z) ⊓ QB B, ⁅l, a⁆ = 1 := by
    intro l hl a ha
    exact comm_eq_one_of_mem_inf_QB_inf_QB hc ⟨w, rfl⟩ hWB hl ha
  obtain ⟨t, htLB, htQ, -⟩ := H.ex
  refine hc.pairing_count h34 (H.toSec5 htLB htQ) hΛle hAle hAZ hcomm
    (card_le_card_inf_QB h34 hspread H ⟨w, rfl⟩ hWB hBW) d hdS ?_
  intro l hl
  exact hld l hl

theorem Sec10Hyp.smul_mem_img_inf_QB_inf_QB (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) {W : Subgroup G} (hW : ∃ w : G, W = conjSubgroup w Z)
    (hWB : W ≠ B) (hBW : B ≤ QB W) (hZW : Z ⊓ QB W = ⊥) (s : K) {e : M₀.E}
    (he : e ∈ M₀.img (Q ⊓ QB W ⊓ QB B)) : s • e ∈ M₀.img (Q ⊓ QB W ⊓ QB B) := by
  obtain ⟨a, ha, haQ, rfl⟩ := M₀.mem_img.mp he
  obtain ⟨w, rfl⟩ := hW
  have hpi : s • M₀.π a ∈ M₀.img (Q ⊓ QB B) :=
    smul_mem_img_inf_QB_of_globalModel H hD (M₀.pi_mem_img ⟨ha.1.1, ha.2⟩ ha.1.1)
  obtain ⟨d, hdS, hdQ, hde⟩ := M₀.mem_img.mp hpi
  have hdAZ : d ∈ (Q ⊓ QB (conjSubgroup w Z) ⊓ QB B) ⊔ Z :=
    mem_sup_of_comm_mem_inf_QB h34 hspread H ⟨w, rfl⟩ hWB hBW hZW hdS
      (fun l hl => comm_mem_Z_of_smul_pi hc hD ⟨w, rfl⟩ hWB hl ha hdQ hde)
  have hAnorm : (Q ⊓ QB (conjSubgroup w Z) ⊓ QB B) ≤
      Subgroup.normalizer (Z : Set G) := fun x hx =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 hx.1.1)
  obtain ⟨a', ha', z, hz, hdz⟩ := exists_mul_of_mem_sup_of_le_normalizer hAnorm hdAZ
  have ha'Q : a' ∈ Q := ha'.1.1
  have hpi' : M₀.π d = M₀.π a' := by
    rw [← hdz, M₀.π_mul a' ha'Q z (hc.hyp.Z_normal.1 hz),
      (M₀.π_ker z (hc.hyp.Z_normal.1 hz)).mpr hz, add_zero]
  have hd_eq : s • M₀.π a = M₀.π a' := by rw [← hde, hpi']
  exact hd_eq ▸ M₀.pi_mem_img ha' ha'Q


end CFSG.RankThree.GF2n.Stroth80
