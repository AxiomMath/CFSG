module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aDataMono
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aLiftX
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aProp1
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6Torus
public import CFSG.RankThree.PartTwo.Sec21.FF81KFacts
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6Transv

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.four_le_localRank_of_torus (h : FF81Hyp b L) (hT : KF_Sp6Torus)
    (hnoL : ∀ g : G, g * b * g⁻¹ ∉ L) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 G := by
  have hTF : KF_Sp6TorusFree := kf_sp6TorusFree
  have hOut : KF_Sp62Out := kf_sp62Out
  have hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 27 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrk, _, _⟩ := hT G L h.model
    exact hrk
  obtain ⟨b₁, b₂, b₃, τ, ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ,
    hb₁, hb₂, hb₃, hE3, hE4, hB₁L, hself, hmonoL, hBC,
    hι₁L, hι₂L, hι₃L, hσ₁₂L, hσ₂₃L, hγL, D, M⟩ :=
    h.exists_Data_Mono hT hTF hOut hnoL
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  let B₁ : Subgroup G := Subgroup.closure ({b₁, b₂, b₃} : Set G)
  have hbB : b ∈ B := Subgroup.subset_closure (by simp)
  have hB₁B : B₁ ≤ B := by
    refine Subgroup.closure_mono ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp
  have hirr : ∀ H : Subgroup G, H ≤ Subgroup.closure ({b₁, b₂, b₃} : Set G) → H ≠ ⊥ →
      (∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), ∀ x ∈ H, g * x * g⁻¹ ∈ H) →
      H = Subgroup.closure ({b₁, b₂, b₃} : Set G) := by
    intro H hHle hHne hHinv
    exact FF81Hyp.B1_irreducible_monomial h hb₁ hb₂ hb₃ hE3 hHle hHne
      M.s₁ M.s₂ M.s₃ M.p₁₂ M.p₂₃ M.cyc
      (fun x hx => hHinv ι₁ (by simp) x hx)
      (fun x hx => hHinv ι₂ (by simp) x hx)
      (fun x hx => hHinv ι₃ (by simp) x hx)
      (fun x hx => hHinv σ₁₂ (by simp) x hx)
      (fun x hx => hHinv σ₂₃ (by simp) x hx)
      (fun x hx => hHinv γ (by simp) x hx)
  have hcenOdd : Odd (Nat.card ↥(CenS B)) := h.odd_cenS hTF hrk hE4 hbB hBC
  have hDB : Cen b ⊓ CenS L ≤ CenS B := fun y hy => by
    have hle : B ≤ Cen y := by
      rw [show B = Subgroup.zpowers b ⊔ B₁ from closure_four_eq b b₁ b₂ b₃]
      refine sup_le (Subgroup.zpowers_le.mpr ?_)
        (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hy.2 z (hB₁L hz)))
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hy.1).symm
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hDodd : Odd (Nat.card ↥(Cen b ⊓ CenS L)) :=
    Odd.of_dvd_nat hcenOdd (Subgroup.card_dvd_of_le hDB)
  have hmono : ∀ n ∈ Nor (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)),
      (n * b * n⁻¹ = b ∨ n * b * n⁻¹ = b⁻¹) →
      ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G) := by
    intro n hn hcase x hx
    have hnb : conjBy n (Subgroup.zpowers b) = Subgroup.zpowers b := by
      change (Subgroup.zpowers b).map (MulAut.conj n).toMonoidHom = Subgroup.zpowers b
      rcases hcase with h' | h'
      · rw [MonoidHom.map_zpowers]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h']
      · rw [MonoidHom.map_zpowers]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h', Subgroup.zpowers_inv]
    exact (h.stab hDodd hB₁L hself hmonoL hE4 hB₁B hn hnb).2 x hx
  have hML : ∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), g ∈ L := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hι₁L, hι₂L, hι₃L, hσ₁₂L, hσ₂₃L, hγL]
  have hself_le : L ⊓ Subgroup.centralizer
      ((Subgroup.closure ({b₁, b₂, b₃} : Set G) : Subgroup G) : Set G) ≤
      Subgroup.closure ({b₁, b₂, b₃} : Set G) := hself.le
  haveI : IsSimpleGroup G := h.simple
  have hperf : commutator G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hbot | htop
    · exfalso
      obtain ⟨x, y, hxy⟩ := h.nonab
      have hmem : ⁅x, y⁆ ∈ commutator G :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hxy (commutatorElement_eq_one_iff_mul_comm.mp hmem)
    · exact htop
  have hbG : b ∈ commutator G := by
    rw [hperf]
    exact Subgroup.mem_top b
  exact Lift.four_le_localRank_of_mono D M hirr hmono hML hself_le hbG

theorem ff81aProp1RankStep_proved : FF81aProp1RankStep := by
  intro G _ _ b L h hrank hnoL hT
  have h4 := h.four_le_localRank_of_torus hT hnoL
  omega


theorem kf_ff81aProp1_proved :
    KF_FF81aProp1 :=
  kf_ff81aProp1_of_rankStep kf_sp6Torus ff81aProp1RankStep_proved

end CFSG.RankThree.PartTwo.Sec21.FF81
