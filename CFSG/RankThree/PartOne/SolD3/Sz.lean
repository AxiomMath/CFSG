module

public import CFSG.RankThree.PartOne.SolD3.Struct
public import CFSG.RankThree.PartOne.SolD3.Inputs3

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit.SolK CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.Asc76X
open scoped commutatorElement

theorem false_of_szU3 (hInd : SzU3SylowIndecomposable) {G : Type} [Group G] [Finite G]
    {M X : Subgroup G} {a : G} (h : Hyp3 G M X) (hb : Blk3 X a)
    (hSz : (∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel G .twistedB2 0 2 s) ∨
      (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel G .PSU 3 2 s)) : False := by
  classical
  obtain ⟨q, k, -, hB⟩ := exists_fusionBenderBorel_of_isSzOrU3
    (CFSG.CGT.PushingUpLit.STT.isSzOrU3_of_stated hSz)
  obtain ⟨S₁, hWS⟩ := hb.isPGroup_W.exists_le_sylow
  have hS₁ne : (S₁ : Subgroup G) ≠ ⊥ := fun hbot => hb.W_ne_bot (le_bot_iff.1 (hbot ▸ hWS))
  obtain ⟨⟨-, -, hodd⟩, -, -, -, -⟩ := hB S₁
  have hNW : Subgroup.normalizer ((pCoreOf 2 X : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((S₁ : Subgroup G) : Set G) := by
    intro g hg
    by_contra hgS
    have hginv : g⁻¹ ∉ Subgroup.normalizer ((S₁ : Subgroup G) : Set G) := fun hh =>
      hgS (by simpa using (Subgroup.normalizer _).inv_mem hh)
    have h1 := hodd g⁻¹ hginv
    have hle : pCoreOf 2 X ≤ Subgroup.normalizer ((S₁ : Subgroup G) : Set G) ⊓
        (Subgroup.normalizer ((S₁ : Subgroup G) : Set G)).map
          (MulAut.conj g⁻¹⁻¹).toMonoidHom := by
      intro w hw
      refine Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer (hWS hw), ?_⟩
      have hw' : g⁻¹ * w * g ∈ pCoreOf 2 X := by
        have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hg) w).1 hw
        simpa using this
      refine ⟨g⁻¹ * w * g, Subgroup.le_normalizer (hWS hw'), ?_⟩
      show g⁻¹⁻¹ * (g⁻¹ * w * g) * (g⁻¹⁻¹)⁻¹ = w
      group
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hb.card] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    obtain ⟨m, hm⟩ := h1
    omega
  have hMW : M ≤ Subgroup.normalizer ((pCoreOf 2 X : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => h.W_normalized hm hw, fun hw => ?_⟩
    have := h.W_normalized (M.inv_mem hm) hw
    simpa [mul_assoc] using this
  have hMB : M ≤ Subgroup.normalizer ((S₁ : Subgroup G) : Set G) := fun m hm => hNW (hMW hm)
  have hBM : Subgroup.normalizer ((S₁ : Subgroup G) : Set G) ≤ M := by
    by_contra hBM
    have hlt : M < Subgroup.normalizer ((S₁ : Subgroup G) : Set G) :=
      lt_of_le_of_ne hMB (fun h' => hBM (h' ▸ le_rfl))
    exact h.maxLocal.2 _ hlt ⟨S₁, hS₁ne, S₁.isPGroup', rfl⟩
  have hS₁M : (S₁ : Subgroup G) ≤ M := fun x hx => hBM (Subgroup.le_normalizer hx)
  have hS₁Q : (S₁ : Subgroup G) ≤ pCoreOf 2 M :=
    le_pCoreOf_of_normalized hS₁M
      (fun m hm x hx => (Subgroup.mem_normalizer_iff.1 (hMB hm) x).1 hx) S₁.isPGroup'
  have hQS : pCoreOf 2 M = (S₁ : Subgroup G) := S₁.is_maximal' (isPGroup_pCoreOf' M) hS₁Q
  refine hInd G hSz S₁ (pCoreOf 2 X) (rOf M X) hb.W_ne_bot hWS ?_ ?_ ?_ ?_
  · rw [← hQS]
    exact inf_le_left
  · intro w hw q hq
    rw [← hQS] at hq
    have := h.q_comm_W hb hq w hw
    calc w * q = (q * w * q⁻¹) * q := by rw [this]
      _ = q * w := by group
  · refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    exact Hyp3.W_inf_C hb (Subgroup.mem_inf.1 hx).1 (Subgroup.mem_inf.1 hx).2.2
  · intro q hq
    rw [← hQS] at hq
    exact h.q_eq_W_mul_R hb hq

end CFSG.RankThree.PartOne.SolD3
