module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClData
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClWitt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClTheoremX

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem ReprData.naturalRep_of_basis {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K]
    [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t)}
    (D : ReprData (Vt M (LB M Q B) B Z t) (Rt M (LB M Q B) t) (hc.CN t) M₀ hS t)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) (X : Subgroup (GL ι K))
    (hX : (b.toGL.toMonoidHom.comp D.ρ).range = X) :
    NaturalRep (ι := ι) K X (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := by
  obtain ⟨φ, hφ, hker, hsec⟩ := D.sec b
  have hφeq : φ = b.toGL.toMonoidHom.comp D.ρ := MonoidHom.ext fun r => hφ r
  refine ⟨φ, ?_, hker, hsec⟩
  rw [hφeq]
  exact hX

theorem stroth310Classify_of_theoremX (h34 : Stroth34Statement)
    (hX : Classify.TheoremXStatement) : Stroth310ClassifyStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs _hR hnot hSymp
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun c _ he => hc.smul_mem_img_Vt h t c he
  obtain ⟨D⟩ := hc.exists_reprData h34 hs hnot h hS
  have hKZ : Nat.card (GaloisField 2 n') = Nat.card Z := h.card
  have hq4 : 4 ≤ Nat.card (GaloisField 2 n') := by
    rw [hKZ]
    exact hc.hyp.q4
  have hdim : 4 ≤ Module.finrank (GaloisField 2 n')
      ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) := by
    obtain ⟨K₁, _, _, hK₁, m₁, hm₁, φ₁, -, -, hsec⟩ := hSymp
    have hcardV := card_eq_of_sectionAct (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t))
      hsec
    have hcardM := M₀.card_eq (hc.Vt_le_Q t) (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B)
      (t := t))
    have hfin : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) =
        Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => mem_imgSub.symm)
    have hpow : Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) =
        Nat.card (GaloisField 2 n') ^ Module.finrank (GaloisField 2 n')
          ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) :=
      Module.natCard_eq_pow_finrank (K := GaloisField 2 n')
        (V := ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS))
    rw [hcardV, hfin] at hcardM
    have h2 := Nat.eq_of_mul_eq_mul_left Nat.card_pos hcardM
    simp only [Fintype.card_sum, Fintype.card_fin] at h2
    rw [hK₁, hpow, hKZ] at h2
    have h3 : 2 ≤ Nat.card Z := by
      have := hc.hyp.q4
      omega
    have h4 := Nat.pow_right_injective h3 h2
    omega
  obtain ⟨P, hP0, hPspan, hPful, hPgen⟩ := hc.theoremX_data h34 hs h D hdim
  have hH : D.ρ.range ≤ Classify.sympSubgroup D.F := by
    rintro _ ⟨r, rfl⟩
    exact D.isom r
  rcases hX (GaloisField 2 n') ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) D.F hq4 D.nondeg D.alt
      hdim D.ρ.range hH P hP0 hPspan hPful hPgen with hsp | ⟨Qf, hQf, hΩ⟩
  · obtain ⟨m, b, hfin, hr⟩ := Classify.exists_basis_range_symp D.F D.nondeg D.alt D.ρ hsp
    exact Or.inl ⟨GaloisField 2 n', inferInstance, inferInstance, hKZ, m, by omega,
      D.naturalRep_of_basis b _ hr⟩
  · have hnd' : Qf.polarBilin.Nondegenerate := hQf ▸ D.nondeg
    obtain ⟨k, hk⟩ := LinearMap.BilinForm.IsAlt.even_finrank D.alt D.nondeg
    have hk2 : 2 ≤ k := by omega
    rcases Classify.exists_basis_range_omega Qf hnd' (by omega) (hk.trans (two_mul k).symm) D.ρ
      hΩ with
      ⟨b, hr⟩ | ⟨β, γ', b, hβ, hirr, hr⟩
    · by_cases hk3 : 3 ≤ k
      · exact Or.inr (Or.inl ⟨GaloisField 2 n', inferInstance, inferInstance, hKZ,
          Or.inl ⟨k, hk3, D.naturalRep_of_basis b _ hr⟩⟩)
      · have hk2' : k = 2 := by omega
        subst hk2'
        exact Or.inr (Or.inr ⟨GaloisField 2 n', inferInstance, inferInstance, hKZ,
          D.naturalRep_of_basis b _ hr⟩)
    · exact Or.inr (Or.inl ⟨GaloisField 2 n', inferInstance, inferInstance, hKZ,
        Or.inr ⟨k, β, γ', hk2, hirr, D.naturalRep_of_basis b _ hr⟩⟩)

theorem stroth310Classify_of_inputs (h34 : Stroth34Statement) (hMcL : McLaughlinStatement)
    (hSp4 : Classify.LemmaPStatement) (hSiegel : Classify.SiegelGenStatement) :
    Stroth310ClassifyStatement :=
  stroth310Classify_of_theoremX h34 (Classify.theoremX_of_inputs hMcL hSp4 hSiegel)

end CFSG.RankThree.GF2n.Stroth80
