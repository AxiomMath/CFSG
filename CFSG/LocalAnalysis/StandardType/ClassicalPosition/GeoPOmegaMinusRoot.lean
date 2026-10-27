module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoSiegelConj
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.WittOmega
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

theorem exists_conj_rootGroup_eq_siegelGroup_POmegaMinus (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] {bq cq : F}
    (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    (a₁ a₂ b₁ b₂ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F)
    (hQ : (Spin.quadMinus n F bq cq) a₁ = 0 ∧ (Spin.quadMinus n F bq cq) a₂ = 0 ∧
      (Spin.quadMinus n F bq cq) b₁ = 0 ∧ (Spin.quadMinus n F bq cq) b₂ = 0)
    (h₁ : QuadraticMap.polar (Spin.quadMinus n F bq cq) a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar (Spin.quadMinus n F bq cq) a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar (Spin.quadMinus n F bq cq) a₁ a₂ = 0 ∧ QuadraticMap.polar
      (Spin.quadMinus n F bq cq) b₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadMinus n F bq cq) a₁ b₂ = 0 ∧ QuadraticMap.polar
        (Spin.quadMinus n F bq cq) a₂ b₁ = 0) :
    ∃ β, β ∈ (Spin.Twisted.minusDatum n hirr).roots ∧ GGLongRoot (Spin.Twisted.minusDatum n hirr) β
      ∧ ∃ u : ↥(spinGroup (Spin.quadMinus n F bq cq)),
      (((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom).map
      (Spin.spinAction (Spin.quadMinus n F bq cq)) =
          siegelGroup (Spin.quadMinus n F bq cq) a₁ a₂ ∧
        (((Spin.Twisted.minusDatum n hirr).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
        (Spin.spinAction (Spin.quadMinus n F bq cq)) =
          siegelGroup (Spin.quadMinus n F bq cq) b₁ b₂ := by
  let Q : QuadraticForm F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) :=
    Spin.quadMinus n F bq cq
  have hQp : Q a₁ = 0 ∧ Q a₂ = 0 ∧ Q b₁ = 0 ∧ Q b₂ = 0 := hQ
  have h₁p : QuadraticMap.polar Q a₁ b₁ = 1 := h₁
  have h₂p : QuadraticMap.polar Q a₂ b₂ = 1 := h₂
  have h₀p : QuadraticMap.polar Q a₁ a₂ = 0 ∧ QuadraticMap.polar Q b₁ b₂ = 0 ∧
      QuadraticMap.polar Q a₁ b₂ = 0 ∧ QuadraticMap.polar Q a₂ b₁ = 0 := h₀
  obtain ⟨γ, hγ, hmax⟩ :=
    exists_maxHeight (D := Spin.Twisted.minusDatum n hirr) (show 0 < n - 1 by omega)
  have hlong : GGLongRoot (Spin.Twisted.minusDatum n hirr) γ :=
    ⟨1, γ, hγ, hmax, by rw [map_one, Module.End.one_apply]⟩
  obtain ⟨i, j, hij, s, t, hst⟩ :=
    RootCentOmega.exists_long_of_ggLongRoot_minus hirr hn hlong
  let Fr : Spin.HypFrame Q (n - 1) := (Spin.Twisted.minusFrame n bq cq).toHypFrame
  have hX : Spin.Twisted.minusRootGroup n hirr γ = (Fr.longRoot hij s t).range :=
    Spin.Twisted.minusRootGroup_eq_long n hirr hij s t hst
  have hst_neg : Spin.toStdB (n - 1) (-γ) =
      Pi.single i (Spin.boolSign (!s)) + Pi.single j (Spin.boolSign (!t)) := by
    calc Spin.toStdB (n - 1) (-γ) = -Spin.toStdB (n - 1) γ := Spin.toStdB_neg (n - 1) γ
      _ = -(Pi.single i (Spin.boolSign s) + Pi.single j (Spin.boolSign t)) := by rw [hst]
      _ = Pi.single i (-Spin.boolSign s) + Pi.single j (-Spin.boolSign t) := by
            rw [neg_add, Pi.single_neg, Pi.single_neg]
      _ = Pi.single i (Spin.boolSign (!s)) + Pi.single j (Spin.boolSign (!t)) := by
            rw [Spin.boolSign_not, Spin.boolSign_not]
  have hXneg : Spin.Twisted.minusRootGroup n hirr (-γ) = (Fr.longRoot hij (!s) (!t)).range :=
    Spin.Twisted.minusRootGroup_eq_long n hirr hij (!s) (!t) hst_neg
  let w : Fin 4 → (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) :=
    ![Fr.vec j t, Fr.vec i s, Fr.vec j (!t), Fr.vec i (!s)]
  let w' : Fin 4 → (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) := ![a₁, a₂, b₁, b₂]
  have hQw : Q (Fr.vec j t) = 0 ∧ Q (Fr.vec i s) = 0 ∧ Q (Fr.vec j (!t)) = 0 ∧
      Q (Fr.vec i (!s)) = 0 :=
    ⟨Fr.map_vec j t, Fr.map_vec i s, Fr.map_vec j (!t), Fr.map_vec i (!s)⟩
  have h0w : QuadraticMap.polar Q (Fr.vec j t) (Fr.vec i s) = 0 ∧
      QuadraticMap.polar Q (Fr.vec j (!t)) (Fr.vec i (!s)) = 0 ∧
      QuadraticMap.polar Q (Fr.vec j t) (Fr.vec i (!s)) = 0 ∧
      QuadraticMap.polar Q (Fr.vec i s) (Fr.vec j (!t)) = 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [QuadraticMap.polar_comm, Fr.polar_vec_of_ne hij]
    · rw [QuadraticMap.polar_comm, Fr.polar_vec_of_ne hij]
    · rw [QuadraticMap.polar_comm, Fr.polar_vec_of_ne hij]
    · exact Fr.polar_vec_of_ne hij s (!t)
  have hw : LinearIndependent F w :=
    Geo.linearIndependent_quad_of_polar Q hQw (Fr.polar_vec_not j t) (Fr.polar_vec_not i s) h0w
  have hw' : LinearIndependent F w' := Geo.linearIndependent_quad_of_polar Q hQp h₁p h₂p h₀p
  have hQf : ∀ k, Q (w' k) = Q (w k) := by
    intro k
    fin_cases k <;>
      simp [w, w', Fr.map_vec, hQp.1, hQp.2.1, hQp.2.2.1, hQp.2.2.2]
  have ha1a1 : QuadraticMap.polar Q a₁ a₁ = 0 := by
    rw [QuadraticMap.polar_self, hQp.1, smul_zero]
  have ha2a2 : QuadraticMap.polar Q a₂ a₂ = 0 := by
    rw [QuadraticMap.polar_self, hQp.2.1, smul_zero]
  have hb1b1 : QuadraticMap.polar Q b₁ b₁ = 0 := by
    rw [QuadraticMap.polar_self, hQp.2.2.1, smul_zero]
  have hb2b2 : QuadraticMap.polar Q b₂ b₂ = 0 := by
    rw [QuadraticMap.polar_self, hQp.2.2.2, smul_zero]
  have hb1a1 : QuadraticMap.polar Q b₁ a₁ = 1 := by
    rw [QuadraticMap.polar_comm, h₁p]
  have hb2a2 : QuadraticMap.polar Q b₂ a₂ = 1 := by
    rw [QuadraticMap.polar_comm, h₂p]
  have ha2a1 : QuadraticMap.polar Q a₂ a₁ = 0 := by
    rw [QuadraticMap.polar_comm, h₀p.1]
  have hb2b1 : QuadraticMap.polar Q b₂ b₁ = 0 := by
    rw [QuadraticMap.polar_comm, h₀p.2.1]
  have hb1a2 : QuadraticMap.polar Q b₁ a₂ = 0 := by
    rw [QuadraticMap.polar_comm, h₀p.2.2.2]
  have hb2a1 : QuadraticMap.polar Q b₂ a₁ = 0 := by
    rw [QuadraticMap.polar_comm, h₀p.2.2.1]
  have hpol : ∀ k l, QuadraticMap.polar Q (w' k) (w' l) =
      QuadraticMap.polar Q (w k) (w l) := by
    intro k l
    fin_cases k <;> fin_cases l <;>
      simp [w, w', Fr.polar_vec_vec, hij, Ne.symm hij, h₁p, h₂p, hb1a1, hb2a2, h₀p.1,
        h₀p.2.1, h₀p.2.2.1, h₀p.2.2.2, ha2a1, hb2b1, hb1a2, hb2a1, ha1a1, ha2a2, hb1b1,
        hb2b2]
  obtain ⟨g, hgO, hg⟩ := CFSG.StandardType.TableBOrth.exists_orth_apply_eq
    (Spin.nondegenerate_polarBilin_quadMinus_of_finite n F hirr) w w' hw hw' hQf hpol
  obtain ⟨a₀, ha₀unit, ha₀⟩ := Fr.exists_aux i j
  let a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F := g a₀
  have ha : Q a ≠ 0 := by
    rw [show a = g a₀ from rfl, CFSG.ClassicalGroups.Orthogonal.map_of_mem hgO]
    exact ha₀unit.ne_zero
  have haw : ∀ k, QuadraticMap.polar Q a (w' k) = 0 := by
    intro k
    rw [show a = g a₀ from rfl, ← hg k,
      CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO, QuadraticMap.polar_comm]
    fin_cases k <;>
      simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · exact (ha₀ t).2
    · exact (ha₀ s).1
    · exact (ha₀ (!t)).2
    · exact (ha₀ (!s)).1
  obtain ⟨u, hu⟩ :=
    exists_spinAction_apply_eq_POmegaMinus n hirr hn w w' hw hw' hQf hpol a ha haw
  refine ⟨γ, hγ, hlong, u, ?_, ?_⟩
  · rw [show (Spin.Twisted.minusDatum n hirr).rootGroup γ =
        Spin.Twisted.minusRootGroup n hirr γ from rfl, hX,
      Geo.map_conj_range_longRoot_eq_siegelGroup Fr hij s t u]
    have h0 : Spin.spinAction Q u (Fr.vec j t) = a₁ := by
      change Spin.spinAction Q u (w 0) = a₁
      exact hu 0
    have h1 : Spin.spinAction Q u (Fr.vec i s) = a₂ := by
      change Spin.spinAction Q u (w 1) = a₂
      exact hu 1
    rw [h0, h1]
  · rw [show (Spin.Twisted.minusDatum n hirr).rootGroup (-γ) =
        Spin.Twisted.minusRootGroup n hirr (-γ) from rfl, hXneg,
      Geo.map_conj_range_longRoot_eq_siegelGroup Fr hij (!s) (!t) u]
    have h2 : Spin.spinAction Q u (Fr.vec j (!t)) = b₁ := by
      change Spin.spinAction Q u (w 2) = b₁
      exact hu 2
    have h3 : Spin.spinAction Q u (Fr.vec i (!s)) = b₂ := by
      change Spin.spinAction Q u (w 3) = b₂
      exact hu 3
    rw [h2, h3]

end CFSG.StandardType.ClassicalPosition
