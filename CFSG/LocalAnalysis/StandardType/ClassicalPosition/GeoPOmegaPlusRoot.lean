module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoSiegelConj
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.WittOmega
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

theorem exists_conj_rootGroup_eq_siegelGroup_POmegaPlus (n : ℕ) (F : Type) [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n) (a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F)
    (hQ : (Spin.quadPlus n F) a₁ = 0 ∧ (Spin.quadPlus n F) a₂ = 0 ∧ (Spin.quadPlus n F) b₁ = 0 ∧
      (Spin.quadPlus n F) b₂ = 0)
    (h₁ : QuadraticMap.polar (Spin.quadPlus n F) a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar (Spin.quadPlus n F) a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar (Spin.quadPlus n F) a₁ a₂ = 0 ∧ QuadraticMap.polar (Spin.quadPlus n F)
      b₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus n F) a₁ b₂ = 0 ∧ QuadraticMap.polar (Spin.quadPlus n F) a₂
        b₁ = 0) :
    ∃ β, β ∈ (Spin.plusDatum n F hn).roots ∧ GGLongRoot (Spin.plusDatum n F hn) β ∧ ∃ u :
      ↥(spinGroup (Spin.quadPlus n F)),
      (((Spin.plusDatum n F hn).rootGroup β).map (MulAut.conj u).toMonoidHom).map
      (Spin.spinAction (Spin.quadPlus n F)) =
          siegelGroup (Spin.quadPlus n F) a₁ a₂ ∧
        (((Spin.plusDatum n F hn).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
        (Spin.spinAction (Spin.quadPlus n F)) =
          siegelGroup (Spin.quadPlus n F) b₁ b₂ := by
  obtain ⟨γ, hγ, hmax⟩ := exists_maxHeight (D := Spin.plusDatum n F hn) (show 0 < n by omega)
  have hlong : GGLongRoot (Spin.plusDatum n F hn) γ :=
    ⟨1, γ, hγ, hmax, by rw [map_one, Module.End.one_apply]⟩
  obtain ⟨i, j, hij, s, t, hst, hX⟩ := Spin.exists_plusRootGroup_eq (K := F) hn hγ
  let Fr : Spin.HypFrame (Spin.quadPlus n F) n := Spin.plusFrame n F hn
  have hX' : Spin.plusRootGroup n F hn γ = (Fr.longRoot hij s t).range := hX
  have hst_neg : Spin.toStdD n (-γ) =
      Pi.single i (Spin.boolSign (!s)) + Pi.single j (Spin.boolSign (!t)) := by
    calc Spin.toStdD n (-γ) = -Spin.toStdD n γ := Spin.toStdD_neg n γ
      _ = -(Pi.single i (Spin.boolSign s) + Pi.single j (Spin.boolSign t)) := by rw [hst]
      _ = Pi.single i (-Spin.boolSign s) + Pi.single j (-Spin.boolSign t) := by
            rw [neg_add, Pi.single_neg, Pi.single_neg]
      _ = Pi.single i (Spin.boolSign (!s)) + Pi.single j (Spin.boolSign (!t)) := by
            rw [Spin.boolSign_not, Spin.boolSign_not]
  have hXneg : Spin.plusRootGroup n F hn (-γ) = (Fr.longRoot hij (!s) (!t)).range :=
    Spin.plusRootGroup_eq hn hij (!s) (!t) hst_neg
  let w : Fin 4 → (Fin n ⊕ Fin n → F) :=
    ![Fr.vec j t, Fr.vec i s, Fr.vec j (!t), Fr.vec i (!s)]
  let w' : Fin 4 → (Fin n ⊕ Fin n → F) := ![a₁, a₂, b₁, b₂]
  have hQw : (Spin.quadPlus n F) (Fr.vec j t) = 0 ∧ (Spin.quadPlus n F) (Fr.vec i s) = 0 ∧
      (Spin.quadPlus n F) (Fr.vec j (!t)) = 0 ∧ (Spin.quadPlus n F) (Fr.vec i (!s)) = 0 :=
    ⟨Fr.map_vec j t, Fr.map_vec i s, Fr.map_vec j (!t), Fr.map_vec i (!s)⟩
  have h0w : QuadraticMap.polar (Spin.quadPlus n F) (Fr.vec j t) (Fr.vec i s) = 0 ∧
      QuadraticMap.polar (Spin.quadPlus n F) (Fr.vec j (!t)) (Fr.vec i (!s)) = 0 ∧
      QuadraticMap.polar (Spin.quadPlus n F) (Fr.vec j t) (Fr.vec i (!s)) = 0 ∧
      QuadraticMap.polar (Spin.quadPlus n F) (Fr.vec i s) (Fr.vec j (!t)) = 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [QuadraticMap.polar_comm, Fr.polar_vec_of_ne hij]
    · rw [QuadraticMap.polar_comm, Fr.polar_vec_of_ne hij]
    · rw [QuadraticMap.polar_comm, Fr.polar_vec_of_ne hij]
    · exact Fr.polar_vec_of_ne hij s (!t)
  have hw : LinearIndependent F w :=
    Geo.linearIndependent_quad_of_polar (Spin.quadPlus n F) hQw (Fr.polar_vec_not j t)
      (Fr.polar_vec_not i s) h0w
  have hw' : LinearIndependent F w' :=
    Geo.linearIndependent_quad_of_polar (Spin.quadPlus n F) hQ h₁ h₂ h₀
  have hQf : ∀ k, (Spin.quadPlus n F) (w' k) = (Spin.quadPlus n F) (w k) := by
    intro k
    fin_cases k <;>
      simp [w, w', Fr.map_vec, hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2]
  have ha1a1 : QuadraticMap.polar (Spin.quadPlus n F) a₁ a₁ = 0 := by
    rw [QuadraticMap.polar_self, hQ.1, smul_zero]
  have ha2a2 : QuadraticMap.polar (Spin.quadPlus n F) a₂ a₂ = 0 := by
    rw [QuadraticMap.polar_self, hQ.2.1, smul_zero]
  have hb1b1 : QuadraticMap.polar (Spin.quadPlus n F) b₁ b₁ = 0 := by
    rw [QuadraticMap.polar_self, hQ.2.2.1, smul_zero]
  have hb2b2 : QuadraticMap.polar (Spin.quadPlus n F) b₂ b₂ = 0 := by
    rw [QuadraticMap.polar_self, hQ.2.2.2, smul_zero]
  have hb1a1 : QuadraticMap.polar (Spin.quadPlus n F) b₁ a₁ = 1 := by
    rw [QuadraticMap.polar_comm, h₁]
  have hb2a2 : QuadraticMap.polar (Spin.quadPlus n F) b₂ a₂ = 1 := by
    rw [QuadraticMap.polar_comm, h₂]
  have ha2a1 : QuadraticMap.polar (Spin.quadPlus n F) a₂ a₁ = 0 := by
    rw [QuadraticMap.polar_comm, h₀.1]
  have hb2b1 : QuadraticMap.polar (Spin.quadPlus n F) b₂ b₁ = 0 := by
    rw [QuadraticMap.polar_comm, h₀.2.1]
  have hb1a2 : QuadraticMap.polar (Spin.quadPlus n F) b₁ a₂ = 0 := by
    rw [QuadraticMap.polar_comm, h₀.2.2.2]
  have hb2a1 : QuadraticMap.polar (Spin.quadPlus n F) b₂ a₁ = 0 := by
    rw [QuadraticMap.polar_comm, h₀.2.2.1]
  have hpol : ∀ k l, QuadraticMap.polar (Spin.quadPlus n F) (w' k) (w' l) =
      QuadraticMap.polar (Spin.quadPlus n F) (w k) (w l) := by
    intro k l
    fin_cases k <;> fin_cases l <;>
      simp [w, w', Fr.polar_vec_vec, hij, Ne.symm hij, h₁, h₂, hb1a1, hb2a2, h₀.1, h₀.2.1,
        h₀.2.2.1, h₀.2.2.2, ha2a1, hb2b1, hb1a2, hb2a1, ha1a1, ha2a2, hb1b1, hb2b2]
  obtain ⟨g, hgO, hg⟩ := CFSG.StandardType.TableBOrth.exists_orth_apply_eq
    (Spin.nondegenerate_polarBilin_quadPlus n F) w w' hw hw' hQf hpol
  obtain ⟨a₀, ha₀unit, ha₀⟩ := Fr.exists_aux i j
  let a : Fin n ⊕ Fin n → F := g a₀
  have ha : (Spin.quadPlus n F) a ≠ 0 := by
    rw [show a = g a₀ from rfl, CFSG.ClassicalGroups.Orthogonal.map_of_mem hgO]
    exact ha₀unit.ne_zero
  have haw : ∀ k, QuadraticMap.polar (Spin.quadPlus n F) a (w' k) = 0 := by
    intro k
    rw [show a = g a₀ from rfl, ← hg k,
      CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO, QuadraticMap.polar_comm]
    fin_cases k <;>
      simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · exact (ha₀ t).2
    · exact (ha₀ s).1
    · exact (ha₀ (!t)).2
    · exact (ha₀ (!s)).1
  obtain ⟨u, hu⟩ := exists_spinAction_apply_eq_POmegaPlus n F hn w w' hw hw' hQf hpol a ha haw
  refine ⟨γ, hγ, hlong, u, ?_, ?_⟩
  · rw [show (Spin.plusDatum n F hn).rootGroup γ = Spin.plusRootGroup n F hn γ from rfl, hX',
      Geo.map_conj_range_longRoot_eq_siegelGroup Fr hij s t u]
    have h0 : Spin.spinAction (Spin.quadPlus n F) u (Fr.vec j t) = a₁ := by
      change Spin.spinAction (Spin.quadPlus n F) u (w 0) = a₁
      exact hu 0
    have h1 : Spin.spinAction (Spin.quadPlus n F) u (Fr.vec i s) = a₂ := by
      change Spin.spinAction (Spin.quadPlus n F) u (w 1) = a₂
      exact hu 1
    rw [h0, h1]
  · rw [show (Spin.plusDatum n F hn).rootGroup (-γ) = Spin.plusRootGroup n F hn (-γ) from rfl,
      hXneg, Geo.map_conj_range_longRoot_eq_siegelGroup Fr hij (!s) (!t) u]
    have h2 : Spin.spinAction (Spin.quadPlus n F) u (Fr.vec j (!t)) = b₁ := by
      change Spin.spinAction (Spin.quadPlus n F) u (w 2) = b₁
      exact hu 2
    have h3 : Spin.spinAction (Spin.quadPlus n F) u (Fr.vec i (!s)) = b₂ := by
      change Spin.spinAction (Spin.quadPlus n F) u (w 3) = b₂
      exact hu 3
    rw [h2, h3]

end CFSG.StandardType.ClassicalPosition
