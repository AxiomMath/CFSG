module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6NonsplitFrame
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem exists_conj_component_of_action
    {R : Type*} [Group R] {k p : ℕ}
    (T : Multiplicative (Fin k → ZMod p) →* R)
    {c n : R} {u v : Equiv.Perm (Fin k → ZMod p)}
    (hc : ∀ x : Fin k → ZMod p,
      c * T (Multiplicative.ofAdd x) * c⁻¹ =
        T (Multiplicative.ofAdd (v x)))
    (hn : ∀ x : Fin k → ZMod p,
      n * T (Multiplicative.ofAdd x) * n⁻¹ =
        T (Multiplicative.ofAdd (u x)))
    {J : Subgroup R} (hnJ : n ∈ J)
    (hcomp : Assembly.IsComponentOf J
      (Subgroup.centralizer (T '' {x : Multiplicative (Fin k → ZMod p) |
        u (Multiplicative.toAdd x) = Multiplicative.toAdd x})))
    (hdvd : p ∣ Nat.card J) :
    c * n * c⁻¹ ∈ J.map (MulAut.conj c).toMonoidHom ∧
    (∀ x : Fin k → ZMod p,
      (c * n * c⁻¹) * T (Multiplicative.ofAdd x) * (c * n * c⁻¹)⁻¹ =
        T (Multiplicative.ofAdd ((v * u * v⁻¹) x))) ∧
    Assembly.IsComponentOf (J.map (MulAut.conj c).toMonoidHom)
      (Subgroup.centralizer (T '' {x : Multiplicative (Fin k → ZMod p) |
        (v * u * v⁻¹) (Multiplicative.toAdd x) = Multiplicative.toAdd x})) ∧
    p ∣ Nat.card (J.map (MulAut.conj c).toMonoidHom) := by
  classical
  let r : R := c * n * c⁻¹
  have hc_inv : ∀ y : Fin k → ZMod p,
      c⁻¹ * T (Multiplicative.ofAdd y) * c =
        T (Multiplicative.ofAdd (v⁻¹ y)) := by
    intro y
    have h' : c * T (Multiplicative.ofAdd (v⁻¹ y)) * c⁻¹ =
        T (Multiplicative.ofAdd y) := by
      have hv : v (v⁻¹ y) = y := Equiv.apply_symm_apply v y
      calc
        c * T (Multiplicative.ofAdd (v⁻¹ y)) * c⁻¹ =
            T (Multiplicative.ofAdd (v (v⁻¹ y))) := hc _
        _ = T (Multiplicative.ofAdd y) := by rw [hv]
    calc
      c⁻¹ * T (Multiplicative.ofAdd y) * c
          = c⁻¹ * (c * T (Multiplicative.ofAdd (v⁻¹ y)) * c⁻¹) * c := by
              rw [← h']
      _ = T (Multiplicative.ofAdd (v⁻¹ y)) := by group
  have hact : ∀ x : Fin k → ZMod p,
      r * T (Multiplicative.ofAdd x) * r⁻¹ =
        T (Multiplicative.ofAdd ((v * u * v⁻¹) x)) := by
    intro x
    calc
      r * T (Multiplicative.ofAdd x) * r⁻¹
          = c * n * (c⁻¹ * T (Multiplicative.ofAdd x) * c) * n⁻¹ * c⁻¹ := by
              simp only [r]
              group
      _ = c * n * T (Multiplicative.ofAdd (v⁻¹ x)) * n⁻¹ * c⁻¹ := by
              rw [hc_inv x]
      _ = c * (n * T (Multiplicative.ofAdd (v⁻¹ x)) * n⁻¹) * c⁻¹ := by group
      _ = c * T (Multiplicative.ofAdd (u (v⁻¹ x))) * c⁻¹ := by rw [hn]
      _ = T (Multiplicative.ofAdd (v (u (v⁻¹ x)))) := hc _
      _ = T (Multiplicative.ofAdd ((v * u * v⁻¹) x)) := rfl
  have hfix : (MulAut.conj c).toMonoidHom '' (T '' {x : Multiplicative (Fin k → ZMod p) |
      u (Multiplicative.toAdd x) = Multiplicative.toAdd x}) =
      T '' {x : Multiplicative (Fin k → ZMod p) |
        (v * u * v⁻¹) (Multiplicative.toAdd x) = Multiplicative.toAdd x} := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨Multiplicative.ofAdd (v (Multiplicative.toAdd x)), ?_, ?_⟩
      · show (v * u * v⁻¹) (Multiplicative.toAdd
            (Multiplicative.ofAdd (v (Multiplicative.toAdd x)))) =
          Multiplicative.toAdd (Multiplicative.ofAdd (v (Multiplicative.toAdd x)))
        rw [toAdd_ofAdd]
        have hx' : u (Multiplicative.toAdd x) = Multiplicative.toAdd x := by
          simpa only [Set.mem_setOf_eq] using hx
        simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv]
        rw [Equiv.symm_apply_apply, hx']
      · change T (Multiplicative.ofAdd (v (Multiplicative.toAdd x))) =
          c * T x * c⁻¹
        exact (hc (Multiplicative.toAdd x)).symm
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨T (Multiplicative.ofAdd (v⁻¹ (Multiplicative.toAdd z))),
        ⟨Multiplicative.ofAdd (v⁻¹ (Multiplicative.toAdd z)), ?_, rfl⟩, ?_⟩
      · show u (Multiplicative.toAdd
            (Multiplicative.ofAdd (v⁻¹ (Multiplicative.toAdd z)))) =
          Multiplicative.toAdd (Multiplicative.ofAdd (v⁻¹ (Multiplicative.toAdd z)))
        rw [toAdd_ofAdd]
        have hz' : u (v⁻¹ (Multiplicative.toAdd z)) = v⁻¹ (Multiplicative.toAdd z) := by
          apply v.injective
          have hzmem : (v * u * v⁻¹) (Multiplicative.toAdd z) =
              Multiplicative.toAdd z := by
            simpa only [Set.mem_setOf_eq] using hz
          calc
            v (u (v⁻¹ (Multiplicative.toAdd z))) = Multiplicative.toAdd z := by
              simpa only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv,
                Equiv.symm_apply_apply] using hzmem
            _ = v (v⁻¹ (Multiplicative.toAdd z)) :=
              (Equiv.apply_symm_apply v (Multiplicative.toAdd z)).symm
        exact hz'
      · change c * T (Multiplicative.ofAdd (v⁻¹ (Multiplicative.toAdd z))) * c⁻¹ = T z
        rw [hc _]
        have hv : v (v⁻¹ (Multiplicative.toAdd z)) = Multiplicative.toAdd z :=
          Equiv.apply_symm_apply v (Multiplicative.toAdd z)
        rw [hv, ofAdd_toAdd]
  have hcent : (Subgroup.centralizer (T '' {x : Multiplicative (Fin k → ZMod p) |
      u (Multiplicative.toAdd x) = Multiplicative.toAdd x})).map
      (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ((MulAut.conj c).toMonoidHom '' (T '' {
        x : Multiplicative (Fin k → ZMod p) |
        u (Multiplicative.toAdd x) = Multiplicative.toAdd x})) := by
    apply le_antisymm
    · exact Subgroup.map_centralizer_le_centralizer_image _ (MulAut.conj c).toMonoidHom
    · intro x hx
      refine ⟨c⁻¹ * x * c, ?_, ?_⟩
      · refine (Subgroup.mem_centralizer_iff).mpr ?_
        intro y hy
        have h := (Subgroup.mem_centralizer_iff.mp hx) (c * y * c⁻¹)
          ⟨y, hy, rfl⟩
        calc
          y * (c⁻¹ * x * c) = c⁻¹ * ((c * y * c⁻¹) * x) * c := by group
          _ = c⁻¹ * (x * (c * y * c⁻¹)) * c := by rw [h]
          _ = (c⁻¹ * x * c) * y := by group
      · change c * (c⁻¹ * x * c) * c⁻¹ = x
        group
  have hmap : Assembly.IsComponentOf (J.map (MulAut.conj c).toMonoidHom)
      ((Subgroup.centralizer (T '' {x : Multiplicative (Fin k → ZMod p) |
        u (Multiplicative.toAdd x) = Multiplicative.toAdd x})).map
          (MulAut.conj c).toMonoidHom) :=
    ⟨Subgroup.map_mono hcomp.1, hcomp.2.1.map (MulAut.conj c).toMonoidHom,
      hcomp.2.2.of_mulEquiv
        (Subgroup.equivMapOfInjective J (MulAut.conj c).toMonoidHom
          (MulAut.conj c).injective).symm⟩
  rw [hcent, hfix] at hmap
  refine ⟨?_, hact, hmap, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨n, hnJ, rfl⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hdvd

end CFSG.StandardType

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K]

theorem exists_component_of_conj_simple (D : E6QPlusThreeFrame K)
    (hsurj : Function.Surjective D.weyl)
    (hsimple : ∀ a : Fin Tag.F4.rank,
      ∃ (n : adjointGroup .E6 K) (J : Subgroup (adjointGroup .E6 K)),
        n ∈ J ∧
        (∀ s : Fin Tag.F4.rank → ZMod 3,
          n * D.frame (Multiplicative.ofAdd s) * n⁻¹ =
            D.frame (Multiplicative.ofAdd
              (TableBExc.torusAct .F4 3 (simple .F4 a) s))) ∧
        Assembly.IsComponentOf J
          (Subgroup.centralizer (SuSplitRootGen.torusFix D.frame
            (TableBExc.torusAct .F4 3 (simple .F4 a)))) ∧
        3 ∣ Nat.card J)
    {w : WeylGroup .F4} {a : Fin Tag.F4.rank} {vW : WeylGroup .F4}
    (hw : w = vW * (simple .F4 a) * vW⁻¹) :
    ∃ (r : adjointGroup .E6 K) (J' : Subgroup (adjointGroup .E6 K)),
      r ∈ J' ∧
      (∀ s : Fin Tag.F4.rank → ZMod 3,
        r * D.frame (Multiplicative.ofAdd s) * r⁻¹ =
          D.frame (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 w s))) ∧
      Assembly.IsComponentOf J'
        (Subgroup.centralizer (SuSplitRootGen.torusFix D.frame
          (TableBExc.torusAct .F4 3 w))) ∧
      3 ∣ Nat.card J' := by
  classical
  obtain ⟨n, J, hnJ, hact_simple, hcomp_simple, hdvd⟩ := hsimple a
  obtain ⟨c, hc_weyl⟩ := hsurj vW
  let cR : adjointGroup .E6 K := c
  let uP : Equiv.Perm (Fin Tag.F4.rank → ZMod 3) :=
    TableBExc.torusPerm .F4 3 (simple .F4 a)
  let vP : Equiv.Perm (Fin Tag.F4.rank → ZMod 3) :=
    TableBExc.torusPerm .F4 3 vW
  have hc : ∀ x : Fin Tag.F4.rank → ZMod 3,
      cR * D.frame (Multiplicative.ofAdd x) * cR⁻¹ =
        D.frame (Multiplicative.ofAdd (vP x)) := by
    intro x
    dsimp only [vP]
    rw [TableBExc.torusPerm_apply]
    simpa only [cR, hc_weyl] using D.conj_frame c x
  have hn : ∀ x : Fin Tag.F4.rank → ZMod 3,
      n * D.frame (Multiplicative.ofAdd x) * n⁻¹ =
        D.frame (Multiplicative.ofAdd (uP x)) := by
    intro x
    dsimp only [uP]
    rw [TableBExc.torusPerm_apply]
    exact hact_simple x
  have hfix_u : SuSplitRootGen.torusFix D.frame
      (TableBExc.torusAct .F4 3 (simple .F4 a)) =
      D.frame '' {x : Multiplicative (Fin Tag.F4.rank → ZMod 3) |
        uP (Multiplicative.toAdd x) = Multiplicative.toAdd x} := by
    simp only [SuSplitRootGen.torusFix, uP, TableBExc.torusPerm_apply]
  have hcomp_gen : Assembly.IsComponentOf J
      (Subgroup.centralizer (D.frame '' {
        x : Multiplicative (Fin Tag.F4.rank → ZMod 3) |
        uP (Multiplicative.toAdd x) = Multiplicative.toAdd x})) := by
    simpa only [hfix_u] using hcomp_simple
  obtain ⟨hrJ, hact, hcomp, hdvd'⟩ :=
    exists_conj_component_of_action (T := D.frame) (c := cR) (n := n)
      (u := uP) (v := vP) hc hn hnJ hcomp_gen hdvd
  have hperm_w : vP * uP * vP⁻¹ = TableBExc.torusPerm .F4 3 w := by
    dsimp only [vP, uP]
    rw [hw, map_mul, map_mul, map_inv]
  have hfix_w : SuSplitRootGen.torusFix D.frame
      (TableBExc.torusAct .F4 3 w) =
      D.frame '' {x : Multiplicative (Fin Tag.F4.rank → ZMod 3) |
        (TableBExc.torusPerm .F4 3 w) (Multiplicative.toAdd x) =
          Multiplicative.toAdd x} := by
    simp only [SuSplitRootGen.torusFix, TableBExc.torusPerm_apply]
  have hact_w : ∀ s : Fin Tag.F4.rank → ZMod 3,
      (cR * n * cR⁻¹) * D.frame (Multiplicative.ofAdd s) * (cR * n * cR⁻¹)⁻¹ =
        D.frame (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 w s)) := by
    intro s
    rw [hact s, hperm_w, TableBExc.torusPerm_apply]
  have hcomp_w : Assembly.IsComponentOf (J.map (MulAut.conj cR).toMonoidHom)
      (Subgroup.centralizer (SuSplitRootGen.torusFix D.frame
        (TableBExc.torusAct .F4 3 w))) := by
    rw [hperm_w, ← hfix_w] at hcomp
    exact hcomp
  exact ⟨cR * n * cR⁻¹, J.map (MulAut.conj cR).toMonoidHom, hrJ, hact_w, hcomp_w, hdvd'⟩

end CFSG.StandardType.ExcFrames.E6QPlusThree

end
