module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitTableP
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

theorem qtwoDB25_orthY_of
    (hRig : GGLabelRigidInput) {Bs N : Subgroup G} {x : G} (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hinner : GGInnerDiagOn Bs N) (hx : x ∈ Bs)
    (hnotcent : x ∉ Subgroup.centralizer (N : Set G)) {d : ℕ} {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (hD : (Even d ∧ 5 ≤ d ∧ lab = ⟨.D, d, 1⟩) ∨ (Odd d ∧ 5 ≤ d ∧ lab = ⟨.twD, d, 1⟩)) :
    ∃ Φ : OrthTorus.OrthFrameCore 3 Bs N, Nat.card Φ.F = 2 ∧ Φ.r = d ∧
      Subgroup.center ↥N = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect ↥N := Group.isPerfect_def.mpr hinner.1
  have hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs N :=
    ggInnerDiagOn_relabel hRig hinner hΛ hlab
  have hProw : ∀ lab' : LargeEvenLabel, (fun _ lab' => lab' = lab) 3 lab' →
      ggRowP_EOmP 3 lab' ∨ ggRowP_EOmM 3 lab' := by
    intro lab' h
    have h' : lab' = lab := h
    subst h'
    rcases hD with ⟨heven, hd, rfl⟩ | ⟨hodd, hd, rfl⟩
    · exact Or.inl ⟨rfl, by change 4 ≤ d; omega, heven, by norm_num⟩
    · exact Or.inr ⟨rfl, by change 5 ≤ d; omega, hodd, by norm_num⟩
  have hZK : ∀ lab' : LargeEvenLabel, (fun _ lab' => lab' = lab) 3 lab' →
      GGHasLabel lab' (↥N ⧸ Subgroup.center ↥N) → Subgroup.center ↥N = ⊥ := by
    intro lab' h hhas
    have h' : lab' = lab := h
    subst h'
    refine CFSG.StandardType.OrthTorus.center_eq_bot_of_hasLabel_orth_two ?_ ?_ hhas
    · rcases hD with ⟨heven, hd, rfl⟩ | ⟨-, hd, rfl⟩
      · refine Or.inl ⟨rfl, ?_⟩
        change 5 ≤ d
        omega
      · exact Or.inr ⟨rfl, by change 4 ≤ d; omega⟩
    · rcases hD with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
  have hact : ∀ hNn : Bs ≤ Subgroup.normalizer (N : Set G),
      ∃ b : ↥Bs, ggGamma N hNn b ≠ 1 := by
    intro hNn
    refine ⟨⟨x, hx⟩, ?_⟩
    intro h1
    rw [ggGamma_eq_one_iff N hNn] at h1
    exact hnotcent h1
  obtain ⟨lab', hPlab', hhas', Φ, hr, hcard, -, -, -⟩ :=
    CFSG.StandardType.OrthTorus.exists_orthFrameCore_of_marking (P := fun _ lab' => lab' = lab)
      hRig (by norm_num : (3 : ℕ) ≠ 2) hBs hSC hProw hmark hZK hact
  have hlab'_eq : lab' = lab := hPlab'
  refine ⟨Φ, ?_, ?_, ?_⟩
  · rw [hcard, hlab'_eq]
    rcases hD with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> norm_num
  · rw [hr, hlab'_eq]
    rcases hD with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
  · exact hZK lab' hPlab' hhas'

theorem ggQTwoDUnit_orthY_eq
    (hRig : GGLabelRigidInput) (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hbase : QTwoUnitBase p B Bs x L ψ ε) (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hdel : QTwoUnitDel Bs βL a b c α g b') (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (hD : (Even (m - 1) ∧ lab = ⟨.D, m - 1, 1⟩) ∨ (Odd (m - 1) ∧ lab = ⟨.twD, m - 1, 1⟩)) :
    ∃ Φ : OrthTorus.OrthFrameCore 3 Bs N, Nat.card Φ.F = 2 ∧ Φ.r = m - 1 ∧
      Subgroup.center ↥N = ⊥ := by
  have hstar : GGBstar 3 B Bs := hbase.p_eq ▸ hcfg.1.1.1.2.1
  have hinner : GGInnerDiagOn Bs N :=
    ggQTwoDUnit_innerDiag_N hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂
  have hnotle : ¬ (⁅N, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf 3 N :=
    qtwoDB17_not_centralizes hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂
  have hnotcent : x ∉ Subgroup.centralizer (N : Set G) := by
    intro hx
    have hNle : N ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcx : Commute x n := ((Subgroup.mem_centralizer_iff.mp hx) n hn).symm
      exact hcx.zpow_left k
    have hbot : (⁅N, Subgroup.zpowers x⁆ : Subgroup G) = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hNle
    exact hnotle (by rw [hbot]; exact bot_le)
  exact qtwoDB25_orthY_of hRig hstar.2.1 hstar.2.2.2 hinner hbase.x_mem hnotcent hΛ hlab
    (by rcases hD with ⟨he, h⟩ | ⟨ho, h⟩
        · exact Or.inl ⟨he, by omega, h⟩
        · exact Or.inr ⟨ho, by omega, h⟩)

end CFSG.StandardType.QTwo

end
