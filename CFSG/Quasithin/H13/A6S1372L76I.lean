module

public import CFSG.Quasithin.H13.A6S1372L76H

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76I

theorem conjAlt_injective {n : ℕ} (τ : Perm (Fin n)) : Function.Injective (A6L76C.conjAlt τ) :=
  fun a b h => by
    have := congrArg (A6L76C.conjAlt τ⁻¹) h
    rwa [A6L76C.conjAlt_conjAlt_inv, A6L76C.conjAlt_conjAlt_inv] at this

theorem e7_facts : A6L76.vecS 7 {4, 5} * A6L76.vecS 7 {4, 6} = A6L76.vecS 7 {5, 6} ∧
    A6L76.vecS 7 {4, 5} ∈ G6.coreMod 7 ∧ A6L76.vecS 7 {4, 6} ∈ G6.coreMod 7 ∧
    A6L76.vecS 7 {5, 6} ∈ G6.coreMod 7 ∧
    (A6L76E.cyc3 (4 : Fin 7) 6 5)⁻¹ 6 = 4 ∧ (A6L76E.cyc3 (4 : Fin 7) 6 5)⁻¹ 4 = 5 ∧
    (A6L76E.cyc3 (4 : Fin 7) 6 5)⁻¹ 5 = 6 := by
  refine ⟨by decide, G6.mem_coreMod.2 (by decide), G6.mem_coreMod.2 (by decide),
    G6.mem_coreMod.2 (by decide), by decide, by decide, by decide⟩

end A6L76I

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace Ctx76

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)] {n : ℕ}

@[expose] noncomputable def twist (C : S.Ctx76 H K (FFModel.altDn n)) (τ : Perm (Fin n)) :
    S.Ctx76 H K (FFModel.altDn n) :=
  { C with
    π := C.π.comp (A6L76C.conjAlt τ⁻¹)
    β := (A6L76C.twistQ τ).comp C.β
    hR := A6L76C.realizesBy_twist C.hR τ
    hπ := C.hπ.comp (A6L76I.conjAlt_injective τ⁻¹) }

theorem twist_βU (C : S.Ctx76 H K (FFModel.altDn n)) (τ : Perm (Fin n))
    (u : ↥(conjClosure S.V3 H)) : (C.twist τ).βU u = A6L76C.twistQ τ (C.βU u) := rfl

end Ctx76

theorem conj_V3_of_L1 {l v : G} (hl : l ∈ S.L1) (hv : v ∈ S.V3) :
    l * v * l⁻¹ ∈ S.V3 := by
  have h1 : l * v * l⁻¹ * v⁻¹ ∈ ⁅S.V3, S.L1⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hl hv
  rw [S.commutator_V3_L1] at h1
  have e : l * v * l⁻¹ = (l * v * l⁻¹ * v⁻¹) * v := by group
  rw [e]
  exact S.V3.mul_mem h1 hv

namespace Ctx76

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]

theorem not_wit_conj (h13314 : Stmt13_3_14)
    (C : S.Ctx76 H K (FFModel.altDn 7)) {m : G6.PermMod 7}
    (hm : m ∈ (FFModel.altDn 7).sec)
    (hxm : C.βU ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨m, hm⟩) {σ : Perm (Fin 7)}
    (hσ : Perm.sign σ = 1) (hW : A6L76E.WitOK 7 (G6.permAct 7 σ m)) : False := by
  obtain ⟨hE, ha, hb⟩ := hW
  obtain ⟨hs1, hs2⟩ := A6L76E.sign_wit 7 (G6.permAct 7 σ m)
  set a := (A6L76E.wit 7 (G6.permAct 7 σ m)).1
  set b := (A6L76E.wit 7 (G6.permAct 7 σ m)).2
  have hinv : G6.permAct 7 σ⁻¹ (G6.permAct 7 σ m) = m := by
    rw [← CFSG.Quasithin.permAct_mul_act, inv_mul_cancel, map_one, MulAut.one_apply]
  have ha' := A6L76H.fixCls_conj ha σ⁻¹
  have hb' := A6L76H.fixCls_conj hb σ⁻¹
  rw [hinv] at ha' hb'
  have hsa : Perm.sign (σ⁻¹ * a * σ⁻¹⁻¹) = 1 := by simp [hs1, hσ]
  have hsb : Perm.sign (σ⁻¹ * b * σ⁻¹⁻¹) = 1 := by simp [hs2, hσ]
  have hE' := hE.map (MulAut.conj σ⁻¹).toMonoidHom (MulAut.conj σ⁻¹).injective
  exact C.not_e9 h13314 hm hxm (a := ⟨_, Perm.mem_alternatingGroup.2 hsa⟩)
    (b := ⟨_, Perm.mem_alternatingGroup.2 hsb⟩) (A6L76H.e9_of_perm hE')
    ((A6L76C.act_mul_inv_mem_ker_iff hm _).2 ha') ((A6L76C.act_mul_inv_mem_ker_iff hm _).2 hb')

theorem classes7 (h13314 : Stmt13_3_14)
    (C : S.Ctx76 H K (FFModel.altDn 7)) {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgL : (g : G) ∈ S.L1) (hg : S.frame.ρ g = swap 0 1 * swap 1 2)
    {m : G6.PermMod 7} (hm : m ∈ (FFModel.altDn 7).sec)
    (hxm : C.βU ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨m, hm⟩) :
    (A6L76E.supp 7 m).length = 2 ∧
      (A6L76E.supp 7 (G6.permAct 7 (A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩)) m)).length = 2 ∧
      (A6L76E.supp 7 (m * G6.permAct 7 (A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩)) m)).length = 2 ∧
      m ≠ G6.permAct 7 (A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩)) m ∧
      m * G6.permAct 7 (A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩)) m =
        G6.permAct 7 (A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩) ^ 2) m := by
  obtain ⟨-, hmz⟩ := C.classes_odd A6L76H.sum_one_seven hgL hg hm hxm
  set γ := A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩) with hγ
  have hwt : ∀ σ : Perm (Fin 7), Perm.sign σ = 1 →
      (A6L76E.supp 7 (G6.permAct 7 σ m)).length = 2 := by
    intro σ hσ
    rcases A6L76E.check7 (G6.permAct 7 σ m) (G6.mem_coreMod.1 (G6.permAct_mem_coreMod _ hm))
      with h | h
    · exact (C.not_wit_conj h13314 hm hxm hσ h).elim
    · exact h
  have hγs : Perm.sign γ = 1 := A6L76C.permOf_sign _
  have hwm := hwt 1 (by simp)
  rw [map_one, MulAut.one_apply] at hwm
  have hwz := hwt (γ ^ 2) (by rw [map_pow, hγs, one_pow])
  rw [← hmz] at hwz
  refine ⟨hwm, hwt γ hγs, hwz, fun h => ?_, hmz⟩
  rw [← h, G6.permMod_mul_self] at hwz
  exact absurd hwz (by decide)

end Ctx76

end Setting4

end CFSG.Quasithin.H13.A6
