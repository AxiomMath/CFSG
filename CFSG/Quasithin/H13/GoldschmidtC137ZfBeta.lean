module

public import CFSG.Quasithin.H13.GoldschmidtC137KMod1
public import CFSG.Quasithin.Background.S1549DA6Dict
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.B3 CFSG.Quasithin.S143
open scoped IsMulCommutative

theorem exists_hom_of_realizes {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {Z : Subgroup W} {π : ↥(alternatingGroup (Fin 6)) →* ↥H}
    (h : (FFModel.altDn 6).RealizesVia H ⊤ Z π) :
    ∃ β : W →* Mod.V 6 Mod.ut0, Function.Surjective β ∧ (∀ w, β w = 1 ↔ w ∈ Z) ∧
      ∀ (γ : ↥(alternatingGroup (Fin 6))) (w : W),
        β (((π γ : ↥H) : MulAut W) w) = Mod.act 6 Mod.ut0 γ.1 (β w) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  let e : (FFModel.symDn 6).Mod ≃* Mod.V 6 Mod.ut0 := S1549D.psiN6.trans n6ModEquiv
  let e₁ : W →* (FFModel.symDn 6).Mod := β.comp Subgroup.topEquiv.symm.toMonoidHom
  refine ⟨e.toMonoidHom.comp e₁, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨x, rfl⟩ := e.surjective q
    obtain ⟨u, rfl⟩ := hβs x
    exact ⟨(u : W), rfl⟩
  · intro w
    exact (MulEquiv.map_eq_one_iff e).trans (hβk ⟨w, trivial⟩)
  · intro γ w
    obtain ⟨m₀, hm⟩ : ∃ m₀ : ↥(G6.coreMod 6),
        (QuotientGroup.mk m₀ : (FFModel.symDn 6).Mod) = β ⟨w, trivial⟩ :=
      QuotientGroup.mk_surjective _
    have hact : G6.permAct 6 (γ : Equiv.Perm (Fin 6)) (m₀ : G6.PermMod 6) ∈ G6.coreMod 6 :=
      G6.permAct_mem_coreMod (γ : Equiv.Perm (Fin 6)) m₀.2
    have h1 : β ⟨((π γ : ↥H) : MulAut W) w, trivial⟩ =
        (QuotientGroup.mk ⟨G6.permAct 6 (γ : Equiv.Perm (Fin 6)) (m₀ : G6.PermMod 6), hact⟩ :
          (FFModel.symDn 6).Mod) :=
      hβe γ ⟨w, trivial⟩ m₀ trivial hact hm.symm
    have h2 : S1549D.psiN6 (β ⟨((π γ : ↥H) : MulAut W) w, trivial⟩) =
        n6Act γ.1 (S1549D.psiN6 (β ⟨w, trivial⟩)) := by
      rw [h1, ← hm]
      exact S1549D.n6Rep_permAct (γ : Equiv.Perm (Fin 6)) m₀
    show n6ModEquiv (S1549D.psiN6 (β ⟨((π γ : ↥H) : MulAut W) w, trivial⟩)) =
      Mod.act 6 Mod.ut0 γ.1 (n6ModEquiv (S1549D.psiN6 (β ⟨w, trivial⟩)))
    rw [h2]
    exact n6ToV_act_perm γ.1 _

variable {G : Type} [Group G]

theorem exists_beta_of_natural_Z {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hnat : ∃ _ : IsMulCommutative ↥V, AlternatingNatural (V := ↥V) (autOn L V) ⊤
      ((centralizer (L : Set G)).subgroupOf V) 6) :
    ∃ (π : LG 6 →* ↥(autI hV L)) (β : IntMod V hV →* Mod.V 6 Mod.ut0),
      Function.Surjective π ∧ Function.Surjective β ∧
      (∀ v, β v = 1 ↔ v.val ∈ centralizer (L : Set G)) ∧
      ∀ (γ : LG 6) (v : IntMod V hV),
        β (((π γ : ↥(autI hV L)) : MulAut (IntMod V hV)) v) = Mod.act 6 Mod.ut0 γ.1 (β v) := by
  obtain ⟨hc, π, hπ⟩ := hnat
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_hom_of_realizes hπ
  exact ⟨π, β, hπ.1, hβs, fun v => (hβk v).trans Subgroup.mem_subgroupOf, hβe⟩

end CFSG.Quasithin.H13.U3.GC137
