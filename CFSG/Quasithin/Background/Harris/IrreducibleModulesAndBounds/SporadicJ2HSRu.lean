module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.AutRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuMain

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem j2_autRank :
    ∀ B : Subgroup (MulAut (NativeSporadic.Carrier .J2)),
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 4 := by
  obtain ⟨Φ, -⟩ := CFSG.QuasithinUnique.Bridge.J2Excl.j2_aut_model
  exact CFSG.QuasithinUnique.Setup.X1.rank_of_equiv Φ
    CFSG.QuasithinUnique.Bridge.J2Excl.j2_rank_R

theorem false_of_J2
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .J2)) : False := by
  obtain ⟨e⟩ := hM
  exact false_of_cover_rank_dim h e
    (fun E _ _ _ π hπ hC hodd => CFSG.QuasithinUnique.Bridge.J2Excl.j2_cover E π hπ hC hodd)
    (r := 4) j2_autRank
    (ρ := 12) (fun W _ _ hW σ hσ => CFSG.QuasithinUnique.Bridge.J2Excl.j2_dim W hW σ hσ)
    (by norm_num)

theorem false_of_HS
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .HS)) : False := by
  obtain ⟨e⟩ := hM
  exact false_of_cover_rank_dim h e
    (fun E _ _ _ π hπ hC hodd => CFSG.QuasithinUnique.Bridge.HSExcl.hs_cover E π hπ hC hodd)
    (r := 6) CFSG.QuasithinUnique.Bridge.HSExcl.hs_rank
    (ρ := 20) (fun W _ _ hW σ hσ => CFSG.QuasithinUnique.Bridge.HSExcl.hs_dim W hW σ hσ)
    (by norm_num)

theorem false_of_Ru
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .Ru)) : False := by
  obtain ⟨e⟩ := hM
  exact false_of_cover_rank_dim h e
    (fun E _ _ _ π hπ hC hodd => CFSG.QuasithinUnique.Bridge.RuExcl.ru_cover E π hπ hC hodd)
    (r := 9) CFSG.QuasithinUnique.Bridge.RuExcl.ru_rank
    (ρ := 28) (fun W _ _ hW σ hσ => CFSG.QuasithinUnique.Bridge.RuExcl.ru_dim W hW σ hσ)
    (by norm_num)

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
