module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheckCl
public import CFSG.LocalAnalysis.StandardType.GGSporKRestKeyLink

public section

namespace CFSG.StandardType.SporadicShape

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem sporKRest_cover_of_actionClK {K : Type} [Group K] [Finite K] {n : ℕ} [MulAction K (Fin n)]
    (B : List ℕ)
    (hbase : ∀ g : K, (∀ i ∈ B, ∀ h : i < n, g • (⟨i, h⟩ : Fin n) = ⟨i, h⟩) → g = 1) (a b : K)
    (α β : Perm (Fin n)) (ha : ∀ i : Fin n, a • i = α i) (hb : ∀ i : Fin n, b • i = β i)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (m : ℕ)
    (d : PermCover.Data) (hcheck : PermCover.checkClMatK B α β (p ^ m) d = true)
    (hcomplete : ∀ s : K, orderOf s = p →
      ∃ c ∈ d.classes, IsConj (sporKRestEval [a, b] (sporKRestParse c.x)) s) :
    SporKRestCover p K := by
  have hfaith : ∀ g : K, (∀ i : Fin n, g • i = i) → g = 1 :=
    fun g hg => hbase g fun i _ h => hg ⟨i, h⟩
  have hφa : MulAction.toPermHom K (Fin n) a = α := Equiv.ext fun i => ha i
  have hφb : MulAction.toPermHom K (Fin n) b = β := Equiv.ext fun i => hb i
  have hB := sporKRest_isBase_of_action B hbase a b α β ha hb hab
  refine sporKRest_cover_of_classCheckK (MulAction.toPermHom K (Fin n))
    (sporKRest_toPermHom_injective hfaith) a b hab B ?_ hp m d ?_ hcomplete
  · rw [hφa, hφb]
    exact hB
  · rw [hφa, hφb]
    exact hcheck

theorem sporKRest_cover_of_tableClK {G : Type} [Group G] [Finite G] {n : ℕ} [MulAction G (Fin n)]
    (B : List ℕ)
    (hbase : ∀ g : G, (∀ i ∈ B, ∀ h : i < n, g • (⟨i, h⟩ : Fin n) = ⟨i, h⟩) → g = 1) (a b : G)
    (Ta Tb : Table) (ha : Rep n Ta a) (hb : Rep n Tb b) (hTa : PermCover.tablePermOK n Ta = true)
    (hTb : PermCover.tablePermOK n Tb = true) (hab : Subgroup.closure ({a, b} : Set G) = ⊤)
    {p : ℕ} (hp : p.Prime) (m : ℕ) (d : PermCover.Data)
    (hcheck : PermCover.checkClMatK B (PermCover.tablePerm n Ta) (PermCover.tablePerm n Tb) (p ^ m) d =
      true)
    (hcomplete : ∀ s : G, orderOf s = p →
      ∃ c ∈ d.classes, IsConj (sporKRestEval [a, b] (sporKRestParse c.x)) s) :
    SporKRestCover p G := by
  exact sporKRest_cover_of_actionClK B hbase a b (PermCover.tablePerm n Ta)
    (PermCover.tablePerm n Tb) (sporKRest_smul_eq_tablePerm ha hTa)
    (sporKRest_smul_eq_tablePerm hb hTb) hab hp m d hcheck hcomplete

end CFSG.StandardType.SporadicShape
