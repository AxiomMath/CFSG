module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheckKey
public import CFSG.LocalAnalysis.StandardType.GGSporKRestModelLink

public section

namespace CFSG.StandardType.SporadicShape

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem sporKRest_isBase_of_action {K : Type} [Group K] {n : ℕ} [MulAction K (Fin n)] (B : List ℕ)
    (hbase : ∀ g : K, (∀ i ∈ B, ∀ h : i < n, g • (⟨i, h⟩ : Fin n) = ⟨i, h⟩) → g = 1) (a b : K)
    (α β : Perm (Fin n)) (ha : ∀ i : Fin n, a • i = α i) (hb : ∀ i : Fin n, b • i = β i)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) :
    PermCover.IsBase B (Subgroup.closure ({α, β} : Set (Perm (Fin n)))) := by
  have hφa : MulAction.toPermHom K (Fin n) a = α := Equiv.ext fun i => ha i
  have hφb : MulAction.toPermHom K (Fin n) b = β := Equiv.ext fun i => hb i
  have hmap : (Subgroup.closure ({a, b} : Set K)).map (MulAction.toPermHom K (Fin n)) =
      Subgroup.closure ({α, β} : Set (Perm (Fin n))) := by
    rw [MonoidHom.map_closure, Set.image_pair, hφa, hφb]
  intro g hg hfix
  rw [← hmap, hab] at hg
  obtain ⟨x, _hx, rfl⟩ := Subgroup.mem_map.mp hg
  have hx1 : x = 1 := by
    apply hbase x
    intro i hi h
    have hh := hfix i hi h
    rwa [MulAction.toPermHom_apply, MulAction.toPerm_apply] at hh
  rw [hx1, map_one]

theorem sporKRest_cover_of_actionMatK {K : Type} [Group K] [Finite K] {n : ℕ} [MulAction K (Fin n)]
    (B : List ℕ)
    (hbase : ∀ g : K, (∀ i ∈ B, ∀ h : i < n, g • (⟨i, h⟩ : Fin n) = ⟨i, h⟩) → g = 1) (a b : K)
    (α β : Perm (Fin n)) (ha : ∀ i : Fin n, a • i = α i) (hb : ∀ i : Fin n, b • i = β i)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card K).factorization p) (d : PermCover.Data)
    (hcheck : PermCover.checkMatK B α β sylowOrder d = true) : SporKRestCover p K := by
  have hfaith : ∀ g : K, (∀ i : Fin n, g • i = i) → g = 1 :=
    fun g hg => hbase g fun i _ h => hg ⟨i, h⟩
  have hφa : MulAction.toPermHom K (Fin n) a = α := Equiv.ext fun i => ha i
  have hφb : MulAction.toPermHom K (Fin n) b = β := Equiv.ext fun i => hb i
  have hB := sporKRest_isBase_of_action B hbase a b α β ha hb hab
  refine sporKRest_cover_of_permModel (MulAction.toPermHom K (Fin n))
    (sporKRest_toPermHom_injective hfaith) a b hab hp sylowOrder hord d ?_
  rw [hφa, hφb]
  exact PermCover.check_of_spec (PermCover.checkMatK_sound hB hcheck)

theorem sporKRest_cover_of_actionPowMatK {K : Type} [Group K] [Finite K] {n : ℕ} [MulAction K (Fin n)]
    (B : List ℕ)
    (hbase : ∀ g : K, (∀ i ∈ B, ∀ h : i < n, g • (⟨i, h⟩ : Fin n) = ⟨i, h⟩) → g = 1) (a b : K)
    (α β : Perm (Fin n)) (ha : ∀ i : Fin n, a • i = α i) (hb : ∀ i : Fin n, b • i = β i)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card K).factorization p) (d : PermCover.Data)
    (hcheck : PermCover.checkPowMatK B p α β sylowOrder d = true) : SporKRestCover p K := by
  have hfaith : ∀ g : K, (∀ i : Fin n, g • i = i) → g = 1 :=
    fun g hg => hbase g fun i _ h => hg ⟨i, h⟩
  have hφa : MulAction.toPermHom K (Fin n) a = α := Equiv.ext fun i => ha i
  have hφb : MulAction.toPermHom K (Fin n) b = β := Equiv.ext fun i => hb i
  have hB := sporKRest_isBase_of_action B hbase a b α β ha hb hab
  refine sporKRest_cover_of_permModelPow (MulAction.toPermHom K (Fin n))
    (sporKRest_toPermHom_injective hfaith) a b hab hp sylowOrder hord d ?_
  rw [hφa, hφb]
  exact PermCover.checkPow_of_spec (PermCover.checkPowMatK_sound hB hcheck)

theorem sporKRest_cover_of_actionEMatK {K : Type} [Group K] [Finite K] {n : ℕ} [MulAction K (Fin n)]
    (B : List ℕ)
    (hbase : ∀ g : K, (∀ i ∈ B, ∀ h : i < n, g • (⟨i, h⟩ : Fin n) = ⟨i, h⟩) → g = 1) (a b : K)
    (α β : Perm (Fin n)) (ha : ∀ i : Fin n, a • i = α i) (hb : ∀ i : Fin n, b • i = β i)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card K).factorization p) (d : PermCover.DataE)
    (hcheck : PermCover.checkEMatK B p α β sylowOrder d = true) : SporKRestCover p K := by
  have hfaith : ∀ g : K, (∀ i : Fin n, g • i = i) → g = 1 :=
    fun g hg => hbase g fun i _ h => hg ⟨i, h⟩
  have hφa : MulAction.toPermHom K (Fin n) a = α := Equiv.ext fun i => ha i
  have hφb : MulAction.toPermHom K (Fin n) b = β := Equiv.ext fun i => hb i
  have hB := sporKRest_isBase_of_action B hbase a b α β ha hb hab
  refine sporKRest_cover_of_permModelE (MulAction.toPermHom K (Fin n))
    (sporKRest_toPermHom_injective hfaith) a b hab hp sylowOrder hord d ?_
  rw [hφa, hφb]
  exact PermCover.checkE_of_spec (PermCover.checkEMatK_sound hB hcheck)

theorem sporKRest_cover_of_tableMatK {G : Type} [Group G] [Finite G] {n : ℕ} [MulAction G (Fin n)]
    (B : List ℕ)
    (hbase : ∀ g : G, (∀ i ∈ B, ∀ h : i < n, g • (⟨i, h⟩ : Fin n) = ⟨i, h⟩) → g = 1) (a b : G)
    (Ta Tb : Table) (ha : Rep n Ta a) (hb : Rep n Tb b) (hTa : PermCover.tablePermOK n Ta = true)
    (hTb : PermCover.tablePermOK n Tb = true) (hab : Subgroup.closure ({a, b} : Set G) = ⊤)
    {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card G).factorization p) (d : PermCover.Data)
    (hcheck : PermCover.checkMatK B (PermCover.tablePerm n Ta) (PermCover.tablePerm n Tb) sylowOrder d =
      true) : SporKRestCover p G := by
  exact sporKRest_cover_of_actionMatK B hbase a b (PermCover.tablePerm n Ta) (PermCover.tablePerm n Tb)
    (sporKRest_smul_eq_tablePerm ha hTa) (sporKRest_smul_eq_tablePerm hb hTb) hab hp sylowOrder hord d
    hcheck

theorem sporKRest_cover_of_tablePowMatK {G : Type} [Group G] [Finite G] {n : ℕ} [MulAction G (Fin n)]
    (B : List ℕ)
    (hbase : ∀ g : G, (∀ i ∈ B, ∀ h : i < n, g • (⟨i, h⟩ : Fin n) = ⟨i, h⟩) → g = 1) (a b : G)
    (Ta Tb : Table) (ha : Rep n Ta a) (hb : Rep n Tb b) (hTa : PermCover.tablePermOK n Ta = true)
    (hTb : PermCover.tablePermOK n Tb = true) (hab : Subgroup.closure ({a, b} : Set G) = ⊤)
    {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card G).factorization p) (d : PermCover.Data)
    (hcheck : PermCover.checkPowMatK B p (PermCover.tablePerm n Ta) (PermCover.tablePerm n Tb)
      sylowOrder d = true) : SporKRestCover p G := by
  exact sporKRest_cover_of_actionPowMatK B hbase a b (PermCover.tablePerm n Ta) (PermCover.tablePerm n Tb)
    (sporKRest_smul_eq_tablePerm ha hTa) (sporKRest_smul_eq_tablePerm hb hTb) hab hp sylowOrder hord d
    hcheck

theorem sporKRest_cover_of_tableEMatK {G : Type} [Group G] [Finite G] {n : ℕ} [MulAction G (Fin n)]
    (B : List ℕ)
    (hbase : ∀ g : G, (∀ i ∈ B, ∀ h : i < n, g • (⟨i, h⟩ : Fin n) = ⟨i, h⟩) → g = 1) (a b : G)
    (Ta Tb : Table) (ha : Rep n Ta a) (hb : Rep n Tb b) (hTa : PermCover.tablePermOK n Ta = true)
    (hTb : PermCover.tablePermOK n Tb = true) (hab : Subgroup.closure ({a, b} : Set G) = ⊤)
    {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card G).factorization p) (d : PermCover.DataE)
    (hcheck : PermCover.checkEMatK B p (PermCover.tablePerm n Ta) (PermCover.tablePerm n Tb)
      sylowOrder d = true) : SporKRestCover p G := by
  exact sporKRest_cover_of_actionEMatK B hbase a b (PermCover.tablePerm n Ta) (PermCover.tablePerm n Tb)
    (sporKRest_smul_eq_tablePerm ha hTa) (sporKRest_smul_eq_tablePerm hb hTb) hab hp sylowOrder hord d
    hcheck

end CFSG.StandardType.SporadicShape
