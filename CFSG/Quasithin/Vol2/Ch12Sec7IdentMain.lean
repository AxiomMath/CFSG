module

public import CFSG.Quasithin.Vol2.Ch12Sec7Orb
public import CFSG.Quasithin.Vol2.Ch12Sec7IdentA

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Blueprint CFSG.Quasithin Subgroup

@[expose] def Struct1277 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    ∀ t ∈ V, (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
      ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) →
        ∀ z ∈ V, (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 → StructAt G z

@[expose] def VInter1277 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    ∀ z ∈ V, ∀ t ∈ V,
      (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 →
      (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
      (∀ v ∈ V, v ≠ 1 → (∃ l ∈ L, l * v * l⁻¹ = z) ∨ (∃ l ∈ L, l * v * l⁻¹ = t)) →
      ∀ W : Subgroup G, W ≤ V → z ∈ W → Nat.card W = 16 →
        ∃ l ∈ L, l⁻¹ * z * l ∈ W ∧ l⁻¹ * z * l ≠ z

@[expose] def Ygen {G : Type} [Group G] (L U : Subgroup G) (z : G) : Subgroup G :=
  Subgroup.closure
    (((Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) :
        Set G) ∪
      ((Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) :
        Set G))

theorem L1_of (h1222 : Stmt12_2_2) (G : Type) [Group G] [Finite G] (T L V : Subgroup G)
    (h : Hyp1271 G T L V) :
    ∃ z ∈ V, z ≠ 1 ∧ T ≤ Subgroup.centralizer ({z} : Set G) ∧
      (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 := by
  obtain ⟨z, hz, hz1, hTz, -, -, -, hz45, -, -⟩ := S127.lemma12_7_4_part1_of h1222 h
  exact ⟨z, (Subgroup.mem_inf.mp hz).1, hz1, hTz, hz45⟩

theorem theoremA_of_struct (h1222 : Stmt12_2_2) (hS : Struct1277) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
      ∀ t ∈ V, (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
        ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) →
          ∀ z ∈ V, (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 →
            Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃*
              ↥(Subgroup.centralizer
                ({Quasithin.H13.transvection15} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))) := by
  intro G _ _ T L V h t ht h18 hGt z hzV hz45
  obtain ⟨hcomm, hV64, -⟩ := S127.card_eq_of_1222 h1222 h
  have hVel : IsElemAbelian 2 V := ⟨hcomm, fun x hx => S127.sq_eq_one_of_mem h.hyp hx⟩
  have hz1 : z ≠ 1 := S127.ne_one_of_relIndex hz45 (by norm_num)
  exact centralizer_iso_transvection_of_structAt hVel hV64 hzV hz1
    (hS G T L V h t ht h18 hGt z hzV hz45)

theorem ident1277_of_struct (h1222 : Stmt12_2_2) (hS : Struct1277) (hVI : VInter1277) :
    Ident1277 := by
  intro G _ _ T L V h t ht h18 hGt
  obtain ⟨z, hzV, t₀, ht₀V, hz45, ht18, horb⟩ := lemma12_7_4_one_of_1222 h1222 G T L V h
  obtain ⟨hcomm, hV64, -⟩ := S127.card_eq_of_1222 h1222 h
  have hVel : IsElemAbelian 2 V := ⟨hcomm, fun x hx => S127.sq_eq_one_of_mem h.hyp hx⟩
  have hz1 : z ≠ 1 := S127.ne_one_of_relIndex hz45 (by norm_num)
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by simpa using hVel.2 z hzV) hz1
  have hSz := hS G T L V h t ht h18 hGt z hzV hz45
  have hSz' := hSz
  obtain ⟨-, -, -, -, A, B, -, -, -, -, hAB, hAB', -, -⟩ := hSz'
  have hzP : z ∈ pCoreOf 2 (Gz z) := by
    have hzA : z ∈ A ⊓ B := by
      rw [hAB']
      exact Subgroup.mem_zpowers z
    rw [← hAB]
    exact (le_sup_left : A ≤ A ⊔ B) hzA.1
  have hzW : z ∈ pCoreOf 2 (Gz z) ⊓ V := ⟨hzP, hzV⟩
  have hW := card_pCore_inf_eq hVel hV64 hzV hz2 hSz
  obtain ⟨l, -, hlW, hlne⟩ := hVI G T L V h z hzV t₀ ht₀V hz45 ht18 horb
    (pCoreOf 2 (Gz z) ⊓ V) inf_le_right hzW hW
  exact ⟨z, hz2, centralizer_iso_transvection_of_structAt hVel hV64 hzV hz1 hSz, l,
    (inf_le_left : pCoreOf 2 (Gz z) ⊓ V ≤ pCoreOf 2 (Gz z)) hlW, hlne⟩

end CFSG.Quasithin.H13.I1277
