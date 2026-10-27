module

public import CFSG.Quasithin.H13.A6S1372L76N3e
public import CFSG.Quasithin.H13.A6S1372L76N3k
public import CFSG.Quasithin.H13.A6S1372L76N3d

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76N3

theorem ne_of_mem_not_mem {G : Type} [Group G] {A B : Subgroup G} {x : G} (hA : x ∈ A)
    (hB : x ∉ B) : A ≠ B := fun h => hB (h ▸ hA)

theorem inf_ne_left_of {G : Type} [Group G] {A B : Subgroup G} {x : G} (hA : x ∈ A)
    (hB : x ∉ B) : A ⊓ B ≠ A := fun h => hB (by rw [← h] at hA; exact hA.2)

theorem inf_ne_inf_of {G : Type} [Group G] {A B C : Subgroup G} {x : G} (hA : x ∈ A)
    (hB : x ∈ B) (hC : x ∉ C) : A ⊓ B ≠ A ⊓ C := fun h => hC (by
  have hx : x ∈ A ⊓ B := ⟨hA, hB⟩
  rw [h] at hx
  exact hx.2)

theorem not_mem_of_cube {G : Type} [Group G] {P : Subgroup G} (hP : IsPGroup 2 ↥P) {x : G}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : x ∉ P := by
  intro hx
  obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
  have hn' : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact hx1 (eq_one_of_pow_two_pow hn' hx3 (by decide))

end A6L76N3

theorem lem1376NThreeC3_of
    (h139 : Stmt13_3_9) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h1337 : Stmt13_3_7) :
    Lem1376NThreeC3 := by
  intro G _ _ T L V S hNS _ hhat hQ H hH hab _ K hK hL1K hSL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D⟩ := S.nonempty_c3Hom h139 h37 h38 h13315 h1356two hNS hhat hH hab hK hL1K hSL
  obtain ⟨hTE, hL2E, hEN, hD2a⟩ := D.d2a h13314 h13315 hhat hH hK
  have hCE : (K ⊔ T) ⊓ Subgroup.centralizer (S.V2 : Set G) ≤ S.e1C3 K := le_sup_right
  obtain ⟨E₁, hE₁⟩ : ∃ E : Subgroup G, E = S.e1C3 K := ⟨_, rfl⟩
  rw [← hE₁] at hTE hL2E hEN hD2a hCE
  obtain ⟨k₀, hk0K, hk0C, hk03, hk01, -, -⟩ := D.exists_k0 hH
  have hkL : (k₀ : G) ∉ Subgroup.normalizer (L : Set G) :=
    S.not_mem_normalizer_L_of_cube h1337 hhat hH k₀.2.1 hk0C hk03 hk01
  obtain ⟨ℓ, hℓL2, hℓ3, hℓz⟩ := S.exists_L2_three hhat
  have hcL1 : (S.cL1 hhat : G) ∈ S.L1 := S.cL1_mem hhat
  have hc3 : (S.cL1 hhat : G) ^ 3 = 1 := S.cL1_cube hhat
  have hcN : (S.cL1 hhat : G) ∉ Subgroup.normalizer (S.V2 : Set G) := S.cL1_not_mem_NV2 hhat
  have hKTH : K ⊔ T ≤ H := (D.KT_le hH).trans inf_le_left
  have hKTz : K ⊔ T ≤ Subgroup.centralizer ({S.z} : Set G) := hKTH.trans hH.2.1
  have hLTM : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer S.T_le_NL
  have hℓLT : ℓ ∈ L ⊔ T := Subgroup.mem_sup_left (oTwoRes_le _ hℓL2).1
  have hℓE : ℓ ∈ E₁ := hL2E hℓL2
  have hℓKT : ℓ ∉ K ⊔ T := fun h => hℓz (by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hKTz h)
    rw [this, mul_inv_cancel_right])
  have hℓ1 : ℓ ≠ 1 := fun h => hℓz (by rw [h]; group)
  have hcLT : (S.cL1 hhat : G) ∈ L ⊔ T := Subgroup.mem_sup_left (S.L1_le_L hcL1)
  have hcKT : (S.cL1 hhat : G) ∈ K ⊔ T := Subgroup.mem_sup_left (hL1K hcL1)
  have hcE : (S.cL1 hhat : G) ∉ E₁ := fun h => hcN (hEN h)
  have hc1 : (S.cL1 hhat : G) ≠ 1 := fun h => hcN (by rw [h]; exact Subgroup.one_mem _)
  have hkE : (k₀ : G) ∈ E₁ := hCE ⟨Subgroup.mem_sup_left hk0K, hk0C⟩
  have hkKT : (k₀ : G) ∈ K ⊔ T := Subgroup.mem_sup_left hk0K
  have hkLT : (k₀ : G) ∉ L ⊔ T := fun h => hkL (hLTM h)
  have hP2 : IsPGroup 2 ↥((L ⊔ T) ⊓ E₁ ⊓ (K ⊔ T)) := by
    refine (S.isPGroup_triple hhat hH).to_le ?_
    rintro x ⟨⟨hx1, hx2⟩, hx3⟩
    exact ⟨⟨hx1, hEN hx2⟩, hKTH hx3⟩
  have hTP : T ≤ (L ⊔ T) ⊓ E₁ ⊓ (K ⊔ T) := le_inf (le_inf le_sup_right hTE) le_sup_right
  have hℓP := A6L76N3.not_mem_of_cube hP2 hℓ3 hℓ1
  have hcP := A6L76N3.not_mem_of_cube hP2 hc3 hc1
  have hkP := A6L76N3.not_mem_of_cube hP2 hk03 hk01
  have hsylT : ∀ X : Subgroup G, T ≤ X → (L ⊔ T) ⊓ E₁ ⊓ (K ⊔ T) ≤ X →
      IsSylowTwoOf ((L ⊔ T) ⊓ E₁ ⊓ (K ⊔ T)) X := by
    intro X hTX hPX
    have hT := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTX
    exact ⟨hPX, hP2, fun hd => hT.2.2 (hd.trans (Subgroup.index_dvd_of_le fun x hx => hTP hx))⟩
  have hsys : IsDSystemIn .C3 ![L ⊔ T, E₁, K ⊔ T] := by
    refine isDSystemIn_C3_of _ (S.d1_LT hhat) hD2a (D.d2b hH) ?_ ?_ ?_ ?_ ?_ (Or.inr hQ)
    · intro i
      fin_cases i
      · exact hsylT (L ⊔ T) le_sup_right (inf_le_left.trans inf_le_left)
      · exact hsylT E₁ hTE (inf_le_left.trans inf_le_right)
      · exact hsylT (K ⊔ T) le_sup_right inf_le_right
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact A6L76N3.ne_of_mem_not_mem ⟨hℓLT, hℓE⟩ hℓP
      · exact A6L76N3.ne_of_mem_not_mem ⟨hcLT, hcKT⟩ hcP
      · exact A6L76N3.ne_of_mem_not_mem ⟨hℓE, hℓLT⟩ hℓP
      · exact absurd rfl hij
      · exact A6L76N3.ne_of_mem_not_mem ⟨hkE, hkKT⟩ hkP
      · exact A6L76N3.ne_of_mem_not_mem ⟨hcKT, hcLT⟩ hcP
      · exact A6L76N3.ne_of_mem_not_mem ⟨hkKT, hkE⟩ hkP
      · exact absurd rfl hij
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact A6L76N3.inf_ne_left_of hcLT hcE
      · exact A6L76N3.inf_ne_left_of hℓLT hℓKT
      · exact A6L76N3.inf_ne_left_of hkE hkLT
      · exact absurd rfl hij
      · exact A6L76N3.inf_ne_left_of hℓE hℓKT
      · exact A6L76N3.inf_ne_left_of hkKT hkLT
      · exact A6L76N3.inf_ne_left_of hcKT hcE
      · exact absurd rfl hij
    · intro i j k hij hik hjk
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        first
        | exact absurd rfl hij
        | exact absurd rfl hik
        | exact absurd rfl hjk
        | skip
      · exact A6L76N3.inf_ne_inf_of hℓLT hℓE hℓKT
      · exact A6L76N3.inf_ne_inf_of hcLT hcKT hcE
      · exact A6L76N3.inf_ne_inf_of hℓE hℓLT hℓKT
      · exact A6L76N3.inf_ne_inf_of hkE hkKT hkLT
      · exact A6L76N3.inf_ne_inf_of hcKT hcLT hcE
      · exact A6L76N3.inf_ne_inf_of hkKT hkE hkLT
    · intro N hNP hN
      exact S.d4_of h139 h37 h38 hH hK N (hP2.to_le hNP) (le_sup_left.trans (le_sup_left.trans hN))
        (le_sup_left.trans (le_sup_right.trans hN))
  exact A6L76N3.false_of_c3System hsys (orderOf_eq_prime S.z_sq S.z_ne_one)
    (Subgroup.mem_sup_right (S.V_le_T S.z_mem_V)) hKTz (D.seven_dvd hH)

theorem lem1376Full_of_l32
    (hL : Lem1376OddNCL32)
    (hF : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h139 : Stmt13_3_9) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h1337 : Stmt13_3_7) : Lem1376Full :=
  lem1376Full_of_l32_c3 hL (lem1376NThreeC3_of h139 h37 h38 h13314 h13315 h1356two h1337) hF h36
    h37 h38 h139 h13314 h13315 h1356two h1337

end CFSG.Quasithin.H13.A6
