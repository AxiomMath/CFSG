module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2PartTwoSzNat2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.QuasithinUnique.Setup.X7 CFSG.LieType.Ree CFSG.LieType.BorelTits
open CFSG.Quasithin.H13 CFSG.Blueprint CFSG.RankThree.GF2n.Tim81.Sec2

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83_partTwo_z1_natural
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ (e : oTwoQuot ↥(L1 ⊔ S) ≃* ↥(suzukiGroup a K)) (c : ℕ)
      (φ : Additive ↥(Z1 L1 L2 S) ≃+ (Fin 4 → K)),
      (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a K ∧
      ∀ (h : ↥(L1 ⊔ S)) (z w : ↥(Z1 L1 L2 S)), (w : G) = (h : G) * z * (h : G)⁻¹ →
        φ (Additive.ofMul w) = Matrix.mulVec
          ((((e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) h) : ↥(suzukiGroup a K)) :
            Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c))
          (φ (Additive.ofMul z)) := by
  obtain ⟨D⟩ := str83_partTwo_z1_main hF hB ha hSz hL2 hII hZ2 hJ hK
  exact ⟨D.e, D.c, D.φ, D.map_S, D.nat⟩

theorem str83_partTwo_z1_irreducible
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S)
    {Y : Subgroup G} (hYZ : Y ≤ Z1 L1 L2 S)
    (hYN : L1 ⊔ S ≤ Subgroup.normalizer (Y : Set G)) :
    Y = ⊥ ∨ Y = Z1 L1 L2 S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Type := GaloisField 2 (2 * a + 1)
  haveI : Field K := inferInstance
  haveI : Finite K := inferInstance
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  obtain ⟨D⟩ := str83_partTwo_z1_main (K := K) hF hB ha hSz hL2 hII hZ2 hJ hK
  exact D.irreducible Y hYZ hYN

theorem str83_partTwo_card_z1
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S) :
    Nat.card ↥(Z1 L1 L2 S) = 2 ^ (4 * (2 * a + 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Type := GaloisField 2 (2 * a + 1)
  haveI : Field K := inferInstance
  haveI : Finite K := inferInstance
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  obtain ⟨D⟩ := str83_partTwo_z1_main (K := K) hF hB ha hSz hL2 hII hZ2 hJ hK
  exact D.card

end CFSG.Quasithin.Stroth

end
