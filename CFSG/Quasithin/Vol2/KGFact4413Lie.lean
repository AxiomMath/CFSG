module

public import CFSG.Quasithin.Vol2.Ch4Sec4W4413
public import CFSG.Quasithin.Background.E2TwoCLie

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.A4
open scoped IsMulCommutative Pointwise

namespace Ch4

@[expose] def E22BorelFactsLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S MH : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    pCoreOf 2 H ≠ ⊥ → (∃ K ∈ cComp H, H = K ⊔ S ∧ E2.E22LieCases H S MH K) →
    QuasithinUnique.IsSylowTwoOf S H → IsUniqueMaxOver H S MH →
      (∃ P : Subgroup G, QuasithinUnique.IsSylowTwoOf P (MH ⊓ oTwoUpper H) ∧
        MH ⊓ oTwoUpper H ≤ Subgroup.normalizer (P : Set G)) ∧
      ∀ B : Subgroup G, B ≤ MH → Odd (Nat.card B) → (∃ k : ℕ, B.relIndex MH = 2 ^ k) →
        IsMulCommutative ↥B

@[expose] def Lemma4413NALie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S MH : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    pCoreOf 2 H ≠ ⊥ → (∃ K ∈ cComp H, H = K ⊔ S ∧ E2.E22LieCases H S MH K) →
    QuasithinUnique.IsSylowTwoOf S H → IsUniqueMaxOver H S MH →
      ∀ B : Subgroup G, B ≤ MH → Odd (Nat.card B) → (∃ k : ℕ, B.relIndex MH = 2 ^ k) →
        ∀ (p : ℕ) (A : Subgroup G), p.Prime → A ≤ B → IsElemAbelian p A →
          (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G) →
            ¬ H ⊓ Subgroup.normalizer (A : Set G) ≤ MH

end Ch4

@[expose] def Stmt4_4_13Lie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S MH : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    pCoreOf 2 H ≠ ⊥ → (∃ K ∈ cComp H, H = K ⊔ S ∧ E2.E22LieCases H S MH K) →
    QuasithinUnique.IsSylowTwoOf S H → IsUniqueMaxOver H S MH →
      (∃ P : Subgroup G, QuasithinUnique.IsSylowTwoOf P (MH ⊓ oTwoUpper H) ∧
        MH ⊓ oTwoUpper H ≤ Subgroup.normalizer (P : Set G)) ∧
      ∀ B : Subgroup G, B ≤ MH → Odd (Nat.card B) → (∃ k : ℕ, B.relIndex MH = 2 ^ k) →
        (∀ (p : ℕ) (A : Subgroup G), p.Prime → A ≤ B → IsElemAbelian p A →
          (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G) →
            H = MH ⊔ (H ⊓ Subgroup.normalizer (A : Set G)) ∧
              ¬ H ⊓ Subgroup.normalizer (A : Set G) ≤ MH) ∧
        ∀ M Mp : Subgroup G, quasithinIsMaxTwoLocal M → S ≤ M → MH = M ⊓ H →
          oTwoUpper Mp = Mp → Mp ≤ M → M ≤ Subgroup.normalizer (Mp : Set G) →
            {b | b ∈ B ∧ ∀ m ∈ Mp, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 Mp} * (S : Set G) =
              (S : Set G) * {b | b ∈ B ∧ ∀ m ∈ Mp, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 Mp}

open Ch4 in
theorem stmt4_4_13Lie_of (hE : E22BorelFactsLie) (hNA : Lemma4413NALie) : Stmt4_4_13Lie := by
  intro G _ _ H S MH hs hnab hK hO hn hS hU
  obtain ⟨h2cl, hab⟩ := hE G H S MH hs hnab hK hO hn hS hU
  refine ⟨h2cl, fun B hBM hBo hBi => ⟨fun p A hp hAB hAel hAS => ?_, ?_⟩⟩
  · have hna := hNA G H S MH hs hnab hK hO hn hS hU B hBM hBo hBi p A hp hAB hAel hAS
    exact ⟨Lemma4413.sup_eq hU inf_le_left hna, hna⟩
  ·
    intro M Mp hM hSM hMH hMp hMpM hMN
    have hBc : IsMulCommutative ↥B := hab B hBM hBo hBi
    obtain ⟨-, hSMH, -⟩ := isUniqueMaxOver_iff.mp hU
    have hSyl : IsSylowTwoOf S MH :=
      ⟨hSMH, hS.2.1, fun h => hS.2.2 (h.trans (by
        have := Subgroup.relIndex_mul_relIndex S MH H hSMH
          (isUniqueMaxOver_iff.mp hU).1.1.le
        exact Dvd.intro _ this))⟩
    have hBS : (B : Set G) * (S : Set G) = (S : Set G) * (B : Set G) := by
      obtain ⟨h1, h2⟩ := Lemma4413.mul_eq hBM hBo hBi hSyl
      rw [h1, h2]
    have hBMM : B ≤ M := hBM.trans (hMH ▸ inf_le_left)
    have hMO : M ≤ Subgroup.normalizer (pCoreOf 2 Mp : Set G) :=
      hMN.trans (normalizer_le_normalizer_pCoreOf 2 Mp)
    set D := B ⊓ centralizerSection M Mp (pCoreOf 2 Mp) with hD
    have hset : (D : Set G) = {b | b ∈ B ∧ ∀ m ∈ Mp, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 Mp} := by
      ext x
      constructor
      · rintro ⟨hxB, -, -, -, hx⟩
        refine ⟨hxB, fun m hm => ?_⟩
        have := (pCoreOf 2 Mp).inv_mem (hx m hm)
        have e : (m * x * m⁻¹ * x⁻¹)⁻¹ = x * m * x⁻¹ * m⁻¹ := by group
        rwa [e] at this
      · rintro ⟨hxB, hx⟩
        refine ⟨hxB, hBMM hxB, hMN (hBMM hxB), hMO (hBMM hxB), fun m hm => ?_⟩
        have := (pCoreOf 2 Mp).inv_mem (hx m hm)
        have e : (x * m * x⁻¹ * m⁻¹)⁻¹ = m * x * m⁻¹ * x⁻¹ := by group
        rwa [e] at this
    rw [← hset]
    have hS2 : IsPGroup 2 ↥S := hS.2.1
    have h444 := eq_commutator_sup_of_wielandt wielandtCoprimeProduct_holds hS2 hBo hBS
    have hBN : B ≤ Subgroup.normalizer ((pCoreOf 2 (S ⊔ B) : Subgroup G) : Set G) :=
      le_sup_right.trans (le_normalizer_pCoreOf 2 (S ⊔ B))
    refine coe_mul_comm_of_eq_sup h444 (fun d hd => mem_normalizer_commutator
        (hBN hd.1) (Subgroup.le_normalizer hd.1)) (fun x hx => ?_)
      (fun x hx => mem_normalizer_commutator
        (le_sup_left.trans (le_normalizer_pCoreOf 2 (S ⊔ B)) hx.1) hx.2)
    exact mem_normalizer_inf hx.2
      (le_normalizer_centralizerSection' hMN (hSM hx.1))

end CFSG.Quasithin.H13
