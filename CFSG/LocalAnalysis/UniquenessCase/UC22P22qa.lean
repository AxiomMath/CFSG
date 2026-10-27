module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qw
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22n
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.LocalAnalysis.UniquenessCase.UC6Grp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

@[expose] def R6_11 (D : Data G) : Prop :=
  3 ∈ D.sig3 → ∀ P : Subgroup G, IsSylowOf 3 P D.M →
    Nonempty (↥P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) ∧
    (Group.IsSolvable ↥D.M ∧ rankThreeGamma 1 3 (thompsonSubgroup P) ≤ D.M) ∧
    CFSG.IsStronglyClosedIn P ((thompsonSubgroup P : Subgroup G) : Set G) ∧
    (∀ Y : Subgroup G, Y ≤ thompsonSubgroup P → Y ≠ ⊥ → InU D.M Y) ∧
    (∀ Q : Subgroup G, IsSylowOf 2 Q (rankThreePrimeCore 3 D.M) → P ≤ normalizer (Q : Set G) →
      ∀ S : Subgroup G, S ≤ Q → IsMulCommutative S → P ≤ normalizer (S : Set G) →
        ∀ b ∈ (Subgroup.upperCentralSeries ↥P 2).map P.subtype, ∀ s ∈ S, b * s = s * b) ∧
    (∀ X Q : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ thompsonSubgroup P →
      IsSylowOf 2 Q (rankThreePrimeCore 3 D.M) → P ≤ normalizer (Q : Set G) →
      ∃ n : ℕ, 1 ≤ n ∧ rankThreeIsQ8CentralCyclic (Q ⊓ centralizer (X : Set G)) n ∧
        Nonempty (↥⁅Q ⊓ centralizer (X : Set G), (Subgroup.center ↥P).map P.subtype⁆ ≃*
          QuaternionGroup 2) ∧
        IsCyclic ↥(Q ⊓ centralizer (X : Set G) ⊓ centralizer (((Subgroup.center ↥P).map P.subtype :
          Subgroup G) : Set G)) ∧
        Nat.card ↥(Q ⊓ centralizer (X : Set G) ⊓ centralizer (((Subgroup.center ↥P).map P.subtype :
          Subgroup G) : Set G)) = 2 ^ n)

@[expose] def R6_11Used (D : Data G) : Prop :=
  3 ∈ D.sig3 → ∀ P : Subgroup G, IsSylowOf 3 P D.M →
    Nonempty (↥P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) ∧
    (Group.IsSolvable ↥D.M ∧ rankThreeGamma 1 3 (thompsonSubgroup P) ≤ D.M) ∧
    (∀ Y : Subgroup G, Y ≤ thompsonSubgroup P → Y ≠ ⊥ → InU D.M Y) ∧
    (∀ Q : Subgroup G, IsSylowOf 2 Q (rankThreePrimeCore 3 D.M) → P ≤ normalizer (Q : Set G) →
      ∀ S : Subgroup G, S ≤ Q → IsMulCommutative S → P ≤ normalizer (S : Set G) →
        ∀ b ∈ (Subgroup.upperCentralSeries ↥P 2).map P.subtype, ∀ s ∈ S, b * s = s * b) ∧
    (∀ X Q : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ thompsonSubgroup P →
      IsSylowOf 2 Q (rankThreePrimeCore 3 D.M) → P ≤ normalizer (Q : Set G) →
      ∃ n : ℕ, 1 ≤ n ∧ rankThreeIsQ8CentralCyclic (Q ⊓ centralizer (X : Set G)) n ∧
        Nonempty (↥⁅Q ⊓ centralizer (X : Set G), (Subgroup.center ↥P).map P.subtype⁆ ≃*
          QuaternionGroup 2) ∧
        IsCyclic ↥(Q ⊓ centralizer (X : Set G) ⊓ centralizer (((Subgroup.center ↥P).map P.subtype :
          Subgroup G) : Set G)) ∧
        Nat.card ↥(Q ⊓ centralizer (X : Set G) ⊓ centralizer (((Subgroup.center ↥P).map P.subtype :
          Subgroup G) : Set G)) = 2 ^ n)

theorem r6_11Used_of_r6_11 {D : Data G} (h : R6_11 D) : R6_11Used D := fun h3 P hP => by
  obtain ⟨h0, h1, -, h3', h5, h4⟩ := h h3 P hP
  exact ⟨h0, h1, h3', h5, h4⟩


theorem uc22p22q_center_le_thompson (P : Subgroup G) :
    (Subgroup.center ↥P).map P.subtype ≤ thompsonSubgroup P := by
  classical
  have hfin : {A : Subgroup G | A ≤ P ∧ IsMulCommutative A}.Finite := Set.toFinite _
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image hfin.toFinset (fun A : Subgroup G => Nat.card A)
    ⟨⊥, (Set.Finite.mem_toFinset hfin).2 ⟨bot_le, inferInstance⟩⟩
  have hAmem : A ≤ P ∧ IsMulCommutative A := by simpa [Set.Finite.mem_toFinset] using hA
  have hAmax : ∀ B : Subgroup G, B ≤ P → IsMulCommutative B → Nat.card B ≤ Nat.card A := by
    intro B hB hBc
    exact hmax B (by simpa [Set.Finite.mem_toFinset] using ⟨hB, hBc⟩)
  have hfam : A ∈ CFSG.ambientMaxCardAbelianFamily P := ⟨hAmem.1, hAmem.2, hAmax⟩
  rintro _ ⟨z, hz, rfl⟩
  have hzc : ∀ y ∈ P, y * (z : G) = (z : G) * y := fun y hy =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨y, hy⟩)
  have hcomm : ∀ x ∈ A, ∀ y ∈ zpowers (z : G), x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute x (z : G) := hzc x (hAmem.1 hx)
    exact (hc.zpow_right n).eq
  have hB : IsMulCommutative (A ⊔ zpowers (z : G) : Subgroup G) := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨x₁, hx₁, y₁, hy₁, h₁⟩ := exists_mul_of_mem_sup_of_commute hcomm a.2
    obtain ⟨x₂, hx₂, y₂, hy₂, h₂⟩ := exists_mul_of_mem_sup_of_commute hcomm b.2
    have hxx : x₁ * x₂ = x₂ * x₁ := hAmem.2.is_comm.comm ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ |> congrArg Subtype.val
    have hyy : y₁ * y₂ = y₂ * y₁ := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy₁
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy₂
      exact ((Commute.refl (z : G)).zpow_zpow m n).eq
    show (a : G) * b = b * a
    rw [h₁, h₂]
    calc x₁ * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
      _ = x₁ * (x₂ * y₁) * y₂ := by rw [← hcomm x₂ hx₂ y₁ hy₁]
      _ = (x₁ * x₂) * (y₁ * y₂) := by group
      _ = (x₂ * x₁) * (y₂ * y₁) := by rw [hxx, hyy]
      _ = x₂ * (x₁ * y₂) * y₁ := by group
      _ = x₂ * (y₂ * x₁) * y₁ := by rw [hcomm x₁ hx₁ y₂ hy₂]
      _ = x₂ * y₂ * (x₁ * y₁) := by group
  have hBP : A ⊔ zpowers (z : G) ≤ P := sup_le hAmem.1 (zpowers_le.2 z.2)
  have hle : Nat.card ↥(A ⊔ zpowers (z : G)) ≤ Nat.card ↥A := hAmax _ hBP hB
  have hAB : A = A ⊔ zpowers (z : G) :=
    Subgroup.eq_of_le_of_card_ge le_sup_left hle
  have hzA : (z : G) ∈ A := by
    rw [hAB]
    exact mem_sup_right (mem_zpowers _)
  exact CFSG.le_ambientMaxCardThompson hfam hzA


theorem uc22p22q_isSylowOf_of_fusion {p : ℕ} [Fact p.Prime] {S H : Subgroup G}
    (h : fusionIsSylowIn p S H) : IsSylowOf p S H := by
  obtain ⟨P, hP⟩ := (fusionIsSylowIn_iff.1 h).2
  exact ⟨P, by rw [hP]; exact Subgroup.map_subgroupOf_eq_of_le h.1⟩

theorem uc22p22q_exists_Q {M P V : Subgroup G} (hP3 : IsPGroup 3 P) (hPM : P ≤ M)
    (hVM : M ≤ normalizer (V : Set G)) (hVMle : V ≤ M) (hV2 : IsPGroup 2 V) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q (rankThreePrimeCore 3 M) ∧ P ≤ normalizer (Q : Set G) ∧ V ≤ Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV3 : V ≤ rankThreePrimeCore 3 M := by
    refine le_sSup ⟨hVMle, ?_, ?_⟩
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hVMle).2 hVM
    · obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hV2
      rw [hk]
      exact Nat.Coprime.pow_right k (by norm_num)
  have hcop : ¬ 3 ∣ Nat.card ↥(rankThreePrimeCore 3 M) := fun hd =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
        Nat.prime_three M) hd |>.elim
  have hPN : P ≤ normalizer ((rankThreePrimeCore 3 M : Subgroup G) : Set G) :=
    hPM.trans <| (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le M)).1
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        Nat.prime_three M)
  obtain ⟨S, hS, hVS, hPS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    (r := 3) (q := 2) Nat.prime_three Nat.prime_two hP3 hcop hPN hV3 hV2 (hPM.trans hVM)
  exact ⟨S, uc22p22q_isSylowOf_of_fusion hS, hPS, hVS⟩


end CFSG.LocalAnalysis.UniquenessCase.UC6

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22q_r111_of (D : Data G) (hstd : Sigma23Std D) (h61 : UC6.R6_1 D) (h611 : UC6.R6_11Used D) :
    F11.R111 D := by
  intro V₀ V hH
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV : InCalV D.M V := by
    rcases hH.1 with h | h
    · exact h.2.1
    · exact h.2.1.1
  have hTI : ¬ IsTI V := hH.2.1
  apply Set.eq_empty_of_forall_notMem
  intro q hq
  have hq3 : q = 3 := hstd.sig3_sub hq
  subst hq3
  have h3sig : 3 ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inr hq
  obtain ⟨P, hP⟩ := exists_isSylowOf 3 D.M
  obtain ⟨hshape, -, -, h5, -⟩ := h611 hq P hP
  obtain ⟨e⟩ := hshape
  obtain ⟨Q, hQ, hPQ, hVQ⟩ := UC6.uc22p22q_exists_Q hP.isPGroup hP.le hV.2.2.1
    hV.2.1 (uc22p22e_isPGroup_of_elem hV.2.2.2)
  have hPV : P ≤ normalizer (V : Set G) := hP.le.trans hV.2.2.1
  have hcent := h5 Q hQ hPQ V hVQ hV.2.2.2.1 hPV
  obtain ⟨B, hB, hBp, hBc⟩ := uc22p22q_wreath_Z2 e
  have hBP : B ≤ P := hB.trans (by rintro _ ⟨x, -, rfl⟩; exact x.2)
  exact hTI (uc22p22n_isTI_of_noncyclic D h61 h3sig hV (hBP.trans hP.le) hBp hBc
    (fun b hb => by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hcent b (hB hb) v hv).symm))

end CFSG.LocalAnalysis.UniquenessCase.UC22
