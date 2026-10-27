module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aB1Invariant
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aTauH0All
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aB1Irreducible
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aChainOnto
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aLift
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aCenEqNor
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aH0Gens

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.exists_Data_Mono (h : FF81Hyp b L) (hT : KF_Sp6Torus)
    (hTF : KF_Sp6TorusFree) (hOut : KF_Sp62Out)
    (hnoL : ∀ g : G, g * b * g⁻¹ ∉ L) :
    ∃ (b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G),
      b₁ ∈ L ∧ b₂ ∈ L ∧ b₃ ∈ L ∧
      IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)) ∧
      IsElemAb 3 4 (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) ∧
      Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ L ∧
      L ⊓ CenS (Subgroup.closure ({b₁, b₂, b₃} : Set G)) =
        Subgroup.closure ({b₁, b₂, b₃} : Set G) ∧
      (∀ n ∈ L, n ∈ Nor (Subgroup.closure ({b₁, b₂, b₃} : Set G)) →
        ∀ x ∈ ({b₁, b₂, b₃} : Set G),
          n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G)) ∧
      Subgroup.closure ({b, b₁, b₂, b₃} : Set G) ≤ Cen b ∧
      ι₁ ∈ L ∧ ι₂ ∈ L ∧ ι₃ ∈ L ∧ σ₁₂ ∈ L ∧ σ₂₃ ∈ L ∧ γ ∈ L ∧
      CFSG.RankThree.PartTwo.Sec21.FF81.Lift.Data b b₁ b₂ b₃ ∧
      CFSG.RankThree.PartTwo.Sec21.FF81.Lift.Mono b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ := by
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, hE, hself, hmono,
    ⟨n₁, hn₁, hn₁b₁, hn₁b₂, hn₁b₃⟩,
    ⟨n₂, hn₂, hn₂b₁, hn₂b₂, hn₂b₃⟩,
    ⟨n₃, hn₃, hn₃b₁, hn₃b₂, hn₃b₃⟩,
    ⟨n₂₃, hn₂₃, hn₂₃b₁, hn₂₃b₂, hn₂₃b₃⟩,
    ⟨n, hnL, hinv₁, hinv₂, hinv₃⟩, hconj, hrk, huniq, _hs⟩ :=
    hT G L h.model
  obtain ⟨t₁, s, c, ht₁X, hsX, hcX, ht₁, hs, hc⟩ :=
    h.exists_H0_generators_of_actions hn₁ hn₂ hn₃ hn₁b₁ hn₁b₂ hn₁b₃ hn₂b₁ hn₂b₂ hn₂b₃
      hn₃b₁ hn₃b₂ hn₃b₃ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  obtain ⟨τ, hτL, hτ2, hτb, hτ₁, hτ₂, hτ₃⟩ :=
    h.exists_inverting_involution_of_inverting hnL hE hself hinv₁ hinv₂ hinv₃
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  let B₁ : Subgroup G := Subgroup.closure ({b₁, b₂, b₃} : Set G)
  have hbB : b ∈ B := Subgroup.subset_closure (by simp)
  have hb₁B : b₁ ∈ B := Subgroup.subset_closure (by simp)
  have hb₂B : b₂ ∈ B := Subgroup.subset_closure (by simp)
  have hb₃B : b₃ ∈ B := Subgroup.subset_closure (by simp)
  have hB₁L : B₁ ≤ L := by
    refine (Subgroup.closure_le L).mpr ?_
    intro x hx
    rcases hx with rfl | rfl | rfl
    exacts [hb₁, hb₂, hb₃]
  have hτN : τ ∈ Nor B :=
    h.tau_mem_normalizer hτL hb₁ hb₂ hb₃ hE hτb ⟨hτ₁, hτ₂, hτ₃⟩
  let τX : MulAut ↥B := FF81X.tau hτN
  have hE4 : IsElemAb 3 4 B := h.isElemAb_B hE hB₁L
  have hBC : B ≤ Cen b := by
    rw [show B = Subgroup.zpowers b ⊔ B₁ from closure_four_eq b b₁ b₂ b₃]
    exact sup_le (Subgroup.zpowers_le.mpr (b_mem_cen b)) (hB₁L.trans h.hLC)
  have hB₁B : B₁ ≤ B := by
    rw [show B = Subgroup.zpowers b ⊔ B₁ from closure_four_eq b b₁ b₂ b₃]
    exact le_sup_right
  have hb₁ne : b₁ ≠ 1 := by
    intro h1
    obtain ⟨e, he₁, -, -⟩ := FF81Hyp.cubeMulEquiv h hb₁ hb₂ hb₃ hE
    have h0 : e ⟨b₁, Subgroup.subset_closure (by simp)⟩ = 1 := by
      rw [show (⟨b₁, Subgroup.subset_closure (by simp)⟩ :
          ↥(Subgroup.closure ({b₁, b₂, b₃} : Set G))) = 1 from Subtype.ext h1]
      simp
    rw [he₁] at h0
    have hz : (Pi.single (0 : Fin 3) (1 : ZMod 3) : Fin 3 → ZMod 3) = 0 := by
      simpa using congrArg Multiplicative.toAdd h0
    have hcoord := congrFun hz 0
    simpa using hcoord
  have hmove : ∃ σ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G)),
      σ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) ∧
      σ ⟨b, Subgroup.subset_closure (by simp)⟩ ∉
        Subgroup.zpowers (⟨b, Subgroup.subset_closure (by simp)⟩ :
          ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) := by
    obtain ⟨m, hm, hmb⟩ := h.exists_move hrk huniq hBC hE4 hbB hB₁B hconj
    refine ⟨Subgroup.normalizerMonoidHom (H := B) ⟨m, hm⟩, ?_, ?_⟩
    · rw [mem_FF81X_iff]
      exact ⟨⟨m, hm⟩, rfl⟩
    · intro hmem
      apply hmb
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hval : b ^ k = m * b * m⁻¹ := by
        have hcoe := congrArg (fun x : ↥B => (x : G)) hk
        simpa [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_zpow] using hcoe
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, hval⟩
  have hB1irr : ∀ U : Subgroup ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G)),
      U ≤ ((Subgroup.closure ({b₁, b₂, b₃} : Set G)).subgroupOf
        (Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) →
      (∀ σ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G)),
        σ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) →
        σ * FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hτb
          ⟨hτ₁, hτ₂, hτ₃⟩) =
          FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hτb
            ⟨hτ₁, hτ₂, hτ₃⟩) * σ →
        Subgroup.map σ U = U) →
      U = ⊥ ∨ U = ((Subgroup.closure ({b₁, b₂, b₃} : Set G)).subgroupOf
        (Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) := by
    intro U hUle hUinv
    by_cases hUbot : U = ⊥
    · exact Or.inl hUbot
    · right
      let H : Subgroup G := U.map B.subtype
      have hHle : H ≤ B₁ := by
        rintro x ⟨u, hu, rfl⟩
        exact Subgroup.mem_subgroupOf.mp (hUle hu)
      have hHne : H ≠ ⊥ := by
        intro hH
        apply hUbot
        apply Subgroup.map_injective B.subtype_injective
        have hH' : U.map B.subtype = ⊥ := by simpa [H] using hH
        rw [hH', Subgroup.map_bot]
      have hfixb : ∀ g ∈ L, g * b * g⁻¹ = b := by
        intro g hg
        have hc : Commute g b := Subgroup.mem_centralizer_singleton_iff.mp (h.hLC hg)
        rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
      have hnor₁ : n₁ ∈ Nor B := by
        refine mem_nor_of_gen (S := ({b, b₁, b₂, b₃} : Set G)) ?_
        intro x hx
        rcases hx with rfl | rfl | rfl | rfl
        · rw [hfixb n₁ hn₁]
          exact Subgroup.subset_closure (by simp)
        · rw [hn₁b₁]
          exact B.inv_mem (Subgroup.subset_closure (by simp))
        · rw [hn₁b₂]
          exact Subgroup.subset_closure (by simp)
        · rw [hn₁b₃]
          exact Subgroup.subset_closure (by simp)
      have hnor₂ : n₂ ∈ Nor B := by
        refine mem_nor_of_gen (S := ({b, b₁, b₂, b₃} : Set G)) ?_
        intro x hx
        rcases hx with rfl | rfl | rfl | rfl
        · rw [hfixb n₂ hn₂]
          exact Subgroup.subset_closure (by simp)
        · rw [hn₂b₁]
          exact Subgroup.subset_closure (by simp)
        · rw [hn₂b₂]
          exact Subgroup.subset_closure (by simp)
        · rw [hn₂b₃]
          exact Subgroup.subset_closure (by simp)
      have hnor₃ : n₃ ∈ Nor B := by
        refine mem_nor_of_gen (S := ({b, b₁, b₂, b₃} : Set G)) ?_
        intro x hx
        rcases hx with rfl | rfl | rfl | rfl
        · rw [hfixb n₃ hn₃]
          exact Subgroup.subset_closure (by simp)
        · rw [hn₃b₁]
          exact Subgroup.subset_closure (by simp)
        · rw [hn₃b₂]
          exact Subgroup.subset_closure (by simp)
        · rw [hn₃b₃]
          exact Subgroup.subset_closure (by simp)
      have hnor₂₃ : n₂₃ ∈ Nor B := by
        refine mem_nor_of_gen (S := ({b, b₁, b₂, b₃} : Set G)) ?_
        intro x hx
        rcases hx with rfl | rfl | rfl | rfl
        · rw [hfixb n₂₃ hn₂₃]
          exact Subgroup.subset_closure (by simp)
        · rw [hn₂₃b₁]
          exact Subgroup.subset_closure (by simp)
        · rw [hn₂₃b₂]
          exact Subgroup.subset_closure (by simp)
        · rw [hn₂₃b₃]
          exact Subgroup.subset_closure (by simp)
      let ι₂ : G := n₂ * n₁ * n₂⁻¹
      let ι₃ : G := n₂₃ * ι₂ * n₂₃⁻¹
      have hι₂N : ι₂ ∈ Nor B := by
        show n₂ * n₁ * n₂⁻¹ ∈ Nor B
        exact (Nor B).mul_mem ((Nor B).mul_mem hnor₂ hnor₁) ((Nor B).inv_mem hnor₂)
      have hι₃N : ι₃ ∈ Nor B := by
        show n₂₃ * ι₂ * n₂₃⁻¹ ∈ Nor B
        exact (Nor B).mul_mem ((Nor B).mul_mem hnor₂₃ hι₂N) ((Nor B).inv_mem hnor₂₃)
      have act : ∀ {g : G} (hgN : g ∈ Nor B) {x y : G} (hxB : x ∈ B) (hyB : y ∈ B) {ε : ℤ},
          g * x * g⁻¹ = y ^ ε →
          Subgroup.normalizerMonoidHom (H := B) ⟨g, hgN⟩ ⟨x, hxB⟩ =
            (⟨y, hyB⟩ : ↥B) ^ ε := by
        intro g hgN x y hxB hyB ε hxy
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_zpow]
        exact hxy
      let σ₁ : MulAut ↥B := Subgroup.normalizerMonoidHom (H := B) ⟨n₁, hnor₁⟩
      let σ₂ : MulAut ↥B := Subgroup.normalizerMonoidHom (H := B) ⟨n₂, hnor₂⟩
      let σ₃ : MulAut ↥B := Subgroup.normalizerMonoidHom (H := B) ⟨n₃, hnor₃⟩
      let σ₂₃ : MulAut ↥B := Subgroup.normalizerMonoidHom (H := B) ⟨n₂₃, hnor₂₃⟩
      have hσ₁X : σ₁ ∈ FF81X B := by
        rw [mem_FF81X_iff]
        exact ⟨⟨n₁, hnor₁⟩, rfl⟩
      have hσ₂X : σ₂ ∈ FF81X B := by
        rw [mem_FF81X_iff]
        exact ⟨⟨n₂, hnor₂⟩, rfl⟩
      have hσ₃X : σ₃ ∈ FF81X B := by
        rw [mem_FF81X_iff]
        exact ⟨⟨n₃, hnor₃⟩, rfl⟩
      have hσ₂₃X : σ₂₃ ∈ FF81X B := by
        rw [mem_FF81X_iff]
        exact ⟨⟨n₂₃, hnor₂₃⟩, rfl⟩
      have hc₁ : σ₁ * τX = τX * σ₁ := by
        refine FF81Hyp.monomial_le_cen_X_tau h hτL hb₁ hb₂ hb₃ hE hτ2 hτb
          ⟨hτ₁, hτ₂, hτ₃⟩ hbB hb₁B hb₂B hb₃B hσ₁X ?_ ?_ ?_ ?_
        · left
          simpa using act hnor₁ hbB hbB (ε := 1)
            (by simpa using hfixb n₁ hn₁)
        · refine ⟨0, -1, ?_⟩
          simpa using act hnor₁ hb₁B hb₁B (ε := -1) (by simpa using hn₁b₁)
        · refine ⟨1, 1, ?_⟩
          simpa using act hnor₁ hb₂B hb₂B (ε := 1) (by simpa using hn₁b₂)
        · refine ⟨2, 1, ?_⟩
          simpa using act hnor₁ hb₃B hb₃B (ε := 1) (by simpa using hn₁b₃)
      have hc₂ : σ₂ * τX = τX * σ₂ := by
        refine FF81Hyp.monomial_le_cen_X_tau h hτL hb₁ hb₂ hb₃ hE hτ2 hτb
          ⟨hτ₁, hτ₂, hτ₃⟩ hbB hb₁B hb₂B hb₃B hσ₂X ?_ ?_ ?_ ?_
        · left
          simpa using act hnor₂ hbB hbB (ε := 1)
            (by simpa using hfixb n₂ hn₂)
        · refine ⟨1, 1, ?_⟩
          simpa using act hnor₂ hb₁B hb₂B (ε := 1) (by simpa using hn₂b₁)
        · refine ⟨0, 1, ?_⟩
          simpa using act hnor₂ hb₂B hb₁B (ε := 1) (by simpa using hn₂b₂)
        · refine ⟨2, 1, ?_⟩
          simpa using act hnor₂ hb₃B hb₃B (ε := 1) (by simpa using hn₂b₃)
      have hc₃ : σ₃ * τX = τX * σ₃ := by
        refine FF81Hyp.monomial_le_cen_X_tau h hτL hb₁ hb₂ hb₃ hE hτ2 hτb
          ⟨hτ₁, hτ₂, hτ₃⟩ hbB hb₁B hb₂B hb₃B hσ₃X ?_ ?_ ?_ ?_
        · left
          simpa using act hnor₃ hbB hbB (ε := 1)
            (by simpa using hfixb n₃ hn₃)
        · refine ⟨1, 1, ?_⟩
          simpa using act hnor₃ hb₁B hb₂B (ε := 1) (by simpa using hn₃b₁)
        · refine ⟨2, 1, ?_⟩
          simpa using act hnor₃ hb₂B hb₃B (ε := 1) (by simpa using hn₃b₂)
        · refine ⟨0, 1, ?_⟩
          simpa using act hnor₃ hb₃B hb₁B (ε := 1) (by simpa using hn₃b₃)
      have hc₂₃ : σ₂₃ * τX = τX * σ₂₃ := by
        refine FF81Hyp.monomial_le_cen_X_tau h hτL hb₁ hb₂ hb₃ hE hτ2 hτb
          ⟨hτ₁, hτ₂, hτ₃⟩ hbB hb₁B hb₂B hb₃B hσ₂₃X ?_ ?_ ?_ ?_
        · left
          simpa using act hnor₂₃ hbB hbB (ε := 1)
            (by simpa using hfixb n₂₃ hn₂₃)
        · refine ⟨0, 1, ?_⟩
          simpa using act hnor₂₃ hb₁B hb₁B (ε := 1) (by simpa using hn₂₃b₁)
        · refine ⟨2, 1, ?_⟩
          simpa using act hnor₂₃ hb₂B hb₃B (ε := 1) (by simpa using hn₂₃b₂)
        · refine ⟨1, 1, ?_⟩
          simpa using act hnor₂₃ hb₃B hb₂B (ε := 1) (by simpa using hn₂₃b₃)
      have hComm₁ : Commute σ₁ τX := hc₁
      have hComm₂ : Commute σ₂ τX := hc₂
      have hComm₃ : Commute σ₃ τX := hc₃
      have hComm₂₃ : Commute σ₂₃ τX := hc₂₃
      have hCommι₂ : Commute (σ₂ * σ₁ * σ₂⁻¹) τX :=
        Commute.mul_left (Commute.mul_left hComm₂ hComm₁) hComm₂.inv_left
      have hCommι₃ : Commute (σ₂₃ * (σ₂ * σ₁ * σ₂⁻¹) * σ₂₃⁻¹) τX :=
        Commute.mul_left (Commute.mul_left hComm₂₃ hCommι₂) hComm₂₃.inv_left
      have hcι₂ : (σ₂ * σ₁ * σ₂⁻¹) * τX = τX * (σ₂ * σ₁ * σ₂⁻¹) := hCommι₂.eq
      have hcι₃ : (σ₂₃ * (σ₂ * σ₁ * σ₂⁻¹) * σ₂₃⁻¹) * τX =
          τX * (σ₂₃ * (σ₂ * σ₁ * σ₂⁻¹) * σ₂₃⁻¹) := hCommι₃.eq
      have hσι₂ : σ₂ * σ₁ * σ₂⁻¹ =
          Subgroup.normalizerMonoidHom (H := B) ⟨ι₂, hι₂N⟩ := by
        change Subgroup.normalizerMonoidHom (H := B) ⟨n₂, hnor₂⟩ *
            Subgroup.normalizerMonoidHom (H := B) ⟨n₁, hnor₁⟩ *
            (Subgroup.normalizerMonoidHom (H := B) ⟨n₂, hnor₂⟩)⁻¹ =
          Subgroup.normalizerMonoidHom (H := B) ⟨ι₂, hι₂N⟩
        rw [← map_mul, ← map_inv, ← map_mul]
        congr 1
      have hσι₃ : σ₂₃ * (σ₂ * σ₁ * σ₂⁻¹) * σ₂₃⁻¹ =
          Subgroup.normalizerMonoidHom (H := B) ⟨ι₃, hι₃N⟩ := by
        change Subgroup.normalizerMonoidHom (H := B) ⟨n₂₃, hnor₂₃⟩ *
            (Subgroup.normalizerMonoidHom (H := B) ⟨n₂, hnor₂⟩ *
              Subgroup.normalizerMonoidHom (H := B) ⟨n₁, hnor₁⟩ *
              (Subgroup.normalizerMonoidHom (H := B) ⟨n₂, hnor₂⟩)⁻¹) *
            (Subgroup.normalizerMonoidHom (H := B) ⟨n₂₃, hnor₂₃⟩)⁻¹ =
          Subgroup.normalizerMonoidHom (H := B) ⟨ι₃, hι₃N⟩
        rw [← map_mul, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul]
        congr 1
      have hσprod₂X : σ₂ * σ₁ * σ₂⁻¹ ∈ FF81X B := by
        rw [hσι₂, mem_FF81X_iff]
        exact ⟨⟨ι₂, hι₂N⟩, rfl⟩
      have hσprod₃X : σ₂₃ * (σ₂ * σ₁ * σ₂⁻¹) * σ₂₃⁻¹ ∈ FF81X B := by
        rw [hσι₃, mem_FF81X_iff]
        exact ⟨⟨ι₃, hι₃N⟩, rfl⟩
      have hHinv : ∀ {g : G} (hgN : g ∈ Nor B),
          Subgroup.map (Subgroup.normalizerMonoidHom (H := B) ⟨g, hgN⟩) U = U →
          ∀ x ∈ H, g * x * g⁻¹ ∈ H := by
        intro g hgN hUg x hx
        obtain ⟨u, hu, rfl⟩ := hx
        refine ⟨Subgroup.normalizerMonoidHom (H := B) ⟨g, hgN⟩ u, ?_, ?_⟩
        · rw [← hUg]
          exact Subgroup.mem_map_of_mem _ hu
        · change (((Subgroup.normalizerMonoidHom (H := B) ⟨g, hgN⟩) u : ↥B) : G) =
            g * (u : G) * g⁻¹
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hHι₁ : ∀ x ∈ H, n₁ * x * n₁⁻¹ ∈ H :=
        hHinv hnor₁ (hUinv σ₁ hσ₁X hc₁)
      have hHσ₁₂ : ∀ x ∈ H, n₂ * x * n₂⁻¹ ∈ H :=
        hHinv hnor₂ (hUinv σ₂ hσ₂X hc₂)
      have hHγ : ∀ x ∈ H, n₃ * x * n₃⁻¹ ∈ H :=
        hHinv hnor₃ (hUinv σ₃ hσ₃X hc₃)
      have hHσ₂₃ : ∀ x ∈ H, n₂₃ * x * n₂₃⁻¹ ∈ H :=
        hHinv hnor₂₃ (hUinv σ₂₃ hσ₂₃X hc₂₃)
      have hHι₂ : ∀ x ∈ H, ι₂ * x * ι₂⁻¹ ∈ H := by
        have hUg : Subgroup.map (Subgroup.normalizerMonoidHom (H := B) ⟨ι₂, hι₂N⟩) U = U := by
          rw [← hσι₂]
          exact hUinv (σ₂ * σ₁ * σ₂⁻¹) hσprod₂X hcι₂
        exact hHinv hι₂N hUg
      have hHι₃ : ∀ x ∈ H, ι₃ * x * ι₃⁻¹ ∈ H := by
        have hUg : Subgroup.map (Subgroup.normalizerMonoidHom (H := B) ⟨ι₃, hι₃N⟩) U = U := by
          rw [← hσι₃]
          exact hUinv (σ₂₃ * (σ₂ * σ₁ * σ₂⁻¹) * σ₂₃⁻¹) hσprod₃X hcι₃
        exact hHinv hι₃N hUg
      have hn₂inv₁ : n₂⁻¹ * b₁ * n₂ = b₂ := by
        calc n₂⁻¹ * b₁ * n₂ = n₂⁻¹ * (n₂ * b₂ * n₂⁻¹) * n₂ := by rw [← hn₂b₂]
          _ = b₂ := by group
      have hn₂inv₂ : n₂⁻¹ * b₂ * n₂ = b₁ := by
        calc n₂⁻¹ * b₂ * n₂ = n₂⁻¹ * (n₂ * b₁ * n₂⁻¹) * n₂ := by rw [← hn₂b₁]
          _ = b₁ := by group
      have hn₂inv₃ : n₂⁻¹ * b₃ * n₂ = b₃ := by
        calc n₂⁻¹ * b₃ * n₂ = n₂⁻¹ * (n₂ * b₃ * n₂⁻¹) * n₂ := by
              conv_lhs => rw [← hn₂b₃]
          _ = b₃ := by group
      have hn₂inv₁' : n₂ * b₁⁻¹ * n₂⁻¹ = b₂⁻¹ := by
        calc n₂ * b₁⁻¹ * n₂⁻¹ = (n₂ * b₁ * n₂⁻¹)⁻¹ := by group
          _ = b₂⁻¹ := by rw [hn₂b₁]
      have hn₂₃inv₁ : n₂₃⁻¹ * b₁ * n₂₃ = b₁ := by
        calc n₂₃⁻¹ * b₁ * n₂₃ = n₂₃⁻¹ * (n₂₃ * b₁ * n₂₃⁻¹) * n₂₃ := by
              conv_lhs => rw [← hn₂₃b₁]
          _ = b₁ := by group
      have hn₂₃inv₂ : n₂₃⁻¹ * b₃ * n₂₃ = b₂ := by
        calc n₂₃⁻¹ * b₃ * n₂₃ = n₂₃⁻¹ * (n₂₃ * b₂ * n₂₃⁻¹) * n₂₃ := by rw [← hn₂₃b₂]
          _ = b₂ := by group
      have hn₂₃inv₃ : n₂₃⁻¹ * b₂ * n₂₃ = b₃ := by
        calc n₂₃⁻¹ * b₂ * n₂₃ = n₂₃⁻¹ * (n₂₃ * b₃ * n₂₃⁻¹) * n₂₃ := by rw [← hn₂₃b₃]
          _ = b₃ := by group
      have hn₂₃inv₂' : n₂₃ * b₂⁻¹ * n₂₃⁻¹ = b₃⁻¹ := by
        calc n₂₃ * b₂⁻¹ * n₂₃⁻¹ = (n₂₃ * b₂ * n₂₃⁻¹)⁻¹ := by group
          _ = b₃⁻¹ := by rw [hn₂₃b₂]
      have hι₂ : ι₂ * b₁ * ι₂⁻¹ = b₁ ∧ ι₂ * b₂ * ι₂⁻¹ = b₂⁻¹ ∧
          ι₂ * b₃ * ι₂⁻¹ = b₃ := by
        refine ⟨?_, ?_, ?_⟩
        · calc ι₂ * b₁ * ι₂⁻¹
              = n₂ * n₁ * (n₂⁻¹ * b₁ * n₂) * n₁⁻¹ * n₂⁻¹ := by
                rw [show ι₂ = n₂ * n₁ * n₂⁻¹ from rfl]
                group
            _ = n₂ * n₁ * b₂ * n₁⁻¹ * n₂⁻¹ := by rw [hn₂inv₁]
            _ = n₂ * (n₁ * b₂ * n₁⁻¹) * n₂⁻¹ := by group
            _ = n₂ * b₂ * n₂⁻¹ := by rw [hn₁b₂]
            _ = b₁ := hn₂b₂
        · calc ι₂ * b₂ * ι₂⁻¹
              = n₂ * n₁ * (n₂⁻¹ * b₂ * n₂) * n₁⁻¹ * n₂⁻¹ := by
                rw [show ι₂ = n₂ * n₁ * n₂⁻¹ from rfl]
                group
            _ = n₂ * n₁ * b₁ * n₁⁻¹ * n₂⁻¹ := by rw [hn₂inv₂]
            _ = n₂ * (n₁ * b₁ * n₁⁻¹) * n₂⁻¹ := by group
            _ = n₂ * b₁⁻¹ * n₂⁻¹ := by rw [hn₁b₁]
            _ = b₂⁻¹ := hn₂inv₁'
        · calc ι₂ * b₃ * ι₂⁻¹
              = n₂ * n₁ * (n₂⁻¹ * b₃ * n₂) * n₁⁻¹ * n₂⁻¹ := by
                rw [show ι₂ = n₂ * n₁ * n₂⁻¹ from rfl]
                group
            _ = n₂ * n₁ * b₃ * n₁⁻¹ * n₂⁻¹ := by rw [hn₂inv₃]
            _ = n₂ * (n₁ * b₃ * n₁⁻¹) * n₂⁻¹ := by group
            _ = n₂ * b₃ * n₂⁻¹ := by rw [hn₁b₃]
            _ = b₃ := hn₂b₃
      have hι₃ : ι₃ * b₁ * ι₃⁻¹ = b₁ ∧ ι₃ * b₂ * ι₃⁻¹ = b₂ ∧
          ι₃ * b₃ * ι₃⁻¹ = b₃⁻¹ := by
        refine ⟨?_, ?_, ?_⟩
        · calc ι₃ * b₁ * ι₃⁻¹
              = n₂₃ * (ι₂ * (n₂₃⁻¹ * b₁ * n₂₃) * ι₂⁻¹) * n₂₃⁻¹ := by
                rw [show ι₃ = n₂₃ * ι₂ * n₂₃⁻¹ from rfl]
                group
            _ = n₂₃ * (ι₂ * b₁ * ι₂⁻¹) * n₂₃⁻¹ := by rw [hn₂₃inv₁]
            _ = n₂₃ * b₁ * n₂₃⁻¹ := by rw [hι₂.1]
            _ = b₁ := hn₂₃b₁
        · calc ι₃ * b₂ * ι₃⁻¹
              = n₂₃ * (ι₂ * (n₂₃⁻¹ * b₂ * n₂₃) * ι₂⁻¹) * n₂₃⁻¹ := by
                rw [show ι₃ = n₂₃ * ι₂ * n₂₃⁻¹ from rfl]
                group
            _ = n₂₃ * (ι₂ * b₃ * ι₂⁻¹) * n₂₃⁻¹ := by rw [hn₂₃inv₃]
            _ = n₂₃ * b₃ * n₂₃⁻¹ := by rw [hι₂.2.2]
            _ = b₂ := hn₂₃b₃
        · calc ι₃ * b₃ * ι₃⁻¹
              = n₂₃ * (ι₂ * (n₂₃⁻¹ * b₃ * n₂₃) * ι₂⁻¹) * n₂₃⁻¹ := by
                rw [show ι₃ = n₂₃ * ι₂ * n₂₃⁻¹ from rfl]
                group
            _ = n₂₃ * (ι₂ * b₂ * ι₂⁻¹) * n₂₃⁻¹ := by rw [hn₂₃inv₂]
            _ = n₂₃ * b₂⁻¹ * n₂₃⁻¹ := by rw [hι₂.2.1]
            _ = b₃⁻¹ := hn₂₃inv₂'
      have hkey : H = B₁ :=
        FF81Hyp.B1_irreducible_monomial h hb₁ hb₂ hb₃ hE hHle hHne
          (ι₁ := n₁) (ι₂ := ι₂) (ι₃ := ι₃)
          (σ₁₂ := n₂) (σ₂₃ := n₂₃) (γ := n₃)
          ⟨hn₁b₁, hn₁b₂, hn₁b₃⟩ hι₂ hι₃
          ⟨hn₂b₁, hn₂b₂, hn₂b₃⟩ ⟨hn₂₃b₁, hn₂₃b₂, hn₂₃b₃⟩
          ⟨hn₃b₁, hn₃b₂, hn₃b₃⟩
          hHι₁ hHι₂ hHι₃ hHσ₁₂ hHσ₂₃ hHγ
      have hmapH : U.map B.subtype = B₁ := by simpa [H] using hkey
      have hmapB₁ : (B₁.subgroupOf B).map B.subtype = B₁ :=
        Subgroup.map_subgroupOf_eq_of_le hB₁B
      have : U = B₁.subgroupOf B :=
        Subgroup.map_injective B.subtype_injective (by rw [hmapH, hmapB₁])
      simpa [B₁, B] using this
  have hB1inv : ∀ σ : MulAut ↥B, σ ∈ FF81X B →
      Subgroup.map σ (B₁.subgroupOf B) = B₁.subgroupOf B :=
    h.B1_invariant_of_torus hT hTF hOut hnoL hτL hb₁ hb₂ hb₃ hb₁ne hE hself hmono hrk hτ2
      hτb ⟨hτ₁, hτ₂, hτ₃⟩ ht₁X hsX hcX ht₁ hs hc hmove hB1irr
  have hB1inv_map (g : MulAut ↥B) (hg : g ∈ FF81X B) {z : ↥B}
      (hz : z ∈ B₁.subgroupOf B) : g z ∈ B₁.subgroupOf B := by
    have h := Subgroup.mem_map_of_mem g.toMonoidHom hz
    have hmap := hB1inv g hg
    rw [MulEquiv.toMonoidHom_eq_coe] at h
    rwa [hmap] at h
  have hB₁N : ∀ n ∈ Nor B, ∀ y ∈ B₁, n * y * n⁻¹ ∈ B₁ := by
    intro n hn y hy
    have hmap := hB1inv (Subgroup.normalizerMonoidHom (H := B) ⟨n, hn⟩) (by
      rw [mem_FF81X_iff]
      exact ⟨⟨n, hn⟩, rfl⟩)
    have hmap' : (Subgroup.map (Subgroup.normalizerMonoidHom (H := B) ⟨n, hn⟩)
          (B₁.subgroupOf B)).map B.subtype = B₁.map (MulAut.conj n).toMonoidHom := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        rcases Subgroup.mem_map.mp hw with ⟨v, hv, rfl⟩
        change B.subtype (Subgroup.normalizerMonoidHom (H := B) ⟨n, hn⟩ v) ∈
          B₁.map (MulAut.conj n).toMonoidHom
        have hval : B.subtype (Subgroup.normalizerMonoidHom (H := B) ⟨n, hn⟩ v) =
            (MulAut.conj n) (v : G) := by
          change ((Subgroup.normalizerMonoidHom (H := B) ⟨n, hn⟩ v : ↥B) : G) = _
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
        rw [hval]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hv)
      · intro hz
        rcases Subgroup.mem_map.mp hz with ⟨v, hv, hvz⟩
        refine ⟨Subgroup.normalizerMonoidHom (H := B) ⟨n, hn⟩ ⟨v, hB₁B hv⟩, ?_, ?_⟩
        · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hv)
        · change ((Subgroup.normalizerMonoidHom (H := B) ⟨n, hn⟩)
            ⟨v, hB₁B hv⟩ : G) = z
          have hvz' : (MulAut.conj n) v = z := hvz
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
          rw [MulAut.conj_apply] at hvz'
          exact hvz'
    have hEq := congrArg (Subgroup.map B.subtype) hmap
    rw [Subgroup.map_subgroupOf_eq_of_le hB₁B, hmap'] at hEq
    have hy' : n * y * n⁻¹ ∈ B₁.map (MulAut.conj n).toMonoidHom := by
      simpa [MulAut.conj_apply] using Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hy
    rwa [hEq] at hy'
  have hb_not_B₁ : b ∉ B₁ := by
    intro hbB₁
    have hB_le_B₁ : B ≤ B₁ := by
      show Subgroup.closure ({b, b₁, b₂, b₃} : Set G) ≤ B₁
      refine (Subgroup.closure_le B₁).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hbB₁
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    have hB₁_le_B : B₁ ≤ B := by
      show Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ B
      refine (Subgroup.closure_le B).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    have hBeq : B = B₁ := le_antisymm hB_le_B₁ hB₁_le_B
    have h81 : Nat.card B = 81 := by
      have h := hE4.2
      rw [h]
      norm_num
    have h27 : Nat.card B₁ = 27 := by
      have h := hE.2
      rw [h]
      norm_num
    rw [hBeq, h27] at h81
    norm_num at h81
  haveI hB_ea : IsElementaryAbelian 3 ↥B := hE4.1
  haveI hB_comm : IsMulCommutative ↥B := hE4.1.toIsMulCommutative
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥B) (⟨y, hy⟩ : ↥B))
  have hB3 : ∀ x ∈ B, x ^ 3 = 1 :=
    fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) x hx
  haveI hB₁_ea : IsElementaryAbelian 3 ↥B₁ := hE.1
  haveI hB₁_comm : IsMulCommutative ↥B₁ := hE.1.toIsMulCommutative
  have hB₁3 : ∀ x ∈ B₁, x ^ 3 = 1 :=
    fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) x hx
  have hBcard : Nat.card B = 81 := by
    have h := hE4.2
    rw [h]
    norm_num
  have hB₁card : Nat.card B₁ = 27 := by
    have h := hE.2
    rw [h]
    norm_num
  have hBeq : B = Subgroup.zpowers b ⊔ B₁ := closure_four_eq b b₁ b₂ b₃
  have hbn : ∀ z ∈ B₁, b * z * b⁻¹ ∈ B₁ := by
    intro z hz
    have hc : b * z = z * b := hBab b hbB z (hB₁B hz)
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hz
  let bB : ↥B := ⟨b, hbB⟩
  have hbB3 : bB ^ 3 = 1 := by
    apply Subtype.ext
    simpa [bB] using hB3 b hbB
  have hAne : FF81ChainStabilizer B B₁ (FF81X B) ≠ ⊥ := by
    intro hbot
    have hτXmem : τX ∈ FF81X B := by
      rw [mem_FF81X_iff]
      exact ⟨⟨τ, hτN⟩, rfl⟩
    have hττ : τ * τ = 1 := by
      simpa [hτ2, pow_two] using pow_orderOf_eq_one τ
    have hτX2 : τX * τX = 1 := by
      change Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩ *
        Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩ = 1
      rw [← map_mul]
      have h2 : (⟨τ, hτN⟩ : ↥(Nor B)) * ⟨τ, hτN⟩ = 1 := Subtype.ext hττ
      rw [h2, map_one]
    have hτXinv : τX⁻¹ = τX := inv_eq_of_mul_eq_one_right hτX2
    have hτXbB : τX bB = bB := by
      apply Subtype.ext
      change ((Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩ bB : ↥B) : G) = (bB : G)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      simpa [bB] using hτb
    have hτinv_G : ∀ y ∈ B₁, τ * y * τ⁻¹ = y⁻¹ :=
      Lift.conj_inv_of_closure (S := ({b₁, b₂, b₃} : Set G))
        (fun x hx y hy => hBab x (hB₁B hx) y (hB₁B hy))
        (by
          intro s hs
          rcases hs with rfl | rfl | rfl
          exacts [hτ₁, hτ₂, hτ₃])
    have hτinv_sub : ∀ w : ↥B, w ∈ B₁.subgroupOf B → τX w = w⁻¹ := by
      intro w hw
      apply Subtype.ext
      change ((τX w : ↥B) : G) = ((w⁻¹ : ↥B) : G)
      rw [show τX = Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩ from rfl,
        Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact hτinv_G w (Subgroup.mem_subgroupOf.mp hw)
    have hZ := FF81Hyp.X_eq_oddCore_mul_centralizer_tau_of_no_conj h hnoL hτL hb₁ hb₂ hb₃
      hE hb₁ne hτ2 hτb ⟨hτ₁, hτ₂, hτ₃⟩ hbB hb₁B hb₂B hb₃B hτXmem hτX2 rfl
    obtain ⟨σ, hσX, hσmove⟩ := hmove
    have hmem : (⟨σ, hσX⟩ : ↥(FF81X B)) ∈ (⊤ : Set ↥(FF81X B)) := Set.mem_univ _
    rw [hZ] at hmem
    obtain ⟨⟨y, hyX⟩, hyO, ⟨c, hcX⟩, hcC, hσyc⟩ := Set.mem_mul.mp hmem
    have hσ_eq : σ = y * c := by
      have h := congrArg (fun z : ↥(FF81X B) => (z : MulAut ↥B)) hσyc
      simpa using h.symm
    have hcCommX : (⟨c, hcX⟩ : ↥(FF81X B)) * ⟨τX, hτXmem⟩ =
        ⟨τX, hτXmem⟩ * ⟨c, hcX⟩ :=
      Subgroup.mem_centralizer_singleton_iff.mp hcC
    have hcComm : c * τX = τX * c := by
      have h := congrArg (fun z : ↥(FF81X B) => (z : MulAut ↥B)) hcCommX
      simpa using h
    have hcLine : c bB = bB ∨ c bB = bB⁻¹ := by
      have h := (FF81Hyp.cen_tau_iff_nor_line h hTF hOut hτL hb₁ hb₂ hb₃ hE hself
        hmono hrk hτ2 hτb ⟨hτ₁, hτ₂, hτ₃⟩ hbB hb₁B hb₂B hb₃B hτN hcX).mp hcComm
      simpa [bB] using h
    have hyMove : y bB ∉ Subgroup.zpowers bB := by
      intro hy
      apply hσmove
      have hσb : σ bB = y (c bB) := by
        rw [hσ_eq]
        rfl
      rw [hσb]
      rcases hcLine with h | h
      · rw [h]
        exact hy
      · rw [h, map_inv]
        exact (Subgroup.zpowers bB).inv_mem hy
    let φ : MulAut ↥B := τX * y * τX⁻¹ * y⁻¹
    have hφX : φ ∈ FF81X B :=
      (FF81X B).mul_mem
        ((FF81X B).mul_mem ((FF81X B).mul_mem hτXmem hyX) ((FF81X B).inv_mem hτXmem))
        ((FF81X B).inv_mem hyX)
    have hφ_fix_B₁ : ∀ z : ↥B, z ∈ B₁.subgroupOf B → φ z = z := by
      intro z hz
      have hyinvz : y⁻¹ z ∈ B₁.subgroupOf B :=
        hB1inv_map y⁻¹ ((FF81X B).inv_mem hyX) hz
      have hyz : y (y⁻¹ z)⁻¹ ∈ B₁.subgroupOf B :=
        hB1inv_map y hyX ((B₁.subgroupOf B).inv_mem hyinvz)
      calc φ z = τX (y (τX⁻¹ (y⁻¹ z))) := rfl
        _ = τX (y ((y⁻¹ z)⁻¹)) := by rw [hτXinv, hτinv_sub (y⁻¹ z) hyinvz]
        _ = τX (z⁻¹) := by
          rw [show (y⁻¹ z)⁻¹ = y⁻¹ (z⁻¹) by rw [map_inv], MulAut.apply_inv_self]
        _ = z := by
          rw [hτinv_sub (z⁻¹) ((B₁.subgroupOf B).inv_mem hz), inv_inv]
    obtain ⟨ny, hny⟩ := mem_FF81X_iff.mp hyX
    have hyb_mem : (ny : G) * b * (ny : G)⁻¹ ∈ Subgroup.zpowers b ⊔ B₁ := by
      have hbB' : (((Subgroup.normalizerMonoidHom (H := B) ny) bB : ↥B) : G) ∈ B :=
        (((Subgroup.normalizerMonoidHom (H := B) ny) bB)).2
      have hcoe : (((Subgroup.normalizerMonoidHom (H := B) ny) bB : ↥B) : G) =
          (ny : G) * b * (ny : G)⁻¹ :=
        Subgroup.normalizerMonoidHom_apply_apply_coe B ny bB
      rw [← hcoe, ← closure_four_eq b b₁ b₂ b₃]
      exact hbB'
    obtain ⟨n₀, hn₀lt, x₀, hx₀, hybG⟩ :=
      CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.exists_of_mem_A (hB3 b hbB) hbn hyb_mem
    have hny_inv : Subgroup.normalizerMonoidHom (H := B) ny⁻¹ = y⁻¹ := by
      rw [← hny, map_inv]
    have hyib_mem : (ny : G)⁻¹ * b * ((ny : G)⁻¹)⁻¹ ∈ Subgroup.zpowers b ⊔ B₁ := by
      have hbB' : (((Subgroup.normalizerMonoidHom (H := B) ny⁻¹) bB : ↥B) : G) ∈ B :=
        (((Subgroup.normalizerMonoidHom (H := B) ny⁻¹) bB)).2
      have hcoe : (((Subgroup.normalizerMonoidHom (H := B) ny⁻¹) bB : ↥B) : G) =
          (ny : G)⁻¹ * b * ((ny : G)⁻¹)⁻¹ :=
        Subgroup.normalizerMonoidHom_apply_apply_coe B ny⁻¹ bB
      rw [← hcoe, ← closure_four_eq b b₁ b₂ b₃]
      exact hbB'
    obtain ⟨n₁, hn₁lt, x₁, hx₁, hyibG⟩ :=
      CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.exists_of_mem_A (hB3 b hbB) hbn hyib_mem
    let x₀B : ↥B := ⟨x₀, hB₁B hx₀⟩
    let x₁B : ↥B := ⟨x₁, hB₁B hx₁⟩
    have hx₀B : x₀B ∈ B₁.subgroupOf B := Subgroup.mem_subgroupOf.mpr hx₀
    have hx₁B : x₁B ∈ B₁.subgroupOf B := Subgroup.mem_subgroupOf.mpr hx₁
    have hyb' : y bB = bB ^ n₀ * x₀B := by
      apply Subtype.ext
      have h1 : ((y bB : ↥B) : G) = (ny : G) * b * (ny : G)⁻¹ := by
        rw [← hny]
        exact Subgroup.normalizerMonoidHom_apply_apply_coe B ny bB
      have h2 : ((bB ^ n₀ * x₀B : ↥B) : G) = b ^ n₀ * x₀ := by
        simp [bB, x₀B, Subgroup.coe_pow, Subgroup.coe_mul]
      rw [h1, h2]
      exact hybG
    have hyib' : y⁻¹ bB = bB ^ n₁ * x₁B := by
      apply Subtype.ext
      have h1 : ((y⁻¹ bB : ↥B) : G) = (ny : G)⁻¹ * b * ((ny : G)⁻¹)⁻¹ := by
        rw [← hny_inv]
        exact Subgroup.normalizerMonoidHom_apply_apply_coe B ny⁻¹ bB
      have h2 : ((bB ^ n₁ * x₁B : ↥B) : G) = b ^ n₁ * x₁ := by
        simp [bB, x₁B, Subgroup.coe_pow, Subgroup.coe_mul]
      rw [h1, h2]
      exact hyibG
    have hn₀ne : n₀ ≠ 0 := by
      intro h0
      have hx₀_mem : y bB ∈ B₁.subgroupOf B := by
        rw [hyb', h0, pow_zero, one_mul]
        exact hx₀B
      have hbB_mem : bB ∈ B₁.subgroupOf B := by
        have h := hB1inv_map y⁻¹ ((FF81X B).inv_mem hyX) hx₀_mem
        simpa using h
      exact hb_not_B₁ (Subgroup.mem_subgroupOf.mp hbB_mem)
    have hn₁ne : n₁ ≠ 0 := by
      intro h0
      have hx₁_mem : y⁻¹ bB ∈ B₁.subgroupOf B := by
        rw [hyib', h0, pow_zero, one_mul]
        exact hx₁B
      have hbB_mem : bB ∈ B₁.subgroupOf B := by
        have h := hB1inv_map y hyX hx₁_mem
        simpa using h
      exact hb_not_B₁ (Subgroup.mem_subgroupOf.mp hbB_mem)
    have hn₀_cases : n₀ = 1 ∨ n₀ = 2 := by omega
    have hn₁_cases : n₁ = 1 ∨ n₁ = 2 := by omega
    have hyinvx₀ : y⁻¹ x₀B ∈ B₁.subgroupOf B :=
      hB1inv_map y⁻¹ ((FF81X B).inv_mem hyX) hx₀B
    have hcomm_bx₁ : Commute (bB ^ n₁) x₁B := by
      apply Subtype.ext
      exact hBab ((bB ^ n₁ : ↥B) : G) ((bB ^ n₁).2) (x₁B : G) x₁B.2
    have hcomm_bx₀ : Commute (bB ^ n₀) x₀B := by
      apply Subtype.ext
      exact hBab ((bB ^ n₀ : ↥B) : G) ((bB ^ n₀).2) (x₀B : G) x₀B.2
    have hpow₁ : (bB ^ n₁ * x₁B) ^ n₀ = bB ^ (n₁ * n₀) * x₁B ^ n₀ := by
      rw [hcomm_bx₁.mul_pow, ← pow_mul]
    have hpow₀ : (bB ^ n₀ * x₀B) ^ n₁ = bB ^ (n₀ * n₁) * x₀B ^ n₁ := by
      rw [hcomm_bx₀.mul_pow, ← pow_mul]
    let x₃B : ↥B := x₁B ^ n₀ * (y⁻¹ x₀B)
    have hx₃B : x₃B ∈ B₁.subgroupOf B :=
      (B₁.subgroupOf B).mul_mem ((B₁.subgroupOf B).pow_mem hx₁B n₀) hyinvx₀
    have hrel : bB = bB ^ (n₀ * n₁) * x₃B := by
      calc bB = y⁻¹ (y bB) := by simp
        _ = y⁻¹ (bB ^ n₀ * x₀B) := by rw [hyb']
        _ = (y⁻¹ bB) ^ n₀ * y⁻¹ x₀B := by rw [map_mul, map_pow]
        _ = (bB ^ n₁ * x₁B) ^ n₀ * y⁻¹ x₀B := by rw [hyib']
        _ = (bB ^ (n₁ * n₀) * x₁B ^ n₀) * y⁻¹ x₀B := by rw [hpow₁]
        _ = bB ^ (n₀ * n₁) * x₃B := by
          rw [Nat.mul_comm n₁ n₀]
          simp only [x₃B]
          group
    have hbB_mem_of_exp2 : n₀ * n₁ = 2 → bB ∈ B₁.subgroupOf B := by
      intro h2
      have h := hrel
      rw [h2] at h
      have hx : bB⁻¹ = x₃B := by
        calc bB⁻¹ = (bB ^ 2)⁻¹ * bB := by group
          _ = (bB ^ 2)⁻¹ * (bB ^ 2 * x₃B) := by
            conv_lhs => arg 2; rw [h]
          _ = x₃B := by group
      rw [← inv_inv bB, hx]
      exact (B₁.subgroupOf B).inv_mem hx₃B
    have hyx₁inv : y (x₁B⁻¹) ∈ B₁.subgroupOf B :=
      hB1inv_map y hyX ((B₁.subgroupOf B).inv_mem hx₁B)
    let x₂B : ↥B := x₀B ^ n₁ * y (x₁B⁻¹)
    have hx₂B : x₂B ∈ B₁.subgroupOf B :=
      (B₁.subgroupOf B).mul_mem ((B₁.subgroupOf B).pow_mem hx₀B n₁) hyx₁inv
    have hφb_formula : φ bB = bB ^ (n₀ * n₁) * x₂B⁻¹ := by
      calc φ bB = τX (y (τX⁻¹ (y⁻¹ bB))) := rfl
        _ = τX (y (τX⁻¹ (bB ^ n₁ * x₁B))) := by rw [hyib']
        _ = τX (y (bB ^ n₁ * x₁B⁻¹)) := by
          rw [hτXinv, map_mul, map_pow, hτXbB, hτinv_sub x₁B hx₁B]
        _ = τX ((y bB) ^ n₁ * y (x₁B⁻¹)) := by rw [map_mul, map_pow]
        _ = τX ((bB ^ n₀ * x₀B) ^ n₁ * y (x₁B⁻¹)) := by rw [hyb']
        _ = τX ((bB ^ (n₀ * n₁) * x₀B ^ n₁) * y (x₁B⁻¹)) := by rw [hpow₀]
        _ = τX (bB ^ (n₀ * n₁) * x₂B) := by
          congr 1
          simp only [x₂B]
          group
        _ = bB ^ (n₀ * n₁) * x₂B⁻¹ := by
          rw [map_mul, map_pow, hτXbB, hτinv_sub x₂B hx₂B]
    have hφb : ∃ d ∈ B₁.subgroupOf B, φ bB = bB * d := by
      rcases hn₀_cases with rfl | rfl <;> rcases hn₁_cases with rfl | rfl
      · refine ⟨x₂B⁻¹, (B₁.subgroupOf B).inv_mem hx₂B, ?_⟩
        rw [hφb_formula]
        simp
      · exfalso
        exact hb_not_B₁ (Subgroup.mem_subgroupOf.mp (hbB_mem_of_exp2 (by norm_num)))
      · exfalso
        exact hb_not_B₁ (Subgroup.mem_subgroupOf.mp (hbB_mem_of_exp2 (by norm_num)))
      · refine ⟨x₂B⁻¹, (B₁.subgroupOf B).inv_mem hx₂B, ?_⟩
        rw [hφb_formula]
        have h4 : bB ^ 4 = bB := by
          calc bB ^ 4 = bB ^ 3 * bB := by group
            _ = bB := by rw [hbB3, one_mul]
        rw [show (2 * 2 : ℕ) = 4 by norm_num, h4]
    have chain_mem_of (ψ : MulAut ↥B) (hψX : ψ ∈ FF81X B)
        (hfix : ∀ z : ↥B, z ∈ B₁.subgroupOf B → ψ z = z)
        (hb : ∃ d ∈ B₁.subgroupOf B, ψ bB = bB * d) :
        (⟨ψ, hψX⟩ : ↥(FF81X B)) ∈ FF81ChainStabilizer B B₁ (FF81X B) := by
      refine ⟨hfix, ?_⟩
      intro x
      have hxmem : (x : G) ∈ Subgroup.zpowers b ⊔ B₁ := by
        rw [← closure_four_eq b b₁ b₂ b₃]
        exact x.2
      obtain ⟨k, hk, z, hz, hxz⟩ :=
        CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.exists_of_mem_A (hB3 b hbB) hbn hxmem
      let zB : ↥B := ⟨z, hB₁B hz⟩
      have hzB : zB ∈ B₁.subgroupOf B := Subgroup.mem_subgroupOf.mpr hz
      have hx_eq : x = bB ^ k * zB := by
        apply Subtype.ext
        simpa [bB, zB, Subgroup.coe_pow, Subgroup.coe_mul] using hxz
      obtain ⟨d, hd, hbd⟩ := hb
      have hcomm : Commute bB d := by
        apply Subtype.ext
        exact hBab b hbB d d.2
      have hpow : (ψ bB) ^ k = bB ^ k * d ^ k := by
        rw [hbd]
        exact hcomm.mul_pow k
      have hψx : ψ x = bB ^ k * d ^ k * zB := by
        rw [hx_eq, map_mul, map_pow, hfix zB hzB, hpow]
      refine ⟨zB⁻¹ * d ^ k * zB, ?_, ?_⟩
      · exact (B₁.subgroupOf B).mul_mem
          ((B₁.subgroupOf B).mul_mem ((B₁.subgroupOf B).inv_mem hzB)
            ((B₁.subgroupOf B).pow_mem hd k)) hzB
      · calc ψ x = bB ^ k * d ^ k * zB := hψx
          _ = (bB ^ k * zB) * (zB⁻¹ * d ^ k * zB) := by group
          _ = x * (zB⁻¹ * d ^ k * zB) := by rw [← hx_eq]
    have hφA : (⟨φ, hφX⟩ : ↥(FF81X B)) ∈ FF81ChainStabilizer B B₁ (FF81X B) :=
      chain_mem_of φ hφX hφ_fix_B₁ hφb
    have hφ1 : φ = 1 := by
      have hx1 : (⟨φ, hφX⟩ : ↥(FF81X B)) = 1 := by
        have hmem_bot : (⟨φ, hφX⟩ : ↥(FF81X B)) ∈ (⊥ : Subgroup ↥(FF81X B)) := by
          rw [← hbot]
          exact hφA
        exact Subgroup.mem_bot.mp hmem_bot
      have h := congrArg (fun z : ↥(FF81X B) => (z : MulAut ↥B)) hx1
      simpa using h
    have hycomm : y * τX = τX * y := by
      have h2 : τX * y * τX⁻¹ = y := by
        have h3 : τX * y * τX⁻¹ * y⁻¹ = 1 := by
          simpa [φ] using hφ1
        exact mul_inv_eq_one.mp h3
      calc y * τX = (τX * y * τX⁻¹) * τX := by rw [h2]
        _ = τX * y := by rw [mul_assoc, hτXinv, hτX2, mul_one]
    have hmapy := FF81Hyp.cen_X_tau_maps_b h hτL hb₁ hb₂ hb₃ hE hτ2 hτb
      ⟨hτ₁, hτ₂, hτ₃⟩ hbB hyX hycomm
    exact hyMove (by
      have hmem' : y bB ∈ Subgroup.map y.toMonoidHom (Subgroup.zpowers bB) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers bB)
      rw [MulEquiv.toMonoidHom_eq_coe] at hmem'
      rwa [hmapy] at hmem')
  have hsurj : ∀ y ∈ B₁, ∃ a : G,
      (∀ z ∈ B₁, a * z * a⁻¹ = z) ∧ a * b * a⁻¹ = y * b := by
    intro y hy
    obtain ⟨a, haN, hacent, hab⟩ :=
      exists_conj_b_mul (B := B) (B₁ := B₁) (X := FF81X B) (τX := τX)
        hbB hB₁B hb_not_B₁ hBcard hB₁card hBab hB1inv hAne hB1irr le_rfl hy
    exact ⟨a, hacent, by rw [hab, hBab b hbB y (hB₁B hy)]⟩
  let D : Lift.Data b b₁ b₂ b₃ :=
    { Bab := hBab
      B3 := hB3
      Bcard := hBcard
      B₁card := hB₁card
      B₁N := hB₁N
      CB := fun x hx hxp =>
        h.mem_of_cenS hrk huniq hB₁L hself hB₁3 hBeq hE4 hconj hx hxp
      surj := hsurj }
  have hfixb : ∀ g ∈ L, g * b * g⁻¹ = b := by
    intro g hg
    have hc : Commute g b := Subgroup.mem_centralizer_singleton_iff.mp (h.hLC hg)
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hnor_of (g : G) (hgL : g ∈ L)
      (h₁ : g * b₁ * g⁻¹ ∈ B) (h₂ : g * b₂ * g⁻¹ ∈ B) (h₃ : g * b₃ * g⁻¹ ∈ B) :
      g ∈ Nor B := by
    refine mem_nor_of_gen (S := ({b, b₁, b₂, b₃} : Set G)) ?_
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [hfixb g hgL]
      exact Subgroup.subset_closure (by simp)
    · exact h₁
    · exact h₂
    · exact h₃
  have hnor₁ : n₁ ∈ Nor B :=
    hnor_of n₁ hn₁ (by rw [hn₁b₁]; exact B.inv_mem (Subgroup.subset_closure (by simp)))
      (by rw [hn₁b₂]; exact Subgroup.subset_closure (by simp))
      (by rw [hn₁b₃]; exact Subgroup.subset_closure (by simp))
  have hnor₂ : n₂ ∈ Nor B :=
    hnor_of n₂ hn₂ (by rw [hn₂b₁]; exact Subgroup.subset_closure (by simp))
      (by rw [hn₂b₂]; exact Subgroup.subset_closure (by simp))
      (by rw [hn₂b₃]; exact Subgroup.subset_closure (by simp))
  have hnor₃ : n₃ ∈ Nor B :=
    hnor_of n₃ hn₃ (by rw [hn₃b₁]; exact Subgroup.subset_closure (by simp))
      (by rw [hn₃b₂]; exact Subgroup.subset_closure (by simp))
      (by rw [hn₃b₃]; exact Subgroup.subset_closure (by simp))
  have hNmono : ∀ g ∈ ({τ, n₁, n₂, n₃} : Set G), g ∈ Nor B ∧ g * b * g⁻¹ = b := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h | h
    · rw [h]; exact ⟨hτN, hτb⟩
    · rw [h]; exact ⟨hnor₁, hfixb n₁ hn₁⟩
    · rw [h]; exact ⟨hnor₂, hfixb n₂ hn₂⟩
    · rw [h]; exact ⟨hnor₃, hfixb n₃ hn₃⟩
  have hMono : Lift.Mono b b₁ b₂ b₃ τ n₁ (n₂ * n₁ * n₂⁻¹)
      (n₃ * (n₂ * n₁ * n₂⁻¹) * n₃⁻¹) n₂ (n₃ * n₂ * n₃⁻¹) n₃ :=
    Lift.Mono.of_gens hNmono ⟨hτ₁, hτ₂, hτ₃⟩ ⟨hn₁b₁, hn₁b₂, hn₁b₃⟩
      ⟨hn₂b₁, hn₂b₂, hn₂b₃⟩ ⟨hn₃b₁, hn₃b₂, hn₃b₃⟩
  exact ⟨b₁, b₂, b₃, τ, n₁, n₂ * n₁ * n₂⁻¹, n₃ * (n₂ * n₁ * n₂⁻¹) * n₃⁻¹,
    n₂, n₃ * n₂ * n₃⁻¹, n₃, hb₁, hb₂, hb₃, hE, hE4, hB₁L, hself, hmono, hBC,
    hn₁,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hn₂ hn₁) (Subgroup.inv_mem _ hn₂),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hn₃
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hn₂ hn₁) (Subgroup.inv_mem _ hn₂)))
      (Subgroup.inv_mem _ hn₃),
    hn₂,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hn₃ hn₂) (Subgroup.inv_mem _ hn₃),
    hn₃, D, hMono⟩

end CFSG.RankThree.PartTwo.Sec21.FF81
