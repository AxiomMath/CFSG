module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aCenYTau
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aNorMono
public import CFSG.GroupTheory.ABGLocalTools.Constraint

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.MulAut

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.CYtau_eq_one
    (h : FF81Hyp b L) (hTF : KF_Sp6TorusFree) (hOut : KF_Sp62Out)
    {b₁ b₂ b₃ τ : G} (hτL : τ ∈ L) (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE3 : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hself : L ⊓ CenS (Subgroup.closure ({b₁, b₂, b₃} : Set G)) =
      Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hmono : ∀ n ∈ L, n ∈ Nor (Subgroup.closure ({b₁, b₂, b₃} : Set G)) →
      ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 27)
    (hE4 : IsElemAb 3 4 (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    (hτ2 : orderOf τ = 2) (hb : τ * b * τ⁻¹ = b)
    (hinv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹)
    (hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₁B : b₁ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₂B : b₂ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₃B : b₃ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hτN : τ ∈ Nor (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    {t₁ s c : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))}
    (ht₁X : t₁ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    (hsX : s ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    (hcX : c ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    (ht₁ : t₁ ⟨b, hbB⟩ = ⟨b, hbB⟩ ∧ t₁ ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹ ∧
      t₁ ⟨b₂, hb₂B⟩ = ⟨b₂, hb₂B⟩ ∧ t₁ ⟨b₃, hb₃B⟩ = ⟨b₃, hb₃B⟩)
    (hs : s ⟨b, hbB⟩ = ⟨b, hbB⟩ ∧ s ⟨b₁, hb₁B⟩ = ⟨b₂, hb₂B⟩ ∧
      s ⟨b₂, hb₂B⟩ = ⟨b₁, hb₁B⟩ ∧ s ⟨b₃, hb₃B⟩ = ⟨b₃, hb₃B⟩)
    (hc : c ⟨b, hbB⟩ = ⟨b, hbB⟩ ∧ c ⟨b₁, hb₁B⟩ = ⟨b₂, hb₂B⟩ ∧
      c ⟨b₂, hb₂B⟩ = ⟨b₃, hb₃B⟩ ∧ c ⟨b₃, hb₃B⟩ = ⟨b₁, hb₁B⟩)
    {g : FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G))}
    (hgY : g ∈ oddCore ↥(FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G))))
    (hgline : (g : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) *
        (FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE3 hb hinv)) =
      (FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE3 hb hinv)) * (g : MulAut _)) :
    (g : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) = 1 := by
  classical
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  let bB : ↥B := ⟨b, hbB⟩
  let b₁B : ↥B := ⟨b₁, hb₁B⟩
  let b₂B : ↥B := ⟨b₂, hb₂B⟩
  let b₃B : ↥B := ⟨b₃, hb₃B⟩
  let X : Subgroup (MulAut ↥B) := FF81X B
  let τX : MulAut ↥B :=
    FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE3 hb hinv)
  have hcomm : (g : MulAut ↥B) * τX = τX * (g : MulAut ↥B) := hgline
  have hmap := FF81Hyp.cen_X_tau_maps_b h hτL hb₁ hb₂ hb₃ hE3 hτ2 hb hinv hbB
    (σ := (g : MulAut ↥B)) g.2 hcomm
  have horderB : orderOf bB = 3 := by
    rw [← Subgroup.orderOf_coe bB]
    simpa [bB] using h.ord
  have hbB_ne : bB ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at horderB
    norm_num at horderB
  have hgb_mem : (g : MulAut ↥B) bB ∈ Subgroup.zpowers bB := by
    have hmem : (g : MulAut ↥B) bB ∈
        Subgroup.map ((g : MulAut ↥B) : ↥B →* ↥B) (Subgroup.zpowers bB) :=
      Subgroup.mem_map_of_mem ((g : MulAut ↥B) : ↥B →* ↥B) (Subgroup.mem_zpowers bB)
    rwa [hmap] at hmem
  have hgb_ne : (g : MulAut ↥B) bB ≠ 1 := by
    intro h1
    apply hbB_ne
    have h := congrArg (fun y => (g : MulAut ↥B)⁻¹ y) h1
    simpa using h
  have hgbpm : (g : MulAut ↥B) bB = bB ∨ (g : MulAut ↥B) bB = bB⁻¹ :=
    eq_or_eq_inv_of_mem_zpowers (b := bB) horderB hgb_mem hgb_ne
  have hgodd : Odd (orderOf (g : MulAut ↥B)) := by
    rw [Subgroup.orderOf_coe]
    have hdvd : orderOf g ∣ Nat.card ↥(oddCore ↥X) :=
      Subgroup.orderOf_dvd_natCard (oddCore X) hgY
    exact Odd.of_dvd_nat (CFSG.ABGLocalTools.odd_card_oddCore (H := ↥X)) hdvd
  haveI : IsElementaryAbelian 3 ↥B := hE4.1
  have h3 : ∀ x : ↥B, x ^ 3 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 ↥B)
  have hgb : (g : MulAut ↥B) bB = bB := by
    rcases hgbpm with hfix | hinv'
    · exact hfix
    · exact CFSG.MulAut.apply_eq_self_of_odd hgodd (h3 bB) (k := -1) (by
        rw [hinv', zpow_neg_one])
  have hmonoσ := FF81Hyp.nor_X_line_monomial h hTF hOut hb₁ hb₂ hb₃ hE3 hself hmono hrk
    hbB hb₁B hb₂B hb₃B (σ := (g : MulAut ↥B)) g.2 (Or.inl hgb)
  have hgl : ∀ x ∈ ({b₁B, b₂B, b₃B} : Set ↥B),
      ∃ y ∈ ({b₁B, b₂B, b₃B} : Set ↥B), ∃ k : ℤ, (g : MulAut ↥B) x = y ^ k := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · obtain ⟨j, k, hk⟩ := hmonoσ.1
      fin_cases j
      · exact ⟨b₁B, by simp, k, by simpa [b₁B] using hk⟩
      · exact ⟨b₂B, by simp, k, by simpa [b₁B, b₂B] using hk⟩
      · exact ⟨b₃B, by simp, k, by simpa [b₁B, b₃B] using hk⟩
    · obtain ⟨j, k, hk⟩ := hmonoσ.2.1
      fin_cases j
      · exact ⟨b₁B, by simp, k, by simpa [b₂B, b₁B] using hk⟩
      · exact ⟨b₂B, by simp, k, by simpa [b₂B] using hk⟩
      · exact ⟨b₃B, by simp, k, by simpa [b₂B, b₃B] using hk⟩
    · obtain ⟨j, k, hk⟩ := hmonoσ.2.2
      fin_cases j
      · exact ⟨b₁B, by simp, k, by simpa [b₃B, b₁B] using hk⟩
      · exact ⟨b₂B, by simp, k, by simpa [b₃B, b₂B] using hk⟩
      · exact ⟨b₃B, by simp, k, by simpa [b₃B] using hk⟩
  have hgen : Subgroup.closure ({bB, b₁B, b₂B, b₃B} : Set ↥B) = ⊤ := by
    have hset : ({bB, b₁B, b₂B, b₃B} : Set ↥B) =
        ((↑) : ↥B → G) ⁻¹' ({b, b₁, b₂, b₃} : Set G) := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro (rfl | rfl | rfl | rfl) <;> simp [bB, b₁B, b₂B, b₃B]
      · rintro (h | h | h | h)
        · exact Or.inl (Subtype.ext (by simpa [bB] using h))
        · exact Or.inr (Or.inl (Subtype.ext (by simpa [b₁B] using h)))
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by simpa [b₂B] using h))))
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by simpa [b₃B] using h))))
    rw [hset]
    exact Subgroup.closure_closure_coe_preimage
  have hY : Odd (Nat.card (oddCore ↥X)) :=
    CFSG.ABGLocalTools.odd_card_oddCore (H := ↥X)
  have hEqX : (g : X) = 1 :=
    CFSG.MulAut.eq_one_of_mem_oddNormal_of_lines_H0 (B := ↥B) (b := bB) (b₁ := b₁B)
      (b₂ := b₂B) (b₃ := b₃B) h3 hgen (X := X) (Y := oddCore X) hY
      ht₁X hsX hcX ht₁ hs hc hgY (Or.inl hgb) hgl
  have hEq : (g : MulAut ↥B) = 1 := by
    simpa using congrArg Subtype.val hEqX
  simpa [B] using hEq

end CFSG.RankThree.PartTwo.Sec21.FF81
