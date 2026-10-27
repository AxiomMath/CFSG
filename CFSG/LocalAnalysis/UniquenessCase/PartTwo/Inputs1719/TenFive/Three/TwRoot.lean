module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.TwHeisThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcRootPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwistRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.TwHeis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootDiagUnit)
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open scoped commutatorElement


private theorem twRoot_commutator {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {k : Type} [Field k] {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hαβ : α ≠ β) (hαβ' : α ≠ -β) (hε : IsRoot τ (α + β)) :
    (commConst τ α β (1, 1) = 1 ∨ commConst τ α β (1, 1) = -1) ∧
      ∀ c d : k, ⁅pinnedX τ k α c, pinnedX τ k β d⁆ =
        pinnedX τ k (α + β) ((commConst τ α β (1, 1) : k) * (c * d)) := by
  have h := (simply_laced_root_commutator_unit τ hτ hα hβ hαβ hαβ').1 hε
  exact ⟨h.1, fun c d => by rw [h.2 k c d, mul_assoc]⟩

private theorem twRoot_conj_commutator {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Type} [Field k] (Q : ModGL τ k)
    {γ δ ε : Fin τ.rank → ℤ} {s t : k} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hγδ : γ ≠ δ)
    (hγδ' : γ ≠ -δ) (hε : IsRoot τ ε) (hsum : γ + δ = ε)
    (hQγ : ∀ c, Q * pinnedX τ k γ c * Q⁻¹ = pinnedX τ k γ (s * c))
    (hQδ : ∀ c, Q * pinnedX τ k δ c * Q⁻¹ = pinnedX τ k δ (t * c)) :
    Q * pinnedX τ k ε (commConst τ γ δ (1, 1)) * Q⁻¹ =
      pinnedX τ k ε ((commConst τ γ δ (1, 1) : k) * s * t) := by
  have hcf := twRoot_commutator (k := k) hτ hγ hδ hγδ hγδ' (hsum ▸ hε)
  have hcomm : ⁅pinnedX τ k γ 1, pinnedX τ k δ 1⁆ =
      pinnedX τ k ε (commConst τ γ δ (1, 1)) := by
    rw [hcf.2 1 1, hsum]
    simp
  have hmap : Q * ⁅pinnedX τ k γ 1, pinnedX τ k δ 1⁆ * Q⁻¹ =
      ⁅Q * pinnedX τ k γ 1 * Q⁻¹, Q * pinnedX τ k δ 1 * Q⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [← hcomm, hmap, hQγ, hQδ, hcf.2 (s * 1) (t * 1), hsum]
  congr 1
  ring

private theorem twRoot_sign_eq {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {k : Type} [Field k] (Q : ModGL τ k) {α β : Fin τ.rank → ℤ} {sα sβ se : k}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hαβ : α ≠ β) (hαβ' : α ≠ -β)
    (hε : IsRoot τ (α + β))
    (hQα : ∀ c, Q * pinnedX τ k α c * Q⁻¹ = pinnedX τ k α (sα * c))
    (hQβ : ∀ c, Q * pinnedX τ k β c * Q⁻¹ = pinnedX τ k β (sβ * c))
    (hQε : ∀ c, Q * pinnedX τ k (α + β) c * Q⁻¹ = pinnedX τ k (α + β) (se * c)) :
    sα * sβ = se := by
  have hconj := twRoot_conj_commutator (ε := α + β) hτ Q hα hβ hαβ hαβ' hε rfl hQα hQβ
  have hcf := twRoot_commutator (k := k) hτ hα hβ hαβ hαβ' hε
  have hN0 : (commConst τ α β (1, 1) : k) ≠ 0 := by
    rcases hcf.1 with h' | h' <;> rw [h'] <;> norm_num
  have h2 : pinnedX τ k (α + β) ((commConst τ α β (1, 1) : k) * sα * sβ) =
      pinnedX τ k (α + β) (se * (commConst τ α β (1, 1) : k)) := by
    rw [← hconj]
    exact hQε _
  have heq := pinnedX_injective τ k (α + β) h2
  have h3 : (commConst τ α β (1, 1) : k) * (sα * sβ) = (commConst τ α β (1, 1) : k) * se := by
    rw [← mul_assoc, heq]
    exact mul_comm se (commConst τ α β (1, 1) : k)
  exact mul_left_cancel₀ hN0 h3

private theorem twRoot_sign_eq_two {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Type} [Field k] (Q : ModGL τ k)
    {α β γ δ : Fin τ.rank → ℤ} {sα sβ sγ sδ : k}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (hαβ : α ≠ β) (hαβ' : α ≠ -β) (hγδ : γ ≠ δ) (hγδ' : γ ≠ -δ)
    (hε : IsRoot τ (α + β)) (hsum : α + β = γ + δ)
    (hQα : ∀ c, Q * pinnedX τ k α c * Q⁻¹ = pinnedX τ k α (sα * c))
    (hQβ : ∀ c, Q * pinnedX τ k β c * Q⁻¹ = pinnedX τ k β (sβ * c))
    (hQγ : ∀ c, Q * pinnedX τ k γ c * Q⁻¹ = pinnedX τ k γ (sγ * c))
    (hQδ : ∀ c, Q * pinnedX τ k δ c * Q⁻¹ = pinnedX τ k δ (sδ * c)) :
    sα * sβ = sγ * sδ := by
  have h1 := twRoot_conj_commutator (ε := α + β) hτ Q hα hβ hαβ hαβ' hε rfl hQα hQβ
  have h2 := twRoot_conj_commutator (ε := α + β) hτ Q hγ hδ hγδ hγδ' hε hsum.symm hQγ hQδ
  have hcfα := twRoot_commutator (k := k) hτ hα hβ hαβ hαβ' hε
  have hcfγ := twRoot_commutator (k := k) hτ hγ hδ hγδ hγδ' (hsum ▸ hε)
  have hN1 : (commConst τ α β (1, 1) : k) ≠ 0 := by
    rcases hcfα.1 with h' | h' <;> rw [h'] <;> norm_num
  have hN2 : ((commConst τ γ δ (1, 1) : ℤ) : k) =
      ((commConst τ α β (1, 1) : ℤ) : k) ∨
      ((commConst τ γ δ (1, 1) : ℤ) : k) = -((commConst τ α β (1, 1) : ℤ) : k) := by
    rcases hcfα.1 with h' | h' <;> rcases hcfγ.1 with h'' | h'' <;> rw [h', h''] <;> norm_num
  rcases hN2 with hN2 | hN2
  · have key : pinnedX τ k (α + β) ((commConst τ α β (1, 1) : k) * sα * sβ) =
        pinnedX τ k (α + β) ((commConst τ γ δ (1, 1) : k) * sγ * sδ) := by
      rw [← h1, ← h2, hN2]
    have heq := pinnedX_injective τ k (α + β) key
    rw [hN2] at heq
    simp only [mul_assoc] at heq
    exact mul_left_cancel₀ hN1 heq
  · have key : pinnedX τ k (α + β) (-((commConst τ α β (1, 1) : k) * sα * sβ)) =
        pinnedX τ k (α + β) ((commConst τ γ δ (1, 1) : k) * sγ * sδ) := by
      rw [← pinnedX_neg, ← h1, ← h2, hN2, ← pinnedX_neg]
      group
    have heq := pinnedX_injective τ k (α + β) key
    rw [hN2] at heq
    have h5 : -((commConst τ α β (1, 1) : k) * sα * sβ) =
        -((commConst τ α β (1, 1) : k) * (sγ * sδ)) := by
      rw [heq]
      ring
    have h := neg_inj.mp h5
    simp only [mul_assoc] at h
    exact mul_left_cancel₀ hN1 h

theorem exists_twist_rootPairs_inv_extraGood {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Type} [Field k] [IsAlgClosed k]
    [CharP k 3] (Q : ModGL τ k) {α β γ δ : Fin τ.rank → ℤ} (h : RootPairs τ α β γ δ)
    (hQ : ∀ ρ ∈ [α, β, γ, δ], ∃ s : k, s * s = 1 ∧
      ∀ c, Q * pinnedX τ k ρ c * Q⁻¹ = pinnedX τ k ρ (s * c))
    {t : ModGL τ k} (htB : ∀ c, t * pinnedX τ k β c * t⁻¹ = pinnedX τ k β (-c)) :
    ∃ u : fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k 3 1 Q), orderOf u = 3 ∧
      IsExtraGood u ∧ t * (u : ModGL τ k) * t⁻¹ = (u : ModGL τ k)⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨sα, hsα, hQα⟩ := hQ α (by simp)
  obtain ⟨sβ, hsβ, hQβ⟩ := hQ β (by simp)
  obtain ⟨sγ, hsγ, hQγ⟩ := hQ γ (by simp)
  obtain ⟨sδ, hsδ, hQδ⟩ := hQ δ (by simp)
  have hsign : sα * sβ = sγ * sδ :=
    twRoot_sign_eq_two hτ Q h.root₁ h.root₂ h.root₃ h.root₄ h.ne₁₂ h.ne₁₂' h.ne₃₄ h.ne₃₄'
      h.root_add h.add_eq.symm hQα hQβ hQγ hQδ
  have hcfαβ := twRoot_commutator (k := k) hτ h.root₁ h.root₂ h.ne₁₂ h.ne₁₂' h.root_add
  have hcfγδ := twRoot_commutator (k := k) hτ h.root₃ h.root₄ h.ne₃₄ h.ne₃₄' (h.add_eq ▸ h.root_add)
  obtain ⟨la, hla⟩ := (IsAlgClosed.exists_eq_mul_self sα).imp fun _ => Eq.symm
  obtain ⟨lb, hlb⟩ := (IsAlgClosed.exists_eq_mul_self sβ).imp fun _ => Eq.symm
  obtain ⟨lg, hlg⟩ := (IsAlgClosed.exists_eq_mul_self sγ).imp fun _ => Eq.symm
  set N₁ : k := (commConst τ α β (1, 1) : k) with hN₁
  set N₂ : k := (commConst τ γ δ (1, 1) : k) with hN₂
  have hN₁sq : N₁ * N₁ = 1 := by
    rw [hN₁]
    rcases hcfαβ.1 with h' | h' <;> rw [h'] <;> norm_num
  have hN₂sq : N₂ * N₂ = 1 := by
    rw [hN₂]
    rcases hcfγδ.1 with h' | h' <;> rw [h'] <;> norm_num
  have hN₁0 : N₁ ≠ 0 := left_ne_zero_of_mul_eq_one hN₁sq
  set ld : k := N₁ * N₂ * la * lb * lg * sγ with hld
  have hldsq : ld * ld = sδ := by
    have hsign' : sα * sβ * sγ = sδ := by
      rw [hsign]
      linear_combination sδ * hsγ
    rw [hld]
    have h1 : (N₁ * N₂ * la * lb * lg * sγ) * (N₁ * N₂ * la * lb * lg * sγ) =
        (N₁ * N₁) * (N₂ * N₂) * (la * la) * (lb * lb) * (lg * lg) * (sγ * sγ) := by ring
    rw [h1]
    simp only [hN₁sq, hN₂sq, hla, hlb, hlg, hsγ, one_mul, mul_one]
    exact hsign'
  have hNcent : N₂ * lg * ld = N₁ * la * lb := by
    rw [hld]
    have h1 : N₂ * lg * (N₁ * N₂ * la * lb * lg * sγ) =
        (N₂ * N₂) * ((lg * lg) * sγ) * (N₁ * (la * lb)) := by ring
    rw [h1]
    simp only [hN₂sq, hlg, hsγ, one_mul, mul_one]
    ring
  have hεα : α + β + α = 2 • α + β := by rw [two_nsmul]; abel
  have hεβ : α + β + β = α + 2 • β := by rw [two_nsmul]; abel
  have hεγ : α + β + γ = 2 • γ + δ := by rw [← h.add_eq, two_nsmul]; abel
  have hεδ : α + β + δ = γ + 2 • δ := by rw [← h.add_eq, two_nsmul]; abel
  have hneα : α + β ≠ -α := by
    intro e; exact h.ne_zero₂₁ (by rw [← hεα, e, neg_add_cancel])
  have hneβ : α + β ≠ -β := by
    intro e; exact h.ne_zero₁₂ (by rw [← hεβ, e, neg_add_cancel])
  have hneγ : α + β ≠ -γ := by
    intro e; exact h.ne_zero₄₃ (by rw [← hεγ, e, neg_add_cancel])
  have hneδ : α + β ≠ -δ := by
    intro e; exact h.ne_zero₃₄ (by rw [← hεδ, e, neg_add_cancel])
  have hneα₁ : α + β ≠ α := fun e => h.root₂.ne_zero (add_eq_left.1 e)
  have hneβ₁ : α + β ≠ β := fun e => h.root₁.ne_zero (add_eq_right.1 e)
  have hneγ₁ : α + β ≠ γ := fun e => h.root₄.ne_zero (add_eq_left.1 (h.add_eq.trans e))
  have hneδ₁ : α + β ≠ δ := fun e => h.root₃.ne_zero (add_eq_right.1 (h.add_eq.trans e))
  have hnrεα : ¬ IsRoot τ (α + β + α) := hεα ▸ h.not_root₂₁
  have hnrεβ : ¬ IsRoot τ (α + β + β) := hεβ ▸ h.not_root₁₂
  have hnrεγ : ¬ IsRoot τ (α + β + γ) := hεγ ▸ h.not_root₄₃
  have hnrεδ : ¬ IsRoot τ (α + β + δ) := hεδ ▸ h.not_root₃₄
  have hcrαγ := h.cross α (by simp) γ (by simp)
  have hcrαδ := h.cross α (by simp) δ (by simp)
  have hcrβγ := h.cross β (by simp) γ (by simp)
  have hcrβδ := h.cross β (by simp) δ (by simp)
  have hcαγ : RootsCommute τ α γ := ⟨fun e => hcrαδ.2 (by rw [e, h.add_eq]; exact h.root_add),
    fun e => hcrαγ.1 (by rw [e, neg_add_cancel]), hcrαγ.2⟩
  have hcαδ : RootsCommute τ α δ :=
    ⟨fun e => hcrαγ.2 (by rw [e, add_comm δ γ, h.add_eq]; exact h.root_add),
      fun e => hcrαδ.1 (by rw [e, neg_add_cancel]), hcrαδ.2⟩
  have hcβγ : RootsCommute τ β γ := ⟨fun e => hcrβδ.2 (by rw [e, h.add_eq]; exact h.root_add),
    fun e => hcrβγ.1 (by rw [e, neg_add_cancel]), hcrβγ.2⟩
  have hcβδ : RootsCommute τ β δ :=
    ⟨fun e => hcrβγ.2 (by rw [e, add_comm δ γ, h.add_eq]; exact h.root_add),
      fun e => hcrβδ.1 (by rw [e, neg_add_cancel]), hcrβδ.2⟩
  let ι : ZMod 3 →+* k := ZMod.castHom (dvd_refl 3) k
  obtain ⟨ι₁, hι₁, hA₁, hB₁, hZ₁⟩ :=
    exists_heis_fixed (X := adjointGroup τ k) (S := frobTwistGL τ k 3 1 Q) (K := ZMod 3)
      (ι := ι) (Nat.card_zmod 3) (A := fun c => pinnedX τ k α c)
      (B := fun c => pinnedX τ k β c) (C := fun c => pinnedX τ k (α + β) (N₁ * c))
      (hA := fun c d => pinnedX_add τ k α c d) (hB := fun c d => pinnedX_add τ k β c d)
      (hC := fun c d => by rw [mul_add, pinnedX_add])
      (hAX := fun c => pinnedX_mem_adjointGroup α c)
      (hBX := fun c => pinnedX_mem_adjointGroup β c) (hsa := hsα) (hsb := hsβ)
      (hSA := fun c => by simpa using frobTwistGL_pinnedX 3 1 Q hQα c)
      (hSB := fun c => by simpa using frobTwistGL_pinnedX 3 1 Q hQβ c)
      (hAB := fun c d => by rw [hcfαβ.2 c d])
      (hCA := fun c d => pinnedX_commute hτ h.root_add h.root₁ hneα₁ hneα hnrεα (N₁ * c) d)
      (hCB := fun c d => pinnedX_commute hτ h.root_add h.root₂ hneβ₁ hneβ hnrεβ (N₁ * c) d)
      (hCinj := fun c hc => (mul_eq_zero.1 (pinnedX_injective τ k (α + β)
        (by rw [hc, pinnedX_zero]))).resolve_left hN₁0)
      (hla := hla) (hlb := hlb)
  obtain ⟨ι₂, hι₂, hA₂, hB₂, hZ₂⟩ :=
    exists_heis_fixed (X := adjointGroup τ k) (S := frobTwistGL τ k 3 1 Q) (K := ZMod 3)
      (ι := ι) (Nat.card_zmod 3) (A := fun c => pinnedX τ k γ c)
      (B := fun c => pinnedX τ k δ c) (C := fun c => pinnedX τ k (α + β) (N₂ * c))
      (hA := fun c d => pinnedX_add τ k γ c d) (hB := fun c d => pinnedX_add τ k δ c d)
      (hC := fun c d => by rw [mul_add, pinnedX_add])
      (hAX := fun c => pinnedX_mem_adjointGroup γ c)
      (hBX := fun c => pinnedX_mem_adjointGroup δ c) (hsa := hsγ) (hsb := hsδ)
      (hSA := fun c => by simpa using frobTwistGL_pinnedX 3 1 Q hQγ c)
      (hSB := fun c => by simpa using frobTwistGL_pinnedX 3 1 Q hQδ c)
      (hAB := fun c d => by rw [hcfγδ.2 c d, h.add_eq])
      (hCA := fun c d => pinnedX_commute hτ h.root_add h.root₃ hneγ₁ hneγ hnrεγ (N₂ * c) d)
      (hCB := fun c d => pinnedX_commute hτ h.root_add h.root₄ hneδ₁ hneδ hnrεδ (N₂ * c) d)
      (hCinj := fun c hc => (mul_eq_zero.1 (pinnedX_injective τ k (α + β)
        (by rw [hc, pinnedX_zero]))).resolve_left (left_ne_zero_of_mul_eq_one hN₂sq))
      (hla := hlg) (hlb := hldsq)
  have hcen : ∀ r, ι₁ ⟨0, 0, r⟩ = ι₂ ⟨0, 0, r⟩ := by
    intro r
    apply Subtype.ext
    rw [hZ₁ r, hZ₂ r]
    congr 1
    calc N₁ * (la * lb * ι r) = (N₁ * la * lb) * ι r := by ring
      _ = (N₂ * lg * ld) * ι r := by rw [hNcent]
      _ = N₂ * (lg * ld * ι r) := by ring
  have hcomm : ∀ a b, Commute (ι₁ a) (ι₂ b) :=
    commute_heis_of_axes hcen
      (fun s t => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hA₁ s, hA₂ t]
        exact pinnedX_commute_of_rootsCommute hτ h.root₁ h.root₃ hcαγ _ _)
      (fun s t => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hA₁ s, hB₂ t]
        exact pinnedX_commute_of_rootsCommute hτ h.root₁ h.root₄ hcαδ _ _)
      (fun s t => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hB₁ s, hA₂ t]
        exact pinnedX_commute_of_rootsCommute hτ h.root₂ h.root₃ hcβγ _ _)
      (fun s t => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hB₁ s, hB₂ t]
        exact pinnedX_commute_of_rootsCommute hτ h.root₂ h.root₄ hcβδ _ _)
  have huG : ((ι₁ ⟨0, 1, 0⟩ : fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k 3 1 Q)) :
      ModGL τ k) = pinnedX τ k β lb := by
    rw [hB₁ 1]
    simp
  refine ⟨ι₁ ⟨0, 1, 0⟩, ?_, ?_, ?_⟩
  · have h := orderOf_injective ι₁ hι₁ (⟨0, 1, 0⟩ : Heis (ZMod 3))
    rw [h]
    refine orderOf_eq_prime ?_ ?_
    · exact Heis.pow_prime_eq_one Nat.prime_three (by norm_num) (⟨0, 1, 0⟩ : Heis (ZMod 3))
    · intro h
      exact one_ne_zero (congrArg Heis.b h)
  · exact isExtraGood_of_heis_pair (Nat.card_zmod 3) hι₁ hι₂ hcomm hcen ⟨0, 1, 0⟩
  · rw [huG, htB lb, pinnedX_neg]

theorem exists_twist_orbit_two_extraGood {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Type} [Field k] [IsAlgClosed k]
    [CharP k 3] (Q : ModGL τ k) (θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (hQ : ∀ γ, IsRoot τ γ → ∃ s : k, s * s = 1 ∧
      ∀ c, Q * pinnedX τ k γ c * Q⁻¹ = pinnedX τ k (θ γ) (s * c))
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (hθβ : IsRoot τ (θ β))
    (hθγ : IsRoot τ (θ γ)) (hθθγ : θ (θ γ) = γ)
    (hβγ : β ≠ γ ∧ β ≠ -γ ∧ IsRoot τ (β + γ)) (hθβθγ : θ β ≠ θ γ ∧ θ β ≠ -θ γ)
    (hsum : θ β + θ γ = β + γ) (hθε : θ (β + γ) = β + γ)
    (hββ : RootsCommute τ β (θ β)) (hγγ : RootsCommute τ γ (θ γ))
    (hβθγ : RootsCommute τ β (θ γ)) (hθβγ : RootsCommute τ (θ β) γ)
    (hz : ∀ ρ ∈ [β, θ β, γ, θ γ], RootsCommute τ (β + γ) ρ)
    {sb sb' : k} (hsb : sb * sb = 1) (hsb' : sb' * sb' = 1)
    (hQβ : ∀ c, Q * pinnedX τ k β c * Q⁻¹ = pinnedX τ k (θ β) (sb * c))
    (hQβ' : ∀ c, Q * pinnedX τ k (θ β) c * Q⁻¹ = pinnedX τ k β (sb' * c))
    {lam : k} (hlam0 : lam ≠ 0) (hlam : lam ^ 9 = lam * (sb * sb')) :
    ∃ u : fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k 3 1 Q),
      (u : ModGL τ k) = pinnedX τ k β lam * pinnedX τ k (θ β) (sb * lam ^ 3) ∧
      orderOf u = 3 ∧ IsExtraGood u := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨sd, hsd, hQγ⟩ := hQ γ hγ
  obtain ⟨sd', hsd', hQγ'⟩ := hQ (θ γ) hθγ
  have hQγθ : ∀ c, Q * pinnedX τ k (θ γ) c * Q⁻¹ = pinnedX τ k γ (sd' * c) := by
    intro c; rw [hQγ' c, hθθγ]
  obtain ⟨se, hse, hQε⟩ := hQ (β + γ) hβγ.2.2
  have hQε' : ∀ c, Q * pinnedX τ k (β + γ) c * Q⁻¹ = pinnedX τ k (β + γ) (se * c) := by
    intro c; rw [hQε c, hθε]
  have hcf := twRoot_commutator (k := k) hτ hβ hγ hβγ.1 hβγ.2.1 hβγ.2.2
  have hcf' := twRoot_commutator (k := k) hτ hθβ hθγ hθβθγ.1 hθβθγ.2 (hsum ▸ hβγ.2.2)
  have hn : (commConst τ β γ (1, 1) : k) * (commConst τ β γ (1, 1) : k) = 1 := by
    rcases hcf.1 with h' | h' <;> rw [h'] <;> norm_num
  have hn' : (commConst τ (θ β) (θ γ) (1, 1) : k) *
      (commConst τ (θ β) (θ γ) (1, 1) : k) = 1 := by
    rcases hcf'.1 with h' | h' <;> rw [h'] <;> norm_num
  have hBadd : ∀ c d : k, pinnedX τ k β (c + d) = pinnedX τ k β c * pinnedX τ k β d :=
    fun c d => pinnedX_add τ k β c d
  have hB'add : ∀ c d : k, pinnedX τ k (θ β) (c + d) =
      pinnedX τ k (θ β) c * pinnedX τ k (θ β) d := fun c d => pinnedX_add τ k (θ β) c d
  have hDadd : ∀ c d : k, pinnedX τ k γ (c + d) = pinnedX τ k γ c * pinnedX τ k γ d :=
    fun c d => pinnedX_add τ k γ c d
  have hD'add : ∀ c d : k, pinnedX τ k (θ γ) (c + d) =
      pinnedX τ k (θ γ) c * pinnedX τ k (θ γ) d := fun c d => pinnedX_add τ k (θ γ) c d
  have hEadd : ∀ c d : k, pinnedX τ k (β + γ) (c + d) =
      pinnedX τ k (β + γ) c * pinnedX τ k (β + γ) d := fun c d => pinnedX_add τ k (β + γ) c d
  have hBXm : ∀ c : k, pinnedX τ k β c ∈ adjointGroup τ k := fun c => pinnedX_mem_adjointGroup β c
  have hB'Xm : ∀ c : k, pinnedX τ k (θ β) c ∈ adjointGroup τ k :=
    fun c => pinnedX_mem_adjointGroup (θ β) c
  have hDXm : ∀ c : k, pinnedX τ k γ c ∈ adjointGroup τ k := fun c => pinnedX_mem_adjointGroup γ c
  have hD'Xm : ∀ c : k, pinnedX τ k (θ γ) c ∈ adjointGroup τ k :=
    fun c => pinnedX_mem_adjointGroup (θ γ) c
  have hSBp : ∀ c : k, frobTwistGL τ k 3 1 Q (pinnedX τ k β c) =
      pinnedX τ k (θ β) (sb * c ^ 3) := fun c => by simpa using frobTwistGL_pinnedX 3 1 Q hQβ c
  have hSB'p : ∀ c : k, frobTwistGL τ k 3 1 Q (pinnedX τ k (θ β) c) =
      pinnedX τ k β (sb' * c ^ 3) := fun c => by simpa using frobTwistGL_pinnedX 3 1 Q hQβ' c
  have hSDp : ∀ c : k, frobTwistGL τ k 3 1 Q (pinnedX τ k γ c) =
      pinnedX τ k (θ γ) (sd * c ^ 3) := fun c => by simpa using frobTwistGL_pinnedX 3 1 Q hQγ c
  have hSD'p : ∀ c : k, frobTwistGL τ k 3 1 Q (pinnedX τ k (θ γ) c) =
      pinnedX τ k γ (sd' * c ^ 3) := fun c => by simpa using frobTwistGL_pinnedX 3 1 Q hQγθ c
  have hSEp : ∀ c : k, frobTwistGL τ k 3 1 Q (pinnedX τ k (β + γ) c) =
      pinnedX τ k (β + γ) (se * c ^ 3) := fun c => by simpa using frobTwistGL_pinnedX 3 1 Q hQε' c
  have hBB'c : ∀ c d : k, Commute (pinnedX τ k β c) (pinnedX τ k (θ β) d) :=
    fun c d => pinnedX_commute_of_rootsCommute hτ hβ hθβ hββ c d
  have hDD'c : ∀ c d : k, Commute (pinnedX τ k γ c) (pinnedX τ k (θ γ) d) :=
    fun c d => pinnedX_commute_of_rootsCommute hτ hγ hθγ hγγ c d
  have hBD'c : ∀ c d : k, Commute (pinnedX τ k β c) (pinnedX τ k (θ γ) d) :=
    fun c d => pinnedX_commute_of_rootsCommute hτ hβ hθγ hβθγ c d
  have hB'Dc : ∀ c d : k, Commute (pinnedX τ k (θ β) c) (pinnedX τ k γ d) :=
    fun c d => pinnedX_commute_of_rootsCommute hτ hθβ hγ hθβγ c d
  have hBDcomm : ∀ c d : k, ⁅pinnedX τ k β c, pinnedX τ k γ d⁆ =
      pinnedX τ k (β + γ) ((commConst τ β γ (1, 1) : k) * (c * d)) := hcf.2
  have hB'D'comm : ∀ c d : k, ⁅pinnedX τ k (θ β) c, pinnedX τ k (θ γ) d⁆ =
      pinnedX τ k (β + γ) ((commConst τ (θ β) (θ γ) (1, 1) : k) * (c * d)) := by
    intro c d
    rw [hcf'.2 c d, hsum]
  have hEBc : ∀ c d : k, Commute (pinnedX τ k (β + γ) c) (pinnedX τ k β d) :=
    fun c d => pinnedX_commute_of_rootsCommute hτ hβγ.2.2 hβ (hz β (by simp)) c d
  have hEB'c : ∀ c d : k, Commute (pinnedX τ k (β + γ) c) (pinnedX τ k (θ β) d) :=
    fun c d => pinnedX_commute_of_rootsCommute hτ hβγ.2.2 hθβ (hz (θ β) (by simp)) c d
  have hEDc : ∀ c d : k, Commute (pinnedX τ k (β + γ) c) (pinnedX τ k γ d) :=
    fun c d => pinnedX_commute_of_rootsCommute hτ hβγ.2.2 hγ (hz γ (by simp)) c d
  have hED'c : ∀ c d : k, Commute (pinnedX τ k (β + γ) c) (pinnedX τ k (θ γ) d) :=
    fun c d => pinnedX_commute_of_rootsCommute hτ hβγ.2.2 hθγ (hz (θ γ) (by simp)) c d
  have hEinjE : ∀ c : k, pinnedX τ k (β + γ) c = 1 → c = 0 := fun c hc =>
    pinnedX_injective τ k (β + γ) (by rw [hc, pinnedX_zero])
  exact exists_orbit_two_extraGood (X := adjointGroup τ k) (S := frobTwistGL τ k 3 1 Q)
    (B := fun c => pinnedX τ k β c) (B' := fun c => pinnedX τ k (θ β) c)
    (D := fun c => pinnedX τ k γ c) (D' := fun c => pinnedX τ k (θ γ) c)
    (E := fun c => pinnedX τ k (β + γ) c)
    (hB := hBadd) (hB' := hB'add) (hD := hDadd) (hD' := hD'add) (hE := hEadd)
    (hBX := hBXm) (hB'X := hB'Xm) (hDX := hDXm) (hD'X := hD'Xm)
    (hsb := hsb) (hsb' := hsb') (hsd := hsd) (hsd' := hsd') (hse := hse)
    (hSB := hSBp) (hSB' := hSB'p) (hSD := hSDp) (hSD' := hSD'p) (hSE := hSEp)
    (hBB' := hBB'c) (hDD' := hDD'c) (hBD' := hBD'c) (hB'D := hB'Dc)
    (hn := hn) (hn' := hn') (hBD := hBDcomm) (hB'D' := hB'D'comm)
    (hEB := hEBc) (hEB' := hEB'c) (hED := hEDc) (hED' := hED'c)
    (hEinj := hEinjE) (hlam0 := hlam0) (hlam := hlam)

private theorem twRoot_commute_orbit_three {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Type} [Field k]
    {ρ : Fin τ.rank → ℤ} (hρ : IsRoot τ ρ) {δ : Fin 3 → Fin τ.rank → ℤ}
    (hδ : ∀ i, IsRoot τ (δ i)) (hc : ∀ i, RootsCommute τ ρ (δ i)) (c a b d : k) :
    Commute (pinnedX τ k ρ c)
      (pinnedX τ k (δ 0) a * pinnedX τ k (δ 1) b * pinnedX τ k (δ 2) d) :=
  ((pinnedX_commute_of_rootsCommute hτ hρ (hδ 0) (hc 0) c a).mul_right
    (pinnedX_commute_of_rootsCommute hτ hρ (hδ 1) (hc 1) c b)).mul_right
    (pinnedX_commute_of_rootsCommute hτ hρ (hδ 2) (hc 2) c d)

theorem exists_twist_fixed_orbit_three_inv_extraGood {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Type} [Field k] [IsAlgClosed k]
    [CharP k 3] (Q : ModGL τ k) (θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (hQ : ∀ γ, IsRoot τ γ → ∃ s : k, s * s = 1 ∧
      ∀ c, Q * pinnedX τ k γ c * Q⁻¹ = pinnedX τ k (θ γ) (s * c))
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hθα : θ α = α)
    (hθβ : θ β = β) (hαβ : α ≠ β ∧ α ≠ -β ∧ IsRoot τ (α + β)) (hθε : θ (α + β) = α + β)
    (hzα : RootsCommute τ (α + β) α) (hzβ : RootsCommute τ (α + β) β)
    {δ γ : Fin 3 → Fin τ.rank → ℤ} (hδ : ∀ i, IsRoot τ (δ i)) (hγ : ∀ i, IsRoot τ (γ i))
    (hθδ : ∀ i, θ (δ i) = δ (i + 1)) (hθγ : ∀ i, θ (γ i) = γ (i + 1))
    (hsum : ∀ i, δ i + γ i = α + β) (hne : ∀ i, δ i ≠ γ i ∧ δ i ≠ -γ i)
    (hδδ : ∀ i j, i ≠ j → RootsCommute τ (δ i) (δ j))
    (hγγ : ∀ i j, i ≠ j → RootsCommute τ (γ i) (γ j))
    (hδγ : ∀ i j, i ≠ j → RootsCommute τ (δ i) (γ j))
    (hz : ∀ i, RootsCommute τ (α + β) (δ i) ∧ RootsCommute τ (α + β) (γ i))
    (hcross : ∀ i, ∀ ρ ∈ [α, β], RootsCommute τ ρ (δ i) ∧ RootsCommute τ ρ (γ i))
    {t : ModGL τ k} (htB : ∀ c, t * pinnedX τ k β c * t⁻¹ = pinnedX τ k β (-c)) :
    ∃ u : fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k 3 1 Q), orderOf u = 3 ∧
      IsExtraGood u ∧ t * (u : ModGL τ k) * t⁻¹ = (u : ModGL τ k)⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨sα, hsα, hQα⟩ := hQ α hα
  obtain ⟨sβ, hsβ, hQβ⟩ := hQ β hβ
  obtain ⟨se, hse, hQε⟩ := hQ (α + β) hαβ.2.2
  have hQα' : ∀ c, Q * pinnedX τ k α c * Q⁻¹ = pinnedX τ k α (sα * c) :=
    fun c => by rw [hQα c, hθα]
  have hQβ' : ∀ c, Q * pinnedX τ k β c * Q⁻¹ = pinnedX τ k β (sβ * c) :=
    fun c => by rw [hQβ c, hθβ]
  have hQε' : ∀ c, Q * pinnedX τ k (α + β) c * Q⁻¹ = pinnedX τ k (α + β) (se * c) :=
    fun c => by rw [hQε c, hθε]
  set N : k := (commConst τ α β (1, 1) : k) with hN
  have hcfαβ := twRoot_commutator (k := k) hτ hα hβ hαβ.1 hαβ.2.1 hαβ.2.2
  have hNsq : N * N = 1 := by
    rw [hN]
    rcases hcfαβ.1 with h' | h' <;> rw [h'] <;> norm_num
  have hN0 : N ≠ 0 := left_ne_zero_of_mul_eq_one hNsq
  have hsign : sα * sβ = se :=
    twRoot_sign_eq hτ Q hα hβ hαβ.1 hαβ.2.1 hαβ.2.2 hQα' hQβ' hQε'
  obtain ⟨la, hla⟩ := (IsAlgClosed.exists_eq_mul_self sα).imp fun _ => Eq.symm
  obtain ⟨lb, hlb⟩ := (IsAlgClosed.exists_eq_mul_self sβ).imp fun _ => Eq.symm
  have hε : IsRoot τ (α + β) := hαβ.2.2
  have hCA : ∀ c d, Commute (pinnedX τ k (α + β) (N * c)) (pinnedX τ k α d) :=
    fun c d => pinnedX_commute_of_rootsCommute hτ hε hα hzα (N * c) d
  have hCB : ∀ c d, Commute (pinnedX τ k (α + β) (N * c)) (pinnedX τ k β d) :=
    fun c d => pinnedX_commute_of_rootsCommute hτ hε hβ hzβ (N * c) d
  have hCinj : ∀ c, pinnedX τ k (α + β) (N * c) = 1 → c = 0 := fun c hc =>
    (mul_eq_zero.1 (pinnedX_injective τ k (α + β) (by rw [hc, pinnedX_zero]))).resolve_left hN0
  let ι : ZMod 3 →+* k := ZMod.castHom (dvd_refl 3) k
  obtain ⟨ι₁, hι₁, hA₁, hB₁, hZ₁⟩ :=
    exists_heis_fixed (X := adjointGroup τ k) (S := frobTwistGL τ k 3 1 Q) (K := ZMod 3)
      (ι := ι) (Nat.card_zmod 3) (A := fun c => pinnedX τ k α c)
      (B := fun c => pinnedX τ k β c) (C := fun c => pinnedX τ k (α + β) (N * c))
      (hA := fun c d => pinnedX_add τ k α c d) (hB := fun c d => pinnedX_add τ k β c d)
      (hC := fun c d => by rw [mul_add, pinnedX_add])
      (hAX := fun c => pinnedX_mem_adjointGroup α c)
      (hBX := fun c => pinnedX_mem_adjointGroup β c) (hsa := hsα) (hsb := hsβ)
      (hSA := fun c => by simpa using frobTwistGL_pinnedX 3 1 Q hQα' c)
      (hSB := fun c => by simpa using frobTwistGL_pinnedX 3 1 Q hQβ' c)
      (hAB := fun c d => by rw [hcfαβ.2 c d])
      (hCA := hCA) (hCB := hCB) (hCinj := hCinj)
      (hla := hla) (hlb := hlb)
  choose s hs hQδ using fun i => hQ (δ i) (hδ i)
  have hQδ' : ∀ i c, Q * pinnedX τ k (δ i) c * Q⁻¹ =
      pinnedX τ k (δ (i + 1)) (s i * c) := fun i c => by rw [hQδ i c, hθδ i]
  choose t ht hQγ using fun i => hQ (γ i) (hγ i)
  have hQγ' : ∀ i c, Q * pinnedX τ k (γ i) c * Q⁻¹ =
      pinnedX τ k (γ (i + 1)) (t i * c) := fun i c => by rw [hQγ i c, hθγ i]
  let n : Fin 3 → k := fun i => (commConst τ (δ i) (γ i) (1, 1) : k)
  have hcfδγ : ∀ i, (commConst τ (δ i) (γ i) (1, 1) = 1 ∨
      commConst τ (δ i) (γ i) (1, 1) = -1) ∧
      ∀ c d : k, ⁅pinnedX τ k (δ i) c, pinnedX τ k (γ i) d⁆ =
        pinnedX τ k (δ i + γ i)
          ((commConst τ (δ i) (γ i) (1, 1) : k) * (c * d)) :=
    fun i => twRoot_commutator hτ (hδ i) (hγ i) (hne i).1 (hne i).2
      (by rw [hsum i]; exact hαβ.2.2)
  have hnsq : ∀ i, n i * n i = 1 := by
    intro i
    show (commConst τ (δ i) (γ i) (1, 1) : k) *
      (commConst τ (δ i) (γ i) (1, 1) : k) = 1
    rcases (hcfδγ i).1 with h' | h' <;> rw [h'] <;> norm_num
  have hBDi : ∀ i c d, ⁅pinnedX τ k (δ i) c, pinnedX τ k (γ i) d⁆ =
      pinnedX τ k (α + β) (n i * (c * d)) := by
    intro i c d
    show ⁅pinnedX τ k (δ i) c, pinnedX τ k (γ i) d⁆ =
      pinnedX τ k (α + β) ((commConst τ (δ i) (γ i) (1, 1) : k) * (c * d))
    rw [(hcfδγ i).2 c d, hsum i]
  have hBB : ∀ i j c d, Commute (pinnedX τ k (δ i) c) (pinnedX τ k (δ j) d) := by
    intro i j c d
    rcases eq_or_ne i j with rfl | hij
    · show pinnedX τ k (δ i) c * pinnedX τ k (δ i) d =
        pinnedX τ k (δ i) d * pinnedX τ k (δ i) c
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    · exact pinnedX_commute_of_rootsCommute hτ (hδ i) (hδ j) (hδδ i j hij) c d
  have hDD : ∀ i j c d, Commute (pinnedX τ k (γ i) c) (pinnedX τ k (γ j) d) := by
    intro i j c d
    rcases eq_or_ne i j with rfl | hij
    · show pinnedX τ k (γ i) c * pinnedX τ k (γ i) d =
        pinnedX τ k (γ i) d * pinnedX τ k (γ i) c
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    · exact pinnedX_commute_of_rootsCommute hτ (hγ i) (hγ j) (hγγ i j hij) c d
  have hBD : ∀ i j c d, i ≠ j →
      Commute (pinnedX τ k (δ i) c) (pinnedX τ k (γ j) d) :=
    fun i j c d hij => pinnedX_commute_of_rootsCommute hτ (hδ i) (hγ j)
      (hδγ i j hij) c d
  have hEB : ∀ i c d, Commute (pinnedX τ k (α + β) c) (pinnedX τ k (δ i) d) :=
    fun i c d => pinnedX_commute_of_rootsCommute hτ hε (hδ i) (hz i).1 c d
  have hED : ∀ i c d, Commute (pinnedX τ k (α + β) c) (pinnedX τ k (γ i) d) :=
    fun i c d => pinnedX_commute_of_rootsCommute hτ hε (hγ i) (hz i).2 c d
  have hEinj : ∀ c, pinnedX τ k (α + β) c = 1 → c = 0 := fun c hc =>
    pinnedX_injective τ k (α + β) (by rw [hc, pinnedX_zero])
  obtain ⟨lam, hlam26⟩ :=
    IsAlgClosed.exists_pow_nat_eq (s 0 * s 1 * s 2) (n := 26) (by norm_num)
  have hlam : lam ^ 27 = lam * (s 0 * s 1 * s 2) := by
    rw [show (27 : ℕ) = 26 + 1 by norm_num, pow_succ, hlam26]
    ring
  have hlam0 : lam ≠ 0 := ne_zero_pow (by norm_num : 26 ≠ 0) <| hlam26 ▸
    mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul_eq_one (hs 0))
      (left_ne_zero_of_mul_eq_one (hs 1))) (left_ne_zero_of_mul_eq_one (hs 2))
  set w : k := N * la * lb with hw
  have hww : w * w = se := by
    rw [hw]
    have h1 : (N * la * lb) * (N * la * lb) = (N * N) * (la * la) * (lb * lb) := by
      ring
    rw [h1, hNsq, hla, hlb, one_mul, hsign]
  obtain ⟨mu, ι₂, hι₂, hA₂, hB₂, hZ₂⟩ :=
    exists_heis_orbit_three_center (X := adjointGroup τ k) (S := frobTwistGL τ k 3 1 Q)
      (K := ZMod 3) (k := k) (ι := ι) (Nat.card_zmod 3)
      (B := fun i c => pinnedX τ k (δ i) c)
      (D := fun i c => pinnedX τ k (γ i) c)
      (E := fun c => pinnedX τ k (α + β) c)
      (hB := fun i c d => pinnedX_add τ k (δ i) c d)
      (hD := fun i c d => pinnedX_add τ k (γ i) c d)
      (hE := fun c d => pinnedX_add τ k (α + β) c d)
      (hBX := fun i c => pinnedX_mem_adjointGroup (δ i) c)
      (hDX := fun i c => pinnedX_mem_adjointGroup (γ i) c)
      (s := s) (t := t) (n := n) (se := se)
      (hs := hs) (ht := ht) (hse := hse) (hn := hnsq)
      (hSB := fun i c => by simpa using frobTwistGL_pinnedX 3 1 Q (hQδ' i) c)
      (hSD := fun i c => by simpa using frobTwistGL_pinnedX 3 1 Q (hQγ' i) c)
      (hSE := fun c => by simpa using frobTwistGL_pinnedX 3 1 Q hQε' c)
      (hBB := hBB) (hDD := hDD) (hBD := hBD) (hBDi := hBDi)
      (hEB := hEB) (hED := hED) (hEinj := hEinj)
      (hlam0 := hlam0) (hlam := hlam) (hw := hww)
  have hcen : ∀ r, ι₁ ⟨0, 0, r⟩ = ι₂ ⟨0, 0, r⟩ := by
    intro r
    apply Subtype.ext
    rw [hZ₁ r, hZ₂ r]
    congr 1
    rw [hw]
    ring
  have hcαδ : ∀ i, RootsCommute τ α (δ i) := fun i => (hcross i α (by simp)).1
  have hcαγ : ∀ i, RootsCommute τ α (γ i) := fun i => (hcross i α (by simp)).2
  have hcβδ : ∀ i, RootsCommute τ β (δ i) := fun i => (hcross i β (by simp)).1
  have hcβγ : ∀ i, RootsCommute τ β (γ i) := fun i => (hcross i β (by simp)).2
  have hcomm : ∀ a b, Commute (ι₁ a) (ι₂ b) :=
    commute_heis_of_axes hcen
      (fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hA₁ x, hA₂ y]
        exact twRoot_commute_orbit_three hτ hα hδ hcαδ (la * ι x)
          (lam * ι y) (s 0 * lam ^ 3 * ι y) (s 0 * s 1 * lam ^ 9 * ι y))
      (fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hA₁ x, hB₂ y]
        exact twRoot_commute_orbit_three hτ hα hγ hcαγ (la * ι x)
          (mu * ι y) (t 0 * mu ^ 3 * ι y) (t 0 * t 1 * mu ^ 9 * ι y))
      (fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hB₁ x, hA₂ y]
        exact twRoot_commute_orbit_three hτ hβ hδ hcβδ (lb * ι x)
          (lam * ι y) (s 0 * lam ^ 3 * ι y) (s 0 * s 1 * lam ^ 9 * ι y))
      (fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hB₁ x, hB₂ y]
        exact twRoot_commute_orbit_three hτ hβ hγ hcβγ (lb * ι x)
          (mu * ι y) (t 0 * mu ^ 3 * ι y) (t 0 * t 1 * mu ^ 9 * ι y))
  have huG : ((ι₁ ⟨0, 1, 0⟩ : fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k 3 1 Q)) :
      ModGL τ k) = pinnedX τ k β lb := by
    rw [hB₁ 1]
    simp
  refine ⟨ι₁ ⟨0, 1, 0⟩, ?_, ?_, ?_⟩
  · have h := orderOf_injective ι₁ hι₁ (⟨0, 1, 0⟩ : Heis (ZMod 3))
    rw [h]
    refine orderOf_eq_prime ?_ ?_
    · exact Heis.pow_prime_eq_one Nat.prime_three (by norm_num) (⟨0, 1, 0⟩ : Heis (ZMod 3))
    · intro h
      exact one_ne_zero (congrArg Heis.b h)
  · exact isExtraGood_of_heis_pair (Nat.card_zmod 3) hι₁ hι₂ hcomm hcen ⟨0, 1, 0⟩
  · rw [huG, htB lb, pinnedX_neg]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
