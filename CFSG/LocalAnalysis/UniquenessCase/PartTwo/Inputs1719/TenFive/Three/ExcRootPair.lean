module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Map
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcHeis
public import CFSG.LieType.Steinberg.Adjoint.ChevExtras
public import CFSG.Blueprint.ChevalleyRootArtifact
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open scoped commutatorElement

private theorem heis_eq_mul_axes {F : Type*} [CommRing F] (a b c : F) :
    (⟨a, b, c⟩ : Heis F) = ⟨0, b, 0⟩ * ⟨a, 0, 0⟩ * ⟨0, 0, c⟩ := by
  ext <;> simp

theorem commute_heis_of_axes {F S : Type*} [CommRing F] [Group S] {ι₁ ι₂ : Heis F →* S}
    (hcen : ∀ c, ι₁ ⟨0, 0, c⟩ = ι₂ ⟨0, 0, c⟩)
    (haa : ∀ s t, Commute (ι₁ ⟨s, 0, 0⟩) (ι₂ ⟨t, 0, 0⟩))
    (hab : ∀ s t, Commute (ι₁ ⟨s, 0, 0⟩) (ι₂ ⟨0, t, 0⟩))
    (hba : ∀ s t, Commute (ι₁ ⟨0, s, 0⟩) (ι₂ ⟨t, 0, 0⟩))
    (hbb : ∀ s t, Commute (ι₁ ⟨0, s, 0⟩) (ι₂ ⟨0, t, 0⟩)) (x y : Heis F) :
    Commute (ι₁ x) (ι₂ y) := by
  have hc : ∀ (c : F) (z : Heis F), Commute (⟨0, 0, c⟩ : Heis F) z := fun c z =>
    ((Subgroup.mem_center_iff.mp (Heis.mem_center.mpr ⟨rfl, rfl⟩)) z).symm
  have hz₁ : ∀ c y, Commute (ι₁ ⟨0, 0, c⟩) (ι₂ y) := fun c y => by
    rw [hcen]
    exact (hc c y).map ι₂
  have hz₂ : ∀ x c, Commute (ι₁ x) (ι₂ ⟨0, 0, c⟩) := fun x c => by
    rw [← hcen]
    exact ((hc c x).map ι₁).symm
  have hy : ∀ w : S, (∀ t, Commute w (ι₂ ⟨t, 0, 0⟩)) → (∀ t, Commute w (ι₂ ⟨0, t, 0⟩)) →
      (∀ t, Commute w (ι₂ ⟨0, 0, t⟩)) → Commute w (ι₂ y) := by
    intro w h1 h2 h3
    obtain ⟨a, b, c⟩ := y
    rw [heis_eq_mul_axes, map_mul, map_mul]
    exact ((h2 b).mul_right (h1 a)).mul_right (h3 c)
  obtain ⟨a, b, c⟩ := x
  rw [heis_eq_mul_axes, map_mul, map_mul]
  exact ((hy _ (hba b) (hbb b) (hz₂ _)).mul_left (hy _ (haa a) (hab a) (hz₂ _))).mul_left
    (hz₁ c y)

structure RootPairs (τ : Tag) (γ₁ γ₂ γ₃ γ₄ : Fin τ.rank → ℤ) : Prop where
  root₁ : IsRoot τ γ₁
  root₂ : IsRoot τ γ₂
  root₃ : IsRoot τ γ₃
  root₄ : IsRoot τ γ₄
  root_add : IsRoot τ (γ₁ + γ₂)
  add_eq : γ₃ + γ₄ = γ₁ + γ₂
  ne₁₂ : γ₁ ≠ γ₂
  ne₁₂' : γ₁ ≠ -γ₂
  ne₃₄ : γ₃ ≠ γ₄
  ne₃₄' : γ₃ ≠ -γ₄
  not_root₁₂ : ¬IsRoot τ (γ₁ + 2 • γ₂)
  not_root₂₁ : ¬IsRoot τ (2 • γ₁ + γ₂)
  not_root₃₄ : ¬IsRoot τ (γ₃ + 2 • γ₄)
  not_root₄₃ : ¬IsRoot τ (2 • γ₃ + γ₄)
  ne_zero₁₂ : γ₁ + 2 • γ₂ ≠ 0
  ne_zero₂₁ : 2 • γ₁ + γ₂ ≠ 0
  ne_zero₃₄ : γ₃ + 2 • γ₄ ≠ 0
  ne_zero₄₃ : 2 • γ₃ + γ₄ ≠ 0
  cross : ∀ u ∈ [γ₁, γ₂], ∀ v ∈ [γ₃, γ₄], u + v ≠ 0 ∧ ¬IsRoot τ (u + v)

@[expose] def rootPairsCheck (τ : Tag) (γ₁ γ₂ γ₃ γ₄ : Fin τ.rank → ℤ) : Bool :=
  let mem : (Fin τ.rank → ℤ) → Bool := fun v => decide (List.ofFn v ∈ τ.artifactRoots)
  let nz : (Fin τ.rank → ℤ) → Bool := fun v =>
    decide (List.ofFn v ≠ List.ofFn (0 : Fin τ.rank → ℤ))
  let ne : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → Bool := fun v w =>
    decide (List.ofFn v ≠ List.ofFn w)
  mem γ₁ && mem γ₂ && mem γ₃ && mem γ₄ && mem (γ₁ + γ₂) &&
    decide (List.ofFn (γ₃ + γ₄) = List.ofFn (γ₁ + γ₂)) &&
    ne γ₁ γ₂ && ne γ₁ (-γ₂) && ne γ₃ γ₄ && ne γ₃ (-γ₄) &&
    !mem (γ₁ + 2 • γ₂) && !mem (2 • γ₁ + γ₂) && !mem (γ₃ + 2 • γ₄) && !mem (2 • γ₃ + γ₄) &&
    nz (γ₁ + 2 • γ₂) && nz (2 • γ₁ + γ₂) && nz (γ₃ + 2 • γ₄) && nz (2 • γ₃ + γ₄) &&
    nz (γ₁ + γ₃) && !mem (γ₁ + γ₃) && nz (γ₁ + γ₄) && !mem (γ₁ + γ₄) &&
    nz (γ₂ + γ₃) && !mem (γ₂ + γ₃) && nz (γ₂ + γ₄) && !mem (γ₂ + γ₄)

theorem RootPairs.of_check {τ : Tag}
    {γ₁ γ₂ γ₃ γ₄ : Fin τ.rank → ℤ} (h : rootPairsCheck τ γ₁ γ₂ γ₃ γ₄ = true) :
    RootPairs τ γ₁ γ₂ γ₃ γ₄ := by
  have hne : ∀ v w : Fin τ.rank → ℤ, List.ofFn v ≠ List.ofFn w → v ≠ w :=
    fun v w h e => h (by rw [e])
  simp only [rootPairsCheck, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_true_eq, decide_eq_false_iff_not, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26⟩ := h
  have hr : ∀ v : Fin τ.rank → ℤ, List.ofFn v ∈ τ.artifactRoots → IsRoot τ v :=
    fun v hv => isRoot_iff_mem_artifactRoots.2 hv
  have hnr : ∀ v : Fin τ.rank → ℤ, List.ofFn v ∉ τ.artifactRoots → ¬IsRoot τ v :=
    fun v hv h => hv (isRoot_iff_mem_artifactRoots.1 h)
  refine ⟨hr _ h1, hr _ h2, hr _ h3, hr _ h4, hr _ h5, List.ofFn_injective h6, hne _ _ h7,
    hne _ _ h8, hne _ _ h9, hne _ _ h10, hnr _ h11, hnr _ h12, hnr _ h13, hnr _ h14,
    hne _ _ h15, hne _ _ h16, hne _ _ h17, hne _ _ h18, ?_⟩
  intro u hu v hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact ⟨hne _ _ h19, hnr _ h20⟩
  · exact ⟨hne _ _ h21, hnr _ h22⟩
  · exact ⟨hne _ _ h23, hnr _ h24⟩
  · exact ⟨hne _ _ h25, hnr _ h26⟩


theorem exists_heis_xPar {τ : Tag} (F : RootOperatorFamily τ) (hτ : NoG2 τ) {D : AdjData τ}
    (hD : D.Valid) {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hs : IsRoot τ (γ + δ)) (hne : γ ≠ δ) (hne' : γ ≠ -δ)
    (h12 : ¬IsRoot τ (γ + 2 • δ)) (h21 : ¬IsRoot τ (2 • γ + δ)) (h12' : γ + 2 • δ ≠ 0)
    (h21' : 2 • γ + δ ≠ 0) :
    ∃ (c : K) (ι : Heis K →* adjointGroup τ K), Function.Injective ι ∧
      (∀ s, ι ⟨s, 0, 0⟩ = xPar F γ (c * s)) ∧ (∀ s, ι ⟨0, s, 0⟩ = xPar F δ s) ∧
      ∀ s, ι ⟨0, 0, s⟩ = xPar F (γ + δ) s := by
  classical
  set N : ℤ := RootOperatorFamily'.coeff11 F hD ⟨γ, hγ⟩ ⟨δ, hδ⟩ with hN
  have hN0 : (N : K) ≠ 0 := by
    have habs := natAbs_coeff11 F hD (α := ⟨γ, hγ⟩) (β := ⟨δ, hδ⟩)
      (fun h => hne' (by rw [show δ = -γ from h, neg_neg])) hs
    rw [← hN] at habs
    rcases habs with h | h <;> rcases Int.natAbs_eq_iff.1 h with h' | h' <;> simp [h', h2]
  let xa : K → adjointGroup τ K := fun s => xPar F γ ((N : K)⁻¹ * s)
  let xb : K → adjointGroup τ K := fun s => xPar F δ s
  let z : K → adjointGroup τ K := fun s => xPar F (γ + δ) s
  have hxa : ∀ s t, xa (s + t) = xa s * xa t := fun s t => by
    simp only [xa, mul_add, xPar_add]
  have hxb : ∀ s t, xb (s + t) = xb s * xb t := fun s t => xPar_add _ s t
  have hz : ∀ s t, z (s + t) = z s * z t := fun s t => xPar_add _ s t
  have hab : ∀ s t, ⁅xa s, xb t⁆ = z (s * t) := by
    intro s t
    simp only [xa, xb, z]
    rw [commutator_xPar hD hτ hγ hδ hne hne', xPar_of_not_isRoot h12, xPar_of_not_isRoot h21,
      mul_one, mul_one, ← hN]
    congr 1
    rw [← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
  have hγδγ : γ + δ + γ = 2 • γ + δ := by
    rw [two_nsmul]
    abel
  have hγδδ : γ + δ + δ = γ + 2 • δ := by
    rw [two_nsmul]
    abel
  have hza : ∀ s t, Commute (z s) (xa t) := fun s t =>
    commute_xPar hD hτ hs hγ (by rw [hγδγ]; exact h21') (by rw [hγδγ]; exact h21) s _
  have hzb : ∀ s t, Commute (z s) (xb t) := fun s t =>
    commute_xPar hD hτ hs hδ (by rw [hγδδ]; exact h12') (by rw [hγδδ]; exact h12) s t
  obtain ⟨ι, hι, ha, hb, hc⟩ :=
    exists_heis_of_comm hxa hxb hz (xPar_injective hs) hab hza hzb
  exact ⟨(N : K)⁻¹, ι, hι, ha, hb, hc⟩

theorem isExtraGood_xPar_mul_of_rootPairs {τ : Tag} (F : RootOperatorFamily τ) (hτ : NoG2 τ)
    {D : AdjData τ} (hD : D.Valid) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {γ₁ γ₂ γ₃ γ₄ : Fin τ.rank → ℤ} (h : RootPairs τ γ₁ γ₂ γ₃ γ₄) (s t : K) :
    IsExtraGood (xPar F γ₂ s * xPar F γ₄ t) := by
  classical
  have : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      le_rfl (by rw [hK, pow_one])
  have h2 : (2 : K) ≠ 0 := fun h0 => by
    have h3 := (CharP.cast_eq_zero_iff K 3 2).1 (by exact_mod_cast h0)
    norm_num at h3
  obtain ⟨c₁, ι₁, hι₁, ha₁, hb₁, hc₁⟩ := exists_heis_xPar F hτ hD h2 h.root₁ h.root₂ h.root_add
    h.ne₁₂ h.ne₁₂' h.not_root₁₂ h.not_root₂₁ h.ne_zero₁₂ h.ne_zero₂₁
  obtain ⟨c₂, ι₂, hι₂, ha₂, hb₂, hc₂⟩ := exists_heis_xPar F hτ hD h2 h.root₃ h.root₄
    (by rw [h.add_eq]; exact h.root_add) h.ne₃₄ h.ne₃₄' h.not_root₃₄ h.not_root₄₃ h.ne_zero₃₄
    h.ne_zero₄₃
  have hcen : ∀ c, ι₁ ⟨0, 0, c⟩ = ι₂ ⟨0, 0, c⟩ := fun c => by rw [hc₁, hc₂, h.add_eq]
  have hroot : ∀ u ∈ [γ₁, γ₂, γ₃, γ₄], IsRoot τ u := by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    exacts [h.root₁, h.root₂, h.root₃, h.root₄]
  have hcomm : ∀ u ∈ [γ₁, γ₂], ∀ v ∈ [γ₃, γ₄], ∀ a b : K,
      Commute (xPar F u a) (xPar F v b) := by
    intro u hu v hv a b
    have hu' : u ∈ [γ₁, γ₂, γ₃, γ₄] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu ⊢
      tauto
    have hv' : v ∈ [γ₁, γ₂, γ₃, γ₄] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv ⊢
      tauto
    exact commute_xPar hD hτ (hroot u hu') (hroot v hv') (h.cross u hu v hv).1
      (h.cross u hu v hv).2 a b
  have hcommι : ∀ a b, Commute (ι₁ a) (ι₂ b) := commute_heis_of_axes hcen
    (fun s t => by rw [ha₁, ha₂]; exact hcomm _ (by simp) _ (by simp) _ _)
    (fun s t => by rw [ha₁, hb₂]; exact hcomm _ (by simp) _ (by simp) _ _)
    (fun s t => by rw [hb₁, ha₂]; exact hcomm _ (by simp) _ (by simp) _ _)
    (fun s t => by rw [hb₁, hb₂]; exact hcomm _ (by simp) _ (by simp) _ _)
  have hx : xPar F γ₂ s * xPar F γ₄ t ∈ ι₁.range ⊔ ι₂.range :=
    mul_mem (Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨⟨0, s, 0⟩, hb₁ s⟩))
      (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨⟨0, t, 0⟩, hb₂ t⟩))
  exact isExtraGood_of_mem_sup_heis_pair hK hι₁ hι₂ hcommι hcen hx

theorem isExtraGood_xPar_of_rootPairs {τ : Tag} (F : RootOperatorFamily τ) (hτ : NoG2 τ)
    {D : AdjData τ} (hD : D.Valid) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {γ₁ γ₂ γ₃ γ₄ : Fin τ.rank → ℤ} (h : RootPairs τ γ₁ γ₂ γ₃ γ₄) (s : K) :
    IsExtraGood (xPar F γ₂ s) := by
  simpa only [xPar_zero, mul_one] using isExtraGood_xPar_mul_of_rootPairs F hτ hD hK h s 0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
