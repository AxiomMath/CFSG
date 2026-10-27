module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec32A
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aMonomial

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.nor_X_line_monomial (h : FF81Hyp b L)
    (hTF : KF_Sp6TorusFree) (hOut : KF_Sp62Out)
    {b₁ b₂ b₃ : G} (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hself : L ⊓ CenS (Subgroup.closure ({b₁, b₂, b₃} : Set G)) =
      Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hmono : ∀ n ∈ L, n ∈ Nor (Subgroup.closure ({b₁, b₂, b₃} : Set G)) →
      ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 27)
    (hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₁B : b₁ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₂B : b₂ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₃B : b₃ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    {σ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))}
    (hσX : σ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    (hσline : σ ⟨b, hbB⟩ = ⟨b, hbB⟩ ∨ σ ⟨b, hbB⟩ = (⟨b, hbB⟩)⁻¹) :
    (∃ j : Fin 3, ∃ ε : ℤ, σ ⟨b₁, hb₁B⟩ =
      (match j with | 0 => ⟨b₁,hb₁B⟩ | 1 => ⟨b₂,hb₂B⟩ | 2 => ⟨b₃,hb₃B⟩) ^ ε) ∧
    (∃ j : Fin 3, ∃ ε : ℤ, σ ⟨b₂, hb₂B⟩ =
      (match j with | 0 => ⟨b₁,hb₁B⟩ | 1 => ⟨b₂,hb₂B⟩ | 2 => ⟨b₃,hb₃B⟩) ^ ε) ∧
    (∃ j : Fin 3, ∃ ε : ℤ, σ ⟨b₃, hb₃B⟩ =
      (match j with | 0 => ⟨b₁,hb₁B⟩ | 1 => ⟨b₂,hb₂B⟩ | 2 => ⟨b₃,hb₃B⟩) ^ ε) := by
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  let B₁ : Subgroup G := Subgroup.closure ({b₁, b₂, b₃} : Set G)
  have hB : B = Subgroup.zpowers b ⊔ B₁ := closure_four_eq b b₁ b₂ b₃
  have hB₁L : B₁ ≤ L := by
    change Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ L
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    exacts [hb₁, hb₂, hb₃]
  have hB₁B : B₁ ≤ B := by
    rw [hB]
    exact le_sup_right
  have hB4 : IsElemAb 3 4 B := h.isElemAb_B hE hB₁L
  have hBC : B ≤ Cen b := by
    rw [hB]
    exact sup_le (Subgroup.zpowers_le.mpr (b_mem_cen b)) (hB₁L.trans h.hLC)
  have hcenOdd : Odd (Nat.card ↥(CenS B)) := h.odd_cenS hTF hrk hB4 hbB hBC
  have hDB : Cen b ⊓ CenS L ≤ CenS B := fun y hy => by
    have hle : B ≤ Cen y := by
      rw [hB]
      refine sup_le (Subgroup.zpowers_le.mpr ?_)
        (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hy.2 z (hB₁L hz)))
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hy.1).symm
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hDodd : Odd (Nat.card ↥(Cen b ⊓ CenS L)) :=
    Odd.of_dvd_nat hcenOdd (Subgroup.card_dvd_of_le hDB)
  obtain ⟨n, hn_eq⟩ := mem_FF81X_iff.mp hσX
  have hσcoe : ∀ x : ↥B, ((σ x : ↥B) : G) = (n : G) * (x : G) * (n : G)⁻¹ := by
    intro x
    rw [← hn_eq]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe B n x
  have hnb : (n : G) * b * (n : G)⁻¹ = b ∨ (n : G) * b * (n : G)⁻¹ = b⁻¹ := by
    rcases hσline with h | h
    · left
      have h' := congrArg Subtype.val h
      rw [hσcoe] at h'
      simpa using h'
    · right
      have h' := congrArg Subtype.val h
      rw [hσcoe] at h'
      simpa using h'
  have hnL : (n : G) ∈ Nor L := h.mem_nor_L hDodd hnb
  obtain ⟨l, hlL, hact⟩ := hOut G L h.model (n : G) hnL
  let d : G := l⁻¹ * (n : G)
  have hnd : (n : G) = l * d := by
    dsimp [d]
    group
  have hdconj : ∀ x : G, x ∈ L → d * x * d⁻¹ = x := by
    intro x hx
    calc d * x * d⁻¹ = l⁻¹ * ((n : G) * x * (n : G)⁻¹) * l := by
          dsimp [d]
          group
      _ = l⁻¹ * (l * x * l⁻¹) * l := by rw [hact x hx]
      _ = x := by group
  have hdb : d * b * d⁻¹ = b ∨ d * b * d⁻¹ = b⁻¹ := by
    have hdn : d * b * d⁻¹ = l⁻¹ * ((n : G) * b * (n : G)⁻¹) * l := by
      dsimp [d]
      group
    rw [hdn]
    have hlb : Commute l b := Subgroup.mem_centralizer_singleton_iff.mp (h.hLC hlL)
    rcases hnb with hb' | hb'
    · left
      rw [hb']
      exact hlb.inv_mul_cancel
    · right
      rw [hb']
      exact hlb.inv_right.inv_mul_cancel
  have hdNorB : d ∈ Nor B := by
    change d ∈ Nor (Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    refine mem_nor_of_gen ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx
    · rw [hx]
      rcases hdb with h | h <;> rw [h]
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · rw [hx, hdconj b₁ hb₁]
      exact Subgroup.subset_closure (by simp)
    · rw [hx, hdconj b₂ hb₂]
      exact Subgroup.subset_closure (by simp)
    · rw [hx, hdconj b₃ hb₃]
      exact Subgroup.subset_closure (by simp)
  have hlNorB : l ∈ Nor B := by
    have hl_eq : l = (n : G) * d⁻¹ := by
      rw [hnd]
      group
    rw [hl_eq]
    exact (Nor B).mul_mem n.2 ((Nor B).inv_mem hdNorB)
  have hlNorL : l ∈ Nor L := h.hLN (h.hLC hlL)
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB4.1.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hBinfL : B ⊓ L = B₁ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      exact le_of_selfcen hBcomm hB₁B hself hx.1 hx.2
    · intro x hx
      exact ⟨hB₁B hx, hB₁L hx⟩
  have hlNorB₁ : l ∈ Nor B₁ := by
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    rw [← hBinfL, Subgroup.mem_inf, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨(Subgroup.mem_normalizer_iff.mp hlNorB x).mp hx.1,
        (Subgroup.mem_normalizer_iff.mp hlNorL x).mp hx.2⟩,
      fun hx => ⟨(Subgroup.mem_normalizer_iff.mp hlNorB x).mpr hx.1,
        (Subgroup.mem_normalizer_iff.mp hlNorL x).mpr hx.2⟩⟩
  have key : ∀ (x : G) (hxB : x ∈ B), x ∈ ({b₁, b₂, b₃} : Set G) →
      ∃ j : Fin 3, ∃ ε : ℤ, σ ⟨x, hxB⟩ =
        (match j with | 0 => ⟨b₁,hb₁B⟩ | 1 => ⟨b₂,hb₂B⟩ | 2 => ⟨b₃,hb₃B⟩) ^ ε := by
    intro x hxB hx
    have hmem := hmono l hlL hlNorB₁ x hx
    have hσx : ((σ ⟨x, hxB⟩ : ↥B) : G) = l * x * l⁻¹ := by
      rw [hσcoe]
      exact hact x (hB₁L (Subgroup.subset_closure hx))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h | h | h
    · exact ⟨0, 1, by apply Subtype.ext; rw [hσx, h]; simp⟩
    · exact ⟨0, -1, by apply Subtype.ext; rw [hσx, h]; simp⟩
    · exact ⟨1, 1, by apply Subtype.ext; rw [hσx, h]; simp⟩
    · exact ⟨1, -1, by apply Subtype.ext; rw [hσx, h]; simp⟩
    · exact ⟨2, 1, by apply Subtype.ext; rw [hσx, h]; simp⟩
    · exact ⟨2, -1, by apply Subtype.ext; rw [hσx, h]; simp⟩
  exact ⟨key b₁ hb₁B (by simp), key b₂ hb₂B (by simp), key b₃ hb₃B (by simp)⟩

theorem FF81Hyp.nor_X_line_le_cen_tau (h : FF81Hyp b L)
    (hTF : KF_Sp6TorusFree) (hOut : KF_Sp62Out)
    {τ b₁ b₂ b₃ : G} (hτL : τ ∈ L) (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hself : L ⊓ CenS (Subgroup.closure ({b₁, b₂, b₃} : Set G)) =
      Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hmono : ∀ n ∈ L, n ∈ Nor (Subgroup.closure ({b₁, b₂, b₃} : Set G)) →
      ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 27)
    (hτ2o : orderOf τ = 2) (hb : τ * b * τ⁻¹ = b)
    (hinv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹)
    (hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₁B : b₁ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₂B : b₂ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₃B : b₃ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hτN : τ ∈ Nor (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    {σ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))}
    (hσX : σ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    (hσline : σ ⟨b, hbB⟩ = ⟨b, hbB⟩ ∨ σ ⟨b, hbB⟩ = (⟨b, hbB⟩)⁻¹) :
    σ * FF81X.tau hτN = FF81X.tau hτN * σ := by
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  have hmonoσ := FF81Hyp.nor_X_line_monomial h hTF hOut hb₁ hb₂ hb₃ hE hself hmono hrk
    hbB hb₁B hb₂B hb₃B hσX hσline
  have hτXcoe : ∀ x : ↥B, (FF81X.tau hτN x : G) = τ * (x : G) * τ⁻¹ := by
    intro x
    change ((Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩) x : G) = τ * (x : G) * τ⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hτXb : FF81X.tau hτN ⟨b, hbB⟩ = ⟨b, hbB⟩ := by
    refine Subtype.ext ?_
    rw [hτXcoe]
    simpa using hb
  have hτX₁ : FF81X.tau hτN ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹ := by
    refine Subtype.ext ?_
    rw [hτXcoe]
    simpa using hinv.1
  have hτX₂ : FF81X.tau hτN ⟨b₂, hb₂B⟩ = (⟨b₂, hb₂B⟩)⁻¹ := by
    refine Subtype.ext ?_
    rw [hτXcoe]
    simpa using hinv.2.1
  have hτX₃ : FF81X.tau hτN ⟨b₃, hb₃B⟩ = (⟨b₃, hb₃B⟩)⁻¹ := by
    refine Subtype.ext ?_
    rw [hτXcoe]
    simpa using hinv.2.2
  exact mulAut_commute_tau_of_monomial hbB hb₁B hb₂B hb₃B rfl hτXb hτX₁ hτX₂ hτX₃
    hσline hmonoσ.1 hmonoσ.2.1 hmonoσ.2.2

end CFSG.RankThree.PartTwo.Sec21.FF81
