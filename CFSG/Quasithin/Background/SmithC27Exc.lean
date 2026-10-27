module

public import CFSG.Quasithin.Background.SmithC27AltSetup
public import CFSG.Quasithin.Background.SmithC27Perm2
public import CFSG.Quasithin.Background.C124YLA7Norm
public import CFSG.Quasithin.Background.C124YLA7Pkg
public import CFSG.Quasithin.Background.C124YLBaum
public import CFSG.Quasithin.Background.C124YLStab

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm C124
open CFSG.QuasithinUnique.L246.C123
open scoped Pointwise


theorem kleinP_eq_kleinRegular7 : kleinP = kleinRegular7 := by
  apply le_antisymm
  · intro g hg
    have hx : x7 ∈ kleinRegular7 := Subgroup.subset_closure (by simp [x7])
    have hy : y7 ∈ kleinRegular7 := Subgroup.subset_closure (by simp [y7])
    have hg' : g ∈ kleinSet := mem_kleinP.1 hg
    rcases (show g = 1 ∨ g = x7 ∨ g = y7 ∨ g = x7 * y7 by simpa [kleinSet] using hg') with
      rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hx
    · exact hy
    · exact Subgroup.mul_mem _ hx hy
  · rw [kleinRegular7, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact x7_mem
    · exact y7_mem

theorem map_normalizer_kleinA :
    (Subgroup.normalizer (kleinA : Set A7)).map (alternatingGroup (Fin 7)).subtype =
      quadStab 7 := by
  have h1 : Subgroup.normalizer (kleinA : Set A7) =
      (Subgroup.normalizer (kleinP : Set (Perm (Fin 7)))).subgroupOf (alternatingGroup (Fin 7)) :=
    (Subgroup.subgroupOf_normalizer_eq kleinP_le).symm
  rw [h1, Subgroup.subgroupOf_map_subtype, inf_comm, kleinP_eq_kleinRegular7,
    alt_inf_normalizer_kleinRegular7]

theorem normalizer_kleinA_le {Y : Subgroup A7} (h : Subgroup.normalizer (kleinA : Set A7) ≤ Y) :
    Y = Subgroup.normalizer (kleinA : Set A7) ∨ Y = ⊤ := by
  set ψ := (alternatingGroup (Fin 7)).subtype
  have hle : quadStab 7 ≤ Y.map ψ := by
    rw [← map_normalizer_kleinA]
    exact Subgroup.map_mono h
  rcases quadStab_overgroups (Or.inr rfl) hle (Subgroup.map_subtype_le _) with h1 | h1
  · left
    apply Subgroup.map_injective (alternatingGroup (Fin 7)).subtype_injective
    rw [h1, map_normalizer_kleinA]
  · right
    apply Subgroup.map_injective (alternatingGroup (Fin 7)).subtype_injective
    rw [h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

section Main

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G}

theorem relIndex_eq_35 (h : Hyp27 H R M K) {T : Subgroup G}
    (E : EntryPlus (K ⊔ R) T (Vc R K) K R 7 (isElemAbelian_omegaOneCenterOf _))
    (hc : CaseA7Four (isElemAbelian_omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) K 7)
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    M.relIndex K = 35 := by
  classical
  set hV := isElemAbelian_omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hhV
  obtain ⟨-, ⟨α, π, hπ⟩, -⟩ := hc
  let C : YL.A7.A7Ctx (autI hV K) (commV (autI hV K)) (fixV (autI hV K) ⊓ commV (autI hV K)) :=
    ⟨α, π, hπ⟩
  have hXN : K ⊔ R ≤ Subgroup.normalizer (Vc R K : Set G) := E.red.2.1
  have hRX : R ≤ K ⊔ R := le_sup_right
  have hRN : R ≤ Subgroup.normalizer (Vc R K : Set G) := hRX.trans hXN
  have hVR : Vc R K ≤ R := (le_pCoreOf_of_reduced E.red).trans E.QR
  have hLX : autI hV K ≤ autI hV (K ⊔ R) := autI_mono hV le_sup_left
  have hnormX : ∀ x ∈ autI hV (K ⊔ R),
      x ∈ Subgroup.normalizer (autI hV K : Set (MulAut (IntMod (Vc R K) hV))) :=
    fun x hx => L2.autI_le_normalizer_of_le_normalizer hV E.normal hx
  have hstab := fun x (hx : x ∈ autI hV (K ⊔ R)) => YL.sec_stable (hnormX x hx)
  have hXL : autI hV (K ⊔ R) ≤ autI hV K :=
    C.le_Ls_of_normalizes hLX hnormX E.fstarX (fun x hx => (hstab x hx).1)
      (fun x hx => (hstab x hx).2)
  have hRs : autI hV R ≤ autI hV K := (autI_mono hV hRX).trans hXL
  set φ := C.phi with hφdef
  have hφ : Function.Injective φ := C.phi_injective
  have hφr : φ.range = autI hV K := C.phi_range
  set R₀ : Subgroup A7 := (autI hV R).comap φ with hR₀
  have hR₀p : IsPGroup 2 R₀ := (C124.YZ.isPGroup_autI hV h.isPGroup).comap_of_injective φ hφ
  obtain ⟨T₀, hRT₀, hT₀⟩ := YL.A7.exists_sylow_ge hR₀p
  obtain ⟨g, hg⟩ := exists_conj_of_card_sylow (P := sylowA) (Q := T₀)
    (by rw [card_sylowA, fac_card_A7]; norm_num) (by rw [hT₀, fac_card_A7]; norm_num)
  set K₀ : Subgroup (MulAut (IntMod (Vc R K) hV)) := (L246.C123.conjSub g kleinA).map φ with hK₀
  have hoff : ∀ B ∈ offenderImages hV R, B = K₀ := by
    intro B hB
    obtain ⟨hw, hBR⟩ := YL.woff_of_mem_offenderImages hV hVR hRN (commV (autI hV K))
      (fixV (autI hV K) ⊓ commV (autI hV K)) hB
    have hBL : B ≤ φ.range := hφr ▸ hBR.trans hRs
    set B₀ : Subgroup A7 := B.comap φ with hB₀
    have hBB₀ : B₀.map φ = B := Subgroup.map_comap_eq_self hBL
    set B₁ : Subgroup A7 := L246.C123.conjSub g⁻¹ B₀ with hB₁
    have hB₁S : B₁ ≤ sylowA := by
      intro x hx
      have h1 : g * x * g⁻¹ ∈ B₀ := by
        have := (L246.C123.mem_conjSub (c := g⁻¹) (H := B₀) (x := x)).1 hx
        simpa using this
      have h2 : g * x * g⁻¹ ∈ T₀ := hRT₀ (hBR h1)
      have := (hg _).1 h2
      simpa [mul_assoc] using this
    have hφg : φ g ∈ autI hV K := C.phi_mem g
    have hφg' : (φ g)⁻¹ ∈ autI hV K := (autI hV K).inv_mem hφg
    have hB₁map : B₁.map φ = B1.conjAut (φ g)⁻¹ B := by
      ext y
      rw [B1.mem_conjAut, inv_inv]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h1 : g * x * g⁻¹ ∈ B₀ := by
          have := (L246.C123.mem_conjSub (c := g⁻¹) (H := B₀) (x := x)).1 hx
          simpa using this
        have : φ g * φ x * (φ g)⁻¹ = φ (g * x * g⁻¹) := by simp [map_mul, map_inv]
        rw [this]
        exact h1
      · intro hy
        have hyr : φ g * y * (φ g)⁻¹ ∈ φ.range := hBL hy
        obtain ⟨x', hx'⟩ := hyr
        refine ⟨g⁻¹ * x' * g, ?_, ?_⟩
        · rw [SetLike.mem_coe, L246.C123.mem_conjSub]
          have : g⁻¹⁻¹ * (g⁻¹ * x' * g) * g⁻¹ = x' := by group
          rw [this]
          show φ x' ∈ B
          rw [hx']
          exact hy
        · rw [map_mul, map_mul, map_inv, hx']
          group
    have hw1 : YL.WOff (commV (autI hV K)) (fixV (autI hV K) ⊓ commV (autI hV K)) (B₁.map φ) := by
      rw [hB₁map]
      exact hw.conj _ (YL.sec_stable (Subgroup.le_normalizer hφg')).1
        (YL.sec_stable (Subgroup.le_normalizer hφg')).2
    have hK : B₁.map φ = kleinA.map φ := C.unique_K (Subgroup.map_mono hB₁S) hw1
    have hB₁K : B₁ = kleinA := Subgroup.map_injective hφ hK
    have hB₀K : B₀ = L246.C123.conjSub g kleinA := by
      ext x
      rw [L246.C123.mem_conjSub, ← hB₁K, hB₁, L246.C123.mem_conjSub, inv_inv]
      constructor
      · intro hx
        simpa [mul_assoc] using hx
      · intro hx
        simpa [mul_assoc] using hx
    rw [← hBB₀, hB₀K]
  have hJ : autI hV (thompsonJ R) = K₀ := by
    apply le_antisymm
    · have h1 := autI_iSup₂ hV (P := IsMaxElemAbelian R) (fun A hA => hA.1.trans hRN)
      show autI hV (⨆ (A : Subgroup G) (_ : IsMaxElemAbelian R A), A) ≤ K₀
      rw [h1]
      refine iSup₂_le fun A hA => ?_
      by_cases hAV : A ≤ Subgroup.centralizer (Vc R K : Set G)
      · rw [autI_eq_bot_of_le_centralizer hV hAV]
        exact bot_le
      · exact (hoff _ ⟨A, ⟨hA, hAV⟩, rfl⟩).le
    · obtain ⟨B, hB⟩ := (offenderImages_nonempty_iff_not_le hV).2 E.hJ
      rw [← hoff B hB]
      obtain ⟨A, ⟨hA, -⟩, rfl⟩ := hB
      exact autI_mono hV (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ R)
  have hstar := normalizer_J_star_le h h.starHyp
  set M₀ : Subgroup A7 := (autI hV (M ⊓ K)).comap φ with hM₀
  have hNM : L246.C123.conjSub g (Subgroup.normalizer (kleinA : Set A7)) ≤ M₀ := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (L246.C123.conjSub g kleinA : Set A7) :=
      (L246.C123.normalizer_conjSub g kleinA x).2 (L246.C123.mem_conjSub.1 hx)
    have h1 : φ x ∈ Subgroup.normalizer (K₀ : Set (MulAut (IntMod (Vc R K) hV))) := by
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      obtain ⟨k, hk, rfl⟩ := hy
      refine ⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxN k).1 hk, ?_⟩
      simp [map_mul, map_inv]
    have h2 : φ x ∈ autOn K (Vc R K) ⊓
        Subgroup.normalizer (autOn (thompsonJ R) (Vc R K) : Set (MulAut ↥(Vc R K))) := by
      refine ⟨C.phi_mem x, ?_⟩
      have : autOn (thompsonJ R) (Vc R K) = K₀ := hJ
      rw [this]
      exact h1
    exact hstar h2
  have hM₀ne : M₀ ≠ ⊤ := by
    intro htop
    apply autOn_MK_ne h h.starHyp
    apply le_antisymm (autI_mono hV inf_le_right)
    intro y hy
    rw [← hφr] at hy
    obtain ⟨x, rfl⟩ := hy
    have : x ∈ M₀ := htop ▸ Subgroup.mem_top x
    exact this
  have h1 : Subgroup.normalizer (kleinA : Set A7) ≤ L246.C123.conjSub g⁻¹ M₀ := by
    intro y hy
    rw [L246.C123.mem_conjSub, inv_inv]
    apply hNM
    rw [L246.C123.mem_conjSub]
    simpa [mul_assoc] using hy
  have hcardM₀ : Nat.card M₀ = 72 := by
    rcases normalizer_kleinA_le h1 with h2 | h2
    · rw [← L246.C123.card_conjSub g⁻¹ M₀, h2, card_normalizer_kleinA]
    · exfalso
      apply hM₀ne
      rw [eq_top_iff]
      intro x _
      have : g⁻¹ * x * g ∈ L246.C123.conjSub g⁻¹ M₀ := h2 ▸ Subgroup.mem_top _
      rw [L246.C123.mem_conjSub, inv_inv] at this
      simpa [mul_assoc] using this
  have hMKr : autI hV (M ⊓ K) ≤ φ.range := hφr ▸ autI_mono hV inf_le_right
  have hcardMK : Nat.card (autI hV (M ⊓ K)) = 72 := by
    rw [← Subgroup.map_comap_eq_self hMKr, Subgroup.card_map_of_injective hφ]
    exact hcardM₀
  have hcardK : Nat.card (autI hV K) = 2520 := C.card_Ls
  have hKN : K ≤ Subgroup.normalizer (Vc R K : Set G) := le_sup_left.trans hXN
  have hKC : K ⊓ Subgroup.centralizer (Vc R K : Set G) = pCoreOf 2 K :=
    h.starHyp.inf_centralizer_eq hZ
  have hO2M : pCoreOf 2 K ≤ M := pCore_K_le_M h h.starHyp
  have hMKC : (M ⊓ K) ⊓ Subgroup.centralizer (Vc R K : Set G) =
      K ⊓ Subgroup.centralizer (Vc R K : Set G) := by
    apply le_antisymm (inf_le_inf_right _ inf_le_right)
    intro x hx
    refine ⟨⟨?_, hx.1⟩, hx.2⟩
    rw [hKC] at hx
    exact hO2M hx
  have e1 := card_eq_card_autOn_mul hKN
  have e2 := card_eq_card_autOn_mul (inf_le_right.trans hKN : M ⊓ K ≤ _)
  rw [hMKC] at e2
  have hc1 : Nat.card ↥(autOn K (Vc R K)) = 2520 := hcardK
  have hc2 : Nat.card ↥(autOn (M ⊓ K) (Vc R K)) = 72 := hcardMK
  rw [hc1] at e1
  rw [hc2] at e2
  have e3 : M.relIndex K * Nat.card ↥(M ⊓ K) = Nat.card K := by
    have h1 : Nat.card ↥(M.subgroupOf K) = Nat.card ↥(M ⊓ K) := by
      rw [← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [← h1]
    exact (M.subgroupOf K).index_mul_card
  rw [e1, e2] at e3
  have hpos : 0 < Nat.card ↥(K ⊓ Subgroup.centralizer (Vc R K : Set G)) := Nat.card_pos
  have : M.relIndex K * 72 = 2520 := by
    have := e3
    nlinarith
  omega

theorem three_of_caseA7Four (h : Hyp27 H R M K) {T : Subgroup G}
    (E : EntryPlus (K ⊔ R) T (Vc R K) K R 7 (isElemAbelian_omegaOneCenterOf _))
    (hc : CaseA7Four (isElemAbelian_omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) K 7)
    (hexc : IsExcA7Block K) : C27Three H R M K (Vc R K) := by
  obtain ⟨α, hα, hker⟩ := hexc.2.1
  have hZ := center_quot_eq_bot_of_surj (Or.inr rfl) α hα hker
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hexc, relIndex_eq_35 h E hc hZ⟩)))

end Main

end CFSG.Quasithin.SmithC27
