module

public import CFSG.Quasithin.H13.GoldschmidtC137WeakB18
public import CFSG.Quasithin.Background.B2FactorizationBaumannVar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

universe u

variable {G : Type u} [Group G]

open B2F in
theorem B2_19' [Finite G] {V L R : Subgroup G} (hV : IsElemAbelian 2 V) (hVN : V.Normal)
    (hL : L = pResidualOf 2 (⊤ : Subgroup G)) (hR : IsPGroup 2 R) (hVR : V ≤ R)
    (hA₁ : pCoreOf 2 L ≤ R ⊓ Subgroup.centralizer (V : Set G))
    (hA₂ : IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
      ((L ⊔ R) ⊓ Subgroup.centralizer (V : Set G)))
    (hA₃ : L ≤ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hB : L ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoPhi L)
    (hC : ∀ A, ¬ IsStrongFFOffender hV R A)
    (hDE : ∃ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod V hV))) (Rs : Fin n → Subgroup G),
      (∀ i, ∃ g ∈ autI hV L, B1.conjAut g (Y i) ≤ autI hV R) ∧
      (∀ i, IsSylowTwoOf (Rs i) (starPre hV hVN (L ⊔ R) (Y i))) ∧
      (∀ i, Y i = autI hV (thompsonJ (Rs i))) ∧ (∀ i, Open.pRank 2 (Rs i) = Open.pRank 2 R) ∧
      autI hV L ≤ ⨆ i, Y i ∧ ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI hV L)) ∧
      ∀ A, IsFFStarOffender (autI hV R) A →
        ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut (IntMod V hV))), A = ⨆ k, Ai k ∧
          ∀ k, IsFFStarOffender (autI hV R) (Ai k) ∧ ∃ j : Fin n, ∃ g ∈ autI hV L,
            Ai k ≤ B1.conjAut g (Y j) ∧ B1.conjAut g (Y j) ≤ autI hV R) :
    pCoreOf 2 L ≤ baum R ∧
      omegaOneCenterOf (thompsonJ R) =
        (omegaOneCenterOf (thompsonJ R) ⊓ Subgroup.centralizer (L : Set G)) ⊔
          (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) ∧
      IsSylowTwoOf (baum R ⊓ Subgroup.centralizer (V : Set G))
        ((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G)) ∧
      (IsSylowTwoOf (autI hV (baum R)) (autI hV L ⊔ autI hV (baum R)) →
        IsSylowTwoOf (baum R) (L ⊔ baum R)) := by
  have hN := mem_normalizer_of_normal hVN
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := fun g _ => hN g
  by_cases hLbot : L = ⊥
  · subst hLbot
    have hcen : Subgroup.centralizer (((⊥ : Subgroup G) : Subgroup G) : Set G) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_iff]
    have hS : IsPGroup 2 (baum R) := hR.to_le inf_le_left
    refine ⟨(pCoreOf_le 2 _).trans bot_le, ?_, ?_, ?_⟩
    · rw [hcen, inf_top_eq]
      exact (sup_eq_left.2 (inf_centralizer_thompsonJ_le hV hVR)).symm
    · rw [bot_sup_eq]
      exact ⟨le_rfl, hR.to_le (inf_le_left.trans inf_le_left), by simp⟩
    · intro _
      rw [bot_sup_eq]
      exact ⟨le_rfl, hS, by simp⟩
  · obtain ⟨n, Y, Rs, hconj, hsyl, hYJ, hrk, hLY, hsum, hE⟩ := hDE
    have hLn : L.Normal := by
      rw [hL]
      exact normal_pResidualOf_top
    have hLodd : ∀ x : G, Odd (orderOf x) → x ∈ L := fun x hx => by
      rw [hL]
      exact mem_pResidualOf_top_of_odd hx
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exfalso
        subst h0
        apply hLbot
        refine eq_bot_of_le_oTwoPhi hL ?_
        have h1 : autI hV L = ⊥ := by
          have h2 := hLY
          rw [iSup_of_empty] at h2
          exact le_bot_iff.1 h2
        have h2 : L ≤ Subgroup.centralizer (V : Set G) :=
          (autI_eq_bot_iff hV (fun x _ => hN x)).1 h1
        exact fun x hx => hB (Subgroup.mem_inf.2 ⟨hx, h2 hx⟩)
      · exact h0
    obtain ⟨X, hXdef⟩ : ∃ X : Fin n → Subgroup G, ∀ i, X i = thompsonJ (Rs i) :=
      ⟨fun i => thompsonJ (Rs i), fun i => rfl⟩
    have hYX : ∀ i, Y i = autI hV (X i) := fun i => by rw [hXdef]; exact hYJ i
    have hXJ : ∀ i, X i = thompsonJ (X i) := fun i => by
      rw [hXdef]
      exact (thompsonJ_thompsonJ _).symm
    have hXrank : ∀ i, Open.pRank 2 (X i) = Open.pRank 2 R := fun i => by
      rw [hXdef, pRank_thompsonJ, hrk]
    have hLX : autI hV L ≤ ⨆ i, autI hV (X i) :=
      hLY.trans (iSup_mono fun i => (hYX i).le)
    have hsum' : ∑ i, rkIdx (fixV (autI hV (X i))) ≤ rkIdx (fixV (autI hV L)) := by
      have h : ∀ i, autI hV (X i) = Y i := fun i => (hYX i).symm
      simp only [h]
      exact hsum
    have hXR : ∀ i, X i ≤ Rs i := fun i => by
      rw [hXdef]
      exact thompsonJ_le_self _
    have hXconj : ∀ i, ∃ l ∈ L, cjSub l (X i) ≤ R := by
      intro i
      obtain ⟨g', hg', hle⟩ := hconj i
      obtain ⟨g, hgL, rfl⟩ := (mem_autI_iff hV hN).1 hg'
      have hRsY : Rs i ≤ starPre hV hVN (L ⊔ R) (Y i) := (hsyl i).1
      have hU2 : IsPGroup 2 (cjSub g (X i)) :=
        ((isSylowTwoOf_cjSub g (hsyl i)).2.1).to_le (cjSub_mono (hXR i))
      have hUM : cjSub g (X i) ≤ L ⊔ R :=
        cjSub_le (Subgroup.le_normalizer (Subgroup.mem_sup_left hgL)) fun x hx =>
          ((mem_starPre hV hVN).1 (hRsY (hXR i hx))).1
      have hU : autI hV (cjSub g (X i)) ≤ autI hV R := by
        intro φ hφ
        obtain ⟨u, hu, rfl⟩ := (mem_autI_iff hV hN).1 hφ
        apply hle
        rw [B1.mem_conjAut]
        have h1 : starHom hV hN (g⁻¹ * u * g) ∈ Y i := by
          rw [hYX i]
          exact (mem_autI_iff hV hN).2 ⟨_, mem_cjSub.1 hu, rfl⟩
        simpa only [map_mul, map_inv] using h1
      obtain ⟨l, hl, hlR⟩ := exists_mem_L_cjSub_le hV hVN hLn hR hA₂ hU2 hUM hU
      exact ⟨l * g, L.mul_mem hl hgL, by rw [cjSub_mul]; exact hlR⟩
    obtain ⟨I, hI⟩ : ∃ I : Subgroup G, I = ⨆ i, X i := ⟨_, rfl⟩
    have hXI : ∀ i, X i ≤ I := fun i => hI ▸ le_iSup X i
    have hLI₀ : autI hV L ≤ autI hV I := by
      rw [hI, autI_iSup hV X (fun i x _ => hN x)]
      exact hLX
    have hdec := L_decomp hV hN hL hB hLI₀
    have hRQ : R ≤ Subgroup.normalizer
        ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
      le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer hRN)
    have hLRN : L ⊔ R ≤ Subgroup.normalizer
        ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := sup_le hA₃ hRQ
    have hfacts := alpha_facts' hV hVR hRN hC
    have hJQ : ∀ D, IsMaxElemAbelian (R ⊓ Subgroup.centralizer (V : Set G)) D → D ≤ I := by
      intro D hD
      have hDR : IsMaxElemAbelian R D := hfacts.1 D hD
      have hQRs := inf_centralizer_le_of_isSylow_starPre hV hVN hR hLRN (hsyl ⟨0, hn⟩)
      have hDmax : IsMaxElemAbelian (Rs ⟨0, hn⟩) D :=
        isMaxElemAbelian_of_pRank_eq hDR (hD.1.trans hQRs) (hrk _)
      have : D ≤ X ⟨0, hn⟩ := by
        rw [hXdef]
        exact le_iSup₂_of_le D hDmax le_rfl
      exact this.trans (hXI _)
    have hJI : thompsonJ R ≤ I := by
      refine iSup_le fun A => iSup_le fun hA => ?_
      by_cases hAC : A ≤ Subgroup.centralizer (V : Set G)
      · refine hJQ A ⟨le_inf hA.1 hAC, hA.2.1, fun B hB' hBe =>
          hA.2.2 B (hB'.trans inf_le_left) hBe⟩
      · have hAoff : IsFFOffender R V A := ⟨hA, hAC⟩
        have hAstar := offenderImages_isFFStarOffender hV hVR hRN
          (⟨A, hAoff, rfl⟩ : autI hV A ∈ offenderImages hV R)
        obtain ⟨r, Ai, hAeq, hAk⟩ := hE _ hAstar
        have hAN : A ≤ Subgroup.normalizer (V : Set G) := fun x _ => hN x
        have hnot : ¬ IsStrongFFOffender hV R A := hC A
        have hV2 : ∀ v : IntMod V hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
        have hle : ∀ k, Ai k ≤ autI hV A := fun k => hAeq ▸ le_iSup Ai k
        have hD : ∀ k, ∃ D, IsMaxElemAbelian R D ∧ preI hV A hAN (Ai k) ≤ D ∧
            autI hV D = Ai k := by
          intro k
          have hff := B2_8_ffLe hV hVR hRN hAoff hnot (hAk k).1.2.1 (hle k)
            (B1_4_1 hV2 (hAk k).1)
          obtain ⟨hDmax, hDeq⟩ := (offender_core hV hVR hRN hA (hle k)).2 hff.2.2.2
          exact ⟨_, hDmax, le_sup_left, hDeq⟩
        have hDI : ∀ k, ∀ D, IsMaxElemAbelian R D → autI hV D = Ai k → D ≤ I := by
          intro k D hD hDk
          obtain ⟨-, j, g', hg', hAij, -⟩ := hAk k
          obtain ⟨l, hl, rfl⟩ := (mem_autI_iff hV hN).1 hg'
          have hXIj : thompsonJ (Rs j) ≤ I := by
            rw [← hXdef j]
            exact hXI j
          exact le_I_of_offender hV hVN hLodd hdec hR hA₁ hLRN hA₂ (hsyl j) (hYJ j) (hrk j)
            hXIj hD hl (hDk ▸ hAij)
        have hne : Nonempty (Fin r) := by
          by_contra hne
          rw [not_nonempty_iff] at hne
          apply hAstar.2.1
          rw [hAeq, iSup_of_empty]
        refine (le_iSup_preI hV hN Ai hle hAeq).trans (iSup_le fun k => ?_)
        obtain ⟨D, hDmax, hBD, hDeq⟩ := hD k
        exact hBD.trans (hDI k D hDmax hDeq)
    obtain ⟨h1, h2, h3⟩ := B2_18' hV hVN hL hR hVR hA₁ hA₃ hB hC
      ⟨n, X, hXconj, hXJ, hXrank, hLX, hsum', by rw [← hI]; exact hJI⟩
    obtain ⟨h3a, h3b⟩ := h3 hA₂
    exact ⟨h1, h2, h3a, h3b⟩

end CFSG.Quasithin
