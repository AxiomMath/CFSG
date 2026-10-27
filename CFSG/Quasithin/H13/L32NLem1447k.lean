module

public import CFSG.Quasithin.H13.L32NLem1447h
public import CFSG.Quasithin.H13.L32NLem1447i
public import CFSG.Quasithin.H13.L32NLem1447j
public import CFSG.Quasithin.H13.L32NLemE8b
public import CFSG.Quasithin.H13.L32NItems144e
public import CFSG.Quasithin.H13.L32NLem1447f

public section

namespace CFSG.Quasithin.H13.L1447

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L144B


theorem facts_of_lemma1442 (h1442 : Lemma1442Big) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G}
    {g : G} (h : Hyp14310One G T L V) (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V))
    (hU32 : Nat.card ↥(fsuU T V) ≠ 2 ^ 5) (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V)
    (hgH : g ∉ l32nH T V) : F1 T V V₂ ∧ F2 T V V₂ g ∧ F3 T V V₂ g := by
  have h12811 := lemma12_8_11_of h1222 h12213
  have h12812 := lemma12_8_12_two_of h1222 h12213
  have B := exists_base h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext hV₂ hgP hgH
  obtain ⟨D⟩ := B.s1282.exists_hatModelU B.h1222 h12213
  rcases h1442 G T L V h hext hU32 V₂ g hV₂ hgP hgH D with h3 | h4 | h8 | h5 | h6
  · obtain ⟨e, c, C⟩ := exists_ctx3 B h3
    exact facts_of_ctx3 h12213 C
  · obtain ⟨e, C⟩ := L14411.exists_ctx h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext
      hV₂ hgP hgH h4
    exact facts_of_ctx4 B h12213 C
  · exact (L1442E8.false_of_case1442EightPrime h1332 h1334 h1222 h12213 h12811
      (lemma12_8_11_hat_of h1222 h12213) h12812 h37 h38 h39 h hext hV₂ hgP hgH h8).elim
  · obtain ⟨b₁, b₂, e₀, hiso, hW8⟩ := h5
    cases b₂ with
    | false => exact facts_of_caseA B h12213 hiso hW8
    | true =>
      cases b₁ with
      | false =>
        exact (L14410.false_of_A5 h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext hV₂
          hgP hgH hiso hW8).elim
      | true =>
        obtain ⟨e, C⟩ := L14410.exists_ctx5 h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h
          hext hV₂ hgP hgH hiso hW8
        exact facts_of_ctx5 h12213 C
  · obtain ⟨e₀, hiso, hW32⟩ := h6
    obtain ⟨e, C⟩ := L14412.exists_ctx6 h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext
      hV₂ hgP hgH hiso hW32
    exact facts_of_ctx6 h12213 C

theorem lemma1447Big_of_inputs (h1442 : Lemma1442Big) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) : Lemma1447Big := by
  intro G _ _ T L V h hext hU32
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, g, hV₂, hgP, hgH⟩ := h.exists_plane_and_g h13322 hV (exist1282g h1222)
  have B := exists_base h1332 h1334 h1222 h12213 (lemma12_8_11_of h1222 h12213)
    (lemma12_8_12_two_of h1222 h12213) h37 h38 h39 h hext hV₂ hgP hgH
  obtain ⟨hF1, hF2, -⟩ := facts_of_lemma1442 h1442 h1332 h1334 h1222 h12213 h37 h38 h39 h hext
    hU32 hV₂ hgP hgH
  have hgH' : g⁻¹ ∉ l32nH T V := fun h' => hgH (by
    have := (l32nH T V).inv_mem h'
    rwa [inv_inv] at this)
  obtain ⟨-, -, hF3⟩ := facts_of_lemma1442 h1442 h1332 h1334 h1222 h12213 h37 h38 h39 h hext
    hU32 hV₂ ((p128 T L V).inv_mem hgP) hgH'
  exact B.fsuU_eq_pCoreOf_of_F h12213 hF1 hF2 hF3

end CFSG.Quasithin.H13.L1447
