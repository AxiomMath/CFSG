module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113D42Four
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113D42Mod
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Main
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113F5113
public import CFSG.Quasithin.Background.A318PFacts2
public import CFSG.Quasithin.Background.A318PQR2
public import CFSG.Quasithin.EmptyFaithful.R3c18WD4
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace Main513

variable {G : Type} [Group G] [Finite G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem atCZ_d42 (m : Main513 G T M L V H B D K₁ X Kh₁ n) (h37 : Vol2Native.A37ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (ty : Type3D4 T D X (conjClosure Kh₁ T) (oTwoUpper H))
    (h4 : conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    {Kz₁ : Subgroup G}
    (hz : IsHatComp (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) K₁ Kz₁) :
    Main513 G T M L V H B D K₁ (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) Kz₁ n ∧
      Kh₁ ≤ Kz₁ := by
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set X' := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hX'def
  obtain ⟨hX', hSX'⟩ := m.inH_centralizer h4
  have hTX : T ≤ X := m.hyp.hStar.1.1.trans m.inH.1
  have hKhX' : Kh₁ ≤ X' := (le_conjClosure Kh₁ T).trans h4
  have hKhL : Kh₁ ∈ lFamily T := cComp_subset_lFamily hTX m.hat.1
  obtain ⟨L', ⟨hL', hKhL'⟩, -⟩ :=
    Vol2Native.lemma_1_2_4_existsUnique hloc h37 h39 hX'.2 hSX' hKhX' hKhL
  have hL'z : L' = Kz₁ := hz.2.2 L' hL' (m.hat.2.1.trans hKhL')
  subst hL'z
  have hlt' : oTwoUpper H < conjClosure L' T :=
    lt_of_lt_of_le m.lt (conjClosure_mono hKhL' le_rfl)
  obtain ⟨-, -, D₃, hD₃, -, hD₃K, -⟩ := ty
  have hnot' : ¬ D ⊓ X' ≤ Subgroup.normalizer (oTwoUpper H : Set G) := fun hle =>
    hD₃K ((le_inf (hD₃.trans inf_le_left) (hD₃.trans (inf_le_right.trans h4))).trans hle)
  exact ⟨⟨m.hyp, m.nota, m.module, m.comp, m.closure, hX', hz, hlt', hnot'⟩, hKhL'⟩

end Main513

theorem stmt5_1_13_lie_D42C_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (hF : FactF5113) (h5171 : A5.Stmt5_1_7_one) (h51 : AsB51) (h5112 : Stmt5_1_12)
    (h513 : Stmt5_1_3) (h432 : Stmt4_3_2) : Stmt5_1_13_lie_D42C := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n k hyp hN hk hV hK₁ hKeq hX hhat hlt htype hres
  by_cases hDK : D ⊓ X ≤ Subgroup.normalizer (oTwoUpper H : Set G)
  · exact Or.inl hDK
  right
  have m : Main513 G T M L V H B D K₁ X Kh₁ n := ⟨hyp, hN, hV, hK₁, hKeq, hX, hhat, hlt, hDK⟩
  obtain ⟨hL8, ty⟩ := m.type3D4 hF318 h36 (a38ForSQTK_of_cat h38) h37 h38 hk htype hres
  have e := m.toEmb512 hk
  have heq : K₁ = oTwoUpper H := e.eq_of_isSimpleGroup (isSimpleGroup_of_lieModel_PSL2 hL8)
  have h4 := m.hat_le_centralizer_d42 h5171 h51 h37 h38 hF h5112 hk heq hL8 ty
  obtain ⟨Kz₁, hz⟩ := m.exists_hat_centralizer h37 h39 h4
  obtain ⟨m', -⟩ := m.atCZ_d42 h37 h39 ty h4 hz
  obtain ⟨htype', hres'⟩ := m'.residual_at h37 h38 hF h5112 hk heq hL8
  obtain ⟨-, ty'⟩ := m'.type3D4 hF318 h36 (a38ForSQTK_of_cat h38) h37 h38 hk htype' hres'
  obtain ⟨hn2, hA5⟩ := m'.mod_d42 h513 h432 ty' rfl
  obtain ⟨hD4', hres3, -⟩ := ty'
  refine ⟨hL8, hn2, hA5, ?_, ?_⟩
  · rw [← hres3]
    exact m'.lt.le
  · have htr : ∀ A B : Subgroup G, A = B → Is3D4 2 1 (O2Q A) → Is3D4 2 1 (O2Q B) := by
      rintro A B rfl hA
      exact hA
    exact htr _ _ hres3 hD4'

theorem stmt5_1_13_lie_D42C_of_inputs
    (h5171 : A5.Stmt5_1_7_one) (h51 : AsB51) (h5112 : Stmt5_1_12) (h513 : Stmt5_1_3)
    (h432 : Stmt4_3_2) : Stmt5_1_13_lie_D42C :=
  stmt5_1_13_lie_D42C_of Vol2Native.a37ForSQTKCat_proved
    (Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)
    Vol2Native.a39ForSQTKCat_proved (a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds)
    VolI.a36ForSQTK_holds F5113.factF5113_holds h5171 h51 h5112 h513 h432

end CFSG.Quasithin.H13
