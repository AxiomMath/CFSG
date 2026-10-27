module

public import CFSG.Quasithin.Vol2.Ch11SecE42S3a

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecE
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G} {z : G}

abbrev LieType11 (K : Subgroup G) (n : ℕ) : Prop :=
  IsSL3 (2 ^ n) (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsPSL 3 2 n (↥K ⧸ CFSG.pCore 2 ↥K) ∨
    IsPSp4 2 n (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsG2 2 n (↥K ⧸ CFSG.pCore 2 ↥K)

omit [Finite G] in
theorem shape11_of_type {K : Subgroup G} (hK : LieType11 K n) : Shape11 K n := by
  rcases hK with ⟨F, _, _, hF, ⟨e⟩⟩ | hK | hK | hK
  · exact Or.inl ⟨F, inferInstance, inferInstance, hF,
      ⟨e.trans (specialLinearGroupEquivStatedSL 3 F).symm⟩⟩
  · exact Or.inr (Or.inl (Or.inl ⟨by decide, hK⟩))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨by decide, hK⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hK⟩))))

theorem exists_hyp11_kz (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43) (hP : SecB.PointFacts)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (hFSU : Ch10.StmtFSUChoice)
    (hc : Conf11_4_2 T L I n V₁ z) (hmax : quasithinIsMaximalLocal T (kz L V₁ z))
    (hK : LieType11 (kz L V₁ z) n) : ∃ I' : Subgroup G, Hyp11 G T (kz L V₁ z) I' n := by
  obtain ⟨I', hfsu⟩ := exists_fsu_kz hF hS hF43 hP h1102 h1110 h1111 h1141 h37 h39 hFSU hc hmax
  obtain ⟨hTK, -, -, -, -, -⟩ := conf_spec hF43 h1102 h1110 h1111 h1141 hc
  exact ⟨I', ⟨hfsu, hTK, hc.hyp.one_lt, shape11_of_type hK⟩⟩

theorem mem_inf_centralizer_kz (hF43 : Facts43) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1) (hc : Conf11_4_2 T L I n V₁ z) :
    z ∈ T ⊓ Subgroup.centralizer (kz L V₁ z : Set G) := by
  obtain ⟨-, -, hKz, -, -, -⟩ := conf_spec hF43 h1102 h1110 h1111 h1141 hc
  refine ⟨SecA.fsuV_le_T hc.hyp hc.mem.1, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (hKz hk)

end CFSG.Quasithin.Vol2.Ch11.O10
