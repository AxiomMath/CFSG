module

public import CFSG.Quasithin.H13.A5S136p

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Quasithin.E3
open CFSG.Blueprint

@[expose] def EndL34K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Concl136 →
    ∀ K ∈ cComp S.G1, S.G1 ≤ Subgroup.normalizer (K : Set G) →
      ¬ K ≤ Subgroup.normalizer (L : Set G) → IsPSL 3 2 2 (↥K ⧸ CFSG.pCore 2 ↥K) → False

theorem fin136_of_ident
    (h1323 : Input1323Two) (h1336 : Input1336) (h523 : Stmt5_2_3)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h312 : A312ForSQTK) (h128 : Lemma128Four)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hL34 : EndL34K) : Fin136 := by
  intro G _ _ T L V S hab h24 hr hw hn hsolv h2661 _
  have hC : S.Concl136 := ⟨hab, h24, hr, hw, hn, hsolv, h2661⟩
  have h24' : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
      ⁅V, conjSub g⁻¹ V⁆ = ⊥ := fun g hg hne => (h24 g hg hne).2
  obtain ⟨K, hK, hKn, hJ | hM | hL | h3D4⟩ :=
    S.exists_ident h1336 hC h523 h37 h38 h39 h312 h128
  · obtain ⟨e⟩ := hJ
    exact S.false_of_J2 h1323 h1336 h24' hD310 hD391 hI4 hK hKn
      (h2661 S.G1 (S.G1_mem_Hz h1336) K hK) e
  · obtain ⟨e⟩ := hM
    exact S.false_of_M23 h1323 h1336 h24' hD310 hD391 hI4 hK hKn
      (h2661 S.G1 (S.G1_mem_Hz h1336) K hK) e
  · exact hL34 G T L V S hC K hK hKn (h2661 S.G1 (S.G1_mem_Hz h1336) K hK) hL
  · exact S.false_of_3D4 h1323 h1336 h24' hD310 hD391 hI4 hK hKn
      (h2661 S.G1 (S.G1_mem_Hz h1336) K hK) h3D4

end CFSG.Quasithin.H13.A5
