module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native312
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem a312Refined_of_facts (hList : Vol2Native.A312ListFactsCat) (hSL2 : A312SL2Fact)
    (h36 : Vol2Native.A36CoreForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) {Q : Type} [Group Q] (hQ : Vol2Native.SQTKHypCat Q) :
    A312Refined Q := by
  have := hQ.finite
  refine Vol2Native.a312_refined_of_list hSL2 (fun L hL hq T' hT' B' hB' hne => ?_)
    (fun L hL hnq => (h36 Q hQ L hL).toStrong hnq) (h37 Q hQ) (h39 Q hQ)
  have hL' : Vol2Native.SQTKHypCat ↥L := hQ.of_subnormal (subnormal_of_mem_cComp hL)
  exact hList ↥L hq hL'.isSQTKCat hL'.o2 T' hT' B' hB' hne

theorem lbar_type (h1011 : Stmt10_1_1) (hyp : Hyp10 G T L I) {Q : Type} [Group Q]
    (e : Q ≃* ModO2 L) :
    ((∃ n : ℕ, CFSG.Blueprint.SuzukiModel Q 2 n) ∨
        Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) ∨
      (Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨
        ∃ n : ℕ, 2 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
          Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 2) F)) := by
  rcases (h1011 G T L I hyp).2.2.2 with ⟨n, hn, ⟨F, _, _, hF, ⟨f⟩⟩, -⟩ | ⟨⟨f⟩, -⟩ | ⟨⟨f⟩, -⟩ |
      ⟨n, hn, ⟨F, _, _, hF, ⟨f⟩⟩, -⟩ | ⟨⟨f⟩, -⟩ | ⟨⟨f⟩, -⟩ | ⟨n, hsz, -⟩
  · exact Or.inr (Or.inr ⟨n, by omega, F, inferInstance, inferInstance, hF, ⟨e.trans f⟩⟩)
  · exact Or.inr (Or.inl ⟨e.trans f⟩)
  · exact Or.inl (Or.inr ⟨e.trans f⟩)
  · exact Or.inr (Or.inr ⟨2 * n, by omega, F, inferInstance, inferInstance, hF, ⟨e.trans f⟩⟩)
  · exact Or.inl (Or.inr ⟨e.trans f⟩)
  · exact Or.inl (Or.inr ⟨e.trans f⟩)
  · exact Or.inl (Or.inl ⟨n, CFSG.SectionRank.suzukiModel_of_mulEquiv e hsz⟩)

theorem exists_mul_ne_mul_modO2 (hyp : Hyp10 G T L I) :
    ∃ a b : ModO2 L, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hyp.fsu.quasisimple
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem isQuasisimple_modO2Image {H K : Subgroup G} (hKc : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple ↥K) : CFSG.IsQuasisimple ↥(modO2Image H K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  have hc : CFSG.pCore 2 ↥K ≤ Subgroup.center ↥K := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hn with h | h
    · exfalso
      apply not_isSolvable_of_mem_cComp hKc
      have hK2 : IsPGroup 2 ↥K := fun g => by
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := ↥K) (p := 2)) ⟨g, h ▸ Subgroup.mem_top g⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
      have := hK2.isNilpotent
      infer_instance
    · exact h
  obtain ⟨e⟩ := modO2_mulEquiv hKc
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (CFSG.LocalCores.quasisimple_central_quotient hq _ hc).1

end CFSG.Quasithin.Vol2.Ch10.SecB
