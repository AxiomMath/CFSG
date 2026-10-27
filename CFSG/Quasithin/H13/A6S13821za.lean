module

public import CFSG.Quasithin.H13.A6S13821z
public import CFSG.Quasithin.H13.A6S13821a
public import CFSG.Quasithin.H13.A6S13821b

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem lieF2n_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ} (h : LieF2n X n) :
    LieF2n Y n := by
  let ec : (X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  unfold LieF2n at h ⊢
  rcases h with h | h | h | h | h
  · exact Or.inl (IsPSL.of_mulEquiv ec h)
  · exact Or.inr (Or.inl (IsPSL.of_mulEquiv ec h))
  · exact Or.inr (Or.inr (Or.inl (IsPSU.of_mulEquiv ec h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (IsPSp4.of_mulEquiv ec h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (IsG2.of_mulEquiv ec h))))

theorem lem13820_of
    (h16 : Lem13816)
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813) (hAut : Fact13820Aut)
    (ha : Case13820a) (hb : Case13820bSL34U38) (hc : Case13820L24) : Lem13820 := by
  intro G _ _ T L V S hS H hH K hK n hn hLie
  obtain ⟨-, hH₀, -, hK₀, hKN₀, -⟩ := S.reduce13821 h16 h36c h37 h38 h139 h1334 h13 hS hH hK
  obtain ⟨e⟩ := S.kst_equiv hS hH hK
  obtain ⟨e₀⟩ := S.kst_equiv hS hH₀ hK₀
  have hLie₀ : LieF2n ↥(S.KSt (K ⊔ (S.L1 ⊔ T)) K) n := lieF2n_congr (e.symm.trans e₀) hLie
  have hLieQ : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n := lieF2n_congr e.symm hLie
  have hCtx : S.Ctx13820 (K ⊔ (S.L1 ⊔ T)) K n := ⟨hS, hH₀, hK₀, hKN₀, rfl, hn, hLie₀⟩
  have hB := S.borel_le_M h13 h1334 hS hH₀ (le_of_mem_cComp hK₀) hKN₀ hn hLieQ
  rcases hAut G T L V S _ K n hCtx (fun _ => hB) with h | h
  · exact ha G T L V S _ K n hCtx h
  · by_cases h2 : IsPSL 2 2 2
      (↥(S.KSt (K ⊔ (S.L1 ⊔ T)) K) ⧸ Subgroup.center ↥(S.KSt (K ⊔ (S.L1 ⊔ T)) K))
    · exact hc G T L V S _ K n hCtx h h2
    · exact hb G T L V S _ K n hCtx h h2

end CFSG.Quasithin.H13.A6
