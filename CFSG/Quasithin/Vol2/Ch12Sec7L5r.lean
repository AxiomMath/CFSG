module

public import CFSG.Quasithin.Vol2.Ch12Sec7Mod4F
public import CFSG.Quasithin.Vol2.Ch12Sec7L5a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

namespace S127.Setup

theorem zs6_fix : ∀ z ∈ S127.Mod.zs6, z.app 1 ≠ 1 → ∀ v < 64, z.app v = v → v = 0 := by
  decide

end S127.Setup

theorem setup1271_of
    (h1222 : Stmt12_2_2) : Setup1271 := by
  intro G _ _ T L V h
  obtain ⟨hcomm, hV64, -⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  obtain ⟨C, hC⟩ := S127.Mod.exists_identL_G h1222 h
  have hXz : ∀ a, a ∈ autOn (S127.XOf L) V ↔ C.cB a ∈ S127.Mod.zs6 :=
    S127.Mod.mem_autOn_XOf h1222 h hC
  refine ⟨⟨hcomm, fun x hx => S127.sq_eq_one_of_mem h.hyp hx⟩, hV64,
    S127.inf_centralizer_eq_of_1222 h1222 h, ?_, ?_, ?_⟩
  ·
    classical
    have e : ↥(autOn (S127.XOf L) V) ≃ {B : S127.Mod.B6 // B ∈ S127.Mod.zs6} :=
      Equiv.ofBijective (fun a => ⟨C.cB a, (hXz a).1 a.2⟩)
        ⟨fun a b hab => Subtype.ext (C.cB_injective (congrArg Subtype.val hab)), fun B => by
          obtain ⟨a, ha⟩ := hC.2 B.1 (S127.Mod.zs6_sub_gm6 _ B.2)
          exact ⟨⟨a, (hXz a).2 (ha ▸ B.2)⟩, Subtype.ext ha⟩⟩
    rw [Nat.card_congr e]
    have e2 : {B : S127.Mod.B6 // B ∈ S127.Mod.zs6} ≃ ↥S127.Mod.zs6.toFinset :=
      Equiv.subtypeEquivRight fun B => by simp
    rw [Nat.card_congr e2, Nat.card_eq_finsetCard,
      List.toFinset_card_of_nodup S127.Mod.zs6_nodup]
    decide
  ·
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    apply C.cB_injective
    rw [C.cB_mul, C.cB_mul]
    exact (S127.Mod.zs6_comm _ ((hXz a).1 ha) _ ((hC.1 b).1 hb)).symm
  ·
    intro x hxX hxC
    have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
      S127.Mod.L_le_normalizer h (S127.L5.XOf_le L hxX)
    have hz := (hXz _).1 (S127.Mod.conjAct_mem_autOn hxX hxN)
    have hne : C.cB (conjAct V ⟨x, hxN⟩) ≠ S127.Mod.B6.id := by
      intro h1
      apply hxC
      rw [← S127.Mod.conjAct_eq_one' hxN]
      apply C.cB_injective
      rw [h1, C.cB_one]
    rw [eq_bot_iff]
    rintro v ⟨hvV, hvx⟩
    rw [Subgroup.mem_bot]
    have hfix : conjAct V ⟨x, hxN⟩ ⟨v, hvV⟩ = ⟨v, hvV⟩ := by
      apply Subtype.ext
      rw [S127.Mod.conjAct_val]
      have hc : v * x = x * v := Subgroup.mem_centralizer_singleton_iff.mp hvx
      rw [← hc, mul_inv_cancel_right]
    have hcd := C.cd_apply (conjAct V ⟨x, hxN⟩) ⟨v, hvV⟩
    rw [hfix] at hcd
    have hne1 : (C.cB (conjAct V ⟨x, hxN⟩)).app 1 ≠ 1 := fun h1 =>
      hne (S127.Mod.zs6_fix1 _ hz h1)
    have h0 := S127.Setup.zs6_fix _ hz hne1 _ (C.cd_lt _) hcd.symm
    exact congrArg Subtype.val (C.cd_eq_zero.mp h0)

end CFSG.Quasithin.H13
