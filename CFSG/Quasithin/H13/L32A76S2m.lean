module

public import CFSG.Quasithin.H13.L32A76S2k
public import CFSG.Quasithin.H13.L32A76S2l
public import CFSG.Quasithin.H13.L32A76S2GL
public import CFSG.Quasithin.H13.L32ASk9

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H Y : Subgroup G}

namespace Ctx

variable (C : Ctx G T L V H Y)
include C

theorem isElemAbelian_A {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g) :
    IsElemAbelian 2 (⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) := by
  have hAU : ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ ≤ conjClosure V H :=
    (C.h98.F913_3 s (X := V) (Y := V) (Or.inl rfl) (Or.inl rfl)).trans inf_le_left
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => C.h98.F911_3.2 x (hAU hx)⟩
  have := C.h98.F911_3.1.is_comm.comm ⟨a, hAU a.2⟩ ⟨b, hAU b.2⟩
  have h2 : (a : G) * b = b * a := congrArg Subtype.val this
  simpa using h2

theorem false_of_inputs (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (hGL : Input1476S2GL) : False := by
  have := C.fact
  obtain ⟨γ, γ', g, e₁, e₂, b, D⟩ := C.exists_good
  have hK := C.S.hyp.fsu.qtke
  have hs := C.S.hyp.fsu.simple
  have hnab := C.S.hyp.fsu.nonabelian
  have hGLA := hGL G T L V H C.S Y C.hY2 C.hYH C.hHY C.hexp C.hYM C.hHYL C.hHL C.hmin C.h25 γ γ'
    g D.s D.mγ D.mH D.card D.V₁_le D.A₁_le
  have hA := C.isElemAbelian_A D.s
  obtain ⟨LA, hLA, hNLA, htop⟩ := exists_LA hK hs hnab h37 h39 hA D.card hGLA
  have hAut := comm_mem_pCoreOf_LA hK hs hnab h36 hA D.card hLA htop
  obtain ⟨S, hSH, hSsyl, hUS⟩ := C.exists_S D.s
  obtain ⟨TA, hTAsyl, hTAN, hTAK, hLAK⟩ := C.exists_TA D hSH hSsyl hUS hLA hNLA htop hAut
  exact C.false_of_TA D h36 hLA htop hTAsyl hTAN hTAK hLAK

end Ctx

theorem input1476S2_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h36 : A36ForSQTK)
    (hGL : Input1476S2GL) : Input1476S2 := by
  intro G _ _ T L V H S Y hY2 hYH hHY hexp hYM hHYL hHL hmin h25
  have h98 := S.hypF98 (stmt13_3_2_two_of h1332) (stmtL32NModule_of_inputs h1332 h1334) h1222
  exact Ctx.false_of_inputs ⟨S, h98, h1222, h1332, h1334, hY2, hYH, hHY, hexp, hYM, hHYL, hHL,
    hmin, h25⟩ h36 (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved)
    (a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved) hGL

end CFSG.Quasithin.H13.L32A.S2

end
