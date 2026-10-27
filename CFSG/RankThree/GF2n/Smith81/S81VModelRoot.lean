module

public import CFSG.RankThree.GF2n.Smith81.S81VModelLemmaS
public import CFSG.RankThree.GF2n.Smith81.S81VRoot
public import CFSG.RankThree.GF2n.Smith81.S81VModelSwap

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F} {K : Type} [Field K]

@[expose] noncomputable def rootDatumU (hσ : IsUnitaryInvolution σ) (hf : Frame σ a b) (e₀ : K ≃+* Fσ σ) :
    RootDatum K (SUid σ 6) where
  N := HermK σ e₀
  u := uK hσ.invol hf
  u_add := uK_add hσ.invol hf
  τ := tauK σ e₀
  n₁ := n1K σ e₀
  τ_n₁ := tauK_n1K
  P := Pstab σ (Wa a)
  Ad := adK hσ.invol hf e₀
  u_Ad := uK_adK hσ.invol hf e₀
  d := dKhom hσ.invol hf e₀
  Ad_d := adK_dKhom hσ.invol hf e₀
  s := sU hσ.invol hf
  s_sq := sU_sq hσ.invol hf
  s_d := sU_dK hσ.invol hf e₀
  ker_stab := ker_stab_U hσ.invol hf e₀
  lemmaS := fun n hn => lemmaS_U hσ hf e₀ n hn
  braid := sU_braid hσ.invol hf e₀

end CFSG.RankThree.GF2n.Smith81.S81V
