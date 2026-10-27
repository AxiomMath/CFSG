module

public import CFSG.Quasithin.Vol2.Asc94.He42BaseFacts
public import CFSG.Quasithin.Vol2.Asc94.He42Y
public import CFSG.Quasithin.Vol2.Asc94.He42Psi
public import CFSG.Quasithin.Vol2.Asc94.He42YFacts
public import CFSG.Quasithin.Vol2.Asc94.He42R
public import CFSG.Quasithin.Vol2.Asc94.He42V
public import CFSG.Quasithin.Vol2.Asc94.He42Zcomm
public import CFSG.Quasithin.Vol2.Asc94.He42Zmat
public import CFSG.Quasithin.Vol2.Asc94.He42L
public import CFSG.Quasithin.Vol2.Asc94.He42Braid
public import CFSG.Quasithin.Vol2.Asc94.He42BN2
public import CFSG.Quasithin.Vol2.Asc94.He42BN
public import CFSG.Quasithin.Vol2.Asc94.He42Spread
public import CFSG.Quasithin.Vol2.Asc94.He42N
public import CFSG.Quasithin.Vol2.Asc94.He42W
public import CFSG.Quasithin.Vol2.Asc94.He42Uniq
public import CFSG.Quasithin.Vol2.Asc94.He42Ker
public import CFSG.Quasithin.Vol2.Asc94.He42Perf
public import CFSG.Quasithin.Vol2.Asc94.He42Final

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

theorem HeSetup.typeL34_main
    (S : HeSetup G)
    (h422 : ∀ y₁ y₂ : G, YSpec S y₁ y₂ → Open422 S y₁ y₂) :
    Subgroup.center ↥S.L = S.B.subgroupOf S.L ∧
      CFSG.ComponentClassification.AS81.TypeL34
        (CFSG.ComponentClassification.RankTwoStandard.rankTwoQuot S.L) := by
  have hB := S.baseFacts
  have hP := S.stepPsi hB
  obtain ⟨y₁, y₂, hY⟩ := S.stepY
  have hn := S.stepYnorm hB hY
  have hf := S.stepYfpf hB hY
  have h0 := S.stepY0 hB hY
  have hR := S.stepR hB hY
  have hAZ := S.stepAZ hB hY
  have hV := S.stepV hB hY
  have hZc := S.stepZcomm hB
  have hZm := S.stepZmat hB hY
  obtain ⟨hc, l₁, l₂, hl⟩ := S.exists_wspec hB hP hY hn hf h0
  have hbraid := S.braid hB hP hY hn hf h0 hV hc hl (h422 y₁ y₂ hY)
  obtain ⟨U₁, U₂, hbn⟩ := S.bnpair hB hP hY hR hl hbraid
  have hcover := CFSG.Quasithin.A94.He42BN.mem_mul_of_bnpair hbn
  have hSp := S.stepSpread hB hP hY hn h0 hR hZm hc
  have hN := S.stepN hB hP
  have hW := S.stepW hB hP hSp
  have hU := S.stepUniq hB hN hW
  have hK := S.stepKer hB hP hSp hU
  have hperf := S.perfect hB hP hY hR hAZ hZc hl
  exact S.typeL34_of hB hU hK hperf hcover

end CFSG.Quasithin.A94.He42
