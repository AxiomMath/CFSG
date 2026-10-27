module

public import CFSG.Quasithin.H13.L32NSet14Gen
public import CFSG.Quasithin.H13.L32NSet14Idx
public import CFSG.Quasithin.H13.U3L14Producers
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem6

public section

namespace CFSG.Quasithin.H13.L32NSet14

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace Setting

variable [Finite G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V] (S : Setting G T L V V₂)
include S

theorem ti (h323 : Stmt3_2_3) : ∀ U H : Subgroup G, U ≠ ⊥ → U ≤ V →
    H ≤ normalizer (U : Set G) →
      H ⊓ normalizer (L : Set G) = H ⊓ normalizer (V : Set G) :=
  (stmt12_2_6_of S.h1222 h323 G T L V (hyp1223 S.h1332 S.hH S.hV)).2

theorem cent_le (h323 : Stmt3_2_3) :
    centralizer (V : Set G) ≤ normalizer (L : Set G) := by
  have hV : V ≠ ⊥ := fun h => by
    have := S.card_V
    rw [h, card_bot] at this
    omega
  have h := S.ti h323 V (centralizer (V : Set G)) hV le_rfl (centralizer_le_normalizer _)
  intro g hg
  have hg' : g ∈ centralizer (V : Set G) ⊓ normalizer (V : Set G) :=
    ⟨hg, centralizer_le_normalizer _ hg⟩
  rw [← h] at hg'
  exact hg'.2

theorem set14 (h323 : Stmt3_2_3) : U3.Set14 G T L V V₂ V (L₁Of L (fsuV1 T V)) where
  h13 := S.hH
  irr := S.hV
  zv := S.hZV
  v2 := S.hV2
  card1 := S.card_V1
  le23 := S.hV2.2.1
  le3V := le_rfl
  T_V3 := S.TV
  card3 := S.card_V
  Lp_eq := Lp_eq
  Lp_L := L1_le.trans inf_le_left
  Lp_V1 := L1_le.trans inf_le_right
  T_Lp := S.T_Lp
  gen := S.gen
  irred := S.irred
  comm3 := S.comm3
  index2 := S.index2_eq
  cv3 := fun _ hy _ => hy.2
  clv := S.clv
  bcase := Or.inl (S.cent_le h323)
  genL := S.genL
  fsu := ((S.h1332 G T L S.hH L S.hH.faithful).2.2.1.2 V S.hV).2.2.1
  T_L := S.TL
  V_T := S.VT
  T_V := S.TV
  Mmax := (S.h1332 G T L S.hH L S.hH.faithful).2.1.2.2.1
  uniq := (S.h1332 G T L S.hH L S.hH.faithful).2.1.2.2.2
  ti := S.ti h323
  Lp_def := ⟨fun h => absurd h S.not_isHatA6, fun _ => rfl⟩
  Lp3 := S.Lp3

end Setting

theorem set14ProducerL32_of_inputs (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2)
    (h323 : Stmt3_2_3) (h1334 : A6.Stmt13_3_4) : U3.Set14ProducerL32 := by
  intro G _ _ T L V V₂ _ hH hV hZV hV2 hlin hnat
  exact ⟨V, L₁Of L (fsuV1 T V),
    (Setting.mk h1222 h1332 h1334 hH hV hZV hV2 hlin hnat).set14 h323⟩

end CFSG.Quasithin.H13.L32NSet14
