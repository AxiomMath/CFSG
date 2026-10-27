module

public import CFSG.Quasithin.EmptyFaithful.F112RF
public import CFSG.Quasithin.EmptyFaithful.F112RA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X
open CFSG.Quasithin.He9 (isQuasithinSub_of)

@[expose] def Input15208F53Res : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L₁ L₂ S : Subgroup G), Hyp111 L₁ L₂ S →
    IsQuasithinSub (L₁ ⊔ L₂ ⊔ S) →
    Nonempty (OTwoQuot L₁ ≃* Equiv.Perm (Fin 3)) →
    Nonempty (OTwoQuot L₂ ≃* ↥(alternatingGroup (Fin 5))) →
    Nonempty (OTwoQuot (L₂ ⊔ S) ≃* Equiv.Perm (Fin 5)) →
    IsSylowTwoOf S (L₂ ⊔ S) →
    ∀ E : Subgroup G, E ≤ S → IsElemAbelian 2 E →
      L₂ ⊔ S ≤ Subgroup.normalizer (E : Set G) →
      IsChiefSeriesFrom (L₂ ⊔ S) E E 2 →
      (∀ L N : Subgroup G, IsChiefStep (L₂ ⊔ S) E L N → ¬ IsCentralStep (L₂ ⊔ S) L N →
        ChiefFactorShape (L₂ ⊔ S) L N) →
      Nat.card E < 64

theorem nonempty_oTwoQuot_of_eq {G : Type*} [Group G] {A B : Subgroup G} (h : A = B) {X : Type*}
    [Group X] (hA : Nonempty (OTwoQuot A ≃* X)) : Nonempty (OTwoQuot B ≃* X) := by
  subst h
  exact hA

theorem input15208F112At_S5_S3_of_res (hR : Input15208F53Res) (h1515 : StageLemma1515CE)
    (h1519 : StageLemma1519) (h15207 : StageLemma15207) (h15201 : StageLemma15201)
    (h15112 : StageLemma15112) :
    Input15208F112At (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 3)) := by
  intro G _ _ T Mc M hs H hH Y₁ hY₁ hφ hq₁
  obtain ⟨φ⟩ := hφ
  have c : S5Ctx T Mc M H Y₁ φ :=
    ⟨hs, hH, h1515 G T Mc M hs.qtfe hs.mf hs.ce, h1519 G T Mc M hs.qtfe hs.mf hs.ce, hY₁,
      h15207 G T Mc M hs Y₁ hY₁⟩
  have hc := (h15112 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
  obtain ⟨hUab, hUP, hPT, hnorm, hU64⟩ := F112RR.exists_elemAbelian_card_ge hs hH c.c1519
    (h15201 G T Mc M hs) hc
  have hHeq : kS5 H φ ⊔ T = H := sup_kS5_eq φ c.hT
  have := hR G (Y₁ ⊔ rcOf Mc M) (kS5 H φ) T (F112RR.S5Ctx.hyp111_S3 c hq₁)
    (isQuasithinSub_of c.hs.qtfe.qtke _) hq₁ (nonempty_oTwoQuot_kS5 H φ)
    (nonempty_oTwoQuot_of_eq hHeq.symm ⟨φ⟩) (by rw [hHeq]; exact c.hT)
    (conjClosure (V154 T Mc M) H) (hUP.trans hPT) hUab
    (by rw [hHeq]; exact hnorm) (by rw [hHeq]; exact hc.chief)
    (by rw [hHeq]; exact hc.shape trivial)
  omega

end CFSG.Quasithin
