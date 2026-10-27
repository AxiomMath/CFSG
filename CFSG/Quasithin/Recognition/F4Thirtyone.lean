module

public import CFSG.Quasithin.Recognition.F4Local
public import CFSG.Quasithin.Recognition.F4Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w' v

namespace LieSetting

variable (S : LieSetting.{u, w})

@[expose] def Mb1 : Subgroup S.ι.G0 := (f1 (c := S.ι)).range

@[expose] def Mb2 : Subgroup S.ι.G0 := (f2 (c := S.ι)).range

variable {S} {Y : Type w'} [Group Y] {M : Type v} [Group M]

@[expose] noncomputable def bOne (hι : S.ι.IsFaithful) (β : S.α.Completion Y) (ε : Y →* M) :
    S.Mb1 →* M :=
  (ε.comp β.φ1).comp (MonoidHom.ofInjective (f1_injective S.ι hι)).symm.toMonoidHom

@[expose] noncomputable def bTwo (hι : S.ι.IsFaithful) (β : S.α.Completion Y) (ε : Y →* M) :
    S.Mb2 →* M :=
  (ε.comp β.φ2).comp (MonoidHom.ofInjective (f2_injective S.ι hι)).symm.toMonoidHom

theorem bOne_apply (hι : S.ι.IsFaithful) (β : S.α.Completion Y) (ε : Y →* M) (a : S.α.G1) :
    bOne hι β ε ⟨f1 (c := S.ι) a, a, rfl⟩ = ε (β.φ1 a) := by
  have : (MonoidHom.ofInjective (f1_injective S.ι hι)).symm ⟨f1 (c := S.ι) a, a, rfl⟩ = a := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show (ε.comp β.φ1) ((MonoidHom.ofInjective (f1_injective S.ι hι)).symm
    ⟨f1 (c := S.ι) a, a, rfl⟩) = ε (β.φ1 a)
  rw [this]
  rfl

theorem bTwo_apply (hι : S.ι.IsFaithful) (β : S.α.Completion Y) (ε : Y →* M) (a : S.α.G2) :
    bTwo hι β ε ⟨f2 (c := S.ι) a, a, rfl⟩ = ε (β.φ2 a) := by
  have : (MonoidHom.ofInjective (f2_injective S.ι hι)).symm ⟨f2 (c := S.ι) a, a, rfl⟩ = a := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show (ε.comp β.φ2) ((MonoidHom.ofInjective (f2_injective S.ι hι)).symm
    ⟨f2 (c := S.ι) a, a, rfl⟩) = ε (β.φ2 a)
  rw [this]
  rfl

theorem fComp (hι : S.ι.IsFaithful) (β : S.α.Completion Y) (hβ : β.IsFaithful) (ε : Y →* M)
    (hε : Function.Injective ε) :
    F431Comp S.Mb1 S.Mb2 (bOne hι β ε) (bTwo hι β ε) := by
  refine ⟨fun x y h => ?_, fun x y h => ?_, ?_⟩
  · exact (MonoidHom.ofInjective (f1_injective S.ι hι)).symm.injective (hβ.1 (hε h))
  · exact (MonoidHom.ofInjective (f2_injective S.ι hι)).symm.injective (hβ.2.2 (hε h))
  · intro g h1 h2
    obtain ⟨a, ha⟩ := h1
    obtain ⟨a', ha'⟩ := h2
    have e1 : (⟨g, ⟨a, ha⟩⟩ : S.Mb1) = ⟨f1 (c := S.ι) a, a, rfl⟩ := Subtype.ext ha.symm
    have e2 : (⟨g, ⟨a', ha'⟩⟩ : S.Mb2) = ⟨f2 (c := S.ι) a', a', rfl⟩ := Subtype.ext ha'.symm
    rw [e1, e2, bOne_apply, bTwo_apply]
    congr 1
    have hιeq : S.ι.φ1 a = S.ι.φ2 a' := congrArg Subtype.val (ha.trans ha'.symm)
    have hmem : S.ι.φ1 a ∈ S.ι.φ1.range ⊓ S.ι.φ2.range := ⟨⟨a, rfl⟩, ⟨a', hιeq.symm⟩⟩
    rw [S.ι.inter] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hc1 : S.α.α1 c = a := hι.1 (by rw [S.ι.comm1, hc])
    have hc2 : S.α.α2 c = a' := hι.2.2 (by rw [S.ι.comm2, hc, hιeq])
    rw [← hc1, ← hc2, β.comm1, β.comm2]

theorem lemma_F444 [Finite M] {T : Subgroup S.ι.G0} {z t : S.ι.G0} (β : S.α.Completion Y)
    (hβ : β.IsFaithful) (ε : Y →* M) (hε : Function.Injective ε)
    (D : F431Lie T S.Mb1 S.Mb2 z t)
    (hb : Subgroup.centralizer ({amalgamMap (bOne S.hι β ε) (bTwo S.hι β ε) z} : Set M) ≤
      (bOne S.hι β ε).range)
    (hnc : ¬ IsConj (amalgamMap (bOne S.hι β ε) (bTwo S.hι β ε) z)
      (amalgamMap (bOne S.hι β ε) (bTwo S.hι β ε) t))
    (h442 : Subgroup.centralizer ({amalgamMap (bOne S.hι β ε) (bTwo S.hι β ε) t} : Set M) ≤
      (bTwo S.hι β ε).range)
    (hF424 : Nat.card Y ≤ Nat.card S.Yb → Nat.card Y = Nat.card S.Yb ∧
      ∃ (Ġ : Type w') (_ : Group Ġ), S.IsExtension Ġ ∧ Nonempty (Y ≃* Ġ)) :
    Nat.card M = Nat.card S.Yb ∧
      ∃ (Ġ : Type w') (_ : Group Ġ), S.IsExtension Ġ ∧ Nonempty (M ≃* Ġ) ∧
        Nat.card Ġ = Nat.card S.Yb := by
  have hC := fComp S.hι β hβ ε hε
  have h443 := D.lemma_F443 hC hb hnc h442
  have hG0 : Nat.card S.ι.G0 = Nat.card S.Yb := card_G0 S.ι
  have hle : Nat.card Y ≤ Nat.card S.Yb := by
    have := Nat.card_le_card_of_injective ε hε
    omega
  obtain ⟨hY, Ġ, hG, hext, ⟨φ⟩⟩ := hF424 hle
  have hMY : Nat.card M = Nat.card S.Yb := by omega
  have hbij : Function.Bijective ε :=
    hε.bijective_of_nat_card_le (by omega)
  have hGY : Nat.card Ġ = Nat.card S.Yb := by
    rw [← Nat.card_congr φ.toEquiv, hY]
  exact ⟨hMY, Ġ, hG, hext, ⟨(MulEquiv.ofBijective ε hbij).symm.trans φ⟩, hGY⟩

end LieSetting

end CFSG.Quasithin
