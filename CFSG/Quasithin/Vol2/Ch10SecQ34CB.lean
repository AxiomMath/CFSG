module

public import CFSG.Quasithin.Vol2.Ch10SecQ34CA
public import CFSG.Quasithin.Vol2.Ch10SecB3Facts
public import CFSG.Quasithin.Background.InternalSecSumB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace C10P34

theorem stab_of_not_secIsoL {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
    {A B : Subgroup V} (hs : A ⊔ B = ⊤) (hi : A ⊓ B = ⊥) (hA : XMod.IsIrr ↥H A)
    (hinvA : ∀ k ∈ H, ∀ w ∈ A, k w ∈ A) (hinvB : ∀ k ∈ H, ∀ w ∈ B, k w ∈ B)
    (hcard : Nat.card A = Nat.card B) (hni : ¬ SecIsoL H A ⊥ B ⊥) {x : MulAut V}
    (hx : ∀ h ∈ H, x * h = h * x) : ∀ w ∈ A, x w ∈ A := by
  set p := InternalSec.proj₂ hs hi with hp
  have hpk : ∀ k ∈ H, ∀ v : V, p (k v) = k (p v) := fun k hk v =>
    (InternalSec.proj_apply_of_stab hs hi (hinvA k hk) (hinvB k hk) v).2
  have hxk : ∀ k ∈ H, ∀ v : V, x (k v) = k (x v) := fun k hk v => by
    have := congrArg (fun g : MulAut V => g v) (hx k hk)
    simpa [MulAut.mul_apply] using this
  set J : Subgroup V := A ⊓ (p.comp x.toMonoidHom).ker with hJ
  have hJinv : XMod.IsInv ↥H J := by
    intro k w hw
    refine ⟨hinvA k k.2 w hw.1, ?_⟩
    have hw2 : p (x w) = 1 := hw.2
    show p (x ((k : MulAut V) w)) = 1
    rw [hxk k k.2, hpk k k.2, hw2, map_one]
  rcases hA.2.2 J hJinv bot_le inf_le_left with hJb | hJA
  · exfalso
    apply hni
    set f : ↥A →* ↥B :=
      { toFun := fun w => ⟨p (x w), InternalSec.proj₂_mem hs hi _⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp) } with hf
    have hfinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro w hw
      have hw1 : p (x (w : V)) = 1 := congrArg Subtype.val hw
      have hwJ : (w : V) ∈ J := ⟨w.2, hw1⟩
      rw [hJb, Subgroup.mem_bot] at hwJ
      exact Subtype.ext hwJ
    have hfbij : Function.Bijective f :=
      (Nat.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard⟩
    refine InternalSec.secIsoL_of_equiv hinvA hinvB (MulEquiv.ofBijective f hfbij) fun k w => ?_
    show p (x ((k : MulAut V) w)) = (k : MulAut V) (p (x w))
    rw [hxk k k.2, hpk k k.2]
  · intro w hw
    have hwJ : w ∈ J := hJA ▸ hw
    have hp1 : p (x w) = 1 := hwJ.2
    have h := InternalSec.proj₁_mul_proj₂ hs hi (x w)
    rw [← hp, hp1, mul_one] at h
    rw [← h]
    exact InternalSec.proj₁_mem hs hi _

theorem card_eq_eight {V : Type} [CommGroup V] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {H : Subgroup (MulAut V)} {W : Subgroup V}
    {π : ↥(StatedSL 3 K) →* ↥H} (hD : (FFModel.nat (StatedSL 3 K)).RealizesVia H W ⊥ π) :
    Nat.card W = 8 := by
  obtain ⟨e, -⟩ := B5.exists_linModel hD
  rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, hK, Nat.card_fin]
  norm_num

end C10P34

theorem factCommL3Pair_holds : FactCommL3Pair := by
  intro V _ _ H W₁ W₂ hsum hinf h1 h2 hni x hx
  obtain ⟨K₁, _, _, hK₁, π₁, hD₁⟩ := h1
  obtain ⟨K₂, _, _, hK₂, π₂, hD₂⟩ := h2
  rw [pow_one] at hK₁ hK₂
  have hI₁ := B5.isIrr_of_realizes (by norm_num) hD₁
  have hI₂ := B5.isIrr_of_realizes (by norm_num) hD₂
  have hinv₁ : ∀ k ∈ H, ∀ w ∈ W₁, k w ∈ W₁ := fun k hk w hw => hD₁.2.2.2.1 ⟨k, hk⟩ w hw
  have hinv₂ : ∀ k ∈ H, ∀ w ∈ W₂, k w ∈ W₂ := fun k hk w hw => hD₂.2.2.2.1 ⟨k, hk⟩ w hw
  have hc₁ := C10P34.card_eq_eight hK₁ hD₁
  have hc₂ := C10P34.card_eq_eight hK₂ hD₂
  have hsum' : W₂ ⊔ W₁ = ⊤ := by rw [sup_comm]; exact hsum
  have hinf' : W₂ ⊓ W₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hs₁ := C10P34.stab_of_not_secIsoL hsum hinf hI₁ hinv₁ hinv₂ (hc₁.trans hc₂.symm) hni hx
  have hs₂ := C10P34.stab_of_not_secIsoL hsum' hinf' hI₂ hinv₂ hinv₁ (hc₂.trans hc₁.symm)
    (fun h => hni (InternalSec.secIsoL_symm hinv₂ hinv₁ h)) hx
  have hf₁ := C10P34.fix_of_comm_nat (by norm_num) hK₁ hD₁ hs₁ hx
  have hf₂ := C10P34.fix_of_comm_nat (by norm_num) hK₂ hD₂ hs₂ hx
  ext v
  have hv := InternalSec.proj₁_mul_proj₂ hsum hinf v
  calc x v = x (InternalSec.proj₁ hsum hinf v * InternalSec.proj₂ hsum hinf v) := by rw [hv]
    _ = InternalSec.proj₁ hsum hinf v * InternalSec.proj₂ hsum hinf v := by
      rw [map_mul, hf₁ _ (InternalSec.proj₁_mem hsum hinf v),
        hf₂ _ (InternalSec.proj₂_mem hsum hinf v)]
    _ = v := hv

end CFSG.Quasithin.Vol2.Ch10.SecB
