module

public import CFSG.Quasithin.Background.C2Blocks

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Bot

variable {M : Type*} [CommGroup M]

@[expose] def quotBotEquiv (S K : Subgroup M) (hK : K = ⊥) : (↥S ⧸ K.subgroupOf S) ≃* ↥S :=
  (QuotientGroup.quotientMulEquivOfEq (by rw [hK, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot

theorem quotBotEquiv_mk (S K : Subgroup M) (hK : K = ⊥) (m : ↥S) :
    quotBotEquiv S K hK (QuotientGroup.mk m) = m := rfl

@[expose] def natQuotEquiv (D : FFModel) (hs : D.sec = ⊤) (hk : D.ker = ⊥) :
    (↥D.sec ⧸ D.ker.subgroupOf D.sec) ≃* D.Amb :=
  (quotBotEquiv D.sec D.ker hk).trans ((MulEquiv.subgroupCongr hs).trans Subgroup.topEquiv)

end Bot

section Alt

open CFSG.Quasithin.G6 in
theorem mem_evenWeight_iff' {n : ℕ} {x : Fin n → ZMod 2} :
    x ∈ evenWeight n ↔ ∑ i, x i = 0 := by
  simp [evenWeight]

open CFSG.Quasithin.G6 in
@[expose] def coreEvenEquiv (n : ℕ) : ↥(coreMod n) ≃* Multiplicative ↥(evenWeight n) where
  toFun x := Multiplicative.ofAdd ⟨Multiplicative.toAdd (x : PermMod n),
    mem_evenWeight_iff'.2 (mem_coreMod.1 x.2)⟩
  invFun y := ⟨Multiplicative.ofAdd ((Multiplicative.toAdd y : ↥(evenWeight n)) : Fin n → ZMod 2),
    mem_coreMod.2 (mem_evenWeight_iff'.1 (Multiplicative.toAdd y).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

open CFSG.Quasithin.G6 in
theorem coreEvenEquiv_coord {n : ℕ} (x : ↥(coreMod n)) (i : Fin n) :
    ((Multiplicative.toAdd (coreEvenEquiv n x) : ↥(evenWeight n)) : Fin n → ZMod 2) i =
      Multiplicative.toAdd (x : PermMod n) i := rfl

open CFSG.Quasithin.G6 in
@[expose] def altHeartHom (n : ℕ) : ↥(coreMod n) →* Multiplicative (AltHeart n) :=
  (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' (constWeight n))).comp
    (coreEvenEquiv n).toMonoidHom

open CFSG.Quasithin.G6 in
theorem altHeartHom_surjective (n : ℕ) : Function.Surjective (altHeartHom n) := by
  intro y
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd y)
  obtain ⟨x, hx⟩ := (coreEvenEquiv n).surjective (Multiplicative.ofAdd a)
  refine ⟨x, ?_⟩
  apply Multiplicative.toAdd.injective
  show (QuotientAddGroup.mk (Multiplicative.toAdd (coreEvenEquiv n x)) : AltHeart n) =
    Multiplicative.toAdd y
  rw [hx]
  exact ha

open CFSG.Quasithin.G6 in
theorem altHeartHom_apply (n : ℕ) (x : ↥(coreMod n)) :
    Multiplicative.toAdd (altHeartHom n x) =
      (QuotientAddGroup.mk (Multiplicative.toAdd (coreEvenEquiv n x)) : AltHeart n) := rfl

open CFSG.Quasithin.G6 in
theorem altHeartHom_eq_one_iff (n : ℕ) (x : ↥(coreMod n)) :
    altHeartHom n x = 1 ↔ ∀ i j, Multiplicative.toAdd (x : PermMod n) i =
      Multiplicative.toAdd (x : PermMod n) j := by
  rw [← Multiplicative.toAdd.injective.eq_iff, altHeartHom_apply, toAdd_one,
    QuotientAddGroup.eq_zero_iff]
  exact Iff.rfl

open CFSG.Quasithin.G6 in
@[expose] def altKer (n : ℕ) : Subgroup ↥(coreMod n) :=
  (Subgroup.zpowers (allOnes n) ⊓ coreMod n).subgroupOf (coreMod n)

open CFSG.Quasithin.G6 in
theorem ker_altHeartHom (n : ℕ) (hn : 0 < n) : (altHeartHom n).ker = altKer n := by
  ext x
  rw [MonoidHom.mem_ker, altHeartHom_eq_one_iff]
  show _ ↔ (x : PermMod n) ∈ Subgroup.zpowers (allOnes n) ⊓ coreMod n
  refine ⟨fun h => ⟨?_, x.2⟩, fun h => ?_⟩
  · rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (Multiplicative.toAdd (x : PermMod n)
      ⟨0, hn⟩) with hc | hc
    · have : (x : PermMod n) = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        rw [h i ⟨0, hn⟩, hc]
        rfl
      rw [this]
      exact Subgroup.one_mem _
    · have : (x : PermMod n) = allOnes n := by
        apply Multiplicative.toAdd.injective
        funext i
        rw [h i ⟨0, hn⟩, hc]
        rfl
      rw [this]
      exact Subgroup.mem_zpowers _
  · intro i j
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h.1
    rw [← hk]
    simp [allOnes]

open CFSG.Quasithin.G6 in
@[expose] noncomputable def altQuotEquiv (n : ℕ) (hn : 0 < n) :
    (↥(coreMod n) ⧸ altKer n) ≃* Multiplicative (AltHeart n) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_altHeartHom n hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (altHeartHom n) (altHeartHom_surjective n))

open CFSG.Quasithin.G6 in
theorem altQuotEquiv_mk (n : ℕ) (hn : 0 < n) (m : ↥(coreMod n)) :
    altQuotEquiv n hn (QuotientGroup.mk m) = altHeartHom n m := rfl

end Alt

end CFSG.Quasithin.C124
