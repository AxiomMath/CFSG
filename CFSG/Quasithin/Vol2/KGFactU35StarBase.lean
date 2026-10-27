
module

public import CFSG.Quasithin.Vol2.KGFactU35Inputs
public import CFSG.Quasithin.Vol2.KGFactU35Defs
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
public import CFSG.Adapters.ProjectiveSpecialLinear

@[expose] public section

namespace CFSG.Quasithin.H13.KGU35

open HNUnitaryBridge CFSG.RankThree.PartOne.HNB CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical
open Matrix

theorem Star5.map {G H : Type*} [Group G] [Group H] (f : G →* H) {x : G} (hx : Star5 x) :
    Star5 (f x) := by
  obtain ⟨a, b, rfl, hab⟩ := hx
  refine ⟨f a, f b, by simp only [map_mul, map_inv], fun g hg => ?_⟩
  rw [← Set.image_pair, ← MonoidHom.map_closure] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  obtain ⟨h5, hc⟩ := hab g' hg'
  exact ⟨by rw [← map_pow, h5, map_one], by rw [← map_mul, ← map_mul, hc]⟩

theorem Star5.of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {x : G}
    (hx : Star5 (e x)) : Star5 x := by
  have := hx.map e.symm.toMonoidHom
  simpa using this

theorem fadd_lt (x y : ℕ) : fadd x y < 25 := by
  unfold fadd
  omega

theorem dec_cConj (x : ℕ) : dec (cConj x) = dec x ^ 5 := by
  have key : ∀ x < 25, dec (cConj x) = dec x ^ 5 := by decide +kernel
  have hx : cConj x = cConj (x % 25) := by
    have h1 : x % 5 = x % 25 % 5 := by omega
    have h2 : x / 5 % 5 = x % 25 / 5 % 5 := by omega
    unfold cConj
    rw [← h1, ← h2]
  rw [hx, dec_mod x]
  exact key _ (Nat.mod_lt _ (by norm_num))

theorem dec_finv : ∀ c < 25, dec (finv c) = (dec c)⁻¹ := by decide +kernel

theorem exists_code : ∀ x : F25, ∃ n < 25, dec n = x := by decide +kernel

@[expose] def Good (A : Array ℕ) : Prop := A.size = 9 ∧ ∀ k < 9, ent A k < 25

theorem decMat_eq_of_eq {f g : ℕ → ℕ} (h : ∀ k < 9, f k = g k) : decMat f = decMat g := by
  ext r s
  simp only [decMat, Matrix.of_apply]
  rw [h (3 * r + s) (by omega)]

theorem ent_mMul (A B : Array ℕ) {k : ℕ} (hk : k < 9) :
    ent (mMul A B) k = mprod (ent A) (ent B) k := by
  simp [mMul, ent, hk]

theorem decMat_mMul (A B : Array ℕ) :
    decMat (ent (mMul A B)) = decMat (ent A) * decMat (ent B) := by
  rw [decMat_eq_of_eq fun k hk => ent_mMul A B hk, decMat_mprod]

theorem decMat_mId : decMat (ent mId) = 1 := by decide +kernel

theorem decMat_mPow (A : Array ℕ) : ∀ k, decMat (ent (mPow A k)) = decMat (ent A) ^ k
  | 0 => by rw [pow_zero]; exact decMat_mId
  | k + 1 => by rw [mPow, decMat_mMul, decMat_mPow A k, pow_succ']

@[expose] noncomputable def suMat : unitarySU 5 1 F25 3 →* Matrix (Fin 3) (Fin 3) F25 :=
  (Units.coeHom _).comp (unitarySU 5 1 F25 3).subtype

theorem suMat_apply (g : unitarySU 5 1 F25 3) :
    suMat g = ((g : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) := rfl

theorem suMat_injective : Function.Injective suMat :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem mem_SU {M : GL (Fin 3) F25} : M ∈ unitarySU 5 1 F25 3 ↔
    (M : Matrix (Fin 3) (Fin 3) F25).det = 1 ∧
      ((M : Matrix (Fin 3) (Fin 3) F25).map (· ^ 5))ᵀ * M = 1 := by
  rw [mem_unitarySU_iff f25Data]
  have hb : (⇑f25Data.bar : F25 → F25) = fun c => c ^ 5 :=
    funext fun c => by rw [UnitaryFieldData.bar_apply, pow_one]
  rw [hb]

theorem suMat_unitaryInvT : suMat (unitaryInvT f25Data) = negNegOneDiag F25 := rfl

theorem pow_three_of_mem {z : unitarySU 5 1 F25 3} (hz : z ∈ unitaryScalars f25Data 3) :
    z ^ 3 = 1 := by
  have hcard : Nat.card (unitaryScalars f25Data 3) = 3 := by
    rw [card_unitaryScalars f25Data (by norm_num)]
    norm_num
  have := pow_card_eq_one' (G := unitaryScalars f25Data 3) (x := ⟨z, hz⟩)
  rw [hcard] at this
  exact congrArg Subtype.val this

end CFSG.Quasithin.H13.KGU35
