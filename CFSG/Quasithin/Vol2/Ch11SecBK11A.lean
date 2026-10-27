module

public import CFSG.RankThree.SubgroupLists.SL2Perfect
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Local
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.BK11

open CFSG.Open CFSG.QuasithinUnique

variable {S : Type} [Group S] {B : Subgroup S}

theorem conj_mem_pCoreOf {x o : S} (hx : x ∈ Subgroup.normalizer (B : Set S))
    (ho : o ∈ pCoreOf 2 B) : x * o * x⁻¹ ∈ pCoreOf 2 B :=
  (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B hx) o).mp ho

theorem pCoreOf_le : pCoreOf 2 B ≤ B := CFSG.openPCoreOf_le 2 B

@[expose] def secCent (B : Subgroup S) : Subgroup S where
  carrier := {x | x ∈ Subgroup.normalizer (B : Set S) ∧
    ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 B}
  mul_mem' := by
    rintro x x' ⟨hx, hxB⟩ ⟨hx', hx'B⟩
    refine ⟨mul_mem hx hx', fun y hy => ?_⟩
    have e : x * x' * y * (x * x')⁻¹ * y⁻¹ =
        x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
    rw [e]
    exact mul_mem (conj_mem_pCoreOf hx (hx'B y hy)) (hxB y hy)
  one_mem' := ⟨one_mem _, fun y _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem _⟩
  inv_mem' := by
    rintro x ⟨hx, hxB⟩
    refine ⟨inv_mem hx, fun y hy => ?_⟩
    have hy' : x⁻¹ * y * x ∈ B := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hx) y).mp hy
    have e : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = (x * (x⁻¹ * y * x) * x⁻¹ * (x⁻¹ * y * x)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (hxB _ hy')

theorem normalizer_le_normalizer_secCent :
    Subgroup.normalizer (B : Set S) ≤ Subgroup.normalizer (secCent B : Set S) := by
  have key : ∀ g ∈ Subgroup.normalizer (B : Set S), ∀ x ∈ secCent B,
      g * x * g⁻¹ ∈ secCent B := by
    rintro g hg x ⟨hx, hxB⟩
    refine ⟨mul_mem (mul_mem hg hx) (inv_mem hg), fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ B := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) y).mp hy
    have e : g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ * y⁻¹ =
        g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact conj_mem_pCoreOf hg (hxB _ hy')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun h => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem pCoreOf_le_secCent : pCoreOf 2 B ≤ secCent B := by
  intro o ho
  refine ⟨Subgroup.le_normalizer (pCoreOf_le ho), fun y hy => ?_⟩
  have e : o * y * o⁻¹ * y⁻¹ = o * (y * o⁻¹ * y⁻¹) := by group
  rw [e]
  exact mul_mem ho (conj_mem_pCoreOf (Subgroup.le_normalizer hy) (inv_mem ho))

theorem relIndex_secCent_dvd_four [Finite S] {R : Subgroup S} (hR2 : IsPGroup 2 R)
    (hRB : R ≤ Subgroup.normalizer (B : Set S)) (h60 : (pCoreOf 2 B).relIndex B = 60)
    (hinn : ∀ r ∈ R, ∃ b ∈ B, ∀ y ∈ B, r * y * r⁻¹ * (b * y * b⁻¹)⁻¹ ∈ pCoreOf 2 B) :
    (secCent B).relIndex R ∣ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRBC : R ≤ B ⊔ secCent B := by
    intro r hr
    obtain ⟨b, hb, hby⟩ := hinn r hr
    have hc : b⁻¹ * r ∈ secCent B := by
      refine ⟨mul_mem (inv_mem (Subgroup.le_normalizer hb)) (hRB hr), fun y hy => ?_⟩
      have e : b⁻¹ * r * y * (b⁻¹ * r)⁻¹ * y⁻¹ =
          b⁻¹ * (r * y * r⁻¹ * (b * y * b⁻¹)⁻¹) * b⁻¹⁻¹ := by group
      rw [e]
      exact conj_mem_pCoreOf (inv_mem (Subgroup.le_normalizer hb)) (hby y hy)
    have e : r = b * (b⁻¹ * r) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hb hc
  have hN := normalizer_le_normalizer_secCent (B := B)
  have h1 : (secCent B).relIndex (R ⊔ secCent B) = (secCent B).relIndex R :=
    A3Gen.relIndex_sup_eq_of_le_normalizer' (hRB.trans hN)
  have h2 : (secCent B).relIndex (B ⊔ secCent B) = (secCent B).relIndex B :=
    A3Gen.relIndex_sup_eq_of_le_normalizer' (Subgroup.le_normalizer.trans hN)
  have h3 := Subgroup.relIndex_mul_relIndex (secCent B) (R ⊔ secCent B) (B ⊔ secCent B)
    le_sup_right (sup_le hRBC le_sup_right)
  have h4 : (secCent B).relIndex B ∣ 60 := by
    rw [← h60]
    exact Subgroup.relIndex_dvd_of_le_left B pCoreOf_le_secCent
  have hd60 : (secCent B).relIndex R ∣ 60 := by
    rw [← h1]
    refine (Dvd.intro _ h3).trans ?_
    rw [h2]
    exact h4
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
  have hdR : (secCent B).relIndex R ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdR
  rw [hjeq] at hd60 ⊢
  have hj2 : j ≤ 2 := by
    by_contra h
    have h8 : 2 ^ 3 ∣ 60 := (Nat.pow_dvd_pow 2 (by omega)).trans hd60
    norm_num at h8
  exact Nat.pow_dvd_pow 2 hj2

theorem commute_of_mem_secCent (hB : ⁅B, B⁆ = B)
    (hZ : ∀ o ∈ pCoreOf 2 B, ∀ y ∈ B, o * y = y * o) {x : S} (hx : x ∈ secCent B) :
    ∀ y ∈ B, x * y = y * x := by
  obtain ⟨-, hxB⟩ := hx
  let f : ↥B →* ↥B :=
    { toFun := fun y => ⟨x * y * x⁻¹ * y⁻¹, pCoreOf_le (hxB y y.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y y' => Subtype.ext (by
        have hc := hZ _ (hxB y' y'.2) y y.2
        change x * ((y * y' : ↥B) : S) * x⁻¹ * ((y * y' : ↥B) : S)⁻¹ =
          x * y * x⁻¹ * (y : S)⁻¹ * (x * y' * x⁻¹ * (y' : S)⁻¹)
        rw [Subgroup.coe_mul]
        calc x * (↑y * ↑y') * x⁻¹ * (↑y * ↑y')⁻¹ =
            x * ↑y * x⁻¹ * (↑y)⁻¹ * (↑y * (x * ↑y' * x⁻¹ * (↑y')⁻¹) * (↑y)⁻¹) := by group
          _ = x * ↑y * x⁻¹ * (↑y)⁻¹ * (x * ↑y' * x⁻¹ * (↑y')⁻¹) := by
            rw [← hc, mul_inv_cancel_right]) }
  have hf := CFSG.RankThree.SubgroupLists.perfect_hom_eq_one_of_commute
    (Subgroup.isPerfect_iff.mpr hB) f (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact Subtype.ext (hZ _ (hxB a a.2) _ (pCoreOf_le (hxB b b.2))))
  intro y hy
  have h1 := congrArg Subtype.val (DFunLike.congr_fun hf ⟨y, hy⟩)
  change x * y * x⁻¹ * y⁻¹ = 1 at h1
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

end CFSG.Quasithin.Vol2.Ch11.SecA.BK11
