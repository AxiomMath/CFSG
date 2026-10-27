module

public import CFSG.Quasithin.Background.C124Core
public import CFSG.Quasithin.Background.C124L2MP

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_inf_centralizer {X V : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) :
    X ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
  fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => ⟨X.mul_mem (X.mul_mem hx hc.1) (X.inv_mem hx),
      conj_mem_centralizer_of_le hXN hx hc.2⟩, fun hc => ?_⟩
    have h1 := conj_mem_centralizer_of_le hXN (X.inv_mem hx) hc.2
    exact ⟨by simpa [mul_assoc] using X.mul_mem (X.mul_mem (X.inv_mem hx) hc.1) hx,
      by simpa [mul_assoc] using h1⟩

omit [Finite G] in
theorem mul_inv_mem_centralizer {V : Subgroup G} {hV : IsElemAbelian 2 V} {a b : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G)) (hb : b ∈ Subgroup.normalizer (V : Set G))
    (h : convI hV ⟨a, ha⟩ = convI hV ⟨b, hb⟩) : a * b⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have h1 : convI hV (⟨a, ha⟩ * ⟨b, hb⟩⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  exact (convI_eq_one_iff hV _).1 h1

namespace EntryPlus

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : EntryPlus X T V L R m hV)

include E

theorem R_le_X : R ≤ X := E.RT.trans E.sylow.1

theorem R_pGroup : IsPGroup 2 R := E.sylow.2.1.to_le E.RT

theorem R_le_normalizer_baum : R ≤ Subgroup.normalizer (baum R : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum R)

theorem baum_le_R : baum R ≤ R := inf_le_left

theorem frattini_star {x : G} (hx : x ∈ X)
    (hxn : convI hV ⟨x, E.hXN hx⟩ ∈
      Subgroup.normalizer (autI hV (baum R) : Set (MulAut (IntMod V hV)))) :
    ∃ c ∈ X ⊓ Subgroup.centralizer (V : Set G), ∃ n ∈ X ⊓ Subgroup.normalizer (baum R : Set G),
      x = c * n := by
  set Q := pCoreOf 2 X with hQ
  set S := baum R with hS
  set C : Subgroup G := X ⊓ Subgroup.centralizer (V : Set G) with hC
  set P₀ : Subgroup G := Q ⊔ S with hP₀
  have hSR : S ≤ R := E.baum_le_R
  have hSX : S ≤ X := hSR.trans E.R_le_X
  have hP₀R : P₀ ≤ R := sup_le E.QR hSR
  have hCX : X ≤ Subgroup.normalizer (C : Set G) := le_normalizer_inf_centralizer E.hXN
  have hQC : Q ≤ C := le_inf (pCoreOf_le 2 X) (pCoreOf_le_centralizer E.red)
  have hP₀C : P₀ ⊓ C = Q := by
    apply le_antisymm
    · intro y hy
      have hQe : Q = R ⊓ Subgroup.centralizer (V : Set G) := E.QC
      rw [hQe]
      exact ⟨hP₀R hy.1, hy.2.2⟩
    · exact le_inf le_sup_left hQC
  have hP₀N : P₀ ≤ Subgroup.normalizer (C : Set G) := (hP₀R.trans E.R_le_X).trans hCX
  set K : Subgroup G := C ⊔ P₀ with hK
  have hKsyl : IsSylowTwoOf P₀ K :=
    L2.isSylowTwoOf_sup_of_normalizing hP₀N (E.R_pGroup.to_le hP₀R) (by rw [hP₀C]; exact E.Csyl)
  have hconjS : ∀ (y : G) (hy : y ∈ X), convI hV ⟨y, E.hXN hy⟩ ∈
      Subgroup.normalizer (autI hV S : Set (MulAut (IntMod V hV))) →
      ∀ s ∈ S, y * s * y⁻¹ ∈ K := by
    intro y hy hyn s hs
    have hysy : y * s * y⁻¹ ∈ X := X.mul_mem (X.mul_mem hy (hSX hs)) (X.inv_mem hy)
    have h1 : convI hV ⟨y * s * y⁻¹, E.hXN hysy⟩ ∈ autI hV S := by
      have hs' : convI hV ⟨s, E.hXN (hSX hs)⟩ ∈ autI hV S := convI_mem_autI hV hs _
      have := (Subgroup.mem_normalizer_iff.1 hyn _).1 hs'
      have e : convI hV ⟨y * s * y⁻¹, E.hXN hysy⟩ =
          convI hV ⟨y, E.hXN hy⟩ * convI hV ⟨s, E.hXN (hSX hs)⟩ * (convI hV ⟨y, E.hXN hy⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact this
    obtain ⟨s', hs'S, hs'e⟩ := (mem_autI hV).1 h1
    have hmem : y * s * y⁻¹ * (s' : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
      mul_inv_mem_centralizer (hV := hV) (E.hXN hysy) s'.2 hs'e.symm
    have hmemX : y * s * y⁻¹ * (s' : G)⁻¹ ∈ C :=
      ⟨X.mul_mem hysy (X.inv_mem (hSX hs'S)), hmem⟩
    have : y * s * y⁻¹ = (y * s * y⁻¹ * (s' : G)⁻¹) * s' := by group
    rw [this]
    exact K.mul_mem (Subgroup.mem_sup_left hmemX)
      (Subgroup.mem_sup_right (Subgroup.mem_sup_right hs'S))
  have hnormK : ∀ (y : G) (hy : y ∈ X), convI hV ⟨y, E.hXN hy⟩ ∈
      Subgroup.normalizer (autI hV S : Set (MulAut (IntMod V hV))) →
      K ≤ K.comap (MulAut.conj y).toMonoidHom := by
    intro y hy hyn
    refine sup_le (fun c hc => ?_) (sup_le (fun q hq => ?_) (fun s hs => ?_))
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hCX hy) c).1 hc)
    · have : y * q * y⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 X hy) q).1 hq
      exact Subgroup.mem_sup_right (Subgroup.mem_sup_left this)
    · exact hconjS y hy hyn s hs
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := by
    have hxinv : convI hV ⟨x⁻¹, E.hXN (X.inv_mem hx)⟩ ∈
        Subgroup.normalizer (autI hV S : Set (MulAut (IntMod V hV))) := by
      have e : convI hV ⟨x⁻¹, E.hXN (X.inv_mem hx)⟩ = (convI hV ⟨x, E.hXN hx⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [e]
      exact Subgroup.inv_mem _ hxn
    apply mem_normalizer_of_conj
    · exact fun k hk => hnormK x hx hxn hk
    · intro k hk
      have := hnormK x⁻¹ (X.inv_mem hx) hxinv hk
      simpa [mul_assoc] using this
  have hK2 : IsSylowTwoOf (B6.conjSub x P₀) K := by
    have := B6.isSylowTwoOf_conjSub hKsyl x
    have hKx : B6.conjSub x K = K := Subgroup.mem_normalizer_iff_map_conj_eq.1 hxK
    rwa [hKx] at this
  obtain ⟨g, hgK, hgx⟩ := B6.isSylowTwoOf_exists_conj hKsyl hK2
  have hz : g⁻¹ * x ∈ Subgroup.normalizer (P₀ : Set G) := by
    apply mem_normalizer_of_conj
    · intro y hy
      have h1 : x * y * x⁻¹ ∈ B6.conjSub x P₀ := by
        rw [B6.mem_conjSub]
        simpa [mul_assoc] using hy
      rw [hgx, B6.mem_conjSub] at h1
      simpa [mul_assoc] using h1
    · intro y hy
      have h1 : g * y * g⁻¹ ∈ B6.conjSub g P₀ := by
        rw [B6.mem_conjSub]
        simpa [mul_assoc] using hy
      rw [← hgx, B6.mem_conjSub] at h1
      simpa [mul_assoc] using h1
  have hbP₀ : baum P₀ = S := (baum_eq_of_le (le_sup_right : S ≤ P₀) hP₀R).symm
  have hzS : g⁻¹ * x ∈ Subgroup.normalizer (S : Set G) := by
    rw [← hbP₀]
    exact normalizer_le_normalizer_baum P₀ hz
  have hP₀S : P₀ ≤ Subgroup.normalizer (S : Set G) :=
    sup_le (E.QR.trans E.R_le_normalizer_baum) Subgroup.le_normalizer
  have hgmem : g ∈ ((C : Set G) * (P₀ : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left C P₀ hP₀N]
    exact hgK
  obtain ⟨c, hc, p, hp, hcp⟩ := hgmem
  have hcp' : c * p = g := hcp
  have hgX : g ∈ X := by
    rw [← hcp']
    exact X.mul_mem hc.1 ((hP₀R.trans E.R_le_X) hp)
  refine ⟨c, hc, p * (g⁻¹ * x), ⟨X.mul_mem ((hP₀R.trans E.R_le_X) hp)
    (X.mul_mem (X.inv_mem hgX) hx), Subgroup.mul_mem _ (hP₀S hp) hzS⟩, ?_⟩
  rw [← mul_assoc, hcp']
  group

end EntryPlus

end CFSG.Quasithin.C124
