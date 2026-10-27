module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56cGB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56Irr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.C56

variable {G : Type} [Group G] [Finite G]

@[expose] def GenI (E P : Subgroup G) (b : G) : Subgroup G :=
  Subgroup.closure ((E : Set G) ∪ {y | ∃ x ∈ P, y = x * b * x⁻¹ * b⁻¹})

omit [Finite G] in
theorem le_GenI {E P : Subgroup G} {b : G} : E ≤ GenI E P b :=
  fun _ hy => Subgroup.subset_closure (Or.inl hy)

omit [Finite G] in
theorem comm_mem_GenI {E P : Subgroup G} {b x : G} (hx : x ∈ P) :
    x * b * x⁻¹ * b⁻¹ ∈ GenI E P b :=
  Subgroup.subset_closure (Or.inr ⟨x, hx, rfl⟩)

omit [Finite G] in
theorem GenI_le {E P U : Subgroup G} {b : G} (hEU : E ≤ U)
    (h : ∀ x ∈ P, x * b * x⁻¹ * b⁻¹ ∈ U) : GenI E P b ≤ U := by
  refine (Subgroup.closure_le U).mpr ?_
  rintro y (hy | ⟨x, hx, rfl⟩)
  · exact hEU hy
  · exact h x hx

theorem normalizer_GenI {X E F : Subgroup G}
    (hq : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5))) (hO : IsOrthSec X E F) (hEF : E ≤ F)
    {b : G} (hbF : ∀ x ∈ oTwoRes X, x * b * x⁻¹ * b⁻¹ ∈ F) :
    oTwoRes X ≤ Subgroup.normalizer
      (GenI E (oTwoRes X ⊓ pCoreOf 2 X) b : Set G) := by
  have hs : IsSec X E F := IsModelSec.isSec hO hEF
  have hLX : oTwoRes X ≤ X := oTwoRes_le X
  have key : ∀ l ∈ oTwoRes X, ∀ y ∈ GenI E (oTwoRes X ⊓ pCoreOf 2 X) b,
      l * y * l⁻¹ ∈ GenI E (oTwoRes X ⊓ pCoreOf 2 X) b := by
    intro l hl y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | ⟨x, hx, rfl⟩
      · exact le_GenI ((Subgroup.mem_normalizer_iff.mp (hs.normL (hLX hl)) y).mp hy)
      · have hxL := hx.1
        have hxQ := hx.2
        have hx'L : l * x * l⁻¹ ∈ oTwoRes X :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes X (hLX hl)) x).mp hxL
        have hx'Q : l * x * l⁻¹ ∈ pCoreOf 2 X :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 X (hLX hl)) x).mp hxQ
        have hf : l * b * l⁻¹ * b⁻¹ ∈ F := hbF l hl
        have hg' : (l * x * l⁻¹) * b * (l * x * l⁻¹)⁻¹ * b⁻¹ ∈ F := hbF _ hx'L
        have he : (l * x * l⁻¹) * (l * b * l⁻¹ * b⁻¹) * (l * x * l⁻¹)⁻¹ *
            (l * b * l⁻¹ * b⁻¹)⁻¹ ∈ E :=
          IsOrthSec.comm_pCore hq hO hEF _ hx'Q _ hf
        have he' : (l * b * l⁻¹ * b⁻¹) * ((l * x * l⁻¹) * b * (l * x * l⁻¹)⁻¹ * b⁻¹) *
            (l * b * l⁻¹ * b⁻¹)⁻¹ * ((l * x * l⁻¹) * b * (l * x * l⁻¹)⁻¹ * b⁻¹)⁻¹ ∈ E :=
          hs.comm _ hf _ hg'
        have hgI := comm_mem_GenI (E := E) (b := b) (Subgroup.mem_inf.mpr ⟨hx'L, hx'Q⟩)
        have e : l * (x * b * x⁻¹ * b⁻¹) * l⁻¹ =
            ((l * x * l⁻¹) * (l * b * l⁻¹ * b⁻¹) * (l * x * l⁻¹)⁻¹ * (l * b * l⁻¹ * b⁻¹)⁻¹) *
            ((l * b * l⁻¹ * b⁻¹) * ((l * x * l⁻¹) * b * (l * x * l⁻¹)⁻¹ * b⁻¹) *
              (l * b * l⁻¹ * b⁻¹)⁻¹ * ((l * x * l⁻¹) * b * (l * x * l⁻¹)⁻¹ * b⁻¹)⁻¹) *
            ((l * x * l⁻¹) * b * (l * x * l⁻¹)⁻¹ * b⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (le_GenI he) (le_GenI he')) hgI
    | one => simp
    | mul y z _ _ hy hz =>
      have : l * (y * z) * l⁻¹ = (l * y * l⁻¹) * (l * z * l⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hy hz
    | inv y _ hy =>
      have : l * y⁻¹ * l⁻¹ = (l * y * l⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hy
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key l hl y, fun hy => ?_⟩
  have := key l⁻¹ ((oTwoRes X).inv_mem hl) _ hy
  simpa [mul_assoc] using this

theorem comm_mem_of_bound {X E F : Subgroup G}
    (hq : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5))) (hO : IsOrthSec X E F) (hEF : E ≤ F)
    {b : G} (hbF : ∀ x ∈ oTwoRes X, x * b * x⁻¹ * b⁻¹ ∈ F) {Y U : Subgroup G}
    (hEU : E ≤ U) (hUF : U ≤ F) (hUi : E.relIndex U ≤ 4)
    (hUY : ∀ x ∈ oTwoRes X ⊓ pCoreOf 2 X, x ∈ Y → x * b * x⁻¹ * b⁻¹ ∈ U)
    (hY : ∀ x ∈ oTwoRes X ⊓ pCoreOf 2 X, ∀ t ∈ oTwoRes X ⊓ pCoreOf 2 X, x ∉ Y → t ∉ Y →
      t⁻¹ * x ∈ Y) :
    ∀ x ∈ oTwoRes X ⊓ pCoreOf 2 X, x * b * x⁻¹ * b⁻¹ ∈ E := by
  have hs : IsSec X E F := IsModelSec.isSec hO hEF
  have hLX : oTwoRes X ≤ X := oTwoRes_le X
  have hgF : ∀ x ∈ oTwoRes X ⊓ pCoreOf 2 X, x * b * x⁻¹ * b⁻¹ ∈ F := fun x hx => hbF x hx.1
  have hIF : GenI E (oTwoRes X ⊓ pCoreOf 2 X) b ≤ F := GenI_le hEF hgF
  have hbound : E.relIndex (GenI E (oTwoRes X ⊓ pCoreOf 2 X) b) ≤ 8 := by
    by_cases hP : ∀ t ∈ oTwoRes X ⊓ pCoreOf 2 X, t ∈ Y
    · have hIU : GenI E (oTwoRes X ⊓ pCoreOf 2 X) b ≤ U :=
        GenI_le hEU fun x hx => hUY x hx (hP x hx)
      exact (relIndex_le_of_le hIU).trans (hUi.trans (by norm_num))
    · push Not at hP
      obtain ⟨t, ht, htY⟩ := hP
      have htF : t * b * t⁻¹ * b⁻¹ ∈ F := hgF t ht
      have hn : t * b * t⁻¹ * b⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
        mem_normalizer_of_sec hs hEU hUF htF
      have hsq : (t * b * t⁻¹ * b⁻¹) ^ 2 ∈ U := hEU (hs.sq _ htF)
      have h2 := relIndex_sup_zpowers_le_two hn hsq
      have h2' : U.relIndex (U ⊔ Subgroup.zpowers (t * b * t⁻¹ * b⁻¹)) ≤ 2 :=
        Nat.le_of_dvd (by norm_num) h2
      have hUK : U ≤ U ⊔ Subgroup.zpowers (t * b * t⁻¹ * b⁻¹) := le_sup_left
      have hIK : GenI E (oTwoRes X ⊓ pCoreOf 2 X) b ≤
          U ⊔ Subgroup.zpowers (t * b * t⁻¹ * b⁻¹) := by
        refine GenI_le (hEU.trans hUK) fun x hx => ?_
        by_cases hxY : x ∈ Y
        · exact hUK (hUY x hx hxY)
        · obtain ⟨x0, rfl⟩ : ∃ x0, x = t * x0 := ⟨t⁻¹ * x, by group⟩
          have hx0P : x0 ∈ oTwoRes X ⊓ pCoreOf 2 X := by
            have := Subgroup.mul_mem _ ((oTwoRes X ⊓ pCoreOf 2 X).inv_mem ht) hx
            simpa using this
          have hx0Y : x0 ∈ Y := by
            have := hY _ hx t ht hxY htY
            simpa using this
          have hg0U : x0 * b * x0⁻¹ * b⁻¹ ∈ U := hUY x0 hx0P hx0Y
          have he : t * (x0 * b * x0⁻¹ * b⁻¹) * t⁻¹ * (x0 * b * x0⁻¹ * b⁻¹)⁻¹ ∈ E :=
            IsOrthSec.comm_pCore hq hO hEF t ht.2 _ (hgF x0 hx0P)
          have e : t * x0 * b * (t * x0)⁻¹ * b⁻¹ =
              (t * (x0 * b * x0⁻¹ * b⁻¹) * t⁻¹ * (x0 * b * x0⁻¹ * b⁻¹)⁻¹) *
              (x0 * b * x0⁻¹ * b⁻¹) * (t * b * t⁻¹ * b⁻¹) := by group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hUK (hEU he)) (hUK hg0U))
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      calc E.relIndex (GenI E (oTwoRes X ⊓ pCoreOf 2 X) b)
          ≤ E.relIndex (U ⊔ Subgroup.zpowers (t * b * t⁻¹ * b⁻¹)) := relIndex_le_of_le hIK
        _ = E.relIndex U * U.relIndex (U ⊔ Subgroup.zpowers (t * b * t⁻¹ * b⁻¹)) :=
          (Subgroup.relIndex_mul_relIndex E U _ hEU hUK).symm
        _ ≤ 4 * 2 := Nat.mul_le_mul hUi h2'
  rcases hO.eq_or_eq_of_oTwoRes le_GenI hIF (normalizer_GenI hq hO hEF hbF) with h | h
  · intro x hx
    have := comm_mem_GenI (E := E) (b := b) hx
    rwa [h] at this
  · exfalso
    rw [h, hO.relIndex_eq] at hbound
    omega

end S35.C56

end F53.Stellmacher

end CFSG.Quasithin
