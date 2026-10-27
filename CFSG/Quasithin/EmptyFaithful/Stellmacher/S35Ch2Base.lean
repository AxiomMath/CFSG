module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch2

open S35.Ch
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure Chart2 (δ : Geo H M) where
  θ : ↥(stab δ) →* Perm (Fin 5)
  π : ↥(Vn δ) →* orth.W
  le : Cb δ ≤ Vn δ
  surj : Function.Surjective θ
  π_surj : Function.Surjective π
  π_eq_one : ∀ x : ↥(Vn δ), π x = 1 ↔ (x : G) ∈ Cb δ
  π_conj : ∀ (g : ↥(stab δ)) (x : ↥(Vn δ)), π (conjV g x) = orth.act (θ g) (π x)
  θ_eq_one : ∀ g : ↥(stab δ), θ g = 1 ↔ ∀ x ∈ Vn δ, (g : G) * x * (g : G)⁻¹ * x⁻¹ ∈ Cb δ

noncomputable def chart2OfSecData {δ : Geo H M} (hle : Cb δ ≤ Vn δ)
    [nrm : ((Cb δ).subgroupOf (Vn δ)).Normal] (θ : ↥(stab δ) →* Perm (Fin 5))
    (β : orth.W →* ↥(Vn δ) ⧸ (Cb δ).subgroupOf (Vn δ)) (hθs : Function.Surjective θ)
    (hθk : θ.ker = (cSecIn (stab δ) (Cb δ) (Vn δ)).subgroupOf (stab δ))
    (hsd : SecData orth (stab δ) (Cb δ) (Vn δ) θ β) : Chart2 δ :=
  have hsec : IsSec (stab δ) (Cb δ) (Vn δ) :=
    IsModelSec.isSec (⟨nrm, θ, β, hθs, hθk, hsd⟩ : IsModelSec orth (stab δ) (Cb δ) (Vn δ)) hle
  let e : orth.W ≃* ↥(Vn δ) ⧸ (Cb δ).subgroupOf (Vn δ) :=
    MulEquiv.ofBijective β ⟨hsd.inj, hsd.surj⟩
  let π : ↥(Vn δ) →* orth.W := e.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  have hβπ : ∀ x : ↥(Vn δ), β (π x) = QuotientGroup.mk x := fun x => by
    show e (e.symm (QuotientGroup.mk x)) = _
    exact e.apply_symm_apply _
  { θ := θ
    π := π
    le := hle
    surj := hθs
    π_surj := fun w => by
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β w)
      exact ⟨x, hsd.inj (by rw [hβπ, hx])⟩
    π_eq_one := fun x => by
      constructor
      · intro h
        have h1 : (QuotientGroup.mk x : ↥(Vn δ) ⧸ (Cb δ).subgroupOf (Vn δ)) = 1 := by
          rw [← hβπ, h, map_one]
        exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
      · intro h
        have h1 : (QuotientGroup.mk x : ↥(Vn δ) ⧸ (Cb δ).subgroupOf (Vn δ)) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h)
        show e.symm (QuotientGroup.mk x) = 1
        rw [h1]
        exact map_one e.symm
    π_conj := fun g x => by
      obtain ⟨hkx, h⟩ := hsd.equiv g (π x) x (hβπ x)
      apply hsd.inj
      rw [h, hβπ]
      rfl
    θ_eq_one := fun g => by
      rw [← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf]
      constructor
      · intro h x hx
        exact ((F53B3.N37.mem_cSecIn_iff (F := stab δ) (L := Cb δ) (X := Vn δ)
          hsec.normL).mp h).2 x hx
      · intro h
        exact Subgroup.subset_closure ⟨g.2, h⟩ }

omit [Finite G] in
theorem nonempty_chart2 {δ : Geo H M} (hle : Cb δ ≤ Vn δ)
    (h : IsOrthSec (stab δ) (Cb δ) (Vn δ)) : Nonempty (Chart2 δ) := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  exact ⟨chart2OfSecData hle θ β hθs hθk hsd⟩

theorem exists_chart2 (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    Nonempty (Chart2 δ) :=
  nonempty_chart2 (S34.Cb_le_Vn δ) (hS.orth δ hδ)

end S35.Ch2

end F53.Stellmacher

end CFSG.Quasithin
