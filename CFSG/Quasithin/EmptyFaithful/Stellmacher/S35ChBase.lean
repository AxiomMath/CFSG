module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Sit
public import CFSG.Quasithin.EmptyFaithful.SzF53B3NSec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem conj_mem_Vn {δ : Geo H M} {g : G} (hg : g ∈ stab δ) {x : G} (hx : x ∈ Vn δ) :
    g * x * g⁻¹ ∈ Vn δ :=
  (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ hg) x).mp hx

@[expose] def conjV {δ : Geo H M} (g : ↥(stab δ)) (x : ↥(Vn δ)) : ↥(Vn δ) :=
  ⟨(g : G) * (x : G) * (g : G)⁻¹, conj_mem_Vn g.2 x.2⟩

omit [Finite G] in
@[simp] theorem coe_conjV {δ : Geo H M} (g : ↥(stab δ)) (x : ↥(Vn δ)) :
    ((conjV g x : ↥(Vn δ)) : G) = (g : G) * (x : G) * (g : G)⁻¹ := rfl

structure Chart (δ : Geo H M) where
  θ : ↥(stab δ) →* Perm (Fin 5)
  π : ↥(Vn δ) →* orth.W
  le : Zv δ ≤ Vn δ
  surj : Function.Surjective θ
  π_surj : Function.Surjective π
  π_eq_one : ∀ x : ↥(Vn δ), π x = 1 ↔ (x : G) ∈ Zv δ
  π_conj : ∀ (g : ↥(stab δ)) (x : ↥(Vn δ)), π (conjV g x) = orth.act (θ g) (π x)
  θ_eq_one : ∀ g : ↥(stab δ), θ g = 1 ↔ ∀ x ∈ Vn δ, (g : G) * x * (g : G)⁻¹ * x⁻¹ ∈ Zv δ

noncomputable def chartOfSecData {δ : Geo H M} (hle : Zv δ ≤ Vn δ)
    [nrm : ((Zv δ).subgroupOf (Vn δ)).Normal] (θ : ↥(stab δ) →* Perm (Fin 5))
    (β : orth.W →* ↥(Vn δ) ⧸ (Zv δ).subgroupOf (Vn δ)) (hθs : Function.Surjective θ)
    (hθk : θ.ker = (cSecIn (stab δ) (Zv δ) (Vn δ)).subgroupOf (stab δ))
    (hsd : SecData orth (stab δ) (Zv δ) (Vn δ) θ β) : Chart δ :=
  have hsec : IsSec (stab δ) (Zv δ) (Vn δ) :=
    IsModelSec.isSec (⟨nrm, θ, β, hθs, hθk, hsd⟩ : IsModelSec orth (stab δ) (Zv δ) (Vn δ)) hle
  let e : orth.W ≃* ↥(Vn δ) ⧸ (Zv δ).subgroupOf (Vn δ) :=
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
        have h1 : (QuotientGroup.mk x : ↥(Vn δ) ⧸ (Zv δ).subgroupOf (Vn δ)) = 1 := by
          rw [← hβπ, h, map_one]
        exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
      · intro h
        have h1 : (QuotientGroup.mk x : ↥(Vn δ) ⧸ (Zv δ).subgroupOf (Vn δ)) = 1 :=
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
        exact ((F53B3.N37.mem_cSecIn_iff (F := stab δ) (L := Zv δ) (X := Vn δ)
          hsec.normL).mp h).2 x hx
      · intro h
        exact Subgroup.subset_closure ⟨g.2, h⟩ }

omit [Finite G] in
theorem nonempty_chart {δ : Geo H M} (hle : Zv δ ≤ Vn δ)
    (h : IsOrthSec (stab δ) (Zv δ) (Vn δ)) : Nonempty (Chart δ) := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  exact ⟨chartOfSecData hle θ β hθs hθk hsd⟩

omit [Finite G] in
theorem exists_chart_normalized {δ : Geo H M} (hle : Zv δ ≤ Vn δ)
    (h : IsOrthSec (stab δ) (Zv δ) (Vn δ)) {P : Subgroup G} (hP : IsSylowTwoOf P (stab δ)) :
    ∃ c : Chart δ, (P.subgroupOf (stab δ)).map c.θ = S5Syl := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, -⟩ := hsd.exists_normalized hθs hθk hP
  exact ⟨chartOfSecData hle Ψ β' hΨs hkΨ hsd', hPS⟩

theorem comm_mem_Zv_of_Qv (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) {q x : G}
    (hq : q ∈ Qv δ) (hx : x ∈ Vn δ) : q * x * q⁻¹ * x⁻¹ ∈ Zv δ := by
  have h1 : ⁅x, q⁆ ∈ ⁅Vn δ, Qv δ⁆ := Subgroup.commutator_mem_commutator hx hq
  have h2 := EmptyFaithful.Stellmacher.OrdinaryProofs.commutator_Vn_Qv_le hS.glob.amalg hδ
    (hS.glob.central δ hδ) h1
  have : q * x * q⁻¹ * x⁻¹ = ⁅x, q⁆⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [this]
  exact (Zv δ).inv_mem h2

omit [Finite G] in
theorem Qv_le_stab' (δ : Geo H M) : Qv δ ≤ stab δ := pCoreOf_le 2 _

omit [Finite G] in
theorem index_ker_five {X : Subgroup G} (φ : ↥X →* Perm (Fin 5)) (hφ : Function.Surjective φ) :
    φ.ker.index = 120 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top, Nat.card_perm,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

end S35.Ch

end F53.Stellmacher

end CFSG.Quasithin
