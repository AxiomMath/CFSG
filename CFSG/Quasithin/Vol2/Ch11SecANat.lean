module

public import CFSG.Quasithin.Background.AutOnSylow
public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag
public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

@[expose] noncomputable def conjV (V : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer (V : Set G)) : MulAut ↥V :=
  conjAct V ⟨x, hx⟩

theorem conjV_apply_coe (V : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (v : ↥V) : ((conjV V x hx v : ↥V) : G) = x * v * x⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl ⟨x, hx⟩) v

theorem conjV_mul (V : Subgroup G) {x y : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G)) :
    conjV V (x * y) (Subgroup.mul_mem _ hx hy) = conjV V x hx * conjV V y hy := by
  ext v
  simp only [MulAut.mul_apply, conjV_apply_coe]
  group

theorem conjV_inv (V : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    conjV V x⁻¹ (Subgroup.inv_mem _ hx) = (conjV V x hx)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← conjV_mul]
  ext v
  simp [conjV_apply_coe]

theorem conjV_mem_autOn {L V : Subgroup G} {x : G} (hxL : x ∈ L)
    (hx : x ∈ Subgroup.normalizer (V : Set G)) : conjV V x hx ∈ autOn L V :=
  ⟨⟨x, hx⟩, hxL, rfl⟩

theorem mem_autOn_iff {L V : Subgroup G} {h : MulAut ↥V} :
    h ∈ autOn L V ↔ ∃ x, ∃ _ : x ∈ L, ∃ hx : x ∈ Subgroup.normalizer (V : Set G),
      h = conjV V x hx := by
  constructor
  · rintro ⟨⟨x, hx⟩, hxL, rfl⟩
    exact ⟨x, hxL, hx, rfl⟩
  · rintro ⟨x, hxL, hx, rfl⟩
    exact conjV_mem_autOn hxL hx

theorem isEndStable_iff {L V : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G))
    (C U : Subgroup G) :
    IsEndStable L V C U ↔ EndStableW (autOn L V) (C.subgroupOf V) (U.subgroupOf V) := by
  constructor
  · intro hE φ hφZ hφH u hu
    refine hE φ (fun c hc => hφZ c hc) ?_ u hu
    intro l hl v w hw
    have := hφH (conjV V l (hL hl)) (conjV_mem_autOn hl (hL hl)) v
    have hw' : conjV V l (hL hl) v = w := Subtype.ext (by rw [conjV_apply_coe, hw])
    rw [hw'] at this
    simpa [Subgroup.mem_subgroupOf, conjV_apply_coe] using this
  · intro hE φ hφC hφL u hu
    refine hE φ (fun z hz => hφC z hz) ?_ u hu
    intro h hh w
    obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hh
    have := hφL l hl w (conjV V l hlV w) (conjV_apply_coe V hlV w)
    simpa [Subgroup.mem_subgroupOf, conjV_apply_coe] using this

theorem conjV_mem_stabW_iff {V U : Subgroup G} (hU : U ≤ V) {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    conjV V x hx ∈ stabW (U.subgroupOf V) ↔ x ∈ Subgroup.normalizer (U : Set G) := by
  rw [mem_stabW, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    by_cases hg : g ∈ V
    · have := h ⟨g, hg⟩
      simpa [Subgroup.mem_subgroupOf, conjV_apply_coe] using this
    · have hg' : x * g * x⁻¹ ∉ V := fun h' => hg ((Subgroup.mem_normalizer_iff.mp hx g).mpr h')
      exact ⟨fun h1 => absurd (hU h1) hg, fun h1 => absurd (hU h1) hg'⟩
  · intro h v
    have := h v
    simpa [Subgroup.mem_subgroupOf, conjV_apply_coe] using this

theorem isSylowTwoOf_autOn [Finite G] {S L V : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (V : Set G)) (hS : QuasithinUnique.IsSylowTwoOf S L) :
    QuasithinUnique.IsSylowTwoOf (autOn S V) (autOn L V) :=
  CFSG.Quasithin.AutOn.isSylowTwoOf_autOn hS hL

end CFSG.Quasithin.Vol2.Ch11.SecA
