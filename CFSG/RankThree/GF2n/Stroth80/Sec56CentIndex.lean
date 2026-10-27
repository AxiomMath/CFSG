module

public import CFSG.RankThree.GF2n.Stroth80.Sec56CentInf
public import CFSG.RankThree.GF2n.Stroth80.GlobalModelData

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem StrothHyp.card_cent_inf (H : StrothHyp M Q Z)
    {E F : Subgroup G} {gE gF : G} (hE : E = conjSubgroup gE Z) (hF : F = conjSubgroup gF Z)
    (hEQ : E ≤ Q) (hFQ : F ≤ Q) (hEZ : E ≠ Z) (hFZ : F ≠ Z) (hFE : ¬ F ≤ E ⊔ Z) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer (E : Set G)) =
      Nat.card ↥(Q ⊓ Subgroup.centralizer (E : Set G) ⊓ Subgroup.centralizer (F : Set G)) *
        Nat.card Z := by
  obtain ⟨nn, γ, M₀, -, h⟩ := stroth_globalModelDataGF H
  obtain ⟨e, he0, he⟩ := h.line gE (hE ▸ hEZ) (hE ▸ hEQ)
  obtain ⟨e', -, he'⟩ := h.line gF (hF ▸ hFZ) (hF ▸ hFQ)
  rw [← hE] at he
  rw [← hF] at he'
  have hind : ∀ s : GaloisField 2 nn, e' ≠ s • e := by
    intro s hs
    apply hFE
    intro x hx
    have hxQ := hFQ hx
    obtain ⟨t, ht⟩ := (he' (M₀.π x)).mp (Tim79.QuadModel.pi_mem_img M₀ hx hxQ)
    obtain ⟨y, hyE, hyQ, hy⟩ := (he (M₀.π x)).mpr ⟨t * s, by rw [ht, hs, smul_smul]⟩
    have hyx : y⁻¹ * x ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ hyQ hxQ).mp hy
    have e1 : x = y * (y⁻¹ * x) := by group
    rw [e1]
    exact Subgroup.mul_mem_sup hyE hyx
  rw [← h.card]
  exact Tim79.QuadModel.card_centralizer_inf h.reg hEQ hFQ he0 he he' hind

theorem map_eq_of_card_eq {H S : Type*} [Group H] [Group S] [Finite H] (φ : H →* S)
    {T P : Subgroup H} {U : Subgroup S} (hTP : T ≤ P) (hP : P.map φ = U)
    (hcard : Nat.card T = Nat.card ↥(T ⊓ φ.ker) * Nat.card U) : T.map φ = U := by
  have hle : T.map φ ≤ U := hP ▸ Subgroup.map_mono hTP
  have hU : Finite U := by
    rw [← hP]
    exact Finite.of_surjective (fun x : P => (⟨φ x, Subgroup.mem_map_of_mem φ x.2⟩ : P.map φ))
      (by rintro ⟨y, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hker : Nat.card (φ.domRestrict T).ker = Nat.card ↥(T ⊓ φ.ker) := by
    rw [MonoidHom.ker_domRestrict]
    exact Nat.card_congr
      { toFun := fun x => ⟨(x.1 : H), Subgroup.mem_inf.mpr ⟨x.1.2, Subgroup.mem_subgroupOf.mp x.2⟩⟩
        invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have h1 := Subgroup.card_ker_mul_card_range (φ.domRestrict T)
  rw [hker, MonoidHom.domRestrict_range, hcard] at h1
  have hpos : 0 < Nat.card ↥(T ⊓ φ.ker) := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos h1).ge
