module

public import CFSG.Quasithin.EmptyFaithful.SBc11Cent
public import CFSG.Quasithin.EmptyFaithful.SBc11List

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc11

section Ctx

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem not_isHatA6Block (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hlist : IsPSL 3 2 1 ↥(Star153 T I L) ∨ IsAlt 6 ↥(Star153 T I L) ∨ IsPSU 3 3 1 ↥(Star153 T I L)) :
    ¬ IsHatA6Block L := by
  rintro ⟨hshort, ⟨-, hcard3, -⟩, -, hcentr⟩
  obtain ⟨-, -, hIL, -, -, hperf⟩ := ctx_basic c
  obtain ⟨hLN, -, hnt⟩ := ctx_star c
  obtain ⟨ψ, hψs, -, hψ1⟩ := exists_star_hom c
  have hcen : Subgroup.center ↥(Star153 T I L) = ⊥ := center_eq_bot_of_list hlist
  have hne : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard3
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hzk : z ∈ ψ.ker := center_le_ker_of_center_eq_bot ψ hψs hcen hz
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
  have hlc : (l : G) ∈ Subgroup.centralizer (UI153 T I : Set G) := (hψ1 l).1 hzk
  have hUIc : ∀ x ∈ UI153 T I, ∀ y ∈ UI153 T I, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (ctx_UI c hx).2 y (ctx_UI c hy).1).symm
  have hUI2 : IsPGroup 2 ↥(UI153 T I) :=
    (pCoreOf_isPGroup 2 I).to_le (fun x hx => (ctx_UI c hx).1)
  have hUIL : UI153 T I ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
    hIL (pCoreOf_le 2 I (ctx_UI c hx).1)
  have hlb : (l : G) ∈ Subgroup.centralizer (blockU L : Set G) :=
    centralizer_le_centralizer_blockU hshort hperf hUIc hUI2 hLN hUIL hnt ⟨l.2, hlc⟩
  have hlq : (l : G) ∈ pCoreOf 2 L := hcentr ▸ (⟨l.2, hlb⟩ : (l : G) ∈ L ⊓ Subgroup.centralizer (blockU L : Set G))
  have hl1 : (QuotientGroup.mk l : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 :=
    (QuotientGroup.eq_one_iff l).2 ((CFSG.QuasithinUnique.AppC.mem_pCore_iff_mem_blockQ l).2 hlq)
  exact hz1 (Subtype.ext hl1)

end Ctx

end SBc11

end CFSG.Quasithin
