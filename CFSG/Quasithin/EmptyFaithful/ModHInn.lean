module

public import CFSG.Quasithin.EmptyFaithful.ModGRed2
public import CFSG.Quasithin.EmptyFaithful.ModHRho
public import CFSG.Quasithin.EmptyFaithful.S153D35

public section

namespace CFSG.Quasithin.ModH

open CFSG.Quasithin

variable {G : Type} [Group G] {L I : Subgroup G}

@[expose] noncomputable def actQ (hN : I ≤ Subgroup.normalizer (L : Set G)) :
    ↥I →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
  quotConjHom.comp (Subgroup.inclusion hN)

theorem actQ_apply (hN : I ≤ Subgroup.normalizer (L : Set G)) (i : ↥I) :
    actQ hN i = quotConj (L := L) ⟨i, hN i.2⟩ := rfl

theorem quotConj_eq_conj_mk (l : ↥L) (hl : (l : G) ∈ Subgroup.normalizer (L : Set G)) :
    quotConj (L := L) ⟨l, hl⟩ = MulAut.conj (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [quotConj_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1

theorem conj_injective_of_center_bot {Q : Type} [Group Q] (hcen : Subgroup.center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  intro a b hab
  have hc : b⁻¹ * a ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h : a * x * a⁻¹ = b * x * b⁻¹ := by
      have := congrArg (fun φ : MulAut Q => φ x) hab
      simpa using this
    have h2 : (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ = x := by
      calc (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * x * a⁻¹) * b := by group
        _ = b⁻¹ * (b * x * b⁻¹) * b := by rw [h]
        _ = x := by group
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  rw [hcen, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

@[expose] noncomputable def innerPart (hN : I ≤ Subgroup.normalizer (L : Set G)) : Subgroup G :=
  ((MulAut.conj : (↥L ⧸ Subgroup.center ↥L) →* MulAut (↥L ⧸ Subgroup.center ↥L)).range.comap
    (actQ hN)).map I.subtype

theorem mem_innerPart {hN : I ≤ Subgroup.normalizer (L : Set G)} {g : G} :
    g ∈ innerPart hN ↔ ∃ hg : g ∈ I, ∃ q : ↥L ⧸ Subgroup.center ↥L,
      MulAut.conj q = actQ hN ⟨g, hg⟩ := by
  simp only [innerPart, Subgroup.mem_map, Subgroup.mem_comap, MonoidHom.mem_range,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, ⟨q, hq⟩, rfl⟩
    exact ⟨x.2, q, hq⟩
  · rintro ⟨hg, q, hq⟩
    exact ⟨⟨g, hg⟩, ⟨q, hq⟩, rfl⟩

theorem innerPart_le (hN : I ≤ Subgroup.normalizer (L : Set G)) : innerPart hN ≤ I := by
  intro g hg
  exact (mem_innerPart.1 hg).1

theorem le_innerPart (hN : I ≤ Subgroup.normalizer (L : Set G)) (hLI : L ≤ I) :
    L ≤ innerPart hN := by
  intro l hl
  refine mem_innerPart.2 ⟨hLI hl, QuotientGroup.mk ⟨l, hl⟩, ?_⟩
  rw [actQ_apply]
  exact (quotConj_eq_conj_mk ⟨l, hl⟩ _).symm

theorem innerPart_conj_mem (hN : I ≤ Subgroup.normalizer (L : Set G)) {s x : G} (hs : s ∈ I)
    (hx : x ∈ innerPart hN) : s * x * s⁻¹ ∈ innerPart hN := by
  obtain ⟨hxI, q, hq⟩ := mem_innerPart.1 hx
  have hsxI : s * x * s⁻¹ ∈ I := I.mul_mem (I.mul_mem hs hxI) (I.inv_mem hs)
  refine mem_innerPart.2 ⟨hsxI, (actQ hN ⟨s, hs⟩) q, ?_⟩
  have h1 : (⟨s * x * s⁻¹, hsxI⟩ : ↥I) = ⟨s, hs⟩ * ⟨x, hxI⟩ * ⟨s, hs⟩⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv, ← hq]
  ext y
  simp [MulAut.conj_apply]

theorem exists_conj_of_mem_innerPart (hN : I ≤ Subgroup.normalizer (L : Set G))
    (x : ↥(innerPart hN)) :
    ∃ q : ↥L ⧸ Subgroup.center ↥L,
      MulAut.conj q = actQ hN ⟨x.1, innerPart_le hN x.2⟩ := by
  obtain ⟨hg, q, hq⟩ := mem_innerPart.1 x.2
  exact ⟨q, hq⟩

@[expose] noncomputable def rho0Fun (hN : I ≤ Subgroup.normalizer (L : Set G))
    (x : ↥(innerPart hN)) : ↥L ⧸ Subgroup.center ↥L :=
  Classical.choose (exists_conj_of_mem_innerPart hN x)

theorem conj_rho0Fun (hN : I ≤ Subgroup.normalizer (L : Set G)) (x : ↥(innerPart hN)) :
    MulAut.conj (rho0Fun hN x) = actQ hN ⟨x.1, innerPart_le hN x.2⟩ :=
  Classical.choose_spec (exists_conj_of_mem_innerPart hN x)

theorem rho0Fun_mul (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) (x y : ↥(innerPart hN)) :
    rho0Fun hN (x * y) = rho0Fun hN x * rho0Fun hN y := by
  apply conj_injective_of_center_bot hcen
  have e1 : (⟨(x * y).1, innerPart_le hN (x * y).2⟩ : ↥I) =
      ⟨x.1, innerPart_le hN x.2⟩ * ⟨y.1, innerPart_le hN y.2⟩ :=
    Subtype.ext (Subgroup.coe_mul _ x y)
  rw [conj_rho0Fun hN (x * y), e1, map_mul, map_mul, conj_rho0Fun hN x, conj_rho0Fun hN y]

@[expose] noncomputable def rho0 (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) :
    ↥(innerPart hN) →* ↥L ⧸ Subgroup.center ↥L :=
  MonoidHom.mk' (rho0Fun hN) (rho0Fun_mul hN hcen)

theorem conj_rho0 (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) (x : ↥(innerPart hN)) :
    MulAut.conj (rho0 hN hcen x) = actQ hN ⟨x.1, innerPart_le hN x.2⟩ :=
  conj_rho0Fun hN x

theorem rho0_mk (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) (hLI : L ≤ I) (l : ↥L) :
    rho0 hN hcen ⟨l.1, le_innerPart hN hLI l.2⟩ = QuotientGroup.mk l := by
  apply conj_injective_of_center_bot hcen
  rw [conj_rho0, actQ_apply]
  exact quotConj_eq_conj_mk l _

theorem rho0_conj (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) (s : ↥I) (x : ↥(innerPart hN)) :
    rho0 hN hcen ⟨s.1 * x.1 * s.1⁻¹, innerPart_conj_mem hN s.2 x.2⟩ =
      actQ hN s (rho0 hN hcen x) := by
  apply conj_injective_of_center_bot hcen
  rw [conj_rho0]
  have h1 : (⟨s.1 * x.1 * s.1⁻¹, innerPart_le hN (innerPart_conj_mem hN s.2 x.2)⟩ : ↥I) =
      s * ⟨x.1, innerPart_le hN x.2⟩ * s⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv, ← conj_rho0 hN hcen x]
  ext y
  simp [MulAut.conj_apply]

theorem rho0_surjective (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) (hLI : L ≤ I) :
    Function.Surjective (rho0 hN hcen) := by
  intro q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨⟨l.1, le_innerPart hN hLI l.2⟩, rho0_mk hN hcen hLI l⟩

theorem innerPart_eq_sup {S : Subgroup G} (hN : I ≤ Subgroup.normalizer (L : Set G)) (hLI : L ≤ I)
    (hIeq : I = L ⊔ S) (hSI : S ≤ I) : innerPart hN = L ⊔ (S ⊓ innerPart hN) := by
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  apply le_antisymm
  · intro x hx
    have hxI : x ∈ L ⊔ S := hIeq ▸ innerPart_le hN hx
    obtain ⟨p, hp, s, hs, hxe⟩ := ModG.Red.exists_mul_of_mem_sup' hSL hxI
    have hpI : p ∈ innerPart hN := le_innerPart hN hLI hp
    have hsx : s ∈ innerPart hN := by
      have : s = p⁻¹ * x := by rw [hxe]; group
      rw [this]
      exact (innerPart hN).mul_mem ((innerPart hN).inv_mem hpI) hx
    rw [hxe]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right ⟨hs, hsx⟩)
  · exact sup_le (le_innerPart hN hLI) inf_le_right

section Ctx

variable [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem center_quot_eq_bot (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) :
    Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := by
  obtain ⟨-, hs, a, b, hab⟩ := c.c33.quasisimple
  have : (Subgroup.center (↥L ⧸ Subgroup.center ↥L)).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ Subgroup.center ↥L))
    with h | h
  · exact h
  · exfalso
    apply hab
    have ha : a ∈ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
      rw [h]
      exact Subgroup.mem_top a
    exact ((Subgroup.mem_center_iff.1 ha) b).symm

end Ctx

end CFSG.Quasithin.ModH
