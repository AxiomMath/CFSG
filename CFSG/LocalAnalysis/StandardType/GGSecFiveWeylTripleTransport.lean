module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ct_tr_congr_apply {G G' : Type} [Group G] [Group G']
    {Bs : Subgroup G} {Bs' : Subgroup G'} (e : ↥Bs ≃* ↥Bs') (φ : MulAut ↥Bs) (b : ↥Bs) :
    MulAut.congr e φ (e b) = e (φ b) := by
  simp [MulAut.congr]

private lemma ct_tr_congr_apply' {G G' : Type} [Group G] [Group G']
    {Bs : Subgroup G} {Bs' : Subgroup G'} (e : ↥Bs ≃* ↥Bs') (φ : MulAut ↥Bs) (b' : ↥Bs') :
    MulAut.congr e φ b' = e (φ (e.symm b')) := by
  simp [MulAut.congr]

private noncomputable def ct_tr_fixedEquiv {G G' : Type} [Group G] [Group G']
    {Bs : Subgroup G} {Bs' : Subgroup G'} (e : ↥Bs ≃* ↥Bs') (φ : MulAut ↥Bs) :
    {b : ↥Bs // φ b = b} ≃ {b' : ↥Bs' // (MulAut.congr e φ) b' = b'} where
  toFun b := ⟨e b, by rw [ct_tr_congr_apply, b.2]⟩
  invFun b' := ⟨e.symm b', by
    have h := b'.2
    rw [ct_tr_congr_apply'] at h
    exact by simpa using congrArg e.symm h⟩
  left_inv b := by ext; simp
  right_inv b' := by ext; simp

private lemma ct_tr_card_fixed {G G' : Type} [Group G] [Group G']
    {Bs : Subgroup G} {Bs' : Subgroup G'} (e : ↥Bs ≃* ↥Bs') (φ : MulAut ↥Bs) :
    Nat.card {b' : ↥Bs' // (MulAut.congr e φ) b' = b'} =
      Nat.card {b : ↥Bs // φ b = b} :=
  Nat.card_congr (ct_tr_fixedEquiv e φ).symm

private theorem ct_tr_isReflection_congr {G G' : Type} [Group G] [Group G'] (p : ℕ)
    {Bs : Subgroup G} {Bs' : Subgroup G'} (e : ↥Bs ≃* ↥Bs') (φ : MulAut ↥Bs) :
    GGIsReflection p φ ↔ GGIsReflection p (MulAut.congr e φ) := by
  constructor
  · rintro ⟨h2, hcard⟩
    refine ⟨?_, ?_⟩
    · exact (map_pow (MulAut.congr e) φ 2).symm.trans (by rw [h2, map_one])
    · rw [ct_tr_card_fixed]
      calc Nat.card {b : ↥Bs // φ b = b} * p = Nat.card ↥Bs := hcard
        _ = Nat.card ↥Bs' := Nat.card_congr e.toEquiv
  · rintro ⟨h2, hcard⟩
    refine ⟨?_, ?_⟩
    · apply (MulAut.congr e).injective
      rw [map_pow, map_one]
      exact h2
    · rw [← ct_tr_card_fixed (e := e) φ]
      calc Nat.card {b' : ↥Bs' // (MulAut.congr e φ) b' = b'} * p = Nat.card ↥Bs' := hcard
        _ = Nat.card ↥Bs := (Nat.card_congr e.toEquiv).symm

private theorem ct_tr_isTransvection_congr {G G' : Type} [Group G] [Group G'] (p : ℕ)
    {Bs : Subgroup G} {Bs' : Subgroup G'} (e : ↥Bs ≃* ↥Bs') (φ : MulAut ↥Bs) :
    GGIsTransvection p φ ↔ GGIsTransvection p (MulAut.congr e φ) := by
  have hcard : Nat.card {b' : ↥Bs' // (MulAut.congr e φ) b' = b'} =
      Nat.card {b : ↥Bs // φ b = b} := ct_tr_card_fixed e φ
  constructor
  · rintro ⟨hc, hfix⟩
    refine ⟨?_, ?_⟩
    · rw [hcard]
      calc Nat.card {b : ↥Bs // φ b = b} * p = Nat.card ↥Bs := hc
        _ = Nat.card ↥Bs' := Nat.card_congr e.toEquiv
    · intro b'
      have h := congrArg e (hfix (e.symm b'))
      simpa [ct_tr_congr_apply'] using h
  · rintro ⟨hc, hfix⟩
    refine ⟨?_, ?_⟩
    · rw [← hcard]
      calc Nat.card {b' : ↥Bs' // (MulAut.congr e φ) b' = b'} * p = Nat.card ↥Bs' := hc
        _ = Nat.card ↥Bs := (Nat.card_congr e.toEquiv).symm
    · intro b
      apply e.injective
      have h := hfix (e b)
      simpa [ct_tr_congr_apply] using h

private theorem ct_tr_isElemAbelian_congr {G G' : Type} [Group G] [Group G'] (p : ℕ)
    {Bs : Subgroup G} {Bs' : Subgroup G'} (e : ↥Bs ≃* ↥Bs') (h : IsElemAbelian p Bs) :
    IsElemAbelian p Bs' := by
  have hcomm : IsMulCommutative ↥Bs := h.1
  refine ⟨IsMulCommutative.of_comm (fun x y => ?_), ?_⟩
  · calc x * y = e (e.symm x * e.symm y) := by simp
      _ = e (e.symm y * e.symm x) := by
        rw [hcomm.is_comm.comm (e.symm x) (e.symm y)]
      _ = y * x := by simp
  · intro x hx
    let x' : ↥Bs' := ⟨x, hx⟩
    obtain ⟨y, hy⟩ := e.surjective x'
    have hx' : x = (e y : ↥Bs') := (congrArg (Subgroup.subtype Bs') hy).symm
    rw [hx']
    calc (((e y : ↥Bs') : G') ^ p) = ((e y : ↥Bs') ^ p : ↥Bs') := by simp
      _ = (e (y ^ p) : ↥Bs') := by rw [map_pow]
      _ = (e 1 : ↥Bs') := by
        rw [show y ^ p = 1 from Subtype.ext (h.2 y y.2)]
      _ = 1 := by simp

private abbrev ct_tr_G {G : Type} [Group G] (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs)) : Type :=
  SemidirectProduct ↥Bs ↥A A.subtype

private def ct_tr_Bs {G : Type} [Group G] (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs)) :
    Subgroup (ct_tr_G Bs A) :=
  (SemidirectProduct.inl : ↥Bs →* ct_tr_G Bs A).range

private noncomputable def ct_tr_e {G : Type} [Group G] (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs)) :
    ↥Bs ≃* ↥(ct_tr_Bs Bs A) :=
  MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := A.subtype))

private theorem ct_tr_e_coe {G : Type} [Group G] (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs))
    (x : ↥Bs) :
    (((ct_tr_e Bs A) x : ↥(ct_tr_Bs Bs A)) : ct_tr_G Bs A) = SemidirectProduct.inl x :=
  rfl

private theorem ct_tr_e_symm_val {G : Type} [Group G] (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs))
    (b : ↥(ct_tr_Bs Bs A)) :
    ((b : ct_tr_G Bs A)) = SemidirectProduct.inl ((ct_tr_e Bs A).symm b) := by
  rw [← ct_tr_e_coe Bs A ((ct_tr_e Bs A).symm b), MulEquiv.apply_symm_apply]

private theorem ct_tr_congr_apply_coe {G : Type} [Group G] (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs))
    (a : MulAut ↥Bs) (b : ↥(ct_tr_Bs Bs A)) :
    (((MulAut.congr (ct_tr_e Bs A) a) b : ↥(ct_tr_Bs Bs A)) : ct_tr_G Bs A)
      = SemidirectProduct.inl (a ((ct_tr_e Bs A).symm b)) :=
  rfl

private theorem ct_tr_finite {G : Type} [Group G] [Finite G] (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs)) :
    Finite (ct_tr_G Bs A) :=
  Finite.of_equiv (↥Bs × ↥A) (SemidirectProduct.equivProd (φ := A.subtype)).symm

private theorem ct_tr_conj_inl {G : Type} [Group G] (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs))
    (hc : ∀ x y : ↥Bs, x * y = y * x) (g : ct_tr_G Bs A) (b : ↥Bs) :
    g * SemidirectProduct.inl b * g⁻¹ = SemidirectProduct.inl ((g.right : MulAut ↥Bs) b) := by
  have haut : (SemidirectProduct.inr g.right * SemidirectProduct.inl b
      * (SemidirectProduct.inr g.right)⁻¹ : ct_tr_G Bs A)
      = SemidirectProduct.inl ((g.right : MulAut ↥Bs) b) := by
    rw [← map_inv]
    exact (SemidirectProduct.inl_aut (φ := A.subtype) (g := g.right) (n := b)).symm
  calc g * SemidirectProduct.inl b * g⁻¹
      = (SemidirectProduct.inl g.left * SemidirectProduct.inr g.right) * SemidirectProduct.inl b
          * (SemidirectProduct.inl g.left * SemidirectProduct.inr g.right)⁻¹ := by
        rw [SemidirectProduct.inl_left_mul_inr_right g]
    _ = SemidirectProduct.inl g.left
          * (SemidirectProduct.inr g.right * SemidirectProduct.inl b
              * (SemidirectProduct.inr g.right)⁻¹)
          * (SemidirectProduct.inl g.left)⁻¹ := by
        group
    _ = SemidirectProduct.inl ((g.right : MulAut ↥Bs) b) := by
        rw [haut, ← map_mul, ← map_inv, ← map_mul, hc g.left ((g.right : MulAut ↥Bs) b),
          mul_assoc, mul_inv_cancel, mul_one]

private theorem ct_tr_noTransvection {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs))
    (hc : ∀ x y : ↥Bs, x * y = y * x) (hNT : ∀ a ∈ A, ¬ GGIsTransvection p a) :
    GGNoTransvection p (ct_tr_Bs Bs A) := by
  intro φ hφ hT
  rw [ggInduced] at hφ
  obtain ⟨g, -, _, hφind⟩ := hφ
  have hEq : φ = MulAut.congr (ct_tr_e Bs A) (g.right : MulAut ↥Bs) := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [hφind b, ct_tr_e_symm_val Bs A b,
      ct_tr_conj_inl Bs A hc g ((ct_tr_e Bs A).symm b),
      ct_tr_congr_apply_coe Bs A (g.right : MulAut ↥Bs) b]
  have hT' : GGIsTransvection p (MulAut.congr (ct_tr_e Bs A) (g.right : MulAut ↥Bs)) := by
    rw [← hEq]
    exact hT
  exact hNT g.right g.right.property
    ((ct_tr_isTransvection_congr p (ct_tr_e Bs A) (g.right : MulAut ↥Bs)).mpr hT')

private theorem ct_tr_inr_conj_mem {G : Type} [Group G] (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs))
    (a : ↥A) {h : ct_tr_G Bs A} (hh : h ∈ ct_tr_Bs Bs A) :
    SemidirectProduct.inr a * h * (SemidirectProduct.inr a)⁻¹ ∈ ct_tr_Bs Bs A := by
  rw [ct_tr_Bs, MonoidHom.mem_range] at hh ⊢
  obtain ⟨b, rfl⟩ := hh
  refine ⟨(a : MulAut ↥Bs) b, ?_⟩
  rw [← map_inv]
  exact SemidirectProduct.inl_aut (φ := A.subtype) a b

private theorem ct_tr_map_le_induced {G : Type} [Group G] (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs)) :
    A.map (MulAut.congr (ct_tr_e Bs A)).toMonoidHom ≤ ggInduced ⊤ (ct_tr_Bs Bs A) := by
  intro ψ hψ
  simp only [SetLike.mem_coe] at hψ
  rw [Subgroup.mem_map] at hψ
  obtain ⟨a, ha, rfl⟩ := hψ
  rw [ggInduced]
  refine ⟨SemidirectProduct.inr ⟨a, ha⟩, trivial, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨h, hh, rfl⟩ := hx
      change SemidirectProduct.inr ⟨a, ha⟩ * h * (SemidirectProduct.inr ⟨a, ha⟩)⁻¹
        ∈ ct_tr_Bs Bs A
      exact ct_tr_inr_conj_mem Bs A ⟨a, ha⟩ hh
    · intro h hh
      rw [Subgroup.mem_map]
      refine ⟨(SemidirectProduct.inr ⟨a, ha⟩)⁻¹ * h * SemidirectProduct.inr ⟨a, ha⟩, ?_, ?_⟩
      · have hmem := ct_tr_inr_conj_mem Bs A (⟨a, ha⟩⁻¹ : ↥A) hh
        simpa only [map_inv, inv_inv] using hmem
      · change SemidirectProduct.inr ⟨a, ha⟩
            * ((SemidirectProduct.inr ⟨a, ha⟩)⁻¹ * h * SemidirectProduct.inr ⟨a, ha⟩)
            * (SemidirectProduct.inr ⟨a, ha⟩)⁻¹ = h
        group
  · intro b
    rw [ct_tr_e_symm_val Bs A b]
    change (((MulAut.congr (ct_tr_e Bs A) a) b : ↥(ct_tr_Bs Bs A)) : ct_tr_G Bs A)
        = SemidirectProduct.inr ⟨a, ha⟩ * SemidirectProduct.inl ((ct_tr_e Bs A).symm b)
            * (SemidirectProduct.inr ⟨a, ha⟩)⁻¹
    rw [ct_tr_congr_apply_coe Bs A a b]
    rw [← map_inv]
    exact SemidirectProduct.inl_aut (φ := A.subtype) ⟨a, ha⟩ ((ct_tr_e Bs A).symm b)

theorem ggRootRefl_of_noTransvection_in
    (G : Type) [Group G] [Finite G] (p : ℕ) (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs))
    (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs) (hNT : ∀ a ∈ A, ¬ GGIsTransvection p a)
    (ι : Type) (M : CoxeterMatrix ι) (hM : GGIsWeylMatrix M)
    (hG2 : ¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e)
    (f : M.Group ≃* ↥A) (hf : ∀ i : ι, GGIsReflection p ((f (M.simple i) : ↥A) : MulAut ↥Bs)) :
    ∀ a : ↥A, GGIsReflection p (a : MulAut ↥Bs) →
      ∃ (i : ι) (g : M.Group), a = f (g * M.simple i * g⁻¹) := by
  intro a ha
  have hfin := ct_tr_finite Bs A
  let e := ct_tr_e Bs A
  let Bs' := ct_tr_Bs Bs A
  let A' := A.map (MulAut.congr e).toMonoidHom
  let f' := f.trans (Subgroup.equivMapOfInjective A (MulAut.congr e).toMonoidHom
    (MulAut.congr e).injective)
  have hf' : ∀ i : ι, GGIsReflection p ((f' (M.simple i) : ↥A') : MulAut ↥Bs') := by
    intro i
    have h := (ct_tr_isReflection_congr p e ((f (M.simple i) : ↥A) : MulAut ↥Bs)).mp (hf i)
    have hcoe : ((f' (M.simple i) : ↥A') : MulAut ↥Bs') =
        (MulAut.congr e).toMonoidHom ((f (M.simple i) : ↥A) : MulAut ↥Bs) :=
      Subgroup.coe_equivMapOfInjective_apply A (MulAut.congr e).toMonoidHom
        (MulAut.congr e).injective (f (M.simple i))
    rw [hcoe]
    exact h
  let a' : ↥A' := ⟨MulAut.congr e (a : MulAut ↥Bs),
    Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom a.2⟩
  have ha' : GGIsReflection p (a' : MulAut ↥Bs') := by
    have h := (ct_tr_isReflection_congr p e (a : MulAut ↥Bs)).mp ha
    exact h
  obtain ⟨i, g, hg⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds (ct_tr_G Bs A) p
    (ct_tr_Bs Bs A) hp hp2
    (ct_tr_isElemAbelian_congr p e hEl)
    (ct_tr_noTransvection p Bs A hEl.1.is_comm.comm hNT)
    A' (ct_tr_map_le_induced Bs A) ι M hM hG2 f' hf' a' ha'
  refine ⟨i, g, ?_⟩
  let Φ := Subgroup.equivMapOfInjective A (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
  have hΦa : Φ a = a' := Subtype.ext rfl
  have hΦf : Φ (f (g * M.simple i * g⁻¹)) = f' (g * M.simple i * g⁻¹) :=
    MulEquiv.trans_apply f Φ _
  exact (Φ.injective (by rw [hΦf, ← hg, hΦa])).symm

end CFSG.StandardType

end
