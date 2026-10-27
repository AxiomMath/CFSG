module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma6Rad
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B1MoreNineC
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace LRed4

section Irr

variable {V : Type} [CommGroup V]

theorem fixed_top_eq_fixV (A : Subgroup (MulAut V)) : XMod.fixed ↥A (⊤ : Subgroup V) = fixV A := by
  ext v
  constructor
  · rintro ⟨-, h⟩ x hx
    exact h ⟨x, hx⟩
  · intro h
    exact ⟨Subgroup.mem_top _, fun a => h a a.2⟩

theorem irr_dichotomy {A : Subgroup (MulAut V)} (hirr : XMod.IsIrrSec ↥A (fixV A) ⊤) {U : Subgroup V}
    (hU : XMod.IsInv ↥A U) : U ≤ fixV A ∨ U ⊔ fixV A = ⊤ := by
  have hJ : XMod.IsInv ↥A (U ⊔ fixV A) := by
    intro a x hx
    obtain ⟨u, hu, f, hf, rfl⟩ := Subgroup.mem_sup.1 hx
    rw [smul_mul']
    have h1 : a • f = f := hf a a.2
    rw [h1]
    exact Subgroup.mul_mem_sup (hU a u hu) hf
  rcases hirr.2 (U ⊔ fixV A) hJ le_sup_right le_top with h | h
  · exact Or.inl (le_sup_left.trans h.le)
  · exact Or.inr h

theorem isIrrSec_of_mem_irrPlus {L : Subgroup (MulAut V)} (hL : commV L = ⊤)
    (h : commV L ∈ IrrPlus L ⊤) : XMod.IsIrrSec ↥L (fixV L) ⊤ := by
  have h2 : XMod.IsIrrSec ↥L (XMod.fixed ↥L (commV L)) (commV L) := h.2.2.2
  rw [hL, fixed_top_eq_fixV] at h2
  exact h2

end Irr

section TwoGroup

variable {V : Type} [CommGroup V]

theorem commV_invariant_of_normalizer {L : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut V))) {u : V} (hu : u ∈ commV L) :
    g u ∈ commV L :=
  CFSG.Quasithin.commV_apply_mem_of_mem_normalizer hg hu

variable [Finite V]

open SemidirectProduct in
theorem commV_eq_top_of_sup_two (hV : ∀ v : V, v ^ 2 = 1) {L T : Subgroup (MulAut V)}
    (hT : IsPGroup 2 ↥T) (hTL : T ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (h : commV (L ⊔ T) = ⊤) : commV L = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup V := commV L with hU
  let φ : ↥T →* MulAut V := T.subtype
  have hUinv : ∀ t : ↥T, ∀ u ∈ U, φ t u ∈ U := fun t u hu => commV_invariant_of_normalizer (hTL t.2) hu
  let N : Subgroup (V ⋊[φ] ↥T) := U.map inl
  have hVp : IsPGroup 2 V := fun g => ⟨1, by simpa using hV g⟩
  have hP : IsPGroup 2 (V ⋊[φ] ↥T) := by
    obtain ⟨a, ha⟩ := hVp.exists_card_eq
    obtain ⟨b, hb⟩ := hT.exists_card_eq
    refine IsPGroup.of_card (n := a + b) ?_
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, ha, hb, pow_add]
  have hfin : Finite (V ⋊[φ] ↥T) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hNn : N.Normal := by
    refine ⟨fun n hn x => ?_⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hn
    have hx : x = inl x.left * inr x.right := by simp
    rw [hx]
    have e : (inl x.left * inr x.right * inl u * (inl x.left * inr x.right)⁻¹ : V ⋊[φ] ↥T) =
        inl (φ x.right u) := by
      have h1 : (inr x.right * inl u * (inr x.right)⁻¹ : V ⋊[φ] ↥T) = inl (φ x.right u) := by
        rw [← map_inv]
        exact (inl_aut (φ := φ) x.right u).symm
      calc (inl x.left * inr x.right * inl u * (inl x.left * inr x.right)⁻¹ : V ⋊[φ] ↥T)
          = inl x.left * (inr x.right * inl u * (inr x.right)⁻¹) * (inl x.left)⁻¹ := by group
        _ = inl x.left * inl (φ x.right u) * (inl x.left)⁻¹ := by rw [h1]
        _ = inl (x.left * φ x.right u * x.left⁻¹) := by rw [map_mul, map_mul, map_inv]
        _ = inl (φ x.right u) := by rw [mul_comm x.left, mul_inv_cancel_right]
    rw [e]
    exact Subgroup.mem_map_of_mem _ (hUinv _ u hu)
  have hQ : IsPGroup 2 ((V ⋊[φ] ↥T) ⧸ N) := hP.to_quotient N
  let f : V →* (V ⋊[φ] ↥T) ⧸ N := (QuotientGroup.mk' N).comp inl
  let Vb : Subgroup ((V ⋊[φ] ↥T) ⧸ N) := f.range
  have hVbn : Vb.Normal := by
    have h1 : (inl : V →* V ⋊[φ] ↥T).range.Normal := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      exact MonoidHom.normal_ker _
    have h2 : Vb = (inl : V →* V ⋊[φ] ↥T).range.map (QuotientGroup.mk' N) := MonoidHom.range_comp _ _
    rw [h2]
    exact h1.map _ (QuotientGroup.mk'_surjective N)
  have hTop : IsPGroup 2 ↥(⊤ : Subgroup ((V ⋊[φ] ↥T) ⧸ N)) := fun g => by
    obtain ⟨k, hk⟩ := hQ (g : (V ⋊[φ] ↥T) ⧸ N)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hf1 : ∀ u ∈ U, f u = 1 := fun u hu =>
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_map_of_mem _ hu)
  have hle : Vb ≤ ⁅Vb, (⊤ : Subgroup ((V ⋊[φ] ↥T) ⧸ N))⁆ := by
    have hrange : Vb = (commV (L ⊔ T)).map f := by
      rw [h, ← MonoidHom.range_eq_map]
    refine hrange.le.trans ?_
    rw [commV, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨w, ⟨x, hx, v, rfl⟩, rfl⟩
    obtain ⟨l, hl, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTL).1 hx
    set t' : ↥T := ⟨t, ht⟩ with ht'
    have hsplit : (l * t) v * v⁻¹ = (l (t v) * (t v)⁻¹) * (t v * v⁻¹) := by
      rw [MulAut.mul_apply]
      group
    have hb : (inl (t v * v⁻¹) : V ⋊[φ] ↥T) = ⁅(inr t' : V ⋊[φ] ↥T), inl v⁆ := by
      have h2 : (inl (t v) : V ⋊[φ] ↥T) = inr t' * inl v * (inr t')⁻¹ := by
        rw [← map_inv]
        exact inl_aut (φ := φ) t' v
      rw [commutatorElement_def, map_mul, map_inv, h2]
    have hfa : f (l (t v) * (t v)⁻¹) = 1 := hf1 _ (Subgroup.subset_closure ⟨l, hl, t v, rfl⟩)
    show f ((l * t) v * v⁻¹) ∈ ⁅Vb, (⊤ : Subgroup ((V ⋊[φ] ↥T) ⧸ N))⁆
    rw [hsplit, map_mul, hfa, one_mul]
    have hc : f (t v * v⁻¹) = ⁅(QuotientGroup.mk' N) (inr t'), f v⁆ := by
      show (QuotientGroup.mk' N) (inl (t v * v⁻¹)) = _
      rw [hb, map_commutatorElement]
      rfl
    rw [hc, Subgroup.commutator_comm Vb ⊤]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) ((show f v ∈ Vb from ⟨v, rfl⟩))
  have hVb0 : Vb = ⊥ := by
    by_contra hne
    have hlt := CFSG.Quasithin.H13.L1296.commutator_lt_self
      (T := (⊤ : Subgroup ((V ⋊[φ] ↥T) ⧸ N))) (V := Vb) hTop le_top
      (Subgroup.le_normalizer_of_normal (H := Vb)) hne
    exact lt_irrefl _ (lt_of_le_of_lt hle hlt)
  rw [eq_top_iff]
  intro v _
  have hv1 : f v = 1 := by
    have : f v ∈ Vb := (show f v ∈ Vb from ⟨v, rfl⟩)
    rw [hVb0, Subgroup.mem_bot] at this
    exact this
  have hmem : (inl v : V ⋊[φ] ↥T) ∈ N := (QuotientGroup.eq_one_iff _).1 hv1
  obtain ⟨u, hu, hui⟩ := Subgroup.mem_map.1 hmem
  have : u = v := SemidirectProduct.inl_injective hui
  rw [← this]
  exact hu

end TwoGroup

end LRed4

end CFSG.Quasithin
