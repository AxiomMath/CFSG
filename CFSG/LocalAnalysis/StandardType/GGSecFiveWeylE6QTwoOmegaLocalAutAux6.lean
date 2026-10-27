module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux5

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open SpCoord
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]

variable {Bs L : Subgroup G} {x : G}

@[expose] public def eBs (Bs L : Subgroup G) (e : ↥(Bs ⊓ L)) : ↥Bs := ⟨(e : G), e.2.1⟩

public theorem eBs_coe (Bs L : Subgroup G) (e : ↥(Bs ⊓ L)) :
    ((eBs Bs L e : ↥Bs) : G) = (e : G) := rfl

@[expose] public def eE (Bs L : Subgroup G) (b : ↥Bs) (hb : b ∈ EB Bs L) : ↥(Bs ⊓ L) :=
  ⟨(b : G), mem_EB.mp hb⟩

public theorem eE_eBs (Bs L : Subgroup G) (e : ↥(Bs ⊓ L)) : eE Bs L (eBs Bs L e) e.2 = e := rfl

public theorem eBs_eE (Bs L : Subgroup G) (b : ↥Bs) (hb : b ∈ EB Bs L) :
    eBs Bs L (eE Bs L b hb) = b := rfl

public theorem conjBs_conjE (l : ↥(NL L Bs)) (e : ↥(Bs ⊓ L)) :
    conjBs L Bs l (eBs Bs L e) = eBs Bs L (conjE L Bs l e) := by
  apply Subtype.ext
  rw [conjBs_coe, eBs_coe, eBs_coe, conjE_coe]

@[expose] public noncomputable def bstarEquiv
    (hcompl : Subgroup.IsComplement' (EB Bs L) ((Subgroup.zpowers x).subgroupOf Bs)) :
    ↥Bs ≃ ↥(EB Bs L) × ↥((Subgroup.zpowers x).subgroupOf Bs) :=
  (Subgroup.isComplement'_def.mp hcompl).equiv

public theorem bstarEquiv_fst_mul_snd
    (hcompl : Subgroup.IsComplement' (EB Bs L) ((Subgroup.zpowers x).subgroupOf Bs))
    (b : ↥Bs) :
    ((bstarEquiv hcompl b).1 : ↥Bs) * ((bstarEquiv hcompl b).2 : ↥Bs) = b :=
  (Subgroup.isComplement'_def.mp hcompl).equiv_fst_mul_equiv_snd b

public theorem bstarEquiv_eq_of_mul_eq
    (hcompl : Subgroup.IsComplement' (EB Bs L) ((Subgroup.zpowers x).subgroupOf Bs))
    {e : ↥(EB Bs L)} {y : ↥((Subgroup.zpowers x).subgroupOf Bs)} {b : ↥Bs}
    (h : (e : ↥Bs) * (y : ↥Bs) = b) :
    bstarEquiv hcompl b = (e, y) := by
  have hex := Subgroup.isComplement_iff_existsUnique.mp
    (Subgroup.isComplement'_def.mp hcompl) b
  have h1 : (e, y) = bstarEquiv hcompl b :=
    hex.unique h (bstarEquiv_fst_mul_snd hcompl b)
  exact h1.symm

public theorem conjBs_zpowers (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (l : ↥(NL L Bs)) (y : ↥((Subgroup.zpowers x).subgroupOf Bs)) :
    conjBs L Bs l y = y := by
  apply Subtype.ext
  show ((l : G) * ((y : ↥Bs) : G) * (l : G)⁻¹) = ((y : ↥Bs) : G)
  have hyx : ((y : ↥Bs) : G) ∈ Subgroup.zpowers x :=
    Subgroup.mem_subgroupOf.mp y.2
  have hxcent : x ∈ Subgroup.centralizer ({(l : G)} : Set G) := by
    have h0 : (l : G) * x = x * (l : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLx l.2.1)
    exact Subgroup.mem_centralizer_singleton_iff.mpr h0.symm
  have h1 : ((y : ↥Bs) : G) ∈ Subgroup.centralizer ({(l : G)} : Set G) :=
    (Subgroup.zpowers_le (H := Subgroup.centralizer ({(l : G)} : Set G))).mpr hxcent hyx
  have h2 : ((y : ↥Bs) : G) * (l : G) = (l : G) * ((y : ↥Bs) : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp h1
  rw [← h2]
  group

public theorem card_fix_conjBs
    (hcompl : Subgroup.IsComplement' (EB Bs L) ((Subgroup.zpowers x).subgroupOf Bs))
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (l : ↥(NL L Bs)) :
    Nat.card {b : ↥Bs // conjBs L Bs l b = b} =
      Nat.card {e : ↥(Bs ⊓ L) // conjE L Bs l e = e} *
        Nat.card ↥((Subgroup.zpowers x).subgroupOf Bs) := by
  classical
  have hfwd : ∀ b : ↥Bs, conjBs L Bs l b = b →
      conjE L Bs l (eE Bs L ((bstarEquiv hcompl b).1 : ↥Bs) (bstarEquiv hcompl b).1.2) =
        eE Bs L ((bstarEquiv hcompl b).1 : ↥Bs) (bstarEquiv hcompl b).1.2 := by
    intro b hfix
    set e₁ := (bstarEquiv hcompl b).1 with he₁
    set y₁ := (bstarEquiv hcompl b).2 with hy₁
    have hb : (e₁ : ↥Bs) * (y₁ : ↥Bs) = b := bstarEquiv_fst_mul_snd hcompl b
    have hy : conjBs L Bs l (y₁ : ↥Bs) = (y₁ : ↥Bs) := conjBs_zpowers hLx l y₁
    have h1 : (conjBs L Bs l (e₁ : ↥Bs)) * (y₁ : ↥Bs) = (e₁ : ↥Bs) * (y₁ : ↥Bs) := by
      calc (conjBs L Bs l (e₁ : ↥Bs)) * (y₁ : ↥Bs)
          = (conjBs L Bs l (e₁ : ↥Bs)) * (conjBs L Bs l (y₁ : ↥Bs)) := by rw [hy]
        _ = conjBs L Bs l ((e₁ : ↥Bs) * (y₁ : ↥Bs)) := (map_mul _ _ _).symm
        _ = conjBs L Bs l b := by rw [hb]
        _ = b := hfix
        _ = (e₁ : ↥Bs) * (y₁ : ↥Bs) := hb.symm
    have h2 : conjBs L Bs l (e₁ : ↥Bs) = (e₁ : ↥Bs) := by
      calc conjBs L Bs l (e₁ : ↥Bs)
          = ((conjBs L Bs l (e₁ : ↥Bs)) * (y₁ : ↥Bs)) * (y₁ : ↥Bs)⁻¹ := by group
        _ = ((e₁ : ↥Bs) * (y₁ : ↥Bs)) * (y₁ : ↥Bs)⁻¹ := by rw [h1]
        _ = (e₁ : ↥Bs) := by group
    have h3 : eBs Bs L (conjE L Bs l (eE Bs L (e₁ : ↥Bs) e₁.2)) =
        eBs Bs L (eE Bs L (e₁ : ↥Bs) e₁.2) := by
      rw [← conjBs_conjE, eBs_eE]
      exact h2
    exact Subtype.ext (congrArg (fun z : ↥Bs => (z : G)) h3)
  have heq : {b : ↥Bs // conjBs L Bs l b = b} ≃
      ({e : ↥(Bs ⊓ L) // conjE L Bs l e = e} ×
        ↥((Subgroup.zpowers x).subgroupOf Bs)) :=
    { toFun := fun b => ⟨⟨eE Bs L ((bstarEquiv hcompl b.1).1 : ↥Bs) (bstarEquiv hcompl b.1).1.2,
          hfwd b.1 b.2⟩, (bstarEquiv hcompl b.1).2⟩
      invFun := fun p => ⟨(eBs Bs L p.1.1 : ↥Bs) * (p.2 : ↥Bs), by
        show conjBs L Bs l ((eBs Bs L p.1.1 : ↥Bs) * (p.2 : ↥Bs)) =
          (eBs Bs L p.1.1 : ↥Bs) * (p.2 : ↥Bs)
        rw [map_mul, conjBs_conjE, p.1.2, conjBs_zpowers hLx l p.2]⟩
      left_inv := by
        intro b
        apply Subtype.ext
        show (eBs Bs L (eE Bs L ((bstarEquiv hcompl b.1).1 : ↥Bs) (bstarEquiv hcompl b.1).1.2) :
          ↥Bs) * ((bstarEquiv hcompl b.1).2 : ↥Bs) = b.1
        rw [eBs_eE, bstarEquiv_fst_mul_snd hcompl b.1]
      right_inv := by
        intro p
        obtain ⟨e, y⟩ := p
        apply Prod.ext
        · apply Subtype.ext
          show eE Bs L ((bstarEquiv hcompl ((eBs Bs L e.1 : ↥Bs) * (y : ↥Bs))).1 : ↥Bs)
            (bstarEquiv hcompl ((eBs Bs L e.1 : ↥Bs) * (y : ↥Bs))).1.2 = e.1
          rw [bstarEquiv_eq_of_mul_eq hcompl (e := ⟨eBs Bs L e.1, e.1.2⟩) (y := y) rfl, eE_eBs]
        · show (bstarEquiv hcompl ((eBs Bs L e.1 : ↥Bs) * (y : ↥Bs))).2 = y
          rw [bstarEquiv_eq_of_mul_eq hcompl (e := ⟨eBs Bs L e.1, e.1.2⟩) (y := y) rfl] }
  rw [Nat.card_congr heq, Nat.card_prod]

public theorem card_fixedPoints_congr {M N : Type} [Group M] [Group N] (e : M ≃* N)
    (φ : MulAut M) :
    Nat.card {y : N // (MulAut.congr e φ) y = y} = Nat.card {x : M // φ x = x} := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun y => ⟨e.symm y.1, ?_⟩
      invFun := fun x => ⟨e x.1, ?_⟩
      left_inv := fun y => by
        apply Subtype.ext
        exact MulEquiv.apply_symm_apply e y.1
      right_inv := fun x => by
        apply Subtype.ext
        exact MulEquiv.symm_apply_apply e x.1 }
  · have h : e (φ (e.symm y.1)) = y.1 := by
      simpa [MulAut.congr_apply, MulEquiv.trans_apply] using y.2
    exact e.injective (by rw [h, MulEquiv.apply_symm_apply])
  · show (MulAut.congr e φ) (e x.1) = e x.1
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, x.2]

public theorem conjBs_sq (l : ↥(NL L Bs)) (e : ↥(Bs ⊓ L)) :
    ((conjBs L Bs l) ^ 2) (eBs Bs L e) = eBs Bs L (((conjE L Bs l) ^ 2) e) := by
  rw [pow_two, pow_two, MulAut.mul_apply, MulAut.mul_apply, conjBs_conjE, conjBs_conjE]

public theorem isReflection_conjE
    (hcompl : Subgroup.IsComplement' (EB Bs L) ((Subgroup.zpowers x).subgroupOf Bs))
    (hxBs : x ∈ Bs) (hord : orderOf x = 3)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (l : ↥(NL L Bs))
    (h2 : (conjE L Bs l) ^ 2 = 1)
    (hc : Nat.card {e : ↥(Bs ⊓ L) // conjE L Bs l e = e} * 3 = Nat.card ↥(Bs ⊓ L)) :
    GGIsReflection 3 (conjBs L Bs l) := by
  have hX : Nat.card ↥((Subgroup.zpowers x).subgroupOf Bs) = 3 := by
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxBs)).toEquiv, Nat.card_zpowers,
      hord]
  have hcardfix := card_fix_conjBs hcompl hLx l
  refine ⟨?_, ?_⟩
  · refine MulEquiv.ext fun b => ?_
    set e₁ := (bstarEquiv hcompl b).1 with he₁
    set y₁ := (bstarEquiv hcompl b).2 with hy₁
    have hb : (e₁ : ↥Bs) * (y₁ : ↥Bs) = b := bstarEquiv_fst_mul_snd hcompl b
    have hy : conjBs L Bs l (y₁ : ↥Bs) = (y₁ : ↥Bs) := conjBs_zpowers hLx l y₁
    have he : ((conjE L Bs l) ^ 2) (eE Bs L (e₁ : ↥Bs) e₁.2) = eE Bs L (e₁ : ↥Bs) e₁.2 := by
      rw [h2]; rfl
    have hy2 : ((conjBs L Bs l) ^ 2) (y₁ : ↥Bs) = (y₁ : ↥Bs) := by
      rw [pow_two, MulAut.mul_apply, hy, hy]
    have he2 : ((conjBs L Bs l) ^ 2) (e₁ : ↥Bs) = (e₁ : ↥Bs) := by
      rw [← eBs_eE Bs L (e₁ : ↥Bs) e₁.2, conjBs_sq, he]
    calc ((conjBs L Bs l) ^ 2) b
        = ((conjBs L Bs l) ^ 2) ((e₁ : ↥Bs) * (y₁ : ↥Bs)) := by rw [hb]
      _ = ((conjBs L Bs l) ^ 2) (e₁ : ↥Bs) * ((conjBs L Bs l) ^ 2) (y₁ : ↥Bs) := map_mul _ _ _
      _ = (e₁ : ↥Bs) * (y₁ : ↥Bs) := by rw [he2, hy2]
      _ = b := hb
  · rw [hcardfix, hX, hcard]
    rw [hcardE] at hc
    rw [hc]
    norm_num

end CFSG.StandardType.E6QTwo

end
