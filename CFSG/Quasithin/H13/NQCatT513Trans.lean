module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.NQCat.T513

open scoped Pointwise commutatorElement

section Descend

variable (S : Type*) [Group S]

@[expose] noncomputable def zDescend : MulAut S →* MulAut (S ⧸ Subgroup.center S) where
  toFun σ := QuotientGroup.congr _ _ σ (Subgroup.map_center_eq σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem zDescend_mk (σ : MulAut S) (x : S) :
    zDescend S σ (QuotientGroup.mk x) = QuotientGroup.mk (σ x) := rfl

end Descend

variable {A : Type} [Group A]

section Conj

variable (Q : Subgroup A)

@[expose] noncomputable def qConj : ↥(Subgroup.normalizer (Q : Set A)) →* MulAut ↥Q :=
  (MulAut.congr (Q.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := Q)))).toMonoidHom.comp
    MulAut.conjNormal

variable {P : Type*} [Group P] (e : ↥Q ⧸ Subgroup.center ↥Q ≃* P)

@[expose] noncomputable def toP : ↥Q →* P := e.toMonoidHom.comp (QuotientGroup.mk' _)

@[expose] noncomputable def autOf : ↥(Subgroup.normalizer (Q : Set A)) →* MulAut P :=
  (MulAut.congr e).toMonoidHom.comp ((zDescend ↥Q).comp (qConj Q))

theorem autOf_toP (n : ↥(Subgroup.normalizer (Q : Set A))) (q : ↥Q) :
    autOf Q e n (toP Q e q) = toP Q e (qConj Q n q) := by
  simp [autOf, toP, MulAut.congr_apply, zDescend_mk]

theorem toP_surjective : Function.Surjective (toP Q e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem ker_toP : (toP Q e).ker = Subgroup.center ↥Q := by
  ext q
  simp [toP]

theorem autOf_of_mem {q : A} (hq : q ∈ Q) :
    autOf Q e ⟨q, Subgroup.le_normalizer hq⟩ = MulAut.conj (toP Q e ⟨q, hq⟩) := by
  ext y
  obtain ⟨x, rfl⟩ := toP_surjective Q e y
  rw [autOf_toP, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

@[expose] noncomputable def pImg (X : Subgroup A) : Subgroup P := (X.subgroupOf Q).map (toP Q e)

@[expose] noncomputable def aImg (X : Subgroup A) : Subgroup (MulAut P) :=
  (X.subgroupOf (Subgroup.normalizer (Q : Set A))).map (autOf Q e)

@[expose] noncomputable def iPart (X : Subgroup A) : Subgroup P :=
  (aImg Q e X).comap MulAut.conj

theorem mem_pImg {X : Subgroup A} {y : P} :
    y ∈ pImg Q e X ↔ ∃ (x : A) (hx : x ∈ Q), x ∈ X ∧ toP Q e ⟨x, hx⟩ = y := by
  constructor
  · rintro ⟨⟨x, hx⟩, hxX, rfl⟩
    exact ⟨x, hx, hxX, rfl⟩
  · rintro ⟨x, hx, hxX, rfl⟩
    exact ⟨⟨x, hx⟩, hxX, rfl⟩

theorem mem_aImg {X : Subgroup A} {α : MulAut P} :
    α ∈ aImg Q e X ↔ ∃ (x : A) (hx : x ∈ Subgroup.normalizer (Q : Set A)), x ∈ X ∧
      autOf Q e ⟨x, hx⟩ = α := by
  constructor
  · rintro ⟨⟨x, hx⟩, hxX, rfl⟩
    exact ⟨x, hx, hxX, rfl⟩
  · rintro ⟨x, hx, hxX, rfl⟩
    exact ⟨⟨x, hx⟩, hxX, rfl⟩

theorem autOf_mem_aImg {X : Subgroup A} {x : A} (hx : x ∈ Subgroup.normalizer (Q : Set A))
    (hxX : x ∈ X) : autOf Q e ⟨x, hx⟩ ∈ aImg Q e X :=
  (mem_aImg Q e).2 ⟨x, hx, hxX, rfl⟩

theorem toP_mem_pImg {X : Subgroup A} {x : A} (hx : x ∈ Q) (hxX : x ∈ X) :
    toP Q e ⟨x, hx⟩ ∈ pImg Q e X :=
  (mem_pImg Q e).2 ⟨x, hx, hxX, rfl⟩

theorem pImg_mono {X Y : Subgroup A} (h : X ≤ Y) : pImg Q e X ≤ pImg Q e Y := by
  intro y hy
  obtain ⟨x, hx, hxX, rfl⟩ := (mem_pImg Q e).1 hy
  exact toP_mem_pImg Q e hx (h hxX)

theorem conj_toP_mem_aImg {X : Subgroup A} {q : A} (hq : q ∈ Q) (hqX : q ∈ X) :
    MulAut.conj (toP Q e ⟨q, hq⟩) ∈ aImg Q e X := by
  rw [← autOf_of_mem]
  exact autOf_mem_aImg Q e _ hqX

theorem pImg_le_iPart {X : Subgroup A} : pImg Q e (X ⊓ Q) ≤ iPart Q e X := by
  intro y hy
  obtain ⟨x, hx, hxX, rfl⟩ := (mem_pImg Q e).1 hy
  exact conj_toP_mem_aImg Q e hx hxX.1

theorem card_aImg_dvd [Finite A] {X : Subgroup A} (hX : X ≤ Subgroup.normalizer (Q : Set A)) :
    Nat.card (aImg Q e X) ∣ Nat.card X := by
  have h1 : Nat.card (aImg Q e X) ∣ Nat.card (X.subgroupOf (Subgroup.normalizer (Q : Set A))) :=
    Subgroup.card_dvd_of_surjective ((autOf Q e).subgroupMap_surjective _)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv] at h1

theorem isCyclic_aImg {X : Subgroup A} (hX : X ≤ Subgroup.normalizer (Q : Set A))
    (hc : IsCyclic ↥X) : IsCyclic (aImg Q e X) := by
  have : IsCyclic ↥(X.subgroupOf (Subgroup.normalizer (Q : Set A))) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hX).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hX).symm.surjective
  exact isCyclic_of_surjective ((autOf Q e).subgroupMap _) ((autOf Q e).subgroupMap_surjective _)

theorem isPGroup_aImg {p : ℕ} {X : Subgroup A} (hX : X ≤ Subgroup.normalizer (Q : Set A))
    (hp : IsPGroup p ↥X) : IsPGroup p (aImg Q e X) :=
  (hp.of_equiv (Subgroup.subgroupOfEquivOfLe hX).symm).map _

theorem isPGroup_pImg {p : ℕ} {X : Subgroup A} (hXQ : X ≤ Q) (hp : IsPGroup p ↥X) :
    IsPGroup p (pImg Q e X) :=
  (hp.of_equiv (Subgroup.subgroupOfEquivOfLe hXQ).symm).map _

theorem inner_perm {S D : Subgroup A} (hSN : S ≤ Subgroup.normalizer (Q : Set A))
    (hDN : D ≤ Subgroup.normalizer (Q : Set A))
    (hDS : (D : Set A) * (S : Set A) = (S : Set A) * (D : Set A)) (hS2 : IsPGroup 2 ↥S)
    (hinn : ∀ α ∈ aImg Q e D, ∃ x, α = MulAut.conj x)
    (hcj : Function.Injective (MulAut.conj : P →* MulAut P))
    (hT : ∀ X : Subgroup P, IsPGroup 2 X → pImg Q e (S ⊓ Q) ≤ X → X = pImg Q e (S ⊓ Q)) :
    ∀ t ∈ pImg Q e (S ⊓ Q), ∀ x ∈ iPart Q e D,
      ∃ x' ∈ iPart Q e D, ∃ t' ∈ pImg Q e (S ⊓ Q), t * x = x' * t' := by
  intro t ht x hx
  obtain ⟨q, hqQ, hqS, rfl⟩ := (mem_pImg Q e).1 ht
  obtain ⟨d, hdN, hdD, hd⟩ := (mem_aImg Q e).1 (show MulAut.conj x ∈ aImg Q e D from hx)
  have hqd : q * d ∈ (S : Set A) * (D : Set A) := Set.mul_mem_mul hqS.1 hdD
  rw [← hDS] at hqd
  obtain ⟨d', hd'D, s', hs'S, hds⟩ := hqd
  obtain ⟨x', hx'⟩ := hinn _ (autOf_mem_aImg Q e (hDN hd'D) hd'D)
  have hx'D : x' ∈ iPart Q e D := by
    show MulAut.conj x' ∈ aImg Q e D
    rw [← hx']
    exact autOf_mem_aImg Q e _ hd'D
  have hmul : (⟨q, Subgroup.le_normalizer hqQ⟩ : ↥(Subgroup.normalizer (Q : Set A))) *
      ⟨d, hdN⟩ = ⟨d', hDN hd'D⟩ * ⟨s', hSN hs'S⟩ := Subtype.ext hds.symm
  have h1 := congrArg (autOf Q e) hmul
  rw [map_mul, map_mul, autOf_of_mem Q e hqQ, hd, hx'] at h1
  set t := toP Q e ⟨q, hqQ⟩ with ht
  have hs' : autOf Q e ⟨s', hSN hs'S⟩ = MulAut.conj (x'⁻¹ * t * x) := by
    rw [map_mul, map_mul, map_inv, mul_assoc, h1, inv_mul_cancel_left]
  have hS₁ : IsPGroup 2 (iPart Q e S) :=
    (isPGroup_aImg Q e hSN hS2).of_injective
      (((MulAut.conj : P →* MulAut P).comp (iPart Q e S).subtype).codRestrict (aImg Q e S)
        fun y => y.2)
      fun a b hab => Subtype.ext (hcj (congrArg Subtype.val hab))
  have hTS₁ : pImg Q e (S ⊓ Q) ≤ iPart Q e S := pImg_le_iPart Q e
  have hS₁T := hT _ hS₁ hTS₁
  have ht' : x'⁻¹ * t * x ∈ pImg Q e (S ⊓ Q) := by
    rw [← hS₁T]
    show MulAut.conj (x'⁻¹ * t * x) ∈ aImg Q e S
    rw [← hs']
    exact autOf_mem_aImg Q e _ hs'S
  exact ⟨x', hx'D, x'⁻¹ * t * x, ht', by group⟩

theorem le_normalizer_of_pImg [Finite A] {R D : Subgroup A} (hRQ : R ≤ Q) (hR : ⁅R, R⁆ = R)
    (hDN : D ≤ Subgroup.normalizer (Q : Set A))
    (h : ∀ (d : A) (hd : d ∈ D), ∀ y ∈ pImg Q e R, autOf Q e ⟨d, hDN hd⟩ y ∈ pImg Q e R) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  intro d hd
  have hdN := hDN hd
  have key : ∀ r ∈ R, ∃ r' ∈ R, ∃ z : A, z ∈ Q ∧ (∀ q ∈ Q, z * q = q * z) ∧
      d * r * d⁻¹ = r' * z := by
    intro r hr
    have h1 := h d hd _ (toP_mem_pImg Q e (hRQ hr) hr)
    rw [autOf_toP] at h1
    obtain ⟨r', hr'Q, hr'R, h2⟩ := (mem_pImg Q e).1 h1
    have h3 : (⟨r', hr'Q⟩ : ↥Q)⁻¹ * qConj Q ⟨d, hdN⟩ ⟨r, hRQ hr⟩ ∈ Subgroup.center ↥Q := by
      rw [← ker_toP Q e, MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
    refine ⟨r', hr'R, r'⁻¹ * (d * r * d⁻¹), ?_, fun q hq => ?_, by group⟩
    · exact Q.mul_mem (Q.inv_mem hr'Q) (qConj Q ⟨d, hdN⟩ ⟨r, hRQ hr⟩).2
    · have := Subgroup.mem_center_iff.1 h3 ⟨q, hq⟩
      exact (congrArg Subtype.val this).symm
  have hcomm : ∀ r₁ ∈ R, ∀ r₂ ∈ R, ⁅d * r₁ * d⁻¹, d * r₂ * d⁻¹⁆ ∈ R := by
    intro r₁ hr₁ r₂ hr₂
    obtain ⟨a, ha, z, hzQ, hz, h1⟩ := key r₁ hr₁
    obtain ⟨b, hb, w, hwQ, hw, h2⟩ := key r₂ hr₂
    rw [h1, h2]
    have hza : z * a = a * z := hz a (hRQ ha)
    have hzb : z * b = b * z := hz b (hRQ hb)
    have hwa : w * a = a * w := hw a (hRQ ha)
    have hwb : w * b = b * w := hw b (hRQ hb)
    have hzw : z * w = w * z := hz w hwQ
    have e1 : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
          = a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
        _ = a * b * (z * w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzb]; group
        _ = a * b * w * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzw]; group
        _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
        _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by
            rw [show w * a⁻¹ = a⁻¹ * w by
              rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hwa, mul_assoc, mul_inv_cancel, mul_one]]
        _ = a * b * a⁻¹ * b⁻¹ := by group
    rw [e1, ← hR]
    exact Subgroup.commutator_mem_commutator ha hb
  let W := R.map (MulAut.conj d).toMonoidHom
  have hWR : W ≤ R := by
    have hWW : ⁅W, W⁆ = W := by
      change ⁅R.map (MulAut.conj d).toMonoidHom, R.map (MulAut.conj d).toMonoidHom⁆ = _
      rw [← Subgroup.map_commutator, hR]
    rw [← hWW, Subgroup.commutator_le]
    rintro _ ⟨r₁, hr₁, rfl⟩ _ ⟨r₂, hr₂, rfl⟩
    exact hcomm r₁ hr₁ r₂ hr₂
  have hcard : Nat.card W = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj d).injective
  have hWeq : W = R := Subgroup.eq_of_le_of_card_ge hWR hcard.ge
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact hWR ⟨r, hr, rfl⟩
  · intro hr
    rw [← hWeq] at hr
    obtain ⟨r', hr', hr'e⟩ := hr
    have : r' = r := by
      simpa [MulAut.conj_apply] using hr'e
    rwa [← this]

end Conj

end CFSG.Quasithin.H13.NQCat.T513
