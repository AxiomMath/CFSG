module

public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearDvdModel
public import CFSG.LocalAnalysis.StandardType.GGSuDvdRootGenAsm
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  UCoord SpCoord

@[expose] noncomputable def ggKGTum_uvec {d p : ℕ} {K : Type} [Field K] (u : Kˣ) (hu : u ^ p = 1) :
    (Fin d → Multiplicative (ZMod p)) →* (Fin d → Kˣ) :=
  MonoidHom.compLeft (TableBSymp.zmodPowHom hu) (Fin d)

theorem ggKGTum_uvec_apply {d p : ℕ} {K : Type} [Field K] [NeZero p]
    (u : Kˣ) (hu : u ^ p = 1) (f : Fin d → Multiplicative (ZMod p)) (k : Fin d) :
    ggKGTum_uvec u hu f k = u ^ (Multiplicative.toAdd (f k)).val := by
  simp only [ggKGTum_uvec, MonoidHom.compLeft_apply, Function.comp_apply,
    TableBSymp.zmodPowHom_apply]

theorem ggKGTum_uvec_permAut {d p : ℕ} {K : Type} [Field K]
    (u : Kˣ) (hu : u ^ p = 1) (σ : Equiv.Perm (Fin d))
    (f : Fin d → Multiplicative (ZMod p)) :
    ggKGTum_uvec u hu (permAut σ f) = ggKGTum_uvec u hu f ∘ ⇑σ⁻¹ := rfl

theorem ggKGTum_uvec_injective_apply {d p : ℕ} {K : Type} [Field K] [NeZero p]
    {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p)
    {f g : Fin d → Multiplicative (ZMod p)} (k : Fin d)
    (h : ggKGTum_uvec u hu f k = ggKGTum_uvec u hu g k) : f k = g k := by
  rw [ggKGTum_uvec_apply, ggKGTum_uvec_apply] at h
  have h2 := (pow_inj_mod (x := u)).mp h
  rw [hord, Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h2
  exact Multiplicative.toAdd.injective (ZMod.val_injective p h2)

theorem ggKGTum_uvec_injective {d p : ℕ} {K : Type} [Field K] [NeZero p]
    {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p) :
    Function.Injective (ggKGTum_uvec (d := d) u hu) := by
  intro f g hfg
  funext k
  exact ggKGTum_uvec_injective_apply hu hord k (congrFun hfg k)

@[expose] def ggKGTum_Good {n d p : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    (φ : ↥(unitarySU 2 n K d) →* L') (A : Subgroup (MulAut L')) (u : Kˣ) (hu : u ^ p = 1)
    (f : Fin d → Multiplicative (ZMod p)) (a : MulAut L') : Prop :=
  a ∈ A ∧ ∃ t : Fin d → K, LineU.ActsDiagU φ a t ∧
    ∃ c : K, ∀ k, t k = c * (ggKGTum_uvec u hu f k : K)

theorem ggKGTum_eq_of_diag_const {n d : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hφs : Function.Surjective φ) {hd : 0 < d}
    {a b : MulAut L'} {t t' : Fin d → K}
    (ha : LineU.ActsDiagU φ a t) (hb : LineU.ActsDiagU φ b t')
    {c : K} (hc : ∀ k, t k = c * t' k) : a = b := by
  have hmul : LineU.ActsDiagU φ (a * b⁻¹) (fun k => t k * (t' k)⁻¹) :=
    LineU.ActsDiagU.mul ha (LineU.ActsDiagU.inv hb)
  have hconst : ∀ k l, (fun k => t k * (t' k)⁻¹) k = (fun k => t k * (t' k)⁻¹) l := by
    intro k l
    change t k * (t' k)⁻¹ = t l * (t' l)⁻¹
    rw [hc k, hc l, mul_assoc, mul_inv_cancel₀ (hb.ne_zero k), mul_one,
      mul_assoc, mul_inv_cancel₀ (hb.ne_zero l), mul_one]
  have h1 : a * b⁻¹ = 1 := LineU.ActsDiagU.eq_one_of_const hφs hmul ⟨0, hd⟩ hconst
  exact mul_inv_eq_one.mp h1

theorem ggKGTum_eq_of_Good {n d p : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hφs : Function.Surjective φ) {hd : 0 < d}
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1}
    {f : Fin d → Multiplicative (ZMod p)} {a b : MulAut L'}
    (ha : ggKGTum_Good φ A u hu f a) (hb : ggKGTum_Good φ A u hu f b) : a = b := by
  obtain ⟨-, t, ht, c, hc⟩ := ha
  obtain ⟨-, t', ht', c', hc'⟩ := hb
  have hc'0 : c' ≠ 0 := by
    intro h0
    have h1 := ht'.ne_zero ⟨0, hd⟩
    rw [hc' _, h0, zero_mul] at h1
    exact h1 rfl
  refine ggKGTum_eq_of_diag_const (hd := hd) hφs ht ht' (c := c * c'⁻¹) fun k => ?_
  have h2 : c'⁻¹ * (c' * ↑((ggKGTum_uvec u hu) f k)) = ↑((ggKGTum_uvec u hu) f k) := by
    rw [← mul_assoc, inv_mul_cancel₀ hc'0, one_mul]
  rw [hc k, hc' k, mul_assoc c, h2]

theorem ggKGTum_Good_mul {n d p : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1}
    {f g : Fin d → Multiplicative (ZMod p)} {a b : MulAut L'}
    (ha : ggKGTum_Good φ A u hu f a) (hb : ggKGTum_Good φ A u hu g b) :
    ggKGTum_Good φ A u hu (f * g) (a * b) := by
  obtain ⟨haA, t, ht, c, hc⟩ := ha
  obtain ⟨hbA, t', ht', c', hc'⟩ := hb
  refine ⟨A.mul_mem haA hbA, fun k => t k * t' k, ht.mul ht', c * c', fun k => ?_⟩
  change t k * t' k = c * c' * ↑((ggKGTum_uvec u hu) (f * g) k)
  rw [hc k, hc' k, map_mul, Pi.mul_apply, Units.val_mul]
  ring

theorem ggKGTum_Good_inv {n d p : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1}
    {f : Fin d → Multiplicative (ZMod p)} {a : MulAut L'}
    (ha : ggKGTum_Good φ A u hu f a) : ggKGTum_Good φ A u hu f⁻¹ a⁻¹ := by
  obtain ⟨haA, t, ht, c, hc⟩ := ha
  refine ⟨A.inv_mem haA, fun k => (t k)⁻¹, ht.inv, c⁻¹, fun k => ?_⟩
  have h1 : (ggKGTum_uvec u hu f⁻¹ k : K) = ((ggKGTum_uvec u hu f k : K))⁻¹ := by
    rw [map_inv]
    simp [Pi.inv_apply]
  change (t k)⁻¹ = c⁻¹ * ↑((ggKGTum_uvec u hu) f⁻¹ k)
  rw [hc k, h1, _root_.mul_inv_rev, mul_comm]

theorem ggKGTum_actsDiag_one_const {n d : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    {c : K} (hc : c ≠ 0) :
    LineU.ActsDiagU φ (1 : MulAut L') (fun _ : Fin d => c) := by
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc), ?_, ?_, fun s => ?_⟩
  · exact Subgroup.center_le_normalizer _ (TableB.scalar_mem_center (ι := Fin d) (Units.mk0 c hc))
  · ext i j
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases hij : i = j <;> simp [hij]
  · rw [MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [LineU.coe_conjN]
    have hcomm :=
      (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center (ι := Fin d) (Units.mk0 c hc))) s
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem ggKGTum_Good_one_of_const {n d p : ℕ} {K : Type} [Field K] [NeZero p]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1} {hd : 0 < d}
    {f : Fin d → Multiplicative (ZMod p)} (hf : ∀ i j, f i = f j) :
    ggKGTum_Good φ A u hu f 1 := by
  have hconst : ∀ k, (ggKGTum_uvec u hu f k : K) = (ggKGTum_uvec u hu f ⟨0, hd⟩ : K) := by
    intro k
    rw [ggKGTum_uvec_apply, ggKGTum_uvec_apply, hf k ⟨0, hd⟩]
  refine ⟨A.one_mem, fun _ => (ggKGTum_uvec u hu f ⟨0, hd⟩ : K),
    ggKGTum_actsDiag_one_const (Units.ne_zero _), 1, fun k => ?_⟩
  rw [hconst k, one_mul]

theorem ggKGTum_Good_one {n d p : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1} :
    ggKGTum_Good φ A u hu (1 : Fin d → Multiplicative (ZMod p)) 1 := by
  refine ⟨A.one_mem, fun _ => (1 : K), LineU.actsDiagU_one φ, 1, fun k => ?_⟩
  change (1 : K) = 1 * ↑((ggKGTum_uvec u hu) 1 k)
  rw [map_one]
  simp

@[expose] def ggKGTum_const (d p : ℕ) : Subgroup (Fin d → Multiplicative (ZMod p)) where
  carrier := {f | ∀ i j, f i = f j}
  mul_mem' := by
    intro f g hf hg i j
    simp only [Pi.mul_apply, hf i j, hg i j]
  one_mem' := fun i j => rfl
  inv_mem' := by
    intro f hf i j
    simp only [Pi.inv_apply, hf i j]

@[expose] def ggKGTum_S {n d p : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    (φ : ↥(unitarySU 2 n K d) →* L') (A : Subgroup (MulAut L')) (u : Kˣ) (hu : u ^ p = 1) :
    Subgroup (Fin d → Multiplicative (ZMod p)) where
  carrier := {f | ∃ a, ggKGTum_Good φ A u hu f a}
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, ggKGTum_Good_mul ha hb⟩
  one_mem' := ⟨1, ggKGTum_Good_one⟩
  inv_mem' := by
    rintro f ⟨a, ha⟩
    exact ⟨a⁻¹, ggKGTum_Good_inv ha⟩

@[expose] noncomputable def ggKGTum_Θ {n d p : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hφs : Function.Surjective φ)
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1} (hd : 0 < d) :
    ↥(ggKGTum_S φ A u hu) →* ↥A where
  toFun f := ⟨Classical.choose f.2, (Classical.choose_spec f.2).1⟩
  map_one' := by
    apply Subtype.ext
    exact ggKGTum_eq_of_Good (hd := hd) hφs
      (Classical.choose_spec (1 : ↥(ggKGTum_S φ A u hu)).2) ggKGTum_Good_one
  map_mul' := by
    intro f g
    apply Subtype.ext
    exact ggKGTum_eq_of_Good (hd := hd) hφs (Classical.choose_spec (f * g).2)
      (ggKGTum_Good_mul (Classical.choose_spec f.2) (Classical.choose_spec g.2))

theorem ggKGTum_Θ_apply {n d p : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} {hφs : Function.Surjective φ}
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1} {hd : 0 < d}
    (f : ↥(ggKGTum_S φ A u hu)) :
    ((ggKGTum_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd f : ↥A) : MulAut L') =
      Classical.choose f.2 := rfl

theorem ggKGTum_Θ_surjective {n d p : ℕ} {K : Type} [Field K] [NeZero p]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hK : UnitaryFieldData 2 n K) (hd3 : 3 ≤ d)
    (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L')}
    (hAp : ∀ a ∈ A, a ^ p = 1) (hdiag : ∀ a ∈ A, ∃ t, LineU.ActsDiagU φ a t)
    {u : Kˣ} {hu : u ^ p = 1} (hζ : IsPrimitiveRoot (u : K) p) (hd : 0 < d) :
    Function.Surjective (ggKGTum_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd) := by
  intro a
  obtain ⟨t, ht⟩ := hdiag a a.2
  have hratio : ∀ k, (t k * (t ⟨0, hd⟩)⁻¹) ^ p = 1 := fun k =>
    LineU.ActsDiagU.ratio_pow hK hd3 hφker ht (hAp a a.2) k ⟨0, hd⟩
  choose n hn_lt hn using fun k => hζ.eq_pow_of_pow_eq_one (hratio k)
  let f : Fin d → Multiplicative (ZMod p) := fun k => Multiplicative.ofAdd (n k : ZMod p)
  have hf : ∀ k, (ggKGTum_uvec u hu f k : K) = t k * (t ⟨0, hd⟩)⁻¹ := by
    intro k
    rw [ggKGTum_uvec_apply]
    change (u ^ (n k : ZMod p).val : K) = t k * (t ⟨0, hd⟩)⁻¹
    have h1 : (n k : ZMod p).val = n k := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hn_lt k)]
    rw [h1]
    exact hn k
  have hgood : ggKGTum_Good φ A u hu f a := by
    refine ⟨a.2, t, ht, t ⟨0, hd⟩, fun k => ?_⟩
    rw [hf k]
    field_simp [ht.ne_zero ⟨0, hd⟩]
  refine ⟨⟨f, ⟨a, hgood⟩⟩, ?_⟩
  apply Subtype.ext
  have hspec : ggKGTum_Good φ A u hu f
      (Classical.choose (⟨a, hgood⟩ : ∃ b, ggKGTum_Good φ A u hu f b)) :=
    Classical.choose_spec _
  exact ggKGTum_eq_of_Good (hd := hd) hφs hspec hgood

theorem ggKGTum_Θ_eq_one_iff {n d p : ℕ} {K : Type} [Field K] [NeZero p]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hK : UnitaryFieldData 2 n K) (hd3 : 3 ≤ d)
    (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1}
    (hord : orderOf u = p) (hd : 0 < d)
    (f : ↥(ggKGTum_S φ A u hu)) :
    ggKGTum_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd f = 1 ↔
      ∃ c : Multiplicative (ZMod p), (f : Fin d → Multiplicative (ZMod p)) = fun _ => c := by
  constructor
  · intro h1
    obtain ⟨-, t, ht, c, hc⟩ := Classical.choose_spec f.2
    have h1' : (Classical.choose f.2 : MulAut L') = 1 := by
      have := congrArg (fun x : ↥A => (x : MulAut L')) h1
      simpa [ggKGTum_Θ_apply] using this
    have ht1 : LineU.ActsDiagU φ (1 : MulAut L') t := h1' ▸ ht
    have hfun : ggKGTum_uvec u hu (f : Fin d → Multiplicative (ZMod p)) =
        ggKGTum_uvec u hu (fun _ => (f : Fin d → Multiplicative (ZMod p)) ⟨0, hd⟩) := by
      funext k
      by_cases hk : k = ⟨0, hd⟩
      · subst hk
        rfl
      · have hratio := LineU.ActsDiagU.ratio_eq hK hd3 hφker ht1
          (LineU.actsDiagU_one φ) k ⟨0, hd⟩
        simp only [inv_one, mul_one] at hratio
        have htk : t k = t ⟨0, hd⟩ := (mul_inv_eq_one₀ (ht.ne_zero ⟨0, hd⟩)).mp hratio
        have hc0 : c ≠ 0 := by
          intro h0
          have h2 := ht.ne_zero k
          rw [hc k, h0, zero_mul] at h2
          exact h2 rfl
        have huv : ggKGTum_uvec u hu (f : Fin d → Multiplicative (ZMod p)) k =
            ggKGTum_uvec u hu (f : Fin d → Multiplicative (ZMod p)) ⟨0, hd⟩ := by
          apply Units.ext
          exact mul_left_cancel₀ hc0 (by rw [← hc k, ← hc ⟨0, hd⟩, htk])
        have hconst : ggKGTum_uvec u hu (fun _ => (f : Fin d → Multiplicative (ZMod p)) ⟨0, hd⟩) k =
            ggKGTum_uvec u hu (f : Fin d → Multiplicative (ZMod p)) ⟨0, hd⟩ := rfl
        rw [hconst]
        exact huv
    refine ⟨(f : Fin d → Multiplicative (ZMod p)) ⟨0, hd⟩, ?_⟩
    exact ggKGTum_uvec_injective hu hord hfun
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    rw [ggKGTum_Θ_apply]
    exact ggKGTum_eq_of_Good (hd := hd) hφs (Classical.choose_spec f.2)
      (ggKGTum_Good_one_of_const (hd := hd) (fun i j => by rw [hc]))

theorem ggKGTum_card_M {d p : ℕ} :
    Nat.card (Fin d → Multiplicative (ZMod p)) = p ^ d := by
  rw [Nat.card_fun, Nat.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem ggKGTum_card_const {d p : ℕ} (hd : 0 < d) :
    Nat.card ↥(ggKGTum_const d p) = p := by
  have hbij : Function.Bijective
      (fun f : ↥(ggKGTum_const d p) => (f : Fin d → Multiplicative (ZMod p)) ⟨0, hd⟩) := by
    constructor
    · intro f g h
      apply Subtype.ext
      funext k
      rw [show (f : Fin d → Multiplicative (ZMod p)) k = f.1 ⟨0, hd⟩ from f.2 k ⟨0, hd⟩,
        show (g : Fin d → Multiplicative (ZMod p)) k = g.1 ⟨0, hd⟩ from g.2 k ⟨0, hd⟩]
      exact h
    · intro c
      exact ⟨⟨fun _ => c, fun _ _ => rfl⟩, rfl⟩
  calc Nat.card ↥(ggKGTum_const d p) = Nat.card (Multiplicative (ZMod p)) :=
        Nat.card_congr (Equiv.ofBijective _ hbij)
    _ = Nat.card (ZMod p) := Nat.card_congr Multiplicative.toAdd
    _ = p := Nat.card_zmod p

theorem ggKGTum_Good_permSU {n d p : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'}
    (hK : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n + 1) (hd3 : 3 ≤ d)
    (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t, LineU.ActsDiagU φ a t)
    {u : Kˣ} {hu : u ^ p = 1} {σ : Equiv.Perm (Fin d)}
    {f : Fin d → Multiplicative (ZMod p)} {a : MulAut L'}
    (ha : ggKGTum_Good φ A u hu f a) :
    ggKGTum_Good φ A u hu (permAut σ f)
      (MulAut.conj (φ (LineU.permSU hK σ)) * a *
        (MulAut.conj (φ (LineU.permSU hK σ)))⁻¹) := by
  obtain ⟨haA, t, ht, c, hc⟩ := ha
  have hN : MulAut.conj (φ (LineU.permSU hK σ)) ∈
      Subgroup.normalizer (A : Set (MulAut L')) :=
    SuDvdRootGen.conj_permSU_mem_normalizer hK hpq hd3 hφs hφker hdiag hAp hsc σ
  have hconjA : MulAut.conj (φ (LineU.permSU hK σ)) * a *
      (MulAut.conj (φ (LineU.permSU hK σ)))⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hN a).mp haA
  have hcd : LineU.ActsDiagU φ
      (MulAut.conj (φ (LineU.permSU hK σ)) * a *
        (MulAut.conj (φ (LineU.permSU hK σ)))⁻¹) (t ∘ ⇑σ.symm) :=
    LineU.ActsDiagU.conj_perm hK ht σ
  refine ⟨hconjA, t ∘ ⇑σ.symm, hcd, c, fun k => ?_⟩
  change t (σ.symm k) = c * ↑((ggKGTum_uvec u hu) (permAut σ f) k)
  rw [hc (σ.symm k), ggKGTum_uvec_permAut]
  rfl

theorem ggKGTum_permAut_mem_S {n d p : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'}
    (hK : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n + 1) (hd3 : 3 ≤ d)
    (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t, LineU.ActsDiagU φ a t)
    {u : Kˣ} {hu : u ^ p = 1} (σ : Equiv.Perm (Fin d)) {f : Fin d → Multiplicative (ZMod p)}
    (hf : f ∈ ggKGTum_S φ A u hu) : permAut σ f ∈ ggKGTum_S φ A u hu := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨_, ggKGTum_Good_permSU hK hpq hd3 hφs hφker hAp hsc hdiag ha⟩

theorem ggKGTum_card_sumZero {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p) (hd : 1 ≤ d) :
    Nat.card ↥(sumZero d p) = p ^ (d - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  obtain ⟨ζ, hζroot⟩ := hζ
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let u : Kˣ := Units.mk0 ζ (hζroot.ne_zero hp.ne_zero)
  have hu : u ^ p = 1 := by
    ext
    simp only [u, Units.val_pow_eq_pow_val, Units.val_one, Units.mk0_val]
    exact hζroot.pow_eq_one
  have hζu : IsPrimitiveRoot u p := IsPrimitiveRoot.coe_units_iff.mp hζroot
  have hord : orderOf u = p := hζu.eq_orderOf.symm
  have hmem : ∀ f : ↥(sumZero (m + 1) p),
      UModel.uvec hu f ∈ RankThree.PartOne.KFU.torusVec p (m + 1) K := fun f =>
    ⟨fun k => UModel.uvec_pow_eq_one hu f k, UModel.prod_uvec hu hord f⟩
  let F : ↥(sumZero (m + 1) p) → RankThree.PartOne.KFU.torusVec p (m + 1) K :=
    fun f => ⟨UModel.uvec hu f, hmem f⟩
  have hbij : Function.Bijective F := by
    constructor
    · intro f g h
      exact UModel.uvec_injective hu hord (Subtype.ext_iff.mp h)
    · intro t
      obtain ⟨f, hf⟩ := UModel.exists_uvec_eq hu hord t.2.1 t.2.2
      exact ⟨f, Subtype.ext hf⟩
  calc Nat.card ↥(sumZero (m + 1) p) =
        Nat.card ↥(RankThree.PartOne.KFU.torusVec p (m + 1) K) :=
        Nat.card_congr (Equiv.ofBijective F hbij)
    _ = p ^ m := RankThree.PartOne.KFU.card_torusVec_eq hp.pos ⟨u, hζu⟩ m

theorem ggKGTum_card_sumZero_eq_torusVec {d p : ℕ} {K : Type} [Field K] [NeZero p]
    {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p) :
    Nat.card ↥(sumZero d p) = Nat.card ↥(RankThree.PartOne.KFU.torusVec p d K) := by
  have hmem : ∀ f : ↥(sumZero d p),
      UModel.uvec hu f ∈ RankThree.PartOne.KFU.torusVec p d K := fun f =>
    ⟨fun k => UModel.uvec_pow_eq_one hu f k, UModel.prod_uvec hu hord f⟩
  let F : ↥(sumZero d p) → RankThree.PartOne.KFU.torusVec p d K :=
    fun f => ⟨UModel.uvec hu f, hmem f⟩
  have hbij : Function.Bijective F := by
    constructor
    · intro f g h
      exact UModel.uvec_injective hu hord (Subtype.ext_iff.mp h)
    · intro t
      obtain ⟨f, hf⟩ := UModel.exists_uvec_eq hu hord t.2.1 t.2.2
      exact ⟨f, Subtype.ext hf⟩
  exact Nat.card_congr (Equiv.ofBijective F hbij)

theorem ggKGTum_S_eq_top_or_sumZero {n d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hd : 5 ≤ d) {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} {A : Subgroup (MulAut L')}
    {u : Kˣ} {hu : u ^ p = 1} (hord : orderOf u = p)
    (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (hperm : ∀ (σ : Equiv.Perm (Fin d)) {f : Fin d → Multiplicative (ZMod p)},
      f ∈ ggKGTum_S φ A u hu → permAut σ f ∈ ggKGTum_S φ A u hu)
    (hSge : p ^ (d - 1) ≤ Nat.card ↥(ggKGTum_S φ A u hu)) :
    ggKGTum_S φ A u hu = ⊤ ∨ ggKGTum_S φ A u hu = sumZero d p := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hd0 : 0 < d := by omega
  let S := ggKGTum_S φ A u hu
  by_cases htop : S = ⊤
  · exact Or.inl htop
  right
  have hindex_gt : 1 < S.index := by
    have hne : S.index ≠ 1 := by
      intro h1
      exact htop ((Subgroup.index_eq_one).mp h1)
    have hpos : 0 < S.index := by
      by_contra h0
      have hzero : S.index = 0 := Nat.eq_zero_of_not_pos h0
      have h := Subgroup.card_mul_index S
      rw [hzero, mul_zero, ggKGTum_card_M] at h
      exact (pow_pos hp.pos d).ne' h.symm
    omega
  have hSdvd : S.index ∣ p ^ d := by
    have h := Subgroup.card_mul_index S
    rw [ggKGTum_card_M] at h
    exact ⟨Nat.card ↥S, by rw [mul_comm]; exact h.symm⟩
  have hindex_le : S.index ≤ p := by
    have h := Subgroup.card_mul_index S
    rw [ggKGTum_card_M] at h
    have h1 : p ^ (d - 1) * S.index ≤ p ^ (d - 1) * p := by
      calc p ^ (d - 1) * S.index ≤ Nat.card ↥S * S.index := Nat.mul_le_mul_right _ hSge
        _ = p ^ d := h
        _ = p ^ (d - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos hp.pos _)
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow hp).mp hSdvd
  have hk1 : k = 1 := by
    have hkpos : 0 < k := by
      by_contra hk0
      rw [Nat.eq_zero_of_not_pos hk0, pow_zero] at hk
      omega
    have hkle : k ≤ 1 := by
      have h1 : p ^ k ≤ p ^ 1 := by rw [pow_one]; exact hk ▸ hindex_le
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    omega
  have hindex_eq : S.index = p := by rw [hk, hk1, pow_one]
  have hScard : Nat.card ↥S = p ^ (d - 1) := by
    have h := Subgroup.card_mul_index S
    rw [hindex_eq, ggKGTum_card_M] at h
    have h1 : Nat.card ↥S * p = p ^ (d - 1) * p := by
      rw [h, show p ^ d = p ^ (d - 1) * p by rw [← pow_succ, Nat.sub_add_cancel (by omega)]]
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1
  have hVcard : Nat.card ↥(sumZero d p) = p ^ (d - 1) := ggKGTum_card_sumZero hp hζ (by omega)
  have hVTV : Nat.card ↥(sumZero d p) = Nat.card ↥(RankThree.PartOne.KFU.torusVec p d K) :=
    ggKGTum_card_sumZero_eq_torusVec hu hord
  have hVindex : (sumZero d p).index = p := by
    have h := Subgroup.card_mul_index (sumZero d p)
    rw [hVcard, ggKGTum_card_M] at h
    have h1 : p ^ (d - 1) * (sumZero d p).index = p ^ (d - 1) * p := by
      rw [h, show p ^ d = p ^ (d - 1) * p by rw [← pow_succ, Nat.sub_add_cancel (by omega)]]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h1
  have hrel_le : S.relIndex (sumZero d p) ≤ p := by
    have h := Subgroup.relIndex_mul_index (H := S) (K := S ⊔ sumZero d p) le_sup_left
    rw [Subgroup.relIndex_sup_left (sumZero d p) S] at h
    rw [hindex_eq] at h
    have hpos : 0 < (S ⊔ sumZero d p).index := by
      by_contra h0
      have hzero : (S ⊔ sumZero d p).index = 0 := Nat.eq_zero_of_not_pos h0
      rw [hzero, mul_zero] at h
      exact hp.ne_zero h.symm
    have h1 : S.relIndex (sumZero d p) ≤ S.relIndex (sumZero d p) * (S ⊔ sumZero d p).index :=
      Nat.le_mul_of_pos_right _ hpos
    omega
  have hcard_inf : Nat.card ↥(S ⊓ sumZero d p) * S.relIndex (sumZero d p) = p ^ (d - 1) := by
    have h := Subgroup.card_mul_index (S ⊓ sumZero d p)
    rw [Subgroup.index_inf, hVindex, ggKGTum_card_M] at h
    have h1 : Nat.card ↥(S ⊓ sumZero d p) * S.relIndex (sumZero d p) * p =
        p ^ (d - 1) * p := by
      rw [show p ^ (d - 1) * p = p ^ d by rw [← pow_succ, Nat.sub_add_cancel (by omega)], ← h]
      ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1
  have hWge : p ^ (d - 2) ≤ Nat.card ↥(S ⊓ sumZero d p) := by
    have hp1 : p ^ (d - 2) * p = p ^ (d - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    have h1 : p ^ (d - 2) * p ≤ Nat.card ↥(S ⊓ sumZero d p) * p := by
      calc p ^ (d - 2) * p = p ^ (d - 1) := hp1
        _ = Nat.card ↥(S ⊓ sumZero d p) * S.relIndex (sumZero d p) := hcard_inf.symm
        _ ≤ Nat.card ↥(S ⊓ sumZero d p) * p := Nat.mul_le_mul_left _ hrel_le
    exact Nat.le_of_mul_le_mul_right h1 hp.pos
  let V := sumZero d p
  let W : Subgroup (Fin d → Multiplicative (ZMod p)) := S ⊓ V
  let incl : ↥W →* ↥V := Subgroup.inclusion inf_le_right
  let ψ₀ : ↥V →* RankThree.PartOne.KFU.torusVec p d K :=
    (UModel.uvec hu).codRestrict _ (fun f =>
      show (∀ k, UModel.uvec hu f k ^ p = 1) ∧ ∏ k, UModel.uvec hu f k = 1 from
        ⟨fun k => UModel.uvec_pow_eq_one hu f k, UModel.prod_uvec hu hord f⟩)
  let ψ : ↥W →* RankThree.PartOne.KFU.torusVec p d K := ψ₀.comp incl
  let B : Subgroup (RankThree.PartOne.KFU.torusVec p d K) := ψ.range
  have hψinj : Function.Injective ψ := by
    intro x y h
    have h1 : UModel.uvec hu (incl x) = UModel.uvec hu (incl y) :=
      congrArg (fun z : ↥(RankThree.PartOne.KFU.torusVec p d K) => (z : Fin d → Kˣ)) h
    have h2 : incl x = incl y := UModel.uvec_injective hu hord h1
    exact Subtype.ext (congrArg (fun z : ↥V => (z : Fin d → Multiplicative (ZMod p))) h2)
  have hψval : ∀ x : ↥W, (ψ x : Fin d → Kˣ) = UModel.uvec hu (incl x) := fun _ => rfl
  have hB : ∀ σ : Equiv.Perm (Fin d), ∀ b ∈ B, RankThree.PartOne.KFU.symAct p K σ b ∈ B := by
    rintro σ b ⟨w, rfl⟩
    refine ⟨⟨permAut σ w.1, hperm σ w.2.1, permAut_mem_sumZero σ w.2.2⟩, ?_⟩
    apply Subtype.ext
    change UModel.uvec hu (incl ⟨permAut σ w.1, hperm σ w.2.1, permAut_mem_sumZero σ w.2.2⟩) =
      ((RankThree.PartOne.KFU.symAct p K σ (ψ w) :
        ↥(RankThree.PartOne.KFU.torusVec p d K)) : Fin d → Kˣ)
    rw [show ((RankThree.PartOne.KFU.symAct p K σ (ψ w) :
          ↥(RankThree.PartOne.KFU.torusVec p d K)) : Fin d → Kˣ) =
        (ψ w : Fin d → Kˣ) ∘ ⇑σ.symm from
        funext fun i => RankThree.PartOne.KFU.coe_symAct σ (ψ w) i, hψval]
    show UModel.uvec hu (incl ⟨permAut σ w.1, hperm σ w.2.1, permAut_mem_sumZero σ w.2.2⟩) =
      UModel.uvec hu (incl w) ∘ ⇑σ.symm
    rw [show incl ⟨permAut σ w.1, hperm σ w.2.1, permAut_mem_sumZero σ w.2.2⟩ =
        permAutV σ (incl w) from Subtype.ext rfl, UModel.uvec_permAutV]
  rcases RankThree.PartOne.KFU.le_scalarSub_or_eq_top hp B hB with hle | htopB
  ·
    exfalso
    have hWle : W ≤ ggKGTum_const d p := by
      intro f hf
      have hle' : ψ ⟨f, hf⟩ ∈ RankThree.PartOne.KFU.scalarSub p d K := hle ⟨⟨f, hf⟩, rfl⟩
      intro i j
      have h1 : ggKGTum_uvec u hu f i = ggKGTum_uvec u hu f j := by
        have h2 := hle' i j
        have h3 : (ψ ⟨f, hf⟩ : Fin d → Kˣ) = ggKGTum_uvec u hu f := by
          rw [hψval]
          rfl
        rwa [h3] at h2
      have h2 : ggKGTum_uvec u hu f i = ggKGTum_uvec u hu (fun _ => f j) i := by
        show ggKGTum_uvec u hu f i = ggKGTum_uvec u hu f j
        exact h1
      exact ggKGTum_uvec_injective_apply hu hord i h2
    have hWle_card : Nat.card ↥W ≤ p := by
      have hinj : Function.Injective
          (fun f : ↥W => (⟨f.1, hWle f.2⟩ : ↥(ggKGTum_const d p))) := by
        intro f g h
        have h1 : f.1 = g.1 :=
          congrArg (fun z : ↥(ggKGTum_const d p) => (z : Fin d → Multiplicative (ZMod p))) h
        exact Subtype.ext h1
      calc Nat.card ↥W ≤ Nat.card ↥(ggKGTum_const d p) :=
            Nat.card_le_card_of_injective _ hinj
        _ = p := ggKGTum_card_const hd0
    have hp_gt : p < p ^ (d - 2) := by
      have h1 : p ^ 1 < p ^ 3 := (Nat.pow_lt_pow_iff_right hp.one_lt).mpr (by norm_num)
      have h2 : p ^ 3 ≤ p ^ (d - 2) := (Nat.pow_le_pow_iff_right hp.one_lt).mpr (by omega)
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := h1
        _ ≤ p ^ (d - 2) := h2
    exact not_lt_of_ge (le_trans hWge hWle_card) hp_gt
  ·
    have hWcard : Nat.card ↥W = Nat.card ↥(sumZero d p) := by
      have h1 : Nat.card ↥B = Nat.card ↥W := by
        rw [show B = Subgroup.map ψ ⊤ from MonoidHom.range_eq_map ψ]
        exact (Subgroup.card_map_of_injective hψinj (K := ⊤)).trans
          (Nat.card_congr Subgroup.topEquiv.toEquiv)
      rw [← h1, htopB]
      exact (Nat.card_congr Subgroup.topEquiv.toEquiv).trans hVTV.symm
    have hWV : W = V := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hWcard])
    have hVS : V ≤ S := by
      intro f hf
      have h1 : f ∈ W := by rw [hWV]; exact hf
      exact h1.1
    exact (Subgroup.eq_of_le_of_card_ge hVS (by rw [hScard, hVcard])).symm

theorem exists_diagonal_of_actsDiagU_conj {n d p : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hK : UnitaryFieldData 2 n K) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {g : ↥(unitarySU 2 n K d)} {w : Fin d → K}
    (h : LineU.ActsDiagU φ (MulAut.conj (φ g)) w) :
    ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun k => c * w k) := by
  classical
  haveI : Finite K := hK.finite
  obtain ⟨E, hE, hEw, hEact⟩ := h
  set M : GL (Fin d) K := (g : GL (Fin d) K) * E⁻¹ with hM
  have hEinv : E⁻¹ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.inv_mem _ hE
  have hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := by
    rw [hM]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer g.2) hEinv
  let τ : ↥(unitarySU 2 n K d) →* ↥(unitarySU 2 n K d) :=
    { toFun := fun u => ⟨M * (u : GL (Fin d) K) * M⁻¹,
        (Subgroup.mem_normalizer_iff.mp hMN (u : GL (Fin d) K)).mp u.2⟩
      map_one' := by
        apply Subtype.ext
        change M * (1 : GL (Fin d) K) * M⁻¹ = (1 : GL (Fin d) K)
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hphiφ : ∀ u : ↥(unitarySU 2 n K d), φ (τ u) = φ u := by
    intro u
    have hy := hEact (LineU.conjN E⁻¹ hEinv u)
    have hcy : LineU.conjN E hE (LineU.conjN E⁻¹ hEinv u) = u :=
      Subtype.ext (by rw [LineU.coe_conjN, LineU.coe_conjN]; group)
    rw [hcy] at hy
    have hgy : φ (g * LineU.conjN E⁻¹ hEinv u * g⁻¹) = φ u := by
      rw [← hy, MulAut.conj_apply, map_mul, map_mul, map_inv]
    have heq : τ u = g * LineU.conjN E⁻¹ hEinv u * g⁻¹ := by
      apply Subtype.ext
      change (M : GL (Fin d) K) * (u : GL (Fin d) K) * M⁻¹ =
        g * (LineU.conjN E⁻¹ hEinv u) * g⁻¹
      rw [LineU.coe_conjN, hM]
      rw [Subgroup.coe_inv]
      group
    rw [heq]
    exact hgy
  have hΦ : ∀ u : ↥(unitarySU 2 n K d),
      LargeEvenProjMk (unitarySU 2 n K d) (τ u) =
        LargeEvenProjMk (unitarySU 2 n K d) u := by
    intro u
    have hmem : τ u * u⁻¹ ∈
        (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) := by
      rw [Subgroup.mem_subgroupOf]
      obtain ⟨c, hc⟩ := hφker (τ u * u⁻¹) (by
        rw [map_mul, map_inv, hphiφ u, mul_inv_cancel])
      refine TableBUE.mem_scalars_of_eq_scalar (c := c) ?_
      rw [hc]
      exact (Matrix.scalar_apply c).symm
    have h1 : LargeEvenProjMk (unitarySU 2 n K d) (τ u * u⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff (τ u * u⁻¹)).mpr hmem
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := hK.charP
  have hperf : Group.IsPerfect ↥(unitarySU 2 n K d) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := n) hK.card_eq_sq
      (n := d) (by omega) (by intro hcon; have h1 := congrArg Prod.fst hcon; omega)
  have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq
    (LargeEvenProjMk (unitarySU 2 n K d)) TableBUE.ker_projMk_le_center hperf
    τ (MonoidHom.id _) hΦ
  have hcomm : ∀ u ∈ unitarySU 2 n K d, M * u = u * M := by
    intro u hu
    have h2 := congrArg Subtype.val (key ⟨u, hu⟩)
    change M * u * M⁻¹ = u at h2
    calc M * u = M * u * M⁻¹ * M := by group
      _ = u * M := by rw [h2]
  obtain ⟨c, hc⟩ := (show M ∈ LargeEvenScalars (Fin d) K from
    TableBUE.mem_scalars_of_commute hK hp hpq hcomm)
  refine ⟨(c : K), ?_⟩
  have hgE : (g : GL (Fin d) K) = M * E := by rw [hM]; group
  rw [hgE, Units.val_mul, ← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    hEw, diagonal_mul_diagonal]

theorem ActsDiagU.conj_of_mul_diagonal {n d : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'} {a : MulAut L'}
    {t t' : Fin d → K} (ha : LineU.ActsDiagU φ a t) {s : ↥(unitarySU 2 n K d)}
    (hs : (((s : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) * diagonal t =
      diagonal t' * (((s : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K)) :
    LineU.ActsDiagU φ (MulAut.conj (φ s) * a * (MulAut.conj (φ s))⁻¹) t' := by
  obtain ⟨D, hD, hDt, haD⟩ := ha
  have hsN : (s : GL (Fin d) K) ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.le_normalizer s.2
  have hD' : (s : GL (Fin d) K) * D * (s : GL (Fin d) K)⁻¹ ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hsN hD) (Subgroup.inv_mem _ hsN)
  refine ⟨(s : GL (Fin d) K) * D * (s : GL (Fin d) K)⁻¹, hD', ?_, fun y => ?_⟩
  · rw [Units.val_mul, Units.val_mul, hDt]
    rw [hs, Matrix.mul_assoc,
      show (((s : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) *
            (↑(((s : GL (Fin d) K))⁻¹) : Matrix (Fin d) (Fin d) K) = 1 by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one],
      Matrix.mul_one]
  · have e : LineU.conjN ((s : GL (Fin d) K) * D * (s : GL (Fin d) K)⁻¹) hD' y =
        s * LineU.conjN D hD (s⁻¹ * y * s) * s⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, LineU.coe_conjN]
      group
    rw [e, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, ← map_inv, ← map_mul,
      ← map_mul, haD, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]

theorem ggKGTum_exists_perm_of_conj_mem_normalizer {n d p : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hK : UnitaryFieldData 2 n K) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, LineU.ActsDiagU φ a t)
    {s : ↥(unitarySU 2 n K d)}
    (hs : MulAut.conj (φ s) ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ∃ σ : Equiv.Perm (Fin d), ∀ a ∈ A,
      MulAut.conj (φ s) * a * (MulAut.conj (φ s))⁻¹ =
        MulAut.conj (φ (LineU.permSU hK σ)) * a *
          (MulAut.conj (φ (LineU.permSU hK σ)))⁻¹ := by
  classical
  haveI : Finite K := hK.finite
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hK.one_le hpq
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot (K := K) hp
    (TableBUE.dvd_card_sub_one hK.card_eq_sq hpq)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζq : ζ ^ (2 ^ n + 1) = 1 := by
    obtain ⟨k, hk⟩ := hpq
    rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
  have hmono : ∀ i j : Fin d, i ≠ j → ∃ D : Fin d → K,
      (((s : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) * diagonal (TypeA.ggPairVec i j ζ) =
        diagonal D * (((s : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    obtain ⟨Dij, hDijm⟩ := LineU.exists_diagSU hK (u := TypeA.ggPairVec i j ζ)
      (LineU.ggPairVec_norm_one hζq i j) (TypeA.prod_ggPairVec ζ hζ0)
    have haij : MulAut.conj (φ Dij) ∈ A :=
      LineU.conj_mem_of_selfCent_U hsc hdiag hDijm (TypeA.pow_ggPairVec hζ.pow_eq_one)
    have hbij : MulAut.conj (φ s) * MulAut.conj (φ Dij) * (MulAut.conj (φ s))⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hs (MulAut.conj (φ Dij))).mp haij
    obtain ⟨w, hwb⟩ := hdiag _ hbij
    have hb_eq : MulAut.conj (φ s) * MulAut.conj (φ Dij) * (MulAut.conj (φ s))⁻¹ =
        MulAut.conj (φ (s * Dij * s⁻¹)) := by
      simp only [map_mul, map_inv]
    rw [hb_eq] at hwb
    obtain ⟨c, hc⟩ := exists_diagonal_of_actsDiagU_conj hK hp hpq (by omega) hφker hwb
    refine ⟨fun k => c * w k, ?_⟩
    have hscaled : ((((s * Dij * s⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K)) :
        Matrix (Fin d) (Fin d) K) * (((s : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) =
        (((s : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) *
          (((Dij : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) := by
      have hGL : ((s * Dij * s⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) *
          (s : GL (Fin d) K) = (s : GL (Fin d) K) * (Dij : GL (Fin d) K) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      simpa only [Units.val_mul] using congrArg (fun x : GL (Fin d) K =>
        (x : Matrix (Fin d) (Fin d) K)) hGL
    have h1 := congrArg (fun M : Matrix (Fin d) (Fin d) K =>
      M * (((s : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K)) hc
    rw [hscaled, hDijm] at h1
    exact h1
  obtain ⟨π, hπ⟩ := TypeA.exists_perm_mul_diagonal hζinv (s : GL (Fin d) K)
    (fun i j hij => by
      obtain ⟨D, hD⟩ := hmono i j hij
      refine ⟨D, ?_⟩
      have hvec : TypeA.ggPairVec i j ζ = TypeA.rootT ζ i j := by
        funext m
        simp only [TypeA.ggPairVec_apply, TypeA.rootT]
        split_ifs <;> simp_all
      rwa [hvec] at hD)
  refine ⟨π⁻¹, fun a ha => ?_⟩
  obtain ⟨t, hat⟩ := hdiag a ha
  have hs' : (((s : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) * diagonal t =
      diagonal (t ∘ π) * (((s : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) := hπ t
  have hL : LineU.ActsDiagU φ (MulAut.conj (φ s) * a * (MulAut.conj (φ s))⁻¹) (t ∘ π) :=
    ActsDiagU.conj_of_mul_diagonal hat hs'
  have hR : LineU.ActsDiagU φ
      (MulAut.conj (φ (LineU.permSU hK π⁻¹)) * a *
        (MulAut.conj (φ (LineU.permSU hK π⁻¹)))⁻¹) (t ∘ π) := by
    have h := hat.conj_perm hK (π⁻¹)
    have hdiag : (fun k => t ((π⁻¹)⁻¹ k)) = (t ∘ π) := by
      funext k
      simp
    rwa [hdiag] at h
  exact LineU.ActsDiagU.unique hφs hL hR

theorem ggKGTum_sumZero_le_S {n d p : ℕ} {K : Type} [Field K] [NeZero p] {L' : Type}
    [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'} (hK : UnitaryFieldData 2 n K)
    {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t, LineU.ActsDiagU φ a t)
    {u : Kˣ} {hu : u ^ p = 1} (huq : u ^ (2 ^ n + 1) = 1) (hord : orderOf u = p) :
    UCoord.sumZero d p ≤ ggKGTum_S φ A u hu := by
  intro f hf
  let f' : ↥(UCoord.sumZero d p) := ⟨f, hf⟩
  have hnorm : ∀ k, (UModel.uvec hu f' k : K) ^ (2 ^ n + 1) = 1 := fun k => by
    rw [← Units.val_pow_eq_pow_val, UModel.uvec_pow_norm hu huq f' k, Units.val_one]
  have hprod : ∏ k, (UModel.uvec hu f' k : K) = 1 := by
    simpa using congrArg (fun x : Kˣ => (x : K)) (UModel.prod_uvec hu hord f')
  obtain ⟨D, hD⟩ := LineU.exists_diagSU hK hnorm hprod
  have hDA : MulAut.conj (φ D) ∈ A :=
    LineU.conj_mem_of_selfCent_U hsc hdiag hD fun k => by
      rw [← Units.val_pow_eq_pow_val, UModel.uvec_pow_eq_one hu f' k, Units.val_one]
  refine ⟨MulAut.conj (φ D), hDA, fun k => (UModel.uvec hu f' k : K),
    LineU.actsDiagU_conj hD, 1, fun k => ?_⟩
  rw [one_mul]
  rfl

theorem ggKGTum_ggConjAut_eq_of_conj_eq {n d p : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hK : UnitaryFieldData 2 n K)
    (hpq : p ∣ 2 ^ n + 1) (hd3 : 3 ≤ d) (hd : 0 < d)
    (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t, LineU.ActsDiagU φ a t)
    {u : Kˣ} {hu : u ^ p = 1}
    {s : ↥(unitarySU 2 n K d)} {σ : Equiv.Perm (Fin d)}
    (hs : MulAut.conj (φ s) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hσ : ∀ a ∈ A, MulAut.conj (φ s) * a * (MulAut.conj (φ s))⁻¹ =
      MulAut.conj (φ (LineU.permSU hK σ)) * a *
        (MulAut.conj (φ (LineU.permSU hK σ)))⁻¹) :
    ∀ f g : ↥(ggKGTum_S φ A u hu),
      (g : Fin d → Multiplicative (ZMod p)) = permAut σ (f : Fin d → Multiplicative (ZMod p)) →
      ggConjAut A hs (ggKGTum_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd f) =
        ggKGTum_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd g := by
  intro f g hfg
  have hg : g = (⟨permAut σ (f : Fin d → Multiplicative (ZMod p)),
      ggKGTum_permAut_mem_S hK hpq hd3 hφs hφker hAp hsc hdiag σ f.2⟩ :
        ↥(ggKGTum_S φ A u hu)) := by
    apply Subtype.ext
    exact hfg
  rw [hg]
  obtain ⟨-, t, ht, c, hc⟩ := Classical.choose_spec f.2
  obtain ⟨-, t', ht', c', hc'⟩ := Classical.choose_spec
    (show (permAut σ (f : Fin d → Multiplicative (ZMod p))) ∈ ggKGTum_S φ A u hu from
      ggKGTum_permAut_mem_S hK hpq hd3 hφs hφker hAp hsc hdiag σ f.2)
  have heq : MulAut.conj (φ s) *
        ((ggKGTum_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd f : ↥A) : MulAut L') *
        (MulAut.conj (φ s))⁻¹ =
      ((ggKGTum_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd
        ⟨permAut σ (f : Fin d → Multiplicative (ZMod p)),
          ggKGTum_permAut_mem_S hK hpq hd3 hφs hφker hAp hsc hdiag σ f.2⟩ : ↥A) :
        MulAut L') := by
    rw [hσ ((ggKGTum_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd f : ↥A))
      ((ggKGTum_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd f : ↥A)).2]
    refine ggKGTum_eq_of_diag_const (hd := hd) hφs
      (LineU.ActsDiagU.conj_perm hK ht σ) ht' (c := c * c'⁻¹) ?_
    intro k
    have hc'0 : c' ≠ 0 := by
      intro h0
      have h1 := ht'.ne_zero k
      rw [hc' k, h0, zero_mul] at h1
      exact h1 rfl
    change t (σ.symm k) = (c * c'⁻¹) * t' k
    rw [hc (σ.symm k), hc' k, ggKGTum_uvec_permAut]
    simp only [Function.comp_apply]
    rw [show ⇑σ.symm = ⇑(σ⁻¹ : Equiv.Perm (Fin d)) from rfl]
    field_simp [hc'0]
  apply Subtype.ext
  rw [ggConjAut_apply]
  exact heq

theorem ggKGTum_ggConjAut_eq {n d p : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d) (hd0 : 0 < d)
    (hK : UnitaryFieldData 2 n K)
    {φ : ↥(unitarySU 2 n K d) →* L'} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t, LineU.ActsDiagU φ a t)
    {u : Kˣ} {hu : u ^ p = 1}
    {m : L'} (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ∃ π : Equiv.Perm (Fin d),
      ∀ f g : ↥(ggKGTum_S φ A u hu),
        (g : Fin d → Multiplicative (ZMod p)) = permAut π (f : Fin d → Multiplicative (ZMod p)) →
        ggConjAut A hm (ggKGTum_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd0 f) =
          ggKGTum_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd0 g := by
  obtain ⟨s, rfl⟩ := hφs m
  obtain ⟨σ, hσ⟩ :=
    ggKGTum_exists_perm_of_conj_mem_normalizer hK hp hpq hd hφs hφker hsc hdiag hm
  exact ⟨σ, ggKGTum_ggConjAut_eq_of_conj_eq hK hpq (by omega) hd0 hφs hφker hA.2 hsc hdiag
    hm hσ⟩

theorem ggKGTAU_permModel
    {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : p ^ (d / p + 2) ≤ Nat.card A) (hsc : GGTorusSelfCent p A) :
    ∃ (φ : ↥(unitarySU 2 n K d) →* L'), Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
        ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) ∧
      (∀ a ∈ A, ∃ t : Fin d → K, LineU.ActsDiagU φ a t) ∧
      ∃ (S : Subgroup (Fin d → Multiplicative (ZMod p))) (Θ : ↥S →* ↥A),
        (S = ⊤ ∨ S = sumZero d p) ∧ Function.Surjective Θ ∧
        (∀ f : ↥S, Θ f = 1 ↔
          ∃ c : Multiplicative (ZMod p), (f : Fin d → Multiplicative (ZMod p)) = fun _ => c) ∧
        (∀ (m : L') (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))),
          ∃ π : Equiv.Perm (Fin d), ∀ f g : ↥S,
            (g : Fin d → Multiplicative (ZMod p)) =
              permAut π (f : Fin d → Multiplicative (ZMod p)) →
              ggConjAut A hm (Θ f) = Θ g) ∧
        (∀ (hK' : UnitaryFieldData 2 n K) (σ : Equiv.Perm (Fin d))
          (hm : MulAut.conj (φ (LineU.permSU hK' σ)) ∈ Subgroup.normalizer (A : Set (MulAut L'))),
          ∀ f g : ↥S, (g : Fin d → Multiplicative (ZMod p)) =
              permAut σ (f : Fin d → Multiplicative (ZMod p)) →
              ggConjAut A hm (Θ f) = Θ g) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hd0 : 0 < d := by omega
  have hdn : (d, n) ≠ (6, 1) := by rintro ⟨-, h⟩; omega
  have hUF : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK (by omega)
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel hK (by omega) hd hp hpq hpd
      (LineU.unitaryUniversalCover_holds n d K hK hd hdn) hψ hker hperf hA hAI hcard
  obtain ⟨u, hord, huq⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one (ℓ := 2) (f := n) hUF hp hpq
  have hu : u ^ p = 1 := hord ▸ pow_orderOf_eq_one u
  have hζu : IsPrimitiveRoot (u : K) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (hord ▸ IsPrimitiveRoot.orderOf u)
  let S := ggKGTum_S φ A u hu
  let Θ := ggKGTum_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd0
  have hsurj : Function.Surjective Θ :=
    ggKGTum_Θ_surjective hUF (by omega) hφs hφker hA.2 hdiag hζu hd0
  have hkerΘ : ∀ f : ↥S, Θ f = 1 ↔
      ∃ c : Multiplicative (ZMod p), (f : Fin d → Multiplicative (ZMod p)) = fun _ => c :=
    fun f => ggKGTum_Θ_eq_one_iff hUF (by omega) hφs hφker hord hd0 f
  have hSge : p ^ (d - 1) ≤ Nat.card ↥S := by
    have hVle : UCoord.sumZero d p ≤ S := ggKGTum_sumZero_le_S hUF hsc hdiag huq hord
    calc p ^ (d - 1) = Nat.card ↥(UCoord.sumZero d p) :=
          (ggKGTum_card_sumZero hp ⟨(u : K), hζu⟩ (by omega)).symm
      _ ≤ Nat.card ↥S := Nat.card_mono (Set.toFinite _) hVle
  have hS_or : S = ⊤ ∨ S = sumZero d p :=
    ggKGTum_S_eq_top_or_sumZero hp hd hord ⟨u, hζu⟩
      (fun σ {f} hf => ggKGTum_permAut_mem_S hUF hpq (by omega) hφs hφker hA.2 hsc hdiag σ hf)
      hSge
  refine ⟨φ, hφs, hφker, hdiag, S, Θ, hS_or, hsurj, hkerΘ, ?_, ?_⟩
  · intro m hm
    obtain ⟨π, hπ⟩ := ggKGTum_ggConjAut_eq hp hpq hd hd0 hUF hφs hφker hA hsc hdiag hm
    exact ⟨π, hπ⟩
  · intro hK' σ hm f g hfg
    exact ggKGTum_ggConjAut_eq_of_conj_eq hK' hpq (by omega) hd0 hφs hφker hA.2 hsc hdiag
      hm (fun _ _ => rfl) f g hfg

end CFSG.StandardType

end
