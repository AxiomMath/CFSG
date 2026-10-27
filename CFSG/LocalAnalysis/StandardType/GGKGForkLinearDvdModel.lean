module

public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearRow
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.RankThree.PartOne.KF.SymTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord UCoord

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private noncomputable def ggKGTm_uvec {d p : ℕ} {K : Type} [Field K] (u : Kˣ) (hu : u ^ p = 1) :
    (Fin d → Multiplicative (ZMod p)) →* (Fin d → Kˣ) :=
  MonoidHom.compLeft (TableBSymp.zmodPowHom hu) (Fin d)

private theorem ggKGTm_uvec_apply {d p : ℕ} {K : Type} [Field K] [NeZero p]
    (u : Kˣ) (hu : u ^ p = 1) (f : Fin d → Multiplicative (ZMod p)) (k : Fin d) :
    ggKGTm_uvec u hu f k = u ^ (Multiplicative.toAdd (f k)).val := by
  simp only [ggKGTm_uvec, MonoidHom.compLeft_apply, Function.comp_apply,
    TableBSymp.zmodPowHom_apply]

private theorem ggKGTm_uvec_permAut {d p : ℕ} {K : Type} [Field K]
    (u : Kˣ) (hu : u ^ p = 1) (σ : Equiv.Perm (Fin d))
    (f : Fin d → Multiplicative (ZMod p)) :
    ggKGTm_uvec u hu (permAut σ f) = ggKGTm_uvec u hu f ∘ ⇑σ⁻¹ := rfl

private theorem ggKGTm_uvec_injective_apply {d p : ℕ} {K : Type} [Field K] [NeZero p]
    {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p)
    {f g : Fin d → Multiplicative (ZMod p)} (k : Fin d)
    (h : ggKGTm_uvec u hu f k = ggKGTm_uvec u hu g k) : f k = g k := by
  rw [ggKGTm_uvec_apply, ggKGTm_uvec_apply] at h
  have h2 := (pow_inj_mod (x := u)).mp h
  rw [hord, Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h2
  exact Multiplicative.toAdd.injective (ZMod.val_injective p h2)

private theorem ggKGTm_uvec_injective {d p : ℕ} {K : Type} [Field K] [NeZero p]
    {u : Kˣ} (hu : u ^ p = 1) (hord : orderOf u = p) :
    Function.Injective (ggKGTm_uvec (d := d) u hu) := by
  intro f g hfg
  funext k
  exact ggKGTm_uvec_injective_apply hu hord k (congrFun hfg k)

private def ggKGTm_Good {d p : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    (φ : SpecialLinearGroup (Fin d) K →* L') (A : Subgroup (MulAut L')) (u : Kˣ) (hu : u ^ p = 1)
    (f : Fin d → Multiplicative (ZMod p)) (a : MulAut L') : Prop :=
  a ∈ A ∧ ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ a t ∧
    ∃ c : K, ∀ k, t k = c * (ggKGTm_uvec u hu f k : K)

private theorem ggKGTm_eq_of_diag_const {d : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    (hφs : Function.Surjective φ) {hd : 0 < d}
    {a b : MulAut L'} {t t' : Fin d → K}
    (ha : TypeANbrDvd.ActsDiag φ a t) (hb : TypeANbrDvd.ActsDiag φ b t')
    {c : K} (hc : ∀ k, t k = c * t' k) : a = b := by
  have hmul : TypeANbrDvd.ActsDiag φ (a * b⁻¹) (fun k => t k * (t' k)⁻¹) :=
    ha.mul hb.inv
  have hconst : ∀ k l, (fun k => t k * (t' k)⁻¹) k = (fun k => t k * (t' k)⁻¹) l := by
    intro k l
    change t k * (t' k)⁻¹ = t l * (t' l)⁻¹
    rw [hc k, hc l, mul_assoc, mul_inv_cancel₀ (hb.ne_zero k), mul_one,
      mul_assoc, mul_inv_cancel₀ (hb.ne_zero l), mul_one]
  have h1 : a * b⁻¹ = 1 := hmul.eq_one hd hφs hconst
  exact mul_inv_eq_one.mp h1

private theorem ggKGTm_eq_of_Good {d p : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    (hφs : Function.Surjective φ) {hd : 0 < d}
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1}
    {f : Fin d → Multiplicative (ZMod p)} {a b : MulAut L'}
    (ha : ggKGTm_Good φ A u hu f a) (hb : ggKGTm_Good φ A u hu f b) : a = b := by
  obtain ⟨-, t, ht, c, hc⟩ := ha
  obtain ⟨-, t', ht', c', hc'⟩ := hb
  have hc'0 : c' ≠ 0 := by
    intro h0
    have h1 := ht'.ne_zero ⟨0, hd⟩
    rw [hc' _, h0, zero_mul] at h1
    exact h1 rfl
  refine ggKGTm_eq_of_diag_const (hd := hd) hφs ht ht' (c := c * c'⁻¹) fun k => ?_
  have h2 : c'⁻¹ * (c' * ↑((ggKGTm_uvec u hu) f k)) = ↑((ggKGTm_uvec u hu) f k) := by
    rw [← mul_assoc, inv_mul_cancel₀ hc'0, one_mul]
  rw [hc k, hc' k, mul_assoc c, h2]

private theorem ggKGTm_Good_mul {d p : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1}
    {f g : Fin d → Multiplicative (ZMod p)} {a b : MulAut L'}
    (ha : ggKGTm_Good φ A u hu f a) (hb : ggKGTm_Good φ A u hu g b) :
    ggKGTm_Good φ A u hu (f * g) (a * b) := by
  obtain ⟨haA, t, ht, c, hc⟩ := ha
  obtain ⟨hbA, t', ht', c', hc'⟩ := hb
  refine ⟨A.mul_mem haA hbA, fun k => t k * t' k, ht.mul ht', c * c', fun k => ?_⟩
  change t k * t' k = c * c' * ↑((ggKGTm_uvec u hu) (f * g) k)
  rw [hc k, hc' k, map_mul, Pi.mul_apply, Units.val_mul]
  ring

private theorem ggKGTm_Good_inv {d p : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1}
    {f : Fin d → Multiplicative (ZMod p)} {a : MulAut L'}
    (ha : ggKGTm_Good φ A u hu f a) : ggKGTm_Good φ A u hu f⁻¹ a⁻¹ := by
  obtain ⟨haA, t, ht, c, hc⟩ := ha
  refine ⟨A.inv_mem haA, fun k => (t k)⁻¹, ht.inv, c⁻¹, fun k => ?_⟩
  have h1 : (ggKGTm_uvec u hu f⁻¹ k : K) = ((ggKGTm_uvec u hu f k : K))⁻¹ := by
    rw [map_inv]
    simp [Pi.inv_apply]
  change (t k)⁻¹ = c⁻¹ * ↑((ggKGTm_uvec u hu) f⁻¹ k)
  rw [hc k, h1, _root_.mul_inv_rev, mul_comm]

private theorem ggKGTm_actsDiag_one_const {d : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    {c : K} (hc : c ≠ 0) :
    TypeANbrDvd.ActsDiag φ (1 : MulAut L') (fun _ : Fin d => c) := by
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc), ?_, fun s => ?_⟩
  · ext i j
    rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply]
    by_cases hij : i = j <;> simp [hij]
  · rw [MulAut.one_apply,
      TypeA.slConjugation_eq_self_of_const (t := fun _ : Fin d => c) (c := c)
        (by ext i j; rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply];
            by_cases hij : i = j <;> simp [hij]) (fun _ => rfl) hc s]

private theorem ggKGTm_Good_one_of_const {d p : ℕ} {K : Type} [Field K] [NeZero p]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1} {hd : 0 < d}
    {f : Fin d → Multiplicative (ZMod p)} (hf : ∀ i j, f i = f j) :
    ggKGTm_Good φ A u hu f 1 := by
  have hconst : ∀ k, (ggKGTm_uvec u hu f k : K) = (ggKGTm_uvec u hu f ⟨0, hd⟩ : K) := by
    intro k
    rw [ggKGTm_uvec_apply, ggKGTm_uvec_apply, hf k ⟨0, hd⟩]
  refine ⟨A.one_mem, fun _ => (ggKGTm_uvec u hu f ⟨0, hd⟩ : K),
    ggKGTm_actsDiag_one_const (Units.ne_zero _), 1, fun k => ?_⟩
  rw [hconst k, one_mul]

private theorem ggKGTm_Good_one {d p : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1} :
    ggKGTm_Good φ A u hu (1 : Fin d → Multiplicative (ZMod p)) 1 := by
  refine ⟨A.one_mem, fun _ => (1 : K), TypeANbrDvd.actsDiag_one, 1, fun k => ?_⟩
  change (1 : K) = 1 * ↑((ggKGTm_uvec u hu) 1 k)
  rw [map_one]
  simp

private def ggKGTm_const (d p : ℕ) : Subgroup (Fin d → Multiplicative (ZMod p)) where
  carrier := {f | ∀ i j, f i = f j}
  mul_mem' := by
    intro f g hf hg i j
    simp only [Pi.mul_apply, hf i j, hg i j]
  one_mem' := fun i j => rfl
  inv_mem' := by
    intro f hf i j
    simp only [Pi.inv_apply, hf i j]

private def ggKGTm_S {d p : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    (φ : SpecialLinearGroup (Fin d) K →* L') (A : Subgroup (MulAut L')) (u : Kˣ) (hu : u ^ p = 1) :
    Subgroup (Fin d → Multiplicative (ZMod p)) where
  carrier := {f | ∃ a, ggKGTm_Good φ A u hu f a}
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, ggKGTm_Good_mul ha hb⟩
  one_mem' := ⟨1, ggKGTm_Good_one⟩
  inv_mem' := by
    rintro f ⟨a, ha⟩
    exact ⟨a⁻¹, ggKGTm_Good_inv ha⟩

private noncomputable def ggKGTm_Θ {d p : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : SpecialLinearGroup (Fin d) K →* L'} (hφs : Function.Surjective φ)
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1} (hd : 0 < d) :
    ↥(ggKGTm_S φ A u hu) →* ↥A where
  toFun f := ⟨Classical.choose f.2, (Classical.choose_spec f.2).1⟩
  map_one' := by
    apply Subtype.ext
    exact ggKGTm_eq_of_Good (hd := hd) hφs
      (Classical.choose_spec (1 : ↥(ggKGTm_S φ A u hu)).2) ggKGTm_Good_one
  map_mul' := by
    intro f g
    apply Subtype.ext
    exact ggKGTm_eq_of_Good (hd := hd) hφs (Classical.choose_spec (f * g).2)
      (ggKGTm_Good_mul (Classical.choose_spec f.2) (Classical.choose_spec g.2))

private theorem ggKGTm_Θ_apply {d p : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : SpecialLinearGroup (Fin d) K →* L'} {hφs : Function.Surjective φ}
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1} {hd : 0 < d}
    (f : ↥(ggKGTm_S φ A u hu)) :
    ((ggKGTm_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd f : ↥A) : MulAut L') =
      Classical.choose f.2 := rfl

private theorem ggKGTm_Θ_surjective {d p : ℕ} {K : Type} [Field K] [NeZero p]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hAp : ∀ a ∈ A, a ^ p = 1) (hdiag : ∀ a ∈ A, ∃ t, TypeANbrDvd.ActsDiag φ a t)
    {u : Kˣ} {hu : u ^ p = 1} (hζ : IsPrimitiveRoot (u : K) p) (hd : 0 < d) :
    Function.Surjective (ggKGTm_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd) := by
  intro a
  obtain ⟨t, ht⟩ := hdiag a a.2
  have hratio : ∀ k, (t k * (t ⟨0, hd⟩)⁻¹) ^ p = 1 := fun k =>
    ht.ratio_pow hφker (hAp a a.2) k ⟨0, hd⟩
  choose n hn_lt hn using fun k => hζ.eq_pow_of_pow_eq_one (hratio k)
  let f : Fin d → Multiplicative (ZMod p) := fun k => Multiplicative.ofAdd (n k : ZMod p)
  have hf : ∀ k, (ggKGTm_uvec u hu f k : K) = t k * (t ⟨0, hd⟩)⁻¹ := by
    intro k
    rw [ggKGTm_uvec_apply]
    change (u ^ (n k : ZMod p).val : K) = t k * (t ⟨0, hd⟩)⁻¹
    have h1 : (n k : ZMod p).val = n k := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hn_lt k)]
    rw [h1]
    exact hn k
  have hgood : ggKGTm_Good φ A u hu f a := by
    refine ⟨a.2, t, ht, t ⟨0, hd⟩, fun k => ?_⟩
    rw [hf k]
    field_simp [ht.ne_zero ⟨0, hd⟩]
  refine ⟨⟨f, ⟨a, hgood⟩⟩, ?_⟩
  apply Subtype.ext
  have hspec : ggKGTm_Good φ A u hu f
      (Classical.choose (⟨a, hgood⟩ : ∃ b, ggKGTm_Good φ A u hu f b)) :=
    Classical.choose_spec _
  exact ggKGTm_eq_of_Good (hd := hd) hφs hspec hgood

private theorem ggKGTm_Θ_eq_one_iff {d p : ℕ} {K : Type} [Field K] [NeZero p]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    (hφs : Function.Surjective φ) (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1}
    (hord : orderOf u = p) (hd : 0 < d)
    (f : ↥(ggKGTm_S φ A u hu)) :
    ggKGTm_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd f = 1 ↔
      ∃ c : Multiplicative (ZMod p), (f : Fin d → Multiplicative (ZMod p)) = fun _ => c := by
  constructor
  · intro h1
    obtain ⟨-, t, ht, c, hc⟩ := Classical.choose_spec f.2
    have h1' : (Classical.choose f.2 : MulAut L') = 1 := by
      have := congrArg (fun x : ↥A => (x : MulAut L')) h1
      simpa [ggKGTm_Θ_apply] using this
    have ht1 : TypeANbrDvd.ActsDiag φ (1 : MulAut L') t := h1' ▸ ht
    have hfun : ggKGTm_uvec u hu (f : Fin d → Multiplicative (ZMod p)) =
        ggKGTm_uvec u hu (fun _ => (f : Fin d → Multiplicative (ZMod p)) ⟨0, hd⟩) := by
      funext k
      by_cases hk : k = ⟨0, hd⟩
      · subst hk
        rfl
      · have hratio := ht1.ratio hφker (TypeANbrDvd.actsDiag_one (φ' := φ)) hk
        simp only [inv_one, mul_one] at hratio
        have htk : t k = t ⟨0, hd⟩ := (mul_inv_eq_one₀ (ht.ne_zero ⟨0, hd⟩)).mp hratio
        have hc0 : c ≠ 0 := by
          intro h0
          have h2 := ht.ne_zero k
          rw [hc k, h0, zero_mul] at h2
          exact h2 rfl
        have huv : ggKGTm_uvec u hu (f : Fin d → Multiplicative (ZMod p)) k =
            ggKGTm_uvec u hu (f : Fin d → Multiplicative (ZMod p)) ⟨0, hd⟩ := by
          apply Units.ext
          exact mul_left_cancel₀ hc0 (by rw [← hc k, ← hc ⟨0, hd⟩, htk])
        have hconst : ggKGTm_uvec u hu (fun _ => (f : Fin d → Multiplicative (ZMod p)) ⟨0, hd⟩) k =
            ggKGTm_uvec u hu (f : Fin d → Multiplicative (ZMod p)) ⟨0, hd⟩ := rfl
        rw [hconst]
        exact huv
    refine ⟨(f : Fin d → Multiplicative (ZMod p)) ⟨0, hd⟩, ?_⟩
    exact ggKGTm_uvec_injective hu hord hfun
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    rw [ggKGTm_Θ_apply]
    exact ggKGTm_eq_of_Good (hd := hd) hφs (Classical.choose_spec f.2)
      (ggKGTm_Good_one_of_const (hd := hd) (fun i j => by rw [hc]))

private theorem ggKGTm_const_le_S {d p : ℕ} {K : Type} [Field K] [NeZero p]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1} (hd : 0 < d) :
    ggKGTm_const d p ≤ ggKGTm_S φ A u hu := by
  intro f hf
  exact ⟨1, ggKGTm_Good_one_of_const (hd := hd) hf⟩

private theorem ggKGTm_card_M {d p : ℕ} :
    Nat.card (Fin d → Multiplicative (ZMod p)) = p ^ d := by
  rw [Nat.card_fun, Nat.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

private theorem ggKGTm_card_const {d p : ℕ} (hd : 0 < d) :
    Nat.card ↥(ggKGTm_const d p) = p := by
  have hbij : Function.Bijective
      (fun f : ↥(ggKGTm_const d p) => (f : Fin d → Multiplicative (ZMod p)) ⟨0, hd⟩) := by
    constructor
    · intro f g h
      apply Subtype.ext
      funext k
      rw [show (f : Fin d → Multiplicative (ZMod p)) k = f.1 ⟨0, hd⟩ from f.2 k ⟨0, hd⟩,
        show (g : Fin d → Multiplicative (ZMod p)) k = g.1 ⟨0, hd⟩ from g.2 k ⟨0, hd⟩]
      exact h
    · intro c
      exact ⟨⟨fun _ => c, fun _ _ => rfl⟩, rfl⟩
  calc Nat.card ↥(ggKGTm_const d p) = Nat.card (Multiplicative (ZMod p)) :=
        Nat.card_congr (Equiv.ofBijective _ hbij)
    _ = Nat.card (ZMod p) := Nat.card_congr Multiplicative.toAdd
    _ = p := Nat.card_zmod p

private theorem ggKGTm_card_S {d p : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    (hφs : Function.Surjective φ)
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1} {hd : 0 < d}
    (hsurj : Function.Surjective (ggKGTm_Θ (φ := φ) hφs (A := A) (u := u) (hu := hu) hd))
    (hker : (ggKGTm_Θ (φ := φ) hφs (A := A) (u := u) (hu := hu) hd).ker =
      (ggKGTm_const d p).subgroupOf (ggKGTm_S φ A u hu))
    (hconst_le : ggKGTm_const d p ≤ ggKGTm_S φ A u hu) :
    Nat.card ↥(ggKGTm_S φ A u hu) = p * Nat.card ↥A := by
  have hidx : (ggKGTm_Θ (φ := φ) hφs (A := A) (u := u) (hu := hu) hd).ker.index =
      Nat.card ↥A := by
    rw [Subgroup.index_ker]
    have hrange : (ggKGTm_Θ (φ := φ) hφs (A := A) (u := u) (hu := hu) hd).range = ⊤ :=
      (MonoidHom.range_eq_top).mpr hsurj
    rw [hrange]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have hcard := Subgroup.card_mul_index
    (ggKGTm_Θ (φ := φ) hφs (A := A) (u := u) (hu := hu) hd).ker
  rw [hidx] at hcard
  have hkercard : Nat.card ↥(ggKGTm_Θ (φ := φ) hφs (A := A) (u := u) (hu := hu) hd).ker = p := by
    rw [hker]
    have heq : Nat.card ↥((ggKGTm_const d p).subgroupOf (ggKGTm_S φ A u hu)) =
        Nat.card ↥(ggKGTm_const d p) :=
      Nat.card_congr
        { toFun := fun f => ⟨f.1.1, f.2⟩
          invFun := fun f => ⟨⟨f.1, hconst_le f.2⟩, f.2⟩
          left_inv := fun f => by ext; rfl
          right_inv := fun f => by ext; rfl }
    rw [heq, ggKGTm_card_const hd]
  rw [hkercard] at hcard
  exact hcard.symm

private theorem ggKGTm_Good_permAut {d p : ℕ} {K : Type} [Field K] [CharP K 2]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    (hφs : Function.Surjective φ) (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t, TypeANbrDvd.ActsDiag φ a t)
    {u : Kˣ} {hu : u ^ p = 1} {σ : Equiv.Perm (Fin d)}
    {f : Fin d → Multiplicative (ZMod p)} {a : MulAut L'}
    (ha : ggKGTm_Good φ A u hu f a) :
    ggKGTm_Good φ A u hu (permAut σ f)
      (NbrInnerWeylA.permConj φ σ * a * (NbrInnerWeylA.permConj φ σ)⁻¹) := by
  obtain ⟨haA, t, ht, c, hc⟩ := ha
  have hN : NbrInnerWeylA.permConj φ σ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    TypeANbrDvd.permConj_mem_normalizer_of_selfCent hφs hφker hAp hsc hdiag σ
  have hconjA : NbrInnerWeylA.permConj φ σ * a * (NbrInnerWeylA.permConj φ σ)⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hN a).mp haA
  have hperm : NbrInnerWeylA.permConj φ σ = MulAut.conj (φ (permSL σ⁻¹)) := rfl
  have hcd : TypeANbrDvd.ActsDiag φ
      (NbrInnerWeylA.permConj φ σ * a * (NbrInnerWeylA.permConj φ σ)⁻¹) (t ∘ ⇑σ.symm) := by
    rw [hperm]
    exact ht.conj_perm σ.symm
  refine ⟨hconjA, t ∘ ⇑σ.symm, hcd, c, fun k => ?_⟩
  change t (σ.symm k) = c * ↑((ggKGTm_uvec u hu) (permAut σ f) k)
  rw [hc (σ.symm k), ggKGTm_uvec_permAut]
  rfl

private theorem ggKGTm_permAut_mem_S {d p : ℕ} {K : Type} [Field K] [CharP K 2]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    (hφs : Function.Surjective φ) (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t, TypeANbrDvd.ActsDiag φ a t)
    {u : Kˣ} {hu : u ^ p = 1} (σ : Equiv.Perm (Fin d)) {f : Fin d → Multiplicative (ZMod p)}
    (hf : f ∈ ggKGTm_S φ A u hu) : permAut σ f ∈ ggKGTm_S φ A u hu := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨_, ggKGTm_Good_permAut hφs hφker hAp hsc hdiag ha⟩

private theorem ggKGTm_card_sumZero {d p : ℕ} {K : Type} [Field K] [Finite K]
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
  calc Nat.card ↥(sumZero (m + 1) p) = Nat.card ↥(RankThree.PartOne.KFU.torusVec p (m + 1) K) :=
        Nat.card_congr (Equiv.ofBijective F hbij)
    _ = p ^ m := RankThree.PartOne.KFU.card_torusVec_eq hp.pos ⟨u, hζu⟩ m

private theorem ggKGTm_card_sumZero_eq_torusVec {d p : ℕ} {K : Type} [Field K] [NeZero p]
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

private theorem ggKGTm_S_eq_top_or_sumZero {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hd : 5 ≤ d) {L' : Type} [Group L']
    {φ : SpecialLinearGroup (Fin d) K →* L'} {A : Subgroup (MulAut L')}
    {u : Kˣ} {hu : u ^ p = 1} (hord : orderOf u = p)
    (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (hperm : ∀ (σ : Equiv.Perm (Fin d)) {f : Fin d → Multiplicative (ZMod p)},
      f ∈ ggKGTm_S φ A u hu → permAut σ f ∈ ggKGTm_S φ A u hu)
    (hSge : p ^ (d - 1) ≤ Nat.card ↥(ggKGTm_S φ A u hu)) :
    ggKGTm_S φ A u hu = ⊤ ∨ ggKGTm_S φ A u hu = sumZero d p := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hd0 : 0 < d := by omega
  let S := ggKGTm_S φ A u hu
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
      rw [hzero, mul_zero, ggKGTm_card_M] at h
      exact (pow_pos hp.pos d).ne' h.symm
    omega
  have hSdvd : S.index ∣ p ^ d := by
    have h := Subgroup.card_mul_index S
    rw [ggKGTm_card_M] at h
    exact ⟨Nat.card ↥S, by rw [mul_comm]; exact h.symm⟩
  have hindex_le : S.index ≤ p := by
    have h := Subgroup.card_mul_index S
    rw [ggKGTm_card_M] at h
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
    rw [hindex_eq, ggKGTm_card_M] at h
    have h1 : Nat.card ↥S * p = p ^ (d - 1) * p := by
      rw [h, show p ^ d = p ^ (d - 1) * p by rw [← pow_succ, Nat.sub_add_cancel (by omega)]]
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1
  have hVcard : Nat.card ↥(sumZero d p) = p ^ (d - 1) := ggKGTm_card_sumZero hp hζ (by omega)
  have hVTV : Nat.card ↥(sumZero d p) = Nat.card ↥(RankThree.PartOne.KFU.torusVec p d K) :=
    ggKGTm_card_sumZero_eq_torusVec hu hord
  have hVindex : (sumZero d p).index = p := by
    have h := Subgroup.card_mul_index (sumZero d p)
    rw [hVcard, ggKGTm_card_M] at h
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
    rw [Subgroup.index_inf, hVindex, ggKGTm_card_M] at h
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
    have hWle : W ≤ ggKGTm_const d p := by
      intro f hf
      have hle' : ψ ⟨f, hf⟩ ∈ RankThree.PartOne.KFU.scalarSub p d K := hle ⟨⟨f, hf⟩, rfl⟩
      intro i j
      have h1 : ggKGTm_uvec u hu f i = ggKGTm_uvec u hu f j := by
        have h2 := hle' i j
        have h3 : (ψ ⟨f, hf⟩ : Fin d → Kˣ) = ggKGTm_uvec u hu f := by
          rw [hψval]
          rfl
        rwa [h3] at h2
      have h2 : ggKGTm_uvec u hu f i = ggKGTm_uvec u hu (fun _ => f j) i := by
        show ggKGTm_uvec u hu f i = ggKGTm_uvec u hu f j
        exact h1
      exact ggKGTm_uvec_injective_apply hu hord i h2
    have hWle_card : Nat.card ↥W ≤ p := by
      have hinj : Function.Injective
          (fun f : ↥W => (⟨f.1, hWle f.2⟩ : ↥(ggKGTm_const d p))) := by
        intro f g h
        have h1 : f.1 = g.1 :=
          congrArg (fun z : ↥(ggKGTm_const d p) => (z : Fin d → Multiplicative (ZMod p))) h
        exact Subtype.ext h1
      calc Nat.card ↥W ≤ Nat.card ↥(ggKGTm_const d p) :=
            Nat.card_le_card_of_injective _ hinj
        _ = p := ggKGTm_card_const hd0
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



private theorem ggKGTm_ker_eq {d p : ℕ} {K : Type} [Field K] [NeZero p]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    (hφs : Function.Surjective φ) (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} {u : Kˣ} {hu : u ^ p = 1}
    (hord : orderOf u = p) (hd : 0 < d) :
    (ggKGTm_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd).ker =
      (ggKGTm_const d p).subgroupOf (ggKGTm_S φ A u hu) := by
  ext f
  rw [MonoidHom.mem_ker, ggKGTm_Θ_eq_one_iff hφs hφker hord hd f, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨c, hc⟩ i j
    rw [hc]
  · intro hf
    exact ⟨(f : Fin d → Multiplicative (ZMod p)) ⟨0, hd⟩,
      funext fun k => by rw [hf k ⟨0, hd⟩]⟩

private theorem ggKGTm_ggConjAut_eq {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    {L' : Type} [Group L'] [Finite L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    (hφs : Function.Surjective φ) (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t, TypeANbrDvd.ActsDiag φ a t)
    {u : Kˣ} {hu : u ^ p = 1} (hd : 0 < d)
    {n : L'} (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ∃ π : Equiv.Perm (Fin d),
      ∀ (f g : ↥(ggKGTm_S φ A u hu)),
        (g : Fin d → Multiplicative (ZMod p)) = permAut π (f : Fin d → Multiplicative (ZMod p)) →
        ggConjAut A hn (ggKGTm_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd f) =
          ggKGTm_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd g := by
  obtain ⟨s, rfl⟩ := hφs n
  obtain ⟨σ, hσ⟩ :=
    TypeANbrDvd.exists_perm_of_conj_mem_normalizer hp hp2 hpK hφs hφker hA hsc hdiag hn
  refine ⟨σ, fun f g hfg => ?_⟩
  have hg : g = (⟨permAut σ (f : Fin d → Multiplicative (ZMod p)),
      ggKGTm_permAut_mem_S hφs hφker hA.2 hsc hdiag σ f.2⟩ : ↥(ggKGTm_S φ A u hu)) := by
    apply Subtype.ext
    exact hfg
  rw [hg]
  obtain ⟨-, t, ht, c, hc⟩ := Classical.choose_spec f.2
  obtain ⟨-, t', ht', c', hc'⟩ := Classical.choose_spec
    (show (permAut σ (f : Fin d → Multiplicative (ZMod p))) ∈ ggKGTm_S φ A u hu from
      ggKGTm_permAut_mem_S hφs hφker hA.2 hsc hdiag σ f.2)
  have heq : MulAut.conj (φ s) *
        ((ggKGTm_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd f : ↥A) : MulAut L') *
        (MulAut.conj (φ s))⁻¹ =
      ((ggKGTm_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd
        ⟨permAut σ (f : Fin d → Multiplicative (ZMod p)),
          ggKGTm_permAut_mem_S hφs hφker hA.2 hsc hdiag σ f.2⟩ : ↥A) : MulAut L') := by
    rw [hσ ((ggKGTm_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd f : ↥A))
      ((ggKGTm_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd f : ↥A).2)]
    refine ggKGTm_eq_of_diag_const (hd := hd) hφs (t := t ∘ ⇑σ.symm) ?_ ht' (c := c * c'⁻¹) ?_
    · have hpc : NbrInnerWeylA.permConj φ σ = MulAut.conj (φ (permSL σ.symm)) := rfl
      rw [hpc]
      exact ht.conj_perm σ.symm
    · intro k
      have hc'0 : c' ≠ 0 := by
        intro h0
        have h2 := ht'.ne_zero k
        rw [hc' k, h0, zero_mul] at h2
        exact h2 rfl
      change t (σ.symm k) = (c * c'⁻¹) * t' k
      rw [hc (σ.symm k), hc' k, ggKGTm_uvec_permAut]
      simp only [Function.comp_apply]
      rw [show ⇑σ.symm = ⇑(σ⁻¹ : Equiv.Perm (Fin d)) from rfl]
      field_simp [hc'0]
  apply Subtype.ext
  rw [ggConjAut_apply]
  exact heq

theorem ggKGTAD_permModel {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d) {L' : Type} [Group L'] [Finite L']
    {φ : SpecialLinearGroup (Fin d) K →* L'} (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hr : p ^ (d - 2) ≤ Nat.card A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ a t) :
    ∃ (S : Subgroup (Fin d → Multiplicative (ZMod p))) (Θ : ↥S →* ↥A),
      (S = ⊤ ∨ S = sumZero d p) ∧ Function.Surjective Θ ∧
      (∀ f : ↥S, Θ f = 1 ↔
        ∃ c : Multiplicative (ZMod p), (f : Fin d → Multiplicative (ZMod p)) = fun _ => c) ∧
      ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ∃ π : Equiv.Perm (Fin d), ∀ f g : ↥S,
          (g : Fin d → Multiplicative (ZMod p)) = permAut π (f : Fin d → Multiplicative (ZMod p)) →
            ggConjAut A hn (Θ f) = Θ g := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hd0 : 0 < d := by omega
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (K := K) hp hpK
  let u : Kˣ := Units.mk0 ζ (hζ.ne_zero hp.ne_zero)
  have hu : u ^ p = 1 := by
    ext
    simp only [u, Units.val_pow_eq_pow_val, Units.val_one, Units.mk0_val]
    exact hζ.pow_eq_one
  have hζu : IsPrimitiveRoot u p := IsPrimitiveRoot.coe_units_iff.mp hζ
  have hord : orderOf u = p := hζu.eq_orderOf.symm
  have hζuK : IsPrimitiveRoot (u : K) p := IsPrimitiveRoot.coe_units_iff.mpr hζu
  let S := ggKGTm_S φ A u hu
  let Θ := ggKGTm_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd0
  have hsurj : Function.Surjective Θ :=
    ggKGTm_Θ_surjective hφs hφker hA.2 hdiag hζuK hd0
  have hker : ∀ f : ↥S, Θ f = 1 ↔
      ∃ c : Multiplicative (ZMod p), (f : Fin d → Multiplicative (ZMod p)) = fun _ => c :=
    fun f => ggKGTm_Θ_eq_one_iff hφs hφker hord hd0 f
  have hSge : p ^ (d - 1) ≤ Nat.card ↥S := by
    have hcard : Nat.card ↥S = p * Nat.card ↥A :=
      ggKGTm_card_S hφs hsurj (ggKGTm_ker_eq hφs hφker hord hd0) (ggKGTm_const_le_S hd0)
    rw [hcard]
    calc p ^ (d - 1) = p * p ^ (d - 2) := by
          rw [mul_comm, ← pow_succ]
          congr 1
          omega
      _ ≤ p * Nat.card ↥A := Nat.mul_le_mul_left _ hr
  have hS_or : S = ⊤ ∨ S = sumZero d p :=
    ggKGTm_S_eq_top_or_sumZero hp hd hord ⟨ζ, hζ⟩
      (fun σ {f} hf => ggKGTm_permAut_mem_S hφs hφker hA.2 hsc hdiag σ hf) hSge
  refine ⟨S, Θ, hS_or, hsurj, hker, ?_⟩
  intro n hn
  obtain ⟨π, hπ⟩ := ggKGTm_ggConjAut_eq hp hp2 hpK hφs hφker hA hsc hdiag hd0 hn
  exact ⟨π, hπ⟩

end TypeA

end CFSG.StandardType

end
