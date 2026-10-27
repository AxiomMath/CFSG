module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelMono

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace LinModel

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]
  {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem pow_val_injective {p : ℕ} [NeZero p] {ω : Fˣ} (hω : IsPrimitiveRoot ω p) {a b : ZMod p}
    (h : ω ^ a.val = ω ^ b.val) : a = b :=
  ZMod.val_injective p (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h)

theorem pow_val_sub {p : ℕ} [NeZero p] {ω : Fˣ} (hω : ω ^ p = 1) (a b : ZMod p) :
    ω ^ (a - b).val = ω ^ a.val * (ω ^ b.val)⁻¹ := by
  have h := pow_val_add hω (a - b) b
  rw [sub_add_cancel] at h
  rw [h, mul_inv_cancel_right]

theorem exists_eq_pow_val {p : ℕ} [NeZero p] {ω : Fˣ} (hω : IsPrimitiveRoot ω p) {x : Fˣ}
    (hx : x ^ p = 1) : ∃ a : ZMod p, x = ω ^ a.val := by
  have hω' : IsPrimitiveRoot (ω : F) p := IsPrimitiveRoot.coe_units_iff.mpr hω
  obtain ⟨i, hip, hi⟩ := hω'.eq_pow_of_pow_eq_one (ξ := (x : F))
    (by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one])
  refine ⟨(i : ZMod p), Units.ext ?_⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hip, Units.val_pow_eq_pow_val, hi]

theorem exists_expo {p : ℕ} [NeZero p] {ω : Fˣ} (hω : IsPrimitiveRoot ω p) {g : G}
    (hg : g ∈ rootTorus p ψ) : ∃ a : Fin (m + 1) → ZMod p,
      (g, InnerDiagA.diagGL (fun i => ω ^ (a i).val)) ∈ LinFusion.ggInducedPairs ψ := by
  obtain ⟨d, hd, hgd⟩ := hg
  choose a ha using fun i => exists_eq_pow_val hω (hd i)
  refine ⟨a, ?_⟩
  have : (fun i => ω ^ (a i).val) = d := funext fun i => (ha i).symm
  rw [this]
  exact hgd

open Classical in
@[expose] noncomputable def expo (p : ℕ) [NeZero p] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    {ω : Fˣ} (hω : IsPrimitiveRoot ω p) (g : G) : Fin (m + 1) → ZMod p :=
  if hg : g ∈ rootTorus p ψ then (exists_expo hω hg).choose else 0

theorem expo_spec {p : ℕ} [NeZero p] {ω : Fˣ} (hω : IsPrimitiveRoot ω p) {g : G}
    (hg : g ∈ rootTorus p ψ) :
    (g, InnerDiagA.diagGL (fun i => ω ^ (expo p ψ hω g i).val)) ∈ LinFusion.ggInducedPairs ψ := by
  classical
  have h := (exists_expo hω hg).choose_spec
  simp only [expo, hg, ↓reduceDIte]
  exact h

theorem exists_const_of_mem_ggInducedPairs [CharP F 2] {p : ℕ} [NeZero p]
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {ω : Fˣ} (hω : IsPrimitiveRoot ω p) {g : G} {a b : Fin (m + 1) → ZMod p}
    (ha : (g, InnerDiagA.diagGL (fun i => ω ^ (a i).val)) ∈ LinFusion.ggInducedPairs ψ)
    (hb : (g, InnerDiagA.diagGL (fun i => ω ^ (b i).val)) ∈ LinFusion.ggInducedPairs ψ) :
    ∃ c : ZMod p, ∀ i, b i = a i + c := by
  obtain ⟨κ, hκ⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker ha hb
  rw [scalar_mul_diagGL] at hκ
  have hent : ∀ i, ω ^ (b i).val = κ * ω ^ (a i).val := fun i =>
    congrFun (diagGL_injective hκ) i
  refine ⟨b 0 - a 0, fun i => ?_⟩
  apply pow_val_injective hω
  rw [pow_val_add hω.pow_eq_one, pow_val_sub hω.pow_eq_one, hent i, hent 0]
  group
  exact mul_comm _ _

theorem inv_mul_diagGL_mul {A : GL (Fin (m + 1)) F} {π : Equiv.Perm (Fin (m + 1))}
    (hA : IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) π) (x : Fin (m + 1) → Fˣ) :
    A⁻¹ * InnerDiagA.diagGL x * A = InnerDiagA.diagGL (x ∘ π) := by
  have h : InnerDiagA.diagGL x * A = A * InnerDiagA.diagGL (x ∘ π) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL]
    ext l i
    rw [diagonal_mul, mul_diagonal, Function.comp_apply]
    by_cases hl : l = π i
    · rw [hl, mul_comm]
    · have h0 : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) l i = 0 := by
        by_contra h0
        exact hl ((hA i l).mp h0)
      rw [h0, mul_zero, zero_mul]
  rw [mul_assoc, h, inv_mul_cancel_left]

theorem isPermOf_one : IsPermOf (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) 1 := by
  intro i l
  rw [Matrix.one_apply, Equiv.Perm.one_apply]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => one_ne_zero⟩
  · exact ⟨fun h' => absurd rfl h', fun h' => absurd h' h⟩

theorem IsPermOf.pow {A : Matrix (Fin (m + 1)) (Fin (m + 1)) F} {π : Equiv.Perm (Fin (m + 1))}
    (hA : IsPermOf A π) (n : ℕ) : IsPermOf (A ^ n) (π ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact isPermOf_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hA

theorem isCycle_of_isPermOf [CharP F 2] {p : ℕ} (hp : p.Prime) (hmp : m + 1 = p)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBs : rootTorus p ψ = Bs) {z : G} (hzC : z ∉ Subgroup.centralizer (Bs : Set G))
    (hzp : z ^ p = 1) {A : GL (Fin (m + 1)) F} (hA : (z, A) ∈ LinFusion.ggInducedPairs ψ)
    {π : Equiv.Perm (Fin (m + 1))} (hπ : IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) π) :
    π.IsCycle ∧ π.support = Finset.univ ∧ π ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hπ1 : π ≠ 1 := by
    rintro rfl
    obtain ⟨d, hd⟩ := IsPermOf.exists_eq_diagGL hπ
    rw [hd] at hA
    apply hzC
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hBs] at hb
    obtain ⟨e, -, hbe⟩ := hb
    exact mul_comm_of_mem_diag hC hbe hA
  have hπp : π ^ p = 1 := by
    have h1 := (LinFusion.ggInducedPairs ψ).pow_mem hA p
    rw [Prod.pow_mk, hzp] at h1
    obtain ⟨c, hc⟩ := LinTorus.exists_scalar_of_mem_ggInducedPairs_one hker h1
    have h2 := hπ.pow p
    rw [← Units.val_pow_eq_pow_val, hc] at h2
    have h3 : IsPermOf ((GeneralLinearGroup.scalar (Fin (m + 1)) c : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) 1 := by
      have := IsPermOf.scalar_mul (A := (1 : GL (Fin (m + 1)) F))
        (by rw [Units.val_one]; exact isPermOf_one) c
      rwa [mul_one] at this
    exact h2.unique h3
  have hord : orderOf π = p := orderOf_eq_prime hπp hπ1
  have hcyc : π.IsCycle := Equiv.Perm.isCycle_of_prime_order' (by rw [hord]; exact hp)
    (by rw [Fintype.card_fin, hord, hmp]; omega)
  refine ⟨hcyc, ?_, hπp⟩
  apply Finset.eq_univ_of_card
  rw [← hcyc.orderOf, hord, Fintype.card_fin, hmp]

@[expose] def cycleIdx {p : ℕ} (π : Equiv.Perm (Fin (m + 1))) (j : ZMod p) : Fin (m + 1) :=
  (π ^ j.val) 0

theorem cycleIdx_succ {p : ℕ} [Fact p.Prime] {π : Equiv.Perm (Fin (m + 1))} (hπp : π ^ p = 1)
    (j : ZMod p) : cycleIdx π (j + 1) = π (cycleIdx π j) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  unfold cycleIdx
  rw [ZMod.val_add, ZMod.val_one]
  have h : π ^ ((j.val + 1) % p) = π ^ (j.val + 1) := by
    conv_rhs => rw [← Nat.div_add_mod (j.val + 1) p, pow_add, pow_mul, hπp, one_pow, one_mul]
  rw [h, pow_succ', Equiv.Perm.mul_apply]

theorem cycleIdx_bijective {p : ℕ} [Fact p.Prime] (hmp : m + 1 = p)
    {π : Equiv.Perm (Fin (m + 1))} (hcyc : π.IsCycle) (hsupp : π.support = Finset.univ)
    (hπp : π ^ p = 1) : Function.Bijective (cycleIdx (p := p) π) := by
  have hsurj : Function.Surjective (cycleIdx (p := p) π) := by
    intro y
    have h0 : π 0 ≠ 0 := Equiv.Perm.mem_support.mp (by rw [hsupp]; exact Finset.mem_univ _)
    have hy : π y ≠ y := Equiv.Perm.mem_support.mp (by rw [hsupp]; exact Finset.mem_univ _)
    obtain ⟨i, hi⟩ := hcyc.exists_pow_eq h0 hy
    refine ⟨(i : ZMod p), ?_⟩
    unfold cycleIdx
    rw [ZMod.val_natCast, ← hi]
    congr 1
    conv_rhs => rw [← Nat.div_add_mod i p, pow_add, pow_mul, hπp, one_pow, one_mul]
  refine (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, ?_⟩
  rw [ZMod.card, Fintype.card_fin, hmp]

end LinModel

@[expose] def GGLinearRegularConjInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m f : ℕ)
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G), 2 ≤ m →
    ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) →
    Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    ∀ (z : G) (A : GL (Fin (m + 1)) (GaloisField 2 f)) (π : Equiv.Perm (Fin (m + 1))),
      (z, A) ∈ LinFusion.ggInducedPairs ψ →
      LinModel.IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) π →
      π.IsCycle → π.support = Finset.univ →
      ∀ g ∈ Subgroup.normalizer (ψ.range : Set G), ∀ d : Fin (m + 1) → (GaloisField 2 f)ˣ,
        (g⁻¹ * z * g, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ → Function.Injective d

@[expose] def GGLinearTypeAkTripleInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m f : ℕ)
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G),
    ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) →
    Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    ∀ (b : G) (d : Fin (m + 1) → (GaloisField 2 f)ˣ),
      (b, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ →
      ∀ g ∈ Subgroup.normalizer (ψ.range : Set G), ∀ K : Subgroup G,
        IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {g * b * g⁻¹}) → GGTypeAk f K →
          ∃ j₁ j₂ j₃ : Fin (m + 1), j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ ∧ d j₁ = d j₂ ∧ d j₁ = d j₃

namespace LinModel

variable {m : ℕ} {G : Type} [Group G]

theorem torusCoords_of_inputs (h4 : GGLinearRegularConjInput) (h5 : GGLinearTypeAkTripleInput)
    [Finite G] {p f : ℕ} (hp : p.Prime) (hmp : m + 1 = p) (hm : 2 ≤ m)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {ω : (GaloisField 2 f)ˣ}
    (hω : IsPrimitiveRoot ω p) {Bs : Subgroup G} (hBs : rootTorus p ψ = Bs)
    (hmat : ∀ u ∈ Subgroup.normalizer (Bs : Set G), (∃ k, u ^ (p ^ k) = 1) →
      ∃ A : GL (Fin (m + 1)) (GaloisField 2 f), (u, A) ∈ LinFusion.ggInducedPairs ψ)
    (hmono : ∀ u ∈ Subgroup.normalizer (Bs : Set G), ∀ A : GL (Fin (m + 1)) (GaloisField 2 f),
      (u, A) ∈ LinFusion.ggInducedPairs ψ → ∃ π,
        IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) π)
    {z : G} (hzN : z ∈ Subgroup.normalizer (Bs : Set G))
    (hzC : z ∉ Subgroup.centralizer (Bs : Set G)) (hzp : z ^ p = 1) :
    ∃ v : G → ZMod p → ZMod p, GGTorusCoords p Bs ψ.range f z v := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨A, hA⟩ := hmat z hzN ⟨1, by rw [pow_one]; exact hzp⟩
  obtain ⟨π, hπ⟩ := hmono z hzN A hA
  obtain ⟨hcyc, hsupp, hπp⟩ := isCycle_of_isPermOf hp hmp hker hC hBs hzC hzp hA hπ
  have hbij := cycleIdx_bijective (p := p) hmp hcyc hsupp hπp
  set ι : ZMod p → Fin (m + 1) := cycleIdx π with hιdef
  set e := expo p ψ hω with hedef
  have hespec : ∀ g ∈ Bs, (g, InnerDiagA.diagGL (fun i => ω ^ (e g i).val)) ∈
      LinFusion.ggInducedPairs ψ := fun g hg => expo_spec hω (by rw [hBs]; exact hg)
  refine ⟨fun g j => e g (ι j), ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a ha b hb
    have h1 := (LinFusion.ggInducedPairs ψ).mul_mem (hespec a ha) (hespec b hb)
    rw [Prod.mk_mul_mk, ← LinFusion.diagGL_mul] at h1
    have h2 : ((fun i => ω ^ (e a i).val) * fun i => ω ^ (e b i).val) =
        fun i => ω ^ ((e a + e b) i).val := funext fun i => by
      rw [Pi.mul_apply, Pi.add_apply, pow_val_add hω.pow_eq_one]
    rw [h2] at h1
    obtain ⟨c, hc⟩ := exists_const_of_mem_ggInducedPairs hker hω h1
      (hespec _ (Bs.mul_mem ha hb))
    exact ⟨c, fun j => by
      show e (a * b) (ι j) = e a (ι j) + e b (ι j) + c
      rw [hc (ι j), Pi.add_apply]⟩
  ·
    rintro a ha ⟨c, hc⟩
    have hconst : ∀ i, e a i = c := fun i => by
      obtain ⟨j, rfl⟩ := hbij.2 i
      exact hc j
    have h1 := hespec a ha
    have h2 : InnerDiagA.diagGL (fun i => ω ^ (e a i).val) =
        GeneralLinearGroup.scalar (Fin (m + 1)) (ω ^ c.val) := by
      apply Units.ext
      rw [InnerDiagA.coe_diagGL, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      congr 1
      funext i
      rw [hconst i]
    rw [h2] at h1
    have h3 := scalar_mul_mem_ggInducedPairs h1 (ω ^ c.val)⁻¹
    rw [← map_mul, inv_mul_cancel, map_one] at h3
    have h4 := LinFusion.mem_centralizer_of_mem_ggInducedPairs_one h3
    rwa [hC, Subgroup.mem_bot] at h4
  ·
    intro a ha
    have hza : z⁻¹ * a * z ∈ Bs := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hzN) a).mp ha
      rwa [inv_inv] at this
    have h1 := (LinFusion.ggInducedPairs ψ).mul_mem
      ((LinFusion.ggInducedPairs ψ).mul_mem ((LinFusion.ggInducedPairs ψ).inv_mem hA)
        (hespec a ha)) hA
    rw [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, inv_mul_diagGL_mul hπ] at h1
    obtain ⟨c, hc⟩ := exists_const_of_mem_ggInducedPairs hker hω
      (a := fun i => e a (π i)) h1 (hespec _ hza)
    refine ⟨c, fun j => ?_⟩
    show e (z⁻¹ * a * z) (ι j) = e a (ι (j + 1)) + c
    have hc' := hc (ι j)
    dsimp only at hc'
    rw [hc', hιdef, cycleIdx_succ hπp]
  ·
    intro z' hz'N hz'C hz'p g hg hgz
    obtain ⟨A', hA'⟩ := hmat z' hz'N ⟨1, by rw [pow_one]; exact hz'p⟩
    obtain ⟨π', hπ'⟩ := hmono z' hz'N A' hA'
    obtain ⟨hcyc', hsupp', -⟩ := isCycle_of_isPermOf hp hmp hker hC hBs hz'C hz'p hA' hπ'
    have hinj := h4 G m f ψ hm hker hC z' A' π' hA' hπ' hcyc' hsupp' g hg _ (hespec _ hgz)
    intro j₁ j₂ hj
    apply hbij.1
    have h1 : ω ^ (e (g⁻¹ * z' * g) (ι j₁)).val = ω ^ (e (g⁻¹ * z' * g) (ι j₂)).val := by
      simp only at hj
      rw [hj]
    exact hinj h1
  ·
    rintro a ha g hg ⟨K, hK, hKA⟩
    obtain ⟨j₁, j₂, j₃, h12, h13, h23, e12, e13⟩ := h5 G m f ψ hker hC a _ (hespec a ha) g hg K hK
      hKA
    obtain ⟨k₁, rfl⟩ := hbij.2 j₁
    obtain ⟨k₂, rfl⟩ := hbij.2 j₂
    obtain ⟨k₃, rfl⟩ := hbij.2 j₃
    refine ⟨k₁, k₂, k₃, fun h => h12 (by rw [h]), fun h => h13 (by rw [h]),
      fun h => h23 (by rw [h]), pow_val_injective hω e12, pow_val_injective hω e13⟩

end LinModel

end CFSG.StandardType
