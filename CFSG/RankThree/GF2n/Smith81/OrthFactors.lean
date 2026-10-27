module

public import CFSG.RankThree.GF2n.Smith81.OrthE2Natural
public import CFSG.RankThree.GF2n.Smith81.OrthNormalFactor
public import CFSG.RankThree.GF2n.Smith81.OrthTensorAlg
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped Matrix

section Abstract

variable {H A B : Type*} [Group H] [Group A] [Group B]

theorem normal_eq_of_card_eq_card [Finite A] [Finite B] [IsSimpleGroup B]
    (hB : ∃ b c : B, b * c ≠ c * b) (hlt : Nat.card A < Nat.card B) (e : H ≃* A × B)
    {N N' : Subgroup H} (hN : N.Normal) (hN' : N'.Normal) (hc : Nat.card N = Nat.card A)
    (hc' : Nat.card N' = Nat.card A) : N = N' := by
  have key : ∀ {P : Subgroup H}, P.Normal → Nat.card P = Nat.card A →
      P.map e.toMonoidHom = (MonoidHom.inl A B).range := by
    intro P hP hPc
    refine normal_eq_range_inl hB hlt (Subgroup.Normal.map hP e.toMonoidHom e.surjective) ?_
    rw [Subgroup.card_map_of_injective e.injective, hPc]
  exact Subgroup.map_injective e.injective ((key hN hc).trans (key hN' hc').symm)

theorem exists_noncomm_of_simple_of_sixteen_dvd {X : Type*} [Group X] [IsSimpleGroup X]
    (h16 : 16 ∣ Nat.card X) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative X := ⟨⟨fun a b => hcon a b⟩⟩
  have hp : (Nat.card X).Prime := Group.is_simple_iff_prime_card.mp inferInstance
  have h1 := (Nat.dvd_prime hp).mp h16
  rcases h1 with h1 | h1
  · omega
  · rw [← h1] at hp
    exact absurd hp (by norm_num)

theorem factor_facts_of_equiv {A B X : Type*} [Group A] [Group B] [Group X] [IsSimpleGroup X]
    (h16 : 16 ∣ Nat.card X) (hlt : Nat.card A < Nat.card X) (eB : B ≃* X) :
    IsSimpleGroup B ∧ (∃ a b : B, a * b ≠ b * a) ∧ Nat.card A < Nat.card B := by
  refine ⟨eB.isSimpleGroup, ?_, by rwa [Nat.card_congr eB.toEquiv]⟩
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_simple_of_sixteen_dvd h16
  refine ⟨eB.symm a, eB.symm b, fun h => hab ?_⟩
  have := congrArg eB h
  simpa using this

end Abstract

section Tensor

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}

theorem actsAsTensor_id_mul {s s' : G} {g g' : Matrix (Fin 2) (Fin 2) K}
    (hs' : ∀ x ∈ Q, s' * x * s'⁻¹ ∈ Q) (h : ActsAsTensor Q Z M₀ φ s g id)
    (h' : ActsAsTensor Q Z M₀ φ s' g' id) : ActsAsTensor Q Z M₀ φ (s * s') (g * g') id :=
  ActsAsTensor.mul (o := LinearMap.id) (o' := LinearMap.id) hs' h h'

theorem actsAsTensor_id_inv {s : G} {g g' : Matrix (Fin 2) (Fin 2) K}
    (hs' : ∀ x ∈ Q, s⁻¹ * x * s ∈ Q) (h : ActsAsTensor Q Z M₀ φ s g id) (hg : g * g' = 1) :
    ActsAsTensor Q Z M₀ φ s⁻¹ g' id :=
  ActsAsTensor.inv (o := LinearEquiv.refl K (ι → K)) hs' h hg

variable [Finite G] {M : Subgroup G}

theorem mem_Q_of_actsAsTensor_one (H : StrothHyp M Q Z) {s : G} (hs : s ∈ M)
    (h : ActsAsTensor Q Z M₀ φ s 1 id) : s ∈ Q := by
  refine mem_Q_of_pi_conj_eq (M₀ := M₀) H hs fun x hx => φ.injective ?_
  rw [h x hx, orthTensor_one_id]

theorem inv_mul_mem_Q_of_actsAsTensor (H : StrothHyp M Q Z) {s₁ s₂ : G} (h₁ : s₁ ∈ M)
    (h₂ : s₂ ∈ M) {g g' : Matrix (Fin 2) (Fin 2) K} (hgg : g * g' = 1)
    (hs₁ : ActsAsTensor Q Z M₀ φ s₁ g id) (hs₂ : ActsAsTensor Q Z M₀ φ s₂ g id) :
    s₁⁻¹ * s₂ ∈ Q := by
  have hQM : ∀ y ∈ M, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 hy) x).mp hx
  have hi : ActsAsTensor Q Z M₀ φ s₁⁻¹ g' id :=
    actsAsTensor_id_inv (fun x hx => by simpa using hQM s₁⁻¹ (M.inv_mem h₁) x hx) hs₁ hgg
  have hm := actsAsTensor_id_mul (hQM s₂ h₂) hi hs₂
  rw [mul_eq_one_comm.mp hgg] at hm
  exact mem_Q_of_actsAsTensor_one H (M.mul_mem (M.inv_mem h₁) h₂) hm

end Tensor

section Normalizer

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {ι : Type} [Fintype ι] [DecidableEq ι] {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}

theorem conj_mem_slPart_of_quotient (hH : StrothHyp M Q Z) {L : Subgroup G} (hLM : L ≤ M)
    (hnorm : ∀ x ∈ M, ∀ l ∈ L, x * l * x⁻¹ ∈ L) [Nonempty ι] {qU : QuadraticForm K (ι → K)}
    (hAct : OrthAct Q Z M₀ qU φ L) [hN : (Q.subgroupOf L).Normal]
    {A B : Type} [Group A] [Group B] [IsSimpleGroup B]
    (hB : ∃ b c : B, b * c ≠ c * b) (hlt : Nat.card A < Nat.card B)
    (hA : Nat.card A = Nat.card K * (Nat.card K ^ 2 - 1))
    (e : (↥L ⧸ Q.subgroupOf L) ≃* A × B) {s : G} (hs : s ∈ L)
    {g : Matrix (Fin 2) (Fin 2) K} (hg : g.det = 1) (hsg : ActsAsTensor Q Z M₀ φ s g id)
    {x : G} (hx : x ∈ M) :
    ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧ ActsAsTensor Q Z M₀ φ (x * s * x⁻¹) g' id := by
  classical
  haveI : Finite (A × B) := Finite.of_equiv _ e.toEquiv
  haveI : Finite A := Finite.prod_left B
  haveI : Finite B := Finite.prod_right A
  have hQM : ∀ y ∈ M, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := fun y hy q hq =>
    (Subgroup.mem_normalizer_iff.mp (hH.Q_normal.2 hy) q).mp hq
  choose sel hselL hsel using fun δ : Matrix.SpecialLinearGroup (Fin 2) K =>
    hAct.sl (δ : Matrix (Fin 2) (Fin 2) K) δ.2
  have hselM : ∀ δ, sel δ ∈ M := fun δ => hLM (hselL δ)
  have hδinv : ∀ δ : Matrix.SpecialLinearGroup (Fin 2) K,
      (δ : Matrix (Fin 2) (Fin 2) K) *
        ((δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 :=
    fun δ => by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hmk : ∀ (l : ↥L) (δ : Matrix.SpecialLinearGroup (Fin 2) K),
      ActsAsTensor Q Z M₀ φ (l : G) (δ : Matrix (Fin 2) (Fin 2) K) id →
      (QuotientGroup.mk l : ↥L ⧸ Q.subgroupOf L) = QuotientGroup.mk ⟨sel δ, hselL δ⟩ := by
    intro l δ hl
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact inv_mul_mem_Q_of_actsAsTensor hH (hLM l.2) (hselM δ) (hδinv δ) hl (hsel δ)
  let ψ : Matrix.SpecialLinearGroup (Fin 2) K →* (↥L ⧸ Q.subgroupOf L) :=
    MonoidHom.mk' (fun δ => QuotientGroup.mk ⟨sel δ, hselL δ⟩) fun δ δ' => by
      rw [← QuotientGroup.mk_mul]
      refine (hmk (⟨sel δ, hselL δ⟩ * ⟨sel δ', hselL δ'⟩) (δ * δ') ?_).symm
      rw [Matrix.SpecialLinearGroup.coe_mul]
      exact actsAsTensor_id_mul (hQM _ (hselM δ')) (hsel δ) (hsel δ')
  have hψ : ∀ δ, ψ δ = QuotientGroup.mk ⟨sel δ, hselL δ⟩ := fun _ => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro δ hδ
    have hδQ : sel δ ∈ Q := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hδ)
    have h2 := (hsel δ).orthTensor_eq (ActsAsTensor.of_mem (φ := φ) (M₀ := M₀) hδQ)
    obtain ⟨κ, -, hκ, hκv⟩ := exists_scalar_of_orthTensor_eq_self (ι := ι) (K := K)
      (δ : Matrix (Fin 2) (Fin 2) K) LinearMap.id
      (fun p => (h2 p).trans (orthTensor_one_id p))
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hκ1 : κ = 1 := by
      have := congrFun (hκv (fun _ => (1 : K))) i
      simpa using this
    apply Matrix.SpecialLinearGroup.ext
    intro a b
    simp [hκ, hκ1]
  have hnormψ : (ψ.range).Normal := by
    refine ⟨fun a ha h => ?_⟩
    obtain ⟨δ, rfl⟩ := ha
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective h
    obtain ⟨g', o, hdet, -, hl⟩ := hAct.act (l : G) l.2
    let γ₁ : Matrix.SpecialLinearGroup (Fin 2) K := ⟨g', hdet⟩
    have h1 := ActsAsTensor.mul (o := (o : (ι → K) →ₗ[K] (ι → K))) (o' := LinearMap.id)
      (hQM (sel δ) (hselM δ)) hl (hsel δ)
    have h2 := ActsAsTensor.inv (o := o) (s := (l : G))
      (g' := ((γ₁⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      (fun y hy => by simpa using hQM (l : G)⁻¹ (M.inv_mem (hLM l.2)) y hy) hl (hδinv γ₁)
    have h3 := ActsAsTensor.mul (o := (o : (ι → K) →ₗ[K] (ι → K)) ∘ₗ LinearMap.id)
      (o' := (o.symm : (ι → K) →ₗ[K] (ι → K)))
      (hQM ((l : G)⁻¹) (M.inv_mem (hLM l.2))) h1 h2
    have hfun : ⇑(((o : (ι → K) →ₗ[K] (ι → K)) ∘ₗ LinearMap.id) ∘ₗ
        (o.symm : (ι → K) →ₗ[K] (ι → K))) = id := by
      funext v
      simp
    rw [hfun] at h3
    have h4 : ActsAsTensor Q Z M₀ φ ((l : G) * sel δ * (l : G)⁻¹)
        ((γ₁ * δ * γ₁⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) id := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact h3
    have hmem : (QuotientGroup.mk l : ↥L ⧸ Q.subgroupOf L) * ψ δ * (QuotientGroup.mk l)⁻¹ =
        ψ (γ₁ * δ * γ₁⁻¹) := by
      rw [hψ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact hmk (l * ⟨sel δ, hselL δ⟩ * l⁻¹) (γ₁ * δ * γ₁⁻¹) h4
    exact ⟨γ₁ * δ * γ₁⁻¹, hmem.symm⟩
  have hcardH₁ : Nat.card ψ.range = Nat.card A := by
    rw [hA, ← CFSG.Open.StatedAPI.card_statedSL_two K, CFSG.Open.StatedAPI.card_statedSL,
      Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
  obtain ⟨cx, hcx⟩ : ∃ cx : ↥L ≃* ↥L, ∀ l : ↥L, ((cx l : ↥L) : G) = x * l * x⁻¹ := by
    refine ⟨{ toFun := fun l => ⟨x * l * x⁻¹, hnorm x hx l l.2⟩
              invFun := fun l => ⟨x⁻¹ * l * x, by simpa using hnorm x⁻¹ (M.inv_mem hx) l l.2⟩
              left_inv := fun l => Subtype.ext (by
                show x⁻¹ * (x * (l : G) * x⁻¹) * x = l
                group)
              right_inv := fun l => Subtype.ext (by
                show x * (x⁻¹ * (l : G) * x) * x⁻¹ = l
                group)
              map_mul' := fun a b => Subtype.ext (by
                show x * ((a : G) * (b : G)) * x⁻¹ = x * (a : G) * x⁻¹ * (x * (b : G) * x⁻¹)
                group) }, fun l => rfl⟩
  have hmapN : (Q.subgroupOf L).map cx.toMonoidHom = Q.subgroupOf L := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hz
      rw [Subgroup.mem_subgroupOf]
      show ((cx z : ↥L) : G) ∈ Q
      rw [hcx]
      exact hQM x hx _ hz
    · intro hy
      refine ⟨cx.symm y, ?_, cx.apply_symm_apply y⟩
      rw [Subgroup.mem_subgroupOf] at hy
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have h1 : ((cx.symm y : ↥L) : G) = x⁻¹ * (y : G) * x := by
        have := hcx (cx.symm y)
        rw [cx.apply_symm_apply] at this
        rw [this]
        group
      rw [h1]
      simpa using hQM x⁻¹ (M.inv_mem hx) _ hy
  let f : (↥L ⧸ Q.subgroupOf L) ≃* (↥L ⧸ Q.subgroupOf L) :=
    QuotientGroup.congr (Q.subgroupOf L) (Q.subgroupOf L) cx hmapN
  have hH₂N : (ψ.range.map f.toMonoidHom).Normal :=
    Subgroup.Normal.map hnormψ f.toMonoidHom f.surjective
  have hH₂card : Nat.card (ψ.range.map f.toMonoidHom) = Nat.card A := by
    rw [Subgroup.card_map_of_injective (f := f.toMonoidHom) f.injective, hcardH₁]
  have hH₂eq : ψ.range.map f.toMonoidHom = ψ.range :=
    normal_eq_of_card_eq_card hB hlt e hH₂N hnormψ hH₂card hcardH₁
  let δ₀ : Matrix.SpecialLinearGroup (Fin 2) K := ⟨g, hg⟩
  have hs0 : (QuotientGroup.mk (⟨s, hs⟩ : ↥L) : ↥L ⧸ Q.subgroupOf L) = ψ δ₀ :=
    hmk ⟨s, hs⟩ δ₀ hsg
  have hmem : f (ψ δ₀) ∈ ψ.range.map f.toMonoidHom := ⟨ψ δ₀, ⟨δ₀, rfl⟩, rfl⟩
  rw [hH₂eq] at hmem
  obtain ⟨δ₂, hδ₂⟩ := hmem
  have hq : (sel δ₂)⁻¹ * (x * s * x⁻¹) ∈ Q := by
    have h1 : (QuotientGroup.mk ⟨sel δ₂, hselL δ₂⟩ : ↥L ⧸ Q.subgroupOf L) =
        QuotientGroup.mk (cx ⟨s, hs⟩) := by
      rw [← hψ, hδ₂, ← hs0]
      rfl
    have h2 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hcx] at h2
    exact h2
  refine ⟨(δ₂ : Matrix (Fin 2) (Fin 2) K) * 1, by rw [mul_one]; exact δ₂.2, ?_⟩
  have hxs : x * s * x⁻¹ = sel δ₂ * ((sel δ₂)⁻¹ * (x * s * x⁻¹)) := by group
  rw [hxs]
  exact actsAsTensor_id_mul (fun y hy => Q.mul_mem (Q.mul_mem hq hy) (Q.inv_mem hq))
    (hsel δ₂) (ActsAsTensor.of_mem hq)

end Normalizer

section Order

open CFSG.Open

theorem card_statedSL_two_lt_omega_minus_of_two_le {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hm : 2 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hq : 4 ≤ Nat.card K) :
    Nat.card K * (Nat.card K ^ 2 - 1) < Nat.card ↥(StatedOmega (StatedQuadMinus m K b c)) := by
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | h3
  · have h := card_statedOmega_minus_eq_of_two_le (K := K) (m := 2) le_rfl hirr
    have hQ : (4 : ℤ) ≤ (Nat.card K : ℤ) := by exact_mod_cast hq
    have hsub : ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ 2 - 1 := by
      have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
      push_cast [Nat.cast_sub this]
      ring
    have h2 : ((Nat.card K * (Nat.card K ^ 2 - 1) : ℕ) : ℤ) <
        (Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) : ℤ) := by
      rw [h]
      push_cast [hsub]
      norm_num
      have hP : (0 : ℤ) < (Nat.card K : ℤ) ^ 2 - 1 := by nlinarith
      have hlt : (Nat.card K : ℤ) < (Nat.card K : ℤ) ^ 2 * ((Nat.card K : ℤ) ^ 2 + 1) := by
        nlinarith
      nlinarith [mul_lt_mul_of_pos_right hlt hP]
    exact_mod_cast h2
  · exact card_statedSL_two_lt_omega_minus h3 hirr hq

end Order

section Main

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem nonempty_index_of_card_Q {M Q Z : Subgroup G} (hH : StrothHyp M Q Z) {m : ℕ}
    (hm : 1 ≤ m) (hQcard : Nat.card Q = Nat.card Z ^ (4 * m + 1)) {K : Type} [Field K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι]
    {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)} : Nonempty ι := by
  by_contra hι
  rw [not_nonempty_iff] at hι
  have hq4 : 4 ≤ Nat.card Z := hH.q4
  obtain ⟨y, hyQ, hyZ⟩ : ∃ y ∈ Q, y ∉ Z := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card Q ≤ Nat.card Z := Subgroup.card_le_of_le hcon
    rw [hQcard] at h1
    have h2 : Nat.card Z ^ 1 < Nat.card Z ^ (4 * m + 1) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    rw [pow_one] at h2
    omega
  apply hyZ
  have h0 : φ (M₀.π y) = φ 0 := Subsingleton.elim _ _
  exact (M₀.π_ker y hyQ).mp (φ.injective h0)

theorem slPart_normal_of_split {M Q Z B : Subgroup G} (hcB : Ctx M Q Z B) {m : ℕ} (hm : 1 ≤ m)
    (hQcard : Nat.card Q = Nat.card Z ^ (4 * m + 1)) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {qU : QuadraticForm K (ι → K)} {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)))
    [hN : (Q.subgroupOf (Lgen M (LB M Q B))).Normal] {A B' : Type} [Group A] [Group B']
    [IsSimpleGroup B'] (hB : ∃ a b : B', a * b ≠ b * a) (hlt : Nat.card A < Nat.card B')
    (hA : Nat.card A = Nat.card K * (Nat.card K ^ 2 - 1))
    (e : (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) ≃* A × B') :
    ∀ s ∈ Lgen M (LB M Q B), ∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 →
      ActsAsTensor Q Z M₀ φ s g id → ∀ x ∈ M, ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧
        ActsAsTensor Q Z M₀ φ (x * s * x⁻¹) g' id := by
  haveI : Nonempty ι := nonempty_index_of_card_Q hcB.hyp hm hQcard (M₀ := M₀) (φ := φ)
  have hLM : Lgen M (LB M Q B) ≤ M := (Lgen_le_H0 hcB).trans inf_le_left
  have hnorm : ∀ x ∈ M, ∀ l ∈ Lgen M (LB M Q B), x * l * x⁻¹ ∈ Lgen M (LB M Q B) :=
    fun x hx l hl => (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M (LB M Q B) hx) l).mp hl
  intro s hs g hg hsg x hx
  exact conj_mem_slPart_of_quotient hcB.hyp hLM hnorm hAct hB hlt hA e hs hg hsg hx

theorem slPart_normal_plus {M Q Z B : Subgroup G} (hcB : Ctx M Q Z B) {t : G} {m : ℕ}
    (hm : 3 ≤ m) (hE : CaseE2Plus M Q Z B t m) {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) {ι : Type}
    [Fintype ι] [DecidableEq ι] {qU : QuadraticForm K (ι → K)}
    {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)} (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))) :
    ∀ s ∈ Lgen M (LB M Q B), ∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 →
      ActsAsTensor Q Z M₀ φ s g id → ∀ x ∈ M, ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧
        ActsAsTensor Q Z M₀ φ (x * s * x⁻¹) g' id := by
  have hq4 : 4 ≤ Nat.card Z := hcB.hyp.q4
  obtain ⟨jj, -, hZ2, -⟩ := hcB.hyp.cp
  have hKZ : Nat.card K = Nat.card Z := hD.card
  obtain ⟨-, hQcard, -, -, hNn, A, B', _, _, ⟨K', _, _, hK', ⟨eA⟩⟩, ⟨K'', _, _, hK'', ⟨eB⟩⟩,
    ⟨e⟩⟩ := hE
  haveI := hNn
  haveI : CharP K'' 2 := charP_two_of_card_eq_two_pow (hK''.trans hZ2)
  have hq4'' : 4 ≤ Nat.card K'' := by rw [hK'']; exact hq4
  obtain ⟨hsimp, h16, -⟩ := endg_omegaPlus_facts hq4'' hm
  haveI := hsimp
  have hAcard : Nat.card A = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [Nat.card_congr eA.toEquiv, StatedAPI.card_statedSL_two, hK', hKZ]
  have hlt' : Nat.card A < Nat.card ↥(StatedOmega (StatedQuadPlus m K'')) := by
    rw [hAcard, hKZ, ← hK'']
    exact card_statedSL_two_lt_omega_plus hm hq4''
  obtain ⟨hsB, hB, hlt⟩ := factor_facts_of_equiv h16 hlt' eB
  haveI := hsB
  exact slPart_normal_of_split hcB (by omega) hQcard hAct hB hlt hAcard e

theorem slPart_normal_minus {M Q Z B : Subgroup G} (hcB : Ctx M Q Z B) {t : G} {m : ℕ}
    (hE : CaseE2Minus M Q Z B t m) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) {ι : Type} [Fintype ι]
    [DecidableEq ι] {qU : QuadraticForm K (ι → K)} {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))) :
    ∀ s ∈ Lgen M (LB M Q B), ∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 →
      ActsAsTensor Q Z M₀ φ s g id → ∀ x ∈ M, ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧
        ActsAsTensor Q Z M₀ φ (x * s * x⁻¹) g' id := by
  have hq4 : 4 ≤ Nat.card Z := hcB.hyp.q4
  obtain ⟨jj, -, hZ2, -⟩ := hcB.hyp.cp
  have hKZ : Nat.card K = Nat.card Z := hD.card
  obtain ⟨hm, hQcard, -, -, hNn, A, B', _, _, ⟨K', _, _, hK', ⟨eA⟩⟩,
    ⟨K'', _, _, hK'', b, c, hirr, ⟨eB⟩⟩, ⟨e⟩⟩ := hE
  haveI := hNn
  haveI : CharP K'' 2 := charP_two_of_card_eq_two_pow (hK''.trans hZ2)
  have hq4'' : 4 ≤ Nat.card K'' := by rw [hK'']; exact hq4
  obtain ⟨hsimp, h16, -⟩ := endg_omegaMinus_facts hq4'' hm hirr
  haveI := hsimp
  have hAcard : Nat.card A = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [Nat.card_congr eA.toEquiv, StatedAPI.card_statedSL_two, hK', hKZ]
  have hlt' : Nat.card A < Nat.card ↥(StatedOmega (StatedQuadMinus m K'' b c)) := by
    rw [hAcard, hKZ, ← hK'']
    exact card_statedSL_two_lt_omega_minus_of_two_le hm hirr hq4''
  obtain ⟨hsB, hB, hlt⟩ := factor_facts_of_equiv h16 hlt' eB
  haveI := hsB
  exact slPart_normal_of_split hcB (by omega) hQcard hAct hB hlt hAcard e

theorem slPart_normal {M Q Z B : Subgroup G} (hcB : Ctx M Q Z B) {t : G} {m : ℕ} (hm : 3 ≤ m)
    (hE : CaseE2Plus M Q Z B t m ∨ CaseE2Minus M Q Z B t m) {K : Type} [Field K] [Finite K]
    [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    {ι : Type} [Fintype ι] [DecidableEq ι] {qU : QuadraticForm K (ι → K)}
    {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)} (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))) :
    ∀ s ∈ Lgen M (LB M Q B), ∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 →
      ActsAsTensor Q Z M₀ φ s g id → ∀ x ∈ M, ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧
        ActsAsTensor Q Z M₀ φ (x * s * x⁻¹) g' id :=
  hE.elim (fun hE => slPart_normal_plus hcB hm hE hD hAct)
    (fun hE => slPart_normal_minus hcB hE hD hAct)

end Main

end CFSG.RankThree.GF2n.Smith81
