module

public import CFSG.SignalizerFunctorTheorem.Quadratic.SL2
public import CFSG.SignalizerFunctorTheorem.Quadratic.Offenders

public section

namespace CFSG.SignalizerFunctorTheorem.Quadratic

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fact p.Prime] [Finite V]
  {H : Subgroup (LGL p V)}

section PairAux

theorem pairF_pow_eq_one {g : LGL p V} (hg : g ∈ Qp p H) (h : g ^ p = 1) : g = 1 := by
  have h4 : orderOf (⟨g, hg⟩ : Qp p H) ∣ Nat.card (Qp p H) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk g hg] at h4
  have h6 : orderOf g ∣ Nat.gcd p (Nat.card (Qp p H)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) h4
  rw [Nat.Coprime.gcd_eq_one (coprime_card_Qp H)] at h6
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h6)

theorem pairF_eq_one {g : LGL p V} (hg : g ∈ Qp p H) {W : Submodule (ZMod p) V}
    (h1 : ∀ w ∈ W, g w = w) (h2 : ∀ v : V, g v - v ∈ W) : g = 1 :=
  pairF_pow_eq_one hg (pow_eq_one_of_trivial h1 h2)

theorem pairF_conj_mem {h q : LGL p V} (hh : h ∈ H) (hq : q ∈ Qp p H) :
    h * q * h⁻¹ ∈ Qp p H :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_Qp (le_refl H) hh) q).mp hq

omit [Finite V] in
theorem pairF_mul_mem {U : Submodule (ZMod p) V} {g h : LGL p V} (hg : ∀ v, g v - v ∈ U)
    (hh : ∀ v, h v - v ∈ U) (v : V) : (g * h) v - v ∈ U := by
  have := U.add_mem (hg (h v)) (hh v)
  rwa [sub_add_sub_cancel] at this

omit [Finite V] in
theorem pairF_inv_mem {U : Submodule (ZMod p) V} {g : LGL p V} (hg : ∀ v, g v - v ∈ U)
    (v : V) : g⁻¹ v - v ∈ U := by
  have := U.neg_mem (hg (g⁻¹ v))
  rwa [apply_inv_apply', neg_sub] at this

omit [Finite V] in
theorem pairF_sup_mem {U : Submodule (ZMod p) V} {A₁ A₂ : Subgroup (LGL p V)}
    (h₁ : ∀ g ∈ A₁, ∀ v, g v - v ∈ U) (h₂ : ∀ g ∈ A₂, ∀ v, g v - v ∈ U) :
    ∀ g ∈ A₁ ⊔ A₂, ∀ v, g v - v ∈ U := by
  let T : Subgroup (LGL p V) :=
    { carrier := {g | ∀ v, g v - v ∈ U}
      mul_mem' := fun {g h} hg hh v => pairF_mul_mem hg hh v
      one_mem' := fun v => by simp
      inv_mem' := fun {g} hg v => pairF_inv_mem hg v }
  exact fun g hg => sup_le (show A₁ ≤ T from h₁) (show A₂ ≤ T from h₂) hg

omit [Finite V] in
theorem pairF_commSub_sup (A₁ A₂ : Subgroup (LGL p V)) :
    commSub (A₁ ⊔ A₂) = commSub A₁ ⊔ commSub A₂ := by
  refine le_antisymm ?_
    (sup_le (commSub_mono _ _ le_sup_left) (commSub_mono _ _ le_sup_right))
  rw [commSub_le_iff]
  exact pairF_sup_mem (fun g hg v => Submodule.mem_sup_left (sub_mem_commSub A₁ hg v))
    (fun g hg v => Submodule.mem_sup_right (sub_mem_commSub A₂ hg v))

theorem pairF_exists_span {L : Submodule (ZMod p) V} (h : Nat.card L = p) :
    ∃ w : V, w ≠ 0 ∧ L = Submodule.span (ZMod p) {w} := by
  have hfr : Module.finrank (ZMod p) L = 1 := by
    have h1 := card_eq_pow_finrank L
    rw [h] at h1
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (h1.symm.trans (pow_one p).symm)
  obtain ⟨⟨w, hwL⟩, hw0, hall⟩ := finrank_eq_one_iff'.mp hfr
  refine ⟨w, fun h0 => hw0 (Subtype.ext h0), le_antisymm ?_ ?_⟩
  · intro v hv
    obtain ⟨c, hc⟩ := hall ⟨v, hv⟩
    exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
  · exact (Submodule.span_singleton_le_iff_mem w L).mpr hwL

omit [Finite V] in
theorem pairF_commSub_cj_span {A : Subgroup (LGL p V)} {w : V} (g : LGL p V)
    (h : commSub A = Submodule.span (ZMod p) {w}) :
    commSub (cj g A) = Submodule.span (ZMod p) {g w} := by
  rw [commSub_cj, h, Submodule.map_span, Set.image_singleton]
  rfl

theorem pairF_tr {a₁ a₂ : LGL p V} (ha₁ : a₁ ∈ H) (hQ : a₂ * a₁⁻¹ ∈ Qp p H)
    (hp₁ : a₁ ^ p = 1) (hp₂ : a₂ ^ p = 1) {U : Submodule (ZMod p) V}
    (h₁ : ∀ v, a₁ v - v ∈ U) (h₂ : ∀ v, a₂ v - v ∈ U) (hfix : ∀ u ∈ U, a₁ u = u) :
    a₂ = a₁ := by
  have ha₂ : a₂ = a₂ * a₁⁻¹ * a₁ := (inv_mul_cancel_right a₂ a₁).symm
  have hgV : ∀ v, (a₂ * a₁⁻¹) v - v ∈ U := pairF_mul_mem h₂ (pairF_inv_mem h₁)
  generalize a₂ * a₁⁻¹ = g at hQ hgV ha₂
  have hcomm : g * (a₁ * g⁻¹ * a₁⁻¹) = 1 := by
    refine pairF_eq_one (W := U) (Subgroup.mul_mem _ hQ (pairF_conj_mem ha₁ (inv_mem hQ)))
      (fun u hu => ?_)
      (pairF_mul_mem hgV
        (pairF_mul_mem (pairF_mul_mem h₁ (pairF_inv_mem hgV)) (pairF_inv_mem h₁)))
    have hu2 : g⁻¹ u ∈ U := by
      have := U.add_mem hu (pairF_inv_mem hgV u)
      rwa [add_sub_cancel] at this
    change g (a₁ (g⁻¹ (a₁⁻¹ u))) = u
    rw [show a₁⁻¹ u = u from a₁.symm_apply_eq.mpr (hfix u hu).symm, hfix _ hu2,
      apply_inv_apply']
  have hcg : Commute g a₁ := by
    have : g * a₁ = g * (a₁ * g⁻¹ * a₁⁻¹) * (a₁ * g) := by group
    rw [hcomm, one_mul] at this
    exact this
  have hgp : g ^ p = 1 := by
    have h := hp₂
    rwa [ha₂, hcg.mul_pow, hp₁, mul_one] at h
  rw [ha₂, pairF_pow_eq_one hQ hgp, one_mul]

theorem pairF_zpowers_eq {A : Subgroup (LGL p V)} (hA : Nat.card A = p) {g : LGL p V}
    (hg : g ∈ A) (hg1 : g ≠ 1) : Subgroup.zpowers g = A := by
  have hord : orderOf g ∣ p := by
    have := orderOf_dvd_natCard (⟨g, hg⟩ : A)
    rwa [Subgroup.orderOf_mk g hg, hA] at this
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hord with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hg1
  · exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg)
      (by rw [Nat.card_zpowers, h, hA])

omit [Finite V] in
theorem pairF_fix_span {ι : Type*} {b : ι → V} {g : LGL p V} (h : ∀ i, g (b i) = b i) :
    ∀ w ∈ Submodule.span (ZMod p) (Set.range b), g w = w := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact h i
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem pairQ_weyl_det {R : Type*} [CommRing R] :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R).det = 1 := by
  rw [Matrix.det_fin_two_of]
  ring

theorem pairQ_weyl_mul {R : Type*} [CommRing R] (c : R) :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) * !![1, c; 0, 1] =
      !![1, 0; -c, 1] * !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem pairQ_one_add_pow {R : Type*} [Ring R] (N : R) (hN : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : R) * N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    calc (1 + (k : R) * N) * (1 + N) = 1 + N + (k : R) * N + (k : R) * (N * N) := by
          noncomm_ring
      _ = 1 + ((k + 1 : ℕ) : R) * N := by
          rw [hN, mul_zero, add_zero]
          push_cast
          noncomm_ring

theorem pairQ_sub_one_sq {R : Type*} [CommRing R] (a b c d : R) (hdet : a * d - b * c = 1)
    (h0 : (a - 1) * (d - 1) - b * c = 0) :
    (!![a, b; c, d] - 1 : Matrix (Fin 2) (Fin 2) R) * (!![a, b; c, d] - 1) = 0 := by
  have hs : a + d = 2 := by linear_combination hdet - h0
  have hsub : (!![a, b; c, d] - 1 : Matrix (Fin 2) (Fin 2) R) = !![a - 1, b; c, d - 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hsub, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-1) * hdet + a * hs
  · linear_combination b * hs
  · linear_combination c * hs
  · linear_combination (-1) * hdet + d * hs

theorem pairQ_matrix_pow_prime (M : Matrix (Fin 2) (Fin 2) (ZMod p))
    (hdet : M.det = 1) (v : Fin 2 → ZMod p) (hv : v ≠ 0) (hMv : M.mulVec v = v) :
    M ^ p = 1 := by
  have h0 : (M - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨v, hv, by rw [Matrix.sub_mulVec, hMv, Matrix.one_mulVec, sub_self]⟩
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ZMod p, M = !![a, b; c, d] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  have hsub : (!![a, b; c, d] - 1 : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      !![a - 1, b; c, d - 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [Matrix.det_fin_two_of] at hdet
  rw [hsub, Matrix.det_fin_two_of] at h0
  have hsq := pairQ_sub_one_sq a b c d hdet h0
  have hM : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      1 + (!![a, b; c, d] - 1) := by abel
  have := pairQ_one_add_pow _ hsq p
  rw [← hM] at this
  rw [this]
  simp

theorem pairQ_coprime_sq_sub_one : Nat.Coprime p (p ^ 2 - 1) := by
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  rw [(Fact.out : p.Prime).coprime_iff_not_dvd]
  intro h
  have h2 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have h3 : p ∣ (p ^ 2 - 1) + 1 := by rwa [Nat.sub_add_cancel hp1]
  have h4 : p ∣ 1 := (Nat.dvd_add_right h).mp h3
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h4)

end PairAux

section Pair

variable (hH : Hyp H) {A : Subgroup (LGL p V)} (hA : IsAVMin H A) {x : LGL p V}
  (hxQ : x ∈ Qp p H) (hx : x ∉ Subgroup.centralizer (A : Set (LGL p V)))

omit [Fact p.Prime] [Finite V] in
include hA hxQ in
theorem pairF_E_le : A ⊔ cj x A ≤ H := by
  have hxH : x ∈ H := Qp_le H hxQ
  refine sup_le hA.1.1 fun y hy => ?_
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
  exact H.mul_mem (H.mul_mem hxH (hA.1.1 ha)) (H.inv_mem hxH)

include hA in
theorem pairF_inf_eq_bot : A ⊓ Qp p H = ⊥ :=
  eq_bot_of_le_Qp (hA.1.2.1.mono inf_le_left) inf_le_right

include hA hxQ in
theorem pairF_comm_mem {g : LGL p V} (hg : g ∈ A) :
    g⁻¹ * (x * g * x⁻¹) ∈ (A ⊔ cj x A) ⊓ Qp p H := by
  have h1 : g⁻¹ ∈ A ⊔ cj x A := Subgroup.mem_sup_left (A.inv_mem hg)
  have h2 : x * g * x⁻¹ ∈ A ⊔ cj x A :=
    Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
  refine ⟨Subgroup.mul_mem _ h1 h2, ?_⟩
  have h3 : g⁻¹ * x * g⁻¹⁻¹ ∈ Qp p H := pairF_conj_mem (H.inv_mem (hA.1.1 hg)) hxQ
  have : g⁻¹ * (x * g * x⁻¹) = g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ h3 (inv_mem hxQ)

include hA hxQ in
theorem pairF_decomp_eq : A ⊔ cj x A = A ⊔ ((A ⊔ cj x A) ⊓ Qp p H) := by
  refine le_antisymm (sup_le le_sup_left fun y hy => ?_) (sup_le le_sup_left inf_le_left)
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
  have : (MulAut.conj x).toMonoidHom g = g * (g⁻¹ * (x * g * x⁻¹)) := by
    change x * g * x⁻¹ = _
    group
  rw [this]
  exact Subgroup.mul_mem_sup hg (pairF_comm_mem hA hxQ hg)

include hA hxQ in
theorem pair_factor :
    ∀ g ∈ A ⊔ cj x A, ∃ a₁ ∈ A, ∃ y ∈ (A ⊔ cj x A) ⊓ Qp p H, g = a₁ * y := by
  intro g hg
  have key : ∀ a₁ ∈ A, ∀ n ∈ (A ⊔ cj x A) ⊓ Qp p H, a₁ * n * a₁⁻¹ ∈ (A ⊔ cj x A) ⊓ Qp p H :=
    fun a₁ ha₁ n hn =>
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₁) hn.1)
        (inv_mem (Subgroup.mem_sup_left ha₁)), pairF_conj_mem (hA.1.1 ha₁) hn.2⟩
  have hle : A ≤ Subgroup.normalizer (((A ⊔ cj x A) ⊓ Qp p H : Subgroup (LGL p V)) :
      Set (LGL p V)) := by
    intro a₁ ha₁
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨key a₁ ha₁ n, fun hn => ?_⟩
    have := key a₁⁻¹ (A.inv_mem ha₁) _ hn
    simpa [mul_assoc] using this
  have hg' : g ∈ (↑(A ⊔ ((A ⊔ cj x A) ⊓ Qp p H)) : Set (LGL p V)) :=
    (pairF_decomp_eq hA hxQ).le hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A _ hle] at hg'
  obtain ⟨a₁, ha₁, y, hy, rfl⟩ := Set.mem_mul.mp hg'
  exact ⟨a₁, ha₁, y, hy, rfl⟩

include hH hA hx in
theorem pairQ_ne_comm {g : LGL p V} (hg : g ∈ A) (hg1 : g ≠ 1) : x * g * x⁻¹ ≠ g := by
  intro h
  apply hx
  have hcomm : Commute x g := mul_inv_eq_iff_eq_mul.mp h
  rw [Subgroup.mem_centralizer_iff]
  intro h' hh'
  rw [← pairF_zpowers_eq (IsAVMin.card_eq hH hA).1 hg hg1] at hh'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
  exact (hcomm.zpow_right k).symm.eq

include hH hA hxQ hx in
theorem pairQ_A_faithful {g : LGL p V} (hg : g ∈ A)
    (hfix : ∀ u ∈ commSub (A ⊔ cj x A), g u = u) : g = 1 := by
  by_contra hg1
  have hgH : g ∈ H := hA.1.1 hg
  have hg' : x * g * x⁻¹ ∈ cj x A := Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
  have hgp : g ^ p = 1 := hA.1.2.1.2 g hg
  have hg'p : (x * g * x⁻¹) ^ p = 1 := by rw [conj_pow, hgp, mul_one, mul_inv_cancel]
  have hQ : x * g * x⁻¹ * g⁻¹ ∈ Qp p H := by
    have : x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hxQ (pairF_conj_mem hgH (inv_mem hxQ))
  exact pairQ_ne_comm hH hA hx hg hg1 (pairF_tr hgH hQ hgp hg'p
    (fun v => sub_mem_commSub _ (Subgroup.mem_sup_left hg) v)
    (fun v => sub_mem_commSub _ (Subgroup.mem_sup_right hg') v) hfix)

include hH hA hxQ hx in
theorem pairQ_A'_faithful {g' : LGL p V} (hg' : g' ∈ cj x A)
    (hfix : ∀ u ∈ commSub (A ⊔ cj x A), g' u = u) : g' = 1 := by
  obtain ⟨g, hg, hgg'⟩ := Subgroup.mem_map.mp hg'
  have hgg : g' = x * g * x⁻¹ := hgg'.symm
  subst hgg
  by_cases hg1 : g = 1
  · rw [hg1]
    group
  · exfalso
    have hgH : g ∈ H := hA.1.1 hg
    have hgp : g ^ p = 1 := hA.1.2.1.2 g hg
    have hg'p : (x * g * x⁻¹) ^ p = 1 := by rw [conj_pow, hgp, mul_one, mul_inv_cancel]
    have hQ : g * (x * g * x⁻¹)⁻¹ ∈ Qp p H := by
      have : g * (x * g * x⁻¹)⁻¹ = (g * x * g⁻¹) * x⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (pairF_conj_mem hgH hxQ) (inv_mem hxQ)
    exact pairQ_ne_comm hH hA hx hg hg1 (pairF_tr (pairF_E_le hA hxQ (Subgroup.mem_sup_right hg'))
      hQ hg'p hgp (fun v => sub_mem_commSub _ (Subgroup.mem_sup_right hg') v)
      (fun v => sub_mem_commSub _ (Subgroup.mem_sup_left hg) v) hfix).symm

include hH hA hxQ hx in
theorem pair_transvections :
    ∃ (b : Fin 2 → V) (a a' : LGL p V) (c c' : ZMod p),
      LinearIndependent (ZMod p) b ∧
      Submodule.span (ZMod p) (Set.range b) = commSub (A ⊔ cj x A) ∧
      A = Subgroup.zpowers a ∧ cj x A = Subgroup.zpowers a' ∧ c ≠ 0 ∧ c' ≠ 0 ∧
      HasMatrix b a !![1, c; 0, 1] ∧ HasMatrix b a' !![1, 0; c', 1] := by
  obtain ⟨hAcard, hcc, hqd⟩ := IsAVMin.card_eq hH hA
  obtain ⟨a, hAa⟩ := exists_zpowers_eq_of_card_eq hAcard
  obtain ⟨w, hw0, hLw⟩ := pairF_exists_span hcc
  have haA : a ∈ A := hAa ▸ Subgroup.mem_zpowers a
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hA.2.1
    rw [hAa, Subgroup.zpowers_one_eq_bot, commSub_bot]
  have hwL : w ∈ commSub A := hLw ▸ Submodule.mem_span_singleton_self w
  have haw : a w = w := hqd hwL a haA
  have hAx : cj x A = Subgroup.zpowers (x * a * x⁻¹) := by
    rw [hAa]
    exact MonoidHom.map_zpowers (MulAut.conj x).toMonoidHom a
  have ha'A : x * a * x⁻¹ ∈ cj x A := Subgroup.mem_map.mpr ⟨a, haA, rfl⟩
  have hxL : commSub (cj x A) = Submodule.span (ZMod p) {x w} := pairF_commSub_cj_span x hLw
  have ha'xw : (x * a * x⁻¹) (x w) = x w := by
    change x (a (x⁻¹ (x w))) = x w
    rw [inv_apply_apply', haw]
  have hU : Submodule.span (ZMod p) (Set.range ![w, x w]) = commSub (A ⊔ cj x A) := by
    rw [pairF_commSub_sup, hLw, hxL, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Submodule.span_union]
  have hfixU : ∀ g : LGL p V, g w = w → g (x w) = x w → ∀ u ∈ commSub (A ⊔ cj x A), g u = u := by
    intro g h1 h2
    rw [← hU]
    refine pairF_fix_span (b := ![w, x w]) fun i => ?_
    fin_cases i
    · simpa using h1
    · simpa using h2
  obtain ⟨c, hc⟩ : ∃ c : ZMod p, a (x w) = c • w + x w := by
    have := sub_mem_commSub A haA (x w)
    rw [hLw, Submodule.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by rw [hc]; abel⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ZMod p, (x * a * x⁻¹) w = c' • x w + w := by
    have := sub_mem_commSub (cj x A) ha'A w
    rw [hxL, Submodule.mem_span_singleton] at this
    obtain ⟨c', hc'⟩ := this
    exact ⟨c', by rw [hc']; abel⟩
  have hcne : c ≠ 0 := by
    rintro rfl
    refine ha1 (pairQ_A_faithful hH hA hxQ hx haA (hfixU a haw ?_))
    rw [hc, zero_smul, zero_add]
  have hc'ne : c' ≠ 0 := by
    rintro rfl
    apply ha1
    have h1 := pairQ_A'_faithful hH hA hxQ hx ha'A
      (hfixU _ (by rw [hc', zero_smul, zero_add]) ha'xw)
    calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  have hb : LinearIndependent (ZMod p) ![w, x w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hw0, rfl⟩
    · exfalso
      have hxw : x w = (-(t⁻¹ * s)) • w := by
        have h1 : t • x w = -(s • w) := eq_neg_of_add_eq_zero_right hst
        calc x w = t⁻¹ • (t • x w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-(t⁻¹ * s)) • w := by
            rw [h1, smul_neg, smul_smul]
            exact (neg_smul _ _).symm
      have h1 : a (x w) = x w := by rw [hxw, map_smul, haw]
      rw [hc] at h1
      have h2 : c • w = 0 := by simpa using h1
      exact hcne ((smul_eq_zero.mp h2).resolve_right hw0)
  refine ⟨![w, x w], a, x * a * x⁻¹, c, c', hb, hU, hAa, hAx, hcne, hc'ne, ?_, ?_⟩
  · intro j
    fin_cases j
    · simp [Fin.sum_univ_two, haw]
    · simp [Fin.sum_univ_two, hc]
  · intro j
    fin_cases j
    · simp [Fin.sum_univ_two, hc', add_comm]
    · simp [Fin.sum_univ_two, ha'xw]

include hH hA hxQ hx in
theorem pair_faithful :
    ∀ g ∈ A ⊔ cj x A, (∀ w ∈ commSub (A ⊔ cj x A), g w = w) → g = 1 := by
  intro g hg hfix
  have hU' : ∀ g ∈ A ⊔ cj x A, ∀ v, g v - v ∈ commSub (A ⊔ cj x A) :=
    pairF_sup_mem (fun g hg v => sub_mem_commSub _ (Subgroup.mem_sup_left hg) v)
      (fun g hg v => sub_mem_commSub _ (Subgroup.mem_sup_right hg) v)
  obtain ⟨a₁, ha₁, y, hy, rfl⟩ := pair_factor hA hxQ g hg
  have hQ : a₁ * (a₁ * y)⁻¹ ∈ Qp p H := by
    have : a₁ * (a₁ * y)⁻¹ = a₁ * y⁻¹ * a₁⁻¹ := by group
    rw [this]
    exact pairF_conj_mem (hA.1.1 ha₁) (inv_mem hy.2)
  have h := pairF_tr (pairF_E_le hA hxQ hg) hQ (pow_eq_one_of_trivial hfix (hU' _ hg))
    (hA.1.2.1.2 a₁ ha₁) (hU' _ hg) (fun v => sub_mem_commSub _ (Subgroup.mem_sup_left ha₁) v) hfix
  have hy1 : y = 1 := mul_left_cancel (h.symm.trans (mul_one a₁).symm)
  subst hy1
  rw [mul_one] at hfix ⊢
  exact pairQ_A_faithful hH hA hxQ hx ha₁ hfix

include hH hA hxQ hx in
theorem pair_card_comm : Nat.card (commSub (A ⊔ cj x A)) = p ^ 2 := by
  obtain ⟨b, -, -, -, -, hb, hspan, -⟩ := pair_transvections hH hA hxQ hx
  have hfr : Module.finrank (ZMod p) (commSub (A ⊔ cj x A)) = 2 := by
    rw [← hspan, finrank_span_eq_card hb]
    simp
  rw [card_eq_pow_finrank, hfr]

include hH hA hxQ hx in
theorem pair_isBlock : (p = 2 ∨ p = 3) ∧ IsBlock p (A ⊔ cj x A) := by
  obtain ⟨b, a, a', c, c', hb, hspan, hAa, hAx, hc, hc', ha, ha'⟩ :=
    pair_transvections hH hA hxQ hx
  have hAcard : Nat.card A = p := (IsAVMin.card_eq hH hA).1
  have hcl : Subgroup.closure {a, a'} = A ⊔ cj x A := by
    rw [hAx, hAa, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, Set.insert_eq]
  have hfaith : ∀ g ∈ Subgroup.closure {a, a'}, (∀ j, g (b j) = b j) → g = 1 := by
    intro g hg hfix
    rw [hcl] at hg
    refine pair_faithful hH hA hxQ hx g hg fun w hw => ?_
    rw [← hspan] at hw
    exact pairF_fix_span hfix w hw
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_closure hb hc hc' ha ha' hfaith
  have hEH : Subgroup.closure {a, a'} ≤ H := hcl ▸ pairF_E_le hA hxQ
  have hsolvH : Group.IsSolvable H := hH.solvable
  have hsolvE : Group.IsSolvable (Subgroup.closure {a, a'}) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hEH)
  have hsolvSL : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    Group.isSolvable_of_surjective (f := Φ.toMonoidHom) Φ.surjective
  have hp23 : p = 2 ∨ p = 3 := by
    have hp5 : p < 5 := by
      by_contra h
      exact not_isSolvable_sl2 (not_lt.mp h) hsolvSL
    have hp2 := (Fact.out : p.Prime).two_le
    have h4 : p ≠ 4 := fun h => by
      have hpp := (Fact.out : p.Prime)
      rw [h] at hpp
      exact absurd hpp (by norm_num)
    omega
  have hcardE : Nat.card (A ⊔ cj x A : Subgroup (LGL p V)) = p * (p ^ 2 - 1) := by
    have h1 : Nat.card (Subgroup.closure {a, a'}) = p * (p ^ 2 - 1) :=
      (Nat.card_congr Φ.toEquiv).trans card_sl2
    rwa [hcl] at h1
  have haE : a ∈ Subgroup.closure {a, a'} := Subgroup.subset_closure (by simp)
  have ha'E : a' ∈ Subgroup.closure {a, a'} := Subgroup.subset_closure (by simp)
  have hΦa : (Φ ⟨a, haE⟩ : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, c; 0, 1] :=
    HasMatrix.unique hb (hΦ ⟨a, haE⟩) ha
  have hΦa' : (Φ ⟨a', ha'E⟩ : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; c', 1] :=
    HasMatrix.unique hb (hΦ ⟨a', ha'E⟩) ha'
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ZMod p) * c' = -c :=
    ⟨(-c * c'⁻¹).val, by rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc', mul_one]⟩
  obtain ⟨e, he⟩ : ∃ e : Subgroup.closure {a, a'}, e * ⟨a, haE⟩ = ⟨a', ha'E⟩ ^ k * e := by
    let W : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) := ⟨!![0, 1; -1, 0], pairQ_weyl_det⟩
    refine ⟨Φ.symm W, Φ.injective ?_⟩
    rw [map_mul, map_mul, map_pow, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_pow, hΦa, hΦa', SL2Aux.lower_pow, hk]
    exact pairQ_weyl_mul c
  have heE : (e : LGL p V) ∈ A ⊔ cj x A := by
    rw [← hcl]
    exact e.2
  have hea : (e : LGL p V) * a * (e : LGL p V)⁻¹ = a' ^ k := by
    rw [mul_inv_eq_iff_eq_mul]
    exact congrArg Subtype.val he
  have hcjle : cj (e : LGL p V) A ≤ cj x A := by
    rw [hAx, hAa, show cj (e : LGL p V) (Subgroup.zpowers a) =
      Subgroup.zpowers ((e : LGL p V) * a * (e : LGL p V)⁻¹) from
      MonoidHom.map_zpowers (MulAut.conj _).toMonoidHom a, hea]
    exact Subgroup.zpowers_le.mpr (pow_mem (Subgroup.mem_zpowers a') _)
  have hcjeq : cj (e : LGL p V) A = cj x A :=
    Subgroup.eq_of_le_of_card_ge hcjle (by rw [card_cj A, card_cj A])
  refine ⟨hp23, pair_card_comm hH hA hxQ hx, pair_faithful hH hA hxQ hx, hcardE, A, le_sup_left,
    hAcard, le_antisymm (iSup₂_le fun g hg => ?_) (sup_le ?_ ?_)⟩
  · intro y hy
    rw [mem_cj] at hy
    have hy' : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [hy']
    exact mul_mem (mul_mem hg (Subgroup.mem_sup_left hy)) (inv_mem hg)
  · exact le_iSup₂_of_le 1 (one_mem _) (by rw [cj_one])
  · exact hcjeq.symm.le.trans (le_iSup₂_of_le _ heE le_rfl)

include hA hxQ in
theorem pair_decomp :
    A ⊔ cj x A = A ⊔ ((A ⊔ cj x A) ⊓ Qp p H) ∧ A ⊓ ((A ⊔ cj x A) ⊓ Qp p H) = ⊥ := by
  refine ⟨pairF_decomp_eq hA hxQ, eq_bot_iff.mpr fun g hg => ?_⟩
  have h : g ∈ A ⊓ Qp p H := ⟨hg.1, hg.2.2⟩
  rwa [pairF_inf_eq_bot hA] at h

include hA hxQ in
theorem pair_Qx_normal :
    ∀ e ∈ A ⊔ cj x A, ∀ q ∈ (A ⊔ cj x A) ⊓ Qp p H, e * q * e⁻¹ ∈ (A ⊔ cj x A) ⊓ Qp p H :=
  fun _ he _ hq =>
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ he hq.1) (inv_mem he),
      pairF_conj_mem (pairF_E_le hA hxQ he) hq.2⟩

include hH hA hxQ hx in
theorem pair_Qx_card :
    Nat.card ((A ⊔ cj x A) ⊓ Qp p H : Subgroup (LGL p V)) = p ^ 2 - 1 := by
  obtain ⟨-, hblock⟩ := pair_isBlock hH hA hxQ hx
  have hAcard : Nat.card A = p := (IsAVMin.card_eq hH hA).1
  have hfac := pair_factor hA hxQ
  have hdec : A ⊓ ((A ⊔ cj x A) ⊓ Qp p H) = ⊥ := (pair_decomp hA hxQ).2
  let f : A × ((A ⊔ cj x A) ⊓ Qp p H : Subgroup (LGL p V)) →
      (A ⊔ cj x A : Subgroup (LGL p V)) :=
    fun q => ⟨q.1 * q.2, mul_mem (Subgroup.mem_sup_left q.1.2) q.2.2.1⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a₁, ha₁⟩, ⟨y₁, hy₁⟩⟩ ⟨⟨a₂, ha₂⟩, ⟨y₂, hy₂⟩⟩ h
      have h1 : a₁ * y₁ = a₂ * y₂ := congrArg Subtype.val h
      have h3 : a₂⁻¹ * a₁ = y₂ * y₁⁻¹ :=
        calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * y₁) * y₁⁻¹ := by group
          _ = a₂⁻¹ * (a₂ * y₂) * y₁⁻¹ := by rw [h1]
          _ = y₂ * y₁⁻¹ := by group
      have h4 : a₂⁻¹ * a₁ ∈ A ⊓ ((A ⊔ cj x A) ⊓ Qp p H) :=
        Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha₂) ha₁, h3 ▸ mul_mem hy₂ (inv_mem hy₁)⟩
      rw [hdec, Subgroup.mem_bot, inv_mul_eq_one] at h4
      subst h4
      have h5 : y₁ = y₂ := mul_left_cancel h1
      subst h5
      rfl
    · rintro ⟨g, hg⟩
      obtain ⟨a₁, ha₁, y, hy, rfl⟩ := hfac g hg
      exact ⟨(⟨a₁, ha₁⟩, ⟨y, hy⟩), rfl⟩
  have hcard : Nat.card A * Nat.card ((A ⊔ cj x A) ⊓ Qp p H : Subgroup (LGL p V)) =
      Nat.card (A ⊔ cj x A : Subgroup (LGL p V)) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (Equiv.ofBijective f hbij)
  rw [hblock.card, hAcard] at hcard
  exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos hcard

include hH hA hxQ hx in
theorem pair_Qx_isPGroup :
    IsPGroup (rp p) ((A ⊔ cj x A) ⊓ Qp p H : Subgroup (LGL p V)) := by
  have hcard := pair_Qx_card hH hA hxQ hx
  rcases (pair_isBlock hH hA hxQ hx).1 with h | h
  · refine IsPGroup.of_card (n := 1) ?_
    rw [hcard, h]
    decide
  · refine IsPGroup.of_card (n := 3) ?_
    rw [hcard, h]
    decide

include hA hxQ in
theorem pair_Qx_le : (A ⊔ cj x A) ⊓ Qp p H ≤ ⁅Qp p H, A⁆ := by
  have hAnQ : A ≤ Subgroup.normalizer (Qp p H : Set (LGL p V)) := le_normalizer_Qp hA.1.1
  have hAE : A ≤ A ⊔ cj x A := le_sup_left
  have hNQ : ⁅Qp p H, A⁆ ≤ Qp p H := by
    rw [Subgroup.commutator_le]
    intro q hq a ha
    have h1 : a * q⁻¹ * a⁻¹ ∈ Qp p H := Subgroup.le_normalizer_iff.mp hAnQ a ha _ (inv_mem hq)
    have h2 : q * a * q⁻¹ * a⁻¹ = q * (a * q⁻¹ * a⁻¹) := by group
    show q * a * q⁻¹ * a⁻¹ ∈ Qp p H
    rw [h2]
    exact mul_mem hq h1
  have hAN : A ≤ Subgroup.normalizer ((⁅Qp p H, A⁆ ⊓ (A ⊔ cj x A) : Subgroup (LGL p V)) :
      Set (LGL p V)) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.normalizer_commutator_ge_right (Qp p H) A ha, Subgroup.le_normalizer (hAE ha)⟩
  have hEle : A ⊔ cj x A ≤ A ⊔ (⁅Qp p H, A⁆ ⊓ (A ⊔ cj x A)) := by
    refine sup_le le_sup_left ?_
    intro t ht
    obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, t = x * a * x⁻¹ := ⟨x⁻¹ * t * x, mem_cj.mp ht, by group⟩
    have hn : x * a * x⁻¹ * a⁻¹ ∈ ⁅Qp p H, A⁆ ⊓ (A ⊔ cj x A) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.commutator_mem_commutator hxQ ha,
        mul_mem (Subgroup.mem_sup_right ht) (inv_mem (hAE ha))⟩
    have h3 : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
    rw [h3]
    exact mul_mem (Subgroup.mem_sup_right hn) (Subgroup.mem_sup_left ha)
  intro y hy
  have hyE : y ∈ A ⊔ (⁅Qp p H, A⁆ ⊓ (A ⊔ cj x A)) := hEle hy.1
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at hyE
  obtain ⟨a, ha, n, hn, hay⟩ := hyE
  have hay' : a * n = y := hay
  have hnQ : n ∈ Qp p H := hNQ hn.1
  have haQ : a ∈ Qp p H := by
    have h1 : a = y * n⁻¹ := by rw [← hay']; group
    rw [h1]
    exact mul_mem hy.2 (inv_mem hnQ)
  have ha1 : a = 1 := by
    have h2 : a ∈ A ⊓ ((A ⊔ cj x A) ⊓ Qp p H) :=
      Subgroup.mem_inf.mpr ⟨ha, Subgroup.mem_inf.mpr ⟨hAE ha, haQ⟩⟩
    rw [(pair_decomp hA hxQ).2] at h2
    exact h2
  rw [ha1, one_mul] at hay'
  rw [← hay']
  exact hn.1

include hH hA hxQ hx in
theorem pairQ_eq_one_of_fix :
    ∀ g ∈ (A ⊔ cj x A) ⊓ Qp p H, ∀ u ∈ commSub (A ⊔ cj x A), u ≠ 0 → g u = u → g = 1 := by
  obtain ⟨-, hblock⟩ := pair_isBlock hH hA hxQ hx
  obtain ⟨b, -, -, -, -, hb, hspan, -⟩ := pair_transvections hH hA hxQ hx
  obtain ⟨Φ, hΦ⟩ := hblock.exists_mulEquiv b hb hspan
  intro g hg u hu hu0 hgu
  let gE : ↥(A ⊔ cj x A) := ⟨g, hg.1⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp (hspan ▸ hu)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hu0
    rw [← hc]
    simp
  have hgu' : (gE : LGL p V) u = u := hgu
  have hmv : (Φ gE : Matrix (Fin 2) (Fin 2) (ZMod p)).mulVec c = c := by
    have h1 := (hΦ gE).apply_sum c
    rw [hc, hgu'] at h1
    have h2 : ∑ k, ((Φ gE : Matrix (Fin 2) (Fin 2) (ZMod p)).mulVec c k - c k) • b k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← h1, hc, sub_self]
    funext k
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hb _ h2 k)
  have hpow : Φ gE ^ p = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact pairQ_matrix_pow_prime _ (Φ gE).2 c hc0 hmv
  have hQx : (⟨g, hg⟩ : ↥((A ⊔ cj x A) ⊓ Qp p H)) ^ (p ^ 2 - 1) = 1 := by
    have := pow_card_eq_one' (x := (⟨g, hg⟩ : ↥((A ⊔ cj x A) ⊓ Qp p H)))
    rwa [pair_Qx_card hH hA hxQ hx] at this
  have hg1 : g ^ (p ^ 2 - 1) = 1 := by simpa using congrArg Subtype.val hQx
  have hgE : gE ^ (p ^ 2 - 1) = 1 := Subtype.ext (by simpa using hg1)
  have hΦpow : Φ gE ^ (p ^ 2 - 1) = 1 := by rw [← map_pow, hgE, map_one]
  have hΦ1 : Φ gE = 1 :=
    (pow_eq_one_iff_of_coprime pairQ_coprime_sq_sub_one).mp ⟨hpow, hΦpow⟩
  have hgE1 : gE = 1 := Φ.injective (hΦ1.trans (map_one Φ).symm)
  exact congrArg Subtype.val hgE1

include hH hA hxQ hx in
theorem pairQ_irred_core (U : Submodule (ZMod p) V) (hU : U ≤ commSub (A ⊔ cj x A))
    (hinv : ∀ g ∈ (A ⊔ cj x A) ⊓ Qp p H, ∀ u ∈ U, g u ∈ U) :
    U = ⊥ ∨ U = commSub (A ⊔ cj x A) := by
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  right
  obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hfree := pairQ_eq_one_of_fix hH hA hxQ hx
  let f : Option ↥((A ⊔ cj x A) ⊓ Qp p H) → U := fun o =>
    o.elim 0 (fun g => ⟨(g : LGL p V) u₀, hinv g g.2 u₀ hu₀⟩)
  have hne : ∀ g : ↥((A ⊔ cj x A) ⊓ Qp p H), (g : LGL p V) u₀ ≠ 0 := by
    intro g h0
    apply hu₀0
    have h1 := inv_apply_apply' (g : LGL p V) u₀
    rwa [h0, map_zero, eq_comm] at h1
  have hf : Function.Injective f := by
    intro o₁ o₂ h
    rcases o₁ with _ | g₁ <;> rcases o₂ with _ | g₂
    · rfl
    · exact absurd (congrArg Subtype.val h).symm (hne g₂)
    · exact absurd (congrArg Subtype.val h) (hne g₁)
    · have h1 : (g₁ : LGL p V) u₀ = (g₂ : LGL p V) u₀ := congrArg Subtype.val h
      have h2 : ((g₂ : LGL p V)⁻¹ * g₁) u₀ = u₀ := by
        change (g₂ : LGL p V)⁻¹ ((g₁ : LGL p V) u₀) = u₀
        rw [h1]
        exact inv_apply_apply' _ _
      have h3 := hfree _ (mul_mem (inv_mem g₂.2) g₁.2) u₀ (hU hu₀) hu₀0 h2
      exact congrArg some (Subtype.ext (inv_mul_eq_one.mp h3).symm)
  have hcard : Nat.card ↥((A ⊔ cj x A) ⊓ Qp p H) + 1 ≤ Nat.card U := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Finite.card_option] at this
  rw [pair_Qx_card hH hA hxQ hx] at hcard
  have hp2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hge : Nat.card (commSub (A ⊔ cj x A)) ≤ Nat.card U := by
    rw [pair_card_comm hH hA hxQ hx]
    omega
  exact SetLike.coe_injective (Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hU hge)

include hH hA hxQ hx in
theorem pair_commSub_Qx :
    commSub ((A ⊔ cj x A) ⊓ Qp p H) = commSub (A ⊔ cj x A) := by
  have hle : commSub ((A ⊔ cj x A) ⊓ Qp p H) ≤ commSub (A ⊔ cj x A) :=
    commSub_mono _ _ inf_le_left
  have hne : commSub ((A ⊔ cj x A) ⊓ Qp p H) ≠ ⊥ := by
    intro h
    have h1 := (commSub_eq_bot_iff _).mp h
    have h2 := pair_Qx_card hH hA hxQ hx
    rw [h1, Subgroup.card_bot] at h2
    have h3 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have h4 : 2 * 2 ≤ p ^ 2 := by nlinarith
    omega
  rcases pairQ_irred_core hH hA hxQ hx _ hle (fun g hg u hu => map_mem_commSub _ hg hu) with h | h
  · exact absurd h hne
  · exact h

omit [Fact p.Prime] [Finite V] in
theorem commSub_le_pair : commSub A ≤ commSub (A ⊔ cj x A) :=
  commSub_mono _ _ le_sup_left

include hH hA hxQ hx in
theorem pair_irred (U : Submodule (ZMod p) V) (hU : U ≤ commSub (A ⊔ cj x A))
    (hinv : ∀ g ∈ (A ⊔ cj x A) ⊓ Qp p H, ∀ u ∈ U, g u ∈ U) :
    U = ⊥ ∨ U = commSub (A ⊔ cj x A) :=
  pairQ_irred_core hH hA hxQ hx U hU hinv

end Pair

section CommutatorGC

open Subgroup

theorem pairC_pow_card_eq_one {M : Type*} [Group M] [Finite M] {ℓ : ℕ} [Fact ℓ.Prime] {s : M}
    (h : ∃ k : ℕ, s ^ (ℓ ^ k) = 1) : s ^ (ℓ ^ Nat.card M) = 1 := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).1 (orderOf_dvd_of_pow_eq_one hk)
  have h1 : ℓ ^ j ≤ Nat.card M := hj ▸ Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard s)
  have h2 : j < ℓ ^ j := Nat.lt_pow_self (Fact.out : ℓ.Prime).one_lt
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  exact pow_dvd_pow ℓ (by omega)

open scoped IsMulCommutative in
theorem pairC_isPGroup_of_center_index {M : Type*} [Group M] [Finite M] {ℓ : ℕ} [Fact ℓ.Prime]
    {S : Set M} (hS : Subgroup.closure S = ⊤) (hSℓ : ∀ s ∈ S, ∃ k : ℕ, s ^ (ℓ ^ k) = 1)
    (hidx : ∃ c : ℕ, (Subgroup.center M).index = ℓ ^ c) : IsPGroup ℓ M := by
  obtain ⟨c, hc⟩ := hidx
  let W : M →* Subgroup.center M :=
    (powMonoidHom (ℓ ^ Nat.card M)).comp (MonoidHom.transferCenterPow M)
  have hW : ∀ m : M, ((W m : Subgroup.center M) : M) = (m ^ (Subgroup.center M).index) ^
      (ℓ ^ Nat.card M) := fun m => rfl
  have hker : Subgroup.closure S ≤ W.ker := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hW, hc, ← pow_mul, mul_comm, pow_mul, pairC_pow_card_eq_one (hSℓ s hs), one_pow]
    rfl
  intro m
  have h1 : m ∈ W.ker := hker (hS ▸ Subgroup.mem_top m)
  have h2 := congrArg Subtype.val (MonoidHom.mem_ker.1 h1)
  rw [hW, hc, ← pow_mul, ← pow_add] at h2
  exact ⟨c + Nat.card M, h2⟩

theorem pairC_commutator_lt {G : Type*} [Group G] {Q N : Subgroup G} (hQ : Group.IsSolvable Q)
    (hNQ : N ≤ Q) (hN : N ≠ ⊥) : ⁅N, N⁆ < N := by
  have h1 : N.subgroupOf Q ≠ ⊥ := by
    intro h
    apply hN
    rw [← Subgroup.map_subgroupOf_eq_of_le hNQ, h, Subgroup.map_bot]
  have h2 := Group.IsSolvable.commutator_lt_of_ne_bot h1
  have h3 := (Subgroup.map_lt_map_iff_of_injective Q.subtype_injective).2 h2
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hNQ] at h3

theorem pairC_exists_prime_pgroup_normal {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQs : Group.IsSolvable Q) (hQ : Q ≠ ⊥) (hQn : Q.Normal) :
    ∃ (N : Subgroup G) (r : ℕ), N.Normal ∧ N ≤ Q ∧ N ≠ ⊥ ∧ r.Prime ∧
      ∀ x ∈ N, ∃ k : ℕ, x ^ (r ^ k) = 1 := by
  let S : Set (Subgroup G) := {N | N.Normal ∧ N ≤ Q ∧ N ≠ ⊥}
  have hSne : S.Nonempty := ⟨Q, hQn, le_rfl, hQ⟩
  obtain ⟨N, ⟨hNn, hNQ, hN⟩, hmin⟩ := WellFounded.has_min wellFounded_lt S hSne
  have hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    have h0 : ⁅N, N⁆ = ⊥ := by
      by_contra hne
      have hnorm : (⁅N, N⁆ : Subgroup G).Normal := inferInstance
      exact hmin ⁅N, N⁆ ⟨hnorm, (Subgroup.commutator_le_left N N).trans hNQ, hne⟩
        (pairC_commutator_lt hQs hNQ hN)
    intro a ha b hb
    have h1 := Subgroup.commutator_mem_commutator ha hb
    rw [h0, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card N ≠ 1 from fun h => hN (Subgroup.card_eq_one.1 h))
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hrdvd
  let Nr : Subgroup G :=
    { carrier := {x | x ∈ N ∧ ∃ k : ℕ, x ^ (r ^ k) = 1}
      one_mem' := ⟨N.one_mem, 0, one_pow _⟩
      mul_mem' := by
        rintro a b ⟨ha, j, hj⟩ ⟨hb, k, hk⟩
        refine ⟨N.mul_mem ha hb, j + k, ?_⟩
        have hab : Commute a b := hcomm a ha b hb
        rw [hab.mul_pow, pow_add, pow_mul, hj, one_pow, mul_comm (r ^ j), pow_mul, hk, one_pow,
          one_mul]
      inv_mem' := by
        rintro a ⟨ha, k, hk⟩
        exact ⟨N.inv_mem ha, k, by rw [inv_pow, hk, inv_one]⟩ }
  have hNr_normal : Nr.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨hxN, k, hk⟩ := hx
    exact ⟨hNn.conj_mem x hxN g, k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  have hNr_le : Nr ≤ N := fun x hx => hx.1
  have hNr_ne : Nr ≠ ⊥ := by
    intro h
    have hyG : orderOf (y : G) = r := (Subgroup.orderOf_coe y).trans hy
    have hy1 : (y : G) ∈ Nr := ⟨y.2, 1, by rw [pow_one, ← hyG]; exact pow_orderOf_eq_one _⟩
    have hy2 : (y : G) ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hyG
      exact hr.one_lt.ne hyG
    rw [h, Subgroup.mem_bot] at hy1
    exact hy2 hy1
  have hNr_eq : Nr = N := by
    by_contra hne
    exact hmin Nr ⟨hNr_normal, hNr_le.trans hNQ, hNr_ne⟩ (lt_of_le_of_ne hNr_le hne)
  refine ⟨N, r, hNn, hNQ, hN, hr, fun x hx => ?_⟩
  have : x ∈ Nr := hNr_eq.symm ▸ hx
  exact this.2

theorem pairC_core {ℓ : ℕ} [Fact ℓ.Prime] (n : ℕ) :
    ∀ {G : Type*} [Group G] [Finite G], Nat.card G = n →
      ∀ (Q A : Subgroup G), Q.Normal → Group.IsSolvable Q →
        (∀ x ∈ Q, ∀ g ∈ A, ∃ k : ℕ, (x * g * x⁻¹ * g⁻¹) ^ (ℓ ^ k) = 1) →
        IsPGroup ℓ (⁅Q, A⁆ : Subgroup G) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn Q A hQn hQs hcomm
  by_cases hQ : Q = ⊥
  · subst hQ
    rw [Subgroup.commutator_bot_left]
    exact IsPGroup.of_bot
  obtain ⟨N, r, hNn, hNQ, hN, hr, hNr⟩ := pairC_exists_prime_pgroup_normal hQs hQ hQn
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hlt : Nat.card (G ⧸ N) < n := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have h2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hN
    have h3 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    rw [← hn, h1]
    exact lt_mul_of_one_lt_right h3 h2
  have hIH : IsPGroup ℓ (⁅Q.map π, A.map π⁆ : Subgroup (G ⧸ N)) := by
    refine ih (Nat.card (G ⧸ N)) hlt rfl (Q.map π) (A.map π) (hQn.map π hπs) ?_ ?_
    · exact Group.isSolvable_of_surjective (f := π.subgroupMap Q) (π.subgroupMap_surjective Q)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨g, hg, rfl⟩
      obtain ⟨k, hk⟩ := hcomm x hx g hg
      refine ⟨k, ?_⟩
      have := congrArg π hk
      simpa only [map_pow, map_mul, map_inv, map_one] using this
  have hπ : ∀ m ∈ (⁅Q, A⁆ : Subgroup G), ∃ k : ℕ, π m ^ (ℓ ^ k) = 1 := by
    intro m hm
    have hm' : π m ∈ (⁅Q.map π, A.map π⁆ : Subgroup (G ⧸ N)) := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.mem_map_of_mem π hm
    obtain ⟨k, hk⟩ := hIH ⟨π m, hm'⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hπN : ∀ (m : G) (k : ℕ), π m ^ (ℓ ^ k) = 1 → m ^ (ℓ ^ k) ∈ N := by
    intro m k hk
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hk
  by_cases hrl : r = ℓ
  · rw [hrl] at hNr
    intro m
    obtain ⟨k, hk⟩ := hπ m m.2
    obtain ⟨j, hj⟩ := hNr _ (hπN m k hk)
    refine ⟨k + j, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_add, pow_mul, hj]
    rfl
  have hA : ∀ y ∈ N, ∀ g ∈ A, y * g = g * y := by
    intro y hy g hg
    have hc : y * g * y⁻¹ * g⁻¹ ∈ N := by
      have : y * g * y⁻¹ * g⁻¹ = y * (g * y⁻¹ * g⁻¹) := by simp only [mul_assoc]
      rw [this]
      exact N.mul_mem hy (hNn.conj_mem _ (N.inv_mem hy) g)
    obtain ⟨a, ha⟩ := hNr _ hc
    obtain ⟨b, hb⟩ := hcomm y (hNQ hy) g hg
    have hcop : Nat.Coprime (r ^ a) (ℓ ^ b) :=
      Nat.Coprime.pow a b ((Nat.coprime_primes hr (Fact.out : ℓ.Prime)).2 hrl)
    have h1 : y * g * y⁻¹ * g⁻¹ = 1 :=
      orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha)
        (orderOf_dvd_of_pow_eq_one hb))
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hC : (⁅Q, A⁆ : Subgroup G) ≤ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.commutator_le]
    intro x hx g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxy : (x⁻¹ * y * x) * g = g * (x⁻¹ * y * x) := by
      refine hA _ ?_ g hg
      simpa using hNn.conj_mem y hy x⁻¹
    have h1 : y * (x * g * x⁻¹) = (x * g * x⁻¹) * y := by
      calc y * (x * g * x⁻¹) = x * ((x⁻¹ * y * x) * g) * x⁻¹ := by group
        _ = x * (g * (x⁻¹ * y * x)) * x⁻¹ := by rw [hxy]
        _ = (x * g * x⁻¹) * y := by group
    have h2 : y * g⁻¹ = g⁻¹ * y := by
      have := hA y hy g hg
      calc y * g⁻¹ = g⁻¹ * (g * y) * g⁻¹ := by group
        _ = g⁻¹ * (y * g) * g⁻¹ := by rw [this]
        _ = g⁻¹ * y := by group
    have h3 : y * (x * g * x⁻¹ * g⁻¹) = (x * g * x⁻¹ * g⁻¹) * y :=
      (Commute.mul_right (show Commute y (x * g * x⁻¹) from h1)
        (show Commute y g⁻¹ from h2)).eq
    exact h3
  set M : Subgroup G := ⁅Q, A⁆ with hM
  let K : Subgroup M := N.subgroupOf M
  have hKc : K ≤ Subgroup.center M := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 (hC m.2) z hz).symm
  have hKn : K.Normal := inferInstance
  have hQuot : IsPGroup ℓ (M ⧸ K) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H m =>
      obtain ⟨k, hk⟩ := hπ m m.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hπN m k hk
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hQuot
  have hKidx : K.index = ℓ ^ b := by rw [Subgroup.index_eq_card]; exact hb
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow (Fact.out : ℓ.Prime)).1
    (hKidx ▸ Subgroup.index_dvd_of_le hKc)
  refine pairC_isPGroup_of_center_index
    (S := ((↑) : M → G) ⁻¹' {g | ∃ x ∈ Q, ∃ g' ∈ A, x * g' * x⁻¹ * g'⁻¹ = g})
    ?_ ?_ ⟨c, hc⟩
  · exact Subgroup.closure_closure_coe_preimage
  · rintro s ⟨x, hx, g, hg, hs⟩
    obtain ⟨k, hk⟩ := hcomm x hx g hg
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, ← hs]; exact hk)⟩

theorem isPGroup_commutator_of_commutators {G : Type*} [Group G] [Finite G] {ℓ : ℕ}
    [Fact ℓ.Prime] {Q A : Subgroup G} (hQ : Group.IsSolvable Q)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hcomm : ∀ x ∈ Q, ∀ g ∈ A, ∃ k : ℕ, (x * g * x⁻¹ * g⁻¹) ^ (ℓ ^ k) = 1) :
    IsPGroup ℓ (⁅Q, A⁆ : Subgroup G) := by
  have hQΓ : Q ≤ Q ⊔ A := le_sup_left
  have hAΓ : A ≤ Q ⊔ A := le_sup_right
  have hΓn : Q ⊔ A ≤ Subgroup.normalizer (Q : Set G) := sup_le Subgroup.le_normalizer hAQ
  have hQn : (Q.subgroupOf (Q ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQΓ).2 hΓn
  have hQs : Group.IsSolvable (Q.subgroupOf (Q ⊔ A)) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hQΓ).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hcomm' : ∀ x ∈ Q.subgroupOf (Q ⊔ A), ∀ g ∈ A.subgroupOf (Q ⊔ A),
      ∃ k : ℕ, (x * g * x⁻¹ * g⁻¹) ^ (ℓ ^ k) = 1 := by
    intro x hx g hg
    obtain ⟨k, hk⟩ := hcomm x hx g hg
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hpg := pairC_core (Nat.card (Q ⊔ A : Subgroup G)) rfl (Q.subgroupOf (Q ⊔ A))
    (A.subgroupOf (Q ⊔ A)) hQn hQs hcomm'
  intro m
  have hm : (m : G) ∈ Subgroup.map (Q ⊔ A).subtype
      (⁅Q.subgroupOf (Q ⊔ A), A.subgroupOf (Q ⊔ A)⁆ : Subgroup (Q ⊔ A : Subgroup G)) := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQΓ,
      Subgroup.map_subgroupOf_eq_of_le hAΓ]
    exact m.2
  obtain ⟨y, hy, hym⟩ := hm
  obtain ⟨k, hk⟩ := hpg ⟨y, hy⟩
  have h1 : y ^ (ℓ ^ k) = 1 := congrArg Subtype.val hk
  have h2 : (y : G) ^ (ℓ ^ k) = 1 := by simpa using congrArg Subtype.val h1
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hym]
  simpa using h2

end CommutatorGC

section CommutatorAux

theorem comm_mul_mul_inv_inv_eq_one {G : Type*} [Group G] {A : Subgroup G} {q : G}
    (hq : q ∈ Subgroup.centralizer (A : Set G)) {a : G} (ha : a ∈ A) :
    q * a * q⁻¹ * a⁻¹ = 1 := by
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  exact (Subgroup.mem_centralizer_iff.mp hq a ha).symm

theorem comm_mem_Qx {A : Subgroup (LGL p V)} (hAH : A ≤ H) {q a : LGL p V} (hq : q ∈ Qp p H)
    (ha : a ∈ A) : q * a * q⁻¹ * a⁻¹ ∈ (A ⊔ cj q A) ⊓ Qp p H := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : q * a * q⁻¹ ∈ cj q A := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left (A.inv_mem ha))
  · have h3 : a * q⁻¹ * a⁻¹ ∈ Qp p H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_Qp hAH ha) q⁻¹).mp ((Qp p H).inv_mem hq)
    have h4 : q * a * q⁻¹ * a⁻¹ = q * (a * q⁻¹ * a⁻¹) := by simp only [mul_assoc]
    rw [h4]
    exact Subgroup.mul_mem _ hq h3

theorem comm_mem_commutator_conj {G : Type*} [Group G] {Q A : Subgroup G} {g n : G}
    (hg : g ∈ Q) (hn : n ∈ ⁅Q, A⁆) : g * n * g⁻¹ ∈ ⁅Q, A⁆ := by
  have key : ⁅Q, A⁆ ≤ (⁅Q, A⁆).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro q hq a ha
    show g * (q * a * q⁻¹ * a⁻¹) * g⁻¹ ∈ ⁅Q, A⁆
    have h1 : g * (q * a * q⁻¹ * a⁻¹) * g⁻¹ =
        (g * q * a * (g * q)⁻¹ * a⁻¹) * (g * a * g⁻¹ * a⁻¹)⁻¹ := by group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (Q.mul_mem hg hq) ha)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hg ha))
  exact key hn

end CommutatorAux

section Commutator

variable (hH : Hyp H) {A : Subgroup (LGL p V)} (hA : IsAVMin H A)

include hH hA in
theorem commutator_ne_bot : ⁅Qp p H, A⁆ ≠ ⊥ := by
  intro h
  have hcent : Qp p H ≤ Subgroup.centralizer (A : Set (LGL p V)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hAQ : A ≤ Qp p H := fun a ha =>
    hH.centralizer_le_Qp
      (Subgroup.mem_inf.mpr ⟨hA.1.1 ha, Subgroup.le_centralizer_iff.mp hcent ha⟩)
  have hbot : A = ⊥ := eq_bot_of_le_Qp hA.1.2.1 hAQ
  exact hA.2.1 (by rw [hbot]; exact commSub_bot)

include hH hA in
theorem comm_exists_noncentral :
    ∃ x ∈ Qp p H, x ∉ Subgroup.centralizer (A : Set (LGL p V)) :=
  IsConcreteLE.not_le_iff_exists.mp fun hle =>
    commutator_ne_bot hH hA (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle)

include hA in
theorem commutator_eq_iSup :
    ⁅Qp p H, A⁆ = ⨆ (x : LGL p V) (_ : x ∈ Qp p H ∧ x ∉ Subgroup.centralizer (A : Set (LGL p V))),
      (A ⊔ cj x A) ⊓ Qp p H := by
  refine le_antisymm ?_ (iSup₂_le fun x hx => pair_Qx_le hA hx.1)
  rw [Subgroup.commutator_le]
  intro q hq a ha
  show q * a * q⁻¹ * a⁻¹ ∈ _
  by_cases hqc : q ∈ Subgroup.centralizer (A : Set (LGL p V))
  · rw [comm_mul_mul_inv_inv_eq_one hqc ha]
    exact one_mem _
  · exact Subgroup.mem_iSup_of_mem q
      (Subgroup.mem_iSup_of_mem ⟨hq, hqc⟩ (comm_mem_Qx hA.1.1 hq ha))

include hH hA in
theorem isPGroup_commutator :
    (p = 2 ∨ p = 3) ∧ IsPGroup (rp p) (⁅Qp p H, A⁆ : Subgroup (LGL p V)) := by
  obtain ⟨x₀, hx₀, hx₀c⟩ := comm_exists_noncentral hH hA
  refine ⟨(pair_isBlock hH hA hx₀ hx₀c).1, ?_⟩
  have : Fact (rp p).Prime := ⟨by unfold rp; split_ifs <;> norm_num⟩
  have := hH.solvable
  refine isPGroup_commutator_of_commutators (G := LGL p V) (ℓ := rp p) (Q := Qp p H) (A := A)
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (Qp_le H)))
    (le_normalizer_Qp hA.1.1) ?_
  intro x hx g hg
  by_cases hxc : x ∈ Subgroup.centralizer (A : Set (LGL p V))
  · exact ⟨0, by rw [pow_zero, pow_one]; exact comm_mul_mul_inv_inv_eq_one hxc hg⟩
  · obtain ⟨k, hk⟩ :=
      pair_Qx_isPGroup hH hA hx hxc ⟨x * g * x⁻¹ * g⁻¹, comm_mem_Qx hA.1.1 hx hg⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

omit [Fact p.Prime] [Finite V] in
theorem commutator_normal : ∀ g ∈ Qp p H, ∀ n ∈ ⁅Qp p H, A⁆, g * n * g⁻¹ ∈ ⁅Qp p H, A⁆ :=
  fun _ hg _ hn => comm_mem_commutator_conj hg hn

end Commutator

end CFSG.SignalizerFunctorTheorem.Quadratic
