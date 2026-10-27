module

public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidInduced
public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

private lemma tau_sub {k p : ℕ} {G : Type} [Group G] {τ : (Fin k → ZMod p) → G}
    (hτ : ∀ x y, τ (x + y) = τ x * τ y) (x y : Fin k → ZMod p) :
    τ (x - y) = τ x * (τ y)⁻¹ := by
  have h0 : τ 0 = 1 := by
    have h : τ 0 * 1 = τ 0 * τ 0 := by
      rw [mul_one]
      have h1 := hτ 0 0
      rwa [add_zero] at h1
    exact (mul_left_cancel h).symm
  have hneg : ∀ z : Fin k → ZMod p, τ (-z) = (τ z)⁻¹ := by
    intro z
    refine mul_left_cancel (a := τ z) ?_
    rw [← hτ z (-z), add_neg_cancel, h0, mul_inv_cancel]
  rw [sub_eq_add_neg, hτ, hneg]

private lemma conjAut_mul_conjAut_inv {M : Type*} [Group M] (a : MulAut M) (n : M) :
    MulAut.conj n * a * (MulAut.conj n)⁻¹ = MulAut.conj (n * (a n)⁻¹) * a := by
  ext x
  have h1 : a (n⁻¹ * x * n) = (a n)⁻¹ * a x * a n := by
    rw [map_mul, map_mul, map_inv]
  have h2 : (MulAut.conj n * a * (MulAut.conj n)⁻¹) x = n * a (n⁻¹ * x * n) * n⁻¹ := by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply]
  have h3 : (MulAut.conj (n * (a n)⁻¹) * a) x =
      (n * (a n)⁻¹) * a x * (n * (a n)⁻¹)⁻¹ := by
    rw [MulAut.mul_apply, MulAut.conj_apply]
  rw [h2, h3, h1, mul_inv_rev, inv_inv]
  group

private lemma psi_mul_inv_eq_tau {p k : ℕ} {L' R G : Type} [Group L'] [Group R] [Group G]
    {ψ : L' →* R} {ι₀ : R →* G} {A : Subgroup (MulAut L')}
    {Φ : A →* Multiplicative (Fin k → ZMod p)} {τ : (Fin k → ZMod p) → G}
    (hτ : ∀ x y, τ (x + y) = τ x * τ y)
    (hconj : ∀ (a : A) (l : L'), ι₀ (ψ ((a : MulAut L') l)) =
      τ (Multiplicative.toAdd (Φ a)) * ι₀ (ψ l) * (τ (Multiplicative.toAdd (Φ a)))⁻¹)
    {s : (Fin k → ZMod p) → Fin k → ZMod p} {r : R}
    (hr : ∀ x, ι₀ r * τ x * (ι₀ r)⁻¹ = τ (s x)) (a : A) {n : L'} (hn : ψ n = r) :
    ι₀ (ψ (n * ((a : MulAut L') n)⁻¹)) =
      τ (s (Multiplicative.toAdd (Φ a)) - Multiplicative.toAdd (Φ a)) := by
  have h1 : ι₀ (ψ (n * ((a : MulAut L') n)⁻¹)) =
      ι₀ (ψ n) * (ι₀ (ψ ((a : MulAut L') n)))⁻¹ := by simp only [map_mul, map_inv]
  rw [h1, hconj a n, hn, tau_sub hτ, ← hr (Multiplicative.toAdd (Φ a))]
  group

private lemma psi_eq_of_tau_eq {p k : ℕ} {L' R G : Type} [Group L'] [Group R] [Group G]
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hZ : Subgroup.center R = ⊥)
    {ι₀ : R →* G} (hι₀ : Function.Injective ι₀) {A : Subgroup (MulAut L')}
    {Φ : A →* Multiplicative (Fin k → ZMod p)} {τ : (Fin k → ZMod p) → G}
    (hconj : ∀ (a : A) (l : L'), ι₀ (ψ ((a : MulAut L') l)) =
      τ (Multiplicative.toAdd (Φ a)) * ι₀ (ψ l) * (τ (Multiplicative.toAdd (Φ a)))⁻¹)
    {b : A} {x y : L'} (hx : MulAut.conj x = (b : MulAut L'))
    (hy : ι₀ (ψ y) = τ (Multiplicative.toAdd (Φ b))) : ψ y = ψ x := by
  have key : ∀ l : L', ψ (y * l * y⁻¹) = ψ (x * l * x⁻¹) := by
    intro l
    apply hι₀
    have h1 : ι₀ (ψ (y * l * y⁻¹)) = τ (Multiplicative.toAdd (Φ b)) * ι₀ (ψ l) *
        (τ (Multiplicative.toAdd (Φ b)))⁻¹ := by
      simp only [map_mul, map_inv, hy]
    have h2 : ι₀ (ψ (x * l * x⁻¹)) = τ (Multiplicative.toAdd (Φ b)) * ι₀ (ψ l) *
        (τ (Multiplicative.toAdd (Φ b)))⁻¹ := by
      have hx' : (b : MulAut L') l = x * l * x⁻¹ := by rw [← hx, MulAut.conj_apply]
      rw [← hx', hconj b l]
    rw [h1, h2]
  have hconj_eq : MulAut.conj (ψ y) = MulAut.conj (ψ x) := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [MulAut.conj_apply, MulAut.conj_apply]
    have h1 : ψ y * ψ l * (ψ y)⁻¹ = ψ (y * l * y⁻¹) := by simp only [map_mul, map_inv]
    have h2 : ψ x * ψ l * (ψ x)⁻¹ = ψ (x * l * x⁻¹) := by simp only [map_mul, map_inv]
    rw [h1, h2, key l]
  have hcenter : ψ y * (ψ x)⁻¹ ∈ Subgroup.center R := by
    rw [← CFSG.GroupTheory.ker_conj_eq_center, MonoidHom.mem_ker]
    rw [map_mul, map_inv, hconj_eq, mul_inv_cancel]
  rw [hZ] at hcenter
  have h3 : ψ y * (ψ x)⁻¹ = 1 := by simpa using hcenter
  have h4 : ψ y * (ψ x)⁻¹ = ψ x * (ψ x)⁻¹ := by rw [h3, mul_inv_cancel]
  exact mul_right_cancel h4

private lemma mem_T_of_psi_eq {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    {T : Subgroup L'} (hkerT : ψ.ker ≤ T) {x y : L'} (hx : x ∈ T) (hy : ψ y = ψ x) :
    y ∈ T := by
  have hz : y * x⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy, mul_inv_cancel]
  have hy' : y = (y * x⁻¹) * x := by group
  rw [hy']
  exact T.mul_mem (hkerT hz) hx

private lemma pow_eq_one_of_psi_eq {p : ℕ} {L' R : Type} [Group L'] [Group R]
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    (hkerp : ∀ z ∈ ψ.ker, z ^ p = 1) {x y : L'} (hxp : x ^ p = 1) (hy : ψ y = ψ x) :
    y ^ p = 1 := by
  have hz : y * x⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy, mul_inv_cancel]
  have hc : Commute (y * x⁻¹) x := (Subgroup.mem_center_iff.mp (hker hz) x).symm
  have hy' : y = (y * x⁻¹) * x := by group
  rw [hy', hc.mul_pow, hkerp (y * x⁻¹) hz, hxp, mul_one]

private lemma ggHypCent_le_centralizer_comap {p k : ℕ} {L' R G : Type} [Group L'] [Group R]
    [Group G] {ψ : L' →* R} {ι₀ : R →* G} {A : Subgroup (MulAut L')}
    {Φ : A →* Multiplicative (Fin k → ZMod p)} {τ : (Fin k → ZMod p) → G}
    (hconj : ∀ (a : A) (l : L'), ι₀ (ψ ((a : MulAut L') l)) =
      τ (Multiplicative.toAdd (Φ a)) * ι₀ (ψ l) * (τ (Multiplicative.toAdd (Φ a)))⁻¹)
    {s : (Fin k → ZMod p) → Fin k → ZMod p} {n : L'}
    (hiff : ∀ a : A, MulAut.conj n * (a : MulAut L') = (a : MulAut L') * MulAut.conj n ↔
      s (Multiplicative.toAdd (Φ a)) = Multiplicative.toAdd (Φ a)) :
    ggHypCent A n ≤ ((Subgroup.centralizer ((fun a : A => τ (Multiplicative.toAdd (Φ a))) ''
      {a | s (Multiplicative.toAdd (Φ a)) = Multiplicative.toAdd (Φ a)})).comap ι₀).comap ψ := by
  intro z hz
  rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  rintro _ ⟨a, ha, rfl⟩
  have hza : (a : MulAut L') z = z :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hz (a : MulAut L')) ⟨a.2, (hiff a).mpr ha⟩
  have h1 := hconj a z
  rw [hza] at h1
  have h2 : ι₀ (ψ z) * τ (Multiplicative.toAdd (Φ a)) =
      τ (Multiplicative.toAdd (Φ a)) * ι₀ (ψ z) := by
    conv_lhs => rw [h1]
    group
  exact h2.symm

private lemma commutator_comap_le_ggHypCent {p k : ℕ} {L' R G : Type} [Group L'] [Group R]
    [Group G] {ψ : L' →* R} {ι₀ : R →* G} (hι₀ : Function.Injective ι₀)
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin k → ZMod p)}
    {τ : (Fin k → ZMod p) → G}
    (hconj : ∀ (a : A) (l : L'), ι₀ (ψ ((a : MulAut L') l)) =
      τ (Multiplicative.toAdd (Φ a)) * ι₀ (ψ l) * (τ (Multiplicative.toAdd (Φ a)))⁻¹)
    (hker : ψ.ker ≤ Subgroup.center L')
    {s : (Fin k → ZMod p) → Fin k → ZMod p} {n : L'} {S : Subgroup R}
    (hS : IsComponentOf S ((Subgroup.centralizer ((fun a : A =>
      τ (Multiplicative.toAdd (Φ a))) '' {a | s (Multiplicative.toAdd (Φ a)) =
      Multiplicative.toAdd (Φ a)})).comap ι₀))
    (hiff : ∀ a : A, MulAut.conj n * (a : MulAut L') = (a : MulAut L') * MulAut.conj n ↔
      s (Multiplicative.toAdd (Φ a)) = Multiplicative.toAdd (Φ a)) :
    ⁅S.comap ψ, S.comap ψ⁆ ≤ ggHypCent A n := by
  refine le_iInf fun a => le_iInf fun ha => ?_
  refine LayerCC.commutator_le_ggFix fun y hy => hker ?_
  have hs : s (Multiplicative.toAdd (Φ ⟨a, ha.1⟩)) =
      Multiplicative.toAdd (Φ ⟨a, ha.1⟩) := (hiff ⟨a, ha.1⟩).mp ha.2
  have hc : τ (Multiplicative.toAdd (Φ ⟨a, ha.1⟩)) * ι₀ (ψ y) =
      ι₀ (ψ y) * τ (Multiplicative.toAdd (Φ ⟨a, ha.1⟩)) :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_comap.mp (hS.1 (Subgroup.mem_comap.mp hy))) _
      ⟨⟨a, ha.1⟩, hs, rfl⟩
  have hψay : ψ ((a : MulAut L') y) = ψ y := by
    apply hι₀
    rw [hconj ⟨a, ha.1⟩ y, hc]
    group
  rw [MonoidHom.mem_ker, map_mul, map_inv, hψay, inv_mul_cancel]

private lemma exists_lift_data {p k : ℕ} {L' R G : Type} [Group L'] [Group R] [Group G]
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hZ : Subgroup.center R = ⊥)
    (hker : ψ.ker ≤ Subgroup.center L') (hkerp : ∀ z ∈ ψ.ker, z ^ p = 1)
    {ι₀ : R →* G} (hι₀ : Function.Injective ι₀) {A : Subgroup (MulAut L')}
    {Φ : A →* Multiplicative (Fin k → ZMod p)} {τ : (Fin k → ZMod p) → G}
    (hτ : ∀ x y, τ (x + y) = τ x * τ y)
    (hconj : ∀ (a : A) (l : L'), ι₀ (ψ ((a : MulAut L') l)) =
      τ (Multiplicative.toAdd (Φ a)) * ι₀ (ψ l) * (τ (Multiplicative.toAdd (Φ a)))⁻¹)
    {T : Subgroup L'} (hkerT : ψ.ker ≤ T)
    {ι : Type} {s : ι → (Fin k → ZMod p) → Fin k → ZMod p} {r : ι → R} {n : ι → L'}
    (hnψ : ∀ i, ψ (n i) = r i)
    (hr : ∀ (i : ι) (x : Fin k → ZMod p), ι₀ (r i) * τ x * (ι₀ (r i))⁻¹ = τ (s i x))
    (hTs : ∀ (i : ι) (a : A), ∃ x ∈ T, x ^ p = 1 ∧ ∃ b : A, MulAut.conj x = (b : MulAut L') ∧
      Multiplicative.toAdd (Φ b) =
        s i (Multiplicative.toAdd (Φ a)) - Multiplicative.toAdd (Φ a)) :
    ∃ b : ι → A → A,
      (∀ (i : ι) (a : A), MulAut.conj (n i) * (a : MulAut L') * (MulAut.conj (n i))⁻¹ =
        ((b i a * a : A) : MulAut L')) ∧
      (∀ (i : ι) (a : A), Multiplicative.toAdd (Φ (b i a)) =
        s i (Multiplicative.toAdd (Φ a)) - Multiplicative.toAdd (Φ a)) ∧
      (∀ (i : ι) (a : A), n i * ((a : MulAut L') (n i))⁻¹ ∈ T) ∧
      (∀ (i : ι) (a : A), (n i * ((a : MulAut L') (n i))⁻¹) ^ p = 1) := by
  have hdata : ∀ (i : ι) (a : A), ∃ b : A,
      MulAut.conj (n i) * (a : MulAut L') * (MulAut.conj (n i))⁻¹ =
        ((b * a : A) : MulAut L') ∧
      Multiplicative.toAdd (Φ b) = s i (Multiplicative.toAdd (Φ a)) -
        Multiplicative.toAdd (Φ a) ∧
      n i * ((a : MulAut L') (n i))⁻¹ ∈ T ∧ (n i * ((a : MulAut L') (n i))⁻¹) ^ p = 1 := by
    intro i a
    obtain ⟨x, hxT, hxp, b, hcx, hΦb⟩ := hTs i a
    have hytau : ι₀ (ψ (n i * ((a : MulAut L') (n i))⁻¹)) =
        τ (Multiplicative.toAdd (Φ b)) := by
      rw [hΦb]
      exact psi_mul_inv_eq_tau hτ hconj (hr i) a (hnψ i)
    have hψy : ψ (n i * ((a : MulAut L') (n i))⁻¹) = ψ x :=
      psi_eq_of_tau_eq hψ hZ hι₀ hconj hcx hytau
    refine ⟨b, ?_, hΦb, mem_T_of_psi_eq hkerT hxT hψy,
      pow_eq_one_of_psi_eq hker hkerp hxp hψy⟩
    rw [conjAut_mul_conjAut_inv, (ReflInner.conj_eq_conj_of_map_eq hker hψy).trans hcx,
      Subgroup.coe_mul]
  choose b hb hΦb hyT hyp using hdata
  exact ⟨b, hb, hΦb, hyT, hyp⟩

private lemma exists_sigma_of_lift_data {p k : ℕ} {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin k → ZMod p)}
    (hΦ : Function.Injective Φ) {ι : Type}
    {s : ι → (Fin k → ZMod p) → Fin k → ZMod p} {n : ι → L'} {b : ι → A → A}
    (hb : ∀ (i : ι) (a : A), MulAut.conj (n i) * (a : MulAut L') *
      (MulAut.conj (n i))⁻¹ = ((b i a * a : A) : MulAut L'))
    (hΦb : ∀ (i : ι) (a : A), Multiplicative.toAdd (Φ (b i a)) =
      s i (Multiplicative.toAdd (Φ a)) - Multiplicative.toAdd (Φ a))
    (hinv : ∀ (i : ι) (a : A), s i (s i (Multiplicative.toAdd (Φ a))) =
      Multiplicative.toAdd (Φ a)) :
    ∃ σ : ι → A → A,
      (∀ (i : ι) (a : A), ((σ i a : A) : MulAut L') =
        MulAut.conj (n i) * (a : MulAut L') * (MulAut.conj (n i))⁻¹) ∧
      (∀ (i : ι) (a : A), Multiplicative.toAdd (Φ (σ i a)) =
        s i (Multiplicative.toAdd (Φ a))) ∧
      (∀ (i : ι) (a : A), σ i (σ i a) = a) := by
  let σ : ι → A → A := fun i a => b i a * a
  have hσ : ∀ (i : ι) (a : A), ((σ i a : A) : MulAut L') =
      MulAut.conj (n i) * (a : MulAut L') * (MulAut.conj (n i))⁻¹ := fun i a => (hb i a).symm
  have hΦσ : ∀ (i : ι) (a : A), Multiplicative.toAdd (Φ (σ i a)) =
      s i (Multiplicative.toAdd (Φ a)) := by
    intro i a
    have h1 : Multiplicative.toAdd (Φ (b i a * a)) =
        Multiplicative.toAdd (Φ (b i a)) + Multiplicative.toAdd (Φ a) := by
      rw [map_mul, toAdd_mul]
    rw [show σ i a = b i a * a from rfl, h1, hΦb i a, sub_add_cancel]
  refine ⟨σ, hσ, hΦσ, ?_⟩
  intro i a
  apply hΦ
  apply Multiplicative.ext
  rw [hΦσ i (σ i a), hΦσ i a, hinv i a]

private lemma conj_commute_iff_of_sigma {p k : ℕ} {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin k → ZMod p)}
    (hΦ : Function.Injective Φ) {ι : Type}
    {s : ι → (Fin k → ZMod p) → Fin k → ZMod p} {n : ι → L'} {σ : ι → A → A}
    (hσ : ∀ (i : ι) (a : A), ((σ i a : A) : MulAut L') =
      MulAut.conj (n i) * (a : MulAut L') * (MulAut.conj (n i))⁻¹)
    (hΦσ : ∀ (i : ι) (a : A), Multiplicative.toAdd (Φ (σ i a)) =
      s i (Multiplicative.toAdd (Φ a))) :
    ∀ (i : ι) (a : A), MulAut.conj (n i) * (a : MulAut L') =
      (a : MulAut L') * MulAut.conj (n i) ↔
      s i (Multiplicative.toAdd (Φ a)) = Multiplicative.toAdd (Φ a) := by
  intro i a
  constructor
  · intro h
    have h1 : σ i a = a := by
      apply Subtype.ext
      rw [hσ i a, h, mul_assoc, mul_inv_cancel, mul_one]
    rw [← hΦσ i a, h1]
  · intro h
    have h1 : σ i a = a := by
      apply hΦ
      apply Multiplicative.ext
      rw [hΦσ i a, h]
    have h2 : MulAut.conj (n i) * (a : MulAut L') * (MulAut.conj (n i))⁻¹ =
        (a : MulAut L') := by
      rw [← hσ i a, h1]
    calc MulAut.conj (n i) * (a : MulAut L')
        = (MulAut.conj (n i) * (a : MulAut L') * (MulAut.conj (n i))⁻¹) *
            MulAut.conj (n i) := by group
      _ = (a : MulAut L') * MulAut.conj (n i) := by rw [h2]

private lemma normalizer_weyl_of_sigma {p : ℕ} {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} {T : Subgroup L'} {ι : Type}
    {n : ι → L'} {σ : ι → A → A}
    (hσ : ∀ (i : ι) (a : A), ((σ i a : A) : MulAut L') =
      MulAut.conj (n i) * (a : MulAut L') * (MulAut.conj (n i))⁻¹)
    (hσ2 : ∀ (i : ι) (a : A), σ i (σ i a) = a)
    (hTA : ∀ a ∈ A, ∀ x ∈ T, a x = x)
    (hyT : ∀ (i : ι) (a : A), n i * ((a : MulAut L') (n i))⁻¹ ∈ T)
    (hyp : ∀ (i : ι) (a : A), (n i * ((a : MulAut L') (n i))⁻¹) ^ p = 1) :
    ∃ hnN : ∀ i, MulAut.conj (n i) ∈ Subgroup.normalizer (A : Set (MulAut L')),
      (∀ i, GGTorusWeylElt p A (n i)) ∧
      (∀ (i : ι) (a : A), ggConjAut A (hnN i) a = σ i a) := by
  have hmapA : ∀ i, A.map (MulAut.conj (MulAut.conj (n i))) = A := by
    intro i
    refine le_antisymm ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      change MulAut.conj (MulAut.conj (n i)) a ∈ A
      rw [MulAut.conj_apply, ← hσ i ⟨a, ha⟩]
      exact (σ i ⟨a, ha⟩).2
    · intro a ha
      refine Subgroup.mem_map.mpr ⟨σ i ⟨a, ha⟩, (σ i ⟨a, ha⟩).2, ?_⟩
      change MulAut.conj (MulAut.conj (n i)) ((σ i ⟨a, ha⟩ : A) : MulAut L') = a
      rw [MulAut.conj_apply, ← hσ i (σ i ⟨a, ha⟩)]
      exact congrArg Subtype.val (hσ2 i ⟨a, ha⟩)
  have hnN : ∀ i, MulAut.conj (n i) ∈ Subgroup.normalizer (A : Set (MulAut L')) := fun i =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hmapA i)
  refine ⟨hnN, fun i a ha => ⟨hyp i ⟨a, ha⟩,
    fun a' ha' => hTA a' ha' _ (hyT i ⟨a, ha⟩)⟩, ?_⟩
  intro i a
  apply Subtype.ext
  exact (ggConjAut_apply A (hnN i) a).trans (hσ i a).symm

private lemma isReflection_of_sigma {p k : ℕ} {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin k → ZMod p)}
    (hΦ : Function.Injective Φ) {ι : Type}
    {s : ι → (Fin k → ZMod p) → Fin k → ZMod p} {n : ι → L'} {σ : ι → A → A}
    {hnN : ∀ i, MulAut.conj (n i) ∈ Subgroup.normalizer (A : Set (MulAut L'))}
    (hgg : ∀ (i : ι) (a : A), ggConjAut A (hnN i) a = σ i a)
    (hΦσ : ∀ (i : ι) (a : A), Multiplicative.toAdd (Φ (σ i a)) =
      s i (Multiplicative.toAdd (Φ a)))
    (hinv : ∀ (i : ι) (a : A), s i (s i (Multiplicative.toAdd (Φ a))) =
      Multiplicative.toAdd (Φ a))
    (hfix : ∀ i, Nat.card {a : A // s i (Multiplicative.toAdd (Φ a)) =
      Multiplicative.toAdd (Φ a)} * p = Nat.card A) :
    ∀ i, GGIsReflection p (ggConjAut A (hnN i)) := by
  have hΦconj : ∀ (i : ι) (a : A), Multiplicative.toAdd (Φ (ggConjAut A (hnN i) a)) =
      s i (Multiplicative.toAdd (Φ a)) := by
    intro i a
    rw [hgg i a, hΦσ i a]
  intro i
  refine ⟨?_, ?_⟩
  · apply MulEquiv.ext
    intro a
    apply hΦ
    apply Multiplicative.ext
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply]
    rw [hΦconj i (ggConjAut A (hnN i) a), hΦconj i a, hinv i a]
  · have hiff2 : ∀ a : A, ggConjAut A (hnN i) a = a ↔
        s i (Multiplicative.toAdd (Φ a)) = Multiplicative.toAdd (Φ a) := by
      intro a
      constructor
      · intro h
        have h1 := congrArg (fun x : A => Multiplicative.toAdd (Φ x)) h
        rwa [hΦconj i a] at h1
      · intro h
        apply hΦ
        apply Multiplicative.ext
        rw [hΦconj i a, h]
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff2), hfix i]

private lemma isComponentOf_of_lift_data {p k : ℕ} {L' R G : Type} [Group L'] [Group R]
    [Group G] {ψ : L' →* R} (hψ : Function.Surjective ψ) {ι₀ : R →* G}
    (hι₀ : Function.Injective ι₀) {A : Subgroup (MulAut L')}
    {Φ : A →* Multiplicative (Fin k → ZMod p)} {τ : (Fin k → ZMod p) → G}
    (hconj : ∀ (a : A) (l : L'), ι₀ (ψ ((a : MulAut L') l)) =
      τ (Multiplicative.toAdd (Φ a)) * ι₀ (ψ l) * (τ (Multiplicative.toAdd (Φ a)))⁻¹)
    (hker : ψ.ker ≤ Subgroup.center L')
    {ι : Type} {s : ι → (Fin k → ZMod p) → Fin k → ZMod p} {n : ι → L'}
    {S : ι → Subgroup R}
    (hS : ∀ i, IsComponentOf (S i) ((Subgroup.centralizer ((fun a : A =>
      τ (Multiplicative.toAdd (Φ a))) '' {a | s i (Multiplicative.toAdd (Φ a)) =
      Multiplicative.toAdd (Φ a)})).comap ι₀))
    (hiff : ∀ (i : ι) (a : A), MulAut.conj (n i) * (a : MulAut L') =
      (a : MulAut L') * MulAut.conj (n i) ↔
      s i (Multiplicative.toAdd (Φ a)) = Multiplicative.toAdd (Φ a)) :
    ∀ i, IsComponentOf ⁅(S i).comap ψ, (S i).comap ψ⁆ (ggHypCent A (n i)) := by
  intro i
  have hHle : ggHypCent A (n i) ≤ ((Subgroup.centralizer ((fun a : A =>
      τ (Multiplicative.toAdd (Φ a))) '' {a | s i (Multiplicative.toAdd (Φ a)) =
      Multiplicative.toAdd (Φ a)})).comap ι₀).comap ψ :=
    ggHypCent_le_centralizer_comap hconj (hiff i)
  have hJle : ⁅(S i).comap ψ, (S i).comap ψ⁆ ≤ ggHypCent A (n i) :=
    commutator_comap_le_ggHypCent hι₀ hconj hker (hS i) (hiff i)
  refine ⟨hJle, ?_, ?_⟩
  · have hJsub : IsSubnormal ⁅(S i).comap ψ, (S i).comap ψ⁆ ((S i).comap ψ) :=
      IsSubnormal.step (CFSG.RankThree.PartOne.KCUnitary.commutator_self_le _)
        ⟨fun x hx g => CFSG.RankThree.PartOne.KCUnitary.conj_mem_commutator_self g.2 hx⟩
        (IsSubnormal.refl _)
    exact LayerCC.isSubnormal_of_le (hJsub.trans ((hS i).2.1.comap ψ)) hJle hHle
  · exact (TableBSymp.isQuasisimple_iff ↥⁅(S i).comap ψ, (S i).comap ψ⁆).mpr
      (CFSG.RankThree.PartOne.S15K.isQuasisimple_commutator_comap hψ hker
        ((TableBSymp.isQuasisimple_iff ↥(S i)).mp (hS i).2.2))

private lemma card_dvd_of_lift_data {p : ℕ} {L' R : Type} [Group L'] [Group R]
    {ψ : L' →* R} {ι : Type} {S : ι → Subgroup R} {J : ι → Subgroup L'}
    (hdvd : ∀ i, p ∣ Nat.card (S i)) (hJmap : ∀ i, (J i).map ψ = S i) :
    ∀ i, p ∣ Nat.card (J i) := by
  intro i
  refine (hdvd i).trans ?_
  rw [← hJmap i]
  exact Subgroup.card_map_dvd (J i) ψ

private lemma rootGenAvoid_of_lift_data {p k : ℕ} {L' R : Type} [Group L']
    [Group R] {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin k → ZMod p)}
    {ι : Type} [Nonempty ι] {s : ι → (Fin k → ZMod p) → Fin k → ZMod p}
    {S : ι → Subgroup R} {J : ι → Subgroup L'} {n : ι → L'}
    (hgen : ∀ j, (⨆ (i : ι) (_ : ∃ a : A, s i (Multiplicative.toAdd (Φ a)) ≠
      s j (Multiplicative.toAdd (Φ a))), S i) = ⊤)
    (hJmap : ∀ i, (J i).map ψ = S i)
    (hnN : ∀ i, MulAut.conj (n i) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hWeyl : ∀ i, GGTorusWeylElt p A (n i))
    (hrefl : ∀ i, GGIsReflection p (ggConjAut A (hnN i)))
    (hΦconj : ∀ (i : ι) (a : A), Multiplicative.toAdd (Φ (ggConjAut A (hnN i) a)) =
      s i (Multiplicative.toAdd (Φ a)))
    (hnJ : ∀ i, n i ∈ J i)
    (hcomp : ∀ i, IsComponentOf (J i) (ggHypCent A (n i)))
    (hdvdJ : ∀ i, p ∣ Nat.card (J i)) :
    GGTorusRootGenAvoid p A := by
  intro ρ
  have hexj : ∃ j : ι, ∀ i : ι, (∃ a : A, s i (Multiplicative.toAdd (Φ a)) ≠
      s j (Multiplicative.toAdd (Φ a))) → ggConjAut A (hnN i) ≠ ρ := by
    by_cases hcase : ∃ j : ι, ggConjAut A (hnN j) = ρ
    · obtain ⟨j, hj⟩ := hcase
      refine ⟨j, fun i hi hEq => ?_⟩
      obtain ⟨a, ha⟩ := hi
      apply ha
      have h1 : ggConjAut A (hnN i) a = ggConjAut A (hnN j) a := by rw [hEq, hj]
      have h2 := congrArg (fun x : A => Multiplicative.toAdd (Φ x)) h1
      rwa [hΦconj i a, hΦconj j a] at h2
    · obtain ⟨j⟩ := ‹Nonempty ι›
      exact ⟨j, fun i _ hEq => hcase ⟨i, hEq⟩⟩
  obtain ⟨j, hj⟩ := hexj
  let P : ι → Prop := fun i => ∃ a : A, s i (Multiplicative.toAdd (Φ a)) ≠
    s j (Multiplicative.toAdd (Φ a))
  let X : Subgroup L' := ⨆ (i : ι) (_ : P i), J i
  have hXle : X ≤ ⨆ (n' : L') (hn : MulAut.conj n' ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (J' : Subgroup L') (_ : GGTorusWeylElt p A n' ∧ GGIsReflection p (ggConjAut A hn) ∧
        ggConjAut A hn ≠ ρ ∧ n' ∈ J' ∧ IsComponentOf J' (ggHypCent A n') ∧
        p ∣ Nat.card J'), J' := by
    refine iSup_le fun i => iSup_le fun hi => ?_
    exact le_iSup_of_le (n i) (le_iSup_of_le (hnN i) (le_iSup_of_le (J i)
      (le_iSup_of_le ⟨hWeyl i, hrefl i, hj i hi, hnJ i, hcomp i, hdvdJ i⟩ le_rfl)))
  have hXmap : X.map ψ = ⊤ := by
    have h1 : X.map ψ = ⨆ (i : ι) (_ : P i), S i := by
      change (⨆ (i : ι) (_ : P i), J i).map ψ = _
      rw [Subgroup.map_iSup]
      simp only [Subgroup.map_iSup, hJmap]
    rw [h1]
    exact hgen j
  have htop : ⊤ ≤ X := by
    have hY : ⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ = ⊤ := by
      rw [← commutator_def]
      exact hperf
    have h2 : (⊤ : Subgroup L').map ψ ≤ ⨆ _ : Unit, X.map ψ := by
      rw [Subgroup.map_top_of_surjective ψ hψ]
      simp only [iSup_const, hXmap, le_top]
    have h1 := CFSG.RankThree.PartOne.S15K.le_iSup_of_isPerfect_of_map_le (ι := Unit)
      (Φ := ψ) hker (Q := fun _ => X) (F := fun _ => X.map ψ) (Y := ⊤) (fun _ => rfl) hY h2
    simpa using h1
  exact eq_top_iff.mpr (htop.trans hXle)

theorem exists_lift_of_coverTorus {p k : ℕ} {L' R G : Type} [Group L'] [Finite L']
    [Group R] [Group G] {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hZ : Subgroup.center R = ⊥) (hkerp : ∀ z ∈ ψ.ker, z ^ p = 1)
    {ι₀ : R →* G} (hι₀ : Function.Injective ι₀)
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin k → ZMod p)}
    (hΦ : Function.Injective Φ) {τ : (Fin k → ZMod p) → G}
    (hτ : ∀ x y, τ (x + y) = τ x * τ y)
    (hconj : ∀ (a : A) (l : L'), ι₀ (ψ ((a : MulAut L') l)) =
      τ (Multiplicative.toAdd (Φ a)) * ι₀ (ψ l) * (τ (Multiplicative.toAdd (Φ a)))⁻¹)
    {T : Subgroup L'} (hTA : ∀ a ∈ A, ∀ x ∈ T, a x = x) (hkerT : ψ.ker ≤ T)
    {ι : Type} {s : ι → (Fin k → ZMod p) → Fin k → ZMod p}
    {r : ι → R} {S : ι → Subgroup R}
    (hr : ∀ i x, ι₀ (r i) * τ x * (ι₀ (r i))⁻¹ = τ (s i x))
    (hinv : ∀ i (a : A),
      s i (s i (Multiplicative.toAdd (Φ a))) = Multiplicative.toAdd (Φ a))
    (hfix : ∀ i, Nat.card {a : A // s i (Multiplicative.toAdd (Φ a)) =
      Multiplicative.toAdd (Φ a)} * p = Nat.card A)
    (hTs : ∀ i (a : A), ∃ x ∈ T, x ^ p = 1 ∧ ∃ b : A, MulAut.conj x = (b : MulAut L') ∧
      Multiplicative.toAdd (Φ b) =
        s i (Multiplicative.toAdd (Φ a)) - Multiplicative.toAdd (Φ a))
    (hrS : ∀ i, r i ∈ S i)
    (hS : ∀ i, IsComponentOf (S i) ((Subgroup.centralizer
      ((fun a : A => τ (Multiplicative.toAdd (Φ a))) ''
        {a | s i (Multiplicative.toAdd (Φ a)) = Multiplicative.toAdd (Φ a)})).comap ι₀))
    (hdvd : ∀ i, p ∣ Nat.card (S i)) :
    ∃ (J : ι → Subgroup L') (n : ι → L')
      (hnN : ∀ i, MulAut.conj (n i) ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      (∀ i, J i = ⁅(S i).comap ψ, (S i).comap ψ⁆) ∧ (∀ i, (J i).map ψ = S i) ∧
      (∀ i, n i ∈ J i) ∧ (∀ i, ψ (n i) = r i) ∧ (∀ i, GGTorusWeylElt p A (n i)) ∧
      (∀ i, GGIsReflection p (ggConjAut A (hnN i))) ∧
      (∀ (i : ι) (a : A), Multiplicative.toAdd (Φ (ggConjAut A (hnN i) a)) =
        s i (Multiplicative.toAdd (Φ a))) ∧
      (∀ i, IsComponentOf (J i) (ggHypCent A (n i))) ∧ (∀ i, p ∣ Nat.card (J i)) := by
  classical
  have hSperf : ∀ i, ⁅S i, S i⁆ = S i := fun i =>
    Subgroup.isPerfect_iff.1 ((TableBSymp.isQuasisimple_iff ↥(S i)).mp (hS i).2.2).1
  let J : ι → Subgroup L' := fun i => ⁅(S i).comap ψ, (S i).comap ψ⁆
  have hJmap : ∀ i, (J i).map ψ = S i := fun i =>
    CFSG.RankThree.PartOne.S15K.map_commutator_comap hψ (hSperf i)
  have hexn : ∀ i, ∃ n ∈ J i, ψ n = r i := by
    intro i
    have hmem : r i ∈ (J i).map ψ := by rw [hJmap i]; exact hrS i
    obtain ⟨n, hn, hψn⟩ := Subgroup.mem_map.mp hmem
    exact ⟨n, hn, hψn⟩
  choose n hnJ hnψ using hexn
  obtain ⟨b, hb, hΦb, hyT, hyp⟩ := exists_lift_data hψ hZ hker hkerp hι₀ hτ hconj
    hkerT hnψ hr hTs
  obtain ⟨σ, hσ, hΦσ, hσ2⟩ := exists_sigma_of_lift_data hΦ hb hΦb hinv
  have hiff := conj_commute_iff_of_sigma hΦ hσ hΦσ
  obtain ⟨hnN, hWeyl, hgg⟩ := normalizer_weyl_of_sigma hσ hσ2 hTA hyT hyp
  have hrefl := isReflection_of_sigma (hnN := hnN) hΦ hgg hΦσ hinv hfix
  have hΦconj : ∀ (i : ι) (a : A),
      Multiplicative.toAdd (Φ (ggConjAut A (hnN i) a)) =
        s i (Multiplicative.toAdd (Φ a)) := by
    intro i a
    rw [hgg i a, hΦσ i a]
  exact ⟨J, n, hnN, fun _ => rfl, hJmap, hnJ, hnψ, hWeyl, hrefl, hΦconj,
    isComponentOf_of_lift_data hψ hι₀ hconj hker hS hiff, card_dvd_of_lift_data hdvd hJmap⟩

theorem ggTorusRootGenAvoid_of_coverTorus {p k : ℕ} {L' R G : Type} [Group L'] [Finite L']
    [Group R] [Group G] {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hZ : Subgroup.center R = ⊥) (hkerp : ∀ z ∈ ψ.ker, z ^ p = 1)
    {ι₀ : R →* G} (hι₀ : Function.Injective ι₀)
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin k → ZMod p)}
    (hΦ : Function.Injective Φ) {τ : (Fin k → ZMod p) → G}
    (hτ : ∀ x y, τ (x + y) = τ x * τ y)
    (hconj : ∀ (a : A) (l : L'), ι₀ (ψ ((a : MulAut L') l)) =
      τ (Multiplicative.toAdd (Φ a)) * ι₀ (ψ l) * (τ (Multiplicative.toAdd (Φ a)))⁻¹)
    {T : Subgroup L'} (hTA : ∀ a ∈ A, ∀ x ∈ T, a x = x) (hkerT : ψ.ker ≤ T)
    {ι : Type} [Nonempty ι] {s : ι → (Fin k → ZMod p) → Fin k → ZMod p}
    {r : ι → R} {S : ι → Subgroup R}
    (hr : ∀ i x, ι₀ (r i) * τ x * (ι₀ (r i))⁻¹ = τ (s i x))
    (hinv : ∀ i (a : A),
      s i (s i (Multiplicative.toAdd (Φ a))) = Multiplicative.toAdd (Φ a))
    (hfix : ∀ i, Nat.card {a : A // s i (Multiplicative.toAdd (Φ a)) =
      Multiplicative.toAdd (Φ a)} * p = Nat.card A)
    (hTs : ∀ i (a : A), ∃ x ∈ T, x ^ p = 1 ∧ ∃ b : A, MulAut.conj x = (b : MulAut L') ∧
      Multiplicative.toAdd (Φ b) =
        s i (Multiplicative.toAdd (Φ a)) - Multiplicative.toAdd (Φ a))
    (hrS : ∀ i, r i ∈ S i)
    (hS : ∀ i, IsComponentOf (S i) ((Subgroup.centralizer
      ((fun a : A => τ (Multiplicative.toAdd (Φ a))) ''
        {a | s i (Multiplicative.toAdd (Φ a)) = Multiplicative.toAdd (Φ a)})).comap ι₀))
    (hdvd : ∀ i, p ∣ Nat.card (S i))
    (hgen : ∀ j, (⨆ (i : ι) (_ : ∃ a : A, s i (Multiplicative.toAdd (Φ a)) ≠
      s j (Multiplicative.toAdd (Φ a))), S i) = ⊤) :
    GGTorusRootGenAvoid p A := by
  obtain ⟨J, n, hnN, -, hJmap, hnJ, -, hWeyl, hrefl, hΦconj, hcomp, hdvdJ⟩ :=
    exists_lift_of_coverTorus hψ hker hZ hkerp hι₀ hΦ hτ hconj hTA hkerT hr hinv hfix hTs hrS hS
      hdvd
  exact rootGenAvoid_of_lift_data hψ hker hperf hgen hJmap hnN hWeyl hrefl hΦconj hnJ
    hcomp hdvdJ

end CFSG.StandardType

end
