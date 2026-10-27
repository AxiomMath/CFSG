module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20v

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Subgroup Matrix

section Torus

variable {k : Type} [Field k] [Finite k]

theorem uc22pwlie_exists_zeta {p : ℕ} (hp : p.Prime) (hpk : p ∣ Nat.card k - 1) :
    ∃ ζ : kˣ, orderOf ζ = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card kˣ = Nat.card k - 1 := by
    rw [Nat.card_units]
  rw [← hcard] at hpk
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpk
  exact ⟨ζ, hζ⟩

end Torus

section Diag

variable {k : Type} [Field k] [Finite k]

@[expose] noncomputable def uc22pwlie_prodHom (μ : Subgroup kˣ) (m : ℕ) : (Fin m → μ) →* μ where
  toFun g := ∏ i, g i
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib]

@[expose] noncomputable def uc22pwlie_diagSL (μ : Subgroup kˣ) (m : ℕ) (g : (uc22pwlie_prodHom μ m).ker) :
    SpecialLinearGroup (Fin m) k :=
  ⟨Matrix.diagonal (fun i => (((g.1 i : μ) : kˣ) : k)), by
    rw [Matrix.det_diagonal]
    have h1 : ∏ i, g.1 i = 1 := g.2
    have h2 := map_prod ((Units.coeHom k).comp μ.subtype) g.1 Finset.univ
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, Subgroup.coe_subtype] at h2
    rw [← h2, h1]
    simp⟩

theorem uc22pwlie_diagSL_coe (μ : Subgroup kˣ) (m : ℕ) (g : (uc22pwlie_prodHom μ m).ker) :
    ((uc22pwlie_diagSL μ m g : SpecialLinearGroup (Fin m) k) : Matrix (Fin m) (Fin m) k) =
      Matrix.diagonal (fun i => (((g.1 i : μ) : kˣ) : k)) := rfl

@[expose] noncomputable def uc22pwlie_diagHom (μ : Subgroup kˣ) (m : ℕ) :
    (uc22pwlie_prodHom μ m).ker →* SpecialLinearGroup (Fin m) k where
  toFun := uc22pwlie_diagSL μ m
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [uc22pwlie_diagSL_coe, Matrix.SpecialLinearGroup.coe_one]
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  map_mul' a b := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, uc22pwlie_diagSL_coe, uc22pwlie_diagSL_coe, uc22pwlie_diagSL_coe,
      Matrix.diagonal_mul_diagonal]
    simp [Matrix.diagonal_apply]

theorem uc22pwlie_diagHom_coe (μ : Subgroup kˣ) (m : ℕ) (g : (uc22pwlie_prodHom μ m).ker) :
    ((uc22pwlie_diagHom μ m g : SpecialLinearGroup (Fin m) k) : Matrix (Fin m) (Fin m) k) =
      Matrix.diagonal (fun i => (((g.1 i : μ) : kˣ) : k)) := rfl

theorem uc22pwlie_diag_const {μ : Subgroup kˣ} {m : ℕ} {g : (uc22pwlie_prodHom μ m).ker}
    (hg : uc22pwlie_diagHom μ m g ∈ scalars m k) (i j : Fin m) : g.1 i = g.1 j := by
  obtain ⟨c, -, hc⟩ := hg
  rw [uc22pwlie_diagHom_coe] at hc
  have hi := congr_fun (congr_fun hc i) i
  have hj := congr_fun (congr_fun hc j) j
  simp only [Matrix.diagonal_apply_eq, Matrix.scalar_apply] at hi hj
  exact Subtype.ext (Units.ext (hi.trans hj.symm))

theorem uc22pwlie_prodHom_surjective (μ : Subgroup kˣ) {m : ℕ} (hm : 1 ≤ m) :
    Function.Surjective (uc22pwlie_prodHom μ m) := by
  intro z
  refine ⟨Pi.mulSingle ⟨0, hm⟩ z, ?_⟩
  change ∏ i, (Pi.mulSingle (⟨0, hm⟩ : Fin m) z : Fin m → μ) i = z
  rw [Finset.prod_eq_single (⟨0, hm⟩ : Fin m)]
  · simp
  · intro b _ hb
    simp [Pi.mulSingle_eq_of_ne hb]
  · simp

theorem uc22pwlie_card_ker_prod_mul (μ : Subgroup kˣ) {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (uc22pwlie_prodHom μ m).ker * Nat.card μ = Nat.card μ ^ m := by
  rw [Subgroup.card_ker_mul_card_of_surjective (uc22pwlie_prodHom_surjective μ hm)]
  simp [Nat.card_fun]

end Diag

section Cover

variable {k : Type} [Field k] [Finite k]

theorem uc22pwlie_range_isElemAbelian {A X : Type} [CommGroup A] [Group X] (ψ : A →* X) {p : ℕ}
    (h : ∀ a : A, a ^ p = 1) : IsElemAbelian p ψ.range := by
  refine ⟨IsMulCommutative.of_setLike_mul_comm fun x hx y hy => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, h a, map_one]

theorem uc22pwlie_ker_pow {μ : Subgroup kˣ} {p : ℕ} (hμ : ∀ x : μ, x ^ p = 1) (m : ℕ)
    (a : (uc22pwlie_prodHom μ m).ker) : a ^ p = 1 :=
  Subtype.ext (funext fun i => hμ (a.1 i))

theorem uc22pwlie_card_ker_le {m : ℕ} (hm : 1 ≤ m) (μ : Subgroup kˣ) {X : Type} [Group X]
    (α : SpecialLinearGroup (Fin m) k →* X) (hαc : α.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) k)) :
    Nat.card (α.comp (uc22pwlie_diagHom μ m)).ker ≤ Nat.card μ := by
  have hs : ∀ g : (α.comp (uc22pwlie_diagHom μ m)).ker, ∀ i, g.1.1 i = g.1.1 ⟨0, hm⟩ := by
    intro g i
    refine uc22pwlie_diag_const ?_ i ⟨0, hm⟩
    rw [scalars_eq_center]
    exact hαc (MonoidHom.mem_ker.2 g.2)
  refine Nat.card_le_card_of_injective (fun g => g.1.1 ⟨0, hm⟩) ?_
  intro g g' h
  refine Subtype.ext (Subtype.ext (funext fun i => ?_))
  rw [hs g i, hs g' i]
  exact h

theorem uc22pwlie_card_range_ge {m : ℕ} (hm : 2 ≤ m) {μ : Subgroup kˣ} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card μ = p) {X : Type} [Group X] (α : SpecialLinearGroup (Fin m) k →* X)
    (hαc : α.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) k)) :
    p ^ (m - 2) ≤ Nat.card (α.comp (uc22pwlie_diagHom μ m)).range := by
  have h1 := Subgroup.card_ker_mul_card_range (α.comp (uc22pwlie_diagHom μ m))
  have h2 := uc22pwlie_card_ker_prod_mul μ (by omega : 1 ≤ m)
  have h3 := uc22pwlie_card_ker_le (by omega : 1 ≤ m) μ α hαc
  rw [hcard] at h2 h3
  have hp0 : 0 < p := hp.pos
  have e1 : p ^ (m - 2) * p ^ 2 = p ^ m := by
    rw [← pow_add]
    congr 1
    omega
  have h4 : p ^ (m - 2) * p ^ 2 ≤ Nat.card (α.comp (uc22pwlie_diagHom μ m)).range * p ^ 2 := by
    rw [e1, ← h2, ← h1]
    calc Nat.card (α.comp (uc22pwlie_diagHom μ m)).ker * Nat.card (α.comp (uc22pwlie_diagHom μ m)).range * p
        ≤ p * Nat.card (α.comp (uc22pwlie_diagHom μ m)).range * p := by gcongr
      _ = Nat.card (α.comp (uc22pwlie_diagHom μ m)).range * p ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_right h4 (by positivity)

theorem uc22pwlie_range_le_normalizer (μ : Subgroup kˣ) (m : ℕ) {X : Type} [Group X]
    (α : SpecialLinearGroup (Fin m) k →* X) :
    (α.comp (uc22pwlie_diagHom μ m)).range ≤
      normalizer (((unitriangular m k).map α : Subgroup X) : Set X) := by
  rintro _ ⟨a, rfl⟩
  have hd : uc22pwlie_diagHom μ m a ∈
      normalizer (unitriangular m k : Set (SpecialLinearGroup (Fin m) k)) := by
    rw [normalizer_unitriangular]
    refine mem_upperTriangular.2 fun i j hij => ?_
    rw [uc22pwlie_diagHom_coe, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]
  exact Subgroup.le_normalizer_map α ⟨_, hd, rfl⟩

end Cover

section Witness

theorem uc22pwlie_borelWit_of_sylow {X : Type} [Group X] [Finite X] {p k : ℕ} (P₀ : Sylow 2 X)
    (F₀ : Subgroup X) (hN : F₀ ≤ normalizer (P₀ : Set X)) (hF : IsElemAbelian p F₀)
    (hc : Nat.card F₀ = p ^ k) : uc22p20oBorelWit X p k := by
  intro P
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₀ P
  refine ⟨F₀.map (MulAut.conj g : X →* X), ?_, uc22p20d_isElemAbelian_map _ (MulAut.conj g).injective hF, ?_⟩
  · have h1 : (P : Subgroup X) = (P₀ : Subgroup X).map (MulAut.conj g : X →* X) := by
      rw [← hg]
      exact coe_sylow_smul g P₀
    have h2 : normalizer (P : Set X) = normalizer ((P : Subgroup X) : Set X) := rfl
    rw [h2, h1, normalizer_map_conj]
    exact Subgroup.map_mono hN
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc]

end Witness

section Main

open CFSG.Blueprint (LieModel)

theorem uc22pwlie_borelWit_of_cover {m : ℕ} (hm : 2 ≤ m) {k : Type} [Field k] [Finite k] [CharP k 2] {p : ℕ}
    (hp : p.Prime) (hpk : p ∣ Nat.card k - 1) {X : Type} [Group X] [Finite X]
    (α : SpecialLinearGroup (Fin m) k →* X) (hα : Function.Surjective α)
    (hαc : α.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) k)) : uc22p20oBorelWit X p (m - 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζ, hζ⟩ := uc22pwlie_exists_zeta hp hpk
  have hcard : Nat.card (Subgroup.zpowers ζ) = p := by rw [Nat.card_zpowers, hζ]
  have hμ : ∀ x : Subgroup.zpowers ζ, x ^ p = 1 := fun x => by
    have h : orderOf x ∣ Nat.card (Subgroup.zpowers ζ) := orderOf_dvd_natCard x
    rw [hcard] at h
    exact orderOf_dvd_iff_pow_eq_one.1 h
  have hE : IsElemAbelian p (α.comp (uc22pwlie_diagHom (Subgroup.zpowers ζ) m)).range :=
    uc22pwlie_range_isElemAbelian _ (uc22pwlie_ker_pow hμ m)
  have hPG : IsPGroup p (α.comp (uc22pwlie_diagHom (Subgroup.zpowers ζ) m)).range := fun x =>
    ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hPG
  have hge : m - 2 ≤ j := by
    have h := uc22pwlie_card_range_ge hm hp hcard α hαc
    rw [hj] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := k) 2 (n := m) (by omega)
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Sylow 2 X, (P₀ : Subgroup X) = (unitriangular m k).map α :=
    ⟨Q.mapSurjective hα, by rw [Sylow.coe_mapSurjective, hQ]⟩
  have hN : (α.comp (uc22pwlie_diagHom (Subgroup.zpowers ζ) m)).range ≤ normalizer (P₀ : Set X) := by
    have h2 : normalizer (P₀ : Set X) = normalizer ((P₀ : Subgroup X) : Set X) := rfl
    rw [h2, hP₀]
    exact uc22pwlie_range_le_normalizer _ m α
  exact uc22p20v_borelWit_mono hp (uc22pwlie_borelWit_of_sylow P₀ _ hN hE hj) hge

theorem uc22pwlie_borelWit_of_lieModel {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    {m n : ℕ} (hm : 3 ≤ m) (hn : 2 < n) (h : LieModel (K ⧸ Subgroup.center K) .PSL m 2 n) {p : ℕ}
    (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) : uc22p20oBorelWit K p (m - 2) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  haveI : CharP F 2 := uc22pwlie_charP_two (n := n) hF
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hk : 5 ≤ Nat.card F := by
    rw [hF]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨α, hα, hαc⟩ := uc22pwlie_exists_slCover (by omega : 2 ≤ m') hk hq e
  exact uc22pwlie_borelWit_of_cover (by omega : 2 ≤ m' + 1) hp (by rw [hF]; exact hpn) α hα hαc

theorem uc22pwlie_lin_holds : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Odd (Nat.card (Subgroup.center K)) →
    ∀ m n : ℕ, (m = 5 ∨ m = 6 ∨ m = 7) → 2 < n → Odd n → LieModel (K ⧸ Subgroup.center K) .PSL m 2 n →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → uc22p20oBorelWit K p 2 := by
  intro K _ _ hq _ m n hm hn _ h p hp hpn
  exact uc22p20v_borelWit_mono hp
    (uc22pwlie_borelWit_of_lieModel hq (by omega) hn h hp hpn) (by omega)

theorem uc22pwlie_lin3_holds : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Odd (Nat.card (Subgroup.center K)) →
    ∀ n : ℕ, 2 < n → LieModel (K ⧸ Subgroup.center K) .PSL 3 2 n →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → p ≠ 3 → uc22p20oBorelWit K p 1 := by
  intro K _ _ hq _ n hn h p hp hpn _
  exact uc22pwlie_borelWit_of_lieModel hq (le_refl 3) hn h hp hpn

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
