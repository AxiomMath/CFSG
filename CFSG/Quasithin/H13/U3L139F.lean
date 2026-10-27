module

public import CFSG.Quasithin.H13.U3L139M
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem T_le_normalizer_fsuV1 (T V : Subgroup G) : T ≤ normalizer (fsuV1 T V : Set G) := by
  have key : ∀ s ∈ T, ∀ y ∈ fsuV1 T V, s * y * s⁻¹ = y := fun s hs y hy => by
    obtain ⟨-, hyC, -⟩ := mem_quasithinOmegaOneCenter_iff.1 hy.2
    rw [mem_centralizer_iff.1 hyC s hs, mul_inv_cancel_right]
  intro t ht
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [key t ht x hx]
    exact hx
  · intro hx
    have h1 := key t⁻¹ (inv_mem ht) _ hx
    rw [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at h1
    rw [h1]
    exact hx

structure Frame139 (T L V : Subgroup G) where
  ρ : ↥(normalizer (V : Set G)) →* Perm (Fin 6)
  L_le : L ≤ normalizer (V : Set G)
  T_le : T ≤ normalizer (V : Set G)
  ker : ∀ g : ↥(normalizer (V : Set G)), ρ g = 1 ↔ (g : G) ∈ centralizer (V : Set G)
  image_L : ∀ σ : Perm (Fin 6),
    (∃ g : ↥(normalizer (V : Set G)), (g : G) ∈ L ∧ ρ g = σ) ↔ σ ∈ alternatingGroup (Fin 6)
  T_D : ∀ g : ↥(normalizer (V : Set G)), (g : G) ∈ T → InD6 (ρ g)
  N1 : ∀ g : ↥(normalizer (V : Set G)), (g : G) ∈ normalizer (fsuV1 T V : Set G) → Pres45 (ρ g)

namespace Frame139

variable {T L V : Subgroup G} (F : Frame139 T L V)
include F

theorem rho_eq_one_iff {n : G} (hn : n ∈ normalizer (V : Set G)) :
    F.ρ ⟨n, hn⟩ = 1 ↔ n ∈ centralizer (V : Set G) :=
  F.ker ⟨n, hn⟩

theorem rho_mul {a b : G} (ha : a ∈ normalizer (V : Set G)) (hb : b ∈ normalizer (V : Set G)) :
    F.ρ ⟨a * b, mul_mem ha hb⟩ = F.ρ ⟨a, ha⟩ * F.ρ ⟨b, hb⟩ := by
  rw [← map_mul]
  rfl

theorem rho_inv {a : G} (ha : a ∈ normalizer (V : Set G)) :
    F.ρ ⟨a⁻¹, inv_mem ha⟩ = (F.ρ ⟨a, ha⟩)⁻¹ := by
  rw [← map_inv]
  rfl

theorem rho_pow {a : G} (ha : a ∈ normalizer (V : Set G)) (n : ℕ) :
    F.ρ ⟨a ^ n, pow_mem ha n⟩ = (F.ρ ⟨a, ha⟩) ^ n := by
  rw [← map_pow]
  rfl

theorem exists_TL [Finite G] (hsyl : IsSylowTwoOf (T ⊓ L) L) {σ : Perm (Fin 6)} (hσD : InD6 σ)
    (hσA : σ ∈ alternatingGroup (Fin 6)) :
    ∃ g : ↥(normalizer (V : Set G)), (g : G) ∈ T ⊓ L ∧ F.ρ g = σ := by
  classical
  let φ : ↥L →* ↥(alternatingGroup (Fin 6)) :=
    (F.ρ.comp (Subgroup.inclusion F.L_le)).codRestrict (alternatingGroup (Fin 6))
      fun l => (F.image_L _).1 ⟨_, l.2, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨τ, hτ⟩
    obtain ⟨g, hgL, hg⟩ := (F.image_L τ).2 hτ
    exact ⟨⟨g, hgL⟩, Subtype.ext (by simp [φ, ← hg]; rfl)⟩
  set H := (T ⊓ L).subgroupOf L with hH
  set K := H.map φ with hK
  have hodd : ¬ 2 ∣ K.index := fun h2 =>
    hsyl.2.2 (h2.trans (index_map_dvd H hφ))
  have hcard := card_mul_index K
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  rw [hA6] at hcard
  have h8 : 8 ∣ Nat.card K := by
    have hcop : Nat.Coprime 8 K.index :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    exact hcop.dvd_of_dvd_mul_right ⟨45, by rw [hcard]⟩
  have hKD : ∀ x ∈ K, InD6 (x : Perm (Fin 6)) := by
    rintro x ⟨⟨l, hl⟩, hlH, rfl⟩
    exact F.T_D _ (mem_inf.1 (mem_subgroupOf.1 hlH)).1
  let S : Finset ↥(alternatingGroup (Fin 6)) := Finset.univ.filter fun x => InD6 (x : Perm (Fin 6))
  have hSc : S.card = 8 := by
    have h1 := card_DA
    rw [← h1]
    refine Finset.card_bij (fun x _ => (x : Perm (Fin 6))) (fun x hx => ?_) (fun x _ y _ h =>
      Subtype.ext h) (fun τ hτ => ?_)
    · have := (Finset.mem_filter.1 hx).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this, Perm.mem_alternatingGroup.1 x.2⟩
    · obtain ⟨-, hτD, hτs⟩ := Finset.mem_filter.1 hτ
      exact ⟨⟨τ, Perm.mem_alternatingGroup.2 hτs⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hτD⟩,
        rfl⟩
  have hKS : (K : Set ↥(alternatingGroup (Fin 6))).toFinset ⊆ S := fun x hx =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hKD x (Set.mem_toFinset.1 hx)⟩
  have hKc : 8 ≤ (K : Set ↥(alternatingGroup (Fin 6))).toFinset.card := by
    rw [Set.toFinset_card]
    have : Nat.card K = Fintype.card (K : Set ↥(alternatingGroup (Fin 6))) := by
      rw [← Nat.card_eq_fintype_card]
      rfl
    rw [← this]
    exact Nat.le_of_dvd Nat.card_pos h8
  have heq := Finset.eq_of_subset_of_card_le hKS (by rw [hSc]; exact hKc)
  have hmem : (⟨σ, hσA⟩ : ↥(alternatingGroup (Fin 6))) ∈ K := by
    have : (⟨σ, hσA⟩ : ↥(alternatingGroup (Fin 6))) ∈ S :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hσD⟩
    rw [← heq] at this
    exact Set.mem_toFinset.1 this
  obtain ⟨⟨l, hl⟩, hlH, hlσ⟩ := hmem
  refine ⟨⟨l, F.L_le hl⟩, mem_subgroupOf.1 hlH, ?_⟩
  exact congrArg Subtype.val hlσ

theorem inA4_of_odd {x : G} (hxN : x ∈ normalizer (V : Set G))
    (hx1 : x ∈ normalizer (fsuV1 T V : Set G)) {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) :
    InA4 (F.ρ ⟨x, hxN⟩) := by
  refine inA4_of_pres45 _ (F.N1 _ hx1) (pow_45_of_odd' hm ?_)
  rw [← F.rho_pow hxN m]
  have : (⟨x ^ m, pow_mem hxN m⟩ : ↥(normalizer (V : Set G))) = 1 := Subtype.ext hxm
  rw [this, map_one]

theorem surj_of_three [Finite G] (hsyl : IsSylowTwoOf (T ⊓ L) L) {X : Subgroup G}
    (hXN : X ≤ normalizer (V : Set G)) (hTX : T ⊓ L ≤ normalizer (X : Set G))
    (hX : ∀ x (hx : x ∈ normalizer (V : Set G)), x ∈ X → InA4 (F.ρ ⟨x, hx⟩))
    {y : G} (hyX : y ∈ X) (hc3 : (F.ρ ⟨y, hXN hyX⟩) ^ 3 = 1)
    (hy1 : F.ρ ⟨y, hXN hyX⟩ ≠ 1) :
    ∀ σ : Perm (Fin 6), InA4 σ →
      ∃ x : G, ∃ hx : x ∈ normalizer (V : Set G), x ∈ X ∧ F.ρ ⟨x, hx⟩ = σ := by
  have hyN := hXN hyX
  set c := F.ρ ⟨y, hyN⟩ with hc
  have hcA4 : InA4 c := hX y hyN hyX
  obtain ⟨t, htTL, ht⟩ := F.exists_TL hsyl d0_mem.1 d0_mem.2
  have htX : (t : G) ∈ normalizer (X : Set G) := hTX htTL
  have hy' : (t : G) * y * (t : G)⁻¹ ∈ X := (mem_normalizer_iff.1 htX y).1 hyX
  have hy'N : (t : G) * y * (t : G)⁻¹ ∈ normalizer (V : Set G) := hXN hy'
  have hρy' : F.ρ ⟨(t : G) * y * (t : G)⁻¹, hy'N⟩ = d0 * c * d0⁻¹ := by
    have e : (⟨(t : G) * y * (t : G)⁻¹, hy'N⟩ : ↥(normalizer (V : Set G))) =
        t * ⟨y, hyN⟩ * t⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, ht]
  intro σ hσ
  obtain ⟨a, b, e, hσe⟩ := a4_gen hcA4 hc3 hy1 hσ
  have hw : y ^ a * ((t : G) * y * (t : G)⁻¹) ^ b * y ^ e ∈ X :=
    mul_mem (mul_mem (pow_mem hyX a) (pow_mem hy' b)) (pow_mem hyX e)
  refine ⟨_, hXN hw, hw, ?_⟩
  rw [F.rho_mul (mul_mem (pow_mem hyN a) (pow_mem hy'N b)) (pow_mem hyN e),
    F.rho_mul (pow_mem hyN a) (pow_mem hy'N b), F.rho_pow hyN, F.rho_pow hy'N, F.rho_pow hyN,
    hρy', hσe]

theorem dichotomy [Finite G] (hsyl : IsSylowTwoOf (T ⊓ L) L) {X : Subgroup G}
    (hXN : X ≤ normalizer (V : Set G)) (hX1 : X ≤ normalizer (fsuV1 T V : Set G))
    (hX2 : X ≤ oTwoRes X) (hTX : T ⊓ L ≤ normalizer (X : Set G)) :
    (∀ x (hx : x ∈ normalizer (V : Set G)), x ∈ X → InA4 (F.ρ ⟨x, hx⟩)) ∧
      (X ≤ centralizer (V : Set G) ∨ ∀ σ : Perm (Fin 6), InA4 σ →
        ∃ x : G, ∃ hx : x ∈ normalizer (V : Set G), x ∈ X ∧ F.ρ ⟨x, hx⟩ = σ) := by
  have hgen : ∀ x ∈ oTwoRes X, ∃ hx : x ∈ normalizer (V : Set G), InA4 (F.ρ ⟨x, hx⟩) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyX, m, hm, hym⟩ := hy
      exact ⟨hXN hyX, F.inA4_of_odd (hXN hyX) (hX1 hyX) hm hym⟩
    | one =>
      have e : (⟨1, one_mem _⟩ : ↥(normalizer (V : Set G))) = 1 := rfl
      exact ⟨one_mem _, by rw [e, map_one]; exact inA4_one⟩
    | mul x y _ _ hx hy =>
      obtain ⟨hxN, hx⟩ := hx
      obtain ⟨hyN, hy⟩ := hy
      exact ⟨mul_mem hxN hyN, by rw [F.rho_mul hxN hyN]; exact inA4_mul hx hy⟩
    | inv x _ hx =>
      obtain ⟨hxN, hx⟩ := hx
      exact ⟨inv_mem hxN, by rw [F.rho_inv hxN]; exact inA4_inv hx⟩
  have hA4 : ∀ x (hx : x ∈ normalizer (V : Set G)), x ∈ X → InA4 (F.ρ ⟨x, hx⟩) := by
    intro x hxN hx
    obtain ⟨_, h⟩ := hgen x (hX2 hx)
    exact h
  refine ⟨hA4, ?_⟩
  by_cases hC : X ≤ centralizer (V : Set G)
  · exact Or.inl hC
  right
  obtain ⟨y, hyX, m, hm, hym, hy1⟩ : ∃ y, ∃ hyX : y ∈ X, ∃ m : ℕ, Odd m ∧ y ^ m = 1 ∧
      F.ρ ⟨y, hXN hyX⟩ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hC
    refine hX2.trans ((closure_le _).2 fun y hy => ?_)
    obtain ⟨hyX, m, hm, hym⟩ := hy
    exact (F.rho_eq_one_iff (hXN hyX)).1 (hall y hyX m hm hym)
  have hyN := hXN hyX
  refine F.surj_of_three hsyl hXN hTX hA4 hyX ?_ hy1
  refine cube_of_inA4 _ (hA4 y hyN hyX) (pow_45_of_odd' hm ?_)
  rw [← F.rho_pow hyN m]
  have : (⟨y ^ m, pow_mem hyN m⟩ : ↥(normalizer (V : Set G))) = 1 := Subtype.ext hym
  rw [this, map_one]

end Frame139

end CFSG.Quasithin.H13.U3
