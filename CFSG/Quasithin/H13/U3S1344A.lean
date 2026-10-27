module

public import CFSG.Quasithin.H13.U3S1349A
public import CFSG.Quasithin.H13.U3S1344AK

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

@[expose] def K4xList : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2, swap 4 5,
    swap 0 1 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 3 * swap 4 5,
    swap 0 3 * swap 1 2 * swap 4 5]

theorem K4x_mul : ∀ a ∈ K4xList, ∀ b ∈ K4xList, a * b ∈ K4xList :=
  (U3K.grp_of (by decide +kernel) (by decide +kernel) U3K.grpX_check.1).1

theorem K4x_inv : ∀ a ∈ K4xList, a⁻¹ ∈ K4xList :=
  (U3K.grp_of (by decide +kernel) (by decide +kernel) U3K.grpX_check.1).2.1

theorem K4x_sq : ∀ a ∈ K4xList, a * a = 1 :=
  (U3K.grp_of (by decide +kernel) (by decide +kernel) U3K.grpX_check.1).2.2

theorem K4x_P1 : ∀ a ∈ K4xList, InP1 a :=
  U3K.p1_of (by decide +kernel) U3K.grpX_check.2

theorem K4x_normal : ∀ σ : Perm (Fin 6), InP1 σ → ∀ κ ∈ K4xList, σ * κ * σ⁻¹ ∈ K4xList :=
  U3K.normal_of U3K.p1_iff (by decide +kernel) U3K.normX_walk

@[expose] def PWit (σ : Perm (Fin 6)) : Prop :=
  ¬ InP1 σ ∨ σ ∈ K4xList ∨ ¬ σ ^ 16 = 1 ∨
    ∃ g : Perm (Fin 6), InP1 g ∧ Perm.sign g = 1 ∧ ¬ (σ * (g * σ * g⁻¹)) ^ 16 = 1

instance (σ : Perm (Fin 6)) : Decidable (PWit σ) := by
  unfold PWit
  infer_instance

theorem pwit_all : ∀ σ : Perm (Fin 6), PWit σ :=
  U3K.pwit_of (by decide +kernel) (lx := K4xList) (by decide +kernel)

theorem D_wit : ∀ σ : Perm (Fin 6), InD6 σ → σ ∉ K4xList →
    ¬ (σ * (c012 * σ * c012⁻¹)) ^ 16 = 1 ∨ ¬ (σ * (c123 * σ * c123⁻¹)) ^ 16 = 1 :=
  U3K.dwit_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem pow_sixteen_of_two_pow {σ : Perm (Fin 6)} {k : ℕ} (h : σ ^ 2 ^ k = 1) : σ ^ 16 = 1 := by
  have h1 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf σ ∣ 720 := by
    have := orderOf_dvd_card (x := σ)
    rwa [Fintype.card_perm, Fintype.card_fin] at this
  obtain ⟨j, hj, hσ⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  rw [hσ] at h2
  have hj4 : j ≤ 4 := by
    by_contra hj4
    have : 2 ^ 5 ∣ 720 := (pow_dvd_pow 2 (by omega)).trans h2
    norm_num at this
  exact orderOf_dvd_iff_pow_eq_one.1 (hσ ▸ pow_dvd_pow 2 hj4)

@[expose] def K4xsub : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ ∈ K4xList}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => K4x_mul a ha b hb
  inv_mem' := fun {a} ha => K4x_inv a ha

theorem mem_K4xsub {σ : Perm (Fin 6)} : σ ∈ K4xsub ↔ σ ∈ K4xList := Iff.rfl

theorem pCoreOf_P1_inf {X : Subgroup (Perm (Fin 6))} (hX : alternatingGroup (Fin 6) ≤ X) :
    pCoreOf 2 (P1sub ⊓ X) = K4xsub ⊓ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro σ hσ
    have hσP : σ ∈ P1sub ⊓ X := LieType.BorelTits.pCoreOf_le 2 _ hσ
    obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 (P1sub ⊓ X) ⟨σ, hσ⟩
    have hσk : σ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine mem_inf.2 ⟨?_, (mem_inf.1 hσP).2⟩
    rcases pwit_all σ with h | h | h | ⟨g, hgP, hgA, hg⟩
    · exact absurd (mem_inf.1 hσP).1 h
    · exact h
    · exact absurd (pow_sixteen_of_two_pow hσk) h
    · exfalso
      have hgX : g ∈ P1sub ⊓ X := mem_inf.2 ⟨hgP, hX (Perm.mem_alternatingGroup.2 hgA)⟩
      have hc : g * σ * g⁻¹ ∈ pCoreOf 2 (P1sub ⊓ X) :=
        (mem_normalizer_iff.1 (LieType.BorelTits.le_normalizer_pCoreOf 2 _ hgX) σ).1 hσ
      obtain ⟨m, hm⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 (P1sub ⊓ X)
        ⟨σ * (g * σ * g⁻¹), mul_mem hσ hc⟩
      exact hg (pow_sixteen_of_two_pow (by simpa using congrArg Subtype.val hm))
  · refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
      (inf_le_inf_right X fun κ hκ => K4x_P1 κ hκ) ?_ ?_
    · refine (normal_subgroupOf_iff_le_normalizer (inf_le_inf_right X fun κ hκ =>
        K4x_P1 κ hκ)).2 fun σ hσ => ?_
      rw [mem_normalizer_iff]
      intro κ
      constructor
      · intro hκ
        exact mem_inf.2 ⟨K4x_normal σ (mem_inf.1 hσ).1 κ (mem_inf.1 hκ).1,
          mul_mem (mul_mem (mem_inf.1 hσ).2 (mem_inf.1 hκ).2) (inv_mem (mem_inf.1 hσ).2)⟩
      · intro hκ
        have h1 := K4x_normal σ⁻¹ (inv_mem (mem_inf.1 hσ).1) _ (mem_inf.1 hκ).1
        have h2 : σ⁻¹ * (σ * κ * σ⁻¹) * σ⁻¹⁻¹ = κ := by group
        rw [h2] at h1
        have h3 := mul_mem (mul_mem (inv_mem (mem_inf.1 hσ).2) (mem_inf.1 hκ).2) (mem_inf.1 hσ).2
        have h4 : σ⁻¹ * (σ * κ * σ⁻¹) * σ = κ := by group
        rw [h4] at h3
        exact mem_inf.2 ⟨h1, h3⟩
    · rintro ⟨κ, hκ⟩
      exact ⟨1, Subtype.ext (by simp [pow_two, K4x_sq κ (mem_inf.1 hκ).1])⟩

@[expose] def K4List : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

theorem K4_mul : ∀ a ∈ K4List, ∀ b ∈ K4List, a * b ∈ K4List :=
  (U3K.grp_of (by decide +kernel) (by decide +kernel) U3K.grp4_check).1

theorem K4_inv : ∀ a ∈ K4List, a⁻¹ ∈ K4List :=
  (U3K.grp_of (by decide +kernel) (by decide +kernel) U3K.grp4_check).2.1

theorem K4_sq : ∀ a ∈ K4List, a * a = 1 :=
  (U3K.grp_of (by decide +kernel) (by decide +kernel) U3K.grp4_check).2.2

theorem A4_two_K4 : ∀ σ : Perm (Fin 6), InA4 σ → σ ^ 16 = 1 → σ ∈ K4List :=
  U3K.two_of (by decide +kernel) (by decide +kernel)

theorem K4_normal_A4 : ∀ σ : Perm (Fin 6), InA4 σ → ∀ κ ∈ K4List, σ * κ * σ⁻¹ ∈ K4List :=
  U3K.normal_of U3K.a4K_iff (by decide +kernel) U3K.norm4_walk

theorem A4_dec : ∀ σ : Perm (Fin 6), InA4 σ →
    σ ∈ K4List ∨ σ * c012⁻¹ ∈ K4List ∨ σ * c012 ∈ K4List :=
  U3K.dec_of (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem tau_facts : InD6 (swap 0 1 * swap 4 5) ∧
    swap (0 : Fin 6) 1 * swap 4 5 ∈ alternatingGroup (Fin 6) ∧
    swap 0 1 * swap 4 5 * c012 * (swap 0 1 * swap 4 5)⁻¹ = c012⁻¹ ∧
    swap 0 1 * swap 4 5 * c012 * (swap 0 1 * swap 4 5)⁻¹ * c012⁻¹ ∉ K4List := by
  simp only [Perm.mem_alternatingGroup]
  decide

theorem K4x_comm_A4 : ∀ κ ∈ K4xList, ∀ σ : Perm (Fin 6), InA4 σ →
    κ * σ * κ⁻¹ * σ⁻¹ ∈ K4List :=
  U3K.comm_of (by decide +kernel) (by decide +kernel)

theorem D_cent : ∀ σ : Perm (Fin 6), InD6 σ → σ * c012 * σ⁻¹ * c012⁻¹ ∈ K4List →
    σ ∈ K4xList :=
  U3K.cent_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem tau2_facts : InD6 (swap 0 2 * swap 1 3) ∧
    swap (0 : Fin 6) 2 * swap 1 3 ∈ alternatingGroup (Fin 6) ∧
    c2perm * (swap 0 2 * swap 1 3) * c2perm⁻¹ * (swap 0 2 * swap 1 3)⁻¹ = c2perm * c2perm ∧
    c2perm * c2perm * c2perm = 1 ∧
    G6.permAct 6 (c2perm * c2perm) e45 ≠ e45 ∧ G6.permAct 6 (c2perm * c2perm) e0123 ≠ e0123 := by
  simp only [Perm.mem_alternatingGroup]
  decide

theorem c012_not_K4 : c012 ∉ K4List ∧ ∀ σ : Perm (Fin 6), InA4 σ → InA4 σ⁻¹ := by
  decide +kernel

theorem mem_pCoreOf_map_of_ker {N Q₁ Q₂ : Type*} [Group N] [Group Q₁] [Group Q₂] [Finite Q₁]
    [Finite Q₂] (φ : N →* Q₁) (ψ : N →* Q₂) (hker : ∀ n, φ n = 1 → ψ n = 1) (X : Subgroup N)
    {x : N} (hx : x ∈ X) (hφ : φ x ∈ pCoreOf 2 (X.map φ)) : ψ x ∈ pCoreOf 2 (X.map ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup N := X ⊓ (pCoreOf 2 (X.map φ)).comap φ with hP
  have hPX : P.map ψ ≤ X.map ψ := map_mono inf_le_left
  have hconj : ∀ n ∈ X, ∀ p ∈ P, n * p * n⁻¹ ∈ P := by
    intro n hn p hp
    refine mem_inf.2 ⟨mul_mem (mul_mem hn (mem_inf.1 hp).1) (inv_mem hn), ?_⟩
    rw [mem_comap, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 (LieType.BorelTits.le_normalizer_pCoreOf 2 (X.map φ)
      (mem_map_of_mem φ hn)) _).1 (mem_inf.1 hp).2
  have hle : P.map ψ ≤ pCoreOf 2 (X.map ψ) := by
    refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ hPX ?_ ?_
    · refine (normal_subgroupOf_iff_le_normalizer hPX).2 ?_
      rintro _ ⟨n, hn, rfl⟩
      rw [mem_normalizer_iff]
      intro q
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨n * p * n⁻¹, hconj n hn p hp, by simp⟩
      · rintro ⟨p, hp, hpq⟩
        refine ⟨n⁻¹ * p * n⁻¹⁻¹, hconj n⁻¹ (inv_mem hn) p hp, ?_⟩
        rw [map_mul, map_mul, map_inv, hpq]
        group
    · rintro ⟨_, ⟨p, hp, rfl⟩⟩
      obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 (X.map φ) ⟨φ p, (mem_inf.1 hp).2⟩
      have h1 : φ (p ^ 2 ^ k) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val hk
      refine ⟨k, Subtype.ext ?_⟩
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow]
      exact hker _ h1
  exact hle ⟨x, mem_inf.2 ⟨hx, hφ⟩, rfl⟩

noncomputable def mapMulEquivOfKer {N Q₁ Q₂ : Type*} [Group N] [Group Q₁] [Group Q₂]
    (φ : N →* Q₁) (ψ : N →* Q₂) (h : ∀ n, φ n = 1 ↔ ψ n = 1) (X : Subgroup N) :
    ↥(X.map φ) ≃* ↥(X.map ψ) :=
  have hk : (φ.comp X.subtype).ker = (ψ.comp X.subtype).ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact h _
  have h₁ : (φ.comp X.subtype).range = X.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h₂ : (ψ.comp X.subtype).range = X.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  (((QuotientGroup.quotientKerEquivRange (φ.comp X.subtype)).trans
      (MulEquiv.subgroupCongr h₁)).symm.trans (QuotientGroup.quotientMulEquivOfEq hk)).trans
    ((QuotientGroup.quotientKerEquivRange (ψ.comp X.subtype)).trans (MulEquiv.subgroupCongr h₂))

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem s134_conjAct_eq_one_iff (V : Subgroup G) (g : ↥(normalizer (V : Set G))) :
    conjAct V g = 1 ↔ (g : G) ∈ centralizer (V : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g

theorem s134_conjAct_eq_one_iff_rho (S : A6.Setting134 G T L V) (g : ↥(normalizer (V : Set G))) :
    conjAct V g = 1 ↔ S.frame.ρ g = 1 := by
  rw [s134_conjAct_eq_one_iff, s134_rho_eq_one_iff]

theorem s134_conjAct_eq_iff_rho (S : A6.Setting134 G T L V) (g g' : ↥(normalizer (V : Set G))) :
    conjAct V g = conjAct V g' ↔ S.frame.ρ g = S.frame.ρ g' := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, s134_conjAct_eq_one_iff_rho, map_mul, map_inv,
    inv_mul_eq_one]

theorem s134_rho_L (S : A6.Setting134 G T L V) :
    (L.subgroupOf (normalizer (V : Set G))).map S.frame.ρ = alternatingGroup (Fin 6) := by
  ext σ
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (S.frame.image_L _).1 ⟨g, mem_subgroupOf.1 hg, rfl⟩
  · intro hσ
    obtain ⟨g, hgL, hgσ⟩ := (S.frame.image_L σ).2 hσ
    exact ⟨g, mem_subgroupOf.2 hgL, hgσ⟩

theorem s134_isA6On (S : A6.Setting134 G T L V) : IsA6On L V :=
  ⟨(mapMulEquivOfKer (conjAct V) S.frame.ρ (s134_conjAct_eq_one_iff_rho S)
    (L.subgroupOf (normalizer (V : Set G)))).trans (MulEquiv.subgroupCongr (s134_rho_L S))⟩

theorem s134_alt_le_rho_LT (S : A6.Setting134 G T L V) :
    alternatingGroup (Fin 6) ≤ ((L ⊔ T).subgroupOf (normalizer (V : Set G))).map S.frame.ρ := by
  rw [← s134_rho_L S]
  exact map_mono (subgroupOf_mono _ le_sup_left)

theorem P1_preserves_W1 : ∀ σ : Perm (Fin 6), InP1 σ → ∀ x : P6, InW1 x →
    InW1 (G6.permAct 6 σ x) := by
  decide +kernel

theorem s134_mem_normalizer_V1_of_P1 (S : A6.Setting134 G T L V) (g : ↥(normalizer (V : Set G)))
    (hg : InP1 (S.frame.ρ g)) : (g : G) ∈ normalizer (fsuV1 T V : Set G) := by
  have key : ∀ h : ↥(normalizer (V : Set G)), InP1 (S.frame.ρ h) →
      ∀ x ∈ fsuV1 T V, (h : G) * x * (h : G)⁻¹ ∈ fsuV1 T V := by
    intro h hh x hx
    obtain ⟨hxV, hxW⟩ := S.mem_V1_iff.1 hx
    refine S.mem_V1_iff.2 ⟨(mem_normalizer_iff.mp h.2 x).mp hxV, ?_⟩
    rw [S.psi_conj h ⟨x, hxV⟩, G6.coreAct_coe]
    exact P1_preserves_W1 _ hh _ hxW
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have h1 := key g⁻¹ (by rw [map_inv]; exact InP1.inv _ hg) _ hx
  simpa [mul_assoc] using h1

theorem s134_rho_M1 (S : A6.Setting134 G T L V) :
    (((L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G)).subgroupOf (normalizer (V : Set G))).map
        S.frame.ρ =
      P1sub ⊓ ((L ⊔ T).subgroupOf (normalizer (V : Set G))).map S.frame.ρ := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hm
    exact mem_inf.2 ⟨inP1_of_pres45 _ (s134_pres45 S m (mem_inf.1 hm).2),
      ⟨m, mem_subgroupOf.2 (mem_inf.1 hm).1, rfl⟩⟩
  · rintro σ ⟨hσP, ⟨m, hm, rfl⟩⟩
    refine ⟨m, mem_subgroupOf.2 (mem_inf.2 ⟨mem_subgroupOf.1 hm, ?_⟩), rfl⟩
    exact s134_mem_normalizer_V1_of_P1 S m hσP

theorem s134_mem_r1Of_iff (S : A6.Setting134 G T L V) {x : G} :
    x ∈ r1Of T L V ↔ x ∈ T ∧ ∀ hx : x ∈ normalizer (V : Set G), S.frame.ρ ⟨x, hx⟩ ∈ K4xsub := by
  set M₁ := (L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G) with hM₁
  set X := M₁.subgroupOf (normalizer (V : Set G)) with hX
  have hTM₁ : T ≤ M₁ := le_inf le_sup_right (T_le_normalizer_fsuV1 T V)
  have hker₁ : ∀ n, conjAct V n = 1 → S.frame.ρ n = 1 := fun n h =>
    (s134_conjAct_eq_one_iff_rho S n).1 h
  have hker₂ : ∀ n, S.frame.ρ n = 1 → conjAct V n = 1 := fun n h =>
    (s134_conjAct_eq_one_iff_rho S n).2 h
  have hcore : pCoreOf 2 (X.map S.frame.ρ) =
      K4xsub ⊓ ((L ⊔ T).subgroupOf (normalizer (V : Set G))).map S.frame.ρ := by
    rw [hX, hM₁, s134_rho_M1 S]
    exact pCoreOf_P1_inf (s134_alt_le_rho_LT S)
  constructor
  · intro hx
    obtain ⟨hxT, ⟨y, hy, rfl⟩⟩ := mem_inf.1 hx
    refine ⟨hxT, fun hx' => ?_⟩
    have hyX : y ∈ X := mem_subgroupOf.2 (hTM₁ hxT)
    have h1 := mem_pCoreOf_map_of_ker (conjAct V) S.frame.ρ hker₁ X hyX hy
    rw [hcore] at h1
    have : (⟨(normalizer (V : Set G)).subtype y, hx'⟩ : ↥(normalizer (V : Set G))) = y :=
      Subtype.ext rfl
    rw [this]
    exact (mem_inf.1 h1).1
  · rintro ⟨hxT, hxK⟩
    have hxN : x ∈ normalizer (V : Set G) := S.frame.T_le hxT
    have hyX : (⟨x, hxN⟩ : ↥(normalizer (V : Set G))) ∈ X := mem_subgroupOf.2 (hTM₁ hxT)
    have h1 : S.frame.ρ ⟨x, hxN⟩ ∈ pCoreOf 2 (X.map S.frame.ρ) := by
      rw [hcore]
      exact mem_inf.2 ⟨hxK hxN, ⟨⟨x, hxN⟩, mem_subgroupOf.2 (le_sup_right (a := L) hxT), rfl⟩⟩
    have h2 := mem_pCoreOf_map_of_ker S.frame.ρ (conjAct V) hker₂ X hyX h1
    exact mem_inf.2 ⟨hxT, ⟨⟨x, hxN⟩, h2, rfl⟩⟩

omit [Finite G] in
theorem r1Of_le_T (T L V : Subgroup G) : r1Of T L V ≤ T := inf_le_left

theorem s134_pCoreOf_L1T_le_r1Of (S : A6.Setting134 G T L V) :
    pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ r1Of T L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  have hsyl : IsSylowTwoOf T (L₁ ⊔ T) := A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right
  have hOT : pCoreOf 2 (L₁ ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl
  intro x hx
  have hxT := hOT hx
  refine (s134_mem_r1Of_iff S).2 ⟨hxT, fun hxN => ?_⟩
  by_contra hK
  have key : ∀ (c : Perm (Fin 6)) (y : G) (hyL1 : y ∈ L₁) (hyN : y ∈ normalizer (V : Set G)),
      S.frame.ρ ⟨y, hyN⟩ = c →
        (S.frame.ρ ⟨x, hxN⟩ * (c * S.frame.ρ ⟨x, hxN⟩ * c⁻¹)) ^ 16 = 1 := by
    intro c y hyL1 hyN hyc
    have hyx : y * x * y⁻¹ ∈ pCoreOf 2 (L₁ ⊔ T) :=
      (mem_normalizer_iff.1 (LieType.BorelTits.le_normalizer_pCoreOf 2 _
        (le_sup_left (b := T) hyL1)) x).1 hx
    obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 (L₁ ⊔ T)
      ⟨x * (y * x * y⁻¹), mul_mem hx hyx⟩
    have hk' : (x * (y * x * y⁻¹)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hN : x * (y * x * y⁻¹) ∈ normalizer (V : Set G) :=
      mul_mem hxN (mul_mem (mul_mem hyN hxN) (inv_mem hyN))
    have e : (⟨x * (y * x * y⁻¹), hN⟩ : ↥(normalizer (V : Set G))) =
        ⟨x, hxN⟩ * (⟨y, hyN⟩ * ⟨x, hxN⟩ * ⟨y, hyN⟩⁻¹) := rfl
    have h1 : S.frame.ρ ⟨x * (y * x * y⁻¹), hN⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨x * (y * x * y⁻¹), hN⟩ : ↥(normalizer (V : Set G))) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using hk')
      rw [this, map_one]
    rw [e, map_mul, map_mul, map_mul, map_inv, hyc] at h1
    exact pow_sixteen_of_two_pow h1
  obtain ⟨y₁, hy₁L1, hy₁N, hy₁⟩ := s134_exists_mem_L1 S c012_props.1 c012_props.2.1
    c012_props.2.2
  obtain ⟨y₂, hy₂L1, hy₂N, hy₂⟩ := s134_exists_mem_L1 S c123_props.1 c123_props.2.1
    c123_props.2.2
  rcases D_wit _ (S.frame.T_D ⟨x, hxN⟩ hxT) hK with h | h
  · exact h (key c012 y₁ hy₁L1 hy₁N hy₁)
  · exact h (key c123 y₂ hy₂L1 hy₂N hy₂)

theorem s134_T_le_normalizer_L1 (S : A6.Setting134 G T L V) :
    T ≤ normalizer (L₁Of L (fsuV1 T V) : Set G) := by
  intro t ht
  refine normalizer_le_normalizer_oTwoRes _ ?_
  rw [mem_normalizer_iff]
  intro x
  have h1 := mem_normalizer_iff.mp (S.T_le_NL ht) x
  have htN := T_le_normalizer_fsuV1 T V ht
  have h2 : x ∈ normalizer (fsuV1 T V : Set G) ↔
      t * x * t⁻¹ ∈ normalizer (fsuV1 T V : Set G) :=
    ⟨fun hx => mul_mem (mul_mem htN hx) (inv_mem htN), fun hx => by
      have := mul_mem (mul_mem (inv_mem htN) hx) htN
      simpa [mul_assoc] using this⟩
  simp only [mem_inf]
  exact ⟨fun ⟨a, b⟩ => ⟨h1.1 a, h2.1 b⟩, fun ⟨a, b⟩ => ⟨h1.2 a, h2.2 b⟩⟩

theorem s134_sylow_TL (S : A6.Setting134 G T L V) : IsSylowTwoOf (T ⊓ L) L :=
  A4.isSylowTwoOf_inf_normal (s134_sylow_LT S) le_sup_left (sup_le le_normalizer S.T_le_NL)

theorem InA4.mul' : ∀ a b : Perm (Fin 6), InA4 a → InA4 b → InA4 (a * b) := by
  intro a b ha hb
  obtain ⟨ha4, ha5, has⟩ := ha
  obtain ⟨hb4, hb5, hbs⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · rw [Perm.mul_apply, hb4, ha4]
  · rw [Perm.mul_apply, hb5, ha5]
  · rw [map_mul, has, hbs, mul_one]

theorem s134_rho_L1 (S : A6.Setting134 G T L V) {l : G} (hl : l ∈ normalizer (V : Set G))
    (hlL1 : l ∈ L₁Of L (fsuV1 T V)) : InA4 (S.frame.ρ ⟨l, hl⟩) := by
  have key : ∀ x ∈ L₁Of L (fsuV1 T V), ∃ hx : x ∈ normalizer (V : Set G),
      InA4 (S.frame.ρ ⟨x, hx⟩) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyLN, m, hm, hym⟩ := hy
      have hyN : y ∈ normalizer (V : Set G) := S.frame.L_le (mem_inf.1 hyLN).1
      refine ⟨hyN, inA4_of_pres45 _ (s134_pres45 S ⟨y, hyN⟩ (mem_inf.1 hyLN).2)
        (pow_45_of_odd' hm ?_)⟩
      rw [← map_pow]
      have : (⟨y, hyN⟩ : ↥(normalizer (V : Set G))) ^ m = 1 := Subtype.ext (by simpa using hym)
      rw [this, map_one]
    | one =>
      refine ⟨one_mem _, ?_⟩
      have h1 : (⟨1, one_mem _⟩ : ↥(normalizer (V : Set G))) = 1 := rfl
      rw [h1, map_one]
      decide
    | mul a b _ _ ha hb =>
      obtain ⟨haN, ha⟩ := ha
      obtain ⟨hbN, hb⟩ := hb
      refine ⟨mul_mem haN hbN, ?_⟩
      rw [show (⟨a * b, mul_mem haN hbN⟩ : ↥(normalizer (V : Set G))) = ⟨a, haN⟩ * ⟨b, hbN⟩
        from rfl, map_mul]
      exact InA4.mul' _ _ ha hb
    | inv a _ ha =>
      obtain ⟨haN, ha⟩ := ha
      refine ⟨inv_mem haN, ?_⟩
      rw [show (⟨a⁻¹, inv_mem haN⟩ : ↥(normalizer (V : Set G))) = ⟨a, haN⟩⁻¹ from rfl, map_inv]
      exact c012_not_K4.2 _ ha
  obtain ⟨_, h⟩ := key l hlL1
  exact h

theorem isPGroup_of_oTwoRes_eq_bot {X : Subgroup G} (h : oTwoRes X = ⊥) : IsPGroup 2 ↥X := by
  rintro ⟨x, hx⟩
  obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have h1 : x ^ 2 ^ a ∈ oTwoRes X := by
    refine subset_closure ⟨pow_mem hx _, m, hm, ?_⟩
    rw [← pow_mul, ← hxm, pow_orderOf_eq_one]
  rw [h, mem_bot] at h1
  exact ⟨a, Subtype.ext (by simpa using h1)⟩

theorem s134_centralizer_VH_le (S : A6.Setting134 G T L V) {z : G} {H VH : Subgroup G}
    (hHz : H ≤ centralizer ({z} : Set G))
    (hX : quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) ⊓ (VH ⊔ zpowers z) ≠ ⊥) :
    H ⊓ centralizer (VH : Set G) ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) ⊓ (VH ⊔ zpowers z) with hXdef
  have hXZ : X ≤ quasithinOmegaOneCenter T := inf_le_left.trans inf_le_left
  have hX2 : IsPGroup 2 ↥X :=
    S.h13.sylow.1.to_le (hXZ.trans ((s134_Z_le_center T).trans inf_le_left))
  have hLT : L ⊔ T ≤ normalizer (X : Set G) := by
    refine sup_le (fun l hl => centralizer_le_normalizer _ ?_) (fun t ht =>
      centralizer_le_normalizer _ ?_)
    · rw [mem_centralizer_iff]
      intro x hx
      exact (mem_centralizer_iff.1 (mem_inf.1 (mem_inf.1 hx).1).2 l hl).symm
    · rw [mem_centralizer_iff]
      intro x hx
      exact (mem_centralizer_iff.1 (mem_quasithinOmegaOneCenter_iff.1 (hXZ hx)).2.1 t ht).symm
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge (⟨X, hX, hX2, rfl⟩ :
    IsTwoLocal (normalizer (X : Set G)))
  have hM'eq := S.uniqueM.2 M' ⟨hM', hLT.trans hM'le⟩
  intro c hc
  obtain ⟨hcH, hcV⟩ := mem_inf.1 hc
  have hsup : VH ⊔ zpowers z ≤ centralizer ({c} : Set G) := by
    refine sup_le (fun v hv => ?_) (zpowers_le.2 ?_)
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 hcV v hv
    · rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_singleton_iff.1 (hHz hcH)).symm
  have hcX : c ∈ centralizer (X : Set G) :=
    mem_centralizer_iff.2 fun g hg => mem_centralizer_singleton_iff.1 (hsup (mem_inf.1 hg).2)
  exact hM'eq ▸ hM'le (centralizer_le_normalizer _ hcX)

end CFSG.Quasithin.H13.U3
