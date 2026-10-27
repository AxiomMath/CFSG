module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136CentBlock

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

lemma w1369_pow_eq_one_iff_even {G : Type} [Group G] {g : G} (hg : g ^ 2 = 1)
    (hg1 : g ≠ 1) (n : ℕ) : g ^ n = 1 ↔ Even n := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hne
    rw [hm, w1369_s16h_pow_odd hg m] at h
    exact hg1 h
  · rintro ⟨m, hm⟩
    rw [hm, show m + m = 2 * m from (two_mul m).symm, w1369_s16h_pow_even hg m]

lemma w1369_card_filter_eq_sum_val (b : Fin 3 → ZMod 2) :
    (Finset.univ.filter (fun j : Fin 3 => b j = 1)).card = ∑ j : Fin 3, (b j).val := by
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : b j = 1
  · rw [if_pos h, h, ZMod.val_one 2]
  · rw [if_neg h]
    have h01 : (b j).val = 0 ∨ (b j).val = 1 := by
      have := ZMod.val_lt (b j)
      omega
    rcases h01 with h0 | h1
    · exact h0.symm
    · exact absurd ((ZMod.val_eq_one (by norm_num) (b j)).mp h1) h

lemma w1369_sum_eq_natCast_sum_val (b : Fin 3 → ZMod 2) :
    (∑ j : Fin 3, b j) = ((∑ j : Fin 3, (b j).val : ℕ) : ZMod 2) := by
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (ZMod.natCast_zmod_val (b j)).symm

@[expose] def w1369_rhoMat : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def w1369_rho : GL (Fin 3) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero w1369_rhoMat (by decide +kernel)

lemma w1369_rho_pow_seven : w1369_rho ^ 7 = 1 := by decide +kernel

lemma w1369_rho_ne_one : w1369_rho ≠ 1 := by decide +kernel

lemma w1369_rho_order : orderOf w1369_rho = 7 := by
  have hdvd : orderOf w1369_rho ∣ 7 :=
    orderOf_dvd_iff_pow_eq_one.mpr w1369_rho_pow_seven
  have hne1 : orderOf w1369_rho ≠ 1 := fun h => w1369_rho_ne_one (orderOf_eq_one_iff.mp h)
  rcases (by norm_num : Nat.Prime 7).eq_one_or_self_of_dvd (orderOf w1369_rho) hdvd with h | h
  · exact absurd h hne1
  · exact h

lemma w1369_rho_fixed :
    ∀ v : Fin 3 → ZMod 2, w1369_rho.val *ᵥ v = v → v = 0 := by decide +kernel

lemma w1369_rho_orbit :
    ∀ c d : Fin 3 → ZMod 2, c ≠ 0 → d ≠ 0 →
      ∃ k : Fin 7, (w1369_rho ^ (k : ℕ)).val *ᵥ c = d := by
  decide +kernel

@[expose] noncomputable def w1369_secHomOfIso {Q : Type} [CommGroup Q]
    {Λ : Subgroup (MulAut Q)} {A B : Subgroup Q} (h : SecIsoOn Λ A ⊥ B ⊥) : ↥A →* ↥B :=
  MonoidHom.codRestrict (Classical.choose h.2.2.2.2.2.2) B
    (Classical.choose_spec h.2.2.2.2.2.2).1

lemma w1369_secHomOfIso_injective {Q : Type} [CommGroup Q]
    {Λ : Subgroup (MulAut Q)} {A B : Subgroup Q} (h : SecIsoOn Λ A ⊥ B ⊥) :
    Function.Injective (w1369_secHomOfIso h) := by
  intro a a' haa'
  have hspec := Classical.choose_spec h.2.2.2.2.2.2
  have h1 : Classical.choose h.2.2.2.2.2.2 (a * a'⁻¹) = 1 := by
    rw [map_mul, map_inv]
    have h2 : Classical.choose h.2.2.2.2.2.2 a = Classical.choose h.2.2.2.2.2.2 a' :=
      congrArg (fun z : ↥B => (z : Q)) haa'
    rw [h2, mul_inv_cancel]
  have h2 : (((a * a'⁻¹ : ↥A) : Q)) ∈ (⊥ : Subgroup Q) :=
    (hspec.2.1 (a * a'⁻¹)).mp (by simpa using h1)
  have h3 : ((a * a'⁻¹ : ↥A) : Q) = 1 := Subgroup.mem_bot.mp h2
  have h4 : (a : Q) = (a' : Q) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    exact mul_inv_eq_one.mp h3
  exact Subtype.ext h4

lemma w1369_secHomOfIso_surjective {Q : Type} [CommGroup Q]
    {Λ : Subgroup (MulAut Q)} {A B : Subgroup Q} (h : SecIsoOn Λ A ⊥ B ⊥) :
    Function.Surjective (w1369_secHomOfIso h) := by
  intro b
  have hspec := Classical.choose_spec h.2.2.2.2.2.2
  obtain ⟨a, ha⟩ := hspec.2.2.1 b b.2
  refine ⟨a, ?_⟩
  apply Subtype.ext
  have h1 : Classical.choose h.2.2.2.2.2.2 a * (b : Q)⁻¹ = 1 := Subgroup.mem_bot.mp ha
  rwa [mul_inv_eq_one] at h1

@[expose] noncomputable def w1369_secEquivOfIso {Q : Type} [CommGroup Q]
    {Λ : Subgroup (MulAut Q)} {A B : Subgroup Q} (h : SecIsoOn Λ A ⊥ B ⊥) : ↥A ≃* ↥B :=
  MulEquiv.ofBijective (w1369_secHomOfIso h)
    ⟨w1369_secHomOfIso_injective h, w1369_secHomOfIso_surjective h⟩

lemma w1369_secEquivOfIso_equivariant {Q : Type} [CommGroup Q]
    {Λ : Subgroup (MulAut Q)} {A B : Subgroup Q} (h : SecIsoOn Λ A ⊥ B ⊥) :
    ∀ g (hg : g ∈ Λ) (a : ↥A),
      (((w1369_secEquivOfIso h) ⟨g (a : Q), h.2.2.1 g hg (a : Q) a.2⟩ : ↥B) : Q) =
        g (((w1369_secEquivOfIso h) a : ↥B) : Q) := by
  intro g hg a
  have hspec := Classical.choose_spec h.2.2.2.2.2.2
  have h1 := hspec.2.2.2 g hg a ⟨g (a : Q), h.2.2.1 g hg (a : Q) a.2⟩ rfl
  have h2 : Classical.choose h.2.2.2.2.2.2 ⟨g (a : Q), h.2.2.1 g hg (a : Q) a.2⟩ =
      g (Classical.choose h.2.2.2.2.2.2 a) := by
    have := Subgroup.mem_bot.mp h1
    rwa [mul_inv_eq_one] at this
  change Classical.choose h.2.2.2.2.2.2 ⟨g (a : Q), h.2.2.1 g hg (a : Q) a.2⟩ =
    g (Classical.choose h.2.2.2.2.2.2 a)
  exact h2

@[expose] noncomputable def w1369_PhiFun {Q : Type} [CommGroup Q] {I : Fin 3 → Subgroup Q}
    (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i)) (c : Fin 3 → ZMod 2) (u : ↥(I 0)) : Q :=
  ∏ i : Fin 3, (if c i = 1 then ((β i u : ↥(I i)) : Q) else 1)

lemma w1369_PhiFun_mul {Q : Type} [CommGroup Q] {I : Fin 3 → Subgroup Q}
    (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i)) (c : Fin 3 → ZMod 2) (u v : ↥(I 0)) :
    w1369_PhiFun β c (u * v) = w1369_PhiFun β c u * w1369_PhiFun β c v := by
  classical
  rw [w1369_PhiFun, w1369_PhiFun, w1369_PhiFun, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : c i = 1 <;> simp [h, map_mul]

@[expose] noncomputable def w1369_Phi {Q : Type} [CommGroup Q] {I : Fin 3 → Subgroup Q}
    (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i)) (c : Fin 3 → ZMod 2) : ↥(I 0) →* Q :=
  MonoidHom.mk' (w1369_PhiFun β c) (w1369_PhiFun_mul β c)

lemma w1369_Phi_apply {Q : Type} [CommGroup Q] {I : Fin 3 → Subgroup Q}
    (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i)) (c : Fin 3 → ZMod 2) (u : ↥(I 0)) :
    w1369_Phi β c u = ∏ i : Fin 3, (if c i = 1 then ((β i u : ↥(I i)) : Q) else 1) := rfl

@[expose] noncomputable def w1369_coord {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {I : Fin 3 → Subgroup Q} (P : w1369_s16h_Proj I Λ) (φ : ↥(I 0) →* Q) :
    Fin 3 → ZMod 2 := by
  classical
  exact fun i => if (P.e i).comp φ = 1 then 0 else 1

lemma w1369_comp_beta_ne_one {Q : Type} [CommGroup Q] {I : Fin 3 → Subgroup Q}
    (hI0 : I 0 ≠ ⊥) (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i)) (i : Fin 3) :
    (I i).subtype.comp (β i).toMonoidHom ≠ 1 := by
  intro h
  obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hI0
  have h1 := congrArg (fun f : ↥(I 0) →* Q => f u) h
  have h2 : ((β i u : ↥(I i)) : Q) = 1 := by simpa using h1
  have h3 : (β i u : ↥(I i)) = 1 := Subtype.ext h2
  exact hu ((β i).injective (by rw [h3, map_one]))

lemma w1369_comp_Phi {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {I : Fin 3 → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i)) (c : Fin 3 → ZMod 2) (i : Fin 3) :
    (P.e i).comp (w1369_Phi β c) =
      if c i = 1 then (I i).subtype.comp (β i).toMonoidHom else 1 := by
  classical
  ext u
  rw [MonoidHom.comp_apply, w1369_Phi_apply, map_prod]
  rw [Finset.prod_eq_single_of_mem (s := Finset.univ)
    (f := fun j : Fin 3 => P.e i (if c j = 1 then ((β j u : ↥(I j)) : Q) else 1))
    i (Finset.mem_univ i)]
  · by_cases h : c i = 1
    · rw [if_pos h, if_pos h]
      exact P.e_self i (β i u : Q) (β i u).2
    · rw [if_neg h, if_neg h]
      exact map_one (P.e i)
  · intro j _ hji
    by_cases h : c j = 1
    · rw [if_pos h]
      exact P.e_other i j hji (β j u : Q) (β j u).2
    · rw [if_neg h]
      exact map_one (P.e i)

lemma w1369_zmod_two_eq_zero_of_ne_one {a : ZMod 2} (h : a ≠ 1) : a = 0 := by
  have h01 : a.val = 0 ∨ a.val = 1 := by
    have := ZMod.val_lt a
    omega
  rcases h01 with h0 | h1
  · exact (ZMod.val_eq_zero a).mp h0
  · exact absurd ((ZMod.val_eq_one (by norm_num) a).mp h1) h

lemma w1369_coord_Phi {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {I : Fin 3 → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i)) (hI0 : I 0 ≠ ⊥) (c : Fin 3 → ZMod 2) :
    w1369_coord P (w1369_Phi β c) = c := by
  funext i
  rw [w1369_coord, w1369_comp_Phi]
  by_cases h : c i = 1
  · rw [if_pos h] at *
    rw [if_neg (w1369_comp_beta_ne_one hI0 β i), h]
  · rw [if_neg h, if_pos rfl, w1369_zmod_two_eq_zero_of_ne_one h]

lemma w1369_prod_ite_eq {G : Type} [CommGroup G] {g : G} (hg : g ^ 2 = 1)
    (b : Fin 3 → ZMod 2) :
    (∏ j : Fin 3, if b j = 1 then g else 1) = if (∑ j : Fin 3, b j) = 0 then 1 else g := by
  classical
  have hprod : (∏ j : Fin 3, if b j = 1 then g else 1) =
      g ^ (Finset.univ.filter (fun j : Fin 3 => b j = 1)).card := by
    rw [show (∏ j : Fin 3, if b j = 1 then g else 1) =
        ∏ j ∈ (Finset.univ.filter (fun j : Fin 3 => b j = 1)), g by
      rw [Finset.prod_ite]; simp]
    rw [Finset.prod_const]
  rw [hprod]
  by_cases hg1 : g = 1
  · rw [hg1]; simp
  · by_cases hsum : (∑ j : Fin 3, b j) = 0
    · rw [if_pos hsum, w1369_pow_eq_one_iff_even hg hg1, w1369_card_filter_eq_sum_val b,
        ← ZMod.natCast_eq_zero_iff_even, ← w1369_sum_eq_natCast_sum_val b]
      exact hsum
    · rw [if_neg hsum]
      obtain ⟨m, hm⟩ : Odd (Finset.univ.filter (fun j : Fin 3 => b j = 1)).card := by
        refine Nat.not_even_iff_odd.mp ?_
        intro heven
        exact hsum (by
          rw [w1369_card_filter_eq_sum_val b] at heven
          rw [w1369_sum_eq_natCast_sum_val b]
          exact ZMod.natCast_eq_zero_iff_even.mpr heven)
      rw [hm, w1369_s16h_pow_odd hg m]

lemma w1369_block_comp_equivariant {Q : Type} [CommGroup Q]
    {Λ : Subgroup (MulAut Q)} {I : Fin 3 → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i))
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hβ : ∀ i, ∀ g (hg : g ∈ Λ) (x : ↥(I 0)),
      ((β i ⟨g (x : Q), hstab 0 g hg (x : Q) x.2⟩ : ↥(I i)) : Q) =
        g ((β i x : ↥(I i)) : Q))
    {x : MulAut Q} (hx : x ∈ Subgroup.centralizer (Λ : Set (MulAut Q))) (i j : Fin 3) :
    ∀ g (hg : g ∈ Λ) (u : ↥(I 0)),
      (((w1369_s16h_block P x i j).comp (β j).toMonoidHom)
        ⟨g (u : Q), hstab 0 g hg (u : Q) u.2⟩ : Q) =
        g ((((w1369_s16h_block P x i j).comp (β j).toMonoidHom) u : ↥(I i)) : Q) := by
  intro g hg u
  change ((w1369_s16h_block P x i j) ((β j) ⟨g (u : Q), hstab 0 g hg (u : Q) u.2⟩) : Q) =
    g ((w1369_s16h_block P x i j) ((β j) u) : Q)
  have h1 : (β j) ⟨g (u : Q), hstab 0 g hg (u : Q) u.2⟩ =
      ⟨g ((β j u : ↥(I j)) : Q), hstab j g hg ((β j u : ↥(I j)) : Q) (β j u).2⟩ :=
    Subtype.ext (hβ j g hg u)
  rw [h1]
  exact w1369_s16h_block_equivariant P hstab (w1369_s16h_cent_comm hx) i j g hg (β j u)

lemma w1369_block_comp_beta {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {I : Fin 3 → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i))
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q,
      (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i → J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hβ : ∀ i, ∀ g (hg : g ∈ Λ) (x : ↥(I 0)),
      ((β i ⟨g (x : Q), hstab 0 g hg (x : Q) x.2⟩ : ↥(I i)) : Q) =
        g ((β i x : ↥(I i)) : Q))
    {x : MulAut Q} (hx : x ∈ Subgroup.centralizer (Λ : Set (MulAut Q))) (i j : Fin 3) :
    (w1369_s16h_block P x i j).comp (β j).toMonoidHom =
      if (w1369_s16h_matrix P x) i j = 1 then (β i).toMonoidHom else 1 := by
  classical
  by_cases hb : w1369_s16h_block P x i j = 1
  · have hmat : (w1369_s16h_matrix P x) i j = 0 := by simp [w1369_s16h_matrix, hb]
    rw [if_neg (by rw [hmat]; exact zero_ne_one), hb]
    simp
  · have hbij := (w1369_s16h_block_one_or_bij P hstab hsimple
      (w1369_s16h_cent_comm hx) i j).resolve_left hb
    have hmat : (w1369_s16h_matrix P x) i j = 1 := by simp [w1369_s16h_matrix, hb]
    rw [if_pos hmat]
    exact w1369_s16h_bijective_unique P hstab hsimple hend _ _
      (hbij.comp (β j).bijective) (β i).bijective
      (w1369_block_comp_equivariant P β hstab hβ hx i j) (hβ i)

lemma w1369_Phi_coord {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {I : Fin 3 → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i))
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q,
      (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i → J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hβ : ∀ i, ∀ g (hg : g ∈ Λ) (x : ↥(I 0)),
      ((β i ⟨g (x : Q), hstab 0 g hg (x : Q) x.2⟩ : ↥(I i)) : Q) =
        g ((β i x : ↥(I i)) : Q))
    {φ : ↥(I 0) →* Q}
    (hφ : ∀ g (hg : g ∈ Λ) (x : ↥(I 0)),
      φ ⟨g (x : Q), hstab 0 g hg (x : Q) x.2⟩ = g (φ x)) :
    φ = w1369_Phi β (w1369_coord P φ) := by
  classical
  ext u
  rw [w1369_Phi_apply]
  rw [← P.e_prod (φ u)]
  apply Finset.prod_congr rfl
  intro i _
  let hφi : ↥(I 0) →* ↥(I i) :=
    MonoidHom.codRestrict ((P.e i).comp φ) (I i) (fun x => P.e_mem i (φ x))
  have hφi_apply : ∀ x : ↥(I 0), ((hφi x : ↥(I i)) : Q) = P.e i (φ x) := fun x => rfl
  have hφie : ∀ g (hg : g ∈ Λ) (x : ↥(I 0)),
      (hφi ⟨g (x : Q), hstab 0 g hg (x : Q) x.2⟩ : Q) = g (hφi x : Q) := by
    intro g hg x
    rw [hφi_apply, hφi_apply, hφ g hg x]
    exact P.e_equiv i g hg (φ x)
  rcases w1369_s16h_hom_zero_or_bij hstab hsimple hφi hφie with h1 | hbij
  · have hcomp : (P.e i).comp φ = 1 := by
      ext x
      rw [MonoidHom.comp_apply, ← hφi_apply, h1]
      rfl
    have hcoord : w1369_coord P φ i = 0 := by rw [w1369_coord]; simp [hcomp]
    rw [hcoord]
    have h3 : P.e i (φ u) = 1 := by
      rw [← hφi_apply, h1]
      rfl
    rw [h3]
    simp
  · have huniq : hφi = β i :=
      w1369_s16h_bijective_unique P hstab hsimple hend hφi (β i) hbij (β i).bijective hφie (hβ i)
    have hcomp : (P.e i).comp φ = (I i).subtype.comp (β i).toMonoidHom := by
      ext x
      rw [MonoidHom.comp_apply, ← hφi_apply, huniq]
      rfl
    have hcoord : w1369_coord P φ i = 1 := by
      rw [w1369_coord, if_neg (by rw [hcomp]; exact w1369_comp_beta_ne_one (hsimple 0).1 β i)]
    rw [hcoord]
    have h3 : P.e i (φ u) = (β i u : Q) := by
      rw [← hφi_apply, huniq]
      rfl
    rw [h3]
    simp

lemma w1369_zmod_two_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  have h01 : a.val = 0 ∨ a.val = 1 := by
    have := ZMod.val_lt a
    omega
  rcases h01 with h0 | h1
  · exact absurd ((ZMod.val_eq_zero a).mp h0) h
  · exact (ZMod.val_eq_one (by norm_num) a).mp h1

lemma w1369_comp_Phi_mul {Q : Type} [CommGroup Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {I : Fin 3 → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i))
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q,
      (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i → J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hβ : ∀ i, ∀ g (hg : g ∈ Λ) (x : ↥(I 0)),
      ((β i ⟨g (x : Q), hstab 0 g hg (x : Q) x.2⟩ : ↥(I i)) : Q) =
        g ((β i x : ↥(I i)) : Q))
    {x : MulAut Q} (hx : x ∈ Subgroup.centralizer (Λ : Set (MulAut Q)))
    (c : Fin 3 → ZMod 2) :
    x.toMonoidHom.comp (w1369_Phi β c) =
      w1369_Phi β (w1369_s16h_matrix P x *ᵥ c) := by
  classical
  ext u
  have hR : ∀ i : Fin 3, P.e i ((w1369_Phi β (w1369_s16h_matrix P x *ᵥ c)) u) =
      (if (w1369_s16h_matrix P x *ᵥ c) i = 1 then ((β i u : ↥(I i)) : Q) else 1) := by
    intro i
    rw [w1369_Phi_apply, map_prod]
    rw [Finset.prod_eq_single_of_mem (s := Finset.univ)
      (f := fun i' : Fin 3 => P.e i (if (w1369_s16h_matrix P x *ᵥ c) i' = 1 then
        ((β i' u : ↥(I i')) : Q) else 1)) i (Finset.mem_univ i)]
    · by_cases h : (w1369_s16h_matrix P x *ᵥ c) i = 1
      · rw [if_pos h]
        exact P.e_self i (β i u : Q) (β i u).2
      · rw [if_neg h]
        exact map_one (P.e i)
    · intro i' _ hi'
      by_cases h : (w1369_s16h_matrix P x *ᵥ c) i' = 1
      · rw [if_pos h]
        exact P.e_other i i' hi' (β i' u : Q) (β i' u).2
      · rw [if_neg h]
        exact map_one (P.e i)
  have hL : ∀ i : Fin 3, P.e i ((x.toMonoidHom.comp (w1369_Phi β c)) u) =
      (if (w1369_s16h_matrix P x *ᵥ c) i = 1 then ((β i u : ↥(I i)) : Q) else 1) := by
    intro i
    rw [MonoidHom.comp_apply, w1369_Phi_apply, map_prod (x.toMonoidHom), map_prod (P.e i)]
    trans ∏ j : Fin 3, (if (w1369_s16h_matrix P x) i j * c j = 1 then
        ((β i u : ↥(I i)) : Q) else 1)
    · apply Finset.prod_congr rfl
      intro j _
      change P.e i (x (if c j = 1 then ((β j u : ↥(I j)) : Q) else 1)) =
        (if (w1369_s16h_matrix P x) i j * c j = 1 then ((β i u : ↥(I i)) : Q) else 1)
      by_cases h : c j = 1
      · have hb : P.e i (x ((β j u : ↥(I j)) : Q)) =
            (if (w1369_s16h_matrix P x) i j = 1 then ((β i u : ↥(I i)) : Q) else 1) := by
          have hb := congrArg (fun f : ↥(I 0) →* ↥(I i) => (f u : Q))
            (w1369_block_comp_beta P β hstab hsimple hend hβ hx i j)
          rw [MonoidHom.comp_apply, w1369_s16h_block_coe] at hb
          exact hb.trans (by by_cases hm : (w1369_s16h_matrix P x) i j = 1 <;> simp [hm])
        rw [if_pos h, hb]
        rw [show (w1369_s16h_matrix P x) i j * c j = (w1369_s16h_matrix P x) i j by
          rw [h, mul_one]]
      · rw [if_neg h]
        have hc : (w1369_s16h_matrix P x) i j * c j = 0 := by
          rw [w1369_zmod_two_eq_zero_of_ne_one h, mul_zero]
        rw [hc, if_neg zero_ne_one]
        simp
    · rw [w1369_prod_ite_eq (hQ _), Matrix.mulVec_apply_eq_sum]
      by_cases hs : (∑ j : Fin 3, (w1369_s16h_matrix P x) i j * c j) = 0
      · rw [if_pos hs, if_neg (by rw [hs]; exact zero_ne_one)]
      · rw [if_neg hs, if_pos (w1369_zmod_two_eq_one_of_ne_zero hs)]
  calc (x.toMonoidHom.comp (w1369_Phi β c)) u
      = ∏ i : Fin 3, P.e i ((x.toMonoidHom.comp (w1369_Phi β c)) u) :=
        (P.e_prod _).symm
    _ = ∏ i : Fin 3, P.e i ((w1369_Phi β (w1369_s16h_matrix P x *ᵥ c)) u) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [hL i, hR i]
    _ = (w1369_Phi β (w1369_s16h_matrix P x *ᵥ c)) u := P.e_prod _

lemma w1369_coord_comp {Q : Type} [CommGroup Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {I : Fin 3 → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i))
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q,
      (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i → J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hβ : ∀ i, ∀ g (hg : g ∈ Λ) (x : ↥(I 0)),
      ((β i ⟨g (x : Q), hstab 0 g hg (x : Q) x.2⟩ : ↥(I i)) : Q) =
        g ((β i x : ↥(I i)) : Q))
    {x : MulAut Q} (hx : x ∈ Subgroup.centralizer (Λ : Set (MulAut Q)))
    {φ : ↥(I 0) →* Q}
    (hφ : ∀ g (hg : g ∈ Λ) (u : ↥(I 0)),
      φ ⟨g (u : Q), hstab 0 g hg (u : Q) u.2⟩ = g (φ u)) :
    w1369_coord P (x.toMonoidHom.comp φ) =
      w1369_s16h_matrix P x *ᵥ w1369_coord P φ := by
  classical
  have hxφ : ∀ g (hg : g ∈ Λ) (u : ↥(I 0)),
      (x.toMonoidHom.comp φ) ⟨g (u : Q), hstab 0 g hg (u : Q) u.2⟩ =
        g ((x.toMonoidHom.comp φ) u) := by
    intro g hg u
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hφ g hg u]
    exact w1369_s16h_cent_comm hx g hg (φ u)
  have h1 : x.toMonoidHom.comp φ =
      w1369_Phi β (w1369_s16h_matrix P x *ᵥ w1369_coord P φ) := by
    calc x.toMonoidHom.comp φ = x.toMonoidHom.comp (w1369_Phi β (w1369_coord P φ)) :=
          congrArg (fun ψ => x.toMonoidHom.comp ψ)
            (w1369_Phi_coord P β hstab hsimple hend hβ hφ)
      _ = w1369_Phi β (w1369_s16h_matrix P x *ᵥ w1369_coord P φ) :=
          w1369_comp_Phi_mul hQ P β hstab hsimple hend hβ hx (w1369_coord P φ)
  have h2 : x.toMonoidHom.comp φ =
      w1369_Phi β (w1369_coord P (x.toMonoidHom.comp φ)) :=
    w1369_Phi_coord P β hstab hsimple hend hβ hxφ
  have h3 : w1369_Phi β (w1369_s16h_matrix P x *ᵥ w1369_coord P φ) =
      w1369_Phi β (w1369_coord P (x.toMonoidHom.comp φ)) := h1.symm.trans h2
  have h4 := congrArg (w1369_coord P) h3
  rw [w1369_coord_Phi P β (hsimple 0).1, w1369_coord_Phi P β (hsimple 0).1] at h4
  exact h4.symm

lemma w1369_exists_iso {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {I : Fin 3 → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i))
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q,
      (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i → J = ⊥ ∨ J = I i)
    (hβ : ∀ i, ∀ g (hg : g ∈ Λ) (x : ↥(I 0)),
      ((β i ⟨g (x : Q), hstab 0 g hg (x : Q) x.2⟩ : ↥(I i)) : Q) =
        g ((β i x : ↥(I i)) : Q))
    {S : Subgroup Q} (hSstab : StableUnder Λ S) (hSne : S ≠ ⊥)
    (hSsimple : ∀ S' : Subgroup Q, StableUnder Λ S' → S' ≤ S → S' = ⊥ ∨ S' = S) :
    ∃ φ : ↥(I 0) →* Q,
      (∀ g (hg : g ∈ Λ) (x : ↥(I 0)),
        φ ⟨g (x : Q), hstab 0 g hg (x : Q) x.2⟩ = g (φ x)) ∧
      Function.Injective φ ∧ φ.range = S := by
  classical
  let proj : ∀ i : Fin 3, ↥S →* ↥(I i) := fun i =>
    MonoidHom.codRestrict ((P.e i).comp S.subtype) (I i) (fun s => P.e_mem i (s : Q))
  have hproj_equiv : ∀ i : Fin 3, ∀ g (hg : g ∈ Λ) (s : ↥S),
      ((proj i ⟨g (s : Q), hSstab g hg (s : Q) s.2⟩ : ↥(I i)) : Q) =
        g ((proj i s : ↥(I i)) : Q) := by
    intro i g hg s
    exact P.e_equiv i g hg (s : Q)
  have hex : ∃ i : Fin 3, Function.Bijective (proj i) := by
    have hex_ne : ∃ i : Fin 3, proj i ≠ 1 := by
      by_contra h
      push Not at h
      apply hSne
      rw [Subgroup.eq_bot_iff_forall]
      intro s hs
      have h1 : (s : Q) = ∏ i : Fin 3, P.e i (s : Q) := (P.e_prod (s : Q)).symm
      rw [h1]
      apply Finset.prod_eq_one
      intro i _
      have h2 : ((proj i ⟨s, hs⟩ : ↥(I i)) : Q) = 1 := by
        have h3 := congrArg (fun f : ↥S →* ↥(I i) => f ⟨s, hs⟩) (h i)
        rw [h3, MonoidHom.one_apply]
        rfl
      change (P.e i) s = 1
      exact h2
    obtain ⟨i, hi⟩ := hex_ne
    refine ⟨i, ?_, ?_⟩
    · rw [← MonoidHom.ker_eq_bot_iff]
      have hKstab : StableUnder Λ ((proj i).ker.map S.subtype) := by
        rintro g hg y ⟨s, hs, rfl⟩
        refine Subgroup.mem_map.mpr ⟨⟨g (s : Q), hSstab g hg (s : Q) s.2⟩, ?_, rfl⟩
        rw [MonoidHom.mem_ker]
        have hs' : proj i s = 1 := MonoidHom.mem_ker.mp hs
        have h := hproj_equiv i g hg s
        rw [hs'] at h
        exact Subtype.ext (by simpa using h)
      rcases hSsimple _ hKstab (Subgroup.map_subtype_le _) with hbot | htop
      · rw [Subgroup.eq_bot_iff_forall]
        intro s hs
        have hmem : (S.subtype s) ∈ (proj i).ker.map S.subtype :=
          Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
        rw [hbot] at hmem
        exact Subtype.ext (by simpa using hmem)
      · exfalso
        apply hi
        ext s
        have hmem : (S.subtype s) ∈ (proj i).ker.map S.subtype := by
          rw [htop]; exact s.2
        obtain ⟨s', hs', hss'⟩ := Subgroup.mem_map.mp hmem
        have hs'' : s' = s := Subtype.ext hss'
        rw [← hs'', MonoidHom.mem_ker.mp hs']
        rfl
    · intro z
      have hLstab : StableUnder Λ ((proj i).range.map (I i).subtype) := by
        rintro g hg y ⟨z, hz, rfl⟩
        rcases MonoidHom.mem_range.mp hz with ⟨s, rfl⟩
        exact Subgroup.mem_map.mpr ⟨proj i ⟨g (s : Q), hSstab g hg (s : Q) s.2⟩, ⟨_, rfl⟩,
          hproj_equiv i g hg s⟩
      rcases (hsimple i).2 _ hLstab (Subgroup.map_subtype_le _) with hbot | htop
      · exfalso
        apply hi
        ext s
        have hmem : ((proj i s : ↥(I i)) : Q) ∈ (proj i).range.map (I i).subtype :=
          Subgroup.mem_map.mpr ⟨proj i s, ⟨s, rfl⟩, rfl⟩
        rw [hbot] at hmem
        simpa using hmem
      · have hmem : (z : Q) ∈ (proj i).range.map (I i).subtype := by rw [htop]; exact z.2
        obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hmem
        rcases MonoidHom.mem_range.mp hw with ⟨s, hs⟩
        exact ⟨s, Subtype.ext (by rw [hs]; exact hwz)⟩
  obtain ⟨i, hbij⟩ := hex
  let e : ↥S ≃* ↥(I i) := MulEquiv.ofBijective (proj i) hbij
  have he_equiv : ∀ g (hg : g ∈ Λ) (s : ↥S),
      ((e ⟨g (s : Q), hSstab g hg (s : Q) s.2⟩ : ↥(I i)) : Q) = g ((e s : ↥(I i)) : Q) :=
    fun g hg s => hproj_equiv i g hg s
  have he_symm_equiv : ∀ g (hg : g ∈ Λ) (z : ↥(I i)),
      ((e.symm ⟨g (z : Q), hstab i g hg (z : Q) z.2⟩ : ↥S) : Q) = g ((e.symm z : ↥S) : Q) := by
    intro g hg z
    have h1 : e ⟨g ((e.symm z : ↥S) : Q), hSstab g hg _ (e.symm z).2⟩ =
        ⟨g (z : Q), hstab i g hg (z : Q) z.2⟩ := by
      apply Subtype.ext
      rw [he_equiv g hg (e.symm z), e.apply_symm_apply z]
    have h2 := congrArg e.symm h1
    rw [e.symm_apply_apply] at h2
    exact (congrArg (fun w : ↥S => (w : Q)) h2).symm
  let iso : ↥(I 0) ≃* ↥S := (β i).trans e.symm
  have hiso_equiv : ∀ g (hg : g ∈ Λ) (y : ↥(I 0)),
      ((iso ⟨g (y : Q), hstab 0 g hg (y : Q) y.2⟩ : ↥S) : Q) = g ((iso y : ↥S) : Q) := by
    intro g hg y
    change ((e.symm ((β i) ⟨g (y : Q), _⟩) : ↥S) : Q) = g ((e.symm ((β i) y) : ↥S) : Q)
    have h1 : (β i) ⟨g (y : Q), hstab 0 g hg (y : Q) y.2⟩ =
        ⟨g ((β i y : ↥(I i)) : Q), hstab i g hg ((β i y : ↥(I i)) : Q) (β i y).2⟩ :=
      Subtype.ext (hβ i g hg y)
    rw [h1]
    exact he_symm_equiv g hg ((β i) y)
  refine ⟨S.subtype.comp iso.toMonoidHom, fun g hg y => hiso_equiv g hg y, ?_, ?_⟩
  · intro a b hab
    exact iso.injective (Subtype.ext hab)
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr iso.surjective]
    ext q
    constructor
    · rintro ⟨s, -, rfl⟩
      exact s.2
    · intro hq
      exact ⟨⟨q, hq⟩, Subgroup.mem_top _, rfl⟩

lemma w1369_center_GL32 : Subgroup.center (GL (Fin 3) (ZMod 2)) = ⊥ := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
  rintro _ ⟨r, rfl⟩
  rw [Subsingleton.elim r 1, map_one]
  exact Subgroup.one_mem _

lemma w1369_exists_simple_sub {Q : Type} [CommGroup Q] [Finite Q]
    {Λ : Subgroup (MulAut Q)} {N : Subgroup Q} (hNstab : StableUnder Λ N) (hNne : N ≠ ⊥) :
    ∃ S : Subgroup Q, S ≤ N ∧ StableUnder Λ S ∧ S ≠ ⊥ ∧
      ∀ T : Subgroup Q, StableUnder Λ T → T ≤ S → T = ⊥ ∨ T = S := by
  classical
  let p : ℕ → Prop := fun m =>
    ∃ S : Subgroup Q, S ≤ N ∧ StableUnder Λ S ∧ S ≠ ⊥ ∧ Nat.card S = m
  have hp : ∃ m, p m := ⟨Nat.card N, N, le_rfl, hNstab, hNne, rfl⟩
  obtain ⟨S, hSN, hSstab, hSne, hScard⟩ := Nat.find_spec hp
  refine ⟨S, hSN, hSstab, hSne, fun T hTstab hTS => ?_⟩
  by_cases h : T = ⊥
  · exact Or.inl h
  · right
    have hle : Nat.card S ≤ Nat.card T := by
      rw [hScard]
      exact Nat.find_min' hp ⟨T, hTS.trans hSN, hTstab, h, rfl⟩
    have hge : Nat.card T ≤ Nat.card S := by
      haveI : Finite ↥S := Finite.of_injective (fun x : ↥S => (x : Q)) Subtype.coe_injective
      exact Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hTS)
    exact Subgroup.eq_of_le_of_card_ge hTS hle

lemma w1369_coord_ne_zero {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {I : Fin 3 → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i))
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q,
      (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i → J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hβ : ∀ i, ∀ g (hg : g ∈ Λ) (x : ↥(I 0)),
      ((β i ⟨g (x : Q), hstab 0 g hg (x : Q) x.2⟩ : ↥(I i)) : Q) =
        g ((β i x : ↥(I i)) : Q))
    {φ : ↥(I 0) →* Q}
    (hφe : ∀ g (hg : g ∈ Λ) (x : ↥(I 0)),
      φ ⟨g (x : Q), hstab 0 g hg (x : Q) x.2⟩ = g (φ x))
    (hφinj : Function.Injective φ) :
    w1369_coord P φ ≠ 0 := by
  intro hc
  have hφ1 : φ = 1 := by
    rw [w1369_Phi_coord P β hstab hsimple hend hβ hφe, hc]
    ext y
    rw [w1369_Phi_apply]
    simp
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hsimple 0).1
  have h1 : φ y = 1 := by rw [hφ1]; rfl
  exact hy (hφinj (h1.trans (map_one φ).symm))

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
