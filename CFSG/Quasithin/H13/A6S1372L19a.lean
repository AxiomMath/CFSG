module

public import CFSG.Quasithin.H13.A6S1372L24a
import CFSG.Quasithin.H13.A6S1372L19aPack

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.QuasithinUnique CFSG.Quasithin

namespace A6L19

open CFSG.Permutation.FinPack CFSG.Quasithin.H13.L32A.C.Alt7Pack CFSG.Quasithin.H13.A6.L19aPack

@[expose] def kl (a b : Perm (Fin 5)) : List (Perm (Fin 5)) := [1, a, b, a * b]

@[expose] def IsKl (a b : Perm (Fin 5)) : Prop :=
  a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ Perm.sign a = 1 ∧
    Perm.sign b = 1

instance (a b : Perm (Fin 5)) : Decidable (IsKl a b) := by unfold IsKl; infer_instance

@[expose] def NormKl (a b g : Perm (Fin 5)) : Prop := g * a * g⁻¹ ∈ kl a b ∧ g * b * g⁻¹ ∈ kl a b

instance (a b g : Perm (Fin 5)) : Decidable (NormKl a b g) := by unfold NormKl; infer_instance

@[expose] def CosKl (a b s : Perm (Fin 5)) : Prop :=
  s * s * s = 1 ∧ ∀ v ∈ kl a b, v * s * v⁻¹ ∈ (kl a b).flatMap fun w => [w, s * w, s * s * w]

instance (a b s : Perm (Fin 5)) : Decidable (CosKl a b s) := by unfold CosKl; infer_instance

@[expose] def ThreeKl (a b s : Perm (Fin 5)) : Prop := s * s * s = 1 ∧ s ≠ 1 ∧ NormKl a b s

instance (a b s : Perm (Fin 5)) : Decidable (ThreeKl a b s) := by unfold ThreeKl; infer_instance

@[expose] def CentKl (a b s g : Perm (Fin 5)) : Prop :=
  g ^ 8 = 1 ∧ NormKl a b g ∧ g * s * g⁻¹ * s⁻¹ ∈ kl a b

instance (a b s g : Perm (Fin 5)) : Decidable (CentKl a b s g) := by
  unfold CentKl; infer_instance

theorem two_mem_check : ∀ a b : Perm (Fin 5), IsKl a b → ∀ g : Perm (Fin 5), g ^ 8 = 1 →
    NormKl a b g → Perm.sign g = 1 → g ∈ kl a b := by
  intro a b h g hg hn hs
  obtain ⟨ha, hb, hab, ha1, hb1, hne, hsa, hsb⟩ := h
  have hF := allK_iff.1 (forall_kl t1_ok ha hb hab ha1 hb1 hne hsa hsb) _
    (memK_iff.1 (mem_twoC hg))
  rw [(normK5_iff a b g).1 hn, (sign_eq_one_iff_evenK h5 g).1 hs] at hF
  simp only [Bool.not_true, Bool.false_or] at hF
  exact (mem_kl_iff a b g).2 hF

theorem normalizes_check : ∀ a b : Perm (Fin 5), IsKl a b → ∀ s : Perm (Fin 5), CosKl a b s →
    NormKl a b s := by
  intro a b h s hc
  obtain ⟨ha, hb, hab, ha1, hb1, hne, hsa, hsb⟩ := h
  have hF := allK_iff.1 (forall_kl t2_ok ha hb hab ha1 hb1 hne hsa hsb) _
    (memK_iff.1 (mem_c3eC hc.1))
  rw [cosK_of a b s hc.2] at hF
  simp only [Bool.not_true, Bool.false_or] at hF
  exact (normK5_iff a b s).2 hF

theorem centralizes_check : ∀ a b : Perm (Fin 5), IsKl a b → ∀ s : Perm (Fin 5), ThreeKl a b s →
    ∀ g : Perm (Fin 5), CentKl a b s g → g ∈ kl a b := by
  intro a b h s hs g hg
  obtain ⟨ha, hb, hab, ha1, hb1, hne, hsa, hsb⟩ := h
  obtain ⟨hs3, hs1, hsn⟩ := hs
  obtain ⟨hg8, hgn, hgc⟩ := hg
  have hF := allK_iff.1 (forall_kl t3_ok ha hb hab ha1 hb1 hne hsa hsb) _
    (memK_iff.1 (mem_c3eC hs3))
  rw [beq_one_false hs1, (normK5_iff a b s).1 hsn] at hF
  simp only [Bool.not_true, Bool.false_or] at hF
  have hG := allK_iff.1 hF _ (memK_iff.1 (mem_twoC hg8))
  have hc : memK (mulK 5 (conjK5 (enc g) (enc s)) (invCK 5 (enc s))) (klK (enc a) (enc b)) =
      true := by
    rw [← enc_conj, ← enc_inv_invCK h5, ← enc_mul h5, ← mem_kl_iff]
    exact hgc
  rw [(normK5_iff a b g).1 hgn, hc] at hG
  simp only [Bool.not_true, Bool.false_or] at hG
  exact (mem_kl_iff a b g).2 hG

theorem exists_normalizing_check : ∀ a b : Perm (Fin 5), IsKl a b →
    ∃ s : Perm (Fin 5), ThreeKl a b s := by
  intro a b h
  obtain ⟨ha, hb, hab, ha1, hb1, hne, hsa, hsb⟩ := h
  have hF := forall_kl t4_ok ha hb hab ha1 hb1 hne hsa hsb
  have hw : walkK 5 (fun c => !(t3K c && normK5 (enc a) (enc b) c)) 5 0 0 0 = false := by
    simpa using hF
  obtain ⟨s, hs⟩ := exists_of_walkK (P := fun c => t3K c && normK5 (enc a) (enc b) c) hw
  rw [Bool.and_eq_true, t3K, Bool.and_eq_true] at hs
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  rw [← enc_mul h5, ← enc_mul h5, ← enc_one5, beq_enc_iff h5] at h1
  refine ⟨s, h1, fun hs1 => ?_, (normK5_iff a b s).2 h3⟩
  rw [hs1, enc_one5, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem sq_check : ∀ g : Perm (Fin 5), g ^ 8 = 1 → Perm.sign g = 1 → g * g = 1 := by
  intro g hg hs
  have h := allK_iff.1 t5_ok _ (memK_iff.1 (mem_twoC hg))
  rw [(sign_eq_one_iff_evenK h5 g).1 hs, ← enc_mul h5, ← enc_one5] at h
  simp only [Bool.not_true, Bool.false_or] at h
  exact (beq_enc_iff h5).1 h

theorem pow_eight_of_pow {g : Perm (Fin 5)} {k : ℕ} (hk : g ^ 2 ^ k = 1) : g ^ 8 = 1 := by
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf g ∣ 120 := by
    have := orderOf_dvd_card (G := Perm (Fin 5)) (x := g)
    rw [Fintype.card_perm, Fintype.card_fin] at this
    exact this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj3 : j ≤ 3 := by
    by_contra hj3
    push Not at hj3
    have h3 : 2 ^ 4 ∣ 120 := (pow_dvd_pow 2 hj3).trans (hj ▸ h2)
    norm_num at h3
  exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ (pow_dvd_pow 2 hj3).trans (by norm_num))

theorem sign_eq_one_of_pow_odd {g : Perm (Fin 5)} {m : ℕ} (hm : Odd m) (hg : g ^ m = 1) :
    Perm.sign g = 1 := by
  have h1 : Perm.sign g ^ m = 1 := by rw [← map_pow, hg, map_one]
  rcases Int.units_eq_one_or (Perm.sign g) with h | h
  · exact h
  · rw [h, hm.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem exists_kl {D : Subgroup (Perm (Fin 5))} (h4 : Nat.card D = 4)
    (h2 : ∀ x ∈ D, x ^ 8 = 1) (hs : ∀ x ∈ D, Perm.sign x = 1) :
    ∃ a b : Perm (Fin 5), IsKl a b ∧ ∀ x, x ∈ D ↔ x ∈ kl a b := by
  classical
  have hex : ∀ s : Finset (Perm (Fin 5)), s.card < Nat.card D → ∃ a ∈ D, a ∉ s := by
    intro s hs'
    by_contra hcon
    push Not at hcon
    have hsub : (D : Set (Perm (Fin 5))) ⊆ (s : Set (Perm (Fin 5))) := fun a ha => hcon a ha
    have h1 : Nat.card D ≤ Nat.card (s : Set (Perm (Fin 5))) := Nat.card_mono s.finite_toSet hsub
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset] at h1
    omega
  have hsq : ∀ x ∈ D, x * x = 1 := fun x hx => sq_check x (h2 x hx) (hs x hx)
  have key : ∀ x ∈ D, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hsq x hx)
  obtain ⟨a, ha, ha1⟩ := hex {1} (by rw [Finset.card_singleton]; omega)
  obtain ⟨b, hb, hb1⟩ := hex {1, a}
    (by have := Finset.card_le_two (a := (1 : Perm (Fin 5))) (b := a); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha1 hb1
  have hab : a * b = b * a := by
    have e1 : a * b = (a * b)⁻¹ := (key _ (D.mul_mem ha hb)).symm
    rw [mul_inv_rev, key _ ha, key _ hb] at e1
    exact e1
  have hab1 : a * b ≠ 1 := fun h => hb1.2 (by
    calc b = a⁻¹ * (a * b) := by group
      _ = a := by rw [h, mul_one, key _ ha])
  have haba : a * b ≠ a := fun h => hb1.1 (by
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  have habb : a * b ≠ b := fun h => ha1 (by
    calc a = a * b * b⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  set s : Finset (Perm (Fin 5)) := {1, a, b, a * b} with hsdef
  have hs4 : s.card = 4 := Finset.card_eq_four.2 ⟨1, a, b, a * b, fun h => ha1 h.symm,
    fun h => hb1.1 h.symm, fun h => hab1 h.symm, fun h => hb1.2 h.symm, fun h => haba h.symm,
    fun h => habb h.symm, rfl⟩
  have hsub : (s : Set (Perm (Fin 5))) ⊆ D := by
    intro y hy
    simp only [hsdef, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact D.one_mem
    · exact ha
    · exact hb
    · exact D.mul_mem ha hb
  have heq : (s : Set (Perm (Fin 5))) = D := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, hs4, ← Nat.card_coe_set_eq]
    exact h4.le
  refine ⟨a, b, ⟨hsq a ha, hsq b hb, hab, ha1, hb1.1, fun h => hb1.2 h.symm, hs a ha, hs b hb⟩,
    fun x => ?_⟩
  rw [← SetLike.mem_coe, ← heq]
  simp [hsdef, kl]

@[expose] noncomputable def autA5 : Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl (by norm_num))

theorem autA5_apply (σ : Perm (Fin 5)) (a : alternatingGroup (Fin 5)) :
    ((autA5 σ a : alternatingGroup (Fin 5)) : Perm (Fin 5)) = σ * a * σ⁻¹ :=
  MulAut.conjNormal_apply σ a

variable {G : Type} [Group G] {K P E : Subgroup G}

@[expose] noncomputable def gam5 (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* alternatingGroup (Fin 5)}
    (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) :
    ↥E →* Perm (Fin 5) :=
  autA5.symm.toMonoidHom.comp (A6L24.gamX hEK hEP hs hα)

section Gam5

variable (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hEP : E ≤ Subgroup.normalizer (P : Set G))
  {α : ↥K →* alternatingGroup (Fin 5)} (hs : Function.Surjective α)
  (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P)

theorem autA5_gam5 (e : ↥E) : autA5 (gam5 hEK hEP hs hα e) = A6L24.gamX hEK hEP hs hα e :=
  autA5.apply_symm_apply _

theorem gam5_conj (e : ↥E) (k : ↥K) :
    gam5 hEK hEP hs hα e * (α k : Perm (Fin 5)) * (gam5 hEK hEP hs hα e)⁻¹ =
      (α (AutA6Rank.conjK hEK e k) : Perm (Fin 5)) := by
  rw [← autA5_apply, autA5_gam5, A6L24.gamX_apply hEK hEP hs hα]

theorem gam5_of_mem (k : ↥K) (hk : (k : G) ∈ E) :
    gam5 hEK hEP hs hα ⟨k, hk⟩ = (α k : Perm (Fin 5)) := by
  apply autA5.injective
  rw [autA5_gam5]
  refine MulEquiv.ext fun a => ?_
  obtain ⟨k', rfl⟩ := hs a
  rw [A6L24.gamX_apply hEK hEP hs hα]
  apply Subtype.ext
  rw [autA5_apply]
  have e : AutA6Rank.conjK hEK ⟨k, hk⟩ k' = k * k' * k⁻¹ :=
    Subtype.ext (by rw [AutA6Rank.conjK_coe]; rfl)
  rw [e, map_mul, map_mul, map_inv]
  rfl

theorem gam5_eq_one_iff (e : ↥E) :
    gam5 hEK hEP hs hα e = 1 ↔ ∀ k ∈ K, (e : G) * k * (e : G)⁻¹ * k⁻¹ ∈ P := by
  have e0 : gam5 hEK hEP hs hα e = autA5.symm (A6L24.gamX hEK hEP hs hα e) := rfl
  rw [e0, MulEquiv.map_eq_one_iff]
  constructor
  · intro h k hk
    have h1 := congrArg (fun γ : MulAut (alternatingGroup (Fin 5)) => γ (α ⟨k, hk⟩)) h
    simp only [A6L24.gamX_apply, MulAut.one_apply] at h1
    have h2 : α (AutA6Rank.conjK hEK e ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (hα _).1 h2
    simpa [AutA6Rank.conjK_coe] using h3
  · intro h
    refine MulEquiv.ext fun a => ?_
    obtain ⟨k, rfl⟩ := hs a
    rw [A6L24.gamX_apply, MulAut.one_apply]
    have h1 : α (AutA6Rank.conjK hEK e k * k⁻¹) = 1 := by
      rw [hα]
      simpa [AutA6Rank.conjK_coe] using h k k.2
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1

end Gam5

theorem sign_of_mem_oTwoRes {X : Subgroup G} (hXE : oTwoRes X ≤ E) (f : ↥E →* Perm (Fin 5))
    {x : G} (hx : x ∈ oTwoRes X) : Perm.sign (f ⟨x, hXE hx⟩) = 1 := by
  have hle : oTwoRes X ≤ ((Perm.sign.comp f).ker).map E.subtype := by
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    have hyE : y ∈ E := hXE (Subgroup.subset_closure hy)
    obtain ⟨-, m, hm, hym⟩ := hy
    refine ⟨⟨y, hyE⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
    refine sign_eq_one_of_pow_odd hm ?_
    rw [← map_pow]
    have : (⟨y, hyE⟩ : ↥E) ^ m = 1 := Subtype.ext (by simpa using hym)
    rw [this, map_one]
  obtain ⟨y, hy, hyx⟩ := hle hx
  have e : y = ⟨x, hXE hx⟩ := Subtype.ext hyx
  rw [← e]
  exact hy

end A6L19

end CFSG.Quasithin.H13.A6
