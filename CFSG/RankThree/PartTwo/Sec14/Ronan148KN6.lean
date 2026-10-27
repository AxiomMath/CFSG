module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Reduction
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.K71Item119
public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig

@[expose] def L3SigType (X : Type) [Group X] (K' : Subgroup X) : Prop :=
  K' = ⊤ ∨
    ((∃ _ : Fact (Nat.Prime 5),
        Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2)) ∨
          Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSU 3 5 1)) ∧
      Nonempty (↥K' ≃* alternatingGroup (Fin 7))) ∨
    (∃ (p f e' : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e' ∧ Sec4.IsoLThreePi X p (f * e') ∧
      IsLThreeEpsAt ↥K' p f)

theorem isoLThreePi_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) {p e : ℕ}
    [Fact p.Prime] (h : Sec4.IsoLThreePi X p e) : Sec4.IsoLThreePi Y p e := by
  unfold Sec4.IsoLThreePi at h ⊢
  rcases h with ⟨hm, ⟨ψ⟩⟩ | ⟨hm, ⟨ψ⟩⟩
  · exact Or.inl ⟨hm, ⟨φ.symm.trans ψ⟩⟩
  · exact Or.inr ⟨hm, ⟨φ.symm.trans ψ⟩⟩

theorem isLThreePi_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    (h : Sec13.IsLThreePi X) : Sec13.IsLThreePi Y := by
  unfold Sec13.IsLThreePi at h ⊢
  obtain ⟨p, e, hp, he, h'⟩ := h
  exact ⟨p, e, hp, he, isoLThreePi_of_mulEquiv φ h'⟩

theorem isLThreeEpsAt_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) {p f : ℕ}
    [Fact p.Prime] (h : IsLThreeEpsAt X p f) : IsLThreeEpsAt Y p f := by
  unfold IsLThreeEpsAt at h ⊢
  rcases h with ⟨⟨ψ⟩⟩ | ⟨h2, ⟨ψ⟩⟩
  · exact Or.inl ⟨φ.symm.trans ψ⟩
  · exact Or.inr ⟨h2, ⟨φ.symm.trans ψ⟩⟩

theorem aschbacherSolvableCore_eq_bot_of_simple_not_solvable {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hns : ¬ Group.IsSolvable S) : aschbacherSolvableCore 3 S = ⊥ := by
  refine aschbacherSolvableCore_eq_bot_of_isSimpleGroup ?_
  by_contra hcon
  apply hns
  apply IsSimpleGroup.comm_iff_isSolvable.mp
  intro a b
  by_contra hab
  exact hcon ⟨a, b, hab⟩

theorem aschbacherSolvableCore_eq_bot_of_mulEquiv {S T : Type} [Group S] [Finite S] [Group T]
    [IsSimpleGroup T] (e : S ≃* T) (hns : ¬ Group.IsSolvable T) :
    aschbacherSolvableCore 3 S = ⊥ := by
  haveI : IsSimpleGroup S := e.isSimpleGroup
  refine aschbacherSolvableCore_eq_bot_of_simple_not_solvable ?_
  intro hs
  exact hns (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

theorem isSimpleGroup_projSL_three_field (p f : ℕ) [Fact p.Prime] :
    IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) :=
  CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _

theorem not_isSolvable_projSL_three (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) :
    ¬ Group.IsSolvable (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) := by
  haveI := isSimpleGroup_projSL_three_field p f
  by_cases hq2 : 2 < p ^ f
  · haveI : Group.IsPerfect (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) := by
      rw [Sec13.projSL_eq]
      exact Sec13.isPerfect_projImage_slPi (Sec13.piField_galoisField p f hf) hq2
    exact Group.IsPerfect.not_isSolvable _
  · have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
    have hq : p ^ f = 2 := by
      have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have h3 : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      omega
    haveI : Finite (GaloisField p f) :=
      Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    have hcard : Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) = 168 := by
      obtain ⟨ν⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_sl3_mulEquiv_projSL
        (F := GaloisField p f) (by simp [hF, hq])
      rw [← Nat.card_congr ν.toEquiv, CFSG.RankThree.PartTwo.KFacts.card_sl_three_eq, hF, hq] <;>
        norm_num
    intro hs
    have hcomm : ∀ a b : CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f),
        a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.mpr hs
    letI : CommGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) :=
      { (inferInstance : Group (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f))) with
        mul_comm := hcomm }
    have hp : (Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f))).Prime :=
      CommGroup.is_simple_iff_prime_card.mp (isSimpleGroup_projSL_three_field p f)
    rw [hcard] at hp
    norm_num at hp

theorem not_isSolvable_projSU_three (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) (hq2 : 2 < p ^ f) :
    ¬ Group.IsSolvable (CFSG.Assembly.RankThreeEven.projSU 3 p f) := by
  haveI := CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f
    hf (by omega)
  haveI : Group.IsPerfect (CFSG.Assembly.RankThreeEven.projSU 3 p f) := by
    rw [Sec13.projSU_eq]
    exact Sec13.isPerfect_projImage_slPi (Sec13.piField_galoisField_two p f hf) hq2
  exact Group.IsPerfect.not_isSolvable _

theorem isSimpleGroup_alt_seven : IsSimpleGroup (alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem not_isSolvable_alt_seven : ¬ Group.IsSolvable (alternatingGroup (Fin 7)) := by
  intro hs
  haveI := isSimpleGroup_alt_seven
  have hcomm : ∀ a b : alternatingGroup (Fin 7), a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr hs
  have h01 : (0 : Fin 7) ≠ 1 := by decide
  have h12 : (1 : Fin 7) ≠ 2 := by decide
  have h13 : (1 : Fin 7) ≠ 3 := by decide
  have h1 : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h01,
      Equiv.Perm.sign_swap h12] <;> decide
  have h2 : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 3) ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h01,
      Equiv.Perm.sign_swap h13] <;> decide
  have key : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) *
      (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 3) ≠
      (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 3) *
        (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) := by
    decide
  exact key (congrArg Subtype.val (hcomm ⟨_, h1⟩ ⟨_, h2⟩))

theorem isSimpleGroup_of_isLThreePi_not_solvable {X : Type} [Group X] [Finite X]
    (hX : Sec13.IsLThreePi X) (hns : ¬ Group.IsSolvable X) : IsSimpleGroup X := by
  unfold Sec13.IsLThreePi at hX
  obtain ⟨p, e, hp, he, hiso⟩ := hX
  unfold Sec4.IsoLThreePi at hiso
  rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨hmod, ⟨φ⟩⟩
  · haveI := isSimpleGroup_projSL_three_field p e
    exact φ.isSimpleGroup
  · by_cases hq : p ^ e = 2
    · exfalso
      have hp2 : p = 2 := by
        have hd : p ∣ 2 := by
          rw [← hq]
          exact dvd_pow_self p (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd
      subst hp2
      have he1 : e = 1 := by
        have h2 : 2 ^ e = 2 ^ 1 := by simpa using hq
        exact Nat.pow_right_injective (le_refl 2) h2
      subst he1
      haveI := Sec13.isSolvable_projSU_two
      exact hns (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
    · haveI := CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two
        p e he hq
      exact φ.isSimpleGroup

section Image

variable {Γ : Type} [Group Γ] {A L K : Subgroup Γ} {X : Type} [Group X]

theorem kappa_actX (hKL : K ≤ L) (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X)
    (hAL : A ≤ normalizer (L : Set Γ)) (hAK : A ≤ normalizer (K : Set Γ)) (a : A) (k : K) :
    actX hAL ψ a (kappa hKL ψ k) = kappa hKL ψ ⟨(a : Γ) * k * (a : Γ)⁻¹, (hAK a.2 k).mp k.2⟩ := by
  rw [kappa_apply, kappa_apply]
  exact actX_toX hAL ψ a (inclusion hKL k)

theorem actX_kappa_eq_self (hKL : K ≤ L) (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X)
    (hAL : A ≤ normalizer (L : Set Γ)) (hAK : A ≤ normalizer (K : Set Γ)) (a : A) (k : K)
    (hk : (a : Γ) * k = k * a) : actX hAL ψ a (kappa hKL ψ k) = kappa hKL ψ k := by
  rw [kappa_actX hKL ψ hAL hAK a k]
  congr 1
  exact Subtype.ext (show (a : Γ) * k * (a : Γ)⁻¹ = k by rw [hk, mul_inv_cancel_right])

@[expose] noncomputable def centAut (hKL : K ≤ L) (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X)
    (hAL : A ≤ normalizer (L : Set Γ)) (hAK : A ≤ normalizer (K : Set Γ)) (a : A) :
    ↥(K ⊓ centralizer ({(a : Γ)} : Set Γ)) →*
      ↥((kappa hKL ψ).range ⊓ Sec4.autFix (actX hAL ψ a)) where
  toFun c := ⟨kappa hKL ψ ⟨c, (mem_inf.1 c.2).1⟩, mem_inf.2 ⟨⟨_, rfl⟩, Sec4.mem_autFix.2
    (actX_kappa_eq_self hKL ψ hAL hAK a ⟨c, (mem_inf.1 c.2).1⟩
      (mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).2).symm)⟩⟩
  map_one' := Subtype.ext (map_one (kappa hKL ψ))
  map_mul' c d := Subtype.ext (map_mul (kappa hKL ψ) ⟨c, (mem_inf.1 c.2).1⟩
    ⟨d, (mem_inf.1 d.2).1⟩)

theorem coe_centAut (hKL : K ≤ L) (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X)
    (hAL : A ≤ normalizer (L : Set Γ)) (hAK : A ≤ normalizer (K : Set Γ)) (a : A)
    (c : ↥(K ⊓ centralizer ({(a : Γ)} : Set Γ))) :
    ((centAut hKL ψ hAL hAK a c : ↥((kappa hKL ψ).range ⊓ Sec4.autFix (actX hAL ψ a))) : X) =
      kappa hKL ψ ⟨c, (mem_inf.1 c.2).1⟩ :=
  rfl

theorem centAut_surjective [Finite Γ] (hKL : K ≤ L) (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X)
    (hAL : A ≤ normalizer (L : Set Γ)) (hAK : A ≤ normalizer (K : Set Γ))
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) (a : A) :
    Function.Surjective (centAut hKL ψ hAL hAK a) := by
  rintro ⟨d, hd⟩
  obtain ⟨⟨k0, rfl⟩, hdfix⟩ := mem_inf.1 hd
  have hfix : actX hAL ψ a (kappa hKL ψ k0) = kappa hKL ψ k0 := Sec4.mem_autFix.1 hdfix
  set n : normalizer (K : Set Γ) := ⟨a, hAK a.2⟩ with hn
  set σ := K.normalizerMonoidHom n with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : n ^ 3 = 1 := Subtype.ext (by simpa [hn] using hA3 a a.2)
    rw [this, map_one]
  have hσg : ∀ g : K, (σ g : Γ) = (a : Γ) * g * (a : Γ)⁻¹ := fun g => rfl
  have hy : ∀ g : K, kappa hKL ψ g = kappa hKL ψ k0 → kappa hKL ψ (σ g) = kappa hKL ψ k0 := by
    intro g hg
    have e : σ g = ⟨(a : Γ) * g * (a : Γ)⁻¹, (hAK a.2 g).mp g.2⟩ := Subtype.ext (hσg g)
    rw [e, ← kappa_actX hKL ψ hAL hAK a g, hg, hfix]
  obtain ⟨g, hg, hσg'⟩ := CFSG.AGLEmbeddingD2.Wilson.Proving.exists_fixed_lift_of_pow_three
    (kappa hKL ψ) (coprime_card_ker_kappa hKL ψ) σ hσ3 hy
  have hgx : (g : Γ) ∈ centralizer ({(a : Γ)} : Set Γ) := by
    rw [mem_centralizer_singleton_iff]
    have h1 := congrArg Subtype.val hσg'
    rw [hσg] at h1
    calc (g : Γ) * (a : Γ) = ((a : Γ) * g * (a : Γ)⁻¹) * (a : Γ) := by rw [h1]
      _ = (a : Γ) * g := by group
  exact ⟨⟨g, mem_inf.2 ⟨g.2, hgx⟩⟩, Subtype.ext hg⟩

theorem map_pPrimeCoreOf_le_autFix [Finite Γ] (hKL : K ≤ L)
    (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X)
    (hAL : A ≤ normalizer (L : Set Γ)) (hAK : A ≤ normalizer (K : Set Γ))
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) (a : A) :
    ((pPrimeCoreOf 3 (K ⊓ centralizer ({(a : Γ)} : Set Γ))).subgroupOf K).map (kappa hKL ψ) ≤
      pPrimeCoreOf 3 ((kappa hKL ψ).range ⊓ Sec4.autFix (actX hAL ψ a)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨c, hc', hck⟩ := mem_subgroupOf.1 hk
  have hmem := CFSG.map_pPrimeCore_le (p := 3) (centAut hKL ψ hAL hAK a)
    (centAut_surjective hKL ψ hAL hAK hA3 a) ⟨c, hc', rfl⟩
  refine ⟨_, hmem, ?_⟩
  rw [coe_subtype, coe_centAut]
  congr 1
  exact Subtype.ext hck

theorem range_kappa_ne_bot [Finite Γ] {A L K : Subgroup Γ} {e : Γ} (h : Sig148 A L K e)
    (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X) : (kappa h.le ψ).range ≠ ⊥ := by
  intro hb
  have hntq := CFSG.LocalCores.isQuasisimple_nontrivial h.isQuasisimple
  have hnt : Nontrivial K := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : Subsingleton (K ⧸ aschbacherSolvableCore 3 K) :=
      (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 K)).subsingleton
    exact not_nontrivial _ hntq
  have hall : ∀ k : K, k ∈ (kappa h.le ψ).ker := fun k => by
    rw [MonoidHom.mem_ker]
    have : kappa h.le ψ k ∈ (kappa h.le ψ).range := ⟨k, rfl⟩
    rwa [hb, mem_bot] at this
  have hsk := isSolvable_ker_kappa h.le ψ
  let f : K →* (kappa h.le ψ).ker :=
    { toFun := fun k => ⟨k, hall k⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinj : Function.Injective f := fun k k' hkk => congrArg Subtype.val hkk
  have hsK : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective hinj
  haveI : Group.IsPerfect K := h.isPerfect
  exact Group.IsPerfect.not_isSolvable K hsK

end Image

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
