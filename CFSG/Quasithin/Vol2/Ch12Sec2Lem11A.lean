module

public import CFSG.Quasithin.Vol2.KGFactBorelThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertU33

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique

namespace Lem11A

@[expose] def Perm3 (K : Type) [Group K] : Prop :=
  ∀ (S X : Subgroup K) (p : ℕ), IsSylowTwoOf S ⊤ → p.Prime → p ≠ 2 → IsPGroup p ↥X → X ≠ ⊥ →
    (∀ s ∈ S, ∀ x ∈ X, ∃ x' ∈ X, ∃ s' ∈ S, s * x = x' * s') → p = 3

variable {A B : Type} [Group A] [Group B]

theorem eq_one_of_pow_eq_one {p a b : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {x : A}
    (ha : x ^ p ^ a = 1) (hb : x ^ 3 ^ b = 1) : x = 1 := by
  have h1 : orderOf x ∣ p ^ a := orderOf_dvd_of_pow_eq_one ha
  have h2 : orderOf x ∣ 3 ^ b := orderOf_dvd_of_pow_eq_one hb
  have hcop : Nat.Coprime (p ^ a) (3 ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_three).mpr hp3)
  have h3 : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem Perm3.of_surjective [Finite A] (f : A →* B) (hf : Function.Surjective f)
    (hker : IsPGroup 3 ↥f.ker) (h : Perm3 B) : Perm3 A := by
  intro S X p hS hp hp2 hXp hX1 hSX
  by_contra hp3
  have hS' : IsSylowTwoOf (S.map f) ⊤ := by
    have h1 := Lem22.isSylowTwoOf_map_hom hS f
    rwa [Subgroup.map_top_of_surjective f hf] at h1
  refine hp3 (h (S.map f) (X.map f) p hS' hp hp2 (hXp.map f) ?_ ?_)
  · intro h0
    apply hX1
    rw [eq_bot_iff]
    intro x hx
    have hxk : x ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have : f x ∈ X.map f := ⟨x, hx, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      exact this
    obtain ⟨a, ha⟩ := hXp ⟨x, hx⟩
    obtain ⟨b, hb⟩ := hker ⟨x, hxk⟩
    exact Subgroup.mem_bot.mpr (eq_one_of_pow_eq_one hp hp3 (congrArg Subtype.val ha)
      (congrArg Subtype.val hb))
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', s', hs', he⟩ := hSX s hs x hx
    exact ⟨f x', ⟨x', hx', rfl⟩, f s', ⟨s', hs', rfl⟩, by rw [← map_mul, he, map_mul]⟩

theorem Perm3.of_mulEquiv [Finite A] (e : A ≃* B) (h : Perm3 B) : Perm3 A := by
  refine Perm3.of_surjective e.toMonoidHom e.surjective ?_ h
  have hk : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  rw [hk]
  exact IsPGroup.of_bot

theorem perm3_of_model [Finite A] {Γ : Type} [Group Γ] [Finite Γ] (e : A ≃* Γ)
    {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hlat : ∀ Z : Subgroup Γ, S₀ ≤ Z → Z ≠ S₀ → 3 ∣ Nat.card Z) : Perm3 A :=
  fun _ _ _ hS hp hp2 hXp hX1 hSX =>
    Lem22.prime_eq_three_of_model e hS₀ hlat hS hp hp2 hXp hX1 hSX

theorem perm3_mulAut
    (V : Type) [Group V] [Finite V] (n : ℕ)
    (hn : n = 3 ∨ n = 4 ∨ n = 5) (hcard : Nat.card V = 2 ^ n) (hcomm : ∀ x y : V, x * y = y * x)
    (hsq : ∀ x : V, x ^ 2 = 1) : Perm3 (MulAut V) :=
  fun S X p hS hp hp2 hXp hX1 hSX =>
    kgBorelOvergroupThree V n hn hcard hcomm hsq S X p hS hp hp2 hXp hX1 hSX

open CFSG.QuasithinUnique.Bridge.Over in
theorem perm3_sl_three :
    Perm3 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  perm3_of_model Vol2Native.A312L.Seven.z8Equiv CertL32.isSylow_D KGBorelThree.z8_three_dvd

theorem perm3_alt_eight : Perm3 ↥(alternatingGroup (Fin 8)) :=
  perm3_of_model (MulEquiv.refl _) KGMinPar.a8_sylow KGBorelThree.a8_three_dvd

theorem perm3_gl_five :
    Perm3 (GL (Fin 5) (ZMod 2)) :=
  perm3_of_model (MulEquiv.refl _) KGMinPar.l52_S_sylow KGBorelThree.l52_three_dvd

theorem perm3_sl_five :
    Perm3 (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
  Perm3.of_mulEquiv (Setup.Family.slEquivGL 5) perm3_gl_five

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Bridge.Over
  CFSG.GH74.KGroups in
theorem u33_three_dvd :
    ∀ Z : Subgroup ↥U33.QP.originalSubgroup, CertU33.D.subgroupOf U33.QP.originalSubgroup ≤ Z →
      Z ≠ CertU33.D.subgroupOf U33.QP.originalSubgroup → 3 ∣ Nat.card Z := by
  intro Z hZ hne
  let Z' : Subgroup (Perm (Fin 28)) := Z.map U33.QP.originalSubgroup.subtype
  have hDZ : Subgroup.closure {g | g ∈ CertU33.cert.tGens} ≤ Z' := fun t ht => by
    have htD : t ∈ CertU33.D := ht
    have htM : t ∈ U33.QP.originalSubgroup := CertU33.D_le htD
    have h1 : (⟨t, htM⟩ : ↥U33.QP.originalSubgroup) ∈ Z :=
      hZ (Subgroup.mem_subgroupOf.mpr htD)
    exact ⟨⟨t, htM⟩, h1, rfl⟩
  have hZM : Z' ≤ Subgroup.closure {g | g ∈ CertU33.cert.mGens} := by
    show Z' ≤ Subgroup.closure {g | g ∈ CertU33.mGens}
    rw [CertU33.closure_mGens]
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  obtain ⟨Lg, hL, hZL⟩ := CertU33.cert.overgroups (rawIsEnc 28) CertU33.cert_check Z' hDZ hZM
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hL
  have hcardZ : Nat.card Z = Nat.card Z' :=
    (Subgroup.card_map_of_injective U33.QP.originalSubgroup.subtype_injective).symm
  have hcard := CertU33.cert.card_member_idx (rawIsEnc 28)
    (CertU33.cert.closedOK_of_check CertU33.cert_check)
    (CertU33.cert.sizesOK_of_check CertU33.cert_check) j hj
  rw [← hZL, ← hcardZ] at hcard
  have hj4 : j < 4 := hj
  rw [hcard]
  interval_cases j
  · exfalso
    apply hne
    have hZZ : Z'.subgroupOf U33.QP.originalSubgroup = Z :=
      Subgroup.comap_map_eq_self_of_injective U33.QP.originalSubgroup.subtype_injective Z
    rw [← hZZ, hZL]
    rfl
  all_goals decide

open CFSG.QuasithinUnique.Bridge.Over in
theorem perm3_u33 :
    Perm3 ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup :=
  perm3_of_model (MulEquiv.refl _) CertU33.isSylow_D u33_three_dvd

end Lem11A

end CFSG.Quasithin.H13
