module

public import Mathlib.GroupTheory.Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.H13.S126P31

open Equiv

private theorem factorization_six_two_P31 : Nat.factorization 6 2 = 1 := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6, Nat.factorization_mul (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (3 : ℕ) ≠ 0),
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]

private theorem card_sylow_two_of_card_six_P31 {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 6) (P : Sylow 2 G) : Nat.card P = 2 := by
  rw [Sylow.card_eq_multiplicity P, hG, factorization_six_two_P31]
  norm_num

private theorem finite_sylow_two_P31 (G : Type*) [Group G] [Finite G] : Finite (Sylow 2 G) :=
  Finite.of_injective (fun P : Sylow 2 G => (P : Set G)) SetLike.coe_injective

private theorem card_sylow_two_eq_three_P31 {Y : Type*} [Group Y] [Finite Y]
    (C : Subgroup Y) [C.Normal] (hC : Nat.card C = 6)
    (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥) :
    Nat.card (Sylow 2 C) = 3 := by
  haveI := finite_sylow_two_P31 C
  obtain ⟨P⟩ : Nonempty (Sylow 2 C) := inferInstance
  have hPcard : Nat.card (P : Subgroup C) = 2 := card_sylow_two_of_card_six_P31 hC P
  have hidx : (P : Subgroup C).index = 3 := by
    have hmi := Subgroup.card_mul_index (H := (P : Subgroup C))
    rw [hPcard, hC] at hmi
    omega
  have hdvd : Nat.card (Sylow 2 C) ∣ 3 := by
    have h := Sylow.card_dvd_index P
    rw [hidx] at h
    exact h
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exfalso
    have hsub : Subsingleton (Sylow 2 C) := (Nat.card_eq_one_iff_unique.mp h).1
    haveI : (P : Subgroup C).Characteristic := Sylow.characteristic_of_subsingleton P
    haveI : ((P : Subgroup C).map C.subtype).Normal := inferInstance
    have hmapcard : Nat.card ((P : Subgroup C).map C.subtype) = 2 := by
      rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact hPcard
    have hpg : IsPGroup 2 ((P : Subgroup C).map C.subtype) := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [hmapcard]; norm_num⟩
    have hN := hO2 ((P : Subgroup C).map C.subtype) inferInstance hpg
    have h1 : Nat.card ((P : Subgroup C).map C.subtype) = 1 := by
      rw [hN]
      exact Subgroup.card_bot
    omega
  · exact h

private theorem mem_of_smul_eq_sylow_two_P31 {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 6) (h3 : Nat.card (Sylow 2 G) = 3) (P : Sylow 2 G) {g : G}
    (hg : g • P = P) : g ∈ (P : Subgroup G) := by
  haveI := finite_sylow_two_P31 G
  have hidx : (Subgroup.normalizer (P : Set G)).index = 3 := by
    rw [← Sylow.card_eq_index_normalizer P, h3]
  have hmi := Subgroup.card_mul_index (H := Subgroup.normalizer (P : Set G))
  rw [hidx, hG] at hmi
  have hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = 2 := by omega
  have hPcard : Nat.card (P : Subgroup G) = 2 := card_sylow_two_of_card_six_P31 hG P
  have hle : (P : Subgroup G) ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer
  have heq : (P : Subgroup G) = Subgroup.normalizer (P : Set G) :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hNcard, hPcard]))
  rw [heq]
  exact Sylow.smul_eq_iff_mem_normalizer.mp hg

private theorem eq_one_of_mem_sylow_two_P31 {G : Type*} [Group G] [Finite G] {P Q : Sylow 2 G}
    (hP : Nat.card (P : Subgroup G) = 2) (hQ : Nat.card (Q : Subgroup G) = 2) (hPQ : P ≠ Q)
    {c : G} (hcP : c ∈ (P : Subgroup G)) (hcQ : c ∈ (Q : Subgroup G)) : c = 1 := by
  by_contra hc
  have hcI : c ∈ (P : Subgroup G) ⊓ (Q : Subgroup G) := ⟨hcP, hcQ⟩
  have hI1 : Nat.card ((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) ≠ 1 := by
    intro h1
    have hbot : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ h1
    rw [hbot] at hcI
    exact hc (Subgroup.mem_bot.mp hcI)
  have hdvd : Nat.card ((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) ∣ 2 := by
    have h := Subgroup.card_dvd_of_le
      (inf_le_left : (P : Subgroup G) ⊓ (Q : Subgroup G) ≤ (P : Subgroup G))
    rwa [hP] at h
  have hI2 : Nat.card ((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left hI1
  have hIP : (P : Subgroup G) ⊓ (Q : Subgroup G) = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hI2, hP]))
  have hIQ : (P : Subgroup G) ⊓ (Q : Subgroup G) = (Q : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [hI2, hQ]))
  exact hPQ (Sylow.ext (hIP.symm.trans hIQ))

private theorem exists_perm_three_injective_on_P31 {Y : Type*} [Group Y] [Finite Y]
    (C : Subgroup Y) [C.Normal] (hC : Nat.card C = 6) (h3 : Nat.card (Sylow 2 C) = 3) :
    ∃ φ : Y →* Perm (Fin 3), ∀ g ∈ C, φ g = 1 → g = 1 := by
  haveI := finite_sylow_two_P31 C
  letI : Fintype (Sylow 2 C) := Fintype.ofFinite _
  have hfin : Fintype.card (Sylow 2 C) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact h3
  let e3 : Sylow 2 C ≃ Fin 3 := Fintype.equivFinOfCardEq hfin
  let act : Y →* Perm (Sylow 2 C) :=
    (MulAction.toPermHom (MulAut C) (Sylow 2 C)).comp (MulAut.conjNormal (H := C))
  refine ⟨e3.permCongrHom.toMonoidHom.comp act, ?_⟩
  intro g hgC hφ
  let c : C := ⟨g, hgC⟩
  have e : (MulAut.conjNormal g : MulAut C) = MulAut.conj c :=
    MulAut.conjNormal_val (h := c)
  have hact1 : act g = 1 := by
    have h := hφ
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
    exact e3.permCongrHom.map_eq_one_iff.mp h
  have hfix : ∀ P : Sylow 2 C, c ∈ (P : Subgroup C) := by
    intro P
    have h2 : (MulAut.conjNormal g : MulAut C) • P = P := by
      have h := congrArg (fun σ : Perm (Sylow 2 C) => σ P) hact1
      simpa [act] using h
    have h3' : c • P = P := by
      rw [Sylow.smul_def, ← e]
      exact h2
    exact mem_of_smul_eq_sylow_two_P31 hC h3 P h3'
  obtain ⟨P₁, P₂, hne⟩ : ∃ P₁ P₂ : Sylow 2 C, P₁ ≠ P₂ := by
    haveI : Nontrivial (Sylow 2 C) := Finite.one_lt_card_iff_nontrivial.mp (by rw [h3]; norm_num)
    exact exists_pair_ne (Sylow 2 C)
  have hc1 : c = 1 :=
    eq_one_of_mem_sylow_two_P31 (card_sylow_two_of_card_six_P31 hC P₁)
      (card_sylow_two_of_card_six_P31 hC P₂) hne (hfix P₁) (hfix P₂)
  exact congrArg Subtype.val hc1

theorem nonempty_mulEquiv_perm_five_three {Y : Type*} [Group Y] [Finite Y]
    (K : Subgroup Y) [K.Normal] (e : ↥K ≃* alternatingGroup (Fin 5))
    (hcard : Nat.card Y = 720)
    (hC : Nat.card (Subgroup.centralizer (K : Set Y)) = 6)
    (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥) :
    Nonempty (Y ≃* Perm (Fin 5) × Perm (Fin 3)) := by
  classical
  have bij5 : Function.Bijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)) :
      Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5))) :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
      (by norm_num) (by norm_num)
  let ψ : MulAut (alternatingGroup (Fin 5)) ≃* Perm (Fin 5) :=
    (MulEquiv.ofBijective _ bij5).symm
  let φ₁ : Y →* Perm (Fin 5) :=
    ψ.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K)))
  have hcent : ∀ x : Y,
      MulAut.conjNormal (H := K) x = 1 ↔ x ∈ Subgroup.centralizer (K : Set Y) := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hx k hk
      have hk' : x * k * x⁻¹ = k := by
        simpa using congrArg Subtype.val (DFunLike.congr_fun hx ⟨k, hk⟩)
      exact (mul_inv_eq_iff_eq_mul.mp hk').symm
    · intro hx
      apply MulEquiv.ext
      rintro ⟨k, hk⟩
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, MulAut.one_apply]
      rw [← hx k hk, mul_inv_cancel_right]
  have hker : φ₁.ker = Subgroup.centralizer (K : Set Y) := by
    ext x
    rw [MonoidHom.mem_ker, ← hcent x]
    show ψ ((MulAut.congr e) (MulAut.conjNormal (H := K) x)) = 1 ↔ _
    rw [ψ.map_eq_one_iff, (MulAut.congr e).map_eq_one_iff]
  have hCcard : Nat.card φ₁.ker = 6 := by
    rw [hker]
    exact hC
  have h3 : Nat.card (Sylow 2 φ₁.ker) = 3 := card_sylow_two_eq_three_P31 φ₁.ker hCcard hO2
  obtain ⟨φ₂, hφ₂⟩ := exists_perm_three_injective_on_P31 φ₁.ker hCcard h3
  let φ : Y →* Perm (Fin 5) × Perm (Fin 3) := φ₁.prod φ₂
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one φ]
    intro g hg
    have h1 : φ₁ g = 1 := congrArg Prod.fst hg
    have h2 : φ₂ g = 1 := congrArg Prod.snd hg
    exact hφ₂ g (MonoidHom.mem_ker.mpr h1) h2
  have hbij : Function.Bijective φ := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [hcard, Nat.card_prod, Nat.card_perm, Nat.card_perm]
    simp [Nat.factorial]
  exact ⟨MulEquiv.ofBijective φ hbij⟩

end CFSG.Quasithin.H13.S126P31
