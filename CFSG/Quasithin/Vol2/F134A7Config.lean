module

public import CFSG.Quasithin.Vol2.F134A7
public import CFSG.Walter.W67.W2Cor32A

public section

namespace CFSG.Quasithin.F134

open CFSG.Quasithin.P134 CFSG.QuasithinUnique

section Abstract

variable {G : Type} [Group G] [Finite G]

theorem le_of_card_three {H P N : Subgroup G} (hH : Nat.card H = 72) (hPH : P ≤ H)
    (hP : Nat.card P = 9) (hNH : N ≤ H) (hN : Nat.card N = 3)
    (hnorm : ∀ x ∈ H, ∀ n ∈ N, x * n * x⁻¹ ∈ N) : N ≤ P := by
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hnorm p (hPH hp) n
    · intro hn
      have := hnorm p⁻¹ (H.inv_mem (hPH hp)) _ hn
      rwa [show p⁻¹ * (p * n * p⁻¹) * p⁻¹⁻¹ = n by group] at this
  have hprod := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hPN
  rw [hN, hP] at hprod
  have hsup : Nat.card (N ⊔ P : Subgroup G) ∣ 72 := hH ▸ Subgroup.card_dvd_of_le (sup_le hNH hPH)
  have hinf : Nat.card (N ⊓ P : Subgroup G) ∣ 3 := hN ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).1 hinf with h1 | h3
  · rw [h1, mul_one] at hprod
    rw [hprod] at hsup
    norm_num at hsup
  · have := Subgroup.eq_of_le_of_card_ge (inf_le_left : N ⊓ P ≤ N) (by rw [h3, hN])
    rw [← this]
    exact inf_le_right

theorem sup_eq_of_card_three {P N₁ N₂ : Subgroup G} (hP : Nat.card P = 9) (h₁ : N₁ ≤ P)
    (h₂ : N₂ ≤ P) (hc₁ : Nat.card N₁ = 3) (hc₂ : Nat.card N₂ = 3) (hne : N₁ ≠ N₂) :
    N₁ ⊔ N₂ = P := by
  have hle : N₁ ⊔ N₂ ≤ P := sup_le h₁ h₂
  have hdvd : Nat.card (N₁ ⊔ N₂ : Subgroup G) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hP]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have h3 : 3 ≤ Nat.card (N₁ ⊔ N₂ : Subgroup G) := hc₁ ▸ Subgroup.card_le_of_le le_sup_left
  interval_cases k
  · rw [hk'] at h3
    norm_num at h3
  · have e₁ := Subgroup.eq_of_le_of_card_ge (le_sup_left : N₁ ≤ N₁ ⊔ N₂) (by rw [hk', hc₁]; rfl)
    have e₂ := Subgroup.eq_of_le_of_card_ge (le_sup_right : N₂ ≤ N₁ ⊔ N₂) (by rw [hk', hc₂]; rfl)
    exact absurd (e₁.trans e₂.symm) hne
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hk', hP]; rfl)

end Abstract

theorem false_of_normal_three {A : Type} [Group A] [Finite A] {L P T : Subgroup A}
    (h : E9Config L P T) (hcard : Nat.card (P ⊔ (T ⊓ L) : Subgroup A) = 72)
    (N : Subgroup A) (hNH : N ≤ P ⊔ (T ⊓ L)) (hN3 : Nat.card N = 3)
    (hNnorm : ∀ x ∈ P ⊔ (T ⊓ L), ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hP : ∃ x ∈ P ⊔ (T ⊓ L), ∃ p ∈ P, x * p * x⁻¹ ∉ P) : False := by
  set H := P ⊔ (T ⊓ L) with hHdef
  have hPH : P ≤ H := le_sup_left
  have hNP : N ≤ P := le_of_card_three hcard hPH h.card hNH hN3 hNnorm
  have hL := h.normal
  have htH : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ x ∈ H, t * x * t⁻¹ ∈ H := by
    intro t ht
    refine conj_mem_sup (fun p hp => Subgroup.mem_sup_left ?_)
      (fun s hs => Subgroup.mem_sup_right ?_)
    · exact (Subgroup.mem_normalizer_iff.mp ht.2 p).1 hp
    · exact ⟨T.mul_mem (T.mul_mem ht.1 hs.1) (T.inv_mem ht.1), hL.conj_mem s hs.2 t⟩
  have hinv : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A),
      t⁻¹ ∈ T ⊓ Subgroup.normalizer (P : Set A) :=
    fun t ht => (T ⊓ Subgroup.normalizer (P : Set A)).inv_mem ht
  have hnormN : T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (N : Set A) := by
    intro t ht
    set Nt := N.map (MulAut.conj t).toMonoidHom
    have hNt3 : Nat.card Nt = 3 := by
      rw [← hN3]
      exact (Nat.card_congr (N.equivMapOfInjective _ (MulAut.conj t).injective).toEquiv).symm
    have hNtH : Nt ≤ H := by
      rintro _ ⟨n, hn, rfl⟩
      exact htH t ht n (hNH hn)
    have hNtnorm : ∀ x ∈ H, ∀ n ∈ Nt, x * n * x⁻¹ ∈ Nt := by
      rintro x hx _ ⟨n, hn, rfl⟩
      have hx' : t⁻¹ * x * t⁻¹⁻¹ ∈ H := htH t⁻¹ (hinv t ht) x hx
      refine ⟨t⁻¹ * x * t⁻¹⁻¹ * n * (t⁻¹ * x * t⁻¹⁻¹)⁻¹, hNnorm _ hx' n hn, ?_⟩
      change t * (t⁻¹ * x * t⁻¹⁻¹ * n * (t⁻¹ * x * t⁻¹⁻¹)⁻¹) * t⁻¹ = x * (t * n * t⁻¹) * x⁻¹
      group
    have hNtP : Nt ≤ P := le_of_card_three hcard hPH h.card hNtH hNt3 hNtnorm
    have hNt : Nt = N := by
      by_contra hne
      have hsup := sup_eq_of_card_three h.card hNP hNtP hN3 hNt3 (Ne.symm hne)
      obtain ⟨x, hx, p, hp, hxp⟩ := hP
      refine hxp ?_
      rw [← hsup] at hp ⊢
      exact conj_mem_sup (fun n hn => Subgroup.mem_sup_left (hNnorm x hx n hn))
        (fun n hn => Subgroup.mem_sup_right (hNtnorm x hx n hn)) p hp
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [← hNt]
      exact ⟨n, hn, rfl⟩
    · intro hn
      rw [← hNt] at hn
      obtain ⟨m, hm, hmn⟩ := hn
      have : m = n := by
        have hmn' : t * m * t⁻¹ = t * n * t⁻¹ := hmn
        simpa using hmn'
      rwa [← this]
  rcases h.irred N hNP hnormN with hbot | htop
  · rw [hbot, Subgroup.card_bot] at hN3
    omega
  · rw [htop, h.card] at hN3
    omega

theorem card_alternating_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem isSylow_three_of_card_nine {Q : Subgroup (alternatingGroup (Fin 7))}
    (hQ : Nat.card Q = 9) : IsPGroup 3 Q ∧ ¬ 3 ∣ Q.index := by
  refine ⟨IsPGroup.of_card (n := 2) (by rw [hQ]; norm_num), ?_⟩
  have h := Q.card_mul_index
  rw [hQ, card_alternating_seven] at h
  omega

theorem mem_map_subgroupOf_iff {A G : Type*} [Group A] [Group G] {L K : Subgroup A}
    (ψ : ↥L ≃* G) (m : ↥L) : ψ m ∈ (K.subgroupOf L).map ψ.toMonoidHom ↔ (m : A) ∈ K := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]

theorem noE9Config_alt7 :
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin 7)) := by
  intro A _ _ L P T ⟨e⟩ hcfg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := P ⊔ (T ⊓ L) with hHdef
  have hHL : H ≤ L := E9Config.sup_inf_le hcfg
  have hPH : P ≤ H := le_sup_left
  have hS := E9Config.isSylowTwoOf_inf hcfg
  have hL : Nat.card L = 2520 := (Nat.card_congr e.toEquiv).trans card_alternating_seven
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.2.1
  have hidx := ((T ⊓ L).subgroupOf L).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hk, hL] at hidx
  have hk3 : k = 3 := by
    have hodd := hS.2.2
    have hle : k ≤ 3 := by
      by_contra hlt
      have : 2 ^ 4 ∣ 2520 := (Nat.pow_dvd_pow 2 (by omega)).trans (Dvd.intro _ hidx)
      norm_num at this
    interval_cases k <;> omega
  have hcard : Nat.card H = 72 := by
    rw [E9Config.card_sup_inf hcfg, hk, hk3]
    norm_num
  have hP' : Nat.card ((P.subgroupOf L).map e.toMonoidHom) = 9 := by
    rw [← Nat.card_congr ((P.subgroupOf L).equivMapOfInjective _ e.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, hcfg.card]
  obtain ⟨hP'p, hP'i⟩ := isSylow_three_of_card_nine hP'
  obtain ⟨hP₀p, hP₀i⟩ := isSylow_three_of_card_nine card_a7P₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (hP'p.toSylow hP'i)
    (hP₀p.toSylow hP₀i)
  let ψ : ↥L ≃* alternatingGroup (Fin 7) := e.trans (MulAut.conj g)
  have hψP : (P.subgroupOf L).map ψ.toMonoidHom = a7P₀ := by
    have hg' := congrArg (fun Q : Sylow 3 (alternatingGroup (Fin 7)) =>
      (Q : Subgroup (alternatingGroup (Fin 7)))) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow, Subgroup.pointwise_smul_def] at hg'
    have key : ((P.subgroupOf L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (P.subgroupOf L).map ψ.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [← key]
    exact hg'
  set H'' := (H.subgroupOf L).map ψ.toMonoidHom with hH''def
  have hH'' : Nat.card H'' = 72 := by
    rw [← Nat.card_congr ((H.subgroupOf L).equivMapOfInjective _ ψ.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv, hcard]
  have hP₀H : a7P₀ ≤ H'' := by
    rw [← hψP]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L hPH)
  obtain ⟨⟨N'', hN''H, hN''3, hN''norm⟩, x'', hx'', p'', hp'', hnot⟩ :=
    a7_key H'' (hP₀H (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
      (hP₀H (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))) hH''
  refine false_of_normal_three hcfg hcard ((N''.comap ψ.toMonoidHom).map L.subtype) ?_ ?_ ?_ ?_
  · rintro _ ⟨m, hm, rfl⟩
    exact (mem_map_subgroupOf_iff ψ m).1 (hN''H hm)
  · rw [← Nat.card_congr ((N''.comap ψ.toMonoidHom).equivMapOfInjective _
      L.subtype_injective).toEquiv, ← hN''3,
      Nat.card_congr ((N''.comap ψ.toMonoidHom).equivMapOfInjective ψ.toMonoidHom
        ψ.injective).toEquiv,
      Subgroup.map_comap_eq_self_of_surjective ψ.surjective]
  · rintro x hx _ ⟨m, hm, rfl⟩
    set x' : ↥L := ⟨x, hHL hx⟩
    have hx' : ψ x' ∈ H'' := (mem_map_subgroupOf_iff ψ x').2 hx
    refine ⟨x' * m * x'⁻¹, ?_, rfl⟩
    show ψ (x' * m * x'⁻¹) ∈ N''
    rw [map_mul, map_mul, map_inv]
    exact hN''norm _ hx' _ hm
  · obtain ⟨x', hx'⟩ : ∃ x' : ↥L, ψ x' = x'' := ⟨ψ.symm x'', ψ.apply_symm_apply x''⟩
    obtain ⟨p', hp'⟩ : ∃ p' : ↥L, ψ p' = p'' := ⟨ψ.symm p'', ψ.apply_symm_apply p''⟩
    have hxH : (x' : A) ∈ H := (mem_map_subgroupOf_iff ψ x').1 (hx' ▸ hx'')
    have hpP : (p' : A) ∈ P := (mem_map_subgroupOf_iff ψ p').1 (hψP ▸ hp' ▸ hp'')
    refine ⟨x', hxH, p', hpP, fun hmem => hnot ?_⟩
    rw [← hψP, ← hx', ← hp', ← map_inv, ← map_mul, ← map_mul]
    exact (mem_map_subgroupOf_iff ψ (x' * p' * x'⁻¹)).2 hmem

end CFSG.Quasithin.F134
