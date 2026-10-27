module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Red1

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

private theorem mul_pow_mem_of_pow_eq_one614 {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {q n : G} (m : ℕ) (hqm : q ^ m = 1) (hn : n ∈ N) : (q * n) ^ m ∈ N := by
  have h1 : QuotientGroup.mk' N (q * n) = QuotientGroup.mk' N q := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e : (q * n)⁻¹ * q = n⁻¹ := by group
    rw [e]
    exact N.inv_mem hn
  have h2 : QuotientGroup.mk' N ((q * n) ^ m) = 1 := by
    rw [map_pow, h1, ← map_pow, hqm, map_one]
  exact (QuotientGroup.eq_one_iff _).mp h2

section Red2a

variable {Γ : Type} [Group Γ] [Finite Γ] {K T : Subgroup Γ}

theorem isSylowTwoOf_imKT614' (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) :
    IsSylowTwoOf (imKT614 hTK T)
      ((MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range ⊔ imKT614 hTK T) := by
  have hrange : (MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range ⊔ imKT614 hTK T =
      (piKT614 hTK).range := by
    rw [← imKT614_self hTK, ← imKT614_sup hTK le_sup_left le_sup_right, imKT614,
      Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  rw [hrange]
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_⟩
  · have hT2 : IsPGroup 2 (T.subgroupOf (K ⊔ T)) :=
      hTs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTs.1).symm
    exact hT2.map _
  · set ρ := (piKT614 hTK).rangeRestrict
    have hsub : (imKT614 hTK T).subgroupOf (piKT614 hTK).range =
        (T.subgroupOf (K ⊔ T)).map ρ := by
      ext ⟨φ, hφ⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨t, ht, he⟩
        exact ⟨t, ht, Subtype.ext he⟩
      · rintro ⟨t, ht, he⟩
        exact ⟨t, ht, congrArg Subtype.val he⟩
    rw [hsub, Subgroup.index_map, MonoidHom.range_eq_top.mpr (MonoidHom.rangeRestrict_surjective _),
      Subgroup.index_top, mul_one, MonoidHom.ker_rangeRestrict]
    exact fun h => hTs.2.2 (h.trans (Subgroup.index_dvd_of_le le_sup_left))

theorem mem_of_piKT614_eq_one_of_mem614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) {X : Subgroup Γ} (hXK : X ≤ K) (hXO : X = oTwoUpper X)
    (hX5 : (X ⊓ T).relIndex X = 5) (hXn : ((X ⊓ T).subgroupOf X).Normal)
    (hXN : ¬ X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ)) {x : Γ} (hx : x ∈ X)
    (hxKT : x ∈ K ⊔ T) (h : piKT614 hTK ⟨x, hxKT⟩ = 1) : x ∈ T := by
  by_contra hxT
  have hxC : x ∈ kerAct614 hTK := (mem_kerAct614 hTK hxKT).mpr h
  have hQ5 : ((X ⊓ T).subgroupOf X).index = 5 := hX5
  have hNn : ((kerAct614 hTK).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgKT : (g : Γ) ∈ K ⊔ T := (le_sup_left : K ≤ K ⊔ T) (hXK g.2)
    have hgN := Subgroup.mem_normalizer_iff.mp (kerAct614_normal hTK hgKT) (n : Γ)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hgN.mp hn
  have hM : (X ⊓ T).subgroupOf X ⊔ (kerAct614 hTK).subgroupOf X = ⊤ := by
    have h5 := Subgroup.relIndex_mul_index
      (le_sup_left : (X ⊓ T).subgroupOf X ≤ (X ⊓ T).subgroupOf X ⊔ (kerAct614 hTK).subgroupOf X)
    rw [hQ5] at h5
    rcases Nat.prime_five.eq_one_or_self_of_dvd _ (Dvd.intro_left _ h5) with h1 | h1
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      rw [h1] at h5
      have hrel : ((X ⊓ T).subgroupOf X).relIndex
          ((X ⊓ T).subgroupOf X ⊔ (kerAct614 hTK).subgroupOf X) = 1 := by omega
      have hxN' : (⟨x, hx⟩ : ↥X) ∈ (kerAct614 hTK).subgroupOf X :=
        Subgroup.mem_subgroupOf.mpr hxC
      have hxM : (⟨x, hx⟩ : ↥X) ∈ (X ⊓ T).subgroupOf X ⊔ (kerAct614 hTK).subgroupOf X :=
        Subgroup.mem_sup_right hxN'
      have hxQ := Subgroup.relIndex_eq_one.mp hrel hxM
      exact hxT (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hxQ)).2
  have hpow : ∀ g ∈ X, ∃ k : ℕ, g ^ 2 ^ k ∈ kerAct614 hTK ⊓ X := by
    intro g hg
    have hmem : (⟨g, hg⟩ : ↥X) ∈ (X ⊓ T).subgroupOf X ⊔ (kerAct614 hTK).subgroupOf X := by
      rw [hM]
      exact Subgroup.mem_top _
    obtain ⟨q, hq, n, hn, hqn⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    have hqT : (q : Γ) ∈ T := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hq)).2
    obtain ⟨k, hk⟩ := hTs.2.1 ⟨(q : Γ), hqT⟩
    have hqk : q ^ 2 ^ k = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    have hgk := mul_pow_mem_of_pow_eq_one614 ((kerAct614 hTK).subgroupOf X) (2 ^ k) hqk hn
    rw [hqn, Subgroup.mem_subgroupOf] at hgk
    exact ⟨k, Subgroup.mem_inf.mpr ⟨by simpa using hgk, X.pow_mem hg _⟩⟩
  have hXC : X ≤ kerAct614 hTK ⊓ X := by
    have h := oTwoUpper_le_of_pow_mem hpow
    rwa [← hXO] at h
  have hXC' : ∀ y ∈ X, y ∈ kerAct614 hTK := fun y hy => (Subgroup.mem_inf.mp (hXC hy)).1
  apply hXN
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact conj_mem_inf_of_kerAct614 hTK hTs (Subgroup.mem_inf.mpr ⟨hXC' y hy, hXK hy⟩) hw
  · intro hw
    have h1 := conj_mem_inf_of_kerAct614 hTK hTs
      (Subgroup.mem_inf.mpr ⟨(kerAct614 hTK).inv_mem (hXC' y hy), K.inv_mem (hXK hy)⟩) hw
    have e : y⁻¹ * (y * w * y⁻¹) * y⁻¹⁻¹ = w := by group
    rwa [e] at h1

theorem not_le_normalizer_imKT614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) {X : Subgroup Γ} (hXK : X ≤ K)
    (hXN : ¬ X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ)) :
    ¬ imKT614 hTK X ≤ Subgroup.normalizer
      ((imKT614 hTK T ⊓ (MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range :
        Subgroup (MulAut (ModO2 K))) : Set (MulAut (ModO2 K))) := by
  intro hle
  apply hXN
  have key : ∀ x ∈ X, ∀ t ∈ T ⊓ K, x * t * x⁻¹ ∈ T ⊓ K := by
    intro x hx t ht
    obtain ⟨htT, htK⟩ := Subgroup.mem_inf.mp ht
    have hxK : x ∈ K := hXK hx
    have hxKT : x ∈ K ⊔ T := (le_sup_left : K ≤ K ⊔ T) hxK
    have htKT : t ∈ K ⊔ T := (le_sup_right : T ≤ K ⊔ T) htT
    have hgKT : x * t * x⁻¹ ∈ K ⊔ T :=
      (K ⊔ T).mul_mem ((K ⊔ T).mul_mem hxKT htKT) ((K ⊔ T).inv_mem hxKT)
    have hgK : x * t * x⁻¹ ∈ K := K.mul_mem (K.mul_mem hxK htK) (K.inv_mem hxK)
    have hπt : piKT614 hTK ⟨t, htKT⟩ ∈
        imKT614 hTK T ⊓ (MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range :=
      Subgroup.mem_inf.mpr ⟨mem_imKT614 hTK htT htKT, by
        rw [← imKT614_self hTK]
        exact mem_imKT614 hTK htK htKT⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hle (mem_imKT614 hTK hx hxKT))
      (piKT614 hTK ⟨t, htKT⟩)).mp hπt
    have hgπ : piKT614 hTK ⟨x * t * x⁻¹, hgKT⟩ = piKT614 hTK ⟨x, hxKT⟩ *
        piKT614 hTK ⟨t, htKT⟩ * (piKT614 hTK ⟨x, hxKT⟩)⁻¹ := by
      have e : (⟨x * t * x⁻¹, hgKT⟩ : ↥(K ⊔ T)) =
          ⟨x, hxKT⟩ * ⟨t, htKT⟩ * (⟨x, hxKT⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
    rw [← hgπ] at h1
    obtain ⟨s, hs, hsg⟩ := (Subgroup.mem_inf.mp (SetLike.mem_coe.mp h1)).1
    have hsT : (s : Γ) ∈ T := Subgroup.mem_subgroupOf.mp hs
    have hcKT : x * t * x⁻¹ * (s : Γ)⁻¹ ∈ K ⊔ T :=
      (K ⊔ T).mul_mem hgKT ((K ⊔ T).inv_mem s.2)
    have hcC : x * t * x⁻¹ * (s : Γ)⁻¹ ∈ kerAct614 hTK := by
      rw [mem_kerAct614 hTK hcKT]
      have e : (⟨x * t * x⁻¹ * (s : Γ)⁻¹, hcKT⟩ : ↥(K ⊔ T)) =
          ⟨x * t * x⁻¹, hgKT⟩ * s⁻¹ := rfl
      rw [e, map_mul, map_inv, hsg, mul_inv_cancel]
    obtain ⟨t₂, ht₂, z, hz, hcz⟩ := exists_mul_of_mem_kerAct614 hTK hTs hcC
    have ht₂T : t₂ ∈ T := (Subgroup.mem_inf.mp ht₂).2
    have hzC : z ∈ kerAct614 hTK := (Subgroup.mem_inf.mp hz).1
    have hzK : z ∈ K := (Subgroup.mem_inf.mp hz).2
    have ht₂KT : t₂ ∈ K ⊔ T := (le_sup_right : T ≤ K ⊔ T) ht₂T
    have hz'C : t₂ * z * t₂⁻¹ ∈ kerAct614 hTK :=
      (Subgroup.mem_normalizer_iff.mp (kerAct614_normal hTK ht₂KT) z).mp hzC
    have hz'K : t₂ * z * t₂⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hTK ht₂T) z).mp hzK
    have hg_eq : x * t * x⁻¹ = t₂ * z * (s : Γ) := by
      calc x * t * x⁻¹ = (x * t * x⁻¹ * (s : Γ)⁻¹) * (s : Γ) := by group
        _ = t₂ * z * (s : Γ) := by rw [hcz]
    have hprod : (t₂ * z * t₂⁻¹) * (t₂ * (s : Γ)) = x * t * x⁻¹ := by
      rw [hg_eq]
      group
    have ht''T : t₂ * (s : Γ) ∈ T := T.mul_mem ht₂T hsT
    have ht''K : t₂ * (s : Γ) ∈ K := by
      have e : t₂ * (s : Γ) = (t₂ * z * t₂⁻¹)⁻¹ * (x * t * x⁻¹) := by
        rw [← hprod]
        group
      rw [e]
      exact K.mul_mem (K.inv_mem hz'K) hgK
    obtain ⟨m, hm⟩ := hTs.2.1 ⟨t, htT⟩
    have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hgm : (x * t * x⁻¹) ^ 2 ^ m = 1 := by
      rw [conj_pow, htm, mul_one, mul_inv_cancel]
    rw [← hprod] at hgm
    rw [← hprod]
    exact mem_inf_of_two_elem_kerAct614 hTK hTs (Subgroup.mem_inf.mpr ⟨hz'C, hz'K⟩)
      (Subgroup.mem_inf.mpr ⟨ht''T, ht''K⟩) hgm
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key x hx h
  · intro hh
    have h2 := key x⁻¹ (X.inv_mem hx) (x * h * x⁻¹) hh
    have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
    rwa [e] at h2

theorem imKT614_ne_bot_of_two_group (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) {E : Subgroup Γ} (hE2 : IsPGroup 2 E) (hEKT : E ≤ K ⊔ T)
    (hEK : ¬ E ≤ pCoreOf 2 (K ⊔ T)) : imKT614 hTK E ≠ ⊥ := by
  intro hbot
  apply hEK
  intro e he
  have hπ : piKT614 hTK ⟨e, hEKT he⟩ = 1 := by
    have hmem : piKT614 hTK ⟨e, hEKT he⟩ ∈ imKT614 hTK E := mem_imKT614 hTK he (hEKT he)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨m, hm⟩ := hE2 ⟨e, he⟩
  exact mem_pCoreOf_of_kerAct614 hTK hTs ((mem_kerAct614 hTK (hEKT he)).mpr hπ)
    (m := m) (by simpa using congrArg Subtype.val hm)

end Red2a

end CFSG.Quasithin.H13
