module

public import CFSG.Quasithin.Background.SmithC27RLieCentral
public import CFSG.Quasithin.Background.SmithC27Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3A6Orbits

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv

theorem card_eq_eight_of_isSylowTwoOf_alt6 {S : Subgroup ↥(alternatingGroup (Fin 6))}
    (hS : IsSylowTwoOf S ⊤) : Nat.card S = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hS.2.1)
  have hodd : ¬ 2 ∣ S.index := by
    have h := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h
  have hmul := Subgroup.card_mul_index S
  rw [CFSG.QuasithinUnique.Setup.X3.card_alt6, hk] at hmul
  have hk9 : k < 9 := by
    by_contra hk9
    have h1 : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ k ≤ 360 := Nat.le_of_dvd (by norm_num) ⟨_, hmul.symm⟩
    omega
  rw [hk]
  interval_cases k <;> omega

theorem card_eq_of_sylow_le_alt6 {S M : Subgroup ↥(alternatingGroup (Fin 6))}
    (hS : IsSylowTwoOf S ⊤) (hSM : S ≤ M) :
    Nat.card M = 8 ∨ Nat.card M = 24 ∨ Nat.card M = 360 := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    CFSG.QuasithinUnique.Setup.X3.isSimpleGroup_alt6
  have h8 : 8 ∣ Nat.card M := card_eq_eight_of_isSylowTwoOf_alt6 hS ▸ Subgroup.card_dvd_of_le hSM
  have hmul := Subgroup.card_mul_index M
  rw [CFSG.QuasithinUnique.Setup.X3.card_alt6] at hmul
  have hpos : 0 < M.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle : M.index ≤ 45 := by
    obtain ⟨c, hc⟩ := h8
    rw [hc] at hmul
    have : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h] at hmul; omega
      · exact h
    nlinarith
  have hsmall : M.index ≠ 3 ∧ M.index ≠ 5 := by
    refine ⟨fun h3 => ?_, fun h5 => ?_⟩
    · have htop := eq_top_of_not_dvd_factorial_index M (by
        rw [h3, CFSG.QuasithinUnique.Setup.X3.card_alt6]; decide)
      rw [htop, Subgroup.index_top] at h3
      omega
    · have htop := eq_top_of_not_dvd_factorial_index M (by
        rw [h5, CFSG.QuasithinUnique.Setup.X3.card_alt6]; decide)
      rw [htop, Subgroup.index_top] at h5
      omega
  have h9 : M.index ≠ 9 := by
    intro h9
    rw [h9] at hmul
    exact CFSG.QuasithinUnique.Setup.X3.no_subgroup_order (K := M) (Or.inr (Or.inl (by omega)))
  obtain ⟨h3, h5⟩ := hsmall
  interval_cases hi : M.index <;> omega

theorem maxParabolicMaximal_alt6 :
    MaxParabolicMaximal (⊤ : Subgroup ↥(alternatingGroup (Fin 6))) := by
  refine maxParabolicMaximal_top_of_forall_sylow fun U hU M hNM hMt => ?_
  have hUM : U ≤ M := Subgroup.le_normalizer.trans hNM
  have hU8 := card_eq_eight_of_isSylowTwoOf_alt6 hU
  rcases card_eq_of_sylow_le_alt6 hU hUM with h | h | h
  · left
    have hUeq : U = M := Subgroup.eq_of_le_of_card_ge hUM (by rw [h, hU8])
    exact le_antisymm (hUeq ▸ Subgroup.le_normalizer) hNM
  · right
    refine ⟨hMt, fun Y hMY => ?_⟩
    have hY := card_eq_of_sylow_le_alt6 hU (hUM.trans hMY.le)
    have hlt := Subgroup.card_lt_of_lt hMY
    refine Subgroup.eq_top_of_card_eq Y ?_
    rw [CFSG.QuasithinUnique.Setup.X3.card_alt6]
    omega
  · exact absurd (Subgroup.eq_top_of_card_eq M (by rw [h, CFSG.QuasithinUnique.Setup.X3.card_alt6]))
      hMt

@[expose] def alt6Inv : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def alt6InvA : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 2 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def alt6InvB : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 1 * swap 4 5, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def alt6InvC : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 3 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def alt6InvD : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 2 3 * swap 4 5, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem card_filter_commute_alt6Inv :
    (Finset.univ.filter fun g : ↥(alternatingGroup (Fin 6)) => g * alt6Inv = alt6Inv * g).card =
      8 := by
  decide +kernel

theorem eq_one_or_eq_alt6Inv_of_commute : ∀ c : ↥(alternatingGroup (Fin 6)),
    c * alt6Inv = alt6Inv * c → c * alt6InvA = alt6InvA * c → c * alt6InvB = alt6InvB * c →
      c = 1 ∨ c = alt6Inv := by
  decide +kernel

theorem involutions_of_commute_alt6Inv : ∀ g : ↥(alternatingGroup (Fin 6)),
    g * alt6Inv = alt6Inv * g → g * g = 1 →
      g = 1 ∨ g = alt6Inv ∨ g = alt6InvA ∨ g = alt6InvB ∨ g = alt6InvC ∨ g = alt6InvD := by
  decide +kernel

theorem exists_conj_alt6Inv_eq {s : ↥(alternatingGroup (Fin 6))}
    (hs : s = alt6InvA ∨ s = alt6InvB ∨ s = alt6InvC ∨ s = alt6InvD) :
    ∃ k : ↥(alternatingGroup (Fin 6)), k * alt6Inv * k⁻¹ = s := by
  rcases hs with rfl | rfl | rfl | rfl
  · exact ⟨⟨swap 1 2 * swap 4 5, by rw [Perm.mem_alternatingGroup]; decide⟩, by decide⟩
  · exact ⟨⟨swap 2 4 * swap 3 5, by rw [Perm.mem_alternatingGroup]; decide⟩, by decide⟩
  · exact ⟨⟨swap 1 3 * swap 4 5, by rw [Perm.mem_alternatingGroup]; decide⟩, by decide⟩
  · exact ⟨⟨swap 0 4 * swap 1 5, by rw [Perm.mem_alternatingGroup]; decide⟩, by decide⟩

@[expose] def alt6Syl : Subgroup ↥(alternatingGroup (Fin 6)) :=
  Subgroup.centralizer {alt6Inv}

theorem mem_alt6Syl {g : ↥(alternatingGroup (Fin 6))} : g ∈ alt6Syl ↔ g * alt6Inv = alt6Inv * g :=
  Subgroup.mem_centralizer_singleton_iff

theorem card_alt6Syl : Nat.card alt6Syl = 8 := by
  rw [← card_filter_commute_alt6Inv, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_alt6Syl)

theorem isSylowTwoOf_alt6Syl : IsSylowTwoOf alt6Syl ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [card_alt6Syl]; norm_num), ?_⟩
  rw [show (alt6Syl.subgroupOf ⊤).index = alt6Syl.index from Subgroup.relIndex_top_right _]
  have h := Subgroup.card_mul_index alt6Syl
  rw [card_alt6Syl, CFSG.QuasithinUnique.Setup.X3.card_alt6] at h
  omega

theorem normalizer_alt6Syl : Subgroup.normalizer (alt6Syl : Set ↥(alternatingGroup (Fin 6))) =
    alt6Syl := by
  refine le_antisymm (fun x hx => ?_) Subgroup.le_normalizer
  have hc : ∀ s ∈ alt6Syl, x * alt6Inv * x⁻¹ * s = s * (x * alt6Inv * x⁻¹) := by
    intro s hs
    have h1 : x⁻¹ * s * x ∈ alt6Syl := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) s).mp hs
      simpa using this
    rw [mem_alt6Syl] at h1
    calc x * alt6Inv * x⁻¹ * s = x * (alt6Inv * (x⁻¹ * s * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * s * x) * alt6Inv) * x⁻¹ := by rw [h1]
      _ = s * (x * alt6Inv * x⁻¹) := by group
  have hz : alt6Inv ∈ alt6Syl := mem_alt6Syl.mpr rfl
  have hA : alt6InvA ∈ alt6Syl := mem_alt6Syl.mpr (by decide)
  have hB : alt6InvB ∈ alt6Syl := mem_alt6Syl.mpr (by decide)
  rcases eq_one_or_eq_alt6Inv_of_commute _ (hc _ hz) (hc _ hA) (hc _ hB) with h | h
  · exfalso
    have h1 : alt6Inv = 1 := by
      have := congrArg (fun y => x⁻¹ * y * x) h
      simpa [mul_assoc] using this
    exact absurd h1 (by decide)
  · rw [mem_alt6Syl]
    calc x * alt6Inv = (x * alt6Inv * x⁻¹) * x := by group
      _ = alt6Inv * x := by rw [h]

theorem centralizer_conj_eq_map {G : Type*} [Group G] (h z : G) :
    Subgroup.centralizer {h * z * h⁻¹} =
      (Subgroup.centralizer {z}).map (MulAut.conj h).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
  constructor
  · intro hg
    calc h⁻¹ * g * h * z = h⁻¹ * (g * (h * z * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * z * h⁻¹) * g) * h := by rw [hg]
      _ = z * (h⁻¹ * g * h) := by group
  · intro hg
    calc g * (h * z * h⁻¹) = h * ((h⁻¹ * g * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * g * h)) * h⁻¹ := by rw [hg]
      _ = h * z * h⁻¹ * g := by group

theorem normalizer_eq_of_isSylowTwoOf_alt6 {S : Subgroup ↥(alternatingGroup (Fin 6))}
    (hS : IsSylowTwoOf S ⊤) :
    Subgroup.normalizer (S : Set ↥(alternatingGroup (Fin 6))) = S := by
  obtain ⟨g, rfl⟩ := exists_map_conj_eq_of_sylow isSylowTwoOf_alt6Syl hS
  rw [← Subgroup.map_equiv_normalizer_eq, normalizer_alt6Syl]

theorem exists_conj_eq_of_involution_alt6 {t : ↥(alternatingGroup (Fin 6))} (ht : t * t = 1)
    (ht1 : t ≠ 1) : ∃ k : ↥(alternatingGroup (Fin 6)), k * alt6Inv * k⁻¹ = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (Subgroup.zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact ht) ht1, pow_one])
  obtain ⟨P, hP⟩ := h2.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_sylow isSylowTwoOf_alt6Syl (sylow_two_isSylowTwoOf_top P)
  have htP : t ∈ (P : Subgroup ↥(alternatingGroup (Fin 6))) := hP (Subgroup.mem_zpowers t)
  rw [← hg, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_alt6Syl] at htP
  have hs2 : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht]; group
  have hback : ∀ k, k * alt6Inv * k⁻¹ = g⁻¹ * t * g → (g * k) * alt6Inv * (g * k)⁻¹ = t := by
    intro k hk
    calc (g * k) * alt6Inv * (g * k)⁻¹ = g * (k * alt6Inv * k⁻¹) * g⁻¹ := by group
      _ = t := by rw [hk]; group
  rcases involutions_of_commute_alt6Inv _ htP hs2 with h | h | h
  · exfalso
    apply ht1
    have := congrArg (fun y => g * y * g⁻¹) h
    simpa [mul_assoc] using this
  · exact ⟨g, hback 1 (by rw [h]; group)⟩
  · obtain ⟨k, hk⟩ := exists_conj_alt6Inv_eq h
    exact ⟨g * k, hback k hk⟩

theorem centralizer_involution_alt6 {t : ↥(alternatingGroup (Fin 6))} (ht : t * t = 1)
    (ht1 : t ≠ 1) :
    IsSylowTwoOf (Subgroup.centralizer {t}) ⊤ ∧
      Subgroup.normalizer (Subgroup.centralizer {t} : Set ↥(alternatingGroup (Fin 6))) =
        Subgroup.centralizer {t} := by
  obtain ⟨k, rfl⟩ := exists_conj_eq_of_involution_alt6 ht ht1
  rw [centralizer_conj_eq_map]
  have hS : IsSylowTwoOf ((Subgroup.centralizer {alt6Inv}).map (MulAut.conj k).toMonoidHom) ⊤ :=
    isSylowTwoOf_map_top_of_surjective (MulAut.conj k).surjective isSylowTwoOf_alt6Syl
  exact ⟨hS, normalizer_eq_of_isSylowTwoOf_alt6 hS⟩

theorem centralizer_le_normalizer_zpowers {G : Type*} [Group G] (t : G) :
    Subgroup.centralizer {t} ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hconj : ∀ n : ℤ, g * t ^ n * g⁻¹ = t ^ n := by
    intro n
    rw [← conj_zpow]
    congr 1
    calc g * t * g⁻¹ = t * g * g⁻¹ := by rw [← hg]
      _ = t := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp only [hconj]⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h1 : g * x * g⁻¹ = t ^ n := hn.symm
    calc t ^ n = g⁻¹ * (g * t ^ n * g⁻¹) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hconj, h1]
      _ = x := by group

theorem exists_sylow_normalizer_le_alt6 {U : Subgroup ↥(alternatingGroup (Fin 6))}
    (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U) :
    ∃ S : Subgroup ↥(alternatingGroup (Fin 6)), IsSylowTwoOf S ⊤ ∧
      Subgroup.normalizer (S : Set ↥(alternatingGroup (Fin 6))) ≤
        Subgroup.normalizer (U : Set ↥(alternatingGroup (Fin 6))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hU2.exists_le_sylow
  have hS := sylow_two_isSylowTwoOf_top P
  have hS8 := card_eq_eight_of_isSylowTwoOf_alt6 hS
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU2
  have hdvd : 2 ^ k ∣ 2 ^ 3 := by
    rw [← hk, show (2 : ℕ) ^ 3 = 8 by norm_num, ← hS8]
    exact Subgroup.card_dvd_of_le hP
  have hk3 : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hU1 (Subgroup.eq_bot_of_card_eq U (by rw [hk, pow_zero]))
  by_cases hk1 : k = 1
  ·
    subst hk1
    obtain ⟨⟨t, htU⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU1
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    have hord : orderOf t ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard U htU
      rwa [hk, pow_one] at this
    have ht2 : t * t = 1 := by
      rw [← sq]
      exact orderOf_dvd_iff_pow_eq_one.mp hord
    have hUz : Subgroup.zpowers t = U := by
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr htU) ?_
      rw [Nat.card_zpowers, hk, pow_one, orderOf_eq_prime (by rw [sq]; exact ht2) ht1']
    obtain ⟨hC, hNC⟩ := centralizer_involution_alt6 ht2 ht1'
    refine ⟨Subgroup.centralizer {t}, hC, ?_⟩
    rw [hNC, ← hUz]
    exact centralizer_le_normalizer_zpowers t
  ·
    refine ⟨P, hS, ?_⟩
    rw [normalizer_eq_of_isSylowTwoOf_alt6 hS]
    have hrel := Subgroup.relIndex_mul_index hP
    have hU := Subgroup.card_mul_index U
    have hSi := Subgroup.card_mul_index (P : Subgroup ↥(alternatingGroup (Fin 6)))
    rw [CFSG.QuasithinUnique.Setup.X3.card_alt6] at hU hSi
    rw [hS8] at hSi
    rw [hk] at hU
    have hPi : (P : Subgroup ↥(alternatingGroup (Fin 6))).index = 45 := by omega
    rw [hPi] at hrel
    have hk23 : k = 2 ∨ k = 3 := by omega
    rcases hk23 with rfl | rfl
    · norm_num at hU
      have h2 : U.relIndex P = 2 := by omega
      have hn : (U.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two h2
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hP).mp hn
    · norm_num at hU
      have h1 : U.relIndex P = 1 := by omega
      have hPU : (P : Subgroup ↥(alternatingGroup (Fin 6))) ≤ U := Subgroup.relIndex_eq_one.mp h1
      rw [le_antisymm hP hPU]
      exact Subgroup.le_normalizer

theorem isRadicalParabolic_alt6 :
    IsRadicalParabolic (⊤ : Subgroup ↥(alternatingGroup (Fin 6))) := by
  intro U _ hU1 hU2 _
  obtain ⟨S, hS, hSU⟩ := exists_sylow_normalizer_le_alt6 hU1 hU2
  refine ⟨le_top, S, hS, ?_⟩
  rw [top_inf_eq, top_inf_eq]
  exact hSU

noncomputable def topMulEquivOfMulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    ↥(⊤ : Subgroup A) ≃* ↥(⊤ : Subgroup B) :=
  Subgroup.topEquiv.trans (e.trans Subgroup.topEquiv.symm)

theorem isRadicalParabolic_of_isHat_alt6 {Γ : Type} [Group Γ] [Finite Γ]
    (h : IsHat Γ ↥(alternatingGroup (Fin 6))) : IsRadicalParabolic (⊤ : Subgroup Γ) := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  refine isRadicalParabolic_top_of_quotient (Subgroup.center Γ) le_rfl (by rw [h3]; decide) ?_
  exact (isRadicalParabolic_congr (topMulEquivOfMulEquiv e)).mpr isRadicalParabolic_alt6

theorem maxParabolicMaximal_of_isHat_alt6 {Γ : Type} [Group Γ] [Finite Γ]
    (h : IsHat Γ ↥(alternatingGroup (Fin 6))) : MaxParabolicMaximal (⊤ : Subgroup Γ) := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  refine maxParabolicMaximal_top_of_quotient (Subgroup.center Γ) le_rfl (by rw [h3]; decide) ?_
  exact (maxParabolicMaximal_congr (topMulEquivOfMulEquiv e)).mpr maxParabolicMaximal_alt6

end CFSG.Quasithin.SmithC27
