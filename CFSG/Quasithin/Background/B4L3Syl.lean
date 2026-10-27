module

public import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem card_L3Γ : Nat.card L3.Γ = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_centralizer_L3 {γ : L3.Γ} (hγ : L3.IsInvol γ) :
    Nat.card (Subgroup.centralizer ({γ} : Set L3.Γ)) = 8 := by
  have h := L3.cent_card γ hγ
  rw [← h, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, L3.cent,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact eq_comm

namespace L3Data

variable [Finite V] {G : Subgroup (MulAut V)} {U Z : Subgroup V} (D : L3Data G U Z)

omit [Finite V] in
include D in
theorem card_G : Nat.card G = 168 := by
  rw [← card_L3Γ]
  exact (Nat.card_congr (Equiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩)).symm

@[expose] def centRho (γ : L3.Γ) : Subgroup (MulAut V) :=
  (Subgroup.centralizer ({γ} : Set L3.Γ)).map D.rho

omit [Finite V] in
include D in
theorem card_centRho {γ : L3.Γ} (hγ : L3.IsInvol γ) : Nat.card (D.centRho γ) = 8 := by
  unfold centRho
  rw [Subgroup.card_map_of_injective D.rho_injective]
  exact card_centralizer_L3 hγ

include D in
theorem elemAbelian_card_le_four {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hAel : IsElemAbelian2 A) :
    Nat.card A ≤ 4 := by
  by_cases hA : A = ⊥
  · rw [hA, Subgroup.card_bot]
    norm_num
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA
  have ha1' : (a : MulAut V) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haG : (a : MulAut V) ∈ G := hAG a.2
  have ha2 : (a : MulAut V) ^ 2 = 1 := hAel.2 _ a.2
  obtain ⟨γ, hγ, hγa⟩ := D.exists_invol haG ha2 ha1'
  have hcardC := D.card_centRho hγ
  have hAC : A ≤ D.centRho γ := by
    intro x hx
    obtain ⟨δ, hδ⟩ := D.exists_rho (hAG hx)
    refine ⟨δ, ?_, hδ⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply D.rho_injective
    rw [map_mul, map_mul, hγa, hδ]
    exact hAel.1 _ a.2 _ hx
  have hne : A ≠ D.centRho γ := by
    intro h
    obtain ⟨x, hx, y, hy, hxy⟩ := L3.cent_nonabelian γ hγ
    have hxC : D.rho x ∈ D.centRho γ := ⟨x, by
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff] at hk
      subst hk
      simpa [L3.cent, eq_comm] using hx, rfl⟩
    have hyC : D.rho y ∈ D.centRho γ := ⟨y, by
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff] at hk
      subst hk
      simpa [L3.cent, eq_comm] using hy, rfl⟩
    rw [← h] at hxC hyC
    apply hxy
    apply D.rho_injective
    rw [map_mul, map_mul]
    exact hAel.1 _ hxC _ hyC
  have hdvd : Nat.card A ∣ Nat.card (D.centRho γ) := Subgroup.card_dvd_of_le hAC
  have hne8 : Nat.card A ≠ 8 := fun h8 =>
    hne (Subgroup.eq_of_le_of_card_ge hAC (by omega))
  rw [hcardC] at hdvd
  have hle : Nat.card A ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card A := Nat.card_pos
  have : Nat.card A ∈ ({1, 2, 4, 8} : Finset ℕ) := by
    interval_cases h : Nat.card A <;> simp_all
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

include D in
theorem card_sylow {T : Subgroup (MulAut V)} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G) :
    Nat.card T = 8 := by
  obtain ⟨hTG, hT2, hTidx⟩ := hT
  have hG := D.card_G
  have h1 : Nat.card (T.subgroupOf G) * (T.subgroupOf G).index = Nat.card G :=
    Subgroup.card_mul_index _
  have h2 : Nat.card (T.subgroupOf G) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTG).toEquiv
  rw [h2, hG] at h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hT2
  rw [hk] at h1
  have hodd : (T.subgroupOf G).index % 2 = 1 := by omega
  have hk7 : k ≤ 7 := by
    by_contra h
    push Not at h
    have h3 : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    have h4 : 0 < (T.subgroupOf G).index := by
      rcases Nat.eq_zero_or_pos (T.subgroupOf G).index with h0 | h0
      · rw [h0] at h1; omega
      · exact h0
    nlinarith
  rw [hk]
  interval_cases k <;> simp at h1 ⊢ <;> omega

include D in
theorem exists_two_centers_in_sylow {T : Subgroup (MulAut V)}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G) :
    ∃ γ δ : L3.Γ, L3.IsInvol γ ∧ L3.IsInvol δ ∧ D.rho γ ∈ T ∧ D.rho δ ∈ T ∧
      L3.cim γ ≠ L3.cim δ := by
  have hT8 := D.card_sylow hT
  obtain ⟨hTG, hT2, -⟩ := hT
  have hnt : Nontrivial T := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  have := hT2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center ↥T) := hT2.to_subgroup _
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).mp hZ2
  have hZgt : 1 < Nat.card (Subgroup.center ↥T) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    omega
  have hdvd : 2 ∣ Nat.card (Subgroup.center ↥T) := by
    rw [hj]
    exact dvd_pow_self 2 hj0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥T)) 2 hdvd
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  set zT : ↥T := (z : ↥T) with hzT
  have hzG : (zT : MulAut V) ∈ G := hTG zT.2
  have hzsq : (zT : MulAut V) ^ 2 = 1 := by
    have := congrArg (fun x : ↥(Subgroup.center ↥T) => ((x : ↥T) : MulAut V)) hz2
    simpa using this
  have hz1' : (zT : MulAut V) ≠ 1 := by
    intro h
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  obtain ⟨ζ, hζ, hζz⟩ := D.exists_invol hzG hzsq hz1'
  have hTC : T ≤ D.centRho ζ := by
    intro t ht
    obtain ⟨τ, hτ⟩ := D.exists_rho (hTG ht)
    refine ⟨τ, ?_, hτ⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply D.rho_injective
    rw [map_mul, map_mul, hζz, hτ]
    have := Subgroup.mem_center_iff.mp z.2 ⟨t, ht⟩
    have h' := congrArg (fun x : ↥T => (x : MulAut V)) this
    simpa using h'.symm
  have hTeq : T = D.centRho ζ :=
    Subgroup.eq_of_le_of_card_ge hTC (by rw [D.card_centRho hζ]; omega)
  obtain ⟨a, ha, b, hb, hia, hib, hab⟩ := L3.cent_two_centers ζ hζ
  refine ⟨a, b, hia, hib, ?_, ?_, hab⟩
  · rw [hTeq]
    refine ⟨a, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    simpa [L3.cent, eq_comm] using ha
  · rw [hTeq]
    refine ⟨b, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    simpa [L3.cent, eq_comm] using hb

end L3Data

end CFSG.Quasithin
