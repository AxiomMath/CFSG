module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationElevenLab

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

@[expose] def CE : Subgroup G := Subgroup.centralizer (E.E₀ : Set G)

theorem mem_CE {g : G} : g ∈ E.CE ↔ ∀ x ∈ E.E₀, x * g = g * x := Subgroup.mem_centralizer_iff

theorem E₀_comm {x y : G} (hx : x ∈ E.E₀) (hy : y ∈ E.E₀) : x * y = y * x := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  rw [← map_mul, ← map_mul, E0h_comm u hu v hv]

theorem E₀_le_CE : E.E₀ ≤ E.CE := fun _ hy => E.mem_CE.2 fun _ hx => E.E₀_comm hx hy

theorem card_E₀ : Nat.card E.E₀ = 4 := by
  rw [E₀, Subgroup.card_map_of_injective E.injective, card_E0h]

theorem t_mem_E₀ : E.t ∈ E.E₀ := ⟨t0, t0_mem_E0h, rfl⟩

theorem e₁_mem_E₀ : E.e₁ ∈ E.E₀ := ⟨e1, e1_mem_E0h, rfl⟩

theorem CE_le_Gt : E.CE ≤ Subgroup.centralizer ({E.t} : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact E.mem_CE.1 hg E.t E.t_mem_E₀

theorem isConj_t_e₁ : IsConj E.t E.e₁ := by
  obtain ⟨m, hm⟩ := e1_conj_t0
  exact E.isConj_ι hm

theorem isConj_t_e₁t : IsConj E.t (E.e₁ * E.t) := by
  obtain ⟨m, hm⟩ := e1t0_conj_t0
  have := E.isConj_ι hm
  rwa [map_mul] at this

theorem not_isConj_t_z [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) :
    ¬ IsConj E.t E.z := by
  intro h
  rw [isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  exact E.t_not_conj_z hT hM ⟨c, by rw [← hc]; group⟩

theorem card_le_32_aux [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPC : P ≤ E.CE) (hEP : E.E₀ ≤ P) :
    Nat.card P ≤ 32 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJle, hJp, hJidx⟩ := E.isSylowTwoOf_J hT hM
  have hGt : P ≤ Subgroup.centralizer ({E.t} : Set G) := hPC.trans E.CE_le_Gt
  have hJp' : IsPGroup 2 (E.J.subgroupOf (Subgroup.centralizer ({E.t} : Set G))) :=
    hJp.of_equiv (Subgroup.subgroupOfEquivOfLe hJle).symm
  let SJ : Sylow 2 ↥(Subgroup.centralizer ({E.t} : Set G)) := hJp'.toSylow hJidx
  have hP' : IsPGroup 2 (P.subgroupOf (Subgroup.centralizer ({E.t} : Set G))) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hGt).symm
  obtain ⟨S', hS'⟩ := hP'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(Subgroup.centralizer ({E.t} : Set G)) SJ S'
  have hconj : ∀ p ∈ P, (g : G)⁻¹ * p * (g : G) ∈ E.J := by
    intro p hp
    have hpS' : (⟨p, hGt hp⟩ : ↥(Subgroup.centralizer ({E.t} : Set G))) ∈
        (S' : Subgroup ↥(Subgroup.centralizer ({E.t} : Set G))) :=
      hS' (Subgroup.mem_subgroupOf.2 hp)
    have h1 : (⟨p, hGt hp⟩ : ↥(Subgroup.centralizer ({E.t} : Set G))) ∈
        ((g • SJ : Sylow 2 ↥(Subgroup.centralizer ({E.t} : Set G))) :
          Subgroup ↥(Subgroup.centralizer ({E.t} : Set G))) := by
      rw [hg]
      exact hpS'
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 : g⁻¹ * (⟨p, hGt hp⟩ : ↥(Subgroup.centralizer ({E.t} : Set G))) * g ∈
        (SJ : Subgroup ↥(Subgroup.centralizer ({E.t} : Set G))) := by
      simpa [MulAut.conj_apply] using h1
    exact Subgroup.mem_subgroupOf.1 h2
  have hy₀t : E.t * (g : G) = (g : G) * E.t := Subgroup.mem_centralizer_iff.1 g.2 E.t rfl
  have he₁P : E.e₁ ∈ P := hEP E.e₁_mem_E₀
  have hfJ : (g : G)⁻¹ * E.e₁ * (g : G) ∈ E.J := hconj _ he₁P
  obtain ⟨w, hwJ, hwf⟩ := hfJ
  have hnc : ∃ g₀ ∈ Jh, w * g₀ ≠ g₀ * w := by
    by_contra hcen
    push Not at hcen
    have hcases := Jh_center w hwJ hcen
    have hteq : (g : G)⁻¹ * E.t * (g : G) = E.t := by
      calc (g : G)⁻¹ * E.t * (g : G) = (g : G)⁻¹ * ((g : G) * E.t) := by rw [← hy₀t]; group
        _ = E.t := by group
    have hf1 : (g : G)⁻¹ * E.e₁ * (g : G) = E.ι w := hwf.symm
    rcases hcases with rfl | rfl | rfl | rfl
    ·
      rw [map_one] at hf1
      apply e1_ne_one
      apply E.injective
      calc E.ι e1 = (g : G) * ((g : G)⁻¹ * E.e₁ * (g : G)) * (g : G)⁻¹ := by
            show E.e₁ = _
            group
        _ = E.ι 1 := by rw [hf1, map_one]; group
    ·
      apply e1_ne_t0
      apply E.injective
      have : E.e₁ = E.t := by
        calc E.e₁ = (g : G) * ((g : G)⁻¹ * E.e₁ * (g : G)) * (g : G)⁻¹ := by group
          _ = (g : G) * E.t * (g : G)⁻¹ := congrArg (fun x => (g : G) * x * (g : G)⁻¹) hf1
          _ = E.t := by rw [← hy₀t]; group
      exact this
    ·
      have h1 : IsConj (E.e₁ * E.t) E.z := by
        rw [isConj_iff]
        refine ⟨(g : G)⁻¹, ?_⟩
        have e1' : E.ι t0' = E.t * E.z := by
          show E.ι t0' = E.ι t0 * E.ι z0
          rw [← map_mul, t0'_eq]
        rw [e1'] at hf1
        calc (g : G)⁻¹ * (E.e₁ * E.t) * (g : G)⁻¹⁻¹
            = ((g : G)⁻¹ * E.e₁ * (g : G)) * ((g : G)⁻¹ * E.t * (g : G)) := by group
          _ = E.t * E.z * E.t := by rw [hf1, hteq]
          _ = E.z := by
            have hzt : E.t * E.z = E.z * E.t :=
              E.B_commute E.t E.t_mem_B E.z E.z_mem_B
            have htt : E.t * E.t = 1 := E.t_sq
            calc E.t * E.z * E.t = E.z * (E.t * E.t) := by rw [hzt]; group
              _ = E.z := by rw [htt, mul_one]
      exact E.not_isConj_t_z hT hM (E.isConj_t_e₁t.trans h1)
    ·
      have h1 : IsConj E.e₁ E.z := by
        rw [isConj_iff]
        exact ⟨(g : G)⁻¹, by rw [inv_inv]; exact hf1⟩
      exact E.not_isConj_t_z hT hM (E.isConj_t_e₁.trans h1)
  obtain ⟨g₀, hg₀J, hg₀ne⟩ := hnc
  have hD : Nat.card (E.J ⊓ Subgroup.centralizer ({E.ι w} : Set G) : Subgroup G) ≤ 32 := by
    have hDle : E.J ⊓ Subgroup.centralizer ({E.ι w} : Set G) ≤ E.J := inf_le_left
    have hdvd := Subgroup.card_dvd_of_le hDle
    rw [E.card_J] at hdvd
    have hne : E.J ⊓ Subgroup.centralizer ({E.ι w} : Set G) ≠ E.J := by
      intro h
      have hmem : E.ι g₀ ∈ E.J ⊓ Subgroup.centralizer ({E.ι w} : Set G) := by
        rw [h]
        exact ⟨g₀, hg₀J, rfl⟩
      have h3 := Subgroup.mem_centralizer_iff.1 hmem.2 (E.ι w) rfl
      apply hg₀ne
      apply E.injective
      rw [map_mul, map_mul]
      exact h3
    obtain ⟨k, hk⟩ := hdvd
    have hk1 : k ≠ 1 := by
      rintro rfl
      apply hne
      refine Subgroup.eq_of_le_of_card_ge hDle ?_
      rw [E.card_J]
      omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    have hk2 : 2 ≤ k := by omega
    have h64 : Nat.card (E.J ⊓ Subgroup.centralizer ({E.ι w} : Set G) : Subgroup G) * 2 ≤ 64 :=
      calc Nat.card (E.J ⊓ Subgroup.centralizer ({E.ι w} : Set G) : Subgroup G) * 2
          ≤ Nat.card (E.J ⊓ Subgroup.centralizer ({E.ι w} : Set G) : Subgroup G) * k :=
            Nat.mul_le_mul_left _ hk2
        _ = 64 := hk.symm
    omega
  have hPD : P.map (MulAut.conj (g : G)⁻¹).toMonoidHom ≤
      E.J ⊓ Subgroup.centralizer ({E.ι w} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    have hpg : (g : G)⁻¹ * p * (g : G) ∈ E.J := hconj p hp
    refine ⟨?_, Subgroup.mem_centralizer_iff.2 ?_⟩
    · simpa [MulAut.conj_apply] using hpg
    · intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have hc : E.e₁ * p = p * E.e₁ := E.mem_CE.1 (hPC hp) E.e₁ E.e₁_mem_E₀
      have hwf' : E.ι w = (g : G)⁻¹ * E.e₁ * (g : G) := hwf
      rw [hwf']
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc (g : G)⁻¹ * E.e₁ * (g : G) * ((g : G)⁻¹ * p * (g : G))
          = (g : G)⁻¹ * (E.e₁ * p) * (g : G) := by group
        _ = (g : G)⁻¹ * (p * E.e₁) * (g : G) := by rw [hc]
        _ = (g : G)⁻¹ * p * (g : G) * ((g : G)⁻¹ * E.e₁ * (g : G)) := by group
  calc Nat.card P = Nat.card (P.map (MulAut.conj (g : G)⁻¹).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj (g : G)⁻¹).injective).symm
    _ ≤ Nat.card (E.J ⊓ Subgroup.centralizer ({E.ι w} : Set G) : Subgroup G) :=
        Subgroup.card_le_of_le hPD
    _ ≤ 32 := hD

theorem card_le_32 [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPC : P ≤ E.CE) : Nat.card P ≤ 32 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf E.CE) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  obtain ⟨S, hS⟩ := hP'.exists_le_sylow
  have hE2 : IsPGroup 2 E.E₀ := IsPGroup.of_card (n := 2) (by rw [E.card_E₀]; norm_num)
  have hE' : IsPGroup 2 (E.E₀.subgroupOf E.CE) :=
    hE2.of_equiv (Subgroup.subgroupOfEquivOfLe E.E₀_le_CE).symm
  have hEn : (E.E₀.subgroupOf E.CE).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := E.mem_CE.1 g.2 (n : G) hn
    have h3 : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
      calc (g : G) * (n : G) * (g : G)⁻¹ = (n : G) * (g : G) * (g : G)⁻¹ := by rw [← h]
        _ = (n : G) := by group
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ E.E₀
    rw [h3]
    exact hn⟩
  have hES : E.E₀.subgroupOf E.CE ≤ (S : Subgroup ↥E.CE) := hE'.le_sylow_of_normal S
  have hP₁p : IsPGroup 2 ((S : Subgroup ↥E.CE).map E.CE.subtype) := S.isPGroup'.map _
  have hP₁C : (S : Subgroup ↥E.CE).map E.CE.subtype ≤ E.CE := Subgroup.map_subtype_le _
  have hP₁E : E.E₀ ≤ (S : Subgroup ↥E.CE).map E.CE.subtype := fun x hx =>
    ⟨⟨x, E.E₀_le_CE hx⟩, hES (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hPP₁ : P ≤ (S : Subgroup ↥E.CE).map E.CE.subtype := fun p hp =>
    ⟨⟨p, hPC hp⟩, hS (Subgroup.mem_subgroupOf.2 hp), rfl⟩
  exact (Subgroup.card_le_of_le hPP₁).trans (E.card_le_32_aux hT hM hP₁p hP₁C hP₁E)

@[expose] def S₀ : Subgroup G := S0m.map E.ι

theorem card_S₀ : Nat.card E.S₀ = 32 := by
  rw [S₀, Subgroup.card_map_of_injective E.injective, card_S0m]

theorem S₀_isPGroup : IsPGroup 2 E.S₀ := IsPGroup.of_card (n := 5) (by rw [E.card_S₀]; norm_num)

theorem S₀_le_CE : E.S₀ ≤ E.CE := by
  rintro _ ⟨y, hy, rfl⟩
  rw [E.mem_CE]
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, ← map_mul, S0m_comm_E0 x hx y hy]

theorem not_two_dvd_relIndex_S₀ [Finite G] (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) : ¬ 2 ∣ E.S₀.relIndex E.CE := by
  classical
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥E.CE) := inferInstance
  have hcard : Nat.card S = 2 ^ (Nat.card E.CE).factorization 2 := Sylow.card_eq_multiplicity S
  have h1 := Subgroup.card_mul_index (E.S₀.subgroupOf E.CE)
  have h2 : Nat.card (E.S₀.subgroupOf E.CE) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe E.S₀_le_CE).toEquiv, E.card_S₀]
  obtain ⟨k, hk⟩ := hdvd
  have h64 : 2 ^ 6 ∣ Nat.card E.CE := ⟨k, by
    rw [← h1, h2]
    unfold Subgroup.relIndex at hk
    rw [hk]
    ring⟩
  have h6 : 6 ≤ (Nat.card E.CE).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h64
  have h64' : 64 ≤ Nat.card S := by
    rw [hcard]
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (Nat.card E.CE).factorization 2 := Nat.pow_le_pow_right (by norm_num) h6
  have hle := E.card_le_32 hT hM (P := (S : Subgroup ↥E.CE).map E.CE.subtype)
    (S.isPGroup'.map _) (Subgroup.map_subtype_le _)
  rw [Subgroup.card_map_of_injective E.CE.subtype_injective] at hle
  omega

theorem not_mem_H_of_central [Finite G] (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) {Km : Subgroup Wc} (hK : Km ≤ S0m)
    (hKn : ∀ h ∈ S0m, ∀ k ∈ Km, h * k * h⁻¹ ∈ Km)
    (hcomm : ∀ x ∈ S0m, ∀ y ∈ S0m, x * y * x⁻¹ * y⁻¹ ∈ Km) {w : Wc} (hw : w ∈ S0m)
    (hwK : w ∉ Km) (hcent : ∀ a ∈ E.CE, a * E.ι w = E.ι w * a) :
    E.ι w ∉ oTwoUpper E.CE := by
  refine not_mem_oTwoUpper_of_transfer (X := E.CE) (H := E.S₀) (K := Km.map E.ι) E.S₀_le_CE
    E.S₀_isPGroup (E.not_two_dvd_relIndex_S₀ hT hM) (Subgroup.map_mono hK) ?_ ?_
    (g := E.ι w) ⟨w, hw, rfl⟩ ?_ ?_
  · rintro _ ⟨h, hh, rfl⟩ _ ⟨k, hk, rfl⟩
    exact ⟨h * k * h⁻¹, hKn h hh k hk, by simp only [map_mul, map_inv]⟩
  · rw [S₀, ← Subgroup.map_commutator]
    apply Subgroup.map_mono
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact hcomm x hx y hy
  · rintro ⟨k, hk, hkw⟩
    exact hwK (E.injective hkw ▸ hk)
  · intro m a ha _
    have hc : Commute a (E.ι w) := hcent a ha
    have h1 : a * (E.ι w) ^ m = (E.ι w) ^ m * a := (hc.zpow_right m).eq
    have h2 : a⁻¹ * (E.ι w) ^ m * a = (E.ι w) ^ m := by
      calc a⁻¹ * (E.ι w) ^ m * a = a⁻¹ * ((E.ι w) ^ m * a) := by group
        _ = a⁻¹ * (a * (E.ι w) ^ m) := by rw [h1]
        _ = (E.ι w) ^ m := by group
    rw [h2, inv_mul_cancel]
    exact one_mem _

theorem E₀_inf_H [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) {x : G}
    (hx : x ∈ E.E₀) (hxH : x ∈ oTwoUpper E.CE) : x = 1 := by
  have hcent : ∀ a ∈ E.CE, a * x = x * a := fun a ha => (E.mem_CE.1 ha x hx).symm
  rcases E.mem_E₀_iff.1 hx with rfl | rfl | rfl | rfl
  · rfl
  · exact absurd hxH (E.not_mem_H_of_central hT hM Kv2_le_S0m Kv2_normal Kv2_comm t0_mem_S0m
      t0_not_mem_Kv2 hcent)
  · exact absurd hxH (E.not_mem_H_of_central hT hM Ktau_le_S0m Ktau_normal Ktau_comm e1_mem_S0m
      e1_not_mem_Ktau hcent)
  · have h : E.ι (e1 * t0) = E.e₁ * E.t := map_mul _ _ _
    rw [← h] at hxH hcent
    exact absurd hxH (E.not_mem_H_of_central hT hM Ktau_le_S0m Ktau_normal Ktau_comm e1t0_mem_S0m
      e1t0_not_mem_Ktau hcent)

end Emb

end CFSG.Quasithin.A10
