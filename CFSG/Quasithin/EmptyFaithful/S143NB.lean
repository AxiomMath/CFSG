module

public import CFSG.Quasithin.EmptyFaithful.S143LE
public import CFSG.Quasithin.EmptyFaithful.S143NA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

@[expose] def kdOf {G : Type*} [Group G] (K : Subgroup G) (δ : G) : Subgroup G :=
  K ⊓ Subgroup.centralizer ({δ} : Set G)

section Gamma

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {y : G} {cm : Mat4}
  (hM : KModel hS cm y) {Vl : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)}
  (hconf : Conf6 cm Vl s)

include hS hM hconf

theorem cmat_ne_Tz_of_mem_kOf {k : G} (hk : k ∈ kOf T M (c.Ac hrW hrV hr2)) :
    cmat z a r r1 k ≠ Tz := by
  intro h
  have hσ : ∀ w, n6Act (hM.q ⟨k, hk⟩ : Equiv.Perm (Fin 6)) (psi cm w) = n6Act s (psi cm w) := by
    intro w
    rw [hM.q_act, h]
    exact (psi_intertwine hconf.s_eq w).symm
  have hact : ∀ b : N6, n6Act (hM.q ⟨k, hk⟩ : Equiv.Perm (Fin 6)) b = n6Act s b := fun b => by
    obtain ⟨w, rfl⟩ := psi_surjective hM.inj b
    exact hσ w
  have hsσ : (hM.q ⟨k, hk⟩ : Equiv.Perm (Fin 6))⁻¹ * s = 1 := by
    apply n6_faithful_perm
    intro b
    rw [map_mul, MulAut.mul_apply, ← hact b, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel,
      map_one]
    rfl
  have hsig : (hM.q ⟨k, hk⟩ : Equiv.Perm (Fin 6)).sign = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp (hM.q _).2
  have hs_eq : (hM.q ⟨k, hk⟩ : Equiv.Perm (Fin 6)) = s := inv_mul_eq_one.mp hsσ
  rw [hs_eq, hconf.s_sign] at hsig
  exact absurd hsig (by decide)

variable {t : G} (htT : t ∈ T) (htRQ : t ∉ rOf T M ⊔ qOf T)

include htT htRQ

theorem exists_decomp_of_mem_centralizer
    (hNA : Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) =
      kOf T M (c.Ac hrW hrV hr2) ⊔ dOf T M)
    {γ : G} (hγ : γ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) :
    ∃ a' ∈ c.Ac hrW hrV hr2, ∃ δ ∈ dOf T M,
      δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ∧ γ = a' * δ := by
  have hB := hS.basis
  have hKN := c.kOf_le_normalizer_Ac hrW hrV hr2
  have hDKN := c.dOf_le_normalizer_kOf hrW hrV hr2
  have hDN := dOf_le_normalizer_Ac (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2)
  have hγN : γ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    Subgroup.centralizer_le_normalizer _ hγ
  rw [hNA] at hγN
  obtain ⟨k, hk, δ, hδ, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hDKN).1 hγN
  have hc1 : cmat z a r r1 (k * δ) = I4 :=
    (hB.cmat_eq_one_iff_mem_centralizer (Subgroup.mul_mem _ (hKN hk) (hDN hδ))).mpr hγ
  have hδ1 : cmat z a r r1 δ = I4 := by
    rcases D_cmat hS hδ with h | h
    · exact h
    · exfalso
      rw [hB.cmat_mul (hKN hk) (hDN hδ), h] at hc1
      have hk1 : cmat z a r r1 k = Tz := by
        calc cmat z a r r1 k = mm I4 (cmat z a r r1 k) := (I4_mm _).symm
          _ = mm (mm Tz Tz) (cmat z a r r1 k) := by rw [Tz_sq]
          _ = mm Tz (mm Tz (cmat z a r r1 k)) := mm_assoc _ _ _
          _ = Tz := by rw [hc1, mm_I4]
      exact cmat_ne_Tz_of_mem_kOf hS hM hconf hk hk1
  have hδΓ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
    (hB.cmat_eq_one_iff_mem_centralizer (hDN hδ)).mp hδ1
  have hkΓ : k ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) := by
    have := Subgroup.mul_mem _ hγ ((Subgroup.centralizer _).inv_mem hδΓ)
    simpa using this
  exact ⟨k, hS.kOf_inf_centralizer_le htT htRQ hM ⟨hk, hkΓ⟩, δ, hδ, hδΓ, rfl⟩

theorem exists_delta
    (hNA : Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) =
      kOf T M (c.Ac hrW hrV hr2) ⊔ dOf T M)
    (hΓ : c.Ac hrW hrV hr2 < Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) :
    ∃ δ ∈ dOf T M, δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ∧
      δ ∉ c.Ac hrW hrV hr2 := by
  obtain ⟨γ, hγ, hγA⟩ : ∃ γ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G),
      γ ∉ c.Ac hrW hrV hr2 := by
    by_contra hh
    push Not at hh
    exact hΓ.ne (le_antisymm hΓ.le hh) |>.elim
  obtain ⟨a', ha', δ, hδ, hδΓ, rfl⟩ := exists_decomp_of_mem_centralizer hS hM hconf htT htRQ hNA hγ
  refine ⟨δ, hδ, hδΓ, fun hδA => hγA ?_⟩
  exact (c.Ac hrW hrV hr2).mul_mem ha' hδA

end Gamma


section Delta

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {Vl Vr : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)} (hP : Conf6Plus cm Vl Vr s)
  (hVl : ∀ σ ∈ Vl, ∃ u ∈ uOfL22 T M, mm cm (matOf6 σ) = mm (cmat z a r r1 u) cm)
  (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)
  {δ : G} (hδD : δ ∈ dOf T M) (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
  (hδA : δ ∉ c.Ac hrW hrV hr2)

include hS htT htRQ hM hP hVl hC1 hδD hδ hδA

theorem exists_unit_cocyc :
    ∃ p : Fin 6, s p ≠ p ∧
      ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = dW (CFSG.Quasithin.S143.A6Model.unitVec p) σ.1 := by
  obtain ⟨w, hw⟩ := eq_dW htT htRQ hM hδ
  have hVan := vanL_of_cocyc hS htT htRQ hM hP.conf hVl hδD hδ hw
  have hnev : ¬ wEven w := fun he => by
    obtain ⟨b, hb⟩ := dW_principal_of_even he
    exact hδA (mem_Ac_of_principal htT htRQ hC1 hM hδ b (fun σ => by rw [hw, hb]))
  obtain ⟨p, hp, hpσ⟩ := hP.odd w hVan hnev
  refine ⟨p, hp, fun σ => ?_⟩
  rw [hw σ]
  have hs1 : σ.1.sign = 1 := Equiv.Perm.mem_alternatingGroup.mp σ.2
  unfold dW
  congr 1
  rw [hpσ σ.1 hs1]


omit hP hVl hC1 in
theorem mem_kdOf_iff {p : Fin 6}
    (hcoc : ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = dW (CFSG.Quasithin.S143.A6Model.unitVec p) σ.1)
    {k : G} (hk : k ∈ kOf T M (c.Ac hrW hrV hr2)) :
    k ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ↔ (hM.q ⟨k, hk⟩ : Equiv.Perm (Fin 6)) p = p := by
  have hB := hS.basis
  have he := fcoc_mem htT htRQ hM hδ ⟨k, hk⟩
  have hq := cocyc_q htT htRQ hM hδ ⟨k, hk⟩
  have hs1 : (hM.q ⟨k, hk⟩ : Equiv.Perm (Fin 6)).sign = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp (hM.q _).2
  rw [hcoc] at hq
  constructor
  · intro hkd
    have hcomm : δ * k = k * δ := Subgroup.mem_centralizer_iff.mp hkd.2 δ rfl
    have h1 : k * δ * k⁻¹ * δ⁻¹ = 1 := by rw [← hcomm]; group
    have h2 : dW (CFSG.Quasithin.S143.A6Model.unitVec p) (hM.q ⟨k, hk⟩ : Equiv.Perm (Fin 6)) = 1 := by
      rw [hq]
      show psiA cm z a r r1 (k * δ * k⁻¹ * δ⁻¹) = 1
      rw [h1, psiA_one hB]
    exact (rawD_unit_eq_zero_iff p _ hs1).mp ((dW_eq_one_iff _ _).mp h2)
  · intro hfix
    have h2 : dW (CFSG.Quasithin.S143.A6Model.unitVec p) (hM.q ⟨k, hk⟩ : Equiv.Perm (Fin 6)) = 1 :=
      (dW_eq_one_iff _ _).mpr ((rawD_unit_eq_zero_iff p _ hs1).mpr hfix)
    have h3 : psiA cm z a r r1 (k * δ * k⁻¹ * δ⁻¹) = psiA cm z a r r1 1 := by
      rw [psiA_one hB]
      exact hq.symm.trans h2
    have h4 : k * δ * k⁻¹ * δ⁻¹ = 1 :=
      psiA_inj hB hM.inj he (c.Ac hrW hrV hr2).one_mem h3
    refine ⟨hk, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h5 : k * h = h * k := by
      calc k * h = (k * h * k⁻¹ * h⁻¹) * h * k := by group
        _ = h * k := by rw [h4, one_mul]
    exact h5.symm

theorem exists_conj_zdelta
    : ∃ k ∈ kOf T M (c.Ac hrW hrV hr2), k * δ * k⁻¹ = z * δ := by
  have hB := hS.basis
  obtain ⟨p, hp, hcoc⟩ := exists_unit_cocyc hS htT htRQ hM hP hVl hC1 hδD hδ hδA
  have hs := hP.swap p hp
  obtain ⟨σ₀, hσ₀s, hσ₀p⟩ := exists_alt_perm_map p (s p)
  have hz1 : psiA cm z a r r1 z ≠ 1 := fun h => hS.z_ne
    (psiA_inj hB hM.inj hS.z_A (c.Ac hrW hrV hr2).one_mem (h.trans (psiA_one hB).symm))
  have hψz : psiA cm z a r r1 z = dW (CFSG.Quasithin.S143.A6Model.unitVec p) σ₀ := by
    have h1 := psi_intertwine (σ := s) hP.conf.s_eq ⟨false, false, false, true⟩
    have h2 : vm (⟨false, false, false, true⟩ : V4) Tz = (⟨true, false, false, false⟩ : V4).add
        ⟨false, false, false, true⟩ := by rw [vm_e3]; rfl
    rw [h2, psi_add] at h1
    have hb : ∀ b : N6, b⁻¹ = b := fun b => inv_eq_of_mul_eq_one_right (n6_mul_self b)
    have h3 : psiA cm z a r r1 z = n6Act s (psi cm ⟨false, false, false, true⟩) *
        (psi cm ⟨false, false, false, true⟩)⁻¹ := by
      rw [h1, hb, mul_assoc, n6_mul_self, mul_one]
      unfold psiA
      rw [hB.coordsOf_e0]
    rw [h3]
    rw [h3] at hz1
    have hne : p ≠ s p := fun h => hp h.symm
    rw [hs] at hz1 ⊢
    rcases swap_comm_cases p (s p) σ₀ (psi cm ⟨false, false, false, true⟩) ⟨hne, hσ₀s, hσ₀p⟩ with
      h | h
    · exact absurd h hz1
    · exact h
  obtain ⟨k, hk⟩ := hM.q_surjective ⟨σ₀, Equiv.Perm.mem_alternatingGroup.mpr hσ₀s⟩
  have hq := cocyc_q htT htRQ hM hδ k
  rw [hk, hcoc] at hq
  have he := fcoc_mem htT htRQ hM hδ k
  have h4 : (k : G) * δ * (k : G)⁻¹ * δ⁻¹ = z := by
    apply psiA_inj hB hM.inj he hS.z_A
    rw [hψz]
    exact hq.symm
  refine ⟨k, k.2, ?_⟩
  calc (k : G) * δ * (k : G)⁻¹ = ((k : G) * δ * (k : G)⁻¹ * δ⁻¹) * δ := by group
    _ = z * δ := by rw [h4]

omit hP hVl hC1 in
theorem exists_order_five_kd {p : Fin 6}
    (hcoc : ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = dW (CFSG.Quasithin.S143.A6Model.unitVec p) σ.1) :
    ∃ y₅ ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ, orderOf y₅ = 5 := by
  obtain ⟨σ, hσs, hσp, hσ5, hσ1⟩ := exists_five_fixing p
  obtain ⟨k, hk⟩ := hM.q_surjective ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσs⟩
  have hkK : (k : G) ∈ kOf T M (c.Ac hrW hrV hr2) := k.2
  have hkd : (k : G) ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ := by
    rw [mem_kdOf_iff hS htT htRQ hM hδD hδ hδA hcoc hkK]
    have : (hM.q ⟨k, hkK⟩ : Equiv.Perm (Fin 6)) = σ := congrArg Subtype.val hk
    rw [this]
    exact hσp
  have hord5 : orderOf (hM.q k) = 5 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    apply orderOf_eq_prime
    · apply Subtype.ext
      show ((hM.q k : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) ^ 5 = 1
      rw [show (hM.q k : ↥(alternatingGroup (Fin 6))) = ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσs⟩
        from hk]
      exact hσ5
    · intro h
      apply hσ1
      have := congrArg Subtype.val (h.trans (by rfl : (1 : ↥(alternatingGroup (Fin 6))) = 1))
      rw [show (hM.q k : ↥(alternatingGroup (Fin 6))) = ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσs⟩
        from hk] at this
      exact this
  have hdvd : 5 ∣ orderOf k := by
    have := orderOf_map_dvd (hM.q) k
    rwa [hord5] at this
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : 0 < orderOf k := orderOf_pos k
  have hm' : 0 < m := by omega
  refine ⟨(k : G) ^ m, (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ).pow_mem hkd m, ?_⟩
  have hkG : orderOf (k : G) = orderOf k := Subgroup.orderOf_coe k
  rw [orderOf_pow_of_dvd hm'.ne' ⟨5, by rw [hkG, hm]; ring⟩, hkG, hm]
  exact Nat.mul_div_cancel 5 hm'


end Delta

end S143

end CFSG.Quasithin
