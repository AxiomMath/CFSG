module

public import CFSG.Quasithin.EmptyFaithful.S143NB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

section FinHelp

variable {G : Type*} [Finite G]

theorem mem_finset_of_card_le (X : Set G) (S : Finset G) (hSX : ∀ s ∈ S, s ∈ X)
    (hcard : Nat.card X ≤ S.card) : ∀ x ∈ X, x ∈ S := by
  classical
  intro x hx
  by_contra hxS
  have h1 : (insert x S).card = S.card + 1 := Finset.card_insert_of_notMem hxS
  have h2 : (insert x S).card ≤ Nat.card ↥X := by
    have : Nat.card ↥(↑(insert x S) : Set G) ≤ Nat.card ↥X :=
      Nat.card_mono (Set.toFinite X) (fun y hy => by
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hy'
        · exact hx
        · exact hSX y hy')
    simpa using this
  omega

theorem commute_of_pow_commute {H : Type*} [Group H] {h x : H} {n : ℕ}
    (hn : Nat.Coprime n (orderOf h)) (hc : h ^ n * x = x * h ^ n) : h * x = x * h := by
  have hmem : h ∈ Subgroup.zpowers (h ^ n) := A4.mem_zpowers_pow_of_coprime hn
  have hcent : Subgroup.zpowers (h ^ n) ≤ Subgroup.centralizer ({x} : Set H) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hc.symm)
  exact (Subgroup.mem_centralizer_iff.mp (hcent hmem) x rfl).symm

end FinHelp

section Counter

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.conj_mem_dOf {x d : G} (hx : x ∈ mcOf T) (hd : d ∈ dOf T M) :
    x * d * x⁻¹ ∈ dOf T M := by
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := c.hHU
  refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (mcOf T) hx) d).mp hd.1,
    Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have hxu : x⁻¹ * u * x⁻¹⁻¹ ∈ uOfL22 T M :=
    (Subgroup.mem_normalizer_iff.mp (hHU ((mcOf T).inv_mem hx)) u).mp hu
  have hyd := Subgroup.mem_centralizer_iff.mp hd.2 _ hxu
  calc u * (x * d * x⁻¹) = x * ((x⁻¹ * u * x⁻¹⁻¹) * d) * x⁻¹ := by group
    _ = x * (d * (x⁻¹ * u * x⁻¹⁻¹)) * x⁻¹ := by rw [hyd]
    _ = (x * d * x⁻¹) * u := by group

omit [Finite G] c in
theorem mem_mcOf_comm {x z : G} (hx : x ∈ mcOf T) (hz : z ∈ quasithinOmegaOneCenter T) :
    x * z = z * x := (Subgroup.mem_centralizer_iff.mp hx z hz).symm

theorem Counter.card_range_actK : Nat.card c.actK.range = 72 := by
  have h := c.h1281
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ := c.c15.orth
  let _ : CommGroup (UT T M) :=
    { (inferInstance : Group (UT T M)) with
      mul_comm := fun a b => (tilde_isMulCommutative h).is_comm.comm a b }
  obtain ⟨L₁, L₂, t₀, hS, -⟩ := exists_ofourStruct_of_plusType
    (W := UT T M) (q := q) (tilde_mul_self h) hq4 hq1 hq2 hq3
  have hrange : c.actK.range = orthogonalGroupOf q := c.actK_range.trans hq6
  rw [hrange]
  exact hS.card_X

theorem Counter.not_five_dvd_card_mcOf : ¬ 5 ∣ Nat.card ↥(mcOf T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 c.actK.ker := by
    intro k
    have hkQ : ((k : ↥(mcOf T)) : G) ∈ qOf T := by
      rw [← c.actK_ker_map]
      exact ⟨k, k.2, rfl⟩
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 (mcOf T) ⟨((k : ↥(mcOf T)) : G), hkQ⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨n, hn⟩ := hker.exists_card_eq
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup c.actK.ker
  have h2 : Nat.card (↥(mcOf T) ⧸ c.actK.ker) = Nat.card c.actK.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange c.actK).toEquiv
  rw [h2, c.card_range_actK, hn] at h1
  rw [h1]
  intro hd
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp hd with h | h
  · omega
  · have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h
    omega

theorem Counter.not_conj_of_order_five {z δ y₅ : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hz1 : z ≠ 1) (hy5 : orderOf y₅ = 5) (hyδ : y₅ * δ = δ * y₅) :
    ∀ x : G, x * z * x⁻¹ ≠ δ := by
  intro x hx
  have hw : x⁻¹ * y₅ * x ∈ mcOf T := by
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    rcases c.mem_Z_cases hz hz1 hu with rfl | rfl
    · simp
    · have h1 : y₅ * (x * u * x⁻¹) = (x * u * x⁻¹) * y₅ := by rw [hx]; exact hyδ
      calc u * (x⁻¹ * y₅ * x) = x⁻¹ * ((x * u * x⁻¹) * y₅) * x := by group
        _ = x⁻¹ * (y₅ * (x * u * x⁻¹)) * x := by rw [h1]
        _ = (x⁻¹ * y₅ * x) * u := by group
  have hord : orderOf (x⁻¹ * y₅ * x) = 5 := by
    have : x⁻¹ * y₅ * x = (MulAut.conj x⁻¹) y₅ := by simp
    rw [this, MulEquiv.orderOf_eq]
    exact hy5
  have hdvd := Subgroup.orderOf_dvd_natCard (mcOf T) hw
  rw [hord] at hdvd
  exact c.not_five_dvd_card_mcOf hdvd

end Counter

section Gamma

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)

include hS htT htRQ hM hC1

theorem Gamma_sq {γ : G} (hγ : γ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) :
    γ * γ = 1 := by
  have hB := hS.basis
  apply cocyc_injective htT htRQ hC1 hM (Subgroup.mul_mem _ hγ hγ) (Subgroup.one_mem _)
  funext σ
  rw [cocyc_mul htT htRQ hM hγ hγ, n6_mul_self]
  obtain ⟨k, rfl⟩ := hM.q_surjective σ
  rw [cocyc_q htT htRQ hM (Subgroup.one_mem _), fcoc_one hB]

end Gamma

section Delta

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {Vl Vr : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)} (hP : Conf6Plus cm Vl Vr s)
  (hVl : ∀ σ ∈ Vl, ∃ u ∈ uOfL22 T M, mm cm (matOf6 σ) = mm (cmat z a r r1 u) cm)
  (hVr : ∀ σ ∈ Vr, ∃ ρ' ∈ rOf T M, mm cm (matOf6 σ) = mm (cmat z a r r1 ρ') cm)
  (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)
  {δ : G} (hδD : δ ∈ dOf T M) (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
  (hδA : δ ∉ c.Ac hrW hrV hr2)

include hS htT htRQ hM hP hVl hC1 hδD hδ hδA

theorem D0_cases {w : G} (hwD : w ∈ dOf T M)
    (hwΓ : w ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) :
    w = 1 ∨ w = z ∨ w = δ ∨ w = z * δ := by
  classical
  have hB := hS.basis
  have hz2 : z * z = 1 := c.sq_Ac hrW hrV hr2 hS.z_A
  have hzD : z ∈ dOf T M := Z_le_dOf c hS.z_mem
  have hzΓ : z ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a' ha' => hB.comm a' ha' z hS.z_A
  set X : Set G := ((dOf T M ⊓ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) : Subgroup G) : Set G)
    with hX
  set S : Finset G := {1, z, δ, z * δ} with hSdef
  have hSX : ∀ s' ∈ S, s' ∈ X := by
    intro s' hs'
    simp only [hSdef, Finset.mem_insert, Finset.mem_singleton] at hs'
    rcases hs' with rfl | rfl | rfl | rfl
    · exact (dOf T M ⊓ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).one_mem
    · exact ⟨hzD, hzΓ⟩
    · exact ⟨hδD, hδ⟩
    · exact (dOf T M ⊓ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).mul_mem ⟨hzD, hzΓ⟩
        ⟨hδD, hδ⟩
  have hz1 : z ≠ 1 := hS.z_ne
  have hδ1 : δ ≠ 1 := fun h => hδA (h ▸ (c.Ac hrW hrV hr2).one_mem)
  have hδz : δ ≠ z := fun h => hδA (h ▸ hS.z_A)
  have hzδ1 : z * δ ≠ 1 := fun h => hδz (by
    have : δ = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]; exact (inv_eq_of_mul_eq_one_right hz2))
  have hzδz : z * δ ≠ z := fun h => hδ1 (by simpa using h)
  have hzδδ : z * δ ≠ δ := fun h => hz1 (by simpa using h)
  have hS4 : S.card = 4 := by
    have h3 : δ ∉ ({z * δ} : Finset G) := by simp [Ne.symm hzδδ]
    have h2 : z ∉ ({δ, z * δ} : Finset G) := by simp [Ne.symm hδz, Ne.symm hzδz]
    have h1 : (1 : G) ∉ ({z, δ, z * δ} : Finset G) := by
      simp [Ne.symm hz1, Ne.symm hδ1, Ne.symm hzδ1]
    rw [hSdef, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have hcard : Nat.card X ≤ S.card := by
    rw [hS4]
    have h0 := D0_card_le hS htT htRQ hM hP.conf hVl hC1
    have hinj : Function.Injective (fun x : ↥(dOf T M ⊓ Subgroup.centralizer
        (c.Ac hrW hrV hr2 : Set G)) =>
        (⟨⟨x.1, x.2.1⟩, Subgroup.mem_subgroupOf.mpr x.2.2⟩ :
          ↥((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M)))) := by
      intro x x' h
      apply Subtype.ext
      have h' := congrArg (fun q : ↥((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf
        (dOf T M)) => (((q : ↥(dOf T M)) : G))) h
      exact h'
    exact (Nat.card_le_card_of_injective _ hinj).trans h0
  have := mem_finset_of_card_le X S hSX hcard w ⟨hwD, hwΓ⟩
  simp only [hSdef, Finset.mem_insert, Finset.mem_singleton] at this
  exact this

theorem centralizer_D_delta {w : G} (hwD : w ∈ dOf T M) (hwδ : w * δ = δ * w) :
    w = 1 ∨ w = z ∨ w = δ ∨ w = z * δ := by
  have hB := hS.basis
  have hDN := dOf_le_normalizer_Ac (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2)
  rcases D_cmat hS hwD with h | h
  · exact D0_cases hS htT htRQ hM hP hVl hC1 hδD hδ hδA hwD
      ((hB.cmat_eq_one_iff_mem_centralizer (hDN hwD)).mp h)
  · exfalso
    refine D_noncomm hS htT htRQ hM hP.conf hVl hC1 hwD h hδD hδ hδA ?_
    calc w * δ * w⁻¹ = (δ * w) * w⁻¹ := by rw [hwδ]
      _ = δ := by group

include hVr

omit hVl hC1 in
theorem exists_rho_not_centralize {p : Fin 6} (hps : s p ≠ p)
    (hcoc : ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = dW (CFSG.Quasithin.S143.A6Model.unitVec p) σ.1) :
    ∃ ρ ∈ rOf T M, ρ * δ ≠ δ * ρ := by
  obtain ⟨σ, hσ, hσp⟩ := hP.rMoves p hps
  obtain ⟨ρ, hρ, hmat⟩ := hVr σ hσ
  have hρK : ρ ∈ kOf T M (c.Ac hrW hrV hr2) :=
    c.rOf_sup_uOfL22_le_kOf hrW hrV hr2 (Subgroup.mem_sup_left hρ)
  have hσ1 : σ.sign = 1 := hP.vr_sign σ hσ
  have hq : (hM.q ⟨ρ, hρK⟩ : Equiv.Perm (Fin 6)) = σ := by
    refine perm_eq_of_act hM.inj (Equiv.Perm.mem_alternatingGroup.mp (hM.q _).2) hσ1 fun w' => ?_
    rw [hM.q_act]
    exact (psi_intertwine hmat w').symm
  refine ⟨ρ, hρ, fun hcomm => ?_⟩
  have hkd : ρ ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ :=
    ⟨hρK, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hcomm.symm⟩
  have := (mem_kdOf_iff hS htT htRQ hM hδD hδ hδA hcoc hρK).mp hkd
  rw [hq] at this
  exact hσp this

omit hVl hC1 in
theorem exists_eps {p : Fin 6} (hps : s p ≠ p)
    (hcoc : ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = dW (CFSG.Quasithin.S143.A6Model.unitVec p) σ.1)
    (hAAt : rOf T M = c.Ac hrW hrV hr2 ⊔ conjSubgroup (c.Ac hrW hrV hr2) t) :
    ∃ ε ∈ dOf T M, cmat z a r r1 ε = Tz := by
  by_contra hne
  push Not at hne
  have hB := hS.basis
  have hDN := dOf_le_normalizer_Ac (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2)
  have hDΓ : ∀ w ∈ dOf T M, w ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) := by
    intro w hw
    rcases D_cmat hS hw with h | h
    · exact (hB.cmat_eq_one_iff_mem_centralizer (hDN hw)).mp h
    · exact absurd h (hne w hw)
  obtain ⟨ρ, hρR, hρ⟩ := exists_rho_not_centralize hS htT htRQ hM hP hVr hδD hδ hδA hps hcoc
  apply hρ
  have htH : t ∈ mcOf T := c.h1281.almostSpecialHyp_g1.T_le_H htT
  have hδ' : t * δ * t⁻¹ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
    hDΓ _ (c.conj_mem_dOf htH hδD)
  have hle : rOf T M ≤ Subgroup.centralizer ({δ} : Set G) := by
    rw [hAAt]
    refine sup_le (fun w hw => ?_) (fun w hw => ?_)
    · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.mp hδ w hw).symm
    · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have hwA : t * w * t⁻¹ ∈ c.Ac hrW hrV hr2 := mem_conjSubgroup_iff.mp hw
      have h1 := Subgroup.mem_centralizer_iff.mp hδ' _ hwA
      have h2 : t * (w * h) * t⁻¹ = t * (h * w) * t⁻¹ := by
        calc t * (w * h) * t⁻¹ = (t * w * t⁻¹) * (t * h * t⁻¹) := by group
          _ = (t * h * t⁻¹) * (t * w * t⁻¹) := h1
          _ = t * (h * w) * t⁻¹ := by group
      have h3 := congrArg (fun q => t⁻¹ * q * t) h2
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at h3
      exact h3.symm
  exact (Subgroup.mem_centralizer_iff.mp (hle hρR) δ rfl).symm

omit hVl hC1 hP hVr hM htT htRQ hδA hδ hδD in
theorem z_comm_dOf {w : G} (hw : w ∈ dOf T M) : z * w = w * z :=
  Subgroup.mem_centralizer_iff.mp hw.2 z (Hyp1281Two.VZ_le_uOfL22 T M hS.z_V)

omit hVl hC1 hP hVr hM htT htRQ hδA hδ hδD hS [Finite G] in
theorem card_invol_D_le
    (hemb : ∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X)) :
    Nat.card ↥{w : G | w ∈ dOf T M ∧ w * w = 1} ≤ 6 := by
  classical
  obtain ⟨X, ⟨e⟩⟩ := hemb
  have hinj : Function.Injective (fun w : ↥{w : G | w ∈ dOf T M ∧ w * w = 1} =>
      (⟨((e ⟨w.1, w.2.1⟩ : ↥X) : DihedralGroup 4), by
        have h := congrArg (fun q : ↥X => ((q : ↥X) : DihedralGroup 4))
          (show e ⟨w.1, w.2.1⟩ * e ⟨w.1, w.2.1⟩ = 1 from by
            rw [← map_mul, ← map_one e]
            congr 1
            exact Subtype.ext w.2.2)
        simpa using h⟩ : {y : DihedralGroup 4 // y * y = 1})) := by
    intro w w' h
    have h0 : ((e ⟨w.1, w.2.1⟩ : ↥X) : DihedralGroup 4) = ((e ⟨w'.1, w'.2.1⟩ : ↥X) : DihedralGroup 4) :=
      congrArg (fun q : {y : DihedralGroup 4 // y * y = 1} => q.1) h
    have h1 : e ⟨w.1, w.2.1⟩ = e ⟨w'.1, w'.2.1⟩ := Subtype.ext h0
    have h2 := e.injective h1
    apply Subtype.ext
    exact congrArg (fun q : ↥(dOf T M) => (q : G)) h2
  refine (Nat.card_le_card_of_injective _ hinj).trans ?_
  rw [Nat.card_eq_fintype_card]
  decide

omit hVr in
theorem odd_commute_delta
    (hemb : ∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X))
    {h : G} (hh : h ∈ mcOf T) (hodd : Odd (orderOf h)) : h * δ = δ * h := by
  classical
  have hz := hS.z_mem
  have hzh : h * z = z * h := mem_mcOf_comm hh hz
  have hz2 : z * z = 1 := c.sq_Ac hrW hrV hr2 hS.z_A
  have hz1 : z ≠ 1 := hS.z_ne
  have hzD : z ∈ dOf T M := Z_le_dOf c hz
  have hδ2 : δ * δ = 1 := Gamma_sq hS htT htRQ hM hC1 hδ
  have hδ1 : δ ≠ 1 := fun e => hδA (e ▸ (c.Ac hrW hrV hr2).one_mem)
  have hδz : δ ≠ z := fun e => hδA (e ▸ hS.z_A)
  have hzδ : z * δ = δ * z := z_comm_dOf hS hδD
  have hcj : ∀ w : G, h * (z * w) * h⁻¹ = z * (h * w * h⁻¹) := fun w => by
    calc h * (z * w) * h⁻¹ = (h * z) * w * h⁻¹ := by group
      _ = (z * h) * w * h⁻¹ := by rw [hzh]
      _ = z * (h * w * h⁻¹) := by group
  have hzz : ∀ w : G, z * (z * w) = w := fun w => by rw [← mul_assoc, hz2, one_mul]
  have hcop : ∀ j : ℕ, Nat.Coprime (2 ^ j) (orderOf h) := fun j =>
    Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
  set δ₁ := h * δ * h⁻¹ with hδ₁
  have hδ₁D : δ₁ ∈ dOf T M := c.conj_mem_dOf hh hδD
  have hδ₁2 : δ₁ * δ₁ = 1 := by
    calc δ₁ * δ₁ = h * (δ * δ) * h⁻¹ := by rw [hδ₁]; group
      _ = 1 := by rw [hδ2]; group
  by_cases hA : δ₁ * δ = δ * δ₁
  · rcases centralizer_D_delta hS htT htRQ hM hP hVl hC1 hδD hδ hδA hδ₁D hA with
      e | e | e | e
    · exact absurd (by
        have := congrArg (fun q => h⁻¹ * q * h) e
        simpa [hδ₁, mul_assoc] using this) hδ1
    · exact absurd (by
        have := congrArg (fun q => h⁻¹ * q * h) e
        have h3 : h⁻¹ * z * h = z := by
          calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
            _ = h⁻¹ * (h * z) := by rw [hzh]
            _ = z := by group
        simpa [hδ₁, mul_assoc, h3] using this) hδz
    ·
      calc h * δ = (h * δ * h⁻¹) * h := by group
        _ = δ * h := by rw [← hδ₁, e]
    ·
      refine commute_of_pow_commute (n := 2) (by simpa using hcop 1) ?_
      have h2 : h * (h * δ * h⁻¹) * h⁻¹ = δ := by
        rw [← hδ₁, e, hcj δ, ← hδ₁, e, hzz]
      rw [pow_two]
      calc h * h * δ = (h * (h * δ * h⁻¹) * h⁻¹) * (h * h) := by group
        _ = δ * (h * h) := by rw [h2]
  ·
    set δ₂ := h * δ₁ * h⁻¹ with hδ₂
    have hδ₂D : δ₂ ∈ dOf T M := c.conj_mem_dOf hh hδ₁D
    have hδ₂2 : δ₂ * δ₂ = 1 := by
      calc δ₂ * δ₂ = h * (δ₁ * δ₁) * h⁻¹ := by rw [hδ₂]; group
        _ = 1 := by rw [hδ₁2]; group
    have e1 : h⁻¹ * δ₂ * h = δ₁ := by rw [hδ₂]; group
    have e2 : h⁻¹ * δ₁ * h = δ := by rw [hδ₁]; group
    have hB2 : ¬ δ₂ * δ₁ = δ₁ * δ₂ := by
      intro hc
      apply hA
      calc δ₁ * δ = (h⁻¹ * δ₂ * h) * (h⁻¹ * δ₁ * h) := by rw [e1, e2]
        _ = h⁻¹ * (δ₂ * δ₁) * h := by group
        _ = h⁻¹ * (δ₁ * δ₂) * h := by rw [hc]
        _ = (h⁻¹ * δ₁ * h) * (h⁻¹ * δ₂ * h) := by group
        _ = δ * δ₁ := by rw [e1, e2]
    have hzc : ∀ w ∈ dOf T M, z * w = w * z := fun w hw => z_comm_dOf hS hw
    have hsqz : ∀ w ∈ dOf T M, w * w = 1 → (z * w) * (z * w) = 1 := by
      intro w hw hw2
      calc (z * w) * (z * w) = z * (w * z) * w := by group
        _ = z * (z * w) * w := by rw [← hzc w hw]
        _ = (z * z) * (w * w) := by group
        _ = 1 := by rw [hz2, hw2, one_mul]
    set Xi : Set G := {w : G | w ∈ dOf T M ∧ w * w = 1} with hXi
    set S6 : Finset G := {1, z, δ, z * δ, δ₁, z * δ₁} with hS6
    have hSX : ∀ s' ∈ S6, s' ∈ Xi := by
      intro s' hs'
      simp only [hS6, Finset.mem_insert, Finset.mem_singleton] at hs'
      rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨(dOf T M).one_mem, mul_one _⟩
      · exact ⟨hzD, hz2⟩
      · exact ⟨hδD, hδ2⟩
      · exact ⟨(dOf T M).mul_mem hzD hδD, hsqz δ hδD hδ2⟩
      · exact ⟨hδ₁D, hδ₁2⟩
      · exact ⟨(dOf T M).mul_mem hzD hδ₁D, hsqz δ₁ hδ₁D hδ₁2⟩
    have hzδ1 : z * δ ≠ 1 := fun e => hδz (by
      have : δ = z⁻¹ := eq_inv_of_mul_eq_one_right e
      rw [this]; exact inv_eq_of_mul_eq_one_right hz2)
    have hzδz : z * δ ≠ z := fun e => hδ1 (by simpa using e)
    have hzδδ : z * δ ≠ δ := fun e => hz1 (by simpa using e)
    have hn1 : δ₁ ≠ 1 := fun e => hA (by rw [e]; simp)
    have hn2 : δ₁ ≠ z := fun e => hA (by rw [e]; exact hzδ)
    have hn3 : δ₁ ≠ δ := fun e => hA (by rw [e])
    have hn4 : δ₁ ≠ z * δ := fun e => hA (by
      rw [e]
      have key : δ * (z * δ) = z * δ * δ := by rw [← mul_assoc, ← hzδ]
      exact key.symm)
    have hm1 : z * δ₁ ≠ 1 := fun e => hn2 (by
      have : δ₁ = z⁻¹ := eq_inv_of_mul_eq_one_right e
      rw [this]; exact inv_eq_of_mul_eq_one_right hz2)
    have hm2 : z * δ₁ ≠ z := fun e => hn1 (by simpa using e)
    have hm3 : z * δ₁ ≠ δ := fun e => hn4 (by
      have : δ₁ = z * δ := by
        calc δ₁ = z * (z * δ₁) := (hzz δ₁).symm
          _ = z * δ := by rw [e]
      exact this)
    have hm4 : z * δ₁ ≠ z * δ := fun e => hn3 (mul_left_cancel e)
    have hm5 : z * δ₁ ≠ δ₁ := fun e => hz1 (by simpa using e)
    have hS6c : S6.card = 6 := by
      have i5 : z * δ₁ ∉ (∅ : Finset G) := by simp
      have i4 : δ₁ ∉ ({z * δ₁} : Finset G) := by simp [Ne.symm hm5]
      have i3 : z * δ ∉ ({δ₁, z * δ₁} : Finset G) := by
        simp [Ne.symm hn4, Ne.symm hm4]
      have i2 : δ ∉ ({z * δ, δ₁, z * δ₁} : Finset G) := by
        simp [Ne.symm hzδδ, Ne.symm hn3, Ne.symm hm3]
      have i1 : z ∉ ({δ, z * δ, δ₁, z * δ₁} : Finset G) := by
        simp [Ne.symm hδz, Ne.symm hzδz, Ne.symm hn2, Ne.symm hm2]
      have i0 : (1 : G) ∉ ({z, δ, z * δ, δ₁, z * δ₁} : Finset G) := by
        simp [Ne.symm hz1, Ne.symm hδ1, Ne.symm hzδ1, Ne.symm hn1, Ne.symm hm1]
      rw [hS6, Finset.card_insert_of_notMem i0, Finset.card_insert_of_notMem i1,
        Finset.card_insert_of_notMem i2, Finset.card_insert_of_notMem i3,
        Finset.card_insert_of_notMem i4, Finset.card_singleton]
    have hcard : Nat.card Xi ≤ S6.card := by
      rw [hS6c]
      exact card_invol_D_le hemb
    have hmem := mem_finset_of_card_le Xi S6 hSX hcard δ₂ ⟨hδ₂D, hδ₂2⟩
    simp only [hS6, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with e | e | e | e | e | e
    · exact absurd (by rw [e]; simp) hB2
    · exact absurd (by rw [e]; exact hzc δ₁ hδ₁D) hB2
    ·
      refine commute_of_pow_commute (n := 2) (by simpa using hcop 1) ?_
      have h2 : h * (h * δ * h⁻¹) * h⁻¹ = δ := by rw [← hδ₁, ← hδ₂, e]
      rw [pow_two]
      calc h * h * δ = (h * (h * δ * h⁻¹) * h⁻¹) * (h * h) := by group
        _ = δ * (h * h) := by rw [h2]
    ·
      refine commute_of_pow_commute (n := 4) (by simpa using hcop 2) ?_
      have h4 : h * (h * (h * (h * δ * h⁻¹) * h⁻¹) * h⁻¹) * h⁻¹ = δ := by
        rw [← hδ₁, ← hδ₂, e, hcj δ, ← hδ₁, hcj δ₁, ← hδ₂, e, hzz]
      have hp4 : h ^ 4 = h * h * h * h := by
        rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, pow_succ, pow_succ, pow_one]
      rw [hp4]
      calc h * h * h * h * δ = (h * (h * (h * (h * δ * h⁻¹) * h⁻¹) * h⁻¹) * h⁻¹) * (h * h * h * h) := by
            group
        _ = δ * (h * h * h * h) := by rw [h4]
    · exact absurd (by rw [e]) hB2
    · have key : δ₁ * (z * δ₁) = z * δ₁ * δ₁ := by rw [← mul_assoc, ← hzc δ₁ hδ₁D]
      exact absurd (by rw [e]; exact key.symm) hB2

omit hVr in
theorem oTwoUpper_mcOf_le_centralizer
    (hemb : ∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X)) :
    oTwoUpper (mcOf T) ≤ Subgroup.centralizer ({δ} : Set G) := by
  refine (Subgroup.closure_le _).mpr fun w hw => ?_
  refine Subgroup.mem_centralizer_iff.mpr fun h' hh' => ?_
  rw [Set.mem_singleton_iff] at hh'
  subst hh'
  exact (odd_commute_delta hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb hw.1 hw.2).symm

end Delta

end S143

end CFSG.Quasithin
