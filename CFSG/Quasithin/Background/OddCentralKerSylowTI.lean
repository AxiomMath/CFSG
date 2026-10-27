module

public import CFSG.GroupTheory.CommutingConjugatePair

public section

namespace CFSG.Quasithin

open CFSG.ABGLocalTools

@[expose] def SylowTwoTI (X : Type*) [Group X] : Prop :=
  ∀ P Q : Sylow 2 X, P ≠ Q → (P : Subgroup X) ⊓ (Q : Subgroup X) = ⊥

theorem eq_one_of_mul_eq_of_two_pow_of_odd {G : Type*} [Group G] {x a b : G}
    (hcomm : Commute a b) (hx : x = a * b) (hx2 : ∃ n : ℕ, orderOf x = 2 ^ n)
    (ha2 : ∃ n : ℕ, orderOf a = 2 ^ n) (hb : Odd (orderOf b)) : b = 1 := by
  obtain ⟨n, hn⟩ := hx2
  obtain ⟨m, hm⟩ := ha2
  have hcop : Nat.Coprime (orderOf a) (orderOf b) := by
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hb)
  have hord : orderOf x = orderOf a * orderOf b := by
    rw [hx]
    exact hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  have hbdvd : orderOf b ∣ 2 ^ n := by
    have h : orderOf b ∣ orderOf a * orderOf b := dvd_mul_left _ _
    rwa [← hord, hn] at h
  have hb1 : orderOf b = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hb)).symm hbdvd (dvd_refl _)
  exact orderOf_eq_one_iff.mp hb1

namespace SylowTwoTI

theorem of_central_odd_ker {E Q : Type*} [Group E] [Finite E] [Group Q] [Finite Q]
    (φ : E →* Q) (hφ : Function.Surjective φ)
    (hker_center : φ.ker ≤ Subgroup.center E) (hker_odd : Odd (Nat.card φ.ker))
    (hQ : SylowTwoTI Q) : SylowTwoTI E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkey : ∀ A B : Sylow 2 E, (A : Subgroup E).map φ = (B : Subgroup E).map φ → A = B := by
    have hle : ∀ A B : Sylow 2 E, (A : Subgroup E).map φ = (B : Subgroup E).map φ →
        (A : Subgroup E) ≤ (B : Subgroup E) := by
      intro A B hAB x hx
      have hxmap : φ x ∈ (B : Subgroup E).map φ := by
        rw [← hAB]
        exact Subgroup.mem_map_of_mem φ hx
      obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.mp hxmap
      set k : E := x * b⁻¹ with hk
      have hkker : k ∈ φ.ker := by
        rw [MonoidHom.mem_ker, hk, map_mul, map_inv, hbx]
        exact mul_inv_cancel _
      have hkcenter : k ∈ Subgroup.center E := hker_center hkker
      have hkodd : Odd (orderOf k) :=
        Odd.of_dvd_nat hker_odd (Subgroup.orderOf_dvd_natCard φ.ker hkker)
      have hcomm : Commute k b :=
        ((commute_iff_eq b k).mpr (Subgroup.mem_center_iff.mp hkcenter b)).symm
      have hx2 : ∃ n : ℕ, orderOf x = 2 ^ n := by
        obtain ⟨n, hn⟩ := A.isPGroup'.exists_orderOf_eq_pow ⟨x, hx⟩
        exact ⟨n, by simpa using hn⟩
      have hb2 : ∃ n : ℕ, orderOf b = 2 ^ n := by
        obtain ⟨n, hn⟩ := B.isPGroup'.exists_orderOf_eq_pow ⟨b, hb⟩
        exact ⟨n, by simpa using hn⟩
      have hxkb : x = b * k := by
        rw [show x = k * b from by rw [hk]; group]
        exact hcomm.eq
      have hk1 : k = 1 :=
        eq_one_of_mul_eq_of_two_pow_of_odd hcomm.symm hxkb hx2 hb2 hkodd
      have hxeq : x = b := by
        calc x = (x * b⁻¹) * b := by group
          _ = 1 * b := by rw [← hk, hk1]
          _ = b := one_mul b
      rwa [hxeq]
    intro A B hAB
    apply Sylow.ext
    exact le_antisymm (hle A B hAB) (hle B A hAB.symm)
  intro P P' hPP'
  let Pbar : Sylow 2 Q := P.mapSurjective hφ
  let P'bar : Sylow 2 Q := P'.mapSurjective hφ
  have hPbar : (Pbar : Subgroup Q) = (P : Subgroup E).map φ :=
    Sylow.coe_mapSurjective (f := φ) (hf := hφ) P
  have hP'bar : (P'bar : Subgroup Q) = (P' : Subgroup E).map φ :=
    Sylow.coe_mapSurjective (f := φ) (hf := hφ) P'
  have hne : Pbar ≠ P'bar := by
    intro h
    apply hPP'
    apply hkey P P'
    rw [← hPbar, ← hP'bar]
    exact congrArg (fun S : Sylow 2 Q => (S : Subgroup Q)) h
  have hint : (Pbar : Subgroup Q) ⊓ (P'bar : Subgroup Q) = ⊥ := hQ Pbar P'bar hne
  rw [eq_bot_iff]
  intro x hx
  have hxker : x ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    have hmem : φ x ∈ (Pbar : Subgroup Q) ⊓ (P'bar : Subgroup Q) := by
      refine ⟨?_, ?_⟩
      · rw [hPbar]
        exact Subgroup.mem_map_of_mem φ hx.1
      · rw [hP'bar]
        exact Subgroup.mem_map_of_mem φ hx.2
    rw [hint, Subgroup.mem_bot] at hmem
    exact hmem
  have hPK : (P : Subgroup E) ⊓ φ.ker = ⊥ :=
    CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd P.isPGroup' hker_odd
  have hxbot : x ∈ (⊥ : Subgroup E) := by
    rw [← hPK]
    exact ⟨hx.1, hxker⟩
  exact Subgroup.mem_bot.mp hxbot

theorem of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (hY : SylowTwoTI Y) : SylowTwoTI X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hφ : Function.Surjective e.toMonoidHom := e.surjective
  intro P Q hPQ
  rw [eq_bot_iff]
  intro x hx
  have hxmap : e x ∈ (P.mapSurjective (f := e.toMonoidHom) hφ :
      Subgroup Y) ⊓ (Q.mapSurjective (f := e.toMonoidHom) hφ : Subgroup Y) := by
    refine ⟨?_, ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hx.1
    · rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hx.2
  have hne : P.mapSurjective (f := e.toMonoidHom) hφ ≠
      Q.mapSurjective (f := e.toMonoidHom) hφ := by
    intro h
    apply hPQ
    apply Sylow.ext
    have h1 : (P.mapSurjective (f := e.toMonoidHom) hφ : Subgroup Y) =
        (P : Subgroup X).map e.toMonoidHom :=
      Sylow.coe_mapSurjective (f := e.toMonoidHom) (hf := hφ) P
    have h2 : (Q.mapSurjective (f := e.toMonoidHom) hφ : Subgroup Y) =
        (Q : Subgroup X).map e.toMonoidHom :=
      Sylow.coe_mapSurjective (f := e.toMonoidHom) (hf := hφ) Q
    have h3 : (P : Subgroup X).map e.toMonoidHom = (Q : Subgroup X).map e.toMonoidHom := by
      rw [← h1, ← h2]
      exact congrArg (fun S : Sylow 2 Y => (S : Subgroup Y)) h
    exact Subgroup.map_injective e.injective h3
  have hbot := hY _ _ hne
  rw [hbot, Subgroup.mem_bot] at hxmap
  exact e.injective (by simpa using hxmap)

theorem isSylowOf_inf_eq_bot {X : Type*} [Group X] [Finite X] (h : SylowTwoTI X)
    {P P' : Subgroup X} (hP : IsSylowOf 2 P ⊤) (hP' : IsSylowOf 2 P' ⊤) (hPP' : P ≠ P') :
    P ⊓ P' = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hP2, hPidx⟩ := isSylowOf_iff.mp hP
  obtain ⟨-, hP'2, hP'idx⟩ := isSylowOf_iff.mp hP'
  let P₀ : Sylow 2 X := hP2.toSylow (by simpa using hPidx)
  let P'₀ : Sylow 2 X := hP'2.toSylow (by simpa using hP'idx)
  have hP₀ : (P₀ : Subgroup X) = P := IsPGroup.toSylow_coe hP2 _
  have hP'₀ : (P'₀ : Subgroup X) = P' := IsPGroup.toSylow_coe hP'2 _
  have hne : P₀ ≠ P'₀ := by
    intro h'
    apply hPP'
    rw [← hP₀, ← hP'₀, h']
  have := h P₀ P'₀ hne
  rwa [hP₀, hP'₀] at this

theorem of_isSylowOf {X : Type*} [Group X] [Finite X]
    (h : ∀ P P' : Subgroup X, IsSylowOf 2 P ⊤ → IsSylowOf 2 P' ⊤ → P ≠ P' → P ⊓ P' = ⊥) :
    SylowTwoTI X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P P' hPP'
  exact h (P : Subgroup X) (P' : Subgroup X)
    (isSylowOf_iff.mpr ⟨le_top, P.isPGroup', by simpa using P.not_dvd_index⟩)
    (isSylowOf_iff.mpr ⟨le_top, P'.isPGroup', by simpa using P'.not_dvd_index⟩)
    (fun h' => hPP' (Sylow.ext h'))

theorem inf_eq_of_sylowTwoTI_quotient {A : Type*} [Group A] [Finite A]
    (N : Subgroup A) [N.Normal] (hTI : SylowTwoTI (A ⧸ N))
    {P Q : Subgroup A} (hP : IsSylowOf 2 P ⊤) (hQ : IsSylowOf 2 Q ⊤)
    (hNP : N ≤ P) (hNQ : N ≤ Q) (hPQ : P ≠ Q) : P ⊓ Q = N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : A →* A ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  obtain ⟨-, hP2, hPidx⟩ := isSylowOf_iff.mp hP
  rw [Subgroup.relIndex_top_right] at hPidx
  obtain ⟨-, hQ2, hQidx⟩ := isSylowOf_iff.mp hQ
  rw [Subgroup.relIndex_top_right] at hQidx
  let Pbar : Sylow 2 (A ⧸ N) := (hP2.map π).toSylow (by
    intro hdvd
    exact hPidx (hdvd.trans (P.index_map_dvd hπ)))
  let Qbar : Sylow 2 (A ⧸ N) := (hQ2.map π).toSylow (by
    intro hdvd
    exact hQidx (hdvd.trans (Q.index_map_dvd hπ)))
  have hPbar : (Pbar : Subgroup (A ⧸ N)) = P.map π :=
    IsPGroup.toSylow_coe (hP2.map π) _
  have hQbar : (Qbar : Subgroup (A ⧸ N)) = Q.map π :=
    IsPGroup.toSylow_coe (hQ2.map π) _
  have hne : Pbar ≠ Qbar := by
    intro h
    apply hPQ
    have hmap : P.map π = Q.map π := by
      rw [← hPbar, ← hQbar]
      exact congrArg (fun S : Sylow 2 (A ⧸ N) => (S : Subgroup (A ⧸ N))) h
    rw [← Subgroup.comap_map_eq_self (f := π) (H := P) (by rw [hker]; exact hNP),
      ← Subgroup.comap_map_eq_self (f := π) (H := Q) (by rw [hker]; exact hNQ), hmap]
  have hint : P.map π ⊓ Q.map π = ⊥ := by
    have h := hTI Pbar Qbar hne
    rwa [hPbar, hQbar] at h
  refine le_antisymm ?_ (le_inf hNP hNQ)
  intro x hx
  have hxker : x ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    have hmem : π x ∈ P.map π ⊓ Q.map π :=
      ⟨Subgroup.mem_map_of_mem π hx.1, Subgroup.mem_map_of_mem π hx.2⟩
    rw [hint, Subgroup.mem_bot] at hmem
    exact hmem
  rwa [hker] at hxker

end SylowTwoTI

end CFSG.Quasithin
