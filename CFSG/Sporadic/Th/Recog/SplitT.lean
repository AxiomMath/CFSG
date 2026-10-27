module

public import CFSG.Sporadic.Th.Recog.SplitTNative
public import CFSG.Sporadic.Th.Recog.Setting
public import CFSG.Sporadic.Th.Recog.SplitTBound
public import CFSG.GroupTheory.CentralSplitTransfer

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.GH74.QTGen4.Recog.G23 CFSG.Sporadic.Recognition.PresentedWords

open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Certificates

private theorem commutator_mul_zpow_central {X : Type*} [Group X] (a b c d : X)
    (hc : ∀ z : X, Commute c z) (hd : ∀ z : X, Commute d z) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  have hd1 : d * (c⁻¹ * a⁻¹) = (c⁻¹ * a⁻¹) * d := (hd _).eq
  have hc1 : c * b = b * c := hc b
  calc (a * c) * (b * d) * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹)
      = (a * c) * ((b * d) * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹)) := by group
    _ = (a * c) * (b * (c⁻¹ * a⁻¹) * b⁻¹) := by
          rw [show (b * d) * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹) =
            b * (d * (c⁻¹ * a⁻¹)) * (d⁻¹ * b⁻¹) by group, hd1]
          group
    _ = a * (b * c) * c⁻¹ * a⁻¹ * b⁻¹ := by
          rw [show (a * c) * (b * (c⁻¹ * a⁻¹) * b⁻¹) =
            a * (c * b) * c⁻¹ * a⁻¹ * b⁻¹ by group, hc1]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem wprod_mem_subgroup {X : Type*} [Group X] {K : Subgroup X} {n : ℕ}
    (y : Fin n → X) (hy : ∀ i, y i ∈ K) (w : List (Fin n × Bool)) : wprod y w ∈ K := by
  rw [wprod]
  exact Subgroup.list_prod_mem K (by
    intro g hg
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
    by_cases h : l.2
    · simpa [h] using hy l.1
    · simpa [h] using K.inv_mem (hy l.1))

private theorem commute_evalW_update {X : Type*} [Group X] {j : X} {v : Fin 6 → X}
    (hv : ∀ i, Commute j (v i)) (r : List (Fin 6 × Bool)) : Commute j (evalW v r) := by
  induction r with
  | nil => simp [evalW]
  | cons l r ih =>
    rw [show evalW v (l :: r) = (if l.2 then v l.1 else (v l.1)⁻¹) * evalW v r from by
      rw [evalW, lift_mk, wprod_cons, ← lift_mk, evalW]]
    have hfac : Commute j (if l.2 then v l.1 else (v l.1)⁻¹) := by
      by_cases h : l.2
      · rw [if_pos h]; exact hv l.1
      · rw [if_neg h]; exact (hv l.1).inv_right
    exact hfac.mul_right ih

private theorem commute_evalW_of_letters {X : Type*} [Group X] {j : X} {u : Fin 6 → X}
    (hu : ∀ i : Fin 5, Commute j (u (Fin.castSucc i))) {r : List (Fin 6 × Bool)}
    (hr : ∀ l ∈ r, l.1 ≠ 5) : Commute j (evalW u r) := by
  have hv : ∀ i : Fin 6, i ≠ 5 → Commute j (u i) := by
    intro i hi
    have hlt : i.val < 5 := by have := i.isLt; omega
    have hcast : Fin.castSucc ⟨i.val, hlt⟩ = i := Fin.ext rfl
    rw [← hcast]
    exact hu ⟨i.val, hlt⟩
  have hupd : ∀ i : Fin 6, Commute j (Function.update u 5 1 i) := by
    intro i
    by_cases hi : i = 5
    · subst hi; simp [Function.update]
    · rw [Function.update_of_ne hi]; exact hv i hi
  change Commute j (FreeGroup.lift u (FreeGroup.mk r))
  rw [← lift_update_of_letters u 1 r hr]
  exact commute_evalW_update hupd r

private theorem exists_fin_pow_eq_of_mem_zpowers {X : Type*} [Group X] {t x : X}
    (ht3 : t ^ 3 = 1) (hx : x ∈ Subgroup.zpowers t) : ∃ c : Fin 3, t ^ c.val = x := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hnonneg : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  refine ⟨⟨(k % 3).toNat, by omega⟩, ?_⟩
  rw [← hk, zpow_eq_zpow_emod' k ht3, ← zpow_natCast, Int.toNat_of_nonneg hnonneg]
  norm_num

private theorem inf_zpowers_eq_bot_of_not_mem {X : Type*} [Group X] {s : X} {K : Subgroup X}
    (hsp : orderOf s = 3) (hs : s ∉ K) : K ⊓ Subgroup.zpowers s = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hdvd : orderOf x ∣ 3 := by
    have := orderOf_dvd_of_mem_zpowers hx.2
    rwa [hsp] at this
  have hxord : orderOf x = 3 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers s := Subgroup.zpowers_le_of_mem hx.2
  haveI : Finite ↥(Subgroup.zpowers s) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hsp]; norm_num)
  have heq : Subgroup.zpowers x = Subgroup.zpowers s :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hsp, hxord])
  have hsmem : s ∈ Subgroup.zpowers x := by rw [heq]; exact Subgroup.mem_zpowers s
  exact hs (Subgroup.zpowers_le.mpr hx.1 hsmem)

private theorem wprod_tauPow {X : Type*} [Group X] (y : Fin 7 → X) (c : Fin 3) :
    wprod y (tauPow c) = (y 6)⁻¹ ^ c.val := by
  simp [tauPow, wprod, List.map_replicate, List.prod_replicate]

private theorem wprod_liftW {X : Type*} [Group X] (y : Fin 7 → X)
    (r : List (Fin 6 × Bool)) : wprod y (liftW r) = wprod (fun i => y (Fin.castSucc i)) r := by
  simpa [liftW] using wprod_comp_letters (Fin.castSucc : Fin 6 → Fin 7) y r

private noncomputable abbrev phi (C : ThCore G) : ↥CFSG.Sporadic.Th.Max3.M →* G where
  toFun x := (C.ψ x : G)
  map_one' := by simp
  map_mul' := by intro a b; simp

namespace SplitT

noncomputable abbrev tG (C : ThCore G) (tM : ↥CFSG.Sporadic.Th.Max3.M) : G :=
  (C.ψ tM : G)

noncomputable abbrev CT (C : ThCore G) (tM : ↥CFSG.Sporadic.Th.Max3.M) : Subgroup G :=
  Subgroup.centralizer ({tG C tM} : Set G)

noncomputable abbrev tC (C : ThCore G) (tM : ↥CFSG.Sporadic.Th.Max3.M) :
    ↥(CT C tM) :=
  ⟨tG C tM, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

end SplitT

open SplitT

private theorem phi_injective (C : ThCore G) : Function.Injective (phi C) := by
  intro a b h
  exact C.ψ.injective (Subtype.ext h)

private theorem orderOf_tG (C : ThCore G) {tM : ↥CFSG.Sporadic.Th.Max3.M}
    (htM : orderOf tM = 3) : orderOf (tG C tM) = 3 := by
  change orderOf ((C.ψ tM : G)) = 3
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, htM]

private theorem orderOf_z (C : ThCore G) : orderOf C.z = 2 := by
  have hzM : orderOf (⟨CFSG.Sporadic.Th.Max3.z, CFSG.Sporadic.Th.Max3.z_mem_M⟩ :
      ↥CFSG.Sporadic.Th.Max3.M) = 2 := by
    rw [Subgroup.orderOf_mk]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (p := 2) ?_ CFSG.Sporadic.Th.Max3.z_ne_one
    rw [pow_two]
    exact CFSG.Sporadic.Th.Max3.z_mul_self
  have hzM' : orderOf (tG C ⟨CFSG.Sporadic.Th.Max3.z, CFSG.Sporadic.Th.Max3.z_mem_M⟩) = 2 := by
    change orderOf ((C.ψ ⟨CFSG.Sporadic.Th.Max3.z, CFSG.Sporadic.Th.Max3.z_mem_M⟩ : G)) = 2
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hzM]
  obtain ⟨g, hg⟩ := C.conj (tG C ⟨CFSG.Sporadic.Th.Max3.z, CFSG.Sporadic.Th.Max3.z_mem_M⟩) hzM'
  have hord : orderOf (g * C.z * g⁻¹) = orderOf C.z := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective C.z
    simpa [MulAut.conj_apply] using this
  rw [← hord, hg, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hzM]

private theorem z_mem_CT (C : ThCore G) (tM : ↥CFSG.Sporadic.Th.Max3.M) : C.z ∈ CT C tM := by
  change C.z ∈ Subgroup.centralizer ({tG C tM} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_singleton_iff.mp (C.ψ tM).2).symm

private noncomputable abbrev zC (C : ThCore G) (tM : ↥CFSG.Sporadic.Th.Max3.M) : ↥(CT C tM) :=
  ⟨C.z, z_mem_CT C tM⟩

private theorem commute_of_map_commute (C : ThCore G) {tM : ↥CFSG.Sporadic.Th.Max3.M}
    (htM : orderOf tM = 3) (π : ↥(CT C tM) →* Ghat)
    (hker : π.ker = Subgroup.zpowers (tC C tM)) {x j : ↥(CT C tM)}
    (hj2 : (j : G) * (j : G) = 1) (hcomm : π x * π j = π j * π x) :
    (x : G) * (j : G) = (j : G) * (x : G) := by
  have ht : orderOf (tG C tM) = 3 := orderOf_tG C htM
  have hmem : x * j * x⁻¹ * j⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (by rwa [hker] at hmem)
  have hk' : (tG C tM) ^ k = (x : G) * (j : G) * (x : G)⁻¹ * (j : G)⁻¹ := by
    have h := congrArg (fun z : ↥(CT C tM) => (z : G)) hk
    simpa [tC] using h
  have hxj : (x : G) * (j : G) * (x : G)⁻¹ = (tG C tM) ^ k * (j : G) := by
    rw [hk']
    group
  have hsq : ((x : G) * (j : G) * (x : G)⁻¹) * ((x : G) * (j : G) * (x : G)⁻¹) = 1 := by
    calc ((x : G) * (j : G) * (x : G)⁻¹) * ((x : G) * (j : G) * (x : G)⁻¹)
        = (x : G) * ((j : G) * (j : G)) * (x : G)⁻¹ := by group
      _ = 1 := by rw [hj2]; group
  have hjt : Commute (j : G) (tG C tM) :=
    Subgroup.mem_centralizer_singleton_iff.mp j.2
  have hc : Commute ((tG C tM) ^ k) (j : G) := hjt.symm.zpow_left k
  have h2 : (tG C tM) ^ k * (tG C tM) ^ k = 1 := by
    have h := hsq
    rw [hxj] at h
    have heq : ((tG C tM) ^ k * (j : G)) * ((tG C tM) ^ k * (j : G)) =
        (tG C tM) ^ k * (tG C tM) ^ k := by
      calc ((tG C tM) ^ k * (j : G)) * ((tG C tM) ^ k * (j : G))
          = (tG C tM) ^ k * ((j : G) * (tG C tM) ^ k) * (j : G) := by group
        _ = (tG C tM) ^ k * ((tG C tM) ^ k * (j : G)) * (j : G) := by rw [hc.eq]
        _ = ((tG C tM) ^ k * (tG C tM) ^ k) * ((j : G) * (j : G)) := by group
        _ = (tG C tM) ^ k * (tG C tM) ^ k := by rw [hj2, mul_one]
    rw [heq] at h
    exact h
  have ht3 : (tG C tM) ^ 3 = 1 := by
    rw [← ht]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_refl (orderOf (tG C tM)))
  have h3 : ((tG C tM) ^ k) ^ 3 = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    rw [← ht]
    exact orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  have hu : (tG C tM) ^ k = 1 := by
    have h := h3
    rw [show ((tG C tM) ^ k) ^ 3 = ((tG C tM) ^ k) * ((tG C tM) ^ k) ^ 2 by group] at h
    rw [show ((tG C tM) ^ k) ^ 2 = ((tG C tM) ^ k) * ((tG C tM) ^ k) by group, h2,
      mul_one] at h
    exact h
  have hxj' : (x : G) * (j : G) * (x : G)⁻¹ = (j : G) := by rw [hxj, hu, one_mul]
  calc (x : G) * (j : G) = ((x : G) * (j : G) * (x : G)⁻¹) * (x : G) := by group
    _ = (j : G) * (x : G) := by rw [hxj']

private theorem phi_range (C : ThCore G) :
    (phi C).range = Subgroup.centralizer ({C.z} : Set G) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact (C.ψ x).2
  · intro y hy
    exact ⟨C.ψ.symm ⟨y, hy⟩, by simp [phi]⟩

private noncomputable abbrev rho {C : ThCore G} {tM : ↥CFSG.Sporadic.Th.Max3.M}
    (π : ↥(CT C tM) →* Ghat) {E : Subgroup G} (hE : E ≤ CT C tM) : ↥E →* Ghat :=
  π.comp (Subgroup.inclusion hE)

private theorem exists_decomp (C : ThCore G) {tM : ↥CFSG.Sporadic.Th.Max3.M}
    (htM : orderOf tM = 3) (D₀ : Subgroup ↥CFSG.Sporadic.Th.Max3.M)
    (hD₀inf : D₀ ⊓ Subgroup.zpowers tM = ⊥)
    (hD₀sup : D₀ ⊔ Subgroup.zpowers tM = Subgroup.centralizer {tM})
    (h7 : ¬ 7 ∣ Nat.card ↥(Subgroup.centralizer ({tM} : Set ↥CFSG.Sporadic.Th.Max3.M)))
    (π : ↥(CT C tM) →* Ghat) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers (tC C tM))
    (j : Ghat) (hj : j = π (zC C tM))
    (hcomm : ∀ x : ↥(CT C tM), π x * j = j * π x → (x : G) * C.z = C.z * (x : G)) :
    ∃ (E : Subgroup G) (hE : E ≤ CT C tM) (ρ : ↥E →* Ghat),
      E ≤ Subgroup.centralizer ({C.z} : Set G) ∧
        Function.Injective ρ ∧
        ρ.range = Subgroup.centralizer ({j} : Set Ghat) ∧
        Nat.card ↥E ∣ Nat.card ↥(Subgroup.centralizer
          ({tM} : Set ↥CFSG.Sporadic.Th.Max3.M)) ∧
        (∀ x : ↥(CT C tM), π x ∈ Subgroup.centralizer ({j} : Set Ghat) →
          ∃ e : ↥E, ∃ k : ℤ, x = Subgroup.inclusion hE e * (tC C tM) ^ k) ∧
        E = D₀.map (phi C) ∧
        (∀ x : ↥E, ρ x = π (Subgroup.inclusion hE x)) := by
  classical
  have hD₀le : D₀ ≤ Subgroup.centralizer ({tM} : Set ↥CFSG.Sporadic.Th.Max3.M) := by
    rw [← hD₀sup]
    exact le_sup_left
  let E : Subgroup G := D₀.map (phi C)
  have hE : E ≤ CT C tM := by
    rintro x ⟨d, hd, rfl⟩
    change (phi C) d ∈ Subgroup.centralizer ({tG C tM} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdcent : (d : ↥CFSG.Sporadic.Th.Max3.M) * tM =
        tM * (d : ↥CFSG.Sporadic.Th.Max3.M) :=
      (Subgroup.mem_centralizer_iff.mp (hD₀le hd) tM (Set.mem_singleton tM)).symm
    have h := congrArg (fun y => (phi C) y) hdcent
    simpa [phi, map_mul] using h
  have hE_central : E ≤ Subgroup.centralizer ({C.z} : Set G) := by
    rintro x ⟨d, hd, rfl⟩
    exact (C.ψ d).2
  have hEcard : Nat.card ↥E = Nat.card ↥D₀ :=
    Subgroup.card_map_of_injective (K := D₀) (phi_injective C)
  have hdvdE : Nat.card ↥E ∣ Nat.card ↥(Subgroup.centralizer
      ({tM} : Set ↥CFSG.Sporadic.Th.Max3.M)) := by
    rw [hEcard]
    exact Subgroup.card_dvd_of_le hD₀le
  set ρ : ↥E →* Ghat := rho π hE with hρ_def
  have hρ_apply : ∀ x : ↥E, ρ x = π (Subgroup.inclusion hE x) := by
    intro x
    rw [hρ_def]
    rfl
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxπ : π (Subgroup.inclusion hE x) = 1 := by
      have := MonoidHom.mem_ker.mp hx
      simpa [hρ_def] using this
    have hxmem : Subgroup.inclusion hE x ∈ π.ker := MonoidHom.mem_ker.mpr hxπ
    rw [hker] at hxmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
    have hkG : (tG C tM) ^ k = (x : G) := by
      have h := congrArg (fun y : ↥(CT C tM) => (y : G)) hk
      simpa [tC] using h
    obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp x.2
    have hdM : d = tM ^ k := by
      apply phi_injective C
      rw [MonoidHom.map_zpow]
      exact hdx.trans hkG.symm
    have hd_inf : d ∈ D₀ ⊓ Subgroup.zpowers tM :=
      ⟨hd, by rw [hdM]; exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩⟩
    rw [hD₀inf] at hd_inf
    have hd1 : d = 1 := Subgroup.mem_bot.mp hd_inf
    have hx1 : (x : G) = 1 := by rw [← hdx, hd1, map_one]
    exact Subtype.ext hx1
  have hρrange : ρ.range = Subgroup.centralizer ({j} : Set Ghat) := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      have hxE : (x : G) ∈ Subgroup.centralizer ({C.z} : Set G) := hE_central x.2
      have hxc : (x : G) * C.z = C.z * (x : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hxE
      have hcommCT : Commute (Subgroup.inclusion hE x) (zC C tM) := by
        apply Subtype.ext
        show (x : G) * C.z = C.z * (x : G)
        exact hxc
      have h := congrArg (fun y : ↥(CT C tM) => π y) hcommCT.eq
      simpa [map_mul, zC, hj, hρ_def] using h.symm
    · intro y hy
      obtain ⟨x, rfl⟩ := hπ y
      have hcommxj : π x * j = j * π x := by
        have h := Subgroup.mem_centralizer_iff.mp hy j (Set.mem_singleton j)
        exact h.symm
      have hxG : (x : G) * C.z = C.z * (x : G) := hcomm x hcommxj
      have hxcent : (x : G) ∈ Subgroup.centralizer ({C.z} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hxG
      have hxrange : (x : G) ∈ (phi C).range := by
        rw [phi_range]
        exact hxcent
      obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hxrange
      have hmcent : m ∈ Subgroup.centralizer ({tM} : Set ↥CFSG.Sporadic.Th.Max3.M) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply phi_injective C
        rw [map_mul, map_mul, hm]
        exact Subgroup.mem_centralizer_singleton_iff.mp x.2
      have hmsup : m ∈ D₀ ⊔ Subgroup.zpowers tM := by
        rw [hD₀sup]
        exact hmcent
      have hnorm : D₀ ≤ Subgroup.normalizer
          ((Subgroup.zpowers tM : Subgroup ↥CFSG.Sporadic.Th.Max3.M) :
            Set ↥CFSG.Sporadic.Th.Max3.M) := by
        refine hD₀le.trans ?_
        have hcent_eq : Subgroup.centralizer
            ((Subgroup.zpowers tM : Subgroup ↥CFSG.Sporadic.Th.Max3.M) :
              Set ↥CFSG.Sporadic.Th.Max3.M) =
            Subgroup.centralizer ({tM} : Set ↥CFSG.Sporadic.Th.Max3.M) := by
          rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        rw [← hcent_eq]
        exact Subgroup.centralizer_le_normalizer _
      have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right D₀
        (Subgroup.zpowers tM) hnorm
      have hmem : m ∈ ((D₀ : Set ↥CFSG.Sporadic.Th.Max3.M) *
          (Subgroup.zpowers tM : Set ↥CFSG.Sporadic.Th.Max3.M)) := by
        rw [← hcoe]
        exact hmsup
      obtain ⟨d, hd, s, hs, hds⟩ := Set.mem_mul.mp hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
      have hdCT : (phi C) d ∈ CT C tM := hE ⟨d, hd, rfl⟩
      have hsCT : (phi C) s ∈ CT C tM := by
        rw [← hk]
        change (phi C) (tM ^ k) ∈ Subgroup.centralizer ({tG C tM} : Set G)
        rw [map_zpow, Subgroup.mem_centralizer_singleton_iff]
        exact (Commute.zpow_left (Commute.refl (tG C tM)) k).eq
      have hxprod : x = (⟨(phi C) d, hdCT⟩ : ↥(CT C tM)) *
          (⟨(phi C) s, hsCT⟩ : ↥(CT C tM)) := by
        apply Subtype.ext
        rw [Subgroup.coe_mul]
        rw [← hm, ← hds, map_mul]
      have hps1 : π (⟨(phi C) s, hsCT⟩ : ↥(CT C tM)) = 1 := by
        have hts : (⟨(phi C) s, hsCT⟩ : ↥(CT C tM)) = (tC C tM) ^ k := by
          apply Subtype.ext
          change (phi C) s = (tG C tM) ^ k
          rw [← hk, map_zpow]
          rfl
        rw [hts, MonoidHom.map_zpow]
        have htC : π (tC C tM) = 1 := by
          have : tC C tM ∈ π.ker := by
            rw [hker]
            exact Subgroup.mem_zpowers (tC C tM)
          exact MonoidHom.mem_ker.mp this
        rw [htC]
        exact one_zpow k
      have hπx : π x = π (⟨(phi C) d, hdCT⟩ : ↥(CT C tM)) := by
        rw [hxprod, map_mul, hps1, mul_one]
      have hphiE : (phi C) d ∈ E := Subgroup.mem_map.mpr ⟨d, hd, rfl⟩
      refine ⟨⟨(phi C) d, hphiE⟩, ?_⟩
      show π (Subgroup.inclusion hE ⟨(phi C) d, hphiE⟩) = π x
      rw [hπx]
      have hinc : (Subgroup.inclusion hE ⟨(phi C) d, hphiE⟩ : ↥(CT C tM)) =
          ⟨(phi C) d, hdCT⟩ := Subtype.ext rfl
      rw [hinc]
  let ρ' : ↥E ≃* ↥(Subgroup.centralizer ({j} : Set Ghat)) :=
    (MulEquiv.ofBijective ρ.rangeRestrict
      ⟨fun a b h => hρinj (congrArg Subtype.val h),
        MonoidHom.rangeRestrict_surjective ρ⟩).trans
      (MulEquiv.subgroupCongr hρrange)
  have hρ'_apply : ∀ x : ↥E,
      ((ρ' x : ↥(Subgroup.centralizer ({j} : Set Ghat))) : Ghat) = ρ x := by
    intro x
    show ((ρ.rangeRestrict x : ↥ρ.range) : Ghat) = ρ x
    rfl
  have hdecomp : ∀ x : ↥(CT C tM),
      π x ∈ Subgroup.centralizer ({j} : Set Ghat) →
        ∃ e : ↥E, ∃ k : ℤ, x = Subgroup.inclusion hE e * (tC C tM) ^ k := by
    intro x hx
    let y : ↥(Subgroup.centralizer ({j} : Set Ghat)) := ⟨π x, hx⟩
    let e : ↥E := ρ'.symm y
    have hρe : ρ e = π x := by
      have h := congrArg (fun z : ↥(Subgroup.centralizer ({j} : Set Ghat)) => (z : Ghat))
        (MulEquiv.apply_symm_apply ρ' y)
      rwa [hρ'_apply] at h
    refine ⟨e, ?_⟩
    let c : ↥(CT C tM) := (Subgroup.inclusion hE e)⁻¹ * x
    have hc_ker : c ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      show π ((Subgroup.inclusion hE e)⁻¹ * x) = 1
      rw [map_mul, map_inv]
      change (ρ e)⁻¹ * π x = 1
      rw [hρe, inv_mul_cancel]
    rw [hker] at hc_ker
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc_ker
    have hk' : (tC C tM) ^ k = (Subgroup.inclusion hE e)⁻¹ * x := by
      simpa [c] using hk
    exact ⟨k, by
      calc x = Subgroup.inclusion hE e * ((Subgroup.inclusion hE e)⁻¹ * x) := by group
        _ = Subgroup.inclusion hE e * (tC C tM) ^ k := by rw [← hk']⟩
  exact ⟨E, hE, ρ, hE_central, hρinj, hρrange, hdvdE, hdecomp, rfl, hρ_apply⟩

end Certificates

open SplitT

private theorem centralizer_split_of_hom_aux
    (C : ThCore G) (tM : ↥CFSG.Sporadic.Th.Max3.M) (htM : orderOf tM = 3)
    (hD₀ : ∃ D₀ : Subgroup ↥CFSG.Sporadic.Th.Max3.M, D₀ ⊓ Subgroup.zpowers tM = ⊥ ∧
      D₀ ⊔ Subgroup.zpowers tM = Subgroup.centralizer {tM})
    (h7 : ¬ 7 ∣ Nat.card ↥(Subgroup.centralizer ({tM} : Set ↥CFSG.Sporadic.Th.Max3.M)))
    (hsimp : IsSimpleGroup Ghat) (hcard : Nat.card Ghat = 7371 * 576)
    (hinv : ∀ a b : Ghat, orderOf a = 2 → orderOf b = 2 → ∃ g, b = g * a * g⁻¹)
    (π : ↥(CT C tM) →* Ghat)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers (tC C tM)) :
    ∃ K : Subgroup G, K ≤ CT C tM ∧
      K ⊓ Subgroup.zpowers (tG C tM) = ⊥ ∧
      K ⊔ Subgroup.zpowers (tG C tM) = CT C tM ∧
      K = ⁅CT C tM, CT C tM⁆ ∧
      Nonempty (↥K ≃* Ghat) := by
  classical
  have hker' : π.ker = Subgroup.zpowers (tC C tM) := hker
  obtain ⟨D₀, hD₀inf, hD₀sup⟩ := hD₀
  have htord : orderOf (tG C tM) = 3 := orderOf_tG C htM
  have htCord : orderOf (tC C tM) = 3 := by
    rw [← Subgroup.orderOf_coe (H := CT C tM) (tC C tM)]
    exact htord
  have htC3 : (tC C tM) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (tC C tM)
    rwa [htCord] at this
  have hzord : orderOf C.z = 2 := orderOf_z C
  have hzCord : orderOf (zC C tM) = 2 := by
    rw [← Subgroup.orderOf_coe (H := CT C tM) (zC C tM)]
    exact hzord
  have hzCsq : (zC C tM) * (zC C tM) = 1 := by
    rw [← pow_two, ← hzCord]
    exact pow_orderOf_eq_one _
  have hzCsqG : (zC C tM : G) * (zC C tM : G) = 1 := by
    have := congrArg (fun y : ↥(CT C tM) => (y : G)) hzCsq
    simpa using this
  have htC_central : ∀ x : ↥(CT C tM), Commute (tC C tM) x := by
    intro x
    apply Subtype.ext
    show (tG C tM) * (x : G) = (x : G) * (tG C tM)
    exact (Subgroup.mem_centralizer_singleton_iff.mp x.2).symm
  have htC1 : π (tC C tM) = 1 := by
    have : tC C tM ∈ π.ker := by
      rw [hker']
      exact Subgroup.mem_zpowers (tC C tM)
    exact MonoidHom.mem_ker.mp this
  let j : Ghat := π (zC C tM)
  have hj2 : j ^ 2 = 1 := by
    calc j ^ 2 = (π (zC C tM)) ^ 2 := rfl
      _ = π ((zC C tM) ^ 2) := (map_pow π (zC C tM) 2).symm
      _ = 1 := by rw [pow_two, hzCsq, map_one]
  have hjne : j ≠ 1 := by
    intro h
    have hzker : zC C tM ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact h
    rw [hker'] at hzker
    have hdvd : orderOf (zC C tM) ∣ orderOf (tC C tM) :=
      orderOf_dvd_of_mem_zpowers hzker
    rw [hzCord, htCord] at hdvd
    norm_num at hdvd
  have hGhat_nonab : ¬ IsMulCommutative Ghat := by
    intro h
    haveI := h
    have hp : (Nat.card Ghat).Prime := (Group.is_simple_iff_prime_card).mp hsimp
    rw [hcard] at hp
    norm_num at hp
  have hjord : orderOf j = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (p := 2) ?_ hjne
    exact hj2
  obtain ⟨u, hu_sat, hu_gen, hu_comm, hu_pd, hu_ord⟩ :=
    exists_letters_native_split hinv j hjord
  have hu_comm' : ∀ i : Fin 6, i ≠ 5 → Commute j (u i) := by
    intro i hi
    have hlt : i.val < 5 := by have := i.isLt; omega
    have hcast : Fin.castSucc ⟨i.val, hlt⟩ = i := Fin.ext rfl
    rw [← hcast]
    exact hu_comm ⟨i.val, hlt⟩
  let mbar : Fin 3 → Ghat := ![evalW u dWord₁, evalW u dWord₂, u 5]
  let Mbar : Subgroup Ghat := Subgroup.closure (Set.range mbar)
  let Dbar : Subgroup Ghat := Subgroup.closure ({mbar 0, mbar 1} : Set Ghat)
  let mbar2 : Fin 2 → Ghat := ![mbar 0, mbar 1]
  have hpm : ∀ r ∈ g23PM, FreeGroup.lift mbar (FreeGroup.mk r) = 1 := by
    exact (g23WordsM_iff u).mp (fun r hr => hu_sat r (by simp [g23Words, hr]))
  have hDbar_le_Mbar : Dbar ≤ Mbar := by
    apply Subgroup.closure_mono
    rintro x (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  have hdbar_cent : Dbar ≤ Subgroup.centralizer ({j} : Set Ghat) := by
    change Subgroup.closure ({mbar 0, mbar 1} : Set Ghat) ≤
      Subgroup.centralizer ({j} : Set Ghat)
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · change mbar 0 ∈ Subgroup.centralizer ({j} : Set Ghat)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact commute_evalW_of_letters hu_comm dWord_letters.1
    · change mbar 1 ∈ Subgroup.centralizer ({j} : Set Ghat)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact commute_evalW_of_letters hu_comm dWord_letters.2
  have hcomm : ∀ x : ↥(CT C tM), π x * j = j * π x →
      (x : G) * C.z = C.z * (x : G) := by
    intro x hx
    exact commute_of_map_commute C htM π hker' hzCsqG hx
  obtain ⟨E, hE, ρ, hE_central, hρinj, hρrange, hdvdE, hdecomp, hEdef, hρ_apply⟩ :=
    exists_decomp C htM D₀ hD₀inf hD₀sup h7 π hπ hker' j rfl hcomm
  have hcard_cent_j : Nat.card ↥(Subgroup.centralizer ({j} : Set Ghat)) = Nat.card ↥E := by
    have hbij : Function.Bijective ρ.rangeRestrict :=
      ⟨fun a b h => hρinj (congrArg Subtype.val h),
        MonoidHom.rangeRestrict_surjective ρ⟩
    have h := Nat.card_congr (Equiv.ofBijective ρ.rangeRestrict hbij)
    rw [hρrange] at h
    exact h.symm
  have h7_dbar : ¬ 7 ∣ Nat.card ↥Dbar := by
    have hdvd : Nat.card ↥Dbar ∣ Nat.card ↥(Subgroup.centralizer ({j} : Set Ghat)) :=
      Subgroup.card_dvd_of_le hdbar_cent
    intro h
    apply h7
    have hcent : 7 ∣ Nat.card ↥(Subgroup.centralizer ({j} : Set Ghat)) :=
      dvd_trans h hdvd
    have hE : 7 ∣ Nat.card ↥E := by rwa [hcard_cent_j] at hcent
    exact dvd_trans hE hdvdE
  have h7_mbar : 7 ∣ Nat.card ↥Mbar := by
    have hxmem : FreeGroup.lift mbar (FreeGroup.mk d2mWord) ∈ Mbar := by
      rw [lift_mk]
      exact wprod_mem_subgroup mbar
        (fun i => Subgroup.subset_closure (Set.mem_range_self i)) d2mWord
    have := Subgroup.orderOf_dvd_natCard Mbar hxmem
    rwa [hu_ord] at this
  have hrel7 : Dbar.relIndex Mbar = 7 := by
    have hidx := relIndex_closure_g23PM mbar hpm
    have hmul := Subgroup.relIndex_mul_card (H := Dbar) (K := Mbar)
    rw [inf_eq_left.mpr hDbar_le_Mbar] at hmul
    have hdvd : 7 ∣ Dbar.relIndex Mbar * Nat.card ↥Dbar := by
      rw [hmul]
      exact h7_mbar
    have hdvd' : 7 ∣ Dbar.relIndex Mbar := by
      rcases ((by norm_num : Nat.Prime 7).dvd_mul).mp hdvd with h | h
      · exact h
      · exact absurd h h7_dbar
    exact le_antisymm hidx.2 (Nat.le_of_dvd hidx.1 hdvd')
  let Mhat : Subgroup ↥(CT C tM) := Mbar.comap π
  let Dhat : Subgroup ↥(CT C tM) := Dbar.comap π
  have hmapM : Subgroup.map π Mhat = Mbar :=
    Subgroup.map_comap_eq_self_of_surjective hπ Mbar
  have hmapD : Subgroup.map π Dhat = Dbar :=
    Subgroup.map_comap_eq_self_of_surjective hπ Dbar
  have hDhat_le_Mhat : Dhat ≤ Mhat := Subgroup.comap_mono hDbar_le_Mbar
  have hrel_hat : Dhat.relIndex Mhat = 7 := by
    rw [Subgroup.relIndex_comap Dbar π Mhat, hmapM, hrel7]
  have hker_le_Dhat : π.ker ≤ Dhat := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact Dbar.one_mem
  have htC_in_Dhat : tC C tM ∈ Dhat := by
    apply hker_le_Dhat
    rw [hker']
    exact Subgroup.mem_zpowers (tC C tM)
  have hDhat_comm_le : ⁅Dhat, Dhat⁆ ≤ E.subgroupOf (CT C tM) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxD : π x ∈ Dbar := Subgroup.mem_comap.mp hx
    have hyD : π y ∈ Dbar := Subgroup.mem_comap.mp hy
    obtain ⟨ex, kx, hxdec⟩ := hdecomp x (hdbar_cent hxD)
    obtain ⟨ey, ky, hydec⟩ := hdecomp y (hdbar_cent hyD)
    have hzx : ∀ w : ↥(CT C tM), Commute ((tC C tM) ^ kx) w :=
      fun w => (htC_central w).zpow_left kx
    have hzy : ∀ w : ↥(CT C tM), Commute ((tC C tM) ^ ky) w :=
      fun w => (htC_central w).zpow_left ky
    have hcommCT : ⁅x, y⁆ = ⁅(Subgroup.inclusion hE ex), (Subgroup.inclusion hE ey)⁆ := by
      rw [commutatorElement_def, commutatorElement_def, hxdec, hydec]
      exact commutator_mul_zpow_central _ _ _ _ hzx hzy
    have hmem : ⁅(Subgroup.inclusion hE ex), (Subgroup.inclusion hE ey)⁆ ∈
        E.subgroupOf (CT C tM) := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.commutator_le_self E (Subgroup.commutator_mem_commutator ex.2 ey.2)
    rw [Subgroup.mem_subgroupOf]
    rw [show ((⁅x, y⁆ : ↥(CT C tM)) : G) =
        ((⁅(Subgroup.inclusion hE ex), (Subgroup.inclusion hE ey)⁆ : ↥(CT C tM)) : G)
      from congrArg (fun z : ↥(CT C tM) => (z : G)) hcommCT]
    exact hmem
  have htC_notin_E : tC C tM ∉ E.subgroupOf (CT C tM) := by
    intro h
    have htE : tG C tM ∈ E := Subgroup.mem_subgroupOf.mp h
    rw [hEdef] at htE
    obtain ⟨d, hd, hdphi⟩ := Subgroup.mem_map.mp htE
    have hdM : d = tM := by
      apply phi_injective C
      change (phi C) d = tG C tM
      exact hdphi
    have hd_inf : d ∈ D₀ ⊓ Subgroup.zpowers tM :=
      ⟨hd, by rw [hdM]; exact Subgroup.mem_zpowers tM⟩
    rw [hD₀inf] at hd_inf
    have hd1 : d = 1 := Subgroup.mem_bot.mp hd_inf
    have ht1 : tG C tM = 1 := by
      rw [← hdphi, hd1]
      exact map_one (phi C)
    rw [ht1, orderOf_one] at htord
    omega
  have htC_notin_Dhat_comm : tC C tM ∉ ⁅Dhat, Dhat⁆ :=
    fun h => htC_notin_E (hDhat_comm_le h)
  have htC_notin_Mhat_comm : tC C tM ∉ ⁅Mhat, Mhat⁆ := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact CFSG.GroupTheory.not_mem_commutator_of_relIndex hDhat_le_Mhat
      (by rw [hrel_hat]; norm_num) htC_in_Dhat (fun x _ => htC_central x) htCord
      htC_notin_Dhat_comm
  have hcomm_inf_ker : ⁅Mhat, Mhat⁆ ⊓ π.ker = ⊥ := by
    rw [hker']
    exact inf_zpowers_eq_bot_of_not_mem htCord htC_notin_Mhat_comm
  have hmap_comm : Subgroup.map π ⁅Mhat, Mhat⁆ = Mbar := by
    rw [Subgroup.map_commutator, hmapM, commutator_closure_g23PM mbar hpm]
  have hdecomp_Mhat : ∀ x ∈ Mhat, ∃ y ∈ ⁅Mhat, Mhat⁆, ∃ k : ℤ,
      x = y * (tC C tM) ^ k := by
    intro x hx
    have hπx : π x ∈ Subgroup.map π ⁅Mhat, Mhat⁆ := by
      rw [hmap_comm]
      exact Subgroup.mem_comap.mp hx
    obtain ⟨y, hy, hyπ⟩ := Subgroup.mem_map.mp hπx
    have hmemker : x * y⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyπ, mul_inv_cancel]
    rw [hker'] at hmemker
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmemker
    refine ⟨y, hy, k, ?_⟩
    calc x = (x * y⁻¹) * y := by group
      _ = (tC C tM) ^ k * y := by rw [← hk]
      _ = y * (tC C tM) ^ k := by rw [(htC_central y).zpow_left k |>.eq]
  have hπinj_comm : Function.Injective (π.comp (⁅Mhat, Mhat⁆).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : (z : ↥(CT C tM)) ∈ ⁅Mhat, Mhat⁆ ⊓ π.ker :=
      ⟨z.2, MonoidHom.mem_ker.mp hz⟩
    rw [hcomm_inf_ker] at hz'
    exact Subtype.ext (Subgroup.mem_bot.mp hz')
  have hupd_mem : ∀ i : Fin 6,
      Function.update u 5 1 i ∈ Subgroup.centralizer ({j} : Set Ghat) := by
    intro i
    by_cases hi : i = 5
    · subst hi
      rw [Function.update_self]
      exact Subgroup.one_mem _
    · rw [Function.update_of_ne hi]
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hu_comm' i hi
  let y0 : Fin 6 → ↥(Subgroup.centralizer ({j} : Set Ghat)) :=
    fun i => ⟨Function.update u 5 1 i, hupd_mem i⟩
  let ρ' : ↥E ≃* ↥(Subgroup.centralizer ({j} : Set Ghat)) :=
    (MulEquiv.ofBijective ρ.rangeRestrict
      ⟨fun a b h => hρinj (congrArg Subtype.val h),
        MonoidHom.rangeRestrict_surjective ρ⟩).trans
      (MulEquiv.subgroupCongr hρrange)
  have hρ'_apply : ∀ x : ↥E,
      ((ρ' x : ↥(Subgroup.centralizer ({j} : Set Ghat))) : Ghat) = ρ x := by
    intro x
    show ((ρ.rangeRestrict x : ↥ρ.range) : Ghat) = ρ x
    rfl
  let w : Fin 6 → ↥E := fun i => ρ'.symm (y0 i)
  have hw_apply : ∀ i, ρ (w i) = Function.update u 5 1 i := by
    intro i
    have h := congrArg (fun z : ↥(Subgroup.centralizer ({j} : Set Ghat)) => (z : Ghat))
      (MulEquiv.apply_symm_apply ρ' (y0 i))
    rwa [hρ'_apply] at h
  have hu5_Mbar : u 5 ∈ Mbar := Subgroup.subset_closure ⟨2, rfl⟩
  have hu5_map : u 5 ∈ Subgroup.map π ⁅Mhat, Mhat⁆ := by
    rw [hmap_comm]
    exact hu5_Mbar
  obtain ⟨m', hm'comm, hm'π⟩ := Subgroup.mem_map.mp hu5_map
  let ê : Fin 6 → ↥(CT C tM) := Function.update (fun i => Subgroup.inclusion hE (w i)) 5 m'
  have hê5 : ê 5 = m' := Function.update_self _ _ _
  have hê_cast : ∀ i : Fin 6, (Fin.castSucc i : Fin 7) ≠ 6 → True := fun i _ => trivial
  have hê_lt : ∀ i : Fin 5,
      ê (Fin.castSucc i) = Subgroup.inclusion hE (w (Fin.castSucc i)) := by
    intro i
    rw [show ê (Fin.castSucc i) = Function.update
        (fun j => Subgroup.inclusion hE (w j)) 5 m' (Fin.castSucc i) from rfl,
      Function.update_of_ne]
    intro h
    have hval : (Fin.castSucc i).val = 5 := congrArg Fin.val h
    change i.val = 5 at hval
    omega
  have hπê : ∀ i, π (ê i) = u i := by
    intro i
    by_cases hi : i = 5
    · subst hi
      rw [hê5]
      exact hm'π
    · change π (Function.update (fun j => Subgroup.inclusion hE (w j)) 5 m' i) = u i
      rw [Function.update_of_ne hi]
      have h := hw_apply i
      rw [Function.update_of_ne hi] at h
      rw [← hρ_apply]
      exact h
  have hπ_eval : ∀ r : List (Fin 6 × Bool), π (evalW ê r) = evalW u r := by
    intro r
    rw [evalW, evalW, lift_mk, lift_mk, map_wprod]
    rw [show (fun i => π (ê i)) = u from funext hπê]
  have hê_eval : ∀ r : List (Fin 6 × Bool), (∀ l ∈ r, l.1 ≠ 5) →
      evalW ê r = Subgroup.inclusion hE (evalW w r) := by
    intro r hr
    change FreeGroup.lift (Function.update (fun i => Subgroup.inclusion hE (w i)) 5 m')
      (FreeGroup.mk r) = Subgroup.inclusion hE (evalW w r)
    rw [lift_update_of_letters (fun i => Subgroup.inclusion hE (w i)) m' r hr]
    change FreeGroup.lift (fun i => Subgroup.inclusion hE (w i)) (FreeGroup.mk r) =
      Subgroup.inclusion hE (FreeGroup.lift w (FreeGroup.mk r))
    rw [lift_mk, lift_mk, ← map_wprod]
  have hρ_eval_w : ∀ r, ρ (evalW w r) = evalW (Function.update u 5 1) r := by
    intro r
    change ρ (FreeGroup.lift w (FreeGroup.mk r)) =
      FreeGroup.lift (Function.update u 5 1) (FreeGroup.mk r)
    rw [lift_mk, lift_mk, map_wprod]
    rw [show (fun i => ρ (w i)) = Function.update u 5 1 from funext hw_apply]
  have hê_H : SatisfiesWords g23WordsH ê := by
    intro r hr
    have hletters := g23WordsH_letters r hr
    have hρ1 : ρ (evalW w r) = 1 := by
      rw [hρ_eval_w]
      change FreeGroup.lift (Function.update u 5 1) (FreeGroup.mk r) = 1
      rw [lift_update_of_letters u 1 r hletters]
      exact hu_sat r (by simp [g23Words, hr])
    have hw1 : evalW w r = 1 := hρinj (by rw [hρ1, map_one])
    change evalW ê r = 1
    rw [hê_eval r hletters, hw1, map_one]
  let wval : Fin 2 → ↥E := ![evalW w dWord₁, evalW w dWord₂]
  let dhat : Fin 2 → ↥(CT C tM) := ![evalW ê dWord₁, evalW ê dWord₂]
  have hρ_wval : ∀ i : Fin 2, ρ (wval i) = mbar2 i := by
    intro i
    fin_cases i
    · change ρ (evalW w dWord₁) = mbar2 (0 : Fin 2)
      rw [hρ_eval_w]
      change FreeGroup.lift (Function.update u 5 1) (FreeGroup.mk dWord₁) = mbar2 0
      rw [lift_update_of_letters u 1 dWord₁ dWord_letters.1]
      rfl
    · change ρ (evalW w dWord₂) = mbar2 (1 : Fin 2)
      rw [hρ_eval_w]
      change FreeGroup.lift (Function.update u 5 1) (FreeGroup.mk dWord₂) = mbar2 1
      rw [lift_update_of_letters u 1 dWord₂ dWord_letters.2]
      rfl
  have hê_dWord : ∀ i : Fin 2, dhat i = Subgroup.inclusion hE (wval i) := by
    intro i
    fin_cases i
    · exact hê_eval dWord₁ dWord_letters.1
    · exact hê_eval dWord₂ dWord_letters.2
  have hê_PD : ∀ r ∈ g23PD, FreeGroup.lift dhat (FreeGroup.mk r) = 1 := by
    intro r hr
    have hlift : FreeGroup.lift dhat (FreeGroup.mk r) =
        Subgroup.inclusion hE (FreeGroup.lift wval (FreeGroup.mk r)) := by
      rw [show dhat = (fun i => Subgroup.inclusion hE (wval i)) from funext hê_dWord,
        lift_mk, lift_mk, ← map_wprod]
    have hρlift : ρ (FreeGroup.lift wval (FreeGroup.mk r)) = 1 := by
      rw [lift_mk, map_wprod]
      rw [show (fun i => ρ (wval i)) = mbar2 from funext hρ_wval]
      rw [← lift_mk]
      simpa [mbar2, mbar] using hu_pd r hr
    have hw1 : FreeGroup.lift wval (FreeGroup.mk r) = 1 :=
      hρinj (by rw [hρlift, map_one])
    rw [hlift, hw1, map_one]
  have hdhat_Mhat : ∀ i : Fin 2, dhat i ∈ Mhat := by
    intro i
    rw [Subgroup.mem_comap]
    have hdhatπ : π (dhat i) = mbar2 i := by
      fin_cases i
      · change π (evalW ê dWord₁) = mbar2 (0 : Fin 2)
        rw [hπ_eval]
        rfl
      · change π (evalW ê dWord₂) = mbar2 (1 : Fin 2)
        rw [hπ_eval]
        rfl
    rw [hdhatπ]
    fin_cases i
    · exact Subgroup.subset_closure (by simp [mbar2])
    · exact Subgroup.subset_closure (by simp [mbar2])
  choose yfun hyfun kfun hkfun using fun i => hdecomp_Mhat (dhat i) (hdhat_Mhat i)
  have hdhatπ : ∀ i : Fin 2, π (dhat i) = mbar2 i := by
    intro i
    fin_cases i
    · change π (evalW ê dWord₁) = mbar2 (0 : Fin 2)
      rw [hπ_eval]
      rfl
    · change π (evalW ê dWord₂) = mbar2 (1 : Fin 2)
      rw [hπ_eval]
      rfl
  have hπyfun : ∀ i : Fin 2, π (yfun i) = mbar2 i := by
    intro i
    have h := congrArg π (hkfun i)
    rw [map_mul, MonoidHom.map_zpow, htC1] at h
    rw [one_zpow, mul_one] at h
    rw [← h, hdhatπ i]
  have hy_PD : ∀ r ∈ g23PD, FreeGroup.lift yfun (FreeGroup.mk r) = 1 := by
    intro r hr
    have hmem : FreeGroup.lift yfun (FreeGroup.mk r) ∈ ⁅Mhat, Mhat⁆ := by
      rw [lift_mk]
      exact wprod_mem_subgroup yfun hyfun r
    have hπy : π (FreeGroup.lift yfun (FreeGroup.mk r)) = 1 := by
      rw [lift_mk, map_wprod]
      rw [show (fun i => π (yfun i)) = mbar2 from funext hπyfun]
      rw [← lift_mk]
      simpa [mbar2, mbar] using hu_pd r hr
    have h1 : (⟨FreeGroup.lift yfun (FreeGroup.mk r), hmem⟩ : ↥⁅Mhat, Mhat⁆) = 1 := by
      apply hπinj_comm
      simpa using hπy
    exact congrArg Subtype.val h1
  have hdhat_comm : ∀ i : Fin 2, dhat i ∈ ⁅Mhat, Mhat⁆ := by
    intro i
    have hdk : ∀ r ∈ g23PD, FreeGroup.lift
        (fun j => yfun j * (tC C tM) ^ kfun j) (FreeGroup.mk r) = 1 := by
      intro r hr
      rw [show (fun j => yfun j * (tC C tM) ^ kfun j) = dhat from
        funext (fun j => (hkfun j).symm)]
      exact hê_PD r hr
    have hzero := g23PD_twist yfun (tC C tM) (fun j => htC_central (yfun j)) htC3
      kfun hy_PD hdk
    rw [hkfun i, hzero i, mul_one]
    exact hyfun i
  have hê_M : SatisfiesWords g23WordsM ê := by
    rw [g23WordsM_iff]
    intro r hr
    let fam : Fin 3 → ↥(CT C tM) := ![dhat 0, dhat 1, ê 5]
    have hfam_comm : ∀ i, fam i ∈ ⁅Mhat, Mhat⁆ := by
      intro i
      fin_cases i
      · exact hdhat_comm 0
      · exact hdhat_comm 1
      · change fam (2 : Fin 3) ∈ ⁅Mhat, Mhat⁆
        rw [show fam (2 : Fin 3) = ê 5 by simp [fam], hê5]
        exact hm'comm
    have hlift_mem : FreeGroup.lift fam (FreeGroup.mk r) ∈ ⁅Mhat, Mhat⁆ := by
      rw [lift_mk]
      exact wprod_mem_subgroup fam hfam_comm r
    have hπfam : π (FreeGroup.lift fam (FreeGroup.mk r)) = 1 := by
      rw [lift_mk, map_wprod]
      have hfun : (fun i => π (fam i)) = mbar := by
        funext i
        fin_cases i
        · exact hdhatπ 0
        · exact hdhatπ 1
        · change π (fam (2 : Fin 3)) = mbar (2 : Fin 3)
          rw [show fam (2 : Fin 3) = ê 5 by simp [fam], hê5, hm'π]
          rfl
      rw [hfun]
      rw [← lift_mk]
      exact hpm r hr
    have h1 : (⟨FreeGroup.lift fam (FreeGroup.mk r), hlift_mem⟩ : ↥⁅Mhat, Mhat⁆) = 1 := by
      apply hπinj_comm
      simpa using hπfam
    exact congrArg Subtype.val h1
  let cyc0 : List (Fin 6 × Bool) := g23WordsCycle.get ⟨0, by decide⟩
  let cyc1 : List (Fin 6 × Bool) := g23WordsCycle.get ⟨1, by decide⟩
  have hcyc0_mem : cyc0 ∈ g23WordsCycle := List.get_mem _ _
  have hcyc1_mem : cyc1 ∈ g23WordsCycle := List.get_mem _ _
  have hcyc0_ker : evalW ê cyc0 ∈ π.ker := by
    rw [MonoidHom.mem_ker, hπ_eval]
    exact hu_sat cyc0 (by simp [g23Words, hcyc0_mem])
  have hcyc1_ker : evalW ê cyc1 ∈ π.ker := by
    rw [MonoidHom.mem_ker, hπ_eval]
    exact hu_sat cyc1 (by simp [g23Words, hcyc1_mem])
  obtain ⟨c1, hc1⟩ := exists_fin_pow_eq_of_mem_zpowers htC3 (by rwa [hker'] at hcyc0_ker)
  obtain ⟨c2, hc2⟩ := exists_fin_pow_eq_of_mem_zpowers htC3 (by rwa [hker'] at hcyc1_ker)
  let e7 : Fin 7 → ↥(CT C tM) := Fin.snoc ê (tC C tM)
  have he7_cast : ∀ i : Fin 6, e7 (Fin.castSucc i) = ê i := by
    intro i
    change @Fin.snoc 6 (fun _ => ↥(CT C tM)) ê (tC C tM) (Fin.castSucc i) = ê i
    exact @Fin.snoc_castSucc 6 (fun _ => ↥(CT C tM)) (tC C tM) ê i
  have he7_last : e7 6 = tC C tM := by
    change @Fin.snoc 6 (fun _ => ↥(CT C tM)) ê (tC C tM) (Fin.last 6) = tC C tM
    exact @Fin.snoc_last 6 (fun _ => ↥(CT C tM)) (tC C tM) ê
  have htau3 : wprod e7 [(6, true), (6, true), (6, true)] = 1 := by
    simp only [wprod_cons, wprod_nil, if_true, mul_one]
    rw [he7_last]
    rw [show tC C tM * (tC C tM * tC C tM) = (tC C tM) ^ 3 by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
      group]
    exact htC3
  have hcommletter : ∀ i : Fin 6,
      wprod e7 [((6 : Fin 7), false), (Fin.castSucc i, false), (6, true),
        (Fin.castSucc i, true)] = 1 := by
    intro i
    simp only [wprod_cons, wprod_nil, if_true, if_false, mul_one]
    rw [he7_last, he7_cast]
    have hc : Commute ((tC C tM)⁻¹) ((ê i)⁻¹) :=
      (htC_central (ê i)).inv_left.inv_right
    calc (tC C tM)⁻¹ * ((ê i)⁻¹ * (tC C tM * ê i))
        = ((tC C tM)⁻¹ * (ê i)⁻¹) * (tC C tM * ê i) := by group
      _ = ((ê i)⁻¹ * (tC C tM)⁻¹) * (tC C tM * ê i) := by rw [hc.eq]
      _ = (ê i)⁻¹ * ê i := by group
      _ = 1 := by group
  have hliftH : ∀ r ∈ g23WordsH, wprod e7 (liftW r) = 1 := by
    intro r hr
    rw [wprod_liftW]
    rw [show (fun i => e7 (Fin.castSucc i)) = ê from funext he7_cast, ← lift_mk]
    exact hê_H r hr
  have hliftM : ∀ r ∈ g23WordsM, wprod e7 (liftW r) = 1 := by
    intro r hr
    rw [wprod_liftW]
    rw [show (fun i => e7 (Fin.castSucc i)) = ê from funext he7_cast, ← lift_mk]
    exact hê_M r hr
  have hcyc0_word : wprod e7 (liftW cyc0 ++ tauPow c1) = 1 := by
    rw [wprod_append, wprod_liftW, wprod_tauPow, he7_last]
    rw [show (fun i => e7 (Fin.castSucc i)) = ê from funext he7_cast, ← lift_mk]
    rw [show FreeGroup.lift ê (FreeGroup.mk cyc0) = (tC C tM) ^ c1.val from hc1.symm]
    rw [inv_pow, mul_inv_cancel]
  have hcyc1_word : wprod e7 (liftW cyc1 ++ tauPow c2) = 1 := by
    rw [wprod_append, wprod_liftW, wprod_tauPow, he7_last]
    rw [show (fun i => e7 (Fin.castSucc i)) = ê from funext he7_cast, ← lift_mk]
    rw [show FreeGroup.lift ê (FreeGroup.mk cyc1) = (tC C tM) ^ c2.val from hc2.symm]
    rw [inv_pow, mul_inv_cancel]
  let cc : Fin 3 × Fin 3 := (c1, c2)
  have hTc : ∀ w ∈ Tc cc, wprod e7 w = 1 := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · rcases List.mem_append.mp hw with hw | hw
          · simp only [List.mem_singleton] at hw
            subst hw
            exact htau3
          · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
            exact hcommletter i
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
          exact hliftH r hr
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
        exact hliftM r hr
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hcyc0_word
      · exact hcyc1_word
  have hcc0 : cc = (0, 0) := by
    by_contra hcc
    have hbound := card_closure_le_of_Tc cc hcc e7 hTc
    let H7 : Subgroup ↥(CT C tM) := Subgroup.closure (Set.range e7)
    have he7_mem : ∀ i, e7 i ∈ H7 := fun i => Subgroup.subset_closure ⟨i, rfl⟩
    have hmapH7 : Subgroup.map π H7 = ⊤ := by
      rw [eq_top_iff, ← hu_gen, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      refine Subgroup.mem_map.mpr ⟨e7 (Fin.castSucc i), he7_mem _, ?_⟩
      rw [he7_cast i]
      exact hπê i
    let πH : ↥H7 →* Ghat := π.comp H7.subtype
    have hπH_surj : Function.Surjective πH := by
      intro y
      have hy : y ∈ Subgroup.map π H7 := by rw [hmapH7]; trivial
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨z, hz⟩, hzy⟩
    have hkerH : πH.ker = (Subgroup.zpowers (tC C tM)).subgroupOf H7 := by
      ext z
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hz
        have hz' : (z : ↥(CT C tM)) ∈ π.ker := MonoidHom.mem_ker.mpr hz
        rwa [hker'] at hz'
      · intro hz
        have hz' : (z : ↥(CT C tM)) ∈ π.ker := by rwa [← hker'] at hz
        exact MonoidHom.mem_ker.mp hz' 
    have hkerH_card : Nat.card ↥πH.ker = 3 := by
      rw [hkerH]
      have hle : Subgroup.zpowers (tC C tM) ≤ H7 :=
        Subgroup.zpowers_le.mpr (by rw [← he7_last]; exact he7_mem 6)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers,
        htCord]
    have hrangeH_card : Nat.card ↥πH.range = Nat.card Ghat := by
      rw [MonoidHom.range_eq_top.mpr hπH_surj, Subgroup.card_top]
    have hcardH7 : Nat.card ↥H7 = 3 * Nat.card Ghat := by
      have h := Subgroup.card_ker_mul_card_range πH
      rw [hkerH_card, hrangeH_card] at h
      exact h.symm
    have hgt : 7371 * 576 < Nat.card ↥H7 := by
      rw [hcardH7, hcard]
      norm_num
    exact absurd hbound (not_le.mpr hgt)
  have hc1zero : c1 = 0 := by
    have := congrArg Prod.fst hcc0
    simpa [cc] using this
  have hc2zero : c2 = 0 := by
    have := congrArg Prod.snd hcc0
    simpa [cc] using this
  have hê_cycle : ∀ r ∈ g23WordsCycle, evalW ê r = 1 := by
    intro r hr
    have hr' : r = cyc0 ∨ r = cyc1 := by
      simpa [g23WordsCycle, cyc0, cyc1] using hr
    rcases hr' with rfl | rfl
    · rw [← hc1, hc1zero]
      norm_num
    · rw [← hc2, hc2zero]
      norm_num
  have hê_g23 : SatisfiesG23Words ê := by
    intro r hr
    have hr' : r ∈ g23WordsH ∨ r ∈ g23WordsM ∨ r ∈ g23WordsCycle := by
      simpa [g23Words, List.mem_append, or_assoc] using hr
    rcases hr' with h | h | h
    · exact hê_H r h
    · exact hê_M r h
    · exact hê_cycle r h
  let K : Subgroup G := Subgroup.closure (Set.range fun i => (ê i : G))
  have hK_le_CT : K ≤ CT C tM := by
    change Subgroup.closure (Set.range fun i => (ê i : G)) ≤ CT C tM
    rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact (ê i).2
  let gK : Fin 6 → ↥K := fun i => ⟨(ê i : G), Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hclosure_gK : Subgroup.closure (Set.range gK) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ Subgroup.closure (Set.range fun i => (ê i : G)) := x.2
    have hmem : (⟨(x : G), hx⟩ : ↥K) ∈ Subgroup.closure (Set.range gK) := by
      refine Subgroup.closure_induction (k := Set.range fun i => (ê i : G))
        (p := fun y hy => (⟨y, hy⟩ : ↥K) ∈ Subgroup.closure (Set.range gK)) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨i, rfl⟩
        exact Subgroup.subset_closure ⟨i, rfl⟩
      · exact Subgroup.one_mem _
      · intro a b ha hb ha' hb'
        exact Subgroup.mul_mem _ ha' hb'
      · intro a ha ha'
        exact Subgroup.inv_mem _ ha'
    simpa using hmem
  have hgK : SatisfiesG23Words gK := by
    intro r hr
    apply K.subtype_injective
    rw [map_one]
    rw [lift_mk, map_wprod]
    show wprod (fun i => (gK i : G)) r = 1
    rw [show (fun i => (gK i : G)) = (fun i => ((ê i : ↥(CT C tM)) : G)) from rfl]
    have hmapw : wprod (fun i => ((ê i : ↥(CT C tM)) : G)) r =
        (CT C tM).subtype (wprod ê r) :=
      (map_wprod (CT C tM).subtype ê r).symm
    rw [hmapw, ← lift_mk, hê_g23 r hr, map_one]
  have hneK : ∃ i, gK i ≠ 1 := by
    by_contra h
    push Not at h
    have hu1 : ∀ i, u i = 1 := by
      intro i
      have h1 : (ê i : G) = 1 := congrArg Subtype.val (h i)
      have h2 : ê i = 1 := Subtype.ext h1
      rw [← hπê i, h2, map_one]
    have hbot : Subgroup.closure (Set.range u) = ⊥ := by
      rw [Subgroup.closure_eq_bot_iff]
      rintro _ ⟨i, rfl⟩
      simpa using hu1 i
    rw [hu_gen] at hbot
    exact top_ne_bot hbot
  have hK_iso : Nonempty (↥K ≃* Ghat) := by
    obtain ⟨e⟩ := nonempty_mulEquiv_native_of_letters hsimp hcard u hu_sat hu_gen gK hgK hneK
    exact ⟨((MulEquiv.subgroupCongr hclosure_gK).trans Subgroup.topEquiv).symm.trans e⟩
  let Kc : Subgroup ↥(CT C tM) := K.subgroupOf (CT C tM)
  let πK : ↥Kc →* Ghat := π.comp Kc.subtype
  have hmapKc : Subgroup.map π Kc = ⊤ := by
    rw [eq_top_iff, ← hu_gen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine Subgroup.mem_map.mpr ⟨⟨(ê i : G), (ê i).2⟩, ?_, hπê i⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hπK_surj : Function.Surjective πK := by
    intro y
    have hy : y ∈ Subgroup.map π Kc := by rw [hmapKc]; trivial
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, hzy⟩
  have hcardKc : Nat.card ↥Kc = Nat.card Ghat := by
    have h1 : Nat.card ↥Kc = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le_CT).toEquiv
    have h2 : Nat.card ↥K = Nat.card Ghat := Nat.card_congr hK_iso.some.toEquiv
    rw [h1, h2]
  have hπK_inj : Function.Injective πK := by
    have hle : Nat.card ↥Kc ≤ Nat.card Ghat := by rw [hcardKc]
    exact (hπK_surj.bijective_of_nat_card_le hle).1
  have hK_inf : K ⊓ Subgroup.zpowers (tG C tM) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxCT : x ∈ CT C tM := hK_le_CT hx.1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx.2
    let xc : ↥(CT C tM) := ⟨x, hxCT⟩
    let zc : ↥Kc := ⟨xc, by rw [Subgroup.mem_subgroupOf]; exact hx.1⟩
    have hxc : xc = (tC C tM) ^ k := by
      apply Subtype.ext
      change x = (tG C tM) ^ k
      exact hk.symm
    have hπzc : πK zc = 1 := by
      change π xc = 1
      rw [hxc]
      rw [MonoidHom.map_zpow, htC1]
      exact one_zpow k
    have hone : zc = 1 := hπK_inj (by rw [hπzc, map_one])
    have hxc1 : (⟨x, hxCT⟩ : ↥(CT C tM)) = 1 := by
      have h1 : (zc : ↥(CT C tM)) = 1 := congrArg Subtype.val hone
      simpa [zc, xc] using h1
    have h2 := congrArg (fun y : ↥(CT C tM) => (y : G)) hxc1
    simpa using h2
  have hZcentral : ∀ z ∈ Subgroup.zpowers (tC C tM), ∀ w : ↥(CT C tM), Commute z w := by
    intro z hz w
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (htC_central w).zpow_left a
  have hnormKc : Kc ≤ Subgroup.normalizer
      ((Subgroup.zpowers (tC C tM) : Subgroup ↥(CT C tM)) : Set ↥(CT C tM)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hc : Commute z x := hZcentral z hz x
      rw [show x * z * x⁻¹ = z from by rw [hc.symm.eq]; group]
      exact hz
    · intro hz
      have hc : Commute (x * z * x⁻¹) x := hZcentral (x * z * x⁻¹) hz x
      have hz_eq : z = x * z * x⁻¹ := by
        calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
          _ = x⁻¹ * ((x * z * x⁻¹) * x) := by group
          _ = x⁻¹ * (x * (x * z * x⁻¹)) := by rw [hc.eq]
          _ = x * z * x⁻¹ := by group
      rwa [← hz_eq] at hz
  have hsupKc : Kc ⊔ Subgroup.zpowers (tC C tM) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨z, hz⟩ := hπK_surj (π x)
    have hz' : π (z : ↥(CT C tM)) = π x := hz
    have hp : x * (z : ↥(CT C tM))⁻¹ ∈ Subgroup.zpowers (tC C tM) := by
      have hmem : x * (z : ↥(CT C tM))⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hz', mul_inv_cancel]
      exact hker' ▸ hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hxeq : x = (tC C tM) ^ k * (z : ↥(CT C tM)) := by
      rw [hk]
      group
    rw [hxeq]
    exact (Kc ⊔ Subgroup.zpowers (tC C tM)).mul_mem
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩))
      (Subgroup.mem_sup_left z.2)
  have hmapKc' : Subgroup.map (CT C tM).subtype Kc = K := by
    change Subgroup.map (CT C tM).subtype (K.subgroupOf (CT C tM)) = K
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK_le_CT]
  have hmapZ : Subgroup.map (CT C tM).subtype (Subgroup.zpowers (tC C tM)) =
      Subgroup.zpowers (tG C tM) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hmapTopCT : Subgroup.map (CT C tM).subtype (⊤ : Subgroup ↥(CT C tM)) =
      CT C tM := by
    apply le_antisymm (Subgroup.map_subtype_le ⊤)
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hK_sup : K ⊔ Subgroup.zpowers (tG C tM) = CT C tM := by
    have h := congrArg (Subgroup.map (CT C tM).subtype) hsupKc
    rw [Subgroup.map_sup, hmapKc', hmapZ, hmapTopCT] at h
    exact h
  let eK := hK_iso.some
  haveI : IsSimpleGroup ↥K := MulEquiv.isSimpleGroup eK
  have hKcard : Nat.card ↥K = Nat.card Ghat := Nat.card_congr eK.toEquiv
  have hK_nonab : ¬ IsMulCommutative ↥K := by
    intro hK
    haveI := hK
    have hKsimple : IsSimpleGroup ↥K := MulEquiv.isSimpleGroup eK
    have hprime : (Nat.card ↥K).Prime :=
      (Group.is_simple_iff_prime_card (α := ↥K)).mp hKsimple
    rw [hKcard, hcard] at hprime
    norm_num at hprime
  have hKperfect : Group.IsPerfect ↥K := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥K) with h | h
    · exact absurd ((commutator_eq_bot_iff ↥K).mp h) hK_nonab
    · exact h
  have hKcomm_eq : ⁅K, K⁆ = K := by
    have htop : commutator ↥K = ⊤ := Group.IsPerfect.commutator_eq_top
    have h := congrArg (Subgroup.map K.subtype) htop
    rw [Subgroup.map_subtype_commutator] at h
    have hmap : Subgroup.map K.subtype (⊤ : Subgroup ↥K) = K := by
      apply le_antisymm (Subgroup.map_subtype_le ⊤)
      intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    rwa [hmap] at h
  have hK_le_comm : K ≤ ⁅CT C tM, CT C tM⁆ := by
    rw [← hKcomm_eq]
    exact Subgroup.commutator_mono hK_le_CT hK_le_CT
  have hdec : ∀ w : ↥(CT C tM), ∃ k : ↥Kc,
      ∃ z ∈ Subgroup.zpowers (tC C tM), (k : ↥(CT C tM)) * z = w := by
    intro w
    have hwtop : w ∈ Kc ⊔ Subgroup.zpowers (tC C tM) := by rw [hsupKc]; trivial
    have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right Kc
      (Subgroup.zpowers (tC C tM)) hnormKc
    have hmem : w ∈ ((Kc : Set ↥(CT C tM)) *
        (Subgroup.zpowers (tC C tM) : Set ↥(CT C tM))) := by
      rw [← hcoe]
      exact hwtop
    obtain ⟨k, hk, z, hz, hkz⟩ := Set.mem_mul.mp hmem
    exact ⟨⟨k, hk⟩, z, hz, hkz⟩
  have hcomm_le_K : ⁅CT C tM, CT C tM⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    let xc : ↥(CT C tM) := ⟨x, hx⟩
    let yc : ↥(CT C tM) := ⟨y, hy⟩
    obtain ⟨kx, zx, hzx, hxdec⟩ := hdec xc
    obtain ⟨ky, zy, hzy, hydec⟩ := hdec yc
    have hzxcent : ∀ w, Commute zx w := hZcentral zx hzx
    have hzycent : ∀ w, Commute zy w := hZcentral zy hzy
    have hcomm_eq : ⁅xc, yc⁆ = ⁅(kx : ↥(CT C tM)), (ky : ↥(CT C tM))⁆ := by
      rw [← hxdec, ← hydec]
      exact commutator_mul_zpow_central _ _ _ _ hzxcent hzycent
    have hmemKc : ⁅(kx : ↥(CT C tM)), (ky : ↥(CT C tM))⁆ ∈ Kc :=
      Subgroup.commutator_le_self Kc (Subgroup.commutator_mem_commutator kx.2 ky.2)
    have hmapmem := Subgroup.mem_map_of_mem (CT C tM).subtype hmemKc
    rw [hmapKc'] at hmapmem
    have hmem_xc : ⁅xc, yc⁆ ∈ Kc := by
      rw [hcomm_eq]
      exact hmemKc
    have hmap2 := Subgroup.mem_map_of_mem (CT C tM).subtype hmem_xc
    rw [hmapKc'] at hmap2
    simpa using hmap2
  have hK_eq_comm : K = ⁅CT C tM, CT C tM⁆ := le_antisymm hK_le_comm hcomm_le_K
  exact ⟨K, hK_le_CT, hK_inf, hK_sup, hK_eq_comm, hK_iso⟩

theorem centralizer_split_of_hom
    (C : ThCore G) (tM : ↥CFSG.Sporadic.Th.Max3.M) (htM : orderOf tM = 3)
    (hD₀ : ∃ D₀ : Subgroup ↥CFSG.Sporadic.Th.Max3.M, D₀ ⊓ Subgroup.zpowers tM = ⊥ ∧
      D₀ ⊔ Subgroup.zpowers tM = Subgroup.centralizer {tM})
    (h7 : ¬ 7 ∣ Nat.card ↥(Subgroup.centralizer ({tM} : Set ↥CFSG.Sporadic.Th.Max3.M)))
    (hsimp : IsSimpleGroup Ghat) (hcard : Nat.card Ghat = 7371 * 576)
    (hinv : ∀ a b : Ghat, orderOf a = 2 → orderOf b = 2 → ∃ g, b = g * a * g⁻¹)
    (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Ghat)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers ⟨C.ψ tM, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) :
    ∃ K : Subgroup G, K ≤ Subgroup.centralizer ({(C.ψ tM : G)} : Set G) ∧
      K ⊓ Subgroup.zpowers (C.ψ tM : G) = ⊥ ∧
      K ⊔ Subgroup.zpowers (C.ψ tM : G) = Subgroup.centralizer ({(C.ψ tM : G)} : Set G) ∧
      K = ⁅Subgroup.centralizer ({(C.ψ tM : G)} : Set G),
        Subgroup.centralizer ({(C.ψ tM : G)} : Set G)⁆ ∧
      Nonempty (↥K ≃* Ghat) := by
  exact centralizer_split_of_hom_aux C tM htM hD₀ h7 hsimp hcard hinv π hπ hker

theorem centralizer_split
    (C : ThCore G) (tM : ↥CFSG.Sporadic.Th.Max3.M) (htM : orderOf tM = 3)
    (hD₀ : ∃ D₀ : Subgroup ↥CFSG.Sporadic.Th.Max3.M, D₀ ⊓ Subgroup.zpowers tM = ⊥ ∧
      D₀ ⊔ Subgroup.zpowers tM = Subgroup.centralizer {tM})
    (h7 : ¬ 7 ∣ Nat.card ↥(Subgroup.centralizer ({tM} : Set ↥CFSG.Sporadic.Th.Max3.M)))
    (hsimp : IsSimpleGroup Ghat) (hcard : Nat.card Ghat = 7371 * 576)
    (hinv : ∀ a b : Ghat, orderOf a = 2 → orderOf b = 2 → ∃ g, b = g * a * g⁻¹)
    (hY : ∃ π' : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →*
        CFSG.GH74.QTGen4.Recog.G23.Ghat,
      Function.Surjective π' ∧ π'.ker = Subgroup.zpowers
        ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) :
    ∃ K : Subgroup G, K ≤ Subgroup.centralizer ({(C.ψ tM : G)} : Set G) ∧
      K ⊓ Subgroup.zpowers (C.ψ tM : G) = ⊥ ∧
      K ⊔ Subgroup.zpowers (C.ψ tM : G) = Subgroup.centralizer ({(C.ψ tM : G)} : Set G) ∧
      K = ⁅Subgroup.centralizer ({(C.ψ tM : G)} : Set G),
        Subgroup.centralizer ({(C.ψ tM : G)} : Set G)⁆ ∧
      Nonempty (↥K ≃* Ghat) := by
  obtain ⟨π, hπ, hker⟩ := hY
  exact centralizer_split_of_hom C tM htM hD₀ h7 hsimp hcard hinv π hπ hker

end CFSG.Sporadic.Th.Recog

end
