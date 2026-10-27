module

public import CFSG.Sporadic.Th.Recog.Setting

public section

namespace CFSG.Sporadic.Th.Recog

theorem odd_normal_eq_bot_of_centralizers {X : Type*} [Group X] [Finite X]
    (hcent : ∀ j : X, orderOf j = 2 →
      Nonempty (↥(Subgroup.centralizer ({j} : Set X)) ≃* DihedralGroup 4))
    {j₀ : X} (hj₀ : orderOf j₀ = 2) (N : Subgroup X) (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have hcardC : ∀ j : X, orderOf j = 2 →
      Nat.card ↥(Subgroup.centralizer ({j} : Set X)) = 8 := by
    intro j hj
    obtain ⟨e⟩ := hcent j hj
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hfix : ∀ (j : X), orderOf j = 2 → ∀ n : N,
      (n : X) * j = j * (n : X) → n = 1 := by
    intro j hj n hcomm
    have hmem : (n : X) ∈ Subgroup.centralizer ({j} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hdvd8 : orderOf (n : X) ∣ 8 := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer ({j} : Set X)) hmem
      rwa [hcardC j hj] at h
    have hdvdN : orderOf (n : X) ∣ Nat.card N :=
      Subgroup.orderOf_dvd_natCard N n.2
    have hcop : Nat.Coprime 8 (Nat.card N) := by
      have h2 : Nat.Coprime (Nat.card N) 2 := Nat.coprime_two_right.mpr hodd
      have h8 : Nat.Coprime (2 ^ 3) (Nat.card N) := h2.symm.pow_left 3
      simpa using h8
    have hd : orderOf (n : X) = 1 :=
      Nat.Coprime.eq_one_of_dvd ((hcop.coprime_dvd_right hdvdN).symm) hdvd8
    exact Subtype.ext (orderOf_eq_one_iff.mp hd)
  have hinv : ∀ j : X, orderOf j = 2 →
      ⇑(MulAut.conjNormal (H := N) j) = fun n : N => n⁻¹ := by
    intro j hj
    apply MonoidHom.FixedPointFree.coe_eq_inv_of_involutive
    · intro n hn
      apply hfix j hj n
      have h := congrArg (fun x : ↥N => (x : X)) hn
      rw [MulAut.conjNormal_apply] at h
      have h' : j * (n : X) * j⁻¹ = (n : X) := by simpa using h
      calc (n : X) * j = (j * (n : X) * j⁻¹) * j := by rw [h']
        _ = j * (n : X) := by group
    · intro n
      have hj2 : j * j = 1 := by
        rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, hj]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
      have hjinvsq : j⁻¹ * j⁻¹ = 1 := by
        rw [inv_eq_of_mul_eq_one_right hj2, hj2]
      calc j * (j * (n : X) * j⁻¹) * j⁻¹ = (j * j) * (n : X) * (j⁻¹ * j⁻¹) := by
            group
        _ = (n : X) := by rw [hj2, hjinvsq]; group
  let C₀ : Subgroup X := Subgroup.centralizer ({j₀} : Set X)
  let e := (hcent j₀ hj₀).some
  let j₀' : ↥C₀ := ⟨j₀, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hchoice : e j₀' ≠ DihedralGroup.sr (0 : ZMod 4) ∨
      e j₀' ≠ DihedralGroup.sr (1 : ZMod 4) := by
    by_contra h
    push Not at h
    have hsr : DihedralGroup.sr (0 : ZMod 4) = DihedralGroup.sr (1 : ZMod 4) :=
      h.1.symm.trans h.2
    exact absurd hsr (by decide)
  obtain ⟨j1, hj1ord, hj1ne, hj1comm⟩ : ∃ j1 : X, orderOf j1 = 2 ∧ j1 ≠ j₀ ∧
      j1 * j₀ = j₀ * j1 := by
    rcases hchoice with h0 | h1
    · refine ⟨↑(e.symm (DihedralGroup.sr (0 : ZMod 4))), ?_, ?_, ?_⟩
      · rw [Subgroup.orderOf_coe,
          ← MulEquiv.orderOf_eq e (e.symm (DihedralGroup.sr (0 : ZMod 4))),
          MulEquiv.apply_symm_apply, DihedralGroup.orderOf_sr]
      · intro hje
        apply h0
        calc e j₀' = e (e.symm (DihedralGroup.sr (0 : ZMod 4))) := by
              rw [show j₀' = e.symm (DihedralGroup.sr (0 : ZMod 4)) from
                Subtype.ext hje.symm]
          _ = DihedralGroup.sr (0 : ZMod 4) := MulEquiv.apply_symm_apply e _
      · exact Subgroup.mem_centralizer_singleton_iff.mp
          (e.symm (DihedralGroup.sr (0 : ZMod 4))).2
    · refine ⟨↑(e.symm (DihedralGroup.sr (1 : ZMod 4))), ?_, ?_, ?_⟩
      · rw [Subgroup.orderOf_coe,
          ← MulEquiv.orderOf_eq e (e.symm (DihedralGroup.sr (1 : ZMod 4))),
          MulEquiv.apply_symm_apply, DihedralGroup.orderOf_sr]
      · intro hje
        apply h1
        calc e j₀' = e (e.symm (DihedralGroup.sr (1 : ZMod 4))) := by
              rw [show j₀' = e.symm (DihedralGroup.sr (1 : ZMod 4)) from
                Subtype.ext hje.symm]
          _ = DihedralGroup.sr (1 : ZMod 4) := MulEquiv.apply_symm_apply e _
      · exact Subgroup.mem_centralizer_singleton_iff.mp
          (e.symm (DihedralGroup.sr (1 : ZMod 4))).2
  have hj0sq : j₀ * j₀ = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, hj₀]
  have hj1sq : j1 * j1 = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, hj1ord]
  let k := j₀ * j1
  have hkord : orderOf k = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      calc (j₀ * j1) * (j₀ * j1) = j₀ * (j1 * j₀) * j1 := by group
        _ = j₀ * (j₀ * j1) * j1 := by rw [hj1comm]
        _ = (j₀ * j₀) * (j1 * j1) := by group
        _ = 1 := by rw [hj0sq, hj1sq, mul_one]
    · change j₀ * j1 ≠ 1
      intro hk
      apply hj1ne
      calc j1 = j₀⁻¹ * (j₀ * j1) := by group
        _ = j₀⁻¹ := by rw [hk, mul_one]
        _ = j₀ := inv_eq_of_mul_eq_one_right hj0sq
  have hkfix : ∀ n : N, (MulAut.conjNormal (H := N) k) n = n := by
    intro n
    have h1 : (MulAut.conjNormal (H := N) j1) n = n⁻¹ :=
      congrFun (hinv j1 hj1ord) n
    have h0 : (MulAut.conjNormal (H := N) j₀) (n⁻¹) = n := by
      simpa using congrFun (hinv j₀ hj₀) (n⁻¹)
    calc (MulAut.conjNormal (H := N) k) n
        = (MulAut.conjNormal (H := N) (j₀ * j1)) n := by
          rw [show k = j₀ * j1 from rfl]
      _ = ((MulAut.conjNormal (H := N) j₀ * MulAut.conjNormal j1 : MulAut ↥N)) n := by
          rw [map_mul]
      _ = (MulAut.conjNormal (H := N) j₀) ((MulAut.conjNormal j1) n) := rfl
      _ = (MulAut.conjNormal (H := N) j₀) (n⁻¹) := by rw [h1]
      _ = n := h0
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  let nN : N := ⟨n, hn⟩
  have hcomm : (nN : X) * k = k * (nN : X) := by
    have h := congrArg (fun x : ↥N => (x : X)) (hkfix nN)
    rw [MulAut.conjNormal_apply] at h
    have h' : k * (nN : X) * k⁻¹ = (nN : X) := by simpa using h
    calc (nN : X) * k = (k * (nN : X) * k⁻¹) * k := by rw [h']
      _ = k * (nN : X) := by group
  exact congrArg Subtype.val (hfix k hkord nN hcomm)

theorem centralizer_inf_split_of_involution {G : Type} [Group G] [Finite G]
    (C : ThCore G)
    (sM : ↥CFSG.Sporadic.Th.Max3.M) (hsM : orderOf sM = 7)
    (hM7 : ∀ x : ↥CFSG.Sporadic.Th.Max3.M, orderOf x = 7 →
      ∃ D : Subgroup ↥CFSG.Sporadic.Th.Max3.M, D ⊓ Subgroup.zpowers x = ⊥ ∧
        D ⊔ Subgroup.zpowers x = Subgroup.centralizer {x} ∧ Nonempty (↥D ≃* DihedralGroup 4))
    {j : G} (hjs : Commute j (C.ψ sM : G)) (hj : orderOf j = 2) :
    ∃ D : Subgroup G, D ⊓ Subgroup.zpowers (C.ψ sM : G) = ⊥ ∧
      D ⊔ Subgroup.zpowers (C.ψ sM : G) =
        Subgroup.centralizer ({(C.ψ sM : G)} : Set G) ⊓ Subgroup.centralizer {j} ∧
      Nonempty (↥D ≃* DihedralGroup 4) := by
  let M := ↥CFSG.Sporadic.Th.Max3.M
  let H : Subgroup G := Subgroup.centralizer ({C.z} : Set G)
  let s : G := (C.ψ sM : G)
  let φ : M →* G :=
    (Subgroup.centralizer ({C.z} : Set G)).subtype.comp
      (C.ψ : M →* ↥(Subgroup.centralizer ({C.z} : Set G)))
  have hφ_inj : Function.Injective φ := by
    intro a b h
    exact C.ψ.injective (Subtype.ext h)
  have hφ_range : φ.range = H := by
    ext y
    constructor
    · rintro ⟨m, rfl⟩
      exact (C.ψ m).2
    · intro hy
      exact ⟨C.ψ.symm ⟨y, hy⟩,
        congrArg Subtype.val (C.ψ.apply_symm_apply ⟨y, hy⟩)⟩
  obtain ⟨g, hg⟩ := C.conj j hj
  let s' : G := g⁻¹ * s * g
  have hsz : s * C.z = C.z * s :=
    Subgroup.mem_centralizer_singleton_iff.mp (C.ψ sM).2
  have hgz : g * C.z = j * g := by
    calc g * C.z = (g * C.z * g⁻¹) * g := by group
      _ = j * g := by rw [hg]
  have hs'comm : s' * C.z = C.z * s' := by
    have hsj : s * j = j * s := hjs.eq.symm
    have hz_eq : C.z = g⁻¹ * j * g := by
      calc C.z = g⁻¹ * (g * C.z * g⁻¹) * g := by group
        _ = g⁻¹ * j * g := by rw [hg]
    calc s' * C.z = g⁻¹ * s * (g * C.z) := by simp [s']; group
      _ = g⁻¹ * s * (j * g) := by rw [hgz]
      _ = g⁻¹ * (s * j) * g := by group
      _ = g⁻¹ * (j * s) * g := by rw [hsj]
      _ = (g⁻¹ * j * g) * (g⁻¹ * s * g) := by group
      _ = C.z * s' := by rw [hz_eq]
  have hs'mem : s' ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr hs'comm
  let x : M := C.ψ.symm ⟨s', hs'mem⟩
  have hφx : φ x = s' := by simp [φ, x]
  have hsord : orderOf s = 7 := by
    calc orderOf s = orderOf (φ sM) := by rw [show φ sM = s from rfl]
      _ = orderOf sM := orderOf_injective φ hφ_inj sM
      _ = 7 := hsM
  have hs'ord : orderOf s' = 7 := by
    have hsem : SemiconjBy g⁻¹ s s' := by
      show g⁻¹ * s = s' * g⁻¹
      simp only [s']
      group
    rw [← hsem.orderOf_eq, hsord]
  have hxord : orderOf x = 7 := by
    rw [← orderOf_injective φ hφ_inj x, hφx]
    exact hs'ord
  obtain ⟨D₁, hD₁inf, hD₁sup, hD₁iso⟩ := hM7 x hxord
  let cg : G →* G := (MulAut.conj g).toMonoidHom
  have hcg_apply : ∀ y : G, cg y = g * y * g⁻¹ := fun y => by
    simp [cg, MulAut.conj_apply]
  have hcg_inj : Function.Injective cg := (MulAut.conj g).injective
  let φg : M →* G := cg.comp φ
  have hφg_inj : Function.Injective φg := hcg_inj.comp hφ_inj
  have hφgx : φg x = s := by
    simp [φg, hcg_apply, hφx, s']; group
  have hmap_cent : Subgroup.map φ (Subgroup.centralizer ({x} : Set M)) =
      H ⊓ Subgroup.centralizer ({s'} : Set G) := by
    apply le_antisymm
    · intro y hy
      rcases hy with ⟨m, hm, rfl⟩
      refine ⟨(C.ψ m).2, ?_⟩
      have hm' : φ m * φ x = φ x * φ m := by
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hm]
      simpa [hφx, Subgroup.mem_centralizer_singleton_iff] using hm'
    · intro y hy
      rw [Subgroup.mem_inf] at hy
      obtain ⟨hyH, hyC⟩ := hy
      obtain ⟨m, hm⟩ := C.ψ.surjective ⟨y, hyH⟩
      have hφm : φ m = y := congrArg Subtype.val hm
      have hmc : m * x = x * m := by
        apply hφ_inj
        rw [map_mul, map_mul, hφm, hφx]
        exact Subgroup.mem_centralizer_singleton_iff.mp hyC
      exact ⟨m, Subgroup.mem_centralizer_singleton_iff.mpr hmc, hφm⟩
  have hmap_conj_cent : ∀ t : G,
      Subgroup.map cg (Subgroup.centralizer ({g⁻¹ * t * g} : Set G)) =
        Subgroup.centralizer ({t} : Set G) := by
    intro t
    apply le_antisymm
    · have h := Subgroup.map_centralizer_le_centralizer_image
          ({g⁻¹ * t * g} : Set G) cg
      have hct : cg (g⁻¹ * t * g) = t := by
        rw [hcg_apply]; group
      rwa [Set.image_singleton, hct] at h
    · intro y hy
      rw [Subgroup.mem_map]
      refine ⟨g⁻¹ * y * g, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
        calc (g⁻¹ * y * g) * (g⁻¹ * t * g)
            = g⁻¹ * (y * t) * g := by group
          _ = g⁻¹ * (t * y) * g := by rw [hy]
          _ = (g⁻¹ * t * g) * (g⁻¹ * y * g) := by group
      · rw [hcg_apply]; group
  have hz_eq : C.z = g⁻¹ * j * g := by
    calc C.z = g⁻¹ * (g * C.z * g⁻¹) * g := by group
      _ = g⁻¹ * j * g := by rw [hg]
  have hmapH : Subgroup.map cg H = Subgroup.centralizer ({j} : Set G) := by
    have hH : H = Subgroup.centralizer ({g⁻¹ * j * g} : Set G) := by
      simp [H, hz_eq]
    rw [hH, hmap_conj_cent j]
  have hmapD1 : Subgroup.map φg (Subgroup.centralizer ({x} : Set M)) =
      Subgroup.centralizer ({s} : Set G) ⊓ Subgroup.centralizer ({j} : Set G) := by
    change Subgroup.map (cg.comp φ) (Subgroup.centralizer ({x} : Set M)) = _
    rw [← Subgroup.map_map, hmap_cent, Subgroup.map_inf_eq _ _ cg hcg_inj,
      hmapH, hmap_conj_cent s, inf_comm]
  refine ⟨D₁.map φg, ?_, ?_, ?_⟩
  · have h := congrArg (Subgroup.map φg) hD₁inf
    rw [Subgroup.map_inf_eq _ _ φg hφg_inj, MonoidHom.map_zpowers, hφgx,
      Subgroup.map_bot] at h
    simpa using h
  · calc D₁.map φg ⊔ Subgroup.zpowers s
        = Subgroup.map φg (D₁ ⊔ Subgroup.zpowers x) := by
          rw [Subgroup.map_sup, MonoidHom.map_zpowers, hφgx]
      _ = Subgroup.map φg (Subgroup.centralizer ({x} : Set M)) := by rw [hD₁sup]
      _ = Subgroup.centralizer ({s} : Set G) ⊓ Subgroup.centralizer ({j} : Set G) :=
          hmapD1
  · exact ⟨(Subgroup.equivMapOfInjective D₁ φg hφg_inj).symm.trans hD₁iso.some⟩

theorem quotient_centralizer_facts {G : Type} [Group G] [Finite G]
    (C : ThCore G)
    (sM : ↥CFSG.Sporadic.Th.Max3.M) (hsM : orderOf sM = 7)
    (hM7 : ∀ x : ↥CFSG.Sporadic.Th.Max3.M, orderOf x = 7 →
      ∃ D : Subgroup ↥CFSG.Sporadic.Th.Max3.M, D ⊓ Subgroup.zpowers x = ⊥ ∧
        D ⊔ Subgroup.zpowers x = Subgroup.centralizer {x} ∧ Nonempty (↥D ≃* DihedralGroup 4))
    {X : Type*} [Group X]
    (π : ↥(Subgroup.centralizer ({(C.ψ sM : G)} : Set G)) →* X)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨C.ψ sM, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) :
    (∀ j : X, orderOf j = 2 →
      Nonempty (↥(Subgroup.centralizer ({j} : Set X)) ≃* DihedralGroup 4)) ∧
    (∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥) ∧ ∃ j : X, orderOf j = 2 := by
  let M := ↥CFSG.Sporadic.Th.Max3.M
  let s : G := (C.ψ sM : G)
  let CS : Subgroup G := Subgroup.centralizer ({s} : Set G)
  let š : ↥CS := ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let φ : M →* G :=
    (Subgroup.centralizer ({C.z} : Set G)).subtype.comp
      (C.ψ : M →* ↥(Subgroup.centralizer ({C.z} : Set G)))
  have hφ_inj : Function.Injective φ := by
    intro a b h
    exact C.ψ.injective (Subtype.ext h)
  have hφsM : φ sM = s := rfl
  have hsord : orderOf s = 7 := by
    calc orderOf s = orderOf (φ sM) := by rw [hφsM]
      _ = orderOf sM := orderOf_injective φ hφ_inj sM
      _ = 7 := hsM
  have hšord : orderOf š = 7 := by
    have h := orderOf_injective CS.subtype CS.subtype_injective š
    rw [show CS.subtype š = s from rfl, hsord] at h
    exact h.symm
  letI : Finite X := Finite.of_surjective π hπ
  have hcentral : ∀ j : X, orderOf j = 2 →
      Nonempty (↥(Subgroup.centralizer ({j} : Set X)) ≃* DihedralGroup 4) := by
    intro j hj
    have hj2 : j ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hj]
    obtain ⟨y, hy⟩ := hπ j
    have hy2ker : y ^ 2 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, hy, hj2]
    have hy2zp : y ^ 2 ∈ Subgroup.zpowers š := by
      rwa [hker] at hy2ker
    have hy2ord : orderOf (y ^ 2) ∣ 7 := by
      rw [← hšord]
      exact orderOf_dvd_of_mem_zpowers hy2zp
    have hy14 : y ^ 14 = 1 := by
      have h7 : (y ^ 2) ^ 7 = 1 := orderOf_dvd_iff_pow_eq_one.mp hy2ord
      calc y ^ 14 = (y ^ 2) ^ 7 := by
            rw [show 14 = 2 * 7 by norm_num, pow_mul]
        _ = 1 := h7
    let i : ↥CS := y ^ 7
    have hi2 : i ^ 2 = 1 := by
      change (y ^ 7) ^ 2 = 1
      rw [← pow_mul]
      norm_num
      exact hy14
    have hiπ : π i = j := by
      change π (y ^ 7) = j
      rw [map_pow, hy]
      rw [show 7 = 2 * 3 + 1 by norm_num, pow_add, pow_mul, hj2]
      simp
    have hi_ne : i ≠ 1 := by
      intro hi1
      have hj1 : j = 1 := by rw [← hiπ, hi1, map_one]
      have h1 : orderOf j = 1 := by rw [hj1]; simp
      rw [hj] at h1
      norm_num at h1
    have hiord : orderOf i = 2 := orderOf_eq_prime hi2 hi_ne
    have hstep : ∀ x : ↥CS, π x * j = j * π x → x * i = i * x := by
      intro x hx
      have hx' : π (x * i * x⁻¹ * i⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul]
        have hxinv : π x⁻¹ = (π x)⁻¹ := map_inv π x
        have hiinv : π i⁻¹ = j⁻¹ := by rw [map_inv, hiπ]
        rw [hxinv, hiinv, hiπ, hx]
        group
      have hzker : x * i * x⁻¹ * i⁻¹ ∈ π.ker := MonoidHom.mem_ker.mpr hx'
      rw [hker] at hzker
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzker
      have hconj : x * i * x⁻¹ = š ^ k * i := by
        calc x * i * x⁻¹ = (x * i * x⁻¹ * i⁻¹) * i := by group
          _ = š ^ k * i := by rw [← hk]
      have hsq : (x * i * x⁻¹) ^ 2 = 1 := by
        rw [pow_two]
        calc (x * i * x⁻¹) * (x * i * x⁻¹) = x * (i * i) * x⁻¹ := by group
          _ = x * i ^ 2 * x⁻¹ := by rw [pow_two]
          _ = 1 := by rw [hi2]; group
      have hsq' : (š ^ k * i) ^ 2 = 1 := by rw [← hconj]; exact hsq
      have hcomm_iš : Commute i š := by
        apply Subtype.ext
        simpa using Subgroup.mem_centralizer_singleton_iff.mp i.2
      have hcommk : Commute (š ^ k) i := hcomm_iš.symm.zpow_left k
      have hsq2 : (š ^ k) ^ 2 = 1 := by
        have h := hcommk.mul_pow 2
        rw [h] at hsq'
        rwa [hi2, mul_one] at hsq'
      have hdvd2 : orderOf (š ^ k) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]
        exact hsq2
      have hdvd7 : orderOf (š ^ k) ∣ 7 := by
        rw [← hšord]
        exact orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
      have hdvd1 : orderOf (š ^ k) ∣ 1 := by
        have h := Nat.dvd_gcd hdvd2 hdvd7
        norm_num at h ⊢
        exact h
      have hpow1 : š ^ k = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
      rw [hpow1, one_mul] at hconj
      calc x * i = (x * i * x⁻¹) * x := by group
        _ = i * x := by rw [hconj]
    have hstep' : ∀ x : ↥CS, x * i = i * x → π x * j = j * π x := by
      intro x hx
      have h := congrArg π hx
      rwa [map_mul, map_mul, hiπ] at h
    have hcomap : Subgroup.comap π (Subgroup.centralizer ({j} : Set X)) =
        Subgroup.centralizer ({i} : Set ↥CS) := by
      ext x
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff]
      exact ⟨hstep x, hstep' x⟩
    have hiGord : orderOf (i : G) = 2 := by
      have h := orderOf_injective CS.subtype CS.subtype_injective i
      exact h.trans hiord
    obtain ⟨D, hDinf, hDsup, hDiso⟩ := centralizer_inf_split_of_involution C sM hsM hM7
      (Subgroup.mem_centralizer_singleton_iff.mp i.2) hiGord
    have hD_le_CS : D ≤ CS := by
      have h := (le_sup_left : D ≤ D ⊔ Subgroup.zpowers (C.ψ sM : G))
      rw [hDsup] at h
      simpa [CS, s] using h.trans inf_le_left
    let Dsub : Subgroup ↥CS := D.subgroupOf CS
    have hπD_inj : Function.Injective (π.comp Dsub.subtype) := by
      intro a b hab
      have hzker : (a : ↥CS) * (b : ↥CS)⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have hab' : π (a : ↥CS) = π (b : ↥CS) := hab
        rw [hab']
        simp
      have hzD : (a * b⁻¹ : ↥CS) ∈ Dsub :=
        Dsub.mul_mem a.2 (Dsub.inv_mem b.2)
      rw [hker] at hzker
      have hzG : ((a * b⁻¹ : ↥CS) : G) ∈ Subgroup.zpowers s := by
        rw [Subgroup.mem_zpowers_iff] at hzker ⊢
        obtain ⟨k, hk⟩ := hzker
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      have hzbot : ((a * b⁻¹ : ↥CS) : G) ∈ (⊥ : Subgroup G) := by
        rw [← hDinf]
        exact ⟨Subgroup.mem_subgroupOf.mp hzD, hzG⟩
      have hz1 : (a * b⁻¹ : ↥CS) = 1 := by
        apply Subtype.ext
        simpa using hzbot
      have hab_eq : a = b := by
        simpa using (mul_eq_one_iff_eq_inv.mp hz1)
      exact hab_eq
    have hCeq : Subgroup.centralizer ({i} : Set ↥CS) =
        (D ⊔ Subgroup.zpowers s).subgroupOf CS := by
      ext x
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, hDsup,
        Subgroup.mem_inf]
      constructor
      · intro hx
        refine ⟨by simpa [CS] using x.2, ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext_iff.mp hx)
      · rintro ⟨-, hx⟩
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hx)
    have hmap_zp : Subgroup.map π ((Subgroup.zpowers s).subgroupOf CS) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro x hx
      rw [hker, Subgroup.mem_zpowers_iff]
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff] at hx
      obtain ⟨k, hk⟩ := hx
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    have hmapDsub : Subgroup.map π Dsub = Subgroup.centralizer ({j} : Set X) := by
      have hsub : (D ⊔ Subgroup.zpowers s).subgroupOf CS =
          Dsub ⊔ (Subgroup.zpowers s).subgroupOf CS := by
        change (D ⊔ Subgroup.zpowers s).subgroupOf CS =
          D.subgroupOf CS ⊔ (Subgroup.zpowers s).subgroupOf CS
        exact Subgroup.subgroupOf_sup hD_le_CS (Subgroup.zpowers_le.mpr š.2)
      calc Subgroup.map π Dsub
          = Subgroup.map π Dsub ⊔ ⊥ := (sup_bot_eq _).symm
        _ = Subgroup.map π Dsub ⊔
              Subgroup.map π ((Subgroup.zpowers s).subgroupOf CS) := by rw [hmap_zp]
        _ = Subgroup.map π (Dsub ⊔ (Subgroup.zpowers s).subgroupOf CS) := by
              rw [Subgroup.map_sup]
        _ = Subgroup.map π ((D ⊔ Subgroup.zpowers s).subgroupOf CS) := by rw [hsub]
        _ = Subgroup.map π (Subgroup.centralizer ({i} : Set ↥CS)) := by rw [hCeq]
        _ = Subgroup.map π (Subgroup.comap π
              (Subgroup.centralizer ({j} : Set X))) := by rw [hcomap]
        _ = Subgroup.centralizer ({j} : Set X) :=
              Subgroup.map_comap_eq_self_of_surjective hπ _
    have hleD : ∀ x : ↥Dsub, π (x : ↥CS) ∈ Subgroup.centralizer ({j} : Set X) := by
      intro x
      rw [← hmapDsub]
      exact Subgroup.mem_map_of_mem π x.2
    let f : ↥Dsub →* ↥(Subgroup.centralizer ({j} : Set X)) :=
      (π.comp Dsub.subtype).codRestrict _ hleD
    have hf_inj : Function.Injective f := by
      intro a b hab
      exact hπD_inj (congrArg Subtype.val hab)
    have hf_surj : Function.Surjective f := by
      intro y
      have hy : (y : X) ∈ Subgroup.map π Dsub := by
        rw [hmapDsub]
        exact y.2
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    let eDsub : ↥Dsub ≃* ↥(Subgroup.centralizer ({j} : Set X)) :=
      MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
    exact ⟨eDsub.symm.trans
      ((Subgroup.subgroupOfEquivOfLe hD_le_CS).trans hDiso.some)⟩
  have hexists : ∃ j : X, orderOf j = 2 := by
    obtain ⟨D₂, hD₂inf, hD₂sup, hD₂iso⟩ := hM7 sM hsM
    let e₂ := hD₂iso.some
    let dD : ↥D₂ := e₂.symm (DihedralGroup.sr (0 : ZMod 4))
    let d : M := dD
    have hsr2 : DihedralGroup.sr (0 : ZMod 4) * DihedralGroup.sr (0 : ZMod 4) = 1 := by
      rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, DihedralGroup.orderOf_sr]
    have hsr_ne : DihedralGroup.sr (0 : ZMod 4) ≠ 1 := by
      intro h
      have h1 : orderOf (DihedralGroup.sr (0 : ZMod 4)) = 1 := by rw [h]; simp
      rw [DihedralGroup.orderOf_sr] at h1
      norm_num at h1
    have hdD2 : dD ^ 2 = 1 := by
      rw [pow_two]
      calc dD * dD = e₂.symm (DihedralGroup.sr (0 : ZMod 4)) *
            e₂.symm (DihedralGroup.sr (0 : ZMod 4)) := rfl
        _ = e₂.symm (DihedralGroup.sr (0 : ZMod 4) *
            DihedralGroup.sr (0 : ZMod 4)) := (map_mul e₂.symm _ _).symm
        _ = e₂.symm 1 := by rw [hsr2]
        _ = 1 := map_one e₂.symm
    have hdD_ne : dD ≠ 1 := by
      intro hd1
      have h : DihedralGroup.sr (0 : ZMod 4) = 1 := by
        calc DihedralGroup.sr (0 : ZMod 4) = e₂ dD :=
              (e₂.apply_symm_apply (DihedralGroup.sr (0 : ZMod 4))).symm
          _ = e₂ 1 := by rw [hd1]
          _ = 1 := map_one e₂
      exact hsr_ne h
    have hdDord : orderOf dD = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · exact hdD2
      · exact hdD_ne
    have hdord : orderOf d = 2 :=
      (orderOf_injective D₂.subtype D₂.subtype_injective dD).trans hdDord
    have hd_mem : d ∈ D₂ := dD.2
    have hd_cent : d ∈ Subgroup.centralizer ({sM} : Set M) := by
      rw [← hD₂sup]
      exact (le_sup_left : D₂ ≤ D₂ ⊔ Subgroup.zpowers sM) hd_mem
    have hd_comm : d * sM = sM * d :=
      (Subgroup.mem_centralizer_singleton_iff (G := M) (g := sM) (k := d)).mp hd_cent
    have hdG_mem : φ d ∈ CS := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := congrArg φ hd_comm
      rw [map_mul, map_mul] at h
      simpa [hφsM] using h
    let e : ↥CS := ⟨φ d, hdG_mem⟩
    let j0 : X := π e
    have hdG_ord : orderOf (φ d) = 2 := by
      rw [orderOf_injective φ hφ_inj d, hdord]
    have heord : orderOf e = 2 := by
      have h := orderOf_injective CS.subtype CS.subtype_injective e
      rw [show CS.subtype e = φ d from rfl, hdG_ord] at h
      exact h.symm
    have he2 : e ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, heord]
    have hj0sq : j0 ^ 2 = 1 := by
      change (π e) ^ 2 = 1
      rw [← map_pow, he2, map_one]
    have hj0_ne : j0 ≠ 1 := by
      intro h1
      have heker : e ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        simpa [j0] using h1
      rw [hker] at heker
      have hdvd : orderOf e ∣ orderOf š := orderOf_dvd_of_mem_zpowers heker
      rw [heord, hšord] at hdvd
      norm_num at hdvd
    exact ⟨j0, orderOf_eq_prime hj0sq hj0_ne⟩
  obtain ⟨j0, hj0ord⟩ := hexists
  refine ⟨hcentral, ?_, ⟨j0, hj0ord⟩⟩
  intro N hN hodd
  exact odd_normal_eq_bot_of_centralizers hcentral hj0ord N hN hodd

end CFSG.Sporadic.Th.Recog
