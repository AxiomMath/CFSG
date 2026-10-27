module

public import CFSG.RankThree.PartOne.K1320.Struct

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec1322Fin CFSG.RankThree.PartOne.Sec1322
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent



set_option maxRecDepth 100000

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gp_triangle : ∀ x : Gp, x * x = 1 → x ≠ 1 → x ≠ z0 → ∀ y : Gp, y * y = 1 → x ≠ y →
    x * y = y * x → (∃ a : Gp, a * x * a⁻¹ = y) → ∀ z : Gp, z * z = 1 → x ≠ z → y ≠ z →
    x * z = z * x → y * z = z * y → (∃ a : Gp, a * x * a⁻¹ = z) →
    (∃ g : Gp, g * x * g⁻¹ = x ∧ g * y * g⁻¹ = z) ∧
      (∃ g : Gp, g * x * g⁻¹ = y ∧ g * y * g⁻¹ = z) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gp_zstar1 : ∀ a : Gp, (isT a ∨ isV' a) → ∀ b : Gp, (isT b ∨ isV' b) → (a * b) ^ 4 = 1 →
    (a * b) ^ 2 ≠ 1 → ∀ z : Gp, (isT z ∨ isV' z) → a * z = z * a → b * z = z * b → z ≠ a →
    z ≠ b → z ≠ a * b * a⁻¹ → z ≠ b * a * b⁻¹ →
    (∃ g : Gp, g * a * g⁻¹ = z) ∨ (∃ g : Gp, g * b * g⁻¹ = z) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gp_zstar2 : ∀ a : Gp, (isT' a ∨ isV' a) → ∀ b : Gp, (isT' b ∨ isV' b) → (a * b) ^ 4 = 1 →
    (a * b) ^ 2 ≠ 1 → ∀ z : Gp, (isT' z ∨ isV' z) → a * z = z * a → b * z = z * b → z ≠ a →
    z ≠ b → z ≠ a * b * a⁻¹ → z ≠ b * a * b⁻¹ →
    (∃ g : Gp, g * a * g⁻¹ = z) ∨ (∃ g : Gp, g * b * g⁻¹ = z) := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

structure Bridge (p : ℕ) (E : Subgroup G) where
  φ : Gp →* MulAut E
  inj : Function.Injective φ
  mem : ∀ g, φ g ∈ reflectionGroup p E
  surj : ∀ y ∈ reflectionGroup p E, ∃ g, φ g = y
  inv : ∀ e : E, φ z0 e = e⁻¹
  refl_iff : ∀ g, IsAutReflection p E (φ g) ↔ φ g ∈ reflectionSet p E
  shape : (∀ x, φ x ∈ reflectionSet p E ↔ isT x ∨ isV' x) ∨
    (∀ x, φ x ∈ reflectionSet p E ↔ isT' x ∨ isV' x)

theorem exists_bridge {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hcardE : Nat.card E = p ^ 3)
    (eX : reflectionGroup p E ≃* Gp) :
    Nonempty (Bridge p E) := by
  classical
  have hp := h.prime
  let φ : Gp →* MulAut E := (reflectionGroup p E).subtype.comp eX.symm.toMonoidHom
  have hφ : ∀ g, φ g = ((eX.symm g : ↥(reflectionGroup p E)) : MulAut E) := fun _ => rfl
  have hφinj : Function.Injective φ := Subtype.val_injective.comp eX.symm.injective
  have hφX : ∀ g, φ g ∈ reflectionGroup p E := fun g => (eX.symm g).2
  have hφsurj : ∀ y ∈ reflectionGroup p E, ∃ g, φ g = y := fun y hy =>
    ⟨eX ⟨y, hy⟩, by simp [hφ]⟩
  set zM : MulAut E := φ z0 with hzM
  have hzX : zM ∈ reflectionGroup p E := hφX z0
  have hz2 : zM * zM = 1 := by rw [hzM, ← map_mul, (z0_props).1, map_one]
  have hz1 : zM ≠ 1 := fun h1 => (z0_props).2.1 (hφinj (h1.trans (map_one φ).symm))
  have hcen : ∀ y ∈ reflectionGroup p E, y * zM = zM * y := by
    intro y hy
    obtain ⟨g, rfl⟩ := hφsurj y hy
    rw [hzM, ← map_mul, ← map_mul, (z0_props).2.2 g]
  have huniq : ∀ y ∈ reflectionGroup p E, y * y = 1 → y ≠ 1 →
      (∀ x ∈ reflectionGroup p E, x * y = y * x) → y = zM := by
    intro y hy hy2 hy1 hyc
    obtain ⟨g, rfl⟩ := hφsurj y hy
    have hg : g = z0 :=
      central_unique g (hφinj (by rw [map_mul, hy2, map_one]))
        (fun hg => hy1 (by rw [hg, map_one]))
        (fun γ => hφinj (by rw [map_mul, map_mul]; exact hyc (φ γ) (hφX γ)))
    rw [hg]
  have hzinv : ∀ e : E, zM e = e⁻¹ := inverts_of_central h hF13 hzX hz2 hz1 hcen huniq
  let Rset : Set Gp := {g | IsAutReflection p E (φ g)}
  let Dset : Set Gp := {g | φ g ∈ reflectionSet p E}
  have hinvφ : ∀ g : Gp, φ g⁻¹ = (φ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])
  have hconj : ∀ g x : Gp, φ (g * x * g⁻¹) = φ g * φ x * (φ g)⁻¹ := fun g x => by
    rw [map_mul, map_mul, hinvφ g]
  have hRc : ∀ g x, x ∈ Rset → g * x * g⁻¹ ∈ Rset := by
    intro g x hx
    show IsAutReflection p E (φ (g * x * g⁻¹))
    rw [hconj]
    exact isAutReflection_conj (φ g) (φ x) hx
  have hDc : ∀ g x, x ∈ Dset → g * x * g⁻¹ ∈ Dset := by
    intro g x hx
    show φ (g * x * g⁻¹) ∈ reflectionSet p E
    rw [hconj]
    obtain ⟨w, hw, hlift⟩ := exists_lift (reflectionGroup_le E (hφX g))
    rw [← hlift]
    exact conj_mem_reflectionSet hp hx hw
  have hDR : Dset ⊆ Rset := fun x hx => hx.1
  have hRi : ∀ x ∈ Rset, x * x = 1 ∧ x ≠ 1 ∧ x ≠ z0 := by
    intro x hx
    have hord : orderOf (φ x) = 2 := hx.1
    have hsq : φ x * φ x = 1 := by
      have h5 := pow_orderOf_eq_one (φ x)
      rw [hord, pow_two] at h5
      exact h5
    refine ⟨hφinj (by rw [map_mul, hsq, map_one]), ?_, ?_⟩
    · rintro rfl
      rw [map_one, orderOf_one] at hord
      omega
    · rintro rfl
      exact not_isAutReflection_of_inverts h hcardE hzinv hx
  have hdich : ∀ x : Gp, x * x = 1 → x ≠ 1 → x ≠ z0 → (x ∈ Rset ↔ z0 * x ∉ Rset) := by
    intro x hx2 hx1 hxz
    have := reflection_dichotomy h hcardE hzinv (x := φ x)
      (by rw [← map_mul, hx2, map_one]) (fun h1 => hx1 (hφinj (h1.trans (map_one φ).symm)))
      (fun h1 => hxz (hφinj h1))
    show IsAutReflection p E (φ x) ↔ ¬ IsAutReflection p E (φ (z0 * x))
    rw [map_mul]
    exact this
  have hgen : Subgroup.closure Dset = ⊤ := by
    have h1 : Subgroup.closure (((↑) : ↥(reflectionGroup p E) → MulAut E) ⁻¹'
        reflectionSet p E) = ⊤ := Subgroup.closure_closure_coe_preimage
    have h2 : Dset = eX '' (((↑) : ↥(reflectionGroup p E) → MulAut E) ⁻¹' reflectionSet p E) := by
      ext g
      constructor
      · intro hg
        exact ⟨eX.symm g, hg, by simp⟩
      · rintro ⟨x, hx, rfl⟩
        show φ (eX x) ∈ reflectionSet p E
        simpa [hφ] using hx
    have h3 := MonoidHom.map_closure eX.toMonoidHom
      (((↑) : ↥(reflectionGroup p E) → MulAut E) ⁻¹' reflectionSet p E)
    rw [h1, Subgroup.map_top_of_surjective _ eX.surjective] at h3
    rw [h2]
    exact h3.symm
  obtain ⟨hDeq, hshape, -⟩ := chain_of_reflection_set hRc hDc hDR hRi hdich hgen
  refine ⟨⟨φ, hφinj, hφX, hφsurj, hzinv, fun g => ?_, ?_⟩⟩
  · have : g ∈ Dset ↔ g ∈ Rset := by rw [hDeq]
    exact this.symm
  · rcases hshape with hs | hs
    · exact Or.inl hs
    · exact Or.inr hs



theorem apply_c_of_mem_torusImage' {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hcE : c ∈ E) {g : MulAut E} (hg : g ∈ torusImage E L) :
    g ⟨c, hcE⟩ = ⟨c, hcE⟩ := by
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hg
  have hnL : (n : G) ∈ L := Subgroup.mem_subgroupOf.mp hn
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  show (n : G) * c * (n : G)⁻¹ = c
  rw [← Sec12Three.comm_c_L h (n : G) hnL, mul_inv_cancel_right]


@[reducible, expose] def commGroupE {E : Subgroup G} (hEc : ∀ a b : ↥E, a * b = b * a) :
    CommGroup ↥E :=
  { (inferInstance : Group ↥E) with mul_comm := hEc }

theorem fixS_u {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hcard : Nat.card E = p ^ 3)
    (hZ : Subgroup.center L = ⊥) {u : MulAut E} (huL : u ∈ torusImage E L) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hcen : ∀ g ∈ torusImage E L, g * u = u * g) :
    autFixedInG E u = Subgroup.zpowers c ∧ Nat.card (autMoved E u) = p ^ 2 := by
  classical
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => h.E_elem.is_comm.comm a b
  let _inst : CommGroup ↥E := commGroupE hEc
  have hpow : ∀ x : ↥E, x ^ p = 1 := fun x =>
    Subtype.ext (by simpa using Sec12Three.pow_eq_one_of_mem_E h x.2)
  have hordc : orderOf (⟨c, hcE⟩ : ↥E) = p := by
    rw [← Subgroup.orderOf_coe]
    exact Sec12Three.orderOf_c h
  have hc1 : (⟨c, hcE⟩ : ↥E) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hordc
    exact hp.one_lt.ne hordc
  have hufix : u ⟨c, hcE⟩ = ⟨c, hcE⟩ := apply_c_of_mem_torusImage' h hcE huL
  set B₁ : Subgroup G := (Invol.fixS u).map E.subtype with hB₁
  have hB₁E : B₁ ≤ E := Subgroup.map_subtype_le _
  have hinv : torusInvariant E L B₁ := by
    intro w hw b hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hwL : w ∈ L := hw.1
    have hwN : w ∈ Subgroup.normalizer (E : Set G) := hw.2
    have hg : conjAut E w hwN ∈ torusImage E L :=
      Sec12Three.mem_torusImage_iff.2 ⟨w, hwL, hwN, rfl⟩
    have hgx : conjAut E w hwN x ∈ Invol.fixS u :=
      Invol.apply_mem_fixS_of_commute (σ := u) (hcen _ hg).symm hx
    refine ⟨_, hgx, ?_⟩
    show ((conjAut E w hwN x : E) : G) = w * (x : G) * w⁻¹
    exact Equivariance.coe_conjAut hwN x
  have hcB₁ : c ∈ B₁ := ⟨⟨c, hcE⟩, hufix, rfl⟩
  have hB₁ne : B₁ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hcB₁
    exact h.c_ne_one hcB₁
  have hB₁top : B₁ ≠ E := by
    intro heq
    apply hu1
    refine MulEquiv.ext fun e => ?_
    have : (e : G) ∈ B₁ := by rw [heq]; exact e.2
    obtain ⟨x, hx, hxe⟩ := this
    have hxe' : x = e := Subtype.ext hxe
    rw [← hxe']
    exact hx
  obtain ⟨hcls, hsplit⟩ := hF.four
  have hB₁c : B₁ = Subgroup.zpowers c := by
    rcases hcls B₁ hB₁E hinv hB₁ne hB₁top with h1 | h1
    · exact h1
    · rcases hsplit with ⟨-, hint⟩ | ⟨⟨hr11, -⟩, -⟩
      · exfalso
        have : c ∈ Subgroup.zpowers c ⊓ ⁅E, L ⊓ torusNormalizer E⁆ :=
          ⟨Subgroup.mem_zpowers c, h1 ▸ hcB₁⟩
        rw [hint, Subgroup.mem_bot] at this
        exact h.c_ne_one this
      · exfalso
        have hcenter : Nat.card (Subgroup.center L) = 5 := hr11.2.1
        rw [hZ, Subgroup.card_bot] at hcenter
        omega
  have hfixS : Invol.fixS u = Subgroup.zpowers (⟨c, hcE⟩ : ↥E) := by
    apply Subgroup.map_injective E.subtype_injective
    rw [← hB₁, hB₁c, MonoidHom.map_zpowers]
    rfl
  have hcardfix : Nat.card (Invol.fixS u) = p := by
    rw [hfixS, Nat.card_zpowers, hordc]
  refine ⟨?_, ?_⟩
  · have h1 : autFixedInG E u = (Invol.fixS u).map E.subtype := rfl
    rw [h1, hfixS, MonoidHom.map_zpowers]
    rfl
  · have hmv : autMoved E u = Invol.invS u := Invol.movedS_eq_invS hp hp2 hpow hu2
    have hcd := Invol.card_eq_mul hp hp2 hpow hu2
    rw [hcard, hcardfix] at hcd
    rw [hmv]
    have : p * Nat.card (Invol.invS u) = p * p ^ 2 := by rw [← hcd]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos this



theorem exists_zstar {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hcard : Nat.card E = p ^ 3)
    {z : MulAut E} (hz : Inverter p E z) {u : MulAut E} (huL : u ∈ torusImage E L)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (hcen : ∀ g ∈ torusImage E L, g * u = u * g)
    (hmov : Nat.card (autMoved E u) = p ^ 2) {hcE : c ∈ E}
    (hfix : autFixedInG E u = Subgroup.zpowers c) :
    ∃ zs : MulAut E, zs = z * u ∧ zs * zs = 1 ∧ IsAutReflection p E zs ∧
      zs ∈ reflectionGroup p E ∧ (∀ g ∈ torusImage E L, g * zs = zs * g) ∧
      zs ⟨c, hcE⟩ = (⟨c, hcE⟩ : ↥E)⁻¹ ∧ autMovedInG E zs = Subgroup.zpowers c ∧
      autFixedInG E zs = autMovedInG E u ∧ zs ∉ torusImage E L := by
  classical
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => h.E_elem.is_comm.comm a b
  let _inst : CommGroup ↥E := commGroupE hEc
  have hpow : ∀ x : ↥E, x ^ p = 1 := fun x =>
    Subtype.ext (by simpa using Sec12Three.pow_eq_one_of_mem_E h x.2)
  have hzz : z * z = 1 := MulEquiv.ext fun e => by
    show z (z e) = e
    rw [hz.inv, hz.inv, inv_inv]
  have hzc : ∀ g : MulAut E, g * z = z * g := fun g => MulEquiv.ext fun e => by
    show g (z e) = z (g e)
    rw [hz.inv, hz.inv, map_inv]
  have hufix : u ⟨c, hcE⟩ = ⟨c, hcE⟩ := apply_c_of_mem_torusImage' h hcE huL
  have hc1 : (⟨c, hcE⟩ : ↥E) ≠ (⟨c, hcE⟩ : ↥E)⁻¹ := by
    intro h1
    have hordc : orderOf (⟨c, hcE⟩ : ↥E) = p := by
      rw [← Subgroup.orderOf_coe]
      exact Sec12Three.orderOf_c h
    have h2 : (⟨c, hcE⟩ : ↥E) ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.2 h1
    have h3 : orderOf (⟨c, hcE⟩ : ↥E) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hordc] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)
  have huz : u ≠ z := by
    intro h1
    apply hc1
    have := congrArg (fun φ : MulAut E => φ ⟨c, hcE⟩) h1
    rw [hufix, hz.inv] at this
    exact this
  have hzu : (z * u) * (z * u) = 1 := by
    calc z * u * (z * u) = z * (u * z) * u := by group
      _ = z * (z * u) * u := by rw [hzc u]
      _ = (z * z) * (u * u) := by group
      _ = 1 := by rw [hzz, hu2, one_mul]
  have hunot : ¬ IsAutReflection p E u := by
    rintro ⟨-, hc⟩
    rw [hmov] at hc
    have : p ^ 2 = p ^ 1 := by rw [hc, pow_one]
    have := Nat.pow_right_injective hp.two_le this
    omega
  have hzurefl : IsAutReflection p E (z * u) := by
    have hd := reflection_dichotomy h hcard hz.inv hu2 hu1 huz
    by_contra hno
    exact hunot (hd.2 hno)
  have hmem : z * u ∈ reflectionGroup p E :=
    (reflectionGroup p E).mul_mem hz.mem (torusImage_le_reflectionGroup hF huL)
  have hinvzu : Invol.invS (z * u) = Invol.fixS u := by
    ext e
    show (z * u) e = e⁻¹ ↔ u e = e
    show z (u e) = e⁻¹ ↔ u e = e
    rw [hz.inv, inv_inj]
  have hfixzu : Invol.fixS (z * u) = Invol.invS u := by
    ext e
    show (z * u) e = e ↔ u e = e⁻¹
    show z (u e) = e ↔ u e = e⁻¹
    rw [hz.inv]
    exact inv_eq_iff_eq_inv
  have hmvzu : autMoved E (z * u) = Invol.invS (z * u) :=
    Invol.movedS_eq_invS hp hp2 hpow hzu
  have hmvu : autMoved E u = Invol.invS u := Invol.movedS_eq_invS hp hp2 hpow hu2
  refine ⟨z * u, rfl, hzu, hzurefl, hmem, fun g hg => ?_, ?_, ?_, ?_, ?_⟩
  · calc g * (z * u) = (g * z) * u := by group
      _ = (z * g) * u := by rw [hzc g]
      _ = z * (g * u) := by group
      _ = z * (u * g) := by rw [hcen g hg]
      _ = (z * u) * g := by group
  · show z (u ⟨c, hcE⟩) = (⟨c, hcE⟩ : ↥E)⁻¹
    rw [hufix, hz.inv]
  · have h1 : autMovedInG E (z * u) = (autMoved E (z * u)).map E.subtype := rfl
    rw [h1, hmvzu, hinvzu]
    have h2 : (Invol.fixS u).map E.subtype = autFixedInG E u := rfl
    rw [h2, hfix]
  · have h1 : autFixedInG E (z * u) = (autFixed E (z * u)).map E.subtype := rfl
    have h2 : autFixed E (z * u) = Invol.fixS (z * u) := rfl
    have h3 : autMovedInG E u = (autMoved E u).map E.subtype := rfl
    rw [h1, h2, hfixzu, h3, hmvu]
  · intro hzL
    have := apply_c_of_mem_torusImage' h hcE hzL
    apply hc1
    have h4 : (z * u) ⟨c, hcE⟩ = (⟨c, hcE⟩ : ↥E)⁻¹ := by
      show z (u ⟨c, hcE⟩) = (⟨c, hcE⟩ : ↥E)⁻¹
      rw [hufix, hz.inv]
    rw [← h4]
    exact this.symm



namespace Bridge

variable {p : ℕ} {E : Subgroup G} (B : Bridge p E)

include B

theorem refl_data {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hcard : Nat.card E = p ^ 3) {x : MulAut E} (hx : x ∈ reflectionSet p E) :
    ∃ g : Gp, B.φ g = x ∧ g * g = 1 ∧ g ≠ 1 ∧ g ≠ z0 := by
  have hXx : x ∈ reflectionGroup p E := Subgroup.subset_closure hx
  obtain ⟨g, rfl⟩ := B.surj x hXx
  have hrefl := hx.1
  have h2 : B.φ g * B.φ g = 1 := RefFacts.mul_self_eq_one hrefl
  refine ⟨g, rfl, B.inj (by rw [map_mul, h2, map_one]), ?_, ?_⟩
  · rintro rfl
    have h3 := hrefl.1
    rw [map_one, orderOf_one] at h3
    omega
  · rintro rfl
    exact not_isAutReflection_of_inverts h hcard B.inv hrefl

theorem triangle {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hcard : Nat.card E = p ^ 3) {x y s : MulAut E} (hx : x ∈ reflectionSet p E)
    (hy : y ∈ reflectionSet p E) (hs : s ∈ reflectionSet p E) (hxy : x ≠ y) (hxs : x ≠ s)
    (hys : y ≠ s) (cxy : x * y = y * x) (cxs : x * s = s * x) (cys : y * s = s * y)
    {a b : MulAut E} (ha : a ∈ reflectionGroup p E) (hb : b ∈ reflectionGroup p E)
    (hay : a * x * a⁻¹ = y) (hbs : b * x * b⁻¹ = s) :
    (∃ g ∈ reflectionGroup p E, g * x * g⁻¹ = x ∧ g * y * g⁻¹ = s) ∧
      (∃ g ∈ reflectionGroup p E, g * x * g⁻¹ = y ∧ g * y * g⁻¹ = s) := by
  obtain ⟨x', rfl, hx2, hx1, hxz⟩ := B.refl_data h hcard hx
  obtain ⟨y', rfl, hy2, -, -⟩ := B.refl_data h hcard hy
  obtain ⟨s', rfl, hs2, -, -⟩ := B.refl_data h hcard hs
  obtain ⟨a', rfl⟩ := B.surj a ha
  obtain ⟨b', rfl⟩ := B.surj b hb
  have hinv : ∀ g : Gp, B.φ g⁻¹ = (B.φ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])
  have e1 : x' ≠ y' := fun h1 => hxy (by rw [h1])
  have e2 : x' ≠ s' := fun h1 => hxs (by rw [h1])
  have e3 : y' ≠ s' := fun h1 => hys (by rw [h1])
  have c1 : x' * y' = y' * x' := B.inj (by rw [map_mul, map_mul]; exact cxy)
  have c2 : x' * s' = s' * x' := B.inj (by rw [map_mul, map_mul]; exact cxs)
  have c3 : y' * s' = s' * y' := B.inj (by rw [map_mul, map_mul]; exact cys)
  have j1 : a' * x' * a'⁻¹ = y' := B.inj (by rw [map_mul, map_mul, hinv]; exact hay)
  have j2 : b' * x' * b'⁻¹ = s' := B.inj (by rw [map_mul, map_mul, hinv]; exact hbs)
  obtain ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ :=
    gp_triangle x' hx2 hx1 hxz y' hy2 e1 c1 ⟨a', j1⟩ s' hs2 e2 e3 c2 c3 ⟨b', j2⟩
  refine ⟨⟨B.φ g₁, B.mem g₁, ?_, ?_⟩, ⟨B.φ g₂, B.mem g₂, ?_, ?_⟩⟩
  · rw [← hinv, ← map_mul, ← map_mul, hg₁.1]
  · rw [← hinv, ← map_mul, ← map_mul, hg₁.2]
  · rw [← hinv, ← map_mul, ← map_mul, hg₂.1]
  · rw [← hinv, ← map_mul, ← map_mul, hg₂.2]

theorem zstar_class {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hcard : Nat.card E = p ^ 3) {a b s : MulAut E} (ha : a ∈ reflectionSet p E)
    (hb : b ∈ reflectionSet p E) (hs : s ∈ reflectionSet p E) (hab : orderOf (a * b) = 4)
    (cas : a * s = s * a) (cbs : b * s = s * b) (hsa : s ≠ a) (hsb : s ≠ b)
    (hsaba : s ≠ a * b * a⁻¹) (hsbab : s ≠ b * a * b⁻¹) :
    (∃ g ∈ reflectionGroup p E, g * a * g⁻¹ = s) ∨
      (∃ g ∈ reflectionGroup p E, g * b * g⁻¹ = s) := by
  obtain ⟨a', rfl, -, -, -⟩ := B.refl_data h hcard ha
  obtain ⟨b', rfl, -, -, -⟩ := B.refl_data h hcard hb
  obtain ⟨s', rfl, -, -, -⟩ := B.refl_data h hcard hs
  have hinv : ∀ g : Gp, B.φ g⁻¹ = (B.φ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])
  have ho : orderOf (a' * b') = 4 := by
    rw [← orderOf_injective B.φ B.inj, map_mul]; exact hab
  have h4 : (a' * b') ^ 4 = 1 := by
    have := pow_orderOf_eq_one (a' * b')
    rwa [ho] at this
  have h2 : (a' * b') ^ 2 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [ho] at this
    omega
  have c1 : a' * s' = s' * a' := B.inj (by rw [map_mul, map_mul]; exact cas)
  have c2 : b' * s' = s' * b' := B.inj (by rw [map_mul, map_mul]; exact cbs)
  have n1 : s' ≠ a' := fun h1 => hsa (by rw [h1])
  have n2 : s' ≠ b' := fun h1 => hsb (by rw [h1])
  have n3 : s' ≠ a' * b' * a'⁻¹ := fun h1 => hsaba (by rw [h1, map_mul, map_mul, hinv])
  have n4 : s' ≠ b' * a' * b'⁻¹ := fun h1 => hsbab (by rw [h1, map_mul, map_mul, hinv])
  have key : (∃ g : Gp, g * a' * g⁻¹ = s') ∨ (∃ g : Gp, g * b' * g⁻¹ = s') := by
    rcases B.shape with hshape | hshape
    · exact gp_zstar1 a' ((hshape a').1 ha) b' ((hshape b').1 hb) h4 h2 s' ((hshape s').1 hs)
        c1 c2 n1 n2 n3 n4
    · exact gp_zstar2 a' ((hshape a').1 ha) b' ((hshape b').1 hb) h4 h2 s' ((hshape s').1 hs)
        c1 c2 n1 n2 n3 n4
  rcases key with ⟨g, hg⟩ | ⟨g, hg⟩
  · left
    refine ⟨B.φ g, B.mem g, ?_⟩
    rw [← hinv, ← map_mul, ← map_mul, hg]
  · right
    refine ⟨B.φ g, B.mem g, ?_⟩
    rw [← hinv, ← map_mul, ← map_mul, hg]

end Bridge



end CFSG.RankThree.PartOne.K1320
