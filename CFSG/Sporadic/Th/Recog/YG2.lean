module

public import CFSG.Sporadic.Th.Recog.Setting
public import CFSG.Quasithin.Recognition.G23TypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGL32
public import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG
open CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Max3

variable {G : Type} [Group G] [Finite G]


private noncomputable abbrev phi (C : ThCore G) : ↥Max3.M →* G :=
  { toFun := fun x => (C.ψ x : G)
    map_one' := by simp
    map_mul' := by intro a b; simp }

private theorem phi_apply (C : ThCore G) (x : ↥Max3.M) : phi C x = (C.ψ x : G) := rfl

private theorem phi_injective (C : ThCore G) : Function.Injective (phi C) := by
  intro a b h
  exact C.ψ.injective (Subtype.ext h)

private noncomputable abbrev tG (C : ThCore G) (tM : ↥Max3.M) : G := (C.ψ tM : G)

private noncomputable abbrev CT (C : ThCore G) (tM : ↥Max3.M) : Subgroup G :=
  Subgroup.centralizer ({tG C tM} : Set G)

private theorem tG_mem_CT (C : ThCore G) (tM : ↥Max3.M) : tG C tM ∈ CT C tM :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

private theorem orderOf_tG (C : ThCore G) {tM : ↥Max3.M} (htM : orderOf tM = 3) :
    orderOf (tG C tM) = 3 := by
  rw [tG, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, htM]

private theorem phi_sq_eq_one_of_sq_eq_one (C : ThCore G) {a : ↥Max3.M} (ha : a * a = 1) :
    phi C a * phi C a = 1 := by
  have h : C.ψ a * C.ψ a = 1 := by rw [← map_mul, ha, map_one]
  have h' := congrArg (fun z : ↥(Subgroup.centralizer ({C.z} : Set G)) => (z : G)) h
  simpa [phi] using h'

private theorem phi_mem_CT_of_commute (C : ThCore G) {tM : ↥Max3.M} {n : ↥Max3.M}
    (hn : n * tM = tM * n) : phi C n ∈ CT C tM := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := congrArg (fun z : ↥Max3.M => (C.ψ z : G)) hn
  simpa [phi, tG, map_mul] using h

private theorem phi_ne_one (C : ThCore G) {a : ↥Max3.M} (ha : a ≠ 1) : phi C a ≠ 1 := by
  intro h
  apply ha
  apply C.ψ.injective
  apply Subtype.ext
  simpa [phi] using h

private theorem mem_normalizer_of_mapsTo {A : Type*} [Group A] {H : Subgroup A} {g : A}
    [Finite ↥H] (h : ∀ a ∈ H, g * a * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set A) := by
  let c : H → H := fun a => ⟨g * (a : A) * g⁻¹, h a a.2⟩
  have hc_inj : Function.Injective c := by
    intro a b hab
    apply Subtype.ext
    have h' : g * (a : A) * g⁻¹ = g * (b : A) * g⁻¹ := congrArg (fun z : H => (z : A)) hab
    have := congrArg (fun z : A => g⁻¹ * z * g) h'
    simpa [mul_assoc] using this
  have hc_surj : Function.Surjective c := Finite.surjective_of_injective hc_inj
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact h a
  · intro ha
    obtain ⟨b, hb⟩ := hc_surj ⟨g * a * g⁻¹, ha⟩
    have hb' : (b : A) = a := by
      have h' : g * (b : A) * g⁻¹ = g * a * g⁻¹ := congrArg (fun z : H => (z : A)) hb
      have := congrArg (fun z : A => g⁻¹ * z * g) h'
      simpa [mul_assoc] using this
    rw [← hb']
    exact b.2

private theorem normalizer_smul_apply {A : Type*} [Group A] {H : Subgroup A}
    (n : ↥(Subgroup.normalizer (H : Set A))) (a : H) :
    ((n • a : H) : A) = (n : A) * (a : A) * (n : A)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe H n a

private theorem mem_normalizer_of_normalizes_E0 (C : ThCore G) {tM : ↥Max3.M}
    {E₀ : Subgroup ↥Max3.M} (hE₀t : ∀ x ∈ E₀, x * tM = tM * x)
    {Y : Type*} [Group Y] (π : CT C tM →* Y) (Ē : Subgroup Y)
    (hĒ : Ē = ((E₀.map (phi C)).subgroupOf (CT C tM)).map π) [Finite ↥Ē]
    {n : ↥Max3.M} (hn : n * tM = tM * n) (hnE : ∀ x ∈ E₀, n * x * n⁻¹ ∈ E₀)
    (hnCT : (phi C) n ∈ CT C tM) :
    π (⟨(phi C) n, hnCT⟩ : CT C tM) ∈ Subgroup.normalizer (Ē : Set Y) := by
  haveI : Finite ↥(((E₀.map (phi C)).subgroupOf (CT C tM)).map π) := hĒ ▸ ‹Finite ↥Ē›
  have hEG_le_CT : E₀.map (phi C) ≤ CT C tM := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun z : ↥Max3.M => (C.ψ z : G)) (hE₀t x hx)
    simpa [phi, tG, map_mul] using h
  rw [hĒ]
  refine mem_normalizer_of_mapsTo ?_
  intro a ha
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp ha')
  have hmem : (phi C) (n * x * n⁻¹) ∈ E₀.map (phi C) :=
    Subgroup.mem_map_of_mem (phi C) (hnE x hx)
  have hmemCT : (phi C) (n * x * n⁻¹) ∈ CT C tM := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun z : ↥Max3.M => (C.ψ z : G)) (hE₀t _ (hnE x hx))
    simpa [phi, tG, map_mul] using h
  have hEq : π (⟨(phi C) n, hnCT⟩ : CT C tM) * π a' *
      (π (⟨(phi C) n, hnCT⟩ : CT C tM))⁻¹ =
      π (⟨(phi C) (n * x * n⁻¹), hmemCT⟩ : CT C tM) := by
    rw [show a' = (⟨(phi C) x,
      hEG_le_CT (Subgroup.mem_map_of_mem (phi C) hx)⟩ : CT C tM)
      from Subtype.ext hxeq.symm]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [map_mul, map_inv, mul_assoc]
  rw [hEq]
  exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hmem)

private theorem eq_one_or_eq_of_mem_zpowers_of_sq_eq_one {A : Type*} [Group A] {z x : A}
    (hz : z * z = 1) (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  let H : Subgroup A :=
    { carrier := {1, z}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hz]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (inv_eq_of_mul_eq_one_right hz) }
  have hzH : z ∈ H := by simp [H]
  have hxH : x ∈ H := Subgroup.zpowers_le.mpr hzH hx
  simpa [H] using hxH

private theorem conj_eq_or_conj_eq_mul_of_commutator_mem_zpowers {A : Type*} [Group A]
    {z q f : A} (hz : z * z = 1) (hc : q * f * q⁻¹ * f⁻¹ ∈ Subgroup.zpowers z) :
    q * f * q⁻¹ = f ∨ q * f * q⁻¹ = z * f := by
  rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one hz hc with h | h
  · left
    have h1 : q * f * q⁻¹ * f⁻¹ = 1 := h
    calc q * f * q⁻¹ = (q * f * q⁻¹ * f⁻¹) * f := by group
      _ = 1 * f := by rw [h1]
      _ = f := one_mul f
  · right
    have h1 : q * f * q⁻¹ * f⁻¹ = z := h
    calc q * f * q⁻¹ = (q * f * q⁻¹ * f⁻¹) * f := by group
      _ = z * f := by rw [h1]

private theorem false_of_map_mul_eq_of_sq_eq_one {B Y : Type*} [Group B] [Group Y] {t : B}
    (π : ↥(Subgroup.centralizer ({t} : Set B)) →* Y)
    (hker : π.ker = Subgroup.zpowers
      ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
    (ht : orderOf t = 3)
    {e z : B} (heCT : e ∈ Subgroup.centralizer ({t} : Set B))
    (hzCT : z ∈ Subgroup.centralizer ({t} : Set B))
    (he2 : e * e = 1) (he1 : e ≠ 1)
    (h : π (⟨e * z, (Subgroup.centralizer ({t} : Set B)).mul_mem heCT hzCT⟩) =
      π ⟨z, hzCT⟩) : False := by
  have h1 : π (⟨e, heCT⟩ : ↥(Subgroup.centralizer ({t} : Set B))) = 1 := by
    have h' : π (⟨e, heCT⟩ : ↥(Subgroup.centralizer ({t} : Set B))) *
        π (⟨z, hzCT⟩ : ↥(Subgroup.centralizer ({t} : Set B))) =
        π (⟨z, hzCT⟩ : ↥(Subgroup.centralizer ({t} : Set B))) := by
      rw [← map_mul]
      exact h
    have h'' := congrArg (fun w : Y => w * (π ⟨z, hzCT⟩)⁻¹) h'
    simpa [mul_assoc] using h''
  have he_mem : (⟨e, heCT⟩ : ↥(Subgroup.centralizer ({t} : Set B))) ∈ π.ker := by
    rwa [MonoidHom.mem_ker]
  rw [hker] at he_mem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp he_mem
  have hk' : t ^ k = e := by
    have := congrArg (fun w : ↥(Subgroup.centralizer ({t} : Set B)) => (w : B)) hk
    simpa using this
  have hu : t ^ k = 1 := by
    let u := t ^ k
    have h2 : u * u = 1 := by simpa [u] using (hk'.symm ▸ he2)
    have h3 : u ^ 3 = 1 := by
      refine orderOf_dvd_iff_pow_eq_one.mp ?_
      rw [← ht]
      exact orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
    have h := h3
    rw [show u ^ 3 = u * u ^ 2 by rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ'],
      show u ^ 2 = u * u by rw [pow_two], h2, mul_one] at h
    simpa [u] using h
  exact he1 (by rw [← hk', hu])

private theorem commute_of_map_commute {B Y : Type*} [Group B] [Group Y] {t : B}
    (π : ↥(Subgroup.centralizer ({t} : Set B)) →* Y)
    (hker : π.ker = Subgroup.zpowers
      ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
    (ht : orderOf t = 3)
    {x j : ↥(Subgroup.centralizer ({t} : Set B))}
    (hj2 : (j : B) * j = 1)
    (hcomm : π x * π j = π j * π x) : (x : B) * j = j * x := by
  have hxt : (x : B) * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp x.2
  have hjt : (j : B) * t = t * j := Subgroup.mem_centralizer_singleton_iff.mp j.2
  have hmem : (x * j * x⁻¹ * j⁻¹ : ↥(Subgroup.centralizer ({t} : Set B))) ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (by rwa [hker] at hmem)
  have hk' : t ^ k = (x : B) * j * (x : B)⁻¹ * (j : B)⁻¹ := by
    have h := congrArg (fun z : ↥(Subgroup.centralizer ({t} : Set B)) => (z : B)) hk
    simpa using h
  have hxj : (x : B) * j * (x : B)⁻¹ = t ^ k * j := by
    rw [hk']
    group
  have hsq : ((x : B) * j * (x : B)⁻¹) * ((x : B) * j * (x : B)⁻¹) = 1 := by
    calc ((x : B) * j * (x : B)⁻¹) * ((x : B) * j * (x : B)⁻¹)
        = (x : B) * (j * j) * (x : B)⁻¹ := by group
      _ = 1 := by rw [hj2]; group
  have htj : Commute (j : B) t := hjt
  have hc : Commute (t ^ k) (j : B) := htj.symm.zpow_left k
  have h2 : (t ^ k) * (t ^ k) = 1 := by
    have h := hsq
    rw [hxj] at h
    have heq : (t ^ k * j) * (t ^ k * j) = (t ^ k) * (t ^ k) := by
      calc (t ^ k * j) * (t ^ k * j)
          = t ^ k * (j * t ^ k) * j := by group
        _ = t ^ k * (t ^ k * j) * j := by rw [hc.eq]
        _ = (t ^ k * t ^ k) * (j * j) := by group
        _ = (t ^ k) * (t ^ k) := by rw [hj2, mul_one]
    rw [heq] at h
    exact h
  have ht3 : t ^ 3 = 1 := by
    rw [← ht]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_refl (orderOf t))
  have h3 : (t ^ k) ^ 3 = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    rw [← ht]
    exact orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  have hu : t ^ k = 1 := by
    have h := h3
    rw [show (t ^ k) ^ 3 = (t ^ k) * (t ^ k) ^ 2 by group] at h
    rw [show (t ^ k) ^ 2 = (t ^ k) * (t ^ k) by group, h2, mul_one] at h
    exact h
  have hxj' : (x : B) * j * (x : B)⁻¹ = j := by rw [hxj, hu, one_mul]
  calc (x : B) * j = ((x : B) * j * (x : B)⁻¹) * x := by group
    _ = j * x := by rw [hxj']

private theorem eq_one_of_map_eq_one_of_sq_eq_one {B Y : Type*} [Group B] [Group Y] {t : B}
    (π : ↥(Subgroup.centralizer ({t} : Set B)) →* Y)
    (hker : π.ker = Subgroup.zpowers
      ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
    (ht : orderOf t = 3)
    {a : ↥(Subgroup.centralizer ({t} : Set B))}
    (ha2 : (a : B) * a = 1) (h : π a = 1) : a = 1 := by
  have hmem : a ∈ π.ker := by rwa [MonoidHom.mem_ker]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (by rwa [hker] at hmem)
  have hk' : t ^ k = (a : B) := by
    have h' := congrArg (fun z : ↥(Subgroup.centralizer ({t} : Set B)) => (z : B)) hk
    simpa using h'
  have h2 : (t ^ k) * (t ^ k) = 1 := by rw [hk', ha2]
  have ht3 : t ^ 3 = 1 := by
    rw [← ht]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_refl (orderOf t))
  have h3 : (t ^ k) ^ 3 = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    rw [← ht]
    exact orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  have hu : t ^ k = 1 := by
    have h := h3
    rw [show (t ^ k) ^ 3 = (t ^ k) * (t ^ k) ^ 2 by group] at h
    rw [show (t ^ k) ^ 2 = (t ^ k) * (t ^ k) by group, h2, mul_one] at h
    exact h
  apply Subtype.ext
  rw [← hk', hu]
  rfl

private theorem exists_Ebar (C : ThCore G)
    (hψa : (C.ψ ⟨Max3.z, Max3.z_mem_M⟩ : G) = C.z)
    {tM : ↥Max3.M} (htM : orderOf tM = 3)
    {E₀ : Subgroup ↥Max3.M}
    (hE₀c : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) (hE₀2 : ∀ x ∈ E₀, x * x = 1)
    (hE₀8 : Nat.card E₀ = 8) (hzE₀ : (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) ∈ E₀)
    (hE₀t : ∀ x ∈ E₀, x * tM = tM * x)
    (hCE : ∀ m : ↥Max3.M, m * tM = tM * m → (∀ x ∈ E₀, m * x = x * m) →
      ∃ x ∈ E₀, ∃ k : ℕ, m = x * tM ^ k)
    {Y : Type} [Group Y] (π : CT C tM →* Y) (Ē : Subgroup Y)
    (hĒ : Ē = ((E₀.map (phi C)).subgroupOf (CT C tM)).map π)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) :
    Nat.card Ē = 8 ∧
      (∀ a ∈ Ē, ∀ b ∈ Ē, a * b = b * a) ∧
      (∀ a ∈ Ē, a * a = 1) ∧
      Subgroup.centralizer (Ē : Set Y) = Ē := by
  rw [hĒ]
  classical
  have ht : orderOf (tG C tM) = 3 := orderOf_tG C htM
  have htCT : tG C tM ∈ (CT C tM) := tG_mem_CT C tM
  let tCT : (CT C tM) := ⟨tG C tM, htCT⟩
  have hker' : π.ker = Subgroup.zpowers tCT := hker
  have hπt : π tCT = 1 := by
    rw [← MonoidHom.mem_ker, hker']
    exact Subgroup.mem_zpowers tCT
  haveI : Finite Y := Finite.of_surjective π hπ
  have hEG_le_CT : E₀.map (phi C) ≤ (CT C tM) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun z : ↥Max3.M => (C.ψ z : G)) (hE₀t x hx)
    simpa [phi, tG, map_mul] using h
  let EG : Subgroup G := E₀.map (phi C)
  let EGsub : Subgroup (CT C tM) := EG.subgroupOf (CT C tM)
  let Ē : Subgroup Y := EGsub.map π
  have hEGsub_sq : ∀ a : EGsub, ((a : (CT C tM)) : G) * ((a : (CT C tM)) : G) = 1 := by
    intro a
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp a.2)
    rw [← hxeq, ← map_mul, hE₀2 x hx, map_one]
  have hEGsub_comm : ∀ a b : EGsub, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp a.2)
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp b.2)
    have ha : ((a : (CT C tM)) : G) = (phi C) x := hxeq.symm
    have hb : ((b : (CT C tM)) : G) = (phi C) y := hyeq.symm
    have hc : (phi C) x * (phi C) y = (phi C) y * (phi C) x := by
      rw [← map_mul, ← map_mul, hE₀c x hx y hy]
    change ((a : (CT C tM)) : G) * ((b : (CT C tM)) : G) =
      ((b : (CT C tM)) : G) * ((a : (CT C tM)) : G)
    rw [ha, hb, hc]
  have hπ_inj : Function.Injective (π.comp EGsub.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext a
    rw [Subgroup.mem_bot, MonoidHom.mem_ker]
    constructor
    · intro ha
      have ha2 : ((a : (CT C tM)) : G) * ((a : (CT C tM)) : G) = 1 := hEGsub_sq a
      have ha1 : (a : (CT C tM)) = 1 :=
        eq_one_of_map_eq_one_of_sq_eq_one π hker' ht ha2 ha
      exact Subtype.ext ha1
    · intro ha
      rw [ha, map_one]
  have hcard_Ē : Nat.card Ē = 8 := by
    rw [show Ē = EGsub.map π from rfl]
    have hinj : Set.InjOn π (EGsub : Set (CT C tM)) := by
      intro a ha b hb hab
      have hab' : (π.comp EGsub.subtype) (⟨a, ha⟩ : EGsub) =
          (π.comp EGsub.subtype) (⟨b, hb⟩ : EGsub) := hab
      exact Subtype.ext_iff.mp (hπ_inj hab')
    have h1 : Nat.card ↥(Subgroup.map π EGsub) =
        (Subgroup.map π EGsub : Set Y).ncard := Nat.card_coe_set_eq _
    rw [h1]
    change (π '' (EGsub : Set (CT C tM))).ncard = 8
    rw [hinj.ncard_image]
    have h2 : Nat.card ↥EGsub = (EGsub : Set (CT C tM)).ncard := Nat.card_coe_set_eq _
    rw [← h2]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG_le_CT).toEquiv]
    change Nat.card ↥(Subgroup.map (phi C) E₀) = 8
    rw [Subgroup.card_map_of_injective (phi_injective C), hE₀8]
  have hĒ_comm : ∀ a ∈ Ē, ∀ b ∈ Ē, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul]
    exact congrArg (fun z : EGsub => π (z : CT C tM))
      (hEGsub_comm ⟨a', ha'⟩ ⟨b', hb'⟩)
  have hĒ2 : ∀ a ∈ Ē, a * a = 1 := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_mul]
    have ha'2 : a' * a' = 1 := by
      apply Subtype.ext
      exact hEGsub_sq ⟨a', ha'⟩
    rw [ha'2, map_one]
  have hCĒ : Subgroup.centralizer (Ē : Set Y) = Ē := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨x₀, hx₀y⟩ := hπ y
      have hx₀_comm : ∀ a ∈ E₀, (x₀ : G) * (phi C) a = (phi C) a * (x₀ : G) := by
        intro a ha
        have hja : (phi C) a ∈ CT C tM :=
          hEG_le_CT (Subgroup.mem_map_of_mem (phi C) ha)
        have hja2 : ((⟨(phi C) a, hja⟩ : CT C tM) : G) *
            ((⟨(phi C) a, hja⟩ : CT C tM) : G) = 1 :=
          hEGsub_sq ⟨⟨(phi C) a, hja⟩, Subgroup.mem_subgroupOf.mpr
            (Subgroup.mem_map_of_mem (phi C) ha)⟩
        have hmemĒ : π (⟨(phi C) a, hja⟩ : CT C tM) ∈ Ē :=
          Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr
            (Subgroup.mem_map_of_mem (phi C) ha))
        have hcommY : π x₀ * π (⟨(phi C) a, hja⟩ : CT C tM) =
            π (⟨(phi C) a, hja⟩ : CT C tM) * π x₀ := by
          rw [hx₀y]
          exact ((Subgroup.mem_centralizer_iff.mp hy) _ hmemĒ).symm
        exact commute_of_map_commute π hker' ht hja2 hcommY
      have hx₀_z : (x₀ : G) ∈ Subgroup.centralizer ({C.z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := hx₀_comm ⟨Max3.z, Max3.z_mem_M⟩ hzE₀
        rwa [phi_apply, hψa] at this
      let m : ↥Max3.M := C.ψ.symm ⟨(x₀ : G), hx₀_z⟩
      have hmψ : C.ψ m = ⟨(x₀ : G), hx₀_z⟩ := C.ψ.apply_symm_apply _
      have hmφ : (phi C) m = (x₀ : G) := by rw [phi_apply, hmψ]
      have hmt : m * tM = tM * m := by
        apply C.ψ.injective
        apply Subtype.ext
        have hx_t : (x₀ : G) * (tG C tM) = (tG C tM) * (x₀ : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp x₀.2
        simpa [map_mul, hmψ, phi, tG] using hx_t
      have hmE : ∀ a ∈ E₀, m * a = a * m := by
        intro a ha
        apply C.ψ.injective
        apply Subtype.ext
        have h := hx₀_comm a ha
        simpa [map_mul, hmψ, phi_apply] using h
      obtain ⟨a₀, ha₀, k, hmk⟩ := hCE m hmt hmE
      have hx₀_eq : (x₀ : G) = (phi C) a₀ * (tG C tM) ^ k := by
        calc (x₀ : G) = (phi C) m := hmφ.symm
          _ = (phi C) (a₀ * tM ^ k) := by rw [hmk]
          _ = (phi C) a₀ * ((phi C) tM) ^ k := by rw [map_mul, map_pow]
          _ = (phi C) a₀ * (tG C tM) ^ k := rfl
      let aCT : CT C tM := ⟨(phi C) a₀,
        hEG_le_CT (Subgroup.mem_map_of_mem (phi C) ha₀)⟩
      have hx₀CT_eq : x₀ = aCT * tCT ^ k := by
        apply Subtype.ext
        simpa [aCT, tCT, tG] using hx₀_eq
      have hy_eq : y = π aCT := by
        rw [← hx₀y]
        rw [hx₀CT_eq, map_mul, map_pow, hπt, one_pow, mul_one]
      rw [hy_eq]
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map_of_mem (phi C) ha₀))
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_mul, ← map_mul]
      exact congrArg (fun z : EGsub => π (z : CT C tM))
        (hEGsub_comm ⟨a', ha'⟩ ⟨b', hb'⟩)
  exact ⟨hcard_Ē, hĒ_comm, hĒ2, hCĒ⟩

private theorem dvd_index_of_transitive {Y : Type*} [Group Y] [Finite Y] {V : Subgroup Y}
    {z₀ e₀ : Y} (hz₀ : z₀ ∈ V) (he₀ : e₀ ∈ V) (hz₀1 : z₀ ≠ 1) (he₀1 : e₀ ≠ 1)
    (he₀z : e₀ ≠ z₀) (h8 : Nat.card V = 8)
    (h1 : ∀ v ∈ V, v ≠ 1 → ∃ n ∈ Subgroup.normalizer (V : Set Y), n * z₀ * n⁻¹ = v)
    (h2 : ∀ v ∈ V, v ≠ 1 → v ≠ z₀ →
      ∃ n ∈ Subgroup.normalizer (V : Set Y), n * z₀ * n⁻¹ = z₀ ∧ n * e₀ * n⁻¹ = v) :
    42 ∣ ((Subgroup.centralizer (V : Set Y)).subgroupOf
      (Subgroup.normalizer (V : Set Y))).index := by
  classical
  let N : Subgroup Y := Subgroup.normalizer (V : Set Y)
  let K : Subgroup ↥N := (Subgroup.centralizer (V : Set Y)).subgroupOf N
  let zV : ↥V := ⟨z₀, hz₀⟩
  let eV : ↥V := ⟨e₀, he₀⟩
  have hOrbit_z : MulAction.orbit ↥N zV = {v : ↥V | (v : Y) ≠ 1} := by
    ext v
    constructor
    · intro hv
      rw [MulAction.mem_orbit_iff] at hv
      obtain ⟨n, rfl⟩ := hv
      intro h
      have h1 : (n • zV : ↥V) = 1 := Subtype.ext h
      have h2 : zV = (n⁻¹ : ↥N) • (n • zV) := by
        rw [smul_smul, inv_mul_cancel, one_smul]
      rw [h1] at h2
      have h3 : zV = 1 := by
        rw [h2]
        exact MulDistribMulAction.smul_one (n⁻¹ : ↥N)
      exact hz₀1 (Subtype.ext_iff.mp h3)
    · intro hv
      rw [MulAction.mem_orbit_iff]
      obtain ⟨n, hnN, hn⟩ := h1 (v : Y) v.2 hv
      refine ⟨⟨n, hnN⟩, ?_⟩
      apply Subtype.ext
      rw [normalizer_smul_apply]
      exact hn
  have hcard_orbit_z : (MulAction.orbit ↥N zV).ncard = 7 := by
    rw [hOrbit_z]
    have hset : {v : ↥V | (v : Y) ≠ 1} = (Set.univ : Set ↥V) \ {1} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and]
      constructor
      · intro h hv
        exact h (by rw [hv]; rfl)
      · intro h hv
        exact h (Subtype.ext hv)
    rw [hset, Set.ncard_diff_singleton_of_mem (Set.mem_univ (1 : ↥V)), Set.ncard_univ,
      show Nat.card ↥V = 8 from h8]
  let S : Subgroup ↥N := MulAction.stabilizer ↥N zV
  have hS_index : S.index = 7 := by
    rw [MulAction.index_stabilizer, hcard_orbit_z]
  letI : MulAction ↥S ↥V := MulAction.compHom ↥V S.subtype
  have hS_smul : ∀ (s : ↥S) (v : ↥V),
      ((s • v : ↥V) : Y) = (s : Y) * (v : Y) * (s : Y)⁻¹ := by
    intro s v
    change (((s : ↥N) • v : ↥V) : Y) = ((s : ↥N) : Y) * (v : Y) * ((s : ↥N) : Y)⁻¹
    rw [normalizer_smul_apply]
  have hOrbit_e : MulAction.orbit ↥S eV = {v : ↥V | (v : Y) ≠ 1 ∧ (v : Y) ≠ z₀} := by
    ext v
    constructor
    · intro hv
      rw [MulAction.mem_orbit_iff] at hv
      obtain ⟨s, rfl⟩ := hv
      constructor
      · intro h
        have h1 : (s • eV : ↥V) = 1 := Subtype.ext h
        have h2 : eV = (s⁻¹ : ↥S) • (s • eV) := by
          rw [smul_smul, inv_mul_cancel, one_smul]
        rw [h1] at h2
        have h3 : eV = 1 := by
          rw [h2]
          exact MulDistribMulAction.smul_one (s⁻¹ : ↥S)
        exact he₀1 (Subtype.ext_iff.mp h3)
      · intro h
        have h1 : (s • eV : ↥V) = zV := Subtype.ext h
        have h2 : eV = (s⁻¹ : ↥S) • (s • eV) := by
          rw [smul_smul, inv_mul_cancel, one_smul]
        rw [h1] at h2
        have hs : (s : ↥N) • zV = zV := MulAction.mem_stabilizer_iff.mp s.2
        have hs' : (s⁻¹ : ↥S) • zV = zV :=
          MulAction.mem_stabilizer_iff.mp (S.inv_mem s.2)
        rw [hs'] at h2
        exact he₀z (Subtype.ext_iff.mp h2)
    · intro hv
      rw [MulAction.mem_orbit_iff]
      obtain ⟨n, hnN, hnz, hne⟩ := h2 (v : Y) v.2 hv.1 hv.2
      have hnS : (⟨n, hnN⟩ : ↥N) ∈ S := by
        rw [MulAction.mem_stabilizer_iff]
        apply Subtype.ext
        rw [normalizer_smul_apply]
        exact hnz
      refine ⟨⟨⟨n, hnN⟩, hnS⟩, ?_⟩
      apply Subtype.ext
      rw [hS_smul]
      exact hne
  have hcard_orbit_e : (MulAction.orbit ↥S eV).ncard = 6 := by
    rw [hOrbit_e]
    have hset : {v : ↥V | (v : Y) ≠ 1 ∧ (v : Y) ≠ z₀} =
        ((Set.univ : Set ↥V) \ {1}) \ {zV} := by
      ext v
      have h1 : ((v : Y) ≠ 1) ↔ (v ≠ 1) := by
        constructor
        · intro h hv; exact h (by rw [hv]; rfl)
        · intro h hv; exact h (Subtype.ext hv)
      have h2 : ((v : Y) ≠ z₀) ↔ (v ≠ zV) := by
        constructor
        · intro h hv; exact h (congrArg (fun w : ↥V => (w : Y)) hv)
        · intro h hv; exact h (Subtype.ext hv)
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and,
        h1, h2]
    rw [hset]
    have hzVmem : zV ∈ (Set.univ : Set ↥V) \ {1} := by
      simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and]
      intro h
      exact hz₀1 (Subtype.ext_iff.mp h)
    rw [Set.ncard_diff_singleton_of_mem hzVmem,
      Set.ncard_diff_singleton_of_mem (Set.mem_univ (1 : ↥V)), Set.ncard_univ,
      show Nat.card ↥V = 8 from h8]
  let T : Subgroup ↥S := MulAction.stabilizer ↥S eV
  have hT_index : T.index = 6 := by
    rw [MulAction.index_stabilizer, hcard_orbit_e]
  have hKS : K ≤ S := by
    intro k hk
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [normalizer_smul_apply]
    change (k : Y) * z₀ * (k : Y)⁻¹ = z₀
    have hk' : (k : Y) ∈ Subgroup.centralizer (V : Set Y) := by
      change k ∈ (Subgroup.centralizer (V : Set Y)).subgroupOf N at hk
      exact Subgroup.mem_subgroupOf.mp hk
    have hcomm : (k : Y) * z₀ = z₀ * (k : Y) :=
      (Subgroup.mem_centralizer_iff.mp hk' z₀ hz₀).symm
    rw [hcomm]
    group
  have hKT : K.subgroupOf S ≤ T := by
    intro k hk
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [hS_smul]
    change ((k : ↥S) : Y) * e₀ * ((k : ↥S) : Y)⁻¹ = e₀
    have hk' : ((k : ↥S) : ↥N) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hk'' : (((k : ↥S) : ↥N) : Y) ∈ Subgroup.centralizer (V : Set Y) :=
      Subgroup.mem_subgroupOf.mp hk'
    have hcomm : ((k : ↥S) : Y) * e₀ = e₀ * ((k : ↥S) : Y) :=
      (Subgroup.mem_centralizer_iff.mp hk'' e₀ he₀).symm
    rw [hcomm]
    group
  have h7 : 7 ∣ K.index := by
    have := Subgroup.index_dvd_of_le hKS
    rwa [hS_index] at this
  have h6 : 6 ∣ (K.subgroupOf S).index := by
    have := Subgroup.index_dvd_of_le hKT
    rwa [hT_index] at this
  have hK_index : K.index = S.index * (K.subgroupOf S).index := by
    have hcardK : Nat.card ↥(K.subgroupOf S) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKS).toEquiv
    have h1 := Subgroup.card_mul_index K
    have h2 := Subgroup.card_mul_index S
    have h3 := Subgroup.card_mul_index (K.subgroupOf S)
    rw [hcardK] at h3
    have h4 : Nat.card ↥K * K.index =
        Nat.card ↥K * ((K.subgroupOf S).index * S.index) := by
      rw [h1, ← h2, ← h3]
      ring
    have hpos : 0 < Nat.card ↥K := Nat.card_pos
    have := Nat.mul_left_cancel hpos h4
    rw [this, mul_comm]
  rw [hK_index, hS_index]
  simpa [show 42 = 7 * 6 by norm_num] using Nat.mul_dvd_mul_left 7 h6

private theorem g23Two_normalizer {Y : Type*} [Group Y] [Finite Y] {V : Subgroup Y}
    (hV : CFSG.Open.IsElemAbelian 2 V) (h8 : Nat.card V = 8)
    (hC : Subgroup.centralizer (V : Set Y) ≤ V)
    (h42 : 42 ∣ ((Subgroup.centralizer (V : Set Y)).subgroupOf
      (Subgroup.normalizer (V : Set Y))).index) :
    CFSG.Quasithin.G23Type.G23Two (Subgroup.normalizer (V : Set Y)) := by
  classical
  let N : Subgroup Y := Subgroup.normalizer (V : Set Y)
  let K : Subgroup ↥N := (Subgroup.centralizer (V : Set Y)).subgroupOf N
  let ρ : ↥N →* MulAut ↥V := V.normalizerMonoidHom
  let R : Subgroup (MulAut ↥V) := ρ.range
  have hK : K = ρ.ker := by
    rw [show ρ.ker = (Subgroup.centralizer (V : Set Y)).subgroupOf N from
      Subgroup.normalizerMonoidHom_ker V]
  have hRcard : Nat.card ↥R = K.index := by
    rw [hK]
    exact (Subgroup.index_ker ρ).symm
  have h2K : 2 ∣ K.index := (show 2 ∣ 42 by norm_num).trans h42
  have h7K : 7 ∣ K.index := (show 7 ∣ 42 by norm_num).trans h42
  have h2R : 2 ∣ Nat.card ↥R := by rw [hRcard]; exact h2K
  have h7R : 7 ∣ Nat.card ↥R := by rw [hRcard]; exact h7K
  obtain ⟨ε⟩ := CFSG.ComponentClassification.GHarris.nonempty_mulAut_equiv_GL32 hV h8
  let R' : Subgroup (GL (Fin 3) (ZMod 2)) := R.map ε.toMonoidHom
  have hcardR' : Nat.card ↥R' = Nat.card ↥R :=
    Subgroup.card_map_of_injective ε.injective
  have h2R' : 2 ∣ Nat.card ↥R' := by rw [hcardR']; exact h2R
  have h7R' : 7 ∣ Nat.card ↥R' := by rw [hcardR']; exact h7R
  have hR'top : R' = ⊤ :=
    CFSG.ComponentClassification.GMS78.eq_top_of_two_dvd_of_seven_dvd_GL32 h2R' h7R'
  have hR168 : Nat.card ↥R = 168 := by
    rw [← hcardR', hR'top, Subgroup.card_top,
      CFSG.ComponentClassification.GHarris.card_GL32_gh]
  have hK168 : K.index = 168 := by rw [← hRcard, hR168]
  have h56 : 56 ∣ K.index := by rw [hK168]; norm_num
  obtain ⟨θ, hθsurj, hθker⟩ :=
    CFSG.ComponentClassification.GHarris.exists_GL32_of_dvd_index hV h8 (by
      rw [show ((Subgroup.centralizer (V : Set Y)).subgroupOf
        (Subgroup.normalizer (V : Set Y))).index = K.index from rfl]
      exact h56)
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  have hV_le_pCore : V ≤ CFSG.Open.pCoreOf 2 N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.le_normalizer) le_rfl hV2
  have hpCore_le_K : pCore 2 ↥N ≤ K := by
    have hmap := CFSG.LieType.BorelTits.map_pCore_le 2 θ hθsurj
    have hpCore_bot : pCore 2 (GL (Fin 3) (ZMod 2)) = ⊥ := by
      rcases CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh.eq_bot_or_eq_top_of_normal
        (pCore 2 (GL (Fin 3) (ZMod 2))) with h | h
      · exact h
      · exfalso
        have hp : IsPGroup 2 (↥(⊤ : Subgroup (GL (Fin 3) (ZMod 2)))) := by
          rw [← h]
          exact CFSG.LieType.BorelTits.pCore_isPGroup 2
        obtain ⟨n, hn⟩ := hp.exists_card_eq
        have hcard : Nat.card ↥(⊤ : Subgroup (GL (Fin 3) (ZMod 2))) = 168 := by
          rw [Subgroup.card_top, CFSG.ComponentClassification.GHarris.card_GL32_gh]
        rw [hcard] at hn
        have hn7 : n ≤ 7 := by
          by_contra hle
          have hdvd : 2 ^ 8 ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
          rw [← hn] at hdvd
          norm_num at hdvd
        interval_cases n <;> norm_num at hn
    rw [hpCore_bot] at hmap
    rw [Subgroup.map_le_iff_le_comap] at hmap
    rw [MonoidHom.comap_bot] at hmap
    rwa [hθker] at hmap
  have hpCoreOf_le_V : CFSG.Open.pCoreOf 2 N ≤ V := by
    have hmap : CFSG.Open.pCoreOf 2 N ≤ Subgroup.centralizer (V : Set Y) := by
      calc CFSG.Open.pCoreOf 2 N = (pCore 2 ↥N).map N.subtype := rfl
        _ ≤ ((Subgroup.centralizer (V : Set Y)).subgroupOf N).map N.subtype :=
            Subgroup.map_mono hpCore_le_K
        _ = Subgroup.centralizer (V : Set Y) :=
            Subgroup.map_subgroupOf_eq_of_le (Subgroup.centralizer_le_normalizer (V : Set Y))
    exact hmap.trans hC
  have hV_eq : CFSG.Open.pCoreOf 2 N = V := le_antisymm hpCoreOf_le_V hV_le_pCore
  have hVEq : Subgroup.centralizer (V : Set Y) = V := by
    refine le_antisymm hC ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg (fun z : ↥V => (z : Y)) (hV.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
  have hF : CFSG.Open.quasithinGenFitting N = V := by
    have h := (CFSG.Quasithin.quasithinGenFitting_eq_pCoreOf_iff N 2).mpr ?_
    · rwa [hV_eq] at h
    · rw [hV_eq]
      exact inf_le_right.trans hC
  refine ⟨?_, ?_, ?_⟩
  · rw [hF]; exact hV
  · rw [hF]; exact h8
  · refine ⟨CFSG.ComponentClassification.GHarris.SL32EquivGL32.symm.toMonoidHom.comp θ,
      CFSG.ComponentClassification.GHarris.SL32EquivGL32.symm.surjective.comp hθsurj, ?_⟩
    rw [MonoidHom.ker_comp_of_injective θ
      CFSG.ComponentClassification.GHarris.SL32EquivGL32.symm.toMonoidHom
      CFSG.ComponentClassification.GHarris.SL32EquivGL32.symm.injective]
    rw [hθker, hF, hVEq]

theorem exists_g23Two_quot (C : ThCore G)
    (hψa : (C.ψ ⟨Max3.z, Max3.z_mem_M⟩ : G) = C.z)
    {tM : ↥Max3.M} (htM : orderOf tM = 3)
    {E₀ : Subgroup ↥Max3.M} {e₀ : ↥Max3.M} (he₀ : e₀ ∈ E₀) (he₀1 : e₀ ≠ 1)
    (he₀z : (e₀ : J) ≠ Max3.z)
    (hE₀c : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) (hE₀2 : ∀ x ∈ E₀, x * x = 1)
    (hE₀8 : Nat.card E₀ = 8) (hzE₀ : (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) ∈ E₀)
    (hE₀t : ∀ x ∈ E₀, x * tM = tM * x)
    (hCE : ∀ m : ↥Max3.M, m * tM = tM * m → (∀ x ∈ E₀, m * x = x * m) →
      ∃ x ∈ E₀, ∃ k : ℕ, m = x * tM ^ k)
    (htrans : ∀ w ∈ E₀, w ≠ 1 → (w : J) ≠ Max3.z → ∃ n : ↥Max3.M, n * tM = tM * n ∧
      (∀ x ∈ E₀, n * x * n⁻¹ ∈ E₀) ∧ n * e₀ * n⁻¹ = w)
    (hZt : ∀ w : ↥Max3.M, (w : J) ∈ Max3.Q → w * tM = tM * w → w ≠ 1 → (w : J) ≠ Max3.z →
      ∃ q : ↥Max3.M, (q : J) ∈ Max3.Q ∧ q * tM = tM * q ∧ q * w ≠ w * q)
    (hC13 : ∃ g : G, g * C.z * g⁻¹ = (C.ψ e₀ : G) ∧
      ∀ x ∈ E₀, ∃ q : ↥Max3.M, (q : J) ∈ Max3.Q ∧ (C.ψ q : G) = g⁻¹ * (C.ψ x : G) * g)
    (hy : ∃ y ∈ Subgroup.centralizer ({(C.ψ tM : G)} : Set G),
      y * (C.ψ e₀ : G) * y⁻¹ = C.z)
    {Y : Type} [Group Y] (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Y)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) :
    ∃ V : Subgroup Y, CFSG.Quasithin.G23Type.G23Two (Subgroup.normalizer (V : Set Y)) := by
  have hEG_le_CT : E₀.map (phi C) ≤ CT C tM := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun z : ↥Max3.M => (C.ψ z : G)) (hE₀t x hx)
    simpa [phi, tG, map_mul] using h
  let EG : Subgroup G := E₀.map (phi C)
  let EGsub : Subgroup (CT C tM) := EG.subgroupOf (CT C tM)
  let Ē : Subgroup Y := EGsub.map π
  have hĒ : Ē = ((E₀.map (phi C)).subgroupOf (CT C tM)).map π := rfl
  obtain ⟨hcard_Ē, hĒ_comm, hĒ2, hCĒ⟩ :=
    exists_Ebar C hψa htM hE₀c hE₀2 hE₀8 hzE₀ hE₀t hCE π Ē hĒ hπ hker
  have ht : orderOf (tG C tM) = 3 := orderOf_tG C htM
  have htCT : tG C tM ∈ CT C tM := tG_mem_CT C tM
  let tCT : CT C tM := ⟨tG C tM, htCT⟩
  have hker' : π.ker = Subgroup.zpowers tCT := hker
  have hπt : π tCT = 1 := by
    rw [← MonoidHom.mem_ker, hker']
    exact Subgroup.mem_zpowers tCT
  haveI : Finite Y := Finite.of_surjective π hπ
  let zG : G := C.z
  let e : G := (C.ψ e₀ : G)
  let zM : ↥Max3.M := ⟨Max3.z, Max3.z_mem_M⟩
  have hzG_phi : phi C zM = zG := hψa
  have hzG_CT : zG ∈ CT C tM := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun z : ↥Max3.M => (C.ψ z : G)) (hE₀t zM hzE₀)
    simpa [zG, zM, phi, tG, map_mul, hψa] using h
  have he_CT : e ∈ CT C tM := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun z : ↥Max3.M => (C.ψ z : G)) (hE₀t e₀ he₀)
    simpa [e, phi, tG, map_mul] using h
  obtain ⟨y, hyCT, hy_eq⟩ := hy
  obtain ⟨g, hg1, hg2⟩ := hC13
  have hyg_z : y * g ∈ Subgroup.centralizer ({zG} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (y * g) * zG = y * (g * zG * g⁻¹) * y⁻¹ * (y * g) := by group
      _ = y * e * y⁻¹ * (y * g) := by rw [hg1]
      _ = zG * (y * g) := by rw [hy_eq]
  let m : ↥Max3.M := C.ψ.symm ⟨y * g, hyg_z⟩
  have hmψ : C.ψ m = ⟨y * g, hyg_z⟩ := C.ψ.apply_symm_apply _
  have hmφ : phi C m = y * g := by rw [phi_apply, hmψ]
  have hyx : ∀ x ∈ E₀, ∃ q : ↥Max3.M, (q : J) ∈ Q ∧
      phi C (m * q * m⁻¹) = y * phi C x * y⁻¹ := by
    intro x hx
    obtain ⟨q, hqQ, hqeq⟩ := hg2 x hx
    refine ⟨q, hqQ, ?_⟩
    have hqeq' : phi C q = g⁻¹ * phi C x * g := by simpa [phi] using hqeq
    have hmq : phi C (m * q * m⁻¹) =
        (y * g) * (g⁻¹ * phi C x * g) * (y * g)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hmφ, hqeq']
    rw [hmq]
    group
  obtain ⟨qz, hqzQ, hqz⟩ := hg2 zM hzE₀
  let w : ↥Max3.M := m * qz * m⁻¹
  have hwQ : (w : J) ∈ Q := AltQuot.conj_mem_Q_of_mem_M m.2 hqzQ
  have hqz' : phi C qz = g⁻¹ * phi C zM * g := by simpa [phi] using hqz
  have hwφ : phi C w = y * zG * y⁻¹ := by
    rw [show w = m * qz * m⁻¹ from rfl, map_mul, map_mul, map_inv, hmφ, hqz', hzG_phi]
    group
  have hwCT : phi C w ∈ CT C tM := by
    rw [hwφ]
    exact (CT C tM).mul_mem ((CT C tM).mul_mem hyCT hzG_CT) ((CT C tM).inv_mem hyCT)
  have hwt : w * tM = tM * w := by
    apply phi_injective C
    have h := hwCT
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    simpa [map_mul, phi, tG] using h
  have hzG_ne_one : zG ≠ 1 := by
    intro h
    have h1 : C.ψ zM = 1 := by
      apply Subtype.ext
      exact hψa.trans h
    have h3 : zM = 1 := C.ψ.injective (by simpa using h1)
    exact Max3.z_ne_one (by simpa [zM] using congrArg (fun z : ↥Max3.M => (z : J)) h3)
  have hw_ne_one : w ≠ 1 := by
    intro h
    have h1 : phi C w = 1 := by rw [h, map_one]
    rw [hwφ] at h1
    have h2 : zG = 1 := by
      calc zG = y⁻¹ * (y * zG * y⁻¹) * y := by group
        _ = y⁻¹ * 1 * y := by rw [h1]
        _ = 1 := by group
    exact hzG_ne_one h2
  have hwz : (w : J) ≠ Max3.z := by
    intro h
    have hwz' : w = zM := Subtype.ext h
    have h1 : phi C w = zG := by rw [hwz', hzG_phi]
    rw [hwφ] at h1
    have hyz : y * zG = zG * y := by
      calc y * zG = (y * zG * y⁻¹) * y := by group
        _ = zG * y := by rw [h1]
    have he_z : e = zG := by
      calc e = y⁻¹ * (y * e * y⁻¹) * y := by group
        _ = y⁻¹ * zG * y := by rw [hy_eq]
        _ = zG := by
          calc y⁻¹ * zG * y = y⁻¹ * (zG * y) := by group
            _ = y⁻¹ * (y * zG) := by rw [← hyz]
            _ = zG := by group
    have he0z : e₀ = zM := by
      apply phi_injective C
      rw [show phi C e₀ = e from rfl, he_z, hzG_phi]
    exact he₀z (by simpa [zM] using congrArg (fun z : ↥Max3.M => (z : J)) he0z)
  obtain ⟨q, hqQ, hqt, hqwnc⟩ := hZt w hwQ hwt hw_ne_one hwz
  have hz2 : Max3.z * Max3.z = 1 := Max3.z_mul_self
  have hcomm_w : (q : J) * (w : J) * (q : J)⁻¹ * (w : J)⁻¹ ∈
      Subgroup.zpowers Max3.z := by
    have h := AltQuot.comm_mem_zpowers hqQ hwQ
    rwa [commutatorElement_def] at h
  have hqw_J : (q : J) * (w : J) * (q : J)⁻¹ = Max3.z * (w : J) := by
    have hcase := conj_eq_or_conj_eq_mul_of_commutator_mem_zpowers (A := J) (z := Max3.z)
      (q := (q : J)) (f := (w : J)) hz2 hcomm_w
    rcases hcase with h | h
    · exfalso
      apply hqwnc
      apply Subtype.ext
      have h' : (q : J) * (w : J) * (q : J)⁻¹ = (w : J) := h
      calc (q : J) * (w : J) = ((q : J) * (w : J) * (q : J)⁻¹) * (q : J) := by group
        _ = (w : J) * (q : J) := by rw [h']
    · exact h
  have hqw : q * w * q⁻¹ = zM * w := by
    apply Subtype.ext
    simpa [zM] using hqw_J
  have hq_conj : ∀ f : ↥Max3.M, (f : J) ∈ Q →
      q * f * q⁻¹ = f ∨ q * f * q⁻¹ = zM * f := by
    intro f hfQ
    have hc : (q : J) * (f : J) * (q : J)⁻¹ * (f : J)⁻¹ ∈
        Subgroup.zpowers Max3.z := by
      have h := AltQuot.comm_mem_zpowers hqQ hfQ
      rwa [commutatorElement_def] at h
    have hcase := conj_eq_or_conj_eq_mul_of_commutator_mem_zpowers (A := J) (z := Max3.z)
      (q := (q : J)) (f := (f : J)) hz2 hc
    rcases hcase with h | h
    · left
      apply Subtype.ext
      simpa [zM] using h
    · right
      apply Subtype.ext
      simpa [zM] using h
  have hqCT : phi C q ∈ CT C tM := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun z : ↥Max3.M => (C.ψ z : G)) hqt
    simpa [phi, tG, map_mul] using h
  let nG : G := y⁻¹ * phi C q * y
  have hnCT : nG ∈ CT C tM :=
    (CT C tM).mul_mem ((CT C tM).mul_mem ((CT C tM).inv_mem hyCT) hqCT) hyCT
  let nCT : CT C tM := ⟨nG, hnCT⟩
  have he_eq : e = y⁻¹ * zG * y := by
    calc e = y⁻¹ * (y * e * y⁻¹) * y := by group
      _ = y⁻¹ * zG * y := by rw [hy_eq]
  have hn_action : ∀ x ∈ E₀, nG * phi C x * nG⁻¹ = phi C x ∨
      nG * phi C x * nG⁻¹ = e * phi C x := by
    intro x hx
    obtain ⟨qx, hqxQ, hqxeq⟩ := hg2 x hx
    let f : ↥Max3.M := m * qx * m⁻¹
    have hfQ : (f : J) ∈ Q := AltQuot.conj_mem_Q_of_mem_M m.2 hqxQ
    have hqxeq' : phi C qx = g⁻¹ * phi C x * g := by simpa [phi] using hqxeq
    have hfφ : phi C f = y * phi C x * y⁻¹ := by
      rw [show f = m * qx * m⁻¹ from rfl, map_mul, map_mul, map_inv, hmφ, hqxeq']
      group
    have hstep : nG * phi C x * nG⁻¹ = y⁻¹ * phi C (q * f * q⁻¹) * y := by
      calc nG * phi C x * nG⁻¹
          = y⁻¹ * phi C q * (y * phi C x * y⁻¹) * (phi C q)⁻¹ * y := by
            rw [show nG = y⁻¹ * phi C q * y from rfl]
            group
        _ = y⁻¹ * phi C q * phi C f * (phi C q)⁻¹ * y := by rw [← hfφ]
        _ = y⁻¹ * phi C (q * f * q⁻¹) * y := by
            rw [show phi C (q * f * q⁻¹) = phi C q * phi C f * (phi C q)⁻¹ by
              rw [map_mul, map_mul, map_inv]]
            group
    rcases hq_conj f hfQ with h | h
    · left
      rw [hstep, h, hfφ]
      group
    · right
      rw [hstep, h, map_mul, hzG_phi, hfφ, he_eq]
      group
  have hn_z : nG * zG * nG⁻¹ = e * zG := by
    have hstep : nG * zG * nG⁻¹ = y⁻¹ * phi C (q * w * q⁻¹) * y := by
      calc nG * zG * nG⁻¹
          = y⁻¹ * phi C q * (y * zG * y⁻¹) * (phi C q)⁻¹ * y := by
            rw [show nG = y⁻¹ * phi C q * y from rfl]
            group
        _ = y⁻¹ * phi C q * phi C w * (phi C q)⁻¹ * y := by rw [← hwφ]
        _ = y⁻¹ * phi C (q * w * q⁻¹) * y := by
            rw [show phi C (q * w * q⁻¹) = phi C q * phi C w * (phi C q)⁻¹ by
              rw [map_mul, map_mul, map_inv]]
            group
    rw [hstep, hqw, map_mul, hzG_phi, hwφ, he_eq]
    group
  let zbar : Y := π ⟨zG, hzG_CT⟩
  let nY : Y := π nCT
  have hnY_maps : ∀ a ∈ Ē, nY * a * nY⁻¹ ∈ Ē := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp ha')
    have hmem : nG * (a' : G) * nG⁻¹ ∈ EG := by
      rw [← hxeq]
      rcases hn_action x hx with h | h
      · rw [h]; exact Subgroup.mem_map_of_mem (phi C) hx
      · rw [h, show e = phi C e₀ from rfl, ← map_mul]
        exact Subgroup.mem_map_of_mem (phi C) (E₀.mul_mem he₀ hx)
    have hmemY : nY * π a' * nY⁻¹ =
        π ((⟨nG, hnCT⟩ : CT C tM) * a' * (⟨nG, hnCT⟩ : CT C tM)⁻¹) := by
      rw [show nY = π ⟨nG, hnCT⟩ from rfl]
      rw [← map_mul, ← map_inv, ← map_mul]
    have hsub : (⟨nG, hnCT⟩ : CT C tM) * a' * (⟨nG, hnCT⟩ : CT C tM)⁻¹ =
        ⟨nG * (a' : G) * nG⁻¹, hEG_le_CT hmem⟩ := by
      apply Subtype.ext
      rfl
    rw [hmemY, hsub]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hmem)
  haveI : Finite ↥Ē := Nat.finite_of_card_ne_zero (by rw [hcard_Ē]; norm_num)
  have hnY_norm : nY ∈ Subgroup.normalizer (Ē : Set Y) :=
    mem_normalizer_of_mapsTo hnY_maps
  have hnY_z : nY * zbar * nY⁻¹ = π (⟨e * zG, (CT C tM).mul_mem he_CT hzG_CT⟩ : CT C tM) := by
    have h : (⟨nG, hnCT⟩ : CT C tM) * ⟨zG, hzG_CT⟩ * (⟨nG, hnCT⟩ : CT C tM)⁻¹ =
        ⟨e * zG, (CT C tM).mul_mem he_CT hzG_CT⟩ := by
      apply Subtype.ext
      simpa using hn_z
    calc nY * zbar * nY⁻¹
        = π ((⟨nG, hnCT⟩ : CT C tM) * ⟨zG, hzG_CT⟩ * (⟨nG, hnCT⟩ : CT C tM)⁻¹) := by
          rw [show nY = π ⟨nG, hnCT⟩ from rfl, show zbar = π ⟨zG, hzG_CT⟩ from rfl]
          rw [← map_mul, ← map_inv, ← map_mul]
      _ = π ⟨e * zG, (CT C tM).mul_mem he_CT hzG_CT⟩ := by rw [h]
  have he_ne_one : e ≠ 1 := phi_ne_one C he₀1
  have hne : π (⟨e * zG, (CT C tM).mul_mem he_CT hzG_CT⟩ : CT C tM) ≠ zbar := by
    intro h
    have he2 : e * e = 1 := by
      simpa [e] using phi_sq_eq_one_of_sq_eq_one C (hE₀2 e₀ he₀)
    exact false_of_map_mul_eq_of_sq_eq_one π hker' ht he_CT hzG_CT he2 he_ne_one
      (by simpa [zbar] using h)
  let ebarY : Y := π ⟨e, he_CT⟩
  have hzbar_mem : zbar ∈ Ē := by
    have h : zbar = π (⟨(phi C) zM, hEG_le_CT (Subgroup.mem_map_of_mem (phi C) hzE₀)⟩ :
        CT C tM) := by simp [zbar, zG, hzG_phi]
    rw [h]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_map_of_mem (phi C) hzE₀))
  have hebar_mem : ebarY ∈ Ē :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_map_of_mem (phi C) he₀))
  have hzG2 : zG * zG = 1 := by
    have hzM2 : zM * zM = 1 := Subtype.ext Max3.z_mul_self
    have h : phi C zM * phi C zM = 1 := phi_sq_eq_one_of_sq_eq_one C hzM2
    rw [show zG = (C.ψ zM : G) from hψa.symm]
    exact h
  have hzbar2 : zbar * zbar = 1 := by
    rw [show zbar = π ⟨zG, hzG_CT⟩ from rfl, ← map_mul]
    have h : (⟨zG, hzG_CT⟩ : CT C tM) * ⟨zG, hzG_CT⟩ = 1 := by
      ext
      exact hzG2
    rw [h, map_one]
  have hebar_ne_one : ebarY ≠ 1 := by
    intro h
    have he2 : ((⟨e, he_CT⟩ : CT C tM) : G) * ((⟨e, he_CT⟩ : CT C tM) : G) = 1 := by
      simpa [e] using phi_sq_eq_one_of_sq_eq_one C (hE₀2 e₀ he₀)
    have he1 : (⟨e, he_CT⟩ : CT C tM) = 1 :=
      eq_one_of_map_eq_one_of_sq_eq_one π hker' ht he2 h
    exact he_ne_one (Subtype.ext_iff.mp he1)
  have hebar_ne_zbar : ebarY ≠ zbar := by
    intro h
    have hez : π (⟨e * zG, (CT C tM).mul_mem he_CT hzG_CT⟩ : CT C tM) = 1 := by
      have h' : π (⟨e, he_CT⟩ : CT C tM) = zbar := h
      have hz' : π (⟨zG, hzG_CT⟩ : CT C tM) = zbar := rfl
      rw [show (⟨e * zG, (CT C tM).mul_mem he_CT hzG_CT⟩ : CT C tM) =
        (⟨e, he_CT⟩ : CT C tM) * ⟨zG, hzG_CT⟩ from rfl, map_mul, h', hz', hzbar2]
    have hez2 : ((⟨e * zG, (CT C tM).mul_mem he_CT hzG_CT⟩ : CT C tM) : G) *
        ((⟨e * zG, (CT C tM).mul_mem he_CT hzG_CT⟩ : CT C tM) : G) = 1 := by
      have he2 : e * e = 1 := by
        simpa [e] using phi_sq_eq_one_of_sq_eq_one C (hE₀2 e₀ he₀)
      have hz_comm : e * zG = zG * e := by
        have h : e₀ * zM = zM * e₀ := hE₀c e₀ he₀ zM hzE₀
        have hzG_eq : (C.ψ zM : G) = zG := hψa
        simpa [e, map_mul, hzG_eq] using
          congrArg (fun z : ↥Max3.M => (C.ψ z : G)) h
      simp only [Subgroup.coe_mul]
      calc e * zG * (e * zG) = e * (zG * e) * zG := by group
        _ = e * (e * zG) * zG := by rw [← hz_comm]
        _ = (e * e) * (zG * zG) := by group
        _ = 1 := by rw [he2, hzG2, one_mul]
    have hez1 : (⟨e * zG, (CT C tM).mul_mem he_CT hzG_CT⟩ : CT C tM) = 1 :=
      eq_one_of_map_eq_one_of_sq_eq_one π hker' ht hez2 hez
    have he_zG : e = zG := by
      have h1 : e * zG = 1 := Subtype.ext_iff.mp hez1
      calc e = e * zG * zG := by rw [mul_assoc, hzG2, mul_one]
        _ = 1 * zG := by rw [h1]
        _ = zG := one_mul _
    have he0z : e₀ = zM := by
      apply phi_injective C
      rw [show phi C e₀ = e from rfl, he_zG, hzG_phi]
    exact he₀z (by simpa [zM] using congrArg (fun z : ↥Max3.M => (z : J)) he0z)
  have hzbar_ne_one : zbar ≠ 1 := by
    intro h
    have h1 : π (⟨zG, hzG_CT⟩ : CT C tM) = 1 := h
    have hz2 : ((⟨zG, hzG_CT⟩ : CT C tM) : G) *
        ((⟨zG, hzG_CT⟩ : CT C tM) : G) = 1 := by
      simpa using hzG2
    have hz1 : (⟨zG, hzG_CT⟩ : CT C tM) = 1 :=
      eq_one_of_map_eq_one_of_sq_eq_one π hker' ht hz2 h1
    exact hzG_ne_one (Subtype.ext_iff.mp hz1)
  have h2trans : ∀ v ∈ Ē, v ≠ 1 → v ≠ zbar →
      ∃ n ∈ Subgroup.normalizer (Ē : Set Y), n * zbar * n⁻¹ = zbar ∧
        n * ebarY * n⁻¹ = v := by
    intro v hv hv1 hvz
    obtain ⟨v', hv', hv_eq⟩ := Subgroup.mem_map.mp hv
    obtain ⟨w, hwE, hw_eq⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hv')
    have hv'eq : v' = (⟨(phi C) w, hEG_le_CT (Subgroup.mem_map_of_mem (phi C) hwE)⟩ :
        CT C tM) := Subtype.ext hw_eq.symm
    have hvπ : v = π (⟨(phi C) w, hEG_le_CT (Subgroup.mem_map_of_mem (phi C) hwE)⟩ :
        CT C tM) := by rw [← hv_eq, hv'eq]
    have hw1 : w ≠ 1 := by
      intro h
      apply hv1
      subst h
      rw [hvπ]
      rw [show (⟨(phi C) 1, _⟩ : CT C tM) = 1 from Subtype.ext (map_one (phi C)), map_one]
    have hwz : (w : J) ≠ Max3.z := by
      intro h
      apply hvz
      have hwz' : w = zM := Subtype.ext h
      rw [hvπ]
      subst hwz'
      have hz : zbar = π (⟨(phi C) zM,
          hEG_le_CT (Subgroup.mem_map_of_mem (phi C) hzE₀)⟩ : CT C tM) := by
        simp [zbar, zG, hzG_phi]
      rw [hz]
    obtain ⟨n, hn_t, hn_E, hn_e⟩ := htrans w hwE hw1 hwz
    let nCT' : CT C tM := ⟨(phi C) n, phi_mem_CT_of_commute C hn_t⟩
    let nY' : Y := π nCT'
    have hnY'_norm : nY' ∈ Subgroup.normalizer (Ē : Set Y) :=
      mem_normalizer_of_normalizes_E0 C hE₀t π Ē hĒ hn_t hn_E
        (phi_mem_CT_of_commute C hn_t)
    refine ⟨nY', hnY'_norm, ?_, ?_⟩
    · change π nCT' * zbar * (π nCT')⁻¹ = zbar
      rw [show zbar = π ⟨zG, hzG_CT⟩ from rfl]
      rw [show nCT' = ⟨(phi C) n, phi_mem_CT_of_commute C hn_t⟩ from rfl]
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      have hz_comm : (C.ψ n : G) * zG = zG * (C.ψ n : G) := by
        have h : n * zM = zM * n := by
          apply Subtype.ext
          simpa [zM] using (commute_z_of_mem_M n.2).symm.eq
        have hzG_eq : (C.ψ zM : G) = zG := hψa
        simpa [map_mul, hzG_eq] using
          congrArg (fun z : ↥Max3.M => (C.ψ z : G)) h
      simp [map_mul, map_inv, hz_comm]
    · rw [hvπ]
      change π nCT' * ebarY * (π nCT')⁻¹ =
        π (⟨(phi C) w, hEG_le_CT (Subgroup.mem_map_of_mem (phi C) hwE)⟩ : CT C tM)
      rw [show ebarY = π ⟨e, he_CT⟩ from rfl]
      change (π nCT' : Y) * (π (⟨e, he_CT⟩ : CT C tM) : Y) * (π nCT')⁻¹ =
        (π (⟨(phi C) w, hEG_le_CT (Subgroup.mem_map_of_mem (phi C) hwE)⟩ : CT C tM) : Y)
      rw [show nCT' = ⟨(phi C) n, phi_mem_CT_of_commute C hn_t⟩ from rfl]
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      change (C.ψ n : G) * (C.ψ e₀ : G) * (C.ψ n : G)⁻¹ = (C.ψ w : G)
      simpa [map_mul, map_inv] using
        congrArg (fun z : ↥Max3.M => (C.ψ z : G)) hn_e
  have h1trans : ∀ v ∈ Ē, v ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (Ē : Set Y), n * zbar * n⁻¹ = v := by
    intro v hv hv1
    by_cases hvz : v = zbar
    · subst hvz
      exact ⟨1, Subgroup.one_mem _, by simp⟩
    · have hvz_mem : v * zbar ∈ Ē := Ē.mul_mem hv hzbar_mem
      have hvz1 : v * zbar ≠ 1 := by
        intro h
        apply hvz
        calc v = (v * zbar) * zbar := by rw [mul_assoc, hzbar2, mul_one]
          _ = 1 * zbar := by rw [h]
          _ = zbar := one_mul _
      have hvzz : v * zbar ≠ zbar := by
        intro h
        apply hv1
        calc v = (v * zbar) * zbar := by rw [mul_assoc, hzbar2, mul_one]
          _ = zbar * zbar := by rw [h]
          _ = 1 := hzbar2
      obtain ⟨s, hsN, hs_z, hs_e⟩ := h2trans (v * zbar) hvz_mem hvz1 hvzz
      refine ⟨s * nY, Subgroup.mul_mem _ hsN hnY_norm, ?_⟩
      have hnY_z' : nY * zbar * nY⁻¹ = ebarY * zbar := by
        rw [hnY_z]
        rw [show ebarY = π ⟨e, he_CT⟩ from rfl]
        rw [show (⟨e * zG, (CT C tM).mul_mem he_CT hzG_CT⟩ : CT C tM) =
          (⟨e, he_CT⟩ : CT C tM) * ⟨zG, hzG_CT⟩ from rfl, map_mul]
      calc (s * nY) * zbar * (s * nY)⁻¹ = s * (nY * zbar * nY⁻¹) * s⁻¹ := by group
        _ = s * (ebarY * zbar) * s⁻¹ := by rw [hnY_z']
        _ = (s * ebarY * s⁻¹) * (s * zbar * s⁻¹) := by group
        _ = (v * zbar) * zbar := by rw [hs_e, hs_z]
        _ = v := by rw [mul_assoc, hzbar2, mul_one]
  have hVĒ : CFSG.Open.IsElemAbelian 2 Ē := by
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      intro a b
      apply Subtype.ext
      exact hĒ_comm a a.2 b b.2
    · intro x hx
      rw [pow_two]
      exact hĒ2 x hx
  have h42 : 42 ∣ ((Subgroup.centralizer (Ē : Set Y)).subgroupOf
      (Subgroup.normalizer (Ē : Set Y))).index :=
    dvd_index_of_transitive hzbar_mem hebar_mem hzbar_ne_one hebar_ne_one hebar_ne_zbar
      hcard_Ē h1trans h2trans
  refine ⟨Ē, ?_⟩
  exact g23Two_normalizer hVĒ hcard_Ē (by rw [hCĒ]) h42

theorem isG23Type_quot (C : ThCore G)
    (hψa : (C.ψ ⟨Max3.z, Max3.z_mem_M⟩ : G) = C.z)
    {tM : ↥Max3.M} (htM : orderOf tM = 3)
    {E₀ : Subgroup ↥Max3.M} {e₀ : ↥Max3.M} (he₀ : e₀ ∈ E₀) (he₀1 : e₀ ≠ 1)
    (he₀z : (e₀ : J) ≠ Max3.z)
    (hE₀c : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) (hE₀2 : ∀ x ∈ E₀, x * x = 1)
    (hE₀8 : Nat.card E₀ = 8) (hzE₀ : (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) ∈ E₀)
    (hE₀t : ∀ x ∈ E₀, x * tM = tM * x)
    (hCE : ∀ m : ↥Max3.M, m * tM = tM * m → (∀ x ∈ E₀, m * x = x * m) →
      ∃ x ∈ E₀, ∃ k : ℕ, m = x * tM ^ k)
    (htrans : ∀ w ∈ E₀, w ≠ 1 → (w : J) ≠ Max3.z → ∃ n : ↥Max3.M, n * tM = tM * n ∧
      (∀ x ∈ E₀, n * x * n⁻¹ ∈ E₀) ∧ n * e₀ * n⁻¹ = w)
    (hZt : ∀ w : ↥Max3.M, (w : J) ∈ Max3.Q → w * tM = tM * w → w ≠ 1 → (w : J) ≠ Max3.z →
      ∃ q : ↥Max3.M, (q : J) ∈ Max3.Q ∧ q * tM = tM * q ∧ q * w ≠ w * q)
    (hC13 : ∃ g : G, g * C.z * g⁻¹ = (C.ψ e₀ : G) ∧
      ∀ x ∈ E₀, ∃ q : ↥Max3.M, (q : J) ∈ Max3.Q ∧ (C.ψ q : G) = g⁻¹ * (C.ψ x : G) * g)
    (hy : ∃ y ∈ Subgroup.centralizer ({(C.ψ tM : G)} : Set G),
      y * (C.ψ e₀ : G) * y⁻¹ = C.z)
    {Y : Type} [Group Y] (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Y)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
    (hG1 : ∃ H H₁ H₂ : Subgroup Y, CFSG.Quasithin.G23Type.G23One H H₁ H₂) :
    CFSG.Quasithin.G23Type.IsG23Type Y := by
  obtain ⟨H, H₁, H₂, h1⟩ := hG1
  obtain ⟨V, h2⟩ := exists_g23Two_quot C hψa htM he₀ he₀1 he₀z hE₀c hE₀2 hE₀8 hzE₀ hE₀t hCE
    htrans hZt hC13 hy π hπ hker
  exact ⟨H, H₁, H₂, _, h1, h2⟩

end CFSG.Sporadic.Th.Recog
