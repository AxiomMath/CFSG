module

public import CFSG.Sporadic.Th.Recog.Setting
public import CFSG.Sporadic.Th.Recog.AltNine
public import CFSG.Monster.B.Short.InvolutionCentralizer
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG
open CFSG.Sporadic.Th.Max3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private noncomputable def phi (C : ThCore G) :
    ↥Max3.M →* G where
  toFun x := C.ψ x
  map_one' := by
    show (C.ψ 1 : G) = 1
    rw [map_one]
    rfl
  map_mul' x y := by
    show (C.ψ (x * y) : G) = (C.ψ x : G) * (C.ψ y : G)
    rw [map_mul]
    rfl

private theorem phi_apply (C : ThCore G)
    (x : ↥Max3.M) : phi C x = (C.ψ x : G) :=
  rfl

private theorem phi_injective (C : ThCore G) :
    Function.Injective (phi C) := by
  intro x y h
  exact C.ψ.injective (Subtype.ext h)

private theorem phi_range (C : ThCore G) :
    (phi C).range = Subgroup.centralizer ({C.z} : Set G) := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact (C.ψ x).2
  · intro hg
    refine ⟨C.ψ.symm ⟨g, hg⟩, ?_⟩
    change (C.ψ (C.ψ.symm ⟨g, hg⟩) : G) = g
    rw [C.ψ.apply_symm_apply]

private noncomputable def QG (C : ThCore G) : Subgroup G :=
  (Max3.Q.subgroupOf Max3.M).map (phi C)

private theorem mem_QG_iff (C : ThCore G) {x : G} :
    x ∈ QG C ↔ ∃ q : ↥Max3.M, (q : J) ∈ Max3.Q ∧ phi C q = x := by
  rw [QG, Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, hqx⟩
    exact ⟨q, Subgroup.mem_subgroupOf.mp hq, hqx⟩
  · rintro ⟨q, hq, hqx⟩
    exact ⟨q, Subgroup.mem_subgroupOf.mpr hq, hqx⟩

private theorem QG_le_centralizer (C : ThCore G) :
    QG C ≤ Subgroup.centralizer ({C.z} : Set G) := by
  intro x hx
  obtain ⟨q, -, rfl⟩ := (mem_QG_iff C).mp hx
  exact (C.ψ q).2

private theorem mem_Q_of_mem_QG (C : ThCore G)
    {x : ↥Max3.M} (hx : phi C x ∈ QG C) : (x : J) ∈ Max3.Q := by
  obtain ⟨q, hq, hqx⟩ := (mem_QG_iff C).mp hx
  have hqeq : q = x := phi_injective C hqx
  rwa [← hqeq]

private theorem QG_map_conj_eq (C : ThCore G)
    {c : G}
    (hc : c ∈ Subgroup.centralizer ({C.z} : Set G)) :
    (QG C).map (MulAut.conj c).toMonoidHom = QG C := by
  have hc_range : c ∈ (phi C).range := by
    rw [phi_range C]
    exact hc
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hc_range
  haveI hN : (Max3.Q.subgroupOf Max3.M).Normal := Max3.normal_Q_subgroupOf_M
  have hy_norm : y ∈ Subgroup.normalizer
      ((Max3.Q.subgroupOf Max3.M) : Set ↥Max3.M) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top y
  have hy_map : (Max3.Q.subgroupOf Max3.M).map
      (MulAut.conj y).toMonoidHom = Max3.Q.subgroupOf Max3.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hy_norm
  rw [← hy]
  have hcomp : (MulAut.conj (phi C y)).toMonoidHom.comp (phi C) =
      (phi C).comp (MulAut.conj y).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulAut.conj_apply]
    change (phi C y) * (phi C x) * (phi C y)⁻¹ = phi C (y * x * y⁻¹)
    rw [phi_apply C y, phi_apply C x, phi_apply C (y * x * y⁻¹)]
    rw [map_mul, map_mul, map_inv]
    rfl
  calc
    (QG C).map (MulAut.conj (phi C y)).toMonoidHom =
        ((Max3.Q.subgroupOf Max3.M).map (phi C)).map
          (MulAut.conj (phi C y)).toMonoidHom := rfl
    _ = (Max3.Q.subgroupOf Max3.M).map
          ((MulAut.conj (phi C y)).toMonoidHom.comp (phi C)) := by
      rw [Subgroup.map_map]
    _ = (Max3.Q.subgroupOf Max3.M).map
          ((phi C).comp (MulAut.conj y).toMonoidHom) := by
      rw [hcomp]
    _ = ((Max3.Q.subgroupOf Max3.M).map (MulAut.conj y).toMonoidHom).map (phi C) := by
      rw [Subgroup.map_map]
    _ = QG C := by
      rw [hy_map]
      rfl

private theorem card_centralizer_phi (C : ThCore G)
    (x : ↥Max3.M) :
    Nat.card (Subgroup.centralizer ({x} : Set ↥Max3.M)) =
      Nat.card ↥(Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({(C.ψ x : G)} : Set G)) := by
  let K : Subgroup ↥Max3.M := Subgroup.centralizer ({x} : Set ↥Max3.M)
  let H : Subgroup G := Subgroup.centralizer ({C.z} : Set G) ⊓
    Subgroup.centralizer ({(C.ψ x : G)} : Set G)
  have hmap : K.map (phi C) = H := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨(C.ψ a).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [phi_apply C a] at *
      simpa only [map_mul, Subgroup.coe_mul] using
        congrArg (fun t : ↥Max3.M => (C.ψ t : G))
          (Subgroup.mem_centralizer_singleton_iff.mp ha)
    · intro hy
      obtain ⟨hz, hx⟩ := Subgroup.mem_inf.mp hy
      have hy_range : y ∈ (phi C).range := by
        rw [phi_range C]
        exact hz
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy_range
      refine ⟨a, ?_, rfl⟩
      change a ∈ Subgroup.centralizer ({x} : Set ↥Max3.M)
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [phi_apply C a] at hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      apply C.ψ.injective
      apply Subtype.ext
      simpa only [map_mul, Subgroup.coe_mul] using hx
  calc
    Nat.card ↥K = Nat.card (K.map (phi C)) :=
      (Subgroup.card_map_of_injective (K := K) (phi_injective C)).symm
    _ = Nat.card ↥H := by rw [hmap]

theorem mem_Q_of_card_centralizer
    {k : ↥Max3.M} (hk : k * k = 1)
    (hC : Nat.card (Subgroup.centralizer ({k} : Set ↥Max3.M)) = 2 ^ 14 * 21) :
    (k : J) ∈ Max3.Q := by
  classical
  by_contra hkQ
  let CM : Subgroup ↥Max3.M := Subgroup.centralizer ({k} : Set ↥Max3.M)
  let f : ↥CM →* ↥(alternatingGroup (Fin 9)) :=
    Max3.InvRep.kap.comp CM.subtype
  have hkQ' : Max3.InvRep.kap k ≠ 1 := fun h =>
    hkQ (Max3.InvRep.kap_eq_one_iff.mp h)
  have hsq : Max3.InvRep.kap k * Max3.InvRep.kap k = 1 := by
    rw [← map_mul, hk, map_one]
  have hord : orderOf (Max3.InvRep.kap k) = 2 :=
    orderOf_eq_prime (by simpa [sq] using hsq) hkQ'
  have hker : Nat.card ↥f.ker ≤ 512 := by
    have hle : (f.ker).map CM.subtype ≤ Max3.Q.subgroupOf Max3.M := by
      rintro y ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Max3.InvRep.kap_eq_one_iff.mp (by
        have hx' := hx
        change Max3.InvRep.kap (x : ↥Max3.M) = 1 at hx'
        exact hx'))
    have hcard := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (K := f.ker) CM.subtype_injective] at hcard
    have hQsub : Nat.card ↥(Max3.Q.subgroupOf Max3.M) = 512 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Max3.Q_le_M).toEquiv,
        Max3.card_Q]
    rwa [hQsub] at hcard
  have hrange : Nat.card ↥f.range ≤ 480 := by
    have hle : f.range ≤ Subgroup.centralizer
        ({(Max3.InvRep.kap k)} : Set (alternatingGroup (Fin 9))) := by
      intro y hy
      obtain ⟨x, -, rfl⟩ := MonoidHom.mem_range.mp hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      change Max3.InvRep.kap (x : ↥Max3.M) * Max3.InvRep.kap k =
        Max3.InvRep.kap k * Max3.InvRep.kap (x : ↥Max3.M)
      simpa only [map_mul] using congrArg Max3.InvRep.kap
        (Subgroup.mem_centralizer_singleton_iff.mp x.2)
    calc
      Nat.card ↥f.range ≤ Nat.card ↥(Subgroup.centralizer
          ({(Max3.InvRep.kap k)} : Set (alternatingGroup (Fin 9)))) :=
        Subgroup.card_le_of_le hle
      _ ≤ 480 := card_centralizer_le_of_orderOf_eq_two hord
  have hmul := Subgroup.card_ker_mul_card_range f
  have hle : 2 ^ 14 * 21 ≤ 512 * 480 := by
    calc
      2 ^ 14 * 21 = Nat.card ↥CM := hC.symm
      _ = Nat.card ↥f.ker * Nat.card ↥f.range := hmul.symm
      _ ≤ 512 * 480 := Nat.mul_le_mul hker hrange
  norm_num at hle

theorem card_Q_inf_centralizer
    {k : ↥Max3.M} (hkQ : (k : J) ∈ Max3.Q)
    (hkz : (k : J) ≠ Max3.z) (hk1 : k ≠ 1) :
    Nat.card ↥(Max3.Q.subgroupOf Max3.M ⊓ Subgroup.centralizer ({k} : Set ↥Max3.M)) =
      2 ^ 8 := by
  classical
  let P : Subgroup ↥Max3.M := Max3.Q.subgroupOf Max3.M ⊓
    Subgroup.centralizer ({k} : Set ↥Max3.M)
  let PJ : Subgroup J := Max3.Q ⊓
    Subgroup.centralizer ({(k : J)} : Set J)
  let r : ↥Max3.Q := ⟨(k : J), hkQ⟩
  have hzord : orderOf Max3.z = 2 :=
    orderOf_eq_prime (by simpa [sq] using Max3.z_mul_self) Max3.z_ne_one
  have hr_not_center : r ∉ Subgroup.center ↥Max3.Q := by
    intro hr
    have hmem : r ∈ (Subgroup.zpowers Max3.z).subgroupOf Max3.Q := by
      rwa [← Max3.center_Q]
    have hmemJ : (r : J) ∈ Subgroup.zpowers Max3.z := Subgroup.mem_subgroupOf.mp hmem
    rw [CFSG.Monster.B.Short.mem_zpowers_iff_of_orderOf_eq_two hzord] at hmemJ
    rcases hmemJ with h | h
    · exact hk1 (Subtype.ext (by simpa [r] using h))
    · exact hkz (by simpa [r] using h)
  have hcardQ : Nat.card ↥Max3.Q = 2 ^ (1 + 2 * 4) := by
    rw [Max3.card_Q]
    norm_num
  have hD : Nat.card ↥(CFSG.Monster.B.Short.invCent r) = 2 ^ 8 := by
    have h := CFSG.Monster.B.Short.natCard_invCent (P := ↥Max3.Q) (r := r) (n := 4)
      Max3.isExtraspecialPGroup_Q hcardQ hr_not_center
    simpa using h
  have hP_map : P.map Max3.M.subtype = PJ := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hpQ, hpC⟩ := Subgroup.mem_inf.mp hp
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hpQ, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      change ((p : ↥Max3.M) : J) * ((k : ↥Max3.M) : J) =
        ((k : ↥Max3.M) : J) * ((p : ↥Max3.M) : J)
      simpa only [Subgroup.coe_mul] using congrArg (Subtype.val : ↥Max3.M → J)
        (Subgroup.mem_centralizer_singleton_iff.mp hpC)
    · intro hy
      obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
      refine ⟨⟨y, Max3.Q_le_M hyQ⟩, ?_, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hyQ, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hyC
  have hPJ_map : PJ = (CFSG.Monster.B.Short.invCent r).map Max3.Q.subtype := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_map.mpr ⟨⟨y, hyQ⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hyC
    · rintro ⟨q, hq, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨q.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      change ((q : ↥Max3.Q) : J) * ((k : ↥Max3.M) : J) =
        ((k : ↥Max3.M) : J) * ((q : ↥Max3.Q) : J)
      simpa only [Subgroup.coe_mul] using congrArg (Subtype.val : ↥Max3.Q → J)
        (Subgroup.mem_centralizer_singleton_iff.mp hq)
  calc
    Nat.card ↥P = Nat.card (P.map Max3.M.subtype) :=
      (Subgroup.card_map_of_injective (K := P) Max3.M.subtype_injective).symm
    _ = Nat.card ↥PJ := by rw [hP_map]
    _ = Nat.card ((CFSG.Monster.B.Short.invCent r).map Max3.Q.subtype) := by rw [hPJ_map]
    _ = Nat.card ↥(CFSG.Monster.B.Short.invCent r) :=
      Subgroup.card_map_of_injective (K := CFSG.Monster.B.Short.invCent r)
        Max3.Q.subtype_injective
    _ = 2 ^ 8 := hD

private theorem card_QG_inf_centralizer (C : ThCore G)
    {x : ↥Max3.M} (hxQ : (x : J) ∈ Max3.Q)
    (hx1 : x ≠ 1) (hxz : (x : J) ≠ Max3.z) :
    Nat.card ↥(QG C ⊓ Subgroup.centralizer ({(C.ψ x : G)} : Set G)) = 2 ^ 8 := by
  let PM : Subgroup ↥Max3.M := Max3.Q.subgroupOf Max3.M ⊓
    Subgroup.centralizer ({x} : Set ↥Max3.M)
  have hPM : Nat.card ↥PM = 2 ^ 8 := card_Q_inf_centralizer hxQ hxz hx1
  have hmap : PM.map (phi C) = QG C ⊓
      Subgroup.centralizer ({(C.ψ x : G)} : Set G) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hpQ, hpc⟩ := Subgroup.mem_inf.mp hp
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨p, hpQ, rfl⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        change (C.ψ p : G) * (C.ψ x : G) = (C.ψ x : G) * (C.ψ p : G)
        simpa only [map_mul, Subgroup.coe_mul] using
          congrArg (fun t : ↥Max3.M => (C.ψ t : G))
            (Subgroup.mem_centralizer_singleton_iff.mp hpc)
    · rintro hy
      obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨p, hpQ, rfl⟩ := (mem_QG_iff C).mp hyQ
      refine ⟨p, Subgroup.mem_inf.mpr ⟨hpQ, ?_⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
      change (C.ψ p : G) * (C.ψ x : G) = (C.ψ x : G) * (C.ψ p : G) at hyC
      apply C.ψ.injective
      apply Subtype.ext
      simpa only [map_mul, Subgroup.coe_mul] using hyC
  calc
    Nat.card ↥(QG C ⊓ Subgroup.centralizer ({(C.ψ x : G)} : Set G)) =
        Nat.card (PM.map (phi C)) := by rw [hmap]
    _ = Nat.card ↥PM := Subgroup.card_map_of_injective (phi_injective C)
    _ = 2 ^ 8 := hPM

theorem exists_conj_le_Q
    (C : ThCore G)
    (hψa : (C.ψ ⟨Max3.z, Max3.z_mem_M⟩ : G) = C.z)
    {E₀ : Subgroup ↥Max3.M} {e₀ : ↥Max3.M} (he₀Q : (e₀ : J) ∈ Max3.Q)
    (he₀2 : e₀ * e₀ = 1) (he₀1 : e₀ ≠ 1) (he₀z : (e₀ : J) ≠ Max3.z)
    (hCe : Nat.card (Subgroup.centralizer ({e₀} : Set ↥Max3.M)) = 2 ^ 14 * 21)
    (hA : ∀ A : Subgroup ↥Max3.M, (∀ x ∈ A, (x : J) ∈ Max3.Q ∧ x * e₀ = e₀ * x) →
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      (∀ c : ↥Max3.M, c * e₀ = e₀ * c → ∀ x ∈ A, c * x * c⁻¹ ∈ A) →
      (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) ∈ A → e₀ ∈ A → Nat.card A = 4 ∨ E₀ ≤ A)
    (hm : ∃ m₁ m₂ : ↥Max3.M, m₁ * e₀ = e₀ * m₁ ∧ m₂ * e₀ = e₀ * m₂ ∧
      (∃ k : ℕ, m₁ ^ 2 ^ k = 1) ∧ (∃ k : ℕ, m₂ ^ 2 ^ k = 1) ∧ 3 ∣ orderOf (m₁ * m₂)) :
    ∃ g : G, g * C.z * g⁻¹ = (C.ψ e₀ : G) ∧
      ∀ x ∈ E₀, ∃ q : ↥Max3.M, (q : J) ∈ Max3.Q ∧
        (C.ψ q : G) = g⁻¹ * (C.ψ x : G) * g := by
  classical
  let e : G := (C.ψ e₀ : G)
  let QG0 : Subgroup G := QG C
  have hzM2 : (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) *
      (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) = 1 :=
    Subtype.ext Max3.z_mul_self
  have hzG2 : C.z * C.z = 1 := by
    have h : C.ψ ⟨Max3.z, Max3.z_mem_M⟩ * C.ψ ⟨Max3.z, Max3.z_mem_M⟩ = 1 := by
      rw [← map_mul, hzM2, map_one]
    simpa [hψa] using
      congrArg (fun t : ↥(Subgroup.centralizer ({C.z} : Set G)) => (t : G)) h
  have hzG_ne_one : C.z ≠ 1 := by
    rw [← hψa]
    intro h
    have hzM1 : (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) = 1 :=
      C.ψ.injective (Subtype.ext (by simpa using h))
    have hzJ : (Max3.z : J) = 1 := by simpa using hzM1
    exact Max3.z_ne_one hzJ
  have he2 : e * e = 1 := by
    have h : C.ψ e₀ * C.ψ e₀ = 1 := by
      rw [← map_mul, he₀2, map_one]
    simpa [e] using congrArg (fun t : ↥(Subgroup.centralizer ({C.z} : Set G)) => (t : G)) h
  have he1 : e ≠ 1 := by
    intro h
    apply he₀1
    apply C.ψ.injective
    apply Subtype.ext
    simpa [e] using h
  have he_ne_z : e ≠ C.z := by
    intro h
    apply he₀z
    have h' : (C.ψ e₀ : G) = (C.ψ ⟨Max3.z, Max3.z_mem_M⟩ : G) :=
      h.trans hψa.symm
    have hEq : e₀ = (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) :=
      C.ψ.injective (Subtype.ext h')
    rw [hEq]
  have horde : orderOf e = 2 := orderOf_eq_prime (by simpa [sq] using he2) he1
  obtain ⟨g, hg⟩ := C.conj e horde
  let h : G := g⁻¹ * C.z * g
  have hghz : g * h * g⁻¹ = C.z := by
    dsimp [h]
    group
  have hh2 : h * h = 1 := by
    calc h * h = g⁻¹ * (C.z * C.z) * g := by
          dsimp [h]
          group
      _ = 1 := by rw [hzG2]; group
  have hze : C.z * e = e * C.z := by
    have hmem : (C.ψ e₀ : G) ∈ Subgroup.centralizer ({C.z} : Set G) := (C.ψ e₀).2
    exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm
  have hze' : C.z * (g * C.z * g⁻¹) = (g * C.z * g⁻¹) * C.z := by
    rw [← hg] at hze
    exact hze
  have hh_comm : h * C.z = C.z * h := by
    calc h * C.z = g⁻¹ * (C.z * (g * C.z * g⁻¹)) * g := by
          dsimp [h]
          group
      _ = g⁻¹ * ((g * C.z * g⁻¹) * C.z) * g := by rw [hze']
      _ = C.z * h := by
          dsimp [h]
          group
  have hh_range : h ∈ (phi C).range := by
    rw [phi_range C]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hh_comm
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hh_range
  have hk2 : k * k = 1 := by
    apply phi_injective C
    rw [map_mul, hk, map_one]
    exact hh2
  have hcard_conj : Nat.card ↥(Subgroup.centralizer ({C.z} : Set G) ⊓
      Subgroup.centralizer ({h} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G)) := by
    have hmap : (Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({h} : Set G)).map (MulAut.conj g).toMonoidHom =
        Subgroup.centralizer ({e} : Set G) ⊓
          Subgroup.centralizer ({C.z} : Set G) := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
        CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton,
        CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton, hg, hghz]
    have hcard := Subgroup.card_map_of_injective
      (f := (MulAut.conj g).toMonoidHom)
      (K := Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({h} : Set G)) (MulAut.conj g).injective
    rw [hmap, inf_comm] at hcard
    exact hcard.symm
  have hCe' : Nat.card ↥(Subgroup.centralizer ({C.z} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) = 2 ^ 14 * 21 := by
    rw [← card_centralizer_phi C e₀]
    exact hCe
  have hCk : Nat.card (Subgroup.centralizer ({k} : Set ↥Max3.M)) = 2 ^ 14 * 21 := by
    rw [card_centralizer_phi C k, ← phi_apply C k, hk, hcard_conj, hCe']
  have hkQ : (k : J) ∈ Max3.Q := mem_Q_of_card_centralizer hk2 hCk
  have hhQG : h ∈ QG0 := by
    rw [← hk]
    exact Subgroup.mem_map.mpr ⟨k, Subgroup.mem_subgroupOf.mpr hkQ, rfl⟩
  have hk1 : k ≠ 1 := by
    intro hk1
    have hh1 : h = 1 := by rw [← hk, hk1, map_one]
    have hz1 : C.z = 1 := by
      calc C.z = g * h * g⁻¹ := hghz.symm
        _ = 1 := by rw [hh1]; group
    exact hzG_ne_one hz1
  have hkz : (k : J) ≠ Max3.z := by
    intro hkz
    have hkzM : k = (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) := Subtype.ext hkz
    have hh_z : h = C.z := by
      calc h = phi C k := hk.symm
        _ = phi C (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) := by rw [hkzM]
        _ = C.z := by rw [phi_apply C, hψa]
    have he_z : e = C.z := by
      calc e = g * C.z * g⁻¹ := hg.symm
        _ = g * h * g⁻¹ := by rw [hh_z]
        _ = C.z := hghz
    exact he_ne_z he_z
  let Q' : Subgroup G := QG0.map (MulAut.conj g).toMonoidHom
  let A0 : Subgroup ↥Max3.M := (QG0 ⊓ Q').comap (phi C)
  have hQprime_le_Ce : Q' ≤ Subgroup.centralizer ({e} : Set G) := by
    intro y hy
    obtain ⟨x, hxQG, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxcomm : x * C.z = C.z * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (QG_le_centralizer C hxQG)
    calc (g * x * g⁻¹) * e = (g * x * g⁻¹) * (g * C.z * g⁻¹) := by rw [← hg]
      _ = g * (x * C.z) * g⁻¹ := by group
      _ = g * (C.z * x) * g⁻¹ := by rw [hxcomm]
      _ = (g * C.z * g⁻¹) * (g * x * g⁻¹) := by group
      _ = e * (g * x * g⁻¹) := by rw [hg]
  have hQG_comm {x y : G} (hx : x ∈ QG0) (hy : y ∈ QG0) :
      x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = C.z := by
    obtain ⟨a, haQ, rfl⟩ := (mem_QG_iff C).mp hx
    obtain ⟨b, hbQ, rfl⟩ := (mem_QG_iff C).mp hy
    have hcJ : ((a * b * a⁻¹ * b⁻¹ : ↥Max3.M) : J) ∈ Subgroup.zpowers Max3.z := by
      simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using
        Max3.AltQuot.comm_mem_zpowers (m := (a : J)) (g := (b : J)) haQ hbQ
    have hzord : orderOf Max3.z = 2 :=
      orderOf_eq_prime (by simpa [sq] using Max3.z_mul_self) Max3.z_ne_one
    rw [CFSG.Monster.B.Short.mem_zpowers_iff_of_orderOf_eq_two hzord] at hcJ
    have hmap : (phi C a) * (phi C b) * (phi C a)⁻¹ * (phi C b)⁻¹ =
        phi C (a * b * a⁻¹ * b⁻¹) := by
      simp only [map_mul, map_inv]
    rw [hmap]
    rcases hcJ with hc | hc
    · left
      have hMeq : a * b * a⁻¹ * b⁻¹ = (1 : ↥Max3.M) := by
        apply Subtype.ext
        simpa using hc
      rw [hMeq, map_one]
    · right
      have hMeq : a * b * a⁻¹ * b⁻¹ =
          (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) := by
        apply Subtype.ext
        simpa using hc
      rw [hMeq, phi_apply C, hψa]
  have hQprime_comm {x y : G} (hx : x ∈ Q') (hy : y ∈ Q') :
      x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = e := by
    obtain ⟨a, haQG, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hbQG, rfl⟩ := Subgroup.mem_map.mp hy
    have hc := hQG_comm haQG hbQG
    have hmap : (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ *
        (g * b * g⁻¹)⁻¹ = g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ := by group
    change (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ *
        (g * b * g⁻¹)⁻¹ = 1 ∨ (g * a * g⁻¹) * (g * b * g⁻¹) *
        (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ = e
    rw [hmap]
    rcases hc with hc | hc
    · left
      rw [hc]
      group
    · right
      rw [hc]
      exact hg
  have hA0_mem_Q {x : ↥Max3.M} (hx : x ∈ A0) : (x : J) ∈ Max3.Q :=
    mem_Q_of_mem_QG C (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).1
  have hA0_comm {x : ↥Max3.M} (hx : x ∈ A0) : x * e₀ = e₀ * x := by
    have hxQ' : phi C x ∈ Q' :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).2
    have hxe : phi C x * e = e * phi C x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hQprime_le_Ce hxQ')
    apply phi_injective C
    rw [map_mul, map_mul, phi_apply C e₀]
    exact hxe
  have hA0_abelian : ∀ x ∈ A0, ∀ y ∈ A0, x * y = y * x := by
    intro x hx y hy
    have hxQG : phi C x ∈ QG0 :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).1
    have hyQG : phi C y ∈ QG0 :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hy)).1
    have hxQ' : phi C x ∈ Q' :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).2
    have hyQ' : phi C y ∈ Q' :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hy)).2
    have hcommQG := hQG_comm hxQG hyQG
    have hcommQ' := hQprime_comm hxQ' hyQ'
    have hcomm1 : phi C x * phi C y * (phi C x)⁻¹ * (phi C y)⁻¹ = 1 := by
      rcases hcommQG with h | h
      · exact h
      · rcases hcommQ' with h' | h'
        · exact absurd (h.symm.trans h') hzG_ne_one
        · exact absurd (h.symm.trans h').symm he_ne_z
    have hcomm : ⁅phi C x, phi C y⁆ = 1 := by
      rwa [commutatorElement_def]
    have hxy := commutatorElement_eq_one_iff_mul_comm.mp hcomm
    apply phi_injective C
    rw [map_mul, map_mul]
    exact hxy
  have hQprime_map_conj {c : G} (hc : c ∈ Subgroup.centralizer ({C.z} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) :
      Q'.map (MulAut.conj c).toMonoidHom = Q' := by
    have hcz : c ∈ Subgroup.centralizer ({C.z} : Set G) :=
      (Subgroup.mem_inf.mp hc).1
    have hce : c ∈ Subgroup.centralizer ({e} : Set G) :=
      (Subgroup.mem_inf.mp hc).2
    have hd : g⁻¹ * c * g ∈ Subgroup.centralizer ({C.z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hce' : c * e = e * c :=
        Subgroup.mem_centralizer_singleton_iff.mp hce
      have h := congrArg (fun t => g⁻¹ * t * g) hce'
      calc (g⁻¹ * c * g) * C.z = g⁻¹ * (c * (g * C.z * g⁻¹)) * g := by group
        _ = g⁻¹ * (c * e) * g := by rw [← hg]
        _ = g⁻¹ * (e * c) * g := h
        _ = g⁻¹ * ((g * C.z * g⁻¹) * c) * g := by rw [← hg]
        _ = C.z * (g⁻¹ * c * g) := by group
    calc Q'.map (MulAut.conj c).toMonoidHom =
        ((QG0.map (MulAut.conj g).toMonoidHom)).map
          (MulAut.conj c).toMonoidHom := rfl
      _ = QG0.map ((MulAut.conj c).toMonoidHom.comp
          (MulAut.conj g).toMonoidHom) := by rw [Subgroup.map_map]
      _ = QG0.map ((MulAut.conj g).toMonoidHom.comp
          (MulAut.conj (g⁻¹ * c * g)).toMonoidHom) := by
        congr 1
        ext x
        change (MulAut.conj c) ((MulAut.conj g) x) =
          (MulAut.conj g) ((MulAut.conj (g⁻¹ * c * g)) x)
        simp only [MulAut.conj_apply]
        group
      _ = (QG0.map (MulAut.conj (g⁻¹ * c * g)).toMonoidHom).map
          (MulAut.conj g).toMonoidHom := by rw [Subgroup.map_map]
      _ = QG0.map (MulAut.conj g).toMonoidHom := by
        rw [QG_map_conj_eq C hd]
      _ = Q' := rfl
  have hA0_inv : ∀ c : ↥Max3.M, c * e₀ = e₀ * c → ∀ x ∈ A0, c * x * c⁻¹ ∈ A0 := by
    intro c hc x hx
    have hxQG : phi C x ∈ QG0 :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).1
    have hxQ' : phi C x ∈ Q' :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).2
    have hcGz : phi C c ∈ Subgroup.centralizer ({C.z} : Set G) := (C.ψ c).2
    have hcGe : phi C c ∈ Subgroup.centralizer ({e} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [phi_apply C c]
      simpa [e, map_mul] using
        congrArg (fun t : ↥Max3.M => (C.ψ t : G)) hc
    have hcCg : phi C c ∈ Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hcGz, hcGe⟩
    have hmemQG : phi C c * phi C x * (phi C c)⁻¹ ∈ QG0 := by
      have hmap := QG_map_conj_eq C hcGz
      have hthis : (MulAut.conj (phi C c)).toMonoidHom (phi C x) ∈
          QG0.map (MulAut.conj (phi C c)).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨phi C x, hxQG, rfl⟩
      rw [hmap] at hthis
      change (MulAut.conj (phi C c)) (phi C x) ∈ QG0 at hthis
      simpa only [MulAut.conj_apply] using hthis
    have hmemQ' : phi C c * phi C x * (phi C c)⁻¹ ∈ Q' := by
      have hmap := hQprime_map_conj hcCg
      have hthis : (MulAut.conj (phi C c)).toMonoidHom (phi C x) ∈
          Q'.map (MulAut.conj (phi C c)).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨phi C x, hxQ', rfl⟩
      rw [hmap] at hthis
      change (MulAut.conj (phi C c)) (phi C x) ∈ Q' at hthis
      simpa only [MulAut.conj_apply] using hthis
    rw [Subgroup.mem_comap]
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.mem_inf.mpr ⟨hmemQG, hmemQ'⟩
  have hzM_mem_A0 : (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) ∈ A0 := by
    rw [Subgroup.mem_comap]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mem_map.mpr
        ⟨⟨Max3.z, Max3.z_mem_M⟩, Subgroup.mem_subgroupOf.mpr Max3.z_mem_Q, rfl⟩
    · refine Subgroup.mem_map.mpr ⟨h, hhQG, ?_⟩
      change (MulAut.conj g) h = phi C (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M)
      rw [MulAut.conj_apply, hghz, phi_apply C, hψa]
  have he₀_mem_A0 : e₀ ∈ A0 := by
    rw [Subgroup.mem_comap]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mem_map.mpr
        ⟨e₀, Subgroup.mem_subgroupOf.mpr he₀Q, rfl⟩
    · have hzQG : C.z ∈ QG0 := by
        refine Subgroup.mem_map.mpr
          ⟨⟨Max3.z, Max3.z_mem_M⟩, Subgroup.mem_subgroupOf.mpr Max3.z_mem_Q, ?_⟩
        rw [phi_apply C, hψa]
      refine Subgroup.mem_map.mpr ⟨C.z, hzQG, ?_⟩
      change (MulAut.conj g) C.z = phi C e₀
      rw [MulAut.conj_apply, hg]
      rfl
  rcases hA A0 (fun x hx => ⟨hA0_mem_Q hx, hA0_comm hx⟩) hA0_abelian
    hA0_inv hzM_mem_A0 he₀_mem_A0 with hA4 | hAE
  · have hcardA0 : Nat.card A0 = Nat.card ↥(QG0 ⊓ Q') := by
      have hHrange : QG0 ⊓ Q' ≤ (phi C).range := by
        intro x hx
        rw [phi_range C]
        exact QG_le_centralizer C (Subgroup.mem_inf.mp hx).1
      have hmap : Subgroup.map (phi C) A0 = QG0 ⊓ Q' :=
        Subgroup.map_comap_eq_self hHrange
      calc Nat.card A0 = Nat.card (Subgroup.map (phi C) A0) :=
            (Subgroup.card_map_of_injective (K := A0) (phi_injective C)).symm
        _ = Nat.card ↥(QG0 ⊓ Q') := by rw [hmap]
    have hcardNP : Nat.card ↥(QG0 ⊓ Q') = 4 := by
      rw [← hcardA0]
      exact hA4
    let P : Subgroup G := QG0 ⊓ Subgroup.centralizer ({e} : Set G)
    let N : Subgroup G := Q' ⊓ Subgroup.centralizer ({C.z} : Set G)
    have hPcard : Nat.card ↥P = 2 ^ 8 := by
      simpa [P, QG0, e] using card_QG_inf_centralizer C he₀Q he₀1 he₀z
    have hNmap : N.map (MulAut.conj g⁻¹).toMonoidHom =
        QG0 ⊓ Subgroup.centralizer ({h} : Set G) := by
      have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp
          (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
        ext x
        change (MulAut.conj g⁻¹) ((MulAut.conj g) x) = x
        simp only [MulAut.conj_apply]
        group
      have hQ'map : Q'.map (MulAut.conj g⁻¹).toMonoidHom = QG0 := by
        calc Q'.map (MulAut.conj g⁻¹).toMonoidHom =
            (QG0.map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj g⁻¹).toMonoidHom := rfl
          _ = QG0.map ((MulAut.conj g⁻¹).toMonoidHom.comp
              (MulAut.conj g).toMonoidHom) := by rw [Subgroup.map_map]
          _ = QG0.map (MonoidHom.id G) := by rw [hcomp]
          _ = QG0 := by simp
      have hCzmap : (Subgroup.centralizer ({C.z} : Set G)).map
          (MulAut.conj g⁻¹).toMonoidHom =
          Subgroup.centralizer ({h} : Set G) := by
        simpa [h] using
          CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton g⁻¹ C.z
      dsimp only [N]
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective, hQ'map, hCzmap]
    have hNcard : Nat.card ↥N = 2 ^ 8 := by
      have hcard := Subgroup.card_map_of_injective
        (f := (MulAut.conj g⁻¹).toMonoidHom) (K := N)
        (MulAut.conj g⁻¹).injective
      rw [hNmap] at hcard
      rw [← hcard, ← hk]
      simpa [QG0, phi_apply] using card_QG_inf_centralizer C hkQ hk1 hkz
    have hNPEq : N ⊓ P = QG0 ⊓ Q' := by
      ext x
      constructor
      · rintro ⟨⟨hxQ', hxCz⟩, ⟨hxQG, hxCe⟩⟩
        exact ⟨hxQG, hxQ'⟩
      · rintro ⟨hxQG, hxQ'⟩
        exact ⟨⟨hxQ', QG_le_centralizer C hxQG⟩,
          ⟨hxQG, hQprime_le_Ce hxQ'⟩⟩
    have hNPcard : Nat.card ↥(N ⊓ P) = 4 := by
      rw [hNPEq]
      exact hcardNP
    have hP_le_Cg : P ≤ Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G) :=
      le_inf (inf_le_left.trans (QG_le_centralizer C)) inf_le_right
    have hN_le_Cg : N ≤ Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G) :=
      le_inf inf_le_right (inf_le_left.trans hQprime_le_Ce)
    have hP_norm : Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G) ≤
        Subgroup.normalizer (P : Set G) := by
      intro c hc
      have hcz : c ∈ Subgroup.centralizer ({C.z} : Set G) :=
        (Subgroup.mem_inf.mp hc).1
      have hce : c ∈ Subgroup.centralizer ({e} : Set G) :=
        (Subgroup.mem_inf.mp hc).2
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      dsimp only [P]
      rw [Subgroup.map_inf _ _ _ (MulAut.conj c).injective]
      have hQGfix : Subgroup.map (MulAut.conj c).toMonoidHom QG0 = QG0 :=
        QG_map_conj_eq C hcz
      rw [show Subgroup.map (↑(MulAut.conj c)) QG0 = QG0 from by
        simpa [QG0] using hQGfix]
      have hfix : Subgroup.map (↑(MulAut.conj c))
          (Subgroup.centralizer ({e} : Set G)) =
          Subgroup.centralizer ({e} : Set G) := by
        simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (Subgroup.le_normalizer (H := Subgroup.centralizer ({e} : Set G)) hce))
      rw [hfix]
    have hN_norm : Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G) ≤
        Subgroup.normalizer (N : Set G) := by
      intro c hc
      have hcz : c ∈ Subgroup.centralizer ({C.z} : Set G) :=
        (Subgroup.mem_inf.mp hc).1
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      dsimp only [N]
      rw [Subgroup.map_inf _ _ _ (MulAut.conj c).injective]
      have hQ'fix : Subgroup.map (MulAut.conj c).toMonoidHom Q' = Q' :=
        hQprime_map_conj hc
      rw [show Subgroup.map (↑(MulAut.conj c)) Q' = Q' from by
        simpa using hQ'fix]
      have hfix : Subgroup.map (↑(MulAut.conj c))
          (Subgroup.centralizer ({C.z} : Set G)) =
          Subgroup.centralizer ({C.z} : Set G) := by
        simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (Subgroup.le_normalizer (H := Subgroup.centralizer ({C.z} : Set G)) hcz))
      rw [hfix]
    have hS_card : Nat.card ↥(N ⊔ P) = 2 ^ 14 := by
      have hformula := CFSG.GH74.GLS.Stage1.Thm3.Sec4.M.card_sup_mul_card_inf
        (A := N) (B := P) (hP_le_Cg.trans hN_norm)
      rw [hNcard, hPcard, hNPcard] at hformula
      norm_num at hformula
      omega
    have hS_le_Cg : N ⊔ P ≤ Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G) := sup_le hN_le_Cg hP_le_Cg
    have hCg_card : Nat.card ↥(Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G)) = 2 ^ 14 * 21 := hCe'
    have hS_norm : Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G) ≤
        Subgroup.normalizer ((N ⊔ P : Subgroup G) : Set G) := by
      intro c hc
      exact Subgroup.inf_normalizer_le_normalizer_sup N P
        ⟨hN_norm hc, hP_norm hc⟩
    have htwo_mem_S : ∀ u : G, u ∈ Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G) → (∃ t : ℕ, u ^ 2 ^ t = 1) →
        u ∈ (N ⊔ P : Subgroup G) := by
      intro u huCg hu2
      obtain ⟨t, ht⟩ := hu2
      have hdvd : orderOf u ∣ 2 ^ t := orderOf_dvd_of_pow_eq_one ht
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hcard_u : Nat.card ↥(Subgroup.zpowers u) = 2 ^ j := by
        rw [Nat.card_zpowers, hj]
      let T : Subgroup G := (N ⊔ P) ⊔ Subgroup.zpowers u
      have hS_pgroup : IsPGroup 2 ↥(N ⊔ P) :=
        IsPGroup.of_card (p := 2) (n := 14) hS_card
      have hInter : (N ⊔ P) ⊓ Subgroup.zpowers u ≤ N ⊔ P := inf_le_left
      obtain ⟨l, hl⟩ := (hS_pgroup.to_le hInter).exists_card_eq
      have hu_norm : Subgroup.zpowers u ≤
          Subgroup.normalizer ((N ⊔ P : Subgroup G) : Set G) :=
        Subgroup.zpowers_le.mpr (hS_norm huCg)
      have hformula := CFSG.GH74.GLS.Stage1.Thm3.Sec4.M.card_sup_mul_card_inf
        (A := N ⊔ P) (B := Subgroup.zpowers u) hu_norm
      rw [hcard_u, hl, hS_card] at hformula
      have hl_le : l ≤ 14 + j := by
        have hdvd' : 2 ^ l ∣ 2 ^ (14 + j) := by
          rw [pow_add, ← hformula]
          exact dvd_mul_left _ _
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd'
      have hcardT : Nat.card ↥T = 2 ^ (14 + j - l) := by
        calc Nat.card ↥T = Nat.card ↥T * 2 ^ l / 2 ^ l := by
              rw [Nat.mul_div_cancel _ (by positivity)]
          _ = 2 ^ (14 + j) / 2 ^ l := by rw [hformula, ← pow_add]
          _ = 2 ^ (14 + j - l) := Nat.pow_div hl_le (by norm_num)
      have h14dvd : 2 ^ 14 ∣ Nat.card ↥T := by
        have h := Subgroup.card_dvd_of_le (le_sup_left : N ⊔ P ≤ T)
        rwa [hS_card] at h
      rw [hcardT] at h14dvd
      have h14le : 14 ≤ 14 + j - l :=
        (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h14dvd
      have hTdvd : Nat.card ↥T ∣ Nat.card ↥(Subgroup.centralizer ({C.z} : Set G) ⊓
          Subgroup.centralizer ({e} : Set G)) :=
        Subgroup.card_dvd_of_le (sup_le hS_le_Cg (Subgroup.zpowers_le.mpr huCg))
      rw [hcardT, hCg_card] at hTdvd
      have hd : 14 + j - l = 14 + ((14 + j - l) - 14) := by omega
      rw [hd, pow_add] at hTdvd
      have hdvd21 : 2 ^ ((14 + j - l) - 14) ∣ 21 :=
        (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ 14)).mp hTdvd
      have hcop : Nat.Coprime (2 ^ ((14 + j - l) - 14)) 21 :=
        Nat.Coprime.pow_left _ (by decide : Nat.Coprime 2 21)
      have hdvd1 : 2 ^ ((14 + j - l) - 14) ∣ 1 :=
        hcop.dvd_of_dvd_mul_right (by simpa using hdvd21)
      have hd0 : (14 + j - l) - 14 = 0 := by
        have h1 : 2 ^ ((14 + j - l) - 14) = 1 := Nat.dvd_one.mp hdvd1
        rcases (Nat.pow_eq_one.mp h1) with h | h
        · norm_num at h
        · exact h
      have hTcard : Nat.card ↥T = 2 ^ 14 := by
        rw [hcardT, hd, hd0]
      have hST : N ⊔ P = T :=
        Subgroup.eq_of_le_of_card_ge (le_sup_left : N ⊔ P ≤ T)
          (by rw [hTcard, hS_card])
      rw [hST]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    obtain ⟨m₁, m₂, hm1e, hm2e, ⟨t1, hm1two⟩, ⟨t2, hm2two⟩, h3dvd⟩ := hm
    have hm1Cg : phi C m₁ ∈ Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨(C.ψ m₁).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [phi_apply C m₁]
      simpa [e, map_mul] using
        congrArg (fun t : ↥Max3.M => (C.ψ t : G)) hm1e
    have hm2Cg : phi C m₂ ∈ Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨(C.ψ m₂).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [phi_apply C m₂]
      simpa [e, map_mul] using
        congrArg (fun t : ↥Max3.M => (C.ψ t : G)) hm2e
    have hm1two' : ∃ t : ℕ, (phi C m₁) ^ 2 ^ t = 1 :=
      ⟨t1, by rw [← map_pow, hm1two, map_one]⟩
    have hm2two' : ∃ t : ℕ, (phi C m₂) ^ 2 ^ t = 1 :=
      ⟨t2, by rw [← map_pow, hm2two, map_one]⟩
    have hm1S : phi C m₁ ∈ (N ⊔ P : Subgroup G) := htwo_mem_S _ hm1Cg hm1two'
    have hm2S : phi C m₂ ∈ (N ⊔ P : Subgroup G) := htwo_mem_S _ hm2Cg hm2two'
    have hm12S : phi C (m₁ * m₂) ∈ (N ⊔ P : Subgroup G) := by
      rw [map_mul]
      exact (N ⊔ P).mul_mem hm1S hm2S
    have hS_pgroup : IsPGroup 2 ↥(N ⊔ P) :=
      IsPGroup.of_card (p := 2) (n := 14) hS_card
    obtain ⟨r, hr⟩ := (IsPGroup.iff_orderOf.mp hS_pgroup)
      ⟨phi C (m₁ * m₂), hm12S⟩
    have hord_phi : orderOf (phi C (m₁ * m₂)) = 2 ^ r :=
      (Subgroup.orderOf_coe (⟨phi C (m₁ * m₂), hm12S⟩ : ↥(N ⊔ P))).trans hr
    have hord_m12 : orderOf (m₁ * m₂) = 2 ^ r := by
      rw [← orderOf_injective (phi C) (phi_injective C) (m₁ * m₂)]
      exact hord_phi
    have h3 : 3 ∣ 2 ^ r := by
      rwa [hord_m12] at h3dvd
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3
    norm_num at h32
  · refine ⟨g, hg, ?_⟩
    intro x hx
    have hxcomap : phi C x ∈ QG0 ⊓ Q' := Subgroup.mem_comap.mp (hAE hx)
    have hxQ' : phi C x ∈ Q' := (Subgroup.mem_inf.mp hxcomap).2
    obtain ⟨q, hqQG, hqx⟩ := Subgroup.mem_map.mp hxQ'
    change (MulAut.conj g) q = phi C x at hqx
    obtain ⟨qM, hqM, rfl⟩ := (mem_QG_iff C).mp hqQG
    refine ⟨qM, hqM, ?_⟩
    rw [← phi_apply C qM, ← phi_apply C x]
    calc phi C qM = g⁻¹ * (g * phi C qM * g⁻¹) * g := by group
      _ = g⁻¹ * phi C x * g := by
        change g⁻¹ * ((MulAut.conj g) (phi C qM)) * g = g⁻¹ * phi C x * g
        rw [hqx]

end CFSG.Sporadic.Th.Recog
