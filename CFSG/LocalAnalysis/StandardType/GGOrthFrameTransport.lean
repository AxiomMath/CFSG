module

public import CFSG.LocalAnalysis.StandardType.GGOTwoPrimeMap
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

section NormalizerAction

variable {M G A : Type*} [Group M] [Group G] [Group A] {Ω : Subgroup M}
  (ψ : ↥Ω →* G) (hinj : Function.Injective ψ)
  (η : A →* G) (β : A →* M)
  (hpres : ∀ (a : A) (y : ↥Ω), β a * (y : M) * (β a)⁻¹ ∈ Ω)
  (hcompat : ∀ (a : A) (y : ↥Ω),
    ψ ⟨β a * (y : M) * (β a)⁻¹, hpres a y⟩ = η a * ψ y * (η a)⁻¹)
include hinj hpres hcompat
theorem normalizer_action_commute_iff (a : A) (y : ↥Ω) :
    η a * ψ y = ψ y * η a ↔ β a * (y : M) = (y : M) * β a := by
  let z : ↥Ω := ⟨β a * (y : M) * (β a)⁻¹, hpres a y⟩
  have hcomp : ψ z = η a * ψ y * (η a)⁻¹ := hcompat a y
  constructor
  · intro hc
    have heq : ψ z = ψ y := by rw [hcomp, hc]; group
    have hz : z = y := hinj heq
    have hzval : β a * (y : M) * (β a)⁻¹ = (y : M) := congrArg Subtype.val hz
    calc β a * (y : M) = (β a * (y : M) * (β a)⁻¹) * β a := by group
      _ = (y : M) * β a := by rw [hzval]
  · intro hc
    have hzval : β a * (y : M) * (β a)⁻¹ = (y : M) := by rw [hc]; group
    have hz : z = y := Subtype.ext hzval
    have heq : η a * ψ y * (η a)⁻¹ = ψ y := by rw [← hcomp, hz]
    calc η a * ψ y = (η a * ψ y * (η a)⁻¹) * η a := by group
      _ = ψ y * η a := by rw [heq]
theorem map_centralizer_of_normalizer_action (H : Subgroup A) :
    ((Ω ⊓ Subgroup.centralizer (H.map β : Set M)).subgroupOf Ω).map ψ =
      ψ.range ⊓ Subgroup.centralizer (H.map η : Set G) := by
  have hcent : ∀ y : ↥Ω,
      ψ y ∈ Subgroup.centralizer (H.map η : Set G) ↔
        (y : M) ∈ Subgroup.centralizer (H.map β : Set M) := by
    intro y
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hy t ht
      obtain ⟨a, ha, rfl⟩ := ht
      exact (normalizer_action_commute_iff ψ hinj η β hpres hcompat a y).mp
        (hy (η a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩))
    · intro hy t ht
      obtain ⟨a, ha, rfl⟩ := ht
      exact (normalizer_action_commute_iff ψ hinj η β hpres hcompat a y).mpr
        (hy (β a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩))
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, (hcent y).mpr hy.2⟩
  · rintro _ ⟨⟨y, rfl⟩, hy⟩
    exact Subgroup.mem_map.mpr ⟨y, ⟨y.2, (hcent y).mp hy⟩, rfl⟩

end NormalizerAction

theorem map_oTwoPrime_centralizer_of_normalizer_action
    {M G : Type} {A : Type*} [Group M] [Group G] [Group A] {Ω : Subgroup M}
    (ψ : ↥Ω →* G) (hinj : Function.Injective ψ)
    (η : A →* G) (β : A →* M)
    (hpres : ∀ (a : A) (y : ↥Ω), β a * (y : M) * (β a)⁻¹ ∈ Ω)
    (hcompat : ∀ (a : A) (y : ↥Ω),
      ψ ⟨β a * (y : M) * (β a)⁻¹, hpres a y⟩ = η a * ψ y * (η a)⁻¹)
    (H : Subgroup A) :
    ((ggOTwoPrime (Ω ⊓ Subgroup.centralizer (H.map β : Set M))).subgroupOf Ω).map ψ =
      ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer (H.map η : Set G)) := by
  let C : Subgroup M := Ω ⊓ Subgroup.centralizer (H.map β : Set M)
  have hres : (ggOTwoPrime C).subgroupOf Ω = ggOTwoPrime (C.subgroupOf Ω) := by
    apply Subgroup.map_injective (f := Ω.subtype) Ω.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr ((ggOTwoPrime_le C).trans inf_le_left),
      ggOTwoPrime_map_of_injective Ω.subtype Ω.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le (show C ≤ Ω from inf_le_left)]
  change ((ggOTwoPrime C).subgroupOf Ω).map ψ = _
  rw [hres, ggOTwoPrime_map_of_injective ψ hinj]
  rw [map_centralizer_of_normalizer_action ψ hinj η β hpres hcompat H]

theorem psi_conj_eq_iff {Ω G : Type} [Group Ω] [Group G] {Bs : Subgroup G} (ψ : Ω →* G)
    (β : ↥Bs →* Ω) (hinj : Function.Injective ψ)
    (hcompat : ∀ (b : ↥Bs) (y : Ω), ψ (β b * y * (β b)⁻¹) = (b : G) * ψ y * (b : G)⁻¹)
    (w : Ω) (h : ↥Bs) :
    ψ w * (h : G) * (ψ w)⁻¹ = (h : G) ↔ w * β h = β h * w := by
  set z : G := (ψ (β h))⁻¹ * (h : G) with hzdef
  have hz : ∀ y : Ω, z * ψ y = ψ y * z := by
    intro y
    have h2 : (ψ (β h))⁻¹ * ((h : G) * ψ y * (h : G)⁻¹) = ψ y * (ψ (β h))⁻¹ := by
      rw [← hcompat h y]
      simp only [map_mul, map_inv]
      group
    calc z * ψ y = (ψ (β h))⁻¹ * ((h : G) * ψ y * (h : G)⁻¹) * (h : G) := by
          rw [hzdef]; group
      _ = (ψ y * (ψ (β h))⁻¹) * (h : G) := by rw [h2]
      _ = ψ y * z := by rw [hzdef]; group
  have hz_inv' : ∀ y : Ω, z⁻¹ * (ψ y)⁻¹ = (ψ y)⁻¹ * z⁻¹ := by
    intro y
    have h := congrArg Inv.inv (hz y)
    simp only [mul_inv_rev] at h
    exact h.symm
  have hzh : (h : G) = ψ (β h) * z := by rw [hzdef]; group
  have hzpsi : ψ (β h) = (h : G) * z⁻¹ := by rw [hzh]; group
  constructor
  · intro hw
    have hmain : w * β h * w⁻¹ = β h := by
      apply hinj
      calc ψ (w * β h * w⁻¹)
          = ψ w * ψ (β h) * (ψ w)⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = ψ w * ((h : G) * z⁻¹) * (ψ w)⁻¹ := by rw [hzpsi]
        _ = (ψ w * (h : G) * (ψ w)⁻¹) * z⁻¹ := by
              calc ψ w * ((h : G) * z⁻¹) * (ψ w)⁻¹
                  = ψ w * (h : G) * (z⁻¹ * (ψ w)⁻¹) := by group
                _ = ψ w * (h : G) * ((ψ w)⁻¹ * z⁻¹) := by rw [hz_inv' w]
                _ = (ψ w * (h : G) * (ψ w)⁻¹) * z⁻¹ := by group
        _ = (h : G) * z⁻¹ := by rw [hw]
        _ = ψ (β h) := hzpsi.symm
    calc w * β h = (w * β h * w⁻¹) * w := by group
      _ = β h * w := by rw [hmain]
  · intro hw
    calc ψ w * (h : G) * (ψ w)⁻¹
        = ψ w * (ψ (β h) * z) * (ψ w)⁻¹ := by rw [hzh]
      _ = ψ w * ψ (β h) * z * (ψ w)⁻¹ := by group
      _ = ψ (w * β h) * z * (ψ w)⁻¹ := by rw [map_mul]
      _ = ψ (β h * w) * z * (ψ w)⁻¹ := by rw [hw]
      _ = ψ (β h) * ψ w * z * (ψ w)⁻¹ := by rw [map_mul]
      _ = ψ (β h) * z * ψ w * (ψ w)⁻¹ := by
            rw [mul_assoc (ψ (β h)) (ψ w) z, ← hz w, ← mul_assoc (ψ (β h)) z (ψ w)]
      _ = ψ (β h) * z := by group
      _ = (h : G) := hzh.symm

theorem mem_ggHyperplane_iff_comm {Ω G : Type} [Group Ω] [Group G] {Bs : Subgroup G} (ψ : Ω →* G)
    (β : ↥Bs →* Ω) (hinj : Function.Injective ψ)
    (hcompat : ∀ (b : ↥Bs) (y : Ω), ψ (β b * y * (β b)⁻¹) = (b : G) * ψ y * (b : G)⁻¹)
    {w : Ω} {a : MulAut ↥Bs} (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = ψ w * b * (ψ w)⁻¹) (z : G) :
    z ∈ ggHyperplane Bs a ↔ ∃ h : ↥Bs, (h : G) = z ∧ w * β h = β h * w := by
  rw [ggHyperplane, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hhz⟩
    have hah : a h = h := by
      have hh' : h ∈ MonoidHom.eqLocusM (a : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs) := hh
      rw [MonoidHom.mem_eqLocusM, MonoidHom.id_apply] at hh'
      exact hh'
    refine ⟨h, hhz, ?_⟩
    have hconj : ψ w * (h : G) * (ψ w)⁻¹ = (h : G) := by rw [← ha h, hah]
    exact (psi_conj_eq_iff ψ β hinj hcompat w h).mp hconj
  · rintro ⟨h, hhz, hw⟩
    refine ⟨h, ?_, hhz⟩
    have hconj : ψ w * (h : G) * (ψ w)⁻¹ = (h : G) :=
      (psi_conj_eq_iff ψ β hinj hcompat w h).mpr hw
    have hah : a h = h := by
      apply Subtype.ext
      rw [ha h, hconj]
    have hh' : h ∈ MonoidHom.eqLocusM (a : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs) := by
      rw [MonoidHom.mem_eqLocusM]
      simpa using hah
    exact hh'

theorem ggRankOneIn_eq_map_of_normalizer_action
    {M G : Type} [Group M] [Group G] [Finite G] {Bs X : Subgroup G}
    {Ω : Subgroup M} (ψ : ↥Ω →* G) (hinj : Function.Injective ψ)
    (hX : ψ.range = X) (β : ↥Bs →* M)
    (hpres : ∀ (b : ↥Bs) (y : ↥Ω), β b * (y : M) * (β b)⁻¹ ∈ Ω)
    (hcompat : ∀ (b : ↥Bs) (y : ↥Ω),
      ψ ⟨β b * (y : M) * (β b)⁻¹, hpres b y⟩ = (b : G) * ψ y * (b : G)⁻¹)
    (r : MulAut ↥Bs) (H : Subgroup M)
    (hH : ∀ t : M, t ∈ H ↔ ∃ b : ↥Bs, r b = b ∧ β b = t) :
    ggRankOneIn X Bs r =
      ((ggOTwoPrime (Ω ⊓ Subgroup.centralizer (H : Set M))).subgroupOf Ω).map ψ := by
  have hhyper : ∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔ r b = b := by
    intro b
    rw [ggHyperplane, Subgroup.mem_map]
    constructor
    · rintro ⟨c, hc, hcb⟩
      have hcb' : c = b := Subtype.ext hcb
      subst c
      have hc' : b ∈ MonoidHom.eqLocusM (r : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs) := hc
      rw [MonoidHom.mem_eqLocusM, MonoidHom.id_apply] at hc'
      exact hc'
    · intro hb
      refine ⟨b, ?_, rfl⟩
      change b ∈ MonoidHom.eqLocusM (r : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs)
      rw [MonoidHom.mem_eqLocusM, MonoidHom.id_apply]
      exact hb
  have key : ∀ (b : ↥Bs) (y : ↥Ω),
      (b : G) * ψ y = ψ y * (b : G) ↔ β b * (y : M) = (y : M) * β b := by
    intro b y
    exact normalizer_action_commute_iff ψ hinj Bs.subtype β hpres hcompat b y
  have hcent : ∀ y : ↥Ω,
      ψ y ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G) ↔
        (y : M) ∈ Subgroup.centralizer (H : Set M) := by
    intro y
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hy t ht
      obtain ⟨b, hb, rfl⟩ := (hH t).mp ht
      exact (key b y).mp (hy (b : G) ((hhyper b).mpr hb))
    · intro hy g hg
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hg
      have hb' : r b = b := (hhyper b).mp (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)
      exact (key b y).mpr (hy (β b) ((hH (β b)).mpr ⟨b, hb', rfl⟩))
  let K : Subgroup M := Ω ⊓ Subgroup.centralizer (H : Set M)
  have hKmap : (K.subgroupOf Ω).map ψ = X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨hX ▸ ⟨y, rfl⟩, (hcent y).mpr ?_⟩
      exact hy.2
    · rintro z ⟨hzX, hzC⟩
      rw [← hX] at hzX
      obtain ⟨y, rfl⟩ := hzX
      exact Subgroup.mem_map.mpr ⟨y, ⟨y.2, (hcent y).mp hzC⟩, rfl⟩
  have hres : (ggOTwoPrime K).subgroupOf Ω = ggOTwoPrime (K.subgroupOf Ω) := by
    apply Subgroup.map_injective (f := Ω.subtype) Ω.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr ((ggOTwoPrime_le K).trans inf_le_left),
      ggOTwoPrime_map_of_injective Ω.subtype Ω.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le (show K ≤ Ω from inf_le_left)]
  change ggOTwoPrime (X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G)) = _
  rw [← hKmap, ← ggOTwoPrime_map_of_injective ψ hinj, ← hres]

theorem ggRankOneIn_eq_map_of_inner {M G : Type} [Group M] [Group G] [Finite G] {Bs : Subgroup G}
    {Ω : Subgroup M} (ψ : ↥Ω →* G) (β : ↥Bs →* ↥Ω) (hinj : Function.Injective ψ)
    (hcompat : ∀ (b : ↥Bs) (y : ↥Ω), ψ (β b * y * (β b)⁻¹) = (b : G) * ψ y * (b : G)⁻¹)
    {A : Subgroup M} (hβA : ∀ b : ↥Bs, (β b : M) ∈ A) (hβsurj : ∀ t ∈ A, ∃ b : ↥Bs, (β b : M) = t)
    {w : ↥Ω} {a : MulAut ↥Bs} (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = ψ w * b * (ψ w)⁻¹)
    {H : Subgroup M} (hH : ∀ t : M, t ∈ H ↔ t ∈ A ∧ (w : M) * t = t * (w : M)) :
    ggRankOneIn ψ.range Bs a =
      ((ggOTwoPrime (Subgroup.centralizer (H : Set M) ⊓ Ω)).subgroupOf Ω).map ψ := by
  let β' : ↥Bs →* M := Ω.subtype.comp β
  have hpres : ∀ (b : ↥Bs) (y : ↥Ω), β' b * (y : M) * (β' b)⁻¹ ∈ Ω := by
    intro b y
    exact Ω.mul_mem (Ω.mul_mem (β b).2 y.2) (Ω.inv_mem (β b).2)
  have hc : ∀ (b : ↥Bs) (y : ↥Ω),
      ψ ⟨β' b * (y : M) * (β' b)⁻¹, hpres b y⟩ = (b : G) * ψ y * (b : G)⁻¹ := by
    intro b y
    have hz : (⟨β' b * (y : M) * (β' b)⁻¹, hpres b y⟩ : ↥Ω) =
        β b * y * (β b)⁻¹ := Subtype.ext rfl
    rw [hz]
    exact hcompat b y
  have hfix : ∀ b : ↥Bs, a b = b ↔ w * β b = β b * w := by
    intro b
    constructor
    · intro hb
      apply (psi_conj_eq_iff ψ β hinj hcompat w b).mp
      rw [← ha b, hb]
    · intro hb
      apply Subtype.ext
      rw [ha b]
      exact (psi_conj_eq_iff ψ β hinj hcompat w b).mpr hb
  have hH' : ∀ t : M, t ∈ H ↔ ∃ b : ↥Bs, a b = b ∧ β' b = t := by
    intro t
    constructor
    · intro ht
      obtain ⟨htA, htcomm⟩ := (hH t).mp ht
      obtain ⟨b, hb⟩ := hβsurj t htA
      refine ⟨b, (hfix b).mpr ?_, hb⟩
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, hb] using htcomm
    · rintro ⟨b, hb, hbt⟩
      change (β b : M) = t at hbt
      apply (hH t).mpr
      refine ⟨hbt ▸ hβA b, ?_⟩
      have hcomm := congrArg Subtype.val ((hfix b).mp hb)
      simpa only [Subgroup.coe_mul, hbt] using hcomm
  have h := ggRankOneIn_eq_map_of_normalizer_action ψ hinj rfl β' hpres hc a H hH'
  rw [inf_comm Ω (Subgroup.centralizer (H : Set M))] at h
  exact h

theorem isReflection_of_inner {M G : Type} [Group M] [Finite M] [Group G] [Finite G] {Bs : Subgroup G}
    {Ω : Subgroup M} (ψ : ↥Ω →* G) (β : ↥Bs →* ↥Ω) (hinj : Function.Injective ψ)
    (hcompat : ∀ (b : ↥Bs) (y : ↥Ω), ψ (β b * y * (β b)⁻¹) = (b : G) * ψ y * (b : G)⁻¹)
    {A : Subgroup M} (hβA : ∀ b : ↥Bs, (β b : M) ∈ A) (hβsurj : ∀ t ∈ A, ∃ b : ↥Bs, (β b : M) = t)
    {p : ℕ} (hp : 1 < p) {w : ↥Ω} {a : MulAut ↥Bs}
    (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = ψ w * b * (ψ w)⁻¹)
    (hw2 : ∀ t ∈ A, (w : M) * (w : M) * t = t * ((w : M) * (w : M))) {H : Subgroup M}
    (hH : ∀ t : M, t ∈ H ↔ t ∈ A ∧ (w : M) * t = t * (w : M))
    (hcard : Nat.card ↥H * p = Nat.card ↥A) : GGIsReflection p a := by
  let β' : ↥Bs →* M := Ω.subtype.comp β
  let C : Subgroup M := Subgroup.centralizer ({(w : M)} : Set M)
  let S : Subgroup ↥Bs := C.comap β'
  have hβ'range : β'.range = A := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      exact hβA b
    · intro hx
      obtain ⟨b, hb⟩ := hβsurj x hx
      exact ⟨b, hb⟩
  have ha2 : a ^ 2 = 1 := by
    ext b
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    have h1 : ((a (a b) : ↥Bs) : G) = (ψ w * ψ w) * (b : G) * (ψ w * ψ w)⁻¹ := by
      rw [ha (a b), ha b]; group
    rw [h1, ← map_mul]
    rw [psi_conj_eq_iff ψ β hinj hcompat (w * w) b]
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using hw2 (β b : M) (hβA b)
  have hfix : Nat.card {b : ↥Bs // a b = b} = Nat.card ↥S := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro b
    rw [Subgroup.mem_comap]
    change (a b = b) ↔ (β b : M) ∈ Subgroup.centralizer ({(w : M)} : Set M)
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h2 : ψ w * (b : G) * (ψ w)⁻¹ = (b : G) := by
        have := congrArg (fun x : ↥Bs => (x : G)) h
        rwa [ha b] at this
      have h3 := (psi_conj_eq_iff ψ β hinj hcompat w b).mp h2
      have h4 := congrArg (fun x : ↥Ω => (x : M)) h3
      simpa only [Subgroup.coe_mul] using h4.symm
    · intro h
      apply Subtype.ext
      rw [ha b]
      apply (psi_conj_eq_iff ψ β hinj hcompat w b).mpr
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using h.symm
  have hSidx : S.index = p := by
    have h1 : S.index = C.relIndex β'.range := Subgroup.index_comap C β'
    rw [h1, hβ'range]
    have h3 : C.relIndex A * Nat.card ↥(C ⊓ A) = Nat.card ↥A := Subgroup.relIndex_mul_card C A
    have h4 : C ⊓ A = H := by
      ext t
      rw [Subgroup.mem_inf]
      change t ∈ Subgroup.centralizer ({(w : M)} : Set M) ∧ t ∈ A ↔ t ∈ H
      rw [Subgroup.mem_centralizer_singleton_iff, hH t]
      exact ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩
    rw [h4] at h3
    have h5 : C.relIndex A * Nat.card ↥H = p * Nat.card ↥H := by
      rw [h3, ← hcard, mul_comm (Nat.card ↥H) p]
    exact mul_right_cancel₀ (Nat.card_ne_zero.mpr ⟨⟨1, H.one_mem⟩, inferInstance⟩) h5
  refine ⟨ha2, ?_⟩
  rw [hfix, ← hSidx]
  exact Subgroup.card_mul_index S

end CFSG.StandardType

end
