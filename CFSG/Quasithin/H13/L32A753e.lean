module

public import CFSG.Quasithin.H13.L32A753d

public section

namespace CFSG.Quasithin.H13.L32A.M753

open CFSG.Open CFSG.Quasithin

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)} {J C : Subgroup V}

theorem resHom_mem_stabSub (g : ↥(stabSub J)) (hg : (g : MulAut V) ∈ stabSub C) :
    resHom J g ∈ stabSub (C.subgroupOf J) := by
  intro x
  have h2 : ((resHom J g x : J) : V) = g.1 (x : V) := rfl
  show (resHom J g x : J) ∈ C.subgroupOf J ↔ x ∈ C.subgroupOf J
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, h2]
  exact hg (x : V)

@[expose] noncomputable def secHom (hKJ : K ≤ stabSub J) (hKC : K ≤ stabSub C) :
    ↥K →* MulAut (Sec J C) :=
  (quotHom (C.subgroupOf J)).comp
    (((resHom J).comp (Subgroup.inclusion hKJ)).codRestrict (stabSub (C.subgroupOf J))
      fun k => resHom_mem_stabSub _ (hKC k.2))

theorem secHom_mk (hKJ : K ≤ stabSub J) (hKC : K ≤ stabSub C) (k : ↥K)
    (j : ↥J) : secHom hKJ hKC k (QuotientGroup.mk j : Sec J C) =
      QuotientGroup.mk (⟨(k : MulAut V) j, (hKJ k.2 j).2 j.2⟩ : ↥J) := rfl

theorem range_secHom (hKJ : K ≤ stabSub J) (hKC : K ≤ stabSub C) :
    (secHom hKJ hKC).range = autSec K J C := by
  ext φ
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨⟨resHom J ⟨k, hKJ k.2⟩, resHom_mem_stabSub _ (hKC k.2)⟩, ?_, rfl⟩
    show resHom J ⟨k, hKJ k.2⟩ ∈ autSub K J
    exact mem_autSub.mpr ⟨⟨k, hKJ k.2⟩, k.2, rfl⟩
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hgK, hgψ⟩ := mem_autSub.mp (show (ψ : MulAut ↥J) ∈ autSub K J from hψ)
    refine ⟨⟨g, hgK⟩, ?_⟩
    have : (⟨resHom J ⟨(g : MulAut V), hKJ hgK⟩, resHom_mem_stabSub _ (hKC hgK)⟩ :
        ↥(stabSub (C.subgroupOf J))) = ψ := by
      apply Subtype.ext
      rw [← hgψ]
    rw [← this]
    rfl

theorem secHom_eq_one_iff (hKJ : K ≤ stabSub J) (hKC : K ≤ stabSub C)
    (k : ↥K) : secHom hKJ hKC k = 1 ↔ ∀ j ∈ J, (k : MulAut V) j * j⁻¹ ∈ C := by
  constructor
  · intro h j hj
    have := congrArg (fun φ : MulAut (Sec J C) => φ (QuotientGroup.mk (⟨j, hj⟩ : ↥J))) h
    simp only [secHom_mk, MulAut.one_apply] at this
    have h2 := (QuotientGroup.eq_iff_div_mem).1 this
    rw [Subgroup.mem_subgroupOf] at h2
    simpa [div_eq_mul_inv] using h2
  · intro h
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H j =>
      rw [secHom_mk, MulAut.one_apply]
      refine (QuotientGroup.eq_iff_div_mem).2 ?_
      rw [Subgroup.mem_subgroupOf]
      simpa [div_eq_mul_inv] using h j j.2

theorem nonempty_equiv_autSec (hKJ : K ≤ stabSub J) (hKC : K ≤ stabSub C)
    (hs : IsSimpleGroup ↥K) (hnt : ∃ k ∈ K, ∃ j ∈ J, k j * j⁻¹ ∉ C) :
    Nonempty (↥K ≃* ↥(autSec K J C)) := by
  have hinj : Function.Injective (secHom hKJ hKC) := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (secHom hKJ hKC).ker with hb | ht
    · exact (MonoidHom.ker_eq_bot_iff _).1 hb
    · exfalso
      obtain ⟨k, hk, j, hj, hkj⟩ := hnt
      have h1 : (⟨k, hk⟩ : ↥K) ∈ (secHom hKJ hKC).ker := ht ▸ trivial
      exact hkj ((secHom_eq_one_iff hKJ hKC _).1 h1 j hj)
  rw [← range_secHom hKJ hKC]
  exact ⟨MonoidHom.ofInjective hinj⟩

theorem isSimpleGroup_of_b42 (hP : B42TypeU33 ↥K) : IsSimpleGroup ↥K := by
  obtain ⟨hZ, hPSU⟩ := hP
  have h1 : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hPSU).2
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem b42TypeU33_autSec (hKJ : K ≤ stabSub J) (hKC : K ≤ stabSub C)
    (hP : B42TypeU33 ↥K) (hnt : ∃ k ∈ K, ∃ j ∈ J, k j * j⁻¹ ∉ C) :
    B42TypeU33 ↥(autSec K J C) := by
  obtain ⟨e⟩ := nonempty_equiv_autSec hKJ hKC (isSimpleGroup_of_b42 hP) hnt
  obtain ⟨hZ, hPSU⟩ := hP
  have hZ' : Subgroup.center ↥(autSec K J C) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : e.symm z ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (e y)
    rw [hZ, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    have := congrArg e h1
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  refine ⟨hZ', ?_⟩
  have e1 : ↥K ⧸ Subgroup.center ↥K ≃* ↥(autSec K J C) ⧸ Subgroup.center ↥(autSec K J C) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
      (e.trans ((QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot).symm)
  exact isPSU_congr e1 hPSU

theorem irr_autSec (hKJ : K ≤ stabSub J) (hKC : K ≤ stabSub C) (hCJ : C ≤ J)
    (hirr : ∀ J' : Subgroup V, C ≤ J' → J' ≤ J → (∀ k ∈ K, ∀ v ∈ J', k v ∈ J') →
      J' = C ∨ J' = J) :
    ∀ U : Subgroup (Sec J C), (∀ l ∈ autSec K J C, ∀ u ∈ U, l u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  set π : ↥J →* Sec J C := QuotientGroup.mk' (C.subgroupOf J) with hπ
  set J' : Subgroup V := (U.comap π).map J.subtype with hJ'
  have hCJ' : C ≤ J' := by
    intro c hc
    refine ⟨⟨c, hCJ hc⟩, ?_, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap]
    have : π ⟨c, hCJ hc⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hc)
    rw [this]
    exact U.one_mem
  have hJ'J : J' ≤ J := by
    rintro _ ⟨j, -, rfl⟩
    exact j.2
  have hinv : ∀ k ∈ K, ∀ v ∈ J', k v ∈ J' := by
    rintro k hk _ ⟨j, hj, rfl⟩
    refine ⟨⟨k j, (hKJ hk j).2 j.2⟩, ?_, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap] at hj ⊢
    have hmem : secHom hKJ hKC ⟨k, hk⟩ ∈ autSec K J C := by
      rw [← range_secHom hKJ hKC]
      exact ⟨_, rfl⟩
    have := hU _ hmem _ hj
    exact this
  rcases hirr J' hCJ' hJ'J hinv with h | h
  · left
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf J) u
    have hj : (j : V) ∈ J' := ⟨j, hu, rfl⟩
    rw [h] at hj
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hj)
  · right
    rw [eq_top_iff]
    intro u _
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf J) u
    have hj : (j : V) ∈ J' := by rw [h]; exact j.2
    obtain ⟨j', hj', hjj⟩ := hj
    have : j' = j := Subtype.ext hjj
    rw [← this]
    exact hj'

theorem natural_of_sec [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) (hKJ : K ≤ stabSub J) (hKC : K ≤ stabSub C) (hCJ : C ≤ J)
    (hP : B42TypeU33 ↥K)
    (hnt : ∃ k ∈ K, ∃ j ∈ J, k j * j⁻¹ ∉ C)
    (hirr : ∀ J' : Subgroup V, C ≤ J' → J' ≤ J → (∀ k ∈ K, ∀ v ∈ J', k v ∈ J') →
      J' = C ∨ J' = J)
    (hcard : Nat.card (Sec J C) ≤ 2 ^ 12) :
    Nat.card (Sec J C) = 2 ^ 6 ∧ G2NaturalDerived (autSec K J C) ⊤ ⊥ 1 := by
  have hV' : ∀ v : Sec J C, v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H j =>
      rw [← QuotientGroup.mk_pow]
      have : j ^ 2 = 1 := Subtype.ext (by simpa using hV (j : V))
      rw [this, QuotientGroup.mk_one]
  exact natural_of_irr hV' (b42TypeU33_autSec hKJ hKC hP hnt) (irr_autSec hKJ hKC hCJ hirr)
    hcard

end CFSG.Quasithin.H13.L32A.M753
