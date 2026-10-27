module

public import CFSG.Quasithin.EmptyFaithful.R3c2Base
public import CFSG.Quasithin.EmptyFaithful.S153D25Defs

public section

namespace CFSG.Quasithin.R3c2

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G}

omit [Finite G] in
theorem le_normalizer_UI153 (T I : Subgroup G) : I ≤ Subgroup.normalizer (UI153 T I : Set G) :=
  le_normalizer_conjClosure _ _

theorem orderOf_ne_three_of_mem_centralizer_UI (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hF : Facts15325 T Mc M V₁ V₂ Yp I) {x : G} (hxI : x ∈ I)
    (hxC : x ∈ Subgroup.centralizer (UI153 T I : Set G)) : orderOf x ≠ 3 := by
  intro hx3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFI : Yp ⊔ Sgp153 T V₁ ≤ I := hI.1.1
  have hUN := le_normalizer_UI153 T I
  obtain ⟨φ, -, hφk⟩ := hF.s3
  have hR2 : IsPGroup 2 (R153 T V₁ Yp) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  set ψ : ↥(Yp ⊔ Sgp153 T V₁) →* MulAut ↥(UI153 T I) :=
    (A4.actionOn (UI153 T I) I hUN).comp (Subgroup.inclusion hFI) with hψ
  have hψ1 : ∀ z : ↥(Yp ⊔ Sgp153 T V₁), ψ z = 1 ↔ (z : G) ∈ Subgroup.centralizer (UI153 T I : Set G) :=
    fun z => A4.actionOn_eq_one_iff hUN (Subgroup.inclusion hFI z)
  have hker : ∀ f : ↥(Yp ⊔ Sgp153 T V₁), φ f = 1 → ∃ k : ℕ, f ^ 2 ^ k = 1 := by
    intro f hf
    have hf' : f ∈ φ.ker := hf
    rw [hφk, Subgroup.mem_subgroupOf] at hf'
    obtain ⟨k, hk⟩ := hR2 ⟨(f : G), hf'⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hxMI : x ∈ M ⊓ I := hF.cent_le ⟨hxI, hxC⟩
  have hxY : x ∈ Yp := by
    rw [hF.theta]
    exact Subgroup.subset_closure ⟨hxMI, hx3⟩
  have hxF : x ∈ Yp ⊔ Sgp153 T V₁ := Subgroup.mem_sup_left hxY
  have hx3' : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx3] at this
  have hx3F : (⟨x, hxF⟩ : ↥(Yp ⊔ Sgp153 T V₁)) ^ 3 = 1 := Subtype.ext (by simpa using hx3')
  have hφx : φ ⟨x, hxF⟩ ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := hker _ h
    have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    rw [hx3] at h2
    have := Nat.prime_three.dvd_of_dvd_pow h2
    omega
  have hgen : Yp ≤ Subgroup.centralizer (UI153 T I : Set G) := by
    rw [hF.theta, thetaOf, Subgroup.closure_le]
    rintro y ⟨hyMI, hy3⟩
    have hyY : y ∈ Yp := by
      rw [hF.theta]
      exact Subgroup.subset_closure ⟨hyMI, hy3⟩
    have hyF : y ∈ Yp ⊔ Sgp153 T V₁ := Subgroup.mem_sup_left hyY
    have hy3' : y ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy3] at this
    have hy3F : (⟨y, hyF⟩ : ↥(Yp ⊔ Sgp153 T V₁)) ^ 3 = 1 := Subtype.ext (by simpa using hy3')
    have hψx : ψ ⟨x, hxF⟩ = 1 := (hψ1 _).2 hxC
    exact (hψ1 _).1 (eq_one_of_cube_of_perm_three ψ φ hker hx3F hψx hφx hy3F)
  apply hF.star_ne
  rw [eq_bot_iff]
  intro a ha
  have hYN : Yp ≤ Subgroup.normalizer (UI153 T I : Set G) := (le_sup_left.trans hFI).trans hUN
  obtain ⟨h, rfl⟩ := (A4.mem_autOn_iff hYN).1 ha
  exact (Subgroup.mem_bot).2 ((A4.actionOn_eq_one_iff hYN h).2 (hgen h.2))


noncomputable abbrev actL (T I L : Subgroup G) (hLI : L ≤ I) : ↥L →* MulAut ↥(UI153 T I) :=
  A4.actionOn (UI153 T I) L (hLI.trans (le_normalizer_UI153 T I))

omit [Finite G] in
theorem range_actL (T I L : Subgroup G) (hLI : L ≤ I) : (actL T I L hLI).range = Star153 T I L := by
  ext a
  rw [MonoidHom.mem_range]
  exact (A4.mem_autOn_iff (hLI.trans (le_normalizer_UI153 T I))).symm

omit [Finite G] in
theorem actL_eq_one_iff (T I L : Subgroup G) (hLI : L ≤ I) (x : ↥L) :
    actL T I L hLI x = 1 ↔ (x : G) ∈ Subgroup.centralizer (UI153 T I : Set G) :=
  A4.actionOn_eq_one_iff _ x

theorem not_three_dvd_card_ker_actL (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hF : Facts15325 T Mc M V₁ V₂ Yp I) (hLI : L ≤ I) :
    ¬ 3 ∣ Nat.card (actL T I L hLI).ker := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := (actL T I L hLI).ker) 3 h3
  have hz1 : ((z : ↥L) : G) ∈ Subgroup.centralizer (UI153 T I : Set G) :=
    (actL_eq_one_iff T I L hLI _).1 z.2
  refine orderOf_ne_three_of_mem_centralizer_UI hI hF (hLI (z : ↥L).2) hz1 ?_
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]

theorem pRank_three_eq_star (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hF : Facts15325 T Mc M V₁ V₂ Yp I) (hLI : L ≤ I) [Finite ↥(Star153 T I L)] :
    CFSG.Open.pRank 3 L = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Star153 T I L)) := by
  have hr := range_actL T I L hLI
  have : Finite (actL T I L hLI).range := Finite.of_equiv _ (MulEquiv.subgroupCongr hr).symm.toEquiv
  have h1 := pRank_three_range_eq (actL T I L hLI) (not_three_dvd_card_ker_actL hI hF hLI)
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L, ← h1]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) (MulEquiv.subgroupCongr hr)

end CFSG.Quasithin.R3c2
