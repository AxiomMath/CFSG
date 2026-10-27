module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageBasic

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

private lemma lk0xu7f_eq_one_of_odd_order_of_pow_two
    {H : Type*} [Group H] {c : H} {k : ℕ}
    (hodd : Odd (orderOf c)) (hpow : c ^ 2 ^ k = 1) : c = 1 := by
  have hdvd : orderOf c ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hcop : Nat.Coprime (orderOf c) (2 ^ k) := hodd.coprime_two_right.pow_right k
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

private lemma lk0xu7f_eq_of_mul_inv_mem_center_of_pow_two
    {H : Type*} [Group H] {y₁ y₂ : H} {k : ℕ}
    (hc : y₁ * y₂⁻¹ ∈ Subgroup.center H) (hodd : Odd (orderOf (y₁ * y₂⁻¹)))
    (h₁ : y₁ ^ 2 ^ k = 1) (h₂ : y₂ ^ 2 ^ k = 1) : y₁ = y₂ := by
  have hcent : Commute (y₁ * y₂⁻¹) y₂ := (Subgroup.mem_center_iff.mp hc y₂).symm
  have hceq : (y₁ * y₂⁻¹) * y₂ = y₁ := by group
  have hpow : (y₁ * y₂⁻¹) ^ 2 ^ k = 1 := by
    have h : ((y₁ * y₂⁻¹) * y₂) ^ 2 ^ k = 1 := by rw [hceq, h₁]
    rw [hcent.mul_pow (2 ^ k), h₂, mul_one] at h
    exact h
  exact mul_inv_eq_one.mp (lk0xu7f_eq_one_of_odd_order_of_pow_two hodd hpow)

theorem odd_card_center_of_odd_card_centralizer {X : Type} [Group X] [Finite X] {G₀ : Subgroup X}
    (h : Odd (Nat.card (Subgroup.centralizer (G₀ : Set X)))) :
    Odd (Nat.card (Subgroup.center ↥G₀)) := by
  let f : Subgroup.center ↥G₀ →* Subgroup.centralizer (G₀ : Set X) :=
    { toFun := fun z => ⟨((z : ↥G₀) : X), by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hz := Subgroup.mem_center_iff.mp z.2 (⟨y, hy⟩ : ↥G₀)
        exact congrArg (fun w : ↥G₀ => (w : X)) hz⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  refine h.of_dvd_nat (Subgroup.card_dvd_of_injective f ?_)
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun u : Subgroup.centralizer (G₀ : Set X) => (u : X)) hab

theorem exists_cover_lift {X Y S : Type} [Group X] [Finite X] [Group Y] [Group S] [Finite S]
    {G₀ K : Subgroup X} (hK : K ≤ G₀) (η : ↥G₀ →* Y) (hker : η.ker ≤ Subgroup.center ↥G₀)
    (hodd : Odd (Nat.card (Subgroup.center ↥G₀)))
    (hS : CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit S) (φ : S →* Y)
    (hφ : φ.range = (K.subgroupOf G₀).map η) (hperf : Group.IsPerfect ↥K) :
    ∃ ψ : S →* ↥K, Function.Surjective ψ ∧ ∀ s, η (Subgroup.inclusion hK (ψ s)) = φ s := by
  let ηK : ↥K →* Y := η.comp (Subgroup.inclusion hK)
  have hmapr : (K.subgroupOf G₀).map η = φ.range := hφ.symm
  have hmem : ∀ k : ↥K, ηK k ∈ φ.range := by
    intro k
    have hk : (⟨(k : X), hK k.2⟩ : ↥G₀) ∈ K.subgroupOf G₀ := Subgroup.mem_subgroupOf.mpr k.2
    have h := Subgroup.mem_map_of_mem η (K := K.subgroupOf G₀) hk
    rw [hmapr] at h
    exact h
  let η' : ↥K →* ↥φ.range := ηK.codRestrict φ.range hmem
  have hη'surj : Function.Surjective η' := by
    intro y
    have hy : (y : Y) ∈ (K.subgroupOf G₀).map η := by
      rw [hmapr]
      exact y.2
    obtain ⟨x, hx, hxη⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨(x : X), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
    apply Subtype.ext
    change η (Subgroup.inclusion hK ⟨(x : X), Subgroup.mem_subgroupOf.mp hx⟩) = (y : Y)
    rw [show Subgroup.inclusion hK ⟨(x : X), Subgroup.mem_subgroupOf.mp hx⟩ = x from
      Subtype.ext rfl, hxη]
  have hη'ker : η'.ker ≤ Subgroup.center ↥K := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro m
    have hk1 : ηK k = 1 := congrArg (Subtype.val) hk
    have hkG : Subgroup.inclusion hK k ∈ η.ker := by
      rw [MonoidHom.mem_ker]
      exact hk1
    have hkZ : Subgroup.inclusion hK k ∈ Subgroup.center ↥G₀ := hker hkG
    have hcomm := (Subgroup.mem_center_iff.mp hkZ) (Subgroup.inclusion hK m)
    exact Subgroup.inclusion_injective hK (by simpa using hcomm)
  have hoddη' : Odd (Nat.card η'.ker) := by
    let g : η'.ker →* η.ker :=
      { toFun := fun k => ⟨Subgroup.inclusion hK (k : ↥K), by
          rw [MonoidHom.mem_ker]
          exact congrArg Subtype.val (MonoidHom.mem_ker.mp k.2)⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun _ _ => Subtype.ext rfl }
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      exact Subgroup.inclusion_injective hK (congrArg Subtype.val hab)
    exact (hodd.of_dvd_nat (Subgroup.card_dvd_of_le hker)).of_dvd_nat
      (Subgroup.card_dvd_of_injective g hg)
  obtain ⟨α, hα, hαsurj, -⟩ :=
    @CFSG.SeitzReduction.SeitzQ2.exists_surjective_of_oddCentralSplit
      S ↥φ.range ↥K _ _ _ φ.rangeRestrict η' _ _ hperf
      hS φ.rangeRestrict_surjective hη'surj hη'ker hoddη'
  exact ⟨α, hαsurj, fun s => by
    have h := congrArg Subtype.val (hα s)
    simpa [ηK, η'] using h⟩

private lemma lk0xu7f_le_of_map_eq {X Y : Type} [Group X] [Finite X] [Group Y]
    {G₀ R R' : Subgroup X} (hR : R ≤ G₀) (hR' : R' ≤ G₀) (η : ↥G₀ →* Y)
    (hker : η.ker ≤ Subgroup.center ↥G₀) (hodd : Odd (Nat.card (Subgroup.center ↥G₀)))
    (h2 : IsPGroup 2 R) (h2' : IsPGroup 2 R')
    (hmap : (R.subgroupOf G₀).map η = (R'.subgroupOf G₀).map η) : R ≤ R' := by
  intro r hr
  have hrG : (⟨r, hR hr⟩ : ↥G₀) ∈ R.subgroupOf G₀ := Subgroup.mem_subgroupOf.mpr hr
  have hηmem : η ⟨r, hR hr⟩ ∈ (R.subgroupOf G₀).map η := Subgroup.mem_map_of_mem η hrG
  rw [hmap] at hηmem
  obtain ⟨x, hx, hxη⟩ := Subgroup.mem_map.mp hηmem
  have hx' : (x : X) ∈ R' := Subgroup.mem_subgroupOf.mp hx
  have hc : (⟨r, hR hr⟩ : ↥G₀) * x⁻¹ ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxη, mul_inv_cancel]
  have hcZ := hker hc
  have hcodd : Odd (orderOf ((⟨r, hR hr⟩ : ↥G₀) * x⁻¹)) :=
    hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard (Subgroup.center ↥G₀) hcZ)
  obtain ⟨k, hk⟩ := h2 (⟨r, hr⟩ : ↥R)
  obtain ⟨l, hl⟩ := h2' (⟨(x : X), hx'⟩ : ↥R')
  have hkX : r ^ 2 ^ k = 1 := by simpa using congrArg (fun w : ↥R => (w : X)) hk
  have hlX : (x : X) ^ 2 ^ l = 1 := by
    simpa using congrArg (fun w : ↥R' => (w : X)) hl
  have hkX' : r ^ 2 ^ max k l = 1 := by
    rw [show max k l = k + (max k l - k) by omega, pow_add, pow_mul, hkX, one_pow]
  have hlX' : (x : X) ^ 2 ^ max k l = 1 := by
    rw [show max k l = l + (max k l - l) by omega, pow_add, pow_mul, hlX, one_pow]
  have hkG : (⟨r, hR hr⟩ : ↥G₀) ^ 2 ^ max k l = 1 := by
    apply Subtype.ext
    simpa using hkX'
  have hlG : x ^ 2 ^ max k l = 1 := by
    apply Subtype.ext
    simpa using hlX'
  have heq : (⟨r, hR hr⟩ : ↥G₀) = x :=
    lk0xu7f_eq_of_mul_inv_mem_center_of_pow_two hcZ hcodd hkG hlG
  rw [show r = (x : X) from congrArg Subtype.val heq]
  exact hx'

theorem eq_of_isPGroup_of_map_eq {X Y : Type} [Group X] [Finite X] [Group Y] {G₀ R R' : Subgroup X}
    (hR : R ≤ G₀) (hR' : R' ≤ G₀) (η : ↥G₀ →* Y) (hker : η.ker ≤ Subgroup.center ↥G₀)
    (hodd : Odd (Nat.card (Subgroup.center ↥G₀))) (h2 : IsPGroup 2 R) (h2' : IsPGroup 2 R')
    (hmap : (R.subgroupOf G₀).map η = (R'.subgroupOf G₀).map η) : R = R' := by
  exact le_antisymm
    (lk0xu7f_le_of_map_eq hR hR' η hker hodd h2 h2' hmap)
    (lk0xu7f_le_of_map_eq hR' hR η hker hodd h2' h2 hmap.symm)

theorem isQuasisimple_map_of_ker_le_center {X Y : Type} [Group X] [Finite X] [Group Y]
    {G₀ K : Subgroup X} (hK : K ≤ G₀) (η : ↥G₀ →* Y) (hker : η.ker ≤ Subgroup.center ↥G₀)
    (hq : CFSG.Assembly.IsQuasisimple ↥K) :
    CFSG.IsQuasisimple ↥((K.subgroupOf G₀).map η) := by
  let f : ↥K →* Y := η.comp (Subgroup.inclusion hK)
  have hfker : f.ker ≤ Subgroup.center ↥K := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro m
    have hk1 : f k = 1 := MonoidHom.mem_ker.mp hk
    have hkG : Subgroup.inclusion hK k ∈ η.ker := by
      rw [MonoidHom.mem_ker]
      exact hk1
    have hkZ : Subgroup.inclusion hK k ∈ Subgroup.center ↥G₀ := hker hkG
    have hcomm := (Subgroup.mem_center_iff.mp hkZ) (Subgroup.inclusion hK m)
    exact Subgroup.inclusion_injective hK (by simpa using hcomm)
  have hQ : CFSG.IsQuasisimple ↥K := by
    refine ⟨⟨hq.1⟩, hq.2, ?_⟩
    haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
    by_contra hc
    push Not at hc
    exact Group.IsPerfect.not_isMulCommutative (G := ↥K ⧸ Subgroup.center ↥K) ⟨⟨hc⟩⟩
  have hrange : f.range = (K.subgroupOf G₀).map η := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact Subgroup.mem_map_of_mem η (Subgroup.mem_subgroupOf.mpr k.2)
    · intro hy
      obtain ⟨x, hx, hxη⟩ := Subgroup.mem_map.mp hy
      refine ⟨⟨(x : X), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
      change η (Subgroup.inclusion hK ⟨(x : X), Subgroup.mem_subgroupOf.mp hx⟩) = y
      rw [show Subgroup.inclusion hK ⟨(x : X), Subgroup.mem_subgroupOf.mp hx⟩ = x from
        Subtype.ext rfl, hxη]
  have hres := CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_range_of_ker_le_center hQ f hfker
  rw [hrange] at hres
  exact hres

end CFSG.StandardType.LieKnownR2.ExcPos
