module

public import CFSG.LocalAnalysis.WeakClosure81.Twelve
public import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Vol2.E2TenSevenMult
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

private theorem eq_one_of_pow_two_of_odd {X : Type} [Group X] {x : X} {m : ℕ}
    (hodd : Odd (orderOf x)) (h : x ^ 2 ^ m = 1) : x = 1 := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    ((orderOf_dvd_iff_pow_eq_one).mpr h)
  have hi0 : i = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf x := by
      rw [hi]
      exact dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  rw [hi0, pow_zero] at hi
  exact orderOf_eq_one_iff.mp hi

theorem schurMultiplierInput_of_mult2Fact (h : CFSG.Quasithin.Mult2Fact) :
    SchurMultiplierInput := by
  intro X _ _ K _ A hKcen hKodd hA2 hAK htype
  obtain ⟨n, hn1, htype'⟩ := htype
  have hperf : commutator (X ⧸ K) = ⊤ :=
    CFSG.Quasithin.E2.commutator_eq_top_of_psl_or_sz hn1 htype'
  haveI : Group.IsPerfect (X ⧸ K) := ⟨hperf⟩
  haveI : IsSimpleGroup (X ⧸ K) := CFSG.Quasithin.E2.isSimpleGroup_of_psl_or_sz htype'
  have hqXK : CFSG.Open.IsQuasisimple (X ⧸ K) :=
    CFSG.ComponentClassification.Quasisimple.simple_of_perfect (X ⧸ K)
  let D : Subgroup X := commutator X
  have hDq : CFSG.Open.IsQuasisimple D :=
    CFSG.ComponentClassification.CentralExtensions.derived_quasisimple
      (G := X) (H := X ⧸ K) hqXK (QuotientGroup.mk' K)
      (QuotientGroup.mk'_surjective K) (by rw [QuotientGroup.ker_mk']; exact hKcen)
  have hDq' : CFSG.IsQuasisimple D :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native D).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open D).mpr hDq)
  have hDsupK : D ⊔ K = ⊤ := by
    have hmap : D.map (QuotientGroup.mk' K) = ⊤ :=
      CFSG.ComponentClassification.CentralExtensions.derived_map_eq_top
        (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
    have hcomap := Subgroup.comap_map_eq (f := QuotientGroup.mk' K) D
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
    exact hcomap.symm
  let q : D →* X ⧸ K := (QuotientGroup.mk' K).domRestrict D
  have hqker : q.ker = K.subgroupOf D := by
    rw [show q = (QuotientGroup.mk' K).domRestrict D from rfl, MonoidHom.ker_domRestrict,
      QuotientGroup.ker_mk']
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    have hx : x ∈ D ⊔ K := by rw [hDsupK]; exact Subgroup.mem_top x
    obtain ⟨d, hd, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    refine ⟨⟨d, hd⟩, ?_⟩
    change (QuotientGroup.mk' K) d = (QuotientGroup.mk' K) (d * k)
    rw [map_mul]
    have hk1 : (QuotientGroup.mk' K) k = 1 := by
      change ((k : X) : X ⧸ K) = 1
      exact (QuotientGroup.eq_one_iff k).mpr hk
    rw [hk1, mul_one]
  have hcenterXK : Subgroup.center (X ⧸ K) = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot (X ⧸ K)
      (CFSG.Quasithin.E2.nonabelian_of_psl_or_sz hn1 htype')
  have hcenter_le_K : ∀ d : D, d ∈ Subgroup.center D → (d : X) ∈ K := by
    intro d hd
    have hqd : q d ∈ Subgroup.center (X ⧸ K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨e, rfl⟩ := hqsurj y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_center_iff.mp hd e
    rw [hcenterXK, Subgroup.mem_bot] at hqd
    have hqd1 : d ∈ q.ker := MonoidHom.mem_ker.mpr hqd
    rw [hqker, Subgroup.mem_subgroupOf] at hqd1
    exact hqd1
  have hcenterD_sub : Subgroup.center D = K.subgroupOf D := by
    refine le_antisymm ?_ ?_
    · intro d hd
      rw [Subgroup.mem_subgroupOf]
      exact hcenter_le_K d hd
    · intro d hd
      rw [Subgroup.mem_subgroupOf] at hd
      rw [Subgroup.mem_center_iff]
      intro e
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hKcen hd) (e : X))
  have hcenterD_eq : Subgroup.center D = q.ker := by
    rw [hcenterD_sub, hqker]
  let e : D ⧸ Subgroup.center D ≃* X ⧸ K :=
    QuotientGroup.liftEquiv (N := Subgroup.center D) (φ := q) hqsurj hcenterD_eq
  have hA134D : CFSG.Quasithin.A134TypesCentral D := by
    rcases htype' with hpsl | hsz
    · exact Or.inl ⟨n, CFSG.Quasithin.IsPSL.of_mulEquiv e.symm hpsl⟩
    · exact Or.inr (Or.inl ⟨n, CFSG.Quasithin.IsSz.of_mulEquiv e.symm hsz⟩)
  have h2center : IsPGroup 2 (Subgroup.center D) := h D hDq' hA134D
  have h2inf : IsPGroup 2 (D ⊓ K : Subgroup X) := by
    have h2sub : IsPGroup 2 (K.subgroupOf D) := hcenterD_sub ▸ h2center
    have hsub : K.subgroupOf D = (D ⊓ K).subgroupOf D := by
      ext d
      simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact (hsub ▸ h2sub).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left)
  have hDK : D ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨m, hm⟩ := h2inf ⟨x, hx⟩
    have hm' : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    exact eq_one_of_pow_two_of_odd
      (hKodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hx.2)) hm'
  have hA_le_D : A ≤ D := by
    intro x hx
    have hxsup : x ∈ D ⊔ K := by rw [hDsupK]; exact Subgroup.mem_top x
    obtain ⟨d, hd, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxsup
    obtain ⟨m, hm⟩ := hA2 ⟨d * k, hx⟩
    have hm' : (d * k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hcomm : Commute d k := Subgroup.mem_center_iff.mp (hKcen hk) d
    have hkpow : k ^ 2 ^ m = 1 := by
      have h1 : d ^ 2 ^ m * k ^ 2 ^ m = 1 := by rw [← hcomm.mul_pow, hm']
      have h2 : k ^ 2 ^ m = (d ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have hmemD : k ^ 2 ^ m ∈ D := by
        rw [h2]
        exact D.inv_mem (Subgroup.pow_mem D hd (2 ^ m))
      have hmemK : k ^ 2 ^ m ∈ K := Subgroup.pow_mem K hk (2 ^ m)
      have hmem : k ^ 2 ^ m ∈ D ⊓ K := ⟨hmemD, hmemK⟩
      rwa [hDK, Subgroup.mem_bot] at hmem
    have hodd : Odd (orderOf k) := hKodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hk)
    rw [eq_one_of_pow_two_of_odd hodd hkpow, mul_one]
    exact hd
  exact ⟨D, inferInstance, by rw [inf_comm]; exact hDK, by rw [sup_comm]; exact hDsupK,
    hA_le_D⟩

theorem schurMultiplierInput : SchurMultiplierInput :=
  schurMultiplierInput_of_mult2Fact CFSG.Quasithin.mult2Fact

end CFSG.LocalAnalysis.WeakClosure81
