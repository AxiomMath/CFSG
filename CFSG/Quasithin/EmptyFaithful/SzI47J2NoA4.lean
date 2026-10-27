module

public import CFSG.Quasithin.EmptyFaithful.SzI47J2Steps
public import CFSG.Quasithin.EmptyFaithful.SzI47J2NoA4Loc

public section

namespace CFSG.Quasithin

open CFSG.ShultStronglyClosedTI.InvolutionCounting CFSG.Quasithin.SzI47J2NoA4

theorem j2CardNe51840_holds : J2CardNe51840 := by
  intro G _ _ hs z hz hcount hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hz2 : z * z = 1 := by rw [← pow_two]; exact hz.sq
  have h27 : Nat.card (_root_.conjugatesOf z) = 27 := by
    have h := card_centralizer_mul_card_conjugatesOf z
    rw [hcard, hz.card_centralizer] at h
    omega
  obtain ⟨g, hgH, hg5⟩ := exists_orderOf_eq_five hz
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg5
    exact absurd hg5 (by norm_num)
  have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hgH
  set K := Subgroup.centralizer ({g} : Set G) with hK
  have hzK : z ∈ K := Subgroup.mem_centralizer_singleton_iff.mpr hgz.symm
  have hgK : g ∈ K := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let z' : ↥K := ⟨z, hzK⟩
  let g' : ↥K := ⟨g, hgK⟩
  have hz'2 : z' * z' = 1 := Subtype.ext hz2
  have hz'1 : z' ≠ 1 := fun h => hz.ne_one (congrArg Subtype.val h)
  have huniq : ∀ w : ↥K, w * w = 1 → w * z' = z' * w → w = 1 ∨ w = z' := by
    intro w hww hwz
    rcases eq_one_or_eq_of_commute hz hgH hg5 (congrArg Subtype.val hwz)
      (Subgroup.mem_centralizer_singleton_iff.mp w.2) (congrArg Subtype.val hww) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hcnt := card_centralizer_mul_card_invSet hz'2 hz'1 huniq
  have hodd := odd_card_invSet hz'2 hz'1 huniq
  have h10 : 10 ∣ Nat.card (Subgroup.centralizer ({z'} : Set ↥K)) := by
    have hg'C : g' ∈ Subgroup.centralizer ({z'} : Set ↥K) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hgz)
    have hz'C : z' ∈ Subgroup.centralizer ({z'} : Set ↥K) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have h5 : 5 ∣ Nat.card (Subgroup.centralizer ({z'} : Set ↥K)) := by
      have h := orderOf_dvd_card_of_mem _ hg'C
      rwa [show orderOf g' = 5 from (Subgroup.orderOf_coe g').symm.trans hg5] at h
    have h2 : 2 ∣ Nat.card (Subgroup.centralizer ({z'} : Set ↥K)) := by
      have h := orderOf_dvd_card_of_mem _ hz'C
      rwa [show orderOf z' = 2 from orderOf_eq_prime (by rw [pow_two]; exact hz'2) hz'1] at h
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 5 2) h5 h2
  have hKdvd : Nat.card ↥K ∣ 51840 := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card K
  obtain ⟨f, hf⟩ : ∃ f, Nat.card ↥(invSet ↥K) = f := ⟨_, rfl⟩
  rw [hf] at hcnt hodd
  have hf5184 : f ∣ 5184 := by
    have h1 : f * 10 ∣ Nat.card ↥K := by
      rw [← hcnt, mul_comm (Nat.card (Subgroup.centralizer ({z'} : Set ↥K))) f]
      exact Nat.mul_dvd_mul_left f h10
    have h2 : f * 10 ∣ 5184 * 10 := by simpa using h1.trans hKdvd
    exact (Nat.mul_dvd_mul_iff_right (by norm_num : 0 < 10)).mp h2
  have hf81 : f ∣ 81 := by
    have h2f : ¬ 2 ∣ f := by
      intro h
      obtain ⟨k, hk⟩ := hodd
      omega
    have hcop : Nat.Coprime f 64 := by
      have h1 : Nat.Coprime 2 f := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2f
      have h2 := (h1.pow_left 6).symm
      simpa using h2
    have h3 : f ∣ 64 * 81 := by simpa using hf5184
    exact hcop.dvd_of_dvd_mul_left h3
  have hP : IsPGroup 5 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg5, pow_one])
  have hmod5 := card_modEq_card_fixed 5 (Subgroup.zpowers g) hP (_root_.conjugatesOf z)
    (fun k _ x hx => hx.trans (isConj_iff.mpr ⟨k, rfl⟩))
  have hF : {x : G | x ∈ _root_.conjugatesOf z ∧ ∀ k ∈ Subgroup.zpowers g, k * x = x * k} =
      Subtype.val '' (invSet ↥K) := by
    ext x
    constructor
    · rintro ⟨hxz, hc⟩
      have hxK : x ∈ K :=
        Subgroup.mem_centralizer_singleton_iff.mpr (hc g (Subgroup.mem_zpowers g)).symm
      refine ⟨⟨x, hxK⟩, ⟨Subtype.ext (mul_self_eq_one_of_isConj hz2 hxz), fun h => hz.ne_one ?_⟩,
        rfl⟩
      have h1 : x = 1 := congrArg Subtype.val h
      rw [h1] at hxz
      exact isConj_one_right.mp hxz.symm
    · rintro ⟨u, ⟨hu, hu1⟩, rfl⟩
      refine ⟨MonoidHom.map_isConj K.subtype (isConj_of_mem_invSet hz'2 huniq hu hu1),
        fun k hk => ?_⟩
      have hg : g ∈ Subgroup.centralizer ({(u : G)} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp u.2).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le.2 hg hk)
  have hcardF : Nat.card {x : G | x ∈ _root_.conjugatesOf z ∧
      ∀ k ∈ Subgroup.zpowers g, k * x = x * k} = f := by
    rw [hF, Nat.card_image_of_injective Subtype.val_injective, hf]
  rw [h27, hcardF] at hmod5
  have hf27 : f = 27 := by
    have hle : f ≤ 81 := Nat.le_of_dvd (by norm_num) hf81
    have h5 : 27 % 5 = f % 5 := hmod5
    clear hcnt hodd hf hf5184 hF hcardF hmod5
    interval_cases f <;> omega
  have hFeq : {x : G | x ∈ _root_.conjugatesOf z ∧ ∀ k ∈ Subgroup.zpowers g, k * x = x * k} =
      _root_.conjugatesOf z := by
    refine Set.eq_of_subset_of_ncard_le (fun x hx => hx.1) ?_ (Set.toFinite _)
    have e1 : (_root_.conjugatesOf z).ncard = 27 := by
      rw [← Nat.card_coe_set_eq]
      exact h27
    have e2 : {x : G | x ∈ _root_.conjugatesOf z ∧
        ∀ k ∈ Subgroup.zpowers g, k * x = x * k}.ncard = 27 := by
      rw [← Nat.card_coe_set_eq, hcardF, hf27]
    rw [e1, e2]
  have hcomm : ∀ u : G, IsConj z u → g * u = u * g := fun u hu => by
    have hu' : u ∈ {x : G | x ∈ _root_.conjugatesOf z ∧
        ∀ k ∈ Subgroup.zpowers g, k * x = x * k} := by
      rw [hFeq]
      exact hu
    exact hu'.2 g (Subgroup.mem_zpowers g)
  have hCne : Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
    intro h
    have h1 := hz.card_centralizer
    rw [h, Subgroup.card_top, hcard] at h1
    omega
  exact false_of_commute_of_isConj hz.ne_one hg1 hCne hcomm

end CFSG.Quasithin
