module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcPlacementDefs

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG.Open (IsElemAbelian)

private theorem eq_one_of_mem_subgroupOf_inf_ker {G : Type} [Group G] {H E : Subgroup G}
    {M : Type} [Group M] {π : ↥H →* M} (hEel : IsElemAbelian 3 E)
    (h3 : ¬ 3 ∣ Nat.card π.ker) {x : ↥H} (hxE : x ∈ E.subgroupOf H) (hxk : x ∈ π.ker) :
    x = 1 := by
  have hx3 : x ^ 3 = 1 := (hEel.subgroupOf H).2 x hxE
  have hdvd3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have hdvdk : orderOf x ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker hxk
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ hdvdk) h3

private theorem commute_of_mem_centralizer_map {G : Type} [Group G] {H E : Subgroup G}
    {M : Type} [Group M] {π : ↥H →* M} (hker : π.ker ≤ Subgroup.center ↥H)
    (h3 : ¬ 3 ∣ Nat.card π.ker) (hEel : IsElemAbelian 3 E) {g : M}
    (hg : g ∈ Subgroup.centralizer (((E.subgroupOf H).map π : Subgroup M) : Set M))
    {h : ↥H} (hgh : π h = g) {e : ↥H} (he : e ∈ E.subgroupOf H) :
    h * e = e * h := by
  let c : ↥H := h * e * h⁻¹ * e⁻¹
  have hc_ker : c ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    have hmem : π e ∈ (E.subgroupOf H).map π := Subgroup.mem_map_of_mem π he
    have hcomm : g * π e = π e * g :=
      (Subgroup.mem_centralizer_iff.mp hg (π e) hmem).symm
    dsimp only [c]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hgh, hcomm]
    group
  have hc_center : c ∈ Subgroup.center ↥H := hker hc_ker
  have hcomm_ce : Commute c e := (Subgroup.mem_center_iff.mp hc_center e).symm
  have hce : h * e * h⁻¹ = c * e := by
    dsimp only [c]
    group
  have hconj : (h * e * h⁻¹) ^ 3 = 1 := by
    rw [show h * e * h⁻¹ = (MulAut.conj h) e from (MulAut.conj_apply h e).symm,
      ← map_pow, (hEel.subgroupOf H).2 e he, map_one]
  have hc3 : c ^ 3 = 1 := by
    rw [hce, hcomm_ce.mul_pow] at hconj
    rw [(hEel.subgroupOf H).2 e he, mul_one] at hconj
    exact hconj
  have hc1 : c = 1 := by
    have hdvd3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have hdvdk : orderOf c ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker hc_ker
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ hdvdk) h3
  have hce1 : h * e * h⁻¹ = e := by rw [hce, hc1, one_mul]
  calc h * e = (h * e * h⁻¹) * h := by group
    _ = e * h := by rw [hce1]

private theorem card_map_subgroupOf_map_eq {G : Type} [Group G] {H E : Subgroup G}
    {M : Type} [Group M] {π : ↥H →* M} (hEH : E ≤ H)
    (h3 : ¬ 3 ∣ Nat.card π.ker) (hEel : IsElemAbelian 3 E) :
    Nat.card ((E.subgroupOf H).map π) = Nat.card E := by
  let E' := E.subgroupOf H
  have hinj : Function.Injective ⇑(π.comp E'.subtype) := by
    intro x y hxy
    have hxy' : π (x : ↥H) = π (y : ↥H) := hxy
    have hmemE : (x : ↥H)⁻¹ * (y : ↥H) ∈ E' := E'.mul_mem (E'.inv_mem x.2) y.2
    have hmemK : (x : ↥H)⁻¹ * (y : ↥H) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy', inv_mul_cancel]
    have h1 := eq_one_of_mem_subgroupOf_inf_ker hEel h3 hmemE hmemK
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  have htop : (⊤ : Subgroup ↥E').map E'.subtype = E' := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hmap : E'.map π = (⊤ : Subgroup ↥E').map (π.comp E'.subtype) := by
    rw [← Subgroup.map_map, htop]
  rw [hmap, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv

private theorem exists_cube_eq_one_commuting {G : Type} [Group G] {H E : Subgroup G}
    {M : Type} [Group M] {π : ↥H →* M} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H) (h3 : ¬ 3 ∣ Nat.card π.ker)
    (hEel : IsElemAbelian 3 E) {g : M}
    (hg : g ∈ Subgroup.centralizer (((E.subgroupOf H).map π : Subgroup M) : Set M))
    (hg3 : g ^ 3 = 1) :
    ∃ h' : ↥H, π h' = g ∧ h' ^ 3 = 1 ∧ ∀ e ∈ E.subgroupOf H, h' * e = e * h' := by
  obtain ⟨h, rfl⟩ := hπ g
  have hcomm : ∀ e ∈ E.subgroupOf H, h * e = e * h :=
    fun e he => commute_of_mem_centralizer_map hker h3 hEel hg rfl he
  have hz_ker : h ^ 3 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hg3]
  have hz3dvd : orderOf (h ^ 3) ∣ Nat.card π.ker :=
    Subgroup.orderOf_dvd_natCard π.ker hz_ker
  have hcop : Nat.Coprime 3 (orderOf (h ^ 3)) :=
    Nat.Coprime.coprime_dvd_right hz3dvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := h ^ 3) (n := 3) hcop
  let w : ↥H := (h ^ 3) ^ m
  have hw3 : w ^ 3 = h ^ 3 := by
    dsimp only [w]
    rw [← pow_mul, mul_comm, pow_mul, hm]
  have hw_ker : w ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    dsimp only [w]
    rw [map_pow, MonoidHom.mem_ker.mp hz_ker]
    exact one_pow m
  have hw_center : w ∈ Subgroup.center ↥H := hker hw_ker
  refine ⟨h * w⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, map_inv, MonoidHom.mem_ker.mp hw_ker, inv_one, mul_one]
  · have hcw : Commute h w⁻¹ := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hw_center) h
    rw [hcw.mul_pow, inv_pow, hw3, mul_inv_cancel]
  · intro e he
    have hhe : h * e = e * h := hcomm e he
    have hwe : w⁻¹ * e = e * w⁻¹ :=
      (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hw_center) e).symm
    calc h * w⁻¹ * e = h * (w⁻¹ * e) := by group
      _ = h * (e * w⁻¹) := by rw [hwe]
      _ = h * e * w⁻¹ := by group
      _ = e * h * w⁻¹ := by rw [hhe]
      _ = e * (h * w⁻¹) := by group

theorem coverSelfCent_holds : CoverSelfCent := by
  intro G _ _ H E M _ hEH π hπ hker h3 hEel hsc
  classical
  have hE'el : IsElemAbelian 3 (E.subgroupOf H) := hEel.subgroupOf H
  refine ⟨hE'el.map π, card_map_subgroupOf_map_eq hEH h3 hEel, ?_⟩
  intro g hg hg3
  obtain ⟨h', hπh', hcube, hcomm⟩ :=
    exists_cube_eq_one_commuting hπ hker h3 hEel hg hg3
  have h'cen : ((h' : ↥H) : G) ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have he : (⟨y, hEH hy⟩ : ↥H) ∈ E.subgroupOf H := Subgroup.mem_subgroupOf.mpr hy
    have h := congrArg Subtype.val (hcomm ⟨y, hEH hy⟩ he)
    simpa using h.symm
  have h'cube : ((h' : ↥H) : G) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hcube
  have h'mem : ((h' : ↥H) : G) ∈ E := hsc _ h'cen h'cube
  have h'E : h' ∈ E.subgroupOf H := Subgroup.mem_subgroupOf.mpr h'mem
  have hmem : π h' ∈ (E.subgroupOf H).map π := Subgroup.mem_map_of_mem π h'E
  rwa [hπh'] at hmem

end CFSG.StandardType.GGQ2Frame
