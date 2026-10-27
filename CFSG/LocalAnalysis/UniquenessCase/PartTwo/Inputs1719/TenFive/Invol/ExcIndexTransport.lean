module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Map

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

private lemma exists_int_mul_add_eq_one {n p : ℕ} (h : Nat.Coprime n p) :
    ∃ a b : ℤ, (n : ℤ) * a + (p : ℤ) * b = 1 := by
  refine ⟨Nat.gcdA n p, Nat.gcdB n p, ?_⟩
  have hg := Nat.gcd_eq_gcd_ab n p
  rw [h.gcd_eq_one] at hg
  simpa using hg.symm

private lemma mem_of_pow_mem_of_coprime {G : Type*} [Group G] {H : Subgroup G} {v : G}
    {n p : ℕ} (hn : v ^ n ∈ H) (hp : v ^ p = 1) (hcop : Nat.Coprime n p) : v ∈ H := by
  obtain ⟨a, b, hab⟩ := exists_int_mul_add_eq_one hcop
  have hv : v = (v ^ n) ^ a * (v ^ p) ^ b := by
    refine (zpow_one v).symm.trans ?_
    rw [← hab, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hp, one_zpow,
      mul_one]
  rw [hv]
  exact H.mul_mem (Subgroup.zpow_mem H hn a)
    (Subgroup.zpow_mem H (by rw [hp]; exact H.one_mem) b)

private lemma mem_map_of_pow_eq_one {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {C : Subgroup G} {R : Subgroup G'} (hCR : C.map f ≤ R)
    (hRn : R ≤ Subgroup.normalizer ((C.map f : Subgroup G') : Set G'))
    {p : ℕ} (hcop : Nat.Coprime ((C.map f).subgroupOf R).index p)
    {v : G'} (hvR : v ∈ R) (hvp : v ^ p = 1) : v ∈ C.map f := by
  have hHn : ((C.map f).subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCR).mpr hRn
  have hpow : (⟨v, hvR⟩ : R) ^ ((C.map f).subgroupOf R).index ∈ (C.map f).subgroupOf R :=
    Subgroup.pow_index_mem ((C.map f).subgroupOf R) ⟨v, hvR⟩
  have hn : v ^ ((C.map f).subgroupOf R).index ∈ C.map f := by
    simpa using (Subgroup.mem_subgroupOf.mp hpow)
  exact mem_of_pow_mem_of_coprime hn hvp hcop

theorem exists_inv_of_conj_index {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {C : Subgroup G} (β : MulAut C) (z : G')
    (hβz : ∀ u : C, f (β u : G) = z * f (u : G) * z⁻¹)
    {R : Subgroup G'} (hCR : C.map f ≤ R)
    (hRn : R ≤ Subgroup.normalizer ((C.map f : Subgroup G') : Set G'))
    {p : ℕ} (hcop : Nat.Coprime ((C.map f).subgroupOf R).index p)
    {T : Subgroup G'} {y : G'} (hTR : ∀ v ∈ T, y⁻¹ * v * y ∈ R)
    {u : T} (hu : orderOf u = p) {Q : Subgroup T} (huQ : u ∈ Q) (hQp : ∀ v ∈ Q, v ^ p = 1)
    (hinv : y * z * y⁻¹ * (u : G') * (y * z * y⁻¹)⁻¹ = (u : G')⁻¹) :
    ∃ (w : C) (Q₀ : Subgroup C), orderOf w = p ∧ β w = w⁻¹ ∧ w ∈ Q₀ ∧ Nonempty (Q ≃* Q₀) := by
  classical
  let φ : T →* G' := (MulAut.conj y⁻¹).toMonoidHom.comp T.subtype
  let ψ : C →* G' := f.comp C.subtype
  have hφinj : Function.Injective φ := by
    intro a b hab
    have hab' : (MulAut.conj y⁻¹) (a : G') = (MulAut.conj y⁻¹) (b : G') := by
      simpa [φ] using hab
    exact Subtype.ext ((MulAut.conj y⁻¹).injective hab')
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact Subtype.ext (hf (by simpa [ψ] using hab))
  have hφC : ∀ v ∈ Q, φ v ∈ C.map f := by
    intro v hv
    refine mem_map_of_pow_eq_one f hCR hRn hcop ?_ ?_
    · simpa [φ, MulAut.conj_apply] using hTR (v : G') v.2
    · rw [← map_pow, hQp v hv, map_one]
  let Q₀ : Subgroup C := (Q.map φ).comap ψ
  have hle : Q.map φ ≤ ψ.range := by
    rintro x ⟨v, hv, rfl⟩
    obtain ⟨c, hcC, hc⟩ := Subgroup.mem_map.mp (hφC v hv)
    exact ⟨⟨c, hcC⟩, by simpa [ψ] using hc⟩
  have hmap : Q₀.map ψ = Q.map φ := Subgroup.map_comap_eq_self hle
  have he : Q ≃* Q₀ := (Subgroup.equivMapOfInjective Q φ hφinj).trans
    ((Subgroup.equivMapOfInjective Q₀ ψ hψinj).trans (MulEquiv.subgroupCongr hmap)).symm
  obtain ⟨c₀, hc₀C, hc₀⟩ := Subgroup.mem_map.mp (hφC u huQ)
  let w : C := ⟨c₀, hc₀C⟩
  have hψw : ψ w = φ u := hc₀
  have hwQ₀ : w ∈ Q₀ := by
    show ψ w ∈ Q.map φ
    rw [hψw]
    exact Subgroup.mem_map_of_mem φ huQ
  have hord : orderOf w = p := by
    rw [← orderOf_injective ψ hψinj w, hψw, orderOf_injective φ hφinj u, hu]
  have hβw : β w = w⁻¹ := by
    refine Subtype.ext (hf ?_)
    have hwG : f (w : G) = y⁻¹ * (u : G') * y := by
      simpa [ψ, φ, MulAut.conj_apply] using hψw
    rw [hβz w, hwG, Subgroup.coe_inv, map_inv, hwG]
    have hA : z * (y⁻¹ * (u : G') * y) * z⁻¹ =
        y⁻¹ * (y * z * y⁻¹ * (u : G') * (y * z * y⁻¹)⁻¹) * y := by group
    rw [hA, hinv]
    group
  exact ⟨w, Q₀, hord, hβw, hwQ₀, ⟨he⟩⟩

theorem exists_inv_good_of_conj_index {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {C : Subgroup G} (β : MulAut C) (z : G')
    (hβz : ∀ u : C, f (β u : G) = z * f (u : G) * z⁻¹)
    {R : Subgroup G'} (hCR : C.map f ≤ R)
    (hRn : R ≤ Subgroup.normalizer ((C.map f : Subgroup G') : Set G'))
    {p : ℕ} (hcop : Nat.Coprime ((C.map f).subgroupOf R).index p)
    {T : Subgroup G'} {y : G'} (hTR : ∀ v ∈ T, y⁻¹ * v * y ∈ R)
    {u : T} (hu : orderOf u = p) (hgood : IsSpecialGood p u)
    (hinv : y * z * y⁻¹ * (u : G') * (y * z * y⁻¹)⁻¹ = (u : G')⁻¹) :
    ∃ w : C, orderOf w = p ∧ β w = w⁻¹ ∧ IsSpecialGood p w := by
  obtain ⟨Q, e, N, huQ, hQ, heN, h3⟩ := hgood
  obtain ⟨w, Q₀, hord, hβw, hwQ₀, ⟨φ⟩⟩ := exists_inv_of_conj_index f hf β z hβz hCR hRn hcop
    hTR hu huQ (fun v hv => by simpa using hQ.1 ⟨v, hv⟩) hinv
  exact ⟨w, hord, hβw, ⟨Q₀, e, N, hwQ₀, hQ.of_mulEquiv φ, heN, h3⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
