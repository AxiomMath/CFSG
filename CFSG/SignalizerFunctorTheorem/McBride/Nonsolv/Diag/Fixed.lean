module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.Block

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag

variable {G : Type*} [Group G]

theorem zpowers_inf_eq_bot {p : ℕ} (hp : p.Prime) {g : G} (hg : g ^ p = 1) {H : Subgroup G}
    (hgH : g ∉ H) : Subgroup.zpowers g ⊓ H = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx, hxH⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [Subgroup.mem_bot]
  by_contra hne
  have hndvd : ¬ (p : ℤ) ∣ i := by
    rintro ⟨m, rfl⟩
    apply hne
    rw [zpow_mul, zpow_natCast, hg, one_zpow]
  have hcop : IsCoprime (p : ℤ) i :=
    ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd).mpr hndvd
  obtain ⟨u, v, huv⟩ := hcop
  apply hgH
  have h1 : g = (g ^ i) ^ v := by
    have h2 : (1 : ℤ) = (p : ℤ) * u + i * v := by rw [← huv]; ring
    calc g = g ^ ((p : ℤ) * u + i * v) := by rw [← h2, zpow_one]
      _ = (g ^ (p : ℤ)) ^ u * (g ^ i) ^ v := by rw [zpow_add, zpow_mul, zpow_mul]
      _ = (g ^ i) ^ v := by rw [zpow_natCast, hg, one_zpow, one_mul]
  rw [h1]
  exact zpow_mem hxH v

theorem isSemisimple_of_isDirectProduct_lcal [Finite G] {K : Subgroup G}
    (hK : IsDirectProduct (lcal K) K) : IsSemisimple K := by
  have hsc : CFSG.SignalizerFunctorTheorem.Nonsolvable.simpleComponents K = lcal K := by
    ext T
    constructor
    · rintro ⟨hTK, hTn, hTs, x, hx, y, hy, hxy⟩
      refine mem_lcal_iff.mpr ⟨hTK, hTn.isSubnormal, hTs, fun hc => hxy ?_⟩
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : T) ⟨y, hy⟩)
    · intro hT
      obtain ⟨hTK, -, hTs, hnc⟩ := mem_lcal_iff.mp hT
      refine ⟨hTK, (Subgroup.normal_subgroupOf_iff_le_normalizer hTK).mpr
        (hK.le_normalizer hT), hTs, ?_⟩
      by_contra hcon
      push Not at hcon
      exact hnc (isMulCommutative_iff.mpr fun x y =>
        Subtype.ext (hcon x x.2 y y.2))
  unfold IsSemisimple
  rw [hsc]
  exact hK

theorem centralizer_zpowers (a : G) :
    Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
      Subgroup.centralizer {a} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem projIn_inf_centralizer_eq_self [Finite G] {p : ℕ} (hp : p.Prime) {K : Subgroup G}
    (hK : IsDirectProduct (lcal K) K) {a : G} (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hap : a ^ p = 1) {J : Subgroup G} (hJ : J ∈ lcal K)
    (haJ : a ∉ Subgroup.normalizer (J : Set G)) :
    projIn (lcal K) J (K ⊓ Subgroup.centralizer {a}) = J := by
  have hZ : Subgroup.zpowers a ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr haK
  have hper : ∀ b ∈ Subgroup.zpowers a, ∀ J ∈ lcal K,
      J.map (MulAut.conj b).toMonoidHom ∈ lcal K :=
    fun b hb _ hJ' => map_conj_mem_lcal hJ' (hZ hb)
  have h1 := projIn_centralizer_eq hK hper hJ
  rw [centralizer_zpowers, zpowers_inf_eq_bot hp hap haJ] at h1
  rw [h1]
  refine le_antisymm inf_le_left fun x hx => Subgroup.mem_inf.mpr ⟨hx, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
  rw [hh]
  simp

theorem exists_mem_inf_centralizer_supp [Finite G] {p : ℕ} (hp : p.Prime) {K : Subgroup G}
    (hK : IsDirectProduct (lcal K) K) {a : G} (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hap : a ^ p = 1) {J₀ : Subgroup G} (hJ₀ : J₀ ∈ lcal K)
    (haJ : a ∉ Subgroup.normalizer (J₀ : Set G)) :
    ∃ y ∈ K ⊓ Subgroup.centralizer {a}, y ∉ sSup (lcal K \ {J₀}) ∧
      ∀ J' ∈ lcal K, J' ∉ L514.conjOrbit (Subgroup.zpowers a) J₀ → y ∈ sSup (lcal K \ {J'}) := by
  set Z := Subgroup.zpowers a with hZdef
  have hZK : Z ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr haK
  have hL := L514.isDirectProduct_conjOrbit hZK hJ₀
  have hΩ := L514.self_mem_conjOrbit Z J₀
  have hΩS : L514.conjOrbit Z J₀ ⊆ lcal K := L514.conjOrbit_subset_lcal hZK hJ₀
  have hper : ∀ b ∈ Z, ∀ J ∈ L514.conjOrbit Z J₀,
      J.map (MulAut.conj b).toMonoidHom ∈ L514.conjOrbit Z J₀ :=
    fun b hb J hJ => L514.map_conj_mem_conjOrbit hJ hb
  have hproj := projIn_centralizer_eq hL hper hΩ
  have hbot : Z ⊓ Subgroup.normalizer (J₀ : Set G) = ⊥ := zpowers_inf_eq_bot hp hap haJ
  have hLK : orbitClosure J₀ Z ≤ K := by
    rw [← hL.sSup_eq]
    exact (sSup_le_sSup hΩS).trans hK.sSup_eq.le
  obtain ⟨x, hxJ, hx1⟩ : ∃ x ∈ J₀, x ≠ 1 := by
    obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hJ₀
    by_contra hcon
    push Not at hcon
    exact hnc (isMulCommutative_iff.mpr fun x y => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hcon x x.2, hcon y y.2]))
  have hx : x ∈ projIn (L514.conjOrbit Z J₀) J₀
      (orbitClosure J₀ Z ⊓ Subgroup.centralizer (Z : Set G)) := by
    rw [hproj, hbot]
    refine Subgroup.mem_inf.mpr ⟨hxJ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
    rw [hh]
    simp
  obtain ⟨-, l, hl, hxl⟩ := (mem_proj_iff (hL.commute_sSup_diff hΩ)).mp hx
  obtain ⟨hxlL, hxlC⟩ := Subgroup.mem_inf.mp hxl
  have hlS : l ∈ sSup (lcal K \ {J₀}) :=
    sSup_le_sSup (Set.sdiff_subset_sdiff_left hΩS) hl
  refine ⟨x * l, Subgroup.mem_inf.mpr ⟨hLK hxlL, ?_⟩, fun hy => ?_, fun J' hJ' hJ'Ω => ?_⟩
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers a)) hxlC
  · have hxS : x ∈ sSup (lcal K \ {J₀}) := by
      have := mul_mem hy (inv_mem hlS)
      simpa using this
    have h1 : x ∈ J₀ ⊓ sSup (lcal K \ {J₀}) := ⟨hxJ, hxS⟩
    rw [(hK.indep hJ₀).eq_bot, Subgroup.mem_bot] at h1
    exact hx1 h1
  · have hsub : L514.conjOrbit Z J₀ ⊆ lcal K \ {J'} := fun K' hK' =>
      ⟨hΩS hK', fun h => hJ'Ω (Set.mem_singleton_iff.mp h ▸ hK')⟩
    rw [← hL.sSup_eq] at hxlL
    exact sSup_le_sSup hsub hxlL

theorem mem_conjOrbit_of_sameBlock [Finite G] {p : ℕ} (hp : p.Prime) {K Y : Subgroup G}
    (hK : IsDirectProduct (lcal K) K) {a : G} (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hap : a ^ p = 1) {J₀ : Subgroup G} (hJ₀ : J₀ ∈ lcal K)
    (haJ : a ∉ Subgroup.normalizer (J₀ : Set G)) (hY : K ⊓ Subgroup.centralizer {a} ≤ Y)
    {J₁ : Subgroup G} (hJ₁ : J₁ ∈ lcal K) (hsame : SameBlock (lcal K) Y J₀ J₁) :
    J₁ ∈ L514.conjOrbit (Subgroup.zpowers a) J₀ := by
  by_contra hJ₁Ω
  obtain ⟨y, hyC, hy0, hyΩ⟩ := exists_mem_inf_centralizer_supp hp hK haK hap hJ₀ haJ
  exact hy0 ((hsame y (hY hyC)).mpr (hyΩ J₁ hJ₁ hJ₁Ω))

theorem sameBlock_map_conj_of_ne {p : ℕ} (hp : p.Prime) {S : Set (Subgroup G)}
    {A Y J : Subgroup G} {a : G} (haA : a ∈ A) (hap : a ^ p = 1)
    (hAS : ∀ c ∈ A, ∀ K ∈ S, K.map (MulAut.conj c).toMonoidHom ∈ S)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {g : G} (hg : g ∈ Subgroup.zpowers a)
    (hgJ : J.map (MulAut.conj g).toMonoidHom ≠ J)
    (hJg : SameBlock S Y J (J.map (MulAut.conj g).toMonoidHom)) :
    SameBlock S Y J (J.map (MulAut.conj a).toMonoidHom) := by
  let R : Subgroup G :=
    { carrier := {c | c ∈ A ∧ SameBlock S Y J (J.map (MulAut.conj c).toMonoidHom)}
      one_mem' := ⟨one_mem A, by rw [map_conj_one]; exact SameBlock.refl _ _ _⟩
      mul_mem' := by
        rintro c d ⟨hcA, hc⟩ ⟨hdA, hd⟩
        refine ⟨mul_mem hcA hdA, ?_⟩
        have h1 := SameBlock.map_conj (hAS c hcA) (hAS c⁻¹ (inv_mem hcA)) (hAY hcA) hd
        rw [L514.map_conj_map_conj] at h1
        exact hc.trans h1
      inv_mem' := by
        rintro c ⟨hcA, hc⟩
        refine ⟨inv_mem hcA, ?_⟩
        have h1 := SameBlock.map_conj (hAS c⁻¹ (inv_mem hcA))
          (hAS c⁻¹⁻¹ (inv_mem (inv_mem hcA))) (hAY (inv_mem hcA)) hc
        rw [L514.map_conj_map_conj, inv_mul_cancel, map_conj_one] at h1
        exact h1.symm }
  have hgR : g ∈ R := ⟨Subgroup.zpowers_le.mpr haA hg, hJg⟩
  by_contra hcon
  have haR : a ∉ R := fun h => hcon h.2
  have h1 : g ∈ Subgroup.zpowers a ⊓ R := ⟨hg, hgR⟩
  rw [zpowers_inf_eq_bot hp hap haR, Subgroup.mem_bot] at h1
  exact hgJ (by rw [h1, map_conj_one])

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag
