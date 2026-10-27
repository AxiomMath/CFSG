module

public import CFSG.RankThree.PartOne.S13K.Sp6Ctx
public import CFSG.RankThree.PartOne.KF.U4Model
public import CFSG.RankThree.PartOne.S12.KFTransfer
public import CFSG.RankThree.PartOne.KF.U4Ambient

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.KFQ
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.Sec12Three CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem IsTor.comm {p : ℕ} {x y : ↥(M10 K)} (hx : IsTor p x) (hy : IsTor p y) : x * y = y * x := by
  obtain ⟨a, -, hxa⟩ := hx
  obtain ⟨b, -, hyb⟩ := hy
  apply Subtype.ext
  change x.1 * y.1 = y.1 * x.1
  rw [hxa, hyb, ← torusEquiv_mul, ← torusEquiv_mul, mul_comm]

namespace Sp6Ctx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} (C : Sp6Ctx p A c L E f K)

include C in
theorem mem_autFixedInG_iff {g : ↥(M10 K)} (hg1 : ∀ x, IsTor p x → IsTor p (g * x * g⁻¹))
    (hg2 : ∀ x, IsTor p x → IsTor p (g⁻¹ * x * g)) {e : G} :
    e ∈ autFixedInG E (E.normalizerMonoidHom ⟨C.phi g, C.mem_normalizer hg1 hg2⟩) ↔
      ∃ x : ↥(M10 K), IsTor p x ∧ g * x = x * g ∧ ∃ i : ℤ, e = C.phi x * c ^ i := by
  have h0 : e ∈ autFixedInG E (E.normalizerMonoidHom ⟨C.phi g, C.mem_normalizer hg1 hg2⟩) ↔
      ∃ _ : e ∈ E, C.phi g * e * (C.phi g)⁻¹ = e := by
    unfold autFixedInG autFixed
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨e', he', rfl⟩
      refine ⟨e'.2, ?_⟩
      have hfix : E.normalizerMonoidHom ⟨C.phi g, C.mem_normalizer hg1 hg2⟩ e' = e' := he'
      exact congrArg Subtype.val hfix
    · rintro ⟨he, h⟩
      exact ⟨⟨e, he⟩, Subtype.ext h, rfl⟩
  rw [h0]
  constructor
  · rintro ⟨he, h⟩
    obtain ⟨x, hx, i, rfl⟩ := C.exists_decomp he
    rw [C.conj_phi_mul_zpow] at h
    have h1 : C.phi (g * x * g⁻¹) = C.phi x := mul_right_cancel h
    have h2 : g * x * g⁻¹ = x := C.phi_injective h1
    exact ⟨x, hx, by rw [mul_inv_eq_iff_eq_mul] at h2; exact h2, i, rfl⟩
  · rintro ⟨x, hx, hgx, i, rfl⟩
    refine ⟨C.phi_mul_zpow_mem hx i, ?_⟩
    rw [C.conj_phi_mul_zpow]
    have : g * x * g⁻¹ = x := by rw [hgx]; group
    rw [this]

theorem kfAtBlock {g : ↥(M10 K)} (hg1 : ∀ x, IsTor p x → IsTor p (g * x * g⁻¹))
    (hg2 : ∀ x, IsTor p x → IsTor p (g⁻¹ * x * g)) (B : Subgroup ↥(M10 K))
    (hBqs : CFSG.IsQuasisimple ↥B) (hBc : Subgroup.center ↥B = ⊥)
    (hBmodel : StatedClassicalModel ↥B .PSL 2 2 f)
    (hBcent : ∀ b ∈ B, ∀ x : ↥(M10 K), IsTor p x → g * x = x * g → b * x = x * b)
    (hBnorm : ∀ m : ↥(M10 K), (∀ x, IsTor p x → g * x = x * g → m * x = x * m) →
      ∀ b ∈ B, m * b * m⁻¹ ∈ B)
    {z : ↥(M10 K)} (hzB : z ∈ B) (hzT : IsTor p z) (hz1 : z ≠ 1) (hzg : g * z * g⁻¹ = z⁻¹)
    (hdec : ∀ x : ↥(M10 K), IsTor p x → ∃ u : ↥(M10 K), IsTor p u ∧ g * u = u * g ∧
      ∃ i : ℤ, x = u * z ^ i)
    (hgB : g ∈ B) :
    KFAt p E f (E.normalizerMonoidHom ⟨C.phi g, C.mem_normalizer hg1 hg2⟩) ∧
      kZero p E (E.normalizerMonoidHom ⟨C.phi g, C.mem_normalizer hg1 hg2⟩) = B.map C.phi := by
  set t := E.normalizerMonoidHom ⟨C.phi g, C.mem_normalizer hg1 hg2⟩ with ht
  set 𝔅 : Subgroup G := B.map C.phi with h𝔅
  have hfix : ∀ {e : G}, e ∈ autFixedInG E t ↔ ∃ x : ↥(M10 K), IsTor p x ∧ g * x = x * g ∧
      ∃ i : ℤ, e = C.phi x * c ^ i := fun {e} => C.mem_autFixedInG_iff hg1 hg2
  have hBL : 𝔅 ≤ L := by
    rintro _ ⟨b, -, rfl⟩
    exact C.phi_mem_L b
  have hct : c ∈ autFixedInG E t :=
    hfix.mpr ⟨1, IsTor.one, by simp, 1, by simp⟩
  have hBX : 𝔅 ≤ Subgroup.centralizer (autFixedInG E t : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨x, hx, hgx, i, rfl⟩ := hfix.mp he
    have h1 : C.phi x * C.phi b = C.phi b * C.phi x := by
      rw [← map_mul, ← map_mul, hBcent b hb x hx hgx |>.symm]
    have h2 : c ^ i * C.phi b = C.phi b * c ^ i :=
      (Commute.zpow_left (C.c_comm_phi b) i).eq
    calc C.phi x * c ^ i * C.phi b = C.phi x * (c ^ i * C.phi b) := by rw [mul_assoc]
      _ = C.phi x * (C.phi b * c ^ i) := by rw [h2]
      _ = (C.phi x * C.phi b) * c ^ i := by rw [mul_assoc]
      _ = (C.phi b * C.phi x) * c ^ i := by rw [h1]
      _ = C.phi b * (C.phi x * c ^ i) := by rw [mul_assoc]
  have hBnorm' : ∀ y ∈ L ⊓ Subgroup.centralizer (autFixedInG E t : Set G), ∀ b' ∈ 𝔅,
      y * b' * y⁻¹ ∈ 𝔅 := by
    rintro y ⟨hyL, hyC⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨m, rfl⟩ := C.exists_phi_eq hyL
    have hm : ∀ x, IsTor p x → g * x = x * g → m * x = x * m := by
      intro x hx hgx
      have hmem : C.phi x ∈ autFixedInG E t := hfix.mpr ⟨x, hx, hgx, 0, by simp⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hyC _ hmem
      apply C.phi_injective
      rw [map_mul, map_mul]
      exact h1.symm
    exact ⟨m * b * m⁻¹, hBnorm m hm b hb, by simp [map_mul, map_inv]⟩
  have e𝔅 : ↥B ≃* ↥𝔅 := Subgroup.equivMapOfInjective B C.phi C.phi_injective
  have hqs𝔅 : CFSG.IsQuasisimple ↥𝔅 := LocalCores.isQuasisimple_of_mulEquiv e𝔅 hBqs
  have hc𝔅 : Subgroup.center ↥𝔅 = ⊥ := by
    rw [← Subgroup.map_center_eq e𝔅, hBc, Subgroup.map_bot]
  have hmod𝔅 : StatedClassicalModel ↥𝔅 .PSL 2 2 f :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv e𝔅.symm hBmodel
  have hz𝔅 : C.phi z ∈ 𝔅 := ⟨z, hzB, rfl⟩
  have hzE : C.phi z ∈ E := (C.phi_mem_E_iff z).mpr hzT
  have hz1' : C.phi z ≠ 1 := by
    intro h1
    exact hz1 (C.phi_injective (by rw [h1, map_one]))
  have hE : ∀ e ∈ E, ∃ u ∈ autFixedInG E t, ∃ i : ℤ, e = u * C.phi z ^ i := by
    intro e he
    obtain ⟨x, hx, j, rfl⟩ := C.exists_decomp he
    obtain ⟨u, hu, hgu, i, rfl⟩ := hdec x hx
    refine ⟨C.phi u * c ^ j, hfix.mpr ⟨u, hu, hgu, j, rfl⟩, i, ?_⟩
    have h1 : c ^ j * C.phi z ^ i = C.phi z ^ i * c ^ j :=
      (Commute.zpow_zpow (C.c_comm_phi z) j i).eq
    calc C.phi (u * z ^ i) * c ^ j = C.phi u * C.phi z ^ i * c ^ j := by
          rw [map_mul, map_zpow]
      _ = C.phi u * (C.phi z ^ i * c ^ j) := by rw [mul_assoc]
      _ = C.phi u * (c ^ j * C.phi z ^ i) := by rw [h1]
      _ = (C.phi u * c ^ j) * C.phi z ^ i := by rw [← mul_assoc]
  have hK : kZero p E t = 𝔅 :=
    kZero_eq_of_block C.h C.hE4 t hct hBL hBX hBnorm' hqs𝔅 hc𝔅 hz𝔅 hzE hz1' hE
  have hwB : C.phi g ∈ kZero p E t := by
    rw [hK]
    exact ⟨g, hgB, rfl⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hK⟩
  · rintro ⟨f', -, -, hf'⟩
    rw [hK] at hf'
    exact not_psu_three_quotient_of_psl_two hmod𝔅 hc𝔅 hf'
  · rw [hK]
    exact hmod𝔅
  · ext e
    constructor
    · rintro ⟨heE, heC⟩
      have h1 : C.phi g * e = e * C.phi g := Subgroup.mem_centralizer_iff.mp heC (C.phi g) hwB
      refine (C.mem_autFixedInG_iff hg1 hg2).mpr ?_
      obtain ⟨x, hx, i, rfl⟩ := C.exists_decomp heE
      refine ⟨x, hx, ?_, i, rfl⟩
      have h2 : C.phi g * (C.phi x * c ^ i) * (C.phi g)⁻¹ = C.phi x * c ^ i := by
        rw [h1]; group
      rw [C.conj_phi_mul_zpow] at h2
      have h3 : C.phi (g * x * g⁻¹) = C.phi x := mul_right_cancel h2
      have h4 : g * x * g⁻¹ = x := C.phi_injective h3
      rw [mul_inv_eq_iff_eq_mul] at h4
      exact h4
    · intro he
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · obtain ⟨x, hx, -, i, rfl⟩ := hfix.mp he
        exact C.phi_mem_E_iff x |>.mpr hx |> fun h => E.mul_mem h (E.zpow_mem C.R.c_mem i)
      · rw [hK]
        refine Subgroup.mem_centralizer_iff.mpr fun b' hb' => ?_
        exact (Subgroup.mem_centralizer_iff.mp (hBX hb') e he).symm
  · rw [autMovedInG_eq_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨e, rfl⟩
    obtain ⟨x, hx, j, hxj⟩ := C.exists_decomp e.2
    obtain ⟨u, hu, hgu, i, hxi⟩ := hdec x hx
    have hgen : ((t e : E) : G) * (e : G)⁻¹ = C.phi (g * x * g⁻¹ * x⁻¹) := by
      change C.phi g * (e : G) * (C.phi g)⁻¹ * (e : G)⁻¹ = _
      rw [hxj, C.conj_phi_mul_zpow]
      simp only [map_mul, map_inv, mul_inv_rev]
      group
    have hval : g * x * g⁻¹ * x⁻¹ = z ^ (-2 * i) := by
      have hc : Commute u (z ^ i) := Commute.zpow_right (IsTor.comm hu hzT) i
      have h1 : g * u * g⁻¹ = u := by rw [hgu]; group
      have h2 : g * z ^ i * g⁻¹ = (z ^ i)⁻¹ := by
        rw [← conj_zpow, hzg, inv_zpow]
      have h3 : g * (u * z ^ i) * g⁻¹ = u * (z ^ i)⁻¹ := by
        calc g * (u * z ^ i) * g⁻¹ = (g * u * g⁻¹) * (g * z ^ i * g⁻¹) := by group
          _ = u * (z ^ i)⁻¹ := by rw [h1, h2]
      have hc' : u * (z ^ i)⁻¹ = (z ^ i)⁻¹ * u := hc.inv_right.eq
      have key : u * (z ^ i)⁻¹ * (u * z ^ i)⁻¹ = (z ^ i)⁻¹ * (z ^ i)⁻¹ := by
        calc u * (z ^ i)⁻¹ * (u * z ^ i)⁻¹ = u * (z ^ i)⁻¹ * ((z ^ i)⁻¹ * u⁻¹) := by
              rw [mul_inv_rev]
          _ = (u * (z ^ i)⁻¹) * (z ^ i)⁻¹ * u⁻¹ := by group
          _ = ((z ^ i)⁻¹ * u) * (z ^ i)⁻¹ * u⁻¹ := by rw [hc']
          _ = (z ^ i)⁻¹ * (u * (z ^ i)⁻¹) * u⁻¹ := by group
          _ = (z ^ i)⁻¹ * ((z ^ i)⁻¹ * u) * u⁻¹ := by rw [hc']
          _ = (z ^ i)⁻¹ * (z ^ i)⁻¹ := by group
      have h5 : z ^ (-2 * i) = (z ^ i)⁻¹ * (z ^ i)⁻¹ := by
        rw [show (-2 * i : ℤ) = -i + -i by ring, zpow_add, zpow_neg]
      rw [hxi, h3, key, h5]
    show ((t e : E) : G) * (e : G)⁻¹ ∈ kZero p E t
    rw [hgen, hK, hval]
    exact ⟨z ^ (-2 * i), B.zpow_mem hzB _, by rw [map_zpow]⟩
  · exact ⟨C.phi g, C.mem_normalizer hg1 hg2, hwB, rfl⟩

end Sp6Ctx

end CFSG.RankThree.PartOne.S13K
