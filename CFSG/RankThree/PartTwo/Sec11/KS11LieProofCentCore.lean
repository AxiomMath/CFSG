module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofTriv
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCentAut
import CFSG.RankThree.PartTwo.Sec6.Item65UsedTools

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace KS11LieProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

theorem range_le_of_image {F Q : Type*} [Group F] [Group Q] (K₁ : Subgroup F)
    (hK₁sn : K₁.IsSubnormal) (hK₁p : Group.IsPerfect K₁) (hK₁ne : K₁ ≠ ⊥)
    (hQ : IsQuasisimple Q) (ρ : Q →* F) (hle : K₁ ≤ ρ.range) : ρ.range ≤ K₁ := by
  have hP := hK₁sn.comap ρ
  have hmapcomap : (K₁.comap ρ).map ρ = K₁ := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hle]
  rcases Sec6.subnormal_le_center_or_eq_top_of_isQuasisimple hQ hP with hPZ | hPtop
  · exfalso
    apply hK₁ne
    have hcomm : ⁅K₁, K₁⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx y hy
      rw [← hmapcomap] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp (hPZ hb)) a]
    rw [← Subgroup.isPerfect_iff.mp hK₁p, hcomm]
  · rintro _ ⟨w, rfl⟩
    exact (show w ∈ K₁.comap ρ from hPtop ▸ Subgroup.mem_top w)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_block_of_mem {Y K : Subgroup G} {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf]
    (hKf : PiField π p f Kf)
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* projImage (slPi π 3 (p ^ f) Kf))
    {h₀ : GL (Fin 3) Kf} (hh₀ : h₀ ∈ glPi π 3 (p ^ f) Kf)
    (hKblock : ∀ y : Y, (y : G) ∈ K → ∃ B ∈ glPi π 2 (p ^ f) Kf, GeneralLinearGroup.det B = 1 ∧
      (φ (y : Y ⧸ aschbacherSolvableCore 3 Y) : ProjGenLinGroup (Fin 3) Kf) =
        ProjGenLinGroup.mk (h₀ * blockHom B * h₀⁻¹))
    (y : Y) (hy : (y : G) ∈ K) :
    ∃ B : slPi π 2 (p ^ f) Kf, φ (y : Y ⧸ aschbacherSolvableCore 3 Y) = blockProj hKf hh₀ B := by
  have hπ : π = false → UnitaryFieldData p f Kf := fun h' => by subst h'; exact hKf.unitary
  obtain ⟨B, hB, hBdet, hBe⟩ := hKblock y hy
  have hBs : B ∈ slPi π 2 (p ^ f) Kf := (mem_slPi_iff hπ).mpr
    ⟨hB, by rw [← GeneralLinearGroup.val_det_apply, hBdet, Units.val_one]⟩
  exact ⟨⟨B, hBs⟩, Subtype.ext hBe⟩

theorem block_mem_image {Y K : Subgroup G} {c : G} (hcN : c ∈ Subgroup.normalizer (Y : Set G))
    (hc3 : c ^ 3 = 1) (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (hT : IsType424 (K ⧸ aschbacherSolvableCore 3 K))
    {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf] (hKf : PiField π p f Kf)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* projImage (slPi π 3 (p ^ f) Kf))
    {h₀ : GL (Fin 3) Kf} (hh₀ : h₀ ∈ glPi π 3 (p ^ f) Kf) {e : Kfˣ}
    (hαc : ∀ m, (MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩)) m :
        ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹) * m *
        (ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹))⁻¹)
    (hKblock : ∀ y : Y, (y : G) ∈ K → ∃ B ∈ glPi π 2 (p ^ f) Kf, GeneralLinearGroup.det B = 1 ∧
      (φ (y : Y ⧸ aschbacherSolvableCore 3 Y) : ProjGenLinGroup (Fin 3) Kf) =
        ProjGenLinGroup.mk (h₀ * blockHom B * h₀⁻¹))
    (B : slPi π 2 (p ^ f) Kf) :
    ∃ y : Y, (y : G) ∈ K ∧ φ (y : Y ⧸ aschbacherSolvableCore 3 Y) = blockProj hKf hh₀ B := by
  obtain ⟨K₁, hK₁sn, hK₁p, hK₁ne, -, hK₁mem⟩ := image_facts hcN hc3 hK hT φ
  have hfix : ∀ B, blockProj hKf hh₀ B ∈
      (MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩))).toMonoidHom.eqLocus
        (MonoidHom.id (projImage (slPi π 3 (p ^ f) Kf))) := by
    intro B
    change MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩))
      (blockProj hKf hh₀ B) = blockProj hKf hh₀ B
    apply Subtype.ext
    rw [hαc, coe_blockProj, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    have hc := blockHom_commute e (B : GL (Fin 2) Kf)
    calc h₀ * diagE e * h₀⁻¹ * (h₀ * blockHom (B : GL (Fin 2) Kf) * h₀⁻¹) *
          (h₀ * diagE e * h₀⁻¹)⁻¹ =
        h₀ * (diagE e * blockHom (B : GL (Fin 2) Kf)) * (diagE e)⁻¹ * h₀⁻¹ := by group
      _ = h₀ * (blockHom (B : GL (Fin 2) Kf) * diagE e) * (diagE e)⁻¹ * h₀⁻¹ := by rw [hc]
      _ = h₀ * blockHom (B : GL (Fin 2) Kf) * h₀⁻¹ := by group
  set ρ := (blockProj hKf hh₀).codRestrict _ hfix with hρ
  have hle : K₁ ≤ ρ.range := by
    intro z hz
    obtain ⟨y, hyK, hy⟩ := (hK₁mem z).mp hz
    obtain ⟨B', hB'⟩ := exists_block_of_mem hKf φ hh₀ hKblock y hyK
    exact ⟨B', Subtype.ext (by rw [← hy, hB']; rfl)⟩
  have hge := range_le_of_image K₁ hK₁sn hK₁p hK₁ne (isQuasisimple_slPi_two hKf hq hq2) ρ hle
  exact (hK₁mem (ρ B)).mp (hge ⟨B, rfl⟩)

omit [Finite G] in
theorem conj_mem_inSubgroup {K : Subgroup G} {k n : G} (hk : k ∈ K)
    (hn : n ∈ inSubgroup (aschbacherSolvableCore 3) K) :
    k * n * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K := by
  obtain ⟨m, hm, rfl⟩ := hn
  refine ⟨⟨k, hk⟩ * m * (⟨k, hk⟩ : K)⁻¹, ?_, rfl⟩
  exact (inferInstance : (aschbacherSolvableCore 3 K).Normal).conj_mem m hm ⟨k, hk⟩

theorem isSolvable_inSubgroup (K : Subgroup G) :
    Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) K) := by
  have hs := (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).1
  exact Group.isSolvable_of_isSolvable_injective
    (f := ((aschbacherSolvableCore 3 K).equivMapOfInjective K.subtype
      K.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)

theorem tau_fixes_block {Y K : Subgroup G} {t : G} (htN : t ∈ Subgroup.normalizer (Y : Set G))
    (hKY : K ≤ Y)
    (htK : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K)
    {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf] (hKf : PiField π p f Kf)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* projImage (slPi π 3 (p ^ f) Kf))
    {h₀ : GL (Fin 3) Kf} (hh₀ : h₀ ∈ glPi π 3 (p ^ f) Kf)
    (hblk : ∀ B : slPi π 2 (p ^ f) Kf, ∃ y : Y, (y : G) ∈ K ∧
      φ (y : Y ⧸ aschbacherSolvableCore 3 Y) = blockProj hKf hh₀ B)
    (himg : ∀ y : Y, (y : G) ∈ K → ∃ B : slPi π 2 (p ^ f) Kf,
      φ (y : Y ⧸ aschbacherSolvableCore 3 Y) = blockProj hKf hh₀ B)
    (B : slPi π 2 (p ^ f) Kf) :
    MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨t, htN⟩))
      (blockProj hKf hh₀ B) = blockProj hKf hh₀ B := by
  set β := MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨t, htN⟩)) with hβ
  set ρ := blockProj hKf hh₀ with hρ
  have hQ := isQuasisimple_slPi_two hKf hq hq2
  have hρinj := blockProj_injective hKf hh₀
  set mkY := φ.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) with hmkY
  have hmkY_apply : ∀ y : Y, mkY y = φ (y : Y ⧸ aschbacherSolvableCore 3 Y) := fun y => rfl
  set Nθ := ((inSubgroup (aschbacherSolvableCore 3) K).subgroupOf Y).map mkY with hNθ
  set N' := Nθ.comap ρ with hN'
  have hθK : inSubgroup (aschbacherSolvableCore 3) K ≤ K := by
    rintro _ ⟨m, -, rfl⟩
    exact m.2
  have hNθs : Group.IsSolvable Nθ := by
    have := isSolvable_inSubgroup K
    have h1 : Group.IsSolvable ((inSubgroup (aschbacherSolvableCore 3) K).subgroupOf Y) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (hθK.trans hKY)).toMonoidHom)
        (MulEquiv.injective _)
    exact Group.isSolvable_of_surjective (mkY.subgroupMap_surjective _)
  have hN's : Group.IsSolvable N' :=
    Group.isSolvable_of_isSolvable_injective (f := ρ.subgroupComap Nθ) (fun x y hxy =>
      Subtype.ext (hρinj (congrArg Subtype.val hxy)))
  have hN'n : N'.Normal := by
    refine ⟨fun z hz B' => ?_⟩
    obtain ⟨n, hn, hnz⟩ := hz
    obtain ⟨y', hy'K, hy'⟩ := hblk B'
    change ρ (B' * z * B'⁻¹) ∈ Nθ
    refine ⟨y' * n * y'⁻¹, ?_, ?_⟩
    · exact conj_mem_inSubgroup hy'K hn
    · rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hnz, hmkY_apply, hy']
  have hN'Z : N' ≤ Subgroup.center (slPi π 2 (p ^ f) Kf) := by
    rcases Sec6.subnormal_le_center_or_eq_top_of_isQuasisimple hQ hN'n.isSubnormal with h | h
    · exact h
    · exfalso
      apply fieldCent_not_isSolvable hQ
      rw [h] at hN's
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.topEquiv).symm.toMonoidHom) (MulEquiv.injective _)
  have hmove : ∀ B, ∃ z ∈ Subgroup.center (slPi π 2 (p ^ f) Kf), β (ρ B) = ρ z * ρ B := by
    intro B
    obtain ⟨y, hyK, hy⟩ := hblk B
    have hnK := htK y hyK
    have hyY : (y : G) ∈ Y := y.2
    have hnY : t * y * t⁻¹ * (y : G)⁻¹ ∈ Y :=
      hKY (hθK hnK)
    set n : Y := ⟨t * y * t⁻¹ * (y : G)⁻¹, hnY⟩ with hn
    obtain ⟨z, hz⟩ := himg n (hθK hnK)
    refine ⟨z, hN'Z ⟨n, hnK, by rw [← hz]; rfl⟩, ?_⟩
    have h1 : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨t, htN⟩)
        (y : Y ⧸ aschbacherSolvableCore 3 Y) = ((n * y : Y) : Y ⧸ aschbacherSolvableCore 3 Y) := by
      rw [Sec4.thetaQuotMulAut_mk]
      congr 1
      apply Subtype.ext
      change t * y * t⁻¹ = t * y * t⁻¹ * (y : G)⁻¹ * y
      group
    rw [← hy, hβ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, h1, QuotientGroup.mk_mul, map_mul, hz]
  have hw : ∀ B, ∃ z ∈ Subgroup.center (slPi π 2 (p ^ f) Kf), (ρ B)⁻¹ * β (ρ B) = ρ z := by
    intro B
    obtain ⟨z, hzZ, hz⟩ := hmove B
    refine ⟨z, hzZ, ?_⟩
    rw [hz, ← mul_assoc, ← map_inv, ← map_mul, ← map_mul,
      (Subgroup.mem_center_iff.mp hzZ) B⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have hcomm : ∀ x : slPi π 2 (p ^ f) Kf, ∀ g : projImage (slPi π 3 (p ^ f) Kf),
      g ∈ ρ.range → (ρ x)⁻¹ * β (ρ x) * g = g * ((ρ x)⁻¹ * β (ρ x)) := by
    intro x g hg
    obtain ⟨z, hzZ, hz⟩ := hw x
    obtain ⟨B', rfl⟩ := hg
    rw [hz, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hzZ) B']
  have heq := eq_of_eq_mul_commute hQ.1 (β.toMonoidHom.comp ρ) ρ
    (fun B => (ρ B)⁻¹ * β (ρ B)) (fun B => (mul_inv_cancel_left _ _).symm)
    (fun x y => hcomm x (ρ y) ⟨y, rfl⟩)
    (fun x y => by
      obtain ⟨z, -, hz⟩ := hw y
      exact hcomm x _ ⟨z, hz.symm⟩) B
  exact heq


theorem cent_core {Y K : Subgroup G} {c t : G} (hcN : c ∈ Subgroup.normalizer (Y : Set G))
    (hc3 : c ^ 3 = 1) (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (hT : IsType424 (K ⧸ aschbacherSolvableCore 3 K))
    {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf] (hKf : PiField π p f Kf)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* projImage (slPi π 3 (p ^ f) Kf))
    (htN : t ∈ Subgroup.normalizer (Y : Set G)) {k : ℕ} (htk : t ^ 3 ^ k = 1)
    (htK : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K) :
    ∃ (h₀ : GL (Fin 3) Kf) (hh₀ : h₀ ∈ glPi π 3 (p ^ f) Kf) (l : Kfˣ),
      (π = false → (l : Kf) ^ (p ^ f + 1) = 1) ∧
      (∀ m, (MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨t, htN⟩)) m :
          ProjGenLinGroup (Fin 3) Kf) =
        ProjGenLinGroup.mk (h₀ * diagE l * h₀⁻¹) * m *
          (ProjGenLinGroup.mk (h₀ * diagE l * h₀⁻¹))⁻¹) ∧
      ∀ B : slPi π 2 (p ^ f) Kf, ∃ y : Y, (y : G) ∈ K ∧
        φ (y : Y ⧸ aschbacherSolvableCore 3 Y) = blockProj hKf hh₀ B := by
  obtain ⟨h₀, hh₀, e, -, -, hαc, hKblock⟩ := core_block hcN hc3 hK hT hKf hq hq2 φ
  have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  have hblk := block_mem_image hcN hc3 hK hT hKf hq hq2 φ hh₀ hαc hKblock
  have himg := exists_block_of_mem hKf φ hh₀ hKblock
  have hfix := tau_fixes_block htN hKY htK hKf hq hq2 φ hh₀ hblk himg
  have hβk : (MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨t, htN⟩))) ^ 3 ^ k =
      1 := by
    have h1 : (⟨t, htN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using htk)
    rw [← map_pow, ← map_pow, ← map_pow, h1, map_one, map_one, map_one]
  obtain ⟨l, hl, hβl⟩ := aut_fix_block hKf hq hq2 hh₀ _ hβk hfix
  exact ⟨h₀, hh₀, l, hl, hβl, hblk⟩

end KS11LieProof

end CFSG.RankThree.PartTwo.Sec11
