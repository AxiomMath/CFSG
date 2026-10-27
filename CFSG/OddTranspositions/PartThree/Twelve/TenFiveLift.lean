module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveCentral
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultiplier
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveLiftModel
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveLiftExtension

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

private theorem mk_coe_mul {k : ℕ} {ε π : Bool} (x y : ↥(fiveReflectionGroup k ε π)) :
    (QuotientGroup.mk (x * y) : fiveProjective k ε π) =
      (QuotientGroup.mk x : fiveProjective k ε π) *
        (QuotientGroup.mk y : fiveProjective k ε π) :=
  map_mul (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) x y

private theorem mk_coe_one {k : ℕ} (ε π : Bool) :
    (QuotientGroup.mk (1 : ↥(fiveReflectionGroup k ε π)) : fiveProjective k ε π) = 1 :=
  map_one (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π)))

private theorem mk_coe_inv {k : ℕ} {ε π : Bool} (x : ↥(fiveReflectionGroup k ε π)) :
    (QuotientGroup.mk x⁻¹ : fiveProjective k ε π) =
      (QuotientGroup.mk x : fiveProjective k ε π)⁻¹ :=
  map_inv (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) x

private theorem fiveLift_map_mk {k : ℕ} (ε π : Bool) :
    (commutator ↥(fiveReflectionGroup k ε π)).map
      (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) =
      commutator (fiveProjective k ε π) := by
  rw [map_commutator_eq,
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), commutator_def]

private theorem fiveLift_P_perfect {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) :
    ⁅commutator (fiveProjective k ε π), commutator (fiveProjective k ε π)⁆ =
      commutator (fiveProjective k ε π) := by
  have hR'perf : ⁅commutator ↥(fiveReflectionGroup k ε π),
      commutator ↥(fiveReflectionGroup k ε π)⁆ = commutator ↥(fiveReflectionGroup k ε π) :=
    commutator_commutator_fiveReflectionGroup hk ε π
  rw [← fiveLift_map_mk ε π, ← Subgroup.map_commutator, hR'perf]

private theorem fiveLift_map_zeta {G : Type*} [Group G] {k : ℕ} {ε π : Bool}
    (ζ : G →* fiveProjective k ε π) (hζ : Function.Surjective ζ) :
    (commutator G).map ζ = commutator (fiveProjective k ε π) := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hζ, commutator_def]

private theorem fiveLift_G_perfect {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    (ζ : G →* fiveProjective k ε π) (hζ : Function.Surjective ζ)
    (hker : ζ.ker ≤ Subgroup.center G) :
    commutator ↥(commutator G) = ⊤ := by
  have hPperf := fiveLift_P_perfect hk ε π
  have hperfZ : ⁅commutator (G ⧸ ζ.ker), commutator (G ⧸ ζ.ker)⁆ =
      commutator (G ⧸ ζ.ker) := by
    let eL : G ⧸ ζ.ker →* fiveProjective k ε π := QuotientGroup.kerLift ζ
    let e := QuotientGroup.quotientKerEquivOfSurjective (φ := ζ) hζ
    have heLsurj : Function.Surjective eL := e.surjective
    have hmk : (commutator (G ⧸ ζ.ker)).map eL = commutator (fiveProjective k ε π) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr heLsurj, commutator_def]
    exact Subgroup.map_injective (show Function.Injective eL from e.injective)
      (by rw [Subgroup.map_commutator, hmk, hPperf])
  obtain ⟨d, hd⟩ := hS.nonempty
  have hGperf_le : commutator G ≤ ⁅commutator G, commutator G⁆ :=
    commutator_le_commutator_commutator hker (hS.oddT.mul_self_eq_one hd)
      (mem_commutator_or_mul_mem_of_setup hS hd) hperfZ
  have hEq : commutator G = ⁅commutator G, commutator G⁆ :=
    le_antisymm hGperf_le (Subgroup.commutator_le_self _)
  exact Subgroup.map_injective (Subgroup.subtype_injective _) (by
    rw [Subgroup.map_subtype_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact hEq.symm)

section Certs



private theorem fiveLift_S8 {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    (ζ : G →* fiveProjective k ε π) (hζ : Function.Surjective ζ)
    (hker : ζ.ker ≤ Subgroup.center G) (hcard : Nat.card ζ.ker = 2)
    (hD : ∀ x : fiveProjective k ε π, x ∈ ζ '' D ↔ ∃ r : fiveReflectionGroup k ε π,
      (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π ∧
        (QuotientGroup.mk r : fiveProjective k ε π) = x)
    (hZ : ζ.ker ≤ commutator G) :
    ∃ ψ : ↥(commutator G) ≃* ↥(commutator ↥(fiveReflectionGroup k ε π)),
      ∀ x, (QuotientGroup.mk (ψ x) : fiveProjective k ε π) = ζ x := by
  classical
  have hGperfect := fiveLift_G_perfect hk ε π hS ζ hζ hker
  have hmapζ := fiveLift_map_zeta ζ hζ
  obtain ⟨ra, rb, hra, hrb, hrab_comm, hne, hnoncen⟩ :=
    exists_commuting_fiveReflections_notMem_center hk ε π
  obtain ⟨a, ha, haζ⟩ := (hD (QuotientGroup.mk ra)).mpr ⟨ra, hra, rfl⟩
  obtain ⟨b, hb, hbζ⟩ := (hD (QuotientGroup.mk rb)).mpr ⟨rb, hrb, rfl⟩
  have ha2 : a * a = 1 := hS.oddT.mul_self_eq_one ha
  have hb2 : b * b = 1 := hS.oddT.mul_self_eq_one hb
  have hra2 : ra * ra = 1 := fiveReflection_mul_self hra
  have hrb2 : rb * rb = 1 := fiveReflection_mul_self hrb
  have hrab2 : (ra * rb) * (ra * rb) = 1 := by
    calc (ra * rb) * (ra * rb) = ra * (rb * ra) * rb := by group
      _ = ra * (ra * rb) * rb := by rw [← hrab_comm.eq]
      _ = (ra * ra) * (rb * rb) := by group
      _ = 1 := by rw [hra2, hrb2, one_mul]
  have hab_comm : Commute a b := by
    by_contra hnc
    have hodd : Odd (orderOf (a * b)) := hS.oddT.odd_of_not_commute ha hb hnc
    have hodd' : Odd (orderOf (ζ (a * b))) :=
      hodd.of_dvd_nat (orderOf_map_dvd ζ (a * b))
    have hmk : ζ (a * b) = (QuotientGroup.mk (ra * rb) : fiveProjective k ε π) := by
      rw [map_mul, haζ, hbζ]
      exact (mk_coe_mul ra rb).symm
    have hsq : (QuotientGroup.mk (ra * rb) : fiveProjective k ε π) ^ 2 = 1 := by
      rw [pow_two, ← mk_coe_mul, hrab2, mk_coe_one]
    have hdvd : orderOf (ζ (a * b)) ∣ 2 := by
      rw [hmk]
      exact orderOf_dvd_iff_pow_eq_one.mpr hsq
    have hone : orderOf (ζ (a * b)) = 1 := by
      obtain ⟨m, hm⟩ := hodd'
      rw [hm] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hzeta1 : ζ (a * b) = 1 := orderOf_eq_one_iff.mp hone
    exact hnoncen ((QuotientGroup.eq_one_iff (ra * rb)).mp (hmk.symm.trans hzeta1))
  have hx2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab_comm.eq]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hxG : a * b ∈ commutator G := by
    have h := hS.abelianization_eq ha hb
    have h2 : Abelianization.of (a * b) = 1 := by
      rw [map_mul, h, ← map_mul, hb2, map_one]
    rwa [← Abelianization.ker_of, MonoidHom.mem_ker]
  let ρ : ↥(commutator G) →* fiveProjective k ε π := ζ.comp (commutator G).subtype
  have hρrange : ρ.range = commutator (fiveProjective k ε π) := by
    change (ζ.comp (commutator G).subtype).range = commutator (fiveProjective k ε π)
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmapζ
  have hρker : ρ.ker ≤ Subgroup.center ↥(commutator G) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hker hx) (y : G))
  have hρcard : Nat.card ρ.ker = 2 := by
    change Nat.card ((ζ.ker).subgroupOf (commutator G)) = 2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv]
    exact hcard
  have hlift : ∃ x : ↥(commutator G),
      ρ x = (QuotientGroup.mk (ra * rb) : fiveProjective k ε π) ∧ x * x = 1 :=
    ⟨⟨a * b, hxG⟩, by
      change ζ (a * b) = (QuotientGroup.mk (ra * rb) : fiveProjective k ε π)
      rw [map_mul, haζ, hbζ]
      exact (mk_coe_mul ra rb).symm, Subtype.ext hx2⟩
  obtain ⟨ψ, hψ⟩ := fiveReflection_involution_lift_cover hk ε π ρ hρrange hGperfect hρker
    hρcard hra hrb hrab_comm hne hlift
  exact ⟨ψ, fun x => (hψ x).symm⟩

private theorem fiveLift_false_of_card {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    (ζ : G →* fiveProjective k ε π) (hζ : Function.Surjective ζ)
    (hker : ζ.ker ≤ Subgroup.center G) (hcard : Nat.card ζ.ker = 2)
    (hD : ∀ x : fiveProjective k ε π, x ∈ ζ '' D ↔ ∃ r : fiveReflectionGroup k ε π,
      (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π ∧
        (QuotientGroup.mk r : fiveProjective k ε π) = x)
    (hZ : ζ.ker ≤ commutator G)
    (hinf : commutator ↥(fiveReflectionGroup k ε π) ⊓
      Subgroup.center (fiveReflectionGroup k ε π) = ⊥) : False := by
  classical
  obtain ⟨ψ, hψ'⟩ := fiveLift_S8 hk ε π hS ζ hζ hker hcard hD hZ
  let ρ : ↥(commutator G) →* fiveProjective k ε π := ζ.comp (commutator G).subtype
  have hρrange : ρ.range = commutator (fiveProjective k ε π) := by
    change (ζ.comp (commutator G).subtype).range = commutator (fiveProjective k ε π)
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact fiveLift_map_zeta ζ hζ
  have hρcard : Nat.card ρ.ker = 2 := by
    change Nat.card ((ζ.ker).subgroupOf (commutator G)) = 2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv]
    exact hcard
  have hPcard : Nat.card (commutator (fiveProjective k ε π)) =
      Nat.card ↥(commutator ↥(fiveReflectionGroup k ε π)) := by
    let f : ↥(commutator ↥(fiveReflectionGroup k ε π)) →* fiveProjective k ε π :=
      (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))).comp
        (commutator ↥(fiveReflectionGroup k ε π)).subtype
    have hfrange : f.range = commutator (fiveProjective k ε π) := by
      change (((QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))).comp
        (commutator ↥(fiveReflectionGroup k ε π)).subtype)).range =
        commutator (fiveProjective k ε π)
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact fiveLift_map_mk ε π
    have hfker : Nat.card f.ker = 1 := by
      have hbot : f.ker = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        change (QuotientGroup.mk (x : fiveReflectionGroup k ε π) :
          fiveProjective k ε π) = 1 at hx
        rw [QuotientGroup.eq_one_iff] at hx
        have hxI : (x : fiveReflectionGroup k ε π) ∈
            commutator ↥(fiveReflectionGroup k ε π) ⊓
              Subgroup.center (fiveReflectionGroup k ε π) := ⟨x.2, hx⟩
        rw [hinf] at hxI
        exact Subtype.ext (Subgroup.mem_bot.mp hxI)
      rw [hbot, Subgroup.card_bot]
    have h1 := Subgroup.card_ker_mul_card_range f
    rw [hfker, hfrange, one_mul] at h1
    exact h1
  have hGcard : Nat.card ↥(commutator G) =
      Nat.card ↥(commutator ↥(fiveReflectionGroup k ε π)) := Nat.card_congr ψ.toEquiv
  have hρcard' : 2 * Nat.card (commutator (fiveProjective k ε π)) =
      Nat.card ↥(commutator G) := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    rw [hρcard, hρrange] at h1
    exact h1
  have hcon : Nat.card ↥(commutator ↥(fiveReflectionGroup k ε π)) =
      2 * Nat.card ↥(commutator ↥(fiveReflectionGroup k ε π)) := by
    omega
  have hpos : 0 < Nat.card ↥(commutator ↥(fiveReflectionGroup k ε π)) := Nat.card_pos
  omega

private theorem fiveLift_false_of_parity {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    (ζ : G →* fiveProjective k ε π) (hζ : Function.Surjective ζ)
    (hker : ζ.ker ≤ Subgroup.center G) (hcard : Nat.card ζ.ker = 2)
    (hD : ∀ x : fiveProjective k ε π, x ∈ ζ '' D ↔ ∃ r : fiveReflectionGroup k ε π,
      (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π ∧
        (QuotientGroup.mk r : fiveProjective k ε π) = x)
    (hZ : ¬ ζ.ker ≤ commutator G)
    (hchar : Subgroup.center (fiveReflectionGroup k ε π) ≤
      (Matrix.GeneralLinearGroup.det.comp (fiveReflectionGroup k ε π).subtype).ker) : False := by
  classical
  obtain ⟨d, hd⟩ := hS.nonempty
  have hGidx : (commutator G).index = 2 := by
    have h0 : (commutator G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle : (commutator G).index ≤ 2 := hS.index_commutator_le_two
    have hne1 : (commutator G).index ≠ 1 := by
      intro h1; exact hZ (by rw [Subgroup.index_eq_one.mp h1]; exact le_top)
    omega
  let η : fiveProjective k ε π →* (ZMod 5)ˣ :=
    QuotientGroup.lift (Subgroup.center (fiveReflectionGroup k ε π))
      (Matrix.GeneralLinearGroup.det.comp (fiveReflectionGroup k ε π).subtype) hchar
  let χ : G →* (ZMod 5)ˣ := η.comp ζ
  have hχd : χ d = -1 := by
    obtain ⟨rd, hrd_refl, hrd_mk⟩ := (hD (ζ d)).mp ⟨d, hd, rfl⟩
    show η (ζ d) = -1
    rw [← hrd_mk]
    change (Matrix.GeneralLinearGroup.det.comp
        (fiveReflectionGroup k ε π).subtype) rd = -1
    exact det_fiveReflection hrd_refl
  have hex : ∃ z : G, z ∈ ζ.ker ∧ z ∉ commutator G := by
    by_contra h
    apply hZ
    intro x hx
    by_contra hx'
    exact h ⟨x, hx, hx'⟩
  obtain ⟨z, hzZ, hzG'⟩ := hex
  have hdnotG' : d ∉ commutator G := by
    intro hdG'
    have h1 : χ d = 1 := MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker χ hdG')
    rw [hχd] at h1
    exact absurd h1 (by decide)
  have hdinv : d⁻¹ ∉ commutator G := fun h =>
    hdnotG' (by simpa using (commutator G).inv_mem h)
  have hzd : z * d⁻¹ ∈ commutator G :=
    (Subgroup.mul_mem_iff_of_index_two hGidx).mpr (iff_of_false hzG' hdinv)
  have hz1 : χ z = 1 := by
    show η (ζ z) = 1
    rw [MonoidHom.mem_ker.mp hzZ, map_one]
  have hzd1 : χ (z * d⁻¹) = 1 :=
    MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker χ hzd)
  have h : χ z = χ (z * d⁻¹) * χ d := by
    rw [← map_mul, mul_assoc, inv_mul_cancel, mul_one]
  rw [hz1, hzd1, one_mul, hχd] at h
  exact absurd h (by decide)

private theorem fiveLift_good_of_ker_le {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    (ζ : G →* fiveProjective k ε π) (hζ : Function.Surjective ζ)
    (hker : ζ.ker ≤ Subgroup.center G) (hcard : Nat.card ζ.ker = 2)
    (hD : ∀ x : fiveProjective k ε π, x ∈ ζ '' D ↔ ∃ r : fiveReflectionGroup k ε π,
      (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π ∧
        (QuotientGroup.mk r : fiveProjective k ε π) = x)
    (hZ : ζ.ker ≤ commutator G)
    (hinf : commutator ↥(fiveReflectionGroup k ε π) ⊓
      Subgroup.center (fiveReflectionGroup k ε π) ≠ ⊥) :
    ∃ φ : G ≃* fiveReflectionGroup k ε π,
      (∀ g : G, (QuotientGroup.mk (φ g) : fiveProjective k ε π) = ζ g) ∧
        ∀ g : G, g ∈ D ↔ (φ g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := by
  classical
  have hGperfect := fiveLift_G_perfect hk ε π hS ζ hζ hker
  obtain ⟨ψ, hψ'⟩ := fiveLift_S8 hk ε π hS ζ hζ hker hcard hD hZ
  obtain ⟨d, hd⟩ := hS.nonempty
  have hd2 : d * d = 1 := hS.oddT.mul_self_eq_one hd
  have hcenter_ne : Subgroup.center (fiveReflectionGroup k ε π) ≠ ⊥ := by
    intro h; exact hinf (by rw [h]; exact inf_bot_eq _)
  have hneg_mem : (-1 : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionGroup k ε π := by
    by_contra hneg
    exact hcenter_ne (center_fiveReflectionGroup_eq_bot hk ε π hneg)
  have hnegR' : (⟨-1, hneg_mem⟩ : fiveReflectionGroup k ε π) ∈
      commutator ↥(fiveReflectionGroup k ε π) := by
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
    have hxR' : (x : fiveReflectionGroup k ε π) ∈
        commutator ↥(fiveReflectionGroup k ε π) := x.2.1
    have hxZ : (x : fiveReflectionGroup k ε π) ∈
        Subgroup.center (fiveReflectionGroup k ε π) := x.2.2
    rcases (mem_center_fiveReflectionGroup_iff hk ε π _).mp hxZ with h1 | hneg
    · have hx1 : (x : fiveReflectionGroup k ε π) = 1 := Subtype.ext h1
      exact absurd (Subtype.ext hx1) hx
    · have heq : (x : fiveReflectionGroup k ε π) = ⟨-1, hneg_mem⟩ := Subtype.ext hneg
      rwa [heq] at hxR'
  have hcenter_le : Subgroup.center (fiveReflectionGroup k ε π) ≤
      (Matrix.GeneralLinearGroup.det.comp
        (fiveReflectionGroup k ε π).subtype).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change Matrix.GeneralLinearGroup.det (x : GL (Fin (k + 1)) (ZMod 5)) = 1
    rcases (mem_center_fiveReflectionGroup_iff hk ε π x).mp hx with h1 | hneg
    · rw [h1, map_one]
    · have heq : x = ⟨-1, hneg_mem⟩ := Subtype.ext hneg
      rw [heq]
      exact MonoidHom.mem_ker.mp ((commutator_subset_ker_det_fiveReflection ε π) hnegR')
  obtain ⟨rd, hrd_refl, hrd_mk⟩ := (hD (ζ d)).mp ⟨d, hd, rfl⟩
  have hrd2 : rd * rd = 1 := fiveReflection_mul_self hrd_refl
  have hrd_notmem : rd ∉ commutator ↥(fiveReflectionGroup k ε π) := by
    intro h
    have h1 : (Matrix.GeneralLinearGroup.det.comp
        (fiveReflectionGroup k ε π).subtype) rd = 1 :=
      MonoidHom.mem_ker.mp ((commutator_subset_ker_det_fiveReflection ε π) h)
    rw [show (Matrix.GeneralLinearGroup.det.comp
        (fiveReflectionGroup k ε π).subtype) rd =
        Matrix.GeneralLinearGroup.det (rd : GL (Fin (k + 1)) (ZMod 5)) from rfl,
        det_fiveReflection hrd_refl] at h1
    exact absurd h1 (by decide)
  have hdnotG' : d ∉ commutator G := by
    intro hdG'
    have hmem : (QuotientGroup.mk rd : fiveProjective k ε π) ∈ (commutator G).map ζ :=
      ⟨d, hdG', hrd_mk.symm⟩
    rw [fiveLift_map_zeta ζ hζ, ← fiveLift_map_mk ε π] at hmem
    obtain ⟨rd', hrd'R', hrd'mk⟩ := hmem
    have hker : rd * rd'⁻¹ ∈ (QuotientGroup.mk'
        (Subgroup.center (fiveReflectionGroup k ε π))).ker := by
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk rd : fiveProjective k ε π) *
        (QuotientGroup.mk rd' : fiveProjective k ε π)⁻¹ = 1
      rw [show (QuotientGroup.mk rd' : fiveProjective k ε π) =
        QuotientGroup.mk rd from hrd'mk, mul_inv_cancel]
    rw [QuotientGroup.ker_mk'] at hker
    have hdetc : (Matrix.GeneralLinearGroup.det.comp
        (fiveReflectionGroup k ε π).subtype) (rd * rd'⁻¹) = 1 :=
      MonoidHom.mem_ker.mp (hcenter_le hker)
    rw [map_mul, map_inv] at hdetc
    have hdet_rd' : (Matrix.GeneralLinearGroup.det.comp
        (fiveReflectionGroup k ε π).subtype) rd' = 1 :=
      MonoidHom.mem_ker.mp ((commutator_subset_ker_det_fiveReflection ε π) hrd'R')
    rw [hdet_rd', inv_one, mul_one] at hdetc
    rw [show (Matrix.GeneralLinearGroup.det.comp
        (fiveReflectionGroup k ε π).subtype) rd =
        Matrix.GeneralLinearGroup.det (rd : GL (Fin (k + 1)) (ZMod 5)) from rfl,
        det_fiveReflection hrd_refl] at hdetc
    exact absurd hdetc (by decide)
  have hGidx : (commutator G).index = 2 := by
    have h0 : (commutator G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle : (commutator G).index ≤ 2 := hS.index_commutator_le_two
    have hne1 : (commutator G).index ≠ 1 := by
      intro h1
      exact hdnotG' (Subgroup.index_eq_one.mp h1 ▸ Subgroup.mem_top d)
    omega
  have hconj : ∀ x : ↥(commutator G),
      (ψ ⟨d * (x : G) * d⁻¹, by
        haveI : (commutator G).Normal := inferInstance
        exact (inferInstance : (commutator G).Normal).conj_mem (x : G) x.2 d⟩ :
          fiveReflectionGroup k ε π) =
      rd * (ψ x : fiveReflectionGroup k ε π) * rd⁻¹ := by
    let hcd : ↥(commutator G) →* ↥(commutator G) :=
      { toFun := fun x => ⟨d * (x : G) * d⁻¹, by
          haveI : (commutator G).Normal := inferInstance
          exact (inferInstance : (commutator G).Normal).conj_mem (x : G) x.2 d⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    let hcr : ↥(commutator ↥(fiveReflectionGroup k ε π)) →*
        ↥(commutator ↥(fiveReflectionGroup k ε π)) :=
      { toFun := fun x => ⟨rd * (x : fiveReflectionGroup k ε π) * rd⁻¹, by
          haveI : (commutator ↥(fiveReflectionGroup k ε π)).Normal := inferInstance
          exact (inferInstance : (commutator ↥(fiveReflectionGroup k ε π)).Normal).conj_mem
            (x : fiveReflectionGroup k ε π) x.2 rd⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hdiff : ∀ x : ↥(commutator G),
        (ψ.toMonoidHom.comp hcd) x * ((hcr.comp ψ.toMonoidHom) x)⁻¹ ∈
          Subgroup.center ↥(commutator ↥(fiveReflectionGroup k ε π)) := by
      intro x
      apply Subgroup.mem_center_iff.mpr
      intro z
      have hyR : ((((ψ.toMonoidHom.comp hcd) x *
          ((hcr.comp ψ.toMonoidHom) x)⁻¹ :
            ↥(commutator ↥(fiveReflectionGroup k ε π))) :
              fiveReflectionGroup k ε π)) ∈ Subgroup.center (fiveReflectionGroup k ε π) := by
        rw [← QuotientGroup.eq_one_iff]
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mk_coe_mul, mk_coe_inv]
        have h1 : (QuotientGroup.mk (((ψ.toMonoidHom.comp hcd) x) :
            ↥(commutator ↥(fiveReflectionGroup k ε π))) : fiveProjective k ε π) =
            ζ (((hcd) x : ↥(commutator G)) : G) := hψ' (hcd x)
        have h2 : (QuotientGroup.mk (((hcr.comp ψ.toMonoidHom) x) :
            ↥(commutator ↥(fiveReflectionGroup k ε π))) : fiveProjective k ε π) =
            ζ (((hcd) x : ↥(commutator G)) : G) := by
          have hc : (((hcr.comp ψ.toMonoidHom) x) : fiveReflectionGroup k ε π) =
              rd * (ψ x : fiveReflectionGroup k ε π) * rd⁻¹ := by
            simp only [MonoidHom.comp_apply, hcr]
            rfl
          rw [hc, mk_coe_mul, mk_coe_mul, mk_coe_inv, hrd_mk, hψ' x,
            show ((hcd x : ↥(commutator G)) : G) = d * (x : G) * d⁻¹ from rfl,
            map_mul, map_mul, map_inv]
        rw [h1, h2, mul_inv_cancel]
      exact Subtype.ext (Subgroup.mem_center_iff.mp hyR (z : fiveReflectionGroup k ε π))
    have heq : ψ.toMonoidHom.comp hcd = hcr.comp ψ.toMonoidHom :=
      monoidHom_eq_of_center_diff_mem hGperfect hdiff
    intro x
    change ((ψ.toMonoidHom.comp hcd) x : fiveReflectionGroup k ε π) =
      ((hcr.comp ψ.toMonoidHom) x : fiveReflectionGroup k ε π)
    exact congrArg (fun y : ↥(commutator ↥(fiveReflectionGroup k ε π)) =>
      (y : fiveReflectionGroup k ε π)) (DFunLike.congr_fun heq x)
  obtain ⟨φhom, hφG', hφd, hφinj⟩ :=
    exists_monoidHom_of_index_two_extension hGidx ψ hd2 hrd2 hdnotG' hrd_notmem hconj
  have hmk_phi : ∀ g : G, (QuotientGroup.mk (φhom g) : fiveProjective k ε π) = ζ g := by
    intro g
    by_cases hg : g ∈ commutator G
    · rw [hφG' ⟨g, hg⟩]
      exact hψ' ⟨g, hg⟩
    · have hgd : g * d⁻¹ ∈ commutator G :=
        (Subgroup.mul_mem_iff_of_index_two hGidx).mpr (iff_of_false hg (by
          intro h; exact hdnotG' (by simpa using (commutator G).inv_mem h)))
      have hdecomp : (g * d⁻¹) * d = g := by rw [mul_assoc, inv_mul_cancel, mul_one]
      rw [← hdecomp, map_mul, hφG' ⟨g * d⁻¹, hgd⟩, hφd, mk_coe_mul, hψ' ⟨g * d⁻¹, hgd⟩,
        hrd_mk, ← map_mul ζ]
  have hcardG : Nat.card G = 2 * Nat.card ↥(commutator G) := by
    have h := Subgroup.card_mul_index (H := commutator G)
    rw [hGidx] at h
    omega
  have hcardR : Nat.card ↥(fiveReflectionGroup k ε π) =
      2 * Nat.card ↥(commutator ↥(fiveReflectionGroup k ε π)) := by
    have h := Subgroup.card_mul_index (H := commutator ↥(fiveReflectionGroup k ε π))
    rw [index_commutator_fiveReflectionGroup hk ε π] at h
    omega
  have hcard_eq : Nat.card G = Nat.card ↥(fiveReflectionGroup k ε π) := by
    rw [hcardG, hcardR, Nat.card_congr ψ.toEquiv]
  have hsurj : Function.Surjective φhom := by
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφinj, Subgroup.card_top,
      hcard_eq]
  have hphiD : ∀ g : G, g ∈ D ↔ (φhom g : GL (Fin (k + 1)) (ZMod 5)) ∈
      fiveReflections k ε π := by
    have hclass : ∀ r : fiveReflectionGroup k ε π,
        r ∈ φhom '' D ↔ (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := by
      intro r
      constructor
      · rintro ⟨g, hg, rfl⟩
        obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj hd hg)
        rw [map_mul, map_mul, map_inv, hφd]
        exact conj_mem_fiveReflections (fiveForm_mulVec_of_mem (φhom c).2) hrd_refl
      · intro hr
        obtain ⟨c, hc, hce⟩ := isConj_of_mem_fiveReflections hk ε π hrd_refl hr
        obtain ⟨g, hg⟩ := hsurj ⟨c, hc⟩
        refine ⟨g * d * g⁻¹, hS.conj_mem g hd, ?_⟩
        have hgc : (φhom g : GL (Fin (k + 1)) (ZMod 5)) = c := congrArg Subtype.val hg
        have hgc' : φhom g = ⟨c, hc⟩ := Subtype.ext hgc
        rw [map_mul, map_mul, map_inv, hφd, hgc']
        exact Subtype.ext hce
    intro g
    constructor
    · intro hg; exact (hclass (φhom g)).mp ⟨g, hg, rfl⟩
    · intro hg
      obtain ⟨g', hg', hg'e⟩ := (hclass (φhom g)).mpr hg
      exact (hφinj hg'e) ▸ hg'
  refine ⟨MulEquiv.ofBijective φhom ⟨hφinj, hsurj⟩, ?_, ?_⟩
  · intro g
    exact hmk_phi g
  · intro g
    exact hphiD g

private theorem fiveLift_good_of_not_ker_le {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    (ζ : G →* fiveProjective k ε π) (hζ : Function.Surjective ζ)
    (hker : ζ.ker ≤ Subgroup.center G) (hcard : Nat.card ζ.ker = 2)
    (hD : ∀ x : fiveProjective k ε π, x ∈ ζ '' D ↔ ∃ r : fiveReflectionGroup k ε π,
      (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π ∧
        (QuotientGroup.mk r : fiveProjective k ε π) = x)
    (hZ : ¬ ζ.ker ≤ commutator G)
    (hchar : ¬ Subgroup.center (fiveReflectionGroup k ε π) ≤
      (Matrix.GeneralLinearGroup.det.comp (fiveReflectionGroup k ε π).subtype).ker) :
    ∃ φ : G ≃* fiveReflectionGroup k ε π,
      (∀ g : G, (QuotientGroup.mk (φ g) : fiveProjective k ε π) = ζ g) ∧
        ∀ g : G, g ∈ D ↔ (φ g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := by
  classical
  have hGidx : (commutator G).index = 2 := by
    have h0 : (commutator G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle : (commutator G).index ≤ 2 := hS.index_commutator_le_two
    have hne1 : (commutator G).index ≠ 1 := by
      intro h1; exact hZ (by rw [Subgroup.index_eq_one.mp h1]; exact le_top)
    omega
  obtain ⟨d, hd⟩ := hS.nonempty
  have hcenter_ne : Subgroup.center (fiveReflectionGroup k ε π) ≠ ⊥ := by
    intro hcontra; exact hchar (by rw [hcontra]; exact bot_le)
  have hneg_mem : (-1 : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionGroup k ε π := by
    by_contra hneg
    exact hcenter_ne (center_fiveReflectionGroup_eq_bot hk ε π hneg)
  have hneg_notmem_R' : (⟨-1, hneg_mem⟩ : fiveReflectionGroup k ε π) ∉
      commutator ↥(fiveReflectionGroup k ε π) := by
    intro h
    exact hchar (by
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      change Matrix.GeneralLinearGroup.det (x : GL (Fin (k + 1)) (ZMod 5)) = 1
      rcases (mem_center_fiveReflectionGroup_iff hk ε π x).mp hx with h1 | hneg
      · rw [h1, map_one]
      · have heq : x = ⟨-1, hneg_mem⟩ := Subtype.ext hneg
        rw [heq]
        exact MonoidHom.mem_ker.mp ((commutator_subset_ker_det_fiveReflection ε π) h))
  have hZinf : ζ.ker ⊓ commutator G = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hzZ, hzG⟩ := hz
    by_contra hz1
    apply hZ
    have hz2 : orderOf z = 2 := by
      have hdvd : orderOf z ∣ Nat.card ↥(ζ.ker) := Subgroup.orderOf_dvd_natCard _ hzZ
      rw [hcard] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hz1
      · exact h2
    have hzp : Subgroup.zpowers z = ζ.ker := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ)
      rw [Nat.card_zpowers, hz2, hcard]
    rw [← hzp]
    exact Subgroup.zpowers_le.mpr hzG
  have hR'inf : commutator ↥(fiveReflectionGroup k ε π) ⊓
      Subgroup.center (fiveReflectionGroup k ε π) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxR', hxc⟩ := hx
    rcases (mem_center_fiveReflectionGroup_iff hk ε π x).mp hxc with h1 | hneg
    · exact Subtype.ext h1
    · have heq : (x : fiveReflectionGroup k ε π) = ⟨-1, hneg_mem⟩ := Subtype.ext hneg
      exact absurd (heq ▸ hxR') hneg_notmem_R'
  have hmk_neg1 : (QuotientGroup.mk (⟨-1, hneg_mem⟩ : fiveReflectionGroup k ε π) :
      fiveProjective k ε π) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr
      ((mem_center_fiveReflectionGroup_iff hk ε π _).mpr (Or.inr rfl))
  have hψ : ∃ ψ : ↥(commutator G) ≃* ↥(commutator ↥(fiveReflectionGroup k ε π)),
      ∀ x, (QuotientGroup.mk (ψ x) : fiveProjective k ε π) = ζ x := by
    let ζG : ↥(commutator G) →* ↥(commutator (fiveProjective k ε π)) :=
      (ζ.comp (commutator G).subtype).codRestrict (commutator (fiveProjective k ε π))
        (fun x => by rw [← fiveLift_map_zeta ζ hζ]; exact ⟨x, x.2, rfl⟩)
    have hζGker : ζG.ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : ζ (x : G) = 1 := by
        have h := congrArg (fun y : ↥(commutator (fiveProjective k ε π)) =>
          (y : fiveProjective k ε π)) hx
        change ζ (x : G) = 1 at h
        exact h
      have hxI : (x : G) ∈ ζ.ker ⊓ commutator G := ⟨hx', x.2⟩
      rw [hZinf] at hxI
      exact Subtype.ext (Subgroup.mem_bot.mp hxI)
    have hζGsurj : Function.Surjective ζG := by
      intro y
      have hy : (y : fiveProjective k ε π) ∈ (commutator G).map ζ := by
        rw [fiveLift_map_zeta ζ hζ]; exact y.2
      obtain ⟨x, hx, hxζ⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxζ⟩
    let eG : ↥(commutator G) ≃* ↥(commutator (fiveProjective k ε π)) :=
      MulEquiv.ofBijective ζG ⟨(MonoidHom.ker_eq_bot_iff ζG).mp hζGker, hζGsurj⟩
    let mkR' : ↥(commutator ↥(fiveReflectionGroup k ε π)) →*
        ↥(commutator (fiveProjective k ε π)) :=
      ((QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))).comp
        (commutator ↥(fiveReflectionGroup k ε π)).subtype).codRestrict
          (commutator (fiveProjective k ε π))
          (fun x => by rw [← fiveLift_map_mk ε π]; exact ⟨x, x.2, rfl⟩)
    have hmkR'ker : mkR'.ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : (QuotientGroup.mk ((x : ↥(commutator ↥(fiveReflectionGroup k ε π))) :
          fiveReflectionGroup k ε π) : fiveProjective k ε π) = 1 := by
        have h := congrArg (fun y : ↥(commutator (fiveProjective k ε π)) =>
          (y : fiveProjective k ε π)) hx
        change (QuotientGroup.mk ((x : ↥(commutator ↥(fiveReflectionGroup k ε π))) :
          fiveReflectionGroup k ε π) : fiveProjective k ε π) = 1 at h
        exact h
      rw [QuotientGroup.eq_one_iff] at hx'
      have hx := hx'
      have hxI : (x : fiveReflectionGroup k ε π) ∈
          commutator ↥(fiveReflectionGroup k ε π) ⊓
            Subgroup.center (fiveReflectionGroup k ε π) := ⟨x.2, hx⟩
      rw [hR'inf] at hxI
      exact Subtype.ext (Subgroup.mem_bot.mp hxI)
    have hmkR'surj : Function.Surjective mkR' := by
      intro y
      have hy : (y : fiveProjective k ε π) ∈ (commutator ↥(fiveReflectionGroup k ε π)).map
          (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) := by
        rw [fiveLift_map_mk ε π]; exact y.2
      obtain ⟨x, hx, hxζ⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxζ⟩
    let eR : ↥(commutator ↥(fiveReflectionGroup k ε π)) ≃*
        ↥(commutator (fiveProjective k ε π)) :=
      MulEquiv.ofBijective mkR' ⟨(MonoidHom.ker_eq_bot_iff mkR').mp hmkR'ker, hmkR'surj⟩
    refine ⟨eG.trans eR.symm, ?_⟩
    intro x
    have h2 : mkR' (eR.symm (eG x)) = eG x := eR.apply_symm_apply (eG x)
    have h3 : (QuotientGroup.mk ((eR.symm (eG x) :
        ↥(commutator ↥(fiveReflectionGroup k ε π))) : fiveReflectionGroup k ε π) :
        fiveProjective k ε π) = (eG x : fiveProjective k ε π) := by
      have h := congrArg (fun y : ↥(commutator (fiveProjective k ε π)) =>
        (y : fiveProjective k ε π)) h2
      change (QuotientGroup.mk ((eR.symm (eG x) :
          ↥(commutator ↥(fiveReflectionGroup k ε π))) : fiveReflectionGroup k ε π) :
          fiveProjective k ε π) = (eG x : fiveProjective k ε π) at h
      exact h
    exact h3.trans rfl
  obtain ⟨ψ, hψ'⟩ := hψ
  have hex : ∃ z : G, z ∈ ζ.ker ∧ z ∉ commutator G := by
    by_contra h
    apply hZ
    intro x hx
    by_contra hx'
    exact h ⟨x, hx, hx'⟩
  obtain ⟨z, hzZ, hzG'⟩ := hex
  have hrd2 : (⟨-1, hneg_mem⟩ : fiveReflectionGroup k ε π) * ⟨-1, hneg_mem⟩ = 1 := by
    apply Subtype.ext
    show (-1 : GL (Fin (k + 1)) (ZMod 5)) * (-1) = 1
    rw [neg_mul_neg, mul_one]
  have hz2 : z * z = 1 := by
    have h := pow_card_eq_one' (G := ↥(ζ.ker)) (x := ⟨z, hzZ⟩)
    rw [hcard] at h
    simpa [pow_two, Subgroup.coe_mul] using congrArg Subtype.val h
  have hconj : ∀ x : ↥(commutator G),
      (ψ ⟨z * (x : G) * z⁻¹, by
        haveI : (commutator G).Normal := inferInstance
        exact (inferInstance : (commutator G).Normal).conj_mem (x : G) x.2 z⟩ :
          fiveReflectionGroup k ε π) =
      (⟨-1, hneg_mem⟩ : fiveReflectionGroup k ε π) * (ψ x : fiveReflectionGroup k ε π) *
        ⟨-1, hneg_mem⟩⁻¹ := by
    intro x
    have hx : (⟨z * (x : G) * z⁻¹, by
        haveI : (commutator G).Normal := inferInstance
        exact (inferInstance : (commutator G).Normal).conj_mem (x : G) x.2 z⟩ :
          ↥(commutator G)) = x := by
      apply Subtype.ext
      change z * (x : G) * z⁻¹ = (x : G)
      have hc : Commute z (x : G) := (Subgroup.mem_center_iff.mp (hker hzZ) (x : G)).symm
      rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hx]
    rw [show (⟨-1, hneg_mem⟩ : fiveReflectionGroup k ε π) *
        (ψ x : fiveReflectionGroup k ε π) * ⟨-1, hneg_mem⟩⁻¹ =
        (ψ x : fiveReflectionGroup k ε π) by
      have hzc : (⟨-1, hneg_mem⟩ : fiveReflectionGroup k ε π) ∈
          Subgroup.center (fiveReflectionGroup k ε π) :=
        (mem_center_fiveReflectionGroup_iff hk ε π _).mpr (Or.inr rfl)
      have hcomm : (ψ x : fiveReflectionGroup k ε π) * ⟨-1, hneg_mem⟩ =
          ⟨-1, hneg_mem⟩ * (ψ x : fiveReflectionGroup k ε π) :=
        Subgroup.mem_center_iff.mp hzc (ψ x)
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]]
  obtain ⟨φhom, hφG', hφd, hφinj⟩ :=
    exists_monoidHom_of_index_two_extension hGidx ψ hz2 hrd2 hzG' hneg_notmem_R' hconj
  have hmk_phi : ∀ g : G, (QuotientGroup.mk (φhom g) : fiveProjective k ε π) = ζ g := by
    intro g
    by_cases hg : g ∈ commutator G
    · rw [hφG' ⟨g, hg⟩]
      exact hψ' ⟨g, hg⟩
    · have hgd : g * z⁻¹ ∈ commutator G :=
        (Subgroup.mul_mem_iff_of_index_two hGidx).mpr (iff_of_false hg (by
          intro h; exact hzG' (by simpa using (commutator G).inv_mem h)))
      have hdecomp : (g * z⁻¹) * z = g := by rw [mul_assoc, inv_mul_cancel, mul_one]
      rw [← hdecomp]
      rw [map_mul φhom (g * z⁻¹) z, map_mul ζ (g * z⁻¹) z]
      rw [hφG' ⟨g * z⁻¹, hgd⟩, hφd, mk_coe_mul,
        hψ' ⟨g * z⁻¹, hgd⟩, hmk_neg1, MonoidHom.mem_ker.mp hzZ]
  have hcardG : Nat.card G = 2 * Nat.card ↥(commutator G) := by
    have h := Subgroup.card_mul_index (H := commutator G)
    rw [hGidx] at h
    omega
  have hcardR : Nat.card ↥(fiveReflectionGroup k ε π) =
      2 * Nat.card ↥(commutator ↥(fiveReflectionGroup k ε π)) := by
    have h := Subgroup.card_mul_index (H := commutator ↥(fiveReflectionGroup k ε π))
    rw [index_commutator_fiveReflectionGroup hk ε π] at h
    omega
  have hcard_eq : Nat.card G = Nat.card ↥(fiveReflectionGroup k ε π) := by
    rw [hcardG, hcardR, Nat.card_congr ψ.toEquiv]
  have hsurj : Function.Surjective φhom := by
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφinj, Subgroup.card_top,
      hcard_eq]
  have hφd_mem : (φhom d : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := by
    have hdet_neg_ne : Matrix.GeneralLinearGroup.det (-1 : GL (Fin (k + 1)) (ZMod 5)) ≠ 1 := by
      intro h1
      apply hchar
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      change Matrix.GeneralLinearGroup.det (x : GL (Fin (k + 1)) (ZMod 5)) = 1
      rcases (mem_center_fiveReflectionGroup_iff hk ε π x).mp hx with h2 | h2
      · rw [h2, map_one]
      · have heq : x = ⟨-1, hneg_mem⟩ := Subtype.ext h2
        rw [heq]
        exact h1
    have hdet_neg : Matrix.GeneralLinearGroup.det (-1 : GL (Fin (k + 1)) (ZMod 5)) = -1 := by
      rw [det_neg_one_five]
      rw [det_neg_one_five] at hdet_neg_ne
      rcases Nat.even_or_odd (k + 1) with hev | hod
      · exact absurd hev.neg_one_pow hdet_neg_ne
      · exact hod.neg_one_pow
    have hdG' : d ∉ commutator G := by
      intro hdG
      have hDsub : D ⊆ commutator G := by
        intro y hy
        obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj hd hy)
        exact (inferInstance : (commutator G).Normal).conj_mem d hdG c
      exact hzG' ((hS.eq_top_of_subset _ hDsub) ▸ Subgroup.mem_top z)
    have hgd : d * z⁻¹ ∈ commutator G :=
      (Subgroup.mul_mem_iff_of_index_two hGidx).mpr (iff_of_false hdG' (fun h =>
        hzG' (by simpa using (commutator G).inv_mem h)))
    have hφform : φhom d = ψ ⟨d * z⁻¹, hgd⟩ * ⟨-1, hneg_mem⟩ := by
      have h1 : φhom ((d * z⁻¹) * z) = φhom (d * z⁻¹) * φhom z := map_mul _ _ _
      rw [show (d * z⁻¹) * z = d from by rw [mul_assoc, inv_mul_cancel, mul_one]] at h1
      rw [h1, hφG' ⟨d * z⁻¹, hgd⟩, hφd]
    obtain ⟨r, hr_refl, hr_mk⟩ := (hD (ζ d)).mp ⟨d, hd, rfl⟩
    have hmk_eq : (QuotientGroup.mk (φhom d) : fiveProjective k ε π) =
        (QuotientGroup.mk r : fiveProjective k ε π) := by
      rw [hmk_phi d]; exact hr_mk.symm
    have hmemc : φhom d * r⁻¹ ∈ Subgroup.center (fiveReflectionGroup k ε π) := by
      rw [← QuotientGroup.eq_one_iff]
      rw [mk_coe_mul, mk_coe_inv, hmk_eq, mul_inv_cancel]
    have hcr : φhom d = (φhom d * r⁻¹) * r := by group
    rcases (mem_center_fiveReflectionGroup_iff hk ε π (φhom d * r⁻¹)).mp hmemc with hc1 | hcneg
    · have hc1' : φhom d * r⁻¹ = 1 := Subtype.ext hc1
      have heq : φhom d = r := by rw [hcr, hc1', one_mul]
      rw [heq]; exact hr_refl
    · exfalso
      have hcneg' : φhom d * r⁻¹ = ⟨-1, hneg_mem⟩ := Subtype.ext hcneg
      have hdet1 : Matrix.GeneralLinearGroup.det (φhom d : GL (Fin (k + 1)) (ZMod 5)) = -1 := by
        rw [hφform, Subgroup.coe_mul, map_mul]
        have h1 : Matrix.GeneralLinearGroup.det
            ((ψ ⟨d * z⁻¹, hgd⟩ : fiveReflectionGroup k ε π) :
              GL (Fin (k + 1)) (ZMod 5)) = 1 :=
          MonoidHom.mem_ker.mp
            ((commutator_subset_ker_det_fiveReflection ε π) (ψ ⟨d * z⁻¹, hgd⟩).2)
        rw [h1, one_mul, hdet_neg]
      have hdet2 : Matrix.GeneralLinearGroup.det (φhom d : GL (Fin (k + 1)) (ZMod 5)) = 1 := by
        have heq : φhom d = ⟨-1, hneg_mem⟩ * r := by rw [hcr, hcneg']
        rw [heq, Subgroup.coe_mul, map_mul, det_fiveReflection hr_refl, hdet_neg]
        rw [show (-1 : (ZMod 5)ˣ) * (-1) = 1 from by decide]
      rw [hdet1] at hdet2
      exact absurd hdet2 (by decide)
  have hclass : ∀ r : fiveReflectionGroup k ε π,
      r ∈ φhom '' D ↔ (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := by
    intro r
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj hd hg)
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_fiveReflections (fiveForm_mulVec_of_mem (φhom c).2) hφd_mem
    · intro hr
      obtain ⟨c, hc, hce⟩ := isConj_of_mem_fiveReflections hk ε π hφd_mem hr
      obtain ⟨g, hg⟩ := hsurj ⟨c, hc⟩
      refine ⟨g * d * g⁻¹, hS.conj_mem g hd, ?_⟩
      have hgc : (φhom g : GL (Fin (k + 1)) (ZMod 5)) = c := congrArg Subtype.val hg
      have hgc' : φhom g = ⟨c, hc⟩ := Subtype.ext hgc
      rw [map_mul, map_mul, map_inv, hgc']
      exact Subtype.ext hce
  have hphiD : ∀ g : G, g ∈ D ↔ (φhom g : GL (Fin (k + 1)) (ZMod 5)) ∈
      fiveReflections k ε π := by
    intro g
    constructor
    · intro hg; exact (hclass (φhom g)).mp ⟨g, hg, rfl⟩
    · intro hg
      obtain ⟨g', hg', hg'e⟩ := (hclass (φhom g)).mpr hg
      exact (hφinj hg'e) ▸ hg'
  refine ⟨MulEquiv.ofBijective φhom ⟨hφinj, hsurj⟩, ?_, ?_⟩
  · intro g
    exact hmk_phi g
  · intro g
    exact hphiD g

theorem centralTwoExtension_fiveReflection {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    (ζ : G →* fiveProjective k ε π) (hζ : Function.Surjective ζ)
    (hker : ζ.ker ≤ Subgroup.center G) (hcard : Nat.card ζ.ker = 2)
    (hD : ∀ x : fiveProjective k ε π, x ∈ ζ '' D ↔ ∃ r : fiveReflectionGroup k ε π,
      (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π ∧
        (QuotientGroup.mk r : fiveProjective k ε π) = x) :
    ∃ φ : G ≃* fiveReflectionGroup k ε π,
      (∀ g : G, (QuotientGroup.mk (φ g) : fiveProjective k ε π) = ζ g) ∧
        ∀ g : G, g ∈ D ↔ (φ g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := by
  classical
  by_cases hZ : ζ.ker ≤ commutator G
  · by_cases hinf : commutator ↥(fiveReflectionGroup k ε π) ⊓
        Subgroup.center (fiveReflectionGroup k ε π) = ⊥
    · exact absurd (fiveLift_false_of_card hk ε π hS ζ hζ hker hcard hD hZ hinf) not_false
    · exact fiveLift_good_of_ker_le hk ε π hS ζ hζ hker hcard hD hZ hinf
  · by_cases hchar : Subgroup.center (fiveReflectionGroup k ε π) ≤
        (Matrix.GeneralLinearGroup.det.comp (fiveReflectionGroup k ε π).subtype).ker
    · exact absurd (fiveLift_false_of_parity hk ε π hS ζ hζ hker hcard hD hZ hchar) not_false
    · exact fiveLift_good_of_not_ker_le hk ε π hS ζ hζ hker hcard hD hZ hchar

end Certs

end CFSG.OddTranspositions.PartThree
