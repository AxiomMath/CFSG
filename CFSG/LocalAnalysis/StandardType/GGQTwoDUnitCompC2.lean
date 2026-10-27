module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompA1
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompA2
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompB1
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompB2
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompB3
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompB4
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompC1

public section

namespace CFSG.StandardType.QTwo

open CFSG CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

theorem qtwoDB7_exists_component
    {H J : Subgroup G} {y : ↥H} {F0 : Type} [Field F0] [Finite F0]
    [CharP F0 2] (hF0 : Nat.card F0 = 4) {d : ℕ} (hd : 5 ≤ d)
    (hθ : ∃ θ : Su F0 2 1 d →* G, Function.Injective θ ∧ θ.range = J)
    (hy3 : y ^ 3 = 1)
    (hc : CFSG.Assembly.IsComponentOf J (H ⊓ Subgroup.centralizer ({(y : G)} : Set G)))
    (hl : J ≤ CFSG.Assembly.LargeEvenPLayer 3 H)
    (hrank : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian 3 E →
      (∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set G)) →
        Nat.card ↥E ≤ 3 ^ (d + 1)) :
    ∃ Q : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H), CFSG.IsComponent Q ∧
      (J.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) ≤ Q := by
  let R : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let π : ↥H →* (↥H ⧸ R) := QuotientGroup.mk' R
  let Jb : Subgroup (↥H ⧸ R) := (J.subgroupOf H).map π
  let τ : ↥H ⧸ R := π y
  obtain ⟨hJH, hJC, _, hcomp⟩ := qtwoDB7_transfer hc
  obtain ⟨hq', h3⟩ := qtwoDB7_su_data hF0 hd hθ hJH
  obtain ⟨hpc, hJbcomp⟩ := qtwoDB7_image_isPCompIn (X := ↥H) hy3 hJC hcomp h3
  have hlay : Jb ≤ CFSG.pLayer (↥H ⧸ R) 3 :=
    (Subgroup.map_mono (qtwoDB7_le_pLayer hl)).trans (qtwoDB7_map_pLayer_le (X := ↥H))
  have hY : CFSG.pPrimeCore 3 (↥H ⧸ R) = ⊥ := qtwoDB7_pPrimeCore_quotient (X := ↥H)
  have hτ : τ ^ 3 = 1 := by
    change (π y) ^ 3 = 1
    rw [← map_pow, hy3, map_one]
  rcases qtwoDB7_single_or_diag hY hτ hpc hlay with
    ⟨Q, hQ, hJQ⟩ | ⟨A, hA, h01, h02, h12, hJA⟩
  · exact ⟨Q, hQ, hJQ⟩
  · exfalso
    have hJq : CFSG.IsQuasisimple Jb := qtwoDB7_map_isQuasisimple (X := ↥H) hq' h3
    have hJC' : Jb ≤ Subgroup.centralizer ({τ} : Set (↥H ⧸ R)) := hpc.1
    obtain ⟨φ, hφ, hker, -⟩ :=
      qtwoDB7_diag_cover hτ hA h01 h02 h12 hJq hJC' hJbcomp hJA
    obtain ⟨e⟩ := qtwoDB7_centerQuot_su hF0 hd hθ hJH
    have hT := qtwoDB7_torusLift_quot hF0 hd e
    have hnab : ∃ a b : ↥Jb, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hJq.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥Jb) a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥Jb) b
      exact ⟨a', b', fun h => hab (by rw [← map_mul, ← map_mul, h])⟩
    obtain ⟨E, U, hU, hU2, hEU, hE, hEcard⟩ :=
      qtwoDB7_diag_torus hτ hA h01 h02 h12 hnab φ hφ hker hT
    obtain ⟨E', U', hU', hU2', hE'U', hE', hcard'⟩ := qtwoDB7_lift_to_G hU hU2 hE hEU
    have hle := hrank E' hE' ⟨U', hU', hU2', hE'U'⟩
    rw [hcard', hEcard] at hle
    have h3r : 3 * CFSG.StandardType.ggUnitaryTorusRank 3 d ≤ d + 1 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
    unfold CFSG.StandardType.ggUnitaryTorusRank at h3r
    split_ifs at h3r <;> omega

end CFSG.StandardType.QTwo

end
