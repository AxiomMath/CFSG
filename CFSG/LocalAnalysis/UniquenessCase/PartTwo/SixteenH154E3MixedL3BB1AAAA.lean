module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB1AAAAA
public import CFSG.Sporadic.HN.PGroupAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_H5_row_L3_three_le_stabSub (L : Subgroup (MulAut W)) :
    L ≤ stabSub (commSub ⊤ L) := by
  intro l hl
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have h1 : l⁻¹ (l u) ∈ commSub ⊤ L :=
      commSub_top_stable151b
        (fun x hx => L.mul_mem (L.mul_mem (L.inv_mem hl) hx) (L.inv_mem (L.inv_mem hl)))
        (l u) hu
    simpa using h1
  · intro hu
    exact commSub_top_stable151b (fun x hx => L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)) u hu

private theorem s16h_H5_row_L3_three_Z_subgroupOf_eq_fixV {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t) :
    (commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L) =
      fixV (autSub L (commSub ⊤ L)) := by
  apply Subgroup.map_injective (commSub ⊤ L).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left : commSub ⊤ L ⊓ fixV L ≤ commSub ⊤ L),
    map_subtype_fixV_autSub (s16h_H5_row_L3_three_le_stabSub L)]

private theorem s16h_H5_row_L3_three_seven_fix_Z {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2)
    (g : MulAut ↥(commSub ⊤ L))
    (hgc : g ∈ Subgroup.centralizer
      (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))))
    (hg7 : g ^ 7 = 1) :
    ∀ z : ↥(commSub ⊤ L), (z : W) ∈ commSub ⊤ L ⊓ fixV L → g z = z := by
  classical
  let Z : Subgroup W := commSub ⊤ L ⊓ fixV L
  let H : Subgroup (MulAut ↥(commSub ⊤ L)) := autSub L (commSub ⊤ L)
  obtain ⟨helemU, -, -, -, -, -, -⟩ := s16h_L3_res_algebra hc h.1
  have helemU2 : ∀ v : ↥(commSub ⊤ L), v ^ 2 = 1 := fun v => by
    rw [pow_two]; exact helemU v
  have hZc : Z.subgroupOf (commSub ⊤ L) = fixV H :=
    s16h_H5_row_L3_three_Z_subgroupOf_eq_fixV hc
  have hgstabZc : g ∈ stabSub (fixV H) := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      rw [mem_fixV] at hu ⊢
      intro ψ hψ
      have hcomm : ψ * g = g * ψ := Subgroup.mem_centralizer_iff.mp hgc ψ hψ
      have h1 : g (ψ u) = g u := by
        calc g (ψ u) = (g * ψ) u := rfl
          _ = (ψ * g) u := by rw [hcomm]
          _ = ψ (g u) := rfl
          _ = g u := hu ψ hψ
      exact g.injective h1
    · intro hu
      rw [mem_fixV] at hu ⊢
      intro ψ hψ
      have hcomm : ψ * g = g * ψ := Subgroup.mem_centralizer_iff.mp hgc ψ hψ
      calc ψ (g u) = (ψ * g) u := rfl
        _ = (g * ψ) u := by rw [hcomm]
        _ = g (ψ u) := rfl
        _ = g u := by rw [hu ψ hψ]
  have hgZpow : (resHom (fixV H) ⟨g, hgstabZc⟩ : MulAut ↥(fixV H)) ^ 7 = 1 := by
    have h1 : (⟨g, hgstabZc⟩ : stabSub (fixV H)) ^ 7 = 1 := by
      apply Subtype.ext
      simpa using hg7
    rw [← map_pow, h1, map_one]
  have hsqZ : ∀ v : ↥(fixV H), v ^ 2 = 1 := by
    intro v
    apply Subtype.ext
    simpa [pow_two] using helemU (v : ↥(commSub ⊤ L))
  have hPZ : IsPGroup 2 ↥(fixV H) := isPGroup_two_of_sq_eq_one hsqZ
  have hrkZ : rk ↥(fixV H) ≤ 2 := by
    rw [← hZc]
    have hcardeq : Nat.card ↥(Z.subgroupOf (commSub ⊤ L)) = Nat.card ↥Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Z ≤ commSub ⊤ L)).toEquiv
    show padicValNat 2 (Nat.card ↥(Z.subgroupOf (commSub ⊤ L))) ≤ 2
    rw [hcardeq]
    exact hd2
  have hcardfix : Nat.card ↥(fixV H) ≤ 4 := by
    rw [card_eq_two_pow (V := ↥(commSub ⊤ L)) helemU2 (fixV H)]
    calc (2 : ℕ) ^ rk ↥(fixV H) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hrkZ
      _ = 4 := by norm_num
  have hcarddvd : Nat.card ↥(fixV H) ∣ 2 ^ 2 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hPZ
    rw [hn]
    exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1
      (by rw [← hn]; simpa using hcardfix))
  have hGL : ∀ r ≤ 2, ¬ 7 ∣ Nat.card (GL (Fin r) (ZMod 2)) := by
    intro r hr
    rw [Matrix.card_GL_field (n := r)]
    interval_cases r <;> norm_num [Fin.prod_univ_succ, ZMod.card]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgZ1 : (resHom (fixV H) ⟨g, hgstabZc⟩ : MulAut ↥(fixV H)) = 1 :=
    CFSG.Sporadic.HN.eq_one_of_pow_eq_one (p := 2) (q := 7) (e := 2)
      (by norm_num) (by norm_num) hPZ hcarddvd hGL hgZpow
  intro z hz
  have hzH : z ∈ fixV H := by
    rw [← hZc, Subgroup.mem_subgroupOf]
    exact hz
  have h1 : (resHom (fixV H) ⟨g, hgstabZc⟩ : MulAut ↥(fixV H)) ⟨z, hzH⟩ = ⟨z, hzH⟩ := by
    rw [hgZ1]; rfl
  have h2 : g z = z := by
    have h3 := congrArg (fun w : ↥(fixV H) => ((w : ↥(commSub ⊤ L)))) h1
    rw [resHom_apply] at h3
    simpa using h3
  exact h2

theorem s16h_H5_row_L3_three_central_seven_eq_one {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2)
    (g : MulAut ↥(commSub ⊤ L))
    (hg : g ∈ autSub (A ⊓ normalizer (L : Set (MulAut W))) (commSub ⊤ L))
    (hgc : g ∈ Subgroup.centralizer
      (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))))
    (hg7 : g ^ 7 = 1) : g = 1 := by
  classical
  let Z : Subgroup W := commSub ⊤ L ⊓ fixV L
  let H : Subgroup (MulAut ↥(commSub ⊤ L)) := autSub L (commSub ⊤ L)
  obtain ⟨helemU, -, -, -, -, hcommH, hfaith⟩ := s16h_L3_res_algebra hc h.1
  have hZc : Z.subgroupOf (commSub ⊤ L) = fixV H :=
    s16h_H5_row_L3_three_Z_subgroupOf_eq_fixV hc
  have hgZ : ∀ z : ↥(commSub ⊤ L), (z : W) ∈ Z → g z = z :=
    s16h_H5_row_L3_three_seven_fix_Z hc h hd2 g hgc hg7
  by_cases hn : ∀ u : ↥(commSub ⊤ L), g u * u⁻¹ ∈ fixV H
  · exact hfaith g hg hn
  · exfalso
    have hfix := s16h_H5_row_L3_three_seven_fixed_mem_Z hc h g hgc hg7 hgZ hn
    have hodd : Odd (Nat.card ↥(Subgroup.zpowers g)) := by
      rw [Nat.card_zpowers]
      have hdvd : orderOf g ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hg7
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvd with h1 | h1
      · rw [h1]; norm_num
      · rw [h1]; norm_num
    have helemU2 : ∀ v : ↥(commSub ⊤ L), v ^ 2 = 1 := fun v => by
      rw [pow_two]; exact helemU v
    have hcop := CFSG.Quasithin.coprime_decomp (V := ↥(commSub ⊤ L))
      (P := Subgroup.zpowers g) hodd helemU2 (W := ⊤) (fun x _ w _ => Subgroup.mem_top (x w))
    have hsup : fixV (Subgroup.zpowers g) ⊔
        commSub (⊤ : Subgroup ↥(commSub ⊤ L)) (Subgroup.zpowers g) = ⊤ := by
      simpa [top_inf_eq, sup_comm] using hcop.1
    have hinf : fixV (Subgroup.zpowers g) ⊓
        commSub (⊤ : Subgroup ↥(commSub ⊤ L)) (Subgroup.zpowers g) = ⊥ := by
      simpa [top_inf_eq, inf_comm] using hcop.2
    have hCeq : fixV (Subgroup.zpowers g) = Z.subgroupOf (commSub ⊤ L) := by
      apply le_antisymm
      · intro u hu
        rw [Subgroup.mem_subgroupOf]
        exact hfix u (mem_fixV_zpowers_iff.mp hu)
      · intro u hu
        rw [mem_fixV_zpowers_iff]
        exact hgZ u (by rwa [Subgroup.mem_subgroupOf] at hu)
    have hCfixH : fixV (Subgroup.zpowers g) = fixV H := by
      rw [hCeq, hZc]
    have hconj : ∀ h ∈ H, ∀ x ∈ Subgroup.zpowers g,
        h * x * h⁻¹ ∈ Subgroup.zpowers g := by
      intro h hh x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hcomm : h * g = g * h := Subgroup.mem_centralizer_iff.mp hgc h hh
      have hconjg : MulAut.conj h g = g := by
        rw [MulAut.conj_apply, hcomm]
        group
      have h1 : MulAut.conj h (g ^ n) = g ^ n := by rw [map_zpow, hconjg]
      have h2 : h * g ^ n * h⁻¹ = g ^ n := by simpa [MulAut.conj_apply] using h1
      rw [h2]
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
    have hHstabD : H ≤ stabSub (commSub (⊤ : Subgroup ↥(commSub ⊤ L))
        (Subgroup.zpowers g)) := by
      intro h hh
      rw [mem_stabSub]
      intro u
      constructor
      · intro hu
        have h1 : h⁻¹ (h u) ∈
            commSub (⊤ : Subgroup ↥(commSub ⊤ L)) (Subgroup.zpowers g) :=
          commSub_top_stable151b (hconj h⁻¹ (H.inv_mem hh)) (h u) hu
        simpa using h1
      · intro hu
        exact commSub_top_stable151b (hconj h hh) u hu
    have hDtop : commSub (⊤ : Subgroup ↥(commSub ⊤ L)) (Subgroup.zpowers g) = ⊤ := by
      have hkey : commSub (⊤ : Subgroup ↥(commSub ⊤ L)) H =
          commSub (commSub (⊤ : Subgroup ↥(commSub ⊤ L)) (Subgroup.zpowers g)) H := by
        conv_lhs => rw [← hsup]
        rw [sup_comm, hCfixH]
        exact CFSG.Quasithin.commSub_sup_fixV (H := H)
          (J := commSub (⊤ : Subgroup ↥(commSub ⊤ L)) (Subgroup.zpowers g))
          (Z := fixV H) le_rfl
      have hle : commSub (commSub (⊤ : Subgroup ↥(commSub ⊤ L)) (Subgroup.zpowers g)) H ≤
          commSub (⊤ : Subgroup ↥(commSub ⊤ L)) (Subgroup.zpowers g) :=
        commSub_le_of_invariant (fun x hx w hw => (mem_stabSub.mp (hHstabD hx) w).2 hw)
      have htop : (⊤ : Subgroup ↥(commSub ⊤ L)) ≤
          commSub (⊤ : Subgroup ↥(commSub ⊤ L)) (Subgroup.zpowers g) :=
        calc (⊤ : Subgroup ↥(commSub ⊤ L))
            = commSub (⊤ : Subgroup ↥(commSub ⊤ L)) H := hcommH.symm
          _ = commSub (commSub (⊤ : Subgroup ↥(commSub ⊤ L)) (Subgroup.zpowers g)) H := hkey
          _ ≤ commSub (⊤ : Subgroup ↥(commSub ⊤ L)) (Subgroup.zpowers g) := hle
      exact top_le_iff.mp htop
    have hCbot : fixV (Subgroup.zpowers g) = ⊥ := by
      have h1 := hinf
      rw [hDtop, inf_top_eq] at h1
      exact h1
    have hZcbot : Z.subgroupOf (commSub ⊤ L) = ⊥ := hCeq ▸ hCbot
    have hZbot : Z = ⊥ := by
      have h2 := Subgroup.map_subgroupOf_eq_of_le (H := Z) (K := commSub ⊤ L)
        (inf_le_left : Z ≤ commSub ⊤ L)
      rw [hZcbot, Subgroup.map_bot] at h2
      exact h2.symm
    exact hZ hZbot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
