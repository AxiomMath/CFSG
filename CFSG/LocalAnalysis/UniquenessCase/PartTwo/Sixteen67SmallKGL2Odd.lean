module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGCom
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGL2Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGL2Fix
import CFSG.Quasithin.Vol2.Ch3E213MP3A
import CFSG.LocalAnalysis.ComponentClassification.Sol78FooteFCB
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L2Cent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem s1667_kgl2_sq_or_cube_mem_centralizer {Q : Type} [Group Q] {E : Subgroup Q}
    [IsKleinFour ↥E] {t : Q} (ht : t ∈ normalizer (E : Set Q)) :
    t ^ 2 ∈ centralizer (E : Set Q) ∨ t ^ 3 ∈ centralizer (E : Set Q) := by
  have key : ∀ s : Equiv.Perm (Fin 3), s ^ 2 = 1 ∨ s ^ 3 = 1 := by decide
  let ψ : normalizer (E : Set Q) →* MulAut ↥E := E.normalizerMonoidHom
  let t' : normalizer (E : Set Q) := ⟨t, ht⟩
  let c := CFSG.GorensteinWalter.kleinFourAutSymmetricThreeEquiv ↥E
  have hmem : ∀ k : ℕ, ψ (t' ^ k) = 1 → t ^ k ∈ centralizer (E : Set Q) := by
    intro k hk
    have h1 : t' ^ k ∈ ψ.ker := hk
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h1
    exact h1
  rcases key (c (ψ t')) with h2 | h3
  · left
    refine hmem 2 ?_
    rw [map_pow]
    exact (map_eq_one_iff c c.injective).mp (by rw [map_pow]; exact h2)
  · right
    refine hmem 3 ?_
    rw [map_pow]
    exact (map_eq_one_iff c c.injective).mp (by rw [map_pow]; exact h3)

theorem s1667_kgl2_mul_self_eq_one {Q : Type} [Group Q] {E : Subgroup Q} (hE : IsElemAbelian 2 E)
    (w : ↥E) : w * w = 1 :=
  Subtype.ext (by simpa [sq] using hE.2 (w : Q) w.2)

theorem s1667_kgl2_isKleinFour_subgroupOf {Q : Type} [Group Q] [Finite Q] {J E : Subgroup Q}
    (hEJ : E ≤ J) (hE : IsElemAbelian 2 E) (hE4 : Nat.card E = 4) :
    IsKleinFour ↥(E.subgroupOf J) := by
  refine CFSG.Quasithin.Ch3E213M.P3.isKleinFour_of_card ?_ fun w => ?_
  · rw [← hE4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
  · exact Subtype.ext (Subtype.ext (by simpa [sq] using hE.2 ((w : ↥J) : Q) w.2))

theorem k67CaseIIIAt_psl2_odd {Q : Type}
    [Group Q] [Finite Q] (J : Subgroup Q) (hJ : J.Normal)
    (hC : centralizer (J : Set Q) = ⊥) {p f : ℕ} (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h : LieModel ↥J .PSL 2 p f) : K67CaseIIIAt Q J := by
  haveI := hJ
  intro x hxJ hx3 E hE hE4 hEJ hEx W hW hW1 hWx hWE hN
  obtain ⟨hp, hf1, -, -, F, hF, hFin, hcard, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data h
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    CFSG.ComponentClassification.AutL2Facts.isOddPrimePower_of hp hp2 hf1 hcard
  let x' : ↥J := ⟨x, hxJ⟩
  have hx'3 : orderOf x' = 3 := (Subgroup.orderOf_coe x').symm.trans hx3
  obtain ⟨hcyc, hord⟩ := s1667_kgl2_centralizer_lieModel h hp2 hp3 hx'3
  obtain ⟨φ⟩ := s1667_kg_inf_centralizer_equiv J hxJ
  have hcycT : IsCyclic ↥(J ⊓ centralizer ({x} : Set Q)) := φ.isCyclic.mpr hcyc
  have hcardT : Nat.card ↥(J ⊓ centralizer ({x} : Set Q)) =
      Nat.card ↥(centralizer ({x'} : Set ↥J)) := Nat.card_congr φ.toEquiv
  haveI hEK : IsKleinFour ↥E := CFSG.Quasithin.Ch3E213M.P3.isKleinFour_of_card hE4
    (s1667_kgl2_mul_self_eq_one hE)
  have hEJK : IsKleinFour ↥(E.subgroupOf J) := s1667_kgl2_isKleinFour_subgroupOf hEJ hE hE4
  have hTn : ∀ t ∈ J ⊓ centralizer ({x} : Set Q), t ∈ normalizer (E : Set Q) := fun t ht =>
    (hN t (s1667_kg_mem_normalizer_zpowers_of_mem_centralizer (Subgroup.mem_inf.mp ht).2)).1
  have key : ∀ t ∈ J ⊓ centralizer ({x} : Set Q), t ^ 2 = 1 ∨ t ^ 3 = 1 := by
    intro t ht
    have htJ : t ∈ J := (Subgroup.mem_inf.mp ht).1
    have htx : t ∈ centralizer ({x} : Set Q) := (Subgroup.mem_inf.mp ht).2
    have hcen : ∀ k : ℕ, t ^ k ∈ centralizer (E : Set Q) → t ^ k = 1 := by
      intro k hk
      have hkJ : t ^ k ∈ J := J.pow_mem htJ k
      have hkx : t ^ k ∈ centralizer ({x} : Set Q) := (centralizer ({x} : Set Q)).pow_mem htx k
      have hmem : (⟨t ^ k, hkJ⟩ : ↥J) ∈ E.subgroupOf J :=
        CFSG.ComponentClassification.Sol78.mem_of_centralizes_kleinFour_psl2 hodd e hEJK
          (a := ⟨t ^ k, hkJ⟩) fun w hw => Subtype.ext
            ((Subgroup.mem_centralizer_iff.mp hk) (w : Q) (Subgroup.mem_subgroupOf.mp hw)).symm
      have hkE : t ^ k ∈ E := Subgroup.mem_subgroupOf.mp hmem
      have hkEx : t ^ k ∈ E ⊓ centralizer ({x} : Set Q) := ⟨hkE, hkx⟩
      rw [hEx, Subgroup.mem_bot] at hkEx
      exact hkEx
    rcases s1667_kgl2_sq_or_cube_mem_centralizer (hTn t ht) with h2 | h3
    · exact Or.inl (hcen 2 h2)
    · exact Or.inr (hcen 3 h3)
  obtain ⟨g, hgT, hgen⟩ := s1667_kg_exists_generator hcycT
  have hxT : x ∈ J ⊓ centralizer ({x} : Set Q) :=
    ⟨hxJ, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hzT : zpowers g = J ⊓ centralizer ({x} : Set Q) :=
    le_antisymm (Subgroup.zpowers_le.mpr hgT) fun t ht => hgen t ht
  have hcard3 : Nat.card ↥(J ⊓ centralizer ({x} : Set Q)) = 3 := by
    have h3dvd : 3 ∣ Nat.card ↥(J ⊓ centralizer ({x} : Set Q)) := by
      have := Subgroup.orderOf_dvd_natCard _ hxT
      rwa [hx3] at this
    rw [← hzT, Nat.card_zpowers] at h3dvd ⊢
    rcases key g hgT with hg2 | hg3
    · exfalso
      have h2 := orderOf_dvd_of_pow_eq_one hg2
      have := Nat.le_of_dvd (by norm_num) (h3dvd.trans h2)
      omega
    · exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hg3) h3dvd
  have h57 : p ^ f = 5 ∨ p ^ f = 7 := by
    rw [hcard3] at hcardT
    omega
  have hFp : (Nat.card F).Prime ∧ Nat.card F ≠ 2 := by
    rw [hcard]
    rcases h57 with h5 | h7
    · rw [h5]
      exact ⟨by norm_num, by norm_num⟩
    · rw [h7]
      exact ⟨by norm_num, by norm_num⟩
  let Θ : Q →* CFSG.GorensteinWalter.PGammaL2 F :=
    (CFSG.ComponentClassification.AutL2Facts.autEquiv e).toMonoidHom.comp
      (MulAut.conjNormal : Q →* MulAut ↥J)
  have hΘ : Function.Injective Θ :=
    (CFSG.ComponentClassification.AutL2Facts.autEquiv e).injective.comp
      (s1667_kg_conjNormal_injective J hC)
  have hE'4 : Nat.card (E.map Θ) = 4 := by
    rw [Subgroup.card_map_of_injective hΘ]
    exact hE4
  have hE'2 : ∀ w ∈ E.map Θ, w * w = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have haa : a * a = 1 := by simpa [sq] using hE.2 a ha
    rw [haa, map_one]
  have hC' := CFSG.Quasithin.Ch3E213M.P3.centralizer_eq_self (p := Nat.card F) hFp.1 hFp.2 rfl
    hE'4 hE'2
  have hWE' : W ≤ E := by
    intro w hw
    have hmem : Θ w ∈ centralizer ((E.map Θ : Subgroup _) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp (hWE hw)) a ha]
    rw [hC'] at hmem
    obtain ⟨a, ha, haw⟩ := hmem
    exact (hΘ haw) ▸ ha
  apply hW1
  rw [eq_bot_iff]
  intro w hw
  have hwE : w ∈ E ⊓ centralizer ({x} : Set Q) := ⟨hWE' hw, hWx hw⟩
  rw [hEx] at hwE
  exact hwE

theorem s1667_kgl2_numerics {p f s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hs : s ^ 2 = p ^ f) (hs5 : s ≤ 5) : p = 5 ∧ f = 2 := by
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h2 := hp.two_le
    have h234 : p = 2 ∨ p = 3 ∨ p = 4 := by omega
    rcases h234 with rfl | rfl | rfl
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hf2 : f ≤ 2 := by
    by_contra hlt
    have h3 : 3 ≤ f := by omega
    have h1 : p ^ 3 ≤ p ^ f := Nat.pow_le_pow_right (by omega) h3
    have h125 : 5 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp5 3
    have h25 : s ^ 2 ≤ 5 ^ 2 := Nat.pow_le_pow_left hs5 2
    omega
  have hf12 : f = 1 ∨ f = 2 := by omega
  rcases hf12 with rfl | rfl
  · exfalso
    rw [pow_one] at hs
    rw [← hs] at hp
    interval_cases s <;> norm_num at hp
  · rw [pow_two, pow_two] at hs
    have hps : p = s := (Nat.mul_self_inj.mp hs.symm)
    exact ⟨by omega, rfl⟩

theorem k67BPrimeOneAt_psl2_odd {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q) (hJ : J.Normal)
    (hC : centralizer (J : Set Q) = ⊥) {p f : ℕ} (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h : LieModel ↥J .PSL 2 p f) : K67BPrimeOneAt Q J := by
  haveI := hJ
  intro x hxJ hx3 A hA hAx hAn h4
  obtain ⟨hp, hf1, -, -, F, hF, hFin, hcard, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data h
  have hchar : ringChar F = p := s1667_kgl2_ringChar_eq hp hcard
  have hK2 : ringChar F ≠ 2 := hchar ▸ hp2
  have hK3 : ringChar F ≠ 3 := hchar ▸ hp3
  let x' : ↥J := ⟨x, hxJ⟩
  have hx'3 : orderOf x' = 3 := (Subgroup.orderOf_coe x').symm.trans hx3
  obtain ⟨hcyc, hord⟩ := s1667_kgl2_centralizer_lieModel h hp2 hp3 hx'3
  obtain ⟨φ⟩ := s1667_kg_inf_centralizer_equiv J hxJ
  have hcycT : IsCyclic ↥(J ⊓ centralizer ({x} : Set Q)) := φ.isCyclic.mpr hcyc
  have hcardT : Nat.card ↥(J ⊓ centralizer ({x} : Set Q)) =
      Nat.card ↥(centralizer ({x'} : Set ↥J)) := Nat.card_congr φ.toEquiv
  obtain ⟨g, hgT, hgen⟩ := s1667_kg_exists_generator hcycT
  have hgJ : g ∈ J := (Subgroup.mem_inf.mp hgT).1
  have hgx : g ∈ centralizer ({x} : Set Q) := (Subgroup.mem_inf.mp hgT).2
  have hzT : zpowers g = J ⊓ centralizer ({x} : Set Q) :=
    le_antisymm (Subgroup.zpowers_le.mpr hgT) fun t ht => hgen t ht
  have hordg : 2 * orderOf g = p ^ f - 1 ∨ 2 * orderOf g = p ^ f + 1 := by
    rw [← Nat.card_zpowers, hzT, hcardT]
    exact hord
  let Θ : Q →* MulAut (CFSG.GorensteinWalter.PSL2 F) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : Q →* MulAut ↥J)
  have hΘ : Function.Injective Θ :=
    (MulAut.congr e).injective.comp (s1667_kg_conjNormal_injective J hC)
  let E : Subgroup (MulAut (CFSG.GorensteinWalter.PSL2 F)) := A.map Θ
  have hE2 : ∀ α ∈ E, α * α = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have haa : a * a = 1 := by simpa [sq] using hA.2 a ha
    rw [haa, map_one]
  have hEx : ∀ α ∈ E, α (e x') = e x' := by
    rintro _ ⟨a, ha, rfl⟩
    have hax : a * x = x * a := Subgroup.mem_centralizer_singleton_iff.mp (hAx ha)
    have h1 : (MulAut.conjNormal a : MulAut ↥J) x' = x' := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply a x']
      show a * x * a⁻¹ = x
      rw [hax]
      group
    have h2 : Θ a (e x') = e ((MulAut.conjNormal a : MulAut ↥J) x') := by
      simp [Θ, MulAut.congr_apply]
    rw [h2, h1]
  have hx3' : orderOf (e x') = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact hx'3
  obtain ⟨hcardE, hE4'⟩ :=
    CFSG.RankThree.PartTwo.Sec20.card_le_four_of_forall_apply_eq hK2 hK3 hx3' E hE2 hEx
  have hAE : Nat.card E = Nat.card A := Subgroup.card_map_of_injective hΘ
  have hE4 : Nat.card E = 4 := by omega
  obtain ⟨⟨α, hαE, hα1, y, hαy⟩, -⟩ := hE4' hE4
  obtain ⟨β, hβE, hβ⟩ := s1667_kgl2_exists_fieldPart_ne_one hK2 hK3 hx3' E hE2 hEx hE4
  obtain ⟨b, hbA, rfl⟩ := hβE
  let u : MulAut ↥J := MulAut.conjNormal b
  have hb2 : b ^ 2 = 1 := hA.2 b hbA
  have hu2 : u ^ 2 = 1 := by
    have hpow : (MulAut.conjNormal (b ^ 2) : MulAut ↥J) = (MulAut.conjNormal b : MulAut ↥J) ^ 2 :=
      map_pow _ _ _
    rw [← hpow, hb2, map_one]
  have hu1 : u ≠ 1 := by
    intro hu
    apply hβ
    have : Θ b = 1 := by
      change MulAut.congr e u = 1
      rw [hu, map_one]
    rw [this, map_one]
  have huord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have hfield : CFSG.Quasithin.autFieldPart F (MulAut.congr e u) ≠ 1 := hβ
  have hc : g ^ 2 * b = b * g ^ 2 :=
    s1667_kg_sq_comm_of_cyclic J hgJ hgx (fun t ht => hgen t ht) hA hAx (hAn g hgT) hbA
  let z : ↥J := ⟨g ^ 2, J.pow_mem hgJ 2⟩
  have huz : u z = z := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply b z]
    show b * g ^ 2 * b⁻¹ = g ^ 2
    rw [← hc]
    exact mul_inv_cancel_right (g ^ 2) b
  obtain ⟨s, hs, hle⟩ := s1667_kgl2_fixed_orderOf_le e huord hfield huz
  have hzord : orderOf z = orderOf (g ^ 2) := (Subgroup.orderOf_coe z).symm
  rw [hzord, orderOf_pow' g (by norm_num : (2 : ℕ) ≠ 0)] at hle
  have hdpos : 0 < Nat.gcd (orderOf g) 2 := Nat.gcd_pos_of_pos_right _ (by norm_num)
  have hd2 : Nat.gcd (orderOf g) 2 ≤ 2 := Nat.gcd_le_right _ (by norm_num)
  have hn : orderOf g ≤ 2 * (s + 1) :=
    calc orderOf g = Nat.gcd (orderOf g) 2 * (orderOf g / Nat.gcd (orderOf g) 2) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
      _ ≤ 2 * (s + 1) := Nat.mul_le_mul hd2 hle
  have hq : s ^ 2 = p ^ f := hs.trans hcard
  have hnpos : 0 < orderOf g := orderOf_pos g
  have h1 : s ^ 2 ≤ 4 * s + 5 := by omega
  have hs5 : s ≤ 5 := by nlinarith
  obtain ⟨rfl, rfl⟩ := s1667_kgl2_numerics hp hp2 hp3 hf1 hq hs5
  refine ⟨h, ?_⟩
  obtain ⟨a, haA, rfl⟩ := hαE
  have ha1 : a ≠ 1 := fun h1 => hα1 (by rw [h1, map_one])
  have hconj : (MulAut.conjNormal a : MulAut ↥J) = MulAut.conj (e.symm y) := by
    refine MulEquiv.ext fun w => e.injective ?_
    have h1 : Θ a (e w) = MulAut.conj y (e w) := by rw [hαy]
    have h2 : Θ a (e w) = e ((MulAut.conjNormal a : MulAut ↥J) w) := by
      simp [Θ, MulAut.congr_apply]
    rw [h2, MulAut.conj_apply] at h1
    rw [h1]
    simp [MulAut.conj_apply]
  have haJ : a ∈ J :=
    (s1667_kg_mem_iff_conjNormal_mem_range J hC a).mpr ⟨e.symm y, hconj.symm⟩
  intro hbot
  have hmem : a ∈ A ⊓ J := ⟨haA, haJ⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact ha1 hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
