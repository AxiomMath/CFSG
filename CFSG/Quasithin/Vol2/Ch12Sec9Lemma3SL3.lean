module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3SL3Lift
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3Dyn
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3SL3Mat

public section

namespace CFSG.Quasithin.H13

namespace L1293S

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

variable {F : Type} [Field F]

theorem det_of_mem_statedSL {A : GL (Fin 3) F} (hA : A ∈ StatedSL 3 F) :
    (A : Matrix (Fin 3) (Fin 3) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hA

theorem scalars_data {H : Subgroup (GL (Fin 3) F)}
    (hH : ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) F).det = 1) :
    (∀ z ∈ (StatedScalars (Fin 3) F).subgroupOf H, ∀ h : ↥H, z * h = h * z) ∧
      ∀ z ∈ (StatedScalars (Fin 3) F).subgroupOf H, z ^ 3 = 1 := by
  refine ⟨fun z hz h => ?_, fun z hz => ?_⟩
  · have hzc : (z : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact Subgroup.mem_subgroupOf.1 hz
    exact Subtype.ext (Subgroup.mem_center_iff.1 hzc (h : GL (Fin 3) F)).symm
  · obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hz
    have hmat : ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (c : F) • 1 := by
      rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]
    have hdet := hH _ z.2
    rw [hmat, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at hdet
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hmat, smul_pow, one_pow, hdet, one_smul]
    rfl

theorem two_pow_dvd_card_proj [Finite F] {H : Subgroup (GL (Fin 3) F)}
    (hH : ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) F).det = 1) {j : ℕ} (h : 2 ^ j ∣ Nat.card H) :
    2 ^ j ∣ Nat.card (StatedProj H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (StatedScalars (Fin 3) F).subgroupOf H with hN
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hodd : ¬ 2 ∣ Nat.card N := by
    intro h2
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 h2
    have h3 : z ^ 3 = 1 := Subtype.ext ((scalars_data hH).2 z z.2)
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hz] at this
    norm_num at this
  rw [hc] at h
  exact (Nat.Coprime.pow_left j
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)).dvd_of_dvd_mul_right h

theorem isSL2_map {X M : Type} [Group X] [Group M] {B K : Subgroup X} (hBK : B ≤ K)
    (e : ↥K ≃* M) (hB : IsSL2 7 ↥B) : IsSL2 7 ↥((B.subgroupOf K).map e.toMonoidHom) :=
  IsSL2.of_mulEquiv (((Subgroup.subgroupOfEquivOfLe hBK).symm).trans
    ((B.subgroupOf K).equivMapOfInjective e.toMonoidHom e.injective)) hB

theorem card_centralizer_dvd_six [Finite F] (hF : Nat.card F = 7) {H : Subgroup (GL (Fin 3) F)}
    (hH : ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) F).det = 1) :
    (∀ B' : Subgroup ↥H, IsSL2 7 ↥B' →
      Nat.card ↥(Subgroup.centralizer (B' : Set ↥H)) ∣ 6) ∧
    ∀ B' : Subgroup (StatedProj H), IsSL2 7 ↥B' →
      Nat.card ↥(Subgroup.centralizer (B' : Set (StatedProj H))) ∣ 6 := by
  have : CharP F 7 := charP_seven (e := 1) (by rw [hF, pow_one])
  have h2 := two_ne_zero_of_charP (F := F)
  have h6 : Nat.card F - 1 = 6 := by rw [hF]
  refine ⟨fun B' hB' => ?_, fun B' hB' => ?_⟩
  · obtain ⟨hperf, -, ⟨z, hzB, hz1, hzz, hzc⟩, -⟩ := sl2_seven_data hB'
    exact h6 ▸ card_centralizer_dvd h2 hH hperf hzB hz1 hzz hzc
  · obtain ⟨hperf, -, ⟨w, hwB, hw1, hww, hwc⟩, -⟩ := sl2_seven_data hB'
    obtain ⟨hZc, hZ3⟩ := scalars_data hH
    obtain ⟨B₀, hB₀, ⟨z, hzB, hz1, hzz, hzc⟩, hdvd⟩ :=
      exists_lift hZc hZ3 hperf hwB hw1 hww hwc
    exact hdvd.trans (h6 ▸ card_centralizer_dvd h2 hH hB₀ hzB hz1 hzz hzc)

theorem card_centralizer_le_eight' [Finite F] (hF : Nat.card F = 7 ^ 2)
    {H : Subgroup (GL (Fin 3) F)} (hSU : H ≤ StatedSU 3 7 F) :
    (∀ B' : Subgroup ↥H, IsSL2 7 ↥B' →
      Nat.card ↥(Subgroup.centralizer (B' : Set ↥H)) ≤ 8) ∧
    ∀ B' : Subgroup (StatedProj H), IsSL2 7 ↥B' →
      Nat.card ↥(Subgroup.centralizer (B' : Set (StatedProj H))) ≤ 8 := by
  have : CharP F 7 := charP_seven hF
  have h2 := two_ne_zero_of_charP (F := F)
  have hH : ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) F).det = 1 := fun g hg =>
    (det_herm_of_mem (hSU hg)).1
  refine ⟨fun B' hB' => ?_, fun B' hB' => ?_⟩
  · obtain ⟨hperf, -, ⟨z, hzB, hz1, hzz, hzc⟩, -⟩ := sl2_seven_data hB'
    exact card_centralizer_le_eight h2 hperf hzB hz1 hzz hzc hSU
  · obtain ⟨hperf, -, ⟨w, hwB, hw1, hww, hwc⟩, -⟩ := sl2_seven_data hB'
    obtain ⟨hZc, hZ3⟩ := scalars_data hH
    obtain ⟨B₀, hB₀, ⟨z, hzB, hz1, hzz, hzc⟩, hdvd⟩ :=
      exists_lift hZc hZ3 hperf hwB hw1 hww hwc
    exact (Nat.le_of_dvd Nat.card_pos hdvd).trans
      (card_centralizer_le_eight h2 hB₀ hzB hz1 hzz hzc hSU)

end L1293S

open L1293S CFSG.Assembly.LowTwoRank in
theorem dynkinFact1293SL3_holds : DynkinFact1293SL3 := by
  intro X _ _ B K S hBK hB hK hS _
  by_contra hcon
  have hall : ∀ s ∈ S, ¬ KbarInducesOuter B s := fun s hs h => hcon ⟨s, hs, h⟩
  have hdvd := card_sylow_dvd hBK hB hS hall
  set c := Nat.card ↥(K ⊓ Subgroup.centralizer (B : Set X)) with hc
  have hcpos : 0 < c := Nat.card_pos
  have key : (2 ^ 5 ∣ Nat.card K ∧ c ∣ 6) ∨ (2 ^ 7 ∣ Nat.card K ∧ c ≤ 8) := by
    obtain ⟨s, hK⟩ := hK
    cases s with
    | true =>
      rcases hK with ⟨-, F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
      ·
        have hF' : Nat.card F = 7 := by rw [hF, pow_one]
        have hH := fun g (hg : g ∈ StatedSL 3 F) => det_of_mem_statedSL hg
        refine Or.inl ⟨?_, ?_⟩
        · rw [Nat.card_congr e.toEquiv]
          refine two_pow_dvd_card_proj hH ?_
          rw [CFSG.SectionRank.OddCover.card_statedSL_three, hF']
          norm_num
        · rw [hc, card_centralizer_eq hBK e]
          exact (card_centralizer_dvd_six hF' hH).2 _ (isSL2_map hBK e hB)
      ·
        have hH := fun g (hg : g ∈ StatedSL 3 F) => det_of_mem_statedSL hg
        refine Or.inl ⟨?_, ?_⟩
        · rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three, hF]
          norm_num
        · rw [hc, card_centralizer_eq hBK e]
          exact (card_centralizer_dvd_six hF hH).1 _ (isSL2_map hBK e hB)
    | false =>
      rcases hK with ⟨-, F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
      ·
        have hF' : Nat.card F = 7 ^ 2 := by rw [hF, pow_one]
        have : CharP F 7 := charP_seven hF'
        have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
        have hSU : StatedSU 3 (7 ^ 1) F ≤ StatedSU 3 7 F := by rw [pow_one]
        have hH : ∀ g ∈ StatedSU 3 (7 ^ 1) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 :=
          fun g hg => (det_herm_of_mem (hSU hg)).1
        refine Or.inr ⟨?_, ?_⟩
        · rw [Nat.card_congr e.toEquiv]
          refine two_pow_dvd_card_proj hH ?_
          rw [CFSG.SectionRank.OddCover.card_statedSU_three (p := 7) (f := 1) hF]
          norm_num
        · rw [hc, card_centralizer_eq hBK e]
          exact (card_centralizer_le_eight' hF' hSU).2 _ (isSL2_map hBK e hB)
      ·
        have : CharP F 7 := charP_seven hF
        have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
        refine Or.inr ⟨?_, ?_⟩
        · have h := CFSG.SectionRank.OddCover.card_statedSU_three (p := 7) (f := 1)
            (K := F) (by rw [hF, pow_one])
          rw [pow_one] at h
          rw [Nat.card_congr e.toEquiv, h]
          norm_num
        · rw [hc, card_centralizer_eq hBK e]
          exact (card_centralizer_le_eight' hF le_rfl).1 _ (isSL2_map hBK e hB)
  rcases key with ⟨hK2, hc6⟩ | ⟨hK2, hc8⟩
  · have h32 := (two_pow_dvd_card hS hK2).trans hdvd
    have h4 : 4 ∣ c := by omega
    have := h4.trans hc6
    norm_num at this
  · have h128 := (two_pow_dvd_card hS hK2).trans hdvd
    have h16 : 16 ∣ c := by omega
    have := Nat.le_of_dvd hcpos h16
    omega

end CFSG.Quasithin.H13
