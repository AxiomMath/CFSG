module

public import CFSG.Quasithin.Background.RonanD321FiveMod
public import CFSG.Quasithin.Background.SmithD321Count

public section

namespace CFSG.Quasithin.RonanD321.Five

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Open CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem exists_five_elt (hB : D321Base M Mp T L V t) (h2 : D321Two L) (htop : orbSup T V ≠ ⊤)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hU : commSub (orbSup T V) L = V) :
    ∃ c ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)), c ≠ 1 ∧ ∃ n : ℕ, c ^ (5 ^ n) = 1 := by
  set N := Subgroup.normalizer (L : Set (MulAut W)) with hN
  have hΛG : ∀ g ∈ M ⊓ N, ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun g hg l hl =>
    (Subgroup.mem_normalizer_iff.1 hg.2 l).1 hl
  have hPG : T ⊓ N ≤ M ⊓ N := inf_le_inf_right _ hB.T_le
  have hodd : Odd ((T ⊓ N).subgroupOf (M ⊓ N)).index :=
    Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hB.sylow_T0.2.2)
  have hLG : L ≤ M ⊓ N := le_inf hB.L_le Subgroup.le_normalizer
  have hfac := exists_mul_mul_of_out_two hLG hPG hodd (out_two_of_isPSL32 h2.1 hΛG)
  have hVinv : XMod.IsInv ↥L V := fun a v hv => hB.Mp_inv_V a (hB.L_le_Mp a.2) v hv
  obtain ⟨p, hp, hp2, y, hyG, hyL, ⟨n, hyn⟩, hyp, u, hu, hyu⟩ :=
    exists_pElement_of_factorization (Γ := MulAut W) (Q := W) hΛG hPG hB.sylow_T0.2.1 hodd
      (fun g hg q hq => B15P4.map_commV_mem hg.2 q hq) (hB.V_le_commV hVt)
      (fun l hl => smul_eq_of_isInv hVinv hl) (fun s hs => map_V_of_mem_T0 hU hs.1 hs.2)
      hfac (hB.commV_le_iSup hVt)
      (fun h => hB.not_le_orbSup htop (h.trans ((le_orbSup T V).trans le_sup_left)))
  have hyNt : y ∈ Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) :=
    mem_normalizer_iff_conjAutSub.2 (hB.conj_Lt_of_mem_normalizer hyG.1 hyG.2)
  have houtt := out_two_of_isPSL32 (d321Two_conjAutSub h2 t).1
    (G := Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)))
    (fun g hg l hl => (Subgroup.mem_normalizer_iff.1 hg l).1 hl)
  have hinner := inner_of_odd_of_out_two houtt hyNt (hp.odd_of_ne_two hp2).pow hyn
  have hUfix : ∀ v ∈ commV L, ∀ g ∈ conjAutSub t L, g v = v := fun v hv g hg =>
    mem_fixV.1 (hB.commV_le_fixV hVt hv) g hg
  have hpL : ¬ p ∣ Nat.card ↥L := fun hpL =>
    hyu (hUfix u hu y (hB.mem_Lt_of_inner hp hp2 hpL hyG.1 hyL hyn hinner))
  have h168 := card_eq_168_of_isPSL32 h2.1
  have hp5 : p = 5 := by
    rcases prime_cases_of_moves hB.exp h2 (fun l hl => (hyL l hl).symm) hp hp2
        (fun v hv => hyp v hv) ⟨u, hu, hyu⟩ with h | h | ⟨h, -⟩
    · exact absurd (by rw [h168, h]; norm_num) hpL
    · exact absurd (by rw [h168, h]; norm_num) hpL
    · exact h
  subst hp5
  obtain ⟨l', hl', hconj⟩ := hinner
  set c := l'⁻¹ * y with hc
  have hcLt : ∀ m ∈ conjAutSub t L, c * m = m * c := by
    intro m hm
    have h1 := hconj m hm
    calc c * m = l'⁻¹ * (y * m * y⁻¹) * y := by rw [hc]; group
      _ = l'⁻¹ * (l' * m * l'⁻¹) * y := by rw [h1]
      _ = m * c := by rw [hc]; group
  have hcL : ∀ l ∈ L, c * l = l * c := by
    intro l hl
    have h1 := hyL l hl
    have h2' : l'⁻¹ * l = l * l'⁻¹ := by
      have h3 : l * l' = l' * l := hB.comm l hl l' hl'
      calc l'⁻¹ * l = l'⁻¹ * (l * l') * l'⁻¹ := by group
        _ = l'⁻¹ * (l' * l) * l'⁻¹ := by rw [h3]
        _ = l * l'⁻¹ := by group
    calc c * l = l'⁻¹ * (y * l) := by rw [hc]; group
      _ = l'⁻¹ * (l * y) := by rw [h1]
      _ = (l'⁻¹ * l) * y := by group
      _ = l * c := by rw [h2', hc]; group
  have hcC : c ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) := by
    refine ⟨M.mul_mem (M.inv_mem (hB.Lt_le hl')) hyG.1, Subgroup.mem_centralizer_iff.2
      fun m hm => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hB.exists_mul_of_mem_Mp hm
    rw [mul_assoc, ← hcLt b hb, ← mul_assoc, ← hcL a ha, mul_assoc]
  refine ⟨c, hcC, fun hc1 => ?_, n, ?_⟩
  ·
    have hy : y = l' := by
      have e : y = l' * c := by rw [hc]; group
      rw [e, hc1, mul_one]
    exact hyu (hUfix u hu y (hy ▸ hl'))
  · have hcomm : Commute l' c := (hcLt l' hl').symm
    have hy : y = l' * c := by rw [hc]; group
    have h1 : l' ^ (5 ^ n) * c ^ (5 ^ n) = 1 := by rw [← hcomm.mul_pow, ← hy, hyn]
    have hmemLt : c ^ (5 ^ n) ∈ conjAutSub t L := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact (conjAutSub t L).inv_mem ((conjAutSub t L).pow_mem hl' _)
    have hmem : c ^ (5 ^ n) ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) ⊓ Mp :=
      ⟨(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))).pow_mem hcC _, hB.Lt_le_Mp hmemLt⟩
    rw [hB.cent_inf_Mp] at hmem
    exact Subgroup.mem_bot.1 hmem

end CFSG.Quasithin.RonanD321.Five
