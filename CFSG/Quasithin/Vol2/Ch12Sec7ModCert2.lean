module

public import Certificates.Certificate7214

public section

namespace CFSG.Quasithin.H13.S127.Mod

theorem cert4_hyp_trans : ∀ c ∈ oVecL, ∃ g ∈ gm6, g.app c = 1 :=
  Certificates.certificate7214.1

theorem cert4_off_trans :
    ∀ c ∈ List.range 64, c ≠ 0 → c ∉ oVecL → ∀ d ∈ p1c, d ≠ 0 → ∃ g ∈ gm6, g.app c = d :=
  Certificates.certificate7214.2.1

theorem cert4_card_pt1 : (gm6.filter (presv pt1)).length = 180 :=
  Certificates.certificate7214.2.2.1

theorem cert4_card_stab1 : stab1.length = 60 :=
  Certificates.certificate7214.2.2.2.1

theorem cert4_blk_ker :
    ∀ g ∈ gm6, presv pt1 g = true → blkC g = [1, 0, 0, 1] → g = B6.id :=
  Certificates.certificate7214.2.2.2.2.1

theorem cert4_det_one : ∀ g ∈ stab1, det2 g = 1 :=
  Certificates.certificate7214.2.2.2.2.2.1

theorem cert4_irr_t :
    ∀ c ∈ List.range 64, c ∉ pt1 →
      spanHas (pt1 ++ stab1.map (·.app c)) (List.range 64) = true :=
  Certificates.certificate7214.2.2.2.2.2.2.1

theorem cert4_comm_span :
    spanHas (stab1.flatMap fun g => (List.range 64).map fun c => c ^^^ g.app c)
      (List.range 64) = true :=
  Certificates.certificate7214.2.2.2.2.2.2.2.1

theorem cert4_gen3 :
    ∀ g ∈ stab1, ∃ a ∈ stab1, ∃ b ∈ stab1, a.pow 3 = B6.id ∧ b.pow 3 = B6.id ∧
      g = a.comp b :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.1

theorem cert4_comm_all :
    ∀ g ∈ stab1, ∃ a ∈ stab1, ∃ b ∈ stab1, g = ((a.comp b).comp (inv6 a)).comp (inv6 b) :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.1

theorem cert4_inv_fix16 :
    ∀ B ∈ nm6, B.comp B = B6.id → B ≠ B6.id → fixCount B ≤ 16 :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_odd_fix8 :
    ∀ B ∈ nm6, B.pow 15 = B6.id → B ≠ B6.id → fixCount B < 8 :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_fix16_hyp :
    ∀ B ∈ nm6, B.comp B = B6.id → B ≠ B6.id → 16 ≤ fixCount B →
      ∃ c ∈ oVecL, B.app c = c :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_axis :
    ∀ B ∈ gm6, B.comp B = B6.id → B ≠ B6.id →
      ∃ g ∈ gm6, ∀ c ∈ List.range 64, (B.app c = c ↔ g.app c ∈ l2c) :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_r2_of_fix8 :
    ∀ B ∈ nm6, 8 ≤ (l2c.filter fun c => B.app c == c).length → B ∈ r2 :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_cent_semi :
    ∀ y ∈ nm6, y ∉ gm6 → y.comp y = B6.id → ∀ B ∈ nm6,
      (∀ c ∈ List.range 64, y.app c = c → B.app c = c) → B = B6.id ∨ B = y :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_semi_fix8 :
    ∀ y ∈ nm6, y ∉ gm6 → y.comp y = B6.id → fixCount y = 8 :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_semi_pt :
    ∀ y ∈ nm6, y ∉ gm6 → y.comp y = B6.id → ∀ p ∈ oPts, presv (ptOf p) y = true →
      ∃ c ∈ oVecL, y.app c = c :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_tau_norm :
    ∀ τ ∈ nm6, τ ∉ gm6 → (∀ s ∈ s0, ∃ s' ∈ s0, τ.comp s = s'.comp τ) → two6 τ = true →
      ∃ k ∈ zs6, ∃ u ∈ s0p, k.comp τ = u.comp k :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_l1s0p_closed :
    ∀ x ∈ l1s0p, ∀ y ∈ l1s0p, x.comp y ∈ l1s0p :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_l2s0p_closed :
    ∀ x ∈ l2s0p, ∀ y ∈ l2s0p, x.comp y ∈ l2s0p :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_center1 :
    ∀ B ∈ l1s0p, (∀ D ∈ l1 ++ s0p, B.comp D = D.comp B) → B = B6.id ∨ B = i1 :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_center2 :
    ∀ B ∈ l2s0p, (∀ D ∈ l2 ++ s0p, B.comp D = D.comp B) → B = B6.id ∨ B = i2 :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_classes :
    ∀ y ∈ nm6, y ∉ gm6 → y.comp y = B6.id →
      ∃ m ∈ nm6, y.comp m = m.comp i1 ∨ y.comp m = m.comp i2 :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_noncong : ∀ m ∈ nm6, i2.comp m ≠ m.comp i1 :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_i12_mem : i1 ∈ nm6 ∧ i1 ∉ gm6 ∧ i2 ∈ nm6 ∧ i2 ∉ gm6 :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_i12_prod : i1 ∈ l1s0p ∧ i2 ∈ l2s0p :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert4_pow60 : ∀ B ∈ nm6, B.pow 60 = B6.id :=
  Certificates.certificate7214.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Quasithin.H13.S127.Mod

end
