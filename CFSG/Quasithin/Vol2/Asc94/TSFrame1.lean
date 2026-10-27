module

public import CFSG.Quasithin.Vol2.Asc94.TSFrame
public import CFSG.Quasithin.Vol2.Asc94.TS39b
public import CFSG.Quasithin.Vol2.Asc94.TSModel9b

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.M24S CFSG.Open

variable {G : Type} [Group G] {z : G} (e : ↥(Cz z) ≃* L52.Hc)

theorem tr_Qh_eq : tr e L52.Qh = pCoreOf 2 (Cz z) := by
  rw [pCoreOf, ← CFSG.pCore_map_iso 2 e.symm, ← L52.pCore_eq_Qh, Subgroup.map_map]
  rfl

theorem tr_commutator (X Y : Subgroup L52.Hc) : tr e ⁅X, Y⁆ = ⁅tr e X, tr e Y⁆ :=
  Subgroup.map_commutator X Y (emb e)

theorem tr_zpowers_zt (hz : orderOf z = 2) : tr e (Subgroup.zpowers L52.zt) = Subgroup.zpowers z := by
  rw [tr, MonoidHom.map_zpowers, emb_zt e hz]

theorem Cz_inf_Cz_emb (t' : L52.Hc) :
    Cz z ⊓ Cz (emb e t') = tr e (Subgroup.centralizer ({t'} : Set L52.Hc)) := by
  ext x
  constructor
  · rintro ⟨hxz, hxt⟩
    obtain ⟨y, rfl⟩ := exists_emb e hxz
    refine ⟨y, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (emb_mul_comm e).1 (Subgroup.mem_centralizer_singleton_iff.1 hxt)
  · rintro ⟨y, hy, rfl⟩
    exact ⟨emb_mem_Cz e y, Subgroup.mem_centralizer_singleton_iff.2
      ((emb_mul_comm e).2 (Subgroup.mem_centralizer_singleton_iff.1 hy))⟩

@[expose] def frame1 [Finite G] (hz : orderOf z = 2) : Frame1 G z where
  toFrame0 := frame0 e hz
  U2 := tr e L52.U2
  Q := tr e L52.Qh
  TQ := emb e '' L52.TQ
  Q_eq := tr_Qh_eq e
  U2_normal := by
    have h := (frame0 (swapIso e) hz).U_normal
    rw [show (frame0 (swapIso e) hz).U = tr e L52.U2 from tr_swap_U1 e] at h
    exact h
  U2_trans := by
    have h := (frame0 (swapIso e) hz).U_trans
    rw [show (frame0 (swapIso e) hz).U = tr e L52.U2 from tr_swap_U1 e] at h
    exact h
  Q_inv := by
    rintro _ ⟨q', hq', rfl⟩ hsq hne
    have hsq' : q' * q' = 1 := by
      apply emb_injective e
      rw [map_mul, hsq, map_one]
    have hne' : q' ≠ 1 := fun h => hne (by rw [h, map_one])
    by_cases h1 : q' ∈ L52.U1
    · by_cases hzt : q' = L52.zt
      · left
        rw [hzt, emb_zt e hz]
      · right
        left
        exact ⟨emb_mem_tr e h1, fun h => hzt (emb_injective e (h.trans (emb_zt e hz).symm))⟩
    · by_cases h2 : q' ∈ L52.U2
      · by_cases hzt : q' = L52.zt
        · left
          rw [hzt, emb_zt e hz]
        · right
          right
          left
          exact ⟨emb_mem_tr e h2, fun h => hzt (emb_injective e (h.trans (emb_zt e hz).symm))⟩
      · right
        right
        right
        exact ⟨q', ⟨hq', hsq', hne', h1, h2⟩, rfl⟩
  TQ_sq := by
    rintro _ ⟨t', ⟨_, ht2, _⟩, rfl⟩
    rw [← map_mul, ht2, map_one]
  TQ_card := by
    rintro _ ⟨t', ht', rfl⟩
    rw [Cz_inf_Cz_emb, card_tr]
    exact L52.card_centralizer_TQ ht'
  TQ_der := by
    rintro _ ⟨t', ht', rfl⟩
    rw [Cz_inf_Cz_emb, ← tr_commutator, ← tr_commutator, L52.derived2_centralizer_TQ ht',
      tr_zpowers_zt e hz]

end CFSG.Quasithin.A94
