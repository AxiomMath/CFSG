module

public import CFSG.Quasithin.Vol2.Asc94.TSSetting
public import CFSG.Quasithin.Vol2.Asc94.TSModel2
public import CFSG.Quasithin.Vol2.Asc94.TSModel1b
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Sporadic.Schreier.J4SSylow

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.M24S CFSG.Open

variable {G : Type} [Group G]

structure Frame0 (G : Type) [Group G] (z : G) where
  U : Subgroup G
  T : Subgroup G
  ord : orderOf z = 2
  z_mem_U : z ∈ U
  U_le_T : U ≤ T
  T_le_H : T ≤ Cz z
  card_H : Nat.card (Cz z) = 21504
  card_T : Nat.card T = 1024
  center_T : ∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x = 1 ∨ x = z
  U_elem : IsElemAbelian 2 U
  card_U : Nat.card U = 16
  U_normal : ∀ h ∈ Cz z, ∀ u ∈ U, h⁻¹ * u * h ∈ U
  U_cent : ∀ x ∈ Cz z, (∀ u ∈ U, x * u = u * x) → x ∈ U
  U_trans : ∀ x ∈ U, x ≠ 1 → x ≠ z → ∀ y ∈ U, y ≠ 1 → y ≠ z → ∃ h ∈ Cz z, y = h⁻¹ * x * h
  U_split : ∃ K : Subgroup G, K ≤ Cz z ∧ U ⊓ K = ⊥ ∧ U ⊔ K = Cz z

variable {z : G} (e : ↥(Cz z) ≃* L52.Hc)

theorem isElemAbelian_tr {X : Subgroup L52.Hc} (hX : IsElemAbelian 2 X) : IsElemAbelian 2 (tr e X) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [← ha, ← hb, emb_mul_comm]
    exact congrArg Subtype.val (hX.1.is_comm.comm (⟨a', ha'⟩ : X) ⟨b', hb'⟩)
  · obtain ⟨x', hx', rfl⟩ := hx
    rw [← map_pow]
    have := hX.2 x' hx'
    rw [this, map_one]

@[expose] def frame0 (hz : orderOf z = 2) : Frame0 G z where
  U := tr e L52.U1
  T := tr e L52.Tm
  ord := hz
  z_mem_U := by
    have h := emb_mem_tr e L52.zt_mem_U1
    rwa [emb_zt e hz] at h
  U_le_T := tr_mono e L52.U1_le_Tm
  T_le_H := tr_le_Cz e _
  card_H := by
    rw [Nat.card_congr e.toEquiv]
    exact L52.card_Hc
  card_T := by
    rw [card_tr, L52.card_Tm]
    norm_num
  center_T := by
    intro x hx hc
    obtain ⟨x', hx', rfl⟩ := hx
    have h1 : ∀ y' ∈ L52.Tm, x' * y' = y' * x' := fun y' hy' =>
      (emb_mul_comm e).1 (hc _ (emb_mem_tr e hy'))
    rcases L52.center_Tm hx' h1 with h | h
    · left
      rw [h, map_one]
    · right
      rw [h, emb_zt e hz]
  U_elem := isElemAbelian_tr e L52.isElemAbelian_U1
  card_U := by
    rw [card_tr, L52.card_U1]
  U_normal := by
    intro h hh u hu
    obtain ⟨h', rfl⟩ := exists_emb e hh
    obtain ⟨u', hu', rfl⟩ := hu
    have h1 := L52.U1_normal_conj h'⁻¹ hu'
    rw [inv_inv] at h1
    have h2 := emb_mem_tr e h1
    rw [emb_conj] at h2
    exact h2
  U_cent := by
    intro x hx hc
    obtain ⟨x', rfl⟩ := exists_emb e hx
    have h1 : x' ∈ Subgroup.centralizer (L52.U1 : Set L52.Hc) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact ((emb_mul_comm e).1 (hc _ (emb_mem_tr e hu))).symm
    rw [L52.centralizer_U1] at h1
    exact emb_mem_tr e h1
  U_trans := by
    intro x hx hx1 hxz y hy hy1 hyz
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hx1' : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hy1' : y' ≠ 1 := fun h => hy1 (by rw [h, map_one])
    have hxz' : x' ≠ L52.zt := fun h => hxz (by rw [h, emb_zt e hz])
    have hyz' : y' ≠ L52.zt := fun h => hyz (by rw [h, emb_zt e hz])
    obtain ⟨g, hg⟩ := L52.U1_trans hx' hx1' hxz' hy' hy1' hyz'
    refine ⟨emb e g, emb_mem_Cz e g, ?_⟩
    rw [hg, emb_conj]
  U_split := by
    refine ⟨tr e L52.K1, tr_le_Cz e _, ?_, ?_⟩
    · rw [inf_comm, ← tr_inf, L52.K1_inf_U1, tr_bot]
    · rw [sup_comm, ← tr_sup, L52.K1_sup_U1, tr_top]

@[expose] def swapIso : ↥(Cz z) ≃* L52.Hc := e.trans L52.sigma

theorem emb_swap (y : L52.Hc) : emb (swapIso e) y = emb e (L52.sigma y) := by
  simp [emb, swapIso, L52.sigma_symm]

theorem tr_swap (X : Subgroup L52.Hc) : tr (swapIso e) X = tr e (X.map L52.sigmaHom) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨L52.sigma y, ⟨y, hy, rfl⟩, (emb_swap e y).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, emb_swap e y⟩

theorem tr_swap_U1 : tr (swapIso e) L52.U1 = tr e L52.U2 := by
  rw [tr_swap, L52.map_sigma_U1]

theorem tr_swap_U2 : tr (swapIso e) L52.U2 = tr e L52.U1 := by
  rw [tr_swap, L52.map_sigma_U2]

theorem tr_swap_A1 : tr (swapIso e) L52.A1 = tr e L52.A2 := by
  rw [tr_swap, L52.map_sigma_A1]

theorem Setting.swap [Finite G] (h : Setting G z e) : Setting G z (swapIso e) := ⟨h.ord, h.notWC⟩

end CFSG.Quasithin.A94
