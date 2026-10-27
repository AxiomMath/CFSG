module

public import CFSG.Quasithin.Vol2.Asc94.TSFrame1
public import CFSG.Quasithin.Vol2.Asc94.TS39c
public import CFSG.Quasithin.Vol2.Asc94.TSModel4

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.M24S CFSG.Open

namespace L52

@[expose] def F6Model : Prop :=
  ∀ E : Subgroup Hc, E ≤ Tm → IsElemAbelian 2 E → Nat.card E = 64 → E = A1 ∨ E = A2

end L52

variable {G : Type} [Group G] {z : G} (e : ↥(Cz z) ≃* L52.Hc)

theorem range_emb : (emb e).range = Cz z := by
  rw [MonoidHom.range_eq_map]
  exact tr_top e

theorem exists_tr_eq_of_le_Cz {E : Subgroup G} (hE : E ≤ Cz z) :
    ∃ E' : Subgroup L52.Hc, tr e E' = E := by
  refine ⟨E.comap (emb e), ?_⟩
  rw [tr, Subgroup.map_comap_eq, range_emb]
  exact inf_eq_right.2 hE

theorem isElemAbelian_of_tr {X : Subgroup L52.Hc} (hX : IsElemAbelian 2 (tr e X)) :
    IsElemAbelian 2 X := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    show (a : L52.Hc) * b = b * a
    have h := congrArg Subtype.val (hX.1.is_comm.comm (⟨emb e a, emb_mem_tr e a.2⟩ : tr e X)
      ⟨emb e b, emb_mem_tr e b.2⟩)
    exact (emb_mul_comm e).1 h
  · have h := hX.2 (emb e x) (emb_mem_tr e hx)
    apply emb_injective e
    rw [map_pow, h, map_one]


@[expose] def frame2 [Finite G] (hz : orderOf z = 2) (hF6 : L52.F6Model) : Frame2 G z where
  toFrame1 := frame1 e hz
  A := tr e L52.A1
  A' := tr e L52.A2
  A_le_T := tr_mono e L52.A1_le_Tm
  A'_le_T := tr_mono e L52.A2_le_Tm
  A_normal := by
    rintro _ ⟨t', ht', rfl⟩ _ ⟨a', ha', rfl⟩
    have h := L52.A1_conj_Tm (Subgroup.inv_mem _ ht') ha'
    rw [inv_inv] at h
    have h2 := emb_mem_tr e h
    rw [emb_conj] at h2
    simpa using h2
  A'_normal := by
    rintro _ ⟨t', ht', rfl⟩ _ ⟨a', ha', rfl⟩
    have h := L52.A2_conj_Tm (Subgroup.inv_mem _ ht') ha'
    rw [inv_inv] at h
    have h2 := emb_mem_tr e h
    rw [emb_conj] at h2
    simpa using h2
  A_elem := isElemAbelian_tr e L52.isElemAbelian_A1
  A'_elem := isElemAbelian_tr e L52.isElemAbelian_A2
  card_A := by rw [card_tr, L52.card_A1]; norm_num
  card_A' := by rw [card_tr, L52.card_A2]; norm_num
  z_mem_A := by
    have h := emb_mem_tr e L52.zt_mem_A1
    rwa [emb_zt e hz] at h
  card_A_U := by
    show Nat.card ↥(tr e L52.A1 ⊓ tr e L52.U1) = 8
    rw [← tr_inf, card_tr, L52.card_A1_inf_U1]
    norm_num
  card_A'_U := by
    show Nat.card ↥(tr e L52.A2 ⊓ tr e L52.U1) = 4
    rw [← tr_inf, card_tr, L52.card_A2_inf_U1]
    norm_num
  A_max := by
    intro E hE hEA hEc
    obtain ⟨E', rfl⟩ := exists_tr_eq_of_le_Cz e (hE.trans (tr_le_Cz e _))
    have h1 : E' ≤ L52.Tm := (tr_le_iff e).1 hE
    have h2 := isElemAbelian_of_tr e hEA
    rw [card_tr] at hEc
    rcases hF6 E' h1 h2 hEc with h | h
    · left
      rw [h]
    · right
      rw [h]
  AU_max := by
    intro E hE hEC
    have hz1 : z ∈ tr e L52.A1 ⊓ tr e L52.U1 := by
      refine ⟨?_, ?_⟩
      · have h := emb_mem_tr e L52.zt_mem_A1
        rwa [emb_zt e hz] at h
      · have h := emb_mem_tr e L52.zt_mem_U1
        rwa [emb_zt e hz] at h
    have hEH : E ≤ Cz z := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 (hEC hx) z hz1).symm)
    obtain ⟨E', rfl⟩ := exists_tr_eq_of_le_Cz e hEH
    have h2 := isElemAbelian_of_tr e hE
    have h3 : E' ≤ Subgroup.centralizer ((L52.A1 ⊓ L52.U1 : Subgroup L52.Hc) : Set L52.Hc) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hd' : emb e d ∈ tr e L52.A1 ⊓ tr e L52.U1 := by
        rw [← tr_inf]
        exact emb_mem_tr e hd
      have h4 := Subgroup.mem_centralizer_iff.1 (hEC (emb_mem_tr e hx)) _ hd'
      exact (emb_mul_comm e).1 h4
    rcases L52.elemAbelian_le_A1_or_U1 h2 h3 with h | h
    · left
      exact tr_mono e h
    · right
      exact tr_mono e h

end CFSG.Quasithin.A94
