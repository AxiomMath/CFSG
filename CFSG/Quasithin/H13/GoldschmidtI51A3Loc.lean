module

public import CFSG.Quasithin.H13.GoldschmidtI51Q0
public import CFSG.Quasithin.H13.GoldschmidtI51Nb

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {Gs : Fin 3 → Subgroup G}

theorem Nbd_mul_A3 (hD : IsDSystem .A3 Gs) {n m : G} (hn : n ∈ Nbd Gs) (hm : m ∈ Nbd Gs) :
    n * m ∈ Nbd Gs := by
  obtain ⟨a, ha, s, hs, c, hc, rfl⟩ := hn
  obtain ⟨a', ha', s', hs', c', hc', rfl⟩ := hm
  have hNr : Nr Gs (c * a') := loc0A_fano hD (c * a') ((Gs 0).mul_mem hc ha')
  have h1 : (s⁻¹)⁻¹ * (c * a') * s' ∈ Nbd Gs := near_collinear hD hNr ((Gs 1).inv_mem hs) hs'
  rw [inv_inv] at h1
  have e : a * s * c * (a' * s' * c') = a * (s * (c * a') * s') * c' := by group
  rw [e]
  exact Nbd_mul_G0 hc' (G0_mul_Nbd ha h1)

theorem Nbd_univ_A3 (hD : IsDSystem .A3 Gs) (g : G) : g ∈ Nbd Gs := by
  let N : Subgroup G :=
    { carrier := Nbd Gs
      mul_mem' := fun {n m} hn hm => Nbd_mul_A3 hD hn hm
      one_mem' := G0_sub_Nbd (Gs 0).one_mem
      inv_mem' := fun {n} hn => Nbd_inv hn }
  have h0 : Gs 0 ≤ N := fun x hx => G0_sub_Nbd hx
  have h1 : Gs 1 ≤ N := fun x hx => G1_sub_Nbd hx
  have h2 : Gs 2 ≤ N := fun x hx => G2_sub_Nbd hD hx
  have : (⊤ : Subgroup G) ≤ N := by
    rw [← hD.d4gen]; exact sup_le (sup_le h0 h1) h2
  exact this (Subgroup.mem_top g)

theorem card_Omega_A3 (hD : IsDSystem .A3 Gs) : Nat.card (G ⧸ Gs 0) = 15 := by
  have hu : (Set.univ : Set (G ⧸ Gs 0)) = insert (oPt Gs) (Dlt Gs) := by
    ext p
    induction p using QuotientGroup.induction_on with | _ a => ?_
    simp only [Set.mem_univ, Set.mem_insert_iff, true_iff]
    by_cases hp : (a : G ⧸ Gs 0) = oPt Gs
    · exact Or.inl hp
    · exact Or.inr ⟨hp, col_oPt.2 (Nbd_univ_A3 hD a)⟩
  have := Set.ncard_insert_of_notMem (a := oPt Gs) (s := Dlt Gs) (by simp [Dlt])
    (Set.toFinite _)
  rw [← hu, Set.ncard_univ, ncard_Dlt_of hD (loc0A_idx01 hD)] at this
  omega

theorem Rx_le_Q0_A3 (hD : IsDSystem .A3 Gs) {g : G} (hg : g ∈ Rx Gs) : g ∈ QQ Gs 0 := by
  obtain ⟨s0, hs0, hs00⟩ := exists_s0 hD
  refine loc0A_core hD g hg.1 (fun h hh => ?_)
  have hpt : g • ((h * s0 : G) : G ⧸ Gs 0) = ((h * s0 : G) : G ⧸ Gs 0) :=
    hg.2 _ (col_oPt.2 ⟨h, hh, s0, hs0, 1, (Gs 0).one_mem, by group⟩)
  have hpt' : ((g * (h * s0) : G) : G ⧸ Gs 0) = ((h * s0 : G) : G ⧸ Gs 0) := hpt
  rw [QuotientGroup.eq] at hpt'
  have hu : h⁻¹ * g * h ∈ Gs 0 :=
    (Gs 0).mul_mem ((Gs 0).mul_mem ((Gs 0).inv_mem hh) hg.1) hh
  have hrel : s0⁻¹ * (h⁻¹ * g * h) * s0 ∈ Gs 0 := by
    have := (Gs 0).inv_mem hpt'
    have e : ((g * (h * s0))⁻¹ * (h * s0))⁻¹ = s0⁻¹ * (h⁻¹ * g * h) * s0 := by group
    rwa [e] at this
  exact ⟨hu, uniq_line hD hs0 hs00 hs0 hu hrel⟩

theorem faithful_A3 (hD : IsDSystem .A3 Gs) {g : G} (hg : ∀ x : G ⧸ Gs 0, g • x = x) :
    g = 1 := by
  let K : Subgroup G := (MulAction.toPermHom G (G ⧸ Gs 0)).ker
  have hK : K.Normal := MonoidHom.normal_ker _
  have hmemK : ∀ k : G, k ∈ K ↔ ∀ x : G ⧸ Gs 0, k • x = x := fun k => by
    rw [MonoidHom.mem_ker, Equiv.ext_iff]
    exact Iff.rfl
  have hKT : K ≤ Gs 0 ⊓ Gs 1 ⊓ Gs 2 := by
    intro k hk
    have hk' := (hmemK k).1 hk
    have hk0 : k ∈ Gs 0 := by
      have := hk' (oPt Gs)
      rw [smul_oPt', oPt, QuotientGroup.eq, mul_one] at this
      simpa using (Gs 0).inv_mem this
    exact QQ_le_TT hD 0 (Rx_le_Q0_A3 hD ⟨hk0, fun p _ => hk' p⟩)
  have h1 := hD.d4core K hK hKT
  have hgK : g ∈ K := (hmemK g).2 hg
  rw [h1] at hgK
  exact Subgroup.mem_bot.1 hgK

theorem card_Q0_ge_A3 (hD : IsDSystem .A3 Gs) : 8 ≤ Nat.card ↥(QQ Gs 0) := by
  have : Fintype (LinesO Gs) := Fintype.ofFinite _
  have h7 : Fintype.card (LinesO Gs) = 7 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]; exact loc0A_idx01 hD
  have hX := card_index_two (Kq Gs) (Kq_inj hD) (Kq_index hD)
  rw [h7] at hX
  have h1 : 1 ≤ Nat.card ↥(⨅ x, Kq Gs x) := Nat.card_pos
  nlinarith

theorem card_G_ge_A3 (hD : IsDSystem .A3 Gs) : 20160 ≤ Nat.card G := by
  have hG := Subgroup.card_eq_card_quotient_mul_card_subgroup (Gs 0)
  rw [card_Omega_A3 hD, loc0A_card hD] at hG
  have := card_Q0_ge_A3 hD
  rw [hG]
  nlinarith

end CFSG.Quasithin.H13.I51
