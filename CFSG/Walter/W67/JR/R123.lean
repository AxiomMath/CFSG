module

public import CFSG.Walter.W67.JR.Ree
public import CFSG.Walter.W67.JR.Basic
public import CFSG.Walter.ReeOrder.WardLocal.Two
public import CFSG.Walter.ReeOrder.WardLocal.Four
public import CFSG.Walter.W67.Prop24
public import CFSG.Walter.W67.Lemma22

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise
open JRBasic

namespace JRGroup

variable {L : Type} [Group L] [Finite L] (h : JRGroup L)

omit [Finite L] in
theorem card_normalizer_of_index {S C : Subgroup L}
    (hidx : (C.subgroupOf (Subgroup.normalizer (S : Set L))).index = 21)
    (hCN : C ≤ Subgroup.normalizer (S : Set L)) :
    Nat.card (Subgroup.normalizer (S : Set L)) = 21 * Nat.card C := by
  have h1 := Subgroup.card_mul_index (C.subgroupOf (Subgroup.normalizer (S : Set L)))
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv] at h1
  omega

theorem r2_of_five_lt
    (hq : 5 < h.q) : h.R2 := by
  have hl := JT.lemma_2_1 (h.toJTHyp hq) h.p_ne_two
  refine ⟨fun S => ⟨hl.2.2.2.1 S, ?_⟩, hl.2.2.1⟩
  rw [card_normalizer_of_index (hl.2.2.2.2.1 S).1 Subgroup.le_normalizer, (hl.2.1 S).2]

theorem r1_of_five_lt
    (hJT : JTThreeHyp) (hq : 5 < h.q) : h.R1 := by
  obtain ⟨hfodd, -⟩ := h.odd_f hJT hq
  have hsimple : IsSimpleGroup L := JT.lemma_3_1 (h.toJTHyp hq) h.p_ne_two
  have hcard : Nat.card L = h.q ^ 3 * (h.q ^ 3 + 1) * (h.q - 1) :=
    (Ward.ward_order (h.toReeTypeHyp hJT hq)).2
  have hnsolv : ¬ Group.IsSolvable L := by
    intro hs
    have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hs
    obtain ⟨S⟩ : Nonempty (Sylow 2 L) := inferInstance
    have hl := JT.lemma_2_1 (h.toJTHyp hq) h.p_ne_two
    have hC := hl.2.2.2.1 S
    have htop : Subgroup.centralizer ((S : Subgroup L) : Set L) = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_centralizer_iff.mpr fun y _ => hcomm y x
    rw [htop] at hC
    have h8 := (hl.2.1 S).2
    rw [← hC, Subgroup.card_top, hcard] at h8
    have h7 : 7 ≤ h.q := by
      obtain ⟨k, hk⟩ := h.odd_q
      omega
    have h343 : 343 ≤ h.q ^ 3 := by
      calc 343 = 7 ^ 3 := by norm_num
        _ ≤ h.q ^ 3 := Nat.pow_le_pow_left h7 3
    have hle : h.q ^ 3 ≤ h.q ^ 3 * (h.q ^ 3 + 1) * (h.q - 1) := by
      calc h.q ^ 3 ≤ h.q ^ 3 * (h.q ^ 3 + 1) := Nat.le_mul_of_pos_right _ (by omega)
        _ ≤ h.q ^ 3 * (h.q ^ 3 + 1) * (h.q - 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  exact ⟨⟨h.f, hfodd, h.q_eq_three_pow hJT hq⟩, fun _ => by rw [hcard]; ring,
    fun _ => hsimple, fun hs => absurd hs hnsolv⟩

theorem r3
    (hJT : JTThreeHyp) (hq5 : h.q ≠ 5) : h.R3 := by
  intro hq3 P
  have hq := h.five_lt_q hq5 hq3
  have hw := WardLocal.ward_two (h.toReeTypeHyp hJT hq) P
  simp only [toReeTypeHyp_q] at hw
  obtain ⟨hcard, -, hZ, hZc, -, -, hfr, hZ2, hcl, -, -, hP1e, hP1c, -, -, -, -, W, hWc, hWcard,
    hPW, hN, hW, -⟩ := hw
  refine ⟨hcard, hZ, hZc, hZ2.symm.trans hfr, hZ2.symm, hZ2.symm.trans hcl, ?_, ?_, W, hWc,
    hWcard, hPW, hN, fun t ht ht2 => ?_⟩
  · rw [← hZ2]
    exact hP1e.toIsMulCommutative
  · rw [← hZ2]
    exact hP1c
  · obtain ⟨-, -, -, hZt, hP1t⟩ := hW t ht ht2
    exact ⟨hZ2.symm.trans hP1t, hZt⟩

theorem r6
    (hJT : JTThreeHyp) (hq5 : h.q ≠ 5) : h.R6 := by
  intro hq3 m hm s
  exact WardLocal.ward_four_hall (h.toReeTypeHyp hJT (h.five_lt_q hq5 hq3)) m hm s

section Three

theorem card_zpowers_J_sup_of {X : Subgroup L} (hX : X ≤ Subgroup.centralizer ({h.J} : Set L))
    (hJX : h.J ∉ X) : Nat.card (Subgroup.zpowers h.J ⊔ X : Subgroup L) = 2 * Nat.card X := by
  have hc : ∀ x ∈ Subgroup.zpowers h.J, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hX hy)).symm n)).eq
  have hd : Subgroup.zpowers h.J ⊓ X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hx.1 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hx.2) hJX
  obtain ⟨hcard, -⟩ := card_sup_mul_card_inf_of_commute _ _ hc
  rw [hd, Subgroup.card_bot, mul_one, Nat.card_zpowers, h.orderOf_J] at hcard
  exact hcard

theorem centralizer_frame
    (fr : Frame h.toHyp) :
    Subgroup.centralizer ((fr.S : Subgroup L) : Set L) = fr.S := by
  have hE : fr.E = ⊥ := by
    have hEK : fr.E ≤ h.K := fun x hx =>
      h.mem_K_of_odd (fr.E_le_H hx) (odd_orderOf_of_mem_oddPart hx)
    have := fr.K_inf_E
    rw [toHyp_K, inf_eq_right.mpr hEK] at this
    exact this
  have hd := fr.isInternalDirectProduct_CS.1.1
  rw [hE, sup_bot_eq] at hd
  exact hd.symm

theorem card_normalizer_frame
    (fr : Frame h.toHyp) :
    Nat.card (Subgroup.normalizer ((fr.S : Subgroup L) : Set L)) = 168 := by
  have hidx := (lemma_2_2 L h.toHyp fr h.index_ne_two).1
  have hC := h.centralizer_frame fr
  have hCN : fr.CS ≤ Subgroup.normalizer ((fr.S : Subgroup L) : Set L) :=
    Subgroup.centralizer_le_normalizer _
  rw [card_normalizer_of_index hidx hCN, show fr.CS = (fr.S : Subgroup L) from hC,
    h.card_sylow fr.S]

theorem r12_of_three
    (hq3 : h.q = 3) : h.R1 ∧ h.R2 := by
  obtain ⟨fr⟩ := Frame.nonempty L h.toHyp
  obtain ⟨L', -, hsup, hinf, hOC, ⟨K', hK'le, hJK', hLH, ⟨eK'⟩⟩, hcases⟩ :=
    prop_2_4 L h.toHyp hq3 h.index_ne_two
  have hK : Nat.card h.K = 12 := by
    rw [PSL2Sub.card_eq h.iso h.odd_p h.f_pos, show h.p ^ h.f = 3 from hq3]
    norm_num
  have hK' : Nat.card K' = 12 := by
    rw [PSL2Sub.card_eq eK' (by decide) (by norm_num)]
    norm_num
  have hH : Nat.card (Subgroup.centralizer ({h.J} : Set L)) = 24 := by
    rw [h.centralizer_eq, h.card_zpowers_J_sup_of h.le_centralizer h.J_not_mem, hK]
  have hJ' : h.J ∈ L' ⊓ h.toHyp.H := by
    rw [hLH]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hK'H : K' ≤ Subgroup.centralizer ({h.J} : Set L) := hK'le.trans inf_le_right
  have hLHc : Nat.card (L' ⊓ h.toHyp.H : Subgroup L) = 24 := by
    rw [hLH, show h.toHyp.J = h.J from rfl, h.card_zpowers_J_sup_of hK'H hJK', hK']
  have hHL : h.toHyp.H ≤ L' := by
    have := Subgroup.eq_of_le_of_card_ge (inf_le_right : L' ⊓ h.toHyp.H ≤ h.toHyp.H)
      (by rw [hLHc]; exact hH.le)
    rw [← this]
    exact inf_le_left
  have hOH : CFSG.pPrimeCore 2 L ≤ h.toHyp.H :=
    hOC.trans (Subgroup.centralizer_le (by simpa using hJ'.1))
  have hO : CFSG.pPrimeCore 2 L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← hinf]
    exact ⟨hHL (hOH hx), hx⟩
  have hL'top : L' = ⊤ := by
    rw [hO, sup_bot_eq] at hsup
    exact hsup
  subst hL'top
  have hCS : ∀ S : Sylow 2 L, Subgroup.centralizer ((S : Subgroup L) : Set L) = S ∧
      Nat.card (Subgroup.normalizer ((S : Subgroup L) : Set L)) = 168 := by
    intro S
    obtain ⟨g, hg⟩ := exists_conj_sylow fr.S S
    rw [hg, centralizer_conj_smul, normalizer_conj_smul, card_conj_smul',
      h.centralizer_frame fr, h.card_normalizer_frame fr]
    exact ⟨rfl, rfl⟩
  have hR2 : h.R2 := ⟨hCS, (lemma_2_2 L h.toHyp fr h.index_ne_two).2.2⟩
  refine ⟨?_, hR2⟩
  have hodd : ∃ n : ℕ, Odd n ∧ h.q = 3 ^ n := ⟨1, odd_one, by rw [hq3, pow_one]⟩
  rcases hcases with ⟨h168, hN⟩ | ⟨h1512, hidx3, ⟨e8⟩⟩
  ·
    have hcard : Nat.card L = 168 := by rw [← Subgroup.card_top (G := L)]; exact h168
    have hnormal : ∀ S : Sylow 2 L, (S : Subgroup L).Normal := fun S => by
      have := hN S le_top
      rw [inf_top_eq] at this
      exact Subgroup.normalizer_eq_top_iff.mp this
    have hsolv : Group.IsSolvable L := by
      obtain ⟨S⟩ : Nonempty (Sylow 2 L) := inferInstance
      have := hnormal S
      have : IsMulCommutative (S : Subgroup L) := (h.elementary_sylow S).toIsMulCommutative
      have hS : Group.IsSolvable (S : Subgroup L) := inferInstance
      have hQ : Group.IsSolvable (L ⧸ (S : Subgroup L)) := by
        have h21 : Nat.card (L ⧸ (S : Subgroup L)) = 21 := by
          have h1 := Subgroup.card_mul_index (S : Subgroup L)
          rw [h.card_sylow S, hcard, Subgroup.index] at h1
          omega
        have hsq : Squarefree 21 := by
          rw [show (21 : ℕ) = 3 * 7 by norm_num]
          exact Nat.squarefree_mul_iff.mpr ⟨by norm_num, Nat.prime_three.squarefree,
            (by norm_num : Nat.Prime 7).squarefree⟩
        have : IsZGroup (L ⧸ (S : Subgroup L)) := IsZGroup.of_squarefree (by rw [h21]; exact hsq)
        infer_instance
      exact Group.isSolvable_of_subgroup_quotient (S : Subgroup L)
    exact ⟨hodd, fun hns => absurd hsolv hns, fun h3 => by omega,
      fun _ => ⟨hq3, hcard, fun S => ⟨hnormal S, (hCS S).1⟩⟩⟩
  ·
    have hcard : Nat.card L = 1512 := by rw [← Subgroup.card_top (G := L)]; exact h1512
    have hnsolv : ¬ Group.IsSolvable L := by
      intro hs
      have h1 : Group.IsSolvable (commutator (⊤ : Subgroup L)) := inferInstance
      have h2 : Group.IsSolvable PSL(2, GaloisField 2 3) :=
        Group.isSolvable_of_surjective (f := e8.toMonoidHom) e8.surjective
      have : IsSimpleGroup PSL(2, GaloisField 2 3) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
          rw [GaloisField.card 2 3 (by norm_num)]; norm_num)
      have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr h2
      have : IsMulCommutative PSL(2, GaloisField 2 3) := ⟨⟨hcomm⟩⟩
      have hprime := (Group.is_simple_iff_prime_card (α := PSL(2, GaloisField 2 3))).mp
        inferInstance
      have h504 : Nat.card PSL(2, GaloisField 2 3) = 504 := by
        rw [← Nat.card_congr e8.toEquiv]
        have h1 := Subgroup.card_mul_index (commutator (⊤ : Subgroup L))
        rw [hidx3, Subgroup.card_top, hcard] at h1
        omega
      rw [h504] at hprime
      norm_num at hprime
    exact ⟨hodd, fun _ => by rw [hcard, hq3]; norm_num, fun h3 => by omega,
      fun hs => absurd hs hnsolv⟩

end Three

end JRGroup

end CFSG.Walter.W67
