module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Partner
public import CFSG.RankThree.GF2n.Stroth80.Sec312bAux

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem StrothHyp.sup_inf_sup_eq (H : StrothHyp M Q Z) {A B P : Subgroup G}
    (hA : ∃ g : G, A = conjSubgroup g Z) (hB : ∃ g : G, B = conjSubgroup g Z) (hne : A ≠ B)
    (hAP : A ≤ P) (hBP : B ≤ P) (hPQ : P ≤ Q) (hPZ : P ⊓ Z = ⊥) :
    (A ⊔ Z) ⊓ (B ⊔ Z) = Z := by
  obtain ⟨a₀, rfl⟩ := hA
  obtain ⟨b₀, rfl⟩ := hB
  have hAB : conjSubgroup a₀ Z ⊓ conjSubgroup b₀ Z = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    by_contra hy1
    exact hne (conjSubgroup_eq_of_mem_ne_one H hy1 hy.1 hy.2)
  have hAQ : conjSubgroup a₀ Z ≤ Q := hAP.trans hPQ
  have hBQ : conjSubgroup b₀ Z ≤ Q := hBP.trans hPQ
  have hAN : conjSubgroup a₀ Z ≤ Subgroup.normalizer (Z : Set G) := fun a ha =>
    H.Z_normal.2 (H.Q_normal.1 (hAQ ha))
  have hBN : conjSubgroup b₀ Z ≤ Subgroup.normalizer (Z : Set G) := fun b hb =>
    H.Z_normal.2 (H.Q_normal.1 (hBQ hb))
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  intro x hx
  obtain ⟨hxA, hxZ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a, haA, z, hzZ, haz⟩ := exists_mul_of_mem_sup_of_le_normalizer hAN hxA
  obtain ⟨b, hbB, z', hz'Z, hbz⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN hxZ
  have hba : b⁻¹ * a = z' * z⁻¹ := by
    calc b⁻¹ * a = b⁻¹ * (a * z) * z⁻¹ := by group
      _ = b⁻¹ * (b * z') * z⁻¹ := by rw [haz, hbz]
      _ = z' * z⁻¹ := by group
  have hin : b⁻¹ * a ∈ P ⊓ Z :=
    Subgroup.mem_inf.mpr ⟨P.mul_mem (P.inv_mem (hBP hbB)) (hAP haA),
      by rw [hba]; exact Z.mul_mem hz'Z (Z.inv_mem hzZ)⟩
  rw [hPZ, Subgroup.mem_bot] at hin
  have hab : a = b := by
    calc a = b * (b⁻¹ * a) := by group
      _ = b := by rw [hin, mul_one]
  have ha1 : a = 1 := by
    have hmem : a ∈ conjSubgroup a₀ Z ⊓ conjSubgroup b₀ Z := ⟨haA, hab ▸ hbB⟩
    rwa [hAB, Subgroup.mem_bot] at hmem
  rw [← haz, ha1, one_mul]
  exact hzZ

private theorem Ctx.exists_conj_not_le_sup_of_mem_Vt (hc : Ctx M Q Z B) {t : G}
    (hV : Nat.card Z ^ 2 < Nat.card ↥(Vt M (LB M Q B) B Z t)) :
    ∃ h ∈ M, t ∈ conjSubgroup h (LB M Q B) ∧ ¬ conjSubgroup h B ≤ B ⊔ Z := by
  by_contra hcon
  push Not at hcon
  have hle : Vt M (LB M Q B) B Z t ≤ B ⊔ Z := by
    refine sec39_Vt_le le_sup_right ?_
    intro m hm htm
    exact hcon m hm htm
  have hcard : Nat.card ↥(Vt M (LB M Q B) B Z t) ≤ Nat.card ↥(B ⊔ Z) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
  have hBZ : Nat.card ↥(B ⊔ Z) = Nat.card Z ^ 2 := by
    obtain ⟨k, hk⟩ := hc.conj
    have hBcard : Nat.card B = Nat.card Z := by rw [hk, card_conjSubgroup]
    have hBN : B ≤ Subgroup.normalizer (Z : Set G) := fun x hx =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.le hx))
    have h := card_sup_mul_card_inf_of_normalizer (A := Z) (C := B) hBN
    rw [hc.inf_eq_bot, Subgroup.card_bot, mul_one, hBcard] at h
    rw [sup_comm, h, pow_two]
  rw [hBZ] at hcard
  omega

private theorem Ctx.conj_inv_le_sup_Z (hc : Ctx M Q Z B) {w : G} (hwQ : w ∈ Q) :
    conjSubgroup w⁻¹ B ≤ B ⊔ Z := by
  intro b hb
  have hb' : w * b * w⁻¹ ∈ B := by simpa using mem_conjSubgroup.mp hb
  have h := hc.LB_conj_mem_BZ (t := w⁻¹) (sec39_Q_le_LB (Q.inv_mem hwQ))
    (Subgroup.mem_sup_left hb')
  rwa [show w⁻¹ * (w * b * w⁻¹) * (w⁻¹)⁻¹ = b by group] at h

private theorem Ctx.conj_mul_ne_of_not_le_sup_Z (hc : Ctx M Q Z B) {w h : G} (hwQ : w ∈ Q)
    (hhnot : ¬ conjSubgroup h B ≤ B ⊔ Z) : conjSubgroup (w * h) B ≠ B := by
  intro heq
  apply hhnot
  have hBh : conjSubgroup h B = conjSubgroup w⁻¹ B := by
    have h1 := congrArg (conjSubgroup w⁻¹) heq
    rw [← conjSubgroup_mul] at h1
    rw [show w⁻¹ * (w * h) = h by group] at h1
    exact h1
  rw [hBh]
  exact hc.conj_inv_le_sup_Z hwQ

theorem Good103.exists_conj_le_inf {hc : Ctx M Q Z B} {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hV : Nat.card Z ^ 2 < Nat.card ↥(Vt M (LB M Q B) B Z t)) :
    ∃ g ∈ M, conjSubgroup g B ≤ Q ⊓ QB Y ∧ conjSubgroup g B ≠ B ∧
      t ∈ conjSubgroup g (LB M Q B) ∧ t ∈ QB (conjSubgroup g B) ∧
      (conjSubgroup g B ⊔ Z) ⊓ (B ⊔ Z) = Z := by
  obtain ⟨h, hhM, hth, hhnot⟩ := hc.exists_conj_not_le_sup_of_mem_Vt hV
  have hVle : conjSubgroup h B ≤ (Q ⊓ QB Y) ⊔ Z :=
    (sec39_conjB_le_Vt hhM hth).trans (le_of_eq (Good103.Vt_eq ht hs))
  obtain ⟨w, hwQ, a, haX, ha1, haP⟩ :=
    Ctx.exists_conj_mem_of_le_sup (hc := hc) (m := h) (P := Q ⊓ QB Y) hhM inf_le_left hVle
  have hgM : w * h ∈ M := M.mul_mem (hc.hyp.Q_normal.1 hwQ) hhM
  have hX : Ctx M Q Z (conjSubgroup (w * h) B) := hc.conj_of_mem hgM
  have htQBX : t ∈ QB (conjSubgroup (w * h) B) :=
    hX.mem_QB_of_inf_QB_zpowers hs haX ha1 (QB_le_QB_zpowers hs haP.2)
  have hXQY : conjSubgroup (w * h) B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hX.conj hs.conj hs.mem hs.ne_one htQBX
  have hXQ : conjSubgroup (w * h) B ≤ Q := hX.le
  have hQleLh : Q ≤ conjSubgroup h (LB M Q B) := by
    rw [← hc.LB_conj hhM]
    exact sec39_Q_le_LB
  have htLg : t ∈ conjSubgroup (w * h) (LB M Q B) := by
    rw [conjSubgroup_mul]
    have hwLh : w ∈ conjSubgroup h (LB M Q B) := hQleLh hwQ
    rw [conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hwLh)]
    exact hth
  have hne : conjSubgroup (w * h) B ≠ B := hc.conj_mul_ne_of_not_le_sup_Z hwQ hhnot
  have hPZ : (Q ⊓ QB Y) ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨⟨-, hzQB⟩, hzZ⟩
    have hmem : z ∈ Z ⊓ QB Y := ⟨hzZ, hzQB⟩
    rwa [Z_inf_QB_eq_bot hs (smith_1_12 hs), Subgroup.mem_bot] at hmem
  have hlast : (conjSubgroup (w * h) B ⊔ Z) ⊓ (B ⊔ Z) = Z := by
    refine hc.hyp.sup_inf_sup_eq (A := conjSubgroup (w * h) B) (B := B)
      (P := Q ⊓ QB Y) ?_ hc.conj hne (le_inf hXQ hXQY)
      (le_inf hc.le (hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one
        ht.1.2.2.2.1)) inf_le_left hPZ
    obtain ⟨b₀, hb₀⟩ := hc.conj
    exact ⟨(w * h) * b₀, by rw [hb₀, ← conjSubgroup_mul]⟩
  exact ⟨w * h, hgM, le_inf hXQ hXQY, hne, htLg, htQBX, hlast⟩

theorem Sec10Hyp.conj_of_mem {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {g : G}
    (hg : g ∈ M) : Sec10Hyp (hc.conj_of_mem hg) n :=
  (H.conjG g).of_eq (hc.conj_of_mem hg) (hc.conj_M_eq hg) (hc.conj_Q_eq hg)
    (hc.conj_Z_eq hg) rfl

theorem SLMNat.conj_of_mem_iff {hc : Ctx M Q Z B} {g : G} (hg : g ∈ M) {t : G} {m : ℕ} :
    SLMNat (hc.conj_of_mem hg) t m ↔ SLMNat hc t m := by
  unfold SLMNat
  rw [(rt_vt_conj hc hg t).1, (rt_vt_conj hc hg t).2, Ctx.CN_conj_eq hc hg t]

theorem Good103.conj_of_mem (hc : Ctx M Q Z B) {t : G} (ht : Good103 M Q Z B t) {g : G}
    (hg : g ∈ M) (htB : t ∈ QB (conjSubgroup g B)) :
    Good103 M Q Z (conjSubgroup g B) t := by
  refine ⟨⟨ht.1.1, ht.1.2.1, ht.1.2.2.1, htB, ?_⟩, ?_⟩
  · intro heq
    apply ht.1.2.2.2.2
    rw [(rt_vt_conj hc hg t).1, hc.LB_conj hg] at heq
    have hle : LB M Q B ≤ conjSubgroup g (LB M Q B) := by
      rw [← heq]
      exact le_Rt (LB M Q B) ht.1.mem_LB
    have hcard : Nat.card (conjSubgroup g (LB M Q B)) = Nat.card (LB M Q B) :=
      card_conjSubgroup g _
    exact heq.trans (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  · rw [(rt_vt_conj hc hg t).2]
    exact ht.2

theorem noSL2_conj_of_mem {hc : Ctx M Q Z B}
    (h : ∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2) {g : G} (hg : g ∈ M) :
    ∀ s : G, Good101 M Q Z (conjSubgroup g B) s → ¬ SLMNat (hc.conj_of_mem hg) s 2 := by
  intro s hs hs2
  have hs' : Good101 (conjSubgroup g M) (conjSubgroup g Q) (conjSubgroup g Z)
      (conjSubgroup g B) s := by
    rwa [hc.conj_M_eq hg, hc.conj_Q_eq hg, hc.conj_Z_eq hg]
  have hnot := noSL2_conjG h g s hs'
  apply hnot
  refine SLMNat.of_eq hs2 (hc.conjBy g) (hc.conj_M_eq hg).symm (hc.conj_Q_eq hg).symm
    (hc.conj_Z_eq hg).symm rfl

end CFSG.RankThree.GF2n.Stroth80
