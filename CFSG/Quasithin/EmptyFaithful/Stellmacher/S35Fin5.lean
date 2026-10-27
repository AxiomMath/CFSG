module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

theorem card_zpowers_vp (p : Fin 5) : Nat.card (Subgroup.zpowers (vp p)) = 2 := by
  rw [Nat.card_zpowers]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact vp_mul_self p) (vp_ne_one p)

theorem mem_fixW_std_iff (w : orth.W) : w ∈ fixW orth S5Syl ↔ w = 1 ∨ w = vp 4 := by
  rw [mem_fixW]
  have h : ∀ w : orth.W, (∀ b ∈ S5SylF, orth.act b w = w) ↔ (w = 1 ∨ w = vp 4) := by
    decide +kernel
  rw [← h w]
  exact ⟨fun hw b hb => hw b ((mem_S5Syl_iff b).mpr hb),
    fun hw b hb => hw b ((mem_S5Syl_iff b).mp hb)⟩

theorem fixW_std : fixW orth S5Syl = Subgroup.zpowers (vp 4) := by
  ext w
  rw [mem_fixW_std_iff, mem_zpowers_iff_of_mul_self (vp_mul_self 4)]

theorem mp_zpowers_vp (g : Perm (Fin 5)) (p : Fin 5) :
    mp g (Subgroup.zpowers (vp p)) = Subgroup.zpowers (vp (g p)) := by
  rw [mp, MonoidHom.map_zpowers]
  congr 1
  exact act_vp g p

theorem fixW_sylow {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {p : Fin 5}
    (hp : IsFixPt D p) : fixW orth D = Subgroup.zpowers (vp p) := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  rw [isFixPt_cj_std_iff.mp hp, fixW_cj, fixW_std, mp_zpowers_vp]

theorem card_fixW_sylow {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    Nat.card (fixW orth D) = 2 := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  rw [fixW_cj, card_mp, fixW_std, card_zpowers_vp]

theorem le_ptStab {D : Subgroup (Perm (Fin 5))} {p : Fin 5} (hp : IsFixPt D p) : D ≤ ptStab p :=
  fun d hd => mem_ptStab.mpr (hp d hd)

theorem commIter_cj (g : Perm (Fin 5)) (B : Subgroup (Perm (Fin 5))) (i : ℕ) :
    F53Mod.commIter orth (cj g B) i = mp g (F53Mod.commIter orth B i) := by
  induction i with
  | zero => exact (map_act_top orth g).symm
  | succ i ih => exact (congrArg (commW orth (cj g B)) ih).trans (commW_cj g B _)

@[expose] def cF1 : Finset orth.W := spanF (commGensF orth S5SylF Finset.univ)

@[expose] def cF2 : Finset orth.W := spanF (commGensF orth S5SylF cF1)

@[expose] def cF3 : Finset orth.W := spanF (commGensF orth S5SylF cF2)

theorem mem_cF1 (w : orth.W) : w ∈ commW orth S5Syl ⊤ ↔ w ∈ cF1 :=
  mem_commW_iff orth mem_S5Syl_iff (fun u => by simp) w

theorem mem_cF2 (w : orth.W) : w ∈ commW orth S5Syl (commW orth S5Syl ⊤) ↔ w ∈ cF2 :=
  mem_commW_iff orth mem_S5Syl_iff mem_cF1 w

theorem mem_cF3 (w : orth.W) :
    w ∈ commW orth S5Syl (commW orth S5Syl (commW orth S5Syl ⊤)) ↔ w ∈ cF3 :=
  mem_commW_iff orth mem_S5Syl_iff mem_cF2 w

set_option maxRecDepth 100000 in
theorem commIter_two_std : F53Mod.commIter orth S5Syl 2 = commW orth (Subgroup.zpowers zStd) ⊤ := by
  ext w
  have h : ∀ w : orth.W, w ∈ cF2 ↔ w ∈ commF zStd := by
    unfold cF2 cF1 commF zStd; decide +kernel
  exact (mem_cF2 w).trans ((h w).trans (mem_commW_zpowers_iff zStd w).symm)

set_option maxRecDepth 100000 in
theorem commIter_three_std : F53Mod.commIter orth S5Syl 3 = fixW orth S5Syl := by
  ext w
  have h : ∀ w : orth.W, w ∈ cF3 ↔ ∀ b ∈ S5SylF, orth.act b w = w := by
    unfold cF3 cF2 cF1; decide +kernel
  rw [mem_fixW]
  refine (mem_cF3 w).trans ((h w).trans ?_)
  exact ⟨fun hw b hb => hw b ((mem_S5Syl_iff b).mp hb),
    fun hw b hb => hw b ((mem_S5Syl_iff b).mpr hb)⟩

theorem commW_two_eq {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {z : Perm (Fin 5)}
    (hz : IsCentInv D z) :
    commW orth D (commW orth D ⊤) = commW orth (Subgroup.zpowers z) ⊤ := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  have e1 : F53Mod.commIter orth (cj g S5Syl) 2 = mp g (F53Mod.commIter orth S5Syl 2) :=
    commIter_cj g _ 2
  have e2 : commW orth (Subgroup.zpowers (g * zStd * g⁻¹)) ⊤ =
      mp g (commW orth (Subgroup.zpowers zStd) ⊤) := by
    rw [← cj_zpowers, commW_cj_top]
  rw [isCentInv_cj_std_iff.mp hz, e2, ← commIter_two_std]
  exact e1

theorem commW_three_eq {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    commW orth D (commW orth D (commW orth D ⊤)) = fixW orth D := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  have e1 : F53Mod.commIter orth (cj g S5Syl) 3 = mp g (F53Mod.commIter orth S5Syl 3) :=
    commIter_cj g _ 3
  rw [fixW_cj, ← commIter_three_std]
  exact e1

theorem card_commW_sylow {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    Nat.card (commW orth D ⊤) = 8 := by
  have := profile_sylow orth (Or.inl rfl) hD
  exact congrArg (fun p => p.1) this

theorem card_commW_two_sylow {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    Nat.card (commW orth D (commW orth D ⊤)) = 4 := by
  have := profile_sylow orth (Or.inl rfl) hD
  exact congrArg (fun p => p.2.2) this

theorem card_commW_z {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {z : Perm (Fin 5)}
    (hz : IsCentInv D z) : Nat.card (commW orth (Subgroup.zpowers z) ⊤) = 4 := by
  rw [← commW_two_eq hD hz]; exact card_commW_two_sylow hD

theorem isInvSub_fixW (D : Subgroup (Perm (Fin 5))) : IsInvSub orth D (fixW orth D) := by
  intro b hb u hu
  rw [mem_fixW.mp hu b hb]; exact hu

theorem isInvSub_bot (D : Subgroup (Perm (Fin 5))) : IsInvSub orth D ⊥ := by
  intro b _ u hu
  rw [Subgroup.mem_bot.mp hu, map_one]; exact Subgroup.one_mem _

theorem isInvSub_top (D : Subgroup (Perm (Fin 5))) : IsInvSub orth D ⊤ := fun _ _ _ _ => trivial

theorem invSub_cases {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {z : Perm (Fin 5)}
    (hz : IsCentInv D z) (U : Subgroup orth.W) (hU : IsInvSub orth D U) :
    U = ⊥ ∨ U = fixW orth D ∨ U = commW orth (Subgroup.zpowers z) ⊤ ∨ U = commW orth D ⊤ ∨
      U = ⊤ := by
  have hdvd : Nat.card U ∣ 2 ^ 4 := by
    have := Subgroup.card_subgroup_dvd_card U
    rwa [card_orth] at this
  obtain ⟨k, hk, hkU⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have huniq : ∀ V : Subgroup orth.W, (IsInvSub orth D V ∧ Nat.card V = 2 ^ k) → U = V :=
    fun V hV => (lemma26_sylow orth (Or.inl rfl) hD k hk).unique ⟨hU, hkU⟩ hV
  have h2z := commW_two_eq hD hz
  interval_cases k
  · left
    refine huniq _ ⟨isInvSub_bot D, ?_⟩
    simp
  · right; left
    refine huniq _ ⟨isInvSub_fixW D, ?_⟩
    simpa using card_fixW_sylow hD
  · right; right; left
    refine huniq _ ⟨?_, ?_⟩
    · rw [← h2z]; exact isInvSub_commIter orth D 2
    · simpa using card_commW_z hD hz
  · right; right; right; left
    refine huniq _ ⟨isInvSub_commIter orth D 1, ?_⟩
    simpa using card_commW_sylow hD
  · right; right; right; right
    refine huniq _ ⟨isInvSub_top D, ?_⟩
    rw [Subgroup.card_top, card_orth]; norm_num

theorem eq_commW_z_of_card_four {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {z : Perm (Fin 5)} (hz : IsCentInv D z) {U : Subgroup orth.W} (hU : IsInvSub orth D U)
    (hc : Nat.card U = 4) : U = commW orth (Subgroup.zpowers z) ⊤ := by
  have h1 := card_fixW_sylow hD
  have h2 := card_commW_z hD hz
  have h3 := card_commW_sylow hD
  rcases invSub_cases hD hz U hU with h | h | h | h | h
  · rw [h] at hc; simp at hc
  · rw [h, h1] at hc; omega
  · exact h
  · rw [h, h3] at hc; omega
  · rw [h, Subgroup.card_top, card_orth] at hc; omega

theorem fixW_le_commW_z {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {z : Perm (Fin 5)}
    (hz : IsCentInv D z) : fixW orth D ≤ commW orth (Subgroup.zpowers z) ⊤ := by
  rw [← commW_two_eq hD hz, ← commW_three_eq hD]
  exact commW_le orth (isInvSub_commIter orth D 2)

theorem commW_z_le_commW {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {z : Perm (Fin 5)}
    (hz : IsCentInv D z) : commW orth (Subgroup.zpowers z) ⊤ ≤ commW orth D ⊤ := by
  rw [← commW_two_eq hD hz]
  exact commW_le orth (isInvSub_commIter orth D 1)

end CFSG.Quasithin.F53.Stellmacher.S35.Fin
