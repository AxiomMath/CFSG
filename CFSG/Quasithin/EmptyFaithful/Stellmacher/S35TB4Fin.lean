module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin11
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin7

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.TB4

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

theorem vp_not_mem : ∀ a b q : Fin 5, a ≠ b → q ≠ a → q ≠ b →
    ¬ (vp q = 1 ∨ vp q = vp a ∨ vp q = vp b ∨ vp q = vp a * vp b) := by
  decide +kernel

theorem vp_mul_not_mem : ∀ a b q : Fin 5, a ≠ b → q ≠ a → q ≠ b →
    ¬ (vp q * vp b = 1 ∨ vp q * vp b = vp a ∨ vp q * vp b = vp b ∨
      vp q * vp b = vp a * vp b) := by
  decide +kernel

theorem mem_sup_zpowers_vp {a b : Fin 5} {w : orth.W} :
    w ∈ Subgroup.zpowers (vp a) ⊔ Subgroup.zpowers (vp b) ↔
      w = 1 ∨ w = vp a ∨ w = vp b ∨ w = vp a * vp b := by
  rw [Subgroup.mem_sup]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rcases (mem_zpowers_iff_of_mul_self (vp_mul_self a)).mp hx with rfl | rfl <;>
      rcases (mem_zpowers_iff_of_mul_self (vp_mul_self b)).mp hy with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, mul_one 1⟩
    · exact ⟨_, Subgroup.mem_zpowers _, 1, Subgroup.one_mem _, mul_one _⟩
    · exact ⟨1, Subgroup.one_mem _, _, Subgroup.mem_zpowers _, one_mul _⟩
    · exact ⟨_, Subgroup.mem_zpowers _, _, Subgroup.mem_zpowers _, rfl⟩

theorem exists_mem_That_move {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {p : Fin 5}
    (hp : IsFixPt D p) {q : Fin 5} (hq : q ≠ p) : ∃ t ∈ That D, t q ≠ q := by
  obtain ⟨a, b, c, d, p', h, hdec⟩ := exists_decomp_of_centInv hD (isCentInv_zc hD)
  have hp' : p' = p :=
    IsFixPt.unique hD (isFixPt_of_decomp hD (isCentInv_zc hD) h hdec) hp
  subst hp'
  have hcov : ∀ a b c d p q : Fin 5, [a, b, c, d, p].Nodup → q ≠ p →
      (q = a ∨ q = b) ∨ (q = c ∨ q = d) := by decide +kernel
  have hnd : ∀ a b c d p : Fin 5, [a, b, c, d, p].Nodup → a ≠ b ∧ c ≠ d := by decide +kernel
  have hm := mem_That_iff hD (isCentInv_zc hD) h hdec
  obtain ⟨hab, hcd⟩ := hnd a b c d p' h
  rcases hcov a b c d p' q h hq with hq' | hq'
  · refine ⟨swap a b, (hm _).mpr (Or.inr (Or.inl rfl)), ?_⟩
    rcases hq' with rfl | rfl
    · rw [swap_apply_left]; exact hab.symm
    · rw [swap_apply_right]; exact hab
  · refine ⟨swap c d, (hm _).mpr (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
    rcases hq' with rfl | rfl
    · rw [swap_apply_left]; exact hcd.symm
    · rw [swap_apply_right]; exact hcd

variable {Da Db : Subgroup (Perm (Fin 5))} {pa pb : Fin 5}

theorem centre_trick (hDa : Nat.card Da = 8) (hDb : Nat.card Db = 8) (hpa : IsFixPt Da pa)
    (hpb : IsFixPt Db pb) (hne : pa ≠ pb) {U : Subgroup orth.W}
    (hU : U ≤ Subgroup.zpowers (vp pa) ⊔ Subgroup.zpowers (vp pb))
    (hia : ∀ g ∈ That Da, ∀ u ∈ U, orth.act g u ∈ U)
    (hib : ∀ g ∈ That Db, ∀ u ∈ U, orth.act g u ∈ U) : U = ⊥ := by
  obtain ⟨t, ht, htq⟩ := exists_mem_That_move hDb hpb (q := pa) hne
  obtain ⟨s, hs, hsq⟩ := exists_mem_That_move hDa hpa (q := pb) hne.symm
  have htb : t pb = pb := hpb t (That_le Db ht)
  have hsa : s pa = pa := hpa s (That_le Da hs)
  have htpb : t pa ≠ pb := fun h => hne (t.injective (h.trans htb.symm))
  have hspa : s pb ≠ pa := fun h => hne.symm (s.injective (h.trans hsa.symm))
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have hu' := mem_sup_zpowers_vp.mp (hU hu)
  have hvt : ∀ u ∈ U, orth.act t u ∈ Subgroup.zpowers (vp pa) ⊔ Subgroup.zpowers (vp pb) :=
    fun u hu => hU (hib t ht u hu)
  have hvs : ∀ u ∈ U, orth.act s u ∈ Subgroup.zpowers (vp pa) ⊔ Subgroup.zpowers (vp pb) :=
    fun u hu => hU (hia s hs u hu)
  rcases hu' with h1 | h1 | h1 | h1
  · exact h1
  · exfalso
    have := mem_sup_zpowers_vp.mp (hvt u hu)
    rw [h1, act_vp] at this
    exact vp_not_mem pa pb (t pa) hne htq htpb this
  · exfalso
    have := mem_sup_zpowers_vp.mp (hvs u hu)
    rw [h1, act_vp] at this
    exact vp_not_mem pa pb (s pb) hne hspa hsq this
  · exfalso
    have := mem_sup_zpowers_vp.mp (hvt u hu)
    rw [h1, map_mul, act_vp, act_vp, htb] at this
    exact vp_mul_not_mem pa pb (t pa) hne htq htpb this

end CFSG.Quasithin.F53.Stellmacher.S35.TB4
