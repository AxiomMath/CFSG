module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsPerm
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {T : Type} [CommGroup T] [Finite T] {ι : Type} [Fintype ι]

structure S16tW3Hyp (Y : ι → Subgroup T) (X : Subgroup (MulAut T)) : Prop where
  card_index : Fintype.card ι = 3
  injective : Function.Injective Y
  iSup_eq_top : ⨆ i, Y i = ⊤
  card_eq_four : ∀ i, Nat.card ↥(Y i) = 4
  perm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j
  surj : ∀ π : Equiv.Perm ι, ∃ g ∈ X, ∀ i, (Y i).map g.toMonoidHom = Y (π i)
  not_three_le_pRank : ¬ 3 ≤ CFSG.Open.pRank 3 X
  dvd_card : 3 ^ 3 ∣ Nat.card X

variable {Y : ι → Subgroup T} {X : Subgroup (MulAut T)}

theorem s16t_w3_pow_six_of_fix (h : S16tW3Hyp Y X) {g : MulAut T}
    (hg : ∀ i, (Y i).map g.toMonoidHom = Y i) : g ^ 6 = 1 :=
  s16t_w3_ext h.iSup_eq_top fun i y hy => s16t_w3_pow_six (h.card_eq_four i) (hg i) y hy

theorem s16t_w3_pow_36 (h : S16tW3Hyp Y X) {g : MulAut T} (hgX : g ∈ X) : g ^ 36 = 1 := by
  classical
  obtain ⟨ρ, hρ⟩ := s16t_a_exists_perm_hom h.injective h.perm
  have h6 : ρ ⟨g, hgX⟩ ^ 6 = 1 := by
    have h1 := pow_card_eq_one (G := Equiv.Perm ι) (x := ρ ⟨g, hgX⟩)
    rw [Fintype.card_perm, h.card_index] at h1
    exact h1
  have hfix : ∀ i, (Y i).map (g ^ 6).toMonoidHom = Y i := by
    intro i
    have h1 := hρ (⟨g, hgX⟩ ^ 6) i
    rw [map_pow, h6] at h1
    exact h1
  calc g ^ 36 = (g ^ 6) ^ 6 := by rw [← pow_mul]
    _ = 1 := by simp only [s16t_w3_pow_six_of_fix h hfix, one_pow]

theorem s16t_w3_exists_S (h : S16tW3Hyp Y X) :
    ∃ S : Subgroup (MulAut T), (∀ g, g ∈ S ↔ g ∈ X ∧ (∀ i, (Y i).map g.toMonoidHom = Y i) ∧
      g ^ 3 = 1) ∧ ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
  have hcomm : ∀ a b : MulAut T, (∀ i, (Y i).map a.toMonoidHom = Y i) → a ^ 3 = 1 →
      (∀ i, (Y i).map b.toMonoidHom = Y i) → b ^ 3 = 1 → a * b = b * a := by
    intro a b ha ha3 hb hb3
    refine s16t_w3_ext h.iSup_eq_top fun i y hy => ?_
    refine s16t_w3_comm (h.card_eq_four i) (ha i) (hb i) (fun z _ => ?_) (fun z _ => ?_) y hy
    · rw [ha3]
      rfl
    · rw [hb3]
      rfl
  refine ⟨{ carrier := {g | g ∈ X ∧ (∀ i, (Y i).map g.toMonoidHom = Y i) ∧ g ^ 3 = 1}
            one_mem' := ⟨X.one_mem, fun i => s16t_w3_map_one, one_pow 3⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun g => Iff.rfl, ?_⟩
  · rintro a b ⟨haX, ha, ha3⟩ ⟨hbX, hb, hb3⟩
    refine ⟨X.mul_mem haX hbX, fun i => by rw [s16t_w3_map_mul, hb i, ha i], ?_⟩
    rw [Commute.mul_pow (hcomm a b ha ha3 hb hb3), ha3, hb3, one_mul]
  · rintro a ⟨haX, ha, ha3⟩
    exact ⟨X.inv_mem haX, fun i => s16t_w3_map_inv (ha i), by rw [inv_pow, ha3, inv_one]⟩
  · rintro a ⟨-, ha, ha3⟩ b ⟨-, hb, hb3⟩
    exact hcomm a b ha ha3 hb hb3

theorem s16t_w3_conj_mem (h : S16tW3Hyp Y X) {S : Subgroup (MulAut T)}
    (hS : ∀ g, g ∈ S ↔ g ∈ X ∧ (∀ i, (Y i).map g.toMonoidHom = Y i) ∧ g ^ 3 = 1)
    {g : MulAut T} (hg : g ∈ X) {s : MulAut T} (hs : s ∈ S) : g * s * g⁻¹ ∈ S := by
  obtain ⟨hsX, hsY, hs3⟩ := (hS s).1 hs
  refine (hS _).2 ⟨X.mul_mem (X.mul_mem hg hsX) (X.inv_mem hg), fun i => ?_, ?_⟩
  · obtain ⟨j, hj⟩ := h.perm g⁻¹ (X.inv_mem hg) i
    rw [s16t_w3_map_mul, s16t_w3_map_mul, hj, hsY j, ← hj, ← s16t_w3_map_mul, mul_inv_cancel,
      s16t_w3_map_one]
  · rw [conj_pow, hs3, mul_one, mul_inv_cancel]

theorem s16t_w3_mem_S_of_pow (h : S16tW3Hyp Y X) {S : Subgroup (MulAut T)}
    (hS : ∀ g, g ∈ S ↔ g ∈ X ∧ (∀ i, (Y i).map g.toMonoidHom = Y i) ∧ g ^ 3 = 1)
    {g : MulAut T} (hgX : g ∈ X) (hg : ∀ i, (Y i).map g.toMonoidHom = Y i) {k : ℕ}
    (hk : g ^ (3 ^ k) = 1) : g ∈ S := by
  refine (hS g).2 ⟨hgX, hg, ?_⟩
  have h1 : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one (s16t_w3_pow_six_of_fix h hg)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
  rw [hj] at h1
  refine orderOf_dvd_iff_pow_eq_one.1 ?_
  rw [hj]
  rcases j with _ | _ | j
  · exact one_dvd 3
  · exact dvd_rfl
  · exact absurd ((pow_dvd_pow 3 (by omega : 2 ≤ j + 2)).trans h1) (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
