module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3ElevInv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3GL6
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {T : Type} [CommGroup T] [Finite T]

private theorem s1614e3_row11_card_of_elemAbelian {E : Subgroup (MulAut T)}
    (hE : IsElemAbelianOfRank 7 2 ↥E) : Nat.card E = 7 ^ 2 := by
  obtain ⟨e⟩ := hE
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_fun,
    Nat.card_fin, Nat.card_zmod]

private theorem s1614e3_row11_pow_seven_eq_one {E : Subgroup (MulAut T)}
    (hE : IsElemAbelianOfRank 7 2 ↥E) : ∀ x ∈ E, x ^ 7 = 1 := by
  obtain ⟨e⟩ := hE
  intro x hx
  have hE1 : (⟨x, hx⟩ : ↥E) ^ 7 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    have hzero : (7 • Multiplicative.toAdd (e ⟨x, hx⟩)) = 0 := by
      funext i
      rw [Pi.zero_apply, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    calc (e ⟨x, hx⟩) ^ 7
        = Multiplicative.ofAdd (7 • Multiplicative.toAdd (e ⟨x, hx⟩)) :=
          (ofAdd_nsmul 7 (Multiplicative.toAdd (e ⟨x, hx⟩))).symm
      _ = Multiplicative.ofAdd 0 := by rw [hzero]
      _ = 1 := rfl
  exact congrArg Subtype.val hE1

theorem s1614e3_row11_rk (hT : ∀ t : T, t ^ 2 = 1) {X A : Subgroup (MulAut T)} {g : MulAut T}
    (h : S16n9bTwo X A g) (hrk : rk ↥(commSub ⊤ A) = 3) : rk T = 6 := by
  have h1 : rk ↥(commSub ⊤ A ⊔ (commSub ⊤ A).map g.toMonoidHom) +
      rk ↥(commSub ⊤ A ⊓ (commSub ⊤ A).map g.toMonoidHom) =
      rk ↥(commSub ⊤ A) + rk ↥((commSub ⊤ A).map g.toMonoidHom) :=
    rk_sup_add_rk_inf _ _
  rw [h.sup, h.inf, rk_top, rk_bot, s16n9b_rk_map g, hrk] at h1
  omega

theorem s1614e3_row11_rkIdx (hT : ∀ t : T, t ^ 2 = 1) {X A : Subgroup (MulAut T)}
    {g : MulAut T} (h : S16n9bTwo X A g) (hrk : rk ↥(commSub ⊤ A) = 3) (hA7 : Nat.card A = 7)
    {t : MulAut T} (htX : t ∈ X) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    rkIdx (fixV (Subgroup.zpowers t)) = 3 := by
  have ht2' : t ^ 2 = 1 := by rw [pow_two]; exact ht2
  have h1 : 3 ≤ rkIdx (fixV (Subgroup.zpowers t)) :=
    s16t_elev_three_le_rkIdx_fixV hT h hrk hA7 htX ht2' ht1
  have h2 : 2 * rkIdx (fixV (Subgroup.zpowers t)) ≤ rk T :=
    s1614e3_two_mul_rkIdx_le hT ht2
  have h3 : rk T = 6 := s1614e3_row11_rk hT h hrk
  omega

theorem s1614e3_row11_commute (hT : ∀ t : T, t ^ 2 = 1) {X A : Subgroup (MulAut T)}
    {g : MulAut T} (h : S16n9bTwo X A g) (hrk : rk ↥(commSub ⊤ A) = 3) (hA7 : Nat.card A = 7)
    (hrkT : rk T = 6) {t : MulAut T} (htX : t ∈ X) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (E : Subgroup (MulAut T)) (hEX : E ≤ X) (hE : IsElemAbelianOfRank 7 2 ↥E) :
    ∃ e ∈ E, e ≠ 1 ∧ e * t = t * e := by
  haveI : Finite (MulAut T) := MulEquiv.finite_left
  have ht2' : t ^ 2 = 1 := by rw [pow_two]; exact ht2
  have hallfix : ∀ a : MulAut T, (∀ y ∈ commSub ⊤ A, a y = y) →
      (∀ y ∈ (commSub ⊤ A).map g.toMonoidHom, a y = y) → a = 1 := by
    intro a h1 h2
    apply MulEquiv.ext
    intro x
    have hx : x ∈ commSub ⊤ A ⊔ (commSub ⊤ A).map g.toMonoidHom := by
      rw [h.sup]; exact Subgroup.mem_top x
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    rw [map_mul, h1 y hy, h2 z hz]
    rfl
  have hAB : A ⊓ A.map (MulAut.conj g).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    exact hallfix a (fun y hy => h.fixB a ha.2 y hy) (fun y hy => h.fixA a ha.1 y hy)
  have hcomm : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj g).toMonoidHom, a * b = b * a := by
    intro a ha b hb
    have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h.comm
    exact ((Subgroup.mem_centralizer_iff.1 (h2 ha)) b hb).symm
  set P : Subgroup (MulAut T) := A ⊔ A.map (MulAut.conj g).toMonoidHom with hP
  have hB7 : Nat.card (A.map (MulAut.conj g).toMonoidHom) = 7 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA7]
  have hP49 : Nat.card P = 7 ^ 2 := by
    rw [hP]
    have hc := CFSG.card_sup_eq_mul_of_commute A (A.map (MulAut.conj g).toMonoidHom)
      (fun a ha b hb => hcomm a ha b hb) hAB
    rw [hA7, hB7] at hc
    rw [hc]
    norm_num
  have hBX : A.map (MulAut.conj g).toMonoidHom ≤ X := by
    rintro b ⟨a, ha, rfl⟩
    show MulAut.conj g a ∈ X
    rw [MulAut.conj_apply]
    exact X.mul_mem (X.mul_mem h.mem (h.le ha)) (X.inv_mem h.mem)
  have hPX : P ≤ X := by
    rw [hP]
    exact sup_le h.le hBX
  have hPn : ∀ x ∈ X, P.map (MulAut.conj x).toMonoidHom ≤ P := by
    intro x hx
    rw [hP]
    rw [Subgroup.map_sup]
    apply sup_le
    · rcases h.conj x hx with h1 | h1
      · rw [h1]; exact le_sup_left
      · rw [h1]; exact le_sup_right
    · rw [s16n9b_map_conj_map_conj A g x]
      rcases h.conj (x * g) (X.mul_mem hx h.mem) with h1 | h1
      · rw [h1]; exact le_sup_left
      · rw [h1]; exact le_sup_right
  have hX7le : (Nat.card X).factorization 7 ≤ 2 :=
    s1614e3_factorization_seven_le_two hT hrkT X
  have hPXdvd : 7 ^ 2 ∣ Nat.card X := by
    rw [← hP49]
    exact Subgroup.card_dvd_of_le hPX
  have hX7ge : 2 ≤ (Nat.card X).factorization 7 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_seven (Nat.card_pos (α := X)).ne').1
      hPXdvd
  have hP7 : (Nat.card P).factorization 7 = 2 := by
    rw [hP49, Nat.factorization_pow_self Nat.prime_seven]
  have hord : (Nat.card X).factorization 7 = (Nat.card P).factorization 7 := by
    rw [hP7]; omega
  have hE49 : Nat.card E = 7 ^ 2 := s1614e3_row11_card_of_elemAbelian hE
  have hEpow : ∀ x ∈ E, x ^ 7 = 1 := s1614e3_row11_pow_seven_eq_one hE
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨x, hxX, hxle⟩ :=
    CFSG.RankThree.PartOne.K133H.exists_conj_le_of_sylow hPX hEX hEpow hord
  have hEP : E ≤ P := by
    intro e he
    have h1 : MulAut.conj x e ∈ P := hxle (Subgroup.mem_map.2 ⟨e, he, rfl⟩)
    have h2 : MulAut.conj x⁻¹ (MulAut.conj x e) ∈ P.map (MulAut.conj x⁻¹).toMonoidHom :=
      Subgroup.mem_map.2 ⟨MulAut.conj x e, h1, rfl⟩
    have h3 : MulAut.conj x⁻¹ (MulAut.conj x e) ∈ P := hPn x⁻¹ (X.inv_mem hxX) h2
    have heq : MulAut.conj x⁻¹ (MulAut.conj x e) = e := by
      rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
      group
    rwa [heq] at h3
  have hEP' : E = P := by
    refine Subgroup.eq_of_le_of_card_ge hEP ?_
    rw [hP49, hE49]
  have hAne : ∃ a ∈ A, a ≠ 1 := by
    have h1 : 1 < Nat.card A := by rw [hA7]; norm_num
    haveI : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.1 h1
    exact (Subgroup.nontrivial_iff_exists_ne_one A).1 inferInstance
  obtain ⟨a, haA, ha1⟩ := hAne
  have hAt : A.map (MulAut.conj t).toMonoidHom = A.map (MulAut.conj g).toMonoidHom :=
    s16t_elev_map_conj_eq_of_ne_one hT h hrk hA7 htX ht2' ht1
  set b : MulAut T := MulAut.conj t a with hb
  have hb_eq : b = t * a * t⁻¹ := by rw [hb, MulAut.conj_apply]
  have hbB : b ∈ A.map (MulAut.conj g).toMonoidHom := by
    rw [hb, ← hAt]
    exact Subgroup.mem_map.2 ⟨a, haA, rfl⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htb : t * b * t⁻¹ = a := by
    rw [hb_eq, htinv]
    calc t * (t * a * t) * t = (t * t) * (a * (t * t)) := by group
      _ = a := by rw [ht2]; group
  refine ⟨a * b, ?_, ?_, ?_⟩
  · rw [hEP', hP]
    exact Subgroup.mul_mem_sup haA hbB
  · intro he1
    have hb1 : a = b⁻¹ := by
      calc a = a * b * b⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
        _ = 1 * b⁻¹ := by rw [he1]
        _ = b⁻¹ := one_mul _
    have haB : a ∈ A.map (MulAut.conj g).toMonoidHom := by
      rw [hb1]; exact Subgroup.inv_mem _ hbB
    have hab : a ∈ A ⊓ A.map (MulAut.conj g).toMonoidHom := ⟨haA, haB⟩
    rw [hAB] at hab
    exact ha1 (Subgroup.mem_bot.1 hab)
  · have hconj : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
    have hba : t * a * t⁻¹ = b := by rw [hb_eq]
    have hte : t * (a * b) * t⁻¹ = a * b := by
      rw [hconj, hba, htb]
      exact (hcomm a haA b hbB).symm
    have het : t * (a * b) = (a * b) * t := by
      calc t * (a * b) = (t * (a * b) * t⁻¹) * t := by group
        _ = (a * b) * t := by rw [hte]
    exact het.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
