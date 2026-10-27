module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B1ChiefCount
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312B

public section

namespace CFSG.Quasithin.H13.L3312.NQ

open CFSG.Open CFSG.QuasithinUnique

theorem sl2_involution_eq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {x y : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)} (hx : x * x = 1) (hy : y * y = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have h2 := CFSG.SectionRank.Ccomm.two_ne_zero_zmod hp
  have key : ∀ w : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), w * w = 1 → w ≠ 1 →
      (w : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 := by
    intro w hw hw1
    have hsq : (w : Matrix (Fin 2) (Fin 2) (ZMod p)) * w = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, hw, Matrix.SpecialLinearGroup.coe_one]
    rcases CFSG.SectionRank.Ccomm.eq_one_or_neg_one_of_sq_eq_one h2 w.2 hsq with h | h
    · exact absurd (Subtype.ext (h.trans Matrix.SpecialLinearGroup.coe_one.symm)) hw1
    · exact h
  exact Subtype.ext ((key x hx hx1).trans (key y hy hy1).symm)

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem inv_mul_mem_of_isSL2 {O : Subgroup Q} [O.Normal] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hQ : IsSL2 p (Q ⧸ O)) {t t' : Q} (ht : t * t = 1) (ht' : t' * t' = 1) (htO : t ∉ O)
    (ht'O : t' ∉ O) : t'⁻¹ * t ∈ O := by
  obtain ⟨e⟩ := hQ
  have hinv : ∀ u : Q, u * u = 1 → u ∉ O →
      e (u : Q ⧸ O) * e (u : Q ⧸ O) = 1 ∧ e (u : Q ⧸ O) ≠ 1 := by
    intro u hu huO
    refine ⟨?_, fun h => huO ?_⟩
    · rw [← map_mul, ← QuotientGroup.mk_mul, hu, QuotientGroup.mk_one, map_one]
    · rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff] at h
      exact h
  obtain ⟨h1, h2⟩ := hinv t ht htO
  obtain ⟨h3, h4⟩ := hinv t' ht' ht'O
  have := e.injective (sl2_involution_eq hp h3 h1 h4 h2)
  rw [QuotientGroup.eq] at this
  exact this

omit [Finite Q] in
theorem conj_apply_eq (d : MulAut Q) (x : Q) :
    MulAut.conj (d x) = d * MulAut.conj x * d⁻¹ := by
  ext y
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv]

omit [Finite Q] in
theorem fix_z (hZodd : Odd (Nat.card (Subgroup.center Q))) {O : Subgroup Q} [O.Characteristic]
    (hOodd : Odd (Nat.card O))
    (huniq : ∀ t t' : Q, t * t = 1 → t' * t' = 1 → t ∉ O → t' ∉ O → t'⁻¹ * t ∈ O)
    {A S : Subgroup (MulAut Q)} (hS : IsSylowTwoOf S A) {z : Q} (hz2 : z * z = 1) (hzO : z ∉ O)
    (hzS : MulAut.conj z ∈ S) {d : MulAut Q} (hd : d ∈ Subgroup.normalizer (S : Set (MulAut Q))) :
    d z = z := by
  have hdz2 : d z * d z = 1 := by rw [← map_mul, hz2, map_one]
  have hdzO : d z ∉ O := by
    intro h
    apply hzO
    have := (Subgroup.characteristic_iff_map_eq.mp ‹O.Characteristic› d⁻¹)
    rw [← this]
    exact ⟨d z, h, by simp⟩
  set o := (d z)⁻¹ * z with ho
  have hoO : o ∈ O := huniq z (d z) hz2 hdz2 hzO hdzO
  have hdzS : MulAut.conj (d z) ∈ S := by
    rw [conj_apply_eq]
    exact (Subgroup.mem_normalizer_iff.mp hd _).mp hzS
  have hoS : MulAut.conj o ∈ S := by
    rw [ho, map_mul, map_inv]
    exact S.mul_mem (S.inv_mem hdzS) hzS
  have hconj1 : MulAut.conj o = 1 := by
    obtain ⟨k, hk⟩ := hS.2.1 ⟨_, hoS⟩
    have h1 : (MulAut.conj o) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : (MulAut.conj o) ^ Nat.card O = 1 := by
      rw [← map_pow]
      have : o ^ Nat.card O = 1 := by
        have := pow_card_eq_one' (G := O) (x := ⟨o, hoO⟩)
        exact congrArg Subtype.val this
      rw [this, map_one]
    have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hOodd)
    have h3 := orderOf_dvd_of_pow_eq_one h1
    have h4 := orderOf_dvd_of_pow_eq_one h2
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h3 hcop) h4
    rwa [orderOf_eq_one_iff] at this
  have hoc : o ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun f : MulAut Q => f g) hconj1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * o = o * g * o⁻¹ * o := by rw [h1]
      _ = o * g := by group
  have hzo : z = d z * o := by rw [ho, mul_inv_cancel_left]
  have ho2 : o * o = 1 := by
    have hcomm : o * d z = d z * o := (Subgroup.mem_center_iff.mp hoc (d z)).symm
    have : z * z = (d z * d z) * (o * o) := by
      have hzz : z * z = (d z * o) * (d z * o) := by rw [← hzo]
      rw [hzz]
      calc d z * o * (d z * o) = d z * (o * d z) * o := by group
        _ = d z * (d z * o) * o := by rw [hcomm]
        _ = (d z * d z) * (o * o) := by group
    rw [hz2, hdz2, one_mul] at this
    exact this.symm
  have ho1 : o = 1 := by
    have h1 : orderOf (⟨o, hoc⟩ : ↥(Subgroup.center Q)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using ho2))
    have h2 := orderOf_dvd_natCard (⟨o, hoc⟩ : ↥(Subgroup.center Q))
    have hcop : Nat.Coprime 2 (Nat.card (Subgroup.center Q)) := Nat.coprime_two_left.mpr hZodd
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rw [orderOf_eq_one_iff] at this
    exact congrArg Subtype.val this
  calc d z = d z * o := by rw [ho1, mul_one]
    _ = z := hzo.symm

theorem conj_mem_of_fix {A S : Subgroup (MulAut Q)}
    (hInn : (MulAut.conj : Q →* MulAut Q).range ≤ A) (hS : IsSylowTwoOf S A) {z : Q}
    (hz2 : z * z = 1) (hSz : ∀ s ∈ S, s z = z) : MulAut.conj z ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut Q) :=
    Finite.of_injective (fun f : MulAut Q => (f : Q → Q)) fun f g h => MulEquiv.ext (congrFun h)
  set c := MulAut.conj z with hc
  have hc2 : c * c = 1 := by rw [hc, ← map_mul, hz2, map_one]
  have hcS : ∀ s ∈ S, s * c * s⁻¹ = c := fun s hs => by
    rw [hc, ← conj_apply_eq, hSz s hs]
  have hz : IsPGroup 2 ↥(Subgroup.zpowers c) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    show (c ^ n) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hc2,
      one_zpow]
  have hSN : S ≤ Subgroup.normalizer (Subgroup.zpowers c : Set (MulAut Q)) := by
    intro s hs
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hsc : Commute s c := by
      have := hcS s hs
      calc s * c = s * c * s⁻¹ * s := by group
        _ = c * s := by rw [this]
    exact (hsc.zpow_right n).symm.eq
  have hX := hS.2.1.to_sup_of_normal_right' hz hSN
  have hcA : c ∈ A := hInn ⟨z, rfl⟩
  have heq := hS.eq_of_le (le_sup_left : S ≤ S ⊔ Subgroup.zpowers c)
    (sup_le hS.1 ((Subgroup.zpowers_le).mpr hcA)) hX
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)

theorem oddNorm_of_complement {B O : Subgroup Q} [O.Characteristic] (hOodd : Odd (Nat.card O))
    (hOsolv : Group.IsSolvable ↥O) (hBO : B ⊓ O = ⊥) (hBsup : B ⊔ O = ⊤) (hperf : ⁅B, B⁆ = B)
    {z : Q} (hzB : z ∈ B) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzuniq : ∀ t ∈ B, t * t = 1 → t = 1 ∨ t = z)
    (huniq : ∀ t t' : Q, t * t = 1 → t' * t' = 1 → t ∉ O → t' ∉ O → t'⁻¹ * t ∈ O)
    (hZodd : Odd (Nat.card (Subgroup.center Q)))
    (hCz : O ⊓ Subgroup.centralizer ({z} : Set Q) ≤ Subgroup.centralizer (B : Set Q)) :
    OddNorm Q B := by
  intro A S hInn hS hSB d hd _
  have hzO : z ∉ O := fun h => hz1 (by
    have : z ∈ B ⊓ O := ⟨hzB, h⟩
    rwa [hBO, Subgroup.mem_bot] at this)
  have hSz : ∀ s ∈ S, s z = z := by
    intro s hs
    have hsB := mem_stabilizer_subgroup_iff.mp (hSB hs)
    have hszB : s z ∈ B := hsB ▸ ⟨z, hzB, rfl⟩
    rcases hzuniq (s z) hszB (by rw [← map_mul, hz2, map_one]) with h | h
    · exfalso
      apply hz1
      apply s.injective
      rw [h, map_one]
    · exact h
  have hdz := fix_z hZodd hOodd huniq hS hz2 hzO (conj_mem_of_fix hInn hS hz2 hSz) hd.1
  set C := Subgroup.centralizer ({z} : Set Q) with hCdef
  have hBC : B ≤ C := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hbz : b * z * b⁻¹ ∈ B := B.mul_mem (B.mul_mem hb hzB) (B.inv_mem hb)
    rcases hzuniq _ hbz (by
      calc b * z * b⁻¹ * (b * z * b⁻¹) = b * (z * z) * b⁻¹ := by group
        _ = 1 := by rw [hz2]; group) with h | h
    · exfalso
      apply hz1
      calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
        _ = 1 := by rw [h]; group
    · calc b * z = (b * z * b⁻¹) * b := by group
        _ = z * b := by rw [h]
  have hCeq : C = B ⊔ (O ⊓ C) := by
    refine le_antisymm ?_ (sup_le hBC inf_le_right)
    have h1 := ChiefCount.inf_sup_le hBC (fun b _ => (Subgroup.normalizer_eq_top (H := O)).symm ▸
      Subgroup.mem_top b) (K := C) (J := O)
    rw [hBsup, inf_top_eq] at h1
    rw [inf_comm] at h1
    exact h1
  have hCN : C ≤ Subgroup.normalizer (B : Set Q) := by
    rw [hCeq]
    exact sup_le Subgroup.le_normalizer
      ((inf_comm O C ▸ (hCz.trans (Subgroup.centralizer_le_normalizer _))))
  have hcore : perfectCore C = B := by
    refine le_antisymm (perfectCore_le_of_sup_solvable hBC
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hBC).mpr hCN) hCeq ?_)
      (le_perfectCore_of_perfect hBC hperf)
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : O ⊓ C ≤ O))
  have hCd : C.map d.toMonoidHom = C := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg d h
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hdz] at this
      exact this
    · intro h
      apply d.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hdz]
      exact h
  rw [mem_stabilizer_subgroup_iff, ← hcore, map_perfectCore, hCd]

end CFSG.Quasithin.H13.L3312.NQ
