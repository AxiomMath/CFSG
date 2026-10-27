module

public import CFSG.RankThree.S4Free.Stellmacher33Dihedral
public import CFSG.RankThree.S4Free.StellmacherL24
public import CFSG.RankThree.S4Free.StellmacherHosts

public section

namespace CFSG.RankThree.S4Free.Stell33

open Subgroup

section Dihedral

variable {n : ℕ}

theorem eq_zero_of_two_mul_eq_zero (hn : Odd n) {a : ZMod n} (h : 2 * a = 0) : a = 0 := by
  have hu : IsUnit (2 : ZMod n) := by
    have := (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hn)).isUnit
    rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
  exact hu.mul_right_eq_zero.mp h

theorem exists_eq_sr (hn : Odd n) {x : DihedralGroup n} (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ i, x = DihedralGroup.sr i := by
  rcases x with i | i
  · exfalso
    apply hx1
    rw [DihedralGroup.r_mul_r, ← DihedralGroup.r_zero] at hx
    have hi : 2 * i = 0 := by rw [two_mul]; exact DihedralGroup.r.inj hx
    rw [eq_zero_of_two_mul_eq_zero hn hi, DihedralGroup.r_zero]
  · exact ⟨i, rfl⟩

theorem sr_eq_sr_of_commute (hn : Odd n) {i j : ZMod n}
    (h : DihedralGroup.sr i * DihedralGroup.sr j = DihedralGroup.sr j * DihedralGroup.sr i) :
    i = j := by
  rw [DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_sr] at h
  have h' : j - i = i - j := DihedralGroup.r.inj h
  have h2 : 2 * (j - i) = 0 := by linear_combination h'
  exact (sub_eq_zero.mp (eq_zero_of_two_mul_eq_zero hn h2)).symm

end Dihedral

variable {H : Type*} [Group H]

abbrev oTwoSub (L : Subgroup H) : Subgroup H := (oTwo ↥L).map L.subtype

theorem oTwoSub_le (L : Subgroup H) : oTwoSub L ≤ L := map_subtype_le _

theorem isPGroup_oTwoSub [Finite H] (L : Subgroup H) : IsPGroup 2 (oTwoSub L) :=
  (Stell.oTwo_isPGroup ↥L).map _

theorem le_normalizer_oTwoSub (L : Subgroup H) : L ≤ normalizer (oTwoSub L : Set H) := by
  refine le_normalizer_of_forall_conj_mem (fun g hg x hx => ?_)
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, (inferInstance : (oTwo ↥L).Normal).conj_mem _ hy _, rfl⟩

theorem oTwoSub_le_of_relIndex [Finite H] {T L : Subgroup H} (hT : IsPGroup 2 T)
    (hTL : ¬ 2 ∣ T.relIndex L) : oTwoSub L ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (T.subgroupOf L) := hT.comap_subtype
  have hle : oTwo ↥L ≤ T.subgroupOf L := by
    have h1 := (Stell.oTwo_isPGroup ↥L).le_sylow_of_normal
      (hP.toSylow (show ¬ 2 ∣ (T.subgroupOf L).index from hTL))
    rwa [IsPGroup.toSylow_coe] at h1
  calc oTwoSub L ≤ (T.subgroupOf L).map L.subtype := map_mono hle
    _ = T ⊓ L := subgroupOf_map_subtype T L
    _ ≤ T := inf_le_left

theorem le_oTwoSub [Finite H] {L N : Subgroup H} (hNL : N ≤ L)
    (hN : L ≤ normalizer (N : Set H)) (hp : IsPGroup 2 N) : N ≤ oTwoSub L := by
  haveI : (N.subgroupOf L).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.mp (hN g.2) n).mp hn⟩
  have h2 := Stell.le_oTwo (K := N.subgroupOf L) hp.comap_subtype
  intro x hx
  exact ⟨⟨x, hNL hx⟩, h2 (show (⟨x, hNL hx⟩ : ↥L) ∈ N.subgroupOf L from hx), rfl⟩

theorem exists_lcfg [Finite H] (hS3 : IsSym3Free H) {T M Wh L : Subgroup H} (hT : IsPGroup 2 T)
    (hMW : M ≤ normalizer (Wh : Set H)) (hTW : T ≤ normalizer (Wh : Set H))
    (hWel : CFSG.Open.IsElemAbelian 2 Wh) (hL : Stell.IsL24 T M Wh L) :
    ∃ u, LCfg L Wh (oTwoSub L) u ∧ ¬ 3 ∣ Nat.card L ∧ ¬ IsPGroup 2 L := by
  obtain ⟨r, s, hr, hr2, hs, ⟨e⟩⟩ := hL.dihedral
  have hodd : Odd (r ^ s) := (hr.odd_of_ne_two hr2).pow
  have hr3' : 3 ≤ r := by have := hr.two_le; omega
  have hn3 : 3 ≤ r ^ s := le_trans hr3' (le_self_pow (by omega) (by omega))
  set n := r ^ s with hn
  set P := oTwoSub L with hP
  let π : ↥L →* DihedralGroup n := e.toMonoidHom.comp (QuotientGroup.mk' (oTwo ↥L))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπ1 : ∀ y : ↥L, π y = 1 ↔ (y : H) ∈ P := by
    intro y
    change e (QuotientGroup.mk y) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    exact (mem_map_iff_mem L.subtype_injective).symm
  have hr1 : (DihedralGroup.r 1 : DihedralGroup n) ≠ 1 := by
    intro h1
    rw [← DihedralGroup.r_zero] at h1
    have := ZMod.one_eq_zero_iff.mp (DihedralGroup.r.inj h1)
    omega
  have hWP : ¬ Wh ≤ P := by
    intro hle
    obtain ⟨x, hxL, hxM⟩ := Set.not_subset.mp hL.not_le
    have hxW : Wh.map (MulAut.conj x).toMonoidHom ≤ P := by
      rintro _ ⟨b, hb, rfl⟩
      exact (mem_normalizer_iff.mp (le_normalizer_oTwoSub L hxL) b).mp (hle hb)
    have hLP : L ≤ P := (hL.sup_conj x hxL hxM).ge.trans (sup_le hle hxW)
    obtain ⟨y, hy⟩ := hπs (DihedralGroup.r 1)
    exact hr1 (by rw [← hy]; exact (hπ1 y).mpr (hLP y.2))
  obtain ⟨w₀, hw₀W, hw₀P⟩ := Set.not_subset.mp hWP
  have hw₀L := hL.le hw₀W
  have hWsq : ∀ w ∈ Wh, w * w = 1 := fun w hw => by rw [← sq]; exact hWel.2 w hw
  have hWcomm : ∀ w₁ ∈ Wh, ∀ w₂ ∈ Wh, w₁ * w₂ = w₂ * w₁ := fun w₁ h₁ w₂ h₂ =>
    congrArg Subtype.val (hWel.1.is_comm.comm ⟨w₁, h₁⟩ ⟨w₂, h₂⟩)
  have hrefl : ∀ w (hw : w ∈ Wh), w ∉ P → ∃ i, π ⟨w, hL.le hw⟩ = DihedralGroup.sr i := by
    intro w hw hwP
    refine exists_eq_sr hodd ?_ (fun h1 => hwP ((hπ1 _).mp h1))
    rw [← map_mul]
    have : (⟨w, hL.le hw⟩ : ↥L) * ⟨w, hL.le hw⟩ = 1 := Subtype.ext (hWsq w hw)
    rw [this, map_one]
  have hsame : ∀ w (hw : w ∈ Wh), w ∉ P → π ⟨w, hL.le hw⟩ = π ⟨w₀, hw₀L⟩ := by
    intro w hw hwP
    obtain ⟨i, hi⟩ := hrefl w hw hwP
    obtain ⟨j, hj⟩ := hrefl w₀ hw₀W hw₀P
    rw [hi, hj]
    congr 1
    apply sr_eq_sr_of_commute hodd
    rw [← hi, ← hj, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hWcomm w hw w₀ hw₀W)
  obtain ⟨i₀, hi₀⟩ := hrefl w₀ hw₀W hw₀P
  have hidx : (Wh ⊓ P).relIndex Wh = 2 := by
    rw [relIndex, index_eq_two_iff]
    refine ⟨⟨w₀, hw₀W⟩, fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    have hbW : (b : H) ∈ Wh := b.2
    by_cases hbP : (b : H) ∈ P
    · refine Or.inr ⟨⟨hbW, hbP⟩, fun hc => hw₀P ?_⟩
      have hc' : (b : H) * w₀ ∈ P := (mem_inf.mp hc).2
      have := P.mul_mem (P.inv_mem hbP) hc'
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨⟨mul_mem hbW hw₀W, ?_⟩, fun hc => hbP (mem_inf.mp hc).2⟩
      have h1 := hsame b hbW hbP
      apply (hπ1 ⟨(b : H) * w₀, L.mul_mem (hL.le hbW) hw₀L⟩).mp
      have e1 : (⟨(b : H) * w₀, L.mul_mem (hL.le hbW) hw₀L⟩ : ↥L) =
          ⟨b, hL.le hbW⟩ * ⟨w₀, hw₀L⟩ := rfl
      rw [e1, map_mul, h1, hi₀, DihedralGroup.sr_mul_self]
  obtain ⟨u', hu'⟩ := hπs (DihedralGroup.sr (i₀ + 1))
  have huL : (u' : H) ∈ L := u'.2
  have huu : (u' : H) * u' ∈ P := by
    apply (hπ1 (u' * u')).mp
    rw [map_mul, hu', DihedralGroup.sr_mul_self]
  have huN : (u' : H) ∉ normalizer (Wh : Set H) := by
    intro hN
    have hcW : (u' : H) * w₀ * (u' : H)⁻¹ ∈ Wh := (mem_normalizer_iff.mp hN w₀).mp hw₀W
    have hcP : (u' : H) * w₀ * (u' : H)⁻¹ ∉ P := fun hc =>
      hw₀P ((mem_normalizer_iff.mp (le_normalizer_oTwoSub L huL) w₀).mpr hc)
    have h1 := hsame _ hcW hcP
    have e1 : (⟨(u' : H) * w₀ * (u' : H)⁻¹, hL.le hcW⟩ : ↥L) = u' * ⟨w₀, hw₀L⟩ * u'⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv, hu', hi₀, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
      DihedralGroup.r_mul_sr] at h1
    have h2 := DihedralGroup.sr.inj h1
    have h3 : ((2 : ℕ) : ZMod n) = 0 := by push_cast; linear_combination h2
    have h4 := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 n).mp h3)
    omega
  have hr3 : r ≠ 3 := by
    rintro rfl
    have hD : IsSym3Free (DihedralGroup (3 ^ s)) :=
      ((hS3.subgroup L).quotient (oTwo ↥L)).of_mulEquiv e
    have hs1 : 3 ^ (s - 1) * 3 = 3 ^ s := by rw [← pow_succ, Nat.sub_add_cancel hs]
    set y : DihedralGroup (3 ^ s) := DihedralGroup.r ((3 ^ (s - 1) : ℕ) : ZMod (3 ^ s)) with hy
    have hy3 : y ^ 3 = 1 := by
      rw [hy, DihedralGroup.r_pow, ← DihedralGroup.r_zero]
      congr 1
      rw [← Nat.cast_mul, hs1, ZMod.natCast_self]
    have hay : DihedralGroup.sr 0 * y * (DihedralGroup.sr 0)⁻¹ = y⁻¹ := by
      rw [hy, DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
        DihedralGroup.inv_r]
      congr 1
      ring
    have hy1 := hD.eq_one_of_inv (by rw [sq, DihedralGroup.sr_mul_self]) hy3 hay
    rw [hy, ← DihedralGroup.r_zero] at hy1
    have h5 := (ZMod.natCast_eq_zero_iff _ _).mp (DihedralGroup.r.inj hy1)
    have h6 := Nat.le_of_dvd (pow_pos (by norm_num) _) h5
    have h7 : 3 ^ (s - 1) < 3 ^ s := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (Stell.oTwo_isPGroup ↥L)
  have hcardL : Nat.card L = 2 * n * 2 ^ a := by
    rw [card_eq_card_quotient_mul_card_subgroup (oTwo ↥L), Nat.card_congr e.toEquiv,
      DihedralGroup.nat_card, ha]
  have h3L : ¬ 3 ∣ Nat.card L := by
    rw [hcardL]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
      · omega
      · exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp
          (Nat.prime_three.dvd_of_dvd_pow h3)).symm
    · have := Nat.le_of_dvd (by norm_num) (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
  have hnp : ¬ IsPGroup 2 L := by
    intro hp
    obtain ⟨k, hk⟩ := (hp.of_surjective π hπs) (DihedralGroup.r 1)
    have hdvd : n ∣ 2 ^ k := by
      have := orderOf_dvd_of_pow_eq_one hk
      rwa [DihedralGroup.orderOf_r_one] at this
    have := (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)).eq_one_of_dvd hdvd
    omega
  refine ⟨u', ⟨⟨hL.le, hWel, oTwoSub_le L, le_normalizer_oTwoSub L, isPGroup_oTwoSub L,
    (oTwoSub_le_of_relIndex hT hL.not_dvd_relIndex).trans hTW, huL, huu,
    hL.sup_conj _ huL (fun hM => huN (hMW hM))⟩, hidx⟩, h3L, hnp⟩

end CFSG.RankThree.S4Free.Stell33
