module

public import CFSG.RankThree.GF2n.Tim79aSec23Tilde
public import CFSG.RankThree.GF2n.Tim79aSec22Ti
public import CFSG.RankThree.GF2n.Tim79aSec23Dich

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem card_barOf_V_eq_two_or_four_le :
    Nat.card (barOf V H V) = 2 ∨ 4 ≤ Nat.card (barOf V H V) := by
  have hP : IsPGroup 2 (barOf V H V) := fun x => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using (hc.barOf_V_sq x.2)⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hne : Nat.card (barOf V H V) ≠ 1 := by
    intro h1
    obtain ⟨d, hdV, hdW⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
    have hdH : d ∈ H := hc.V_le_H hdV
    have hd1 : piBar V H ⟨d, hdH⟩ ≠ 1 := fun h => hdW ((piBar_eq_one_iff _).1 h)
    have hdm : piBar V H ⟨d, hdH⟩ ∈ barOf V H V := mem_barOf_iff.mpr ⟨_, hdV, rfl⟩
    have := Nat.card_eq_one_iff_unique.mp h1
    exact hd1 (congrArg Subtype.val (this.1.elim ⟨_, hdm⟩ 1))
  rw [hk] at hne ⊢
  rcases k with _ | _ | k
  · exact absurd rfl hne
  · left; norm_num
  · right
    have : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
    rw [this]
    have := Nat.one_le_two_pow (n := k)
    omega

theorem card_barOf_V_eq_two_of_not_meetsSq (hd : Sec23Data V H)
    (hns : ¬ ∃ u ∈ Dtilde V H, ∃ v ∈ Dtilde V H, u ≠ v ∧ Commute u v ∧ u * v ∈ Dtilde V H) :
    Nat.card (barOf V H V) = 2 := by
  rcases hc.card_barOf_V_eq_two_or_four_le with h | h
  · exact h
  · exact absurd (hc.tilde_meetsSq hd h) hns

theorem sup_eq_H_of_noncommute
    (hdeg : ∀ d ∈ Dy V H, ∀ e ∈ Dy V H, orderOf (d * e) ≠ 4)
    {e' : ↥H} (he : piBar V H e' ∈ dbarOf V H) {v : Hbar V H} (hv : v ∈ barOf V H V)
    (hne : v * piBar V H e' ≠ piBar V H e' * v) :
    P ⊔ Subgroup.closure {(e' : G)} = H := by
  set K : Subgroup G := P ⊔ Subgroup.closure {(e' : G)} with hK
  have he'K : (e' : G) ∈ K := Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
  have hKH : K ≤ H := sup_le hc.PleH ((Subgroup.closure_le _).2 (by simpa using e'.2))
  by_contra hKne
  have hKlt : K < H := lt_of_le_of_ne hKH hKne
  have hPK : P ≤ K := le_sup_left
  have hO2 : inSubgroup (pCore 2) K ≠ ⊥ := by
    set S : Subgroup G := inSubgroup (pCore 2) H ⊓ K with hS
    have hSK : S ≤ K := inf_le_right
    have hSn : K ≤ Subgroup.normalizer (S : Set G) := fun k hk =>
      mem_normalizer_inf ((inSubgroup_pCore_two H).2.2 (hKH hk)) (Subgroup.le_normalizer hk)
    have hS2 : IsPGroup 2 S := (inSubgroup_pCore_two H).1.to_le inf_le_left
    have hSO : S ≤ inSubgroup (pCore 2) K := le_inSubgroup_pCore hSK hSn hS2
    intro hbot
    apply hc.eOf_inf_V_ne_bot
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxV⟩ := Subgroup.mem_inf.mp hx
    have : x ∈ S := ⟨(eOf_le_pCore H) hxE, hPK (hc.V_le_P hxV)⟩
    have := hSO this
    rw [hbot] at this
    exact this
  have hVO : V ≤ inSubgroup (pCore 2) K := hc.min K hPK hO2 hKlt
  have hVe : conjSubgroup (e' : G) V ≤ inSubgroup (pCore 2) K := by
    have hn := mem_normalizer_iff_conjSubgroup_eq.mp ((inSubgroup_pCore_two K).2.2 he'K)
    rw [← hn]
    exact Subgroup.map_mono hVO
  have hVVe : IsPGroup 2 ↥(V ⊔ conjSubgroup (e' : G) V) :=
    (inSubgroup_pCore_two K).1.to_le (sup_le hVO hVe)
  have hVH := hc.V_le_H
  have hUH : conjSubgroup (e' : G) V ≤ H := conjSubgroup_le_of_le_of_mem hVH e'.2
  have hW2 : IsPGroup 2 (wOf V H) :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian
  have h2g : IsPGroup 2 ↥(V ⊔ conjSubgroup (e' : G) V ⊔ wOf V H) :=
    hVVe.to_sup_of_normal_right' hW2 (fun k hk => H_le_normalizer_wOf V H (sup_le hVH hUH hk))
  have hcomm := hc.commute_of_isPGroup_sup_wOf e'.2 h2g
  have hv1 : v ≠ 1 := fun h => hne (by rw [h]; simp)
  obtain ⟨u₀', hu₀V, hu₀v⟩ := mem_barOf_iff.mp hv
  have hv₂ : (e' : G) * (u₀' : G) * (e' : G)⁻¹ ∈ conjSubgroup (e' : G) V := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hu₀V
  have hc2 := hcomm (u₀' : G) hu₀V _ hv₂
  have hc2' : u₀' * (e' * u₀' * e'⁻¹) = (e' * u₀' * e'⁻¹) * u₀' :=
    Subtype.ext (by simpa using hc2)
  have hc3 := congrArg (piBar V H) hc2'
  simp only [map_mul, map_inv, hu₀v] at hc3
  have heX : piBar V H e' ∈ barOf V H (xOf V H) := hc.dbarOf_subset_barOf_xOf he
  have hvX : v ∈ barOf V H (xOf V H) := barOf_V_le V H hv
  set e : Xbar V H := ⟨piBar V H e', heX⟩ with he_def
  set v' : Xbar V H := ⟨v, hvX⟩ with hv'_def
  have heD : e ∈ Dy V H := he
  have hv'D : v' ∈ Dy V H := hc.barOf_V_subset_dbarOf hv hv1
  have he2 : e * e = 1 := by
    rw [← sq]
    have := hc.Dy_root.1 e heD
    rw [← this]; exact pow_orderOf_eq_one e
  have hv'2 : v' * v' = 1 := by
    rw [← sq]
    have := hc.Dy_root.1 v' hv'D
    rw [← this]; exact pow_orderOf_eq_one v'
  have hne' : v' * e ≠ e * v' := fun h => hne (congrArg Subtype.val h)
  have hcomm' : v' * (e * v' * e⁻¹) = (e * v' * e⁻¹) * v' :=
    Subtype.ext (by simpa [he_def, hv'_def] using hc3)
  have hw2 : (e * v' * e⁻¹) * (e * v' * e⁻¹) = 1 := by
    calc (e * v' * e⁻¹) * (e * v' * e⁻¹) = e * (v' * v') * e⁻¹ := by group
      _ = 1 := by rw [hv'2]; group
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have hsq : (v' * e) ^ 2 = v' * (e * v' * e⁻¹) := by
    rw [sq]
    calc v' * e * (v' * e) = v' * (e * v' * e⁻¹) * (e * e) := by group
      _ = v' * (e * v' * e⁻¹) := by rw [he2, mul_one]
  have h4 : (v' * e) ^ 4 = 1 := by
    have : (v' * e) ^ 4 = ((v' * e) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [this, hsq, sq]
    calc v' * (e * v' * e⁻¹) * (v' * (e * v' * e⁻¹))
        = v' * v' * ((e * v' * e⁻¹) * (e * v' * e⁻¹)) := by
          rw [mul_assoc v' _ _, ← mul_assoc _ v' _, ← hcomm']; group
      _ = 1 := by rw [hv'2, hw2, mul_one]
  have hdvd : orderOf (v' * e) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  rcases hc.Dy_root.2.1 v' hv'D e heD with h2o | h4o | hodd
  · apply hne'
    have h1 : (v' * e) ^ 2 = 1 := by rw [← h2o]; exact pow_orderOf_eq_one _
    rw [sq] at h1
    calc v' * e = (v' * e)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = e * v' := by rw [mul_inv_rev, heinv, inv_eq_of_mul_eq_one_right hv'2]
  · exact hdeg v' hv'D e heD h4o
  · have h1 : orderOf (v' * e) = 1 := by
      have h2 : orderOf (v' * e) ∣ 2 ^ 2 := by simpa using hdvd
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
      rw [hk'] at hodd ⊢
      rcases k with _ | k
      · rfl
      · exact absurd hodd
          (by rw [Nat.not_odd_iff_even]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩)
    apply hne'
    have h3 : v' * e = 1 := orderOf_eq_one_iff.mp h1
    calc v' * e = 1 := h3
      _ = e * v' := by
        have : e = v'⁻¹ := eq_inv_of_mul_eq_one_right h3
        rw [this, inv_eq_of_mul_eq_one_right hv'2]; exact hv'2.symm

end MinCex

@[expose] def cenGen {Y : Type} [Group Y] (D : Set Y) (d : Y) : Subgroup Y :=
  Subgroup.closure (D ∩ (Subgroup.centralizer ({d} : Set Y) : Set Y))

@[expose] def NoSqE1 {Y : Type} [Group Y] (D : Set Y) : Prop :=
  ∀ d ∈ D, inSubgroup (pCore 2) (cenGen D d) ≤ Subgroup.zpowers d ⊔ Subgroup.center Y

end CFSG.RankThree.GF2n.Tim79a
