module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoLeavesCent
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.Quasithin.Vol2.Ch12Sec6L12A6Num
public import CFSG.Quasithin.H13.LocDblOddHeC0
public import CFSG.Sporadic.HeldB.InnerClass

public section

namespace CFSG.Quasithin.H13.K1262Two.HeCent

open CFSG.Open CFSG.Blueprint
open CFSG.Sporadic.Schreier (centralizerIn conjClass centralizerIn_conj)
open CFSG.Sporadic.HeldB
open CFSG.Quasithin.H13.LocDbl.HeC0 (oddIndexBound_heP_cent0)

theorem card_eq_two_pow_of_iso {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    (hiso : quasithinO2QuotientIso Y ↥(alternatingGroup (Fin 6))) :
    ∃ j : ℕ, Nat.card ↥Y = 360 * 2 ^ j := by
  have hY := card_eq_pCore_mul_of_iso hiso
  have hQ : Nat.card ↥(pCoreOf 2 Y) = Nat.card ↥(pCore 2 ↥Y) := by
    rw [pCoreOf]
    exact Subgroup.card_map_of_injective Y.subtype_injective
  obtain ⟨j, hj⟩ := (CFSG.LargeExtraspecial.AS62.isPGroup_pCoreOf 2 Y).exists_card_eq
  exact ⟨j, by rw [hY, hQ.symm.trans hj, mul_comm]⟩

theorem card_sup_facts {X : Type} [Group X] [Finite X] {Y P : Subgroup X}
    (hiso : quasithinO2QuotientIso Y ↥(alternatingGroup (Fin 6))) (hP : IsPGroup 2 ↥P)
    (hPN : P ≤ Subgroup.normalizer (Y : Set X)) :
    45 ∣ Nat.card ↥(Y ⊔ P) ∧ ¬ 7 ∣ Nat.card ↥(Y ⊔ P) ∧ Nat.card ↥P ∣ Nat.card ↥(Y ⊔ P) := by
  obtain ⟨j, hj⟩ := card_eq_two_pow_of_iso hiso
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hPN
  have hinf : Nat.card ↥(Y ⊓ P) ∣ 2 ^ m := hm ▸ Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hinf
  rw [hi, hj, hm] at hprod
  refine ⟨?_, ?_, Subgroup.card_dvd_of_le le_sup_right⟩
  · have h45 : 45 ∣ Nat.card ↥(Y ⊔ P) * 2 ^ i := by
      rw [hprod]
      exact ⟨8 * 2 ^ j * 2 ^ m, by ring⟩
    exact (Nat.Coprime.pow_right i (by norm_num : Nat.Coprime 45 2)).dvd_of_dvd_mul_right h45
  · intro h7
    have h7' : 7 ∣ Nat.card ↥(Y ⊔ P) * 2 ^ i := Dvd.dvd.mul_right h7 _
    rw [hprod] at h7'
    have hp7 : Nat.Prime 7 := by norm_num
    rcases (Nat.Prime.dvd_mul hp7).1 h7' with h | h
    · rcases (Nat.Prime.dvd_mul hp7).1 h with h | h
      · exact absurd h (by norm_num)
      · exact absurd (hp7.dvd_of_dvd_pow h) (by norm_num)
    · exact absurd (hp7.dvd_of_dvd_pow h) (by norm_num)

theorem false_of_sub_cent_involution
    {H : Subgroup (Equiv.Perm (Fin 8330))} {w : Equiv.Perm (Fin 8330)}
    (hHP : H ≤ heP) (hw : w ∈ heP) (hw2 : orderOf w = 2) (hHw : H ≤ Subgroup.centralizer {w})
    (h5 : 5 ∣ Nat.card ↥H) (h512 : 2 ^ 9 ∣ Nat.card ↥H) (h7 : ¬ 7 ∣ Nat.card ↥H)
    (h9 : 9 ∣ Nat.card ↥H) : False := by
  have hle : H ≤ centralizerIn heP w := le_inf hHP hHw
  rcases involution_conj_cases hw hw2 with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · rw [centralizerIn_conj heP hc] at hle
    set Γ := centralizerIn heP (heGenPerm 0) with hΓ
    have hH₂ : H.map (MulAut.conj c⁻¹).toMonoidHom ≤ Γ := by
      rintro _ ⟨h, hh, rfl⟩
      obtain ⟨g, hg, hgh⟩ := hle hh
      have : (MulAut.conj c⁻¹).toMonoidHom h = g := by
        rw [← hgh]
        simp [MulAut.conj_apply, mul_assoc]
      rw [this]
      exact hg
    set H₂ := H.map (MulAut.conj c⁻¹).toMonoidHom with hH₂def
    have hcard₂ : Nat.card ↥H₂ = Nat.card ↥H :=
      Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
    have hcard₃ : Nat.card ↥(H₂.subgroupOf Γ) = Nat.card ↥H := by
      rw [← hcard₂]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₂).toEquiv
    have hidx := Subgroup.index_mul_card (H := H₂.subgroupOf Γ)
    rw [hcard₃, hΓ, card_heP_cent0] at hidx
    have hodd : ¬ 2 ∣ (H₂.subgroupOf Γ).index := by
      obtain ⟨s, hs⟩ := h512
      rw [hs] at hidx
      rintro ⟨t, ht⟩
      rw [ht] at hidx
      have h1024 : 2 ^ 10 ∣ 161280 := ⟨t * s, by rw [← hidx]; ring⟩
      exact absurd h1024 (by norm_num)
    rcases eq_or_ne (H₂.subgroupOf Γ) ⊤ with htop | hne
    · apply h7
      rw [← hcard₃, htop, Subgroup.card_top, hΓ, card_heP_cent0]
      norm_num
    · obtain ⟨N, hN, hd⟩ := oddIndexBound_heP_cent0 _ hodd hne
      rw [hcard₃] at hd
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hN
      subst hN
      exact absurd (h9.trans hd) (by norm_num)
  · rw [centralizerIn_conj heP hc] at hle
    have hd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, card_heP_cent1] at hd
    exact absurd (h5.trans hd) (by norm_num)

end CFSG.Quasithin.H13.K1262Two.HeCent

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint
open CFSG.Sporadic.HeldB (heP heEquivP)

theorem a6CentHe_holds :
    A6CentHe := by
  intro X _ _ ⟨e⟩ Y P u hY hP hPN
  by_contra hlt
  replace hlt : 2 ^ 9 ≤ Nat.card ↥P := not_lt.1 hlt
  obtain ⟨-, hiso, huY, hu2, huc⟩ := hY
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hu2' : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at this
  obtain ⟨v, hvY, hv1, hv2, hvc, hvP⟩ := exists_central_involution_fixed huY hu1 hu2' huc hP hPN
  have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
  have hHv : Y ⊔ P ≤ Subgroup.centralizer {v} := by
    refine sup_le (fun y hy => ?_) (fun p hp => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hvc y hy).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hvP p hp)
  obtain ⟨h45, h7, hPH⟩ := HeCent.card_sup_facts hiso hP hPN
  have h512 : 2 ^ 9 ∣ Nat.card ↥(Y ⊔ P) := by
    obtain ⟨m, hm⟩ := hP.exists_card_eq
    have h9m : 9 ≤ m := by
      have : 2 ^ 9 ≤ 2 ^ m := hm ▸ hlt
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    exact ((Nat.pow_dvd_pow 2 h9m).trans (hm ▸ dvd_rfl)).trans hPH
  set φ : X ≃* heP := e.trans heEquivP with hφ
  set H₁ : Subgroup (Equiv.Perm (Fin 8330)) := ((Y ⊔ P).map φ.toMonoidHom).map heP.subtype with hH₁
  have hcard₁ : Nat.card ↥H₁ = Nat.card ↥(Y ⊔ P) := by
    rw [hH₁, Subgroup.card_map_of_injective heP.subtype_injective,
      Subgroup.card_map_of_injective φ.injective]
  refine HeCent.false_of_sub_cent_involution (H := H₁) (w := ((φ v : heP) : Equiv.Perm (Fin 8330)))
    (Subgroup.map_subtype_le _) (φ v).2 ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hvo
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxv := Subgroup.mem_centralizer_singleton_iff.1 (hHv hx)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have := congrArg (fun z : X => ((φ z : heP) : Equiv.Perm (Fin 8330))) hxv
    simpa using this
  · rw [hcard₁]
    exact (by norm_num : 5 ∣ 45).trans h45
  · rw [hcard₁]
    exact h512
  · rw [hcard₁]
    exact h7
  · rw [hcard₁]
    exact (by norm_num : 9 ∣ 45).trans h45

end CFSG.Quasithin.H13.K1262Two
