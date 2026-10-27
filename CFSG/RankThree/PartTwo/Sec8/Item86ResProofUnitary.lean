module

public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofOrders
public import CFSG.RankThree.PartTwo.Sec21.Item223Of

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Timmesfeld.Orders CFSG.Open
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Unitary

variable {X : Type} [Group X]

open Matrix in
theorem card_projSU_three_zero_dvd : Nat.card (projSU 3 2 0) ∣ 168 := by
  classical
  let F := GaloisField 2 (2 * 0)
  have hF : Nat.card F = 2 := Sec21.natCard_galoisField_two_zero
  let := Fintype.ofFinite F
  have hGL : Nat.card (GL (Fin 3) F) = 168 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_three, Fintype.card_eq_nat_card, hF]
    norm_num
  have hindex : (Subgroup.center (GL (Fin 3) F)).index = Nat.card (ProjGenLinGroup (Fin 3) F) :=
    rfl
  calc Nat.card (projSU 3 2 0) ∣ Nat.card (ProjGenLinGroup (Fin 3) F) :=
        Subgroup.card_subgroup_dvd_card _
    _ ∣ Nat.card (GL (Fin 3) F) := hindex ▸ (Subgroup.center (GL (Fin 3) F)).index_dvd_card
    _ = 168 := hGL

theorem false_of_isUnitaryTwo_zero {N : ℕ} {Z : ℕ → Prop} (hP : Profile (Nat.card X) N Z)
    (hN : 9 ≤ N) (h : IsUnitaryTwo X 0) : False := by
  rcases h with he | ⟨K, _, _, hK, -⟩
  · obtain ⟨e⟩ := he
    obtain ⟨r, -, hr⟩ := hP.two
    have h1 : 2 ^ N ∣ 168 := by
      have h0 : 2 ^ N ∣ Nat.card X := Dvd.intro r hr.symm
      rw [Nat.card_congr e.toEquiv] at h0
      exact h0.trans card_projSU_three_zero_dvd
    have h2 : 2 ^ 9 ∣ 168 := (pow_dvd_pow 2 hN).trans h1
    norm_num at h2
  · have : 1 < Nat.card K := Finite.one_lt_card
    simp at hK
    omega

theorem not_isUnitaryTwo_of_profile {N : ℕ} {Z : ℕ → Prop} (hP : Profile (Nat.card X) N Z)
    (hle : ∀ k, Z k → k ≤ N) (hN : 9 ≤ N) (g : ℕ) : ¬ IsUnitaryTwo X g := by
  intro h
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · exact false_of_isUnitaryTwo_zero hP hN h
  have hU : UnitarySig X g := by
    rcases h with he | hS
    · obtain ⟨e⟩ := he
      exact unitarySig_of_projSU hg e
    · exact unitarySig_of_isoSUThree hg hS
  have hN' := two_eq hU.profile hP
  have h' := (z_iff hU.profile hP (k := 6 * g) (by omega) (by omega)).mp hU.top
  have := hle _ h'
  omega

theorem SigD4.not_isUnitaryTwo {p : ℕ} (h : SigD4 X p) (hp : 1 ≤ p) (g : ℕ) :
    ¬ IsUnitaryTwo X g :=
  not_isUnitaryTwo_of_profile h.profile h.le (by omega) g

theorem SigG2.not_isUnitaryTwo {p : ℕ} (h : SigG2 X p) (hp : 1 ≤ p) (g : ℕ) :
    ¬ IsUnitaryTwo X g :=
  not_isUnitaryTwo_of_profile h.profile h.le (by omega) g

theorem SigF4.not_isUnitaryTwo {p : ℕ} (h : SigF4 X p) (hp : 1 ≤ p) (g : ℕ) :
    ¬ IsUnitaryTwo X g :=
  not_isUnitaryTwo_of_profile h.profile h.le (by omega) g

theorem SigSp4.not_isUnitaryTwo {p : ℕ} (h : SigSp4 X p) (hp : 1 ≤ p) (g : ℕ) :
    ¬ IsUnitaryTwo X g :=
  not_isUnitaryTwo_of_profile h.profile h.le (by omega) g

theorem SigF4.false_of_isUnitaryTwo {p g : ℕ} (h : SigF4 X p) (hp : 1 ≤ p)
    (hU : IsUnitaryTwo X g) : False :=
  h.not_isUnitaryTwo hp g hU

end Unitary

section Centralize

variable {G : Type} [Group G] [Finite G]

theorem card_projSL_two_eq {g : ℕ} (hg : 1 ≤ g) :
    ∃ r, Odd r ∧ Nat.card (projSL 2 (GaloisField 2 g)) = 2 ^ g * r :=
  ⟨_, odd_pow_sub_one hg (by norm_num), Sec21.card_projSL_two g hg⟩

theorem card_imageModTheta_self (L : Subgroup G) :
    Nat.card (imageModTheta L L) = Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
  have h : imageModTheta L L = ⊤ := by
    rw [imageModTheta, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rw [h, Subgroup.card_top]


theorem false_of_isGammaIndex_of_centralizes {A L : Subgroup G} {x : G} {m : ℕ}
    (h : IsGammaIndex A L x m) (hL : Group.IsPerfect L)
    (hx : L ≤ Subgroup.centralizer ({x} : Set G)) : False := by
  have hm : 1 ≤ m := one_le_of_isGammaIndex h
  have htype := isGammaType_of_isGammaIndex h
  have hK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({x} : Set G)) = L := by
    rw [inf_eq_left.mpr hx]
    exact inSubgroup_perfectResidual_of_isPerfect hL
  have hcard := card_imageModTheta_self L
  obtain ⟨-, -, -, ⟨k, hk, hkm, he, hSU⟩ | ⟨-, ⟨eL⟩⟩⟩ := h
  ·
    rw [hK] at hSU
    have hF := sigF4_of_reeF4 hm ⟨k, hk, hkm, he⟩
    have hU := unitarySig_of_isoSUThree (by omega) hSU
    have := two_eq (profile_of_eq hU.profile hcard.symm) hF.profile
    omega
  ·
    rw [hK] at eL
    obtain ⟨r, hr, hcL⟩ := card_projSL_two_eq (g := 3 * m) (by omega)
    have h2 : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = 2 ^ (3 * m) * r := by
      rw [← hcard, Nat.card_congr eL.toEquiv, hcL]
    rcases sig_of_isGammaType hm htype with hS | hS | hS | hS | hS
    all_goals
      obtain ⟨r', hr', h'⟩ := hS.profile.two
      have := eq_of_two_pow_mul_odd hr' hr (h'.symm.trans h2)
      omega

end Centralize

section ThreePart

variable {G : Type} [Group G] [Finite G]

theorem card_imageModTheta_dvd {L K : Subgroup G} (hKL : K ≤ L) :
    Nat.card (imageModTheta L K) ∣ Nat.card K := by
  have h := Subgroup.card_map_dvd (K.subgroupOf L) (QuotientGroup.mk' (aschbacherSolvableCore 3 L))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv] at h

theorem pow_three_dvd_card_imageModTheta {X K : Subgroup G} (hKX : K ≤ X) {k : ℕ}
    (hk : 3 ^ k ∣ Nat.card K) : 3 ^ k ∣ Nat.card (imageModTheta X K) := by
  set φ : K.subgroupOf X →* X ⧸ aschbacherSolvableCore 3 X :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp (K.subgroupOf X).subtype with hφ
  have hrange : φ.range = imageModTheta X K := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : Nat.card φ.ker ∣ Nat.card (aschbacherSolvableCore 3 X) := by
    have hle : φ.ker.map (K.subgroupOf X).subtype ≤ aschbacherSolvableCore 3 X := by
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy
      rw [← QuotientGroup.ker_mk' (aschbacherSolvableCore 3 X), MonoidHom.mem_ker]
      exact hy
    have h1 := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (K.subgroupOf X).subtype_injective] at h1
  have hcard : Nat.card φ.ker * Nat.card (imageModTheta X K) = Nat.card K := by
    rw [← hrange, Subgroup.card_ker_mul_card_range,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv]
  have hcop : Nat.Coprime (3 ^ k) (Nat.card φ.ker) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact fun h3 => KFacts.not_three_dvd_card_aschbacherSolvableCore X (h3.trans hker)
  rw [← hcard] at hk
  exact hcop.dvd_of_dvd_mul_left hk

theorem isPerfect_inSubgroup_perfectResidual' (Y : Subgroup G) :
    Group.IsPerfect (inSubgroup perfectResidual Y) := by
  have := (perfect_residual_characterization (G := Y)).2.2.1
  exact Group.IsPerfect.map Y.subtype

theorem false_of_isoSUThree_le_projSL {L X K M : Subgroup G} (hKL : K ≤ L) (hKM : K ≤ M)
    (hMX : M ≤ X) {n : ℕ} (hn : Odd n) (hSU : IsoSUThree (imageModTheta L K) (2 ^ (3 * n)))
    (hL2 : Nonempty (imageModTheta X M ≃* projSL 2 (GaloisField 2 (3 * n)))) : False := by
  have hn1 : 1 ≤ n := hn.pos
  set Q := 2 ^ (3 * n) with hQ
  have hQ2 : 1 ≤ Q ^ 2 - 1 := by
    have : 4 ≤ Q ^ 2 := by
      have h8 : 2 ≤ Q := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ Q := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    omega
  set v := padicValNat 3 (Q ^ 2 - 1) with hv
  have hSUcard : Nat.card (imageModTheta L K) = Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hSU
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (3 * n) F :=
      ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.card_unitarySU_three hU
  have h3Q : 3 ∣ Q ^ 3 + 1 := by
    have h1 := KFacts.three_dvd_two_pow_three_mul_add_one hn
    have h2 : Q + 1 ∣ Q ^ 3 + 1 := add_one_dvd_pow_add_one Q (by decide)
    exact h1.trans h2
  have hvdvd : 3 ^ v ∣ Q ^ 2 - 1 := pow_padicValNat_dvd
  have hSU3 : 3 ^ (v + 1) ∣ Nat.card (imageModTheta L K) := by
    rw [hSUcard, pow_succ, mul_assoc]
    exact Dvd.dvd.mul_left (mul_dvd_mul hvdvd h3Q) _
  have hK3 : 3 ^ (v + 1) ∣ Nat.card K := hSU3.trans (card_imageModTheta_dvd hKL)
  have hKX3 := pow_three_dvd_card_imageModTheta (hKM.trans hMX) hK3
  have hle : imageModTheta X K ≤ imageModTheta X M := by
    apply Subgroup.map_mono
    intro x hx
    exact hKM hx
  have hM3 : 3 ^ (v + 1) ∣ Nat.card (imageModTheta X M) :=
    hKX3.trans (Subgroup.card_dvd_of_le hle)
  obtain ⟨eM⟩ := hL2
  have hMcard : Nat.card (imageModTheta X M) = Q * (Q ^ 2 - 1) := by
    rw [Nat.card_congr eM.toEquiv]
    exact Sec21.card_projSL_two (3 * n) (by omega)
  rw [hMcard] at hM3
  have hcop : Nat.Coprime (3 ^ (v + 1)) Q := by
    apply Nat.Coprime.pow_left
    rw [hQ]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have h4 : 3 ^ (v + 1) ∣ Q ^ 2 - 1 := hcop.dvd_of_dvd_mul_left hM3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h5 := (padicValNat_dvd_iff_le (by omega)).mp h4
  omega

end ThreePart

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
