module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74N1

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def commDG (x : G) (K : Subgroup G) : Subgroup G :=
  Subgroup.closure {d | ∃ k ∈ K, d = x * k * x⁻¹ * k⁻¹}

theorem commDG_le {x : G} {K : Subgroup G} (hK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) :
    commDG x K ≤ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  exact mul_mem (hK k hk) (inv_mem hk)

theorem commDG_conj {x : G} {K : Subgroup G} (hK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) {d : G}
    (hd : d ∈ commDG x K) : x * d * x⁻¹ ∈ commDG x K := by
  have hle : commDG x K ≤ (commDG x K).comap (MulAut.conj x).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    show x * (x * k * x⁻¹ * k⁻¹) * x⁻¹ ∈ commDG x K
    have e : x * (x * k * x⁻¹ * k⁻¹) * x⁻¹ =
        x * (x * k * x⁻¹) * x⁻¹ * (x * k * x⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.subset_closure ⟨x * k * x⁻¹, hK k hk, rfl⟩
  exact hle hd

theorem exists_mul_of_comm {x : G} (hx : x ^ 5 = 1) {K : Subgroup G} (hK2 : IsPGroup 2 K)
    [Finite K] (hK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) {k : G} (hk : k ∈ K) :
    ∃ d ∈ commDG x K, ∃ c ∈ K, x * c = c * x ∧ k = d * c := by
  have hDK := commDG_le hK
  have hDfin : Finite (commDG x K) := Finite.of_injective (Subgroup.inclusion hDK)
    (Subgroup.inclusion_injective _)
  obtain ⟨m, hm⟩ := (hK2.to_le hDK).exists_card_eq
  set S : Set G := (fun d => d * k) '' (commDG x K : Set G) with hS
  have hSclosed : ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨x * d * x⁻¹ * (x * k * x⁻¹ * k⁻¹), mul_mem (commDG_conj hK hd)
      (Subgroup.subset_closure ⟨k, hk, rfl⟩), ?_⟩
    show x * d * x⁻¹ * (x * k * x⁻¹ * k⁻¹) * k = x * (d * k) * x⁻¹
    group
  have hSfin : S.Finite := (Set.toFinite _).image _
  have hScard : S.ncard = Nat.card (commDG x K) := by
    rw [hS, Set.ncard_image_of_injective _ (fun a b h => mul_right_cancel h)]
    exact (Nat.card_coe_set_eq (commDG x K : Set G)).symm
  have hndvd : ¬ 5 ∣ S.ncard := by
    rw [hScard, hm]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h)
    omega
  obtain ⟨_, ⟨d, hd, rfl⟩, hfix⟩ := exists_fixed_of_not_dvd hx hSclosed hSfin hndvd
  refine ⟨d⁻¹, inv_mem hd, d * k, mul_mem (hDK hd) hk, ?_, by group⟩
  have h1 : x * (d * k) * x⁻¹ = d * k := hfix
  calc x * (d * k) = x * (d * k) * x⁻¹ * x := by group
    _ = d * k * x := by rw [h1]

variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem xe_act (F : FanTree Γ G) (L : ZLab Γ G) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5)
    (k : G) : xe L (Arc.act F k P) = k * xe L P * k⁻¹ := by
  have h0 : valence Γ (P.vert 0) = 5 := valence_vert F P h5 (by norm_num) (by norm_num)
  have h8 : valence Γ (P.vert 8) = 5 := valence_vert F P h5 (by norm_num) (by norm_num)
  unfold xe
  rw [Arc.act_vert, Arc.act_vert, L.equivariant k _ h0, L.equivariant k _ h8]
  group

theorem ballStab_three_comm_commDG (h40 : Fan40 F) (h64 : Fan64 F) (h71a : Fan71a F L)
    (h71c : Fan71c F L) (h72b : Fan72b F L) (h73b : Fan73b F L) {P : Arc Γ 8}
    (h5 : valence Γ (P.vert 4) = 5) {n : G} (hn : n ∈ ballStab Γ G 3 (P.vert 4)) {d : G}
    (hd : d ∈ commDG (xe L P) (nbrStab Γ G (P.vert 4))) : d * n = n * d := by
  have hxn : xe L P * n = n * xe L P := by
    have := ballStab_three_le_calpha h40 h64 h71a h71c h72b h73b h5 hn
    exact Subgroup.mem_centralizer_iff.1
      (show n ∈ nbrStab Γ G (P.vert 4) ⊓ Subgroup.centralizer ({xe L P} : Set G) from this).2
      _ (Set.mem_singleton _)
  have hgen : ∀ k ∈ nbrStab Γ G (P.vert 4),
      Commute (xe L P * k * (xe L P)⁻¹ * k⁻¹) n := by
    intro k hk
    have hkα : k • P.vert 4 = P.vert 4 :=
      MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hk)
    have h5k : valence Γ ((Arc.act F k P).vert 4) = 5 := by
      rw [Arc.act_vert, hkα]; exact h5
    have hnk : n ∈ ballStab Γ G 3 ((Arc.act F k P).vert 4) := by
      rw [Arc.act_vert, hkα]; exact hn
    have hcal := ballStab_three_le_calpha h40 h64 h71a h71c h72b h73b h5k hnk
    have hcomm : xe L (Arc.act F k P) * n = n * xe L (Arc.act F k P) :=
      Subgroup.mem_centralizer_iff.1
        (show n ∈ nbrStab Γ G ((Arc.act F k P).vert 4) ⊓
          Subgroup.centralizer ({xe L (Arc.act F k P)} : Set G) from hcal).2 _
        (Set.mem_singleton _)
    rw [xe_act F L h5 k] at hcomm
    have hA : Commute (xe L P) n := hxn
    have hB : Commute (k * xe L P * k⁻¹) n := hcomm
    have e : xe L P * k * (xe L P)⁻¹ * k⁻¹ = xe L P * (k * xe L P * k⁻¹)⁻¹ := by group
    rw [e]
    exact hA.mul_left hB.inv_left
  have hle : commDG (xe L P) (nbrStab Γ G (P.vert 4)) ≤ Subgroup.centralizer ({n} : Set G) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (hgen k hk).symm
  exact (Subgroup.mem_centralizer_iff.1 (hle hd) n (Set.mem_singleton _)).symm

end P74

end CFSG.Quasithin.Fan86
