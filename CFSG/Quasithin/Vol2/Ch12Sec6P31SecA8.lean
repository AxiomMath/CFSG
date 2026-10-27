module

public import CFSG.Quasithin.Vol2.Ch12Sec6L19c

public section

namespace CFSG.Quasithin.H13.P31Sec

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126 S126L19a Equiv
open scoped IsMulCommutative

theorem eq_top_of_dvd_card_A8 {D : Subgroup ↥(alternatingGroup (Fin 8))}
    (h : 2880 ∣ Nat.card D) : D = ⊤ := by
  have hcard : Nat.card ↥(alternatingGroup (Fin 8)) = 20160 := S126L1a.card_A8
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hdvd : Nat.card D ∣ 20160 := hcard ▸ Subgroup.card_subgroup_dvd_card D
  obtain ⟨k, hk⟩ := h
  have hk7 : k ∣ 7 := by
    have : 2880 * k ∣ 2880 * 7 := by rw [← hk]; exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  rcases (Nat.dvd_prime (by norm_num)).1 hk7 with rfl | rfl
  ·
    exfalso
    have hind : D.index = 7 := by
      have := Subgroup.card_mul_index D
      rw [hcard, hk] at this
      omega
    let φ := MulAction.toPermHom ↥(alternatingGroup (Fin 8)) (↥(alternatingGroup (Fin 8)) ⧸ D)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h0 | h0
    · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 h0
      have hle := Nat.card_le_card_of_injective φ hinj
      rw [hcard, Nat.card_perm] at hle
      have h7 : Nat.card (↥(alternatingGroup (Fin 8)) ⧸ D) = 7 := hind
      rw [h7] at hle
      norm_num [Nat.factorial] at hle
    · have hall : ∀ g : ↥(alternatingGroup (Fin 8)), g ∈ D := by
        intro g
        have hg : φ g = 1 := by
          have : g ∈ φ.ker := h0 ▸ Subgroup.mem_top g
          exact this
        have h1 : (QuotientGroup.mk g : ↥(alternatingGroup (Fin 8)) ⧸ D) = QuotientGroup.mk 1 := by
          have h2 : (φ g) (QuotientGroup.mk (1 : ↥(alternatingGroup (Fin 8)))) =
              QuotientGroup.mk (1 : ↥(alternatingGroup (Fin 8))) := by
            rw [hg]
            rfl
          have h3 : (φ g) (QuotientGroup.mk (1 : ↥(alternatingGroup (Fin 8)))) =
              (QuotientGroup.mk g : ↥(alternatingGroup (Fin 8)) ⧸ D) := by
            show g • (QuotientGroup.mk (1 : ↥(alternatingGroup (Fin 8))) :
              ↥(alternatingGroup (Fin 8)) ⧸ D) = _
            rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
          rw [← h3]
          exact h2
        rw [QuotientGroup.eq] at h1
        simpa using h1
      have htop : D = ⊤ := eq_top_iff.2 fun g _ => hall g
      rw [htop, Subgroup.card_top, hcard] at hk
      omega
  ·
    refine Subgroup.eq_top_of_card_eq D ?_
    rw [hcard, hk]

section Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem psi_image_eq_top (F : Frame126 T L V) (hH : Hyp126 G T L V) {J : Subgroup G} (hJL : J ≤ L)
    (hJT : T ≤ Subgroup.normalizer (J : Set G))
    (h45 : 45 ∣ Nat.card ↥((J.subgroupOf L).map (psi F hH))) :
    (J.subgroupOf L).map (psi F hH) = ⊤ := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  set Jb : Subgroup ↥(alternatingGroup (Fin 8)) := (J.subgroupOf L).map (psi F hH) with hJb
  set Tb : Subgroup ↥(alternatingGroup (Fin 8)) := S126L19c.Tbar F hH with hTb
  have hconj : ∀ y ∈ Tb, ∀ x ∈ Jb, y * x * y⁻¹ ∈ Jb := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨j, hj, rfl⟩
    have htT : ((t : ↥L) : G) ∈ T := (Subgroup.mem_subgroupOf.1 ht).1
    have hjJ : ((j : ↥L) : G) ∈ J := Subgroup.mem_subgroupOf.1 hj
    refine ⟨t * j * t⁻¹, ?_, by simp⟩
    refine Subgroup.mem_subgroupOf.2 ?_
    have h := (Subgroup.mem_normalizer_iff.1 (hJT htT) ((j : ↥L) : G)).1 hjJ
    simpa using h
  have hnorm : Tb ≤ Subgroup.normalizer (Jb : Set ↥(alternatingGroup (Fin 8))) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj y hy x hx, fun hx => ?_⟩
    have h := hconj y⁻¹ (Subgroup.inv_mem _ hy) _ hx
    have h2 : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
    rwa [h2] at h
  have hJ45 : 45 ∣ Nat.card (Jb ⊔ Tb : Subgroup ↥(alternatingGroup (Fin 8))) :=
    h45.trans (Subgroup.card_dvd_of_le le_sup_left)
  have hT64 : 64 ∣ Nat.card (Jb ⊔ Tb : Subgroup ↥(alternatingGroup (Fin 8))) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : Tb ≤ Jb ⊔ Tb)
    rwa [hTb, S126L19c.card_Tbar F hH] at this
  have hD : (Jb ⊔ Tb : Subgroup ↥(alternatingGroup (Fin 8))) = ⊤ :=
    eq_top_of_dvd_card_A8 (by
      have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 45 64) hJ45 hT64
      simpa using this)
  have hn : Jb.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hD]
    exact sup_le Subgroup.le_normalizer hnorm
  haveI := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Jb with h0 | h0
  · exfalso
    rw [h0, Subgroup.card_bot] at h45
    omega
  · exact h0

end Setting

end CFSG.Quasithin.H13.P31Sec
