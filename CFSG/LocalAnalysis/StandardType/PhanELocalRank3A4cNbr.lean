module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A4cSkew
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A4cPlane

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private lemma plh_flag_facts (hK : Nat.card K = (2 ^ f) ^ 2) {p : Submodule K (Fin 4 → K)}
    (h : ∃ L H, AdmCh (Adm4c (K := K) f) p L H) :
    finrank K p = 1 ∧ sgS K f 4 p ≠ p := by
  obtain ⟨L, H, hch⟩ := h
  exact ⟨hch.1.p1, adm4c_nonreal (f := f) hK hch⟩

private lemma plh_common (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (P : Finset (Submodule K (Fin 4 → K))) (hPcard : P.card ≤ 4)
    (hP : ∀ p ∈ P, finrank K p = 1 ∧ sgS K f 4 p ≠ p) :
    ∃ t : Submodule K (Fin 4 → K), finrank K t = 1 ∧ sgS K f 4 t ≠ t ∧
      ∀ p ∈ P, AdmAdj (Adm4c (K := K) f) p t := by
  classical
  let Rs : Finset (Submodule K (Fin 4 → K)) := P.image (fun p => p ⊔ sgS K f 4 p)
  have hRsle : Rs.card ≤ 4 := by
    calc Rs.card ≤ P.card := Finset.card_image_le
      _ ≤ 4 := hPcard
  have hR : ∀ R ∈ Rs, finrank K R = 2 ∧ sgS K f 4 R = R := by
    intro R hR
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hR
    exact ⟨finrank_realLine (f := f) hK (hP p hp).1 (hP p hp).2,
      sgS_realLine (f := f) hK p⟩
  have hxle : 2 ^ f ≤ (2 ^ f) ^ 3 := by nlinarith [hq]
  have hcountA : Rs.card * (2 ^ f) ^ 2 + 1 < (2 ^ f) ^ 4 := by
    have hx2 : 16 ≤ (2 ^ f) ^ 2 := by nlinarith [hq]
    have hx4 : 4 * (2 ^ f) ^ 2 + 1 < (2 ^ f) ^ 4 := by nlinarith [hx2]
    nlinarith [hRsle, hx4]
  have hcountB : Rs.card * ((2 ^ f) ^ 3 - 2 ^ f) +
      (∅ : Finset (Submodule K (Fin 4 → K))).card * (2 ^ f) ^ 2 + 2 ^ f < (2 ^ f) ^ 4 := by
    have hx3 : 4 * ((2 ^ f) ^ 3 - 2 ^ f) + 2 ^ f < (2 ^ f) ^ 4 := by
      have h1 : 4 * ((2 ^ f) ^ 3 - 2 ^ f) + 2 ^ f <
          4 * ((2 ^ f) ^ 3 - 2 ^ f) + 4 * 2 ^ f := by
        have : 2 ^ f < 4 * 2 ^ f := by nlinarith [hq]
        omega
      have h2 : 4 * ((2 ^ f) ^ 3 - 2 ^ f) + 4 * 2 ^ f = 4 * (2 ^ f) ^ 3 := by
        rw [← mul_add, Nat.sub_add_cancel hxle]
      have h3 : 4 * (2 ^ f) ^ 3 ≤ (2 ^ f) ^ 4 := by nlinarith [hq]
      rw [h2] at h1
      omega
    simp only [Finset.card_empty, Nat.zero_mul, Nat.zero_add]
    nlinarith [hRsle, hx3, Nat.zero_le ((2 ^ f) ^ 3 - 2 ^ f)]
  obtain ⟨u, v, hu, hv, huv, hRu, -⟩ :=
    exists_real_plane (f := f) hK Rs ∅ hR (by intro L hL; simp at hL) hcountA hcountB
  obtain ⟨lam, hlam, -, -⟩ := exists_sg_moved_avoid (f := f) hK hq 0 0
  obtain ⟨ht1, htne, htsup⟩ := realPlane_point (f := f) hK hu hv huv hlam
  refine ⟨Submodule.span K {u + lam • v}, ht1, htne, ?_⟩
  intro p hp
  have hp1 : finrank K p = 1 := (hP p hp).1
  have hpne : sgS K f 4 p ≠ p := (hP p hp).2
  have hpR : p ⊔ sgS K f 4 p ∈ Rs := Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hdisj : (p ⊔ sgS K f 4 p) ⊓ Submodule.span K {u, v} = ⊥ := hRu _ hpR
  have hpt : p ≠ Submodule.span K {u + lam • v} := by
    intro heq
    have hle : p ≤ (p ⊔ sgS K f 4 p) ⊓ Submodule.span K {u, v} := by
      refine le_inf le_sup_left ?_
      rw [heq, ← htsup]
      exact le_sup_left
    rw [hdisj] at hle
    have hbot : p = ⊥ := le_bot_iff.mp hle
    rw [hbot, finrank_bot] at hp1
    omega
  have hskew : (p ⊔ Submodule.span K {u + lam • v}) ⊓
      sgS K f 4 (p ⊔ Submodule.span K {u + lam • v}) = ⊥ :=
    (skew_iff (f := f) hK hp1 ht1 hpne htne hpt).mpr (by rw [htsup]; exact hdisj)
  exact (adm4c_adj_iff (f := f) hK hq hp1 ht1 hpne htne hpt).mpr hskew

theorem adm4c_commonNbrW (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    AdmCommonNbrW (Adm4c (K := K) f) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro u v hu hv
    have hP : ∀ p ∈ ({u, v} : Finset (Submodule K (Fin 4 → K))),
        finrank K p = 1 ∧ sgS K f 4 p ≠ p := by
      intro p hp
      rw [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact plh_flag_facts (f := f) hK hu
      · exact plh_flag_facts (f := f) hK hv
    obtain ⟨t, -, -, hadj⟩ :=
      plh_common (f := f) hK hq {u, v}
        (by have h := Finset.card_le_two (a := u) (b := v); omega) hP
    exact ⟨t, hadj u (by simp), hadj v (by simp)⟩
  · intro a b c d hab hbc hcd hda
    obtain ⟨-, La, Ha, haLH, hbLH⟩ := hab
    obtain ⟨-, Lb, Hb, -, hcLH⟩ := hbc
    obtain ⟨-, Lc, Hc, -, hdLH⟩ := hcd
    have hpa : finrank K a = 1 ∧ sgS K f 4 a ≠ a :=
      ⟨haLH.1.p1, adm4c_nonreal (f := f) hK haLH⟩
    have hpb : finrank K b = 1 ∧ sgS K f 4 b ≠ b :=
      ⟨hbLH.1.p1, adm4c_nonreal (f := f) hK hbLH⟩
    have hpc : finrank K c = 1 ∧ sgS K f 4 c ≠ c :=
      ⟨hcLH.1.p1, adm4c_nonreal (f := f) hK hcLH⟩
    have hpd : finrank K d = 1 ∧ sgS K f 4 d ≠ d :=
      ⟨hdLH.1.p1, adm4c_nonreal (f := f) hK hdLH⟩
    have hP : ∀ p ∈ ({a, b, c, d} : Finset (Submodule K (Fin 4 → K))),
        finrank K p = 1 ∧ sgS K f 4 p ≠ p := by
      intro p hp
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact hpa
      · exact hpb
      · exact hpc
      · exact hpd
    obtain ⟨t, -, -, hadj⟩ :=
      plh_common (f := f) hK hq {a, b, c, d} Finset.card_le_four hP
    exact ⟨t, hadj a (by simp), hadj b (by simp), hadj c (by simp), hadj d (by simp)⟩
  · intro u c d hu hcd
    obtain ⟨-, Lc, Hc, hcLH, hdLH⟩ := hcd
    have hpu : finrank K u = 1 ∧ sgS K f 4 u ≠ u := plh_flag_facts (f := f) hK hu
    have hpc : finrank K c = 1 ∧ sgS K f 4 c ≠ c :=
      ⟨hcLH.1.p1, adm4c_nonreal (f := f) hK hcLH⟩
    have hpd : finrank K d = 1 ∧ sgS K f 4 d ≠ d :=
      ⟨hdLH.1.p1, adm4c_nonreal (f := f) hK hdLH⟩
    have hP : ∀ p ∈ ({u, c, d} : Finset (Submodule K (Fin 4 → K))),
        finrank K p = 1 ∧ sgS K f 4 p ≠ p := by
      intro p hp
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hpu
      · exact hpc
      · exact hpd
    obtain ⟨t, -, -, hadj⟩ :=
      plh_common (f := f) hK hq {u, c, d}
        (by have h := Finset.card_le_three (a := u) (b := c) (c := d); omega) hP
    exact ⟨t, hadj u (by simp), hadj c (by simp), hadj d (by simp)⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
