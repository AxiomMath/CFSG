module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveL2

public section

namespace CFSG.Quasithin.H13.FiveNorm

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.NQCat.T513 CFSG.GorensteinWalter
open scoped Pointwise

local notation "L24" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)

variable {Y : Type} [Group Y] [Finite Y] {L T D B : Subgroup Y}

theorem le_normalizer_of_psl2_prime_two
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) (h5 : p ^ 2 % 5 = 1) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* PSL2 K) (hZ2 : IsPGroup 2 (Subgroup.center ↥L))
    (hT : IsSylowTwoOf T ⊤) (hTN : T ≤ Subgroup.normalizer (L : Set Y)) (hD : Nat.card D = 5)
    (hDN : D ≤ Subgroup.normalizer (L : Set Y))
    (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) (hBL : B ≤ L)
    (hB : ⁅B, B⁆ = B) (hA5 : IsAlt 5 (ModO2 B)) (hTB : IsSylowTwoOf (T ⊓ B) B) {b : Y}
    (hbB : b ∈ B) (hb3 : orderOf b = 3)
    (hbT : b ∈ Subgroup.normalizer ((T ⊓ B : Subgroup Y) : Set Y))
    (hbD : ∀ d ∈ D, d * b = b * d) : D ≤ Subgroup.normalizer (B : Set Y) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp11 := eleven_le hp h5 h8
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩
  have hcen := psl2_center_eq_bot K
  have hinn : FiveInner (PSL2 K) := fiveInner_of_oddInner
    (inner_of_odd_psl2 hodd (ringAut_mul_self hp le_rfl (by norm_num) (by rw [hK, pow_one])))
  rcases eq_one_or_card_iPart e hcen hinn hD hDN with h1 | ⟨hinn', hD₁⟩
  · exact le_normalizer_of_pImg L e hBL hB hDN fun d hd y hy => by
      rw [h1 d hd, MulAut.one_apply]
      exact hy
  have hsyl := isSylowTwoOf_pImg e hT hTN
  have hmax : ∀ X : Subgroup (PSL2 K), IsPGroup 2 X → pImg L e (T ⊓ L) ≤ X →
      X = pImg L e (T ⊓ L) := fun X hX hle =>
    le_antisymm ((A4.isSylowTwoOf_iff_maximal.mp hsyl).2.2 X le_top hX hle) hle
  have hperm := inner_perm L e hTN hDN hDT hT.2.1 hinn' (conj_injective_of_center hcen) hmax
  obtain ⟨u, hu, hPu, -⟩ := psl2_card_four_mul hp hK h8
  have hP4 := card_le_four_of_isPGroup hu hPu
  set fB : ↥B →* ↥(pImg L e B) :=
    ((toP L e).comp (Subgroup.inclusion hBL)).codRestrict (pImg L e B)
      fun r => toP_mem_pImg L e (hBL r.2) r.2 with hfB
  have hfBs : Function.Surjective fB := by
    rintro ⟨y, hy⟩
    obtain ⟨r, hrL, hrB, rfl⟩ := (mem_pImg L e).1 hy
    exact ⟨⟨r, hrB⟩, rfl⟩
  have hker : ∀ r : ↥B, fB r = 1 → (Subgroup.inclusion hBL r) ∈ Subgroup.center ↥L := by
    intro r hr
    rw [← ker_toP L e, MonoidHom.mem_ker]
    exact congrArg Subtype.val hr
  have hkB : IsPGroup 2 fB.ker := by
    let g : ↥fB.ker →* ↥(Subgroup.center ↥L) :=
      ((Subgroup.inclusion hBL).comp fB.ker.subtype).codRestrict _ fun r =>
        hker r.1 (MonoidHom.mem_ker.mp r.2)
    refine hZ2.of_injective g fun a c hac => ?_
    have := congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : Y)) hac
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨eA⟩ := hA5
  obtain ⟨eL⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
  obtain ⟨eR⟩ := nonempty_equiv_l24_of_surjective (eA.trans eL.symm) fB hfBs hkB fun X hX => by
    have h1 := hP4 (X.map (pImg L e B).subtype) (hX.map _)
    rwa [Subgroup.card_map_of_injective (pImg L e B).subtype_injective] at h1
  have hB60 : Nat.card ↥(pImg L e B) = 2 ^ 2 * 15 := by
    rw [Nat.card_congr (eR.trans eL).toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  have himg : (((T ⊓ B).subgroupOf B).map fB).map (pImg L e B).subtype = pImg L e (T ⊓ B) := by
    ext y
    constructor
    · rintro ⟨_, ⟨⟨x, hxB⟩, hx, rfl⟩, rfl⟩
      exact (mem_pImg L e).2 ⟨x, hBL hxB, Subgroup.mem_subgroupOf.mp hx, rfl⟩
    · intro hy
      obtain ⟨x, hxL, hxTB, rfl⟩ := (mem_pImg L e).1 hy
      exact ⟨fB ⟨x, hxTB.2⟩, ⟨⟨x, hxTB.2⟩, Subgroup.mem_subgroupOf.mpr hxTB, rfl⟩, rfl⟩
  have hTB4 : Nat.card ↥(pImg L e (T ⊓ B)) = 2 ^ 2 := by
    have h1 := isSylowTwoOf_top_map_of_surjective
      (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hTB) fB hfBs
    have h2 := card_eq_of_isSylowTwoOf_top h1 hB60 (by decide)
    rw [← himg, Subgroup.card_map_of_injective (pImg L e B).subtype_injective]
    exact h2
  have hTLB : pImg L e (T ⊓ L) = pImg L e (T ⊓ B) := by
    have hle : pImg L e (T ⊓ B) ≤ pImg L e (T ⊓ L) := pImg_mono L e (inf_le_inf_left T hBL)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hTB4]
    exact hP4 _ (isPGroup_pImg L e inf_le_right hT.2.1.to_inf_left)
  have hb3' : orderOf (toP L e ⟨b, hBL hbB⟩) = 3 := by
    have h1 : orderOf (toP L e ⟨b, hBL hbB⟩) ∣ 3 := by
      rw [← hb3, ← Subgroup.orderOf_mk b (hBL hbB)]
      exact orderOf_map_dvd _ _
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exfalso
      have hz : (⟨b, hBL hbB⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [← ker_toP L e, MonoidHom.mem_ker]
        exact orderOf_eq_one_iff.mp h
      obtain ⟨k, hk⟩ := hZ2 ⟨_, hz⟩
      have h2 : b ^ 2 ^ k = 1 := by
        have := congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : Y)) hk
        simpa using this
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hb3] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    · exact h
  have hbD' : toP L e ⟨b, hBL hbB⟩ ∈ Subgroup.normalizer (iPart L e D : Set (PSL2 K)) :=
    mem_normalizer_of_commute fun x hx => toP_commute_iPart e hcen (hBL hbB) hbD hx
  have hbT' : toP L e ⟨b, hBL hbB⟩ ∈
      Subgroup.normalizer (pImg L e (T ⊓ L) : Set (PSL2 K)) := by
    rw [hTLB]
    exact toP_mem_normalizer_pImg e (inf_le_right.trans hBL) (hBL hbB) hbT
  have hTR : pImg L e (T ⊓ L) ≤ pImg L e B := by
    rw [hTLB]
    exact pImg_mono L e inf_le_right
  obtain ⟨hT2, hTi⟩ := isSylowTwoOf_top_index hsyl
  have hcore := core_psl2_prime_le hK h8 hp11 (hT2.toSylow hTi) (isCyclic_of_prime_card hD₁)
    (by rw [hD₁]; decide) hperm eR hTR (toP_mem_pImg L e (hBL hbB) hbB) hb3' hbD' hbT'
  exact le_normalizer_of_iPart_le e hBL hB hDN hinn' fun x hx =>
    Subgroup.le_normalizer (hcore hx).1

end CFSG.Quasithin.H13.FiveNorm
