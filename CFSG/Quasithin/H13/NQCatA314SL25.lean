module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open Matrix CFSG.Open

@[expose] def negOne25 : SpecialLinearGroup (Fin 2) (ZMod 5) :=
  ⟨-1, by rw [Matrix.det_neg]; simp⟩

theorem negOne25_mem_center :
    negOne25 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  show ((g : Matrix (Fin 2) (Fin 2) (ZMod 5)) * (-1)) i j =
    ((-1) * (g : Matrix (Fin 2) (Fin 2) (ZMod 5))) i j
  simp

theorem orderOf_negOne25 : orderOf negOne25 = 2 := by
  apply orderOf_eq_prime
  · rw [sq]
    ext i j
    show ((-1) * (-1) : Matrix (Fin 2) (Fin 2) (ZMod 5)) i j =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) i j
    simp
  · intro h
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin 2) (ZMod 5) =>
      (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0) h
    have h2 : (-1 : ZMod 5) = 1 := h1
    exact absurd h2 (by decide)

theorem card_sl25 : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_two, ZMod.card]

theorem isPGroup_center_sl25 :
    IsPGroup 2 (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 5))) := by
  intro c
  obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp c.2
  rw [Fintype.card_fin] at hr
  refine ⟨1, ?_⟩
  have h1 : ((c.1 ^ 2 : SpecialLinearGroup (Fin 2) (ZMod 5)) : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrc, ← map_pow, hr, map_one]
  apply Subtype.ext
  rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  ext i j
  exact congrFun (congrFun h1 i) j

theorem le_center_of_normal_sl25 {N : Subgroup (SpecialLinearGroup (Fin 2) (ZMod 5))}
    (hN : N.Normal) (h2 : IsPGroup 2 N) :
    N ≤ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
  set Z := Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 5)) with hZ
  set q := QuotientGroup.mk' Z with hq
  have hNq : (N.map q).Normal := hN.map q (QuotientGroup.mk'_surjective Z)
  rcases hs.eq_bot_or_eq_top_of_normal (N.map q) with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    have hsup : N ⊔ Z = ⊤ := by
      rw [← QuotientGroup.ker_mk' Z, ← Subgroup.comap_map_eq, ← hq, h, Subgroup.comap_top]
    have htop : IsPGroup 2 (⊤ : Subgroup (SpecialLinearGroup (Fin 2) (ZMod 5))) :=
      hsup ▸ IsPGroup.to_sup_of_normal_right h2 isPGroup_center_sl25
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp htop
    rw [Subgroup.card_top, card_sl25] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 120)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem sl25_core {G : Type} [Group G] {B : Subgroup G}
    (e : ↥B ≃* SpecialLinearGroup (Fin 2) (ZMod 5)) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ pCoreOf 2 B ∧
      B ≤ Subgroup.centralizer (pCoreOf 2 B : Set G) := by
  set x : ↥B := e.symm negOne25 with hx
  have hx2 : orderOf x = 2 := by rw [hx, MulEquiv.orderOf_eq, orderOf_negOne25]
  have hxc : x ∈ Subgroup.center ↥B := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply e.injective
    rw [map_mul, map_mul, hx, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp negOne25_mem_center (e y)
  have hcen : ∀ N : Subgroup ↥B, N.Normal → IsPGroup 2 N → N ≤ Subgroup.center ↥B := by
    intro N hN hN2
    have h1 := le_center_of_normal_sl25 (hN.map e.toMonoidHom e.surjective) (hN2.map _)
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro y
    apply e.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp (h1 ⟨n, hn, rfl⟩) (e y)
  have hO : Open.pCore 2 ↥B ≤ Subgroup.center ↥B := by
    rw [CFSG.pCore_eq_iSup]
    exact iSup_le fun N => iSup_le fun hN => iSup_le fun hN2 => hcen N hN hN2
  have hzN : (Subgroup.zpowers x).Normal := ⟨fun n hn g => by
    have hc := Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hxc hn) g
    rw [hc, mul_inv_cancel_right]
    exact hn⟩
  have hz2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])
  have hle : Subgroup.zpowers x ≤ Open.pCore 2 ↥B := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (Subgroup.zpowers x) (le_iSup_of_le hzN (le_iSup_of_le hz2 le_rfl))
  have hxO : x ∈ Open.pCore 2 ↥B := hle (Subgroup.mem_zpowers x)
  refine ⟨(x : G), by rw [Subgroup.orderOf_coe, hx2], ⟨x, hxO, rfl⟩, fun b hb => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨p, hp, rfl⟩
  have h1 := Subgroup.mem_center_iff.mp (hO hp) ⟨b, hb⟩
  exact (congrArg Subtype.val h1).symm

end CFSG.Quasithin.H13.NQCat.A314D
