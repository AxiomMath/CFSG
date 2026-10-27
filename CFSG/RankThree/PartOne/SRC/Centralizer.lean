module

public import CFSG.RankThree.OddKernel.OddLift
public import CFSG.RankThree.PartOne.SRC.RankOne
public import CFSG.RankThree.PartOne.SRC.Reduce
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne.SRC

open Subgroup

theorem exists_involution_lift {Y S : Type*} [Group Y] [Finite Y] [Group S] (φ : Y →* S) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hker : IsPGroup p φ.ker) {t : S} (ht : orderOf t = 2)
    (hs : t ∈ φ.range) : ∃ t' : Y, orderOf t' = 2 ∧ φ t' = t := by
  obtain ⟨y, hy⟩ := hs
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hy2 : y ^ 2 ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hy, ht2]
  obtain ⟨a, ha⟩ := hker ⟨y ^ 2, hy2⟩
  have ha' : (y ^ 2) ^ (p ^ a) = 1 := by simpa using congrArg Subtype.val ha
  have hodd : Odd (p ^ a) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨k, hk⟩ := hodd
  have hφ : φ (y ^ (p ^ a)) = t := by
    rw [map_pow, hy, hk, pow_succ, pow_mul, ht2, one_pow, one_mul]
  have hsq : (y ^ (p ^ a)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ha']
  refine ⟨y ^ (p ^ a), orderOf_eq_prime hsq fun h1 => ?_, hφ⟩
  rw [h1, map_one] at hφ
  rw [← hφ] at ht
  simp at ht

theorem exists_mem_centralizer_lift {Y S : Type*} [Group Y] [Finite Y] [Group S] (φ : Y →* S)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hker : IsPGroup p φ.ker) {t' : Y}
    (ht' : orderOf t' = 2) {s : S} (hs : s ∈ φ.range) (hc : s * φ t' = φ t' * s) :
    ∃ y : Y, y ∈ Subgroup.centralizer ({t'} : Set Y) ∧ φ y = s := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y₁, hy₁⟩ := hs
  obtain ⟨n, hn⟩ := hker.exists_card_eq
  have hodd : Odd (Nat.card φ.ker) := by
    rw [hn]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hu : orderOf (y₁ * t' * y₁⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht']
  have hmk : ((t' : Y) : Y ⧸ φ.ker) = ((y₁ * t' * y₁⁻¹ : Y) : Y ⧸ φ.ker) := by
    rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hy₁]
    rw [hc]
    group
  obtain ⟨m, hm, hmt⟩ := CFSG.RankThree.OddKernel.isConj_of_mk_eq φ.ker hodd ht' hu hmk
  refine ⟨m⁻¹ * y₁, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc (m⁻¹ * y₁) * t' = m⁻¹ * (y₁ * t' * y₁⁻¹) * y₁ := by group
      _ = m⁻¹ * (m * t' * m⁻¹) * y₁ := by rw [hmt]
      _ = t' * m⁻¹ * y₁ := by group
      _ = t' * (m⁻¹ * y₁) := by group
  · rw [map_mul, map_inv, (MonoidHom.mem_ker.mp hm), inv_one, one_mul, hy₁]

theorem rankFourCover_of_mulEquiv {p : ℕ} {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : RankFourCover p S') : RankFourCover p S := by
  intro Y _ _ φ hφ hker
  refine h Y (e.toMonoidHom.comp φ) (e.surjective.comp hφ) ?_
  have hk : (e.toMonoidHom.comp φ).ker = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact map_eq_one_iff e.toMonoidHom e.injective
  rw [hk]
  exact hker


theorem rankFourCover_of_SL2 {p e : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [CharP F p]
    (hF : Nat.card F = p ^ e) (hp2 : p ≠ 2) (he : 4 ≤ e) {S : Type}
    [Group S] (ι : Matrix.SpecialLinearGroup (Fin 2) F →* S)
    (hι : Function.Injective ι) {t : S} (ht : orderOf t = 2) (hc : ∀ g, ι g * t = t * ι g) :
    RankFourCover p S := by
  classical
  intro Y _ _ φ hφ hker
  have hp : p.Prime := Fact.out
  obtain ⟨t', ht'2, hφt'⟩ := exists_involution_lift φ hp hp2 hker ht (hφ t)
  set W : Subgroup Y := Subgroup.centralizer ({t'} : Set Y) ⊓ ι.range.comap φ with hW
  let φW : W →* ι.range := (φ.comp W.subtype).codRestrict ι.range (fun w => w.2.2)
  let ρ : W →* Matrix.SpecialLinearGroup (Fin 2) (F) :=
    (MonoidHom.ofInjective hι).symm.toMonoidHom.comp φW
  have hρι : ∀ w : W, ι (ρ w) = φ (w : Y) := by
    intro w
    have h1 := (MonoidHom.ofInjective hι).apply_symm_apply (φW w)
    exact congrArg Subtype.val h1
  have hρs : Function.Surjective ρ := by
    intro g
    obtain ⟨y, hy, hyφ⟩ := exists_mem_centralizer_lift φ hp hp2 hker ht'2 (hφ (ι g))
      (by rw [hφt']; exact hc g)
    have hyW : y ∈ W := ⟨hy, ⟨g, hyφ.symm⟩⟩
    refine ⟨⟨y, hyW⟩, hι ?_⟩
    rw [hρι]
    exact hyφ
  have hρker : IsPGroup p ρ.ker := by
    intro x
    have hx1 : φ ((x : W) : Y) = 1 := by
      rw [← hρι, MonoidHom.mem_ker.mp x.2, map_one]
    obtain ⟨k, hk⟩ := hker ⟨((x : W) : Y), hx1⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg (fun z : φ.ker => (z : Y)) hk))⟩
  obtain ⟨E, k, hk, hE, hcard⟩ := rank_four_of_cover_SL2 hF hp2 he ρ hρs hρker
  have ht'1 : t' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht'2
    omega
  refine ⟨Subgroup.zpowers t', E.map W.subtype, k, ?_, ?_, isElementaryAbelian_map' W.subtype hE,
    hk, ?_, ?_⟩
  · intro h
    exact ht'1 (by simpa using (Subgroup.zpowers_eq_bot.mp h))
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht'2]; simp)
  · rw [Subgroup.card_map_of_injective W.subtype_injective, hcard]
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    have hxc : (w : Y) ∈ Subgroup.centralizer ((Subgroup.zpowers t' : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcw : t' * (w : Y) = (w : Y) * t' :=
        (Subgroup.mem_centralizer_singleton_iff.mp w.2.1).symm
      exact ((Commute.zpow_left (show Commute t' (w : Y) from hcw) m).eq)
    exact Subgroup.centralizer_le_normalizer _ hxc

end CFSG.RankThree.PartOne.SRC
