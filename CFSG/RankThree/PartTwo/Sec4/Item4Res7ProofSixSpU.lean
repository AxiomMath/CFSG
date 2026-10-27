module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofTools
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofU4
import CFSG.RankThree.PartOne.KF.SymCtxMatrix
import CFSG.RankThree.PartOne.KF.SUSylow
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.LieType.BorelTits
open CFSG.Assembly.RankThreeEven (projSp projSU)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Unitary (conjTr SU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)

namespace Res4Seven

variable {X : Type} [Group X] [Finite X] {D : Subgroup X} {c d : X} {K : Subgroup X}

theorem mem_of_commute (h : InnerConfig424 X D c d K) {x : X} (hx3 : x ^ 3 = 1)
    (hxD : ∀ y ∈ D, x * y = y * x) : x ∈ D := by
  by_contra hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsup := Sec5.isElemAbelian_sup_zpowers h.maximal.prop hx hx3
    (fun y hy => (hxD y hy).symm)
  exact hx (h.maximal.2 hsup.1 le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))

theorem false_of_dihedral_four (h : InnerConfig424 X D c d K)
    (e : autIn (⊤ : Subgroup X) D ≃* DihedralGroup 4) : False := by
  refine Item424Res2.false_of_pow_four h
    (Item424Res2.exists_pow_four_of_mulEquiv e (m := DihedralGroup.r 1) ?_ ?_)
  · rw [DihedralGroup.r_one_pow]
    exact congrArg DihedralGroup.r (by decide)
  · rw [DihedralGroup.r_one_pow]
    intro h2
    have h2' : DihedralGroup.r (2 : ZMod 4) = DihedralGroup.r 0 := h2
    exact absurd (DihedralGroup.r.inj h2') (by decide)

theorem census424_of_sp4_even {n : ℕ} (hn1 : 1 ≤ n) (hev : Even n)
    (eX : X ≃* projSp 2 (GaloisField 2 n)) : Census424 X := by
  intro D c d J h
  have hDe := h.maximal.prop
  have hmax : ∀ x : X, x ^ 3 = 1 → (∀ y ∈ D, x * y = y * x) → x ∈ D := fun x hx3 hxD =>
    mem_of_commute h hx3 hxD
  set F := GaloisField 2 n with hFdef
  have hF : Nat.card F = 2 ^ n := GaloisField.card 2 n (by omega)
  have hdvd : 3 ∣ Nat.card F - 1 := by rw [hF]; exact Res417Six.three_dvd_two_pow_sub_one hev
  have hζ := Res417Six.exists_primitiveRoot_three hdvd
  let e₀ : X ≃* spRev F := (eX.trans (Res417Six.projSpEquivSp F)).trans (spRevEquiv F)
  set T : Subgroup (spRev F) := (d8Tor 3 F 4).subgroupOf (spRev F) with hTdef
  have hTexp : ∀ t ∈ T, t ^ 3 = 1 := by
    intro t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((t : spRev F) : GL (Fin 4) F) ^ 3 = 1
    rw [← hv]
    show diagU (d8Vec 4 v) ^ 3 = 1
    rw [diagU_pow, d8Vec_pow_eq_one, diagU_one]
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((s : spRev F) : GL (Fin 4) F) * (t : GL (Fin 4) F) =
      (t : GL (Fin 4) F) * (s : GL (Fin 4) F)
    rw [← hv, ← hw]
    show diagU (d8Vec 4 v) * diagU (d8Vec 4 w) = diagU (d8Vec 4 w) * diagU (d8Vec 4 v)
    rw [diagU_mul, diagU_mul, mul_comm]
  have hD'exp : ∀ x ∈ D.map e₀.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show e₀ x ^ 3 = 1
    rw [← map_pow, hDe.2 x hx, map_one]
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_sp Nat.prime_three (by norm_num) hdvd _ hD'exp
  have hmap : D.map (e₀.trans (MulAut.conj g)).toMonoidHom = T :=
    Res417Six.map_eq_of_conj_le e₀ hmax hTcomm hTexp fun x hx => hg _ ⟨x, hx, rfl⟩
  have hT4 : ∀ v : D8Mod 3 F, (diagU (d8Vec 4 v) : GL (Fin 4) F) ∈ spRev F := fun v => by
    rw [d8Vec_four]
    exact diagU_dvec4_mem_spRev _ _
  have hP4 : ∀ τ : Equiv.Perm (Fin 4), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (permGL τ : GL (Fin 4) F) ∈ spRev F := fun τ hτ => by
    rw [mem_spRev_iff]
    simpa [conjTr] using permGL_gram (RingEquiv.refl F) τ hτ
  obtain ⟨SM⟩ := exists_d8ctx d8Comb_four d8Comb2_four Nat.prime_three (by norm_num) hζ
    (spRev F) hT4 hP4
  obtain ⟨φ⟩ := Res417Six.nonempty_autIn_mulEquiv_of_map_eq _ hmap
  exact (false_of_dihedral_four h (φ.trans (SM.weylEquiv Nat.prime_three (by norm_num) hζ))).elim

theorem census424_of_u4_even {n : ℕ} (hn1 : 1 ≤ n) (hev : Even n)
    (eX : X ≃* projSU 4 2 n) : Census424 X := by
  intro D c d J h
  have hDe := h.maximal.prop
  have hmax : ∀ x : X, x ^ 3 = 1 → (∀ y ∈ D, x * y = y * x) → x ∈ D := fun x hx3 hxD =>
    mem_of_commute h hx3 hxD
  set F := GaloisField 2 (2 * n) with hFdef
  have hF : Nat.card F = (2 ^ n) ^ 2 := Res417Six.card_galoisField_two_mul hn1
  set σ : F ≃+* F := unitaryInvolution F 2 n with hσdef
  have hσ : ∀ c : F, σ c = c ^ 2 ^ n := fun c => unitaryInvolution_apply F 2 n c
  have hpq : 3 ∣ 2 ^ n - 1 := Res417Six.three_dvd_two_pow_sub_one hev
  let e₀ : X ≃* SU σ 4 := eX.trans (Res417Six.projSUEquivSU hn1)
  set T : Subgroup (SU σ 4) := (d8Tor 3 F 4).subgroupOf (SU σ 4) with hTdef
  have hTexp : ∀ t ∈ T, t ^ 3 = 1 := by
    intro t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((t : SU σ 4) : GL (Fin 4) F) ^ 3 = 1
    rw [← hv]
    show diagU (d8Vec 4 v) ^ 3 = 1
    rw [diagU_pow, d8Vec_pow_eq_one, diagU_one]
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((s : SU σ 4) : GL (Fin 4) F) * (t : GL (Fin 4) F) =
      (t : GL (Fin 4) F) * (s : GL (Fin 4) F)
    rw [← hv, ← hw]
    show diagU (d8Vec 4 v) * diagU (d8Vec 4 w) = diagU (d8Vec 4 w) * diagU (d8Vec 4 v)
    rw [diagU_mul, diagU_mul, mul_comm (d8Vec 4 v) (d8Vec 4 w)]
  have hD'exp : ∀ x ∈ D.map e₀.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show e₀ x ^ 3 = 1
    rw [← map_pow, hDe.2 x hx, map_one]
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_su (Or.inl rfl) d8Comb_four hF Nat.prime_three
    (by norm_num) hpq _ hD'exp
  have hmap : D.map (e₀.trans (MulAut.conj g)).toMonoidHom = T :=
    Res417Six.map_eq_of_conj_le e₀ hmax hTcomm hTexp fun x hx => hg _ ⟨x, hx, rfl⟩
  have hdvd : 3 ∣ Nat.card F - 1 := by
    rw [hF]
    have h1 : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := by
      have : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
        have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        zify [Nat.one_le_pow 2 (2 ^ n) (by omega), hq]
        ring
      rw [this]
      exact dvd_mul_right _ _
    exact hpq.trans h1
  have hζ := Res417Six.exists_primitiveRoot_three hdvd
  have hσfix : ∀ u : rootsOfUnity 3 F, σ ((u : Fˣ) : F) = (u : Fˣ) := by
    intro u
    have h1 : (u : Fˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp u.2
    have h2 : (u : Fˣ) ^ (2 ^ n - 1) = 1 := by
      obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, h1, one_pow]
    rw [hσ, ← Units.val_pow_eq_pow_val]
    have : (u : Fˣ) ^ 2 ^ n = (u : Fˣ) := by
      calc (u : Fˣ) ^ 2 ^ n = (u : Fˣ) ^ (2 ^ n - 1) * (u : Fˣ) := by
            rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
        _ = (u : Fˣ) := by rw [h2, one_mul]
    rw [this]
  have hT4 : ∀ v : D8Mod 3 F, (diagU (d8Vec 4 v) : GL (Fin 4) F) ∈ SU σ 4 :=
    fun v => d8Vec_mem_SU (Or.inl rfl) d8Comb_four σ hσfix v
  have hP4 : ∀ τ : Equiv.Perm (Fin 4), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (permGL τ : GL (Fin 4) F) ∈ SU σ 4 := fun τ hτ => permGL_mem_SU σ τ hτ
  obtain ⟨SM⟩ := exists_d8ctx d8Comb_four d8Comb2_four Nat.prime_three (by norm_num) hζ
    (SU σ 4) hT4 hP4
  obtain ⟨φ⟩ := Res417Six.nonempty_autIn_mulEquiv_of_map_eq _ hmap
  exact (false_of_dihedral_four h (φ.trans (SM.weylEquiv Nat.prime_three (by norm_num) hζ))).elim

theorem census424_of_u4_odd {n : ℕ} (hn : Odd n) (eX : X ≃* projSU 4 2 n) : Census424 X := by
  intro D c d J h
  have hDe := h.maximal.prop
  have hmax : ∀ x : X, x ^ 3 = 1 → (∀ y ∈ D, x * y = y * x) → x ∈ D := fun x hx3 hxD =>
    mem_of_commute h hx3 hxD
  have hn1 : 1 ≤ n := hn.pos
  set F := GaloisField 2 (2 * n) with hFdef
  have hF : Nat.card F = (2 ^ n) ^ 2 := Res417Six.card_galoisField_two_mul hn1
  have hU : UnitaryFieldData 2 n F := ⟨Nat.prime_two, hn1, GaloisField.card 2 (2 * n) (by omega)⟩
  have h3 : 3 ∣ 2 ^ n + 1 := Res417Six.three_dvd_two_pow_add_one hn
  have hDexp : ∀ x ∈ D, x ^ 3 = 1 := hDe.2
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU Nat.prime_three h3
    ((Res417Six.unitarySUEquivProjSU hn1).trans eX.symm) D hDexp hDcomm
  set T : Subgroup (unitarySU 2 n F 4) := (torusSU 3 4 F).subgroupOf (unitarySU 2 n F 4)
    with hTdef
  have hTexp : ∀ t ∈ T, t ^ 3 = 1 := by
    intro t ht
    obtain ⟨d, hd1, -, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp ht)
    apply Subtype.ext
    show (t : GL (Fin 4) F) ^ 3 = 1
    rw [← hd, diagU_pow, show d ^ 3 = 1 from funext hd1, diagU_one]
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    obtain ⟨d, -, -, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp hs)
    obtain ⟨d', -, -, hd'⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp ht)
    apply Subtype.ext
    show (s : GL (Fin 4) F) * t = t * s
    rw [← hd, ← hd', diagU_mul, diagU_mul, mul_comm d d']
  have hmap : D.map (ψ.symm.trans (MulAut.conj 1)).toMonoidHom = T := by
    refine Res417Six.map_eq_of_conj_le ψ.symm hmax hTcomm hTexp fun x hx => ?_
    rw [one_mul, inv_one, mul_one]
    exact Subgroup.mem_subgroupOf.mpr (hψ _ (by rw [MulEquiv.apply_symm_apply]; exact hx))
  have hdvd : 3 ∣ Nat.card F - 1 := by
    rw [hF]
    have h1 : 2 ^ n + 1 ∣ (2 ^ n) ^ 2 - 1 := by
      have : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
        have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        zify [Nat.one_le_pow 2 (2 ^ n) (by omega), hq]
        ring
      rw [this]
      exact dvd_mul_left _ _
    exact h3.trans h1
  obtain ⟨ζ, hζ⟩ := Res417Six.exists_primitiveRoot_three hdvd
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have := hζ.dvd_of_pow_eq_one 2 h
    norm_num at this
  have hdist : ∀ i j : Fin 4, i ≠ j → ∃ x ∈ torusSU 3 4 F, ent x i i ≠ ent x j j :=
    fun i j hij => torusSU_char_distinct hζ3 hζ2 hij
  obtain ⟨SM⟩ := SymCtx.ofMatrixGroup (unitarySU 2 n F 4) (torusSU_le_unitarySU hU h3)
    (fun σ => permGL_mem_unitarySU hU σ) hdist
  have hcard := Res417Six.card_eq_of_map_eq _ hmap
  rw [SM.card_F (m := 3) rfl (by norm_num) ⟨ζ, hζ⟩, h.card_eq] at hcard
  norm_num at hcard

end Res4Seven

end CFSG.RankThree.PartTwo.Sec4
