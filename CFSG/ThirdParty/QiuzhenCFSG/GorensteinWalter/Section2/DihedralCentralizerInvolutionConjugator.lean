module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOppositeReflectionConjugator
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralUniqueCentralInvolution
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra

namespace CFSG
end CFSG
open CFSG

/-!
# An involutory conjugator inside a product centralizer

If distinct commuting involutions have a product centralizer of order
divisible by eight, a Sylow subgroup of that centralizer transports into an
ambient dihedral Sylow subgroup.  The product is then the central rotation and
the two involutions are opposite reflections, so an involution inside the
product centralizer interchanges them.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem exists_involution_conjugator_in_product_centralizer_of_dihedral_sylow_core
    {G : Type u} [Group G] [Finite G]
    (P0 : Sylow 2 G) {m : ℕ}
    (e0 : P0 ≃* DihedralGroup (2 ^ m))
    (t s : G) (ht : IsInvolution t) (hs : IsInvolution s)
    (hts : Commute t s) (htsne : t ≠ s)
    (h8 : 8 ∣ Nat.card
      (Subgroup.centralizer ({t * s} : Set G)))
    (PC : Sylow 2 (Subgroup.centralizer ({t * s} : Set G)))
    (hV : (Subgroup.zpowers t ⊔ Subgroup.zpowers s).subgroupOf
      (Subgroup.centralizer ({t * s} : Set G)) ≤
      (PC : Subgroup (Subgroup.centralizer ({t * s} : Set G)))) :
    ∃ y : G, IsInvolution y ∧
      y * t * y⁻¹ = s ∧
      y ∈ ((PC : Subgroup (Subgroup.centralizer ({t * s} : Set G))).map
        (Subgroup.centralizer ({t * s} : Set G)).subtype) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by simpa [pow_two] using ht.2
  have hss : s * s = 1 := by simpa [pow_two] using hs.2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  let z : G := t * s
  have hzsq : z * z = 1 := by
    dsimp [z]
    calc
      (t * s) * (t * s) = t * (s * t) * s := by group
      _ = t * (t * s) * s := by rw [← hts.eq]
      _ = (t * t) * (s * s) := by group
      _ = 1 := by rw [htt, hss]; simp
  have hzne : z ≠ 1 := by
    intro hz
    apply htsne
    calc
      t = t * 1 := by simp
      _ = t * (s * s) := by rw [hss]
      _ = (t * s) * s := by group
      _ = 1 * s := by rw [show t * s = 1 by simpa [z] using hz]
      _ = s := by simp
  let C : Subgroup G := Subgroup.centralizer ({z} : Set G)
  have htC : t ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    dsimp [z]
    calc
      t * (t * s) = s := by rw [← mul_assoc, htt, one_mul]
      _ = (t * s) * t := by
        rw [mul_assoc, ← hts.eq, ← mul_assoc, htt, one_mul]
  have hsC : s ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    dsimp [z]
    calc
      s * (t * s) = t := by
        rw [← mul_assoc, ← hts.eq, mul_assoc, hss, mul_one]
      _ = (t * s) * s := by rw [mul_assoc, hss, mul_one]
  let A : Subgroup G := Subgroup.zpowers t
  let B : Subgroup G := Subgroup.zpowers s
  have htord : orderOf t = 2 := orderOf_eq_prime ht.2 ht.1
  have hsord : orderOf s = 2 := orderOf_eq_prime hs.2 hs.1
  have hAp : IsPGroup 2 A := by
    apply IsPGroup.of_card (n := 1)
    simp [A, Nat.card_zpowers, htord]
  have hBp : IsPGroup 2 B := by
    apply IsPGroup.of_card (n := 1)
    simp [B, Nat.card_zpowers, hsord]
  have hsNormA : s ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (s * t * s⁻¹) = Subgroup.zpowers t
    have hconj : s * t * s⁻¹ = t := by
      rw [hsinv]
      calc
        s * t * s = t * (s * s) := by rw [← hts.eq]; group
        _ = t := by rw [hss, mul_one]
    rw [hconj]
  have hBnormA : B ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.zpowers_le.mpr hsNormA
  let V : Subgroup G := A ⊔ B
  have hVp : IsPGroup 2 V :=
    IsPGroup.to_sup_of_normal_left' hAp hBp hBnormA
  have hVleC : V ≤ C := by
    apply sup_le
    · exact Subgroup.zpowers_le.mpr htC
    · exact Subgroup.zpowers_le.mpr hsC
  let VC : Subgroup C := V.subgroupOf C
  have hVCp : IsPGroup 2 VC := by
    let eVC : VC ≃* V := Subgroup.subgroupOfEquivOfLe hVleC
    exact IsPGroup.of_equiv hVp eVC.symm
  have hVCPC : VC ≤ (PC : Subgroup C) := by
    simpa [C, V] using hV
  have hPCge : 8 ≤ Nat.card (↥(PC : Subgroup C)) := by
    have hfac : 3 ≤ (Nat.card C).factorization 2 := by
      apply (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        (Nat.card_pos (α := C)).ne').mp
      simpa [C, z] using h8
    rw [PC.card_eq_multiplicity]
    change 2 ^ 3 ≤ 2 ^ (Nat.card C).factorization 2
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).2 hfac
  have htV : t ∈ V :=
    (le_sup_left : A ≤ V) (Subgroup.mem_zpowers t)
  have hsV : s ∈ V :=
    (le_sup_right : B ≤ V) (Subgroup.mem_zpowers s)
  have htPC : (⟨t, htC⟩ : C) ∈ (PC : Subgroup C) := by
    apply hVCPC
    exact Subgroup.mem_subgroupOf.mpr htV
  have hsPC : (⟨s, hsC⟩ : C) ∈ (PC : Subgroup C) := by
    apply hVCPC
    exact Subgroup.mem_subgroupOf.mpr hsV
  let PG : Subgroup G := (PC : Subgroup C).map C.subtype
  have hPGp : IsPGroup 2 PG := PC.isPGroup'.map C.subtype
  have hPGcard : Nat.card PG = Nat.card (↥(PC : Subgroup C)) := by
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective (PC : Subgroup C) C.subtype
        (fun _ _ h => Subtype.ext h)).toEquiv).symm
  have htPG : t ∈ PG :=
    Subgroup.mem_map.mpr ⟨⟨t, htC⟩, htPC, rfl⟩
  have hsPG : s ∈ PG :=
    Subgroup.mem_map.mpr ⟨⟨s, hsC⟩, hsPC, rfl⟩
  have hPGleC : PG ≤ C := Subgroup.map_subtype_le (PC : Subgroup C)
  obtain ⟨Q, hPGQ⟩ := IsPGroup.exists_le_sylow hPGp
  obtain ⟨g, hg⟩ :=
    @MulAction.IsPretransitive.exists_smul_eq G (Sylow 2 G)
      inferInstance inferInstance Q P0
  let cg : G →* G := (MulAut.conj g).toMonoidHom
  have hconjPGP0 : PG.map cg ≤ (P0 : Subgroup G) := by
    rw [← hg]
    exact Subgroup.map_mono hPGQ
  let D : Subgroup P0 := (PG.map cg).subgroupOf (P0 : Subgroup G)
  have hDcard : Nat.card D = Nat.card PG := by
    calc
      Nat.card D = Nat.card (PG.map cg) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hconjPGP0).toEquiv
      _ = Nat.card PG :=
        (Nat.card_congr
          (Subgroup.equivMapOfInjective PG cg
            (MulAut.conj g).injective).toEquiv).symm
  have hDge : 8 ≤ Nat.card D := by
    rw [hDcard, hPGcard]
    exact hPCge
  have hP0card : Nat.card (↥(P0 : Subgroup G)) = 2 * 2 ^ m :=
    (Nat.card_congr e0.toEquiv).trans DihedralGroup.nat_card
  have hm2 : 2 ≤ m := by
    have hDle : Nat.card D ≤ Nat.card (↥(P0 : Subgroup G)) := by
      have hle := Subgroup.card_le_of_le (show D ≤ (⊤ : Subgroup P0) from le_top)
      simpa using hle
    have h8P0 : 8 ≤ Nat.card (↥(P0 : Subgroup G)) := hDge.trans hDle
    have h4pow : 4 ≤ 2 ^ m := by
      rw [hP0card] at h8P0
      omega
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
      (by simpa using h4pow)
  have htMap : g * t * g⁻¹ ∈ PG.map cg :=
    Subgroup.mem_map.mpr ⟨t, htPG, rfl⟩
  have hsMap : g * s * g⁻¹ ∈ PG.map cg :=
    Subgroup.mem_map.mpr ⟨s, hsPG, rfl⟩
  have hzPG : z ∈ PG := by
    exact PG.mul_mem htPG hsPG
  have hzMap : g * z * g⁻¹ ∈ PG.map cg :=
    Subgroup.mem_map.mpr ⟨z, hzPG, rfl⟩
  let t0 : P0 := ⟨g * t * g⁻¹, hconjPGP0 htMap⟩
  let s0 : P0 := ⟨g * s * g⁻¹, hconjPGP0 hsMap⟩
  let z0 : P0 := ⟨g * z * g⁻¹, hconjPGP0 hzMap⟩
  have ht0D : t0 ∈ D := Subgroup.mem_subgroupOf.mpr htMap
  have hs0D : s0 ∈ D := Subgroup.mem_subgroupOf.mpr hsMap
  have hz0D : z0 ∈ D := Subgroup.mem_subgroupOf.mpr hzMap
  have hz0sq : z0 ^ 2 = 1 := by
    apply Subtype.ext
    change (g * z * g⁻¹) ^ 2 = 1
    rw [pow_two]
    calc
      (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzsq]; simp
  have hz0ne : z0 ≠ 1 := by
    intro hz0
    apply hzne
    have hconjOne : g * z * g⁻¹ = 1 := congrArg Subtype.val hz0
    calc
      z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [hconjOne]; simp
  have hz0centD : ∀ q : ↥D,
      (⟨z0, hz0D⟩ : ↥D) * q = q * (⟨z0, hz0D⟩ : ↥D) := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    have hqmap : ((q : P0) : G) ∈ PG.map cg :=
      Subgroup.mem_subgroupOf.mp q.2
    rcases Subgroup.mem_map.mp hqmap with ⟨x, hxPG, hxq⟩
    have hxC : x ∈ C := hPGleC hxPG
    have hxcomm : x * z = z * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hxC
    change (g * z * g⁻¹) * (q : G) = (q : G) * (g * z * g⁻¹)
    rw [← hxq]
    calc
      (g * z * g⁻¹) * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hxcomm.symm]
      _ = (g * x * g⁻¹) * (g * z * g⁻¹) := by group
  have hz0center : z0 ∈ Subgroup.center P0 :=
    central_of_centralizes_large_subgroup_of_dihedral
      z0 hz0sq hz0ne hm2 e0 D hDge hz0D hz0centD
  have hez0 : e0 z0 = DihedralGroup.r
      (2 ^ (m - 1) : ZMod (2 ^ m)) :=
    unique_central_involution_of_dihedral_two_pow hm2 (e0 z0)
      (by
        rw [Subgroup.mem_center_iff]
        intro x
        obtain ⟨q, rfl⟩ := e0.surjective x
        simpa using congrArg e0
          (Subgroup.mem_center_iff.mp hz0center q))
      (by simpa using congrArg e0 hz0sq)
      (by
        intro h
        apply hz0ne
        exact e0.injective (by simpa using h))
  have ht0sq : t0 ^ 2 = 1 := by
    apply Subtype.ext
    change (g * t * g⁻¹) ^ 2 = 1
    rw [pow_two]
    calc
      (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [htt]; simp
  have hs0sq : s0 ^ 2 = 1 := by
    apply Subtype.ext
    change (g * s * g⁻¹) ^ 2 = 1
    rw [pow_two]
    calc
      (g * s * g⁻¹) * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      _ = 1 := by rw [hss]; simp
  have ht0ne : t0 ≠ 1 := by
    intro h
    apply ht.1
    have hc : g * t * g⁻¹ = 1 := congrArg Subtype.val h
    calc
      t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [hc]; simp
  have hs0ne : s0 ≠ 1 := by
    intro h
    apply hs.1
    have hc : g * s * g⁻¹ = 1 := congrArg Subtype.val h
    calc
      s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = 1 := by rw [hc]; simp
  have ht0s0 : t0 * s0 = z0 := by
    apply Subtype.ext
    change (g * t * g⁻¹) * (g * s * g⁻¹) = g * z * g⁻¹
    dsimp [z]
    group
  let T : DihedralGroup (2 ^ m) := e0 t0
  let S : DihedralGroup (2 ^ m) := e0 s0
  have hTpow : T ^ 2 = 1 := by simpa [T] using congrArg e0 ht0sq
  have hSpow : S ^ 2 = 1 := by simpa [S] using congrArg e0 hs0sq
  have hTne : T ≠ 1 := by
    intro h
    exact ht0ne (e0.injective (by simpa [T] using h))
  have hSne : S ≠ 1 := by
    intro h
    exact hs0ne (e0.injective (by simpa [S] using h))
  have hTS : T * S = DihedralGroup.r
      (2 ^ (m - 1) : ZMod (2 ^ m)) := by
    calc
      T * S = e0 (t0 * s0) := by simp [T, S]
      _ = e0 z0 := by rw [ht0s0]
      _ = DihedralGroup.r
          (2 ^ (m - 1) : ZMod (2 ^ m)) := hez0
  have rotation_eq_center
      (i : ZMod (2 ^ m))
      (hsq : (DihedralGroup.r i) ^ 2 = 1)
      (hne : DihedralGroup.r i ≠ 1) :
      DihedralGroup.r i = DihedralGroup.r
        (2 ^ (m - 1) : ZMod (2 ^ m)) := by
    have htwo : (2 : ZMod (2 ^ m)) * i = 0 := by
      have hri : DihedralGroup.r (i + i) = DihedralGroup.r 0 := by
        simpa only [pow_two, DihedralGroup.r_mul_r,
          DihedralGroup.one_def] using hsq
      injection hri with hii
      simpa only [two_mul] using hii
    rcases (zmod_two_mul_eq_zero_iff hm2 i).mp htwo with hi0 | hihalf
    · exfalso
      apply hne
      rw [hi0, DihedralGroup.r_zero]
    · rw [hihalf]
  obtain ⟨i, hTi⟩ : ∃ i : ZMod (2 ^ m), T = DihedralGroup.sr i := by
    rcases dihedralGroup_cases T with ⟨i, hTi⟩ | ⟨i, hTi⟩
    · have hTc : T = DihedralGroup.r
          (2 ^ (m - 1) : ZMod (2 ^ m)) := by
        rw [hTi]
        exact rotation_eq_center i (by simpa [hTi] using hTpow)
          (by simpa [hTi] using hTne)
      have hSone : S = 1 := by
        apply mul_left_cancel (a := DihedralGroup.r
          (2 ^ (m - 1) : ZMod (2 ^ m)))
        simpa [hTc] using hTS
      exact False.elim (hSne hSone)
    · exact ⟨i, hTi⟩
  obtain ⟨j, hSj⟩ : ∃ j : ZMod (2 ^ m), S = DihedralGroup.sr j := by
    rcases dihedralGroup_cases S with ⟨j, hSj⟩ | ⟨j, hSj⟩
    · have hSc : S = DihedralGroup.r
          (2 ^ (m - 1) : ZMod (2 ^ m)) := by
        rw [hSj]
        exact rotation_eq_center j (by simpa [hSj] using hSpow)
          (by simpa [hSj] using hSne)
      have hTone : T = 1 := by
        apply mul_right_cancel (b := DihedralGroup.r
          (2 ^ (m - 1) : ZMod (2 ^ m)))
        simpa [hSc] using hTS
      exact False.elim (hTne hTone)
    · exact ⟨j, hSj⟩
  have hrefprod : DihedralGroup.sr i * DihedralGroup.sr j =
      DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m)) := by
    simpa [hTi, hSj] using hTS
  obtain ⟨yM, hyM, hyMconj, hyMcent⟩ :=
    exists_involution_conjugator_of_opposite_dihedral_reflections
      hm2 i j hrefprod
  let y0 : P0 := e0.symm yM
  have hy0sq : y0 ^ 2 = 1 := by
    apply e0.injective
    simpa [y0] using hyM.2
  have hy0ne : y0 ≠ 1 := by
    intro h
    apply hyM.1
    calc
      yM = e0 y0 := by simp [y0]
      _ = e0 1 := by rw [h]
      _ = 1 := by simp
  have hy0conj : y0 * t0 * y0⁻¹ = s0 := by
    apply e0.injective
    simpa [y0, T, S, hTi, hSj] using hyMconj
  have hy0cent : y0 * z0 * y0⁻¹ = z0 := by
    apply e0.injective
    rw [← ht0s0, map_mul]
    simpa [y0, T, S, hTi, hSj] using hyMcent
  let y : G := g⁻¹ * (y0 : G) * g
  have hysq : y ^ 2 = 1 := by
    dsimp [y]
    rw [pow_two]
    calc
      (g⁻¹ * (y0 : G) * g) * (g⁻¹ * (y0 : G) * g) =
          g⁻¹ * ((y0 : G) * (y0 : G)) * g := by group
      _ = 1 := by
        have hy0sqG : (y0 : G) * (y0 : G) = 1 := by
          exact congrArg (fun q : P0 => (q : G))
            (by simpa [pow_two] using hy0sq)
        rw [hy0sqG]
        simp
  have hyne : y ≠ 1 := by
    intro hy
    apply hy0ne
    apply Subtype.ext
    change (y0 : G) = 1
    calc
      (y0 : G) = g * y * g⁻¹ := by dsimp [y]; group
      _ = 1 := by rw [hy]; simp
  have hyconj : y * t * y⁻¹ = s := by
    have hy0conjG : (y0 : G) * (g * t * g⁻¹) * (y0 : G)⁻¹ =
        g * s * g⁻¹ := congrArg (fun q : P0 => (q : G)) hy0conj
    dsimp [y]
    calc
      (g⁻¹ * (y0 : G) * g) * t *
          (g⁻¹ * (y0 : G) * g)⁻¹ =
          g⁻¹ * ((y0 : G) * (g * t * g⁻¹) * (y0 : G)⁻¹) * g := by group
      _ = g⁻¹ * (g * s * g⁻¹) * g := by rw [hy0conjG]
      _ = s := by group
  have hycentz : y * z * y⁻¹ = z := by
    have hy0centG : (y0 : G) * (g * z * g⁻¹) * (y0 : G)⁻¹ =
        g * z * g⁻¹ := congrArg (fun q : P0 => (q : G)) hy0cent
    dsimp [y]
    calc
      (g⁻¹ * (y0 : G) * g) * z *
          (g⁻¹ * (y0 : G) * g)⁻¹ =
          g⁻¹ * ((y0 : G) * (g * z * g⁻¹) * (y0 : G)⁻¹) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [hy0centG]
      _ = z := by group
  refine ⟨y, ⟨hyne, by simpa [pow_two] using hysq⟩, hyconj, ?_⟩
  have hyC : y ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      y * (t * s) = y * z := by rfl
      _ = (y * z * y⁻¹) * y := by group
      _ = z * y := by rw [hycentz]
      _ = (t * s) * y := by rfl
  have hyQ : y ∈ (Q : Subgroup G) := by
    have hP0map : (P0 : Subgroup G) =
        (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      rw [← hg]
      rw [Sylow.coe_subgroup_smul]
      rfl
    have hy0P0 : (y0 : G) ∈ (P0 : Subgroup G) := y0.2
    rw [hP0map] at hy0P0
    rcases Subgroup.mem_map.mp hy0P0 with ⟨q, hqQ, hqval⟩
    have hyq : y = q := by
      dsimp [y]
      rw [← hqval]
      change g⁻¹ * (g * q * g⁻¹) * g = q
      group
    rw [hyq]
    exact hqQ
  let Qc : Subgroup G := (Q : Subgroup G) ⊓ C
  have hQcp : IsPGroup 2 Qc := Q.isPGroup'.to_inf_left
  have hPGleQc : PG ≤ Qc := by
    intro x hx
    exact ⟨hPGQ hx, hPGleC hx⟩
  have hQcC : Qc ≤ C := inf_le_right
  let QcC : Subgroup C := Qc.subgroupOf C
  have hQcCp : IsPGroup 2 QcC := by
    let eQc : QcC ≃* Qc := Subgroup.subgroupOfEquivOfLe hQcC
    exact IsPGroup.of_equiv hQcp eQc.symm
  obtain ⟨R, hQcR⟩ := IsPGroup.exists_le_sylow (G := C) (p := 2) hQcCp
  have hRcard : Nat.card (R : Subgroup C) = Nat.card (PC : Subgroup C) := by
    let eR : R ≃* PC := Sylow.equiv R PC
    exact Nat.card_congr eR.toEquiv
  have hQc_card : Nat.card Qc ≤ Nat.card PG := by
    calc
      Nat.card Qc = Nat.card QcC := by
        exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQcC).toEquiv).symm
      _ ≤ Nat.card (R : Subgroup C) := Subgroup.card_le_of_le hQcR
      _ = Nat.card (PC : Subgroup C) := hRcard
      _ = Nat.card PG := hPGcard.symm
  have hPGQc : PG = Qc :=
    Subgroup.eq_of_le_of_card_ge hPGleQc hQc_card
  have hyPG : y ∈ PG := by
    have hyQc : y ∈ Qc := ⟨hyQ, hyC⟩
    simpa [hPGQc] using hyQc
  change y ∈ ((PC : Subgroup C).map C.subtype)
  exact hyPG

/-- An involutory conjugator inside a prescribed Sylow subgroup of the
product centralizer.

If distinct commuting involutions have a product centralizer of order
divisible by eight, a Sylow subgroup of that centralizer transports into an
ambient dihedral Sylow subgroup.  The product is then the central rotation and
the two involutions are opposite reflections, so an involution inside the
given Sylow subgroup of the product centralizer interchanges them. -/
public theorem exists_involution_conjugator_in_product_centralizer_of_dihedral_sylow_in_sylow
    {G : Type u} [Group G] [Finite G]
    (P0 : Sylow 2 G) {m : ℕ}
    (e0 : P0 ≃* DihedralGroup (2 ^ m))
    (t s : G) (ht : IsInvolution t) (hs : IsInvolution s)
    (hts : Commute t s) (htsne : t ≠ s)
    (h8 : 8 ∣ Nat.card
      (Subgroup.centralizer ({t * s} : Set G)))
    (PC : Sylow 2 (Subgroup.centralizer ({t * s} : Set G)))
    (hV : (Subgroup.zpowers t ⊔ Subgroup.zpowers s).subgroupOf
      (Subgroup.centralizer ({t * s} : Set G)) ≤
      (PC : Subgroup (Subgroup.centralizer ({t * s} : Set G)))) :
    ∃ y : G, IsInvolution y ∧
      y * t * y⁻¹ = s ∧
      y ∈ ((PC : Subgroup (Subgroup.centralizer ({t * s} : Set G))).map
        (Subgroup.centralizer ({t * s} : Set G)).subtype) :=
  exists_involution_conjugator_in_product_centralizer_of_dihedral_sylow_core
    P0 e0 t s ht hs hts htsne h8 PC hV

/-- An involutory conjugator inside the product centralizer of two distinct
commuting involutions whose product has a centralizer of order divisible by
eight. -/
public theorem exists_involution_conjugator_in_product_centralizer_of_dihedral_sylow
    {G : Type u} [Group G] [Finite G]
    (P0 : Sylow 2 G) {m : ℕ}
    (e0 : P0 ≃* DihedralGroup (2 ^ m))
    (t s : G) (ht : IsInvolution t) (hs : IsInvolution s)
    (hts : Commute t s) (htsne : t ≠ s)
    (h8 : 8 ∣ Nat.card
      (Subgroup.centralizer ({t * s} : Set G))) :
    ∃ y : G, IsInvolution y ∧
      y * t * y⁻¹ = s ∧
      y ∈ Subgroup.centralizer ({t * s} : Set G) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := Subgroup.centralizer ({t * s} : Set G)
  have htC : t ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      t * (t * s) = s := by
        rw [← mul_assoc]
        simpa [pow_two] using congrArg (fun x : G => x * s) ht.2
      _ = (t * s) * t := by
        rw [mul_assoc, ← hts.eq, ← mul_assoc]
        rw [show t * t = 1 by simpa [pow_two] using ht.2, one_mul]
  have hsC : s ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      s * (t * s) = t := by
        rw [← mul_assoc, ← hts.eq, mul_assoc]
        rw [show s * s = 1 by simpa [pow_two] using hs.2, mul_one]
      _ = (t * s) * s := by
        rw [mul_assoc]
        rw [show s * s = 1 by simpa [pow_two] using hs.2, mul_one]
  let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s
  have hVleC : V ≤ C := by
    apply sup_le
    · exact Subgroup.zpowers_le.mpr htC
    · exact Subgroup.zpowers_le.mpr hsC
  have hVp : IsPGroup 2 V := by
    have htord : orderOf t = 2 := orderOf_eq_prime ht.2 ht.1
    have hsord : orderOf s = 2 := orderOf_eq_prime hs.2 hs.1
    have hAp : IsPGroup 2 (Subgroup.zpowers t : Subgroup G) := by
      apply IsPGroup.of_card (n := 1)
      simp [Nat.card_zpowers, htord]
    have hBp : IsPGroup 2 (Subgroup.zpowers s : Subgroup G) := by
      apply IsPGroup.of_card (n := 1)
      simp [Nat.card_zpowers, hsord]
    have hsNormA : s ∈
        Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      change Subgroup.zpowers (s * t * s⁻¹) = Subgroup.zpowers t
      have hconj : s * t * s⁻¹ = t := by
        rw [inv_eq_of_mul_eq_one_right
          (show s * s = 1 by simpa [pow_two] using hs.2)]
        calc
          s * t * s = t * (s * s) := by rw [← hts.eq]; group
          _ = t := by
            rw [show s * s = 1 by simpa [pow_two] using hs.2, mul_one]
      rw [hconj]
    have hBnormA : Subgroup.zpowers s ≤
        Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr hsNormA
    exact IsPGroup.to_sup_of_normal_left' hAp hBp hBnormA
  let VC : Subgroup C := V.subgroupOf C
  have hVCp : IsPGroup 2 VC := by
    let eVC : VC ≃* V := Subgroup.subgroupOfEquivOfLe hVleC
    exact IsPGroup.of_equiv hVp eVC.symm
  obtain ⟨PC, hVCPC⟩ := IsPGroup.exists_le_sylow hVCp
  rcases exists_involution_conjugator_in_product_centralizer_of_dihedral_sylow_core
      P0 e0 t s ht hs hts htsne h8 PC
      (by simpa [C, V, VC] using hVCPC) with ⟨y, hyI, hyconj, hyPG⟩
  refine ⟨y, hyI, hyconj, ?_⟩
  change y ∈ C
  exact Subgroup.map_subtype_le (PC : Subgroup C) hyPG

end CFSG.GorensteinWalter
