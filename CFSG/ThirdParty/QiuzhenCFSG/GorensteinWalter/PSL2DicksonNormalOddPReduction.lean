module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupAlternating
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupAlternatingFour
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupPGL2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupPSL2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupSymmetricFour
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
import Mathlib.GroupTheory.Complement
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Dickson reduction for invariant odd-prime subgroups of `PSL₂`

Let `M` contain a Sylow `2`-subgroup of odd `PSL₂(F)`, and let `P` be a
normal odd-prime subgroup of `M`.  Dickson's classification shows that `P`
is centralized by the central Sylow involution unless `M` is one of the
dihedral alternatives.  The latter is retained explicitly as the sole
remaining local model core.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

open BenderSuzuki.MatrixGroups

universe u

/-- In Dickson's classification of a subgroup containing a noncyclic Sylow
`2`-subgroup, every branch except the dihedral branch forces a normal
odd-prime subgroup to be centralized by the central Sylow involution. -/
public theorem psl2_normal_oddP_dihedral_or_centralized_of_contains_sylow
    {F : Type u} [Field F] [Finite F]
    {r f p : ℕ} [Fact r.Prime] [Fact p.Prime]
    (hFcard : Nat.card F = r ^ f) (hrodd : Odd r) (hpodd : Odd p)
    (S : Sylow 2 (PSL2MatrixGroup F))
    (M P : Subgroup (PSL2MatrixGroup F))
    (hSM : (S : Subgroup (PSL2MatrixGroup F)) ≤ M)
    (hPleM : P ≤ M)
    (hPnormal : (P.subgroupOf M).Normal)
    (hPp : IsPGroup p P)
    {t : PSL2MatrixGroup F} (htS : t ∈ (S : Subgroup (PSL2MatrixGroup F)))
    (_htcenter : (⟨t, htS⟩ : S) ∈ Subgroup.center S) :
    (∃ z : ℕ, Nat.card M = 2 * z ∧ Nonempty (M ≃* DihedralGroup z)) ∨
      P ≤ Subgroup.centralizer ({t} : Set (PSL2MatrixGroup F)) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf_ne_zero : f ≠ 0 := by
    intro hf_zero
    have hcard_one : Nat.card F = 1 := by
      simpa [hf_zero, pow_zero] using hFcard
    exact (Nat.ne_of_gt (Finite.one_lt_card (α := F))) hcard_one
  have hoddF : IsOddPrimePower (Nat.card F) :=
    ⟨r, f, Fact.out, hrodd, Nat.one_le_iff_ne_zero.mpr hf_ne_zero, hFcard⟩
  have hSnotcyc : ¬ IsCyclic S := by
    rcases psl2_odd_hasDihedralSylowTwo_model F hoddF S with
      ⟨m, hm, ⟨eS⟩⟩
    intro hScyc
    have hDcyc : IsCyclic (DihedralGroup (2 ^ m)) := eS.isCyclic.mp hScyc
    have hpow_ne_one : 2 ^ m ≠ 1 := by
      exact ne_of_gt (Nat.one_lt_pow (Nat.ne_of_gt hm) (by norm_num))
    exact DihedralGroup.not_isCyclic hpow_ne_one hDcyc
  let PM : Subgroup M := P.subgroupOf M
  have hPMp : IsPGroup p PM :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPleM).symm
  have hPbot_of_PMbot : PM = ⊥ → P = ⊥ := by
    intro hPMbot
    apply le_bot_iff.mp
    intro x hx
    have hxPM : (⟨x, hPleM hx⟩ : M) ∈ PM :=
      Subgroup.mem_subgroupOf.mpr hx
    have hxone : (⟨x, hPleM hx⟩ : M) = 1 := by
      rw [hPMbot] at hxPM
      exact Subgroup.mem_bot.mp hxPM
    exact congrArg Subtype.val hxone
  have hcentral_of_Pbot : P = ⊥ →
      P ≤ Subgroup.centralizer ({t} : Set (PSL2MatrixGroup F)) := by
    intro hPbot x hx
    have hxone : x = 1 := by
      rw [hPbot] at hx
      exact Subgroup.mem_bot.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y _hy
    simp [hxone]
  let SN : Subgroup M := (S : Subgroup (PSL2MatrixGroup F)).subgroupOf M
  have hSN2 : IsPGroup 2 SN :=
    S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm
  have hS_not_rgroup : ¬ IsPGroup r (S : Subgroup (PSL2MatrixGroup F)) := by
    intro hSr
    have hr_ne_two : 2 ≠ r := by
      intro h
      have hr_two : r = 2 := h.symm
      subst r
      exact hrodd.not_two_dvd_nat (by simp)
    have hcoprime : Nat.Coprime (Nat.card S) (Nat.card S) :=
      IsPGroup.coprime_card_of_ne 2 r hr_ne_two
        (S : Subgroup (PSL2MatrixGroup F))
        (S : Subgroup (PSL2MatrixGroup F)) S.isPGroup' hSr
    have hScard_one : Nat.card S = 1 :=
      hcoprime.eq_one_of_dvd (dvd_refl _)
    rcases psl2_odd_hasDihedralSylowTwo_model F hoddF S with
      ⟨m, _hm, ⟨eS⟩⟩
    have hScard : Nat.card S = 2 * 2 ^ m := by
      calc
        Nat.card S = Nat.card (DihedralGroup (2 ^ m)) :=
          Nat.card_congr eS.toEquiv
        _ = 2 * 2 ^ m := DihedralGroup.nat_card
    rw [hScard_one] at hScard
    have hpow_pos : 0 < 2 ^ m := pow_pos (by norm_num) m
    omega
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := r) (f := f) hFcard M with
    hElementary | hCyclic | hDihedral | hA4 | hS4 | hA5 |
      hSemidirect | hPSL | hPGL
  · exfalso
    have hMr : IsPGroup r M := IsElementaryAbelian.isPGroup r M
    have hSNr : IsPGroup r SN := hMr.to_subgroup SN
    have hSr : IsPGroup r (S : Subgroup (PSL2MatrixGroup F)) :=
      hSNr.of_equiv (Subgroup.subgroupOfEquivOfLe hSM)
    exact hS_not_rgroup hSr
  · exfalso
    rcases hCyclic with ⟨_z, _hz, _hcard, hMcyc⟩
    let : IsCyclic M := hMcyc
    exact hSnotcyc (Subgroup.isCyclic_of_le hSM)
  · exact Or.inl
      ⟨hDihedral.choose, hDihedral.choose_spec.2.1,
        hDihedral.choose_spec.2.2⟩
  · right
    have hPMbot : PM = ⊥ :=
      normal_pSubgroup_eq_bot_of_mulEquiv_alternatingGroup_four
        hA4.2 p Fact.out hpodd PM hPnormal hPMp
    exact hcentral_of_Pbot (hPbot_of_PMbot hPMbot)
  · right
    have hPMbot : PM = ⊥ :=
      normal_pSubgroup_eq_bot_of_mulEquiv_perm_four
        hS4.2 p Fact.out hpodd PM hPnormal hPMp
    exact hcentral_of_Pbot (hPbot_of_PMbot hPMbot)
  · right
    have hPMbot : PM = ⊥ :=
      normal_pSubgroup_eq_bot_of_mulEquiv_alternatingGroup
        (n := 5) (by norm_num) hA5.2 p Fact.out hpodd PM hPnormal hPMp
    exact hcentral_of_Pbot (hPbot_of_PMbot hPMbot)
  · exfalso
    rcases hSemidirect with
      ⟨m, ccard, _hccard_dvd, _hccard_ambient, N, C,
        hNnormal, hNelem, _hNcard, hCcyc, _hCcard, hdisj, hjoin⟩
    let : N.Normal := hNnormal
    have hcomp : N.IsComplement' C := by
      refine ⟨Subgroup.mul_injective_of_disjoint hdisj, ?_⟩
      intro g
      have hg : (g : M) ∈ (N : Set M) * (C : Set M) := by
        rw [← Subgroup.normal_mul N C, hjoin]
        trivial
      rcases hg with ⟨n, hn, c, hc, hnc⟩
      exact ⟨⟨⟨n, hn⟩, ⟨c, hc⟩⟩, hnc⟩
    let eQ : M ⧸ N ≃* C := hcomp.symm.QuotientMulEquiv
    let : IsCyclic (M ⧸ N) := eQ.isCyclic.mpr hCcyc
    have hNr : IsPGroup r N := IsElementaryAbelian.isPGroup r N
    have hr_ne_two : 2 ≠ r := by
      intro h
      have hr_two : r = 2 := h.symm
      subst r
      exact hrodd.not_two_dvd_nat (by simp)
    have hcoprime : Nat.Coprime (Nat.card SN) (Nat.card N) :=
      IsPGroup.coprime_card_of_ne 2 r hr_ne_two SN N hSN2 hNr
    have hinf : SN ⊓ N = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard hcoprime).eq_bot
    let q : M →* M ⧸ N := QuotientGroup.mk' N
    let qS : SN →* M ⧸ N := q.comp SN.subtype
    have hqSker : qS.ker = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxq : q (x : M) = 1 := by simpa [qS] using hx
      have hxN : (x : M) ∈ N :=
        (QuotientGroup.eq_one_iff (N := N) (x : M)).mp hxq
      have hxinf : (x : M) ∈ SN ⊓ N := ⟨x.property, hxN⟩
      have hxone : (x : M) = 1 := by
        have hxbot : (x : M) ∈ (⊥ : Subgroup M) := by
          rw [← hinf]
          exact hxinf
        exact Subgroup.mem_bot.mp hxbot
      exact Subtype.ext hxone
    have hqSinj : Function.Injective qS :=
      (MonoidHom.ker_eq_bot_iff qS).mp hqSker
    have hSNcyc : IsCyclic SN := isCyclic_of_injective qS hqSinj
    have hScyc : IsCyclic S :=
      (Subgroup.subgroupOfEquivOfLe hSM).isCyclic.mp hSNcyc
    exact hSnotcyc hScyc
  · right
    rcases hPSL with ⟨m, hm, _hmdiv, ⟨eM⟩⟩
    let K := GaloisField r m
    have hKcard : Nat.card K = r ^ m := GaloisField.card r m hm
    have hKodd : IsOddPrimePower (Nat.card K) :=
      ⟨r, m, Fact.out, hrodd, Nat.one_le_iff_ne_zero.mpr hm, hKcard⟩
    let Q : Subgroup (PSL2 K) := PM.map eM.toMonoidHom
    have hQnormal : Q.Normal := hPnormal.map eM.toMonoidHom eM.surjective
    have hQp : IsPGroup p Q := IsPGroup.map hPMp eM.toMonoidHom
    have hQbot : Q = ⊥ :=
      normal_pSubgroup_eq_bot_of_psl2_odd K hKodd p Fact.out hpodd Q hQnormal hQp
    have hPMbot : PM = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective
        (H := PM) (f := eM.toMonoidHom) eM.injective).mp
      simpa [Q] using hQbot
    exact hcentral_of_Pbot (hPbot_of_PMbot hPMbot)
  · right
    rcases hPGL with ⟨m, hm, _hmdiv, ⟨eM⟩⟩
    let K := GaloisField r m
    have hKcard : Nat.card K = r ^ m := GaloisField.card r m hm
    have hKodd : IsOddPrimePower (Nat.card K) :=
      ⟨r, m, Fact.out, hrodd, Nat.one_le_iff_ne_zero.mpr hm, hKcard⟩
    let Q : Subgroup (PGL2 K) := PM.map eM.toMonoidHom
    have hQnormal : Q.Normal := hPnormal.map eM.toMonoidHom eM.surjective
    have hQp : IsPGroup p Q := IsPGroup.map hPMp eM.toMonoidHom
    have hQbot : Q = ⊥ :=
      normal_pSubgroup_eq_bot_of_pgl2_odd K hKodd p Fact.out hpodd Q hQnormal hQp
    have hPMbot : PM = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective
        (H := PM) (f := eM.toMonoidHom) eM.injective).mp
      simpa [Q] using hQbot
    exact hcentral_of_Pbot (hPbot_of_PMbot hPMbot)

end CFSG.GorensteinWalter
