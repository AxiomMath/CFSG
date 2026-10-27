module

public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_top_of_sup_pCore {L : Subgroup G}
    (h2 : ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤) (N : Subgroup ↥L)
    [N.Normal] (h : N ⊔ CFSG.pCore 2 ↥L = ⊤) : N = ⊤ := by
  refine h2 N ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    have hx : x ∈ N ⊔ CFSG.pCore 2 ↥L := h ▸ Subgroup.mem_top x
    obtain ⟨n, hn, p, hp, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨p, hp⟩
    refine ⟨k, ?_⟩
    have hpk : p ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hn1 : (QuotientGroup.mk n : ↥L ⧸ N) = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [QuotientGroup.mk_mul, hn1, one_mul, ← QuotientGroup.mk_pow, hpk, QuotientGroup.mk_one]

theorem mem_cComp_of_quasisimple_quotient [Finite G] {L Y : Subgroup G}
    (h2 : ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hsub : IsSubnormal L Y) :
    L ∈ cComp Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have key : ∀ (N : Subgroup ↥L) [N.Normal], N.map π = ⊤ → N = ⊤ := by
    intro N _ hN
    apply eq_top_of_sup_pCore h2 N
    have := Subgroup.comap_map_eq π N
    rw [hN, Subgroup.comap_top] at this
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L)]
    exact this.symm
  have hperf : ⁅L, L⁆ = L := by
    rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
    apply key
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hπ]
    exact hq.1.commutator_eq_top
  have hne : L ≠ ⊥ := by
    intro hb
    obtain ⟨a, b, hab⟩ := (CFSG.LocalCores.isQuasisimple_nontrivial hq).exists_pair_ne
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hxy : x = y := by
      apply Subtype.ext
      rw [(Subgroup.eq_bot_iff_forall L).1 hb _ x.2, (Subgroup.eq_bot_iff_forall L).1 hb _ y.2]
    rw [hxy]
  refine ⟨hne, hperf, hsub, fun K hKL hKne hKperf hKsub => ?_⟩
  have hKL' : IsSubnormal K L := A3.subnormal_of_le_of_le hKsub hKL.le (A3.subnormal_le hsub)
  obtain ⟨P, hPL, hPn, hKP⟩ := A3.subnormal_exists_normal_of_lt hKL' hKL
  have hPm : ((P.subgroupOf L).map π).Normal := Subgroup.Normal.map hPn π hπ
  have hP1 : P.subgroupOf L ≠ ⊤ := fun h =>
    hPL.ne (le_antisymm hPL.le (Subgroup.subgroupOf_eq_top.1 h))
  have hcen : (P.subgroupOf L).map π ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hPm with h | h
    · exact absurd (key (P.subgroupOf L) h) hP1
    · exact h
  have hKQ : K ≤ pCoreOf 2 L := by
    rw [← hKperf]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    set a' : ↥L := ⟨a, hPL.le (hKP ha)⟩
    set b' : ↥L := ⟨b, hPL.le (hKP hb)⟩
    have ha' : π a' ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := hcen ⟨a', hKP ha, rfl⟩
    have h1 : ⁅π a', π b'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 ((Subgroup.mem_center_iff.1 ha' (π b')).symm)
    have h2 : π ⁅a', b'⁆ = 1 := by rw [map_commutatorElement, h1]
    have h3 : ⁅a', b'⁆ ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).1 h2
    exact ⟨⁅a', b'⁆, h3, rfl⟩
  have hKp : IsPGroup 2 K := (LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hKQ
  have hnil : Group.IsNilpotent ↥K := hKp.isNilpotent
  have hnt : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hKne
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥K)
  have hperfK : commutator ↥K = ⊤ := (Subgroup.isPerfect_iff.2 hKperf).commutator_eq_top
  exact absurd hperfK hlt.ne

end CFSG.Quasithin.H13
