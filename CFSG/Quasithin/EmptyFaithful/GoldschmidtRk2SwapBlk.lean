module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclA38
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclG
public import CFSG.Quasithin.EmptyFaithful.S151S4D
public import CFSG.Quasithin.Background.G2A5Iso
public import CFSG.Quasithin.EmptyFaithful.R3cBase

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.Quasithin.S151S4
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Chi0

variable {G : Type} [Group G]

theorem chi0Block_of_c126Third [Finite G] {L S : Subgroup G}
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hS2 : IsPGroup 2 ↥S) (hperf : ⁅L, L⁆ = L)
    (hqs : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (h3 : C126Third (L ⊔ S) S) :
    IsChi0Block (L ⊔ S) L := by
  obtain ⟨r, K, hr, hblock, hcomm, hres, -, -⟩ := h3
  rw [twoResidual_sup_eq_self hSN hS2 hperf] at hres
  have hKL : ∀ i, K i ≤ L := fun i => by
    calc K i ≤ ⨆ j, K j := le_iSup K i
      _ = L := hres.symm
  have hKN : ∀ i, L ≤ Subgroup.normalizer (K i : Set G) := by
    intro i
    calc L = ⨆ j, K j := hres
      _ ≤ Subgroup.normalizer (K i : Set G) := by
        refine iSup_le fun j => ?_
        by_cases hij : j = i
        · subst hij
          exact Subgroup.le_normalizer
        · have hc : ⁅K j, K i⁆ = ⊥ := hcomm j i hij
          exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans
            (Subgroup.centralizer_le_normalizer _)
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hex : ∃ i, ((K i).subgroupOf L).map π = ⊤ := by
    by_contra hne
    push Not at hne
    have hcen : ∀ i, ((K i).subgroupOf L).map π ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      intro i
      have hnorm : ((K i).subgroupOf L).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (hKL i)).mpr (hKN i)
      have hmn : (((K i).subgroupOf L).map π).Normal := hnorm.map π hπs
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs hmn with h | h
      · exact absurd h (hne i)
      · exact h
    have hC : L ≤ ((Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).comap π).map L.subtype := by
      calc L = ⨆ j, K j := hres
        _ ≤ _ := by
          refine iSup_le fun j x hx => ?_
          have hxL : x ∈ L := hKL j hx
          refine ⟨⟨x, hxL⟩, ?_, rfl⟩
          exact hcen j ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hall : ∀ q : ↥L ⧸ CFSG.pCore 2 ↥L, q ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      intro q
      obtain ⟨l, rfl⟩ := hπs q
      obtain ⟨c, hc, hcl⟩ := hC l.2
      have : c = l := Subtype.ext hcl
      rw [← this]
      exact hc
    have hsub : Subsingleton ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b => exact QuotientGroup.eq.mpr (hall _)
    have hnt : Nontrivial ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      hqs.2.1.toNontrivial
    exact false_of_nontrivial_of_subsingleton
      ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  obtain ⟨i, hi⟩ := hex
  have hOp : IsPGroup 2 ↥(pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hLKi : L ≤ K i := by
    have h2 : twoResidual L ≤ K i := by
      refine twoResidual_le_of_isTwoQuotient (hKL i) (hKN i) ?_
      intro y hy
      have hmem : π ⟨y, hy⟩ ∈ ((K i).subgroupOf L).map π := hi ▸ Subgroup.mem_top _
      obtain ⟨x, hx, hxy⟩ := hmem
      have hker : x⁻¹ * ⟨y, hy⟩ ∈ CFSG.pCore 2 ↥L := by
        have h3 : π (x⁻¹ * ⟨y, hy⟩) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff _).mp h3
      have hker' : ((x⁻¹ * ⟨y, hy⟩ : ↥L) : G) ∈ pCoreOf 2 L :=
        ⟨_, by assumption, rfl⟩
      obtain ⟨m, hm⟩ := hOp ⟨_, hker'⟩
      have hm' : ((x⁻¹ * ⟨y, hy⟩ : ↥L) : G) ^ 2 ^ m = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      have hxK : (x : G) ∈ K i := Subgroup.mem_subgroupOf.mp hx
      have hoN : ((x⁻¹ * ⟨y, hy⟩ : ↥L) : G) ∈ Subgroup.normalizer (K i : Set G) :=
        hKN i (CFSG.LieType.BorelTits.pCoreOf_le 2 L hker')
      obtain ⟨q, hq, hqe⟩ := zb_mul_pow_mem hoN hxK (2 ^ m)
      refine ⟨m, ?_⟩
      have hy' : y = (x : G) * ((x⁻¹ * ⟨y, hy⟩ : ↥L) : G) := by
        simp
      rw [hy', hqe, hm', mul_one]
      exact hq
    rw [← twoResidual_eq_self_of_perfect hperf]
    exact h2
  have hKiL : K i = L := le_antisymm (hKL i) hLKi
  have hch := (hblock i).1
  rwa [hKiL] at hch

end Chi0

section TypeB

variable {G : Type} [Group G] [Finite G]

theorem not_c126Third_of_typeB {L S : Subgroup G} (hB : ListB15120' L)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hS2 : IsPGroup 2 ↥S) (hperf : ⁅L, L⁆ = L)
    (hqs : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) : ¬ C126Third (L ⊔ S) S := by
  intro h3
  obtain ⟨-, hty⟩ := chi0Block_of_c126Third hSN hS2 hperf hqs h3
  have hpg : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hty with ⟨n, hn, F, hF, hFin, hcard, α, hαs, hαk, -⟩ | ⟨α, hαs, hαk, -⟩ |
      ⟨α, hαs, hαk, -⟩
  ·
    have hcardN : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
    have : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hcardN
    obtain ⟨hpsl, -⟩ := levi_modO2 hn hcardN α hαs (hpg.to_le hαk.le)
    exact rankTwoNotA38Type_holds G L hB (Or.inl ⟨n, hpsl⟩)
  ·
    have hcomm3 : IsMulCommutative (alternatingGroup (Fin 3)) :=
      alternatingGroup.isMulCommutative_of_card_le_three (by simp)
    have hc : ∀ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b = b * a := by
      intro a b
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      have h1 : α (x * y) = α (y * x) := by
        rw [map_mul, map_mul]
        exact hcomm3.is_comm.comm (α x) (α y)
      have h2 : (x * y)⁻¹ * (y * x) ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      rw [hαk] at h2
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact QuotientGroup.eq.mpr h2
    have hcen : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊤ := by
      rw [Subgroup.eq_top_iff']
      exact fun x => Subgroup.mem_center_iff.mpr fun g => hc g x
    have hS : IsSimpleGroup ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      hqs.2.1
    obtain ⟨a, b, hab⟩ := hS.toNontrivial.exists_pair_ne
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    apply hab
    rw [QuotientGroup.eq, hcen]
    exact Subgroup.mem_top _
  ·
    obtain ⟨e₀, -⟩ := A5Model.exists_mulEquiv_A5_SL2_four
    let g : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) := e₀.toMonoidHom.comp α
    have hgs : Function.Surjective g := e₀.surjective.comp hαs
    have hgk : g.ker = α.ker := by
      ext x
      simp [g, MonoidHom.mem_ker]
    have hK : Nat.card (GaloisField 2 2) = 2 ^ 2 := by rw [A5Model.card_gf4]; norm_num
    have hker : IsPGroup 2 g.ker := by
      rw [hgk]
      exact hpg.to_le hαk.le
    obtain ⟨hpsl, -⟩ := levi_modO2 (le_refl 2) hK g hgs hker
    exact rankTwoNotA38Type_holds G L hB (Or.inl ⟨2, hpsl⟩)

end TypeB

end CFSG.Quasithin.Rk2
