module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105U3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Grow
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102AltTen
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem ncl_le {N X : Subgroup G} (hX : X ≤ N) : ncl N X ≤ N := by
  unfold ncl
  refine (closure_le N).mpr ?_
  rintro y ⟨g, hg, x, hx, rfl⟩
  exact N.mul_mem (N.mul_mem hg (hX hx)) (N.inv_mem hg)

private theorem conj_mem_ncl {N X : Subgroup G} {g y : G} (hg : g ∈ N) (hy : y ∈ ncl N X) :
    g * y * g⁻¹ ∈ ncl N X := by
  unfold ncl at hy ⊢
  refine Subgroup.closure_induction (p := fun z _ => g * z * g⁻¹ ∈
    Subgroup.closure {y : G | ∃ g ∈ N, ∃ x ∈ X, y = g * x * g⁻¹}) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨a, ha, x, hx, rfl⟩
    exact Subgroup.subset_closure ⟨g * a, N.mul_mem hg ha, x, hx, by group⟩
  · simp
  · intro a b _ _ ha hb
    rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ha

private theorem ncl_normal {N X : Subgroup G} (hX : X ≤ N) :
    N ≤ normalizer (ncl N X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using conj_mem_ncl hg hx
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · simpa using conj_mem_ncl (N := N) (X := X) (g := g⁻¹) (N.inv_mem hg) hy
    · show g * (g⁻¹ * y * g) * g⁻¹ = y
      group

private theorem pCoreOf_two_le_relPPrimeCore_three (N : Subgroup G) :
    pCoreOf 2 N ≤ relPPrimeCore 3 N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.pCoreOf_two_le_relPPrimeCore
    (by norm_num) N

private theorem le_normalizer_pCoreOf_self (N : Subgroup G) :
    N ≤ normalizer (pCoreOf 2 N : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N

private theorem le_normalizer_relPPrimeCore_self (N : Subgroup G) :
    N ≤ normalizer (relPPrimeCore 3 N : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N)).mp
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three N)

private theorem kOf8103_le_N {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : F08.KOf8103 L B ≤ N :=
  (c.toCex8105.memH.2.2.1).trans c.toCex8105.memN.2

private theorem b'_le_N {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : B' ≤ N :=
  c.toLines8105.le.trans (kOf8103_le_N c)

private theorem commutator_ncl_relPPrimeCore_le (hS : KSuzukiL2) {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) :
    ⁅ncl N B', relPPrimeCore 3 N⁆ ≤ pCoreOf 2 N := by
  have hKI : ⁅relPPrimeCore 3 N, F08.KOf8103 L B⁆ ≤ pCoreOf 2 N :=
    commutator_relPPrimeCore_le hS c
  have hgen : ∀ x, x ∈ {y : G | ∃ g ∈ N, ∃ b ∈ B', y = g * b * g⁻¹} →
      ∀ y ∈ relPPrimeCore 3 N, ⁅x, y⁆ ∈ pCoreOf 2 N := by
    rintro x ⟨g, hg, b, hb, rfl⟩ y hy
    have hxK : g * b * g⁻¹ ∈ (F08.KOf8103 L B).map (MulAut.conj g).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨b, c.toLines8105.le hb, ?_⟩
      simp [MulAut.conj_apply]
    have hIeq : (relPPrimeCore 3 N).map (MulAut.conj g).toMonoidHom = relPPrimeCore 3 N :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_relPPrimeCore_self N hg)
    have hQeq : (pCoreOf 2 N).map (MulAut.conj g).toMonoidHom = pCoreOf 2 N :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_pCoreOf_self N hg)
    have hmap : ⁅relPPrimeCore 3 N, (F08.KOf8103 L B).map (MulAut.conj g).toMonoidHom⁆ ≤
        pCoreOf 2 N := by
      have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hKI
      rw [Subgroup.map_commutator, hIeq, hQeq] at h
      exact h
    have hcomm : ⁅(F08.KOf8103 L B).map (MulAut.conj g).toMonoidHom,
        relPPrimeCore 3 N⁆ ≤ pCoreOf 2 N := by
      rw [Subgroup.commutator_comm]
      exact hmap
    exact hcomm (Subgroup.commutator_mem_commutator hxK hy)
  have hnormN : Subgroup.closure {y : G | ∃ g ∈ N, ∃ b ∈ B', y = g * b * g⁻¹} ≤
      normalizer (pCoreOf 2 N : Set G) := by
    change ncl N B' ≤ normalizer (pCoreOf 2 N : Set G)
    exact (ncl_le (b'_le_N c)).trans (le_normalizer_pCoreOf_self N)
  have hnormI : Subgroup.closure (relPPrimeCore 3 N : Set G) ≤
      normalizer (pCoreOf 2 N : Set G) := by
    rw [closure_eq (relPPrimeCore 3 N)]
    exact (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le
      N).trans (le_normalizer_pCoreOf_self N)
  have h := TauCeti.commutator_closure_closure_le
    (X := {y : G | ∃ g ∈ N, ∃ b ∈ B', y = g * b * g⁻¹})
    (Y := (relPPrimeCore 3 N : Set G)) (N := pCoreOf 2 N) hnormN hnormI hgen
  rwa [closure_eq (relPPrimeCore 3 N)] at h

private theorem pow_three_eq_one_of_mem_b' {D : Data G} {L P B B' D₀ H N : Subgroup G}
    {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) {b : G} (hb : b ∈ B') : b ^ 3 = 1 := by
  have hcard : Nat.card ↥B' = 3 := c.toLines8105.notB'.1
  have hdvd : orderOf b ∣ 3 := by
    have h := orderOf_dvd_natCard (⟨b, hb⟩ : ↥B')
    rwa [Subgroup.orderOf_mk, hcard] at h
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

private theorem normal_subgroupOf_pCoreOf_ncl {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) :
    ((pCoreOf 2 N ⊓ ncl N B').subgroupOf (ncl N B')).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    (inf_le_right : pCoreOf 2 N ⊓ ncl N B' ≤ ncl N B')]
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq,
    Subgroup.map_inf _ _ _ (MulAut.conj x).injective]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_pCoreOf_self N ((ncl_le (b'_le_N c)) hx)),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (ncl_normal (b'_le_N c) ((ncl_le (b'_le_N c)) hx))]

private theorem normal_subgroupOf_relPPrimeCore_ncl {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) :
    ((relPPrimeCore 3 N ⊓ ncl N B').subgroupOf (ncl N B')).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    (inf_le_right : relPPrimeCore 3 N ⊓ ncl N B' ≤ ncl N B')]
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq,
    Subgroup.map_inf _ _ _ (MulAut.conj x).injective]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_relPPrimeCore_self N ((ncl_le (b'_le_N c)) hx)),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (ncl_normal (b'_le_N c) ((ncl_le (b'_le_N c)) hx))]

private noncomputable def quotient_pCore_equiv_of_surjective {A B : Type} [Group A] [Group B]
    [Finite A] (f : A →* B) (hf : Function.Surjective f) (hker : f.ker ≤ CFSG.pCore 2 A) :
    (A ⧸ CFSG.pCore 2 A) ≃* (B ⧸ CFSG.pCore 2 B) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : (CFSG.pCore 2 A).map f = CFSG.pCore 2 B := by
    refine le_antisymm ?_ ?_
    · exact le_sSup ⟨Subgroup.Normal.map CFSG.pCore_normal f hf,
        IsPGroup.map CFSG.pCore_isPGroup f⟩
    · have hcomap : (CFSG.pCore 2 B).comap f ≤ CFSG.pCore 2 A :=
        le_sSup ⟨CFSG.pCore_normal.comap f,
          IsPGroup.comap_of_ker_isPGroup CFSG.pCore_isPGroup f
            ((CFSG.pCore_isPGroup (G := A)).to_le hker)⟩
      exact (Subgroup.map_comap_eq_self_of_surjective hf (CFSG.pCore 2 B)).symm.trans_le
        (Subgroup.map_mono hcomap)
  let g : A →* B ⧸ CFSG.pCore 2 B := (QuotientGroup.mk' (CFSG.pCore 2 B)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hker' : g.ker = CFSG.pCore 2 A := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, ← Subgroup.mem_comap]
    have hcomap : (CFSG.pCore 2 B).comap f = CFSG.pCore 2 A := by
      rw [← hmap, Subgroup.comap_map_eq, sup_eq_left.mpr hker]
    rw [hcomap]
  exact (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)

private theorem isL2_quotient_pCore_of_surjective {A B : Type} [Group A] [Group B] [Finite A]
    {n : ℕ} (f : A →* B) (hf : Function.Surjective f) (hker : f.ker ≤ CFSG.pCore 2 A)
    (h : IsL2 (A ⧸ CFSG.pCore 2 A) n) : IsL2 (B ⧸ CFSG.pCore 2 B) n :=
  CFSG.Blueprint.LieModel.of_mulEquiv (quotient_pCore_equiv_of_surjective f hf hker) h

private theorem ker_comp_inclusion_eq {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n)
    {X : Type} [Group X] (φ : ↥(ncl N B') →* X)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B')) :
    (φ.comp (Subgroup.inclusion (kOf8103_le_ncl c))).ker =
      (relPPrimeCore 3 N).subgroupOf (F08.KOf8103 L B) := by
  ext x
  constructor
  · intro hx
    change (Subgroup.inclusion (kOf8103_le_ncl c) x) ∈ φ.ker at hx
    rw [hφker, Subgroup.mem_subgroupOf] at hx
    exact Subgroup.mem_subgroupOf.mpr hx
  · intro hx
    change (Subgroup.inclusion (kOf8103_le_ncl c) x) ∈ φ.ker
    rw [hφker]
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx)

private theorem ker_comp_inclusion_le_pCore {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n)
    {X : Type} [Group X] (φ : ↥(ncl N B') →* X)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N) :
    (φ.comp (Subgroup.inclusion (kOf8103_le_ncl c))).ker ≤
      CFSG.pCore 2 ↥(F08.KOf8103 L B) := by
  rw [ker_comp_inclusion_eq c φ hφker]
  have hIK : relPPrimeCore 3 N ⊓ F08.KOf8103 L B ≤
      pCoreOf 2 N ⊓ F08.KOf8103 L B :=
    le_inf ((inf_le_inf le_rfl (kOf8103_le_ncl c)).trans hN2I) inf_le_right
  have hsub : (relPPrimeCore 3 N).subgroupOf (F08.KOf8103 L B) ≤
      (pCoreOf 2 N ⊓ F08.KOf8103 L B).subgroupOf (F08.KOf8103 L B) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hIK ⟨hx, x.2⟩
  refine hsub.trans ?_
  have hQKnormal : ((pCoreOf 2 N ⊓ F08.KOf8103 L B).subgroupOf
      (F08.KOf8103 L B)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer
      (inf_le_right : pCoreOf 2 N ⊓ F08.KOf8103 L B ≤ F08.KOf8103 L B)]
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_inf _ _ _ (MulAut.conj x).injective,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (le_normalizer_pCoreOf_self N ((kOf8103_le_N c) hx)),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)]
  have hQKp : IsPGroup 2 ↥((pCoreOf 2 N ⊓ F08.KOf8103 L B).subgroupOf
      (F08.KOf8103 L B)) :=
    IsPGroup.of_equiv
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le
        (inf_le_left : pCoreOf 2 N ⊓ F08.KOf8103 L B ≤ pCoreOf 2 N))
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : pCoreOf 2 N ⊓ F08.KOf8103 L B ≤ F08.KOf8103 L B)).symm
  unfold CFSG.pCore
  exact le_sSup ⟨hQKnormal, hQKp⟩

private theorem range_comp_inclusion_commutator {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n)
    {X : Type} [Group X] (φ : ↥(ncl N B') →* X) :
    ⁅(φ.comp (Subgroup.inclusion (kOf8103_le_ncl c))).range,
        (φ.comp (Subgroup.inclusion (kOf8103_le_ncl c))).range⁆ =
      (φ.comp (Subgroup.inclusion (kOf8103_le_ncl c))).range := by
  let f := φ.comp (Subgroup.inclusion (kOf8103_le_ncl c))
  have htop : ⁅(⊤ : Subgroup ↥(F08.KOf8103 L B)),
      (⊤ : Subgroup ↥(F08.KOf8103 L B))⁆ = ⊤ := by
    have hperf : Group.IsPerfect ↥(F08.KOf8103 L B) := by
      unfold F08.KOf8103
      exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.isPerfect_derInf8 _
    exact (Group.isPerfect_def).mp hperf
  have hmap : f.range = Subgroup.map f ⊤ := (Subgroup.map_top f).symm
  rw [hmap, ← Subgroup.map_commutator, htop]

private noncomputable def step91Kq {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : Subgroup ↥(ncl N B') :=
  (pCoreOf 2 N ⊓ ncl N B').subgroupOf (ncl N B')

private instance step91Kq_normal {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : (step91Kq c).Normal :=
  normal_subgroupOf_pCoreOf_ncl c

private noncomputable abbrev step91W {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : Type :=
  ↥(ncl N B') ⧸ step91Kq c

private noncomputable abbrev step91Z {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : Subgroup (step91W c) :=
  ((relPPrimeCore 3 N ⊓ ncl N B').subgroupOf (ncl N B')).map
    (QuotientGroup.mk' (step91Kq c))

private theorem step91_center {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n)
    (hcomm : ⁅ncl N B', relPPrimeCore 3 N⁆ ≤ pCoreOf 2 N) :
    step91Z c ≤ Subgroup.center (step91W c) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (step91Kq c) w
  have hxI : (x : G) ∈ relPPrimeCore 3 N := (Subgroup.mem_subgroupOf.mp hx).1
  have hyN2 : (y : G) ∈ ncl N B' := y.2
  have hcomm' : ⁅relPPrimeCore 3 N, ncl N B'⁆ ≤ pCoreOf 2 N := by
    rwa [Subgroup.commutator_comm] at hcomm
  have hmem : ⁅(x : G), (y : G)⁆ ∈ pCoreOf 2 N :=
    hcomm' (Subgroup.commutator_mem_commutator hxI hyN2)
  have hmemKq : ⁅x, y⁆ ∈ step91Kq c := by
    change ((⁅x, y⁆ : ↥(ncl N B')) : G) ∈ pCoreOf 2 N ⊓ ncl N B'
    exact ⟨hmem, (⁅x, y⁆ : ↥(ncl N B')).2⟩
  have hmk : (QuotientGroup.mk' (step91Kq c)) ⁅x, y⁆ = 1 :=
    (QuotientGroup.eq_one_iff (⁅x, y⁆)).mpr hmemKq
  have h2 : ⁅(QuotientGroup.mk' (step91Kq c)) x, (QuotientGroup.mk' (step91Kq c)) y⁆ = 1 := by
    rw [← map_commutatorElement (QuotientGroup.mk' (step91Kq c)) x y]
    exact hmk
  have h3 : (QuotientGroup.mk' (step91Kq c)) x * (QuotientGroup.mk' (step91Kq c)) y =
      (QuotientGroup.mk' (step91Kq c)) y * (QuotientGroup.mk' (step91Kq c)) x :=
    commutatorElement_eq_one_iff_mul_comm.mp h2
  exact h3.symm

private theorem step91_coprime {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : ¬ 3 ∣ Nat.card (step91Z c) := by
  have hIcop : Nat.Coprime 3 (Nat.card (relPPrimeCore 3 N)) :=
    coprime_card_relPPrimeCore Nat.prime_three N
  have hcardSub : Nat.card ↥((relPPrimeCore 3 N ⊓ ncl N B').subgroupOf (ncl N B')) =
      Nat.card ↥(relPPrimeCore 3 N ⊓ ncl N B') :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : relPPrimeCore 3 N ⊓ ncl N B' ≤ ncl N B')).toEquiv
  have hdvd : Nat.card (step91Z c) ∣ Nat.card (relPPrimeCore 3 N) := by
    refine (Subgroup.card_map_dvd _ _).trans ?_
    rw [hcardSub]
    exact Subgroup.card_dvd_of_le inf_le_left
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (hIcop.coprime_dvd_right hdvd)

private instance step91Z_normal {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : (step91Z c).Normal :=
  Subgroup.Normal.map (normal_subgroupOf_relPPrimeCore_ncl c) _
    (QuotientGroup.mk'_surjective (step91Kq c))

private theorem step91_isU3 {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hU3 : IsU3 X (2 * n)) : IsU3 (step91W c ⧸ step91Z c) (2 * n) := by
  have hKq_le_I : step91Kq c ≤
      ((relPPrimeCore 3 N ⊓ ncl N B').subgroupOf (ncl N B')) := by
    intro x hx
    change ((x : ↥(ncl N B')) : G) ∈ pCoreOf 2 N ⊓ ncl N B' at hx
    rw [Subgroup.mem_subgroupOf]
    exact ⟨pCoreOf_two_le_relPPrimeCore_three N hx.1, hx.2⟩
  haveI hKqINormal : ((relPPrimeCore 3 N ⊓ ncl N B').subgroupOf (ncl N B')).Normal :=
    normal_subgroupOf_relPPrimeCore_ncl c
  let e1 : step91W c ⧸ step91Z c ≃*
      (↥(ncl N B') ⧸ ((relPPrimeCore 3 N ⊓ ncl N B').subgroupOf (ncl N B'))) :=
    QuotientGroup.quotientQuotientEquivQuotient (step91Kq c) _ hKq_le_I
  have hkerEq : ((relPPrimeCore 3 N ⊓ ncl N B').subgroupOf (ncl N B')) = φ.ker := by
    rw [hφker]
    exact inf_subgroupOf_right _ _
  let e2 : (↥(ncl N B') ⧸ ((relPPrimeCore 3 N ⊓ ncl N B').subgroupOf (ncl N B'))) ≃*
      (↥(ncl N B') ⧸ φ.ker) := QuotientGroup.quotientMulEquivOfEq hkerEq
  let e3 : (↥(ncl N B') ⧸ φ.ker) ≃* X := QuotientGroup.quotientKerEquivOfSurjective φ hφsurj
  exact CFSG.Blueprint.LieModel.of_mulEquiv (e1.trans (e2.trans e3)).symm hU3

private theorem step91_gen {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) :
    Subgroup.closure {x : step91W c | x ^ 3 = 1} = ⊤ := by
  let S : Set G := {z : G | ∃ g ∈ N, ∃ b ∈ B', z = g * b * g⁻¹}
  let T : Set ↥(ncl N B') := {y | (y : G) ∈ S}
  have himg : (ncl N B').subtype '' T = S := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hz
      exact ⟨⟨z, Subgroup.subset_closure hz⟩, hz, rfl⟩
  have hTgen : Subgroup.closure T = ⊤ := by
    apply Subgroup.map_injective (ncl N B').subtype_injective
    rw [MonoidHom.map_closure, himg, Subgroup.map_top, Subgroup.range_subtype]
    rfl
  have hstep : ∀ y ∈ T, (QuotientGroup.mk' (step91Kq c) y) ^ 3 = 1 := by
    rintro y ⟨g, hg, b, hb, hbeq⟩
    have hy3 : (y : G) ^ 3 = 1 := by
      rw [hbeq]
      have h := map_pow (MulAut.conj g) b 3
      rw [pow_three_eq_one_of_mem_b' c hb, map_one] at h
      simpa [MulAut.conj_apply] using h.symm
    have hy3' : y ^ 3 = 1 := by
      ext
      simpa using hy3
    simpa using congrArg (QuotientGroup.mk' (step91Kq c)) hy3'
  have hmapT : (Subgroup.closure T).map (QuotientGroup.mk' (step91Kq c)) = ⊤ := by
    rw [hTgen, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (step91Kq c))]
  rw [eq_top_iff]
  calc (⊤ : Subgroup (step91W c)) =
      (Subgroup.closure T).map (QuotientGroup.mk' (step91Kq c)) := hmapT.symm
    _ = Subgroup.closure (QuotientGroup.mk' (step91Kq c) '' T) := MonoidHom.map_closure _ _
    _ ≤ Subgroup.closure {x : step91W c | x ^ 3 = 1} := by
        apply Subgroup.closure_mono
        rintro _ ⟨y, hy, rfl⟩
        exact hstep y hy

private theorem inf_relPPrimeCore_le_pCoreOf (hM3 : KU3Mult) {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n)
    (hcomm : ⁅ncl N B', relPPrimeCore 3 N⁆ ≤ pCoreOf 2 N)
    {X : Type} [Group X] (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hU3 : IsU3 X (2 * n)) :
    relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N := by
  have hZcenter : step91Z c ≤ Subgroup.center (step91W c) := step91_center c hcomm
  have hZcoprime : ¬ 3 ∣ Nat.card (step91Z c) := step91_coprime c
  have hU3WZ : IsU3 (step91W c ⧸ step91Z c) (2 * n) :=
    step91_isU3 c φ hφsurj hφker hU3
  have hgen : Subgroup.closure {x : step91W c | x ^ 3 = 1} = ⊤ := step91_gen c
  have hfin : 4 ≤ 2 * n := by
    have := c.toStd8105.two_le
    omega
  have heven : Even (2 * n) := ⟨n, by ring⟩
  have hZbot : step91Z c = ⊥ :=
    hM3 (step91W c) (step91Z c) (2 * n) hZcenter hZcoprime hU3WZ hfin heven hgen
  intro x hx
  have hxN2 : x ∈ ncl N B' := hx.2
  have hxI : x ∈ relPPrimeCore 3 N := hx.1
  have hxZ : (QuotientGroup.mk' (step91Kq c)) ⟨x, hxN2⟩ ∈ step91Z c :=
    Subgroup.mem_map.mpr ⟨⟨x, hxN2⟩, by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hxI, hxN2⟩, rfl⟩
  rw [hZbot, Subgroup.mem_bot] at hxZ
  have hxKq : (⟨x, hxN2⟩ : ↥(ncl N B')) ∈ step91Kq c :=
    (QuotientGroup.eq_one_iff _).mp (by simpa [QuotientGroup.mk'_apply] using hxZ)
  exact (Subgroup.mem_subgroupOf.mp hxKq).1

private abbrev actionR {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (_c : Ctx8105 D L P B B' D₀ H N p n) : Subgroup G := pCoreOf 2 H

private abbrev actionN2 {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (_c : Ctx8105 D L P B B' D₀ H N p n) : Subgroup G := ncl N B'

private theorem actionR_le_N {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : actionR c ≤ N :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans c.toCex8105.memN.2

private theorem actionN2_normal {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : N ≤ normalizer (actionN2 c : Set G) :=
  ncl_normal (b'_le_N c)

private abbrev actionKq {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : Subgroup ↥(actionN2 c) :=
  (pCoreOf 2 N ⊓ actionN2 c).subgroupOf (actionN2 c)

private instance actionKq_normal {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : (actionKq c).Normal :=
  normal_subgroupOf_pCoreOf_ncl c

private noncomputable def actionConjN2 {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) (r : ↥(actionR c)) :
    ↥(actionN2 c) ≃* ↥(actionN2 c) :=
  (Subgroup.equivMapOfInjective (actionN2 c) (MulAut.conj (r : G)).toMonoidHom
      (MulAut.conj (r : G)).injective).trans
    (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (actionN2_normal c (actionR_le_N c r.2))))

private theorem actionConjN2_val {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) (r : ↥(actionR c)) (x : ↥(actionN2 c)) :
    (((actionConjN2 c r).toMonoidHom x : ↥(actionN2 c)) : G) =
      (r : G) * (x : G) * (r : G)⁻¹ := rfl

private theorem actionConjN2_val_fun {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) (r : ↥(actionR c)) (x : ↥(actionN2 c)) :
    ((actionConjN2 c r x : ↥(actionN2 c)) : G) = (r : G) * (x : G) * (r : G)⁻¹ :=
  actionConjN2_val c r x

private abbrev actionW {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : Type := ↥(actionN2 c) ⧸ actionKq c

private theorem actionConjN2_Kq {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) (r : ↥(actionR c)) :
    (actionKq c).map (actionConjN2 c r).toMonoidHom = actionKq c := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyRN : ((y : ↥(actionN2 c)) : G) ∈ pCoreOf 2 N ⊓ actionN2 c :=
      Subgroup.mem_subgroupOf.mp hy
    have hrnQ : (r : G) ∈ normalizer (pCoreOf 2 N : Set G) :=
      le_normalizer_pCoreOf_self N (actionR_le_N c r.2)
    have hrnN2 : (r : G) ∈ normalizer (actionN2 c : Set G) :=
      actionN2_normal c (actionR_le_N c r.2)
    have hq : (r : G) * (y : G) * (r : G)⁻¹ ∈ pCoreOf 2 N :=
      ((Subgroup.mem_normalizer_iff.mp hrnQ) (y : G)).mp hyRN.1
    have hn2 : (r : G) * (y : G) * (r : G)⁻¹ ∈ actionN2 c :=
      ((Subgroup.mem_normalizer_iff.mp hrnN2) (y : G)).mp hyRN.2
    change (((actionConjN2 c r).toMonoidHom y : ↥(actionN2 c)) : G) ∈
      pCoreOf 2 N ⊓ actionN2 c
    rw [actionConjN2_val]
    exact ⟨hq, hn2⟩
  · intro hx
    have hxRN : ((x : ↥(actionN2 c)) : G) ∈ pCoreOf 2 N ⊓ actionN2 c :=
      Subgroup.mem_subgroupOf.mp hx
    have hrnQ : ((r : G)⁻¹) ∈ normalizer (pCoreOf 2 N : Set G) :=
      (normalizer (pCoreOf 2 N : Set G)).inv_mem
        (le_normalizer_pCoreOf_self N (actionR_le_N c r.2))
    have hrnN2 : ((r : G)⁻¹) ∈ normalizer (actionN2 c : Set G) :=
      (normalizer (actionN2 c : Set G)).inv_mem
        (actionN2_normal c (actionR_le_N c r.2))
    have hyQ : (r : G)⁻¹ * (x : G) * (r : G) ∈ pCoreOf 2 N := by
      simpa using ((Subgroup.mem_normalizer_iff.mp hrnQ) (x : G)).mp hxRN.1
    have hyN2 : (r : G)⁻¹ * (x : G) * (r : G) ∈ actionN2 c := by
      simpa using ((Subgroup.mem_normalizer_iff.mp hrnN2) (x : G)).mp hxRN.2
    refine Subgroup.mem_map.mpr ⟨⟨(r : G)⁻¹ * (x : G) * (r : G), hyN2⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨hyQ, hyN2⟩
    · apply Subtype.ext
      rw [actionConjN2_val]
      group

private theorem action_ker_eq {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N) :
    φ.ker = actionKq c := by
  rw [hφker]
  have hinf : relPPrimeCore 3 N ⊓ ncl N B' = pCoreOf 2 N ⊓ ncl N B' :=
    le_antisymm (le_inf hN2I inf_le_right)
      (inf_le_inf_right _ (pCoreOf_two_le_relPPrimeCore_three N))
  change (relPPrimeCore 3 N).subgroupOf (ncl N B') =
    (pCoreOf 2 N ⊓ ncl N B').subgroupOf (ncl N B')
  rw [← hinf, inf_subgroupOf_right]

private noncomputable def actionEWX {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N) : actionW c ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq (action_ker_eq c φ hφker hN2I).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)

private theorem actionEWX_mk {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N) (y : ↥(actionN2 c)) :
    actionEWX c φ hφsurj hφker hN2I ((QuotientGroup.mk' (actionKq c)) y) = φ y := rfl

private noncomputable def actionBeta {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) (r : ↥(actionR c)) : MulAut (actionW c) :=
  QuotientGroup.congr (actionKq c) (actionKq c) (actionConjN2 c r) (actionConjN2_Kq c r)

private noncomputable abbrev actionAlphaFun {D : Data G} {L P B B' D₀ H N : Subgroup G}
    {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N)
    (r : ↥(actionR c)) : MulAut X :=
  (MulAut.congr (actionEWX c φ hφsurj hφker hN2I)) (actionBeta c r)

private theorem actionAlpha_formula {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    {φ : ↥(ncl N B') →* X} {hφsurj : Function.Surjective φ}
    {hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B')}
    {hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N}
    (r : ↥(actionR c)) (y : ↥(actionN2 c)) :
    actionAlphaFun c φ hφsurj hφker hN2I r (φ y) = φ (actionConjN2 c r y) := by
  change (MulAut.congr (actionEWX c φ hφsurj hφker hN2I) (actionBeta c r)) (φ y) =
    φ (actionConjN2 c r y)
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have h1 : (actionEWX c φ hφsurj hφker hN2I).symm (φ y) =
      (QuotientGroup.mk' (actionKq c)) y := by
    rw [← actionEWX_mk c φ hφsurj hφker hN2I y, MulEquiv.symm_apply_apply]
  rw [h1]
  have h2 : actionBeta c r ((QuotientGroup.mk' (actionKq c)) y) =
      (QuotientGroup.mk' (actionKq c)) (actionConjN2 c r y) :=
    QuotientGroup.congr_mk (actionKq c) (actionKq c) (actionConjN2 c r)
      (actionConjN2_Kq c r) y
  rw [h2, actionEWX_mk]

private noncomputable def actionAlpha {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N) :
    ↥(actionR c) →* MulAut X :=
  { toFun := actionAlphaFun c φ hφsurj hφker hN2I
    map_one' := by
      ext x
      obtain ⟨y, rfl⟩ := hφsurj x
      rw [MulAut.one_apply, actionAlpha_formula c 1 y]
      congr 1
      apply Subtype.ext
      rw [actionConjN2_val_fun]
      simp
    map_mul' := by
      intro r s
      ext x
      obtain ⟨y, rfl⟩ := hφsurj x
      rw [MulAut.mul_apply]
      conv_lhs => rw [actionAlpha_formula c (r * s) y]
      conv_rhs =>
        rw [actionAlpha_formula c s y]
        rw [actionAlpha_formula c r (actionConjN2 c s y)]
      congr 1
      apply Subtype.ext
      rw [actionConjN2_val_fun, actionConjN2_val_fun, actionConjN2_val_fun]
      simp only [Subgroup.coe_mul]
      group }

private noncomputable abbrev actionA {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N) : Subgroup (MulAut X) :=
  (actionAlpha c φ hφsurj hφker hN2I).range

private noncomputable abbrev actionF0 {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) : ↥(F08.KOf8103 L B) →* X :=
  φ.comp (Subgroup.inclusion (kOf8103_le_ncl c))

private noncomputable abbrev actionK0 {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) : Subgroup X :=
  (actionF0 c φ).range

private theorem action_isPGroup {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N) :
    IsPGroup 2 ↥(actionA c φ hφsurj hφker hN2I) :=
  IsPGroup.of_surjective (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
    (actionAlpha c φ hφsurj hφker hN2I).rangeRestrict
    (actionAlpha c φ hφsurj hφker hN2I).rangeRestrict_surjective

private theorem action_fixes {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N)
    (hRK : ⁅actionR c, F08.KOf8103 L B⁆ ≤ pCoreOf 2 N) :
    ∀ a ∈ actionA c φ hφsurj hφker hN2I, ∀ x ∈ actionK0 c φ, a x = x := by
  intro a ha x hx
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp ha
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
  have hcomN2 : (r : G) * (k : G) * (r : G)⁻¹ * (k : G)⁻¹ ∈ actionN2 c := by
    have h1 : (r : G) * (k : G) * (r : G)⁻¹ ∈ actionN2 c :=
      ((Subgroup.mem_normalizer_iff.mp (actionN2_normal c (actionR_le_N c r.2))) (k : G)).mp
        ((kOf8103_le_ncl c) k.2)
    exact (actionN2 c).mul_mem h1 ((actionN2 c).inv_mem ((kOf8103_le_ncl c) k.2))
  have hcomQ : (r : G) * (k : G) * (r : G)⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 N :=
    hRK (Subgroup.commutator_mem_commutator r.2 k.2)
  have hq : (⟨(r : G) * (k : G) * (r : G)⁻¹ * (k : G)⁻¹, hcomN2⟩ : ↥(actionN2 c)) ∈
      actionKq c := by
    change ((⟨(r : G) * (k : G) * (r : G)⁻¹ * (k : G)⁻¹, hcomN2⟩ : ↥(actionN2 c)) : G) ∈
      pCoreOf 2 N ⊓ actionN2 c
    exact ⟨hcomQ, hcomN2⟩
  have hphi : φ (actionConjN2 c r ⟨k, (kOf8103_le_ncl c) k.2⟩) =
      φ ⟨k, (kOf8103_le_ncl c) k.2⟩ := by
    have h2 : (⟨(r : G) * (k : G) * (r : G)⁻¹ * (k : G)⁻¹, hcomN2⟩ : ↥(actionN2 c)) =
        actionConjN2 c r ⟨k, (kOf8103_le_ncl c) k.2⟩ *
          ⟨k, (kOf8103_le_ncl c) k.2⟩⁻¹ := by
      apply Subtype.ext
      simp [actionConjN2_val_fun]
    have hq' : (⟨(r : G) * (k : G) * (r : G)⁻¹ * (k : G)⁻¹, hcomN2⟩ : ↥(actionN2 c)) ∈
        φ.ker := by
      rwa [action_ker_eq c φ hφker hN2I]
    have h1 : φ (actionConjN2 c r ⟨k, (kOf8103_le_ncl c) k.2⟩ *
        ⟨k, (kOf8103_le_ncl c) k.2⟩⁻¹) = 1 := by
      rw [← h2]
      exact hq'
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  show actionAlphaFun c φ hφsurj hφker hN2I r (actionF0 c φ k) = actionF0 c φ k
  rw [show actionF0 c φ k = φ ⟨k, (kOf8103_le_ncl c) k.2⟩ from rfl,
    actionAlpha_formula c r ⟨k, (kOf8103_le_ncl c) k.2⟩, hphi]

private theorem eq_of_ne_one_of_card_le_two {A : Type} [Group A] [Finite A]
    (hA : Nat.card A ≤ 2) {a b : A} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  by_contra hab
  have hinj : Function.Injective (fun i : Fin 3 => ![1, a, b] i) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hle := Nat.card_le_card_of_injective (fun i : Fin 3 => ![1, a, b] i) hinj
  simp at hle
  omega

private theorem action_simple {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X] (hsimple : IsSimpleGroup X)
    (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N) :
    ∀ X' : Subgroup G, X' ≤ ncl N B' → ncl N B' ≤ normalizer (X' : Set G) →
      X' ≤ pCoreOf 2 N ∨ ncl N B' ≤ X' ⊔ pCoreOf 2 N := by
  intro X' hX'N2 hX'norm
  haveI hX'normal : (X'.subgroupOf (ncl N B')).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX'N2).mpr hX'norm
  haveI himgNormal : ((X'.subgroupOf (ncl N B')).map φ).Normal :=
    Subgroup.Normal.map hX'normal φ hφsurj
  rcases hsimple.eq_bot_or_eq_top_of_normal ((X'.subgroupOf (ncl N B')).map φ)
    with hbot | htop
  · left
    intro x hx
    have hxN2 : x ∈ ncl N B' := hX'N2 hx
    have hxmem : (⟨x, hxN2⟩ : ↥(ncl N B')) ∈ X'.subgroupOf (ncl N B') :=
      Subgroup.mem_subgroupOf.mpr hx
    have hker : (⟨x, hxN2⟩ : ↥(ncl N B')) ∈ φ.ker := by
      rw [Subgroup.map_eq_bot_iff] at hbot
      exact hbot hxmem
    rw [hφker] at hker
    exact hN2I ⟨Subgroup.mem_subgroupOf.mp hker, hxN2⟩
  · right
    intro y hy
    have hyimg : φ ⟨y, hy⟩ ∈ (X'.subgroupOf (ncl N B')).map φ := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨x, hxX', hxφ⟩ := Subgroup.mem_map.mp hyimg
    have hxX : (x : G) ∈ X' := Subgroup.mem_subgroupOf.mp hxX'
    have hxN2 : (x : G) ∈ ncl N B' := x.2
    have hmemker : (⟨(x : G)⁻¹ * y,
        (ncl N B').mul_mem ((ncl N B').inv_mem hxN2) hy⟩ : ↥(ncl N B')) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have hval : φ (⟨(x : G)⁻¹ * y,
          (ncl N B').mul_mem ((ncl N B').inv_mem hxN2) hy⟩ : ↥(ncl N B')) =
          (φ x)⁻¹ * φ ⟨y, hy⟩ := by
        have harg : (⟨(x : G)⁻¹ * y,
            (ncl N B').mul_mem ((ncl N B').inv_mem hxN2) hy⟩ : ↥(ncl N B')) =
            (⟨(x : G), hxN2⟩ : ↥(ncl N B'))⁻¹ * ⟨y, hy⟩ := by
          apply Subtype.ext
          simp [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [harg, map_mul, map_inv]
      rw [hval, hxφ]
      simp
    rw [hφker] at hmemker
    have hq : (x : G)⁻¹ * y ∈ pCoreOf 2 N :=
      hN2I ⟨Subgroup.mem_subgroupOf.mp hmemker,
        (ncl N B').mul_mem ((ncl N B').inv_mem hxN2) hy⟩
    rw [← show (x : G) * ((x : G)⁻¹ * y) = y by group]
    refine Subgroup.mul_mem (X' ⊔ pCoreOf 2 N) ?_ ?_
    · exact Subgroup.mem_sup_left hxX
    · exact Subgroup.mem_sup_right hq

private theorem actionK0_L2 {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N) :
    IsL2 (Bar2 (actionK0 c φ)) (2 * n) := by
  let fK : ↥(F08.KOf8103 L B) →* ↥(actionK0 c φ) :=
    (actionF0 c φ).codRestrict (actionK0 c φ) (fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hfKsurj : Function.Surjective fK := by
    intro y
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.2
    exact ⟨x, Subtype.ext hx⟩
  have hfKker : fK.ker = (relPPrimeCore 3 N).subgroupOf (F08.KOf8103 L B) := by
    rw [MonoidHom.ker_codRestrict]
    exact ker_comp_inclusion_eq c φ hφker
  refine isL2_quotient_pCore_of_surjective fK hfKsurj ?_ ?_
  · rw [hfKker, ← ker_comp_inclusion_eq c φ hφker]
    exact ker_comp_inclusion_le_pCore c φ hφker hN2I
  · simpa using c.toStd8105.notB.2.2

private theorem actionK0_commutator {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) : ⁅actionK0 c φ, actionK0 c φ⁆ = actionK0 c φ := by
  have h := range_comp_inclusion_commutator c φ
  simpa [actionK0, actionF0] using h

private abbrev actionRN2 {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : Subgroup ↥(actionN2 c) :=
  (actionR c ⊓ actionN2 c).subgroupOf (actionN2 c)

private theorem action_conj_mem {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (k : ↥(F08.KOf8103 L B)) (z : ↥(actionN2 c))
    (hz : z ∈ actionRN2 c) :
    actionF0 c φ k * φ z * (actionF0 c φ k)⁻¹ ∈ (actionRN2 c).map φ := by
  have hzRN : ((z : ↥(actionN2 c)) : G) ∈ actionR c ⊓ actionN2 c :=
    Subgroup.mem_subgroupOf.mp hz
  have hknR : (k : G) ∈ normalizer (actionR c : Set G) :=
    le_normalizer_pCoreOf_self H (c.toCex8105.memH.2.2.1 k.2)
  have hknN2 : (k : G) ∈ normalizer (actionN2 c : Set G) :=
    actionN2_normal c (kOf8103_le_N c k.2)
  have hzR' : (k : G) * (z : G) * (k : G)⁻¹ ∈ actionR c :=
    ((Subgroup.mem_normalizer_iff.mp hknR) (z : G)).mp hzRN.1
  have hzN2' : (k : G) * (z : G) * (k : G)⁻¹ ∈ actionN2 c :=
    ((Subgroup.mem_normalizer_iff.mp hknN2) (z : G)).mp hzRN.2
  refine Subgroup.mem_map.mpr ⟨⟨(k : G) * (z : G) * (k : G)⁻¹, hzN2'⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr ⟨hzR', hzN2'⟩
  · have harg : (⟨(k : G) * (z : G) * (k : G)⁻¹, hzN2'⟩ : ↥(actionN2 c)) =
        ⟨(k : G), (kOf8103_le_ncl c) k.2⟩ * z *
          ⟨(k : G), (kOf8103_le_ncl c) k.2⟩⁻¹ := by
      apply Subtype.ext
      simp [Subgroup.coe_mul, Subgroup.coe_inv]
    show φ ⟨(k : G) * (z : G) * (k : G)⁻¹, hzN2'⟩ =
      actionF0 c φ k * φ z * (actionF0 c φ k)⁻¹
    rw [show actionF0 c φ k = φ ⟨(k : G), (kOf8103_le_ncl c) k.2⟩ from rfl, harg]
    simp only [map_mul, map_inv]

private theorem action_K0_le_normalizer {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) :
    actionK0 c φ ≤ normalizer ((actionRN2 c).map φ : Set X) := by
  rintro _ ⟨k, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact action_conj_mem c φ k z hz
  · intro hy
    obtain ⟨z, hz, hzφ⟩ := Subgroup.mem_map.mp hy
    have hz' : actionF0 c φ k⁻¹ * φ z * (actionF0 c φ k⁻¹)⁻¹ ∈ (actionRN2 c).map φ :=
      action_conj_mem c φ k⁻¹ z hz
    rw [map_inv] at hz'
    have hz'' : (actionF0 c φ k)⁻¹ * φ z * actionF0 c φ k ∈ (actionRN2 c).map φ := by
      simpa using hz'
    rwa [show (actionF0 c φ k)⁻¹ * φ z * actionF0 c φ k = y from by rw [hzφ]; group] at hz''

private theorem action_inf_le_pCoreOf {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N)
    (hF1 : ∀ U : Subgroup X, IsPGroup 2 ↥U → actionK0 c φ ≤ normalizer U → U = ⊥) :
    actionR c ⊓ actionN2 c ≤ pCoreOf 2 N := by
  have hRN2_2 : IsPGroup 2 ↥(actionRN2 c) :=
    IsPGroup.of_equiv
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le
        (inf_le_left : actionR c ⊓ actionN2 c ≤ actionR c))
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : actionR c ⊓ actionN2 c ≤ actionN2 c)).symm
  have hU2 : IsPGroup 2 ↥((actionRN2 c).map φ) := IsPGroup.map hRN2_2 φ
  have hbot := hF1 ((actionRN2 c).map φ) hU2 (action_K0_le_normalizer c φ)
  intro x hx
  have hxmem : (⟨x, hx.2⟩ : ↥(actionN2 c)) ∈ actionRN2 c := by
    change ((⟨x, hx.2⟩ : ↥(actionN2 c)) : G) ∈ actionR c ⊓ actionN2 c
    exact hx
  have hxmap : φ ⟨x, hx.2⟩ ∈ (actionRN2 c).map φ :=
    Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hxmem, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hxmap
  have hxk : (⟨x, hx.2⟩ : ↥(actionN2 c)) ∈ φ.ker := hxmap
  rw [action_ker_eq c φ hφker hN2I] at hxk
  exact (Subgroup.mem_subgroupOf.mp hxk).1

private theorem action_RK {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N)
    (hF1 : ∀ U : Subgroup X, IsPGroup 2 ↥U → actionK0 c φ ≤ normalizer U → U = ⊥) :
    ⁅actionR c, F08.KOf8103 L B⁆ ≤ pCoreOf 2 N := by
  have hinf := action_inf_le_pCoreOf c φ hφker hN2I hF1
  rw [Subgroup.commutator_le]
  intro r hr k hk
  have hmemR : r * k * r⁻¹ * k⁻¹ ∈ actionR c := by
    have hknR : k ∈ normalizer (actionR c : Set G) :=
      le_normalizer_pCoreOf_self H (c.toCex8105.memH.2.2.1 hk)
    have hconj : k * r⁻¹ * k⁻¹ ∈ actionR c :=
      ((Subgroup.mem_normalizer_iff.mp hknR) r⁻¹).mp ((actionR c).inv_mem hr)
    have h1 : r * (k * r⁻¹ * k⁻¹) ∈ actionR c := (actionR c).mul_mem hr hconj
    rwa [show r * k * r⁻¹ * k⁻¹ = r * (k * r⁻¹ * k⁻¹) by group]
  have hmemN2 : r * k * r⁻¹ * k⁻¹ ∈ actionN2 c := by
    have hrnN2 : r ∈ normalizer (actionN2 c : Set G) :=
      actionN2_normal c (actionR_le_N c hr)
    have hconj : r * k * r⁻¹ ∈ actionN2 c :=
      ((Subgroup.mem_normalizer_iff.mp hrnN2) k).mp ((kOf8103_le_ncl c) hk)
    exact (actionN2 c).mul_mem hconj ((actionN2 c).inv_mem ((kOf8103_le_ncl c) hk))
  exact hinf (Subgroup.mem_inf.mpr ⟨hmemR, hmemN2⟩)

private theorem action_eq_one_iff {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N) (r : ↥(actionR c)) :
    actionAlpha c φ hφsurj hφker hN2I r = 1 ↔
      CentMod (ncl N B') (pCoreOf 2 N) (r : G) := by
  constructor
  · intro h y hyN2
    have hfix : actionAlphaFun c φ hφsurj hφker hN2I r (φ ⟨y, hyN2⟩) = φ ⟨y, hyN2⟩ := by
      change actionAlpha c φ hφsurj hφker hN2I r (φ ⟨y, hyN2⟩) = φ ⟨y, hyN2⟩
      rw [h, MulAut.one_apply]
    rw [actionAlpha_formula c r ⟨y, hyN2⟩] at hfix
    have hker : (actionConjN2 c r ⟨y, hyN2⟩ * ⟨y, hyN2⟩⁻¹ : ↥(actionN2 c)) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfix]
      simp
    rw [action_ker_eq c φ hφker hN2I] at hker
    change (((actionConjN2 c r ⟨y, hyN2⟩ * ⟨y, hyN2⟩⁻¹ : ↥(actionN2 c)) : G) ∈
      pCoreOf 2 N ⊓ actionN2 c) at hker
    have hval : ((actionConjN2 c r ⟨y, hyN2⟩ * ⟨y, hyN2⟩⁻¹ : ↥(actionN2 c)) : G) =
        (r : G) * y * (r : G)⁻¹ * y⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, actionConjN2_val_fun]
    rw [hval] at hker
    exact hker.1
  · intro h
    ext x
    obtain ⟨y, rfl⟩ := hφsurj x
    show actionAlphaFun c φ hφsurj hφker hN2I r (φ y) = φ y
    rw [actionAlpha_formula c r y]
    have hq : (actionConjN2 c r y * y⁻¹ : ↥(actionN2 c)) ∈ φ.ker := by
      rw [action_ker_eq c φ hφker hN2I]
      change (((actionConjN2 c r y * y⁻¹ : ↥(actionN2 c)) : G) ∈
        pCoreOf 2 N ⊓ actionN2 c)
      have hval : ((actionConjN2 c r y * y⁻¹ : ↥(actionN2 c)) : G) =
          (r : G) * (y : G) * (r : G)⁻¹ * (y : G)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, actionConjN2_val_fun]
      refine ⟨?_, ?_⟩
      · rw [hval]
        exact h (y : G) y.2
      · exact (actionConjN2 c r y * y⁻¹).2
    have h1 : φ (actionConjN2 c r y * y⁻¹) = 1 := hq
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1

private theorem action_coset {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X] [Finite X]
    (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N)
    (hAcard : Nat.card ↥(actionA c φ hφsurj hφker hN2I) ≤ 2) :
    ∀ r ∈ actionR c, ∀ r' ∈ actionR c,
      ¬ CentMod (ncl N B') (pCoreOf 2 N) r →
      ¬ CentMod (ncl N B') (pCoreOf 2 N) r' →
      CentMod (ncl N B') (pCoreOf 2 N) (r * r'⁻¹) := by
  intro r hr r' hr' hnr hnr'
  have hAr : actionAlpha c φ hφsurj hφker hN2I ⟨r, hr⟩ ∈
      actionA c φ hφsurj hφker hN2I := MonoidHom.mem_range.mpr ⟨⟨r, hr⟩, rfl⟩
  have hAr' : actionAlpha c φ hφsurj hφker hN2I ⟨r', hr'⟩ ∈
      actionA c φ hφsurj hφker hN2I := MonoidHom.mem_range.mpr ⟨⟨r', hr'⟩, rfl⟩
  have hne : actionAlpha c φ hφsurj hφker hN2I ⟨r, hr⟩ ≠ 1 :=
    fun h => hnr ((action_eq_one_iff c φ hφsurj hφker hN2I _).mp h)
  have hne' : actionAlpha c φ hφsurj hφker hN2I ⟨r', hr'⟩ ≠ 1 :=
    fun h => hnr' ((action_eq_one_iff c φ hφsurj hφker hN2I _).mp h)
  have h1 : (⟨actionAlpha c φ hφsurj hφker hN2I ⟨r, hr⟩, hAr⟩ :
      ↥(actionA c φ hφsurj hφker hN2I)) ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have h2 : (⟨actionAlpha c φ hφsurj hφker hN2I ⟨r', hr'⟩, hAr'⟩ :
      ↥(actionA c φ hφsurj hφker hN2I)) ≠ 1 := fun h => hne' (congrArg Subtype.val h)
  have heqsub : (⟨actionAlpha c φ hφsurj hφker hN2I ⟨r, hr⟩, hAr⟩ :
      ↥(actionA c φ hφsurj hφker hN2I)) =
      ⟨actionAlpha c φ hφsurj hφker hN2I ⟨r', hr'⟩, hAr'⟩ :=
    eq_of_ne_one_of_card_le_two hAcard h1 h2
  have heq : actionAlpha c φ hφsurj hφker hN2I ⟨r, hr⟩ =
      actionAlpha c φ hφsurj hφker hN2I ⟨r', hr'⟩ := congrArg Subtype.val heqsub
  have hone : actionAlpha c φ hφsurj hφker hN2I (⟨r, hr⟩ * ⟨r', hr'⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  exact (action_eq_one_iff c φ hφsurj hφker hN2I _).mp hone

private theorem action_order {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N)
    (g : ↥(actionN2 c)) {gtilde : X} (hgφ : φ g = gtilde)
    (hgord : orderOf gtilde = 2 ^ (2 * n) + 1) :
    ∀ k : ℕ, (g : G) ^ k ∈ pCoreOf 2 N → 2 ^ (2 * n) + 1 ∣ k := by
  intro k hk
  have hmemker : (g ^ k : ↥(actionN2 c)) ∈ actionKq c := by
    change ((g ^ k : ↥(actionN2 c)) : G) ∈ pCoreOf 2 N ⊓ actionN2 c
    exact ⟨hk, (actionN2 c).pow_mem g.2 k⟩
  have hphi : φ (g ^ k) = 1 := by
    have : (g ^ k : ↥(actionN2 c)) ∈ φ.ker := by rwa [action_ker_eq c φ hφker hN2I]
    exact this
  rw [map_pow, hgφ] at hphi
  rw [← hgord]
  exact orderOf_dvd_of_pow_eq_one hphi

private theorem action_inversion {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {X : Type} [Group X]
    (φ : ↥(ncl N B') →* X) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = (relPPrimeCore 3 N).subgroupOf (ncl N B'))
    (hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N)
    (g : ↥(actionN2 c)) {gtilde : X} (hgφ : φ g = gtilde)
    (hAinv : ∀ a ∈ actionA c φ hφsurj hφker hN2I, a ≠ 1 → a gtilde = gtilde⁻¹) :
    ∀ r ∈ actionR c, ¬ CentMod (ncl N B') (pCoreOf 2 N) r →
      r * (g : G) * r⁻¹ * (g : G) ∈ pCoreOf 2 N := by
  intro r hr hnr
  have hne : actionAlpha c φ hφsurj hφker hN2I ⟨r, hr⟩ ≠ 1 :=
    fun h => hnr ((action_eq_one_iff c φ hφsurj hφker hN2I _).mp h)
  have hinv := hAinv (actionAlpha c φ hφsurj hφker hN2I ⟨r, hr⟩)
    (MonoidHom.mem_range.mpr ⟨⟨r, hr⟩, rfl⟩) hne
  have hinv' : actionAlphaFun c φ hφsurj hφker hN2I ⟨r, hr⟩ gtilde = gtilde⁻¹ := hinv
  have h1 : φ (actionConjN2 c ⟨r, hr⟩ g) = (φ g)⁻¹ := by
    rw [← actionAlpha_formula c ⟨r, hr⟩ g, hgφ]
    exact hinv'
  have hker : (actionConjN2 c ⟨r, hr⟩ g * g : ↥(actionN2 c)) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, h1, hgφ]
    simp
  rw [action_ker_eq c φ hφker hN2I] at hker
  change (((actionConjN2 c ⟨r, hr⟩ g * g : ↥(actionN2 c)) : G) ∈
    pCoreOf 2 N ⊓ actionN2 c) at hker
  have hval : ((actionConjN2 c ⟨r, hr⟩ g * g : ↥(actionN2 c)) : G) =
      r * (g : G) * r⁻¹ * (g : G) := by
    rw [Subgroup.coe_mul, actionConjN2_val_fun]
  rw [hval] at hker
  exact hker.1

theorem action_facts (hU3 : KU3Ident) (hM3 : KU3Mult) (hF : KU3Facts) (h332 : UCK.K332ThreeAb)
    (hS : KSuzukiL2) {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) (hC : UC6.calCGS (pCoreOf 2 H) ≤ D.M) :
    (∀ X : Subgroup G, X ≤ ncl N B' → ncl N B' ≤ normalizer (X : Set G) →
      X ≤ pCoreOf 2 N ∨ ncl N B' ≤ X ⊔ pCoreOf 2 N) ∧
    ∃ g ∈ ncl N B', (∀ k : ℕ, g ^ k ∈ pCoreOf 2 N → 2 ^ (2 * n) + 1 ∣ k) ∧
      (∀ r ∈ pCoreOf 2 H, ∀ r' ∈ pCoreOf 2 H, ¬ CentMod (ncl N B') (pCoreOf 2 N) r →
        ¬ CentMod (ncl N B') (pCoreOf 2 N) r' →
          CentMod (ncl N B') (pCoreOf 2 N) (r * r'⁻¹)) ∧
      ∀ r ∈ pCoreOf 2 H, ¬ CentMod (ncl N B') (pCoreOf 2 N) r →
        r * g * r⁻¹ * g ∈ pCoreOf 2 N := by
  have hQleR : pCoreOf 2 N ≤ pCoreOf 2 H := pCoreOf_le_of_calCGS_le c.toCex8105 hC
  have hQleM : pCoreOf 2 N ≤ D.M :=
    hQleR.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans c.toCex8105.memH.1)
  obtain ⟨X, instX, φ, hφsurj, hφker, hU3X⟩ := isU3_ncl hU3 h332 hS c hQleM
  letI : Group X := instX
  haveI hXfin : Finite X := Finite.of_surjective φ hφsurj
  have hcomm : ⁅ncl N B', relPPrimeCore 3 N⁆ ≤ pCoreOf 2 N :=
    commutator_ncl_relPPrimeCore_le hS c
  have hN2I : relPPrimeCore 3 N ⊓ ncl N B' ≤ pCoreOf 2 N :=
    inf_relPPrimeCore_le_pCoreOf hM3 c hcomm φ hφsurj hφker hU3X
  haveI hsimple : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSU) (by decide) hU3X
  have hsimp := action_simple c hsimple φ hφsurj hφker hN2I
  have h4 : 4 ≤ 2 * n := by
    have := c.toStd8105.two_le
    omega
  have heven : Even (2 * n) := ⟨n, by ring⟩
  obtain ⟨hF1, _hF2, gtilde, _hgt, hgord, hAcond⟩ :=
    hF X (2 * n) hU3X h4 heven (actionK0 c φ) (actionK0_commutator c φ)
      (actionK0_L2 c φ hφsurj hφker hN2I)
  have hRK : ⁅actionR c, F08.KOf8103 L B⁆ ≤ pCoreOf 2 N :=
    action_RK c φ hφker hN2I hF1
  have hA2 : IsPGroup 2 ↥(actionA c φ hφsurj hφker hN2I) :=
    action_isPGroup c φ hφsurj hφker hN2I
  have hAfix := action_fixes c φ hφsurj hφker hN2I hRK
  have hAcard : Nat.card ↥(actionA c φ hφsurj hφker hN2I) ≤ 2 := (hAcond _ hA2 hAfix).1
  have hAinv : ∀ a ∈ actionA c φ hφsurj hφker hN2I, a ≠ 1 → a gtilde = gtilde⁻¹ :=
    (hAcond _ hA2 hAfix).2
  obtain ⟨g, hgφ⟩ := hφsurj gtilde
  refine ⟨hsimp, (g : G), g.2, ?_, ?_, ?_⟩
  · exact action_order c φ hφker hN2I g hgφ hgord
  · exact action_coset c φ hφsurj hφker hN2I hAcard
  · exact action_inversion c φ hφsurj hφker hN2I g hgφ hAinv

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105
