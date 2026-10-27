module

public import CFSG.Quasithin.H13.L32A768j
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.H13.L32A768g

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem isSimpleGroup_of_psl {X : Type} [Group X] {n p f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n p f) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ _ _ _ h).2

omit [Finite G] in
theorem false_of_simple_of_mem_center {I : Subgroup G} (hs : IsSimpleGroup ↥I)
    (hq : CFSG.IsQuasisimple ↥I) {u : G} (huI : u ∈ I) (huC : ∀ x ∈ I, x * u = u * x)
    (hu1 : u ≠ 1) : False := by
  have hmem : (⟨u, huI⟩ : ↥I) ∈ Subgroup.center ↥I :=
    Subgroup.mem_center_iff.mpr fun x => Subtype.ext (huC x x.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥I) with hb | ht
  · rw [hb, Subgroup.mem_bot] at hmem
    exact hu1 (congrArg Subtype.val hmem)
  · obtain ⟨a, b, hab⟩ := hq.2.2
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    rw [ht]
    exact Subgroup.mem_top _

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

theorem lemma115Hyp_centralizer {z : G} (hzV1 : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (hgen : ∀ c ∈ fsuV1 T V, c = 1 ∨ c = z) {u : G} (hu : u ∈ u0 T V) (hu1 : u ≠ 1)
    (hS : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer ({u} : Set G))
      (Subgroup.centralizer ({u} : Set G))) :
    Lemma115Hyp (Subgroup.centralizer ({u} : Set G)) (T ⊓ Subgroup.centralizer ({u} : Set G))
      (hz T V) z := by
  have h := C.hyp
  obtain ⟨hVe, -, -, hV1, -⟩ := C.hMod G T L V h.hyp h.fsu
  have hHz := hz_eq_centralizer_singleton hzV1 hgen
  have huU : u ∈ fsuU T V := centralizerMod_le_left _ _ _ hu
  have hu2 : u ^ 2 = 1 := C.hUe u huU
  have huH : u ∈ hz T V := C.U_le_H huU
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hzV1).1
  have hV1H : fsuV1 T V ≤ hz T V := fun c hc => C.U_le_H ((le_conjClosure V _ : V ≤ fsuU T V)
    (Subgroup.mem_inf.mp hc).1)
  have hO2H : pCoreOf 2 (hz T V) ≠ ⊥ := by
    have hle : fsuV1 T V ≤ pCoreOf 2 (hz T V) :=
      le_pCoreOf_of_le_normalizer 2 hV1H (Subgroup.centralizer_le_normalizer _)
        (IsPGroup.of_card (n := 1) (by rw [hV1, pow_one]))
    intro hb
    rw [hb] at hle
    exact hz1 (Subgroup.mem_bot.mp (hle hzV1))
  obtain ⟨S, hSy⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hSH : (S : Subgroup G) ≤ hz T V := by
    rw [hSy]
    exact T_le_hz h C.h63
  have hchar : CharTwo (hz T V) := charTwo_of_inH h.fsu.qtke.2.1 S ⟨hSH, hO2H⟩
  have hzu : Subgroup.zpowers u ≤ Subgroup.centralizer ({u} : Set G) ⊓ hz T V :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, huH⟩)
  have hzuN : Subgroup.centralizer ({u} : Set G) ⊓ hz T V ≤
      Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    intro x hx
    refine mem_normalizer_of_forall_conj_mem fun y hy => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxc : Commute x u :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).1
    rw [(hxc.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  have hzu2 : IsPGroup 2 (Subgroup.zpowers u) := fun y =>
    ⟨1, Subtype.ext (by simpa using (isElemAbelian_zpowers_of_pow hu2).2 y y.2)⟩
  have huO : u ∈ pCoreOf 2 (Subgroup.centralizer ({u} : Set G) ⊓ hz T V) :=
    le_pCoreOf_of_le_normalizer 2 hzu hzuN hzu2 (Subgroup.mem_zpowers u)
  have hzZ : z ∈ quasithinOmegaOneCenter T := (Subgroup.mem_inf.mp hzV1).2
  have hzT : z ∈ T := (Subgroup.closure_le _).mpr (fun _ hx => hx.1.1) hzZ
  have hzCT : z ∈ Subgroup.centralizer (T : Set G) := quasithinOmegaOneCenter_le_centralizer T hzZ
  refine ⟨pCoreOf_centralizer_ne_bot hu1 (by rw [← pow_two]; exact hu2), hS, hchar, hO2H,
    inf_le_left.trans (T_le_hz h C.h63), fun x hx => ?_, hHz.ge, hz1,
    Subgroup.mem_inf.mpr ⟨hzT, ?_⟩, Subgroup.centralizer_le inf_le_left hzCT, hVe.2 z hzV⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 u huO).symm
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp huH z hzV1

theorem false_of_quasisimple (h13314 : A6.Stmt13_3_14) (hIdent : KG1468Ident)
    (hTwoRu : KG1468TwoRu) (hlist : Lemma115_3_List)
    (hR3 : ∀ w ∈ u0 T V, w ≠ 1 → T ≤ Subgroup.centralizer ({w} : Set G) →
      Subgroup.centralizer ({w} : Set G) ≤ hz T V)
    {u : G} (hu : u ∈ u0 T V) (hu1 : u ≠ 1) (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V)
    (hS : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer ({u} : Set G))
      (Subgroup.centralizer ({u} : Set G)))
    {I : Subgroup G} (hI : I ∈ cComp (Subgroup.centralizer ({u} : Set G)))
    (hIn : (I.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal) (hKI : kz T V ≤ I)
    (hne : I ≠ kz T V) (hq : CFSG.IsQuasisimple ↥I) : False := by
  have h := C.hyp
  have := h.fsu.simple
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V h.hyp h.fsu
  obtain ⟨z, hzV1, hz1, hgen⟩ := exists_gen_of_card_two hV1
  have hIu : I ≤ Subgroup.centralizer ({u} : Set G) := A3.subnormal_le hI.2.2.1
  have hIp : ⁅I, I⁆ = I := hI.2.1
  have huU : u ∈ fsuU T V := centralizerMod_le_left _ _ _ hu
  have huI : u ∈ I := hKI ((C.fsuU_le_pCoreOf_kz.trans (pCoreOf_le 2 _)) huU)
  have huC : ∀ x ∈ I, x * u = u * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hIu hx)
  have hu2 : u ^ 2 = 1 := C.hUe u huU
  have hcomp : IsComponentIn I (Subgroup.centralizer ({u} : Set G)) :=
    ⟨hIu, (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hIu)).2 hq, hIn.isSubnormal⟩
  have hcases := hlist G h.fsu.simple h.fsu.nonabelian
    (qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke) _ _ _ z
    (C.lemma115Hyp_centralizer hzV1 hz1 hgen hu hu1 hS) I hcomp
  have hcard2 : 2 ∣ Nat.card ↥(Subgroup.center ↥I) := by
    have hmem : (⟨u, huI⟩ : ↥I) ∈ Subgroup.center ↥I :=
      Subgroup.mem_center_iff.mpr fun x => Subtype.ext (huC x x.2)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have ho : orderOf (⟨⟨u, huI⟩, hmem⟩ : ↥(Subgroup.center ↥I)) = 2 :=
      orderOf_eq_prime (Subtype.ext (Subtype.ext hu2)) fun e => hu1 (by
        simpa using congrArg (fun w : ↥(Subgroup.center ↥I) => ((w : ↥I) : G)) e)
    rw [← ho]
    exact orderOf_dvd_natCard _
  rcases hcases with ⟨hsI, -, -⟩ | ⟨-, -, hL34, -⟩ | ⟨-, -, hc13, -, -⟩ | ⟨-, -, hc13, -, -⟩ |
    ⟨he, -⟩ | ⟨⟨s, hs, hsI⟩, hinner⟩
  · exact false_of_simple_of_mem_center hsI hq huI huC hu1
  · exact C.false_of_ident h13314 hIdent hzV1 hz1 hKI hne hq (Or.inl hL34)
  · rcases hc13 with e | e <;> rw [e] at hcard2 <;> norm_num at hcard2
  · rcases hc13 with e | e <;> rw [e] at hcard2 <;> norm_num at hcard2
  · rcases he with he | ⟨p, -, he⟩
    · exact false_of_simple_of_mem_center (isSimpleGroup_of_psl he) hq huI huC hu1
    · exact false_of_simple_of_mem_center (isSimpleGroup_of_psl he) hq huI huC hu1
  · by_cases hRu : s = .Ru
    · subst hRu
      exact C.false_of_ru hTwoRu hR3 hu hu1 hT hS hIu hIn hKI hne hIp hq hsI
    · exact C.false_of_ident h13314 hIdent hzV1 hz1 hKI hne hq
        (Or.inr ⟨⟨s, hs, hRu, hsI⟩, hinner⟩)

end Ctx764

end CFSG.Quasithin.H13.L32A
