module

public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbZeta
public import CFSG.RankThree.GF2n.Tim81.Sec4.SecRepFixed
public import CFSG.RankThree.GF2n.Tim81.Sec2.NatSumRecog
public import CFSG.RankThree.GF2n.Tim81.Sec4.VLeW0
public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbEpsilon
public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbDelta

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec2 CFSG.QuasithinUnique.Setup.X7
open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.QuotMod
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

private theorem xOf_le_of_le_of_le_normalizer {E : Subgroup G} (hVE : V ≤ E)
    (hN : H ≤ Subgroup.normalizer (E : Set G)) : Tim79a.xOf V H ≤ E := by
  refine iSup_le fun U => iSup_le fun hU => ?_
  obtain ⟨z, hzH, rfl⟩ := hU
  have hzE : conjSubgroup z E = E := conjSubgroup_eq_self_iff.mpr (hN hzH)
  rw [← hzE]
  exact Subgroup.map_mono hVE

theorem eq_sup_inf_Pc_conj_xOf (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) :
    Tim79a.xOf V H = (Pc M V ⊓ Tim79a.xOf V H) ⊔
      (conjSubgroup h₀ (Pc M V) ⊓ Tim79a.xOf V H) := by
  obtain ⟨y, hyH, hPy, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hN : H ≤ Subgroup.normalizer
      (((Pc M V ⊓ Tim79a.xOf V H) ⊔
        (conjSubgroup y (Pc M V) ⊓ Tim79a.xOf V H) : Subgroup G) : Set G) :=
    le_normalizer_sup_inf_Pc_conj_of_mem h hPH hVH hyH hHy
      (W₀ := Tim79a.xOf V H) (hW₀ := le_refl _) (hN := Tim79a.H_le_normalizer_xOf V H)
  rw [← hPy] at hN
  refine le_antisymm ?_ (sup_le inf_le_right inf_le_right)
  exact xOf_le_of_le_of_le_normalizer (E := (Pc M V ⊓ Tim79a.xOf V H) ⊔
    (conjSubgroup h₀ (Pc M V) ⊓ Tim79a.xOf V H))
    (fun v hv => Subgroup.mem_sup_left
      (Subgroup.mem_inf.mpr ⟨h.toHyp.le_Pc hv, le_xOf_self V H hv⟩))
    hN

private abbrev secPc (M V H : Subgroup G) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) : Subgroup (SL(2, F)) :=
  (imgK V H (Pc M V)).map ψ

private abbrev secConjPc (M V H : Subgroup G) (h₀ : G) {F : Type} [Field F] [Fintype F]
    [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) : Subgroup (SL(2, F)) :=
  (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ

section C15Aux

variable {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
variable [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
variable {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
variable (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
variable {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
variable (hs : QuotMod.Hyp H (Tim79a.xOf V H) W₀)
variable [(W₀.subgroupOf (Tim79a.xOf V H)).Normal]
variable [Module (ZMod 2) (SecMod hs)]
variable (hKsec : ∀ k ∈ kOf V H, ∀ n ∈ Tim79a.xOf V H, k * n * k⁻¹ * n⁻¹ ∈ W₀)

private theorem hKsec_of_hyp : ∀ k ∈ kOf V H, ∀ n ∈ Tim79a.xOf V H, k * n * k⁻¹ * n⁻¹ ∈ W₀ := by
  intro k hk n hn
  have hcomm : n * k = k * n :=
    Subgroup.mem_centralizer_iff.mp ((mem_kOf_iff.mp hk).2) n hn
  rw [← hcomm]
  have h1 : n * k * k⁻¹ * n⁻¹ = 1 := by group
  rw [h1]
  exact W₀.one_mem

private theorem subSec_inf_Pc_le_fixedSub
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) :
    subSec hs (Pc M V ⊓ Tim79a.xOf V H) ≤ fixedSub (repSec hs hKsec SL(2, F) ψ)
      (secPc M V H ψ) := by
  have hcomm : ⁅Pc M V ⊓ Tim79a.xOf V H, Pc M V⁆ ≤ V ⊓ W₀ :=
    commutator_inf_xOf_le h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne
  intro v hv
  obtain ⟨n, hn⟩ := (mem_subSec_iff hs).1 hv
  rw [← hn, CFSG.QuasithinUnique.Setup.X7.mem_fixedSub]
  intro a ha
  obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp ha
  obtain ⟨z, hzP, hzy⟩ := (mem_imgK_iff).mp hy
  rw [← hya, ← hzy]
  refine (SecRepFixed.fixed_iff_commutator_mem (N := Tim79a.xOf V H) (N₀ := W₀)
    (hs := hs) (ψ := ψ) (hKsec := hKsec)
    (z := z) (n := Subgroup.inclusion inf_le_right n)).mpr ?_
  exact (inf_le_right : V ⊓ W₀ ≤ W₀)
    (hcomm (Subgroup.commutator_mem_commutator n.2.1 hzP))

private theorem subSec_conj_inf_Pc_le_fixedSub
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) :
    subSec hs (conjSubgroup h₀ (Pc M V) ⊓ Tim79a.xOf V H) ≤
      fixedSub (repSec hs hKsec SL(2, F) ψ) (secConjPc M V H h₀ ψ) := by
  have hann : ⁅conjSubgroup h₀ (Pc M V) ⊓ Tim79a.xOf V H,
      conjSubgroup h₀ (Pc M V) ⊓ kOf V H⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have hcomm : a * b = b * a :=
      Subgroup.mem_centralizer_iff.mp ((mem_kOf_iff.mp hb.2).2) a ha.2
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have hcomm : ⁅conjSubgroup h₀ (Pc M V) ⊓ Tim79a.xOf V H,
      conjSubgroup h₀ (Pc M V)⁆ ≤ conjSubgroup h₀ V ⊓ W₀ :=
    commutator_le_inf_conj_of_commutator_inf_conj_kOf_eq_bot h hPH hVH hH hnM hK hnab hL
      hW₀ hN hW₀ne inf_le_left hann
  intro v hv
  obtain ⟨n, hn⟩ := (mem_subSec_iff hs).1 hv
  rw [← hn, CFSG.QuasithinUnique.Setup.X7.mem_fixedSub]
  intro a ha
  obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp ha
  obtain ⟨z, hzP, hzy⟩ := (mem_imgK_iff).mp hy
  rw [← hya, ← hzy]
  refine (SecRepFixed.fixed_iff_commutator_mem (N := Tim79a.xOf V H) (N₀ := W₀)
    (hs := hs) (ψ := ψ) (hKsec := hKsec)
    (z := z) (n := Subgroup.inclusion inf_le_right n)).mpr ?_
  exact (inf_le_right : conjSubgroup h₀ V ⊓ W₀ ≤ W₀)
    (hcomm (Subgroup.commutator_mem_commutator n.2.1 hzP))

private theorem exists_mul_eq_of_mem_xOf (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) {n : G} (hn : n ∈ Tim79a.xOf V H) :
    ∃ x ∈ Pc M V ⊓ Tim79a.xOf V H, ∃ y ∈ conjSubgroup h₀ (Pc M V) ⊓ Tim79a.xOf V H,
      x * y = n := by
  have h5 := eq_sup_inf_Pc_conj_xOf h hPH hVH hH
  refine CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute ?_ ?_
  · intro a ha b hb
    exact congrArg Subtype.val ((isElemAbelian_xOf h hPH hVH).1.is_comm.comm
      ⟨a, (inf_le_right : Pc M V ⊓ Tim79a.xOf V H ≤ Tim79a.xOf V H) ha⟩
        ⟨b, (inf_le_right : conjSubgroup h₀ (Pc M V) ⊓ Tim79a.xOf V H ≤ Tim79a.xOf V H) hb⟩)
  · rw [← h5]
    exact hn

private theorem mem_W0_of_mem_conj_inf_xOf_of_fixed
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    {y : G} (hy : y ∈ conjSubgroup h₀ (Pc M V) ⊓ Tim79a.xOf V H)
    (hfix : SecMod.mk hs ⟨y, hy.2⟩ ∈
      fixedSub (repSec hs hKsec SL(2, F) ψ) (secPc M V H ψ)) :
    y ∈ W₀ := by
  obtain ⟨x₀, hx₀P, hx₀K⟩ := exists_mem_Pc_not_mem_kOf h hPH hH hnM
  have hx₀H : x₀ ∈ H := hPH hx₀P
  have ha₀ : ψ (piK V H ⟨x₀, hx₀H⟩) ∈ secPc M V H ψ :=
    Subgroup.mem_map.mpr ⟨piK V H ⟨x₀, hx₀H⟩,
      (mem_imgK_iff).mpr ⟨⟨x₀, hx₀H⟩, hx₀P, rfl⟩, rfl⟩
  have hcomm : ⁅(y : G), x₀⁆ ∈ W₀ :=
    (SecRepFixed.fixed_iff_commutator_mem (N := Tim79a.xOf V H) (N₀ := W₀)
      (hs := hs) (ψ := ψ) (hKsec := hKsec)
      (z := ⟨x₀, hx₀H⟩) (n := ⟨y, hy.2⟩)).mp
      (CFSG.QuasithinUnique.Setup.X7.mem_fixedSub.mp hfix _ ha₀)
  have hcomm' : ⁅x₀, (y : G)⁆ ∈ W₀ := by
    rw [show ⁅x₀, (y : G)⁆ = ⁅(y : G), x₀⁆⁻¹ from (commutatorElement_inv (y : G) x₀).symm]
    exact W₀.inv_mem hcomm
  exact mem_W0_of_mem_conj_inf_xOf_of_commutator_mem h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne
    ψ hl horth hy hx₀P hx₀K hcomm'

private theorem mem_W0_of_mem_inf_xOf_of_fixed
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    {x : G} (hx : x ∈ Pc M V ⊓ Tim79a.xOf V H)
    (hfix : SecMod.mk hs ⟨x, hx.2⟩ ∈
      fixedSub (repSec hs hKsec SL(2, F) ψ) (secConjPc M V H h₀ ψ)) :
    x ∈ W₀ := by
  obtain ⟨y₀, hy₀, hy₀K⟩ := exists_mem_conj_not_mem_kOf h hH hnM
  have hy₀H : y₀ ∈ H := (by rw [hH]; exact Subgroup.mem_sup_right hy₀)
  have ha₀ : ψ (piK V H ⟨y₀, hy₀H⟩) ∈ secConjPc M V H h₀ ψ :=
    Subgroup.mem_map.mpr ⟨piK V H ⟨y₀, hy₀H⟩,
      (mem_imgK_iff).mpr ⟨⟨y₀, hy₀H⟩, hy₀, rfl⟩, rfl⟩
  have hcomm : ⁅(x : G), y₀⁆ ∈ W₀ :=
    (SecRepFixed.fixed_iff_commutator_mem (N := Tim79a.xOf V H) (N₀ := W₀)
      (hs := hs) (ψ := ψ) (hKsec := hKsec)
      (z := ⟨y₀, hy₀H⟩) (n := ⟨x, hx.2⟩)).mp
      (CFSG.QuasithinUnique.Setup.X7.mem_fixedSub.mp hfix _ ha₀)
  have hcomm' : ⁅y₀, (x : G)⁆ ∈ W₀ := by
    rw [show ⁅y₀, (x : G)⁆ = ⁅(x : G), y₀⁆⁻¹ from (commutatorElement_inv (x : G) y₀).symm]
    exact W₀.inv_mem hcomm
  exact mem_W0_of_mem_inf_xOf_of_commutator_mem h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne
    ψ hl horth hx hy₀ hy₀K hcomm'

private theorem fixedSub_top_eq_bot
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN)) :
    fixedSub (repSec hs hKsec SL(2, F) ψ) (⊤ : Subgroup SL(2, F)) = ⊥ := by
  let ρ := repSec hs hKsec SL(2, F) ψ
  refine le_antisymm ?_ bot_le
  intro w hw
  have hwA : w ∈ fixedSub ρ (secPc M V H ψ) := fun a _ => hw a (Subgroup.mem_top a)
  have hwA' : w ∈ fixedSub ρ (secConjPc M V H h₀ ψ) := fun a _ => hw a (Subgroup.mem_top a)
  obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs w
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_eq_of_mem_xOf h hPH hVH hH n.2
  have hnk : SecMod.mk hs n = SecMod.mk hs ⟨x, hx.2⟩ + SecMod.mk hs ⟨y, hy.2⟩ := by
    rw [← SecMod.mk_mul hs]
    exact congrArg (SecMod.mk hs) (Subtype.ext hxy.symm)
  have hxfix : SecMod.mk hs ⟨x, hx.2⟩ ∈ fixedSub ρ (secPc M V H ψ) :=
    subSec_inf_Pc_le_fixedSub (h := h) (hPH := hPH) (hVH := hVH) (hH := hH) (hnM := hnM)
      (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN) (hW₀ne := hW₀ne)
      (ψ := ψ) (hs := hs) (hKsec := hKsec)
      (SecRepFixed.mk_mem_subSec_of_mem (N := Tim79a.xOf V H) (N₀ := W₀) (hs := hs)
        (E := Pc M V ⊓ Tim79a.xOf V H) (n := ⟨x, hx.2⟩) hx)
  have hyfix : SecMod.mk hs ⟨y, hy.2⟩ ∈ fixedSub ρ (secPc M V H ψ) := by
    have hsub := (fixedSub ρ (secPc M V H ψ)).sub_mem hwA hxfix
    rwa [hnk, add_sub_cancel_left] at hsub
  have hyW0 : y ∈ W₀ :=
    mem_W0_of_mem_conj_inf_xOf_of_fixed (h := h) (hPH := hPH) (hVH := hVH) (hH := hH)
      (hnM := hnM) (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN)
      (hW₀ne := hW₀ne) (ψ := ψ) (hs := hs) (hKsec := hKsec) (hl := hl) (horth := horth)
      hy hyfix
  have hyfix' : SecMod.mk hs ⟨y, hy.2⟩ ∈ fixedSub ρ (secConjPc M V H h₀ ψ) :=
    subSec_conj_inf_Pc_le_fixedSub (h := h) (hPH := hPH) (hVH := hVH) (hH := hH) (hnM := hnM)
      (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN) (hW₀ne := hW₀ne)
      (ψ := ψ) (hs := hs) (hKsec := hKsec)
      (SecRepFixed.mk_mem_subSec_of_mem (N := Tim79a.xOf V H) (N₀ := W₀) (hs := hs)
        (E := conjSubgroup h₀ (Pc M V) ⊓ Tim79a.xOf V H)
        (n := ⟨y, hy.2⟩) hy)
  have hxfix' : SecMod.mk hs ⟨x, hx.2⟩ ∈ fixedSub ρ (secConjPc M V H h₀ ψ) := by
    have hsub := (fixedSub ρ (secConjPc M V H h₀ ψ)).sub_mem hwA' hyfix'
    rwa [hnk, add_sub_cancel_right] at hsub
  have hxW0 : x ∈ W₀ :=
    mem_W0_of_mem_inf_xOf_of_fixed (h := h) (hPH := hPH) (hVH := hVH) (hH := hH)
      (hnM := hnM) (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN)
      (hW₀ne := hW₀ne) (ψ := ψ) (hs := hs) (hKsec := hKsec) (hl := hl) (horth := horth)
      hx hxfix'
  have h0x : SecMod.mk hs ⟨x, hx.2⟩ = 0 := (SecMod.mk_eq_zero_iff hs _).mpr hxW0
  have h0y : SecMod.mk hs ⟨y, hy.2⟩ = 0 := (SecMod.mk_eq_zero_iff hs _).mpr hyW0
  rw [hnk, h0x, h0y, zero_add]
  exact (⊥ : Submodule (ZMod 2) (SecMod hs)).zero_mem

private theorem quad_repSec
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) :
    ∀ a ∈ secPc M V H ψ, ∀ b ∈ secPc M V H ψ,
      (repSec hs hKsec SL(2, F) ψ a - 1) ∘ₗ (repSec hs hKsec SL(2, F) ψ b - 1) = 0 := by
  have hcommW : ⁅Tim79a.xOf V H, Pc M V⁆ ≤ Pc M V ⊓ Tim79a.xOf V H :=
    commutator_W0_Pc_le h hPH hVH (W₀ := Tim79a.xOf V H) le_rfl
      (Tim79a.H_le_normalizer_xOf V H)
  intro a ha b hb
  obtain ⟨b', hb', hb''⟩ := Subgroup.mem_map.mp hb
  obtain ⟨z, hzP, hzy⟩ := (mem_imgK_iff).mp hb'
  rw [← hb'', ← hzy]
  refine LinearMap.ext fun w => ?_
  obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs w
  have hd := SecRepFixed.repSec_sub_eq_mk (N := Tim79a.xOf V H) (N₀ := W₀) (hs := hs)
    (ψ := ψ) (hKsec := hKsec) (z := z) (n := n)
  have hmem : repSec hs hKsec SL(2, F) ψ (ψ (piK V H z)) (SecMod.mk hs n) - SecMod.mk hs n ∈
      subSec hs (Pc M V ⊓ Tim79a.xOf V H) := by
    rw [hd]
    have hc : ⁅(n : G), (z : G)⁆ ∈ Pc M V ⊓ Tim79a.xOf V H :=
      hcommW (Subgroup.commutator_mem_commutator n.2 hzP)
    exact SecRepFixed.mk_mem_subSec_of_mem (N := Tim79a.xOf V H) (N₀ := W₀) (hs := hs)
      (E := Pc M V ⊓ Tim79a.xOf V H) (n := ⟨_, _⟩)
      (Subgroup.mem_inf.mpr ⟨(Pc M V).inv_mem hc.1, (Tim79a.xOf V H).inv_mem hc.2⟩)
  have hfix := subSec_inf_Pc_le_fixedSub (h := h) (hPH := hPH) (hVH := hVH) (hH := hH)
    (hnM := hnM) (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN)
    (hW₀ne := hW₀ne) (ψ := ψ) (hs := hs) (hKsec := hKsec) hmem
  rw [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply]
  exact sub_eq_zero.mpr (CFSG.QuasithinUnique.Setup.X7.mem_fixedSub.mp hfix a ha)

private theorem map_subSec_conj {y : G} (hyH : y ∈ H) (E : Subgroup G) :
    (subSec hs E).map (repSec hs hKsec SL(2, F) ψ (ψ (piK V H ⟨y, hyH⟩))) =
      subSec hs (conjSubgroup y E) := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨n, hn⟩ := (mem_subSec_iff hs).1 hu
    rw [← hn, repSec_apply_piK_mk hs hKsec SL(2, F) ψ ⟨y, hyH⟩]
    refine (mem_subSec_iff hs).2 ⟨⟨y * (n : G) * y⁻¹, ⟨?_, ?_⟩⟩, ?_⟩
    · refine mem_conjSubgroup.mpr ?_
      have h2 : y⁻¹ * (y * (n : G) * y⁻¹) * y = (n : G) := by group
      rw [h2]
      exact n.2.1
    · exact (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H hyH) (n : G)).mp n.2.2
    · exact congrArg (SecMod.mk hs) (Subtype.ext rfl)
  · intro hv
    obtain ⟨m, hm⟩ := (mem_subSec_iff hs).1 hv
    rw [← hm]
    obtain ⟨n, hnE, hnym⟩ := Subgroup.mem_map.mp m.2.1
    have hnym' : y * n * y⁻¹ = (m : G) := by
      simpa [MulAut.conj_apply] using hnym
    have hnW : n ∈ Tim79a.xOf V H := by
      have h := (Subgroup.mem_normalizer_iff.mp
        (Tim79a.H_le_normalizer_xOf V H (H.inv_mem hyH)) (m : G)).mp m.2.2
      have h' : y⁻¹ * (y * n * y⁻¹) * (y⁻¹)⁻¹ ∈ Tim79a.xOf V H := by
        simpa only [hnym'] using h
      have h2 : y⁻¹ * (y * n * y⁻¹) * (y⁻¹)⁻¹ = n := by group
      rwa [h2] at h'
    refine Submodule.mem_map.mpr ⟨SecMod.mk hs ⟨n, hnW⟩, ?_, ?_⟩
    · exact (mem_subSec_iff hs).2 ⟨⟨n, ⟨hnE, hnW⟩⟩,
        congrArg (SecMod.mk hs) (Subtype.ext rfl)⟩
    · rw [repSec_apply_piK_mk hs hKsec SL(2, F) ψ ⟨y, hyH⟩]
      exact congrArg (SecMod.mk hs) (Subtype.ext hnym')

theorem isNatSumModule_repSec
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN)) :
    Sec2.IsNatSumModule (repSec hs hKsec SL(2, F) ψ) := by
  have hd1 := subSec_inf_Pc_le_fixedSub (h := h) (hPH := hPH) (hVH := hVH) (hH := hH)
    (hnM := hnM) (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN)
    (hW₀ne := hW₀ne) (ψ := ψ) (hs := hs) (hKsec := hKsec)
  have hd2 := subSec_conj_inf_Pc_le_fixedSub (h := h) (hPH := hPH) (hVH := hVH) (hH := hH)
    (hnM := hnM) (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN)
    (hW₀ne := hW₀ne) (ψ := ψ) (hs := hs) (hKsec := hKsec)
  have hsum : subSec hs (Pc M V ⊓ Tim79a.xOf V H) ⊔
      subSec hs (conjSubgroup h₀ (Pc M V) ⊓ Tim79a.xOf V H) = ⊤ := by
    rw [← subSec_sup hs (inf_le_right : Pc M V ⊓ Tim79a.xOf V H ≤ Tim79a.xOf V H)
      (inf_le_right : conjSubgroup h₀ (Pc M V) ⊓ Tim79a.xOf V H ≤ Tim79a.xOf V H),
      ← eq_sup_inf_Pc_conj_xOf h hPH hVH hH, subSec_self]
  have hspan : fixedSub (repSec hs hKsec SL(2, F) ψ) (secPc M V H ψ) ⊔
      fixedSub (repSec hs hKsec SL(2, F) ψ) (secConjPc M V H h₀ ψ) = ⊤ := by
    refine le_antisymm (sup_le le_top le_top) ?_
    rw [← hsum]
    exact sup_le (hd1.trans le_sup_left) (hd2.trans le_sup_right)
  obtain ⟨-, -, a, b, ha, hb, hne⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  refine Sec2.isNatSumModule_of_fixedSub_conj (repSec hs hKsec SL(2, F) ψ)
    (fixedSub_top_eq_bot (h := h) (hPH := hPH) (hVH := hVH) (hH := hH) (hnM := hnM)
      (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN) (hW₀ne := hW₀ne)
      (ψ := ψ) (hs := hs) (hKsec := hKsec) (hl := hl) (horth := horth)) hne ?_ ?_
  · rw [← ha]
    exact quad_repSec (h := h) (hPH := hPH) (hVH := hVH) (hH := hH) (hnM := hnM) (hK := hK)
      (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN) (hW₀ne := hW₀ne)
      (ψ := ψ) (hs := hs) (hKsec := hKsec)
  · rw [← ha, ← hb]
    exact hspan

end C15Aux

private theorem subSec_V_le_fixedSub_secPc
    {W₀ : Subgroup G} (hs : QuotMod.Hyp H (Tim79a.xOf V H) W₀)
    [(W₀.subgroupOf (Tim79a.xOf V H)).Normal]
    [Module (ZMod 2) (SecMod hs)]
    (hKsec : ∀ k ∈ kOf V H, ∀ n ∈ Tim79a.xOf V H, k * n * k⁻¹ * n⁻¹ ∈ W₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) :
    subSec hs V ≤ fixedSub (repSec hs hKsec SL(2, F) ψ) (secPc M V H ψ) := by
  intro u hu
  obtain ⟨n, hn⟩ := (mem_subSec_iff hs).1 hu
  rw [← hn, CFSG.QuasithinUnique.Setup.X7.mem_fixedSub]
  intro c hc
  obtain ⟨y₁, hy₁, hy₁c⟩ := Subgroup.mem_map.mp hc
  obtain ⟨z, hzP, hzy⟩ := (mem_imgK_iff).mp hy₁
  rw [← hy₁c, ← hzy]
  refine (SecRepFixed.fixed_iff_commutator_mem (N := Tim79a.xOf V H) (N₀ := W₀)
    (hs := hs) (ψ := ψ) (hKsec := hKsec)
    (z := z) (n := Subgroup.inclusion inf_le_right n)).mpr ?_
  have hzC : (z : G) ∈ Subgroup.centralizer (V : Set G) :=
    (inf_le_right : Pc M V ≤ Subgroup.centralizer (V : Set G)) hzP
  have hVn : ((Subgroup.inclusion inf_le_right n : ↥(Tim79a.xOf V H)) : G) ∈ V := n.2.1
  have hcomm : ((Subgroup.inclusion inf_le_right n : ↥(Tim79a.xOf V H)) : G) * (z : G) =
      (z : G) * ((Subgroup.inclusion inf_le_right n : ↥(Tim79a.xOf V H)) : G) :=
    Subgroup.mem_centralizer_iff.mp hzC _ hVn
  have h1 : ⁅((Subgroup.inclusion inf_le_right n : ↥(Tim79a.xOf V H)) : G), (z : G)⁆ = 1 := by
    rw [commutatorElement_def, hcomm]
    group
  rw [h1]
  exact W₀.one_mem

private theorem normalizer_secPc_le_normalizer_subSec_V (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {W₀ : Subgroup G} (hs : QuotMod.Hyp H (Tim79a.xOf V H) W₀)
    [(W₀.subgroupOf (Tim79a.xOf V H)).Normal]
    [Module (ZMod 2) (SecMod hs)]
    (hKsec : ∀ k ∈ kOf V H, ∀ n ∈ Tim79a.xOf V H, k * n * k⁻¹ * n⁻¹ ∈ W₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) :
    ∀ g ∈ Subgroup.normalizer (secPc M V H ψ : Set (SL(2, F))),
      ∀ u ∈ subSec hs V, repSec hs hKsec SL(2, F) ψ g u ∈ subSec hs V := by
  intro g hg u hu
  obtain ⟨z, hz⟩ := piK_surjective V H (ψ.symm g)
  have hgz : g = ψ (piK V H z) := by
    rw [hz, MulEquiv.apply_symm_apply]
  have hmap := Subgroup.map_normalizer_eq_of_bijective (imgK V H (Pc M V))
    (f := ψ.toMonoidHom) ψ.bijective
  have hmemN : ψ (piK V H z) ∈
      (Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))).map ψ.toMonoidHom := by
    rw [hmap]
    rwa [← hgz]
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hmemN
  have hw_eq : w = piK V H z := ψ.injective hwz
  have hzM : (z : G) ∈ M := by
    have hzN : piK V H z ∈ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
      rw [hw_eq] at hw
      exact hw
    exact (mem_M_and_mem_normalizer_inf_of_mem_normalizer_imgK h hPH hzN).1
  have hzV : ∀ v ∈ V, (z : G) * v * (z : G)⁻¹ ∈ V := by
    intro v hv
    exact (Subgroup.mem_normalizer_iff.mp (h.toHyp.maxAb.1.2.1 hzM) v).mp hv
  obtain ⟨n, hn⟩ := (mem_subSec_iff hs).1 hu
  rw [← hn, hgz, repSec_apply_piK_mk hs hKsec SL(2, F) ψ z]
  refine (mem_subSec_iff hs).2 ⟨⟨(z : G) * (n : G) * (z : G)⁻¹, ⟨?_, ?_⟩⟩, ?_⟩
  · exact hzV _ n.2.1
  · exact (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H z.2) (n : G)).mp
      n.2.2
  · exact congrArg (SecMod.mk hs) (Subtype.ext rfl)

private theorem not_mem_normalizer_secPc_of_mem_conj (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {y : G} (hyH : y ∈ H)
    (hPy : conjSubgroup h₀ (Pc M V) = conjSubgroup y (Pc M V)) :
    ψ (piK V H ⟨y, hyH⟩) ∉ Subgroup.normalizer (secPc M V H ψ : Set (SL(2, F))) := by
  intro hg
  have hmap := Subgroup.map_normalizer_eq_of_bijective (imgK V H (Pc M V))
    (f := ψ.toMonoidHom) ψ.bijective
  have hmemN : ψ (piK V H ⟨y, hyH⟩) ∈
      (Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))).map ψ.toMonoidHom := by
    rw [hmap]
    exact hg
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hmemN
  have hw_eq : w = piK V H ⟨y, hyH⟩ := ψ.injective hwz
  have hzN : piK V H ⟨y, hyH⟩ ∈ Subgroup.normalizer
      (imgK V H (Pc M V) : Set (HBar V H)) := by
    rw [hw_eq] at hw
    exact hw
  have hconj : conjSubgroup (piK V H ⟨y, hyH⟩) (imgK V H (Pc M V)) =
      imgK V H (Pc M V) := conjSubgroup_eq_self_iff.mpr hzN
  have hkey := imgK_conjSubgroup (V := V) (H := H) hyH hPH
  rw [hconj] at hkey
  exact (imgK_ne_bot_and_ne_of_sup h hPH hH hnM).2 (by rw [← hkey, hPy])

private theorem map_invariant_subSec_V
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    (hs : QuotMod.Hyp H (Tim79a.xOf V H) W₀)
    [(W₀.subgroupOf (Tim79a.xOf V H)).Normal]
    [Module (ZMod 2) (SecMod hs)]
    (hKsec : ∀ k ∈ kOf V H, ∀ n ∈ Tim79a.xOf V H, k * n * k⁻¹ * n⁻¹ ∈ W₀)
    {y : G} (hyH : y ∈ H)
    (hPy : conjSubgroup h₀ (Pc M V) = conjSubgroup y (Pc M V)) :
    ∀ g, ∀ w ∈ subSec hs V ⊔ (subSec hs V).map
        (repSec hs hKsec SL(2, F) ψ (ψ (piK V H ⟨y, hyH⟩))),
      repSec hs hKsec SL(2, F) ψ g w ∈ subSec hs V ⊔ (subSec hs V).map
        (repSec hs hKsec SL(2, F) ψ (ψ (piK V H ⟨y, hyH⟩))) := by
  have hρ : Sec2.IsNatSumModule (repSec hs hKsec SL(2, F) ψ) :=
    isNatSumModule_repSec (hW := hW) (W₀ := W₀) (h := h) (hPH := hPH) (hVH := hVH)
      (hH := hH) (hnM := hnM) (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀)
      (hN := hN) (hW₀ne := hW₀ne) (ψ := ψ) (hs := hs) (hKsec := hKsec) (hl := hl)
      (horth := horth)
  obtain ⟨hA2, hAcard, -⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  have hUA : subSec hs V ≤ fixedSub (repSec hs hKsec SL(2, F) ψ) (secPc M V H ψ) :=
    subSec_V_le_fixedSub_secPc (W₀ := W₀) (hs := hs) (hKsec := hKsec) (ψ := ψ)
  have hUN : ∀ g ∈ Subgroup.normalizer (secPc M V H ψ : Set (SL(2, F))),
      ∀ u ∈ subSec hs V, repSec hs hKsec SL(2, F) ψ g u ∈ subSec hs V :=
    normalizer_secPc_le_normalizer_subSec_V h hPH (W₀ := W₀) (hs := hs) (hKsec := hKsec)
      (ψ := ψ)
  have hψnotN : ψ (piK V H ⟨y, hyH⟩) ∉
      Subgroup.normalizer (secPc M V H ψ : Set (SL(2, F))) :=
    not_mem_normalizer_secPc_of_mem_conj h hPH hH hnM (ψ := ψ) (hyH := hyH) (hPy := hPy)
  exact Sec2.sup_map_invariant_of_isNatSumModule (repSec hs hKsec SL(2, F) ψ) hρ hA2 hAcard
    hUA hUN hψnotN

private theorem subSec_sup_sup_conj_eq
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hs : QuotMod.Hyp H (Tim79a.xOf V H) W₀)
    [(W₀.subgroupOf (Tim79a.xOf V H)).Normal]
    [Module (ZMod 2) (SecMod hs)]
    (hKsec : ∀ k ∈ kOf V H, ∀ n ∈ Tim79a.xOf V H, k * n * k⁻¹ * n⁻¹ ∈ W₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {h₀ : G} {y : G} (hyH : y ∈ H)
    (hVy : conjSubgroup h₀ V = conjSubgroup y V) :
    subSec hs (W₀ ⊔ V ⊔ conjSubgroup h₀ V) =
      subSec hs V ⊔ (subSec hs V).map
        (repSec hs hKsec SL(2, F) ψ (ψ (piK V H ⟨y, hyH⟩))) := by
  rw [hVy, subSec_sup hs (sup_le hW₀ (le_xOf_self V H))
      (conjSubgroup_le_xOf_of_mem (V := V) (H := H) hyH),
    subSec_sup hs hW₀ (le_xOf_self V H),
    subSec_eq_bot_of_le (N := Tim79a.xOf V H) (N₀ := W₀) (hs := hs) (E := W₀)
      le_rfl, bot_sup_eq,
    map_subSec_conj (W₀ := W₀) (ψ := ψ) (hs := hs) (hKsec := hKsec) (hyH := hyH) V]

private theorem normalizer_sup_sup_conj
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    (hs : QuotMod.Hyp H (Tim79a.xOf V H) W₀)
    [(W₀.subgroupOf (Tim79a.xOf V H)).Normal]
    [Module (ZMod 2) (SecMod hs)]
    (hKsec : ∀ k ∈ kOf V H, ∀ n ∈ Tim79a.xOf V H, k * n * k⁻¹ * n⁻¹ ∈ W₀)
    {y : G} (hyH : y ∈ H)
    (hPy : conjSubgroup h₀ (Pc M V) = conjSubgroup y (Pc M V))
    (hVy : conjSubgroup h₀ V = conjSubgroup y V) :
    H ≤ Subgroup.normalizer ((W₀ ⊔ V ⊔ conjSubgroup h₀ V : Subgroup G) : Set G) := by
  have hVh_le : conjSubgroup h₀ V ≤ Tim79a.xOf V H := by
    rw [hVy]
    exact conjSubgroup_le_xOf_of_mem (V := V) (H := H) hyH
  refine (normalizer_subSec_iff hs hKsec ψ (le_sup_of_le_left (le_sup_of_le_left le_rfl))
    (sup_le (sup_le hW₀ (le_xOf_self V H)) hVh_le)).mpr ?_
  intro x v hv
  rw [subSec_sup_sup_conj_eq (W₀ := W₀) (hW₀ := hW₀) (hs := hs) (hKsec := hKsec)
    (ψ := ψ) (hyH := hyH) (hVy := hVy)] at hv ⊢
  exact map_invariant_subSec_V (h := h) (hPH := hPH) (hVH := hVH) (hH := hH) (hnM := hnM)
    (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN) (hW₀ne := hW₀ne)
    (ψ := ψ) (hl := hl) (horth := horth) (hW := hW) (hs := hs) (hKsec := hKsec)
    (hyH := hyH) (hPy := hPy) x v hv

theorem eq_sup_sup_conj_of_isNatSumModule
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN)) :
    Tim79a.xOf V H = W₀ ⊔ V ⊔ conjSubgroup h₀ V := by
  classical
  have hsq : ∀ n ∈ Tim79a.xOf V H, n * n ∈ W₀ := by
    intro n hn
    have h1 : n * n = 1 := by
      simpa [pow_two] using hW.2 n hn
    rw [h1]
    exact W₀.one_mem
  let hs : QuotMod.Hyp H (Tim79a.xOf V H) W₀ :=
    { le := hW₀
      comm := by
        intro n hn n' hn'
        have hc : n * n' = n' * n :=
          congrArg Subtype.val (hW.1.is_comm.comm ⟨n, hn⟩ ⟨n', hn'⟩)
        have h1 : n * n' * n⁻¹ * n'⁻¹ = 1 := by rw [hc]; group
        rw [h1]
        exact W₀.one_mem
      conj := by
        intro g hg n hn
        exact (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H hg) n).mp hn
      conj₀ := by
        intro g hg n hn
        exact (Subgroup.mem_normalizer_iff.mp (hN hg) n).mp hn }
  haveI hNorm : (W₀.subgroupOf (Tim79a.xOf V H)).Normal := hs.normal
  haveI hMod : Module (ZMod 2) (SecMod hs) := SecMod.module hs hsq
  let hKsec : ∀ k ∈ kOf V H, ∀ n ∈ Tim79a.xOf V H, k * n * k⁻¹ * n⁻¹ ∈ W₀ :=
    hKsec_of_hyp
  obtain ⟨y, hyH, hPy, hVy, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hE'norm : H ≤ Subgroup.normalizer
      ((W₀ ⊔ V ⊔ conjSubgroup h₀ V : Subgroup G) : Set G) :=
    normalizer_sup_sup_conj (hW := hW) (h := h) (hPH := hPH) (hVH := hVH) (hH := hH)
      (hnM := hnM) (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN)
      (hW₀ne := hW₀ne) (ψ := ψ) (hl := hl) (horth := horth) (hs := hs) (hKsec := hKsec)
      (hyH := hyH) (hPy := hPy) (hVy := hVy)
  refine le_antisymm ?_ ?_
  · exact xOf_le_of_le_of_le_normalizer (V := V) (H := H)
      (le_sup_of_le_left le_sup_right) hE'norm
  · exact sup_le (sup_le hW₀ (le_xOf_self V H)) (by
      rw [hVy]
      exact conjSubgroup_le_xOf_of_mem (V := V) (H := H) hyH)

private theorem inf_Pc_sup_conj_eq_inf
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    (h : RootHyp M V) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hW0le : W₀ ≤ (Pc M V ⊓ W₀) ⊔ conjSubgroup h₀ V)
    {y : G} (hyH : y ∈ H) (hVy : conjSubgroup h₀ V = conjSubgroup y V) :
    Pc M V ⊓ (W₀ ⊔ conjSubgroup h₀ V) = Pc M V ⊓ W₀ := by
  have hVh_le : conjSubgroup h₀ V ≤ Tim79a.xOf V H := by
    rw [hVy]
    exact conjSubgroup_le_xOf_of_mem (V := V) (H := H) hyH
  have hcommW : ∀ a ∈ Tim79a.xOf V H, ∀ b ∈ Tim79a.xOf V H, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hW.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxW : x ∈ (Pc M V ⊓ W₀) ⊔ conjSubgroup h₀ V := (sup_le hW0le le_sup_right) hx.2
    have hcommAB : ∀ a ∈ Pc M V ⊓ W₀, ∀ b ∈ conjSubgroup h₀ V, a * b = b * a := by
      intro a ha b hb
      exact hcommW a (hW₀ (Subgroup.mem_inf.mp ha).2) b (hVh_le hb)
    obtain ⟨e, he, f, hf, hef⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommAB hxW
    have hfP : f ∈ Pc M V := by
      have heq : e⁻¹ * x = f := by rw [← hef]; group
      rw [← heq]
      exact (Pc M V).mul_mem ((Pc M V).inv_mem he.1) hx.1
    have hfbot : f = 1 := by
      have hmem : f ∈ conjSubgroup h₀ V ⊓ Pc M V := Subgroup.mem_inf.mpr ⟨hf, hfP⟩
      rw [conjSubgroup_inf_Pc_eq_bot h hH hnM] at hmem
      exact Subgroup.mem_bot.mp hmem
    rw [← hef, hfbot, mul_one]
    exact he
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.mem_sup_left hx.2⟩

theorem inf_Pc_xOf_eq_sup_inf_W0
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    (hW0le : W₀ ≤ (Pc M V ⊓ W₀) ⊔ conjSubgroup h₀ V) :
    Pc M V ⊓ Tim79a.xOf V H = V ⊔ (Pc M V ⊓ W₀) := by
  have hWsup : Tim79a.xOf V H = W₀ ⊔ V ⊔ conjSubgroup h₀ V :=
    eq_sup_sup_conj_of_isNatSumModule h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne ψ hl horth
  have habel := isElemAbelian_xOf h hPH hVH
  have hcommW : ∀ a ∈ Tim79a.xOf V H, ∀ b ∈ Tim79a.xOf V H, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (habel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hVh_le : conjSubgroup h₀ V ≤ Tim79a.xOf V H := by
    rw [hVy]
    exact conjSubgroup_le_xOf_of_mem (V := V) (H := H) hyH
  have hPW0 : Pc M V ⊓ (W₀ ⊔ conjSubgroup h₀ V) = Pc M V ⊓ W₀ :=
    inf_Pc_sup_conj_eq_inf (hW := hW) h hH hnM (hW₀ := hW₀) (hW0le := hW0le)
      (hyH := hyH) (hVy := hVy)
  have hW' : W₀ ⊔ V ⊔ conjSubgroup h₀ V = V ⊔ (W₀ ⊔ conjSubgroup h₀ V) := by
    rw [sup_assoc, sup_comm W₀ (V ⊔ conjSubgroup h₀ V), sup_assoc,
      sup_comm (conjSubgroup h₀ V) W₀]
  rw [hWsup, hW']
  refine le_antisymm ?_ ?_
  · intro p hp
    have hcommVB : ∀ a ∈ V, ∀ b ∈ W₀ ⊔ conjSubgroup h₀ V, a * b = b * a := by
      intro a ha b hb
      exact hcommW a (le_xOf_self V H ha) b ((sup_le hW₀ hVh_le) hb)
    obtain ⟨v, hv, x, hx, hvx⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommVB hp.2
    have hxP : x ∈ Pc M V := by
      have heq : v⁻¹ * p = x := by rw [← hvx]; group
      rw [← heq]
      exact (Pc M V).mul_mem ((Pc M V).inv_mem (h.toHyp.le_Pc hv)) hp.1
    have hxPW0 : x ∈ Pc M V ⊓ W₀ := by
      rw [← hPW0]
      exact Subgroup.mem_inf.mpr ⟨hxP, hx⟩
    rw [← hvx]
    exact Subgroup.mul_mem_sup hv hxPW0
  · have h1 : V ≤ Pc M V ⊓ (V ⊔ (W₀ ⊔ conjSubgroup h₀ V)) :=
      le_inf h.toHyp.le_Pc (le_sup_left : V ≤ V ⊔ (W₀ ⊔ conjSubgroup h₀ V))
    have h2 : Pc M V ⊓ W₀ ≤ Pc M V ⊓ (V ⊔ (W₀ ⊔ conjSubgroup h₀ V)) :=
      le_inf inf_le_left ((inf_le_right : Pc M V ⊓ W₀ ≤ W₀).trans
        ((le_sup_left : W₀ ≤ W₀ ⊔ conjSubgroup h₀ V).trans
          (le_sup_right : W₀ ⊔ conjSubgroup h₀ V ≤ V ⊔ (W₀ ⊔ conjSubgroup h₀ V))))
    exact sup_le h1 h2

theorem eq_xOf_and_card_of_isOrthModule
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    (hW0le : W₀ ≤ (Pc M V ⊓ W₀) ⊔ conjSubgroup h₀ V)
    (hPW₀ : Pc M V ⊓ W₀ = ⁅W₀, Pc M V⁆)
    (hcard : Nat.card ↥(V ⊓ W₀) = 2 ^ l) :
    W₀ = Tim79a.xOf V H ∧ Nat.card V = 2 ^ l ∧
      Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
        (Tim79a.H_le_normalizer_xOf V H)) := by
  have hstar : Pc M V ⊓ Tim79a.xOf V H ≤ V ⊔ (Pc M V ⊓ W₀) := by
    rw [inf_Pc_xOf_eq_sup_inf_W0 h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne ψ hl horth hW0le]
  have hVW0 : V ≤ W₀ :=
    le_of_isOrthModule h hPH hVH hH hnM ψ hl hW₀ hN horth (le_of_eq hPW₀) hstar
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hVhW0 : conjSubgroup h₀ V ≤ W₀ := by
    rw [hVy]
    calc conjSubgroup y V ≤ conjSubgroup y W₀ := Subgroup.map_mono hVW0
      _ = W₀ := conjSubgroup_eq_self_iff.mpr (hN hyH)
  have hWsup : Tim79a.xOf V H = W₀ ⊔ V ⊔ conjSubgroup h₀ V :=
    eq_sup_sup_conj_of_isNatSumModule h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne ψ hl horth
  have hW0W : W₀ = Tim79a.xOf V H := by
    rw [hWsup]
    exact le_antisymm (le_sup_of_le_left (le_sup_of_le_left le_rfl))
      (sup_le (sup_le le_rfl hVW0) hVhW0)
  have hcardV : Nat.card V = 2 ^ l := by
    rw [← inf_eq_left.mpr hVW0]
    exact hcard
  refine ⟨hW0W, hcardV, ?_⟩
  subst hW0W
  have hsub : subRepW hW ψ hW₀ hN = subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H) := by
    unfold subRepW
    rw [Subsingleton.elim hW₀ (le_refl (Tim79a.xOf V H)),
      Subsingleton.elim hN (Tim79a.H_le_normalizer_xOf V H)]
  rwa [hsub] at horth

theorem exists_orth_and_card_of_nonabelian
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2)
      (ψ : HBar V H ≃* SL(2, F)) (l : ℕ) (_ : 1 ≤ l)
      (hl : Fintype.card F = 2 ^ (2 * l)),
      Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
        (Tim79a.H_le_normalizer_xOf V H)) ∧ Nat.card V = 2 ^ l ∧
        Tim79a.xOf V H ≤ ⁅kOf V H, kOf V H⁆ := by
  obtain ⟨W₀, hW₀K', hW₀ne, hN, hmin⟩ :=
    exists_minimal_normalized_le_inf_commutator h hPH hK hnab
  have hW₀ : W₀ ≤ Tim79a.xOf V H := hW₀K'.trans inf_le_left
  have hW₀K'' : W₀ ≤ ⁅kOf V H, kOf V H⁆ := hW₀K'.trans inf_le_right
  obtain ⟨F, hField, hFint, hCharP, -, ⟨ψ⟩⟩ :=
    exists_sl2_of_nonabelian h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne hmin
  letI := hField
  letI := hFint
  letI := hCharP
  have hW0le : W₀ ≤ (Pc M V ⊓ W₀) ⊔ conjSubgroup h₀ V := by
    have h1 := eq_sup_inf_of_minimal (h := h) (hPH := hPH) (hVH := hVH) (hH := hH)
      (hnM := hnM) (hW₀ := hW₀) (hN := hN) (hW₀ne := hW₀ne) (hmin := hmin)
    have h2 := inf_conj_Pc_W0_eq_sup (h := h) (hPH := hPH) (hVH := hVH) (hH := hH)
      (hnM := hnM) (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN)
      (hW₀ne := hW₀ne) (hW₀K' := hW₀K'') (ψ := ψ)
    conv_lhs => rw [h1, h2]
    exact sup_le (le_sup_left : Pc M V ⊓ W₀ ≤ (Pc M V ⊓ W₀) ⊔ conjSubgroup h₀ V)
      (sup_le ((le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ ≤ Pc M V ⊓ W₀).trans
        (le_sup_left : Pc M V ⊓ W₀ ≤ (Pc M V ⊓ W₀) ⊔ conjSubgroup h₀ V))
        ((inf_le_left : conjSubgroup h₀ V ⊓ W₀ ≤ conjSubgroup h₀ V).trans
          (le_sup_right : conjSubgroup h₀ V ≤ (Pc M V ⊓ W₀) ⊔ conjSubgroup h₀ V)))
  have hPW₀ : Pc M V ⊓ W₀ = (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) :=
    inf_Pc_W0_eq_sup (hW := hW) (h := h) (hPH := hPH) (hVH := hVH) (hH := hH)
      (hnM := hnM) (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN)
      (hW₀ne := hW₀ne) (hW₀K' := hW₀K'') (ψ := ψ)
  have hcardW₀ : Nat.card W₀ = Nat.card ↥(V ⊓ W₀) ^ 2 *
      Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) :=
    card_eq_of_nonabelian (hW := hW) (h := h) (hPH := hPH) (hVH := hVH) (hH := hH) (hnM := hnM)
      (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN) (hW₀ne := hW₀ne)
      (hW₀K' := hW₀K'') (hmin := hmin) (ψ := ψ)
  obtain ⟨l, hl1, hl, horth₀, hcardA, hPW⟩ :=
    exists_orth_of_kOf_nonabelian (hW := hW) (h := h) (hPH := hPH) (hVH := hVH)
      (hH := hH) (hnM := hnM) (hK := hK) (hnab := hnab) (hL := hL) (ψ := ψ)
      (hW₀ := hW₀) (hN := hN) (hW₀ne := hW₀ne) (hmin := hmin) (hPW₀ := hPW₀)
      (hcardW₀ := hcardW₀)
  obtain ⟨hW0W, hcardV, horth⟩ :=
    eq_xOf_and_card_of_isOrthModule (hW := hW) (W₀ := W₀) (h := h) (hPH := hPH) (hVH := hVH)
      (hH := hH) (hnM := hnM) (hK := hK) (hnab := hnab) (hL := hL) (hW₀ := hW₀) (hN := hN)
      (hW₀ne := hW₀ne) (ψ := ψ) (hl := hl) (horth := horth₀) (hW0le := hW0le)
      (hPW₀ := hPW) (hcard := hcardA)
  exact ⟨F, hField, hFint, hCharP, ψ, l, hl1, hl, horth, hcardV, hW0W ▸ hW₀K''⟩

end RootHyp

end CFSG.RankThree.GF2n.Tim81
