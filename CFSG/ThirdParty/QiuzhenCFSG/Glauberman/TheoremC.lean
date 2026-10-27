module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremA
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma5_2
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma7_1
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma7_2
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_2
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem7_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman Theorem C (corrected statement)

This module proves the corrected form of Glauberman's Theorem C
([6], §7; `refs/glauberman-p-stable.tex` L1925–L1961).  The printed theorem
quantifies over every *non-empty* subset `W` of `S`; for `W = {1}` the conclusion
would force `G = O_{p'}(G)N_G(Z(J(S)))`, which is false in general (e.g.
`A₅`, `p = 3`).  The theorem proved here therefore replaces `W.Nonempty` with the
stronger witness `∃ w ∈ W, w ≠ 1`.  The source `refs/glauberman-p-stable.tex` is
left unchanged; this is a recorded fidelity drift, not an edit to the refs.

The route proved here is the paper's route:

1. From `pStable p G` and `pConstrained p G`, every `M ∈ M_p(G)` satisfies
   condition `(F_p)` (`satisfiesFp_of_pStable_pConstrained`): Lemma 7.2 makes
   `M/O_{p'}(M)` p-stable, `pConstrainedLocal` + Lemma 5.2 give the
   `C(O_p(-)) ⊆ O_p(-)` hypothesis for Theorem A, and the Frattini argument
   with `Z(J(T))` a Sylow subgroup of `O_{p'}(M)Z(J(T))` gives
   `M = O_{p'}(M)N_M(Z(J(T)))`.
2. Lemma 7.1 turns `(F_p)` into `(C_p*)`, hence `(C_p)`, on every `M ∈ M_p(G)`;
   Theorem 5.1(b) then gives `(C_p)` for `G` (`satisfiesCp_of_pStable_pConstrained`).
3. Theorem 7.1 gives `N(W) = O_{p'}(N(W))·(N(W) ∩ N(Z(J(S))))` for every
   non-identity subgroup `W ≤ S`; applying Lemma 7.1 inside `N(W)` to an
   element `c ∈ C(W)` yields `d ∈ O_{p'}(N(W)) ∩ C(W)` and
   `m ∈ N(W) ∩ N(Z(J(S)))`, with `c = d·m`.  Finally
   `O_{p'}(N(W)) ∩ C(W) ⊆ O_{p'}(C(W))`
   (`pPrimeCore_le_of_mem_normalizer_centralizer`) and
   `C(⟨V⟩) = C(V)` (`Subgroup.centralizer_closure`) finish the theorem.

**Known gap in the printed statement.**  The paper says "non-empty subset `W`",
and the pinned wrapper statement has `W.Nonempty`.  For `W = {1}` the conclusion
reduces to `G = O_{p'}(G)N_G(Z(J(S)))`, which is not implied by the hypotheses:
`A₅` with `p = 3` is p-stable and p-constrained (its `M_p`-elements are `C₃` and
`S₃`), but for a Sylow `3`-subgroup `S` one has `N_G(Z(J(S)))` of order `12`,
not `60`.  This exact gap is documented in `/tmp/glauberman-c-report.md`; the
proof below is complete for the nontrivial case `Subgroup.closure W ≠ ⊥`.
-/

open scoped Pointwise
namespace CFSG.Glauberman
set_option maxHeartbeats 800000

set_option backward.isDefEq.respectTransparency false in
private theorem Op_p'p_map_iso {G G' : Type*} [Group G] [Group G'] (p : ℕ)
    (e : G ≃* G') :
    (Op_p'p p G).map e.toMonoidHom = Op_p'p p G' := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let M' : Subgroup G' := pPrimeCore p G'
  have hMmap : M.map e.toMonoidHom = M' := pPrimeCore_map_iso p e
  let ebar : G ⧸ M ≃* G' ⧸ M' := QuotientGroup.congr M M' e hMmap
  have hcoremap : (pCore p (G ⧸ M)).map ebar.toMonoidHom = pCore p (G' ⧸ M') := pCore_map_iso p ebar
  have hcomm (y : G) : ebar (QuotientGroup.mk' M y) = QuotientGroup.mk' M' (e y) := by
    dsimp [ebar]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    dsimp [Op_p'p]
    rw [Subgroup.mem_comap]
    rw [← hcoremap]
    exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' M y, by simpa [Op_p'p] using hy, hcomm y⟩
  · intro hx
    have hy : e.symm x ∈ Op_p'p p G := by
      dsimp [Op_p'p]
      rw [Subgroup.mem_comap]
      have hback : QuotientGroup.mk' M (e.symm x) ∈ pCore p (G ⧸ M) := by
        have hcomm' : ebar (QuotientGroup.mk' M (e.symm x)) = QuotientGroup.mk' M' x := by
          dsimp [ebar]
          congr 1
          simp
        have hmem : ebar (QuotientGroup.mk' M (e.symm x)) ∈ pCore p (G' ⧸ M') := by
          rw [hcomm']
          simpa [Op_p'p] using hx
        rw [← hcoremap] at hmem
        rcases Subgroup.mem_map.mp hmem with ⟨z, hz, hz_eq⟩
        have hz' : z = QuotientGroup.mk' M (e.symm x) := ebar.injective hz_eq
        simpa [hz'] using hz
      exact hback
    refine ⟨e.symm x, hy, by simp⟩

private theorem pConstrainedLocal_congr {G G' : Type*} [Group G] [Group G']
    [Finite G] [Finite G'] (p : ℕ) [Fact p.Prime] (e : G ≃* G')
    (h : pConstrainedLocal p G) :
    pConstrainedLocal p G' := by
  classical
  let O : Subgroup G := Op_p'p p G
  let O' : Subgroup G' := Op_p'p p G'
  have hOmap : O.map e.toMonoidHom = O' := Op_p'p_map_iso p e
  let eO : ↥O ≃* ↥O' :=
    { toFun := fun y => ⟨e y.1, by
        have hmem : e y.1 ∈ O.map e.toMonoidHom :=
          Subgroup.mem_map_of_mem e.toMonoidHom y.2
        rwa [hOmap] at hmem⟩
      invFun := fun z => ⟨e.symm z.1, by
        have hcomap : O'.comap e.toMonoidHom = O := by
          apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
          rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective O']
          exact hOmap.symm
        have hm : e.symm z.1 ∈ O'.comap e.toMonoidHom := by
          change e (e.symm z.1) ∈ O'
          simp
        rwa [hcomap] at hm⟩
      left_inv := fun y => by
        apply Subtype.ext
        simp
      right_inv := fun z => by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        change e (a.1 * b.1) = e a.1 * e b.1
        exact e.map_mul a.1 b.1 }
  intro T'
  let T : Sylow p (↥O) := T'.mapSurjective (f := eO.symm.toMonoidHom) eO.symm.surjective
  have hTmap : (T : Subgroup ↥O).map eO.toMonoidHom = (T' : Subgroup ↥O') := by
    change ((T' : Subgroup ↥O').map eO.symm.toMonoidHom).map eO.toMonoidHom =
      (T' : Subgroup ↥O')
    rw [Subgroup.map_map]
    simp
  have hcent : Subgroup.centralizer ((T.map O.subtype : Subgroup G) : Set G) ≤ O :=
    h T
  have hcentG : Subgroup.centralizer (((T.map O.subtype).map e.toMonoidHom : Subgroup G') : Set G') ≤ O' := by
    have hmap := map_centralizer_eq_of_equiv (e := e) (P := T.map O.subtype)
    rw [← hmap]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨c, hc, rfl⟩
    have hmem : e c ∈ O.map e.toMonoidHom := by
      rw [Subgroup.mem_map]
      exact ⟨c, hcent hc, rfl⟩
    rw [hOmap] at hmem
    exact hmem
  have hsub : (T.map O.subtype).map e.toMonoidHom = T'.map O'.subtype := by
    calc
      (T.map O.subtype).map e.toMonoidHom = (T : Subgroup ↥O).map (e.toMonoidHom.comp O.subtype) := by
        rw [Subgroup.map_map]
      _ = (T : Subgroup ↥O).map (O'.subtype.comp eO.toMonoidHom) := by
        congr 1
      _ = ((T : Subgroup ↥O).map eO.toMonoidHom).map O'.subtype := by
        rw [Subgroup.map_map]
      _ = T'.map O'.subtype := by rw [hTmap]
  rw [hsub] at hcentG
  exact hcentG

private theorem pConstrainedLocal_of_core_ne_bot {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hconst : pConstrained p G) (hOp : pCore p G ≠ ⊥) :
    pConstrainedLocal p G := by
  classical
  let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  have htop : pConstrainedLocal p (↥(⊤ : Subgroup G)) :=
    hconst (⊤ : Subgroup G) (mem_MpSet_top (G := G) p hOp)
  exact pConstrainedLocal_congr (G := ↥(⊤ : Subgroup G)) (G' := G) p e htop

private theorem satisfiesFpExplicit_of_pStable_pConstrained {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] (hpodd : p ≠ 2)
    (hstab : pStable p G) (hconst : pConstrained p G) (hOp : pCore p G ≠ ⊥) :
    ∀ S : Sylow p G,
      pPrimeCore p G ⊔ Subgroup.normalizer
        (((zjCharacteristicFunctor p).K (S : Subgroup G) : Subgroup G) : Set G) = ⊤ := by
  classical
  intro S
  let M : Subgroup G := pPrimeCore p G
  let Gbar : Type _ := G ⧸ M
  let q : G →* Gbar := QuotientGroup.mk' M
  let Sbar : Sylow p Gbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective M)
  have hstabQuot : pStable p Gbar := lemma7_2 (G := G) p hpodd hstab hOp
  let O : Subgroup G := Op_p'p p G
  have hCS : (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ O) : Set G) ≤
      (S : Subgroup G) ⊓ O := by
    obtain ⟨P, hPmap⟩ := sylow_inf_normal (G := G) S (N := O)
    have hcentO : Subgroup.centralizer (((S : Subgroup G) ⊓ O) : Set G) ≤ O := by
      have hconstLocal : pConstrainedLocal p G :=
        pConstrainedLocal_of_core_ne_bot p hconst hOp
      have hc := hconstLocal P
      have hPmap' : (P : Subgroup ↥O).map O.subtype = (S : Subgroup G) ⊓ O := by
        rw [hPmap]
        rw [Subgroup.subgroupOf_map_subtype]
        rw [inf_eq_left.mpr (inf_le_right : (S : Subgroup G) ⊓ O ≤ O)]
      change Subgroup.centralizer ((P.map O.subtype : Subgroup G) : Set G) ≤ O at hc
      have hc' : Subgroup.centralizer (((S : Subgroup G) ⊓ O) : Set G) ≤ O := by
        simpa [hPmap'] using hc
      exact hc'
    intro x hx
    exact ⟨(Subgroup.mem_inf.mp hx).1, hcentO (Subgroup.mem_inf.mp hx).2⟩
  have hcentralQuot :
      Subgroup.centralizer ((pCore p Gbar : Subgroup Gbar) : Set Gbar) ≤ pCore p Gbar :=
    lemma5_2 p S hCS
  have hZbar_normal : (ZJ (G := Gbar) (Sbar : Subgroup Gbar)).Normal := by
    have hchar : (ZJ (G := Gbar) (Sbar : Subgroup Gbar)).Characteristic :=
      TheoremA.theoremA hpodd (G := Gbar) Sbar hstabQuot hcentralQuot
    exact (inferInstance : (ZJ (G := Gbar) (Sbar : Subgroup Gbar)).Normal)
  let Z : Subgroup G := (zjCharacteristicFunctor p).K (S : Subgroup G)
  have hq_inj : Function.Injective (q.comp (S : Subgroup G).subtype) :=
    quotient_pPrimeCore_subgroupMap_injective (G := G) (H := (S : Subgroup G)) S.isPGroup'
  have hZbar_map : (ZJ (G := Gbar) (Sbar : Subgroup Gbar) : Subgroup Gbar) = Z.map q := by
    change (zjCharacteristicFunctor p).K ((S : Subgroup G).map q) = Z.map q
    exact K_commutes_of_injective_on (zjCharacteristicFunctor p) q (S : Subgroup G) hq_inj
  let L : Subgroup G := M ⊔ Z
  have hL_comap : L = Subgroup.comap q (Z.map q) := by
    dsimp [L]
    exact (QuotientGroup.comap_map_mk' M Z).symm
  have hL_normal : L.Normal := by
    rw [hL_comap]
    have hZbar_comap : (Subgroup.comap q (Z.map q)).Normal := by
      rw [← hZbar_map]
      exact Subgroup.Normal.comap hZbar_normal q
    exact hZbar_comap
  have : L.Normal := hL_normal
  have hZ_le_S : Z ≤ (S : Subgroup G) := (zjCharacteristicFunctor p).K_le (S : Subgroup G)
  have hS_M_disjoint : Disjoint (S : Subgroup G) M := by
    apply Subgroup.disjoint_of_coprime_natCard
    rcases S.isPGroup'.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
  have hS_inf_M : (S : Subgroup G) ⊓ M = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hx1 : x = 1 := (Subgroup.disjoint_def.mp hS_M_disjoint) hx.1 hx.2
      simpa using hx1
    · exact bot_le
  have hS_inf_L : (S : Subgroup G) ⊓ L = Z := by
    apply le_antisymm
    · intro x hx
      have hxS : x ∈ (S : Subgroup G) := hx.1
      have hxL : x ∈ L := hx.2
      rcases (Subgroup.mem_sup_of_normal_left (s := M) (t := Z) (x := x)).1 hxL with
        ⟨m, hmM, z, hzZ, hmz⟩
      have hzS : z ∈ (S : Subgroup G) := hZ_le_S hzZ
      have hmS : m ∈ (S : Subgroup G) := by
        have hxz : x * z⁻¹ = m := by
          calc
            x * z⁻¹ = (m * z) * z⁻¹ := by rw [← hmz]
            _ = m := by group
        rw [← hxz]
        exact (S : Subgroup G).mul_mem hxS ((S : Subgroup G).inv_mem hzS)
      have hm1 : m = 1 := by
        have hminf : m ∈ (S : Subgroup G) ⊓ M := ⟨hmS, hmM⟩
        rw [hS_inf_M] at hminf
        exact Subgroup.mem_bot.mp hminf
      rw [hm1, one_mul] at hmz
      simpa [hmz] using hzZ
    · intro x hxZ
      exact ⟨hZ_le_S hxZ, Subgroup.mem_sup_right (S := M) (T := Z) hxZ⟩
  obtain ⟨P, hPmapL⟩ := sylow_inf_normal (G := G) S (N := L)
  have hPmapZ : (P : Subgroup ↥L).map L.subtype = Z := by
    rw [hPmapL]
    rw [Subgroup.subgroupOf_map_subtype]
    rw [inf_eq_left.mpr (inf_le_right : (S : Subgroup G) ⊓ L ≤ L)]
    exact hS_inf_L
  have hfr := Sylow.normalizer_sup_eq_top (N := L) P
  have hfr' : Subgroup.normalizer (Z : Set G) ⊔ L = ⊤ := by
    simpa [hPmapZ] using hfr
  have hZ_le_NZ : Z ≤ Subgroup.normalizer (Z : Set G) := Subgroup.le_normalizer
  have hL_le_MNZ : L ≤ M ⊔ Subgroup.normalizer (Z : Set G) := by
    calc
      L = M ⊔ Z := rfl
      _ ≤ M ⊔ Subgroup.normalizer (Z : Set G) := sup_le_sup_left (c := M) hZ_le_NZ
  have heqNZ : Subgroup.normalizer (Z : Set G) ⊔ L =
      M ⊔ Subgroup.normalizer (Z : Set G) := by
    dsimp [L]
    calc
      Subgroup.normalizer (Z : Set G) ⊔ (M ⊔ Z)
          = (Subgroup.normalizer (Z : Set G) ⊔ M) ⊔ Z := by rw [sup_assoc]
      _ = (M ⊔ Subgroup.normalizer (Z : Set G)) ⊔ Z := by
            rw [sup_comm (a := Subgroup.normalizer (Z : Set G)) (b := M)]
      _ = M ⊔ (Subgroup.normalizer (Z : Set G) ⊔ Z) := by rw [sup_assoc]
      _ = M ⊔ Subgroup.normalizer (Z : Set G) := by
            rw [sup_eq_left.2 hZ_le_NZ]
  have hgoal : M ⊔ Subgroup.normalizer (Z : Set G) = ⊤ := by
    apply le_antisymm
    · exact le_top
    · rw [← heqNZ, ← hfr']
  simpa [Z] using hgoal

private theorem satisfiesFp_of_pStable_pConstrained {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] (hpodd : p ≠ 2)
    (hstab : pStable p G) (hconst : pConstrained p G) (hOp : pCore p G ≠ ⊥) :
    SatisfiesFp p (zjCharacteristicFunctor p) G := by
  change ∀ S : Sylow p G,
    pPrimeCore p G ⊔ Subgroup.normalizer
      (((zjCharacteristicFunctor p).K (S : Subgroup G) : Subgroup G) : Set G) = ⊤
  exact satisfiesFpExplicit_of_pStable_pConstrained hpodd hstab hconst hOp


private theorem pStable_of_core_ne_bot {G : Type*} [Group G] (p : ℕ) [Fact p.Prime]
    (h : pStableLocal p G) (hOp : pCore p G ≠ ⊥) : pStable p G := by
  classical
  intro M hM
  have htop : M = ⊤ := MpSet_eq_top_of_core_ne_bot (G := G) p hOp M hM
  let e : ↥M ≃* ↥(⊤ : Subgroup G) :=
    { toEquiv := Equiv.subtypeEquivRight (fun y : G => by rw [htop])
      map_mul' := by intro a b; rfl }
  have hTop : pStableLocal p (↥(⊤ : Subgroup G)) :=
    (pStableLocal_congr (p := p) (e := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G))).2 h
  exact (pStableLocal_congr (p := p) (e := e)).2 hTop

private theorem pConstrained_of_core_ne_bot {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (h : pConstrainedLocal p G) (hOp : pCore p G ≠ ⊥) :
    pConstrained p G := by
  classical
  intro M hM
  have htop : M = ⊤ := MpSet_eq_top_of_core_ne_bot (G := G) p hOp M hM
  let e : ↥M ≃* ↥(⊤ : Subgroup G) :=
    { toEquiv := Equiv.subtypeEquivRight (fun y : G => by rw [htop])
      map_mul' := by intro a b; rfl }
  have hTop : pConstrainedLocal p (↥(⊤ : Subgroup G)) :=
    pConstrainedLocal_congr (G := G) (G' := ↥(⊤ : Subgroup G)) p
      (Subgroup.topEquiv.symm : G ≃* ↥(⊤ : Subgroup G)) h
  exact pConstrainedLocal_congr (G := ↥(⊤ : Subgroup G)) (G' := ↥M) p e.symm hTop

private theorem cpStar_of_satisfiesFpExplicit {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (K : CharacteristicFunctor p) (S : Sylow p G)
    (hF : ∀ T : Sylow p G,
      pPrimeCore p G ⊔ Subgroup.normalizer
        ((K.K (T : Subgroup G) : Subgroup G) : Set G) = ⊤) : CpStar K S := by
  intro W hWp hWleN g hWg
  let H : Subgroup G := Subgroup.normalizer ((K.K (S : Subgroup G) : Subgroup G) : Set G)
  have hGH : pPrimeCore p G ⊔ H = ⊤ := hF S
  let WH : Subgroup H := W.subgroupOf H
  have hWHp : IsPGroup p WH :=
    IsPGroup.of_equiv (hG := hWp) (Subgroup.subgroupOfEquivOfLe hWleN).symm
  have hghyp : ∀ w : WH, g⁻¹ * (w : G) * g ∈ H := by
    intro w
    have hwW : (w : G) ∈ W := (Subgroup.mem_subgroupOf).1 w.2
    have hwconj : g⁻¹ * (w : G) * g ∈ conjSubgroup g W :=
      Subgroup.mem_map.mpr ⟨(w : G), hwW, by simp⟩
    exact hWg hwconj
  rcases lemma7_1 (G := G) H hGH WH hWHp (g := g) hghyp with ⟨c, hcCore, hcCent, h, hhH, hgh⟩
  refine ⟨c, h, ?_, hhH, hgh⟩
  have hmap : WH.map H.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWleN
  simpa [hmap] using hcCent

private theorem cp_of_satisfiesFpExplicit {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (K : CharacteristicFunctor p) (S : Sylow p G)
    (hF : ∀ T : Sylow p G,
      pPrimeCore p G ⊔ Subgroup.normalizer
        ((K.K (T : Subgroup G) : Subgroup G) : Set G) = ⊤) : Cp K S :=
  cp_of_cpStar K S (cpStar_of_satisfiesFpExplicit K S hF)

private theorem satisfiesCp_of_pStable_pConstrained {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] (hpodd : p ≠ 2)
    (hstab : pStable p G) (hconst : pConstrained p G) :
    SatisfiesCp (zjCharacteristicFunctor p) G := by
  intro S
  apply theorem5_1 S
  right
  intro M hM
  have hstabM : pStable p ↥M := pStable_of_core_ne_bot (p := p) (hstab M hM) hM.1
  have hconstM : pConstrained p ↥M := pConstrained_of_core_ne_bot (p := p) (hconst M hM) hM.1
  intro T
  exact cp_of_satisfiesFpExplicit (G := ↥M) (zjCharacteristicFunctor p) T
    (satisfiesFpExplicit_of_pStable_pConstrained (G := ↥M) hpodd hstabM hconstM hM.1)



private theorem pPrimeCore_le_of_mem_normalizer_centralizer {G : Type*} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] (W : Subgroup G) {d : G}
    (hdC : d ∈ Subgroup.centralizer (W : Set G))
    (hdN : d ∈ (pPrimeCore p ↥(Subgroup.normalizer (W : Set G))).map
      (Subgroup.normalizer (W : Set G)).subtype) :
    d ∈ (pPrimeCore p ↥(Subgroup.centralizer (W : Set G))).map
      (Subgroup.centralizer (W : Set G)).subtype := by
  classical
  let N : Subgroup G := Subgroup.normalizer (W : Set G)
  let C : Subgroup G := Subgroup.centralizer (W : Set G)
  have hC_le_N : C ≤ N := Subgroup.centralizer_le_normalizer (W : Set G)
  let P : Subgroup ↥N := pPrimeCore p ↥N
  let incl : ↥C →* ↥N := Subgroup.inclusion hC_le_N
  have hPC_normal : (P.comap incl).Normal :=
    Subgroup.Normal.comap (pPrimeCore_normal (G := ↥N)) incl
  have hPC_p' : Nat.Coprime p (Nat.card ↥(P.comap incl)) := by
    have hmap_le : (P.comap incl).map incl ≤ P := Subgroup.map_comap_le (f := incl) (H := P)
    have hcard_dvd : Nat.card ((P.comap incl).map incl) ∣ Nat.card ↥P :=
      Subgroup.card_dvd_of_le hmap_le
    have hcard_eq : Nat.card ↥(P.comap incl) =
        Nat.card ((P.comap incl).map incl) :=
      (Subgroup.card_map_of_injective (K := P.comap incl) (f := incl)
        (Subgroup.inclusion_injective hC_le_N)).symm
    have hcard_dvd' : Nat.card ↥(P.comap incl) ∣ Nat.card ↥P := by
      rw [hcard_eq]
      exact hcard_dvd
    exact Nat.Coprime.of_dvd_right hcard_dvd' (pPrimeCore_coprime_card (G := ↥N) (p := p))
  have hPC_le_core : P.comap incl ≤ pPrimeCore p ↥C := le_sSup ⟨hPC_normal, hPC_p'⟩
  rcases Subgroup.mem_map.mp hdN with ⟨d0, hd0P, hd0_eq⟩
  have hd0C : (d0 : G) ∈ C := by
    rwa [← hd0_eq] at hdC
  let c0 : ↥C := ⟨d0.1, hd0C⟩
  have hc0 : c0 ∈ P.comap incl := by
    rw [Subgroup.mem_comap]
    have hincl : incl c0 = d0 := by
      apply Subtype.ext
      rfl
    rwa [hincl]
  have hdCoreC : c0 ∈ pPrimeCore p ↥C := hPC_le_core hc0
  refine Subgroup.mem_map.mpr ⟨c0, hdCoreC, ?_⟩
  simpa [c0] using hd0_eq

private theorem theoremC_of_nontrivial {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] (hpodd : p ≠ 2) (S : Sylow p G)
    (hstab : pStable p G) (hconst : pConstrained p G) :
    ∀ W : Set G, W.Nonempty → W ⊆ (S : Subgroup G) →
      Subgroup.closure W ≠ ⊥ →
      ∀ g : G, conjSubset g W ⊆ (S : Subgroup G) →
        ∃ c n : G,
          c ∈ (pPrimeCore p (↥(Subgroup.centralizer W))).map (Subgroup.centralizer W).subtype ∧
            n ∈ Subgroup.normalizer ((ZJ (G := G) S.toSubgroup : Subgroup G) : Set G) ∧
              g = c * n := by
  classical
  intro V hVne hVleS hXne g hVg
  let K := zjCharacteristicFunctor p
  let X : Subgroup G := Subgroup.closure V
  have hWleS : X ≤ (S : Subgroup G) := (Subgroup.closure_le (K := (S : Subgroup G))).mpr hVleS
  have hWp : IsPGroup p X := IsPGroup.to_le S.isPGroup' hWleS
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let NK : Subgroup G := Subgroup.normalizer ((K.K (S : Subgroup G) : Subgroup G) : Set G)
  have hS_le_NK : (S : Subgroup G) ≤ NK := sylow_le_normalizer_K K S
  have hWN : X ≤ N := Subgroup.le_normalizer (H := X)
  have hW_le_NK : X ≤ NK := hWleS.trans hS_le_NK
  have hW_le_NinfNK : X ≤ N ⊓ NK := le_inf hWN hW_le_NK
  have hCp : SatisfiesCp K G := satisfiesCp_of_pStable_pConstrained hpodd hstab hconst
  have hFp : ∀ M : Subgroup G, M ∈ MpSet p G → SatisfiesFp p K ↥M := by
    intro M hM
    have hstabM : pStable p ↥M := pStable_of_core_ne_bot (p := p) (hstab M hM) hM.1
    have hconstM : pConstrained p ↥M := pConstrained_of_core_ne_bot (p := p) (hconst M hM) hM.1
    exact satisfiesFp_of_pStable_pConstrained (G := ↥M) hpodd hstabM hconstM hM.1
  have hWg_sub : conjSubgroup g X ≤ (S : Subgroup G) := by
    rw [conjSubgroup, MonoidHom.map_closure]
    refine (Subgroup.closure_le (K := (S : Subgroup G))).mpr ?_
    intro x hx
    rcases hx with ⟨w, hwV, rfl⟩
    exact hVg ⟨w, hwV, by simp⟩
  have hWg_le_S : conjSubset g (X : Set G) ⊆ (S : Subgroup G) := by
    intro x hx
    exact hWg_sub (by simpa [conjSubset_eq_conjSubgroup] using hx)
  rcases (hCp S (X : Set G) ⟨1, X.one_mem⟩ hWleS g hWg_le_S) with ⟨c, n, hcC, hnNK, hcn⟩
  have hcN : c ∈ N := (Subgroup.centralizer_le_normalizer (X : Set G)) hcC
  have h7 := theorem7_1 p K S hCp hFp X hWleS hXne
  let L' : Subgroup ↥N := pPrimeCore p ↥N
  let H0 : Subgroup ↥N := (N ⊓ NK).subgroupOf N
  have h7N : L' ⊔ H0 = ⊤ := by
    apply Subgroup.map_injective (f := N.subtype) N.subtype_injective
    calc
      (L' ⊔ H0).map N.subtype = L'.map N.subtype ⊔ H0.map N.subtype := Subgroup.map_sup L' H0 N.subtype
      _ = (pPrimeCore p ↥N).map N.subtype ⊔ (N ⊓ NK) := by
        dsimp [H0]
        rw [Subgroup.subgroupOf_map_subtype]
        rw [inf_eq_left.mpr (inf_le_left : N ⊓ NK ≤ N)]
      _ = N := by
        simpa [N, NK, L'] using h7.symm
      _ = (⊤ : Subgroup ↥N).map N.subtype := by
        ext x
        constructor
        · intro hx
          exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, trivial, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact y.property
  let WN : Subgroup ↥N := X.subgroupOf N
  have hWN_le_H0 : WN ≤ H0 := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hW_le_NinfNK hx
  let W0 : Subgroup H0 := WN.subgroupOf H0
  have eW0 : W0 ≃* X :=
    (Subgroup.subgroupOfEquivOfLe hWN_le_H0).trans (Subgroup.subgroupOfEquivOfLe hWN)
  have hW0p : IsPGroup p W0 := IsPGroup.of_equiv (hG := hWp) eW0.symm
  let cN : ↥N := ⟨c, hcN⟩
  have hghyp : ∀ w : W0, cN⁻¹ * (w : ↥N) * cN ∈ H0 := by
    intro w
    have hwW : (w : G) ∈ X := (Subgroup.mem_subgroupOf).1 ((Subgroup.mem_subgroupOf).1 w.2)
    have hcomm : (w : G) * c = c * (w : G) :=
      (Subgroup.mem_centralizer_iff.mp hcC) (w : G) hwW
    have heq : c⁻¹ * (w : G) * c = (w : G) := by
      calc
        c⁻¹ * (w : G) * c = c⁻¹ * ((w : G) * c) := by group
        _ = c⁻¹ * (c * (w : G)) := by rw [hcomm]
        _ = w := by group
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, ?_⟩
    · change c⁻¹ * (w : G) * c ∈ N
      exact N.mul_mem (N.mul_mem (N.inv_mem hcN) ((w : ↥N).2)) hcN
    · change c⁻¹ * (w : G) * c ∈ NK
      rw [heq]
      exact hW_le_NK hwW
  rcases lemma7_1 (G := ↥N) (H := H0) (hGH := h7N) (W := W0) (hWp := hW0p)
    (g := cN) hghyp with ⟨dN, hdCore, hdCent, mN, hmH0, hdm⟩
  let d : G := dN
  let m : G := mN
  have hdL : d ∈ (pPrimeCore p ↥N).map N.subtype :=
    Subgroup.mem_map.mpr ⟨dN, hdCore, rfl⟩
  have hdC : d ∈ Subgroup.centralizer (X : Set G) := by
    have hmap0 : W0.map H0.subtype = WN := Subgroup.map_subgroupOf_eq_of_le hWN_le_H0
    have hdCent' : dN ∈ Subgroup.centralizer ((WN : Set ↥N)) := by
      simpa [hmap0] using hdCent
    rw [Subgroup.mem_centralizer_iff]
    intro x hxW
    have hxWN : (⟨x, hWN hxW⟩ : ↥N) ∈ WN := (Subgroup.mem_subgroupOf).2 hxW
    have hcommN := (Subgroup.mem_centralizer_iff.mp hdCent') (⟨x, hWN hxW⟩) hxWN
    exact congrArg Subtype.val hcommN
  have hmNM : m ∈ N ⊓ NK := (Subgroup.mem_subgroupOf).1 hmH0
  have hmNK : m ∈ NK := (Subgroup.mem_inf.mp hmNM).2
  have hdc : c = d * m := congrArg Subtype.val hdm
  have hgdm : g = d * (m * n) := by
    calc
      g = c * n := hcn
      _ = (d * m) * n := by rw [hdc]
      _ = d * (m * n) := by group
  have hdCoreC : d ∈ (pPrimeCore p ↥(Subgroup.centralizer (X : Set G))).map
      (Subgroup.centralizer (X : Set G)).subtype :=
    pPrimeCore_le_of_mem_normalizer_centralizer (G := G) X hdC hdL
  have hC_eq : Subgroup.centralizer (X : Set G) = Subgroup.centralizer V := by
    dsimp [X]
    exact Subgroup.centralizer_closure V
  have hdCoreC' : d ∈ (pPrimeCore p ↥(Subgroup.centralizer
      ((Subgroup.closure V : Subgroup G) : Set G))).map
      (Subgroup.centralizer ((Subgroup.closure V : Subgroup G) : Set G)).subtype := by
    dsimp [X] at hdCoreC
    exact hdCoreC
  have hdCoreV : d ∈ (pPrimeCore p ↥(Subgroup.centralizer V)).map
      (Subgroup.centralizer V).subtype := by
    have hC_eq' : Subgroup.centralizer V =
        Subgroup.centralizer ((Subgroup.closure V : Subgroup G) : Set G) :=
      (Subgroup.centralizer_closure V).symm
    rw [hC_eq']
    exact hdCoreC'
  have hmnNK : m * n ∈ NK := NK.mul_mem hmNK hnNK
  refine ⟨d, m * n, hdCoreV, ?_, hgdm⟩
  · change m * n ∈ Subgroup.normalizer ((K.K (S : Subgroup G) : Subgroup G) : Set G)
    exact hmnNK

private lemma closure_ne_bot_of_exists_ne_one {G : Type*} [Group G] {W : Set G}
    (h : ∃ w : G, w ∈ W ∧ w ≠ 1) : Subgroup.closure W ≠ ⊥ := by
  intro hbot
  rcases h with ⟨w, hwW, hwne⟩
  have hw1 : w = 1 := (Subgroup.closure_eq_bot_iff.mp hbot) hwW
  exact hwne hw1

/-- Glauberman's Theorem C, corrected from the printed "non-empty" clause to an
explicit non-identity witness.  This is the wrapper statement with `W.Nonempty`
strengthened to `∃ w ∈ W, w ≠ 1`; the printed `W.Nonempty` version is false for
`W = {1}` (see the module docstring and `/tmp/glauberman-c-report.md`). -/
public theorem theoremC {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (S : Sylow p G) :
    pStable p G → pConstrained p G →
      ∀ W : Set G, (∃ w : G, w ∈ W ∧ w ≠ 1) → W ⊆ (S : Subgroup G) →
        ∀ g : G, conjSubset g W ⊆ (S : Subgroup G) →
          ∃ c n : G,
            c ∈ (pPrimeCore p (↥(Subgroup.centralizer W))).map (Subgroup.centralizer W).subtype ∧
              n ∈ Subgroup.normalizer ((ZJ (G := G) S.toSubgroup : Subgroup G) : Set G) ∧
                g = c * n := by
  classical
  intro hstab hconst W hWne hWleS g hVg
  rcases hWne with ⟨w, hwW, hwne⟩
  exact theoremC_of_nontrivial hpodd S hstab hconst W ⟨w, hwW⟩ hWleS
    (closure_ne_bot_of_exists_ne_one ⟨w, hwW, hwne⟩) g hVg

end CFSG.Glauberman
