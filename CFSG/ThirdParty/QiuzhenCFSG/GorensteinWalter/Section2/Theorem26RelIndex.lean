module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26Core
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2LowReflectedToriCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddSubgroupLeNormalIndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2LowOddCyclicCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise
open scoped commutatorElement
open scoped IsMulCommutative

namespace CFSG.GorensteinWalter

universe u

public theorem S_relIndex_E_eq_two_t26
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K) :
    d.E.relIndex (c.S : Subgroup G) = 2 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
  let : O.Normal := by
    dsimp [O]
    infer_instance
  let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
  let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
  have hend26 : (d.E.subgroupOf c.Hhat).Normal :=
    (d.pgl2_component_ambient_endpoint K hK L hLnormal hLindex e).1
  let : Ei.Normal := by
    simpa [Ei] using hend26
  let Ebar : Subgroup (c.Hhat ⧸ O) := Ei.map q
  let hSle : (c.S : Subgroup G) ≤ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 c.Hhat := c.S.subtype hSle
  let Pq : Sylow 2 (c.Hhat ⧸ O) :=
    P.mapSurjective (QuotientGroup.mk'_surjective O)
  have hPqL : (Pq : Subgroup (c.Hhat ⧸ O)) ≤ L :=
    sylow_le_of_normal_odd_index_local L hLnormal hLindex Pq
  let PL : Sylow 2 L := Pq.subtype hPqL
  let Pmodel : Sylow 2 (PGL2 K) :=
    PL.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨hcard, _hEbarne, _hEbarperf, _hEbarsn, hEbarL, hJeq⟩ :=
    d.pgl2_component_image_eq_commutator K hK L hLnormal hLindex e
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  have hJindex : J.index = 2 := by
    dsimp [J]
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    exact pgl2_psl2Range_index_eq_two K hK
  let : J.Normal := by
    dsimp [J]
    infer_instance
  -- `q` is injective on `P` (the kernel `P ∩ O` is trivial).
  have hqP : Function.Injective (q.comp (P : Subgroup c.Hhat).subtype) := by
    have hcop : Nat.Coprime (Nat.card (P : Subgroup c.Hhat))
        (Nat.card O) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
      rw [hn]
      exact (pPrimeCore_coprime_card (p := 2) (G := c.Hhat)).pow_left n
    have hdis : Disjoint (P : Subgroup c.Hhat) O :=
      Subgroup.disjoint_of_coprime_natCard hcop
    apply (MonoidHom.ker_eq_bot_iff (q.comp (P : Subgroup c.Hhat).subtype)).mp
    apply le_antisymm
    · intro x hx
      have hxO : (x : c.Hhat) ∈ O := by
        apply (QuotientGroup.eq_one_iff (N := O) (x : c.Hhat)).mp
        exact hx
      have hxone : (x : c.Hhat) = 1 :=
        Subgroup.disjoint_def.mp hdis x.2 hxO
      exact Subgroup.mem_bot.mpr (Subtype.ext hxone)
    · exact bot_le
  -- Model side: `|Pq : Pq ∩ Ebar| = 2`.
  let PqL : Subgroup L := (Pq : Subgroup (c.Hhat ⧸ O)).subgroupOf L
  let EbarL : Subgroup L := Ebar.subgroupOf L
  have hPqPmodel : PqL.map e.toMonoidHom =
      (Pmodel : Subgroup (PGL2 K)) := by
    rfl
  have hEbarJ : EbarL.map e.toMonoidHom = J := hJeq
  have hPqrel : Ebar.relIndex (Pq : Subgroup (c.Hhat ⧸ O)) = 2 := by
    have hPnot : ¬ (Pmodel : Subgroup (PGL2 K)) ≤ J := by
      intro hPJ
      have hrel := Subgroup.relIndex_mul_index hPJ
      rw [hJindex] at hrel
      have htwo : 2 ∣ (Pmodel : Subgroup (PGL2 K)).index := by
        refine ⟨(Pmodel : Subgroup (PGL2 K)).relIndex J, ?_⟩
        rw [mul_comm]
        exact hrel.symm
      exact Pmodel.not_dvd_index htwo
    have hPmodelJ : (Pmodel : Subgroup (PGL2 K)) ⊔ J = ⊤ := by
      have hle : J ≤ (Pmodel : Subgroup (PGL2 K)) ⊔ J := le_sup_right
      have hrel := Subgroup.relIndex_mul_index hle
      rw [hJindex] at hrel
      have hne : J.relIndex ((Pmodel : Subgroup (PGL2 K)) ⊔ J) ≠ 1 := by
        intro h1
        have hJle : (Pmodel : Subgroup (PGL2 K)) ⊔ J ≤ J :=
          Subgroup.relIndex_eq_one.mp h1
        exact hPnot (le_sup_left.trans hJle)
      have hind : 2 ≤ J.relIndex ((Pmodel : Subgroup (PGL2 K)) ⊔ J) := by
        have hpos : 0 < J.relIndex ((Pmodel : Subgroup (PGL2 K)) ⊔ J) :=
          Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
            (H := J.subgroupOf ((Pmodel : Subgroup (PGL2 K)) ⊔ J)))
        omega
      have htop : ((Pmodel : Subgroup (PGL2 K)) ⊔ J).index = 1 := by
        have hrdvd : J.relIndex ((Pmodel : Subgroup (PGL2 K)) ⊔ J) ∣ 2 := by
          refine ⟨((Pmodel : Subgroup (PGL2 K)) ⊔ J).index, ?_⟩
          exact hrel.symm
        have hr2 : J.relIndex ((Pmodel : Subgroup (PGL2 K)) ⊔ J) = 2 := by
          rcases (Nat.dvd_prime Nat.prime_two).mp hrdvd with h1 | h2
          · exact False.elim (hne h1)
          · exact h2
        have hmul : 2 * ((Pmodel : Subgroup (PGL2 K)) ⊔ J).index = 2 := by
          simpa [hr2] using hrel.symm
        omega
      exact Subgroup.index_eq_one.mp htop
    have hLrel : Ebar.relIndex (Pq : Subgroup (c.Hhat ⧸ O)) = EbarL.relIndex PqL := by
      have h := Subgroup.relIndex_map_map_of_injective (f := L.subtype)
        (H := EbarL) (K := PqL) L.subtype_injective
      have hE : EbarL.map L.subtype = Ebar := by
        dsimp [EbarL]
        exact Subgroup.map_subgroupOf_eq_of_le hEbarL
      have hP : PqL.map L.subtype = (Pq : Subgroup (c.Hhat ⧸ O)) := by
        dsimp [PqL]
        exact Subgroup.map_subgroupOf_eq_of_le hPqL
      rw [hE, hP] at h
      exact h
    have hMap : J.relIndex (Pmodel : Subgroup (PGL2 K)) = EbarL.relIndex PqL := by
      have h := Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom)
        (H := EbarL) (K := PqL) e.injective
      rw [hEbarJ, hPqPmodel] at h
      exact h
    rw [hLrel, ← hMap]
    calc
      J.relIndex (Pmodel : Subgroup (PGL2 K)) =
          ((Pmodel : Subgroup (PGL2 K)) ⊓ J).relIndex (Pmodel : Subgroup (PGL2 K)) :=
        (Subgroup.inf_relIndex_left (H := (Pmodel : Subgroup (PGL2 K))) (K := J)).symm
      _ = J.relIndex (Pmodel : Subgroup (PGL2 K)) :=
        Subgroup.inf_relIndex_left (H := (Pmodel : Subgroup (PGL2 K))) (K := J)
      _ = J.relIndex ((Pmodel : Subgroup (PGL2 K)) ⊔ J) :=
        (Subgroup.relIndex_sup_right (H := (Pmodel : Subgroup (PGL2 K))) (K := J)).symm
      _ = J.relIndex ⊤ := by rw [hPmodelJ]
      _ = 2 := by rw [Subgroup.relIndex_top_right, hJindex]
  -- `|P ∩ (E·O) : P| = 2` through the injective map `q|P`.
  have hPinter : ((P : Subgroup c.Hhat) ⊓ (Ei ⊔ O)).relIndex
      (P : Subgroup c.Hhat) = 2 := by
    have hOmap : O.map q = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨o, ho, rfl⟩
      have hq : q o = 1 := (QuotientGroup.eq_one_iff (N := O) o).mpr ho
      exact Subgroup.mem_bot.mpr hq
    have hEsup : (Ei ⊔ O).map q = Ei.map q := by
      rw [Subgroup.map_sup, hOmap, sup_bot_eq]
    have hmap : ((P : Subgroup c.Hhat) ⊓ (Ei ⊔ O)).map q =
        (P : Subgroup c.Hhat).map q ⊓ (Ei ⊔ O).map q := by
      apply le_antisymm
      · intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact Subgroup.mem_inf.mpr
          ⟨Subgroup.mem_map.mpr ⟨y, hy.1, rfl⟩,
            Subgroup.mem_map.mpr ⟨y, hy.2, rfl⟩⟩
      · intro x hx
        rcases Subgroup.mem_inf.mp hx with ⟨hxP, hxE⟩
        rcases Subgroup.mem_map.mp hxP with ⟨p, hp, rfl⟩
        rcases Subgroup.mem_map.mp hxE with ⟨e0, he0, hxe⟩
        have hpe : q (p * e0⁻¹) = 1 := by
          rw [map_mul, map_inv]
          rw [← hxe]
          simp
        have hpE : p ∈ Ei ⊔ O := by
          have hq1 : q (p * e0⁻¹) = 1 := hpe
          have hmem : p * e0⁻¹ ∈ O :=
            (QuotientGroup.eq_one_iff (N := O) (p * e0⁻¹)).mp hq1
          have hback : p = (p * e0⁻¹) * e0 := by group
          rw [hback]
          exact (Ei ⊔ O).mul_mem ((le_sup_right : O ≤ Ei ⊔ O) hmem) he0
        exact Subgroup.mem_map.mpr
          ⟨p, ⟨hp, hpE⟩, rfl⟩
    have hPq : (P : Subgroup c.Hhat).map q = (Pq : Subgroup (c.Hhat ⧸ O)) := by
      rfl
    let f : (P : Subgroup c.Hhat) →* c.Hhat ⧸ O :=
      q.comp (P : Subgroup c.Hhat).subtype
    have hrel' := Subgroup.relIndex_map_map_of_injective (f := f)
      (H := ((P : Subgroup c.Hhat) ⊓ (Ei ⊔ O)).subgroupOf (P : Subgroup c.Hhat))
      (K := ⊤) hqP
    rw [Subgroup.relIndex_top_right] at hrel'
    change (((P : Subgroup c.Hhat) ⊓ (Ei ⊔ O)).subgroupOf
        (P : Subgroup c.Hhat)).index = 2
    rw [← hrel']
    calc
      (Subgroup.map f (((P : Subgroup c.Hhat) ⊓ (Ei ⊔ O)).subgroupOf
          (P : Subgroup c.Hhat))).relIndex (Subgroup.map f ⊤)
          = (((P : Subgroup c.Hhat) ⊓ (Ei ⊔ O)).map q).relIndex
              ((P : Subgroup c.Hhat).map q) := by
              congr 1 <;> ext x <;>
                simp [f, Subgroup.mem_map, Subgroup.mem_subgroupOf, and_assoc, and_comm, and_left_comm]
      _ = Ebar.relIndex (Pq : Subgroup (c.Hhat ⧸ O)) := by
              rw [hmap, hEsup, hPq]
              rw [Subgroup.inf_relIndex_left (H := (Pq : Subgroup (c.Hhat ⧸ O)))
                (K := (Subgroup.map q Ei))]
      _ = 2 := hPqrel
  -- The odd factor `|P ∩ (E·O) : P ∩ E|` divides `|O|`.
  have hodd : Odd (Subgroup.relIndex ((P : Subgroup c.Hhat) ⊓ Ei)
      ((P : Subgroup c.Hhat) ⊓ (Ei ⊔ O))) := by
    let A : Subgroup c.Hhat := (P : Subgroup c.Hhat) ⊓ (Ei ⊔ O)
    let B : Subgroup c.Hhat := (P : Subgroup c.Hhat) ⊓ Ei
    have hBA : B ≤ A := inf_le_inf le_rfl (le_sup_left : Ei ≤ Ei ⊔ O)
    have hBnormP : IsNormalIn B (P : Subgroup c.Hhat) := by
      -- `B = P ∩ Ei` is normal in `P`, hence in `A`
      have hEiNorm : IsNormalIn Ei (⊤ : Subgroup c.Hhat) := by
        refine ⟨le_top, ?_⟩
        intro h hh k hk
        exact (inferInstance : Ei.Normal).conj_mem k hk h
      refine ⟨?_, ?_⟩
      · intro x hx
        exact hx.1
      · intro a ha b hb
        have hbEi : b ∈ Ei := hb.2
        have hconjEi : a * b * a⁻¹ ∈ Ei := hEiNorm.2 a (by trivial) b hbEi
        have hconjP : a * b * a⁻¹ ∈ (P : Subgroup c.Hhat) :=
          (P : Subgroup c.Hhat).mul_mem ((P : Subgroup c.Hhat).mul_mem ha hb.1)
            ((P : Subgroup c.Hhat).inv_mem ha)
        exact ⟨hconjP, hconjEi⟩
    have hA_norm_B : A ≤ Subgroup.normalizer (B : Set c.Hhat) :=
      (inf_le_left : A ≤ (P : Subgroup c.Hhat)).trans
        (le_normalizer_of_isNormalIn hBnormP)
    let : (B.subgroupOf A).Normal := by
      exact Subgroup.normal_subgroupOf_of_le_normalizer (H := A) (N := B)
        hA_norm_B
    let ψ : A →* c.Hhat ⧸ Ei := (QuotientGroup.mk' Ei).comp A.subtype
    have hψker : ψ.ker = B.subgroupOf A := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change QuotientGroup.mk' Ei (x : c.Hhat) = 1 ↔ (x : c.Hhat) ∈ B
      rw [← MonoidHom.mem_ker (f := QuotientGroup.mk' Ei)]
      rw [QuotientGroup.ker_mk']
      simp [B]
      exact fun _ => x.2.1
    have hψrange : Nat.card ψ.range = B.relIndex A := by
      have h1 : Nat.card (A ⧸ (B.subgroupOf A)) = Nat.card ψ.range := by
        rw [← hψker]
        simpa [MonoidHom.range_comp, Subgroup.subtype_range] using
          (Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv)
      rw [Subgroup.relIndex]
      exact h1.symm
    have hrange_le : ψ.range ≤ (Ei ⊔ O).map (QuotientGroup.mk' Ei) := by
      intro y hy
      rcases MonoidHom.mem_range.mp hy with ⟨x, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(x : c.Hhat), (x : A).2.2, rfl⟩
    have hdvd1 : B.relIndex A ∣
        Nat.card ((Ei ⊔ O).map (QuotientGroup.mk' Ei)) := by
      rw [← hψrange]
      exact Subgroup.card_dvd_of_le hrange_le
    -- `|(Ei ⊔ O) ⧸ Ei| = |O| / |O ∩ Ei|` divides `|O|`.
    let EO : Subgroup c.Hhat := Ei ⊔ O
    let ψ2 : EO →* c.Hhat ⧸ Ei := (QuotientGroup.mk' Ei).comp EO.subtype
    have hψ2ker : ψ2.ker = Ei.subgroupOf EO := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change QuotientGroup.mk' Ei (x : c.Hhat) = 1 ↔ (x : c.Hhat) ∈ Ei
      rw [← MonoidHom.mem_ker (f := QuotientGroup.mk' Ei)]
      rw [QuotientGroup.ker_mk']
    have hrange2 : ψ2.range = (Ei ⊔ O).map (QuotientGroup.mk' Ei) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact Subgroup.mem_map.mpr ⟨(x : c.Hhat), x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
    have hdvd2 : Nat.card ((Ei ⊔ O).map (QuotientGroup.mk' Ei)) ∣ Nat.card O := by
      -- the map `o ↦ o·Ei` from `O` is surjective onto `(Ei ⊔ O) ⧸ Ei`
      let φ : O →* c.Hhat ⧸ Ei := (QuotientGroup.mk' Ei).comp O.subtype
      have hφker : φ.ker = Ei.subgroupOf O := by
        ext x
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        change QuotientGroup.mk' Ei (x : c.Hhat) = 1 ↔ (x : c.Hhat) ∈ Ei
        rw [← MonoidHom.mem_ker (f := QuotientGroup.mk' Ei)]
        rw [QuotientGroup.ker_mk']
      have hφrange : φ.range = (Ei ⊔ O).map (QuotientGroup.mk' Ei) := by
        apply le_antisymm
        · intro y hy
          rcases MonoidHom.mem_range.mp hy with ⟨o, rfl⟩
          exact Subgroup.mem_map.mpr ⟨(o : c.Hhat), (le_sup_right : O ≤ Ei ⊔ O) o.2, rfl⟩
        · intro y hy
          rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
          rcases Subgroup.mem_sup_of_normal_left.mp hx with ⟨e0, he0, o, ho, hxo⟩
          have hq : QuotientGroup.mk' Ei (o : c.Hhat) = QuotientGroup.mk' Ei (x : c.Hhat) := by
            apply (QuotientGroup.eq_iff_div_mem (N := Ei)
              (x := (o : c.Hhat)) (y := (x : c.Hhat))).2
            have hdiv : (o : c.Hhat) / x = e0⁻¹ := by
              rw [← hxo, div_eq_mul_inv]
              group
            rw [hdiv]
            exact Ei.inv_mem he0
          refine MonoidHom.mem_range.mpr ⟨⟨(o : c.Hhat), ho⟩, ?_⟩
          simpa [φ] using hq
      have h1 : Nat.card (O ⧸ (Ei.subgroupOf O)) = Nat.card ((Ei ⊔ O).map (QuotientGroup.mk' Ei)) := by
        rw [← hφker, ← hφrange]
        simpa [MonoidHom.range_comp, Subgroup.subtype_range] using
          (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv)
      have h2 : Nat.card O = Nat.card (O ⧸ (Ei.subgroupOf O)) * Nat.card (Ei.subgroupOf O) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Ei.subgroupOf O)
      rw [h1] at h2
      exact ⟨Nat.card (Ei.subgroupOf O), h2⟩
    have hdvdO : B.relIndex A ∣ Nat.card O := hdvd1.trans hdvd2
    have hOodd : Odd (Nat.card O) := by
      have hOcop : Nat.Coprime 2 (Nat.card O) := by
        simpa [O] using (pPrimeCore_coprime_card (p := 2) (G := c.Hhat))
      exact Nat.coprime_two_left.mp hOcop
    exact hOodd.of_dvd_nat hdvdO
  -- `|P : P ∩ E| = 2·(odd)` is a `2`-power, so it is exactly `2`.
  have hpow : ∃ n : ℕ,
      ((P : Subgroup c.Hhat) ⊓ Ei).relIndex (P : Subgroup c.Hhat) = 2 ^ n := by
    let B : Subgroup c.Hhat := (P : Subgroup c.Hhat) ⊓ Ei
    have hcard : Nat.card B * B.relIndex (P : Subgroup c.Hhat) =
        Nat.card (P : Subgroup c.Hhat) := by
      rw [Subgroup.relIndex]
      have h := Subgroup.card_mul_index
        (H := B.subgroupOf (P : Subgroup c.Hhat))
      have hcard' : Nat.card B =
          Nat.card (↥(B.subgroupOf (P : Subgroup c.Hhat))) := by
        exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_left : B ≤ (P : Subgroup c.Hhat))).toEquiv).symm
      rw [hcard']
      exact h
    rcases IsPGroup.iff_card.mp P.isPGroup' with ⟨n, hn⟩
    have hdvd : Nat.card B ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases hdvd with ⟨k, hk⟩ -- `hk : 2 ^ n = Nat.card B * k`
    have hrelEq : B.relIndex (P : Subgroup c.Hhat) = k := by
      apply Nat.mul_left_cancel (Nat.card_pos (α := B))
      calc
        Nat.card B * B.relIndex (P : Subgroup c.Hhat) = Nat.card (P : Subgroup c.Hhat) := hcard
        _ = 2 ^ n := hn
        _ = Nat.card B * k := hk
    have hkpow : ∃ m : ℕ, k = 2 ^ m := by
      have hkdvd : k ∣ 2 ^ n := by
        refine ⟨Nat.card B, ?_⟩
        rw [mul_comm]
        exact hk
      rcases (Nat.dvd_prime_pow Nat.prime_two).mp hkdvd with ⟨m, _hmle, hm⟩
      exact ⟨m, hm⟩
    rcases hkpow with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hrelEq, hm]
  have hrel : ((P : Subgroup c.Hhat) ⊓ Ei).relIndex (P : Subgroup c.Hhat) = 2 := by
    let B : Subgroup c.Hhat := (P : Subgroup c.Hhat) ⊓ Ei
    let A : Subgroup c.Hhat := (P : Subgroup c.Hhat) ⊓ (Ei ⊔ O)
    have hBA : B ≤ A := inf_le_inf le_rfl (le_sup_left : Ei ≤ Ei ⊔ O)
    have hAP : A ≤ (P : Subgroup c.Hhat) := inf_le_left
    have h1 : B.relIndex A * A.relIndex (P : Subgroup c.Hhat) =
        B.relIndex (P : Subgroup c.Hhat) :=
      Subgroup.relIndex_mul_relIndex B A (P : Subgroup c.Hhat) hBA hAP
    have htwo : B.relIndex (P : Subgroup c.Hhat) = 2 * B.relIndex A := by
      rw [← h1, hPinter]
      rw [mul_comm]
    rcases hpow with ⟨n, hn⟩
    have hn1 : n = 1 := by
      by_contra hn1
      have hn0 : n = 0 ∨ 2 ≤ n := by omega
      rcases hn0 with hn0 | hn2
      · exfalso
        rw [hn0] at hn
        have hEq : B.relIndex (P : Subgroup c.Hhat) = 1 := hn
        rw [htwo] at hEq
        rcases hodd with ⟨k, hk⟩
        rw [hk] at hEq
        norm_num at hEq
      · exfalso
        rcases hodd with ⟨k, hk⟩
        have h4 : 4 ∣ 2 * (2 * k + 1) := by
          rw [← hk, ← htwo, hn]
          exact pow_dvd_pow 2 (by omega)
        have h4not : ¬ 4 ∣ 2 * (2 * k + 1) := by
          rintro ⟨c, hc⟩
          have hmul : 2 * (2 * k + 1) = 2 * (2 * c) := by
            rw [hc]
            ring
          have hcancel : 2 * k + 1 = 2 * c :=
            Nat.mul_left_cancel (by norm_num) hmul
          omega
        exact h4not h4
    rw [hn, hn1]
    norm_num
  -- convert to the ambient `G`
  have hconv : d.E.relIndex (c.S : Subgroup G) =
      ((P : Subgroup c.Hhat) ⊓ Ei).relIndex (P : Subgroup c.Hhat) := by
    have hE : Ei.map c.Hhat.subtype = d.E := by
      dsimp [Ei]
      exact Subgroup.map_subgroupOf_eq_of_le d.isComponent.1
    have hP : (P : Subgroup c.Hhat).map c.Hhat.subtype = (c.S : Subgroup G) := by
      dsimp [P]
      exact Subgroup.map_subgroupOf_eq_of_le hSle
    have h := Subgroup.relIndex_map_map_of_injective (f := c.Hhat.subtype)
      (H := Ei) (K := (P : Subgroup c.Hhat)) c.Hhat.subtype_injective
    rw [hE, hP] at h
    calc
      d.E.relIndex (c.S : Subgroup G) = Ei.relIndex (P : Subgroup c.Hhat) := h
      _ = ((P : Subgroup c.Hhat) ⊓ Ei).relIndex (P : Subgroup c.Hhat) :=
        (Subgroup.inf_relIndex_left (H := (P : Subgroup c.Hhat)) (K := Ei)).symm
  rw [hconv]
  exact hrel


end CFSG.GorensteinWalter
