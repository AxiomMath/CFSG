module

public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs

import CFSG.Quasithin.Recognition.GoldschmidtF112RTransport
import CFSG.Quasithin.Recognition.St84.Gen.NatSecMap
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups commutatorElement

variable {G H : Type*} [Group G] [Group H]
variable {L : Subgroup G} {N : Subgroup H}

private theorem mem_centerOf_iff_of_mulEquiv_of_mem_iff (e : ↥L ≃* ↥N) {Y : Subgroup G}
    {Y' : Subgroup H} (hYL : Y ≤ L) (hY'N : Y' ≤ N)
    (hY : ∀ x : ↥L, (x : G) ∈ Y ↔ ((e x : ↥N) : H) ∈ Y') (x : ↥L) :
    (x : G) ∈ centerOf Y ↔ ((e x : ↥N) : H) ∈ centerOf Y' := by
  rw [centerOf, centerOf, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff, hY]
  refine and_congr_right fun _ => ⟨fun hx y hy => ?_, fun hx y hy => ?_⟩
  · obtain ⟨y', hy'⟩ := e.surjective ⟨y, hY'N hy⟩
    have hy'Y : (y' : G) ∈ Y := (hY y').mpr (by rw [hy']; exact hy)
    have hL : y' * x = x * y' := Subtype.ext (hx (y' : G) hy'Y)
    have he := congrArg e hL
    rw [map_mul, map_mul] at he
    have hval : (e y' : H) * (e x : H) = (e x : H) * (e y' : H) :=
      congrArg Subtype.val he
    rw [hy'] at hval
    simpa using hval
  · let y' : ↥L := ⟨y, hYL hy⟩
    have hN : e y' * e x = e x * e y' := Subtype.ext (hx (e y' : H) ((hY y').mp hy))
    have hL : y' * x = x * y' := e.injective (by rw [map_mul, map_mul]; exact hN)
    exact congrArg Subtype.val hL

theorem mem_centerOf_iff_of_mulEquiv (e : ↥L ≃* ↥N) (x : ↥L) :
    (x : G) ∈ centerOf L ↔ ((e x : ↥N) : H) ∈ centerOf N :=
  mem_centerOf_iff_of_mulEquiv_of_mem_iff e le_rfl le_rfl (fun y => iff_of_true y.2 (e y).2) x

theorem mem_centerOf_pCoreOf_iff_of_mulEquiv (e : ↥L ≃* ↥N) (p : ℕ) (x : ↥L) :
    (x : G) ∈ centerOf (pCoreOf p L) ↔ ((e x : ↥N) : H) ∈ centerOf (pCoreOf p N) :=
  mem_centerOf_iff_of_mulEquiv_of_mem_iff e (CFSG.LieType.BorelTits.pCoreOf_le p L)
    (CFSG.LieType.BorelTits.pCoreOf_le p N) (mem_pCoreOf_iff_of_mulEquiv e p) x

theorem centerOf_pCoreOf_eq_of_mulEquiv (e : ↥L ≃* ↥N) {p : ℕ}
    (h : centerOf (pCoreOf p N) = centerOf N) : centerOf (pCoreOf p L) = centerOf L := by
  ext x
  constructor
  · intro hx
    have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le p L (Subgroup.mem_inf.mp hx).1
    refine (mem_centerOf_iff_of_mulEquiv e ⟨x, hxL⟩).mpr ?_
    rw [← h]
    exact (mem_centerOf_pCoreOf_iff_of_mulEquiv e p ⟨x, hxL⟩).mp hx
  · intro hx
    have hxL : x ∈ L := (Subgroup.mem_inf.mp hx).1
    refine (mem_centerOf_pCoreOf_iff_of_mulEquiv e p ⟨x, hxL⟩).mpr ?_
    rw [h]
    exact (mem_centerOf_iff_of_mulEquiv e ⟨x, hxL⟩).mp hx

private theorem mem_map_subgroupOf_map (e : ↥L ≃* ↥N) {W : Subgroup G} (hWL : W ≤ L)
    (y : ↥N) :
    ((y : H) ∈ ((W.subgroupOf L).map e.toMonoidHom).map N.subtype ↔
      ((e.symm y : ↥L) : G) ∈ W) := by
  have h1 : ((y : H) ∈ ((W.subgroupOf L).map e.toMonoidHom).map N.subtype ↔
      y ∈ (W.subgroupOf L).map e.toMonoidHom) :=
    Subgroup.mem_map_iff_mem N.subtype_injective
  have h2 : (y ∈ (W.subgroupOf L).map e.toMonoidHom ↔
      e.symm y ∈ W.subgroupOf L) := Subgroup.mem_map_equiv
  rw [h1, h2, Subgroup.mem_subgroupOf]

private theorem mem_map_subgroupOf_map_symm (e : ↥L ≃* ↥N) {W' : Subgroup H}
    (x : ↥L) :
    ((x : G) ∈ ((W'.subgroupOf N).map e.symm.toMonoidHom).map L.subtype ↔
      ((e x : ↥N) : H) ∈ W') := by
  have h1 : ((x : G) ∈ ((W'.subgroupOf N).map e.symm.toMonoidHom).map L.subtype ↔
      x ∈ (W'.subgroupOf N).map e.symm.toMonoidHom) :=
    Subgroup.mem_map_iff_mem L.subtype_injective
  have h2 : (x ∈ (W'.subgroupOf N).map e.symm.toMonoidHom ↔
      e x ∈ W'.subgroupOf N) := by
    rw [Subgroup.mem_map_equiv]
    simp
  rw [h1, h2, Subgroup.mem_subgroupOf]

theorem exists_sub_of_mulEquiv (e : ↥L ≃* ↥N) {p : ℕ} {W' : Subgroup H}
    (hZW' : centerOf (pCoreOf p N) ≤ W') (hW'Q : W' ≤ pCoreOf p N)
    (hcomm : ⁅W', N⁆ ≤ centerOf (pCoreOf p N)) :
    ∃ W : Subgroup G, centerOf (pCoreOf p L) ≤ W ∧ W ≤ pCoreOf p L ∧
      Nat.card W = Nat.card W' ∧ ⁅W, L⁆ ≤ centerOf (pCoreOf p L) ∧
      ∀ x : ↥L, (x : G) ∈ W ↔ ((e x : ↥N) : H) ∈ W' := by
  let W : Subgroup G := ((W'.subgroupOf N).map e.symm.toMonoidHom).map L.subtype
  have hW'N : W' ≤ N := hW'Q.trans (CFSG.LieType.BorelTits.pCoreOf_le p N)
  have hWL : W ≤ L := Subgroup.map_subtype_le _
  have hWmem : ∀ x : ↥L, ((x : G) ∈ W ↔ ((e x : ↥N) : H) ∈ W') :=
    fun x => mem_map_subgroupOf_map_symm e x
  have hZW : centerOf (pCoreOf p L) ≤ W := by
    intro z hz
    have hzL : z ∈ L := CFSG.LieType.BorelTits.pCoreOf_le p L (Subgroup.mem_inf.mp hz).1
    refine (hWmem ⟨z, hzL⟩).mpr ?_
    exact hZW' ((mem_centerOf_pCoreOf_iff_of_mulEquiv e p ⟨z, hzL⟩).mp hz)
  have hWQ : W ≤ pCoreOf p L := by
    intro z hz
    have hzL : z ∈ L := hWL hz
    refine (mem_pCoreOf_iff_of_mulEquiv e p ⟨z, hzL⟩).mpr ?_
    exact hW'Q ((hWmem ⟨z, hzL⟩).mp hz)
  have hcard : Nat.card W = Nat.card W' := by
    have h1 : Nat.card ↥W = Nat.card ↥((W'.subgroupOf N).map e.symm.toMonoidHom) :=
      Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective
    have h2 : Nat.card ↥((W'.subgroupOf N).map e.symm.toMonoidHom) =
        Nat.card ↥(W'.subgroupOf N) :=
      Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective
    have h3 : Nat.card ↥(W'.subgroupOf N) = Nat.card ↥W' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW'N).toEquiv
    rw [h1, h2, h3]
  have hcommW : ⁅W, L⁆ ≤ centerOf (pCoreOf p L) := by
    rw [Subgroup.commutator_le]
    intro w hw l hl
    have hwL : w ∈ L := hWL hw
    let wL : ↥L := ⟨w, hwL⟩
    let lL : ↥L := ⟨l, hl⟩
    have hw' : ((e wL : ↥N) : H) ∈ W' := (hWmem wL).mp hw
    have hl' : ((e lL : ↥N) : H) ∈ N := (e lL).2
    have hZ : ((⁅e wL, e lL⁆ : ↥N) : H) ∈ centerOf (pCoreOf p N) :=
      (Subgroup.commutator_le.mp hcomm) _ hw' _ hl'
    have hZ' : ((e ⁅wL, lL⁆ : ↥N) : H) ∈ centerOf (pCoreOf p N) := by
      rwa [map_commutatorElement]
    have hthis := (mem_centerOf_pCoreOf_iff_of_mulEquiv e p ⁅wL, lL⁆).mpr hZ'
    change ((⁅wL, lL⁆ : ↥L) : G) ∈ centerOf (pCoreOf p L)
    exact hthis
  exact ⟨W, hZW, hWQ, hcard, hcommW, hWmem⟩

private theorem map_subgroupOf_map_normalizer (e : ↥L ≃* ↥N) {W : Subgroup G} (hWL : W ≤ L)
    (hWnorm : L ≤ Subgroup.normalizer (W : Set G)) :
    N ≤ Subgroup.normalizer (((W.subgroupOf L).map e.toMonoidHom).map N.subtype : Set H) := by
  have hWmem : ∀ y : ↥N,
      ((y : H) ∈ ((W.subgroupOf L).map e.toMonoidHom).map N.subtype ↔
        ((e.symm y : ↥L) : G) ∈ W) := fun y => mem_map_subgroupOf_map e hWL y
  have hstep : ∀ n ∈ N,
      ∀ y ∈ ((W.subgroupOf L).map e.toMonoidHom).map N.subtype,
        n * y * n⁻¹ ∈ ((W.subgroupOf L).map e.toMonoidHom).map N.subtype := by
    intro n hn y hy
    have hyN : y ∈ N := Subgroup.map_subtype_le _ hy
    let nN : ↥N := ⟨n, hn⟩
    let yN : ↥N := ⟨y, hyN⟩
    have hyW : ((e.symm yN : ↥L) : G) ∈ W := (hWmem yN).mp hy
    have hmemN : n * y * n⁻¹ ∈ N := N.mul_mem (N.mul_mem hn hyN) (N.inv_mem hn)
    refine (hWmem ⟨n * y * n⁻¹, hmemN⟩).mpr ?_
    have hconj : ((e.symm nN : ↥L) : G) * ((e.symm yN : ↥L) : G) *
        ((e.symm nN : ↥L) : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hWnorm (e.symm nN).2) _).mp hyW
    have heq : (e.symm ⟨n * y * n⁻¹, hmemN⟩ : ↥L) =
        (e.symm nN) * (e.symm yN) * (e.symm nN)⁻¹ := by
      apply e.injective
      simp only [map_mul, map_inv]
      apply Subtype.ext
      simp [nN, yN]
    rw [heq]
    exact hconj
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨hstep n hn y, fun hy => by
    have h := hstep n⁻¹ (N.inv_mem hn) (n * y * n⁻¹) hy
    have heq : n⁻¹ * (n * y * n⁻¹) * (n⁻¹)⁻¹ = y := by group
    rwa [heq] at h⟩

theorem eq_centerOf_or_eq_pCoreOf_of_mulEquiv (e : ↥L ≃* ↥N) {p : ℕ}
    (h : ∀ W : Subgroup H, centerOf (pCoreOf p N) ≤ W → W ≤ pCoreOf p N →
      N ≤ Subgroup.normalizer (W : Set H) → W = centerOf (pCoreOf p N) ∨ W = pCoreOf p N)
    {W : Subgroup G} (hZW : centerOf (pCoreOf p L) ≤ W) (hWQ : W ≤ pCoreOf p L)
    (hWnorm : L ≤ Subgroup.normalizer (W : Set G)) :
    W = centerOf (pCoreOf p L) ∨ W = pCoreOf p L := by
  have hWL : W ≤ L := hWQ.trans (CFSG.LieType.BorelTits.pCoreOf_le p L)
  let W' : Subgroup H := ((W.subgroupOf L).map e.toMonoidHom).map N.subtype
  have hW'mem : ∀ y : ↥N, ((y : H) ∈ W' ↔ ((e.symm y : ↥L) : G) ∈ W) :=
    fun y => mem_map_subgroupOf_map e hWL y
  have hW'N : W' ≤ N := Subgroup.map_subtype_le _
  have hZW' : centerOf (pCoreOf p N) ≤ W' := by
    intro y hy
    have hyN : y ∈ N := (CFSG.LieType.BorelTits.pCoreOf_le p N) (Subgroup.mem_inf.mp hy).1
    let yN : ↥N := ⟨y, hyN⟩
    refine (hW'mem yN).mpr ?_
    exact hZW ((mem_centerOf_pCoreOf_iff_of_mulEquiv e.symm p yN).mp hy)
  have hW'Q : W' ≤ pCoreOf p N := by
    intro y hy
    have hyN : y ∈ N := hW'N hy
    let yN : ↥N := ⟨y, hyN⟩
    exact (mem_pCoreOf_iff_of_mulEquiv e.symm p yN).mpr (hWQ ((hW'mem yN).mp hy))
  have hW'norm : N ≤ Subgroup.normalizer (W' : Set H) :=
    map_subgroupOf_map_normalizer e hWL hWnorm
  rcases h W' hZW' hW'Q hW'norm with hW' | hW'
  · left
    apply le_antisymm ?_ hZW
    intro x hx
    have hxL : x ∈ L := hWL hx
    let xL : ↥L := ⟨x, hxL⟩
    have hxW' : ((e xL : ↥N) : H) ∈ W' := by
      refine (hW'mem (e xL)).mpr ?_
      simpa [xL] using hx
    rw [hW'] at hxW'
    exact (mem_centerOf_pCoreOf_iff_of_mulEquiv e p xL).mpr hxW'
  · right
    apply le_antisymm hWQ ?_
    intro x hx
    have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le p L hx
    let xL : ↥L := ⟨x, hxL⟩
    have hxW' : ((e xL : ↥N) : H) ∈ W' := by
      rw [hW']
      exact (mem_pCoreOf_iff_of_mulEquiv e p xL).mp hx
    simpa [xL] using (hW'mem (e xL)).mp hxW'

theorem isNatSecOf_centerOf_of_mulEquiv {F : Type*} [Field F] (e : ↥L ≃* ↥N) {α : ↥N →* SL(2, F)}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥N)
    (hnat : IsNatSecOf N (centerOf (pCoreOf 2 N)) ⊥ α) :
    Function.Surjective (α.comp e.toMonoidHom) ∧
      (α.comp e.toMonoidHom).ker = CFSG.pCore 2 ↥L ∧
      IsNatSecOf L (centerOf (pCoreOf 2 L)) ⊥ (α.comp e.toMonoidHom) := by
  have hE : centerOf (pCoreOf 2 L) ≤ L := fun x hx =>
    CFSG.LieType.BorelTits.pCoreOf_le 2 L (Subgroup.mem_inf.mp hx).1
  have hE' : centerOf (pCoreOf 2 N) ≤ N := fun x hx =>
    CFSG.LieType.BorelTits.pCoreOf_le 2 N (Subgroup.mem_inf.mp hx).1
  have hEe : ∀ x : ↥N, (x : H) ∈ centerOf (pCoreOf 2 N) ↔
      ((e.symm x : ↥L) : G) ∈ centerOf (pCoreOf 2 L) :=
    fun x => mem_centerOf_pCoreOf_iff_of_mulEquiv e.symm 2 x
  have hne : ∀ x : ↥N, (x : H) ∈ (⊥ : Subgroup H) ↔
      ((e.symm x : ↥L) : G) ∈ (⊥ : Subgroup G) := by
    intro x
    simp
  have hnat' : IsNatSecOf L (centerOf (pCoreOf 2 L)) ⊥ (α.comp e.toMonoidHom) := by
    simpa using IsNatSecOf.of_mulEquiv (e := e.symm) hE' hE hEe hne hnat
  refine ⟨hα.comp e.surjective, ?_, hnat'⟩
  change (α.comp (e : ↥L →* ↥N)).ker = CFSG.pCore 2 ↥L
  rw [MonoidHom.ker_comp_mulEquiv, hker]
  simpa using CFSG.pCore_map_iso 2 e.symm

end CFSG.Quasithin.F112R.St84

end
