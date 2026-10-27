module

public import CFSG.RankThree.GF2n.Tim81.Sec5.Stmts
import CFSG.RankThree.GF2n.Tim81.Sec5.S58Big
import CFSG.RankThree.GF2n.Tim81.Sec5.S53S55

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin CFSG.GroupTheory
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V : Subgroup G}

namespace Sec5Hyp

private theorem q3_plane_g (hS : Sec5Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) {y : G} (hyP : y ∈ Pc M V)
    (hyC : y ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) :
    (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆ =
        ⁅Pc M V, conjSubgroup g V⁆ ⊓ Subgroup.centralizer ({y} : Set G)) ∧
      Nat.card ↥(V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) = Nat.card V ^ 2 ∧
      (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) ∈ fSet M V := by
  classical
  have hroot := hS.toRootHyp
  have hSg := hS.shape hg
  obtain ⟨yg, hygH, -, hVyg, -⟩ :=
    hroot.exists_mem_conj_eq_of_eq_sup hSg.Pc_le hSg.hH
  have hygV : conjSubgroup yg V ≠ V := by
    rw [← hVyg]
    exact ne_of_mem_sigmaSet hroot hg
  have hCg : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) =
      Pc M V ⊓ kOf V (hOf M V g) := by
    rw [hVyg]
    exact hSg.Pc_inf_centralizer_conj hroot hygH hygV
  have hEg : ⁅Pc M V, conjSubgroup g V⁆ =
      Pc M V ⊓ Tim79a.xOf V (hOf M V g) := by
    rw [hVyg]
    exact hSg.commutator_Pc_conj_eq hroot hygH hygV
  have hyKg : y ∉ kOf V (hOf M V g) := by
    intro hyk
    exact hyC (hCg.symm ▸ Subgroup.mem_inf.mpr ⟨hyP, hyk⟩)
  have hc3g := hSg.sup_commutator_eq hroot hygH hygV hyP hyKg
  have hA1g : V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆ =
      Tim79a.xOf V (hOf M V g) ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hVyg]
    exact hc3g.1
  have hplaneLeP : Tim79a.xOf V (hOf M V g) ⊓
      Subgroup.centralizer ({y} : Set G) ≤ Pc M V :=
    (hSg.xOf_inf_centralizer_le_and_card hroot hyP hyKg).1
  have hAEg : V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆ =
      ⁅Pc M V, conjSubgroup g V⁆ ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hA1g, hEg]
    rw [inf_assoc, inf_eq_right.mpr hplaneLeP]
  have hcardg : Nat.card ↥(V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) =
      Nat.card V ^ 2 := by
    rw [hA1g]
    exact (hSg.xOf_inf_centralizer_le_and_card hroot hyP hyKg).2
  refine ⟨hAEg, hcardg, ?_⟩
  refine hS.stmt51a (conjSubgroup g V) hg y hyP ?_
  intro hycen
  exact hyC (Subgroup.mem_inf.mpr ⟨hyP, hycen⟩)

private theorem q3_plane_h (hS : Sec5Hyp M V) {g h : G}
    (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hC : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) =
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))
    {y : G} (hyP : y ∈ Pc M V)
    (hyC : y ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) :
    V ⊔ ⁅conjSubgroup h V, Subgroup.zpowers y⁆ =
      ⁅Pc M V, conjSubgroup h V⁆ ⊓ Subgroup.centralizer ({y} : Set G) := by
  classical
  have hroot := hS.toRootHyp
  have hSh := hS.shape hh
  obtain ⟨yh, hyhH, -, hVyh, -⟩ :=
    hroot.exists_mem_conj_eq_of_eq_sup hSh.Pc_le hSh.hH
  have hyhV : conjSubgroup yh V ≠ V := by
    rw [← hVyh]
    exact ne_of_mem_sigmaSet hroot hh
  have hCh : Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h) := by
    rw [hVyh]
    exact hSh.Pc_inf_centralizer_conj hroot hyhH hyhV
  have hEh : ⁅Pc M V, conjSubgroup h V⁆ =
      Pc M V ⊓ Tim79a.xOf V (hOf M V h) := by
    rw [hVyh]
    exact hSh.commutator_Pc_conj_eq hroot hyhH hyhV
  have hyCh : y ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) := by
    rw [← hC]
    exact hyC
  have hyKh : y ∉ kOf V (hOf M V h) := by
    intro hyk
    exact hyCh (hCh.symm ▸ Subgroup.mem_inf.mpr ⟨hyP, hyk⟩)
  have hc3h := hSh.sup_commutator_eq hroot hyhH hyhV hyP hyKh
  have hA1h : V ⊔ ⁅conjSubgroup h V, Subgroup.zpowers y⁆ =
      Tim79a.xOf V (hOf M V h) ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hVyh]
    exact hc3h.1
  have hplaneLePh : Tim79a.xOf V (hOf M V h) ⊓
      Subgroup.centralizer ({y} : Set G) ≤ Pc M V :=
    (hSh.xOf_inf_centralizer_le_and_card hroot hyP hyKh).1
  have hAEh : V ⊔ ⁅conjSubgroup h V, Subgroup.zpowers y⁆ =
      ⁅Pc M V, conjSubgroup h V⁆ ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hA1h, hEh]
    rw [inf_assoc, inf_eq_right.mpr hplaneLePh]
  exact hAEh

private theorem q3_plane (hS : Sec5Hyp M V) {g h : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hE : ⁅Pc M V, conjSubgroup g V⁆ = ⁅Pc M V, conjSubgroup h V⁆)
    (hC : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) =
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))
    {y : G} (hyP : y ∈ Pc M V)
    (hyC : y ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) :
    (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆ =
        V ⊔ ⁅conjSubgroup h V, Subgroup.zpowers y⁆) ∧
      (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆ =
        ⁅Pc M V, conjSubgroup g V⁆ ⊓ Subgroup.centralizer ({y} : Set G)) ∧
      Nat.card ↥(V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) = Nat.card V ^ 2 ∧
      (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) ∈ fSet M V := by
  obtain ⟨hAEg, hcardg, hf⟩ := q3_plane_g hS hg hyP hyC
  have hAEh := q3_plane_h hS hh hC hyP hyC
  exact ⟨by rw [hAEg, hAEh, hE], hAEg, hcardg, hf⟩

private structure Q3ExistsData (hS : Sec5Hyp M V) {g h : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hE : ⁅Pc M V, conjSubgroup g V⁆ = ⁅Pc M V, conjSubgroup h V⁆) {x₀ : G}
    (hx₀P : x₀ ∈ Pc M V)
    (hx₀C : x₀ ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G))
    (yh : G) : Prop where
  hC : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) =
    Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)
  hyhH : yh ∈ hOf M V h
  hVyh : conjSubgroup h V = conjSubgroup yh V
  hyhV : conjSubgroup yh V ≠ V
  hCh : Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
    Pc M V ⊓ kOf V (hOf M V h)
  hx₀Kh : x₀ ∉ kOf V (hOf M V h)
  hYcard : Nat.card ↥⁅conjSubgroup h V, Subgroup.zpowers x₀⁆ = Nat.card V
  hYleP : ⁅conjSubgroup h V, Subgroup.zpowers x₀⁆ ≤ Pc M V
  hZA : ⁅Pc M V, conjSubgroup h V⁆ ≤
    Subgroup.centralizer (conjSubgroup h V : Set G)
  hYleEh : ⁅conjSubgroup h V, Subgroup.zpowers x₀⁆ ≤
    ⁅Pc M V, conjSubgroup h V⁆

private theorem q3_exists_data (hS : Sec5Hyp M V) {g h : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hE : ⁅Pc M V, conjSubgroup g V⁆ = ⁅Pc M V, conjSubgroup h V⁆)
    (hEC : ⁅Pc M V, conjSubgroup g V⁆ ≤
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))
    {x₀ : G} (hx₀P : x₀ ∈ Pc M V)
    (hx₀C : x₀ ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G))
    {yh : G} (hyhH : yh ∈ hOf M V h)
    (hVyh : conjSubgroup h V = conjSubgroup yh V)
    (hyhV : conjSubgroup yh V ≠ V) :
    Q3ExistsData hS hg hh hE hx₀P hx₀C yh := by
  classical
  have hroot := hS.toRootHyp
  have hC : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) =
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) := by
    calc Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)
        = Pc M V ⊓ Subgroup.centralizer
            ((⁅Pc M V, conjSubgroup g V⁆ : Subgroup G) : Set G) :=
          hS.Pc_inf_centralizer_eq_commutator hg
      _ = Pc M V ⊓ Subgroup.centralizer
            ((⁅Pc M V, conjSubgroup h V⁆ : Subgroup G) : Set G) := by rw [hE]
      _ = Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) :=
          (hS.Pc_inf_centralizer_eq_commutator hh).symm
  have hx₀Ch : x₀ ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) := by
    rwa [← hC]
  have hSh := hS.shape hh
  have hCh : Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h) := by
    rw [hVyh]
    exact hSh.Pc_inf_centralizer_conj hroot hyhH hyhV
  have hx₀Kh : x₀ ∉ kOf V (hOf M V h) := by
    intro hk
    exact hx₀Ch (hCh.symm ▸ Subgroup.mem_inf.mpr ⟨hx₀P, hk⟩)
  have hc3h := hSh.sup_commutator_eq hroot hyhH hyhV hx₀P hx₀Kh
  have hYcard : Nat.card ↥⁅conjSubgroup h V, Subgroup.zpowers x₀⁆ = Nat.card V := by
    rw [hVyh]
    exact hc3h.2.2
  have hYleP : ⁅conjSubgroup h V, Subgroup.zpowers x₀⁆ ≤ Pc M V := by
    have h1 : V ⊔ ⁅conjSubgroup h V, Subgroup.zpowers x₀⁆ =
        Tim79a.xOf V (hOf M V h) ⊓ Subgroup.centralizer ({x₀} : Set G) := by
      rw [hVyh]
      exact hc3h.1
    exact (le_sup_right.trans (le_of_eq h1)).trans
      (hSh.xOf_inf_centralizer_le_and_card hroot hx₀P hx₀Kh).1
  have hZA : ⁅Pc M V, conjSubgroup h V⁆ ≤
      Subgroup.centralizer (conjSubgroup h V : Set G) := by
    rw [← hE]
    exact hEC.trans inf_le_right
  have hYleEh : ⁅conjSubgroup h V, Subgroup.zpowers x₀⁆ ≤
      ⁅Pc M V, conjSubgroup h V⁆ :=
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hx₀P)).trans
      (le_of_eq (Subgroup.commutator_comm (conjSubgroup h V) (Pc M V)))
  exact ⟨hC, hyhH, hVyh, hyhV, hCh, hx₀Kh, hYcard, hYleP, hZA, hYleEh⟩

private theorem q3_range_eq (hS : Sec5Hyp M V) {g h : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hE : ⁅Pc M V, conjSubgroup g V⁆ = ⁅Pc M V, conjSubgroup h V⁆)
    {x₀ : G} (hx₀P : x₀ ∈ Pc M V)
    (hx₀C : x₀ ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G))
    {yh : G} (d : Q3ExistsData hS hg hh hE hx₀P hx₀C yh) :
    ∃ φ : ↥(conjSubgroup h V) →* ↥⁅Pc M V, conjSubgroup h V⁆,
      (∀ a, (φ a : G) = ⁅x₀, (a : G)⁆) ∧
        φ.range = (⁅conjSubgroup h V, Subgroup.zpowers x₀⁆).subgroupOf
          ⁅Pc M V, conjSubgroup h V⁆ := by
  classical
  have hroot := hS.toRootHyp
  have hSh := hS.shape hh
  have hxA : ∀ a ∈ conjSubgroup h V, ⁅x₀, a⁆ ∈ ⁅Pc M V, conjSubgroup h V⁆ :=
    fun a ha => Subgroup.commutator_mem_commutator hx₀P ha
  let φ : ↥(conjSubgroup h V) →* ↥⁅Pc M V, conjSubgroup h V⁆ :=
    commutatorElementHom x₀ d.hZA hxA
  have hdisj : conjSubgroup h V ⊓ Subgroup.centralizer ({x₀} : Set G) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro a ha
    obtain ⟨haU, haC⟩ := Subgroup.mem_inf.mp ha
    by_contra ha1
    have hcomm : a * x₀ = x₀ * a := Subgroup.mem_centralizer_singleton_iff.mp haC
    have h1 : ⁅x₀, a⁆ = 1 :=
      (commutatorElement_eq_one_iff_mul_comm).mpr hcomm.symm
    exact d.hx₀Kh (Sec45Shape.mem_kOf_of_commutator_mem hroot hSh d.hyhH d.hyhV
      (d.hVyh ▸ haU) ha1 hx₀P (by rw [h1]; exact V.one_mem))
  have hker : φ.ker = ⊥ := by
    rw [ker_commutatorElementHom, Subgroup.subgroupOf_eq_bot, Subgroup.disjoint_def]
    intro a ha _
    rw [hdisj] at ha
    exact Subgroup.mem_bot.mp ha
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  have hrangecard : Nat.card ↥φ.range = Nat.card V := by
    calc Nat.card ↥φ.range = Nat.card ↥(conjSubgroup h V) :=
          (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
      _ = Nat.card V := card_conjSubgroup h V
  have hrange_le : φ.range ≤ (⁅conjSubgroup h V, Subgroup.zpowers x₀⁆).subgroupOf
      ⁅Pc M V, conjSubgroup h V⁆ := by
    rintro z ⟨a, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    change ⁅x₀, (a : G)⁆ ∈ ⁅conjSubgroup h V, Subgroup.zpowers x₀⁆
    rw [show ⁅x₀, (a : G)⁆ = ⁅(a : G), x₀⁆⁻¹ from
      (commutatorElement_inv (a : G) x₀).symm]
    exact (⁅conjSubgroup h V, Subgroup.zpowers x₀⁆).inv_mem
      (Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_zpowers x₀))
  have hYsubcard : Nat.card ↥((⁅conjSubgroup h V, Subgroup.zpowers x₀⁆).subgroupOf
      ⁅Pc M V, conjSubgroup h V⁆) = Nat.card V := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.hYleEh).toEquiv, d.hYcard]
  have hrange_eq : φ.range = (⁅conjSubgroup h V, Subgroup.zpowers x₀⁆).subgroupOf
      ⁅Pc M V, conjSubgroup h V⁆ := by
    refine Subgroup.eq_of_le_of_card_ge hrange_le ?_
    rw [hrangecard, hYsubcard]
  exact ⟨φ, fun a => rfl, hrange_eq⟩

private theorem q3_exists_mem_mul_commutator_mem (hS : Sec5Hyp M V) {g h : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hE : ⁅Pc M V, conjSubgroup g V⁆ = ⁅Pc M V, conjSubgroup h V⁆)
    (hEC : ⁅Pc M V, conjSubgroup g V⁆ ≤
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))
    {x₀ : G} (hx₀P : x₀ ∈ Pc M V)
    (hx₀C : x₀ ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G))
    {u : G} (huU : u ∈ conjSubgroup g V) :
    ∃ u' ∈ conjSubgroup h V, ⁅x₀, u'⁻¹ * u⁆ ∈ V := by
  classical
  have hroot := hS.toRootHyp
  obtain ⟨yh, hyhH, -, hVyh, -⟩ :=
    hroot.exists_mem_conj_eq_of_eq_sup (hS.shape hh).Pc_le (hS.shape hh).hH
  have hyhV : conjSubgroup yh V ≠ V := by
    rw [← hVyh]
    exact ne_of_mem_sigmaSet hroot hh
  let d : Q3ExistsData hS hg hh hE hx₀P hx₀C yh :=
    q3_exists_data hS hg hh hE hEC hx₀P hx₀C hyhH hVyh hyhV
  obtain ⟨φ, hφeval, hrange_eq⟩ := q3_range_eq hS hg hh hE hx₀P hx₀C d
  obtain ⟨hAx_eq, hAx_E, hAx_card, -⟩ := q3_plane hS hg hh hE d.hC hx₀P hx₀C
  have hxu : ⁅x₀, u⁆ ∈ V ⊔ ⁅conjSubgroup h V, Subgroup.zpowers x₀⁆ := by
    have h1 : ⁅u, x₀⁆ ∈ V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆ :=
      Subgroup.mem_sup_right
        (Subgroup.commutator_mem_commutator huU (Subgroup.mem_zpowers x₀))
    rw [hAx_eq] at h1
    rw [show ⁅x₀, u⁆ = ⁅u, x₀⁆⁻¹ from (commutatorElement_inv u x₀).symm]
    exact (V ⊔ ⁅conjSubgroup h V, Subgroup.zpowers x₀⁆).inv_mem h1
  have hVP : V ≤ Subgroup.centralizer (Pc M V : Set G) := by
    rw [hroot.toHyp.centralizer_Pc]
  have hcomm : ∀ a ∈ V, ∀ b ∈ ⁅conjSubgroup h V, Subgroup.zpowers x₀⁆,
      a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hVP ha) b (d.hYleP hb)).symm
  obtain ⟨v, hvV, y, hyY, hxy⟩ := exists_mul_of_mem_sup_of_commute hcomm hxu
  have hyRange : (⟨y, d.hYleEh hyY⟩ : ↥⁅Pc M V, conjSubgroup h V⁆) ∈ φ.range := by
    rw [hrange_eq]
    exact Subgroup.mem_subgroupOf.mpr hyY
  obtain ⟨u', hu'eq⟩ := MonoidHom.mem_range.mp hyRange
  have hφu' : ⁅x₀, (u' : G)⁆ = y := by
    have h := congrArg (fun z : ↥⁅Pc M V, conjSubgroup h V⁆ => (z : G)) hu'eq
    rw [hφeval u'] at h
    exact h
  have hcomm_u'y : (u' : G) * y = y * (u' : G) :=
    Subgroup.mem_centralizer_iff.mp (d.hZA (d.hYleEh hyY)) (u' : G) u'.2
  have hφinv : ⁅x₀, (u' : G)⁻¹⁆ = y⁻¹ := by
    rw [commutatorElement_inv_right,
      show ⁅(u' : G), x₀⁆ = y⁻¹ from by
        rw [← commutatorElement_inv x₀ (u' : G), hφu']]
    have hyinv : y⁻¹ * (u' : G) = (u' : G) * y⁻¹ :=
      (commute_iff_eq y⁻¹ (u' : G)).mp
        ((commute_iff_eq (u' : G) y).mpr hcomm_u'y).symm.inv_left
    calc (u' : G)⁻¹ * y⁻¹ * (u' : G) = (u' : G)⁻¹ * (y⁻¹ * (u' : G)) := by group
      _ = (u' : G)⁻¹ * ((u' : G) * y⁻¹) := by rw [hyinv]
      _ = y⁻¹ := by group
  have hxuEh : ⁅x₀, u⁆ ∈ ⁅Pc M V, conjSubgroup h V⁆ := by
    rw [← hE]
    exact Subgroup.commutator_mem_commutator hx₀P huU
  have hcomm_u'e : (u' : G) * ⁅x₀, u⁆ = ⁅x₀, u⁆ * (u' : G) :=
    Subgroup.mem_centralizer_iff.mp (d.hZA hxuEh) (u' : G) u'.2
  have hconj : (u' : G)⁻¹ * ⁅x₀, u⁆ * (u' : G) = ⁅x₀, u⁆ := by
    calc (u' : G)⁻¹ * ⁅x₀, u⁆ * (u' : G) =
        (u' : G)⁻¹ * (⁅x₀, u⁆ * (u' : G)) := by group
      _ = (u' : G)⁻¹ * ((u' : G) * ⁅x₀, u⁆) := by rw [hcomm_u'e]
      _ = ⁅x₀, u⁆ := by group
  refine ⟨u', u'.2, ?_⟩
  have hb_eq : ⁅x₀, (u' : G)⁻¹ * u⁆ = y⁻¹ * (v * y) := by
    rw [commutatorElement_mul_right_eq_mul_conj, hφinv, inv_inv]
    calc y⁻¹ * (u' : G)⁻¹ * ⁅x₀, u⁆ * (u' : G) =
        y⁻¹ * ((u' : G)⁻¹ * ⁅x₀, u⁆ * (u' : G)) := by group
      _ = y⁻¹ * ⁅x₀, u⁆ := by rw [hconj]
      _ = y⁻¹ * (v * y) := by rw [← hxy]
  rw [hb_eq]
  have hyv : y * v = v * y :=
    Subgroup.mem_centralizer_iff.mp (hVP hvV) y (d.hYleP hyY)
  rw [← hyv]
  convert hvV using 1
  group

private structure Q3RigidityData (M V : Subgroup G) (g h x₀ u u' b : G) : Prop where
  hS : Sec5Hyp M V
  hg : conjSubgroup g V ∈ sigmaSet M V
  hh : conjSubgroup h V ∈ sigmaSet M V
  hE : ⁅Pc M V, conjSubgroup g V⁆ = ⁅Pc M V, conjSubgroup h V⁆
  hEC : ⁅Pc M V, conjSubgroup g V⁆ ≤
    Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)
  hx₀P : x₀ ∈ Pc M V
  hx₀C : x₀ ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)
  huU : u ∈ conjSubgroup g V
  hu'U : u' ∈ conjSubgroup h V
  hb : b = u'⁻¹ * u
  hbx : ⁅x₀, b⁆ ∈ V
  hC : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) =
    Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)
  hCEg : Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, conjSubgroup g V⁆ : Subgroup G) : Set G) =
    Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)
  hZA : ⁅Pc M V, conjSubgroup h V⁆ ≤
    Subgroup.centralizer (conjSubgroup h V : Set G)
  hVP : V ≤ Subgroup.centralizer (Pc M V : Set G)
  hPP : ⁅Pc M V, Pc M V⁆ = V
  hVN : Pc M V ≤ Subgroup.normalizer (V : Set G)
  hbC : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤
    Subgroup.centralizer ({b} : Set G)
  hAx_eq : V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆ =
    V ⊔ ⁅conjSubgroup h V, Subgroup.zpowers x₀⁆
  hAx_E : V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆ =
    ⁅Pc M V, conjSubgroup g V⁆ ⊓ Subgroup.centralizer ({x₀} : Set G)
  hAx_card : Nat.card ↥(V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆) =
    Nat.card V ^ 2

private theorem q3_rigidity_data (hS : Sec5Hyp M V) {g h : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hE : ⁅Pc M V, conjSubgroup g V⁆ = ⁅Pc M V, conjSubgroup h V⁆)
    (hEC : ⁅Pc M V, conjSubgroup g V⁆ ≤
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))
    {x₀ : G} (hx₀P : x₀ ∈ Pc M V)
    (hx₀C : x₀ ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G))
    {u u' : G} (huU : u ∈ conjSubgroup g V) (hu'U : u' ∈ conjSubgroup h V)
    {b : G} (hb : b = u'⁻¹ * u) (hbx : ⁅x₀, b⁆ ∈ V) :
    Q3RigidityData M V g h x₀ u u' b := by
  classical
  have hroot := hS.toRootHyp
  have hC : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) =
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) := by
    calc Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)
        = Pc M V ⊓ Subgroup.centralizer
            ((⁅Pc M V, conjSubgroup g V⁆ : Subgroup G) : Set G) :=
          hS.Pc_inf_centralizer_eq_commutator hg
      _ = Pc M V ⊓ Subgroup.centralizer
            ((⁅Pc M V, conjSubgroup h V⁆ : Subgroup G) : Set G) := by rw [hE]
      _ = Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) :=
          (hS.Pc_inf_centralizer_eq_commutator hh).symm
  have hCEg : Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, conjSubgroup g V⁆ : Subgroup G) : Set G) =
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) :=
    (hS.Pc_inf_centralizer_eq_commutator hg).symm
  have hZA : ⁅Pc M V, conjSubgroup h V⁆ ≤
      Subgroup.centralizer (conjSubgroup h V : Set G) := by
    rw [← hE]
    exact hEC.trans inf_le_right
  have hVP : V ≤ Subgroup.centralizer (Pc M V : Set G) := by
    rw [hroot.toHyp.centralizer_Pc]
  have hPP : ⁅Pc M V, Pc M V⁆ = V := (hS.shape hg).commutator_Pc hroot
  have hVN : Pc M V ≤ Subgroup.normalizer (V : Set G) :=
    hroot.toHyp.Pc_le_M.trans hroot.toHyp.le_normalizer
  have hbC : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤
      Subgroup.centralizer ({b} : Set G) := by
    intro c hc
    have hcP : c ∈ Pc M V := (Subgroup.mem_inf.mp hc).1
    have hcu : c * u = u * c :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 u huU).symm
    have hcCh : c ∈ Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) := hC ▸ hc
    have hcu' : c * u' = u' * c :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcCh).2 u' hu'U).symm
    rw [Subgroup.mem_centralizer_singleton_iff, hb]
    have hcu'inv : c * u'⁻¹ = u'⁻¹ * c :=
      (commute_iff_eq c u'⁻¹).mp ((commute_iff_eq c u').mpr hcu').inv_right
    calc c * (u'⁻¹ * u) = (c * u'⁻¹) * u := by group
      _ = (u'⁻¹ * c) * u := by rw [hcu'inv]
      _ = u'⁻¹ * (c * u) := by group
      _ = u'⁻¹ * (u * c) := by rw [hcu]
      _ = (u'⁻¹ * u) * c := by group
  obtain ⟨hAx_eq, hAx_E, hAx_card, -⟩ :=
    q3_plane hS hg hh hE hC hx₀P hx₀C
  exact ⟨hS, hg, hh, hE, hEC, hx₀P, hx₀C, huU, hu'U, hb, hbx,
    hC, hCEg, hZA, hVP, hPP, hVN, hbC, hAx_eq, hAx_E, hAx_card⟩

private theorem q3_centralizer_le_centralizer_plane {g h x₀ u u' b : G}
    (d : Q3RigidityData M V g h x₀ u u' b) :
    Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤
      Pc M V ⊓ Subgroup.centralizer
        ((V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆ : Subgroup G) : Set G) := by
  intro c hc
  have hcP : c ∈ Pc M V := (Subgroup.mem_inf.mp hc).1
  have hcE : c ∈ Subgroup.centralizer
      ((⁅Pc M V, conjSubgroup g V⁆ : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp (d.hCEg ▸ hc)).2
  refine Subgroup.mem_inf.mpr ⟨hcP, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have haE : a ∈ ⁅Pc M V, conjSubgroup g V⁆ := by
    rw [d.hAx_E] at ha
    exact (Subgroup.mem_inf.mp ha).1
  exact Subgroup.mem_centralizer_iff.mp hcE a haE

private theorem q3_centralizer_plane_lt {g h x₀ u u' b : G}
    (d : Q3RigidityData M V g h x₀ u u' b) :
    Pc M V ⊓ Subgroup.centralizer
        ((V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆ : Subgroup G) : Set G) <
      Pc M V := by
  refine lt_of_le_of_ne inf_le_left ?_
  intro hSP
  have hAx_le_C : (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆) ≤
      Subgroup.centralizer (Pc M V : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpS : p ∈ Pc M V ⊓ Subgroup.centralizer
        ((V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆ : Subgroup G) : Set G) := by
      rw [hSP]
      exact hp
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hpS).2 a ha).symm
  have hZP : Pc M V ⊓ Subgroup.centralizer (Pc M V : Set G) = V := by
    rw [d.hS.toRootHyp.toHyp.centralizer_Pc]
    exact le_antisymm inf_le_right
      (le_inf d.hS.toRootHyp.toHyp.le_Pc le_rfl)
  have hAxP : (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆) ≤ Pc M V := by
    rw [d.hAx_E]
    intro x hx
    exact d.hS.commutator_le_Pc d.hg (Subgroup.mem_inf.mp hx).1
  have hAxV : (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆) ≤ V := by
    have h := le_inf hAxP hAx_le_C
    rwa [hZP] at h
  have hcard_le : Nat.card V ^ 2 ≤ Nat.card V := by
    rw [← d.hAx_card]
    exact Subgroup.card_le_of_le hAxV
  have h4 := d.hS.toRootHyp.four_le_card
  nlinarith

private theorem q3_commutator_mem_V_of_mul_mem_centralizer {g h x₀ u u' b : G}
    (d : Q3RigidityData M V g h x₀ u u' b) {y : G}
    (hzC : x₀ * y ∈ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) :
    ⁅y, b⁆ ∈ V := by
  have hroot := d.hS.toRootHyp
  have hz_cen : x₀ * y ∈ Subgroup.centralizer ({b} : Set G) := d.hbC hzC
  have hzb : ⁅x₀ * y, b⁆ = 1 :=
    (commutatorElement_eq_one_iff_mul_comm).mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hz_cen)
  have hx0inv : ⁅x₀⁻¹, b⁆ ∈ V := by
    rw [commutatorElement_inv_left,
      show ⁅b, x₀⁆ = ⁅x₀, b⁆⁻¹ from (commutatorElement_inv x₀ b).symm]
    simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      (hroot.toHyp.le_normalizer (M.inv_mem (hroot.toHyp.Pc_le_M d.hx₀P))) _).mp
      (V.inv_mem d.hbx)
  have hyb : ⁅y, b⁆ ∈ V := by
    have hy_eq : y = x₀⁻¹ * (x₀ * y) := by group
    rw [hy_eq, commutatorElement_mul_left_eq_conj_mul, hzb]
    simpa using hx0inv
  exact hyb

private theorem q3_planes_ne_of_not_mem_centralizer_plane {g h x₀ u u' b : G}
    (d : Q3RigidityData M V g h x₀ u u' b) {y : G} (hyP : y ∈ Pc M V)
    (hyS : y ∉ Pc M V ⊓ Subgroup.centralizer
      ((V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆ : Subgroup G) : Set G))
    (hzC : x₀ * y ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) :
    (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) ≠
      (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆) := by
  have hyC : y ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) :=
    fun h => hyS (q3_centralizer_le_centralizer_plane d h)
  obtain ⟨hAy_eq, hAy_E, hAy_card, -⟩ :=
    q3_plane d.hS d.hg d.hh d.hE d.hC hyP hyC
  have hzP : x₀ * y ∈ Pc M V := (Pc M V).mul_mem d.hx₀P hyP
  obtain ⟨hAz_eq, hAz_E, hAz_card, -⟩ :=
    q3_plane d.hS d.hg d.hh d.hE d.hC hzP hzC
  have hAyC : (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) ≤
      Subgroup.centralizer ({y} : Set G) := by
    rw [hAy_E]
    exact inf_le_right
  have hAzC : (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆) ≤
      Subgroup.centralizer ({x₀ * y} : Set G) := by
    rw [hAz_E]
    exact inf_le_right
  intro heq
  have hcen : (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) ≤
      Subgroup.centralizer ({x₀} : Set G) := by
    intro a ha
    have hay : a * y = y * a :=
      Subgroup.mem_centralizer_singleton_iff.mp (hAyC ha)
    have haz : a * (x₀ * y) = (x₀ * y) * a := by
      have ha' : a ∈ V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆ := by
        rw [← heq]
        exact ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hAzC ha')
    have hx0 : Commute a x₀ := by
      have hx0eq : x₀ = (x₀ * y) * y⁻¹ := by group
      rw [hx0eq]
      exact ((commute_iff_eq a (x₀ * y)).mpr haz).mul_right
        ((commute_iff_eq a y).mpr hay).inv_right
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((commute_iff_eq a x₀).mp hx0)
  have hAle : (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) ≤
      V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆ := by
    rw [d.hAx_E]
    exact le_inf (hAy_E ▸ inf_le_left) hcen
  have hAeq : (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) =
      V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆ :=
    Subgroup.eq_of_le_of_card_ge hAle (by rw [d.hAx_card, hAy_card])
  have hyS' : y ∈ Pc M V ⊓ Subgroup.centralizer
      ((V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆ : Subgroup G) : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hyP, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haAy : a ∈ V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆ := by
      rw [hAeq]
      exact ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hAyC haAy)
  exact hyS hyS'

private theorem q3_commutators_mem_planes {g h x₀ u u' b : G}
    (d : Q3RigidityData M V g h x₀ u u' b) {y : G} (hyP : y ∈ Pc M V)
    (hyS : y ∉ Pc M V ⊓ Subgroup.centralizer
      ((V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆ : Subgroup G) : Set G))
    (hzC : x₀ * y ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) :
    (⁅y, b⁆ ∈ V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) ∧
      (⁅x₀ * y, b⁆ ∈ V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆) := by
  have hyC : y ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) :=
    fun h => hyS (q3_centralizer_le_centralizer_plane d h)
  obtain ⟨hAy_eq, hAy_E, -, -⟩ :=
    q3_plane d.hS d.hg d.hh d.hE d.hC hyP hyC
  have hzP : x₀ * y ∈ Pc M V := (Pc M V).mul_mem d.hx₀P hyP
  obtain ⟨hAz_eq, hAz_E, -, -⟩ :=
    q3_plane d.hS d.hg d.hh d.hE d.hC hzP hzC
  have hconj_E : ∀ e ∈ ⁅Pc M V, conjSubgroup h V⁆,
      (u' : G)⁻¹ * e * (u' : G) = e := by
    intro e he
    have hcomm : (u' : G) * e = e * (u' : G) :=
      Subgroup.mem_centralizer_iff.mp (d.hZA he) (u' : G) d.hu'U
    calc (u' : G)⁻¹ * e * (u' : G) =
        (u' : G)⁻¹ * (e * (u' : G)) := by group
      _ = (u' : G)⁻¹ * ((u' : G) * e) := by rw [hcomm]
      _ = e := by group
  have hyuE : ⁅y, u⁆ ∈ ⁅Pc M V, conjSubgroup h V⁆ := by
    rw [← d.hE]
    exact Subgroup.commutator_mem_commutator hyP d.huU
  have hconj_y : (u' : G)⁻¹ * ⁅y, u⁆ * (u' : G) = ⁅y, u⁆ := hconj_E _ hyuE
  have hyb_Ay : ⁅y, b⁆ ∈ V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆ := by
    rw [d.hb, commutatorElement_mul_right_eq_mul_conj, inv_inv]
    have hre : ⁅y, (u' : G)⁻¹⁆ * (u' : G)⁻¹ * ⁅y, u⁆ * (u' : G) =
        ⁅y, (u' : G)⁻¹⁆ * ((u' : G)⁻¹ * ⁅y, u⁆ * (u' : G)) := by group
    rw [hre, hconj_y]
    refine (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆).mul_mem ?_ ?_
    · rw [show ⁅y, (u' : G)⁻¹⁆ = ⁅(u' : G)⁻¹, y⁆⁻¹ from
        (commutatorElement_inv (u' : G)⁻¹ y).symm]
      refine (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆).inv_mem ?_
      rw [hAy_eq]
      exact Subgroup.mem_sup_right
        (Subgroup.commutator_mem_commutator ((conjSubgroup h V).inv_mem d.hu'U)
          (Subgroup.mem_zpowers y))
    · rw [show ⁅y, u⁆ = ⁅u, y⁆⁻¹ from (commutatorElement_inv u y).symm]
      exact (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆).inv_mem
        (Subgroup.mem_sup_right
          (Subgroup.commutator_mem_commutator d.huU (Subgroup.mem_zpowers y)))
  have hzb_Az : ⁅x₀ * y, b⁆ ∈
      V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆ := by
    rw [d.hb, commutatorElement_mul_right_eq_mul_conj, inv_inv]
    have hre : ⁅x₀ * y, (u' : G)⁻¹⁆ * (u' : G)⁻¹ * ⁅x₀ * y, u⁆ * (u' : G) =
        ⁅x₀ * y, (u' : G)⁻¹⁆ *
          ((u' : G)⁻¹ * ⁅x₀ * y, u⁆ * (u' : G)) := by group
    have hzuE : ⁅x₀ * y, u⁆ ∈ ⁅Pc M V, conjSubgroup h V⁆ := by
      rw [← d.hE]
      exact Subgroup.commutator_mem_commutator hzP d.huU
    rw [hre, hconj_E _ hzuE]
    refine (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆).mul_mem ?_ ?_
    · rw [show ⁅x₀ * y, (u' : G)⁻¹⁆ = ⁅(u' : G)⁻¹, x₀ * y⁆⁻¹ from
        (commutatorElement_inv (u' : G)⁻¹ (x₀ * y)).symm]
      refine (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆).inv_mem ?_
      rw [hAz_eq]
      exact Subgroup.mem_sup_right
        (Subgroup.commutator_mem_commutator ((conjSubgroup h V).inv_mem d.hu'U)
          (Subgroup.mem_zpowers (x₀ * y)))
    · rw [show ⁅x₀ * y, u⁆ = ⁅u, x₀ * y⁆⁻¹ from
        (commutatorElement_inv u (x₀ * y)).symm]
      exact (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆).inv_mem
        (Subgroup.mem_sup_right
          (Subgroup.commutator_mem_commutator d.huU (Subgroup.mem_zpowers (x₀ * y))))
  exact ⟨hyb_Ay, hzb_Az⟩

private theorem q3_commutator_mem_V_of_not_mem_centralizer_plane {g h x₀ u u' b : G}
    (d : Q3RigidityData M V g h x₀ u u' b) {y : G} (hyP : y ∈ Pc M V)
    (hyS : y ∉ Pc M V ⊓ Subgroup.centralizer
      ((V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆ : Subgroup G) : Set G))
    (hzC : x₀ * y ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) :
    ⁅y, b⁆ ∈ V := by
  have hyC : y ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) :=
    fun h => hyS (q3_centralizer_le_centralizer_plane d h)
  have hAne := q3_planes_ne_of_not_mem_centralizer_plane d hyP hyS hzC
  obtain ⟨hyb_Ay, hzb_Az⟩ := q3_commutators_mem_planes d hyP hyS hzC
  have hzP : x₀ * y ∈ Pc M V := (Pc M V).mul_mem d.hx₀P hyP
  obtain ⟨-, hAy_E, -, hAy_f⟩ := q3_plane d.hS d.hg d.hh d.hE d.hC hyP hyC
  obtain ⟨-, hAz_E, -, hAz_f⟩ := q3_plane d.hS d.hg d.hh d.hE d.hC hzP hzC
  have hcap : (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) ⊓
      (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆) = V := by
    rcases d.hS.stmt51e (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) hAy_f
      (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆) hAz_f with heq | hcap
    · exact absurd heq hAne
    · exact hcap
  have hybP : ⁅y, b⁆ ∈ Pc M V :=
    d.hS.commutator_le_Pc d.hg (Subgroup.mem_inf.mp (hAy_E ▸ hyb_Ay)).1
  have hxx : ⁅x₀, ⁅y, b⁆⁆ ∈ V := by
    rw [← d.hPP]
    exact Subgroup.commutator_mem_commutator d.hx₀P hybP
  have hconj_e : x₀ * ⁅y, b⁆ * x₀⁻¹ = ⁅x₀, ⁅y, b⁆⁆ * ⁅y, b⁆ := by
    rw [commutatorElement_def]
    group
  have hz_eq : ⁅x₀ * y, b⁆ =
      (⁅x₀, ⁅y, b⁆⁆ * ⁅y, b⁆) * ⁅x₀, b⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, hconj_e]
  have hq_comm : ⁅x₀, ⁅y, b⁆⁆ * ⁅y, b⁆ = ⁅y, b⁆ * ⁅x₀, ⁅y, b⁆⁆ :=
    (Subgroup.mem_centralizer_iff.mp (d.hVP hxx) ⁅y, b⁆ hybP).symm
  have hp_comm : ⁅x₀, b⁆ * ⁅y, b⁆ = ⁅y, b⁆ * ⁅x₀, b⁆ :=
    (Subgroup.mem_centralizer_iff.mp (d.hVP d.hbx) ⁅y, b⁆ hybP).symm
  have hpqV : ⁅x₀, ⁅y, b⁆⁆ * ⁅x₀, b⁆ ∈ V := V.mul_mem hxx d.hbx
  have hyb_Az : ⁅y, b⁆ ∈ V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆ := by
    have hz_eq' : ⁅x₀ * y, b⁆ =
        ⁅y, b⁆ * (⁅x₀, ⁅y, b⁆⁆ * ⁅x₀, b⁆) := by
      rw [hz_eq]
      calc ⁅x₀, ⁅y, b⁆⁆ * ⁅y, b⁆ * ⁅x₀, b⁆ =
          (⁅x₀, ⁅y, b⁆⁆ * ⁅y, b⁆) * ⁅x₀, b⁆ := by group
        _ = (⁅y, b⁆ * ⁅x₀, ⁅y, b⁆⁆) * ⁅x₀, b⁆ := by rw [hq_comm]
        _ = ⁅y, b⁆ * (⁅x₀, ⁅y, b⁆⁆ * ⁅x₀, b⁆) := by group
    have h1 : ⁅y, b⁆ = ⁅x₀ * y, b⁆ * (⁅x₀, ⁅y, b⁆⁆ * ⁅x₀, b⁆)⁻¹ := by
      rw [hz_eq']
      group
    rw [h1]
    exact (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆).mul_mem hzb_Az
      ((V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆).inv_mem
        (Subgroup.mem_sup_left hpqV))
  have hybV : ⁅y, b⁆ ∈ V := by
    have hmem : ⁅y, b⁆ ∈ (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers y⁆) ⊓
        (V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers (x₀ * y)⁆) :=
      Subgroup.mem_inf.mpr ⟨hyb_Ay, hyb_Az⟩
    rwa [hcap] at hmem
  exact hybV

private theorem q3_commutator_mem_V (hS : Sec5Hyp M V) {g h : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hE : ⁅Pc M V, conjSubgroup g V⁆ = ⁅Pc M V, conjSubgroup h V⁆)
    (hEC : ⁅Pc M V, conjSubgroup g V⁆ ≤
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G))
    {x₀ : G} (hx₀P : x₀ ∈ Pc M V)
    (hx₀C : x₀ ∉ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G))
    {u u' : G} (huU : u ∈ conjSubgroup g V) (hu'U : u' ∈ conjSubgroup h V)
    {b : G} (hb : b = u'⁻¹ * u) (hbx : ⁅x₀, b⁆ ∈ V) :
    ∀ p ∈ Pc M V, ⁅p, b⁆ ∈ V := by
  classical
  let d : Q3RigidityData M V g h x₀ u u' b :=
    q3_rigidity_data hS hg hh hE hEC hx₀P hx₀C huU hu'U hb hbx
  let S0 : Subgroup G := Pc M V ⊓ Subgroup.centralizer
    ((V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x₀⁆ : Subgroup G) : Set G)
  let T0 : Subgroup G := commMemSubgroup (Pc M V) V d.hVN b
  have hC_le_S : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤ S0 :=
    q3_centralizer_le_centralizer_plane d
  have hS_lt : S0 < Pc M V := q3_centralizer_plane_lt d
  have hT : ∀ y ∈ Pc M V, y ∉ S0 → y ∈ T0 := by
    intro y hyP hyS
    have hybV : ⁅y, b⁆ ∈ V := by
      by_cases hzC : x₀ * y ∈ Pc M V ⊓
          Subgroup.centralizer (conjSubgroup g V : Set G)
      · exact q3_commutator_mem_V_of_mul_mem_centralizer d hzC
      · exact q3_commutator_mem_V_of_not_mem_centralizer_plane d hyP hyS hzC
    exact (mem_commMemSubgroup d.hVN b y).mpr ⟨hyP, hybV⟩
  have hsub : (Pc M V : Set G) ⊆ (T0 : Set G) ∪ (S0 : Set G) := by
    intro y hyP
    by_cases hyS : y ∈ S0
    · exact Or.inr hyS
    · exact Or.inl (hT y hyP hyS)
  have hPT : Pc M V ≤ T0 := by
    have hPS : Pc M V ≤ T0 ∨ Pc M V ≤ S0 :=
      Iff.mp (SubgroupClass.subset_union (H := Pc M V) (K := T0) (L := S0)) hsub
    rcases hPS with h | h
    · exact h
    · exfalso
      exact not_lt_of_ge h hS_lt
  intro p hp
  exact (mem_commMemSubgroup d.hVN b p).mp (hPT hp) |>.2

private theorem q3_equal_data (hS : Sec5Hyp M V) {g h : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hle : ⁅Pc M V, conjSubgroup g V⁆ ≤ ⁅Pc M V, conjSubgroup h V⁆) :
    (⁅Pc M V, conjSubgroup g V⁆ = ⁅Pc M V, conjSubgroup h V⁆) ∧
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) =
        Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) ∧
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) < Pc M V) := by
  classical
  have hroot := hS.toRootHyp
  have hE : ⁅Pc M V, conjSubgroup g V⁆ = ⁅Pc M V, conjSubgroup h V⁆ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hS.card_commutator_Pc hh, hS.card_commutator_Pc hg]
  have hC : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) =
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) := by
    calc Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)
        = Pc M V ⊓ Subgroup.centralizer
            ((⁅Pc M V, conjSubgroup g V⁆ : Subgroup G) : Set G) :=
          hS.Pc_inf_centralizer_eq_commutator hg
      _ = Pc M V ⊓ Subgroup.centralizer
            ((⁅Pc M V, conjSubgroup h V⁆ : Subgroup G) : Set G) := by rw [hE]
      _ = Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) :=
          (hS.Pc_inf_centralizer_eq_commutator hh).symm
  have hC_lt : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) < Pc M V := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hCP
    have hcard := hS.card_Pc_inf_centralizer hg
    rw [hCP] at hcard
    have hpos : 0 < Nat.card ↥(Pc M V) :=
      Finite.card_pos_iff.mpr ⟨⟨1, (Pc M V).one_mem⟩⟩
    have hq2 : Nat.card V ^ 2 = 1 :=
      Nat.eq_of_mul_eq_mul_left hpos (by simpa using hcard)
    have h4 := hroot.four_le_card
    nlinarith
  exact ⟨hE, hC, hC_lt⟩

private theorem q3_hOf_eq (hS : Sec5Hyp M V) {g h : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V)
    (hle : ⁅Pc M V, conjSubgroup g V⁆ ≤ ⁅Pc M V, conjSubgroup h V⁆)
    (hEC : ⁅Pc M V, conjSubgroup g V⁆ ≤
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)) :
    hOf M V g = hOf M V h := by
  classical
  have hroot := hS.toRootHyp
  obtain ⟨hE, hC, hC_lt⟩ := q3_equal_data hS hg hh hle
  obtain ⟨x₀, hx₀P, hx₀C⟩ := SetLike.exists_of_lt hC_lt
  have hUne : conjSubgroup g V ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card V = 1 := by
      rw [← card_conjSubgroup g V, hbot]
      simp
    have h4 := hroot.four_le_card
    omega
  obtain ⟨⟨u, huU⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨u', hu'U, hbu⟩ :=
    q3_exists_mem_mul_commutator_mem hS hg hh hE hEC hx₀P hx₀C huU
  let b : G := u'⁻¹ * u
  have hb_eq : b = u'⁻¹ * u := rfl
  have huM : u ∈ M := (hS.le_M_of_mem_sigmaSet hg).1 huU
  have hu'M : u' ∈ M := (hS.le_M_of_mem_sigmaSet hh).1 hu'U
  have hbM : b ∈ M := M.mul_mem (M.inv_mem hu'M) huM
  have huV : u ∈ Subgroup.centralizer (V : Set G) := (hS.le_M_of_mem_sigmaSet hg).2 huU
  have hu'V : u' ∈ Subgroup.centralizer (V : Set G) := (hS.le_M_of_mem_sigmaSet hh).2 hu'U
  have hbV : b ∈ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro v hv
    have hu'c : Commute u' v :=
      (commute_iff_eq u' v).mpr (Subgroup.mem_centralizer_iff.mp hu'V v hv).symm
    have huc : Commute u v :=
      (commute_iff_eq u v).mpr (Subgroup.mem_centralizer_iff.mp huV v hv).symm
    exact ((commute_iff_eq (u'⁻¹ * u) v).mp (hu'c.inv_left.mul_left huc)).symm
  have hbP : ∀ p ∈ Pc M V, ⁅p, b⁆ ∈ V :=
    q3_commutator_mem_V hS hg hh hE hEC hx₀P hx₀C huU hu'U hb_eq hbu
  have hbPc : b ∈ Pc M V :=
    Sec45Shape.mem_Pc_of_commutator_mem hroot (hS.shape hg) hbM hbV hbP
  have hu'1 : u' ≠ 1 := by
    intro h1
    have huP : u ∈ Pc M V := by simpa [hb_eq, h1] using hbPc
    have hmem : u ∈ conjSubgroup g V ⊓ Pc M V := Subgroup.mem_inf.mpr ⟨huU, huP⟩
    rw [hS.inf_Pc_eq_bot hg] at hmem
    exact hu1' (Subgroup.mem_bot.mp hmem)
  have hu'_eq : u' = u * b⁻¹ := by
    rw [hb_eq]
    group
  have hmeet : conjSubgroup h V ⊓ (conjSubgroup g V ⊔ Pc M V) ≠ ⊥ := by
    intro hbot
    have hu'_mem : u' ∈ conjSubgroup h V ⊓ (conjSubgroup g V ⊔ Pc M V) := by
      refine Subgroup.mem_inf.mpr ⟨hu'U, ?_⟩
      rw [hu'_eq]
      exact Subgroup.mul_mem_sup huU ((Pc M V).inv_mem hbPc)
    rw [hbot] at hu'_mem
    exact hu'1 (Subgroup.mem_bot.mp hu'_mem)
  obtain ⟨p, hpP, hUh⟩ := hS.stmt55 (conjSubgroup g V) hg (conjSubgroup h V) hh hmeet
  exact (hroot.toHyp.hOf_eq_of_conjSubgroup_eq_conj hpP hUh).symm

private theorem q3_trichotomy (hS : Sec5Hyp M V) {g h : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) (hh : conjSubgroup h V ∈ sigmaSet M V) :
    (⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆ = V) ∨
      (⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆ ∈ fSet M V) ∨
      (⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆ =
        ⁅Pc M V, conjSubgroup g V⁆) := by
  classical
  refine hS.eq_V_or_mem_fSet_or_eq_commutator hg
    (X := ⁅Pc M V, conjSubgroup g V⁆ ⊓ ⁅Pc M V, conjSubgroup h V⁆) ?_ inf_le_left ?_
  · exact le_inf (hS.V_le_commutator hg) (hS.V_le_commutator hh)
  · intro x hx hxV
    obtain ⟨A, hA, hxA, hAE⟩ := hS.stmt52a (conjSubgroup g V) hg x hx.1
    obtain ⟨B, hB, hxB, hBE⟩ := hS.stmt52a (conjSubgroup h V) hh x hx.2
    rcases hS.stmt51e A hA B hB with hAB | hcap
    · exact ⟨A, hA, hxA, le_inf hAE (hAB.symm ▸ hBE)⟩
    · exfalso
      exact hxV (hcap ▸ Subgroup.mem_inf.mpr ⟨hxA, hxB⟩)

theorem stmt58 (hS : Sec5Hyp M V) (h57 : Sec5.Stmt57 M V) : Sec5.Stmt58 M V := by
  intro g h hh hg hc
  have hle_g : ⁅Pc M V, conjSubgroup g V⁆ ≤
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) :=
    h57.le_of_commute hg hh hc
  have hc' : ⁅conjSubgroup h V, conjSubgroup g V⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm]
  have hle_h : ⁅Pc M V, conjSubgroup h V⁆ ≤
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) :=
    h57.le_of_commute hh hg hc'
  have hKFg : ∀ u ∈ conjSubgroup g V,
      (∀ z ∈ hOf M V h, ⁅u, z⁆ ∈ kOf V (hOf M V h)) ∧
        u ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V h) : Set G) :=
    hS.forall_commutator_mem_kOf_of_le hh hg hc hle_g
  rcases q3_trichotomy hS hg hh with hV | hF | hE
  · right
    exact hS.Pc_eq_sup_centralizer_of_inf_eq_V hg hh hle_h hKFg hV
  · exact (hS.fSet_inf_eq_V_impossible hS.stmt51d hg hh hKFg hF).elim
  · left
    exact q3_hOf_eq hS hg hh (inf_eq_left.mp hE) hle_g

end Sec5Hyp

end CFSG.RankThree.GF2n.Tim81

end
