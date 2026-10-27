module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432CoverIndex
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzFuse

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint
open CFSG.Sporadic.SuzOddCore (suzM suzM_card_chain suzEquivM outer_carrier_suz)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.TabSuzFuse
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.RankThree.Native
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem suz_transfer_pow {G : Type} [Group G] {k h d c s : G} {e : ℕ} (hdc : h * d * h⁻¹ = c)
    (hf : k * c ^ e * k⁻¹ = s) : k * h * d ^ e * (k * h)⁻¹ = s := by
  subst hdc
  subst hf
  rw [conj_pow]
  group

theorem suz_conj_of_common {c : Equiv.Perm (Fin 1782)}
    {a b : Fin 5 → ZMod 3}
    (h1 : ∃ h ∈ suzM, h * φ (Multiplicative.ofAdd a) * h⁻¹ = c)
    (h2 : ∃ h ∈ suzM, h * φ (Multiplicative.ofAdd b) * h⁻¹ = c) :
    ∃ g ∈ suzM, g * φ (Multiplicative.ofAdd a) * g⁻¹ = φ (Multiplicative.ofAdd b) := by
  obtain ⟨h1', hh1, e1⟩ := h1
  obtain ⟨h2', hh2, e2⟩ := h2
  refine ⟨h2'⁻¹ * h1', suzM.mul_mem (suzM.inv_mem hh2) hh1, ?_⟩
  have hb : φ (Multiplicative.ofAdd b) = h2'⁻¹ * c * h2' := by
    rw [← e2]
    group
  rw [hb, ← e1]
  group

theorem suz_orderOf_three {x : ↥suzM} (h3 : (x : Equiv.Perm (Fin 1782)) ^ 3 = 1)
    (h1 : (x : Equiv.Perm (Fin 1782)) ≠ 1) : orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_prime h3 h1

theorem suz_label_one : fuseCls[1]! = 0 := by decide +kernel

theorem suz_label_thirtysix : fuseCls[36]! = 0 := by decide +kernel

theorem suz_label_three : fuseCls[3]! ≠ 0 := by decide +kernel

theorem suz_label_four : fuseCls[4]! ≠ 0 := by decide +kernel

theorem suz_phi_pow_three (a : Fin 5 → ZMod 3) :
    φ (Multiplicative.ofAdd a) ^ 3 = 1 :=
  Dg_pow_three _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

theorem suz_phi_notMem_zpowers {a b : Fin 5 → ZMod 3}
    {i : Fin 5} (hb : b i = 0) (ha : a i ≠ 0) :
    φ (Multiplicative.ofAdd a) ∉ Subgroup.zpowers (φ (Multiplicative.ofAdd b)) := by
  rintro hmem
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hn' : φ (Multiplicative.ofAdd b ^ n) = φ (Multiplicative.ofAdd a) := by
    rw [map_zpow]
    exact hn
  have h2 := congrArg Multiplicative.toAdd (φ_injective hn')
  rw [toAdd_zpow, toAdd_ofAdd, toAdd_ofAdd] at h2
  have h3 := congrFun h2 i
  simp only [Pi.smul_apply, hb, smul_zero] at h3
  exact ha h3.symm

theorem suz_yPerm_ne_one : yPerm ≠ 1 := fun h => by
  have h1 := (eqA_iff rep_y rep_idA).2 h
  rw [cCheck_parts.2.2.2.1] at h1
  exact Bool.false_ne_true h1

theorem suz_phi_mem
    (a : Fin 5 → ZMod 3) : φ (Multiplicative.ofAdd a) ∈ suzM :=
  Dg_le (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

theorem suz_three_dvd_index_y
    (y : ↥suzM) (hy : (y : Equiv.Perm (Fin 1782)) = yPerm) :
    3 ∣ (Subgroup.centralizer ({y} : Set ↥suzM)).index := by
  have hc := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_inf_centralizer_of_injective
    suzM.subtype suzM.subtype_injective ⊤ y
  have hsub : suzM.subtype y = (y : Equiv.Perm (Fin 1782)) := rfl
  rw [top_inf_eq, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hsub, hy] at hc
  have hcard : Nat.card (Subgroup.centralizer ({y} : Set ↥suzM)) = 3240 := by
    have h := Subgroup.card_map_of_injective (K := Subgroup.centralizer ({y} : Set ↥suzM))
      suzM.subtype_injective
    rw [hc, inf_comm, ← Cy_eq.1] at h
    rw [← h]
    exact Cy_eq.2
  have hmul := Subgroup.card_mul_index (Subgroup.centralizer ({y} : Set ↥suzM))
  rw [hcard, suzM_card_chain] at hmul
  have hidx : (Subgroup.centralizer ({y} : Set ↥suzM)).index = 138378240 := by
    omega
  rw [hidx]
  norm_num

theorem suz_fuse_labelled
    {k : ℕ} (hk : k < 243)
    (hk0 : k ≠ 0) :
    (fuseCls[k]! = 0 → ∃ h ∈ suzM, h * φ (Multiplicative.ofAdd (vec k)) * h⁻¹ = fuseXA) ∧
    (fuseCls[k]! ≠ 0 → ∃ h ∈ suzM, h * φ (Multiplicative.ofAdd (vec k)) * h⁻¹ = fuseXB) := by
  obtain ⟨hv, hP, heA, heB⟩ := fuseCheck_parts.2.2 k hk hk0
  have hrep := rep_conjA hv (rep_dElts hk)
  refine ⟨fun hc => ⟨_, mem_suzM_of_inP (rep_of_validA hv) hP, ?_⟩,
    fun hc => ⟨_, mem_suzM_of_inP (rep_of_validA hv) hP, ?_⟩⟩
  · exact (eqA_iff hrep rep_fuseXA).1 (heA hc)
  · exact (eqA_iff hrep rep_fuseXB).1 (heB hc)

theorem suz_conj_one_thirtysix :
    ∃ g ∈ suzM, g * φ (Multiplicative.ofAdd (vec 1)) * g⁻¹ =
      φ (Multiplicative.ofAdd (vec 36)) :=
  suz_conj_of_common ((suz_fuse_labelled (k := 1) (by norm_num) (by norm_num)).1 suz_label_one)
    ((suz_fuse_labelled (k := 36) (by norm_num) (by norm_num)).1 suz_label_thirtysix)

theorem suz_conj_three_four :
    ∃ g ∈ suzM, g * φ (Multiplicative.ofAdd (vec 3)) * g⁻¹ =
      φ (Multiplicative.ofAdd (vec 4)) :=
  suz_conj_of_common ((suz_fuse_labelled (k := 3) (by norm_num) (by norm_num)).2 suz_label_three)
    ((suz_fuse_labelled (k := 4) (by norm_num) (by norm_num)).2 suz_label_four)

theorem listRow_suzM :
    ListRow ↥suzM := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨dA, hdA⟩ : ∃ d : ↥suzM,
      (d : Equiv.Perm (Fin 1782)) = φ (Multiplicative.ofAdd (vec 1)) :=
    ⟨⟨_, suz_phi_mem (vec 1)⟩, rfl⟩
  obtain ⟨dB, hdB⟩ : ∃ d : ↥suzM,
      (d : Equiv.Perm (Fin 1782)) = φ (Multiplicative.ofAdd (vec 3)) :=
    ⟨⟨_, suz_phi_mem (vec 3)⟩, rfl⟩
  obtain ⟨dC, hdC⟩ : ∃ d : ↥suzM,
      (d : Equiv.Perm (Fin 1782)) = φ (Multiplicative.ofAdd (vec 36)) :=
    ⟨⟨_, suz_phi_mem (vec 36)⟩, rfl⟩
  obtain ⟨dD, hdD⟩ : ∃ d : ↥suzM,
      (d : Equiv.Perm (Fin 1782)) = φ (Multiplicative.ofAdd (vec 4)) :=
    ⟨⟨_, suz_phi_mem (vec 4)⟩, rfl⟩
  obtain ⟨yS, hyS⟩ : ∃ y : ↥suzM, (y : Equiv.Perm (Fin 1782)) = yPerm :=
    ⟨⟨yPerm, yPerm_mem⟩, rfl⟩
  have hA3 : (dA : Equiv.Perm (Fin 1782)) ^ 3 = 1 := by
    rw [hdA]
    exact suz_phi_pow_three _
  have hB3 : (dB : Equiv.Perm (Fin 1782)) ^ 3 = 1 := by
    rw [hdB]
    exact suz_phi_pow_three _
  have hA1 : (dA : Equiv.Perm (Fin 1782)) ≠ 1 := by
    intro h
    rw [hdA] at h
    obtain ⟨h1, -, e1⟩ :=
      (suz_fuse_labelled (k := 1) (by norm_num) (by norm_num)).1 suz_label_one
    rw [h, mul_one, mul_inv_cancel] at e1
    exact fuseXA_ne_one e1.symm
  have hB1 : (dB : Equiv.Perm (Fin 1782)) ≠ 1 := by
    intro h
    rw [hdB] at h
    obtain ⟨h3, -, e3⟩ :=
      (suz_fuse_labelled (k := 3) (by norm_num) (by norm_num)).2 suz_label_three
    rw [h, mul_one, mul_inv_cancel] at e3
    exact fuseXB_ne_one e3.symm
  have hR : ∀ c ∈ ({dA, dB, yS} : Set ↥suzM), orderOf c = 3 := by
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc | hc <;> rw [hc]
    · exact suz_orderOf_three hA3 hA1
    · exact suz_orderOf_three hB3 hB1
    · exact suz_orderOf_three (by rw [hyS]; exact yPerm_pow)
        (by rw [hyS]; exact suz_yPerm_ne_one)
  have hcov : ∀ s : ↥suzM, orderOf s = 3 → ∃ k c : ↥suzM,
      c ∈ ({dA, dB, yS} : Set ↥suzM) ∧ ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ k * c ^ e * k⁻¹ = s := by
    intro s hs
    have hs' : orderOf (s : Equiv.Perm (Fin 1782)) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact hs
    obtain ⟨k, hk, c, hc, e, he, hfuse⟩ := suz_exists_conj_classes s.2 hs'
    rcases hc with hc | hc | hc
    · obtain ⟨h1, hh1, e1⟩ :=
        (suz_fuse_labelled (k := 1) (by norm_num) (by norm_num)).1 suz_label_one
      rw [hc] at hfuse
      refine ⟨⟨k * h1, suzM.mul_mem hk hh1⟩, dA, by simp, e, he, Subtype.ext ?_⟩
      show (k * h1) * (dA : Equiv.Perm (Fin 1782)) ^ e * (k * h1)⁻¹ =
        (s : Equiv.Perm (Fin 1782))
      rw [hdA]
      exact suz_transfer_pow e1 hfuse
    · obtain ⟨h3, hh3, e3⟩ :=
        (suz_fuse_labelled (k := 3) (by norm_num) (by norm_num)).2 suz_label_three
      rw [hc] at hfuse
      refine ⟨⟨k * h3, suzM.mul_mem hk hh3⟩, dB, by simp, e, he, Subtype.ext ?_⟩
      show (k * h3) * (dB : Equiv.Perm (Fin 1782)) ^ e * (k * h3)⁻¹ =
        (s : Equiv.Perm (Fin 1782))
      rw [hdB]
      exact suz_transfer_pow e3 hfuse
    · rw [hc] at hfuse
      refine ⟨⟨k, hk⟩, yS, by simp, e, he, Subtype.ext ?_⟩
      show k * (yS : Equiv.Perm (Fin 1782)) ^ e * k⁻¹ = (s : Equiv.Perm (Fin 1782))
      rw [hyS]
      exact hfuse
  have hw : ∀ c ∈ ({dA, dB, yS} : Set ↥suzM),
      3 ∣ (Subgroup.centralizer ({c} : Set ↥suzM)).index ∨
        ∃ g : ↥suzM, (g * c * g⁻¹) * c = c * (g * c * g⁻¹) ∧
          g * c * g⁻¹ ∉ Subgroup.zpowers c := by
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc | hc <;> rw [hc]
    · right
      obtain ⟨g, hg, hgc⟩ := suz_conj_one_thirtysix
      have hgd : (⟨g, hg⟩ : ↥suzM) * dA * (⟨g, hg⟩ : ↥suzM)⁻¹ = dC := by
        apply Subtype.ext
        show g * (dA : Equiv.Perm (Fin 1782)) * g⁻¹ = (dC : Equiv.Perm (Fin 1782))
        rw [hdA, hdC]
        exact hgc
      refine ⟨⟨g, hg⟩, ?_, ?_⟩
      · rw [hgd]
        apply Subtype.ext
        show (dC : Equiv.Perm (Fin 1782)) * (dA : Equiv.Perm (Fin 1782)) =
          (dA : Equiv.Perm (Fin 1782)) * (dC : Equiv.Perm (Fin 1782))
        rw [hdA, hdC]
        exact Dg_comm _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩) _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      · rw [hgd]
        intro hmem
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have h1 := congrArg Subtype.val hn
        rw [Subgroup.coe_zpow, hdA, hdC] at h1
        exact suz_phi_notMem_zpowers (a := vec 36) (b := vec 1) (i := 2) (by decide)
          (by decide) (Subgroup.mem_zpowers_iff.mpr ⟨n, h1⟩)
    · right
      obtain ⟨g, hg, hgc⟩ := suz_conj_three_four
      have hgd : (⟨g, hg⟩ : ↥suzM) * dB * (⟨g, hg⟩ : ↥suzM)⁻¹ = dD := by
        apply Subtype.ext
        show g * (dB : Equiv.Perm (Fin 1782)) * g⁻¹ = (dD : Equiv.Perm (Fin 1782))
        rw [hdB, hdD]
        exact hgc
      refine ⟨⟨g, hg⟩, ?_, ?_⟩
      · rw [hgd]
        apply Subtype.ext
        show (dD : Equiv.Perm (Fin 1782)) * (dB : Equiv.Perm (Fin 1782)) =
          (dB : Equiv.Perm (Fin 1782)) * (dD : Equiv.Perm (Fin 1782))
        rw [hdB, hdD]
        exact Dg_comm _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩) _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      · rw [hgd]
        intro hmem
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have h1 := congrArg Subtype.val hn
        rw [Subgroup.coe_zpow, hdB, hdD] at h1
        exact suz_phi_notMem_zpowers (a := vec 4) (b := vec 3) (i := 0) (by decide)
          (by decide) (Subgroup.mem_zpowers_iff.mpr ⟨n, h1⟩)
    · left
      exact suz_three_dvd_index_y yS hyS
  exact listRow_of_cover_or_index ({dA, dB, yS} : Set ↥suzM) hR hcov hw

theorem listRow_suz [Finite NativeSporadic.Suz] :
    ListRow NativeSporadic.Suz :=
  ListRow.of_mulEquiv suzEquivM.symm listRow_suzM

theorem outerRow_suz [Finite NativeSporadic.Suz] :
    OuterRow NativeSporadic.Suz := by
  refine outerRow_of_not_three_dvd_outer ?_
  have h2 : Nat.card (Outer NativeSporadic.Suz) = 2 := outer_carrier_suz.1
  rw [h2]
  norm_num

theorem row_carrier_suz :
    RowOf (NativeSporadic.Carrier .Suz) := by
  haveI : Finite NativeSporadic.Suz := Finite.of_equiv _ suzEquivM.symm.toEquiv
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.Suz) e.symm ⟨listRow_suz, outerRow_suz⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
