module

public import Certificates.Kernel.Co3Nine.Chk
public import CFSG.Certificates.Kernel.Co3NineSound
public import CFSG.Sporadic.SmallOddCore.Co3Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesPackage
public import CFSG.HardMathSupport.Lang.E6Descent.SylowNormal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoSetupSylow
public import CFSG.Walter.Bender1970.S38.Omega
public import CFSG.Fischer.Classification.Basic.Heisenberg
public import CFSG.HardMathSupport.Lang.E6Descent.FixedElementary

public section

namespace CertificateChecks.KernelSpor.Co3Nine

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
open CFSG.Certificates CFSG.Certificates.Native
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
open CFSG.QuasithinUnique CFSG.HardMathSupport.Lang.E6Descent CFSG.Walter
open CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
open CFSG.KS.Co3Nine CFSG.KS.Raw.Orb
open scoped Pointwise

@[expose] noncomputable def m9 (k : Nat) : Equiv.Perm (Fin 276) :=
  CFSG.Monster.B.Co2.permOfArr 276 co3MArrs[k]!

theorem hS9 : ∀ j < 7, PRep 276 9 (Co3M.S j) (m9 j) ∧ PRep 276 9 (Co3M.SI j) (m9 j)⁻¹ :=
  fun _ hj => prep_PS Co3M.binds Co3M.perm (by omega)

theorem hT9 : ∀ t < 8, PRep 276 9 (Co3T.S t) (co3TGen t) :=
  fun _ ht => (prep_PS Co3T.binds Co3T.perm (by omega)).1

@[expose] noncomputable def X0 : Set (Fin 276) := finSet 276 co3IndexNineYList

@[expose] noncomputable def X9 : Equiv.Perm (Fin 276) := wP m9 co3IndexNineXWord

@[expose] noncomputable def Y9 : Equiv.Perm (Fin 276) := wP m9 co3IndexNineYWord

@[expose] noncomputable def tr9 (i : Nat) : Set (Fin 276) := wP m9 (ES.getD i []).tail • X0

theorem facts :
    Letters co3IndexNineXWord ∧ Letters co3IndexNineYWord ∧ X9 ^ 3 = 1 ∧ Y9 ^ 3 = 1 ∧
      X9 * Y9 = Y9 * X9 ∧ X9 ≠ 1 ∧ Y9 ≠ 1 ∧ Y9 ≠ X9 ∧ Y9 ≠ X9 * X9 ∧ X9 • X0 = X0 ∧
      Y9 • X0 = X0 ∧ (∀ t < 8, co3TGen t • X0 = X0) ∧ ES.length = 315 ∧
      (∀ i < 315, Letters (ES.getD i []).tail) ∧
      (∀ i j, i < 315 → j < 315 → tr9 i = tr9 j → i = j) ∧
      (∀ i < 315, tr9 i = X0 ∨ ∃ t < 8, co3TGen t • tr9 i ≠ tr9 i) :=
  co39K_sound hS9 hT9 chk

theorem m9_mem : ∀ j < 7, m9 j ∈ co3M := by
  intro j hj
  rw [co3M_eq]
  exact Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩

theorem X9_mem_M : X9 ∈ co3M := wP_mem m9_mem _ facts.1

theorem Y9_mem_M : Y9 ∈ co3M := wP_mem m9_mem _ facts.2.1

theorem tr9_mem {i : Nat} (hi : i < 315) : tr9 i ∈ MulAction.orbit ↥co3M X0 :=
  ⟨⟨_, wP_mem m9_mem _ (facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi)⟩, rfl⟩

theorem XY_facts :
    X9 ^ 3 = 1 ∧ Y9 ^ 3 = 1 ∧ Commute X9 Y9 ∧ X9 ≠ 1 ∧ Y9 ≠ 1 ∧ Y9 ≠ X9 ∧ Y9 ≠ X9 ^ 2 := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9, -⟩ := facts
  exact ⟨h3, h4, h5, h6, h7, h8, by rw [pow_two]; exact h9⟩

theorem T_le_M :
    co3T ≤ co3M := by
  rw [co3M_eq_centralizer]
  exact le_inf co3T_le_P co3T_le_centralizer_Z

theorem T_le_stab : co3T ≤ MulAction.stabilizer (Equiv.Perm (Fin 276)) X0 := by
  rw [co3T_eq, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  change co3TGen (k : ℕ) ∈ MulAction.stabilizer (Equiv.Perm (Fin 276)) X0
  rw [MulAction.mem_stabilizer_iff]
  exact facts.2.2.2.2.2.2.2.2.2.2.2.1 k k.2

theorem U_fix (u : ↥co3P) (hu : u ∈ co3T.subgroupOf co3P) :
    (u : Equiv.Perm (Fin 276)) • X0 = X0 := by
  have huT : (u : Equiv.Perm (Fin 276)) ∈ co3T := Subgroup.mem_subgroupOf.mp hu
  have hstab := T_le_stab huT
  rwa [MulAction.mem_stabilizer_iff] at hstab

theorem tr9_inj : Function.Injective fun i : Fin 315 => tr9 i :=
  fun i j h => Fin.ext (facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i j i.2 j.2 h)

theorem range_ncard : (Set.range fun i : Fin 315 => tr9 i).ncard = 315 := by
  rw [Set.ncard_range_of_injective tr9_inj, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem range_sub : (Set.range fun i : Fin 315 => tr9 i) ⊆ MulAction.orbit ↥co3M X0 := by
  rintro _ ⟨i, rfl⟩
  exact tr9_mem i.2

theorem orbit_ge : 315 ≤ Nat.card (MulAction.orbit ↥co3M X0) := by
  rw [Nat.card_coe_set_eq, ← range_ncard]
  exact Set.ncard_le_ncard range_sub (Set.toFinite _)

theorem X_fix : X9 • X0 = X0 := facts.2.2.2.2.2.2.2.2.2.1

theorem Y_fix : Y9 • X0 = X0 := facts.2.2.2.2.2.2.2.2.2.2.1

theorem stab_S_card :
    Nat.card (MulAction.stabilizer ↥co3M X0) = 9216 := by
  let S : Subgroup ↥co3M := MulAction.stabilizer ↥co3M X0
  have : Fintype ↥co3M :=
    Fintype.ofInjective (Subtype.val : ↥co3M → Equiv.Perm (Fin 276)) Subtype.val_injective
  have : Fintype (MulAction.orbit ↥co3M X0) := Fintype.ofFinite _
  have hco3M : Fintype.card ↥co3M = 2903040 := by
    rw [← Nat.card_eq_fintype_card, card_co3M]
  have hOS : Nat.card (MulAction.orbit ↥co3M X0) * Nat.card S = 2903040 := by
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥co3M X0
    rw [hco3M] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hupper : Nat.card S ≤ 9216 := by
    have hge := orbit_ge
    have h1 : 315 * Nat.card S ≤ 2903040 := by
      calc 315 * Nat.card S
          ≤ Nat.card (MulAction.orbit ↥co3M X0) * Nat.card S :=
            Nat.mul_le_mul_right _ hge
        _ = 2903040 := hOS
    omega
  have hUM : co3T ≤ co3M := T_le_M
  have hUcard : Nat.card (co3T.subgroupOf co3M) = 1024 := by
    rw [card_subgroupOf_of_le hUM, card_co3T]
  obtain ⟨hx3, hy3, hcomm, hx1, hy1, hyx_ne, hyx2⟩ := XY_facts
  have hyx : Y9 ∉ Subgroup.zpowers X9 :=
    CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne hx3 hy1 hyx_ne hyx2
  let xM : ↥co3M := ⟨X9, X9_mem_M⟩
  let yM : ↥co3M := ⟨Y9, Y9_mem_M⟩
  have hx3M : xM ^ 3 = 1 := by
    apply Subtype.ext
    simpa [xM] using hx3
  have hy3M : yM ^ 3 = 1 := by
    apply Subtype.ext
    simpa [yM] using hy3
  have hcommM : Commute xM yM := by
    change xM * yM = yM * xM
    apply Subtype.ext
    simpa [xM, yM] using hcomm.eq
  have hx1M : xM ≠ 1 := by
    intro h
    exact hx1 (congrArg Subtype.val h)
  have hyxM : yM ∉ Subgroup.zpowers xM := by
    intro h
    apply hyx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact ⟨k, by simpa [xM, yM] using congrArg Subtype.val hk⟩
  have hQcard : Nat.card (Subgroup.closure ({xM, yM} : Set ↥co3M)) = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hx3M hy3M hcommM hx1M hyxM
  have hUle : co3T.subgroupOf co3M ≤ S := by
    intro u hu
    have huT : (u : Equiv.Perm (Fin 276)) ∈ co3T := Subgroup.mem_subgroupOf.mp hu
    have hP : (⟨(u : Equiv.Perm (Fin 276)), co3T_le_P huT⟩ : ↥co3P) ∈
        co3T.subgroupOf co3P := Subgroup.mem_subgroupOf.mpr huT
    have hfix := U_fix ⟨(u : Equiv.Perm (Fin 276)), co3T_le_P huT⟩ hP
    rw [MulAction.mem_stabilizer_iff]
    exact hfix
  have hQle : Subgroup.closure ({xM, yM} : Set ↥co3M) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · change xM ∈ MulAction.stabilizer ↥co3M X0
      rw [MulAction.mem_stabilizer_iff]
      simpa [xM] using X_fix
    · change yM ∈ MulAction.stabilizer ↥co3M X0
      rw [MulAction.mem_stabilizer_iff]
      simpa [yM] using Y_fix
  have hdis : co3T.subgroupOf co3M ⊓ Subgroup.closure ({xM, yM} : Set ↥co3M) = ⊥ := by
    have hU2 : IsPGroup 2 ↥(co3T.subgroupOf co3M) :=
      IsPGroup.of_card (n := 10) (by rw [hUcard]; norm_num)
    have hQ3 : IsPGroup 3 ↥(Subgroup.closure ({xM, yM} : Set ↥co3M)) :=
      IsPGroup.of_card (n := 2) (by rw [hQcard]; norm_num)
    exact (IsPGroup.disjoint_of_coprime hU2 hQ3 (by decide)).eq_bot
  have hlower : 9216 ≤ Nat.card S := by
    have h := card_mul_card_le_of_inf_eq_bot hUle hQle hdis
    rw [hUcard, hQcard] at h
    norm_num at h ⊢
    exact h
  exact le_antisymm hupper hlower

theorem stab_card :
    Nat.card ((co3M ⊓ MulAction.stabilizer (Equiv.Perm (Fin 276)) X0).subgroupOf co3P)
      = 9 * Nat.card (co3T.subgroupOf co3P) := by
  let S : Subgroup ↥co3M := MulAction.stabilizer ↥co3M X0
  have hmap : (co3M ⊓ MulAction.stabilizer (Equiv.Perm (Fin 276)) X0) =
      S.map co3M.subtype := by
    ext g
    constructor
    · rintro ⟨hgM, hgS⟩
      exact ⟨⟨g, hgM⟩, hgS, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.2, hs⟩
  have hleP : co3M ⊓ MulAction.stabilizer (Equiv.Perm (Fin 276)) X0 ≤ co3P :=
    fun g hg => co3M_le_P (Subgroup.mem_inf.mp hg).1
  have hleft : Nat.card ((co3M ⊓ MulAction.stabilizer (Equiv.Perm (Fin 276))
      X0).subgroupOf co3P) = Nat.card S := by
    rw [card_subgroupOf_of_le hleP, hmap,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective co3M)]
  rw [hleft, stab_S_card, card_co3T_subgroupOf]

theorem orbit_card :
    Nat.card (MulAction.orbit ↥co3M X0) = 315 := by
  have : Fintype ↥co3M :=
    Fintype.ofInjective (Subtype.val : ↥co3M → Equiv.Perm (Fin 276)) Subtype.val_injective
  have : Fintype (MulAction.orbit ↥co3M X0) := Fintype.ofFinite _
  have hco3M : Fintype.card ↥co3M = 2903040 := by
    rw [← Nat.card_eq_fintype_card, card_co3M]
  have hS : Fintype.card ↥(MulAction.stabilizer ↥co3M X0) = 9216 := by
    rw [← Nat.card_eq_fintype_card]
    exact stab_S_card
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥co3M X0
  rw [hco3M, hS] at h
  have h315 : Fintype.card (MulAction.orbit ↥co3M X0) = 315 := by omega
  rw [Nat.card_eq_fintype_card]
  exact h315

theorem huniq :
    ∀ c ∈ co3P ⊓ co3M,
      (∀ u ∈ co3T.subgroupOf co3P,
        (u : Equiv.Perm (Fin 276)) • (c • X0) = c • X0) →
      c • X0 = X0 := by
  intro c hc hfix
  have hcM : c ∈ co3M := (Subgroup.mem_inf.mp hc).2
  have hBeq : (Set.range fun i : Fin 315 => tr9 i) = MulAction.orbit ↥co3M X0 := by
    refine Set.eq_of_subset_of_ncard_le range_sub ?_ (Set.toFinite _)
    rw [range_ncard, ← Nat.card_coe_set_eq, orbit_card]
  have hcOrbit : c • X0 ∈ MulAction.orbit ↥co3M X0 :=
    MulAction.mem_orbit_iff.mpr ⟨⟨c, hcM⟩, rfl⟩
  rw [← hBeq] at hcOrbit
  obtain ⟨i, hi⟩ := hcOrbit
  rw [← hi]
  rcases facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 i i.2 with h | ⟨t, ht, hne⟩
  · exact h
  · exfalso
    apply hne
    have hgen : co3TGen t ∈ co3T := co3TGen_mem ht
    have hu : (⟨co3TGen t, co3T_le_P hgen⟩ : ↥co3P) ∈ co3T.subgroupOf co3P :=
      Subgroup.mem_subgroupOf.mpr hgen
    have := hfix _ hu
    rw [← hi] at this
    exact this

@[expose] noncomputable def P9 : Subgroup ↥co3P :=
  (co3M ⊓ MulAction.stabilizer (Equiv.Perm (Fin 276)) X0).subgroupOf co3P

@[expose] noncomputable def Q9 : Subgroup ↥co3P :=
  (Subgroup.closure ({X9, Y9} : Set (Equiv.Perm (Fin 276)))).subgroupOf co3P

theorem X_in_P :
    (⟨X9, co3M_le_P X9_mem_M⟩ : ↥co3P) ∈ P9 := by
  rw [P9, Subgroup.mem_subgroupOf]
  refine ⟨X9_mem_M, ?_⟩
  change X9 ∈ MulAction.stabilizer (Equiv.Perm (Fin 276)) X0
  rw [MulAction.mem_stabilizer_iff]
  exact X_fix

theorem Y_in_P :
    (⟨Y9, co3M_le_P Y9_mem_M⟩ : ↥co3P) ∈ P9 := by
  rw [P9, Subgroup.mem_subgroupOf]
  refine ⟨Y9_mem_M, ?_⟩
  change Y9 ∈ MulAction.stabilizer (Equiv.Perm (Fin 276)) X0
  rw [MulAction.mem_stabilizer_iff]
  exact Y_fix

theorem U_le_P :
    co3T.subgroupOf co3P ≤ P9 := by
  intro u hu
  rw [P9, Subgroup.mem_subgroupOf]
  have huT : (u : Equiv.Perm (Fin 276)) ∈ co3T := Subgroup.mem_subgroupOf.mp hu
  refine ⟨T_le_M huT, ?_⟩
  change (u : Equiv.Perm (Fin 276)) ∈ MulAction.stabilizer (Equiv.Perm (Fin 276)) X0
  rw [MulAction.mem_stabilizer_iff]
  exact U_fix u hu

theorem Q_le_P :
    Q9 ≤ P9 := by
  have hX := X_in_P
  have hY := Y_in_P
  have hle : Subgroup.closure ({X9, Y9} : Set (Equiv.Perm (Fin 276))) ≤
      P9.map co3P.subtype := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨⟨X9, co3M_le_P X9_mem_M⟩, hX, rfl⟩
    · exact ⟨⟨Y9, co3M_le_P Y9_mem_M⟩, hY, rfl⟩
  intro q hq
  rw [Q9, Subgroup.mem_subgroupOf] at hq
  obtain ⟨g, hgP, hgq⟩ := hle hq
  rw [← Subtype.ext hgq]
  exact hgP

theorem Q_card :
    Nat.card Q9 = 9 := by
  obtain ⟨hx3, hy3, hcomm, hx1, hy1, hyx_ne, hyx2⟩ := XY_facts
  have hyx : Y9 ∉ Subgroup.zpowers X9 :=
    CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne hx3 hy1 hyx_ne hyx2
  have hleP : Subgroup.closure ({X9, Y9} : Set (Equiv.Perm (Fin 276))) ≤ co3P := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact co3M_le_P X9_mem_M
    · exact co3M_le_P Y9_mem_M
  rw [Q9, card_subgroupOf_of_le hleP]
  exact CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hx3 hy3 hcomm hx1 hyx

theorem Q_pow_three : ∀ q ∈ Q9, q ^ 3 = 1 := by
  obtain ⟨hx3, hy3, hcomm, -, -, -, -⟩ := XY_facts
  have hcube : CFSG.Fischer.Classification.CubeRel X9 Y9 := by
    refine ⟨hx3, hy3, ?_, ?_⟩
    · rw [hcomm.mul_pow, hx3, hy3, one_mul]
    · rw [hcomm.inv_right.mul_pow, hx3, inv_pow, hy3, inv_one, mul_one]
  intro q hq
  rw [Q9, Subgroup.mem_subgroupOf] at hq
  have hq3 := hcube.pow_three_eq_one hq
  apply Subtype.ext
  simpa using hq3

theorem hNC :
    (co3P : Subgroup (Equiv.Perm (Fin 276))) ⊓
      Subgroup.normalizer (co3T : Set (Equiv.Perm (Fin 276))) ≤ co3M := by
  intro g hg
  obtain ⟨hgP, hgN⟩ := Subgroup.mem_inf.mp hg
  have hzc : ∀ y ∈ co3T, co3Z * y = y * co3Z := by
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.1 (co3T_le_centralizer_Z hy)).symm
  have hcent : g ∈ Subgroup.centralizer ({co3Z} : Set (Equiv.Perm (Fin 276))) :=
    normalizer_le_centralizer_of_center co3Z_mem_T co3Z_ne_one hzc
      (fun x hx h => (co3T_center_iff x).1 ⟨hx, h⟩) hgN
  rw [co3M_eq_centralizer]
  exact Subgroup.mem_inf.mpr ⟨hgP, hcent⟩

theorem p_mem_P
    {p : ↥co3P}
    (hα : (co3T.subgroupOf co3P).map (MulAut.conj p).toMonoidHom =
      co3T.subgroupOf co3P) : p ∈ P9 := by
  have hpN : (p : Equiv.Perm (Fin 276)) ∈ Subgroup.normalizer (co3T : Set
      (Equiv.Perm (Fin 276))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : co3T.map (MulAut.conj (p : Equiv.Perm (Fin 276))).toMonoidHom ≤ co3T := by
      rintro _ ⟨x, hx, rfl⟩
      have hu : (⟨x, co3T_le_P hx⟩ : ↥co3P) ∈ co3T.subgroupOf co3P :=
        Subgroup.mem_subgroupOf.mpr hx
      have hm : (MulAut.conj p) ⟨x, co3T_le_P hx⟩ ∈ co3T.subgroupOf co3P := by
        rw [← hα]
        exact ⟨_, hu, rfl⟩
      have := Subgroup.mem_subgroupOf.mp hm
      simpa [MulAut.conj_apply] using this
    have hcard : Nat.card (co3T.map (MulAut.conj
        (p : Equiv.Perm (Fin 276))).toMonoidHom) = Nat.card co3T :=
      Subgroup.card_map_of_injective (MulAut.conj (p : Equiv.Perm (Fin 276))).injective
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hpM : (p : Equiv.Perm (Fin 276)) ∈ co3M :=
    hNC (Subgroup.mem_inf.mpr ⟨p.2, hpN⟩)
  have hpfix : (p : Equiv.Perm (Fin 276)) • X0 = X0 := by
    apply huniq p (Subgroup.mem_inf.mpr ⟨p.2, hpM⟩)
    intro u hu
    have huT : (u : Equiv.Perm (Fin 276)) ∈ co3T := Subgroup.mem_subgroupOf.mp hu
    have hpinvN : (p : Equiv.Perm (Fin 276))⁻¹ ∈ Subgroup.normalizer (co3T : Set
        (Equiv.Perm (Fin 276))) := Subgroup.inv_mem _ hpN
    have hconj : (p : Equiv.Perm (Fin 276))⁻¹ * (u : Equiv.Perm (Fin 276)) *
        (p : Equiv.Perm (Fin 276)) ∈ co3T := by
      have := (Subgroup.mem_normalizer_iff.mp hpinvN
        (u : Equiv.Perm (Fin 276))).mp huT
      simpa [mul_assoc] using this
    have hfixu := U_fix
      (⟨(p : Equiv.Perm (Fin 276))⁻¹ * (u : Equiv.Perm (Fin 276)) *
        (p : Equiv.Perm (Fin 276)), co3T_le_P hconj⟩ : ↥co3P)
      (Subgroup.mem_subgroupOf.mpr hconj)
    calc (u : Equiv.Perm (Fin 276)) • ((p : Equiv.Perm (Fin 276)) • X0)
        = ((u : Equiv.Perm (Fin 276)) * (p : Equiv.Perm (Fin 276))) • X0 := by rw [mul_smul]
      _ = ((p : Equiv.Perm (Fin 276)) * ((p : Equiv.Perm (Fin 276))⁻¹ *
            (u : Equiv.Perm (Fin 276)) * (p : Equiv.Perm (Fin 276)))) • X0 := by group
      _ = (p : Equiv.Perm (Fin 276)) • (((p : Equiv.Perm (Fin 276))⁻¹ *
            (u : Equiv.Perm (Fin 276)) * (p : Equiv.Perm (Fin 276))) • X0) := by
          rw [mul_smul]
      _ = (p : Equiv.Perm (Fin 276)) • X0 := by rw [hfixu]
  rw [P9, Subgroup.mem_subgroupOf]
  refine ⟨hpM, ?_⟩
  change (p : Equiv.Perm (Fin 276)) ∈ MulAction.stabilizer (Equiv.Perm (Fin 276)) X0
  rwa [MulAction.mem_stabilizer_iff]

theorem map_P
    (α : MulAut ↥co3P)
    (hα : (co3T.subgroupOf co3P).map α.toMonoidHom = co3T.subgroupOf co3P) :
    P9.map α.toMonoidHom = P9 := by
  obtain ⟨p, hp⟩ := co3P_allInner α
  rw [hp] at hα ⊢
  have hpP : p ∈ P9 := p_mem_P hα
  ext q
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact P9.mul_mem (P9.mul_mem hpP hr) (P9.inv_mem hpP)
  · intro hq
    refine ⟨p⁻¹ * q * p, ?_, ?_⟩
    · exact P9.mul_mem (P9.mul_mem (P9.inv_mem hpP) hq) hpP
    · change p * (p⁻¹ * q * p) * p⁻¹ = q
      group

theorem package744103 :
    IndexNinePackage ↥co3P := by
  have hU : IsSylowTwoOf (co3T.subgroupOf co3P) ⊤ := by
    refine ⟨le_top, co3T_isPGroup, ?_⟩
    have hidx : ((co3T.subgroupOf co3P).subgroupOf ⊤).index =
        (co3T.subgroupOf co3P).index := Subgroup.relIndex_top_right _
    rw [hidx]
    exact co3T_not_dvd_index
  refine ⟨co3T.subgroupOf co3P, P9, Q9, hU, U_le_P, stab_card, ?_, Q_le_P, Q_card,
    Q_pow_three⟩
  intro α hα
  exact map_P α hα

end CertificateChecks.KernelSpor.Co3Nine

end
