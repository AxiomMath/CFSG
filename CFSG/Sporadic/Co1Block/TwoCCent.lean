module

public import CFSG.Sporadic.Co1Block.TwoCCheck
public import CFSG.Sporadic.Co1Block.CentQ
public import CFSG.Sporadic.Co1Block.Classes
public import CFSG.Sporadic.Co1Block.PointStab

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative Matrix

section Orbit

@[expose, instance_reducible] def glAct : MulAction GL24 Vec24 where
  smul g v := ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v
  one_smul v := by
    show ((1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v
    rw [Units.val_one, one_mulVec]
  mul_smul g h v := mulVec_mul' g h v

attribute [local instance] glAct

theorem card_cent_le_of_stab
    {c : GL24} (hc : c ∈ stabH) (hu : stabPermEquiv ⟨c, hc⟩ = co2U)
    (hfix : (xFix c).ncard = 264) :
    Nat.card (GA ⊓ Subgroup.centralizer {c} : Subgroup GL24) ≤ 389283840 := by
  set C : Subgroup GL24 := GA ⊓ Subgroup.centralizer {c}
  have hcGA : c ∈ GA := stabH_le_GA hc
  have hcv : ((c : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec 0 = certVec 0 :=
    (fix_iff_stabH ⟨c, hcGA⟩).2 hc
  have horb : MulAction.orbit C (certVec 0) ⊆ xFix c := by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    change ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec 0 ∈ xFix c
    obtain ⟨hgA, hgc⟩ := Subgroup.mem_inf.1 hg
    have hgc' : g * c = c * g := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hgc
      exact hgc
    have h0 : certVec 0 ∈ certX := ⟨0, by norm_num, rfl⟩
    refine ⟨mulVec_mem_certX hgA h0, ?_⟩
    calc ((c : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
          (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec 0)
        = ((c * g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec 0 :=
          (mulVec_mul' c g _).symm
      _ = ((g * c : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec 0 := by rw [hgc']
      _ = ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
          (((c : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec 0) := mulVec_mul' g c _
      _ = ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec 0 := by rw [hcv]
  have hmemH : ∀ g : MulAction.stabilizer C (certVec 0), ((g : C) : GL24) ∈ stabH := by
    intro g
    have h := g.2
    rw [MulAction.mem_stabilizer_iff] at h
    exact (fix_iff_stabH ⟨_, (Subgroup.mem_inf.1 (g : C).2).1⟩).1 h
  have hcomm : ∀ g : MulAction.stabilizer C (certVec 0),
      ((g : C) : GL24) * c = c * ((g : C) : GL24) := fun g => by
    have h := (Subgroup.mem_inf.1 (g : C).2).2
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    exact h
  have hcu : clsHom ⟨c, hc⟩ = CFSG.Sporadic.Co2Schreier.locU := by
    rw [← stabPermEquiv_apply, hu]
  have hcls : ∀ g : MulAction.stabilizer C (certVec 0),
      clsHom ⟨_, hmemH g⟩ ∈ CFSG.Sporadic.Co2Schreier.locH3 := by
    intro g
    rw [CFSG.Sporadic.Co2Schreier.mem_locH3]
    refine ⟨?_, ?_⟩
    · rw [← stabPermEquiv_apply]
      exact (stabPermEquiv _).2
    · have e : (⟨_, hmemH g⟩ : stabH) * ⟨c, hc⟩ = ⟨c, hc⟩ * ⟨_, hmemH g⟩ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact hcomm g
      have h1 := congrArg clsHom e
      rw [map_mul, map_mul, hcu] at h1
      exact h1.symm
  have hstab : Nat.card (MulAction.stabilizer C (certVec 0)) ≤
      Nat.card CFSG.Sporadic.Co2Schreier.locH3 := by
    refine Nat.card_le_card_of_injective (fun g => ⟨clsHom ⟨_, hmemH g⟩, hcls g⟩) ?_
    intro g g' h
    have h1 := congrArg Subtype.val h
    dsimp only at h1
    have h3 := congrArg Subtype.val (clsHom_injective h1)
    dsimp only at h3
    exact Subtype.ext (Subtype.ext h3)
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer C (certVec 0))
  rw [MulAction.index_stabilizer] at h1
  have h2 : (MulAction.orbit C (certVec 0)).ncard ≤ 264 :=
    hfix ▸ Set.ncard_le_ncard horb (Set.toFinite _)
  have h3 := CFSG.Sporadic.Co2Schreier.card_locH3_le
  rw [← h1]
  calc _ ≤ 1474560 * 264 := Nat.mul_le_mul (hstab.trans h3) h2
    _ = 389283840 := by norm_num

end Orbit

abbrev cG : GL24 := (iotaC : GL24)

theorem card_cent_cG_le :
    Nat.card (GA ⊓ Subgroup.centralizer {cG} : Subgroup GL24) ≤ 389283840 :=
  card_cent_le_of_stab iotaC.2 stabPermEquiv_iotaC (by
    rw [ncard_fix_certX rep_iotaC]
    exact class_parts.2.1)

abbrev twoCE : Subgroup GL24 := brayE cG twoCD1 twoCBray

theorem twoCE_le :
    twoCE ≤ GA ⊓ Subgroup.centralizer {cG} :=
  brayE_le rep_iotaC iotaC_mem_GA twoC_cent_check

theorem card_twoCE_ge :
    389283840 ≤ Nat.card twoCE := by
  have h := card_brayE_ge rep_iotaC twoC_cent_check
  have hp : ∏ i ∈ Finset.range twoCVBase.length, twoCVSizes.getD i 0 = 389283840 := by
    simp only [twoCVBase, twoCVSizes, List.length_cons, List.length_nil, Finset.prod_range_succ,
      Finset.prod_range_zero]
    rfl
  rw [hp] at h
  exact h

theorem twoCE_eq :
    twoCE = GA ⊓ Subgroup.centralizer {cG} :=
  Subgroup.eq_of_le_of_card_ge twoCE_le (card_cent_cG_le.trans card_twoCE_ge)

theorem card_cent_cG :

    Nat.card (GA ⊓ Subgroup.centralizer {cG} : Subgroup GL24) = 389283840 :=
  le_antisymm card_cent_cG_le (twoCE_eq ▸ card_twoCE_ge)

@[expose, irreducible] def twoCQg (l : ℕ) : GL24 :=
  (strongDagG cG twoCD1 twoCBray twoCD2).getD (twoCQGens.getD l 0) 1

theorem twoCQg_def (l : ℕ) :
    twoCQg l = (strongDagG cG twoCD1 twoCBray twoCD2).getD (twoCQGens.getD l 0) 1 := by
  unfold twoCQg
  rfl

abbrev twoCQ : Subgroup GL24 := qSub twoCQg twoCQRows.length

theorem twoCQRows_length : twoCQRows.length = 11 := by simp [twoCQRows, twoCQGens]

theorem qRep_twoC :
    QRep twoCQRows twoCQg := by
  intro l hl
  have hl' : l < twoCQGens.length := by simpa [twoCQRows] using hl
  have e : twoCQRows.getD l CFSG.Sporadic.Co1Schreier.Native.one =
      (strongRows iotaCRows twoCD1 twoCBray twoCD2).getD (twoCQGens.getD l 0)
        CFSG.Sporadic.Co1Schreier.Native.one := by
    simp only [twoCQRows, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hl', Option.map_some, Option.getD_some]
  rw [e, twoCQg_def]
  exact getD_rep (rep_strongDag rep_iotaC twoC_cent_check) MRep.one _

theorem twoC_misc_parts :
    (gtBFS twoCQRows.toArray 2048).pts.size = 2048 ∧
    (∀ q ∈ twoCQRows, CFSG.Sporadic.Co1Schreier.Native.mul q iotaCRows =
      CFSG.Sporadic.Co1Schreier.Native.mul iotaCRows q) ∧
    (∀ q ∈ twoCQRows, CFSG.Sporadic.Co1Schreier.Native.mul q q =
      CFSG.Sporadic.Co1Schreier.Native.one) ∧
    (∀ q ∈ twoCQRows, ∀ q' ∈ twoCQRows, CFSG.Sporadic.Co1Schreier.Native.mul q q' =
      CFSG.Sporadic.Co1Schreier.Native.mul q' q) := by
  have h := twoC_misc_check
  simp only [twoCMiscOf, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩, -⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem card_twoCQ :
    Nat.card twoCQ = 2048 := by
  rw [card_Q qRep_twoC twoC_q_check, twoC_misc_parts.1]

theorem twoCQRows_mem {l : ℕ} (hl : l < 11) :
    twoCQRows.getD l CFSG.Sporadic.Co1Schreier.Native.one ∈ twoCQRows := by
  rw [List.getD_eq_getElem _ _ (by rw [twoCQRows_length]; exact hl)]
  exact List.getElem_mem _

theorem twoCQg_comm_c
    {l : ℕ} (hl : l < 11) : twoCQg l * cG = cG * twoCQg l := by
  have hr := qRep_twoC l (by rw [twoCQRows_length]; exact hl)
  exact (hr.mul rep_iotaC).eq (by
    rw [twoC_misc_parts.2.1 _ (twoCQRows_mem hl)]
    exact rep_iotaC.mul hr)

theorem twoCQg_sq
    {l : ℕ} (hl : l < 11) : twoCQg l * twoCQg l = 1 := by
  have hr := qRep_twoC l (by rw [twoCQRows_length]; exact hl)
  have h := hr.mul hr
  rw [twoC_misc_parts.2.2.1 _ (twoCQRows_mem hl)] at h
  exact h.eq MRep.one

theorem twoCQg_comm
    {l l' : ℕ} (hl : l < 11) (hl' : l' < 11) :
    twoCQg l * twoCQg l' = twoCQg l' * twoCQg l := by
  have hr := qRep_twoC l (by rw [twoCQRows_length]; exact hl)
  have hr' := qRep_twoC l' (by rw [twoCQRows_length]; exact hl')
  exact (hr.mul hr').eq (by
    rw [twoC_misc_parts.2.2.2 _ (twoCQRows_mem hl) _ (twoCQRows_mem hl')]
    exact hr'.mul hr)

theorem twoCQ_eq : twoCQ = Subgroup.closure (twoCQg '' {l | l < 11}) := by
  simp only [twoCQ, qSub, twoCQRows_length]

theorem twoCQ_comm
    {q r : GL24} (hq : q ∈ twoCQ) (hr : r ∈ twoCQ) : q * r = r * q := by
  rw [twoCQ_eq] at hq hr
  have hS : ∀ s ∈ twoCQg '' {l | l < 11}, q * s = s * q := by
    rintro _ ⟨l, hl, rfl⟩
    have hle : Subgroup.closure (twoCQg '' {l | l < 11}) ≤
        Subgroup.centralizer {twoCQg l} := by
      rw [Subgroup.closure_le]
      rintro _ ⟨l', hl', rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (twoCQg_comm hl' hl)
    have h := hle hq
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    exact h
  have hle : Subgroup.closure (twoCQg '' {l | l < 11}) ≤ Subgroup.centralizer {q} := by
    rw [Subgroup.closure_le]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.2 (hS s hs).symm
  have h := hle hr
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  exact h.symm

theorem twoCQ_sq
    {q : GL24} (hq : q ∈ twoCQ) : q * q = 1 := by
  rw [twoCQ_eq] at hq
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact twoCQg_sq hl
  | one => exact _root_.mul_one 1
  | mul x y hx hy ihx ihy =>
    have hxQ : x ∈ twoCQ := by rw [twoCQ_eq]; exact hx
    have hyQ : y ∈ twoCQ := by rw [twoCQ_eq]; exact hy
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [twoCQ_comm hyQ hxQ]
      _ = x * x * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx => rw [← _root_.mul_inv_rev, ihx, inv_one]

theorem twoCQ_le :
    twoCQ ≤ GA ⊓ Subgroup.centralizer {cG} := by
  rw [twoCQ_eq, Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 (twoCQg_comm_c hl)⟩
  rw [twoCQg_def]
  exact (Subgroup.mem_inf.1 (twoCE_le (getD_mem_of_forall strongDag_mem _))).1

theorem twoCQ_normal :
    ∀ g ∈ GA ⊓ Subgroup.centralizer {cG}, ∀ q ∈ twoCQ, g * q * g⁻¹ ∈ twoCQ := by
  rw [← twoCE_eq]
  exact brayE_conj_mem_Q rep_iotaC twoC_cent_check qRep_twoC twoC_q_check

theorem twoCRoots_length : twoCRoots.length = 3 := rfl

theorem twoC_tower_prod : ∏ i ∈ Finset.range twoCRoots.length, twoCCSizes.getD i 0 =
    190080 := by
  simp only [twoCRoots_length, twoCCSizes, Finset.prod_range_succ, Finset.prod_range_zero]
  rfl

theorem twoC_selfCentralizing :
    ∀ g ∈ GA ⊓ Subgroup.centralizer {cG},
    (∀ q ∈ twoCQ, g * q = q * g) → g ∈ twoCQ := by
  obtain ⟨b, hb⟩ := exists_roots qRep_twoC twoC_q_check
  have hT := card_mul_card_towerStab_brayE_le rep_iotaC twoC_cent_check twoC_q_check
    (fun i hi => (hb i hi).2)
  have hE : brayE cG twoCD1 twoCBray = GA ⊓ Subgroup.centralizer {cG} := twoCE_eq
  rw [twoC_tower_prod, hE, card_cent_cG] at hT
  set T := towerStab (GA ⊓ Subgroup.centralizer {cG}) b twoCRoots.length
  have hT2 : Nat.card T ≤ 2048 := by omega
  have hmemT : ∀ g ∈ GA ⊓ Subgroup.centralizer {cG}, (∀ q ∈ twoCQ, g * q = q * g) → g ∈ T :=
    fun g hg hq => mem_towerStab_of_lt hg _ fun i hi => hq (b i) (hb i hi).1
  have hQT : twoCQ ≤ T := fun q hq =>
    hmemT q (twoCQ_le hq) fun r hr => twoCQ_comm hq hr
  have hTQ : twoCQ = T := Subgroup.eq_of_le_of_card_ge hQT (by rw [card_twoCQ]; exact hT2)
  intro g hg hq
  rw [hTQ]
  exact hmemT g hg hq

end CFSG.Sporadic.Co1Block
