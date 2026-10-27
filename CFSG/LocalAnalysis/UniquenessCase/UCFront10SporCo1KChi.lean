module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1KAct
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreClasses
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1Defs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.Cover CFSG.Blueprint
open CFSG.EvenSporadicStandard.TwoCo1 (epsMask eMaskA matHom_epsMask)
open CFSG.Sporadic.Co1.Module (matHom)
open CFSG.KD.Co1K105 (wordRows t24Codes wordOf)
open CFSG.Sporadic.Co1Schreier.Native (Rows)


theorem rep_co1MatEquiv {u : NativeSporadic.Co1} {R : Rows}
    (h : matHom u = CFSG.Sporadic.SmallF2.rowsMatrix 24 R) : MRep R (co1MatEquiv u : GL24) := by
  unfold MRep
  rw [co1MatEquiv_val]
  exact h.symm

abbrev AG : GL24 := (co1MatEquiv (regCov 0) : GL24)

theorem rep_AG : MRep (rrCov 0) AG := rep_co1MatEquiv (matHom_regCov 0)

theorem rep_wordRows (w : List Bool) : ∀ {R : Rows} {g : GL24}, MRep R g →
    MRep (w.foldl (fun acc b => Native.mul acc (if b then rrCov 5 else rrCov 4)) R)
      (g * (co1MatEquiv (CFSG.Sporadic.Co1.Cover.eltPos ga gb w) : GL24)) := by
  induction w with
  | nil =>
    intro R g h
    simpa [CFSG.Sporadic.Co1.Cover.eltPos] using h
  | cons c w ih =>
    intro R g h
    rw [List.foldl_cons, CFSG.Sporadic.Co1.Cover.eltPos_cons, map_mul, Subgroup.coe_mul,
      ← mul_assoc]
    refine ih (h.mul ?_)
    cases c
    · exact rep_co1MatEquiv matHom_ga
    · exact rep_co1MatEquiv matHom_gb

theorem iota_eltPos
    (w : List Bool) :
    iota (CFSG.Sporadic.Co1.Cover.eltPos (CFSG.Monster.Schur.M24.gen 0)
      (CFSG.Monster.Schur.M24.gen 1) w) = CFSG.Sporadic.Co1.Cover.eltPos ga gb w := by
  unfold CFSG.Sporadic.Co1.Cover.eltPos
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  cases c <;> simp [iota_gen0, iota_gen1]

theorem mrep_t24Gen (j : Fin 4) :
    MRep (wordRows Native.one (rrCov 4) (rrCov 5) (wsT.getD j.val []))
      (co1MatEquiv (iota (t24Gen j)) : GL24) := by
  have hj : j.val < t24Codes.length := j.isLt
  have hj' : j.val < wsT.length := by simpa [wsT] using hj
  have e : wsT.getD j.val [] =
      wordOf (t24Codes.getD j.val (0, 0)).1 (t24Codes.getD j.val (0, 0)).2 := by
    rw [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hj]
    simp [wsT]
  rw [e, t24Gen, iota_eltPos]
  have h := rep_wordRows (wordOf (t24Codes.getD j.val (0, 0)).1 (t24Codes.getD j.val (0, 0)).2)
    MRep.one
  rw [one_mul] at h
  exact h

abbrev bG (k : ℕ) : GL24 := (brayEltsG aG twoAD1 twoABray).getD k 1

section


theorem rep_bray (k : ℕ) : MRep (brayL.getD k Native.one) (bG k) :=
  getD_rep (rep_brayElts rep_iotaA (centCheck_parts twoA_cent_check).1) MRep.one k

theorem bG_mem (k : ℕ) : bG k ∈ cA :=
  getD_mem_of_forall (fun g hg => twoAE_le
    (Subgroup.subset_closure (show g ∈ {g | g ∈ brayEltsG aG twoAD1 twoABray} from hg))) k

end

abbrev zG : GL24 := (co1MatEquiv (epsMask eMaskA) : GL24)

@[expose] def cG : GL24 := (AG * zG * AG⁻¹ * aG) ^ 2 * AG

theorem cG_mem : cG ∈ GA :=
  GA.mul_mem (GA.pow_mem (GA.mul_mem (GA.mul_mem (GA.mul_mem (co1MatEquiv _).2 (co1MatEquiv _).2)
    (GA.inv_mem (co1MatEquiv _).2)) iotaA_mem_GA) 2) (co1MatEquiv _).2

theorem rep_zG : MRep zRows zG := rep_co1MatEquiv (matHom_epsMask eMaskA)

@[expose] def conjC : NativeSporadic.Co1 →* GL24 :=
  MonoidHom.mk' (fun u => cG * (co1MatEquiv u : GL24) * cG⁻¹) fun u v => by
    rw [map_mul, Subgroup.coe_mul]
    group

theorem conjC_apply (u : NativeSporadic.Co1) :
    conjC u = cG * (co1MatEquiv u : GL24) * cG⁻¹ := rfl

theorem conjC_injective : Function.Injective conjC := by
  intro u v h
  rw [conjC_apply, conjC_apply, mul_left_inj, mul_right_inj] at h
  exact co1MatEquiv.injective (Subtype.ext h)

abbrev Cz : Subgroup NativeSporadic.Co1 := Subgroup.centralizer {epsMask eMaskA}

@[expose] def zC : Cz := ⟨epsMask eMaskA, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem coe_zC : (zC : NativeSporadic.Co1) = epsMask eMaskA := Subtype.coe_mk _ _

section


theorem rep_cG : MRep cRows cG :=
  ((((rep_AG.mul rep_zG).mul (rep_AG.inv letters_parts.1)).mul rep_iotaA).pow 2).mul rep_AG

theorem cG_conj : cG * zG * cG⁻¹ = aG := by
  have h := (rep_cG.mul rep_zG).mul (rep_cG.inv letters_parts.2.1)
  rw [letters_parts.2.2.1] at h
  exact h.eq rep_iotaA

theorem rep_conjC {u : NativeSporadic.Co1} {R : Rows} (h : MRep R (co1MatEquiv u : GL24)) :
    MRep (Native.mul (Native.mul cRows R) (Native.inv cRows)) (conjC u) :=
  (rep_cG.mul h).mul (rep_cG.inv letters_parts.2.1)

theorem conjC_epsA : conjC (epsMask eMaskA) = aG := cG_conj

theorem conjC_mem {u : NativeSporadic.Co1} (hu : u ∈ Cz) : conjC u ∈ cA := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [conjC_apply]
    exact GA.mul_mem (GA.mul_mem cG_mem (co1MatEquiv u).2) (GA.inv_mem cG_mem)
  · rw [Subgroup.mem_centralizer_singleton_iff, ← conjC_epsA, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 hu]

@[expose] def chiC : Cz →* cA := (conjC.domRestrict Cz).codRestrict cA fun u => conjC_mem u.2

theorem chiC_val (u : Cz) : (chiC u : GL24) = conjC u := rfl

theorem chiC_injective : Function.Injective chiC := by
  intro u v h
  have e := congrArg Subtype.val h
  rw [chiC_val, chiC_val] at e
  exact Subtype.ext (conjC_injective e)

theorem chiC_surjective : Function.Surjective chiC := by
  intro x
  obtain ⟨hxG, hxc⟩ := Subgroup.mem_inf.1 x.2
  have hxa := Subgroup.mem_centralizer_singleton_iff.1 hxc
  have hx : cG⁻¹ * (x : GL24) * cG ∈ GA := GA.mul_mem (GA.mul_mem (GA.inv_mem cG_mem) hxG) cG_mem
  have hu : conjC (co1MatEquiv.symm ⟨_, hx⟩) = x := by
    rw [conjC_apply, MulEquiv.apply_symm_apply]
    show cG * (cG⁻¹ * (x : GL24) * cG) * cG⁻¹ = x
    group
  have huC : co1MatEquiv.symm ⟨_, hx⟩ ∈ Cz := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply conjC_injective
    rw [map_mul, map_mul, hu, conjC_epsA]
    exact hxa
  exact ⟨⟨_, huC⟩, Subtype.ext (by rw [chiC_val]; exact hu)⟩

theorem chiC_zC : chiC zC = aC :=
  Subtype.ext (by rw [chiC_val, coe_zC, coe_aC]; exact conjC_epsA)

end

theorem epsHom_mem {K : Subgroup NativeSporadic.Co1} (hK : ∀ i, eps0 i ∈ K)
    (x : Multiplicative (Fin 11 → ZMod 2)) : epsHom x ∈ K := by
  obtain ⟨v, rfl⟩ := Multiplicative.ofAdd.surjective x
  have hs : ∀ s : Finset (Fin 11),
      epsHom (Multiplicative.ofAdd (∑ i ∈ s, Pi.single i (v i))) ∈ K := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, ofAdd_add, map_mul]
      refine K.mul_mem ?_ ih
      rcases CFSG.Sporadic.Co1.Cover.zmod2_cases (v j) with h0 | h1
      · rw [h0, Pi.single_zero, ofAdd_zero, map_one]
        exact K.one_mem
      · rw [h1, epsHom_single]
        exact hK j
  have := hs Finset.univ
  rwa [Finset.univ_sum_single] at this


@[expose] def sGen (l : ℕ) : NativeSporadic.Co1 :=
  if h : l < 11 then eps0 ⟨l, h⟩ else if h' : l - 11 < 4 then iota (t24Gen ⟨l - 11, h'⟩) else 1

theorem co1Sylow_le {K : Subgroup NativeSporadic.Co1} (hE : ∀ i, eps0 i ∈ K)
    (hT : ∀ j, iota (t24Gen j) ∈ K) : co1Sylow ≤ K := by
  have hT' : t24 ≤ K.comap iota := by
    rw [t24, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact hT j
  rintro _ ⟨s, hs, rfl⟩
  have hs' : s.right ∈ t24 := hs
  rw [theta_apply]
  exact K.mul_mem (epsHom_mem hE _) (hT' hs')


theorem sGen_mem (l : ℕ) : sGen l ∈ co1Sylow := by
  unfold sGen
  split_ifs with h h'
  · rw [← epsHom_single]
    exact epsHom_range_le_co1Sylow ⟨_, rfl⟩
  · rw [← theta_inr, theta_mem_co1Sylow_iff]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  · exact co1Sylow.one_mem

theorem closure_sGen : Subgroup.closure (sGen '' {l | l < 15}) = co1Sylow := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun _ ⟨l, _, he⟩ => he ▸ sGen_mem l)
    (co1Sylow_le (fun i => ?_) fun j => ?_)
  · have hi := i.isLt
    refine Subgroup.subset_closure ⟨i.val, by rw [Set.mem_setOf_eq]; omega, ?_⟩
    rw [sGen, dif_pos hi]
  · have hj := j.isLt
    have h1 : ¬ 11 + j.val < 11 := by omega
    have h2 : 11 + j.val - 11 < 4 := by omega
    have e : (⟨11 + j.val - 11, h2⟩ : Fin 4) = j := Fin.ext (Nat.add_sub_cancel_left ..)
    refine Subgroup.subset_closure ⟨11 + j.val, by rw [Set.mem_setOf_eq]; omega, ?_⟩
    rw [sGen, dif_neg h1, dif_pos h2, e]

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K
