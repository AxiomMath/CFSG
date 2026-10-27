module

public import CFSG.Sporadic.SmallOddCore.McL
public import CFSG.Sporadic.SmallOddCore.McLLocalCheck
public import CFSG.Sporadic.SmallOddCore.CompImage
public import CFSG.Sporadic.SmallOddCore.LocalTransport
public import CFSG.Sporadic.SuzOddCore.Restrict

public noncomputable section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Blueprint
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.SuzOddCore
open CFSG.LocalAnalysis.ComponentInitial CFSG.Sporadic.SmallOddCore.Native

abbrev mclT0 : Equiv.Perm (Fin 275) := tp 275 (mclCentTbl 4)

abbrev mclCt : Subgroup (Equiv.Perm (Fin 275)) := mclP ⊓ centralizer ({mclT0} : Set _)

theorem mclT0_facts :
    mclT0 ∈ mclP ∧ orderOf mclT0 = 2 ∧
    closure (tp 275 '' {x | x ∈ [mclCentTbl 5, mclCentTbl 6].toArray}) = mclCt ∧
    Nat.card mclCt = 40320 ∧
    ∀ τ ∈ mclP, orderOf τ = 2 → ∃ g ∈ mclP, τ = g * mclT0 * g⁻¹ := by
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := mcl_involution_centralizers
  obtain ⟨-, h2, h3, h4, h5, -⟩ := hrows _ List.mem_cons_self
  dsimp only [mclC] at h2 h3 h4 h5
  have hP : mclT0 ∈ mclP := by
    by_contra h
    exact Bool.false_ne_true (h3.2 h)
  refine ⟨hP, h2, h4, h5, fun τ hτ hτ2 => ?_⟩
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover τ (Subgroup.mem_sup_left hτ) hτ2
  have key : ∀ x : Equiv.Perm (Fin 275), g * x * g⁻¹ ∈ mclP → x ∈ mclP := fun x hx => by
    have := mclP.mul_mem (mclP.mul_mem (mclP.inv_mem hg) hx) hg
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  simp only [mclRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨g, hg, ?_⟩
    dsimp only
  · exfalso
    obtain ⟨-, -, h3', -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
    dsimp only at h3' hτ
    exact h3'.1 rfl (key _ hτ)

theorem rep_mclT0 : CFSG.Monster.B.Co2.Rep 275 mclT0Arr mclT0 :=
  co2Rep_natArr_iff.2 (rep_tp mclX_basic.2.2.2.2.1)

theorem mem_mclFix
    (x : Fin 275) : (x : ℕ) ∈ mclFix ↔ mclT0 x = x := by
  rw [mclFix, fixedList, List.mem_filter, List.mem_range, beq_iff_eq, rep_mclT0 x]
  exact ⟨fun h => Fin.ext h.2, fun h => ⟨x.2, by rw [h]⟩⟩

theorem mclFix_points : PointsList 275 35 mclFix where
  len := mclX_basic.1
  lt x hx := by
    rw [mclFix, fixedList, List.mem_filter, List.mem_range] at hx
    exact hx.1
  nodup := List.nodup_range.filter _

theorem mclCt_preserves :
    ∀ g ∈ mclCt, ∀ x : Fin 275, (x : ℕ) ∈ mclFix → (g x : ℕ) ∈ mclFix := by
  intro g hg x hx
  rw [mem_mclFix] at hx ⊢
  have hc := mem_centralizer_singleton_iff.1 (mem_inf.1 hg).2
  rw [← Equiv.Perm.mul_apply, ← hc, Equiv.Perm.mul_apply, hx]

@[expose] def mclRho : mclCt →* Equiv.Perm (Fin 35) :=
  mclFix_points.restrHom mclCt mclCt_preserves

theorem mclCGen_mem
    {k : ℕ} (hk : k < 2) : tp 275 (mclCentTbl (k + 5)) ∈ mclCt := by
  rw [← mclT0_facts.2.2.1]
  refine subset_closure ⟨mclCentTbl (k + 5), ?_, rfl⟩
  interval_cases k <;> simp

@[expose] def mclCGen
    (k : ℕ) : mclCt :=
  if hk : k < 2 then ⟨tp 275 (mclCentTbl (k + 5)), mclCGen_mem hk⟩ else 1

@[expose] def mclXPerm
    (k : ℕ) : Equiv.Perm (Fin 35) := mclRho (mclCGen k)

theorem tabRep_mclXGens :
    ∀ k < mclXGens.size, TabRep mclXGens[k]! (mclXPerm k) := by
  intro k hk
  have hk2 : k < 2 := by simpa [mclXGens] using hk
  have h1 : mclXGens[k]! = restrictArr mclFix (natArr (mclCentTbl (k + 5))) := by
    rw [mclXGens, getElem!_pos _ k (by simpa using hk2), Array.getElem_ofFn]
  rw [h1, mclXPerm]
  refine mclFix_points.tabRep_restrHom _ _ _ ?_
  simp only [mclCGen, hk2, ↓reduceDIte]
  exact co2Rep_natArr_iff.2 (rep_tp (mclX_basic.2.2.2.2.2 k hk2))

theorem mclX_cert :
    ClassCert 35 mclXGens mclXInvs mclXEnum 14 mclXWords mclXSizes mclXOrbits where
  enum := mclX_enum.1
  words_lt := mclX_orbits.2.2.1
  rep0 := mclX_orbits.2.2.2
  orbit := mclX_orbits.1
  notIn := mclX_orbits.2.1
  cover := by
    intro k hk
    obtain ⟨l, hl, hf⟩ := cover_of_coverAllOK mclX_cover k hk
    exact ⟨l, by rw [mclX_basic.2.2.2.1] at hl; exact hl, hf⟩

theorem mclX_simple :
    IsSimpleGroup (genGroup 35 mclXGens mclXPerm) ∧
    ∃ a b : genGroup 35 mclXGens mclXPerm, a * b ≠ b * a :=
  isSimpleGroup_of_classCert tabRep_mclXGens mclX_cert (by norm_num)
    (by rw [mclX_enum.2]; norm_num) (by rw [mclX_enum.2]; exact mclX_sums) ⟨1, by decide⟩

theorem card_mclX :
    Nat.card (genGroup 35 mclXGens mclXPerm) = 20160 := by
  rw [(genGroup_enumerates tabRep_mclXGens mclX_cert).card, Array.length_toList, mclX_enum.2]

theorem mclX_le_range :
    genGroup 35 mclXGens mclXPerm ≤ mclRho.range := by
  rw [genGroup, closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact ⟨mclCGen k, rfl⟩

theorem mclT0_mem_Ct :
    mclT0 ∈ mclCt :=
  mem_inf.mpr ⟨mclT0_facts.1, mem_centralizer_singleton_iff.mpr rfl⟩

theorem mclT0_mem_ker :
    (⟨mclT0, mclT0_mem_Ct⟩ : mclCt) ∈ mclRho.ker := by
  rw [MonoidHom.mem_ker, mclRho, PointsList.restrHom_eq_one_iff]
  intro x hx
  rw [Subgroup.coe_mk]
  exact (mem_mclFix x).1 hx

theorem mclRho_range :
    mclRho.range = genGroup 35 mclXGens mclXPerm ∧ Nat.card mclRho.ker = 2 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup mclRho.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange mclRho).toEquiv,
    mclT0_facts.2.2.2.1] at h
  have hker2 : 2 ≤ Nat.card mclRho.ker := by
    have hne : (⟨⟨mclT0, mclT0_mem_Ct⟩, mclT0_mem_ker⟩ : mclRho.ker) ≠ 1 := by
      intro h1
      have h1' : mclT0 = 1 :=
        congrArg (fun x : mclRho.ker => ((x : mclCt) : Equiv.Perm (Fin 275))) h1
      have h2 := mclT0_facts.2.1
      rw [h1', orderOf_one] at h2
      norm_num at h2
    have : Nontrivial mclRho.ker := ⟨⟨_, 1, hne⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.mpr this
  have hle := Subgroup.card_le_of_le mclX_le_range
  rw [card_mclX] at hle
  obtain ⟨a, ha⟩ : ∃ a, Nat.card mclRho.range = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, Nat.card mclRho.ker = b := ⟨_, rfl⟩
  rw [ha, hb] at h
  rw [hb] at hker2
  rw [ha] at hle
  have h1 : a * 2 ≤ a * b := Nat.mul_le_mul_left a hker2
  rw [← h] at h1
  have ha' : a = 20160 := by omega
  subst ha'
  refine ⟨(Subgroup.eq_of_le_of_card_ge mclX_le_range (by rw [card_mclX, ha])).symm, ?_⟩
  rw [hb]
  omega

theorem mclCt_component
    {B : Subgroup (Equiv.Perm (Fin 275))}
    (hB : CFSG.Assembly.IsComponentOf B mclCt) :
    Nat.card ↥(mclCt ⊓ centralizer (B : Set (Equiv.Perm (Fin 275)))) = 2 := by
  obtain ⟨hrange, hker⟩ := mclRho_range
  have hkerZ : mclRho.ker ≤ center mclCt := by
    have hz : zpowers (⟨mclT0, mclT0_mem_Ct⟩ : mclCt) = mclRho.ker := by
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr mclT0_mem_ker)
      rw [hker, Nat.card_zpowers, Subgroup.orderOf_mk, mclT0_facts.2.1]
    rw [← hz, zpowers_le, mem_center_iff]
    intro g
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 g.2).2
  obtain ⟨hs, hnab⟩ := mclX_simple
  have hs' : IsSimpleGroup mclRho.range := by
    rw [hrange]
    exact hs
  have hnab' : ∃ a b : mclRho.range, a * b ≠ b * a := by
    rw [hrange]
    exact hnab
  have hcen : center mclRho.range = ⊥ := center_eq_bot_of_simple' hs' hnab'
  have hsurj := mclRho.rangeRestrict_surjective
  have hkerS : Group.IsSolvable mclRho.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have hp : IsPGroup 2 mclRho.ker := IsPGroup.of_card (n := 1) (by rw [hker, pow_one])
    have : Group.IsNilpotent mclRho.ker := hp.isNilpotent
    infer_instance
  have hkerZ' : mclRho.rangeRestrict.ker ≤ center mclCt := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hkerZ
  have hB' := (isComponentOf_iff_isComponent_subgroupOf hB.1).1 hB
  have hmap := map_eq_top_of_isComponent mclRho.rangeRestrict hsurj hkerS hs' hB'
  rw [card_inf_centralizer_subgroupOf hB.1,
    centralizer_eq_center_of_map_eq_top mclRho.rangeRestrict hmap hkerZ',
    center_eq_ker_of_surjective mclRho.rangeRestrict hsurj hcen hkerZ',
    MonoidHom.ker_rangeRestrict, hker]

theorem mclP_local_components :
    ∀ τ ∈ mclP, orderOf τ = 2 →
    ∀ B : Subgroup (Equiv.Perm (Fin 275)),
      CFSG.Assembly.IsComponentOf B (mclP ⊓ centralizer ({τ} : Set _)) →
        Nat.card ↥(mclP ⊓ centralizer ({τ} : Set _) ⊓
          centralizer (B : Set (Equiv.Perm (Fin 275)))) = 2 :=
  fun τ hτP hτ B hB => card_local_of_reps {mclT0}
    (fun τ hτP hτ => by
      obtain ⟨g, hg, h⟩ := mclT0_facts.2.2.2.2 τ hτP hτ
      exact ⟨mclT0, rfl, g, hg, h⟩)
    (fun r hr B hB => by
      rw [Set.mem_singleton_iff] at hr
      subst hr
      exact mclCt_component hB) hτP hτ hB

theorem cti_mcl_involution_local_component_centralizer_order_two
    {T : Type*} [Group T]
    (hT : Nonempty (T ≃* NativeSporadic.McL)) {t : T} (ht : orderOf t = 2) {B : Subgroup T}
    (hB : CFSG.Assembly.IsComponentOf B (centralizer ({t} : Set T))) :
    Nat.card ↥(centralizer ({t} : Set T) ⊓ centralizer (B : Set T)) = 2 := by
  obtain ⟨e⟩ := hT
  exact card_local_of_model (e.trans mclPermEquiv) mclP_local_components ht hB

end CFSG.Sporadic.SmallOddCore
