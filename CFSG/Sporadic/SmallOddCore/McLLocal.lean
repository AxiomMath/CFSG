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

theorem tabRep_mclXInvs :
    ∀ j < mclXInvs.size, TabRep mclXInvs[j]! (mclXPerm j)⁻¹ := fun j hj => by
  have hj' : j < mclXGens.size := by simpa [mclXInvs] using hj
  exact invsOK_spec mclX_basic.2.2.1 hj' (tabRep_mclXGens j hj')

theorem card_mclX :
    Nat.card (genGroup 35 mclXGens mclXPerm) = 20160 := by
  rw [(enumerates_closure (genGroup_hA tabRep_mclXGens) (genGroup_hgens tabRep_mclXGens)
    mclX_enum.1).card, Array.length_toList, mclX_enum.2]

@[expose] def mclSylPerm (i j : ℕ) : Equiv.Perm (Fin 35) :=
  (((mclSylWords.getD i []).getD j []).map mclXPerm).prod

theorem mclSyl_word {i j : ℕ} (hj : j < (mclSylGens i).size) :
    j < (mclSylWords.getD i []).length ∧
      (mclSylWords.getD i []).getD j [] = (mclSylWords.getD i [])[j]'(by
        simpa [mclSylGens] using hj) ∧
      (mclSylGens i)[j]! = wordTabS 35 mclXGens ((mclSylWords.getD i []).getD j []) := by
  have hj' : j < (mclSylWords.getD i []).length := by simpa [mclSylGens] using hj
  have e2 : (mclSylWords.getD i []).getD j [] = (mclSylWords.getD i [])[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    rfl
  refine ⟨hj', e2, ?_⟩
  rw [getElem!_pos _ j hj, e2]
  simp [mclSylGens]

theorem mclSyl_lt {i j : ℕ} (hj : j < (mclSylGens i).size) :
    i < 4 ∧ ∀ l ∈ (mclSylWords.getD i []).getD j [], l < mclXGens.size := by
  obtain ⟨hj', e, -⟩ := mclSyl_word hj
  have hi : i < 4 := by
    by_contra h
    have e0 : mclSylWords.getD i [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [mclSylWords]; omega)]
      rfl
    rw [e0] at hj'
    simp at hj'
  exact ⟨hi, fun l hl => (mclX_sylow i hi).1 _ (e ▸ List.getElem_mem hj') l hl⟩

theorem tabRep_mclSylGens (i : ℕ) :
    ∀ j < (mclSylGens i).size, TabRep (mclSylGens i)[j]! (mclSylPerm i j) := fun j hj => by
  rw [(mclSyl_word hj).2.2]
  exact tabRep_wordTabS tabRep_mclXGens _ (mclSyl_lt hj).2

theorem mclSyl_le (i : ℕ) :
    genGroup 35 (mclSylGens i) (mclSylPerm i) ≤ genGroup 35 mclXGens mclXPerm := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, rfl⟩
  exact wordProd_mem_genGroup (mclSyl_lt hj).2

theorem mclSyl_enum {i : ℕ} (hi : i < 4) :
    Enumerates (genGroup 35 (mclSylGens i) (mclSylPerm i)) (mclSylEnum i).tabs.toList :=
  enumerates_closure (genGroup_hA (tabRep_mclSylGens i)) (genGroup_hgens (tabRep_mclSylGens i))
    (mclX_sylow i hi).2.1

theorem mclSyl_card {i : ℕ} (hi : i < 4) :
    Nat.card (genGroup 35 (mclSylGens i) (mclSylPerm i)) = mclSylSizes.getD i 0 := by
  rw [(mclSyl_enum hi).card, Array.length_toList, (mclX_sylow i hi).2.2.1]

theorem mclSyl_gen {i : ℕ} (hi : i < 4) (x : genGroup 35 mclXGens mclXPerm)
    (hx : (x : Equiv.Perm (Fin 35)) ∈ genGroup 35 (mclSylGens i) (mclSylPerm i))
    (hox : orderOf x = mclSylPrimes.getD i 0) :
    Subgroup.normalClosure ({x} : Set (genGroup 35 mclXGens mclXPerm)) = ⊤ := by
  obtain ⟨q, hq, hrep⟩ := (mclSyl_enum hi).exists_pos hx
  have hox' : orderOf (x : Equiv.Perm (Fin 35)) = mclSylPrimes.getD i 0 := by
    rw [Subgroup.orderOf_coe, hox]
  have hp1 : mclSylPrimes.getD i 0 ≠ 1 := by
    interval_cases i <;> decide
  rcases (mclX_sylow i hi).2.2.2 q hq with h | h | ⟨cs, W, h⟩
  · exfalso
    rw [h] at hrep
    have h1 : (x : Equiv.Perm (Fin 35)) = 1 := hrep.perm_eq TabRep.idTab
    rw [h1, orderOf_one] at hox'
    exact hp1 hox'.symm
  · exfalso
    apply h
    have hw := tabRep_wordTabS (gs := #[(mclSylEnum i).tabs[q]!])
      (f := fun _ => (x : Equiv.Perm (Fin 35))) (fun j hj => by
        have hj0 : j = 0 := by simpa using hj
        subst hj0
        simpa using hrep) (List.replicate (mclSylPrimes.getD i 0) 0)
      (fun j hj => by
        rw [List.eq_of_mem_replicate hj]
        simp)
    have h1 : (x : Equiv.Perm (Fin 35)) ^ mclSylPrimes.getD i 0 = 1 := by
      rw [← hox']
      exact pow_orderOf_eq_one _
    rw [List.map_replicate, List.prod_replicate, h1] at hw
    exact hw.tab_eq TabRep.idTab
  · exact normalClosure_eq_top_of_nclWordsOK tabRep_mclXGens tabRep_mclXInvs hrep h

theorem factorization_pow_mul_of_not_dvd {p k m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    (p ^ k * m).factorization p = k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hm]
  simp

theorem mclX_simple :
    IsSimpleGroup (genGroup 35 mclXGens mclXPerm) ∧
    ∃ a b : genGroup 35 mclXGens mclXPerm, a * b ≠ b * a := by
  have hcard := card_mclX
  have : Nontrivial (genGroup 35 mclXGens mclXPerm) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  have key : ∀ p, p.Prime → p ∣ Nat.card (genGroup 35 mclXGens mclXPerm) →
      p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    intro p hp hd
    have e : Nat.card (genGroup 35 mclXGens mclXPerm) = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by
      rw [hcard]
      norm_num
    rw [e] at hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h7
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h5
      · rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h3
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
        · exact Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5)))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7)))
  have hs : IsSimpleGroup (genGroup 35 mclXGens mclXPerm) :=
    isSimpleGroup_of_sylow_normalClosure_le _
      (fun p => genGroup 35 (mclSylGens (mclSylPrimes.idxOf p)) (mclSylPerm (mclSylPrimes.idxOf p)))
      (fun p => mclSyl_le _)
      (fun p hp hd => by
        rw [hcard]
        rcases key p hp hd with rfl | rfl | rfl | rfl
        · have e : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
          rw [e, factorization_pow_mul_of_not_dvd Nat.prime_two (by norm_num)]
          exact mclSyl_card (i := 0) (by norm_num)
        · have e : (20160 : ℕ) = 3 ^ 2 * 2240 := by norm_num
          rw [e, factorization_pow_mul_of_not_dvd Nat.prime_three (by norm_num)]
          exact mclSyl_card (i := 1) (by norm_num)
        · have e : (20160 : ℕ) = 5 ^ 1 * 4032 := by norm_num
          rw [e, factorization_pow_mul_of_not_dvd Nat.prime_five (by norm_num)]
          exact mclSyl_card (i := 2) (by norm_num)
        · have e : (20160 : ℕ) = 7 ^ 1 * 2880 := by norm_num
          rw [e, factorization_pow_mul_of_not_dvd (by norm_num) (by norm_num)]
          exact mclSyl_card (i := 3) (by norm_num))
      (fun p hp hd x hx hox => by
        rcases key p hp hd with rfl | rfl | rfl | rfl
        · exact mclSyl_gen (i := 0) (by norm_num) x hx hox
        · exact mclSyl_gen (i := 1) (by norm_num) x hx hox
        · exact mclSyl_gen (i := 2) (by norm_num) x hx hox
        · exact mclSyl_gen (i := 3) (by norm_num) x hx hox)
  refine ⟨hs, ?_⟩
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  let inst : CommGroup (genGroup 35 mclXGens mclXPerm) :=
    { (inferInstance : Group (genGroup 35 mclXGens mclXPerm)) with mul_comm := hcon }
  have hs' : @IsSimpleGroup _ (@CommGroup.toGroup _ inst) := hs
  have hp : (Nat.card (genGroup 35 mclXGens mclXPerm)).Prime := @IsSimpleGroup.prime_card _ inst hs'
  rw [hcard] at hp
  norm_num at hp

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
