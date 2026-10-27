module

public import CFSG.OddTranspositions.PartThree.Twelve.Six
public import CFSG.OddTranspositions.PartFour.LinePolar
public import CFSG.OddTranspositions.PartFour.Fourteen.OrthLines
import CFSG.OddTranspositions.WidthSylow
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Hom
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockSp
import CFSG.OddTranspositions.PartThree.Twelve.Five
import CFSG.OddTranspositions.PartThree.Nine.Setup
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.Timmesfeld.Connectivity
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

section Dihedral

variable {X : Type} [Group X] [Finite X] {E : Set X}

omit [Finite X] in
theorem conj_pow_mul_eq_inv {a b : X} (ha : a * a = 1) (hb : b * b = 1) (m : ℕ) :
    a * (a * b) ^ m * a⁻¹ = ((a * b) ^ m)⁻¹ := by
  have hai : a⁻¹ = a := (eq_inv_of_mul_eq_one_left ha).symm
  have hbi : b⁻¹ = b := (eq_inv_of_mul_eq_one_left hb).symm
  have h1 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, hai, hbi]
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha, one_mul]
  rw [← conj_pow, h1, inv_pow]

theorem orderOf_mul_le_ncard_inter_closure (hE : IsOddTransp E)
    (hN : ∀ g : X, ∀ x ∈ E, g * x * g⁻¹ ∈ E) {a b : X} (ha : a ∈ E) (hb : b ∈ E)
    (hab : ¬ Commute a b) :
    orderOf (a * b) ≤ (E ∩ (Subgroup.closure ({a, b} : Set X) : Set X)).ncard := by
  classical
  have ha2 : a * a = 1 := hE.mul_self_eq_one ha
  have hb2 : b * b = 1 := hE.mul_self_eq_one hb
  set k := orderOf (a * b) with hk
  have hodd : Odd k := hE.odd_of_not_commute ha hb hab
  have hkpos : 0 < k := hodd.pos
  have hconj : ∀ j : ℕ, (a * b) ^ (2 * j) * a = (a * b) ^ j * a * ((a * b) ^ j)⁻¹ := by
    intro j
    have h1 := conj_pow_mul_eq_inv ha2 hb2 j
    have hai : a⁻¹ = a := (eq_inv_of_mul_eq_one_left ha2).symm
    rw [hai] at h1
    calc (a * b) ^ (2 * j) * a = (a * b) ^ j * ((a * b) ^ j * a) := by
          rw [two_mul, pow_add, mul_assoc]
      _ = (a * b) ^ j * (a * (a * (a * b) ^ j * a)) := by
          congr 1
          calc (a * b) ^ j * a = (a * a) * (a * b) ^ j * a := by rw [ha2, one_mul]
            _ = a * (a * (a * b) ^ j * a) := by group
      _ = (a * b) ^ j * a * ((a * b) ^ j)⁻¹ := by rw [h1]; group
  obtain ⟨c, hc⟩ : ∃ c, 2 * c % k = 1 % k := by
    refine ⟨(k + 1) / 2, ?_⟩
    have hk2 : k % 2 = 1 := Nat.odd_iff.mp hodd
    have h2 : 2 * ((k + 1) / 2) = 1 + k := by omega
    rw [h2, Nat.add_mod_right]
  let φ : ℕ → X := fun i => (a * b) ^ i * a
  have hmem : ∀ i, φ i ∈ E ∩ (Subgroup.closure ({a, b} : Set X) : Set X) := by
    intro i
    refine ⟨?_, ?_⟩
    · have h1 : (a * b) ^ (2 * (c * i)) = (a * b) ^ i := by
        rw [← pow_mod_orderOf, ← hk, ← mul_assoc, Nat.mul_mod, hc, ← Nat.mul_mod,
          one_mul, pow_mod_orderOf]
      show (a * b) ^ i * a ∈ E
      rw [← h1, hconj]
      exact hN _ _ ha
    · have hamem : a ∈ Subgroup.closure ({a, b} : Set X) := Subgroup.subset_closure (by simp)
      have hbmem : b ∈ Subgroup.closure ({a, b} : Set X) := Subgroup.subset_closure (by simp)
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mul_mem _ hamem hbmem) _) hamem
  have hinj : Set.InjOn φ (Set.Iio k) := by
    intro i hi j hj h
    have h1 : (a * b) ^ i = (a * b) ^ j := mul_right_cancel h
    exact pow_injOn_Iio_orderOf hi hj h1
  calc k = (Set.Iio k).ncard := by rw [Set.ncard_eq_toFinset_card', Set.toFinset_Iio]; simp
    _ = (φ '' Set.Iio k).ncard := (hinj.ncard_image).symm
    _ ≤ _ := Set.ncard_le_ncard (by rintro _ ⟨i, -, rfl⟩; exact hmem i) (Set.toFinite _)

omit [Finite X] in
theorem inter_closure_subset_lineMem {a b : X} :
    E ∩ (Subgroup.closure ({a, b} : Set X) : Set X) ⊆ lineMem E a b := by
  rintro z ⟨hzE, hz⟩
  refine ⟨hzE, fun y ⟨⟨hyE, hya⟩, ⟨_, hyb⟩⟩ => ⟨hyE, ?_⟩⟩
  have hle : Subgroup.closure ({a, b} : Set X) ≤ Subgroup.centralizer {y} := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hya.eq.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hyb.eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hz)).symm

omit [Finite X] in
theorem lineMem_conj (hN : ∀ g : X, ∀ x ∈ E, g * x * g⁻¹ ∈ E) (g : X) (a b : X) :
    lineMem E (g * a * g⁻¹) (g * b * g⁻¹) = (MulAut.conj g) '' lineMem E a b := by
  have hiff : ∀ z, z ∈ E ↔ g * z * g⁻¹ ∈ E := fun z => ⟨fun h => hN g z h, fun h => by
    have := hN g⁻¹ _ h
    simpa [mul_assoc] using this⟩
  have hcomm : ∀ u v : X, Commute (g * u * g⁻¹) (g * v * g⁻¹) ↔ Commute u v :=
    fun u v => Commute.conj_iff g
  ext z
  obtain ⟨z, rfl⟩ := (MulAut.conj g).surjective z
  rw [(MulAut.conj g).injective.mem_set_image]
  simp only [MulAut.conj_apply, mem_lineMem, perpMem, Set.subset_def, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨(hiff z).mpr hz, fun y ⟨⟨hyE, hya⟩, ⟨_, hyb⟩⟩ => ⟨hyE, ?_⟩⟩
    have := h (g * y * g⁻¹) ⟨⟨hiff y |>.mp hyE, (hcomm y a).mpr hya⟩,
      ⟨hiff y |>.mp hyE, (hcomm y b).mpr hyb⟩⟩
    exact (hcomm y z).mp this.2
  · rintro ⟨hz, h⟩
    refine ⟨(hiff z).mp hz, fun y ⟨⟨hyE, hya⟩, ⟨_, hyb⟩⟩ => ⟨hyE, ?_⟩⟩
    obtain ⟨y, rfl⟩ := (MulAut.conj g).surjective y
    rw [MulAut.conj_apply] at hyE hya hyb ⊢
    have := h y ⟨⟨(hiff y).mpr hyE, (hcomm y a).mp hya⟩, ⟨(hiff y).mpr hyE, (hcomm y b).mp hyb⟩⟩
    exact (hcomm y z).mpr this.2

omit [Finite X] in
theorem orderOf_mul_mk_eq (hE : IsOddTransp E) {N : Subgroup X} [N.Normal]
    (hNZ : N ≤ Subgroup.center X) {a b : X} (ha : a ∈ E) (hb : b ∈ E) (hab : ¬ Commute a b) :
    orderOf (QuotientGroup.mk' N a * QuotientGroup.mk' N b) = orderOf (a * b) := by
  have ha2 : a * a = 1 := hE.mul_self_eq_one ha
  have hb2 : b * b = 1 := hE.mul_self_eq_one hb
  have hodd : Odd (orderOf (a * b)) := hE.odd_of_not_commute ha hb hab
  rw [← map_mul]
  set m := orderOf (QuotientGroup.mk' N (a * b)) with hm
  have hdvd1 : m ∣ orderOf (a * b) := orderOf_map_dvd _ _
  refine Nat.dvd_antisymm hdvd1 ?_
  have hz : (a * b) ^ m ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, hm, pow_orderOf_eq_one]
  have hzc := hNZ hz
  have h1 := conj_pow_mul_eq_inv ha2 hb2 m
  rw [show a * (a * b) ^ m * a⁻¹ = (a * b) ^ m by
    rw [Subgroup.mem_center_iff.mp hzc a, mul_inv_cancel_right]] at h1
  have h2 : (a * b) ^ (2 * m) = 1 := by
    rw [two_mul, pow_add]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel _
  have h3 : orderOf (a * b) ∣ 2 * m := orderOf_dvd_of_pow_eq_one h2
  exact (Nat.Coprime.dvd_mul_left hodd.coprime_two_right).mp h3

end Dihedral

section Lines

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem image_setOf_isConj {X Y : Type} [Group X] [Group Y] {φ : X →* Y}
    (hφ : Function.Surjective φ) (t : X) :
    φ '' {g | IsConj t g} = {y | IsConj (φ t) y} := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨c, rfl⟩ := isConj_iff.mp (show IsConj t g from hg)
    exact isConj_iff.mpr ⟨φ c, by simp⟩
  · intro hy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hy
    obtain ⟨c', rfl⟩ := hφ c
    exact ⟨c' * t * c'⁻¹, isConj_iff.mpr ⟨c', rfl⟩, by simp⟩

theorem exists_lineMem_ncard_eq_of_model (hIH : Theorem4Below (Nat.card G)) (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s) {N : ℕ}
    (hmodel : ∀ (X : Type) [Group X], Subgroup.center X = ⊥ → ∀ t : X,
      CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X n f t →
      ∃ v ∈ {x | IsConj t x}, ∃ w ∈ {x | IsConj t x}, ¬ Commute v w ∧ orderOf (v * w) = N ∧
        {z | z ∈ {x | IsConj t x} ∧ ∀ y ∈ {x | IsConj t x}, Commute y v → Commute y w →
          Commute y z}.ncard ≤ N) :
    ∃ w ∈ D, ¬ Commute w hC.d ∧ (lineMem D hC.d w).ncard = N := by
  classical
  have hZ := center_Hbar_eq_bot hC
  have hne := (subset_rootBlock_and_ne_of_isSymplecticTransvection (imageClass_isClass hC) hZ hs
    hSp).2
  obtain ⟨b₀, hb₀, hsb₀⟩ := exists_not_commute_of_rootBlock_ne (imageClass_isClass hC) hs hne s hs
  obtain ⟨xH, hxH, hxs⟩ := hs
  obtain ⟨yH, hyH, rfl⟩ := hb₀
  have hx : (xH : G) ∈ commSet D hC.d := by
    rw [← Nine.DalphaStar_eq_commSet hC hα]
    exact (mem_DstarH_iff hC).mp hxH
  have hy : (yH : G) ∈ commSet D hC.d := by
    rw [← Nine.DalphaStar_eq_commSet hC hα]
    exact (mem_DstarH_iff hC).mp hyH
  have hxy : ¬ Commute (xH : G) (yH : G) := fun h =>
    hsb₀ (by rw [← hxs]; exact (commute_iff_commute_mk hC hMZ hα hx hy).mp h)
  have hs' : s ∈ imageClass hC := ⟨xH, hxH, hxs⟩
  set x : G := (xH : G)
  set y : G := (yH : G)
  have hdΓ := d_mem_commSet_inter hC hx hy
  set Ω := compSet D x y hC.d with hΩdef
  have hΩΓ : Ω = commSet D x ∩ commSet D y :=
    compSet_eq_of_not_disconnected hdΓ (not_disconnected_commSet_inter hC hMZ hα hs' hn hf hSp
      hx hy hxy)
  have hloc : ∀ v ∈ Ω, LocalPivot D x y v := fun v hv =>
    localPivot_of_mem hC hMZ hα hs' hn hf hSp hv.1.1.1
      ⟨hx.1, hv.1.1.2.1.symm, fun h => hv.1.1.2.2 h.symm⟩
      ⟨hy.1, hv.1.2.2.1.symm, fun h => hv.1.2.2.2 h.symm⟩ hxy
  have hcls := isClass_inClosure_compSet hC.setup.normal hC.setup.oddT hdΓ
    (fun v hv => (hloc v hv).2.1) (fun v hv => (hloc v hv).2.2.1)
  have hS := setup_inClosure hC.setup.oddT (fun z hz => hz.1.1.1) hcls
  have hcen := solvableRadical_le_center_of_noTwins hS
    (noOpenTwins_inClosure_compSet (fun v hv => (hloc v hv).1) fun v hv => (hloc v hv).2.2.2.2)
    (noClosedTwins_inClosure_compSet fun v hv => (hloc v hv).2.2.2.1)
  obtain ⟨t, ht, hOt⟩ := twelveSix_sp_component hIH hC hMZ hα hs' hn hf hSp hx hy hxy
  set S := Subgroup.closure Ω with hSdef
  set R := CFSG.solvableRadical S with hRdef
  have hRZ : R = Subgroup.center S :=
    le_antisymm hcen (CFSG.OddTranspositions.center_le_solvableRadical S)
  have hZX : Subgroup.center (S ⧸ R) = ⊥ := by
    have h1 := CFSG.OddTranspositions.center_le_solvableRadical (S ⧸ R)
    rwa [CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_quotient, le_bot_iff] at h1
  set tS : S := ⟨t, Subgroup.subset_closure ht⟩ with htS
  have hOX : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection (S ⧸ R) n f
      (QuotientGroup.mk' R tS) := by
    refine isOrthReflection_of_centerQuotient
      (((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot).trans
        (QuotientGroup.quotientMulEquivOfEq hRZ)) ?_ hOt
    rfl
  obtain ⟨v, hv, w, hw, hvw, hord, hline⟩ := hmodel (S ⧸ R) hZX _ hOX
  have hclsΩ : inClosure Ω = {g | IsConj tS g} := by
    obtain ⟨t₀, ht₀⟩ := hcls
    have htt : IsConj t₀ tS := by
      have : tS ∈ inClosure Ω := ht
      rw [ht₀] at this
      exact this
    rw [ht₀]
    ext g
    exact ⟨fun h => (isConj_comm.mp htt).trans h, fun h => htt.trans h⟩
  have himgE : QuotientGroup.mk' R '' inClosure Ω = {z | IsConj (QuotientGroup.mk' R tS) z} := by
    rw [hclsΩ]
    exact image_setOf_isConj (QuotientGroup.mk'_surjective R) tS
  rw [← himgE] at hv hw
  obtain ⟨a, ha, rfl⟩ := hv
  obtain ⟨b, hb, rfl⟩ := hw
  have hE := isOddTransp_inClosure (Ω := Ω) hC.setup.oddT (fun z hz => hz.1.1.1)
  have hnc := exists_not_commute_of_setup hS
    (not_isSolvable_closure_of_subset hC hMZ hα hs' hn hf hSp hx hy hxy
      (gammaAt_self_subset_compSet hdΓ))
  have hRZ' : R ≤ Subgroup.center S := hRZ.le
  have hinj := injOn_mk_of_le_center hE hRZ' hnc
  have hab : ¬ Commute a b := fun h => hvw (h.map _)
  have hcommiff : ∀ c ∈ inClosure Ω, ∀ c' ∈ inClosure Ω,
      (Commute c c' ↔ Commute (QuotientGroup.mk' R c) (QuotientGroup.mk' R c')) :=
    fun c hc c' hc' => ⟨fun h => h.map _, commute_of_commute_mk_of_le_center' hE hRZ' hc hc'⟩
  have hordG : orderOf ((a : G) * (b : G)) = N := by
    rw [← hord, orderOf_mul_mk_eq hE hRZ' ha hb hab]
    exact Subgroup.orderOf_coe (a * b)
  have habG : ¬ Commute (a : G) (b : G) := fun h => hab (Subtype.ext h.eq)
  have haD : (a : G) ∈ D := ha.1.1.1
  have hbD : (b : G) ∈ D := hb.1.1.1
  have hlow : N ≤ (lineMem D (a : G) (b : G)).ncard := by
    rw [← hordG]
    exact (orderOf_mul_le_ncard_inter_closure hC.setup.oddT
      (fun g z hz => hC.setup.conj_mem g hz) haD hbD habG).trans
      (Set.ncard_le_ncard inter_closure_subset_lineMem (Set.toFinite _))
  have hsubΓ : lineMem D (a : G) (b : G) ⊆ Ω := by
    intro z hz
    rw [hΩΓ]
    have hxab : x ∈ perpMem D (a : G) ∩ perpMem D (b : G) :=
      ⟨⟨hx.1, (ha.1.1 : (a : G) ∈ commSet D x).2.1.symm⟩,
        ⟨hx.1, (hb.1.1 : (b : G) ∈ commSet D x).2.1.symm⟩⟩
    have hyab : y ∈ perpMem D (a : G) ∩ perpMem D (b : G) :=
      ⟨⟨hy.1, (ha.1.2 : (a : G) ∈ commSet D y).2.1.symm⟩,
        ⟨hy.1, (hb.1.2 : (b : G) ∈ commSet D y).2.1.symm⟩⟩
    have hzx := (hz.2 hxab).2
    have hzy := (hz.2 hyab).2
    refine ⟨⟨hz.1, hzx.symm, fun h => hxy ?_⟩, ⟨hz.1, hzy.symm, fun h => hxy ?_⟩⟩
    · rw [h] at hzy
      exact hzy.symm
    · rw [h] at hzx
      exact hzx
  have hup : (lineMem D (a : G) (b : G)).ncard ≤ N := by
    refine le_trans ?_ hline
    refine Set.ncard_le_ncard_of_injOn (fun z => QuotientGroup.mk' R
      (if hz : z ∈ Ω then (⟨z, Subgroup.subset_closure hz⟩ : S) else 1)) ?_ ?_ (Set.toFinite _)
    · intro z hz
      have hzΩ := hsubΓ hz
      simp only [dif_pos hzΩ]
      have hmemE : QuotientGroup.mk' R (⟨z, Subgroup.subset_closure hzΩ⟩ : S) ∈
          {x | IsConj (QuotientGroup.mk' R tS) x} := by
        rw [← himgE]
        exact ⟨_, hzΩ, rfl⟩
      refine ⟨hmemE, ?_⟩
      intro u hu hua hub
      rw [← himgE] at hu
      obtain ⟨γ, hγ, rfl⟩ := hu
      have hγa : Commute γ a := (hcommiff γ hγ a ha).mpr hua
      have hγb : Commute γ b := (hcommiff γ hγ b hb).mpr hub
      have hγz : Commute (γ : G) z :=
        (hz.2 ⟨⟨hγ.1.1.1, congrArg Subtype.val hγa.eq⟩, ⟨hγ.1.1.1, congrArg Subtype.val hγb.eq⟩⟩).2
      exact Commute.map (show Commute γ (⟨z, Subgroup.subset_closure hzΩ⟩ : S) from
        Subtype.ext hγz.eq) _
    · intro z hz z' hz' h
      have hzΩ := hsubΓ hz
      have hzΩ' := hsubΓ hz'
      simp only [dif_pos hzΩ, dif_pos hzΩ'] at h
      exact congrArg Subtype.val (hinj hzΩ hzΩ' h)
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj haD hC.hd)
  refine ⟨g * b * g⁻¹, hC.setup.conj_mem g hbD, fun h => habG ?_, ?_⟩
  · rw [← hg] at h
    exact (Commute.conj_iff g).mp h.symm
  · rw [← hg, lineMem_conj (fun g' z hz => hC.setup.conj_mem g' hz),
      Set.ncard_image_of_injective _ (MulAut.conj g).injective]
    exact le_antisymm hup hlow

theorem twelveSeven_sp_exists (hIH : Theorem4Below (Nat.card G)) (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s) :
    (∃ w ∈ D, ¬ Commute w hC.d ∧ (lineMem D hC.d w).ncard = 2 ^ f + 1) ∧
      ∃ w ∈ D, ¬ Commute w hC.d ∧ (lineMem D hC.d w).ncard = 2 ^ f - 1 :=
  ⟨exists_lineMem_ncard_eq_of_model hIH hC hMZ hα hs hn hf hSp fun _ _ hZ _ hO =>
      exists_hypLine_succ_of_isOrthReflection hZ hf hO,
    exists_lineMem_ncard_eq_of_model hIH hC hMZ hα hs hn hf hSp fun _ _ hZ _ hO =>
      exists_hypLine_pred_of_isOrthReflection hZ hf hO⟩

end Lines

end CFSG.OddTranspositions.PartThree

end
