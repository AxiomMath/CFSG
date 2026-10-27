module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Kbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeNaturalProduct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Gl3K
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearDirectProductProjection
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Bridge
public import CFSG.GroupTheory.Fitting.MulEquiv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private noncomputable def s16e3IncK {W : Type} [CommGroup W]
    (A B : Subgroup (MulAut W)) :
    ↥(s1t3KBar A B) →* ↥A :=
  Subgroup.inclusion (inf_le_left : A ⊓ Subgroup.centralizer (B : Set (MulAut W)) ≤ A)

private theorem s16e3IncK_injective {W : Type} [CommGroup W]
    (A B : Subgroup (MulAut W)) :
    Function.Injective (s16e3IncK A B) := by
  intro x y hxy
  have h : (x : MulAut W) = (y : MulAut W) := by
    have h' := congrArg (fun z : ↥A => (z : MulAut W)) hxy
    exact h'
  exact Subtype.ext_iff.mpr h


private theorem s16e3_quasisimple_B {W : Type} [CommGroup W]
    {A B T : Subgroup (MulAut W)} (h : ThreeNat A B T) :
    CFSG.IsQuasisimple ↥B :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥B).mp
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥B).mpr
      h.quasi)

private theorem s16e3_quasisimple_B_subgroupOf {W : Type} [CommGroup W]
    {A B T : Subgroup (MulAut W)} (h : ThreeNat A B T) :
    CFSG.IsQuasisimple ↥(B.subgroupOf A) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe h.le).symm (s16e3_quasisimple_B h)


variable {W : Type} [CommGroup W] [Finite W] {A B T : Subgroup (MulAut W)}


private theorem s16e3_exists_fano_kBar_injective
    (h : ThreeNat A B T) (h7 : Nat.card ↥(irrSet B) = 7) :
    ∃ π : ↥(s1t3KBar A B) →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2),
      Function.Injective π := by
  classical
  let K : Subgroup (MulAut W) := s1t3KBar A B
  have hKA : K ≤ A := inf_le_left
  obtain ⟨r, hr, -⟩ := ThreeNat.exists_fano_rep h h7
  let π : ↥K →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    r.comp (s16e3IncK A B)
  have hπ_inj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    have hfix : ∀ J ∈ irrSet B, J.map (k : MulAut W).toMonoidHom = J := by
      intro J hJ
      have h1 : π k = 1 := MonoidHom.mem_ker.mp hk
      have h2 : r (s16e3IncK A B k) = 1 := by
        simpa [π] using h1
      exact (hr (s16e3IncK A B k)).mp h2 J hJ
    exact Subtype.ext (ThreeNat.eq_one_of_kBar_fix h (by simp [K]) hfix)
  exact ⟨π, hπ_inj⟩

private theorem s16e3_exists_bk_product
    (h : ThreeNat A B T) (h7 : Nat.card ↥(irrSet B) = 7)
    (hL3 : IsL3 ↥B 1) :
    ∃ eAK : ↥A ≃* ↥B × ↥(s1t3KBar A B),
      (∀ b : ↥B, eAK (Subgroup.inclusion h.le b) = (b, 1)) ∧
      (∀ k : ↥(s1t3KBar A B),
        eAK (s16e3IncK A B k) = (1, k)) ∧
      (∀ (b : ↥B) (k : ↥(s1t3KBar A B)),
        eAK (Subgroup.inclusion h.le b *
          s16e3IncK A B k) = (b, k)) ∧
      (∀ (b : ↥B) (k : ↥(s1t3KBar A B)),
        eAK.symm (b, k) = Subgroup.inclusion h.le b *
          s16e3IncK A B k) ∧
      B ⊓ s1t3KBar A B = ⊥ ∧
      (∀ b ∈ B, ∀ k ∈ s1t3KBar A B, b * k = k * b) := by
  classical
  have hKA : s1t3KBar A B ≤ A := inf_le_left
  obtain ⟨N, -, hBN, -, hNKcomm, hNKbot, -, -⟩ := ThreeNat.structure_of_seven h h7
  have hBKbot : B ⊓ s1t3KBar A B = ⊥ := by
    apply le_bot_iff.mp
    calc B ⊓ s1t3KBar A B ≤ N ⊓ s1t3KBar A B := inf_le_inf_right (s1t3KBar A B) hBN
      _ = ⊥ := hNKbot
  have hBKcomm : ∀ b ∈ B, ∀ k ∈ s1t3KBar A B, b * k = k * b :=
    fun b hb k hk => hNKcomm b (hBN hb) k hk
  have hBKsup : B ⊔ s1t3KBar A B = A := ThreeNat.sup_kBar_eq_of_isL3 h h7 hL3
  obtain ⟨fBK, hfBK_left, hfBK_right⟩ :=
    CFSG.GorensteinWalter.subgroup_sup_exists_prod_equiv_of_commute_of_disjoint
      B (s1t3KBar A B) hBKbot (fun b k hb hk => hBKcomm b hb k hk)
  let eAK : ↥A ≃* ↥B × ↥(s1t3KBar A B) :=
    (MulEquiv.subgroupCongr hBKsup).symm.trans fBK
  have heAK_left : ∀ b : ↥B, eAK (Subgroup.inclusion h.le b) = (b, 1) := by
    intro b
    dsimp [eAK]
    rw [show (MulEquiv.subgroupCongr hBKsup).symm (Subgroup.inclusion h.le b) =
        (⟨b, Subgroup.mem_sup_left b.2⟩ : ↥(B ⊔ s1t3KBar A B)) by
          apply Subtype.ext
          rfl,
      hfBK_left]
  have heAK_right : ∀ k : ↥(s1t3KBar A B), eAK (s16e3IncK A B k) = ((1 : ↥B), k) := by
    intro k
    dsimp [eAK]
    rw [show (MulEquiv.subgroupCongr hBKsup).symm (s16e3IncK A B k) =
        (⟨k, Subgroup.mem_sup_right k.2⟩ : ↥(B ⊔ s1t3KBar A B)) by
          apply Subtype.ext
          rfl,
      hfBK_right]
  have heAK_apply : ∀ (b : ↥B) (k : ↥(s1t3KBar A B)),
      eAK (Subgroup.inclusion h.le b * s16e3IncK A B k) = (b, k) := by
    intro b k
    rw [map_mul, heAK_left, heAK_right, Prod.mk_mul_mk, mul_one, one_mul]
  have heAK_symm_apply : ∀ (b : ↥B) (k : ↥(s1t3KBar A B)),
      eAK.symm (b, k) = Subgroup.inclusion h.le b * s16e3IncK A B k := by
    intro b k
    calc
      eAK.symm (b, k) = eAK.symm ((b, 1) * (1, k)) := by rw [Prod.mk_mul_mk, mul_one, one_mul]
      _ = eAK.symm (b, 1) * eAK.symm (1, k) := map_mul _ _ _
      _ = Subgroup.inclusion h.le b * s16e3IncK A B k := by
            rw [← heAK_left b, ← heAK_right k, MulEquiv.symm_apply_apply,
              MulEquiv.symm_apply_apply]
  exact ⟨eAK, heAK_left, heAK_right, heAK_apply, heAK_symm_apply, hBKbot, hBKcomm⟩

private theorem s16e3_exists_kBar_mulEquiv_B
    (h : ThreeNat A B T) (h7 : Nat.card ↥(irrSet B) = 7)
    (hL3 : IsL3 ↥B 1) (hK168 : Nat.card ↥(s1t3KBar A B) = 168) :
    Nonempty (↥(s1t3KBar A B) ≃* ↥B) := by
  classical
  let K : Subgroup (MulAut W) := s1t3KBar A B
  have hK168' : Nat.card ↥K = 168 := by simpa [K] using hK168
  obtain ⟨π, hπ_inj⟩ := s16e3_exists_fano_kBar_injective h h7
  have hbij : Function.Bijective π :=
    hπ_inj.bijective_of_nat_card_le (by
      rw [CFSG.ComponentClassification.GHarris.card_GL32_gh, hK168'])
  let eK : ↥K ≃* GL (Fin 3) (ZMod 2) := MulEquiv.ofBijective π hbij
  obtain ⟨eB⟩ := CFSG.SeitzReduction.LinearPilot.nonempty_equiv_GL32_of_lieModel hL3
  exact ⟨eK.trans eB.symm⟩

theorem ThreeNat.nonempty_fstar_mulEquiv_zmod_seven_prod_of_small_kBar
    (h : ThreeNat A B T)
    (h7 : Nat.card ↥(irrSet B) = 7)
    (hL3 : IsL3 ↥B 1)
    (hK : Nat.card ↥(s1t3KBar A B) = 7 ∨
      Nat.card ↥(s1t3KBar A B) = 21) :
    Nonempty (↥(Fstar A) ≃* Multiplicative (ZMod 7) × ↥B) := by
  classical
  let BA : Subgroup ↥A := B.subgroupOf A
  let KA : Subgroup ↥A := (s1t3KBar A B).subgroupOf A
  have hKA : s1t3KBar A B ≤ A := inf_le_left
  have hK' : Nat.card ↥(s1t3KBar A B) = 7 ∨ Nat.card ↥(s1t3KBar A B) = 21 := by simpa using hK
  obtain ⟨π, hπ_inj⟩ := s16e3_exists_fano_kBar_injective h h7
  have h7dvd : 7 ∣ Nat.card ↥(s1t3KBar A B) := by
    rcases hK' with h | h <;> simp [h]
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥(s1t3KBar A B)) 7 h7dvd
  have hno : ∀ x : ↥(s1t3KBar A B), orderOf x = 7 → π x ≠ 1 ∧ π x ≠ 1 := by
    intro x hx
    have hxne : π x ≠ 1 := by
      intro h1
      have hx1 : x = 1 := hπ_inj (h1.trans (map_one π).symm)
      rw [hx1, orderOf_one] at hx
      omega
    exact ⟨hxne, hxne⟩
  have hstruct := s16h_e3_gl3_K_structure π π
    (fun x h1 _ => hπ_inj (h1.trans (map_one π).symm)) hno hd
  rcases hstruct with hL3K | ⟨Z, hZcard, hZuniq, hKsolv, hZcontains⟩
  · exfalso
    have h168 : Nat.card ↥(s1t3KBar A B) = 168 := card_eq_of_isL3 hL3K
    rcases hK' with h | h <;> omega
  have hZnormal : Z.Normal := by
    constructor
    intro z hz g
    have hmap : Z.map (MulAut.conj g).toMonoidHom = Z := by
      apply hZuniq
      rw [Subgroup.card_map_of_injective (K := Z) (MulAut.conj g).injective, hZcard]
    have hmem : (MulAut.conj g).toMonoidHom z ∈ Z.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hz
    rw [hmap] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hZnil : Group.IsNilpotent ↥Z :=
    (IsPGroup.of_card (p := 7) (n := 1) (by rw [hZcard]; norm_num)).isNilpotent
  have hfittingK : fittingSubgroup ↥(s1t3KBar A B) = Z := by
    apply le_antisymm
    · refine sSup_le ?_
      intro N hN
      exact hZcontains N hN.1 hN.2
    · exact le_sSup ⟨hZnormal, hZnil⟩
  obtain ⟨eAK, -, heAK_right, -, heAK_symm_apply, hBKbot, hBKcomm⟩ :=
    s16e3_exists_bk_product h h7 hL3
  have heAK_right' : ∀ k : ↥(s1t3KBar A B),
      eAK (s16e3IncK A B k) = ((1 : ↥B), k) := by
    intro k
    simpa [s16e3IncK] using heAK_right k
  have heAK_symm_apply' : ∀ (b : ↥B) (k : ↥(s1t3KBar A B)),
      eAK.symm (b, k) = Subgroup.inclusion h.le b * s16e3IncK A B k := by
    intro b k
    simpa [s16e3IncK] using heAK_symm_apply b k
  let pK : ↥A →* ↥(s1t3KBar A B) :=
    (MonoidHom.snd ↥B ↥(s1t3KBar A B)).comp eAK.toMonoidHom
  have hpK_apply : ∀ k : ↥(s1t3KBar A B), pK (s16e3IncK A B k) = k := by
    intro k
    have h1 : eAK (s16e3IncK A B k) = ((1 : ↥B), k) := heAK_right' k
    change (eAK (s16e3IncK A B k)).2 = k
    rw [h1]
  have hpK_surj : Function.Surjective pK :=
    fun k => ⟨s16e3IncK A B k, hpK_apply k⟩
  have hpK_KA : ∀ x : ↥KA,
      pK (KA.subtype x) = (Subgroup.subgroupOfEquivOfLe hKA) x := by
    intro x
    have hx : KA.subtype x = s16e3IncK A B ((Subgroup.subgroupOfEquivOfLe hKA) x) := by
      apply Subtype.ext
      rfl
    rw [hx, hpK_apply]
  have hBA_quasi : CFSG.IsQuasisimple ↥BA := by
    simpa [BA] using s16e3_quasisimple_B_subgroupOf h
  have hBA_normal : BA.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
  have hBA : CFSG.IsComponent BA := ⟨hBA_quasi, hBA_normal.isSubnormal⟩
  have hlayerA : layer ↥A = BA := by
    apply le_antisymm
    · refine sSup_le ?_
      intro C hC
      rcases CFSG.LocalCores.distinct_components_commute hC hBA with hCEq | hcomm
      · rw [hCEq]
      · exfalso
        have hC_le_KA : C ≤ KA := by
          intro c hc
          rw [Subgroup.mem_subgroupOf]
          refine ⟨c.2, ?_⟩
          change (c : MulAut W) ∈ Subgroup.centralizer (B : Set (MulAut W))
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          have hcommC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
          have hbc := (Subgroup.mem_centralizer_iff.mp (hcommC hc))
            (⟨b, h.le hb⟩ : ↥A) hb
          exact congrArg Subtype.val hbc
        have hCsolv : Group.IsSolvable ↥C := by
          have : Group.IsSolvable ↥(s1t3KBar A B) := hKsolv
          exact Group.isSolvable_of_isSolvable_injective
            (f := (Subgroup.subgroupOfEquivOfLe hKA).toMonoidHom.comp
              (Subgroup.inclusion hC_le_KA))
            ((Subgroup.subgroupOfEquivOfLe hKA).injective.comp
              (Subgroup.inclusion_injective hC_le_KA))
        have : Nontrivial ↥C := CFSG.LocalCores.isQuasisimple_nontrivial hC.1
        have : Group.IsPerfect ↥C := hC.1.1
        exact (Group.IsPerfect.not_isSolvable ↥C) hCsolv
    · exact le_sSup hBA
  have hFA_le_KA : fittingSubgroup ↥A ≤ KA := by
    intro f hf
    rw [Subgroup.mem_subgroupOf]
    refine ⟨f.2, ?_⟩
    change (f : MulAut W) ∈ Subgroup.centralizer (B : Set (MulAut W))
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hl : ⁅fittingSubgroup ↥A, BA⁆ = ⊥ := by
      simpa [BA, hlayerA] using CFSG.LocalCores.fitting_layer_commute (G := ↥A)
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hl
    have hfb := (Subgroup.mem_centralizer_iff.mp (hle hf))
      (⟨b, h.le hb⟩ : ↥A) hb
    exact congrArg Subtype.val hfb
  let ZA : Subgroup ↥A := Z.map (s16e3IncK A B)
  have hmap_le : (fittingSubgroup ↥A).map pK ≤ Z := by
    have h := CFSG.WholeGroup.fittingSubgroup_map_le_of_surjective pK hpK_surj
    simpa [hfittingK] using h
  have hFA_le_ZA : fittingSubgroup ↥A ≤ ZA := by
    intro f hf
    have hfK : f ∈ KA := hFA_le_KA hf
    let x : ↥KA := ⟨f, hfK⟩
    have hxZ : (Subgroup.subgroupOfEquivOfLe hKA) x ∈ Z := by
      have hmem : pK f ∈ Z := hmap_le (Subgroup.mem_map_of_mem pK hf)
      have hp : pK f = (Subgroup.subgroupOfEquivOfLe hKA) x := hpK_KA x
      simpa [hp] using hmem
    have hsub : KA.subtype x = s16e3IncK A B ((Subgroup.subgroupOfEquivOfLe hKA) x) := by
      apply Subtype.ext
      rfl
    rw [show f = KA.subtype x from rfl, hsub]
    exact Subgroup.mem_map_of_mem (s16e3IncK A B) hxZ
  have hZA_normal : ZA.Normal := by
    constructor
    intro z hz a
    obtain ⟨p, hp⟩ := eAK.symm.surjective a
    rcases p with ⟨b, k⟩
    rw [← hp, heAK_symm_apply']
    obtain ⟨zK, hzK, rfl⟩ := Subgroup.mem_map.mp hz
    have hbcomm : ∀ x : ↥(s1t3KBar A B),
        Subgroup.inclusion h.le b * s16e3IncK A B x = s16e3IncK A B x * Subgroup.inclusion h.le b := by
      intro x
      apply Subtype.ext
      exact hBKcomm b b.2 x x.2
    have hz' : k * zK * k⁻¹ ∈ Z := hZnormal.conj_mem zK hzK k
    have hmemZA : s16e3IncK A B (k * zK * k⁻¹) ∈ ZA :=
      Subgroup.mem_map_of_mem (s16e3IncK A B) hz'
    have hcalc : (Subgroup.inclusion h.le b * s16e3IncK A B k) * s16e3IncK A B zK *
        (Subgroup.inclusion h.le b * s16e3IncK A B k)⁻¹ = s16e3IncK A B (k * zK * k⁻¹) := by
      calc
        (Subgroup.inclusion h.le b * s16e3IncK A B k) * s16e3IncK A B zK *
            (Subgroup.inclusion h.le b * s16e3IncK A B k)⁻¹
            = Subgroup.inclusion h.le b *
                (s16e3IncK A B k * s16e3IncK A B zK * (s16e3IncK A B k)⁻¹) *
                (Subgroup.inclusion h.le b)⁻¹ := by group
        _ = Subgroup.inclusion h.le b * s16e3IncK A B (k * zK * k⁻¹) *
                (Subgroup.inclusion h.le b)⁻¹ := by
              simp only [s16e3IncK, ← map_mul, ← map_inv]
        _ = s16e3IncK A B (k * zK * k⁻¹) := by
              rw [hbcomm (k * zK * k⁻¹)]
              group
    rw [hcalc]
    exact hmemZA
  have hZA_nil : Group.IsNilpotent ↥ZA := by
    have : Group.IsNilpotent ↥Z := hZnil
    exact Group.nilpotent_of_mulEquiv
      (G := ↥Z) (G' := ↥ZA)
      (Subgroup.equivMapOfInjective Z (s16e3IncK A B)
        (s16e3IncK_injective A B))
  have hfittingA : fittingSubgroup ↥A = ZA := by
    apply le_antisymm hFA_le_ZA
    exact le_sSup ⟨hZA_normal, hZA_nil⟩
  have hgenF : genFittingFStar ↥A = ZA ⊔ BA := by
    rw [CFSG.Adapters.genFittingFStar_eq_foundations ↥A]
    rw [CFSG.generalizedFitting.eq_sup (↥A), hfittingA, hlayerA]
  have hFstar_eq : Fstar A = Z.map (Subgroup.subtype (s1t3KBar A B)) ⊔ B := by
    rw [show Fstar A = (genFittingFStar ↥A).map (Subgroup.subtype A) from rfl, hgenF,
      Subgroup.map_sup]
    have hZA_map : ZA.map (Subgroup.subtype A) = Z.map (Subgroup.subtype (s1t3KBar A B)) := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
        exact Subgroup.mem_map_of_mem (Subgroup.subtype (s1t3KBar A B)) hz
      · rintro ⟨z, hz, rfl⟩
        exact ⟨s16e3IncK A B z, Subgroup.mem_map_of_mem _ hz, rfl⟩
    have hBA_map : BA.map (Subgroup.subtype A) = B :=
      Subgroup.map_subgroupOf_eq_of_le h.le
    rw [hZA_map, hBA_map]
  have hZleK : Z.map (Subgroup.subtype (s1t3KBar A B)) ≤ s1t3KBar A B := Subgroup.map_subtype_le Z
  have hinf : Z.map (Subgroup.subtype (s1t3KBar A B)) ⊓ B = ⊥ := by
    apply le_bot_iff.mp
    calc Z.map (Subgroup.subtype (s1t3KBar A B)) ⊓ B ≤ s1t3KBar A B ⊓ B := inf_le_inf_right B hZleK
      _ = B ⊓ s1t3KBar A B := inf_comm (s1t3KBar A B) B
      _ = ⊥ := hBKbot
  have hcommZ : ∀ z ∈ Z.map (Subgroup.subtype (s1t3KBar A B)), ∀ b ∈ B, z * b = b * z := by
    rintro z ⟨k, hk, rfl⟩ b hb
    exact (hBKcomm b hb k k.2).symm
  let eF : ↥(Z.map (Subgroup.subtype (s1t3KBar A B))) × ↥B ≃* ↥(Fstar A) :=
    CFSG.ComponentClassification.Asc75T4.mulEquivOfCommute
      (A := Z.map (Subgroup.subtype (s1t3KBar A B))) (B := B) (C := Fstar A)
      (by rw [hFstar_eq]; exact le_sup_left)
      (by rw [hFstar_eq]; exact le_sup_right)
      hcommZ hinf (by rw [hFstar_eq])
  let eZ : ↥(Z.map (Subgroup.subtype (s1t3KBar A B))) ≃* ↥Z :=
    (Subgroup.equivMapOfInjective Z (Subgroup.subtype (s1t3KBar A B)) (Subgroup.subtype_injective (s1t3KBar A B))).symm
  have hZmod : Nat.card (Multiplicative (ZMod 7)) = 7 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, ZMod.card]
  let e7 : ↥Z ≃* Multiplicative (ZMod 7) :=
    mulEquivOfPrimeCardEq (p := 7) hZcard hZmod
  exact ⟨eF.symm.trans ((MulEquiv.prodCongr eZ (MulEquiv.refl ↥B)).trans
    (MulEquiv.prodCongr e7 (MulEquiv.refl ↥B)))⟩


theorem ThreeNat.fstar_eq_of_card_kBar_eq_168
    (h : ThreeNat A B T) (h7 : Nat.card ↥(irrSet B) = 7)
    (hL3 : IsL3 ↥B 1) (hK168 : Nat.card ↥(s1t3KBar A B) = 168) :
    Fstar A = A := by
  classical
  let BA : Subgroup ↥A := B.subgroupOf A
  let KA : Subgroup ↥A := (s1t3KBar A B).subgroupOf A
  have hKA : s1t3KBar A B ≤ A := inf_le_left
  have hBKsup : B ⊔ s1t3KBar A B = A := ThreeNat.sup_kBar_eq_of_isL3 h h7 hL3
  obtain ⟨j⟩ := s16e3_exists_kBar_mulEquiv_B h h7 hL3 hK168
  have hB_native : CFSG.IsQuasisimple ↥B := s16e3_quasisimple_B h
  have hBA_quasi : CFSG.IsQuasisimple ↥BA := by
    simpa [BA] using s16e3_quasisimple_B_subgroupOf h
  have hBA_normal : BA.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
  have hBA : CFSG.IsComponent BA := ⟨hBA_quasi, hBA_normal.isSubnormal⟩
  let eKA : ↥KA ≃* ↥(s1t3KBar A B) := Subgroup.subgroupOfEquivOfLe hKA
  have hKA_quasi : CFSG.IsQuasisimple ↥KA :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (j.symm.trans eKA.symm) hB_native
  have hcentBA : Subgroup.centralizer (BA : Set ↥A) = KA := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      change (x : MulAut W) ∈ A ⊓ Subgroup.centralizer (B : Set (MulAut W))
      refine ⟨x.2, ?_⟩
      change (x : MulAut W) ∈ Subgroup.centralizer (B : Set (MulAut W))
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hx ⟨b, h.le hb⟩ hb)
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hx' : (x : MulAut W) ∈ Subgroup.centralizer (B : Set (MulAut W)) := by
        have h := Subgroup.mem_subgroupOf.mp hx
        change (x : MulAut W) ∈ A ⊓ Subgroup.centralizer (B : Set (MulAut W)) at h
        exact h.2
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hx') (y : MulAut W) hy
  have hKA_normal : KA.Normal := by
    rw [← hcentBA]
    exact Subgroup.normal_centralizer (H := BA)
  have hKA_comp : CFSG.IsComponent KA := ⟨hKA_quasi, hKA_normal.isSubnormal⟩
  have hBAKA : BA ⊔ KA = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.le hKA, hBKsup, Subgroup.subgroupOf_self]
  have hlayer_top : layer ↥A = ⊤ := by
    apply top_unique
    rw [← hBAKA]
    exact sup_le (CFSG.LocalCores.component_le_layer hBA)
      (CFSG.LocalCores.component_le_layer hKA_comp)
  have hgen_top : genFittingFStar ↥A = ⊤ := by
    rw [CFSG.Adapters.genFittingFStar_eq_foundations ↥A]
    rw [CFSG.generalizedFitting.eq_sup (↥A), hlayer_top, sup_top_eq]
  rw [show Fstar A = (genFittingFStar ↥A).map (Subgroup.subtype A) from rfl,
    hgen_top, Subgroup.map_top, Subgroup.range_subtype]

theorem ThreeNat.nonempty_fstar_mulEquiv_prod_self_of_card_kBar_eq_168
    (h : ThreeNat A B T) (h7 : Nat.card ↥(irrSet B) = 7)
    (hL3 : IsL3 ↥B 1) (hK168 : Nat.card ↥(s1t3KBar A B) = 168) :
    Nonempty (↥(Fstar A) ≃* (↥B × ↥B)) := by
  classical
  have hF : Fstar A = A := ThreeNat.fstar_eq_of_card_kBar_eq_168 h h7 hL3 hK168
  obtain ⟨j⟩ := s16e3_exists_kBar_mulEquiv_B h h7 hL3 hK168
  obtain ⟨eAK, -, -, -, -, -, -⟩ := s16e3_exists_bk_product h h7 hL3
  exact ⟨(MulEquiv.subgroupCongr hF).trans
    (eAK.trans (MulEquiv.prodCongr (MulEquiv.refl ↥B) j))⟩

theorem s168e3_threeNatSeven_l3_fstarBar_eq_mbar_of_kBar_168
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL3 : IsL3 ↥(lBar V₀ V hV L) 1)
    (hK168 : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) :
    fstarBar D.M V₀ V hV = Mbar D.M V₀ V hV := by
  have hmain := ThreeNat.fstar_eq_of_card_kBar_eq_168
    (W := Vtil V₀ V hV) h h7 hL3 hK168
  simpa [fstarBar] using hmain

theorem s168e3_threeNatSeven_l3_fstarBar_equiv_lBar_prod_self_of_kBar_168
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL3 : IsL3 ↥(lBar V₀ V hV L) 1)
    (hK168 : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) :
    Nonempty (↥(fstarBar D.M V₀ V hV) ≃*
      (↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L))) := by
  have hmain := ThreeNat.nonempty_fstar_mulEquiv_prod_self_of_card_kBar_eq_168
    (W := Vtil V₀ V hV) h h7 hL3 hK168
  exact hmain

theorem s168e3_threeNatSeven_l3_fstarBar_equiv_zmod_seven_prod_lBar_of_small_kBar
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL3 : IsL3 ↥(lBar V₀ V hV L) 1)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 7 ∨
      Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 21) :
    Nonempty (↥(fstarBar D.M V₀ V hV) ≃*
      Multiplicative (ZMod 7) × ↥(lBar V₀ V hV L)) := by
  have hmain := ThreeNat.nonempty_fstar_mulEquiv_zmod_seven_prod_of_small_kBar
    (W := Vtil V₀ V hV) h h7 hL3 hK
  exact hmain

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
