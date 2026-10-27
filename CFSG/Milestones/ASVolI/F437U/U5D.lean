module

public import CFSG.Milestones.ASVolI.F437U.U5
public import CFSG.Milestones.ASVolI.F429.aC7U5
public import CFSG.Milestones.ASVolI.F437.U5

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.EvenBN.U5
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit

section ZP

variable {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)

theorem burnsideF437U_ZP_eq {z z' : hypSU h 2 1} (hz : z ∈ ZPsub h) (hz' : z' ∈ ZPsub h)
    (hz1 : z ≠ 1) (hz1' : z' ≠ 1) : z = z' := by
  have key : ∀ w ∈ ZPsub h, w ≠ 1 → mat w ιe₁ ιf₁ = 1 := by
    intro w hw hw1
    have hb := bar_eq_of_mem_ZPsub hw
    rw [h.bar_apply, pow_one, sq] at hb
    have h0 : mat w ιe₁ ιf₁ ≠ 0 := by
      intro h0
      apply hw1
      refine eq_of_mem_ZPsub hw (one_mem _) ?_
      rw [h0, mat_one, one_apply_ne (by decide)]
    have := mul_left_cancel₀ h0 (hb.trans (mul_one _).symm)
    exact this
  exact eq_of_mem_ZPsub hz hz' (by rw [key z hz hz1, key z' hz' hz1'])

theorem burnsideF437U_ZP_centralizer_le {z : hypSU h 2 1} (hz : z ∈ ZPsub h) (hz1 : z ≠ 1)
    {g : hypSU h 2 1} (hg : g * z = z * g) : g ∈ u5PtStab h := by
  have hc : mat z ιe₁ ιf₁ ≠ 0 := by
    intro h0
    apply hz1
    refine eq_of_mem_ZPsub hz (one_mem _) ?_
    rw [h0, mat_one, one_apply_ne (by decide)]
  have hm := mat_ZPsub hz
  rw [mem_u5PtStab_iff]
  intro a ha
  have e := congrFun (congrFun (congrArg mat hg) a) ιf₁
  rw [mat_mul, mat_mul, hm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.add_apply, Matrix.add_apply, mul_single_apply_same] at e
  have hR : (single ιe₁ ιf₁ (mat z ιe₁ ιf₁) * mat g) a ιf₁ = 0 :=
    single_mul_apply_of_ne _ _ _ _ _ ha _
  have e' : mat g a ιe₁ * mat z ιe₁ ιf₁ = 0 := by linear_combination e + hR
  exact (mul_eq_zero.mp e').resolve_right hc

end ZP

section Gen

variable {E : Type} [Group E]

theorem burnsideF437U_card_eq_two_mul [Finite E] {Gp X : Subgroup E} [Gp.Normal]
    (hidx : Gp.index = 2) {x : E} (hxX : x ∈ X) (hxG : x ∉ Gp) :
    Nat.card X = 2 * Nat.card ↥(Gp ⊓ X) := by
  have hdvd : Gp.relIndex X ∣ 2 := hidx ▸ Subgroup.relIndex_dvd_index_of_normal Gp X
  have hne : Gp.relIndex X ≠ 1 := fun h1 => hxG (Subgroup.relIndex_eq_one.mp h1 hxX)
  have h2 : Gp.relIndex X = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  rw [← Subgroup.relIndex_mul_card, h2]

theorem burnsideF437U_twoPart_two_mul {X Y : Subgroup E} [Finite E]
    (h : Nat.card X = 2 * Nat.card Y) :
    CFSG.QuasithinUnique.twoPart X = 2 * CFSG.QuasithinUnique.twoPart Y := by
  have hY : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  unfold CFSG.QuasithinUnique.twoPart
  rw [h, Nat.factorization_mul two_ne_zero hY, Finsupp.add_apply, Nat.Prime.factorization_self
    Nat.prime_two, pow_add, pow_one]

theorem burnsideF437U_ctr_map {X : Type} [Group X] (φ : X →* E) (hφ : Function.Injective φ)
    (A : Subgroup X) : ctr (A.map φ) = (ctr A).map φ := by
  ext e
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hc⟩
    refine ⟨a, ⟨ha, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩, rfl⟩
    have := (Subgroup.mem_centralizer_iff.mp hc) (φ b) ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact hφ this
  · rintro ⟨a, ⟨ha, hc⟩, rfl⟩
    refine ⟨⟨a, ha, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hc) b hb]

theorem burnsideF437U_conj_mem_ctr {X : Subgroup E} {n w : E}
    (hn : n ∈ Subgroup.normalizer (X : Set E)) (hw : w ∈ ctr X) : n * w * n⁻¹ ∈ ctr X :=
  burnsideF437_conj_mem_ctr hn hw

end Gen

section U5Data

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF437U_u5DataInput : burnsideF437_U5DataInput := by
  intro E _ Gp M₁ M₂ hyp Tb hTb fb hfbT hinv hgr
  haveI := hyp.finite
  haveI := hyp.normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : Gp.index = 2 := by
    rcases burnsideF429_F429_one_Un_two (Or.inr rfl) hyp with h | h
    · exact absurd (h ▸ Subgroup.mem_top fb) hinv.not_mem
    · exact h.1
  obtain ⟨K, fK, h, φ, hφ, hrange, h1, h2, a, hact⟩ := burnsideF437U_U5_model hyp hgr
  haveI : Finite K := h.finite
  have hpc := burnsideF437U_U5_pCore h
  obtain ⟨c, hcB, hact'⟩ := burnsideF437U_borel_conj φ hφ hrange
    (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom h1 h2
    (burnsideF437U_U5_frob_u h) (by rw [hpc]; exact burnsideF437U_U5_u_U h)
    (fun g hg => burnsideF437U_U5_reg h g (by rwa [hpc] at hg)) hinv a hact
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  have hB : Gp ⊓ (M₁ ⊓ M₂) = (u5PtStab h ⊓ u5LnStab h).map φ := by
    rw [show Gp ⊓ (M₁ ⊓ M₂) = (Gp ⊓ M₁) ⊓ (Gp ⊓ M₂) by
      rw [inf_inf_distrib_left], h1, h2, Subgroup.map_inf_eq _ _ _ hφ]
  have hS : S = (hypUnitriangular h 2 1).map φ := by
    rw [hSdef, hB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, hpc]
  have hZ : ctr (oPPrime 2 (Gp ⊓ M₁)) = (ZPsub h).map φ := by
    rw [← burnsideF429a_c7_U5 hyp, ← hSdef, hS, burnsideF437U_ctr_map φ hφ, ← centerIn_U]
    rfl
  have hMN : M₁ ⊓ M₂ ≤ Subgroup.normalizer (S : Set E) := by
    intro m hm
    refine CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxG, hxM⟩
      exact ⟨(inferInstance : Gp.Normal).conj_mem x hxG m,
        (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem hm hxM) ((M₁ ⊓ M₂).inv_mem hm)⟩
    · rintro ⟨hxG, hxM⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : Gp.Normal).conj_mem _ hxG m⁻¹
        simpa [mul_assoc] using this
      · have := (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).inv_mem hm) hxM) hm
        simpa [mul_assoc] using this
  have hS2 : IsPGroup 2 ↥S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hSM : S ≤ M₁ ⊓ M₂ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hST : S ≤ Tb := CFSG.QuasithinUnique.IsSylowTwoOf.le_of_normalizes
    ⟨hTb.1, hTb.2.1, hTb.2.2⟩ hSM hMN hS2
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    set H := M₁ ⊓ Subgroup.centralizer ({fb} : Set E) with hH
    set T₀ := Tb ⊓ Subgroup.centralizer ({fb} : Set E) with hT₀
    set R := S ⊓ Subgroup.centralizer ({fb} : Set E) with hR
    have hfbC : fb ∈ Subgroup.centralizer ({fb} : Set E) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hfbM₁ : fb ∈ M₁ := hinv.mem.1
    have hRN : IsSylowOf 2 R (Gp ⊓ H) := by
      refine burnsideF429_isSylowOf_of_le hinv.sylow ?_ ?_
      · intro y hy
        obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
        have hyB := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hyS
        exact ⟨hyB.1, hyB.2.1, hyC⟩
      · rintro y ⟨hyG, hyM, hyC⟩
        exact ⟨hyG, hyC⟩
    have hT₀G : Gp ⊓ T₀ = R := by
      have hR' : CFSG.QuasithinUnique.IsSylowTwoOf R (Gp ⊓ H) := ⟨hRN.1, hRN.2.1, hRN.2.2⟩
      refine hR'.eq_of_le ?_ ?_ ?_
      · intro y hy
        obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
        exact ⟨(CFSG.LieType.BorelTits.pCoreOf_le 2 _ hyS).1, hST hyS, hyC⟩
      · rintro y ⟨hyG, hyT, hyC⟩
        exact ⟨hyG, (hTb.1 hyT).1, hyC⟩
      · exact hTb.2.1.to_le (fun y hy => (Subgroup.mem_inf.mp hy).2.1)
    have hcH := burnsideF437U_card_eq_two_mul hidx (X := H) ⟨hfbM₁, hfbC⟩ hinv.not_mem
    have hcT := burnsideF437U_card_eq_two_mul hidx (X := T₀) ⟨hfbT, hfbC⟩ hinv.not_mem
    rw [hT₀G] at hcT
    have hR2 : CFSG.QuasithinUnique.IsSylowTwoOf R (Gp ⊓ H) := ⟨hRN.1, hRN.2.1, hRN.2.2⟩
    refine CFSG.QuasithinUnique.isSylowTwoOf_of_card_eq (fun y hy => ?_)
      (hTb.2.1.to_le inf_le_left) ?_
    · exact ⟨(hTb.1 hy.1).1, hy.2⟩
    · rw [hcT, burnsideF437U_twoPart_two_mul hcH, hR2.card_eq]
  ·
    rw [hZ]
    rintro _ ⟨z, hz, rfl⟩
    have hzS : φ z ∈ S := by rw [hS]; exact ⟨z, ZPsub_le_U hz, rfl⟩
    refine ⟨hST hzS, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    by_cases hz1 : z = 1
    · rw [hz1, map_one, one_mul, mul_one]
    ·
      have hctrS : φ z ∈ ctr S := by
        rw [hS, burnsideF437U_ctr_map φ hφ, ← centerIn_U] at *
        exact ⟨z, hz, rfl⟩
      have hconj := burnsideF437U_conj_mem_ctr (hMN (hTb.1 ht)) hctrS
      rw [hS, burnsideF437U_ctr_map φ hφ] at hconj
      obtain ⟨z', hz', hz'e⟩ := hconj
      have hz'Z : z' ∈ ZPsub h := by rw [← centerIn_U]; exact hz'
      have hz'1 : z' ≠ 1 := by
        rintro rfl
        rw [map_one] at hz'e
        apply hz1
        apply hφ
        rw [map_one]
        have := congrArg (fun w => t⁻¹ * w * t) hz'e
        simpa [mul_assoc] using this.symm
      have hzz : z' = z := burnsideF437U_ZP_eq h hz'Z hz hz'1 hz1
      rw [hzz] at hz'e
      calc t * φ z = (t * φ z * t⁻¹) * t := by group
        _ = φ z * t := by rw [← hz'e]
  ·
    rw [← burnsideF429a_c7_U5 hyp]
    exact inf_le_left
  ·
    intro y hy hyS x hx hx1 hconj
    rw [hZ] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hz1 : z ≠ 1 := fun e => hx1 (by rw [e, map_one])
    obtain ⟨g, hgG, rfl⟩ := hconj
    rw [← hrange] at hgG
    obtain ⟨g', rfl⟩ := hgG
    have hcu : c * burnsideF437U_U5_u h * c⁻¹ ∈ hypUnitriangular h 2 1 := by
      have := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (u5PtStab h ⊓ u5LnStab h) hcB)
          (burnsideF437U_U5_u h)).mp (by rw [hpc]; exact burnsideF437U_U5_u_U h)
      rwa [hpc] at this
    have huT : φ (c * burnsideF437U_U5_u h * c⁻¹) ∈ Tb ⊓ Subgroup.centralizer ({fb} : Set E) := by
      refine ⟨hST (by rw [hS]; exact ⟨_, hcu, rfl⟩), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have e1 : fb * φ (c * burnsideF437U_U5_u h * c⁻¹) * fb⁻¹ =
          φ (c * burnsideF437U_U5_u h * c⁻¹) := by
        rw [hact']
        congr 1
        rw [show c⁻¹ * (c * burnsideF437U_U5_u h * c⁻¹) * c = burnsideF437U_U5_u h by group,
          burnsideF437U_U5_frob_u h]
      calc φ (c * burnsideF437U_U5_u h * c⁻¹) * fb =
          (fb * φ (c * burnsideF437U_U5_u h * c⁻¹) * fb⁻¹) * fb := by rw [e1]
        _ = fb * φ (c * burnsideF437U_U5_u h * c⁻¹) := by group
    have hcomm := (Subgroup.mem_centralizer_iff.mp hy.2) _ huT
    have hcomm' : (c * burnsideF437U_U5_u h * c⁻¹) * (g' * z * g'⁻¹) =
        (g' * z * g'⁻¹) * (c * burnsideF437U_U5_u h * c⁻¹) := by
      apply hφ
      simpa only [map_mul, map_inv] using hcomm
    have hzc : (g'⁻¹ * c * burnsideF437U_U5_u h * (g'⁻¹ * c)⁻¹) * z =
        z * (g'⁻¹ * c * burnsideF437U_U5_u h * (g'⁻¹ * c)⁻¹) := by
      have := congrArg (fun w => g'⁻¹ * w * g') hcomm'
      calc (g'⁻¹ * c * burnsideF437U_U5_u h * (g'⁻¹ * c)⁻¹) * z =
          g'⁻¹ * (c * burnsideF437U_U5_u h * c⁻¹ * (g' * z * g'⁻¹)) * g' := by group
        _ = g'⁻¹ * (g' * z * g'⁻¹ * (c * burnsideF437U_U5_u h * c⁻¹)) * g' := by rw [this]
        _ = z * (g'⁻¹ * c * burnsideF437U_U5_u h * (g'⁻¹ * c)⁻¹) := by group
    have hP := burnsideF437U_ZP_centralizer_le h hz hz1 hzc
    have hg'c := burnsideF437U_U5_reg₁ h _ hP
    have hg' : g' ∈ u5PtStab h := by
      have := (u5PtStab h).mul_mem hcB.1 ((u5PtStab h).inv_mem hg'c)
      simpa [mul_assoc] using this
    have hz' := conj_mem_ZPsub_of_mem_u5PtStab hg' hz
    have hz'1 : g' * z * g'⁻¹ ≠ 1 := fun e => hz1 (by
      have := congrArg (fun w => g'⁻¹ * w * g') e
      simpa [mul_assoc] using this)
    rw [← map_inv, ← map_mul, ← map_mul, burnsideF437U_ZP_eq h hz' hz hz'1 hz1]

end U5Data

end CFSG.ASVolI
