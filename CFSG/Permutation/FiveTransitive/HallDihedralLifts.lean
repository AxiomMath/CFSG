module

public import CFSG.Permutation.FiveTransitive.HallInvolutionConsequence

public section

namespace CFSG

namespace FiveTransitive.Research.HallDihedralLifts

open Research.OddFourStabilizerLifts
open Research.OddFourCorrection

def orbitA : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 3, 2]
  invFun := ![1, 0, 3, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def orbitB : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def orbitQuarter : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 1, 0]
  invFun := ![3, 2, 0, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem orbitQuarter_sq : orbitQuarter ^ 2 = orbitA := by decide

private theorem orbitQuarter_mul_orbitB :
    orbitQuarter * orbitB = (orbitA * orbitB) * orbitQuarter := by
  decide

private theorem orbitQuarter_order : orderOf orbitQuarter = 4 := by
  have htwo : ¬orbitQuarter ^ 2 ^ 1 = 1 := by
    intro h
    have hi := Equiv.Perm.congr_fun h (0 : Fin 4)
    contradiction
  have hfour : orbitQuarter ^ 2 ^ (1 + 1) = 1 := by
    ext i
    fin_cases i <;> rfl
  simpa using
    (orderOf_eq_prime_pow (x := orbitQuarter) (p := 2) (n := 1) htwo hfour)

private def normalKleinFour : Subgroup (Equiv.Perm (Fin 4)) :=
  Subgroup.map (alternatingGroup (Fin 4)).subtype
    (alternatingGroup.kleinFour (Fin 4))

private theorem normalKleinFour_normal : normalKleinFour.Normal := by
  letI : (alternatingGroup.kleinFour (Fin 4)).Characteristic :=
    alternatingGroup.characteristic_kleinFour (by norm_num)
  exact ConjAct.normal_of_characteristic_of_normal

private theorem normalKleinFour_card : Nat.card normalKleinFour = 4 := by
  rw [normalKleinFour,
    Subgroup.card_map_of_injective (alternatingGroup (Fin 4)).subtype_injective]
  exact alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)

private theorem normalKleinFour_isPGroup : IsPGroup 2 normalKleinFour := by
  apply IsPGroup.of_card (n := 2)
  norm_num [normalKleinFour_card]

private theorem orbitA_mem_normalKleinFour : orbitA ∈ normalKleinFour := by
  change ∃ q, q ∈ alternatingGroup.kleinFour (Fin 4) ∧ (q : Equiv.Perm (Fin 4)) = orbitA
  have hA : orbitA = Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 := by
    ext i
    fin_cases i <;> rfl
  have hAlt : orbitA ∈ alternatingGroup (Fin 4) := by
    rw [Equiv.Perm.mem_alternatingGroup, hA, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    norm_num
  let q : alternatingGroup (Fin 4) := ⟨orbitA, hAlt⟩
  refine ⟨q, ?_, rfl⟩
  rw [← SetLike.mem_coe,
    alternatingGroup.coe_kleinFour_of_card_eq_four (by norm_num)]
  right
  change orbitA.cycleType = {2, 2}
  rw [hA]
  exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)

private theorem orbitB_mem_normalKleinFour : orbitB ∈ normalKleinFour := by
  change ∃ q, q ∈ alternatingGroup.kleinFour (Fin 4) ∧ (q : Equiv.Perm (Fin 4)) = orbitB
  have hB : orbitB = Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3 := by
    ext i
    fin_cases i <;> rfl
  have hAlt : orbitB ∈ alternatingGroup (Fin 4) := by
    rw [Equiv.Perm.mem_alternatingGroup, hB, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    norm_num
  let q : alternatingGroup (Fin 4) := ⟨orbitB, hAlt⟩
  refine ⟨q, ?_, rfl⟩
  rw [← SetLike.mem_coe,
    alternatingGroup.coe_kleinFour_of_card_eq_four (by norm_num)]
  right
  change orbitB.cycleType = {2, 2}
  rw [hB]
  exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)

private theorem exists_dihedralSylow :
    ∃ Q : Sylow 2 (Equiv.Perm (Fin 4)),
      orbitQuarter ∈ Q ∧ orbitA ∈ Q ∧ orbitB ∈ Q := by
  have hcycCard : Nat.card (Subgroup.zpowers orbitQuarter) = 2 ^ 2 := by
    rw [Nat.card_zpowers, orbitQuarter_order]
    norm_num
  have hcyc : IsPGroup 2 (Subgroup.zpowers orbitQuarter) :=
    IsPGroup.of_card hcycCard
  obtain ⟨Q, hQ⟩ := hcyc.exists_le_sylow
  haveI : normalKleinFour.Normal := normalKleinFour_normal
  have hnormal : normalKleinFour ≤ (Q : Subgroup (Equiv.Perm (Fin 4))) :=
    normalKleinFour_isPGroup.le_sylow_of_normal Q
  exact ⟨Q, hQ (Subgroup.mem_zpowers orbitQuarter),
    hnormal orbitA_mem_normalKleinFour,
    hnormal orbitB_mem_normalKleinFour⟩

private theorem closure_pair_isPGroup_two
    {L : Type*} [Group L] (a b : L)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b) :
    IsPGroup 2 (Subgroup.closure ({a, b} : Set L)) := by
  let V : Subgroup L := Subgroup.closure ({a, b} : Set L)
  have hgenComm :
      ∀ x ∈ ({a, b} : Set L), ∀ y ∈ ({a, b} : Set L), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hab.eq
    · exact hab.eq.symm
    · rfl
  letI : IsMulCommutative V := Subgroup.isMulCommutative_closure (fun _ hx _ hy _ => hgenComm _ hx _ hy)
  have hcommV : ∀ x y : V, x * y = y * x :=
    isMulCommutative_iff.mp (inferInstance : IsMulCommutative V)
  have hsquare : ∀ x : V, (x : L) ^ 2 = 1 := by
    intro x
    apply Subgroup.closure_induction (p := fun z _ ↦ z ^ 2 = 1)
        (k := ({a, b} : Set L))
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hb
    · simp
    · intro x y hx hy hxTwo hyTwo
      have hxy : Commute x y := by
        change x * y = y * x
        exact congrArg Subtype.val (hcommV ⟨x, hx⟩ ⟨y, hy⟩)
      rw [hxy.mul_pow, hxTwo, hyTwo, one_mul]
    · intro x hx hxTwo
      rw [inv_pow, hxTwo, inv_one]
    · exact x.property
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  refine ⟨1, ?_⟩
  norm_num only [pow_one]
  exact Subtype.ext (hsquare x)

theorem stabilizer_card_odd_of_four_transitive
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e f : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e))) :
    Odd (Nat.card (MulAction.stabilizer G f)) := by
  let _ : MulAction.IsMultiplyPretransitive G X 4 := h4
  obtain ⟨g, hg⟩ := h4.exists_smul_eq e f
  have hfe : f = g • e := hg.symm
  have hcard : Nat.card (MulAction.stabilizer G e) =
      Nat.card (MulAction.stabilizer G f) :=
    Nat.card_congr (MulAction.stabilizerEquivStabilizer hfe).toEquiv
  rwa [← hcard]

theorem exists_hall_quarterTurn_of_odd_stabilizer
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b) (y : X)
    (hya : a • y ≠ y) (hyb : b • y ≠ y)
    (hyc : (a * b) • y ≠ y) :
    ∃ u : G,
      u • y = b • y ∧
      u • (a • y) = (a * b) • y ∧
      u • (b • y) = a • y ∧
      u • ((a * b) • y) = y ∧
      u ^ 2 = a ∧ u * a = a * u ∧ u * b = (a * b) * u := by
  classical
  let c : G := a * b
  have haInv (z : X) : a • (a • z) = z := by
    rw [← mul_smul, ← pow_two, haTwo, one_smul]
  have hbInv (z : X) : b • (b • z) = z := by
    rw [← mul_smul, ← pow_two, hbTwo, one_smul]
  have habAct (z : X) : a • (b • z) = c • z := by
    rw [← mul_smul]
  have hbaAct (z : X) : b • (a • z) = c • z := by
    rw [← mul_smul, show b * a = c from hab.eq.symm.trans rfl]
  have hac : a * c = b := by
    dsimp only [c]
    rw [← mul_assoc, ← pow_two, haTwo, one_mul]
  have hbc : b * c = a := by
    dsimp only [c]
    calc
      b * (a * b) = a * (b * b) := by
        rw [← mul_assoc, ← hab.eq, mul_assoc]
      _ = a := by rw [← pow_two, hbTwo, mul_one]
  have hacAct (z : X) : a • (c • z) = b • z := by
    rw [← mul_smul, hac]
  have hbcAct (z : X) : b • (c • z) = a • z := by
    rw [← mul_smul, hbc]
  have hy_a : y ≠ a • y := hya.symm
  have hy_b : y ≠ b • y := hyb.symm
  have hy_c : y ≠ c • y := by simpa only [c] using hyc.symm
  have haby : a • y ≠ b • y := by
    intro h
    apply hyc
    calc
      (a * b) • y = a • (b • y) := mul_smul _ _ _
      _ = a • (a • y) := congrArg (fun z : X ↦ a • z) h.symm
      _ = y := haInv y
  have hacy : a • y ≠ c • y := by
    intro h
    apply hyb
    calc
      b • y = a • (c • y) := (hacAct y).symm
      _ = a • (a • y) := congrArg (fun z : X ↦ a • z) h.symm
      _ = y := haInv y
  have hbcy : b • y ≠ c • y := by
    intro h
    apply hya
    calc
      a • y = b • (c • y) := (hbcAct y).symm
      _ = b • (b • y) := congrArg (fun z : X ↦ b • z) h.symm
      _ = y := hbInv y
  let f : Fin 4 → X := ![y, a • y, b • y, c • y]
  have hf : Function.Injective f := by
    have hya' : a • y ≠ y := hya
    have hyb' : b • y ≠ y := hyb
    have hyc' : c • y ≠ y := by simpa only [c] using hyc
    have hbay : b • y ≠ a • y := haby.symm
    have hcay : c • y ≠ a • y := hacy.symm
    have hcby : c • y ≠ b • y := hbcy.symm
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, hy_a, hy_b, hy_c, hya', hyb', hyc', haby, hacy, hbcy,
        hbay, hcay, hcby] at hij ⊢
  let ef : Fin 4 ↪ X := ⟨f, hf⟩
  have haBase : ∀ i, a • ef i = ef (orbitA i) := by
    intro i
    fin_cases i <;>
      simp [ef, f, orbitA, haInv, habAct, hacAct]
  have hbBase : ∀ i, b • ef i = ef (orbitB i) := by
    intro i
    fin_cases i <;>
      simp [ef, f, orbitB, hbInv, hbaAct, hbcAct]
  have hoddEf : Odd (Nat.card (MulAction.stabilizer G ef)) :=
    stabilizer_card_odd_of_four_transitive h4 e ef hodd
  obtain ⟨Q₀, hτQ₀, haQ₀, hbQ₀⟩ := exists_dihedralSylow
  let ρ : Equiv.Perm (Fin 4) ≃* Equiv.Perm (Set.range ef : Set X) :=
    (baseRangeEquiv ef).permCongrHom
  let Q : Sylow 2 (Equiv.Perm (Set.range ef : Set X)) :=
    Sylow.mapSurjective (f := ρ.toMonoidHom) ρ.surjective Q₀
  have hτQ : ρ orbitQuarter ∈ Q := by
    change ρ orbitQuarter ∈ Subgroup.map ρ.toMonoidHom
      (Q₀ : Subgroup (Equiv.Perm (Fin 4)))
    exact ⟨orbitQuarter, hτQ₀, rfl⟩
  have haQ : ρ orbitA ∈ Q := by
    change ρ orbitA ∈ Subgroup.map ρ.toMonoidHom
      (Q₀ : Subgroup (Equiv.Perm (Fin 4)))
    exact ⟨orbitA, haQ₀, rfl⟩
  have hbQ : ρ orbitB ∈ Q := by
    change ρ orbitB ∈ Subgroup.map ρ.toMonoidHom
      (Q₀ : Subgroup (Equiv.Perm (Fin 4)))
    exact ⟨orbitB, hbQ₀, rfl⟩
  let aK : baseSetwiseStabilizer (G := G) ef :=
    ⟨a, mem_baseSetwiseStabilizer_of_base_perm (G := G) ef a orbitA haBase⟩
  let bK : baseSetwiseStabilizer (G := G) ef :=
    ⟨b, mem_baseSetwiseStabilizer_of_base_perm (G := G) ef b orbitB hbBase⟩
  have haImage : baseSetwisePermHom (G := G) ef aK = ρ orbitA := by
    simpa only [aK, ρ, rangeBasePerm] using
      baseSetwisePermHom_eq_rangeBasePerm ef a orbitA haBase
  have hbImage : baseSetwisePermHom (G := G) ef bK = ρ orbitB := by
    simpa only [bK, ρ, rangeBasePerm] using
      baseSetwisePermHom_eq_rangeBasePerm ef b orbitB hbBase
  let L := baseSubgroupPreimage (G := G) ef (Q : Subgroup _)
  let φ : L →* Q := baseSubgroupQuotientHom (G := G) ef (Q : Subgroup _)
  let aL : L := ⟨aK, by
    change baseSetwisePermHom (G := G) ef aK ∈ Q
    rw [haImage]
    exact haQ⟩
  let bL : L := ⟨bK, by
    change baseSetwisePermHom (G := G) ef bK ∈ Q
    rw [hbImage]
    exact hbQ⟩
  have hφa : φ aL = ⟨ρ orbitA, haQ⟩ := by
    apply Subtype.ext
    exact haImage
  have hφb : φ bL = ⟨ρ orbitB, hbQ⟩ := by
    apply Subtype.ext
    exact hbImage
  have haLTwo : aL ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact haTwo
  have hbLTwo : bL ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hbTwo
  have habL : Commute aL bL := by
    change aL * bL = bL * aL
    apply Subtype.ext
    apply Subtype.ext
    exact hab.eq
  let V : Subgroup L := Subgroup.closure ({aL, bL} : Set L)
  have hVtwo : IsPGroup 2 V :=
    closure_pair_isPGroup_two aL bL haLTwo hbLTwo habL
  obtain ⟨S, hVS⟩ := hVtwo.exists_le_sylow
  have hφsurj : Function.Surjective φ :=
    baseSubgroupQuotientHom_surjective h4 ef (Q : Subgroup _)
  let Sbar : Sylow 2 Q := Sylow.mapSurjective hφsurj S
  have htopIsP : IsPGroup 2 (⊤ : Subgroup Q) := Q.isPGroup'.to_subgroup ⊤
  have htop : (⊤ : Subgroup Q) = (Sbar : Subgroup Q) :=
    Sbar.is_maximal' htopIsP le_top
  let τQ : Q := ⟨ρ orbitQuarter, hτQ⟩
  have hτSbar : τQ ∈ (Sbar : Subgroup Q) := by
    rw [← htop]
    trivial
  change τQ ∈ Subgroup.map φ (S : Subgroup L) at hτSbar
  obtain ⟨uL, huS, hφu⟩ := hτSbar
  have haV : aL ∈ V := Subgroup.subset_closure (by simp)
  have hbV : bL ∈ V := Subgroup.subset_closure (by simp)
  have haS : aL ∈ (S : Subgroup L) := hVS haV
  have hbS : bL ∈ (S : Subgroup L) := hVS hbV
  have hoddKer : Odd (Nat.card φ.ker) := by
    rw [natCard_baseSubgroupKer_eq_pointwiseStabilizer ef (Q : Subgroup _)]
    exact hoddEf
  obtain ⟨r, hScard⟩ := S.isPGroup'.exists_card_eq
  have hcoprime : (Nat.card (S : Subgroup L)).Coprime (Nat.card φ.ker) := by
    rw [hScard]
    exact (Nat.coprime_two_left.mpr hoddKer).pow_left r
  have hdisjoint : Disjoint (S : Subgroup L) φ.ker :=
    Subgroup.disjoint_of_coprime_natCard hcoprime
  have hφinj {x z : L} (hx : x ∈ (S : Subgroup L))
      (hz : z ∈ (S : Subgroup L)) (hxz : φ x = φ z) : x = z := by
    have hSxz : x * z⁻¹ ∈ (S : Subgroup L) :=
      (S : Subgroup L).mul_mem hx ((S : Subgroup L).inv_mem hz)
    have hKxz : x * z⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxz, mul_inv_cancel]
    have hone : x * z⁻¹ = 1 :=
      (Subgroup.disjoint_def.mp hdisjoint) hSxz hKxz
    calc
      x = (x * z⁻¹) * z := by group
      _ = z := by rw [hone, one_mul]
  have hφu' : φ uL = τQ := hφu
  have huSqL : uL ^ 2 = aL := by
    apply hφinj ((S : Subgroup L).pow_mem huS 2) haS
    rw [map_pow, hφu', hφa]
    apply Subtype.ext
    change (ρ orbitQuarter) ^ 2 = ρ orbitA
    rw [← map_pow, orbitQuarter_sq]
  have hubL : uL * bL = (aL * bL) * uL := by
    apply hφinj ((S : Subgroup L).mul_mem huS hbS)
      ((S : Subgroup L).mul_mem
        ((S : Subgroup L).mul_mem haS hbS) huS)
    rw [map_mul, map_mul, map_mul, hφu', hφa, hφb]
    apply Subtype.ext
    change ρ orbitQuarter * ρ orbitB =
      (ρ orbitA * ρ orbitB) * ρ orbitQuarter
    simpa only [map_mul] using congrArg ρ orbitQuarter_mul_orbitB
  have huaL : uL * aL = aL * uL := by
    rw [← huSqL]
    group
  let uK : baseSetwiseStabilizer (G := G) ef := uL
  let u : G := uK
  have hφuVal : baseSetwisePermHom (G := G) ef uK = ρ orbitQuarter := by
    exact congrArg Subtype.val hφu'
  have huBase : ∀ i, u • ef i = ef (orbitQuarter i) := by
    apply Research.HallInvolutionConsequence.smul_base_of_setwisePermHom_eq
      ef uK orbitQuarter
    simpa only [ρ] using hφuVal
  refine ⟨u, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [u, uK, ef, f, orbitQuarter] using huBase 0
  · simpa [u, uK, ef, f, orbitQuarter, c] using huBase 1
  · simpa [u, uK, ef, f, orbitQuarter] using huBase 2
  · simpa [u, uK, ef, f, orbitQuarter, c] using huBase 3
  · exact congrArg (fun z : L ↦ ((((z : L) :
      baseSetwiseStabilizer (G := G) ef) : G))) huSqL
  · exact congrArg (fun z : L ↦ ((((z : L) :
      baseSetwiseStabilizer (G := G) ef) : G))) huaL
  · exact congrArg (fun z : L ↦ ((((z : L) :
      baseSetwiseStabilizer (G := G) ef) : G))) hubL

end FiveTransitive.Research.HallDihedralLifts

end CFSG
