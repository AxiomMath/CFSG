module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section8

universe v
universe w
universe u

@[expose] public def theorem_8_5_c_statement
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G) : Prop :=
  typePDefinitionData M MF U W1 W2 →
    section16TISubsetWithNormalizer (section16HatW W1 W2) (W1 ⊔ W2)


/-- Peterfalvi Definition `(8.7)`. -/


private theorem typeP_hallSubgroupOf_of_le
    {G : Type u} [Group G] [Finite G]
    {H K L : Subgroup G}
    (hHall : section16HallSubgroupOf H L)
    (hHK : H ≤ K) (hKL : K ≤ L) :
    section16HallSubgroupOf H K := by
  classical
  rcases hHall with ⟨hHL, hHallL⟩
  refine ⟨hHK, ?_⟩
  refine isHallSubgroup_of (G := K) (π := subgroupPrimeSet H)
    (H := H.subgroupOf K) ?_ ?_
  · intro p hp
    have hcardK : Nat.card (H.subgroupOf K) = Nat.card H := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := H) (K := K) hHK).toEquiv
    simpa [subgroupPrimeSet, hcardK] using hp
  · intro p hpπ hpidx
    let KsubL : Subgroup L := K.subgroupOf L
    have hHsub_le_Ksub : H.subgroupOf L ≤ KsubL := by
      intro x hx
      exact hHK hx
    have hrel_eq :
        (H.subgroupOf K).index = (H.subgroupOf L).relIndex KsubL := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := H) (K := K) (L := L) hKL
      simpa [KsubL, Subgroup.relIndex] using hsub.symm
    have hidx_dvd :
        (H.subgroupOf K).index ∣ (H.subgroupOf L).index := by
      have hrel_dvd :
          (H.subgroupOf L).relIndex KsubL ∣ (H.subgroupOf L).index :=
        Subgroup.relIndex_dvd_index_of_le hHsub_le_Ksub
      simpa [hrel_eq] using hrel_dvd
    exact (hHallL.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ

private theorem typeP_complement_isHall_compl_of_isHall
    {R : Type u} [Group R] [Finite R] {π : Set Nat.Primes}
    {K D : Subgroup R}
    (hKHall : IsHallSubgroup π K)
    (hcomp : K.IsComplement' D) :
    IsHallSubgroup πᶜ D := by
  classical
  refine isHallSubgroup_of (G := R) (π := πᶜ) (H := D) ?_ ?_
  · intro q hqD hqπ
    have hqKidx : q.val ∣ K.index := by
      simpa [hcomp.symm.index_eq_card] using hqD
    exact (hKHall.p_in_pi_of_p_dvd_index q hqKidx) hqπ
  · intro q hqπc hqDidx
    have hqK : q.val ∣ Nat.card K := by
      simpa [hcomp.index_eq_card] using hqDidx
    exact hqπc (hKHall.p_in_pi_of_p_dvd_card q hqK)

private theorem typeP_W1_le_M
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    W1 ≤ M := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  exact hW1hall.1

private theorem typeP_W2_le_M
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    W2 ≤ M := by
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  rcases hMF.1 with ⟨hMFM, _hMFnormM, _hMFnil, _hMFHallM⟩
  exact hW2le.trans inf_le_left |>.trans hMFM


private theorem typeP_W1_inf_W2_eq_bot
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    W1 ⊓ W2 = ⊥ := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  apply le_antisymm
  · intro x hx
    have hxD : x ∈ ambientDerivedSubgroup M :=
      (by
        have hDerDer_le_Der :
            section16SecondDerivedSubgroup M ≤ ambientDerivedSubgroup M := by
          simpa [section16SecondDerivedSubgroup] using
            (section12_ambientDerivedSubgroup_le (G := G)
              (E := ambientDerivedSubgroup M))
        exact hDerDer_le_Der (hW2le hx.2).2)
    have hxInf : x ∈ ambientDerivedSubgroup M ⊓ W1 := ⟨hxD, hx.1⟩
    simpa [hcompMW1.2.2.2.eq_bot] using hxInf
  · exact bot_le


private theorem typeP_W_isMulCommutative
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    IsMulCommutative (W1 ⊔ W2 : Subgroup G) := by
  classical
  rcases hP with
    ⟨_hMF, hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, hW2le, hW2cyc, _hW2ne,
      hcentW1, _hnormX⟩
  have hW2centW1 : W2 ≤ Subgroup.centralizer (W1 : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    by_cases hx1 : x = 1
    · simp [hx1]
    · have hyCent : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := by
        simpa [hcentW1 x hx hx1] using hy
      exact (Subgroup.mem_centralizer_singleton_iff.mp hyCent.2).symm
  letI : IsCyclic W1 := hW1cyc
  letI : IsCyclic W2 := hW2cyc
  let D : Subgroup G := W1 ⊔ W2
  let W1D : Subgroup D := W1.subgroupOf D
  let W2D : Subgroup D := W2.subgroupOf D
  have hW1_norm_W2 : W1 ≤ Subgroup.normalizer (W2 : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hcomm : a * y = y * a :=
        Subgroup.mem_centralizer_iff.mp (hW2centW1 hy) a ha
      have hconj : a * y * a⁻¹ = y := by
        calc
          a * y * a⁻¹ = y * a * a⁻¹ := by rw [hcomm]
          _ = y := by simp [mul_assoc]
      simpa [hconj] using hy
    · intro hy
      let y' : G := a * y * a⁻¹
      have hy'W2 : y' ∈ W2 := by simpa [y'] using hy
      have hcomm' : a * y' = y' * a :=
        Subgroup.mem_centralizer_iff.mp (hW2centW1 hy'W2) a ha
      have hconj : a⁻¹ * y' * a = y' := by
        have h := congrArg (fun t : G => a⁻¹ * t) hcomm'
        simpa [mul_assoc] using h.symm
      have hy_eq : y = y' := by
        calc
          y = a⁻¹ * y' * a := by simp [y', mul_assoc]
          _ = y' := hconj
      simpa [hy_eq] using hy'W2
  haveI : W2D.Normal := by
    simpa [D, W2D] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := W1) (N := W2) hW1_norm_W2)
  have hW1D_W2D_top : W1D ⊔ W2D = ⊤ := by
    calc
      W1D ⊔ W2D = D.subgroupOf D := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := W1) (A' := W2) (B := D)
          (by simp [D])
          (by simp [D])
      _ = ⊤ := by simp
  refine ⟨⟨fun x y => ?_⟩⟩
  have hxTop : x ∈ W1D ⊔ W2D := by simp [hW1D_W2D_top]
  have hyTop : y ∈ W1D ⊔ W2D := by simp [hW1D_W2D_top]
  rcases (Subgroup.mem_sup_of_normal_right (s := W1D) (t := W2D) (x := x)).1 hxTop with
    ⟨aD, haD, bD, hbD, hxab⟩
  rcases (Subgroup.mem_sup_of_normal_right (s := W1D) (t := W2D) (x := y)).1 hyTop with
    ⟨cD, hcD, dD, hdD, hycd⟩
  let a : G := aD
  let b : G := bD
  let c : G := cD
  let d : G := dD
  have haW1 : a ∈ W1 := by simpa [a, W1D, Subgroup.mem_subgroupOf] using haD
  have hbW2 : b ∈ W2 := by simpa [b, W2D, Subgroup.mem_subgroupOf] using hbD
  have hcW1 : c ∈ W1 := by simpa [c, W1D, Subgroup.mem_subgroupOf] using hcD
  have hdW2 : d ∈ W2 := by simpa [d, W2D, Subgroup.mem_subgroupOf] using hdD
  have hx_eq : (x : G) = a * b := by
    have hval := congrArg (fun z : D => (z : G)) hxab
    simpa [a, b] using hval.symm
  have hy_eq : (y : G) = c * d := by
    have hval := congrArg (fun z : D => (z : G)) hycd
    simpa [c, d] using hval.symm
  have hac : a * c = c * a :=
    setLike_mul_comm (s := W1) haW1 hcW1
  have hbd : b * d = d * b :=
    setLike_mul_comm (s := W2) hbW2 hdW2
  have hbc : b * c = c * b :=
    (Subgroup.mem_centralizer_iff.mp (hW2centW1 hbW2) c hcW1).symm
  have had : a * d = d * a :=
    Subgroup.mem_centralizer_iff.mp (hW2centW1 hdW2) a haW1
  apply Subtype.ext
  change (x : G) * (y : G) = (y : G) * (x : G)
  rw [hx_eq, hy_eq]
  calc
    (a * b) * (c * d) = a * (b * c) * d := by simp [mul_assoc]
    _ = a * (c * b) * d := by rw [hbc]
    _ = (a * c) * (b * d) := by simp [mul_assoc]
    _ = (c * a) * (d * b) := by rw [hac, hbd]
    _ = c * (a * d) * b := by simp [mul_assoc]
    _ = c * (d * a) * b := by rw [had]
    _ = (c * d) * (a * b) := by simp [mul_assoc]

private theorem typeP_hatW_nonempty
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    (section16HatW W1 W2).Nonempty := by
  classical
  have hP0 := hP
  rcases hP with
    ⟨_hMF, _hW1cyc, hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, hW2ne,
      _hcentW1, _hnormX⟩
  have hdisj : W1 ⊓ W2 = ⊥ :=
    typeP_W1_inf_W2_eq_bot (M := M) (MF := MF) (U := U) hP0
  obtain ⟨a, haW1, ha1⟩ : ∃ a : G, a ∈ W1 ∧ a ≠ 1 := by
    by_contra hnone
    apply hW1ne
    apply le_antisymm
    · intro x hx
      have hx1 : x = 1 := by
        by_contra hxne
        exact hnone ⟨x, hx, hxne⟩
      simp [hx1]
    · exact bot_le
  obtain ⟨b, hbW2, hb1⟩ : ∃ b : G, b ∈ W2 ∧ b ≠ 1 := by
    by_contra hnone
    apply hW2ne
    apply le_antisymm
    · intro x hx
      have hx1 : x = 1 := by
        by_contra hxne
        exact hnone ⟨x, hx, hxne⟩
      simp [hx1]
    · exact bot_le
  refine ⟨a * b, ?_⟩
  constructor
  · exact Subgroup.mul_mem_sup haW1 hbW2
  · intro hab
    rcases hab with habW1 | habW2
    · have hbW1 : b ∈ W1 := by
        have h : a⁻¹ * (a * b) ∈ W1 := W1.mul_mem (W1.inv_mem haW1) habW1
        simpa [mul_assoc] using h
      have hbInf : b ∈ W1 ⊓ W2 := ⟨hbW1, hbW2⟩
      have hbBot : b ∈ (⊥ : Subgroup G) := by simpa [hdisj] using hbInf
      exact hb1 (by simpa using hbBot)
    · have haW2 : a ∈ W2 := by
        have h : (a * b) * b⁻¹ ∈ W2 := W2.mul_mem habW2 (W2.inv_mem hbW2)
        simpa [mul_assoc] using h
      have haInf : a ∈ W1 ⊓ W2 := ⟨haW1, haW2⟩
      have haBot : a ∈ (⊥ : Subgroup G) := by simpa [hdisj] using haInf
      exact ha1 (by simpa using haBot)

private theorem typeP_hatW_normalizer_eq_self
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    Subgroup.normalizer (section16HatW W1 W2) = W1 ⊔ W2 := by
  have hP0 := hP
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, hnormX⟩
  exact hnormX (section16HatW W1 W2) (typeP_hatW_nonempty hP0) (fun _ hx => hx)

private theorem typeP_W1_characteristic_in_W
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    (W1.subgroupOf (W1 ⊔ W2 : Subgroup G)).Characteristic := by
  classical
  let W : Subgroup G := W1 ⊔ W2
  have hWcomm : IsMulCommutative W := by
    simpa [W] using typeP_W_isMulCommutative (M := M) (MF := MF) (U := U) hP
  letI : IsMulCommutative W := hWcomm
  haveI : (W1.subgroupOf W).Normal := by infer_instance
  have hW1leM : W1 ≤ M := typeP_W1_le_M (MF := MF) (U := U) (W2 := W2) hP
  have hW2leM : W2 ≤ M := typeP_W2_le_M (MF := MF) (U := U) (W1 := W1) hP
  have hWleM : W ≤ M := by
    simpa [W] using sup_le hW1leM hW2leM
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  have hW1HallW : IsHallSubgroup (subgroupPrimeSet W1) (W1.subgroupOf W) :=
    (typeP_hallSubgroupOf_of_le (H := W1) (K := W) (L := M)
      hW1hall (by simp [W]) hWleM).2
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  exact hW1HallW.eq_of_normal (hW1HallW.map_mulAut φ)

private theorem typeP_W2_characteristic_in_W
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    (W2.subgroupOf (W1 ⊔ W2 : Subgroup G)).Characteristic := by
  classical
  let W : Subgroup G := W1 ⊔ W2
  have hWcomm : IsMulCommutative W := by
    simpa [W] using typeP_W_isMulCommutative (M := M) (MF := MF) (U := U) hP
  letI : IsMulCommutative W := hWcomm
  haveI : (W1.subgroupOf W).Normal := by infer_instance
  haveI : (W2.subgroupOf W).Normal := by infer_instance
  have hW1leM : W1 ≤ M := typeP_W1_le_M (MF := MF) (U := U) (W2 := W2) hP
  have hW2leM : W2 ≤ M := typeP_W2_le_M (MF := MF) (U := U) (W1 := W1) hP
  have hWleM : W ≤ M := by
    simpa [W] using sup_le hW1leM hW2leM
  have hW1disjW2 : W1 ⊓ W2 = ⊥ :=
    typeP_W1_inf_W2_eq_bot (M := M) (MF := MF) (U := U) hP
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  have hW1HallW : IsHallSubgroup (subgroupPrimeSet W1) (W1.subgroupOf W) :=
    (typeP_hallSubgroupOf_of_le (H := W1) (K := W) (L := M)
      hW1hall (by simp [W]) hWleM).2
  have hdisjSub : Disjoint (W1.subgroupOf W) (W2.subgroupOf W) := by
    rw [disjoint_iff]
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ W1 ⊓ W2 := by
        exact ⟨by simpa [W, Subgroup.mem_subgroupOf] using hx.1,
          by simpa [W, Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hW1disjW2] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hsupTop : W1.subgroupOf W ⊔ W2.subgroupOf W = ⊤ := by
    calc
      W1.subgroupOf W ⊔ W2.subgroupOf W = W.subgroupOf W := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := W1) (A' := W2) (B := W)
          (by simp [W])
          (by simp [W])
      _ = ⊤ := by simp
  have hcomp : (W1.subgroupOf W).IsComplement' (W2.subgroupOf W) :=
    isComplement'_of_disjoint_sup_eq_top_of_normal
      (W1.subgroupOf W) (W2.subgroupOf W) hdisjSub hsupTop
  have hW2HallW : IsHallSubgroup (subgroupPrimeSet W1)ᶜ (W2.subgroupOf W) :=
    typeP_complement_isHall_compl_of_isHall hW1HallW hcomp
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  exact hW2HallW.eq_of_normal (hW2HallW.map_mulAut φ)

private theorem typeP_hatW_conj_mem_of_mem_normalizer_W
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2)
    {g x : G}
    (hgW : g ∈ Subgroup.normalizer ((W1 ⊔ W2 : Subgroup G) : Set G))
    (hx : x ∈ section16HatW W1 W2) :
    g * x * g⁻¹ ∈ section16HatW W1 W2 := by
  classical
  let W : Subgroup G := W1 ⊔ W2
  let φ : MulAut W :=
    Subgroup.normalizerMonoidHom (H := W) ⟨g, by simpa [W] using hgW⟩
  let xW : W := ⟨x, by simpa [W, section16HatW] using hx.1⟩
  have hW1char : (W1.subgroupOf W).Characteristic := by
    simpa [W] using typeP_W1_characteristic_in_W (M := M) (MF := MF) (U := U) hP
  have hW2char : (W2.subgroupOf W).Characteristic := by
    simpa [W] using typeP_W2_characteristic_in_W (M := M) (MF := MF) (U := U) hP
  have hW1map_symm :
      (W1.subgroupOf W).map φ.symm.toMonoidHom = W1.subgroupOf W :=
    Subgroup.characteristic_iff_map_eq.mp hW1char φ.symm
  have hW2map_symm :
      (W2.subgroupOf W).map φ.symm.toMonoidHom = W2.subgroupOf W :=
    Subgroup.characteristic_iff_map_eq.mp hW2char φ.symm
  constructor
  · exact (Subgroup.mem_normalizer_iff.mp hgW x).1 hx.1
  · intro hbad
    rcases hbad with hW1 | hW2
    · have hφxW1 : φ xW ∈ W1.subgroupOf W := by
        change ((φ xW : W) : G) ∈ W1
        simpa [φ, xW, W, Subgroup.normalizerMonoidHom_apply_apply_coe] using hW1
      have hxW1Sub : xW ∈ W1.subgroupOf W := by
        have hmap : φ.symm (φ xW) ∈ (W1.subgroupOf W).map φ.symm.toMonoidHom :=
          Subgroup.mem_map.mpr ⟨φ xW, hφxW1, rfl⟩
        rw [hW1map_symm] at hmap
        simpa using hmap
      exact hx.2 (Or.inl (by simpa [xW, W, Subgroup.mem_subgroupOf] using hxW1Sub))
    · have hφxW2 : φ xW ∈ W2.subgroupOf W := by
        change ((φ xW : W) : G) ∈ W2
        simpa [φ, xW, W, Subgroup.normalizerMonoidHom_apply_apply_coe] using hW2
      have hxW2Sub : xW ∈ W2.subgroupOf W := by
        have hmap : φ.symm (φ xW) ∈ (W2.subgroupOf W).map φ.symm.toMonoidHom :=
          Subgroup.mem_map.mpr ⟨φ xW, hφxW2, rfl⟩
        rw [hW2map_symm] at hmap
        simpa using hmap
      exact hx.2 (Or.inr (by simpa [xW, W, Subgroup.mem_subgroupOf] using hxW2Sub))

private theorem typeP_mem_normalizer_singleton_of_mem_centralizer_singleton
    {G : Type u} [Group G] {a c : G}
    (hc : c ∈ Subgroup.centralizer ({a} : Set G)) :
    c ∈ Subgroup.normalizer ({a} : Set G) := by
  have hcomm : c * a = a * c :=
    Subgroup.mem_centralizer_singleton_iff.mp hc
  have hfix : c * a * c⁻¹ = a := by
    calc
      c * a * c⁻¹ = a * c * c⁻¹ := by rw [hcomm]
      _ = a := by simp [mul_assoc]
  change ∀ y : G, y ∈ ({a} : Set G) ↔ c * y * c⁻¹ ∈ ({a} : Set G)
  intro y
  constructor
  · intro hy
    have hy_eq : y = a := by simpa using hy
    simp [hy_eq, hfix]
  · intro hy
    have hy_eq : c * y * c⁻¹ = a := by simpa using hy
    have hfix_inv : c⁻¹ * a * c = a := by
      have h := congrArg (fun z : G => c⁻¹ * z * c) hfix
      simpa [mul_assoc] using h.symm
    have hy_a : y = a := by
      calc
        y = c⁻¹ * (c * y * c⁻¹) * c := by group
        _ = c⁻¹ * a * c := by rw [hy_eq]
        _ = a := hfix_inv
    simp [hy_a]

private theorem typeP_mem_normalizer_of_conjBy_eq
    {G : Type u} [Group G] {H : Subgroup G} {g : G}
    (hg : H.conjBy g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g :=
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    simpa [hg] using hx'
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by
      simpa [hg] using hx
    rcases hx' with ⟨y, hy, hyx⟩
    have hxy : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹) * g := by
          rw [show g * x * g⁻¹ = g * y * g⁻¹ by
            simpa [MulAut.conj_apply] using hyx.symm]
        _ = y := by group
    simpa [hxy] using hy

private theorem typeP_mem_normalizer_of_conjBy_le_self
    {G : Type u} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (hg : H.conjBy g ≤ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  have hcard : Nat.card (H.conjBy g) = Nat.card H := by
    simpa [Subgroup.conjBy] using
      (Subgroup.card_map_of_injective (K := H) (f := (MulAut.conj g).toMonoidHom)
        (hf := EquivLike.injective (MulAut.conj g)))
  have hEq : H.conjBy g = H := Subgroup.eq_of_le_of_card_ge hg (by simp [hcard])
  exact typeP_mem_normalizer_of_conjBy_eq hEq

private theorem typeP_singleton_hatW_normalizer_eq_self
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2)
    {v : G} (hv : v ∈ section16HatW W1 W2) :
    Subgroup.normalizer ({v} : Set G) = W1 ⊔ W2 := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, hnormX⟩
  exact hnormX ({v} : Set G) ⟨v, rfl⟩
    (by
      intro y hy
      have hy_eq : y = v := by simpa using hy
      simpa [hy_eq] using hv)

private theorem typeP_hatW_conjugateSet_eq_of_mem_normalizer_W
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2)
    {g : G}
    (hgW : g ∈ Subgroup.normalizer ((W1 ⊔ W2 : Subgroup G) : Set G)) :
    section16ConjugateSet (section16HatW W1 W2) g = section16HatW W1 W2 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact typeP_hatW_conj_mem_of_mem_normalizer_W
      (M := M) (MF := MF) (U := U) hP hgW hx
  · intro hy
    have hginvW : g⁻¹ ∈ Subgroup.normalizer ((W1 ⊔ W2 : Subgroup G) : Set G) :=
      (Subgroup.normalizer ((W1 ⊔ W2 : Subgroup G) : Set G)).inv_mem hgW
    have hx :=
      typeP_hatW_conj_mem_of_mem_normalizer_W
        (M := M) (MF := MF) (U := U) hP hginvW hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · simpa [mul_assoc] using hx
    · group

private theorem typeP_conjBy_W_le_W_of_hatW_inter_conj_nonempty
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2)
    {g v x : G}
    (hv : v ∈ section16HatW W1 W2)
    (hx : x ∈ section16HatW W1 W2)
    (hv_eq : v = g * x * g⁻¹) :
    (W1 ⊔ W2 : Subgroup G).conjBy g ≤ W1 ⊔ W2 := by
  classical
  let W : Subgroup G := W1 ⊔ W2
  have hWcomm : IsMulCommutative W := by
    simpa [W] using typeP_W_isMulCommutative (M := M) (MF := MF) (U := U) hP
  have hsingNorm :
      Subgroup.normalizer ({v} : Set G) = W := by
    simpa [W] using typeP_singleton_hatW_normalizer_eq_self
      (M := M) (MF := MF) (U := U) hP hv
  intro y hy
  rcases Subgroup.mem_map.mp hy with ⟨w, hwW, rfl⟩
  have hcent : g * w * g⁻¹ ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : w * x = x * w :=
      setLike_mul_comm (s := W) hwW (by simpa [W] using hx.1)
    rw [hv_eq]
    calc
      (g * w * g⁻¹) * (g * x * g⁻¹) = g * (w * x) * g⁻¹ := by group
      _ = g * (x * w) * g⁻¹ := by rw [hcomm]
      _ = (g * x * g⁻¹) * (g * w * g⁻¹) := by group
  have hnorm :
      g * w * g⁻¹ ∈ Subgroup.normalizer ({v} : Set G) :=
    typeP_mem_normalizer_singleton_of_mem_centralizer_singleton hcent
  simpa [W, hsingNorm, MulAut.conj_apply] using hnorm

public theorem theorem_8_5_c
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G) :
    theorem_8_5_c_statement M MF U W1 W2 := by
  intro hP
  refine ⟨?_, typeP_hatW_normalizer_eq_self hP⟩
  intro g
  by_cases hnonempty :
      (section16HatW W1 W2 ∩
        section16ConjugateSet (section16HatW W1 W2) g).Nonempty
  · left
    rcases hnonempty with ⟨v, hv, hvconj⟩
    rcases hvconj with ⟨x, hx, hv_eq⟩
    have hWle :
        (W1 ⊔ W2 : Subgroup G).conjBy g ≤ W1 ⊔ W2 :=
      typeP_conjBy_W_le_W_of_hatW_inter_conj_nonempty
        (M := M) (MF := MF) (U := U) hP hv hx hv_eq
    have hgW : g ∈ Subgroup.normalizer ((W1 ⊔ W2 : Subgroup G) : Set G) :=
      typeP_mem_normalizer_of_conjBy_le_self hWle
    exact typeP_hatW_conjugateSet_eq_of_mem_normalizer_W
      (M := M) (MF := MF) (U := U) hP hgW
  · right
    intro y hy
    exact False.elim (hnonempty ⟨y, hy.1, hy.2⟩)

end CFSG.Section8
