module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection14.lemma_14_5

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Lemma 14 6 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
private theorem CFSG.section14_eq_left_or_right_of_alt1_alt2_product
    {x x' y y' : G} {M : Subgroup G}
    (hx : section14SigmaLength x = 1)
    (hxr : x' ∈ section14R x)
    (hy : section14SigmaLength y = 1)
    (hy'ne : y' ≠ 1)
    (hy'sigma' : section14IsPiElement (section10SigmaPrimes M)ᶜ y')
    (hy'cent : y' ∈ elementCentralizerIn M y)
    (hM : M ∈ section14MsigmaElement y)
    (hEq : x * x' = y * y') :
    (y = x ∧ y' = x') ∨ (y = x' ∧ y' = x) := by
  have hxne : x ≠ 1 := section14_sigmaLength_one_ne_one hx
  have hyne : y ≠ 1 := section14_sigmaLength_one_ne_one hy
  have support_dvd {a : G} {p : Nat.Primes}
      (hp : p ∈ section14ElementPrimeSupport a) :
      p.val ∣ orderOf a := by
    simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hp
  have dvd_support {a : G} {p : Nat.Primes}
      (hp : p.val ∣ orderOf a) :
      p ∈ section14ElementPrimeSupport a := by
    simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hp
  have support_mono {a b : G} (hab : a ∈ Subgroup.zpowers b) :
      section14ElementPrimeSupport a ⊆ section14ElementPrimeSupport b := by
    intro p hp
    exact section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hab) hp
  have sigma_unique {a : G} (ha : section14SigmaLength a = 1) :
      ∀ {π₁ π₂ : Set Nat.Primes},
        π₁ ∈ section14SigmaSupport a →
        π₂ ∈ section14SigmaSupport a → π₁ = π₂ := by
    obtain ⟨π0, hπ0, huniq⟩ := section14_unique_sigma_block_of_length_one ha
    intro π₁ π₂ h₁ h₂
    exact (huniq _ h₁).trans (huniq _ h₂).symm
  have support_subset_left_or_right
      {a : G} (ha : section14SigmaLength a = 1)
      {π₁ π₂ : Set Nat.Primes}
      (hπ₁ : π₁ ∈ section14SigmaBlocks G)
      (hπ₂ : π₂ ∈ section14SigmaBlocks G)
      (hdisj : Disjoint π₁ π₂)
      (hcover : section14ElementPrimeSupport a ⊆ π₁ ∪ π₂) :
      section14ElementPrimeSupport a ⊆ π₁ ∨
        section14ElementPrimeSupport a ⊆ π₂ := by
    obtain ⟨q, z, hz_zpowa, _hzA, _hz_ne, hzprime⟩ :=
      section14_exists_primeOrder_zpowers_in (G := G)
        (B := Subgroup.zpowers a) (Subgroup.mem_zpowers a)
        (section14_sigmaLength_one_ne_one ha)
    have hqA : q ∈ section14ElementPrimeSupport a := by
      have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
        rw [subgroupPrimeSet]
        rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
          ⟨_hzle, hqcard⟩
        simp [hqcard]
      simpa [section14ElementPrimeSupport] using
        section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hz_zpowa) hqz
    rcases hcover hqA with hq₁ | hq₂
    · left
      intro p hpA
      rcases hcover hpA with hp₁ | hp₂
      · exact hp₁
      · have hπ₁A : π₁ ∈ section14SigmaSupport a := ⟨hπ₁, ⟨q, hqA, hq₁⟩⟩
        have hπ₂A : π₂ ∈ section14SigmaSupport a := ⟨hπ₂, ⟨p, hpA, hp₂⟩⟩
        have hEqπ : π₁ = π₂ := sigma_unique ha hπ₁A hπ₂A
        exact False.elim ((Set.disjoint_left.mp hdisj) hq₁ (hEqπ ▸ hq₁))
    · right
      intro p hpA
      rcases hcover hpA with hp₁ | hp₂
      · have hπ₁A : π₁ ∈ section14SigmaSupport a := ⟨hπ₁, ⟨p, hpA, hp₁⟩⟩
        have hπ₂A : π₂ ∈ section14SigmaSupport a := ⟨hπ₂, ⟨q, hqA, hq₂⟩⟩
        have hEqπ : π₁ = π₂ := sigma_unique ha hπ₁A hπ₂A
        exact False.elim ((Set.disjoint_left.mp hdisj) hp₁ (hEqπ ▸ hp₁))
      · exact hp₂
  let B : Set Nat.Primes := section10SigmaPrimes M
  have hB_block : B ∈ section14SigmaBlocks G := ⟨M, hM.1, rfl⟩
  have hyB : section14ElementPrimeSupport y ⊆ B :=
    section14_primeSupport_subset_sigma_of_msigmaMember hM
  have hy'Bc : section14ElementPrimeSupport y' ⊆ Bᶜ := hy'sigma'
  have hyy'Comm : Commute y y' := by
    exact (Subgroup.mem_centralizer_singleton_iff.mp hy'cent.2).symm
  have hcopy : Nat.Coprime (orderOf y) (orderOf y') :=
    section14_coprime_order_of_support_split
      (π := Bᶜ) (by simpa using hyB) hy'Bc
  have sigmaSupport_mono {a b : G}
      (hab : section14ElementPrimeSupport a ⊆ section14ElementPrimeSupport b) :
      section14SigmaSupport a ⊆ section14SigmaSupport b := by
    intro π hπ
    rcases hπ with ⟨hπblock, ⟨p, hpA, hpπ⟩⟩
    exact ⟨hπblock, ⟨p, hab hpA, hpπ⟩⟩
  by_cases hx'1 : x' = 1
  · have hEqx : x = y * y' := by
      simpa [hx'1] using hEq
    have hyG0 : y ∈ Subgroup.zpowers (y * y') :=
      section14_mem_zpowers_mul_of_commute_of_coprime_order hyy'Comm hcopy
    have hyG : y ∈ Subgroup.zpowers x := by
      simpa [hEqx] using hyG0
    have hy'G0 : y' ∈ Subgroup.zpowers (y' * y) :=
      section14_mem_zpowers_mul_of_commute_of_coprime_order
        hyy'Comm.symm (by simpa [Nat.coprime_comm] using hcopy)
    have hy'G1 : y' ∈ Subgroup.zpowers (y * y') := by
      simpa [hyy'Comm.eq] using hy'G0
    have hy'G : y' ∈ Subgroup.zpowers x := by
      simpa [hEqx] using hy'G1
    have hB_y : B ∈ section14SigmaSupport y := by
      simp [B, section14_sigmaSupport_eq_singleton_of_length_one hy hM]
    have hB_x : B ∈ section14SigmaSupport x :=
      sigmaSupport_mono (support_mono hyG) hB_y
    have hyMσ : y ∈ section10Msigma M := hM.2 (by simp)
    have hcor :=
      corollary_14_3 (G := G) (M := M) (x := y) (x' := y') hM.1
        hyMσ hyne hy'ne hy'cent hy'sigma'
    rcases hcor with hκ | hτ2
    · obtain ⟨q, z, hz_zpowy', _hzY', _hz_ne, hzprime⟩ :=
        section14_exists_primeOrder_zpowers_in (G := G)
          (B := Subgroup.zpowers y') (Subgroup.mem_zpowers y') hy'ne
      have hqSupp : q ∈ section14ElementPrimeSupport y' := by
        have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
          rw [subgroupPrimeSet]
          rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
            ⟨_hzle, hqcard⟩
          simp [hqcard]
        simpa [section14ElementPrimeSupport] using
          section8_subgroupPrimeSet_mono
            (Subgroup.zpowers_le.2 hz_zpowy') hqz
      have hqκ : q ∈ section14KappaPrimes M := hκ.1 hqSupp
      have hMP : M ∈ section14MFamilyP G := ⟨hM.1, ⟨q, hqκ⟩⟩
      obtain ⟨X, hXzp⟩ :=
        section14_exists_primeOrderSubgroupIn_of_dvd_card
          (G := G) (A := Subgroup.zpowers y') (p := q) hqSupp
      rcases hXzp with ⟨hXle_zpow, hXcard⟩
      have hy'M : y' ∈ M := hy'cent.1
      have hXM : X ≤ M := hXle_zpow.trans (Subgroup.zpowers_le.2 hy'M)
      letI : MulDistribMulAction Unit M := {
        smul := fun _ y => y
        one_smul := fun _ => rfl
        mul_smul := fun _ _ _ => rfl
        smul_mul := fun _ _ _ => rfl
        smul_one := fun _ => rfl }
      let Xsub : Subgroup M := X.subgroupOf M
      have hXsubπ :
          IsPiSubgroup (G := M) (section14KappaPrimes M) Xsub := by
        intro r hrXsub
        have hrdiv : r.val ∣ q.val := by
          have hcard : Nat.card Xsub = Nat.card X := section12_card_subgroupOf_eq hXM
          simpa [Xsub, hcard, hXcard] using hrXsub
        have hreq : r = q :=
          Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 q.2).mp hrdiv)
        simpa [hreq] using hqκ
      have hXsubInv : IsInvariant Unit M Xsub := by
        refine ⟨?_⟩
        intro _ y
        simp [Xsub]
      have hsolvM : IsSolvable M :=
        IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1.1)
      have hcop : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
      obtain ⟨Ksub, hKsubHall, _hKsubInv, hXsubK⟩ :=
        exists_isHallSubgroup_isInvariant_of_isPiSubgroup
          (G := M) (A := Unit) hsolvM hcop (section14KappaPrimes M)
          Xsub hXsubπ hXsubInv
      let K : Subgroup G := Ksub.map M.subtype
      have hK : section12HallSubgroupIn (section14KappaPrimes M) K M :=
        section14_hallSubgroupIn_map_subtype hKsubHall
      have hXK : X ≤ K := by
        intro w hwX
        exact Subgroup.mem_map.mpr
          ⟨⟨w, hXM hwX⟩,
            hXsubK (show (⟨w, hXM hwX⟩ : M) ∈ Xsub from hwX), rfl⟩
      have hXne : X ≠ ⊥ := by
        intro hXbot
        have hcard_one : Nat.card X = 1 := by
          simp [hXbot]
        exact q.2.ne_one (hXcard.symm.trans hcard_one)
      have hXne_top : X ≠ ⊤ := by
        intro hXtop
        have htop_le_M : (⊤ : Subgroup G) ≤ M := by
          simpa [hXtop] using hXM
        exact hM.1.1 (top_le_iff.mp htop_le_M)
      have hNXne_top : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
        intro hNtop
        have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
        letI : IsSimpleGroup G := IsMinCE.simple
        rcases hXnormal.eq_bot_or_eq_top with hXbot | hXtop
        · exact hXne hXbot
        · exact hXne_top hXtop
      obtain ⟨Mstar, hMstar⟩ :=
        section9_exists_maximalSubgroupsContaining_of_ne_top
          (G := G) (H := Subgroup.normalizer (X : Set G)) hNXne_top
      have hqσMstar : q ∈ section10SigmaPrimes Mstar := by
        exact section14_b2_prime_mem_sigma_of_primeOrder
          (G := G) (M := M) (K := K) (X := X) (Mstar := Mstar)
          hMP hK (show X ∈ section10PrimeOrderSubgroupsIn q K from ⟨hXK, hXcard⟩) hMstar
      have hqSuppX : q ∈ section14ElementPrimeSupport x :=
        support_mono hy'G hqSupp
      have hBstar_x : section10SigmaPrimes Mstar ∈ section14SigmaSupport x :=
        ⟨⟨Mstar, hMstar.1, rfl⟩, ⟨q, hqSuppX, hqσMstar⟩⟩
      have hEqσ : section10SigmaPrimes Mstar = B :=
        sigma_unique hx hBstar_x hB_x
      exact False.elim ((hy'Bc hqSupp) (hEqσ.symm ▸ hqσMstar))
    · have hy'SuppX : section14SigmaSupport y' ⊆ section14SigmaSupport x :=
        sigmaSupport_mono (support_mono hy'G)
      obtain ⟨B', hB'y', _huniqB'⟩ :=
        section14_unique_sigma_block_of_length_one hτ2.2.1
      have hEqB' : B' = B :=
        sigma_unique hx (hy'SuppX hB'y') hB_x
      rcases hB'y' with ⟨_hB'block, ⟨q, hqSupp, hqB'⟩⟩
      exact False.elim ((hy'Bc hqSupp) (hEqB' ▸ hqB'))
  · have hx'ne : x' ≠ 1 := hx'1
    obtain ⟨_hx, hσx, hcardx⟩ := section14_nonsingleton_of_mem_R_ne_one hxr hx'ne
    let Mx : Subgroup G := Classical.choose hσx
    have hMx : Mx ∈ section14MsigmaElement x := Classical.choose_spec hσx
    have hNx := section14N_mem_of_nonsingleton (x := x) hxne hσx hcardx
    let Bx : Set Nat.Primes := section10SigmaPrimes Mx
    let π : Set Nat.Primes := section10SigmaPrimes (section14N x)
    have hBx_block : Bx ∈ section14SigmaBlocks G := ⟨Mx, hMx.1, rfl⟩
    have hπ_block : π ∈ section14SigmaBlocks G := ⟨section14N x, hNx.1, rfl⟩
    have hxBx : section14ElementPrimeSupport x ⊆ Bx :=
      section14_primeSupport_subset_sigma_of_msigmaMember hMx
    have hx'π : section14ElementPrimeSupport x' ⊆ π := by
      simpa [π] using section14_primeSupport_subset_sigmaN_of_mem_R hxr
    have hxπc : section14ElementPrimeSupport x ⊆ πᶜ := by
      intro p hpX hpπ
      rcases (by
        simpa [π, section12Tau2Primes] using
          section14_primeSupport_subset_tau2N_of_mem_R_ne_one hxr hx'ne hpX) with
        ⟨hp_not_π, _hprank⟩
      exact hp_not_π hpπ
    have hBx_disj : Disjoint Bx π := by
      rw [Set.disjoint_left]
      intro p hpBx hpπ
      have hEqπ : Bx = π :=
        section14_sigma_eq_of_common_prime hMx.1 hNx.1 hpBx hpπ
      have hxπ : section14ElementPrimeSupport x ⊆ π := by
        simpa [Bx, hEqπ] using hxBx
      exact hxne (section14_eq_one_of_support_subset_and_compl hxπ hxπc)
    have hRdefx :=
      (theorem_14_4_a (G := G) (x := x) hxne hσx hcardx hMx).1
    have hxrCx : x' ∈ elementCentralizerIn (section10Msigma (section14N x)) x := by
      simpa [hRdefx] using hxr
    have hxx'Comm : Commute x x' := by
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxrCx.2).symm
    have hcopx : Nat.Coprime (orderOf x) (orderOf x') :=
      section14_coprime_order_of_support_split hxπc hx'π
    have hdisjxx' : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers x') := by
      have hcopCard :
          Nat.Coprime (Nat.card (Subgroup.zpowers x))
            (Nat.card (Subgroup.zpowers x')) := by
        simpa [Nat.card_zpowers] using hcopx
      exact Subgroup.disjoint_of_coprime_natCard hcopCard
    have hcover_of_memG {a : G} (haG : a ∈ Subgroup.zpowers (x * x')) :
        section14ElementPrimeSupport a ⊆ Bx ∪ π := by
      intro p hpA
      have hpG : p.val ∣ orderOf (x * x') := by
        exact support_dvd (support_mono haG hpA)
      have hpMul : p.val ∣ orderOf x * orderOf x' := by
        simpa [hxx'Comm.orderOf_mul_eq_mul_orderOf_of_coprime hcopx] using hpG
      rcases p.property.dvd_or_dvd hpMul with hpX | hpX'
      · exact Or.inl (hxBx (dvd_support hpX))
      · exact Or.inr (hx'π (dvd_support hpX'))
    have hyG : y ∈ Subgroup.zpowers (x * x') := by
      have hyG0 : y ∈ Subgroup.zpowers (y * y') :=
        section14_mem_zpowers_mul_of_commute_of_coprime_order hyy'Comm hcopy
      simpa [hEq] using hyG0
    have hy'G : y' ∈ Subgroup.zpowers (x * x') := by
      have hy'G0 : y' ∈ Subgroup.zpowers (y' * y) :=
        section14_mem_zpowers_mul_of_commute_of_coprime_order
          hyy'Comm.symm (by simpa [Nat.coprime_comm] using hcopy)
      have hy'G1 : y' ∈ Subgroup.zpowers (y * y') := by
        simpa [hyy'Comm.eq] using hy'G0
      simpa [hEq] using hy'G1
    obtain ⟨q, z, hz_zpowy, _hzY, _hz_ne, hzprime⟩ :=
      section14_exists_primeOrder_zpowers_in (G := G)
        (B := Subgroup.zpowers y) (Subgroup.mem_zpowers y) hyne
    have hqSupp : q ∈ section14ElementPrimeSupport y := by
      have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
        rw [subgroupPrimeSet]
        rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
          ⟨_hzle, hqcard⟩
        simp [hqcard]
      simpa [section14ElementPrimeSupport] using
        section8_subgroupPrimeSet_mono
          (Subgroup.zpowers_le.2 hz_zpowy) hqz
    rcases support_subset_left_or_right hy hBx_block hπ_block hBx_disj
        (hcover_of_memG hyG) with hyBx | hyπ
    · have hyπc : section14ElementPrimeSupport y ⊆ πᶜ := by
        intro p hpY hpπ
        exact (Set.disjoint_left.mp hBx_disj) (hyBx hpY) hpπ
      have hyZpowX : y ∈ Subgroup.zpowers x :=
        section14_mem_zpowers_left_of_support_subset
          (a := x) (b := x') (y := y)
          hxx'Comm hcopx hxπc hx'π hyG hyπc
      have hqB : q ∈ B := hyB hqSupp
      have hqBx : q ∈ Bx := hyBx hqSupp
      have hEqBBx : B = Bx :=
        section14_sigma_eq_of_common_prime hM.1 hMx.1 hqB hqBx
      have hy'π : section14ElementPrimeSupport y' ⊆ π := by
        intro p hpY'
        rcases hcover_of_memG hy'G hpY' with hpBx | hpπ
        · exact False.elim ((hy'Bc hpY') (hEqBBx ▸ hpBx))
        · exact hpπ
      have hy'ZpowX' : y' ∈ Subgroup.zpowers x' :=
        section14_mem_zpowers_right_of_support_subset
          (a := x) (b := x') (y := y')
          hxx'Comm hcopx hxπc hx'π hy'G hy'π
      have hyEq : y = x :=
        section14_b1_left_eq_of_mul_eq_of_disjoint
          (G := G) hdisjxx'
          hyZpowX hy'ZpowX' (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers x')
          hEq.symm
      left
      refine ⟨hyEq, ?_⟩
      have hcancel := congrArg (fun t : G => x⁻¹ * t) hEq
      simpa [hyEq, mul_assoc] using hcancel.symm
    · have hyZpowX' : y ∈ Subgroup.zpowers x' :=
        section14_mem_zpowers_right_of_support_subset
          (a := x) (b := x') (y := y)
          hxx'Comm hcopx hxπc hx'π hyG hyπ
      have hqB : q ∈ B := hyB hqSupp
      have hqπ : q ∈ π := hyπ hqSupp
      have hEqBπ : B = π :=
        section14_sigma_eq_of_common_prime hM.1 hNx.1 hqB hqπ
      have hy'πc : section14ElementPrimeSupport y' ⊆ πᶜ := by
        simpa [B, hEqBπ] using hy'Bc
      have hy'ZpowX : y' ∈ Subgroup.zpowers x :=
        section14_mem_zpowers_left_of_support_subset
          (a := x) (b := x') (y := y')
          hxx'Comm hcopx hxπc hx'π hy'G hy'πc
      have hEq' : x * x' = y' * y := by
        simpa [hyy'Comm.eq] using hEq
      have hy'Eq : y' = x := by
        symm
        exact section14_b1_left_eq_of_mul_eq_of_disjoint
          (G := G) hdisjxx'
          (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers x')
          hy'ZpowX hyZpowX' hEq'
      have hx'Eqy : x' = y := by
        have hcancel := congrArg (fun t : G => x⁻¹ * t) hEq'
        simpa [mul_assoc, hy'Eq] using hcancel
      right
      exact ⟨hx'Eqy.symm, hy'Eq⟩

public theorem CFSG.section14_exists_sigma_support_witness
    {g : G} (hg : g ≠ 1) :
    ∃ M : Subgroup G, M ∈ section9MaximalSubgroups G ∧
      (section14ElementPrimeSupport g ∩ section10SigmaPrimes M).Nonempty := by
  obtain ⟨q, z, hz_zpowg, _hzG, _hz_ne, hzprime⟩ :=
    section14_exists_primeOrder_zpowers_in (G := G)
      (B := Subgroup.zpowers g) (Subgroup.mem_zpowers g) hg
  let X : Subgroup G := Subgroup.zpowers z
  have hXprime : X ∈ section10PrimeOrderSubgroupsIn q (Subgroup.zpowers g) := by
    simpa [X] using hzprime
  have hXle_zpowg : X ≤ Subgroup.zpowers g := Subgroup.zpowers_le.2 hz_zpowg
  have hXne : X ≠ ⊥ := section12_primeOrder_ne_bot hXprime
  have hXorder : orderOf z = q.val := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn, X] using hXprime) with
      ⟨_hz, hzord⟩
    exact hzord
  have hXcard : Nat.card X = q.val := by
    simp [X, hXorder]
  have hXq : IsPGroup q.val X := by
    exact IsPGroup.of_card (n := 1) (by simp [hXcard])
  have hzpowg_ne_top : Subgroup.zpowers g ≠ ⊤ := by
    intro htop
    let _ : IsCyclic G := (isCyclic_iff_exists_zpowers_eq_top (α := G)).2 ⟨g, htop⟩
    exact IsMinCE.not_solvable (G := G) (inferInstance : Group.IsSolvable G)
  have hXne_top : X ≠ ⊤ := by
    intro hXtop
    have htop_le_zpowg : (⊤ : Subgroup G) ≤ Subgroup.zpowers g := by
      simpa [hXtop] using hXle_zpowg
    exact hzpowg_ne_top (top_le_iff.mp htop_le_zpowg)
  have hNXne_top : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
    intro hNtop
    have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    letI : IsSimpleGroup G := IsMinCE.simple
    rcases hXnormal.eq_bot_or_eq_top with hXbot | hXtop
    · exact hXne hXbot
    · exact hXne_top hXtop
  obtain ⟨M0, hM0⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) (H := Subgroup.normalizer (X : Set G)) hNXne_top
  have hqSupp : q ∈ section14ElementPrimeSupport g := by
    have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
      rw [subgroupPrimeSet]
      simp [hXorder]
    simpa [section14ElementPrimeSupport, X] using
      section8_subgroupPrimeSet_mono hXle_zpowg hqz
  have hXsub_char : (X.subgroupOf (Subgroup.zpowers g)).Characteristic := by
    letI : IsCyclic (Subgroup.zpowers g) := inferInstance
    exact section12_subgroup_characteristic_of_cyclic (X.subgroupOf (Subgroup.zpowers g))
  have hNormZpow_le_NormX :
      Subgroup.normalizer (Subgroup.zpowers g : Set G) ≤
        Subgroup.normalizer (X : Set G) := by
    letI : (X.subgroupOf (Subgroup.zpowers g)).Characteristic := hXsub_char
    simpa [Subgroup.map_subgroupOf_eq_of_le hXle_zpowg] using
      section8_normalizer_map_subtype_le_of_characteristic
        (G := G) (H := Subgroup.zpowers g) (K := X.subgroupOf (Subgroup.zpowers g))
  have hg_normX : g ∈ Subgroup.normalizer (X : Set G) := by
    exact hNormZpow_le_NormX (Subgroup.le_normalizer (Subgroup.mem_zpowers g))
  have hgM0 : g ∈ M0 := hM0.2 hg_normX
  have hXle_M0 : X ≤ M0 := Subgroup.le_normalizer.trans hM0.2
  have hq_alt :
      q ∈ section10SigmaPrimes M0 ∪ section12Tau2Primes M0 :=
    lemma_12_2_a (G := G) (M := M0) (Mstar := M0) (X := X) (p := q)
      hM0.1 hXq hXne hXle_M0 hM0
  rcases hq_alt with hqσ0 | hqτ20
  · exact ⟨M0, hM0.1, ⟨q, hqSupp, hqσ0⟩⟩
  · have hbot_pi : IsPiSubgroup (G := G) (section10SigmaPrimes M0)ᶜ (⊥ : Subgroup G) := by
      intro p hp
      simp [p.2.ne_one] at hp
    obtain ⟨E, hEcomp, _hbotE⟩ :=
      section14_exists_sigma_complement_containing
        (G := G) (M := M0) (K := ⊥) hM0.1 bot_le hbot_pi
    obtain ⟨E₁₂, E₁, E₂, E₃, hE⟩ :=
      section14_exists_EData_of_complement (G := G) (M := M0) (E := E) hM0.1 hEcomp
    obtain ⟨A, hA⟩ :=
      section12_exists_rankTwo_in_E_of_tau2
        (G := G) (M := M0) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM0.1 hE hqτ20
    have hA_M0 : A ∈ section12RankTwoElementaryAbelianIn q M0 :=
      section12_rankTwo_of_EData hE hA
    have hA_le_M0 : A ≤ M0 := section12_rankTwo_le hA_M0
    have hNormA_proper : Subgroup.normalizer (A : Set G) ≠ ⊤ := by
      intro hnorm_top
      have hA_normal : A.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
      letI : IsSimpleGroup G := IsMinCE.simple
      rcases (haveI := hA_normal; IsSimpleGroup.eq_bot_or_eq_top_of_normal A) with hAbot | hAtop
      · exact (section12_rankTwo_ne_bot hA) hAbot
      · have htop_le_M0 : (⊤ : Subgroup G) ≤ M0 := by
          simpa [hAtop] using hA_le_M0
        exact hM0.1.1 (top_le_iff.mp htop_le_M0)
    obtain ⟨M1, hM1⟩ :=
      section9_exists_maximalSubgroupsContaining_of_ne_top
        (G := G) (H := Subgroup.normalizer (A : Set G)) hNormA_proper
    have hqσ1 : q ∈ section10SigmaPrimes M1 :=
      (lemma_12_11_a
        (G := G) (M := M0) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
        (A := A) (Mstar := M1) (p := q)
        hM0.1 hE hqτ20 hA hM1) hqτ20 |>.1
    exact ⟨M1, hM1.1, ⟨q, hqSupp, hqσ1⟩⟩

omit [IsMinCE G] in
private theorem CFSG.section14_exists_block_factor
    {g : G} {B : Set Nat.Primes}
    (hB : B ∈ section14SigmaSupport g) :
    ∃ y y' : G,
      g = y * y' ∧ y ≠ 1 ∧
        y ∈ Subgroup.zpowers g ∧ y' ∈ Subgroup.zpowers g ∧
        section14ElementPrimeSupport y ⊆ B ∧
        section14ElementPrimeSupport y' ⊆ Bᶜ ∧
        Commute y y' := by
  classical
  rcases hB with ⟨hBblock, ⟨q, hqSupp, hqB⟩⟩
  let H : Subgroup G := Subgroup.zpowers g
  have hsolvH : Group.IsSolvable H := by
    let _ : IsCyclic H := inferInstance
    infer_instance
  obtain ⟨K, hK⟩ := section14_exists_hallSubgroupIn (G := G) hsolvH B
  obtain ⟨L, hL⟩ := section14_exists_hallSubgroupIn (G := G) hsolvH Bᶜ
  rcases hK with ⟨hKleH, hKHall⟩
  rcases hL with ⟨hLleH, hLHall⟩
  let Ksub : Subgroup H := K.subgroupOf H
  let Lsub : Subgroup H := L.subgroupOf H
  letI : Ksub.Characteristic := by
    letI : IsCyclic H := inferInstance
    exact section12_subgroup_characteristic_of_cyclic Ksub
  have hcomp : Ksub.IsComplement' Lsub :=
    section11_isComplement_of_isHall_compl hKHall hLHall
  let gH : H := ⟨g, Subgroup.mem_zpowers g⟩
  have hgTop : gH ∈ Ksub ⊔ Lsub := by
    have htop : Ksub ⊔ Lsub = ⊤ := hcomp.sup_eq_top
    simp [htop]
  rcases (Subgroup.mem_sup_of_normal_left (x := gH) (s := Ksub) (t := Lsub)).1 hgTop with
    ⟨yK, hyKsub, yL, hyLsub, hyEq⟩
  let y : G := yK
  let y' : G := yL
  have hyK : y ∈ K := by
    simpa [y, Ksub, Subgroup.mem_subgroupOf] using hyKsub
  have hyL : y' ∈ L := by
    simpa [y', Lsub, Subgroup.mem_subgroupOf] using hyLsub
  have hyH : y ∈ H := hKleH hyK
  have hy'H : y' ∈ H := hLleH hyL
  have hEq : g = y * y' := by
    simpa [y, y'] using (congrArg Subtype.val hyEq).symm
  have hKsupp : subgroupPrimeSet K ⊆ B := by
    intro p hpK
    have hcardK : Nat.card (K.subgroupOf H) = Nat.card K :=
      section12_card_subgroupOf_eq hKleH
    exact hKHall.p_in_pi_of_p_dvd_card p (by simpa [subgroupPrimeSet, hcardK] using hpK)
  have hLsupp : subgroupPrimeSet L ⊆ Bᶜ := by
    intro p hpL
    have hcardL : Nat.card (L.subgroupOf H) = Nat.card L :=
      section12_card_subgroupOf_eq hLleH
    exact hLHall.p_in_pi_of_p_dvd_card p (by simpa [subgroupPrimeSet, hcardL] using hpL)
  have hyB : section14ElementPrimeSupport y ⊆ B := by
    intro p hpY
    exact hKsupp <| section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hyK) hpY
  have hy'Bc : section14ElementPrimeSupport y' ⊆ Bᶜ := by
    intro p hpY'
    exact hLsupp <| section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hyL) hpY'
  have hyne : y ≠ 1 := by
    intro hy1
    have hEq' : g = y' := by simp [hEq, hy1]
    exact (hy'Bc (by simpa [hEq'] using hqSupp)) hqB
  have hycomm : Commute y y' := by
    rcases Subgroup.mem_zpowers_iff.mp hyH with ⟨m, hm⟩
    rcases Subgroup.mem_zpowers_iff.mp hy'H with ⟨n, hn⟩
    simpa [hm, hn] using (((Commute.refl g).zpow_left m).zpow_right n)
  exact ⟨y, y', hEq, hyne, hyH, hy'H, hyB, hy'Bc, hycomm⟩

public theorem CFSG.section14_exists_msigma_factor_of_ne_one
    {g : G} (hg : g ≠ 1) :
    ∃ x x' : G, ∃ M : Subgroup G,
      g = x * x' ∧ section14SigmaLength x = 1 ∧
        section14IsPiElement (section10SigmaPrimes M)ᶜ x' ∧
        Commute x x' ∧ M ∈ section14MsigmaElement x := by
  obtain ⟨M0, hM0, hMeet⟩ := section14_exists_sigma_support_witness (G := G) hg
  let B : Set Nat.Primes := section10SigmaPrimes M0
  have hB : B ∈ section14SigmaSupport g := ⟨⟨M0, hM0, rfl⟩, hMeet⟩
  obtain ⟨x, x', hgxx', hxne, hxZ, hx'Z, hxB, hx'Bc, hcomm⟩ :=
    section14_exists_block_factor (G := G) hB
  let Y : Subgroup G := Subgroup.zpowers x
  have hYσ : IsPiSubgroup (G := G) B Y :=
    section14_isPiSubgroup_zpowers_of_support_subset (G := G) hxB
  have hYne : Y ≠ ⊥ := (Subgroup.zpowers_ne_bot).2 hxne
  have hYne_top : Y ≠ ⊤ := by
    intro hYtop
    let _ : IsCyclic G := (isCyclic_iff_exists_zpowers_eq_top (α := G)).2 ⟨x, hYtop⟩
    exact IsMinCE.not_solvable (G := G) (inferInstance : Group.IsSolvable G)
  obtain ⟨a, hYa⟩ :=
    section14_exists_conjugating_element_of_sigmaSubgroup
      (G := G) (M := M0) (Y := Y) hM0 hYσ hYne hYne_top
  have hax_mem : a * x * a⁻¹ ∈ Y.conjBy a := by
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_zpowers x, by simp [MulAut.conj_apply]⟩
  have haxMσ : a * x * a⁻¹ ∈ section10Msigma M0 := hYa hax_mem
  have hxMσ : x ∈ section10Msigma (M0.conjBy a⁻¹) := by
    simpa [mul_assoc] using
      section14_mem_msigma_conjBy
        (G := G) (M := M0) (x := a * x * a⁻¹) (a := a⁻¹) haxMσ
  have hMx : M0.conjBy a⁻¹ ∈ section14MsigmaElement x := by
    refine ⟨section14_maximal_conjBy (G := G) hM0 a⁻¹, ?_⟩
    simpa using hxMσ
  have hxlen : section14SigmaLength x = 1 :=
    section14_sigmaLength_one_of_mem_msigma (G := G) hMx.1 (hMx.2 (by simp)) hxne
  refine ⟨x, x', M0.conjBy a⁻¹, hgxx', hxlen, ?_, hcomm, hMx⟩
  change section14ElementPrimeSupport x' ⊆
    (section10SigmaPrimes (M0.conjBy a⁻¹))ᶜ
  simpa [B, section14_sigmaPrimes_conjBy (G := G) M0 a⁻¹] using hx'Bc

private theorem CFSG.section14_exists_msigmaElement_of_tau2_centralizer
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {x x' : G}
    (hxMσ : x ∈ section10Msigma M) (hxne : x ≠ 1)
    (hx'cent : x' ∈ elementCentralizerIn M x)
    (hx'ne : x' ≠ 1)
    (hx'τ2 : section14ElementPrimeSupport x' ⊆ section12Tau2Primes M) :
    ∃ Mstar : Subgroup G,
      Mstar ∈ section14MsigmaElement x' ∧ Mstar ≠ M ∧ x ∉ Mstar := by
  let K : Subgroup G := Subgroup.zpowers x'
  have hx'M : x' ∈ M := hx'cent.1
  have hKleM : K ≤ M := Subgroup.zpowers_le.2 hx'M
  have hx'σc : section14ElementPrimeSupport x' ⊆ (section10SigmaPrimes M)ᶜ := by
    intro p hp
    exact (hx'τ2 hp).1
  have hKπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ K := by
    simpa [K] using
      section14_isPiSubgroup_zpowers_of_support_subset
        (G := G) (a := x') hx'σc
  obtain ⟨E, E₁₂, E₁, E₂, E₃, hE, hKE⟩ :=
    section14_exists_EData_containing
      (G := G) (M := M) (K := K) hM hKleM hKπ
  have hx'E : x' ∈ E := hKE (Subgroup.mem_zpowers x')
  obtain ⟨q, z, hz_zpowx', _hzK, _hz_ne, hzprime⟩ :=
    section14_exists_primeOrder_zpowers_in (G := G)
      (B := K) (Subgroup.mem_zpowers x') hx'ne
  let X : Subgroup G := Subgroup.zpowers z
  have hXleK : X ≤ K := Subgroup.zpowers_le.2 hz_zpowx'
  have hXprimeK : X ∈ section10PrimeOrderSubgroupsIn q K := by
    simpa [X] using hzprime
  have hXorder : orderOf z = q.val := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn, X] using hXprimeK) with
      ⟨_hzK, hXorder⟩
    exact hXorder
  have hXcard : Nat.card X = q.val := by
    simp [X, hXorder]
  have hqSupp : q ∈ section14ElementPrimeSupport x' := by
    have hqX : q ∈ subgroupPrimeSet X := by
      rw [subgroupPrimeSet]
      simp [hXcard]
    simpa [section14ElementPrimeSupport, X] using
      section8_subgroupPrimeSet_mono
        (Subgroup.zpowers_le.2 hz_zpowx') hqX
  have hqτ2 : q ∈ section12Tau2Primes M := hx'τ2 hqSupp
  have hXprimeE : X ∈ section10PrimeOrderSubgroupsIn q E := by
    exact ⟨hXleK.trans hKE, hXcard⟩
  obtain ⟨A, hA⟩ :=
    section12_exists_rankTwo_in_E_of_tau2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hqτ2
  have hXprimeA : X ∈ section10PrimeOrderSubgroupsIn q A := by
    have hEq :=
      (corollary_12_6_a
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
        (A := A) (p := q) hM hE hqτ2 hA).2
    simpa [hEq] using hXprimeE
  have hAnormE : section10NormalIn A E :=
    (corollary_12_6_a
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (A := A) (p := q) hM hE hqτ2 hA).1
  have hEleNormA : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAnormE.1).1 hAnormE.2
  have hx'normA : x' ∈ Subgroup.normalizer (A : Set G) := hEleNormA hx'E
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn q M :=
    section12_rankTwo_of_EData hE hA
  have hA_le_M : A ≤ M := section12_rankTwo_le hA_M
  have hNormA_proper : Subgroup.normalizer (A : Set G) ≠ ⊤ := by
    intro hnorm_top
    have hA_normal : A.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
    letI : IsSimpleGroup G := IsMinCE.simple
    rcases (haveI := hA_normal; IsSimpleGroup.eq_bot_or_eq_top_of_normal A) with hAbot | hAtop
    · exact (section12_rankTwo_ne_bot hA) hAbot
    · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        simpa [hAtop] using hA_le_M
      exact hM.1 (top_le_iff.mp htop_le_M)
  obtain ⟨Mstar, hMstar⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) (H := Subgroup.normalizer (A : Set G)) hNormA_proper
  have hMstar_ne_M : Mstar ≠ M := by
    have hnotNormA_le_M :
        ¬ Subgroup.normalizer (A : Set G) ≤ M :=
      (corollary_12_6_b
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
        (A := A) (p := q) hM hE hqτ2 hA).2.2
    intro hEq
    exact hnotNormA_le_M (by simpa [hEq] using hMstar.2)
  have hx'Mstar : x' ∈ Mstar := hMstar.2 hx'normA
  have hA_Mstar : Mstar ∈ section9MaximalSubgroupsContaining A := by
    refine ⟨hMstar.1, ?_⟩
    exact (Subgroup.le_normalizer : A ≤ Subgroup.normalizer (A : Set G)).trans hMstar.2
  have hMsigma_inf : section10Msigma M ⊓ Mstar = ⊥ :=
    theorem_12_5_e (G := G) (M := M) (A := A) (p := q)
      hM hqτ2 hA_M Mstar hA_Mstar hMstar_ne_M
  have hx_not_Mstar : x ∉ Mstar := by
    intro hxMstar
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← hMsigma_inf]
      exact ⟨hxMσ, hxMstar⟩
    exact hxne (Subgroup.mem_bot.mp hxbot)
  have hsupp_sigma_star :
      section14ElementPrimeSupport x' ⊆ section10SigmaPrimes Mstar := by
    intro r hr
    exact
      ((lemma_12_11_a
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
        (A := A) (Mstar := Mstar) (p := q)
        hM hE hqτ2 hA hMstar) (hx'τ2 hr)).1
  have hx'Mstarσ : x' ∈ section10Msigma Mstar :=
    section14_mem_msigma_of_primeSupport_subset
      (G := G) (M := Mstar) hMstar.1 hx'Mstar hsupp_sigma_star
  refine ⟨Mstar, ?_, hMstar_ne_M, hx_not_Mstar⟩
  refine ⟨hMstar.1, ?_⟩
  intro y hy
  rcases Set.mem_singleton_iff.mp hy with rfl
  exact hx'Mstarσ

private theorem CFSG.section14_mem_R_of_tau2_centralizer
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {x x' : G}
    (hxMσ : x ∈ section10Msigma M) (hxne : x ≠ 1)
    (hx'cent : x' ∈ elementCentralizerIn M x)
    (hx'ne : x' ≠ 1)
    (hx'τ2 : section14ElementPrimeSupport x' ⊆ section12Tau2Primes M)
    (hMax :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer ({x'} : Set G)) = {M}) :
    x ∈ section14R x' := by
  classical
  obtain ⟨Mstar, hMstar, _hMstar_ne_M, hx_not_Mstar⟩ :=
    section14_exists_msigmaElement_of_tau2_centralizer
      (G := G) (M := M) hM hxMσ hxne hx'cent hx'ne hx'τ2
  have hx'Mstarσ : x' ∈ section10Msigma Mstar := hMstar.2 (by simp)
  have hMstar_norm :
      Subgroup.normalizer (Mstar : Set G) = Mstar :=
    section14_maximal_normalizer_eq_self_of_msigma_member
      (G := G) hMstar.1 hx'Mstarσ hx'ne
  have hcomm : Commute x x' :=
    (Subgroup.mem_centralizer_singleton_iff.mp hx'cent.2).symm
  have hMstar_conj : Mstar.conjBy x ∈ section14MsigmaElement x' := by
    have hconj :
        Mstar.conjBy x ∈ section14MsigmaElement (x * x' * x⁻¹) :=
      section14_msigmaElement_conjBy (G := G) (x := x') (a := x) hMstar
    simpa [hcomm.eq, mul_assoc] using hconj
  have hMstar_conj_ne : Mstar.conjBy x ≠ Mstar := by
    intro hEq
    have hxnorm : x ∈ Subgroup.normalizer (Mstar : Set G) :=
      section14_mem_normalizer_of_conjBy_eq (G := G) (H := Mstar) hEq
    have hxMstar : x ∈ Mstar := by simpa [hMstar_norm] using hxnorm
    exact hx_not_Mstar hxMstar
  let Ωx' : Type _ := {L : Subgroup G // L ∈ section14MsigmaElement x'}
  let L₁ : Ωx' := ⟨Mstar, hMstar⟩
  let L₂ : Ωx' := ⟨Mstar.conjBy x, hMstar_conj⟩
  have hσx' : (section14MsigmaElement x').Nonempty := ⟨Mstar, hMstar⟩
  have hcardx' :
      1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x'} := by
    have hne : L₁ ≠ L₂ := by
      intro hEq
      exact hMstar_conj_ne (congrArg Subtype.val hEq).symm
    haveI : Nontrivial Ωx' := ⟨L₁, L₂, hne⟩
    change 1 < Nat.card Ωx'
    exact Finite.one_lt_card
  have hNx' :
      section14N x' ∈
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) :=
    section14N_mem_of_nonsingleton (G := G) hx'ne hσx' hcardx'
  obtain ⟨N0, hN0, huniqN0⟩ :=
    theorem_14_4_unique_N (G := G) (x := x') hx'ne hσx' hcardx'
  have hN0_eq_M : N0 = M := by
    have hN0single : N0 ∈ ({M} : Set (Subgroup G)) := by
      simpa [hMax] using hN0
    simpa using hN0single
  have hNx'_eq_M : section14N x' = M := by
    have hNx'_eq : section14N x' = N0 := huniqN0 _ hNx'
    exact hNx'_eq.trans hN0_eq_M
  have hRdef :=
    (theorem_14_4_a (G := G) (x := x') hx'ne hσx' hcardx' hMstar).1
  have hxcent' : x ∈ elementCentralizerIn (section10Msigma M) x' := by
    refine ⟨hxMσ, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  simpa [hRdef, hNx'_eq_M] using hxcent'

private theorem CFSG.section14_alt1_or_alt2_of_msigma_centralizer_factor
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {g x x' : G}
    (hg : g = x * x')
    (hxMσ : x ∈ section10Msigma M) (hxne : x ≠ 1)
    (hx'cent : x' ∈ elementCentralizerIn M x)
    (hx'sigma' : section14IsPiElement (section10SigmaPrimes M)ᶜ x') :
    (∃ a a' : G,
      g = a * a' ∧ section14SigmaLength a = 1 ∧ a' ∈ section14R a) ∨
      (∃ y y' : G, ∃ M0 : Subgroup G,
        g = y * y' ∧ section14SigmaLength y = 1 ∧ y' ≠ 1 ∧
          section14IsPiElement (section14KappaPrimes M0) y' ∧
          y' ∈ elementCentralizerIn M0 y ∧
          M0 ∈ section14MsigmaElement y) := by
  have hxlen : section14SigmaLength x = 1 :=
    section14_sigmaLength_one_of_mem_msigma (G := G) hM hxMσ hxne
  have hMx : M ∈ section14MsigmaElement x := by
    exact ⟨hM, by simpa using hxMσ⟩
  by_cases hx'1 : x' = 1
  · left
    refine ⟨x, 1, ?_, hxlen, ?_⟩
    · simpa [hx'1] using hg
    · exact (section14R x).one_mem
  · have hx'ne : x' ≠ 1 := hx'1
    have hcor :=
      corollary_14_3 (G := G) (M := M) (x := x) (x' := x') hM
        hxMσ hxne hx'ne hx'cent hx'sigma'
    rcases hcor with hκ | hτ2
    · right
      exact ⟨x, x', M, hg, hxlen, hx'ne, hκ.1, hx'cent, hMx⟩
    · left
      have hxR : x ∈ section14R x' :=
        section14_mem_R_of_tau2_centralizer
          (G := G) (M := M) hM hxMσ hxne hx'cent hx'ne hτ2.1 hτ2.2.2
      have hcomm : Commute x x' :=
        (Subgroup.mem_centralizer_singleton_iff.mp hx'cent.2).symm
      refine ⟨x', x, ?_, hτ2.2.1, hxR⟩
      simpa [hcomm.eq, mul_assoc] using hg

/-- Lemma 14.6: every nonidentity element satisfies exactly one of the two
Section 14 alternatives. -/
public theorem CFSG.lemma_14_6
    {g : G} (hg : g ≠ 1) :
    let Alternative1 :=
      ∃ x x' : G,
        g = x * x' ∧ section14SigmaLength x = 1 ∧ x' ∈ section14R x
    let Alternative2 :=
      ∃ y y' : G, ∃ M : Subgroup G,
        g = y * y' ∧ section14SigmaLength y = 1 ∧ y' ≠ 1 ∧
          section14IsPiElement (section14KappaPrimes M) y' ∧
          y' ∈ elementCentralizerIn M y ∧
          M ∈ section14MsigmaElement y
    (Alternative1 ∨ Alternative2) ∧ ¬ (Alternative1 ∧ Alternative2) := by
  dsimp
  refine ⟨?_, ?_⟩
  · by_cases hlen : section14SigmaLength g = 1
    · left
      exact ⟨g, 1, by simp, hlen, (section14R g).one_mem⟩
    · by_contra hNo
      have hAlt1_not :
          ¬ ∃ x x' : G,
            g = x * x' ∧ section14SigmaLength x = 1 ∧ x' ∈ section14R x := by
        intro hAlt1
        exact hNo (Or.inl hAlt1)
      have hAlt2_not :
          ¬ ∃ y y' : G, ∃ M : Subgroup G,
            g = y * y' ∧ section14SigmaLength y = 1 ∧ y' ≠ 1 ∧
              section14IsPiElement (section14KappaPrimes M) y' ∧
              y' ∈ elementCentralizerIn M y ∧
              M ∈ section14MsigmaElement y := by
        intro hAlt2
        exact hNo (Or.inr hAlt2)
      obtain ⟨x, x', M, hgxx', hxlen, hx'sigma', hcomm, hMx⟩ :=
        section14_exists_msigma_factor_of_ne_one (G := G) hg
      have hxMσ : x ∈ section10Msigma M := hMx.2 (by simp)
      have hxne : x ≠ 1 := section14_sigmaLength_one_ne_one hxlen
      have hgcommx : Commute g x := by
        calc
          g * x = (x * x') * x := by rw [hgxx']
          _ = x * (x' * x) := by simp [mul_assoc]
          _ = x * (x * x') := by rw [hcomm.eq]
          _ = x * g := by rw [hgxx']
      by_cases hgM : g ∈ M
      · have hxM : x ∈ M := section14_msigma_le M hxMσ
        have hx'Eq : x' = x⁻¹ * g := by
          have hcancel := congrArg (fun t : G => x⁻¹ * t) hgxx'
          simpa [mul_assoc] using hcancel.symm
        have hx'M : x' ∈ M := by
          rw [hx'Eq]
          exact M.mul_mem (M.inv_mem hxM) hgM
        have hx'cent : x' ∈ elementCentralizerIn M x := by
          refine ⟨hx'M, ?_⟩
          exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
        exact hNo <|
          section14_alt1_or_alt2_of_msigma_centralizer_factor
            (G := G) (M := M) (g := g) (x := x) (x' := x')
            hMx.1 hgxx' hxMσ hxne hx'cent hx'sigma'
      · let Ωx : Type _ := {L : Subgroup G // L ∈ section14MsigmaElement x}
        have hMnorm :
            Subgroup.normalizer (M : Set G) = M :=
          section14_maximal_normalizer_eq_self_of_msigma_member
            (G := G) hMx.1 hxMσ hxne
        have hMconjg : M.conjBy g ∈ section14MsigmaElement x := by
          have hconj :
              M.conjBy g ∈ section14MsigmaElement (g * x * g⁻¹) :=
            section14_msigmaElement_conjBy
              (G := G) (M := M) (x := x) (a := g) hMx
          have hgxg : g * x * g⁻¹ = x := by
            have hEq := congrArg (fun t : G => t * g⁻¹) hgcommx.eq
            simpa [mul_assoc] using hEq
          simpa [hgxg] using hconj
        have hMconjg_ne : M.conjBy g ≠ M := by
          intro hEq
          have hg_norm : g ∈ Subgroup.normalizer (M : Set G) :=
            section14_mem_normalizer_of_conjBy_eq (G := G) (H := M) hEq
          have hgM' : g ∈ M := by simpa [hMnorm] using hg_norm
          exact hgM hgM'
        have hσx : (section14MsigmaElement x).Nonempty := ⟨M, hMx⟩
        have hcardx :
            1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x} := by
          let L₁ : Ωx := ⟨M, hMx⟩
          let L₂ : Ωx := ⟨M.conjBy g, hMconjg⟩
          have hne : L₁ ≠ L₂ := by
            intro hEq
            exact hMconjg_ne (congrArg Subtype.val hEq).symm
          haveI : Nontrivial Ωx := ⟨L₁, L₂, hne⟩
          change 1 < Nat.card Ωx
          exact Finite.one_lt_card
        let N : Subgroup G := section14N x
        have hNx :
            N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
          simpa [N] using
            section14N_mem_of_nonsingleton (G := G) (x := x) hxne hσx hcardx
        have hgcent : g ∈ Subgroup.centralizer ({x} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr hgcommx
        have hgN : g ∈ N := hNx.2 hgcent
        have hNoSigmaNFactor :
            section10SigmaPrimes N ∉ section14SigmaSupport g := by
          intro hBN
          obtain ⟨y, y', hgy, hyne, hyZ, hy'Z, hyσN, hy'sigmaN', hycomm⟩ :=
            section14_exists_block_factor (G := G) hBN
          have hyN : y ∈ N := (Subgroup.zpowers_le.2 hgN) hyZ
          have hy'N : y' ∈ N := (Subgroup.zpowers_le.2 hgN) hy'Z
          have hyMσ : y ∈ section10Msigma N :=
            section14_mem_msigma_of_primeSupport_subset
              (G := G) (M := N) hNx.1 hyN hyσN
          have hylen : section14SigmaLength y = 1 :=
            section14_sigmaLength_one_of_mem_msigma
              (G := G) hNx.1 hyMσ hyne
          have hy'cent : y' ∈ elementCentralizerIn N y := by
            refine ⟨hy'N, ?_⟩
            exact Subgroup.mem_centralizer_singleton_iff.mpr hycomm.symm
          exact hNo <|
            section14_alt1_or_alt2_of_msigma_centralizer_factor
              (G := G) (M := N) (g := g) (x := y) (x' := y')
              hNx.1 hgy hyMσ hyne hy'cent hy'sigmaN'
        have hgsigmaN' : section14IsPiElement (section10SigmaPrimes N)ᶜ g := by
          intro p hpSupp hpσN
          exact hNoSigmaNFactor ⟨⟨N, hNx.1, rfl⟩, ⟨p, hpSupp, hpσN⟩⟩
        let Cx : Subgroup G := Subgroup.centralizer ({x} : Set G)
        let R : Subgroup G := section14R x
        let Cmx : Subgroup G := elementCentralizerIn (M ⊓ N) x
        have hCxleN : Cx ≤ N := by
          simpa [Cx, N] using hNx.2
        have hCxne_top : Cx ≠ ⊤ := by
          intro htop
          exact hNx.1.1 (top_le_iff.mp (by simpa [Cx, htop] using hCxleN))
        have hCxsolv : IsSolvable Cx :=
          IsMinCE.proper_subgroups_solvable Cx (lt_top_iff_ne_top.mpr hCxne_top)
        have hRdefx : R = elementCentralizerIn (section10Msigma N) x := by
          simpa [R, N] using
            (theorem_14_4_a (G := G) (x := x) hxne hσx hcardx hMx).1
        have hCx_prod :
            ((Cx : Subgroup G) : Set G) = (Cmx : Set G) * (R : Set G) := by
          simpa [Cx, Cmx, N, R] using
            theorem_14_4_b (G := G) (x := x) hxne hσx hcardx hMx
        have hcompN :
            section12ComplementIn N (section10Msigma N) (M ⊓ N) := by
          simpa [N] using
            theorem_14_4_e (G := G) (x := x) hxne hσx hcardx hMx
        have hCmx_le_Cx : Cmx ≤ Cx := by
          intro y hy
          exact hy.2
        have hRle_Cx : R ≤ Cx := by
          rw [hRdefx]
          intro y hy
          exact hy.2
        have hRle_sigmaN : R ≤ section10Msigma N := by
          rw [hRdefx]
          intro y hy
          exact hy.1
        have hCmx_le_MN : Cmx ≤ M ⊓ N := by
          intro y hy
          exact hy.1
        have hCmx_inf_R : Cmx ⊓ R = ⊥ := by
          apply bot_unique
          intro y hy
          exact Subgroup.disjoint_def.mp hcompN.2.2.2
            (hRle_sigmaN hy.2) (hCmx_le_MN hy.1)
        have hCmxComp :
            (Cmx.subgroupOf Cx).IsComplement' (R.subgroupOf Cx) := by
          refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
          · rw [Subgroup.disjoint_def]
            intro z hzC hzR
            apply Subtype.ext
            have hzbot : ((z : Cx) : G) ∈ (⊥ : Subgroup G) := by
              have hzinf : ((z : Cx) : G) ∈ Cmx ⊓ R := by
                exact ⟨by simpa [Cmx, Subgroup.mem_subgroupOf] using hzC,
                  by simpa [R, Subgroup.mem_subgroupOf] using hzR⟩
              simpa [hCmx_inf_R] using hzinf
            simpa using hzbot
          · rw [Set.eq_univ_iff_forall]
            intro z
            have hzprod : (z : G) ∈ (Cmx : Set G) * (R : Set G) := by
              rw [← hCx_prod]
              exact z.property
            rcases hzprod with ⟨u, huC, r, hrR, hur⟩
            refine ⟨⟨u, hCmx_le_Cx huC⟩, ?_, ⟨r, hRle_Cx hrR⟩, ?_, ?_⟩
            · simpa [Cmx, Subgroup.mem_subgroupOf] using huC
            · simpa [R, Subgroup.mem_subgroupOf] using hrR
            · apply Subtype.ext
              exact hur
        have hRsub_sigma :
            subgroupPrimeSet (R.subgroupOf Cx) ⊆ section10SigmaPrimes N := by
          intro p hpRsub
          have hpR : p ∈ subgroupPrimeSet R := by
            have hcardR : Nat.card (R.subgroupOf Cx) = Nat.card R :=
              section12_card_subgroupOf_eq hRle_Cx
            simpa [subgroupPrimeSet, hcardR] using hpRsub
          exact
            ((theorem_10_2_b (G := G) hNx.1).1).p_in_pi_of_p_dvd_card p <|
              section8_subgroupPrimeSet_mono hRle_sigmaN hpR
        have hCmxHall :
            IsHallSubgroup (section10SigmaPrimes N)ᶜ (Cmx.subgroupOf Cx) := by
          refine isHallSubgroup_of (G := Cx) (π := (section10SigmaPrimes N)ᶜ)
            (H := Cmx.subgroupOf Cx) ?_ ?_
          · intro p hpCsub
            have hpC : p ∈ subgroupPrimeSet Cmx := by
              have hcardC : Nat.card (Cmx.subgroupOf Cx) = Nat.card Cmx :=
                section12_card_subgroupOf_eq hCmx_le_Cx
              simpa [subgroupPrimeSet, hcardC] using hpCsub
            rw [Set.mem_compl_iff]
            intro hpσN
            obtain ⟨X, hX⟩ :=
              section14_exists_primeOrderSubgroupIn_of_dvd_card
                (G := G) (A := Cmx) (p := p) hpC
            rcases hX with ⟨hXC, hXcard⟩
            have hXp : IsPGroup p.val X := by
              exact IsPGroup.of_card (n := 1) (by simp [hXcard])
            have hXN : X ≤ N := by
              intro y hy
              exact (hCmx_le_MN (hXC hy)).2
            let Xsub : Subgroup N := X.subgroupOf N
            have hXsub_p : IsPGroup p.val Xsub := by
              simpa [Xsub] using
                hXp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := N) hXN).symm
            have hXsub_le_sigma :
                Xsub ≤ section10MsigmaSubgroup N :=
              section12_pSubgroup_le_normal_hall_of_prime_mem
                (R := N) (π := section10SigmaPrimes N)
                (H := section10MsigmaSubgroup N) (A := Xsub)
                ((theorem_10_2_b (G := G) hNx.1).2) hpσN hXsub_p
            have hXle_sigma : X ≤ section10Msigma N := by
              intro y hy
              have hy_sub : (⟨y, hXN hy⟩ : N) ∈ Xsub := by
                simpa [Xsub, Subgroup.mem_subgroupOf] using hy
              have hy_sigma : (⟨y, hXN hy⟩ : N) ∈ section10MsigmaSubgroup N :=
                hXsub_le_sigma hy_sub
              exact Subgroup.mem_map.mpr ⟨⟨y, hXN hy⟩, hy_sigma, rfl⟩
            have hXne : X ≠ ⊥ := section12_primeOrder_ne_bot ⟨hXC, hXcard⟩
            have hXbot : X ≤ ⊥ := by
              intro y hy
              exact Subgroup.disjoint_def.mp hcompN.2.2.2 (hXle_sigma hy)
                (hXC.trans hCmx_le_MN hy)
            exact hXne (bot_unique hXbot)
          · intro p hpσNc hpidx
            have hpRsub : p ∈ subgroupPrimeSet (R.subgroupOf Cx) := by
              rw [subgroupPrimeSet]
              simpa [hCmxComp.symm.index_eq_card] using hpidx
            exact hpσNc (hRsub_sigma hpRsub)
        have hYle_Cx : Subgroup.zpowers g ≤ Cx := by
          intro y hy
          rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hgcommx.zpow_left n)
        let Ysub : Subgroup Cx := (Subgroup.zpowers g).subgroupOf Cx
        have hYsub_sigma_compl :
            IsPiSubgroup (G := Cx) (section10SigmaPrimes N)ᶜ Ysub := by
          intro p hpYsub
          have hpY : p ∈ subgroupPrimeSet (Subgroup.zpowers g) := by
            have hcardY : Nat.card Ysub = Nat.card (Subgroup.zpowers g) :=
              section12_card_subgroupOf_eq hYle_Cx
            simpa [Ysub, subgroupPrimeSet, hcardY] using hpYsub
          exact hgsigmaN' hpY
        letI : MulDistribMulAction Unit Cx := {
          smul := fun _ y => y
          one_smul := fun _ => rfl
          mul_smul := fun _ _ _ => rfl
          smul_mul := fun _ _ _ => rfl
          smul_one := fun _ => rfl }
        have hYsub_inv : IsInvariant Unit Cx Ysub := by
          refine ⟨?_⟩
          intro _ y
          simp [Ysub]
        have hcopCx : Nat.Coprime (Nat.card Unit) (Nat.card Cx) := by simp
        obtain ⟨Lsub, hLHall, _hLInv, hYsubL⟩ :=
          exists_isHallSubgroup_isInvariant_of_isPiSubgroup
            (G := Cx) (A := Unit) hCxsolv hcopCx
            (section10SigmaPrimes N)ᶜ Ysub hYsub_sigma_compl hYsub_inv
        obtain ⟨a, ha⟩ :=
          exists_conj_eq_of_isHallSubgroup_of_solvable
            (G := Cx) hCxsolv hLHall hCmxHall
        have hYsub_conj_le :
            Ysub.map (MulAut.conj a).toMonoidHom ≤ Cmx.subgroupOf Cx := by
          have htmp :
              Ysub.map (MulAut.conj a).toMonoidHom ≤
                Lsub.map (MulAut.conj a).toMonoidHom :=
            Subgroup.map_mono hYsubL
          simpa [ha] using htmp
        have hYconj_le_Cmx :
            (Subgroup.zpowers g).conjBy (a : G) ≤ Cmx := by
          simpa [Ysub] using
            section14_conjBy_le_of_subgroupOf_conjBy_le
              (G := G) (H := Subgroup.zpowers g) (K := Cmx) (M := Cx)
              (g := (a : G)) a.property hYle_Cx hYsub_conj_le
        have hgaCmx : (a : G) * g * (a : G)⁻¹ ∈ Cmx := by
          apply hYconj_le_Cmx
          exact Subgroup.mem_map.mpr ⟨g, Subgroup.mem_zpowers g, by
            simp [MulAut.conj_apply, mul_assoc]⟩
        have haxcomm : Commute (a : G) x :=
          Subgroup.mem_centralizer_singleton_iff.mp a.property
        have hax : (a : G)⁻¹ * x * (a : G) = x := by
          have hEq := congrArg (fun t : G => (a : G)⁻¹ * t) haxcomm.eq
          simpa [mul_assoc] using hEq.symm
        have hMag : M.conjBy (a : G)⁻¹ ∈ section14MsigmaElement x := by
          have hconj :=
            section14_msigmaElement_conjBy
              (G := G) (M := M) (x := x) (a := (a : G)⁻¹) hMx
          simpa [inv_inv, hax] using hconj
        have hgaM : g ∈ M.conjBy (a : G)⁻¹ := by
          refine Subgroup.mem_map.mpr ⟨(a : G) * g * (a : G)⁻¹, hgaCmx.1.1, ?_⟩
          simp [mul_assoc]
        have hxMagσ : x ∈ section10Msigma (M.conjBy (a : G)⁻¹) :=
          hMag.2 (by simp)
        have hxMag : x ∈ M.conjBy (a : G)⁻¹ :=
          section14_msigma_le (M.conjBy (a : G)⁻¹) hxMagσ
        have hx'Eq : x' = x⁻¹ * g := by
          have hcancel := congrArg (fun t : G => x⁻¹ * t) hgxx'
          simpa [mul_assoc] using hcancel.symm
        have hx'Mag : x' ∈ M.conjBy (a : G)⁻¹ := by
          rw [hx'Eq]
          exact (M.conjBy (a : G)⁻¹).mul_mem
            ((M.conjBy (a : G)⁻¹).inv_mem hxMag) hgaM
        have hx'sigma'ag :
            section14IsPiElement (section10SigmaPrimes (M.conjBy (a : G)⁻¹))ᶜ x' := by
          simpa [section14_sigmaPrimes_conjBy (G := G) M (a : G)⁻¹] using hx'sigma'
        have hx'centag : x' ∈ elementCentralizerIn (M.conjBy (a : G)⁻¹) x := by
          refine ⟨hx'Mag, ?_⟩
          exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
        exact hNo <|
          section14_alt1_or_alt2_of_msigma_centralizer_factor
            (G := G) (M := M.conjBy (a : G)⁻¹) (g := g) (x := x) (x' := x')
            hMag.1 hgxx' hxMagσ hxne hx'centag hx'sigma'ag
  · intro hBoth
    rcases hBoth with ⟨hAlt1, hAlt2⟩
    rcases hAlt1 with ⟨x, x', hgx, hxlen, hx'R⟩
    rcases hAlt2 with ⟨y, y', M, hgy, hylen, hy'ne, hy'κ, hy'cent, hMy⟩
    have hy'sigma' : section14IsPiElement (section10SigmaPrimes M)ᶜ y' := by
      intro p hp
      exact section14_kappa_subset_not_sigma (M := M) (hy'κ hp)
    have hPair :
        (y = x ∧ y' = x') ∨ (y = x' ∧ y' = x) :=
      section14_eq_left_or_right_of_alt1_alt2_product
        (G := G) hxlen hx'R hylen hy'ne hy'sigma' hy'cent hMy (hgx.symm.trans hgy)
    have hyMσ : y ∈ section10Msigma M := hMy.2 (by simp)
    have hyne : y ≠ 1 := section14_sigmaLength_one_ne_one hylen
    have hcor :=
      corollary_14_3 (G := G) (M := M) (x := y) (x' := y') hMy.1
        hyMσ hyne hy'ne hy'cent hy'sigma'
    have hcentyM : Subgroup.centralizer ({y} : Set G) ≤ M := by
      rcases hcor with hκ | hτ2
      · exact hκ.2
      · exfalso
        obtain ⟨q, z, hz_zpowy, _hzY, _hz_ne, hzprime⟩ :=
          section14_exists_primeOrder_zpowers_in (G := G)
            (B := Subgroup.zpowers y') (Subgroup.mem_zpowers y') hy'ne
        have hqSupp : q ∈ section14ElementPrimeSupport y' := by
          have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
            rw [subgroupPrimeSet]
            rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
              ⟨_hzle, hqcard⟩
            simp [hqcard]
          simpa [section14ElementPrimeSupport] using
            section8_subgroupPrimeSet_mono
              (Subgroup.zpowers_le.2 hz_zpowy) hqz
        have hqκ : q ∈ section14KappaPrimes M := hy'κ hqSupp
        have hqτ13 : q ∈ section12Tau1Primes M ∪ section12Tau3Primes M :=
          section14_kappa_subset_tau13 hqκ
        exact hqτ13.elim
          (fun hqτ1 => by
            have h1 : primeRank q.val M = 1 := hqτ1.2.2
            have h2 : primeRank q.val M = 2 := (hτ2.1 hqSupp).2
            omega)
          (fun hqτ3 => by
            have h1 : primeRank q.val M = 1 := hqτ3.2.2
            have h2 : primeRank q.val M = 2 := (hτ2.1 hqSupp).2
            omega)
    have hyMax :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)) :=
      ⟨hMy.1, hcentyM⟩
    rcases hPair with ⟨rfl, hy'Eq⟩ | ⟨hyEq, hy'Eq⟩
    · have hx'ne : x' ≠ 1 := by
        simpa [hy'Eq] using hy'ne
      obtain ⟨_hy, hσy, hcardy⟩ := section14_nonsingleton_of_mem_R_ne_one hx'R hx'ne
      have hNy :
          section14N y ∈ section9MaximalSubgroupsContaining
            (Subgroup.centralizer ({y} : Set G)) :=
        section14N_mem_of_nonsingleton (G := G) hyne hσy hcardy
      obtain ⟨N0, hN0, huniqN0⟩ :=
        theorem_14_4_unique_N (G := G) (x := y) hyne hσy hcardy
      have hN_eq : section14N y = N0 := huniqN0 _ hNy
      have hM_eq : M = N0 := huniqN0 _ hyMax
      have hMN : M = section14N y := hM_eq.trans hN_eq.symm
      have hyτ2 :
          section14ElementPrimeSupport y ⊆ section12Tau2Primes (section14N y) :=
        (theorem_14_4_c (G := G) (x := y) hyne hσy hcardy
          (Classical.choose_spec hσy)).1
      have hyτ2M : section14ElementPrimeSupport y ⊆ section12Tau2Primes M := by
        simpa [hMN] using hyτ2
      have hyσM : section14ElementPrimeSupport y ⊆ section10SigmaPrimes M :=
        section14_primeSupport_subset_sigma_of_msigmaMember hMy
      obtain ⟨q, z, hz_zpowy, _hzY, _hz_ne, hzprime⟩ :=
        section14_exists_primeOrder_zpowers_in (G := G)
          (B := Subgroup.zpowers y) (Subgroup.mem_zpowers y) hyne
      have hqSupp : q ∈ section14ElementPrimeSupport y := by
        have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
          rw [subgroupPrimeSet]
          rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
            ⟨_hzle, hqcard⟩
          simp [hqcard]
        simpa [section14ElementPrimeSupport] using
            section8_subgroupPrimeSet_mono
              (Subgroup.zpowers_le.2 hz_zpowy) hqz
      exact (hyτ2M hqSupp).1 (hyσM hqSupp)
    · have hxne : x ≠ 1 := section14_sigmaLength_one_ne_one hxlen
      have hx'ne : x' ≠ 1 := by
        simpa [hyEq] using section14_sigmaLength_one_ne_one hylen
      obtain ⟨_hx, hσx, hcardx⟩ := section14_nonsingleton_of_mem_R_ne_one hx'R hx'ne
      have hNx :
          section14N x ∈ section9MaximalSubgroupsContaining
            (Subgroup.centralizer ({x} : Set G)) :=
        section14N_mem_of_nonsingleton (G := G) hxne hσx hcardx
      have hxτ2 :
          section14ElementPrimeSupport x ⊆ section12Tau2Primes (section14N x) :=
        (theorem_14_4_c (G := G) (x := x) hxne hσx hcardx
          (Classical.choose_spec hσx)).1
      obtain ⟨q, z, hz_zpowx, _hzX, _hz_ne, hzprime⟩ :=
        section14_exists_primeOrder_zpowers_in (G := G)
          (B := Subgroup.zpowers x) (Subgroup.mem_zpowers x) hxne
      have hqSupp : q ∈ section14ElementPrimeSupport x := by
        have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
          rw [subgroupPrimeSet]
          rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
            ⟨_hzle, hqcard⟩
          simp [hqcard]
        simpa [section14ElementPrimeSupport] using
          section8_subgroupPrimeSet_mono
            (Subgroup.zpowers_le.2 hz_zpowx) hqz
      have hqκ : q ∈ section14KappaPrimes M := by
        have hqSupp' : q ∈ section14ElementPrimeSupport y' := by
          simpa [hy'Eq] using hqSupp
        exact hy'κ hqSupp'
      have hqrankM : primeRank q.val M = 1 := by
        exact section12_tau13_primeRank_eq_one (section14_kappa_subset_tau13 hqκ)
      have hMx' : M ∈ section14MsigmaElement x' := by
        simpa [hyEq] using hMy
      obtain ⟨q', z', hz'_zpowy, _hz'X, _hz'_ne, hz'prime⟩ :=
        section14_exists_primeOrder_zpowers_in (G := G)
          (B := Subgroup.zpowers x') (Subgroup.mem_zpowers x') hx'ne
      have hq'Supp : q' ∈ section14ElementPrimeSupport x' := by
        have hq'z : q' ∈ subgroupPrimeSet (Subgroup.zpowers z') := by
          rw [subgroupPrimeSet]
          rcases (by simpa [section10PrimeOrderSubgroupsIn] using hz'prime) with
            ⟨_hzle, hq'card⟩
          simp [hq'card]
        simpa [section14ElementPrimeSupport] using
          section8_subgroupPrimeSet_mono
            (Subgroup.zpowers_le.2 hz'_zpowy) hq'z
      have hq'M : q' ∈ section10SigmaPrimes M :=
        section14_primeSupport_subset_sigma_of_msigmaMember hMx' hq'Supp
      have hq'N : q' ∈ section10SigmaPrimes (section14N x) :=
        section14_primeSupport_subset_sigmaN_of_mem_R hx'R hq'Supp
      have hconjNxM : section14ConjugateSubgroups (section14N x) M := by
        by_cases hconj : section14ConjugateSubgroups (section14N x) M
        · exact hconj
        · have hnot : section12NotConjugate (section14N x) M := by
            intro a hNa
            exact hconj ⟨a⁻¹, by
              simpa [section11_conjBy_inv] using congrArg (fun K => K.conjBy a⁻¹) hNa⟩
          have hdisj : Disjoint (section10SigmaPrimes M) (section10SigmaPrimes (section14N x)) :=
            theorem_13_9 (G := G) hMx'.1 hNx.1 hnot
          exact False.elim ((Set.disjoint_left.mp hdisj) hq'M hq'N)
      have hqrankN : primeRank q.val (section14N x) = 1 := by
        rcases hconjNxM with ⟨a, hNa⟩
        let e : M ≃* section14N x := by
          exact hNa.symm ▸ (MulAut.conj a).subgroupMap M
        have hle₁ :
            primeRank q.val (section14N x) ≤ primeRank q.val M :=
          section14_primeRank_le_of_equiv q.val e
        have hle₂ :
            primeRank q.val M ≤ primeRank q.val (section14N x) :=
          section14_primeRank_le_of_equiv q.val e.symm
        exact (le_antisymm hle₁ hle₂).trans hqrankM
      have hqτ2 : q ∈ section12Tau2Primes (section14N x) := hxτ2 hqSupp
      have hqrankN2 : primeRank q.val (section14N x) = 2 := hqτ2.2
      omega

end Section14
