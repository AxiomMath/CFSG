module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Inner
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45SzFix
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open scoped IsMulCommutative
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem pow_val_add_zmod {H : Type*} [Group H] {p : ℕ} [NeZero p] {g : H}
    (hg : orderOf g = p) (x y : ZMod p) :
    g ^ (x + y).val = g ^ x.val * g ^ y.val := by
  have key := pow_mod_orderOf g (x.val + y.val)
  rw [hg] at key
  rw [ZMod.val_add, key, pow_add]

theorem zpowers_sq_eq {H : Type*} [Group H] {x : H} (hodd : Odd (orderOf x)) :
    Subgroup.zpowers (x ^ 2) = Subgroup.zpowers x := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.zpowers_le]
    simpa using Subgroup.zpow_mem_zpowers x (2 : ℤ)
  rw [Subgroup.zpowers_le]
  exact mem_zpowers_pow_iff.mpr (Nat.coprime_iff_gcd_eq_one.mp (Nat.coprime_two_left.mpr hodd))

theorem exists_elemAbelian_card_pow_of_independent {B : Type*} [CommGroup B] [Finite B]
    {q : ℕ} [Fact q.Prime] {ι : Type*} [Fintype ι] (y : ι → B)
    (hy : ∀ i, orderOf (y i) = q)
    (hind : ∀ n : ι → ℤ, (∏ i, y i ^ n i) = 1 → ∀ i, (q : ℤ) ∣ n i) :
    ∃ E : Subgroup B, IsElemAbelian q E ∧ Nat.card E = q ^ Fintype.card ι := by
  classical
  let Φ : Multiplicative (ι → ZMod q) →* B :=
    { toFun := fun v => ∏ i, y i ^ ((Multiplicative.toAdd v) i).val
      map_one' := by
        refine Finset.prod_eq_one fun i _ => ?_
        simp
      map_mul' := by
        intro v w
        simp only [toAdd_mul, Pi.add_apply]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        exact pow_val_add_zmod (hy i) _ _ }
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hprod : (∏ i, y i ^ (((Multiplicative.toAdd v) i).val : ℤ)) = 1 := by
      rw [← hv]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact zpow_natCast (y i) _
    have hdvd : ∀ i, (q : ℤ) ∣ (((Multiplicative.toAdd v) i).val : ℤ) :=
      hind (fun i => (((Multiplicative.toAdd v) i).val : ℤ)) hprod
    have hzero : ∀ i, (Multiplicative.toAdd v) i = 0 := by
      intro i
      have hq : q ∣ ((Multiplicative.toAdd v) i).val :=
        Int.natCast_dvd_natCast.mp (hdvd i)
      exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt hq (ZMod.val_lt _))
    rw [← toAdd_eq_zero]
    exact funext hzero
  have htop : IsElemAbelian q (⊤ : Subgroup (Multiplicative (ι → ZMod q))) := by
    refine ⟨inferInstance, fun x _ => ?_⟩
    rw [← toAdd_eq_zero, toAdd_pow]
    funext i
    simp [nsmul_eq_mul]
  have hEea : IsElemAbelian q Φ.range := by
    refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm (a : B) b)⟩⟩, fun x hx => ?_⟩
    obtain ⟨v, rfl⟩ := hx
    have hvq : v ^ q = 1 := by
      rw [← toAdd_eq_zero, toAdd_pow]
      funext i
      simp [nsmul_eq_mul]
    calc Φ v ^ q = Φ (v ^ q) := (map_pow Φ v q).symm
      _ = Φ 1 := by rw [hvq]
      _ = 1 := map_one Φ
  refine ⟨Φ.range, hEea, ?_⟩
  have hbij : Function.Bijective Φ.rangeRestrict :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), Φ.rangeRestrict_surjective⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ.rangeRestrict hbij)]
  change Nat.card (ι → ZMod q) = q ^ Fintype.card ι
  rw [Nat.card_pi]
  simp [Nat.card_zmod]

theorem pRank_four_of_three_components_and_central {H : Type*} [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) {K : Fin 3 → Subgroup H} (hK : ∀ i, IsComponent (K i))
    (hinj : Function.Injective K) {y : Fin 3 → H} (hy : ∀ i, y i ∈ K i)
    (hyo : ∀ i, orderOf (y i) = p)
    (hyZ : ∀ i, y i ∉ Subgroup.centralizer ((K i : Set H)))
    {z : H} (hz : z ∈ Subgroup.center H) (hzo : orderOf z = p) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup H) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcommK : ∀ i j, i ≠ j → K i ≤ Subgroup.centralizer (K j : Set H) := by
    intro i j hij
    rcases LocalCores.distinct_components_commute (hK i) (hK j) with h | h
    · exact absurd (hinj h) hij
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by simpa [Subgroup.commutator_comm] using h)
  have hcommY : ∀ i j, i ≠ j → Commute (y i) (y j) := by
    intro i j hij
    exact (Subgroup.mem_centralizer_iff.mp (hcommK i j hij (hy i)) (y j) (hy j)).symm
  have hzy : ∀ i, Commute z (y i) := by
    intro i
    exact (Subgroup.mem_center_iff.mp hz (y i)).symm
  let Y : Option (Fin 3) → H := fun o => o.elim z y
  have hYsome : ∀ i, Y (some i) = y i := fun i => rfl
  have hYnone : Y none = z := rfl
  have hpair : (Set.range Y).Pairwise Commute := by
    rintro _ ⟨o₁, rfl⟩ _ ⟨o₂, rfl⟩ hne
    rcases o₁ with - | i <;> rcases o₂ with - | j
    · exact absurd rfl hne
    · rw [hYnone, hYsome]; exact hzy j
    · rw [hYsome, hYnone]; exact (hzy i).symm
    · rw [hYsome, hYsome]
      exact hcommY i j (fun h => hne (by rw [h]))
  let B : Subgroup H := Subgroup.closure (Set.range Y)
  have hBcomm : IsMulCommutative B := Subgroup.isMulCommutative_closure hpair
  let g : Option (Fin 3) → B := fun o => ⟨Y o, Subgroup.subset_closure ⟨o, rfl⟩⟩
  have hgval : ∀ o, (g o : H) = Y o := fun o => rfl
  have hgord : ∀ o, orderOf (g o) = p := by
    intro o
    rw [Subgroup.orderOf_mk]
    rcases o with - | i
    · change orderOf (Y none) = p
      rw [hYnone]; exact hzo
    · change orderOf (Y (some i)) = p
      rw [hYsome]; exact hyo i
  have hind : ∀ n : Option (Fin 3) → ℤ, (∏ o, g o ^ n o) = 1 → ∀ o, (p : ℤ) ∣ n o := by
    intro n hn
    have hzC : ∀ i, z ∈ Subgroup.centralizer ((K i : Set H)) := by
      intro i
      rw [Subgroup.mem_centralizer_iff]
      intro k _
      exact Subgroup.mem_center_iff.mp hz k
    have hsome : ∀ i : Fin 3, (p : ℤ) ∣ n (some i) := by
      intro i
      have hsplit : g (some i) ^ n (some i) *
          (∏ o ∈ Finset.univ.erase (some i), g o ^ n o) = 1 := by
        rw [Finset.mul_prod_erase Finset.univ (fun o => g o ^ n o) (Finset.mem_univ (some i))]
        exact hn
      have hrest : (∏ o ∈ Finset.univ.erase (some i), g o ^ n o) ∈
          (Subgroup.centralizer ((K i : Set H))).comap B.subtype := by
        refine Subgroup.prod_mem _ fun o ho => ?_
        rw [Finset.mem_erase] at ho
        rw [Subgroup.mem_comap]
        rcases o with - | j
        · simpa [g, Y] using
            (Subgroup.centralizer ((K i : Set H))).zpow_mem (hzC i) (n none)
        · have hji : j ≠ i := fun h => ho.1 (by rw [h])
          simpa [g, Y] using
            (Subgroup.centralizer ((K i : Set H))).zpow_mem (hcommK j i hji (hy j)) (n (some j))
      have hgi : g (some i) ^ n (some i) ∈
          (Subgroup.centralizer ((K i : Set H))).comap B.subtype := by
        have h := inv_mem hrest
        rwa [← eq_inv_of_mul_eq_one_left hsplit] at h
      have hH : y i ^ n (some i) ∈ Subgroup.centralizer ((K i : Set H)) := by
        have h := Subgroup.mem_comap.mp hgi
        simpa [hgval, hYsome] using h
      set k : ℕ := (n (some i) % (p : ℤ)).toNat with hk
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hppos : (0 : ℤ) < p := by exact_mod_cast hp.pos
      have hkval : (k : ℤ) = n (some i) % (p : ℤ) := by
        rw [hk]
        exact Int.toNat_of_nonneg (Int.emod_nonneg _ hpz)
      have hpow : y i ^ n (some i) = y i ^ k := by
        have h1 : y i ^ (n (some i) % (orderOf (y i) : ℤ)) = y i ^ n (some i) :=
          zpow_mod_orderOf _ _
        rw [hyo i] at h1
        rw [← h1, ← zpow_natCast (y i) k, hkval]
      by_contra hmod
      have hkne : k ≠ 0 := by
        intro h0
        apply hmod
        have hnn := Int.emod_nonneg (n (some i)) hpz
        rw [hk] at h0
        omega
      have hklt : k < p := by
        rw [hk]
        have hnn := Int.emod_nonneg (n (some i)) hpz
        have hlt := Int.emod_lt_of_pos (n (some i)) hppos
        omega
      have hcent_k : y i ^ k ∈ Subgroup.centralizer ((K i : Set H)) := by
        rwa [← hpow]
      have hnotdvd : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hkne) hklt
      have hgcd : k.gcd (orderOf (y i)) = 1 := by
        rw [hyo i]
        exact Nat.coprime_iff_gcd_eq_one.mp
          (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hnotdvd))
      have hyin : y i ∈ Subgroup.zpowers (y i ^ k) := mem_zpowers_pow_iff.mpr hgcd
      exact hyZ i (Subgroup.zpowers_le.mpr hcent_k hyin)
    intro o
    rcases o with - | i
    · have hfac : ∀ o ∈ Finset.univ.erase (none : Option (Fin 3)), g o ^ n o = 1 := by
        intro o ho
        rw [Finset.mem_erase] at ho
        rcases o with - | j
        · exact absurd rfl ho.1
        · have hdvd := hsome j
          rw [← orderOf_dvd_iff_zpow_eq_one, hgord (some j)]
          exact hdvd
      have hsplit : g none ^ n none * (∏ o ∈ Finset.univ.erase (none : Option (Fin 3)),
          g o ^ n o) = 1 := by
        rw [Finset.mul_prod_erase Finset.univ (fun o => g o ^ n o) (Finset.mem_univ none)]
        exact hn
      rw [Finset.prod_eq_one hfac, mul_one] at hsplit
      have hsplitH : z ^ n none = 1 := by
        have h := congrArg (fun x : B => (x : H)) hsplit
        simpa [g, Y] using h
      have hdvd : (orderOf z : ℤ) ∣ n none :=
        (orderOf_dvd_iff_zpow_eq_one (x := z) (i := n none)).mpr hsplitH
      rw [hzo] at hdvd
      exact hdvd
    · exact hsome i
  obtain ⟨E, hEea, hEcard⟩ := exists_elemAbelian_card_pow_of_independent (B := B) g hgord hind
  have hcardmap : Nat.card (E.map B.subtype) = p ^ Fintype.card (Option (Fin 3)) := by
    rw [Subgroup.card_map_of_injective B.subtype_injective, hEcard]
  have hEeaH : IsElemAbelian p (E.map B.subtype) := hEea.map B.subtype
  have hk : Nat.card (E.map B.subtype) = p ^ 4 := by
    rw [hcardmap, Fintype.card_option, Fintype.card_fin]
  exact CFSG.SectionRank.le_pRank (p := p) (G := H) (H := (⊤ : Subgroup H))
    (E := E.map B.subtype) hp.one_lt le_top hEeaH hk

theorem pElement_normalizes_thetaComponent_of_pRank_three {H : Type*} [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {z : H} (hz : z ∈ Subgroup.center H) (hzo : orderOf z = p)
    {L : Subgroup H} (hL : L ∈ CFSG.RankThree.thetaComponents p H) (hpL : p ∣ Nat.card L)
    {x : H} (hx : ∃ k : ℕ, orderOf x = p ^ k)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ 3) :
    x ∈ Subgroup.normalizer (L : Set H) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup H := CFSG.RankThree.LocalRank.aschbacherSolvableCore p H with hN
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  have hNcop : ¬ p ∣ Nat.card N :=
    (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := H)
      hp).2.2.1
  have hpLstar : p ∣ Nat.card (L.map π) := by
    obtain ⟨η, -⟩ := CFSG.RankThree.exists_thetaQuotient_mulEquiv_map (H := H) hp hL.2.1
    have hθcop : ¬ p ∣ Nat.card
        (CFSG.RankThree.LocalRank.aschbacherSolvableCore p L) :=
      (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := L)
        hp).2.2.1
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.RankThree.LocalRank.aschbacherSolvableCore p L)
    have hpdvd : p ∣ Nat.card
        (L ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore p L) := by
      rw [hcard] at hpL
      exact (hp.dvd_mul.mp hpL).resolve_right hθcop
    rw [← Nat.card_congr η.toEquiv]
    exact hpdvd
  have hLstar : CFSG.IsComponent (L.map π) :=
    CFSG.RankThree.isComponent_map_of_mem_thetaComponents hp hL
  have hzN : z ∉ N := by
    intro hzmem
    apply hNcop
    have hdvd : p ∣ Nat.card N := by
      have h := orderOf_dvd_natCard (⟨z, hzmem⟩ : N)
      rwa [Subgroup.orderOf_mk, hzo] at h
    exact hdvd
  have hzbar_center : π z ∈ Subgroup.center (H ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N y
    have h := Subgroup.mem_center_iff.mp hz w
    show QuotientGroup.mk' N w * QuotientGroup.mk' N z =
      QuotientGroup.mk' N z * QuotientGroup.mk' N w
    rw [← map_mul, ← map_mul, h]
  have hzbar_ord : orderOf (π z) = p := by
    have hdvd : orderOf (π z) ∣ p := by
      have h := orderOf_map_dvd π z
      rwa [hzo] at h
    have hne : π z ≠ 1 := fun h1 => hzN ((QuotientGroup.eq_one_iff _).mp h1)
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  obtain ⟨k, hk⟩ := hx
  have hxbar_ord : ∃ j : ℕ, orderOf (π x) = p ^ j := by
    have hdvd : orderOf (π x) ∣ p ^ k := by
      rw [← hk]; exact orderOf_map_dvd π x
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    exact ⟨j, hj⟩
  by_contra hxnorm
  have hxbar_move : π x ∉
      Subgroup.normalizer ((L.map π : Subgroup (H ⧸ N)) : Set (H ⧸ N)) := by
    intro hmem
    apply hxnorm
    have hτ : ∀ h : H, (MulAut.conj (π x)) (π h) = π ((MulAut.conj x) h) := by
      intro h
      simp [MulAut.conj_apply, map_mul]
    have hequi := (CFSG.RankThree.theta_component_quotient_correspondence_equivariant
      (H := H) hp).2 (MulAut.conj x) (MulAut.conj (π x)) hτ
    obtain ⟨hLσ, himg⟩ := hequi.1 L hL
    have hfix : (L.map π).map (MulAut.conj (π x)).toMonoidHom = L.map π :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hmem
    have heq : (L.map (MulAut.conj x).toMonoidHom).map π = L.map π := by
      rw [himg, hfix]
    obtain ⟨hbij, -, -⟩ := CFSG.RankThree.theta_component_quotient_correspondence
      (H := H) hp
    have hLeq : L.map (MulAut.conj x).toMonoidHom = L := hbij.injOn hLσ hL heq
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hLeq
  let K : Fin 3 → Subgroup (H ⧸ N) := fun i =>
    (L.map π).map (MulAut.conj ((π x) ^ (i : ℕ))).toMonoidHom
  have hK : ∀ i, CFSG.IsComponent (K i) := fun i =>
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj ((π x) ^ (i : ℕ))) hLstar
  have hK0 : K 0 = L.map π := by
    change (L.map π).map (MulAut.conj ((π x) ^ ((0 : Fin 3) : ℕ))).toMonoidHom = L.map π
    rw [Fin.val_zero, pow_zero, map_one]
    ext y
    simp [MulAut.one_apply]
  have hK1 : K 1 = (L.map π).map (MulAut.conj (π x)).toMonoidHom := by simp [K]
  have hK2 : K 2 = (L.map π).map (MulAut.conj ((π x) ^ 2)).toMonoidHom := by simp [K]
  have h01 : K 0 ≠ K 1 := by
    intro h
    apply hxbar_move
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hK0, hK1] at h
    exact h.symm
  have h02 : K 0 ≠ K 2 := by
    intro h
    apply hxbar_move
    have hfix : (π x) ^ 2 ∈
        Subgroup.normalizer ((L.map π : Subgroup (H ⧸ N)) : Set (H ⧸ N)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      rw [hK0, hK2] at h
      exact h.symm
    obtain ⟨j, hj⟩ := hxbar_ord
    have hodd : Odd (orderOf (π x)) := by
      rw [hj]; exact (hp.odd_of_ne_two hp2).pow
    have hle : Subgroup.zpowers ((π x) ^ 2) ≤
        Subgroup.normalizer ((L.map π : Subgroup (H ⧸ N)) : Set (H ⧸ N)) :=
      Subgroup.zpowers_le.mpr hfix
    rw [zpowers_sq_eq hodd] at hle
    exact hle (Subgroup.mem_zpowers (π x))
  have h12 : K 1 ≠ K 2 := by
    intro h
    have hcompl : ((MulAut.conj ((π x)⁻¹)) * (MulAut.conj ((π x) ^ 2)) :
        MulAut (H ⧸ N)) = MulAut.conj (π x) := by
      rw [← map_mul]
      congr 1
      group
    have hcomp1 : ((MulAut.conj ((π x)⁻¹)).toMonoidHom).comp
        (MulAut.conj ((π x) ^ 2)).toMonoidHom = (MulAut.conj (π x)).toMonoidHom := by
      ext y
      show (π x)⁻¹ * ((π x) ^ 2 * y * ((π x) ^ 2)⁻¹) * ((π x)⁻¹)⁻¹ =
        π x * y * (π x)⁻¹
      group
    have hcomp2 : ((MulAut.conj ((π x)⁻¹)).toMonoidHom).comp
        (MulAut.conj (π x)).toMonoidHom = MonoidHom.id (H ⧸ N) := by
      ext y
      show (π x)⁻¹ * (π x * y * (π x)⁻¹) * ((π x)⁻¹)⁻¹ = y
      group
    have hmap := congrArg
      (fun S : Subgroup (H ⧸ N) => S.map (MulAut.conj ((π x)⁻¹)).toMonoidHom) h
    rw [hK1, hK2] at hmap
    simp only [Subgroup.map_map] at hmap
    rw [← MonoidHom.comp_assoc, ← MonoidHom.comp_assoc] at hmap
    rw [hcomp2, hcomp1, MonoidHom.id_comp] at hmap
    rw [← Subgroup.map_map] at hmap
    apply h01
    rw [hK0, hK1]
    exact hmap
  have hinjK : Function.Injective K := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij h01
    · exact absurd hij h02
    · exact absurd hij.symm h01
    · rfl
    · exact absurd hij h12
    · exact absurd hij.symm h02
    · exact absurd hij.symm h12
    · rfl
  have hKcard : ∀ i, Nat.card (K i) = Nat.card (L.map π) := fun i =>
    Subgroup.card_map_of_injective (MulAut.conj ((π x) ^ (i : ℕ))).injective
  choose t ht_ord ht_cent using fun i =>
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      ((CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥(K i))).mp (hK i).1) hp hp2
      (by rw [hKcard i]; exact hpLstar)
  have hT_mem : ∀ i, (t i : H ⧸ N) ∈ K i := fun i => (t i).2
  have hT_ord : ∀ i, orderOf ((t i : H ⧸ N)) = p := by
    intro i
    rw [Subgroup.orderOf_coe]
    exact ht_ord i
  have hT_cent : ∀ i, (t i : H ⧸ N) ∉
      Subgroup.centralizer ((K i : Set (H ⧸ N))) := by
    intro i hc
    apply ht_cent i
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc (u : H ⧸ N) u.2
  have h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ N)) :=
    pRank_four_of_three_components_and_central hp hK hinjK hT_mem hT_ord hT_cent
      hzbar_center hzbar_ord
  have hrankQ : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ N)) ≤ 3 := by
    rw [CFSG.SectionRank.pRank_quotient_eq N hNcop]
    exact hrank
  omega

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
