module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLOfGood
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLDescent
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHolds
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Comm
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverLift

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.StandardType.E6ThreeModel
open scoped commutatorElement

variable {R : Type} [Group R]

theorem exists_model_commutators_of_good_odd (hAL : GGAbelianLift) (D : FrameData R) (hD : D.Good)
    (hcov : CoverOdd R) (I : Set (MulAut R)) (hI : (D.H : Set (MulAut R)) = I)
    (hrow : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Odd (Nat.card ψ.ker) →
      ∀ w : Fin 6 → L', (∀ i, ψ (w i) = D.nb i) →
        ∃ t : Fin 6 → L', (∀ i, ψ (t i) ∈ D.V0) ∧
          ψ.ker ≤ Subgroup.closure (Set.range fun i => ⁅w i, t i⁆)) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ A : Subgroup (MulAut L'), CFSG.Open.IsElemAbelian 3 A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
        3 ^ 5 ≤ Nat.card A → GGTorusSelfCent 3 A →
        ∃ (Φ : A →* Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup L') (w t : Fin 6 → L'),
          GGE6ThreeWeylModelWith ψ.ker A Φ T w ∧
            (∀ i, t i ^ 3 = 1) ∧
            (∀ i, ∀ a ∈ A, a (t i) = t i) ∧
            ∀ z ∈ ψ.ker, (∃ k : ℕ, z ^ 3 ^ k = 1) →
              z ∈ Subgroup.closure (Set.range fun i => ⁅w i, t i⁆) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h5 hsc
  classical
  have : Finite R := Finite.of_surjective ψ hψ
  have hZ : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hD.center
  let ρ : MulAut L' →* MulAut R := BstarDesc.descAut hψ hZ
  have hρ : ∀ a l, ρ a (ψ l) = ψ (a l) := fun a l => BstarDesc.descAut_apply hψ hZ a l
  have hρinj : Function.Injective ρ := BstarDesc.descAut_injective hψ hZ hperf
  have hAH : ∀ a ∈ A, ρ a ∈ D.H := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hρφ : ρ a = φ := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hρ, hφ]
    have hφH : φ ∈ (D.H : Set (MulAut R)) := by rw [hI]; exact hφI
    rw [hρφ]
    exact hφH
  obtain ⟨γ, -, hγ⟩ := exists_align D hD.shape hρinj hA h5 hAH
  let ψ' : L' →* R := γ.toMonoidHom.comp ψ
  have hψ' : Function.Surjective ψ' := γ.surjective.comp hψ
  have hkerEq : ψ'.ker = ψ.ker := by
    ext l
    simp [ψ', MonoidHom.mem_ker]
  have hker' : ψ'.ker ≤ Subgroup.center L' := hkerEq ▸ hker
  have hZ' : ψ'.ker = Subgroup.center L' := hkerEq ▸ hZ
  let ρ' : MulAut L' →* MulAut R := BstarDesc.descAut hψ' hZ'
  have hρ' : ∀ a l, ρ' a (ψ' l) = ψ' (a l) := fun a l => BstarDesc.descAut_apply hψ' hZ' a l
  have hρ'inj : Function.Injective ρ' := BstarDesc.descAut_injective hψ' hZ' hperf
  have hρ'eq : ∀ a, ρ' a = γ * ρ a * γ⁻¹ := by
    intro a
    refine MulEquiv.ext fun r => ?_
    obtain ⟨l, rfl⟩ := hψ' r
    rw [hρ']
    simp only [ψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.mul_apply,
      MulAut.inv_apply_self, hρ]
  have hal : ∀ a ∈ A, ρ' a ∈ D.diag.range := fun a ha => by
    rw [hρ'eq]
    exact hγ a ha
  have hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ'.ker hker') := fun a ha =>
    U63TB.mem_presZ_of_ker hker' fun z hz =>
      U63TB.preserves_ker (I := Set.univ) ⟨ρ' a, Set.mem_univ _, fun l => hρ' a l⟩ hz
  have hψb : Function.Surjective (U63TB.psi1 hker') := U63TB.psi1_surjective hker' hψ'
  have hkerb := U63TB.psi1_ker_central hker'
  have hperfb := U63TB.commutator_quot hker' hperf
  have hodd := U63TB.odd_card_ker_psi1 hker'
  have hcardb : Nat.card (U63TB.psi1 hker').ker = 1 ∨ Nat.card (U63TB.psi1 hker').ker = 3 := by
    obtain ⟨k, hk⟩ := hcov _ (U63TB.psi1 hker') hψb hkerb hperfb
    have h3 : Nat.card (U63TB.psi1 hker').ker ∣ 3 :=
      (Nat.Coprime.pow_right k hodd.coprime_two_right).dvd_of_dvd_mul_left hk
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    exacts [Or.inl h, Or.inr h]
  have hZb := BstarDesc.ker_eq_center hψb hkerb hD.center
  let ρb := BstarDesc.descAut hψb hZb
  have hρb : ∀ a l, ρb a (U63TB.psi1 hker' l) = U63TB.psi1 hker' (a l) := fun a l =>
    BstarDesc.descAut_apply hψb hZb a l
  have hρbinj := BstarDesc.descAut_injective hψb hZb hperfb
  have hAb := U63TB.isElemAbelian_range_redSub hker' hAle hA
  have hscb := U63TB.selfCent_quot hker' hA hAle hsc
  have halb : ∀ ab ∈ (U63TB.redSub hker' hAle).range, ρb ab ∈ D.diag.range := by
    rintro _ ⟨a, rfl⟩
    have hab : ρb (U63TB.redSub hker' hAle a) = ρ' a.1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨lb, rfl⟩ := hψb r
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective lb
      rw [hρb, U63TB.psi1_mk, U63TB.redSub_mk, U63TB.psi1_mk, hρ']
    rw [hab, hρ'eq]
    exact hγ a.1 a.2
  obtain ⟨Φb, wb, hmodelb, hwb, -⟩ :=
    zl_model_odd D hAL hD hψb hkerb hcardb hρb hρbinj hAb hscb halb
  have hTbodd : ∀ t ∈ D.Tor.comap (U63TB.psi1 hker'), Odd (orderOf t) := by
    intro t ht
    have hψt : U63TB.psi1 hker' t ∈ D.Tor := ht
    have hm : Odd (orderOf (U63TB.psi1 hker' t)) := hD.torus.2.1 (U63TB.psi1 hker' t) hψt
    have hmem : t ^ orderOf (U63TB.psi1 hker' t) ∈ (U63TB.psi1 hker').ker := by
      rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
    have h1 : (⟨t ^ orderOf (U63TB.psi1 hker' t), hmem⟩ : (U63TB.psi1 hker').ker) ^
        Nat.card (U63TB.psi1 hker').ker = 1 := pow_card_eq_one'
    have h2 : t ^ (orderOf (U63TB.psi1 hker' t) * Nat.card (U63TB.psi1 hker').ker) = 1 := by
      have := congrArg Subtype.val h1
      simpa [pow_mul] using this
    exact (hm.mul hodd).of_dvd_nat (orderOf_dvd_of_pow_eq_one h2)
  obtain ⟨T, w, hbody, hwlift⟩ := zl_model_descent hker' hZ' hperf hA hAle hmodelb hTbodd
  obtain ⟨tb, htb, hsub⟩ := hrow (L' ⧸ U63TB.twoSub ψ'.ker hker') (U63TB.psi1 hker')
    hψb hkerb hperfb hodd wb hwb
  have htbT : ∀ i, tb i ∈ D.Tor.comap (U63TB.psi1 hker') := fun i =>
    ((FrameData.mem_V0 D).1 (htb i)).1
  have hAbp : IsPGroup 3 (U63TB.redSub hker' hAle).range := fun g =>
    ⟨1, Subtype.ext (by simpa using hAb.2 g.1 g.2)⟩
  have htbcube : ∀ i, tb i ^ 3 = 1 := fun i =>
    (abelianLift_apply D hAL hD hψb hkerb hcardb hρb hAbp halb hwb).2.2 (tb i) (htb i)
  obtain ⟨-, -, -, -, hfixb, -⟩ := hmodelb
  let Z2 : Subgroup L' := U63TB.twoSub ψ'.ker hker'
  have hZ2c : Z2 ≤ Subgroup.center L' := U63TB.twoSub_le_center hker'
  have hZ2p : IsPGroup 2 Z2 := U63TB.isPGroup_twoSub hker'
  have hKc : (QuotientGroup.mk' Z2).ker ≤ Subgroup.center L' := by
    rw [QuotientGroup.ker_mk']
    exact hZ2c
  have hK2 : IsPGroup 2 (QuotientGroup.mk' Z2).ker := by
    rw [QuotientGroup.ker_mk']
    exact hZ2p
  choose t0 ht0 using fun i => QuotientGroup.mk_surjective (tb i)
  choose t ht using fun i =>
    CFSG.LocalAnalysis.ComponentInitial.exists_lift_pow_three_eq_one
      (η := QuotientGroup.mk' Z2) hKc hK2 (y := t0 i) (by
        rw [QuotientGroup.mk'_apply, ht0 i]
        exact htbcube i)
  have htmap : ∀ i, (QuotientGroup.mk' Z2) (t i) = (QuotientGroup.mk' Z2) (t0 i) :=
    fun i => (ht i).1
  have ht3 : ∀ i, t i ^ 3 = 1 := fun i => (ht i).2
  have htmap' : ∀ i, ((t i : L') : L' ⧸ Z2) = ((t0 i : L') : L' ⧸ Z2) :=
    fun i => by simpa only [QuotientGroup.mk'_apply] using htmap i
  have htπ : ∀ i, ((t i : L') : L' ⧸ Z2) = tb i :=
    fun i => (htmap' i).trans (ht0 i)
  have htfix : ∀ i, ∀ a ∈ A, a (t i) = t i := by
    intro i a ha
    have h3a : (a (t i)) ^ 3 = 1 := by rw [← map_pow, ht3 i, map_one]
    have hmap : (QuotientGroup.mk' Z2) (a (t i)) = (QuotientGroup.mk' Z2) (t i) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        ← U63TB.redSub_mk hker' hAle ⟨a, ha⟩ (t i), htπ i]
      exact hfixb _ ⟨⟨a, ha⟩, rfl⟩ _ (htbT i)
    exact CFSG.LocalAnalysis.ComponentInitial.eq_of_pow_three_eq_one_of_map_eq
      hKc hK2 h3a (ht3 i) hmap
  let S : Subgroup L' := Subgroup.closure (Set.range fun i => ⁅w i, t i⁆)
  have hmapS : Subgroup.closure (Set.range fun i => ⁅wb i, tb i⁆) =
      S.map (QuotientGroup.mk' Z2) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨⁅w i, t i⁆, ⟨i, rfl⟩, ?_⟩
      rw [map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        hwlift i, htπ i]
    · rintro ⟨y, ⟨i, rfl⟩, hy⟩
      refine ⟨i, ?_⟩
      rw [map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        hwlift i, htπ i] at hy
      exact hy
  have hclose : ∀ z ∈ ψ.ker, (∃ k : ℕ, z ^ 3 ^ k = 1) → z ∈ S := by
    intro z hz hz3pow
    have hz' : z ∈ ψ'.ker := by rwa [hkerEq]
    have hzq : (z : L' ⧸ Z2) ∈ (U63TB.psi1 hker').ker :=
      (U63TB.mem_ker_psi1 hker').mpr hz'
    have hzSmap : (z : L' ⧸ Z2) ∈ S.map (QuotientGroup.mk' Z2) := by
      rw [← hmapS]
      exact hsub hzq
    obtain ⟨s, hs, hsq⟩ := hzSmap
    have hsq' : (s : L' ⧸ Z2) = (z : L' ⧸ Z2) := by
      rwa [QuotientGroup.mk'_apply] at hsq
    have hsz : s⁻¹ * z ∈ Z2 := QuotientGroup.eq.mp hsq'
    have hnM : (s⁻¹ * z) ^ (2 ^ Nat.card L') = 1 := ((U63TB.mem_twoSub hker').mp hsz).2
    have hncenter : s⁻¹ * z ∈ Subgroup.center L' := U63TB.twoSub_le_center hker' hsz
    have hcomm : Commute s (s⁻¹ * z) := Subgroup.mem_center_iff.mp hncenter s
    have hzM : z ^ (2 ^ Nat.card L') = s ^ (2 ^ Nat.card L') := by
      rw [show z = s * (s⁻¹ * z) by group, hcomm.mul_pow, hnM, mul_one]
    obtain ⟨k, hk⟩ := hz3pow
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hz1 : z = 1 := by simpa using hk
      rw [hz1]
      exact S.one_mem
    · have hgt : 1 < 3 ^ k := Nat.one_lt_pow (Nat.ne_of_gt hkpos) (by norm_num)
      have hcop : Nat.Coprime (2 ^ Nat.card L') (3 ^ k) :=
        (Nat.Coprime.pow_left (Nat.card L') (by norm_num : Nat.Coprime 2 3)).pow_right k
      obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hgt
      have hzpow : z ^ (2 ^ Nat.card L' * u) = z := by
        rw [pow_eq_pow_mod _ hk, hu, pow_one]
      have hz_eq : z = (z ^ (2 ^ Nat.card L')) ^ u := by
        rw [← pow_mul]
        exact hzpow.symm
      have hzS : z ∈ S := by
        rw [hz_eq, hzM]
        exact S.pow_mem (S.pow_mem hs (2 ^ Nat.card L')) u
      exact hzS
  refine ⟨Φb.comp (U63TB.redSub hker' hAle).rangeRestrict, T, w, t, ?_, ht3, htfix, hclose⟩
  exact (congrArg (fun Z => GGE6ThreeWeylModelWith Z A
    (Φb.comp (U63TB.redSub hker' hAle).rangeRestrict) T w) hkerEq) ▸ hbody

theorem zlProp_of_good_odd (hAL : GGAbelianLift) (D : FrameData R) (hD : D.Good)
    (hcov : CoverOdd R) (I : Set (MulAut R)) (hI : (D.H : Set (MulAut R)) = I)
    (hrow : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Odd (Nat.card ψ.ker) →
      ∀ w : Fin 6 → L', (∀ i, ψ (w i) = D.nb i) →
        ∃ t : Fin 6 → L', (∀ i, ψ (t i) ∈ D.V0) ∧
          ψ.ker ≤ Subgroup.closure (Set.range fun i => ⁅w i, t i⁆)) :
    GGE6DepZLProp R I := by
  intro L' _ _ ψ A hTB _
  obtain ⟨hψ, hker, hperf, hA, hAI, h5, -, hsc⟩ := hTB
  obtain ⟨Φ, T, w, t, hmodel, ht3, htfix, hclose⟩ :=
    exists_model_commutators_of_good_odd hAL D hD hcov I hI hrow
      L' ψ hψ hker hperf A hA hAI h5 hsc
  refine ⟨Φ, T, w, hmodel, ?_⟩
  intro z hz hz3
  have hz3' : z ^ 3 = 1 := by simpa [hz3] using pow_orderOf_eq_one z
  have hzS : z ∈ Subgroup.closure (Set.range fun i => ⁅w i, t i⁆) :=
    hclose z hz ⟨1, by simpa using hz3'⟩
  have hle : Subgroup.closure (Set.range fun i => ⁅w i, t i⁆) ≤ ggE6WeylCobdry A w := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact commutator_mem_cobdry i (hsc (t i) (fun a ha => htfix i a ha) (ht3 i))
  exact hle hzS

theorem coverCommSCr_of_good_odd (hAL : GGAbelianLift) (D : FrameData R) (hD : D.Good)
    (hcov : CoverOdd R) (I : Set (MulAut R)) (hI : (D.H : Set (MulAut R)) = I)
    (hrow : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Odd (Nat.card ψ.ker) →
      ∀ w : Fin 6 → L', (∀ i, ψ (w i) = D.nb i) →
        ∃ t : Fin 6 → L', (∀ i, ψ (t i) ∈ D.V0) ∧
          ψ.ker ≤ Subgroup.closure (Set.range fun i => ⁅w i, t i⁆)) :
    GGE6ThreeCoverCommSCr R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h5 hsc z hz hz3pow
  obtain ⟨Φ, T, w, t, hmodel, ht3, htfix, hclose⟩ :=
    exists_model_commutators_of_good_odd hAL D hD hcov I hI hrow
      L' ψ hψ hker hperf A hA hAI h5 hsc
  obtain ⟨-, -, -, -, -, -, -, hact, -⟩ := hmodel
  have hle : Subgroup.closure (Set.range fun i => ⁅w i, t i⁆) ≤
      Subgroup.closure {x : L' | ∃ m t : L',
        (∀ a ∈ A, MulAut.conj m * a * (MulAut.conj m)⁻¹ ∈ A) ∧
        (∀ a ∈ A, a t = t) ∧ t ^ 3 = 1 ∧ x = m * t * m⁻¹ * t⁻¹} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine Subgroup.subset_closure ⟨w i, t i, ?_, htfix i, ht3 i, ?_⟩
    · intro a ha
      obtain ⟨b, hb, -⟩ := hact i ⟨a, ha⟩
      rw [hb]
      exact b.2
    · exact commutatorElement_def _ _
  exact hle (hclose z hz hz3pow)

end CFSG.StandardType.E6Dep.ZL

end
