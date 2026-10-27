module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Dihedral
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs2
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Action
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Mbar

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L1547

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits DihedralGroup

variable {G : Type*} [Group G]

theorem commutator_le_left {V X : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G)) :
    ⁅V, X⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv x hx
  rw [commutatorElement_def]
  have : v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
  rw [this]
  exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hXV hx) v⁻¹).mp (V.inv_mem hv))

theorem le_centralizer_of_isElemAbelian {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    V ≤ Subgroup.centralizer (V : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have := hV.1
  exact setLike_mul_comm hw hv

variable [Finite G]

theorem conjPerm_injective {M X Q : Subgroup G} (hX : IsA4 X Q) (hXM : X ≤ M)
    (hΩ : ∀ m ∈ M, ∀ P ∈ syl3 X, cjSub m P ∈ syl3 X)
    (hCM : M ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    Function.Injective (conjPerm M (syl3 X) hΩ) := by
  rw [injective_iff_map_eq_one]
  intro m hm
  set K : Subgroup G := (conjPerm M (syl3 X) hΩ).ker.map M.subtype with hK
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    refine mem_normalizer_of_conj_mem ?_
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    exact (conjPerm M (syl3 X) hΩ).normal_ker.conj_mem k hk _
  have hKP : ∀ k ∈ K, ∀ P ∈ syl3 X, k ∈ Subgroup.normalizer (P : Set G) := by
    rintro _ ⟨k, hk, rfl⟩ P hP
    refine mem_normalizer_of_cjSub_eq ?_
    have := congrArg (fun π : Equiv.Perm (syl3 X) => ((π ⟨P, hP⟩ : syl3 X) : Subgroup G))
      (MonoidHom.mem_ker.mp hk)
    simpa [conjPerm_apply] using this
  have hc := commute_of_forall_mem_normalizer hX hXM hMK hKP
  have hmC : (m : G) ∈ M ⊓ Subgroup.centralizer (X : Set G) :=
    ⟨m.2, Subgroup.mem_centralizer_iff.mpr fun x hx => (hc m ⟨m, hm, rfl⟩ x hx).symm⟩
  rw [hCM, Subgroup.mem_bot] at hmC
  exact Subtype.ext hmC

theorem isLThreeTwoOrASix_of_card_four (hI41 : InputI41Two) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hEven : quasithinEvenCharacteristic G)
    (S : Sylow 2 G) {M : Subgroup G} (hSM : (S : Subgroup G) ≤ M) (hF : CharTwo M)
    (hZ2 : Nat.card (quasithinOmegaOneCenter (S : Subgroup G)) = 2)
    (hV4 : Nat.card (VZ (S : Subgroup G) M) = 4)
    (hJ : ¬ thompsonJ (S : Subgroup G) ≤ Subgroup.centralizer (VZ (S : Subgroup G) M : Set G))
    {X : Subgroup G} (hX : IsA4 X (pCoreOf 2 X)) (hXM : X ≤ M)
    (hXs : (X.subgroupOf M).IsSubnormal)
    (hXV : ¬ X ≤ Subgroup.centralizer (VZ (S : Subgroup G) M : Set G)) : IsLThreeTwoOrASix G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := VZ (S : Subgroup G) M with hVdef
  set Z : Subgroup G := quasithinOmegaOneCenter (S : Subgroup G) with hZdef
  have hred : IsTwoReducedIn M V := isTwoReducedIn_conjClosure M S hSM hF le_rfl
  have hVM : V ≤ M := hred.1
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVab : IsElemAbelian 2 V := hred.2.2.1
  have hVS : V ≤ (S : Subgroup G) :=
    (le_pCoreOf_of_isTwoReducedIn hred).trans (pCoreOf_two_le_sylow M S hSM)
  have hV2 : IsPGroup 2 V := S.isPGroup'.to_le hVS
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := le_centralizer_of_isElemAbelian hVab
  have hcomm := commutator_eq_of_isSubnormal hX rfl hXM hXs hVM hMV hV2 hXV
  have hQV : pCoreOf 2 X ≤ V := hcomm ▸ commutator_le_left (hXM.trans hMV)
  have hQeq : pCoreOf 2 X = V := Subgroup.eq_of_le_of_card_ge hQV (by rw [hV4, hX.card_Q])
  obtain ⟨z, hzZ, hz1, hz2, hZ⟩ := exists_eq_of_card_eq_two hZ2
  have hzV : z ∈ V := le_conjClosure Z M hzZ
  have hZC : Z ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
    ((Subgroup.closure_le _).mpr fun x hx => hx.1 :
      Z ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G)).trans inf_le_right
  have hzS : z ∈ (S : Subgroup G) := hVS hzV
  have hzc : ∀ t ∈ (S : Subgroup G), t * z = z * t := fun t ht =>
    Subgroup.mem_centralizer_iff.mp (hZC hzZ) t ht
  obtain ⟨R, -, hRM, hMR, hR3, hRC, hRsub⟩ := exists_rhat hVM hMV hVC hF
  have hXR : X ≤ R := hRsub X hXM hXs fun x hx => ⟨1, by rw [pow_one, ← hQeq]; exact hX.cube x hx⟩
  have hR12 : Nat.card R ≤ 12 := by
    have h3 := relIndex_le_three_of_card_eq_four hV4 (hRM.trans hMV) fun r hr => by
      obtain ⟨k, hk⟩ := hR3 r hr
      exact ⟨k, hVC hk⟩
    have hmul := Subgroup.relIndex_mul_card (R ⊓ Subgroup.centralizer (V : Set G)) R
    rw [inf_eq_left.mpr (inf_le_left : R ⊓ Subgroup.centralizer (V : Set G) ≤ R)] at hmul
    have h4 : Nat.card ↥(R ⊓ Subgroup.centralizer (V : Set G)) ≤ 4 :=
      hV4 ▸ Subgroup.card_le_of_le hRC
    rw [← hmul]
    calc (R ⊓ Subgroup.centralizer (V : Set G)).relIndex R *
          Nat.card ↥(R ⊓ Subgroup.centralizer (V : Set G)) ≤ 3 * 4 := Nat.mul_le_mul h3 h4
      _ = 12 := by norm_num
  have hXeq : X = R := Subgroup.eq_of_le_of_card_ge hXR (by rw [hX.card]; exact hR12)
  have hMX : M ≤ Subgroup.normalizer (X : Set G) := hXeq ▸ hMR
  have hzX : z ∉ Subgroup.centralizer (X : Set G) := by
    intro hzC
    obtain ⟨p, hpX, hp⟩ := hX.exists_orderOf_eq_three
    exact hz1 (hX.fpf p hpX hp z (hQeq ▸ hzV) (Subgroup.mem_centralizer_iff.mp hzC p hpX))
  have hT1 := eq_one_of_mem_centralizer S (hSM.trans hMX) hZ hzX
  have hCM := inf_centralizer_eq_bot S hSM hF hMX hT1
  have hΩ : ∀ m ∈ M, ∀ P ∈ syl3 X, cjSub m P ∈ syl3 X := fun m hm P hP =>
    ⟨cjSub_le (hMX hm) hP.1, by rw [card_cjSub]; exact hP.2⟩
  have hM24 : Nat.card M ≤ 24 := by
    have := Nat.card_le_card_of_injective _ (conjPerm_injective hX hXM hΩ hCM)
    rw [Nat.card_perm, hX.card_syl3] at this
    simpa [Nat.factorial] using this
  have hT8 : Nat.card (S : Subgroup G) = 8 := by
    have h12 : 12 ∣ Nat.card M := hX.card ▸ Subgroup.card_dvd_of_le hXM
    have hdvd : Nat.card (S : Subgroup G) ∣ Nat.card M := Subgroup.card_dvd_of_le hSM
    have hge : 8 ≤ Nat.card (S : Subgroup G) := by
      have hmul := Subgroup.relIndex_mul_card ((S : Subgroup G) ⊓
        Subgroup.centralizer (V : Set G)) (S : Subgroup G)
      rw [inf_eq_left.mpr (inf_le_left : (S : Subgroup G) ⊓
        Subgroup.centralizer (V : Set G) ≤ S)] at hmul
      have h4 : 4 ≤ Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)) :=
        hV4 ▸ Subgroup.card_le_of_le (le_inf hVS hVC)
      have h2 : 2 ≤ ((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)).relIndex S := by
        have h0 : ((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)).relIndex S ≠ 0 :=
          Subgroup.index_ne_zero_of_finite
        have h1 : ((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)).relIndex S ≠ 1 := by
          intro h1
          apply hJ
          exact (thompsonJ_le_self _).trans
            ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right)
        omega
      rw [← hmul]
      calc 8 = 2 * 4 := by norm_num
        _ ≤ _ := Nat.mul_le_mul h2 h4
    have hMpos : 0 < Nat.card M := Nat.card_pos
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn] at hdvd hge ⊢
    have hn4 : n ≤ 4 := by
      by_contra h
      have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.le_of_dvd Nat.card_pos hdvd
      omega
    interval_cases n
    · norm_num at hge
    · norm_num at hge
    · norm_num at hge
    · rfl
    · exfalso
      norm_num at hdvd
      omega
  have hfix : ∀ v ∈ V, (∀ t ∈ (S : Subgroup G), t * v = v * t) → v = 1 ∨ v = z := by
    intro v hv hvc
    refine hZ v (Subgroup.subset_closure ⟨⟨hVS hv, ?_⟩, hVab.2 v hv⟩)
    exact Subgroup.mem_centralizer_iff.mpr fun t ht => hvc t ht
  obtain ⟨a, haS, b, hbS, ha2, ha4, hb2, hrel, hba, hgen⟩ :=
    exists_dihedral_generators hT8 hVS hV4 hVab.2 (hSM.trans hMV) hzV hz1 hzc hfix
  obtain ⟨φ⟩ := nonempty_mulEquiv_dihedralFour haS hbS ha4 hb2 hrel hba hgen
  have hzφ : φ ⟨z, hzS⟩ = r 2 := by
    have hcenD : ∀ g : DihedralGroup 4, (∀ k : DihedralGroup 4, g * k = k * g) →
        g = 1 ∨ g = r 2 := by decide
    have hcen : ∀ k : DihedralGroup 4, φ ⟨z, hzS⟩ * k = k * φ ⟨z, hzS⟩ := by
      intro k
      obtain ⟨t, rfl⟩ := φ.surjective k
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hzc t t.2).symm
    rcases hcenD _ hcen with h | h
    · exfalso
      apply hz1
      have : (⟨z, hzS⟩ : (S : Subgroup G)) = 1 := φ.injective (by rw [h, map_one])
      exact congrArg Subtype.val this
    · exact h
  have hCz := centralizer_eq_of_dihedral hEven S φ hzS hzφ
  have hidx : (Subgroup.zpowers a).relIndex S = 2 := by
    have hmul := Subgroup.relIndex_mul_card (Subgroup.zpowers a) (S : Subgroup G)
    rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr haS), Nat.card_zpowers, ha4, hT8] at hmul
    omega
  have hza : ∀ y ∈ Subgroup.zpowers a, orderOf y = 2 → y = z := by
    intro y hy hy2
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr hy : y ∈ Submonoid.powers a)
    have hn' : a ^ (n % 4) = y := by rw [← ha4, pow_mod_orderOf]; exact hn
    have hlt : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hy2' : y ^ 2 = 1 := by rw [← hy2]; exact pow_orderOf_eq_one y
    interval_cases h : n % 4
    · rw [← hn', pow_zero, orderOf_one] at hy2
      norm_num at hy2
    · rw [← hn', pow_one, ha4] at hy2
      norm_num at hy2
    · rw [← hn', ha2]
    · exfalso
      rw [← hn', ← pow_mul, show 3 * 2 = 4 + 2 by rfl, pow_add,
        show a ^ 4 = 1 by rw [← ha4]; exact pow_orderOf_eq_one a, one_mul, ha2] at hy2'
      exact hz1 hy2'
  have hconj : ∀ u : G, orderOf u = 2 → IsConj u z := fun u hu =>
    isConj_of_index_two hnonab S haS hidx hza hu
  exact hI41 G (fun x y hx hy => (hconj x hx).trans (hconj y hy).symm) z hz2
    ⟨(MulEquiv.subgroupCongr hCz).trans φ⟩

end L1547

end CFSG.Quasithin.EmptyFaithfulMultiple
