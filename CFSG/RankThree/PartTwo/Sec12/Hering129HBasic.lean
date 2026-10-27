module

public import CFSG.RankThree.PartTwo.Sec12.Hering129GNotIii
import CFSG.RankThree.PartTwo.Sec12.Item128BarProofTools
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
public import CFSG.RankThree.PartTwo.Sec12.Hering129Setup

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Aux

variable {G : Type} [Group G] [Finite G]

theorem Cfg129.not_mem_B_of_mem_D {A L K S : Subgroup G} {c b a : G}
    (cfg : Cfg129 G A c L b a K S) {x : G} (hxD : x ∈ D129 a b)
    (hxb : x ∉ Subgroup.zpowers b) : x ∉ Sec4.thetaQuotCentralizer L := by
  have hstd := cfg.std
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  have hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  intro hxC
  obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup (hAc a haA b hbA) hxD
  have hai : a ^ i ∈ Sec4.thetaQuotCentralizer L := by
    have h1 : a ^ i = x * (b ^ j)⁻¹ := by rw [hij]; group
    rw [h1]
    exact Subgroup.mul_mem _ hxC (Subgroup.inv_mem _ (Subgroup.zpow_mem _ cfg.hb.2 j))
  rw [Sec4.zpow_emod_three ha3 i] at hai
  have hi : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hi with h | h | h
  · apply hxb
    rw [hij, Sec4.zpow_emod_three ha3 i, h, zpow_zero, one_mul]
    exact Subgroup.zpow_mem_zpowers b j
  · rw [h, zpow_one] at hai
    exact haB hai
  · rw [h] at hai
    apply haB
    have h2 : a = (a ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← zpow_mul]
      have h3 : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha3
      calc a = a ^ (3 : ℤ) * a := by rw [h3, one_mul]
        _ = a ^ (4 : ℤ) := by rw [← zpow_add_one]; norm_num
        _ = _ := by norm_num
    rw [h2]
    exact Subgroup.zpow_mem _ hai 2

theorem mem_theta_of_mem_theta_of_le {I J : Subgroup G} (hIJ : I ≤ J) {t : G} (htI : t ∈ I)
    (htJ : t ∈ inSubgroup (aschbacherSolvableCore 3) J) :
    (⟨t, htI⟩ : I) ∈ aschbacherSolvableCore 3 I := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJs, -, hJ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := J) Nat.prime_three
  obtain ⟨-, -, -, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := I) Nat.prime_three
  set T : Subgroup G := inSubgroup (aschbacherSolvableCore 3) J with hT
  have hTJ : T ≤ J := Subgroup.map_subtype_le _
  have hTJn : ∀ g ∈ J, ∀ u ∈ T, g * u * g⁻¹ ∈ T := fun g hg u hu =>
    conj_mem_inSubgroup_theta (Subgroup.le_normalizer hg) hu
  set N : Subgroup I := T.subgroupOf I with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    exact hTJn _ (hIJ g.2) _ hn⟩
  have hNs : Group.IsSolvable N := by
    haveI : Group.IsSolvable (aschbacherSolvableCore 3 J) := hJs
    let e : (aschbacherSolvableCore 3 J) ≃* T :=
      Subgroup.equivMapOfInjective _ J.subtype J.subtype_injective
    haveI : Group.IsSolvable T :=
      solvable_of_solvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    let f : N →* T := MonoidHom.codRestrict (I.subtype.comp N.subtype) T (fun x => x.2)
    refine solvable_of_solvable_injective (f := f) (fun x y hxy => ?_)
    have h := congrArg (fun z : T => (z : G)) hxy
    exact Subtype.ext (Subtype.ext h)
  have hN3 : ¬ 3 ∣ Nat.card N := by
    have h1 : Nat.card N = Nat.card (T ⊓ I : Subgroup G) := by
      rw [hN, ← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have h2 : Nat.card (T ⊓ I : Subgroup G) ∣ Nat.card T := Subgroup.card_dvd_of_le inf_le_left
    have h3 : ¬ 3 ∣ Nat.card T := by
      rw [hT, inSubgroup, Subgroup.card_map_of_injective J.subtype_injective]
      exact hJ3
    rw [h1]
    exact fun h => h3 (h.trans h2)
  exact hmax N hNn hNs hN3 (Subgroup.mem_subgroupOf.mpr htJ)

theorem mem_sup_of_mem_thetaQuotCentralizer {A I J : Subgroup G} {x c j g : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hxA : x ∈ A) (hcA : c ∈ A) (hjA : j ∈ A) (hx1 : x ≠ 1) (hc1 : c ≠ 1)
    (hxc : x ∉ Subgroup.zpowers c) (hj : j ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers c)
    (hIJ : I ≤ J) (hjI : j ∈ I) (hcI : c ∈ I)
    (hxI : ∀ i ∈ I, x * i = i * x) (hcI' : ∀ i ∈ I, c * i = i * c)
    (hZ : Nat.card (Subgroup.center (↥I ⧸ aschbacherSolvableCore 3 ↥I)) = 3)
    (hgA : g ∈ A) (hg : g ∈ Sec4.thetaQuotCentralizer J) :
    g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  set U := Subgroup.zpowers x ⊔ Subgroup.zpowers c with hU
  have hU9 : Nat.card U = 9 := Proof128.card_zpowers_sup_eq_nine hAe hcA hxA hc1 hx1 hxc
  have hUA : U ≤ A := sup_le (Subgroup.zpowers_le.mpr hxA) (Subgroup.zpowers_le.mpr hcA)
  have hAeq : Subgroup.zpowers j ⊔ U = A :=
    eq_of_card_nine_lt hA27 (sup_le (Subgroup.zpowers_le.mpr hjA) hUA) le_sup_right hU9
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers j)) hj
  have hjU : ∀ f ∈ U, j * f = f * j := fun f hf => hAc j hjA f (hUA hf)
  obtain ⟨k, f, hf, hgeq⟩ :=
    Hering129G.exists_zpow_mul_of_mem_sup_zpowers_sup hAeq.symm hjU g hgA
  have hUI : ∀ f ∈ U, ∀ i ∈ I, f * i = i * f := by
    have hle : U ≤ Subgroup.centralizer (I : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_iff.mpr fun i hi => (hxI i hi).symm
      · exact Subgroup.mem_centralizer_iff.mpr fun i hi => (hcI' i hi).symm
    intro f hf i hi
    exact (Subgroup.mem_centralizer_iff.mp (hle hf) i hi).symm
  have hjk : j ^ k ∈ I := I.zpow_mem hjI k
  have hA3 : IsPGroup 3 A := fun y => ⟨1, Subtype.ext (by simpa using hAe.2 y y.2)⟩
  have hAθ : A ⊓ inSubgroup (aschbacherSolvableCore 3) I = ⊥ := inf_inSubgroup_theta_eq_bot hA3
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 I) with hπ
  set w : I := ⟨j ^ k, hjk⟩ with hw
  have hcentral : π w ∈ Subgroup.center (↥I ⧸ aschbacherSolvableCore 3 ↥I) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 I) q
    have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hg).2 (i : G) (hIJ i.2)
    have h2 : (g * (i : G) * g⁻¹) = j ^ k * (i : G) * (j ^ k)⁻¹ := by
      rw [hgeq]
      have := hUI f hf i i.2
      calc j ^ k * f * (i : G) * (j ^ k * f)⁻¹ = j ^ k * (f * (i : G) * f⁻¹) * (j ^ k)⁻¹ := by
            group
        _ = j ^ k * (i : G) * (j ^ k)⁻¹ := by
            rw [show f * (i : G) * f⁻¹ = (i : G) by rw [this]; group]
    rw [h2] at h1
    have h3 : ((i : G))⁻¹ * (j ^ k * (i : G) * (j ^ k)⁻¹) ∈ I := by
      exact I.mul_mem (I.inv_mem i.2) (I.mul_mem (I.mul_mem hjk i.2) (I.inv_mem hjk))
    have h4 := mem_theta_of_mem_theta_of_le hIJ h3 h1
    have h5 : (⟨_, h3⟩ : I) = i⁻¹ * (w * i * w⁻¹) := rfl
    rw [h5] at h4
    have h6 : π (i⁻¹ * (w * i * w⁻¹)) = 1 := (QuotientGroup.eq_one_iff _).mpr h4
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h6
    have h7 : π w * π i = π i * π w := by
      have h8 : π i = π w * π i * (π w)⁻¹ := inv_mul_eq_one.mp h6
      calc π w * π i = (π w * π i * (π w)⁻¹) * π w := by group
        _ = π i * π w := by rw [← h8]
    exact h7.symm
  set c' : I := ⟨c, hcI⟩ with hc'
  have hc'π : π c' ≠ 1 := by
    intro h1
    have h2 : c' ∈ aschbacherSolvableCore 3 I := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : c ∈ A ⊓ inSubgroup (aschbacherSolvableCore 3) I :=
      ⟨hcA, Subgroup.mem_map.mpr ⟨c', h2, rfl⟩⟩
    rw [hAθ, Subgroup.mem_bot] at h3
    exact hc1 h3
  have hc'center : π c' ∈ Subgroup.center (↥I ⧸ aschbacherSolvableCore 3 ↥I) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 I) q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcI' i i.2).symm
  have hc'3 : orderOf (π c') = 3 := by
    refine orderOf_eq_prime ?_ hc'π
    rw [← map_pow]
    have : c' ^ 3 = 1 := Subtype.ext (by simpa [hc'] using hAe.2 c hcA)
    rw [this, map_one]
  have hcen_eq : Subgroup.zpowers (π c') = Subgroup.center (↥I ⧸ aschbacherSolvableCore 3 ↥I) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc'center) ?_
    rw [hZ, Nat.card_zpowers, hc'3]
  have hwmem : π w ∈ Subgroup.zpowers (π c') := hcen_eq ▸ hcentral
  obtain ⟨δ, hδ⟩ := Subgroup.mem_zpowers_iff.mp hwmem
  have hδ' : π w = π (c' ^ δ) := by rw [← hδ, map_zpow]
  have h9 : (w⁻¹ * c' ^ δ) ∈ aschbacherSolvableCore 3 I := by
    have h : π (w⁻¹ * c' ^ δ) = 1 := by
      rw [map_mul, map_inv, ← hδ']
      exact inv_mul_cancel _
    exact (QuotientGroup.eq_one_iff _).mp h
  have h10 : (j ^ k)⁻¹ * c ^ δ ∈ A ⊓ inSubgroup (aschbacherSolvableCore 3) I := by
    refine ⟨A.mul_mem (A.inv_mem (A.zpow_mem hjA k)) (A.zpow_mem hcA δ), ?_⟩
    exact Subgroup.mem_map.mpr ⟨_, h9, rfl⟩
  rw [hAθ, Subgroup.mem_bot, inv_mul_eq_one] at h10
  have h11 : j ^ k ∈ Subgroup.zpowers c := ⟨δ, h10.symm⟩
  rw [hgeq]
  exact U.mul_mem (le_sup_right (a := Subgroup.zpowers x) h11) hf

theorem le_centralizer_of_isPerfect_of_le_normalizer_zpowers {R : Subgroup G} {c : G}
    (hR : Group.IsPerfect R) (hRN : R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    R ≤ Subgroup.centralizer ({c} : Set G) := by
  set N : Subgroup G := Subgroup.zpowers c with hN
  set M : Subgroup G := Subgroup.normalizer (N : Set G) with hM
  have hNM : N ≤ M := Subgroup.le_normalizer
  let N' : Subgroup M := N.subgroupOf M
  haveI : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr le_rfl
  haveI : IsCyclic N' := by
    have e : N' ≃* N := Subgroup.subgroupOfEquivOfLe hNM
    exact (MulEquiv.isCyclic e).mpr inferInstance
  let P : Subgroup M := R.subgroupOf M
  have hPperf : Group.IsPerfect P :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hRN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hRN).symm.surjective
  let φ : P →* MulAut N' := (MulAut.conjNormal (H := N')).comp P.subtype
  let ψ : P →* (ZMod (Nat.card N'))ˣ := (IsCyclic.mulAutMulEquiv N').toMonoidHom.comp φ
  have hker : (⊤ : Subgroup P) ≤ ψ.ker := by
    rw [← hPperf.commutator_eq_top]
    exact Abelianization.commutator_subset_ker ψ
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hgM : g ∈ M := hRN hg
  have h1 : ψ ⟨⟨g, hgM⟩, Subgroup.mem_subgroupOf.mpr hg⟩ = 1 := hker (Subgroup.mem_top _)
  have h2 : φ ⟨⟨g, hgM⟩, Subgroup.mem_subgroupOf.mpr hg⟩ = 1 :=
    (IsCyclic.mulAutMulEquiv N').injective (by simpa [ψ] using h1)
  let c'' : N' := ⟨⟨c, hNM (Subgroup.mem_zpowers c)⟩, Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_zpowers c)⟩
  have h3 := congrArg (fun a : MulAut N' => ((a c'' : N') : M)) h2
  simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
    MulAut.one_apply] at h3
  have h4 := congrArg (fun m : M => (m : G)) h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
  calc g * c = (g * c * g⁻¹) * g := by group
    _ = c * g := by rw [h4]

theorem inSubgroup_perfectResidual_normalizer_zpowers {Y : Subgroup G} {c : G} :
    inSubgroup perfectResidual (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) =
      inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({c} : Set G)) := by
  have hCN : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun g hg =>
    mem_normalizer_zpowers_of_commute (Subgroup.mem_centralizer_singleton_iff.mp hg)
  apply le_antisymm
  · have hp := Sec6.isPerfect_inSubgroup_perfectResidual
      (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    have hRle : inSubgroup perfectResidual (Y ⊓ Subgroup.normalizer
        (Subgroup.zpowers c : Set G)) ≤ Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      Subgroup.map_subtype_le _
    have hRC := le_centralizer_of_isPerfect_of_le_normalizer_zpowers hp (hRle.trans inf_le_right)
    exact le_inSubgroup_perfectResidual_of_isPerfect (le_inf (hRle.trans inf_le_left) hRC) hp
  · have hp := Sec6.isPerfect_inSubgroup_perfectResidual (Y ⊓ Subgroup.centralizer ({c} : Set G))
    exact le_inSubgroup_perfectResidual_of_isPerfect
      (((Subgroup.map_subtype_le _ : inSubgroup perfectResidual
        (Y ⊓ Subgroup.centralizer ({c} : Set G)) ≤ _).trans (inf_le_inf_left Y hCN))) hp

@[expose] def resCent (K : Subgroup G) (x : G) : Subgroup G :=
  inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({x} : Set G))

theorem resCent_le (K : Subgroup G) (x : G) :
    resCent K x ≤ K ⊓ Subgroup.centralizer ({x} : Set G) :=
  Subgroup.map_subtype_le _

theorem isPerfect_resCent (K : Subgroup G) (x : G) : Group.IsPerfect (resCent K x) :=
  Sec6.isPerfect_inSubgroup_perfectResidual _

theorem isSLThreePiAt_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {q : ℕ}
    (hX : Sec4.IsSLThreePiAt X q) : Sec4.IsSLThreePiAt Y q := by
  obtain ⟨K, hK, hKf, h1 | h1⟩ := hX
  · obtain ⟨hq, hq3, ⟨f⟩⟩ := h1
    exact ⟨K, hK, hKf, Or.inl ⟨hq, hq3, ⟨e.symm.trans f⟩⟩⟩
  · obtain ⟨hq, hq3, ⟨f⟩⟩ := h1
    exact ⟨K, hK, hKf, Or.inr ⟨hq, hq3, ⟨e.symm.trans f⟩⟩⟩


end Aux

end CFSG.RankThree.PartTwo.Sec12
