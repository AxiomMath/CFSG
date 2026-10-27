module

public import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofCover
public import CFSG.RankThree.PartTwo.Sec15.Item152GenProofS
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofTools
import CFSG.RankThree.PartTwo.Sec15.KS152Named
import CFSG.RankThree.PartTwo.Sec15.Item155Proof
import CFSG.RankThree.PartTwo.KFacts.ONanKS152J2Named
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof155w

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof156Res4

theorem eq_top_of_invariant_two_of_cover {C : Type} [Group C]
    [Finite C] (hperf : Group.IsPerfect C) (Z : Subgroup C) [Z.Normal]
    (hZ : Subgroup.center C = Z) (hZ3 : Nat.card Z = 3) (e : C ⧸ Z ≃* alternatingGroup (Fin 6))
    {B : Subgroup C} (hZB : Z ≤ B) (hB3 : ∀ b ∈ B, b ^ 3 = 1) (hB9 : Nat.card B ≤ 9)
    {H : Subgroup C}
    (hH : ∀ R : Subgroup C, IsPGroup 2 R → B ≤ Subgroup.normalizer (R : Set C) → R ≤ H) :
    H = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ₀ : C →* Equiv.Perm (Fin 6) :=
    (alternatingGroup (Fin 6)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' Z)) with hρ₀
  set ρ : ↥(⊤ : Subgroup C) →* Equiv.Perm (Fin 6) := ρ₀.comp (⊤ : Subgroup C).subtype with hρ
  have hρ₀apply : ∀ x : C, ρ₀ x = (e (QuotientGroup.mk' Z x) : Equiv.Perm (Fin 6)) := fun _ => rfl
  have hρ₀ker : ∀ x : C, ρ₀ x = 1 ↔ x ∈ Z := by
    intro x
    rw [hρ₀apply]
    constructor
    · intro h1
      have h2 : e (QuotientGroup.mk' Z x) = 1 := Subtype.ext h1
      rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact h2
    · intro hx
      have h2 : QuotientGroup.mk' Z x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [h2, map_one]
      rfl
  have hρrange : ρ.range = alternatingGroup (Fin 6) := by
    ext σ
    constructor
    · rintro ⟨k, rfl⟩
      exact (e (QuotientGroup.mk' Z (k : C))).2
    · intro hσ
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z (e.symm ⟨σ, hσ⟩)
      refine ⟨⟨x, Subgroup.mem_top x⟩, ?_⟩
      change (e (QuotientGroup.mk' Z x) : Equiv.Perm (Fin 6)) = σ
      rw [hx, MulEquiv.apply_symm_apply]
  have hρker : ∀ k : ↥(⊤ : Subgroup C), ρ k = 1 ↔ (k : C) ∈ Subgroup.center C := by
    intro k
    rw [hZ]
    exact hρ₀ker k
  have hZ3' : ∀ z ∈ Subgroup.center C, z ^ 3 = 1 := by
    intro z hz
    rw [hZ] at hz
    have h := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  have hperf' : Group.IsPerfect ↥(⊤ : Subgroup C) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup C) ≃* C).symm.toMonoidHom) (MulEquiv.surjective _)
  set B' := B.map ρ₀ with hB'
  have hB'3 : ∀ y ∈ B', y ^ 3 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB3 b hb, map_one]
  have hB'card : Nat.card B' ∣ 3 := by
    set f : ↥B →* Equiv.Perm (Fin 6) := ρ₀.comp B.subtype with hf
    have hrange : f.range = B' := by
      rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    have hZker : Z.subgroupOf B ≤ f.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      exact (hρ₀ker x).mpr (Subgroup.mem_subgroupOf.mp hx)
    have hZcard : Nat.card (Z.subgroupOf B) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv, hZ3]
    have hkle : 3 ≤ Nat.card f.ker := hZcard ▸ Subgroup.card_le_of_le hZker
    have hmul := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hrange] at hmul
    have hle3 : Nat.card B' ≤ 3 := by
      have hpos : 0 < Nat.card B' := Nat.card_pos
      by_contra hgt
      have : 3 * 4 ≤ Nat.card f.ker * Nat.card B' := Nat.mul_le_mul hkle (by omega)
      omega
    have hp3 : IsPGroup 3 B' := fun y => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact hB'3 y y.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp3
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have h9 : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hk] at h9
      omega
    rw [hk]
    interval_cases k <;> norm_num
  have : IsCyclic B' := isCyclic_of_card_dvd_prime hB'card
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := B')
  set t : Equiv.Perm (Fin 6) := (g : Equiv.Perm (Fin 6)) with ht
  have hB't : ∀ y ∈ B', y ∈ Subgroup.zpowers t := by
    intro y hy
    obtain ⟨k, hk⟩ := hg ⟨y, hy⟩
    refine ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have htA : t ∈ alternatingGroup (Fin 6) := by
    obtain ⟨b, -, hb⟩ := g.2
    rw [ht, ← hb]
    exact (e (QuotientGroup.mk' Z b)).2
  have ht3 : t ^ 3 = 1 := hB'3 t g.2
  have hle := le_of_signals (K := ⊤) (ρ := ρ) hperf' hZ3' hρrange hρker htA ht3 (H := H)
    (fun V hV => by
      refine hH _ ?_ ?_
      · intro r
        refine ⟨1, Subtype.ext ?_⟩
        rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
        exact liftSignal_sq _ r.2
      · intro b hb
        refine mem_normalizer_of_conj_le (hB3 b hb) fun r hr => ?_
        have hk₀ : ρ ⟨b, Subgroup.mem_top b⟩ ∈ Subgroup.normalizer (V : Set (Equiv.Perm (Fin 6))) :=
          (Subgroup.zpowers_le.mpr hV.2.2.2) (hB't _ ⟨b, hb, rfl⟩)
        exact conj_mem_liftSignal ⟨b, Subgroup.mem_top b⟩ hk₀ r hr)
  exact top_le_iff.mp hle

variable {G : Type} [Group G] [Finite G]

theorem le_of_invariant_two_of_j2
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {H : Subgroup G}
    (hH : ∀ R : Subgroup G, R ≤ L → IsPGroup 2 R → A ≤ Subgroup.normalizer (R : Set G) → R ≤ H) :
    L ≤ H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set π := QuotientGroup.mk' θ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  have hθ2 : IsPGroup 2 θ := Proof152Gen.isPGroup_theta_of_j2 h hJ
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hθ2
  have hLc : L ≤ Subgroup.centralizer {c} := hD.le_centralizer
  obtain ⟨-, hAL9, hAc⟩ := j2_point_facts hD hJ
  have hAinv : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G) := by
    intro V hVL hV
    rw [hAc]
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (V : Set G) ?_)) hV
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (hVL hv))
  have hθH : inSubgroup (aschbacherSolvableCore 3) L ≤ H :=
    hH _ (Sec6.theta_le L) (hθ2.map L.subtype)
      (hD.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta L))
  set H₀ := (H.subgroupOf L).map π with hH₀
  have hlift : ∀ W : Subgroup (↥L ⧸ θ), IsPGroup 2 W →
      (A.subgroupOf L).map π ≤ Subgroup.normalizer (W : Set (↥L ⧸ θ)) → W ≤ H₀ := by
    intro W hW2 hWA
    have hWH : (W.comap π).map L.subtype ≤ H :=
      hH _ (Subgroup.map_subtype_le _) (isPGroup_map_comap π hW2 hker)
        (hAinv _ (Subgroup.map_subtype_le _) (inf_le_normalizer_map_comap π hWA))
    intro w hw
    obtain ⟨l, rfl⟩ := hπs w
    exact ⟨l, Subgroup.mem_subgroupOf.mpr (hWH ⟨l, hw, rfl⟩), rfl⟩
  obtain ⟨U, hU⟩ := exists_mem_scriptQPiStar155 (A := A)
    (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2)
  obtain ⟨hQ2, hQ64⟩ := Proof152Gen.sixtyFour_dvd_card_map_inf ks152J2InvolNine_holds h hJ hU
  have hQH : ((U ⊓ L).subgroupOf L).map π ≤ H₀ := by
    have hAU : A ≤ Subgroup.normalizer (U : Set G) := hU.prop.1.1.1.2.2
    have hU2 : IsPGroup 2 U := isPGroup_of_mem_scriptQPi Nat.prime_two hU.prop
    have hle : U ⊓ L ≤ H := hH _ inf_le_right (hU2.to_le inf_le_left)
      (Late.le_normalizer_inf hAU hD.le_normalizer)
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨d, hdA, hd1, hdL, S3, hdS3, hS3d⟩ := exists_three_central_of_j2 hD hJ
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  set z : ↥L ⧸ θ := π ⟨d, hdL⟩ with hz
  have hz1 : z ≠ 1 := by
    intro hz1
    have hmem : (⟨d, hdL⟩ : ↥L) ∈ θ := (QuotientGroup.eq_one_iff _).mp hz1
    have hord : orderOf (⟨⟨d, hdL⟩, hmem⟩ : θ) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hd3 hd1
    have h3 := orderOf_dvd_natCard (⟨⟨d, hdL⟩, hmem⟩ : θ)
    rw [hord] at h3
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1 h3
  have hzc : ∃ S' : Sylow 3 (↥L ⧸ θ), z ∈ (S' : Subgroup (↥L ⧸ θ)) ∧
      (S' : Subgroup (↥L ⧸ θ)) ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) := by
    refine ⟨S3.mapSurjective hπs, ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact ⟨⟨d, hdL⟩, hdS3, rfl⟩
    · rw [Sylow.coe_mapSurjective]
      rintro _ ⟨s, hs, rfl⟩
      have hs' := hS3d hs
      rw [Subgroup.mem_centralizer_singleton_iff] at hs' ⊢
      rw [hz, ← map_mul, ← map_mul, hs']
  set C := Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) with hC
  obtain ⟨hZc, hZ3, hZn, ⟨eA⟩⟩ := KFacts.KS14.Native.j2_centralizer_quotient hJ hz1 hzc
  have hZ := KFacts.KS14.Native.j2_center_centralizer hJ hz1 hzc
  have hCp := KFacts.KS14.Native.j2_centralizer_isPerfect hJ hz1 hzc
  set Z := (Subgroup.zpowers z).subgroupOf C with hZdef
  set Abar := (A.subgroupOf L).map π with hAbar
  have hAbarC : Abar ≤ C := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff, hz, ← map_mul, ← map_mul]
    have hcomm : (a : G) * d = d * (a : G) := congrArg Subtype.val
      (hA.1.1.is_comm.comm ⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩ ⟨d, hdA⟩)
    have hcomm' : a * ⟨d, hdL⟩ = ⟨d, hdL⟩ * a := Subtype.ext hcomm
    rw [hcomm']
  set B := Abar.subgroupOf C with hB
  have hzAbar : z ∈ Abar := ⟨⟨d, hdL⟩, Subgroup.mem_subgroupOf.mpr hdA, rfl⟩
  have hZB : Z ≤ B := by
    intro x hx
    rw [hB, Subgroup.mem_subgroupOf]
    rw [hZdef, Subgroup.mem_subgroupOf] at hx
    exact (Subgroup.zpowers_le.mpr hzAbar) hx
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := by
    intro b hb
    rw [hB, Subgroup.mem_subgroupOf] at hb
    obtain ⟨a, ha, hab⟩ := hb
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hab, ← map_pow]
    have ha3 : (a : ↥L) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hA.1.2 _ (Subgroup.mem_subgroupOf.mp ha))
    rw [ha3, map_one]
  have hB9 : Nat.card B ≤ 9 := by
    have h1 : Nat.card B = Nat.card Abar :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAbarC).toEquiv
    rw [h1, hAbar, card_map_mk_subgroupOf hA.1, hAL9]
  have hCH : C ≤ H₀ := by
    have htop := eq_top_of_invariant_two_of_cover (C := ↥C) hCp Z hZ hZ3 eA hZB hB3 hB9
      (H := H₀.subgroupOf C) (fun R hR2 hBR => by
        intro r hr
        rw [Subgroup.mem_subgroupOf]
        refine hlift (R.map C.subtype) (hR2.map C.subtype) ?_ ⟨r, hr, rfl⟩
        rintro _ ⟨a, ha, rfl⟩
        have haC : π a ∈ C := hAbarC ⟨a, ha, rfl⟩
        have haB : (⟨π a, haC⟩ : ↥C) ∈ B := by
          rw [hB, Subgroup.mem_subgroupOf]
          exact ⟨a, ha, rfl⟩
        have hN := Subgroup.le_normalizer_map C.subtype ⟨⟨π a, haC⟩, hBR haB, rfl⟩
        exact hN)
    intro x hx
    have : (⟨x, hx⟩ : ↥C) ∈ H₀.subgroupOf C := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨F₀, hF₀p, hF₀60⟩ := Proof156.exists_isPerfect_card_sixty_of_quotient_six Z hZc hZ3 eA
  have htop := ks152J2Gen_holds (↥L ⧸ θ) hJ z hz1 hzc _ (F₀.map C.subtype) hQ2 hQ64
    (Subgroup.map_subtype_le F₀) (isPerfect_map_subtype hF₀p)
    (by rw [Subgroup.card_map_of_injective C.subtype_injective, hF₀60])
  have hH₀ : H₀ = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact sup_le hQH ((Subgroup.map_subtype_le F₀).trans hCH)
  intro l hl
  obtain ⟨j, hj, hjl⟩ : π ⟨l, hl⟩ ∈ H₀ := hH₀ ▸ Subgroup.mem_top _
  have hjθ : j⁻¹ * ⟨l, hl⟩ ∈ θ := by
    rw [← QuotientGroup.eq]
    exact hjl
  have h1 : ((j⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ H := hθH ⟨_, hjθ, rfl⟩
  have h2 : (j : G) ∈ H := Subgroup.mem_subgroupOf.mp hj
  have h3 : l = (j : G) * ((j⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h3]
  exact H.mul_mem h2 h1

theorem le_delta_of_le_of_j2
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {H' : Subgroup G} (hLH : L ≤ H') : L ≤ delta A (lB A) H' := by
  have hD := h.toSec13Data
  have hLN : L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)
  refine le_of_invariant_two_of_j2 h hJ fun R hRL hR2 hAR => ?_
  have hR3 : ¬ 3 ∣ Nat.card R := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  exact le_delta (mem_scriptQ_of_hj_point h hJ ⟨hRL.trans hLN,
    (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩).1 (hRL.trans hLH)

end CFSG.RankThree.PartTwo.Sec15.Proof155w
