module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofPoints
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofM12Q
import CFSG.RankThree.PartTwo.KFacts.K412Conjugacy
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413Res3

variable {G : Type} [Group G] [Finite G]

section Pre

variable {L : Subgroup G} {M : Type*} [Group M] (π : ↥L →* M)

@[expose] def preP (V : Subgroup M) : Subgroup G := (V.comap π).map L.subtype

omit [Finite G] in
theorem preP_le (V : Subgroup M) : preP π V ≤ L := Subgroup.map_subtype_le _

omit [Finite G] in
theorem mem_preP {V : Subgroup M} {g : G} (hg : g ∈ L) : g ∈ preP π V ↔ π ⟨g, hg⟩ ∈ V := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact hh
  · intro hv
    exact ⟨⟨g, hg⟩, hv, rfl⟩

@[expose] def imgP (R : Subgroup G) : Subgroup M := (R.subgroupOf L).map π

omit [Finite G] in
theorem mem_imgP (hπ : Function.Injective π) {R : Subgroup G} {g : G} (hg : g ∈ L) :
    π ⟨g, hg⟩ ∈ imgP π R ↔ g ∈ R := by
  constructor
  · rintro ⟨h, hh, hhg⟩
    have : h = ⟨g, hg⟩ := hπ hhg
    rw [this] at hh
    exact Subgroup.mem_subgroupOf.mp hh
  · intro hgR
    exact ⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.mpr hgR, rfl⟩

omit [Finite G] in
theorem imgP_le_iff (hπ : Function.Injective π) {R : Subgroup G} (hRL : R ≤ L)
    {V : Subgroup M} : imgP π R ≤ V ↔ R ≤ preP π V := by
  constructor
  · intro h g hg
    exact (mem_preP π (hRL hg)).mpr (h ((mem_imgP π hπ (hRL hg)).mpr hg))
  · rintro h _ ⟨r, hr, rfl⟩
    exact (mem_preP π r.2).mp (h (Subgroup.mem_subgroupOf.mp hr))

omit [Finite G] in
theorem card_imgP (hπ : Function.Injective π) {R : Subgroup G} (hRL : R ≤ L) :
    Nat.card (imgP π R) = Nat.card R := by
  rw [imgP, Subgroup.card_map_of_injective hπ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv]

omit [Finite G] in
theorem card_preP (hπ : Function.Injective π) {V : Subgroup M} (hV : V ≤ π.range) :
    Nat.card (preP π V) = Nat.card V := by
  have h1 : imgP π (preP π V) = V := by
    refine le_antisymm ((imgP_le_iff π hπ (preP_le π V)).mpr le_rfl) fun v hv => ?_
    obtain ⟨l, rfl⟩ := hV hv
    exact (mem_imgP π hπ l.2).mpr ((mem_preP π l.2).mpr hv)
  rw [← card_imgP π hπ (preP_le π V), h1]

end Pre

theorem hyperplane_of_family {M : Type*} [Group M] [Finite M] {A L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hAel : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hc : orderOf c = 3) (hcL : c ∉ L) (h27 : Nat.card A = 27)
    (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (π : ↥L →* M) (hπ : Function.Injective π)
    {T : Subgroup M} (hT : (A.subgroupOf L).map π = T) {ι : Type*} (hι : Nonempty ι)
    (W : ι → Subgroup M) (hWL : ∀ i, W i ≤ π.range) (hW2 : ∀ i, IsPGroup 2 (W i))
    (hWT : ∀ i, T ≤ Subgroup.normalizer (W i : Set M))
    (hWmax : ∀ Y : Subgroup M, IsPGroup 2 Y → T ≤ Subgroup.normalizer (Y : Set M) → Y ≠ ⊥ →
      ∃ i, Y ≤ W i)
    (hWa : ∀ i, ∃ a ∈ T, a ≠ 1 ∧ a ∈ Subgroup.centralizer (W i : Set M))
    (hWz : ∀ i, ∃ z ∈ T, z ∉ Subgroup.centralizer (W i : Set M))
    (hQ : ∀ R : Subgroup G, R ≤ L → A ≤ Subgroup.normalizer (R : Set G) → IsPGroup 2 R →
      R ∈ scriptQPi A (lB A) L (piOf 2))
    {R : Subgroup G} (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2)) :
    ∃ i, R = preP π (W i) ∧ IsHyperplane A (A ⊓ Subgroup.centralizer (R : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAπ : ∀ b (hb : b ∈ A ⊓ L), π ⟨b, hb.2⟩ ∈ T := fun b hb =>
    hT ▸ ⟨⟨b, hb.2⟩, Subgroup.mem_subgroupOf.mpr hb.1, rfl⟩
  have hπA : ∀ t ∈ T, ∃ b ∈ A ⊓ L, ∃ hb : b ∈ L, π ⟨b, hb⟩ = t := by
    intro t ht
    rw [← hT] at ht
    obtain ⟨m, hm, rfl⟩ := ht
    exact ⟨m, ⟨Subgroup.mem_subgroupOf.mp hm, m.2⟩, m.2, rfl⟩
  have hcC : ∀ S : Subgroup G, S ≤ L → c ∈ Subgroup.centralizer (S : Set G) :=
    fun S hS => Subgroup.mem_centralizer_iff.mpr fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (hS hs))
  have hNpre : ∀ (V : Subgroup M) (b : G) (hb : b ∈ L),
      π ⟨b, hb⟩ ∈ Subgroup.normalizer (V : Set M) →
        b ∈ Subgroup.normalizer (preP π V : Set G) := by
    intro V b hb hbN
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    rw [SetLike.mem_coe] at hg ⊢
    have hgL := preP_le π V hg
    have hconj : π ⟨b * g * b⁻¹, mul_mem (mul_mem hb hgL) (inv_mem hb)⟩ =
        π ⟨b, hb⟩ * π ⟨g, hgL⟩ * (π ⟨b, hb⟩)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [mem_preP π (mul_mem (mul_mem hb hgL) (inv_mem hb)), hconj]
    exact (Subgroup.mem_normalizer_iff.mp hbN _).mp ((mem_preP π hgL).mp hg)
  have hAN : ∀ i, A ≤ Subgroup.normalizer (preP π (W i) : Set G) := by
    intro i x hx
    obtain ⟨k, -, b, hb, rfl⟩ := exists_pow_mul_of_mem hAel hcA hAa hx
    exact mul_mem (pow_mem (Subgroup.centralizer_le_normalizer _ (hcC _ (preP_le π _))) k)
      (hNpre _ b hb.2 (hWT i (hAπ b hb)))
  have hP2 : ∀ i, IsPGroup 2 (preP π (W i)) := by
    intro i
    obtain ⟨k, hk⟩ := (hW2 i).exists_card_eq
    exact IsPGroup.of_card (n := k) (by rw [card_preP π hπ (hWL i), hk])
  have hPQ : ∀ i, preP π (W i) ∈ scriptQPi A (lB A) L (piOf 2) := fun i =>
    hQ _ (preP_le π _) (hAN i) (hP2 i)
  obtain ⟨i₀⟩ := hι
  have hR0 : R ≠ ⊥ := by
    intro h0
    have h1 := hR.2 (hPQ i₀) (by rw [h0]; exact bot_le)
    rw [h0, le_bot_iff] at h1
    obtain ⟨z, -, hz⟩ := hWz i₀
    apply hz
    have hW0 : W i₀ = ⊥ := by
      have h2 := card_preP π hπ (hWL i₀)
      rw [h1, Subgroup.card_bot] at h2
      exact Subgroup.eq_bot_of_card_eq _ h2.symm
    rw [hW0]
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
      rw [hh, one_mul, mul_one]
  have hRL : R ≤ L := hR.prop.1.2
  have himg2 : IsPGroup 2 (imgP π R) := by
    obtain ⟨k, hk⟩ := (isPGroup_of_mem_scriptQPi Nat.prime_two hR.prop).exists_card_eq
    exact IsPGroup.of_card (n := k) (by rw [card_imgP π hπ hRL, hk])
  have himgT : T ≤ Subgroup.normalizer (imgP π R : Set M) := by
    intro t ht
    obtain ⟨b, hbAL, hb, rfl⟩ := hπA t ht
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨r, hr, rfl⟩ := hy
    have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
    have h1 : b * r * b⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hR.prop.1.1.1.2.2 hbAL.1) _).mp hrR
    refine ⟨⟨b * r * b⁻¹, mul_mem (mul_mem hb r.2) (inv_mem hb)⟩,
      Subgroup.mem_subgroupOf.mpr h1, ?_⟩
    change π (⟨b, hb⟩ * r * ⟨b, hb⟩⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have himg0 : imgP π R ≠ ⊥ := by
    intro h0
    apply hR0
    have h1 := card_imgP π hπ hRL
    rw [h0, Subgroup.card_bot] at h1
    exact Subgroup.eq_bot_of_card_eq R h1.symm
  obtain ⟨i, hi⟩ := hWmax _ himg2 himgT himg0
  have hRP : R = preP π (W i) := hR.eq_of_le (hPQ i) ((imgP_le_iff π hπ hRL).mp hi)
  refine ⟨i, hRP, ?_⟩
  obtain ⟨a, haT, ha1, haC⟩ := hWa i
  obtain ⟨z, hzT, hzC⟩ := hWz i
  obtain ⟨aa, haaAL, haaL, rfl⟩ := hπA a haT
  obtain ⟨zz, hzzAL, hzzL, rfl⟩ := hπA z hzT
  have hmemC : ∀ (g : G) (hg : g ∈ L), π ⟨g, hg⟩ ∈ Subgroup.centralizer (W i : Set M) →
      g ∈ Subgroup.centralizer (R : Set G) := by
    intro g hg hgC
    rw [hRP, Subgroup.mem_centralizer_iff]
    intro r hr
    have hrL := preP_le π _ hr
    have h1 := Subgroup.mem_centralizer_iff.mp hgC _ ((mem_preP π hrL).mp hr)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hπ h1)
  have hnotC : zz ∉ Subgroup.centralizer (R : Set G) := by
    intro hzzC
    apply hzC
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨l, rfl⟩ := hWL i hw
    have hlR : (l : G) ∈ R := by rw [hRP]; exact (mem_preP π l.2).mpr hw
    have h1 := Subgroup.mem_centralizer_iff.mp hzzC _ hlR
    have h2 : l * ⟨zz, hzzL⟩ = ⟨zz, hzzL⟩ * l := Subtype.ext h1
    have h3 := congrArg π h2
    rwa [map_mul, map_mul] at h3
  have hle : Subgroup.closure ({c, aa} : Set G) ≤ A ⊓ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨hcA, hcC R hRL⟩
    · exact ⟨haaAL.1, hmemC _ haaL haC⟩
  have hne : A ⊓ Subgroup.centralizer (R : Set G) ≠ A := by
    intro h
    exact hnotC (by rw [← h] at hzzAL; exact hzzAL.1.2)
  have hgt : 3 < Nat.card (Subgroup.closure ({c, aa} : Set G)) := by
    have hlt : Subgroup.zpowers c < Subgroup.closure ({c, aa} : Set G) := by
      refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr (Subgroup.subset_closure
        (Set.mem_insert c _))) fun h => ?_
      have haa : aa ∈ Subgroup.zpowers c := h ▸ Subgroup.subset_closure
        (Set.mem_insert_of_mem c (Set.mem_singleton aa))
      have h1 : aa ∈ L ⊓ Subgroup.zpowers c := ⟨haaL, haa⟩
      rw [Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hc hcL, Subgroup.mem_bot] at h1
      apply ha1
      have h2 : (⟨aa, haaL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [h2, map_one]
    have h3 : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc]
    rw [← h3]
    exact Subgroup.card_lt_of_lt hlt
  have hdvd1 : Nat.card (Subgroup.closure ({c, aa} : Set G)) ∣
      Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) :=
    Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k₂, hk₂, hk₂'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd2
  have hk₂3 : k₂ ≠ 3 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk₂', h27]; norm_num))
  have hle2 := Nat.le_of_dvd (by rw [hk₂']; positivity) hdvd1
  refine ⟨inf_le_left, ?_⟩
  rw [h27, hk₂']
  interval_cases k₂
  · rw [hk₂'] at hle2; omega
  · rw [hk₂'] at hle2; omega
  · norm_num
  · exact absurd rfl hk₂3

section M12

open CFSG.GH74.M12.Hyp (G12)
open CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig (V ai tbl_ai isPGroup_V A_le_normalizer_V
  le_V_of_mem_invariant z_mem_A card_C)
open scoped commutatorElement

theorem ai_ne_one (i : Fin 3) :
    ai i ≠ 1 := by
  intro h
  have h1 := card_C i
  have h2 : Subgroup.centralizer ({ai i} : Set G12) = ⊤ := by
    rw [h]
    exact Subgroup.eq_top_iff' _ |>.mpr fun g =>
      Subgroup.mem_centralizer_singleton_iff.mpr (by rw [one_mul, mul_one])
  rw [h2, Subgroup.card_top, KFacts.KS14.card_nativeM12] at h1
  norm_num at h1

theorem m12_family
    {A L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hAel : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hc : orderOf c = 3) (hcL : c ∉ L) (h27 : Nat.card A = 27)
    (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (χ : ↥L ≃* G12)
    (hχ : (A.subgroupOf L).map χ.toMonoidHom = Toolkit.M12.basisA.sub)
    (hQ : ∀ R : Subgroup G, R ≤ L → A ≤ Subgroup.normalizer (R : Set G) → IsPGroup 2 R →
      R ∈ scriptQPi A (lB A) L (piOf 2))
    {R : Subgroup G} (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2)) :
    ∃ i : Fin 3, R = preP χ.toMonoidHom (V i) ∧
      IsHyperplane A (A ⊓ Subgroup.centralizer (R : Set G)) :=
  hyperplane_of_family hLc hAel hcA hc hcL h27 hAa χ.toMonoidHom χ.injective hχ ⟨0⟩ V
    (fun _ => by rw [MonoidHom.range_eq_top_of_surjective _ χ.surjective]; exact le_top)
    isPGroup_V A_le_normalizer_V
    (fun Y hY2 hYT hY0 => le_V_of_mem_invariant
      ⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two Y).mpr hY2, hYT⟩ hY0)
    (fun i => ⟨ai i, Proof1413Res2.ai_mem_A i, ai_ne_one i,
      Proof1413Res2.ai_mem_centralizer_V i⟩)
    (fun i => ⟨⁅Toolkit.M12.x, Toolkit.M12.y⁆, z_mem_A, Proof1413Res2.z_not_mem_centralizer_V i⟩)
    hQ hR

@[expose] noncomputable def tI (i : Fin 3) : G12 :=
  Toolkit.M12.wE Toolkit.M12.wU ^ i.val * Toolkit.M12.wE Toolkit.M12.wS *
    (Toolkit.M12.wE Toolkit.M12.wU ^ i.val)⁻¹

theorem tI_conj_ai (i : Fin 3) : tI i * ai i * (tI i)⁻¹ = (ai i)⁻¹ := by
  rw [Toolkit.M12.eq_iff_tbl, Toolkit.M12.tblG_conj, Toolkit.M12.tblG_inv, tbl_ai, tI,
    Toolkit.M12.tblG_mul, Toolkit.M12.tblG_mul, Toolkit.M12.tblG_inv, Toolkit.M12.tblG_pow,
    Toolkit.M12.tbl_wE, Toolkit.M12.tbl_wE]
  fin_cases i <;> decide +kernel

theorem tI_mem_normalizer (i : Fin 3) :
    tI i ∈ Subgroup.normalizer (Toolkit.M12.basisA.sub : Set G12) := by
  obtain ⟨hu, hs, -⟩ := Toolkit.M12.us_tables
  have huN : Toolkit.M12.wE Toolkit.M12.wU ∈
      Subgroup.normalizer (Toolkit.M12.basisA.sub : Set G12) :=
    (Toolkit.M12.mem_normalizer_pair_iff Toolkit.M12.tbl_z Toolkit.M12.tbl_a
      Toolkit.M12.mem_A_iff _).2 (by rw [Toolkit.M12.tbl_wE]; exact hu)
  have hsN : Toolkit.M12.wE Toolkit.M12.wS ∈
      Subgroup.normalizer (Toolkit.M12.basisA.sub : Set G12) :=
    (Toolkit.M12.mem_normalizer_pair_iff Toolkit.M12.tbl_z Toolkit.M12.tbl_a
      Toolkit.M12.mem_A_iff _).2 (by rw [Toolkit.M12.tbl_wE]; exact hs)
  exact mul_mem (mul_mem (pow_mem huN _) hsN) (inv_mem (pow_mem huN _))

theorem m12_inv
    {A L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hAel : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hc : orderOf c = 3) (hcL : c ∉ L) (h27 : Nat.card A = 27)
    (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (χ : ↥L ≃* G12)
    (hχ : (A.subgroupOf L).map χ.toMonoidHom = Toolkit.M12.basisA.sub) {R : Subgroup G}
    {i : Fin 3} (hRi : R = preP χ.toMonoidHom (V i))
    (hB : IsHyperplane A (A ⊓ Subgroup.centralizer (R : Set G))) :
    ∃ t ∈ L ⊓ Subgroup.normalizer (A : Set G),
      ∀ x ∈ A ⊓ Subgroup.centralizer (R : Set G) ⊓ L, t * x * t⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hχA : ∀ t ∈ Toolkit.M12.basisA.sub, ((χ.symm t : ↥L) : G) ∈ A := by
    intro t ht
    rw [← hχ] at ht
    obtain ⟨m, hm, rfl⟩ := ht
    have h1 : ((χ.symm (χ.toMonoidHom m) : ↥L) : G) = (m : G) := by simp
    rw [h1]
    exact Subgroup.mem_subgroupOf.mp hm
  set aa : G := ((χ.symm (ai i) : ↥L) : G) with haa
  have haaL : aa ∈ L := (χ.symm (ai i)).2
  have haaχ : χ ⟨aa, haaL⟩ = ai i := by simp [haa]
  have haaC : aa ∈ Subgroup.centralizer (R : Set G) := by
    rw [hRi, Subgroup.mem_centralizer_iff]
    intro r hr
    have hrL := preP_le χ.toMonoidHom _ hr
    have h1 := Subgroup.mem_centralizer_iff.mp (Proof1413Res2.ai_mem_centralizer_V i) _
      ((mem_preP χ.toMonoidHom hrL).mp hr)
    change χ ⟨r, hrL⟩ * ai i = ai i * χ ⟨r, hrL⟩ at h1
    rw [← haaχ, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (χ.injective h1)
  have haaBL : aa ∈ A ⊓ Subgroup.centralizer (R : Set G) ⊓ L :=
    ⟨⟨hχA _ (Proof1413Res2.ai_mem_A i), haaC⟩, haaL⟩
  have haa1 : aa ≠ 1 := by
    intro h1
    apply ai_ne_one i
    rw [← haaχ]
    have h2 : (⟨aa, haaL⟩ : ↥L) = 1 := Subtype.ext h1
    rw [h2, map_one]
  have haa3 : orderOf aa = 3 := orderOf_eq_prime (hAel.2 aa haaBL.1.1) haa1
  have hcB : c ∈ A ⊓ Subgroup.centralizer (R : Set G) :=
    ⟨hcA, Subgroup.mem_centralizer_iff.mpr fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mp
        (hLc (hRi ▸ preP_le χ.toMonoidHom (V i) |>.trans le_rfl <| hr))⟩
  obtain ⟨a', -, ha'3, hBL, -⟩ := exists_point_of_hyperplane hAel h27 hcA hc hcL hAa hB hcB
  have hBLa : A ⊓ Subgroup.centralizer (R : Set G) ⊓ L = Subgroup.zpowers aa := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haaBL) ?_).symm
    rw [hBL, Nat.card_zpowers, Nat.card_zpowers, ha'3, haa3]
  set t : G := ((χ.symm (tI i) : ↥L) : G) with ht
  have htL : t ∈ L := (χ.symm (tI i)).2
  have htχ : χ ⟨t, htL⟩ = tI i := by simp [ht]
  have htc : ∀ k : ℕ, t * c ^ k * t⁻¹ = c ^ k := by
    intro k
    have h1 : Commute t c := Subgroup.mem_centralizer_singleton_iff.mp (hLc htL)
    rw [(h1.pow_right k).eq, mul_inv_cancel_right]
  have htA : t ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨k, -, b, hb, rfl⟩ := exists_pow_mul_of_mem hAel hcA hAa ha
    have hbT : χ ⟨b, hb.2⟩ ∈ Toolkit.M12.basisA.sub :=
      hχ ▸ ⟨⟨b, hb.2⟩, Subgroup.mem_subgroupOf.mpr hb.1, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (tI_mem_normalizer i) _).mp hbT
    rw [← htχ, ← map_mul, ← map_inv, ← map_mul] at h1
    have h2 := hχA _ h1
    rw [MulEquiv.symm_apply_apply] at h2
    rw [show t * (c ^ k * b) * t⁻¹ = (t * c ^ k * t⁻¹) * (t * b * t⁻¹) by group, htc k]
    exact mul_mem (pow_mem hcA k) h2
  refine ⟨t, ⟨htL, htA⟩, fun x hx => ?_⟩
  rw [hBLa] at hx
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, aa ^ n = x := by
    have h1 : x ∈ (Submonoid.powers aa : Set G) := by
      rw [powers_eq_zpowers]
      exact hx
    exact Submonoid.mem_powers_iff _ _ |>.mp h1
  have htaa : t * aa * t⁻¹ = aa⁻¹ := by
    have h1 : χ.symm (tI i * ai i * (tI i)⁻¹) = χ.symm ((ai i)⁻¹) := by rw [tI_conj_ai]
    rw [map_mul, map_mul, map_inv, map_inv] at h1
    have h2 := congrArg Subtype.val h1
    simpa [ht, haa] using h2
  rw [← conj_pow, htaa, inv_pow]

end M12

section A7

open Equiv KFacts.KP2

theorem eNineF_conj_vF : ∀ i j : Fin 3, ∀ m : Fin 4,
    (∃ m' : Fin 4, eNineF i j * vOneF m * (eNineF i j)⁻¹ = vOneF m') ∧
      ∃ m' : Fin 4, eNineF i j * vTwoF m * (eNineF i j)⁻¹ = vTwoF m' := by
  decide +kernel

theorem eNine_le_normalizer_vOne : eNine ≤ Subgroup.normalizer (vOne : Set (Perm (Fin 7))) := by
  rintro _ ⟨i, j, rfl⟩
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨m', hm'⟩ := (eNineF_conj_vF i j m).1
  exact ⟨m', hm'⟩

theorem eNine_le_normalizer_vTwo : eNine ≤ Subgroup.normalizer (vTwo : Set (Perm (Fin 7))) := by
  rintro _ ⟨i, j, rfl⟩
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨m', hm'⟩ := (eNineF_conj_vF i j m).2
  exact ⟨m', hm'⟩

theorem cOne_cTwo_ne_one : cOne ≠ 1 ∧ cTwo ≠ 1 := by decide

theorem a7_family {A L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hAel : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hc : orderOf c = 3) (hcL : c ∉ L) (h27 : Nat.card A = 27)
    (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (ψ : ↥L ≃* ↥(alternatingGroup (Fin 7)))
    (hQ : ∀ R : Subgroup G, R ≤ L → A ≤ Subgroup.normalizer (R : Set G) → IsPGroup 2 R →
      R ∈ scriptQPi A (lB A) L (piOf 2))
    {R : Subgroup G} (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2)) :
    IsHyperplane A (A ⊓ Subgroup.centralizer (R : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π₀ : ↥L →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp ψ.toMonoidHom
    with hπ₀
  have hπ₀i : Function.Injective π₀ := Subtype.val_injective.comp ψ.injective
  have hE9 : Nat.card ((A.subgroupOf L).map π₀) = 9 := by
    rw [Subgroup.card_map_of_injective hπ₀i, ← h9, ← Subgroup.subgroupOf_map_subtype,
      Subgroup.card_map_of_injective L.subtype_injective]
  obtain ⟨g, hg⟩ := KFacts.K412.exists_conj_eq_eNine hE9
  set π : ↥L →* Perm (Fin 7) := (MulAut.conj g).toMonoidHom.comp π₀ with hπdef
  have hπi : Function.Injective π := (MulAut.conj g).injective.comp hπ₀i
  have hT : (A.subgroupOf L).map π = eNine := by
    rw [hπdef, ← Subgroup.map_map, hg]
  have hrange : alternatingGroup (Fin 7) ≤ π.range := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ alternatingGroup (Fin 7) := by
      have := (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem x hx g⁻¹
      simpa using this
    refine ⟨ψ.symm ⟨g⁻¹ * x * g, hx'⟩, ?_⟩
    simp [hπdef, hπ₀, MulAut.conj_apply, mul_assoc]
  have hvOneA : vOne ≤ alternatingGroup (Fin 7) := vOne_le_centOne.trans inf_le_right
  have hvTwoA : vTwo ≤ alternatingGroup (Fin 7) := vTwo_le_centTwo.trans inf_le_right
  set W : Fin 2 → Subgroup (Perm (Fin 7)) := ![vOne, vTwo] with hW
  have hWL : ∀ i, W i ≤ π.range := by
    rw [Fin.forall_fin_two]
    exact ⟨hvOneA.trans hrange, hvTwoA.trans hrange⟩
  have hW2 : ∀ i, IsPGroup 2 (W i) := by
    rw [Fin.forall_fin_two]
    exact ⟨IsPGroup.of_card (n := 2) (by rw [show W 0 = vOne from rfl, card_vOne]; norm_num),
      IsPGroup.of_card (n := 2) (by rw [show W 1 = vTwo from rfl, card_vTwo]; norm_num)⟩
  have hWT : ∀ i, eNine ≤ Subgroup.normalizer (W i : Set (Perm (Fin 7))) := by
    rw [Fin.forall_fin_two]
    exact ⟨eNine_le_normalizer_vOne, eNine_le_normalizer_vTwo⟩
  have hWmax : ∀ Y : Subgroup (Perm (Fin 7)), IsPGroup 2 Y →
      eNine ≤ Subgroup.normalizer (Y : Set (Perm (Fin 7))) → Y ≠ ⊥ → ∃ i, Y ≤ W i := by
    intro Y hY2 hYT _
    have h3 : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_isPGroup_two hY2
    rcases le_vOne_or_le_vTwo h3 (hYT cOne_mem_eNine) (hYT cTwo_mem_eNine) with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hWa : ∀ i, ∃ a ∈ eNine, a ≠ 1 ∧ a ∈ Subgroup.centralizer (W i : Set (Perm (Fin 7))) := by
    rw [Fin.forall_fin_two]
    refine ⟨⟨cOne, cOne_mem_eNine, cOne_cTwo_ne_one.1, Subgroup.mem_centralizer_iff.mpr
      fun v hv => ?_⟩, ⟨cTwo, cTwo_mem_eNine, cOne_cTwo_ne_one.2, Subgroup.mem_centralizer_iff.mpr
      fun v hv => ?_⟩⟩
    · obtain ⟨m, rfl⟩ := hv
      exact (vOneF_spec m).1
    · obtain ⟨m, rfl⟩ := hv
      exact (vTwoF_spec m).1
  have hWz : ∀ i, ∃ z ∈ eNine, z ∉ Subgroup.centralizer (W i : Set (Perm (Fin 7))) := by
    rw [Fin.forall_fin_two]
    refine ⟨⟨cTwo, cTwo_mem_eNine, fun h => ?_⟩, ⟨cOne, cOne_mem_eNine, fun h => ?_⟩⟩
    · exact vOneF_not_commute 1 (by decide) (Subgroup.mem_centralizer_iff.mp h _ ⟨1, rfl⟩)
    · exact vTwoF_not_commute 1 (by decide) (Subgroup.mem_centralizer_iff.mp h _ ⟨1, rfl⟩)
  obtain ⟨i, -, hB⟩ := hyperplane_of_family hLc hAel hcA hc hcL h27 hAa π hπi hT
    (⟨0⟩ : Nonempty (Fin 2)) W hWL hW2 hWT hWmax hWa hWz hQ hR
  exact hB

end A7

end Proof1413Res3

end CFSG.RankThree.PartTwo.Sec14
