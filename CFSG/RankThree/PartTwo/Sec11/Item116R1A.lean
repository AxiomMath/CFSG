module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1Defs
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Comp
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Data
public import CFSG.RankThree.PartTwo.Sec11.TwoStarProofFitting

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type} [Group G] [Finite G]

theorem mk_ne_one_of_pow_three {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {x : H} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    (QuotientGroup.mk' N x : H ⧸ N) ≠ 1 := by
  intro h
  have hxN : x ∈ N := (QuotientGroup.eq_one_iff (N := N) x).mp h
  have hz3 : (⟨x, hxN⟩ : N) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hz3) with h1 | h1
  · exact hx1 (congrArg Subtype.val (orderOf_eq_one_iff.mp h1))
  · exact hN (by rw [← h1]; exact orderOf_dvd_natCard _)

theorem aPoint_J {A : Subgroup G} {a c d : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hAcl : Subgroup.closure ({c, d, a} : Set G) = A)
    {K₁ K₂ : Subgroup (QAt a)} (h1 : CFSG.IsComponent K₁) (h2 : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂)
    (hZ1 : Subgroup.center K₁ = ⊥) (hZ2 : Subgroup.center K₂ = ⊥)
    (hdK : ∀ x : CAt a, (x : G) = d →
      (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) x : QAt a) ∈ K₁)
    (hcK : ∀ x : CAt a, (x : G) = c →
      (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) x : QAt a) ∈ K₂)
    (hd1 : d ≠ 1) (hc1 : c ≠ 1) :
    ∀ y ∈ A, y ∉ Subgroup.zpowers a →
      ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G)), A⁆ ≤
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
  intro y hyA hyZ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hAcomm, hAexp⟩ := hAe
  have hcomm : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (isMulCommutative_iff.mp hAcomm ⟨x, hx⟩ ⟨z, hz⟩)
  have hpow3 : ∀ x ∈ A, x ^ 3 = 1 := hAexp
  have ha : a ∈ A := by rw [← hAcl]; exact Subgroup.subset_closure (by simp)
  have hc : c ∈ A := by rw [← hAcl]; exact Subgroup.subset_closure (by simp)
  have hd : d ∈ A := by rw [← hAcl]; exact Subgroup.subset_closure (by simp)
  have hcdA : ({c, d} : Set G) ⊆ A := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · rw [h]; exact hc
    · rw [h]; exact hd
  have hAC : ∀ x ∈ A, x ∈ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx a ha)
  obtain ⟨c', hc'⟩ : ∃ x : CAt a, (x : G) = c := ⟨⟨c, hAC c hc⟩, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ x : CAt a, (x : G) = d := ⟨⟨d, hAC d hd⟩, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ x : CAt a, (x : G) = a := ⟨⟨a, hAC a ha⟩, rfl⟩
  have key3 : ∀ x : CAt a, (x : G) ^ 3 = 1 → x ^ 3 = 1 := fun x hx =>
    Subtype.ext (by simpa using hx)
  have hc'1 : c' ≠ 1 := fun h => hc1 (by rw [← hc', h, Subgroup.coe_one])
  have hd'1 : d' ≠ 1 := fun h => hd1 (by rw [← hd', h, Subgroup.coe_one])
  have hc'3 : c' ^ 3 = 1 := key3 c' (by rw [hc']; exact hpow3 c hc)
  have hd'3 : d' ^ 3 = 1 := key3 d' (by rw [hd']; exact hpow3 d hd)
  have h3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 (CAt a)) :=
    (solvable_prime_complement_core_characterization (H := CAt a) Nat.prime_three).2.2.1
  have hqc3 : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) c' : QAt a) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hc'3, map_one])
      (mk_ne_one_of_pow_three (aschbacherSolvableCore 3 (CAt a)) h3 hc'3 hc'1)
  have hqd3 : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) d' : QAt a) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hd'3, map_one])
      (mk_ne_one_of_pow_three (aschbacherSolvableCore 3 (CAt a)) h3 hd'3 hd'1)
  obtain ⟨i, b, hbcl, hyb⟩ := exists_pow_mul_mem_closure_pair hcomm hAcl hyA
  subst hyb
  have hb1 : b ≠ 1 := by
    intro h
    apply hyZ
    rw [h, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i
  have hbA : b ∈ A := by
    have hcl : Subgroup.closure ({c, d} : Set G) ≤ A := by
      rw [Subgroup.closure_le]; exact hcdA
    exact hcl hbcl
  have hb3 : b ^ 3 = 1 := hpow3 b hbA
  have hmapcd : (Subgroup.closure ({c', d'} : Set (CAt a))).map
      (Subgroup.centralizer ({a} : Set G)).subtype = Subgroup.closure ({c, d} : Set G) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, hc', hd']
  obtain ⟨b', hb'cl, hb'⟩ : ∃ x ∈ Subgroup.closure ({c', d'} : Set (CAt a)), (x : G) = b := by
    have hmem : b ∈ (Subgroup.closure ({c', d'} : Set (CAt a))).map
        (Subgroup.centralizer ({a} : Set G)).subtype := by
      rw [hmapcd]; exact hbcl
    obtain ⟨x, hx, hxb⟩ := Subgroup.mem_map.mp hmem
    exact ⟨x, hx, hxb⟩
  have hb'3 : b' ^ 3 = 1 := key3 b' (by rw [hb']; exact hb3)
  have hb'1 : b' ≠ 1 := fun h => hb1 (by rw [← hb', h, Subgroup.coe_one])
  have hqb_ne : (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) b' : QAt a) ≠ 1 :=
    mk_ne_one_of_pow_three (aschbacherSolvableCore 3 (CAt a)) h3 hb'3 hb'1
  have hqb_cl : (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) b' : QAt a) ∈
      Subgroup.closure ({(QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) c' : QAt a),
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) d' : QAt a)} : Set (QAt a)) := by
    have hmem :=
      Subgroup.mem_map_of_mem (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) hb'cl
    rw [MonoidHom.map_closure] at hmem
    simpa [Set.image_insert_eq] using hmem
  have hsub := pCore_two_centralizer_le_pair (X := QAt a) h1 h2 hne hZ1 hZ2
    (hdK d' hd') (hcK c' hc') hqd3 hqc3 hqb_cl hqb_ne
  have hpc : ∀ p ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b'} : Set (CAt a))),
      (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) p : QAt a) ∈
        Subgroup.centralizer ({(QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) c' : QAt a)} :
          Set (QAt a)) ⊓
        Subgroup.centralizer ({(QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) d' : QAt a)} :
          Set (QAt a)) := by
    intro p hp
    exact hsub (map_pCore_two_centralizer_le (aschbacherSolvableCore 3 (CAt a)) h3 hb'3
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) hp))
  have hcenq : ∀ p : CAt a,
      (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) a' : QAt a) *
        QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) p =
      QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) p *
        QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) a' := by
    intro p
    have hcen : a' * p = p * a' := by
      apply Subtype.ext
      have hh : (p : G) * a = a * (p : G) := Subgroup.mem_centralizer_singleton_iff.mp p.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ha']
      exact hh.symm
    have := congrArg (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) hcen
    simpa only [map_mul] using this
  have hAmap : (Subgroup.closure ({c', d', a'} : Set (CAt a))).map
      (Subgroup.centralizer ({a} : Set G)).subtype = A := by
    rw [MonoidHom.map_closure, ← hAcl]
    congr 1
    simp [Set.image_insert_eq, hc', hd', ha']
  have hαZ : ∀ α ∈ A, ∃ z ∈ Subgroup.closure ({c', d', a'} : Set (CAt a)), (z : G) = α := by
    intro α hα
    rw [← hAmap] at hα
    obtain ⟨z, hz, hzα⟩ := Subgroup.mem_map.mp hα
    exact ⟨z, hz, hzα⟩
  have hCy : Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({a ^ i * b} : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine and_congr_right fun hx1 => ?_
    have hxai : x * a ^ i = a ^ i * x := (Commute.pow_right (show Commute x a from hx1) i).eq
    rw [← mul_assoc, hxai, mul_assoc, mul_assoc, mul_right_inj]
  have hPy := inSubgroup_pCore_centralizer_inf a b'
  rw [hb'] at hPy
  rw [hCy, hPy, Subgroup.commutator_le]
  intro x hx α hα
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨z, hz, rfl⟩ := hαZ α hα
  have hZp : Subgroup.closure ({c', d', a'} : Set (CAt a)) ≤
      (Subgroup.centralizer ({QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) p} :
        Set (QAt a))).comap (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    rcases hx with h | h | h
    · rw [h]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hpc p hp)).1).symm
    · rw [h]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hpc p hp)).2).symm
    · rw [h]
      exact hcenq p
  have hzZ := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp (hZp hz))
  have hcommθ : p * z * p⁻¹ * z⁻¹ ∈ aschbacherSolvableCore 3 (CAt a) := by
    have h0 : (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) (p * z * p⁻¹ * z⁻¹) :
        QAt a) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hzZ]
      simp [mul_assoc]
    exact (QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 (CAt a))
      (p * z * p⁻¹ * z⁻¹)).mp h0
  unfold inSubgroup
  refine Subgroup.mem_map.mpr ⟨p * z * p⁻¹ * z⁻¹, hcommθ, ?_⟩
  simp [commutatorElement_def]

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type} [Group G] [Finite G]

theorem aPoint_T {A : Subgroup G} {a c d : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hAcl : Subgroup.closure ({c, d, a} : Set G) = A)
    {K₁ K₂ : Subgroup (QAt a)} (h1 : CFSG.IsComponent K₁) (h2 : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂)
    (hZ1 : Subgroup.center K₁ = ⊥) (hZ2 : Subgroup.center K₂ = ⊥)
    (hdK : ∀ x : CAt a, (x : G) = d →
      (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) x : QAt a) ∈ K₁)
    (hcK : ∀ x : CAt a, (x : G) = c →
      (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) x : QAt a) ∈ K₂)
    (hd1 : d ≠ 1) (hc1 : c ≠ 1) (hca : c ∉ Subgroup.zpowers a) (hda : d ∉ Subgroup.zpowers a) :
    ∀ u : G, (∀ y ∈ A, y ∉ Subgroup.zpowers a →
        u ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G))) →
      u ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro u hu
  have hcA : c ∈ A := by rw [← hAcl]; exact Subgroup.subset_closure (by simp)
  have hdA : d ∈ A := by rw [← hAcl]; exact Subgroup.subset_closure (by simp)
  have haA : a ∈ A := by rw [← hAcl]; exact Subgroup.subset_closure (by simp)
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    CFSG.Open.IsElemAbelian.comm hAe hx hy
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hcC : c ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c hcA a haA)
  have hdC : d ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm d hdA a haA)
  obtain ⟨c', hc'⟩ : ∃ x : CAt a, (x : G) = c := ⟨⟨c, hcC⟩, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ x : CAt a, (x : G) = d := ⟨⟨d, hdC⟩, rfl⟩
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simp [hc', hexp c hcA])
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simp [hd', hexp d hdA])
  have hc'1 : c' ≠ 1 := by
    rintro rfl
    exact hc1 (by simpa using hc'.symm)
  have hd'1 : d' ≠ 1 := by
    rintro rfl
    exact hd1 (by simpa using hd'.symm)
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 (CAt a)) :=
    (solvable_prime_complement_core_characterization (H := CAt a) Nat.prime_three).2.2.1
  have hnot : ∀ x : CAt a, x ^ 3 = 1 → x ≠ 1 → x ∉ aschbacherSolvableCore 3 (CAt a) := by
    intro x hx3 hx1 hxθ
    have hdvd := orderOf_dvd_natCard (⟨x, hxθ⟩ : aschbacherSolvableCore 3 (CAt a))
    rw [Subgroup.orderOf_mk, orderOf_eq_prime hx3 hx1] at hdvd
    exact hθ3 hdvd
  have hπc3 : (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) c' : QAt a) ^ 3 = 1 := by
    rw [← map_pow, hc'3, map_one]
  have hπd3 : (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) d' : QAt a) ^ 3 = 1 := by
    rw [← map_pow, hd'3, map_one]
  have hπc1 : (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) c' : QAt a) ≠ 1 := fun h =>
    hnot c' hc'3 hc'1 ((QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 (CAt a)) c').mp h)
  have hπd1 : (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) d' : QAt a) ≠ 1 := fun h =>
    hnot d' hd'3 hd'1 ((QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 (CAt a)) d').mp h)
  have hordc : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) c' : QAt a) = 3 :=
    orderOf_eq_prime hπc3 hπc1
  have hordd : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) d' : QAt a) = 3 :=
    orderOf_eq_prime hπd3 hπd1
  have hu_c : u ∈ (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c'} : Set (CAt a)))).map
      (Subgroup.centralizer ({a} : Set G)).subtype := by
    rw [← inSubgroup_pCore_centralizer_inf a c', hc']
    exact hu c hcA hca
  have hu_d : u ∈ (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({d'} : Set (CAt a)))).map
      (Subgroup.centralizer ({a} : Set G)).subtype := by
    rw [← inSubgroup_pCore_centralizer_inf a d', hd']
    exact hu d hdA hda
  obtain ⟨u_c, hu_c_mem, hu_c_eq⟩ := Subgroup.mem_map.mp hu_c
  obtain ⟨u_d, hu_d_mem, hu_d_eq⟩ := Subgroup.mem_map.mp hu_d
  have huu : u_d = u_c := Subtype.ext (hu_d_eq.trans hu_c_eq.symm)
  rw [huu] at hu_d_mem
  have hπu_c := map_pCore_two_centralizer_le (aschbacherSolvableCore 3 (CAt a)) hθ3 hc'3
    (Subgroup.mem_map_of_mem (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) hu_c_mem)
  have hπu_d := map_pCore_two_centralizer_le (aschbacherSolvableCore 3 (CAt a)) hθ3 hd'3
    (Subgroup.mem_map_of_mem (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) hu_d_mem)
  have hθQ : aschbacherSolvableCore 3 (QAt a) = ⊥ :=
    aschbacherSolvableCore_quotient_eq_bot (CAt a)
  have hinf := pCore_two_centralizers_inf_eq_bot hθQ h1 h2 hne hZ1 hZ2
    (hdK d' hd') (hcK c' hc') hordd hordc
  have hone : (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) u_c : QAt a) ∈
      (⊥ : Subgroup (QAt a)) := by
    rw [← hinf]
    exact Subgroup.mem_inf.mpr ⟨hπu_c, hπu_d⟩
  rw [Subgroup.mem_bot] at hone
  have hu_c_θ : u_c ∈ aschbacherSolvableCore 3 (CAt a) :=
    (QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 (CAt a)) u_c).mp hone
  unfold inSubgroup
  exact Subgroup.mem_map.mpr ⟨u_c, hu_c_θ, hu_c_eq⟩

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.RankThree.GroupTheory

namespace CFSG.RankThree.PartTwo.Sec11

section Certified


theorem twoStarAtA_of (hP2b : Item116P2b) (hP2c : Item116P2c) (h45 : Sec4.Item4_5) :
    ResidueR1TwoStarA := by
  intro G _ _ A c L a R Y d h hT hR1 _ hKF
  obtain ⟨-, hD8, n, hnW, hnc, hnd, hna⟩ := hR1
  obtain ⟨K₁, K₂, h1, h2, hne, hZ1, hZ2, hdK, hcK, -, -⟩ :=
    aComponentData hP2b hP2c h45 h hT hD8 hnW hnc hnd hna
  have hs := h.toSec11Std hT
  have hAe := h.mem_partTwoF.1
  have hEA : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hAe
  have h27 : Nat.card A = 3 ^ 3 := by rw [h.card_eq]; norm_num
  have hdA := h.d_mem
  have hd1 : d ≠ 1 := fun h1 => h.not_mem_zpowers (h1 ▸ Subgroup.one_mem _)
  have hcd9 := SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three h27 h.mem_A h.ne_one hdA
    h.not_mem_zpowers
  have hclle : ∀ H : Subgroup G, c ∈ H → d ∈ H → a ∈ H → A ≤ H := by
    intro H hc hd ha
    rw [← h.closure_eq, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hc
    · exact hd
    · exact ha
  have haV : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    intro ha
    have hle := hclle (Subgroup.zpowers c ⊔ Subgroup.zpowers d)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)) ha
    have := Subgroup.card_le_of_le hle
    rw [h.card_eq, hcd9] at this
    norm_num at this
  have hc3 : c ^ 3 = 1 := hAe.2 c h.mem_A
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have ha3 : a ^ 3 = 1 := hAe.2 a h.a_mem
  have hda : d ∉ Subgroup.zpowers a := by
    intro hd
    apply haV
    have heq := TheoremO.zpowers_eq_of_mem_of_ne_one ha3 hd hd1
    exact Subgroup.mem_sup_right (by rw [heq]; exact Subgroup.mem_zpowers a)
  have hca : c ∉ Subgroup.zpowers a := by
    intro hc
    apply haV
    have heq := TheoremO.zpowers_eq_of_mem_of_ne_one ha3 hc h.ne_one
    exact Subgroup.mem_sup_left (by rw [heq]; exact Subgroup.mem_zpowers a)
  have hVA : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr h.mem_A) (Subgroup.zpowers_le.mpr hdA)
  have hdK' : d ∈ sec11K L a := TheoremO.mem_sec11K_d h45 hs h.inf_eq_zpowers h.not_mem_zpowers
  refine TwoStarProof.twoStarConditionAt_of_theta hAe h.card_eq h.a_mem h.a_ne_one
    (V := Subgroup.zpowers c ⊔ Subgroup.zpowers d) (by rw [hcd9]; norm_num) hVA haV hdA hda ?_
    (aPoint_J hAe h.closure_eq h1 h2 hne hZ1 hZ2 hdK hcK hd1 h.ne_one)
    (aPoint_T hAe h.closure_eq h1 h2 hne hZ1 hZ2 hdK hcK hd1 h.ne_one hca hda)
  · intro v hv
    have := hKF (Subgroup.commutator_mem_commutator hdK' hv)
    rwa [commutatorElement_def] at this

end Certified

end CFSG.RankThree.PartTwo.Sec11
