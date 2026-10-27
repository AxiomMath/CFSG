module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec46Sp4qBasic

import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open scoped commutatorElement Pointwise

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem card_sup_mul_card_inf_of_le_finite {P H K : Subgroup G} [Finite ↥P] (hHP : H ≤ P)
    (hKP : K ≤ P) (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have hN : H.subgroupOf P ≤ Subgroup.normalizer ((K.subgroupOf P : Subgroup ↥P) : Set ↥P) := by
    intro x hx
    refine Subgroup.mem_normalizer_iff.mpr (fun y => ?_)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rw [show ((x * y * x⁻¹ : ↥P) : G) = (x : G) * (y : G) * (x : G)⁻¹ from rfl]
    exact Subgroup.mem_normalizer_iff.mp (hHK (Subgroup.mem_subgroupOf.mp hx)) (y : G)
  have h := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq hN
  have e1 : K.subgroupOf P ⊔ H.subgroupOf P = (H ⊔ K).subgroupOf P := by
    rw [sup_comm, Subgroup.subgroupOf_sup hHP hKP]
  have e2 : K.subgroupOf P ⊓ H.subgroupOf P = (H ⊓ K).subgroupOf P := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    exact and_comm
  rw [e1, e2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hHP hKP)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hHP)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHP).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv] at h
  rw [h, mul_comm]

namespace Setup

variable {X : Setup Γ G}

theorem Q_le_normalizer_Z (X : Setup Γ G) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    X.Q (1 - i) ≤ Subgroup.normalizer (X.Z i : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hgS : g ∈ X.S := X.Q_le_S (by rcases hi with rfl | rfl <;> simp) hg
  exact X.Z_normal i g ((X.isSylowTwoOf_S_Gi hi).1 hgS)

theorem CaseBGen.mem_mul_of_mem_S (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) {x : G}
    (hx : x ∈ X.S) : ∃ z ∈ X.Z i, ∃ a ∈ X.Q (1 - i), x = z * a := by
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (X.Q (1 - i)) (X.Z i)
    (X.Q_le_normalizer_Z hi)
  have hx' : x ∈ ((X.Q (1 - i) ⊔ X.Z i : Subgroup G) : Set G) := by
    rw [sup_comm, B.Z_sup_Q hi]
    exact hx
  rw [hcoe] at hx'
  obtain ⟨a, ha, z, hz, rfl⟩ := hx'
  refine ⟨a * z * a⁻¹, ?_, a, ha, by group⟩
  have h := (Subgroup.mem_normalizer_iff.mp (X.Q_le_normalizer_Z hi ha) z).mp hz
  exact h

theorem CaseBGen.commutator_mem_Z (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) {x y : G}
    (hx : x ∈ X.Q i) (hy : y ∈ X.Z (1 - i)) : ⁅x, y⁆ ∈ X.Z i := by
  obtain ⟨z, hz, a, ha, rfl⟩ := B.mem_mul_of_mem_S hi (X.Q_le_S hi hx)
  have hay : a * y = y * a :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center (1 - i) hy)).2 a ha
  have he : ⁅z * a, y⁆ = ⁅z, y⁆ := by
    rw [commutatorElement_def, commutatorElement_def,
      show z * a * y * (z * a)⁻¹ * y⁻¹ = z * (a * y) * a⁻¹ * z⁻¹ * y⁻¹ by group, hay]
    group
  rw [he]
  have hR : ⁅z, y⁆ ∈ ⁅X.Z 0, X.Z 1⁆ := by
    rcases hi with rfl | rfl
    · exact Subgroup.commutator_mem_commutator hz hy
    · rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hz hy
  rcases hi with rfl | rfl
  · exact (B.R_le hR).1
  · exact (B.R_le hR).2

theorem Gi_le_normalizer_L_Q_Z (X : Setup Γ G) (i : ℤ) :
    X.Gi i ≤ Subgroup.normalizer (X.L i : Set G) ∧ X.Gi i ≤ Subgroup.normalizer (X.Q i : Set G) ∧
      X.Gi i ≤ Subgroup.normalizer (X.Z i : Set G) := by
  refine ⟨le_normalizer_oTwoPrime (X.Gi i),
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i), fun g hg => ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact X.Z_normal i g hg

theorem CaseBGen.odd_conj_mem (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) {k : G}
    (hk : k ∈ X.L i) (hodd : Odd (orderOf k)) {x : G} (hx : x ∈ X.Q i) :
    x⁻¹ * (k * x * k⁻¹) ∈ X.Z i := by
  classical
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  haveI : Finite ↥(X.L i) := finite_of_le_stabilizer X.hyp (H := X.L i) (X.L_le_Gi i)
  obtain ⟨hNL, hNQ, hNZ⟩ := X.Gi_le_normalizer_L_Q_Z i
  have hLZ : X.L i ≤ Subgroup.normalizer (X.Z i : Set G) := (X.L_le_Gi i).trans hNZ
  have hLQ : X.L i ≤ Subgroup.normalizer (X.Q i : Set G) := (X.L_le_Gi i).trans hNQ
  set C : Subgroup G := relCent (X.L i) (X.Z i) (X.Q i) with hCdef
  have hmemC : ∀ g, g ∈ C ↔ g ∈ X.L i ∧ ∀ a ∈ X.Q i, ⁅g, a⁆ ∈ X.Z i := fun g =>
    mem_relCent hLZ
  have hCL : C ≤ X.L i := fun g hg => ((hmemC g).mp hg).1
  have hZC : X.Z (1 - i) ≤ C := by
    intro y hy
    refine (hmemC y).mpr ⟨B.Z_le_L hi hy, fun a ha => ?_⟩
    have h := (X.Z i).inv_mem (B.commutator_mem_Z hi ha hy)
    rwa [commutatorElement_inv] at h
  have hGC : X.Gi i ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h := conjSub_relCent g (A := X.Q i) hLZ
    have hL : conjSub g (X.L i) = X.L i := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNL hg)
    have hQ : conjSub g (X.Q i) = X.Q i := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNQ hg)
    have hZ : conjSub g (X.Z i) = X.Z i := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNZ hg)
    rw [hL, hQ, hZ] at h
    exact h
  have hY : X.L i ≤ C ⊔ X.Q i := by
    have hYG : C ⊔ X.Q i ≤ X.Gi i := sup_le (hCL.trans (X.L_le_Gi i)) (X.Q_le_Gi i)
    have hGY : X.Gi i ≤ Subgroup.normalizer ((C ⊔ X.Q i : Subgroup G) : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hGC hg),
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNQ hg)]
    have hSY : X.S ≤ C ⊔ X.Q i := by
      have h := B.Z_sup_Q (i := 1 - i) (by rcases hi with rfl | rfl <;> simp)
      rw [sub_sub_cancel] at h
      rw [← h]
      exact sup_le_sup_right hZC _
    have hSyl := X.isSylowTwoOf_S_Gi hi
    refine oTwoPrime_le_of_odd_relIndex hYG
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hYG).mpr hGY) fun h2 => hSyl.2.2 ?_
    exact h2.trans (Subgroup.relIndex_dvd_of_le_left (X.Gi i) hSY)
  have hkC : k ∈ C := by
    set C' : Subgroup ↥(X.L i) := C.subgroupOf (X.L i) with hC'
    haveI : C'.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCL).mpr ((X.L_le_Gi i).trans hGC)
    let q : ↥(X.L i) →* ↥(X.L i) ⧸ C' := QuotientGroup.mk' C'
    have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right C (X.Q i) (hCL.trans hLQ)
    have hkY : k ∈ ((C ⊔ X.Q i : Subgroup G) : Set G) := hY hk
    rw [hcoe] at hkY
    obtain ⟨c, hc, y, hy, hcy⟩ := hkY
    have hyL : y ∈ X.L i := X.Q_le_L i hy
    have hqk : q ⟨k, hk⟩ = q ⟨y, hyL⟩ := by
      have hck : (⟨k, hk⟩ : ↥(X.L i)) = ⟨c, hCL hc⟩ * ⟨y, hyL⟩ := Subtype.ext hcy.symm
      have hqc : q ⟨c, hCL hc⟩ = 1 := by
        simp only [q, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hc
      rw [hck, map_mul, hqc, one_mul]
    obtain ⟨e, he⟩ := (pCoreOf_isPGroup' (X.Gi i)) ⟨y, hy⟩
    have hy2 : (q ⟨y, hyL⟩) ^ 2 ^ e = 1 := by
      rw [← map_pow]
      have : (⟨y, hyL⟩ : ↥(X.L i)) ^ 2 ^ e = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val he
        simpa using this
      rw [this, map_one]
    have hdvd1 : orderOf (q ⟨k, hk⟩) ∣ 2 ^ e := by
      rw [hqk]
      exact orderOf_dvd_of_pow_eq_one hy2
    have hdvd2 : orderOf (q ⟨k, hk⟩) ∣ orderOf k := by
      refine (orderOf_map_dvd q _).trans ?_
      rw [Subgroup.orderOf_mk]
    have hone : orderOf (q ⟨k, hk⟩) = 1 := by
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd1
      rcases m with _ | m
      · simpa using hm
      · exfalso
        have h2 : 2 ∣ orderOf k :=
          (dvd_pow_self 2 (Nat.succ_ne_zero m)).trans (hm ▸ hdvd2)
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    have hq1 : q ⟨k, hk⟩ = 1 := orderOf_eq_one_iff.mp hone
    simp only [q, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq1
    exact Subgroup.mem_subgroupOf.mp hq1
  have hkx : ⁅k, x⁆ ∈ X.Z i := ((hmemC k).mp hkC).2 x hx
  have he : x⁻¹ * (k * x * k⁻¹) = x⁻¹ * ⁅k, x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [he]
  have h := (Subgroup.mem_normalizer_iff.mp (hNZ (X.Q_le_Gi i (inv_mem hx))) ⁅k, x⁆).mp hkx
  simpa using h

private theorem s46sp4q_solvable (X : Setup Γ G) (i : ℤ) {A : Subgroup G} (hA : A ≤ X.Q i) :
    Group.IsSolvable ↥(A.subgroupOf (X.Gi i)) := by
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  have hAG : A ≤ X.Gi i := hA.trans (X.Q_le_Gi i)
  have hp : IsPGroup 2 ↥(A.subgroupOf (X.Gi i)) :=
    ((pCoreOf_isPGroup' (X.Gi i)).to_le hA).of_equiv (Subgroup.subgroupOfEquivOfLe hAG).symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hp.isNilpotent
  infer_instance

private theorem s46sp4q_coprime (X : Setup Γ G) (i : ℤ) {A K' : Subgroup G} (hA : A ≤ X.Q i)
    (hK' : Odd (Nat.card K')) : (Nat.card K').Coprime (Nat.card A) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(X.Q i) := finite_of_le_stabilizer X.hyp (H := X.Q i) (X.Q_le_Gi i)
  haveI : Finite ↥A := Finite.of_injective (Subgroup.inclusion hA) (Subgroup.inclusion_injective hA)
  obtain ⟨m, hm⟩ := ((pCoreOf_isPGroup' (X.Gi i)).to_le hA).exists_card_eq
  rw [hm]
  have h2 : Nat.Coprime 2 (Nat.card K') := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
    fun h => (Nat.not_even_iff_odd.mpr hK') (even_iff_two_dvd.mpr h)
  exact Nat.Coprime.pow_right m h2.symm

private theorem s46sp4q_odd_orderOf {K' : Subgroup G} (hK' : Odd (Nat.card K')) {k : G}
    (hk : k ∈ K') : Odd (orderOf k) :=
  Odd.of_dvd_nat hK' (Subgroup.orderOf_dvd_natCard K' hk)

theorem CaseBGen.exists_mul_of_odd (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1)
    {K' : Subgroup G} (hK'L : K' ≤ X.L i) (hK' : Odd (Nat.card K')) {x : G} (hx : x ∈ X.Q i) :
    ∃ c ∈ X.Q i ⊓ Subgroup.centralizer (K' : Set G), ∃ z ∈ X.Z i, x = c * z := by
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  obtain ⟨-, hNQ, hNZ⟩ := X.Gi_le_normalizer_L_Q_Z i
  exact exists_mem_inf_centralizer_mul_of_finite (X.Q_le_Gi i) (X.Z_le_Q i)
    (hK'L.trans (X.L_le_Gi i)) hNQ hNZ (s46sp4q_solvable X i le_rfl)
    (s46sp4q_coprime X i le_rfl hK')
    (fun k hk q hq => B.odd_conj_mem hi (hK'L hk) (s46sp4q_odd_orderOf hK' hk) hq) hx

theorem CaseBGen.inf_centralizer_eq (B : X.CaseBGen) {i : ℤ}
    (hnat : NatQuot (X.L i) (X.Z i) (centerOf (X.L i)) (X.n i)) {K' : Subgroup G}
    (hK'L : K' ≤ X.L i) (hK' : Odd (Nat.card K')) (hne : K' ≠ ⊥) :
    X.Z i ⊓ Subgroup.centralizer (K' : Set G) = centerOf (X.L i) := by
  refine le_antisymm ?_ (le_inf (X.centerOf_L_le_Z B.char i) ?_)
  · intro z hz
    obtain ⟨hzZ, hzC⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hkodd := s46sp4q_odd_orderOf hK' k.2
    have hkZ : (k : G) ∉ X.Z i := by
      intro hkZ
      obtain ⟨e, he⟩ := (pCoreOf_isPGroup' (X.Gi i)) ⟨k, X.Z_le_Q i hkZ⟩
      have h2 : orderOf (k : G) ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one
        (by simpa using congrArg Subtype.val he)
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
      rcases m with _ | m
      · exact hk1 (Subtype.ext (orderOf_eq_one_iff.mp (by simpa using hm)))
      · exact (Nat.not_even_iff_odd.mpr hkodd)
          (even_iff_two_dvd.mpr (hm ▸ dvd_pow_self 2 (Nat.succ_ne_zero m)))
    refine hnat.fpf k (hK'L k.2) hkodd hkZ z hzZ ?_
    have hc : z * k = k * z := Subgroup.mem_centralizer_iff.mp hzC k k.2 |>.symm
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
    exact one_mem _
  · intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 k (hK'L hk))

theorem CaseBGen.card_Z (B : X.CaseBGen) {i : ℤ}
    (hnat : NatQuot (X.L i) (X.Z i) (centerOf (X.L i)) (X.n i)) :
    Nat.card (X.Z i) = 2 ^ (2 * X.n i) * Nat.card (centerOf (X.L i)) := by
  have h := Subgroup.relIndex_mul_card (H := centerOf (X.L i)) (K := X.Z i)
  rw [inf_eq_left.mpr (X.centerOf_L_le_Z B.char i), hnat.index] at h
  exact h.symm

private theorem s46sp4q_card_center_pos (X : Setup Γ G) (i : ℤ) :
    0 < Nat.card (centerOf (X.L i)) := by
  haveI : Finite ↥(centerOf (X.L i)) :=
    finite_of_le_stabilizer X.hyp (H := centerOf (X.L i)) (inf_le_left.trans (X.L_le_Gi i))
  exact Nat.card_pos

theorem CaseBGen.card_cent (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) (hn : X.n 0 = X.n 1)
    (hnat : NatQuot (X.L i) (X.Z i) (centerOf (X.L i)) (X.n i)) {K' : Subgroup G}
    (hK'L : K' ≤ X.L i) (hK' : Odd (Nat.card K')) (hne : K' ≠ ⊥) :
    Nat.card ↥(X.Q i ⊓ Subgroup.centralizer (K' : Set G)) = 2 ^ X.n i := by
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  obtain ⟨-, -, hNZ⟩ := X.Gi_le_normalizer_L_Q_Z i
  set D := X.Q i ⊓ Subgroup.centralizer (K' : Set G) with hD
  have hDG : D ≤ X.Gi i := inf_le_left.trans (X.Q_le_Gi i)
  have hsup : D ⊔ X.Z i = X.Q i := by
    refine le_antisymm (sup_le inf_le_left (X.Z_le_Q i)) fun x hx => ?_
    obtain ⟨c, hc, z, hz, rfl⟩ := B.exists_mul_of_odd hi hK'L hK' hx
    exact mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hz)
  have hinf : D ⊓ X.Z i = centerOf (X.L i) := by
    rw [← B.inf_centralizer_eq hnat hK'L hK' hne]
    ext x
    simp only [hD, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨-, hc⟩, hz⟩
      exact ⟨hz, hc⟩
    · rintro ⟨hz, hc⟩
      exact ⟨⟨X.Z_le_Q i hz, hc⟩, hz⟩
  have hprod := card_sup_mul_card_inf_of_le_finite hDG (X.Z_le_Gi i) (hDG.trans hNZ)
  rw [hsup, hinf, B.card_Q hi, B.card_Z hnat] at hprod
  have hnj : X.n (1 - i) = X.n i := by rcases hi with rfl | rfl <;> simp [hn]
  rw [hnj, show X.n i + 2 * X.n i = X.n i + 2 * X.n i from rfl, pow_add,
    mul_assoc] at hprod
  exact (Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (by positivity) (s46sp4q_card_center_pos X i)) hprod).symm

private theorem s46sp4q_le_normalizer_inf {H A B : Subgroup G}
    (hA : H ≤ Subgroup.normalizer (A : Set G)) (hB : H ≤ Subgroup.normalizer (B : Set G)) :
    H ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.mp (hA hg) x)
    (Subgroup.mem_normalizer_iff.mp (hB hg) x)

theorem CaseBGen.cent_le_Q (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) (hn : X.n 0 = X.n 1)
    (hnat : NatQuot (X.L i) (X.Z i) (centerOf (X.L i)) (X.n i))
    (hinf : X.Z i ⊓ X.Q (1 - i) = relCent (X.Z i) (centerOf (X.L i)) X.S) {K' : Subgroup G}
    (hK'L : K' ≤ X.L i) (hK'G : K' ≤ X.Gi (1 - i)) (hK' : Odd (Nat.card K')) (hne : K' ≠ ⊥) :
    X.Q i ⊓ Subgroup.centralizer (K' : Set G) ≤ X.Q (1 - i) := by
  have hj : 1 - i = 0 ∨ 1 - i = 1 := by rcases hi with rfl | rfl <;> simp
  have hcenQj : centerOf (X.L i) ≤ X.Q (1 - i) := by
    rcases hi with rfl | rfl
    · simpa using (X.centerOf_L_le_Q_adj B.char 0).2
    · simpa using (X.centerOf_L_le_Q_adj B.char 0).1
  set j := 1 - i with hjdef
  set H := X.Gi i ⊓ X.Gi j with hH
  haveI : Finite ↥H := finite_of_le_stabilizer X.hyp (H := H) inf_le_left
  obtain ⟨-, hNQi, hNZi⟩ := X.Gi_le_normalizer_L_Q_Z i
  obtain ⟨-, hNQj, -⟩ := X.Gi_le_normalizer_L_Q_Z j
  have hQiS := X.Q_le_S hi
  have hQjS := X.Q_le_S hj
  have hSH : X.S ≤ H := le_inf (X.isSylowTwoOf_S_Gi hi).1 (X.isSylowTwoOf_S_Gi hj).1
  have hQiH : X.Q i ≤ H := hQiS.trans hSH
  have hQjH : X.Q j ≤ H := hQjS.trans hSH
  have hHQi : H ≤ Subgroup.normalizer (X.Q i : Set G) := inf_le_left.trans hNQi
  have hHQj : H ≤ Subgroup.normalizer (X.Q j : Set G) := inf_le_right.trans hNQj
  have hHZi : H ≤ Subgroup.normalizer (X.Z i : Set G) := inf_le_left.trans hNZi
  set A := X.Q i ⊓ X.Q j with hA
  set N := X.Z i ⊓ X.Q j with hN
  set D := X.Q i ⊓ Subgroup.centralizer (K' : Set G) with hD
  have hAH : A ≤ H := inf_le_left.trans hQiH
  have hNA : N ≤ A := inf_le_inf_right _ (X.Z_le_Q i)
  have hK'H : K' ≤ H := le_inf (hK'L.trans (X.L_le_Gi i)) hK'G
  have hfac : ∀ a ∈ A, ∃ c ∈ A ⊓ Subgroup.centralizer (K' : Set G), ∃ m ∈ N, a = c * m := by
    intro a ha
    refine exists_mem_inf_centralizer_mul_of_finite hAH hNA hK'H
      (s46sp4q_le_normalizer_inf hHQi hHQj) (s46sp4q_le_normalizer_inf hHZi hHQj) ?_
      (s46sp4q_coprime X i inf_le_left hK') ?_ ha
    · have h := s46sp4q_solvable X i (A := A) inf_le_left
      have e : A.subgroupOf H ≃* A.subgroupOf (X.Gi i) :=
        (Subgroup.subgroupOfEquivOfLe hAH).trans
          (Subgroup.subgroupOfEquivOfLe (hAH.trans inf_le_left)).symm
      exact solvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · intro k hk q hq
      refine Subgroup.mem_inf.mpr ⟨B.odd_conj_mem hi (hK'L hk) (s46sp4q_odd_orderOf hK' hk)
        (Subgroup.mem_inf.mp hq).1, ?_⟩
      have hkq : k * q * k⁻¹ ∈ X.Q j :=
        (Subgroup.mem_normalizer_iff.mp (hNQj (hK'G hk)) q).mp (Subgroup.mem_inf.mp hq).2
      exact mul_mem (inv_mem (Subgroup.mem_inf.mp hq).2) hkq
  have hAsup : (A ⊓ Subgroup.centralizer (K' : Set G)) ⊔ N = A := by
    refine le_antisymm (sup_le inf_le_left hNA) fun a ha => ?_
    obtain ⟨c, hc, m, hm, rfl⟩ := hfac a ha
    exact mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hm)
  have hAinf : (A ⊓ Subgroup.centralizer (K' : Set G)) ⊓ N = centerOf (X.L i) := by
    rw [← B.inf_centralizer_eq hnat hK'L hK' hne]
    refine le_antisymm ?_ ?_
    · intro x hx
      simp only [hA, hN, Subgroup.mem_inf] at hx
      exact Subgroup.mem_inf.mpr ⟨hx.2.1, hx.1.2⟩
    · intro x hx
      have hx' : x ∈ centerOf (X.L i) := by rw [← B.inf_centralizer_eq hnat hK'L hK' hne]; exact hx
      obtain ⟨hxZ, hxC⟩ := Subgroup.mem_inf.mp hx
      have hxQj := hcenQj hx'
      simp only [hA, hN, Subgroup.mem_inf]
      exact ⟨⟨⟨X.Z_le_Q i hxZ, hxQj⟩, hxC⟩, hxZ, hxQj⟩
  have hn0 : X.n 0 = X.n i := by rcases hi with rfl | rfl <;> simp [hn]
  have hn1 : X.n 1 = X.n i := by rcases hi with rfl | rfl <;> simp [hn]
  have hnj : X.n j = X.n i := by rcases hj with h | h <;> rw [h] <;> simp [hn0, hn1]
  have hcardA : Nat.card ↥A = 2 ^ (2 * X.n i) := by
    have hSN : X.S ≤ Subgroup.normalizer (X.Q j : Set G) := (X.isSylowTwoOf_S_Gi hj).1.trans hNQj
    have h := card_sup_mul_card_inf_of_le_finite hQiH hQjH (hQiS.trans hSN)
    have hsup : X.Q i ⊔ X.Q j = X.S := by
      rcases hi with rfl | rfl
      · simpa [hjdef] using B.Q_sup_Q
      · simpa [hjdef, sup_comm] using B.Q_sup_Q
    have hQj := B.card_Q hj
    rw [show 1 - j = i by rw [hjdef]; ring, hnj] at hQj
    rw [hsup, B.card_S, B.card_Q hi, hQj, hn0, hn1, ← hjdef, hnj] at h
    have e : 2 ^ (X.n i + 2 * X.n i) * 2 ^ (X.n i + 2 * X.n i) =
        2 ^ (2 * X.n i + 2 * X.n i) * 2 ^ (2 * X.n i) := by
      rw [← pow_add, ← pow_add]
      ring_nf
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (h.trans e)
  have hcardN : Nat.card ↥N = 2 ^ X.n i * Nat.card (centerOf (X.L i)) := by
    rw [show N = relCent (X.Z i) (centerOf (X.L i)) X.S from hinf]
    have hle : centerOf (X.L i) ≤ relCent (X.Z i) (centerOf (X.L i)) X.S := by
      intro z hz
      refine ⟨X.centerOf_L_le_Z B.char i hz, Subgroup.le_normalizer hz, fun s hs => ?_⟩
      have hzs : s * z = z * s :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 s ((X.isSylowTwoOf_S_L hi).1 hs)
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hzs.symm]
      exact one_mem _
    have h := Subgroup.relIndex_mul_card (H := centerOf (X.L i))
      (K := relCent (X.Z i) (centerOf (X.L i)) X.S)
    rw [inf_eq_left.mpr hle, hnat.line X.S (X.isSylowTwoOf_S_L hi)] at h
    exact h.symm
  have hACH : A ⊓ Subgroup.centralizer (K' : Set G) ≤ H := inf_le_left.trans hAH
  have hNH : N ≤ H := hNA.trans hAH
  have hACN : A ⊓ Subgroup.centralizer (K' : Set G) ≤ Subgroup.normalizer (N : Set G) :=
    (inf_le_left.trans hAH).trans (s46sp4q_le_normalizer_inf hHZi hHQj)
  have hprod := card_sup_mul_card_inf_of_le_finite hACH hNH hACN
  rw [hAsup, hAinf, hcardA, hcardN] at hprod
  have hcardAC : Nat.card ↥(A ⊓ Subgroup.centralizer (K' : Set G)) = 2 ^ X.n i := by
    have e : 2 ^ (2 * X.n i) * Nat.card ↥(centerOf (X.L i)) =
        2 ^ X.n i * (2 ^ X.n i * Nat.card ↥(centerOf (X.L i))) := by
      rw [← mul_assoc, ← pow_add]
      ring_nf
    rw [e] at hprod
    exact (Nat.eq_of_mul_eq_mul_right
      (Nat.mul_pos (by positivity) (s46sp4q_card_center_pos X i)) hprod).symm
  have hAC : A ⊓ Subgroup.centralizer (K' : Set G) = D ⊓ X.Q j := by
    ext x
    simp only [hA, hD, Subgroup.mem_inf]
    tauto
  haveI : Finite ↥D :=
    finite_of_le_stabilizer X.hyp (H := D) (inf_le_left.trans (X.Q_le_Gi i))
  have heq : D ⊓ X.Q j = D := Subgroup.eq_of_le_of_card_ge inf_le_left (by
    rw [← hAC, hcardAC, B.card_cent hi hn hnat hK'L hK' hne])
  exact inf_eq_left.mp heq

end Setup

end CFSG.Quasithin.St84

end
