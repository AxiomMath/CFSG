module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofCyclic
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Comp
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Lift

public section

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

@[expose] def CyclicSylowThreeOutAbelian : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.IsKGroup J → IsSimpleGroup J →
    (∃ x y : J, x * y ≠ y * x) → (∀ P : Sylow 3 J, IsCyclic ↥(P : Subgroup J)) →
      ∀ σ τ : MulAut J, KFacts.IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹)

structure CDHyp {X : Type} [Group X] (Abar Bbar Rbar : Subgroup X) (cb db ab : X) : Prop where
  A_exp : ∀ x ∈ Abar, x ^ 3 = 1
  A_comm : ∀ x ∈ Abar, ∀ y ∈ Abar, x * y = y * x
  cb_mem : cb ∈ Abar
  db_mem : db ∈ Abar
  ab_mem : ab ∈ Abar
  A_gen : Subgroup.closure ({cb, db, ab} : Set X) = Abar
  B_def : Bbar = Subgroup.closure ({cb, db} : Set X)
  card_A : Nat.card Abar = 27
  card_B : Nat.card Bbar = 9
  z_ne : cb * db ≠ 1
  z_central : ∀ x : X, x * (cb * db) = (cb * db) * x
  R_pgroup : IsPGroup 3 Rbar
  A_le_R : Abar ≤ Rbar
  omega : ∀ x ∈ Rbar, x ^ 3 = 1 → x ∈ Abar
  R_centralizes_B : ∀ r ∈ Rbar, ∀ b ∈ Bbar, r * b * r⁻¹ = b
  transvection : ∀ u ∈ Abar, u ∉ Bbar → ∀ b ∈ Bbar, ∃ r ∈ Rbar, r * u * r⁻¹ = u * b
  C_cd : ∀ x : X, x * cb = cb * x → x * db = db * x
  C_dc : ∀ x : X, x * db = db * x → x * cb = cb * x


end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

section Pure

variable {X : Type} [Group X] [Finite X] {Abar Bbar Rbar : Subgroup X} {cb db ab : X}

theorem cd_step1 (H : CDHyp Abar Bbar Rbar cb db ab) {J : Subgroup X} (hJ : CFSG.IsComponent J)
    (hZ : Subgroup.center J = ⊥) {u : X} (huJ : u ∈ J) (huA : u ∈ Abar) : u ∈ Bbar := by
  by_contra huB
  have hzB : cb * db ∈ Bbar := by
    rw [H.B_def]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  obtain ⟨r, -, hr⟩ := H.transvection u huA huB (cb * db) hzB
  have hJ' : CFSG.IsComponent (J.map (MulAut.conj r).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj r) hJ
  have huz : u * (cb * db) ∈ J.map (MulAut.conj r).toMonoidHom := ⟨u, huJ, hr⟩
  rcases CFSG.LocalCores.distinct_components_commute hJ hJ' with hJJ | hcomm
  ·
    rw [← hJJ] at huz
    have hzJ : cb * db ∈ J := by
      have h := J.mul_mem (J.inv_mem huJ) huz
      rwa [inv_mul_cancel_left] at h
    have hzc : (⟨cb * db, hzJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      show (g : X) * (cb * db) = (cb * db) * (g : X)
      exact H.z_central (g : X)
    rw [hZ, Subgroup.mem_bot] at hzc
    exact H.z_ne (congrArg Subtype.val hzc)
  ·
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have huc : (⟨u, huJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      show (g : X) * u = u * (g : X)
      have hg := Subgroup.mem_centralizer_iff.mp (hle g.2) (u * (cb * db)) huz
      have key : u * (g : X) * (cb * db) = (g : X) * u * (cb * db) := by
        calc u * (g : X) * (cb * db) = u * ((g : X) * (cb * db)) := mul_assoc _ _ _
          _ = u * ((cb * db) * (g : X)) := by rw [H.z_central (g : X)]
          _ = u * (cb * db) * (g : X) := (mul_assoc _ _ _).symm
          _ = (g : X) * (u * (cb * db)) := hg
          _ = (g : X) * u * (cb * db) := (mul_assoc _ _ _).symm
      exact (mul_right_cancel key).symm
    rw [hZ, Subgroup.mem_bot] at huc
    have hu1 : u = 1 := congrArg Subtype.val huc
    exact huB (by rw [hu1]; exact Subgroup.one_mem _)

theorem cd_normalizes (H : CDHyp Abar Bbar Rbar cb db ab) {J : Subgroup X} (hJ : CFSG.IsComponent J)
    (hZ : Subgroup.center J = ⊥) {e : X} (heJ : e ∈ J) (he1 : e ≠ 1) (heB : e ∈ Bbar) :
    ∀ r ∈ Rbar, ∀ x ∈ J, r * x * r⁻¹ ∈ J := by
  intro r hr x hx
  have hJ' : CFSG.IsComponent (J.map (MulAut.conj r).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj r) hJ
  by_cases hJJ : J = J.map (MulAut.conj r).toMonoidHom
  · rw [hJJ]
    exact ⟨x, hx, rfl⟩
  ·
    have heJ' : e ∈ J.map (MulAut.conj r).toMonoidHom := by
      refine ⟨e, heJ, ?_⟩
      exact H.R_centralizes_B r hr e heB
    have he0 : e ∈ J ⊓ J.map (MulAut.conj r).toMonoidHom := Subgroup.mem_inf.mpr ⟨heJ, heJ'⟩
    rw [compJ3_inf_eq_bot hJ hJ' hJJ hZ, Subgroup.mem_bot] at he0
    exact absurd he0 he1

end Pure

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

section Pure

variable {X : Type} [Group X] [Finite X] {Abar Bbar Rbar : Subgroup X} {cb db ab : X}

theorem cd_cyclic (H : CDHyp Abar Bbar Rbar cb db ab) {J : Subgroup X} (hJ : CFSG.IsComponent J)
    (hZ : Subgroup.center J = ⊥) (hB : ∀ u ∈ J, u ∈ Abar → u ∈ Bbar) : IsCyclic ↥(Rbar ⊓ J) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzJ : cb * db ∉ J := by
    intro hmem
    have hmemC : (⟨cb * db, hmem⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact H.z_central g.1
    rw [hZ, Subgroup.mem_bot] at hmemC
    exact H.z_ne (congrArg Subtype.val hmemC)
  have hzB : cb * db ∈ Bbar := by
    rw [H.B_def]
    exact mul_mem (Subgroup.subset_closure (Set.mem_insert cb {db}))
      (Subgroup.subset_closure (Set.mem_insert_of_mem cb (Set.mem_singleton db)))
  have hlt : Bbar ⊓ J < Bbar := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    apply hzJ
    have hmem : cb * db ∈ Bbar ⊓ J := by
      rw [heq]
      exact hzB
    exact (Subgroup.mem_inf.mp hmem).2
  have hcardlt : Nat.card ↥(Bbar ⊓ J) < 9 := by
    have h := Subgroup.card_lt_of_lt hlt
    rw [H.card_B] at h
    exact h
  have hdvd : Nat.card ↥(Bbar ⊓ J) ∣ 9 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : Bbar ⊓ J ≤ Bbar)
    rw [H.card_B] at h
    exact h
  have key : ∀ n : ℕ, n < 9 → n ∣ 9 → n ≤ 3 := by decide
  have hle3 : Nat.card ↥(Bbar ⊓ J) ≤ 3 := key _ hcardlt hdvd
  have hmem : ∀ x : {x : ↥(Rbar ⊓ J) // x ^ 3 = 1}, (x.1 : X) ∈ Bbar ⊓ J := by
    intro x
    have hx3 : (x.1 : X) ^ 3 = 1 := by
      have h := congrArg Subtype.val x.2
      simpa using h
    obtain ⟨hR, hJx⟩ := Subgroup.mem_inf.mp x.1.2
    have hA : (x.1 : X) ∈ Abar := H.omega _ hR hx3
    exact Subgroup.mem_inf.mpr ⟨hB _ hJx hA, hJx⟩
  have hcard : Nat.card {x : ↥(Rbar ⊓ J) // x ^ 3 = 1} ≤ 3 := by
    let f : {x : ↥(Rbar ⊓ J) // x ^ 3 = 1} → ↥(Bbar ⊓ J) := fun x => ⟨(x.1 : X), hmem x⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have h1 := congrArg Subtype.val hxy
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    exact (Nat.card_le_card_of_injective f hf).trans hle3
  have hp : IsPGroup 3 ↥(Rbar ⊓ J) := H.R_pgroup.to_inf_left
  exact CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof.isCyclic_of_card_pow_eq_one_le
    (p := 3) (by norm_num) hp hcard

end Pure

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem cdP3_closure_cube {G : Type*} [Group G] {a b : G} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set G), x ^ 3 = 1 := by
  have h1 : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({a, b} : Set G) := by
    rw [Subgroup.closure_le]
    intro s hs
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh hs
    rcases hh with rfl | rfl <;> rcases hs with rfl | rfl <;>
      first | rfl | exact hab | exact hab.symm
  have h2 : ∀ x ∈ Subgroup.closure ({a, b} : Set G),
      ∀ y ∈ Subgroup.closure ({a, b} : Set G), x * y = y * x := by
    intro x hx
    have hsub : ({a, b} : Set G) ⊆
        (Subgroup.centralizer ((Subgroup.closure ({a, b} : Set G) : Set G)) : Set G) := by
      intro s hs
      simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      exact ((Subgroup.mem_centralizer_iff.mp (h1 hh)) s hs).symm
    have hle : Subgroup.closure ({a, b} : Set G) ≤
        Subgroup.centralizer ((Subgroup.closure ({a, b} : Set G) : Set G)) :=
      (Subgroup.closure_le _).mpr hsub
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (hle hx)) y hy).symm
  intro x hx
  refine Subgroup.closure_induction (p := fun x _ => x ^ 3 = 1) ?_ ?_ ?_ ?_ hx
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact ha
    · exact hb
  · exact one_pow 3
  · intro x y hx hy hx3 hy3
    have hx3' : x ^ 3 = 1 := hx3
    have hy3' : y ^ 3 = 1 := hy3
    show (x * y) ^ 3 = 1
    rw [(show Commute x y from h2 x hx y hy).mul_pow, hx3', hy3', one_mul]
  · intro x hx hx3
    have hx3' : x ^ 3 = 1 := hx3
    show x⁻¹ ^ 3 = 1
    rw [inv_pow, hx3', inv_one]

section Pure

variable {X : Type} [Group X] [Finite X] {Abar Bbar Rbar : Subgroup X} {cb db ab : X}

theorem cd_not_all_inner (H : CDHyp Abar Bbar Rbar cb db ab) {J : Subgroup X}
    (hJ : CFSG.IsComponent J) (hZ : Subgroup.center J = ⊥) {e : X} (heJ : e ∈ J) (he1 : e ≠ 1)
    (heB : e ∈ Bbar) (hnorm : ∀ r ∈ Rbar, ∀ x ∈ J, r * x * r⁻¹ ∈ J)
    (hcyc : ∀ P : Sylow 3 ↥J, IsCyclic ↥(P : Subgroup ↥J)) :
    ¬ ∀ y ∈ Abar, ∃ j ∈ J, ∀ x ∈ J, y * x * y⁻¹ = j * x * j⁻¹ := by
  intro hall
  have hcbB : cb ∈ Bbar := by
    rw [H.B_def]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hdbB : db ∈ Bbar := by
    rw [H.B_def]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hBA : Bbar ≤ Abar := by
    rw [H.B_def, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨H.cb_mem, H.db_mem⟩
  have hab3 : ab ^ 3 = 1 := H.A_exp ab H.ab_mem
  have heA : e ∈ Abar := hBA heB
  have he3 : e ^ 3 = 1 := H.A_exp e heA
  have hab_notB : ab ∉ Bbar := by
    intro habB
    have hAle : Abar ≤ Bbar := by
      rw [← H.A_gen, Subgroup.closure_le, Set.insert_subset_iff, Set.insert_subset_iff,
        Set.singleton_subset_iff]
      exact ⟨hcbB, hdbB, habB⟩
    have hle := Subgroup.card_le_of_le hAle
    rw [H.card_A, H.card_B] at hle
    omega
  have hcen1 : ∀ z : X, ∀ hz : z ∈ J, (∀ g ∈ J, z * g = g * z) → z = 1 := by
    intro z hz hcomm
    have hmem : (⟨z, hz⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (hcomm g.1 g.2).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hconj : ∀ r ∈ Rbar, ∀ y : X, (∀ x ∈ J, y * x = x * y) →
      ∀ x ∈ J, (r * y * r⁻¹) * x = x * (r * y * r⁻¹) := by
    intro r hr y hy x hx
    have hx' : r⁻¹ * x * r⁻¹⁻¹ ∈ J := hnorm r⁻¹ (Rbar.inv_mem hr) x hx
    have hyx := hy _ hx'
    have e1 : (r * y * r⁻¹) * x = r * (y * (r⁻¹ * x * r⁻¹⁻¹)) * r⁻¹ := by group
    have e2 : x * (r * y * r⁻¹) = r * ((r⁻¹ * x * r⁻¹⁻¹) * y) * r⁻¹ := by group
    rw [e1, e2, hyx]
  have hC : ∀ y ∈ Abar, (∀ x ∈ J, y * x = x * y) → y ∈ Bbar := by
    intro y hyA hyC
    by_contra hyB
    have hBcent : ∀ b ∈ Bbar, ∀ x ∈ J, b * x = x * b := by
      intro b hb x hx
      obtain ⟨r, hrR, hr⟩ := H.transvection y hyA hyB b hb
      have h1 := hconj r hrR y hyC x hx
      rw [hr] at h1
      have h2 : y * (b * x) = y * (x * b) := by
        calc y * (b * x) = y * b * x := (mul_assoc _ _ _).symm
          _ = x * (y * b) := h1
          _ = x * y * b := (mul_assoc _ _ _).symm
          _ = y * x * b := by rw [hyC x hx]
          _ = y * (x * b) := mul_assoc _ _ _
      exact mul_left_cancel h2
    exact he1 (hcen1 e heJ (fun g hg => hBcent e heB g hg))
  obtain ⟨jw, hjwJ, hjw⟩ := hall ab H.ab_mem
  have hpow : ∀ n : ℕ, ∀ x ∈ J, jw ^ n * x * (jw ^ n)⁻¹ = ab ^ n * x * (ab ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ k ih =>
      intro x hx
      have hkx : jw ^ k * x * (jw ^ k)⁻¹ ∈ J :=
        J.mul_mem (J.mul_mem (J.pow_mem hjwJ k) hx) (J.inv_mem (J.pow_mem hjwJ k))
      calc jw ^ (k + 1) * x * (jw ^ (k + 1))⁻¹
          = jw * (jw ^ k * x * (jw ^ k)⁻¹) * jw⁻¹ := by rw [pow_succ']; group
        _ = ab * (jw ^ k * x * (jw ^ k)⁻¹) * ab⁻¹ := by rw [← hjw _ hkx]
        _ = ab * (ab ^ k * x * (ab ^ k)⁻¹) * ab⁻¹ := by rw [ih x hx]
        _ = ab ^ (k + 1) * x * (ab ^ (k + 1))⁻¹ := by rw [pow_succ']; group
  have hjw3 : jw ^ 3 = 1 := by
    apply hcen1 (jw ^ 3) (J.pow_mem hjwJ 3)
    intro g hg
    have h := hpow 3 g hg
    rw [hab3, one_mul, inv_one, mul_one] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hcommE : jw * e = e * jw := by
    have hae : ab * e = e * ab := H.A_comm ab H.ab_mem e heA
    have h1 := hjw e heJ
    have h2 : jw * e * jw⁻¹ = e := by
      rw [← h1, hae, mul_inv_cancel_right]
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hjwnotB : ∀ u ∈ Bbar, jw ≠ u := by
    intro u hu hEq
    have hjwA : jw ∈ Abar := by
      rw [hEq]
      exact hBA hu
    have hvJ : ∀ x ∈ J, (ab * jw⁻¹) * x = x * (ab * jw⁻¹) := by
      intro x hx
      have hy' : jw⁻¹ * x * jw ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hjwJ) hx) hjwJ
      have h1 := hjw _ hy'
      have h2 : jw * (jw⁻¹ * x * jw) * jw⁻¹ = x := by group
      rw [h2] at h1
      have h4 : ab * (jw⁻¹ * x * jw) = x * ab := mul_inv_eq_iff_eq_mul.mp h1
      calc ab * jw⁻¹ * x = ab * (jw⁻¹ * x * jw) * jw⁻¹ := by group
        _ = x * ab * jw⁻¹ := by rw [h4]
        _ = x * (ab * jw⁻¹) := by group
    have hv := hC (ab * jw⁻¹) (Abar.mul_mem H.ab_mem (Abar.inv_mem hjwA)) hvJ
    have hjwB : jw ∈ Bbar := by
      rw [hEq]
      exact hu
    apply hab_notB
    have h5 : ab * jw⁻¹ * jw ∈ Bbar := Bbar.mul_mem hv hjwB
    simpa using h5
  have hjw1 : jw ≠ 1 := hjwnotB 1 Bbar.one_mem
  have hjwe : jw ≠ e := hjwnotB e heB
  have hee : e * e ∈ Bbar := Bbar.mul_mem heB heB
  have hjwee : jw ≠ e * e := hjwnotB (e * e) hee
  have hee3 : (e * e) ^ 3 = 1 := by
    rw [(Commute.refl e).mul_pow, he3, one_mul]
  have hee_ne1 : e * e ≠ 1 := by
    intro h
    apply he1
    have h3 : e * (e * e) = 1 := by
      rw [← pow_three]
      exact he3
    rw [h, mul_one] at h3
    exact h3
  have hee_ne_e : e * e ≠ e := by
    intro h
    apply he1
    exact mul_left_cancel (h.trans (mul_one e).symm)
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcomm' : (⟨e, heJ⟩ : ↥J) * ⟨jw, hjwJ⟩ = ⟨jw, hjwJ⟩ * ⟨e, heJ⟩ :=
    Subtype.ext hcommE.symm
  have ha'3 : (⟨e, heJ⟩ : ↥J) ^ 3 = 1 := Subtype.ext he3
  have hb'3 : (⟨jw, hjwJ⟩ : ↥J) ^ 3 = 1 := Subtype.ext hjw3
  have hcubeK := cdP3_closure_cube hcomm' ha'3 hb'3
  have hKp : IsPGroup 3 (Subgroup.closure ({⟨e, heJ⟩, ⟨jw, hjwJ⟩} : Set ↥J)) := by
    refine isPGroup_iff_pow_pow_eq_one.mpr (fun g => ⟨1, ?_⟩)
    apply Subtype.ext
    simp only [Subgroup.coe_pow, pow_one, Subgroup.coe_one]
    exact hcubeK _ g.2
  obtain ⟨P, hKP⟩ := IsPGroup.exists_le_sylow hKp
  have ha'P : (⟨e, heJ⟩ : ↥J) ∈ (P : Subgroup ↥J) :=
    hKP (Subgroup.subset_closure (Set.mem_insert _ _))
  have hb'P : (⟨jw, hjwJ⟩ : ↥J) ∈ (P : Subgroup ↥J) :=
    hKP (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hcycP := hcyc P
  classical
  haveI : Fintype ↥(P : Subgroup ↥J) := Fintype.ofFinite _
  have hcard := IsCyclic.card_pow_eq_one_le (α := ↥(P : Subgroup ↥J)) (n := 3) (by norm_num)
  have hcubeP : ∀ x : ↥(P : Subgroup ↥J), ((x : ↥J) : X) ^ 3 = 1 → x ^ 3 = 1 := by
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    simpa using hx
  have hne : ∀ x y : ↥(P : Subgroup ↥J), ((x : ↥J) : X) ≠ ((y : ↥J) : X) → x ≠ y :=
    fun x y h hxy => h (by rw [hxy])
  obtain ⟨u2, hu2⟩ : ∃ u : ↥(P : Subgroup ↥J), ((u : ↥J) : X) = e :=
    ⟨⟨⟨e, heJ⟩, ha'P⟩, rfl⟩
  obtain ⟨u3, hu3⟩ : ∃ u : ↥(P : Subgroup ↥J), ((u : ↥J) : X) = e * e :=
    ⟨⟨⟨e, heJ⟩ * ⟨e, heJ⟩, (P : Subgroup ↥J).mul_mem ha'P ha'P⟩, rfl⟩
  obtain ⟨u4, hu4⟩ : ∃ u : ↥(P : Subgroup ↥J), ((u : ↥J) : X) = jw :=
    ⟨⟨⟨jw, hjwJ⟩, hb'P⟩, rfl⟩
  have hu1 : (((1 : ↥(P : Subgroup ↥J)) : ↥J) : X) = 1 := rfl
  have hgt : 3 < (Finset.univ.filter (fun x : ↥(P : Subgroup ↥J) => x ^ 3 = 1)).card := by
    have hm : ∀ x : ↥(P : Subgroup ↥J), x ^ 3 = 1 →
        x ∈ Finset.univ.filter (fun x : ↥(P : Subgroup ↥J) => x ^ 3 = 1) :=
      fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    rw [Finset.three_lt_card]
    refine ⟨1, hm 1 (one_pow 3), u2, hm u2 (hcubeP u2 (by rw [hu2]; exact he3)),
      u3, hm u3 (hcubeP u3 (by rw [hu3]; exact hee3)),
      u4, hm u4 (hcubeP u4 (by rw [hu4]; exact hjw3)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hne _ _ (by rw [hu1, hu2]; exact he1.symm)
    · exact hne _ _ (by rw [hu1, hu3]; exact hee_ne1.symm)
    · exact hne _ _ (by rw [hu1, hu4]; exact hjw1.symm)
    · exact hne _ _ (by rw [hu2, hu3]; exact hee_ne_e.symm)
    · exact hne _ _ (by rw [hu2, hu4]; exact hjwe.symm)
    · exact hne _ _ (by rw [hu3, hu4]; exact hjwee.symm)
  exact absurd hcard (not_le.mpr hgt)

end Pure

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

section Pure

variable {X : Type} [Group X] [Finite X] {Abar Bbar Rbar : Subgroup X} {cb db ab : X}

theorem cd_swap (H : CDHyp Abar Bbar Rbar cb db ab) (ν : MulAut X) {i : ℕ} (hi : ¬ 3 ∣ i)
    (hνc : ν cb = db ^ i) (hνd : ν db = cb ^ i) {J : Subgroup X} (hJ : CFSG.IsComponent J)
    (hZ : Subgroup.center J = ⊥) {e : X} (heJ : e ∈ J) (he1 : e ≠ 1) (heB : e ∈ Bbar) :
    ∀ x ∈ J, ν x ∈ J := by
  have hc : Commute cb db := H.A_comm cb H.cb_mem db H.db_mem
  have hc3 : cb ^ 3 = 1 := H.A_exp cb H.cb_mem
  have hd3 : db ^ 3 = 1 := H.A_exp db H.db_mem
  have hc2 : Commute cb (db ^ 2) := hc.pow_right 2
  have hcsq2 : (cb ^ 2) ^ 2 = cb := by
    rw [← pow_mul, show 2 * 2 = 1 + 3 by norm_num, pow_add, hc3, mul_one, pow_one]
  have hdsq2 : (db ^ 2) ^ 2 = db := by
    rw [← pow_mul, show 2 * 2 = 1 + 3 by norm_num, pow_add, hd3, mul_one, pow_one]
  have hsq21 : (cb ^ 2 * db ^ 1) ^ 2 = cb * db ^ 2 := by
    rw [pow_one, (hc.pow_left 2).mul_pow 2, hcsq2]
  have hsq' : (cb * db ^ 2) ^ 2 = cb ^ 2 * db ^ 1 := by
    rw [pow_one, hc2.mul_pow 2, hdsq2]
  have hrep : ∀ g ∈ Bbar, ∃ a b : ℕ, g = cb ^ a * db ^ b := by
    intro g hg
    rw [H.B_def] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · exact ⟨1, 0, by rw [hx]; simp⟩
      · exact ⟨0, 1, by rw [hx]; simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨a, b, rfl⟩ := ihx
      obtain ⟨c, d, rfl⟩ := ihy
      refine ⟨a + c, b + d, ?_⟩
      calc cb ^ a * db ^ b * (cb ^ c * db ^ d)
          = cb ^ a * (db ^ b * cb ^ c) * db ^ d := by simp only [mul_assoc]
        _ = cb ^ a * (cb ^ c * db ^ b) * db ^ d := by rw [(hc.symm.pow_pow b c).eq]
        _ = cb ^ (a + c) * db ^ (b + d) := by rw [pow_add, pow_add]; simp only [mul_assoc]
    | inv x _ ihx =>
      obtain ⟨a, b, rfl⟩ := ihx
      refine ⟨2 * a, 2 * b, ?_⟩
      apply inv_eq_of_mul_eq_one_right
      have h1 : cb ^ a * cb ^ (2 * a) = 1 := by
        rw [← pow_add, show a + 2 * a = 3 * a by ring, pow_mul, hc3, one_pow]
      have h2 : db ^ b * db ^ (2 * b) = 1 := by
        rw [← pow_add, show b + 2 * b = 3 * b by ring, pow_mul, hd3, one_pow]
      calc cb ^ a * db ^ b * (cb ^ (2 * a) * db ^ (2 * b))
          = cb ^ a * (db ^ b * cb ^ (2 * a)) * db ^ (2 * b) := by simp only [mul_assoc]
        _ = cb ^ a * (cb ^ (2 * a) * db ^ b) * db ^ (2 * b) := by
            rw [(hc.symm.pow_pow b (2 * a)).eq]
        _ = (cb ^ a * cb ^ (2 * a)) * (db ^ b * db ^ (2 * b)) := by simp only [mul_assoc]
        _ = 1 := by rw [h1, h2, one_mul]
  have hrep3 : ∀ g ∈ Bbar, ∃ a b : ℕ, a < 3 ∧ b < 3 ∧ g = cb ^ a * db ^ b := by
    intro g hg
    obtain ⟨a, b, rfl⟩ := hrep g hg
    refine ⟨a % 3, b % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← pow_eq_pow_mod a hc3, ← pow_eq_pow_mod b hd3]
  have hcb1 : cb ≠ 1 := by
    intro h
    have hle : Bbar ≤ Subgroup.zpowers db := by
      rw [H.B_def, Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg
      · rw [hg, h]; exact Subgroup.one_mem _
      · rw [hg]; exact Subgroup.mem_zpowers db
    have h1 := Subgroup.card_le_of_le hle
    rw [H.card_B, Nat.card_zpowers] at h1
    have h2 : orderOf db ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  have hdb1 : db ≠ 1 := by
    intro h
    have hle : Bbar ≤ Subgroup.zpowers cb := by
      rw [H.B_def, Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg
      · rw [hg]; exact Subgroup.mem_zpowers cb
      · rw [hg, h]; exact Subgroup.one_mem _
    have h1 := Subgroup.card_le_of_le hle
    rw [H.card_B, Nat.card_zpowers] at h1
    have h2 : orderOf cb ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  have hroot : ∀ g : X, g ^ 3 = 1 → ∀ n : ℕ, ¬ 3 ∣ n → ∃ m : ℕ, (g ^ n) ^ m = g := by
    intro g hg n hn
    have hn' : n % 3 ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
    rcases (show n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h
    · exact ⟨1, by rw [pow_one, pow_eq_pow_mod n hg, h, pow_one]⟩
    · exact ⟨2, by rw [← pow_mul, pow_eq_pow_mod (n * 2) hg, show n * 2 % 3 = 1 by omega, pow_one]⟩
  obtain ⟨J', hJ'def⟩ : ∃ J' : Subgroup X, J' = J.map ν.toMonoidHom := ⟨_, rfl⟩
  have hJ'c : CFSG.IsComponent J' := by
    rw [hJ'def]
    exact CFSG.LocalCores.isComponent_map_mulEquiv ν hJ
  have hmemJ' : ∀ x ∈ J, ν x ∈ J' := by
    intro x hx
    rw [hJ'def]
    exact Subgroup.mem_map_of_mem ν.toMonoidHom hx
  have hZ' : Subgroup.center J' = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    rw [Subgroup.mem_center_iff] at hz
    have hz2 : (z : X) ∈ J.map ν.toMonoidHom := by
      rw [← hJ'def]
      exact z.2
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz2
    have hyc : (⟨y, hy⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 : ν g.1 * z.1 = z.1 * ν g.1 :=
        congrArg Subtype.val (hz ⟨ν g.1, hmemJ' g.1 g.2⟩)
      rw [← hyz] at h1
      have h3 : ν (g.1 * y) = ν (y * g.1) := by
        rw [map_mul, map_mul]
        exact h1
      show g.1 * y = y * g.1
      exact ν.injective h3
    rw [hZ, Subgroup.mem_bot] at hyc
    have hy1 : y = 1 := congrArg Subtype.val hyc
    have hνy : ν y = 1 := by rw [hy1, map_one]
    apply Subtype.ext
    show (z : X) = 1
    exact hyz.symm.trans hνy
  have hzJ : cb * db ∉ J := by
    intro hzJ
    have hmem : (⟨cb * db, hzJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      show g.1 * (cb * db) = (cb * db) * g.1
      exact H.z_central g.1
    rw [hZ, Subgroup.mem_bot] at hmem
    exact H.z_ne (congrArg Subtype.val hmem)
  suffices hJJ' : J' = J by
    intro x hx
    have hx' := hmemJ' x hx
    rwa [hJJ'] at hx'
  by_contra hne
  have hne' : J ≠ J' := fun h => hne h.symm
  have hinf : J ⊓ J' = ⊥ := compJ3_inf_eq_bot hJ hJ'c hne' hZ
  have hJ'cent : J' ≤ Subgroup.centralizer (J : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hJ'c hJ).resolve_left hne)
  have hcbJ : cb ∉ J := by
    intro hcJ
    have hdJ' : db ∈ J' := by
      have hm : db ^ i ∈ J' := by
        have h0 := hmemJ' cb hcJ
        rwa [hνc] at h0
      obtain ⟨m, hm'⟩ := hroot db hd3 i hi
      have h0 := J'.pow_mem hm m
      rwa [hm'] at h0
    have hmem : (⟨db, hdJ'⟩ : J') ∈ Subgroup.center J' := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 : cb * g.1 = g.1 * cb := Subgroup.mem_centralizer_iff.mp (hJ'cent g.2) cb hcJ
      show g.1 * db = db * g.1
      exact H.C_cd g.1 h1.symm
    rw [hZ', Subgroup.mem_bot] at hmem
    exact hdb1 (congrArg Subtype.val hmem)
  have hdbJ : db ∉ J := by
    intro hdJ
    have hcJ' : cb ∈ J' := by
      have hm : cb ^ i ∈ J' := by
        have h0 := hmemJ' db hdJ
        rwa [hνd] at h0
      obtain ⟨m, hm'⟩ := hroot cb hc3 i hi
      have h0 := J'.pow_mem hm m
      rwa [hm'] at h0
    have hmem : (⟨cb, hcJ'⟩ : J') ∈ Subgroup.center J' := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 : db * g.1 = g.1 * db := Subgroup.mem_centralizer_iff.mp (hJ'cent g.2) db hdJ
      show g.1 * cb = cb * g.1
      exact H.C_dc g.1 h1.symm
    rw [hZ', Subgroup.mem_bot] at hmem
    exact hcb1 (congrArg Subtype.val hmem)
  have hw : cb * db ^ 2 ∈ J ∧ cb * db ^ 2 ≠ 1 := by
    obtain ⟨a, b, ha, hb, rfl⟩ := hrep3 e heB
    obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    all_goals obtain rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 := by omega
    · exact (he1 (by simp)).elim
    · rw [pow_zero, one_mul, pow_one] at heJ
      exact (hdbJ heJ).elim
    · rw [pow_zero, one_mul] at heJ
      have h5 := J.pow_mem heJ 2
      rw [hdsq2] at h5
      exact (hdbJ h5).elim
    · rw [pow_zero, mul_one, pow_one] at heJ
      exact (hcbJ heJ).elim
    · simp only [pow_one] at heJ
      exact (hzJ heJ).elim
    · simp only [pow_one] at heJ he1
      exact ⟨heJ, he1⟩
    · rw [pow_zero, mul_one] at heJ
      have h5 := J.pow_mem heJ 2
      rw [hcsq2] at h5
      exact (hcbJ h5).elim
    · refine ⟨?_, ?_⟩
      · have h5 := J.pow_mem heJ 2
        rw [hsq21] at h5
        exact h5
      · intro h1
        apply he1
        rw [← hsq', h1, one_pow]
    · exfalso
      have hc22 : Commute (cb ^ 2) (db ^ 2) := (hc.pow_left 2).pow_right 2
      have h5 := J.pow_mem heJ 2
      rw [hc22.mul_pow 2, hcsq2, hdsq2] at h5
      exact hzJ h5
  obtain ⟨hwJ, hw1⟩ := hw
  have hνw : ν (cb * db ^ 2) = (cb * db ^ 2) ^ (2 * i) := by
    have hdi : (db ^ 2) ^ (2 * i) = db ^ i := by
      rw [← pow_mul, show 2 * (2 * i) = i + 3 * i by ring, pow_add, pow_mul, hd3, one_pow,
        mul_one]
    rw [map_mul, map_pow, hνc, hνd, hc2.mul_pow (2 * i), hdi, ← pow_mul, mul_comm i 2]
    exact (hc.symm.pow_pow i (2 * i)).eq
  have hνwJ : ν (cb * db ^ 2) ∈ J := by
    rw [hνw]
    exact J.pow_mem hwJ _
  have hνwJ' : ν (cb * db ^ 2) ∈ J' := hmemJ' _ hwJ
  have hνw1 : ν (cb * db ^ 2) ≠ 1 := by
    intro h
    apply hw1
    apply ν.injective
    rw [h, map_one]
  have hmem_inf : ν (cb * db ^ 2) ∈ J ⊓ J' := Subgroup.mem_inf.mpr ⟨hνwJ, hνwJ'⟩
  rw [hinf, Subgroup.mem_bot] at hmem_inf
  exact hνw1 hmem_inf

end Pure

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

def cdRestrictJ {X : Type} [Group X] {J : Subgroup X} (f : MulAut X) (h : ∀ x ∈ J, f x ∈ J)
    (h' : ∀ x ∈ J, f⁻¹ x ∈ J) : MulAut ↥J where
  toFun x := ⟨f x.1, h x.1 x.2⟩
  invFun x := ⟨f⁻¹ x.1, h' x.1 x.2⟩
  left_inv x := Subtype.ext (MulAut.inv_apply_self _ f x.1)
  right_inv x := Subtype.ext (MulAut.apply_inv_self _ f x.1)
  map_mul' x y := Subtype.ext (map_mul f x.1 y.1)

section Pure

variable {X : Type} [Group X] [Finite X] {Abar Bbar Rbar : Subgroup X} {cb db ab : X}

theorem cd_out_inner {J : Subgroup X} (hK1 : ∀ σ τ : MulAut ↥J, KFacts.IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹))
    (ν : MulAut X) (hνJ : ∀ x ∈ J, ν x ∈ J) (hνa : ν ab = ab⁻¹) (hab3 : ab ^ 3 = 1)
    (habJ : ∀ x ∈ J, ab * x * ab⁻¹ ∈ J) :
    ∃ j ∈ J, ∀ x ∈ J, ab * x * ab⁻¹ = j * x * j⁻¹ := by
  have h3 : ab * ab * ab = 1 := (pow_three' ab).symm.trans hab3
  have hsq : ab * ab = ab⁻¹ := eq_inv_of_mul_eq_one_left h3
  have hτinv : ∀ x ∈ J, ab⁻¹ * x * ab ∈ J := by
    intro x hx
    have h1 : ab * (ab * x * ab⁻¹) * ab⁻¹ ∈ J := habJ _ (habJ x hx)
    have h2 : ab * (ab * x * ab⁻¹) * ab⁻¹ = ab⁻¹ * x * ab := by
      calc ab * (ab * x * ab⁻¹) * ab⁻¹ = (ab * ab) * x * (ab * ab)⁻¹ := by group
        _ = ab⁻¹ * x * ab := by rw [hsq, inv_inv]
    rwa [h2] at h1
  have hνJ' : ∀ x ∈ J, ν⁻¹ x ∈ J := by
    intro x hx
    let ψ : ↥J → ↥J := fun y => ⟨ν y.1, hνJ y.1 y.2⟩
    have hψ : Function.Injective ψ := by
      intro a b hab
      have hab' : ν a.1 = ν b.1 := congrArg Subtype.val hab
      exact Subtype.ext (MulEquiv.injective ν hab')
    obtain ⟨y, hy⟩ := Finite.surjective_of_injective hψ ⟨x, hx⟩
    have hyx : ν y.1 = x := congrArg Subtype.val hy
    rw [← hyx, MulAut.inv_apply_self]
    exact y.2
  obtain ⟨σ, hσ, hσi⟩ : ∃ σ : MulAut ↥J, (∀ x : ↥J, ((σ x : ↥J) : X) = ν x) ∧
      (∀ x : ↥J, ((σ⁻¹ x : ↥J) : X) = ν⁻¹ x) :=
    ⟨cdRestrictJ ν hνJ hνJ', fun _ => rfl, fun _ => rfl⟩
  obtain ⟨τ, hτ, hτi⟩ : ∃ τ : MulAut ↥J,
      (∀ x : ↥J, ((τ x : ↥J) : X) = ab * (x : X) * ab⁻¹) ∧
      (∀ x : ↥J, ((τ⁻¹ x : ↥J) : X) = ab⁻¹ * (x : X) * ab) :=
    ⟨cdRestrictJ (MulAut.conj ab) habJ hτinv, fun _ => rfl, fun _ => rfl⟩
  have hconj : σ * τ * σ⁻¹ = τ⁻¹ := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    show ((σ (τ (σ⁻¹ x)) : ↥J) : X) = ((τ⁻¹ x : ↥J) : X)
    rw [hσ, hτ, hσi, hτi]
    simp only [map_mul, map_inv, hνa, inv_inv, MulAut.apply_inv_self]
  have hτ3 : τ * τ * τ = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    show ((τ (τ (τ x)) : ↥J) : X) = ((1 : MulAut ↥J) x : X)
    rw [hτ, hτ, hτ, MulAut.one_apply]
    have e : ab * (ab * (ab * (x : X) * ab⁻¹) * ab⁻¹) * ab⁻¹
        = (ab * ab * ab) * (x : X) * (ab * ab * ab)⁻¹ := by
      group
    rw [e, h3, one_mul, inv_one, mul_one]
  have hsqτ : τ * τ = τ⁻¹ := eq_inv_of_mul_eq_one_left hτ3
  have hcomm : σ * τ * σ⁻¹ * τ⁻¹ = τ := by
    rw [hconj, ← hsqτ]
    calc τ * τ * (τ * τ) = τ * τ * τ * τ := by group
      _ = τ := by rw [hτ3, one_mul]
  have hinner : KFacts.IsInnerAut τ := by
    have h := hK1 σ τ
    rw [hcomm] at h
    exact h
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hinner
  refine ⟨(g : X), g.2, fun x hx => ?_⟩
  calc ab * x * ab⁻¹ = ((τ ⟨x, hx⟩ : ↥J) : X) := (hτ ⟨x, hx⟩).symm
    _ = ((MulAut.conj g ⟨x, hx⟩ : ↥J) : X) := by rw [hg]
    _ = (g : X) * x * (g : X)⁻¹ := rfl

end Pure

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

section Aux

variable {X : Type} [Group X]

theorem cdP6_exists_noncomm {J : Subgroup X} (hJ : CFSG.IsComponent J) :
    ∃ x y : J, x * y ≠ y * x := by
  obtain ⟨a, b, hab⟩ := hJ.1.2.2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨x, y, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul]

open scoped Pointwise in
theorem cdP6_mem_conj_smul (g : X) (H : Subgroup X) (y : X) :
    y ∈ MulAut.conj g • H ↔ g⁻¹ * y * g ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]

open scoped Pointwise in
theorem cdP6_conj_mem_of_sylow (g : X) (Rs R' : Sylow 3 X) (hg : g • Rs = R') {z : X}
    (hz : z ∈ (R' : Subgroup X)) : g⁻¹ * z * g ∈ (Rs : Subgroup X) := by
  rw [← hg, Sylow.coe_subgroup_smul, cdP6_mem_conj_smul] at hz
  exact hz

theorem cdP6_all_sylow_cyclic {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hS : IsCyclic ↥(S : Subgroup G)) :
    ∀ P : Sylow p G, IsCyclic ↥(P : Subgroup G) := by
  intro P
  haveI : Finite (Sylow p G) :=
    Finite.of_injective (fun Q : Sylow p G => (Q : Set G)) (fun Q R h => SetLike.coe_injective h)
  exact (MulEquiv.isCyclic (Sylow.equiv S P)).mp hS

abbrev cdP6_Inn (J : Subgroup X) (y : X) : Prop :=
  ∃ j ∈ J, ∀ x ∈ J, y * x * y⁻¹ = j * x * j⁻¹

theorem cdP6_Inn_one (J : Subgroup X) : cdP6_Inn J 1 :=
  ⟨1, one_mem J, fun _ _ => rfl⟩

theorem cdP6_Inn_mul {J : Subgroup X} {a b : X} (ha : cdP6_Inn J a)
    (hb : cdP6_Inn J b) : cdP6_Inn J (a * b) := by
  obtain ⟨ja, hja, hA⟩ := ha
  obtain ⟨jb, hjb, hB⟩ := hb
  have hk : a * jb * a⁻¹ ∈ J := by
    rw [hA jb hjb]
    exact mul_mem (mul_mem hja hjb) (inv_mem hja)
  refine ⟨a * jb * a⁻¹ * ja, mul_mem hk hja, fun x hx => ?_⟩
  calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    _ = a * (jb * x * jb⁻¹) * a⁻¹ := by rw [hB x hx]
    _ = (a * jb * a⁻¹) * (a * x * a⁻¹) * (a * jb * a⁻¹)⁻¹ := by group
    _ = (a * jb * a⁻¹) * (ja * x * ja⁻¹) * (a * jb * a⁻¹)⁻¹ := by rw [hA x hx]
    _ = (a * jb * a⁻¹ * ja) * x * (a * jb * a⁻¹ * ja)⁻¹ := by group

theorem cdP6_Inn_inv {J : Subgroup X} {a : X} (ha : cdP6_Inn J a) :
    cdP6_Inn J a⁻¹ := by
  obtain ⟨j, hj, hA⟩ := ha
  refine ⟨j⁻¹, inv_mem hj, fun x hx => ?_⟩
  have hx' : j⁻¹ * x * j ∈ J := mul_mem (mul_mem (inv_mem hj) hx) hj
  have key : a * (j⁻¹ * x * j) * a⁻¹ = x := by
    rw [hA _ hx']
    group
  have h2 : a⁻¹ * x * a = j⁻¹ * x * j := by
    calc a⁻¹ * x * a = a⁻¹ * (a * (j⁻¹ * x * j) * a⁻¹) * a := by rw [key]
      _ = j⁻¹ * x * j := by group
  simpa only [inv_inv] using h2

theorem cdP6_Inn_central {J : Subgroup X} {z : X} (hz : ∀ x : X, x * z = z * x) :
    cdP6_Inn J z := by
  refine ⟨1, one_mem J, fun x _ => ?_⟩
  rw [← hz x]
  simp

theorem cdP6_Inn_closure {J : Subgroup X} {s : Set X} (hs : ∀ a ∈ s, cdP6_Inn J a) {a : X}
    (ha : a ∈ Subgroup.closure s) : cdP6_Inn J a :=
  Subgroup.closure_induction (p := fun x _ => cdP6_Inn J x) (fun x hx => hs x hx)
    (cdP6_Inn_one J) (fun _ _ _ _ hx hy => cdP6_Inn_mul hx hy)
    (fun _ _ hx => cdP6_Inn_inv hx) ha

end Aux

section Pure

variable {X : Type} [Group X] [Finite X] {Abar Bbar Rbar : Subgroup X} {cb db ab : X}

theorem cdP6_core (hK1 : CyclicSylowThreeOutAbelian) (hX : CFSG.IsKGroup X)
    (Rs : Sylow 3 X) (H : CDHyp Abar Bbar (Rs : Subgroup X) cb db ab) {i : ℕ} (hi : ¬ 3 ∣ i)
    (ν : MulAut X) (hνc : ν cb = db ^ i) (hνd : ν db = cb ^ i) (hνa : ν ab = ab⁻¹)
    (hcl : ∀ J : Subgroup X, CFSG.IsComponent J → Subgroup.center J = ⊥)
    (J : Subgroup X) (hJ : CFSG.IsComponent J) (h3 : 3 ∣ Nat.card J)
    (S : Sylow 3 ↥J) (hS : ∀ y ∈ (S : Subgroup ↥J), (y : X) ∈ (Rs : Subgroup X)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center J = ⊥ := hcl J hJ
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(S : Subgroup ↥J)) 3
    (S.dvd_card_of_dvd_card h3)
  obtain ⟨e, heJ, heR, he3⟩ : ∃ e : X, e ∈ J ∧ e ∈ (Rs : Subgroup X) ∧ orderOf e = 3 :=
    ⟨((x : ↥J) : X), (x : ↥J).2, hS (x : ↥J) x.2, by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]⟩
  have he1 : e ≠ 1 := by
    intro h
    rw [h, orderOf_one] at he3
    norm_num at he3
  have he3pow : e ^ 3 = 1 := by
    rw [← he3]
    exact pow_orderOf_eq_one e
  have heA : e ∈ Abar := H.omega e heR he3pow
  have heB : e ∈ Bbar := cd_step1 H hJ hZ heJ heA
  have hB : ∀ u ∈ J, u ∈ Abar → u ∈ Bbar := fun u hu huA => cd_step1 H hJ hZ hu huA
  have hnorm := cd_normalizes H hJ hZ heJ he1 heB
  have hQp : IsPGroup 3 (((Rs : Subgroup X) ⊓ J).subgroupOf J) :=
    (H.R_pgroup.to_le inf_le_left).comap_subtype
  have hSle : (S : Subgroup ↥J) ≤ ((Rs : Subgroup X) ⊓ J).subgroupOf J := by
    intro y hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨hS y hy, y.2⟩
  have hSeq : ((Rs : Subgroup X) ⊓ J).subgroupOf J = (S : Subgroup ↥J) :=
    S.is_maximal' hQp hSle
  have hcycS : IsCyclic ↥(S : Subgroup ↥J) := by
    rw [← hSeq]
    exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : (Rs : Subgroup X) ⊓ J ≤ J))).mpr (cd_cyclic H hJ hZ hB)
  have hcyc : ∀ P : Sylow 3 ↥J, IsCyclic ↥(P : Subgroup ↥J) :=
    cdP6_all_sylow_cyclic S hcycS
  have hK1' : ∀ σ τ : MulAut ↥J, KFacts.IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) :=
    hK1 ↥J (CFSG.IsKGroup.subgroup hX J) (isSimpleGroup_of_component_center_bot hJ hZ)
      (cdP6_exists_noncomm hJ) hcyc
  have hνJ : ∀ x ∈ J, ν x ∈ J := cd_swap H ν hi hνc hνd hJ hZ heJ he1 heB
  have habJ : ∀ x ∈ J, ab * x * ab⁻¹ ∈ J := hnorm ab (H.A_le_R H.ab_mem)
  have hab3 : ab ^ 3 = 1 := H.A_exp ab H.ab_mem
  obtain ⟨j, hjJ, hj⟩ := cd_out_inner hK1' ν hνJ hνa hab3 habJ
  have hP_ab : cdP6_Inn J ab := ⟨j, hjJ, hj⟩
  have hzJ : cb * db ∉ J := by
    intro hzJ
    have hmem : (⟨cb * db, hzJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (H.z_central g)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact H.z_ne (congrArg Subtype.val hmem)
  have hcb : cb ∈ Bbar := by
    rw [H.B_def]
    exact Subgroup.subset_closure (by simp)
  have hdb : db ∈ Bbar := by
    rw [H.B_def]
    exact Subgroup.subset_closure (by simp)
  have hzB : cb * db ∈ Bbar := mul_mem hcb hdb
  obtain ⟨K, hK⟩ : ∃ K : Subgroup X, K = Subgroup.closure ({e, cb * db} : Set X) := ⟨_, rfl⟩
  have hKB : K ≤ Bbar := by
    rw [hK, Subgroup.closure_le]
    intro y hy
    rcases hy with h | h
    · rw [h]
      exact heB
    · rw [Set.mem_singleton_iff.mp h]
      exact hzB
  have hzpe : Subgroup.zpowers e ≤ K := by
    rw [hK, Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hcardz : Nat.card (Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, he3]
  have hdvdK : Nat.card K ∣ 9 := by
    rw [← H.card_B]
    exact Subgroup.card_dvd_of_le hKB
  have h3K : 3 ∣ Nat.card K := by
    rw [← hcardz]
    exact Subgroup.card_dvd_of_le hzpe
  have hne3 : Nat.card K ≠ 3 := by
    intro hc
    have heq : Subgroup.zpowers e = K :=
      Subgroup.eq_of_le_of_card_ge hzpe (le_of_eq (by rw [hc, hcardz]))
    have hzK : cb * db ∈ K := by
      rw [hK]
      exact Subgroup.subset_closure (by simp)
    have hzJ' : cb * db ∈ Subgroup.zpowers e := by
      rw [heq]
      exact hzK
    exact hzJ ((Subgroup.zpowers_le.mpr heJ) hzJ')
  have hK9 : Nat.card K = 9 := by
    have hle : Nat.card K ≤ 9 := Nat.le_of_dvd (by norm_num) hdvdK
    obtain ⟨m, hm⟩ := h3K
    have hm3 : m ≤ 3 := by omega
    interval_cases m
    · rw [hm] at hdvdK
      norm_num at hdvdK
    · omega
    · rw [hm] at hdvdK
      norm_num at hdvdK
    · omega
  have hKeq : K = Bbar :=
    Subgroup.eq_of_le_of_card_ge hKB (le_of_eq (by rw [hK9, H.card_B]))
  have hcbK : cb ∈ K := by
    rw [hKeq]
    exact hcb
  have hdbK : db ∈ K := by
    rw [hKeq]
    exact hdb
  have hKinn : ∀ y ∈ K, cdP6_Inn J y := by
    intro y hy
    rw [hK] at hy
    refine cdP6_Inn_closure (s := ({e, cb * db} : Set X)) ?_ hy
    intro a ha
    rcases ha with h | h
    · rw [h]
      exact ⟨e, heJ, fun _ _ => rfl⟩
    · rw [Set.mem_singleton_iff.mp h]
      exact cdP6_Inn_central H.z_central
  have hAll : ∀ y ∈ Abar, cdP6_Inn J y := by
    intro y hy
    rw [← H.A_gen] at hy
    refine cdP6_Inn_closure (s := ({cb, db, ab} : Set X)) ?_ hy
    intro a ha
    rcases ha with h | h | h
    · rw [h]
      exact hKinn cb hcbK
    · rw [h]
      exact hKinn db hdbK
    · rw [h]
      exact hP_ab
  exact cd_not_all_inner H hJ hZ heJ he1 heB hnorm hcyc hAll

theorem censusD_pure (hK1 : CyclicSylowThreeOutAbelian) (hX : CFSG.IsKGroup X) (Rs : Sylow 3 X)
    (H : CDHyp Abar Bbar (Rs : Subgroup X) cb db ab) {i : ℕ} (hi : ¬ 3 ∣ i) (ν : MulAut X)
    (hνc : ν cb = db ^ i) (hνd : ν db = cb ^ i) (hνa : ν ab = ab⁻¹)
    (hcl : ∀ J : Subgroup X, CFSG.IsComponent J → Subgroup.center J = ⊥) :
    ∀ J : Subgroup X, CFSG.IsComponent J → ¬ 3 ∣ Nat.card J := by
  intro J hJ h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Sylow 3 X) :=
    Finite.of_injective (fun Q : Sylow 3 X => (Q : Set X)) (fun Q R h => SetLike.coe_injective h)
  obtain ⟨S0⟩ : Nonempty (Sylow 3 ↥J) := Sylow.nonempty
  have hQp : IsPGroup 3 ((S0 : Subgroup ↥J).map J.subtype) := S0.isPGroup'.map J.subtype
  obtain ⟨R', hR'⟩ := IsPGroup.exists_le_sylow hQp
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Rs R'
  let f : X ≃* X := MulAut.conj g⁻¹
  have hJ' : CFSG.IsComponent (J.map f.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv f hJ
  have hcard' : 3 ∣ Nat.card (J.map f.toMonoidHom) := by
    have e1 : Nat.card J = Nat.card (J.map f.toMonoidHom) :=
      Nat.card_congr (MulEquiv.subgroupMap f J).toEquiv
    rw [← e1]
    exact h3
  let φ : ↥J →* ↥(J.map f.toMonoidHom) := (MulEquiv.subgroupMap f J).toMonoidHom
  have hφ : Function.Surjective φ := (MulEquiv.subgroupMap f J).surjective
  let Sstar : Sylow 3 ↥(J.map f.toMonoidHom) := S0.mapSurjective hφ
  have hSstar : ∀ y ∈ (Sstar : Subgroup ↥(J.map f.toMonoidHom)),
      ((y : ↥(J.map f.toMonoidHom)) : X) ∈ (Rs : Subgroup X) := by
    intro y hy
    have hy' : y ∈ (S0 : Subgroup ↥J).map φ := hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
    have hzR : ((z : ↥J) : X) ∈ (R' : Subgroup X) :=
      hR' (Subgroup.mem_map_of_mem J.subtype hz)
    have hzRs : g⁻¹ * ((z : ↥J) : X) * g ∈ (Rs : Subgroup X) :=
      cdP6_conj_mem_of_sylow g Rs R' hg hzR
    have hyX : ((y : ↥(J.map f.toMonoidHom)) : X) = g⁻¹ * ((z : ↥J) : X) * g := by
      rw [← hzy]
      show g⁻¹ * ((z : ↥J) : X) * g⁻¹⁻¹ = g⁻¹ * ((z : ↥J) : X) * g
      rw [inv_inv]
    rw [hyX]
    exact hzRs
  exact cdP6_core hK1 hX Rs H hi ν hνc hνd hνa hcl (J.map f.toMonoidHom) hJ' hcard' Sstar
    hSstar

end Pure

end CFSG.RankThree.PartTwo.Sec11

end
