module

public import CFSG.LocalAnalysis.StandardType.GGWeylCartan
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
public import CFSG.LieType.RootSystem.Cartan
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.Logic.Relation
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

section DihedralEdges

private lemma ggInv_of_sq_eq_one {G : Type*} [Group G] {a : G} (h : a * a = 1) : a⁻¹ = a :=
  (mul_eq_one_iff_inv_eq).mp h

private lemma ggDihedral_braid {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) ^ 3 = 1) : a * b * a = b * a * b := by
  have h1 : a * b * a * b * a * b = 1 := by
    simpa [pow_succ, mul_assoc] using hab
  have h3 : (a * b * a) * (b * a * b) = 1 := by
    calc (a * b * a) * (b * a * b) = a * b * a * b * a * b := by group
      _ = 1 := h1
  have h4 : (b * a * b) * (b * a * b) = 1 := by
    calc (b * a * b) * (b * a * b) = b * a * (b * b) * a * b := by group
      _ = b * (a * a) * b := by rw [hb]; group
      _ = 1 := by simp [ha, hb]
  exact mul_right_cancel (h3.trans h4.symm)

private lemma ggDihedral_ababa {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hbraid : a * b * a = b * a * b) : a * b * a * b * a = b := by
  calc a * b * a * b * a = (a * b * a) * b * a := by group
    _ = (b * a * b) * b * a := by rw [hbraid]
    _ = b * a * (b * b) * a := by group
    _ = b * (a * a) := by rw [hb]; group
    _ = b := by rw [ha]; group

private lemma ggDihedral_babab {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hbraid : a * b * a = b * a * b) : b * a * b * a * b = a := by
  calc b * a * b * a * b = (b * a * b) * a * b := by group
    _ = (a * b * a) * a * b := by rw [hbraid.symm]
    _ = a * b * (a * a) * b := by group
    _ = a * (b * b) := by rw [ha]; group
    _ = a := by rw [hb]; group

private lemma ggDihedral_conj_aba_a {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : (a * b) ^ 3 = 1) :
    (a * b * a) * a * (a * b * a)⁻¹ = b := by
  have ha_inv : a⁻¹ = a := ggInv_of_sq_eq_one ha
  have hb_inv : b⁻¹ = b := ggInv_of_sq_eq_one hb
  have hbraid : a * b * a = b * a * b := ggDihedral_braid ha hb hab
  have haba_inv : (a * b * a)⁻¹ = a * b * a := by
    rw [mul_inv_rev, mul_inv_rev, ha_inv, hb_inv]; group
  calc (a * b * a) * a * (a * b * a)⁻¹ = a * b * a * a * a * b * a := by rw [haba_inv]; group
    _ = a * b * (a * a) * a * b * a := by group
    _ = a * b * a * b * a := by rw [ha]; group
    _ = b := ggDihedral_ababa ha hb hbraid

private lemma ggDihedral_conj_aba_b {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : (a * b) ^ 3 = 1) :
    (a * b * a) * b * (a * b * a)⁻¹ = a := by
  have ha_inv : a⁻¹ = a := ggInv_of_sq_eq_one ha
  have hb_inv : b⁻¹ = b := ggInv_of_sq_eq_one hb
  have hbraid : a * b * a = b * a * b := ggDihedral_braid ha hb hab
  have haba_inv : (a * b * a)⁻¹ = a * b * a := by
    rw [mul_inv_rev, mul_inv_rev, ha_inv, hb_inv]; group
  calc (a * b * a) * b * (a * b * a)⁻¹ = a * b * a * b * a * b * a := by rw [haba_inv]; group
    _ = (a * b * a * b * a) * b * a := by group
    _ = b * b * a := by rw [ggDihedral_ababa ha hb hbraid]
    _ = a := by rw [hb]; group

private lemma ggDihedral_conj_ab_a {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : (a * b) ^ 3 = 1) : (a * b) * a * (a * b)⁻¹ = b := by
  have ha_inv : a⁻¹ = a := ggInv_of_sq_eq_one ha
  have hb_inv : b⁻¹ = b := ggInv_of_sq_eq_one hb
  have hbraid : a * b * a = b * a * b := ggDihedral_braid ha hb hab
  have hab_inv : (a * b)⁻¹ = b * a := by rw [mul_inv_rev, ha_inv, hb_inv]
  calc (a * b) * a * (a * b)⁻¹ = a * b * a * b * a := by rw [hab_inv]; group
    _ = b := ggDihedral_ababa ha hb hbraid

private lemma ggDihedral_conj_ab_b {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : (a * b) ^ 3 = 1) : (a * b) * b * (a * b)⁻¹ = a * b * a := by
  have ha_inv : a⁻¹ = a := ggInv_of_sq_eq_one ha
  have hb_inv : b⁻¹ = b := ggInv_of_sq_eq_one hb
  have hab_inv : (a * b)⁻¹ = b * a := by rw [mul_inv_rev, ha_inv, hb_inv]
  calc (a * b) * b * (a * b)⁻¹ = a * b * b * b * a := by rw [hab_inv]; group
    _ = a * b * (b * b) * a := by group
    _ = a * b * a := by rw [hb]; group

private lemma ggDihedral_conj_ba_a {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : (a * b) ^ 3 = 1) : (b * a) * a * (b * a)⁻¹ = a * b * a := by
  have ha_inv : a⁻¹ = a := ggInv_of_sq_eq_one ha
  have hb_inv : b⁻¹ = b := ggInv_of_sq_eq_one hb
  have hbraid : a * b * a = b * a * b := ggDihedral_braid ha hb hab
  have hba_inv : (b * a)⁻¹ = a * b := by rw [mul_inv_rev, ha_inv, hb_inv]
  calc (b * a) * a * (b * a)⁻¹ = b * a * a * a * b := by rw [hba_inv]; group
    _ = b * (a * a) * a * b := by group
    _ = b * a * b := by rw [ha]; group
    _ = a * b * a := hbraid.symm

private lemma ggDihedral_conj_ba_b {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : (a * b) ^ 3 = 1) : (b * a) * b * (b * a)⁻¹ = a := by
  have ha_inv : a⁻¹ = a := ggInv_of_sq_eq_one ha
  have hb_inv : b⁻¹ = b := ggInv_of_sq_eq_one hb
  have hbraid : a * b * a = b * a * b := ggDihedral_braid ha hb hab
  have hba_inv : (b * a)⁻¹ = a * b := by rw [mul_inv_rev, ha_inv, hb_inv]
  calc (b * a) * b * (b * a)⁻¹ = b * a * b * a * b := by rw [hba_inv]; group
    _ = a := ggDihedral_babab ha hb hbraid

private lemma ggDihedral_conj_a {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : (a * b) ^ 3 = 1) :
    ∀ r : G, (r = a ∨ r = b ∨ r = a * b * a) →
      (a * r * a⁻¹ = a ∨ a * r * a⁻¹ = b ∨ a * r * a⁻¹ = a * b * a) := by
  have ha_inv : a⁻¹ = a := ggInv_of_sq_eq_one ha
  intro r hr
  rcases hr with rfl | rfl | rfl
  · left; simp [ha, ha_inv]
  · right; right; rw [ha_inv]
  · right; left
    calc a * (a * b * a) * a⁻¹ = a * a * b * a * a := by rw [ha_inv]; group
      _ = (a * a) * b * (a * a) := by group
      _ = b := by rw [ha]; group

private lemma ggDihedral_conj_b {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : (a * b) ^ 3 = 1) :
    ∀ r : G, (r = a ∨ r = b ∨ r = a * b * a) →
      (b * r * b⁻¹ = a ∨ b * r * b⁻¹ = b ∨ b * r * b⁻¹ = a * b * a) := by
  have hb_inv : b⁻¹ = b := ggInv_of_sq_eq_one hb
  have hbraid : a * b * a = b * a * b := ggDihedral_braid ha hb hab
  intro r hr
  rcases hr with rfl | rfl | rfl
  · right; right; rw [hb_inv]; exact hbraid.symm
  · right; left; simp [hb, hb_inv]
  · left
    calc b * (a * b * a) * b⁻¹ = b * a * b * a * b := by rw [hb_inv]; group
      _ = a := ggDihedral_babab ha hb hbraid

theorem ggDihedral_pair {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) ^ 3 = 1) {t t' : G} (ht : t = a ∨ t = b ∨ t = a * b * a)
    (ht' : t' = a ∨ t' = b ∨ t' = a * b * a) (hne : t ≠ t') :
    ∃ w : G, w * a * w⁻¹ = t ∧ w * b * w⁻¹ = t' := by
  have ha_inv : a⁻¹ = a := ggInv_of_sq_eq_one ha
  have hb_inv : b⁻¹ = b := ggInv_of_sq_eq_one hb
  have hbraid : a * b * a = b * a * b := ggDihedral_braid ha hb hab
  have hbab : b * a * b = a * b * a := hbraid.symm
  rcases ht with hta | htb | htaba
  · rw [hta] at hne ⊢
    rcases ht' with ht'a | ht'b | ht'aba
    · rw [ht'a] at hne
      exact absurd rfl hne
    · rw [ht'b] at hne ⊢
      exact ⟨1, by simp, by simp⟩
    · rw [ht'aba] at hne ⊢
      exact ⟨a, by simp [ha, ha_inv], by rw [ha_inv]⟩
  · rw [htb] at hne ⊢
    rcases ht' with ht'a | ht'b | ht'aba
    · rw [ht'a] at hne ⊢
      exact ⟨a * b * a, ggDihedral_conj_aba_a ha hb hab, ggDihedral_conj_aba_b ha hb hab⟩
    · rw [ht'b] at hne
      exact absurd rfl hne
    · rw [ht'aba] at hne ⊢
      exact ⟨a * b, ggDihedral_conj_ab_a ha hb hab, ggDihedral_conj_ab_b ha hb hab⟩
  · rw [htaba] at hne ⊢
    rcases ht' with ht'a | ht'b | ht'aba
    · rw [ht'a] at hne ⊢
      exact ⟨b * a, ggDihedral_conj_ba_a ha hb hab, ggDihedral_conj_ba_b ha hb hab⟩
    · rw [ht'b] at hne ⊢
      exact ⟨b, by rw [hb_inv]; exact hbab, by simp [hb, hb_inv]⟩
    · rw [ht'aba] at hne
      exact absurd rfl hne

theorem ggDihedral_conj_mem {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) ^ 3 = 1) {v : G} (hv : v ∈ Subgroup.closure ({a, b} : Set G)) {k : G}
    (hk : k = a ∨ k = b) :
    v * k * v⁻¹ = a ∨ v * k * v⁻¹ = b ∨ v * k * v⁻¹ = a * b * a := by
  have ha_inv : a⁻¹ = a := ggInv_of_sq_eq_one ha
  have hb_inv : b⁻¹ = b := ggInv_of_sq_eq_one hb
  have key : ∀ w : G, w ∈ Subgroup.closure ({a, b} : Set G) →
      ∀ r : G, (r = a ∨ r = b ∨ r = a * b * a) →
        (w * r * w⁻¹ = a ∨ w * r * w⁻¹ = b ∨ w * r * w⁻¹ = a * b * a) := by
    intro w hw
    refine Subgroup.closure_induction''
      (p := fun w _ => ∀ r : G, (r = a ∨ r = b ∨ r = a * b * a) →
        (w * r * w⁻¹ = a ∨ w * r * w⁻¹ = b ∨ w * r * w⁻¹ = a * b * a)) ?_ ?_ ?_ ?_ hw
    · intro x hx
      rcases hx with rfl | rfl
      · exact ggDihedral_conj_a ha hb hab
      · exact ggDihedral_conj_b ha hb hab
    · intro x hx
      rcases hx with rfl | rfl
      · simpa [ha_inv] using ggDihedral_conj_a ha hb hab
      · simpa [hb_inv] using ggDihedral_conj_b ha hb hab
    · intro r hr
      simpa using hr
    · intro x y hx hy hpx hpy r hr
      have hxy := hpx (y * r * y⁻¹) (hpy r hr)
      rw [show (x * y) * r * (x * y)⁻¹ = x * (y * r * y⁻¹) * x⁻¹ by group]
      exact hxy
  rcases hk with hka | hkb
  · exact key v hv k (Or.inl hka)
  · exact key v hv k (Or.inr (Or.inl hkb))

private lemma ggCox_sq {ι : Type*} {M : CoxeterMatrix ι} (i : ι) :
    M.simple i * M.simple i = 1 := by
  simpa [CoxeterMatrix.toCoxeterSystem_simple] using M.toCoxeterSystem.simple_mul_simple_self i

private lemma ggCox_pow {ι : Type*} {M : CoxeterMatrix ι} (i j : ι) :
    (M.simple i * M.simple j) ^ M.M i j = 1 := by
  simpa [CoxeterMatrix.toCoxeterSystem_simple] using M.toCoxeterSystem.simple_mul_simple_pow i j

private lemma ggCox_inv {ι : Type*} {M : CoxeterMatrix ι} (i : ι) :
    (M.simple i)⁻¹ = M.simple i := ggInv_of_sq_eq_one (ggCox_sq i)

private lemma ggCox_comm_of_sq {ι : Type*} {M : CoxeterMatrix ι} {i j : ι}
    (h : (M.simple i * M.simple j) ^ 2 = 1) :
    M.simple i * M.simple j = M.simple j * M.simple i := by
  have h2 : (M.simple i * M.simple j) * (M.simple i * M.simple j) = 1 := by
    simpa [pow_two] using h
  have hinv : (M.simple i * M.simple j)⁻¹ = M.simple i * M.simple j :=
    (mul_eq_one_iff_inv_eq).mp h2
  calc M.simple i * M.simple j = (M.simple i * M.simple j)⁻¹ := hinv.symm
    _ = (M.simple j)⁻¹ * (M.simple i)⁻¹ := mul_inv_rev _ _
    _ = M.simple j * M.simple i := by rw [ggCox_inv i, ggCox_inv j]

private lemma ggConj_word_xyz_left {G : Type*} [Group G] {x y z : G} (hx2 : x * x = 1)
    (hy2 : y * y = 1) (hz2 : z * z = 1) (hxy : x * y * x = y * x * y)
    (hyz : y * z * y = z * y * z) (hxz : x * z = z * x) :
    (x * y * z) * x * (x * y * z)⁻¹ = y := by
  have hx_inv : x⁻¹ = x := ggInv_of_sq_eq_one hx2
  have hy_inv : y⁻¹ = y := ggInv_of_sq_eq_one hy2
  have hz_inv : z⁻¹ = z := ggInv_of_sq_eq_one hz2
  calc (x * y * z) * x * (x * y * z)⁻¹ = x * y * (z * x * z) * y * x := by
        rw [mul_inv_rev, mul_inv_rev, hz_inv, hy_inv, hx_inv]; group
    _ = x * y * (x * (z * z)) * y * x := by rw [hxz.symm]; group
    _ = x * y * x * y * x := by rw [hz2]; group
    _ = (x * y * x) * y * x := by group
    _ = (y * x * y) * y * x := by rw [hxy]
    _ = y * x * (y * y) * x := by group
    _ = y * (x * x) := by rw [hy2]; group
    _ = y := by rw [hx2]; group

private lemma ggConj_word_xyz_right {G : Type*} [Group G] {x y z : G} (hx2 : x * x = 1)
    (hy2 : y * y = 1) (hz2 : z * z = 1) (hxy : x * y * x = y * x * y)
    (hyz : y * z * y = z * y * z) (hxz : x * z = z * x) :
    (x * y * z) * y * (x * y * z)⁻¹ = z := by
  have hx_inv : x⁻¹ = x := ggInv_of_sq_eq_one hx2
  have hy_inv : y⁻¹ = y := ggInv_of_sq_eq_one hy2
  have hz_inv : z⁻¹ = z := ggInv_of_sq_eq_one hz2
  calc (x * y * z) * y * (x * y * z)⁻¹ = x * y * (z * y * z) * y * x := by
        rw [mul_inv_rev, mul_inv_rev, hz_inv, hy_inv, hx_inv]; group
    _ = x * (y * z * y) * z * y * x := by group
    _ = x * (z * y * z) * z * y * x := by rw [hyz]
    _ = x * z * y * (z * z) * y * x := by group
    _ = x * z * (y * y) * x := by rw [hz2]; group
    _ = x * z * x := by rw [hy2]; group
    _ = z * (x * x) := by rw [hxz]; group
    _ = z := by rw [hx2]; group

private lemma ggEdge_pivot {ι : Type*} {M : CoxeterMatrix ι}
    (htri : ∀ a b c : ι, M.M a b = 3 → M.M b c = 3 → a ≠ c → M.M a c = 2)
    {x y z : ι} (hxy : M.M x y = 3) (hyz : M.M y z = 3) :
    ∃ w' : M.Group, w' * M.simple x * w'⁻¹ = M.simple y ∧
      w' * M.simple y * w'⁻¹ = M.simple z := by
  by_cases hxz : x = z
  · have hz_eq : z = x := hxz.symm
    have hx2 : M.simple x * M.simple x = 1 := ggCox_sq x
    have hy2 : M.simple y * M.simple y = 1 := ggCox_sq y
    have hxy3 : (M.simple x * M.simple y) ^ 3 = 1 := by simpa [hxy] using ggCox_pow (M := M) x y
    refine ⟨M.simple x * M.simple y * M.simple x, ?_, ?_⟩
    · exact ggDihedral_conj_aba_a hx2 hy2 hxy3
    · rw [hz_eq]; exact ggDihedral_conj_aba_b hx2 hy2 hxy3
  · have hxz2 : M.M x z = 2 := htri x y z hxy hyz hxz
    have hx2 : M.simple x * M.simple x = 1 := ggCox_sq x
    have hy2 : M.simple y * M.simple y = 1 := ggCox_sq y
    have hz2 : M.simple z * M.simple z = 1 := ggCox_sq z
    have hxy3 : (M.simple x * M.simple y) ^ 3 = 1 := by simpa [hxy] using ggCox_pow (M := M) x y
    have hyz3 : (M.simple y * M.simple z) ^ 3 = 1 := by simpa [hyz] using ggCox_pow (M := M) y z
    have hxz2' : (M.simple x * M.simple z) ^ 2 = 1 := by simpa [hxz2] using ggCox_pow (M := M) x z
    have hbraid_xy : M.simple x * M.simple y * M.simple x = M.simple y * M.simple x * M.simple y :=
      ggDihedral_braid hx2 hy2 hxy3
    have hbraid_yz : M.simple y * M.simple z * M.simple y = M.simple z * M.simple y * M.simple z :=
      ggDihedral_braid hy2 hz2 hyz3
    have hcomm_xz : M.simple x * M.simple z = M.simple z * M.simple x := ggCox_comm_of_sq hxz2'
    refine ⟨M.simple x * M.simple y * M.simple z, ?_, ?_⟩
    · exact ggConj_word_xyz_left hx2 hy2 hz2 hbraid_xy hbraid_yz hcomm_xz
    · exact ggConj_word_xyz_right hx2 hy2 hz2 hbraid_xy hbraid_yz hcomm_xz

theorem ggEdge_conj {ι : Type} {M : CoxeterMatrix ι}
    (hconn : ∀ i j : ι, Relation.ReflTransGen (fun a b : ι => M.M a b = 3) i j)
    (htri : ∀ a b c : ι, M.M a b = 3 → M.M b c = 3 → a ≠ c → M.M a c = 2)
    {a b c d : ι} (hab : M.M a b = 3) (hcd : M.M c d = 3) :
    ∃ w : M.Group, w * M.simple a * w⁻¹ = M.simple c ∧ w * M.simple b * w⁻¹ = M.simple d := by
  let P : ι → ι → Prop := fun x y => ∃ w : M.Group,
    w * M.simple a * w⁻¹ = M.simple x ∧ w * M.simple b * w⁻¹ = M.simple y
  have hPstep : ∀ x y z : ι, M.M x y = 3 → M.M y z = 3 → P x y → P y z := by
    intro x y z hxy hyz hP
    obtain ⟨w, hw1, hw2⟩ := hP
    obtain ⟨w', hw'1, hw'2⟩ := ggEdge_pivot htri hxy hyz
    refine ⟨w' * w, ?_, ?_⟩
    · calc (w' * w) * M.simple a * (w' * w)⁻¹ = w' * (w * M.simple a * w⁻¹) * w'⁻¹ := by group
        _ = w' * M.simple x * w'⁻¹ := by rw [hw1]
        _ = M.simple y := hw'1
    · calc (w' * w) * M.simple b * (w' * w)⁻¹ = w' * (w * M.simple b * w⁻¹) * w'⁻¹ := by group
        _ = w' * M.simple y * w'⁻¹ := by rw [hw2]
        _ = M.simple z := hw'2
  have hreach : ∀ z : ι, Relation.ReflTransGen (fun a b : ι => M.M a b = 3) b z →
      ∃ y, M.M y z = 3 ∧ P y z := by
    intro z hz
    induction hz with
    | refl => exact ⟨a, hab, ⟨1, by simp, by simp⟩⟩
    | tail _ hstep ih =>
        obtain ⟨y, hy_mid, hPy⟩ := ih
        exact ⟨_, hstep, hPstep y _ _ hy_mid hstep hPy⟩
  obtain ⟨y, hyc, hPyc⟩ := hreach c (hconn b c)
  exact hPstep y c d hyc hcd hPyc

end DihedralEdges

open CFSG.LieType.RootSystem

variable {ι : Type}

private theorem ggIntCartan_three {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ} (hC : GGIntCartan M C)
    {a b : ι} (hab : a ≠ b) (hm : M a b = 3) : C a b = -1 ∧ C b a = -1 := by
  rcases hC.2 a b hab with ⟨h2, -⟩ | ⟨-, h1, h2⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · exfalso; omega
  · exact ⟨h1, h2⟩
  · exfalso; omega
  · exfalso; omega

private theorem coxeter_simple_comm {M : CoxeterMatrix ι} {W : Type*} [Group W]
    (cs : CoxeterSystem M W) {j k : ι} (h : M.M j k = 2) :
    cs.simple j * cs.simple k = cs.simple k * cs.simple j := by
  have hsq : (cs.simple j * cs.simple k) ^ 2 = 1 := by
    simpa [h] using cs.simple_mul_simple_pow j k
  have hxx : (cs.simple j * cs.simple k) * (cs.simple j * cs.simple k) = 1 := by
    simpa [pow_two] using hsq
  calc cs.simple j * cs.simple k
      = (cs.simple j * cs.simple k)⁻¹ := (inv_eq_of_mul_eq_one_right hxx).symm
    _ = (cs.simple k)⁻¹ * (cs.simple j)⁻¹ := by rw [mul_inv_rev]
    _ = cs.simple k * cs.simple j := by
        rw [inv_eq_of_mul_eq_one_right (cs.simple_mul_simple_self k),
          inv_eq_of_mul_eq_one_right (cs.simple_mul_simple_self j)]

private theorem ggParabolic_singleton_central {M : CoxeterMatrix ι} {W : Type*} [Group W]
    (cs : CoxeterSystem M W) (i : ι) :
    cs.parabolic ({i} : Set ι) ≤ Subgroup.centralizer ({cs.simple i} : Set W) := by
  rw [cs.parabolic_le_iff]
  intro k hk
  rw [Set.mem_singleton_iff] at hk
  subst hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact rfl

private theorem ggParabolic_pair_central {M : CoxeterMatrix ι} {W : Type*} [Group W]
    (cs : CoxeterSystem M W) {j k : ι}
    (hcomm : cs.simple j * cs.simple k = cs.simple k * cs.simple j) :
    cs.parabolic ({j, k} : Set ι) ≤
      Subgroup.centralizer ({cs.simple j, cs.simple k} : Set W) := by
  rw [cs.parabolic_le_iff]
  intro i hi
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hi with rfl | rfl <;> rcases hy with rfl | rfl
  · exact rfl
  · exact hcomm.symm
  · exact hcomm
  · exact rfl

private theorem ggParabolic_pair_le_closure {M : CoxeterMatrix ι} {W : Type*} [Group W]
    (cs : CoxeterSystem M W) (j k : ι) :
    cs.parabolic ({j, k} : Set ι) ≤
      Subgroup.closure ({cs.simple j, cs.simple k} : Set W) := by
  rw [cs.parabolic_le_iff]
  intro i hi
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

private theorem conj_eq_self_of_comm {G : Type*} [Group G] {z s : G} (h : s * z = z * s) :
    z⁻¹ * s * z = s := by
  have h' : z⁻¹ * s = s * z⁻¹ := by
    calc z⁻¹ * s = z⁻¹ * s * (z * z⁻¹) := by group
      _ = z⁻¹ * (s * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * s) * z⁻¹ := by rw [← h]
      _ = s * z⁻¹ := by group
  rw [h', mul_assoc, inv_mul_cancel, mul_one]

private theorem simple_conj_mul_self {M : CoxeterMatrix ι} {t : M.Group}
    (ht : ∃ (w : M.Group) (i : ι), t = w * M.toCoxeterSystem.simple i * w⁻¹) : t * t = 1 := by
  obtain ⟨w, i, rfl⟩ := ht
  rw [show (w * M.toCoxeterSystem.simple i * w⁻¹) *
        (w * M.toCoxeterSystem.simple i * w⁻¹) =
        w * (M.toCoxeterSystem.simple i * M.toCoxeterSystem.simple i) * w⁻¹ by group,
    M.toCoxeterSystem.simple_mul_simple_self i, mul_one, mul_inv_cancel]

private theorem ggA2_no_triangle [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℤ}
    (hC : TauCeti.IsFiniteType C) (hCart : GGIntCartan (coxeterMatrix hC) C) :
    ∀ a b c : ι, (coxeterMatrix hC).M a b = 3 → (coxeterMatrix hC).M b c = 3 → a ≠ c →
      (coxeterMatrix hC).M a c = 2 := by
  intro a b c hab hbc hac
  have hab_ne : a ≠ b := by
    rintro rfl
    simp [CoxeterMatrix.diagonal] at hab
  have hbc_ne : b ≠ c := by
    rintro rfl
    simp [CoxeterMatrix.diagonal] at hbc
  have hba : C b a = -1 := (ggIntCartan_three hCart hab_ne hab).2
  have hbc' : C b c = -1 := (ggIntCartan_three hCart hbc_ne hbc).1
  have hCac : C a c = 0 :=
    TauCeti.IsFiniteType.apply_eq_zero_of_apply_ne_zero hC hab_ne.symm hbc_ne hac
      (by rw [hba]; norm_num) (by rw [hbc']; norm_num)
  rcases hCart.2 a c hac with ⟨hm2, -, -⟩ | ⟨hm3, h1, -⟩ | ⟨hm4, -, h2, -⟩ | ⟨hm6, -, h2, -⟩
  · exact hm2
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

private theorem ggA2_edge [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℤ}
    (hC : TauCeti.IsFiniteType C) (hsl : GGSimplyLaced (coxeterMatrix hC))
    {t t' : (coxeterMatrix hC).Group}
    (ht : ∃ (w : (coxeterMatrix hC).Group) (i : ι),
      t = w * (coxeterMatrix hC).toCoxeterSystem.simple i * w⁻¹)
    (ht' : ∃ (w : (coxeterMatrix hC).Group) (i : ι),
      t' = w * (coxeterMatrix hC).toCoxeterSystem.simple i * w⁻¹)
    (hne : t ≠ t') (hord : (t * t') ^ 3 = 1) :
    ∃ (j k : ι) (w : (coxeterMatrix hC).Group),
      (coxeterMatrix hC).M j k = 3 ∧
        w * (coxeterMatrix hC).toCoxeterSystem.simple j * w⁻¹ = t ∧
        w * (coxeterMatrix hC).toCoxeterSystem.simple k * w⁻¹ = t' := by
  classical
  let cs : CoxeterSystem (coxeterMatrix hC) (coxeterMatrix hC).Group :=
    (coxeterMatrix hC).toCoxeterSystem
  have htt : t * t = 1 := simple_conj_mul_self ht
  have ht't' : t' * t' = 1 := simple_conj_mul_self ht'
  obtain ⟨w₁, r₁, ht₁⟩ := ht
  obtain ⟨w₂, r₂, ht₂⟩ := ht'
  have hγ : weylAction hC w₁ (Pi.single r₁ 1) ∈ roots hC (∅ : Set ι) :=
    Or.inl ⟨w₁, r₁, rfl⟩
  have hγ' : weylAction hC w₂ (Pi.single r₂ 1) ∈ roots hC (∅ : Set ι) :=
    Or.inl ⟨w₂, r₂, rfl⟩
  obtain ⟨u, J, hJcard, hsupp⟩ := exists_weylAction_support_subset hC (∅ : Set ι) hγ hγ'
  have hsuppγ : ∀ k ∉ J, weylAction hC (u * w₁) (Pi.single r₁ 1) k = 0 := by
    intro k hk
    rw [weylAction_mul_apply]
    exact hsupp _ hγ ⟨1, 0, fun k => by simp⟩ k hk
  have hsuppγ' : ∀ k ∉ J, weylAction hC (u * w₂) (Pi.single r₂ 1) k = 0 := by
    intro k hk
    rw [weylAction_mul_apply]
    exact hsupp _ hγ' ⟨0, 1, fun k => by simp⟩ k hk
  obtain ⟨z₁, hz₁, m, hmJ, hzm⟩ := exists_parabolic_of_support hC (J : Set ι) (u * w₁) r₁ hsuppγ
  obtain ⟨z₂, hz₂, m', hm'J, hzm'⟩ :=
    exists_parabolic_of_support hC (J : Set ι) (u * w₂) r₂ hsuppγ'
  have hroot₁ : weylAction hC (z₁ * (u * w₁)) (Pi.single r₁ 1) = Pi.single m 1 := by
    rw [weylAction_mul_apply]; exact hzm
  have hroot₂ : weylAction hC (z₂ * (u * w₂)) (Pi.single r₂ 1) = Pi.single m' 1 := by
    rw [weylAction_mul_apply]; exact hzm'
  have hconcat₁ : toRat (weylAction hC (z₁ * (u * w₁)) (Pi.single r₁ 1)) =
      1 • toRat (weylAction hC 1 (Pi.single m 1)) := by
    rw [hroot₁]; simp
  have hconcat₂ : toRat (weylAction hC (z₂ * (u * w₂)) (Pi.single r₂ 1)) =
      1 • toRat (weylAction hC 1 (Pi.single m' 1)) := by
    rw [hroot₂]; simp
  have hconj₁ := ggWeyl_conj_simple_eq_of_root_smul hC (z₁ * (u * w₁)) 1 r₁ m one_ne_zero hconcat₁
  have hconj₂ := ggWeyl_conj_simple_eq_of_root_smul hC (z₂ * (u * w₂)) 1 r₂ m' one_ne_zero hconcat₂
  have hz1t : z₁ * (u * t * u⁻¹) * z₁⁻¹ =
      (coxeterMatrix hC).toCoxeterSystem.simple m := by
    have h1 : z₁ * (u * t * u⁻¹) * z₁⁻¹ =
        (z₁ * (u * w₁)) * (coxeterMatrix hC).toCoxeterSystem.simple r₁ *
          (z₁ * (u * w₁))⁻¹ := by
      rw [ht₁]; group
    rw [h1, hconj₁]; simp
  have hz2t : z₂ * (u * t' * u⁻¹) * z₂⁻¹ =
      (coxeterMatrix hC).toCoxeterSystem.simple m' := by
    have h1 : z₂ * (u * t' * u⁻¹) * z₂⁻¹ =
        (z₂ * (u * w₂)) * (coxeterMatrix hC).toCoxeterSystem.simple r₂ *
          (z₂ * (u * w₂))⁻¹ := by
      rw [ht₂]; group
    rw [h1, hconj₂]; simp
  have hJpos : 0 < J.card := Finset.card_pos.mpr ⟨m, hmJ⟩
  have hcard : J.card = 1 ∨ J.card = 2 := by omega
  rcases hcard with h1 | h2
  ·
    obtain ⟨m₀, hJ⟩ := Finset.card_eq_one.mp h1
    have hm_eq : m = m₀ := by simpa [hJ] using hmJ
    have hm'_eq : m' = m₀ := by simpa [hJ] using hm'J
    have hz₁' : z₁ ∈ cs.parabolic ({m₀} : Set ι) := by
      have : z₁ ∈ cs.parabolic (({m₀} : Finset ι) : Set ι) := by simpa [hJ] using hz₁
      simpa using this
    have hz₂' : z₂ ∈ cs.parabolic ({m₀} : Set ι) := by
      have : z₂ ∈ cs.parabolic (({m₀} : Finset ι) : Set ι) := by simpa [hJ] using hz₂
      simpa using this
    have hcomm₁ : cs.simple m₀ * z₁ = z₁ * cs.simple m₀ :=
      (Subgroup.mem_centralizer_iff.mp ((ggParabolic_singleton_central cs m₀) hz₁'))
        (cs.simple m₀) (by simp)
    have hcomm₂ : cs.simple m₀ * z₂ = z₂ * cs.simple m₀ :=
      (Subgroup.mem_centralizer_iff.mp ((ggParabolic_singleton_central cs m₀) hz₂'))
        (cs.simple m₀) (by simp)
    have hz1s : z₁⁻¹ * (coxeterMatrix hC).toCoxeterSystem.simple m * z₁ =
        (coxeterMatrix hC).toCoxeterSystem.simple m := by
      rw [hm_eq]; exact conj_eq_self_of_comm hcomm₁
    have hz2s : z₂⁻¹ * (coxeterMatrix hC).toCoxeterSystem.simple m' * z₂ =
        (coxeterMatrix hC).toCoxeterSystem.simple m' := by
      rw [hm'_eq]; exact conj_eq_self_of_comm hcomm₂
    have hut : u * t * u⁻¹ = (coxeterMatrix hC).toCoxeterSystem.simple m := by
      have h := congrArg (fun x => z₁⁻¹ * x * z₁) hz1t
      rw [show z₁⁻¹ * (z₁ * (u * t * u⁻¹) * z₁⁻¹) * z₁ = u * t * u⁻¹ by group, hz1s] at h
      exact h
    have hut' : u * t' * u⁻¹ = (coxeterMatrix hC).toCoxeterSystem.simple m' := by
      have h := congrArg (fun x => z₂⁻¹ * x * z₂) hz2t
      rw [show z₂⁻¹ * (z₂ * (u * t' * u⁻¹) * z₂⁻¹) * z₂ = u * t' * u⁻¹ by group, hz2s] at h
      exact h
    have hsame : t = t' := by
      have hc : u * t * u⁻¹ = u * t' * u⁻¹ := by rw [hut, hut', hm_eq, hm'_eq]
      have h := congrArg (fun x => u⁻¹ * x * u) hc
      rwa [show u⁻¹ * (u * t * u⁻¹) * u = t by group,
        show u⁻¹ * (u * t' * u⁻¹) * u = t' by group] at h
    exact absurd hsame hne
  ·
    obtain ⟨j, k, hjk_ne, hJ⟩ := Finset.card_eq_two.mp h2
    have hm_cases : m = j ∨ m = k := by
      have : m ∈ ({j, k} : Finset ι) := by simpa [hJ] using hmJ
      simpa using this
    have hm'_cases : m' = j ∨ m' = k := by
      have : m' ∈ ({j, k} : Finset ι) := by simpa [hJ] using hm'J
      simpa using this
    have hz₁' : z₁ ∈ cs.parabolic ({j, k} : Set ι) := by
      have : z₁ ∈ cs.parabolic (({j, k} : Finset ι) : Set ι) := by simpa [hJ] using hz₁
      simpa using this
    have hz₂' : z₂ ∈ cs.parabolic ({j, k} : Set ι) := by
      have : z₂ ∈ cs.parabolic (({j, k} : Finset ι) : Set ι) := by simpa [hJ] using hz₂
      simpa using this
    rcases hsl j k hjk_ne with hjk2 | hjk3
    ·
      have hcommjk : cs.simple j * cs.simple k = cs.simple k * cs.simple j :=
        coxeter_simple_comm cs hjk2
      have hcent := ggParabolic_pair_central cs hcommjk
      have hmemj : cs.simple m ∈ ({cs.simple j, cs.simple k} : Set (coxeterMatrix hC).Group) := by
        rcases hm_cases with h | h
        · rw [h]; simp
        · rw [h]; simp
      have hmemj' : cs.simple m' ∈ ({cs.simple j, cs.simple k} : Set (coxeterMatrix hC).Group) := by
        rcases hm'_cases with h | h
        · rw [h]; simp
        · rw [h]; simp
      have hcommm : cs.simple m * z₁ = z₁ * cs.simple m :=
        (Subgroup.mem_centralizer_iff.mp (hcent hz₁')) (cs.simple m) hmemj
      have hcommm' : cs.simple m' * z₂ = z₂ * cs.simple m' :=
        (Subgroup.mem_centralizer_iff.mp (hcent hz₂')) (cs.simple m') hmemj'
      have hsmsm' : cs.simple m * cs.simple m' = cs.simple m' * cs.simple m := by
        rcases hm_cases with hmj | hmk <;> rcases hm'_cases with hm'j | hm'k
        · rw [hmj, hm'j]
        · rw [hmj, hm'k]; exact hcommjk
        · rw [hmk, hm'j]; exact hcommjk.symm
        · rw [hmk, hm'k]
      have hz1s : z₁⁻¹ * (coxeterMatrix hC).toCoxeterSystem.simple m * z₁ =
          (coxeterMatrix hC).toCoxeterSystem.simple m := conj_eq_self_of_comm hcommm
      have hz2s : z₂⁻¹ * (coxeterMatrix hC).toCoxeterSystem.simple m' * z₂ =
          (coxeterMatrix hC).toCoxeterSystem.simple m' := conj_eq_self_of_comm hcommm'
      have hut : u * t * u⁻¹ = (coxeterMatrix hC).toCoxeterSystem.simple m := by
        have h := congrArg (fun x => z₁⁻¹ * x * z₁) hz1t
        rw [show z₁⁻¹ * (z₁ * (u * t * u⁻¹) * z₁⁻¹) * z₁ = u * t * u⁻¹ by group, hz1s] at h
        exact h
      have hut' : u * t' * u⁻¹ = (coxeterMatrix hC).toCoxeterSystem.simple m' := by
        have h := congrArg (fun x => z₂⁻¹ * x * z₂) hz2t
        rw [show z₂⁻¹ * (z₂ * (u * t' * u⁻¹) * z₂⁻¹) * z₂ = u * t' * u⁻¹ by group, hz2s] at h
        exact h
      have hcomm_tt' : t * t' = t' * t := by
        have hc : (u * t * u⁻¹) * (u * t' * u⁻¹) = (u * t' * u⁻¹) * (u * t * u⁻¹) := by
          rw [hut, hut']; exact hsmsm'
        have h := congrArg (fun x => u⁻¹ * x * u) hc
        rwa [show u⁻¹ * ((u * t * u⁻¹) * (u * t' * u⁻¹)) * u = t * t' by group,
          show u⁻¹ * ((u * t' * u⁻¹) * (u * t * u⁻¹)) * u = t' * t by group] at h
      have h2 : (t * t') ^ 2 = 1 := by
        rw [pow_two]
        calc (t * t') * (t * t') = t * (t' * t) * t' := by group
          _ = t * (t * t') * t' := by rw [← hcomm_tt']
          _ = (t * t) * (t' * t') := by group
          _ = 1 := by rw [htt, ht't', mul_one]
      have h3eq : t * t' = 1 := by
        have h := hord
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, h2, one_mul] at h
        exact h
      have hsame : t = t' := by
        rw [eq_inv_of_mul_eq_one_left h3eq]
        exact inv_eq_of_mul_eq_one_right ht't'
      exact absurd hsame hne
    ·
      have hle : cs.parabolic ({j, k} : Set ι) ≤
          Subgroup.closure ({cs.simple j, cs.simple k} : Set (coxeterMatrix hC).Group) :=
        ggParabolic_pair_le_closure cs j k
      have hz₁'' : z₁⁻¹ ∈
          Subgroup.closure ({cs.simple j, cs.simple k} : Set (coxeterMatrix hC).Group) :=
        inv_mem (hle hz₁')
      have hz₂'' : z₂⁻¹ ∈
          Subgroup.closure ({cs.simple j, cs.simple k} : Set (coxeterMatrix hC).Group) :=
        inv_mem (hle hz₂')
      have ha : cs.simple j * cs.simple j = 1 := cs.simple_mul_simple_self j
      have hb : cs.simple k * cs.simple k = 1 := cs.simple_mul_simple_self k
      have hab : (cs.simple j * cs.simple k) ^ 3 = 1 := by
        rw [← hjk3]
        exact cs.simple_mul_simple_pow j k
      have hm_k : cs.simple m = cs.simple j ∨ cs.simple m = cs.simple k := by
        rcases hm_cases with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])
      have hm'_k : cs.simple m' = cs.simple j ∨ cs.simple m' = cs.simple k := by
        rcases hm'_cases with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])
      have hmem₁ := ggDihedral_conj_mem ha hb hab hz₁'' hm_k
      have hmem₁' : z₁⁻¹ * cs.simple m * z₁ = cs.simple j ∨
          z₁⁻¹ * cs.simple m * z₁ = cs.simple k ∨
          z₁⁻¹ * cs.simple m * z₁ = cs.simple j * cs.simple k * cs.simple j := by
        simpa using hmem₁
      have hmem₂ := ggDihedral_conj_mem ha hb hab hz₂'' hm'_k
      have hmem₂' : z₂⁻¹ * cs.simple m' * z₂ = cs.simple j ∨
          z₂⁻¹ * cs.simple m' * z₂ = cs.simple k ∨
          z₂⁻¹ * cs.simple m' * z₂ = cs.simple j * cs.simple k * cs.simple j := by
        simpa using hmem₂
      have hut : u * t * u⁻¹ = z₁⁻¹ * cs.simple m * z₁ := by
        have h := congrArg (fun x => z₁⁻¹ * x * z₁) hz1t
        rw [show z₁⁻¹ * (z₁ * (u * t * u⁻¹) * z₁⁻¹) * z₁ = u * t * u⁻¹ by group] at h
        exact h
      have hut' : u * t' * u⁻¹ = z₂⁻¹ * cs.simple m' * z₂ := by
        have h := congrArg (fun x => z₂⁻¹ * x * z₂) hz2t
        rw [show z₂⁻¹ * (z₂ * (u * t' * u⁻¹) * z₂⁻¹) * z₂ = u * t' * u⁻¹ by group] at h
        exact h
      have hut₁ : u * t * u⁻¹ = cs.simple j ∨ u * t * u⁻¹ = cs.simple k ∨
          u * t * u⁻¹ = cs.simple j * cs.simple k * cs.simple j := by
        rcases hmem₁' with h | h | h
        · exact Or.inl (hut.trans h)
        · exact Or.inr (Or.inl (hut.trans h))
        · exact Or.inr (Or.inr (hut.trans h))
      have hut₂ : u * t' * u⁻¹ = cs.simple j ∨ u * t' * u⁻¹ = cs.simple k ∨
          u * t' * u⁻¹ = cs.simple j * cs.simple k * cs.simple j := by
        rcases hmem₂' with h | h | h
        · exact Or.inl (hut'.trans h)
        · exact Or.inr (Or.inl (hut'.trans h))
        · exact Or.inr (Or.inr (hut'.trans h))
      have hne_u : u * t * u⁻¹ ≠ u * t' * u⁻¹ := by
        intro h
        apply hne
        have h' := congrArg (fun x => u⁻¹ * x * u) h
        rwa [show u⁻¹ * (u * t * u⁻¹) * u = t by group,
          show u⁻¹ * (u * t' * u⁻¹) * u = t' by group] at h'
      obtain ⟨w', hw'j, hw'k⟩ := ggDihedral_pair ha hb hab hut₁ hut₂ hne_u
      refine ⟨j, k, u⁻¹ * w', hjk3, ?_, ?_⟩
      · calc (u⁻¹ * w') * cs.simple j * (u⁻¹ * w')⁻¹
            = u⁻¹ * (w' * cs.simple j * w'⁻¹) * u := by group
          _ = u⁻¹ * (u * t * u⁻¹) * u := by rw [hw'j]
          _ = t := by group
      · calc (u⁻¹ * w') * cs.simple k * (u⁻¹ * w')⁻¹
            = u⁻¹ * (w' * cs.simple k * w'⁻¹) * u := by group
          _ = u⁻¹ * (u * t' * u⁻¹) * u := by rw [hw'k]
          _ = t' := by group

theorem ggA2_conj {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {t t' : M.Group} (ht : ∃ (w : M.Group) (i : ι), t = w * M.simple i * w⁻¹)
    (ht' : ∃ (w : M.Group) (i : ι), t' = w * M.simple i * w⁻¹) (hne : t ≠ t')
    (hord : (t * t') ^ 3 = 1) {i j : ι} (hij : M.M i j = 3) :
    ∃ w : M.Group, w * M.simple i * w⁻¹ = t ∧ w * M.simple j * w⁻¹ = t' := by
  haveI : Finite ι := ggIsWeylMatrix_finite hM
  haveI : Fintype ι := Fintype.ofFinite ι
  classical
  obtain ⟨C, hC, hCart, rfl⟩ := ggWeylCartan hM h3
  have hslc := ggSimplyLacedConnected_of_weyl hM h3
  have hsl : GGSimplyLaced (coxeterMatrix hC) := hslc.1
  have hconn : ∀ a b : ι,
      Relation.ReflTransGen (fun x y : ι => (coxeterMatrix hC).M x y = 3) a b := hslc.2
  have ht_cs : ∃ (w : (coxeterMatrix hC).Group) (i : ι),
      t = w * (coxeterMatrix hC).toCoxeterSystem.simple i * w⁻¹ := by
    obtain ⟨w, a, hw⟩ := ht
    exact ⟨w, a, by simpa only [CoxeterMatrix.toCoxeterSystem_simple] using hw⟩
  have ht'_cs : ∃ (w : (coxeterMatrix hC).Group) (i : ι),
      t' = w * (coxeterMatrix hC).toCoxeterSystem.simple i * w⁻¹ := by
    obtain ⟨w, a, hw⟩ := ht'
    exact ⟨w, a, by simpa only [CoxeterMatrix.toCoxeterSystem_simple] using hw⟩
  obtain ⟨j₀, k₀, w₀, hjk, hw₀t, hw₀t'⟩ :=
    ggA2_edge hC hsl ht_cs ht'_cs hne hord
  have htri : ∀ a b c : ι, (coxeterMatrix hC).M a b = 3 → (coxeterMatrix hC).M b c = 3 →
      a ≠ c → (coxeterMatrix hC).M a c = 2 := ggA2_no_triangle hC hCart
  obtain ⟨w'', hw''i, hw''j⟩ := ggEdge_conj hconn htri hjk hij
  have hw''i_cs : w'' * (coxeterMatrix hC).toCoxeterSystem.simple j₀ * w''⁻¹ =
      (coxeterMatrix hC).toCoxeterSystem.simple i := by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using hw''i
  have hw''j_cs : w'' * (coxeterMatrix hC).toCoxeterSystem.simple k₀ * w''⁻¹ =
      (coxeterMatrix hC).toCoxeterSystem.simple j := by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using hw''j
  have goal_cs : ∃ w : (coxeterMatrix hC).Group,
      w * (coxeterMatrix hC).toCoxeterSystem.simple i * w⁻¹ = t ∧
      w * (coxeterMatrix hC).toCoxeterSystem.simple j * w⁻¹ = t' := by
    refine ⟨w₀ * w''⁻¹, ?_, ?_⟩
    · calc (w₀ * w''⁻¹) * (coxeterMatrix hC).toCoxeterSystem.simple i * (w₀ * w''⁻¹)⁻¹
          = (w₀ * w''⁻¹) * (w'' * (coxeterMatrix hC).toCoxeterSystem.simple j₀ * w''⁻¹) *
              (w₀ * w''⁻¹)⁻¹ := by rw [hw''i_cs]
        _ = w₀ * (coxeterMatrix hC).toCoxeterSystem.simple j₀ * w₀⁻¹ := by group
        _ = t := hw₀t
    · calc (w₀ * w''⁻¹) * (coxeterMatrix hC).toCoxeterSystem.simple j * (w₀ * w''⁻¹)⁻¹
          = (w₀ * w''⁻¹) * (w'' * (coxeterMatrix hC).toCoxeterSystem.simple k₀ * w''⁻¹) *
              (w₀ * w''⁻¹)⁻¹ := by rw [hw''j_cs]
        _ = w₀ * (coxeterMatrix hC).toCoxeterSystem.simple k₀ * w₀⁻¹ := by group
        _ = t' := hw₀t'
  simpa only [CoxeterMatrix.toCoxeterSystem_simple] using goal_cs

end CFSG.StandardType

end