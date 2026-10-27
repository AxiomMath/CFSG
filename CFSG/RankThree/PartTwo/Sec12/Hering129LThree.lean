module

public import CFSG.RankThree.PartTwo.Sec12.Hering129LSL3
public import CFSG.RankThree.PartTwo.Sec12.Hering129HKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Conj

variable {X : Type} [Group X] [Finite X]

theorem centralizer_conj_eq_map (g z : X) :
    Subgroup.centralizer ({g * z * g⁻¹} : Set X) =
      (Subgroup.centralizer ({z} : Set X)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹ * x) * g := by rw [h]
      _ = z * (g⁻¹ * x * g) := by group
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
      _ = g * (z * y) * g⁻¹ := by rw [hy]
      _ = g * z * g⁻¹ * (g * y * g⁻¹) := by group

theorem resCent_top_conj (g z : X) :
    resCent (⊤ : Subgroup X) (g * z * g⁻¹) =
      (resCent (⊤ : Subgroup X) z).map (MulAut.conj g).toMonoidHom := by
  unfold resCent
  rw [top_inf_eq, top_inf_eq, centralizer_conj_eq_map, ← map_inSubgroup_perfectResidual]

noncomputable def resCentConjEquiv (g z : X) :
    ↥(resCent (⊤ : Subgroup X) z) ≃* ↥(resCent (⊤ : Subgroup X) (g * z * g⁻¹)) :=
  ((resCent (⊤ : Subgroup X) z).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr (resCent_top_conj g z).symm)

theorem mem_resCent_self_conj {g z : X} (h : z ∈ resCent (⊤ : Subgroup X) z) :
    g * z * g⁻¹ ∈ resCent (⊤ : Subgroup X) (g * z * g⁻¹) := by
  rw [resCent_top_conj]
  exact ⟨z, h, rfl⟩

theorem isThreeA_conj {z : X} {m : ℕ} (h : IsThreeA z m) (g : X) : IsThreeA (g * z * g⁻¹) m := by
  obtain ⟨h3, hz, hsl⟩ := h
  refine ⟨?_, mem_resCent_self_conj hz, isSLThreePiAt_congr (resCentConjEquiv g z) hsl⟩
  have := (MulAut.conj g).orderOf_eq z
  simpa [MulAut.conj_apply, h3] using this

theorem isThreeB_conj {z : X} {s : ℕ} (h : IsThreeB z s) (g : X) : IsThreeB (g * z * g⁻¹) s := by
  obtain ⟨h3, F, hF, hFf, hFc, ⟨e⟩⟩ := h
  refine ⟨?_, F, hF, hFf, hFc, ⟨(resCentConjEquiv g z).symm.trans e⟩⟩
  have := (MulAut.conj g).orderOf_eq z
  simpa [MulAut.conj_apply, h3] using this

theorem conj_mem_resCent_iff (g z w : X) :
    g * w * g⁻¹ ∈ resCent (⊤ : Subgroup X) (g * z * g⁻¹) ↔ w ∈ resCent (⊤ : Subgroup X) z := by
  rw [resCent_top_conj, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyw⟩
    have : y = w := (MulAut.conj g).injective (by simpa using hyw)
    exact this ▸ hy
  · intro h
    exact ⟨w, h, rfl⟩

theorem orderOf_conj_eq (g z : X) : orderOf (g * z * g⁻¹) = orderOf z := by
  simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq z

theorem mem_centralizer_of_mem_resCent {z w : X} (h : w ∈ resCent (⊤ : Subgroup X) z) :
    w * z = z * w := by
  have := (resCent_le ⊤ z) h
  exact Subgroup.mem_centralizer_singleton_iff.mp this.2

end Conj

section Exclusive

variable {X : Type} [Group X] [Finite X]

theorem not_isThreeA_and_isThreeB {z : X} {m s : ℕ} (hA : IsThreeA z m) (hB : IsThreeB z s) :
    False := by
  have hc3 : Nat.card (Subgroup.center ↥(resCent (⊤ : Subgroup X) z)) = 3 :=
    card_center_eq_three_of_isSLThreePi ⟨m, hA.2.2⟩
  obtain ⟨-, F, hF, hFfin, -, ⟨e⟩⟩ := hB
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥(resCent (⊤ : Subgroup X) z)) 3
      (by rw [hc3])
  have hy3 : (y : ↥(resCent (⊤ : Subgroup X) z)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    exact congrArg Subtype.val this
  have hy1 : (y : ↥(resCent (⊤ : Subgroup X) z)) ≠ 1 := by
    intro h
    have : y = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy
    omega
  have hcen : e (y : ↥(resCent (⊤ : Subgroup X) z)) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨w, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp y.2) w]
  have hsq : e (y : ↥(resCent (⊤ : Subgroup X) z)) ^ 2 = 1 := by
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow]
    have hr2 : r ^ 2 = 1 := by simpa using hr
    rw [hr2, map_one]
    rfl
  have hcu : e (y : ↥(resCent (⊤ : Subgroup X) z)) ^ 3 = 1 := by
    rw [← map_pow, hy3, map_one]
  have h1 : e (y : ↥(resCent (⊤ : Subgroup X) z)) = 1 := by
    calc e (y : ↥(resCent (⊤ : Subgroup X) z)) = e y ^ 3 * (e y ^ 2)⁻¹ := by group
      _ = 1 := by rw [hcu, hsq]; group
  exact hy1 (e.injective (by rw [h1, map_one]))

end Exclusive

section Center

variable {X : Type} [Group X] [Finite X]

theorem notMem_center_of_notMem_zpowers {z w : X} {m : ℕ} (hz : IsThreeA z m)
    (hw : w ∈ resCent (⊤ : Subgroup X) z) (hwz : w ∉ Subgroup.zpowers z) :
    (⟨w, hw⟩ : ↥(resCent (⊤ : Subgroup X) z)) ∉ Subgroup.center ↥(resCent (⊤ : Subgroup X) z) := by
  intro hc
  set Q := resCent (⊤ : Subgroup X) z
  set z' : ↥Q := ⟨z, hz.2.1⟩ with hz'
  have hz'c : z' ∈ Subgroup.center ↥Q := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (mem_centralizer_of_mem_resCent g.2)
  have hord : orderOf z' = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hz.1
  have hc3 : Nat.card (Subgroup.center ↥Q) = 3 := card_center_eq_three_of_isSLThreePi ⟨_, hz.2.2⟩
  have hle : Subgroup.zpowers z' ≤ Subgroup.center ↥Q := by
    rw [Subgroup.zpowers_le]; exact hz'c
  have heq : Subgroup.zpowers z' = Subgroup.center ↥Q :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, hc3])
  rw [← heq] at hc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact hwz ⟨k, by simpa [hz'] using congrArg Subtype.val hk⟩

end Center

section Model

variable {X : Type} [Group X] [Finite X]

structure ThreeLocalModel (X : Type) [Group X] [Finite X] (r : TauCeti.PrimePower) (s : ℕ)
    (S M : Subgroup X) : Prop where
  S_sl2 : ComponentClassification.HarrisLit.IsSLTwoOver s S
  M_perfect : Group.IsPerfect M
  comm : ∀ a ∈ S, ∀ b ∈ M, a * b = b * a
  inter : ∀ x ∈ S, x ∈ M → x ^ 3 = 1 → x = 1
  exists_three : ∃ μ ∈ M, orderOf μ = 3
  conj : ∀ g : X, orderOf g = 3 → ∃ h : X, h * g * h⁻¹ ∈ S ∨ h * g * h⁻¹ ∈ M
  three_A : ∀ z ∈ S, orderOf z = 3 → IsThreeA z r.card
  three_B : ∀ t ∈ M, orderOf t = 3 → resCent (⊤ : Subgroup X) t = S

namespace ThreeLocalModel

variable {r : TauCeti.PrimePower} {s : ℕ} {S M : Subgroup X} (hM : ThreeLocalModel X r s S M)
include hM

theorem isThreeB_of_mem {t : X} (htM : t ∈ M) (ht3 : orderOf t = 3) :
    IsThreeB t s := by
  obtain ⟨F, hF, hFfin, hFc, ⟨e⟩⟩ := hM.S_sl2
  exact ⟨ht3, F, hF, hFfin, hFc, ⟨(MulEquiv.subgroupCongr (hM.three_B t htM ht3)).trans e⟩⟩

theorem exists_conj_mem_M {t : X} (ht : IsThreeB t s) :
    ∃ h : X, h * t * h⁻¹ ∈ M := by
  obtain ⟨h, h1 | h1⟩ := hM.conj t ht.1
  · exfalso
    have hA := hM.three_A _ h1 (by rw [orderOf_conj_eq]; exact ht.1)
    have hA' := isThreeA_conj hA h⁻¹
    rw [show h⁻¹ * (h * t * h⁻¹) * h⁻¹⁻¹ = t by group] at hA'
    exact not_isThreeA_and_isThreeB hA' ht
  · exact ⟨h, h1⟩

theorem exists_conj_mem_S {z : X} (hz : IsThreeA z r.card) :
    ∃ h : X, h * z * h⁻¹ ∈ S := by
  obtain ⟨h, h1 | h1⟩ := hM.conj z hz.1
  · exact ⟨h, h1⟩
  · exfalso
    have hB := hM.isThreeB_of_mem h1 (by rw [orderOf_conj_eq]; exact hz.1)
    have hB' := isThreeB_conj hB h⁻¹
    rw [show h⁻¹ * (h * z * h⁻¹) * h⁻¹⁻¹ = z by group] at hB'
    exact not_isThreeA_and_isThreeB hz hB'

theorem clause_zero {z : X} (hz : orderOf z = 3) :
    IsThreeA z r.card ∨ IsThreeB z s := by
  obtain ⟨h, h1 | h1⟩ := hM.conj z hz
  · left
    have := isThreeA_conj (hM.three_A _ h1 (by rw [orderOf_conj_eq]; exact hz)) h⁻¹
    rwa [show h⁻¹ * (h * z * h⁻¹) * h⁻¹⁻¹ = z by group] at this
  · right
    have := isThreeB_conj (hM.isThreeB_of_mem h1 (by rw [orderOf_conj_eq]; exact hz)) h⁻¹
    rwa [show h⁻¹ * (h * z * h⁻¹) * h⁻¹⁻¹ = z by group] at this

theorem clause_d1 {t : X} (ht : IsThreeB t s) {g : X}
    (hg : g ∈ resCent (⊤ : Subgroup X) t) (hg3 : orderOf g = 3) : IsThreeA g r.card := by
  obtain ⟨h, hh⟩ := hM.exists_conj_mem_M ht
  have hh3 : orderOf (h * t * h⁻¹) = 3 := by rw [orderOf_conj_eq]; exact ht.1
  have hgS : h * g * h⁻¹ ∈ S := by
    rw [← hM.three_B _ hh hh3]
    exact (conj_mem_resCent_iff h t g).mpr hg
  have := isThreeA_conj (hM.three_A _ hgS (by rw [orderOf_conj_eq]; exact hg3)) h⁻¹
  rwa [show h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g by group] at this

theorem M_le_resCent {z : X} (hz : z ∈ S) : M ≤ resCent (⊤ : Subgroup X) z := by
  unfold resCent
  refine le_inSubgroup_perfectResidual_of_isPerfect (le_inf le_top ?_) hM.M_perfect
  intro b hb
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hM.comm z hz b hb).symm

theorem clause_a {z t : X} (hz : IsThreeA z r.card) (ht : IsThreeB t s)
    (hzt : z ∈ resCent (⊤ : Subgroup X) t) : t ∈ resCent (⊤ : Subgroup X) z := by
  obtain ⟨h, hh⟩ := hM.exists_conj_mem_M ht
  have hh3 : orderOf (h * t * h⁻¹) = 3 := by rw [orderOf_conj_eq]; exact ht.1
  have hzS : h * z * h⁻¹ ∈ S := by
    rw [← hM.three_B _ hh hh3]
    exact (conj_mem_resCent_iff h t z).mpr hzt
  have h1 : h * t * h⁻¹ ∈ resCent (⊤ : Subgroup X) (h * z * h⁻¹) := hM.M_le_resCent hzS hh
  exact (conj_mem_resCent_iff h z t).mp h1

theorem exists_conj_to_M {z₀ w : X} (hz₀S : z₀ ∈ S) (hz₀3 : orderOf z₀ = 3)
    (hw : w ∈ resCent (⊤ : Subgroup X) z₀) (hw3 : w ^ 3 = 1) (hwz : w ∉ Subgroup.zpowers z₀) :
    ∃ g ∈ resCent (⊤ : Subgroup X) z₀, ∃ μ ∈ M, orderOf μ = 3 ∧ g * μ * g⁻¹ = w := by
  have hA := hM.three_A z₀ hz₀S hz₀3
  obtain ⟨μ, hμM, hμ3⟩ := hM.exists_three
  have hμQ : μ ∈ resCent (⊤ : Subgroup X) z₀ := hM.M_le_resCent hz₀S hμM
  have hμz : μ ∉ Subgroup.zpowers z₀ := by
    intro h
    have hμS : μ ∈ S := (Subgroup.zpowers_le.mpr hz₀S) h
    have hμ3' : μ ^ 3 = 1 := by rw [← hμ3]; exact pow_orderOf_eq_one μ
    have := hM.inter μ hμS hμM hμ3'
    rw [this, orderOf_one] at hμ3
    omega
  obtain ⟨g, hg⟩ := exists_conj_of_isSLThreePiAt hA.2.2
    (a := (⟨μ, hμQ⟩ : ↥(resCent (⊤ : Subgroup X) z₀))) (b := ⟨w, hw⟩)
    (Subtype.ext (by simpa using (by rw [← hμ3]; exact pow_orderOf_eq_one μ : μ ^ 3 = 1)))
    (Subtype.ext (by simpa using hw3))
    (notMem_center_of_notMem_zpowers hA hμQ hμz) (notMem_center_of_notMem_zpowers hA hw hwz)
  exact ⟨g, g.2, μ, hμM, hμ3, congrArg Subtype.val hg⟩

theorem clause_c {z t : X} (hz : IsThreeA z r.card) (ht : t ∈ resCent (⊤ : Subgroup X) z)
    (ht3 : t ^ 3 = 1) (htz : t ∉ Subgroup.zpowers z) : IsThreeB t s := by
  obtain ⟨h, hhS⟩ := hM.exists_conj_mem_S hz
  have hz₀3 : orderOf (h * z * h⁻¹) = 3 := by rw [orderOf_conj_eq]; exact hz.1
  have ht₀ : h * t * h⁻¹ ∈ resCent (⊤ : Subgroup X) (h * z * h⁻¹) :=
    (conj_mem_resCent_iff h z t).mpr ht
  have ht₀3 : (h * t * h⁻¹) ^ 3 = 1 := by rw [conj_pow, ht3]; group
  have ht₀z : h * t * h⁻¹ ∉ Subgroup.zpowers (h * z * h⁻¹) := by
    rintro ⟨k, hk⟩
    apply htz
    refine ⟨k, ?_⟩
    have hk' : (h * z * h⁻¹) ^ k = h * t * h⁻¹ := hk
    rw [conj_zpow] at hk'
    simpa using hk'
  obtain ⟨g, -, μ, hμM, hμ3, hg⟩ := hM.exists_conj_to_M hhS hz₀3 ht₀ ht₀3 ht₀z
  have hB := isThreeB_conj (hM.isThreeB_of_mem hμM hμ3) g
  rw [hg] at hB
  have := isThreeB_conj hB h⁻¹
  rwa [show h⁻¹ * (h * t * h⁻¹) * h⁻¹⁻¹ = t by group] at this

theorem clause_d2 {z t : X} (hz : IsThreeA z r.card) (ht : IsThreeB t s)
    (hzt : t ∈ resCent (⊤ : Subgroup X) z) : z ∈ resCent (⊤ : Subgroup X) t := by
  obtain ⟨h, hhS⟩ := hM.exists_conj_mem_S hz
  have hz₀3 : orderOf (h * z * h⁻¹) = 3 := by rw [orderOf_conj_eq]; exact hz.1
  have ht₀ : h * t * h⁻¹ ∈ resCent (⊤ : Subgroup X) (h * z * h⁻¹) :=
    (conj_mem_resCent_iff h z t).mpr hzt
  have ht₀B : IsThreeB (h * t * h⁻¹) s := isThreeB_conj ht h
  have ht₀3 : (h * t * h⁻¹) ^ 3 = 1 := by
    have := ht₀B.1
    rw [← this]
    exact pow_orderOf_eq_one _
  have ht₀z : h * t * h⁻¹ ∉ Subgroup.zpowers (h * z * h⁻¹) := by
    intro hmem
    have hS : h * t * h⁻¹ ∈ S := (Subgroup.zpowers_le.mpr hhS) hmem
    exact not_isThreeA_and_isThreeB (hM.three_A _ hS ht₀B.1) ht₀B
  obtain ⟨g, hgQ, μ, hμM, hμ3, hg⟩ := hM.exists_conj_to_M hhS hz₀3 ht₀ ht₀3 ht₀z
  have hcomm : g * (h * z * h⁻¹) = (h * z * h⁻¹) * g := mem_centralizer_of_mem_resCent hgQ
  have hz₀ : h * z * h⁻¹ ∈ resCent (⊤ : Subgroup X) (h * t * h⁻¹) := by
    rw [← hg, resCent_top_conj, hM.three_B μ hμM hμ3]
    refine ⟨h * z * h⁻¹, hhS, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * (h * z * h⁻¹) * g⁻¹ = (h * z * h⁻¹) * g * g⁻¹ := by rw [hcomm]
      _ = h * z * h⁻¹ := by group
  exact (conj_mem_resCent_iff h t z).mp hz₀

end ThreeLocalModel

end Model

section Transport

variable {X X' : Type} [Group X] [Group X'] [Finite X] [Finite X']

theorem centralizer_map_equiv_eq (e : X ≃* X') (z : X) :
    Subgroup.centralizer ({e z} : Set X') =
      (Subgroup.centralizer ({z} : Set X)).map e.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨e.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hy]

theorem resCent_top_map (e : X ≃* X') (z : X) :
    resCent (⊤ : Subgroup X') (e z) = (resCent (⊤ : Subgroup X) z).map e.toMonoidHom := by
  unfold resCent
  rw [top_inf_eq, top_inf_eq, centralizer_map_equiv_eq, ← map_inSubgroup_perfectResidual]

noncomputable def resCentMapEquiv (e : X ≃* X') (z : X) :
    ↥(resCent (⊤ : Subgroup X) z) ≃* ↥(resCent (⊤ : Subgroup X') (e z)) :=
  ((resCent (⊤ : Subgroup X) z).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (resCent_top_map e z).symm)

theorem isThreeA_map (e : X ≃* X') {z : X} {m : ℕ} (h : IsThreeA z m) : IsThreeA (e z) m := by
  obtain ⟨h3, hz, hsl⟩ := h
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact h3, ?_, isSLThreePiAt_congr (resCentMapEquiv e z) hsl⟩
  rw [resCent_top_map]
  exact ⟨z, hz, rfl⟩

variable {r : TauCeti.PrimePower} {s : ℕ} {S M : Subgroup X}

theorem ThreeLocalModel.map (e : X ≃* X') (hM : ThreeLocalModel X r s S M) :
    ThreeLocalModel X' r s (S.map e.toMonoidHom) (M.map e.toMonoidHom) where
  S_sl2 := by
    obtain ⟨F, hF, hFf, hFc, ⟨e'⟩⟩ := hM.S_sl2
    exact ⟨F, hF, hFf, hFc, ⟨(S.equivMapOfInjective e.toMonoidHom e.injective).symm.trans e'⟩⟩
  M_perfect := by
    have := hM.M_perfect
    exact Group.IsPerfect.ofSurjective
      (f := (M.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
      (MulEquiv.surjective _)
  comm := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hM.comm a ha b hb]
  inter := by
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩ h3
    simp only [MulEquiv.coe_toMonoidHom] at hba h3
    have : b = a := e.injective hba
    subst this
    have h3' : b ^ 3 = 1 := e.injective (by rw [map_pow, h3, map_one])
    rw [hM.inter b ha hb h3', map_one]
  exists_three := by
    obtain ⟨μ, hμ, hμ3⟩ := hM.exists_three
    exact ⟨e μ, ⟨μ, hμ, rfl⟩, by rw [MulEquiv.orderOf_eq]; exact hμ3⟩
  conj := by
    intro g hg
    have hg' : orderOf (e.symm g) = 3 := by rw [MulEquiv.orderOf_eq]; exact hg
    obtain ⟨h, h1 | h1⟩ := hM.conj (e.symm g) hg'
    · refine ⟨e h, Or.inl ⟨_, h1, ?_⟩⟩
      simp
    · refine ⟨e h, Or.inr ⟨_, h1, ?_⟩⟩
      simp
  three_A := by
    rintro _ ⟨z, hz, rfl⟩ h3
    exact isThreeA_map e (hM.three_A z hz (by rw [← MulEquiv.orderOf_eq e]; exact h3))
  three_B := by
    rintro _ ⟨t, ht, rfl⟩ h3
    have h3' : orderOf (e t) = 3 := h3
    show resCent (⊤ : Subgroup X') (e t) = _
    rw [resCent_top_map, hM.three_B t ht (by rw [← MulEquiv.orderOf_eq e]; exact h3')]

end Transport

end Hering129L

end CFSG.RankThree.PartTwo.Sec12
