module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofExc

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

namespace KS11Lie4Proof

variable {G : Type} [Group G]

theorem isSubnormal_map_subgroupOf {H S : Subgroup G} (hSH : S ≤ H) {L : Subgroup H}
    (hL : L.IsSubnormal) : ((L.map H.subtype).subgroupOf S).IsSubnormal := by
  have h1 := hL.comap (Subgroup.inclusion hSH)
  have h2 : L.comap (Subgroup.inclusion hSH) = (L.map H.subtype).subgroupOf S := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_map,
      Subgroup.coe_subtype]
    constructor
    · intro hx
      exact ⟨_, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : Subgroup.inclusion hSH x = y := Subtype.ext (by simpa using hyx.symm)
      rw [this]
      exact hy
  rwa [h2] at h1

theorem eq_bot_of_isPerfect_of_le_center {S : Subgroup G} {J : Subgroup S}
    (hJp : Group.IsPerfect J) (hJc : J ≤ Subgroup.center S) : J = ⊥ := by
  have hcomm : _root_.commutator J = ⊥ := by
    rw [eq_bot_iff, commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨x, y, rfl⟩
    have hxy : (x : S) * y = y * x := Subgroup.mem_center_iff.mp (hJc y.2) x
    have hxy' : x * y = y * x := Subtype.ext hxy
    rw [SetLike.mem_coe, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hxy'
  rw [hJp.commutator_eq_top] at hcomm
  rw [eq_bot_iff]
  intro j hj
  have hj' : (⟨j, hj⟩ : J) ∈ (⊤ : Subgroup J) := Subgroup.mem_top _
  rw [hcomm, Subgroup.mem_bot] at hj'
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hj'

theorem ne_bot_of_mem_thetaComponentsIn {H J : Subgroup G} (hJ : J ∈ thetaComponentsIn H) :
    J ≠ ⊥ := by
  rintro rfl
  obtain ⟨L, hL, hLJ⟩ := hJ
  have hLb : L = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    have : (l : G) ∈ (⊥ : Subgroup G) := hLJ ▸ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  subst hLb
  obtain ⟨-, -, hq⟩ := hL
  obtain ⟨-, -, u, v, huv⟩ := hq
  exact huv (Subsingleton.elim _ _)

theorem eq_of_mem_thetaComponentsIn {H S J : Subgroup G} (hSH : S ≤ H)
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ S) (hSq : CFSG.IsQuasisimple S)
    (hJ : J ∈ thetaComponentsIn H) : J = S := by
  have hJp : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJH : J ≤ H := le_of_mem_thetaComponentsIn hJ
  have hJS : J ≤ S := by
    have h1 : ⁅J, J⁆ = J := Subgroup.commutator_eq_self
    rw [← h1, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact hcomm a (hJH ha) b (hJH hb)
  obtain ⟨L, hL, rfl⟩ := hJ
  have hsn := isSubnormal_map_subgroupOf hSH hL.2.1
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hSq hsn with
    htop | hcen
  · refine le_antisymm hJS fun s hs => ?_
    have : (⟨s, hs⟩ : S) ∈ (L.map H.subtype).subgroupOf S := htop ▸ Subgroup.mem_top _
    exact this
  · exfalso
    have hJp' : Group.IsPerfect ((L.map H.subtype).subgroupOf S) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJS).symm.toMonoidHom)
        (MulEquiv.surjective _)
    have hbot := eq_bot_of_isPerfect_of_le_center hJp' hcen
    apply ne_bot_of_mem_thetaComponentsIn (H := H) ⟨L, hL, rfl⟩
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hJS hx⟩ : S) ∈ (L.map H.subtype).subgroupOf S := hx
    rw [hbot, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this

theorem theta_central_of_isQuasisimple {J : Subgroup G} (hJq : CFSG.IsQuasisimple J)
    (hJT : CFSG.IsQuasisimple (J ⧸ aschbacherSolvableCore 3 J)) :
    ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) J, ∀ k ∈ J, t * k = k * t := by
  have hn : (aschbacherSolvableCore 3 J).Normal := inferInstance
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hJq
      hn.isSubnormal with htop | hcen
  · exfalso
    have hsub : Subsingleton (J ⧸ aschbacherSolvableCore 3 J) := ⟨fun a b => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, htop]
      exact Subgroup.mem_top _⟩
    obtain ⟨-, -, u, v, huv⟩ := hJT
    apply huv
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    rw [Subsingleton.elim u v]
  · rintro _ ⟨t, ht, rfl⟩ k hk
    have h1 := Subgroup.mem_center_iff.mp (hcen ht) ⟨k, hk⟩
    exact (congrArg Subtype.val h1).symm

end KS11Lie4Proof

end CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

namespace KS11Lie4Proof

section ThreeB

variable {Z : Type} [Group Z] [Finite Z]

omit [Finite Z] in
theorem fixSub_conj_eq_centralizer (z : Z) :
    Item426.fixSub (MulAut.conj z) = Subgroup.centralizer ({z} : Set Z) := by
  ext x
  rw [Item426.mem_fixSub, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc x * z = z * x * z⁻¹ * z := by rw [hx]
      _ = z * x := by group
  · intro hx
    calc z * x * z⁻¹ = x * z * z⁻¹ := by rw [hx]
      _ = x := by group

omit [Finite Z] in
theorem eq_bot_of_isPerfect_of_isSolvable {J : Subgroup Z} (hJp : Group.IsPerfect J)
    (hJs : Group.IsSolvable J) : J = ⊥ := by
  obtain ⟨n, hn⟩ := hJs.solvable
  have hd : ∀ k, derivedSeries J k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, hJp.commutator_eq_top]
  rw [hd n] at hn
  rw [eq_bot_iff]
  intro j hj
  have : (⟨j, hj⟩ : J) ∈ (⊤ : Subgroup J) := Subgroup.mem_top _
  rw [hn, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

structure ThreeBAt (Z : Type) [Group Z] (z : Z) (S : Subgroup Z) : Prop where
  quasisimple : CFSG.IsQuasisimple S
  le : S ≤ Subgroup.centralizer ({z} : Set Z)
  comm : ∀ x ∈ Subgroup.centralizer ({z} : Set Z), ∀ y ∈ Subgroup.centralizer ({z} : Set Z),
    x * y * x⁻¹ * y⁻¹ ∈ S

variable {z : Z} {S M J : Subgroup Z}

theorem false_of_threeA {N : Subgroup Z} (hNC : N ≤ Subgroup.centralizer ({z} : Set Z))
    (hcomm : ∀ x ∈ Subgroup.centralizer ({z} : Set Z), ∀ y ∈ Subgroup.centralizer ({z} : Set Z),
      x * y * x⁻¹ * y⁻¹ ∈ N) (hNq : CFSG.IsQuasisimple N)
    (hx : ∃ x ∈ N, (∀ n ∈ N, x * n = n * x) ∧ x ≠ 1 ∧ x ^ 3 = 1)
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) : False := by
  have hJ' : J ∈ thetaComponentsIn (Subgroup.centralizer ({z} : Set Z)) := by
    rw [← fixSub_conj_eq_centralizer]
    exact hJ
  have hJeq := eq_of_mem_thetaComponentsIn hNC hcomm hNq hJ'
  subst hJeq
  obtain ⟨x, hxJ, hc, hx1, hx3⟩ := hx
  obtain ⟨⟨u, hu⟩, huθ, hue⟩ := KS11Lie2Proof.mem_theta_of_central hJT hxJ hc
  have hu' : (⟨u, hu⟩ : J) = ⟨x, hxJ⟩ := Subtype.ext hue
  rw [hu'] at huθ
  have h1 := eq_one_of_mem_theta_of_pow_eq_one huθ (k := 1) (Subtype.ext (by simpa using hx3))
  exact hx1 (congrArg Subtype.val h1)

omit [Finite Z] in
theorem ThreeBAt.eq (h : ThreeBAt Z z S)
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z))) : J = S := by
  have hJ' : J ∈ thetaComponentsIn (Subgroup.centralizer ({z} : Set Z)) := by
    rw [← fixSub_conj_eq_centralizer]
    exact hJ
  exact eq_of_mem_thetaComponentsIn h.le h.comm h.quasisimple hJ'

theorem isQuasisimple_quot_of_mem {H : Subgroup Z} (hJ : J ∈ thetaComponentsIn H) :
    CFSG.IsQuasisimple (J ⧸ aschbacherSolvableCore 3 J) := by
  obtain ⟨hJH, hJ'⟩ := mem_thetaComponentsIn_iff.mp hJ
  set e := Subgroup.subgroupOfEquivOfLe hJH
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)) hJ'.2.2

theorem ThreeBAt.thetaCentral (h : ThreeBAt Z z S)
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z))) :
    ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) J, ∀ k ∈ J, t * k = k * t := by
  have hJS := h.eq hJ
  have hq := isQuasisimple_quot_of_mem hJ
  subst hJS
  exact theta_central_of_isQuasisimple h.quasisimple hq

theorem ThreeBAt.inn (h : ThreeBAt Z z S) {m : ℕ} (hm : m ∣ Nat.card S)
    (hexp : ∀ b ∈ Subgroup.centralizer ({z} : Set Z), b ∈ Subgroup.centralizer (S : Set Z) →
      b ^ m = 1) {b : Z}
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z))) (hb : ∃ k : ℕ, b ^ 3 ^ k = 1)
    (hbz : b * z = z * b) (hbJ : ∀ j ∈ J, b * j = j * b) :
    b ^ (3 ^ (Nat.card J).factorization 3) = 1 := by
  have hJS := h.eq hJ
  subst hJS
  have hbm := hexp b (Subgroup.mem_centralizer_singleton_iff.mpr hbz)
    (Subgroup.mem_centralizer_iff.mpr fun j hj => (hbJ j hj).symm)
  obtain ⟨k, hk⟩ := hb
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have hdvd : 3 ^ j ∣ Nat.card J := hj ▸ (orderOf_dvd_of_pow_eq_one hbm).trans hm
  have hj' : j ≤ (Nat.card J).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  exact Nat.pow_dvd_pow 3 hj'

omit [Finite Z] in
theorem ThreeBAt.out (h : ThreeBAt Z z S)
    (hout : ∀ β : MulAut Z, (∃ k : ℕ, β ^ 3 ^ k = 1) → (∀ x ∈ S, β x = x) →
      β ∈ (MulAut.conj : Z →* MulAut Z).range) {β : MulAut Z}
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z))) (hβ : ∃ k : ℕ, β ^ 3 ^ k = 1)
    (hβJ : ∀ j ∈ J, β j = j) : β ∈ (MulAut.conj : Z →* MulAut Z).range := by
  have hJS := h.eq hJ
  subst hJS
  exact hout β hβ hβJ

theorem ThreeBAt.normCent (h : ThreeBAt Z z S) (hMS : ∀ s ∈ S, ∀ m ∈ M, s * m = m * s)
    (hMp : Group.IsPerfect M)
    (hnine : ∀ y ∈ S, (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 ≠ 1 →
      (∀ x ∈ Subgroup.centralizer ({y} : Set Z), ∀ w ∈ Subgroup.centralizer ({y} : Set Z),
        x * w * x⁻¹ * w⁻¹ ∈ M) ∧
      ∀ x ∈ Subgroup.centralizer ({y} : Set Z), x ∈ Subgroup.centralizer (S : Set Z) → x ∈ M)
    {y g : Z}
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z))) (hyJ : y ∈ J)
    (hy : ∃ k : ℕ, y ^ 3 ^ k = 1) (hy3 : y ^ 3 ≠ 1) (hgy : g * y * g⁻¹ ∈ Subgroup.zpowers y) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (J : Set Z) : Subgroup Z) : Set Z) := by
  have hJS := h.eq hJ
  subst hJS
  obtain ⟨hcomm, hcy⟩ := hnine y hyJ hy hy3
  have hcent : Subgroup.centralizer (J : Set Z) = M := by
    refine le_antisymm (fun x hx => hcy x ?_ hx) fun m hm => ?_
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx y hyJ).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact hMS s hs m hm
  rw [hcent]
  set Cy := Subgroup.centralizer ({y} : Set Z) with hCy
  have hMC : M ≤ Cy := fun m hm => by
    rw [← hcent] at hm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hm y hyJ).symm
  have hMeq : ⁅Cy, Cy⁆ = M := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact hcomm a ha b hb
    · have h1 : ⁅M, M⁆ = M := Subgroup.commutator_eq_self
      rw [← h1]
      exact Subgroup.commutator_mono hMC hMC
  rw [← hMeq]
  suffices hg : g ∈ Subgroup.normalizer (Cy : Set Z) by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
    rw [Subgroup.map_commutator, hg]
  rw [hCy]
  have hgy' : g * y * g⁻¹ ∈ Subgroup.zpowers y := hgy
  have hzp : (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers y := by
    have hle : (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom ≤ Subgroup.zpowers y := by
      rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le]
      exact hgy'
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hcy : ∀ x : Z, x ∈ Subgroup.centralizer ({y} : Set Z) ↔
      x ∈ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup Z) : Set Z) := by
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hx).symm n)).eq
    · intro hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx y (Subgroup.mem_zpowers y)).symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hcy, hcy]
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro w hw
    have hw' : g⁻¹ * w * g ∈ Subgroup.zpowers y := by
      rw [← hzp] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      simpa [MulAut.conj_apply, mul_assoc] using hu
    have := hx _ hw'
    calc w * (g * x * g⁻¹) = g * (g⁻¹ * w * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * w := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro w hw
    have hw' : g * w * g⁻¹ ∈ Subgroup.zpowers y := by
      rw [← hzp]
      exact ⟨w, hw, rfl⟩
    have := hx _ hw'
    calc w * x = g⁻¹ * ((g * w * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * w * g⁻¹)) * g := by rw [this]
      _ = x * w := by group

end ThreeB

end KS11Lie4Proof

end CFSG.RankThree.PartTwo.Sec11
