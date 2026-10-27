module

public import CFSG.Quasithin.Recognition.St84.Sec48D
public import CFSG.Quasithin.Recognition.St84.Gen.NatSecCob
public import CFSG.GroupTheory.ChiefSectionPGroup
public import CFSG.Quasithin.Recognition.HSTypeZQ
public import CFSG.Quasithin.Recognition.St84.Gen.Sec48U4qTypes
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBS3Vertex

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

variable {r d : ℕ}

private abbrev WQ : Subgroup G := X.Q 0 ⊓ X.Q 2

private abbrev PQ : Subgroup G := X.Q 0 ⊓ X.Q 1

private abbrev YQ : Subgroup G := relCent X.PQ (X.Z 0) (X.Z 4)

variable {X}

namespace Comm48

private theorem s48e_mem_normalizer_relCent {E Z A : Subgroup G} {g : G}
    (hgE : g ∈ Subgroup.normalizer (E : Set G)) (hgZ : g ∈ Subgroup.normalizer (Z : Set G))
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer (relCent E Z A : Set G) := by
  have key : ∀ h : G, h ∈ Subgroup.normalizer (E : Set G) →
      h ∈ Subgroup.normalizer (Z : Set G) → h ∈ Subgroup.normalizer (A : Set G) →
      ∀ x ∈ relCent E Z A, h * x * h⁻¹ ∈ relCent E Z A := by
    rintro h hE hZ hA x ⟨hxE, hxN, hx⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hE x).mp hxE,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hZ hxN) (Subgroup.inv_mem _ hZ), fun a ha => ?_⟩
    have ha' : h⁻¹ * a * h ∈ A := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hA) a).mp ha
    have e : ⁅h * x * h⁻¹, a⁆ = h * ⁅x, h⁻¹ * a * h⁆ * h⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hZ _).mp (hx _ ha')
  refine B6.mem_normalizer_of_forall_mem (key g hgE hgZ hgA) ?_
  intro x hx
  simpa using key g⁻¹ (Subgroup.inv_mem _ hgE) (Subgroup.inv_mem _ hgZ)
    (Subgroup.inv_mem _ hgA) x hx

private theorem s48e_Ki_add (m i : ℤ) : X.Ki (i + 2 * m) = conjSub (X.τ ^ m) (X.Ki i) := by
  have hK : conjSub (X.τ ^ m) X.K = X.K :=
    mem_normalizer_iff_conjSub.mp (zpow_mem X.τ_norm m)
  show X.K ⊓ X.L (i + 2 * m) = conjSub (X.τ ^ m) (X.K ⊓ X.L i)
  rw [conjSub_inf, hK, X.L_add m i]

private theorem s48e_Ki_smul {t : G} (ht : t ∈ Subgroup.normalizer (X.K : Set G)) {i j : ℤ}
    (h : t • X.vert i = X.vert j) : X.Ki j = conjSub t (X.Ki i) := by
  have hK : conjSub t X.K = X.K := mem_normalizer_iff_conjSub.mp ht
  show X.K ⊓ X.L j = conjSub t (X.K ⊓ X.L i)
  rw [conjSub_inf, hK, L_smul X X h]

private theorem s48e_fixes_conj {A : Subgroup G} {g : G} {i j : ℤ} (hv : g • X.vert i = X.vert j)
    (hA : ∀ w, Γ.Adj (X.vert i) w → ∀ x ∈ A, x • w = w) :
    ∀ w, Γ.Adj (X.vert j) w → ∀ x ∈ conjSub g A, x • w = w := by
  intro w hw x hx
  have hx' : g⁻¹ * x * g ∈ A := mem_conjSub.mp hx
  have hw' : Γ.Adj (X.vert i) (g⁻¹ • w) := by
    have h := (X.hyp.adj_smul g⁻¹ (X.vert j) w).2 hw
    rwa [← hv, inv_smul_smul] at h
  have h := hA _ hw' _ hx'
  rw [mul_smul, mul_smul, smul_inv_smul] at h
  exact (smul_left_cancel_iff g⁻¹).mp h

private theorem s48e_K_le_normalizer_Ki (i : ℤ) : X.K ≤ Subgroup.normalizer (X.Ki i : Set G) :=
  F1.le_normalizer_inf_of_le ((X.K_le_Gi i).trans (le_normalizer_oTwoPrime (X.Gi i)))

private theorem s48e_eq_of_fixes (i : ℤ) {A B : Subgroup G} {q : ℕ}
    (hKq : Nat.card X.K = q ^ 2) (hKi : Nat.card (X.Ki i) = q)
    (hA : A ≤ X.K) (hB : B ≤ X.K) (hcA : Nat.card A = q) (hcB : Nat.card B = q)
    (hfA : ∀ w, Γ.Adj (X.vert i) w → ∀ x ∈ A, x • w = w)
    (hfB : ∀ w, Γ.Adj (X.vert i) w → ∀ x ∈ B, x • w = w) : A = B := by
  let F : Subgroup G := ⨅ (w : V) (_ : Γ.Adj (X.vert i) w), MulAction.stabilizer G w
  have hAF : A ≤ F := by
    intro x hx
    simp only [F, Subgroup.mem_iInf]
    intro w hw
    exact MulAction.mem_stabilizer_iff.mpr (hfA w hw x hx)
  have hBF : B ≤ F := by
    intro x hx
    simp only [F, Subgroup.mem_iInf]
    intro w hw
    exact MulAction.mem_stabilizer_iff.mpr (hfB w hw x hx)
  have hABK : A ⊔ B ≤ X.K := sup_le hA hB
  have hdisj : (A ⊔ B) ⊓ X.Ki i = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvAB, hvKi⟩ := Subgroup.mem_inf.mp hv
    have hvF : v ∈ F := sup_le hAF hBF hvAB
    have hvL : v ∈ X.L i := hvKi.2
    have hfixv : ∀ w, Γ.Adj (X.vert i) w → v • w = w := by
      intro w hw
      simp only [F, Subgroup.mem_iInf] at hvF
      exact MulAction.mem_stabilizer_iff.mp (hvF w hw)
    have hN := X.hyp.isLocL2_oTwoPrime (X.vert i)
    have hvQ : v ∈ X.Q i :=
      hN.N_fixes_neighbors_mem_Q X.hyp.adj_smul (X.hyp.finite_stab (X.vert i))
        (X.hyp.valency (X.vert i)).2 (X.hyp.valency (X.vert i)).1 (x := ⟨v, hvL⟩) hfixv
    have hmem : v ∈ X.K ⊓ X.edgeSylow i := ⟨hvKi.1, X.Q_le_edgeSylow_left i hvQ⟩
    rw [X.K_inf_edgeSylow i] at hmem
    exact hmem
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (H := X.K) (X.K_le_Gi 0)
  haveI : Finite ↥A :=
    Finite.of_injective (Subgroup.inclusion hA) (Subgroup.inclusion_injective _)
  haveI : Finite ↥B :=
    Finite.of_injective (Subgroup.inclusion hB) (Subgroup.inclusion_injective _)
  haveI : Finite ↥(A ⊔ B) :=
    Finite.of_injective (Subgroup.inclusion hABK) (Subgroup.inclusion_injective _)
  have hle := CFSG.card_mul_card_le_of_inf_eq_bot (G := G) (A := X.K) (D := A ⊔ B)
    (D' := X.Ki i) hABK inf_le_left hdisj
  rw [hKi, hKq] at hle
  have hqpos : 0 < q := hcA ▸ Nat.card_pos
  have hcard : Nat.card ↥(A ⊔ B) ≤ q := by
    have hle' : Nat.card ↥(A ⊔ B) * q ≤ q * q := by
      simpa [pow_two] using hle
    exact Nat.le_of_mul_le_mul_right hle' hqpos
  have h1 : A = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcA]; exact hcard)
  have h2 : B = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hcB]; exact hcard)
  exact h1.trans h2.symm

private theorem s48e_comm_mul_left {P Z1 Z4 : Subgroup G}
    (hPZ4 : ∀ x ∈ P, ∀ z ∈ Z4, ⁅x, z⁆ ∈ Z1)
    (hPZ1 : ∀ x ∈ P, ∀ c ∈ Z1, x * c = c * x)
    (hZ1ab : ∀ c ∈ Z1, ∀ c' ∈ Z1, c * c' = c' * c)
    {x y z : G} (hx : x ∈ P) (hy : y ∈ P) (hz : z ∈ Z4) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have e : ⁅x * y, z⁆ = (x * ⁅y, z⁆ * x⁻¹) * ⁅x, z⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, hPZ1 x hx _ (hPZ4 y hy z hz), mul_inv_cancel_right]
  exact hZ1ab _ (hPZ4 y hy z hz) _ (hPZ4 x hx z hz)

private theorem s48e_comm_inv_left {P Z1 Z4 : Subgroup G}
    (hPZ4 : ∀ x ∈ P, ∀ z ∈ Z4, ⁅x, z⁆ ∈ Z1)
    (hPZ1 : ∀ x ∈ P, ∀ c ∈ Z1, x * c = c * x)
    (hZ1ab : ∀ c ∈ Z1, ∀ c' ∈ Z1, c * c' = c' * c)
    {x z : G} (hx : x ∈ P) (hz : z ∈ Z4) :
    ⁅x⁻¹, z⁆ = ⁅x, z⁆⁻¹ := by
  have h := s48e_comm_mul_left hPZ4 hPZ1 hZ1ab (P.inv_mem hx) hx hz
  rw [inv_mul_cancel, commutatorElement_one_left] at h
  exact eq_inv_of_mul_eq_one_left h.symm

private theorem s48e_le_normalizer_relCent {P Z0 Z1 Z4 : Subgroup G}
    (hPZ4 : ∀ x ∈ P, ∀ z ∈ Z4, ⁅x, z⁆ ∈ Z1)
    (hPZ1 : ∀ x ∈ P, ∀ c ∈ Z1, x * c = c * x)
    (hZ1ab : ∀ c ∈ Z1, ∀ c' ∈ Z1, c * c' = c' * c)
    (hPZ0 : P ≤ Subgroup.normalizer (Z0 : Set G)) :
    P ≤ Subgroup.normalizer (relCent P Z0 Z4 : Set G) := by
  have key : ∀ p ∈ P, ∀ y ∈ relCent P Z0 Z4, p * y * p⁻¹ ∈ relCent P Z0 Z4 := by
    intro p hp y hy
    obtain ⟨hyP, -, hyc⟩ := hy
    have hpyP : p * y * p⁻¹ ∈ P := P.mul_mem (P.mul_mem hp hyP) (P.inv_mem hp)
    refine ⟨hpyP, hPZ0 hpyP, fun z hz => ?_⟩
    have e : ⁅p * y * p⁻¹, z⁆ = ⁅y, z⁆ := by
      rw [s48e_comm_mul_left hPZ4 hPZ1 hZ1ab (P.mul_mem hp hyP) (P.inv_mem hp) hz,
        s48e_comm_mul_left hPZ4 hPZ1 hZ1ab hp hyP hz,
        s48e_comm_inv_left hPZ4 hPZ1 hZ1ab hp hz,
        hZ1ab _ (hPZ4 p hp z hz) _ (hPZ4 y hyP z hz), mul_inv_cancel_right]
    rw [e]
    exact hyc z hz
  intro p hp
  refine B6.mem_normalizer_of_forall_mem (key p hp) ?_
  intro y hy
  simpa using key p⁻¹ (P.inv_mem hp) y hy

private theorem s48e_Z_neg_two (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.HasB (-2) 4 ∧ X.Z (-2) = pCoreOf 2 (X.arcStab (-6) 2) ∧ X.Z (-2) ⊓ X.Q 2 = ⊥ ∧
      X.Z (-1) = X.Z (-2) ⊔ X.Z 0 := by
  obtain ⟨hB0, -, -, hZ0pc, -, -, -, -⟩ := X.s48_2 C
  obtain ⟨-, hZ1sup, -, -, -, -⟩ := X.s48_4' C hH
  obtain ⟨hr8, hd3⟩ := X.s48_12 C hH
  subst d
  subst r
  have hB0_4 : X.HasB 0 4 := by simpa using hB0
  have hBm2_4 : X.HasB (-2) 4 :=
    (X.hasB_iff_of_even (i := -2) (j := 0) (by norm_num) 4).mpr hB0_4
  have hZ0pc' : X.Z 0 = pCoreOf 2 (X.arcStab (-4) 4) := by simpa using hZ0pc
  have hZneg2pc : X.Z (-2) = pCoreOf 2 (X.arcStab (-6) 2) := by
    calc X.Z (-2) = conjSub (X.τ ^ (-1 : ℤ)) (X.Z 0) := by
          simpa using (X.Z_add (-1) 0)
      _ = conjSub (X.τ ^ (-1 : ℤ)) (pCoreOf 2 (X.arcStab (-4) 4)) := by rw [hZ0pc']
      _ = pCoreOf 2 (conjSub (X.τ ^ (-1 : ℤ)) (X.arcStab (-4) 4)) := by rw [pCoreOf_conjSub]
      _ = pCoreOf 2 (X.arcStab (-6) 2) := by
          rw [show X.arcStab (-6) 2 =
            conjSub (X.τ ^ (-1 : ℤ)) (X.arcStab (-4) 4) by
            simpa using X.arcStab_add (-1) (-4) 4]
  have hKZ : X.K ≤ Subgroup.normalizer (X.Z (-2) : Set G) := fun g hg =>
    mem_normalizer_iff_conjSub.mpr (X.Z_normal (-2) g (X.K_le_Gi (-2) hg))
  have hKQ2 : X.K ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    (X.K_le_Gi 2).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
  have hKinf : X.K ≤ Subgroup.normalizer ((X.Z (-2) ⊓ X.Q 2 : Subgroup G) : Set G) :=
    (le_inf hKZ hKQ2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hZm2infQ2 : X.Z (-2) ⊓ X.Q 2 = ⊥ := by
    by_contra hne
    have hle : X.Z (-2) ⊓ X.Q 2 ≤ pCoreOf 2 (X.arcStab (-6) 2) := by
      rw [← hZneg2pc]
      exact inf_le_left
    have heq := X.eq_of_le_pCoreOf_arcStab_r C.hyp (a := -6) hKinf hne hle
    have heq' : X.Z (-2) ⊓ X.Q 2 = pCoreOf 2 (X.arcStab (-6) 2) := by simpa using heq
    have hleQ2 : X.Z (-2) ≤ X.Q 2 := by
      rw [hZneg2pc, ← heq']
      exact inf_le_right
    exact (X.not_Z_le_Q_edge hBm2_4).1 (by simpa using hleQ2)
  have hZm1eq : X.Z (-1) = X.Z (-2) ⊔ X.Z 0 := by
    simpa using X.Z_eq_sup_of_odd C hH (j := -1) ⟨-1, by norm_num⟩
  exact ⟨hBm2_4, hZneg2pc, hZm2infQ2, hZm1eq⟩

private theorem s48e_Z_four (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.HasB 4 4 ∧ X.Z 4 ≤ X.Q 1 ∧ X.Z 4 ≤ X.Q 2 ∧ X.Z 4 ≤ X.Gi 0 ∧ X.Z 4 ≤ X.Gi 1 ∧
      ¬ X.Z 4 ≤ X.Q 0 ∧ X.Z 4 = pCoreOf 2 (X.arcStab 0 8) ∧
      Nat.card (X.Z 4) = 2 ^ X.n 0 ∧ IsElemAbelian 2 (X.Z 4) := by
  obtain ⟨hr8, hd3⟩ := X.s48_12 C hH
  subst d
  subst r
  have hB4 := X.hasB_four_four C hH
  have h41 : X.Z 4 ≤ X.Q 1 := X.Z_le_Q_of_lt hB4 (j := 1) (by norm_num)
  have h42 : X.Z 4 ≤ X.Q 2 := X.Z_le_Q_of_lt hB4 (j := 2) (by norm_num)
  have h40 : X.Z 4 ≤ X.Gi 0 := hB4.Z_le_Gi (by norm_num)
  have hG1 : X.Z 4 ≤ X.Gi 1 := hB4.Z_le_Gi (by norm_num)
  have hnot : ¬ X.Z 4 ≤ X.Q 0 := fun h =>
    (X.not_Z_le_Q_edge hB4).2 (by simpa using h)
  have hpc := X.Z_four_eq_pCoreOf C hH
  have hcard := X.card_Z_four C
  have helem : IsElemAbelian 2 (X.Z 4) := by
    rw [hpc]
    exact X.isElemAbelian_pCoreOf_arcStab_r C.hyp 0
  exact ⟨hB4, h41, h42, h40, hG1, hnot, hpc, hcard, helem⟩

private theorem s48e_PQ_Z_four (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : ∀ x ∈ X.PQ, ∀ z ∈ X.Z 4, ⁅x, z⁆ ∈ X.Z 1 := by
  obtain ⟨hV2eq, hV2inf, -, -, -, -, -⟩ := X.s48_13 C hH
  obtain ⟨-, -, -, h40, hG1, -, -, -, -⟩ := s48e_Z_four C hH
  have hPG2 : X.PQ ≤ X.Gi 2 := fun x hx => (X.Q_le_Gi_adj 1 hx.2).2
  have hPN : X.PQ ≤ Subgroup.normalizer (X.Vk 2 : Set G) := hPG2.trans (X.Gi_le_normalizer_Vk 2)
  have hV2G : X.Vk 2 ≤ X.Gi 0 ⊓ X.Gi 1 := by
    rw [hV2eq]
    exact sup_le
      (le_inf ((X.Z_le_Q 1).trans ((X.Q_le_Gi_adj 1).trans inf_le_left)) (X.Z_le_Gi 1))
      (le_inf h40 hG1)
  have hV2N : X.Vk 2 ≤ Subgroup.normalizer (X.PQ : Set G) :=
    hV2G.trans X.inf_Gi_le_normalizer_inf_Q
  have hEq : X.Vk 2 ⊓ X.PQ = X.Z 1 := by
    rw [Setup.PQ, ← inf_assoc, hV2inf, inf_eq_left.mpr (X.Z_le_Q 1)]
  have hcomm : ⁅X.Vk 2, X.PQ⁆ ≤ X.Z 1 :=
    (F7.commutator_le_inf_of_normalizes hV2N hPN).trans hEq.le
  intro x hx z hz
  have hzV : z ∈ X.Vk 2 := by
    rw [hV2eq]
    exact Subgroup.mem_sup_right hz
  have h := hcomm (Subgroup.commutator_mem_commutator hzV hx)
  rw [← commutatorElement_inv]
  exact (X.Z 1).inv_mem h

private theorem QA_eq_Vk_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.QA = X.Vk 0 := by
  obtain ⟨-, -, -, -, -, hAeq, -⟩ := X.s48_13 C hH
  obtain ⟨hV0eq, -⟩ := X.s48_8 C hH
  obtain ⟨hZ0le, -⟩ := X.s48_1 C
  rw [hAeq, X.s48_14 C hH, sup_eq_right.mpr]
  rw [hV0eq]
  exact le_sup_of_le_left hZ0le

private theorem natQuot_Q_zero_Vk_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : NatQuot (X.L 0) (X.Q 0) (X.Vk 0) (X.n 0) := by
  rw [← QA_eq_Vk_zero C hH]
  exact (X.s48_13 C hH).2.2.2.1

private theorem natQuot_exists_commutatorElement_notMem {L E Z : Subgroup G} {n : ℕ}
    [Finite ↥E] (h : NatQuot L E Z n) (hE2 : IsPGroup 2 E) (hn : 1 ≤ n) {k : G}
    (hkL : k ∈ L) (hkodd : Odd (orderOf k)) (hk1 : k ≠ 1) :
    ∃ l ∈ L, ∃ e ∈ E, ⁅l, e⁆ ∉ Z := by
  have hEneZ : E ≠ Z := by
    intro hEZ
    have hcard := h.index
    rw [hEZ, Subgroup.relIndex_self] at hcard
    have hlt : 1 < 2 ^ (2 * n) := Nat.one_lt_two_pow (by omega)
    exact (by omega : 2 ^ (2 * n) ≠ 1) hcard.symm
  have hnotsub : ¬ E ≤ Z := fun hsub => hEneZ (le_antisymm hsub h.Z_le)
  obtain ⟨e, heE, heZ⟩ := Set.not_subset.mp hnotsub
  have hknotE : k ∉ E := by
    intro hkE
    obtain ⟨m, hm⟩ := hE2.exists_card_eq
    have hdvd : orderOf k ∣ 2 ^ m := by
      rw [← hm]
      exact Subgroup.orderOf_dvd_natCard E hkE
    have hcop : Nat.Coprime (2 ^ m) (orderOf k) :=
      (hkodd.coprime_two_right.pow_right m).symm
    have hone : orderOf k = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hdvd (dvd_refl (orderOf k))
    exact hk1 (orderOf_eq_one_iff.mp hone)
  refine ⟨k, hkL, e, heE, ?_⟩
  intro hcomm
  exact heZ (h.fpf k hkL hkodd hknotE e heE (by
    rw [(commutatorElement_inv k e).symm]
    exact Z.inv_mem hcomm))

private theorem isElemSec_Vk_zero_Q_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : IsElemSec (X.Vk 0) (X.Q 0) := by
  obtain ⟨-, -, -, hV0le, -, -, -⟩ := X.s48_8 C hH
  have hQA := QA_eq_Vk_zero C hH
  have hQq := X.Q_quot C.hyp.char C.hyp.sing (Nat.le_of_succ_le C.hyp.five_le) 0
  refine ⟨hV0le.trans inf_le_left, ?_, ?_⟩
  · rw [← hQA]
    simpa [Setup.QA, inf_comm] using hQq.2.2.1
  · intro e he
    rw [← hQA]
    simpa [Setup.QA, inf_comm] using hQq.2.1 e he

private theorem natPre_Q_zero_Vk_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    NatPre (X.Gi 0) (X.L 0) (X.Q 0) (X.Vk 0) (X.n 0) := by
  obtain ⟨-, -, -, hV0le, -, -, -⟩ := X.s48_8 C hH
  have hnat := natQuot_Q_zero_Vk_zero C hH
  have hcommQ : ⁅X.Q 0, X.Q 0⁆ ≤ X.Vk 0 := by
    rw [← QA_eq_Vk_zero C hH]
    simpa [Setup.QA, inf_comm] using (X.Q_quot C.hyp.char C.hyp.sing (Nat.le_of_succ_le C.hyp.five_le) 0).2.2.1
  have hq0 : IsL2Quot (X.n 0) (oTwoQuot ↥(X.L 0)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
  haveI : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (H := X.Q 0) (X.Q_le_Gi 0)
  haveI : Finite ↥(X.Vk 0) := Finite.of_injective
    (Subgroup.inclusion ((show X.Vk 0 ≤ X.Q 0 from hV0le.trans inf_le_left)))
    (Subgroup.inclusion_injective _)
  obtain ⟨k, hkKi, hk1, hkord, -⟩ := X.exists_generator_Ki 0 (C.hyp.two_le_n 0)
  have hkL : k ∈ X.L 0 := hkKi.2
  have hkodd : Odd (orderOf k) := by
    rw [hkord]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by have := C.hyp.two_le_n 0; omega)
  have hQ02 : IsPGroup 2 (X.Q 0) := pCoreOf_isPGroup' (X.Gi 0)
  have hnpos : 1 ≤ X.n 0 := by have := C.hyp.two_le_n 0; omega
  have hntE : ∃ l ∈ X.L 0, ∃ e ∈ X.Q 0, ⁅l, e⁆ ∉ X.Vk 0 :=
    natQuot_exists_commutatorElement_notMem hnat hQ02 hnpos hkL hkodd hk1
  exact
    { le := X.L_le_Gi 0
      norm_L := le_normalizer_oTwoPrime (X.Gi 0)
      norm_E := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)
      norm_K := X.Gi_le_normalizer_Vk 0
      sec := isElemSec_Vk_zero_Q_zero C hH
      card := by simpa using hnat.index
      core := by
        intro q hq e he
        exact hcommQ (Subgroup.commutator_mem_commutator hq he)
      quot := hq0
      nontriv := hntE }

private theorem natPre_Vk_zero_Z_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    NatPre (X.Gi 0) (X.L 0) (X.Vk 0) (X.Z 0) (X.n 0) := by
  obtain ⟨hV0eq, -, hV0ab, hV0le, hcommV0, hnatV0, -⟩ := X.s48_8 C hH
  obtain ⟨hZ0le, -⟩ := X.s48_1 C
  have hZle : X.Z 0 ≤ X.Vk 0 := by
    rw [hV0eq]
    exact le_sup_of_le_left hZ0le
  have hVsec : IsElemSec (X.Z 0) (X.Vk 0) := by
    refine ⟨hZle, ?_, ?_⟩
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hV0ab.comm ha hb)]
      exact (X.Z 0).one_mem
    · intro a ha
      rw [hV0ab.2 a ha]
      exact (X.Z 0).one_mem
  have hcommV0' : ⁅X.Q 0, X.Vk 0⁆ = X.Z 0 := by
    rw [Subgroup.commutator_comm]
    exact hcommV0
  have hq0 : IsL2Quot (X.n 0) (oTwoQuot ↥(X.L 0)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
  haveI : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (H := X.Q 0) (X.Q_le_Gi 0)
  haveI : Finite ↥(X.Vk 0) := Finite.of_injective
    (Subgroup.inclusion ((show X.Vk 0 ≤ X.Q 0 from hV0le.trans inf_le_left)))
    (Subgroup.inclusion_injective _)
  obtain ⟨k, hkKi, hk1, hkord, -⟩ := X.exists_generator_Ki 0 (C.hyp.two_le_n 0)
  have hkL : k ∈ X.L 0 := hkKi.2
  have hkodd : Odd (orderOf k) := by
    rw [hkord]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by have := C.hyp.two_le_n 0; omega)
  have hVk2 : IsPGroup 2 (X.Vk 0) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le (hV0le.trans inf_le_left)
  have hnpos : 1 ≤ X.n 0 := by have := C.hyp.two_le_n 0; omega
  have hntV : ∃ l ∈ X.L 0, ∃ e ∈ X.Vk 0, ⁅l, e⁆ ∉ X.Z 0 :=
    natQuot_exists_commutatorElement_notMem hnatV0 hVk2 hnpos hkL hkodd hk1
  exact
    { le := X.L_le_Gi 0
      norm_L := le_normalizer_oTwoPrime (X.Gi 0)
      norm_E := X.Gi_le_normalizer_Vk 0
      norm_K := fun g hg => mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 g hg)
      sec := hVsec
      card := by simpa using hnatV0.index
      core := by
        intro q hq e he
        exact (le_of_eq hcommV0') (Subgroup.commutator_mem_commutator hq he)
      quot := hq0
      nontriv := hntV }

theorem commutator_Q_zero_le_Z_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : ⁅X.Q 0, X.Q 0⁆ ≤ X.Z 0 := by
  obtain ⟨-, -, -, -, hcommV0, hnatV0, -⟩ := X.s48_8 C hH
  have hnat := natQuot_Q_zero_Vk_zero C hH
  have hcommQ : ⁅X.Q 0, X.Q 0⁆ ≤ X.Vk 0 := by
    rw [← QA_eq_Vk_zero C hH]
    simpa [Setup.QA, inf_comm] using (X.Q_quot C.hyp.char C.hyp.sing (Nat.le_of_succ_le C.hyp.five_le) 0).2.2.1
  have hcommV0' : ⁅X.Q 0, X.Vk 0⁆ = X.Z 0 := by
    rw [Subgroup.commutator_comm]
    exact hcommV0
  have hEpre := natPre_Q_zero_Vk_zero C hH
  have hVpre := natPre_Vk_zero_Z_zero C hH
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  exact comm_le_of_natPre (C.hyp.two_le_n 0) hEpre hVpre hnat hnatV0 hcommQ
    (le_of_eq hcommV0')

private theorem Q_zero_inf_centralizer_Vk_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Q 0 ⊓ Subgroup.centralizer (X.Vk 0 : Set G) = X.Vk 0 := by
  obtain ⟨-, -, hV0ab, hV0le, hcommV0, -⟩ := X.s48_8 C hH
  obtain ⟨-, -, -, -, hZ0card, -⟩ := X.s48_2 C
  have hnat := natQuot_Q_zero_Vk_zero C hH
  have hZ0ne : X.Z 0 ≠ ⊥ := by
    intro hbot
    have hc := hZ0card
    rw [hbot, Subgroup.card_bot] at hc
    have hlt : 1 < 2 ^ X.n 0 := Nat.one_lt_two_pow (by have := C.hyp.two_le_n 0; omega)
    omega
  have hnormV : X.Gi 0 ≤ Subgroup.normalizer (X.Vk 0 : Set G) := X.Gi_le_normalizer_Vk 0
  have hCnorm : X.Gi 0 ≤ Subgroup.normalizer
      ((X.Q 0 ⊓ Subgroup.centralizer (X.Vk 0 : Set G) : Subgroup G) : Set G) :=
    (le_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
      (B6.le_normalizer_centralizer hnormV)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hVleC : X.Vk 0 ≤ (X.Q 0 ⊓ Subgroup.centralizer (X.Vk 0 : Set G) : Subgroup G) := by
    intro v hv
    refine Subgroup.mem_inf.mpr ⟨hV0le.trans inf_le_left hv, ?_⟩
    haveI : IsMulCommutative ↥(X.Vk 0) := hV0ab.1
    exact Subgroup.le_centralizer (X.Vk 0) hv
  rcases hnat.irred (X.Q 0 ⊓ Subgroup.centralizer (X.Vk 0 : Set G)) hVleC inf_le_left
      ((X.L_le_Gi 0).trans hCnorm) with hC | hC
  · exact hC
  · exfalso
    have hQcent : X.Q 0 ≤ Subgroup.centralizer (X.Vk 0 : Set G) := by
      intro q hq
      have hqC : q ∈ (X.Q 0 ⊓ Subgroup.centralizer (X.Vk 0 : Set G) : Subgroup G) := by
        rw [hC]
        exact hq
      exact (Subgroup.mem_inf.mp hqC).2
    have hcommbot : ⁅X.Q 0, X.Vk 0⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hQcent
    have hcommbot' : ⁅X.Vk 0, X.Q 0⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hcommbot
    have : X.Z 0 = ⊥ := by
      rw [← hcommV0]
      exact hcommbot'
    exact hZ0ne this

private theorem Z_one_le_WQ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 1 ≤ X.WQ := by
  obtain ⟨-, hd3⟩ := X.s48_12 C hH
  subst d
  have hB1 : X.HasB 1 3 := by simpa using C.hasB
  exact le_inf (X.Z_le_Q_of_lt hB1 (j := 0) (by norm_num))
    (X.Z_le_Q_of_lt hB1 (j := 2) (by norm_num))

private theorem Vk_zero_inf_Q_two (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Vk 0 ⊓ X.Q 2 = X.Z 1 := by
  obtain ⟨hV0eq, -, hV0ab, -⟩ := X.s48_8 C hH
  obtain ⟨hZ0le, -⟩ := X.s48_1 C
  obtain ⟨-, -, hZm2infQ2, hZm1eq⟩ := s48e_Z_neg_two C hH
  have hZ1leQ2 : X.Z 1 ≤ X.Q 2 := (Z_one_le_WQ C hH).trans inf_le_right
  have hZ0leQ2 : X.Z 0 ≤ X.Q 2 := hZ0le.trans hZ1leQ2
  have hZ0leV0 : X.Z 0 ≤ X.Vk 0 := by
    rw [hV0eq]
    exact le_sup_of_le_left hZ0le
  have hZm2leV0 : X.Z (-2) ≤ X.Vk 0 := by
    rw [hV0eq, show X.Z (-1) = X.Z (-2) ⊔ X.Z 0 from hZm1eq, sup_comm]
    exact le_sup_of_le_left le_sup_left
  have hZm2N : X.Z (-2) ≤ Subgroup.normalizer (X.Z 0 : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer _ <| Subgroup.mem_centralizer_iff.mpr fun a ha =>
      hV0ab.comm (hZ0leV0 ha) (hZm2leV0 hb)
  have hZm1infQ2 : X.Z (-1) ⊓ X.Q 2 = X.Z 0 := by
    rw [hZm1eq, inf_comm, ← Subgroup.inf_sup_assoc_of_le hZm2N hZ0leQ2, inf_comm (X.Q 2),
      hZm2infQ2, bot_sup_eq]
  have hZ1leV0 : X.Z 1 ≤ X.Vk 0 := by
    rw [hV0eq]
    exact le_sup_of_le_left le_rfl
  have hZm1leV0 : X.Z (-1) ≤ X.Vk 0 := by
    rw [hV0eq]
    exact le_sup_of_le_right le_rfl
  have hZm1N : X.Z (-1) ≤ Subgroup.normalizer (X.Z 1 : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer _ <| Subgroup.mem_centralizer_iff.mpr fun a ha =>
      hV0ab.comm (hZ1leV0 ha) (hZm1leV0 hb)
  rw [hV0eq, sup_comm, inf_comm, ← Subgroup.inf_sup_assoc_of_le hZm1N hZ1leQ2,
    inf_comm (X.Q 2), hZm1infQ2, sup_eq_right.mpr hZ0le]

private theorem Vk_zero_inf_WQ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Vk 0 ⊓ X.WQ = X.Z 1 := by
  obtain ⟨-, -, -, hV0le, -⟩ := X.s48_8 C hH
  rw [Setup.WQ, ← inf_assoc, inf_eq_left.mpr (hV0le.trans inf_le_left)]
  exact Vk_zero_inf_Q_two C hH

private theorem commutator_Q_two_le_Z_two (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : ⁅X.Q 2, X.Q 2⁆ ≤ X.Z 2 := by
  have h := conjSub_mono (X.τ ^ (1 : ℤ)) (commutator_Q_zero_le_Z_zero C hH)
  rw [← conjSub_commutator, ← X.Q_add (m := 1) (i := 0),
    ← X.Z_add (m := 1) (i := 0)] at h
  simpa using h

private theorem WQ_le_Q_one (C : X.Comm48 s r d) : X.WQ ≤ X.Q 1 :=
  (X.Q_quot C.hyp.char C.hyp.sing (Nat.le_of_succ_le C.hyp.five_le) 1).1

private theorem L_one_le_normalizer_WQ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.L 1 ≤ Subgroup.normalizer (X.WQ : Set G) := by
  obtain ⟨hB0, -⟩ := X.s48_2 C
  obtain ⟨-, hd3⟩ := X.s48_12 C hH
  subst d
  have hB0_4 : X.HasB 0 4 := by simpa using hB0
  have hB2_4 : X.HasB 2 4 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num) 4).mpr hB0_4
  have hZ0leQ2 : X.Z 0 ≤ X.Q 2 :=
    X.Z_le_Q_of_lt hB0_4 (j := 2) (by norm_num)
  have hZ2leQ0 : X.Z 2 ≤ X.Q 0 :=
    X.Z_le_Q_of_lt hB2_4 (j := 0) (by norm_num)
  have hcommQ2 := commutator_Q_two_le_Z_two C hH
  have hQ0normW : X.Q 0 ≤ Subgroup.normalizer (X.WQ : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr <|
      (Subgroup.commutator_mono le_rfl (inf_le_left : X.WQ ≤ X.Q 0)).trans <|
        le_inf (Subgroup.commutator_le_self _) ((commutator_Q_zero_le_Z_zero C hH).trans hZ0leQ2)
  have hQ2normW : X.Q 2 ≤ Subgroup.normalizer (X.WQ : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr <|
      (Subgroup.commutator_mono le_rfl (inf_le_right : X.WQ ≤ X.Q 2)).trans <|
        le_inf (hcommQ2.trans hZ2leQ0) (Subgroup.commutator_le_self _)
  have hQ1normQ0 : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    ((X.Q_le_Gi_adj 1).trans inf_le_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hQ1normQ2 : X.Q 1 ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    ((X.Q_le_Gi_adj 1).trans inf_le_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
  have hQ1normW : X.Q 1 ≤ Subgroup.normalizer (X.WQ : Set G) :=
    F7.le_normalizer_inf hQ1normQ0 hQ1normQ2
  have hS0norm : X.edgeSylow 0 ≤ Subgroup.normalizer (X.WQ : Set G) := by
    rw [← X.sup_Q_eq_edgeSylow C.hyp.char 0]
    exact sup_le hQ0normW hQ1normW
  have hS1norm : X.edgeSylow 1 ≤ Subgroup.normalizer (X.WQ : Set G) := by
    rw [← X.sup_Q_eq_edgeSylow C.hyp.char 1]
    exact sup_le hQ1normW hQ2normW
  rw [← X.edgeSylow_sup_edgeSylow 1, show (1 : ℤ) - 1 = 0 by norm_num]
  exact sup_le hS0norm hS1norm

private theorem card_WQ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : Nat.card X.WQ = 2 ^ (3 * X.n 0) := by
  obtain ⟨-, hV0card, -, hV0le, -⟩ := X.s48_8 C hH
  have hnat := natQuot_Q_zero_Vk_zero C hH
  have hWleQ1 : X.WQ ≤ X.Q 1 := WQ_le_Q_one C
  have hcardQ0 : Nat.card (X.Q 0) = 2 ^ (5 * X.n 0) := by
    have h := Subgroup.relIndex_mul_card (H := X.Vk 0) (K := X.Q 0)
    rw [inf_eq_left.mpr (hV0le.trans inf_le_left), hnat.index, hV0card] at h
    have hpow : 2 ^ (5 * X.n 0) = 2 ^ (2 * X.n 0) * 2 ^ (3 * X.n 0) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hpow]
    exact h.symm
  have hcardS : Nat.card (X.edgeSylow 0) = 2 ^ (6 * X.n 0) := by
    have h := Subgroup.relIndex_mul_card (H := X.Q 0) (K := X.edgeSylow 0)
    rw [inf_eq_left.mpr (X.Q_le_edgeSylow_left 0), X.relIndex_Q_edgeSylow 0,
      hcardQ0] at h
    have hpow : 2 ^ (6 * X.n 0) = 2 ^ X.n 0 * 2 ^ (5 * X.n 0) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hpow]
    exact h.symm
  have hQ1S : X.Q 1 ≤ X.edgeSylow 0 := by
    rw [← X.sup_Q_eq_edgeSylow C.hyp.char 0]
    exact le_sup_right
  have hQ1rel : (X.Q 1).relIndex (X.edgeSylow 0) = 2 ^ X.n 1 := by
    simpa using X.relIndex_Q_succ_edgeSylow 0
  have hn1 : X.n 1 = X.n 0 := C.n_one_eq hH
  have hcardQ1 : Nat.card (X.Q 1) = 2 ^ (5 * X.n 0) := by
    have h := Subgroup.relIndex_mul_card (H := X.Q 1) (K := X.edgeSylow 0)
    rw [inf_eq_left.mpr hQ1S, hQ1rel, hn1, hcardS] at h
    have hpow : 2 ^ (6 * X.n 0) = 2 ^ X.n 0 * 2 ^ (5 * X.n 0) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by norm_num)) h
  have hQq1 := X.Q_quot C.hyp.char C.hyp.sing (Nat.le_of_succ_le C.hyp.five_le) 1
  have hrelW : X.WQ.relIndex (X.Q 1) = 2 ^ (2 * X.n 0) := by
    have h := hQq1.2.2.2.1
    rw [show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num] at h
    have hn2 : X.n 2 = X.n 0 := by
      have h2 := X.n_add 1 0
      rwa [show (0 : ℤ) + 2 * (1 : ℤ) = 2 by norm_num] at h2
    rw [hn2] at h
    simpa [Setup.WQ] using h
  have h := Subgroup.relIndex_mul_card (H := X.WQ) (K := X.Q 1)
  rw [inf_eq_left.mpr hWleQ1, hrelW, hcardQ1] at h
  have hpow : 2 ^ (5 * X.n 0) = 2 ^ (2 * X.n 0) * 2 ^ (3 * X.n 0) := by
    rw [← pow_add]
    congr 1
    ring
  rw [hpow] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by norm_num)) h

private theorem PQ_card_eq_and_sup_card_eq (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    Nat.card (X.PQ) = 2 ^ (4 * X.n 0) ∧
      Nat.card (X.Vk 0 ⊔ X.WQ : Subgroup G) = 2 ^ (4 * X.n 0) := by
  obtain ⟨-, hV0card, -, hV0le, -⟩ := X.s48_8 C hH
  obtain ⟨-, -, -, hZ1card, -⟩ := X.s48_4' C hH
  have hQA := QA_eq_Vk_zero C hH
  have hcardW := card_WQ C hH
  have hVinfW := Vk_zero_inf_WQ C hH
  have hWnormV0 : X.WQ ≤ Subgroup.normalizer (X.Vk 0 : Set G) :=
    (inf_le_left.trans (X.Q_le_Gi 0)).trans (X.Gi_le_normalizer_Vk 0)
  have hQq0 := X.Q_quot C.hyp.char C.hyp.sing (Nat.le_of_succ_le C.hyp.five_le) 0
  have hn1 : X.n 1 = X.n 0 := C.n_one_eq hH
  have hrelP : (X.Vk 0).relIndex (X.PQ) = 2 ^ X.n 0 := by
    have h := hQq0.2.2.2.2.1
    rw [show (0 : ℤ) - 1 = -1 by norm_num, show (0 : ℤ) + 1 = 1 by norm_num] at h
    rw [hn1] at h
    simpa [Setup.QA, inf_comm, ← hQA, Setup.PQ] using h
  have hcardP : Nat.card (X.PQ) = 2 ^ (4 * X.n 0) := by
    have h := Subgroup.relIndex_mul_card (H := X.Vk 0) (K := X.PQ)
    rw [inf_eq_left.mpr hV0le, hrelP, hV0card] at h
    have hpow : 2 ^ (4 * X.n 0) = 2 ^ X.n 0 * 2 ^ (3 * X.n 0) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hpow]
    exact h.symm
  have hrelVW : (X.Vk 0).relIndex (X.WQ) = 2 ^ X.n 0 := by
    have h := Subgroup.relIndex_mul_card (H := X.Vk 0) (K := X.WQ)
    rw [hVinfW, hZ1card, hcardW] at h
    have hpow : 2 ^ (3 * X.n 0) = 2 ^ X.n 0 * 2 ^ (2 * X.n 0) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by norm_num)) h
  have hcardsup : Nat.card (X.Vk 0 ⊔ X.WQ : Subgroup G) = 2 ^ (4 * X.n 0) := by
    have hrelsup : (X.Vk 0).relIndex (X.WQ ⊔ X.Vk 0) = (X.Vk 0).relIndex (X.WQ) :=
      CFSG.Quasithin.B2F.relIndex_sup_eq_of_le_normalizer' hWnormV0
    have h := Subgroup.relIndex_mul_card (H := X.Vk 0) (K := X.WQ ⊔ X.Vk 0)
    rw [inf_eq_left.mpr le_sup_right, hrelsup, hrelVW, hV0card] at h
    rw [sup_comm]
    have hpow : 2 ^ (4 * X.n 0) = 2 ^ X.n 0 * 2 ^ (3 * X.n 0) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hpow]
    exact h.symm
  exact ⟨hcardP, hcardsup⟩

private theorem PQ_eq_Vk_zero_sup_WQ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.PQ = X.Vk 0 ⊔ X.WQ := by
  obtain ⟨-, hV0card, -, hV0le, -⟩ := X.s48_8 C hH
  obtain ⟨hcardP, hcardsup⟩ := PQ_card_eq_and_sup_card_eq C hH
  have hWleQ1 : X.WQ ≤ X.Q 1 := WQ_le_Q_one C
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI : Finite ↥(X.PQ) :=
    Finite.of_injective
      (Subgroup.inclusion ((show X.PQ ≤ X.Q 0 from inf_le_left).trans (X.Q_le_Gi 0)))
      (Subgroup.inclusion_injective _)
  have hle : X.Vk 0 ⊔ X.WQ ≤ X.PQ :=
    sup_le hV0le (le_inf (show X.WQ ≤ X.Q 0 from inf_le_left) hWleQ1)
  have hcardge : Nat.card (X.PQ) ≤ Nat.card (X.Vk 0 ⊔ X.WQ : Subgroup G) := by
    rw [hcardP, hcardsup]
  exact (Subgroup.eq_of_le_of_card_ge hle hcardge).symm

private theorem L_one_le_normalizer_Z_one :
    X.L 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
  intro l hl
  exact mem_normalizer_iff_conjSub.mpr (X.Z_normal 1 l (X.L_le_Gi 1 hl))

private theorem Q_one_le_L_one : X.Q 1 ≤ X.L 1 := by
  have hQ1eq : pCoreOf 2 (X.L 1) = X.Q 1 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  rw [← hQ1eq]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 (X.L 1)

private theorem Z_one_relIndex_WQ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : (X.Z 1).relIndex X.WQ = 2 ^ X.n 0 := by
  have hZ1leW : X.Z 1 ≤ X.WQ := Z_one_le_WQ C hH
  have hcardW : Nat.card X.WQ = 2 ^ (3 * X.n 0) := card_WQ C hH
  have hZ1card : Nat.card (X.Z 1) = 2 ^ (2 * X.n 0) := (X.s48_4' C hH).2.2.2.1
  have h := Subgroup.relIndex_mul_card (H := X.Z 1) (K := X.WQ)
  rw [inf_eq_left.mpr hZ1leW, hZ1card, hcardW] at h
  have hpow : 2 ^ (3 * X.n 0) = 2 ^ X.n 0 * 2 ^ (2 * X.n 0) := by
    rw [← pow_add]
    congr 1
    ring
  rw [hpow] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by norm_num)) h

private theorem odd_card_Ki_one (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : Odd (Nat.card ↥(X.Ki 1)) := by
  rw [X.card_Ki 1, C.n_one_eq hH]
  exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by have := C.hyp.two_le_n 0; omega)

private theorem WQ_comm (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : ∀ a ∈ X.WQ, ∀ b ∈ X.WQ, a * b = b * a := by
  obtain ⟨-, -, hZ0Z2, -, -⟩ := X.s48_4' C hH
  have hWW0 : ⁅X.WQ, X.WQ⁆ ≤ X.Z 0 :=
    (Subgroup.commutator_mono (inf_le_left : X.WQ ≤ X.Q 0)
      (inf_le_left : X.WQ ≤ X.Q 0)).trans (commutator_Q_zero_le_Z_zero C hH)
  have hWW2 : ⁅X.WQ, X.WQ⁆ ≤ X.Z 2 :=
    (Subgroup.commutator_mono (inf_le_right : X.WQ ≤ X.Q 2)
      (inf_le_right : X.WQ ≤ X.Q 2)).trans (commutator_Q_two_le_Z_two C hH)
  have hbot : ⁅X.WQ, X.WQ⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (le_inf hWW0 hWW2).trans (le_of_eq hZ0Z2)
  haveI : IsMulCommutative ↥(X.WQ) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm' ⟨a, ha⟩ ⟨b, hb⟩)

private theorem sup_commutator_Q1_lt (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {Y : Subgroup G}
    (hZY : X.Z 1 ≤ Y) (hYW : Y ≤ X.WQ)
    (hNY : X.L 1 ≤ Subgroup.normalizer (Y : Set G)) (hYne : Y ≠ X.Z 1) :
    X.Z 1 ⊔ ⁅Y, X.Q 1⁆ < Y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ1eq : pCoreOf 2 (X.L 1) = X.Q 1 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  have hQ1L : X.Q 1 ≤ X.L 1 := Q_one_le_L_one (X := X)
  have hQ12 : IsPGroup 2 (X.Q 1) := by
    rw [← hQ1eq]
    exact pCoreOf_isPGroup' (X.L 1)
  have hWQleQ1 : X.WQ ≤ X.Q 1 := WQ_le_Q_one C
  have hYQ1 : Y ≤ X.Q 1 := hYW.trans hWQleQ1
  have hZ1Q1 : X.Z 1 ≤ X.Q 1 := hZY.trans hYQ1
  have hYQ1norm : X.Q 1 ≤ Subgroup.normalizer (Y : Set G) := hQ1L.trans hNY
  have hZ1Q1norm : X.Q 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) :=
    hQ1L.trans (L_one_le_normalizer_Z_one (X := X))
  have hcommV_leY : ⁅Y, X.Q 1⁆ ≤ Y := by
    rw [Subgroup.commutator_le]
    intro y hy q hq
    have hyq : q * y⁻¹ * q⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hYQ1norm hq) y⁻¹).mp (Y.inv_mem hy)
    have e : ⁅y, q⁆ = y * (q * y⁻¹ * q⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Y.mul_mem hy hyq
  have hVne : (X.Z 1).subgroupOf (X.Q 1) ≠ Y.subgroupOf (X.Q 1) := by
    intro heq
    apply hYne
    have h := congrArg (Subgroup.map (X.Q 1).subtype) heq
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hZ1Q1, inf_eq_left.mpr hYQ1] at h
    exact h.symm
  haveI hYnorm : (Y.subgroupOf (X.Q 1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hYQ1norm
  haveI hZnorm : ((X.Z 1).subgroupOf (X.Q 1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hZ1Q1norm
  haveI : Finite ↥(X.Gi 1) := X.hyp.finite_stab (X.vert 1)
  haveI : Finite ↥(X.Q 1) :=
    Finite.of_injective (Subgroup.inclusion (X.Q_le_Gi 1)) (Subgroup.inclusion_injective _)
  have hlt := CFSG.GroupTheory.commutator_sup_lt_of_isPGroup
    (p := 2) (G := ↥(X.Q 1)) (X := Y.subgroupOf (X.Q 1))
    (Q := (⊤ : Subgroup ↥(X.Q 1))) (V := (X.Z 1).subgroupOf (X.Q 1))
    le_top (hQ12.to_subgroup ⊤)
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hYnorm])
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hZnorm])
    (fun z hz => Subgroup.mem_subgroupOf.mpr (hZY (Subgroup.mem_subgroupOf.mp hz)))
    hVne
  have hmap := (Subgroup.map_lt_map_iff_of_injective (X.Q 1).subtype_injective).2 hlt
  rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_top,
    Subgroup.range_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZ1Q1,
    inf_eq_left.mpr hYQ1] at hmap
  simpa [sup_comm] using hmap

private theorem sup_closure_sq_lt {Y V : Subgroup G} [Finite ↥Y]
    (hY2 : IsPGroup 2 ↥Y) (hVlt : V < Y) :
    V ⊔ Subgroup.closure {y ^ 2 | y ∈ Y} < Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVY : V ≤ Y := hVlt.le
  have hVtopne : V.subgroupOf Y ≠ (⊤ : Subgroup ↥Y) := by
    intro heq
    apply hVlt.ne
    have h := congrArg (Subgroup.map Y.subtype) heq
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVY, Subgroup.map_top,
      Subgroup.range_subtype] at h
  have htop2 : IsPGroup 2 (⊤ : Subgroup ↥Y) := hY2.to_subgroup ⊤
  have hlt := CFSG.GroupTheory.sup_pow_closure_lt_of_isPGroup
    (p := 2) (G := ↥Y) (X := (⊤ : Subgroup ↥Y)) (V := V.subgroupOf Y)
    le_top htop2 hVtopne
  have hmap := (Subgroup.map_lt_map_iff_of_injective Y.subtype_injective).2 hlt
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVY,
    MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype] at hmap
  have hset : (Y.subtype ''
      {z : ↥Y | ∃ x : ↥Y, x ∈ (⊤ : Subgroup ↥Y) ∧ x ^ 2 = z}) =
      {z : G | ∃ y ∈ Y, y ^ 2 = z} := by
    ext z
    constructor
    · rintro ⟨w, ⟨x, -, hxw⟩, rfl⟩
      exact ⟨(x : G), x.2, by rw [← hxw]; simp⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩ ^ 2, ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩, by simp⟩
  rw [hset] at hmap
  simpa using hmap

private theorem L_one_le_normalizer_sup_commutator (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {Y : Subgroup G}
    (hNY : X.L 1 ≤ Subgroup.normalizer (Y : Set G)) :
    X.L 1 ≤ Subgroup.normalizer ((X.Z 1 ⊔ ⁅Y, X.Q 1⁆ : Subgroup G) : Set G) := by
  have hQ1eq : pCoreOf 2 (X.L 1) = X.Q 1 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  exact CFSG.GroupTheory.HuppertProduct.le_normalizer_sup
    (L_one_le_normalizer_Z_one (X := X))
    (CFSG.GroupTheory.FT63ChII.le_normalizer_commutator hNY
      (by rw [← hQ1eq]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.L 1)))

private theorem L_one_le_normalizer_sup_closure_sq {Y V : Subgroup G}
    (hNY : X.L 1 ≤ Subgroup.normalizer (Y : Set G))
    (hNV : X.L 1 ≤ Subgroup.normalizer (V : Set G)) :
    X.L 1 ≤
      Subgroup.normalizer ((V ⊔ Subgroup.closure {y ^ 2 | y ∈ Y} : Subgroup G) : Set G) :=
  CFSG.GroupTheory.HuppertProduct.le_normalizer_sup hNV
    (CFSG.GroupTheory.le_normalizer_closure_pow hNY)

private theorem commutator_le_of_le_sup_sq (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {Y Y2 : Subgroup G}
    [Finite ↥Y] [Finite ↥(X.Ki 1)]
    (hY2 : IsPGroup 2 ↥Y) (hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a)
    (hAK : X.Ki 1 ≤ Subgroup.normalizer (Y : Set G))
    (hY2Y : Y2 ≤ Y) (hcommY : ⁅Y, X.Ki 1⁆ ≤ Y2)
    (hIY2 : ⁅Y2, X.Ki 1⁆ ≤ X.Z 1) : ⁅Y, X.Ki 1⁆ ≤ X.Z 1 := by
  have hKi1odd : Odd (Nat.card ↥(X.Ki 1)) := odd_card_Ki_one C hH
  have hcop : Nat.Coprime (Nat.card ↥(X.Ki 1)) (Nat.card ↥Y) := by
    obtain ⟨e, he⟩ := hY2.exists_card_eq
    rw [he]
    exact hKi1odd.coprime_two_right.pow_right e
  haveI : Group.IsNilpotent ↥Y := hY2.isNilpotent
  have hdec := CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite
    (R := Y) (A := X.Ki 1) hAK hcop (inferInstance : Group.IsSolvable ↥Y)
  have hYle : Y ≤ Y2 ⊔ (Y ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) :=
    hdec.trans (sup_le_sup hcommY le_rfl)
  have hCnormY2 : (Y ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ≤
      Subgroup.normalizer (Y2 : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer _ <|
      Subgroup.mem_centralizer_iff.mpr fun c hc =>
        (hYcomm b hb.1 c (hY2Y hc)).symm
  rw [Subgroup.commutator_le]
  intro y hy k hk
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hCnormY2).mp (hYle hy)
  have hbk : b * k = k * b := (Subgroup.mem_centralizer_iff.mp hb.2 k hk).symm
  have e : ⁅a * b, k⁆ = ⁅a, k⁆ := by
    calc ⁅a * b, k⁆ = a * (b * k * b⁻¹) * a⁻¹ * k⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = a * k * a⁻¹ * k⁻¹ := by
          rw [show b * k * b⁻¹ = k by rw [hbk]; group]
      _ = ⁅a, k⁆ := by simp only [commutatorElement_def]
  rw [e]
  exact hIY2 (Subgroup.commutator_mem_commutator ha hk)

private theorem small_section_data (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {Y V Y2 : Subgroup G}
    (hYQ1 : Y ≤ X.Q 1) (hY2Y : Y2 ≤ Y)
    (hVdef : V = X.Z 1 ⊔ ⁅Y, X.Q 1⁆)
    (hY2def : Y2 = V ⊔ Subgroup.closure {y ^ 2 | y ∈ Y})
    (hNY : X.L 1 ≤ Subgroup.normalizer (Y : Set G))
    (hNY2 : X.L 1 ≤ Subgroup.normalizer (Y2 : Set G))
    (hcommY : ¬ ⁅Y, X.Ki 1⁆ ≤ Y2) :
    (∃ l ∈ X.L 1, ∃ v ∈ Y, ⁅l, v⁆ ∉ Y2) ∧ IsElemSec Y2 Y ∧
      X.L 1 ≤ Subgroup.normalizer (Y : Set G) ⊓ Subgroup.normalizer (Y2 : Set G) ∧
      (∀ p ∈ pCoreOf 2 (X.L 1), ∀ v ∈ Y, ⁅p, v⁆ ∈ Y2) := by
  have hQ1eq : pCoreOf 2 (X.L 1) = X.Q 1 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  have hnt : ∃ l ∈ X.L 1, ∃ v ∈ Y, ⁅l, v⁆ ∉ Y2 := by
    rw [Subgroup.commutator_le] at hcommY
    push Not at hcommY
    obtain ⟨y, hy, k, hk, hne⟩ := hcommY
    refine ⟨k, hk.2, y, hy, fun h => hne ?_⟩
    rw [(commutatorElement_inv k y).symm]
    exact Y2.inv_mem h
  have hsec : IsElemSec Y2 Y := by
    refine ⟨hY2Y, ?_, ?_⟩
    · exact (Subgroup.commutator_mono le_rfl hYQ1).trans
        (by
          have h1 : ⁅Y, X.Q 1⁆ ≤ V := by rw [hVdef]; exact le_sup_right
          rw [hY2def]
          exact le_sup_of_le_left h1)
    · intro y hy
      rw [hY2def]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨y, hy, rfl⟩)
  have hL : X.L 1 ≤ Subgroup.normalizer (Y : Set G) ⊓
      Subgroup.normalizer (Y2 : Set G) := le_inf hNY hNY2
  have hQ : ∀ p ∈ pCoreOf 2 (X.L 1), ∀ v ∈ Y, ⁅p, v⁆ ∈ Y2 := by
    rw [hQ1eq]
    intro p hp v hv
    have hmem : ⁅v, p⁆ ∈ ⁅Y, X.Q 1⁆ := Subgroup.commutator_mem_commutator hv hp
    rw [show ⁅p, v⁆ = ⁅v, p⁆⁻¹ from (commutatorElement_inv v p).symm]
    have hmemV : ⁅v, p⁆⁻¹ ∈ V := by
      rw [hVdef]
      exact Subgroup.mem_sup_right (Subgroup.inv_mem _ hmem)
    rw [hY2def]
    exact Subgroup.mem_sup_left hmemV
  exact ⟨hnt, hsec, hL, hQ⟩

private theorem false_of_small_section (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {Y V Y2 : Subgroup G} [Finite ↥Y]
    (hYQ1 : Y ≤ X.Q 1) (hYW : Y ≤ X.WQ)
    (hZY2 : X.Z 1 ≤ Y2) (hY2Y : Y2 ≤ Y) (hY2W : Y2 ≤ X.WQ)
    (hVdef : V = X.Z 1 ⊔ ⁅Y, X.Q 1⁆)
    (hY2def : Y2 = V ⊔ Subgroup.closure {y ^ 2 | y ∈ Y})
    (hNY : X.L 1 ≤ Subgroup.normalizer (Y : Set G))
    (hNY2 : X.L 1 ≤ Subgroup.normalizer (Y2 : Set G))
    (hcommY : ¬ ⁅Y, X.Ki 1⁆ ≤ Y2) : False := by
  classical
  obtain ⟨hnt, hsec, hL, hQ⟩ :=
    small_section_data C hH hYQ1 hY2Y hVdef hY2def hNY hNY2 hcommY
  haveI : Finite ↥(X.L 1) :=
    finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
  have hquot : IsL2Quot (X.n 1) (oTwoQuot ↥(X.L 1)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 1)).quot
  have hVL : Y ≤ X.L 1 := hYQ1.trans (Q_one_le_L_one (X := X))
  have hF4 := two_pow_le_relIndex_of_nontrivial_of_le
    (L := X.L 1) (V := Y) (Z := Y2) (m := X.n 1)
    (by have := C.hyp.two_le_n 1; omega) hquot hVL hsec hL hQ hnt
  haveI : Finite ↥Y2 :=
    Finite.of_injective (Subgroup.inclusion hY2Y) (Subgroup.inclusion_injective _)
  haveI : Finite ↥(X.WQ) :=
    finite_of_le_stabilizer X.hyp (H := X.WQ) ((inf_le_left : X.WQ ≤ X.Q 0).trans (X.Q_le_Gi 0))
  have hrel_le : Y2.relIndex Y ≤ (X.Z 1).relIndex X.WQ := by
    have h1 := Subgroup.relIndex_mul_relIndex (X.Z 1) Y2 Y hZY2 hY2Y
    have h2 := Subgroup.relIndex_mul_relIndex (X.Z 1) Y X.WQ (hZY2.trans hY2Y) hYW
    have hpos1 : 0 < (X.Z 1).relIndex Y2 := by
      rw [Subgroup.relIndex, Subgroup.index]
      exact Nat.card_pos
    have hpos2 : 0 < Y.relIndex X.WQ := by
      rw [Subgroup.relIndex, Subgroup.index]
      exact Nat.card_pos
    calc Y2.relIndex Y ≤ (X.Z 1).relIndex Y2 * (Y2.relIndex Y) :=
          Nat.le_mul_of_pos_left _ hpos1
      _ = (X.Z 1).relIndex Y := h1
      _ ≤ (X.Z 1).relIndex Y * (Y.relIndex X.WQ) := Nat.le_mul_of_pos_right _ hpos2
      _ = (X.Z 1).relIndex X.WQ := h2
  rw [Z_one_relIndex_WQ C hH] at hrel_le
  have hn1 : X.n 1 = X.n 0 := C.n_one_eq hH
  have hlt : 2 ^ X.n 0 < 2 ^ (2 * X.n 1) := by
    rw [hn1]
    exact Nat.pow_lt_pow_right (by norm_num) (by have := C.hyp.two_le_n 0; omega)
  exact (not_le_of_gt hlt) (hF4.trans hrel_le)

private theorem commutator_WQ_Ki_one_le_Z_one (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : ⁅X.WQ, X.Ki 1⁆ ≤ X.Z 1 := by
  classical
  have hZ1leW : X.Z 1 ≤ X.WQ := Z_one_le_WQ C hH
  have hL1normW : X.L 1 ≤ Subgroup.normalizer (X.WQ : Set G) := L_one_le_normalizer_WQ C hH
  haveI : Finite ↥(X.Ki 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Ki 1)
      ((inf_le_right : X.Ki 1 ≤ X.L 1).trans (X.L_le_Gi 1))
  have key : ∀ m, ∀ Y : Subgroup G, X.Z 1 ≤ Y → Y ≤ X.WQ →
      X.L 1 ≤ Subgroup.normalizer (Y : Set G) → Nat.card ↥Y = m →
      ⁅Y, X.Ki 1⁆ ≤ X.Z 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro Y hZY hYW hNY hcardY
      by_contra hnot
      have hYne : Y ≠ X.Z 1 := by
        intro hYeq
        apply hnot
        rw [hYeq]
        have hZL : ⁅X.Z 1, X.L 1⁆ ≤ X.Z 1 := by
          rw [Subgroup.commutator_comm]
          exact Subgroup.le_normalizer_iff_commutator_le_right.mp
            (L_one_le_normalizer_Z_one (X := X))
        exact (Subgroup.commutator_mono le_rfl (inf_le_right : X.Ki 1 ≤ X.L 1)).trans hZL
      have hYQ1 : Y ≤ X.Q 1 := hYW.trans (WQ_le_Q_one C)
      haveI : Finite ↥Y :=
        finite_of_le_stabilizer X.hyp (H := Y) (hYQ1.trans (X.Q_le_Gi 1))
      have hY2 : IsPGroup 2 ↥Y :=
        ((pCoreOf_isPGroup' (X.Gi 0)).to_le (hYW.trans inf_le_left))
      have hVlt : X.Z 1 ⊔ ⁅Y, X.Q 1⁆ < Y :=
        sup_commutator_Q1_lt C hH hZY hYW hNY hYne
      set V : Subgroup G := X.Z 1 ⊔ ⁅Y, X.Q 1⁆ with hVdef
      have hY₂lt : V ⊔ Subgroup.closure {y ^ 2 | y ∈ Y} < Y :=
        sup_closure_sq_lt (Y := Y) (V := V) hY2 hVlt
      set Y2 : Subgroup G := V ⊔ Subgroup.closure {y ^ 2 | y ∈ Y} with hY2def
      have hZY2 : X.Z 1 ≤ Y2 := by
        rw [hY2def]; exact le_sup_of_le_left (by rw [hVdef]; exact le_sup_left)
      have hY2Y : Y2 ≤ Y := hY₂lt.le
      have hY2W : Y2 ≤ X.WQ := hY2Y.trans hYW
      have hNV : X.L 1 ≤ Subgroup.normalizer (V : Set G) := by
        rw [hVdef]; exact L_one_le_normalizer_sup_commutator C hH hNY
      have hNY2 : X.L 1 ≤ Subgroup.normalizer (Y2 : Set G) := by
        rw [hY2def]; exact L_one_le_normalizer_sup_closure_sq hNY hNV
      have hltcard : Nat.card ↥Y2 < m := by
        rw [← hcardY]
        exact Subgroup.card_lt_of_lt hY₂lt
      have hIY2 : ⁅Y2, X.Ki 1⁆ ≤ X.Z 1 :=
        ih (Nat.card ↥Y2) hltcard Y2 hZY2 hY2W hNY2 rfl
      by_cases hcommY : ⁅Y, X.Ki 1⁆ ≤ Y2
      · have hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
          WQ_comm C hH a (hYW ha) b (hYW hb)
        have hAK : X.Ki 1 ≤ Subgroup.normalizer (Y : Set G) :=
          (inf_le_right : X.Ki 1 ≤ X.L 1).trans hNY
        exact hnot (commutator_le_of_le_sup_sq C hH hY2 hYcomm hAK hY2Y hcommY hIY2)
      · exact false_of_small_section C hH hYQ1 hYW hZY2 hY2Y hY2W hVdef hY2def hNY hNY2 hcommY
  exact key (Nat.card X.WQ) X.WQ hZ1leW le_rfl hL1normW rfl

private theorem Ki_one_fix_nbrs_zero (C : X.Comm48 s r d)
    (hfixm1 : ∀ w, Γ.Adj (X.vert 0) w → ∀ x ∈ X.Ki (-1), x • w = w) :
    ∀ w, Γ.Adj (X.vert 0) w → ∀ x ∈ X.Ki 1, x • w = w := by
  obtain ⟨t, htGN, ht, -⟩ := X.exists_reflection_oTwoRes C.hyp 0
  have ht1 : t • X.vert (-1) = X.vert 1 := by
    have h := ht (-1)
    rwa [show (0 : ℤ) + -1 = -1 by norm_num, show (0 : ℤ) - -1 = 1 by norm_num] at h
  have ht0 : t • X.vert 0 = X.vert 0 :=
    MulAction.mem_stabilizer_iff.mp (X.L_le_Gi 0 (oTwoRes_le (X.L 0) htGN.1))
  have hK1t : X.Ki 1 = conjSub t (X.Ki (-1)) := s48e_Ki_smul htGN.2 ht1
  rw [hK1t]
  exact s48e_fixes_conj ht0 hfixm1

private theorem Ki_four_and_neg_one_eq_Ki_one (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hfixm1 : ∀ w, Γ.Adj (X.vert 0) w → ∀ x ∈ X.Ki (-1), x • w = w)
    (hfix1 : ∀ w, Γ.Adj (X.vert 0) w → ∀ x ∈ X.Ki 1, x • w = w)
    (hfix4 : ∀ w, Γ.Adj (X.vert 0) w → ∀ x ∈ X.Ki 4, x • w = w) :
    X.Ki 4 = X.Ki 1 ∧ X.Ki (-1) = X.Ki 1 := by
  have hn4 : X.n 4 = X.n 0 := by
    have h := X.n_add 2 0
    rwa [show (0 : ℤ) + 2 * 2 = 4 by norm_num] at h
  have hn1 : X.n 1 = X.n 0 := C.n_one_eq hH
  have hnm1 : X.n (-1) = X.n 0 := by
    have h := X.n_add (-1) 1
    rw [hn1] at h
    rwa [show (1 : ℤ) + 2 * (-1) = -1 by norm_num] at h
  have hcardKi0 : Nat.card ↥(X.Ki 0) = 2 ^ X.n 0 - 1 := X.card_Ki 0
  have hcardKi4 : Nat.card ↥(X.Ki 4) = 2 ^ X.n 0 - 1 := by
    rw [X.card_Ki 4, hn4]
  have hcardKi1 : Nat.card ↥(X.Ki 1) = 2 ^ X.n 0 - 1 := by
    rw [X.card_Ki 1, hn1]
  have hcardKim1 : Nat.card ↥(X.Ki (-1)) = 2 ^ X.n 0 - 1 := by
    rw [X.card_Ki (-1), hnm1]
  exact
    ⟨s48e_eq_of_fixes 0 (C.card_K hH) hcardKi0 inf_le_left inf_le_left
        hcardKi4 hcardKi1 hfix4 hfix1,
      s48e_eq_of_fixes 0 (C.card_K hH) hcardKi0 inf_le_left inf_le_left
        hcardKim1 hcardKi1 hfixm1 hfix1⟩

private theorem Ki_zero_eq_Ki_one (hK41 : X.Ki 4 = X.Ki 1)
    (hKm11 : X.Ki (-1) = X.Ki 1) : X.Ki 0 = X.Ki 1 := by
  have hKm1 : X.Ki (-1) = conjSub (X.τ ^ (-1 : ℤ)) (X.Ki 1) := by
    have h := s48e_Ki_add (X := X) (-1) 1
    rwa [show (1 : ℤ) + 2 * (-1) = -1 by norm_num] at h
  have e2 : X.Ki (-3) = conjSub (X.τ ^ (-1 : ℤ)) (X.Ki (-1)) := by
    have h := s48e_Ki_add (X := X) (-1) (-1)
    rwa [show (-1 : ℤ) + 2 * (-1) = -3 by norm_num] at h
  have e3 : X.Ki 0 = conjSub (X.τ ^ (-2 : ℤ)) (X.Ki 4) := by
    have h := s48e_Ki_add (X := X) (-2) 4
    rwa [show (4 : ℤ) + 2 * (-2) = 0 by norm_num] at h
  have e4 : X.Ki (-3) = conjSub (X.τ ^ (-2 : ℤ)) (X.Ki 1) := by
    have h := s48e_Ki_add (X := X) (-2) 1
    rwa [show (1 : ℤ) + 2 * (-2) = -3 by norm_num] at h
  rw [e3, hK41, ← e4, e2, hKm11, ← hKm1, hKm11]

private theorem Z_neg_two_inf_centralizer_Ki_one (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z (-2) ⊓ Subgroup.centralizer (X.Ki 1 : Set G) = ⊥ := by
  obtain ⟨h6inf, -, h6fix⟩ := X.s48_6 C
  obtain ⟨hr8, hd3⟩ := X.s48_12 C hH
  subst d
  subst r
  by_contra hne
  obtain ⟨hBm2_4, hZneg2pc, -, -⟩ := s48e_Z_neg_two (X := X) C hH
  have hKZ : X.K ≤ Subgroup.normalizer (X.Z (-2) : Set G) := fun g hg =>
    mem_normalizer_iff_conjSub.mpr (X.Z_normal (-2) g (X.K_le_Gi (-2) hg))
  have hKH : X.K ≤ Subgroup.normalizer
      ((X.Z (-2) ⊓ Subgroup.centralizer (X.Ki 1 : Set G) : Subgroup G) : Set G) :=
    (le_inf hKZ (B6.le_normalizer_centralizer (s48e_K_le_normalizer_Ki 1))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hZC : X.Z (-2) ≤ Subgroup.centralizer (X.Ki 1 : Set G) := by
    have heq := X.eq_of_le_pCoreOf_arcStab_r C.hyp (a := -6) hKH hne
      (inf_le_left.trans hZneg2pc.le)
    have heq' : X.Z (-2) ⊓ Subgroup.centralizer (X.Ki 1 : Set G) = X.Z (-2) :=
      heq.trans hZneg2pc.symm
    rw [← heq']
    exact inf_le_right
  have hle1 : X.Z (-2) ≤ X.Q 1 := X.Z_le_Q_of_lt hBm2_4 (j := 1) (by norm_num)
  have hnot2 : ¬ X.Z (-2) ≤ X.Q 2 := fun h =>
    (X.not_Z_le_Q_edge hBm2_4).1 (by simpa using h)
  have hPS : X.Z (-2) ⊔ X.Q 2 = X.edgeSylow 1 :=
    X.sup_Q_eq_edgeSylow_of_gen (i := 1) (A := X.Z (-2)) (inf_le_left.trans hKZ)
      (hle1.trans (X.Q_le_edgeSylow_left 1)) hnot2
  have hP : IsPGroup 2 (X.Z (-2)) := (pCoreOf_isPGroup' (X.Gi (-2))).to_le (X.Z_le_Q (-2))
  have hfix2 : ∀ w, Γ.Adj (X.vert 2) w → ∀ x ∈ X.Ki 1, x • w = w :=
    (X.fix_nbrs_of_centralizes C.hyp.char 2 (U := X.Ki 1) (P := X.Z (-2)) inf_le_left hP
      (Or.inr hPS) hZC).1
  have hτ : X.τ ^ (-1 : ℤ) • X.vert 2 = X.vert 0 := by
    have h := X.zpow_smul_vert (-1) 2
    rwa [show (2 : ℤ) + 2 * (-1) = 0 by norm_num] at h
  have hKm1 : X.Ki (-1) = conjSub (X.τ ^ (-1 : ℤ)) (X.Ki 1) := by
    have h := s48e_Ki_add (X := X) (-1) 1
    rwa [show (1 : ℤ) + 2 * (-1) = -1 by norm_num] at h
  have hfixm1 : ∀ w, Γ.Adj (X.vert 0) w → ∀ x ∈ X.Ki (-1), x • w = w := by
    rw [hKm1]
    exact s48e_fixes_conj hτ hfix2
  have hfix1 : ∀ w, Γ.Adj (X.vert 0) w → ∀ x ∈ X.Ki 1, x • w = w :=
    Ki_one_fix_nbrs_zero C hfixm1
  obtain ⟨hK41, hKm11⟩ :=
    Ki_four_and_neg_one_eq_Ki_one C hH hfixm1 hfix1 (by simpa using h6fix)
  have hK0 : X.Ki 0 = X.Ki 1 := Ki_zero_eq_Ki_one hK41 hKm11
  have h6 : X.Ki 4 ⊓ X.Ki 0 = ⊥ := by simpa using h6inf
  rw [hK41, ← hK0, inf_idem] at h6
  have h3 : Nat.card ↥(X.Ki 0) = 2 ^ X.n 0 - 1 := X.card_Ki 0
  rw [h6, Subgroup.card_bot] at h3
  have hge : 4 ≤ 2 ^ X.n 0 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) (C.hyp.two_le_n 0)
  omega

private theorem K_le_normalizer_PQ : X.K ≤ Subgroup.normalizer (X.PQ : Set G) :=
  (le_inf (X.K_le_Gi 0) (X.K_le_Gi 1)).trans X.inf_Gi_le_normalizer_inf_Q

private theorem PQ_commute_Z_one : ∀ x ∈ X.PQ, ∀ c ∈ X.Z 1, x * c = c * x := fun x hx c hc =>
  Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 1 hc)).2 x hx.2

private theorem PQ_le_normalizer_Z_zero : X.PQ ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
  fun x hx => mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 x (X.Q_le_Gi 0 hx.1))

private theorem K_le_normalizer_YQ : X.K ≤ Subgroup.normalizer (X.YQ : Set G) := fun g hg =>
  s48e_mem_normalizer_relCent (K_le_normalizer_PQ hg)
    (mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 g (X.K_le_Gi 0 hg)))
    (mem_normalizer_iff_conjSub.mpr (X.Z_normal 4 g (X.K_le_Gi 4 hg)))

private theorem YQ_le_PQ : X.YQ ≤ X.PQ := fun y hy => by
  obtain ⟨h, -, -⟩ := hy
  exact h

private theorem PQ_le_normalizer_YQ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.PQ ≤ Subgroup.normalizer (X.YQ : Set G) := by
  obtain ⟨-, -, -, -, hZ1elem, -⟩ := X.s48_4' C hH
  exact s48e_le_normalizer_relCent (s48e_PQ_Z_four C hH) PQ_commute_Z_one
    (fun c hc c' hc' => hZ1elem.comm hc hc') PQ_le_normalizer_Z_zero

private theorem Z_one_le_YQ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 1 ≤ X.YQ := by
  obtain ⟨hV0eq, -, -, hV0le, -⟩ := X.s48_8 C hH
  obtain ⟨-, h41, -⟩ := s48e_Z_four C hH
  have hZ1leV0 : X.Z 1 ≤ X.Vk 0 := by
    rw [hV0eq]
    exact le_sup_left
  have hZ1leP : X.Z 1 ≤ X.PQ := hZ1leV0.trans hV0le
  have hZ1cent : ∀ c ∈ X.Z 1, c ∈ Subgroup.centralizer (X.Q 1 : Set G) := fun c hc =>
    (Subgroup.mem_inf.mp (X.Z_le_center 1 hc)).2
  have hZ4Z1 : ∀ z ∈ X.Z 4, ∀ c ∈ X.Z 1, z * c = c * z := fun z hz c hc =>
    Subgroup.mem_centralizer_iff.mp (hZ1cent c hc) z (h41 hz)
  intro c hc
  refine (mem_relCent PQ_le_normalizer_Z_zero).mpr ⟨hZ1leP hc, fun z hz => ?_⟩
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hZ4Z1 z hz c hc).symm]
  exact (X.Z 0).one_mem

private theorem YQ_inf_Vk_zero_le_relCent (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.YQ ⊓ X.Vk 0 ≤ relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0) := by
  obtain ⟨-, -, -, hV0le, hcommV0, -, -⟩ := X.s48_8 C hH
  obtain ⟨-, h41, -, h40, -, hnot40, -⟩ := s48e_Z_four C hH
  have hKZ : ∀ i : ℤ, X.K ≤ Subgroup.normalizer (X.Z i : Set G) := fun i g hg =>
    mem_normalizer_iff_conjSub.mpr (X.Z_normal i g (X.K_le_Gi i hg))
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI : Finite ↥X.PQ :=
    Finite.of_injective
      (Subgroup.inclusion ((show X.PQ ≤ X.Q 0 from inf_le_left).trans (X.Q_le_Gi 0)))
      (Subgroup.inclusion_injective _)
  have hS : X.Z 4 ⊔ X.Q 0 = X.edgeSylow 0 :=
    X.sup_Q_eq_edgeSylow_of_left_gen (i := 0) (A := X.Z 4) (inf_le_left.trans (hKZ 4))
      (h41.trans (by simpa using X.Q_le_edgeSylow (i := 0))) hnot40
  have hG0Z0 : X.Gi 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := fun g hg =>
    mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 g hg)
  have hYV_S : ⁅X.YQ ⊓ X.Vk 0, X.edgeSylow 0⁆ ≤ X.Z 0 := by
    rw [← hS]
    refine CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer (h40.trans hG0Z0)
      ((X.Q_le_Gi 0).trans hG0Z0) ?_ ?_
    · rw [Subgroup.commutator_le]
      intro y hy z hz
      obtain ⟨⟨-, -, hyc⟩, -⟩ := hy
      exact hyc z hz
    · exact (Subgroup.commutator_mono inf_le_right le_rfl).trans (le_of_eq hcommV0)
  have hV0Z0 : X.Vk 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    hV0le.trans PQ_le_normalizer_Z_zero
  intro y hy
  exact (mem_relCent hV0Z0).mpr ⟨hy.2, fun t ht =>
    hYV_S (Subgroup.commutator_mem_commutator hy ht)⟩

private theorem YQ_inf_Vk_zero_eq_Z_one (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.YQ ⊓ X.Vk 0 = X.Z 1 := by
  obtain ⟨hV0eq, -, -, hV0le, -, hnatV0, -⟩ := X.s48_8 C hH
  obtain ⟨-, -, -, hZ1card, -⟩ := X.s48_4' C hH
  obtain ⟨hZ0le, -⟩ := X.s48_1 C
  obtain ⟨-, -, -, -, hZ0card, -⟩ := X.s48_2 C
  have hZ1Y := Z_one_le_YQ C hH
  have hZ1leV0 : X.Z 1 ≤ X.Vk 0 := by
    rw [hV0eq]
    exact le_sup_left
  have hYVleR := YQ_inf_Vk_zero_le_relCent C hH
  have hZ1R : X.Z 1 ≤ relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0) :=
    (le_inf hZ1Y hZ1leV0).trans hYVleR
  have hRle : relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0) ≤ X.PQ := fun x hx => by
    obtain ⟨hxV, -, -⟩ := hx
    exact hV0le hxV
  haveI : Finite ↥X.PQ :=
    finite_of_le_stabilizer X.hyp (H := X.PQ) (inf_le_left.trans (X.Q_le_Gi 0))
  haveI : Finite ↥(relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0)) :=
    Finite.of_injective (Subgroup.inclusion hRle) (Subgroup.inclusion_injective _)
  have hSylL : IsSylowTwoOf (X.edgeSylow 0) (X.L 0) := X.isSylowTwoOf_edgeSylow_L 0
  have hRcard : Nat.card ↥(relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0)) = 2 ^ (2 * X.n 0) := by
    have hline := hnatV0.line (X.edgeSylow 0) hSylL
    have h := Subgroup.relIndex_mul_card (H := X.Z 0)
      (K := relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0))
    rw [inf_eq_left.mpr (hZ0le.trans hZ1R), hline, hZ0card] at h
    have hpow : 2 ^ (2 * X.n 0) = 2 ^ X.n 0 * 2 ^ X.n 0 := by
      rw [← pow_add]
      congr 1
      ring
    rw [hpow]
    exact h.symm
  have hZ1eqR : X.Z 1 = relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0) :=
    Subgroup.eq_of_le_of_card_ge hZ1R (by rw [hRcard, hZ1card])
  exact le_antisymm (hYVleR.trans hZ1eqR.ge) (le_inf hZ1Y hZ1leV0)

private theorem YQ_sup_Vk_zero_eq_PQ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hY : X.YQ.relIndex X.PQ ≤ 2 ^ X.n 0) : X.YQ ⊔ X.Vk 0 = X.PQ := by
  obtain ⟨-, hV0card, -, hV0le, -⟩ := X.s48_8 C hH
  obtain ⟨-, -, -, hZ1card, -⟩ := X.s48_4' C hH
  have he1 := YQ_inf_Vk_zero_eq_Z_one C hH
  have hidx := hY
  have hYle : X.YQ ≤ X.PQ := YQ_le_PQ
  have hV0normY : X.Vk 0 ≤ Subgroup.normalizer (X.YQ : Set G) :=
    hV0le.trans (PQ_le_normalizer_YQ C hH)
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI : Finite ↥X.PQ :=
    Finite.of_injective
      (Subgroup.inclusion ((show X.PQ ≤ X.Q 0 from inf_le_left).trans (X.Q_le_Gi 0)))
      (Subgroup.inclusion_injective _)
  have hrelsup : X.YQ.relIndex (X.Vk 0 ⊔ X.YQ) = X.YQ.relIndex (X.Vk 0) :=
    CFSG.Quasithin.B2F.relIndex_sup_eq_of_le_normalizer' hV0normY
  have hrelV : X.YQ.relIndex (X.Vk 0) = 2 ^ X.n 0 := by
    have h := Subgroup.relIndex_mul_card (H := X.YQ) (K := X.Vk 0)
    rw [he1, hZ1card, hV0card] at h
    have hpow : 2 ^ (3 * X.n 0) = 2 ^ X.n 0 * 2 ^ (2 * X.n 0) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by norm_num)) h
  have hcardYV : Nat.card ↥(X.Vk 0 ⊔ X.YQ) = 2 ^ X.n 0 * Nat.card ↥X.YQ := by
    have h := Subgroup.relIndex_mul_card (H := X.YQ) (K := X.Vk 0 ⊔ X.YQ)
    rw [inf_eq_left.mpr le_sup_right, hrelsup, hrelV] at h
    exact h.symm
  have hcardP : Nat.card ↥X.PQ ≤ 2 ^ X.n 0 * Nat.card ↥X.YQ := by
    have h := Subgroup.relIndex_mul_card (H := X.YQ) (K := X.PQ)
    rw [inf_eq_left.mpr hYle] at h
    rw [← h]
    exact Nat.mul_le_mul_right _ hidx
  rw [sup_comm]
  exact Subgroup.eq_of_le_of_card_ge (sup_le hV0le hYle) (by rw [hcardYV]; exact hcardP)

private theorem mem_Z_one_of_commutator_Ki_one_le (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ∀ v ∈ X.Vk 0, (∀ t ∈ X.Ki 1, ⁅v, t⁆ ∈ X.Z 1) → v ∈ X.Z 1 := by
  obtain ⟨hV0eq, -, hV0ab, -⟩ := X.s48_8 C hH
  obtain ⟨hZ0le, -⟩ := X.s48_1 C
  obtain ⟨-, -, hZm2infQ2, hZm1eq⟩ := s48e_Z_neg_two C hH
  have hZ1leQ2 : X.Z 1 ≤ X.Q 2 := (Z_one_le_WQ C hH).trans inf_le_right
  have hZ1leV0 : X.Z 1 ≤ X.Vk 0 := by
    rw [hV0eq]
    exact le_sup_left
  have hV0eq' : X.Vk 0 = X.Z (-2) ⊔ X.Z 1 := by
    rw [hV0eq, hZm1eq, sup_comm (X.Z (-2)) (X.Z 0), ← sup_assoc, sup_eq_left.mpr hZ0le]
    exact sup_comm _ _
  have hZm2leV0 : X.Z (-2) ≤ X.Vk 0 := by
    rw [hV0eq']
    exact le_sup_left
  have hV0comm : ∀ a ∈ X.Vk 0, ∀ b ∈ X.Vk 0, a * b = b * a := fun a ha b hb =>
    hV0ab.comm ha hb
  have hZ1normZm2 : X.Z 1 ≤ Subgroup.normalizer (X.Z (-2) : Set G) := by
    intro c hc
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hV0comm z (hZm2leV0 hz) c (hZ1leV0 hc)
  have hKZ : ∀ i : ℤ, X.K ≤ Subgroup.normalizer (X.Z i : Set G) := fun i g hg =>
    mem_normalizer_iff_conjSub.mpr (X.Z_normal i g (X.K_le_Gi i hg))
  intro v hv hvt
  rw [hV0eq'] at hv
  obtain ⟨z, hz, c, hc, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hZ1normZm2).mp hv
  have hzC : z ∈ X.Z (-2) ⊓ Subgroup.centralizer (X.Ki 1 : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hz, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have htZm2 : ⁅z, t⁆ ∈ X.Z (-2) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (hKZ (-2))
        (Subgroup.commutator_mem_commutator hz ht.1)
    have hct : ⁅c, t⁆ ∈ X.Z 1 :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (hKZ 1)
        (Subgroup.commutator_mem_commutator hc ht.1)
    have htZ1 : ⁅z, t⁆ ∈ X.Z 1 := by
      have e : ⁅z, t⁆ = (z * ⁅c, t⁆ * z⁻¹)⁻¹ * ⁅z * c, t⁆ := by
        simp only [commutatorElement_def]; group
      rw [e, hV0comm z (hZm2leV0 hz) _ (hZ1leV0 hct), mul_inv_cancel_right]
      exact (X.Z 1).mul_mem ((X.Z 1).inv_mem hct) (hvt t ht)
    have hbot : ⁅z, t⁆ ∈ X.Z (-2) ⊓ X.Q 2 := ⟨htZm2, hZ1leQ2 htZ1⟩
    rw [hZm2infQ2] at hbot
    exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hbot)).symm
  rw [Z_neg_two_inf_centralizer_Ki_one C hH] at hzC
  rw [Subgroup.mem_bot.mp hzC, one_mul]
  exact hc

private theorem YQ_le_WQ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.YQ ≤ X.WQ := by
  obtain ⟨hV0eq, -, hV0ab, -⟩ := X.s48_8 C hH
  have hPeq := PQ_eq_Vk_zero_sup_WQ C hH
  have hWK1 := commutator_WQ_Ki_one_le_Z_one C hH
  have hYVinf := YQ_inf_Vk_zero_eq_Z_one C hH
  have hmemZ1 := mem_Z_one_of_commutator_Ki_one_le C hH
  have hZ1leW := Z_one_le_WQ C hH
  have hYle : X.YQ ≤ X.PQ := YQ_le_PQ
  have hKiY : X.Ki 1 ≤ Subgroup.normalizer (X.YQ : Set G) := fun t ht =>
    K_le_normalizer_YQ ht.1
  have hZ1leV0 : X.Z 1 ≤ X.Vk 0 := by
    rw [hV0eq]
    exact le_sup_left
  have hV0comm : ∀ a ∈ X.Vk 0, ∀ b ∈ X.Vk 0, a * b = b * a := fun a ha b hb =>
    hV0ab.comm ha hb
  have hKV0 : X.K ≤ Subgroup.normalizer (X.Vk 0 : Set G) :=
    (X.K_le_Gi 0).trans (X.Gi_le_normalizer_Vk 0)
  have hWnormV0 : X.WQ ≤ Subgroup.normalizer (X.Vk 0 : Set G) :=
    (inf_le_left.trans (X.Q_le_Gi 0)).trans (X.Gi_le_normalizer_Vk 0)
  intro y hy
  have hyP : y ∈ X.Vk 0 ⊔ X.WQ := by
    rw [← hPeq]
    exact hYle hy
  obtain ⟨v, hv, w, hw, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hWnormV0).mp hyP
  have hvt : ∀ t ∈ X.Ki 1, ⁅v, t⁆ ∈ X.Z 1 := by
    intro t ht
    have hwt : ⁅w, t⁆ ∈ X.Z 1 := hWK1 (Subgroup.commutator_mem_commutator hw ht)
    have hvtV : ⁅v, t⁆ ∈ X.Vk 0 :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hKV0
        (Subgroup.commutator_mem_commutator hv ht.1)
    have hytY : ⁅v * w, t⁆ ∈ X.YQ :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hKiY
        (Subgroup.commutator_mem_commutator hy ht)
    have e2 : ⁅v * w, t⁆ = v * ⁅w, t⁆ * v⁻¹ * ⁅v, t⁆ := by
      simp only [commutatorElement_def]; group
    have hytV : ⁅v * w, t⁆ ∈ X.Vk 0 := by
      rw [e2]
      exact (X.Vk 0).mul_mem ((X.Vk 0).mul_mem ((X.Vk 0).mul_mem hv (hZ1leV0 hwt))
        ((X.Vk 0).inv_mem hv)) hvtV
    have hytZ1 : ⁅v * w, t⁆ ∈ X.Z 1 := by
      rw [← hYVinf]
      exact ⟨hytY, hytV⟩
    have hconj : v * ⁅w, t⁆ * v⁻¹ = ⁅w, t⁆ := by
      rw [hV0comm v hv _ (hZ1leV0 hwt), mul_inv_cancel_right]
    have e3 : ⁅v, t⁆ = (v * ⁅w, t⁆ * v⁻¹)⁻¹ * ⁅v * w, t⁆ := by
      rw [e2]; group
    rw [e3, hconj]
    exact (X.Z 1).mul_mem ((X.Z 1).inv_mem hwt) hytZ1
  exact X.WQ.mul_mem (hZ1leW (hmemZ1 v hv hvt)) hw

private theorem YQ_eq_WQ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hY : X.YQ.relIndex X.PQ ≤ 2 ^ X.n 0) : X.YQ = X.WQ := by
  have hPeq := PQ_eq_Vk_zero_sup_WQ C hH
  have hYVinf := YQ_inf_Vk_zero_eq_Z_one C hH
  have hYVsup : X.YQ ⊔ X.Vk 0 = X.PQ := YQ_sup_Vk_zero_eq_PQ C hH hY
  have hYle : X.YQ ≤ X.PQ := YQ_le_PQ
  have hVinfW := Vk_zero_inf_WQ C hH
  have hWnormV0 : X.WQ ≤ Subgroup.normalizer (X.Vk 0 : Set G) :=
    (inf_le_left.trans (X.Q_le_Gi 0)).trans (X.Gi_le_normalizer_Vk 0)
  have hV0normY : X.YQ ≤ Subgroup.normalizer (X.Vk 0 : Set G) :=
    (hYle.trans (inf_le_left.trans (X.Q_le_Gi 0))).trans (X.Gi_le_normalizer_Vk 0)
  have hr1 : (X.Vk 0).relIndex (X.YQ ⊔ X.Vk 0) = (X.Vk 0).relIndex X.YQ :=
    CFSG.Quasithin.B2F.relIndex_sup_eq_of_le_normalizer' hV0normY
  have hr2 : (X.Vk 0).relIndex (X.WQ ⊔ X.Vk 0) = (X.Vk 0).relIndex X.WQ :=
    CFSG.Quasithin.B2F.relIndex_sup_eq_of_le_normalizer' hWnormV0
  have hrYW : (X.Vk 0).relIndex X.YQ = (X.Vk 0).relIndex X.WQ := by
    rw [← hr1, ← hr2, hYVsup, sup_comm X.WQ, ← hPeq]
  have hcYW : Nat.card ↥X.YQ = Nat.card ↥X.WQ := by
    have h1 := Subgroup.relIndex_mul_card (H := X.Vk 0) (K := X.YQ)
    have h2 := Subgroup.relIndex_mul_card (H := X.Vk 0) (K := X.WQ)
    rw [inf_comm, hYVinf] at h1
    rw [hVinfW] at h2
    rw [← h1, ← h2, hrYW]
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI : Finite ↥X.WQ :=
    Finite.of_injective (Subgroup.inclusion ((inf_le_left : X.WQ ≤ X.Q 0).trans (X.Q_le_Gi 0)))
      (Subgroup.inclusion_injective _)
  exact Subgroup.eq_of_le_of_card_ge (YQ_le_WQ C hH) hcYW.ge

private theorem WQ_le_centralizer_Vk_two (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hY : X.YQ.relIndex X.PQ ≤ 2 ^ X.n 0) : X.WQ ≤ Subgroup.centralizer (X.Vk 2 : Set G) := by
  obtain ⟨hV2eq, -⟩ := X.s48_13 C hH
  obtain ⟨-, -, hZ0Z2, -⟩ := X.s48_4' C hH
  obtain ⟨-, -, h42, -⟩ := s48e_Z_four C hH
  have hcommQ2 := commutator_Q_two_le_Z_two C hH
  have hYeqW := YQ_eq_WQ C hH hY
  have hWleQ1 : X.WQ ≤ X.Q 1 := WQ_le_Q_one C
  have hWcentZ4 : ∀ w ∈ X.WQ, ∀ z ∈ X.Z 4, w * z = z * w := by
    intro w hw z hz
    have hwY : w ∈ X.YQ := by
      rw [hYeqW]
      exact hw
    have h0 : ⁅w, z⁆ ∈ X.Z 0 := by
      obtain ⟨-, -, h⟩ := hwY
      exact h z hz
    have h2 : ⁅w, z⁆ ∈ X.Z 2 := hcommQ2 (Subgroup.commutator_mem_commutator hw.2 (h42 hz))
    have hbot : ⁅w, z⁆ ∈ X.Z 0 ⊓ X.Z 2 := ⟨h0, h2⟩
    rw [hZ0Z2] at hbot
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hbot)
  have hWcentZ1 : ∀ w ∈ X.WQ, ∀ c ∈ X.Z 1, w * c = c * w := fun w hw c hc =>
    Subgroup.mem_centralizer_iff.mp ((Subgroup.mem_inf.mp (X.Z_le_center 1 hc)).2) w
      (hWleQ1 hw)
  have hV2leC : X.Vk 2 ≤ Subgroup.centralizer (X.WQ : Set G) := by
    rw [hV2eq]
    refine sup_le ?_ ?_
    · intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact hWcentZ1 w hw c hc
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact hWcentZ4 w hw z hz
  exact Subgroup.le_centralizer_iff.mp hV2leC

private theorem s48e_false_of_le (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hY : X.YQ.relIndex X.PQ ≤ 2 ^ X.n 0) : False := by
  obtain ⟨hV0eq, -⟩ := X.s48_8 C hH
  obtain ⟨hV2eq, hV2inf, -⟩ := X.s48_13 C hH
  obtain ⟨-, hZ1sup, -, hZ1card, -⟩ := X.s48_4' C hH
  have hWleC := WQ_le_centralizer_Vk_two C hH hY
  have hconjV0 : conjSub (X.τ ^ (1 : ℤ)) (X.Vk 0) = X.Vk 2 := by
    simpa using (X.Vk_add 1 0).symm
  have hcQ : conjSub (X.τ ^ (1 : ℤ)) (X.Q 0) = X.Q 2 := by
    simpa using (X.Q_add 1 0).symm
  have hcentV2 : X.Q 2 ⊓ Subgroup.centralizer (X.Vk 2 : Set G) = X.Vk 2 := by
    have h := congrArg (conjSub (X.τ ^ (1 : ℤ))) (Q_zero_inf_centralizer_Vk_zero C hH)
    rw [conjSub_inf, ← conjSub_centralizer, hcQ, hconjV0] at h
    exact h
  have hWV2 : X.WQ ≤ X.Vk 2 := by
    rw [← hcentV2]
    exact le_inf inf_le_right hWleC
  have hWZ1 : X.WQ ≤ X.Z 1 := by
    rw [← hV2inf]
    exact le_inf hWV2 inf_le_left
  haveI : Finite ↥(X.Gi 1) := X.hyp.finite_stab (X.vert 1)
  haveI : Finite ↥(X.Z 1) :=
    Finite.of_injective (Subgroup.inclusion (X.Z_le_Gi 1)) (Subgroup.inclusion_injective _)
  have hc := Subgroup.card_le_of_le hWZ1
  rw [card_WQ C hH, hZ1card] at hc
  have hlt : 2 ^ (2 * X.n 0) < 2 ^ (3 * X.n 0) :=
    Nat.pow_lt_pow_right (by norm_num) (by have := C.hyp.two_le_n 0; omega)
  exact (not_le_of_gt hlt) hc

private theorem false_of_le_of_relIndex (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hY : (relCent (X.Q 0 ⊓ X.Q 1) (X.Z 0) (X.Z 4)).relIndex (X.Q 0 ⊓ X.Q 1) ≤ 2 ^ X.n 0) :
    False := by
  exact s48e_false_of_le C hH (by simpa [YQ, PQ] using hY)

private theorem s48e_exists_alpha :
    ∃ α : ↥(X.L 0) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 0)),
      Function.Surjective α ∧ α.ker = (X.Q 0).subgroupOf (X.L 0) ∧
      (X.S.subgroupOf (X.L 0)).map α =
        CFSG.Timmesfeld.upperUnipotent (GaloisField 2 (X.n 0)) := by
  have hP : IsSylowTwoOf X.S (X.L 0) := by
    simpa [X.edgeSylow_zero] using X.isSylowTwoOf_edgeSylow_L 0
  have hq : IsL2Quot (X.n 0) (oTwoQuot ↥(X.L 0)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
  have hp : pCoreOf 2 (X.L 0) = X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  obtain ⟨α, hα, hker, hU⟩ :=
    CFSG.GroupTheory.exists_SL2_hom_map_sylowTwo_eq_upperUnipotent hq hP
  exact ⟨α, hα, by rw [hp] at hker; exact hker, hU⟩

private theorem s48e_card_galoisField (C : X.Comm48 s r d) :
    Nat.card (GaloisField 2 (X.n 0)) = 2 ^ X.n 0 :=
  GaloisField.card 2 (X.n 0) (by have := C.hyp.two_le_n 0; omega)

private theorem s48e_Z_four_le_S (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 4 ≤ X.S := by
  obtain ⟨-, h41, -, -, -, -, -, -, -⟩ := s48e_Z_four C hH
  have hQ : X.Q 1 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow (i := 0)
  exact h41.trans hQ

private theorem s48e_Z_four_le_L_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 4 ≤ X.L 0 := by
  obtain ⟨-, -, -, h40, -, -, -, hZ4card, -⟩ := s48e_Z_four C hH
  have hp : IsPGroup 2 (X.Z 4) := IsPGroup.of_card (n := X.n 0) (by rw [hZ4card])
  exact le_oTwoPrime_of_isPGroup hp h40

private theorem s48e_Z_four_le_normalizer_PQ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 4 ≤ Subgroup.normalizer (X.PQ : Set G) := by
  obtain ⟨-, -, -, h40, hG1, -, -, -, -⟩ := s48e_Z_four C hH
  exact (le_inf h40 hG1).trans X.inf_Gi_le_normalizer_inf_Q

private theorem s48e_Z_four_inf_Z_one (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 4 ⊓ X.Z 1 = ⊥ := by
  obtain ⟨-, hV0card, hV0elem, -, -, -, -⟩ := X.s48_8 C hH
  obtain ⟨-, -, -, hZ1card, -, -⟩ := X.s48_4' C hH
  obtain ⟨hV2eq, -, -⟩ := X.s48_13 C hH
  obtain ⟨-, -, -, -, -, -, -, hZ4card, -⟩ := s48e_Z_four C hH
  have hconjV0 : conjSub (X.τ ^ (1 : ℤ)) (X.Vk 0) = X.Vk 2 := by
    simpa using (X.Vk_add 1 0).symm
  have hV2card : Nat.card (X.Vk 2) = 2 ^ (3 * X.n 0) := by
    rw [← hconjV0]
    exact (Subgroup.card_map_of_injective (MulAut.conj (X.τ ^ (1 : ℤ))).injective).trans hV0card
  have hV2elem : IsElemAbelian 2 (X.Vk 2) := by
    rw [← hconjV0]
    exact CFSG.Quasithin.F7.isElemAbelian_conjSub hV0elem
  have hZ1leV2 : X.Z 1 ≤ X.Vk 2 := hV2eq ▸ le_sup_left
  have hZ4leV2 : X.Z 4 ≤ X.Vk 2 := hV2eq ▸ le_sup_right
  have hZ4normZ1 : X.Z 4 ≤ Subgroup.normalizer (X.Z 1 : Set G) := fun z hz =>
    Subgroup.centralizer_le_normalizer _ <| Subgroup.mem_centralizer_iff.mpr fun c hc =>
      (hV2elem.comm (hZ4leV2 hz) (hZ1leV2 hc)).symm
  have hprod := CFSG.Quasithin.HSType.card_sup_mul_card_inf_of_le_normalizer
    (X := X.Z 4) (N := X.Z 1) hZ4normZ1
  have hsup : X.Z 4 ⊔ X.Z 1 = X.Vk 2 := by rw [hV2eq, sup_comm]
  rw [hsup, hV2card, hZ4card, hZ1card] at hprod
  have hpow : 2 ^ X.n 0 * 2 ^ (2 * X.n 0) = 2 ^ (3 * X.n 0) := by
    rw [← pow_add]
    congr 1
    ring
  rw [hpow] at hprod
  have hc : Nat.card ↥(X.Z 4 ⊓ X.Z 1) = 1 :=
    Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (n := 3 * X.n 0) (by norm_num : 0 < 2))
      (by simpa using hprod)
  exact (Subgroup.eq_bot_iff_card (H := X.Z 4 ⊓ X.Z 1)).mpr hc

private theorem s48e_Z_four_inf_Q_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 4 ⊓ X.Q 0 = ⊥ := by
  obtain ⟨hV2eq, hV2inf, -⟩ := X.s48_13 C hH
  have hZ1Z4 : X.Z 1 ⊓ X.Z 4 = ⊥ := by
    rw [inf_comm]
    exact s48e_Z_four_inf_Z_one C hH
  refine le_bot_iff.mp ?_
  calc X.Z 4 ⊓ X.Q 0 ≤ X.Z 1 ⊓ X.Z 4 := by
        refine le_inf ?_ inf_le_left
        calc X.Z 4 ⊓ X.Q 0 ≤ X.Vk 2 ⊓ X.Q 0 :=
              inf_le_inf_right _ (hV2eq ▸ le_sup_right)
          _ = X.Z 1 := hV2inf
    _ = ⊥ := hZ1Z4

private theorem s48e_relIndex_Vk_zero_PQ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : (X.Vk 0).relIndex X.PQ = 2 ^ X.n 0 := by
  obtain ⟨-, hV0card, -, hV0le, -, -, -⟩ := X.s48_8 C hH
  obtain ⟨hPcard, -⟩ := PQ_card_eq_and_sup_card_eq C hH
  have h := Subgroup.relIndex_mul_card (H := X.Vk 0) (K := X.PQ)
  rw [inf_eq_left.mpr hV0le, hV0card, hPcard] at h
  have hpow : 2 ^ (4 * X.n 0) = 2 ^ X.n 0 * 2 ^ (3 * X.n 0) := by
    rw [← pow_add]
    congr 1
    ring
  rw [hpow] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (n := 3 * X.n 0) (by norm_num : 0 < 2)) h

private theorem s48e_isNatSecOf_Q_zero_Vk_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    {α : ↥(X.L 0) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 0))}
    (hα : Function.Surjective α) (hker : α.ker = (X.Q 0).subgroupOf (X.L 0))
    (hF : Nat.card (GaloisField 2 (X.n 0)) = 2 ^ X.n 0) :
    CFSG.Quasithin.F112R.St84.IsNatSecOf (X.L 0) (X.Q 0) (X.Vk 0) α := by
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI : Fintype (GaloisField 2 (X.n 0)) := Fintype.ofFinite _
  have hF' : Fintype.card (GaloisField 2 (X.n 0)) = 2 ^ X.n 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF
  have hp : pCoreOf 2 (X.L 0) = X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hker' : α.ker = (pCoreOf 2 (X.L 0)).subgroupOf (X.L 0) := by
    rw [hp]
    exact hker
  have hT : IsSylowTwoOf X.S (X.L 0) := by
    simpa [X.edgeSylow_zero] using X.isSylowTwoOf_edgeSylow_L 0
  have hline := (natQuot_Q_zero_Vk_zero C hH).line X.S hT
  exact NatPre.isNatSecOf (C.hyp.two_le_n 0) hF' hα hker' (natPre_Q_zero_Vk_zero C hH)
    (X.Q_le_Gi 0) hT (le_of_eq hline.symm)

private theorem s48e_isNatSecOf_Vk_zero_Z_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    {α : ↥(X.L 0) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 0))}
    (hα : Function.Surjective α) (hker : α.ker = (X.Q 0).subgroupOf (X.L 0))
    (hF : Nat.card (GaloisField 2 (X.n 0)) = 2 ^ X.n 0) :
    CFSG.Quasithin.F112R.St84.IsNatSecOf (X.L 0) (X.Vk 0) (X.Z 0) α := by
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI : Fintype (GaloisField 2 (X.n 0)) := Fintype.ofFinite _
  have hF' : Fintype.card (GaloisField 2 (X.n 0)) = 2 ^ X.n 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF
  obtain ⟨-, -, -, hV0le, -, hnatV0, -⟩ := X.s48_8 C hH
  have hp : pCoreOf 2 (X.L 0) = X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hker' : α.ker = (pCoreOf 2 (X.L 0)).subgroupOf (X.L 0) := by
    rw [hp]
    exact hker
  have hT : IsSylowTwoOf X.S (X.L 0) := by
    simpa [X.edgeSylow_zero] using X.isSylowTwoOf_edgeSylow_L 0
  have hline := hnatV0.line X.S hT
  exact NatPre.isNatSecOf (C.hyp.two_le_n 0) hF' hα hker' (natPre_Vk_zero_Z_zero C hH)
    (hV0le.trans (inf_le_left.trans (X.Q_le_Gi 0))) hT (le_of_eq hline.symm)

private theorem s48e_torus_diag (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    {α : ↥(X.L 0) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 0))}
    (hker : α.ker = (X.Q 0).subgroupOf (X.L 0))
    (hU : (X.S.subgroupOf (X.L 0)).map α =
      CFSG.Timmesfeld.upperUnipotent (GaloisField 2 (X.n 0)))
    (hF : Nat.card (GaloisField 2 (X.n 0)) = 2 ^ X.n 0) :
    ∀ c : GaloisField 2 (X.n 0), c ≠ 0 → ∃ k : ↥(X.L 0), (k : G) ∈ X.Ki 0 ∧
      (α k : Matrix (Fin 2) (Fin 2) (GaloisField 2 (X.n 0))) 0 0 = c ∧
      (α k : Matrix (Fin 2) (Fin 2) (GaloisField 2 (X.n 0))) 1 0 = 0 := by
  haveI : Fintype (GaloisField 2 (X.n 0)) := Fintype.ofFinite _
  have hF' : Fintype.card (GaloisField 2 (X.n 0)) = 2 ^ X.n 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF
  haveI : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  have hTQ : X.Ki 0 ⊓ X.Q 0 = ⊥ := by
    refine le_bot_iff.mp ?_
    calc X.Ki 0 ⊓ X.Q 0 ≤ X.K ⊓ X.Q 0 := inf_le_inf inf_le_left le_rfl
      _ = ⊥ := X.K_inf_Q_eq_bot 0
  have hS : ((X.edgeSylow 0).subgroupOf (X.L 0)).map α =
      CFSG.Timmesfeld.upperUnipotent (GaloisField 2 (X.n 0)) := by
    rw [X.edgeSylow_zero]
    exact hU
  have hTS : X.Ki 0 ≤ Subgroup.normalizer (X.edgeSylow 0 : Set G) :=
    (inf_le_left : X.Ki 0 ≤ X.K).trans
      (X.K_le_inf.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0 ⊓ X.Gi 1)))
  exact CFSG.Quasithin.St84.exists_mem_upper_diag_eq
    (L := X.L 0) (Q := X.Q 0) (T := X.Ki 0) (S := X.edgeSylow 0) hF' hker
    (inf_le_right : X.Ki 0 ≤ X.L 0) (X.edgeSylow_le_L 0) hTQ (X.card_Ki 0) hS hTS

private theorem s48e_torus (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    {α : ↥(X.L 0) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 0))}
    (hker : α.ker = (X.Q 0).subgroupOf (X.L 0))
    (hU : (X.S.subgroupOf (X.L 0)).map α =
      CFSG.Timmesfeld.upperUnipotent (GaloisField 2 (X.n 0)))
    (hF : Nat.card (GaloisField 2 (X.n 0)) = 2 ^ X.n 0) :
    ∀ c : GaloisField 2 (X.n 0), c ≠ 0 → ∃ k : ↥(X.L 0),
      (k : G) ∈ Subgroup.normalizer (X.Z 4 : Set G) ∧
      (k : G) ∈ Subgroup.normalizer (X.PQ : Set G) ∧
      (α k : Matrix (Fin 2) (Fin 2) (GaloisField 2 (X.n 0))) 0 0 = c ∧
      (α k : Matrix (Fin 2) (Fin 2) (GaloisField 2 (X.n 0))) 1 0 = 0 := by
  intro c hc
  obtain ⟨k, hkKi, hdiag, hlow⟩ := s48e_torus_diag C hH hker hU hF c hc
  exact ⟨k, mem_normalizer_iff_conjSub.mpr (X.Z_normal 4 k (X.K_le_Gi 4 hkKi.1)),
    K_le_normalizer_PQ hkKi.1, hdiag, hlow⟩

private theorem s48e_exists_mul_commutator_mem_Z_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    {α : ↥(X.L 0) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 0))}
    (hα : Function.Surjective α) (hker : α.ker = (X.Q 0).subgroupOf (X.L 0))
    (hU : (X.S.subgroupOf (X.L 0)).map α =
      CFSG.Timmesfeld.upperUnipotent (GaloisField 2 (X.n 0)))
    (hF : Nat.card (GaloisField 2 (X.n 0)) = 2 ^ X.n 0) :
    ∀ x ∈ X.PQ, ∃ v ∈ X.Vk 0, ∀ a ∈ X.Z 4, ⁅x * v, a⁆ ∈ X.Z 0 := by
  haveI : Fintype (GaloisField 2 (X.n 0)) := Fintype.ofFinite _
  have hF' : Fintype.card (GaloisField 2 (X.n 0)) = 2 ^ X.n 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF
  obtain ⟨-, hV0card, -, hV0le, -, -, -⟩ := X.s48_8 C hH
  obtain ⟨-, h41, -, -, -, -, -, hZ4card, -⟩ := s48e_Z_four C hH
  have hAU : ((X.Z 4).subgroupOf (X.L 0)).map α ≤
      CFSG.Timmesfeld.upperUnipotent (GaloisField 2 (X.n 0)) := by
    rw [← hU]
    exact Subgroup.map_mono (f := α) (Subgroup.subgroupOf_mono (X.L 0) (s48e_Z_four_le_S C hH))
  exact CFSG.Quasithin.St84.exists_mul_commutator_mem_of_isNatSecOf
    (L := X.L 0) (Q := X.Q 0) (V := X.Vk 0) (Z := X.Z 0) (P := X.PQ) (A := X.Z 4)
    (n := X.n 0) (C.hyp.two_le_n 0) hF' (X.Q_le_L 0) hker
    (s48e_isNatSecOf_Q_zero_Vk_zero C hH hα hker hF)
    (s48e_isNatSecOf_Vk_zero_Z_zero C hH hα hker hF)
    hV0le inf_le_left (s48e_relIndex_Vk_zero_PQ C hH)
    (s48e_Z_four_le_L_zero C hH) (s48e_Z_four_inf_Q_zero C hH) hZ4card hAU
    (s48e_Z_four_le_normalizer_PQ C hH) (commutator_Q_zero_le_Z_zero C hH)
    (s48e_torus C hH hker hU hF)

private theorem s48e_PQ_le_YQ_sup_Vk_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hcomm : ∀ x ∈ X.PQ, ∃ v ∈ X.Vk 0, ∀ a ∈ X.Z 4, ⁅x * v, a⁆ ∈ X.Z 0) :
    X.PQ ≤ X.YQ ⊔ X.Vk 0 := by
  obtain ⟨-, -, -, hV0le, -, -, -⟩ := X.s48_8 C hH
  intro x hx
  obtain ⟨v, hv, hva⟩ := hcomm x hx
  have hxvP : x * v ∈ X.PQ := X.PQ.mul_mem hx (hV0le hv)
  have hxvY : x * v ∈ X.YQ :=
    (mem_relCent (PQ_le_normalizer_Z_zero (X := X))).mpr ⟨hxvP, hva⟩
  have hx' : (x * v) * v⁻¹ = x := by group
  rw [← hx']
  exact (X.YQ ⊔ X.Vk 0).mul_mem (Subgroup.mem_sup_left hxvY)
    (Subgroup.mem_sup_right ((X.Vk 0).inv_mem hv))

private theorem s48e_relIndex_YQ_PQ_le (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hPle : X.PQ ≤ X.YQ ⊔ X.Vk 0) : X.YQ.relIndex X.PQ ≤ 2 ^ X.n 0 := by
  obtain ⟨-, hV0card, -, hV0le, -, -, -⟩ := X.s48_8 C hH
  obtain ⟨-, -, -, hZ1card, -, -⟩ := X.s48_4' C hH
  have he1 := YQ_inf_Vk_zero_eq_Z_one C hH
  have hV0normY : X.Vk 0 ≤ Subgroup.normalizer (X.YQ : Set G) :=
    hV0le.trans (PQ_le_normalizer_YQ C hH)
  have hrelsup : X.YQ.relIndex (X.Vk 0 ⊔ X.YQ) = X.YQ.relIndex (X.Vk 0) :=
    CFSG.Quasithin.B2F.relIndex_sup_eq_of_le_normalizer' hV0normY
  have hrelV : X.YQ.relIndex (X.Vk 0) = 2 ^ X.n 0 := by
    have h := Subgroup.relIndex_mul_card (H := X.YQ) (K := X.Vk 0)
    rw [he1, hZ1card, hV0card] at h
    have hpow : 2 ^ (3 * X.n 0) = 2 ^ X.n 0 * 2 ^ (2 * X.n 0) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_right
      (Nat.pow_pos (n := 2 * X.n 0) (by norm_num : 0 < 2)) h
  have hne : X.YQ.relIndex (X.YQ ⊔ X.Vk 0) ≠ 0 := by
    rw [sup_comm, hrelsup, hrelV]
    exact pow_ne_zero _ (by norm_num)
  have hle := Subgroup.relIndex_le_of_le_right
    (H := X.YQ) (K := X.PQ) (L := X.YQ ⊔ X.Vk 0) hPle hne
  rw [sup_comm, hrelsup, hrelV] at hle
  exact hle

theorem relIndex_relCent_le (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    (relCent (X.Q 0 ⊓ X.Q 1) (X.Z 0) (X.Z 4)).relIndex (X.Q 0 ⊓ X.Q 1) ≤ 2 ^ X.n 0 := by
  obtain ⟨α, hα, hker, hU⟩ := s48e_exists_alpha (X := X)
  have hcomm := s48e_exists_mul_commutator_mem_Z_zero C hH hα hker hU (s48e_card_galoisField C)
  exact s48e_relIndex_YQ_PQ_le C hH (s48e_PQ_le_YQ_sup_Vk_zero C hH hcomm)

theorem false_of_le (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : False :=
  C.false_of_le_of_relIndex hH (C.relIndex_relCent_le hH)

end Comm48

variable (X) in
theorem comm48_u4q (C : X.Comm48 s r d) :
    X.n 1 = 2 * X.n 0 ∧
      CFSG.Quasithin.F112R.St84.U4qLocalData (X.L 0) (X.L 1) X.S (X.n 0) := by
  by_cases hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)
  · exact (C.false_of_le hH).elim
  · rcases X.s48_3d C hH with h1 | h3
    · exact C.u4qLocalData_of_eq_one h1
    · exact absurd h3 (X.s48_3e C hH)

theorem Comm48.false (C : X.Comm48 s r d) (hn : X.n 0 = X.n 1) : False := by
  have h := (X.comm48_u4q C).1
  have h2 := C.hyp.two_le_n 0
  omega

end Setup

end CFSG.Quasithin.St84

end
