module

public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteenSetup
public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteenCentral
public import CFSG.LocalAnalysis.WeakClosure81.ThreeTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def centerMod (K I : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ K ∧ z ∈ Subgroup.normalizer (I : Set G) ∧ ∀ k ∈ K, ⁅z, k⁆ ∈ I}
  one_mem' := by
    refine ⟨K.one_mem, (Subgroup.normalizer (I : Set G)).one_mem, fun k _ => ?_⟩
    rw [commutatorElement_def]
    simpa using I.one_mem
  mul_mem' := by
    rintro a b ⟨haK, haN, ha⟩ ⟨hbK, hbN, hb⟩
    refine ⟨K.mul_mem haK hbK, (Subgroup.normalizer (I : Set G)).mul_mem haN hbN, fun k hk => ?_⟩
    have h1 : a * ⁅b, k⁆ * a⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.mp haN _).mp (hb k hk)
    have h2 : ⁅a * b, k⁆ = (a * ⁅b, k⁆ * a⁻¹) * ⁅a, k⁆ := by
      simp only [commutatorElement_def]; group
    rw [h2]
    exact I.mul_mem h1 (ha k hk)
  inv_mem' := by
    rintro a ⟨haK, haN, ha⟩
    refine ⟨K.inv_mem haK, (Subgroup.normalizer (I : Set G)).inv_mem haN, fun k hk => ?_⟩
    have hka : ⁅k, a⁆ ∈ I := by
      rw [← commutatorElement_inv]
      exact I.inv_mem (ha k hk)
    have h1 : a⁻¹ * ⁅k, a⁆ * a⁻¹⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (I : Set G)).inv_mem haN) _).mp hka
    have h2 : ⁅a⁻¹, k⁆ = a⁻¹ * ⁅k, a⁆ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h2]
    exact h1

omit [Finite G] in
theorem mem_centerMod_iff {K I : Subgroup G} {z : G} :
    z ∈ centerMod K I ↔ z ∈ K ∧ z ∈ Subgroup.normalizer (I : Set G) ∧ ∀ k ∈ K, ⁅z, k⁆ ∈ I :=
  Iff.rfl

private theorem mem_normalizer_of_conj_le_aux {A : Subgroup G} {b : G}
    (h : ∀ a ∈ A, b⁻¹ * a * b ∈ A) : b ∈ Subgroup.normalizer (A : Set G) := by
  have hle : A.map (MulAut.conj b⁻¹).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using h a ha
  have hcard : Nat.card A ≤ Nat.card (A.map (MulAut.conj b⁻¹).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj b⁻¹).injective]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hy' : y ∈ A.map (MulAut.conj b⁻¹).toMonoidHom := by rw [heq]; exact hy
    obtain ⟨a, ha, hay⟩ := hy'
    have : b * y * b⁻¹ = a := by
      rw [← hay]; simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      group
    rw [this]; exact ha
  · intro hy
    have := h _ hy
    simpa [mul_assoc] using this

theorem exists_complement_normalized_by_involution {V H E Q : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hVΩ : V ∈ omegaSet V H E)
    (hQK : Q ≤ kSub V H E) (hIQ : iSub V H E ≤ Q)
    (hQnorm : (Q.subgroupOf (kSub V H E)).Normal)
    (hindex : (V ⊓ iSub V H E).relIndex V = 2) (hodd : Odd ((iSub V H E).relIndex Q))
    [((iSub V H E).subgroupOf Q).Normal]
    (hnil : Group.IsNilpotent (↥Q ⧸ (iSub V H E).subgroupOf Q))
    {v : G} (hv : v ∈ V) (hvI : v ∉ iSub V H E) :
    ∃ P : Subgroup G, P ≤ Q ∧ P ⊓ iSub V H E = ⊥ ∧ P ⊔ iSub V H E = Q ∧
      v ∈ Subgroup.normalizer (P : Set G) := by
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le hOmH
  have hQH : Q ≤ H := hQK.trans hKH
  have hIO : iSub V H E ≤ pCoreOf 2 H := iSup₂_le fun U _ => inf_le_right
  have hIH : iSub V H E ≤ H := hIO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hHI : H ≤ normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIH (iSub_subgroupOf_normal hEH hEnorm)
  have hKQ : kSub V H E ≤ normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mp hQnorm
  have hVK : V ≤ kSub V H E := le_kSub hVΩ
  have hIe : IsElemAbelian 2 (iSub V H E) := seven_two_iSub_isElemAbelian_uncond hV hTI hE hOmH
  have hvv : v * v = 1 := elemAbelian_mul_self hV hv
  have hvN : v ∈ normalizer (iSub V H E : Set G) := hHI (hKH (hVK hv))
  have hVv : V ≤ zpowers v ⊔ iSub V H E :=
    (le_zpowers_sup_of_relIndex_eq_two inf_le_left hindex hv (fun h => hvI h.2)).trans
      (sup_le_sup_left inf_le_right _)
  have hN := nVSub_eq_inf_iSub_of_relIndex_eq_two hV hTI hE hEH hEnorm hOmH hindex
  refine exists_complement_normalized_of_involution hIQ hIe.isPGroup hodd hnil hvv (hKQ (hVK hv)) ?_
  intro x hxQ hxi
  have hxH : x ∈ H := hQH hxQ
  have hxI : x ∈ normalizer (iSub V H E : Set G) := hHI hxH
  have hxN : x ∈ normalizer ((V ⊔ iSub V H E : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_le_aux
    intro t ht
    have hiv : x⁻¹ * v * x = (x⁻¹ * (v * x * v⁻¹)) * v := by group
    have hIV : iSub V H E ≤ V ⊔ iSub V H E := le_sup_right
    have hmem : x⁻¹ * v * x ∈ V ⊔ iSub V H E := by
      rw [hiv]
      exact Subgroup.mul_mem _ (hIV hxi) (le_sup_left (a := V) hv)
    have ht' : t ∈ zpowers v ⊔ iSub V H E := sup_le hVv le_sup_right ht
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right (zpowers v) (iSub V H E)
      (zpowers_le.mpr hvN)] at ht'
    obtain ⟨w, hw, i', hi', rfl⟩ := ht'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
    have h1 : x⁻¹ * (v ^ n * i') * x = (x⁻¹ * v * x) ^ n * (x⁻¹ * i' * x) := by
      rw [show (x⁻¹ * v * x) ^ n = x⁻¹ * v ^ n * x by
        simpa using (conj_zpow (a := x⁻¹) (b := v) (i := n))]
      group
    rw [h1]
    have hxinv : x⁻¹ ∈ normalizer (iSub V H E : Set G) :=
      (normalizer (iSub V H E : Set G)).inv_mem hxI
    refine Subgroup.mul_mem _ (Subgroup.zpow_mem _ hmem n) (hIV ?_)
    simpa using (Subgroup.mem_normalizer_iff.mp hxinv i').mp hi'
  obtain ⟨m, hmm, j, hjI, hxmj⟩ := seven_three_four_normalizer hV hTI hE hEH hEnorm hVΩ hOmH hIO
    (iSub_subgroupOf_normal hEH hEnorm) le_rfl hxH hxN
  rw [Subgroup.mem_inf] at hmm
  obtain ⟨hmH, hmV⟩ := hmm
  have hmQ : m ∈ Q := by
    have : m = x * j⁻¹ := by rw [hxmj]; group
    rw [this]; exact Q.mul_mem hxQ (Q.inv_mem (hIQ hjI))
  have hcV : m⁻¹ * v * m ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (V : Set G)).inv_mem hmV) v).mp hv
    simpa using this
  have hcI : m⁻¹ * v * m ∉ iSub V H E := by
    intro h
    apply hvI
    have := (Subgroup.mem_normalizer_iff.mp (hHI hmH) _).mp h
    simpa [mul_assoc] using this
  have hw : v⁻¹ * (m⁻¹ * v * m) ∈ V ⊓ iSub V H E :=
    inv_mul_mem_of_relIndex_eq_two (A := V ⊓ iSub V H E) (B := V) hindex hv hcV
      (fun h => hvI h.2) (fun h => hcI h.2)
  obtain ⟨a, haI, hac⟩ := exists_commutator_eq_of_mem_inf_iSub hV hTI hEH hEnorm hOmH hVΩ hN hv hvI
    _ hw
  refine ⟨m * a, Q.mul_mem hmQ (hIQ haI), ?_, ?_⟩
  ·
    have hav : a * v * a⁻¹ = m⁻¹ * v * m := by
      have h1 : a * v * a⁻¹ * v⁻¹ = v⁻¹ * (m⁻¹ * v * m) := hac
      have h2 : v⁻¹ * (m⁻¹ * v * m) = (m⁻¹ * v * m) * v⁻¹ := by
        have := hV.comm ((inv_mem hv : v⁻¹ ∈ V)) hcV
        exact this
      calc a * v * a⁻¹ = (a * v * a⁻¹ * v⁻¹) * v := by group
        _ = ((m⁻¹ * v * m) * v⁻¹) * v := by rw [h1, h2]
        _ = m⁻¹ * v * m := by group
    calc v * (m * a) = (m * a) * (a⁻¹ * (m⁻¹ * v * m) * a) := by group
      _ = (m * a) * v := by
          congr 1
          rw [← hav]; group
  · have : x⁻¹ * (m * a) = j⁻¹ * a := by rw [hxmj]; group
    rw [this]
    exact (iSub V H E).mul_mem ((iSub V H E).inv_mem hjI) haI

theorem seven_fifteen {V H E Q : Subgroup G} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hVΩ : V ∈ omegaSet V H E)
    (hQK : Q ≤ kSub V H E) (hIQ : iSub V H E ≤ Q)
    (hQnorm : (Q.subgroupOf (kSub V H E)).Normal) (hKQV : kSub V H E = Q ⊔ V)
    [((iSub V H E).subgroupOf Q).Normal]
    [CFSG.IsExtraspecial p (↥Q ⧸ (iSub V H E).subgroupOf Q)]
    (hcard : Nat.card (↥Q ⧸ (iSub V H E).subgroupOf Q) = p ^ 3)
    (hexp : Monoid.exponent (↥Q ⧸ (iSub V H E).subgroupOf Q) = p) :
    ∃ k : ℕ, Nat.card ↥(iSub V H E) = 2 ^ (p * k) ∧
      Nat.card ↥(iSub V H E ⊓ Subgroup.centralizer (V : Set G)) = 2 ^ ((p + 1) * k / 2) ∧
      Nat.card ↥(V ⊓ iSub V H E) = 2 ^ ((p - 1) * k / 2) ∧
      ⁅iSub V H E, centerMod (kSub V H E) (iSub V H E)⁆ = iSub V H E := by
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le hOmH
  have hQH : Q ≤ H := hQK.trans hKH
  have hIO : iSub V H E ≤ pCoreOf 2 H := iSup₂_le fun U _ => inf_le_right
  have hIH : iSub V H E ≤ H := hIO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hHI : H ≤ normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIH (iSub_subgroupOf_normal hEH hEnorm)
  have hKQ : kSub V H E ≤ normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mp hQnorm
  have hVK : V ≤ kSub V H E := le_kSub hVΩ
  have hIe : IsElemAbelian 2 (iSub V H E) := seven_two_iSub_isElemAbelian_uncond hV hTI hE hOmH
  have hrel : (iSub V H E).relIndex Q = p ^ 3 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]; exact hcard
  have hp' : Odd p := Nat.Prime.odd_of_ne_two Fact.out hp
  have hodd : Odd ((iSub V H E).relIndex Q) := hrel ▸ hp'.pow
  have hQI : ¬ Q ≤ iSub V H E := by
    intro h
    have h1 := Subgroup.relIndex_eq_one.mpr h
    rw [hrel] at h1
    have := (Nat.Prime.one_lt (Fact.out : p.Prime))
    have h2 : p ^ 3 ≠ 1 := by
      intro h3
      have : p = 1 := by simpa using h3
      omega
    exact h2 h1
  have hnil : Group.IsNilpotent (↥Q ⧸ (iSub V H E).subgroupOf Q) :=
    (IsPGroup.of_card hcard).isNilpotent
  have hindex : (V ⊓ iSub V H E).relIndex V = 2 :=
    relIndex_inf_iSub_eq_two hV hTI hE hEH hEnorm hOmH hVΩ hQK hIQ hQnorm hKQV hodd hQI
  have hU2 : ∀ U ∈ omegaSet V H E, (U ⊓ iSub V H E).relIndex U = 2 := fun U hU =>
    relIndex_inf_iSub_eq_two_of_mem_omegaSet hV hEH hEnorm hOmH hQK hIQ hQnorm hKQV hodd hindex hU
  have hgenQ : Q ≤ iSub V H E ⊔ ⁅Q, V⁆ :=
    le_iSub_sup_commutator hV hEH hEnorm hOmH hQK hIQ hQnorm hKQV hodd
  have hIK : iSub V H E ≤ ⁅iSub V H E, kSub V H E⁆ :=
    iSub_le_commutator_kSub hV hTI hE hEH hEnorm hOmH hU2
  have hVnI : ¬ V ≤ iSub V H E := by
    intro h
    obtain ⟨g, -, -, hnot⟩ := mem_omegaSet.mp hVΩ
    exact hnot (h.trans hIO)
  obtain ⟨v, hvV, hvI⟩ := Set.not_subset.mp hVnI
  have hv : v * v = 1 := elemAbelian_mul_self hV hvV
  have hVv : V ≤ zpowers v ⊔ iSub V H E :=
    (le_zpowers_sup_of_relIndex_eq_two inf_le_left hindex hvV (fun h => hvI h.2)).trans
      (sup_le_sup_left inf_le_right _)
  obtain ⟨P, hPQ, hPI, hPIQ, hvP⟩ := exists_complement_normalized_by_involution hV hTI hE hEH
    hEnorm hOmH hVΩ hQK hIQ hQnorm hindex hodd hnil hvV hvI
  haveI hext : CFSG.IsExtraspecial p ↥P := isExtraspecial_of_complement hPQ hPI hPIQ
  have hPcard : Nat.card ↥P = p ^ 3 := (nat_card_eq_of_complement hPQ hPI hPIQ).trans hcard
  have hPexp : Monoid.exponent ↥P = p := (exponent_eq_of_complement hPQ hPI hPIQ).trans hexp
  have hvN : v ∈ normalizer (iSub V H E : Set G) := hHI (hKH (hVK hvV))
  have hPv : ⁅P, zpowers v⁆ = P :=
    commutator_zpowers_eq_of_complement (hQH.trans hHI) hvN hPI hPIQ hvP hVv hgenQ
  obtain ⟨x, z, g, cfg⟩ := exists_heisConfig hp hPcard hPexp hv hvP hPv
  have hPH : P ≤ H := hPQ.trans hQH
  have hPN : P ≤ normalizer (iSub V H E : Set G) := hPH.trans hHI
  have hP : IsPGroup p ↥P := IsPGroup.of_card hPcard
  have hKle : kSub V H E ≤ iSub V H E ⊔ P ⊔ zpowers v := by
    rw [hKQV, ← hPIQ]
    exact sup_le (sup_le (le_sup_of_le_left le_sup_right) (le_sup_of_le_left le_sup_left))
      (hVv.trans (sup_le le_sup_right (le_sup_of_le_left le_sup_left)))
  have hIgen : iSub V H E ≤ ⁅iSub V H E, iSub V H E ⊔ P ⊔ zpowers v⁆ :=
    hIK.trans (Subgroup.commutator_mono le_rfl hKle)
  have hT : ∀ y ∈ normalizer (iSub V H E : Set G), ∀ w ∈ ⁅iSub V H E, zpowers v⁆, w ≠ 1 →
      y ∈ centralizer ({w} : Set G) → ⁅v, y⁆ ∈ iSub V H E := fun y hy w hw hw1 hyw =>
    commutator_mem_iSub_of_mem_centralizer hV hTI hE hEH hEnorm hOmH hVΩ hindex hvV hvI hy hw hw1
      hyw
  have hCz : iSub V H E ⊓ centralizer ({z} : Set G) = ⊥ :=
    inf_centralizer_eq_bot hp hIe hP hPN hvN hv hvP cfg hPI hPv hIgen hT
  have hCx : iSub V H E ⊓ centralizer ({x} : Set G) ≤ centralizer ({v} : Set G) :=
    inf_centralizer_le_centralizer_involution hPN hvN hvP cfg hPI hT
  obtain ⟨k, hk1, hk2, hk3⟩ := exists_card_eq_pow_of_inverting_involution hp hIe
    (hPN cfg.x_mem) (hPN cfg.z_mem) (hPN cfg.g_mem) hvN cfg.x_pow cfg.z_pow
    (cfg.z_central x cfg.x_mem) cfg.g_conj_x (cfg.z_central g cfg.g_mem) cfg.v_conj_x
    cfg.v_comm_z hv hCz hCx
  have hCV : iSub V H E ⊓ centralizer (V : Set G) = iSub V H E ⊓ centralizer ({v} : Set G) := by
    refine le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le (by simpa using hvV))) ?_
    intro a ha
    rw [Subgroup.mem_inf] at ha ⊢
    obtain ⟨haI, hav⟩ := ha
    refine ⟨haI, ?_⟩
    have hC : zpowers v ⊔ iSub V H E ≤ centralizer ({a} : Set G) := by
      refine sup_le ?_ ?_
      · rw [zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hav).symm
      · intro i hi
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hIe.comm hi haI
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hC (hVv hw))
  have hN := nVSub_eq_inf_iSub_of_relIndex_eq_two hV hTI hE hEH hEnorm hOmH hindex
  have hcomm : ⁅iSub V H E, zpowers v⁆ = V ⊓ iSub V H E :=
    commutator_iSub_eq_inf_iSub hV hTI hE hEH hEnorm hOmH hVΩ hN hvV hvI
  refine ⟨k, hk1, ?_, ?_, ?_⟩
  · rw [hCV]; exact hk2
  · rw [← hcomm]; exact hk3
  · have hzK : z ∈ centerMod (kSub V H E) (iSub V H E) := by
      refine ⟨hQK (hPQ cfg.z_mem), hPN cfg.z_mem, fun k hk => ?_⟩
      have hS : ∀ s ∈ ((iSub V H E : Set G) ∪ (P : Set G) ∪ {v}),
          s ∈ normalizer (iSub V H E : Set G) ∧ ∀ a ∈ zpowers z, ⁅a, s⁆ ∈ iSub V H E := by
        have hzH : zpowers z ≤ H := zpowers_le.mpr (hPH cfg.z_mem)
        have hcz : ∀ s : G, s * z = z * s → ∀ a ∈ zpowers z, ⁅a, s⁆ ∈ iSub V H E := by
          intro s hs a ha
          have hcs : Commute a s := by
            obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
            exact (show Commute z s from hs.symm).zpow_left n
          rw [commutatorElement_eq_one_iff_commute.mpr hcs]
          exact one_mem _
        rintro s ((hs | hs) | hs)
        · refine ⟨Subgroup.le_normalizer hs, fun a ha => ?_⟩
          have h1 : a * s * a⁻¹ ∈ iSub V H E :=
            (Subgroup.mem_normalizer_iff.mp (hHI (hzH ha)) s).mp hs
          rw [commutatorElement_def]
          exact (iSub V H E).mul_mem h1 ((iSub V H E).inv_mem hs)
        · exact ⟨hPN hs, hcz s (cfg.z_central s hs)⟩
        · rw [Set.mem_singleton_iff] at hs
          subst hs
          exact ⟨hvN, hcz s cfg.v_comm_z⟩
      have hKc : kSub V H E ≤ Subgroup.closure
          ((iSub V H E : Set G) ∪ (P : Set G) ∪ {v}) := by
        rw [hKQV, ← hPIQ]
        refine sup_le (sup_le ?_ ?_) ?_
        · exact fun y hy => Subgroup.subset_closure (Or.inl (Or.inr hy))
        · exact fun y hy => Subgroup.subset_closure (Or.inl (Or.inl hy))
        · refine hVv.trans (sup_le ?_ ?_)
          · rw [zpowers_le]; exact Subgroup.subset_closure (Or.inr rfl)
          · exact fun y hy => Subgroup.subset_closure (Or.inl (Or.inl hy))
      exact commutator_closure_le hS
        (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers z) (hKc hk))
    have hle : ⁅iSub V H E, centerMod (kSub V H E) (iSub V H E)⁆ ≤ iSub V H E := by
      rw [Subgroup.commutator_le]
      intro a ha w hw
      have h1 : ⁅w, a⁆ ∈ iSub V H E := hw.2.2 a (hQK (hIQ ha))
      rw [← commutatorElement_inv]
      exact (iSub V H E).inv_mem h1
    have hge : iSub V H E ≤ ⁅iSub V H E, centerMod (kSub V H E) (iSub V H E)⁆ := by
      rw [Subgroup.commutator_comm]
      have hzN := hPN cfg.z_mem
      let ψ : ↥(iSub V H E) → ↥(iSub V H E) := fun b =>
        ⟨⁅z, (b : G)⁆, by
          rw [commutatorElement_def]
          exact (iSub V H E).mul_mem ((Subgroup.mem_normalizer_iff.mp hzN _).mp b.2)
            ((iSub V H E).inv_mem b.2)⟩
      have hinj : Function.Injective ψ := by
        intro a b hab
        have h : ⁅z, (a : G)⁆ = ⁅z, (b : G)⁆ := congrArg Subtype.val hab
        have hA : z * (a : G) * z⁻¹ ∈ iSub V H E := (Subgroup.mem_normalizer_iff.mp hzN _).mp a.2
        have hB : z * (b : G) * z⁻¹ ∈ iSub V H E := (Subgroup.mem_normalizer_iff.mp hzN _).mp b.2
        have hba : (b : G)⁻¹ * (a : G) ∈ iSub V H E :=
          (iSub V H E).mul_mem ((iSub V H E).inv_mem b.2) a.2
        have hBc : (z * (b : G) * z⁻¹) * ((b : G)⁻¹ * (a : G)) =
            ((b : G)⁻¹ * (a : G)) * (z * (b : G) * z⁻¹) := hIe.comm hB hba
        have hmem : (a : G) * (b : G)⁻¹ ∈ iSub V H E ⊓ centralizer ({z} : Set G) := by
          rw [Subgroup.mem_inf]
          refine ⟨(iSub V H E).mul_mem a.2 ((iSub V H E).inv_mem b.2), ?_⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          have h' : z * (a : G) * z⁻¹ * (a : G)⁻¹ = z * (b : G) * z⁻¹ * (b : G)⁻¹ := h
          have hA' : z * (a : G) * z⁻¹ = (z * (b : G) * z⁻¹) * ((b : G)⁻¹ * (a : G)) := by
            calc z * (a : G) * z⁻¹ = (z * (a : G) * z⁻¹ * (a : G)⁻¹) * (a : G) := by group
              _ = (z * (b : G) * z⁻¹ * (b : G)⁻¹) * (a : G) := by rw [h']
              _ = (z * (b : G) * z⁻¹) * ((b : G)⁻¹ * (a : G)) := by group
          have key : z * ((a : G) * (b : G)⁻¹) * z⁻¹ = (a : G) * (b : G)⁻¹ := by
            calc z * ((a : G) * (b : G)⁻¹) * z⁻¹
                = (z * (a : G) * z⁻¹) * (z * (b : G) * z⁻¹)⁻¹ := by group
              _ = ((z * (b : G) * z⁻¹) * ((b : G)⁻¹ * (a : G))) * (z * (b : G) * z⁻¹)⁻¹ := by
                  rw [hA']
              _ = (((b : G)⁻¹ * (a : G)) * (z * (b : G) * z⁻¹)) * (z * (b : G) * z⁻¹)⁻¹ := by
                  rw [hBc]
              _ = (b : G)⁻¹ * (a : G) := by group
              _ = (a : G) * (b : G)⁻¹ := hIe.comm ((iSub V H E).inv_mem b.2) a.2
          calc (a : G) * (b : G)⁻¹ * z = z * ((a : G) * (b : G)⁻¹) * z⁻¹ * z := by rw [key]
            _ = z * ((a : G) * (b : G)⁻¹) := by group
        rw [hCz, Subgroup.mem_bot] at hmem
        exact Subtype.ext (mul_inv_eq_one.mp hmem)
      have hsurj := Finite.injective_iff_surjective.mp hinj
      intro a ha
      obtain ⟨b, hb⟩ := hsurj ⟨a, ha⟩
      have hba : ⁅z, (b : G)⁆ = a := congrArg Subtype.val hb
      rw [← hba]
      exact Subgroup.commutator_mem_commutator hzK b.2
    exact le_antisymm hle hge

end CFSG.LocalAnalysis.WeakClosure81
