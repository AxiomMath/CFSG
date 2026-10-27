module

public import CFSG.RankThree.PartOne.KFOUT3.KtyLift
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.RankThree.PartOne.S12.Facts13

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.Torsion37
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

omit [Finite G] in
theorem kZero_le_centralizer (p : ℕ) (E : Subgroup G) (t : MulAut E) :
    kZero p E t ≤ Subgroup.centralizer (autFixedInG E t : Set G) := by
  unfold kZero pElementSubgroup
  rw [Subgroup.closure_le]
  intro x hx
  exact Subgroup.map_subtype_le _ hx.1

theorem c_mem_autFixedInG (h : Sec12Hyp G p A c L E) {t : MulAut E} (ht : t ∈ torusImage E L) :
    c ∈ autFixedInG E t := by
  have hcE : c ∈ E := h.A_le_E h.c_mem
  obtain ⟨n, hn, hnt, htn⟩ := Sec12Three.mem_torusImage_iff.mp ht
  refine ⟨⟨c, hcE⟩, ?_, rfl⟩
  show t ⟨c, hcE⟩ = ⟨c, hcE⟩
  rw [← htn]
  apply Subtype.ext
  show n * c * n⁻¹ = c
  rw [← Sec12Three.comm_c_L h n hn, mul_inv_cancel_right]

theorem exists_fixed_gen (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) (hEA : E = A)
    (hF13 : Sec13Facts G p A c L E) {t : MulAut E} (ht : t ∈ reflectionSet p E)
    (htL : t ∈ torusImage E L) :
    ∃ z : G, z ∈ L ∧ z ∈ E ∧ z ≠ 1 ∧ z ^ p = 1 ∧
      autFixedInG E t = Subgroup.zpowers z ⊔ Subgroup.zpowers c := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have R := h.restr_of_generic hG
  have hcL := h.c_not_mem_of_generic hG
  have hc := Sec12Three.orderOf_c h
  obtain ⟨hdec, hdisj, hM⟩ := hF13.reflection t ht
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hcomm_E : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    mul_comm_of_isElementaryAbelian h.E_elem hx hy
  have hHE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hME : autMovedInG E t ≤ E := Subgroup.map_subtype_le _
  have hE3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hHcard : Nat.card (autFixedInG E t) = p ^ 2 := by
    have h1 : Nat.card ↥(autFixedInG E t ⊔ autMovedInG E t) =
        Nat.card (autFixedInG E t) * Nat.card (autMovedInG E t) :=
      card_sup_of_commute_disjoint (fun k hk l hl => hcomm_E k (hHE hk) l (hME hl))
        (disjoint_iff.mpr hdisj)
    rw [← hdec, hE3, hM] at h1
    have h2 : Nat.card (autFixedInG E t) * p = p ^ 2 * p := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  have hcH : c ∈ autFixedInG E t := c_mem_autFixedInG h htL
  set H' : Subgroup G := autFixedInG E t ⊓ (E ⊓ L) with hH'
  have hHeq : autFixedInG E t = H' ⊔ Subgroup.zpowers c := by
    apply le_antisymm
    · intro x hx
      obtain ⟨f, hf, i, rfl⟩ := R.exists_mul_zpow (hHE hx)
      have hci : c ^ i ∈ autFixedInG E t := Subgroup.zpow_mem _ hcH i
      have hfH : f ∈ autFixedInG E t := by
        have := Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hci)
        simpa using this
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hfH, hf⟩)
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) i)
    · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hcH)
  have hH'card : Nat.card H' = p := by
    have hH'L : H' ≤ L := fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).2
    have hdj : Disjoint H' (Subgroup.zpowers c) :=
      (Disjoint.mono_right hH'L
        (disjoint_iff.mpr (Sec12Three.zpowers_inf_eq_bot hp hc hcL))).symm
    have h1 : Nat.card ↥(H' ⊔ Subgroup.zpowers c) = Nat.card H' * Nat.card (Subgroup.zpowers c) :=
      card_sup_of_commute_disjoint (fun k hk l hl => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
        exact (R.commute_zpow (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hk).2).2 i)) hdj
    rw [← hHeq, hHcard, Nat.card_zpowers, hc] at h1
    have h2 : Nat.card H' * p = p * p := by rw [← h1, sq]
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  have hne : ∃ z ∈ H', z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : H' = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hH'card
    exact hp.one_lt.ne hH'card
  obtain ⟨z, hzH', hz1⟩ := hne
  have hzE : z ∈ E := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hzH').2).1
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hzH').2).2
  have hzp : z ^ p = 1 := Sec12Three.pow_eq_one_of_mem_E h hzE
  have hord : orderOf z = p := orderOf_eq_prime hzp hz1
  have hzgen : Subgroup.zpowers z = H' := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzH') ?_
    rw [Nat.card_zpowers, hord, hH'card]
  exact ⟨z, hzL, hzE, hz1, hzp, by rw [hHeq, hzgen]⟩


omit [Finite G] in
theorem pElementSubgroup_eq_of_quasisimple {B : Subgroup G} (hB : IsQuasisimple B) {z : G}
    (hzB : z ∈ B) (hzp : orderOf z = p) (hz : (⟨z, hzB⟩ : B) ∉ Subgroup.center B) :
    pElementSubgroup p B = B := by
  refine le_antisymm ((Subgroup.closure_le B).mpr fun x hx => hx.1) fun b hb => ?_
  set H' : Subgroup B := (pElementSubgroup p B).subgroupOf B with hH'
  set z' : B := ⟨z, hzB⟩ with hz'
  have hle : Subgroup.normalClosure {z'} ≤ H' := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ha, hconj⟩ := hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    rw [Set.mem_singleton_iff] at ha
    subst ha
    have hord : orderOf (g * z' * g⁻¹ : B) = p := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz', Subgroup.orderOf_mk, hzp]
    have hmem : (((g * z' * g⁻¹ : B)) : G) ∈
        {x : G | x ∈ B ∧ ∃ k : ℕ, orderOf x = p ^ k} :=
      ⟨(g * z' * g⁻¹ : B).2, 1, by rw [Subgroup.orderOf_coe, hord, pow_one]⟩
    exact Subgroup.subset_closure hmem
  set M : Subgroup B := Subgroup.normalClosure {z'} with hM
  have : M.Normal := Subgroup.normalClosure_normal
  have : IsSimpleGroup (B ⧸ Subgroup.center B) := hB.2.1
  have hz'M : z' ∈ M := Subgroup.subset_normalClosure rfl
  have hdecomp : ∀ x : B, ∃ m ∈ M, ∃ z₀ ∈ Subgroup.center B, x = m * z₀ := by
    have hnorm : (M.map (QuotientGroup.mk' (Subgroup.center B))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases hnorm.eq_bot_or_eq_top with h0 | h0
    · exfalso
      apply hz
      have : QuotientGroup.mk' (Subgroup.center B) z' ∈
          M.map (QuotientGroup.mk' (Subgroup.center B)) := Subgroup.mem_map_of_mem _ hz'M
      rw [h0, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    · intro x
      have : QuotientGroup.mk' (Subgroup.center B) x ∈
          M.map (QuotientGroup.mk' (Subgroup.center B)) := by rw [h0]; trivial
      obtain ⟨m, hm, hmx⟩ := this
      refine ⟨m, hm, m⁻¹ * x, ?_, by group⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hmx
      exact hmx
  have hMtop : M = ⊤ := by
    rw [eq_top_iff]
    have h1 : Group.IsPerfect B := hB.1
    have h2 : commutator B = ⊤ := h1.commutator_eq_top
    rw [← h2, commutator_def, Subgroup.commutator_le]
    intro g _ h _
    obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := hdecomp g
    obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := hdecomp h
    rw [commutator_mul_central hz₁ hz₂]
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)
  have : (⟨b, hb⟩ : B) ∈ H' := hle (hMtop ▸ Subgroup.mem_top _)
  exact this

theorem subnormal_inf_subgroupOf' (h : Sec12Hyp G p A c L E) {X : Subgroup G}
    (hX : X ≤ Subgroup.centralizer ({c} : Set G)) : ((L ⊓ X).subgroupOf X).IsSubnormal := by
  have hsn := isSubnormal_of_mem_thetaComponentsAt h.L_mem.2
  have h1 := hsn.comap (Subgroup.inclusion hX)
  convert h1 using 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap]
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩

theorem le_kZero_of_quasisimple (h : Sec12Hyp G p A c L E) {t : MulAut E}
    (hct : c ∈ autFixedInG E t) {B : Subgroup G} (hBL : B ≤ L)
    (hBX : B ≤ Subgroup.centralizer (autFixedInG E t : Set G))
    (hBnorm : ∀ y ∈ L ⊓ Subgroup.centralizer (autFixedInG E t : Set G), ∀ b ∈ B,
      y * b * y⁻¹ ∈ B)
    (hBqs : IsQuasisimple B) {z : G} (hzB : z ∈ B) (hzp : orderOf z = p)
    (hz : (⟨z, hzB⟩ : B) ∉ Subgroup.center B) : B ≤ kZero p E t := by
  set X : Subgroup G := Subgroup.centralizer (autFixedInG E t : Set G) with hXdef
  have hXc : X ≤ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mp hx y hct
  have hYsn := subnormal_inf_subgroupOf' h hXc
  set B' : Subgroup X := B.subgroupOf X with hB'
  have hB'qs : IsQuasisimple B' :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBX).symm hBqs
  have hB'sn : B'.IsSubnormal := by
    refine Subgroup.IsSubnormal.step B' ((L ⊓ X).subgroupOf X) (fun b hb => ?_) hYsn ?_
    · rw [Subgroup.mem_subgroupOf] at hb ⊢
      exact Subgroup.mem_inf.mpr ⟨hBL hb, hBX hb⟩
    · refine ⟨fun n hn g => ?_⟩
      have hn' : (((n : (L ⊓ X).subgroupOf X) : X) : G) ∈ B := hn
      have hg : ((((g : (L ⊓ X).subgroupOf X) : X) : G)) ∈ L ⊓ X := g.2
      show ((((g * n * g⁻¹ : (L ⊓ X).subgroupOf X) : X) : G)) ∈ B
      exact hBnorm _ hg _ hn'
  have hle : B' ≤ layer X := le_sSup ⟨hB'qs, hB'sn⟩
  have hin : B ≤ inSubgroup (fun K _ => layer K) X := fun b hb =>
    ⟨⟨b, hBX hb⟩, hle (show (⟨b, hBX hb⟩ : X) ∈ B' from hb), rfl⟩
  calc B = pElementSubgroup p B :=
        (pElementSubgroup_eq_of_quasisimple hBqs hzB hzp hz).symm
    _ ≤ pElementSubgroup p (inSubgroup (fun K _ => layer K) X) :=
        Subgroup.closure_mono fun x hx => ⟨hin hx.1, hx.2⟩
    _ = kZero p E t := rfl


theorem kty_false (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) {Q : Type} [Group Q] {ε : ↥L →* Q}
    (hε : IsCentralPQuot p ε) {t s : MulAut E} (ht : t ∈ reflectionSet p E)
    (htL : t ∈ torusImage E L) (hsL : s ∈ torusImage E L) {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G))
    (heq : conjAut E g hg * t * (conjAut E g hg)⁻¹ = s) {zt zs : ↥L}
    (hzt : autFixedInG E t = Subgroup.zpowers (zt : G) ⊔ Subgroup.zpowers c)
    (hzs : autFixedInG E s = Subgroup.zpowers (zs : G) ⊔ Subgroup.zpowers c) (hzsp : zs ^ p = 1)
    {S : Subgroup Q} (hSperf : Group.IsPerfect S) (hSsimple : IsSimpleGroup S)
    (hSp : ∃ σ ∈ S, orderOf σ = p) (hSc : ∀ σ ∈ S, ε zs * σ = σ * ε zs)
    (hSnorm : ∀ x : Q, ε zs * x = x * ε zs → ∀ σ ∈ S, x * σ * x⁻¹ ∈ S)
    (hbad : ∀ T : Subgroup Q, Group.IsPerfect T → (∀ τ ∈ T, ε zt * τ = τ * ε zt) →
      ¬ Nat.card S ∣ Nat.card T) : False := by
  classical
  have : Finite Q := Finite.of_surjective ε hε.surjective
  have hnorm := selected_prime_elements_normalize_theta_components
  have hdec_t := (hF13.reflection t ht).1
  have hKtL : kZero p E t ≤ L := kZero_le_of_mem_torusImage h hnorm htL hdec_t
  have hcs : c ∈ autFixedInG E s := c_mem_autFixedInG h hsL
  have hzs_mem : (zs : G) ∈ autFixedInG E s := by
    rw [hzs]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hzt_mem : (zt : G) ∈ autFixedInG E t := by
    rw [hzt]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  set Xs : Subgroup G := Subgroup.centralizer (autFixedInG E s : Set G) with hXs
  set Xt : Subgroup G := Subgroup.centralizer (autFixedInG E t : Set G) with hXt
  have hmemXs : ∀ y : ↥L, ε zs * ε y = ε y * ε zs → (y : G) ∈ Xs := by
    intro y hy
    have hcomm : Commute zs y := hε.commute_of_map_commute hzsp hy
    have h1 : Commute (zs : G) (y : G) := congrArg Subtype.val hcomm.eq
    have h2 : Commute c (y : G) := Sec12Three.comm_c_L h y y.2
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [hzs] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute (fun k hk l hl => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
      exact (Commute.zpow_zpow (Sec12Three.comm_c_L h zs zs.2).symm i j).eq) hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((h1.zpow_left i).mul_left (h2.zpow_left j)).eq
  set Ys : Subgroup ↥L := (L ⊓ Xs).subgroupOf L with hYs
  have hYs_mem : ∀ y : ↥L, y ∈ Ys ↔ (y : G) ∈ Xs := fun y => by
    rw [hYs, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
  have hSY : ∀ σ ∈ S, ∃ y ∈ Ys, ε y = σ := by
    intro σ hσ
    obtain ⟨y, rfl⟩ := hε.surjective σ
    exact ⟨y, (hYs_mem y).mpr (hmemXs y (hSc _ hσ)), rfl⟩
  have hSnorm' : ∀ y ∈ Ys, ∀ σ ∈ S, ε y * σ * (ε y)⁻¹ ∈ S := by
    intro y hy σ hσ
    have hyX : (y : G) ∈ Xs := (hYs_mem y).mp hy
    have h1 : (zs : G) * y = y * zs := Subgroup.mem_centralizer_iff.mp hyX _ hzs_mem
    have h2 : ε zs * ε y = ε y * ε zs := by
      rw [← map_mul, ← map_mul]
      exact congrArg ε (Subtype.ext h1)
    exact hSnorm (ε y) h2 σ hσ
  obtain ⟨PΛ, hPΛY, hPΛnorm, hPΛS, hPΛqs⟩ := exists_perfect_lift hε hSY hSnorm' hSperf hSsimple
  set P : Subgroup G := PΛ.map L.subtype with hP
  have hPL : P ≤ L := Subgroup.map_subtype_le _
  have hPX : P ≤ Xs := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hYs_mem y).mp (hPΛY hy)
  have hPnorm : ∀ y ∈ L ⊓ Xs, ∀ b ∈ P, y * b * y⁻¹ ∈ P := by
    intro y hy b hb
    obtain ⟨hyL, hyX⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨⟨y, hyL⟩ * b' * ⟨y, hyL⟩⁻¹, hPΛnorm _ ((hYs_mem _).mpr hyX) b' hb', rfl⟩
  have hPqs : IsQuasisimple P :=
    LocalCores.isQuasisimple_of_mulEquiv
      (PΛ.equivMapOfInjective L.subtype L.subtype_injective) hPΛqs
  obtain ⟨σ, hσS, hσp⟩ := hSp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hσmap : σ ∈ PΛ.map ε := by rw [hPΛS]; exact hσS
  have hσpow : σ ^ p = 1 := by rw [← hσp]; exact pow_orderOf_eq_one σ
  obtain ⟨z, hzP, hzσ, hzpow⟩ := exists_pow_lift hε hσmap hσpow
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσp
    exact hp.one_lt.ne hσp
  have hzG1 : (z : G) ≠ 1 := by
    intro h1
    apply hσ1
    have hz1 : z = 1 := Subtype.ext h1
    rw [← hzσ, hz1, map_one]
  have hzGp : (z : G) ^ p = 1 := by simpa using congrArg Subtype.val hzpow
  have hzord : orderOf (z : G) = p := orderOf_eq_prime hzGp hzG1
  have hzP' : (z : G) ∈ P := ⟨z, hzP, rfl⟩
  have hzc : (⟨(z : G), hzP'⟩ : P) ∉ Subgroup.center P := by
    intro hcen
    have hσc : (⟨σ, hσS⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨x, hxP, hxw⟩ := (show (w : Q) ∈ PΛ.map ε by rw [hPΛS]; exact w.2)
      apply Subtype.ext
      show (w : Q) * σ = σ * (w : Q)
      rw [← hzσ, ← hxw, ← map_mul, ← map_mul]
      congr 1
      have hxP' : (x : G) ∈ P := ⟨x, hxP, rfl⟩
      have h3 := Subgroup.mem_center_iff.mp hcen ⟨x, hxP'⟩
      have h4 : (x : G) * z = z * x := congrArg (fun q : P => (q : G)) h3
      exact Subtype.ext h4
    exact hσ1 (congrArg Subtype.val (center_eq_bot_of_simple_perfect hSperf hSsimple _ hσc))
  have hPK : P ≤ kZero p E s :=
    le_kZero_of_quasisimple h hcs hPL hPX hPnorm hPqs hzP' hzord hzc
  have hkz : kZero p E s = conjBy g (kZero p E t) := by
    rw [← heq]
    exact kZero_conj p t hg
  set P'' : Subgroup G := P.map (MulAut.conj g⁻¹).toMonoidHom with hP''
  have hP''K : P'' ≤ kZero p E t := by
    rintro _ ⟨b, hb, rfl⟩
    have := hPK hb
    rw [hkz, Equivariance.mem_conjBy] at this
    simpa [MulAut.conj_apply] using this
  have hP''L : P'' ≤ L := fun x hx => hKtL (hP''K hx)
  have hP''Xt : P'' ≤ Xt := fun x hx => kZero_le_centralizer p E t (hP''K hx)
  set P''Λ : Subgroup ↥L := P''.subgroupOf L with hP''Λ
  let e : ↥PΛ ≃* ↥P''Λ :=
    (PΛ.equivMapOfInjective L.subtype L.subtype_injective).trans
      ((P.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).trans
        (Subgroup.subgroupOfEquivOfLe hP''L).symm)
  have hN : ∀ z ∈ Subgroup.center ↥(PΛ.map ε), z = 1 := by
    rw [hPΛS]
    exact center_eq_bot_of_simple_perfect hSperf hSsimple
  have hcard := card_dvd_of_equiv hε e hN
  have hperfP : Group.IsPerfect ↥PΛ := hPΛqs.1
  have hperfP'' : Group.IsPerfect ↥P''Λ := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hperfT : Group.IsPerfect ↥(P''Λ.map ε) := Group.IsPerfect.map ε
  have hP''ε : P''Λ.map ε ≤ Subgroup.centralizer ({ε zt} : Set Q) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyX : (y : G) ∈ Xt := hP''Xt (Subgroup.mem_subgroupOf.mp hy)
    have h1 : (zt : G) * y = y * zt := Subgroup.mem_centralizer_iff.mp hyX _ hzt_mem
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    rw [← map_mul, ← map_mul]
    exact congrArg ε (Subtype.ext h1)
  have hcomm : ∀ τ ∈ P''Λ.map ε, ε zt * τ = τ * ε zt := fun τ hτ =>
    Subgroup.mem_centralizer_iff.mp (hP''ε hτ) _ (Set.mem_singleton _)
  refine hbad _ hperfT hcomm ?_
  rw [← hPΛS]
  exact hcard


theorem F_facts (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) :
    (∀ f ∈ E ⊓ L, f ^ p = 1) ∧ (∀ a ∈ E ⊓ L, ∀ b ∈ E ⊓ L, a * b = b * a) ∧
      ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
        (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → E ⊓ L ≤ F' → F' = E ⊓ L := by
  refine ⟨fun f hf => Sec12Three.pow_eq_one_of_mem_E h (Subgroup.mem_inf.mp hf).1,
    fun a ha b hb => mul_comm_of_isElementaryAbelian h.E_elem (Subgroup.mem_inf.mp ha).1
      (Subgroup.mem_inf.mp hb).1, ?_⟩
  intro F' hF'L hexp hcomm hFF'
  have hc : IsMulCommutative F' := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
  have hel : IsElementaryAbelian p F' :=
    { toIsMulCommutative := hc
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun g =>
        Subtype.ext (hexp _ g.2) }
  refine Sec12Three.F_max_generic h hG F' hF'L hel ?_ hFF'
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' := Subgroup.mem_inf.mp ha
  exact hcomm a (hFF' (Subgroup.mem_inf.mpr ⟨h.A_le_E ha'.1, ha'.2⟩)) x hx

end CFSG.RankThree.PartOne.KFOUT3
