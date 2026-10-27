module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan2
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesFusX
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesD
import CFSG.RankThree.PartTwo.Sec13.Item13Res2ProofCubeLift
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofTypes
import CFSG.RankThree.PartTwo.Sec13.Item131Facts

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem eq_of_card_three_lt {G : Type} [Group G] [Finite G] {P S T : Subgroup G}
    (hP : Nat.card P = 9) (hSP : S ≤ P) (hTS : T ≤ S) (hT : Nat.card T = 3) {x : G} (hxS : x ∈ S)
    (hxT : x ∉ T) : S = P := by
  have hdvd : Nat.card S ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hP]
    exact Subgroup.card_dvd_of_le hSP
  have h3 : 3 ∣ Nat.card S := hT ▸ Subgroup.card_dvd_of_le hTS
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  refine Subgroup.eq_of_le_of_card_ge hSP ?_
  interval_cases k
  · rw [hk] at h3
    norm_num at h3
  · exfalso
    have hST : T = S := Subgroup.eq_of_le_of_card_ge hTS (by rw [hk, hT]; norm_num)
    exact hxT (hST ▸ hxS)
  · rw [hk, hP]
    norm_num

theorem mem_thetaC_of_mk_eq_one {G : Type} [Group G] [Finite G] {c : G}
    {x : Subgroup.normalizer (Subgroup.zpowers c : Set G)}
    (hxC : (x : G) ∈ Subgroup.centralizer ({c} : Set G))
    (h : QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))) x = 1) : (x : G) ∈ thetaC c := by
  unfold thetaC
  rw [inSubgroup_theta_centralizer c]
  exact ⟨hxC, x, (QuotientGroup.eq_one_iff x).mp h, rfl⟩

theorem mk_eq_one_of_mem_thetaC {G : Type} [Group G] [Finite G] {c : G}
    {x : Subgroup.normalizer (Subgroup.zpowers c : Set G)} (hx : (x : G) ∈ thetaC c) :
    QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))) x = 1 := by
  unfold thetaC at hx
  rw [inSubgroup_theta_centralizer c] at hx
  obtain ⟨t, ht, hte⟩ := hx.2
  have htx : t = x := Subtype.ext hte
  rw [← htx]
  exact (QuotientGroup.eq_one_iff t).mpr ht

theorem mem_zpowers_sup_thetaC_of_mk {G : Type} [Group G] [Finite G] {c : G}
    {x : Subgroup.normalizer (Subgroup.zpowers c : Set G)} {m : ℤ}
    (hxC : (x : G) ∈ Subgroup.centralizer ({c} : Set G))
    (h : QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))) x =
      (QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
        ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩) ^ m) :
    (x : G) ∈ Subgroup.zpowers c ⊔ thetaC c := by
  set cH : Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ with hcH
  have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ((cH ^ m)⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, map_zpow, ← h, inv_mul_cancel]
  have hcm : ((cH ^ m : Subgroup.normalizer (Subgroup.zpowers c : Set G)) : G) = c ^ m := rfl
  have hCm : c ^ m ∈ Subgroup.centralizer ({c} : Set G) :=
    zpow_mem (Subgroup.mem_centralizer_singleton_iff.mpr rfl) m
  have hxm : (((cH ^ m)⁻¹ * x : Subgroup.normalizer (Subgroup.zpowers c : Set G)) : G) ∈
      thetaC c := by
    refine mem_thetaC_of_mk_eq_one ?_ h1
    have : (((cH ^ m)⁻¹ * x : Subgroup.normalizer (Subgroup.zpowers c : Set G)) : G) =
        (c ^ m)⁻¹ * x := rfl
    rw [this]
    exact mul_mem (inv_mem hCm) hxC
  have hxe : (x : G) = c ^ m * (((cH ^ m)⁻¹ * x : Subgroup.normalizer
      (Subgroup.zpowers c : Set G)) : G) := by
    have : (((cH ^ m)⁻¹ * x : Subgroup.normalizer (Subgroup.zpowers c : Set G)) : G) =
        (c ^ m)⁻¹ * x := rfl
    rw [this]
    group
  rw [hxe]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers c m)) (Subgroup.mem_sup_right hxm)

theorem s2fus_holds : S2fus := by
  intro G _ _ A c L E hCfg
  have hD := hCfg.hD
  have hSL2 := hCfg.hSL
  have hEle := hCfg.hEle
  have hEe := hCfg.hEe
  have hE27 := hCfg.hE27
  have hEC := hCfg.hEC
  have hEL := hCfg.hEL
  have hL := hD.mem_thetaComponentsAt
  have hcL : c ∈ L := mem_of_isSLThreePiTwo slTwoCenter hD hSL2
  have hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ResProof.isSLThreePi_of_isSLThreePiTwo hD hSL2
  have hty : Item131bProof.HeisType (L ⧸ aschbacherSolvableCore 3 L) := Or.inl hSL
  obtain ⟨hcE, hP1, hP2, hsup⟩ :=
    Item131bProof.e_facts hD hty hcL (hEle.trans inf_le_left) hEe hE27 hEC hEL
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc3 : c ^ 3 = 1 := by rw [← hD.orderOf_eq]; exact pow_orderOf_eq_one c
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hEC' : E ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hEcomm x hx c hcE)
  have hNΘ := centralizer_le_normalizer_thetaC (G := G) c
  have hΘL : ∀ x ∈ inSubgroup (aschbacherSolvableCore 3) L, x ∈ thetaC c := by
    intro x hx
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL] at hx
    exact hx.2
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  set θH := aschbacherSolvableCore 3 H with hθH
  have hLH : L ≤ H := le_normalizer_zpowers_of_mem hL
  have hθ3 : ¬ 3 ∣ Nat.card θH :=
    (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).2.2.1
  obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData hSL2
  have hL₀ : (Sec12.lBar c L).subgroupOf (lBarA c L A) = D.L₀ :=
    Res2Proof.subgroupOf_lBar_eq_L₀ hD D
  obtain ⟨e, ⟨heE, heL⟩, hecz⟩ : ∃ e ∈ E ⊓ L, e ∉ Subgroup.zpowers c := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show E ⊓ L ≤ Subgroup.zpowers c from h)
    rw [hP2, Nat.card_zpowers, hD.orderOf_eq] at this
    norm_num at this
  have he3 : e ^ 3 = 1 := hEe.2 e heE
  have hec : e * c = c * e := hEcomm e heE c hcE
  set eH : H := ⟨e, hLH heL⟩ with heH
  have heY : eH ∈ (L ⊔ A).subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left heL)
  set eb : lBarA c L A := ⟨QuotientGroup.mk' θH eH, Subgroup.mem_map_of_mem _ heY⟩ with heb
  obtain ⟨hebL₀, heb3, hebC⟩ :=
    Res2Proof.bar_mem_not_mem_centralizer hD D hcL heL he3 hec hecz (eb := eb) rfl
  set cb := mkC (L := L) hD.mem_A with hcb
  have hcbΛ : cb ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) := mkC_mem_lBar hD hcL
  have hcbC : cb ∈ D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set (lBarA c L A)) :=
    ⟨hL₀ ▸ hcbΛ, Subgroup.center_le_centralizer _ (mkC_mem_center hD)⟩
  have hcb1 : cb ≠ 1 := mkC_ne_one hD
  have hcb3 : cb ^ 3 = 1 := by
    have h : orderOf cb = 3 := orderOf_mkC hD
    have h' := pow_orderOf_eq_one cb
    rwa [h] at h'
  have hcb2 : cb ^ 2 ≠ 1 := by
    intro h2
    apply hcb1
    calc cb = cb ^ 3 * (cb ^ 2)⁻¹ := by group
      _ = 1 := by rw [hcb3, h2]; group
  obtain ⟨vb, hvbL, hvb3, hvbe⟩ :=
    sLTwoData_exists_transvection D hebL₀ heb3 hebC hcbC hcb1
  have hvbΛ : vb ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) := hL₀ ▸ hvbL
  obtain ⟨w, hwL, hwvb⟩ := Subgroup.mem_subgroupOf.mp hvbΛ
  have hwL' : (w : G) ∈ L := Subgroup.mem_subgroupOf.mp hwL
  have hvb3' : ((vb : lBarA c L A) : H ⧸ θH) ^ 3 = 1 := by
    have := congrArg Subtype.val hvb3
    simpa using this
  have hw3 : w ^ 3 ∈ θH := by
    apply (QuotientGroup.eq_one_iff (w ^ 3)).mp
    change QuotientGroup.mk' θH (w ^ 3) = 1
    rw [map_pow, hwvb]
    exact hvb3'
  have hw3o : orderOf (w ^ 3) ∣ Nat.card θH := Subgroup.orderOf_dvd_natCard θH hw3
  have ho3 : ¬ 3 ∣ orderOf (w ^ 3) := fun h3 => hθ3 (h3.trans hw3o)
  obtain ⟨t, hot, ht⟩ : ∃ t : ℕ, orderOf (w ^ 3) ∣ t ∧ t % 3 = 1 := by
    have : orderOf (w ^ 3) % 3 = 1 ∨ orderOf (w ^ 3) % 3 = 2 := by omega
    rcases this with h1 | h2
    · exact ⟨orderOf (w ^ 3), dvd_refl _, h1⟩
    · exact ⟨2 * orderOf (w ^ 3), dvd_mul_left _ 2, by omega⟩
  set vH : H := w ^ t with hvH
  have hvH3 : vH ^ 3 = 1 := by
    rw [hvH, ← pow_mul, mul_comm, pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp hot
  have hvbt : (vb : lBarA c L A) ^ t = vb := by
    conv_lhs => rw [← Nat.div_add_mod t 3, ht, pow_add, pow_mul, hvb3, one_pow, one_mul, pow_one]
  have hmkv : QuotientGroup.mk' θH vH = ((vb : lBarA c L A) : H ⧸ θH) := by
    rw [hvH, map_pow, hwvb]
    have := congrArg Subtype.val hvbt
    simpa using this
  set v : G := (vH : G) with hv
  have hvL : v ∈ L := by
    rw [hv, hvH]
    exact pow_mem hwL' t
  have hv3 : v ^ 3 = 1 := by
    have := congrArg Subtype.val hvH3
    simpa [hv] using this
  have hvC : v ∈ Subgroup.centralizer ({c} : Set G) := hLC hvL
  have hxH : v * e * v⁻¹ * e⁻¹ ∈ H := by
    refine hLH ?_
    exact mul_mem (mul_mem (mul_mem hvL heL) (inv_mem hvL)) (inv_mem heL)
  have hmkx : QuotientGroup.mk' θH (vH * eH * vH⁻¹ * eH⁻¹) = ((cb ^ 2 : lBarA c L A) : H ⧸ θH) := by
    rw [← hvbe]
    simp only [map_mul, map_inv, hmkv, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  have hxC : v * e * v⁻¹ * e⁻¹ ∈ Subgroup.centralizer ({c} : Set G) :=
    mul_mem (mul_mem (mul_mem hvC (hLC heL)) (inv_mem hvC)) (inv_mem (hLC heL))
  have hveM : v * e * v⁻¹ * e⁻¹ ∈ Subgroup.zpowers c ⊔ thetaC c := by
    have hcbv : ((cb : lBarA c L A) : H ⧸ θH) =
        QuotientGroup.mk' θH ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ := rfl
    exact mem_zpowers_sup_thetaC_of_mk (c := c) (x := vH * eH * vH⁻¹ * eH⁻¹) (m := 2) hxC (by
      rw [hmkx, Subgroup.coe_pow, hcbv]
      norm_cast)
  have hvenot : v * e * v⁻¹ * e⁻¹ ∉ thetaC c := by
    intro hΘ
    have h1 := mk_eq_one_of_mem_thetaC (c := c) (x := vH * eH * vH⁻¹ * eH⁻¹) hΘ
    rw [hmkx] at h1
    apply hcb2
    exact Subtype.ext h1
  have hEconj : ∀ y ∈ E, ∀ z ∈ Subgroup.zpowers c ⊔ thetaC c,
      y * z * y⁻¹ ∈ Subgroup.zpowers c ⊔ thetaC c := by
    intro y hy z hz
    refine conj_mem_zpowers_sup (hNΘ (hEC' hy)) ?_ hz
    have h1 : y * c * y⁻¹ * c⁻¹ = 1 := by
      rw [hEcomm y hy c hcE]
      group
    rw [h1]
    exact one_mem _
  let S : Subgroup G :=
    { carrier := {y | y ∈ E ⊓ L ∧ v * y * v⁻¹ * y⁻¹ ∈ Subgroup.zpowers c ⊔ thetaC c}
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
        refine ⟨mul_mem hy₁ hy₂, ?_⟩
        have e1 : v * (y₁ * y₂) * v⁻¹ * (y₁ * y₂)⁻¹ =
            (v * y₁ * v⁻¹ * y₁⁻¹) * (y₁ * (v * y₂ * v⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
        rw [e1]
        exact mul_mem h₁ (hEconj y₁ hy₁.1 _ h₂)
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro y ⟨hy, h⟩
        refine ⟨inv_mem hy, ?_⟩
        have e1 : v * y⁻¹ * v⁻¹ * y⁻¹⁻¹ = y⁻¹ * (v * y * v⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e1]
        exact hEconj y⁻¹ (inv_mem hy.1) _ (inv_mem h) }
  have hcS : c ∈ S := by
    refine ⟨⟨hcE, hcL⟩, ?_⟩
    have h1 : v * c * v⁻¹ * c⁻¹ = 1 := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hvC]
      group
    rw [h1]
    exact one_mem _
  have heS : e ∈ S := ⟨⟨heE, heL⟩, hveM⟩
  have hSP : S ≤ E ⊓ L := fun y hy => hy.1
  have hTS : Subgroup.zpowers c ≤ S := Subgroup.zpowers_le.mpr hcS
  have hT : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hD.orderOf_eq]
  have hSeq : S = E ⊓ L := eq_of_card_three_lt hP2 hSP hTS hT heS hecz
  refine ⟨v, hvL, hv3, ?_, ?_, e, ⟨heE, heL⟩, hvenot⟩
  · intro y hy
    have h := (Sec6.mem_thetaQuotCentralizer_iff.mp hy.2).2 v⁻¹ (inv_mem hvL)
    have e1 : v⁻¹⁻¹ * (y * v⁻¹ * y⁻¹) = v * y * v⁻¹ * y⁻¹ := by group
    rw [e1] at h
    exact hΘL _ h
  · intro y hy
    have : y ∈ S := hSeq ▸ hy
    exact this.2

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
