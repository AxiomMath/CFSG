module

public import CFSG.LocalAnalysis.WeakClosure81.SevenThreeTI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem conjSubgroup_commutator' (A B : Subgroup G) (g : G) :
    conjSubgroup ⁅A, B⁆ g = ⁅conjSubgroup A g, conjSubgroup B g⁆ := by
  show (⁅A, B⁆).map (MulAut.conj g⁻¹).toMonoidHom = _
  rw [Subgroup.map_commutator]
  rfl

private theorem zpow_eq_one_or_self_of_mul_self_eq_one {x : G} (hx : x * x = 1) (n : ℤ) :
    x ^ n = 1 ∨ x ^ n = x := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num,
      zpow_natCast, pow_two, hx]
    rw [h2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_one, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num,
      zpow_natCast, pow_two, hx]
    rw [h2, one_zpow, one_mul]

theorem exists_mem_commutator_conjSubgroup_ne_bot {V H : Subgroup G}
    (hV : IsElemAbelian 2 V) (hVH : V ≤ H) (hVnotO : ¬ V ≤ pCoreOf 2 H) :
    ∃ h ∈ H, ⁅conjSubgroup V h, V⁆ ≠ ⊥ := by
  obtain ⟨a, haV, haO⟩ := Set.not_subset.mp hVnotO
  by_contra hcon
  push Not at hcon
  apply haO
  refine mem_pCoreOf_of_forall_closure_isPGroup (hVH haV) ?_
  intro g hg
  have hcomm : ⁅conjSubgroup V g⁻¹, V⁆ = ⊥ := hcon g⁻¹ (H.inv_mem hg)
  have hcomm' : ⁅V, conjSubgroup V g⁻¹⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]; exact hcomm
  have hle : V ≤ Subgroup.normalizer (conjSubgroup V g⁻¹ : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm').trans
      (Subgroup.centralizer_le_normalizer _)
  have hmem : g * a * g⁻¹ ∈ conjSubgroup V g⁻¹ := by
    rw [mem_conjSubgroup_iff]
    rw [show g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ = a by group]
    exact haV
  exact isPGroup_closure_pair_of_mem_normalizer (V := V) (a := 1) (b := g⁻¹) hV
    (by rw [CFSG.Quasithin.conjSubgroup_one]; exact haV) hmem (hle haV)

theorem bSub_eq_inf_iSub {V H E : Subgroup G}
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal) (hVΩ : V ∈ omegaSet V H E)
    (hN : ∀ U ∈ omegaSet V H E, ⁅U, V⁆ ≠ ⊥ →
      V ⊓ Subgroup.normalizer (U : Set G) = V ⊓ iSub V H E)
    {h : G} (hh : h ∈ H) (hcomm : ⁅conjSubgroup V h, V⁆ ≠ ⊥) :
    bSub V h = conjSubgroup V h ⊓ iSub V H E := by
  have hU'Om : conjSubgroup V h⁻¹ ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet hEH hEnorm hVΩ (H.inv_mem hh)
  have hcomm' : ⁅conjSubgroup V h⁻¹, V⁆ ≠ ⊥ := by
    intro hbot
    apply hcomm
    have hconj : conjSubgroup ⁅conjSubgroup V h⁻¹, V⁆ h = ⁅V, conjSubgroup V h⁆ := by
      rw [conjSubgroup_commutator', CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
        CFSG.Quasithin.conjSubgroup_one]
    rw [hbot] at hconj
    simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_bot] at hconj
    rw [Subgroup.commutator_comm]
    exact hconj.symm
  have hN' := hN (conjSubgroup V h⁻¹) hU'Om hcomm'
  have hIleH : iSub V H E ≤ H := by
    refine iSup_le fun U => iSup_le fun _ => ?_
    exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hfixI : conjSubgroup (iSub V H E) h = iSub V H E :=
    conjSubgroup_eq_iff_mem_normalizer.mpr
      (le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal hEH hEnorm) hh)
  have key := congrArg (fun X => conjSubgroup X h) hN'
  rw [conjSubgroup_inf', conjSubgroup_inf', conjSubgroup_normalizer, hfixI] at key
  rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel, CFSG.Quasithin.conjSubgroup_one]
    at key
  rw [bSub, key]

theorem exists_commutator_eq_of_mem_inf_iSub {V H E : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hVΩ : V ∈ omegaSet V H E)
    (hN : ∀ U ∈ omegaSet V H E, ⁅U, V⁆ ≠ ⊥ →
      V ⊓ Subgroup.normalizer (U : Set G) = V ⊓ iSub V H E)
    {v : G} (hv : v ∈ V) (hvI : v ∉ iSub V H E) :
    ∀ w ∈ V ⊓ iSub V H E, ∃ a ∈ iSub V H E, ⁅a, v⁆ = w := by
  have hVH : V ≤ H := hOmH V hVΩ
  have hVnotO : ¬ V ≤ pCoreOf 2 H := (mem_omegaSet.mp hVΩ).choose_spec.2.2
  obtain ⟨h, hh, hcomm⟩ := exists_mem_commutator_conjSubgroup_ne_bot hV hVH hVnotO
  have hVhOm : conjSubgroup V h ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet hEH hEnorm hVΩ hh
  have hU0 : nVSub V h = V ⊓ iSub V H E := by
    rw [nVSub]
    exact hN (conjSubgroup V h) hVhOm hcomm
  have hB' : bSub V h = conjSubgroup V h ⊓ iSub V H E :=
    bSub_eq_inf_iSub hEH hEnorm hVΩ hN hh hcomm
  have hne : conjSubgroup V h ≠ V := by
    intro heq
    apply hcomm
    rw [heq, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1
  have hvU : v ∉ nVSub V h := by
    rw [hU0]
    exact fun hx => hvI hx.2
  have hCbot : bSub V h ⊓ Subgroup.centralizer ({v} : Set G) = ⊥ :=
    bSub_inf_centralizer_eq_bot hTI hne hv hvU
  let f : ↥(bSub V h) → ↥(nVSub V h) := fun b =>
    ⟨⁅(b : G), v⁆, by
      have hmem : ⁅v, (b : G)⁆ ∈ nVSub V h := commutator_mem_nVSub hV hTI hv b.2
      rw [← commutatorElement_inv]
      exact (nVSub V h).inv_mem hmem⟩
  have hf : Function.Injective f := by
    intro b₁ b₂ hb
    apply Subtype.ext
    have heq : ⁅(b₁ : G), v⁆ = ⁅(b₂ : G), v⁆ := congrArg Subtype.val hb
    have hmem_sub : (b₂ : G)⁻¹ * (b₁ : G) ∈ bSub V h :=
      (bSub V h).mul_mem ((bSub V h).inv_mem b₂.2) b₁.2
    have hmem_cen : (b₂ : G)⁻¹ * (b₁ : G) ∈ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      rw [commutatorElement_def, commutatorElement_def] at heq
      have h' : (b₁ : G) * v * (b₁ : G)⁻¹ = (b₂ : G) * v * (b₂ : G)⁻¹ :=
        mul_right_cancel heq
      calc v * ((b₂ : G)⁻¹ * (b₁ : G))
          = (b₂ : G)⁻¹ * ((b₂ : G) * v * (b₂ : G)⁻¹ * (b₁ : G)) := by group
        _ = (b₂ : G)⁻¹ * ((b₁ : G) * v) := by rw [← h']; group
        _ = ((b₂ : G)⁻¹ * (b₁ : G)) * v := by group
    have hmem : (b₂ : G)⁻¹ * (b₁ : G) ∈
        bSub V h ⊓ Subgroup.centralizer ({v} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hmem_sub, hmem_cen⟩
    have hmem1 : (b₂ : G)⁻¹ * (b₁ : G) ∈ (⊥ : Subgroup G) := by
      rw [← hCbot]
      exact hmem
    have h1 : (b₂ : G)⁻¹ * (b₁ : G) = 1 := Subgroup.mem_bot.mp hmem1
    calc (b₁ : G) = (b₂ : G) * ((b₂ : G)⁻¹ * (b₁ : G)) := by group
      _ = (b₂ : G) := by rw [h1, mul_one]
  have hIleH : iSub V H E ≤ H := by
    refine iSup_le fun U => iSup_le fun _ => ?_
    exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hfixI : conjSubgroup (iSub V H E) h = iSub V H E :=
    conjSubgroup_eq_iff_mem_normalizer.mpr
      (le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal hEH hEnorm) hh)
  have hcardB : Nat.card ↥(bSub V h) = Nat.card ↥(V ⊓ iSub V H E) := by
    have hconjinf : conjSubgroup (V ⊓ iSub V H E) h = conjSubgroup V h ⊓ iSub V H E := by
      rw [conjSubgroup_inf', hfixI]
    rw [hB', ← hconjinf, card_conjSubgroup']
  have hcardU : Nat.card ↥(nVSub V h) = Nat.card ↥(V ⊓ iSub V H E) := by rw [hU0]
  have hcard_le : Nat.card ↥(nVSub V h) ≤ Nat.card ↥(bSub V h) :=
    le_of_eq (by rw [hcardU, hcardB])
  intro w hw
  obtain ⟨b, hb⟩ := (hf.bijective_of_nat_card_le hcard_le).2
    (⟨w, by rw [hU0]; exact hw⟩ : ↥(nVSub V h))
  refine ⟨(b : G), ?_, ?_⟩
  · have hmem : (b : G) ∈ conjSubgroup V h ⊓ iSub V H E := hB' ▸ b.2
    exact (Subgroup.mem_inf.mp hmem).2
  · exact congrArg Subtype.val hb

theorem commutator_mem_inf_iSub {V H E : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hVΩ : V ∈ omegaSet V H E)
    {a v : G} (ha : a ∈ iSub V H E) (hv : v ∈ V) :
    ⁅a, v⁆ ∈ V ⊓ iSub V H E := by
  have hIleH : iSub V H E ≤ H := by
    refine iSup_le fun U => iSup_le fun _ => ?_
    exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hIN : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal hEH hEnorm)
  have hvH : v ∈ H := hOmH V hVΩ hv
  have hcommI : ⁅a, v⁆ ∈ iSub V H E := by
    have hconj : v * a⁻¹ * v⁻¹ ∈ iSub V H E :=
      (Subgroup.mem_normalizer_iff.mp (hIN hvH) a⁻¹).mp ((iSub V H E).inv_mem ha)
    rw [commutatorElement_def]
    rw [show a * v * a⁻¹ * v⁻¹ = a * (v * a⁻¹ * v⁻¹) by group]
    exact (iSub V H E).mul_mem ha hconj
  have hVIn : V ⊓ iSub V H E ≠ ⊥ := by
    rw [inf_iSub_eq_inf_pCoreOf hVΩ]
    exact inf_pCoreOf_ne_bot_of_mem_omegaSet hV hE hEH hEnorm hVΩ
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVIn
  have hwV : (w : G) ∈ V := (Subgroup.mem_inf.mp w.2).1
  have hwI : (w : G) ∈ iSub V H E := (Subgroup.mem_inf.mp w.2).2
  have hwne : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hIab : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond hV hTI hE hOmH
  have haC : a ∈ Subgroup.centralizer ({(w : G)} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (congrArg Subtype.val (hIab.1.is_comm.comm ⟨a, ha⟩ ⟨(w : G), hwI⟩)).symm
  have haN : a ∈ Subgroup.normalizer (V : Set G) :=
    centralizer_le_normalizer_of_isTI hTI hwV hwne haC
  have hcommV : ⁅a, v⁆ ∈ V := by
    rw [commutatorElement_def]
    have h1 : a * v * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp haN v).mp hv
    exact V.mul_mem h1 (V.inv_mem hv)
  exact ⟨hcommV, hcommI⟩

theorem commutator_iSub_eq_inf_iSub {V H E : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hVΩ : V ∈ omegaSet V H E)
    (hN : ∀ U ∈ omegaSet V H E, ⁅U, V⁆ ≠ ⊥ →
      V ⊓ Subgroup.normalizer (U : Set G) = V ⊓ iSub V H E)
    {v : G} (hv : v ∈ V) (hvI : v ∉ iSub V H E) :
    ⁅iSub V H E, Subgroup.zpowers v⁆ = V ⊓ iSub V H E := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro a ha w hw
    rw [Subgroup.mem_zpowers_iff] at hw
    obtain ⟨n, rfl⟩ := hw
    rcases zpow_eq_one_or_self_of_mul_self_eq_one (elemAbelian_mul_self hV hv) n with h1 | hv'
    · rw [h1]; simp [commutatorElement_def]
    · rw [hv']
      exact commutator_mem_inf_iSub hV hTI hE hEH hEnorm hOmH hVΩ ha hv
  · intro w hw
    obtain ⟨a, ha, haw⟩ :=
      exists_commutator_eq_of_mem_inf_iSub hV hTI hEH hEnorm hOmH hVΩ hN hv hvI w hw
    rw [← haw]
    exact Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers v)

theorem nVSub_eq_inf_iSub_of_relIndex_eq_two {V H E : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hindex : (V ⊓ iSub V H E).relIndex V = 2) :
    ∀ U ∈ omegaSet V H E, ⁅U, V⁆ ≠ ⊥ →
      V ⊓ Subgroup.normalizer (U : Set G) = V ⊓ iSub V H E := by
  intro U hU hUV
  obtain ⟨g, rfl, hEU, hUnotO⟩ := mem_omegaSet.mp hU
  have hUg : conjSubgroup V g ∈ omegaSet V H E := ⟨g, rfl, hEU, hUnotO⟩
  have hneUV : conjSubgroup V g ≠ V := by
    intro heq
    apply hUV
    rw [heq, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1
  have hIab : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond hV hTI hE hOmH
  have hIne : conjSubgroup V g ⊓ iSub V H E ≠ ⊥ := by
    rw [inf_iSub_eq_inf_pCoreOf hUg]
    exact inf_pCoreOf_ne_bot_of_mem_omegaSet hV hE hEH hEnorm hUg
  obtain ⟨w', hw'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hIne
  have hw'U : (w' : G) ∈ conjSubgroup V g := (Subgroup.mem_inf.mp w'.2).1
  have hw'I : (w' : G) ∈ iSub V H E := (Subgroup.mem_inf.mp w'.2).2
  have hw'ne : (w' : G) ≠ 1 := fun h => hw'1 (Subtype.ext h)
  have hstep : V ⊓ iSub V H E ≤ V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) := by
    intro x hx
    obtain ⟨hxV, hxI⟩ := Subgroup.mem_inf.mp hx
    have hcomm : x * (w' : G) = (w' : G) * x :=
      congrArg Subtype.val (hIab.1.is_comm.comm ⟨x, hxI⟩ ⟨(w' : G), hw'I⟩)
    have hxC : x ∈ Subgroup.centralizer ({(w' : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm
    exact ⟨hxV, centralizer_le_normalizer_conj hTI g hw'U hw'ne hxC⟩
  have hMne : V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) ≠ V := by
    intro hMV
    have hVN : V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
      have h := inf_le_right (a := V)
        (b := Subgroup.normalizer (conjSubgroup V g : Set G))
      rwa [hMV] at h
    have hB_eq_U : bSub V g = conjSubgroup V g := by
      by_contra hB
      have hy : ∃ y ∈ conjSubgroup V g, y ∉ bSub V g := by
        by_contra h
        push Not at h
        exact hB (le_antisymm inf_le_left (fun y hy => h y hy))
      obtain ⟨y, hyU, hyB⟩ := hy
      have hCbot : nVSub V g ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ :=
        nVSub_inf_centralizer_eq_bot hTI hneUV hyU hyB
      have hnV : nVSub V g = V := hMV
      let f : ↥V → ↥(bSub V g) := fun u =>
        ⟨⁅(u : G), y⁆, by
          have hmem : ⁅y, (u : G)⁆ ∈ bSub V g :=
            commutator_mem_bSub hV hTI hyU (by rw [hnV]; exact u.2)
          rw [← commutatorElement_inv]
          exact (bSub V g).inv_mem hmem⟩
      have hf : Function.Injective f := by
        intro u₁ u₂ heq
        apply Subtype.ext
        have he : ⁅(u₁ : G), y⁆ = ⁅(u₂ : G), y⁆ := congrArg Subtype.val heq
        have hmem_sub : (u₂ : G)⁻¹ * (u₁ : G) ∈ nVSub V g := by
          rw [hnV]
          exact V.mul_mem (V.inv_mem u₂.2) u₁.2
        have hmem_cen : (u₂ : G)⁻¹ * (u₁ : G) ∈ Subgroup.centralizer ({y} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          rw [commutatorElement_def, commutatorElement_def] at he
          have h' : (u₁ : G) * y * (u₁ : G)⁻¹ = (u₂ : G) * y * (u₂ : G)⁻¹ :=
            mul_right_cancel he
          calc y * ((u₂ : G)⁻¹ * (u₁ : G))
              = (u₂ : G)⁻¹ * ((u₂ : G) * y * (u₂ : G)⁻¹ * (u₁ : G)) := by group
            _ = (u₂ : G)⁻¹ * ((u₁ : G) * y) := by rw [← h']; group
            _ = ((u₂ : G)⁻¹ * (u₁ : G)) * y := by group
        have hmem : (u₂ : G)⁻¹ * (u₁ : G) ∈
            nVSub V g ⊓ Subgroup.centralizer ({y} : Set G) :=
          Subgroup.mem_inf.mpr ⟨hmem_sub, hmem_cen⟩
        have hmem1 : (u₂ : G)⁻¹ * (u₁ : G) ∈ (⊥ : Subgroup G) := by
          rw [← hCbot]
          exact hmem
        have h1 : (u₂ : G)⁻¹ * (u₁ : G) = 1 := Subgroup.mem_bot.mp hmem1
        calc (u₁ : G) = (u₂ : G) * ((u₂ : G)⁻¹ * (u₁ : G)) := by group
          _ = (u₂ : G) := by rw [h1, mul_one]
      have hcard_ge : Nat.card (conjSubgroup V g) ≤ Nat.card (bSub V g) := by
        rw [card_conjSubgroup']
        exact Nat.card_le_card_of_injective f hf
      exact hB (Subgroup.eq_of_le_of_card_ge inf_le_left hcard_ge)
    have hUN : conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) := by
      rw [← hB_eq_U]
      exact inf_le_right
    have hle : ⁅conjSubgroup V g, V⁆ ≤ ⊥ := by
      rw [← inf_conjSubgroup_eq_bot_of_isTI hTI hneUV]
      rw [Subgroup.commutator_le]
      intro u hu v hv
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        have h1 : u * v * u⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hUN hu) v).mp hv
        exact V.mul_mem h1 (V.inv_mem hv)
      · rw [commutatorElement_def]
        have h1 : v * u⁻¹ * v⁻¹ ∈ conjSubgroup V g :=
          (Subgroup.mem_normalizer_iff.mp (hVN hv) u⁻¹).mp ((conjSubgroup V g).inv_mem hu)
        rw [show u * v * u⁻¹ * v⁻¹ = u * (v * u⁻¹ * v⁻¹) by group]
        exact (conjSubgroup V g).mul_mem hu h1
    exact hUV (le_bot_iff.mp hle)
  have hrel := Subgroup.relIndex_mul_relIndex (H := V ⊓ iSub V H E)
    (K := V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) (L := V) hstep inf_le_left
  rw [hindex] at hrel
  have hMrel_ne_one :
      (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)).relIndex V ≠ 1 := by
    intro h
    exact hMne (le_antisymm inf_le_left (Subgroup.relIndex_eq_one.mp h))
  have hdvd : (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)).relIndex V ∣ 2 :=
    ⟨(V ⊓ iSub V H E).relIndex (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)),
      by rw [mul_comm]; exact hrel.symm⟩
  have hMrel : (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)).relIndex V = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hMrel_ne_one
    · exact h
  have hKrel : (V ⊓ iSub V H E).relIndex
      (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) = 1 := by
    rw [hMrel] at hrel
    omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hKrel) hstep

end CFSG.LocalAnalysis.WeakClosure81
