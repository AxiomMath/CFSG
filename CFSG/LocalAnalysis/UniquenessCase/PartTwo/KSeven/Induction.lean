module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open Subgroup

private noncomputable def ksindAutOfInvariant {J : Type} [Group J] {K : Subgroup J}
    (w : MulAut J) (hw : K.map (w : J →* J) ≤ K)
    (hw' : K.map ((w⁻¹ : MulAut J) : J →* J) ≤ K) : MulAut K :=
  (w.subgroupMap K).trans (MulEquiv.subgroupCongr (le_antisymm hw (by
    have hcomp : (w : J →* J).comp ((w⁻¹ : MulAut J) : J →* J) = MonoidHom.id J := by
      ext x; simp
    calc K = (K.map ((w⁻¹ : MulAut J) : J →* J)).map (w : J →* J) := by
          rw [Subgroup.map_map, hcomp, Subgroup.map_id]
      _ ≤ K.map (w : J →* J) := Subgroup.map_mono hw')))

private noncomputable def ksindActionOnInvariant {J : Type} [Group J]
    (W : Subgroup (MulAut J)) (K : Subgroup J)
    (hK : ∀ w ∈ W, K.map (w : J →* J) ≤ K) : W →* MulAut K where
  toFun w := ksindAutOfInvariant (w : MulAut J) (hK w w.2)
    (hK ((w : MulAut J)⁻¹) (W.inv_mem w.2))
  map_one' := by ext x; rfl
  map_mul' w v := by ext x; rfl

private lemma ksindActionOnInvariant_apply {J : Type} [Group J]
    {W : Subgroup (MulAut J)} {K : Subgroup J}
    (hK : ∀ w ∈ W, K.map (w : J →* J) ≤ K) (w : W) (x : K) :
    ((ksindActionOnInvariant W K hK w x : K) : J) = (w : MulAut J) x := rfl

private lemma ksind_commutator_le_of_le {J : Type} [Group J] {F K : Subgroup J}
    (h : F ≤ K) : ⁅F, F⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem (h ha) (h hb)) (K.inv_mem (h ha))) (K.inv_mem (h hb))

private lemma ksind_map_fixedBy_zpowers_le {J : Type} [Group J]
    {W : Subgroup (MulAut J)} {v : MulAut J} (hvW : v ∈ W)
    (hcomm : ∀ w ∈ W, w * v = v * w) (w : W) :
    (fixedBy (Subgroup.zpowers v)).map ((w : MulAut J) : J →* J) ≤
      fixedBy (Subgroup.zpowers v) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ fixedBy (Subgroup.zpowers v) := by simpa using hx
  rw [mem_fixedBy] at hx'
  change ∀ z ∈ Subgroup.zpowers v, z ((w : MulAut J) x) = (w : MulAut J) x
  intro z hz
  rw [Subgroup.mem_zpowers_iff] at hz
  obtain ⟨k, rfl⟩ := hz
  have hcommk : Commute (w : MulAut J) (v ^ k) :=
    (commute_iff_eq _ _).mpr (hcomm (w : MulAut J) w.2) |>.zpow_right k
  have hxv : (v ^ k) x = x :=
    hx' (v ^ k) (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  calc (v ^ k) ((w : MulAut J) x)
      = (((v ^ k) * (w : MulAut J)) x) := rfl
    _ = (((w : MulAut J) * (v ^ k)) x) := by rw [← hcommk.eq]
    _ = (w : MulAut J) ((v ^ k) x) := rfl
    _ = (w : MulAut J) x := by rw [hxv]

private lemma ksindActionOnInvariant_eq_one_of_fixed {J : Type} [Group J]
    {W : Subgroup (MulAut J)} {K : Subgroup J}
    (hK : ∀ w ∈ W, K.map (w : J →* J) ≤ K) {v : MulAut J} (hvW : v ∈ W)
    (hfix : ∀ x ∈ K, v x = x) :
    ksindActionOnInvariant W K hK ⟨v, hvW⟩ = 1 := by
  ext x
  simpa [ksindActionOnInvariant_apply] using hfix x x.2

private lemma ksind_map_normalizer_subtype_le {J : Type} [Group J]
    {K Z : Subgroup J} (hZK : Z ≤ K) :
    (normalizer ((Z.subgroupOf K : Subgroup K) : Set K)).map K.subtype ≤
      normalizer (Z : Set J) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hZK]
  calc ((normalizer Z).subgroupOf K).map K.subtype = normalizer Z ⊓ K :=
        Subgroup.subgroupOf_map_subtype _ _
    _ ≤ normalizer Z := inf_le_left

private lemma ksind_map_fixedBy_subtype_le {J : Type} [Group J]
    (W : Subgroup (MulAut J)) (K : Subgroup J)
    (hK : ∀ w ∈ W, K.map (w : J →* J) ≤ K) :
    (fixedBy (ksindActionOnInvariant W K hK).range).map K.subtype ≤ fixedBy W := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ fixedBy (ksindActionOnInvariant W K hK).range := by simpa using hx
  rw [mem_fixedBy] at hx'
  rw [mem_fixedBy]
  intro w hw
  have hmem : ksindActionOnInvariant W K hK ⟨w, hw⟩ ∈
      (ksindActionOnInvariant W K hK).range := ⟨⟨w, hw⟩, rfl⟩
  have happ := hx' (ksindActionOnInvariant W K hK ⟨w, hw⟩) hmem
  have := congrArg (fun y : ↥K => (y : J)) happ
  simpa [ksindActionOnInvariant_apply] using this

theorem sevenFree_of_prime_step (Good : ∀ (J : Type) [Group J], Prop)
    (hGood : ∀ (J : Type) [Group J], Good J → Finite J ∧ 3 ∣ Nat.card J ∧ ¬ 9 ∣ Nat.card J)
    (hstep : ∀ (J : Type) [Group J] [Finite J], Good J → ∀ W : Subgroup (MulAut J),
      IsPGroup 7 W → Nat.card W = 7 → ∀ Z : Sylow 3 J,
      (∀ w ∈ W, ∀ z ∈ (Z : Subgroup J), w z = z) → StepConcl Good W (Z : Subgroup J))
    (J : Type) [Group J] (hJ : Good J) : SevenFree J := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let Q : ℕ → Prop := fun n => ∀ (J : Type) [Group J], Good J →
    ∀ W : Subgroup (MulAut J), IsPGroup 7 W → Nat.card W = n → W ≠ ⊥ →
      ∀ Z : Sylow 3 J, (∀ w ∈ W, ∀ z ∈ (Z : Subgroup J), w z = z) →
        normalizer ((Z : Subgroup J) : Set J) ⊔ fixedBy W = ⊤
  have hQ : ∀ n, Q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro J _ hJ W hW hcard hWne Z hZ
      haveI hJfin : Finite J := (hGood J hJ).1
      haveI hAutFin : Finite (MulAut J) := MulEquiv.finite_left
      have hWnt : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hWne
      haveI := hWnt
      have hcenter_nt : Nontrivial (Subgroup.center ↥W) := hW.center_nontrivial
      haveI := hcenter_nt
      have hcenter_p : IsPGroup 7 ↥(Subgroup.center ↥W) :=
        hW.to_subgroup (Subgroup.center ↥W)
      have h7dvd : 7 ∣ Nat.card ↥(Subgroup.center ↥W) := by
        rcases hcenter_p.card_eq_or_dvd with h1 | hdvd
        · exact absurd h1 (Nat.ne_of_gt Finite.one_lt_card)
        · exact hdvd
      obtain ⟨u, hu⟩ :=
        exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥W)) 7 h7dvd
      let uW : ↥W := (u : ↥W)
      let v : MulAut J := (uW : MulAut J)
      have huW_order : orderOf uW = 7 := by
        change orderOf ((u : ↥W)) = 7
        rw [Subgroup.orderOf_coe, hu]
      have hv_order : orderOf v = 7 := by
        change orderOf ((uW : MulAut J)) = 7
        rw [Subgroup.orderOf_coe, huW_order]
      have hv_ne : v ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hv_order
        exact (by norm_num : (1 : ℕ) ≠ 7) hv_order
      have hcenter_comm : ∀ g : ↥W, g * uW = uW * g := by
        intro g
        exact Subgroup.mem_center_iff.mp u.2 g
      have hcomm : ∀ w ∈ W, w * v = v * w := by
        intro w hw
        exact congrArg (fun x : ↥W => (x : MulAut J)) (hcenter_comm ⟨w, hw⟩)
      let W1 : Subgroup (MulAut J) := Subgroup.zpowers v
      have hW1le : W1 ≤ W := Subgroup.zpowers_le.mpr uW.2
      have hW1 : IsPGroup 7 W1 := by
        apply IsPGroup.of_card (n := 1)
        rw [Nat.card_zpowers, hv_order, pow_one]
      have hW1card : Nat.card W1 = 7 := by rw [Nat.card_zpowers, hv_order]
      have hZ1 : ∀ y ∈ W1, ∀ z ∈ (Z : Subgroup J), y z = z := by
        intro y hy z hz
        exact hZ y (hW1le hy) z hz
      obtain ⟨hGoodJ1, hZleJ1, hsupJ1⟩ := hstep J hJ W1 hW1 hW1card Z hZ1
      let F : Subgroup J := fixedBy W1
      let J1 : Subgroup J := ⁅F, F⁆
      have hFmap : ∀ w ∈ W, F.map (w : J →* J) ≤ F := by
        intro w hw
        exact ksind_map_fixedBy_zpowers_le uW.2 hcomm ⟨w, hw⟩
      have hJ1inv : ∀ w ∈ W, J1.map (w : J →* J) ≤ J1 := by
        intro w hw
        change (⁅F, F⁆).map (w : J →* J) ≤ ⁅F, F⁆
        rw [Subgroup.map_commutator]
        exact Subgroup.commutator_mono (hFmap w hw) (hFmap w hw)
      let ρ : ↥W →* MulAut ↥J1 := ksindActionOnInvariant W J1 hJ1inv
      let W' : Subgroup (MulAut ↥J1) := ρ.range
      have hW' : IsPGroup 7 W' :=
        hW.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
      have hJ1le_fixed : J1 ≤ fixedBy W1 :=
        ksind_commutator_le_of_le (le_refl F)
      have hv_fix_J1 : ∀ x ∈ J1, v x = x := by
        intro x hx
        exact (mem_fixedBy.mp (hJ1le_fixed hx)) v (Subgroup.mem_zpowers v)
      have hρv : ρ ⟨v, hW1le (Subgroup.mem_zpowers v)⟩ = 1 :=
        ksindActionOnInvariant_eq_one_of_fixed hJ1inv
          (hW1le (Subgroup.mem_zpowers v)) hv_fix_J1
      have hker_ne : ρ.ker ≠ ⊥ := by
        intro hbot
        have hmem : (⟨v, hW1le (Subgroup.mem_zpowers v)⟩ : ↥W) ∈ ρ.ker := by
          rw [MonoidHom.mem_ker]
          exact hρv
        rw [hbot] at hmem
        have hone : (⟨v, hW1le (Subgroup.mem_zpowers v)⟩ : ↥W) = 1 := by
          simpa using hmem
        exact hv_ne (congrArg (fun x : ↥W => (x : MulAut J)) hone)
      have hker_gt : 1 < Nat.card ρ.ker :=
        (Subgroup.one_lt_card_iff_ne_bot ρ.ker).mpr hker_ne
      have hltW : Nat.card W' < Nat.card ↥W := by
        calc Nat.card W' < Nat.card ρ.ker * Nat.card W' :=
              (Nat.lt_mul_iff_one_lt_left Nat.card_pos).mpr hker_gt
          _ = Nat.card ↥W := Subgroup.card_ker_mul_card_range ρ
      have hltn : Nat.card W' < n := by rw [← hcard]; exact hltW
      by_cases hW'bot : W' = ⊥
      · have hJ1F : J1 ≤ fixedBy W := by
          intro x hx
          rw [mem_fixedBy]
          intro w hw
          have hρ1 : ρ = 1 := MonoidHom.range_eq_bot_iff.mp hW'bot
          have hw1 : ρ ⟨w, hw⟩ = 1 := by rw [hρ1]; rfl
          have happ := congrArg (fun e : MulAut ↥J1 => ((e ⟨x, hx⟩ : ↥J1) : J)) hw1
          simpa [ρ, ksindActionOnInvariant_apply] using happ
        refine le_antisymm le_top ?_
        calc (⊤ : Subgroup J) = normalizer ((Z : Subgroup J) : Set J) ⊔ J1 := hsupJ1.symm
          _ ≤ normalizer ((Z : Subgroup J) : Set J) ⊔
              (normalizer ((Z : Subgroup J) : Set J) ⊔ fixedBy W) :=
              sup_le_sup_left (hJ1F.trans le_sup_right) _
          _ = normalizer ((Z : Subgroup J) : Set J) ⊔ fixedBy W := by
              rw [← sup_assoc, sup_idem]
      · let Z' : Sylow 3 ↥J1 := Z.subtype hZleJ1
        have hZ' : ∀ w ∈ W', ∀ z ∈ (Z' : Subgroup ↥J1), w z = z := by
          intro w hw z hz
          rw [MonoidHom.mem_range] at hw
          obtain ⟨w₀, rfl⟩ := hw
          apply Subtype.ext
          rw [ksindActionOnInvariant_apply]
          exact hZ (w₀ : MulAut J) w₀.2 (z : J) hz
        have hQJ1 := ih (Nat.card W') hltn ↥J1 hGoodJ1 W' hW' rfl hW'bot Z' hZ'
        have hmapN : (normalizer ((Z' : Subgroup ↥J1) : Set ↥J1)).map J1.subtype ≤
            normalizer ((Z : Subgroup J) : Set J) :=
          ksind_map_normalizer_subtype_le hZleJ1
        have hmapF : (fixedBy W').map J1.subtype ≤ fixedBy W :=
          ksind_map_fixedBy_subtype_le W J1 hJ1inv
        have hmapJ1 : (⊤ : Subgroup ↥J1).map J1.subtype = J1 := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
        have hJ1le : J1 ≤ normalizer ((Z : Subgroup J) : Set J) ⊔ fixedBy W := by
          have hle : (⊤ : Subgroup ↥J1).map J1.subtype ≤
              normalizer ((Z : Subgroup J) : Set J) ⊔ fixedBy W := by
            calc (⊤ : Subgroup ↥J1).map J1.subtype =
                  (normalizer ((Z' : Subgroup ↥J1) : Set ↥J1) ⊔
                    fixedBy W').map J1.subtype := by rw [hQJ1]
              _ = (normalizer ((Z' : Subgroup ↥J1) : Set ↥J1)).map J1.subtype ⊔
                  (fixedBy W').map J1.subtype := Subgroup.map_sup _ _ _
              _ ≤ normalizer ((Z : Subgroup J) : Set J) ⊔ fixedBy W :=
                  sup_le (hmapN.trans le_sup_left) (hmapF.trans le_sup_right)
          rwa [hmapJ1] at hle
        refine le_antisymm le_top ?_
        calc (⊤ : Subgroup J) = normalizer ((Z : Subgroup J) : Set J) ⊔ J1 := hsupJ1.symm
          _ ≤ normalizer ((Z : Subgroup J) : Set J) ⊔
              (normalizer ((Z : Subgroup J) : Set J) ⊔ fixedBy W) :=
              sup_le_sup_left hJ1le _
          _ = normalizer ((Z : Subgroup J) : Set J) ⊔ fixedBy W := by
              rw [← sup_assoc, sup_idem]
  intro W hW hWne Z hZ
  exact hQ (Nat.card W) J hJ W hW rfl hWne Z hZ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
