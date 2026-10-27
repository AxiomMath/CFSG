module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Bar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem layer_conj_mem_sup {Γ : Type} [Group Γ] [Finite Γ] {C D : Subgroup Γ}
    (hC : IsComponent C) (hD : IsComponent D) (hcomm : ∀ x ∈ C, ∀ y ∈ D, x * y = y * x)
    {e : Γ} (he : e ∈ layer Γ) {k : Γ} (hk : k ∈ C ⊔ D) : e * k * e⁻¹ ∈ C ⊔ D := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hk
  have e1 : e * (a * b) * e⁻¹ = (e * a * e⁻¹) * (e * b * e⁻¹) := by group
  rw [e1]
  exact Subgroup.mul_mem_sup
    ((Subgroup.mem_normalizer_iff.mp (CFSG.LocalCores.layer_le_normalizer hC he) a).mp ha)
    ((Subgroup.mem_normalizer_iff.mp (CFSG.LocalCores.layer_le_normalizer hD he) b).mp hb)

section Swap

variable [(Q.subgroupOf M).Normal]

theorem Ctx.false_of_swap_centralized (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hCQ : ClassicalQuasisimpleStatement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hcs : CompSimple (Mbar M Q)) {Zc : Subgroup (Mbar M Q)} (hZ : IsComponent Zc)
    {s : Mbar M Q} (hs : s ∈ bar M Q (LB M Q B)) (hne : conjSubgroup s Zc ≠ Zc) {τ : M}
    (hτ : (τ : G) ∈ LB M Q B) (hτQ : (τ : G) ∉ Q)
    (hcZ : ∀ x ∈ Zc, x * (QuotientGroup.mk τ : Mbar M Q) = QuotientGroup.mk τ * x)
    (hcZ' : ∀ x ∈ conjSubgroup s Zc,
      x * (QuotientGroup.mk τ : Mbar M Q) = QuotientGroup.mk τ * x) : False := by
  classical
  have hΛ := hc.swapHyp hw hn hno
  set Zc' := conjSubgroup s Zc with hZc'
  have hZ'c : IsComponent Zc' := isComponent_conjSubgroup s hZ
  have hcomm := swap_comm hZ hne
  have hinf := swap_inf_eq_bot hcs hZ hne
  set KK : Subgroup (Mbar M Q) := Zc ⊔ Zc' with hKK
  set R : Subgroup (Mbar M Q) := bar M Q (Rt M (LB M Q B) (τ : G)) with hR
  have hZR : Zc ≤ R := hc.component_le_bar_Rt h34 hw hn hno hgen hcs hZ hτ hcZ
  have hZ'R : Zc' ≤ R := hc.component_le_bar_Rt h34 hw hn hno hgen hcs hZ'c hτ hcZ'
  have hKR : KK ≤ R := sup_le hZR hZ'R
  have hRne : Rt M (LB M Q B) (τ : G) ≠ LB M Q B := by
    intro hRL
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hZ
    have hZΛ : Zc ≤ bar M Q (LB M Q B) := by
      have := hZR
      rwa [hR, hRL] at this
    exact hab (Subtype.ext (hΛ.comm _ (hZΛ a.2) _ (hZΛ b.2)))
  obtain ⟨K, hF, hFin, hK2, Gc, hGc, π, hK, hπs, hπk, hcl⟩ :=
    hc.classical_quotient h310 hw hn hno hgen hτ hτQ hRne
  have hq4 : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
  have hshape := hcl.shape hCQ hq4
  have hSL2K : CFSG.IsQuasisimple ↥(StatedSL 2 K) := (hCQ K hq4).1 2 le_rfl
  have hKN : KK ⊓ bar M Q (hc.CN (τ : G)) = ⊥ := by
    have h := hc.sSup_inf_CN_eq_bot h34 hw hn hno hgen hcs hτ {Zc, Zc'}
      (by
        intro C hC
        rcases hC with rfl | rfl
        · exact ⟨hZ, hZR⟩
        · exact ⟨hZ'c, hZ'R⟩)
    rwa [sSup_pair] at h
  have hinj : ∀ x : ↥KK, π ⟨(x : Mbar M Q), hKR x.2⟩ = 1 → x = 1 := by
    intro x hx
    have h1 := (hπk ⟨(x : Mbar M Q), hKR x.2⟩).mp hx
    have h2 : (x : Mbar M Q) ∈ KK ⊓ bar M Q (hc.CN (τ : G)) := ⟨x.2, h1⟩
    rw [hKN, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hEn : (layer (Mbar M Q)).Normal := by
    haveI := CFSG.LocalCores.layer_characteristic (G := Mbar M Q)
    infer_instance
  have hZE : Zc ≤ layer (Mbar M Q) := CFSG.LocalCores.component_le_layer hZ
  have hZ'E : Zc' ≤ layer (Mbar M Q) := CFSG.LocalCores.component_le_layer hZ'c
  have hKE : KK ≤ layer (Mbar M Q) := sup_le hZE hZ'E
  have hnorm : ∀ e ∈ layer (Mbar M Q), ∀ k ∈ KK, e * k * e⁻¹ ∈ KK := by
    intro e he k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hk
    have e1 : e * (a * b) * e⁻¹ = (e * a * e⁻¹) * (e * b * e⁻¹) := by group
    rw [e1]
    exact Subgroup.mul_mem_sup
      ((Subgroup.mem_normalizer_iff.mp (CFSG.LocalCores.layer_le_normalizer hZ he) a).mp ha)
      ((Subgroup.mem_normalizer_iff.mp (CFSG.LocalCores.layer_le_normalizer hZ'c he) b).mp hb)
  have hns : ¬ Group.IsSolvable ↥KK := by
    intro hs
    haveI := hs
    exact not_isSolvable_of_isQuasisimple hZ.1
      (solvable_of_solvable_injective (f := Subgroup.inclusion (le_sup_left : Zc ≤ KK))
        (Subgroup.inclusion_injective _))
  rcases subnormal_embedding_cases hSL2K (R := R) (H := R ⊓ layer (Mbar M Q)) (X := KK) π hπs
    hshape (le_inf hKR hKE) inf_le_left (fun h hh k hk => hnorm h hh.2 k hk)
    (fun r hr h hh => ⟨R.mul_mem (R.mul_mem hr hh.1) (R.inv_mem hr),
      hEn.conj_mem h hh.2 r⟩) hinj hns with ⟨hsurj, -⟩ | he
  ·
    have hsR : s ∈ R := hc.bar_LB_le_bar_Rt hτ hs
    obtain ⟨x, hx⟩ := hsurj (π ⟨s, hsR⟩)
    have hnormZ : KK ≤ Subgroup.normalizer (Zc : Set (Mbar M Q)) :=
      sup_le_normalizer_of_commute hcomm
    have hfinj : Function.Injective (π.comp (Subgroup.inclusion hKR)) := by
      rw [injective_iff_map_eq_one]
      exact fun y hy => hinj y hy
    apply ne_bot_of_isComponent hZ
    rw [eq_bot_iff]
    intro z hz
    have hzR : z ∈ R := hZR hz
    have hu : s * z * s⁻¹ ∈ Zc' := mul_mem_conjSubgroup_iff.mpr hz
    have hv : (x : Mbar M Q) * z * (x : Mbar M Q)⁻¹ ∈ Zc :=
      (Subgroup.mem_normalizer_iff.mp (hnormZ x.2) z).mp hz
    have hKu : s * z * s⁻¹ ∈ KK := (le_sup_right : Zc' ≤ KK) hu
    have hKv : (x : Mbar M Q) * z * (x : Mbar M Q)⁻¹ ∈ KK := (le_sup_left : Zc ≤ KK) hv
    have hπ : (π.comp (Subgroup.inclusion hKR)) ⟨s * z * s⁻¹, hKu⟩ =
        (π.comp (Subgroup.inclusion hKR)) ⟨(x : Mbar M Q) * z * (x : Mbar M Q)⁻¹, hKv⟩ := by
      show π ⟨s * z * s⁻¹, hKR hKu⟩ = π ⟨(x : Mbar M Q) * z * (x : Mbar M Q)⁻¹, hKR hKv⟩
      have e1 : (⟨s * z * s⁻¹, hKR hKu⟩ : ↥R) = ⟨s, hsR⟩ * ⟨z, hzR⟩ * ⟨s, hsR⟩⁻¹ := rfl
      have e2 : (⟨(x : Mbar M Q) * z * (x : Mbar M Q)⁻¹, hKR hKv⟩ : ↥R) =
          ⟨(x : Mbar M Q), hKR x.2⟩ * ⟨z, hzR⟩ * ⟨(x : Mbar M Q), hKR x.2⟩⁻¹ := rfl
      rw [e1, e2, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hx]
    have heq := hfinj hπ
    have h1 : s * z * s⁻¹ = (x : Mbar M Q) * z * (x : Mbar M Q)⁻¹ := congrArg Subtype.val heq
    have hmem : s * z * s⁻¹ ∈ Zc ⊓ Zc' := ⟨h1 ▸ hv, hu⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have h2 : z = 1 := by
      have h3 : s⁻¹ * (s * z * s⁻¹) * s = z := by group
      rw [hmem] at h3
      simpa using h3.symm
    exact Subgroup.mem_bot.mpr h2
  ·
    obtain ⟨e⟩ := he
    haveI : IsSimpleGroup ↥(StatedSL 2 K) := isSimpleGroup_statedSL_two hSL2K
    haveI : IsSimpleGroup ↥KK := (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
    have hnormZ : KK ≤ Subgroup.normalizer (Zc : Set (Mbar M Q)) :=
      sup_le_normalizer_of_commute hcomm
    have hZn : (Zc.subgroupOf KK).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : Zc ≤ KK)).mpr hnormZ
    rcases hZn.eq_bot_or_eq_top with hb | ht
    · apply ne_bot_of_isComponent hZ
      rw [eq_bot_iff]
      intro z hz
      have : (⟨z, (le_sup_left : Zc ≤ KK) hz⟩ : ↥KK) ∈ Zc.subgroupOf KK := hz
      rw [hb, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · apply ne_bot_of_isComponent hZ'c
      rw [eq_bot_iff]
      intro z hz
      have hzZ : z ∈ Zc := by
        have : (⟨z, (le_sup_right : Zc' ≤ KK) hz⟩ : ↥KK) ∈ Zc.subgroupOf KK := by
          rw [ht]; exact Subgroup.mem_top _
        exact this
      have : z ∈ Zc ⊓ Zc' := ⟨hzZ, hz⟩
      rwa [hinf] at this


theorem Ctx.false_of_swap_third (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hCQ : ClassicalQuasisimpleStatement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hcs : CompSimple (Mbar M Q)) {Zc : Subgroup (Mbar M Q)} (hZ : IsComponent Zc)
    {s : Mbar M Q} (hs : s ∈ bar M Q (LB M Q B)) (hne : conjSubgroup s Zc ≠ Zc)
    {W : Subgroup (Mbar M Q)} (hW : IsComponent W) (hWZ : W ≠ Zc)
    (hWZ' : W ≠ conjSubgroup s Zc) : False := by
  have hΛ := hc.swapHyp hw hn hno
  have hZ'c : IsComponent (conjSubgroup s Zc) := isComponent_conjSubgroup s hZ
  obtain ⟨τb, hτbΛ, hτb1, hτZ, hτZ'⟩ : ∃ τb ∈ bar M Q (LB M Q B), τb ≠ 1 ∧
      (∀ x ∈ Zc, x * τb = τb * x) ∧ (∀ x ∈ conjSubgroup s Zc, x * τb = τb * x) := by
    by_cases hN : bar M Q (LB M Q B) ≤ Subgroup.normalizer (W : Set (Mbar M Q))
    · obtain ⟨d, hd⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
        (hc.inter_bar_LB_ne_bot h34 hw hn hno hgen hW.1 hN)
      refine ⟨d, d.2.1, fun h => hd (Subtype.ext h), fun x hx => ?_, fun x hx => ?_⟩
      · exact comm_of_ne_component hZ hW (Ne.symm hWZ) x hx d d.2.2
      · exact comm_of_ne_component hZ'c hW (Ne.symm hWZ') x hx d d.2.2
    · obtain ⟨s', hs'Λ, hs'W⟩ := Set.not_subset.mp hN
      have hne' : conjSubgroup s' W ≠ W := fun h => hs'W (conjSubgroup_eq_self_iff.mp h)
      obtain ⟨d, hdΛ, hd1, hdK⟩ := swap_exists_d hΛ hcs hW hs'Λ hne'
      have hW'c := isComponent_conjSubgroup s' hW
      have horb := swap_orbit hΛ hcs hZ hs hne
      have hinvs' : s'⁻¹ ∈ bar M Q (LB M Q B) := (bar M Q (LB M Q B)).inv_mem hs'Λ
      have hback : conjSubgroup s'⁻¹ (conjSubgroup s' W) = W := by
        rw [← conjSubgroup_mul_sec4, inv_mul_cancel, conjSubgroup_one_sec4]
      have hW'Z : conjSubgroup s' W ≠ Zc := by
        intro h
        rw [h] at hback
        rcases horb _ hinvs' with h1 | h1
        · exact hWZ (hback.symm.trans h1)
        · exact hWZ' (hback.symm.trans h1)
      have horb' : ∀ r ∈ bar M Q (LB M Q B), conjSubgroup r (conjSubgroup s Zc) = Zc ∨
          conjSubgroup r (conjSubgroup s Zc) = conjSubgroup s Zc := by
        intro r hr
        have hrs : r * s = s * r := hΛ.comm r hr s hs
        have hss : s * s = 1 := by rw [← pow_two]; exact hΛ.sq s hs
        have e : conjSubgroup r (conjSubgroup s Zc) = conjSubgroup s (conjSubgroup r Zc) := by
          rw [← conjSubgroup_mul_sec4, ← conjSubgroup_mul_sec4, hrs]
        rcases horb r hr with h1 | h1
        · right
          rw [e, h1]
        · left
          rw [e, h1, ← conjSubgroup_mul_sec4, hss, conjSubgroup_one_sec4]
      have hW'Z' : conjSubgroup s' W ≠ conjSubgroup s Zc := by
        intro h
        rw [h] at hback
        rcases horb' _ hinvs' with h1 | h1
        · exact hWZ (hback.symm.trans h1)
        · exact hWZ' (hback.symm.trans h1)
      have hcentZ : ∀ x ∈ Zc, d * x = x * d := by
        intro x hx
        have hle : W ⊔ conjSubgroup s' W ≤ Subgroup.centralizer ({x} : Set (Mbar M Q)) := by
          refine sup_le (fun w hw => ?_) (fun w hw => ?_)
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact comm_of_ne_component hW hZ hWZ w hw x hx
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact comm_of_ne_component hW'c hZ hW'Z w hw x hx
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle hdK)
      have hcentZ' : ∀ x ∈ conjSubgroup s Zc, d * x = x * d := by
        intro x hx
        have hle : W ⊔ conjSubgroup s' W ≤ Subgroup.centralizer ({x} : Set (Mbar M Q)) := by
          refine sup_le (fun w hw => ?_) (fun w hw => ?_)
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact comm_of_ne_component hW hZ'c hWZ' w hw x hx
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact comm_of_ne_component hW'c hZ'c hW'Z' w hw x hx
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle hdK)
      exact ⟨d, hdΛ, hd1, fun x hx => (hcentZ x hx).symm, fun x hx => (hcentZ' x hx).symm⟩
  obtain ⟨t, htLB, htQ, htmk⟩ := hc.exists_lift_ne_one hτbΛ hτb1
  exact hc.false_of_swap_centralized h34 h310 hCQ hw hn hno hgen hcs hZ hs hne htLB htQ
    (fun x hx => by rw [htmk]; exact hτZ x hx) (fun x hx => by rw [htmk]; exact hτZ' x hx)

end Swap

end CFSG.RankThree.GF2n.Stroth80
