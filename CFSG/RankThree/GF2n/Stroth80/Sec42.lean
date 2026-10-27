module

public import CFSG.RankThree.GF2n.Stroth80.Sec4SwapCtx

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem pow_pred_ne_two_mul_sq {q n : ℕ} (hq : 4 ≤ q) (hn : 2 < n) :
    q ^ (n - 1) ≠ 2 * q ^ 2 := by
  intro h
  rcases Nat.lt_or_ge (n - 1) 3 with h3 | h3
  · have h2 : n - 1 = 2 := by omega
    rw [h2] at h
    have hpos : 0 < q ^ 2 := by positivity
    omega
  · have h4 : q ^ 3 ≤ q ^ (n - 1) := Nat.pow_le_pow_right (by omega) h3
    have h5 : 4 * q ^ 2 ≤ q ^ 3 := by
      have : q ^ 3 = q * q ^ 2 := by ring
      rw [this]
      exact Nat.mul_le_mul_right _ hq
    have hpos : 0 < q ^ 2 := by positivity
    omega

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.swap_range_le_bar_Rt (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (hcs : CompSimple (Mbar M Q)) {Y : Subgroup (Mbar M Q)}
    (hY : IsComponent Y) {s : Mbar M Q} (hs : s ∈ bar M Q (LB M Q B))
    (hne : conjSubgroup s Y ≠ Y) {t : M} (ht : (t : G) ∈ LB M Q B)
    (hts : (QuotientGroup.mk t : Mbar M Q) = s) :
    (swapChi Y s (swap_comm hY hne)).range ≤ bar M Q (Rt M (LB M Q B) (t : G)) := by
  have hΛ := hc.swapHyp hw hn hno
  haveI := swap_range_isSimpleGroup hΛ hcs hY hs hne
  have hsq : s ^ 2 = 1 := hΛ.sq s hs
  refine hc.le_bar_Rt_of_normalClosure ht
    (S := bar M Q (LB M Q B) ⊓ (swapChi Y s (swap_comm hY hne)).range) inf_le_left inf_le_right
    (normalClosure_subgroupOf_eq_top_of_forall inf_le_right fun N hN hSN =>
      le_of_inf_ne_bot_of_simple hN ?_) ?_
  · obtain ⟨d, hd, hd1⟩ := swap_Lam_inf_range_ne_bot hΛ hcs hY hs hne
    intro hbot
    have : d ∈ N ⊓ (swapChi Y s (swap_comm hY hne)).range := ⟨hSN hd, hd.2⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hd1 this
  · intro x hx
    rw [hts]
    obtain ⟨g, rfl⟩ := hx
    have h1 := swapChi_comm_t (swap_comm hY hne) hsq g
    calc swapChi Y s (swap_comm hY hne) g * s
        = (s * swapChi Y s (swap_comm hY hne) g * s⁻¹) * s := by rw [h1]
      _ = s * swapChi Y s (swap_comm hY hne) g := by group

theorem Ctx.exists_c_of_swap_omega (h34 : Stroth34Statement) (hOm : OmegaMinusFourSylowStatement)
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B))
    (hgen : GenByB M Q B) (hcs : CompSimple (Mbar M Q)) {Y : Subgroup (Mbar M Q)}
    (hY : IsComponent Y) {s : Mbar M Q} (hs : s ∈ bar M Q (LB M Q B))
    (hne : conjSubgroup s Y ≠ Y) {t : M} (htLB : (t : G) ∈ LB M Q B)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = Nat.card Z)
    (hq4 : 4 ≤ Nat.card K) {Gc : Type} [Group Gc] [Finite Gc] (R : Subgroup (Mbar M Q))
    (hR : R = bar M Q (Rt M (LB M Q B) (t : G))) (π : ↥R →* Gc)
    (hπk : ∀ x : ↥R, π x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN (t : G)))
    (hYhR : (swapChi Y s (swap_comm hY hne)).range ≤ R)
    (hYhN : (swapChi Y s (swap_comm hY hne)).range ⊓ bar M Q (hc.CN (t : G)) = ⊥)
    {b c : K} (hirr : ∀ x : K, x ^ 2 + b * x + c ≠ 0)
    (e1 : Gc ≃* ↥(StatedOmega (StatedQuadMinus 2 K b c)))
    (eYΩ : ↥Y ≃* ↥(StatedOmega (StatedQuadMinus 2 K b c))) :
    ∃ x : Mbar M Q, x ∈ bar M Q (LB M Q B) ∧ x ≠ 1 ∧ x ∈ bar M Q (hc.CN (t : G)) ∧
      conjSubgroup x Y = Y := by
  classical
  have hΛ := hc.swapHyp hw hn hno
  have hc12 := swap_comm hY hne
  have hinf := swap_inf_eq_bot hcs hY hne
  set Yh := (swapChi Y s hc12).range with hYh
  set Λ' := bar M Q (LB M Q B) with hΛ'
  have hΛR : Λ' ≤ R := hR ▸ hc.bar_LB_le_bar_Rt htLB
  obtain ⟨P, hDP⟩ := swap_Lam_inf_range_eq_map hΛ hcs hY hs hne
  obtain ⟨P'⟩ : Nonempty (Sylow 2 ↥(StatedOmega (StatedQuadMinus 2 K b c))) := inferInstance
  have hDcard : Nat.card ↥(Λ' ⊓ Yh) = Nat.card K ^ 2 := by
    rw [hDP, Subgroup.card_map_of_injective (swapChi_injective hc12 hinf),
      card_sylow_eq_of_mulEquiv eYΩ P P', hOm K hq4 b c hirr P']
  let f : ↥Yh →* Gc := π.comp (Subgroup.inclusion hYhR)
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 := (hπk ⟨(x : Mbar M Q), hYhR x.2⟩).mp hx
    have h2 : (x : Mbar M Q) ∈ Yh ⊓ bar M Q (hc.CN (t : G)) := ⟨x.2, h1⟩
    rw [hYhN, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  let T : Subgroup Gc := (Λ'.subgroupOf R).map π
  have hTp : IsPGroup 2 ↥T := by
    intro g
    obtain ⟨l, hl, hlg⟩ := g.2
    refine ⟨1, Subtype.ext ?_⟩
    show (g : Gc) ^ 2 ^ 1 = 1
    rw [pow_one, ← hlg, ← map_pow]
    have : l ^ 2 = 1 := Subtype.ext (by
      simpa using hΛ.sq (l : Mbar M Q) (Subgroup.mem_subgroupOf.mp hl))
    rw [this, map_one]
  obtain ⟨PG⟩ : Nonempty (Sylow 2 Gc) := inferInstance
  have hTcard : Nat.card ↥T ≤ Nat.card K ^ 2 := by
    have h1 := card_le_card_sylow hTp PG
    rw [card_sylow_eq_of_mulEquiv e1 PG P', hOm K hq4 b c hirr P'] at h1
    exact h1
  let D' : Subgroup Gc := ((Λ' ⊓ Yh).subgroupOf Yh).map f
  have hD'T : D' ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_subgroupOf.mp hx
    exact ⟨⟨(x : Mbar M Q), hYhR x.2⟩, Subgroup.mem_subgroupOf.mpr hx'.1, rfl⟩
  have hD'card : Nat.card ↥D' = Nat.card K ^ 2 := by
    rw [Subgroup.card_map_of_injective hfinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Λ' ⊓ Yh ≤ Yh)).toEquiv]
    exact hDcard
  have hDT : D' = T := Subgroup.eq_of_le_of_card_ge hD'T (by rw [hD'card]; exact hTcard)
  have hcover : ∀ l ∈ Λ', ∃ d ∈ Λ' ⊓ Yh, ∃ a ∈ Λ' ⊓ bar M Q (hc.CN (t : G)), l = d * a := by
    intro l hl
    have hlT : π ⟨l, hΛR hl⟩ ∈ T := ⟨⟨l, hΛR hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    rw [← hDT] at hlT
    obtain ⟨x, hx, hxl⟩ := hlT
    have hx' := Subgroup.mem_subgroupOf.mp hx
    refine ⟨(x : Mbar M Q), hx', (x : Mbar M Q)⁻¹ * l,
      ⟨Λ'.mul_mem (Λ'.inv_mem hx'.1) hl, ?_⟩, by group⟩
    have hxR : (x : Mbar M Q) ∈ R := hYhR x.2
    have hlR : l ∈ R := hΛR hl
    have h1 : π ((⟨(x : Mbar M Q), hxR⟩ : ↥R)⁻¹ * ⟨l, hlR⟩) = 1 := by
      rw [map_mul, map_inv]
      have : π ⟨(x : Mbar M Q), hxR⟩ = π ⟨l, hlR⟩ := hxl
      rw [this, inv_mul_cancel]
    exact (hπk _).mp h1
  have hDN : Λ' ⊓ Yh ≤ Λ' ⊓ Subgroup.normalizer (Y : Set (Mbar M Q)) := by
    refine le_inf inf_le_left (fun x hx => ?_)
    have hxK : x ∈ Y ⊔ conjSubgroup s Y := swapChi_range_le_sup hΛ hcs hY hs hne hx.2
    exact (sup_le_normalizer_of_commute hc12) hxK
  have hne2 : Nat.card ↥Λ' ≠ 2 * Nat.card ↥(Λ' ⊓ Yh) := by
    rw [hDcard, hΛ', hc.card_bar_LB_of_34 h34 hw hn hno hgen, ← hK]
    rw [hK]
    exact pow_pred_ne_two_mul_sq hc.hyp.q4 hn
  obtain ⟨x, ⟨hxA, hxN⟩, hx1⟩ := exists_ne_one_inf_of_card (Λ := Λ')
    (N := Λ' ⊓ Subgroup.normalizer (Y : Set (Mbar M Q))) (D := Λ' ⊓ Yh)
    (A := Λ' ⊓ bar M Q (hc.CN (t : G))) inf_le_left (swap_card_eq_two_mul hΛ hcs hY hs hne)
    hDN inf_le_left hcover hne2
  exact ⟨x, hxA.1, hx1, hxA.2, conjSubgroup_eq_self_iff.mpr hxN.2⟩

theorem Ctx.false_of_swap_component (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hCQ : ClassicalQuasisimpleStatement) (hO4 : ClassicalOrderFourStatement)
    (hOm : OmegaMinusFourSylowStatement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hcs : CompSimple (Mbar M Q)) {Y : Subgroup (Mbar M Q)} (hY : IsComponent Y)
    (hYSL : ¬ IsSLModel 2 (Nat.card Z) ↥Y) {s : Mbar M Q} (hs : s ∈ bar M Q (LB M Q B))
    (hne : conjSubgroup s Y ≠ Y) : False := by
  classical
  have hΛ := hc.swapHyp hw hn hno
  have hc12 := swap_comm hY hne
  have hinf := swap_inf_eq_bot hcs hY hne
  have hs1 : s ≠ 1 := fun h => hne (by rw [h, conjSubgroup_one_sec4])
  obtain ⟨t, htLB, htQ, htmk⟩ := hc.exists_lift_ne_one hs hs1
  haveI hYhs := swap_range_isSimpleGroup hΛ hcs hY hs hne
  have hYhnab := swap_range_nonabelian hΛ hcs hY hs hne
  have hYhR := hc.swap_range_le_bar_Rt hw hn hno hcs hY hs hne htLB htmk
  have hRne : Rt M (LB M Q B) (t : G) ≠ LB M Q B := by
    intro hRL
    obtain ⟨a, b, hab⟩ := hYhnab
    have hΛ' : (swapChi Y s hc12).range ≤ bar M Q (LB M Q B) := by
      have := hYhR
      rwa [hRL] at this
    exact hab (Subtype.ext (hΛ.comm _ (hΛ' a.2) _ (hΛ' b.2)))
  obtain ⟨K, hF, hFin, hK2, Gc, hGc, π, hK, hπs, hπk, hcl⟩ :=
    hc.classical_quotient h310 hw hn hno hgen htLB htQ hRne
  have hq4 : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
  haveI : CharP K 2 := hK2
  haveI : Finite Gc := Finite.of_surjective π hπs
  have hshape := hcl.shape hCQ hq4
  have hSL2K : CFSG.IsQuasisimple ↥(StatedSL 2 K) := (hCQ K hq4).1 2 le_rfl
  obtain ⟨d0, hd0, hd01⟩ := swap_Lam_inf_range_ne_bot hΛ hcs hY hs hne
  have hΛYh : bar M Q (LB M Q B) ⊓ (swapChi Y s hc12).range ≠ ⊥ := fun h =>
    hd01 (Subgroup.mem_bot.mp (h ▸ hd0))
  have hYhN := hc.inf_CN_eq_bot_of_simple h34 hw hn hno hgen htLB hYhR hYhnab hΛYh
  have hinj : ∀ x : ↥(swapChi Y s hc12).range,
      π ⟨(x : Mbar M Q), hYhR x.2⟩ = 1 → x = 1 := by
    intro x hx
    have h1 := (hπk ⟨(x : Mbar M Q), hYhR x.2⟩).mp hx
    have h2 : (x : Mbar M Q) ∈ (swapChi Y s hc12).range ⊓ bar M Q (hc.CN (t : G)) := ⟨x.2, h1⟩
    rw [hYhN, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hEn : (layer (Mbar M Q)).Normal := by
    haveI := CFSG.LocalCores.layer_characteristic (G := Mbar M Q)
    infer_instance
  have hYhE : (swapChi Y s hc12).range ≤ layer (Mbar M Q) :=
    (swapChi_range_le_sup hΛ hcs hY hs hne).trans
      (sup_le (CFSG.LocalCores.component_le_layer hY)
        (CFSG.LocalCores.component_le_layer (isComponent_conjSubgroup s hY)))
  have hXn : ∀ h ∈ bar M Q (Rt M (LB M Q B) (t : G)) ⊓ layer (Mbar M Q),
      ∀ x ∈ (swapChi Y s hc12).range, h * x * h⁻¹ ∈ (swapChi Y s hc12).range := by
    intro h hh x hx
    have hxK : x ∈ Y ⊔ conjSubgroup s Y := swapChi_range_le_sup hΛ hcs hY hs hne hx
    have h1 : h * x * h⁻¹ ∈ Y ⊔ conjSubgroup s Y :=
      layer_conj_mem_sup hY (isComponent_conjSubgroup s hY) hc12 hh.2 hxK
    refine swap_mem_range_of_comm_t hΛ hcs hY hs hne _ h1 ?_
    have hsh : h * s = s * h := by
      have := hc.bar_Rt_comm (t := t) h hh.1
      rwa [htmk] at this
    have hxs : s * x * s⁻¹ = x := by
      obtain ⟨g, rfl⟩ := hx
      exact swapChi_comm_t hc12 (hΛ.sq s hs) g
    calc s * (h * x * h⁻¹) * s⁻¹ = (s * h) * x * (s * h)⁻¹ := by group
      _ = (h * s) * x * (h * s)⁻¹ := by rw [hsh]
      _ = h * (s * x * s⁻¹) * h⁻¹ := by group
      _ = h * x * h⁻¹ := by rw [hxs]
  have hHn : ∀ r ∈ bar M Q (Rt M (LB M Q B) (t : G)),
      ∀ h ∈ bar M Q (Rt M (LB M Q B) (t : G)) ⊓ layer (Mbar M Q),
        r * h * r⁻¹ ∈ bar M Q (Rt M (LB M Q B) (t : G)) ⊓ layer (Mbar M Q) :=
    fun r hr h hh => ⟨(bar M Q (Rt M (LB M Q B) (t : G))).mul_mem
      ((bar M Q (Rt M (LB M Q B) (t : G))).mul_mem hr hh.1)
      ((bar M Q (Rt M (LB M Q B) (t : G))).inv_mem hr), hEn.conj_mem h hh.2 r⟩
  let eY : ↥Y ≃* ↥(swapChi Y s hc12).range :=
    MonoidHom.ofInjective (swapChi_injective hc12 hinf)
  have hns : ¬ Group.IsSolvable ↥(swapChi Y s hc12).range := by
    intro hs'
    haveI := hs'
    exact not_isSolvable_of_isQuasisimple hY.1
      (solvable_of_solvable_injective (f := eY.toMonoidHom) eY.injective)
  rcases subnormal_embedding_cases hSL2K (R := bar M Q (Rt M (LB M Q B) (t : G)))
    (H := bar M Q (Rt M (LB M Q B) (t : G)) ⊓ layer (Mbar M Q))
    (X := (swapChi Y s hc12).range) π hπs hshape (le_inf hYhR hYhE) inf_le_left hXn hHn hinj
    hns with ⟨-, hQSS⟩ | he'
  · rcases hQSS with ⟨hq, ⟨e⟩⟩ | he
    · have hY2 : ∀ y : ↥Y, (∃ k : ℕ, y ^ 2 ^ k = 1) → y ^ 2 = 1 := by
        rintro y ⟨k, hk⟩
        apply Subtype.ext
        have h0 : (y : Mbar M Q) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        simpa using swap_exp_two hΛ hcs hY hs hne (y : Mbar M Q) y.2 ⟨k, h0⟩
      let eGY : Gc ≃* ↥Y := e.symm.trans eY.symm
      have hno' : ∀ g : Gc, orderOf g ≠ 4 := fun g hg =>
        noOrderFour_of_exp_two hY2 (eGY g) (by rw [MulEquiv.orderOf_eq]; exact hg)
      rcases hcl.cases hCQ hO4 hq4 hno' with he1 | he1 | ⟨b, c, hirr, he1⟩
      · obtain ⟨e1⟩ := he1
        exact hYSL ⟨K, hF, hFin, hK, ⟨eGY.symm.trans e1⟩⟩
      · obtain ⟨e1⟩ := he1
        exact not_isSimpleGroup_of_prod hSL2K (e.trans e1)
      · obtain ⟨e1⟩ := he1
        obtain ⟨x, hxΛ, hx1, hxN, hxY⟩ := hc.exists_c_of_swap_omega h34 hOm hw hn hno hgen hcs hY
          hs hne htLB hK hq4 (bar M Q (Rt M (LB M Q B) (t : G))) rfl π hπk hYhR hYhN hirr e1
          (eGY.symm.trans e1)
        have hcYh : ∀ y ∈ (swapChi Y s hc12).range, x * y * x⁻¹ = y := by
          intro y hy
          have h1 : x * y * x⁻¹ ∈ (swapChi Y s hc12).range :=
            swap_normalizes_range hΛ hcs hY hs hne x hxΛ y hy
          have h2 : (x * y * x⁻¹) * y⁻¹ ∈ (swapChi Y s hc12).range ⊓
              bar M Q (hc.CN (t : G)) := by
            refine ⟨Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hy), ?_⟩
            have e2 : (x * y * x⁻¹) * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
            rw [e2]
            exact (bar M Q (hc.CN (t : G))).mul_mem hxN
              (hc.bar_CN_conj_mem htLB (hYhR hy) ((bar M Q (hc.CN (t : G))).inv_mem hxN))
          rw [hYhN, Subgroup.mem_bot, mul_inv_eq_one] at h2
          exact h2
        obtain ⟨hcg, hcg'⟩ := swap_centralizes_of_centralizes_range hΛ hcs hY hs hne hxΛ hxY hcYh
        obtain ⟨τ, hτLB, hτQ, hτmk⟩ := hc.exists_lift_ne_one hxΛ hx1
        refine hc.false_of_swap_centralized h34 h310 hCQ hw hn hno hgen hcs hY hs hne hτLB hτQ
          ?_ ?_
        · intro g hg
          rw [hτmk]
          calc g * x = (x * g * x⁻¹) * x := by rw [hcg g hg]
            _ = x * g := by group
        · intro g hg
          rw [hτmk]
          calc g * x = (x * g * x⁻¹) * x := by rw [hcg' g hg]
            _ = x * g := by group
    · obtain ⟨e⟩ := he
      exact not_isSimpleGroup_of_prod hSL2K e
  · obtain ⟨e'⟩ := he'
    exact hYSL ⟨K, hF, hFin, hK, ⟨eY.trans e'⟩⟩

section Main

theorem stroth42_of_41ii (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h41ii : Stroth41iiStatement) (h44 : Stroth44Statement)
    (hCQ : ClassicalQuasisimpleStatement) (hO4 : ClassicalOrderFourStatement)
    (hOm : OmegaMinusFourSylowStatement) : Stroth42Statement := by
  intro G _ _ M Q Z B hN hc n hw hn hno hgen hE hnoSL
  classical
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  have hSL2 : ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card Z →
      CFSG.IsQuasisimple ↥(StatedSL 2 K) := by
    intro K _ _ hK
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hZ2)
    exact (hCQ K (by rw [hK]; exact hq4)).1 2 le_rfl
  have hqSL : ∀ X : Subgroup (Mbar M Q), IsSLModel 2 (Nat.card Z) ↥X → CFSG.IsQuasisimple ↥X := by
    rintro X ⟨K, hF, hFin, hK, ⟨e⟩⟩
    exact isQuasisimple_of_mulEquiv' e.symm (hSL2 K hK)
  have hcs := hc.compSimple h34 h44 hw hn hno hgen
  have hnoComp : ∀ C : Subgroup (Mbar M Q), IsComponent C →
      ¬ IsSLModel 2 (Nat.card Z) ↥C := fun C hC hCSL =>
    hnoSL ⟨C, CFSG.LocalCores.component_le_layer hC,
      (CFSG.LocalCores.components_normal_in_layer hC).2, hCSL⟩
  have hclaim : ∀ C : Subgroup (Mbar M Q), IsComponent C → ∀ s ∈ bar M Q (LB M Q B),
      conjSubgroup s C = C := by
    intro C hC s hs
    by_contra hne
    exact hc.false_of_swap_component h34 h310 hCQ hO4 hOm hw hn hno hgen hcs hC (hnoComp C hC)
      hs hne
  have hQS : ∀ C : Subgroup (Mbar M Q), IsComponent C →
      IsQSNormalIn C (bar M Q (Lgen M (LB M Q B))) := by
    intro C hC
    have hle : C ≤ bar M Q (Lgen M (LB M Q B)) :=
      component_le_of_not_centralizes hc.normal_bar_Lgen (hc.noComm h34 hw hn hno hgen) hC
    have hnorm : bar M Q (Lgen M (LB M Q B)) ≤ Subgroup.normalizer (C : Set (Mbar M Q)) :=
      hc.bar_Lgen_le_normalizer_of_forall fun g s hs =>
        conjSubgroup_eq_self_iff.mp (hclaim _ (isComponent_conjSubgroup g hC) s hs)
    exact ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnorm, hC.1⟩
  have hno' : ¬ ∃ X : Subgroup (Mbar M Q), X ≤ bar M Q (Lgen M (LB M Q B)) ∧
      (X.subgroupOf (bar M Q (Lgen M (LB M Q B)))).Normal ∧ IsSLModel 2 (Nat.card Z) ↥X := by
    rintro ⟨X, hXM, hXn, hXSL⟩
    exact hnoComp X ⟨hqSL X hXSL, Subgroup.IsSubnormal.trans hXM hXn.isSubnormal
      hc.normal_bar_Lgen.isSubnormal⟩ hXSL
  have huniq : ∀ C₁ C₂ : Subgroup (Mbar M Q), IsComponent C₁ → IsComponent C₂ → C₁ = C₂ :=
    fun C₁ C₂ h₁ h₂ => h41ii G M Q Z B hc n hw hn hno hgen hno' C₁ C₂ (hQS C₁ h₁) (hQS C₂ h₂)
  obtain ⟨C₀, hC₀⟩ : ∃ C : Subgroup (Mbar M Q), IsComponent C := by
    by_contra hcon
    push Not at hcon
    exact hE (CFSG.LocalCores.layer_eq_bot_of_forall hcon)
  have hlayer : layer (Mbar M Q) = C₀ :=
    le_antisymm (sSup_le fun C hC => (huniq C C₀ hC hC₀).le)
      (CFSG.LocalCores.component_le_layer hC₀)
  exact isQuasisimple_of_mulEquiv' (MulEquiv.subgroupCongr hlayer.symm) hC₀.1

end Main

end CFSG.RankThree.GF2n.Stroth80
