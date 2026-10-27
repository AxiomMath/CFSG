module

public import CFSG.Quasithin.Vol2.Ch12Sec6L13c
public import CFSG.Quasithin.Vol2.Ch12Sec6VvKey

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126VK

theorem pv_add_pv : ∀ a b c : Fin 8, a ≠ b → a ≠ c → b ≠ c →
    B5FinS8.pv a b + B5FinS8.pv a c = B5FinS8.pv b c := by
  decide

theorem exists_third : ∀ a b : Fin 8, a ∈ six → b ∈ six → ∃ c ∈ six, c ≠ a ∧ c ≠ b := by
  decide

theorem vSix_add_vSix : vSix + vSix = 0 := by
  decide

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem eq_Vv_of_le (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {D : Subgroup G}
    (hDV : D ≤ Vv L V v) (hDN : Lv L v ≤ Subgroup.normalizer (D : Set G)) {x : G} (hxD : x ∈ D)
    {l : G} (hl : l ∈ Lv L v) (hxl : l * x * l⁻¹ ≠ x) : D = Vv L V v := by
  classical
  have hconj : ∀ {y : G}, y ∈ D → ∀ {m : G}, m ∈ Lv L v → m * y * m⁻¹ ∈ D :=
    fun hy _ hm => (Subgroup.mem_normalizer_iff.1 (hDN hm) _).1 hy
  have hxv := hDV hxD
  have hlL : l ∈ L := Lv_le_L L v hl
  have hΔ : ∃ u ∈ D, u ∈ Delta F v := by
    rcases coordV_cases h1222 hH hv hβ hxv with h0 | hd | hq | h6
    · exfalso
      have hx1 : x = 1 := coordV_injOn h1222 hH hv hβ hxv (Vv L V v).one_mem
        (h0.trans (coordV_one h1222 hH hv hβ).symm)
      exact hxl (by rw [hx1]; group)
    · exact ⟨x, hxD, (mem_Delta_iff h1222 hH hv hβ).2 ⟨hxv, hd⟩⟩
    · obtain ⟨d, hd, hdx⟩ := Finset.mem_image.1 hq
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := (mem_duads_iff _).1 hd
      obtain ⟨c, hc, hca, hcb⟩ := exists_third a b ha hb
      obtain ⟨τ, hτ, hτa, hτb⟩ := exists_A6s_pair ha hb hab ha hc (Ne.symm hca)
      obtain ⟨m, hm, hmτ⟩ := exists_Lv_of_A6s h1222 F hH hv hβ τ hτ
      have hmx : (m : G) * x * (m : G)⁻¹ ∈ D := hconj hxD hm
      have hmxv := hDV hmx
      refine ⟨x * ((m : G) * x * (m : G)⁻¹), D.mul_mem hxD hmx,
        (mem_Delta_iff h1222 hH hv hβ).2 ⟨(Vv L V v).mul_mem hxv hmxv, ?_⟩⟩
      rw [coordV_mul h1222 hH hv hβ hxv hmxv, coordV_conj h1222 hH hv hβ hm hxv, ← hdx, hmτ]
      have e : (fun i => (B5FinS8.pv a b + vSix) (τ⁻¹ i)) = B5FinS8.pv (τ a) (τ b) + vSix := by
        funext i
        have h1 := congrFun (pv_comp_inv τ a b) i
        have h2 := congrFun (vSix_comp_inv hτ) i
        simp only [Pi.add_apply] at h1 h2 ⊢
        rw [h1, h2]
      rw [e, hτa, hτb]
      have e2 : B5FinS8.pv a b + vSix + (B5FinS8.pv a c + vSix) = B5FinS8.pv b c := by
        rw [show B5FinS8.pv a b + vSix + (B5FinS8.pv a c + vSix) =
            B5FinS8.pv a b + B5FinS8.pv a c + (vSix + vSix) by abel,
          pv_add_pv a b c hab (Ne.symm hca) (Ne.symm hcb), vSix_add_vSix, add_zero]
      rw [e2]
      exact pv_mem_duads hb hc (Ne.symm hcb)
    · exfalso
      apply hxl
      have hσ : psiP F hH ⟨l, hlL⟩ ∈ A6s :=
        psiP_mem_A6s h1222 F hH hv hβ (show (⟨l, hlL⟩ : ↥L) ∈ (Lv L v).subgroupOf L from hl)
      have hlxv : l * x * l⁻¹ ∈ Vv L V v :=
        (Subgroup.mem_normalizer_iff.1 (Lv_le_normalizer_Vv hH v hl) x).1 hxv
      refine coordV_injOn h1222 hH hv hβ hlxv hxv ?_
      have h1 := coordV_conj h1222 hH hv hβ (l := ⟨l, hlL⟩) hl hxv
      simp only at h1
      rw [h1, h6]
      exact vSix_comp_inv hσ
  obtain ⟨u, huD, huΔ⟩ := hΔ
  have hΔD : Delta F v ⊆ D := by
    intro u' hu'
    obtain ⟨m, hm, hmu⟩ := exists_Lv_conj_eq h1222 hH hv hβ huΔ hu'
    rw [← hmu]
    exact hconj huD hm
  exact le_antisymm hDV ((Vv_le_closure_Delta h1222 hH hv hβ).trans
    ((Subgroup.closure_le _).2 hΔD))

theorem comm_omega_ne_bot (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {R : Subgroup G}
    (hR2 : IsPGroup 2 R) (hRP : R ≤ Subgroup.normalizer (pCoreOf 2 (Lv L v) : Set G))
    (hRc : ∀ r ∈ R, ∀ l ∈ Lv L v, l * r * l⁻¹ * r⁻¹ ∈ pCoreOf 2 (Lv L v))
    (hPR : pCoreOf 2 (Lv L v) ≤ R) :
    ⁅quasithinOmegaOneCenter R, Lv L v⁆ ≠ ⊥ := by
  intro hbot
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 (Lv L v) with hPdef
  set W := quasithinOmegaOneCenter P with hWdef
  obtain ⟨-, hVe⟩ := V_facts h1222 hH
  have hP2 : IsPGroup 2 P := pCoreOf_isPGroup 2 _
  have hWP : W ≤ P := fun w hw => (mem_quasithinOmegaOneCenter_iff.1 hw).1
  have hW2 : IsPGroup 2 W := hP2.to_le hWP
  have hLP : Lv L v ≤ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 _
  have hLW : Lv L v ≤ Subgroup.normalizer (W : Set G) :=
    hLP.trans (normalizer_le_normalizer_omega P)
  have hRW : R ≤ Subgroup.normalizer (W : Set G) := hRP.trans (normalizer_le_normalizer_omega P)
  have hPV := pCoreOf_Lv_le h1222 F hH hv hβ
  have hVW : Vv L V v ≤ W := by
    intro x hx
    have hxV := Vv_le_V hH v hx
    refine mem_quasithinOmegaOneCenter_iff.2 ⟨Vv_le_pCoreOf h1222 hH hv hx, ?_, hVe.2 x hxV⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.1 (hPV hp) x hxV).symm
  have hodd : ∀ c ∈ Lv L v, Odd (orderOf c) → c ∈ Subgroup.centralizer (W : Set G) := by
    intro c hc hco
    have hcW : Subgroup.zpowers c ≤ Subgroup.normalizer (W : Set G) :=
      Subgroup.zpowers_le.2 (hLW hc)
    have hcL : Subgroup.zpowers c ≤ Lv L v := Subgroup.zpowers_le.2 hc
    let α : ↥(Subgroup.zpowers c) →* MulAut ↥W :=
      W.normalizerMonoidHom.comp (Subgroup.inclusion hcW)
    let β : ↥R →* MulAut ↥W := W.normalizerMonoidHom.comp (Subgroup.inclusion hRW)
    have hα : ∀ (a : ↥(Subgroup.zpowers c)) (w : ↥W),
        ((α a w : ↥W) : G) = (a : G) * w * (a : G)⁻¹ := fun _ _ => rfl
    have hβ' : ∀ (b : ↥R) (w : ↥W), ((β b w : ↥W) : G) = (b : G) * w * (b : G)⁻¹ :=
      fun _ _ => rfl
    have hA : ¬ 2 ∣ Nat.card ↥(Subgroup.zpowers c) := by
      rw [Nat.card_zpowers]
      exact Nat.odd_iff.mp hco |> fun h => by omega
    have hcomm : ∀ a b, α a * β b = β b * α a := by
      intro a b
      ext w
      simp only [MulAut.mul_apply]
      rw [hα, hβ', hβ', hα]
      have ho : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ P := hRc b b.2 a (hcL a.2)
      have hwb : (b : G) * ((a : G) * w * (a : G)⁻¹) * (b : G)⁻¹ ∈ W := by
        have h1 : (a : G) * w * (a : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 (hcW a.2) _).1 w.2
        exact (Subgroup.mem_normalizer_iff.1 (hRW b.2) _).1 h1
      have hoc := (mem_quasithinOmegaOneCenter_iff.1 hwb).2.1
      have h2 := Subgroup.mem_centralizer_iff.1 hoc _ ho
      set o := (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ with hodef
      calc (a : G) * ((b : G) * w * (b : G)⁻¹) * (a : G)⁻¹
          = o * ((b : G) * ((a : G) * w * (a : G)⁻¹) * (b : G)⁻¹) * o⁻¹ := by
            rw [hodef]; group
        _ = ((b : G) * ((a : G) * w * (a : G)⁻¹) * (b : G)⁻¹) * o * o⁻¹ := by rw [h2]
        _ = (b : G) * ((a : G) * w * (a : G)⁻¹) * (b : G)⁻¹ := by group
    have hfix : ∀ a w, (∀ b, β b w = w) → α a w = w := by
      intro a w hw
      have hwR : (w : G) ∈ quasithinOmegaOneCenter R := by
        refine mem_quasithinOmegaOneCenter_iff.2 ⟨hPR (hWP w.2), ?_,
          (mem_quasithinOmegaOneCenter_iff.1 w.2).2.2⟩
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have h1 := congrArg Subtype.val (hw ⟨r, hr⟩)
        rw [hβ'] at h1
        calc r * w = r * w * r⁻¹ * r := by group
          _ = w * r := by rw [h1]
      have h1 : ⁅(w : G), (a : G)⁆ ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact Subgroup.commutator_mem_commutator hwR (hcL a.2)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      apply Subtype.ext
      rw [hα]
      calc (a : G) * w * (a : G)⁻¹ = w * a * (a : G)⁻¹ := by rw [h1]
        _ = w := by group
    have h := CFSG.GroupTheory.thompson_A_times_B hW2 hA hR2 α β hcomm hfix
      ⟨c, Subgroup.mem_zpowers c⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : G)) h
    simp only [MulAut.one_apply] at h1
    rw [hα] at h1
    calc w * c = c * w * c⁻¹ * c := by rw [h1]
      _ = c * w := by group
  have hLperf : Group.IsPerfect ↥(Lv L v) := Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
  have hLC : Lv L v ≤ Subgroup.centralizer (W : Set G) :=
    (perfect_le_oTwoUpper le_rfl hLperf).trans
      ((Subgroup.closure_le _).2 fun c hc => hodd c hc.1 hc.2)
  have hcomm : ⁅Vv L V v, Lv L v⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.1 (hLC hl) x (hVW hx)).symm
  exact Vv_ne_bot h1222 F hH hv hβ (le_bot_iff.1 (hcomm ▸ Vv_le_comm h1222 hH hv))

end S126VK

theorem stmt12_6_13_three_of (h1222 : Stmt12_2_2) (h1261 : Lemma12_6_1)
    (hD3 : Lemma12_6_6_9) : Stmt12_6_13_three := by
  intro G _ _ T L V _ F v Kv S hC
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hTvL : Tv T v ≤ Subgroup.normalizer (Lv L v : Set G) := fun _t ht =>
    normalizer_le_normalizer_perfectCore _ (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hH.hyp.normalizes ht.1, Subgroup.le_normalizer ht.2⟩)
  have hTvV : Tv T v ≤ Subgroup.normalizer (Vv L V v : Set G) :=
    MS93.le_normalizer_commutator_of (inf_le_left.trans hTV) hTvL
  set R := centralizerSection S (Lv L v) (pCoreOf 2 (Lv L v)) with hRdef
  by_cases hJ : thompsonJ (Tv T v) ≤ Qv T V
  · obtain ⟨hS, -⟩ := (hD3 G T L V F v Kv S hC).2.2.2.1 hJ
    intro x hx
    exact hTvV (hS ▸ hx.1)
  · obtain ⟨hJT, -⟩ := (hD3 G T L V F v Kv S hC).2.2.2.2 hJ
    have hQN : Lv L v ≤ Subgroup.normalizer (Qv T V : Set G) :=
      ((Lv_le_L L v).trans le_sup_left).trans (LT_le_normalizer_Qv h1222 hH)
    have hPQ : pCoreOf 2 (Lv L v) ≤ Qv T V := by
      rw [Qv_eq h1222 hH]
      exact le_inf ((pCoreOf_le 2 _).trans ((Lv_le_L L v).trans le_sup_left))
        (pCoreOf_Lv_le h1222 F hH hv hβ)
    have hQR : Qv T V ≤ R := by
      intro x hx
      have hxTv : x ∈ Tv T v := ⟨hx.1, Qv_le_Gv hv hx⟩
      have hxL := hTvL hxTv
      refine ⟨hC.tv_le hxTv, hxL, normalizer_le_normalizer_pCoreOf 2 _ hxL, fun l hl => ?_⟩
      have hmem : l * x * l⁻¹ * x⁻¹ ∈ Lv L v ⊓ Qv T V := by
        refine ⟨?_, ?_⟩
        · have h1 : x * l⁻¹ * x⁻¹ ∈ Lv L v :=
            (Subgroup.mem_normalizer_iff.1 hxL _).1 ((Lv L v).inv_mem hl)
          have e : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by group
          rw [e]
          exact (Lv L v).mul_mem hl h1
        · exact (Qv T V).mul_mem ((Subgroup.mem_normalizer_iff.1 (hQN hl) x).1 hx)
            ((Qv T V).inv_mem hx)
      have hQ2 : IsPGroup 2 (Qv T V) := hH.hyp.sylow.1.to_le inf_le_left
      have hle : Lv L v ⊓ Qv T V ≤ pCoreOf 2 (Lv L v) :=
        le_pCoreOf_of_le_normalizer 2 inf_le_left
          (fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
            ⟨Subgroup.le_normalizer hy, hQN hy⟩) (hQ2.to_le inf_le_right)
      exact hle hmem
    have hRc : ∀ r ∈ R, ∀ l ∈ Lv L v, l * r * l⁻¹ * r⁻¹ ∈ pCoreOf 2 (Lv L v) :=
      fun r hr l hl => hr.2.2.2 l hl
    have hRL : ∀ r ∈ R, ∀ l ∈ Lv L v, r * l * r⁻¹ * l⁻¹ ∈ Qv T V := by
      intro r hr l hl
      have h1 := hRc r hr l⁻¹ ((Lv L v).inv_mem hl)
      have h2 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hl) _).1 h1
      have e : r * l * r⁻¹ * l⁻¹ = l * (l⁻¹ * r * l⁻¹⁻¹ * r⁻¹) * l⁻¹ := by group
      rw [e]
      exact hPQ h2
    have hle := S126VK.comm_omega_le_Vv h1222 h1261 F hH hJT v hQR hRL
    have hR2 : IsPGroup 2 R := hC.sylow.2.1.to_le fun x hx => hx.1
    have hRN : R ≤ Subgroup.normalizer (Lv L v : Set G) := fun x hx => hx.2.1
    have hne := S126VK.comm_omega_ne_bot h1222 hH hv hβ hR2 (fun x hx => hx.2.2.1) hRc
      (hPQ.trans hQR)
    set D : Subgroup G := ⁅quasithinOmegaOneCenter R, Lv L v⁆ with hD
    have hLR := S126VK.le_normalizer_of_comm_le h1222 hH v hQR hRL
    have hLΩ : Lv L v ≤ Subgroup.normalizer (quasithinOmegaOneCenter R : Set G) :=
      hLR.trans (S126VK.normalizer_le_normalizer_omega R)
    have hLD : Lv L v ≤ Subgroup.normalizer (D : Set G) :=
      MS93.le_normalizer_commutator_of hLΩ Subgroup.le_normalizer
    have hRD : R ≤ Subgroup.normalizer (D : Set G) :=
      MS93.le_normalizer_commutator_of
        (Subgroup.le_normalizer.trans (S126VK.normalizer_le_normalizer_omega R)) hRN
    obtain ⟨x, hxD, l, hl, hxl⟩ : ∃ x ∈ D, ∃ l ∈ Lv L v, l * x * l⁻¹ ≠ x := by
      by_contra hcon
      push Not at hcon
      apply hne
      have hLp : ⁅Lv L v, Lv L v⁆ = Lv L v := perfectCore_perfect _
      rw [hD, MS93.S4A.P442.commutator_eq_commutator_commutator hLp hLΩ
        (S126VK.commutator_omega_eq_bot _), Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := hcon y hy l hl
      calc l * y = l * y * l⁻¹ * l := by group
        _ = y * l := by rw [h1]
    have heq := S126VK.eq_Vv_of_le h1222 hH hv hβ hle hLD hxD hl hxl
    rw [← heq]
    exact hRD

end CFSG.Quasithin.H13
