module

public import CFSG.Milestones.ASVolI.C41.MS93RMain
public import CFSG.Milestones.ASVolI.C41.MS93RLin
public import CFSG.Milestones.ASVolI.C41.Grp
public import CFSG.Milestones.ASVolI.C41.Main
public import CFSG.Milestones.ASVolI.C4Kernel

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped commutatorElement Pointwise

section Core

set_option linter.unusedSectionVars false



theorem burnsideMS93R_clause_core
    {G : Type} [Group G] [Finite G]
    {H R M L V K : Subgroup G} (hyp : HypC41 H R M L V K)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hMS : IsMSPair (K ⊔ R) R)
    {n : ℕ} {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n) (hn : 1 < n)
    {V₁ : Subgroup G} (hV₁V : V₁ ≤ V) (hline : IsStabilizedLineOfNatural F R M K V₁)
    (h4 : C134CorrLocal.IsC134Case4Corr (K ⊔ R) R K) :
    c134CQ (K ⊔ R) K ≤ CFSG.Quasithin.centerOf (K ⊔ R) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G₀ := K ⊔ R with hG₀
  set P := pCoreOf 2 G₀ with hP
  have hQdef : c134Q G₀ K = ⁅P, K⁆ := rfl
  set Q := c134Q G₀ K with hQ
  have hKG₀ : K ≤ G₀ := le_sup_left
  have hRG₀ : R ≤ G₀ := le_sup_right
  have hG₀K : G₀ ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have hG₀P : G₀ ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₀
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀
  have hPG₀ : P ≤ G₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 G₀
  obtain ⟨hR2, hPR⟩ := MS93.isMSPair_isPGroup_and_pCoreOf_le hMS
  have hQKP : Q ≤ K ⊓ P := by
    rw [hQdef, Subgroup.commutator_le]
    intro p hp k hk
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hG₀K (hPG₀ hp)) k).mp hk) (K.inv_mem hk)
    · rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine P.mul_mem hp ?_
      have h1 := (Subgroup.mem_normalizer_iff.mp (hG₀P (hKG₀ hk)) p⁻¹).mp (P.inv_mem hp)
      simpa [mul_assoc] using h1
  have hQK : Q ≤ K := hQKP.trans inf_le_left
  have hQP : Q ≤ P := hQKP.trans inf_le_right
  have hG₀Q : G₀ ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]
    exact burnsideC41b_le_normalizer_commutator hG₀P hG₀K
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := hKG₀.trans hG₀Q
  have hPCQ : P ≤ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) :=
    (hPG₀.trans hG₀Q).trans (burnsideC41b_normalizer_le_normalizer_centralizer Q)
  have hKCQ : K ≤ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) :=
    hKQ.trans (burnsideC41b_normalizer_le_normalizer_centralizer Q)
  obtain ⟨W, hWle, αW, βW, hnat, hFline, -⟩ := hline
  have hnat₀ := hnat
  obtain ⟨hKW, hαs, hαk, hβs, hβk, hβe⟩ := hnat
  obtain ⟨-, W₀, hW₀, hV₁W₀⟩ := hFline
  have hβinj : Function.Injective βW := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hRV₁ : ∀ r ∈ R, ∀ x ∈ V₁, r * x = x * r := fun r hr x hx =>
    burnsideC41b_le_centralizer_V hyp.hyp r hr x (hV₁V hx)
  obtain ⟨w₀, hw₀, hw₀0⟩ : ∃ w ∈ W₀, w ≠ 0 := by
    have hne : W₀ ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hW₀
      exact absurd hW₀ (by norm_num)
    exact Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u₀, hu₀⟩ := hβs (Multiplicative.ofAdd w₀)
  have hu₀V : (u₀ : G) ∈ V₁ := (hV₁W₀ u₀).mpr (by rw [hu₀]; exact hw₀)
  have hu₀1 : βW u₀ ≠ 1 := by
    rw [hu₀]
    exact fun h => hw₀0 (ofAdd_eq_one.mp h)
  have hWne : W ≠ ⊥ := by
    intro h
    have h1 : (u₀ : G) ∈ (⊥ : Subgroup G) := by
      rw [← h]
      exact u₀.2
    exact hu₀1 (by rw [show u₀ = 1 from Subtype.ext (Subgroup.mem_bot.mp h1), map_one])
  have hRW : R ≤ Subgroup.normalizer (W : Set G) :=
    burnsideC41b_le_normalizer_W hnat₀ hRK hRV₁ hu₀V hu₀1
  have hOmK : K ≤ Subgroup.normalizer (omegaOneCenterOf P : Set G) :=
    (hKG₀.trans hG₀P).trans (normalizer_le_normalizer_omegaOneCenterOf P)
  have hWOm : W ≤ omegaOneCenterOf P :=
    hWle.trans ((Subgroup.le_normalizer_iff_commutator_le_left).mp hOmK)
  have hPW : ∀ p ∈ P, ∀ w ∈ W, p * w = w * p := fun p hp w hw =>
    mem_centralizer_of_mem_omegaOneCenterOf (hWOm hw) hp
  have hWQ : W ≤ Q := by
    rw [hQdef]
    exact hWle.trans (Subgroup.commutator_mono (omegaOneCenterOf_le P) le_rfl)
  have hCW : G₀ ⊓ Subgroup.centralizer (W : Set G) ≤ P :=
    burnsideC41b_inf_centralizer_le hnat₀ hRK hRW hR2
  let e : ↥W ≃* Multiplicative (Fin 3 → F) := MulEquiv.ofBijective βW ⟨hβinj, hβs⟩
  have hbound : P.relIndex R ≤ (2 ^ n) ^ 2 := by
    rw [← hF]
    exact burnsideC41b_relIndex_le_sq hF hαs e hKW (fun a u v h => hβe a u v h) W₀ hW₀
      (fun u => hV₁W₀ u) hRW hRK hRV₁ hR2
      (fun r hr hc => hCW (Subgroup.mem_inf.mpr ⟨hRG₀ hr, hc⟩))
  have hKcomp : K ∈ cComp G₀ := cComp_mem_of_le hyp.comp hKG₀
    (sup_le (le_of_mem_cComp hyp.comp) (hyp.hyp.le_M.trans hyp.hyp.le_H))
  have hset : (G₀ : Set G) = (K : Set G) * (R : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K R hRK
  have hRlin : R ≤ K ⊔ P :=
    burnsideMS93R_le_sup_of_line hF hαs e hKW (fun a u v h => hβe a u v h) W₀ hW₀
      (fun u => hV₁W₀ u) hRW hRK hRV₁ hR2
      (fun g hg hc => hCW (Subgroup.mem_inf.mpr ⟨hg, hc⟩))
  obtain ⟨T, hTR, hTchar, hTP, hTidx, hZ₀⟩ :=
    burnsideMS93R_exists hMS hKcomp hset hF ⟨hαs, hαk⟩ h4 (Or.inr hRlin)
      (fun h1 => absurd h1 (by omega))
  have hTG₀ : T ≤ G₀ := hTR.trans hRG₀
  have hTnP : T ≤ Subgroup.normalizer (P : Set G) := hTG₀.trans hG₀P
  have hKT_P : (K ⊔ T) ⊓ P ≤ pCoreOf 2 (K ⊔ T) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      (hP2.to_le inf_le_right)
    exact (le_inf Subgroup.le_normalizer ((sup_le hKG₀ hTG₀).trans hG₀P)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hidx : (2 ^ n) ^ 2 ≤ P.relIndex T := by
    rw [← hTidx, ← Subgroup.inf_relIndex_right P T]
    exact Subgroup.relIndex_le_of_le_left
      ((le_inf (inf_le_right.trans le_sup_right) inf_le_left).trans hKT_P)
      (Subgroup.index_ne_zero_of_finite (H := (P ⊓ T).subgroupOf T))
  have hRTP : R ≤ T ⊔ P := burnsideC41b_le_sup_of_relIndex hTR hPR hTnP hbound hidx
  have hRdec : ∀ r ∈ R, ∃ t ∈ T, ∃ x ∈ P, t * x = r := by
    intro r hr
    have hr' : r ∈ ((T ⊔ P : Subgroup G) : Set G) := hRTP hr
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T P hTnP] at hr'
    exact Set.mem_mul.mp hr'
  have hQT : Q ≤ T := fun q hq =>
    hTP (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (hQK hq), hQP hq⟩)
  have hZTQ : ∀ z ∈ CFSG.Quasithin.centerOf T, z ∈ Subgroup.centralizer (Q : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2) q (hQT hq)
  have hZTP : ∀ z ∈ CFSG.Quasithin.centerOf T, z ∈ P := by
    intro z hz
    refine hCW (Subgroup.mem_inf.mpr ⟨hTG₀ (Subgroup.mem_inf.mp hz).1, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hZTQ z hz)) w (hWQ hw)
  set Z := CFSG.Quasithin.centerOf Q with hZ
  set U := ⁅Z, K⁆ with hU
  have hKZ : K ≤ Subgroup.normalizer (Z : Set G) :=
    hKQ.trans (normalizer_le_normalizer_centerOf Q)
  have hUZ : U ≤ Z := (Subgroup.le_normalizer_iff_commutator_le_left).mp hKZ
  have hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2) x (Subgroup.mem_inf.mp hx).1
  have hKU : ∀ k ∈ K, ∀ y ∈ Z, k * y * k⁻¹ * y⁻¹ ∈ U := by
    intro k hk y hy
    have h1 := Subgroup.commutator_mem_commutator hk hy
    rw [Subgroup.commutator_comm] at h1
    exact h1
  have hcoc : ∀ a ∈ P, a ∈ Subgroup.centralizer (Q : Set G) → ∀ k ∈ K, ⁅a, k⁆ ∈ U := by
    intro a haP haC
    refine burnsideC41b_cocycle_mem (perfect_of_mem_cComp hyp.comp) hUZ hZab hKU
      (fun k => ⁅a, k⁆) ?_ ?_
    · intro k hk
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hQdef]
        exact Subgroup.commutator_mem_commutator haP hk
      · rw [commutatorElement_def, mul_assoc, mul_assoc]
        refine Subgroup.mul_mem _ haC ?_
        have h1 := (Subgroup.mem_normalizer_iff.mp (hKCQ hk) a⁻¹).mp (Subgroup.inv_mem _ haC)
        simpa [mul_assoc] using h1
    · intro k₁ _ k₂ _
      simp only [commutatorElement_def]
      group
  have hWU : W ≤ U := by
    refine hWle.trans ?_
    rw [Subgroup.commutator_le]
    intro a ha k hk
    refine hcoc a (omegaOneCenterOf_le P ha) ?_ k hk
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact mem_centralizer_of_mem_omegaOneCenterOf ha (hQP hq)
  obtain ⟨⟨n', F', iF', fF', αU, -, hαU, -, -, -, hUnat, -⟩, -⟩ := h4
  have hUW : U ≤ W := burnsideC41b_le_of_natural hαU.1 hUnat hWU hKW hWne
  have hUP : ∀ u ∈ U, ∀ p ∈ P, u * p = p * u := fun u hu p hp =>
    (hPW p hp u (hUW hu)).symm
  set N := ⁅CFSG.Quasithin.centerOf T, R⁆ with hN
  have hNR : N ≤ R := Subgroup.commutator_le_of_le (inf_le_left.trans hTR) le_rfl
  have hNchar : (N.subgroupOf R).Characteristic :=
    burnsideC41b_characteristic_commutator_center hTR hTchar
  have hRT : R ≤ Subgroup.normalizer (T : Set G) :=
    burnsideC41b_le_normalizer_of_characteristic hTR hTchar
  have hRN : R ≤ Subgroup.normalizer (N : Set G) :=
    burnsideC41b_le_normalizer_commutator (hRT.trans (normalizer_le_normalizer_centerOf T))
      Subgroup.le_normalizer
  have hKgen : ∀ k ∈ K, ∀ z ∈ CFSG.Quasithin.centerOf T, ∀ r ∈ R,
      k * ⁅z, r⁆ * k⁻¹ = ⁅z, r⁆ := by
    intro k hk z hz r hr
    obtain ⟨t, ht, x, hx, rfl⟩ := hRdec r hr
    have hzt : Commute z t :=
      ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2) t ht).symm
    have hx'P : t * x * t⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hTnP ht) x).mp hx
    have hcomm_eq : ⁅z, t * x⁆ = ⁅z, t * x * t⁻¹⁆ := by
      have hc : Commute z⁻¹ t := hzt.inv_left
      rw [commutatorElement_def, commutatorElement_def]
      calc z * (t * x) * z⁻¹ * (t * x)⁻¹ = z * t * x * (t⁻¹ * (t * z⁻¹)) * x⁻¹ * t⁻¹ := by
            group
        _ = z * t * x * (t⁻¹ * (z⁻¹ * t)) * x⁻¹ * t⁻¹ := by rw [← hc.eq]
        _ = z * (t * x * t⁻¹) * z⁻¹ * (t * x * t⁻¹)⁻¹ := by group
    rw [hcomm_eq]
    have hzP := hZTP z hz
    have hzQ := hZTQ z hz
    have hu : ⁅k, z⁆ ∈ U := by
      rw [← commutatorElement_inv]
      exact U.inv_mem (hcoc z hzP hzQ k hk)
    have hy : ⁅k, t * x * t⁻¹⁆ ∈ Q := by
      have h1 := Subgroup.commutator_mem_commutator hk hx'P
      rw [Subgroup.commutator_comm] at h1
      rw [hQdef]
      exact h1
    have hcz : ⁅z, t * x * t⁻¹⁆ ∈ Subgroup.centralizer (Q : Set G) := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine Subgroup.mul_mem _ hzQ ?_
      have h1 := (Subgroup.mem_normalizer_iff.mp (hPCQ hx'P) z⁻¹).mp (Subgroup.inv_mem _ hzQ)
      simpa [mul_assoc] using h1
    refine burnsideC41b_conj_commutator_eq (u := ⁅k, z⁆) (y := ⁅k, t * x * t⁻¹⁆) ?_ ?_
      (hUP _ hu z hzP) (hUP _ hu _ (hQP hy)) (hUP _ hu _ hx'P)
      ((Subgroup.mem_centralizer_iff.mp hzQ) _ hy).symm
      ((Subgroup.mem_centralizer_iff.mp hcz) _ hy).symm
    · rw [commutatorElement_def]
      group
    · rw [commutatorElement_def]
      group
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := by
    have hNC : N ≤ Subgroup.centralizer (K : Set G) := by
      rw [hN, Subgroup.commutator_le]
      intro z hz r hr
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := hKgen k hk z hz r hr
      calc k * ⁅z, r⁆ = k * ⁅z, r⁆ * k⁻¹ * k := by group
        _ = ⁅z, r⁆ * k := by rw [h1]
    exact (Subgroup.le_centralizer_iff.mp hNC).trans (Subgroup.centralizer_le_normalizer _)
  have hNbot : N = ⊥ := by
    by_contra hne
    exact hMS.2.2 N hNR hne hNchar (sup_le hKN hRN)
  intro z hz
  obtain ⟨hzQ, hzK⟩ := Subgroup.mem_inf.mp hz
  have hzG₀ : z ∈ G₀ := hKG₀ (hQK hzQ)
  have hzT : z ∈ CFSG.Quasithin.centerOf T := by
    refine Subgroup.mem_inf.mpr ⟨hQT hzQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hZ₀ hz)).2) t
      (Subgroup.mem_sup_right ht)
  have hzR : ∀ r ∈ R, r * z = z * r := by
    intro r hr
    have h1 : ⁅z, r⁆ ∈ N := Subgroup.commutator_mem_commutator hzT hr
    rw [hNbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hcen : G₀ ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le (fun k hk => ?_) (fun r hr => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hzK) k hk
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hzR r hr
  refine Subgroup.mem_inf.mpr ⟨hzG₀, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.mp (hcen hg)

theorem burnsideMS93R_clauseBridgeN
    : burnsideC41b_ClauseBridgeN := by
  intro G _ _ H R M L V K hyp hRK hC3 h4
  obtain ⟨n, F, iF, fF, hn, hF, -, hMS, -, -, -, hline⟩ := hC3
  obtain ⟨V₁, hV₁V, hV₁⟩ : ∃ V₁ : Subgroup G, V₁ ≤ V ∧ IsStabilizedLineOfNatural F R M K V₁ := by
    rcases hline with h | ⟨-, V₁, V₂, h1, -, rfl⟩
    · exact ⟨V, le_rfl, h⟩
    · exact ⟨V₁, le_sup_left, h1⟩
  have hclause := burnsideMS93R_clause_core hyp hRK hMS hF hn hV₁V hV₁ h4
  obtain ⟨⟨n', F', iF', fF', α, hF', hα, hE, h1⟩, hN⟩ := h4
  exact ⟨⟨n', F', iF', fF', α, hF', hα, hE, hclause, h1⟩, hN⟩

end Core

section Bridge

set_option linter.unusedSectionVars false



open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideMS93R_clauseBridge
    : burnsideC4h_C41Case4ClauseBridge := by
  intro G _ _ H R M L V K hyp hC3 h4
  have hRK : R ≤ Subgroup.normalizer (K : Set G) :=
    CFSG.Quasithin.C41Pf.le_normalizer CFSG.Quasithin.asc82Thm2_holds
      CFSG.Quasithin.H13.a3ForSQTK_holds.1 CFSG.Quasithin.H13.a3ForSQTK_holds.2.1
      (fun _ _ hX => CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hX)
      (CFSG.Quasithin.H13.VolI.asc129Statement_holds G) (CFSG.Quasithin.asc111Statement_holds G)
      (CFSG.Quasithin.asc19Statement_holds G) CFSG.Quasithin.C41Pf.c41KGBorel_holds
      hyp.hyp hyp.comp hyp.charTwo hyp.quasi hyp.not_le
  exact burnsideMS93R_clauseBridgeN G H R M L V K hyp hRK hC3 h4

end Bridge

end CFSG.ASVolI
