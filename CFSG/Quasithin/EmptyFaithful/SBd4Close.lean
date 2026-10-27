module

public import CFSG.Quasithin.EmptyFaithful.S153G23
public import CFSG.Quasithin.EmptyFaithful.SzN3Lin2
public import CFSG.Quasithin.Background.C1PackS15348

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def L3YLLabel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsLnTwoQuot L 3 → Concl15312Two Yp L →
      ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥ → Yp = Y153 Mc M →
      (YL153 Yp L = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ∧
          YC153 Yp L = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₂ : Set G))) ∨
        (YL153 Yp L = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₂ : Set G)) ∧
          YC153 Yp L = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)))

@[expose] def L3ClosingQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsLnTwoQuot L 3 → Concl15312Two Yp L →
      ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥ → Yp = Y153 Mc M →
      Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) →
      ∀ t' ∈ T, t' ∉ Sgp153 T V₁ → B6.conjSub t' (YL153 Yp L) = YC153 Yp L →
        ⁅B6.conjSub t' ⁅pCoreOf 2 (L ⊔ R153 T V₁ Yp), L⁆, L⁆ ≤ ⁅pCoreOf 2 (L ⊔ R153 T V₁ Yp), L⁆

namespace SBd4

section Generic

variable {G : Type} [Group G]

theorem mem_normalizer_commutator' {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (A : Set G) → g ∈ Subgroup.normalizer (B : Set G) →
      ∀ x ∈ ⁅A, B⁆, g * x * g⁻¹ ∈ ⁅A, B⁆ := by
    intro g hA hB x hx
    have hle : ⁅A, B⁆ ≤ (⁅A, B⁆).comap (MulAut.conj g).toMonoidHom := by
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      show g * ⁅a, b⁆ * g⁻¹ ∈ ⁅A, B⁆
      have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hA a).mp ha)
        ((Subgroup.mem_normalizer_iff.mp hB b).mp hb)
    exact hle hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hA hB x hx, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hA) (inv_mem hB) _ hx
  simpa [mul_assoc] using this

theorem mem_normalizer_conjSub {g t' : G} {Q : Subgroup G}
    (h : t'⁻¹ * g * t' ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer ((B6.conjSub t' Q : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [B6.mem_conjSub, B6.mem_conjSub]
  have h1 := Subgroup.mem_normalizer_iff.mp h (t'⁻¹ * x * t')
  have e : t'⁻¹ * g * t' * (t'⁻¹ * x * t') * (t'⁻¹ * g * t')⁻¹ = t'⁻¹ * (g * x * g⁻¹) * t' := by
    group
  rw [e] at h1
  exact h1

theorem isPGroup_conjSub {Q : Subgroup G} (hQ : IsPGroup 2 Q) (g : G) :
    IsPGroup 2 ↥(B6.conjSub g Q) := by
  intro x
  obtain ⟨k, hk⟩ := hQ ⟨g⁻¹ * (x : G) * g, B6.mem_conjSub.mp x.2⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (g⁻¹ * (x : G) * g) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have e : (x : G) ^ 2 ^ k = g * (g⁻¹ * (x : G) * g) ^ 2 ^ k * g⁻¹ := by
    rw [← conj_pow]
    group
  simp [e, h1]

theorem closing_core [Finite G] {Q L S T Y : Subgroup G} {t' : G} (hQL : Q ≤ L) (hQ2 : IsPGroup 2 Q)
    (hQ0 : Q ≠ ⊥) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hSQ : S ≤ Subgroup.normalizer (Q : Set G)) (hYQ : Y ≤ Subgroup.normalizer (Q : Set G))
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (ht'T : t' ∈ T) (ht'S : t' ∉ S) (hprod : ∀ a ∈ T, ∀ b ∈ T, a ∉ S → b ∉ S → a * b ∈ S)
    (hcomm : ⁅B6.conjSub t' Q, L⁆ ≤ Q) :
    ∃ W : Subgroup G, W ≠ ⊥ ∧ IsPGroup 2 W ∧ L ≤ Subgroup.normalizer (W : Set G) ∧
      T ≤ Subgroup.normalizer (W : Set G) ∧ Y ≤ Subgroup.normalizer (W : Set G) := by
  classical
  set Q' : Subgroup G := B6.conjSub t' Q with hQ'
  refine ⟨Q ⊔ Q', ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hQ0 (eq_bot_iff.mpr (h ▸ le_sup_left))
  ·
    have hcQ : ∀ q' ∈ Q', ∀ x ∈ Q, q' * x * q'⁻¹ ∈ Q := by
      intro q' hq' x hx
      have h1 : ⁅q', x⁆ ∈ Q := hcomm (Subgroup.commutator_mem_commutator hq' (hQL hx))
      have e : q' * x * q'⁻¹ = ⁅q', x⁆ * x := by simp only [commutatorElement_def]; group
      rw [e]
      exact Q.mul_mem h1 hx
    have hQ'N : Q' ≤ Subgroup.normalizer (Q : Set G) := fun q' hq' =>
      B6.mem_normalizer_of_forall_mem (hcQ q' hq') (fun x hx => by
        have := hcQ q'⁻¹ (Q'.inv_mem hq') x hx
        simpa using this)
    have hQ'2 : IsPGroup 2 Q' := isPGroup_conjSub hQ2 t'
    intro x
    obtain ⟨k, hk⟩ := C1Pack153.exists_pow_mem_of_mem_sup_two hQ'2 hQ'N x.2
    obtain ⟨j, hj⟩ := hQ2 ⟨(x : G) ^ 2 ^ k, hk⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have h1 : ((x : G) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    simpa [pow_add, pow_mul] using h1
  ·
    have hcL : ∀ l ∈ L, ∀ x ∈ Q ⊔ Q', l * x * l⁻¹ ∈ Q ⊔ Q' := by
      intro l hl x hx
      have hle : Q ⊔ Q' ≤ (Q ⊔ Q').comap (MulAut.conj l).toMonoidHom := by
        refine sup_le (fun q hq => ?_) (fun q' hq' => ?_)
        · show l * q * l⁻¹ ∈ Q ⊔ Q'
          exact (le_sup_left : Q ≤ Q ⊔ Q') ((Subgroup.mem_normalizer_iff.mp (hLQ hl) q).mp hq)
        · show l * q' * l⁻¹ ∈ Q ⊔ Q'
          have h1 : ⁅q', l⁆ ∈ Q := hcomm (Subgroup.commutator_mem_commutator hq' hl)
          have e : l * q' * l⁻¹ = (⁅q', l⁆)⁻¹ * q' := by simp only [commutatorElement_def]; group
          rw [e]
          exact (Q ⊔ Q').mul_mem ((Q ⊔ Q').inv_mem ((le_sup_left : Q ≤ Q ⊔ Q') h1))
            ((le_sup_right : Q' ≤ Q ⊔ Q') hq')
      exact hle hx
    intro l hl
    exact B6.mem_normalizer_of_forall_mem (fun x hx => hcL l hl x hx)
      (fun x hx => by simpa using hcL l⁻¹ (L.inv_mem hl) x hx)
  ·
    have hSW : ∀ s ∈ S, s ∈ Subgroup.normalizer ((Q ⊔ Q' : Subgroup G) : Set G) := by
      intro s hs
      refine Subgroup.inf_normalizer_le_normalizer_sup Q Q' ⟨hSQ hs, ?_⟩
      refine mem_normalizer_conjSub ?_
      have h1 : t'⁻¹ * s * t'⁻¹⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hTS (inv_mem ht'T)) s).mp hs
      exact hSQ (by simpa using h1)
    have hTW : ∀ x ∈ T, x ∉ S → B6.conjSub x (Q ⊔ Q') = Q ⊔ Q' := by
      intro x hx hxS
      have hx1 : t'⁻¹ * x ∈ S := hprod _ (inv_mem ht'T) _ hx (fun h => ht'S (by simpa using S.inv_mem h)) hxS
      have hx2 : x * t' ∈ S := hprod _ hx _ ht'T hxS ht'S
      have hc1 : B6.conjSub x Q = Q' := by
        have e : x = t' * (t'⁻¹ * x) := by group
        rw [e, B6.conjSub_mul, B6.conjSub_eq_self (hSQ hx1)]
      have hc2 : B6.conjSub x Q' = Q := by
        rw [hQ', ← B6.conjSub_mul, B6.conjSub_eq_self (hSQ hx2)]
      rw [map_sup, hc1, hc2, sup_comm]
    intro x hx
    by_cases hxS : x ∈ S
    · exact hSW x hxS
    · refine B6.mem_normalizer_of_conjSub_le (le_of_eq (hTW x hx hxS)) (le_of_eq (hTW x⁻¹ (inv_mem hx) ?_))
      exact fun h => hxS (by simpa using S.inv_mem h)
  ·
    intro y hy
    refine Subgroup.inf_normalizer_le_normalizer_sup Q Q' ⟨hYQ hy, ?_⟩
    refine mem_normalizer_conjSub (hYQ ?_)
    have := (Subgroup.mem_normalizer_iff.mp (hTY (inv_mem ht'T)) y).mp hy
    simpa using this

end Generic

section Main

variable {G : Type} [Group G] [Finite G]

open CFSG.Quasithin.S153D in
theorem l3Closing_of_named_inputs (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kL : L3YLLabel) (kQ : L3ClosingQ) : L3Closing := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hq c12 hV hYY
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  obtain ⟨hLc, hLn, -, -, -, hLq⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hYpL : Yp ≤ Subgroup.normalizer (L : Set G) := Yp_le_normalizer h37 h38 hh c.ctx.inH hLI
  have hRN : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := c.c16.R_norm
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp := pCoreOf_sup_R153_le c.facts hLI hLq hRN
  have hlab := kL G T Mc M V₁ V₂ Yp I L t c hq c12 hV hYY
  obtain ⟨t', ht'T, ht'S, hswap⟩ := szN3_exists_swap hyp hh.decomp hlab
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp hh.decomp
  have hSV₁ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₁ : Set G) := inf_le_right
  have hSV₂ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) := by
    obtain ⟨hc1, -⟩ := szN3_conj_V_swap hyp hh.decomp ht'T ht'S
    intro s hs
    have h1 : t'⁻¹ * s * t' ∈ Sgp153 T V₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (hTS (inv_mem ht'T)) s).mp hs
      simpa using this
    rw [← hc1]
    exact mem_normalizer_conjSub (hSV₁ h1)
  have hSYL : Sgp153 T V₁ ≤ Subgroup.normalizer (YL153 Yp L : Set G) := by
    rcases hlab with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact szN3_S_le_normalizer_oTwoUpper hyp inf_le_left hSV₁
    · rw [h1]; exact szN3_S_le_normalizer_oTwoUpper hyp inf_le_left hSV₂
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) :=
    szN3_S_le_normalizer_L h37 h38 c hSYL
  have hcomm := kQ G T Mc M V₁ V₂ Yp I L t c hq c12 hV hYY hSL t' ht'T ht'S hswap
  set R : Subgroup G := R153 T V₁ Yp with hR
  set O : Subgroup G := pCoreOf 2 (L ⊔ R) with hOdef
  set Q : Subgroup G := ⁅O, L⁆ with hQ
  have hOL : L ≤ Subgroup.normalizer (O : Set G) := fun l hl =>
    le_normalizer_pCoreOf 2 (L ⊔ R) (Subgroup.mem_sup_left hl)
  have hYpR : Yp ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans (le_normalizer_pCoreOf 2 _)
  have hSR : Sgp153 T V₁ ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  have hNO : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G) → g ∈ Subgroup.normalizer (R : Set G) →
      g ∈ Subgroup.normalizer (O : Set G) := fun g h1 h2 =>
    normalizer_le_normalizer_pCoreOf 2 (L ⊔ R)
      (Subgroup.inf_normalizer_le_normalizer_sup L R ⟨h1, h2⟩)
  have hQL : Q ≤ L := by
    refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    have h1 : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hRN (hO hx)) l).mp hl
    rw [commutatorElement_def]
    exact L.mul_mem h1 (L.inv_mem hl)
  have hQO : Q ≤ O := by
    refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    have h1 : l * x⁻¹ * l⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hOL hl) _).mp (O.inv_mem hx)
    have e : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
    rw [commutatorElement_def, e]
    exact O.mul_mem hx h1
  have hQ2 : IsPGroup 2 Q := (pCoreOf_isPGroup 2 (L ⊔ R)).to_le hQO
  have hUQ : ⁅WL153 T M L, L⁆ ≤ Q := by
    have hWc : WL153 T M L ≤ centerOf O := WL_le_centerOf hh c.ctx c.facts hLI hO
    exact Subgroup.commutator_mono (fun x hx => (hWc hx).1) le_rfl
  have hU0 : ⁅WL153 T M L, L⁆ ≠ ⊥ := by
    intro h0
    apply not_le_centralizer_WL hh hLle hLn
    have h1 : ⁅L, WL153 T M L⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h0
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hQ0 : Q ≠ ⊥ := fun h => hU0 (eq_bot_iff.mpr (h ▸ hUQ))
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := fun l hl =>
    mem_normalizer_commutator' (hOL hl) (Subgroup.le_normalizer hl)
  have hSQ : Sgp153 T V₁ ≤ Subgroup.normalizer (Q : Set G) := fun s hs =>
    mem_normalizer_commutator' (hNO s (hSL hs) (hSR hs)) (hSL hs)
  have hYQ : Y153 Mc M ≤ Subgroup.normalizer (Q : Set G) := fun y hy => by
    have hy' : y ∈ Yp := hYY ▸ hy
    exact mem_normalizer_commutator' (hNO y (hYpL hy') (hYpR hy')) (hYpL hy')
  have hTY : T ≤ Subgroup.normalizer (Y153 Mc M : Set G) := fun x hx =>
    le_normalizer_Y153 Mc M (hyp.T_le hx)
  have hidx : (Sgp153 T V₁).relIndex T = 2 := hh.decomp.relIndex_nS hyp
  have hprod : ∀ a ∈ T, ∀ b ∈ T, a ∉ Sgp153 T V₁ → b ∉ Sgp153 T V₁ → a * b ∈ Sgp153 T V₁ := by
    intro a ha b hb haS hbS
    have h2 : ((Sgp153 T V₁).subgroupOf T).index = 2 := hidx
    have h3 := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    have hiff : (⟨a, ha⟩ * ⟨b, hb⟩ : ↥T) ∈ (Sgp153 T V₁).subgroupOf T := by
      rw [h3]
      exact iff_of_false (fun h => haS h) (fun h => hbS h)
    exact hiff
  exact closing_core hQL hQ2 hQ0 hLQ hSQ hYQ hTS hTY ht'T ht'S hprod hcomm

end Main

end SBd4

end CFSG.Quasithin
