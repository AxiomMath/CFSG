module

public import CFSG.Milestones.ASVolI.C121.P1e
public import CFSG.Milestones.ASVolI.C121.P1d

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

namespace burnsideC121_YCtx

variable {Ω : Type} [Group Ω] [Finite Ω] {X R T Y W : Subgroup Ω}
  (c : burnsideC121_YCtx X R T Y W) {n : ℕ} {F : Type} [Field F] [Fintype F]
  (D : burnsideC121_NatD Y W n F)

include c

theorem YS_le_normalizer : Y ⊔ baum T ≤ Subgroup.normalizer (Y : Set Ω) :=
  sup_le Subgroup.le_normalizer c.S_le_normalizer

theorem charTwo_YS : CharTwo (Y ⊔ baum T) := by
  have hY : CharTwo Y := A4.charTwo_of_normal c.Y_le_H c.H_le_normalizer c.charTwo_H
  exact A4.charTwo_sup hY c.S_le_normalizer c.S_pGroup

theorem omega_S_eq :
    omegaOneCenterOf (baum T) = omegaOneCenterOf (thompsonJ (burnsideC121_P X R T Y)) := by
  rw [← c.baum_P, burnsideC121_omegaOneCenter_baum]

theorem YS_prod : ∀ x ∈ Y ⊔ baum T, ∃ y ∈ Y, ∃ s ∈ baum T, x = y * s := by
  intro x hx
  have hx' : x ∈ ((Y ⊔ baum T : Subgroup Ω) : Set Ω) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y _ c.S_le_normalizer] at hx'
  obtain ⟨y, hy, s, hs, rfl⟩ := hx'
  exact ⟨y, hy, s, hs, rfl⟩

theorem pCore_Y_le_S (hSyl : IsSylowTwoOf (baum T) (Y ⊔ baum T)) : pCoreOf 2 Y ≤ baum T :=
  (B6.pCoreOf_two_le_of_isSylowTwoOf
    (A4.isSylowTwoOf_inf_normal hSyl le_sup_left c.YS_le_normalizer)).trans inf_le_left

include D

theorem not_le_centralizer_omega_n2 (h610 : B_6_10) (h123 : I_2_3) (hn : 2 ≤ n)
    (hYS : ¬ Y ≤ Subgroup.normalizer (baum T : Set Ω)) :
    ¬ Y ≤ Subgroup.centralizer (omegaOneCenterOf (baum T) : Set Ω) := by
  obtain ⟨hSyl, -⟩ := c.b610 D h610 hn hYS
  obtain ⟨u, huM, huP, huY⟩ := c.exists_fixed_commW D h123 hn
  intro hYE
  apply huY
  have huS : u ∈ baum T := c.pCore_Y_le_S hSyl (c.commW_le_pCore_Y huM)
  have huE : u ∈ omegaOneCenterOf (baum T) :=
    Subgroup.subset_closure ⟨⟨huS, Subgroup.centralizer_le c.S_le_P huP⟩,
      c.W_elem.2 u (c.commW_le_W huM)⟩
  exact Subgroup.mem_centralizer_iff.2 fun y hy =>
    (Subgroup.mem_centralizer_iff.1 (hYE hy) u huE).symm

theorem hasNaturalFstar_n2 (h610 : B_6_10) (h123 : I_2_3) (hn : 2 ≤ n)
    (hYS : ¬ Y ≤ Subgroup.normalizer (baum T : Set Ω)) :
    HasNaturalFstar (Y ⊔ baum T) (VZ (baum T) (Y ⊔ baum T)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSyl, hdec⟩ := c.b610 D h610 hn hYS
  set S := baum T with hSdef
  set H₁ := Y ⊔ S with hH₁
  set V₁ := VZ S H₁ with hV₁
  set E := omegaOneCenterOf (thompsonJ (burnsideC121_P X R T Y)) with hE
  have hF₁ : CharTwo H₁ := c.charTwo_YS
  obtain ⟨-, hV₁el0, hred₁0⟩ := conjClosure_isTwoReducedIn_of_charTwo hSyl hF₁
    (Z := quasithinOmegaOneCenter S) le_rfl
  have hV₁el : IsElemAbelian 2 V₁ := hV₁el0
  have hred₁ : IsTwoReducedIn H₁ V₁ := hred₁0
  clear hV₁el0 hred₁0
  have hH₁N : H₁ ≤ Subgroup.normalizer (V₁ : Set Ω) := hred₁.2.1
  have hYH₁ : Y ≤ H₁ := le_sup_left
  have hYN₁ : Y ≤ Subgroup.normalizer (V₁ : Set Ω) := hYH₁.trans hH₁N
  have hαs := c.alpha_surjective D hn
  have h4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, D.card]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hEV₁ : omegaOneCenterOf S ≤ V₁ := le_conjClosure _ _
  have hYV₁ : ¬ Y ≤ Subgroup.centralizer (V₁ : Set Ω) := fun h =>
    c.not_le_centralizer_omega_n2 D h610 h123 hn hYS (h.trans (Subgroup.centralizer_le hEV₁))
  have hCY₁ : Y ⊓ Subgroup.centralizer (V₁ : Set Ω) = pCoreOf 2 Y := by
    have hn' : Y ≤ Subgroup.normalizer
        ((Y ⊓ Subgroup.centralizer (V₁ : Set Ω) : Subgroup Ω) : Set Ω) :=
      fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy, B2F.normalizer_le_normalizer_centralizer V₁ (hYN₁ hy)⟩
    rcases c.normal_le_or_eq D inf_le_left hn' with h | h
    · refine le_antisymm h (le_inf (pCoreOf_le 2 Y) ?_)
      have hO : pCoreOf 2 Y ≤ pCoreOf 2 H₁ :=
        le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYH₁)
          (c.YS_le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 Y)) (pCoreOf_isPGroup 2 Y)
      exact hO.trans (C124.pCoreOf_le_centralizer hred₁)
    · exact absurd (h ▸ inf_le_right) hYV₁
  set B : Subgroup Ω := ⁅W, Y⁆ ⊔ (E ⊓ Subgroup.centralizer (Y : Set Ω)) with hB
  have hEB : E ≤ B := by
    rw [hdec]
    exact sup_le_sup_right inf_le_left _
  have hSE : S ≤ Subgroup.normalizer (E : Set Ω) := by
    rw [hE, ← c.omega_S_eq]
    intro s hs
    exact normalizer_le_normalizer_omegaOneCenterOf S (Subgroup.le_normalizer hs)
  have hH₁B : H₁ ≤ Subgroup.normalizer (B : Set Ω) := by
    refine sup_le (fun y hy => Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨c.Y_le_H.trans c.H_le_normalizer_commW hy, Subgroup.centralizer_le_normalizer _ ?_⟩)
      (fun s hs => Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨(c.S_le_P.trans c.P_le_H).trans c.H_le_normalizer_commW hs,
          Subgroup.inf_normalizer_le_normalizer_inf ⟨hSE hs,
            B2F.normalizer_le_normalizer_centralizer Y (c.S_le_normalizer hs)⟩⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.1 hz.2 y hy).symm
  have hV₁B : V₁ ≤ B := by
    refine conjClosure_le fun h hh z hz => ?_
    have hzE : z ∈ E := by
      rw [hE, ← c.omega_S_eq]
      exact hz
    exact (Subgroup.mem_normalizer_iff.1 (hH₁B hh) z).1 (hEB hzE)
  have hES : E ≤ S := by
    rw [hE, ← c.omega_S_eq]
    exact C1GN.omegaOneCenterOf_le_self S
  have hzN : E ⊓ Subgroup.centralizer (Y : Set Ω) ≤
      Subgroup.normalizer ((⁅W, Y⁆ : Subgroup Ω) : Set Ω) :=
    inf_le_left.trans (hES.trans ((c.S_le_P.trans c.P_le_H).trans c.H_le_normalizer_commW))
  have hBY : ⁅B, Y⁆ ≤ ⁅W, Y⁆ := by
    rw [Subgroup.commutator_le]
    intro b hb y hy
    have hb' : b ∈ ((⁅W, Y⁆ ⊔ (E ⊓ Subgroup.centralizer (Y : Set Ω)) : Subgroup Ω) : Set Ω) := hb
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hzN] at hb'
    obtain ⟨m, hm, z, hz, rfl⟩ := hb'
    have hzy : z * y * z⁻¹ = y := by
      rw [← Subgroup.mem_centralizer_iff.1 hz.2 y hy, mul_inv_cancel_right]
    have e1 : ⁅m * z, y⁆ = ⁅m, y⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc m * z * y * (m * z)⁻¹ * y⁻¹ = m * (z * y * z⁻¹) * m⁻¹ * y⁻¹ := by group
        _ = m * y * m⁻¹ * y⁻¹ := by rw [hzy]
    rw [e1, ← c.commutator_commutator_W]
    exact Subgroup.commutator_mem_commutator hm hy
  have hV₁Y : ⁅V₁, Y⁆ ≤ ⁅W, Y⁆ := (Subgroup.commutator_mono hV₁B le_rfl).trans hBY
  have hVL : ⁅V₁, Y⁆ ≠ ⊥ := fun h =>
    hYV₁ (Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h))
  obtain ⟨-, -, hFstar₁, -⟩ := C124.B2_10_2 hV₁el hred₁ (B6.pCoreOf_two_le_of_isSylowTwoOf hSyl)
    le_rfl hSyl hYH₁ c.YS_le_normalizer c.YS_prod hVL (Or.inl (c.isQuasisimple_quot D hn))
  have hfA : fstarAut H₁ V₁ = autOn Y V₁ := by
    unfold fstarAut
    rw [CFSG.generalizedFitting_eq_componentClassification,
      ← CFSG.Quasithin.quasithinGenFitting_eq_map_subtype]
    exact hFstar₁
  set K := fstarPre H₁ V₁ with hKdef
  have hmemK : ∀ g : Ω, g ∈ K ↔ g ∈ H₁ ∧ ∃ hg : g ∈ Subgroup.normalizer (V₁ : Set Ω),
      convI hV₁el ⟨g, hg⟩ ∈ autI hV₁el Y := by
    intro g
    rw [hKdef]
    unfold fstarPre
    rw [hfA]
    constructor
    · rintro ⟨hgH, nn, hnn, rfl⟩
      exact ⟨hgH, nn.2, hnn⟩
    · rintro ⟨hgH, hg, h⟩
      exact ⟨hgH, ⟨g, hg⟩, h, rfl⟩
  have hKN : K ≤ Subgroup.normalizer (V₁ : Set Ω) := fun g hg => ((hmemK g).1 hg).2.1
  have hYK : Y ≤ K := fun y hy => (hmemK y).2 ⟨hYH₁ hy, hYN₁ hy, convI_mem_autI hV₁el hy (hYN₁ hy)⟩
  have hact : ∀ g ∈ K, ∃ y ∈ Y, ∀ w ∈ V₁, g * w * g⁻¹ = y * w * y⁻¹ := by
    intro g hg
    obtain ⟨-, hgN, hmem⟩ := (hmemK g).1 hg
    obtain ⟨yy, hyy, hyyg⟩ := (mem_autI hV₁el).1 hmem
    refine ⟨yy, hyy, fun w hw => ?_⟩
    have h1 := congrArg (fun φ : MulAut (IntMod V₁ hV₁el) => (φ (IntMod.mk hV₁el ⟨w, hw⟩)).val)
      hyyg
    simp only [convI_apply_val] at h1
    exact h1.symm
  obtain ⟨e₁, he₁⟩ := burnsideC121_exists_autIEquiv hV₁el hYN₁ D.α hαs (by rw [hCY₁, D.αk])
  let φK : ↥K →* MulAut (IntMod V₁ hV₁el) := (convI hV₁el).comp (Subgroup.inclusion hKN)
  have hφK : ∀ k : ↥K, φK k ∈ autI hV₁el Y := fun k => by
    obtain ⟨-, hg, h⟩ := (hmemK k).1 k.2
    exact h
  let α' : ↥K →* SL(2, F) := e₁.toMonoidHom.comp (φK.codRestrict (autI hV₁el Y) hφK)
  have hα'y : ∀ k : ↥K, ∀ y : ↥Y, (∀ w ∈ V₁, (k : Ω) * w * (k : Ω)⁻¹ = y * w * (y : Ω)⁻¹) →
      α' k = D.α y := by
    intro k y hky
    have h1 : (φK.codRestrict (autI hV₁el Y) hφK k : ↥(autI hV₁el Y)) =
        ⟨convHom hV₁el Y hYN₁ y, (range_convHom hV₁el Y hYN₁) ▸ ⟨y, rfl⟩⟩ := by
      apply Subtype.ext
      ext w
      apply IntMod.val_injective
      show (convI hV₁el ⟨k, hKN k.2⟩ w).val = (convI hV₁el ⟨y, hYN₁ y.2⟩ w).val
      rw [convI_apply_val, convI_apply_val]
      exact hky w.val w.val_mem
    show e₁ (φK.codRestrict (autI hV₁el Y) hφK k) = D.α y
    rw [h1, he₁]
  have hα's : Function.Surjective α' := by
    intro s
    obtain ⟨y, rfl⟩ := hαs s
    exact ⟨⟨y, hYK y.2⟩, hα'y _ y fun w _ => rfl⟩
  have hα'k : α'.ker = (Subgroup.centralizer (V₁ : Set Ω)).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show e₁ (φK.codRestrict (autI hV₁el Y) hφK k) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    constructor
    · intro h
      have h2 : φK k = 1 := congrArg Subtype.val h
      exact (convI_eq_one_iff hV₁el _).1 h2
    · intro h
      apply Subtype.ext
      exact (convI_eq_one_iff hV₁el ⟨k, hKN k.2⟩).2 h
  have hα'r : α'.range = commutator SL(2, F) := by
    rw [MonoidHom.range_eq_top.2 hα's, CFSG.Quasithin.C126.Nat.commutator_sl2_eq_top h4]
  have hVK : ⁅V₁, K⁆ ≤ ⁅W, Y⁆ := by
    rw [Subgroup.commutator_le]
    intro v hv k hk
    obtain ⟨y, hy, hky⟩ := hact k hk
    have e1 : ⁅v, k⁆ = ⁅v, y⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      have h1 := hky v⁻¹ (V₁.inv_mem hv)
      calc v * k * v⁻¹ * k⁻¹ = v * (k * v⁻¹ * k⁻¹) := by group
        _ = v * (y * v⁻¹ * y⁻¹) := by rw [h1]
        _ = v * y * v⁻¹ * y⁻¹ := by group
    rw [e1]
    exact hV₁Y (Subgroup.commutator_mem_commutator hv hy)
  have hVKW : ⁅V₁, K⁆ ≤ W := hVK.trans c.commW_le_W
  have hVKV : ⁅V₁, K⁆ ≤ V₁ := Subgroup.le_normalizer_iff_commutator_le_left.mp hKN
  let β' : ↥⁅V₁, K⁆ →* Multiplicative (Fin 2 → F) := D.β.comp (Subgroup.inclusion hVKW)
  have hβ's : Function.Surjective β' := by
    set A : Subgroup (Multiplicative (Fin 2 → F)) := (⁅V₁, Y⁆.subgroupOf W).map D.β with hA
    have hAinv : ∀ (g : SL(2, F)) (x : Multiplicative (Fin 2 → F)), x ∈ A →
        Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd x)) ∈
          A := by
      rintro g _ ⟨u, hu, rfl⟩
      obtain ⟨y, rfl⟩ := hαs g
      have hu' : (u : Ω) ∈ ⁅V₁, Y⁆ := hu
      have hyu : (y : Ω) * u * (y : Ω)⁻¹ ∈ ⁅V₁, Y⁆ :=
        (Subgroup.mem_normalizer_iff.1 (Subgroup.normalizer_commutator_ge_right V₁ Y y.2) u).1 hu'
      have hyuW : (y : Ω) * u * (y : Ω)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.1 (c.Y_le_normalizer_W y.2) u).1 u.2
      refine ⟨⟨_, hyuW⟩, hyu, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      exact D.βe y u ⟨_, hyuW⟩ rfl
    have hAne : A ≠ ⊥ := by
      intro hbot
      have hle : ⁅V₁, Y⁆ ≤ Subgroup.centralizer (Y : Set Ω) := by
        intro u hu
        have huW : u ∈ W := hV₁Y.trans c.commW_le_W hu
        have h1 : D.β ⟨u, huW⟩ ∈ A := ⟨⟨u, huW⟩, hu, rfl⟩
        rw [hbot, Subgroup.mem_bot] at h1
        have h2 : (⟨u, huW⟩ : ↥W) ∈ D.β.ker := h1
        rw [D.βk, Subgroup.mem_subgroupOf] at h2
        exact h2.2
      have h3 : ⁅⁅V₁, Y⁆, Y⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact hle
      rw [CFSG.CGT.PushingUpLit.SixThree.commutator_commutator_eq c.noTwoQuotient
        (B2F.isPGroup_of_isElemAbelian hV₁el) hYN₁] at h3
      exact hVL h3
    have hAtop := burnsideC121_sl2_irreducible A hAinv hAne
    intro x
    have hx : x ∈ A := hAtop ▸ Subgroup.mem_top x
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨⟨u, Subgroup.commutator_mono le_rfl hYK hu⟩, rfl⟩
  have hβ'k : β'.ker = (⁅V₁, K⁆ ⊓ Subgroup.centralizer (K : Set Ω)).subgroupOf ⁅V₁, K⁆ := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show D.β (Subgroup.inclusion hVKW u) = 1 ↔ _
    rw [← MonoidHom.mem_ker, D.βk, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨-, hC⟩
      refine ⟨u.2, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
      obtain ⟨y, hy, hky⟩ := hact k hk
      have h1 := hky u (hVKV u.2)
      have hC' : (u : Ω) ∈ Subgroup.centralizer (Y : Set Ω) := hC
      have hyu : (y : Ω) * u * y⁻¹ = u := by
        rw [Subgroup.mem_centralizer_iff.1 hC' y hy, mul_inv_cancel_right]
      rw [hyu] at h1
      calc k * (u : Ω) = (k * u * k⁻¹) * k := by group
        _ = u * k := by rw [h1]
    · rintro ⟨-, hC⟩
      exact ⟨hVKW u.2, Subgroup.centralizer_le hYK hC⟩
  have hβ'e : ∀ (k : ↥K) (u v : ↥⁅V₁, K⁆), (v : Ω) = k * u * k⁻¹ →
      Multiplicative.toAdd (β' v) =
        (α' k : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β' u)) := by
    intro k u v huv
    obtain ⟨y, hy, hky⟩ := hact k k.2
    rw [hα'y k ⟨y, hy⟩ hky]
    exact D.βe ⟨y, hy⟩ (Subgroup.inclusion hVKW u) (Subgroup.inclusion hVKW v)
      (by show (v : Ω) = y * u * y⁻¹; rw [← hky u (hVKV u.2)]; exact huv)
  exact ⟨n, D.one_le, F, inferInstance, inferInstance, D.card, α', hα'k, hα'r, β', hβ's, hβ'k,
    hβ'e⟩

end burnsideC121_YCtx

end CFSG.ASVolI
