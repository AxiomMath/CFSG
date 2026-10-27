module

public import CFSG.Quasithin.Background.RonanE114D4LowHex
public import CFSG.Quasithin.Background.RonanE114D4LowBT
public import CFSG.Quasithin.Background.RonanE114D4LowRank

public section

namespace CFSG.Quasithin.RonanE114Low

open CFSG.GH74.BNPair CFSG.Quasithin CFSG.Quasithin.H13.F431.BN CFSG.Open
  CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage4.Hex CFSG.Timmesfeld.RankTwo
  CFSG.LieType.Steinberg.TwistedD4

variable {X : Type} [Group X] [Finite X] {K : Type} [Field K] [CharP K 2] {σ : K →+* K}
  {hσ : ∀ c, σ (σ (σ c)) = c} {D : RankTwoSystem X 6} {ψ : ∀ i : Fin 6, d43Par σ i → X}
  (hU : CFSG.QuasithinUnique.IsSylowTwoOf D.U ⊤) (hψ : D4Coords D hσ ψ) (hσ1 : ∃ c : K, σ c ≠ c)

theorem mem_normalizer_of_map_conj {H : Subgroup X} {x : X}
    (h : H.map (MulAut.conj x).toMonoidHom = H) : x ∈ Subgroup.normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← h]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← h] at hg
    obtain ⟨g', hg', he⟩ := hg
    have : g' = g := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
      exact mul_left_cancel (mul_right_cancel he)
    rw [← this]
    exact hg'

omit [Finite X] in
theorem le_normalizer_map_of_normal (H : Subgroup X) (N : Subgroup ↥H) [hN : N.Normal] :
    H ≤ Subgroup.normalizer ((N.map H.subtype : Subgroup X) : Set X) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨x, hx⟩ * r * ⟨x, hx⟩⁻¹, hN.conj_mem r hr _, by simp⟩
  · rintro ⟨r, hr, hrz⟩
    refine ⟨⟨x, hx⟩⁻¹ * r * ⟨x, hx⟩, ?_, ?_⟩
    · have := hN.conj_mem r hr ⟨x, hx⟩⁻¹
      simpa using this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hrz ⊢
      rw [hrz]
      group

theorem isSolvable_map_solvableRadical (H : Subgroup X) :
    Group.IsSolvable ↥((CFSG.solvableRadical ↥H).map H.subtype) := by
  have hs : Group.IsSolvable (CFSG.solvableRadical ↥H) := A3.solvableRadical_isSolvable
  exact Group.isSolvable_of_isSolvable_injective
    (f := ((CFSG.solvableRadical ↥H).equivMapOfInjective H.subtype
      H.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)

include hψ in
omit [Finite X] in
theorem psi_two_mul_self (t : K) : ψ 2 t * ψ 2 t = 1 := by
  have h := hψ.rel.add 2 t t
  have h0 : ((t : d43Par σ 2) + (t : d43Par σ 2) : d43Par σ 2) = 0 :=
    CharTwo.add_self_eq_zero (R := K) t
  have h1 : ψ 2 ((t : d43Par σ 2) + (t : d43Par σ 2)) = ψ 2 0 := congrArg (ψ 2) h0
  calc ψ 2 t * ψ 2 t = ψ 2 ((t : d43Par σ 2) + (t : d43Par σ 2)) := h.symm
    _ = ψ 2 0 := h1
    _ = 1 := psi_zero hψ 2

include hU hψ hσ1

theorem fix_line (hBT : Holds X 2) (Φ : Subgroup (MulAut X)) (K₁ : Subgroup X)
    (hK₁Φ : ∀ x ∈ K₁, MulAut.conj x ∈ Φ) {R₀ : Subgroup X} (hR₀ : R₀ ≠ ⊥)
    (hR₀2 : IsPGroup 2 R₀) (hΦR₀ : ∀ φ ∈ Φ, R₀.map φ.toMonoidHom = R₀) (α : MulAut X)
    (hAK : (D.root 3).map α.toMonoidHom ≤ K₁)
    (hO2 : ¬ (D.root 3).map α.toMonoidHom ≤ pCoreOf 2 K₁)
    (hOinf : (D.root 3).map α.toMonoidHom ⊓ (CFSG.solvableRadical ↥K₁).map K₁.subtype ≠ ⊥)
    (hO2U : pCoreOf 2 K₁ ≤ D.U) :
    ∀ φ ∈ Φ, (P D false).map φ.toMonoidHom = P D false := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := card_root_one_ne_six hψ hσ1
  set A : Subgroup X := (D.root 3).map α.toMonoidHom with hAdef
  have hA2 : IsPGroup 2 A :=
    (hU.2.1.to_le (D.root_le_U (k := 3) (by norm_num) (by norm_num))).map _
  obtain ⟨P₀, S, hP₀, hP₀Φ, hSP₀⟩ := exists_invariant_parabolic hBT Φ hR₀ hR₀2 hΦR₀
  obtain ⟨c, hc⟩ := eq_stab_of_normalizer_sylow D hU hP₀ S hSP₀
  obtain ⟨i, hyΦ⟩ : ∃ i : Bool, ∀ φ ∈ Φ, (stab D (c • v D i)).map φ.toMonoidHom =
      stab D (c • v D i) := by
    rcases hc with hB | ⟨i, hi⟩
    · refine ⟨false, fun φ hφ => map_stab_of_map_borel D hU hcard φ c ?_ false⟩
      rw [← hB]
      exact hP₀Φ φ hφ
    · exact ⟨i, fun φ hφ => hi ▸ hP₀Φ φ hφ⟩
  set y : V D := c • v D i with hy
  have hK₁y : K₁ ≤ stab D y := by
    intro x hx
    rw [← normalizer_stab D hU y]
    exact mem_normalizer_of_map_conj (hyΦ _ (hK₁Φ x hx))
  have hK₁N : K₁ ≤ Subgroup.normalizer (stab D y : Set X) :=
    hK₁y.trans Subgroup.le_normalizer
  have hK₁rad : K₁ ≤ Subgroup.normalizer (rad D y : Set X) :=
    hK₁N.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hAy : A ≤ stab D y := hAK.trans hK₁y
  have hradK : K₁ ⊓ rad D y ≤ pCoreOf 2 K₁ := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 (stab D y)).to_le inf_le_right)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hx) z
    have h2 := Subgroup.mem_normalizer_iff.1 (hK₁rad hx) z
    simp only [Subgroup.mem_inf]
    exact and_congr h1 h2
  have hAnot : ¬ A ≤ rad D y := fun h => hO2 (le_inf hAK h |>.trans hradK)
  set Ω : Set (V D) := (Γ D).neighborSet y with hΩ
  have hPΩ : ∀ g ∈ stab D y, ∀ w ∈ Ω, g • w ∈ Ω := by
    intro g hg w hw
    have hgy : g • y = y := hg
    show (Γ D).Adj y (g • w)
    rw [← hgy]
    exact (adj_smul_iff' D g).2 hw
  by_cases hyv : stab D y = P D false
  · intro φ hφ
    rw [← hyv]
    exact hyΦ φ hφ
  exfalso
  have hdich : ∀ u, (Γ D).Adj y u → (∀ a ∈ A, a • u = u) →
      (∀ w w', (Γ D).Adj y w → (Γ D).Adj y w' → w ≠ u → w' ≠ u → ∃ a ∈ A, a • w = w') →
      ∀ w ∈ Ω, ∀ w' ∈ Ω, ∃ x ∈ K₁ ⊓ stab D y, x • w = w' := by
    intro u hu hAu htr
    obtain ⟨S', hS'2, hS'n, hS'⟩ := exists_sylow_chamber D hU hu
    have hAS : A ≤ S' := hS' A (le_inf hAy fun a ha => hAu a ha) hA2
    rcases rank_one_dichotomy (P := stab D y) (Ω := Ω) hu hPΩ hS'2 hS'n hAS hK₁N hAK hAy hAu
      (fun w hw w' hw' hwu hw'u => htr w w' hw hw' hwu hw'u) with h | h
    · exact absurd h hO2
    · exact h
  cases i
  ·
    have hyl : ∃ h : X, y = h • v D false := ⟨c, rfl⟩
    have hyne : y ≠ v D false := fun h => hyv (by rw [h, stab_v])
    rcases line_class_aut hU hψ hσ1 α hyl hAy with h | ⟨u, hu, hAu, htr, hnot⟩
    · exact hAnot h
    obtain ⟨p, hp, hpU⟩ := sylow_line hU hyl hyne
    have htrans := hdich u hu hAu htr
    obtain ⟨p', hp', hpp'⟩ := exists_adj_ne D hU y p
    obtain ⟨x, hx, hxp⟩ := htrans p hp p' hp'
    obtain ⟨hxK, hxy⟩ := Subgroup.mem_inf.1 hx
    apply hnot p p' hp hp' (Ne.symm hpp')
    intro z hz
    obtain ⟨hzA, hzy⟩ := Subgroup.mem_inf.1 hz
    have hzO : z ∈ pCoreOf 2 K₁ ⊓ rad D y :=
      Subgroup.mem_inf.2 ⟨hradK (Subgroup.mem_inf.2 ⟨hAK hzA, hzy⟩), hzy⟩
    have hYp : ∀ w ∈ pCoreOf 2 K₁ ⊓ rad D y, w ∈ rad D p := fun w hw =>
      hpU (Subgroup.mem_inf.2 ⟨hO2U (Subgroup.mem_inf.1 hw).1, (Subgroup.mem_inf.1 hw).2⟩)
    refine Subgroup.mem_inf.2 ⟨hYp z hzO, ?_⟩
    have hxn : x⁻¹ * z * x ∈ pCoreOf 2 K₁ ⊓ rad D y := by
      obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hzO
      have hx1 := le_normalizer_pCoreOf 2 K₁ (K₁.inv_mem hxK)
      have hx2 := (hK₁rad (K₁.inv_mem hxK))
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 hx1 z).1 hz1
        simpa using this
      · have := (Subgroup.mem_normalizer_iff.1 hx2 z).1 hz2
        simpa using this
    rw [← hxp, mem_rad_smul_iff]
    exact hYp _ hxn
  ·
    have hyp : ∃ h : X, y = h • v D true := ⟨c, rfl⟩
    rcases point_class_aut hU hψ hσ1 α hyp hAy with h | ⟨hbot, u, hu, hAu, htr⟩
    · exact hAnot h
    have htrans := hdich u hu hAu htr
    have hA4 : ∃ e₁ ∈ A, ∃ e₂ ∈ A, e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₁ ≠ e₂ := by
      obtain ⟨c₀, hc₀⟩ := hσ1
      have hc0 : c₀ ≠ 0 := fun h => hc₀ (by rw [h, map_zero])
      have hc1 : c₀ ≠ 1 := fun h => hc₀ (by rw [h, map_one])
      have hne : ∀ {t t' : K}, t ≠ t' → α (ψ 2 t) ≠ α (ψ 2 t') :=
        fun h h' => h (hψ.inj 2 (α.injective h'))
      have h1 : α (ψ 2 (0 : K)) = 1 := by rw [psi2_zero hψ, map_one]
      refine ⟨α (ψ 2 (1 : K)), ⟨_, hψ.mem 2 _, rfl⟩, α (ψ 2 c₀), ⟨_, hψ.mem 2 _, rfl⟩,
        ?_, ?_, hne (Ne.symm hc1)⟩
      · rw [← h1]
        exact hne one_ne_zero
      · rw [← h1]
        exact hne hc0
    obtain ⟨e₁, he₁, e₂, he₂, he₁1, he₂1, he₁₂⟩ := hA4
    have hE2 : ∀ e ∈ A, e * e = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨t, rfl⟩ := exists_psi2 hψ ha
      show α (ψ 2 t) * α (ψ 2 t) = 1
      rw [← map_mul, psi_two_mul_self hψ, map_one]
    obtain ⟨w₀, hw₀, hw₀u⟩ := exists_adj_ne D hU y u
    have hEfree : ∀ e ∈ A, ∀ w ∈ Ω, w ≠ u → e • w = w → e = 1 := by
      intro e he w hw hwu hew
      have hle := le_rad D hU (R := Subgroup.zpowers e) hw hu hwu
        (by
          rw [Subgroup.zpowers_le]
          exact hAy he)
        (hA2.to_le (by rw [Subgroup.zpowers_le]; exact he))
        (fun r hr => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
          exact (MulAction.stabilizer X w).zpow_mem hew k)
        (fun r hr => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
          exact (MulAction.stabilizer X u).zpow_mem (hAu e he) k)
      have : e ∈ A ⊓ rad D y := Subgroup.mem_inf.2 ⟨he, hle (Subgroup.mem_zpowers e)⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    set R : Subgroup X := (CFSG.solvableRadical ↥K₁).map K₁.subtype ⊓ stab D y with hR
    have hRJ : K₁ ⊓ stab D y ≤ Subgroup.normalizer (R : Set X) := by
      intro x hx
      obtain ⟨hxK, hxy⟩ := Subgroup.mem_inf.1 hx
      have h1 := le_normalizer_map_of_normal K₁ (CFSG.solvableRadical ↥K₁) hxK
      have h2 := Subgroup.le_normalizer hxy
      rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
      intro z
      simp only [hR, Subgroup.mem_inf]
      exact and_congr (h1 z) (h2 z)
    have hRs : Group.IsSolvable R := by
      have h := isSolvable_map_solvableRadical K₁
      exact Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (inf_le_left : R ≤ _))
    have hRfix := fix_of_isSolvable (J := K₁ ⊓ stab D y) (R := R) (E := A) (Ω := Ω) (u := u) hu
      (fun g hg w hw => hPΩ g (Subgroup.mem_inf.1 hg).2 w hw) htrans (le_inf hAK hAy) hAu
      (fun w hw w' hw' hwu hw'u => htr w w' hw hw' hwu hw'u) hEfree hE2 he₁ he₂ he₁1 he₂1 he₁₂
      ⟨w₀, hw₀, hw₀u⟩ hRJ hRs (fun r hr w hw => hPΩ r (Subgroup.mem_inf.1 hr).2 w hw)
    apply hOinf
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzA, hzR⟩ := Subgroup.mem_inf.1 hz
    have hzR' : z ∈ R := Subgroup.mem_inf.2 ⟨hzR, hAy hzA⟩
    have hle := le_rad D hU (R := A ⊓ R) hu hw₀ (Ne.symm hw₀u) (inf_le_left.trans hAy)
      (hA2.to_le inf_le_left) (fun r hr => hRfix r (Subgroup.mem_inf.1 hr).2 u hu)
      (fun r hr => hRfix r (Subgroup.mem_inf.1 hr).2 w₀ hw₀)
    have : z ∈ A ⊓ rad D y := Subgroup.mem_inf.2 ⟨hzA, hle (Subgroup.mem_inf.2 ⟨hzA, hzR'⟩)⟩
    rw [hbot] at this
    exact this

theorem map_P_false_of_map_weakClosure {W : Subgroup X} (hWU : W ≤ D.U) (hX1 : D.root 1 ≤ W)
    (hBW : D.B ≤ Subgroup.normalizer (W : Set X)) (φ : MulAut X)
    (hφ : W.map φ.toMonoidHom = W) : (P D false).map φ.toMonoidHom = P D false := by
  have hm := mi_true_not_mem_normalizer D hWU hX1
  have hcases : Subgroup.normalizer (W : Set X) = D.B ∨
      Subgroup.normalizer (W : Set X) = P D false := by
    rcases eq_B_or_P_or_top D hBW with h | ⟨i, h⟩ | h
    · exact Or.inl h
    · cases i
      · exact Or.inr h
      · exact absurd (h ▸ mi_mem_P D true) hm
    · exact absurd (h ▸ Subgroup.mem_top _) hm
  have hN : (Subgroup.normalizer (W : Set X)).map φ.toMonoidHom =
      Subgroup.normalizer (W : Set X) := by
    rw [Subgroup.map_equiv_normalizer_eq, hφ]
  rcases hcases with h | h
  · rw [h] at hN
    exact map_P_of_map_B D hU (card_root_one_ne_six hψ hσ1) φ hN false
  · rw [h] at hN
    exact hN

end CFSG.Quasithin.RonanE114Low
