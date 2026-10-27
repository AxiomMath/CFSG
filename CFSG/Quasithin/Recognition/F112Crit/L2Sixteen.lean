module

public import CFSG.Quasithin.Recognition.F112Crit.Theorem723
public import CFSG.Quasithin.Recognition.F112Crit.PermBound.Orbit

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ T Z : Subgroup G}

structure TorusLocal (μ : CosetGeom G₀ G₁ G₂) (L : Subgroup G) : Prop where
  le_stab : L ≤ stab μ
  normal : stab μ ≤ Subgroup.normalizer (L : Set G)
  trans : ∀ δ ∈ nbrs μ, ∀ δ' ∈ nbrs μ, δ ≠ δ' → ∀ ε ∈ nbrs μ, ∀ ε' ∈ nbrs μ, ε ≠ δ → ε ≠ δ' →
    ε' ≠ δ → ε' ≠ δ' → ∃ g : ↥G₀, (g : G) ∈ L ∧ g • δ = δ ∧ g • δ' = δ' ∧ g • ε = ε'
  reg : ∀ g : ↥G₀, (g : G) ∈ L → ∀ δ ∈ nbrs μ, ∀ δ' ∈ nbrs μ, ∀ ε ∈ nbrs μ, δ ≠ δ' → ε ≠ δ →
    ε ≠ δ' → g • δ = δ → g • δ' = δ' → g • ε = ε → (g : G) ∈ ballStab 1 μ

theorem TorusLocal.smul {μ : CosetGeom G₀ G₁ G₂} {L : Subgroup G} (hT : TorusLocal μ L)
    (g : ↥G₀) : TorusLocal (g • μ) (conjSub (g : G) L) where
  le_stab := by
    rw [CosetGeom.stab_smul]
    exact conjSub_mono _ hT.le_stab
  normal := by
    rw [CosetGeom.stab_smul]
    exact conjSub_le_normalizer hT.normal
  trans := by
    intro δ hδ δ' hδ' hne ε hε ε' hε' h1 h2 h3 h4
    obtain ⟨a, rfl⟩ : ∃ a, δ = g • a := ⟨g⁻¹ • δ, by simp⟩
    obtain ⟨b, rfl⟩ : ∃ b, δ' = g • b := ⟨g⁻¹ • δ', by simp⟩
    obtain ⟨e, rfl⟩ : ∃ e, ε = g • e := ⟨g⁻¹ • ε, by simp⟩
    obtain ⟨e', rfl⟩ : ∃ e', ε' = g • e' := ⟨g⁻¹ • ε', by simp⟩
    have ha : a ∈ nbrs μ := (CosetGeom.smul_adj g).mp hδ
    have hb : b ∈ nbrs μ := (CosetGeom.smul_adj g).mp hδ'
    have he : e ∈ nbrs μ := (CosetGeom.smul_adj g).mp hε
    have he' : e' ∈ nbrs μ := (CosetGeom.smul_adj g).mp hε'
    obtain ⟨k, hkL, hka, hkb, hke⟩ := hT.trans a ha b hb (fun h => hne (by rw [h]))
      e he e' he' (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))
      (fun h => h3 (by rw [h])) (fun h => h4 (by rw [h]))
    refine ⟨g * k * g⁻¹, ?_, ?_, ?_, ?_⟩
    · show (g : G) * (k : G) * (g : G)⁻¹ ∈ conjSub (g : G) L
      exact mul_mem_conjSub hkL
    · rw [mul_smul, mul_smul, inv_smul_smul, hka]
    · rw [mul_smul, mul_smul, inv_smul_smul, hkb]
    · rw [mul_smul, mul_smul, inv_smul_smul, hke]
  reg := by
    intro k hk δ hδ δ' hδ' ε hε hne h1 h2 hkδ hkδ' hkε
    obtain ⟨a, rfl⟩ : ∃ a, δ = g • a := ⟨g⁻¹ • δ, by simp⟩
    obtain ⟨b, rfl⟩ : ∃ b, δ' = g • b := ⟨g⁻¹ • δ', by simp⟩
    obtain ⟨e, rfl⟩ : ∃ e, ε = g • e := ⟨g⁻¹ • ε, by simp⟩
    have ha : a ∈ nbrs μ := (CosetGeom.smul_adj g).mp hδ
    have hb : b ∈ nbrs μ := (CosetGeom.smul_adj g).mp hδ'
    have he : e ∈ nbrs μ := (CosetGeom.smul_adj g).mp hε
    rw [CosetGeom.ballStab_smul, mem_conjSub]
    have hk' : ((g⁻¹ * k * g : ↥G₀) : G) ∈ L := mem_conjSub.mp hk
    have hfix : ∀ x : CosetGeom G₀ G₁ G₂, k • g • x = g • x → (g⁻¹ * k * g) • x = x := by
      intro x hx
      calc (g⁻¹ * k * g) • x = g⁻¹ • (k • (g • x)) := by simp [mul_smul]
        _ = g⁻¹ • (g • x) := by rw [hx]
        _ = x := inv_smul_smul g x
    exact hT.reg (g⁻¹ * k * g) hk' a ha b hb e he (fun h => hne (by rw [h]))
      (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h])) (hfix a hkδ) (hfix b hkδ') (hfix e hkε)

theorem not_dvd_sixteen_and_fifteen {f : ℕ} (h6 : 6 ≤ f) (h9 : f ≤ 9) (h16 : f - 1 ∣ 16)
    (h15 : f - 2 ∣ 15) : False := by
  interval_cases f <;> revert h16 h15 <;> decide

variable [Finite G]

open T723

theorem TorusLocal.card_fixed_sub_two_dvd {μ : CosetGeom G₀ G₁ G₂} {M : Subgroup G}
    (hT : TorusLocal μ M) {z : G} (hzμ : z ∈ stab μ) {ω₀ μ₀ ν₀ : CosetGeom G₀ G₁ G₂}
    (hω₀ : ω₀ ∈ nbrs μ ∧ z ∈ stab ω₀) (hμ₀ : μ₀ ∈ nbrs μ ∧ z ∈ stab μ₀)
    (hν₀ : ν₀ ∈ nbrs μ ∧ z ∈ stab ν₀) (h01 : ω₀ ≠ μ₀) (h02 : ω₀ ≠ ν₀) (h12 : μ₀ ≠ ν₀) :
    Nat.card {δ | δ ∈ nbrs μ ∧ z ∈ stab δ} - 2 ∣ Nat.card (nbrs μ) - 2 := by
  classical
  set F : Set (CosetGeom G₀ G₁ G₂) := {δ | δ ∈ nbrs μ ∧ z ∈ stab δ} with hF
  set z' : ↥(stab μ) := ⟨z, hzμ⟩ with hz'
  set ω₀' : ↥(nbrs μ) := ⟨ω₀, hω₀.1⟩
  set μ₀' : ↥(nbrs μ) := ⟨μ₀, hμ₀.1⟩
  set ν₀' : ↥(nbrs μ) := ⟨ν₀, hν₀.1⟩
  have hfixz : ∀ {δ : CosetGeom G₀ G₁ G₂} (hδ : δ ∈ F), z' • (⟨δ, hδ.1⟩ : ↥(nbrs μ)) = ⟨δ, hδ.1⟩ :=
    fun hδ => Subtype.ext (CosetGeom.smul_eq_of_mem_stab (g := stabToG₀ μ z') hδ.2)
  have hcardF : Nat.card (MulAction.fixedBy ↥(nbrs μ) z') = Nat.card F :=
    card_fixedBy_nbrs μ z'
  set Φ := MulAction.fixedBy ↥(nbrs μ) z' with hΦ
  have hω₀Φ : ω₀' ∈ Φ := hfixz hω₀
  have hμ₀Φ : μ₀' ∈ Φ := hfixz hμ₀
  have hne01 : ω₀' ≠ μ₀' := fun h => h01 (congrArg Subtype.val h)
  have hne02 : ω₀' ≠ ν₀' := fun h => h02 (congrArg Subtype.val h)
  have hne12 : μ₀' ≠ ν₀' := fun h => h12 (congrArg Subtype.val h)
  set D : Subgroup ↥(stab μ) := M.subgroupOf (stab μ) ⊓
    MulAction.stabilizer ↥(stab μ) ω₀' ⊓ MulAction.stabilizer ↥(stab μ) μ₀' with hD
  have hz'ω₀ : z' • ω₀' = ω₀' := hfixz hω₀
  have hz'μ₀ : z' • μ₀' = μ₀' := hfixz hμ₀
  have horbD : MulAction.orbit D ν₀' = ({ω₀', μ₀'} : Set ↥(nbrs μ))ᶜ := by
    ext ω
    rw [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨d, rfl⟩ hω
      have hdω₀ : (d : ↥(stab μ)) • ω₀' = ω₀' := d.2.1.2
      have hdμ₀ : (d : ↥(stab μ)) • μ₀' = μ₀' := d.2.2
      rcases hω with hω | hω
      · apply hne02
        calc ω₀' = (d : ↥(stab μ))⁻¹ • ((d : ↥(stab μ)) • ω₀') := (inv_smul_smul _ _).symm
          _ = (d : ↥(stab μ))⁻¹ • ((d : ↥(stab μ)) • ν₀') := by rw [hdω₀, ← hω]; rfl
          _ = ν₀' := inv_smul_smul _ _
      · apply hne12
        calc μ₀' = (d : ↥(stab μ))⁻¹ • ((d : ↥(stab μ)) • μ₀') := (inv_smul_smul _ _).symm
          _ = (d : ↥(stab μ))⁻¹ • ((d : ↥(stab μ)) • ν₀') := by rw [hdμ₀, ← hω]; rfl
          _ = ν₀' := inv_smul_smul _ _
    · intro hω
      push Not at hω
      obtain ⟨k, hkL, hkω₀, hkμ₀, hkν₀⟩ := hT.trans ω₀ hω₀.1 μ₀ hμ₀.1 h01 ν₀ hν₀.1 ω.1 ω.2
        (Ne.symm h02) (Ne.symm h12) (fun h => hω.1 (Subtype.ext h))
        (fun h => hω.2 (Subtype.ext h))
      have hkμ : (k : G) ∈ stab μ := hT.le_stab hkL
      refine ⟨⟨⟨(k : G), hkμ⟩, ⟨hkL, Subtype.ext hkω₀⟩, Subtype.ext hkμ₀⟩, Subtype.ext hkν₀⟩
  have hregD : ∀ d ∈ D, d • ν₀' = ν₀' → ∀ ω : ↥(nbrs μ), d • ω = ω := by
    intro d hd hdν ω
    obtain ⟨⟨hdL, hdω₀⟩, hdμ₀⟩ := hd
    have hdω₀' : d • ω₀' = ω₀' := hdω₀
    have hdμ₀' : d • μ₀' = μ₀' := hdμ₀
    have hball := hT.reg (stabToG₀ μ d) hdL ω₀ hω₀.1 μ₀ hμ₀.1 ν₀ hν₀.1 h01 (Ne.symm h02)
      (Ne.symm h12) (congrArg Subtype.val hdω₀') (congrArg Subtype.val hdμ₀')
      (congrArg Subtype.val hdν)
    exact smul_eq_of_mem_ballStab μ hball ω
  have hzD : ∀ d ∈ D, ∃ d' ∈ D, ∀ ω : ↥(nbrs μ), (z' * d * z'⁻¹) • ω = d' • ω := by
    intro d hd
    obtain ⟨⟨hdL, hdω₀⟩, hdμ₀⟩ := hd
    have hdω₀' : d • ω₀' = ω₀' := hdω₀
    have hdμ₀' : d • μ₀' = μ₀' := hdμ₀
    refine ⟨z' * d * z'⁻¹, ⟨⟨?_, ?_⟩, ?_⟩, fun ω => rfl⟩
    · show z * (d : G) * z⁻¹ ∈ M
      exact (Subgroup.mem_normalizer_iff.mp (hT.normal hzμ) (d : G)).mp hdL
    · show (z' * d * z'⁻¹) • ω₀' = ω₀'
      rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hz'ω₀.symm, hdω₀', hz'ω₀]
    · show (z' * d * z'⁻¹) • μ₀' = μ₀'
      rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hz'μ₀.symm, hdμ₀', hz'μ₀]
  have hdvd := PermBound.card_fixedBy_inter_orbit_dvd (D := D) (ν₀ := ν₀') (z := z') hregD
    (hfixz hν₀) hzD
  rw [horbD] at hdvd
  have hpair : ({ω₀', μ₀'} : Set ↥(nbrs μ)).ncard = 2 := Set.ncard_pair hne01
  have hc2 : Nat.card ↥(({ω₀', μ₀'} : Set ↥(nbrs μ))ᶜ) = Nat.card (nbrs μ) - 2 := by
    have h := Set.ncard_add_ncard_compl ({ω₀', μ₀'} : Set ↥(nbrs μ))
    rw [hpair] at h
    rw [Nat.card_coe_set_eq (({ω₀', μ₀'} : Set ↥(nbrs μ))ᶜ)]
    omega
  have hsub : ({ω₀', μ₀'} : Set ↥(nbrs μ)) ⊆ Φ := by
    intro x hx
    rcases hx with rfl | hx
    · exact hω₀Φ
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hμ₀Φ
  have hc2' : Nat.card ↥(Φ ∩ ({ω₀', μ₀'} : Set ↥(nbrs μ))ᶜ) = Nat.card F - 2 := by
    rw [← Set.diff_eq, Nat.card_coe_set_eq, Set.ncard_diff hsub, hpair, ← Nat.card_coe_set_eq,
      hcardF]
  rw [hc2, hc2'] at hdvd
  exact hdvd

theorem card_nbrs_γ₀_ne_seventeen (hc : CritAmalgam G₀ G₁ G₂ T Z) {p : ℕ} {X₀ : Subgroup G}
    (hloc : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) (hp : p = 3 ∨ p = 5) {L M : Subgroup G}
    (hL : BenderLocal (γ₀ G₀ G₁ G₂) L) (hT : TorusLocal (γ₀ G₀ G₁ G₂) M)
    (hb : Even (critB G₀ G₁ G₂ Z)) (hb4 : 4 ≤ critB G₀ G₁ G₂ Z) :
    Nat.card (nbrs (γ₀ G₀ G₁ G₂)) ≠ 17 := by
  classical
  intro h17
  obtain ⟨α', z, hα', -, hzα', -, hlow, hf, -⟩ := theorem723_bound hc hloc hp hL hb hb4
  have hN : Nat.card (nbrs α') = 17 := (card_nbrs_eq hc hα').trans h17
  rw [hN] at hlow hf
  set F : Set (CosetGeom G₀ G₁ G₂) := {δ | δ ∈ nbrs α' ∧ z ∈ stab δ} with hF
  have hf9 : Nat.card F ≤ 9 := by omega
  have hf6 : 6 ≤ Nat.card F := by
    by_contra hlt
    have h6 : 6 ≤ (17 - Nat.card F) / 2 := by omega
    have h64 : (64 : ℕ) ≤ 2 ^ ((17 - Nat.card F) / 2) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h6)
    omega
  obtain ⟨ω₀, μ₀, ν₀, hω₀, hμ₀, hν₀, h01, h02, h12⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite F)).mp (by rw [← Nat.card_coe_set_eq]; omega)
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ hα'
  have hL' : BenderLocal α' (conjSub (g : G) L) := by
    rw [hg]
    exact hL.smul g
  have hT' : TorusLocal α' (conjSub (g : G) M) := by
    rw [hg]
    exact hT.smul g
  set z' : ↥(stab α') := ⟨z, hzα'⟩ with hz'
  set ω₀' : ↥(nbrs α') := ⟨ω₀, hω₀.1⟩
  set μ₀' : ↥(nbrs α') := ⟨μ₀, hμ₀.1⟩
  have hfixz : ∀ {δ : CosetGeom G₀ G₁ G₂} (hδ : δ ∈ F), z' • (⟨δ, hδ.1⟩ : ↥(nbrs α')) = ⟨δ, hδ.1⟩ :=
    fun hδ => Subtype.ext (CosetGeom.smul_eq_of_mem_stab (g := stabToG₀ α' z') hδ.2)
  have hcardF : Nat.card (MulAction.fixedBy ↥(nbrs α') z') = Nat.card F :=
    card_fixedBy_nbrs α' z'
  set Φ := MulAction.fixedBy ↥(nbrs α') z' with hΦ
  have hω₀Φ : ω₀' ∈ Φ := hfixz hω₀
  have hne01 : ω₀' ≠ μ₀' := fun h => h01 (congrArg Subtype.val h)
  obtain ⟨U, -, -, hUfix, hUtrans, hUreg, hUnorm⟩ := exists_unipotentH hL' hω₀.1
  have horbU : MulAction.orbit U μ₀' = ({ω₀'} : Set ↥(nbrs α'))ᶜ := by
    ext ω
    rw [Set.mem_compl_iff, Set.mem_singleton_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨u, rfl⟩ hω
      apply hne01
      calc ω₀' = (u : ↥(stab α'))⁻¹ • ω₀' := (hUfix _ (U.inv_mem u.2)).symm
        _ = (u : ↥(stab α'))⁻¹ • ((u : ↥(stab α')) • μ₀') := by
          rw [← hω]
          rfl
        _ = μ₀' := inv_smul_smul _ _
    · intro hω
      obtain ⟨u, hu, huμ⟩ := hUtrans μ₀' ω (Ne.symm hne01) hω
      exact ⟨⟨u, hu⟩, huμ⟩
  have hdvd1 := PermBound.card_fixedBy_inter_orbit_dvd (D := U) (ν₀ := μ₀') (z := z')
    (fun d hd hfix => hUreg d hd μ₀' (Ne.symm hne01) hfix) (hfixz hμ₀) (hUnorm z' hω₀.2)
  rw [horbU] at hdvd1
  have hc1 : Nat.card ↥(({ω₀'} : Set ↥(nbrs α'))ᶜ) = 16 := by
    have h := Set.ncard_add_ncard_compl ({ω₀'} : Set ↥(nbrs α'))
    rw [Set.ncard_singleton, hN] at h
    rw [Nat.card_coe_set_eq]
    omega
  have hc1' : Nat.card ↥(Φ ∩ ({ω₀'} : Set ↥(nbrs α'))ᶜ) = Nat.card F - 1 := by
    rw [← Set.diff_eq, Nat.card_coe_set_eq, Set.ncard_diff_singleton_of_mem hω₀Φ,
      ← Nat.card_coe_set_eq, hcardF]
  rw [hc1, hc1'] at hdvd1
  have hdvd2 := hT'.card_fixed_sub_two_dvd hzα' hω₀ hμ₀ hν₀ h01 h02 h12
  rw [hN] at hdvd2
  exact not_dvd_sixteen_and_fifteen hf6 hf9 hdvd1 hdvd2

end CFSG.Quasithin.F112Crit

end
