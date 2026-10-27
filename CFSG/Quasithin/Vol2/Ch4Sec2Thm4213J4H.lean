module

public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213C2
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4D

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Quasithin.A4

namespace NoJ4

variable {G : Type} [Group G] [Finite G]

theorem exists_comm_eq (hBlk : J4BlockFacts) {T M L Mm I H K : Subgroup G}
    (hy : Hyp4_2_3 G T M L Mm I) (hIH : InM I H) (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) {r : G} (hrI : I ≤ Subgroup.centralizer ({r} : Set G))
    (hrR₁ : ∀ x ∈ pCoreOf 2 (L ⊔ T) ⊓ Subgroup.normalizer (pCoreOf 2 I : Set G),
      x * r * x⁻¹ * r⁻¹ ∈ pCoreOf 2 (perfectCore (L ⊓ H)))
    (hker : pCoreOf 2 (L ⊔ T) ⊓ Subgroup.normalizer (pCoreOf 2 I : Set G) ⊓
      Subgroup.centralizer ({r} : Set G) ≤ pCoreOf 2 I)
    (hlt : pCoreOf 2 I < pCoreOf 2 (L ⊔ T) ⊓ Subgroup.normalizer (pCoreOf 2 I : Set G)) :
    ∀ v ∈ pCoreOf 2 (perfectCore (L ⊓ H)), ∃ s ∈ pCoreOf 2 (L ⊔ T) ⊓
      Subgroup.normalizer (pCoreOf 2 I : Set G), s * r * s⁻¹ * r⁻¹ = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLH
  set E := pCoreOf 2 LH with hE
  set R := pCoreOf 2 I with hR
  set Rp := pCoreOf 2 (L ⊔ T) with hRp
  set R₁ := Rp ⊓ Subgroup.normalizer (R : Set G) with hR₁
  have hLHI : LH ≤ I := LH_le hy hIH c
  have hVE : ⁅reducedAggregate (L ⊔ T), L⁆ = E := v_eq hBlk c h6
  have hEZ : E ≤ centerOf Rp := by
    rw [← hVE]
    exact c.V_le_omega.trans (C1GN.omegaOneCenterOf_le_centerOf _)
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hEZ hb).2 a (hEZ ha).1
  let χ : ↥R₁ →* G :=
    { toFun := fun s => (s : G) * r * (s : G)⁻¹ * r⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have ha := hrR₁ a a.2
        have hb := hrR₁ b b.2
        have h1 : (a : G) * ((b : G) * r * (b : G)⁻¹ * r⁻¹) * (a : G)⁻¹ =
            (b : G) * r * (b : G)⁻¹ * r⁻¹ := by
          rw [Subgroup.mem_centralizer_iff.mp (hEZ hb).2 a a.2.1, mul_inv_cancel_right]
        calc ((a * b : ↥R₁) : G) * r * ((a * b : ↥R₁) : G)⁻¹ * r⁻¹
            = ((a : G) * ((b : G) * r * (b : G)⁻¹ * r⁻¹) * (a : G)⁻¹) *
                ((a : G) * r * (a : G)⁻¹ * r⁻¹) := by
              simp only [Subgroup.coe_mul]
              group
          _ = ((b : G) * r * (b : G)⁻¹ * r⁻¹) * ((a : G) * r * (a : G)⁻¹ * r⁻¹) := by rw [h1]
          _ = ((a : G) * r * (a : G)⁻¹ * r⁻¹) * ((b : G) * r * (b : G)⁻¹ * r⁻¹) :=
              hEab _ hb _ ha }
  have hχ : ∀ s : ↥R₁, χ s = (s : G) * r * (s : G)⁻¹ * r⁻¹ := fun _ => rfl
  have hWE : χ.range ≤ E := by
    rintro _ ⟨s, rfl⟩
    exact hrR₁ s s.2
  have hWN : LH ≤ Subgroup.normalizer (χ.range : Set G) := by
    intro l hl
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    obtain ⟨s, rfl⟩ := hw
    have hlI : l ∈ I := hLHI hl
    have hlr : l * r * l⁻¹ = r := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hrI hlI), mul_inv_cancel_right]
    have hls : l * (s : G) * l⁻¹ ∈ R₁ := by
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (L ⊔ T)
          (Subgroup.mem_sup_left ((perfectCore_le (L ⊓ H)).trans inf_le_left hl))) _).mp s.2.1
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (le_normalizer_pCoreOf 2 I hlI) s.2.2)
          (Subgroup.inv_mem _ (le_normalizer_pCoreOf 2 I hlI))
    refine ⟨⟨_, hls⟩, ?_⟩
    rw [hχ, hχ]
    calc l * (s : G) * l⁻¹ * r * (l * (s : G) * l⁻¹)⁻¹ * r⁻¹
        = l * (s : G) * l⁻¹ * (l * r * l⁻¹) * (l * (s : G) * l⁻¹)⁻¹ * (l * r * l⁻¹)⁻¹ := by
          rw [hlr]
      _ = l * ((s : G) * r * (s : G)⁻¹ * r⁻¹) * l⁻¹ := by group
  have hWne : χ.range ≠ ⊥ := by
    obtain ⟨y, hyR₁, hyR⟩ := IsConcreteLE.exists_of_lt hlt
    intro hbot
    have h1 : χ ⟨y, hyR₁⟩ ∈ χ.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot, hχ] at h1
    apply hyR
    refine hker ⟨hyR₁, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc y * r = (y * r * y⁻¹ * r⁻¹) * (r * y) := by group
      _ = r * y := by rw [h1, one_mul]
  rcases (blockFacts_of_case6 hBlk c h6).2.2.1 _ hWE hWN with h | h
  · exact absurd h hWne
  · intro v hv
    have h' : χ.range = E := h
    rw [← h'] at hv
    obtain ⟨s, rfl⟩ := hv
    exact ⟨s, s.2, rfl⟩

theorem exists_mem_centralizer_comm_eq {R R₁ : Subgroup G} {r x v s₀ : G}
    (hR2 : IsPGroup 2 ↥R) (hRR₁ : R ≤ R₁) (hRr : R ≤ Subgroup.centralizer ({r} : Set G))
    (hker : R₁ ⊓ Subgroup.centralizer ({r} : Set G) ≤ R) (hx3 : orderOf x = 3)
    (hxR₁ : x ∈ Subgroup.normalizer (R₁ : Set G)) (hxr : x * r = r * x) (hxv : x * v = v * x)
    (hs₀ : s₀ ∈ R₁) (hs₀v : s₀ * r * s₀⁻¹ * r⁻¹ = v) :
    ∃ s ∈ R₁, s * x = x * s ∧ s * r * s⁻¹ * r⁻¹ = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := Subgroup.zpowers x with hP
  have hPN : P ≤ Subgroup.normalizer (R₁ : Set G) := Subgroup.zpowers_le.mpr hxR₁
  have hPr : ∀ g ∈ P, g * r * g⁻¹ = r := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [((Commute.zpow_left (hxr : Commute x r) k) : x ^ k * r = r * x ^ k),
      mul_inv_cancel_right]
  have hPv : ∀ g ∈ P, g * v * g⁻¹ = v := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [((Commute.zpow_left (hxv : Commute x v) k) : x ^ k * v = v * x ^ k),
      mul_inv_cancel_right]
  let α := {s : G // s ∈ R₁ ∧ s * r * s⁻¹ * r⁻¹ = v}
  have hmem : ∀ g ∈ P, ∀ s : α, g * s.1 * g⁻¹ ∈ R₁ ∧
      (g * s.1 * g⁻¹) * r * (g * s.1 * g⁻¹)⁻¹ * r⁻¹ = v := by
    intro g hg s
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hPN hg) _).mp s.2.1, ?_⟩
    calc (g * s.1 * g⁻¹) * r * (g * s.1 * g⁻¹)⁻¹ * r⁻¹
        = (g * s.1 * g⁻¹) * (g * r * g⁻¹) * (g * s.1 * g⁻¹)⁻¹ * (g * r * g⁻¹)⁻¹ := by
          rw [hPr g hg]
      _ = g * (s.1 * r * s.1⁻¹ * r⁻¹) * g⁻¹ := by group
      _ = v := by rw [s.2.2, hPv g hg]
  let _ : MulAction ↥P α :=
    { smul := fun g s => ⟨(g : G) * s.1 * (g : G)⁻¹, hmem g g.2 s⟩
      one_smul := fun s => Subtype.ext (show ((1 : ↥P) : G) * s.1 * ((1 : ↥P) : G)⁻¹ = s.1 by
        simp)
      mul_smul := fun g h s => Subtype.ext (show ((g * h : ↥P) : G) * s.1 * ((g * h : ↥P) : G)⁻¹ =
          (g : G) * ((h : G) * s.1 * (h : G)⁻¹) * (g : G)⁻¹ by
        simp only [Subgroup.coe_mul]
        group) }
  have hP3 : IsPGroup 3 ↥P := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3, pow_one])
  have h1 : ∀ s : α, s₀⁻¹ * s.1 ∈ R := by
    intro s
    apply hker
    refine ⟨R₁.mul_mem (R₁.inv_mem hs₀) s.2.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have e1 : s.1 * r * s.1⁻¹ = s₀ * r * s₀⁻¹ := mul_right_cancel (s.2.2.trans hs₀v.symm)
    calc s₀⁻¹ * s.1 * r = s₀⁻¹ * (s.1 * r * s.1⁻¹) * s.1 := by group
      _ = s₀⁻¹ * (s₀ * r * s₀⁻¹) * s.1 := by rw [e1]
      _ = r * (s₀⁻¹ * s.1) := by group
  have h2 : ∀ ρ : ↥R, s₀ * ρ ∈ R₁ ∧ (s₀ * ρ) * r * (s₀ * ρ)⁻¹ * r⁻¹ = v := by
    intro ρ
    refine ⟨R₁.mul_mem hs₀ (hRR₁ ρ.2), ?_⟩
    have hρr : (ρ : G) * r = r * ρ := Subgroup.mem_centralizer_singleton_iff.mp (hRr ρ.2)
    calc (s₀ * ρ) * r * (s₀ * ρ)⁻¹ * r⁻¹ = s₀ * ((ρ : G) * r) * (ρ : G)⁻¹ * s₀⁻¹ * r⁻¹ := by
          group
      _ = s₀ * (r * ρ) * (ρ : G)⁻¹ * s₀⁻¹ * r⁻¹ := by rw [hρr]
      _ = s₀ * r * s₀⁻¹ * r⁻¹ := by group
      _ = v := hs₀v
  have hcard : Nat.card α = Nat.card ↥R := Nat.card_congr
    { toFun := fun s => ⟨s₀⁻¹ * s.1, h1 s⟩
      invFun := fun ρ => ⟨s₀ * ρ, h2 ρ⟩
      left_inv := fun s => Subtype.ext (by simp)
      right_inv := fun ρ => Subtype.ext (by simp) }
  have hndvd : ¬ 3 ∣ Nat.card α := by
    rw [hcard]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  obtain ⟨⟨s, hsR₁, hsv⟩, hfix⟩ := hP3.nonempty_fixed_point_of_prime_not_dvd_card α hndvd
  have hxs : x * s * x⁻¹ = s :=
    congrArg Subtype.val (hfix (⟨x, Subgroup.mem_zpowers x⟩ : ↥P))
  refine ⟨s, hsR₁, ?_, hsv⟩
  calc s * x = (x * s * x⁻¹) * x := by rw [hxs]
    _ = x * s := by group

end NoJ4

end CFSG.Quasithin.H13.Ch4
