module

public import CFSG.Milestones.ASVolI.F411.SwapRed

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

variable {E : Type} [Group E]

@[expose] def burnsideF411_ctr (H : Subgroup E) : Subgroup E :=
  H ⊓ Subgroup.centralizer (H : Set E)

theorem burnsideF411_mem_ctr {H : Subgroup E} {x : E} :
    x ∈ burnsideF411_ctr H ↔ x ∈ H ∧ ∀ h ∈ H, h * x = x * h := by
  unfold burnsideF411_ctr
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem burnsideF411_pCoreOf_eq_of_key [Finite E] {p : ℕ} [Fact p.Prime] {Gp M₁ M₂ : Subgroup E}
    (hN : Gp.Normal) {T : Subgroup E} (hTp : IsPGroup p T) (hTi : ¬ p ∣ T.index)
    (hT : T ≤ M₁ ⊓ M₂)
    (hkey : ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ (p ^ k) = 1 →
      (∀ b ∈ Gp ⊓ (M₁ ⊓ M₂), r * b * r⁻¹ * b⁻¹ ∈ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp)
    {M : Subgroup E} (hM : M₁ ⊓ M₂ ≤ M) :
    pCoreOf p M = pCoreOf p (Gp ⊓ M) := by
  have hMN : M ≤ Subgroup.normalizer (pCoreOf p M : Set E) := burnsideF411_le_normalizer_pCoreOf M
  have hRp : IsPGroup p (pCoreOf p M) := burnsideF411_pCoreOf_isPGroup M
  have hRT : pCoreOf p M ≤ T := by
    have hTS : IsSylowOf p T ⊤ := ⟨le_top, hTp, by rwa [Subgroup.relIndex_top_right]⟩
    have hp : IsPGroup p (pCoreOf p M ⊔ T : Subgroup E) :=
      IsPGroup.to_sup_of_normal_left' hRp hTp ((hT.trans hM).trans hMN)
    have heq := burnsideF411_eq_of_isSylowOf hTS le_sup_right le_top hp
    exact heq ▸ le_sup_left
  have hRB : pCoreOf p M ≤ M₁ ⊓ M₂ := hRT.trans hT
  have hRG : pCoreOf p M ≤ Gp := by
    intro r hr
    obtain ⟨k, hk⟩ := hRp ⟨r, hr⟩
    have hrk : r ^ (p ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    refine hkey r (hRB hr) k hrk fun b hb => ?_
    have hbM : b ∈ M := hM hb.2
    have hr' : r ∈ M₁ ⊓ M₂ := hRB hr
    have hc1 : r * b * r⁻¹ * b⁻¹ ∈ pCoreOf p M := by
      have h1 : b * r⁻¹ * b⁻¹ ∈ pCoreOf p M :=
        (Subgroup.mem_normalizer_iff.mp (hMN hbM) r⁻¹).mp ((pCoreOf p M).inv_mem hr)
      have := (pCoreOf p M).mul_mem hr h1
      simpa [mul_assoc] using this
    have hc2 : r * b * r⁻¹ * b⁻¹ ∈ Gp ⊓ (M₁ ⊓ M₂) := by
      refine ⟨Gp.mul_mem (hN.conj_mem _ hb.1 r) (Gp.inv_mem hb.1), ?_⟩
      exact (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem hr' hb.2)
        ((M₁ ⊓ M₂).inv_mem hr')) ((M₁ ⊓ M₂).inv_mem hb.2)
    have hle : pCoreOf p M ⊓ (Gp ⊓ (M₁ ⊓ M₂)) ≤ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)) := by
      refine burnsideF411_le_pCoreOf inf_le_right ?_ (hRp.to_le inf_le_left)
      refine burnsideF411_le_normalizer fun z hz s hs => ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hMN (hM hz.2)) s).mp hs.1
      · exact (Gp ⊓ (M₁ ⊓ M₂)).mul_mem ((Gp ⊓ (M₁ ⊓ M₂)).mul_mem hz hs.2)
          ((Gp ⊓ (M₁ ⊓ M₂)).inv_mem hz)
    exact hle ⟨hc1, hc2⟩
  apply le_antisymm
  · refine burnsideF411_le_pCoreOf (le_inf hRG (burnsideF411_pCoreOf_le M)) ?_ hRp
    exact inf_le_right.trans hMN
  · exact burnsideF411_le_pCoreOf ((burnsideF411_pCoreOf_le _).trans inf_le_right)
      (burnsideF411_le_normalizer_pCoreOf_inf p hN M) (burnsideF411_pCoreOf_isPGroup _)

theorem burnsideF411_map_pCoreOf_self {H : Subgroup E} (p : ℕ) (φ : ↥H →* E)
    (hφ : Function.Injective φ) (hr : φ.range = H) :
    (pCore p ↥H).map φ = pCoreOf p H := by
  let e : ↥H ≃* ↥H := (MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hr)
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  have h2 : H.subtype.comp e.toMonoidHom = φ := MonoidHom.ext fun _ => rfl
  unfold pCoreOf
  conv_rhs => rw [← h1]
  rw [Subgroup.map_map, h2]

theorem burnsideF411_ctr_ne_bot [Finite E] {p : ℕ} [Fact p.Prime] {H : Subgroup E}
    (hp : IsPGroup p H) (hH : H ≠ ⊥) : burnsideF411_ctr H ≠ ⊥ := by
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  have hp' : IsPGroup p ↥H := hp
  haveI := hp'.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center ↥H)
  intro hbot
  apply hz
  have hzc : ((z : ↥H) : E) ∈ burnsideF411_ctr H :=
    burnsideF411_mem_ctr.mpr ⟨(z : ↥H).2, fun h hh =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨h, hh⟩)⟩
  rw [hbot, Subgroup.mem_bot] at hzc
  exact Subtype.ext (Subtype.ext hzc)

theorem burnsideF411_parabolics_sup {p : ℕ} {Gp B P₁ P₂ : Subgroup E}
    (hP : IsLieParabolics p Gp B P₁ P₂) : P₁ ⊔ P₂ = Gp := by
  obtain ⟨-, hne, -, hmax⟩ := hP
  obtain ⟨-, hP₁Gp, hP₁ne, hP₁max⟩ := (hmax P₁).mpr (Or.inl rfl)
  obtain ⟨-, hP₂Gp, -, hP₂max⟩ := (hmax P₂).mpr (Or.inr rfl)
  have h21 : ¬ P₂ ≤ P₁ := fun h =>
    hP₁ne (hP₂max P₁ (lt_of_le_of_ne h fun h' => hne h'.symm) hP₁Gp)
  refine hP₁max _ (lt_of_le_of_ne le_sup_left fun h => h21 ?_) (sup_le hP₁Gp hP₂Gp)
  rw [h]
  exact le_sup_right

theorem burnsideF411_pCoreOf_borel_ne_bot [Finite E] {p : ℕ} [Fact p.Prime]
    {Gp B P₁ P₂ : Subgroup E} (hP : IsLieParabolics p Gp B P₁ P₂) : pCoreOf p B ≠ ⊥ := by
  obtain ⟨⟨S₀, hS₀, hBS⟩, -, -, hmax⟩ := hP
  obtain ⟨hBP₁, hP₁Gp, hP₁ne, -⟩ := (hmax P₁).mpr (Or.inl rfl)
  have hS₀B : S₀ ≤ B := hBS ▸ le_inf hS₀.1 Subgroup.le_normalizer
  have hS₀U : S₀ ≤ pCoreOf p B :=
    burnsideF411_le_pCoreOf hS₀B (hBS ▸ inf_le_right) hS₀.2.1
  intro hbot
  have hS₀bot : S₀ = ⊥ := le_bot_iff.mp (hbot ▸ hS₀U)
  apply hP₁ne
  refine le_antisymm hP₁Gp fun g hg => hBP₁ ?_
  rw [hBS, hS₀bot]
  refine ⟨hg, Subgroup.mem_normalizer_iff.mpr fun h => ?_⟩
  show h = 1 ↔ g * h * g⁻¹ = 1
  constructor
  · rintro rfl
    group
  · intro hh
    have := congrArg (fun x => g⁻¹ * x * g) hh
    simpa [mul_assoc] using this

theorem burnsideF411_swap_of_center [Finite E] {p : ℕ} [Fact p.Prime] {Gp M₁ M₂ : Subgroup E}
    (hN : Gp.Normal) (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h)
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hBT : burnsideF411_BorelTitsIn p Gp)
    (hB : pCoreOf p (M₁ ⊓ M₂) = pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)))
    (hZ : Gp ⊓ M₁ ≤
      Subgroup.normalizer (burnsideF411_ctr (pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))) : Set E)) :
    burnsideF411_Swap M₁ M₂ := by
  classical
  intro χ₁ χ₂ hχ₁ _ hr₁ hr₂ hagree
  exfalso
  have hsup := burnsideF411_parabolics_sup hP
  have hUne := burnsideF411_pCoreOf_borel_ne_bot hP
  set Bh : Subgroup E := M₁ ⊓ M₂ with hBh
  set U : Subgroup E := pCoreOf p (Gp ⊓ Bh) with hU
  set Z : Subgroup E := burnsideF411_ctr U with hZdef
  have hUp : IsPGroup p U := burnsideF411_pCoreOf_isPGroup _
  have hZU : Z ≤ U := fun z hz => (burnsideF411_mem_ctr.mp hz).1
  have hZB : Z ≤ Bh := fun z hz => (burnsideF411_pCoreOf_le _ (hZU hz)).2
  have hZG : Z ≤ Gp := fun z hz => (burnsideF411_pCoreOf_le _ (hZU hz)).1
  let φ : ↥Bh →* E := χ₁.comp (Subgroup.inclusion inf_le_left)
  have hφinj : Function.Injective φ :=
    hχ₁.comp (Subgroup.inclusion_injective inf_le_left)
  have hφle : φ.range ≤ Bh := by
    rintro _ ⟨x, rfl⟩
    refine ⟨?_, ?_⟩
    · have h1 : χ₂ (Subgroup.inclusion inf_le_right x) ∈ χ₂.range := ⟨_, rfl⟩
      rw [hr₂] at h1
      have h2 : φ x = χ₂ (Subgroup.inclusion inf_le_right x) := hagree x
      rw [h2]
      exact h1
    · have h1 : φ x ∈ χ₁.range := ⟨_, rfl⟩
      rwa [hr₁] at h1
  have hφr : φ.range = Bh := by
    refine Subgroup.eq_of_le_of_card_ge hφle ?_
    have : Nat.card ↥φ.range = Nat.card ↥Bh := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφinj, Subgroup.card_top]
    exact this.ge
  have hφU : (pCore p ↥Bh).map φ = U := by
    rw [burnsideF411_map_pCoreOf_self p φ hφinj hφr, hB]
  have hUle : ∀ u ∈ U, ∃ x : ↥Bh, x ∈ pCore p ↥Bh ∧ φ x = u := fun u hu => by
    rw [← hφU] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨x, hx, rfl⟩
  have hφZ : ∀ x : ↥Bh, (x : E) ∈ Z → φ x ∈ Z := by
    intro x hx
    have hxU : (x : E) ∈ pCoreOf p Bh := by rw [hB]; exact hZU hx
    obtain ⟨x', hx', hxx'⟩ := hxU
    have hxeq : x' = x := Subtype.ext hxx'
    subst hxeq
    refine burnsideF411_mem_ctr.mpr ⟨?_, fun u hu => ?_⟩
    · rw [← hφU]
      exact ⟨x', hx', rfl⟩
    · obtain ⟨y, hy, rfl⟩ := hUle u hu
      have hyU : (y : E) ∈ U := by rw [← hB]; exact ⟨y, hy, rfl⟩
      have hc := (burnsideF411_mem_ctr.mp hx).2 (y : E) hyU
      have : y * x' = x' * y := Subtype.ext hc
      rw [← map_mul, ← map_mul, this]
  have hBhZ : Bh ≤ Subgroup.normalizer (Z : Set E) := by
    have hBU : Bh ≤ Subgroup.normalizer (U : Set E) := by
      rw [← hB]
      exact burnsideF411_le_normalizer_pCoreOf Bh
    refine burnsideF411_le_normalizer fun y hy s hs => burnsideF411_mem_ctr.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hBU hy) s).mp (burnsideF411_mem_ctr.mp hs).1
    · intro u hu
      have hu' : y⁻¹ * u * y ∈ U := by
        have := (Subgroup.mem_normalizer_iff.mp (hBU (Bh.inv_mem hy)) u).mp hu
        simpa using this
      have hc := (burnsideF411_mem_ctr.mp hs).2 _ hu'
      calc u * (y * s * y⁻¹) = y * ((y⁻¹ * u * y) * s) * y⁻¹ := by group
        _ = y * (s * (y⁻¹ * u * y)) * y⁻¹ := by rw [hc]
        _ = y * s * y⁻¹ * u := by group
  have hM₁Z : M₁ ≤ Subgroup.normalizer (Z : Set E) := by
    intro m hm
    obtain ⟨n, hn, h, hh, rfl⟩ := hsplit m
    have hnM : n ∈ M₁ := by
      have := M₁.mul_mem hm (M₁.inv_mem hh.1)
      simpa using this
    exact Subgroup.mul_mem _ (hZ ⟨hn, hnM⟩) (hBhZ hh)
  have hZφ : ∀ z ∈ Z, ∃ x : ↥M₁, (x : E) ∈ Z ∧ χ₁ x = z := by
    intro z hz
    let ZB : Subgroup ↥Bh := Z.subgroupOf Bh
    have hmapZ : ZB.map φ = Z := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact hφZ x hx
      · rw [Subgroup.card_map_of_injective hφinj]
        exact le_of_eq (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv).symm
    rw [← hmapZ] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨Subgroup.inclusion inf_le_left x, hx, rfl⟩
  have hM₂Z : M₂ ≤ Subgroup.normalizer (Z : Set E) := by
    refine burnsideF411_le_normalizer fun y hy s hs => ?_
    rw [← hr₁] at hy
    obtain ⟨m, rfl⟩ := hy
    obtain ⟨x, hxZ, rfl⟩ := hZφ s hs
    have hmx : ((m * x * m⁻¹ : ↥M₁) : E) ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hM₁Z m.2) x).mp hxZ
    have h := hφZ ⟨((m * x * m⁻¹ : ↥M₁) : E), hZB hmx⟩ hmx
    have e : φ ⟨((m * x * m⁻¹ : ↥M₁) : E), hZB hmx⟩ = χ₁ (m * x * m⁻¹) := rfl
    rw [e, map_mul, map_mul, map_inv] at h
    exact h
  have hGZ : Gp ≤ Subgroup.normalizer (Z : Set E) := by
    rw [← hsup]
    exact sup_le (inf_le_right.trans hM₁Z) (inf_le_right.trans hM₂Z)
  have hZne : Z ≠ ⊥ := burnsideF411_ctr_ne_bot hUp hUne
  obtain ⟨-, -, P, hPG, hPne, hNP, -⟩ := hBT Z hZG hZne (hUp.to_le hZU)
  exact hPne (le_antisymm hPG fun g hg => hNP ⟨hg, hGZ hg⟩)

end CFSG.ASVolI
