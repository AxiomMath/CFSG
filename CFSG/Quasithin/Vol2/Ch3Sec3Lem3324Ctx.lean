module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324Main
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.CZL32 CFSG.Quasithin.H13.X3324
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

namespace Ctx3324

variable {G : Type} [Group G]

section Coords

variable {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)

@[expose] noncomputable def z2Coords (k : ℕ) :
    Multiplicative (Fin k → Fin 3 → F) →* Multiplicative (Fin k → L3.Vec) :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.compLeft
    (AddMonoidHom.compLeft (Mod3323.toZ2 hF).toAddMonoidHom (Fin 3)) (Fin k))

theorem toAdd_z2Coords {k : ℕ} (x : Multiplicative (Fin k → Fin 3 → F)) (i : Fin k) :
    Multiplicative.toAdd (z2Coords hF k x) i = Mod3323.toZ2 hF ∘ Multiplicative.toAdd x i :=
  rfl

theorem z2Coords_injective (k : ℕ) : Function.Injective (z2Coords hF k) := by
  intro x y hxy
  apply Multiplicative.toAdd.injective
  funext i j
  have := congrFun (congrFun (congrArg Multiplicative.toAdd hxy) i) j
  exact (Mod3323.toZ2 hF).injective this

theorem z2Coords_surjective (k : ℕ) : Function.Surjective (z2Coords hF k) := by
  intro y
  refine ⟨Multiplicative.ofAdd fun i j => (Mod3323.toZ2 hF).symm (Multiplicative.toAdd y i j), ?_⟩
  apply Multiplicative.toAdd.injective
  funext i j
  show Mod3323.toZ2 hF ((Mod3323.toZ2 hF).symm (Multiplicative.toAdd y i j)) = _
  rw [RingEquiv.apply_symm_apply]

@[expose] noncomputable def alpha3 {L : Subgroup G}
    (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) : ↥L →* L3.Γ :=
  (Mod3323.toL3 hF).comp
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.toMonoidHom.comp α)

variable {L : Subgroup G} {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}

theorem alpha3_surjective (hα : Function.Surjective α) : Function.Surjective (alpha3 hF α) := by
  intro γ
  obtain ⟨g, rfl⟩ := Mod3323.toL3_surjective hF γ
  obtain ⟨ℓ, hℓ⟩ := hα (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F g)
  refine ⟨ℓ, ?_⟩
  simp only [alpha3, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hℓ,
    MulEquiv.symm_apply_apply]

theorem alpha3_eq_one (ℓ : ↥L) : alpha3 hF α ℓ = 1 ↔ α ℓ = 1 := by
  simp only [alpha3, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [map_eq_one_iff _ (Mod3323.toL3_injective hF), MulEquiv.map_eq_one_iff]

theorem act_alpha3 (ℓ : ↥L) (x : Fin 3 → F) :
    L3.act (alpha3 hF α ℓ) (Mod3323.toZ2 hF ∘ x) =
      Mod3323.toZ2 hF ∘ ((α ℓ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x := by
  have hm' : (((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm (α ℓ) :
      Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((α ℓ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 F
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm (α ℓ))
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  rw [← hm']
  exact Mod3323.act_toL3 hF _ x

theorem mem_of_alpha3 (hα : IsModO2Surj L α) (ℓ : ↥L) (h1 : alpha3 hF α ℓ = 1) :
    (ℓ : G) ∈ pCoreOf 2 L := by
  have h2 : ℓ ∈ α.ker := (alpha3_eq_one hF ℓ).mp h1
  rw [hα.2] at h2
  exact (Lem3328.mem_pCore_iff ℓ).mp h2

theorem z2_equiv {V : Subgroup G} {k : ℕ} (β : ↥V →* Multiplicative (Fin k → Fin 3 → F))
    (hβe : ∀ (a : ↥L) (u v : ↥V), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (α a : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i))
    (a : ↥L) (u v : ↥V) (huv : (v : G) = a * u * a⁻¹) (i : Fin k) :
    Multiplicative.toAdd ((z2Coords hF k).comp β v) i =
      L3.act (alpha3 hF α a) (Multiplicative.toAdd ((z2Coords hF k).comp β u) i) := by
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, toAdd_z2Coords, toAdd_z2Coords, act_alpha3,
    hβe a u v huv i]
  rfl

end Coords

section Natural

variable {L W : Subgroup G} (β : ↥W ≃* Multiplicative L3.Vec) (α₃ : ↥L →* L3.Γ)

theorem exists_conj_eq (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hα₃s : Function.Surjective α₃)
    (hβe : ∀ (ℓ : ↥L) (u v : ↥W), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) = L3.act (α₃ ℓ) (Multiplicative.toAdd (β u)))
    {z₀ : G} (hz₀W : z₀ ∈ W) (hz₀ : z₀ ≠ 1) {q : G} (hq : q ∈ W) :
    q = 1 ∨ ∃ ℓ ∈ L, q = ℓ * z₀ * ℓ⁻¹ := by
  by_cases hq1 : q = 1
  · exact Or.inl hq1
  right
  have hne : ∀ {u : G} (hu : u ∈ W), u ≠ 1 → Multiplicative.toAdd (β ⟨u, hu⟩) ≠ 0 :=
    fun hu hu1 h0 => hu1 (congrArg Subtype.val (eq_of_toAdd_beta β (u := ⟨_, hu⟩) (u' := 1)
      (by rw [toAdd_beta_one]; exact h0)))
  obtain ⟨g, hg⟩ := trans_check _ _ (hne hz₀W hz₀) (hne hq hq1)
  obtain ⟨ℓ, rfl⟩ := hα₃s g
  have h1 : (ℓ : G) * z₀ * (ℓ : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hLW ℓ.2) z₀).mp hz₀W
  have h2 : (⟨_, h1⟩ : ↥W) = ⟨q, hq⟩ :=
    eq_of_toAdd_beta β (by rw [hβe ℓ ⟨z₀, hz₀W⟩ ⟨_, h1⟩ rfl, hg])
  exact ⟨ℓ, ℓ.2, (congrArg Subtype.val h2).symm⟩

theorem le_of_conj_z₀ (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hα₃s : Function.Surjective α₃)
    (hβe : ∀ (ℓ : ↥L) (u v : ↥W), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) = L3.act (α₃ ℓ) (Multiplicative.toAdd (β u)))
    {z₀ : G} (hz₀W : z₀ ∈ W) (hz₀ : z₀ ≠ 1) {K : Subgroup G} (hz₀K : z₀ ∈ K)
    (hLK : L ≤ Subgroup.normalizer (K : Set G)) : W ≤ K := by
  intro q hq
  rcases exists_conj_eq β α₃ hLW hα₃s hβe hz₀W hz₀ hq with rfl | ⟨ℓ, hℓ, rfl⟩
  · exact K.one_mem
  · exact (Subgroup.mem_normalizer_iff.mp (hLK hℓ) z₀).mp hz₀K

theorem le_normalizer_of_trans {T : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hα₃s : Function.Surjective α₃)
    (hβe : ∀ (ℓ : ↥L) (u v : ↥W), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) = L3.act (α₃ ℓ) (Multiplicative.toAdd (β u)))
    {z₀ : G} (hz₀W : z₀ ∈ W) (hz₀ : z₀ ≠ 1) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTz : ∀ t ∈ T, t * z₀ * t⁻¹ = z₀) : T ≤ Subgroup.normalizer (W : Set G) := by
  refine Main3324.le_normalizer_of_conj fun t ht q hq => ?_
  rcases exists_conj_eq β α₃ hLW hα₃s hβe hz₀W hz₀ hq with rfl | ⟨ℓ, hℓ, rfl⟩
  · rw [mul_one, mul_inv_cancel]
    exact W.one_mem
  · have hℓ' : t * ℓ * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hTL ht) ℓ).mp hℓ
    have e : t * (ℓ * z₀ * ℓ⁻¹) * t⁻¹ = (t * ℓ * t⁻¹) * (t * z₀ * t⁻¹) * (t * ℓ * t⁻¹)⁻¹ := by
      group
    rw [e, hTz t ht]
    exact (Subgroup.mem_normalizer_iff.mp (hLW hℓ') z₀).mp hz₀W

end Natural

theorem fix_of_odd {K T : Subgroup G} (f : ↥K →* L3.Γ) (hTK : T ≤ K) (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hf : Function.Surjective f) {e v : L3.Vec} (he : e ≠ 0)
    (hfe : ∀ t (ht : t ∈ T), L3.act (f ⟨t, hTK ht⟩) e = e)
    (hfv : ∀ t (ht : t ∈ T), L3.act (f ⟨t, hTK ht⟩) v = v) : v = 0 ∨ v = e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := (T.subgroupOf K).map f with hI
  have hI2 : IsPGroup 2 I := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm).map f
  have hodd : ¬ 2 ∣ I.index := by
    have h1 := Subgroup.index_map_dvd (T.subgroupOf K) hf
    exact fun h3 => hTidx ((h3.trans h1).trans (Subgroup.relIndex_dvd_index_of_le hTK))
  obtain ⟨e', he'⟩ := Mod3323.exists_fix hI2 hodd
  have hfix : ∀ w, (∀ t (ht : t ∈ T), L3.act (f ⟨t, hTK ht⟩) w = w) →
      ∀ g ∈ I, L3.act g w = w := by
    rintro w hw _ ⟨y, hy, rfl⟩
    exact hw y hy
  rcases he' e (hfix e hfe) with h0 | h1
  · exact absurd h0 he
  · rw [h1]
    exact he' v (hfix v hfv)

theorem ncAtMost_inf [Finite G] {X A B : Subgroup G} {c : ℕ} (hAB : A ≤ B)
    (h : A.relIndex B < 4 ^ (c + 1)) : NCAtMost X (X ⊓ A) (X ⊓ B) c := by
  refine ncAtMost_of_relIndex_lt (lt_of_le_of_lt ?_ h)
  have e1 : X ⊓ A = A ⊓ (X ⊓ B) := by
    ext y
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.2, h.1, hAB h.2⟩, fun h => ⟨h.2.1, h.1⟩⟩
  rw [e1, Subgroup.inf_relIndex_right]
  exact Subgroup.relIndex_le_of_le_right inf_le_right
    (show (A.subgroupOf B).index ≠ 0 from Subgroup.index_ne_zero_of_finite)

variable [Finite G] {T M L D : Subgroup G}

theorem z_decomp (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G)) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) :
    ∃ u ∈ quasithinOmegaOneCenter T ⊓ ⁅vPlus L T, L⁆,
      ∃ c ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G), z = u * c := by
  set Z := quasithinOmegaOneCenter T with hZdef
  have hMp := Hyp331.mPlus_eq_of_le hTL
  obtain ⟨-, hV4⟩ := Hyp331.vPlus_decomp h
  rw [hMp] at hV4
  have hZV : Z ≤ vPlus L T := le_conjClosure _ _
  have hCZU : Z ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := fun c hc =>
    Main3324.mem_normalizer_comm (Subgroup.le_normalizer (hZV hc.1))
      (Subgroup.centralizer_le_normalizer _ hc.2)
  have h1 : z ∈ ⁅vPlus L T, L⁆ ⊔ Z ⊓ Subgroup.centralizer (L : Set G) := by
    have h2 := hZV hz
    rwa [hV4] at h2
  obtain ⟨u, hu, c, hc, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCZU).mp h1
  refine ⟨u, ⟨?_, hu⟩, c, hc, rfl⟩
  have := Z.mul_mem hz (Z.inv_mem hc.1)
  rwa [mul_inv_cancel_right] at this

theorem exists_z₀
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ z₀ ∈ quasithinOmegaOneCenter T ⊓ ⁅vPlus L T, L⁆, z₀ ≠ 1 := by
  set Z := quasithinOmegaOneCenter T with hZdef
  by_contra hcon
  push Not at hcon
  apply h.not_L_le_centralizer h38 h39
  have hZL : Z ≤ Subgroup.centralizer (L : Set G) := by
    intro z hz
    obtain ⟨u, hu, c, hc, rfl⟩ := z_decomp h hTL hz
    rw [hcon u hu, one_mul]
    exact hc.2
  have hMp := Hyp331.mPlus_eq_of_le hTL
  have hVc : vPlus L T ≤ Subgroup.centralizer (L : Set G) := by
    show conjClosure Z (mPlus L T) ≤ _
    rw [hMp]
    refine conjClosure_le fun ℓ hℓ z hz => ?_
    have h1 := Subgroup.mem_centralizer_iff.mp (hZL hz) ℓ hℓ
    have e : ℓ * z * ℓ⁻¹ = z := by rw [h1]; group
    rw [e]
    exact hZL hz
  exact Subgroup.le_centralizer_iff.mp hVc

theorem vL_le (h : Hyp331 G T M L D) :
    ⁅vPlus L T, L⁆ ≤ c134Q (L ⊔ T) L ⊓ Subgroup.centralizer (qL L T : Set G) := by
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) :=
    (le_conjClosure L T).trans (le_normalizer_conjClosure _ _)
  exact le_inf (Subgroup.commutator_mono (hred.1.trans inf_le_left) le_rfl)
    ((commutator_le_left_of_le_normalizer hLV).trans (hred.1.trans inf_le_right))

theorem centZ (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G)) {y : G}
    (hy : y ∈ L) (hyZ : ∀ u ∈ quasithinOmegaOneCenter T ⊓ ⁅vPlus L T, L⁆, y * u * y⁻¹ = u) :
    y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨u, hu, c, hc, rfl⟩ := z_decomp h hTL hz
  have hcy : c * y = y * c := (Subgroup.mem_centralizer_iff.mp hc.2 y hy).symm
  have hyu : u * y = y * u := by
    have := hyZ u hu
    calc u * y = (y * u * y⁻¹) * y := by rw [this]
      _ = y * u := by group
  calc u * c * y = u * (c * y) := mul_assoc _ _ _
    _ = u * (y * c) := by rw [hcy]
    _ = (u * y) * c := (mul_assoc _ _ _).symm
    _ = (y * u) * c := by rw [hyu]
    _ = y * (u * c) := mul_assoc _ _ _

theorem xStructU (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (hWq : W ≤ qL L T)
    (hqW : qL L T ≤ Subgroup.centralizer (W : Set G)) (β : ↥W ≃* Multiplicative L3.Vec)
    (α₃ : ↥L →* L3.Γ) (hα₃s : Function.Surjective α₃)
    (hα₃k : ∀ ℓ : ↥L, α₃ ℓ = 1 → (ℓ : G) ∈ pCoreOf 2 L)
    (hβe : ∀ (ℓ : ↥L) (u v : ↥W), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) = L3.act (α₃ ℓ) (Multiplicative.toAdd (β u)))
    {z₀ : G} (hz₀W : z₀ ∈ W) (hz₀Z : z₀ ∈ quasithinOmegaOneCenter T) (hz₀ : z₀ ≠ 1)
    (hZ : ∀ y (hy : y ∈ L), L3.act (α₃ ⟨y, hy⟩) (Multiplicative.toAdd (β ⟨z₀, hz₀W⟩)) =
      Multiplicative.toAdd (β ⟨z₀, hz₀W⟩) →
        y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ∃ σ : L3.Γ, ∃ X : Subgroup G, oTwoUpper X = X ∧ T ≤ Subgroup.normalizer (X : Set G) ∧
      Nonempty (↥(X ⊔ T) ⧸ CFSG.pCore 2 ↥(X ⊔ T) ≃* Equiv.Perm (Fin 3)) ∧
      X ⊔ T = L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T ∧
      X ≤ L ∧ X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
      W ≤ ⁅W, X⁆ ∧ W ≤ pCoreOf 2 X ∧
      (∀ W' : Subgroup G, W' ≤ W → z₀ ∈ W' → X ≤ Subgroup.normalizer (W' : Set G) →
        (∃ w ∈ W', w ∉ Subgroup.zpowers z₀) → W ≤ W') ∧
      (∃ r₀ ∈ pCoreOf 2 X, ∃ v₀ ∈ pCoreOf 2 X, ⁅r₀, v₀⁆ = z₀) ∧
      (∃ v₁ ∈ W, v₁ ∉ Subgroup.zpowers z₀ ∧ ∀ t ∈ T, ⁅v₁, t⁆ ∈ Subgroup.zpowers z₀) ∧
      (∀ γ ∈ rSub, ∃ r ∈ ⁅pCoreOf 2 X, X⁆, ∃ hr : r ∈ L, α₃ ⟨r, hr⟩ = σ⁻¹ * γ * σ) ∧
      NCAtMost X (X ⊓ pCoreOf 2 L) X 1 := by
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  obtain ⟨σ, hσ⟩ := exists_twist hTW hT2 β
  have hρα : ∀ ℓ (hℓ : ℓ ∈ L), rhoV β ⟨ℓ, hLW hℓ⟩ = α₃ ⟨ℓ, hℓ⟩ :=
    fun ℓ hℓ => rhoV_eq β hLW α₃ hβe ⟨ℓ, hℓ⟩
  have hρL : ∀ γ : L3.Γ, ∃ ℓ, ∃ hℓ : ℓ ∈ L,
      rhoV (β.trans (actEquiv σ)) ⟨ℓ, hLW hℓ⟩ = γ := by
    intro γ
    obtain ⟨ℓ, hℓ⟩ := hα₃s (σ⁻¹ * γ * σ)
    refine ⟨ℓ, ℓ.2, ?_⟩
    rw [rhoV_twist, hρα ℓ ℓ.2, show (⟨(ℓ : G), ℓ.2⟩ : ↥L) = ℓ from rfl, hℓ]
    group
  have hρK : ∀ ℓ (hℓ : ℓ ∈ L), rhoV (β.trans (actEquiv σ)) ⟨ℓ, hLW hℓ⟩ = 1 →
      ℓ ∈ pCoreOf 2 L := by
    intro ℓ hℓ h1
    apply hα₃k ⟨ℓ, hℓ⟩
    rw [rhoV_twist, hρα ℓ hℓ] at h1
    calc α₃ ⟨ℓ, hℓ⟩ = σ⁻¹ * (σ * α₃ ⟨ℓ, hℓ⟩ * σ⁻¹) * σ := by group
      _ = 1 := by rw [h1]; group
  have hsurj : Function.Surjective (rhoV (β.trans (actEquiv σ))) := fun γ => by
    obtain ⟨ℓ, hℓ, e⟩ := hρL γ
    exact ⟨_, e⟩
  have hTZ : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hcz : ∀ t ∈ T, t * z₀ * t⁻¹ = z₀ := fun t ht => by
    have := Subgroup.mem_centralizer_iff.mp (hTZ ht) z₀ hz₀Z
    rw [← this]
    group
  have hθz : Multiplicative.toAdd ((β.trans (actEquiv σ)) ⟨z₀, hz₀W⟩) = e1 := by
    rcases fix_T (rhoV (β.trans (actEquiv σ))) hTW hTidx hσ hsurj
        (v := Multiplicative.toAdd ((β.trans (actEquiv σ)) ⟨z₀, hz₀W⟩))
        (fun t ht => act_rhoV_of_conj _ (g := ⟨t, hTW ht⟩) (u := ⟨z₀, hz₀W⟩) (hcz t ht))
      with h0 | h1
    · exact absurd (congrArg Subtype.val (eq_of_toAdd_beta (β.trans (actEquiv σ))
        (u := ⟨z₀, hz₀W⟩) (u' := 1) (by rw [toAdd_beta_one]; exact h0))) hz₀
    · exact h1
  have hZ' : ∀ y (hy : y ∈ L), L3.act (rhoV (β.trans (actEquiv σ)) ⟨y, hLW hy⟩) e1 = e1 →
      y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro y hy h1
    apply hZ y hy
    rw [← hθz, toAdd_actEquiv, rhoV_twist, hρα y hy, L3.act_mul, L3.act_mul,
      L3.act_inv_act] at h1
    have h2 := congrArg (L3.act σ⁻¹) h1
    rwa [L3.act_inv_act, L3.act_inv_act] at h2
  obtain ⟨X, hXX, hTX, hS3, hXTe, hXL, hXZ, hWXc, hWO, hirr, hcomm, hv₁, hliftC, hNC⟩ :=
    xStruct h hTL hLW hTW hWq hqW (β.trans (actEquiv σ)) hσ hρL hρK hz₀W hz₀Z hz₀ hZ'
  refine ⟨σ, X, hXX, hTX, hS3, hXTe, hXL, hXZ, hWXc, hWO, hirr, hcomm, hv₁, fun γ hγ => ?_, hNC⟩
  obtain ⟨r, hr, hrL, e⟩ := hliftC γ hγ
  refine ⟨r, hr, hrL, ?_⟩
  rw [rhoV_twist, hρα r hrL] at e
  rw [← e]
  group

omit [Finite G] in
theorem le_pCoreOf_sup {X Q : Subgroup G} (hQT : Q ≤ T)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (hTQ : T ≤ Subgroup.normalizer (Q : Set G))
    (hQ2 : IsPGroup 2 Q) : Q ≤ pCoreOf 2 (X ⊔ T) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
    (sup_le hXQ hTQ) hQ2

end Ctx3324

end CFSG.Quasithin.H13
