module

public import CFSG.Quasithin.Vol2.KGFactHeInspCore
public import CFSG.Quasithin.Vol2.KGFactAutSylowJ4
public import CFSG.Quasithin.Vol2.KGFact3312J1

public section

namespace CFSG.Quasithin.H13.KGInsp

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KGH91 CFSG.Blueprint
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open CFSG.ComponentClassification.OuterAutomorphisms
open Matrix

@[expose] def InnerOn (m : ℕ) {X : Type} [Group X] (N Y : Subgroup X) : Prop :=
  ∀ ρ : ↥Y →* SpecialLinearGroup (Fin m) (ZMod 2), Function.Surjective ρ → IsPGroup 2 ρ.ker →
    ∀ t ∈ N, ∃ y₀ : Y, ∀ y y' : Y, (y' : X) = t * y * t⁻¹ → ρ y' = ρ (y₀ * y * y₀⁻¹)

@[expose] def KGJ4SylowOvergroups : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.Carrier .J4) →
    (∀ N Y : Subgroup X, (∃ R : Subgroup X, IsSylowTwoOf R ⊤ ∧ R ≤ N) → 7 ∣ Nat.card N →
      N ≠ ⊤ → Y ≤ N → N ≤ Subgroup.normalizer (Y : Set X) → InnerOn 3 N Y) ∧
    (∀ N Y : Subgroup X, pCoreOf 2 Y ≠ ⊥ → Y ≤ N → N ≤ Subgroup.normalizer (Y : Set X) →
      InnerOn 4 N Y)

variable {X : Type} [Group X] {n : ℕ}

theorem exists_ne_one_of_natCoord {Y W : Subgroup X} (hn : 1 ≤ n) (C : NatCoord Y W n) :
    ∃ a ∈ W, a ≠ 1 := by
  obtain ⟨a, ha, hE⟩ := C.surj (Pi.single ⟨0, hn⟩ 1)
  refine ⟨a, ha, fun h => ?_⟩
  rw [h, C.E_one] at hE
  have := congrFun hE ⟨0, hn⟩
  simp at this

theorem false_of_innerOn (hn : 3 ≤ n) {Y W₁ W₂ : Subgroup X} (C₁ : NatCoord Y W₁ n)
    (C₂ : NatCoord Y W₂ n) (hdual : ∀ y, C₂.ρ y = slGraphAut n (ZMod 2) (C₁.ρ y)) {t : X}
    (htN : t ∈ Subgroup.normalizer (Y : Set X)) (ht : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₂) (y₀ : Y)
    (hy₀ : ∀ y y' : Y, (y' : X) = t * y * t⁻¹ → C₁.ρ y' = C₁.ρ (y₀ * y * y₀⁻¹)) : False := by
  set c := (y₀ : X)⁻¹ * t with hc
  have hconjY : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp htN y).mp hy
  have hfW : ∀ a ∈ W₁, c * a * c⁻¹ ∈ W₂ := by
    intro a ha
    have h1 := C₂.conj_mem ⟨(y₀ : X)⁻¹, Y.inv_mem y₀.2⟩ (ht a ha)
    have e : c * a * c⁻¹ = (y₀ : X)⁻¹ * (t * a * t⁻¹) * ((y₀ : X)⁻¹)⁻¹ := by rw [hc]; group
    rw [e]
    exact h1
  have hfl : ∀ (l : ↥Y), ∀ a ∈ W₁, c * ((l : X) * a * (l : X)⁻¹) * c⁻¹ =
      (l : X) * (c * a * c⁻¹) * (l : X)⁻¹ := by
    intro l a ha
    set l'' : Y := ⟨t * l * t⁻¹, hconjY l l.2⟩ with hl''
    have hρ'' : C₁.ρ l'' = C₁.ρ (y₀ * l * y₀⁻¹) := hy₀ l l'' rfl
    set l' : Y := y₀⁻¹ * l'' * y₀ with hl'
    have hl'X : (l' : X) = c * l * c⁻¹ := by
      rw [hl', hl'', hc]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hρ' : C₁.ρ l' = C₁.ρ l := by
      rw [hl', map_mul, map_mul, hρ'', map_mul, map_mul, map_inv]
      group
    have hρ₂ : C₂.ρ l' = C₂.ρ l := by rw [hdual, hdual, hρ']
    have hb : c * a * c⁻¹ ∈ W₂ := hfW a ha
    have hact : (l' : X) * (c * a * c⁻¹) * (l' : X)⁻¹ = (l : X) * (c * a * c⁻¹) * (l : X)⁻¹ :=
      C₂.inj _ (C₂.conj_mem l' hb) _ (C₂.conj_mem l hb) (by
        rw [C₂.conj l' _ hb, C₂.conj l _ hb, hρ₂])
    rw [← hact, hl'X]
    group
  have h1 := NatCoord.eq_one_of_dual C₁ hn hdual hfW (fun a _ b _ => by group) hfl
  obtain ⟨a, ha, hne⟩ := exists_ne_one_of_natCoord (by omega) C₁
  apply hne
  have h2 := h1 a ha
  have : a = c⁻¹ * (c * a * c⁻¹) * c := by group
  rw [this, h2]
  group

theorem all_inner_of_maps_inner {G : Type} [Group G] [Finite G]
    (h : ∀ P : Subgroup G, IsSylowTwoOf P ⊤ → ∀ α : MulAut G, (∀ x ∈ P, α x ∈ P) → α ∈ inner G)
    (α : MulAut G) : ∃ g : G, α = MulAut.conj g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hP := KG3312.isSylowTwoOf_map_equiv α (isSylowTwoOf_top_of_sylow P₀)
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hp.toSylow hi) P₀
  have hmap : ((P₀ : Subgroup G).map α.toMonoidHom).map (MulAut.conj g).toMonoidHom = P₀ := by
    have := congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) hg
    simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at this
    exact Eq.trans rfl this
  have hγ : MulAut.conj g * α ∈ inner G := by
    refine h (P₀ : Subgroup G) (isSylowTwoOf_top_of_sylow P₀) _ fun x hx => ?_
    rw [← hmap]
    exact ⟨α x, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨k, hk⟩ := hγ
  refine ⟨g⁻¹ * k, ?_⟩
  rw [map_mul, hk, map_inv, inv_mul_cancel_left]

open CFSG.Sporadic.J4 in
theorem j4_all_inner
    {Q : Type} [Group Q] (e : Q ≃* J) (α : MulAut Q) :
    ∃ g, α = MulAut.conj g := by
  have hfin : Finite J := Finite.of_equiv _ (seedEquiv j4Facts.mat).toEquiv
  have hJ : ∀ β : MulAut J, ∃ g : J, β = MulAut.conj g := fun β =>
    @all_inner_of_maps_inner J (Subgroup.toGroup _) hfin
      (fun P hP γ hγ => KGAutSyl.j4_maps_inner P hP γ hγ) β
  exact @KG3312.exists_conj_of_mulEquiv Q J _ (Subgroup.toGroup _) e hJ α

theorem heInspJ4_of
    (h : KGJ4SylowOvergroups) : HeInspJ4 := by
  have : Finite (NativeSporadic.Carrier .J4) := CFSG.Sporadic.J4.fam_j4_simplicity.1
  suffices key : ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.Carrier .J4) →
      ¬ HeInspCfg X 3 ∧ ¬ HeInspCfg X 4 from key _ ⟨MulEquiv.refl _⟩
  intro X _ _ hX
  obtain ⟨e⟩ := hX
  let eJ : X ≃* CFSG.Sporadic.J4.J :=
    e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  have hJcard : Nat.card CFSG.Sporadic.J4.J = 86775571046077562880 :=
    CFSG.Sporadic.J4.card_J CFSG.Sporadic.J4.j4Facts
  have hXcard : Nat.card X = 86775571046077562880 := by rw [Nat.card_congr eJ.toEquiv, hJcard]
  have : IsSimpleGroup X :=
    @MulEquiv.isSimpleGroup X _ CFSG.Sporadic.J4.J (Subgroup.toGroup _)
      (CFSG.Sporadic.J4.isSimpleGroup_J CFSG.Sporadic.J4.j4Facts) eJ
  have hX168 : Nat.card X ≠ 168 := by rw [hXcard]; norm_num
  obtain ⟨h3, h4⟩ := h X ⟨e⟩
  refine ⟨fun hcfg => ?_, fun hcfg => ?_⟩
  · obtain ⟨Y, W₁, W₂, C₁, C₂, τ, -, -, -, hK, hdual, hτY, hτW, hsyl⟩ := hcfg
    obtain ⟨t, rfl⟩ := j4_all_inner eJ τ
    have htN : t ∈ Subgroup.normalizer (Y : Set X) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hτY
    have h7 : 7 ∣ Nat.card (Subgroup.normalizer (Y : Set X)) :=
      (Nat.dvd_trans (by rw [card_Y C₁]; exact Dvd.dvd.mul_right (by norm_num) _)
        (Subgroup.card_dvd_of_le Subgroup.le_normalizer))
    obtain ⟨y₀, hy₀⟩ := h3 _ Y (hsyl rfl) h7 (normalizer_ne_top hX168 C₁ hK)
      Subgroup.le_normalizer le_rfl C₁.ρ C₁.ρ_surj hK t htN
    exact false_of_innerOn le_rfl C₁ C₂ hdual htN (fun w hw => by simpa using hτW w hw) y₀ hy₀
  · obtain ⟨Y, W₁, W₂, C₁, C₂, τ, hWY, -, hab, hK, hdual, hτY, hτW, -⟩ := hcfg
    obtain ⟨t, rfl⟩ := j4_all_inner eJ τ
    have htN : t ∈ Subgroup.normalizer (Y : Set X) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hτY
    have hO2 : pCoreOf 2 Y ≠ ⊥ := by
      intro hbot
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hsq : ∀ x ∈ W₁, x ^ 2 = 1 := fun x hx => hab.2 x (Subgroup.mem_sup_left hx)
      have hp : IsPGroup 2 W₁ := fun x => ⟨1, Subtype.ext (by
        rw [pow_one, Subgroup.coe_pow]
        exact hsq x x.2)⟩
      have hle : W₁ ≤ pCoreOf 2 Y :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_sup_left.trans hWY) C₁.le hp
      obtain ⟨a, ha, hne⟩ := exists_ne_one_of_natCoord (by norm_num) C₁
      have := hle ha
      rw [hbot, Subgroup.mem_bot] at this
      exact hne this
    obtain ⟨y₀, hy₀⟩ := h4 _ Y hO2 Subgroup.le_normalizer le_rfl C₁.ρ C₁.ρ_surj hK t htN
    exact false_of_innerOn (by norm_num) C₁ C₂ hdual htN (fun w hw => by simpa using hτW w hw) y₀
      hy₀

end CFSG.Quasithin.H13.KGInsp
