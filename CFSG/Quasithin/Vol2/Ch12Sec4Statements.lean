module

public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Stmt12_3_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
    ¬ Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7))

@[expose] def Cor12_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Hyp1223 G T L V →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Subgroup.normalizer (L : Set G) →
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
      Group.IsSolvable ↥H ∨
        (LieModel (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) .PSL 2 2 2 ∧
          quasithinIsMaximalLocal T (oTwoUpper H) ∧ quasithinIsFaithfulLocal T (oTwoUpper H) ∧
          IsA5ModuleSum (oTwoUpper H) ⁅VZ T (oTwoUpper H), oTwoUpper H⁆)

variable {G : Type} [Group G]

theorem VZ_eq_VZ_oTwoUpper [Finite G] {T H : Subgroup G}
    (hT : QuasithinUnique.IsSylowTwoOf T H) : VZ T H = VZ T (oTwoUpper H) := by
  have hTH : T ≤ H := hT.1
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  refine le_antisymm ?_ (conjClosure_mono le_rfl hKH)
  have hZT : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun _ hz => hz.1
  have hTZ : T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (Subgroup.le_centralizer_iff.mp (hZT.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hres : twoResidual H ≤ oTwoUpper H :=
    twoResidual_le_of_isTwoQuotient (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
      fun y hy => exists_pow_mem_oTwoUpper H hy
  have hHeq : T ⊔ oTwoUpper H = H :=
    le_antisymm (sup_le hTH hKH) ((sup_twoResidual_eq hT).symm.le.trans (sup_le_sup_left hres T))
  have key : ∀ s ∈ T, ∀ x ∈ VZ T (oTwoUpper H), s * x * s⁻¹ ∈ VZ T (oTwoUpper H) := by
    intro s hs x hx
    have hle : VZ T (oTwoUpper H) ≤
        (VZ T (oTwoUpper H)).comap (MulAut.conj s).toMonoidHom := by
      refine conjClosure_le fun k hk z hz => ?_
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hk' : s * k * s⁻¹ ∈ oTwoUpper H :=
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_oTwoUpper H (hTH hs)) k).1 hk
      have hz' : s * z * s⁻¹ ∈ quasithinOmegaOneCenter T :=
        (Subgroup.mem_normalizer_iff.1 (hTZ hs) z).1 hz
      have := mem_conjClosure hk' hz'
      rwa [show s * k * s⁻¹ * (s * z * s⁻¹) * (s * k * s⁻¹)⁻¹ = s * (k * z * k⁻¹) * s⁻¹ by
        group] at this
    have h1 := hle hx
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  have hTN : T ≤ Subgroup.normalizer (VZ T (oTwoUpper H) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key t ht x, fun hx => ?_⟩
    have h1 := key t⁻¹ (T.inv_mem ht) _ hx
    rwa [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at h1
  have hHN : H ≤ Subgroup.normalizer (VZ T (oTwoUpper H) : Set G) := by
    have h := sup_le hTN (le_normalizer_conjClosure (quasithinOmegaOneCenter T) (oTwoUpper H))
    rwa [hHeq] at h
  intro x hx
  refine (conjClosure_le fun h hh z hz => ?_) hx
  have hz' : z ∈ VZ T (oTwoUpper H) := le_conjClosure _ _ hz
  exact (Subgroup.mem_normalizer_iff.1 (hHN hh) z).1 hz'

theorem cor12_3_2_of_stmt12_3_1 (h1231 : Stmt12_3_1) (h1227 : Stmt12_2_7) (h1222 : Stmt12_2_2) :
    Cor12_3_2 := by
  intro G _ _ T L V H hyp hCZ hH
  by_cases hsol : Group.IsSolvable ↥H
  · exact Or.inl hsol
  right
  obtain ⟨h2, Y, hKY, hYmax, hYf, hcase⟩ := (h1227 G T L V H hyp hCZ hH).2 hsol
  have hTH : T ≤ H := hH.1.1
  have hsyl : QuasithinUnique.IsSylowTwoOf T H :=
    ⟨hTH, hyp.sylow.1, fun h => hyp.sylow.2 (h.trans (by
      simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTH))⟩
  rcases hcase with ⟨hYK, hA5⟩ | ⟨hA7, hYq, hTY, -⟩
  · subst hYK
    refine ⟨h2, hYmax, hYf, ?_⟩
    rwa [VZ_eq_VZ_oTwoUpper hsyl] at hA5
  · exfalso
    rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
    · exact hyp.notAlt hAlt
    obtain ⟨-, ⟨VY, hVY⟩, -⟩ := h3 Y hYmax hYf hYq
    exact h1231 G T Y VY ⟨hyp.simple, hyp.nonabelian, hyp.qtke, hyp.sylow, hyp.notAlt, hYmax,
      hYf, hYq, hTY, hVY⟩ hA7

@[expose] def Lemma12_4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Subgroup.normalizer (L : Set G) →
    ∀ hV : IsElemAbelian 2 V, 1 < E3.sParam hV →
      ∃ g : G, ⁅V, CFSG.conjugate V g⁆ ≠ ⊥ ∧
        ⁅V, CFSG.conjugate V g⁆ ≤ V ⊓ CFSG.conjugate V g

structure Cx1242 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) : Prop where
  hyp : Hyp1223 G T L V
  cx : ((Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) ∧
      V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) ∨
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
      Nat.card V = 2 ^ 10 ∧
      Subgroup.centralizer ((V ⊓ quasithinOmegaOneCenter T : Subgroup G) : Set G) ≤
        Subgroup.normalizer (L : Set G))

theorem stmt12_4_2_iff_forall_not_cx :
    Stmt12_4_2 ↔ ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), ¬ Cx1242 G T L V := by
  rw [stmt12_4_2_iff]
  constructor
  · intro h G _ _ T L V hcx
    obtain ⟨h1, h2⟩ := h G T L V hcx.hyp
    rcases hcx.cx with ⟨hq, hne⟩ | ⟨hq, hcard, hle⟩
    · exact hne (h1 hq)
    · exact h2 hq hcard hle
  · intro h G _ _ T L V hyp
    refine ⟨fun hq => ?_, fun hq hcard hle => h G T L V ⟨hyp, Or.inr ⟨hq, hcard, hle⟩⟩⟩
    by_contra hne
    exact h G T L V ⟨hyp, Or.inl ⟨hq, hne⟩⟩

@[expose] def Pre1242 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    ∃ z : G, z ∈ V ⊓ quasithinOmegaOneCenter T ∧ orderOf z = 2 ∧
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
      ((Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
          LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
        V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers z) ∧
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
        V ⊓ quasithinOmegaOneCenter T = Subgroup.zpowers z)

@[expose] def Lemma12_4_3_one : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma12_4_3_two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    L = ⁅L, thompsonJ T⁆

theorem lemma12_4_3_one_of_pre (hpre : Pre1242) : Lemma12_4_3_one := by
  intro G _ _ T L V hcx
  obtain ⟨z, hz, -, hGz, -⟩ := hpre G T L V hcx
  refine le_trans (Subgroup.centralizer_le ?_) hGz
  rintro _ rfl
  exact hz.2

@[expose] def Lemma12_4_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    ¬ Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))

@[expose] def Post1244 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      ∃ z : G, orderOf z = 2 ∧ V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers z ∧
        Subgroup.normalizer (L : Set G) = Subgroup.centralizer ({z} : Set G) ∧
        Subgroup.normalizer (L : Set G) = Subgroup.normalizer (V : Set G) ∧
        ∃ hV : IsElemAbelian 2 V, E3.mParam (autI hV ⊤) = 2

@[expose] def Lemma12_4_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ E : Subgroup G, E ≤ V → Nat.card E = 4 → T ≤ Subgroup.normalizer (E : Set G) →
      ∀ v ∈ E, v ∉ Subgroup.centralizer (L : Set G) →
        QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer (E : Set G))
          (Subgroup.centralizer ({v} : Set G)) ∧
        (T ⊓ Subgroup.centralizer (E : Set G)).relIndex T = 2

@[expose] def Lemma12_4_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      ∀ v ∈ V, ∀ g : G, g⁻¹ * v * g ∈ V → ∃ l ∈ L, l⁻¹ * v * l = g⁻¹ * v * g

@[expose] def Lemma12_4_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      1 < E3.rParam V

@[expose] def Lemma12_4_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      ∀ g : G, CFSG.conjugate V g ≤ Subgroup.normalizer (V : Set G) →
        ⁅CFSG.conjugate V g, V⁆ ≠ ⊥ →
          ¬ V ≤ Subgroup.normalizer (CFSG.conjugate V g : Set G)

theorem le_normalizer_of_commutator_le {V A : Subgroup G} (h : ⁅V, A⁆ ≤ V ⊓ A) :
    A ≤ Subgroup.normalizer (V : Set G) ∧ V ≤ Subgroup.normalizer (A : Set G) := by
  have key : ∀ {X Y : Subgroup G}, ⁅X, Y⁆ ≤ X → Y ≤ Subgroup.normalizer (X : Set G) := by
    intro X Y hXY
    have hc : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X := fun y hy x hx => by
      have h1 : x * y * x⁻¹ * y⁻¹ ∈ X := hXY (Subgroup.commutator_mem_commutator hx hy)
      have h2 : y * x * y⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ * x := by group
      rw [h2]
      exact X.mul_mem (X.inv_mem h1) hx
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hc y hy x, fun hx => ?_⟩
    have h1 := hc y⁻¹ (Y.inv_mem hy) _ hx
    rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at h1
  exact ⟨key (h.trans inf_le_left),
    key ((Subgroup.commutator_comm A V).le.trans (h.trans inf_le_right))⟩

theorem stmt12_4_2_of_lemmas (h1241 : Lemma12_4_1) (h1243 : Lemma12_4_3_one)
    (h1244 : Lemma12_4_4) (hpost : Post1244) (h1248 : Lemma12_4_8) (h1249 : Lemma12_4_9) :
    Stmt12_4_2 := by
  rw [stmt12_4_2_iff_forall_not_cx]
  intro G _ _ T L V hcx
  have hq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 := by
    rcases hcx.cx with ⟨hq, -⟩ | ⟨hq, -⟩
    · exact hq
    · exact absurd hq (h1244 G T L V hcx)
  obtain ⟨-, -, -, -, -, hV, hm⟩ := hpost G T L V hcx hq
  have hr := h1248 G T L V hcx hq
  have hs : 1 < E3.sParam hV := by
    unfold E3.sParam
    rw [hm]
    have h2 : (2 : ℕ∞) ≤ E3.rParam V := by
      have := Order.add_one_le_of_lt hr
      rwa [one_add_one_eq_two] at this
    rw [min_eq_right (by exact_mod_cast h2)]
    simp
  obtain ⟨g, hne, hle⟩ := h1241 G T L V hcx.hyp (h1243 G T L V hcx) hV hs
  obtain ⟨hAV, hVA⟩ := le_normalizer_of_commutator_le hle
  have hne' : ⁅CFSG.conjugate V g, V⁆ ≠ ⊥ := by
    rwa [Subgroup.commutator_comm]
  exact h1249 G T L V hcx hq g hAV hne' hVA

end CFSG.Quasithin.H13
