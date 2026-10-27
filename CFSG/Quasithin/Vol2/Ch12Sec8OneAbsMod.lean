module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsG
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabMod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}


noncomputable def phiS3 (S : Setting V V₁ L T) : ↥(L ⊔ T) →* Equiv.Perm (Fin 3) :=
  (Classical.choice S.sThree).toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(L ⊔ T)))

omit [Finite G] in
theorem phiS3_eq_one_iff (S : Setting V V₁ L T) (x : ↥(L ⊔ T)) :
    S.phiS3 x = 1 ↔ (x : G) ∈ pCoreOf 2 (L ⊔ T) := by
  have e1 : S.phiS3 x = 1 ↔ (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(L ⊔ T)) x) = 1 := by
    constructor
    · intro h1
      refine (Classical.choice S.sThree).injective ?_
      rw [map_one]
      exact h1
    · intro h1
      show (Classical.choice S.sThree) (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(L ⊔ T)) x) = 1
      rw [h1, map_one]
  rw [e1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (Subgroup.mem_map_iff_mem (L ⊔ T).subtype_injective).symm

omit [Finite G] in
theorem pow_three_mem_pCoreOf_LT (S : Setting V V₁ L T) {x : G} (hx : x ∈ L) :
    x ^ 3 ∈ pCoreOf 2 (L ⊔ T) := by
  let ι : ↥L →* ↥(L ⊔ T) := Subgroup.inclusion le_sup_left
  let N : Subgroup ↥L := MonoidHom.ker (Equiv.Perm.sign.comp (S.phiS3.comp ι))
  have htop : N = ⊤ := by
    refine eq_top_of_oTwoUpper_eq S.base.oTwo_eq N fun y => ⟨1, ?_⟩
    rw [MonoidHom.mem_ker, pow_one]
    simp only [MonoidHom.comp_apply, map_pow]
    exact Int.units_pow_two _
  have hxN : (⟨x, hx⟩ : ↥L) ∈ N := by rw [htop]; exact Subgroup.mem_top _
  have h1 : Equiv.Perm.sign (S.phiS3 (ι ⟨x, hx⟩)) = 1 := hxN
  have h2 : (S.phiS3 (ι ⟨x, hx⟩)) ^ 3 = 1 := perm3_sign_pow _ h1
  rw [← map_pow, ← map_pow] at h2
  exact (S.phiS3_eq_one_iff _).mp h2

omit [Finite G] in
theorem mul_mul_inv_mul_mem_pCoreOf_LT (S : Setting V V₁ L T) {a b : G} (ha : a ∈ L ⊔ T)
    (hb : b ∈ L ⊔ T) (ha2 : a ^ 2 ∈ pCoreOf 2 (L ⊔ T)) (ha1 : a ∉ pCoreOf 2 (L ⊔ T))
    (hb3 : b ^ 3 ∈ pCoreOf 2 (L ⊔ T)) (hb1 : b ∉ pCoreOf 2 (L ⊔ T)) :
    a * b * a⁻¹ * b ∈ pCoreOf 2 (L ⊔ T) := by
  have h2 : S.phiS3 (⟨a, ha⟩ ^ 2) = 1 := (S.phiS3_eq_one_iff _).mpr ha2
  have h3 : S.phiS3 (⟨b, hb⟩ ^ 3) = 1 := (S.phiS3_eq_one_iff _).mpr hb3
  have h1a : S.phiS3 ⟨a, ha⟩ ≠ 1 := fun he => ha1 ((S.phiS3_eq_one_iff _).mp he)
  have h1b : S.phiS3 ⟨b, hb⟩ ≠ 1 := fun he => hb1 ((S.phiS3_eq_one_iff _).mp he)
  rw [map_pow] at h2 h3
  have := perm3_conj_inv _ _ h2 h1a h3 h1b
  have h4 : S.phiS3 (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv]
    exact this
  exact (S.phiS3_eq_one_iff _).mp h4

section Mod

variable (S : Setting V V₁ L T)

include S

omit [Finite G] in
theorem V_le_pCoreOf_LT : V ≤ pCoreOf 2 (L ⊔ T) := by
  rw [← S.centralizer]
  refine le_inf (S.base.V_le_T.trans le_sup_right) fun x hx => ?_
  exact Subgroup.mem_centralizer_iff.mpr fun y hy => S.base.commV hy hx

theorem sq_mem_pCoreOf_LT {u : G} (hu : u ∈ uA V V₁) : u ^ 2 ∈ pCoreOf 2 (L ⊔ T) :=
  S.V_le_pCoreOf_LT (S.V₁_le (S.sq_mem hu))

omit [Finite G] in
theorem pCoreOf_LT_le_centralizer : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) := by
  rw [← S.centralizer]
  exact inf_le_right

omit [Finite G] in
theorem not_mem_pCoreOf_LT_of_not_mem_W {u : G} (hu : u ∈ uA V V₁) (huW : u ∉ wA V V₁) :
    u ∉ pCoreOf 2 (L ⊔ T) := fun hmem => huW ⟨hu, S.pCoreOf_LT_le_centralizer hmem⟩

omit [Finite G] in
theorem not_mem_pCoreOf_LT_of_good {g : G} (hg : Good V₁ L g) :
    g ∉ pCoreOf 2 (L ⊔ T) := by
  intro hmem
  apply hg.not_mem
  have hc : g ∈ Subgroup.centralizer (V : Set G) := S.pCoreOf_LT_le_centralizer hmem
  rw [S.normalizer_eq_centralizer]
  exact Subgroup.centralizer_le (S.V₁_le) hc

variable {g : G} (hg : Good V₁ L g)

include hg

theorem mul_mul_mem_pCoreOf_sup : g * g * g ∈ pCoreOf 2 (L ⊔ uA V V₁) := by
  rw [S.pCoreOf_sup_eq hg]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (hg.mem_sup _) (hg.mem_sup _)) (hg.mem_sup _), ?_⟩
  have := S.pCoreOf_LT_le_centralizer (S.pow_three_mem_pCoreOf_LT hg.mem)
  have e : g ^ 3 = g * g * g := by rw [pow_succ, pow_two]
  rwa [e] at this

theorem mul_mul_inv_mul_mem_pCoreOf_sup {u : G} (hu : u ∈ uA V V₁) (huW : u ∉ wA V V₁) :
    u * g * u⁻¹ * g ∈ pCoreOf 2 (L ⊔ uA V V₁) := by
  have huLT : u ∈ L ⊔ T := Subgroup.mem_sup_right (S.uA_le_T hu)
  have hgLT : g ∈ L ⊔ T := Subgroup.mem_sup_left hg.mem
  have h1 := S.mul_mul_inv_mul_mem_pCoreOf_LT huLT hgLT (S.sq_mem_pCoreOf_LT hu)
    (S.not_mem_pCoreOf_LT_of_not_mem_W hu huW) (S.pow_three_mem_pCoreOf_LT hg.mem)
    (S.not_mem_pCoreOf_LT_of_good hg)
  rw [S.pCoreOf_sup_eq hg]
  refine ⟨?_, S.pCoreOf_LT_le_centralizer h1⟩
  have huI : u ∈ L ⊔ uA V V₁ := Subgroup.mem_sup_right hu
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ huI (hg.mem_sup _))
    (Subgroup.inv_mem _ huI)) (hg.mem_sup _)

theorem module_relations {u : G} (hu : u ∈ uA V V₁) (huW : u ∉ wA V V₁) :
    (∀ w ∈ wA V V₁, w * (g * w * g⁻¹) * (g * g * w * (g * g)⁻¹) ∈
        wA V V₁ ⊓ rconj (wA V V₁) g) ∧
      (∀ w ∈ wA V V₁, (g⁻¹ * w * g) * u * (g⁻¹ * w * g)⁻¹ * u⁻¹ * w⁻¹ ∈
        wA V V₁ ⊓ rconj (wA V V₁) g) ∧
      (∀ x ∈ rconj (wA V V₁) g, ∀ ζ ∈ wA V V₁,
        (u * x * u⁻¹ * x⁻¹)⁻¹ * ζ ∈ wA V V₁ ⊓ rconj (wA V V₁) g →
          x⁻¹ * (g⁻¹ * ζ * g) ∈ wA V V₁ ⊓ rconj (wA V V₁) g) ∧
      (∀ c ∈ pCoreOf 2 (L ⊔ uA V V₁), (g * c * g⁻¹)⁻¹ * c ∈ wA V V₁ ⊓ rconj (wA V V₁) g →
        c ∈ wA V V₁ ⊓ rconj (wA V V₁) g) := by
  set U := uA V V₁ with hUdef
  set W := wA V V₁ with hWdef
  set X := rconj W g with hXdef
  set E := W ⊓ X with hEdef
  set I := L ⊔ U with hIdef
  set Sg := pCoreOf 2 I with hSdef
  have hEU : E = U ⊓ rconj U g := S.wA_inf_rconj_eq hg
  have hEN : I ≤ Subgroup.normalizer (E : Set G) := by
    rw [hEU]
    exact S.sup_le_normalizer_inf_rconj hg
  have hEnorm : (E.subgroupOf I).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hEN
  let π : ↥I →* ↥I ⧸ E.subgroupOf I := QuotientGroup.mk' _
  have hEq : ∀ a b : ↥I, π a = π b ↔ (a : G)⁻¹ * b ∈ E := fun a b => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rfl
  have hπ1 : ∀ a : ↥I, π a = 1 ↔ (a : G) ∈ E := fun a => by
    have := hEq a 1
    rw [map_one] at this
    rw [this]
    simp
  have hKq : ∀ K : Subgroup G, E ≤ K → ∀ a : ↥I, π a ∈ (K.subgroupOf I).map π ↔ (a : G) ∈ K := by
    intro K hEK a
    constructor
    · rintro ⟨k, hk, hka⟩
      have hk' : (k : G) ∈ K := hk
      have h2 : (k : G)⁻¹ * a ∈ E := (hEq k a).mp hka
      have e : (a : G) = k * ((k : G)⁻¹ * a) := by group
      rw [e]
      exact K.mul_mem hk' (hEK h2)
    · intro ha
      exact ⟨a, ha, rfl⟩
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hEW : E ≤ W := inf_le_left
  have hEX : E ≤ X := inf_le_right
  have hES : E ≤ Sg := (inf_le_left.trans (S.wA_le_pCoreOf hg))
  have hWI : W ≤ I := (wA_le_uA V V₁).trans le_sup_right
  have hSI : Sg ≤ I := pCoreOf_le 2 I
  have hSW : W ≤ Sg := S.wA_le_pCoreOf hg
  have hSX : X ≤ Sg := S.rconj_wA_le_pCoreOf hg
  have hXI : X ≤ I := hSX.trans hSI
  have hSset : ((Sg : Subgroup G) : Set G) = (W : Set G) * (X : Set G) :=
    (S.pCoreOf_sup_eq_wA_sup hg).2
  have huI : u ∈ I := Subgroup.mem_sup_right hu
  have hgI : g ∈ I := hg.mem_sup U
  have hmem : ∀ (K : Subgroup G) (a : ↥I ⧸ E.subgroupOf I),
      a ∈ (K.subgroupOf I).map π ↔ ∃ y : ↥I, (y : G) ∈ K ∧ π y = a := fun K a => by
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have hZE : V₁ ≤ E := S.V₁_le_inf_rconj hg
  have hVE : V ≤ E := by
    rw [hEU]
    exact S.le_inf_rconj hg
  have hπcomm : ∀ x y : ↥I, ((x : G) ∈ W ∨ (x : G) ∈ X) → ((y : G) ∈ W ∨ (y : G) ∈ X) →
      π x * π y = π y * π x := by
    intro x y hx hy
    rw [← map_mul, ← map_mul, hEq]
    have e : ((x * y : ↥I) : G)⁻¹ * ((y * x : ↥I) : G) = (y : G)⁻¹ * (x : G)⁻¹ * y * x := by
      simp [mul_assoc]
    rw [e]
    have hWX' : ∀ a ∈ W, ∀ b ∈ X, (b : G)⁻¹ * a⁻¹ * b * a ∈ E := by
      intro a ha b hb
      have h1 : ⁅b⁻¹, a⁻¹⁆ ∈ ⁅X, W⁆ :=
        Subgroup.commutator_mem_commutator (X.inv_mem hb) (W.inv_mem ha)
      rw [Subgroup.commutator_comm] at h1
      have h2 := S.commutator_wA_rconj_le hg h1
      have e2 : ⁅b⁻¹, a⁻¹⁆ = b⁻¹ * a⁻¹ * b * a := by simp [commutatorElement_def]
      rw [e2] at h2
      exact h2
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · have := S.commutator_mem (x := (y : G)⁻¹) (y := (x : G)⁻¹)
        (U.inv_mem (wA_le_uA V V₁ hy)) (U.inv_mem (wA_le_uA V V₁ hx))
      simp only [inv_inv] at this
      exact hZE this
    · exact hWX' _ hx _ hy
    · have := hWX' _ hy _ hx
      have e3 : ∀ a b : G, b⁻¹ * a⁻¹ * b * a = (a⁻¹ * b⁻¹ * a * b)⁻¹ := fun a b => by group
      rw [e3]
      exact E.inv_mem this
    · have := S.commutator_rconj_uA_mem hg (a := (y : G)⁻¹) (b := (x : G)⁻¹)
        (by
          have : (y : G) ∈ rconj U g := by
            rw [mem_rconj] at hy ⊢
            exact wA_le_uA V V₁ hy
          exact (rconj U g).inv_mem this)
        (by
          have : (x : G) ∈ rconj U g := by
            rw [mem_rconj] at hx ⊢
            exact wA_le_uA V V₁ hx
          exact (rconj U g).inv_mem this)
      simp only [inv_inv] at this
      exact hVE this
  have hXUg : X ≤ rconj U g := by
    intro y hy
    have hy' : y ∈ rconj W g := hy
    rw [mem_rconj] at hy'
    rw [mem_rconj]
    exact wA_le_uA V V₁ hy'
  have hSdec : ∀ a : ↥I, (a : G) ∈ Sg → ∃ w ∈ W, ∃ x ∈ X, (a : G) = w * x := by
    intro a ha
    have : (a : G) ∈ (W : Set G) * (X : Set G) := by rw [← hSset]; exact ha
    obtain ⟨w, hw, x, hx, hwx⟩ := this
    exact ⟨w, hw, x, hx, hwx.symm⟩
  have hSq : ∀ s' ∈ (Sg.subgroupOf I).map π, ∃ w x : ↥I, (w : G) ∈ W ∧ (x : G) ∈ X ∧
      s' = π w * π x := by
    intro s' hs'
    obtain ⟨a, ha, rfl⟩ := (hmem Sg s').mp hs'
    obtain ⟨w, hw, x, hx, hax⟩ := hSdec a ha
    refine ⟨⟨w, hWI hw⟩, ⟨x, hXI hx⟩, hw, hx, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hax
  have hcomm : ∀ a ∈ (Sg.subgroupOf I).map π, ∀ b ∈ (Sg.subgroupOf I).map π, a * b = b * a := by
    intro a ha b hb
    obtain ⟨w₁, x₁, hw₁, hx₁, rfl⟩ := hSq a ha
    obtain ⟨w₂, x₂, hw₂, hx₂, rfl⟩ := hSq b hb
    have c11 : Commute (π w₁) (π w₂) := hπcomm w₁ w₂ (Or.inl hw₁) (Or.inl hw₂)
    have c12 : Commute (π w₁) (π x₂) := hπcomm w₁ x₂ (Or.inl hw₁) (Or.inr hx₂)
    have c21 : Commute (π x₁) (π w₂) := hπcomm x₁ w₂ (Or.inr hx₁) (Or.inl hw₂)
    have c22 : Commute (π x₁) (π x₂) := hπcomm x₁ x₂ (Or.inr hx₁) (Or.inr hx₂)
    exact (Commute.mul_left (Commute.mul_right c11 c12) (Commute.mul_right c21 c22))
  have hsq : ∀ a ∈ (Sg.subgroupOf I).map π, a * a = 1 := by
    intro a ha
    obtain ⟨w, x, hw, hx, rfl⟩ := hSq a ha
    have c : π w * π x = π x * π w := hπcomm w x (Or.inl hw) (Or.inr hx)
    have hw2 : π w * π w = 1 := by
      rw [← map_mul, hπ1]
      have := S.sq_mem (wA_le_uA V V₁ hw)
      rw [pow_two] at this
      exact hZE this
    have hx2 : π x * π x = 1 := by
      rw [← map_mul, hπ1]
      have h1 := (S.l2Setting).rconj_sq_mem (hXUg hx)
      have h2 := (S.l2Setting).V₁_le_rconj_V hg.mem h1
      rw [pow_two] at h2
      exact hVE h2
    calc π w * π x * (π w * π x) = π w * (π x * π w) * π x := by group
      _ = π w * (π w * π x) * π x := by rw [← c]
      _ = (π w * π w) * (π x * π x) := by group
      _ = 1 := by rw [hw2, hx2, one_mul]
  have hWS' : (W.subgroupOf I).map π ≤ (Sg.subgroupOf I).map π := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := (hmem W a).mp ha
    exact (hmem Sg _).mpr ⟨y, hSW hy, rfl⟩
  have hXS' : (X.subgroupOf I).map π ≤ (Sg.subgroupOf I).map π := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := (hmem X a).mp ha
    exact (hmem Sg _).mpr ⟨y, hSX hy, rfl⟩
  have hSWX : ∀ s ∈ (Sg.subgroupOf I).map π, ∃ w ∈ (W.subgroupOf I).map π,
      ∃ x ∈ (X.subgroupOf I).map π, s = w * x := by
    intro s hs
    obtain ⟨w, x, hw, hx, rfl⟩ := hSq s hs
    exact ⟨π w, (hmem W _).mpr ⟨w, hw, rfl⟩, π x, (hmem X _).mpr ⟨x, hx, rfl⟩, rfl⟩
  have hXg : ∀ x : ↥I ⧸ E.subgroupOf I, x ∈ (X.subgroupOf I).map π ↔
      π ⟨g, hgI⟩ * x * (π ⟨g, hgI⟩)⁻¹ ∈ (W.subgroupOf I).map π := by
    intro x
    obtain ⟨y, rfl⟩ := hπsurj x
    have e : π ⟨g, hgI⟩ * π y * (π ⟨g, hgI⟩)⁻¹ = π (⟨g, hgI⟩ * y * ⟨g, hgI⟩⁻¹) := by
      simp [map_mul, map_inv]
    rw [e, hKq X hEX, hKq W hEW]
    exact mem_rconj
  have hWX : ∀ a ∈ (W.subgroupOf I).map π, a ∈ (X.subgroupOf I).map π → a = 1 := by
    intro a haW haX
    obtain ⟨y, hyW, rfl⟩ := (hmem W a).mp haW
    have hyX := (hKq X hEX y).mp haX
    exact (hπ1 y).mpr ⟨hyW, hyX⟩
  have hgS : ∀ s ∈ (Sg.subgroupOf I).map π,
      π ⟨g, hgI⟩ * s * (π ⟨g, hgI⟩)⁻¹ ∈ (Sg.subgroupOf I).map π := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := (hmem Sg s).mp hs
    have e : π ⟨g, hgI⟩ * π a * (π ⟨g, hgI⟩)⁻¹ = π (⟨g, hgI⟩ * a * ⟨g, hgI⟩⁻¹) := by
      simp [map_mul, map_inv]
    rw [e]
    exact (hmem Sg _).mpr ⟨_, (Subgroup.mem_normalizer_iff.mp (hg.mem_normalizer_pCoreOf U)
      a).mp ha, rfl⟩
  have hg3 : π ⟨g, hgI⟩ * π ⟨g, hgI⟩ * π ⟨g, hgI⟩ ∈ (Sg.subgroupOf I).map π := by
    rw [← map_mul, ← map_mul]
    exact (hmem Sg _).mpr ⟨_, S.mul_mul_mem_pCoreOf_sup hg, rfl⟩
  have hu2 : π ⟨u, huI⟩ * π ⟨u, huI⟩ = 1 := by
    rw [← map_mul, hπ1]
    have := S.sq_mem hu
    rw [pow_two] at this
    exact hZE this
  have huW' : ∀ w' ∈ (W.subgroupOf I).map π, π ⟨u, huI⟩ * w' * (π ⟨u, huI⟩)⁻¹ = w' := by
    intro w' hw'
    obtain ⟨y, hy, rfl⟩ := (hmem W w').mp hw'
    have e : π ⟨u, huI⟩ * π y * (π ⟨u, huI⟩)⁻¹ = π (⟨u, huI⟩ * y * ⟨u, huI⟩⁻¹) := by
      simp [map_mul, map_inv]
    rw [e, hEq]
    have := S.commutator_mem (x := u) (y := (y : G)⁻¹) hu
      (U.inv_mem (wA_le_uA V V₁ hy))
    have e2 : ((⟨u, huI⟩ * y * ⟨u, huI⟩⁻¹ : ↥I) : G)⁻¹ * (y : G) =
        u * (y : G)⁻¹ * u⁻¹ * (y : G) := by
      simp [mul_assoc]
    rw [e2]
    simpa using hZE this
  have huSW : ∀ s' ∈ (Sg.subgroupOf I).map π,
      π ⟨u, huI⟩ * s' * (π ⟨u, huI⟩)⁻¹ * s'⁻¹ ∈ (W.subgroupOf I).map π := by
    intro s' hs'
    obtain ⟨a, ha, rfl⟩ := (hmem Sg s').mp hs'
    have e : π ⟨u, huI⟩ * π a * (π ⟨u, huI⟩)⁻¹ * (π a)⁻¹ =
        π (⟨u, huI⟩ * a * ⟨u, huI⟩⁻¹ * a⁻¹) := by
      simp [map_mul, map_inv]
    rw [e, hKq W hEW]
    show u * (a : G) * u⁻¹ * (a : G)⁻¹ ∈ W
    rw [hWdef, S.wA_eq_inf_pCoreOf hg]
    refine ⟨?_, ?_⟩
    · have hau : (a : G) * u⁻¹ * (a : G)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp
          (S.pCoreOf_sup_le_normalizer_uA hg ha) _).mp (U.inv_mem hu)
      have e3 : u * (a : G) * u⁻¹ * (a : G)⁻¹ = u * ((a : G) * u⁻¹ * (a : G)⁻¹) := by group
      rw [e3]
      exact U.mul_mem hu hau
    · have hua : u * (a : G) * u⁻¹ ∈ Sg :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 I huI) _).mp ha
      exact Sg.mul_mem hua (Sg.inv_mem ha)
  have hker : ∀ y' ∈ (X.subgroupOf I).map π,
      π ⟨u, huI⟩ * y' * (π ⟨u, huI⟩)⁻¹ * y'⁻¹ = 1 → y' = 1 := by
    intro y' hy' h1
    obtain ⟨y, hyX, rfl⟩ := (hmem X y').mp hy'
    have e : π ⟨u, huI⟩ * π y * (π ⟨u, huI⟩)⁻¹ * (π y)⁻¹ =
        π (⟨u, huI⟩ * y * ⟨u, huI⟩⁻¹ * y⁻¹) := by
      simp [map_mul, map_inv]
    rw [e, hπ1] at h1
    have h2 : (y : G) * u * (y : G)⁻¹ * u⁻¹ ∈ E := by
      have e2 : (y : G) * u * (y : G)⁻¹ * u⁻¹ = (u * (y : G) * u⁻¹ * (y : G)⁻¹)⁻¹ := by group
      rw [e2]
      exact E.inv_mem h1
    exact (hπ1 y).mpr (S.mem_inf_of_commutator_mem hg hu huW hyX h2)
  have hK2 : π ⟨u, huI⟩ * π ⟨g, hgI⟩ * (π ⟨u, huI⟩)⁻¹ * π ⟨g, hgI⟩ ∈
      (Sg.subgroupOf I).map π := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact (hmem Sg _).mpr ⟨_, S.mul_mul_inv_mul_mem_pCoreOf_sup hg hu huW, rfl⟩
  obtain ⟨hN, hKI, huniq, hfix⟩ := s3_module_core ((Sg.subgroupOf I).map π) ((W.subgroupOf I).map π)
    ((X.subgroupOf I).map π) (π ⟨g, hgI⟩) (π ⟨u, huI⟩) hcomm hsq hWS' hXS' hSWX hXg hWX hgS hg3 hu2
    huW' huSW hker hK2
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun x hx ζ hζ hxζ => ?_, fun c hc hcE => ?_⟩
  · have hn := hN (π ⟨w, hWI hw⟩) ((hmem W _).mpr ⟨_, hw, rfl⟩)
    have : π (⟨w, hWI hw⟩ * (⟨g, hgI⟩ * ⟨w, hWI hw⟩ * ⟨g, hgI⟩⁻¹) *
        (⟨g, hgI⟩ * ⟨g, hgI⟩ * ⟨w, hWI hw⟩ * (⟨g, hgI⟩ * ⟨g, hgI⟩)⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      exact hn
    exact (hπ1 _).mp this
  · have hn := hKI (π ⟨w, hWI hw⟩) ((hmem W _).mpr ⟨_, hw, rfl⟩)
    have h1 : π (⟨g, hgI⟩⁻¹ * ⟨w, hWI hw⟩ * ⟨g, hgI⟩ * ⟨u, huI⟩ *
        (⟨g, hgI⟩⁻¹ * ⟨w, hWI hw⟩ * ⟨g, hgI⟩)⁻¹ * ⟨u, huI⟩⁻¹ * ⟨w, hWI hw⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv] at hn ⊢
      rw [hn]
      group
    exact (hπ1 _).mp h1
  · have hxI : x ∈ I := hXI hx
    have hζI : ζ ∈ I := hWI hζ
    have h1 : π (⟨u, huI⟩ * ⟨x, hxI⟩ * ⟨u, huI⟩⁻¹ * ⟨x, hxI⟩⁻¹) = π ⟨ζ, hζI⟩ := by
      rw [hEq]
      exact hxζ
    have h2 := huniq (π ⟨x, hxI⟩) ((hmem X _).mpr ⟨_, hx, rfl⟩) (π ⟨ζ, hζI⟩)
      ((hmem W _).mpr ⟨_, hζ, rfl⟩) (by simpa only [map_mul, map_inv] using h1)
    have h3 : π ⟨x, hxI⟩ = π (⟨g, hgI⟩⁻¹ * ⟨ζ, hζI⟩ * ⟨g, hgI⟩) := by
      simpa only [map_mul, map_inv] using h2
    rw [hEq] at h3
    exact h3
  · have hcI : c ∈ I := hSI hc
    have h1 : π ⟨g, hgI⟩ * π ⟨c, hcI⟩ * (π ⟨g, hgI⟩)⁻¹ = π ⟨c, hcI⟩ := by
      have e : π ⟨g, hgI⟩ * π ⟨c, hcI⟩ * (π ⟨g, hgI⟩)⁻¹ =
          π (⟨g, hgI⟩ * ⟨c, hcI⟩ * ⟨g, hgI⟩⁻¹) := by
        simp only [map_mul, map_inv]
      rw [e, hEq]
      exact hcE
    exact (hπ1 _).mp (hfix _ ((hmem Sg _).mpr ⟨_, hc, rfl⟩) h1)

end Mod

end Setting

end L128A

end CFSG.Quasithin.H13
