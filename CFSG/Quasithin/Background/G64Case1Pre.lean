module

public import CFSG.Quasithin.Background.G64ProofGroup
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.Background.G64ProofBasic
public import CFSG.Quasithin.Background.G64RankOne

public section

namespace CFSG.Quasithin.G64

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank
open scoped Matrix

@[expose] def G2NoTransvection : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 →
    ∀ γ : ↥(quasithinG2 F), ¬ ModelTransvec (FFModel.zornQ (quasithinG2 F)) γ

section Zorn

variable {F : Type} [Field F]

theorem mem_zornO0 {x : Multiplicative (quasithinZorn F)} :
    x ∈ zornO0 F ↔ (Multiplicative.toAdd x).1 + (Multiplicative.toAdd x).2.2.2 = 0 :=
  Iff.rfl

theorem mem_zornR {x : Multiplicative (quasithinZorn F)} :
    x ∈ zornR F ↔ ∃ c : F, Multiplicative.toAdd x = (c, 0, 0, c) :=
  Iff.rfl

theorem card_le_two_of_zornQ {Γ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F)} {γ : ↥Γ}
    (h : ModelTransvec (FFModel.zornQ Γ) γ) : Nat.card F ≤ 2 := by
  classical
  obtain ⟨m', hm', hmv, hall⟩ := h
  set g : quasithinZorn F ≃ₗ[F] quasithinZorn F := (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F)
    with hg
  set x₁ : quasithinZorn F := Multiplicative.toAdd (m' : Multiplicative (quasithinZorn F))
    with hx₁
  have hm'eq : (m' : Multiplicative (quasithinZorn F)) = Multiplicative.ofAdd x₁ := rfl
  have hm₁ : Multiplicative.ofAdd x₁ ∈ zornO0 F := hm'
  have hact : ∀ x : quasithinZorn F, zornAct Γ γ (Multiplicative.ofAdd x) *
      (Multiplicative.ofAdd x)⁻¹ = Multiplicative.ofAdd (g x - x) := by
    intro x
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, sub_eq_add_neg]
    rfl
  have hy₁R : Multiplicative.ofAdd (g x₁ - x₁) ∉ zornR F := by
    rw [← hact]
    exact hmv
  have hall' : ∀ x : quasithinZorn F, Multiplicative.ofAdd x ∈ zornO0 F →
      Multiplicative.ofAdd (g x - x) ∈ zornR F ∨
        Multiplicative.ofAdd ((g x - x) - (g x₁ - x₁)) ∈ zornR F := by
    intro x hx
    rcases hall (Multiplicative.ofAdd x) hx with h0 | h0
    · left
      rw [← hact]
      exact h0
    · right
      have e : Multiplicative.ofAdd ((g x - x) - (g x₁ - x₁)) =
          zornAct Γ γ (Multiplicative.ofAdd x) * (Multiplicative.ofAdd x)⁻¹ *
            (zornAct Γ γ (Multiplicative.ofAdd x₁) * (Multiplicative.ofAdd x₁)⁻¹)⁻¹ := by
        rw [hact, hact]
        apply Multiplicative.toAdd.injective
        rw [toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, sub_eq_add_neg]
      rw [e]
      exact h0
  have hO0 : ∀ (c : F) (x : quasithinZorn F), Multiplicative.ofAdd x ∈ zornO0 F →
      Multiplicative.ofAdd (c • x) ∈ zornO0 F := by
    intro c x hx
    rw [mem_zornO0] at hx ⊢
    simp only [toAdd_ofAdd, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx ⊢
    rw [← mul_add, hx, mul_zero]
  have hR : ∀ (c : F) (x : quasithinZorn F), Multiplicative.ofAdd x ∈ zornR F →
      Multiplicative.ofAdd (c • x) ∈ zornR F := by
    intro c x hx
    obtain ⟨d, hd⟩ := mem_zornR.1 hx
    refine mem_zornR.2 ⟨c * d, ?_⟩
    simp only [toAdd_ofAdd] at hd ⊢
    rw [hd]
    ext <;> simp
  have hF : ∀ c : F, c = 0 ∨ c = 1 := by
    intro c
    have hgc : g (c • x₁) - c • x₁ = c • (g x₁ - x₁) := by rw [map_smul, smul_sub]
    rcases hall' _ (hO0 c x₁ hm₁) with h0 | h0
    · left
      by_contra hc
      apply hy₁R
      rw [hgc] at h0
      have := hR c⁻¹ _ h0
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    · right
      by_contra hc
      apply hy₁R
      have h2 : Multiplicative.ofAdd ((c - 1) • (g x₁ - x₁)) ∈ zornR F := by
        rw [sub_smul, one_smul, ← hgc]
        exact h0
      have := hR (c - 1)⁻¹ _ h2
      rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hc), one_smul] at this
  calc Nat.card F ≤ Nat.card Bool :=
        Nat.card_le_card_of_surjective (fun b : Bool => if b then (1 : F) else 0) (by
          intro c
          rcases hF c with rfl | rfl
          · exact ⟨false, by simp⟩
          · exact ⟨true, by simp⟩)
    _ = 2 := by simp

theorem modelTransvec_zornQ_of_derived {γ : ↥⁅quasithinG2 F, quasithinG2 F⁆}
    (h : ModelTransvec (FFModel.zornQ ⁅quasithinG2 F, quasithinG2 F⁆) γ) :
    ModelTransvec (FFModel.zornQ (quasithinG2 F))
      ⟨(γ : quasithinZorn F ≃ₗ[F] quasithinZorn F),
        (Subgroup.commutator_le.2 fun x hx y hy => by
          rw [commutatorElement_def]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
            (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)) γ.2⟩ :=
  h

end Zorn

theorem dualNat_faithful {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) : (FFModel.dualNat Γ).Faithful := by
  intro (γ : ↥Γ) hγ
  have h1 : ∀ v : ι → K, (((γ⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι K) :
      Matrix ι ι K)ᵀ *ᵥ v = v := by
    intro v
    have := Subgroup.mem_bot.1 (hγ (Multiplicative.ofAdd v) trivial)
    exact congrArg Multiplicative.toAdd (mul_inv_eq_one.1 this)
  have h2 : (((γ⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)ᵀ = 1 := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [Matrix.one_mulVec]
    exact h1 _
  have h3 : (((γ⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) = 1 := by
    rw [← Matrix.transpose_transpose (((γ⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι K) :
      Matrix ι ι K), h2, Matrix.transpose_one]
  have h4 : γ⁻¹ = 1 := Subtype.ext (Units.ext h3)
  exact inv_eq_one.1 h4

theorem IsQuasisimple.exists_ne {X : Type*} [Group X] (h : CFSG.IsQuasisimple X) :
    ∃ x y : X, x * y ≠ y * x := by
  obtain ⟨-, -, a, b, hab⟩ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨x, y, fun hxy => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]

theorem commutator_le_of_index_two {X : Type*} [Group X] {N : Subgroup X} (hN : N.index = 2) :
    commutator X ≤ N := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [commutatorElement_def]
  have h1 : x * y ∈ N ↔ x⁻¹ * y⁻¹ ∈ N := by
    rw [Subgroup.mul_mem_iff_of_index_two hN, Subgroup.mul_mem_iff_of_index_two hN,
      N.inv_mem_iff, N.inv_mem_iff]
  have h2 : x * y * x⁻¹ * y⁻¹ = (x * y) * (x⁻¹ * y⁻¹) := by group
  rw [h2, Subgroup.mul_mem_iff_of_index_two hN]
  exact h1

theorem not_isQuasisimple_of_index_two {X : Type*} [Group X] {N : Subgroup X}
    (hN : N.index = 2) : ¬ CFSG.IsQuasisimple X := by
  intro h
  have hle := commutator_le_of_index_two hN
  rw [h.1.commutator_eq_top, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hN
  omega

theorem not_isQuasisimple_of_perm {X : Type*} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (e : X ≃* Equiv.Perm (Fin n)) : ¬ CFSG.IsQuasisimple X := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  refine not_isQuasisimple_of_index_two (N := (alternatingGroup (Fin n)).comap e.toMonoidHom) ?_
  rw [Subgroup.index_comap_of_surjective _ e.surjective]
  exact alternatingGroup.index_eq_two

theorem not_isQuasisimple_of_card_six {X : Type*} [Group X] [Finite X] (h6 : Nat.card X = 6) :
    ¬ CFSG.IsQuasisimple X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [h6]; norm_num)
  refine not_isQuasisimple_of_index_two (N := Subgroup.zpowers g) ?_
  have hmul := Subgroup.card_mul_index (Subgroup.zpowers g)
  rw [Nat.card_zpowers, hg, h6] at hmul
  omega

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {a : MulAut V}

theorem comm_of_fix_commV {X : Subgroup (MulAut V)}
    (h : ∀ x ∈ X, ∀ v ∈ commV X, x v = v) : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
  intro x hx y hy
  ext v
  rw [MulAut.mul_apply, MulAut.mul_apply]
  have e1 : x (y v) = (y v * v⁻¹) * (x v * v⁻¹) * v := by
    calc x (y v) = x ((y v * v⁻¹) * v) := by congr 1; group
      _ = x (y v * v⁻¹) * x v := map_mul _ _ _
      _ = (y v * v⁻¹) * x v := by rw [h x hx _ (G6.mem_commV_of_mem hy v)]
      _ = (y v * v⁻¹) * (x v * v⁻¹) * v := by group
  have e2 : y (x v) = (x v * v⁻¹) * (y v * v⁻¹) * v := by
    calc y (x v) = y ((x v * v⁻¹) * v) := by congr 1; group
      _ = y (x v * v⁻¹) * y v := map_mul _ _ _
      _ = (x v * v⁻¹) * y v := by rw [h y hy _ (G6.mem_commV_of_mem hx v)]
      _ = (x v * v⁻¹) * (y v * v⁻¹) * v := by group
  rw [e1, e2, mul_comm (y v * v⁻¹)]

theorem le_normalizer_fstar :
    G ≤ Subgroup.normalizer
      (quasithinGenFitting (conjClosure (Subgroup.zpowers a) G) : Set (MulAut V)) :=
  (le_normalizer_conjClosure _ G).trans (normalizer_le_normalizer_quasithinGenFitting _)

theorem commV_eq_top_of_fstar [Finite V] (h : Hyp61 G a)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2)
    (hq : CFSG.IsQuasisimple ↥(quasithinGenFitting (conjClosure (Subgroup.zpowers a) G))) :
    commV (quasithinGenFitting (conjClosure (Subgroup.zpowers a) G)) = ⊤ := by
  set K := conjClosure (Subgroup.zpowers a) G with hK
  set L := quasithinGenFitting K with hL
  set U := commV L with hU
  have hLK : L ≤ K := quasithinGenFitting_le K
  have hGL : G ≤ Subgroup.normalizer
      (quasithinGenFitting (conjClosure (Subgroup.zpowers a) G) : Set (MulAut V)) :=
    le_normalizer_fstar
  have hUG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U := fun g hg u hu => G6.apply_mem_commV
    (fun x hx => (Subgroup.mem_normalizer_iff.1 (hGL hg) x).1 hx) hu
  by_cases haU : commV (Subgroup.zpowers a) ≤ U
  ·
    rw [eq_top_iff, ← h.span]
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨v, hv, rfl⟩
    exact hUG g hg v (haU hv)
  · exfalso
    obtain ⟨w, hw, hwU⟩ := Set.not_subset.1 haU
    have hw1 : w ≠ 1 := fun e => hwU (e ▸ U.one_mem)
    have haf : ∀ u ∈ U, a u = u := by
      intro u hu
      rcases eq_one_or_eq_of_card_two htr hw hw1 (G6.mem_commV_of_mem (Subgroup.mem_zpowers a) u)
        with h1 | h1
      · exact mul_inv_eq_one.1 h1
      · exfalso
        apply hwU
        rw [← h1]
        exact U.mul_mem (hUG a h.mem u hu) (U.inv_mem hu)
    have hKU : K ≤ fixPt U := by
      rw [hK]
      refine conjClosure_le fun g hg z hz => mem_fixPt.2 fun u hu => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      have h1 : (g * a ^ k * g⁻¹) u = g ((a ^ k) (g⁻¹ u)) := rfl
      have hgu : g⁻¹ u ∈ U := hUG _ (G.inv_mem hg) u hu
      have hak : (a ^ k) (g⁻¹ u) = g⁻¹ u := by
        have ha' : a ∈ fixPt U := mem_fixPt.2 haf
        exact mem_fixPt.1 ((fixPt U).zpow_mem ha' k) _ hgu
      rw [h1, hak]
      simp
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := IsQuasisimple.exists_ne hq
    apply hxy
    apply Subtype.ext
    exact comm_of_fix_commV (fun z hz u hu => mem_fixPt.1 (hKU (hLK hz)) u hu) x hx y hy

theorem exists_moved_of_fstar [Finite V] (h : Hyp61 G a)
    (hq : CFSG.IsQuasisimple ↥(quasithinGenFitting (conjClosure (Subgroup.zpowers a) G))) :
    ∃ v, a v * v⁻¹ ∉ fixV (quasithinGenFitting (conjClosure (Subgroup.zpowers a) G)) := by
  set K := conjClosure (Subgroup.zpowers a) G with hK
  set L := quasithinGenFitting K with hL
  by_contra hcon
  push Not at hcon
  have hGL : G ≤ Subgroup.normalizer
      (quasithinGenFitting (conjClosure (Subgroup.zpowers a) G) : Set (MulAut V)) :=
    le_normalizer_fstar
  have hCG : ∀ g ∈ G, ∀ c ∈ fixV L, g c ∈ fixV L := by
    intro g hg c hc
    rw [mem_fixV] at hc ⊢
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (hGL (G.inv_mem hg)) l).1 hl
      simpa using this
    have := hc _ hl'
    calc l (g c) = g ((g⁻¹ * l * g) c) := by simp
      _ = g c := by rw [this]
  have hKV : commV K = ⊤ := commV_classK h
  have hcl : Subgroup.closure (transSet G a) = K := closure_transSet G a
  have hle : commV K ≤ fixV L := by
    rw [← hcl]
    refine G6.commV_closure_le ?_
    rintro _ ⟨g, hg, rfl⟩ v
    have : (g * a * g⁻¹) v * v⁻¹ = g (a (g⁻¹ v) * (g⁻¹ v)⁻¹) := by simp
    rw [this]
    exact hCG g hg _ (hcon _)
  rw [hKV] at hle
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := IsQuasisimple.exists_ne hq
  apply hxy
  have hx1 : x = 1 := MulEquiv.ext fun v => (mem_fixV.1 (hle (Subgroup.mem_top v))) x hx
  have hy1 : y = 1 := MulEquiv.ext fun v => (mem_fixV.1 (hle (Subgroup.mem_top v))) y hy
  apply Subtype.ext
  simp [hx1, hy1]

end CFSG.Quasithin.G64
