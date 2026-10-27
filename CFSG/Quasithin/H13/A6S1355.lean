module

public import CFSG.Quasithin.H13.A6S1354

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem c012_facts : Perm.sign (swap (0 : Fin 6) 1 * swap 1 2) = 1 ∧
    act4f (swap 0 1 * swap 1 2) e0123 = e0123 ∧ (swap (0 : Fin 6) 1 * swap 1 2) ^ 3 = 1 := by
  decide

theorem c012_pow_four_pow (a : ℕ) :
    (swap (0 : Fin 6) 1 * swap 1 2) ^ (4 ^ a) = swap 0 1 * swap 1 2 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, pow_mul, ih]
    decide

theorem W3_of_fix : ∀ σ : Perm (Fin 6), act4f σ e0123 = e0123 → ∀ x : P6, InW4 x → InW3 x →
    InW3 (act4f σ x) := by
  decide +kernel

@[expose] def InW34 (x : P6) : Prop := InW4 x ∧ InW3 x

instance : DecidablePred InW34 := fun x => by unfold InW34; infer_instance

@[expose] def GenHyp (y : P6) : Prop := InW34 y ∧ y ≠ 1 ∧ y ≠ e0123

instance : DecidablePred GenHyp := fun y => by unfold GenHyp; infer_instance

@[expose] def Span8 (y x : P6) : Prop :=
  x = 1 ∨ x = e0123 ∨ x = y ∨ x = y * e0123 ∨ x = act4f (swap 0 1 * swap 1 2) y ∨
    x = act4f (swap 0 1 * swap 1 2) y * e0123 ∨ x = y * act4f (swap 0 1 * swap 1 2) y ∨
    x = y * act4f (swap 0 1 * swap 1 2) y * e0123

instance (y x : P6) : Decidable (Span8 y x) := by unfold Span8; infer_instance

theorem W3_gen : ∀ y x : P6, GenHyp y → InW34 x → Span8 y x := by
  decide +kernel

@[expose] def SpanBasis (x : P6) : Prop :=
  x = 1 ∨ x = dv 0 1 ∨ x = dv 0 2 ∨ x = dv 0 1 * dv 0 2 ∨ x = e0123 ∨ x = dv 0 1 * e0123 ∨
    x = dv 0 2 * e0123 ∨ x = dv 0 1 * dv 0 2 * e0123

instance : DecidablePred SpanBasis := fun x => by unfold SpanBasis; infer_instance

theorem W3_span : ∀ x : P6, InW34 x → SpanBasis x := by
  decide +kernel

@[expose] def StabWit (a b : P6) : Prop :=
  ∃ σ : Perm (Fin 6), act4f σ (dv 0 1) = a ∧ act4f σ (dv 0 2) = b ∧ act4f σ e0123 = e0123 ∧
    Perm.sign σ = 1

instance (a b : P6) : Decidable (StabWit a b) := by unfold StabWit; infer_instance

@[expose] def IndepHyp (a b : P6) : Prop :=
  InW34 a ∧ InW34 b ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a ≠ e0123 ∧ b ≠ e0123 ∧ a * b ≠ e0123

instance (a b : P6) : Decidable (IndepHyp a b) := by unfold IndepHyp; infer_instance

theorem stabWit : ∀ a b : P6, IndepHyp a b → StabWit a b := by
  decide +kernel

theorem basis_facts : InW3 (dv 0 1) ∧ InW3 (dv 0 2) ∧ InW3 e0123 ∧ InW3 (dv 0 1 * dv 0 2) ∧
    dv 0 1 ≠ 1 ∧ dv 0 2 ≠ 1 ∧ dv 0 1 ≠ dv 0 2 ∧ dv 0 1 ≠ e0123 ∧ dv 0 2 ≠ e0123 ∧
    dv 0 1 * dv 0 2 ≠ e0123 := by
  decide

theorem W3sub_le_closure : W3sub ≤ Subgroup.closure ({⟨dv 0 1, dv_mem 0 1⟩,
    ⟨dv 0 2, dv_mem 0 2⟩, ⟨e0123, e0123_mem_W4⟩} : Set ↥W4) := by
  intro x hx
  have h1 : (⟨dv 0 1, dv_mem 0 1⟩ : ↥W4) ∈ Subgroup.closure ({⟨dv 0 1, dv_mem 0 1⟩,
      ⟨dv 0 2, dv_mem 0 2⟩, ⟨e0123, e0123_mem_W4⟩} : Set ↥W4) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have h2 : (⟨dv 0 2, dv_mem 0 2⟩ : ↥W4) ∈ Subgroup.closure ({⟨dv 0 1, dv_mem 0 1⟩,
      ⟨dv 0 2, dv_mem 0 2⟩, ⟨e0123, e0123_mem_W4⟩} : Set ↥W4) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have h3 : (⟨e0123, e0123_mem_W4⟩ : ↥W4) ∈ Subgroup.closure ({⟨dv 0 1, dv_mem 0 1⟩,
      ⟨dv 0 2, dv_mem 0 2⟩, ⟨e0123, e0123_mem_W4⟩} : Set ↥W4) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  rcases W3_span x ⟨x.2, hx⟩ with h | h | h | h | h | h | h | h
  · rw [show x = 1 from Subtype.ext h]
    exact Subgroup.one_mem _
  · rw [show x = ⟨dv 0 1, dv_mem 0 1⟩ from Subtype.ext h]
    exact h1
  · rw [show x = ⟨dv 0 2, dv_mem 0 2⟩ from Subtype.ext h]
    exact h2
  · rw [show x = ⟨dv 0 1, dv_mem 0 1⟩ * ⟨dv 0 2, dv_mem 0 2⟩ from Subtype.ext h]
    exact Subgroup.mul_mem _ h1 h2
  · rw [show x = ⟨e0123, e0123_mem_W4⟩ from Subtype.ext h]
    exact h3
  · rw [show x = ⟨dv 0 1, dv_mem 0 1⟩ * ⟨e0123, e0123_mem_W4⟩ from Subtype.ext h]
    exact Subgroup.mul_mem _ h1 h3
  · rw [show x = ⟨dv 0 2, dv_mem 0 2⟩ * ⟨e0123, e0123_mem_W4⟩ from Subtype.ext h]
    exact Subgroup.mul_mem _ h2 h3
  · rw [show x = ⟨dv 0 1, dv_mem 0 1⟩ * ⟨dv 0 2, dv_mem 0 2⟩ * ⟨e0123, e0123_mem_W4⟩ from
      Subtype.ext h]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem conj_z_of_normalizes {g : G} (hg : g ∈ Subgroup.normalizer (fsuV1 T V : Set G)) :
    g * S.z * g⁻¹ = S.z := by
  rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff] at hg
  rw [hg, mul_inv_cancel_right]

theorem fix_e0123 (g : ↥(Subgroup.normalizer (V : Set G))) (hg : (g : G) * S.z * (g : G)⁻¹ = S.z) :
    act4f (S.frame.ρ g) e0123 = e0123 := by
  have := (S.conj_eq_iff g ⟨S.z, S.z_mem_V⟩).1 hg
  rw [S.psi_z] at this
  exact congrArg Subtype.val this

theorem le_normalizer_pre {X : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    {Y : Subgroup ↥W4} (hY : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ X →
      ∀ y ∈ Y, act4 (S.frame.ρ g) y ∈ Y) :
    X ≤ Subgroup.normalizer (S.pre Y : Set G) := by
  intro t ht
  have hY' : ∀ (g : ↥(Subgroup.normalizer (V : Set G))), (g : G) ∈ X → ∀ x : G,
      x ∈ S.pre Y → (g : G) * x * (g : G)⁻¹ ∈ S.pre Y := by
    intro g hg x hx
    obtain ⟨hxV, hxY⟩ := S.mem_pre.1 hx
    refine S.mem_pre.2 ⟨(Subgroup.mem_normalizer_iff.mp g.2 x).mp hxV, ?_⟩
    rw [S.psi_conj g ⟨x, hxV⟩]
    exact hY _ hg _ hxY
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hY' ⟨t, hXV ht⟩ ht x
  · intro hx
    have h := hY' ⟨t, hXV ht⟩⁻¹ (X.inv_mem ht) _ hx
    simp only [InvMemClass.coe_inv, inv_inv] at h
    have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
    rwa [e] at h

theorem NLV1_le_NV3 : L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) ≤
    Subgroup.normalizer (S.V3 : Set G) := by
  refine S.le_normalizer_pre (inf_le_left.trans S.frame.L_le) fun g hg y hy => ?_
  have hfix := S.fix_e0123 g (S.conj_z_of_normalizes hg.2)
  show InW3 ((act4 (S.frame.ρ g) y : ↥W4) : P6)
  rw [act4_coe]
  exact W3_of_fix _ hfix _ y.2 hy

theorem T_le_NV1 : T ≤ Subgroup.normalizer (fsuV1 T V : Set G) := by
  intro t ht
  rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨-, hzC, -⟩ := mem_quasithinOmegaOneCenter_iff.1 (S.mem_V1_iff.2 (Or.inr rfl)).2
  exact Subgroup.mem_centralizer_iff.1 hzC t ht

theorem L1_le : S.L1 ≤ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) := oTwoRes_le _

theorem L1T_le_NV1 : S.L1 ⊔ T ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
  sup_le (S.L1_le.trans inf_le_right) S.T_le_NV1

theorem L1T_le_NV3 : S.L1 ⊔ T ≤ Subgroup.normalizer (S.V3 : Set G) :=
  sup_le (S.L1_le.trans S.NLV1_le_NV3) S.T_le_normalizer_V3

@[expose] noncomputable def img (W : Subgroup G) : Subgroup ↥W4 :=
  (W.subgroupOf V).map S.frame.ψ.toMonoidHom

theorem mem_img_iff {W : Subgroup G} (v : ↥V) : S.frame.ψ v ∈ S.img W ↔ (v : G) ∈ W := by
  constructor
  · rintro ⟨u, hu, huv⟩
    have : u = v := S.frame.ψ.injective huv
    rw [← this]
    exact hu
  · intro h
    exact ⟨v, h, rfl⟩

theorem act4_mem_img {W : Subgroup G} (g : ↥(Subgroup.normalizer (V : Set G)))
    (hgW : (g : G) ∈ Subgroup.normalizer (W : Set G)) {y : ↥W4} (hy : y ∈ S.img W) :
    act4 (S.frame.ρ g) y ∈ S.img W := by
  obtain ⟨v, rfl⟩ := S.frame.ψ.surjective y
  rw [S.mem_img_iff] at hy
  rw [← S.psi_conj g v, S.mem_img_iff]
  exact (Subgroup.mem_normalizer_iff.mp hgW v).mp hy

theorem exists_L1_c012 : ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ S.L1 ∧
    S.frame.ρ g = swap 0 1 * swap 1 2 := by
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L _).2 (Perm.mem_alternatingGroup.2 c012_facts.1)
  have hgz : (g : G) * S.z * (g : G)⁻¹ = S.z := by
    rw [S.conj_eq_iff g ⟨S.z, S.z_mem_V⟩, S.psi_z, hg]
    exact Subtype.ext c012_facts.2.1
  have hgN : (g : G) ∈ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) := by
    refine ⟨hgL, ?_⟩
    show (g : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G)
    rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
    calc (g : G) * S.z = (g : G) * S.z * (g : G)⁻¹ * g := by group
      _ = S.z * g := by rw [hgz]
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨g ^ (4 ^ a), ?_, by rw [map_pow, hg, c012_pow_four_pow]⟩
  refine Subgroup.subset_closure ⟨?_, m, hm, ?_⟩
  · simpa using Subgroup.pow_mem _ hgN (4 ^ a)
  · have h1 : (g ^ (4 ^ a)) ^ m = (g ^ (2 ^ a * m)) ^ (2 ^ a) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
      ring
    have h2 : g ^ (2 ^ a * m) = 1 := by rw [← hnm, pow_orderOf_eq_one]
    have h3 : (g ^ (4 ^ a)) ^ m = 1 := by rw [h1, h2, one_pow]
    simpa using congrArg Subtype.val h3

theorem irred_V3 (W : Subgroup G) (h1 : fsuV1 T V ≤ W) (h3 : W ≤ S.V3)
    (hN : S.L1 ⊔ T ≤ Subgroup.normalizer (W : Set G)) : W = fsuV1 T V ∨ W = S.V3 := by
  by_cases hW : W ≤ fsuV1 T V
  · exact Or.inl (le_antisymm hW h1)
  right
  refine le_antisymm h3 fun x hx => ?_
  obtain ⟨w, hwW, hwV1⟩ := IsConcreteLE.not_le_iff_exists.1 hW
  have hwV : w ∈ V := S.V3_le_V (h3 hwW)
  have hxV : x ∈ V := S.V3_le_V hx
  obtain ⟨_, hy3⟩ := S.mem_pre.1 (h3 hwW)
  obtain ⟨_, hx3⟩ := S.mem_pre.1 hx
  set y := S.frame.ψ ⟨w, hwV⟩ with hy
  have hy1 : (y : P6) ≠ 1 := fun h => hwV1 (by
    have : (⟨w, hwV⟩ : ↥V) = 1 :=
      S.frame.ψ.injective (by rw [← hy, map_one]; exact Subtype.ext h)
    rw [S.mem_V1_iff]
    exact Or.inl (congrArg Subtype.val this))
  have hyW : (y : P6) ≠ e0123 := fun h => hwV1 (by
    have : (⟨w, hwV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ :=
      S.frame.ψ.injective (by rw [← hy, S.psi_z]; exact Subtype.ext h)
    rw [S.mem_V1_iff]
    exact Or.inr (congrArg Subtype.val this))
  obtain ⟨g, hgL1, hg⟩ := S.exists_L1_c012
  have hgW : (g : G) ∈ Subgroup.normalizer (W : Set G) := hN (le_sup_left (a := S.L1) hgL1)
  have hyI : y ∈ S.img W := (S.mem_img_iff _).2 hwW
  have hzI : (⟨e0123, e0123_mem_W4⟩ : ↥W4) ∈ S.img W := by
    rw [← S.psi_z, S.mem_img_iff]
    exact h1 (S.mem_V1_iff.2 (Or.inr rfl))
  have hcI : act4 (swap 0 1 * swap 1 2) y ∈ S.img W := hg ▸ S.act4_mem_img g hgW hyI
  refine (S.mem_img_iff ⟨x, hxV⟩).1 ?_
  set x' := S.frame.ψ ⟨x, hxV⟩
  rcases W3_gen (y : P6) (x' : P6) ⟨⟨y.2, hy3⟩, hy1, hyW⟩ ⟨x'.2, hx3⟩ with
    h | h | h | h | h | h | h | h
  · rw [show x' = 1 from Subtype.ext h]
    exact (S.img W).one_mem
  · rw [show x' = ⟨e0123, e0123_mem_W4⟩ from Subtype.ext h]
    exact hzI
  · rw [show x' = y from Subtype.ext h]
    exact hyI
  · rw [show x' = y * ⟨e0123, e0123_mem_W4⟩ from Subtype.ext h]
    exact (S.img W).mul_mem hyI hzI
  · rw [show x' = act4 (swap 0 1 * swap 1 2) y from Subtype.ext h]
    exact hcI
  · rw [show x' = act4 (swap 0 1 * swap 1 2) y * ⟨e0123, e0123_mem_W4⟩ from Subtype.ext h]
    exact (S.img W).mul_mem hcI hzI
  · rw [show x' = y * act4 (swap 0 1 * swap 1 2) y from Subtype.ext h]
    exact (S.img W).mul_mem hyI hcI
  · rw [show x' = y * act4 (swap 0 1 * swap 1 2) y * ⟨e0123, e0123_mem_W4⟩ from Subtype.ext h]
    exact (S.img W).mul_mem ((S.img W).mul_mem hyI hcI) hzI

theorem centralizer_V3_le (h13315 : Stmt13_3_15) :
    Subgroup.centralizer (S.V3 : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  classical
  let X : Subgroup G := if IsHatA6 L then oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆ else L₁Of L S.V2
  have hX₁ : IsHatA6 L → X = oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆ := fun h => by simp [X, h]
  have hX₂ : ¬ IsHatA6 L → X = L₁Of L S.V2 := fun h => by simp [X, h]
  obtain ⟨-, -, -, -, -, -, -, -, h9⟩ := h13315 G T L V S.V2 X _ S.h13 S.irr S.zv S.isV2
    S.not_iso_a5 hX₁ hX₂ rfl
  exact (h9 S.V3 S.V2_le_V3 S.V3_le_V S.T_le_normalizer_V3 S.card_V3).1

theorem G1_inf_G3_le (h13315 : Stmt13_3_15) :
    S.G1 ⊓ Subgroup.normalizer (S.V3 : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  rintro g ⟨hg1, hg3⟩
  have hgz : g * S.z * g⁻¹ = S.z := by
    have h : g * S.z = S.z * g := Subgroup.mem_centralizer_singleton_iff.mp hg1
    rw [h, mul_inv_cancel_right]
  have hconj : ∀ v : G, v ∈ S.V3 → g * v * g⁻¹ ∈ S.V3 := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hg3 v).mp hv
  have hpre : ∀ x : ↥W4, InW3 (x : P6) → ((S.frame.ψ.symm x : ↥V) : G) ∈ S.V3 := by
    intro x hx
    have e : S.frame.ψ ⟨((S.frame.ψ.symm x : ↥V) : G), (S.frame.ψ.symm x).2⟩ = x :=
      S.frame.ψ.apply_symm_apply x
    exact S.mem_pre.2 ⟨(S.frame.ψ.symm x).2, by rw [e]; exact hx⟩
  let β : ∀ x : ↥W4, InW3 (x : P6) → ↥W4 := fun x hx =>
    S.frame.ψ ⟨g * (S.frame.ψ.symm x : G) * g⁻¹, S.V3_le_V (hconj _ (hpre x hx))⟩
  have hβ3 : ∀ x hx, InW3 (β x hx : P6) := fun x hx => (S.mem_pre.1 (hconj _ (hpre x hx))).2
  have hβinj : ∀ x y hx hy, β x hx = β y hy → x = y := by
    intro x y hx hy h
    have h1 := congrArg Subtype.val (S.frame.ψ.injective h)
    simp only [mul_left_inj, mul_right_inj] at h1
    exact S.frame.ψ.symm.injective (Subtype.ext h1)
  have hβmul : ∀ x y hx hy hxy, β (x * y) hxy = β x hx * β y hy := by
    intro x y hx hy hxy
    simp only [β]
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    group
  have hβz : β ⟨e0123, e0123_mem_W4⟩ basis_facts.2.2.1 = ⟨e0123, e0123_mem_W4⟩ := by
    have h : (⟨g * (S.frame.ψ.symm ⟨e0123, e0123_mem_W4⟩ : G) * g⁻¹,
        S.V3_le_V (hconj _ (hpre _ basis_facts.2.2.1))⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ :=
      Subtype.ext hgz
    exact (congrArg S.frame.ψ h).trans S.psi_z
  have hβ1 : β 1 (by decide) = 1 := by
    have h : (⟨g * (S.frame.ψ.symm 1 : G) * g⁻¹, S.V3_le_V (hconj _ (hpre 1 (by decide)))⟩ :
        ↥V) = 1 := Subtype.ext (by simp)
    exact (congrArg S.frame.ψ h).trans (map_one _)
  obtain ⟨b1, b2, b3, b12, n1, n2, n12, n1e, n2e, n12e⟩ := basis_facts
  set u1 : ↥W4 := ⟨dv 0 1, dv_mem 0 1⟩
  set u2 : ↥W4 := ⟨dv 0 2, dv_mem 0 2⟩
  set e3 : ↥W4 := ⟨e0123, e0123_mem_W4⟩
  have ha1 : (β u1 b1 : P6) ≠ 1 := fun h =>
    n1 (congrArg Subtype.val (hβinj u1 1 b1 (by decide) (by rw [hβ1]; exact Subtype.ext h)))
  have hb1 : (β u2 b2 : P6) ≠ 1 := fun h =>
    n2 (congrArg Subtype.val (hβinj u2 1 b2 (by decide) (by rw [hβ1]; exact Subtype.ext h)))
  have hab : (β u1 b1 : P6) ≠ β u2 b2 := fun h =>
    n12 (congrArg Subtype.val (hβinj u1 u2 b1 b2 (Subtype.ext h)))
  have hae : (β u1 b1 : P6) ≠ e0123 := fun h =>
    n1e (congrArg Subtype.val (hβinj u1 e3 b1 b3 (by rw [hβz]; exact Subtype.ext h)))
  have hbe : (β u2 b2 : P6) ≠ e0123 := fun h =>
    n2e (congrArg Subtype.val (hβinj u2 e3 b2 b3 (by rw [hβz]; exact Subtype.ext h)))
  have habe : (β u1 b1 : P6) * β u2 b2 ≠ e0123 := fun h =>
    n12e (congrArg Subtype.val (hβinj (u1 * u2) e3 b12 b3
      (by rw [hβz, hβmul u1 u2 b1 b2 b12]; exact Subtype.ext h)))
  obtain ⟨σ, hσ1, hσ2, hσz, hσs⟩ := stabWit _ _ ⟨⟨(β u1 b1).2, hβ3 u1 b1⟩,
    ⟨(β u2 b2).2, hβ3 u2 b2⟩, ha1, hb1, hab, hae, hbe, habe⟩
  obtain ⟨l, hlL, hl⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.2 hσs)
  have hagree : ∀ x : ↥W4, ∀ hx : InW3 (x : P6), ((act4 σ x : ↥W4) : P6) = β x hx →
      g * (S.frame.ψ.symm x : G) * g⁻¹ = (l : G) * (S.frame.ψ.symm x : G) * (l : G)⁻¹ := by
    intro x hx h
    have h1 := S.psi_conj l (S.frame.ψ.symm x)
    rw [MulEquiv.apply_symm_apply, hl] at h1
    have h2 : S.frame.ψ ⟨(l : G) * (S.frame.ψ.symm x : G) * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp l.2 _).mp (S.frame.ψ.symm x).2⟩ = β x hx :=
      h1.trans (Subtype.ext h)
    exact (congrArg Subtype.val (S.frame.ψ.injective h2)).symm
  have hgen : ∀ x : ↥W4, x ∈ Subgroup.closure ({u1, u2, e3} : Set ↥W4) →
      g * (S.frame.ψ.symm x : G) * g⁻¹ = (l : G) * (S.frame.ψ.symm x : G) * (l : G)⁻¹ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact hagree _ b1 hσ1
      · exact hagree _ b2 hσ2
      · exact hagree _ b3 (hσz.trans (congrArg Subtype.val hβz).symm)
    | one => simp
    | mul x y _ _ hx hy =>
      rw [map_mul, Subgroup.coe_mul]
      have e1 : ∀ c a b : G, c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := fun c a b => by
        group
      rw [e1, e1, hx, hy]
    | inv x _ hx =>
      rw [map_inv, Subgroup.coe_inv]
      have e2 : ∀ c a : G, c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := fun c a => by group
      rw [e2, e2, hx]
  have hC : (l : G)⁻¹ * g ∈ Subgroup.centralizer (S.V3 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨hvV, hv3⟩ := S.mem_pre.1 hv
    have h := hgen _ (W3sub_le_closure hv3)
    rw [MulEquiv.symm_apply_apply] at h
    calc v * ((l : G)⁻¹ * g) = (l : G)⁻¹ * ((l : G) * v * (l : G)⁻¹) * g := by group
      _ = (l : G)⁻¹ * (g * v * g⁻¹) * g := by rw [← h]
      _ = (l : G)⁻¹ * g * v := by group
  have := Subgroup.mul_mem _ l.2 (S.centralizer_V3_le h13315 hC)
  rwa [mul_inv_cancel_left] at this

end Setting4

end CFSG.Quasithin.H13.A6
