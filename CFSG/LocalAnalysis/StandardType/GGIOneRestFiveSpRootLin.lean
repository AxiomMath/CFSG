module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFinNum
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeOrthSp
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec

public section

namespace CFSG.StandardType.SpRootLin

open Module CFSG.Assembly TableB CFSG.StandardType.TwoThree
open CFSG.Open (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

section Generic

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem bilin_fix_sub_one (B : LinearMap.BilinForm K V) (g : Module.End K V)
    (hg : ∀ v w, B (g v) (g w) = B v w) {w : V} (hw : g w = w) (y : V) :
    B w ((g - 1) y) = 0 := by
  have h1 : B w (g y) = B w y := by
    have h := hg w y
    rwa [hw] at h
  rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, h1, sub_self]

theorem ker_inf_range_sub_one [CharP K 2] (g : Module.End K V) (hg3 : g ^ 3 = 1) :
    LinearMap.ker (g - 1) ⊓ LinearMap.range (g - 1) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxk, hxr⟩
  obtain ⟨y, rfl⟩ := hxr
  set x := (g - 1) y with hx
  have hgx : g x = x := by
    have h := LinearMap.mem_ker.mp hxk
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
  have hkey : (g ^ 2 + g + 1) * (g - 1) = 0 := by
    have e : (g ^ 2 + g + 1) * (g - 1) = g ^ 3 - 1 := by noncomm_ring
    rw [e, hg3, sub_self]
  have hx0 : (g ^ 2 + g + 1 : Module.End K V) x = 0 := by
    have h := congrArg (fun f : Module.End K V => f y) hkey
    simpa [Module.End.mul_apply, hx] using h
  have h2 : x + x = 0 := by
    rw [← two_smul K x, show (2 : K) = 0 by exact_mod_cast CharP.cast_eq_zero K 2, zero_smul]
  have hsum : (g ^ 2 + g + 1 : Module.End K V) x = x := by
    rw [LinearMap.add_apply, LinearMap.add_apply, pow_two, Module.End.mul_apply, hgx, hgx,
      Module.End.one_apply]
    calc x + x + x = (x + x) + x := by abel
      _ = x := by rw [h2, zero_add]
  rw [Submodule.mem_bot]
  rw [← hsum, hx0]

theorem ker_sup_range_sub_one [CharP K 2] (g : Module.End K V) (hg3 : g ^ 3 = 1) :
    LinearMap.ker (g - 1) ⊔ LinearMap.range (g - 1) = ⊤ := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (g - 1))
    (LinearMap.range (g - 1))
  rw [ker_inf_range_sub_one g hg3, finrank_bot, add_zero] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker (g - 1)
  apply Submodule.eq_top_of_finrank_eq
  omega

theorem fix_of_mem_ker_sub_one (g : Module.End K V) {w : V} (hw : w ∈ LinearMap.ker (g - 1)) :
    g w = w := by
  have h := LinearMap.mem_ker.mp hw
  rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h

theorem range_sub_one_le_orth (B : LinearMap.BilinForm K V) (g : Module.End K V)
    (hg : ∀ v w, B (g v) (g w) = B v w) :
    LinearMap.range (g - 1) ≤ B.orthogonal (LinearMap.ker (g - 1)) := by
  rintro x ⟨y, rfl⟩ w hw
  exact bilin_fix_sub_one B g hg (fix_of_mem_ker_sub_one g hw) y

theorem ker_sup_orth_eq_top [CharP K 2] (B : LinearMap.BilinForm K V) (g : Module.End K V)
    (hg : ∀ v w, B (g v) (g w) = B v w) (hg3 : g ^ 3 = 1) :
    LinearMap.ker (g - 1) ⊔ B.orthogonal (LinearMap.ker (g - 1)) = ⊤ := by
  rw [eq_top_iff, ← ker_sup_range_sub_one g hg3]
  exact sup_le_sup_left (range_sub_one_le_orth B g hg) _

end Generic

section Rank

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} [NeZero m]

theorem isElemAbelian_of_le {G : Type*} [Group G] {p : ℕ} {A X : Subgroup G}
    (hA : IsElemAbelian p A) (h : X ≤ A) : IsElemAbelian p X :=
  ⟨⟨⟨fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA (h a.2) (h b.2))⟩⟩,
    fun x hx => hA.2 x (h hx)⟩

theorem spRep_inv_apply (a : LargeEvenProj (LargeEvenSpGroup K m)) (v : Fin m ⊕ Fin m → K) :
    (SmallRule.spRep a⁻¹ : Module.End K (Fin m ⊕ Fin m → K))
      ((SmallRule.spRep a : Module.End K (Fin m ⊕ Fin m → K)) v) = v := by
  rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
    Units.val_one, Module.End.one_apply]

theorem spRep_apply_inv (a : LargeEvenProj (LargeEvenSpGroup K m)) (v : Fin m ⊕ Fin m → K) :
    (SmallRule.spRep a : Module.End K (Fin m ⊕ Fin m → K))
      ((SmallRule.spRep a⁻¹ : Module.End K (Fin m ⊕ Fin m → K)) v) = v := by
  rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
    Units.val_one, Module.End.one_apply]

theorem exists_ne_one_fix (hK : Nat.card K = 2)
    {A : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))} (hA : IsElemAbelian 3 A)
    (h27 : 27 ≤ Nat.card A) {T : Submodule K (Fin m ⊕ Fin m → K)}
    (hT2 : Module.finrank K T ≤ 2)
    (hTA : ∀ a ∈ A, ∀ t ∈ T, (SmallRule.spRep a : Module.End K (Fin m ⊕ Fin m → K)) t ∈ T) :
    ∃ t ∈ A, t ≠ 1 ∧
      ∀ v ∈ T, (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) v = v := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype T := Fintype.ofFinite T
  let σ : A → Equiv.Perm T := fun a =>
    { toFun := fun v => ⟨(SmallRule.spRep (a : LargeEvenProj (LargeEvenSpGroup K m)) :
        Module.End K (Fin m ⊕ Fin m → K)) v.1, hTA a a.2 v.1 v.2⟩
      invFun := fun v => ⟨(SmallRule.spRep ((a : LargeEvenProj (LargeEvenSpGroup K m))⁻¹) :
        Module.End K (Fin m ⊕ Fin m → K)) v.1, hTA (a⁻¹) (A.inv_mem a.2) v.1 v.2⟩
      left_inv := fun v => Subtype.ext (spRep_inv_apply _ _)
      right_inv := fun v => Subtype.ext (spRep_apply_inv _ _) }
  have hσ : Function.Injective σ := by
    intro a b hab
    have hfix : ∀ v ∈ T, (SmallRule.spRep ((a : LargeEvenProj (LargeEvenSpGroup K m))⁻¹ *
        (b : LargeEvenProj (LargeEvenSpGroup K m))) :
          Module.End K (Fin m ⊕ Fin m → K)) v = v := by
      intro v hv
      have h1 := congrArg (fun p : Equiv.Perm T => (p ⟨v, hv⟩ : T).1) hab
      have h2 : (SmallRule.spRep (a : LargeEvenProj (LargeEvenSpGroup K m)) :
          Module.End K (Fin m ⊕ Fin m → K)) v =
            (SmallRule.spRep (b : LargeEvenProj (LargeEvenSpGroup K m)) :
              Module.End K (Fin m ⊕ Fin m → K)) v := h1
      rw [map_mul, Units.val_mul, Module.End.mul_apply, ← h2, spRep_inv_apply]
    have hone : (a : LargeEvenProj (LargeEvenSpGroup K m))⁻¹ *
        (b : LargeEvenProj (LargeEvenSpGroup K m)) = 1 := by
      by_contra hne
      obtain ⟨v, hv, hv'⟩ := hcon _ (A.mul_mem (A.inv_mem a.2) b.2) hne
      exact hv' (hfix v hv)
    exact Subtype.ext (inv_mul_eq_one.mp hone)
  have hcardσ : Nat.card A ≤ Nat.card (Equiv.Perm T) := Nat.card_le_card_of_injective σ hσ
  have hperm : Nat.card (Equiv.Perm T) = Nat.factorial (Nat.card T) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.card_eq_fintype_card]
  have hT4 : Nat.card T ≤ 4 := by
    have h := Module.card_eq_pow_finrank (K := K) (V := T)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card (α := K), hK] at h
    rw [h]
    calc 2 ^ Module.finrank K T ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hT2
      _ = 4 := by norm_num
  have hfac : Nat.factorial (Nat.card T) ≤ Nat.factorial 4 := Nat.factorial_le hT4
  have h24 : Nat.factorial 4 = 24 := by decide
  omega

theorem exists_two_dim_fix (hK : Nat.card K = 2)
    {A : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))} (hA : IsElemAbelian 3 A)
    (hcard : 3 ^ (m - 1) ≤ Nat.card A) (h27 : 27 ≤ Nat.card A)
    {T : Submodule K (Fin m ⊕ Fin m → K)} (hT0 : T ≠ ⊥) (hT2 : Module.finrank K T ≤ 2)
    (hTiso : ∀ u ∈ T, ∀ v ∈ T, CFSG.ClassicalInvolution.Models.SymplecticPairs.form u v = 0)
    (hTA : ∀ a ∈ A, ∀ t ∈ T, (SmallRule.spRep a : Module.End K (Fin m ⊕ Fin m → K)) t ∈ T) :
    ∃ t ∈ A, t ≠ 1 ∧ (∀ v ∈ T, (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) v = v) ∧
      Module.finrank K (LinearMap.range
        ((SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) - 1)) = 2 ∧
      ∀ s ∈ A, (∀ w, (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) w = w →
        (SmallRule.spRep s : Module.End K (Fin m ⊕ Fin m → K)) w = w) →
          s ∈ Subgroup.zpowers t := by
  classical
  obtain ⟨t₀, ht₀A, ht₀1, ht₀T⟩ := exists_ne_one_fix hK hA h27 hT2 hTA
  set X : Subgroup (LargeEvenProj (LargeEvenSpGroup K m)) :=
    A ⊓ (TwoThree.fixG T).comap (SmallRule.spRep (K := K) (m := m)) with hXdef
  have hmemX : ∀ a, a ∈ X ↔
      a ∈ A ∧ ∀ v ∈ T, (SmallRule.spRep a : Module.End K (Fin m ⊕ Fin m → K)) v = v := by
    intro a
    rw [hXdef, Subgroup.mem_inf, Subgroup.mem_comap]
    rfl
  have ht₀X : t₀ ∈ X := (hmemX t₀).mpr ⟨ht₀A, ht₀T⟩
  have hXne : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at ht₀X
    exact ht₀1 ht₀X
  let Φ : LargeEvenProj (LargeEvenSpGroup K m) ≃* StatedSp m K := TableBSymp.spProjEquivSp
  have hXA : IsElemAbelian 3 X := isElemAbelian_of_le hA (fun a ha => ((hmemX a).mp ha).1)
  have hXmA : IsElemAbelian 3 (X.map Φ.toMonoidHom) := TableB.isElemAbelian_map hXA _
  have hXm_ne : X.map Φ.toMonoidHom ≠ ⊥ := fun h =>
    hXne ((Subgroup.map_eq_bot_iff_of_injective _ Φ.injective).mp h)
  obtain ⟨g, hgX, hg1, hgmin, -, heven⟩ :=
    TwoThreeOrth.exists_minimal_node_sp hK hXmA hXm_ne
  obtain ⟨t, htX, htg⟩ := Subgroup.mem_map.mp hgX
  subst htg
  have htA : t ∈ A := ((hmemX t).mp htX).1
  have htfix : ∀ v ∈ T, (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) v = v :=
    ((hmemX t).mp htX).2
  have ht1 : t ≠ 1 := fun h => hg1 (by rw [h, map_one])
  have ht3 : t ^ 3 = 1 := hA.2 t htA
  have hρΦ : ∀ x : LargeEvenProj (LargeEvenSpGroup K m),
      (SmallRule.spRep x : Module.End K (Fin m ⊕ Fin m → K)) =
        Matrix.toLin' (mat m K (Φ x)) := by
    intro x
    apply LinearMap.ext
    intro v
    rw [SmallRule.spRep_apply, Matrix.toLin'_apply]
  have hgmin' : ∀ s ∈ X, (∀ w, (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) w = w →
      (SmallRule.spRep s : Module.End K (Fin m ⊕ Fin m → K)) w = w) →
        s ∈ Subgroup.zpowers t := by
    intro s hs hfix
    have hmem : Φ s ∈ X.map Φ.toMonoidHom := Subgroup.mem_map_of_mem _ hs
    have hfix' : ∀ w, Matrix.mulVec (mat m K (Φ t)) w = w →
        Matrix.mulVec (mat m K (Φ s)) w = w := by
      intro w hw
      have hw' : (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) w = w := by
        rw [SmallRule.spRep_apply]
        exact hw
      have h1 := hfix w hw'
      rw [SmallRule.spRep_apply] at h1
      exact h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgmin (Φ s) hmem hfix')
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Φ.injective (by rw [map_zpow]; exact hk)⟩
  have hiso : ∀ v w : Fin m ⊕ Fin m → K,
      SmallRule.spBilin K m ((SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) v)
        ((SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) w) =
          SmallRule.spBilin K m v w :=
    fun v w => SmallRule.spRep_isometry t v w
  have hρ3 : (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) ^ 3 = 1 := by
    have h3u : (SmallRule.spRep t) ^ 3 = (1 : (Module.End K (Fin m ⊕ Fin m → K))ˣ) := by
      rw [← map_pow, ht3, map_one]
    have h := congrArg Units.val h3u
    simpa using h
  have hWc0 := ker_sup_orth_eq_top (SmallRule.spBilin K m)
    (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) hiso hρ3
  have hfinV : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, ← two_mul]
  have hrk := LinearMap.finrank_range_add_finrank_ker
    ((SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) - 1)
  rw [hfinV] at hrk
  have heven' : Even (Module.finrank K (LinearMap.range
      ((SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) - 1))) := by
    rw [hρΦ t]
    exact heven
  have hu0 : Module.finrank K (LinearMap.range
      ((SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) - 1)) ≠ 0 := by
    intro h0
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot, sub_eq_zero] at h0
    apply ht1
    apply SmallRule.spRep_injective
    rw [map_one]
    exact Units.ext (by rw [Units.val_one]; exact h0)
  obtain ⟨W, hWdef⟩ : ∃ W : Submodule K (Fin m ⊕ Fin m → K),
      W = LinearMap.ker ((SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) - 1) :=
    ⟨_, rfl⟩
  have hWfix : ∀ w ∈ W, (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) w = w := by
    intro w hw
    rw [hWdef] at hw
    exact fix_of_mem_ker_sub_one _ hw
  have hWc : W ⊔ (SmallRule.spBilin K m).orthogonal W = ⊤ := by
    rw [hWdef]
    exact hWc0
  have hfinW : Module.finrank K W + Module.finrank K (LinearMap.range
      ((SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) - 1)) = 2 * m := by
    rw [hWdef]
    omega
  have hTW : T ≤ W := by
    intro v hv
    rw [hWdef, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact htfix v hv
  have hdT : 1 ≤ Module.finrank K T :=
    Nat.pos_of_ne_zero (fun h => hT0 (Submodule.finrank_eq_zero.mp h))
  have hTWfin : Module.finrank K T ≤ Module.finrank K W := Submodule.finrank_mono hTW
  have hXend_card : Nat.card (A.map (SmallRule.spRep (K := K) (m := m))) = Nat.card A :=
    Subgroup.card_map_of_injective SmallRule.spRep_injective
  have hcomm : ∀ x ∈ A.map (SmallRule.spRep (K := K) (m := m)),
      ∀ y ∈ A.map (SmallRule.spRep (K := K) (m := m)), x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hA ha hb]
  have hexp : ∀ x ∈ A.map (SmallRule.spRep (K := K) (m := m)), x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.2 a ha, map_one]
  have hinv : ∀ x ∈ A.map (SmallRule.spRep (K := K) (m := m)), ∀ v w : Fin m ⊕ Fin m → K,
      SmallRule.spBilin K m ((x : Module.End K (Fin m ⊕ Fin m → K)) v)
        ((x : Module.End K (Fin m ⊕ Fin m → K)) w) = SmallRule.spBilin K m v w := by
    rintro _ ⟨a, ha, rfl⟩ v w
    exact SmallRule.spRep_isometry a v w
  have hWX : ∀ x ∈ A.map (SmallRule.spRep (K := K) (m := m)), ∀ w ∈ W,
      (x : Module.End K (Fin m ⊕ Fin m → K)) w ∈ W := by
    rintro _ ⟨a, ha, rfl⟩ w hw
    have hc : (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) *
        (SmallRule.spRep a : Module.End K (Fin m ⊕ Fin m → K)) =
          (SmallRule.spRep a : Module.End K (Fin m ⊕ Fin m → K)) *
            (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) := by
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul,
        TableB.IsElemAbelian.comm hA htA ha]
    have hw' : (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) w = w := hWfix w hw
    rw [hWdef, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    calc (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) ((SmallRule.spRep a :
            Module.End K (Fin m ⊕ Fin m → K)) w)
        = ((SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) *
            (SmallRule.spRep a : Module.End K (Fin m ⊕ Fin m → K))) w := by
          rw [Module.End.mul_apply]
      _ = ((SmallRule.spRep a : Module.End K (Fin m ⊕ Fin m → K)) *
            (SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K))) w := by rw [hc]
      _ = (SmallRule.spRep a : Module.End K (Fin m ⊕ Fin m → K)) w := by
          rw [Module.End.mul_apply, hw']
  have hTiso' : ∀ u ∈ T, ∀ v ∈ T, SmallRule.spBilin K m u v = 0 := by
    intro u hu v hv
    rw [SmallRule.spBilin_apply]
    exact hTiso u hu v hv
  have hTX : ∀ x ∈ A.map (SmallRule.spRep (K := K) (m := m)), ∀ t' ∈ T,
      (x : Module.End K (Fin m ⊕ Fin m → K)) t' ∈ T := by
    rintro _ ⟨a, ha, rfl⟩ t' ht'
    exact hTA a ha t' ht'
  have hsq := SpFin.card_sq_le_sub hK (SmallRule.spBilin K m) SmallRule.spBilin_nondegenerate
    SmallRule.spBilin_isRefl (A.map (SmallRule.spRep (K := K) (m := m))) hcomm hexp hinv hWX
    hWc hTW hTiso' hTX
  have hsub : (A.map (SmallRule.spRep (K := K) (m := m))) ⊓ TwoThree.fixG W ≤
      Subgroup.zpowers (SmallRule.spRep t) := by
    intro y hy
    obtain ⟨hyA, hyW⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hyA
    have hyW' : ∀ u ∈ W, (SmallRule.spRep a : Module.End K (Fin m ⊕ Fin m → K)) u = u := hyW
    have haX : a ∈ X := (hmemX a).mpr ⟨ha, fun v hv => hyW' v (hTW hv)⟩
    have hzp := hgmin' a haX (fun w hw => hyW' w (by
      rw [hWdef, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact hw))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzp
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← hk, map_zpow]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Module.End K (Fin m ⊕ Fin m → K))ˣ := TwoThree.finite_units_end
  have hfixcard : Nat.card ↥((A.map (SmallRule.spRep (K := K) (m := m))) ⊓
      TwoThree.fixG W) ≤ 3 := by
    calc Nat.card ↥((A.map (SmallRule.spRep (K := K) (m := m))) ⊓ TwoThree.fixG W)
        ≤ Nat.card ↥(Subgroup.zpowers (SmallRule.spRep t)) :=
          Subgroup.card_le_of_le hsub
      _ = orderOf (SmallRule.spRep t) := Nat.card_zpowers _
      _ = orderOf t := orderOf_injective _ SmallRule.spRep_injective t
      _ = 3 := orderOf_eq_prime ht3 ht1
  have hsq' : Nat.card A ^ 2 ≤ 3 ^ (Module.finrank K W - Module.finrank K T) * 3 ^ 2 := by
    rw [hXend_card] at hsq
    have h2 : Nat.card ↥((A.map (SmallRule.spRep (K := K) (m := m))) ⊓ TwoThree.fixG W) ^ 2 ≤
        3 ^ 2 := Nat.pow_le_pow_left hfixcard 2
    calc Nat.card A ^ 2 ≤ 3 ^ (Module.finrank K W - Module.finrank K T) *
          Nat.card ↥((A.map (SmallRule.spRep (K := K) (m := m))) ⊓ TwoThree.fixG W) ^ 2 := hsq
      _ ≤ 3 ^ (Module.finrank K W - Module.finrank K T) * 3 ^ 2 :=
          Nat.mul_le_mul_left _ h2
  have hlow : 3 ^ ((m - 1) * 2) ≤ Nat.card A ^ 2 := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hcard 2
  have hcomb : 3 ^ ((m - 1) * 2) ≤ 3 ^ ((Module.finrank K W - Module.finrank K T) + 2) := by
    rw [pow_add]
    exact hlow.trans hsq'
  have hexp2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hcomb
  have hm1 : 0 < m := Nat.pos_of_neZero m
  have hu2 : Module.finrank K (LinearMap.range
      ((SmallRule.spRep t : Module.End K (Fin m ⊕ Fin m → K)) - 1)) = 2 := by
    obtain ⟨c, hc⟩ := heven'
    omega
  refine ⟨t, htA, ht1, htfix, hu2, ?_⟩
  intro s hs hfix
  exact hgmin' s ((hmemX s).mpr ⟨hs, fun v hv => hfix v (htfix v hv)⟩) hfix

end Rank

end CFSG.StandardType.SpRootLin
