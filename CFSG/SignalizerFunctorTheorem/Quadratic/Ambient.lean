module

public import Mathlib
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.SignalizerFunctor.CentralizerImages
public import CFSG.SignalizerFunctorTheorem.Quadratic.Core
public import CFSG.GroupTheory.PCore.Defs

public section

open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.Quadratic

variable {G : Type*} [Group G] [Finite G]

@[expose] def QOneAmb (V₀ E : Subgroup G) : Prop :=
  ∀ B : Subgroup G, B ≤ E →
    Nat.card B * Nat.card ↥(V₀ ⊓ Subgroup.centralizer (B : Set G)) ≤
      Nat.card E * Nat.card ↥(V₀ ⊓ Subgroup.centralizer (E : Set G))

section LinAlg

variable {q : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod q) V]

private theorem amb_pow_apply_mem {d : LGL q V} {W : Submodule (ZMod q) V}
    (hd : ∀ w ∈ W, d w ∈ W) (k : ℕ) : ∀ w ∈ W, (d ^ k) w ∈ W := by
  induction k with
  | zero => intro w hw; simpa using hw
  | succ k ih =>
    intro w hw
    rw [pow_succ]
    exact ih _ (hd w hw)

private theorem amb_pow_fixed {d : LGL q V} (hd3 : d ^ 3 = 1) {m : ℕ} (hm : ¬ 3 ∣ m)
    {W : Submodule (ZMod q) V} (hfix : ∀ w ∈ W, d w = w → w = 0) {w : V} (hw : w ∈ W)
    (h : (d ^ m) w = w) : w = 0 := by
  have hm' : m % 3 = 1 ∨ m % 3 = 2 := by omega
  have e : d ^ m = d ^ (m % 3) := by
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hd3, one_pow, one_mul]
  rw [e] at h
  rcases hm' with h1 | h2
  · rw [h1, pow_one] at h
    exact hfix w hw h
  · rw [h2] at h
    apply hfix w hw
    have h3 : (d ^ 3) w = w := by rw [hd3]; rfl
    calc d w = d ((d ^ 2) w) := by rw [h]
      _ = (d ^ 3) w := by rw [pow_succ' d 2]; rfl
      _ = w := h3

end LinAlg

section Amb

open scoped IsMulCommutative

variable {q : ℕ} [Fact q.Prime] {V₀ : Subgroup G} [IsElementaryAbelian q V₀]

omit [Finite G]

private def amb_conjMul (g : Subgroup.normalizer (V₀ : Set G)) : V₀ ≃* V₀ where
  toFun x := ⟨(g : G) * (x : G) * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 x).mp x.2⟩
  invFun x := ⟨(g : G)⁻¹ * (x : G) * (g : G), (Subgroup.mem_normalizer_iff''.mp g.2 x).mp x.2⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

private def amb_rho : Subgroup.normalizer (V₀ : Set G) →* LGL q (Additive V₀) where
  toFun g := (MulEquiv.toAdditive (amb_conjMul g)).toLinearEquiv
    (fun c v => ZMod.map_smul (MulEquiv.toAdditive (amb_conjMul g)) c v)
  map_one' := by
    ext v
    simp [amb_conjMul]
  map_mul' g h := by
    ext v
    simp [amb_conjMul, mul_assoc]

private theorem amb_rho_apply (g : Subgroup.normalizer (V₀ : Set G)) (v : Additive V₀) :
    (((amb_rho (q := q) g) v).toMul : G) = (g : G) * (v.toMul : G) * (g : G)⁻¹ := rfl

private def amb_img (S : Subgroup G) : Subgroup (LGL q (Additive V₀)) :=
  (S.subgroupOf (Subgroup.normalizer (V₀ : Set G))).map amb_rho

local notation "img" => amb_img (q := q) (V₀ := V₀)
local notation "ρ" => amb_rho (q := q) (V₀ := V₀)

private theorem amb_mem_img {S : Subgroup G} {y : LGL q (Additive V₀)} :
    y ∈ img S ↔ ∃ g : Subgroup.normalizer (V₀ : Set G), (g : G) ∈ S ∧ ρ g = y := by
  simp [amb_img, Subgroup.mem_map, Subgroup.mem_subgroupOf]

private theorem amb_mem_img_of_mem {S : Subgroup G} (g : Subgroup.normalizer (V₀ : Set G))
    (hg : (g : G) ∈ S) : ρ g ∈ img S :=
  amb_mem_img.mpr ⟨g, hg, rfl⟩

private theorem amb_img_mono {S T : Subgroup G} (h : S ≤ T) : img S ≤ img T := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := amb_mem_img.mp hy
  exact amb_mem_img_of_mem g (h hg)

private theorem amb_rho_eq_one_iff (g : Subgroup.normalizer (V₀ : Set G)) :
    ρ g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V₀ : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have h1 := congrArg
      (fun y : LGL q (Additive V₀) => ((y (Additive.ofMul ⟨x, hx⟩)).toMul : G)) h
    simp only [amb_rho_apply] at h1
    change (g : G) * x * (g : G)⁻¹ = x at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  · intro h
    ext v
    rw [amb_rho_apply]
    change _ = (v.toMul : G)
    rw [mul_inv_eq_iff_eq_mul]
    exact (h v.toMul v.toMul.2).symm

private theorem amb_mem_fixSub_img {S : Subgroup G} {v : Additive V₀} :
    v ∈ fixSub (img S) ↔ ∀ g : Subgroup.normalizer (V₀ : Set G), (g : G) ∈ S →
      (g : G) * (v.toMul : G) * (g : G)⁻¹ = (v.toMul : G) := by
  rw [mem_fixSub]
  constructor
  · intro h g hg
    have := h (ρ g) (amb_mem_img_of_mem g hg)
    exact congrArg (fun w : Additive V₀ => (w.toMul : G)) this
  · intro h y hy
    obtain ⟨g, hg, rfl⟩ := amb_mem_img.mp hy
    apply Additive.toMul.injective
    apply Subtype.ext
    exact h g hg

private theorem amb_card_fixSub_img {S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (V₀ : Set G)) :
    Nat.card (fixSub (img S)) = Nat.card ↥(V₀ ⊓ Subgroup.centralizer (S : Set G)) := by
  refine Nat.card_congr
    { toFun := fun v => ⟨(v.1.toMul : G), v.1.toMul.2, ?_⟩
      invFun := fun x => ⟨Additive.ofMul ⟨x.1, x.2.1⟩, ?_⟩
      left_inv := fun v => rfl
      right_inv := fun x => rfl }
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    intro s hs
    have := (amb_mem_fixSub_img.mp v.2) ⟨s, hS hs⟩ hs
    exact mul_inv_eq_iff_eq_mul.mp this
  · rw [amb_mem_fixSub_img]
    intro g hg
    have := (Subgroup.mem_centralizer_iff.mp x.2.2) g hg
    change (g : G) * x.1 * (g : G)⁻¹ = x.1
    rw [mul_inv_eq_iff_eq_mul]
    exact this

private theorem amb_card_img {S : Subgroup G} (hS : S ≤ Subgroup.normalizer (V₀ : Set G)) :
    Nat.card (img S) * Nat.card ↥(S ⊓ Subgroup.centralizer (V₀ : Set G)) = Nat.card S := by
  let f : S →* LGL q (Additive V₀) := MonoidHom.comp ρ (Subgroup.inclusion hS)
  have h1 : f.range = img S := by
    ext y
    rw [MonoidHom.mem_range, amb_mem_img]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s.1, hS s.2⟩, s.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g.1, hg⟩, rfl⟩
  have h2 : Nat.card f.ker = Nat.card ↥(S ⊓ Subgroup.centralizer (V₀ : Set G)) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨s.1.1, s.1.2, (amb_rho_eq_one_iff _).mp s.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, (amb_rho_eq_one_iff _).mpr x.2.2⟩
        left_inv := fun s => rfl
        right_inv := fun x => rfl }
  rw [← h1, ← h2, mul_comm]
  exact Subgroup.card_ker_mul_card_range f

private theorem amb_img_eq_bot_iff {S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (V₀ : Set G)) :
    img S = ⊥ ↔ S ≤ Subgroup.centralizer (V₀ : Set G) := by
  rw [eq_bot_iff]
  constructor
  · intro h g hg
    have := h (amb_mem_img_of_mem ⟨g, hS hg⟩ hg)
    exact (amb_rho_eq_one_iff ⟨g, hS hg⟩).mp (Subgroup.mem_bot.mp this)
  · intro h y hy
    obtain ⟨g, hg, rfl⟩ := amb_mem_img.mp hy
    rw [Subgroup.mem_bot]
    exact (amb_rho_eq_one_iff g).mpr (h hg)

private theorem amb_isElemAb_img {r : ℕ} {E : Subgroup G} (hE : IsElemAb r E) :
    IsElemAb r (img E) := by
  have hE' : IsElemAb r (E.subgroupOf (Subgroup.normalizer (V₀ : Set G))) := by
    obtain ⟨hc, hx⟩ := hE
    refine ⟨?_, ?_⟩
    · have := hc
      infer_instance
    · intro x hx'
      apply Subtype.ext
      simpa using hx (x : G) hx'
  exact hE'.map ρ

private theorem amb_img_le_normalizer {J A : Subgroup G}
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    img A ≤ Subgroup.normalizer (img J : Set (LGL q (Additive V₀))) := by
  refine CFSG.SignalizerFunctor.Helpers.normalizer_image_le ρ
    (A.subgroupOf (Subgroup.normalizer (V₀ : Set G)))
    (J.subgroupOf (Subgroup.normalizer (V₀ : Set G))) ?_
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf] at ha
  have := Subgroup.mem_normalizer_iff.mp (hAJ ha) (h : G)
  simpa [Subgroup.mem_subgroupOf] using this

private theorem amb_img_inf_centralizer {r : ℕ} (hr : r.Prime) {J A : Subgroup G}
    (hJ : J ≤ Subgroup.normalizer (V₀ : Set G)) (hA : A ≤ Subgroup.normalizer (V₀ : Set G))
    (hA' : IsPGroup r A) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hcop : Nat.Coprime r (Nat.card J)) :
    img (J ⊓ Subgroup.centralizer (A : Set G)) =
      img J ⊓ Subgroup.centralizer (img A : Set (LGL q (Additive V₀))) := by
  have key := CFSG.SignalizerFunctor.Helpers.coprime_centralizer_image r hr ρ
    (A.subgroupOf (Subgroup.normalizer (V₀ : Set G)))
    (J.subgroupOf (Subgroup.normalizer (V₀ : Set G)))
    (hA'.of_equiv (Subgroup.subgroupOfEquivOfLe hA).symm) ?_ ?_
  · have hsub : (J ⊓ Subgroup.centralizer (A : Set G)).subgroupOf
        (Subgroup.normalizer (V₀ : Set G)) =
        J.subgroupOf (Subgroup.normalizer (V₀ : Set G)) ⊓
          Subgroup.centralizer
            ((A.subgroupOf (Subgroup.normalizer (V₀ : Set G)) : Subgroup _) : Set _) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨hxJ, hxC⟩
        refine ⟨hxJ, fun a ha => ?_⟩
        exact Subtype.ext (hxC (a : G) ha)
      · rintro ⟨hxJ, hxC⟩
        refine ⟨hxJ, fun a ha => ?_⟩
        have := hxC ⟨a, hA ha⟩ ha
        exact congrArg Subtype.val this
    unfold amb_img
    rw [hsub]
    exact key
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf] at ha
    have := Subgroup.mem_normalizer_iff.mp (hAJ ha) (h : G)
    simpa [Subgroup.mem_subgroupOf] using this
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ).toEquiv] at hcop
    exact hcop

private def amb_pre (S : Subgroup (LGL q (Additive V₀))) : Subgroup G :=
  (S.comap ρ).map (Subgroup.normalizer (V₀ : Set G)).subtype

local notation "pre" => amb_pre (q := q) (V₀ := V₀)

private theorem amb_mem_pre {S : Subgroup (LGL q (Additive V₀))} {x : G} :
    x ∈ pre S ↔ ∃ h : x ∈ Subgroup.normalizer (V₀ : Set G), ρ ⟨x, h⟩ ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

private def amb_restr {S : Subgroup G} (hS : S ≤ Subgroup.normalizer (V₀ : Set G)) :
    S →* ↥(img S) :=
  (MonoidHom.subgroupMap ρ (S.subgroupOf (Subgroup.normalizer (V₀ : Set G)))).comp
    (Subgroup.subgroupOfEquivOfLe hS).symm.toMonoidHom

local notation "restr" => amb_restr (q := q) (V₀ := V₀)

private theorem amb_restr_apply {S : Subgroup G} (hS : S ≤ Subgroup.normalizer (V₀ : Set G))
    (x : S) : ((restr hS x : ↥(img S)) : LGL q (Additive V₀)) = ρ ⟨x, hS x.2⟩ := rfl

private theorem amb_restr_surjective {S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (V₀ : Set G)) : Function.Surjective (restr hS) :=
  (MonoidHom.subgroupMap_surjective ρ _).comp (MulEquiv.surjective _)

private theorem amb_card_img_dvd {S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (V₀ : Set G)) : Nat.card (img S) ∣ Nat.card S :=
  Subgroup.card_dvd_of_surjective (amb_restr_surjective hS)

private theorem amb_solvable_img {S : Subgroup G} (hS : S ≤ Subgroup.normalizer (V₀ : Set G))
    (h : Group.IsSolvable S) : Group.IsSolvable (img S) :=
  Group.isSolvable_of_surjective (amb_restr_surjective hS)

private theorem amb_isSyl_img [Finite G] {J P : Subgroup G}
    (hJ : J ≤ Subgroup.normalizer (V₀ : Set G)) (hP : IsSyl q P J) :
    IsSyl q (img P) (img J) := by
  obtain ⟨P0, hP0⟩ := hP
  refine ⟨Sylow.mapSurjective (amb_restr_surjective hJ) P0, ?_⟩
  rw [Sylow.coe_mapSurjective]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hz
    refine amb_mem_img.mpr ⟨⟨x, hJ x.2⟩, ?_, rfl⟩
    rw [← hP0]
    exact ⟨x, hx, rfl⟩
  · intro hy
    obtain ⟨g, hg, rfl⟩ := amb_mem_img.mp hy
    rw [← hP0] at hg
    obtain ⟨x, hx, hxg⟩ := hg
    refine ⟨restr hJ x, ⟨x, hx, rfl⟩, ?_⟩
    rw [Subgroup.coe_subtype, amb_restr_apply]
    congr 1
    exact Subtype.ext hxg

private theorem amb_qOne_img [Finite G] {E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (V₀ : Set G)) (hQ : QOneAmb V₀ E) : QOne (img E) := by
  intro B' hB'
  obtain ⟨B0, hB0⟩ : ∃ B0 : Subgroup G, B0 = E ⊓ pre B' := ⟨_, rfl⟩
  have hB0E : B0 ≤ E := hB0 ▸ inf_le_left
  have hB0N : B0 ≤ Subgroup.normalizer (V₀ : Set G) := hB0E.trans hE
  have himg : img B0 = B' := by
    apply le_antisymm
    · intro y hy
      obtain ⟨g, hg, rfl⟩ := amb_mem_img.mp hy
      rw [hB0] at hg
      obtain ⟨h, hh⟩ := amb_mem_pre.mp hg.2
      exact hh
    · intro y hy
      obtain ⟨g, hg, rfl⟩ := amb_mem_img.mp (hB' hy)
      refine amb_mem_img_of_mem g ?_
      rw [hB0]
      exact ⟨hg, amb_mem_pre.mpr ⟨g.2, hy⟩⟩
  have hker : B0 ⊓ Subgroup.centralizer (V₀ : Set G) =
      E ⊓ Subgroup.centralizer (V₀ : Set G) := by
    apply le_antisymm
    · exact inf_le_inf hB0E le_rfl
    · intro x hx
      refine ⟨?_, hx.2⟩
      rw [hB0]
      refine ⟨hx.1, amb_mem_pre.mpr ⟨hE hx.1, ?_⟩⟩
      have := (amb_rho_eq_one_iff (q := q) ⟨x, hE hx.1⟩).mpr hx.2
      rw [this]
      exact B'.one_mem
  have h1 := amb_card_img (q := q) hB0N
  have h2 := amb_card_img (q := q) hE
  have h3 := amb_card_fixSub_img (q := q) hB0N
  have h4 := amb_card_fixSub_img (q := q) hE
  have h5 := hQ B0 hB0E
  rw [himg, hker] at h1
  rw [himg] at h3
  have hpos : 0 < Nat.card ↥(E ⊓ Subgroup.centralizer (V₀ : Set G)) := Nat.card_pos
  rw [← h1, ← h2, ← h3, ← h4] at h5
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card B' * Nat.card (fixSub B') * Nat.card ↥(E ⊓ Subgroup.centralizer (V₀ : Set G))
      = Nat.card B' * Nat.card ↥(E ⊓ Subgroup.centralizer (V₀ : Set G)) *
        Nat.card (fixSub B') := by ring
    _ ≤ Nat.card (img E) * Nat.card ↥(E ⊓ Subgroup.centralizer (V₀ : Set G)) *
        Nat.card (fixSub (img E)) := h5
    _ = Nat.card (img E) * Nat.card (fixSub (img E)) *
        Nat.card ↥(E ⊓ Subgroup.centralizer (V₀ : Set G)) := by ring

private def amb_sub (W' : Submodule (ZMod q) (Additive V₀)) : Subgroup G :=
  (AddSubgroup.toSubgroup' W'.toAddSubgroup).map V₀.subtype

local notation "subgp" => amb_sub (q := q) (V₀ := V₀)

private theorem amb_mem_sub {W' : Submodule (ZMod q) (Additive V₀)} {x : G} :
    x ∈ subgp W' ↔ ∃ h : x ∈ V₀, Additive.ofMul (⟨x, h⟩ : V₀) ∈ W' := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

private theorem amb_sub_le (W' : Submodule (ZMod q) (Additive V₀)) : subgp W' ≤ V₀ :=
  fun _ hx => (amb_mem_sub.mp hx).1

private theorem amb_card_sub (W' : Submodule (ZMod q) (Additive V₀)) :
    Nat.card (subgp W') = Nat.card W' := by
  rw [amb_sub, Subgroup.card_map_of_injective V₀.subtype_injective]
  exact Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul (fun x => Iff.rfl))

omit [Fact q.Prime] in
private theorem amb_isElemAb_of_le {W : Subgroup G} (h : W ≤ V₀) : IsElemAb q W := by
  refine ⟨?_, fun x hx => ?_⟩
  · have : IsMulCommutative V₀ := inferInstance
    exact isMulCommutative_anti h
  · exact elemPow_eq_one_of_isElementaryAbelian x (h hx)

private theorem amb_sub_le_centralizer {A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V₀ : Set G)) {W' : Submodule (ZMod q) (Additive V₀)}
    (hW : W' ≤ fixSub (img A)) : subgp W' ≤ V₀ ⊓ Subgroup.centralizer (A : Set G) := by
  intro x hx
  obtain ⟨h, hxW⟩ := amb_mem_sub.mp hx
  refine ⟨h, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
  have := (amb_mem_fixSub_img.mp (hW hxW)) ⟨a, hA ha⟩ ha
  exact mul_inv_eq_iff_eq_mul.mp this

private theorem amb_mem_normalizer_sub {W' : Submodule (ZMod q) (Additive V₀)}
    (n : Subgroup.normalizer (V₀ : Set G)) (h1 : ∀ w ∈ W', ρ n w ∈ W')
    (h2 : ∀ w ∈ W', (ρ n)⁻¹ w ∈ W') : (n : G) ∈ Subgroup.normalizer (subgp W' : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨h, hxW⟩ := amb_mem_sub.mp hx
    have hn : (n : G) * x * (n : G)⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.mp n.2 x).mp h
    exact amb_mem_sub.mpr ⟨hn, h1 _ hxW⟩
  · intro hx
    obtain ⟨hn, hxW⟩ := amb_mem_sub.mp hx
    have h : x ∈ V₀ := (Subgroup.mem_normalizer_iff.mp n.2 x).mpr hn
    refine amb_mem_sub.mpr ⟨h, ?_⟩
    have := h2 _ hxW
    have e : ((ρ n)⁻¹ (Additive.ofMul ⟨(n : G) * x * (n : G)⁻¹, hn⟩) : Additive V₀) =
        Additive.ofMul ⟨x, h⟩ := LinearEquiv.symm_apply_apply (ρ n) (Additive.ofMul ⟨x, h⟩)
    rwa [e] at this

private theorem amb_main [Finite G] {r : ℕ} (hr : r.Prime) {J A : Subgroup G}
    (hJV : J ≤ Subgroup.normalizer (V₀ : Set G))
    (hAV : A ≤ Subgroup.normalizer (V₀ : Set G)) (hsolv : Group.IsSolvable J)
    (hnoP : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal →
      (∀ n ∈ N, ∃ k : ℕ, n ^ (q ^ k) ∈ Subgroup.centralizer (V₀ : Set G)) →
      N ≤ Subgroup.centralizer (V₀ : Set G))
    (hgen : (⨆ (E : Subgroup G) (_ : E ≤ J ∧ IsElemAb q E ∧ QOneAmb V₀ E), E) = J)
    (hne : ¬ J ≤ Subgroup.centralizer (V₀ : Set G))
    (hA : IsElemAb r A) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hcop : Nat.Coprime r (Nat.card J)) :
    (q = 2 ∨ q = 3) ∧
    (∀ P : Subgroup G, IsSyl q P J →
      J ≤ (J ⊓ Subgroup.centralizer (A : Set G)) ⊔ P ⊔
        (J ⊓ Subgroup.centralizer (V₀ : Set G))) ∧
    (q = 2 → ∃ W : Subgroup G, W ≤ V₀ ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAb 2 W ∧
      Nat.card W = 4 ∧ ∃ d ∈ J ⊓ Subgroup.centralizer (A : Set G),
        IsPGroup 3 (Subgroup.zpowers d) ∧ d ∈ Subgroup.normalizer (W : Set G) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1) ∧
    (q = 3 → ∃ W : Subgroup G, W ≤ V₀ ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAb 3 W ∧
      Nat.card W = 9 ∧ ∃ D : Subgroup G, D ≤ J ⊓ Subgroup.centralizer (A : Set G) ∧
        ∃ φ : D →* SL(2, ZMod 3), Function.Surjective φ) := by
  have hH : Hyp (img J) := by
    refine ⟨amb_solvable_img hJV hsolv, ?_⟩
    intro N1 hN1H hN1n hN1p
    obtain ⟨M, hM⟩ : ∃ M : Subgroup G, M = J ⊓ pre N1 := ⟨_, rfl⟩
    have hMJ : M ≤ J := hM ▸ inf_le_left
    have hMn : (M.subgroupOf J).Normal := by
      refine ⟨fun m hm j => ?_⟩
      rw [Subgroup.mem_subgroupOf, hM] at hm ⊢
      obtain ⟨hmJ, hmP⟩ := hm
      obtain ⟨hmN, hmρ⟩ := amb_mem_pre.mp hmP
      have hjmJ : ((j * m * j⁻¹ : J) : G) ∈ J := (j * m * j⁻¹ : J).2
      refine ⟨hjmJ, amb_mem_pre.mpr ⟨hJV hjmJ, ?_⟩⟩
      have hj : ρ ⟨(j : G), hJV j.2⟩ ∈ img J := amb_mem_img_of_mem _ j.2
      have hmm : ρ ⟨(m : G), hmN⟩ ∈ img J := amb_mem_img_of_mem _ hmJ
      have := hN1n.conj_mem ⟨ρ ⟨(m : G), hmN⟩, hmm⟩ hmρ ⟨ρ ⟨(j : G), hJV j.2⟩, hj⟩
      have e : ρ ⟨((j * m * j⁻¹ : J) : G), hJV hjmJ⟩ =
          ρ ⟨(j : G), hJV j.2⟩ * ρ ⟨(m : G), hmN⟩ * (ρ ⟨(j : G), hJV j.2⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact this
    have hMp : ∀ m ∈ M, ∃ k : ℕ, m ^ (q ^ k) ∈ Subgroup.centralizer (V₀ : Set G) := by
      intro m hm
      rw [hM] at hm
      obtain ⟨hmJ, hmP⟩ := hm
      obtain ⟨hmN, hmρ⟩ := amb_mem_pre.mp hmP
      obtain ⟨k, hk⟩ := hN1p ⟨ρ ⟨(m : G), hmN⟩, hmρ⟩
      refine ⟨k, ?_⟩
      have h0 : ρ (⟨(m : G), hmN⟩ ^ (q ^ k)) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk
      exact (amb_rho_eq_one_iff _).mp h0
    have hMK : M ≤ Subgroup.centralizer (V₀ : Set G) := hnoP M hMJ hMn hMp
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨g, hgJ, rfl⟩ := amb_mem_img.mp (hN1H hy)
    have hgM : (g : G) ∈ M := hM ▸ ⟨hgJ, amb_mem_pre.mpr ⟨g.2, hy⟩⟩
    exact Subgroup.mem_bot.mpr ((amb_rho_eq_one_iff g).mpr (hMK hgM))
  have hS3 : (⨆ (B : Subgroup (LGL q (Additive V₀))) (_ : IsAV (img J) B), B) = img J := by
    apply le_antisymm (iSup₂_le fun B hB => hB.1)
    intro y hy
    obtain ⟨g, hgJ, rfl⟩ := amb_mem_img.mp hy
    have hJle : J ≤ pre (⨆ (B : Subgroup (LGL q (Additive V₀))) (_ : IsAV (img J) B), B) := by
      refine hgen.symm.le.trans (iSup₂_le fun E hE => ?_)
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (V₀ : Set G) := hJV (hE.1 hx)
      refine amb_mem_pre.mpr ⟨hxN, ?_⟩
      have hAV : IsAV (img J) (img E) :=
        ⟨amb_img_mono hE.1, amb_isElemAb_img hE.2.1, amb_qOne_img (hE.1.trans hJV) hE.2.2⟩
      have hle : img E ≤ ⨆ (B : Subgroup (LGL q (Additive V₀))) (_ : IsAV (img J) B), B :=
        le_iSup₂ (f := fun B (_ : IsAV (img J) B) => B) (img E) hAV
      exact hle (amb_mem_img_of_mem ⟨x, hxN⟩ hx)
    obtain ⟨h, hh⟩ := amb_mem_pre.mp (hJle hgJ)
    exact hh
  have hne' : img J ≠ ⊥ := fun h => hne ((amb_img_eq_bot_iff hJV).mp h)
  have hXr : IsElemAb r (img A) := amb_isElemAb_img hA
  have hXH : img A ≤ Subgroup.normalizer (img J : Set (LGL q (Additive V₀))) :=
    amb_img_le_normalizer hAJ
  have hcop' : Nat.Coprime r (Nat.card (img J)) :=
    hcop.coprime_dvd_right (amb_card_img_dvd hJV)
  obtain ⟨h1, h2, h3, h4⟩ := core (p := q) (V := Additive V₀) hH hS3 hne' hr hXr hXH hcop'
  have hAp : IsPGroup r A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g g.2)⟩
  have hC : img (J ⊓ Subgroup.centralizer (A : Set G)) =
      img J ⊓ Subgroup.centralizer (img A : Set (LGL q (Additive V₀))) :=
    amb_img_inf_centralizer hr hJV hAV hAp hAJ hcop
  refine ⟨h1, ?_, ?_, ?_⟩
  · intro P hP
    have hPJ : P ≤ J := by
      obtain ⟨P0, rfl⟩ := hP
      exact Subgroup.map_subtype_le _
    have key := h2 (img P) (amb_isSyl_img hJV hP)
    rw [← hC] at key
    intro j hj
    have hρ : ρ ⟨j, hJV hj⟩ ∈ img J := amb_mem_img_of_mem _ hj
    have hmem := key hρ
    have hle : img (J ⊓ Subgroup.centralizer (A : Set G)) ⊔ img P ≤
        img ((J ⊓ Subgroup.centralizer (A : Set G)) ⊔ P) :=
      sup_le (amb_img_mono le_sup_left) (amb_img_mono le_sup_right)
    obtain ⟨y, hy, hyρ⟩ := amb_mem_img.mp (hle hmem)
    have hyJ : (y : G) ∈ J := (sup_le inf_le_left hPJ) hy
    have hk : (y : G)⁻¹ * j ∈ J ⊓ Subgroup.centralizer (V₀ : Set G) := by
      refine ⟨J.mul_mem (J.inv_mem hyJ) hj, ?_⟩
      have : ρ (y⁻¹ * ⟨j, hJV hj⟩) = 1 := by
        rw [map_mul, map_inv, hyρ, inv_mul_cancel]
      exact (amb_rho_eq_one_iff (y⁻¹ * ⟨j, hJV hj⟩)).mp this
    rw [← mul_inv_cancel_left (y : G) j]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hk)
  · intro hq2
    obtain ⟨W', hW'fix, hW'card, d', hd'mem, hd'3, hd'W, hd'fix⟩ := h3 hq2
    have hd'C : d' ∈ img (J ⊓ Subgroup.centralizer (A : Set G)) := by
      rw [hC]
      exact hd'mem
    obtain ⟨g, hg, hgd⟩ := amb_mem_img.mp hd'C
    obtain ⟨a, m, hm3, hord⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (g : G)).ne' 3 (by norm_num)
    have hmpos : m ≠ 0 := by
      rintro rfl
      have := orderOf_pos (g : G)
      rw [hord] at this
      simp at this
    have hdvd : m ∣ orderOf (g : G) := Dvd.intro_left _ hord.symm
    have hρd : ρ (g ^ m) = d' ^ m := by rw [map_pow, hgd]
    refine ⟨subgp W', amb_sub_le_centralizer hAV hW'fix, ?_, ?_, (g : G) ^ m, ?_, ?_, ?_, ?_⟩
    · rw [← hq2]
      exact amb_isElemAb_of_le (amb_sub_le W')
    · rw [amb_card_sub, hW'card, hq2]
      norm_num
    · exact Subgroup.pow_mem _ hg m
    · refine IsPGroup.of_card (n := a) ?_
      rw [Nat.card_zpowers, orderOf_pow_of_dvd hmpos hdvd, hord]
      exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hmpos)
    · have hinv : d'⁻¹ = d' ^ 2 := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← pow_succ']
        exact hd'3
      refine amb_mem_normalizer_sub (g ^ m) ?_ ?_
      · intro w hw
        rw [hρd]
        exact amb_pow_apply_mem hd'W m w hw
      · intro w hw
        rw [hρd, ← inv_pow, hinv, ← pow_mul]
        exact amb_pow_apply_mem hd'W (2 * m) w hw
    · intro w hw hdw
      obtain ⟨hwV, hwW⟩ := amb_mem_sub.mp hw
      have hfix : (d' ^ m) (Additive.ofMul ⟨w, hwV⟩) = Additive.ofMul ⟨w, hwV⟩ := by
        rw [← hρd]
        apply Additive.toMul.injective
        apply Subtype.ext
        exact hdw
      have hu0 := amb_pow_fixed hd'3 hm3 hd'fix hwW hfix
      exact congrArg (fun v : Additive V₀ => (v.toMul : G)) hu0
  · intro hq3
    obtain ⟨W', hW'fix, hW'card, D', hD'le, φ', hφ'⟩ := h4 hq3
    have hex : ∃ D : Subgroup G, D ≤ J ⊓ Subgroup.centralizer (A : Set G) ∧
        ∃ φ : D →* SL(2, ZMod q), Function.Surjective φ := by
      obtain ⟨D, hD⟩ : ∃ D : Subgroup G,
          D = (J ⊓ Subgroup.centralizer (A : Set G)) ⊓ pre D' := ⟨_, rfl⟩
      have hmemD : ∀ x : G, x ∈ D ↔
          x ∈ J ⊓ Subgroup.centralizer (A : Set G) ∧ x ∈ pre D' := by
        intro x
        rw [hD]
        exact Iff.rfl
      have hDle : D ≤ J ⊓ Subgroup.centralizer (A : Set G) :=
        fun x hx => ((hmemD x).mp hx).1
      have hDN : D ≤ Subgroup.normalizer (V₀ : Set G) := hDle.trans (inf_le_left.trans hJV)
      have hψ : ∀ x : D, ρ (Subgroup.inclusion hDN x) ∈ D' := by
        intro x
        obtain ⟨h, hh⟩ := amb_mem_pre.mp ((hmemD x).mp x.2).2
        exact hh
      let ψ : D →* D' :=
        MonoidHom.codRestrict (MonoidHom.comp ρ (Subgroup.inclusion hDN)) D' hψ
      refine ⟨D, hDle, φ'.comp ψ, ?_⟩
      intro s
      obtain ⟨d', hd'⟩ := hφ' s
      have hd'C : (d' : LGL q (Additive V₀)) ∈
          img (J ⊓ Subgroup.centralizer (A : Set G)) := by
        rw [hC]
        exact hD'le d'.2
      obtain ⟨g, hg, hgd⟩ := amb_mem_img.mp hd'C
      have hρg : ρ g ∈ D' := by
        rw [hgd]
        exact d'.2
      have hgD : (g : G) ∈ D := (hmemD g).mpr ⟨hg, amb_mem_pre.mpr ⟨g.2, hρg⟩⟩
      refine ⟨⟨g, hgD⟩, ?_⟩
      have : ψ ⟨g, hgD⟩ = d' := Subtype.ext hgd
      change φ' (ψ ⟨g, hgD⟩) = s
      rw [this]
      exact hd'
    refine ⟨subgp W', amb_sub_le_centralizer hAV hW'fix, ?_, ?_, ?_⟩
    · rw [← hq3]
      exact amb_isElemAb_of_le (amb_sub_le W')
    · rw [amb_card_sub, hW'card, hq3]
      norm_num
    · rw [hq3] at hex
      exact hex

end Amb

omit [Finite G] in
private theorem amb_isElementaryAbelian {q : ℕ} {V₀ : Subgroup G} (h : IsElemAb q V₀) :
    IsElementaryAbelian q V₀ :=
  { toIsMulCommutative := h.1
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      fun x => Subtype.ext (by simpa using h.2 x x.2) }

theorem core_ambient {q r : ℕ} (hq : q.Prime) (hr : r.Prime) {V₀ J A : Subgroup G}
    (hV₀ : IsElemAb q V₀) (hJV : J ≤ Subgroup.normalizer (V₀ : Set G))
    (hAV : A ≤ Subgroup.normalizer (V₀ : Set G)) (hsolv : Group.IsSolvable J)
    (hnoP : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal →
      (∀ n ∈ N, ∃ k : ℕ, n ^ (q ^ k) ∈ Subgroup.centralizer (V₀ : Set G)) →
      N ≤ Subgroup.centralizer (V₀ : Set G))
    (hgen : (⨆ (E : Subgroup G) (_ : E ≤ J ∧ IsElemAb q E ∧ QOneAmb V₀ E), E) = J)
    (hne : ¬ J ≤ Subgroup.centralizer (V₀ : Set G))
    (hA : IsElemAb r A) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hcop : Nat.Coprime r (Nat.card J)) :
    (q = 2 ∨ q = 3) ∧
    (∀ P : Subgroup G, IsSyl q P J →
      J ≤ (J ⊓ Subgroup.centralizer (A : Set G)) ⊔ P ⊔
        (J ⊓ Subgroup.centralizer (V₀ : Set G))) ∧
    (q = 2 → ∃ W : Subgroup G, W ≤ V₀ ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAb 2 W ∧
      Nat.card W = 4 ∧ ∃ d ∈ J ⊓ Subgroup.centralizer (A : Set G),
        IsPGroup 3 (Subgroup.zpowers d) ∧ d ∈ Subgroup.normalizer (W : Set G) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1) ∧
    (q = 3 → ∃ W : Subgroup G, W ≤ V₀ ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAb 3 W ∧
      Nat.card W = 9 ∧ ∃ D : Subgroup G, D ≤ J ⊓ Subgroup.centralizer (A : Set G) ∧
        ∃ φ : D →* SL(2, ZMod 3), Function.Surjective φ) := by
  have : Fact q.Prime := ⟨hq⟩
  have : IsElementaryAbelian q V₀ := amb_isElementaryAbelian hV₀
  exact amb_main hr hJV hAV hsolv hnoP hgen hne hA hAJ hcop

end CFSG.SignalizerFunctorTheorem.Quadratic
