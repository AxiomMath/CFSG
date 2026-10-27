module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFinRed
public import CFSG.RankThree.PartOne.S11d.OddAlt

public section

namespace CFSG.StandardType.SpFin

open Module CFSG.StandardType.TwoThree CFSG.Assembly TableB

theorem add_self_eq_zero_mod (K : Type) [Field K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] (v : V) : v + v = 0 := by
  rw [← two_smul K v, show (2 : K) = 0 from CharP.cast_eq_zero K 2, zero_smul]

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_card_eq_pow_three {G : Type*} [Group G] [Finite G] {Y : Subgroup G}
    (hY : ∀ y ∈ Y, y ^ 3 = 1) : ∃ j : ℕ, Nat.card Y = 3 ^ j := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 Y := fun y => ⟨1, Subtype.ext (by simpa using hY y y.2)⟩
  exact IsPGroup.iff_card.mp hP

theorem card_sq_le_sub (hK : Nat.card K = 2) (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hr : B.IsRefl) (X : Subgroup (Module.End K V)ˣ) (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hexp : ∀ x ∈ X, x ^ 3 = 1)
    (hinv : ∀ x ∈ X, ∀ v w, B ((x : Module.End K V) v) ((x : Module.End K V) w) = B v w)
    {W : Submodule K V} (hWX : ∀ x ∈ X, ∀ w ∈ W, (x : Module.End K V) w ∈ W)
    (hWc : W ⊔ B.orthogonal W = ⊤) {T : Submodule K V} (hTW : T ≤ W)
    (hTiso : ∀ u ∈ T, ∀ v ∈ T, B u v = 0) (hTX : ∀ x ∈ X, ∀ t ∈ T, (x : Module.End K V) t ∈ T) :
    Nat.card X ^ 2 ≤ 3 ^ (finrank K W - finrank K T) *
      Nat.card (X ⊓ fixG W : Subgroup (Module.End K V)ˣ) ^ 2 := by
  classical
  have := finite_units_end (K := K) (V := V)
  set S := W ⊓ B.orthogonal T with hS
  have hSX : ∀ x ∈ X, ∀ s ∈ S, (x : Module.End K V) s ∈ S := by
    intro x hx s hs
    refine ⟨hWX x hx s hs.1, ?_⟩
    intro t ht
    have h1 : ((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) t ∈ T :=
      hTX x⁻¹ (X.inv_mem hx) t ht
    have h2 := hinv x hx (((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) t) s
    have h3 : (x : Module.End K V) (((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) t) = t := by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
    rw [h3] at h2
    rw [h2]
    exact hs.2 _ h1
  have hcardle := card_sq_le hK (finrank K S) S rfl X hcomm hexp hSX
  have hfix : X ⊓ fixG S ≤ X ⊓ fixG W := by
    rintro g ⟨hgX, hgS⟩
    refine ⟨hgX, fun w hw => ?_⟩
    have hg3 : (g : Module.End K V) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hexp g hgX, Units.val_one]
    have hguS : ∀ s ∈ S, (g : Module.End K V) s = s := fun s hs => hgS s hs
    set u : V := (g : Module.End K V) w - w with hu
    have huW : u ∈ W := W.sub_mem (hWX g hgX w hw) hw
    have huS : ∀ s ∈ S, B s u = 0 := by
      intro s hs
      have h1 := hinv g hgX w s
      rw [hguS s hs] at h1
      refine hr.eq_zero ?_
      rw [hu, map_sub, LinearMap.sub_apply, h1, sub_self]
    have huT : u ∈ T := by
      rw [← B.orthogonal_orthogonal hB hr T, LinearMap.BilinForm.mem_orthogonal_iff]
      intro v hv
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
      obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ :=
        Submodule.mem_sup.mp (hWc ▸ Submodule.mem_top : v ∈ W ⊔ B.orthogonal W)
      have h1 : B w₁ u = 0 := hr.eq_zero (hw₁ u huW)
      have h2 : w₀ ∈ B.orthogonal T := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro t ht
        have h3 := hv t ht
        rw [map_add, LinearMap.BilinForm.mem_orthogonal_iff.mp hw₁ t (hTW ht), add_zero] at h3
        exact h3
      rw [map_add, LinearMap.add_apply, huS w₀ ⟨hw₀, h2⟩, h1, add_zero]
    have huS' : u ∈ S := ⟨hTW huT, fun t ht => hTiso t ht u huT⟩
    have h4 : (g : Module.End K V) u = u := hguS u huS'
    rw [hu, map_sub] at h4
    have h5 : (g : Module.End K V) ((g : Module.End K V) w) = w := by
      have hv2 := add_self_eq_zero_mod K (V := V)
      calc (g : Module.End K V) ((g : Module.End K V) w)
          = ((g : Module.End K V) ((g : Module.End K V) w) - (g : Module.End K V) w) +
            (g : Module.End K V) w := by abel
        _ = ((g : Module.End K V) w - w) + (g : Module.End K V) w := by rw [h4]
        _ = ((g : Module.End K V) w + (g : Module.End K V) w) - w := by abel
        _ = 0 - w := by rw [hv2]
        _ = w := by rw [zero_sub]; exact neg_eq_of_add_eq_zero_right (hv2 w)
    have h6 : (g : Module.End K V) w = w := by
      have h7 : ((g : Module.End K V) ^ 3) w = w := by rw [hg3, Module.End.one_apply]
      have h8 : ((g : Module.End K V) ^ 3) w = (g : Module.End K V) w := by
        rw [pow_succ, Module.End.mul_apply, pow_two, Module.End.mul_apply, h5]
      rw [← h8, h7]
    exact h6
  have hcard : Nat.card (X ⊓ fixG S : Subgroup (Module.End K V)ˣ) ≤
      Nat.card (X ⊓ fixG W : Subgroup (Module.End K V)ˣ) :=
    Subgroup.card_le_of_le hfix
  have hsup : W ⊔ B.orthogonal T = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ :=
      Submodule.mem_sup.mp (hWc ▸ Submodule.mem_top : v ∈ W ⊔ B.orthogonal W)
    refine Submodule.add_mem_sup hw₀ ?_
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro t ht
    exact LinearMap.BilinForm.mem_orthogonal_iff.mp hw₁ t (hTW ht)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (B.orthogonal T)
  rw [hsup, finrank_top, LinearMap.BilinForm.finrank_orthogonal hB T, ← hS] at h1
  have hTV : finrank K T ≤ finrank K V := Submodule.finrank_le T
  have hTW' : finrank K T ≤ finrank K W := Submodule.finrank_mono hTW
  have hdim : finrank K S ≤ finrank K W - finrank K T := by omega
  calc Nat.card X ^ 2 ≤ 3 ^ finrank K S *
        Nat.card (X ⊓ fixG S : Subgroup (Module.End K V)ˣ) ^ 2 := hcardle
    _ ≤ 3 ^ (finrank K W - finrank K T) *
        Nat.card (X ⊓ fixG W : Subgroup (Module.End K V)ˣ) ^ 2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hdim) (Nat.pow_le_pow_left hcard 2)

section Decomp

open CFSG.RankThree.PartOne.OddIso

theorem sub_one_apply_comm {x y : Module.End K V} (h : x * y = y * x) (v : V) :
    (x - 1) (y v) = y ((x - 1) v) := by
  have h' : x (y v) = y (x v) := by rw [← Module.End.mul_apply, h, Module.End.mul_apply]
  simp [LinearMap.sub_apply, h']

theorem isCompl_fix_rng {x₀ : (Module.End K V)ˣ} (hx3 : x₀ ^ 3 = 1) :
    IsCompl (LinearMap.ker ((x₀ : Module.End K V) - 1))
      (LinearMap.range ((x₀ : Module.End K V) - 1)) :=
  isCompl_ker_range (p := 3) ⟨1, by norm_num⟩
    (by rw [← Units.val_pow_eq_pow_val, hx3, Units.val_one])

theorem fix_rng_orth (B : LinearMap.BilinForm K V) {x₀ : (Module.End K V)ˣ}
    (hinv : ∀ v w, B ((x₀ : Module.End K V) v) ((x₀ : Module.End K V) w) = B v w) {v w : V}
    (hv : v ∈ LinearMap.ker ((x₀ : Module.End K V) - 1))
    (hw : w ∈ LinearMap.range ((x₀ : Module.End K V) - 1)) : B v w = 0 := by
  obtain ⟨u, rfl⟩ := hw
  exact B_fix_range B hinv (sub_eq_zero.mp (LinearMap.mem_ker.mp hv)) u

theorem rng_fix_orth (B : LinearMap.BilinForm K V) {x₀ : (Module.End K V)ˣ}
    (hinv : ∀ v w, B ((x₀ : Module.End K V) v) ((x₀ : Module.End K V) w) = B v w) {v w : V}
    (hv : v ∈ LinearMap.ker ((x₀ : Module.End K V) - 1))
    (hw : w ∈ LinearMap.range ((x₀ : Module.End K V) - 1)) : B w v = 0 := by
  obtain ⟨u, rfl⟩ := hw
  exact B_range_fix B hinv (sub_eq_zero.mp (LinearMap.mem_ker.mp hv)) u

theorem fix_sup_orth (B : LinearMap.BilinForm K V) {x₀ : (Module.End K V)ˣ} (hx3 : x₀ ^ 3 = 1)
    (hinv : ∀ v w, B ((x₀ : Module.End K V) v) ((x₀ : Module.End K V) w) = B v w) :
    LinearMap.ker ((x₀ : Module.End K V) - 1) ⊔
      B.orthogonal (LinearMap.ker ((x₀ : Module.End K V) - 1)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← (isCompl_fix_rng hx3).sup_eq_top]
  refine sup_le_sup_left ?_ _
  intro w hw
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro v hv
  exact fix_rng_orth B hinv hv hw

theorem rng_sup_orth (B : LinearMap.BilinForm K V) {x₀ : (Module.End K V)ˣ} (hx3 : x₀ ^ 3 = 1)
    (hinv : ∀ v w, B ((x₀ : Module.End K V) v) ((x₀ : Module.End K V) w) = B v w) :
    LinearMap.range ((x₀ : Module.End K V) - 1) ⊔
      B.orthogonal (LinearMap.range ((x₀ : Module.End K V) - 1)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← (isCompl_fix_rng hx3).sup_eq_top, sup_comm]
  refine sup_le_sup_left ?_ _
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  exact rng_fix_orth B hinv hv hw

theorem fix_invariant {x₀ g : (Module.End K V)ˣ} (h : x₀ * g = g * x₀) {v : V}
    (hv : v ∈ LinearMap.ker ((x₀ : Module.End K V) - 1)) :
    (g : Module.End K V) v ∈ LinearMap.ker ((x₀ : Module.End K V) - 1) := by
  have h' : (x₀ : Module.End K V) * g = g * x₀ := by rw [← Units.val_mul, ← Units.val_mul, h]
  rw [LinearMap.mem_ker, sub_one_apply_comm h' v, LinearMap.mem_ker.mp hv, map_zero]

theorem rng_invariant' {x₀ g : (Module.End K V)ˣ} (h : x₀ * g = g * x₀) {v : V}
    (hv : v ∈ LinearMap.range ((x₀ : Module.End K V) - 1)) :
    (g : Module.End K V) v ∈ LinearMap.range ((x₀ : Module.End K V) - 1) := by
  have h' : (x₀ : Module.End K V) * g = g * x₀ := by rw [← Units.val_mul, ← Units.val_mul, h]
  obtain ⟨u, rfl⟩ := hv
  exact ⟨(g : Module.End K V) u, by rw [sub_one_apply_comm h']⟩

theorem rng_ne_bot {x₀ : (Module.End K V)ˣ} (hx₁ : x₀ ≠ 1) :
    LinearMap.range ((x₀ : Module.End K V) - 1) ≠ ⊥ := by
  intro h
  apply hx₁
  apply Units.ext
  apply LinearMap.ext
  intro v
  have : ((x₀ : Module.End K V) - 1) v ∈ LinearMap.range ((x₀ : Module.End K V) - 1) :=
    LinearMap.mem_range_self _ v
  rw [h, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
  rw [this, Units.val_one, Module.End.one_apply]

theorem even_finrank_rng (hK : Nat.card K = 2) {x₀ : (Module.End K V)ˣ} (hx3 : x₀ ^ 3 = 1) :
    Even (finrank K (LinearMap.range ((x₀ : Module.End K V) - 1))) :=
  even_finrank_of_fpf hK (by rw [← Units.val_pow_eq_pow_val, hx3, Units.val_one])
    (fun u hu => range_invariant _ hu)
    (fun u hu h => eq_zero_of_fixed_range (p := 3) ⟨1, by norm_num⟩
      (by rw [← Units.val_pow_eq_pow_val, hx3, Units.val_one]) hu h)

theorem splitTI {x₀ : (Module.End K V)ˣ}
    (hx3' : x₀ ^ 3 = 1) {T : Submodule K V} (hT : ∀ t ∈ T, (x₀ : Module.End K V) t ∈ T)
    (hT0 : T ≠ ⊥) :
    T ⊓ LinearMap.ker ((x₀ : Module.End K V) - 1) ≠ ⊥ ∨
      T ⊓ LinearMap.range ((x₀ : Module.End K V) - 1) ≠ ⊥ := by
  by_contra hcon
  simp only [not_or, ne_eq, not_not] at hcon
  obtain ⟨t, htT, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
  have hx3v : (x₀ : Module.End K V) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx3', Units.val_one]
  set a := (x₀ : Module.End K V) t with ha
  set b := (x₀ : Module.End K V) a with hb
  have haT : a ∈ T := hT t htT
  have hbT : b ∈ T := hT a haT
  have hxb : (x₀ : Module.End K V) b = t := by
    have h7 : ((x₀ : Module.End K V) ^ 3) t = t := by rw [hx3v, Module.End.one_apply]
    rw [← h7, pow_succ, Module.End.mul_apply, pow_two, Module.End.mul_apply]
  have hv1T : t + a + b ∈ T := T.add_mem (T.add_mem htT haT) hbT
  have hv1K : t + a + b ∈ LinearMap.ker ((x₀ : Module.End K V) - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_add, map_add, hxb,
      ← ha, ← hb]
    rw [sub_eq_zero]
    abel
  have hv1 : t + a + b = 0 := by
    have := hcon.1
    have hmem : t + a + b ∈ T ⊓ LinearMap.ker ((x₀ : Module.End K V) - 1) := ⟨hv1T, hv1K⟩
    rw [this, Submodule.mem_bot] at hmem
    exact hmem
  have h2 := add_self_eq_zero_mod K (V := V)
  have htr : t ∈ LinearMap.range ((x₀ : Module.End K V) - 1) := by
    refine ⟨a, ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply, ← hb, sub_eq_add_neg,
      neg_eq_of_add_eq_zero_right (h2 a)]
    have h3 : t = -(a + b) := eq_neg_of_add_eq_zero_left (by rw [← hv1]; abel)
    rw [h3, neg_eq_of_add_eq_zero_right (h2 (a + b))]
    exact add_comm b a
  have hmem2 : t ∈ T ⊓ LinearMap.range ((x₀ : Module.End K V) - 1) := ⟨htT, htr⟩
  rw [hcon.2, Submodule.mem_bot] at hmem2
  exact ht0 hmem2

end Decomp

section Numerics

structure IsoSetup (B : LinearMap.BilinForm K V) (X : Subgroup (Module.End K V)ˣ) : Prop where
  comm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x
  exp : ∀ x ∈ X, x ^ 3 = 1
  inv : ∀ x ∈ X, ∀ v w, B ((x : Module.End K V) v) ((x : Module.End K V) w) = B v w

theorem lemI (hK : Nat.card K = 2) {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    (hr : B.IsRefl) {X : Subgroup (Module.End K V)ˣ} (hX : IsoSetup B X)
    {x₀ : (Module.End K V)ˣ} (hx₀ : x₀ ∈ X) (hx₁ : x₀ ≠ 1) {n : ℕ} (hn : 3 ≤ n)
    (hdim : finrank K V = 2 * n) (hcard : 3 ^ (n - 1) ≤ Nat.card X) {T : Submodule K V}
    (hT0 : T ≠ ⊥) (hTiso : ∀ u ∈ T, ∀ v ∈ T, B u v = 0)
    (hTX : ∀ x ∈ X, ∀ t ∈ T, (x : Module.End K V) t ∈ T) :
    (∃ g ∈ X, g ∉ Subgroup.zpowers x₀ ∧ g ∈ fixG (LinearMap.ker ((x₀ : Module.End K V) - 1))) ∨
      (finrank K (LinearMap.range ((x₀ : Module.End K V) - 1)) ≤ 4 ∧
        3 ^ (n - 2) ≤ Nat.card (X ⊓ fixG (LinearMap.range ((x₀ : Module.End K V) - 1)) :
          Subgroup (Module.End K V)ˣ)) := by
  classical
  have := finite_units_end (K := K) (V := V)
  set Vp := LinearMap.ker ((x₀ : Module.End K V) - 1) with hVp
  set Vm := LinearMap.range ((x₀ : Module.End K V) - 1) with hVm
  have hx3 : x₀ ^ 3 = 1 := hX.exp x₀ hx₀
  have hcompl : IsCompl Vp Vm := isCompl_fix_rng hx3
  have hsum : finrank K Vp + finrank K Vm = 2 * n :=
    hdim ▸ Submodule.finrank_add_eq_of_isCompl hcompl
  have hVpX : ∀ x ∈ X, ∀ v ∈ Vp, (x : Module.End K V) v ∈ Vp :=
    fun x hx v hv => fix_invariant (hX.comm x₀ hx₀ x hx) hv
  have hVmX : ∀ x ∈ X, ∀ v ∈ Vm, (x : Module.End K V) v ∈ Vm :=
    fun x hx v hv => rng_invariant' (hX.comm x₀ hx₀ x hx) hv
  have hx0inv := hX.inv x₀ hx₀
  by_cases hC1 : ∃ g ∈ X, g ∉ Subgroup.zpowers x₀ ∧ g ∈ fixG Vp
  · exact Or.inl hC1
  right
  have hC1' : ∀ g ∈ X, g ∈ fixG Vp → g ∈ Subgroup.zpowers x₀ := fun g hg hgf =>
    by_contra fun hn' => hC1 ⟨g, hg, hn', hgf⟩
  have hXp : Nat.card (X ⊓ fixG Vp : Subgroup (Module.End K V)ˣ) ≤ 3 := by
    have hle : (X ⊓ fixG Vp : Subgroup (Module.End K V)ˣ) ≤ Subgroup.zpowers x₀ :=
      fun g hg => hC1' g hg.1 hg.2
    calc Nat.card (X ⊓ fixG Vp : Subgroup (Module.End K V)ˣ)
        ≤ Nat.card (Subgroup.zpowers x₀) := Subgroup.card_le_of_le hle
      _ = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx₁]
  have h1 := card_sq_le hK (finrank K Vp) Vp rfl X hX.comm hX.exp hVpX
  have hd1 : 2 * n - 4 ≤ finrank K Vp := by
    have h2 : 3 ^ ((n - 1) * 2) ≤ 3 ^ (finrank K Vp + 2) := calc
      3 ^ ((n - 1) * 2) = (3 ^ (n - 1)) ^ 2 := pow_mul 3 (n - 1) 2
      _ ≤ Nat.card X ^ 2 := Nat.pow_le_pow_left hcard 2
      _ ≤ 3 ^ finrank K Vp * Nat.card (X ⊓ fixG Vp : Subgroup (Module.End K V)ˣ) ^ 2 := h1
      _ ≤ 3 ^ finrank K Vp * 3 ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hXp 2)
      _ = 3 ^ (finrank K Vp + 2) := by rw [pow_add]
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h2
    omega
  have hdm4 : finrank K Vm ≤ 4 := by omega
  refine ⟨hdm4, ?_⟩
  have hXmexp : ∀ y ∈ (X ⊓ fixG Vm : Subgroup (Module.End K V)ˣ), y ^ 3 = 1 :=
    fun y hy => hX.exp y hy.1
  obtain ⟨j, hj⟩ := exists_card_eq_pow_three hXmexp
  have h3 := card_sq_le hK (finrank K Vm) Vm rfl X hX.comm hX.exp hVmX
  have hdmeven : Even (finrank K Vm) := even_finrank_rng hK hx3
  have hdm1 : 1 ≤ finrank K Vm := Submodule.one_le_finrank_iff.mpr (rng_ne_bot hx₁)
  have hcard2 : 3 ^ ((n - 1) * 2) ≤ Nat.card X ^ 2 := by
    rw [pow_mul 3 (n - 1) 2]
    exact Nat.pow_le_pow_left hcard 2
  suffices hj' : n - 2 ≤ j by
    rw [hj]
    exact Nat.pow_le_pow_right (by norm_num) hj'
  obtain ⟨c, hc⟩ := hdmeven
  have hdmcases : finrank K Vm = 2 ∨ finrank K Vm = 4 := by omega
  rcases hdmcases with hdm2 | hdm4'
  ·
    have h4 : 3 ^ ((n - 1) * 2) ≤ 3 ^ (2 + j * 2) := calc
      3 ^ ((n - 1) * 2) ≤ Nat.card X ^ 2 := hcard2
      _ ≤ 3 ^ finrank K Vm * Nat.card (X ⊓ fixG Vm : Subgroup (Module.End K V)ˣ) ^ 2 := h3
      _ = 3 ^ (2 + j * 2) := by rw [hdm2, hj, ← pow_mul, pow_add]
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h4
    omega
  ·
    have hdp : finrank K Vp = 2 * n - 4 := by omega
    set Tp := T ⊓ Vp with hTp
    set Tm := T ⊓ Vm with hTm
    have hTpX : ∀ x ∈ X, ∀ t ∈ Tp, (x : Module.End K V) t ∈ Tp :=
      fun x hx t ht => ⟨hTX x hx t ht.1, hVpX x hx t ht.2⟩
    have hTmX : ∀ x ∈ X, ∀ t ∈ Tm, (x : Module.End K V) t ∈ Tm :=
      fun x hx t ht => ⟨hTX x hx t ht.1, hVmX x hx t ht.2⟩
    have hTpiso : ∀ u ∈ Tp, ∀ v ∈ Tp, B u v = 0 := fun u hu v hv => hTiso u hu.1 v hv.1
    have hTmiso : ∀ u ∈ Tm, ∀ v ∈ Tm, B u v = 0 := fun u hu v hv => hTiso u hu.1 v hv.1
    have hsplit := splitTI hx3 (fun t ht => hTX x₀ hx₀ t ht) hT0
    by_cases hTp0 : Tp = ⊥
    · have hTm0 : Tm ≠ ⊥ := by
        rcases hsplit with h | h
        · exact absurd hTp0 h
        · exact h
      have h5 := card_sq_le_sub hK B hB hr X hX.comm hX.exp hX.inv hVmX
        (rng_sup_orth B hx3 hx0inv) (T := Tm) inf_le_right hTmiso hTmX
      have hTm1 : 1 ≤ finrank K Tm := Submodule.one_le_finrank_iff.mpr hTm0
      have h6 : 3 ^ ((n - 1) * 2) ≤ 3 ^ (3 + j * 2) := calc
        3 ^ ((n - 1) * 2) ≤ Nat.card X ^ 2 := hcard2
        _ ≤ 3 ^ (finrank K Vm - finrank K Tm) *
            Nat.card (X ⊓ fixG Vm : Subgroup (Module.End K V)ˣ) ^ 2 := h5
        _ ≤ 3 ^ 3 * Nat.card (X ⊓ fixG Vm : Subgroup (Module.End K V)ˣ) ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = 3 ^ (3 + j * 2) := by rw [hj, ← pow_mul, pow_add]
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h6
      omega
    · exfalso
      have h5 := card_sq_le_sub hK B hB hr X hX.comm hX.exp hX.inv hVpX
        (fix_sup_orth B hx3 hx0inv) (T := Tp) inf_le_right hTpiso hTpX
      have hTp1 : 1 ≤ finrank K Tp := Submodule.one_le_finrank_iff.mpr hTp0
      have h6 : 3 ^ ((n - 1) * 2) ≤ 3 ^ (2 * n - 5 + 2) := calc
        3 ^ ((n - 1) * 2) ≤ Nat.card X ^ 2 := hcard2
        _ ≤ 3 ^ (finrank K Vp - finrank K Tp) *
            Nat.card (X ⊓ fixG Vp : Subgroup (Module.End K V)ˣ) ^ 2 := h5
        _ ≤ 3 ^ (2 * n - 5) * 3 ^ 2 :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
            (Nat.pow_le_pow_left hXp 2)
        _ = 3 ^ (2 * n - 5 + 2) := by rw [pow_add]
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h6
      omega

theorem lemII (hK : Nat.card K = 2) {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    (hr : B.IsRefl) {X : Subgroup (Module.End K V)ˣ} (hX : IsoSetup B X)
    {x₀ : (Module.End K V)ˣ} (hx₀ : x₀ ∈ X) (hx₁ : x₀ ≠ 1) {n : ℕ} (hn : 3 ≤ n)
    (hdim : finrank K V = 2 * n) (hcard : 3 ^ (n - 1) ≤ Nat.card X) {T : Submodule K V}
    (hT0 : T ≠ ⊥) (hTiso : ∀ u ∈ T, ∀ v ∈ T, B u v = 0)
    (hTX : ∀ x ∈ X, ∀ t ∈ T, (x : Module.End K V) t ∈ T)
    (hXm : ∀ g ∈ X, g ∈ fixG (LinearMap.range ((x₀ : Module.End K V) - 1)) → g = 1) :
    finrank K (LinearMap.ker ((x₀ : Module.End K V) - 1)) ≤ 2 ∧
      ∀ g ∈ X, g ∈ fixG (LinearMap.ker ((x₀ : Module.End K V) - 1)) := by
  classical
  have := finite_units_end (K := K) (V := V)
  set Vp := LinearMap.ker ((x₀ : Module.End K V) - 1) with hVp
  set Vm := LinearMap.range ((x₀ : Module.End K V) - 1) with hVm
  have hx3 : x₀ ^ 3 = 1 := hX.exp x₀ hx₀
  have hcompl : IsCompl Vp Vm := isCompl_fix_rng hx3
  have hsum : finrank K Vp + finrank K Vm = 2 * n :=
    hdim ▸ Submodule.finrank_add_eq_of_isCompl hcompl
  have hVpX : ∀ x ∈ X, ∀ v ∈ Vp, (x : Module.End K V) v ∈ Vp :=
    fun x hx v hv => fix_invariant (hX.comm x₀ hx₀ x hx) hv
  have hVmX : ∀ x ∈ X, ∀ v ∈ Vm, (x : Module.End K V) v ∈ Vm :=
    fun x hx v hv => rng_invariant' (hX.comm x₀ hx₀ x hx) hv
  have hx0inv := hX.inv x₀ hx₀
  have hXm' : (X ⊓ fixG Vm : Subgroup (Module.End K V)ˣ) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    exact hXm g hg.1 hg.2
  have h3 := card_sq_le hK (finrank K Vm) Vm rfl X hX.comm hX.exp hVmX
  rw [hXm', Subgroup.card_bot, one_pow, mul_one] at h3
  have hcard2 : 3 ^ ((n - 1) * 2) ≤ Nat.card X ^ 2 := by
    rw [pow_mul 3 (n - 1) 2]
    exact Nat.pow_le_pow_left hcard 2
  have hdm : 2 * n - 2 ≤ finrank K Vm := by
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hcard2.trans h3)
    omega
  have hdp2 : finrank K Vp ≤ 2 := by omega
  refine ⟨hdp2, ?_⟩
  have hdmeven : Even (finrank K Vm) := even_finrank_rng hK hx3
  obtain ⟨c, hc⟩ := hdmeven
  have hdpcases : finrank K Vp = 0 ∨ finrank K Vp = 2 := by omega
  rcases hdpcases with hdp0 | hdp2'
  · have hbot : Vp = ⊥ := Submodule.finrank_eq_zero.mp hdp0
    intro g _ u hu
    rw [hbot, Submodule.mem_bot] at hu
    rw [hu, map_zero]
  · have hdmv : finrank K Vm = 2 * n - 2 := by omega
    set Tp := T ⊓ Vp with hTp
    set Tm := T ⊓ Vm with hTm
    have hTpX : ∀ x ∈ X, ∀ t ∈ Tp, (x : Module.End K V) t ∈ Tp :=
      fun x hx t ht => ⟨hTX x hx t ht.1, hVpX x hx t ht.2⟩
    have hTmX : ∀ x ∈ X, ∀ t ∈ Tm, (x : Module.End K V) t ∈ Tm :=
      fun x hx t ht => ⟨hTX x hx t ht.1, hVmX x hx t ht.2⟩
    have hTpiso : ∀ u ∈ Tp, ∀ v ∈ Tp, B u v = 0 := fun u hu v hv => hTiso u hu.1 v hv.1
    have hTmiso : ∀ u ∈ Tm, ∀ v ∈ Tm, B u v = 0 := fun u hu v hv => hTiso u hu.1 v hv.1
    have hsplit := splitTI hx3 (fun t ht => hTX x₀ hx₀ t ht) hT0
    by_cases hTp0 : Tp = ⊥
    · exfalso
      have hTm0 : Tm ≠ ⊥ := by
        rcases hsplit with h | h
        · exact absurd hTp0 h
        · exact h
      have h5 := card_sq_le_sub hK B hB hr X hX.comm hX.exp hX.inv hVmX
        (rng_sup_orth B hx3 hx0inv) (T := Tm) inf_le_right hTmiso hTmX
      rw [hXm', Subgroup.card_bot, one_pow, mul_one] at h5
      have hTm1 : 1 ≤ finrank K Tm := Submodule.one_le_finrank_iff.mpr hTm0
      have h6 : 3 ^ ((n - 1) * 2) ≤ 3 ^ (2 * n - 3) := calc
        3 ^ ((n - 1) * 2) ≤ Nat.card X ^ 2 := hcard2
        _ ≤ 3 ^ (finrank K Vm - finrank K Tm) := h5
        _ ≤ 3 ^ (2 * n - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h6
      omega
    · have hTp1 : 1 ≤ finrank K Tp := Submodule.one_le_finrank_iff.mpr hTp0
      have h5 := card_sq_le_sub hK B hB hr X hX.comm hX.exp hX.inv hVpX
        (fix_sup_orth B hx3 hx0inv) (T := Tp) inf_le_right hTpiso hTpX
      have hXpexp : ∀ y ∈ (X ⊓ fixG Vp : Subgroup (Module.End K V)ˣ), y ^ 3 = 1 :=
        fun y hy => hX.exp y hy.1
      obtain ⟨j, hj⟩ := exists_card_eq_pow_three hXpexp
      obtain ⟨i, hi⟩ := exists_card_eq_pow_three hX.exp
      have hi1 : n - 1 ≤ i := by
        have h7 : 3 ^ (n - 1) ≤ 3 ^ i := hi ▸ hcard
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h7
      have hi2 : i * 2 ≤ 2 * n - 2 := by
        have h7 : 3 ^ (i * 2) ≤ 3 ^ (2 * n - 2) := calc
          3 ^ (i * 2) = Nat.card X ^ 2 := by rw [hi, ← pow_mul]
          _ ≤ 3 ^ finrank K Vm := h3
          _ = 3 ^ (2 * n - 2) := by rw [hdmv]
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h7
      have hj1 : i * 2 ≤ 1 + j * 2 := by
        have h7 : 3 ^ (i * 2) ≤ 3 ^ (1 + j * 2) := calc
          3 ^ (i * 2) = Nat.card X ^ 2 := by rw [hi, ← pow_mul]
          _ ≤ 3 ^ (finrank K Vp - finrank K Tp) *
              Nat.card (X ⊓ fixG Vp : Subgroup (Module.End K V)ˣ) ^ 2 := h5
          _ ≤ 3 ^ 1 * Nat.card (X ⊓ fixG Vp : Subgroup (Module.End K V)ˣ) ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
          _ = 3 ^ (1 + j * 2) := by rw [hj, ← pow_mul, pow_add]
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h7
      have hij : i ≤ j := by omega
      have hle : (X ⊓ fixG Vp : Subgroup (Module.End K V)ˣ) ≤ X := inf_le_left
      have heq : (X ⊓ fixG Vp : Subgroup (Module.End K V)ˣ) = X :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [hi, hj]
          exact Nat.pow_le_pow_right (by norm_num) hij)
      intro g hg
      have : g ∈ (X ⊓ fixG Vp : Subgroup (Module.End K V)ˣ) := by
        rw [heq]
        exact hg
      exact this.2

end Numerics

end CFSG.StandardType.SpFin
