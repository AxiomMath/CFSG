module

public import CFSG.Walter.W67.Section6.Util

public section

open scoped Pointwise

namespace CFSG.LocalAnalysis.WeakClosure81

variable {X : Type*} [Group X] [Finite X]

private def fixedBy (a : MulAut X) : Subgroup X where
  carrier := {x | a x = x}
  mul_mem' := by intro x y hx hy; simp only [Set.mem_setOf_eq] at *; rw [map_mul, hx, hy]
  one_mem' := by simp only [Set.mem_setOf_eq]; exact map_one a
  inv_mem' := by intro x hx; simp only [Set.mem_setOf_eq] at *; rw [map_inv, hx]

private lemma mem_fixedBy {a : MulAut X} {x : X} : x ∈ fixedBy a ↔ a x = x := Iff.rfl

private lemma map_eq_self_of_isPGroup_two_of_odd_index {Y : Subgroup X} [Y.Normal]
    (hY : IsPGroup 2 Y) (hodd : Odd Y.index) (a : MulAut X) :
    Y.map a.toMonoidHom = Y := by
  have hY' : IsPGroup 2 (Y.map a.toMonoidHom) := hY.map a.toMonoidHom
  have hP : IsPGroup 2 (Y ⊔ Y.map a.toMonoidHom : Subgroup X) :=
    IsPGroup.to_sup_of_normal_left hY hY'
  have hQ : IsPGroup 2 ((Y ⊔ Y.map a.toMonoidHom : Subgroup X).map
      (QuotientGroup.mk' Y)) := hP.map (QuotientGroup.mk' Y)
  have hdvd : Nat.card ((Y ⊔ Y.map a.toMonoidHom : Subgroup X).map
      (QuotientGroup.mk' Y)) ∣ Y.index := by
    rw [Subgroup.index]
    exact Subgroup.card_subgroup_dvd_card _
  have hoddQ : Odd (Nat.card ((Y ⊔ Y.map a.toMonoidHom : Subgroup X).map
      (QuotientGroup.mk' Y))) := Odd.of_dvd_nat hodd hdvd
  have hone : Nat.card ((Y ⊔ Y.map a.toMonoidHom : Subgroup X).map
      (QuotientGroup.mk' Y)) = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    have hk0 : k = 0 := by
      by_contra hkne
      rw [hk] at hoddQ
      exact (Nat.not_odd_iff_even.mpr (even_two.pow_of_ne_zero hkne)) hoddQ
    rw [hk, hk0, pow_zero]
  have hbot : (Y ⊔ Y.map a.toMonoidHom : Subgroup X).map (QuotientGroup.mk' Y) = ⊥ := by
    rw [Subgroup.eq_bot_iff_card]
    exact hone
  have hle : Y ⊔ Y.map a.toMonoidHom ≤ Y := by
    have h := (Subgroup.map_eq_bot_iff _).mp hbot
    rwa [QuotientGroup.ker_mk'] at h
  have hle' : Y.map a.toMonoidHom ≤ Y := le_trans le_sup_right hle
  refine Subgroup.eq_of_le_of_card_ge hle' ?_
  exact le_of_eq (Subgroup.card_map_of_injective
    (show Function.Injective a.toMonoidHom from a.injective)).symm

private lemma map_eq_self_of_forall_mem {V : Subgroup X} {a : MulAut X}
    (hV : ∀ v ∈ V, a v ∈ V) : V.map a.toMonoidHom = V := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.mpr ?_) ?_
  · intro v hv
    exact hV v hv
  · exact le_of_eq (Subgroup.card_map_of_injective
      (show Function.Injective a.toMonoidHom from a.injective)).symm

private lemma exists_fixed_of_involutive_odd {α : Type*} [Fintype α] [DecidableEq α]
    (f : α ≃ α) (hf : f * f = 1) (hodd : Odd (Nat.card α)) : ∃ x, f x = x := by
  have hcard : ¬ 2 ∣ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card]
    exact Odd.not_two_dvd_nat hodd
  refine Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hcard ?_
  rw [pow_one, pow_two]
  exact hf

private lemma exists_mulAut_quotient_of_normalizes {Y : Subgroup X} [Y.Normal] (a : MulAut X)
    (ha : a * a = 1) (hY : Y.map a.toMonoidHom = Y) :
    ∃ ā : MulAut (X ⧸ Y),
      (∀ x : X, ā (QuotientGroup.mk' Y x) = QuotientGroup.mk' Y (a x)) ∧ ā * ā = 1 := by
  have hle : Y ≤ Y.comap a.toMonoidHom := by
    intro y hy
    rw [Subgroup.mem_comap]
    exact hY ▸ (show a y ∈ Y.map a.toMonoidHom from ⟨y, hy, rfl⟩)
  let f : X ⧸ Y →* X ⧸ Y := QuotientGroup.map Y Y a.toMonoidHom hle
  have hff : ∀ z : X ⧸ Y, f (f z) = z := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Y z
    have h1 : f (QuotientGroup.mk' Y x) = QuotientGroup.mk' Y (a x) :=
      QuotientGroup.map_mk' Y Y a.toMonoidHom hle x
    have h2 : f (QuotientGroup.mk' Y (a x)) = QuotientGroup.mk' Y (a (a x)) :=
      QuotientGroup.map_mk' Y Y a.toMonoidHom hle (a x)
    rw [h1, h2]
    have : a (a x) = x := by rw [← MulAut.mul_apply, ha, MulAut.one_apply]
    rw [this]
  have hbij : Function.Bijective f :=
    ⟨fun x y h => by have := congrArg f h; rwa [hff x, hff y] at this,
      fun x => ⟨f x, hff x⟩⟩
  let ā : MulAut (X ⧸ Y) := MulEquiv.ofBijective f hbij
  refine ⟨ā, ?_, ?_⟩
  · intro x
    change f (QuotientGroup.mk' Y x) = QuotientGroup.mk' Y (a x)
    rw [QuotientGroup.map_mk']
    rfl
  · ext z
    change f (f z) = z
    exact hff z

private lemma mem_sup_of_inv_mul_mem_sup {Y V : Subgroup X} [Y.Normal] {a : MulAut X}
    (ha : a * a = 1) (hY : Y.map a.toMonoidHom = Y) (hV : ∀ v ∈ V, a v ∈ V)
    (hodd : Odd Y.index) (hC : fixedBy a ≤ V ⊔ Y)
    (hfix : ∀ x : X, x⁻¹ * a x ∈ Y → ∃ y : X, a y = y ∧ x⁻¹ * y ∈ Y)
    {r : X} (hr : r⁻¹ * a r ∈ V ⊔ Y) : r ∈ V ⊔ Y := by
  have hHinv : (V ⊔ Y).map a.toMonoidHom = V ⊔ Y := by
    rw [Subgroup.map_sup, map_eq_self_of_forall_mem hV, hY]
  obtain ⟨ā, hāmk, hā2⟩ := exists_mulAut_quotient_of_normalizes a ha hY
  let B : Subgroup (X ⧸ Y) := (V ⊔ Y).map (QuotientGroup.mk' Y)
  have hcomp : ā.toMonoidHom.comp (QuotientGroup.mk' Y) =
      (QuotientGroup.mk' Y).comp a.toMonoidHom := by
    ext x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact hāmk x
  have hBmap : B.map ā.toMonoidHom = B := by
    show ((V ⊔ Y).map (QuotientGroup.mk' Y)).map ā.toMonoidHom =
      (V ⊔ Y).map (QuotientGroup.mk' Y)
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hHinv]
  have hāB : ∀ b ∈ B, ā b ∈ B := by
    intro b hb
    have hmem : ā b ∈ B.map ā.toMonoidHom := ⟨b, hb, rfl⟩
    rwa [hBmap] at hmem
  let b₀ : X ⧸ Y := QuotientGroup.mk' Y (r⁻¹ * a r)
  have hb₀B : b₀ ∈ B := ⟨r⁻¹ * a r, hr, rfl⟩
  have hāq : ā (QuotientGroup.mk' Y r) = QuotientGroup.mk' Y r * b₀ := by
    show ā (QuotientGroup.mk' Y r) =
      QuotientGroup.mk' Y r * QuotientGroup.mk' Y (r⁻¹ * a r)
    rw [hāmk, ← map_mul]
    congr 1
    group
  have ht : a (r⁻¹ * a r) = (r⁻¹ * a r)⁻¹ := by
    rw [map_mul, map_inv, ← MulAut.mul_apply, ha, MulAut.one_apply]
    group
  have hb₀inv : b₀ * ā b₀ = 1 := by
    show QuotientGroup.mk' Y (r⁻¹ * a r) * ā (QuotientGroup.mk' Y (r⁻¹ * a r)) = 1
    rw [hāmk, ← map_mul, show (r⁻¹ * a r) * a (r⁻¹ * a r) = 1 from by rw [ht, mul_inv_cancel],
      map_one]
  let ψ : B → B := fun b => ⟨b₀ * ā b.1, B.mul_mem hb₀B (hāB b.1 b.2)⟩
  have hψ : ∀ b : B, ψ (ψ b) = b := by
    intro b
    apply Subtype.ext
    show b₀ * ā (b₀ * ā b.1) = b.1
    rw [map_mul, show ā (ā b.1) = b.1 from by
      rw [← MulAut.mul_apply, hā2, MulAut.one_apply], ← mul_assoc, hb₀inv, one_mul]
  have hψp : (⟨ψ, ψ, hψ, hψ⟩ : Equiv.Perm B) * ⟨ψ, ψ, hψ, hψ⟩ = 1 := by
    apply Equiv.ext
    intro b
    exact hψ b
  have hBodd : Odd (Nat.card B) := by
    refine Odd.of_dvd_nat hodd ?_
    rw [Subgroup.index]
    exact Subgroup.card_subgroup_dvd_card B
  haveI := Fintype.ofFinite B
  classical
  obtain ⟨b, hb⟩ := exists_fixed_of_involutive_odd ⟨ψ, ψ, hψ, hψ⟩ hψp hBodd
  have hbv : b₀ * ā b.1 = b.1 := congrArg Subtype.val hb
  obtain ⟨h, hhH, hh⟩ := b.2
  have hc : ā (QuotientGroup.mk' Y (r * h)) = QuotientGroup.mk' Y (r * h) := by
    rw [show QuotientGroup.mk' Y (r * h) = QuotientGroup.mk' Y r * QuotientGroup.mk' Y h from
      map_mul _ _ _, map_mul, hh, hāq, mul_assoc, hbv]
  have hmemY : (r * h)⁻¹ * a (r * h) ∈ Y := by
    have h1 : a (r * h) / (r * h) ∈ Y := by
      rw [← QuotientGroup.eq_iff_div_mem]
      show QuotientGroup.mk' Y (a (r * h)) = QuotientGroup.mk' Y (r * h)
      rw [← hāmk (r * h)]
      exact hc
    have h2 : a (r * h) * (r * h)⁻¹ ∈ Y := by simpa [div_eq_mul_inv] using h1
    exact (inferInstance : Y.Normal).mem_comm_iff.mp h2
  obtain ⟨y, hay, hxy⟩ := hfix (r * h) hmemY
  have hyH : y ∈ V ⊔ Y := hC hay
  have hrhH : r * h ∈ V ⊔ Y := by
    have hmem : (r * h)⁻¹ * y ∈ V ⊔ Y := (le_sup_right : Y ≤ V ⊔ Y) hxy
    have := (V ⊔ Y).mul_mem hyH (Subgroup.inv_mem _ hmem)
    simpa [mul_assoc] using this
  exact mul_mem_cancel_right hhH |>.mp hrhH

private lemma mem_of_pow_mem_of_pow_mem_of_coprime {H : Subgroup X} {x : X} {m n : ℕ}
    (hcop : Nat.Coprime m n) (hm : x ^ m ∈ H) (hn : x ^ n ∈ H) : x ∈ H := by
  have hxP : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  set P : Subgroup X := Subgroup.zpowers x with hP
  set K : Subgroup X := H ⊓ P with hK
  have h1 : (QuotientGroup.mk' (K.subgroupOf P)) (⟨x, hxP⟩ : P) ^ m = 1 := by
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
    exact ⟨hm, Subgroup.pow_mem _ hxP m⟩
  have h2 : (QuotientGroup.mk' (K.subgroupOf P)) (⟨x, hxP⟩ : P) ^ n = 1 := by
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
    exact ⟨hn, Subgroup.pow_mem _ hxP n⟩
  have hq : (QuotientGroup.mk' (K.subgroupOf P)) (⟨x, hxP⟩ : P) = 1 :=
    (pow_eq_one_iff_of_coprime hcop).mp ⟨h1, h2⟩
  have hmem : (⟨x, hxP⟩ : P) ∈ K.subgroupOf P := by
    rw [← QuotientGroup.ker_mk' (K.subgroupOf P)]
    exact MonoidHom.mem_ker.mp hq
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).1

private lemma card_dvd_card_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (φ : A →* B) (hφ : Function.Surjective φ) : Nat.card B ∣ Nat.card A := by
  have h1 : Nat.card A = Nat.card (MonoidHom.ker φ) * Nat.card B := by
    rw [← Subgroup.card_mul_index (H := MonoidHom.ker φ), Subgroup.index]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    rw [MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top]
  rw [h1]
  exact dvd_mul_left _ _

private lemma relIndex_sup_zpowers_dvd_orderOf {V : Subgroup X} {x : X}
    (hx : x ∈ Subgroup.normalizer (V : Set X)) :
    V.relIndex (V ⊔ Subgroup.zpowers x) ∣ orderOf x := by
  set V₁ : Subgroup X := V ⊔ Subgroup.zpowers x with hV₁
  have hle : V ≤ V₁ := le_sup_left
  have hnorm : V₁ ≤ Subgroup.normalizer (V : Set X) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hx)
  have hN : (V.subgroupOf V₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnorm
  let φ : Subgroup.zpowers x →* V₁ ⧸ V.subgroupOf V₁ :=
    (QuotientGroup.mk' (V.subgroupOf V₁)).comp (Subgroup.inclusion le_sup_right)
  have hφsurj : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf V₁) q
    have hsup : V.subgroupOf V₁ ⊔ (Subgroup.zpowers x).subgroupOf V₁ = ⊤ := by
      have h1 : V.subgroupOf V₁ ⊔ (Subgroup.zpowers x).subgroupOf V₁ =
          (V ⊔ Subgroup.zpowers x).subgroupOf V₁ :=
        (Subgroup.subgroupOf_sup le_sup_left le_sup_right).symm
      rw [h1, ← hV₁, Subgroup.subgroupOf_self]
    have hy : y ∈ V.subgroupOf V₁ ⊔ (Subgroup.zpowers x).subgroupOf V₁ := by
      rw [hsup]
      exact Subgroup.mem_top y
    have hy' : y ∈ (V.subgroupOf V₁ : Set V₁) * ((Subgroup.zpowers x).subgroupOf V₁ : Set V₁) := by
      rw [← Subgroup.normal_mul]
      exact hy
    obtain ⟨v, hv, w, hw, hvw⟩ := Set.mem_mul.mp hy'
    refine ⟨⟨(w : X), Subgroup.mem_subgroupOf.mp hw⟩, ?_⟩
    have hv1 : QuotientGroup.mk' (V.subgroupOf V₁) v = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hv
    have hwi : Subgroup.inclusion le_sup_right
        (⟨(w : X), Subgroup.mem_subgroupOf.mp hw⟩ : Subgroup.zpowers x) = w := Subtype.ext rfl
    show QuotientGroup.mk' (V.subgroupOf V₁)
        (Subgroup.inclusion le_sup_right
          (⟨(w : X), Subgroup.mem_subgroupOf.mp hw⟩ : Subgroup.zpowers x)) =
        QuotientGroup.mk' (V.subgroupOf V₁) y
    rw [hwi, ← hvw, map_mul, hv1, one_mul]
  have h := card_dvd_card_of_surjective φ hφsurj
  rwa [Nat.card_zpowers] at h

private lemma exists_odd_pow_of_notMem {Y V : Subgroup X} [Y.Normal] {a : MulAut X}
    (ha : a * a = 1) (hY : IsPGroup 2 Y) (hodd : Odd Y.index) {x : X}
    (hxinv : a x = x⁻¹) (hxH : x ∉ V ⊔ Y) :
    ∃ x' : X, Odd (orderOf x') ∧ a x' = x'⁻¹ ∧ x' ∈ Subgroup.zpowers x ∧
      x' ∉ V ⊔ Y := by
  set d : ℕ := orderOf (QuotientGroup.mk' Y x) with hd
  set k : ℕ := orderOf x / d with hk
  have hdx : d ∣ orderOf x := orderOf_map_dvd (QuotientGroup.mk' Y) x
  have hdne : d ≠ 0 := (isOfFinOrder_of_finite (QuotientGroup.mk' Y x)).orderOf_pos.ne'
  have hxne : orderOf x ≠ 0 := (isOfFinOrder_of_finite x).orderOf_pos.ne'
  have hdodd : Odd d := Odd.of_dvd_nat hodd (orderOf_dvd_natCard (QuotientGroup.mk' Y x))
  have hxd_mem : x ^ d ∈ Y := by
    rw [← QuotientGroup.ker_mk' Y, MonoidHom.mem_ker]
    show (QuotientGroup.mk' Y) (x ^ d) = 1
    rw [map_pow]
    exact pow_orderOf_eq_one _
  have hkord : k = orderOf (x ^ d) := (orderOf_pow_of_dvd hdne hdx).symm
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hY
  have hk_dvd : k ∣ 2 ^ j := by
    rw [hkord, ← hj]
    have h := orderOf_dvd_natCard (⟨x ^ d, hxd_mem⟩ : Y)
    rwa [Subgroup.orderOf_mk] at h
  have hcop : Nat.Coprime k d :=
    (Nat.coprime_two_right.mpr hdodd).symm.pow_left j |>.coprime_dvd_left hk_dvd
  refine ⟨x ^ k, ?_, ?_, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) k, ?_⟩
  · rw [orderOf_pow_orderOf_div hxne hdx]
    exact hdodd
  · rw [map_pow, hxinv, inv_pow]
  · exact fun hmem => hxH (mem_of_pow_mem_of_pow_mem_of_coprime hcop hmem
      ((le_sup_right : Y ≤ V ⊔ Y) hxd_mem))


private lemma mem_normalizer_of_cj_eq_self {V : Subgroup X} {g : X}
    (h : CFSG.Walter.W67.Sec6.cj g V = V) : g ∈ Subgroup.normalizer (V : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : g * x * g⁻¹ ∈ CFSG.Walter.W67.Sec6.cj g V := CFSG.Walter.W67.Sec6.conj_mem_cj hx
    rwa [h] at h1
  · intro hx
    have hcg : CFSG.Walter.W67.Sec6.cj g⁻¹ V = V := by
      have h1 := CFSG.Walter.W67.Sec6.cj_inv_cj g V
      rwa [h] at h1
    have h1 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ CFSG.Walter.W67.Sec6.cj g⁻¹ V :=
      CFSG.Walter.W67.Sec6.conj_mem_cj (g := g⁻¹) hx
    rw [hcg] at h1
    simpa [inv_inv, mul_assoc] using h1

theorem exists_complement_invariant_of_involution {Y : Subgroup X} [Y.Normal] (hY : IsPGroup 2 Y)
    (hodd : Odd Y.index) (hnil : Group.IsNilpotent (X ⧸ Y)) (a : MulAut X) (ha : a * a = 1)
    (hfix : ∀ x : X, x⁻¹ * a x ∈ Y → ∃ y : X, a y = y ∧ x⁻¹ * y ∈ Y) :
    ∃ S : Subgroup X, S ⊓ Y = ⊥ ∧ S ⊔ Y = ⊤ ∧ ∀ s ∈ S, a s ∈ S := by
  classical
  have hYmap : Y.map a.toMonoidHom = Y := map_eq_self_of_isPGroup_two_of_odd_index hY hodd a
  have hcop : Nat.Coprime (Nat.card (Y.subgroupOf (fixedBy a)))
      (Y.subgroupOf (fixedBy a)).index := by
    have h2 : IsPGroup 2 (Y.comap (fixedBy a).subtype) := hY.comap_subtype (K := fixedBy a)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    change Nat.Coprime (Nat.card (Y.comap (fixedBy a).subtype)) (Y.relIndex (fixedBy a))
    rw [hk]
    exact (Nat.coprime_two_right.mpr (Odd.of_dvd_nat hodd
      (Subgroup.relIndex_dvd_index_of_normal (H := Y) (K := fixedBy a)))).symm.pow_left k
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup X, U = K.map (fixedBy a).subtype := ⟨_, rfl⟩
  have hUle : U ≤ fixedBy a := by rw [hUdef]; exact Subgroup.map_subtype_le _
  have hUinv : ∀ v ∈ U, a v ∈ U := fun v hv => by
    rw [mem_fixedBy.mp (hUle hv)]
    exact hv
  have hUsup : fixedBy a ≤ U ⊔ Y := by
    have h2 : (Y.subgroupOf (fixedBy a)).map (fixedBy a).subtype ⊔ U = fixedBy a := by
      rw [hUdef, ← Subgroup.map_sup, hK.sup_eq_top, Subgroup.map_top, Subgroup.range_subtype]
    have hleY : (Y.subgroupOf (fixedBy a)).map (fixedBy a).subtype ≤ Y := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_le_left
    calc fixedBy a = (Y.subgroupOf (fixedBy a)).map (fixedBy a).subtype ⊔ U := h2.symm
      _ ≤ Y ⊔ U := sup_le_sup_right hleY U
      _ = U ⊔ Y := sup_comm Y U
  have hUodd : Odd (Nat.card U) := by
    rw [hUdef, Subgroup.card_map_of_injective (fixedBy a).subtype_injective]
    rw [show Nat.card K = (Y.subgroupOf (fixedBy a)).index from hK.card_right]
    exact Odd.of_dvd_nat hodd (Subgroup.relIndex_dvd_index_of_normal (H := Y) (K := fixedBy a))
  let 𝒮 : Set (Subgroup X) := {V | Odd (Nat.card V) ∧ (∀ v ∈ V, a v ∈ V) ∧ fixedBy a ≤ V ⊔ Y}
  have h𝒮ne : 𝒮.Nonempty := ⟨U, hUodd, hUinv, hUsup⟩
  have h𝒮fin : 𝒮.Finite := by
    haveI : Finite (Subgroup X) :=
      Finite.of_injective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective
    exact Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  obtain ⟨V, hVmem, hVmax⟩ := Finset.exists_max_image h𝒮fin.toFinset (fun V => Nat.card V)
    ((Set.Finite.toFinset_nonempty h𝒮fin).mpr h𝒮ne)
  have hV𝒮 : V ∈ 𝒮 := (Set.Finite.mem_toFinset h𝒮fin).mp hVmem
  obtain ⟨hVodd, hVinv, hVsup⟩ := hV𝒮
  have hVmax' : ∀ W ∈ 𝒮, V ≤ W → Nat.card W ≤ Nat.card V :=
    fun W hW _ => hVmax W ((Set.Finite.mem_toFinset h𝒮fin).mpr hW)
  have hVinfY : V ⊓ Y = ⊥ := by
    have h2 : IsPGroup 2 (V ⊓ Y : Subgroup X) := hY.to_le inf_le_right
    have hodd2 : Odd (Nat.card ↥(V ⊓ Y)) := by
      have h := Subgroup.relIndex_mul_card (H := V ⊓ Y) (K := V)
      rw [inf_eq_left.mpr inf_le_left] at h
      exact Odd.of_dvd_nat hVodd (dvd_of_mul_left_eq _ h)
    have hone : Nat.card ↥(V ⊓ Y) = 1 := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
      rw [hk] at hodd2
      have hk0 : k = 0 := by
        by_contra hkne
        exact (Nat.not_odd_iff_even.mpr (even_two.pow_of_ne_zero hkne)) hodd2
      rw [hk, hk0, pow_zero]
    exact Subgroup.eq_bot_of_card_eq _ hone
  by_cases htop : V ⊔ Y = ⊤
  · exact ⟨V, hVinfY, htop, hVinv⟩
  ·
    set H : Subgroup X := V ⊔ Y with hH
    have hHlt : H < ⊤ := lt_top_iff_ne_top.mpr htop
    haveI := hnil
    have hnc : NormalizerCondition (X ⧸ Y) := Group.normalizerCondition_of_isNilpotent
    have hkerle : (QuotientGroup.mk' Y).ker ≤ H := by
      rw [QuotientGroup.ker_mk']
      exact le_sup_right
    have hHmap_lt : H.map (QuotientGroup.mk' Y) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro hcon
      apply htop
      have h1 := congrArg (Subgroup.comap (QuotientGroup.mk' Y)) hcon
      rwa [Subgroup.comap_map_eq_self hkerle, Subgroup.comap_top] at h1
    obtain ⟨z, hzN, hzH⟩ := SetLike.exists_of_lt (hnc (H.map (QuotientGroup.mk' Y)) hHmap_lt)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Y z
    have hgH : g ∉ H := fun hg => hzH (Subgroup.mem_map_of_mem _ hg)
    have hgN : g ∈ Subgroup.normalizer (H : Set X) := by
      have h1 : g ∈ (Subgroup.normalizer (H.map (QuotientGroup.mk' Y))).comap
          (QuotientGroup.mk' Y) := hzN
      rwa [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective Y),
        Subgroup.comap_map_eq_self hkerle] at h1
    have hYnormH : H ≤ Subgroup.normalizer (Y : Set X) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : Y.Normal)]
      exact le_top
    have hYtop : Y ≤ Subgroup.normalizer (Y : Set X) := Subgroup.le_normalizer
    have hcopY : Nat.Coprime (Nat.card Y) (Y.relIndex H) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hY
      rw [hk]
      exact (Nat.coprime_two_right.mpr (Odd.of_dvd_nat hodd
        (Subgroup.relIndex_dvd_index_of_normal (H := Y) (K := H)))).symm.pow_left k
    have hVY : V ≤ H := le_sup_left
    have hgVY : CFSG.Walter.W67.Sec6.cj g V ≤ H :=
      (CFSG.Walter.W67.Sec6.cj_mono hVY).trans_eq
        (CFSG.Walter.W67.Sec6.cj_eq_self_of_mem_normalizer hgN)
    have hYgV : Y ⊓ CFSG.Walter.W67.Sec6.cj g V = ⊥ := by
      have h2 : IsPGroup 2 (Y ⊓ CFSG.Walter.W67.Sec6.cj g V : Subgroup X) := hY.to_le inf_le_left
      have hodd2 : Odd (Nat.card ↥(Y ⊓ CFSG.Walter.W67.Sec6.cj g V)) := by
        have h := Subgroup.relIndex_mul_card (H := Y ⊓ CFSG.Walter.W67.Sec6.cj g V)
          (K := CFSG.Walter.W67.Sec6.cj g V)
        rw [inf_eq_left.mpr inf_le_right, CFSG.Walter.W67.Sec6.card_cj] at h
        exact Odd.of_dvd_nat hVodd (dvd_of_mul_left_eq _ h)
      have hone : Nat.card ↥(Y ⊓ CFSG.Walter.W67.Sec6.cj g V) = 1 := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
        rw [hk] at hodd2
        have hk0 : k = 0 := by
          by_contra hkne
          exact (Nat.not_odd_iff_even.mpr (even_two.pow_of_ne_zero hkne)) hodd2
        rw [hk, hk0, pow_zero]
      exact Subgroup.eq_bot_of_card_eq _ hone
    have hYgVs : Y ⊔ CFSG.Walter.W67.Sec6.cj g V = H := by
      have hYcj : CFSG.Walter.W67.Sec6.cj g Y = Y :=
        CFSG.Walter.W67.Sec6.cj_eq_self_of_mem_normalizer (by
          rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : Y.Normal)]
          exact Subgroup.mem_top g)
      calc Y ⊔ CFSG.Walter.W67.Sec6.cj g V
          = CFSG.Walter.W67.Sec6.cj g Y ⊔ CFSG.Walter.W67.Sec6.cj g V := by rw [hYcj]
        _ = CFSG.Walter.W67.Sec6.cj g (Y ⊔ V) := (CFSG.Walter.W67.Sec6.cj_sup g Y V).symm
        _ = CFSG.Walter.W67.Sec6.cj g H := by rw [hH, sup_comm]
        _ = H := CFSG.Walter.W67.Sec6.cj_eq_self_of_mem_normalizer hgN
    obtain ⟨c, hcY, hccj⟩ := CFSG.Walter.W67.Sec6.exists_conj_complement_in
      (C := Y) (N := H) (W₁ := V) (W₂ := CFSG.Walter.W67.Sec6.cj g V)
      le_sup_right hYnormH hcopY hVY hgVY (by rw [inf_comm]; exact hVinfY)
      (by rw [hH, sup_comm]) hYgV hYgVs
    let n : X := c⁻¹ * g
    have hnV : n ∈ Subgroup.normalizer (V : Set X) := by
      apply mem_normalizer_of_cj_eq_self
      show CFSG.Walter.W67.Sec6.cj (c⁻¹ * g) V = V
      rw [CFSG.Walter.W67.Sec6.cj_mul, hccj, CFSG.Walter.W67.Sec6.cj_inv_cj]
    have hnH : n ∉ H := by
      intro hn
      apply hgH
      have hcn : c * n = g := by rw [show n = c⁻¹ * g from rfl]; group
      rw [← hcn]
      exact H.mul_mem ((le_sup_right : Y ≤ V ⊔ Y) hcY) hn
    let x : X := n⁻¹ * a n
    have hxinv : a x = x⁻¹ := by
      show a (n⁻¹ * a n) = (n⁻¹ * a n)⁻¹
      rw [map_mul, map_inv, ← MulAut.mul_apply, ha, MulAut.one_apply]
      group
    have hxH : x ∉ H := fun hx =>
      hnH (mem_sup_of_inv_mul_mem_sup ha hYmap hVinv hodd hVsup hfix
        (r := n) (by rw [show n⁻¹ * a n = x from rfl]; exact hx))
    have hVmap : V.map a.toMonoidHom = V := map_eq_self_of_forall_mem hVinv
    have hViff : ∀ v : X, a v ∈ V ↔ v ∈ V := by
      intro v
      constructor
      · intro hv
        rw [← hVmap] at hv
        obtain ⟨w, hw, hwv⟩ := hv
        rwa [a.injective hwv] at hw
      · intro hv
        rw [← hVmap]
        exact ⟨v, hv, rfl⟩
    have hViff' : ∀ v : X, a⁻¹ v ∈ V ↔ v ∈ V := by
      intro v
      have h := hViff (a⁻¹ v)
      rw [show a (a⁻¹ v) = v from by
        rw [← MulAut.mul_apply, mul_inv_cancel a, MulAut.one_apply]] at h
      exact h.symm
    have haN : a n ∈ Subgroup.normalizer (V : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro v
      have h1 : a (n * (a⁻¹ v) * n⁻¹) = (a n) * v * (a n)⁻¹ := by
        rw [map_mul, map_mul, map_inv, show a (a⁻¹ v) = v from by
          rw [← MulAut.mul_apply, mul_inv_cancel a, MulAut.one_apply]]
      rw [← h1, hViff]
      exact (hViff' v).symm.trans (Subgroup.mem_normalizer_iff.mp hnV (a⁻¹ v))
    have hxN : x ∈ Subgroup.normalizer (V : Set X) := by
      show n⁻¹ * a n ∈ Subgroup.normalizer (V : Set X)
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hnV) haN
    obtain ⟨x', hx'odd, hx'inv, hx'zp, hx'H⟩ :=
      exists_odd_pow_of_notMem ha hY hodd hxinv (by simpa only [hH] using hxH)
    have hx'N : x' ∈ Subgroup.normalizer (V : Set X) :=
      Subgroup.zpowers_le.mpr hxN hx'zp
    have hx'V : x' ∉ V := fun hv => hx'H ((le_sup_left : V ≤ V ⊔ Y) hv)
    have hV₁inv : ∀ v ∈ V ⊔ Subgroup.zpowers x', a v ∈ V ⊔ Subgroup.zpowers x' := by
      have hmap : (V ⊔ Subgroup.zpowers x').map a.toMonoidHom = V ⊔ Subgroup.zpowers x' := by
        rw [Subgroup.map_sup, hVmap, MonoidHom.map_zpowers,
          show a.toMonoidHom x' = x'⁻¹ from hx'inv, Subgroup.zpowers_inv]
      intro v hv
      have : a v ∈ (V ⊔ Subgroup.zpowers x').map a.toMonoidHom := ⟨v, hv, rfl⟩
      rwa [hmap] at this
    have hV₁odd : Odd (Nat.card ↥(V ⊔ Subgroup.zpowers x')) := by
      have hcard : Nat.card ↥(V ⊔ Subgroup.zpowers x') =
          V.relIndex (V ⊔ Subgroup.zpowers x') * Nat.card V := by
        have h := Subgroup.relIndex_mul_card (H := V) (K := V ⊔ Subgroup.zpowers x')
        rw [inf_eq_left.mpr le_sup_left] at h
        exact h.symm
      rw [hcard, mul_comm]
      exact hVodd.mul (Odd.of_dvd_nat hx'odd (relIndex_sup_zpowers_dvd_orderOf hx'N))
    have hV₁sup : fixedBy a ≤ (V ⊔ Subgroup.zpowers x' : Subgroup X) ⊔ Y :=
      hVsup.trans (sup_le_sup_right (le_sup_left : V ≤ V ⊔ Subgroup.zpowers x') Y)
    have hV₁lt : V < (V ⊔ Subgroup.zpowers x' : Subgroup X) :=
      lt_of_le_of_ne le_sup_left fun h =>
        hx'V (h ▸ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x') :
          x' ∈ V ⊔ Subgroup.zpowers x'))
    exact absurd (hVmax' (V ⊔ Subgroup.zpowers x') ⟨hV₁odd, hV₁inv, hV₁sup⟩ le_sup_left)
      (not_le_of_gt (Subgroup.card_lt_of_lt hV₁lt))

theorem exists_complement_normalized_of_involution {G : Type*} [Group G] [Finite G]
    {X Y : Subgroup G} {a : G} (hYX : Y ≤ X) [(Y.subgroupOf X).Normal]
    (hY : IsPGroup 2 Y) (hodd : Odd (Y.relIndex X))
    (hnil : Group.IsNilpotent (↥X ⧸ Y.subgroupOf X)) (ha : a * a = 1)
    (haX : a ∈ Subgroup.normalizer (X : Set G))
    (hfix : ∀ x ∈ X, x⁻¹ * (a * x * a⁻¹) ∈ Y → ∃ y ∈ X, a * y = y * a ∧ x⁻¹ * y ∈ Y) :
    ∃ S : Subgroup G, S ≤ X ∧ S ⊓ Y = ⊥ ∧ S ⊔ Y = X ∧
      a ∈ Subgroup.normalizer (S : Set G) := by
  classical
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  let φ : MulAut ↥X := X.normalizerMonoidHom ⟨a, haX⟩
  have hφa : ∀ x : ↥X, ((φ x : ↥X) : G) = a * (x : G) * a⁻¹ := fun _ => rfl
  have hφ2 : φ * φ = 1 := by
    ext x
    rw [MulAut.mul_apply, hφa, hφa, ha', MulAut.one_apply]
    rw [show a * (a * (x : G) * a) * a = (a * a) * ((x : G) * (a * a)) from by group,
      ha, one_mul, mul_one]
  have hfix' : ∀ x : ↥X, x⁻¹ * φ x ∈ Y.subgroupOf X →
      ∃ y : ↥X, φ y = y ∧ x⁻¹ * y ∈ Y.subgroupOf X := by
    intro x hx
    have hxG : (x : G)⁻¹ * (a * (x : G) * a⁻¹) ∈ Y := hx
    obtain ⟨y, hyX, hay, hxy⟩ := hfix (x : G) x.2 hxG
    refine ⟨⟨y, hyX⟩, ?_, ?_⟩
    · apply Subtype.ext
      show a * y * a⁻¹ = y
      rw [hay, mul_assoc, mul_inv_cancel a, mul_one]
    · show (x : G)⁻¹ * y ∈ Y
      exact hxy
  obtain ⟨S', hS'inf, hS'sup, hS'inv⟩ :=
    exists_complement_invariant_of_involution (Y := Y.subgroupOf X) (hY.comap_subtype (K := X))
      hodd hnil φ hφ2 hfix'
  refine ⟨S'.map X.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · have hYeq : (Y.subgroupOf X).map X.subtype = Y := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYX]
    have h := congrArg (Subgroup.map X.subtype) hS'inf
    rw [Subgroup.map_inf_eq _ _ _ X.subtype_injective, hYeq, Subgroup.map_bot] at h
    exact h
  · have hYeq : (Y.subgroupOf X).map X.subtype = Y := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYX]
    have h := congrArg (Subgroup.map X.subtype) hS'sup
    rw [Subgroup.map_sup, hYeq, Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(φ s : ↥X), hS'inv s hs, hφa s⟩
    · intro hz
      obtain ⟨s, hs, hsz⟩ := hz
      refine ⟨(φ s : ↥X), hS'inv s hs, ?_⟩
      change ((φ s : ↥X) : G) = z
      rw [hφa s, show (s : G) = a * z * a⁻¹ from hsz, ha']
      rw [show a * (a * z * a) * a = (a * a) * (z * (a * a)) from by group,
        ha, one_mul, mul_one]

end CFSG.LocalAnalysis.WeakClosure81
