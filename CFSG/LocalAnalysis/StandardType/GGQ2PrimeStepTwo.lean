module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GGQ2Prime

open Subgroup

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {X N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) {g : G} (hg : g ∈ X ⊔ N) :
    ∃ a ∈ X, ∃ n ∈ N, a * n = g := by
  have : g ∈ ((X ⊔ N : Subgroup G) : Set G) := hg
  rw [coe_mul_of_left_le_normalizer_right X N hXN] at this
  obtain ⟨a, ha, n, hn, h⟩ := Set.mem_mul.1 this
  exact ⟨a, ha, n, hn, h⟩

theorem eq_of_mul_eq_mul {G : Type*} [Group G] {X N : Subgroup G}
    (hint : X ⊓ N = ⊥) {a a' n n' : G} (ha : a ∈ X) (ha' : a' ∈ X)
    (hn : n ∈ N) (hn' : n' ∈ N) (h : a * n = a' * n') : a = a' := by
  have h1 : a'⁻¹ * a = n' * n⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * n) * n⁻¹ := by group
      _ = a'⁻¹ * (a' * n') * n⁻¹ := by rw [h]
      _ = n' * n⁻¹ := by group
  have hm : a'⁻¹ * a ∈ X ⊓ N := mem_inf.2 ⟨mul_mem (inv_mem ha') ha, h1 ▸ mul_mem hn' (inv_mem hn)⟩
  rw [hint, mem_bot] at hm
  calc a = a' * (a'⁻¹ * a) := by group
    _ = a' := by rw [hm, mul_one]

@[expose] noncomputable def proj {G : Type*} [Group G] {X N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) (hint : X ⊓ N = ⊥) :
    ↥(X ⊔ N) →* ↥X where
  toFun g := ⟨Classical.choose (exists_mul_of_mem_sup hXN g.2),
    (Classical.choose_spec (exists_mul_of_mem_sup hXN g.2)).1⟩
  map_one' := by
    obtain ⟨ha, n, hn, h⟩ := Classical.choose_spec (exists_mul_of_mem_sup hXN (one_mem (X ⊔ N)))
    apply Subtype.ext
    exact eq_of_mul_eq_mul hint ha (one_mem X) hn (one_mem N) (by simpa using h)
  map_mul' g h := by
    obtain ⟨ha, n, hn, hg⟩ := Classical.choose_spec (exists_mul_of_mem_sup hXN g.2)
    obtain ⟨hb, m, hm, hh⟩ := Classical.choose_spec (exists_mul_of_mem_sup hXN h.2)
    obtain ⟨hc, k, hk, hgh⟩ := Classical.choose_spec (exists_mul_of_mem_sup hXN (g * h).2)
    set a := Classical.choose (exists_mul_of_mem_sup hXN g.2)
    set b := Classical.choose (exists_mul_of_mem_sup hXN h.2)
    set c := Classical.choose (exists_mul_of_mem_sup hXN (g * h).2)
    apply Subtype.ext
    show c = a * b
    have hbn : b⁻¹ * n * b ∈ N := by
      have := (mem_normalizer_iff.1 (hXN (inv_mem hb)) n).1 hn
      simpa using this
    refine eq_of_mul_eq_mul hint hc (mul_mem ha hb) hk (mul_mem hbn hm) ?_
    rw [hgh, Subgroup.coe_mul, ← hg, ← hh]
    group

theorem proj_spec {G : Type*} [Group G] {X N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) (hint : X ⊓ N = ⊥) (g : ↥(X ⊔ N)) :
    ∃ n ∈ N, ((proj hXN hint g : X) : G) * n = g :=
  (Classical.choose_spec (exists_mul_of_mem_sup hXN g.2)).2

theorem proj_eq {G : Type*} [Group G] {X N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) (hint : X ⊓ N = ⊥) (g : ↥(X ⊔ N)) {a n : G}
    (ha : a ∈ X) (hn : n ∈ N) (h : a * n = g) : ((proj hXN hint g : X) : G) = a := by
  obtain ⟨m, hm, hg⟩ := proj_spec hXN hint g
  exact eq_of_mul_eq_mul hint (proj hXN hint g).2 ha hm hn (hg.trans h.symm)

abbrev bothNorm {G : Type*} [Group G] (X N : Subgroup G) : Subgroup G :=
  normalizer ((X ⊔ N : Subgroup G) : Set G) ⊓ normalizer (N : Set G)

theorem conj_mem_sup {G : Type*} [Group G] [Finite G] {X N : Subgroup G}
    {s : G} (hs : s ∈ bothNorm X N) {y : G} (hy : y ∈ X) :
    s * y * s⁻¹ ∈ X ⊔ N :=
  (mem_normalizer_iff.1 hs.1 y).1 (mem_sup_left hy)

@[expose] noncomputable def actEnd {G : Type*} [Group G] [Finite G] {X N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) (hint : X ⊓ N = ⊥)
    (s : bothNorm X N) : ↥X →* ↥X where
  toFun y := proj hXN hint ⟨s * y * (s : G)⁻¹, conj_mem_sup s.2 y.2⟩
  map_one' := by
    rw [← map_one (proj hXN hint)]
    congr 1
    ext; simp
  map_mul' y z := by
    rw [← map_mul]
    congr 1
    ext; simp [mul_assoc]

theorem actEnd_injective {G : Type*} [Group G] [Finite G] {X N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) (hint : X ⊓ N = ⊥)
    (s : bothNorm X N) : Function.Injective (actEnd hXN hint s) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨n, hn, h⟩ := proj_spec hXN hint ⟨s * y * (s : G)⁻¹, conj_mem_sup s.2 y.2⟩
  have h1 : ((proj hXN hint ⟨s * y * (s : G)⁻¹, conj_mem_sup s.2 y.2⟩ : X) : G) = 1 :=
    congrArg Subtype.val hy
  rw [h1, one_mul] at h
  have h' : (s : G) * y * (s : G)⁻¹ = n := by simpa using h.symm
  have hyN : (y : G) ∈ N := (mem_normalizer_iff.1 s.2.2 y).2 (h' ▸ hn)
  have hyb : (y : G) ∈ X ⊓ N := mem_inf.2 ⟨y.2, hyN⟩
  rw [hint, mem_bot] at hyb
  exact Subtype.ext hyb

@[expose] noncomputable def actAut {G : Type*} [Group G] [Finite G] {X N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) (hint : X ⊓ N = ⊥)
    (s : bothNorm X N) : MulAut ↥X :=
  MulEquiv.ofBijective (actEnd hXN hint s)
    ⟨actEnd_injective hXN hint s, Finite.injective_iff_surjective.1 (actEnd_injective hXN hint s)⟩

theorem actAut_apply {G : Type*} [Group G] [Finite G] {X N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) (hint : X ⊓ N = ⊥) (s : bothNorm X N)
    (y : X) : actAut hXN hint s y = proj hXN hint ⟨s * y * (s : G)⁻¹, conj_mem_sup s.2 y.2⟩ :=
  rfl

@[expose] noncomputable def actHom {G : Type*} [Group G] [Finite G] {X N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) (hint : X ⊓ N = ⊥) :
    bothNorm X N →* MulAut ↥X where
  toFun := actAut hXN hint
  map_one' := by
    ext y
    rw [actAut_apply, MulAut.one_apply]
    exact proj_eq hXN hint _ y.2 (one_mem N) (by simp)
  map_mul' s r := by
    ext y
    rw [MulAut.mul_apply, actAut_apply, actAut_apply, actAut_apply]
    obtain ⟨n, hn, hr⟩ := proj_spec hXN hint ⟨r * y * (r : G)⁻¹, conj_mem_sup r.2 y.2⟩
    set a := proj hXN hint ⟨r * y * (r : G)⁻¹, conj_mem_sup r.2 y.2⟩
    obtain ⟨m, hm, hs⟩ := proj_spec hXN hint ⟨s * a * (s : G)⁻¹, conj_mem_sup s.2 a.2⟩
    set b := proj hXN hint ⟨s * a * (s : G)⁻¹, conj_mem_sup s.2 a.2⟩
    have hsn : (s : G) * n * (s : G)⁻¹ ∈ N := (mem_normalizer_iff.1 s.2.2 n).1 hn
    refine proj_eq hXN hint _ b.2 (mul_mem hm hsn) ?_
    simp only [Subgroup.coe_mul] at hr hs ⊢
    calc (b : G) * (m * (s * n * (s : G)⁻¹)) = (b * m) * (s * n * (s : G)⁻¹) := by group
      _ = (s * a * (s : G)⁻¹) * (s * n * (s : G)⁻¹) := by rw [hs]
      _ = s * (a * n) * (s : G)⁻¹ := by group
      _ = s * (r * y * (r : G)⁻¹) * (s : G)⁻¹ := by rw [hr]
      _ = s * r * y * (s * (r : G))⁻¹ := by group

theorem comm_mem_of_two_elem {G : Type*} [Group G] [Finite G] {X N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) (hint : X ⊓ N = ⊥)
    {X₀ : Subgroup G} (hF : ∀ α : MulAut ↥X, (∀ y : X, (y : G) ∈ X₀ → α y = y) → α ^ 3 = 1)
    {t : G} (htXN : t ∈ normalizer ((X ⊔ N : Subgroup G) : Set G))
    (htN : t ∈ normalizer (N : Set G))
    {k : ℕ} (ht2 : t ^ (2 ^ k) = 1) (htX₀ : ∀ y ∈ X₀, t * y * t⁻¹ = y) :
    ∀ y ∈ X, t * y * t⁻¹ * y⁻¹ ∈ N := by
  set s : bothNorm X N := ⟨t, htXN, htN⟩
  set α := actHom hXN hint s
  have h3 : α ^ 3 = 1 := hF α fun y hy => by
    apply Subtype.ext
    show ((proj hXN hint ⟨t * y * t⁻¹, conj_mem_sup s.2 y.2⟩ : X) : G) = y
    exact proj_eq hXN hint _ y.2 (one_mem N) (by simp [htX₀ y hy])
  have h2 : α ^ (2 ^ k) = 1 := by
    rw [← map_pow]
    have : s ^ (2 ^ k) = 1 := Subtype.ext (by simpa [s] using ht2)
    rw [this, map_one]
  have hα : α = 1 := by
    have hd : orderOf α ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
    rw [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).gcd_eq_one,
      Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  intro y hy
  have hfix : ((proj hXN hint ⟨t * y * t⁻¹, conj_mem_sup s.2 hy⟩ : X) : G) = y := by
    have := congrArg (fun φ : MulAut ↥X => ((φ ⟨y, hy⟩ : X) : G)) hα
    simpa [α, actHom, actAut_apply] using this
  obtain ⟨n, hn, h⟩ := proj_spec hXN hint ⟨t * y * t⁻¹, conj_mem_sup s.2 hy⟩
  rw [hfix] at h
  have h' : y * n = t * y * t⁻¹ := h
  have : t * y * t⁻¹ * y⁻¹ = y * n * y⁻¹ := by rw [← h']
  rw [this]
  exact (mem_normalizer_iff.1 (hXN hy) n).1 hn

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G]
    {V : Subgroup G} {g : G} (h : ∀ v ∈ V, g * v * g⁻¹ ∈ V) :
    g ∈ normalizer (V : Set G) := by
  let f : V → V := fun v => ⟨g * v * g⁻¹, h v v.2⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext (by
    have := congrArg Subtype.val hab
    simpa [f] using this)
  have hs := Finite.injective_iff_surjective.1 hf
  rw [mem_normalizer_iff]
  intro v
  refine ⟨fun hv => h v hv, fun hv => ?_⟩
  obtain ⟨w, hw⟩ := hs ⟨g * v * g⁻¹, hv⟩
  have : (w : G) = v := by
    have := congrArg Subtype.val hw
    simpa [f] using this
  exact this ▸ w.2

theorem step_two {G : Type*} [Group G] [Finite G]
    {X O : Subgroup G} (hXO : X ≤ normalizer (O : Set G)) (hXs : IsSimpleGroup X)
    (h2 : 2 ∣ Nat.card X) (h3 : 3 ∣ Nat.card X) (hO3 : Nat.Coprime 3 (Nat.card O))
    (hNodd : Odd (Nat.card (⁅X, O⁆ : Subgroup G))) {t : G} (htO : t ∈ normalizer (O : Set G))
    (htW : t ∈ normalizer ((X ⊔ O : Subgroup G) : Set G)) :
    X ⊓ ⁅X, O⁆ = ⊥ ∧ t ∈ normalizer ((X ⊔ ⁅X, O⁆ : Subgroup G) : Set G) ∧
      t ∈ normalizer ((⁅X, O⁆ : Subgroup G) : Set G) := by
  set N : Subgroup G := ⁅X, O⁆ with hNdef
  set V : Subgroup G := X ⊔ N with hVdef
  set W : Subgroup G := X ⊔ O with hWdef
  have hXN : X ≤ normalizer (N : Set G) := normalizer_commutator_ge_left X O
  have hON : O ≤ normalizer (N : Set G) := normalizer_commutator_ge_right X O
  haveI := hXs
  have hint : X ⊓ N = ⊥ := by
    haveI := normal_subgroupOf_of_le_normalizer hXN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf X) with h | h
    · rw [subgroupOf_eq_bot] at h
      exact disjoint_iff.1 h.symm
    · rw [subgroupOf_eq_top] at h
      have hd := card_dvd_of_le h
      exact absurd (even_iff_two_dvd.2 (h2.trans hd)) (Nat.not_even_iff_odd.2 hNodd)
  have hVO : ∀ v ∈ V, ∀ o ∈ O, v * o * v⁻¹ * o⁻¹ ∈ N := by
    intro v hv o ho
    obtain ⟨a, ha, n, hn, rfl⟩ := exists_mul_of_mem_sup hXN hv
    have hno : n * o * n⁻¹ * o⁻¹ ∈ N := by
      have : o * n⁻¹ * o⁻¹ ∈ N := (mem_normalizer_iff.1 (hON ho) n⁻¹).1 (inv_mem hn)
      simpa [mul_assoc] using mul_mem hn this
    have h1 : a * (n * o * n⁻¹ * o⁻¹) * a⁻¹ ∈ N := (mem_normalizer_iff.1 (hXN ha) _).1 hno
    have h2 : a * o * a⁻¹ * o⁻¹ ∈ N := commutator_mem_commutator ha ho
    have := mul_mem h1 h2
    rw [show a * n * o * (a * n)⁻¹ * o⁻¹
        = a * (n * o * n⁻¹ * o⁻¹) * a⁻¹ * (a * o * a⁻¹ * o⁻¹) by group]
    exact this
  have hOV : O ≤ normalizer (V : Set G) := by
    intro o ho
    apply mem_normalizer_of_conj_mem
    intro v hv
    have hc := hVO v hv o ho
    have : o * v * o⁻¹ = (o * v * o⁻¹ * v⁻¹) * v := by group
    rw [this]
    refine mul_mem (mem_sup_right ?_) hv
    have h' : o * v * o⁻¹ * v⁻¹ = (v * o * v⁻¹ * o⁻¹)⁻¹ := by group
    rw [h']
    exact inv_mem hc
  have hVW : V ≤ W := by
    refine sup_le le_sup_left ?_
    rw [hNdef, commutator_le]
    intro a ha o ho
    exact mul_mem (mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right ho))
      (inv_mem (mem_sup_left ha)))
      (inv_mem (mem_sup_right ho))
  have hXt : ∀ y ∈ X, t * y * t⁻¹ ∈ V := by
    have hWV : W ≤ normalizer (V : Set G) := sup_le (le_trans le_sup_left le_normalizer) hOV
    haveI : (V.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer hWV
    let φ : X →* W ⧸ V.subgroupOf W :=
      (QuotientGroup.mk' (V.subgroupOf W)).comp
        { toFun := fun y => ⟨t * y * t⁻¹, (mem_normalizer_iff.1 htW y).1 (mem_sup_left y.2)⟩
          map_one' := by ext; simp
          map_mul' := fun y z => by ext; simp [mul_assoc] }
    have hφ : ∀ y : X, (φ y = 1 ↔ t * (y : G) * t⁻¹ ∈ V) := by
      intro y
      simp [φ, QuotientGroup.eq_one_iff, mem_subgroupOf]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hk | hk
    · exfalso
      have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hk
      have hd1 := card_dvd_of_injective φ hinj
      let ψ : O →* W ⧸ V.subgroupOf W :=
        (QuotientGroup.mk' (V.subgroupOf W)).comp (inclusion le_sup_right)
      have hψ : Function.Surjective ψ := by
        intro q
        obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨a, ha, o, ho, rfl⟩ := exists_mul_of_mem_sup hXO hw
        refine ⟨⟨o, ho⟩, ?_⟩
        show (QuotientGroup.mk (inclusion (le_sup_right : O ≤ W) ⟨o, ho⟩) : W ⧸ V.subgroupOf W) =
          QuotientGroup.mk ⟨a * o, hw⟩
        rw [QuotientGroup.eq_iff_div_mem, mem_subgroupOf]
        have : (((inclusion (le_sup_right : O ≤ W) ⟨o, ho⟩ : W) / ⟨a * o, hw⟩ : W) : G) = a⁻¹ := by
          simp only [div_eq_mul_inv, Subgroup.coe_mul, InvMemClass.coe_inv, coe_inclusion]
          group
        rw [this]
        exact mem_sup_left (inv_mem ha)
      have hd2 := card_dvd_of_surjective hψ
      have h3O : 3 ∣ Nat.card O := h3.trans (hd1.trans hd2)
      have := Nat.Coprime.eq_one_of_dvd hO3 h3O
      omega
    · intro y hy
      exact (hφ ⟨y, hy⟩).1 (by rw [← MonoidHom.mem_ker, hk]; trivial)
  have htN : t ∈ normalizer (N : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro n hn
    have hmap : N.map (MulAut.conj t).toMonoidHom ≤ N := by
      rw [hNdef, map_commutator, commutator_le]
      rintro _ ⟨y, hy, rfl⟩ _ ⟨o, ho, rfl⟩
      have := hVO _ (hXt y hy) _ ((mem_normalizer_iff.1 htO o).1 ho)
      simpa [commutatorElement_def, MulAut.conj_apply] using this
    exact hmap (mem_map_of_mem _ hn)
  refine ⟨hint, ?_, htN⟩
  apply mem_normalizer_of_conj_mem
  intro v hv
  obtain ⟨a, ha, n, hn, rfl⟩ := exists_mul_of_mem_sup hXN hv
  have : t * (a * n) * t⁻¹ = (t * a * t⁻¹) * (t * n * t⁻¹) := by group
  rw [this]
  exact mul_mem (hXt a ha) (mem_sup_right ((mem_normalizer_iff.1 htN n).1 hn))

end CFSG.GGQ2Prime
