module

public import CFSG.Quasithin.Recognition.M12AscEx
public import CFSG.Dihedral.DisconnectedInvolutionGraph.StrongEmbeddingFusion

public section

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G]

structure E8Data (z : G) (F : Subgroup G) : Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  card : Nat.card F = 8
  elem : ∀ x ∈ F, ∀ y ∈ F, x * x = 1 ∧ x * y = y * x
  z_mem : z ∈ F
  H_norm : ∀ h : G, h * z = z * h → h ∈ Subgroup.normalizer (F : Set G)
  C_F : ∀ g : G, (∀ f ∈ F, g * f = f * g) → g ∈ F
  trans : ∀ e ∈ F, e ≠ 1 → ∃ m ∈ Subgroup.normalizer (F : Set G), m * z * m⁻¹ = e
  sc : ∀ x : G, x * z * x⁻¹ ∈ Subgroup.normalizer (F : Set G) → x * z * x⁻¹ ∈ F

namespace E8Data

variable {z : G} {F : Subgroup G}

theorem sc1 (h : E8Data z F) {e : G} (he : e ∈ F) (he1 : e ≠ 1) {x : G} (hx : x * e * x⁻¹ ∈ F) :
    x ∈ Subgroup.normalizer (F : Set G) := by
  obtain ⟨m', hm', hm'e⟩ := h.trans e he he1
  have he' : x * e * x⁻¹ ≠ 1 := by
    intro e'
    apply he1
    calc e = x⁻¹ * (x * e * x⁻¹) * x := by group
      _ = 1 := by rw [e']; group
  obtain ⟨m'', hm'', hm''e⟩ := h.trans _ hx he'
  have hc : (m''⁻¹ * x * m') * z = z * (m''⁻¹ * x * m') := by
    calc (m''⁻¹ * x * m') * z = m''⁻¹ * x * (m' * z * m'⁻¹) * m' := by group
      _ = m''⁻¹ * x * e * m' := by rw [hm'e]
      _ = m''⁻¹ * (x * e * x⁻¹) * (x * m') := by group
      _ = m''⁻¹ * (m'' * z * m''⁻¹) * (x * m') := by rw [hm''e]
      _ = z * (m''⁻¹ * x * m') := by group
  have hcM := h.H_norm _ hc
  have : x = m'' * (m''⁻¹ * x * m') * m'⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem hm'' hcM) (inv_mem hm')

theorem sc2 (h : E8Data z F) {e : G} (he : e ∈ F) (he1 : e ≠ 1) {x : G}
    (hx : x * e * x⁻¹ ∈ Subgroup.normalizer (F : Set G)) : x * e * x⁻¹ ∈ F := by
  obtain ⟨m', hm', hm'e⟩ := h.trans e he he1
  have heq : (x * m') * z * (x * m')⁻¹ = x * e * x⁻¹ := by rw [← hm'e]; group
  have := h.sc (x * m') (by rw [heq]; exact hx)
  rwa [heq] at this

theorem cent_of_mem_F (h : E8Data z F) {j : G} (hj : j ∈ F) (hj1 : j ≠ 1) {g : G}
    (hg : g * j = j * g) : g ∈ Subgroup.normalizer (F : Set G) := by
  obtain ⟨m, hm, hme⟩ := h.trans j hj hj1
  have hc : (m⁻¹ * g * m) * z = z * (m⁻¹ * g * m) := by
    calc (m⁻¹ * g * m) * z = m⁻¹ * g * (m * z * m⁻¹) * m := by group
      _ = m⁻¹ * (g * j) * m := by rw [hme]; group
      _ = m⁻¹ * (j * g) * m := by rw [hg]
      _ = z * (m⁻¹ * g * m) := by
        calc m⁻¹ * (j * g) * m = (m⁻¹ * j * m) * (m⁻¹ * g * m) := by group
          _ = z * (m⁻¹ * g * m) := by
            rw [← hme]; group
  have hcM := h.H_norm _ hc
  have : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem hm hcM) (inv_mem hm)

theorem two_elems_of_card_two {K : Type*} [Group K] (hK : Nat.card K = 2) {a : K} (ha : a ≠ 1)
    (x : K) : x = 1 ∨ x = a := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  by_contra hcon
  push Not at hcon
  have h3 : ({1, a, x} : Set K).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hcon.2)]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm ha, Ne.symm hcon.1⟩
  have h4 := Set.ncard_le_ncard (Set.subset_univ ({1, a, x} : Set K)) (Set.toFinite _)
  rw [Set.ncard_univ] at h4
  omega

theorem exists_ne_one_ne_of_card_four {K : Type*} [Group K] (hK : Nat.card K = 4) (a : K) :
    ∃ b : K, b ≠ 1 ∧ b ≠ a := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  by_contra hcon
  push Not at hcon
  have hsub : (Set.univ : Set K) ⊆ {1, a} := fun x _ => by
    by_cases hx : x = 1
    · simp [hx]
    · simp [hcon x hx]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, a} : Set K).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : K) ({a} : Set K)
    rw [Set.ncard_singleton] at this
    exact this
  rw [Set.ncard_univ] at h1
  omega

theorem cent_of_mem_M [Finite G] (h : E8Data z F) {j : G}
    (hjM : j ∈ Subgroup.normalizer (F : Set G)) (hjF : j ∉ F) (hj2 : j * j = 1) {g : G}
    (hg : g * j = j * g) : g ∈ Subgroup.normalizer (F : Set G) := by
  classical
  have hconj : ∀ f : G, f ∈ F ↔ j * f * j⁻¹ ∈ F := Subgroup.mem_normalizer_iff.1 hjM
  have hFc : ∀ a b : F, a * b = b * a := fun a b => Subtype.ext (h.elem a a.2 b b.2).2
  have hFs : ∀ a : F, a * a = 1 := fun a => Subtype.ext (h.elem a a.2 a a.2).1
  let α : F →* F := MonoidHom.mk' (fun f => ⟨j * f * j⁻¹, (hconj f).1 f.2⟩) (by
    intro a b
    apply Subtype.ext
    show j * ((a : G) * b) * j⁻¹ = (j * a * j⁻¹) * (j * b * j⁻¹)
    group)
  have hαc : ∀ f : F, ((α f : F) : G) = j * f * j⁻¹ := fun f => rfl
  have hαα : ∀ f : F, α (α f) = f := by
    intro f
    apply Subtype.ext
    rw [hαc, hαc]
    calc j * (j * (f : G) * j⁻¹) * j⁻¹ = (j * j) * (f : G) * (j * j)⁻¹ := by group
      _ = f := by rw [hj2]; group
  let φ : F →* F := MonoidHom.mk' (fun x => x * α x) (by
    intro a b
    rw [map_mul]
    calc a * b * (α a * α b) = a * (b * α a) * α b := by group
      _ = a * (α a * b) * α b := by rw [hFc b (α a)]
      _ = (a * α a) * (b * α b) := by group)
  have hφ : ∀ x : F, φ x = x * α x := fun x => rfl
  have hker : ∀ x : F, φ x = 1 ↔ (x : G) * j = j * x := by
    intro x
    rw [hφ]
    constructor
    · intro h1
      have h2 : α x = x := by
        have : α x = x⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]; exact inv_eq_of_mul_eq_one_right (hFs x)
      have h3 := congrArg Subtype.val h2
      rw [hαc] at h3
      calc (x : G) * j = (j * x * j⁻¹) * j := by rw [h3]
        _ = j * x := by group
    · intro h1
      have h2 : α x = x := by
        apply Subtype.ext
        rw [hαc]
        calc j * (x : G) * j⁻¹ = (x * j) * j⁻¹ := by rw [h1]
          _ = x := by group
      rw [h2]; exact hFs x
  have hφφ : ∀ x : F, φ (φ x) = 1 := by
    intro x
    rw [hφ (φ x), hφ x, map_mul, hαα]
    calc x * α x * (α x * x) = x * (α x * α x) * x := by group
      _ = 1 := by rw [hFs, mul_one, hFs]
  have hmul : Nat.card φ.ker * Nat.card φ.range = 8 := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, h.card] at h1
    exact h1
  have hrle : Nat.card φ.range ≤ Nat.card φ.ker :=
    Subgroup.card_le_of_le (fun y hy => by
      obtain ⟨x, rfl⟩ := hy
      exact hφφ x)
  have hkne : φ.ker ≠ ⊤ := by
    intro htop
    apply hjF
    apply h.C_F j
    intro f hf
    have hf1 : φ ⟨f, hf⟩ = 1 := by rw [← MonoidHom.mem_ker, htop]; trivial
    exact ((hker ⟨f, hf⟩).1 hf1).symm
  have hlt : Nat.card φ.ker < 8 := by
    have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hkne)
    rwa [Subgroup.card_top, h.card] at this
  have hkcard : Nat.card φ.ker = 4 ∧ Nat.card φ.range = 2 := by
    have hdvd : Nat.card φ.ker ∣ 8 := ⟨_, hmul.symm⟩
    generalize Nat.card φ.ker = a at *
    generalize Nat.card φ.range = b at *
    interval_cases a <;> omega
  set U : Subgroup G := φ.ker.map F.subtype with hU
  have hUF : U ≤ F := Subgroup.map_subtype_le _
  have hUmem : ∀ x : G, x ∈ U ↔ x ∈ F ∧ x * j = j * x := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hker y).1 hy⟩
    · rintro ⟨hxF, hxj⟩
      exact ⟨⟨x, hxF⟩, (hker ⟨x, hxF⟩).2 hxj, rfl⟩
  have hUcard : Nat.card U = 4 := by
    rw [← hkcard.1]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective φ.ker F.subtype F.subtype_injective)).symm
  have hr1 : φ.range ≠ ⊥ := by
    intro hbot
    have := hkcard.2
    rw [hbot, Subgroup.card_bot] at this
    omega
  obtain ⟨u0, hu0ne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hr1
  obtain ⟨x0, hx0⟩ := u0.2
  have hrange : ∀ w ∈ φ.range, w = 1 ∨ w = (u0 : F) := by
    intro w hw
    have := two_elems_of_card_two hkcard.2 hu0ne ⟨w, hw⟩
    rcases this with e | e
    · left; exact congrArg Subtype.val e
    · right; exact congrArg Subtype.val e
  have hu0U : ((u0 : F) : G) ∈ U := by
    rw [hUmem]
    refine ⟨(u0 : F).2, (hker u0).1 ?_⟩
    rw [← hx0]; exact hφφ x0
  have hu0G : ((u0 : F) : G) ≠ 1 := fun e => hu0ne (Subtype.ext (Subtype.ext e))
  have hUJ : ∀ x ∈ U, x ∈ Subgroup.centralizer ({j} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 ((hUmem x).1 hx).2
  set J : Subgroup G := Subgroup.centralizer ({j} : Set G) with hJ
  set E : Subgroup J := U.subgroupOf J with hE
  have hEmem : ∀ x : J, x ∈ E ↔ (x : G) ∈ U := fun x => Subgroup.mem_subgroupOf
  have hJc : ∀ x : J, (x : G) * j = j * x := fun x =>
    Subgroup.mem_centralizer_singleton_iff.1 x.2
  have hinvcomm : ∀ x : G, x * j = j * x → x⁻¹ * j = j * x⁻¹ := by
    intro x hxj
    calc x⁻¹ * j = x⁻¹ * (j * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * j) * x⁻¹ := by rw [hxj]
      _ = j * x⁻¹ := by group
  have hnormU : ∀ x : G, x ∈ Subgroup.normalizer (F : Set G) → x * j = j * x →
      ∀ u ∈ U, x * u * x⁻¹ ∈ U := by
    intro x hx hxj u hu
    rw [hUmem]
    refine ⟨(Subgroup.mem_normalizer_iff.1 hx u).1 (hUF hu), ?_⟩
    have hu' := ((hUmem u).1 hu).2
    calc x * u * x⁻¹ * j = x * u * (x⁻¹ * j) := by group
      _ = x * u * (j * x⁻¹) := by rw [hinvcomm x hxj]
      _ = x * (u * j) * x⁻¹ := by group
      _ = x * (j * u) * x⁻¹ := by rw [hu']
      _ = (x * j) * u * x⁻¹ := by group
      _ = (j * x) * u * x⁻¹ := by rw [hxj]
      _ = j * (x * u * x⁻¹) := by group
  have hMofnorm : ∀ n : J, n ∈ Subgroup.normalizer (E : Set J) →
      (n : G) ∈ Subgroup.normalizer (F : Set G) := by
    intro n hn
    obtain ⟨b, hb1, -⟩ := exists_ne_one_ne_of_card_four hUcard (1 : U)
    have hbJ : (b : G) ∈ J := hUJ _ b.2
    have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨(b : G), hbJ⟩).1 ((hEmem _).2 b.2)
    have h2 : (n : G) * (b : G) * (n : G)⁻¹ ∈ U := (hEmem _).1 h1
    exact h.sc1 (hUF b.2) (fun e => hb1 (Subtype.ext e)) (hUF h2)
  have hinv : ∀ e ∈ E, e ≠ 1 → e * e = 1 := by
    intro e he _
    have heF := hUF ((hEmem e).1 he)
    exact Subtype.ext (h.elem _ heF _ heF).1
  have hTI : ∀ (x w : J), w ∈ E → w ≠ 1 → x * w * x⁻¹ ∈ E →
      x ∈ Subgroup.normalizer (E : Set J) := by
    intro x w hw hw1 hxw
    have hwU := (hEmem w).1 hw
    have hxwU : (x : G) * w * (x : G)⁻¹ ∈ U := (hEmem _).1 hxw
    have hxM := h.sc1 (hUF hwU) (fun e => hw1 (Subtype.ext e)) (hUF hxwU)
    refine Subgroup.mem_normalizer_iff.2 (fun k => ⟨fun hk => ?_, fun hk => ?_⟩)
    · exact (hEmem _).2 (hnormU x hxM (hJc x) k ((hEmem k).1 hk))
    · have hkU : (x : G) * k * (x : G)⁻¹ ∈ U := (hEmem _).1 hk
      have := hnormU (x : G)⁻¹ (inv_mem hxM) (hinvcomm _ (hJc x)) _ hkU
      rw [show (x : G)⁻¹ * ((x : G) * k * (x : G)⁻¹) * ((x : G)⁻¹)⁻¹ = k by group] at this
      exact (hEmem k).2 this
  have hsc : ∀ e ∈ E, e ≠ 1 → ∀ x : J, x * e * x⁻¹ ∈ Subgroup.normalizer (E : Set J) →
      x * e * x⁻¹ ∈ E := by
    intro e he he1 x hxe
    have heU := (hEmem e).1 he
    have hnM := hMofnorm _ hxe
    have hF' : (x : G) * e * (x : G)⁻¹ ∈ F :=
      h.sc2 (hUF heU) (fun e' => he1 (Subtype.ext e')) hnM
    exact (hEmem _).2 ((hUmem _).2 ⟨hF', hJc (x * e * x⁻¹)⟩)
  by_cases hN : Subgroup.normalizer (E : Set J) = ⊤
  · have hgJ : g ∈ J := Subgroup.mem_centralizer_singleton_iff.2 hg
    have : (⟨g, hgJ⟩ : J) ∈ Subgroup.normalizer (E : Set J) := by rw [hN]; trivial
    exact hMofnorm _ this
  · exfalso
    have htr := transitive_of_TI_strongly_closed E hinv hTI hsc hN
    obtain ⟨b, hb1, hbu⟩ := exists_ne_one_ne_of_card_four hUcard (⟨((u0 : F) : G), hu0U⟩ : U)
    have hbJ : (b : G) ∈ J := hUJ _ b.2
    obtain ⟨m, hm, hmeq⟩ := htr ⟨((u0 : F) : G), hUJ _ hu0U⟩ ((hEmem _).2 hu0U)
      (fun e => hu0G (congrArg (fun w : J => (w : G)) e)) ⟨(b : G), hbJ⟩ ((hEmem _).2 b.2)
      (fun e => hb1 (Subtype.ext (congrArg (fun w : J => (w : G)) e)))
    have hmM := hMofnorm m hm
    have hmj : (m : G) * j = j * m := hJc m
    have hmeq' : (m : G) * ((u0 : F) : G) * (m : G)⁻¹ = (b : G) := congrArg Subtype.val hmeq
    have hu0eq : ((u0 : F) : G) = (x0 : G) * (j * x0 * j⁻¹) := by
      rw [← hx0, hφ]; rfl
    have hx'F : (m : G) * x0 * (m : G)⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.1 hmM x0).1 x0.2
    have hmjm : (m : G) * j * (m : G)⁻¹ = j := by rw [hmj]; group
    have hbeq : (b : G) = ((m : G) * x0 * (m : G)⁻¹) *
        (j * ((m : G) * x0 * (m : G)⁻¹) * j⁻¹) := by
      rw [← hmeq', hu0eq]
      calc (m : G) * ((x0 : G) * (j * x0 * j⁻¹)) * (m : G)⁻¹
          = ((m : G) * x0 * (m : G)⁻¹) * (((m : G) * j * (m : G)⁻¹) * ((m : G) * x0 * (m : G)⁻¹) *
              ((m : G) * j * (m : G)⁻¹)⁻¹) := by group
        _ = _ := by rw [hmjm]
    have hbrange : (⟨(b : G), hUF b.2⟩ : F) ∈ φ.range :=
      ⟨⟨_, hx'F⟩, Subtype.ext hbeq.symm⟩
    rcases hrange _ hbrange with e | e
    · exact hb1 (Subtype.ext (congrArg (fun w : F => (w : G)) e))
    · exact hbu (Subtype.ext (congrArg (fun w : F => (w : G)) e))

end E8Data

theorem asc_false_of_strongly_closed_E8 [Finite G] [IsSimpleGroup G]
    {z : G} (hz : orderOf z = 2)
    (F : Subgroup G) (hFcard : Nat.card F = 8)
    (hFea : ∀ x ∈ F, ∀ y ∈ F, x * x = 1 ∧ x * y = y * x)
    (hzF : z ∈ F)
    (hFH : ∀ h : G, h * z = z * h → h ∈ Subgroup.normalizer (F : Set G))
    (hCF : ∀ g : G, (∀ f ∈ F, g * f = f * g) → g ∈ F)
    (htrans : ∀ e ∈ F, e ≠ 1 → ∃ m ∈ Subgroup.normalizer (F : Set G), m * z * m⁻¹ = e)
    (hsc : ∀ x : G, x * z * x⁻¹ ∈ Subgroup.normalizer (F : Set G) → x * z * x⁻¹ ∈ F)
    {t : G} (ht : orderOf t = 2) (htz : ¬ IsConj z t) : False := by
  classical
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, pow_two] at this
  have hz1 : z ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hz
    omega
  have hdata : E8Data z F := ⟨hz2, hz1, hFcard, hFea, hzF, hFH, hCF, htrans, hsc⟩
  set M := Subgroup.normalizer (F : Set G) with hM
  have hFM : F ≤ M := Subgroup.le_normalizer
  have hMtop : M ≠ ⊤ := by
    intro hMt
    have hFn : F.Normal := Subgroup.normalizer_eq_top_iff.1 hMt
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal F with hb | htop
    · have := hzF
      rw [hb, Subgroup.mem_bot] at this
      exact hz1 this
    · have hcomm : ∀ a b : G, a * b = b * a := fun a b =>
        (hFea a (by rw [htop]; trivial) b (by rw [htop]; trivial)).2
      have hnorm : (Subgroup.zpowers z).Normal := ⟨fun n hn g => by
        rw [show g * n * g⁻¹ = n by
          calc g * n * g⁻¹ = (n * g) * g⁻¹ := by rw [hcomm g n]
            _ = n := by group]
        exact hn⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers z) with hb | htop2
      · have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
        rw [hb, Subgroup.mem_bot] at this
        exact hz1 this
      · have h1 : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
        rw [htop2, Subgroup.card_top] at h1
        have h2 : Nat.card F = Nat.card G := by rw [htop, Subgroup.card_top]
        omega
  have hK : ∀ j : G, j * j = 1 → j ≠ 1 → j ∈ M → ∀ g : G, g * j = j * g → g ∈ M := by
    intro j hj2 hj1 hjM g hg
    by_cases hjF : j ∈ F
    · exact hdata.cent_of_mem_F hjF hj1 hg
    · exact hdata.cent_of_mem_M hjM hjF hj2 hg
  by_cases hconn : (CFSG.Open.disconnectedInvolutionCommutingGraph G).Preconnected
  · have hall : ∀ a : {x : G // orderOf x = 2}, (a : G) ∈ M := by
      intro a
      have hreach := hconn ⟨z, hz⟩ a
      rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
      induction hreach with
      | refl => exact hFM hzF
      | @tail b c _ hadj ih =>
        obtain ⟨-, hbc⟩ := (CFSG.DisconnectedInvolutionGraph.Helpers.involutionGraph_adj_iff b c).1
          hadj
        have hb2 : (b : G) * b = 1 := by
          have := pow_orderOf_eq_one (b : G)
          rwa [b.2, pow_two] at this
        have hb1 : (b : G) ≠ 1 := by
          intro e
          have := b.2
          rw [e, orderOf_one] at this
          omega
        exact hK b hb2 hb1 ih c hbc.symm
    apply hMtop
    have hnc : Subgroup.normalClosure ({z} : Set G) = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({z} : Set G))
        with hb | htop
      · exfalso
        have : z ∈ Subgroup.normalClosure ({z} : Set G) := Subgroup.subset_normalClosure rfl
        rw [hb, Subgroup.mem_bot] at this
        exact hz1 this
      · exact htop
    rw [eq_top_iff, ← hnc]
    unfold Subgroup.normalClosure
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    rw [Set.mem_singleton_iff] at ha
    rw [ha] at hconj
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    have hord : orderOf x = 2 := by
      rw [← hc]
      have := (MulAut.conj c).orderOf_eq z
      rw [MulAut.conj_apply] at this
      rw [this]; exact hz
    exact hall ⟨x, hord⟩
  · obtain ⟨S, hS⟩ :=
      CFSG.DisconnectedInvolutionGraph.Helpers.disconnected_exists_stronglyEmbedded hconn
    obtain ⟨g, hg⟩ :=
      CFSG.DisconnectedInvolutionGraph.Helpers.stronglyEmbedded_all_involutions_conjugate S hS
        ⟨z, hz⟩ ⟨t, ht⟩
    apply htz
    refine isConj_iff.2 ⟨g, ?_⟩
    have := congrArg Subtype.val hg
    simpa [CFSG.DisconnectedInvolutionGraph.Helpers.conjugateInvolution, MulAut.conj_apply]
      using this

end CFSG.Quasithin
