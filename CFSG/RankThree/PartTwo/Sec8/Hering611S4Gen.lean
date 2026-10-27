module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S4Tab
public import CFSG.RankThree.PartTwo.Sec18.Components
public import CFSG.RankThree.PartTwo.Sec18.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

open Subgroup CFSG CFSG.RankThree.PartTwo.Sec18

@[simp] theorem prodG_nil (Rg : ℕ → Gp) : prodG Rg [] = 1 := rfl

@[simp] theorem prodG_cons (Rg : ℕ → Gp) (i : ℕ) (l : List ℕ) :
    prodG Rg (i :: l) = Rg i * prodG Rg l := by
  simp [prodG]

theorem prodG_mem {Rg : ℕ → Gp} {K : Subgroup Gp} {l : List ℕ} (h : ∀ i ∈ l, Rg i ∈ K) :
    prodG Rg l ∈ K := by
  induction l with
  | nil => exact K.one_mem
  | cons i l ih =>
    rw [prodG_cons]
    exact K.mul_mem (h i List.mem_cons_self) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem Ksub_mem {Rg : ℕ → Gp} {gi : List ℕ} {r : ℕ} (h : r ∈ gi) : Rg r ∈ Ksub Rg gi :=
  subset_closure ⟨r, h, rfl⟩

theorem Ksub_le {Rg : ℕ → Gp} {gi : List ℕ} {K : Subgroup Gp} (h : ∀ r ∈ gi, Rg r ∈ K) :
    Ksub Rg gi ≤ K := by
  rw [Ksub, closure_le]
  rintro _ ⟨r, hr, rfl⟩
  exact h r hr

theorem Ksub_append (Rg : ℕ → Gp) (gi gj : List ℕ) :
    Ksub Rg (gi ++ gj) = Ksub Rg gi ⊔ Ksub Rg gj := by
  simp only [Ksub, ← Subgroup.closure_union, ← Set.image_union]
  congr 2
  ext r
  simp [List.mem_append]

section General

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_gens [Finite G] {V : Subgroup G} {S : Set G}
    (hS : closure S = V) {x : G} (h : ∀ s ∈ S, x * s * x⁻¹ ∈ V) :
    x ∈ normalizer (V : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have hle : V.map (MulAut.conj x).toMonoidHom ≤ V := by
    calc V.map (MulAut.conj x).toMonoidHom = (closure S).map (MulAut.conj x).toMonoidHom := by
          rw [hS]
      _ = closure ((MulAut.conj x).toMonoidHom '' S) := MonoidHom.map_closure _ _
      _ ≤ V := by
          rw [closure_le]
          rintro _ ⟨s, hs, rfl⟩
          exact h s hs
  exact eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective (MulAut.conj x).injective])

theorem conj_mem_of_mem_normalizer {V : Subgroup G} {x : G} (hx : x ∈ normalizer (V : Set G))
    {s : G} (hs : s ∈ V) : x * s * x⁻¹ ∈ V :=
  ((mem_normalizer_iff.1 hx) s).1 hs

theorem normalizer_inf_eq [Finite G] {P V M C : Subgroup G} {t : G} {S : Set G}
    (hS : closure S = V) (hVcard : Nat.card V = 16) (ht : t ∈ V) (ht1 : t ≠ 1)
    (hMP : M ≤ P) (hMN : M ≤ normalizer (V : Set G)) (hMcard : Nat.card M = 2880)
    (hC : C = P ⊓ centralizer {t})
    (hcount : Set.ncard {x | x ∈ C ∧ ∀ s ∈ S, x * s * x⁻¹ ∈ V} ≤ 192) :
    normalizer (V : Set G) ⊓ P = M := by
  set N : Subgroup G := normalizer (V : Set G) ⊓ P with hN
  have hMle : M ≤ N := le_inf hMN hMP
  have horbit := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card N t
  have hcls : (CFSG.Sporadic.SmallOddCore.conjClass N t).ncard ≤ 15 := by
    have hsub : CFSG.Sporadic.SmallOddCore.conjClass N t ⊆ (V : Set G) \ {1} := by
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨conj_mem_of_mem_normalizer hg.1 ht, fun h1 => ht1 ?_⟩
      have : g * t * g⁻¹ = 1 := h1
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
    have h1 : ((V : Set G) \ {1}).ncard = 15 := by
      rw [Set.ncard_diff_singleton_of_mem V.one_mem, ← Nat.card_coe_set_eq]
      exact (congrArg (· - 1) hVcard)
    calc (CFSG.Sporadic.SmallOddCore.conjClass N t).ncard ≤ ((V : Set G) \ {1}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 15 := h1
  have hstab : Nat.card ↥(N ⊓ centralizer ({t} : Set G)) ≤ 192 := by
    have hsub : ((N ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ⊆
        {x | x ∈ C ∧ ∀ s ∈ S, x * s * x⁻¹ ∈ V} := by
      intro x hx
      refine ⟨by rw [hC]; exact ⟨hx.1.2, hx.2⟩, fun s hs => ?_⟩
      exact conj_mem_of_mem_normalizer hx.1.1 (hS ▸ subset_closure hs)
    calc Nat.card ↥(N ⊓ centralizer ({t} : Set G))
        = ((N ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G).ncard :=
          (Nat.card_coe_set_eq _)
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 192 := hcount
  have hNcard : Nat.card N ≤ 2880 := by
    rw [← horbit]
    calc _ ≤ 15 * 192 := Nat.mul_le_mul hcls hstab
      _ = 2880 := by norm_num
  exact (eq_of_le_of_card_ge hMle (by rw [hMcard]; exact hNcard)).symm

end General

section Elem

variable {G : Type*} [Group G]

theorem isElemAbelian_closure {S : Set G} {p : ℕ} (hcomm : S.Pairwise Commute)
    (hp : ∀ a ∈ S, a ^ p = 1) : CFSG.Open.IsElemAbelian p (closure S) := by
  haveI := isMulCommutative_closure hcomm
  refine ⟨inferInstance, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hp x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := Subtype.ext_iff.1
      (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : closure S) ⟨y, hy⟩)
    rw [hc.mul_pow, ihx, ihy, mul_one]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem mem_map_conj_iff {K : Subgroup G} {g x : G} :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  rw [mem_map_equiv]
  rfl

theorem conj_mem_map {K : Subgroup G} {g y : G} (hy : y ∈ K) :
    g * y * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom :=
  ⟨y, hy, rfl⟩

end Elem

section Conj

variable {G : Type*} [Group G]

@[expose] def cj (g : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj g).toMonoidHom

theorem mem_cj {K : Subgroup G} {g x : G} : x ∈ cj g K ↔ g⁻¹ * x * g ∈ K :=
  mem_map_conj_iff

theorem conj_mem_cj {K : Subgroup G} {g y : G} (hy : y ∈ K) : g * y * g⁻¹ ∈ cj g K :=
  conj_mem_map hy

theorem cj_mono {K L : Subgroup G} (g : G) (h : K ≤ L) : cj g K ≤ cj g L :=
  map_mono h

theorem card_cj (g : G) (K : Subgroup G) : Nat.card (cj g K) = Nat.card K :=
  card_map_of_injective (MulAut.conj g).injective

theorem cj_le_of_mem {P K : Subgroup G} {g : G} (hg : g ∈ P) (hK : K ≤ P) : cj g K ≤ P := by
  rintro _ ⟨y, hy, rfl⟩
  exact P.mul_mem (P.mul_mem hg (hK hy)) (P.inv_mem hg)

theorem normalizer_cj (g : G) (K : Subgroup G) :
    normalizer ((cj g K : Subgroup G) : Set G) = cj g (normalizer (K : Set G)) := by
  ext x
  rw [mem_cj, mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h n
    have := h (g * n * g⁻¹)
    rw [mem_cj, mem_cj] at this
    simpa [mul_assoc] using this
  · intro h n
    rw [mem_cj, mem_cj]
    have := h (g⁻¹ * n * g)
    simpa [mul_assoc] using this

theorem cj_inf_of_mem {P K : Subgroup G} {g : G} (hg : g ∈ P) :
    cj g K ⊓ P = cj g (K ⊓ P) := by
  ext x
  rw [mem_inf, mem_cj, mem_cj, mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simpa [mul_assoc] using P.mul_mem (P.mul_mem (P.inv_mem hg) h2) hg⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simpa [mul_assoc] using P.mul_mem (P.mul_mem hg h2) (P.inv_mem hg)⟩

theorem normalizer_cj_inf {P V M : Subgroup G} {g : G} (hg : g ∈ P)
    (hN : normalizer (V : Set G) ⊓ P = M) :
    normalizer ((cj g V : Subgroup G) : Set G) ⊓ P = cj g M := by
  rw [normalizer_cj, cj_inf_of_mem hg, hN]

theorem inSubgroup_perfectResidual_cj {M H : Subgroup G} (g : G)
    (hH : inSubgroup perfectResidual M = H) :
    inSubgroup perfectResidual (cj g M) = cj g H := by
  rw [cj, ← CFSG.RankThree.PartTwo.map_inSubgroup_perfectResidual (MulAut.conj g) M, hH]
  rfl

theorem isElemAbelian_cj {K : Subgroup G} {p : ℕ} (h : CFSG.Open.IsElemAbelian p K) (g : G) :
    CFSG.Open.IsElemAbelian p (cj g K) := by
  haveI := h.1
  refine ⟨inferInstanceAs (IsMulCommutative (K.map (MulAut.conj g).toMonoidHom)), fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hx
  have := h.2 y hy
  change (g * y * g⁻¹) ^ p = 1
  rw [conj_pow, this]
  simp

end Conj

theorem Ksub_conj4 {Rg : ℕ → Gp} {g : Gp} {a1 a2 a3 a4 v1 v2 v3 v4 : ℕ}
    (h1 : Rg a1 = g * Rg v1 * g⁻¹) (h2 : Rg a2 = g * Rg v2 * g⁻¹)
    (h3 : Rg a3 = g * Rg v3 * g⁻¹) (h4 : Rg a4 = g * Rg v4 * g⁻¹) :
    Ksub Rg [a1, a2, a3, a4] = cj g (Ksub Rg [v1, v2, v3, v4]) := by
  rw [cj, Ksub, Ksub, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases hr with rfl | rfl | rfl | rfl
    exacts [⟨Rg v1, ⟨v1, Or.inl rfl, rfl⟩, h1.symm⟩,
      ⟨Rg v2, ⟨v2, Or.inr (Or.inl rfl), rfl⟩, h2.symm⟩,
      ⟨Rg v3, ⟨v3, Or.inr (Or.inr (Or.inl rfl)), rfl⟩, h3.symm⟩,
      ⟨Rg v4, ⟨v4, Or.inr (Or.inr (Or.inr rfl)), rfl⟩, h4.symm⟩]
  · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
    rcases hr with rfl | rfl | rfl | rfl
    exacts [⟨a1, Or.inl rfl, h1⟩, ⟨a2, Or.inr (Or.inl rfl), h2⟩,
      ⟨a3, Or.inr (Or.inr (Or.inl rfl)), h3⟩, ⟨a4, Or.inr (Or.inr (Or.inr rfl)), h4⟩]

section Pull

variable {G : Type*} [Group G] {P : Subgroup G}

theorem subgroupOf_le_subgroupOf {X Y : Subgroup G} (h : X ≤ Y) :
    X.subgroupOf P ≤ Y.subgroupOf P := fun _ hx => h hx

theorem card_subgroupOf_of_le {X : Subgroup G} (hX : X ≤ P) :
    Nat.card (X.subgroupOf P) = Nat.card X :=
  Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv

theorem isElemAbelian_subgroupOf {X : Subgroup G} {p : ℕ} (hX : X ≤ P)
    (h : CFSG.Open.IsElemAbelian p X) : CFSG.Open.IsElemAbelian p (X.subgroupOf P) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have := h.1.is_comm.comm (⟨a.1.1, a.2⟩ : X) ⟨b.1.1, b.2⟩
    exact Subtype.ext (Subtype.ext (congrArg (fun z : X => (z : G)) this))
  · have h2 := h.2 (x : G) hx
    exact Subtype.ext (by simpa using h2)

theorem normalizer_subgroupOf {X : Subgroup G} (hX : X ≤ P) :
    normalizer ((X.subgroupOf P : Subgroup P) : Set P) =
      (normalizer (X : Set G)).subgroupOf P := by
  ext x
  simp only [mem_subgroupOf, mem_normalizer_iff, SetLike.mem_coe]
  constructor
  · intro h n
    constructor
    · intro hn
      have := (h ⟨n, hX hn⟩).1 hn
      simpa using this
    · intro hn
      have hnP : n ∈ P := by
        have h1 : (x : G)⁻¹ * ((x : G) * n * (x : G)⁻¹) * (x : G) ∈ P :=
          P.mul_mem (P.mul_mem (P.inv_mem x.2) (hX hn)) x.2
        simpa [mul_assoc] using h1
      have := (h ⟨n, hnP⟩).2 (by simpa using hn)
      simpa using this
  · intro h n
    have h1 := h (n : G)
    constructor
    · intro hn
      simpa using h1.1 hn
    · intro hn
      simpa using h1.2 (by simpa using hn)

theorem centralizer_inf_subgroupOf {X : Subgroup G} (y : P) :
    centralizer ({y} : Set P) ⊓ X.subgroupOf P =
      (centralizer ({(y : G)} : Set G) ⊓ X).subgroupOf P := by
  ext x
  simp only [mem_inf, mem_subgroupOf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa using congrArg (fun z : P => (z : G)) h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Subtype.ext (by simpa using h1), h2⟩

theorem inSubgroup_perfectResidual_subgroupOf {N H : Subgroup G} (hN : N ≤ P)
    (hH : inSubgroup perfectResidual N = H) :
    inSubgroup perfectResidual (N.subgroupOf P) = H.subgroupOf P := by
  have h1 := inSubgroup_perfectResidual_map P.subtype P.subtype_injective (N.subgroupOf P)
  have h2 : (N.subgroupOf P).map P.subtype = N := by
    rw [subgroupOf_map_subtype]
    exact inf_eq_left.2 hN
  rw [h2, hH] at h1
  rw [h1]
  exact (comap_map_eq_self_of_injective P.subtype_injective _).symm

end Pull

section SylowPair

variable {M : Type*} [Group M]

theorem exists_conj_mem_of_card_prime [Finite M] (p : ℕ) [Fact p.Prime] {R S : Subgroup M}
    (hSR : S ≤ R) (hS : Nat.card S = p ^ (Nat.card R).factorization p) {t : M} (ht : t ∈ R)
    (htp : orderOf t = p) : ∃ x ∈ R, x⁻¹ * t * x ∈ S := by
  let S' : Sylow p R := Sylow.ofCard (S.subgroupOf R) (by
    rw [← hS]
    exact Nat.card_congr (subgroupOfEquivOfLe hSR).toEquiv)
  have htRp : IsPGroup p (zpowers (⟨t, ht⟩ : R)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, htp, pow_one]
  obtain ⟨T, hT⟩ := htRp.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq R S' T
  refine ⟨x, x.2, ?_⟩
  have htT : (⟨t, ht⟩ : R) ∈ (T : Subgroup R) := hT (mem_zpowers _)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htT
  obtain ⟨s, hs, hst⟩ := htT
  have hsS : (s : M) ∈ S := by
    have : s ∈ S.subgroupOf R := by
      rwa [show ((S' : Subgroup R)) = S.subgroupOf R from Sylow.coe_ofCard _ _] at hs
    exact mem_subgroupOf.mp this
  have e : x⁻¹ * ⟨t, ht⟩ * x = s := by
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
  rw [e']
  exact hsS

theorem mem_closure_pair_pow {x y : M} (hxy : Commute x y) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    {s : M} (hs : s ∈ closure ({x, y} : Set M)) :
    ∃ a b : ℕ, a < 3 ∧ b < 3 ∧ s = x ^ a * y ^ b := by
  have hx' : x⁻¹ = x ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx)
  have hy' : y⁻¹ = y ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hy)
  have red : ∀ a b : ℕ, ∃ a' b' : ℕ, a' < 3 ∧ b' < 3 ∧ x ^ a * y ^ b = x ^ a' * y ^ b' := by
    intro a b
    exact ⟨a % 3, b % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), by
      rw [pow_eq_pow_mod a hx, pow_eq_pow_mod b hy]⟩
  induction hs using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
    · exact ⟨0, 1, by norm_num, by norm_num, by simp⟩
  | one => exact ⟨0, 0, by norm_num, by norm_num, by simp⟩
  | mul z w hz hw ihz ihw =>
    obtain ⟨a, b, -, -, rfl⟩ := ihz
    obtain ⟨c, d, -, -, rfl⟩ := ihw
    have : x ^ a * y ^ b * (x ^ c * y ^ d) = x ^ (a + c) * y ^ (b + d) := by
      calc x ^ a * y ^ b * (x ^ c * y ^ d) = x ^ a * (y ^ b * x ^ c) * y ^ d := by
            simp only [mul_assoc]
        _ = x ^ a * (x ^ c * y ^ b) * y ^ d := by rw [(hxy.symm.pow_pow b c).eq]
        _ = x ^ (a + c) * y ^ (b + d) := by rw [pow_add, pow_add]; simp only [mul_assoc]
    rw [this]
    exact red _ _
  | inv z hz ih =>
    obtain ⟨a, b, -, -, rfl⟩ := ih
    have : (x ^ a * y ^ b)⁻¹ = x ^ (2 * a) * y ^ (2 * b) := by
      rw [mul_inv_rev, ← inv_pow, ← inv_pow, hx', hy', ← pow_mul, ← pow_mul]
      exact (hxy.symm.pow_pow (2 * b) (2 * a)).eq
    rw [this]
    exact red _ _

end SylowPair

section NormalClosure

variable {G : Type*} [Group G]

theorem normal_closure_eq [Finite G] {Y K' : Subgroup G} {a : G} {S : Set G} (ha : a ∈ Y)
    (hK : closure S = K') (hS : ∀ s ∈ S, ∃ x ∈ Y, s = x * a * x⁻¹) (hKY : K' ≤ Y)
    (hcard : Nat.card Y ≤ Nat.card K') :
    closure {z : G | ∃ x ∈ Y, z = x * a * x⁻¹} = Y := by
  refine le_antisymm ((closure_le Y).2 ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact Y.mul_mem (Y.mul_mem hx ha) (Y.inv_mem hx)
  · have hKeq : K' = Y := eq_of_le_of_card_ge hKY hcard
    calc Y = K' := hKeq.symm
      _ = closure S := hK.symm
      _ ≤ closure {z : G | ∃ x ∈ Y, z = x * a * x⁻¹} := closure_mono fun s hs => by
          obtain ⟨x, hx, rfl⟩ := hS s hs
          exact ⟨x, hx, rfl⟩

theorem closure_conj_set_subgroupOf {P Y : Subgroup G} (hY : Y ≤ P) {a : G} (ha : a ∈ Y)
    (h : closure {z : G | ∃ x ∈ Y, z = x * a * x⁻¹} = Y) :
    closure {z : P | ∃ x ∈ Y.subgroupOf P, z = x * ⟨a, hY ha⟩ * x⁻¹} = Y.subgroupOf P := by
  apply Subgroup.map_injective P.subtype_injective
  rw [MonoidHom.map_closure, subgroupOf_map_subtype, inf_eq_left.2 hY]
  conv_rhs => rw [← h]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hY hx⟩ * ⟨a, hY ha⟩ * ⟨x, hY hx⟩⁻¹, ⟨⟨x, hY hx⟩, hx, rfl⟩, by simp⟩

end NormalClosure

section Residual

variable {Y : Type*} [Group Y]

theorem conj_mem_of_conj_gens {H : Subgroup Y} {S : Set Y} (hS : closure S = H) {x : Y}
    (h : ∀ s ∈ S, x * s * x⁻¹ ∈ H) {y : Y} (hy : y ∈ H) : x * y * x⁻¹ ∈ H := by
  have : H.map (MulAut.conj x).toMonoidHom ≤ H := by
    calc H.map (MulAut.conj x).toMonoidHom = (closure S).map (MulAut.conj x).toMonoidHom := by
          rw [hS]
      _ = closure ((MulAut.conj x).toMonoidHom '' S) := MonoidHom.map_closure _ _
      _ ≤ H := by
          rw [closure_le]
          rintro _ ⟨s, hs, rfl⟩
          exact h s hs
  exact this ⟨y, hy, rfl⟩

theorem inSubgroup_perfectResidual_eq [Finite Y] {M H : Subgroup Y} {S : Set Y}
    (hHM : H ≤ M) (hS : closure S = H) (hperf : ⁅H, H⁆ = H)
    (hnorm : ∀ x ∈ M, ∀ s ∈ S, x * s * x⁻¹ ∈ H) (hidx : Nat.card M = 3 * Nat.card H) :
    inSubgroup perfectResidual M = H := by
  haveI hn : (H.subgroupOf M).Normal :=
    ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      simpa using conj_mem_of_conj_gens hS (hnorm g g.2) hn⟩
  have hcard : Nat.card (M ⧸ H.subgroupOf M) = 3 := by
    have h1 := (H.subgroupOf M).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (subgroupOfEquivOfLe hHM).toEquiv, hidx] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (M ⧸ H.subgroupOf M) := isCyclic_of_prime_card hcard
  haveI : Group.IsSolvable (M ⧸ H.subgroupOf M) :=
    Group.isSolvable_of_comm fun a b =>
      (IsCyclic.commGroup (α := M ⧸ H.subgroupOf M)).mul_comm a b
  exact le_antisymm (inSubgroup_perfectResidual_le_of_isSolvable hHM this)
    (le_inSubgroup_perfectResidual hperf hHM)

end Residual

end CFSG.RankThree.PartTwo.Sec8.Hering611.J3T
