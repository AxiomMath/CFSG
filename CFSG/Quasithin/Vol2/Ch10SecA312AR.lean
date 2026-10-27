module

public import CFSG.Quasithin.Vol2.Ch10SecA312AD
public import CFSG.Sporadic.HS
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

section General

variable {G : Type} [Group G]

theorem normal_of_le_center' {H : Subgroup G} (h : H ≤ Subgroup.center G) : H.Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (h hn) g, mul_inv_cancel_right]
    exact hn⟩

theorem pCore_eq_of_isSimpleGroup (W : Subgroup G) [W.Normal] (hW2 : IsPGroup 2 W)
    (hs : IsSimpleGroup (G ⧸ W)) (hnp : ¬ IsPGroup 2 (G ⧸ W)) : CFSG.pCore 2 G = W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup inferInstance hW2)
  have hn : ((CFSG.pCore 2 G).map (QuotientGroup.mk' W)).Normal :=
    (inferInstance : (CFSG.pCore 2 G).Normal).map _ (QuotientGroup.mk'_surjective W)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 G).map
    (QuotientGroup.mk' W)) with h | h
  · intro x hx
    have : QuotientGroup.mk' W x ∈ (CFSG.pCore 2 G).map (QuotientGroup.mk' W) := ⟨x, hx, rfl⟩
    rwa [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  · exfalso
    apply hnp
    have hp : IsPGroup 2 ((CFSG.pCore 2 G).map (QuotientGroup.mk' W)) :=
      (CFSG.pCore_isPGroup (p := 2) (G := G)).map _
    rw [h] at hp
    exact hp.of_equiv Subgroup.topEquiv

theorem mem_of_comm_of_isSimpleGroup {N : Subgroup G} [N.Normal] (hs : IsSimpleGroup (G ⧸ N))
    (hp : ¬ (Nat.card (G ⧸ N)).Prime) {z : G} (hz : ∀ b : G, z * b = b * z) : z ∈ N := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (G ⧸ N)) with h | h
  · have : QuotientGroup.mk' N z ∈ Subgroup.center (G ⧸ N) := by
      refine Subgroup.mem_center_iff.mpr fun q => ?_
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N q
      rw [← map_mul, ← map_mul, hz b]
    rwa [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  · have : IsMulCommutative (G ⧸ N) := Subgroup.center_eq_top_iff.1 h
    exact absurd (Group.is_simple_iff_prime_card.1 hs) hp

theorem mem_of_odd_index [Finite G] {B : Subgroup G} (hB : ¬ 2 ∣ B.index) {z : G}
    (hz : IsPGroup 2 (Subgroup.zpowers z)) (hzB : ∀ b ∈ B, z * b = b * z) : z ∈ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_isSylowTwoOf B
  have hS' : IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, hS.isPGroup, fun h2 => ?_⟩
    have h1 : (S.subgroupOf ⊤).index = (S.subgroupOf B).index * B.index := by
      show S.relIndex ⊤ = S.relIndex B * B.index
      rw [Subgroup.relIndex_top_right, Subgroup.relIndex_mul_index hS.le]
    rw [h1] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hS.2.2 h
    · exact hB h
  have hzN : z ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      rwa [hzB s (hS.le hs), mul_inv_cancel_right]
    · intro hs
      have h1 : z * (z * s * z⁻¹) = z * s := by
        rw [hzB _ (hS.le hs)]
        group
      rwa [mul_left_cancel h1] at hs
  have hsup : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers z) :=
    hS'.isPGroup.to_sup_of_normal_left' hz ((Subgroup.zpowers_le).mpr hzN)
  have heq := hS'.eq_of_le le_sup_left le_top hsup
  have hzS : z ∈ S := by
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  exact hS.le hzS

theorem comm_of_pow_seven [Finite G] {N : Subgroup G} [N.Normal]
    (hN : Nat.card {w : G // w ∈ N ∧ w * w = 1} ≤ 8) {g : G} (hg : g ^ 7 = 1) {v : G}
    (hvN : v ∈ N) (hv1 : v ≠ 1) (hv2 : v * v = 1) (hgv : g * v = v * g) {w : G} (hwN : w ∈ N)
    (hw2 : w * w = 1) : g * w = w * g := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fintype {w : G // w ∈ N ∧ w * w = 1} := Fintype.ofFinite _
  have hconj : ∀ h x : G, x ∈ N → x * x = 1 →
      h * x * h⁻¹ ∈ N ∧ h * x * h⁻¹ * (h * x * h⁻¹) = 1 := fun h x hx hx2 =>
    ⟨‹N.Normal›.conj_mem x hx h, by
      calc h * x * h⁻¹ * (h * x * h⁻¹) = h * (x * x) * h⁻¹ := by group
        _ = 1 := by rw [hx2]; group⟩
  let σ : Equiv.Perm {w : G // w ∈ N ∧ w * w = 1} :=
    { toFun := fun x => ⟨g * x.1 * g⁻¹, hconj g x.1 x.2.1 x.2.2⟩
      invFun := fun x => ⟨g⁻¹ * x.1 * g⁻¹⁻¹, hconj g⁻¹ x.1 x.2.1 x.2.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
  have hpow : ∀ n : ℕ, ∀ x, ((σ ^ n) x).1 = g ^ n * x.1 * (g ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ' σ n, Equiv.Perm.mul_apply]
      show g * ((σ ^ n) x).1 * g⁻¹ = _
      rw [ih x]
      group
  have h7 : σ ^ 7 ^ 1 = 1 := by
    rw [pow_one]
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [hpow 7 x, hg]
    simp
  have hmod : σ.supportᶜ.card % 7 = Fintype.card {w : G // w ∈ N ∧ w * w = 1} % 7 :=
    Equiv.Perm.card_compl_support_modEq h7
  have hfix : ∀ x, σ x = x → x ∈ σ.supportᶜ := fun x hx =>
    Finset.mem_compl.mpr fun h => (Equiv.Perm.mem_support.mp h) hx
  have hne : (⟨1, N.one_mem, one_mul 1⟩ : {w : G // w ∈ N ∧ w * w = 1}) ≠ ⟨v, hvN, hv2⟩ :=
    fun h => hv1 (congrArg Subtype.val h).symm
  have h2 : 2 ≤ σ.supportᶜ.card := by
    have hsub : ({⟨1, N.one_mem, one_mul 1⟩, ⟨v, hvN, hv2⟩} :
        Finset {w : G // w ∈ N ∧ w * w = 1}) ⊆ σ.supportᶜ := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hfix _ (Subtype.ext (show g * 1 * g⁻¹ = 1 by group))
      · exact hfix _ (Subtype.ext (show g * v * g⁻¹ = v by rw [hgv, mul_inv_cancel_right]))
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hne] at this
  have hle := Finset.card_le_univ σ.supportᶜ
  have hS8 : Fintype.card {w : G // w ∈ N ∧ w * w = 1} ≤ 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact hN
  have huniv := Finset.eq_univ_of_card _ (by omega : σ.supportᶜ.card = _)
  have hx : (⟨w, hwN, hw2⟩ : {w : G // w ∈ N ∧ w * w = 1}) ∈ σ.supportᶜ := by
    rw [huniv]
    exact Finset.mem_univ _
  have hσw : σ ⟨w, hwN, hw2⟩ = ⟨w, hwN, hw2⟩ := by
    by_contra h
    exact (Finset.mem_compl.mp hx) (Equiv.Perm.mem_support.mpr h)
  have h3 : g * w * g⁻¹ = w := congrArg Subtype.val hσw
  calc g * w = g * w * g⁻¹ * g := by group
    _ = w * g := by rw [h3]

theorem comm_of_isSimpleGroup {N : Subgroup G} [N.Normal]
    (hNc : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hs : IsSimpleGroup (G ⧸ N)) {g : G} (hgN : g ∉ N)
    (hg : ∀ w ∈ N, w * w = 1 → g * w = w * g) (b : G) {w : G} (hwN : w ∈ N) (hw2 : w * w = 1) :
    b * w = w * b := by
  let C : Subgroup G := Subgroup.centralizer {x | x ∈ N ∧ x * x = 1}
  have hCn : C.Normal := ⟨fun c hc h => by
    rw [Subgroup.mem_centralizer_iff]
    rintro x ⟨hxN, hx2⟩
    have hx' : h⁻¹ * x * h ∈ {x | x ∈ N ∧ x * x = 1} := by
      refine ⟨by simpa using ‹N.Normal›.conj_mem x hxN h⁻¹, ?_⟩
      calc h⁻¹ * x * h * (h⁻¹ * x * h) = h⁻¹ * (x * x) * h := by group
        _ = 1 := by rw [hx2]; group
    have := Subgroup.mem_centralizer_iff.mp hc _ hx'
    calc x * (h * c * h⁻¹) = h * (h⁻¹ * x * h * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * x * h)) * h⁻¹ := by rw [this]
      _ = h * c * h⁻¹ * x := by group⟩
  have hNC : N ≤ C := fun n hn =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => hNc x hx.1 n hn
  have hgC : g ∈ C := Subgroup.mem_centralizer_iff.mpr fun x hx => (hg x hx.1 hx.2).symm
  have hn : (C.map (QuotientGroup.mk' N)).Normal := hCn.map _ (QuotientGroup.mk'_surjective N)
  have hmap : C.map (QuotientGroup.mk' N) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map (QuotientGroup.mk' N)) with h | h
    · exfalso
      have : QuotientGroup.mk' N g ∈ C.map (QuotientGroup.mk' N) := ⟨g, hgC, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact hgN this
    · exact h
  have hCtop : C = ⊤ := by
    rw [← Subgroup.comap_map_eq_self (f := QuotientGroup.mk' N) (H := C)
      (by rwa [QuotientGroup.ker_mk']), hmap, Subgroup.comap_top]
  have hb : b ∈ C := hCtop ▸ Subgroup.mem_top b
  exact (Subgroup.mem_centralizer_iff.mp hb w ⟨hwN, hw2⟩).symm

end General

variable {X : Type} [Group X] [Finite X]

theorem isPGroup_of_isZ4StarExtra2 {W : Type} [Group W] (h : IsZ4StarExtra2 W) :
    IsPGroup 2 W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Z, E, hZ4, -, hE, hZcen, hsup, -⟩ := h
  have : Z.Normal := normal_of_le_center' hZcen
  have hZ2 : IsPGroup 2 ↥Z := IsPGroup.of_card (n := 2) (by rw [hZ4]; norm_num)
  have hE2 : IsPGroup 2 ↥E := IsPGroup.of_card (n := 5) (by rw [hE.2])
  have h := hZ2.to_sup_of_normal_left hE2
  rw [hsup] at h
  exact h.of_equiv Subgroup.topEquiv

theorem eq_of_center_involution {W : Type} [Group W] [Finite W] (h : IsZ4StarExtra2 W)
    {v w : W} (hv : v ∈ Subgroup.center W) (hw : w ∈ Subgroup.center W) (hv2 : v * v = 1)
    (hw2 : w * w = 1) (hv1 : v ≠ 1) (hw1 : w ≠ 1) : v = w := by
  classical
  obtain ⟨Z, E, hZ4, hZc, hE, hZcen, hsup, hZE⟩ := h
  have : Z.Normal := normal_of_le_center' hZcen
  have := hE.1
  have hle : (Z ⊓ E).subgroupOf E ≤ Subgroup.center ↥E := fun x hx =>
    Subgroup.mem_center_iff.mpr fun f => Subtype.ext
      (Subgroup.mem_center_iff.mp (hZcen (Subgroup.mem_subgroupOf.mp hx).1) f)
  have hEc : Subgroup.center ↥E ≤ (Z ⊓ E).subgroupOf E := by
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).ge
    rw [CFSG.IsExtraspecial.center_order_p 2 ↥E, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Z ⊓ E ≤ E)).toEquiv, hZE]
  have hmem : ∀ u ∈ Subgroup.center W, u ∈ Z := by
    intro u hu
    have hu' : u ∈ ((Z ⊔ E : Subgroup W) : Set W) := by
      rw [hsup]
      exact Subgroup.mem_top u
    rw [Subgroup.normal_mul] at hu'
    obtain ⟨c, hc, e, he, rfl⟩ := Set.mem_mul.mp hu'
    have heZ : (⟨e, he⟩ : ↥E) ∈ Subgroup.center ↥E := by
      refine Subgroup.mem_center_iff.mpr fun f => Subtype.ext ?_
      have h1 := Subgroup.mem_center_iff.mp hu (f : W)
      have h2 := Subgroup.mem_center_iff.mp (hZcen hc) (f : W)
      show (f : W) * e = e * f
      refine mul_left_cancel (a := c) ?_
      calc c * (↑f * e) = ↑f * (c * e) := by rw [← mul_assoc, ← h2, mul_assoc]
        _ = c * e * ↑f := h1
        _ = c * (e * ↑f) := mul_assoc _ _ _
    exact Z.mul_mem hc (Subgroup.mem_subgroupOf.mp (hEc heZ)).1
  by_contra hvw
  have : Fintype ↥Z := Fintype.ofFinite _
  have h4 : (Finset.univ.filter (fun a : ↥Z => a ^ 2 = 1)).card ≤ 2 := by
    convert IsCyclic.card_pow_eq_one_le (α := ↥Z) (n := 2) two_pos
  have h3 : ({1, ⟨v, hmem v hv⟩, ⟨w, hmem w hw⟩} : Finset ↥Z).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, ⟨v, hmem v hv⟩, ⟨w, hmem w hw⟩,
      fun h => hv1 (congrArg Subtype.val h).symm, fun h => hw1 (congrArg Subtype.val h).symm,
      fun h => hvw (congrArg Subtype.val h), rfl⟩
  have hsub : ({1, ⟨v, hmem v hv⟩, ⟨w, hmem w hw⟩} : Finset ↥Z) ⊆
      Finset.univ.filter (fun a : ↥Z => a ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext (by simpa [pow_two] using hv2)
    · exact Subtype.ext (by simpa [pow_two] using hw2)
  have := Finset.card_le_card hsub
  omega

theorem false_of_isZ4StarExtra2 {T B V : Subgroup X} (hB : B ∈ lFamily T) (N : Subgroup ↥B)
    [N.Normal] (hN : IsZ4StarExtra2 ↥N) (hs : IsSimpleGroup (↥B ⧸ N)) (hVB : V ≤ B)
    (hV : IsElemAbelian 2 V) (hBV : B ≤ Subgroup.normalizer (V : Set X)) (hcomm : ⁅V, B⁆ = V)
    (hV1 : V ≠ ⊥) (hc : pCoreOf 2 B ≤ Subgroup.centralizer (V : Set X)) : False := by
  have hN2 := isPGroup_of_isZ4StarExtra2 hN
  have heq := pCore_eq_of_isSimpleGroup N hN2 hs (not_isPGroup_quotient hB N hN2)
  refine false_of_V hVB hV hBV hcomm hV1 hc fun v hv hvc hv2 b hb => ?_
  rw [pCoreOf_eq_map, heq] at hv hvc
  obtain ⟨v', hv'N, rfl⟩ := hv
  have hnc : (⟨v', hv'N⟩ : ↥N) ∈ Subgroup.center ↥N := by
    refine Subgroup.mem_center_iff.mpr fun u => ?_
    have := hvc _ ⟨u, u.2, rfl⟩
    exact Subtype.ext (Subtype.ext (by simpa using this))
  have hn2 : (⟨v', hv'N⟩ : ↥N) * ⟨v', hv'N⟩ = 1 := Subtype.ext (Subtype.ext (by simpa using hv2))
  by_cases hn1 : (⟨v', hv'N⟩ : ↥N) = 1
  · have : v' = 1 := congrArg Subtype.val hn1
    simp [this]
  have hφc : MulAut.conjNormal (⟨b, hb⟩ : ↥B) ⟨v', hv'N⟩ ∈ Subgroup.center ↥N := by
    refine Subgroup.mem_center_iff.mpr fun u => ?_
    obtain ⟨u', rfl⟩ := MulEquiv.surjective (MulAut.conjNormal (⟨b, hb⟩ : ↥B)) u
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hnc u']
  have hφn := eq_of_center_involution hN hφc hnc (by rw [← map_mul, hn2, map_one]) hn2
    (fun h => hn1 (MulEquiv.injective (MulAut.conjNormal (⟨b, hb⟩ : ↥B))
      (h.trans (map_one _).symm))) hn1
  have h1 := MulAut.conjNormal_apply (H := N) (⟨b, hb⟩ : ↥B) ⟨v', hv'N⟩
  rw [hφn] at h1
  have h2 : b * (v' : X) * b⁻¹ = v' := congrArg Subtype.val h1.symm
  show b * (v' : X) = v' * b
  calc b * (v' : X) = b * v' * b⁻¹ * b := by group
    _ = v' * b := by rw [h2]

theorem card_sq_eq_one_le :
    Nat.card {a : Multiplicative (Fin 3 → ZMod 4) // a * a = 1} ≤ 8 := by
  have key : ∀ x y : ZMod 4, x + x = 0 → y + y = 0 → (x = 2 ↔ y = 2) → x = y := by decide
  have h2 : ∀ a : {a : Multiplicative (Fin 3 → ZMod 4) // a * a = 1}, ∀ i : Fin 3,
      Multiplicative.toAdd a.1 i + Multiplicative.toAdd a.1 i = 0 := fun a i => by
    have := congrArg (fun x : Multiplicative (Fin 3 → ZMod 4) => Multiplicative.toAdd x i) a.2
    simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply] at this
    exact this
  have hf : Function.Injective (fun (a : {a : Multiplicative (Fin 3 → ZMod 4) // a * a = 1})
      (i : Fin 3) => decide (Multiplicative.toAdd a.1 i = 2)) := by
    intro a b hab
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    exact key _ _ (h2 a i) (h2 b i) (decide_eq_decide.mp (congrFun hab i))
  calc Nat.card _ ≤ Nat.card (Fin 3 → Bool) := Nat.card_le_card_of_injective _ hf
    _ = 8 := by
      rw [Nat.card_fun]
      simp

theorem card_sq_le_of_isZ4Cubed {G : Type} [Group G] {N : Subgroup G} (hN : IsZ4Cubed ↥N) :
    Nat.card {w : G // w ∈ N ∧ w * w = 1} ≤ 8 := by
  obtain ⟨e⟩ := hN
  refine le_trans (Nat.card_le_card_of_injective (fun w : {w : G // w ∈ N ∧ w * w = 1} =>
    (⟨e ⟨w.1, w.2.1⟩, by rw [← map_mul, show (⟨w.1, w.2.1⟩ : ↥N) * ⟨w.1, w.2.1⟩ = 1 from
      Subtype.ext w.2.2, map_one]⟩ : {a : Multiplicative (Fin 3 → ZMod 4) // a * a = 1}))
    ?_) card_sq_eq_one_le
  intro a b hab
  have h := e.injective (congrArg Subtype.val hab)
  exact Subtype.ext (congrArg (fun x : ↥N => (x : G)) h)

theorem false_of_isZ4Cubed {T B V : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T)
    (hX : Nat.card X = 44352000) {z : X} (hzT : z ∈ T) (hz1 : z ≠ 1)
    (hzB : ∀ b ∈ B, z * b = b * z) (N : Subgroup ↥B) [N.Normal] (hN : IsZ4Cubed ↥N)
    (hY : IsPSL 3 2 1 (↥B ⧸ N)) (hVB : V ≤ B) (hV : IsElemAbelian 2 V)
    (hBV : B ≤ Subgroup.normalizer (V : Set X)) (hcomm : ⁅V, B⁆ = V) (hV1 : V ≠ ⊥)
    (hc : pCoreOf 2 B ≤ Subgroup.centralizer (V : Set X)) : False := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨e₁⟩ := id hN
  have hs : IsSimpleGroup (↥B ⧸ N) := isSimpleGroup_of_stated hY
  have hcardQ : Nat.card (↥B ⧸ N) = 168 := by
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hY).1 rfl]
    decide
  have hcardN : Nat.card ↥N = 64 := by
    rw [Nat.card_congr (e₁.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod]
    simp
  have hcardB : Nat.card ↥B = 10752 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hcardQ, hcardN]
  have hidx : ¬ 2 ∣ B.index := by
    have := Subgroup.index_mul_card B
    rw [hcardB, hX] at this
    omega
  have hzB' : z ∈ B :=
    mem_of_odd_index hidx (hT.isPGroup.to_le (Subgroup.zpowers_le.mpr hzT)) hzB
  have hzc : ∀ b : ↥B, (⟨z, hzB'⟩ : ↥B) * b = b * ⟨z, hzB'⟩ := fun b => Subtype.ext (hzB b b.2)
  have hzN : (⟨z, hzB'⟩ : ↥B) ∈ N :=
    mem_of_comm_of_isSimpleGroup hs (by rw [hcardQ]; norm_num) hzc
  have hN2 : IsPGroup 2 ↥N := IsPGroup.of_card (n := 6) (by rw [hcardN]; norm_num)
  obtain ⟨k, hk1, hk2⟩ := exists_pow_involution hN2 (γ := ⟨⟨z, hzB'⟩, hzN⟩)
    (fun h => hz1 (congrArg (fun x : ↥N => ((x : ↥B) : X)) h))
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 7 (by rw [hcardB]; norm_num)
  have hgN : g ∉ N := fun h => by
    have := orderOf_dvd_natCard (⟨g, h⟩ : ↥N)
    rw [Subgroup.orderOf_mk, hg, hcardN] at this
    norm_num at this
  have hv : (((⟨⟨z, hzB'⟩, hzN⟩ : ↥N) ^ k : ↥N) : ↥B) = (⟨z, hzB'⟩ : ↥B) ^ k := by simp
  have hgΩ : ∀ w ∈ N, w * w = 1 → g * w = w * g := fun w hwN hw2 =>
    comm_of_pow_seven (card_sq_le_of_isZ4Cubed hN) (by rw [← hg]; exact pow_orderOf_eq_one g)
      ((⟨⟨z, hzB'⟩, hzN⟩ : ↥N) ^ k).2 (fun h => hk1 (Subtype.ext h))
      (congrArg Subtype.val hk2) (by rw [hv]; exact (Commute.pow_left (hzc g) k).symm.eq) hwN hw2
  have hNc : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := fun x hx y hy => by
    have h : (⟨x, hx⟩ : ↥N) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
      e₁.injective (by rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  have heq := pCore_eq_of_isSimpleGroup N hN2 hs (not_isPGroup_quotient hB N hN2)
  refine false_of_V hVB hV hBV hcomm hV1 hc fun v hv _ hv2 b hb => ?_
  rw [pCoreOf_eq_map, heq] at hv
  obtain ⟨v', hv'N, rfl⟩ := hv
  exact congrArg Subtype.val (comm_of_isSimpleGroup hNc hs hgN hgΩ ⟨b, hb⟩ hv'N
    (Subtype.ext (by simpa using hv2)))

theorem a312ZCentHS_holds : A312ZCentHS := by
  intro X _ _ T B hcase hc
  obtain ⟨-, -, -, hT, hB, -, -, -, ⟨z, hzT, hz1, -, hzB⟩, V, hVB, hV, hBV, hcomm, hV1, hcV, -⟩ :=
    hc
  obtain ⟨hcase, ⟨eHS⟩⟩ := hcase
  rcases hcase with ⟨N, hNn, hN, hY⟩ | ⟨N, hNn, hN, hY⟩
  · exact false_of_isZ4StarExtra2 hB N hN (isSimpleGroup_alt (Or.inl rfl) hY) hVB hV hBV hcomm
      hV1 hcV
  · have hX : Nat.card X = 44352000 := by
      rw [← Subgroup.card_top (G := X), Nat.card_congr eHS.toEquiv]
      exact CFSG.Sporadic.HS.card_HS
    exact false_of_isZ4Cubed hT hB hX hzT hz1 hzB N hN hY hVB hV hBV hcomm hV1 hcV

end CFSG.Quasithin.Vol2.Ch10.A312A
