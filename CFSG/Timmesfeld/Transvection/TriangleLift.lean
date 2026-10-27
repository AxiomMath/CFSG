module

public import CFSG.Timmesfeld.Transvection.TriangleQuot

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.LeviQuot
open scoped commutatorElement Matrix

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

theorem SL2.exists_mulVec_pair {K : Type*} [Field K] {u w : Fin 2 → K} {c : K} (hc : c ≠ 0)
    (hd : u 0 * w 1 - u 1 * w 0 ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ![c, 0] = u ∧
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ![0, (u 0 * w 1 - u 1 * w 0) / c] = w := by
  set d := u 0 * w 1 - u 1 * w 0 with hd_def
  refine ⟨⟨!![u 0 / c, w 0 * c / d; u 1 / c, w 1 * c / d], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    field_simp
    rw [hd_def]
    ring
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp

theorem commute_of_mk_eq {Y : Subgroup G} {a a' b b' : ↥Y}
    (ha : QuotientGroup.mk' (Subgroup.center ↥Y) a = QuotientGroup.mk' (Subgroup.center ↥Y) a')
    (hb : QuotientGroup.mk' (Subgroup.center ↥Y) b = QuotientGroup.mk' (Subgroup.center ↥Y) b')
    (h : Commute a' b') : Commute a b := by
  obtain ⟨z, hz, rfl⟩ : ∃ z ∈ Subgroup.center ↥Y, a = a' * z := by
    refine ⟨a'⁻¹ * a, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff]
    show QuotientGroup.mk' (Subgroup.center ↥Y) (a'⁻¹ * a) = 1
    rw [map_mul, map_inv, ha, inv_mul_cancel]
  obtain ⟨z', hz', rfl⟩ : ∃ z ∈ Subgroup.center ↥Y, b = b' * z := by
    refine ⟨b'⁻¹ * b, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff]
    show QuotientGroup.mk' (Subgroup.center ↥Y) (b'⁻¹ * b) = 1
    rw [map_mul, map_inv, hb, inv_mul_cancel]
  have hz1 := Subgroup.mem_center_iff.1 hz
  have hz2 := Subgroup.mem_center_iff.1 hz'
  have h1 : Commute a' (b' * z') := h.mul_right (hz2 a')
  have h2 : Commute z (b' * z') := (hz1 (b' * z')).symm
  exact h1.mul_left h2

theorem quotMap_sup {V P Q : Subgroup G} (hP : P ≤ V) (hQ : Q ≤ V) :
    quotMap V (P ⊔ Q) = quotMap V P ⊔ quotMap V Q := by
  rw [quotMap, quotMap, quotMap, ← Subgroup.map_sup, Subgroup.subgroupOf_sup hP hQ]

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G} (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
include S htY

omit htY in
theorem graph_le_sup : graph A t ≤ A ⊔ E ⊔ B := by
  intro f hf
  obtain ⟨a, ha, rfl⟩ := (mem_graph_iff S.commuting_conjSub).1 hf
  have hb : t * a * t⁻¹ ∈ B := S.conjA ▸ conj_mem_conjSub t ha
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
    (Subgroup.mem_sup_right hb)

omit htY in
theorem corrN_le_sup : corrN A E t ≤ A ⊔ E ⊔ B := by
  rw [corrN, Subgroup.closure_le]
  rintro _ ⟨x, hx, f, hf, rfl⟩
  have hxY : x ∈ A ⊔ E ⊔ B := le_sup_left (b := B) hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxY (S.graph_le_sup hf))
    (Subgroup.inv_mem _ hxY)

omit S htY in
theorem quotMap_sup_left :
    quotMap (A ⊔ E ⊔ B) (A ⊔ E) = quotMap (A ⊔ E ⊔ B) A ⊔ quotMap (A ⊔ E ⊔ B) E := by
  have hA : A ≤ A ⊔ E ⊔ B := le_sup_left.trans le_sup_left
  have hE : E ≤ A ⊔ E ⊔ B := le_sup_right.trans le_sup_left
  rw [quotMap, quotMap, quotMap, ← Subgroup.map_sup, Subgroup.subgroupOf_sup hA hE]

theorem quotMap_corrN [Finite G] : quotMap (A ⊔ E ⊔ B) (corrN A E t) =
    corrN (quotMap (A ⊔ E ⊔ B) A) (quotMap (A ⊔ E ⊔ B) E)
      (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨t, htY⟩) := by
  have hNY := S.corrN_le_sup
  have hXY : A ⊔ E ≤ A ⊔ E ⊔ B := le_sup_left
  have hAY : A ≤ A ⊔ E ⊔ B := le_sup_left.trans le_sup_left
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    have hn' : (n : G) ∈ corrN A E t := Subgroup.mem_subgroupOf.1 hn
    obtain ⟨n, hnY⟩ := n
    simp only at hn'
    clear hn
    induction hn' using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨x, hx, f, hf, rfl⟩ := hg
      have hxq : QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨x, hXY hx⟩ ∈
          quotMap (A ⊔ E ⊔ B) A ⊔ quotMap (A ⊔ E ⊔ B) E := by
        rw [← quotMap_sup_left]
        exact mk_mem_quotMap hx
      obtain ⟨a, ha, rfl⟩ := (mem_graph_iff S.commuting_conjSub).1 hf
      have hfq : QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))
          ⟨a * (t * a * t⁻¹), S.graph_le_sup hf⟩ ∈ graph (quotMap (A ⊔ E ⊔ B) A)
            (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨t, htY⟩) := by
        rw [mem_graph_iff (S.quotSetting htY).commuting_conjSub]
        refine ⟨QuotientGroup.mk' _ ⟨a, hAY ha⟩, mk_mem_quotMap ha, ?_⟩
        rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      refine Subgroup.subset_closure ⟨_, hxq, _, hfq, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    | one => exact Subgroup.one_mem _
    | mul g g' hg hg' ih ih' =>
      have := Subgroup.mul_mem _ (ih (hNY hg)) (ih' (hNY hg'))
      rw [← map_mul] at this
      exact this
    | inv g hg ih =>
      have := Subgroup.inv_mem _ (ih (hNY hg))
      rw [← map_inv] at this
      exact this
  · rw [corrN, Subgroup.closure_le]
    rintro _ ⟨x, hx, f, hf, rfl⟩
    rw [← quotMap_sup_left] at hx
    obtain ⟨x', hx', rfl⟩ := exists_of_mem_quotMap hx
    obtain ⟨f', hf', rfl⟩ := S.exists_of_mem_graph_quot htY hf
    have hmem : ((x' * f' * x'⁻¹ : ↥(A ⊔ E ⊔ B)) : G) ∈ corrN A E t :=
      Subgroup.subset_closure ⟨x', hx', f', hf', rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact mk_mem_quotMap hmem

omit htY in
theorem eq_one_of_mem_graph_of_commute [Finite G] {f : G} (hf : f ∈ graph A t)
    (hfE : ∀ e ∈ E, Commute f e) : f = 1 := by
  obtain ⟨a, ha, rfl⟩ := (mem_graph_iff S.commuting_conjSub).1 hf
  have hb : t * a * t⁻¹ ∈ B := S.conjA ▸ conj_mem_conjSub t ha
  by_cases ha1 : a = 1
  · rw [ha1]
    group
  exfalso
  have hb1 : t * a * t⁻¹ ≠ 1 := fun h => ha1 (conj_eq_one_iff.1 h)
  obtain ⟨e, he, he1⟩ := S.cls.root.exists_ne_one S.tri.memE
  have h1 := (commute_mul_iff S.cls S.iso S.tri.memE S.tri.memA S.tri.memB S.tri.ne S.tri.comm he
    he1 ha ha1 hb hb1).1 (hfE e he).symm
  exact S.tri.oppA.not_commute_of_mem he he1 fun a' ha' =>
    (S.cls.commuting_of_commute S.iso S.tri.memE S.tri.memA he he1 ha ha1 h1.1) e he a' ha'

omit htY in
theorem card_graph : Nat.card (graph A t) = Nat.card A := by
  have hinj : Function.Injective fun a : A =>
      (⟨(a : G) * (t * a * t⁻¹), (mem_graph_iff S.commuting_conjSub).2 ⟨a, a.2, rfl⟩⟩ :
        graph A t) := by
    intro a a' h
    have h' : (a : G) * (t * a * t⁻¹) = a' * (t * a' * t⁻¹) := congrArg Subtype.val h
    have hb : ∀ x ∈ A, t * x * t⁻¹ ∈ B := fun x hx => S.conjA ▸ conj_mem_conjSub t hx
    have hx : (a' : G)⁻¹ * a ∈ A ⊓ B := by
      refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
      have : (a' : G)⁻¹ * a = t * a' * t⁻¹ * (t * a * t⁻¹)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * (t * a' * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by rw [h']
          _ = t * a' * t⁻¹ * (t * a * t⁻¹)⁻¹ := by group
      rw [this]
      exact B.mul_mem (hb _ a'.2) (B.inv_mem (hb _ a.2))
    rw [S.cls.inf_eq_bot S.iso S.tri.memA S.tri.memB S.tri.ne, Subgroup.mem_bot,
      inv_mul_eq_one] at hx
    exact Subtype.ext hx.symm
  have hsurj : Function.Surjective fun a : A =>
      (⟨(a : G) * (t * a * t⁻¹), (mem_graph_iff S.commuting_conjSub).2 ⟨a, a.2, rfl⟩⟩ :
        graph A t) := by
    rintro ⟨f, hf⟩
    obtain ⟨a, ha, rfl⟩ := (mem_graph_iff S.commuting_conjSub).1 hf
    exact ⟨⟨a, ha⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm

theorem commute_of_mem_corrN' [Finite G] (hq : 4 ≤ Nat.card A) {n n' : G}
    (hn : n ∈ corrN A E t) (hn' : n' ∈ corrN A E t) : Commute n n' := by
  have hNY := S.corrN_le_sup
  have hFY := S.graph_le_sup
  obtain ⟨k, hk, φ, hφE, hφA, θ, hθ, hrange⟩ := S.exists_isNaturalModule_quot htY hq
  have hlift : ∀ v, ∃ m : ↥(A ⊔ E ⊔ B), (m : G) ∈ corrN A E t ∧
      QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) m = θ v := by
    intro v
    have h1 : θ v ∈ (corrN (quotMap (A ⊔ E ⊔ B) A) (quotMap (A ⊔ E ⊔ B) E)
        (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨t, htY⟩) : Set _) :=
      hrange ▸ ⟨v, rfl⟩
    rw [SetLike.mem_coe, ← S.quotMap_corrN htY] at h1
    exact exists_of_mem_quotMap h1
  choose ℓ hℓN hℓ using hlift
  have hθN : ∀ m : ↥(A ⊔ E ⊔ B), (m : G) ∈ corrN A E t →
      ∃ v, θ v = QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) m := by
    intro m hm
    have h1 : QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) m ∈
        (corrN (quotMap (A ⊔ E ⊔ B) A) (quotMap (A ⊔ E ⊔ B) E)
          (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨t, htY⟩) : Set _) := by
      rw [SetLike.mem_coe, ← S.quotMap_corrN htY]
      exact mk_mem_quotMap hm
    rw [← hrange] at h1
    exact h1
  obtain ⟨e₀, he₀, he₀1⟩ := S.cls.root.exists_ne_one S.tri.memE
  have hsN : partnerElt A E B e₀ ∈ corrN A E t :=
    corrM_le_corrN (S.partnerElt_mem_corrM he₀ he₀1)
  set s : ↥(A ⊔ E ⊔ B) := ⟨partnerElt A E B e₀, hNY hsN⟩ with hs_def
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, θ ![c₀, 0] = QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) s := by
    refine (hθ.mem_fixed_upper_iff hφE le_sup_left).1 ⟨hθN s hsN, fun a ha => ?_⟩
    obtain ⟨a', ha', rfl⟩ := exists_of_mem_quotMap ha
    exact Commute.map (show Commute a' s from
      Subtype.ext (S.commute_partnerElt he₀ he₀1 ha').symm) _
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    have h1 : QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) s = 1 := by
      rw [← hc₀]
      convert hθ.map_zero using 2
      ext i
      fin_cases i <;> rfl
    have h2 := Subgroup.mem_center_iff.1 ((QuotientGroup.eq_one_iff s).1 h1)
    apply S.tri.ne
    rw [← S.conjSub_partnerElt he₀ he₀1]
    refine (Aux.conjSub_eq_of_commute fun a ha => ?_).symm
    have hAY : A ≤ A ⊔ E ⊔ B := le_sup_left.trans le_sup_left
    have := congrArg Subtype.val (h2 ⟨a, hAY ha⟩)
    exact this.symm
  have hF : ∀ c, ∃ f : ↥(A ⊔ E ⊔ B), (f : G) ∈ graph A t ∧
      QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) f = θ ![0, c] := by
    have hfix : ∀ f : ↥(A ⊔ E ⊔ B), (f : G) ∈ graph A t →
        ∃ c, θ ![0, c] = QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) f := by
      intro f hf
      refine (hθ.mem_fixed_lower_iff hφA le_sup_right).1
        ⟨hθN f (corrM_le_corrN (graph_le_corrM hf)), fun a ha => ?_⟩
      obtain ⟨a', ha', rfl⟩ := exists_of_mem_quotMap ha
      exact Commute.map (show Commute a' f from
        Subtype.ext (S.commute_graph_left hf ha').symm) _
    set T : Set (↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B)) :=
      (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))) ''
        ((graph A t).subgroupOf (A ⊔ E ⊔ B) : Set ↥(A ⊔ E ⊔ B)) with hT
    have hTsub : T ⊆ Set.range fun c => θ ![0, c] := by
      rintro _ ⟨f, hf, rfl⟩
      obtain ⟨c, hc⟩ := hfix f (Subgroup.mem_subgroupOf.1 hf)
      exact ⟨c, hc⟩
    have hinj : Set.InjOn (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)))
        ((graph A t).subgroupOf (A ⊔ E ⊔ B) : Set ↥(A ⊔ E ⊔ B)) := by
      intro f hf f' hf' h
      have h1 : f⁻¹ * f' ∈ Subgroup.center ↥(A ⊔ E ⊔ B) := by
        rw [← QuotientGroup.eq_one_iff]
        show QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) (f⁻¹ * f') = 1
        rw [map_mul, map_inv, h, inv_mul_cancel]
      have h2 : ((f⁻¹ * f' : ↥(A ⊔ E ⊔ B)) : G) ∈ graph A t :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hf))
          (Subgroup.mem_subgroupOf.1 hf')
      have hEY : E ≤ A ⊔ E ⊔ B := le_sup_right.trans le_sup_left
      have h3 := S.eq_one_of_mem_graph_of_commute h2 fun e he =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.1 h1 ⟨e, hEY he⟩)).symm
      have h4 : f⁻¹ * f' = 1 := Subtype.ext h3
      rw [inv_mul_eq_one] at h4
      exact h4
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [hk] at hq
      norm_num at hq
    have hcardT : T.ncard = Nat.card A := by
      rw [hT, hinj.ncard_image, ← S.card_graph,
        ← card_subgroupOf_of_le (S.graph_le_sup)]
      rfl
    have hcardR : (Set.range fun c : GaloisField 2 k => θ ![0, c]).ncard = Nat.card A := by
      rw [Set.ncard_range_of_injective, GaloisField.card 2 k hk0, hk]
      intro c c' h
      have := congrFun (hθ.injective h) 1
      simpa using this
    have heq := Set.eq_of_subset_of_ncard_le hTsub (by rw [hcardT, hcardR]) (Set.toFinite _)
    intro c
    have : θ ![0, c] ∈ T := heq ▸ ⟨c, rfl⟩
    obtain ⟨f, hf, hfc⟩ := this
    exact ⟨f, Subgroup.mem_subgroupOf.1 hf, hfc⟩
  have hsF : ∀ f : ↥(A ⊔ E ⊔ B), (f : G) ∈ graph A t → Commute s f := by
    intro f hf
    have hS' := S.partnerSetting he₀ he₀1
    rw [S.graph_eq_of_setting hS'] at hf
    obtain ⟨a, ha, haf⟩ := (mem_graph_iff hS'.commuting_conjSub).1 hf
    have hss := S.partnerElt_mul_self he₀ he₀1
    have hb : partnerElt A E B e₀ * a * (partnerElt A E B e₀)⁻¹ ∈ B := by
      have := conj_mem_conjSub (partnerElt A E B e₀) ha
      rwa [S.conjSub_partnerElt he₀ he₀1] at this
    have hab := (S.tri.comm a ha _ hb).eq
    obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ = partnerElt A E B e₀ := ⟨_, rfl⟩
    rw [← hs₀] at hss hab haf
    have hsinv : s₀⁻¹ = s₀ := inv_eq_of_mul_eq_one_right hss
    rw [hsinv] at hab haf
    apply Subtype.ext
    show partnerElt A E B e₀ * (f : G) = f * partnerElt A E B e₀
    rw [← hs₀, haf]
    calc s₀ * (a * (s₀ * a * s₀)) = (s₀ * a * s₀) * a * s₀ := by group
      _ = a * (s₀ * a * s₀) * s₀ := by rw [← hab]
  have hind : ∀ u w : Fin 2 → GaloisField 2 k, u 0 * w 1 - u 1 * w 0 ≠ 0 →
      Commute (ℓ u) (ℓ w) := by
    intro u w hd
    obtain ⟨g, hgu, hgw⟩ := SL2.exists_mulVec_pair hc₀0 hd
    obtain ⟨f, hf, hfc⟩ := hF ((u 0 * w 1 - u 1 * w 0) / c₀)
    set x := φ.symm g with hx
    have hxX : (x : ↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B)) ∈
        quotMap (A ⊔ E ⊔ B) (E ⊔ A) := by
      rw [quotMap_sup (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left)]
      exact x.2
    obtain ⟨x', -, hx'⟩ := exists_of_mem_quotMap hxX
    have hφx : φ x = g := by rw [hx, MulEquiv.apply_symm_apply]
    have hconj : ∀ y : ↥(A ⊔ E ⊔ B), ∀ v, QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) y =
        θ v → QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) (x' * y * x'⁻¹) =
          θ ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)) *ᵥ v) := by
      intro y v hy
      rw [map_mul, map_mul, map_inv, hx', hy, ← hφx, hθ.map_mulVec]
    have h1 := hconj s ![c₀, 0] hc₀.symm
    have h2 := hconj f _ hfc
    rw [hgu] at h1
    rw [hgw] at h2
    exact commute_of_mk_eq ((hℓ u).trans h1.symm) ((hℓ w).trans h2.symm)
      ((hsF f hf).map (MulAut.conj x').toMonoidHom)
  have hall : ∀ u w : Fin 2 → GaloisField 2 k, Commute (ℓ u) (ℓ w) := by
    intro u w
    by_cases hd : u 0 * w 1 - u 1 * w 0 = 0
    · by_cases hu : u = 0
      ·
        have h0 : QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) (ℓ u) = 1 := by
          rw [hℓ, hu, hθ.map_zero]
        have hc := Subgroup.mem_center_iff.1 ((QuotientGroup.eq_one_iff _).1 h0)
        exact (hc (ℓ w)).symm
      obtain ⟨w', hw'⟩ : ∃ w' : Fin 2 → GaloisField 2 k, u 0 * w' 1 - u 1 * w' 0 ≠ 0 := by
        by_cases hu0 : u 0 = 0
        · refine ⟨![1, 0], ?_⟩
          have hu1 : u 1 ≠ 0 := by
            intro hu1
            apply hu
            ext i
            fin_cases i <;> simp [hu0, hu1]
          simpa [hu0] using hu1
        · exact ⟨![0, 1], by simpa using hu0⟩
      have h1 := hind u (w + w') (by
        simp only [Pi.add_apply]
        intro h
        apply hw'
        linear_combination h - hd)
      have h2 := hind u w' hw'
      have hmk : QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) (ℓ w) =
          QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) (ℓ (w + w') * (ℓ w')⁻¹) := by
        rw [map_mul, map_inv, hℓ, hℓ, hℓ, hθ.map_add, mul_inv_cancel_right]
      exact commute_of_mk_eq rfl hmk (h1.mul_right h2.inv_right)
    · exact hind u w hd
  have hnY := hNY hn
  have hn'Y := hNY hn'
  obtain ⟨v, hv⟩ := hθN ⟨n, hnY⟩ hn
  obtain ⟨v', hv'⟩ := hθN ⟨n', hn'Y⟩ hn'
  have hc := commute_of_mk_eq (a := ⟨n, hnY⟩) (b := ⟨n', hn'Y⟩) ((hℓ v).trans hv).symm
    ((hℓ v').trans hv').symm (hall v v')
  exact congrArg Subtype.val hc

end TriangleSetting

end CFSG.Timmesfeld.Transvection
