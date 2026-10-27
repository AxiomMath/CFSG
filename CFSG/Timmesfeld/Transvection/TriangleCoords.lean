module

public import CFSG.Timmesfeld.Transvection.TriangleLift

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.LeviQuot CFSG.Timmesfeld.ARS.NaturalModule
open scoped Matrix

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

theorem diagElt_pow {K : Type*} [Field K] (c : Kˣ) (j : ℕ) :
    diagElt c ^ j = diagElt (c ^ j) := by
  induction j with
  | zero => rw [pow_zero, pow_zero, diagElt_one]
  | succ j ih => rw [pow_succ, ih, diagElt_mul_diagElt, pow_succ]

theorem conjSub_pow_eq {H : Subgroup G} {h : G} (hH : conjSub H h = H) (j : ℕ) :
    conjSub H (h ^ j) = H := by
  induction j with
  | zero => rw [pow_zero, conjSub_one]
  | succ j ih => rw [pow_succ, conjSub_mul, hH, ih]

theorem conjSub_inv_eq {H : Subgroup G} {h : G} (hH : conjSub H h = H) : conjSub H h⁻¹ = H := by
  conv_lhs => rw [← hH]
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_conj_eq {A B : Subgroup G} {h s : G} (hA : conjSub A h = A)
    (hs : conjSub A s = B) : conjSub A (h * s * h⁻¹) = conjSub B h := by
  rw [conjSub_mul, conjSub_inv_eq hA, conjSub_mul, hs]

theorem exists_triangleSetting [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    {A E B : Subgroup G} (hT : IsTriangle Δ A E B) :
    ∃ t ∈ A ⊔ E ⊔ B, TriangleSetting Δ A E B t := by
  obtain ⟨e, he, he1⟩ := hΔ.root.exists_ne_one hT.memE
  have S₀ : TriangleSetting Δ A E B (trElt A E B e) := ⟨hΔ, hiso, hT,
    (trElt_spec hΔ hT.memA hT.memB hT.memE hT.comm hT.oppA hT.oppB he he1).1,
    fun _ hy => commute_trElt hΔ hT.memB hT.memE hT.comm hT.oppA hT.oppB he he1 hy,
    conjSub_trElt hΔ hiso hT.memA hT.memB hT.memE hT.comm hT.oppA hT.oppB he he1⟩
  refine ⟨partnerElt A E B e, ?_, S₀.partnerSetting he he1⟩
  have hA' : partner E A e ∈ A ⊔ E ⊔ B :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (partner_mem hT.oppA he he1))
  have hE' : e ∈ A ⊔ E ⊔ B := Subgroup.mem_sup_left (Subgroup.mem_sup_right he)
  have hB' : partner E B e ∈ A ⊔ E ⊔ B := Subgroup.mem_sup_right (partner_mem hT.oppB he he1)
  have hf := Subgroup.mul_mem _ hA' hB'
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hE' hf) hE') hf

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G} (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
include S htY

theorem fourTerm [Finite G] (hq : 4 ≤ Nat.card A) : FourTerm A E t := by
  intro e he f hf f' hf'
  have hfN : f ∈ corrN A E t := corrM_le_corrN (graph_le_corrM hf)
  have hf'N : f' ∈ corrN A E t := corrM_le_corrN (graph_le_corrM hf')
  have hmem : e * f * e * f ∈ corrN A E t := by
    have h1 : e * f * e⁻¹ ∈ corrN A E t := conj_mem_corrN (Subgroup.mem_sup_right he) hfN
    rw [inv_eq_of_mul_eq_one_right (S.cls.mul_self S.tri.memE he)] at h1
    exact Subgroup.mul_mem _ h1 hfN
  exact S.commute_of_mem_corrN' htY hq hmem hf'N

theorem eq_one_of_mem_of_mem_corrN [Finite G] (hq : 4 ≤ Nat.card A) {a : G} (ha : a ∈ A)
    (haN : a ∈ corrN A E t) : a = 1 := by
  obtain ⟨e, he, he1⟩ := S.cls.root.exists_ne_one S.tri.memE
  have hsN : partnerElt A E B e ∈ corrN A E t := corrM_le_corrN (S.partnerElt_mem_corrM he he1)
  have hb := conj_mem_conjSub (partnerElt A E B e) ha
  rw [S.conjSub_partnerElt he he1, (S.commute_of_mem_corrN' htY hq hsN haN).eq,
    mul_inv_cancel_right] at hb
  have hab : a ∈ A ⊓ B := ⟨ha, hb⟩
  rwa [S.cls.inf_eq_bot S.iso S.tri.memA S.tri.memB S.tri.ne, Subgroup.mem_bot] at hab

theorem commute_of_conjSub_eq [Finite G] (hq : 4 ≤ Nat.card A) {n : G} (hn : n ∈ corrN A E t)
    (hnA : conjSub A n = A) {a : G} (ha : a ∈ A) : Commute n a := by
  have h1 : n * a * n⁻¹ * a⁻¹ ∈ A := A.mul_mem (hnA ▸ conj_mem_conjSub n ha) (A.inv_mem ha)
  have h2 : n * a * n⁻¹ * a⁻¹ ∈ corrN A E t := by
    have : a * n⁻¹ * a⁻¹ ∈ corrN A E t :=
      conj_mem_corrN (Subgroup.mem_sup_left ha) (Subgroup.inv_mem _ hn)
    rw [show n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) by group]
    exact Subgroup.mul_mem _ hn this
  have h3 := S.eq_one_of_mem_of_mem_corrN htY hq h1 h2
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3

theorem conjSub_eq_of_forall_commute_quotMap [Finite G] (m : ↥(A ⊔ E ⊔ B))
    (hm : ∀ y ∈ quotMap (A ⊔ E ⊔ B) A,
      Commute (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) m) y) :
    conjSub A (m : G) = A := by
  refine S.injOn_quotMap' htY ⟨m, m.2, rfl⟩ (S.mem_triClass htY).1 ?_
  rw [quotMap_conjSub A m.2]
  exact conjSub_of_forall_commute hm

theorem exists_coords [Finite G] (hq : 4 ≤ Nat.card A) {e₀ : G} (he₀ : e₀ ∈ E)
    (he₀1 : e₀ ≠ 1) : ∃ k : ℕ, Nat.card A = 2 ^ k ∧
    ∃ φ : ↥(quotMap (A ⊔ E ⊔ B) E ⊔ quotMap (A ⊔ E ⊔ B) A) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k),
      ((quotMap (A ⊔ E ⊔ B) E).subgroupOf (quotMap (A ⊔ E ⊔ B) E ⊔
        quotMap (A ⊔ E ⊔ B) A)).map φ.toMonoidHom = upperUnipotent (GaloisField 2 k) ∧
      ((quotMap (A ⊔ E ⊔ B) A).subgroupOf (quotMap (A ⊔ E ⊔ B) E ⊔
        quotMap (A ⊔ E ⊔ B) A)).map φ.toMonoidHom = lowerUnipotent (GaloisField 2 k) ∧
      ∃ θ : (Fin 2 → GaloisField 2 k) → ↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B),
        IsNaturalModule φ θ ∧
        (∀ m : ↥(A ⊔ E ⊔ B), (m : G) ∈ corrN A E t →
          ∃ v, θ v = QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) m) ∧
        (∀ v, ∃ m : ↥(A ⊔ E ⊔ B), (m : G) ∈ corrN A E t ∧
          QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) m = θ v) ∧
        (∃ c₀ : GaloisField 2 k, c₀ ≠ 0 ∧ ∀ m : ↥(A ⊔ E ⊔ B), (m : G) = partnerElt A E B e₀ →
          θ ![c₀, 0] = QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) m) ∧
        ∀ c, ∃ f : ↥(A ⊔ E ⊔ B), (f : G) ∈ graph A t ∧
          QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) f = θ ![0, c] := by
  have hNY := S.corrN_le_sup
  obtain ⟨k, hk, φ, hφE, hφA, θ, hθ, hrange⟩ := S.exists_isNaturalModule_quot htY hq
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
  have hlift : ∀ v, ∃ m : ↥(A ⊔ E ⊔ B), (m : G) ∈ corrN A E t ∧
      QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) m = θ v := by
    intro v
    have h1 : θ v ∈ (corrN (quotMap (A ⊔ E ⊔ B) A) (quotMap (A ⊔ E ⊔ B) E)
        (QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) ⟨t, htY⟩) : Set _) :=
      hrange ▸ ⟨v, rfl⟩
    rw [SetLike.mem_coe, ← S.quotMap_corrN htY] at h1
    exact exists_of_mem_quotMap h1
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
    exact (congrArg Subtype.val (h2 ⟨a, hAY ha⟩)).symm
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
      rw [hT, hinj.ncard_image, ← S.card_graph, ← card_subgroupOf_of_le S.graph_le_sup]
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
  refine ⟨k, hk, φ, hφE, hφA, θ, hθ, hθN, hlift, ⟨c₀, hc₀0, fun m hm => ?_⟩, hF⟩
  rw [show m = s from Subtype.ext hm, hc₀]


theorem exists_torus [Finite G] (hq : 4 ≤ Nat.card A) :
    ∃ h ∈ A ⊔ E, conjSub A h = A ∧ conjSub B h ≠ B ∧
      (∀ f ∈ graph A t, ∃ f' ∈ graph A t, Commute (f'⁻¹ * (h * f * h⁻¹)) h) ∧
      ∀ n ∈ corrN A E t, conjSub A n = A ∨ ∃ j : ℕ, conjSub A n = conjSub B (h ^ j) := by
  classical
  have hNY := S.corrN_le_sup
  obtain ⟨e₀, he₀, he₀1⟩ := S.cls.root.exists_ne_one S.tri.memE
  obtain ⟨k, hk, φ, hφE, hφA, θ, hθ, hθN, -, ⟨c₀, hc₀0, hc₀⟩, hF⟩ :=
    S.exists_coords htY hq he₀ he₀1
  have hsN : partnerElt A E B e₀ ∈ corrN A E t :=
    corrM_le_corrN (S.partnerElt_mem_corrM he₀ he₀1)
  have hsB : conjSub A (partnerElt A E B e₀) = B := S.conjSub_partnerElt he₀ he₀1
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := (GaloisField 2 k)ˣ)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [hk] at hq
    norm_num at hq
  have hμ1 : μ ≠ 1 := by
    intro h1
    have hall : ∀ u : (GaloisField 2 k)ˣ, u = 1 := fun u => by
      have := hμ u
      rwa [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
    let _ : Fintype (GaloisField 2 k) := Fintype.ofFinite _
    have h2 : Fintype.card (GaloisField 2 k)ˣ = 1 := Fintype.card_eq_one_iff.2 ⟨1, hall⟩
    rw [Fintype.card_units] at h2
    have h3 : Fintype.card (GaloisField 2 k) = Nat.card A := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 k hk0, hk]
    omega
  have hx₀X : ((φ.symm (diagElt μ) : ↥(quotMap (A ⊔ E ⊔ B) E ⊔ quotMap (A ⊔ E ⊔ B) A)) :
      ↥(A ⊔ E ⊔ B) ⧸ Subgroup.center ↥(A ⊔ E ⊔ B)) ∈ quotMap (A ⊔ E ⊔ B) (A ⊔ E) := by
    rw [TriangleSetting.quotMap_sup_left, sup_comm (quotMap (A ⊔ E ⊔ B) A)]
    exact (φ.symm (diagElt μ)).2
  obtain ⟨h₀, hh₀X, hh₀⟩ := exists_of_mem_quotMap hx₀X
  have hφx₀ : φ (φ.symm (diagElt μ)) = diagElt μ := MulEquiv.apply_symm_apply φ _
  have hinj := S.injOn_quotMap' htY
  have hfixA := S.conjSub_eq_of_forall_commute_quotMap htY
  have hθ0 : ∀ c, ∀ y ∈ quotMap (A ⊔ E ⊔ B) A, Commute (θ ![0, c]) y := fun c y hy =>
    ((hθ.forall_commute_lower_iff hφA le_sup_right _).2 (by simp) y hy).symm
  have hhA : conjSub A (h₀ : G) = A := by
    refine hinj ⟨h₀, h₀.2, rfl⟩ (S.mem_triClass htY).1 ?_
    rw [quotMap_conjSub A h₀.2]
    show conjSub (quotMap (A ⊔ E ⊔ B) A) (QuotientGroup.mk' _ h₀) = _
    rw [hh₀, conjSub_eq_self_iff]
    refine NaturalModule.coe_mem_normalizer hφA le_sup_right ?_
    rw [hφx₀]
    exact diagElt_mem_normalizer_lowerUnipotent μ
  have hact : ∀ (j : ℕ) (m : ↥(A ⊔ E ⊔ B)) (v : Fin 2 → GaloisField 2 k),
      θ v = QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) m →
      θ ![((μ ^ j : (GaloisField 2 k)ˣ) : GaloisField 2 k) * v 0,
        (((μ ^ j)⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) * v 1] =
      QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) (h₀ ^ j * m * (h₀ ^ j)⁻¹) := by
    intro j m v hv
    have h1 := hθ.map_mulVec (φ.symm (diagElt μ) ^ j) v
    rw [map_pow, hφx₀, diagElt_pow, diagElt_mulVec] at h1
    rw [h1, map_mul, map_mul, map_inv, map_pow, hh₀, ← hv]
    simp
  set s : ↥(A ⊔ E ⊔ B) := ⟨partnerElt A E B e₀, hNY hsN⟩ with hs_def
  have hs := hc₀ s rfl
  have hcases : ∀ n ∈ corrN A E t, conjSub A n = A ∨
      ∃ j : ℕ, conjSub A n = conjSub B ((h₀ : G) ^ j) := by
    intro n hn
    obtain ⟨v, hv⟩ := hθN ⟨n, hNY hn⟩ hn
    by_cases hv0 : v 0 = 0
    · left
      refine hfixA ⟨n, hNY hn⟩ fun y hy => ?_
      rw [← hv]
      exact ((hθ.forall_commute_lower_iff hφA le_sup_right v).2 hv0 y hy).symm
    · right
      obtain ⟨j, hj⟩ : ∃ j : ℕ, μ ^ j = Units.mk0 (v 0 / c₀) (div_ne_zero hv0 hc₀0) := by
        have := hμ (Units.mk0 (v 0 / c₀) (div_ne_zero hv0 hc₀0))
        rw [← mem_powers_iff_mem_zpowers] at this
        obtain ⟨j, hj⟩ := this
        exact ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have hn' := hact j s _ hs
      have hm' : conjSub A (((h₀ ^ j * s * (h₀ ^ j)⁻¹)⁻¹ * ⟨n, hNY hn⟩ : ↥(A ⊔ E ⊔ B)) : G) =
          A := by
        refine hfixA _ fun y hy => ?_
        have : QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))
            ((h₀ ^ j * s * (h₀ ^ j)⁻¹)⁻¹ * ⟨n, hNY hn⟩) = θ ![0, v 1] := by
          rw [map_mul, map_inv, ← hn', ← hv, ← hθ.map_neg, ← hθ.map_add]
          congr 1
          ext i
          fin_cases i
          · simp [hj, div_mul_cancel₀ _ hc₀0]
          · simp
        rw [this]
        exact hθ0 _ y hy
      have hsplit : n = ((h₀ ^ j * s * (h₀ ^ j)⁻¹ : ↥(A ⊔ E ⊔ B)) : G) *
          (((h₀ ^ j * s * (h₀ ^ j)⁻¹)⁻¹ * ⟨n, hNY hn⟩ : ↥(A ⊔ E ⊔ B)) : G) := by
        rw [← Subgroup.coe_mul, mul_inv_cancel_left]
      rw [hsplit, conjSub_mul, hm']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow]
      exact conjSub_conj_eq (conjSub_pow_eq hhA j) hsB
  refine ⟨h₀, hh₀X, hhA, fun hBh => ?_, fun f hf => ?_, hcases⟩
  ·
    have h1 : conjSub A ((h₀ : G) * partnerElt A E B e₀ * (h₀ : G)⁻¹) = B := by
      rw [conjSub_conj_eq hhA hsB, hBh]
    have hm : conjSub A ((partnerElt A E B e₀)⁻¹ * ((h₀ : G) * partnerElt A E B e₀ *
        (h₀ : G)⁻¹)) = A := by
      have h2 := Aux.conjSub_conjSub_inv A (partnerElt A E B e₀)
      rw [hsB] at h2
      rw [conjSub_mul, h1, h2]
    have hmN : (partnerElt A E B e₀)⁻¹ * ((h₀ : G) * partnerElt A E B e₀ * (h₀ : G)⁻¹) ∈
        corrN A E t :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hsN) (conj_mem_corrN hh₀X hsN)
    have hc := fun a (ha : a ∈ A) => S.commute_of_conjSub_eq htY hq hmN hm ha
    have hn' := hact 1 s _ hs
    have hmk : θ (-![c₀, 0] + ![((μ ^ 1 : (GaloisField 2 k)ˣ) : GaloisField 2 k) * c₀,
        (((μ ^ 1)⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) * 0]) =
        QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B)) (s⁻¹ * (h₀ ^ 1 * s * (h₀ ^ 1)⁻¹)) := by
      rw [hθ.map_add, hθ.map_neg, map_mul, map_inv, hs, ← hn']
      rfl
    have hcomm := (hθ.forall_commute_lower_iff hφA le_sup_right _).1 fun b hb => by
      obtain ⟨a, ha, rfl⟩ := exists_of_mem_quotMap hb
      rw [hmk]
      refine Commute.map (Subtype.ext ?_) _
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, pow_one]
      exact (hc a ha).symm
    simp only [pow_one, Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero] at hcomm
    apply hμ1
    have h2 : ((μ : GaloisField 2 k) - 1) * c₀ = 0 := by linear_combination hcomm
    have h3 : (μ : GaloisField 2 k) = 1 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h hc₀0
    exact Units.val_eq_one.1 h3
  ·
    set fY : ↥(A ⊔ E ⊔ B) := ⟨f, S.graph_le_sup hf⟩ with hfY
    obtain ⟨c, hc⟩ := (hθ.mem_fixed_lower_iff hφA le_sup_right).1
      ⟨hθN fY (corrM_le_corrN (graph_le_corrM hf)), fun a ha => by
        obtain ⟨a', ha', rfl⟩ := exists_of_mem_quotMap ha
        exact Commute.map (show Commute a' fY from
          Subtype.ext (S.commute_graph_left hf ha').symm) _⟩
    obtain ⟨f', hf', hf'c⟩ := hF ((((μ ^ 1)⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) * c)
    refine ⟨f', hf', ?_⟩
    have h1 := hact 1 fY ![0, c] hc
    have hz : f'⁻¹ * (h₀ ^ 1 * fY * (h₀ ^ 1)⁻¹) ∈ Subgroup.center ↥(A ⊔ E ⊔ B) := by
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' (Subgroup.center ↥(A ⊔ E ⊔ B))
        (f'⁻¹ * (h₀ ^ 1 * fY * (h₀ ^ 1)⁻¹)) = 1
      rw [map_mul, map_inv, ← h1, hf'c]
      simp
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz h₀)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, pow_one] at h2
    exact h2.symm

end TriangleSetting

end CFSG.Timmesfeld.Transvection
