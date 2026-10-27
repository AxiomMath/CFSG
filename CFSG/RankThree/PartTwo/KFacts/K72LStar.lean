module

public import CFSG.RankThree.PartTwo.KFacts.K72Transvection
public import CFSG.RankThree.PartTwo.KFacts.K72Lift
public import CFSG.RankThree.PartTwo.KFacts.K73Lines
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_theta {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    {y : G} (hy : y ∈ (aschbacherSolvableCore 3 L).map L.subtype) :
    g * y * g⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype := by
  obtain ⟨y', hy', rfl⟩ := hy
  have h1 : L.normalizerMonoidHom ⟨g, hg⟩ y' ∈ aschbacherSolvableCore 3 L := by
    rw [← map_aschbacherSolvableCore (L.normalizerMonoidHom ⟨g, hg⟩)]
    exact ⟨y', hy', rfl⟩
  exact ⟨_, h1, rfl⟩

theorem normalizer_le_normalizer_theta (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer
        (((aschbacherSolvableCore 3 L).map L.subtype : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact conj_mem_theta hg
  · intro hy
    have h1 := conj_mem_theta (Subgroup.inv_mem _ hg) hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at h1

omit [Finite G] in
theorem closure_le_normalizer {L : Subgroup G} {c a d : G} (hc3 : c ^ 3 = 1)
    (hLc : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype)
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (hdL : d ∈ L) :
    Subgroup.closure {c, a, d} ≤ Subgroup.normalizer (L : Set G) := by
  have hθL : (aschbacherSolvableCore 3 L).map L.subtype ≤ L := Subgroup.map_subtype_le _
  have hfw : ∀ z ∈ L, c * z * c⁻¹ ∈ L := fun z hz => by
    have e1 : c * z * c⁻¹ = (c * z * c⁻¹ * z⁻¹) * z := by group
    rw [e1]
    exact L.mul_mem (hθL (hLc z hz)) hz
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hfw y, fun hy => ?_⟩
    have hccc : c * c * c = 1 := by rw [← pow_two, ← pow_succ, hc3]
    have e2 : y = c * (c * (c * y * c⁻¹) * c⁻¹) * c⁻¹ := by
      calc y = (c * c * c) * y * (c * c * c)⁻¹ := by rw [hccc]; group
        _ = c * (c * (c * y * c⁻¹) * c⁻¹) * c⁻¹ := by group
    rw [e2]
    exact hfw _ (hfw _ hy)
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact hcN
  · exact haN
  · exact Subgroup.le_normalizer hdL

theorem exists_threeElement_moving_of_inducesKindPSL2 {A L : Subgroup G} {c a d : G}
    {K : Type} [Field K] [Finite K] (h3K : (3 : K) ≠ 0)
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A) (haA : a ∈ A) (hdA : d ∈ A)
    (hA : A = Subgroup.closure {c, a, d})
    (hLc : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype)
    (hdL : d ∈ L) (hd1 : d ≠ 1)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 K)
    (ha : InducesKind L (stdPinnedPSL2 K) e a .field) :
    ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), (∃ k : ℕ, l ^ 3 ^ k = 1) ∧
      ∃ x ∈ A, l * x * l⁻¹ ≠ x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ' := (aschbacherSolvableCore 3 L).map L.subtype with hθ'
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hθ3 : ¬ 3 ∣ Nat.card θ' := by
    rw [hθ', Subgroup.card_map_of_injective L.subtype_injective]
    exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hθL : θ' ≤ L := Subgroup.map_subtype_le _
  have hdisj := inf_eq_bot_of_coprime hA3 hθ3
  have hAθ1 : ∀ y ∈ A, y ∈ θ' → y = 1 := fun y hy hyθ => by
    have : y ∈ A ⊓ θ' := ⟨hy, hyθ⟩
    rwa [hdisj, Subgroup.mem_bot] at this
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hexp d hdA) hd1
  obtain ⟨haN, hfield⟩ := ha
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := by
    rw [hA]
    exact closure_le_normalizer (hexp c hcA) hLc haN hdL
  have hAθ : A ≤ Subgroup.normalizer (θ' : Set G) := hAN.trans (normalizer_le_normalizer_theta L)
  set τ₀ := thetaQuotMulAut L (compAction L ⟨a, haN⟩) with hτ₀
  set α := inducedAutHom L e ⟨a, haN⟩ with hαdef
  have hα : ∀ y, α (e y) = e (τ₀ y) := fun y => by
    show e (τ₀ (e.symm (e y))) = e (τ₀ y)
    rw [MulEquiv.symm_apply_apply]
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hexp a haA)
    rw [hαdef, ← map_pow, h1, map_one]
  obtain ⟨φ, ⟨σ, rfl⟩, hφ1, δ, -, hαδ⟩ := hfield
  have hσ3 : orderOf σ = 3 := by
    have hφ3 : psl2FieldAut K σ ^ 3 = 1 := by
      have h1 : (δ * psl2FieldAut K σ * δ⁻¹) ^ 3 = δ * psl2FieldAut K σ ^ 3 * δ⁻¹ := conj_pow
      rw [← hαδ, hα3] at h1
      calc psl2FieldAut K σ ^ 3 = δ⁻¹ * (δ * psl2FieldAut K σ ^ 3 * δ⁻¹) * δ := by group
        _ = 1 := by rw [← h1]; group
    rw [← orderOf_injective (psl2FieldAut K) (psl2FieldAut_injective K) σ]
    exact orderOf_eq_prime hφ3 hφ1
  set dl : L := ⟨d, hdL⟩ with hdl
  set db : L ⧸ aschbacherSolvableCore 3 L := (dl : L ⧸ aschbacherSolvableCore 3 L) with hdb
  have hτd : τ₀ db = db := by
    rw [hdb, hτ₀, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    show a * d * a⁻¹ = d
    rw [hcomm a haA d hdA, mul_inv_cancel_right]
  have hdb3 : db ^ 3 = 1 := by
    rw [hdb, ← QuotientGroup.mk_pow]
    have : dl ^ 3 = 1 := Subtype.ext (by simpa using hexp d hdA)
    rw [this, QuotientGroup.mk_one]
  have hdb1 : db ≠ 1 := by
    intro h1
    rw [hdb, QuotientGroup.eq_one_iff] at h1
    exact hd1 (hAθ1 d hdA ⟨dl, h1, rfl⟩)
  set d'' := δ⁻¹ (e db) with hd''
  have hd''σ : psl2FieldAut K σ d'' = d'' := by
    have h1 : α (e db) = e db := by rw [hα, hτd]
    rw [hαδ] at h1
    have h2 : δ (psl2FieldAut K σ (δ⁻¹ (e db))) = e db := h1
    have h3 := congrArg (δ⁻¹ : MulAut (PSL2 K)) h2
    rwa [MulAut.inv_apply_self] at h3
  have hd''3 : d'' ^ 3 = 1 := by rw [hd'', ← map_pow, ← map_pow, hdb3, map_one, map_one]
  have hd''1 : d'' ≠ 1 := by
    intro h1
    apply hdb1
    apply e.injective
    rw [map_one]
    have h2 := congrArg δ h1
    rwa [hd'', MulAut.apply_inv_self, map_one] at h2
  obtain ⟨y'', hy''d, hy''σ⟩ := exists_psl_commute_mul_inv_eq_sq h3K hσ3 hd''3 hd''1 hd''σ
  set xb := e.symm (δ y'') with hxb
  have hxbd : xb * db = db * xb := by
    apply e.injective
    rw [map_mul, map_mul, hxb, MulEquiv.apply_symm_apply]
    have h1 : e db = δ d'' := by rw [hd'', MulAut.apply_inv_self]
    rw [h1, ← map_mul, ← map_mul, hy''d]
  have hxbτ : xb * (τ₀ xb)⁻¹ = db ^ 2 := by
    apply e.injective
    rw [map_mul, map_inv, ← hα, hxb, MulEquiv.apply_symm_apply, map_pow]
    have h1 : e db = δ d'' := by rw [hd'', MulAut.apply_inv_self]
    rw [h1, hαδ]
    show δ y'' * (δ (psl2FieldAut K σ (δ⁻¹ (δ y''))))⁻¹ = (δ d'') ^ 2
    rw [MulAut.inv_apply_self, ← map_inv, ← map_mul, hy''σ, map_pow]
  obtain ⟨xl, hxl⟩ := QuotientGroup.mk_surjective xb
  set x : G := (xl : G) with hx
  have hxL : x ∈ L := xl.2
  have hR1 : (x * d * x⁻¹)⁻¹ * d ∈ θ' := by
    have h1 : ((xl * dl * xl⁻¹ : L) : L ⧸ aschbacherSolvableCore 3 L) =
        (dl : L ⧸ aschbacherSolvableCore 3 L) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxl, ← hdb, hxbd,
        mul_inv_cancel_right]
    exact ⟨_, QuotientGroup.eq.mp h1, rfl⟩
  have hR2 : (x * (a * x * a⁻¹)⁻¹)⁻¹ * d ^ 2 ∈ θ' := by
    set al := compAction L ⟨a, haN⟩ xl with hal
    have hal' : (al : G) = a * x * a⁻¹ := Sec4.normalizerMonoidHom_apply_coe haN xl
    have h1 : ((xl * al⁻¹ : L) : L ⧸ aschbacherSolvableCore 3 L) =
        ((dl ^ 2 : L) : L ⧸ aschbacherSolvableCore 3 L) := by
      have h2 : (al : L ⧸ aschbacherSolvableCore 3 L) = τ₀ xb := by
        rw [hτ₀, ← hxl, thetaQuotMulAut_mk]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxl, QuotientGroup.mk_pow, ← hdb, h2, hxbτ]
    refine ⟨_, QuotientGroup.eq.mp h1, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow,
      hal']
    rfl
  set w₁ := (x * d * x⁻¹)⁻¹ * d with hw₁
  set w₂ := (x * (a * x * a⁻¹)⁻¹)⁻¹ * d ^ 2 with hw₂
  set w₀ := c * x * c⁻¹ * x⁻¹ with hw₀
  have hw₀θ : w₀ ∈ θ' := hLc x hxL
  have hxd : x * d * x⁻¹ = d * w₁⁻¹ := by rw [hw₁]; group
  have hxa : x * a * x⁻¹ = d ^ 2 * w₂⁻¹ * a := by rw [hw₂]; group
  have hxc : x * c * x⁻¹ = w₀⁻¹ * c := by rw [hw₀]; group
  have hxA : ∀ y ∈ A, x * y * x⁻¹ ∈ A ⊔ θ' := by
    have hle : Subgroup.closure ({c, a, d} : Set G) ≤
        (A ⊔ θ').comap (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy | hy <;> rw [hy]
      · show x * c * x⁻¹ ∈ A ⊔ θ'
        rw [hxc]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ hw₀θ))
          (Subgroup.mem_sup_left hcA)
      · show x * a * x⁻¹ ∈ A ⊔ θ'
        rw [hxa]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (A.pow_mem hdA 2))
          (Subgroup.mem_sup_right (Subgroup.inv_mem _ hR2))) (Subgroup.mem_sup_left haA)
      · show x * d * x⁻¹ ∈ A ⊔ θ'
        rw [hxd]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hdA)
          (Subgroup.mem_sup_right (Subgroup.inv_mem _ hR1))
    intro y hy
    rw [hA] at hy
    exact hle hy
  obtain ⟨t, ht, hlN, hact⟩ := exists_mul_mem_normalizer hA3 hθ3 hAθ hxA
  set l := t * x with hl
  have hlL : l ∈ L := L.mul_mem (hθL ht) hxL
  have hdθ : ∀ w ∈ θ', ∀ n : ℕ, d ^ n * w * (d ^ n)⁻¹ ∈ θ' := fun w hw n =>
    conj_mem_theta (Subgroup.le_normalizer (L.pow_mem hdL n)) hw
  have hld : l * d * l⁻¹ = d := by
    have hz : l * d * l⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hlN d).mp hdA
    have h1 := hact d hdA
    rw [hxd] at h1
    have h2 : l * d * l⁻¹ * d⁻¹ ∈ θ' := by
      have e : l * d * l⁻¹ * d⁻¹ = (l * d * l⁻¹ * (d * w₁⁻¹)⁻¹) * (d ^ 1 * w₁⁻¹ * (d ^ 1)⁻¹) := by
        group
      rw [e]
      exact θ'.mul_mem h1 (hdθ _ (θ'.inv_mem hR1) 1)
    have h3 := hAθ1 _ (A.mul_mem hz (A.inv_mem hdA)) h2
    calc l * d * l⁻¹ = l * d * l⁻¹ * d⁻¹ * d := by group
      _ = d := by rw [h3, one_mul]
  have hla : l * a * l⁻¹ = a * d ^ 2 := by
    have hz : l * a * l⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hlN a).mp haA
    have h1 := hact a haA
    rw [hxa] at h1
    have h2 : l * a * l⁻¹ * a⁻¹ * (d ^ 2)⁻¹ ∈ θ' := by
      have e : l * a * l⁻¹ * a⁻¹ * (d ^ 2)⁻¹ =
          (l * a * l⁻¹ * (d ^ 2 * w₂⁻¹ * a)⁻¹) * (d ^ 2 * w₂⁻¹ * (d ^ 2)⁻¹) := by group
      rw [e]
      exact θ'.mul_mem h1 (hdθ _ (θ'.inv_mem hR2) 2)
    have h3 := hAθ1 _ (A.mul_mem (A.mul_mem hz (A.inv_mem haA)) (A.inv_mem (A.pow_mem hdA 2))) h2
    have h4 : l * a * l⁻¹ = d ^ 2 * a := by
      calc l * a * l⁻¹ = l * a * l⁻¹ * a⁻¹ * (d ^ 2)⁻¹ * (d ^ 2 * a) := by group
        _ = d ^ 2 * a := by rw [h3, one_mul]
    rw [h4, hcomm _ (A.pow_mem hdA 2) a haA]
  obtain ⟨v, m, hm3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (orderOf_pos_iff.mpr (isOfFinOrder_of_finite l)).ne' 3 (by norm_num)
  refine ⟨l ^ m, ⟨L.pow_mem hlL m, Subgroup.pow_mem _ hlN m⟩, ⟨v, ?_⟩, a, haA, ?_⟩
  · rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  · have hld2 : l * d ^ 2 = d ^ 2 * l := by
      have hc : Commute l d := by
        calc l * d = l * d * l⁻¹ * l := by group
          _ = d * l := by rw [hld]
      exact (hc.pow_right 2).eq
    rw [KFacts.conj_pow_eq_mul_pow hla hld2 m]
    intro h
    have h1 : (d ^ 2) ^ m = 1 := by
      calc (d ^ 2) ^ m = a⁻¹ * (a * (d ^ 2) ^ m) := by group
        _ = 1 := by rw [h, inv_mul_cancel]
    rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hd3] at h1
    exact hm3 ((Nat.Prime.dvd_mul Nat.prime_three).mp h1 |>.resolve_left (by norm_num))

end CFSG.RankThree.PartTwo.KFacts
