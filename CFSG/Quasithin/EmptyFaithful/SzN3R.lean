module

public import CFSG.Quasithin.EmptyFaithful.S153F18B
public import CFSG.Quasithin.EmptyFaithful.S153F18C
public import CFSG.Quasithin.EmptyFaithful.S153F19

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

section Model

variable {W : Type} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem szN3_fpf_mul (h : OfourStruct X L₁ L₂ t) {a b : MulAut W} (ha : a ∈ L₁) (hb : b ∈ L₂)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) :
    ∀ w : W, (a * b) w = w → w = 1 := by
  intro w hw
  obtain ⟨hwa, hwb⟩ := h.fix_of_fix_mul ha hb hw
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := h.exists_decomp_W w
  have e1 : b u₁ = u₁ := h.L₂_fix₁ hb hu₁
  have e2 : a u₂ = u₂ := h.L₁_fix₂ ha hu₂
  have hau : a u₁ = u₁ := by
    have h' : a (u₁ * u₂) = a u₁ * u₂ := by rw [map_mul, e2]
    rw [h'] at hwa
    exact mul_right_cancel hwa
  have hbu : b u₂ = u₂ := by
    have h' : b (u₁ * u₂) = u₁ * b u₂ := by rw [map_mul, e1]
    rw [h'] at hwb
    exact mul_left_cancel hwb
  have hodd : ∀ {c : MulAut W}, c ^ 3 = 1 → Odd (orderOf c) := fun hc =>
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hc)
  have hu₁1 : u₁ = 1 := by
    by_contra hne
    exact ha1 (eq_one_of_odd_of_fixed h.nat₁ (fun l hl u hu => commV_stable L₁ hl hu) ha
      (hodd ha3) hu₁ hne hau)
  have hu₂1 : u₂ = 1 := by
    by_contra hne
    exact hb1 (eq_one_of_odd_of_fixed h.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) hb
      (hodd hb3) hu₂ hne hbu)
  rw [hu₁1, hu₂1, one_mul]

end Model

section Generic

variable {G : Type} [Group G]

theorem szN3_le_or_le_of_forall {H K₁ K₂ : Subgroup G} (h : ∀ x ∈ H, x ∈ K₁ ∨ x ∈ K₂) :
    H ≤ K₁ ∨ H ≤ K₂ := by
  by_contra hno
  push Not at hno
  obtain ⟨hn1, hn2⟩ := hno
  obtain ⟨x, hxH, hxK₁⟩ := IsConcreteLE.not_le_iff_exists.mp hn1
  obtain ⟨y, hyH, hyK₂⟩ := IsConcreteLE.not_le_iff_exists.mp hn2
  have hx2 : x ∈ K₂ := (h x hxH).resolve_left hxK₁
  have hy1 : y ∈ K₁ := (h y hyH).resolve_right hyK₂
  rcases h (x * y) (H.mul_mem hxH hyH) with h1 | h2
  · apply hxK₁
    have := K₁.mul_mem h1 (K₁.inv_mem hy1)
    simpa using this
  · apply hyK₂
    have := K₂.mul_mem (K₂.inv_mem hx2) h2
    simpa using this

end Generic

section Context

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem szN3_VZ_le_normalizer_L (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) :
    VZ T M ≤ Subgroup.normalizer (L : Set G) := by
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hVR : VZ T M ≤ R153 T V₁ Yp := by
    rw [c.facts.R_eq]
    refine le_inf hh.hyp.VZ_le_T fun v hv => Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have := hh.hyp.elemAbelian.1
    exact setLike_mul_comm hw hv
  exact hVR.trans c.c16.R_norm

theorem szN3_core_eq (h113 : StageLemma14113) (hyp : Hyp153 G T Mc M)
    (hE9 : IsElemAbelianOfRank 3 2 (OTwoQuot (Y153 Mc M))) :
    pCoreOf 2 (Y153 Mc M) = Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  rcases Hyp153.lemma_15_3_7_cases h113 hyp with ⟨hcore, -⟩ | ⟨hP, -⟩
  · exact hcore
  · exfalso
    have h9 := S153F.card_eq_nine_of_isElemAbelianOfRank hE9
    have h27 := hP.2.1
    rw [h9] at h27
    norm_num at h27

end Context

section UBlock

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem szN3_blockU_le_of_Z {L Y' : Subgroup G} {n : ℕ} (hL : IsLin2Type L n)
    (hZ : blockZ L ≤ Y') (hY'L : Y' ≤ L)
    (hUN : blockU L ≤ Subgroup.normalizer (Y' : Set G)) {x : G} (hxY : x ∈ Y')
    (hxo : Odd (orderOf x)) (hx1 : x ≠ 1) : blockU L ≤ Y' := by
  classical
  have hxL : x ∈ L := hY'L hxY
  have hxU : x ∈ Subgroup.normalizer (blockU L : Set G) :=
    S153F.mem_normalizer_blockU (Subgroup.le_normalizer hxL)
  have hconjU : ∀ u : ↥(blockU L), x * (u : G) * x⁻¹ ∈ blockU L := fun u =>
    (Subgroup.mem_normalizer_iff.mp hxU u).mp u.2
  obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, β, hβs, hβk, hβc⟩ := hL
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    rw [hcard] at this
    simp at this
  have h2 : (2 : F) = 0 := by
    have h0 : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
    rw [hcard] at h0
    push_cast at h0
    exact (pow_eq_zero_iff hn0).mp h0
  set A : Matrix (Fin 2) (Fin 2) F := (α ⟨x, hxL⟩ : Matrix (Fin 2) (Fin 2) F) with hA
  have hβconj : ∀ u : ↥(blockU L), β ⟨x * (u : G) * x⁻¹, hconjU u⟩ =
      Multiplicative.ofAdd (A.mulVec (Multiplicative.toAdd (β u))) := by
    intro u
    have := hβc ⟨x, hxL⟩ u ⟨x * (u : G) * x⁻¹, hconjU u⟩ rfl
    rw [← this]
    simp
  have hnofix : ∀ w : Fin 2 → F, A.mulVec w = w → w = 0 := by
    intro w hw
    by_contra hw0
    let ℓ : ↥L := ⟨x, hxL⟩
    have hsq := S153F.sl2_sq_eq_one_of_fixed h2 (α ℓ) w hw0 hw
    have hd1 : orderOf (α ℓ) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have hd2 : orderOf (α ℓ) ∣ orderOf x := by
      have := orderOf_map_dvd α ℓ
      rwa [Subgroup.orderOf_mk x hxL] at this
    have hodd : Odd (orderOf (α ℓ)) := Odd.of_dvd_nat hxo hd2
    have hk : orderOf (α ℓ) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hd1 with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    have hα1 : α ℓ = 1 := orderOf_eq_one_iff.mp hk
    have hℓ : ℓ ∈ CFSG.pCore 2 ↥L := hαk ▸ MonoidHom.mem_ker.mpr hα1
    obtain ⟨k, hk2⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L)) ⟨ℓ, hℓ⟩
    have hpow : ℓ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk2
    have hdy : orderOf x ∣ 2 ^ k := by
      have := orderOf_dvd_of_pow_eq_one hpow
      rwa [Subgroup.orderOf_mk x hxL] at this
    have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hxo)
    exact hx1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdy))
  let φ : (Fin 2 → F) → (Fin 2 → F) := fun v => A.mulVec v - v
  have hinj : Function.Injective φ := by
    intro v v' hvv
    have hw : A.mulVec (v - v') = v - v' := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_sub_iff_sub_eq_sub.mp hvv
    exact sub_eq_zero.mp (hnofix _ hw)
  have hsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hinj
  intro u₀ hu₀
  obtain ⟨v, hv⟩ := hsurj (Multiplicative.toAdd (β ⟨u₀, hu₀⟩))
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd v)
  have hβeq : β (⟨x * (u : G) * x⁻¹, hconjU u⟩ * u⁻¹) = β ⟨u₀, hu₀⟩ := by
    rw [map_mul, map_inv, hβconj, hu]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
    rw [← hv]
    simp [φ, sub_eq_add_neg]
  have hker : (⟨x * (u : G) * x⁻¹, hconjU u⟩ * u⁻¹)⁻¹ * ⟨u₀, hu₀⟩ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβeq, inv_mul_cancel]
  rw [hβk] at hker
  have hzZ := Subgroup.mem_subgroupOf.mp hker
  have hzY : (x * (u : G) * x⁻¹ * (u : G)⁻¹)⁻¹ * u₀ ∈ Y' := hZ hzZ
  have h1 : (u : G) * x⁻¹ * (u : G)⁻¹ ∈ Y' :=
    (Subgroup.mem_normalizer_iff.mp (hUN u.2) x⁻¹).mp (Y'.inv_mem hxY)
  have hcom : x * (u : G) * x⁻¹ * (u : G)⁻¹ ∈ Y' := by
    have e : x * (u : G) * x⁻¹ * (u : G)⁻¹ = x * ((u : G) * x⁻¹ * (u : G)⁻¹) := by group
    rw [e]
    exact Y'.mul_mem hxY h1
  have e : u₀ = (x * (u : G) * x⁻¹ * (u : G)⁻¹) * ((x * (u : G) * x⁻¹ * (u : G)⁻¹)⁻¹ * u₀) := by
    group
  rw [e]
  exact Y'.mul_mem hcom hzY

end UBlock

@[expose] def Lin2ZLInYL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
      Yp = Y153 Mc M → ¬ YL153 Yp L ≤ Subgroup.centralizer (VZ T M : Set G) →
        blockZ L ≤ YL153 Yp L

section Final2

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem szN3_le_centralizer_of_YL_noZ (kS : Lin2Setup)
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hn : ∃ n : ℕ, 1 < n ∧ IsLin2Type L n)
    {V' : Subgroup G} (hV' : V' ≤ VZ T M)
    (hYLV' : YL153 Yp L ≤ Subgroup.centralizer (V' : Set G)) :
    V' ≤ Subgroup.centralizer (L : Set G) := by
  obtain ⟨-, -, hVdec⟩ := kS G T Mc M V₁ V₂ Yp I L t c hn
  obtain ⟨y, hyY, hyo, hy1⟩ : ∃ y ∈ Yp ⊓ L, Odd (orderOf y) ∧ y ≠ 1 := by
    by_contra hno
    push Not at hno
    apply c.c16.YL_ne
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, ho⟩
    exact Subgroup.mem_bot.mpr (hno x hx ho)
  have hyYL : y ∈ YL153 Yp L := mem_oTwoUpper_of_odd hyY hyo
  obtain ⟨n, -, hnL⟩ := hn
  intro v hv
  obtain ⟨a, ha, b, hb, hvab⟩ := hVdec v (hV' hv)
  have hyv : v * y = y * v := Subgroup.mem_centralizer_iff.mp (hYLV' hyYL) v hv
  have hyb : y * b = b * y := Subgroup.mem_centralizer_iff.mp hb y hyY.2
  have hay : a * y = y * a := by
    have h3 : a * y * b = y * a * b := by
      calc a * y * b = a * (y * b) := by group
        _ = a * (b * y) := by rw [hyb]
        _ = a * b * y := by group
        _ = v * y := by rw [← hvab]
        _ = y * v := hyv
        _ = y * (a * b) := by rw [← hvab]
        _ = y * a * b := by group
    exact mul_right_cancel h3
  have hya : y * a * y⁻¹ = a := by
    rw [← hay]
    group
  have haC := S153F.lin2NatFixedPoints_proved G L n hnL y hyY.2 hyo hy1 a ha.1 hya
  rw [hvab]
  exact mul_mem haC hb

end Final2

end CFSG.Quasithin
