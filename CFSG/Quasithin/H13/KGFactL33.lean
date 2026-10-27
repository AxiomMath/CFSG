module

public import CFSG.Quasithin.H13.A5S136o
public import CFSG.Quasithin.H13.KGFactL33Mat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutFinal
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 Matrix

namespace KGL33

theorem eq_of_mem_centralizer_sylow {H : Type*} [Group H] [Finite H] {T W D : H}
    (h2 : IsPGroup 2 (Subgroup.closure {T, W}))
    (hC : ∀ g : H, g * T = T * g → g * W = W * g → g = 1 ∨ g = D) (P : Sylow 2 H) {x y : H}
    (hx : ∀ t ∈ (P : Subgroup H), x * t = t * x) (hy : ∀ t ∈ (P : Subgroup H), y * t = t * y)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := h2.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H P₀ P
  have hPeq : (P : Subgroup H) = (P₀ : Subgroup H).map (MulAut.conj h).toMonoidHom := by
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hmem : ∀ s ∈ (Subgroup.closure {T, W} : Subgroup H), h * s * h⁻¹ ∈ (P : Subgroup H) := by
    intro s hs
    rw [hPeq]
    exact ⟨s, hP₀ hs, rfl⟩
  have hT : h * T * h⁻¹ ∈ (P : Subgroup H) := hmem T (Subgroup.subset_closure (by simp))
  have hW : h * W * h⁻¹ ∈ (P : Subgroup H) := hmem W (Subgroup.subset_closure (by simp))
  have key : ∀ u : H, (∀ t ∈ (P : Subgroup H), u * t = t * u) → u ≠ 1 → h⁻¹ * u * h = D := by
    intro u hu hu1
    have c : ∀ s : H, h * s * h⁻¹ ∈ (P : Subgroup H) →
        h⁻¹ * u * h * s = s * (h⁻¹ * u * h) := by
      intro s hs
      have e := hu _ hs
      calc h⁻¹ * u * h * s = h⁻¹ * (u * (h * s * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * s * h⁻¹) * u) * h := by rw [e]
        _ = s * (h⁻¹ * u * h) := by group
    rcases hC _ (c T hT) (c W hW) with h1 | h1
    · exfalso
      apply hu1
      calc u = h * (h⁻¹ * u * h) * h⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have e1 := key x hx hx1
  have e2 := key y hy hy1
  calc x = h * (h⁻¹ * x * h) * h⁻¹ := by group
    _ = h * (h⁻¹ * y * h) * h⁻¹ := by rw [e1, e2]
    _ = y := by group

theorem sl3_criterion {H : Type*} [Group H] {F : Type} [Field F] [Fintype F] [CharP F 3]
    (hF : Fintype.card F = 3) (φ : H ≃* SpecialLinearGroup (Fin 3) F) :
    IsPGroup 2 (Subgroup.closure {φ.symm tSL, φ.symm wSL}) ∧
      ∀ g : H, g * φ.symm tSL = φ.symm tSL * g → g * φ.symm wSL = φ.symm wSL * g →
        g = 1 ∨ g = φ.symm dSL := by
  refine ⟨?_, fun g hgt hgw => ?_⟩
  · have e : Subgroup.closure {φ.symm tSL, φ.symm wSL} =
        (Subgroup.closure {(tSL : SpecialLinearGroup (Fin 3) F), wSL}).map
          φ.symm.toMonoidHom := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [e]
    exact isPGroup_closure_tSL_wSL.map _
  · have ht : φ g * tSL = tSL * φ g := by
      have := congrArg φ hgt
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    have hw : φ g * wSL = wSL * φ g := by
      have := congrArg φ hgw
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    rcases eq_one_or_eq_dSL_of_commute hF (φ g) ht hw with h | h
    · left
      exact φ.injective (h.trans (map_one φ).symm)
    · right
      rw [← h, MulEquiv.symm_apply_apply]

theorem exists_sylow_le {G : Type*} [Group G] [Finite G] {K X Q : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hQ : IsSylowTwoOf Q X) :
    ∃ P : Sylow 2 ↥K, ∀ t ∈ (P : Subgroup ↥K), (t : G) ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hQ2, hQodd⟩ := hQ
  have hQ2' : IsPGroup 2 (Q.subgroupOf X) := hQ2.comap_subtype
  let QX : Sylow 2 ↥X := hQ2'.toSylow hQodd
  have hN : (K.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hXN g.2) (n : G)).1 hn
    simpa using this⟩
  obtain ⟨P₁, hP₁⟩ := CFSG.Glauberman.sylow_inf_normal QX (N := K.subgroupOf X)
  let eK : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
  have he : Function.Surjective eK.toMonoidHom := eK.surjective
  refine ⟨P₁.mapSurjective he, fun t ht => ?_⟩
  rw [Sylow.coe_mapSurjective] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  rw [hP₁, SetLike.mem_coe, Subgroup.mem_subgroupOf] at hs
  have hs' : (s : ↥X) ∈ (QX : Subgroup ↥X) := hs.1
  rw [IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf] at hs'
  exact hs'

@[expose] def conjK {G : Type*} [Group G] (K : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : ↥K ≃* ↥K where
  toFun x := ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg x).1 x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by
    apply (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * x * g)).2
    have e : g * (g⁻¹ * (x : G) * g) * g⁻¹ = x := by group
    rw [e]
    exact x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjK_apply {G : Type*} [Group G] (K : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (x : ↥K) :
    ((conjK K g hg x : ↥K) : G) = g * x * g⁻¹ := rfl

end KGL33

open KGL33 in
theorem factConfL33_holds : FactConfL33 := by
  intro G _ _ K X Q a z l _hqs hm hconf
  obtain ⟨hKX, hXN, hQ, haQ, hzQ, ha2, -, haC, hzC, ha1, hz1, haz, ⟨l₀, hl₀K, hl₀⟩, -, -, -, -⟩ :=
    hconf
  have hm' := hm
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm'
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : Fintype.card F = 3 := (Nat.card_eq_fintype_card (α := F)).symm.trans
    (hcard.trans (pow_one 3))
  have : CharP F 3 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  let φ : ↥K ≃* SpecialLinearGroup (Fin 3) F :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq (center_SL_eq_bot hF)).trans QuotientGroup.quotientBot)
  have hZK : ∀ x : ↥K, (∀ y : ↥K, x * y = y * x) → x = 1 := by
    intro x hx
    have h1 : φ x ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := φ.surjective g
      rw [← map_mul, ← map_mul, hx y]
    rw [center_SL_eq_bot hF, Subgroup.mem_bot] at h1
    exact φ.injective (h1.trans (map_one φ).symm)
  obtain ⟨P, hPQ⟩ := exists_sylow_le hKX hXN hQ
  have fixP : ∀ c ∈ Q, (∀ t ∈ Q, c * t * c⁻¹ * t⁻¹ ∈ Subgroup.centralizer (K : Set G)) →
      ∀ t ∈ (P : Subgroup ↥K), c * (t : G) * c⁻¹ = t := by
    intro c hcQ hc t ht
    have hcN : c ∈ Subgroup.normalizer (K : Set G) := hXN (hQ.1 hcQ)
    have h1 := hc t (hPQ t ht)
    have h2 : c * (t : G) * c⁻¹ * (t : G)⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.1 hcN t).1 t.2) (K.inv_mem t.2)
    have h3 : (⟨_, h2⟩ : ↥K) = 1 := hZK _ fun y => Subtype.ext
      (Subgroup.mem_centralizer_iff.1 h1 y y.2).symm
    have h4 : c * (t : G) * c⁻¹ * (t : G)⁻¹ = 1 := congrArg Subtype.val h3
    calc c * (t : G) * c⁻¹ = (c * (t : G) * c⁻¹ * (t : G)⁻¹) * t := by group
      _ = t := by rw [h4, one_mul]
  have haN : a ∈ Subgroup.normalizer (K : Set G) := hXN (hQ.1 haQ)
  have hzN : z ∈ Subgroup.normalizer (K : Set G) := hXN (hQ.1 hzQ)
  have hβ : ∀ x, conjK K a haN (conjK K a haN x) = x := by
    intro x
    apply Subtype.ext
    rw [conjK_apply, conjK_apply]
    have haa : a * a = 1 := by rw [← sq]; exact ha2
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    rw [hainv]
    calc a * (a * (x : G) * a) * a = (a * a) * x * (a * a) := by simp only [mul_assoc]
      _ = x := by rw [haa, one_mul, mul_one]
  obtain ⟨k, hk⟩ := oddAutInner_psl3 Nat.prime_three (by norm_num) hm (conjK K a haN) hβ
    ⟨P, fun t ht => Subtype.ext (fixP a haQ haC t ht)⟩
  have hau : ∀ x ∈ K, a * x * a⁻¹ = ((k⁻¹ : ↥K) : G) * x * ((k⁻¹ : ↥K) : G)⁻¹ := by
    intro x hx
    have := congrArg Subtype.val (hk ⟨x, hx⟩)
    rw [conjK_apply] at this
    rw [this]
    simp
  have hzl : ∀ x ∈ K, z * x * z⁻¹ = l₀ * x * l₀⁻¹ := by
    intro x hx
    have hy : z * x * z⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hzN x).1 hx
    have := hl₀ _ hy
    have e1 : z⁻¹ * (z * x * z⁻¹) * z = x := by group
    rw [e1] at this
    calc z * x * z⁻¹ = l₀ * (l₀⁻¹ * (z * x * z⁻¹) * l₀) * l₀⁻¹ := by group
      _ = l₀ * x * l₀⁻¹ := by rw [← this]
  let u : ↥K := k⁻¹
  let w : ↥K := ⟨l₀, hl₀K⟩
  have hu : ∀ t ∈ (P : Subgroup ↥K), u * t = t * u := by
    intro t ht
    apply Subtype.ext
    have h1 := fixP a haQ haC t ht
    rw [hau _ t.2] at h1
    show (u : G) * t = t * u
    calc (u : G) * t = ((u : G) * t * (u : G)⁻¹) * u := by group
      _ = t * u := by rw [h1]
  have hw : ∀ t ∈ (P : Subgroup ↥K), w * t = t * w := by
    intro t ht
    apply Subtype.ext
    have h1 := fixP z hzQ hzC t ht
    rw [hzl _ t.2] at h1
    show l₀ * (t : G) = t * l₀
    calc l₀ * (t : G) = (l₀ * (t : G) * l₀⁻¹) * l₀ := by group
      _ = t * l₀ := by rw [h1]
  have hu1 : u ≠ 1 := by
    intro h
    apply ha1
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hau x hx
    rw [show ((k⁻¹ : ↥K) : G) = 1 from congrArg Subtype.val h] at this
    calc x * a = a * x * a⁻¹ * a := by rw [this]; group
      _ = a * x := by group
  have hw1 : w ≠ 1 := by
    intro h
    apply hz1
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hzl x hx
    rw [show l₀ = 1 from congrArg Subtype.val h] at this
    calc x * z = z * x * z⁻¹ * z := by rw [this]; group
      _ = z * x := by group
  obtain ⟨hP2, hC⟩ := sl3_criterion hF φ
  have huw : u = w := eq_of_mem_centralizer_sylow hP2 hC P hu hw hu1 hw1
  have huw' : ((k⁻¹ : ↥K) : G) = l₀ := congrArg Subtype.val huw
  apply haz
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hy : z⁻¹ * x * z ∈ K := by
    have := hl₀ x hx
    rw [this]
    exact K.mul_mem (K.mul_mem (K.inv_mem hl₀K) hx) hl₀K
  have e1 : a * (z⁻¹ * x * z) * a⁻¹ = x := by
    rw [hau _ hy, huw', hl₀ x hx]
    group
  calc x * (a * z⁻¹) = a * (z⁻¹ * x * z) * a⁻¹ * (a * z⁻¹) := by rw [e1]
    _ = a * z⁻¹ * x := by group

end CFSG.Quasithin.H13.A5
