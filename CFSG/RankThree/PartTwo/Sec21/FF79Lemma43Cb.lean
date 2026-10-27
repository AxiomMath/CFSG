module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Setup
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Gen

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem s43_ker {b : G} {J B : Subgroup G} (S : Setup14 5 b J B)
    (hX : Odd (Nat.card (Opp 3 (Cen b)))) {g : G} (hg : g ∈ Cen b)
    (hgJ : ∀ x ∈ J, g * x * g⁻¹ = x) (h2 : Is2El g) : g = 1 := by
  have hC0 : Odd (Nat.card ↥(Cen b ⊓ CenS J)) := by
    rw [S.card_C0 hX]; exact (by decide : Odd 3).mul hX
  refine h2.eq_one_of_odd_card hC0 (Subgroup.mem_inf.mpr ⟨hg, ?_⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  calc x * g = (g * x * g⁻¹) * g := by rw [hgJ x hx]
    _ = g * x := by group

theorem good_b {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂)
    (hX : Odd (Nat.card (Opp 3 (Cen b)))) (e : J ≃* GL (Fin 5) (ZMod 2)) (hO5 : FF79KO2L5)
    {σ : G} (hσB : σ ∈ CenS B) (hσo : orderOf σ = 2) : Good43 σ b := by
  have S := setup_of_sec4 h4 e
  obtain ⟨hb₁o, hb₂o, hb₁b₂, hK1⟩ := s43_orders h4
  have hb₁J : b₁ ∈ J := (Subgroup.mem_inf.mp h4.hb₁).2
  have hb₂J : b₂ ∈ J := (Subgroup.mem_inf.mp h4.hb₂).2
  have hb₁B : b₁ ∈ B := (Subgroup.mem_inf.mp h4.hb₁).1
  have hb₂B : b₂ ∈ B := (Subgroup.mem_inf.mp h4.hb₂).1
  have hσb : σ ∈ Cen b := S.cenB_le_cen hσB
  have hσN : σ ∈ Nor J := S.cen_le_nor hσb
  have hσ2 : σ * σ = 1 := by rw [← pow_two]; exact hσo ▸ pow_orderOf_eq_one σ
  have hσ2el : Is2El σ := ⟨1, by simpa [pow_two] using hσ2⟩
  have hker : ∀ g ∈ Cen b, (∀ x ∈ J, g * x * g⁻¹ = x) → Is2El g → g = 1 :=
    fun g hg hgJ h2 => s43_ker S hX hg hgJ h2
  intro Q hQ hQle hQn q hq
  have hqb : q ∈ Cen b := (hQle hq).1
  have hqσ : q ∈ Cen σ := (hQle hq).2
  have hqN : q ∈ Nor J := S.cen_le_nor hqb
  have hqσc : q * σ = σ * q := (s43_cen_comm hqσ).symm
  have hq2 : Is2El q := Is2El.of_mem_pGroup hQ hq
  let ρ := normAut J e
  let σ' : Nor J := ⟨σ, hσN⟩
  let q' : Nor J := ⟨q, hqN⟩
  have hcomm : q' * σ' = σ' * q' := Subtype.ext hqσc
  by_cases h1 : ρ q' = 1
  · have := hker q hqb ((normAut_eq_one_iff J e q').mp h1) hq2
    rw [this]; exact Subgroup.one_mem _
  by_cases h2 : ρ q' = ρ σ'
  · have hk : (ρ (q' * σ'⁻¹)) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
    have hk' := (normAut_eq_one_iff J e (q' * σ'⁻¹)).mp hk
    have hker' : q * σ⁻¹ = 1 := by
      refine hker _ (Subgroup.mul_mem _ hqb (Subgroup.inv_mem _ hσb)) ?_ ?_
      · intro x hx
        exact hk' x hx
      · exact Is2El.mul ((show Commute q σ from hqσc).inv_right) hq2 hσ2el.inv
    have : q = σ := mul_inv_eq_one.mp hker'
    rw [this]; exact Subgroup.mem_zpowers σ
  exfalso
  have hφ2 : ρ σ' * ρ σ' = 1 := by
    rw [← map_mul, show σ' * σ' = 1 from Subtype.ext hσ2, map_one]
  have hφ1 : ρ σ' ≠ 1 := by
    intro h
    have := hker σ hσb ((normAut_eq_one_iff J e σ').mp h) hσ2el
    rw [this, orderOf_one] at hσo
    omega
  have hfix : ∀ x : J, (x : G) ∈ B → ρ σ' (e x) = e x := by
    intro x hxB
    refine (normAut_eq_self_iff J e σ' x).mpr ?_
    have := Subgroup.mem_centralizer_iff.mp hσB x hxB
    show σ * x * σ⁻¹ = x
    calc σ * x * σ⁻¹ = (x * σ) * σ⁻¹ := by rw [this]
      _ = x := by group
  obtain ⟨c, hcfix, hcnot⟩ := hO5 (ρ σ') hφ2 hφ1 (e ⟨b₁, hb₁J⟩) (e ⟨b₂, hb₂J⟩)
    (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hb₁o)
    (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hb₂o)
    (by rw [← map_mul, ← map_mul]; exact congrArg e (Subtype.ext hb₁b₂))
    (by
      rintro ⟨k, hk⟩
      apply hK1
      have h' : (⟨b₁, hb₁J⟩ : J) ^ k = ⟨b₂, hb₂J⟩ := by
        apply e.injective
        rw [map_zpow]; exact hk
      exact ⟨k, congrArg Subtype.val h'⟩)
    (hfix ⟨b₁, hb₁J⟩ hb₁B) (hfix ⟨b₂, hb₂J⟩ hb₂B) (ρ q') (by rw [← map_mul, ← map_mul, hcomm])
    (Is2El.map ρ (is2El_subtype q' hq2)) h1 h2
  set s : J := e.symm c with hs
  have hcs : e s = c := e.apply_symm_apply c
  have hsσ : σ * (s : G) * σ⁻¹ = s := (normAut_eq_self_iff J e σ' s).mp (by rw [hcs]; exact hcfix)
  have hsC : (s : G) ∈ Cen b ⊓ Cen σ :=
    ⟨S.J_le_cen s.2, s43_mem_cen (by
      calc σ * (s : G) = (σ * s * σ⁻¹) * σ := by group
        _ = s * σ := by rw [hsσ])⟩
  have hcommQ : (s : G) * q * (s : G)⁻¹ * q⁻¹ ∈ Q :=
    Subgroup.mul_mem _ (hQn _ hsC q hq) (Subgroup.inv_mem _ hq)
  let s' : Nor J := ⟨(s : G), Subgroup.le_normalizer s.2⟩
  have hw : Is2El (s' * q' * s'⁻¹ * q'⁻¹) :=
    is2El_subtype _ (Is2El.of_mem_pGroup hQ hcommQ)
  have hw' := Is2El.map ρ hw
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, show ρ s' = MulAut.conj c by
    rw [← hcs]; exact normAut_of_mem J e s] at hw'
  exact hcnot hw'

theorem two_pow_dvd_cenB {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂)
    (hX : Odd (Nat.card (Opp 3 (Cen b)))) (e : J ≃* GL (Fin 5) (ZMod 2)) (hF5 : FF79KAut5Fix) :
    ∀ k : ℕ, 2 ^ k ∣ Nat.card ↥(CenS B) → k ≤ 1 := by
  intro k hk
  by_contra hlt
  push Not at hlt
  have S := setup_of_sec4 h4 e
  obtain ⟨hb₁o, hb₂o, hb₁b₂, hK1⟩ := s43_orders h4
  have hb₁J : b₁ ∈ J := (Subgroup.mem_inf.mp h4.hb₁).2
  have hb₂J : b₂ ∈ J := (Subgroup.mem_inf.mp h4.hb₂).2
  have hb₁B : b₁ ∈ B := (Subgroup.mem_inf.mp h4.hb₁).1
  have hb₂B : b₂ ∈ B := (Subgroup.mem_inf.mp h4.hb₂).1
  have h4k : 2 ^ 2 ∣ Nat.card ↥(CenS B) := (pow_dvd_pow 2 hlt).trans hk
  obtain ⟨K, hKc⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(CenS B)) 2 h4k
  let T : Subgroup G := K.map (CenS B).subtype
  have hTle : T ≤ CenS B := Subgroup.map_subtype_le K
  have hTc : Nat.card T = 2 ^ 2 := by
    rw [Subgroup.card_map_of_injective (CenS B).subtype_injective, hKc]
  have hTp : IsPGroup 2 T := IsPGroup.of_card hTc
  let ρ := normAut J e
  have hmemN : ∀ g ∈ CenS B, g ∈ Nor J := fun g hg => S.cen_le_nor (S.cenB_le_cen hg)
  let N : ∀ g : G, g ∈ CenS B → Nor J := fun g hg => ⟨g, hmemN g hg⟩
  have hfix : ∀ (g : G) (hg : g ∈ CenS B) (x : J), (x : G) ∈ B → ρ (N g hg) (e x) = e x := by
    intro g hg x hxB
    refine (normAut_eq_self_iff J e (N g hg) x).mpr ?_
    have := Subgroup.mem_centralizer_iff.mp hg x hxB
    show g * x * g⁻¹ = x
    calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [this]
      _ = x := by group
  have hnz : ∀ (g : G) (hg : g ∈ CenS B), g ∈ T → g ≠ 1 → ρ (N g hg) ≠ 1 := by
    intro g hg hgT hg1 h
    exact hg1 (s43_ker S hX (S.cenB_le_cen hg) ((normAut_eq_one_iff J e _).mp h)
      (Is2El.of_mem_pGroup hTp hgT))
  have hy1 : orderOf (e ⟨b₁, hb₁J⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hb₁o
  have hy2 : orderOf (e ⟨b₂, hb₂J⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hb₂o
  have hyc : e ⟨b₁, hb₁J⟩ * e ⟨b₂, hb₂J⟩ = e ⟨b₂, hb₂J⟩ * e ⟨b₁, hb₁J⟩ := by
    rw [← map_mul, ← map_mul]; exact congrArg e (Subtype.ext hb₁b₂)
  have hyn : e ⟨b₂, hb₂J⟩ ∉ Subgroup.zpowers (e ⟨b₁, hb₁J⟩) := by
    rintro ⟨k, hk⟩
    apply hK1
    have h' : (⟨b₁, hb₁J⟩ : J) ^ k = ⟨b₂, hb₂J⟩ := by
      apply e.injective
      rw [map_zpow]; exact hk
    exact ⟨k, congrArg Subtype.val h'⟩
  have hinj : ∀ (g g' : G) (hg : g ∈ CenS B) (hg' : g' ∈ CenS B), g ∈ T → g' ∈ T → g ≠ 1 →
      g' ≠ 1 → g = g' := by
    intro g g' hg hg' hgT hg'T hg1 hg'1
    have hρ := hF5 _ _ hy1 hy2 hyc hyn (ρ (N g hg)) (ρ (N g' hg'))
      (hfix g hg ⟨b₁, hb₁J⟩ hb₁B) (hfix g hg ⟨b₂, hb₂J⟩ hb₂B)
      (hfix g' hg' ⟨b₁, hb₁J⟩ hb₁B) (hfix g' hg' ⟨b₂, hb₂J⟩ hb₂B)
      (Is2El.map ρ (is2El_subtype _ (Is2El.of_mem_pGroup hTp hgT)))
      (Is2El.map ρ (is2El_subtype _ (Is2El.of_mem_pGroup hTp hg'T)))
      (hnz g hg hgT hg1) (hnz g' hg' hg'T hg'1)
    have hk : ρ (N g hg * (N g' hg')⁻¹) = 1 := by
      rw [map_mul, map_inv, hρ, mul_inv_cancel]
    have hk' := (normAut_eq_one_iff J e _).mp hk
    have h1 : g * g'⁻¹ = 1 :=
      s43_ker S hX (Subgroup.mul_mem _ (S.cenB_le_cen hg)
        (Subgroup.inv_mem _ (S.cenB_le_cen hg')))
        (fun x hx => hk' x hx)
        (Is2El.of_mem_pGroup hTp (T.mul_mem hgT (T.inv_mem hg'T)))
    exact mul_inv_eq_one.mp h1
  have hT1 : ∃ q₀ ∈ T, q₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : T = ⊥ := (Subgroup.eq_bot_iff_forall T).mpr h
    rw [this, Subgroup.card_bot] at hTc
    norm_num at hTc
  obtain ⟨q₀, hq₀T, hq₀1⟩ := hT1
  have hsub : (T : Set G) ⊆ {1, q₀} := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (hinj x q₀ (hTle hx) (hTle hq₀T) hx hq₀T hx1 hq₀1)
  have hle2 : Nat.card T ≤ 2 := by
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, q₀} : Set G).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    have h3 : Nat.card T = (T : Set G).ncard := Nat.card_coe_set_eq (T : Set G)
    omega
  rw [hTc] at hle2
  omega

end CFSG.RankThree.PartTwo.Sec21.FF79
