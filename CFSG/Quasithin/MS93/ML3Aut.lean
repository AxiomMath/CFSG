module

public import CFSG.Quasithin.MS93.ML3Rec

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin Matrix ML3
open scoped commutatorElement

namespace ML3

section Bij

variable {F F' : Type} [Field F] [Field F']

theorem ker_le_center_of_surjective [Finite F] {G : Type*} [Group G] (θ : SL3 F →* G)
    (hθ : Function.Surjective θ) (hnt : ∃ x : G, x ≠ 1) : θ.ker ≤ Subgroup.center (SL3 F) := by
  obtain ⟨hperf, hsimple, -⟩ :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 F
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hN : (θ.ker.map (QuotientGroup.mk' (Subgroup.center (SL3 F)))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have _ := hsimple
  have _ := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (θ.ker.map (QuotientGroup.mk' (Subgroup.center (SL3 F)))) with hbot | htop
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  · exfalso
    obtain ⟨x, hx⟩ := hnt
    have hdecomp : ∀ g : SL3 F, ∃ z ∈ Subgroup.center (SL3 F), θ g = θ z := fun g => by
      have hmem : (QuotientGroup.mk' (Subgroup.center (SL3 F)) g) ∈
          θ.ker.map (QuotientGroup.mk' (Subgroup.center (SL3 F))) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨k, hk, hkg⟩ := hmem
      refine ⟨k⁻¹ * g, QuotientGroup.eq.mp hkg, ?_⟩
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]
    have hcomm : ∀ g h : SL3 F, θ ⁅g, h⁆ = 1 := fun g h => by
      obtain ⟨z, hz, hgz⟩ := hdecomp g
      obtain ⟨z', hz', hhz⟩ := hdecomp h
      rw [map_commutatorElement, hgz, hhz, ← map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz' z),
        map_one]
    have hker : θ.ker = ⊤ := by
      have _ := hperf
      rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top]
      rw [commutator, Subgroup.commutator_le]
      intro g _ h _
      exact MonoidHom.mem_ker.mpr (hcomm g h)
    obtain ⟨y, rfl⟩ := hθ x
    exact hx (MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top y))

theorem pow_three_eq_one_of_mem_center {g : SL3 F} (hg : g ∈ Subgroup.center (SL3 F)) :
    g ^ 3 = 1 := by
  obtain ⟨r, hr3, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  rw [Fintype.card_fin] at hr3
  apply Subtype.ext
  change ((g ^ 3 : SL3 F) : Matrix (Fin 3) (Fin 3) F) = ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F)
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrg, ← map_pow, hr3, map_one]
  rfl

private theorem pow_two_eq_of_mul_odd {a b O O' : ℕ} (hO : Odd O) (hO' : Odd O')
    (h : 2 ^ a * O = 2 ^ b * O') : a = b := by
  have hO0 : O ≠ 0 := fun h0 => by simp [h0] at hO
  have hO0' : O' ≠ 0 := fun h0 => by simp [h0] at hO'
  have h2 := congrArg (padicValNat 2) h
  rw [padicValNat.mul (by positivity) hO0, padicValNat.mul (by positivity) hO0',
    padicValNat.prime_pow, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd
      (fun hd => (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr hd)),
    padicValNat.eq_zero_of_not_dvd
      (fun hd => (Nat.not_even_iff_odd.mpr hO') (even_iff_two_dvd.mpr hd))] at h2
  simpa using h2

private theorem odd_card_SL3_part [Finite F] [CharP F 2] :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card F = 2 ^ n ∧
      Odd ((Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) := by
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hn1 : 1 ≤ (n : ℕ) := n.2
  refine ⟨n, hn1, hF, ?_⟩
  have hodd : ∀ k, 1 ≤ k → Odd ((2 ^ (n : ℕ)) ^ k - 1) := fun k hk => by
    rw [← pow_mul]
    have hnk : (n : ℕ) * k ≠ 0 := by positivity
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, hnk⟩) odd_one
  rw [hF]
  exact Nat.odd_mul.mpr ⟨hodd 3 (by norm_num), hodd 2 (by norm_num)⟩

theorem injective_of_surjective [Finite F] [CharP F 2] [Finite F'] [CharP F' 2]
    (θ : SL3 F →* SL3 F') (hθ : Function.Surjective θ) :
    Function.Injective θ ∧ Nat.card F = Nat.card F' := by
  have hnt : ∃ x : SL3 F', x ≠ 1 := ⟨rootElt 0 1 1, by
    rw [Ne, rootElt_eq_one_iff (by decide)]
    exact one_ne_zero⟩
  have hker := ker_le_center_of_surjective θ hθ hnt
  have h3 : IsPGroup 3 θ.ker := fun k =>
    ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact pow_three_eq_one_of_mem_center (hker k.2))⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := h3.exists_card_eq
  have hcard : Nat.card (SL3 F) = Nat.card θ.ker * Nat.card (SL3 F') := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv, mul_comm]
  obtain ⟨n, -, hF, hO⟩ := odd_card_SL3_part (F := F)
  obtain ⟨n', -, hF', hO'⟩ := odd_card_SL3_part (F := F')
  rw [card_SL3, card_SL3, hk] at hcard
  set O := (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) with hOdef
  set O' := (Nat.card F' ^ 3 - 1) * (Nat.card F' ^ 2 - 1) with hO'def
  have h : 2 ^ (n * 3) * O = 2 ^ (n' * 3) * (3 ^ k * O') := by
    rw [pow_mul, pow_mul, ← hF, ← hF', hcard]
    ring
  have hnn : n = n' := by
    have := pow_two_eq_of_mul_odd hO (Nat.odd_mul.mpr ⟨Odd.pow (by decide), hO'⟩) h
    omega
  have hqq : Nat.card F = Nat.card F' := by rw [hF, hF', hnn]
  refine ⟨?_, hqq⟩
  have hOO : O' = O := by rw [hO'def, hOdef, hqq]
  rw [hOO, ← hqq] at hcard
  have hpos : 0 < Nat.card F ^ 3 * O := by
    rw [hOdef, ← card_SL3]
    exact Nat.card_pos
  have h1 : 3 ^ k = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact hcard.symm)
  have hbot : θ.ker = ⊥ := by
    rw [← Subgroup.card_eq_one, hk, h1]
  exact (MonoidHom.ker_eq_bot_iff θ).mp hbot

end Bij

section Unipotent

variable {F : Type} [Field F]

theorem uniTri_eq_iff {a b c a' b' c' : F} :
    uniTri a b c = uniTri a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    have := uniTri_injective (F := F) (a₁ := (a, b, c)) (a₂ := (a', b', c')) h
    simp only [Prod.mk.injEq] at this
    exact this
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem mem_qPt_iff_uniTri {g : SL3 F} :
    g ∈ (qPt : Subgroup (SL3 F)) ↔ ∃ a b : F, uniTri a b 0 = g := by
  let P : Subgroup (SL3 F) :=
    { carrier := {g | ∃ a b : F, uniTri a b 0 = g}
      one_mem' := ⟨0, 0, uniTri_zero⟩
      mul_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
        exact ⟨a + a', b + a * 0 + b', by rw [uniTri_mul, add_zero]⟩
      inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        exact ⟨-a, a * 0 - b, by rw [uniTri_inv, neg_zero]⟩ }
  constructor
  · intro hg
    have hle : (qPt : Subgroup (SL3 F)) ≤ P := by
      refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact ⟨a, 0, (rootElt01_eq_uniTri a).symm⟩
      · rintro _ ⟨b, rfl⟩
        exact ⟨0, b, (rootElt02_eq_uniTri b).symm⟩
    exact hle hg
  · rintro ⟨a, b, rfl⟩
    have he : uniTri a b (0 : F) = rootElt 0 1 a * rootElt 0 2 b := by
      rw [rootElt01_eq_uniTri, rootElt02_eq_uniTri, uniTri_mul]
      simp
    rw [he]
    exact Subgroup.mul_mem_sup (rootElt_mem_rootGroup 0 1 a) (rootElt_mem_rootGroup 0 2 b)

theorem mem_qLn_iff_uniTri {g : SL3 F} :
    g ∈ (qLn : Subgroup (SL3 F)) ↔ ∃ b c : F, uniTri 0 b c = g := by
  rw [mem_qLn_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨a, b, ?_⟩
    rw [rootElt02_eq_uniTri, rootElt12_eq_uniTri, uniTri_mul]
    simp
  · rintro ⟨b, c, rfl⟩
    refine ⟨b, c, ?_⟩
    rw [rootElt02_eq_uniTri, rootElt12_eq_uniTri, uniTri_mul]
    simp

theorem qPt_le_sStar : (qPt : Subgroup (SL3 F)) ≤ sStar := le_sup_left

theorem card_qPt [Finite F] : Nat.card (qPt : Subgroup (SL3 F)) = Nat.card F ^ 2 := by
  have e : F × F ≃ (qPt : Subgroup (SL3 F)) :=
    Equiv.ofBijective (fun p => ⟨uniTri p.1 p.2 0, mem_qPt_iff_uniTri.mpr ⟨_, _, rfl⟩⟩)
      ⟨fun p p' h => by
        have := uniTri_eq_iff.mp (congrArg Subtype.val h)
        exact Prod.ext this.1 this.2.1, by
        rintro ⟨g, hg⟩
        obtain ⟨a, b, rfl⟩ := mem_qPt_iff_uniTri.mp hg
        exact ⟨(a, b), rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, sq]

theorem card_qLn [Finite F] : Nat.card (qLn : Subgroup (SL3 F)) = Nat.card F ^ 2 := by
  have e : F × F ≃ (qLn : Subgroup (SL3 F)) :=
    Equiv.ofBijective (fun p => ⟨uniTri 0 p.1 p.2, mem_qLn_iff_uniTri.mpr ⟨_, _, rfl⟩⟩)
      ⟨fun p p' h => by
        have := uniTri_eq_iff.mp (congrArg Subtype.val h)
        exact Prod.ext this.2.1 this.2.2, by
        rintro ⟨g, hg⟩
        obtain ⟨b, c, rfl⟩ := mem_qLn_iff_uniTri.mp hg
        exact ⟨(b, c), rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, sq]

theorem qPt_ne_qLn : (qPt : Subgroup (SL3 F)) ≠ qLn := by
  intro h
  have hmem : uniTri (1 : F) 0 0 ∈ (qLn : Subgroup (SL3 F)) := by
    rw [← h]
    exact mem_qPt_iff_uniTri.mpr ⟨1, 0, rfl⟩
  obtain ⟨b, c, hbc⟩ := mem_qLn_iff_uniTri.mp hmem
  have := (uniTri_eq_iff.mp hbc).1
  exact zero_ne_one this

theorem le_qPt_or_le_qLn [CharP F 2] {A : Subgroup (SL3 F)} (hA : A ≤ sStar)
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hs : ∀ x ∈ A, x * x = 1) :
    A ≤ qPt ∨ A ≤ qLn := by
  have hsq : ∀ a b c : F, uniTri a b c * uniTri a b c = 1 → a * c = 0 := fun a b c h => by
    rw [uniTri_mul, ← uniTri_zero] at h
    have := (uniTri_eq_iff.mp h).2.1
    have h2 : b + a * c + b = a * c := by
      rw [add_comm b, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [h2] at this
    exact this
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  obtain ⟨x, hxA, hx⟩ := Set.not_subset.mp h1
  obtain ⟨y, hyA, hy⟩ := Set.not_subset.mp h2
  obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp (hA hxA)
  obtain ⟨a', b', c', rfl⟩ := mem_sStar_iff.mp (hA hyA)
  have hc0 : c ≠ 0 := fun h0 => hx (mem_qPt_iff_uniTri.mpr ⟨a, b, by rw [h0]⟩)
  have ha0 : a' ≠ 0 := fun h0 => hy (mem_qLn_iff_uniTri.mpr ⟨b', c', by rw [h0]⟩)
  have hac := hsq a b c (hs _ hxA)
  have hac' := hsq a' b' c' (hs _ hyA)
  have ha : a = 0 := by
    rcases mul_eq_zero.mp hac with h | h
    · exact h
    · exact absurd h hc0
  have hc' : c' = 0 := by
    rcases mul_eq_zero.mp hac' with h | h
    · exact absurd h ha0
    · exact h
  have hcomm := hc _ hxA _ hyA
  rw [uniTri_mul, uniTri_mul] at hcomm
  have := (uniTri_eq_iff.mp hcomm).2.1
  rw [ha, hc', zero_mul, add_zero] at this
  have h3 : a' * c = 0 := by linear_combination -this
  rcases mul_eq_zero.mp h3 with h | h
  · exact ha0 h
  · exact hc0 h

theorem eq_qPt_or_qLn [Finite F] [CharP F 2] {A : Subgroup (SL3 F)} (hA : A ≤ sStar)
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hs : ∀ x ∈ A, x * x = 1)
    (hcard : Nat.card A = Nat.card F ^ 2) : A = qPt ∨ A = qLn := by
  rcases le_qPt_or_le_qLn hA hc hs with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [hcard, card_qPt]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [hcard, card_qLn]))

end Unipotent

section Conj

variable {F : Type} [Field F]

theorem mem_map_conj {G : Type*} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
    exact hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem mem_sylow_smul {G : Type*} [Group G] {p : ℕ} {P : Sylow p G} {g x : G} :
    x ∈ (g • P : Sylow p G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  show x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ _
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem mem_fixN_map_conj {H : Subgroup (SL3 F)} {g : SL3 F} {v : Fin 3 → F} :
    v ∈ fixN (H.map (MulAut.conj g).toMonoidHom) ↔
      ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ fixN H := by
  rw [mem_fixN, mem_fixN]
  constructor
  · intro h k hk
    have h1 := h (g * k * g⁻¹) (mem_map_conj.mpr (by group; exact hk))
    have e : g⁻¹ * (g * k * g⁻¹) = k * g⁻¹ := by group
    calc ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
        = ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            (((g * k * g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← coe_mul_SL3, ← coe_mul_SL3, e]
      _ = ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by rw [h1]
  · intro h x hx
    have hk := h _ (mem_map_conj.mp hx)
    have h2 := congrArg (fun u => ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u) hk
    simp only [Matrix.mulVec_mulVec, ← coe_mul_SL3] at h2
    rw [show g * (g⁻¹ * x * g * g⁻¹) = x by group, show g * g⁻¹ = 1 from mul_inv_cancel g,
      coe_one_SL3, Matrix.one_mulVec] at h2
    exact h2

theorem card_fixN_map_conj [Finite F] (H : Subgroup (SL3 F)) (g : SL3 F) :
    Nat.card (fixN (H.map (MulAut.conj g).toMonoidHom)) = Nat.card (fixN H) := by
  refine Nat.card_congr
    { toFun := fun v => ⟨((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v,
        mem_fixN_map_conj.mp v.2⟩
      invFun := fun v => ⟨((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v,
        mem_fixN_map_conj.mpr (by
          rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3,
            Matrix.one_mulVec]
          exact v.2)⟩
      left_inv := fun v => Subtype.ext (by
        simp only [Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3,
          Matrix.one_mulVec])
      right_inv := fun v => Subtype.ext (by
        simp only [Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3,
          Matrix.one_mulVec]) }

theorem card_pt0 [Finite F] : Nat.card (pt0 : Submodule F (Fin 3 → F)) = Nat.card F := by
  symm
  refine Nat.card_congr
    { toFun := fun a => ⟨![a, 0, 0], ⟨rfl, rfl⟩⟩
      invFun := fun x => (x : Fin 3 → F) 0
      left_inv := fun a => rfl
      right_inv := fun x => Subtype.ext (by
        funext k
        fin_cases k
        · rfl
        · exact x.2.1.symm
        · exact x.2.2.symm) }

theorem card_fixN_qPt [Finite F] : Nat.card (fixN (qPt : Subgroup (SL3 F))) = Nat.card F := by
  rw [fixN_qPt, card_pt0]

theorem card_fixN_qLn [Finite F] :
    Nat.card (fixN (qLn : Subgroup (SL3 F))) = Nat.card F ^ 2 := by
  rw [fixN_qLn, card_ln01]

theorem card_ne_sq [Finite F] : Nat.card F ≠ Nat.card F ^ 2 := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  intro h
  have : Nat.card F * 1 = Nat.card F * Nat.card F := by rw [mul_one, ← sq, ← h]
  have := Nat.eq_of_mul_eq_mul_left (by omega) this
  omega

theorem qPt_elemAb [CharP F 2] :
    (∀ x ∈ (qPt : Subgroup (SL3 F)), ∀ y ∈ (qPt : Subgroup (SL3 F)), x * y = y * x) ∧
      ∀ x ∈ (qPt : Subgroup (SL3 F)), x * x = 1 := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨a, b, rfl⟩ := mem_qPt_iff_uniTri.mp hx
    obtain ⟨a', b', rfl⟩ := mem_qPt_iff_uniTri.mp hy
    rw [uniTri_mul, uniTri_mul, uniTri_eq_iff]
    refine ⟨add_comm _ _, ?_, rfl⟩
    rw [mul_zero, mul_zero, add_zero, add_zero, add_comm]
  · obtain ⟨a, b, rfl⟩ := mem_qPt_iff_uniTri.mp hx
    rw [uniTri_mul, ← uniTri_zero, uniTri_eq_iff]
    refine ⟨CharTwo.add_self_eq_zero a, ?_, CharTwo.add_self_eq_zero 0⟩
    rw [mul_zero, add_zero, CharTwo.add_self_eq_zero]

theorem qLn_elemAb [CharP F 2] :
    (∀ x ∈ (qLn : Subgroup (SL3 F)), ∀ y ∈ (qLn : Subgroup (SL3 F)), x * y = y * x) ∧
      ∀ x ∈ (qLn : Subgroup (SL3 F)), x * x = 1 := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨b, c, rfl⟩ := mem_qLn_iff_uniTri.mp hx
    obtain ⟨b', c', rfl⟩ := mem_qLn_iff_uniTri.mp hy
    rw [uniTri_mul, uniTri_mul, uniTri_eq_iff]
    refine ⟨rfl, ?_, add_comm _ _⟩
    rw [zero_mul, zero_mul, add_zero, add_zero, add_comm]
  · obtain ⟨b, c, rfl⟩ := mem_qLn_iff_uniTri.mp hx
    rw [uniTri_mul, ← uniTri_zero, uniTri_eq_iff]
    refine ⟨CharTwo.add_self_eq_zero 0, ?_, CharTwo.add_self_eq_zero c⟩
    rw [zero_mul, add_zero, CharTwo.add_self_eq_zero]

theorem elemAb_map {G G' : Type*} [Group G] [Group G'] {A : Subgroup G} (f : G →* G')
    (h : (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ ∀ x ∈ A, x * x = 1) :
    (∀ x ∈ A.map f, ∀ y ∈ A.map f, x * y = y * x) ∧ ∀ x ∈ A.map f, x * x = 1 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h.1 x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, h.2 x hx, map_one]

theorem exists_card_eq_two_pow [Finite F] [CharP F 2] : ∃ n : ℕ, Nat.card F = 2 ^ n := by
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩

end Conj

section Radicals

variable {F F' : Type} [Field F] [Finite F] [CharP F 2] [Field F'] [Finite F'] [CharP F' 2]

theorem exists_conj_sStar_image (θ : SL3 F →* SL3 F') (hθi : Function.Injective θ)
    (hθs : Function.Surjective θ) (c : SL3 F) :
    ∃ g : SL3 F', ∀ x : SL3 F',
      x ∈ ((sStar : Subgroup (SL3 F)).map (MulAut.conj c).toMonoidHom).map θ ↔
        g⁻¹ * x * g ∈ (sStar : Subgroup (SL3 F')) := by
  obtain ⟨n, hF⟩ := exists_card_eq_two_pow (F := F)
  obtain ⟨n', hF'⟩ := exists_card_eq_two_pow (F := F')
  set H := ((sStar : Subgroup (SL3 F)).map (MulAut.conj c).toMonoidHom).map θ with hH
  have hHp : IsPGroup 2 H := ((isPGroup_sStar hF).map _).map _
  have hker : θ.ker ≤ (sStar : Subgroup (SL3 F)).map (MulAut.conj c).toMonoidHom := by
    rw [(MonoidHom.ker_eq_bot_iff θ).mpr hθi]
    exact bot_le
  have hHi : ¬ 2 ∣ H.index := by
    rw [hH, Subgroup.index_map_eq _ hθs hker]
    have hs : Function.Surjective (MulAut.conj c).toMonoidHom := fun x =>
      ⟨(MulAut.conj c).symm x, by simp; group⟩
    have hk : (MulAut.conj c).toMonoidHom.ker ≤ (sStar : Subgroup (SL3 F)) := by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr (MulEquiv.injective _)]
      exact bot_le
    rw [Subgroup.index_map_eq _ hs hk]
    exact not_two_dvd_index_sStar hF
  let P' : Sylow 2 (SL3 F') := (isPGroup_sStar hF').toSylow (not_two_dvd_index_sStar hF')
  let Q : Sylow 2 (SL3 F') := hHp.toSylow hHi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL3 F') P' Q
  refine ⟨g, fun x => ?_⟩
  have h1 : x ∈ H ↔ x ∈ Q := (hHp.mem_toSylow hHi).symm
  rw [h1, ← hg, mem_sylow_smul]
  exact (isPGroup_sStar hF').mem_toSylow (not_two_dvd_index_sStar hF')

theorem image_radicals (θ : SL3 F →* SL3 F') (hθi : Function.Injective θ)
    (hθs : Function.Surjective θ) (hcard : Nat.card F = Nat.card F') (c : SL3 F)
    {A B : Subgroup (SL3 F)}
    (hA : A ≤ (sStar : Subgroup (SL3 F)).map (MulAut.conj c).toMonoidHom)
    (hB : B ≤ (sStar : Subgroup (SL3 F)).map (MulAut.conj c).toMonoidHom)
    (hAe : (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ ∀ x ∈ A, x * x = 1)
    (hBe : (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ ∀ x ∈ B, x * x = 1)
    (hAc : Nat.card A = Nat.card F ^ 2) (hBc : Nat.card B = Nat.card F ^ 2) (hAB : A ≠ B) :
    ∃ g : SL3 F',
      (A.map θ = (qPt : Subgroup (SL3 F')).map (MulAut.conj g).toMonoidHom ∧
        B.map θ = (qLn : Subgroup (SL3 F')).map (MulAut.conj g).toMonoidHom) ∨
      (A.map θ = (qLn : Subgroup (SL3 F')).map (MulAut.conj g).toMonoidHom ∧
        B.map θ = (qPt : Subgroup (SL3 F')).map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨g, hg⟩ := exists_conj_sStar_image θ hθi hθs c
  refine ⟨g, ?_⟩
  have hconj : ∀ {D : Subgroup (SL3 F)},
      D ≤ (sStar : Subgroup (SL3 F)).map (MulAut.conj c).toMonoidHom →
      ((D.map θ).map (MulAut.conj g⁻¹).toMonoidHom) ≤ sStar := by
    intro D hD x hx
    rw [mem_map_conj, inv_inv] at hx
    have h := (hg (g * x * g⁻¹)).mp (Subgroup.map_mono hD hx)
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h
  have hcd : ∀ {D : Subgroup (SL3 F)}, Nat.card D = Nat.card F ^ 2 →
      Nat.card ((D.map θ).map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card F' ^ 2 := by
    intro D hD
    rw [Subgroup.card_map_of_injective (MulEquiv.injective _),
      Subgroup.card_map_of_injective hθi, hD, hcard]
  have hel : ∀ {D : Subgroup (SL3 F)},
      ((∀ x ∈ D, ∀ y ∈ D, x * y = y * x) ∧ ∀ x ∈ D, x * x = 1) →
      ((∀ x ∈ (D.map θ).map (MulAut.conj g⁻¹).toMonoidHom,
        ∀ y ∈ (D.map θ).map (MulAut.conj g⁻¹).toMonoidHom, x * y = y * x) ∧
        ∀ x ∈ (D.map θ).map (MulAut.conj g⁻¹).toMonoidHom, x * x = 1) := fun hD =>
    elemAb_map _ (elemAb_map _ hD)
  have hback : ∀ (D : Subgroup (SL3 F)) (R : Subgroup (SL3 F')),
      (D.map θ).map (MulAut.conj g⁻¹).toMonoidHom = R →
        D.map θ = R.map (MulAut.conj g).toMonoidHom := by
    intro D R h
    ext x
    rw [mem_map_conj, ← h, mem_map_conj, inv_inv,
      show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
  have hne : (A.map θ).map (MulAut.conj g⁻¹).toMonoidHom ≠
      (B.map θ).map (MulAut.conj g⁻¹).toMonoidHom := fun h =>
    hAB (Subgroup.map_injective hθi (Subgroup.map_injective (MulEquiv.injective _) h))
  rcases eq_qPt_or_qLn (hconj hA) (hel hAe).1 (hel hAe).2 (hcd hAc) with hA' | hA' <;>
    rcases eq_qPt_or_qLn (hconj hB) (hel hBe).1 (hel hBe).2 (hcd hBc) with hB' | hB'
  · exact absurd (hA'.trans hB'.symm) hne
  · exact Or.inl ⟨hback _ _ hA', hback _ _ hB'⟩
  · exact Or.inr ⟨hback _ _ hA', hback _ _ hB'⟩
  · exact absurd (hA'.trans hB'.symm) hne

end Radicals

section Facts

variable {F : Type} [Field F]

theorem mem_qPt_of_mulVec {g : SL3 F}
    (h0 : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0])
    (h1 : ∀ v : Fin 3 → F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ pt0) :
    g ∈ (qPt : Subgroup (SL3 F)) := by
  have he1 := h1 ![0, 1, 0]
  have he2 := h1 ![0, 0, 1]
  rw [mem_pt0] at he1 he2
  rw [mulVec_e0] at h0
  have c0 := congrFun h0 0
  have c1 := congrFun h0 1
  have c2 := congrFun h0 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at he1 he2 c0 c1 c2
  refine mem_qPt_iff_uniTri.mpr ⟨((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 1,
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 2, ?_⟩
  apply Subtype.ext
  change ((uniTri _ _ 0 : SL3 F) : Matrix (Fin 3) (Fin 3) F) = _
  rw [coe_uniTri]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c0, c1, c2] <;>
    first
    | (symm; linear_combination he1.1)
    | (symm; linear_combination he1.2)
    | (symm; linear_combination he2.1)
    | (symm; linear_combination he2.2)

theorem conj_mem_qPt_of_mem_ptStab {k x : SL3 F} (hk : k ∈ (ptStab : Subgroup (SL3 F)))
    (hx : x ∈ (qPt : Subgroup (SL3 F))) : k * x * k⁻¹ ∈ (qPt : Subgroup (SL3 F)) := by
  have hfix : ∀ u ∈ pt0, ((x : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u = u := fun u hu => by
    have : u ∈ fixN (qPt : Subgroup (SL3 F)) := by rw [fixN_qPt]; exact hu
    exact this x hx
  have hcomm : ∀ u, ((x : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u - u ∈ pt0 := fun u => by
    have := sub_mem_commN hx u
    rwa [commN_qPt] at this
  have hkpt : ∀ {k' : SL3 F}, k' ∈ (ptStab : Subgroup (SL3 F)) → ∀ u ∈ pt0,
      ((k' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈ pt0 := fun hk' u hu => by
    rw [eq_smul_e0_of_mem_pt0 hu, Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (mem_ptStab_iff_mulVec_e0.mp hk')
  have hki : k⁻¹ ∈ (ptStab : Subgroup (SL3 F)) := Subgroup.inv_mem _ hk
  apply mem_qPt_of_mulVec
  · rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hfix _ (mem_ptStab_iff_mulVec_e0.mp hki), Matrix.mulVec_mulVec, ← coe_mul_SL3,
      mul_inv_cancel, coe_one_SL3, Matrix.one_mulVec]
  · intro v
    have he : ((k * x * k⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v =
        ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((x : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            (((k⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) -
              ((k⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        ← coe_mul_SL3, ← coe_mul_SL3, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3,
        Matrix.one_mulVec, mul_assoc]
    rw [he]
    exact hkpt hk _ (hcomm _)

theorem rootElt10_not_mem_qPt : rootElt 1 0 (1 : F) ∉ (qPt : Subgroup (SL3 F)) := by
  intro h
  obtain ⟨a, b, hab⟩ := mem_qPt_iff_uniTri.mp h
  have h' := congrArg (fun g : SL3 F => ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 0) hab
  simp [coe_uniTri, coe_rootElt (show (1 : Fin 3) ≠ 0 by decide)] at h'

theorem rootGroup_le_lnLevi {i j : Fin 3} (h : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) : rootGroup i j ≤ (lnLevi : Subgroup (SL3 F)) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem qPt_le_lnLevi : (qPt : Subgroup (SL3 F)) ≤ lnLevi :=
  sup_le (rootGroup_le_lnLevi (Or.inl ⟨rfl, rfl⟩))
    (rootGroup_le_lnLevi (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))

variable [CharP F 2]

theorem swap01_eq_prod :
    (swap01 : SL3 F) = rootElt 0 1 1 * rootElt 1 0 1 * rootElt 0 1 1 := by
  have h := rootElt01_mul_swap01 (F := F)
  calc (swap01 : SL3 F) = rootElt 0 1 1 * (rootElt 0 1 1 * swap01) := by
        rw [← mul_assoc, rootElt_mul_self, one_mul]
    _ = rootElt 0 1 1 * rootElt 1 0 1 * rootElt 0 1 1 := by rw [h, mul_assoc]

theorem swap01_mem_lnLevi : (swap01 : SL3 F) ∈ (lnLevi : Subgroup (SL3 F)) := by
  rw [swap01_eq_prod]
  have h01 := rootGroup_le_lnLevi (F := F) (Or.inl ⟨rfl, rfl⟩) (rootElt_mem_rootGroup 0 1 1)
  have h10 := rootGroup_le_lnLevi (F := F) (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (rootElt_mem_rootGroup 1 0 1)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h01 h10) h01

theorem swap12_mul_self : (swap12 : SL3 F) * swap12 = 1 := by
  apply Subtype.ext
  change ((swap12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((swap12 : SL3 F) : Matrix _ _ F) = 1
  rw [coe_swap12]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem swap12_inv : (swap12 : SL3 F)⁻¹ = swap12 :=
  inv_eq_of_mul_eq_one_right swap12_mul_self

theorem swap12_conj_uniTri (a b : F) :
    (swap12 : SL3 F)⁻¹ * uniTri a b 0 * swap12 = uniTri b a 0 := by
  rw [swap12_inv]
  apply Subtype.ext
  change ((swap12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((uniTri a b 0 : SL3 F) :
      Matrix _ _ F) * ((swap12 : SL3 F) : Matrix _ _ F) = ((uniTri b a 0 : SL3 F) : Matrix _ _ F)
  rw [coe_swap12, coe_uniTri, coe_uniTri]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem swap12_conj_rootElt21 (c : F) :
    (swap12 : SL3 F)⁻¹ * rootElt 2 1 c * swap12 = rootElt 1 2 c := by
  rw [swap12_inv]
  apply Subtype.ext
  change ((swap12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((rootElt 2 1 c : SL3 F) :
      Matrix _ _ F) * ((swap12 : SL3 F) : Matrix _ _ F) = ((rootElt 1 2 c : SL3 F) : Matrix _ _ F)
  rw [coe_swap12, coe_rootElt (by decide), coe_rootElt (by decide)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply,
      Matrix.vecMul, dotProduct]

end Facts

section NaturalCase

variable {F F' : Type} [Field F] [Finite F] [CharP F 2] [Field F'] [Finite F'] [CharP F' 2]

omit [Finite F] [CharP F 2] [Finite F'] [CharP F' 2] in
theorem mem_fixN_of_map_eq {θ : SL3 F →* SL3 F'} {A : Subgroup (SL3 F)}
    {R : Subgroup (SL3 F')} {g : SL3 F'} (h : A.map θ = R.map (MulAut.conj g).toMonoidHom)
    {u : Fin 3 → F'} : u ∈ fixN (A.map θ) ↔
      ((g⁻¹ : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ u ∈ fixN R := by
  rw [h, mem_fixN_map_conj]

omit [Finite F] [CharP F 2] [CharP F' 2] in
theorem card_fixN_of_map_eq {θ : SL3 F →* SL3 F'} {A : Subgroup (SL3 F)}
    {R : Subgroup (SL3 F')} {g : SL3 F'} (h : A.map θ = R.map (MulAut.conj g).toMonoidHom) :
    Nat.card (fixN (A.map θ)) = Nat.card (fixN R) := by
  rw [h, card_fixN_map_conj]

theorem exists_natEquiv_of_radical (θ : SL3 F →* SL3 F') (hθi : Function.Injective θ)
    (hθs : Function.Surjective θ) (hcard : Nat.card F = Nat.card F') {V : Type*} [CommGroup V]
    (ρ : SL3 F →* MulAut V) (e : V ≃* Multiplicative (Fin 3 → F'))
    (he : ∀ (g : SL3 F) (v : V), Multiplicative.toAdd (e (ρ g v)) =
      ((θ g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (e v))
    {g₀ : SL3 F'} (hpt : (qPt : Subgroup (SL3 F)).map θ =
      (qPt : Subgroup (SL3 F')).map (MulAut.conj g₀).toMonoidHom) :
    ∃ β : V ≃* Multiplicative (Fin 3 → F), ∀ (g : SL3 F) (v : V),
      Multiplicative.toAdd (β (ρ g v)) =
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β v) := by
  set p : Fin 3 → F' := ((g₀ : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ ![1, 0, 0] with hp
  have hp0 : p ≠ 0 := mulVec_e0_ne_zero g₀
  set w : V := e.symm (Multiplicative.ofAdd p) with hw
  have hew : Multiplicative.toAdd (e w) = p := by
    rw [hw, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hρeq : ∀ (h : SL3 F) (v v' : V), ρ h v = v' ↔
      ((θ h : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (e v) =
        Multiplicative.toAdd (e v') := fun h v v' => by
    rw [← he, ← e.injective.eq_iff, ← Multiplicative.toAdd.injective.eq_iff]
  have hg₀p : ((g₀⁻¹ : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ p = ![1, 0, 0] := by
    rw [hp, Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3, Matrix.one_mulVec]
  have he0 : (![1, 0, 0] : Fin 3 → F') ∈ pt0 := ⟨rfl, rfl⟩
  have hpPt : p ∈ fixN ((qPt : Subgroup (SL3 F)).map θ) := by
    rw [mem_fixN_of_map_eq hpt, hg₀p, fixN_qPt]
    exact he0
  have hcardPt : Nat.card (fixN ((qPt : Subgroup (SL3 F)).map θ)) = Nat.card F' := by
    rw [card_fixN_of_map_eq hpt, card_fixN_qPt]
  have hrad : ∀ (c : SL3 F) (B : Subgroup (SL3 F)),
      (qPt : Subgroup (SL3 F)) ≤ (sStar : Subgroup (SL3 F)).map (MulAut.conj c).toMonoidHom →
      B ≤ (sStar : Subgroup (SL3 F)).map (MulAut.conj c).toMonoidHom →
      ((∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ ∀ x ∈ B, x * x = 1) →
      Nat.card B = Nat.card F ^ 2 → (qPt : Subgroup (SL3 F)) ≠ B → p ∈ fixN (B.map θ) := by
    intro c B hA hB hBe hBc hAB
    obtain ⟨g, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := image_radicals θ hθi hθs hcard c hA hB qPt_elemAb hBe
      card_qPt hBc hAB
    · rw [mem_fixN_of_map_eq h2, fixN_qLn]
      have := (mem_fixN_of_map_eq h1).mp hpPt
      rw [fixN_qPt] at this
      exact pt0_le_ln01 this
    · exfalso
      have := card_fixN_of_map_eq h1
      rw [hcardPt, card_fixN_qLn] at this
      exact card_ne_sq this
  have hsStar1 : ∀ x : SL3 F, x ∈ (sStar : Subgroup (SL3 F)) →
      x ∈ (sStar : Subgroup (SL3 F)).map (MulAut.conj (1 : SL3 F)).toMonoidHom := fun x hx => by
    rw [mem_map_conj]
    simpa using hx
  have hpLn : p ∈ fixN ((qLn : Subgroup (SL3 F)).map θ) :=
    hrad 1 _ (fun x hx => hsStar1 x (qPt_le_sStar hx)) (fun x hx => hsStar1 x (qLn_le_sStar hx))
      qLn_elemAb card_qLn qPt_ne_qLn
  have hpLn2 : p ∈ fixN (((qLn : Subgroup (SL3 F)).map
      (MulAut.conj swap12).toMonoidHom).map θ) := by
    refine hrad swap12 _ (fun x hx => ?_) (Subgroup.map_mono qLn_le_sStar)
      (elemAb_map _ qLn_elemAb)
      (by rw [Subgroup.card_map_of_injective (MulEquiv.injective _), card_qLn]) ?_
    · obtain ⟨a, b, rfl⟩ := mem_qPt_iff_uniTri.mp hx
      rw [mem_map_conj, swap12_conj_uniTri]
      exact qPt_le_sStar (mem_qPt_iff_uniTri.mpr ⟨b, a, rfl⟩)
    · intro h
      have hm : uniTri (0 : F) 1 0 ∈ (qLn : Subgroup (SL3 F)).map
          (MulAut.conj swap12).toMonoidHom := by
        rw [← h]
        exact mem_qPt_iff_uniTri.mpr ⟨0, 1, rfl⟩
      rw [mem_map_conj, swap12_conj_uniTri] at hm
      obtain ⟨b, c, hbc⟩ := mem_qLn_iff_uniTri.mp hm
      exact zero_ne_one (uniTri_eq_iff.mp hbc).1
  let P : Subgroup (SL3 F) :=
    { carrier := {h | ((θ h : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ p = p}
      one_mem' := by
        show ((θ 1 : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ p = p
        rw [map_one, coe_one_SL3, Matrix.one_mulVec]
      mul_mem' := fun {a b} ha hb => by
        show ((θ (a * b) : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ p = p
        rw [map_mul, coe_mul_SL3, ← Matrix.mulVec_mulVec,
          show ((θ b : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ p = p from hb]
        exact ha
      inv_mem' := fun {a} ha => by
        show ((θ a⁻¹ : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ p = p
        conv_lhs => rw [← show ((θ a : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ p = p from ha]
        rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, ← map_mul, inv_mul_cancel, map_one,
          coe_one_SL3, Matrix.one_mulVec] }
  have hfixP : ∀ {A : Subgroup (SL3 F)}, p ∈ fixN (A.map θ) → A ≤ P := fun hA h hh =>
    hA (θ h) ⟨h, hh, rfl⟩
  have hlevi : (ptLevi : Subgroup (SL3 F)) ≤ P := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact (le_sup_left : rootGroup 0 1 ≤ (qPt : Subgroup (SL3 F))).trans (hfixP hpPt)
    · exact (le_sup_right : rootGroup 0 2 ≤ (qPt : Subgroup (SL3 F))).trans (hfixP hpPt)
    · exact (le_sup_right : rootGroup 1 2 ≤ (qLn : Subgroup (SL3 F))).trans (hfixP hpLn)
    · refine le_trans ?_ (hfixP hpLn2)
      rintro _ ⟨c, rfl⟩
      rw [mem_map_conj, swap12_conj_rootElt21]
      exact (le_sup_right : rootGroup 1 2 ≤ (qLn : Subgroup (SL3 F)))
        (rootElt_mem_rootGroup 1 2 c)
  have hw' : ∀ h ∈ (ptLevi : Subgroup (SL3 F)), ρ h w = w := fun h hh => by
    rw [hρeq, hew]
    exact hlevi hh
  have hquad : ∀ a ∈ rootGroup 0 1, ∀ a' ∈ rootGroup 0 1, ∀ v : V,
      ρ a' (ρ a v * v⁻¹) = ρ a v * v⁻¹ := by
    intro a ha a' ha' v
    have haPt : a ∈ (qPt : Subgroup (SL3 F)) := (le_sup_left : rootGroup 0 1 ≤ _) ha
    have ha'Pt : a' ∈ (qPt : Subgroup (SL3 F)) := (le_sup_left : rootGroup 0 1 ≤ _) ha'
    rw [hρeq, map_mul, map_inv, toAdd_mul, toAdd_inv, he, ← sub_eq_add_neg]
    have hmem : ((θ a : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (e v) -
        Multiplicative.toAdd (e v) ∈ fixN ((qPt : Subgroup (SL3 F)).map θ) := by
      rw [mem_fixN_of_map_eq hpt, fixN_qPt]
      have hy : g₀⁻¹ * θ a * g₀ ∈ (qPt : Subgroup (SL3 F')) := by
        have := (Subgroup.mem_map_of_mem θ haPt)
        rw [hpt, mem_map_conj] at this
        exact this
      have := sub_mem_commN hy (((g₀⁻¹ : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ
        Multiplicative.toAdd (e v))
      rw [commN_qPt] at this
      convert this using 1
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← coe_mul_SL3,
        ← coe_mul_SL3, show g₀⁻¹ * θ a * g₀ * g₀⁻¹ = g₀⁻¹ * θ a by group]
    exact hmem (θ a') (Subgroup.mem_map_of_mem θ ha'Pt)
  have hfix : ∀ v : V, (∀ g ∈ (lnLevi : Subgroup (SL3 F)), ρ g v = v) → v = 1 := by
    intro v hv
    set u := Multiplicative.toAdd (e v) with hu
    have hvu : ∀ g ∈ (lnLevi : Subgroup (SL3 F)),
        ((θ g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ u = u := fun g hg =>
      (hρeq g v v).mp (hv g hg)
    have huPt : u ∈ fixN ((qPt : Subgroup (SL3 F)).map θ) := by
      rintro _ ⟨h, hh, rfl⟩
      exact hvu h (qPt_le_lnLevi hh)
    rw [mem_fixN_of_map_eq hpt, fixN_qPt] at huPt
    obtain ⟨l, hl⟩ : ∃ l : F', ((g₀⁻¹ : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ u =
        l • ![1, 0, 0] := ⟨_, eq_smul_e0_of_mem_pt0 huPt⟩
    have hul : u = l • p := by
      rw [hp, ← Matrix.mulVec_smul, ← hl, Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel,
        coe_one_SL3, Matrix.one_mulVec]
    by_cases hl0 : l = 0
    · have hu0 : u = 0 := by rw [hul, hl0, zero_smul]
      have : e v = 1 := by
        rw [← ofAdd_toAdd (e v), ← hu, hu0, ofAdd_zero]
      exact (MulEquiv.map_eq_one_iff e).mp this
    exfalso
    have hsw : ((θ swap01 : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ p = p := by
      have h := hvu _ swap01_mem_lnLevi
      rw [hul, Matrix.mulVec_smul] at h
      exact smul_right_injective _ hl0 h
    set k := g₀⁻¹ * θ swap01 * g₀ with hk
    have hkP : k ∈ (ptStab : Subgroup (SL3 F')) := by
      rw [mem_ptStab_iff_mulVec_e0, hk, coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, ← hp, hsw, hg₀p]
      exact he0
    have hy : g₀⁻¹ * θ (rootElt 0 1 1) * g₀ ∈ (qPt : Subgroup (SL3 F')) := by
      have h01 : rootElt 0 1 (1 : F) ∈ (qPt : Subgroup (SL3 F)) :=
        (le_sup_left : rootGroup 0 1 ≤ (qPt : Subgroup (SL3 F))) (rootElt_mem_rootGroup 0 1 1)
      have := Subgroup.mem_map_of_mem θ h01
      rw [hpt, mem_map_conj] at this
      exact this
    have hz := conj_mem_qPt_of_mem_ptStab hkP hy
    have hθx : θ (rootElt 1 0 1) ∈ (qPt : Subgroup (SL3 F)).map θ := by
      rw [hpt, mem_map_conj]
      convert hz using 1
      rw [← swap01_conj_rootElt01, map_mul, map_mul, map_inv, hk]
      group
    obtain ⟨z, hzq, hzx⟩ := hθx
    rw [hθi hzx] at hzq
    exact rootElt10_not_mem_qPt hzq
  have hgen : Subgroup.closure (Set.range fun g : SL3 F => ρ g w) = ⊤ := by
    set C := Subgroup.closure (Set.range fun g : SL3 F => ρ g w) with hC
    have hCinv : ∀ (h : SL3 F), ∀ x ∈ C, ρ h x ∈ C := fun h x hx => by
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨g, rfl⟩ := hy
        exact Subgroup.subset_closure ⟨h * g, by
          show ρ (h * g) w = ρ h (ρ g w)
          rw [map_mul, MulAut.mul_apply]⟩
      | one => rw [map_one]; exact C.one_mem
      | mul y z _ _ hy hz => rw [map_mul]; exact C.mul_mem hy hz
      | inv y _ hy => rw [map_inv]; exact C.inv_mem hy
    let S : AddSubgroup (Fin 3 → F') :=
      { carrier := {y | e.symm (Multiplicative.ofAdd y) ∈ C}
        zero_mem' := by
          show e.symm (Multiplicative.ofAdd 0) ∈ C
          rw [ofAdd_zero, map_one]
          exact C.one_mem
        add_mem' := fun {y y'} hy hy' => by
          show e.symm (Multiplicative.ofAdd (y + y')) ∈ C
          rw [ofAdd_add, map_mul]
          exact C.mul_mem hy hy'
        neg_mem' := fun {y} hy => by
          show e.symm (Multiplicative.ofAdd (-y)) ∈ C
          rw [ofAdd_neg, map_inv]
          exact C.inv_mem hy }
    have hS : ∀ (g : SL3 F') (y : Fin 3 → F'), y ∈ S →
        ((g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ y ∈ S := by
      intro g y hy
      obtain ⟨h, rfl⟩ := hθs g
      show e.symm (Multiplicative.ofAdd _) ∈ C
      have heq : e.symm (Multiplicative.ofAdd (((θ h : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ
          y)) = ρ h (e.symm (Multiplicative.ofAdd y)) := by
        rw [MulEquiv.symm_apply_eq]
        apply Multiplicative.toAdd.injective
        rw [he, MulEquiv.apply_symm_apply, toAdd_ofAdd, toAdd_ofAdd]
      rw [heq]
      exact hCinv h _ hy
    have hpS : p ∈ S := by
      show e.symm (Multiplicative.ofAdd p) ∈ C
      exact Subgroup.subset_closure ⟨1, by
        show ρ 1 w = w
        rw [map_one, MulAut.one_apply]⟩
    rw [eq_top_iff]
    intro v _
    have := mem_of_invariant S hS hpS hp0 (Multiplicative.toAdd (e v))
    have hv : e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (e v))) = v := by
      rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
    rw [← hv]
    exact this
  have hw1 : w ≠ 1 := by
    intro h
    apply hp0
    rw [← hew, h, map_one, toAdd_one]
  obtain ⟨β, hβ, -⟩ := exists_natEquiv_of_vecStab ρ w hw1 hw' hquad hfix hgen
  exact ⟨β, hβ⟩

end NaturalCase

section DualCase

variable {F : Type} [Field F]

theorem transposeInv_uniTri_mul_cyc (a b : F) :
    transposeInv (uniTri a b 0) * cyc = cyc * uniTri 0 (-a) (-b) := by
  apply Subtype.ext
  change dualMat (uniTri a b 0) * ((cyc : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
    ((cyc : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((uniTri 0 (-a) (-b) : SL3 F) : Matrix _ _ F)
  rw [dualMat, uniTri_inv, coe_uniTri, coe_uniTri, coe_cyc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem map_transposeInv_qPt :
    (qPt : Subgroup (SL3 F)).map transposeInv =
      (qLn : Subgroup (SL3 F)).map (MulAut.conj cyc).toMonoidHom := by
  ext x
  rw [mem_map_conj]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, b, rfl⟩ := mem_qPt_iff_uniTri.mp hy
    rw [show cyc⁻¹ * transposeInv (uniTri a b 0) * cyc = uniTri 0 (-a) (-b) by
      rw [mul_assoc, transposeInv_uniTri_mul_cyc, inv_mul_cancel_left]]
    exact mem_qLn_iff_uniTri.mpr ⟨_, _, rfl⟩
  · intro hx
    obtain ⟨b, c, hbc⟩ := mem_qLn_iff_uniTri.mp hx
    refine ⟨uniTri (-b) (-c) 0, mem_qPt_iff_uniTri.mpr ⟨_, _, rfl⟩, ?_⟩
    have h := transposeInv_uniTri_mul_cyc (-b) (-c)
    rw [neg_neg, neg_neg, hbc, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at h
    exact mul_right_cancel h

theorem map_map_conj {G G' : Type*} [Group G] [Group G'] (θ : G →* G') (c : G)
    (H : Subgroup G) : (H.map (MulAut.conj c).toMonoidHom).map θ =
      (H.map θ).map (MulAut.conj (θ c)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem transposeInv_bijective : Function.Bijective (transposeInv : SL3 F →* SL3 F) :=
  Function.bijective_iff_has_inverse.mpr ⟨transposeInv, transposeInv_transposeInv,
    transposeInv_transposeInv⟩

theorem card_fixV_map {F' : Type} [Field F'] {θ : SL3 F →* SL3 F'} {V : Type*} [CommGroup V]
    {ρ : SL3 F →* MulAut V} {e : V ≃* Multiplicative (Fin 3 → F')}
    (he : ∀ (g : SL3 F) (v : V), Multiplicative.toAdd (e (ρ g v)) =
      ((θ g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (e v))
    (H : Subgroup (SL3 F)) : Nat.card ↥(fixV (H.map ρ)) = Nat.card (fixN (H.map θ)) := by
  have hiff : ∀ v : V, v ∈ fixV (H.map ρ) ↔ Multiplicative.toAdd (e v) ∈ fixN (H.map θ) := by
    intro v
    rw [mem_fixV, mem_fixN]
    constructor
    · rintro hv _ ⟨h, hh, rfl⟩
      rw [← he, hv _ ⟨h, hh, rfl⟩]
    · rintro hv _ ⟨h, hh, rfl⟩
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [he]
      exact hv _ ⟨h, hh, rfl⟩
  refine Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd (e v), (hiff v).mp v.2⟩
      invFun := fun u => ⟨e.symm (Multiplicative.ofAdd u), (hiff _).mpr (by
        rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
        exact u.2)⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp) }

end DualCase

end ML3

section Main

variable {F F' : Type} [Field F] [Finite F] [CharP F 2] [Field F'] [Finite F'] [CharP F' 2]

theorem exists_natEquiv_or_dual_of_surj (θ : SL3 F →* SL3 F') (hθ : Function.Surjective θ)
    {V : Type*} [CommGroup V] (ρ : SL3 F →* MulAut V) (e : V ≃* Multiplicative (Fin 3 → F'))
    (he : ∀ (g : SL3 F) (v : V), Multiplicative.toAdd (e (ρ g v)) =
      ((θ g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (e v)) :
    ∃ (dual : Bool) (β : V ≃* Multiplicative (Fin 3 → F)),
      (∀ (g : SL3 F) (v : V), Multiplicative.toAdd (β (ρ g v)) =
        natAct dual g *ᵥ Multiplicative.toAdd (β v)) ∧
      (dual = false ↔ Nat.card ↥(fixV ((qLn : Subgroup (SL3 F)).map ρ)) = Nat.card F ^ 2) := by
  obtain ⟨hθi, hcard⟩ := injective_of_surjective θ hθ
  have hsStar1 : ∀ x : SL3 F, x ∈ (sStar : Subgroup (SL3 F)) →
      x ∈ (sStar : Subgroup (SL3 F)).map (MulAut.conj (1 : SL3 F)).toMonoidHom := fun x hx => by
    rw [mem_map_conj]
    simpa using hx
  have hfixLn := card_fixV_map he qLn
  obtain ⟨g, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := image_radicals θ hθi hθ hcard 1
    (fun x hx => hsStar1 x (qPt_le_sStar hx)) (fun x hx => hsStar1 x (qLn_le_sStar hx))
    qPt_elemAb qLn_elemAb card_qPt card_qLn qPt_ne_qLn
  · obtain ⟨β, hβ⟩ := exists_natEquiv_of_radical θ hθi hθ hcard ρ e he h1
    refine ⟨false, β, fun g v => by rw [natAct_false]; exact hβ g v, ?_⟩
    rw [hfixLn, card_fixN_of_map_eq h2, card_fixN_qLn, hcard]
    simp
  ·
    have hθ' : Function.Surjective (θ.comp transposeInv) :=
      hθ.comp transposeInv_bijective.2
    have hθi' : Function.Injective (θ.comp transposeInv) :=
      hθi.comp transposeInv_bijective.1
    have he' : ∀ (g : SL3 F) (v : V), Multiplicative.toAdd (e ((ρ.comp transposeInv) g v)) =
        (((θ.comp transposeInv) g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ
          Multiplicative.toAdd (e v) := fun g v => he _ v
    have hpt' : (qPt : Subgroup (SL3 F)).map (θ.comp transposeInv) =
        (qPt : Subgroup (SL3 F')).map (MulAut.conj (θ cyc * g)).toMonoidHom := by
      rw [← Subgroup.map_map, map_transposeInv_qPt, map_map_conj, h2]
      ext x
      rw [mem_map_conj, mem_map_conj, mem_map_conj]
      constructor <;> intro h <;> convert h using 1 <;> group
    obtain ⟨β, hβ⟩ := exists_natEquiv_of_radical (θ.comp transposeInv) hθi' hθ' hcard
      (ρ.comp transposeInv) e he' hpt'
    refine ⟨true, β, fun g v => ?_, ?_⟩
    · have h := hβ (transposeInv g) v
      rwa [MonoidHom.comp_apply, transposeInv_transposeInv, coe_transposeInv, ← natAct_true] at h
    · rw [hfixLn, card_fixN_of_map_eq h2, card_fixN_qPt, hcard]
      simp only [Bool.true_eq_false, false_iff]
      exact card_ne_sq

end Main

end CFSG.Quasithin.MS93
