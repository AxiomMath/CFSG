module

public import CFSG.Quasithin.Background.RonanE211Fin
public import CFSG.Quasithin.Background.RonanE211Odd
public import CFSG.Quasithin.Background.RonanE211Quot
public import CFSG.Quasithin.Vol2.Ch3E213MP6ED
public import CFSG.Quasithin.Vol2.E2TenSevenCore

public section

namespace CFSG.Quasithin.RonanE211

open Equiv CFSG.Quasithin CFSG.Quasithin.E2 CFSG.Quasithin.Ch3E213M CFSG.Quasithin.Ch3E213M.P6E
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252.A6 CFSG.Quasithin.RonanE27

open scoped commutatorElement

theorem commutator_eq_top_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : commutator B = ⊤) : commutator A = ⊤ := by
  have hmap : (commutator B).map e.symm.toMonoidHom = commutator A := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.symm.surjective]
  rw [← hmap, h, Subgroup.map_top_of_surjective _ e.symm.surjective]

section Setup

variable {Q : Type} [Group Q]

noncomputable def altSixEquiv (J₀ : Subgroup Q) [J₀.Normal] (ρ : Q →* P6) (hρk : ρ.ker = J₀)
    (hρr : ρ.range = alternatingGroup (Fin 6)) : Q ⧸ J₀ ≃* ↥(alternatingGroup (Fin 6)) :=
  ((QuotientGroup.quotientMulEquivOfEq hρk.symm).trans
    (QuotientGroup.quotientKerEquivRange ρ)).trans (MulEquiv.subgroupCongr hρr)

theorem altSix_simple (J₀ : Subgroup Q) [J₀.Normal] (ρ : Q →* P6) (hρk : ρ.ker = J₀)
    (hρr : ρ.range = alternatingGroup (Fin 6)) : IsSimpleGroup (Q ⧸ J₀) :=
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  MulEquiv.isSimpleGroup (altSixEquiv J₀ ρ hρk hρr)

theorem altSix_perfect (J₀ : Subgroup Q) [J₀.Normal] (ρ : Q →* P6) (hρk : ρ.ker = J₀)
    (hρr : ρ.range = alternatingGroup (Fin 6)) : commutator (Q ⧸ J₀) = ⊤ :=
  commutator_eq_top_of_mulEquiv' (altSixEquiv J₀ ρ hρk hρr) commutator_alt_six

theorem altSix_nonabelian (J₀ : Subgroup Q) [J₀.Normal] (ρ : Q →* P6) (hρk : ρ.ker = J₀)
    (hρr : ρ.range = alternatingGroup (Fin 6)) : ∃ a b : Q ⧸ J₀, a * b ≠ b * a := by
  refine ⟨(altSixEquiv J₀ ρ hρk hρr).symm ⟨rD, D0_le_A6 rD_mem⟩,
    (altSixEquiv J₀ ρ hρk hρr).symm ⟨sD, D0_le_A6 sD_mem⟩, fun h => ?_⟩
  have := congrArg (altSixEquiv J₀ ρ hρk hρr) h
  simp only [map_mul, MulEquiv.apply_symm_apply] at this
  exact rD_sD_ne (congrArg Subtype.val this)

end Setup

section LemmaA

variable {Q : Type} [Group Q] [Finite Q]

theorem center_commutator_eq_bot_of_alt_six (hKG : KGI22One) (J₀ : Subgroup Q) [J₀.Normal]
    (hJc : J₀ ≤ Subgroup.center Q) (hJ2 : IsPGroup 2 J₀)
    (ρ : Q →* P6) (hρk : ρ.ker = J₀) (hρr : ρ.range = alternatingGroup (Fin 6))
    {v t : Q} (hv : v * v = 1) (hρv : ρ v = zA) (hρt : ρ t = sD) (hvt : v * t = t * v) :
    Subgroup.center (commutator Q) = ⊥ := by
  by_contra hne
  set eQ := altSixEquiv J₀ ρ hρk hρr with heQ
  have hsimp : IsSimpleGroup (Q ⧸ J₀) := altSix_simple J₀ ρ hρk hρr
  have hS : commutator (Q ⧸ J₀) = ⊤ := altSix_perfect J₀ ρ hρk hρr
  have hna : ∃ a b : Q ⧸ J₀, a * b ≠ b * a := altSix_nonabelian J₀ ρ hρk hρr
  obtain ⟨hLq, ⟨eL⟩⟩ := quasisimple_commutator J₀ hJc hS hsimp hna
  have hLJ := commutator_sup_eq_top J₀ hS
  have hZ := map_center_commutator_eq J₀ hJc hS hsimp hna
  have hZ2 : IsPGroup 2 (Subgroup.center (commutator Q)) := by
    intro z
    have hzJ : ((z : commutator Q) : Q) ∈ J₀ := by
      have : ((z : commutator Q) : Q) ∈
          (Subgroup.center (commutator Q)).map (commutator Q).subtype := ⟨z, z.2, rfl⟩
      rw [hZ] at this
      exact this.2
    obtain ⟨k, hk⟩ := hJ2 ⟨_, hzJ⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun x : J₀ => (x : Q)) hk
    simpa using this
  obtain ⟨eS⟩ := (hKG (commutator Q) hLq hne hZ2).2 ⟨eL.trans eQ⟩
  have h2 : (2 : GaloisField 3 2) ≠ 0 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    intro h
    have h3 : ((2 : ℕ) : GaloisField 3 2) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField 3 2) 3] at h3
    omega
  have hcen : ∀ y : commutator Q, y ∈ Subgroup.center (commutator Q) ↔
      eS y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 2)) := by
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_center_iff] at hy ⊢
      intro B
      obtain ⟨x, rfl⟩ := eS.surjective B
      rw [← map_mul, ← map_mul, hy x]
    · intro hy
      rw [Subgroup.mem_center_iff] at hy ⊢
      intro x
      apply eS.injective
      rw [map_mul, map_mul, hy (eS x)]
  set c : Q := ((eS.symm (-1) : commutator Q) : Q) with hc
  have hinvc : ∀ y ∈ commutator Q, y * y = 1 →
      y ∈ (Subgroup.center (commutator Q)).map (commutator Q).subtype := by
    intro y hy hyy
    refine ⟨⟨y, hy⟩, (hcen _).2 ?_, rfl⟩
    have : eS ⟨y, hy⟩ * eS ⟨y, hy⟩ = 1 := by
      rw [← map_mul]
      have : (⟨y, hy⟩ : commutator Q) * ⟨y, hy⟩ = 1 := Subtype.ext hyy
      rw [this, map_one]
    rcases sl2_eq_one_or_neg_one_of_mul_self h2 this with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_center_iff.2 fun B => by rw [mul_neg, neg_mul, mul_one, one_mul]
  have hcZ : ∀ z ∈ (Subgroup.center (commutator Q)).map (commutator Q).subtype, z = 1 ∨ z = c := by
    rintro _ ⟨y, hy, rfl⟩
    rcases sl2_center_eq_one_or_neg_one ((hcen y).1 hy) with h | h
    · left
      have : y = 1 := eS.injective (by rw [h, map_one])
      rw [this]; rfl
    · right
      have : y = eS.symm (-1) := by rw [← h, MulEquiv.symm_apply_apply]
      rw [this, hc]
      rfl
  have hcc : c * c = 1 := by
    have : (eS.symm (-1) : commutator Q) * eS.symm (-1) = 1 := by
      rw [← map_mul]
      simp
    exact congrArg Subtype.val this
  have hsqJ : ∀ w ∈ commutator Q, w ∈ J₀ → w * w = 1 ∧ ∀ y : Q, w * y = y * w := by
    intro w hw hwJ
    refine ⟨?_, fun y => (Subgroup.mem_center_iff.1 (hJc hwJ) y).symm⟩
    have hw' : w ∈ (Subgroup.center (commutator Q)).map (commutator Q).subtype := by
      rw [hZ]; exact ⟨hw, hwJ⟩
    rcases hcZ w hw' with h | h
    · rw [h, mul_one]
    · rw [h]; exact hcc
  have hmemLJ : ∀ x : Q, ∃ l ∈ commutator Q, ∃ z ∈ J₀, l * z = x := fun x =>
    Subgroup.mem_sup_of_normal_right.1 (hLJ ▸ Subgroup.mem_top x)
  obtain ⟨l, hl, z, hz, hlz⟩ := hmemLJ v
  obtain ⟨lt, hlt, zt, hzt, hltzt⟩ := hmemLJ t
  have hρJ : ∀ j ∈ J₀, ρ j = 1 := fun j hj => MonoidHom.mem_ker.1 (hρk ▸ hj)
  have hρl : ρ l = zA := by
    have := congrArg ρ hlz
    rw [map_mul, hρJ z hz, mul_one, hρv] at this
    exact this
  have hρlt : ρ lt = sD := by
    have := congrArg ρ hltzt
    rw [map_mul, hρJ zt hzt, mul_one, hρt] at this
    exact this
  obtain ⟨a, ha⟩ : ∃ a : Q, ρ a = rD := by
    have : rD ∈ ρ.range := hρr ▸ D0_le_A6 rD_mem
    exact this
  obtain ⟨rt, hrt, zr, hzr, hrtzr⟩ := hmemLJ a
  have hρrt : ρ rt = rD := by
    have := congrArg ρ hrtzr
    rw [map_mul, hρJ zr hzr, mul_one, ha] at this
    exact this
  have hzc : ∀ y : Q, z * y = y * z := fun y => (Subgroup.mem_center_iff.1 (hJc hz) y).symm
  have hztc : ∀ y : Q, zt * y = y * zt := fun y => (Subgroup.mem_center_iff.1 (hJc hzt) y).symm
  have hvlt : v * lt = lt * v := by
    have h1 : v * (lt * zt) = (lt * zt) * v := by rw [hltzt]; exact hvt
    have h2 : v * lt * zt = lt * v * zt := by
      calc v * lt * zt = v * (lt * zt) := by group
        _ = (lt * zt) * v := h1
        _ = lt * (zt * v) := by group
        _ = lt * (v * zt) := by rw [hztc v]
        _ = lt * v * zt := by group
    exact mul_right_cancel h2
  have hllt : l * lt = lt * l := by
    have h1 : l * z * lt = lt * (l * z) := by rw [hlz]; exact hvlt
    have h2 : l * lt * z = lt * l * z := by
      calc l * lt * z = l * (lt * z) := by group
        _ = l * (z * lt) := by rw [← hzc lt]
        _ = l * z * lt := by group
        _ = lt * (l * z) := h1
        _ = lt * l * z := by group
    exact mul_right_cancel h2
  have hl2 : l * l ≠ 1 := by
    intro h1
    have hlZ := hinvc l hl h1
    rw [hZ] at hlZ
    have := hρJ l hlZ.2
    rw [hρl] at this
    exact zA_ne_one this
  have hLmul : ∀ {a b : Q}, a ∈ commutator Q → b ∈ commutator Q → a * b ∈ commutator Q :=
    fun ha hb => Subgroup.mul_mem _ ha hb
  have hLinv : ∀ {a : Q}, a ∈ commutator Q → a⁻¹ ∈ commutator Q :=
    fun ha => Subgroup.inv_mem _ ha
  have hw₀ := hsqJ (l * (rt * rt)⁻¹) (hLmul hl (hLinv (hLmul hrt hrt))) (by
    rw [← hρk, MonoidHom.mem_ker, map_mul, map_inv, map_mul, hρl, hρrt, rD_sq, mul_inv_cancel])
  have hw₁ := hsqJ (lt * rt * lt⁻¹ * rt) (hLmul (hLmul (hLmul hlt hrt) (hLinv hlt)) hrt) (by
    rw [← hρk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hρlt, hρrt, sD_conj,
      inv_mul_cancel])
  obtain ⟨hw₀sq, hw₀c⟩ := hw₀
  obtain ⟨hw₁sq, hw₁c⟩ := hw₁
  set w₀ : Q := l * (rt * rt)⁻¹ with hw₀def
  set w₁ : Q := lt * rt * lt⁻¹ * rt with hw₁def
  set A : Q := rt * rt with hA
  set u : Q := lt * rt * lt⁻¹ with hu
  have hlw : l = w₀ * A := by rw [hw₀def]; group
  have huw : u = w₁ * rt⁻¹ := by rw [hw₁def]; group
  have huu : u * u = A⁻¹ := by
    calc u * u = (w₁ * rt⁻¹) * (w₁ * rt⁻¹) := by rw [← huw]
      _ = w₁ * (rt⁻¹ * w₁) * rt⁻¹ := by group
      _ = w₁ * (w₁ * rt⁻¹) * rt⁻¹ := by rw [hw₁c rt⁻¹]
      _ = (w₁ * w₁) * (rt⁻¹ * rt⁻¹) := by group
      _ = A⁻¹ := by rw [hw₁sq, one_mul, hA, mul_inv_rev]
  have hconj : lt * l * lt⁻¹ = w₀ * A⁻¹ := by
    calc lt * l * lt⁻¹ = lt * (w₀ * A) * lt⁻¹ := by rw [← hlw]
      _ = (lt * w₀) * A * lt⁻¹ := by group
      _ = (w₀ * lt) * A * lt⁻¹ := by rw [hw₀c lt]
      _ = w₀ * (lt * (rt * rt) * lt⁻¹) := by rw [hA]; group
      _ = w₀ * (u * u) := by rw [hu]; group
      _ = w₀ * A⁻¹ := by rw [huu]
  have hinv : l⁻¹ = w₀ * A⁻¹ := by
    have hw₀i : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀sq
    calc l⁻¹ = (w₀ * A)⁻¹ := by rw [← hlw]
      _ = A⁻¹ * w₀⁻¹ := by rw [mul_inv_rev]
      _ = A⁻¹ * w₀ := by rw [hw₀i]
      _ = w₀ * A⁻¹ := (hw₀c A⁻¹).symm
  have hcomm : lt * l * lt⁻¹ = l := by
    rw [← hllt]; group
  apply hl2
  have : l = l⁻¹ := hcomm.symm.trans (hconj.trans hinv.symm)
  calc l * l = l * l⁻¹ := by rw [← this]
    _ = 1 := mul_inv_cancel l

end LemmaA

section Main

variable {Q : Type} [Group Q] [Finite Q]

theorem sq_eq_one_of_perm_six_aux (hKG : KGI22One) (hOdd : OddCoverExact P6) (J₀ : Subgroup Q)
    [J₀.Normal] (hJc : J₀ ≤ Subgroup.center Q) (ρ : Q →* P6) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker = J₀) (V₀ T₀ : Subgroup Q) (hV₀ : ∀ v ∈ V₀, v * v = 1) (hVJ : V₀ ⊓ J₀ = ⊥)
    (hVT : V₀ ≤ T₀) (hTV : T₀ ≤ Subgroup.normalizer (V₀ : Set Q)) (hT : T₀.map ρ = S06)
    (hVc : ∀ v ∈ V₀, ∀ t ∈ T₀, ρ v * ρ t = ρ t * ρ v) {q : Q}
    (hgen : V₀ ⊔ V₀.map (MulAut.conj q).toMonoidHom = ⊤) : ∀ j ∈ J₀, j * j = 1 := by
  have hρJ : ∀ j ∈ J₀, ρ j = 1 := fun j hj => MonoidHom.mem_ker.1 (hρk ▸ hj)
  have hV'Z : ∀ v ∈ V₀, ρ v = 1 ∨ ρ v = zA ∨ ρ v = zB ∨ ρ v = zA * zB := by
    intro v hv
    have hvS : ρ v ∈ S06 := hT ▸ Subgroup.mem_map_of_mem ρ (hVT hv)
    refine mem_Z6_of_central_S06 hvS fun s hs => ?_
    rw [← hT] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact hVc v hv t ht
  have hgenV' : V₀.map ρ ⊔ (V₀.map ρ).map (MulAut.conj (ρ q)).toMonoidHom = ⊤ := by
    have h1 := congrArg (Subgroup.map ρ) hgen
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ hρs] at h1
    have h2 : (V₀.map (MulAut.conj q).toMonoidHom).map ρ =
        (V₀.map ρ).map (MulAut.conj (ρ q)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp
    rw [h2] at h1
    exact h1
  have hzA : zA ∈ V₀.map ρ := zA_mem_of_gen (by
    rintro _ ⟨v, hv, rfl⟩
    exact hV'Z v hv) hgenV'
  obtain ⟨v, hv, hρv⟩ := hzA
  have hsD : sD ∈ T₀.map ρ := hT ▸ sD_mem_S06
  obtain ⟨t₁, ht₁, hρt₁⟩ := hsD
  have hvt : v * t₁ = t₁ * v := by
    have hmem : t₁ * v * t₁⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 (hTV ht₁) v).1 hv
    have hρe : ρ (t₁ * v * t₁⁻¹ * v⁻¹) = 1 := by
      have hc : ρ t₁ * ρ v = ρ v * ρ t₁ := (hVc v hv t₁ ht₁).symm
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have he : t₁ * v * t₁⁻¹ * v⁻¹ ∈ V₀ ⊓ J₀ :=
      ⟨V₀.mul_mem hmem (V₀.inv_mem hv), by rw [← hρk]; exact MonoidHom.mem_ker.2 hρe⟩
    rw [hVJ, Subgroup.mem_bot] at he
    have h1 : t₁ * v * t₁⁻¹ = v := mul_inv_eq_one.1 he
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hgen' : Subgroup.closure {x : Q | x * x = 1} = ⊤ := by
    rw [eq_top_iff, ← hgen, sup_le_iff]
    constructor
    · exact fun x hx => Subgroup.subset_closure (hV₀ x hx)
    · rintro _ ⟨x, hx, rfl⟩
      refine Subgroup.subset_closure ?_
      show q * x * q⁻¹ * (q * x * q⁻¹) = 1
      have := hV₀ x hx
      calc q * x * q⁻¹ * (q * x * q⁻¹) = q * (x * x) * q⁻¹ := by group
        _ = 1 := by rw [this]; group
  have hJ2 : IsPGroup 2 J₀ := isPGroup_two_of_oddCoverExact J₀ hJc hOdd
    ((QuotientGroup.quotientMulEquivOfEq hρk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)) hgen'
  set Q₁ : Subgroup Q := (alternatingGroup (Fin 6)).comap ρ with hQ₁
  haveI : Q₁.Normal := Subgroup.Normal.comap inferInstance ρ
  have hmemQ₁ : ∀ x : Q, x ∈ Q₁ ↔ ρ x ∈ alternatingGroup (Fin 6) := fun x => Iff.rfl
  have hJQ₁ : J₀ ≤ Q₁ := fun j hj => by
    rw [hmemQ₁, hρJ j hj]
    exact Subgroup.one_mem _
  let ρ₁ : ↥Q₁ →* P6 := ρ.comp Q₁.subtype
  have hρ₁k : ρ₁.ker = J₀.subgroupOf Q₁ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hρk, MonoidHom.mem_ker]
    rfl
  have hρ₁r : ρ₁.range = alternatingGroup (Fin 6) := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro ha
      obtain ⟨x, rfl⟩ := hρs a
      exact ⟨⟨x, ha⟩, rfl⟩
  haveI : (J₀.subgroupOf Q₁).Normal := Subgroup.Normal.subgroupOf inferInstance Q₁
  have hJc₁ : J₀.subgroupOf Q₁ ≤ Subgroup.center ↥Q₁ := by
    rintro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hJc (Subgroup.mem_subgroupOf.1 hx)) g)
  have hJ2₁ : IsPGroup 2 ↥(J₀.subgroupOf Q₁) :=
    hJ2.of_equiv (Subgroup.subgroupOfEquivOfLe hJQ₁).symm
  have hvQ₁ : v ∈ Q₁ := by rw [hmemQ₁, hρv]; exact D0_le_A6 (by
    have : zA = rD * rD := rD_sq.symm
    rw [this]; exact D0.mul_mem rD_mem rD_mem)
  have ht₁Q₁ : t₁ ∈ Q₁ := by rw [hmemQ₁, hρt₁]; exact D0_le_A6 sD_mem
  have hcenter : Subgroup.center (commutator ↥Q₁) = ⊥ :=
    center_commutator_eq_bot_of_alt_six hKG (J₀.subgroupOf Q₁) hJc₁ hJ2₁ ρ₁ hρ₁k hρ₁r
      (v := ⟨v, hvQ₁⟩) (t := ⟨t₁, ht₁Q₁⟩) (Subtype.ext (hV₀ v hv)) hρv hρt₁
      (Subtype.ext hvt)
  set Λ : Subgroup Q := (commutator ↥Q₁).map Q₁.subtype with hΛ
  have hΛ' : Λ = ⁅Q₁, Q₁⁆ := Subgroup.map_subtype_commutator Q₁
  haveI : Λ.Normal := by rw [hΛ']; infer_instance
  have hS₁ := altSix_perfect (J₀.subgroupOf Q₁) ρ₁ hρ₁k hρ₁r
  have hsimp₁ := altSix_simple (J₀.subgroupOf Q₁) ρ₁ hρ₁k hρ₁r
  have hna₁ := altSix_nonabelian (J₀.subgroupOf Q₁) ρ₁ hρ₁k hρ₁r
  have hLJ := commutator_sup_eq_top (J₀.subgroupOf Q₁) hS₁
  have hΛJ : Λ ⊔ J₀ = Q₁ := by
    have h1 := congrArg (Subgroup.map Q₁.subtype) hLJ
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJQ₁, Subgroup.map_top,
      Subgroup.range_subtype] at h1
    exact h1
  obtain ⟨q', hq'⟩ := hρs (swap (0 : Fin 6) 1)
  have hq : ∀ x : Q, x ∈ Λ ⊔ J₀ ∨ q'⁻¹ * x ∈ Λ ⊔ J₀ := by
    intro x
    rw [hΛJ]
    by_cases hx : ρ x ∈ alternatingGroup (Fin 6)
    · exact Or.inl hx
    · right
      rw [hmemQ₁, map_mul, map_inv, hq', Equiv.Perm.mem_alternatingGroup]
      have hx' : ¬ Equiv.Perm.sign (ρ x) = 1 := fun h => hx (Equiv.Perm.mem_alternatingGroup.2 h)
      have hs : Equiv.Perm.sign (ρ x) = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign (ρ x)) with h | h
        · exact absurd h hx'
        · exact h
      rw [map_mul, map_inv, Equiv.Perm.sign_swap (by decide), hs]
      decide
  have hcomm := commutator_mem_of_index_two Λ J₀ hJc hq
  have hsq := sq_mem_of_gen Λ hcomm hgen'
  intro j hj
  obtain ⟨x', hx', hxj⟩ := hsq j
  have hx'J : x' ∈ J₀.subgroupOf Q₁ :=
    Subgroup.mem_subgroupOf.2
      (by rw [Subgroup.coe_subtype] at hxj; rw [hxj]; exact J₀.mul_mem hj hj)
  have hZ := map_center_commutator_eq (J₀.subgroupOf Q₁) hJc₁ hS₁ hsimp₁ hna₁
  rw [hcenter, Subgroup.map_bot] at hZ
  have hx0 : x' ∈ (⊥ : Subgroup ↥Q₁) := by
    have : x' ∈ commutator ↥Q₁ ⊓ J₀.subgroupOf Q₁ := ⟨hx', hx'J⟩
    rw [← hZ] at this
    exact this
  rw [Subgroup.mem_bot] at hx0
  rw [← hxj, hx0]
  rfl

theorem sq_eq_one_of_perm_six (hKG : KGI22One) (hOdd : OddCoverExact P6) (J₀ : Subgroup Q)
    [J₀.Normal] (hJc : J₀ ≤ Subgroup.center Q) (ρ : Q →* P6) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker = J₀) (V₀ T₀ : Subgroup Q) (hV₀ : ∀ v ∈ V₀, v * v = 1) (hVJ : V₀ ⊓ J₀ = ⊥)
    (hVT : V₀ ≤ T₀) (hTV : T₀ ≤ Subgroup.normalizer (V₀ : Set Q))
    (hSyl : IsSylowTwoOf (T₀.map ρ) ⊤)
    (hVc : ∀ v ∈ V₀, ∀ t ∈ T₀, ρ v * ρ t = ρ t * ρ v) {q : Q}
    (hgen : V₀ ⊔ V₀.map (MulAut.conj q).toMonoidHom = ⊤) : ∀ j ∈ J₀, j * j = 1 := by
  obtain ⟨c, hc⟩ := exists_conj_of_isSylowTwoOf_top hSyl isSylowTwoOf_S06
  let ρ' : Q →* P6 := (MulAut.conj c).toMonoidHom.comp ρ
  have hρ's : Function.Surjective ρ' := (MulAut.conj c).surjective.comp hρs
  have hρ'k : ρ'.ker = J₀ := by
    rw [← hρk]
    ext x
    simp only [ρ', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  refine sq_eq_one_of_perm_six_aux hKG hOdd J₀ hJc ρ' hρ's hρ'k V₀ T₀ hV₀ hVJ hVT hTV ?_ ?_ hgen
  · rw [← hc, Subgroup.map_map]
  · intro v hv t ht
    have h := hVc v hv t ht
    set f := (MulAut.conj c).toMonoidHom with hf
    show f (ρ v) * f (ρ t) = f (ρ t) * f (ρ v)
    calc f (ρ v) * f (ρ t) = f (ρ v * ρ t) := (map_mul f _ _).symm
      _ = f (ρ t * ρ v) := by rw [h]
      _ = f (ρ t) * f (ρ v) := map_mul f _ _

end Main

end CFSG.Quasithin.RonanE211
