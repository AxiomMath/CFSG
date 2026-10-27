module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Good
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Tr

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem isGoodInv_conj {g a : Ah} (hg : IsGoodInv g)
    (ha : a ∈ Bh) : IsGoodInv (a * g * a⁻¹) := by
  obtain ⟨hgB, hgY, hg2, hgc⟩ := hg
  refine ⟨Bh.mul_mem (Bh.mul_mem ha hgB) (Bh.inv_mem ha), ?_, ?_, ?_⟩
  · intro h
    apply hgY
    have := Yh_normal.conj_mem _ h a⁻¹
    simpa [mul_assoc] using this
  · calc (a * g * a⁻¹) ^ 2 = a * g ^ 2 * a⁻¹ := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hg2]; group
  · rw [card_centralizer_conj g a]
    exact hgc

theorem good_conj_That {f : Ah}
    (hf : f ∈ That) (hg : IsGoodInv f) : ∃ m ∈ That, f = m * fhatA * m⁻¹ := by
  obtain ⟨hfB, hfY, hf2, hfc⟩ := hg
  have hf2' : f * f = 1 := by rw [← pow_two]; exact hf2
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff f).1 hf
  have hl_out : l ∉ Tl := fun hlT => by
    obtain ⟨y, -, hyrep⟩ := exists_T_of_mem_Tl hlT
    have : f = incl y := Subtype.ext (eq_of_repL hrep hyrep)
    exact hfY (this ▸ (mem_Yh_iff_incl _).2 ⟨y, rfl⟩)
  have hl2 : comp l l = idL := repL_unique (repL_mul hrep hrep) (by
    have : (f : P45) * (f : P45) = 1 := congrArg Subtype.val hf2'
    rw [this]
    exact repL_one 45)
  rcases outer_classify l hl hl_out hl2 with ⟨m, hm, hmeq⟩ | ⟨w, hw, hweq⟩
  · obtain ⟨m', hm', hmrep⟩ := exists_That_of_mem_Thl hm
    refine ⟨m', hm', ?_⟩
    have h1 : f * m' = m' * fhatA := by
      apply Subtype.ext
      apply eq_of_repL (l := comp l m)
      · exact repL_mul hrep hmrep
      · rw [hmeq]
        exact repL_mul hmrep repL_fhat
    calc f = (f * m') * m'⁻¹ := by group
      _ = (m' * fhatA) * m'⁻¹ := by rw [h1]
  · exfalso
    set h : Ah := ⟨wordAP w, wordAP_mem w⟩ with hh
    have h1 : f * h = h * e0A := by
      apply Subtype.ext
      apply eq_of_repL (l := comp l (evalAL w))
      · exact repL_mul hrep (repL_wordAP w)
      · rw [hweq]
        exact repL_mul (repL_wordAP w) repL_e0A
    have h2 : f = h * e0A * h⁻¹ := by
      calc f = (f * h) * h⁻¹ := by group
        _ = h * e0A * h⁻¹ := by rw [h1]
    rw [h2, card_centralizer_conj e0A h] at hfc
    have := card_cent_e0_lt
    omega

theorem exists_toG_eq {G : Type} [Group G] {M₁ M₂ : Subgroup G} (iso : AutIso M₁ M₂) {b : G}
    (hb : b ∈ M₁ ⊓ M₂) : ∃ bh : Bh, iso.toG bh = b :=
  ⟨iso.phiB.symm ⟨b, hb⟩, congrArg Subtype.val (iso.phiB.apply_symm_apply ⟨b, hb⟩)⟩

section Norm

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem exists_norm
    (c : AutCtx G M₁ M₂ z) {T : Subgroup G} (hT : IsSylowTwoOf T (M₁ ⊓ M₂)) {f : G} (hfT : f ∈ T)
    (hf : c.IsGoodAt f) :
    ∃ g ∈ M₁ ⊓ M₂, g * z * g⁻¹ = z ∧ T = B6.conjSub g (c.iso.imgG That) ∧
      f = g * c.iso.toG fhB * g⁻¹ := by
  obtain ⟨b, hbB, hTb⟩ := B6.isSylowTwoOf_exists_conj (isSylowTwoOf_imgG_That c.iso) hT
  obtain ⟨bh, hbh⟩ := exists_toG_eq c.iso hbB
  obtain ⟨f', hf'good, rfl⟩ := hf
  have h1 : b⁻¹ * c.iso.toG f' * b ∈ c.iso.imgG That := B6.mem_conjSub.1 (hTb ▸ hfT)
  have h2 : c.iso.toG (bh⁻¹ * f' * bh) = b⁻¹ * c.iso.toG f' * b := by
    rw [AutIso.toG_mul, AutIso.toG_mul, AutIso.toG_inv, hbh]
  obtain ⟨f₁, hf₁T, hf₁⟩ := c.iso.mem_imgG.1 (h2 ▸ h1)
  have hf₁eq : f₁ = bh⁻¹ * f' * bh := c.iso.toG_injective hf₁
  have hgood₁ : IsGoodInv (f₁ : Ah) := by
    rw [hf₁eq]
    have := isGoodInv_conj hf'good (Bh.inv_mem bh.2)
    simpa [mul_assoc] using this
  obtain ⟨m, hm, hfm⟩ := good_conj_That hf₁T hgood₁
  set mB : Bh := ⟨m, That_le_Bh hm⟩ with hmB
  have hf₁m : f₁ = mB * fhB * mB⁻¹ := Subtype.ext hfm
  have hzc : ∀ h ∈ M₁ ⊓ M₂, h * z = z * h := fun h hh =>
    Subgroup.mem_centralizer_iff.1 c.zc.2 h hh
  have hmG : c.iso.toG mB ∈ c.iso.imgG That := c.iso.mem_imgG.2 ⟨mB, hm, rfl⟩
  refine ⟨b * c.iso.toG mB, Subgroup.mul_mem _ hbB (c.iso.toG_mem mB), ?_, ?_, ?_⟩
  · have hb : b * z = z * b := hzc b hbB
    have hm' : c.iso.toG mB * z = z * c.iso.toG mB := hzc _ (c.iso.toG_mem mB)
    calc b * c.iso.toG mB * z * (b * c.iso.toG mB)⁻¹
        = b * (c.iso.toG mB * z) * (c.iso.toG mB)⁻¹ * b⁻¹ := by group
      _ = b * (z * c.iso.toG mB) * (c.iso.toG mB)⁻¹ * b⁻¹ := by rw [hm']
      _ = b * z * b⁻¹ := by group
      _ = z := by rw [hb]; group
  · rw [hTb, B6.conjSub_mul, B6.conjSub_eq_self (Subgroup.le_normalizer hmG)]
  · have h3 : c.iso.toG f' = b * c.iso.toG f₁ * b⁻¹ := by
      rw [hf₁, h2]
      group
    rw [h3, hf₁m, AutIso.toG_mul, AutIso.toG_mul, AutIso.toG_inv]
    group

end Norm

end CFSG.Quasithin.H13.F431.U42Aut
