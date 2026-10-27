module

public import CFSG.Quasithin.Vol2.Ch11G2Q8OffRealRad
public import CFSG.Quasithin.Vol2.Ch11G2Q8OffLines
public import CFSG.Quasithin.Vol2.Ch10SecABasicAut
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open scoped IsMulCommutative commutatorElement

variable {K : Type} [Field K] [CharP K 2]

theorem qr_tL (s : K) (x : Ix3 → K) : qr (tL s) x = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  conv_lhs => rw [q6_eta x]
  simp only [qr, g2Act_tL, polarQ, q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0,
    q6_apply_inr1, q6_apply_inr2]
  linear_combination (x (.inl 0) * x (.inr 0) + s * x (.inl 2) * x (.inr 0) +
    x (.inl 1) * x (.inr 1) + x (.inl 2) * x (.inr 2)) * h2

theorem qr_A1_eq_zero {d : Option K} {w : Ix3 → K} (hw : FixD d w) {γ : ↥(cayleyGroup K)}
    (hγ : γ ∈ A1 K) : qr γ w = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hd, -⟩ := (fixD_iff d w).mp hw
  obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hγ
  conv_lhs => rw [q6_eta w]
  simp only [qr, g2Act_A1, polarQ, q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0,
    q6_apply_inr1, q6_apply_inr2]
  rw [hd]
  linear_combination (w (.inl 1) * w (.inr 1) + w (.inl 2) * w (.inr 2) +
    α * w (.inl 1) * w (.inl 2)) * h2

theorem factG2OffenderRad_holds : FactG2OffenderRad := by
  intro G _ _ L V X T V₁ V₂ V₃ n hfl _ A hAN hAel haS
  obtain ⟨_, K, _, _, _, hK, π, f, hf, c₀, hc0, hc1, g, -, hV₁, hV₂, hV₃⟩ :=
    exists_coord_flagG2 hfl
  have hn := hfl.two_le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_cayleyGroup (F := K)
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hLV := hfl.le_normalizer
  have h₁ : V₁ ≤ V := hfl.le₁₂.trans (hfl.le₂₃.trans hfl.le₃)
  have h₂ : V₂ ≤ V := hfl.le₂₃.trans hfl.le₃
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hfl.elem.2 w w.2)
  have hsurj : Function.Surjective f := hf.surj
  have hZfix : ∀ h ∈ autOn L V, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V,
      h z = z := fun h hh z hz => autOn_apply_of_mem_centralizer hh hz
  have hcomm : commV (autOn L V) = ⊤ := by
    rw [Ch10.SecA.commV_autOn_eq hLV, hfl.commutator_eq, Subgroup.subgroupOf_self]
  obtain ⟨hĀX, hĀne, ⟨hĀc, hĀ2⟩, hĀP⟩ := haS
  have hĀX' : autOn A V ≤ autOn X V := hĀX
  have hĀ1 : ∀ φ ∈ autOn A V, φ * φ = 1 := fun φ hφ => by
    rw [← sq]
    exact hĀ2 φ hφ
  have hPĀ : ∀ B ≤ autOn A V, Nat.card ↥(autOn A V) < Nat.card K ^ 2 * Nat.card ↥B →
      ∀ v : ↥V, (∀ b ∈ B, b v = v) → ∀ φ ∈ autOn A V, φ v = v := by
    intro B hB hcard v hv φ hφ
    have h1 := Subgroup.relIndex_mul_card (H := B) (K := autOn A V)
    rw [inf_of_le_left hB] at h1
    have hidx : B.relIndex (autOn A V) < 2 ^ (2 * n) := by
      rw [mul_comm 2 n, pow_mul, ← hK]
      by_contra hge
      have h3 := Nat.mul_le_mul_right (Nat.card ↥B) (not_lt.mp hge)
      rw [h1] at h3
      omega
    have hm : E3.mQuot (autOn A V) B < 2 * n := by
      have h0 : B.relIndex (autOn A V) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h1
        exact Nat.card_pos.ne' h1.symm
      exact (padicValNat_le_nat_log _).trans_lt (Nat.log_lt_of_lt_pow h0 hidx)
    have h4 := hĀP B hB hm
    have h3 : v ∈ fixV (V := IntMod V hfl.elem) B := fun b hb => hv b hb
    rw [h4] at h3
    exact h3 φ hφ
  obtain ⟨Φ, hΦinj, hΦ, hΦρ⟩ := exists_g2Hom_rad hf hsq hcomm hc0 hc1 hK hn hfl.normalizer_le
    hĀX' hĀ1 (by rw [sq]; exact lt_mul_self hq) hPĀ
  have hΓ1 : ∀ γ ∈ Φ.range, γ * γ = 1 := by
    rintro _ ⟨φ, rfl⟩
    rw [← map_mul, show φ * φ = 1 from Subtype.ext (hĀ1 φ φ.2), map_one]
  have hΓc : ∀ γ ∈ Φ.range, ∀ δ ∈ Φ.range, γ * δ = δ * γ := by
    rintro _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩
    rw [← map_mul, ← map_mul, show φ * ψ = ψ * φ from
      Subtype.ext (hĀc (φ : MulAut ↥V) φ.2 (ψ : MulAut ↥V) ψ.2)]
  have hΓne : Φ.range ≠ ⊥ := by
    intro h
    apply hĀne
    rw [eq_bot_iff]
    intro φ hφ
    have h1 : Φ ⟨φ, hφ⟩ ∈ Φ.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one Φ] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hΦinj h1))
  have hPΓ : FixStable (Nat.card K ^ 2) Φ.range := by
    intro B hB hcard w hw γ hγ
    have hcB : Nat.card ↥((B.comap Φ).map (autOn A V).subtype) = Nat.card ↥B := by
      rw [Subgroup.card_map_of_injective Subtype.val_injective]
      have hmap : (B.comap Φ).map Φ = B := Subgroup.map_comap_eq_self (hB.trans le_rfl)
      rw [← hmap, Subgroup.card_map_of_injective hΦinj, hmap]
    have hcΓ : Nat.card ↥Φ.range = Nat.card ↥(autOn A V) := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hΦinj, Subgroup.card_top]
    obtain ⟨v, rfl⟩ := hsurj w
    have h1 := hPĀ _ (Subgroup.map_subtype_le _) (by rw [hcB, ← hcΓ]; exact hcard) v (by
      rintro _ ⟨φ, hφ, rfl⟩
      rw [Subgroup.coe_subtype, hΦρ φ]
      exact rhoG_fix hK hn hf hc0 hc1 hsq hZfix (hw _ hφ))
    obtain ⟨φ, rfl⟩ := hγ
    rw [← hΦ, h1 φ φ.2]
  obtain ⟨x₀, hx₀⟩ := eq_conj_A1 hK (by omega) hΓ1 hΓc hΓne hPΓ
  let ι : ↥A →* ↥(autOn A V) :=
    { toFun := fun a => ⟨SecA.conjV V a (hAN a.2), SecA.conjV_mem_autOn a.2 _⟩
      map_one' := Subtype.ext (by
        ext v
        simp [SecA.conjV_apply_coe])
      map_mul' := fun a b => Subtype.ext (SecA.conjV_mul V (hAN a.2) (hAN b.2)) }
  have hιs : Function.Surjective ι := by
    rintro ⟨φ, hφ⟩
    obtain ⟨a, haA, haV, rfl⟩ := SecA.mem_autOn_iff.mp hφ
    exact ⟨⟨a, haA⟩, rfl⟩
  have hι : ∀ a : ↥A, ((ι a : ↥(autOn A V)) : MulAut ↥V) = SecA.conjV V a (hAN a.2) :=
    fun _ => rfl
  have hact : ∀ (a : ↥A) (w : ↥V), f (SecA.conjV V a (hAN a.2) w) = g2Act (Φ (ι a)) (f w) :=
    fun a w => hΦ (ι a) w
  have hrange : (Φ.comp ι).range = Φ.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hιs, ← MonoidHom.range_eq_map]
  obtain ⟨l, hlL, hlV, hl⟩ := SecA.mem_autOn_iff.mp (rhoG hc0 hc1 π (g * x₀⁻¹)).2
  have hP₁ := subgroupOf_conjSubgroup_eq hf hc0 hc1 hV₁ hlV hl
  have hP₃ := subgroupOf_conjSubgroup_eq hf hc0 hc1 hV₃ hlV hl
  rw [show (g * x₀⁻¹)⁻¹ * g = x₀ by group] at hP₁ hP₃
  refine ⟨l, hlL, fun x hxL hx1 hx3 => ?_⟩
  obtain ⟨ax, hax⟩ := exists_rhoG_eq_conjV hf hc0 hc1 hxL (hLV hxL)
  have hI := subgroupOf_conjSubgroup_eq hf hc0 hc1 hV₂ (hLV hxL) hax
  obtain ⟨c, hc⟩ : ∃ c, c = ax⁻¹ * g := ⟨_, rfl⟩
  rw [← hc] at hI
  have hIV : conjSubgroup V₂ x ≤ V := conjSubgroup_le_of_le h₂ (hLV hxL)
  have hmemI : ∀ v : ↥V, (v : G) ∈ conjSubgroup V₂ x ↔ f v ∈ gmapG c (stdF K 2) := by
    intro v
    have h1 : v ∈ (conjSubgroup V₂ x).subgroupOf V ↔ (v : G) ∈ conjSubgroup V₂ x := Iff.rfl
    rw [← h1, hI, hf.mem_pre, Submodule.mem_toAddSubgroup]
  have hle : ∀ {U : Subgroup G} {S S' : Submodule K (Ix3 → K)} {y y' : ↥(cayleyGroup K)},
      U ≤ V → U.subgroupOf V = hf.pre (gmapG y S).toAddSubgroup →
      conjSubgroup V₂ x = U ∨ True → U ≤ conjSubgroup V₂ x →
      S' = S → y' = y → gmapG y' S' ≤ gmapG c (stdF K 2) := by
    intro U S S' y y' hUV hU _ hUI hS hy z hz
    subst hS hy
    obtain ⟨v, rfl⟩ := hsurj z
    have hvU : v ∈ U.subgroupOf V := by
      rw [hU, hf.mem_pre, Submodule.mem_toAddSubgroup]
      exact hz
    exact (hmemI v).mp (hUI hvU)
  have hy1 : stdF K 1 ≤ gmapG (x₀⁻¹ * c) (stdF K 2) := by
    intro z hz
    have h1 : g2Act x₀ z ∈ gmapG x₀ (stdF K 1) := by
      rw [mem_gmapG, g2Act_inv_apply]
      exact hz
    have h3 := hle (conjSubgroup_le_of_le h₁ hlV) hP₁ (Or.inr trivial) hx1 rfl rfl h1
    rw [mem_gmapG] at h3 ⊢
    rwa [_root_.mul_inv_rev, inv_inv, g2Act_mul_apply]
  have hy3 : gmapG (x₀⁻¹ * c) (stdF K 2) ≤ stdF K 3 := by
    intro z hz
    obtain ⟨v, hv⟩ := hsurj (g2Act x₀ z)
    have h1 : f v ∈ gmapG c (stdF K 2) := by
      rw [hv, mem_gmapG]
      rw [mem_gmapG, _root_.mul_inv_rev, inv_inv, g2Act_mul_apply] at hz
      exact hz
    have h3 : v ∈ (conjSubgroup V₃ l).subgroupOf V := hx3 ((hmemI v).mpr h1)
    rw [hP₃, hf.mem_pre, Submodule.mem_toAddSubgroup, mem_gmapG, hv, g2Act_inv_apply] at h3
    exact h3
  obtain ⟨d, hd⟩ := exists_inLine_of_le (x₀⁻¹ * c) hy1 hy3
  have hlineQ : ∀ y : Ix3 → K, y ∈ gmapG c (stdF K 2) ↔ InLine d (g2Act x₀⁻¹ y) := by
    intro y
    rw [← hd, mem_gmapG, mem_gmapG, _root_.mul_inv_rev, inv_inv, g2Act_mul_apply,
      g2Act_apply_inv]
  let Dz : Subgroup ↥(cayleyGroup K) := (rootD d).map (MulAut.conj x₀).toMonoidHom
  let D : Subgroup G := (Dz.comap (Φ.comp ι)).map A.subtype
  have hDA : D ≤ A := Subgroup.map_subtype_le _
  have hmemD : ∀ a : ↥A, (a : G) ∈ D ↔ Φ (ι a) ∈ Dz := by
    intro a
    constructor
    · rintro ⟨b, hb, hab⟩
      have : b = a := Subtype.ext hab
      rw [← this]
      exact hb
    · intro h
      exact ⟨a, h, rfl⟩
  have hDz : ∀ γ : ↥(cayleyGroup K), γ ∈ Dz ↔ x₀⁻¹ * γ * x₀ ∈ rootD d := by
    intro γ
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      change x₀⁻¹ * (x₀ * δ * x₀⁻¹) * x₀ ∈ rootD d
      rwa [show x₀⁻¹ * (x₀ * δ * x₀⁻¹) * x₀ = δ by group]
    · intro h
      exact ⟨_, h, by change x₀ * (x₀⁻¹ * γ * x₀) * x₀⁻¹ = γ; group⟩
  have hΓA1 : ∀ a : ↥A, x₀⁻¹ * Φ (ι a) * x₀ ∈ A1 K := by
    intro a
    have h1 : Φ (ι a) ∈ Φ.range := ⟨_, rfl⟩
    rw [hx₀] at h1
    obtain ⟨δ, hδ, hδeq⟩ := h1
    rw [← hδeq]
    change x₀⁻¹ * (x₀ * δ * x₀⁻¹) * x₀ ∈ A1 K
    rwa [show x₀⁻¹ * (x₀ * δ * x₀⁻¹) * x₀ = δ by group]
  have hconjA : ∀ (a : ↥A) (v : ↥V), (a : G) * v = v * a ↔
      SecA.conjV V a (hAN a.2) v = v := by
    intro a v
    constructor
    · intro h
      exact Subtype.ext (by rw [SecA.conjV_apply_coe, h, mul_inv_cancel_right])
    · intro h
      have h1 := congrArg Subtype.val h
      rw [SecA.conjV_apply_coe] at h1
      calc (a : G) * v = a * v * (a : G)⁻¹ * a := by group
        _ = v * a := by rw [h1]
  have hfixΦ : ∀ (a : ↥A) (v : ↥V), (a : G) * v = v * a ↔
      g2Act (x₀⁻¹ * Φ (ι a) * x₀) (g2Act x₀⁻¹ (f v)) = g2Act x₀⁻¹ (f v) := by
    intro a v
    rw [hconjA, g2Act_mul_apply, g2Act_mul_apply, g2Act_apply_inv]
    constructor
    · intro h
      rw [← hact, h]
    · intro h
      have h1 := congrArg (g2Act x₀) h
      rw [g2Act_apply_inv, g2Act_apply_inv] at h1
      have h3 := rhoG_fix hK hn hf hc0 hc1 hsq hZfix h1
      rwa [← hΦρ (ι a), hι] at h3
  have hCD : ∀ v : ↥V, (v : G) ∈ Subgroup.centralizer (D : Set G) ↔
      FixD d (g2Act x₀⁻¹ (f v)) := by
    intro v
    constructor
    · intro hv δ hδ
      have hmem : x₀ * δ * x₀⁻¹ ∈ (Φ.comp ι).range := by
        rw [hrange, hx₀]
        exact ⟨δ, rootD_le_A1 d hδ, rfl⟩
      obtain ⟨a, ha⟩ := hmem
      have ha' : Φ (ι a) = x₀ * δ * x₀⁻¹ := ha
      have haD : (a : G) ∈ D := (hmemD a).mpr (by rw [ha']; exact ⟨δ, hδ, rfl⟩)
      have h1 := (hfixΦ a v).mp (Subgroup.mem_centralizer_iff.mp hv _ haD)
      rwa [ha', show x₀⁻¹ * (x₀ * δ * x₀⁻¹) * x₀ = δ by group] at h1
    · intro hv
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨a, haDz, rfl⟩
      have h1 : x₀⁻¹ * Φ (ι a) * x₀ ∈ rootD d := (hDz _).mp haDz
      exact (hfixΦ a v).mpr (hv _ h1)
  obtain ⟨vt, hvt⟩ : ∃ vt : Subgroup ↥V,
      vt = (commHom (psiG hc0 hc1 π c (tL 1))).range := ⟨_, rfl⟩
  have hLIV : LOf L (conjSubgroup V₂ x) ≤ Subgroup.normalizer (V : Set G) :=
    ((perfectCore_le _).trans inf_le_left).trans hLV
  have hLU : autOn (LOf L (conjSubgroup V₂ x)) V =
      (perfectCore (stabQ (stdF K 2))).map (psiG hc0 hc1 π c) := by
    rw [SecA.autOn_lOf hLV hIV, hI]
    exact gammaW_two_eqG hf hc0 hc1 c
  have hR : (⁅conjSubgroup V₂ x, LOf L (conjSubgroup V₂ x)⁆).subgroupOf V = vt := by
    rw [← commS_autOn_eq hIV hLIV, hLU, hI, hvt]
    exact commS_eq_vt hf hc0 hc1 c hsq hZfix
  have hgen : ∀ (a : ↥A) (v : ↥V), (v : G) ∈ Subgroup.centralizer (D : Set G) →
      SecA.conjV V a (hAN a.2) v * v⁻¹ ∈ vt := by
    intro a v hv
    have hw := (hCD v).mp hv
    have hδ := hΓA1 a
    have he : g2Act (Φ (ι a)) (f v) - f v ∈ gmapG c (stdF K 2) := by
      rw [hlineQ, map_sub]
      have h1 := comm_inLine hw hδ
      rwa [g2Act_mul_apply, g2Act_mul_apply, g2Act_apply_inv] at h1
    obtain ⟨y, hy⟩ := exists_tL_sub_eq one_ne_zero (mem_gmapG.mp he)
    obtain ⟨u, hu⟩ := hsurj (g2Act c y)
    have hcomm' := rhoG_comm_eq hK hn hf hc0 hc1 hsq hZfix (γ₁ := Φ (ι a))
      (γ₂ := c * tL 1 * c⁻¹) (w₁ := v) (w₂ := u)
      (by rw [hu, g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply, ← map_sub, hy,
        g2Act_apply_inv])
      (by
        have h1 := qr_conj x₀ (x₀⁻¹ * Φ (ι a) * x₀) (g2Act x₀⁻¹ (f v))
        rw [show x₀ * (x₀⁻¹ * Φ (ι a) * x₀) * x₀⁻¹ = Φ (ι a) by group, g2Act_apply_inv] at h1
        rw [h1, qr_A1_eq_zero hw hδ, hu, qr_conj, qr_tL])
    rw [hvt]
    refine ⟨u, ?_⟩
    rw [commHom_apply, psiG_apply, ← hcomm', ← hΦρ (ι a), hι]
  refine ⟨D, hDA, ?_, ?_, ?_, ?_⟩
  ·
    rintro a ⟨haA, haV⟩
    refine (hmemD ⟨a, haA⟩).mpr ?_
    have h1 : ι ⟨a, haA⟩ = 1 := by
      apply Subtype.ext
      refine MulEquiv.ext fun v => ?_
      exact ((hconjA ⟨a, haA⟩ v).mp (Subgroup.mem_centralizer_iff.mp haV v v.2).symm)
    rw [h1, map_one]
    exact Dz.one_mem
  ·
    have hsub : D.subgroupOf A = Dz.comap (Φ.comp ι) :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective A) _
    have hidx : D.relIndex A = Nat.card K ^ 2 := by
      rw [Subgroup.relIndex, hsub, Subgroup.index_comap, hrange, hx₀,
        Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj x₀).injective,
        relIndex_rootD_A1]
    rw [E3.mQuot, hidx, hK, ← pow_mul, mul_comm n 2, padicValNat.prime_pow]
  ·
    apply le_antisymm
    · rintro a ⟨haA, haC⟩
      refine (hmemD ⟨a, haA⟩).mpr ((hDz _).mpr (mem_rootD_of_fixD (hΓA1 _) fun w hw => ?_))
      obtain ⟨v, hv⟩ := hsurj (g2Act x₀ w)
      have hvC : (v : G) ∈ V ⊓ Subgroup.centralizer (D : Set G) :=
        ⟨v.2, (hCD v).mpr (by rw [hv, g2Act_inv_apply]; exact hw)⟩
      have h1 := (hfixΦ ⟨a, haA⟩ v).mp (Subgroup.mem_centralizer_iff.mp haC _ hvC).symm
      rwa [hv, g2Act_inv_apply] at h1
    · intro a haD
      refine ⟨hDA haD, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp hz.2 a haD).symm
  ·
    have hCDle : (⁅V ⊓ Subgroup.centralizer (D : Set G), A⁆).subgroupOf V = vt := by
      apply le_antisymm
      ·
        have hle' : ⁅V ⊓ Subgroup.centralizer (D : Set G), A⁆ ≤ vt.map V.subtype := by
          rw [Subgroup.commutator_le]
          intro z hz a haA
          have hmem := hgen ⟨a, haA⟩ ⟨z, hz.1⟩ hz.2
          refine ⟨(SecA.conjV V a (hAN haA) ⟨z, hz.1⟩ * (⟨z, hz.1⟩ : ↥V)⁻¹)⁻¹,
            vt.inv_mem hmem, ?_⟩
          simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul,
            SecA.conjV_apply_coe]
          rw [commutatorElement_def]
          group
        intro v hv
        rw [Subgroup.mem_subgroupOf] at hv
        obtain ⟨w, hw, hwv⟩ := hle' hv
        rwa [← Subtype.ext hwv]
      ·
        intro u hu
        have huI : f u ∈ gmapG c (stdF K 2) := by
          rw [hvt] at hu
          exact mem_gmapG.mpr (mem_gmapG.mp (vt_le_U2 hf hc0 hc1 c 1 hu))
        obtain ⟨w₁, w₂, γ₁, γ₂, hw₁, hw₂, hγ₁, hγ₂, hsum⟩ := exists_comm_eq ((hlineQ _).mp huI)
        have hγA : ∀ γ ∈ A1 K, ∃ a : ↥A, Φ (ι a) = x₀ * γ * x₀⁻¹ := by
          intro γ hγ
          have hmem : x₀ * γ * x₀⁻¹ ∈ (Φ.comp ι).range := by
            rw [hrange, hx₀]
            exact ⟨γ, hγ, rfl⟩
          obtain ⟨a, ha⟩ := hmem
          exact ⟨a, ha⟩
        obtain ⟨a₁, ha₁⟩ := hγA γ₁ hγ₁
        obtain ⟨a₂, ha₂⟩ := hγA γ₂ hγ₂
        obtain ⟨v₁, hv₁⟩ := hsurj (g2Act x₀ w₁)
        obtain ⟨v₂, hv₂⟩ := hsurj (g2Act x₀ w₂)
        have hv₁C : (v₁ : G) ∈ Subgroup.centralizer (D : Set G) :=
          (hCD v₁).mpr (by rw [hv₁, g2Act_inv_apply]; exact hw₁)
        have hv₂C : (v₂ : G) ∈ Subgroup.centralizer (D : Set G) :=
          (hCD v₂).mpr (by rw [hv₂, g2Act_inv_apply]; exact hw₂)
        obtain ⟨p, hp⟩ : ∃ p : ↥V, p = (SecA.conjV V a₁ (hAN a₁.2) v₁ * v₁⁻¹) *
            (SecA.conjV V a₂ (hAN a₂.2) v₂ * v₂⁻¹) := ⟨_, rfl⟩
        have hpvt : p ∈ vt := by
          rw [hp]
          exact vt.mul_mem (hgen a₁ v₁ hv₁C) (hgen a₂ v₂ hv₂C)
        have hfp : f p = f u := by
          rw [hp, hf.map_mul, hf.map_mul_inv, hf.map_mul_inv, hact, hact, ha₁, ha₂, hv₁, hv₂]
          have h3 := congrArg (g2Act x₀) hsum
          rw [g2Act_apply_inv, map_add, map_sub, map_sub] at h3
          rw [h3, g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply, g2Act_mul_apply,
            g2Act_mul_apply, g2Act_inv_apply]
        have hup : u * p⁻¹ ∈ vt ⊓ (Subgroup.centralizer (L : Set G)).subgroupOf V :=
          ⟨vt.mul_mem hu (vt.inv_mem hpvt), eq_of_f_eq hf hfp.symm⟩
        have ha : ((Units.mk0 c₀ hc0 : Kˣ) : K) ≠ 1 := hc1
        rw [hvt, vt_inf_Z hf hc0 hc1 c hsq hZfix one_ne_zero ha, Subgroup.mem_bot,
          mul_inv_eq_one] at hup
        rw [hup, hp]
        rw [Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SecA.conjV_apply_coe]
        refine Subgroup.mul_mem _ ?_ ?_
        · have hv₁m : (v₁ : G) ∈ V ⊓ Subgroup.centralizer (D : Set G) := ⟨v₁.2, hv₁C⟩
          have h1 := Subgroup.commutator_mem_commutator hv₁m a₁.2
          have h3 := Subgroup.inv_mem _ h1
          rw [commutatorElement_def] at h3
          convert h3 using 1
          group
        · have hv₂m : (v₂ : G) ∈ V ⊓ Subgroup.centralizer (D : Set G) := ⟨v₂.2, hv₂C⟩
          have h1 := Subgroup.commutator_mem_commutator hv₂m a₂.2
          have h3 := Subgroup.inv_mem _ h1
          rw [commutatorElement_def] at h3
          convert h3 using 1
          group
    have h1 := Subgroup.subgroupOf_inj.mp (hCDle.trans hR.symm)
    rwa [inf_of_le_left (commutator_le_of_le_of_normalizer inf_le_left hAN),
      inf_of_le_left (commutator_le_of_le_of_normalizer hIV hLIV)] at h1

end CFSG.Quasithin.Vol2.Ch11.G2Q8
