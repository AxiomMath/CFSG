module

public import CFSG.Quasithin.Recognition.RuTypeJ27i

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem z_mem_TB : M.z ∈ M.TB := M.SB_le_TB M.z_mem_SB

theorem B_le_H : M.B ≤ ruH M.T := Subgroup.zpowers_le.mpr M.bel_mem_H

theorem bel_comm_z : (M.bel : G) * M.z = M.z * M.bel := M.mem_GB.mp (M.TB_le_GB M.z_mem_TB)

theorem z_mul_inv {c : G} (hc : c * M.bel * c⁻¹ = (M.bel : G)⁻¹) :
    (M.z * c) * M.bel * (M.z * c)⁻¹ = (M.bel : G)⁻¹ := by
  have hbz : Commute (M.bel : G) M.z := M.bel_comm_z
  calc (M.z * c) * M.bel * (M.z * c)⁻¹ = M.z * (c * M.bel * c⁻¹) * M.z⁻¹ := by group
    _ = M.z * (M.bel : G)⁻¹ * M.z⁻¹ := by rw [hc]
    _ = (M.bel : G)⁻¹ := by rw [← hbz.inv_left.eq]; group

theorem comm_TB_of_central {c : G} (hc : c ∈ M.GP)
    (hcomm : ∀ g ∈ M.GP, ∃ b ∈ M.B, c * g = g * c * b) {t : G} (ht : t ∈ M.TB) :
    c * t = t * c := by
  have htGB : t ∈ M.GB := M.TB_le_GB ht
  obtain ⟨b, hb, hbt⟩ := hcomm t (M.GB_le_GP htGB)
  set b' := c * b * c⁻¹ with hb'def
  have hb' : b' ∈ M.B := M.conj_mem_B hc hb
  have hu : c * t * c⁻¹ = t * b' := by rw [hbt, hb'def]; group
  have ht16 : t ^ 16 = 1 := by
    have h := pow_card_eq_one' (G := M.TB) (x := ⟨t, ht⟩)
    rw [M.card_TB] at h
    have := congrArg Subtype.val h
    simpa using this
  have hcomm' : Commute t b' := (Subgroup.mem_centralizer_iff.mp htGB b' hb').symm
  have h16 : (t * b') ^ 16 = b' := by
    rw [hcomm'.mul_pow, ht16, one_mul]
    have h3 := M.pow_three_of_mem_B hb'
    calc b' ^ 16 = (b' ^ 3) ^ 5 * b' := by group
      _ = b' := by rw [h3]; group
  have hu16 : (c * t * c⁻¹) ^ 16 = 1 := by rw [conj_pow, ht16]; group
  rw [hu, h16] at hu16
  have h1 : c * t * c⁻¹ = t := by rw [hu, hu16, mul_one]
  calc c * t = (c * t * c⁻¹) * c := by group
    _ = t * c := by rw [h1]

theorem mem_H_of_central {c : G} (hc : c ∈ M.GP)
    (hcomm : ∀ g ∈ M.GP, ∃ b ∈ M.B, c * g = g * c * b) : c ∈ ruH M.T :=
  M.mem_H_iff_comm.mpr (M.comm_TB_of_central hc hcomm M.z_mem_TB).symm

theorem mem_K_of_central {c : G} (hc : c ∈ M.GP)
    (hcomm : ∀ g ∈ M.GP, ∃ b ∈ M.B, c * g = g * c * b) : c ∈ M.K := by
  by_contra hK
  have h := M.conj_HC_of_not_mem_K (M.mem_H_of_central hc hcomm) hK (M.HB_le_HC M.t1el_mem_HB)
  have ht := M.comm_TB_of_central hc hcomm (Or.inl M.t1el_mem_HB)
  have e : c * M.t1el * c⁻¹ = M.t1el := by rw [ht, mul_inv_cancel_right]
  rw [e] at h
  exact M.nel_moves M.t1el_mem_S M.χ_t1el h

theorem isConj_z_mul_of_central {c : G} (hc : c ∈ M.GP)
    (hinv : c * M.bel * c⁻¹ = (M.bel : G)⁻¹) (hsq : c * c = 1)
    (hcomm : ∀ g ∈ M.GP, ∃ b ∈ M.B, c * g = g * c * b) : IsConj M.z (M.z * c) := by
  obtain ⟨hjH, hjK, hj2, -, -⟩ := M.jel_spec
  have hH := M.mem_H_of_central hc hcomm
  have hK := M.mem_K_of_central hc hcomm
  have hjc : c * M.jel = M.jel * c := M.comm_TB_of_central hc hcomm M.jel_mem_TB
  have hjcH : M.jel * c ∈ ruH M.T := mul_mem hjH hH
  have hjcK : M.jel * c ∉ M.K := fun h => hjK (by
    have := mul_mem h (inv_mem hK)
    rwa [mul_inv_cancel_right] at this)
  have hjc2 : (M.jel * c) ^ 2 = 1 := by
    have e : M.jel * c * (M.jel * c) = (M.jel * M.jel) * (c * c) := by
      calc M.jel * c * (M.jel * c) = M.jel * (c * M.jel) * c := by group
        _ = M.jel * (M.jel * c) * c := by rw [hjc]
        _ = (M.jel * M.jel) * (c * c) := by group
    rw [pow_two, e, M.jel_mul_self, hsq, one_mul]
  have h1 : IsConj M.z (M.jel * c) := M.lemma_J26.2.2.1 _ hjcH hjcK hjc2
  have hj1 : M.jel ≠ 1 := fun h => hjK (by rw [h]; exact one_mem _)
  obtain ⟨g, hg, hgz⟩ := M.lemma_J27_9 (M.TB_le_GB M.jel_mem_TB) hj2 hj1
  obtain ⟨b, hb, hbg⟩ := hcomm g (M.GB_le_GP hg)
  have hgc : g⁻¹ * c = c * b * g⁻¹ := by
    calc g⁻¹ * c = g⁻¹ * (c * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * c * b) * g⁻¹ := by rw [hbg]
      _ = c * b * g⁻¹ := by group
  have e2 : M.z * c * b = b * (M.z * c) * b⁻¹ := M.mul_eq_conj_of_inv (M.z_mul_inv hinv) hb
  have e1 : M.jel * c = (g * b) * (M.z * c) * (g * b)⁻¹ := by
    calc M.jel * c = g * M.z * (g⁻¹ * c) := by rw [← hgz]; group
      _ = g * (M.z * c * b) * g⁻¹ := by rw [hgc]; group
      _ = g * (b * (M.z * c) * b⁻¹) * g⁻¹ := by rw [e2]
      _ = (g * b) * (M.z * c) * (g * b)⁻¹ := by group
  exact h1.trans (isConj_iff.mpr ⟨g * b, e1.symm⟩).symm

theorem mk_eq_mk_iff_XP {a b : M.GP} :
    (QuotientGroup.mk a : M.XP) = QuotientGroup.mk b ↔ (a : G)⁻¹ * b ∈ M.B := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem inv_classes_of_central
    (c : M.GP) (hcR : (QuotientGroup.mk c : M.XP) ∉ M.ι.range)
    (hc2 : (QuotientGroup.mk c : M.XP) * QuotientGroup.mk c = 1)
    (hcc : ∀ y : M.XP, y * QuotientGroup.mk c = QuotientGroup.mk c * y) (y : M.GP)
    (hyR : (QuotientGroup.mk y : M.XP) ∉ M.ι.range) (hy2 : (y : G) * y = 1) :
    (c : G)⁻¹ * y ∈ M.B ∨ IsConj ((c : G) * M.z) y := by
  set cq : M.XP := QuotientGroup.mk c
  have hidx := M.index_range_ι
  have hw : cq * QuotientGroup.mk y ∈ M.ι.range :=
    (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hcR hyR)
  obtain ⟨v, hv⟩ := hw
  have hcinv : cq⁻¹ = cq := inv_eq_of_mul_eq_one_right hc2
  have hyy : (QuotientGroup.mk y : M.XP) * QuotientGroup.mk y = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : y * y = 1 := Subtype.ext hy2
    rw [this, QuotientGroup.mk_one]
  have hvv : v * v = 1 := by
    apply M.ι_injective
    rw [map_mul, hv, map_one]
    calc cq * QuotientGroup.mk y * (cq * QuotientGroup.mk y) =
        cq * (QuotientGroup.mk y * cq) * QuotientGroup.mk y := by group
      _ = cq * (cq * QuotientGroup.mk y) * QuotientGroup.mk y := by rw [hcc]
      _ = (cq * cq) * (QuotientGroup.mk y * QuotientGroup.mk y) := by group
      _ = 1 := by rw [hc2, hyy, one_mul]
  have hyv : (QuotientGroup.mk y : M.XP) = cq * M.ι v := by
    rw [hv, ← mul_assoc, hc2, one_mul]
  by_cases hv1 : v = 1
  · left
    rw [hv1, map_one, mul_one] at hyv
    exact M.mk_eq_mk_iff_XP.mp hyv.symm
  · right
    obtain ⟨x, hx2, rfl⟩ := M.exists_lift_sq (u := v) (by rw [pow_two]; exact hvv)
    have hx1 : (x : G) ≠ 1 := fun h => hv1 (by
      rw [show x = 1 from Subtype.ext h, QuotientGroup.mk_one])
    have hx2' : (x : G) ^ 2 = 1 := by
      have := congrArg Subtype.val hx2
      simpa using this
    obtain ⟨g, hg, hgz⟩ := M.lemma_J27_9 x.2 hx2' hx1
    set g' : M.GP := ⟨g, M.GB_le_GP hg⟩
    set z' : M.GP := ⟨M.z, M.GB_le_GP (M.TB_le_GB M.z_mem_TB)⟩
    have hincl : Subgroup.inclusion M.GB_le_GP x = g' * z' * g'⁻¹ := Subtype.ext (by
      rw [Subgroup.coe_inclusion, ← hgz]
      rfl)
    have hyq : (QuotientGroup.mk y : M.XP) = QuotientGroup.mk (g' * (c * z') * g'⁻¹) := by
      rw [hyv, M.ι_mk, hincl]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      calc cq * (QuotientGroup.mk g' * QuotientGroup.mk z' * (QuotientGroup.mk g')⁻¹) =
          (cq * QuotientGroup.mk g') * QuotientGroup.mk z' * (QuotientGroup.mk g')⁻¹ := by group
        _ = (QuotientGroup.mk g' * cq) * QuotientGroup.mk z' * (QuotientGroup.mk g')⁻¹ := by
          rw [hcc]
        _ = _ := by rw [show cq = QuotientGroup.mk c from rfl]; group
    have hb := M.mk_eq_mk_iff_XP.mp hyq.symm
    set b := ((g' * (c * z') * g'⁻¹ : M.GP) : G)⁻¹ * y with hbdef
    have hcz : ((c : G) * M.z) * M.bel * ((c : G) * M.z)⁻¹ = (M.bel : G)⁻¹ := by
      have hcinvB : (c : G) * M.bel * (c : G)⁻¹ = (M.bel : G)⁻¹ := by
        refine M.conj_bel_of_not_mem_GB c.2 fun h => hcR ?_
        exact (M.mk_mem_range_ι_iff c).mpr h
      have hbz : Commute (M.bel : G) M.z := M.bel_comm_z
      calc ((c : G) * M.z) * M.bel * ((c : G) * M.z)⁻¹ =
          c * (M.z * M.bel * M.z⁻¹) * (c : G)⁻¹ := by group
        _ = c * M.bel * (c : G)⁻¹ := by rw [← hbz.eq]; group
        _ = (M.bel : G)⁻¹ := hcinvB
    have hy' : ((g' * (c * z') * g'⁻¹ : M.GP) : G) = g * ((c : G) * M.z) * g⁻¹ := rfl
    have hconj : (g * ((c : G) * M.z) * g⁻¹) * M.bel * (g * ((c : G) * M.z) * g⁻¹)⁻¹ =
        (M.bel : G)⁻¹ := by
      have hgb : g⁻¹ * M.bel * g = M.bel := by
        have := (M.mem_GB_iff_conj.mp (inv_mem hg))
        rwa [inv_inv] at this
      calc (g * ((c : G) * M.z) * g⁻¹) * M.bel * (g * ((c : G) * M.z) * g⁻¹)⁻¹ =
          g * (((c : G) * M.z) * (g⁻¹ * M.bel * g) * ((c : G) * M.z)⁻¹) * g⁻¹ := by group
        _ = g * (M.bel : G)⁻¹ * g⁻¹ := by rw [hgb, hcz]
        _ = (g * M.bel * g⁻¹)⁻¹ := by group
        _ = (M.bel : G)⁻¹ := by rw [M.mem_GB_iff_conj.mp hg]
    have hyeq : (y : G) = (g * ((c : G) * M.z) * g⁻¹) * b := by rw [hbdef, hy']; group
    have e := M.mul_eq_conj_of_inv hconj hb
    rw [← hyeq] at e
    refine isConj_iff.mpr ⟨b * g, ?_⟩
    rw [e]
    group

theorem not_exists_central
    :
    ¬ ∃ c : M.XP, c ∉ M.ι.range ∧ c * c = 1 ∧ ∀ y : M.XP, y * c = c * y := by
  rintro ⟨c, hcR, hc2, hcc⟩
  obtain ⟨c1, rfl⟩ := QuotientGroup.mk_surjective c
  have hc0GB : (c1 : G) ∉ M.GB := fun h => hcR ((M.mk_mem_range_ι_iff c1).mpr h)
  have hinv := M.conj_bel_of_not_mem_GB c1.2 hc0GB
  have hsq : (c1 : G) * c1 = 1 := by
    refine M.sq_eq_one_of_inv hinv ?_
    have : (QuotientGroup.mk (c1 * c1) : M.XP) = 1 := by rw [QuotientGroup.mk_mul]; exact hc2
    rw [QuotientGroup.eq_one_iff] at this
    exact Subgroup.mem_subgroupOf.mp this
  have hcomm : ∀ g ∈ M.GP, ∃ b ∈ M.B, (c1 : G) * g = g * c1 * b := by
    intro g hg
    have h := hcc (QuotientGroup.mk ⟨g, hg⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, M.mk_eq_mk_iff_XP] at h
    refine ⟨_, h, ?_⟩
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group
  have hzc := M.isConj_z_mul_of_central c1.2 hinv hsq hcomm
  have hcz : (c1 : G) * M.z = M.z * c1 := M.comm_TB_of_central c1.2 hcomm M.z_mem_TB
  have hsH := M.S0_le_H M.s1el_mem_S0
  have hs2 : M.s1el ^ 2 = 1 := M.S0_elem.2 _ M.s1el_mem_S0
  have hsQ : M.s1el ∉ ruQ M.T := fun h => M.s1el_ne_one (M.eq_one_of_mem_S0_Q M.s1el_mem_S0 h)
  obtain ⟨h, hh, hs0⟩ := M.exists_conj_inv_bel hsH hs2 hsQ
  set s0 := h * M.s1el * h⁻¹ with hs0def
  have hs0GP : s0 ∈ M.GP := M.mem_GP_of_inv hs0
  have hs0GB : s0 ∉ M.GB := fun hm => M.bel_ne_inv (by rw [← hs0, M.mem_GB_iff_conj.mp hm])
  have hs0R : (QuotientGroup.mk (⟨s0, hs0GP⟩ : M.GP) : M.XP) ∉ M.ι.range :=
    fun hm => hs0GB ((M.mk_mem_range_ι_iff _).mp hm)
  have hs02 : s0 * s0 = 1 := by
    rw [hs0def]
    calc h * M.s1el * h⁻¹ * (h * M.s1el * h⁻¹) = h * (M.s1el * M.s1el) * h⁻¹ := by group
      _ = 1 := by rw [← pow_two, hs2]; group
  have hss : IsConj s0 M.s1el := isConj_iff.mpr ⟨h⁻¹, by rw [hs0def]; group⟩
  have hsz : ¬ IsConj M.z s0 := by
    intro hz
    obtain ⟨g, hg⟩ := isConj_iff.mp (hz.trans hss)
    exact M.lemma_J23_2 g (hg ▸ M.s1el_mem_S0)
  rcases M.inv_classes_of_central c1 hcR hc2 hcc ⟨s0, hs0GP⟩ hs0R hs02 with hb | hcj
  ·
    set b := (c1 : G)⁻¹ * s0 with hbdef
    have e := M.mul_eq_conj_of_inv hinv hb
    have hs0b : s0 = b * c1 * b⁻¹ := by
      rw [← e, hbdef]
      group
    have hbH : b ∈ ruH M.T := M.B_le_H hb
    set k := b⁻¹ * h with hkdef
    have hkH : k ∈ ruH M.T := mul_mem (inv_mem hbH) hh
    have hck : (c1 : G) = k * M.s1el * k⁻¹ := by
      rw [hkdef]
      calc (c1 : G) = b⁻¹ * (b * c1 * b⁻¹) * b := by group
        _ = b⁻¹ * s0 * b := by rw [← hs0b]
        _ = b⁻¹ * h * M.s1el * (b⁻¹ * h)⁻¹ := by rw [hs0def]; group
    have hRc : (c1 : G) * M.Rel = M.Rel * c1 := M.comm_TB_of_central c1.2 hcomm M.Rel_mem_TB
    set f := k⁻¹ * M.Rel * k with hfdef
    have hRH : M.Rel ∈ ruH M.T := (Subgroup.mem_inf.mp (M.TB_le_CHB M.Rel_mem_TB)).1
    have hfH : f ∈ ruH M.T := mul_mem (mul_mem (inv_mem hkH) hRH) hkH
    have hfs : f * M.s1el = M.s1el * f := by
      have hs : M.s1el = k⁻¹ * c1 * k := by rw [hck]; group
      rw [hs, hfdef]
      calc k⁻¹ * M.Rel * k * (k⁻¹ * c1 * k) = k⁻¹ * (M.Rel * c1) * k := by group
        _ = k⁻¹ * (c1 * M.Rel) * k := by rw [hRc]
        _ = k⁻¹ * c1 * k * (k⁻¹ * M.Rel * k) := by group
    have hf4 : f ^ 4 = M.z := by
      have hzk : M.z * k = k * M.z := M.mem_H_iff_comm.mp hkH
      have hf' : f = k⁻¹ * M.Rel * k⁻¹⁻¹ := by rw [hfdef, inv_inv]
      rw [hf', conj_pow, inv_inv, M.Rel_pow_four]
      calc k⁻¹ * M.z * k = k⁻¹ * (M.z * k) := by group
        _ = M.z := by rw [hzk]; group
    have := M.pow_four_of_comm_s1el hfH hfs
    rw [hf4] at this
    exact M.z_ne_one this
  ·
    apply hsz
    rw [hcz] at hcj
    exact hzc.trans hcj

theorem lemma_J27_3
    : Nonempty ((↥M.GP ⧸ M.B.subgroupOf M.GP) ≃* A6Models.autA6) := by
  obtain ⟨e⟩ := M.nonempty_NP_psl29
  rcases M.ρ_dichotomy e with hinj | hc
  · have hbij : Function.Bijective (M.ρ e) :=
      hinj.bijective_of_nat_card_le (by rw [M.card_XP, A6Facts.card_autA6])
    exact ⟨MulEquiv.ofBijective _ hbij⟩
  · obtain ⟨c, hcR, hc2, -, hcc⟩ := hc
    exact (M.not_exists_central ⟨c, hcR, hc2, hcc⟩).elim

end RuDataM

end CFSG.Quasithin.RuType
