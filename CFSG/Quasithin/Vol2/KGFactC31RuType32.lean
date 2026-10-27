module

public import CFSG.Quasithin.Vol2.KGFactC31RuHyp
public import CFSG.Sporadic.Schreier.RuIso
public import CFSG.Quasithin.Vol2.KGFactC31RuBigZ
public import CFSG.Quasithin.Vol2.KGFactC31RuRefK
public import CFSG.Sporadic.Schreier.RuPair

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Sporadic.RuSchreier
  CFSG.Quasithin.KGC31

variable {A : Type} [Group A]

section Facts


theorem ncard_u32_diff : ((u32 : Set (Equiv.Perm (Fin 4060))) \ {1}).ncard = 31 := by
  rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _), ← Nat.card_coe_set_eq]
  change Nat.card u32 - 1 = 31
  rw [card_refSub hv32]
  norm_num

theorem normalizer32_le :
    ruP ⊓ Subgroup.normalizer (u32 : Set (Equiv.Perm (Fin 4060))) ≤ ruC := by
  set H := ruP ⊓ Subgroup.normalizer (u32 : Set (Equiv.Perm (Fin 4060))) with hH
  intro g hg
  by_contra hgC
  have hCH : ruC ≤ H := le_inf ruC_le ruC_le_normalizer32
  have hgz : g * ruZ * g⁻¹ ≠ ruZ := by
    intro he
    apply hgC
    rw [ruC_eq_centralizer]
    refine ⟨hg.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc g * ruZ = g * ruZ * g⁻¹ * g := by group
      _ = ruZ * g := by rw [he]
  have hconj : ∀ h ∈ H, h * ruZ * h⁻¹ ∈ u32 := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp hh.2 ruZ).mp ruZ_mem_u32
  have hne1 : ∀ h : Equiv.Perm (Fin 4060), h * ruZ * h⁻¹ ≠ 1 := fun h h1 => ruZ_ne_one (by
    have : ruZ = h⁻¹ * (h * ruZ * h⁻¹) * h := by group
    rw [this, h1]
    group)
  obtain ⟨c₀, hc₀, hc₀e⟩ := exists_conj_r30 (hconj g hg) (hne1 g) hgz
  have hT : (u32 : Set (Equiv.Perm (Fin 4060))) \ {1} =
      {y | ∃ h ∈ H, h * ruZ * h⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨hy, hy1⟩
      have hy1' : y ≠ 1 := hy1
      by_cases hyz : y = ruZ
      · exact ⟨1, H.one_mem, by rw [hyz]; group⟩
      obtain ⟨c, hc, rfl⟩ := exists_conj_r30 hy hy1' hyz
      refine ⟨c * c₀⁻¹ * g, H.mul_mem (H.mul_mem (hCH hc) (H.inv_mem (hCH hc₀))) hg, ?_⟩
      have : c * c₀⁻¹ * g * ruZ * (c * c₀⁻¹ * g)⁻¹ = c * c₀⁻¹ * (g * ruZ * g⁻¹) * (c * c₀⁻¹)⁻¹ :=
        by group
      rw [this, ← hc₀e]
      group
    · rintro ⟨h, hh, rfl⟩
      exact ⟨hconj h hh, hne1 h⟩
  have hdvd := dvd_card_of_conj_eq H ruZ hT
  rw [ncard_u32_diff] at hdvd
  have h2 := hdvd.trans (Subgroup.card_dvd_of_le (inf_le_left : H ≤ ruP))
  rw [card_ruP'] at h2
  exact absurd h2 (by norm_num)

theorem ncard_u16_diff : ((u16 : Set (Equiv.Perm (Fin 4060))) \ {1}).ncard = 15 := by
  rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _), ← Nat.card_coe_set_eq]
  change Nat.card u16 - 1 = 15
  rw [card_refSub hv16]
  norm_num

theorem not_dvd_card_normalizer16 :
    ¬ 5 ^ 2 ∣ Nat.card ↥(ruP ⊓ Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060)))) := by
  set N₀ := ruP ⊓ Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060))) with hN₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((N₀ ⊓ Subgroup.centralizer {ruZ}).subgroupOf N₀)
  rw [card_subgroupOf_of_le inf_le_left] at h1
  have hq := card_quot_le_of_conj_mem N₀ ruZ (T := (u16 : Set (Equiv.Perm (Fin 4060))) \ {1})
    (Set.toFinite _) fun g hg => ⟨(Subgroup.mem_normalizer_iff.mp hg.2 ruZ).mp ruZ_mem_u16,
      fun h1 => ruZ_ne_one (by
        have : ruZ = g⁻¹ * (g * ruZ * g⁻¹) * g := by group
        rw [this, Set.mem_singleton_iff.mp h1]
        group)⟩
  rw [ncard_u16_diff] at hq
  have hqpos : 0 < Nat.card (↥N₀ ⧸ (N₀ ⊓ Subgroup.centralizer {ruZ}).subgroupOf N₀) :=
    Nat.card_pos
  have h2 : IsPGroup 2 ↥(N₀ ⊓ Subgroup.centralizer {ruZ}) := by
    intro g
    have hgC : (g : Equiv.Perm (Fin 4060)) ∈ ruC := by
      rw [ruC_eq_centralizer]
      exact ⟨g.2.1.1, g.2.2⟩
    exact ⟨10, Subtype.ext (by simpa using pow_normalizer16 hgC g.2.1.2)⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp h2
  rw [ha] at h1
  intro hdvd
  rw [h1] at hdvd
  have h3 : 5 ^ 2 ∣ Nat.card (↥N₀ ⧸ (N₀ ⊓ Subgroup.centralizer {ruZ}).subgroupOf N₀) :=
    (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime (5 ^ 2) 2)).dvd_of_dvd_mul_right hdvd
  have := Nat.le_of_dvd hqpos h3
  omega

theorem ruC_le_normalizerJ :
    ruC ≤ Subgroup.normalizer (ruJ : Set (Equiv.Perm (Fin 4060))) := by
  have hN := (Subgroup.normal_subgroupOf_iff ruJ_leC).1 ruJ_normal
  intro c hc
  exact mem_normalizer_of_conj_le fun j hj => hN j c hj hc

end Facts

section Config

variable [Finite A]

theorem false_u32_core {M₀ R M V : Subgroup A} (h : RuHyp M₀ R M V) (e : G₀ ≃* A)
    (hUV : img e u32 ≤ V) (hx : e ⟨x32, ruC_le x32_memC⟩ ∈ M₀) : False := by
  obtain ⟨hVO, hOR, hRC, hNRM⟩ := h.facts
  set V' := pb e V with hV'
  set M₀' := pb e M₀ with hM₀'
  have hVP : V' ≤ ruP := pb_le e V
  have hUV' : u32 ≤ V' := (le_iff_img_le e (refSub_le_ruP _)).mp hUV
  have hVab : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a := by
    intro a ha b hb
    obtain ⟨haP, haV⟩ := (mem_pb e).mp ha
    obtain ⟨hbP, hbV⟩ := (mem_pb e).mp hb
    have := h.V_comm _ haV _ hbV
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (e.injective this)
  have hVsq : ∀ a ∈ V', a * a = 1 := by
    intro a ha
    obtain ⟨haP, haV⟩ := (mem_pb e).mp ha
    have := h.V_sq _ haV
    rw [← map_mul, ← map_one e] at this
    exact congrArg Subtype.val (e.injective this)
  have hM₀N : M₀' ≤ Subgroup.normalizer (V' : Set (Equiv.Perm (Fin 4060))) :=
    pb_le_normalizer e h.M₀V
  have hxM : x32 ∈ M₀' := (apply_mem_iff_mem_pb e).mp hx
  have hV32 : V' ≤ u32 := by
    intro v hv
    refine mem_u32_of (hVP hv) (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      hVab u (hUV' hu) v hv) (hVsq v hv) fun j _ => ?_
    have hc : x32 ^ (j + 1) * v * (x32 ^ (j + 1))⁻¹ ∈ V' :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hM₀N hxM) _) v).mp hv
    exact hVab v hv _ hc
  have hVeq : pb e V = u32 := le_antisymm hV32 hUV'
  have hC2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A)) := by
    refine isPGroup_of_pb e ?_
    rw [pb_centralizer, hVeq]
    intro g
    exact ⟨7, Subtype.ext (by simpa using pow_centralizer32 g.2.1 g.2.2)⟩
  have hR : R = Subgroup.centralizer (V : Set A) := h.R_eq hC2
  have hNV : Subgroup.normalizer (V : Set A) ≤ Subgroup.normalizer (M₀ : Set A) := by
    refine le_trans ?_ hNRM
    rw [hR]
    exact normalizer_le_normalizer_centralizer V
  have hCV : img e ruC ≤ Subgroup.normalizer (V : Set A) := by
    rw [le_iff_img_le e ruC_le, pb_normalizer, hVeq]
    exact le_inf ruC_le ruC_le_normalizer32
  have hM₀C : M₀' ≤ ruC := fun m hm => normalizer32_le ⟨pb_le e M₀ hm, hVeq ▸ hM₀N hm⟩
  have hcN : cQ ∈ Subgroup.normalizer (M₀' : Set (Equiv.Perm (Fin 4060))) := by
    have h1 : img e ruC ≤ Subgroup.normalizer (M₀ : Set A) := hCV.trans hNV
    rw [le_iff_img_le e ruC_le, pb_normalizer] at h1
    exact (h1 cQ_memC).2
  have hcommM : x32 * cQ * x32⁻¹ * cQ⁻¹ ∈ M₀' := by
    have h1 : cQ * x32⁻¹ * cQ⁻¹ ∈ M₀' :=
      (Subgroup.mem_normalizer_iff.mp hcN _).mp (M₀'.inv_mem hxM)
    have : x32 * cQ * x32⁻¹ * cQ⁻¹ = x32 * (cQ * x32⁻¹ * cQ⁻¹) := by group
    rw [this]
    exact M₀'.mul_mem hxM h1
  have hcommJ : x32 * cQ * x32⁻¹ * cQ⁻¹ ∈ ruJ := by
    have h1 : x32 * cQ * x32⁻¹ ∈ ruJ :=
      (Subgroup.mem_normalizer_iff.mp (ruC_le_normalizerJ x32_memC) cQ).mp cQ_memJ
    exact ruJ.mul_mem h1 (ruJ.inv_mem cQ_memJ)
  have hJ2 : IsPGroup 2 ↥(img e ruJ) := by
    rw [img]
    exact (isPGroup_ruJ.of_equiv (Subgroup.subgroupOfEquivOfLe (ruJ_leC.trans ruC_le)).symm).map _
  have hM₀J : M₀ ≤ Subgroup.normalizer ((img e ruJ : Subgroup A) : Set A) := by
    rw [normalizer_img e (ruJ_leC.trans ruC_le), img_le_iff_le_pb]
    exact le_inf (pb_le e M₀) (hM₀C.trans ruC_le_normalizerJ)
  have hJO : M₀ ⊓ img e ruJ ≤ pCoreOf 2 M₀ :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun m hm => mem_normalizer_inf (Subgroup.le_normalizer hm) (hM₀J hm))
      (hJ2.to_le inf_le_right)
  have hmem : e ⟨_, pb_le e M₀ hcommM⟩ ∈ M₀ ⊓ img e ruJ :=
    ⟨(apply_mem_iff_mem_pb e).mpr hcommM, (apply_mem_img e).mpr hcommJ⟩
  have hC := hRC (hOR (hJO hmem))
  rw [apply_mem_iff_mem_pb e, pb_centralizer, hVeq] at hC
  exact commut_not_mem hC.2

theorem false_u32 {M₀ R M V : Subgroup A} (h : RuHyp M₀ R M V) (e : G₀ ≃* A)
    (hUV : img e u32 ≤ V) {y : G₀} (hyM : e y ∈ M₀)
    (hyN : (y : Equiv.Perm (Fin 4060)) ∈ Subgroup.normalizer (u32 : Set (Equiv.Perm (Fin 4060))))
    (hy : ∃ k : ℕ, y ^ 5 ^ k = 1) (hy1 : y ≠ 1) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hyC : (y : Equiv.Perm (Fin 4060)) ∈ ruC := normalizer32_le ⟨y.2, hyN⟩
  obtain ⟨n, hnC, hxM⟩ := exists_conj_std e ruC_le x32_memC orderOf_x32
    (by rw [card_ruC]; norm_num) hyC hy hy1 hyM
  have hnN : ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060)) ∈
      Subgroup.normalizer (u32 : Set (Equiv.Perm (Fin 4060))) :=
    ruC_le_normalizer32 (by simpa using ruC.inv_mem hnC)
  have e1 : u32.map (MulAut.conj ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060))).toMonoidHom = u32 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN
  exact false_u32_core h (conjE e n⁻¹) (by rw [img_conjE, e1]; exact hUV) hxM

theorem false_u16_core {M₀ R M V : Subgroup A} (h : RuHyp M₀ R M V) (e : G₀ ≃* A)
    (hUV : img e u16 ≤ V) (hx : e ⟨x16, wG_mem _⟩ ∈ M₀) : False := by
  obtain ⟨hVO, hOR, hRC, hNRM⟩ := h.facts
  set V' := pb e V with hV'
  set M₀' := pb e M₀ with hM₀'
  have hVP : V' ≤ ruP := pb_le e V
  have hUV' : u16 ≤ V' := (le_iff_img_le e (refSub_le_ruP _)).mp hUV
  have hVab : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a := by
    intro a ha b hb
    obtain ⟨haP, haV⟩ := (mem_pb e).mp ha
    obtain ⟨hbP, hbV⟩ := (mem_pb e).mp hb
    have := h.V_comm _ haV _ hbV
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (e.injective this)
  have hVsq : ∀ a ∈ V', a * a = 1 := by
    intro a ha
    obtain ⟨haP, haV⟩ := (mem_pb e).mp ha
    have := h.V_sq _ haV
    rw [← map_mul, ← map_one e] at this
    exact congrArg Subtype.val (e.injective this)
  have hM₀N : M₀' ≤ Subgroup.normalizer (V' : Set (Equiv.Perm (Fin 4060))) :=
    pb_le_normalizer e h.M₀V
  have hxM : x16 ∈ M₀' := (apply_mem_iff_mem_pb e).mp hx
  have hVp : V' ≤ uV32p := by
    intro v hv
    refine mem_V32p_of (hVP hv) (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      hVab u (hUV' hu) v hv) (hVsq v hv) fun j _ => ?_
    have hc : x16 ^ (j + 1) * v * (x16 ^ (j + 1))⁻¹ ∈ V' :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hM₀N hxM) _) v).mp hv
    exact hVab v hv _ hc
  have hC2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A)) := by
    refine isPGroup_of_pb e ?_
    rw [pb_centralizer]
    intro g
    exact ⟨7, Subtype.ext (by
      simpa using pow_centralizer16 g.2.1 (Subgroup.centralizer_le hUV' g.2.2))⟩
  have hR : R = Subgroup.centralizer (V : Set A) := h.R_eq hC2
  by_cases hVe : V' = u16
  · have hVe' : pb e V = u16 := hVe
    have hg : g16 ∈ Subgroup.normalizer
        ((ruP ⊓ Subgroup.centralizer (u16 : Set (Equiv.Perm (Fin 4060))) : Subgroup _) :
          Set (Equiv.Perm (Fin 4060))) :=
      mem_normalizer_of_conj_le fun c hc => ⟨ruP.mul_mem (ruP.mul_mem (wG_mem _) hc.1)
        (ruP.inv_mem (wG_mem _)), conj_g16_centralizer16 hc.1 hc.2⟩
    have hgR : e ⟨g16, wG_mem _⟩ ∈ Subgroup.normalizer (R : Set A) := by
      rw [hR, ← img_pb e (Subgroup.centralizer (V : Set A)), normalizer_img e (pb_le e _),
        pb_centralizer, hVe', apply_mem_img]
      exact ⟨wG_mem _, hg⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hNRM hgR) _).mp hx
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    have h2 := hM₀N ((apply_mem_iff_mem_pb e).mp h1)
    rw [hVe] at h2
    exact conj_x16_not_mem_normalizer (by simpa using h2)
  ·
    have hVeq : V' = uV32p := by
      have hd := Subgroup.card_dvd_of_le hVp
      rw [card_refSub hvV32p] at hd
      have hge : Nat.card u16 ≤ Nat.card V' := Subgroup.card_le_of_le hUV'
      rw [card_refSub hv16] at hge
      have hne : Nat.card V' ≠ 2 ^ 4 := fun hc => hVe
        (le_antisymm (by
          have := Subgroup.eq_of_le_of_card_ge hUV' (by rw [hc, card_refSub hv16])
          exact this.symm.le) hUV')
      have h32 : Nat.card V' = 2 ^ 5 := by
        obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
        rw [hk'] at hge hne ⊢
        have : k ≤ 5 := hk
        have : 4 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hge
        interval_cases k
        · exact absurd rfl hne
        · rfl
      exact Subgroup.eq_of_le_of_card_ge hVp (by rw [h32, card_refSub hvV32p])
    have hVeq' : pb e V = uV32p := hVeq
    set e' := conjE e ⟨k16, wG_mem _⟩ with he'
    have hUV2 : img e' u32 ≤ V := by
      rw [img_conjE]
      show img e (u32.map (MulAut.conj k16).toMonoidHom) ≤ V
      rw [map_k16_u32, ← hVeq', img_pb]
    have hyP : k16⁻¹ * x16 * k16 ∈ ruP :=
      ruP.mul_mem (ruP.mul_mem (ruP.inv_mem (wG_mem _)) (wG_mem _)) (wG_mem _)
    have hyM : e' ⟨_, hyP⟩ ∈ M₀ := by
      rw [conjE_apply]
      convert hx using 2
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hyN : k16⁻¹ * x16 * k16 ∈ Subgroup.normalizer (u32 : Set (Equiv.Perm (Fin 4060))) :=
      conj_mem_normalizer_of_map map_k16_u32 (hVeq ▸ hM₀N hxM)
    have hy5 : (⟨_, hyP⟩ : G₀) ^ 5 ^ 1 = 1 := by
      apply Subtype.ext
      simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      rw [show (k16⁻¹ * x16 * k16) ^ 5 = k16⁻¹ * x16 ^ 5 * k16 by
        rw [show k16⁻¹ * x16 * k16 = k16⁻¹ * x16 * k16⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv],
        ← orderOf_x16, pow_orderOf_eq_one]
      group
    have hy1 : (⟨_, hyP⟩ : G₀) ≠ 1 := by
      intro h1
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_one] at h2
      have : x16 = 1 := by
        have : x16 = k16 * (k16⁻¹ * x16 * k16) * k16⁻¹ := by group
        rw [this, h2]
        group
      have h3 := orderOf_x16
      rw [this, orderOf_one] at h3
      exact absurd h3 (by norm_num)
    exact false_u32 h e' hUV2 hyM hyN ⟨1, hy5⟩ hy1

theorem false_u16 {M₀ R M V : Subgroup A} (h : RuHyp M₀ R M V) (e : G₀ ≃* A)
    (hUV : img e u16 ≤ V) {y : G₀} (hyM : e y ∈ M₀)
    (hyN : (y : Equiv.Perm (Fin 4060)) ∈ Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060))))
    (hy : ∃ k : ℕ, y ^ 5 ^ k = 1) (hy1 : y ≠ 1) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨n, hnN, hxM⟩ := exists_conj_std e inf_le_left ⟨wG_mem _, x16_mem_normalizer⟩
    orderOf_x16 not_dvd_card_normalizer16 ⟨y.2, hyN⟩ hy hy1 hyM
  have hnN' : ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060)) ∈
      Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060))) := by
    have := (ruP ⊓ Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060)))).inv_mem hnN
    simpa using this.2
  have e1 : u16.map (MulAut.conj ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060))).toMonoidHom = u16 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN'
  exact false_u16_core h (conjE e n⁻¹) (by rw [img_conjE, e1]; exact hUV) hxM

end Config

end CFSG.Quasithin.KGC31.Ru

end
