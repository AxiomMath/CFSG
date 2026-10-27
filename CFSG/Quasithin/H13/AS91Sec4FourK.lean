module

public import CFSG.Quasithin.H13.AS91Sec4Three
public import CFSG.GF2Type.Aschbacher1976Full.HSGL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour

variable {G : Type} [Group G] [Finite G]

theorem QG_le_normalizer (T : Setting G) {Y : Subgroup G} (hY : Y ≤ T.QG) (hz : T.z ∈ Y) :
    T.QG ≤ normalizer (Y : Set G) := by
  intro q hq
  refine mem_normalizer_fintype fun y hy => ?_
  rcases T.commutator_eq_one_or_z hq (hY hy) with h1 | h1
  · have e : q * y * q⁻¹ = y := by
      calc q * y * q⁻¹ = (q * y * q⁻¹ * y⁻¹) * y := by group
        _ = y := by rw [h1, one_mul]
    rw [e]
    exact hy
  · have e : q * y * q⁻¹ = T.z * y := by
      calc q * y * q⁻¹ = (q * y * q⁻¹ * y⁻¹) * y := by group
        _ = T.z * y := by rw [h1]
    rw [e]
    exact mul_mem hz hy

theorem facts_of_theta {Zs K : Subgroup G}
    (θ : ↥(normalizer (Zs : Set G)) →* GL (Fin 3) (ZMod 2)) (hθs : Function.Surjective θ)
    (hθk : θ.ker = (centralizer (Zs : Set G)).subgroupOf (normalizer (Zs : Set G)))
    (hKN : K ≤ normalizer (Zs : Set G))
    (hKn : ∀ n ∈ normalizer (Zs : Set G), ∀ k ∈ K, n * k * n⁻¹ ∈ K)
    (hne : ∃ u ∈ K, u ∉ centralizer (Zs : Set G)) :
    normalizer (Zs : Set G) = K ⊔ centralizer (Zs : Set G) ∧
      ∃ φ : ↥K →* GL (Fin 3) (ZMod 2), Function.Surjective φ ∧
        φ.ker = (K ⊓ centralizer (Zs : Set G)).subgroupOf K := by
  have hK'n : (K.subgroupOf (normalizer (Zs : Set G))).Normal :=
    ⟨fun k hk n => hKn n n.2 k (mem_subgroupOf.mp hk)⟩
  have hmem : ∀ x : ↥(normalizer (Zs : Set G)), θ x = 1 ↔ (x : G) ∈ centralizer (Zs : Set G) :=
    fun x => by rw [← MonoidHom.mem_ker, hθk, mem_subgroupOf]
  have htop : (K.subgroupOf (normalizer (Zs : Set G))).map θ = ⊤ := by
    haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
    haveI := hK'n.map θ hθs
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left fun hbot => ?_
    obtain ⟨u, huK, huC⟩ := hne
    apply huC
    refine (hmem ⟨u, hKN huK⟩).mp ?_
    have : θ ⟨u, hKN huK⟩ ∈ (K.subgroupOf (normalizer (Zs : Set G))).map θ :=
      ⟨_, mem_subgroupOf.mpr huK, rfl⟩
    rw [hbot] at this
    exact this
  have hsurj : ∀ y, ∃ k : ↥(normalizer (Zs : Set G)), (k : G) ∈ K ∧ θ k = y := fun y => by
    have : y ∈ (K.subgroupOf (normalizer (Zs : Set G))).map θ := by rw [htop]; exact mem_top y
    obtain ⟨k, hk, rfl⟩ := this
    exact ⟨k, hk, rfl⟩
  refine ⟨le_antisymm (fun n hn => ?_) (sup_le hKN (centralizer_le_normalizer _)), ?_⟩
  · obtain ⟨k, hk, hkn⟩ := hsurj (θ ⟨n, hn⟩)
    have hc : ((k⁻¹ * ⟨n, hn⟩ : ↥(normalizer (Zs : Set G))) : G) ∈ centralizer (Zs : Set G) :=
      (hmem _).mp (by rw [map_mul, map_inv, hkn, inv_mul_cancel])
    have e : n = (k : G) * ((k⁻¹ * ⟨n, hn⟩ : ↥(normalizer (Zs : Set G))) : G) := by simp
    rw [e]
    exact mul_mem_sup hk hc
  · refine ⟨θ.comp (Subgroup.inclusion hKN), fun y => ?_, ?_⟩
    · obtain ⟨k, hk, rfl⟩ := hsurj y
      exact ⟨⟨k, hk⟩, rfl⟩
    · ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hmem, mem_subgroupOf, mem_inf]
      exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩

namespace Data41

variable {z : G} {h : HypJ4 G z}

@[expose] noncomputable def K0 (g₁ : G) (s₀ : h.setting.M) : Subgroup G :=
  h.setting.QG ⊔ h.setting.Qa g₁ ⊔ h.setting.Qa ((s₀ : G) * g₁)

@[expose] noncomputable def Kgrp (g₁ : G) (s₀ : h.setting.M) : Subgroup G :=
  ⨆ (g : G) (_ : g * z * g⁻¹ ∈ Zinf (h := h) g₁ s₀), (Q z).map (MulAut.conj g).toMonoidHom

theorem Zinf_le_QG (g₁ : G) (s₀ : h.setting.M) : Zinf (h := h) g₁ s₀ ≤ h.setting.QG := by
  rw [Zinf_eq]
  exact inf_le_left.trans inf_le_left

theorem Zinf_le_Qa₁ (g₁ : G) (s₀ : h.setting.M) : Zinf (h := h) g₁ s₀ ≤ h.setting.Qa g₁ := by
  rw [Zinf_eq]
  exact inf_le_left.trans inf_le_right

theorem Zinf_le_Qa₂ (g₁ : G) (s₀ : h.setting.M) :
    Zinf (h := h) g₁ s₀ ≤ h.setting.Qa ((s₀ : G) * g₁) := by
  rw [Zinf_eq]
  exact inf_le_right

theorem QG_le_K0 (g₁ : G) (s₀ : h.setting.M) : h.setting.QG ≤ K0 (h := h) g₁ s₀ :=
  le_sup_left.trans le_sup_left

theorem Qa₁_le_K0 (g₁ : G) (s₀ : h.setting.M) : h.setting.Qa g₁ ≤ K0 (h := h) g₁ s₀ :=
  le_sup_right.trans le_sup_left

theorem Qa₂_le_K0 (g₁ : G) (s₀ : h.setting.M) :
    h.setting.Qa ((s₀ : G) * g₁) ≤ K0 (h := h) g₁ s₀ :=
  le_sup_right

theorem conjBy_z₂ (g₁ : G) (s₀ : h.setting.M) :
    (h.setting.conjBy ((s₀ : G) * g₁)).z = (s₀ : G) * (g₁ * z * g₁⁻¹) * (s₀ : G)⁻¹ := by
  rw [Setting.conjBy_z, h.setting_z]
  group

variable (D : Data41 h)

section Four

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3)
  {s₀ : h.setting.M} (hs₀ : D.Φo (h.setting.ρ s₀) = Two.tE)

include hOut hTw hg₁ hs₀

theorem z_mem_Zinf' : h.setting.z ∈ Zinf (h := h) g₁ s₀ := D.z_mem_Zinf hOut hTw hg₁ hs₀

theorem conjBy₁_z_mem : (h.setting.conjBy g₁).z ∈ Zinf (h := h) g₁ s₀ := by
  rw [Setting.conjBy_z, h.setting_z, hg₁]
  exact D.rep3_mem_Zinf hOut hTw hg₁ hs₀

theorem conjBy₂_z_mem : (h.setting.conjBy ((s₀ : G) * g₁)).z ∈ Zinf (h := h) g₁ s₀ := by
  rw [conjBy_z₂, hg₁]
  exact D.conj_rep3_mem_Zinf hOut hTw hg₁ hs₀

theorem K0_le_normalizer : K0 (h := h) g₁ s₀ ≤ normalizer (Zinf (h := h) g₁ s₀ : Set G) :=
  sup_le (sup_le (QG_le_normalizer h.setting (Zinf_le_QG g₁ s₀) (D.z_mem_Zinf' hOut hTw hg₁ hs₀))
    (QG_le_normalizer (h.setting.conjBy g₁) (Zinf_le_Qa₁ g₁ s₀)
      (D.conjBy₁_z_mem hOut hTw hg₁ hs₀)))
    (QG_le_normalizer (h.setting.conjBy ((s₀ : G) * g₁)) (Zinf_le_Qa₂ g₁ s₀)
      (D.conjBy₂_z_mem hOut hTw hg₁ hs₀))

theorem exists_conj_eq_of_mem {x : G} (hx : x ∈ Zinf (h := h) g₁ s₀) (hx1 : x ≠ 1) :
    ∃ n ∈ K0 (h := h) g₁ s₀, n * z * n⁻¹ = x := by
  let S := h.setting
  let Zs := Zinf (h := h) g₁ s₀
  let r₁ := D.rep 3
  let r₂ := (s₀ : G) * D.rep 3 * (s₀ : G)⁻¹
  have hzZ : z ∈ Zs := D.z_mem_Zinf hOut hTw hg₁ hs₀
  have hr₁Z : r₁ ∈ Zs := D.rep3_mem_Zinf hOut hTw hg₁ hs₀
  have hr₂Z : r₂ ∈ Zs := D.conj_rep3_mem_Zinf hOut hTw hg₁ hs₀
  have hZQ : Zs ≤ S.QG := Zinf_le_QG g₁ s₀
  have hT1z : (S.conjBy g₁).z = r₁ := by rw [Setting.conjBy_z, h.setting_z, hg₁]
  have hT2z : (S.conjBy ((s₀ : G) * g₁)).z = r₂ := by rw [conjBy_z₂, hg₁]
  let O : Set G := {y | ∃ n ∈ K0 (h := h) g₁ s₀, n * z * n⁻¹ = y}
  have step : ∀ T : Setting G, T.QG ≤ K0 (h := h) g₁ s₀ → Zs ≤ T.QG → ∀ y ∈ O, y ∈ Zs →
      y ≠ 1 → y ≠ T.z → y * T.z ∈ O := by
    rintro T hT hZT y ⟨n, hn, rfl⟩ hy hy1 hyz
    obtain ⟨u, hu, hu'⟩ := T.exists_conj_eq_mul_z (hZT hy) hy1 hyz
    exact ⟨u * n, mul_mem (hT hu) hn, by rw [← hu']; group⟩
  have hO0 : z ∈ O := ⟨1, one_mem _, by group⟩
  have hcz : D.ψV (S.cl z) = 0 := by rw [show S.cl z = 0 from S.cl_z, map_zero]
  have hc₁ : D.ψV (S.cl r₁) = vecOf 3 := D.ψV_cl_rep 3
  have hc₂ : D.ψV (S.cl r₂) = vecOf 192 := D.ψV_cl_conj_rep3 hOut hTw hg₁ hs₀
  have hne : ∀ {a b : G}, D.ψV (S.cl a) ≠ D.ψV (S.cl b) → a ≠ b := fun hab e => hab (by rw [e])
  have hne1 : ∀ {a : G}, a ∈ S.QG → D.ψV (S.cl a) ≠ 0 → a ≠ 1 ∧ a ≠ S.z := fun ha hc =>
    ⟨fun e => hc (by rw [e, S.cl_one, map_zero]),
      fun e => hc (by rw [e, show S.cl S.z = 0 from S.cl_z, map_zero])⟩
  have h3 : vecOf 3 ≠ 0 := vecOf_three_ne
  have h192 : vecOf 192 ≠ 0 := fun h0 =>
    absurd (vecOf_inj (by norm_num) (by norm_num) (h0.trans vecOf_zero.symm)) (by norm_num)
  have h195 : vecOf 195 ≠ 0 := fun h0 =>
    absurd (vecOf_inj (by norm_num) (by norm_num) (h0.trans vecOf_zero.symm)) (by norm_num)
  have h3192 : vecOf 3 ≠ vecOf 192 := fun e =>
    absurd (vecOf_inj (by norm_num) (by norm_num) e) (by norm_num)
  have hy₁ : z * r₁ ∈ O := by
    have := step (S.conjBy g₁) (Qa₁_le_K0 g₁ s₀) (Zinf_le_Qa₁ g₁ s₀) z hO0 hzZ S.z_ne_one
      (by rw [hT1z]; exact (D.rep_props vecOf_three_ne q0_three).2.2.symm)
    rwa [hT1z] at this
  have hy₂ : z * r₂ ∈ O := by
    have := step (S.conjBy ((s₀ : G) * g₁)) (Qa₂_le_K0 g₁ s₀) (Zinf_le_Qa₂ g₁ s₀) z hO0 hzZ
      S.z_ne_one (by rw [hT2z]; exact (hne (by rw [hcz, hc₂]; exact h192.symm)))
    rwa [hT2z] at this
  have hcy₁ : D.ψV (S.cl (z * r₁)) = vecOf 3 := by
    rw [S.cl_mul (hZQ hzZ) (hZQ hr₁Z), map_add, hcz, hc₁, zero_add]
  have hcy₂ : D.ψV (S.cl (z * r₂)) = vecOf 192 := by
    rw [S.cl_mul (hZQ hzZ) (hZQ hr₂Z), map_add, hcz, hc₂, zero_add]
  have hy₃ : z * r₁ * r₂ ∈ O := by
    have hZ1 : z * r₁ ∈ Zs := mul_mem hzZ hr₁Z
    have := step (S.conjBy ((s₀ : G) * g₁)) (Qa₂_le_K0 g₁ s₀) (Zinf_le_Qa₂ g₁ s₀) (z * r₁) hy₁
      hZ1 (hne1 (hZQ hZ1) (by rw [hcy₁]; exact h3)).1
      (by rw [hT2z]; exact hne (by rw [hcy₁, hc₂]; exact h3192))
    rwa [hT2z] at this
  have hcy₃ : D.ψV (S.cl (z * r₁ * r₂)) = vecOf 195 := by
    rw [S.cl_mul (hZQ (mul_mem hzZ hr₁Z)) (hZQ hr₂Z), map_add, hcy₁, hc₂, ← vecOf_xor,
      show (3 : ℕ) ^^^ 192 = 195 by decide]
  have hfin : ∀ y ∈ O, y ∈ Zs → D.ψV (S.cl y) ≠ 0 → ∀ x ∈ Zs, D.ψV (S.cl x) = D.ψV (S.cl y) →
      x ∈ O := by
    intro y hyO hyZ hy0 x hxZ hxy
    rcases (S.cl_eq_cl_iff (hZQ hyZ) (hZQ hxZ)).mp (D.ψV.injective hxy.symm) with rfl | rfl
    · exact hyO
    · obtain ⟨hy1, hyz⟩ := hne1 (hZQ hyZ) hy0
      exact step S (QG_le_K0 g₁ s₀) hZQ y hyO hyZ hy1 hyz
  obtain ⟨hxQ, hxZ'⟩ := (D.mem_Zinf_iff hOut hTw hg₁ hs₀).mp hx
  rcases (Two.inZ_iff _).mp hxZ' with h0 | hx3 | hx192 | hx195
  · rcases (S.cl_eq_zero_iff hxQ).mp (D.ψV.injective (by rw [h0, map_zero])) with e | e
    · exact absurd e hx1
    · exact e ▸ hO0
  · exact hfin _ hy₁ (mul_mem hzZ hr₁Z) (by rw [hcy₁]; exact h3) x hx (by rw [hx3, hcy₁])
  · exact hfin _ hy₂ (mul_mem hzZ hr₂Z) (by rw [hcy₂]; exact h192) x hx (by rw [hx192, hcy₂])
  · exact hfin _ hy₃ (mul_mem (mul_mem hzZ hr₁Z) hr₂Z) (by rw [hcy₃]; exact h195) x hx
      (by rw [hx195, hcy₃])

theorem conj_ne_one_of_mem {g : G} : g * z * g⁻¹ ≠ 1 := fun e => h.setting.z_ne_one (by
  have hz : z = g⁻¹ * (g * z * g⁻¹) * g := by group
  rw [h.setting_z, hz, e]
  group)

theorem exists_Qa_eq {g : G} (hg : g * z * g⁻¹ ∈ Zinf (h := h) g₁ s₀) :
    ∃ n ∈ K0 (h := h) g₁ s₀, h.setting.Qa g = h.setting.Qa n := by
  obtain ⟨n, hn, hnz⟩ := D.exists_conj_eq_of_mem hOut hTw hg₁ hs₀ hg
    (D.conj_ne_one_of_mem hOut hTw hg₁ hs₀)
  exact ⟨n, hn, h.setting.Qa_eq_of_conj_eq (by rw [h.setting_z]; exact hnz.symm)⟩

theorem Kgrp_eq_K0 : Kgrp (h := h) g₁ s₀ = K0 (h := h) g₁ s₀ := by
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    obtain ⟨n, hn, he⟩ := D.exists_Qa_eq hOut hTw hg₁ hs₀ hg
    rw [← h.setting_QG, ← Setting.Qa_eq_map, he, Setting.Qa_eq_map]
    rintro _ ⟨q, hq, rfl⟩
    show n * q * n⁻¹ ∈ _
    exact mul_mem (mul_mem hn (QG_le_K0 g₁ s₀ hq)) (inv_mem hn)
  · have hgen : ∀ g : G, g * z * g⁻¹ ∈ Zinf (h := h) g₁ s₀ →
        h.setting.Qa g ≤ Kgrp (h := h) g₁ s₀ := by
      intro g hg
      rw [Setting.Qa_eq_map, h.setting_QG]
      exact le_iSup₂ (f := fun g (_ : g * z * g⁻¹ ∈ Zinf (h := h) g₁ s₀) =>
        (Q z).map (MulAut.conj g).toMonoidHom) g hg
    refine sup_le (sup_le ?_ (hgen g₁ ?_)) (hgen _ ?_)
    · have := hgen 1 (by simpa using D.z_mem_Zinf hOut hTw hg₁ hs₀)
      rwa [Setting.Qa_one] at this
    · rw [hg₁]
      exact D.rep3_mem_Zinf hOut hTw hg₁ hs₀
    · have := D.conjBy₂_z_mem hOut hTw hg₁ hs₀
      rwa [Setting.conjBy_z, h.setting_z] at this

theorem Kgrp_le_normalizer : Kgrp (h := h) g₁ s₀ ≤ normalizer (Zinf (h := h) g₁ s₀ : Set G) := by
  rw [D.Kgrp_eq_K0 hOut hTw hg₁ hs₀]
  exact D.K0_le_normalizer hOut hTw hg₁ hs₀

omit hOut hTw hg₁ hs₀ in
theorem conj_mem_Kgrp {n : G} (hn : n ∈ normalizer (Zinf (h := h) g₁ s₀ : Set G)) {k : G}
    (hk : k ∈ Kgrp (h := h) g₁ s₀) : n * k * n⁻¹ ∈ Kgrp (h := h) g₁ s₀ := by
  have hle : Kgrp (h := h) g₁ s₀ ≤ (Kgrp (h := h) g₁ s₀).comap (MulAut.conj n).toMonoidHom := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨q, hq, rfl⟩
    have hng : (n * g) * z * (n * g)⁻¹ ∈ Zinf (h := h) g₁ s₀ := by
      have := (mem_normalizer_iff.mp hn (g * z * g⁻¹)).mp hg
      rwa [show n * (g * z * g⁻¹) * n⁻¹ = (n * g) * z * (n * g)⁻¹ by group] at this
    have hmem : (MulAut.conj (n * g)).toMonoidHom q ∈ Kgrp (h := h) g₁ s₀ :=
      le_iSup₂ (f := fun g (_ : g * z * g⁻¹ ∈ Zinf (h := h) g₁ s₀) =>
        (Q z).map (MulAut.conj g).toMonoidHom) (n * g) hng ⟨q, hq, rfl⟩
    rw [Subgroup.mem_comap]
    show n * (g * q * g⁻¹) * n⁻¹ ∈ Kgrp (h := h) g₁ s₀
    have e : n * (g * q * g⁻¹) * n⁻¹ = (n * g) * q * (n * g)⁻¹ := by group
    rw [e]
    exact hmem
  exact hle hk

theorem isElemAbelian_Zinf : IsElemAbelian 2 (Zinf (h := h) g₁ s₀) := by
  have hsq : ∀ x ∈ Zinf (h := h) g₁ s₀, x * x = 1 := fun x hx => D.Zinf_sq hOut hTw hg₁ hs₀ hx
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => by rw [pow_two]; exact hsq x hx⟩
  have hab := hsq _ (mul_mem a.2 b.2)
  have ha := hsq _ a.2
  have hb := hsq _ b.2
  show (a : G) * b = b * a
  calc (a : G) * b = (a : G) * b * (b * a) * (b * a) := by
        rw [mul_assoc ((a : G) * b), hsq _ (mul_mem b.2 a.2), mul_one]
    _ = (b : G) * a := by
        rw [show (a : G) * b * (b * a) * (b * a) = a * (b * b) * a * (b * a) by group, hb,
          mul_one, ha, one_mul]

theorem fourteen_dvd : 14 ∣ Nat.card (Zinf (h := h) g₁ s₀).normalizerMonoidHom.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzZ : z ∈ Zinf (h := h) g₁ s₀ := D.z_mem_Zinf hOut hTw hg₁ hs₀
  have hNK := D.K0_le_normalizer hOut hTw hg₁ hs₀
  have h7 : 7 ∣ Nat.card (Zinf (h := h) g₁ s₀).normalizerMonoidHom.range := by
    have horb : MulAction.orbit ↥(Zinf (h := h) g₁ s₀).normalizerMonoidHom.range
        (⟨z, hzZ⟩ : ↥(Zinf (h := h) g₁ s₀)) = {a | a ≠ 1} := by
      ext a
      constructor
      · rintro ⟨f, rfl⟩ h1
        have h1' : ((f : MulAut ↥(Zinf (h := h) g₁ s₀)) ⟨z, hzZ⟩) = 1 := h1
        rw [MulEquiv.map_eq_one_iff] at h1'
        exact h.setting.z_ne_one (congrArg Subtype.val h1')
      · intro ha
        obtain ⟨n, hn, hnz⟩ := D.exists_conj_eq_of_mem hOut hTw hg₁ hs₀ a.2
          (fun h1 => ha (Subtype.ext h1))
        exact ⟨⟨_, ⟨⟨n, hNK hn⟩, rfl⟩⟩, Subtype.ext hnz⟩
    have h1 := MulAction.index_stabilizer ↥(Zinf (h := h) g₁ s₀).normalizerMonoidHom.range
      (⟨z, hzZ⟩ : ↥(Zinf (h := h) g₁ s₀))
    have e : ({a | a ≠ 1} : Set ↥(Zinf (h := h) g₁ s₀)) = Set.univ \ {1} := by
      ext a
      simp
    rw [horb, e, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
      D.card_Zinf hOut hTw hg₁ hs₀] at h1
    rw [show 7 = 8 - 1 from rfl, ← h1]
    exact Subgroup.index_dvd_card _
  have h2 : 2 ∣ Nat.card (Zinf (h := h) g₁ s₀).normalizerMonoidHom.range := by
    have hr₁Z := D.rep3_mem_Zinf hOut hTw hg₁ hs₀
    obtain ⟨-, h31, h3z⟩ := D.rep_props vecOf_three_ne q0_three
    obtain ⟨u, hu, hur⟩ := h.setting.exists_conj_eq_mul_z (Zinf_le_QG g₁ s₀ hr₁Z) h31 h3z
    set f := (Zinf (h := h) g₁ s₀).normalizerMonoidHom ⟨u, hNK (QG_le_K0 g₁ s₀ hu)⟩ with hf
    have hfa : ∀ a : ↥(Zinf (h := h) g₁ s₀), ((f a : ↥(Zinf (h := h) g₁ s₀)) : G) = u * a * u⁻¹ :=
      fun a => rfl
    have hf1 : f ≠ 1 := by
      intro e
      have := hfa ⟨D.rep 3, hr₁Z⟩
      rw [e] at this
      change D.rep 3 = u * D.rep 3 * u⁻¹ at this
      rw [hur] at this
      exact h.setting.z_ne_one (by simpa using this.symm)
    have hf2 : f ^ 2 = 1 := by
      ext a
      rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
      change u * (u * (a : G) * u⁻¹) * u⁻¹ = a
      have hzc := h.setting.z_comm_QG (Zinf_le_QG g₁ s₀ a.2)
      rcases h.setting.sq_eq_one_or_z hu with hsq | hsq
      · rw [show u * (u * (a : G) * u⁻¹) * u⁻¹ = (u * u) * a * (u * u)⁻¹ by group, ← pow_two,
          hsq]
        group
      · rw [show u * (u * (a : G) * u⁻¹) * u⁻¹ = (u * u) * a * (u * u)⁻¹ by group, ← pow_two,
          hsq, ← hzc, mul_inv_cancel_right]
    have hord : orderOf (⟨f, ⟨_, rfl⟩⟩ : ↥(Zinf (h := h) g₁ s₀).normalizerMonoidHom.range) = 2 :=
      orderOf_eq_prime (Subtype.ext hf2) (fun e => hf1 (congrArg Subtype.val e))
    rw [← hord]
    exact orderOf_dvd_natCard _
  exact (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 7) h2 h7)

theorem exists_theta : ∃ θ : ↥(normalizer (Zinf (h := h) g₁ s₀ : Set G)) →* GL (Fin 3) (ZMod 2),
    Function.Surjective θ ∧ θ.ker = (centralizer (Zinf (h := h) g₁ s₀ : Set G)).subgroupOf
      (normalizer (Zinf (h := h) g₁ s₀ : Set G)) := by
  refine CFSG.GF2Type.Aschbacher1976Full.HS.exists_GL32_of_dvd_14_index
    (D.isElemAbelian_Zinf hOut hTw hg₁ hs₀) (D.card_Zinf hOut hTw hg₁ hs₀) ?_
  rw [← Subgroup.normalizerMonoidHom_ker, Subgroup.index_ker]
  exact D.fourteen_dvd hOut hTw hg₁ hs₀

theorem K_facts :
    normalizer (Zinf (h := h) g₁ s₀ : Set G) =
        Kgrp (h := h) g₁ s₀ ⊔ centralizer (Zinf (h := h) g₁ s₀ : Set G) ∧
      ∃ φ : ↥(Kgrp (h := h) g₁ s₀) →* GL (Fin 3) (ZMod 2), Function.Surjective φ ∧
        φ.ker = (Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G)).subgroupOf
          (Kgrp (h := h) g₁ s₀) := by
  obtain ⟨θ, hθs, hθk⟩ := D.exists_theta hOut hTw hg₁ hs₀
  refine facts_of_theta θ hθs hθk (D.Kgrp_le_normalizer hOut hTw hg₁ hs₀)
    (fun n hn k hk => conj_mem_Kgrp (h := h) hn hk) ?_
  have hr₁Z := D.rep3_mem_Zinf hOut hTw hg₁ hs₀
  obtain ⟨-, h31, h3z⟩ := D.rep_props vecOf_three_ne q0_three
  obtain ⟨u, hu, hur⟩ := h.setting.exists_conj_eq_mul_z (Zinf_le_QG g₁ s₀ hr₁Z) h31 h3z
  refine ⟨u, by rw [D.Kgrp_eq_K0 hOut hTw hg₁ hs₀]; exact QG_le_K0 g₁ s₀ hu, fun huC => ?_⟩
  have hc := mem_centralizer_iff.mp huC (D.rep 3) hr₁Z
  have e : u * D.rep 3 * u⁻¹ = D.rep 3 := by rw [← hc]; group
  rw [e] at hur
  exact h.setting.z_ne_one (mul_left_cancel (hur.symm.trans (mul_one _).symm))

end Four

end Data41

end CFSG.Quasithin.H13.AS91
