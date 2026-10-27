module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Act
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Centre
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5TwoLocal
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Index
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UOuter

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup)

section InnerL

private lemma w6L_isElemAbelian_comap {G H : Type*} [Group G] [Group H] {p : ℕ} {f : G →* H}
    (hf : Function.Injective f) {E : Subgroup H} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap f) := by
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff]
    intro x y
    apply Subtype.ext
    show (x : G) * (y : G) = (y : G) * (x : G)
    apply hf
    rw [map_mul, map_mul]
    exact congrArg Subtype.val ((isMulCommutative_iff.mp hE.1) ⟨f x, x.2⟩ ⟨f y, y.2⟩)
  · intro x hx
    apply hf
    rw [map_pow, map_one]
    exact hE.2 (f x) hx

private lemma w6L_map_subtype_le_normalizer {X : Type*} [Group X] {H : Subgroup X}
    {E T : Subgroup ↥H} (h : E ≤ Subgroup.normalizer (T : Set ↥H)) :
    Subgroup.map H.subtype E ≤
      Subgroup.normalizer ((Subgroup.map H.subtype T : Subgroup X) : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨e * t * e⁻¹, ?_, ?_⟩
  · exact ((Subgroup.mem_normalizer_iff.mp (h he)) t).mp ht
  · simp

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

theorem TwE6Act.exists_twoLocal_rankFive_of_outer
    (hf : 1 ≤ f) (hB3 : ∀ b ∈ B, b ^ 3 = 1) (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (h3 : 3 ∣ 2 ^ f + 1) (hZ : Subgroup.center ↥G₀ = ⊥) (act : TwE6Act G₀ B hf) (b : ↥B)
    (hbout : (act.lam b : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∉
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQEquiv hf).toRingHom) :
    ∃ E T : Subgroup ↥(G₀ ⊔ Subgroup.zpowers (b : X)), T ≠ ⊥ ∧ IsPGroup 2 ↥T ∧ IsElemAbelian 3 E ∧
      3 ^ 5 ≤ Nat.card E ∧ E ≤ Subgroup.normalizer (T : Set ↥(G₀ ⊔ Subgroup.zpowers (b : X))) := by
  classical
  let K := GaloisField 2 (2 * f)
  let σ : K ≃+* K := frobQEquiv hf
  let C : Subgroup (ModGL TwistTag.E6.tag K) :=
    graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  have hcard : Nat.card K = (2 ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  have hσ : ∀ c : K, σ c = c ^ 2 ^ f := fun c =>
    CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 f c
  replace hbout : (act.lam b : ModGL TwistTag.E6.tag K) ∉ C := hbout
  have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using hB3 (b : X) b.2)
  let H : Subgroup X := G₀ ⊔ Subgroup.zpowers (b : X)
  have hHle : H ≤ Subgroup.normalizer (G₀ : Set X) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr (hBN b.2))
  let cH : ↥H →* MulAut ↥G₀ :=
    (Subgroup.normalizerMonoidHom G₀).comp (Subgroup.inclusion hHle)
  have cH_coe : ∀ (y : ↥H) (a : ↥G₀),
      ((cH y) a : X) = (y : X) * (a : X) * (y : X)⁻¹ := by
    intro y a
    exact Subgroup.normalizerMonoidHom_apply_apply_coe G₀ (Subgroup.inclusion hHle y) a
  let e₀ : ↥G₀ ≃* ↥C :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans act.θ
  let Φ : MulAut ↥G₀ ≃* MulAut ↥C := MulAut.congr e₀
  have h_e0 : ∀ y : ↥G₀, e₀ y = act.θ (QuotientGroup.mk y) := by
    intro y
    show act.θ ((QuotientGroup.quotientMulEquivOfEq hZ).symm
      (QuotientGroup.quotientBot.symm y)) = act.θ (QuotientGroup.mk y)
    rw [QuotientGroup.quotientBot_symm_apply, ← QuotientGroup.quotientMulEquivOfEq_mk hZ y,
      MulEquiv.symm_apply_apply]
  have hΦ_apply : ∀ (g : MulAut ↥G₀) (c : ↥C), (Φ g) c = e₀ (g (e₀.symm c)) := by
    intro g c
    simp only [Φ, MulAut.congr_apply, MulEquiv.trans_apply]
  let bH : ↥H := ⟨(b : X), Subgroup.mem_sup_right (Subgroup.mem_zpowers (b : X))⟩
  have hcHg : ∀ g : ↥G₀,
      cH ⟨(g : X), Subgroup.mem_sup_left g.2⟩ = MulAut.conj g := by
    intro g
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [cH_coe, MulAut.conj_apply]
    rfl
  have hΦg : ∀ g : ↥G₀,
      Φ (cH ⟨(g : X), Subgroup.mem_sup_left g.2⟩) = MulAut.conj (e₀ g) := by
    intro g
    rw [hcHg g]
    apply MulEquiv.ext
    intro c
    simp only [Φ, MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hΦb : Φ (cH bH) = RecipeExcLang.twConj K σ (act.lam b) := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    have hy' : (((cH bH) (e₀.symm c)) : X) =
        (b : X) * ((e₀.symm c : ↥G₀) : X) * (b : X)⁻¹ := by
      rw [cH_coe]
    have hact := act.act b (e₀.symm c) ((cH bH) (e₀.symm c)) hy'
    have hθc : act.θ (QuotientGroup.mk (e₀.symm c)) = c := by
      rw [← h_e0 (e₀.symm c), MulEquiv.apply_symm_apply]
    rw [hΦ_apply, RecipeExcLang.coe_twConj]
    rw [h_e0 ((cH bH) (e₀.symm c))]
    rw [show (c : ModGL TwistTag.E6.tag K) =
        (act.θ (QuotientGroup.mk (e₀.symm c)) : ModGL TwistTag.E6.tag K) by rw [hθc]]
    exact hact
  let Ψ : ↥H →* MulAut ↥C := Φ.toMonoidHom.comp cH
  have hNnorm : (G₀.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff le_sup_left]
    intro a k ha hk
    exact (Subgroup.mem_normalizer_iff.mp (hHle hk) a).mp ha
  have hsupH : G₀.subgroupOf H ⊔ (Subgroup.zpowers (b : X)).subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : G₀ ≤ H)
      (le_sup_right : Subgroup.zpowers (b : X) ≤ H)]
    exact Subgroup.subgroupOf_self H
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro y0 hy0
    have : (G₀.subgroupOf H).Normal := hNnorm
    have hy0sup : y0 ∈ G₀.subgroupOf H ⊔ (Subgroup.zpowers (b : X)).subgroupOf H := by
      rw [hsupH]; exact Subgroup.mem_top y0
    obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_left
      (s := G₀.subgroupOf H) (t := (Subgroup.zpowers (b : X)).subgroupOf H)).mp hy0sup
    have hx_eq : y0 = y * z := hyz.symm
    let g : ↥G₀ := ⟨(y : X), Subgroup.mem_subgroupOf.mp hy⟩
    have hy_eq : y = ⟨(g : X), Subgroup.mem_sup_left g.2⟩ := Subtype.ext rfl
    have hzp : (z : X) ∈ Submonoid.powers (b : X) :=
      (mem_powers_iff_mem_zpowers).mpr (Subgroup.mem_subgroupOf.mp hz)
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff (z : X) (b : X)).mp hzp
    have hz_eq : bH ^ i = z := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      simpa using hi
    have hx_decomp : y0 = y * bH ^ i := by rw [hx_eq, hz_eq]
    have hcHy0 : cH y0 = 1 := by
      have h1 : Φ (cH y0) = 1 := show Ψ y0 = 1 from hy0
      exact Φ.injective (by rw [h1, map_one])
    have hcHy : Φ (cH y) = MulAut.conj (e₀ g) := by
      rw [hy_eq]
      exact hΦg g
    have hd3 : (act.lam b : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
      have h1 : (act.lam b) ^ 3 = 1 := by
        rw [← map_pow, hb3, map_one]
      have h2 := congrArg (fun w : ↥(RecipeExcLang.twInndiagGroup K σ) =>
          (w : ModGL TwistTag.E6.tag K)) h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
    let d : ↥(RecipeExcLang.twInndiagGroup K σ) := act.lam b
    have hcx' : cH y * (cH bH) ^ i = 1 := by
      rw [← hcHy0, hx_decomp, map_mul, map_pow]
    have hconj_mul : MulAut.conj (e₀ g) *
        (RecipeExcLang.twConj K σ (act.lam b)) ^ i = 1 := by
      have h1 := congrArg Φ hcx'
      rw [map_mul, map_pow, map_one] at h1
      rw [hcHy, hΦb] at h1
      exact h1
    have htw : (RecipeExcLang.twConj K σ (act.lam b)) ^ i =
        (MulAut.conj (e₀ g))⁻¹ := eq_inv_of_mul_eq_one_right hconj_mul
    let c0 : ↥C := (e₀ g)⁻¹
    have htw2 : RecipeExcLang.twConj K σ ((act.lam b) ^ i) =
        RecipeExcLang.twConj K σ
          (⟨c0, RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c0.2⟩ :
            ↥(RecipeExcLang.twInndiagGroup K σ)) := by
      have h1 : RecipeExcLang.twConj K σ ((act.lam b) ^ i) = MulAut.conj c0 := by
        rw [map_pow, htw, ← map_inv]
      rw [h1, ← RecipeExcLang.twConj_of_mem_C0 σ c0]
    have hlam_i_C : (act.lam b) ^ i =
        (⟨c0, RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c0.2⟩ :
          ↥(RecipeExcLang.twInndiagGroup K σ)) :=
      NoOffTwE6Three.twConj_injective hf hcard σ hσ htw2
    have hlam_i_mem : (d : ModGL TwistTag.E6.tag K) ^ i ∈ C := by
      have h1 : ((d ^ i : ↥(RecipeExcLang.twInndiagGroup K σ)) :
          ModGL TwistTag.E6.tag K) ∈ C := by
        rw [show d = act.lam b from rfl, hlam_i_C]
        exact c0.2
      rwa [Subgroup.coe_pow] at h1
    have hmod_mem : (d : ModGL TwistTag.E6.tag K) ^ (i % 3) ∈ C := by
      have hsplit : (d : ModGL TwistTag.E6.tag K) ^ i =
          (d : ModGL TwistTag.E6.tag K) ^ (i % 3) := by
        conv_lhs => rw [← Nat.div_add_mod i 3]
        rw [pow_add, pow_mul, hd3, one_pow, one_mul]
      rw [← hsplit]
      exact hlam_i_mem
    have hmod0 : i % 3 = 0 := by
      by_contra hne
      have hlt : i % 3 < 3 := Nat.mod_lt i (by norm_num)
      interval_cases h : i % 3
      · exact hne rfl
      · exact hbout (by simpa [h, d] using hmod_mem)
      · apply hbout
        have h2 : (d : ModGL TwistTag.E6.tag K) ^ 2 ∈ C := by simpa [h] using hmod_mem
        have hd4 : (d : ModGL TwistTag.E6.tag K) ^ 4 = d := by
          calc (d : ModGL TwistTag.E6.tag K) ^ 4 =
                (d : ModGL TwistTag.E6.tag K) ^ (3 + 1) := by norm_num
            _ = (d : ModGL TwistTag.E6.tag K) ^ 3 * d := by rw [pow_add, pow_one]
            _ = d := by rw [hd3, one_mul]
        have hd_eq : (d : ModGL TwistTag.E6.tag K) =
            ((d : ModGL TwistTag.E6.tag K) ^ 2) ^ 2 := by
          rw [← pow_mul]
          norm_num
          exact hd4.symm
        rw [hd_eq]
        exact Subgroup.pow_mem C h2 2
    have hdvd : 3 ∣ i := Nat.dvd_iff_mod_eq_zero.mpr hmod0
    have hbi : b ^ i = 1 :=
      (orderOf_dvd_iff_pow_eq_one).mp
        (dvd_trans (orderOf_dvd_of_pow_eq_one hb3) hdvd)
    have hbiX : (b : X) ^ i = 1 := congrArg Subtype.val hbi
    have hz1 : z = 1 := by
      apply Subtype.ext
      rw [← hi, hbiX]
      rfl
    have hbHi : bH ^ i = 1 := by rw [hz_eq, hz1]
    have hy1 : y = 1 := by
      have hΨy : Ψ y = 1 := by
        have h1 : y0 = y := by rw [hx_decomp, hbHi, mul_one]
        rw [← h1]; exact hy0
      have hcy : cH y = 1 := by
        have h1 : Φ (cH y) = Φ 1 := by rw [map_one]; exact show Ψ y = 1 from hΨy
        exact Φ.injective h1
      have hcHg' : cH y = MulAut.conj g := by
        rw [hy_eq]
        exact hcHg g
      have hconj1 : MulAut.conj g = 1 := by rw [← hcHg']; exact hcy
      have hgcenter : g ∈ Subgroup.center ↥G₀ := by
        rw [Subgroup.mem_center_iff]
        intro a
        have ha := congrArg (fun f : MulAut ↥G₀ => f a) hconj1
        simp only [MulAut.conj_apply, MulAut.one_apply] at ha
        calc a * g = (g * a * g⁻¹) * g := by rw [ha]
          _ = g * a := by group
      have hg1 : g = 1 := by
        have h1 : g ∈ (⊥ : Subgroup ↥G₀) := hZ ▸ hgcenter
        exact Subgroup.mem_bot.mp h1
      rw [hy_eq, hg1]
      exact Subtype.ext (by simp)
    rw [hx_eq, hz1, mul_one, hy1]
  let dMod : ModGL TwistTag.E6.tag K := (act.lam b : ModGL TwistTag.E6.tag K)
  have hsup : RecipeExcLang.twInndiagGroup K σ = C ⊔ Subgroup.zpowers dMod :=
    twInndiag_eq_sup_zpowers hf hcard σ hσ (show dMod ∈ RecipeExcLang.twInndiagGroup K σ
      from (act.lam b).2) (show dMod ∉ C from hbout)
  have htop : C.subgroupOf (RecipeExcLang.twInndiagGroup K σ) ⊔
      (Subgroup.zpowers dMod).subgroupOf (RecipeExcLang.twInndiagGroup K σ) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (RecipeExcLang.graphFixedRootGroup_le_twInndiag σ)
      (Subgroup.zpowers_le.mpr (show dMod ∈ RecipeExcLang.twInndiagGroup K σ
        from (act.lam b).2)), ← hsup, Subgroup.subgroupOf_self]
  have hΨrange : (RecipeExcLang.twConj K σ).range ≤ Ψ.range := by
    rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨w, hw, rfl⟩
      have hwC : (w : ModGL TwistTag.E6.tag K) ∈ C := Subgroup.mem_subgroupOf.mp hw
      have hw' : RecipeExcLang.twConj K σ w =
          MulAut.conj (⟨(w : ModGL TwistTag.E6.tag K), hwC⟩ : ↥C) := by
        have hc : MulAut.conj (⟨(w : ModGL TwistTag.E6.tag K), hwC⟩ : ↥C) =
            RecipeExcLang.twConj K σ (⟨(w : ModGL TwistTag.E6.tag K),
              RecipeExcLang.graphFixedRootGroup_le_twInndiag σ hwC⟩ :
                ↥(RecipeExcLang.twInndiagGroup K σ)) :=
          (RecipeExcLang.twConj_of_mem_C0 σ ⟨(w : ModGL TwistTag.E6.tag K), hwC⟩).symm
        rw [hc]
      rw [hw']
      let g₀ : ↥G₀ := e₀.symm (⟨(w : ModGL TwistTag.E6.tag K), hwC⟩ : ↥C)
      refine ⟨⟨(g₀ : X), Subgroup.mem_sup_left g₀.2⟩, ?_⟩
      rw [show Ψ ⟨(g₀ : X), Subgroup.mem_sup_left g₀.2⟩ =
          Φ (cH ⟨(g₀ : X), Subgroup.mem_sup_left g₀.2⟩) from rfl, hΦg g₀,
        MulEquiv.apply_symm_apply]
    · rintro _ ⟨w, hw, rfl⟩
      have hwd : (w : ModGL TwistTag.E6.tag K) ∈ Subgroup.zpowers dMod :=
        Subgroup.mem_subgroupOf.mp hw
      have hwd' : (w : ModGL TwistTag.E6.tag K) ∈ Submonoid.powers dMod :=
        (mem_powers_iff_mem_zpowers).mpr hwd
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (w : ModGL TwistTag.E6.tag K) dMod).mp hwd'
      have hw_eq : w = (act.lam b) ^ k := by
        apply Subtype.ext
        show (w : ModGL TwistTag.E6.tag K) =
          ((act.lam b : ModGL TwistTag.E6.tag K)) ^ k
        exact hk.symm
      have hgen : RecipeExcLang.twConj K σ (act.lam b) ∈ Ψ.range := by
        refine ⟨bH, ?_⟩
        change Φ (cH bH) = RecipeExcLang.twConj K σ (act.lam b)
        exact hΦb
      rw [hw_eq]
      simpa only [map_pow] using Subgroup.pow_mem Ψ.range hgen k
  obtain ⟨E, T, hEtw, hTtw, hEelem, hEcard, hTp, hTne, hEnorm⟩ :=
    exists_twoLocal_rankFive_twE6 hf hcard σ hσ h3
  have hErange : E ≤ Ψ.range := hEtw.trans hΨrange
  have hTrange : T ≤ Ψ.range := hTtw.trans hΨrange
  let E' : Subgroup ↥H := E.comap Ψ
  let T' : Subgroup ↥H := T.comap Ψ
  have hE'map : Subgroup.map Ψ E' = E := Subgroup.map_comap_eq_self hErange
  have hT'map : Subgroup.map Ψ T' = T := Subgroup.map_comap_eq_self hTrange
  have hT'ne : T' ≠ ⊥ := by
    intro hbot
    apply hTne
    rw [← hT'map, hbot, Subgroup.map_bot]
  have hT'_p : IsPGroup 2 ↥T' := by
    let ϕ : ↥T' →* ↥T :=
      { toFun := fun a => ⟨Ψ (a : ↥H), Subgroup.mem_comap.mp a.2⟩
        map_one' := Subtype.ext (map_one Ψ)
        map_mul' := fun a b => Subtype.ext (map_mul Ψ (a : ↥H) (b : ↥H)) }
    refine IsPGroup.of_injective hTp ϕ ?_
    intro a b hab
    apply Subtype.ext
    exact hΨinj (congrArg Subtype.val hab)
  have hE_elem : IsElemAbelian 3 E' := w6L_isElemAbelian_comap hΨinj hEelem
  have hE'card : 3 ^ 5 ≤ Nat.card E' := by
    have h1 : Nat.card E' = Nat.card E := by
      rw [show E' = E.comap Ψ from rfl, ← Subgroup.card_map_of_injective hΨinj, hE'map]
    rw [h1]; exact hEcard
  have hnorm : E' ≤ Subgroup.normalizer (T' : Set ↥H) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he t ht
    rw [Subgroup.mem_comap] at he ht ⊢
    have h2 : Ψ (e * t * e⁻¹) = Ψ e * Ψ t * (Ψ e)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [h2]
    exact (Subgroup.mem_normalizer_iff.mp (hEnorm he) (Ψ t)).mp ht
  exact ⟨E', T', hT'ne, hT'_p, hE_elem, hE'card, hnorm⟩

theorem GGTCHyp.lam_mem_inner_twE6
    {ψ : (ggU .twistedE6 n f).K →* X}
    (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x) (hp : p = 3) (hf : 1 ≤ f) (hf1 : f = 1)
    (hB : Nat.card B ≤ 3 ^ 4) (hZ : Subgroup.center ↥G₀ = ⊥) (act : TwE6Act G₀ B hf)
    (b : ↥B) :
    (act.lam b : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQEquiv hf).toRingHom := by
  classical
  let K := GaloisField 2 (2 * f)
  let σ : K ≃+* K := frobQEquiv hf
  let C : Subgroup (ModGL TwistTag.E6.tag K) :=
    graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  have h3 : 3 ∣ 2 ^ f + 1 := by rw [hf1]; norm_num
  change (act.lam b : ModGL TwistTag.E6.tag K) ∈ C
  by_contra hbout
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := fun b hb => by
    have h1 := h.b_elem.2 b hb
    rwa [hp] at h1
  obtain ⟨E', T', hT'ne, hT'_p, hE_elem, hE'card, hnorm⟩ :=
    TwE6Act.exists_twoLocal_rankFive_of_outer hf hB3 h.b_norm h3 hZ act b hbout
  let H : Subgroup X := G₀ ⊔ Subgroup.zpowers (b : X)
  have hsubker : H.subtype.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff H.subtype).mpr (Subgroup.subtype_injective H)
  have hT_X_ne : Subgroup.map H.subtype T' ≠ ⊥ := by
    intro hbot
    have h1 : T' ≤ H.subtype.ker := (Subgroup.map_eq_bot_iff T').mp hbot
    rw [hsubker] at h1
    exact hT'ne (le_bot_iff.mp h1)
  let E_X : Subgroup X := Subgroup.map H.subtype E'
  let T_X : Subgroup X := Subgroup.map H.subtype T'
  have hEXcard : Nat.card E_X = Nat.card E' :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective H)
  have hEXelem : IsElemAbelian p E_X := by
    rw [show p = 3 from hp]
    exact hE_elem.map H.subtype
  have hTXp : IsPGroup 2 T_X := hT'_p.map H.subtype
  have hEXnorm : E_X ≤ Subgroup.normalizer (T_X : Set X) := w6L_map_subtype_le_normalizer hnorm
  have hrank := h.rank_le E_X T_X hT_X_ne hTXp hEXelem hEXnorm
  rw [hEXcard] at hrank
  norm_num at hE'card hB
  omega

end InnerL

end CFSG.StandardType.TableCRes

end
