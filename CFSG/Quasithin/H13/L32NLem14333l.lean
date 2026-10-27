module

public import CFSG.Quasithin.H13.L32NLem14333k

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits CFSG.Quasithin.SL3Model
open scoped commutatorElement MatrixGroups

namespace L14333

@[expose] def a7 : SL(3, ZMod 2) := ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], by decide⟩

theorem a7_pow : a7 ^ 7 = 1 := by decide

theorem a7_ne_one : a7 ≠ 1 := by decide

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx G T L V V₂ K g a z b d x D)
include c

theorem right_eq_one_of_mem_K (φ : ↥(D.img (l32nH T V)) ≃* RuType.SigmaL2F4) {y : G}
    (hyK : y ∈ K) : (φ (imgHom D ⟨y, le_of_mem_cComp c.comp hyK⟩)).right = 1 := by
  set R : Subgroup G := ((SemidirectProduct.rightHom.comp φ.toMonoidHom).comp (imgHom D)).ker.map
    (l32nH T V).subtype with hR
  have hle : oTwoUpper (l32nH T V) ≤ R := by
    refine (Subgroup.closure_le R).mpr fun g hg => ?_
    refine ⟨⟨g, hg.1⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
      SemidirectProduct.rightHom_eq_right]
    refine sigma_right_eq_one hg.2 ?_
    rw [← map_pow, ← map_pow]
    have : (⟨g, hg.1⟩ : ↥(l32nH T V)) ^ orderOf g = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one, map_one]
  obtain ⟨⟨y', hy'⟩, hk, hyy⟩ := hle (c.eq_oTwoUpper ▸ hyK)
  rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
    SemidirectProduct.rightHom_eq_right] at hk
  have e : y' = y := hyy
  subst e
  exact hk

theorem ncard_fix_eq_four {y : G} (hyK : y ∈ K) (hy2 : y * y = 1)
    (hyQ : y ∉ pCoreOf 2 (l32nH T V)) :
    {w : D.V | D.ρ ⟨y, l32nH_le_normalizer_fsuU T V (le_of_mem_cComp c.comp hyK)⟩ w = w}.ncard =
      4 := by
  have hyH : y ∈ l32nH T V := le_of_mem_cComp c.comp hyK
  obtain ⟨φ, ψ, hψ⟩ := c.ii.natural
  have hr : (φ (imgHom D ⟨y, hyH⟩)).right = 1 := c.right_eq_one_of_mem_K φ hyK
  have hsq : (φ (imgHom D ⟨y, hyH⟩)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow]
    have : (⟨y, hyH⟩ : ↥(l32nH T V)) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hy2)
    rw [this, map_one, map_one]
  have e : ∀ w : RuType.SigmaL2F4, w.right = 1 → (w ^ 2).left = w.left ^ 2 := by
    intro w hw
    have hw' : w = SemidirectProduct.inl w.left := by
      ext
      · rfl
      · rw [hw]; rfl
    rw [hw', ← map_pow]
    rfl
  have hA2 : (φ (imgHom D ⟨y, hyH⟩)).left ^ 2 = 1 := by
    have h := congrArg SemidirectProduct.left hsq
    rw [e _ hr] at h
    exact h
  have hA1 : (φ (imgHom D ⟨y, hyH⟩)).left ≠ 1 := by
    intro h
    apply hyQ
    have h1 : φ (imgHom D ⟨y, hyH⟩) = 1 := SemidirectProduct.ext h hr
    have h2 : imgHom D ⟨y, hyH⟩ = 1 := φ.injective (h1.trans (map_one φ).symm)
    have h3 := congrArg Subtype.val h2
    rw [imgHom_apply] at h3
    rw [c.q_eq]
    exact (rho_eq_one_iff_mem hyH _).mp h3
  have hcard := sl2_card_fix_of_sq _ hA2 hA1
  have hact : ∀ w : D.V, ψ (D.ρ ⟨y, l32nH_le_normalizer_fsuU T V hyH⟩ w) =
      ((φ (imgHom D ⟨y, hyH⟩)).left : Matrix (Fin 2) (Fin 2) RuType.F4).mulVec (ψ w) := by
    intro w
    have h : ψ (D.ρ ⟨y, l32nH_le_normalizer_fsuU T V hyH⟩ w) =
        RuType.sigmaAct (φ (imgHom D ⟨y, hyH⟩)) (ψ w) := hψ (imgHom D ⟨y, hyH⟩) w
    rw [h, sigmaAct_of_right_eq_one hr]
  have hS : ψ '' {w : D.V | D.ρ ⟨y, l32nH_le_normalizer_fsuU T V hyH⟩ w = w} =
      ↑(Finset.univ.filter fun v : Fin 2 → RuType.F4 =>
        ((φ (imgHom D ⟨y, hyH⟩)).left : Matrix (Fin 2) (Fin 2) RuType.F4).mulVec v = v) := by
    ext v
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [← hact, hw]
    · intro hv
      refine ⟨ψ.symm v, ?_, ψ.apply_symm_apply v⟩
      apply ψ.injective
      rw [hact, ψ.apply_symm_apply, hv]
  rw [← Set.ncard_image_of_injective _ ψ.injective, hS, Set.ncard_coe_finset, hcard]

theorem exists_conj_V_of_mem_U (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V))
    {u : G} (hu : u ∈ fsuU T V) (hu2 : u * u = 1) (huZ : u ∉ centerOf (fsuU T V)) :
    ∃ h ∈ l32nH T V, h⁻¹ * u * h ∈ V := by
  obtain ⟨φ, ψ, hψ⟩ := c.ii.natural
  have haU := c.ctx.aU
  have hψu : ψ (D.π u) ≠ 0 := fun h =>
    huZ ((L128A.HatU.π_eq_zero_iff D hu).mp (ψ.injective (h.trans (map_zero ψ).symm)))
  have hψa : ψ (D.π a) ≠ 0 := fun h => c.ctx.pi_ne (ψ.injective (h.trans (map_zero ψ).symm))
  obtain ⟨B, hB⟩ := sl2_exists_mulVec_eq _ _ hψa hψu
  obtain ⟨⟨h, hh⟩, hhγ⟩ := imgHom_surjective D (φ.symm (SemidirectProduct.inl B))
  have hφ : φ (imgHom D ⟨h, hh⟩) = SemidirectProduct.inl B := by
    rw [hhγ, MulEquiv.apply_symm_apply]
  have h1 : ψ (D.ρ ⟨h, l32nH_le_normalizer_fsuU T V hh⟩ (D.π a)) =
      RuType.sigmaAct (φ (imgHom D ⟨h, hh⟩)) (ψ (D.π a)) := hψ (imgHom D ⟨h, hh⟩) (D.π a)
  rw [hφ, sigmaAct_of_right_eq_one (SemidirectProduct.right_inl B), SemidirectProduct.left_inl,
    hB, D.ρ_π _ a haU] at h1
  have hwU : h * a * h⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp (l32nH_le_normalizer_fsuU T V hh) a).mp haU
  have h3 : D.π (h * a * h⁻¹) = D.π u := ψ.injective h1
  have he : (h * a * h⁻¹)⁻¹ * u ∈ centerOf (fsuU T V) := (D.π_eq_iff _ hwU u hu).mp h3
  set e := (h * a * h⁻¹)⁻¹ * u with he'
  have hue : u = h * a * h⁻¹ * e := by rw [he']; group
  have hww : h * a * h⁻¹ * (h * a * h⁻¹) = 1 := by
    calc h * a * h⁻¹ * (h * a * h⁻¹) = h * (a * a) * h⁻¹ := by group
      _ = 1 := by rw [c.mul_self_V c.a_mem_V]; group
  have hec : h * a * h⁻¹ * e = e * (h * a * h⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp he).2 _ hwU
  have hee : e * e = 1 := by
    calc e * e = h * a * h⁻¹ * (h * a * h⁻¹) * (e * e) := by rw [hww, one_mul]
      _ = h * a * h⁻¹ * (h * a * h⁻¹ * e) * e := by group
      _ = h * a * h⁻¹ * (e * (h * a * h⁻¹)) * e := by rw [hec]
      _ = (h * a * h⁻¹ * e) * (h * a * h⁻¹ * e) := by group
      _ = u * u := by rw [← hue]
      _ = 1 := hu2
  have heV : e ∈ V := c.mem_V_of_mul_self hyp ((le_sup_right.trans (c.sup_zU_le_P hyp)) he) hee
  have heV1 : e ∈ fsuV1 T V := by rw [← c.vZ]; exact ⟨heV, he⟩
  have hconj : h⁻¹ * e * h = e := by
    have := c.ctx.H_V1 h⁻¹ (inv_mem hh) e heV1
    rwa [inv_inv] at this
  refine ⟨h, hh, ?_⟩
  have h4 : h⁻¹ * u * h = a * e := by
    calc h⁻¹ * u * h = h⁻¹ * (h * a * h⁻¹ * e) * h := by rw [← hue]
      _ = a * (h⁻¹ * e * h) := by group
      _ = a * e := by rw [hconj]
  rw [h4]
  exact V.mul_mem c.a_mem_V heV

theorem card_cent_V_le {y : G} (hyL : y ∈ L) (hyP : y ∉ pCoreOf 2 L) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) ≤ 4 := by
  obtain ⟨_, S⟩ := c.setting
  have hdvd : Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) ∣ 8 := by
    rw [← c.card_V]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) ≠ 8 := by
    intro h8
    apply hyP
    have heq := Subgroup.eq_of_le_of_card_ge
      (inf_le_left : V ⊓ Subgroup.centralizer ({y} : Set G) ≤ V) (by rw [c.card_V, h8])
    rw [← S.cent_eq]
    refine ⟨hyL, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : v ∈ V ⊓ Subgroup.centralizer ({y} : Set G) := by rw [heq]; exact hv
    exact Subgroup.mem_centralizer_singleton_iff.mp hv'.2
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  set n := Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) with hn
  interval_cases n <;> omega

end Ctx

namespace Inv

variable {T L V V₂ K : Subgroup G} {g a z b d x r : G} {D : HatModelU (fsuU T V)}
  (ι : Inv G T L V V₂ K g a z b d x r D)
include ι

theorem not_conj_V (g : G) : g⁻¹ * r * g ∉ V := by
  intro hv
  obtain ⟨_, S⟩ := ι.setting
  obtain ⟨θ, ψ, hsurj, hker, -, -, -, -⟩ := ι.exists_coordZ ι.hyp
  obtain ⟨⟨l₀, hl₀⟩, hl₀θ⟩ := hsurj a7
  obtain ⟨p, hp, hpl⟩ := ι.exists_mul_comm ι.hyp ι.r_P ι.r_L hl₀
  have hc₀L : p * l₀ ∈ L := L.mul_mem (pCoreOf_le 2 L hp) hl₀
  have hθ : θ ⟨p * l₀, hc₀L⟩ = a7 := by
    have e : (⟨p * l₀, hc₀L⟩ : ↥L) = ⟨p, pCoreOf_le 2 L hp⟩ * ⟨l₀, hl₀⟩ := rfl
    rw [e, map_mul, (hker _).mpr hp, one_mul, hl₀θ]
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 : 7 ∣ orderOf (p * l₀) := by
    have h1 : orderOf a7 = 7 := orderOf_eq_prime a7_pow a7_ne_one
    have h2 := orderOf_map_dvd θ ⟨p * l₀, hc₀L⟩
    rw [hθ, h1, ← Subgroup.orderOf_coe] at h2
    exact h2
  obtain ⟨m, hm⟩ := h7
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hm
    exact (orderOf_pos (p * l₀)).ne' hm
  set c₁ := (p * l₀) ^ m with hc₁
  have hc₁7 : orderOf c₁ = 7 := by
    rw [hc₁, orderOf_pow_of_dvd hm0 ⟨7, by rw [hm, mul_comm]⟩, hm]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  have hc₁r : c₁ * r = r * c₁ := (Commute.pow_left (show Commute (p * l₀) r from hpl.symm) m).eq
  have hv1 : g⁻¹ * r * g ≠ 1 := by
    intro h1
    apply ι.r_notL
    have : r = g * (g⁻¹ * r * g) * g⁻¹ := by group
    rw [this, h1, mul_one, mul_inv_cancel]
    exact L.one_mem
  obtain ⟨l, -, hlz⟩ := ι.exists_conj_eq ι.hyp hv hv1
  have hr : r = (g * l) * z * (g * l)⁻¹ := by
    calc r = g * (g⁻¹ * r * g) * g⁻¹ := by group
      _ = g * (l * z * l⁻¹) * g⁻¹ := by rw [hlz]
      _ = (g * l) * z * (g * l)⁻¹ := by group
  set h := g * l with hh
  set y := h⁻¹ * c₁ * h with hy
  have hyz : y * z * y⁻¹ = z := by
    calc y * z * y⁻¹ = h⁻¹ * (c₁ * (h * z * h⁻¹) * c₁⁻¹) * h := by rw [hy]; group
      _ = h⁻¹ * (c₁ * r * c₁⁻¹) * h := by rw [← hr]
      _ = h⁻¹ * r * h := by rw [hc₁r]; group
      _ = z := by rw [hr]; group
  have hyH : y ∈ l32nH T V := S.mem_g1 ι.z_mem ι.z_ne hyz
  have hy7 : y ^ 7 = 1 := by
    have e : y = (MulAut.conj h⁻¹) c₁ := by rw [MulAut.conj_apply, inv_inv]
    rw [e, ← map_pow, ← hc₁7, pow_orderOf_eq_one, map_one]
  have hy1 : y ≠ 1 := by
    intro h1
    have : c₁ = 1 := by
      calc c₁ = h * y * h⁻¹ := by rw [hy]; group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hc₁7
    omega
  apply hy1
  refine ι.eq_one_of_imgHom hyH (by decide : Odd 7) hy7 ?_
  have h1 := orderOf_dvd_natCard (imgHom D ⟨y, hyH⟩)
  rw [ι.card_img_H] at h1
  have h2 : orderOf (imgHom D ⟨y, hyH⟩) ∣ 7 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow]
    have : (⟨y, hyH⟩ : ↥(l32nH T V)) ^ 7 = 1 := Subtype.ext (by simpa using hy7)
    rw [this, map_one]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 7 120) h2 h1)

theorem sq_mem_V1 {f : G} (hf : f ∈ T ⊓ Subgroup.centralizer ({r} : Set G))
    (hfc : ∀ t ∈ T ⊓ Subgroup.centralizer ({r} : Set G), t * (f * f) = f * f * t) :
    f * f ∈ fsuV1 T V := by
  obtain ⟨_, S⟩ := ι.setting
  obtain ⟨θ, ψ, -, hker, hequiv, hline, -, hQv⟩ := ι.exists_coordZ ι.hyp
  have hX : ∀ {t : G}, t ∈ T → t * r = r * t → t ∈ T ⊓ Subgroup.centralizer ({r} : Set G) :=
    fun ht htr => ⟨ht, Subgroup.mem_centralizer_singleton_iff.mpr htr⟩
  have hsL : f * f ∈ L := ι.sq_mem hf.1
  have hsP : f * f ∈ pCoreOf 2 L := by
    rw [← S.cent_eq]
    exact ⟨hsL, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      hfc v (hX (S.VT hv) (ι.r_V v hv).symm)⟩
  have hsr : r * (f * f) = f * f * r := hfc r (hX ι.r_T rfl)
  have hss : f * f * (f * f) = 1 := by
    have h1 := ι.r_P _ hsP
    have h2 : r * (f * f) * r⁻¹ = f * f := by rw [hsr]; group
    have h3 : f * f = (f * f)⁻¹ := h2.symm.trans h1
    calc f * f * (f * f) = f * f * (f * f)⁻¹ := congrArg (f * f * ·) h3
      _ = 1 := mul_inv_cancel _
  have hsV : f * f ∈ V := ι.mem_V_of_mul_self ι.hyp hsP hss
  have hfix : ∀ q ∈ Qv (vE (ZMod 2) 0),
      q • Multiplicative.toAdd (ψ ⟨f * f, hsV⟩) = Multiplicative.toAdd (ψ ⟨f * f, hsV⟩) := by
    intro q hq
    obtain ⟨u, huU, rfl⟩ := hQv q hq
    obtain ⟨p, hp, hpu⟩ := ι.exists_mul_comm ι.hyp ι.r_P ι.r_L u.2
    have hpuL : p * u ∈ L := L.mul_mem (pCoreOf_le 2 L hp) u.2
    have hpuX := hX (T.mul_mem (ι.P_le_T hp) (ι.U_le_T huU)) hpu.symm
    have hθ : θ ⟨p * u, hpuL⟩ = θ u := by
      have e : (⟨p * u, hpuL⟩ : ↥L) = ⟨p, pCoreOf_le 2 L hp⟩ * u := rfl
      rw [e, map_mul, (hker _).mpr hp, one_mul]
    calc θ u • Multiplicative.toAdd (ψ ⟨f * f, hsV⟩) =
          θ ⟨p * u, hpuL⟩ • Multiplicative.toAdd (ψ ⟨f * f, hsV⟩) := by rw [hθ]
      _ = Multiplicative.toAdd (ψ ⟨p * u * (f * f) * (p * u)⁻¹, ι.conj_mem_V hpuL hsV⟩) :=
          (hequiv ⟨p * u, hpuL⟩ ⟨f * f, hsV⟩).symm
      _ = Multiplicative.toAdd (ψ ⟨f * f, hsV⟩) := by
          congr 2
          apply Subtype.ext
          show p * u * (f * f) * (p * u)⁻¹ = f * f
          rw [hfc _ hpuX]
          group
  obtain ⟨e, he⟩ := eq_smul_e0_of_fix hfix
  exact (hline ⟨f * f, hsV⟩).mpr ⟨e, he⟩

end Inv

end L14333

end CFSG.Quasithin.H13
