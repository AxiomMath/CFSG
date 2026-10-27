module

public import CFSG.RankThree.GF2n.Tim81.Sec4.SL2Facts
public import CFSG.RankThree.GF2n.Tim81.Sec2.InvolutionModule
public import CFSG.RankThree.GF2n.Tim81.Sec4.W0Orth
public import CFSG.LocalAnalysis.EvenBN.Common.RadicalRank
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbAlpha
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PGroup

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Quasithin CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Tim81.Sec2 CFSG.RankThree.GF2n.Tim78 CFSG.QuasithinUnique.Setup.X7
  CFSG.LocalAnalysis.EvenBN.Common
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}
variable {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
variable [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]

namespace RootHyp

theorem card_sq_inf_V_W0_le_card_inf_Pc_conj_inf_W0
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hL : IsL2OrSz V H) {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (hcardW₀ : Nat.card W₀ =
      Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀)) :
    Nat.card ↥(V ⊓ W₀) ^ 2 ≤ Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) := by
  have hle : Nat.card ↥(V ⊓ W₀) ^ 4 ≤ Nat.card W₀ := by
    by_contra hlt
    rw [not_le] at hlt
    exact false_of_card_lt_fixedSub (hW := hW) h hPH hVH hH hnM hL hW₀ hN hW₀ne hmin hlt
  have hpos : 0 < Nat.card ↥(V ⊓ W₀) ^ 2 := Nat.pow_pos Nat.card_pos
  have h4 : Nat.card ↥(V ⊓ W₀) ^ 4 =
      Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(V ⊓ W₀) ^ 2 := by ring
  rw [hcardW₀, h4] at hle
  exact Nat.le_of_mul_le_mul_left hle hpos

theorem conjSubgroup_eq_of_imgK_conjSubgroup_eq
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {g₁ g₂ : G} (hg₁ : g₁ ∈ H) (hg₂ : g₂ ∈ H)
    (himg : imgK V H (conjSubgroup g₁ (Pc M V)) =
      imgK V H (conjSubgroup g₂ (Pc M V))) :
    conjSubgroup g₁ (Pc M V) = conjSubgroup g₂ (Pc M V) := by
  set y : G := g₂⁻¹ * g₁ with hy
  have hyH : y ∈ H := H.mul_mem (H.inv_mem hg₂) hg₁
  have hg₁H : conjSubgroup g₁ (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hg₁
  have hg₂H : conjSubgroup g₂ (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hg₂
  have hinv : piK V H ⟨g₂⁻¹, H.inv_mem hg₂⟩ = (piK V H ⟨g₂, hg₂⟩)⁻¹ := by
    rw [← map_inv]
    congr 1
  have hconj := congrArg (conjSubgroup (piK V H ⟨g₂⁻¹, H.inv_mem hg₂⟩)) himg
  rw [imgK_conjSubgroup hg₁ hPH, imgK_conjSubgroup hg₂ hPH,
    CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
    CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup, hinv, inv_mul_cancel,
    conjSubgroup_one] at hconj
  have hmul : (piK V H ⟨g₂, hg₂⟩)⁻¹ * piK V H ⟨g₁, hg₁⟩ = piK V H ⟨y, hyH⟩ := by
    rw [← map_inv, ← map_mul]
    congr 1
  rw [hmul] at hconj
  have hconj' : imgK V H (conjSubgroup y (Pc M V)) = imgK V H (Pc M V) := by
    rw [imgK_conjSubgroup hyH hPH]
    exact hconj
  have hyH' : conjSubgroup y (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hyH
  have hsup : conjSubgroup y (Pc M V) ⊔ kOf V H = Pc M V ⊔ kOf V H :=
    (imgK_eq_iff_sup_kOf_eq (V := V) (H := H) hyH' hPH).mp hconj'
  have hPy : conjSubgroup y (Pc M V) = Pc M V :=
    (h.conjSubgroup_eq_self_of_sup_conj_Pc_eq hPH hyH hsup).2.1
  have hfinal : conjSubgroup g₁ (Pc M V) = conjSubgroup g₂ (conjSubgroup y (Pc M V)) := by
    rw [hy, CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    congr 1
    group
  rw [hfinal, hPy]


private theorem exists_singer_partner
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {x : G} (hxH : x ∈ H) (hxP : x ∈ Pc M V) (hxK : x ∉ kOf V H) :
    ∃ y : G, ∃ hyH : y ∈ H, y ∈ conjSubgroup h₀ (Pc M V) ∧ y ∉ kOf V H ∧
      piK V H ⟨y, hyH⟩ * piK V H ⟨y, hyH⟩ = 1 ∧
      ∃ z : G, ∃ hzH : z ∈ H,
        piK V H ⟨z, hzH⟩ = piK V H ⟨x, hxH⟩ * piK V H ⟨y, hyH⟩ ∧
        ∀ g : G, g ∈ H → ∃ k : ℕ,
          imgK V H (conjSubgroup g (Pc M V)) =
            imgK V H (conjSubgroup (z ^ k) (Pc M V)) := by
  classical
  obtain ⟨-, -, a, b, ha, hb, hne⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  have hxA : ψ (piK V H ⟨x, hxH⟩) ∈ conjSubgroup a (utri F) := by
    rw [← ha]
    exact Subgroup.mem_map.mpr ⟨piK V H ⟨x, hxH⟩,
      (mem_imgK_iff).mpr ⟨⟨x, hxH⟩, hxP, rfl⟩, rfl⟩
  have hx1 : ψ (piK V H ⟨x, hxH⟩) ≠ 1 := by
    intro hh
    exact hxK ((piK_eq_one_iff _).mp (ψ.injective (by rw [hh, map_one])))
  obtain ⟨y0, hy0A', hy01, hreg⟩ :=
    CFSG.RankThree.GF2n.Tim81.Sec4.exists_mul_conjSubgroup_conj_utri_pow_of_ne hne hxA hx1
  have hymem : y0 ∈ (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom := by
    rw [hb]; exact hy0A'
  obtain ⟨ybar, hybar, hybarψ⟩ := Subgroup.mem_map.mp hymem
  obtain ⟨yH, hyHpi⟩ := piK_surjective V H ybar
  have hybar' : piK V H yH ∈ imgK V H (conjSubgroup h₀ (Pc M V)) := by
    rw [hyHpi]; exact hybar
  obtain ⟨yH', hyPh', hyH'pi⟩ := (mem_imgK_iff).mp hybar'
  have hybarψ' : ψ (piK V H yH') = y0 := by
    rw [hyH'pi, hyHpi]
    exact hybarψ
  have hyK : (yH' : G) ∉ kOf V H := by
    intro hk
    apply hy01
    rw [← hybarψ']
    simpa using congrArg ψ ((piK_eq_one_iff yH').mpr hk)
  obtain ⟨zH, hzHpi⟩ := piK_surjective V H
    (piK V H ⟨x, hxH⟩ * piK V H yH')
  have hz0 : ψ (piK V H zH) = ψ (piK V H ⟨x, hxH⟩) * y0 := by
    rw [hzHpi, map_mul, hybarψ']
  have hy0sq : y0 * y0 = 1 := by
    have hmem := mem_conjSubgroup.mp hy0A'
    have hu2 : (b⁻¹ * y0 * b) * (b⁻¹ * y0 * b) = 1 := by
      simpa [pow_two] using (isElemAbelian_utri (F := F)).2 (b⁻¹ * y0 * b) hmem
    calc y0 * y0 = b * ((b⁻¹ * y0 * b) * (b⁻¹ * y0 * b)) * b⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hy2 : piK V H yH' * piK V H yH' = 1 := by
    apply ψ.injective
    rw [map_mul, map_one, hybarψ']
    exact hy0sq
  refine ⟨(yH' : G), yH'.2, hyPh', hyK, hy2, (zH : G), zH.2, ?_, ?_⟩
  · exact hzHpi
  · intro g hg
    obtain ⟨k, hk⟩ := hreg (ψ (piK V H ⟨g, hg⟩))
    have hL : (imgK V H (conjSubgroup g (Pc M V))).map ψ.toMonoidHom =
        conjSubgroup (ψ (piK V H ⟨g, hg⟩)) ((imgK V H (Pc M V)).map ψ.toMonoidHom) := by
      rw [imgK_conjSubgroup hg hPH]
      exact map_conjSubgroup_mulEquiv ψ (piK V H ⟨g, hg⟩) (imgK V H (Pc M V))
    have hR : (imgK V H (conjSubgroup ((zH : G) ^ k) (Pc M V))).map ψ.toMonoidHom =
        conjSubgroup (ψ (piK V H (zH ^ k)))
          ((imgK V H (Pc M V)).map ψ.toMonoidHom) := by
      have harg : conjSubgroup ((zH : G) ^ k) (Pc M V) =
          conjSubgroup (((zH : ↥H) ^ k : ↥H) : G) (Pc M V) := rfl
      rw [harg, imgK_conjSubgroup (zH ^ k).2 hPH]
      exact map_conjSubgroup_mulEquiv ψ (piK V H (zH ^ k)) (imgK V H (Pc M V))
    have hzpow : piK V H (zH ^ k) = (piK V H zH) ^ k := map_pow (piK V H) zH k
    refine ⟨k, ?_⟩
    apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
    rw [hL, hR, ha, hzpow, map_pow, hz0]
    exact hk

private theorem le_normalizer_iInf_conjSubgroup :
    H ≤ Subgroup.normalizer
      ((⨅ g : ↥H, conjSubgroup (g : G) (Pc M V) : Subgroup G) : Set G) := by
  intro h hh
  rw [mem_normalizer_iff_conjSubgroup_eq]
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_iInf] at hy ⊢
    intro g
    have hy' := hy (⟨h⁻¹ * (g : G), H.mul_mem (H.inv_mem hh) g.2⟩ : ↥H)
    have hconj : conjSubgroup h
        (conjSubgroup (h⁻¹ * (g : G)) (Pc M V)) = conjSubgroup (g : G) (Pc M V) := by
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      congr 1
      group
    rw [← hconj]
    exact conj_mem_conjSubgroup h hy'
  · intro x hx
    rw [mem_conjSubgroup]
    rw [Subgroup.mem_iInf] at hx ⊢
    intro g
    have h1 := hx (⟨h * (g : G), H.mul_mem hh g.2⟩ : ↥H)
    have hconj : conjSubgroup h⁻¹ (conjSubgroup (h * (g : G)) (Pc M V)) =
        conjSubgroup (g : G) (Pc M V) := by
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      congr 1
      group
    rw [← hconj]
    simpa using conj_mem_conjSubgroup h⁻¹ h1

private theorem mul_comm_of_piK_eq_mul_of_common_fixed
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    {x y z w : G} (hxH : x ∈ H) (hyH : y ∈ H) (hzH : z ∈ H)
    (hzy : piK V H ⟨z, hzH⟩ = piK V H ⟨x, hxH⟩ * piK V H ⟨y, hyH⟩)
    (hwW : w ∈ W₀) (hxw : x * w = w * x) (hyw : y * w = w * y) :
    z * w = w * z := by
  have hxyw : (x * y) * w = w * (x * y) := by
    calc (x * y) * w = x * (y * w) := by group
      _ = x * (w * y) := by rw [hyw]
      _ = (x * w) * y := by group
      _ = (w * x) * y := by rw [hxw]
      _ = w * (x * y) := by group
  set k : G := z⁻¹ * (x * y) with hkdef
  have hkx : k ∈ kOf V H := by
    change z⁻¹ * (x * y) ∈ kOf V H
    refine (piK_eq_one_iff (V := V) (H := H)
      ⟨z⁻¹ * (x * y), H.mul_mem (H.inv_mem hzH) (H.mul_mem hxH hyH)⟩).mp ?_
    have h1 : (⟨z⁻¹ * (x * y), H.mul_mem (H.inv_mem hzH) (H.mul_mem hxH hyH)⟩ : ↥H) =
        (⟨z, hzH⟩ : ↥H)⁻¹ * (⟨x, hxH⟩ * ⟨y, hyH⟩) := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv, hzy]
    group
  have hkcomm : k * w = w * k := by
    exact (Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hkx).2 w (hW₀ hwW)).symm
  have hkinv : k⁻¹ * w = w * k⁻¹ := by
    calc k⁻¹ * w = k⁻¹ * (w * k) * k⁻¹ := by group
      _ = k⁻¹ * (k * w) * k⁻¹ := by rw [hkcomm]
      _ = w * k⁻¹ := by group
  have hz_eq : z = (x * y) * k⁻¹ := by
    rw [hkdef]; group
  calc z * w = ((x * y) * k⁻¹) * w := by rw [hz_eq]
    _ = (x * y) * (k⁻¹ * w) := by group
    _ = (x * y) * (w * k⁻¹) := by rw [hkinv]
    _ = ((x * y) * w) * k⁻¹ := by group
    _ = (w * (x * y)) * k⁻¹ := by rw [hxyw]
    _ = w * ((x * y) * k⁻¹) := by group
    _ = w * z := by rw [hz_eq]

private theorem two_le_card_of_ne_bot {K : Subgroup G} (hK : K ≠ ⊥) : 2 ≤ Nat.card K := by
  obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hne1 : Nat.card K ≠ 1 := by
    intro h1
    have hbot : K = ⊥ := Subgroup.card_eq_one.mp h1
    have hu1 : (u : G) = 1 := by simpa [hbot] using u.2
    exact hu (Subtype.ext hu1)
  omega

private theorem conjSubgroup_inf_W0_ne_bot
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥) :
    conjSubgroup h₀ V ⊓ W₀ ≠ ⊥ := by
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hPh2 : IsPGroup 2 (conjSubgroup h₀ (Pc M V)) := hP2.map _
  have hW02 : IsPGroup 2 W₀ := (isElemAbelian_xOf h hPH hVH).isPGroup.to_le hW₀
  have hPhH : conjSubgroup h₀ (Pc M V) ≤ H := by rw [hH]; exact le_sup_right
  have hPhN : conjSubgroup h₀ (Pc M V) ≤ Subgroup.normalizer (W₀ : Set G) :=
    hPhH.trans hN
  have hne := CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot
    Nat.prime_two hPh2 hW02 hW₀ne hPhN
  rwa [inf_centralizer_conj_Pc_eq_inf (h := h)] at hne

private theorem inf_centralizer_inf_eq_bot_of_singer
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    {x y z : G} (hxH : x ∈ H) (hyH : y ∈ H) (hzH : z ∈ H)
    (hzy : piK V H ⟨z, hzH⟩ = piK V H ⟨x, hxH⟩ * piK V H ⟨y, hyH⟩)
    (hreg : ∀ g : G, g ∈ H → ∃ k : ℕ,
      imgK V H (conjSubgroup g (Pc M V)) =
        imgK V H (conjSubgroup (z ^ k) (Pc M V))) :
    Pc M V ⊓ W₀ ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro w hw
  simp only [Subgroup.mem_inf] at hw
  obtain ⟨⟨⟨hwP, hwW⟩, hwx⟩, hwy⟩ := hw
  by_contra hw1
  have hxw : x * w = w * x := Subgroup.mem_centralizer_iff.mp hwx x (by simp)
  have hyw : y * w = w * y := Subgroup.mem_centralizer_iff.mp hwy y (by simp)
  have hzcomm : z * w = w * z :=
    mul_comm_of_piK_eq_mul_of_common_fixed hW₀ hxH hyH hzH hzy hwW hxw hyw
  set N : Subgroup G := W₀ ⊓ ⨅ g : ↥H, conjSubgroup (g : G) (Pc M V) with hNdef
  have hzpow : ∀ k : ℕ, z ^ k * w = w * z ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        calc z ^ k * z * w = z ^ k * (z * w) := by group
          _ = z ^ k * (w * z) := by rw [hzcomm]
          _ = (z ^ k * w) * z := by group
          _ = (w * z ^ k) * z := by rw [ih]
          _ = w * (z ^ k * z) := by group
  have hwN : w ∈ N := by
    refine Subgroup.mem_inf.mpr ⟨hwW, ?_⟩
    rw [Subgroup.mem_iInf]
    intro g
    obtain ⟨k, hk⟩ := hreg (g : G) g.2
    have hPg : conjSubgroup (g : G) (Pc M V) = conjSubgroup (z ^ k) (Pc M V) :=
      conjSubgroup_eq_of_imgK_conjSubgroup_eq h hPH g.2 (H.pow_mem hzH k) hk
    rw [hPg]
    rw [mem_conjSubgroup]
    have hfix : (z ^ k)⁻¹ * w * (z ^ k) = w := by
      calc (z ^ k)⁻¹ * w * (z ^ k) = (z ^ k)⁻¹ * (w * (z ^ k)) := by group
        _ = (z ^ k)⁻¹ * ((z ^ k) * w) := by rw [← hzpow k]
        _ = w := by group
    rw [hfix]
    exact hwP
  have hNne : N ≠ ⊥ := fun hbot => hw1 (by
    have : w ∈ (⊥ : Subgroup G) := hbot ▸ hwN
    exact Subgroup.mem_bot.mp this)
  have hNinv : H ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [hNdef]
    exact mem_normalizer_inf (hN hg) (le_normalizer_iInf_conjSubgroup hg)
  have hNeq : N = W₀ := hmin N inf_le_left hNne hNinv
  have hW0leP : W₀ ≤ Pc M V := by
    have hle : W₀ ≤ ⨅ g : ↥H, conjSubgroup (g : G) (Pc M V) := by
      rw [← hNeq, hNdef]
      exact inf_le_right
    have h1 := hle.trans (iInf_le (f := fun g : ↥H =>
      conjSubgroup (g : G) (Pc M V)) ⟨1, H.one_mem⟩)
    rwa [conjSubgroup_one] at h1
  have hBbot : (conjSubgroup h₀ V ⊓ W₀ : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    have hbP : b ∈ Pc M V := hW0leP hb.2
    have hmem : b ∈ conjSubgroup h₀ V ⊓ Pc M V := ⟨hb.1, hbP⟩
    rw [conjSubgroup_inf_Pc_eq_bot h hH hnM] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact conjSubgroup_inf_W0_ne_bot h hPH hVH hH hW₀ hN hW₀ne hBbot


private theorem card_le_card_inf_centralizer_mul
    {W₀ R Z : Subgroup G}
    (hWcomm : ∀ u ∈ W₀, ∀ v ∈ W₀, u * v = v * u)
    (hWsq : ∀ u ∈ W₀, u * u = 1)
    {t : G} (htN : t ∈ Subgroup.normalizer (W₀ : Set G))
    (hRW : R ≤ W₀) (himg : ∀ w ∈ R, ⁅(w : G), t⁆ ∈ Z) (hZW : Z ≤ W₀) :
    Nat.card R ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set G)) * Nat.card Z := by
  classical
  let ψ : ↥W₀ →* ↥W₀ := twistMap hWcomm t htN
  let φ : ↥R →* ↥W₀ := ψ.comp (Subgroup.inclusion hRW)
  have hφval : ∀ w : ↥R, ((φ w : ↥W₀) : G) = ⁅(w : G), t⁆ := by
    intro w
    have hval : ((φ w : ↥W₀) : G) = (w : G) * (t * (w : G) * t⁻¹) := rfl
    rw [hval, commutatorElement_def, inv_eq_of_mul_eq_one_right (hWsq (w : G) (hRW w.2))]
    group
  have hker : φ.ker = (R ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf R := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hw
      have h1 : ⁅(w : G), t⁆ = 1 := by
        have := congrArg (fun z : ↥W₀ => (z : G)) hw
        simpa [hφval w] using this
      refine Subgroup.mem_inf.mpr ⟨w.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have h2 : ⁅t, (w : G)⁆ = 1 := by
        rw [← commutatorElement_inv (w : G) t, h1, inv_one]
      exact commutatorElement_eq_one_iff_mul_comm.mp h2
    · rintro ⟨-, hc⟩
      apply Subtype.ext
      rw [hφval w]
      change ⁅(w : G), t⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hc t (by simp)).symm
  have hkerCard : Nat.card ↥φ.ker =
      Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange_le : φ.range ≤ Z.subgroupOf W₀ := by
    rintro y ⟨w, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [hφval w]
    exact himg w w.2
  have hZcard : Nat.card ↥(Z.subgroupOf W₀) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv
  have hrank := Subgroup.card_ker_mul_card_range φ
  calc Nat.card R = Nat.card ↥φ.ker * Nat.card ↥φ.range := hrank.symm
    _ ≤ Nat.card ↥φ.ker * Nat.card ↥(Z.subgroupOf W₀) :=
        Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective (Subgroup.inclusion hrange_le)
          (Subgroup.inclusion_injective _))
    _ = Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set G)) * Nat.card Z := by
        rw [hkerCard, hZcard]

private theorem card_W0_le_card_inf_centralizer_sq
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {X : Type} [Group X] (ψ : HBar V H ≃* X) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {y : G} (hyH : y ∈ H)
    (hy2 : piK V H ⟨y, hyH⟩ * piK V H ⟨y, hyH⟩ = 1) :
    Nat.card W₀ ≤ Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({y} : Set G)) ^ 2 := by
  classical
  let ρ : Representation (ZMod 2) X (subW hW W₀) := subRepW hW ψ hW₀ hN
  have hy2' : ψ (piK V H ⟨y, hyH⟩) * ψ (piK V H ⟨y, hyH⟩) = 1 := by
    rw [← map_mul, hy2, map_one]
  have hA6 : Nat.card ↥(subW hW W₀) ≤
      Nat.card (fixedSub ρ (Subgroup.zpowers (ψ (piK V H ⟨y, hyH⟩)))) ^ 2 :=
    Sec2.natCard_le_natCard_fixedSub_zpowers_sq ρ hy2'
  have hsub : (Subgroup.zpowers y).subgroupOf H = Subgroup.zpowers ⟨y, hyH⟩ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hmapS : Subgroup.map ((↑ψ) : HBar V H →* X) (imgK V H (Subgroup.zpowers y)) =
      Subgroup.zpowers (ψ (piK V H ⟨y, hyH⟩)) := by
    rw [imgK, hsub, Subgroup.map_map]
    exact MonoidHom.map_zpowers (((↑ψ) : HBar V H →* X).comp (piK V H)) ⟨y, hyH⟩
  have hcent : Subgroup.centralizer (Subgroup.zpowers y : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hfix := natCard_fixedSub_subRepW (hW := hW) ψ hW₀ hN
    (S := Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hyH)
  rw [hmapS] at hfix
  rw [hcent] at hfix
  calc Nat.card W₀ = Nat.card ↥(subW hW W₀) := (natCard_subW hW hW₀).symm
    _ ≤ Nat.card (fixedSub ρ (Subgroup.zpowers (ψ (piK V H ⟨y, hyH⟩)))) ^ 2 := hA6
    _ = Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({y} : Set G)) ^ 2 := by rw [hfix]

private theorem inf_V_W0_ne_bot
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) :
    V ⊓ W₀ ≠ ⊥ := by
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hW02 : IsPGroup 2 W₀ := (isElemAbelian_xOf h hPH hVH).isPGroup.to_le hW₀
  have hPN : Pc M V ≤ Subgroup.normalizer (W₀ : Set G) := hPH.trans hN
  have hne := CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot
    Nat.prime_two hP2 hW02 hW₀ne hPN
  rwa [inf_centralizer_Pc_eq_inf (h := h)] at hne

private theorem card_inf_Pc_W0_eq_mul_of_card
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hPW₀ : Pc M V ⊓ W₀ =
      (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀)) :
    Nat.card ↥(Pc M V ⊓ W₀) =
      Nat.card ↥(V ⊓ W₀) * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) := by
  classical
  set A : Subgroup G := V ⊓ W₀ with hA
  set P0 : Subgroup G := Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ with hP0
  have hPW : Pc M V ⊓ W₀ = A ⊔ P0 := by rw [hA, hP0]; exact hPW₀
  have hbot : A ⊓ P0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    simp only [Subgroup.mem_inf] at hx
    obtain ⟨⟨hxV, -⟩, ⟨-, hxPh⟩, -⟩ := hx
    have hmem : x ∈ V ⊓ conjSubgroup h₀ (Pc M V) := ⟨hxV, hxPh⟩
    rw [inf_conj_Pc_eq_bot h hH hnM] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hcomm : ∀ a ∈ A, ∀ b ∈ P0, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val ((isElemAbelian_xOf h hPH hVH).1.is_comm.comm
      ⟨a, hW₀ ha.2⟩ ⟨b, hW₀ hb.2⟩)
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A P0 hcomm).1
  rw [hbot, Subgroup.card_bot, mul_one] at h
  rw [hPW]
  exact h

private theorem exists_commutator_of_card
    {W₀ R Z : Subgroup G}
    (hWcomm : ∀ u ∈ W₀, ∀ v ∈ W₀, u * v = v * u)
    (hWsq : ∀ u ∈ W₀, u * u = 1)
    {t : G} (htN : t ∈ Subgroup.normalizer (W₀ : Set G))
    (hRW : R ≤ W₀) (himg : ∀ w ∈ R, ⁅(w : G), t⁆ ∈ Z) (hZW : Z ≤ W₀)
    (hcard : Nat.card R = Nat.card Z ^ 2)
    (hker : Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set G)) = Nat.card Z) :
    ∀ c ∈ Z, ∃ w ∈ R, ⁅(w : G), t⁆ = c := by
  classical
  let ψ : ↥W₀ →* ↥W₀ := twistMap hWcomm t htN
  let φ : ↥R →* ↥W₀ := ψ.comp (Subgroup.inclusion hRW)
  have hφval : ∀ w : ↥R, ((φ w : ↥W₀) : G) = ⁅(w : G), t⁆ := by
    intro w
    have hval : ((φ w : ↥W₀) : G) = (w : G) * (t * (w : G) * t⁻¹) := rfl
    rw [hval, commutatorElement_def, inv_eq_of_mul_eq_one_right (hWsq (w : G) (hRW w.2))]
    group
  have hkerφ : Nat.card ↥φ.ker = Nat.card Z := by
    have hkeq : φ.ker = (R ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf R := by
      ext w
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hw
        have h1 : ⁅(w : G), t⁆ = 1 := by
          have := congrArg (fun z : ↥W₀ => (z : G)) hw
          simpa [hφval w] using this
        refine Subgroup.mem_inf.mpr ⟨w.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        have h2 : ⁅t, (w : G)⁆ = 1 := by
          rw [← commutatorElement_inv (w : G) t, h1, inv_one]
        exact commutatorElement_eq_one_iff_mul_comm.mp h2
      · rintro ⟨-, hc⟩
        apply Subtype.ext
        rw [hφval w]
        change ⁅(w : G), t⁆ = 1
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp hc t (by simp)).symm
    rw [hkeq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).trans hker
  have hrange_le : φ.range ≤ Z.subgroupOf W₀ := by
    rintro y ⟨w, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [hφval w]
    exact himg w w.2
  have hZcard : Nat.card ↥(Z.subgroupOf W₀) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv
  have hrank := Subgroup.card_ker_mul_card_range φ
  have hrange_card : Nat.card ↥φ.range = Nat.card Z := by
    have h1 : Nat.card Z * Nat.card ↥φ.range = Nat.card Z * Nat.card Z := by
      calc Nat.card Z * Nat.card ↥φ.range
          = Nat.card ↥φ.ker * Nat.card ↥φ.range := by rw [hkerφ]
        _ = Nat.card R := hrank
        _ = Nat.card Z ^ 2 := hcard
        _ = Nat.card Z * Nat.card Z := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) h1
  have hrange_eq : φ.range = Z.subgroupOf W₀ :=
    Subgroup.eq_of_le_of_card_ge hrange_le (by rw [hrange_card, hZcard])
  intro c hc
  have hmem : (⟨c, hZW hc⟩ : ↥W₀) ∈ Z.subgroupOf W₀ :=
    Subgroup.mem_subgroupOf.mpr hc
  rw [← hrange_eq] at hmem
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, w.2, by rw [← hφval w]; exact congrArg Subtype.val hw⟩


private theorem commutator_mem_inf_V_W0
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {x w : G} (hxP : x ∈ Pc M V) (hw : w ∈ Pc M V ⊓ W₀) :
    ⁅w, x⁆ ∈ V ⊓ W₀ := by
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hw2 : w * w = 1 := by
    have := (isElemAbelian_xOf h hPH hVH).2 w (hW₀ hw.2)
    simpa [pow_two] using this
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact h.toHyp.frattini_Pc_le (commutatorElement_mem_inSubgroup_frattini hP2 hw.1 hxP)
  · have hxw : x * w * x⁻¹ ∈ W₀ :=
      (Subgroup.mem_normalizer_iff.mp (hN (hPH hxP)) w).mp hw.2
    have hval : ⁅w, x⁆ = w * (x * w * x⁻¹) := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_left hw2]
      group
    rw [hval]
    exact W₀.mul_mem hw.2 hxw

private theorem commutator_mem_conj_inf_V_W0
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) {y w : G}
    (hyPh : y ∈ conjSubgroup h₀ (Pc M V))
    (hw : w ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) :
    ⁅w, y⁆ ∈ conjSubgroup h₀ V ⊓ W₀ := by
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hPh2 : IsPGroup 2 (conjSubgroup h₀ (Pc M V)) := hP2.map _
  have hPhi : inSubgroup frattini (conjSubgroup h₀ (Pc M V)) ≤ conjSubgroup h₀ V :=
    frattini_conj_le hP2 h.toHyp.frattini_Pc_le h₀
  have hwPh : w ∈ conjSubgroup h₀ (Pc M V) := hw.1.2
  have hw2 : w * w = 1 := by
    have := (isElemAbelian_xOf h hPH hVH).2 w (hW₀ hw.2)
    simpa [pow_two] using this
  have hyH : y ∈ H := by rw [hH]; exact Subgroup.mem_sup_right hyPh
  refine Subgroup.mem_inf.mpr ⟨hPhi (commutatorElement_mem_inSubgroup_frattini hPh2 hwPh hyPh), ?_⟩
  have hyw : y * w * y⁻¹ ∈ W₀ :=
    (Subgroup.mem_normalizer_iff.mp (hN hyH) w).mp hw.2
  have hval : ⁅w, y⁆ = w * (y * w * y⁻¹) := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_left hw2]
    group
  rw [hval]
  exact W₀.mul_mem hw.2 hyw

private theorem commute_and_sq_of_le_xOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) :
    (∀ u ∈ W₀, ∀ v ∈ W₀, u * v = v * u) ∧ (∀ u ∈ W₀, u * u = 1) := by
  have hE := isElemAbelian_xOf h hPH hVH
  refine ⟨?_, ?_⟩
  · intro u hu v hv
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨u, hW₀ hu⟩ ⟨v, hW₀ hv⟩)
  · intro u hu
    have := hE.2 u (hW₀ hu)
    simpa [pow_two] using this

private theorem centralizer_card_bounds_of_partner
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (hPW₀ : Pc M V ⊓ W₀ =
      (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    (hcardW₀ : Nat.card W₀ =
      Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    {x y z : G} (hxH : x ∈ H) (hxP : x ∈ Pc M V) (hyH : y ∈ H) (hzH : z ∈ H)
    (hzy : piK V H ⟨z, hzH⟩ = piK V H ⟨x, hxH⟩ * piK V H ⟨y, hyH⟩)
    (hreg : ∀ g : G, g ∈ H → ∃ k : ℕ,
      imgK V H (conjSubgroup g (Pc M V)) =
        imgK V H (conjSubgroup (z ^ k) (Pc M V))) :
    Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) ≤
        Nat.card ↥(Pc M V ⊓ W₀ ⊓ Subgroup.centralizer ({x} : Set G)) ∧
      Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({y} : Set G)) ≤
        Nat.card ↥(V ⊓ W₀) ^ 2 := by
  classical
  set A : Subgroup G := V ⊓ W₀ with hA
  set P0 : Subgroup G := Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ with hP0
  have hcardW : Nat.card W₀ = Nat.card A ^ 2 * Nat.card P0 := by
    rw [hA, hP0]; exact hcardW₀
  have hno := inf_centralizer_inf_eq_bot_of_singer h hPH hVH hH hnM hW₀ hN hW₀ne hmin
    hxH hyH hzH hzy hreg
  have hcardPW : Nat.card ↥(Pc M V ⊓ W₀) = Nat.card A * Nat.card P0 :=
    card_inf_Pc_W0_eq_mul_of_card h hPH hVH hH hnM hW₀ hPW₀
  have himgX : ∀ w ∈ Pc M V ⊓ W₀, ⁅w, x⁆ ∈ A := by
    intro w hw
    exact commutator_mem_inf_V_W0 h hPH hVH hW₀ hN hxP hw
  have hcardX : Nat.card ↥(Pc M V ⊓ W₀) ≤
      Nat.card ↥(Pc M V ⊓ W₀ ⊓ Subgroup.centralizer ({x} : Set G)) *
        Nat.card A :=
    card_le_card_inf_centralizer_mul
      (fun u hu v hv => congrArg Subtype.val ((isElemAbelian_xOf h hPH hVH).1.is_comm.comm
        ⟨u, hW₀ hu⟩ ⟨v, hW₀ hv⟩))
      (fun u hu => by
        have := (isElemAbelian_xOf h hPH hVH).2 u (hW₀ hu)
        simpa [pow_two] using this)
      (hN hxH) inf_le_right himgX (by rw [hA]; exact inf_le_right)
  have hdisc : (Pc M V ⊓ W₀ ⊓ Subgroup.centralizer ({x} : Set G)) ⊓
      (W₀ ⊓ Subgroup.centralizer ({y} : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    simp only [Subgroup.mem_inf] at hv
    obtain ⟨⟨⟨hvP, hvW⟩, hvx⟩, -, hvy⟩ := hv
    have hmem : v ∈ Pc M V ⊓ W₀ ⊓ Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
        ⟨hvP, hvW⟩, hvx⟩, hvy⟩
    rw [hno] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hprodXY : Nat.card ↥(Pc M V ⊓ W₀ ⊓ Subgroup.centralizer ({x} : Set G)) *
      Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({y} : Set G)) ≤ Nat.card W₀ :=
    CFSG.card_mul_card_le_of_inf_eq_bot (inf_le_left.trans inf_le_right) inf_le_left hdisc
  have hkX : Nat.card P0 ≤
      Nat.card ↥(Pc M V ⊓ W₀ ⊓ Subgroup.centralizer ({x} : Set G)) := by
    have h := hcardX
    rw [hcardPW, mul_comm (Nat.card A) (Nat.card P0)] at h
    exact Nat.le_of_mul_le_mul_right h (Nat.card_pos (α := A))
  have hkY : Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({y} : Set G)) ≤ Nat.card A ^ 2 := by
    have h1 : Nat.card P0 * Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({y} : Set G)) ≤
        Nat.card A ^ 2 * Nat.card P0 := by
      calc Nat.card P0 * Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({y} : Set G))
          ≤ Nat.card ↥(Pc M V ⊓ W₀ ⊓ Subgroup.centralizer ({x} : Set G)) *
              Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({y} : Set G)) :=
            Nat.mul_le_mul_right _ hkX
        _ ≤ Nat.card W₀ := hprodXY
        _ = Nat.card A ^ 2 * Nat.card P0 := hcardW
    have h2 : Nat.card P0 * Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({y} : Set G)) ≤
        Nat.card P0 * Nat.card A ^ 2 := by
      rwa [mul_comm (Nat.card A ^ 2) (Nat.card P0)] at h1
    exact Nat.le_of_mul_le_mul_left h2 (Nat.card_pos (α := P0))
  exact ⟨hkX, hkY⟩

private theorem card_inf_Pc_conj_inf_W0_eq_and_card_W0
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hL : IsL2OrSz V H) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (hPW₀ : Pc M V ⊓ W₀ =
      (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    (hcardW₀ : Nat.card W₀ =
      Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    {x : G} (hxP : x ∈ Pc M V) (hxK : x ∉ kOf V H) :
    Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) = Nat.card ↥(V ⊓ W₀) ^ 2 ∧
      Nat.card W₀ = Nat.card ↥(V ⊓ W₀) ^ 4 := by
  classical
  set A : Subgroup G := V ⊓ W₀ with hA
  set P0 : Subgroup G := Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ with hP0
  have hxH : x ∈ H := hPH hxP
  have hcardW : Nat.card W₀ = Nat.card A ^ 2 * Nat.card P0 := by
    rw [hA, hP0]; exact hcardW₀
  have hC9 : Nat.card A ^ 2 ≤ Nat.card P0 := by
    rw [hA, hP0]
    exact card_sq_inf_V_W0_le_card_inf_Pc_conj_inf_W0 (hW := hW) h hPH hVH hH hnM hL
      hW₀ hN hW₀ne hmin hcardW₀
  obtain ⟨y, hyH, -, -, hy2, z, hzH, hzy, hreg⟩ :=
    exists_singer_partner h hPH hVH hH hnM ψ hxH hxP hxK
  have hno := inf_centralizer_inf_eq_bot_of_singer h hPH hVH hH hnM hW₀ hN hW₀ne hmin
    hxH hyH hzH hzy hreg
  have hWleY : Nat.card W₀ ≤ Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({y} : Set G)) ^ 2 :=
    card_W0_le_card_inf_centralizer_sq (hW := hW) ψ hW₀ hN hyH hy2
  obtain ⟨hkX, hkY⟩ := centralizer_card_bounds_of_partner h hPH hVH hH hnM hW₀ hN hW₀ne
    hmin hPW₀ hcardW₀ hxH hxP hyH hzH hzy hreg
  have hP0_le : Nat.card P0 ≤ Nat.card A ^ 2 := by
    have h1 : Nat.card A ^ 2 * Nat.card P0 ≤ Nat.card A ^ 2 * Nat.card A ^ 2 := by
      calc Nat.card A ^ 2 * Nat.card P0 = Nat.card W₀ := hcardW.symm
        _ ≤ Nat.card ↥(W₀ ⊓ Subgroup.centralizer ({y} : Set G)) ^ 2 := hWleY
        _ ≤ (Nat.card A ^ 2) ^ 2 := Nat.pow_le_pow_left hkY 2
        _ = Nat.card A ^ 2 * Nat.card A ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos (Nat.card_pos (α := A)) 2)
  have hP0_eq : Nat.card P0 = Nat.card A ^ 2 := le_antisymm hP0_le hC9
  exact ⟨hP0_eq, by rw [hcardW, hP0_eq]; ring⟩


private theorem card_conjSubgroup_inf_V_W0
    (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V))
    {W₀ : Subgroup G} (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) :
    Nat.card ↥(conjSubgroup h₀ V ⊓ W₀) = Nat.card ↥(V ⊓ W₀) := by
  obtain ⟨y₀, hy₀H, -, hVy₀, -⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hW₀conj : conjSubgroup y₀ W₀ = W₀ := conjSubgroup_eq_self_iff.mpr (hN hy₀H)
  calc Nat.card ↥(conjSubgroup h₀ V ⊓ W₀)
      = Nat.card ↥(conjSubgroup y₀ V ⊓ W₀) := by rw [hVy₀]
    _ = Nat.card ↥(conjSubgroup y₀ V ⊓ conjSubgroup y₀ W₀) := by rw [hW₀conj]
    _ = Nat.card ↥(conjSubgroup y₀ (V ⊓ W₀)) := by
        rw [CFSG.RankThree.GF2n.conjSubgroup_inf]
    _ = Nat.card ↥(V ⊓ W₀) := card_conjSubgroup y₀ (V ⊓ W₀)

private theorem kernel_bounds_of_partner
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    {x : G} (hxP : x ∈ Pc M V) (hxK : x ∉ kOf V H)
    (hP0_eq : Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) =
      Nat.card ↥(V ⊓ W₀) ^ 2) :
    Nat.card ↥(V ⊓ W₀) ≤
        Nat.card ↥((Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) ⊓
          Subgroup.centralizer ({x} : Set G)) ∧
      ∃ k2 : ℕ,
        Nat.card ↥(V ⊓ W₀) ≤ k2 ∧
          Nat.card ↥((Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) ⊓
            Subgroup.centralizer ({x} : Set G)) * k2 ≤
            Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) := by
  have hxH : x ∈ H := hPH hxP
  obtain ⟨y, hyH, hyPh, -, hy2, z, hzH, hzy, hreg⟩ :=
    exists_singer_partner h hPH hVH hH hnM ψ hxH hxP hxK
  have hno := inf_centralizer_inf_eq_bot_of_singer h hPH hVH hH hnM hW₀ hN hW₀ne hmin
    hxH hyH hzH hzy hreg
  set A : Subgroup G := V ⊓ W₀ with hA
  set P0 : Subgroup G := Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ with hP0
  set B : Subgroup G := conjSubgroup h₀ V ⊓ W₀ with hB
  have hP0_eq' : Nat.card P0 = Nat.card A ^ 2 := by
    rw [hP0, hA]; exact hP0_eq
  have hBcard : Nat.card B = Nat.card A := by
    rw [hB, hA]
    exact card_conjSubgroup_inf_V_W0 h hPH hH hN
  have hP0W : P0 ≤ W₀ := by rw [hP0]; exact inf_le_right
  obtain ⟨hcomm, hsq⟩ := commute_and_sq_of_le_xOf h hPH hVH hW₀
  have himgX : ∀ w ∈ P0, ⁅w, x⁆ ∈ A := by
    intro w hw
    exact commutator_mem_inf_V_W0 h hPH hVH hW₀ hN hxP ⟨hw.1.1, hw.2⟩
  have himgY : ∀ w ∈ P0, ⁅w, y⁆ ∈ B := by
    intro w hw
    exact commutator_mem_conj_inf_V_W0 h hPH hVH hH hW₀ hN hyPh ⟨⟨hw.1.1, hw.1.2⟩, hw.2⟩
  have hweakX : Nat.card P0 ≤ Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set G)) *
      Nat.card A :=
    card_le_card_inf_centralizer_mul hcomm hsq (hN hxH) hP0W himgX
      (by rw [hA]; exact inf_le_right)
  have hweakY : Nat.card P0 ≤ Nat.card ↥(P0 ⊓ Subgroup.centralizer ({y} : Set G)) *
      Nat.card A := by
    have h := card_le_card_inf_centralizer_mul hcomm hsq (hN hyH) hP0W himgY
      (by rw [hB]; exact inf_le_right)
    rwa [hBcard] at h
  have hjX : Nat.card A ≤ Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set G)) := by
    have h := hweakX
    rw [hP0_eq', pow_two] at h
    exact Nat.le_of_mul_le_mul_right h (Nat.card_pos (α := A))
  have hjY : Nat.card A ≤ Nat.card ↥(P0 ⊓ Subgroup.centralizer ({y} : Set G)) := by
    have h := hweakY
    rw [hP0_eq', pow_two] at h
    exact Nat.le_of_mul_le_mul_right h (Nat.card_pos (α := A))
  have hjbot : (P0 ⊓ Subgroup.centralizer ({x} : Set G)) ⊓
      (P0 ⊓ Subgroup.centralizer ({y} : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    simp only [Subgroup.mem_inf] at hv
    obtain ⟨⟨hvP0, hvx⟩, -, hvy⟩ := hv
    obtain ⟨⟨hvP, hvPh⟩, hvW⟩ := hvP0
    have hmem : v ∈ Pc M V ⊓ W₀ ⊓ Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
        ⟨hvP, hvW⟩, hvx⟩, hvy⟩
    rw [hno] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hjprod : Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set G)) *
      Nat.card ↥(P0 ⊓ Subgroup.centralizer ({y} : Set G)) ≤ Nat.card P0 :=
    CFSG.card_mul_card_le_of_inf_eq_bot inf_le_left inf_le_left hjbot
  refine ⟨by simpa [hP0, hA] using hjX,
    ⟨Nat.card ↥(P0 ⊓ Subgroup.centralizer ({y} : Set G)),
      by simpa [hP0, hA] using hjY, by simpa [hP0, hA] using hjprod⟩⟩

private theorem card_inf_P0_centralizer_eq
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    {x : G} (hxP : x ∈ Pc M V) (hxK : x ∉ kOf V H)
    (hP0_eq : Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) =
      Nat.card ↥(V ⊓ W₀) ^ 2) :
    Nat.card ↥((Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) ⊓
      Subgroup.centralizer ({x} : Set G)) = Nat.card ↥(V ⊓ W₀) := by
  classical
  set A : Subgroup G := V ⊓ W₀ with hA
  set P0 : Subgroup G := Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ with hP0
  have hP0_eq' : Nat.card P0 = Nat.card A ^ 2 := by
    rw [hP0, hA]; exact hP0_eq
  obtain ⟨hjX_raw, k2, hjY_raw, hjprod_raw⟩ :=
    kernel_bounds_of_partner h hPH hVH hH hnM ψ hW₀ hN hW₀ne hmin hxP hxK hP0_eq
  have hjX : Nat.card A ≤ Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set G)) := by
    simpa [← hA, ← hP0] using hjX_raw
  have hjY : Nat.card A ≤ k2 := by simpa [← hA] using hjY_raw
  have hjprod : Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set G)) * k2 ≤
      Nat.card P0 := by simpa [← hP0] using hjprod_raw
  have hjX_eq : Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card A := by
    refine le_antisymm ?_ hjX
    have h1 : Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set G)) * Nat.card A ≤
        Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set G)) * k2 :=
      Nat.mul_le_mul_left _ hjY
    have h2 : Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set G)) * Nat.card A ≤
        Nat.card A * Nat.card A := by
      calc Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set G)) * Nat.card A
          ≤ _ := h1
        _ ≤ Nat.card P0 := hjprod
        _ = Nat.card A * Nat.card A := by rw [hP0_eq']; ring
    exact Nat.le_of_mul_le_mul_right h2 (Nat.card_pos (α := A))
  exact hjX_eq


private theorem closure_commutator_P0_eq
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    {x : G} (hxP : x ∈ Pc M V) (hxK : x ∉ kOf V H)
    (hP0_eq : Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) =
      Nat.card ↥(V ⊓ W₀) ^ 2) :
    Subgroup.closure {c : G | ∃ w ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀,
      c = ⁅w, x⁆} = V ⊓ W₀ ∧
      Nat.card ↥((Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) ⊓
        Subgroup.centralizer ({x} : Set G)) = Nat.card ↥(V ⊓ W₀) := by
  classical
  have hxH : x ∈ H := hPH hxP
  set A : Subgroup G := V ⊓ W₀ with hA
  set P0 : Subgroup G := Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ with hP0
  have hP0_eq' : Nat.card P0 = Nat.card A ^ 2 := by
    rw [hP0, hA]; exact hP0_eq
  have hP0W : P0 ≤ W₀ := by rw [hP0]; exact inf_le_right
  obtain ⟨hcomm, hsq⟩ := commute_and_sq_of_le_xOf h hPH hVH hW₀
  have himgX : ∀ w ∈ P0, ⁅w, x⁆ ∈ A := by
    intro w hw
    exact commutator_mem_inf_V_W0 h hPH hVH hW₀ hN hxP ⟨hw.1.1, hw.2⟩
  have hjX_eq : Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card A := by
    have h := card_inf_P0_centralizer_eq h hPH hVH hH hnM ψ hW₀ hN hW₀ne hmin
      hxP hxK hP0_eq
    rwa [← hP0, ← hA] at h
  have hexists : ∀ c ∈ A, ∃ w ∈ P0, ⁅w, x⁆ = c :=
    exists_commutator_of_card hcomm hsq (hN hxH) hP0W himgX (by rw [hA]; exact inf_le_right)
      hP0_eq' hjX_eq
  have hset : {c : G | ∃ w ∈ P0, c = ⁅w, x⁆} = (A : Set G) := by
    ext c
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact himgX w hw
    · intro hc
      obtain ⟨w, hw, hwx⟩ := hexists c hc
      exact ⟨w, hw, hwx.symm⟩
  have hclosure : Subgroup.closure {c : G | ∃ w ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀,
      c = ⁅w, x⁆} = V ⊓ W₀ := by
    rw [show {c : G | ∃ w ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀,
      c = ⁅w, x⁆} = {c : G | ∃ w ∈ P0, c = ⁅w, x⁆} from by rw [hP0], hset, ← hA]
    change Subgroup.closure (A : Set G) = A
    refine le_antisymm ?_ Subgroup.subset_closure
    rw [Subgroup.closure_le]
  exact ⟨hclosure, hjX_eq⟩

theorem card_inf_Pc_conj_inf_W0_eq_and_closure_commutator
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hL : IsL2OrSz V H) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (hPW₀ : Pc M V ⊓ W₀ =
      (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    (hcardW₀ : Nat.card W₀ =
      Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    {x : G} (hxP : x ∈ Pc M V) (hxK : x ∉ kOf V H) :
    Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) = Nat.card ↥(V ⊓ W₀) ^ 2 ∧
      Nat.card W₀ = Nat.card ↥(V ⊓ W₀) ^ 4 ∧
      Subgroup.closure {c : G | ∃ w ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀,
        c = ⁅w, x⁆} = V ⊓ W₀ := by
  obtain ⟨h1, h2⟩ := card_inf_Pc_conj_inf_W0_eq_and_card_W0 (hW := hW)
    h hPH hVH hH hnM hL ψ hW₀ hN hW₀ne hmin hPW₀ hcardW₀ hxP hxK
  exact ⟨h1, h2, (closure_commutator_P0_eq h hPH hVH hH hnM ψ hW₀ hN hW₀ne hmin
    hxP hxK h1).1⟩


private theorem commutator_conj_mem_closure
    (h : RootHyp M V) {h₀ : G} {W₀ : Subgroup G} {a c w : G}
    (hc : c ∈ Subgroup.centralizer (V : Set G)) (haP : a ∈ Pc M V)
    (hw : w ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) :
    ⁅w, c * a * c⁻¹⁆ ∈ {z : G | ∃ p ∈ Pc M V, z = ⁅p, a⁆} := by
  have hwP : w ∈ Pc M V := hw.1.1
  have hwcP : c⁻¹ * w * c ∈ Pc M V := by
    have hcN : c ∈ Subgroup.normalizer (Pc M V : Set G) :=
      h.toHyp.le_normalizer_Pc (h.centralizer_le_M hc)
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) w).mp hwP
    simpa using h1
  have hconj : ⁅w, c * a * c⁻¹⁆ = c * ⁅c⁻¹ * w * c, a⁆ * c⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hinnerV : ⁅c⁻¹ * w * c, a⁆ ∈ V :=
    h.toHyp.frattini_Pc_le (commutatorElement_mem_inSubgroup_frattini
      ((inSubgroup_pCore_two M).1.to_le inf_le_left) hwcP haP)
  have hfix : c * ⁅c⁻¹ * w * c, a⁆ * c⁻¹ = ⁅c⁻¹ * w * c, a⁆ := by
    have hcomm := Subgroup.mem_centralizer_iff.mp hc ⁅c⁻¹ * w * c, a⁆ hinnerV
    rw [← hcomm]
    group
  exact ⟨c⁻¹ * w * c, hwcP, by simpa [hconj, hfix]⟩

theorem closure_commutator_Pc_eq_inf_V_W0
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (hPW₀ : Pc M V ⊓ W₀ =
      (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    (hcardW₀ : Nat.card W₀ =
      Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    {a : G} (ha : a ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) (ha1 : a ≠ 1) :
    Subgroup.closure {c : G | ∃ p ∈ Pc M V, c = ⁅p, a⁆} = V ⊓ W₀ := by
  classical
  set A : Subgroup G := V ⊓ W₀ with hA
  set P0 : Subgroup G := Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ with hP0
  have haP0 : a ∈ P0 := by rwa [hP0]
  have haP : a ∈ Pc M V := ha.1.1
  have haW : a ∈ W₀ := ha.2
  have haPh : a ∈ conjSubgroup h₀ (Pc M V) := ha.1.2
  set L : Subgroup G := V ⊔ Subgroup.zpowers a with hLdef
  have hLW : L ≤ Tim79a.xOf V H :=
    sup_le (le_xOf_self V H) (Subgroup.zpowers_le.mpr (hW₀ haW))
  have hLV : ¬ L ≤ V := by
    intro hle
    have hmem : a ∈ V := hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    have hmem' : a ∈ V ⊓ conjSubgroup h₀ (Pc M V) :=
      ⟨hmem, haPh⟩
    rw [inf_conj_Pc_eq_bot h hH hnM] at hmem'
    exact ha1 (Subgroup.mem_bot.mp hmem')
  obtain ⟨c, hc, hcL⟩ :=
    RootHyp.exists_conj_not_le_kOf h hPH hVH hH hnM hK hnab hL hLW hLV
  have hcV : conjSubgroup c V = V :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer _ hc)
  have hcL' : conjSubgroup c L = V ⊔ Subgroup.zpowers (c * a * c⁻¹) := by
    rw [hLdef, CFSG.CGT.Timmesfeld75.conjSubgroup_sup, hcV]
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup, MonoidHom.map_zpowers]
    rfl
  have halphaK : c * a * c⁻¹ ∉ kOf V H := by
    intro hk
    apply hcL
    rw [hcL']
    exact sup_le (le_kOf h hPH hVH) (Subgroup.zpowers_le.mpr hk)
  have halphaP : c * a * c⁻¹ ∈ Pc M V := by
    have hcM : c ∈ M := h.centralizer_le_M hc
    exact (Subgroup.mem_normalizer_iff.mp (h.toHyp.le_normalizer_Pc hcM) a).mp haP
  have hα := card_inf_Pc_conj_inf_W0_eq_and_closure_commutator (hW := hW)
    h hPH hVH hH hnM hL ψ hW₀ hN hW₀ne hmin hPW₀ hcardW₀ halphaP halphaK
  have hsubset : {z : G | ∃ w ∈ P0, z = ⁅w, c * a * c⁻¹⁆} ⊆
      {z : G | ∃ p ∈ Pc M V, z = ⁅p, a⁆} := by
    rintro z ⟨w, hw, rfl⟩
    exact commutator_conj_mem_closure h hc haP (by rwa [hP0] at hw)
  have hA_le : A ≤ Subgroup.closure {c : G | ∃ p ∈ Pc M V, c = ⁅p, a⁆} := by
    rw [hA, ← hα.2.2]
    exact Subgroup.closure_mono hsubset
  have hSA : Subgroup.closure {c : G | ∃ p ∈ Pc M V, c = ⁅p, a⁆} ≤ A := by
    rw [Subgroup.closure_le]
    rintro z ⟨p, hp, rfl⟩
    have h := commutator_mem_inf_V_W0 h hPH hVH hW₀ hN hp ⟨haP, haW⟩
    rw [hA]
    rw [← commutatorElement_inv a p]
    exact (V ⊓ W₀).inv_mem h
  exact le_antisymm hSA hA_le

private theorem exists_mem_P0_centralized_by_P
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hL : IsL2OrSz V H) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (hPW₀ : Pc M V ⊓ W₀ =
      (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    (hcardW₀ : Nat.card W₀ =
      Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    :
    ∃ x a : G, x ∈ Pc M V ∧ x ∉ kOf V H ∧
      a ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ ∧
      a ∈ Subgroup.centralizer ({x} : Set G) ∧ a ≠ 1 ∧
      Nat.card W₀ = Nat.card ↥(V ⊓ W₀) ^ 4 := by
  classical
  set A : Subgroup G := V ⊓ W₀ with hA
  set P0 : Subgroup G := Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ with hP0
  obtain ⟨xbar, hxbar1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (imgK_ne_bot_and_ne_of_sup h hPH hH hnM).1
  obtain ⟨xH, hxHpi⟩ := piK_surjective V H (xbar : HBar V H)
  have hxbarP : (xbar : HBar V H) ∈ imgK V H (Pc M V) := xbar.2
  obtain ⟨xH', hxP, hxpi⟩ := (mem_imgK_iff).mp hxbarP
  have hxK : (xH' : G) ∉ kOf V H := by
    intro hk
    apply hxbar1
    refine Subtype.ext ?_
    rw [← hxpi]
    exact (piK_eq_one_iff xH').mpr hk
  set x : G := (xH' : G) with hxdef
  have hα := card_inf_Pc_conj_inf_W0_eq_and_closure_commutator (hW := hW)
    h hPH hVH hH hnM hL ψ hW₀ hN hW₀ne hmin hPW₀ hcardW₀ hxP hxK
  have hP0_eq : Nat.card P0 = Nat.card A ^ 2 := by
    have h := hα.1
    rwa [← hP0, ← hA] at h
  have hW_eq : Nat.card W₀ = Nat.card A ^ 4 := by
    have h := hα.2.1
    rwa [← hA] at h
  have hkerX : Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card A :=
    (closure_commutator_P0_eq h hPH hVH hH hnM ψ hW₀ hN hW₀ne hmin hxP hxK
      (by rw [← hP0, ← hA]; exact hP0_eq)).2
  have hA_ne : A ≠ ⊥ := by
    rw [hA]
    exact inf_V_W0_ne_bot h hPH hVH hW₀ hN hW₀ne
  have hA_ge2 : 2 ≤ Nat.card A := two_le_card_of_ne_bot hA_ne
  have hker_ne : P0 ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(P0 ⊓ Subgroup.centralizer ({x} : Set G)) = 1 := by
      rw [hbot]; simp
    rw [hkerX] at h1
    omega
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker_ne
  have haKer : (a : G) ∈ P0 ⊓ Subgroup.centralizer ({x} : Set G) := a.2
  have haP0 : (a : G) ∈ P0 := (Subgroup.mem_inf.mp a.2).1
  have haCx : (a : G) ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp a.2).2
  have haP : (a : G) ∈ Pc M V := ((Subgroup.mem_inf.mp haP0).1).1
  have haW : (a : G) ∈ W₀ := (Subgroup.mem_inf.mp haP0).2
  have haG1 : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  exact ⟨x, (a : G), hxP, hxK, haP0, haCx, haG1, hW_eq⟩

private theorem two_mul_card_le_card_centralizer
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H) {x a : G}
    (hxP : x ∈ Pc M V) (hxK : x ∉ kOf V H) (haW : a ∈ W₀)
    (haCx : a ∈ Subgroup.centralizer ({x} : Set G)) :
    Nat.card ↥(Pc M V ⊓ kOf V H) * 2 ≤
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({a} : Set G)) := by
  classical
  set CP : Subgroup G := Pc M V ⊓ Subgroup.centralizer ({a} : Set G) with hCP
  set CP : Subgroup G := Pc M V ⊓ Subgroup.centralizer ({(a : G)} : Set G) with hCP
  have hPK_le_CP : Pc M V ⊓ kOf V H ≤ CP := by
    intro k hk
    refine Subgroup.mem_inf.mpr ⟨hk.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hk.2).2 (a : G) (hW₀ haW)
  have hxCP : Subgroup.zpowers x ≤ CP := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hxP, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (Subgroup.mem_centralizer_iff.mp haCx x (by simp)).symm
  have hx_notK : x ∉ Pc M V ⊓ kOf V H := fun hx => hxK hx.2
  have hS_ne : (Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers x ≠ Pc M V ⊓ kOf V H := by
    intro h
    apply hx_notK
    rw [← h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hrel_gt : 1 < (Pc M V ⊓ kOf V H).relIndex
      ((Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers x) := by
    have hrelcard := Subgroup.relIndex_mul_card (H := Pc M V ⊓ kOf V H)
      (K := (Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers x)
    have hinf : (Pc M V ⊓ kOf V H) ⊓
        ((Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers x) = Pc M V ⊓ kOf V H :=
      inf_eq_left.mpr le_sup_left
    rw [hinf] at hrelcard
    have hpos : 0 < (Pc M V ⊓ kOf V H).relIndex
        ((Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers x) := by
      by_contra h0
      have h0' : (Pc M V ⊓ kOf V H).relIndex
          ((Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers x) = 0 := by omega
      rw [h0', zero_mul] at hrelcard
      have hposS : 0 < Nat.card ↥((Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers x) := Nat.card_pos
      omega
    by_contra hle
    push Not at hle
    have h1 : (Pc M V ⊓ kOf V H).relIndex
        ((Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers x) = 1 := by omega
    rw [h1, one_mul] at hrelcard
    exact hS_ne (Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq hrelcard.symm)).symm
  have hS_card : Nat.card ↥(Pc M V ⊓ kOf V H) * 2 ≤
      Nat.card ↥((Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers x) := by
    have hrelcard := Subgroup.relIndex_mul_card (H := Pc M V ⊓ kOf V H)
      (K := (Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers x)
    have hinf : (Pc M V ⊓ kOf V H) ⊓
        ((Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers x) = Pc M V ⊓ kOf V H :=
      inf_eq_left.mpr le_sup_left
    rw [hinf] at hrelcard
    calc Nat.card ↥(Pc M V ⊓ kOf V H) * 2
        ≤ Nat.card ↥(Pc M V ⊓ kOf V H) *
            (Pc M V ⊓ kOf V H).relIndex ((Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers x) :=
          Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hrel_gt)
      _ = Nat.card ↥((Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers x) := by
          rw [mul_comm, hrelcard]
  have hCP_card : Nat.card ↥(Pc M V ⊓ kOf V H) * 2 ≤ Nat.card ↥CP :=
    hS_card.trans (Nat.card_le_card_of_injective
      (Subgroup.inclusion (sup_le hPK_le_CP hxCP)) (Subgroup.inclusion_injective _))
  exact hCP_card

private theorem exists_centralizer_card_ge
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hL : IsL2OrSz V H) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (hPW₀ : Pc M V ⊓ W₀ =
      (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    (hcardW₀ : Nat.card W₀ =
      Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀)) :
    ∃ a : G, a ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ ∧ a ≠ 1 ∧
      Nat.card ↥(Pc M V ⊓ kOf V H) * 2 ≤
        Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({a} : Set G)) ∧
      Nat.card W₀ = Nat.card ↥(V ⊓ W₀) ^ 4 := by
  classical
  set A : Subgroup G := V ⊓ W₀ with hA
  set P0 : Subgroup G := Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ with hP0
  obtain ⟨x, a, hxP, hxK, haP0raw, haCx, haG1, hW_eq_raw⟩ :=
    exists_mem_P0_centralized_by_P (hW := hW) h hPH hVH hH hnM hL ψ hW₀ hN
      hW₀ne hmin hPW₀ hcardW₀
  have haP0 : a ∈ P0 := haP0raw
  have haP : a ∈ Pc M V := ((Subgroup.mem_inf.mp haP0).1).1
  have haW : a ∈ W₀ := (Subgroup.mem_inf.mp haP0).2
  have hW_eq : Nat.card W₀ = Nat.card A ^ 4 := hW_eq_raw
  have hCP_card := two_mul_card_le_card_centralizer hW₀ hxP hxK haW haCx
  exact ⟨a, haP0raw, haG1, hCP_card, hW_eq_raw⟩

private theorem card_range_commutatorElementHom_eq_card_inf
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (hPW₀ : Pc M V ⊓ W₀ =
      (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    (hcardW₀ : Nat.card W₀ =
      Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    {a : G} (haP0 : a ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) (ha1 : a ≠ 1)
    (hZA : V ≤ Subgroup.centralizer (Pc M V : Set G))
    (hxA : ∀ p ∈ Pc M V, ⁅(a : G), p⁆ ∈ V) :
    Nat.card (commutatorElementHom (a : G) hZA hxA).range = Nat.card ↥(V ⊓ W₀) := by
  classical
  set A : Subgroup G := V ⊓ W₀ with hA
  let χ : ↥(Pc M V) →* ↥V := commutatorElementHom (a : G) hZA hxA
  let R : Subgroup G := (χ.range).map V.subtype
  have hS_range : {z : G | ∃ p ∈ Pc M V, z = ⁅p, (a : G)⁆} = (R : Set G) := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hmem : (⟨⁅(a : G), p⁆, hxA p hp⟩ : ↥V) ∈ χ.range :=
        ⟨⟨p, hp⟩, by apply Subtype.ext; rw [commutatorElementHom_apply]⟩
      have hinv : (⟨⁅(a : G), p⁆, hxA p hp⟩ : ↥V)⁻¹ ∈ χ.range :=
        χ.range.inv_mem hmem
      refine Subgroup.mem_map.mpr ⟨(⟨⁅(a : G), p⁆, hxA p hp⟩ : ↥V)⁻¹, hinv, ?_⟩
      simpa [Subgroup.coe_inv] using (commutatorElement_inv (a : G) p).symm
    · rintro ⟨v, hv, hvz⟩
      have hinv : v⁻¹ ∈ χ.range := χ.range.inv_mem hv
      obtain ⟨q, hq⟩ := hinv
      refine ⟨(q : G), q.2, ?_⟩
      have hq' : ⁅(a : G), (q : G)⁆ = ((v : ↥V) : G)⁻¹ := by
        have h := congrArg Subtype.val hq
        rw [commutatorElementHom_apply] at h
        exact h
      calc z = ((v : ↥V) : G) := hvz.symm
        _ = (((v : ↥V) : G)⁻¹)⁻¹ := (inv_inv _).symm
        _ = ⁅(a : G), (q : G)⁆⁻¹ := by rw [hq']
        _ = ⁅(q : G), (a : G)⁆ := commutatorElement_inv (a : G) (q : G)
  have hclosure : Subgroup.closure {z : G | ∃ p ∈ Pc M V, z = ⁅p, (a : G)⁆} = A := by
    have h := closure_commutator_Pc_eq_inf_V_W0 (hW := hW) h hPH hVH hH hnM hK hnab
      hL ψ hW₀ hN hW₀ne hmin hPW₀ hcardW₀ haP0 ha1
    rwa [← hA] at h
  have h1 : Subgroup.closure (R : Set G) = A := by
    rwa [← hS_range]
  have h2 : Subgroup.closure (R : Set G) = R := by
    refine le_antisymm ?_ Subgroup.subset_closure
    rw [Subgroup.closure_le]
  rw [h2] at h1
  have hrange : Nat.card χ.range = Nat.card A :=
    calc Nat.card χ.range = Nat.card R :=
          (Subgroup.card_map_of_injective V.subtype_injective).symm
      _ = Nat.card A := by rw [h1]
  simpa [hA] using hrange

private theorem card_range_mul_card_centralizer_eq
    {a : G} (hZA : V ≤ Subgroup.centralizer (Pc M V : Set G))
    (hxA : ∀ p ∈ Pc M V, ⁅(a : G), p⁆ ∈ V) :
    Nat.card (commutatorElementHom (a : G) hZA hxA).range *
        Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({a} : Set G)) =
      Nat.card ↥(Pc M V) := by
  have h := Subgroup.card_ker_mul_card_range (commutatorElementHom (a : G) hZA hxA)
  rw [ker_commutatorElementHom] at h
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  rwa [mul_comm] at h

private theorem card_Pc_eq_card_mul_centralizer
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (hPW₀ : Pc M V ⊓ W₀ =
      (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    (hcardW₀ : Nat.card W₀ =
      Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    {a : G} (haP0 : a ∈ Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) (ha1 : a ≠ 1) :
    Nat.card ↥(Pc M V) =
      Nat.card ↥(V ⊓ W₀) * Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({a} : Set G)) := by
  classical
  have haP : a ∈ Pc M V := ((Subgroup.mem_inf.mp haP0).1).1
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hZA : V ≤ Subgroup.centralizer (Pc M V : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hPCV : Pc M V ≤ Subgroup.centralizer (V : Set G) := inf_le_right
    exact (Subgroup.mem_centralizer_iff.mp (hPCV hp) z hz).symm
  have hxA : ∀ p ∈ Pc M V, ⁅(a : G), p⁆ ∈ V := by
    intro p hp
    exact h.toHyp.frattini_Pc_le (commutatorElement_mem_inSubgroup_frattini hP2 haP hp)
  have hrange := card_range_commutatorElementHom_eq_card_inf (hW := hW) h hPH hVH hH hnM
    hK hnab hL ψ hW₀ hN hW₀ne hmin hPW₀ hcardW₀ haP0 ha1 hZA hxA
  have hE9 := card_range_mul_card_centralizer_eq (a := a) hZA hxA
  rw [← hE9, hrange]

private theorem card_Pc_eq_card_inf_kOf_mul_card_field
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {n : ℕ} (hFn : Fintype.card F = 2 ^ n) :
    Nat.card ↥(Pc M V) = Nat.card ↥(Pc M V ⊓ kOf V H) * 2 ^ n := by
  classical
  let φ : ↥(Pc M V) →* HBar V H := (piK V H).comp (Subgroup.inclusion hPH)
  have hφrange : φ.range = imgK V H (Pc M V) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hφker : φ.ker = (Pc M V ⊓ kOf V H).subgroupOf (Pc M V) := by
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hp
      refine ⟨p.2, ?_⟩
      exact (piK_eq_one_iff (⟨p, hPH p.2⟩ : ↥H)).mp hp
    · rintro ⟨-, hp⟩
      exact (piK_eq_one_iff (⟨p, hPH p.2⟩ : ↥H)).mpr hp
  have hPcard : Nat.card ↥(Pc M V) =
      Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card (imgK V H (Pc M V)) := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hφker, hφrange] at h
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
    exact h.symm
  have hPbar : Nat.card (imgK V H (Pc M V)) = 2 ^ n := by
    rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective,
      (imgK_map_sl2 h hPH hVH hH hnM ψ).2.1, hFn]
  rw [hPcard, hPbar]

private theorem card_le_two_pow_sub_one_of_card_Pc_eq
    {A C : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hPcardA : Nat.card ↥(Pc M V) = Nat.card ↥A * Nat.card ↥C)
    (hC_card : Nat.card ↥(Pc M V ⊓ kOf V H) * 2 ≤ Nat.card ↥C)
    (hPcardK : Nat.card ↥(Pc M V) =
      Nat.card ↥(Pc M V ⊓ kOf V H) * 2 ^ n) :
    Nat.card ↥A ≤ 2 ^ (n - 1) := by
  have hbound : 2 * Nat.card A ≤ 2 ^ n := by
    have h1 : Nat.card ↥(Pc M V ⊓ kOf V H) * (2 * Nat.card A) ≤
        Nat.card ↥(Pc M V ⊓ kOf V H) * 2 ^ n := by
      calc Nat.card ↥(Pc M V ⊓ kOf V H) * (2 * Nat.card A)
          = Nat.card A * (2 * Nat.card ↥(Pc M V ⊓ kOf V H)) := by ring
        _ ≤ Nat.card A * Nat.card ↥C := Nat.mul_le_mul_left _ (by
            rw [mul_comm]; exact hC_card)
        _ = Nat.card ↥(Pc M V) := hPcardA.symm
        _ = Nat.card ↥(Pc M V ⊓ kOf V H) * 2 ^ n := hPcardK
    have hpos : 0 < Nat.card ↥(Pc M V ⊓ kOf V H) := Nat.card_pos
    exact Nat.le_of_mul_le_mul_left h1 hpos
  have h2 : 2 * Nat.card A ≤ 2 * 2 ^ (n - 1) := by
    calc 2 * Nat.card A ≤ 2 ^ n := hbound
      _ = 2 * 2 ^ (n - 1) := by
        rw [show n = 1 + (n - 1) by rw [add_comm]; exact (Nat.sub_add_cancel hn).symm,
          pow_add, pow_one]
        norm_num
  exact Nat.le_of_mul_le_mul_left h2 (by norm_num)

private theorem card_inf_V_W0_le_two_pow_sub_one_and_card_W0
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (hPW₀ : Pc M V ⊓ W₀ =
      (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    (hcardW₀ : Nat.card W₀ =
      Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    {n : ℕ} (hn : 1 ≤ n) (hFn : Fintype.card F = 2 ^ n) :
    Nat.card ↥(V ⊓ W₀) ≤ 2 ^ (n - 1) ∧
      Nat.card W₀ = Nat.card ↥(V ⊓ W₀) ^ 4 := by
  classical
  set A : Subgroup G := V ⊓ W₀ with hA
  obtain ⟨a, haP0raw, haG1, hCP_card, hW_eq_raw⟩ :=
    exists_centralizer_card_ge (hW := hW) h hPH hVH hH hnM hL ψ hW₀ hN hW₀ne
      hmin hPW₀ hcardW₀
  set CP : Subgroup G := Pc M V ⊓ Subgroup.centralizer ({a} : Set G) with hCP
  have hPcardA : Nat.card ↥(Pc M V) =
      Nat.card ↥A * Nat.card ↥CP := by
    have h := card_Pc_eq_card_mul_centralizer (hW := hW) h hPH hVH hH hnM hK hnab hL ψ
      hW₀ hN hW₀ne hmin hPW₀ hcardW₀ haP0raw haG1
    simpa [hA, hCP] using h
  have hCP_card' : Nat.card ↥(Pc M V ⊓ kOf V H) * 2 ≤ Nat.card ↥CP := by
    simpa [hCP] using hCP_card
  have hPcardK := card_Pc_eq_card_inf_kOf_mul_card_field h hPH hVH hH hnM ψ hFn
  have hA_le := card_le_two_pow_sub_one_of_card_Pc_eq hn hPcardA hCP_card' hPcardK
  exact ⟨by simpa [hA] using hA_le, hW_eq_raw⟩

theorem exists_orth_of_kOf_nonabelian
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (hPW₀ : Pc M V ⊓ W₀ =
      (V ⊓ W₀) ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀))
    (hcardW₀ : Nat.card W₀ =
      Nat.card ↥(V ⊓ W₀) ^ 2 * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀)) :
    ∃ (l : ℕ) (_ : 1 ≤ l) (hl : Fintype.card F = 2 ^ (2 * l)),
      Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN) ∧
      Nat.card ↥(V ⊓ W₀) = 2 ^ l ∧
      Pc M V ⊓ W₀ = ⁅W₀, Pc M V⁆ := by
  classical
  obtain ⟨n, -, hFn⟩ := FiniteField.card F 2
  have hFn' : Fintype.card F = 2 ^ (n : ℕ) := hFn
  have hn : 1 ≤ (n : ℕ) := by
    have h2 : 1 < Fintype.card F := Fintype.one_lt_card
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by rw [← hFn']; omega)
  obtain ⟨hAle, hWeq⟩ := card_inf_V_W0_le_two_pow_sub_one_and_card_W0 (hW := hW)
    h hPH hVH hH hnM hK hnab hL ψ hW₀ hN hW₀ne hmin hPW₀ hcardW₀ hn hFn'
  set A : Subgroup G := V ⊓ W₀ with hA
  have hA_le_pow : Nat.card A ≤ 2 ^ ((n : ℕ) - 1) := hAle
  have hW_eq : Nat.card W₀ = Nat.card A ^ 4 := hWeq
  have hWlt : Nat.card W₀ < 2 ^ (4 * (n : ℕ)) := by
    rw [hW_eq]
    calc Nat.card A ^ 4 ≤ (2 ^ ((n : ℕ) - 1)) ^ 4 := Nat.pow_le_pow_left hA_le_pow 4
      _ = 2 ^ (4 * ((n : ℕ) - 1)) := by rw [← pow_mul]; ring_nf
      _ < 2 ^ (4 * (n : ℕ)) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  set ρ : Representation (ZMod 2) SL(2, F) (subW hW W₀) := subRepW hW ψ hW₀ hN
  haveI : Fact ρ.IsIrreducible := ⟨isIrreducible_subRepW hW ψ hW₀ hN hW₀ne hmin⟩
  have hnt := exists_apply_subRepW_ne_one h hPH hH hnM ψ hW₀ hN hW₀ne
  obtain ⟨hA2, hAcard, -⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  have hAcard' : Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = 2 ^ (n : ℕ) := by
    rw [hAcard, hFn']
  have hlt' : Nat.card ↥(subW hW W₀) < 2 ^ (4 * (n : ℕ)) := by
    simpa only [natCard_subW hW hW₀] using hWlt
  rcases Sec2.isNaturalModule_or_isOrthModule_or_of_card_lt hn hFn ρ hnt
    ((imgK V H (Pc M V)).map ψ.toMonoidHom) hA2 hAcard' hlt' with hnat | horth | hthird
  · exact absurd hnat (not_isNaturalModule_subRepW h hPH hVH hH hnM ψ hW₀ hN hW₀ne)
  · obtain ⟨l, hl, hn2, horth⟩ := horth
    have hl1 : 1 ≤ l := by omega
    refine ⟨l, hl1, hl, horth, ?_, ?_⟩
    · rw [hA]
      exact card_inf_V_W0_eq_pow_of_isOrthModule h hPH hVH hH hnM ψ hl hW₀ hN horth
    · exact inf_Pc_W0_eq_commutator_of_isOrthModule h hPH hVH hH hnM ψ hl hW₀ hN horth
  · obtain ⟨l, hn3, hWcard3, hfixcard⟩ := hthird
    have hfixeq : Nat.card (fixedSub ρ ((imgK V H (Pc M V)).map ψ.toMonoidHom)) =
        Nat.card A := by
      rw [MulEquiv.toMonoidHom_eq_coe ψ,
        natCard_fixedSub_subRepW (hW := hW) ψ hW₀ hN (S := Pc M V) hPH,
        inf_centralizer_Pc_eq_inf (h := h), hA]
    have hAeq : Nat.card A = 2 ^ l := hfixeq.symm.trans hfixcard
    have hWcard3' : Nat.card W₀ = 2 ^ (8 * l) := by
      simpa only [natCard_subW hW hW₀] using hWcard3
    have hl1 : 1 ≤ l := by omega
    have heq : 2 ^ (4 * l) = 2 ^ (8 * l) := by
      rw [← hWcard3']
      calc (2 : ℕ) ^ (4 * l) = (2 ^ l) ^ 4 := by rw [← pow_mul]; ring_nf
        _ = Nat.card A ^ 4 := by rw [hAeq]
        _ = Nat.card W₀ := hW_eq.symm
    have hlt : 2 ^ (4 * l) < 2 ^ (8 * l) :=
      Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
    exact absurd heq (ne_of_lt hlt)

end RootHyp

end CFSG.RankThree.GF2n.Tim81
