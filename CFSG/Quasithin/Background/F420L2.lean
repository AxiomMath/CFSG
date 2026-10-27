module

public import CFSG.Quasithin.Background.F420Basic
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenL2
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective

public section

namespace CFSG.Quasithin.F420

open CFSG.Open (quasithinIsSylowTwo)
open CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter
open scoped MatrixGroups

theorem eq_one_of_fix_sylow_of_statedPSL_two_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 n) {S : Subgroup X} (hS : quasithinIsSylowTwo S)
    {y : X} (hy : orderOf y = 3) (α : MulAut X) (hα : ∀ s ∈ S, α s = s) (hαy : α y = y) :
    α = 1 := by
  have hn : 1 ≤ n := h.1.2.1
  have hcardX := card_of_statedPSL_two_two h
  have hfinX : Finite X := Nat.finite_of_card_ne_zero (by
    rw [hcardX]
    have : 1 < 4 ^ n := Nat.one_lt_pow (by omega) (by norm_num)
    exact Nat.mul_ne_zero (by positivity) (by omega))
  have hinner := CFSG.QuasithinUnique.Ch1.sylowCentralizingAutInner_of_stated_psl_two hn h
  obtain ⟨x, hx⟩ := hinner S (CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mpr hS) α hα
  have hcomm : ∀ w : X, α w = w → x * w = w * x := by
    intro w hw
    have h1 := (hx w).symm.trans hw
    calc x * w = x * (x⁻¹ * w * x) := by rw [h1]
      _ = w * x := by group
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn
      hK
  let e' : X ≃* PSL(2, K) := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hinv : ∀ t w : X, orderOf t = 2 → t * w = w * t → w ^ 2 = 1 := by
    intro t w ht htw
    have ht' : orderOf (e' t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
    have hw' : e' w ∈ Subgroup.centralizer ({e' t} : Set PSL(2, K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, htw]
    have := CFSG.Walter.psl2_sq_eq_one_of_mem_centralizer_of_charTwo ht' hw'
    apply e'.injective
    rw [map_pow, this, map_one]
  have h2X : 2 ∣ Nat.card X := by
    rw [hcardX]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 h2X
  have hT : IsPGroup 2 (Subgroup.zpowers t₀) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht₀, pow_one]
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup hT hS
  let t := g * t₀ * g⁻¹
  have ht : orderOf t = 2 := by
    rw [show t = MulAut.conj g t₀ from rfl, MulEquiv.orderOf_eq, ht₀]
  have htS : t ∈ S := hg t₀ (Subgroup.mem_zpowers t₀)
  have hx2 : x ^ 2 = 1 := hinv t x ht (hcomm t (hα t htS)).symm
  have hx1 : x = 1 := by
    by_contra hx1
    have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    have hy2 : y ^ 2 = 1 := hinv x y hxo (hcomm y hαy)
    have := orderOf_dvd_of_pow_eq_one hy2
    rw [hy] at this
    omega
  ext w
  rw [hx w, hx1]
  simp

section Odd

variable {K : Type} [Field K] [Finite K]

theorem ringEquiv_eq_refl_of_card_prime {q : ℕ} (hq : q.Prime) (hK : Nat.card K = q)
    (σ : K ≃+* K) : σ = RingEquiv.refl K := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = q := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K q := charP_of_card_eq_prime hcard
  let f : ZMod q →+* K := ZMod.castHom (dvd_refl q) K
  have hf : Function.Bijective f := by
    refine (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, ?_⟩
    rw [ZMod.card, hcard]
  have hσf : σ.toRingHom.comp f = f := RingHom.ext_zmod _ _
  ext a
  obtain ⟨b, rfl⟩ := hf.2 a
  exact DFunLike.congr_fun hσf b

theorem exists_pgl2_of_card_prime {q : ℕ} (hq : q.Prime) (hK : Nat.card K = q)
    (hKodd : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (α : MulAut (PSL2 K)) :
    ∃ a : PGL2 K, pgl2InnerAutPSL2 K hKodd hcard a = α := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective K (p := q) (f := 1) (by rw [hK, pow_one])
    hKodd hcard α
  refine ⟨x.left, ?_⟩
  rw [← hx]
  conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
  rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr,
    ringEquiv_eq_refl_of_card_prime hq hK x.right]
  have h1 : psl2FieldAut K (RingEquiv.refl K) = 1 := map_one (psl2FieldAut K)
  rw [h1, mul_one]

theorem commute_of_pgl2InnerAutPSL2_apply_eq (hKodd : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {a : PGL2 K} {v : PSL2 K}
    (h : pgl2InnerAutPSL2 K hKodd hcard a v = v) :
    a * Matrix.ProjectiveSpecialLinearGroup.toPGL v =
      Matrix.ProjectiveSpecialLinearGroup.toPGL v * a := by
  have h2 := toPGL_pgl2InnerAutPSL2_apply K hKodd hcard a v
  rw [h] at h2
  calc a * Matrix.ProjectiveSpecialLinearGroup.toPGL v =
      (a * Matrix.ProjectiveSpecialLinearGroup.toPGL v * a⁻¹) * a := by group
    _ = Matrix.ProjectiveSpecialLinearGroup.toPGL v * a := by rw [← h2]

theorem mem_klein_of_pgl2
    (hKodd : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (P : Sylow 2 (PSL2 K)) {a b c : PGL2 K}
    (ha : ∀ v ∈ (P : Subgroup (PSL2 K)), pgl2InnerAutPSL2 K hKodd hcard a v = v)
    (hb : ∀ v ∈ (P : Subgroup (PSL2 K)), pgl2InnerAutPSL2 K hKodd hcard b v = v)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hcomm : a * b = b * a) (ha2 : a * a = 1)
    (hb2 : b * b = 1) (hca : c * a = a * c) (hcb : c * b = b * c) :
    c = 1 ∨ c = a ∨ c = b ∨ c = a * b := by
  classical
  have hdih := psl2_odd_hasDihedralSylowTwo_model K hKodd
  obtain ⟨m, hm, ⟨eP⟩⟩ := hdih P
  obtain ⟨V, hVP, hV⟩ :=
    exists_kleinFour_le_of_dihedral_subgroup_mulEquiv (P : Subgroup (PSL2 K)) hm eP
  let toPGL : PSL2 K →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  let V' : Subgroup (PGL2 K) := V.map toPGL
  have hV' : IsKleinFour V' := isKleinFour_map_of_injective V hV toPGL htoPGL
  have hC := pgl2_kleinFour_centralizer_eq_self K hKodd V' hV'
  have hmem : ∀ d : PGL2 K, (∀ v ∈ (P : Subgroup (PSL2 K)),
      pgl2InnerAutPSL2 K hKodd hcard d v = v) → d ∈ V' := by
    intro d hd
    rw [← hC, Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    exact (commute_of_pgl2InnerAutPSL2_apply_eq hKodd hcard (hd v (hVP hv))).symm
  have haV := hmem a ha
  have hbV := hmem b hb
  have hab1 : a * b ≠ 1 := by
    intro h1
    apply hab
    calc a = a * (b * b) := by rw [hb2, mul_one]
      _ = (a * b) * b := by group
      _ = b := by rw [h1, one_mul]
  have haba : a * b ≠ a := fun h1 => hb1 (by simpa using h1)
  have habb : a * b ≠ b := fun h1 => ha1 (by simpa using h1)
  let F : Finset (PGL2 K) := {1, a, b, a * b}
  have hFcard : F.card = 4 := by
    simp only [F]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair habb.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, fun h1 => haba h1.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h1 => ha1 h1.symm, fun h1 => hb1 h1.symm, fun h1 => hab1 h1.symm⟩
  have hFV : ∀ d ∈ F, d ∈ V' := by
    intro d hd
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact V'.one_mem
    · exact haV
    · exact hbV
    · exact V'.mul_mem haV hbV
  have hVF : ∀ d ∈ V', d ∈ F := by
    have hfin : Finite V' := Nat.finite_of_card_ne_zero (by rw [hV'.card_four]; norm_num)
    have : Fintype V' := Fintype.ofFinite V'
    let F' : Finset V' := F.subtype (· ∈ V')
    have hF' : F'.card = 4 := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem hFV, hFcard]
    have huniv : F' = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hF', ← Nat.card_eq_fintype_card, hV'.card_four]
    intro d hd
    have : (⟨d, hd⟩ : V') ∈ F' := by rw [huniv]; exact Finset.mem_univ _
    simpa [F'] using this
  have hcV : c ∈ V' := by
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro d hd
    have hdF := hVF d hd
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hdF
    rcases hdF with rfl | rfl | rfl | rfl
    · group
    · exact hca.symm
    · exact hcb.symm
    · calc a * b * c = a * (b * c) := by group
        _ = a * (c * b) := by rw [hcb]
        _ = (a * c) * b := by group
        _ = (c * a) * b := by rw [hca]
        _ = c * (a * b) := by group
  have := hVF c hcV
  simpa [F] using this

end Odd

theorem mem_klein_of_fix_sylow_of_statedPSL_two_odd
    {X : Type} [Group X] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (h : StatedClassicalModel X .PSL 2 q 1) {S : Subgroup X}
    (hS : quasithinIsSylowTwo S) (α β γ : MulAut X) (hα : ∀ s ∈ S, α s = s)
    (hβ : ∀ s ∈ S, β s = s) (hα1 : α ≠ 1) (hβ1 : β ≠ 1) (hαβ : α ≠ β) (hcomm : α * β = β * α)
    (hα2 : α * α = 1) (hβ2 : β * β = 1) (hγα : γ * α = α * γ) (hγβ : γ * β = β * γ) :
    γ = 1 ∨ γ = α ∨ γ = β ∨ γ = α * β := by
  obtain ⟨⟨-, -, -, -, h23⟩, K, _, _, hK, ⟨e⟩⟩ := h
  rw [pow_one] at hK
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hKodd : IsOddPrimePower (Nat.card K) := ⟨q, 1, hq, hqodd, le_rfl, by rw [hK, pow_one]⟩
  have hcard : 3 < Nat.card K := by
    rw [hK]
    have h3 : q ≠ 3 := fun h3 => h23 (by rw [h3, pow_one])
    have := hq.two_le
    obtain ⟨k, hk⟩ := hqodd
    omega
  let e' : X ≃* PSL2 K := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  let C : MulAut X ≃* MulAut (PSL2 K) := MulAut.congr e'
  let ι := pgl2InnerAutPSL2 K hKodd hcard
  have hι : Function.Injective ι := pgl2InnerAutPSL2_injective K hKodd hcard
  obtain ⟨a, ha⟩ := exists_pgl2_of_card_prime hq hK hKodd hcard (C α)
  obtain ⟨b, hb⟩ := exists_pgl2_of_card_prime hq hK hKodd hcard (C β)
  obtain ⟨c, hc⟩ := exists_pgl2_of_card_prime hq hK hKodd hcard (C γ)
  have hfinX : Finite X := Finite.of_equiv _ e'.symm.toEquiv
  obtain ⟨P, hP⟩ := exists_sylow_eq (quasithinIsSylowTwo_map e' hS)
  have hfix : ∀ φ : MulAut X, (∀ s ∈ S, φ s = s) → ∀ v ∈ (P : Subgroup (PSL2 K)), C φ v = v := by
    intro φ hφ v hv
    rw [hP] at hv
    obtain ⟨s, hs, rfl⟩ := hv
    change e' (φ (e'.symm (e' s))) = e' s
    rw [MulEquiv.symm_apply_apply, hφ s hs]
  have hinj : ∀ {φ ψ : MulAut X} {d f : PGL2 K}, ι d = C φ → ι f = C ψ → (d = f ↔ φ = ψ) := by
    intro φ ψ d f hd hf
    constructor
    · rintro rfl
      exact C.injective (hd.symm.trans hf)
    · rintro rfl
      exact hι (hd.trans hf.symm)
  have hmul : ∀ {φ ψ : MulAut X} {d f : PGL2 K}, ι d = C φ → ι f = C ψ → ι (d * f) = C (φ * ψ) := by
    intro φ ψ d f hd hf
    rw [map_mul, map_mul, hd, hf]
  have h1 : ι 1 = C 1 := by rw [map_one, map_one]
  have key := mem_klein_of_pgl2 hKodd hcard P (a := a) (b := b) (c := c)
    (fun v hv => by rw [ha]; exact hfix α hα v hv) (fun v hv => by rw [hb]; exact hfix β hβ v hv)
    (fun h0 => hα1 ((hinj ha h1).mp h0)) (fun h0 => hβ1 ((hinj hb h1).mp h0))
    (fun h0 => hαβ ((hinj ha hb).mp h0))
    ((hinj (hmul ha hb) (hmul hb ha)).mpr hcomm) ((hinj (hmul ha ha) h1).mpr hα2)
    ((hinj (hmul hb hb) h1).mpr hβ2) ((hinj (hmul hc ha) (hmul ha hc)).mpr hγα)
    ((hinj (hmul hc hb) (hmul hb hc)).mpr hγβ)
  rcases key with h0 | h0 | h0 | h0
  · exact Or.inl ((hinj hc h1).mp h0)
  · exact Or.inr (Or.inl ((hinj hc ha).mp h0))
  · exact Or.inr (Or.inr (Or.inl ((hinj hc hb).mp h0)))
  · exact Or.inr (Or.inr (Or.inr ((hinj hc (hmul ha hb)).mp h0)))

end CFSG.Quasithin.F420
