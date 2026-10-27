module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Xb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoKer
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_eps_mul {V₀ : Subgroup G} {z a b : G}
    (ha : a ∈ normalizer (V₀ : Set G)) (hb : b ∈ normalizer (V₀ : Set G))
    (ha' : a * z * a⁻¹ * z⁻¹ ∈ V₀) (hb' : b * z * b⁻¹ * z⁻¹ ∈ V₀) :
    a * b * z * (a * b)⁻¹ * z⁻¹ ∈ V₀ := by
  have h1 : a * b * z * (a * b)⁻¹ * z⁻¹ =
      (a * (b * z * b⁻¹ * z⁻¹) * a⁻¹) * (a * z * a⁻¹ * z⁻¹) := by group
  rw [h1]
  exact V₀.mul_mem ((Subgroup.mem_normalizer_iff.1 ha _).1 hb') ha'

private theorem c23ne_eps_inv {V₀ : Subgroup G} {z a : G}
    (ha : a ∈ normalizer (V₀ : Set G)) (ha' : a * z * a⁻¹ * z⁻¹ ∈ V₀) :
    a⁻¹ * z * (a⁻¹)⁻¹ * z⁻¹ ∈ V₀ := by
  have h1 : a⁻¹ * z * (a⁻¹)⁻¹ * z⁻¹ = a⁻¹ * (a * z * a⁻¹ * z⁻¹)⁻¹ * a := by group
  rw [h1]
  simpa using (Subgroup.mem_normalizer_iff.1 ((normalizer (V₀ : Set G)).inv_mem ha) _).1
    (V₀.inv_mem ha')

theorem c23ne_exists_X_cover {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) (hMs : D.M ≤ stabTil V₀ V) :
    ∃ (z : IntMod V hV) (X : Subgroup G),
      mkTil V₀ V hV z ∈ c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)) ∧
      (∀ t ∈ D.T, t * z.val * t⁻¹ * (z.val)⁻¹ ∈ V₀) ∧
      (∀ g ∈ X, g * z.val = z.val * g) ∧
      CFSG.ABGLocalTools.IsSylowOf 3 X (K₁ ⊔ K₂) ∧
      (∀ n ∈ (K₁ ⊔ K₂) ⊓ normalizer (X : Set G), n * z.val * n⁻¹ * (z.val)⁻¹ ∈ V₀) ∧
      ∀ j ∈ K₁ ⊔ K₂, j * z.val * j⁻¹ * (z.val)⁻¹ ∈ V₀ → ∃ g ∈ X, ∃ t ∈ D.T, j = g * t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK₁M : K₁ ≤ D.M := uc22p22a_le_of_isSubnormal hctx.mem₁.1
  have hK₂M : K₂ ≤ D.M := uc22p22a_le_of_isSubnormal hctx.mem₂.1
  have h𝓛M : K₁ ⊔ K₂ ≤ D.M := sup_le hK₁M hK₂M
  have h𝓛s : K₁ ⊔ K₂ ≤ stabTil V₀ V := h𝓛M.trans hMs
  have hTs : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMs
  have hbarA : barSub V₀ V hV (K₁ ⊔ K₂) =
      barSub V₀ V hV L ⊔ barSub V₀ V hV (conjSubgroup L x) := by
    rw [s16c7_barSub_sup V₀ V hV (hK₁M.trans hMs) (hK₂M.trans hMs), hctx.bar₁, hctx.bar₂]
  have hQ2M : c23neQ2 K₁ K₂ ≤ D.M := by
    rw [← hctx.ker]
    exact inf_le_right.trans h𝓛M
  have hQ2norm : ∀ m ∈ D.M, ∀ y ∈ c23neQ2 K₁ K₂, m * y * m⁻¹ ∈ c23neQ2 K₁ K₂ := by
    intro m hm y hy
    have hCTnorm : D.M ≤ normalizer (F11.CTilde D.M V₀ V : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (WeakClosure81.cTilde_le_M D.M V₀ V)).1
        (WeakClosure81.cTilde_subgroupOf_normal hV
          (hMs.trans (stabTil_le_normalizer V₀ V))
          (hMs.trans (stabTil_le_normalizer₀ V₀ V)))
    have hy' : y ∈ F11.CTilde D.M V₀ V ⊓ (K₁ ⊔ K₂) := by rwa [hctx.ker]
    obtain ⟨hyC, hyL⟩ := Subgroup.mem_inf.1 hy'
    have h1 : m * y * m⁻¹ ∈ F11.CTilde D.M V₀ V :=
      (Subgroup.mem_normalizer_iff.1 (hCTnorm hm) y).1 hyC
    have h2 : m * y * m⁻¹ ∈ K₁ ⊔ K₂ :=
      (Subgroup.mem_normalizer_iff.1 (c23ne_M_le_normalizer_sup hctx hm) y).1 hyL
    rw [← hctx.ker]
    exact Subgroup.mem_inf.2 ⟨h1, h2⟩
  have hNT : c23neQ2 K₁ K₂ ≤ D.T :=
    (s16c7_le_pCoreOf hQ2M hQ2norm hctx.q2_pgroup).trans
      (s16c7_pCoreOf_le_of_isSylowOf D.sylowM)
  have h4 : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂) :=
    D.sylowM.inf_of_le_normalizer h𝓛M (c23ne_M_le_normalizer_sup hctx)
  have h5 := s16c7_isSylowOf_barSub V₀ V hV h4 h𝓛s
  have hTbar : IsPGroup 2 (barSub V₀ V hV D.T) := by
    have h0 : IsPGroup 2 (D.T.subgroupOf (stabTil V₀ V)) := D.sylowM.isPGroup.comap_subtype
    exact h0.map (actTil V₀ V hV)
  have hS : CFSG.ABGLocalTools.IsSylowOf 2
      (barSub V₀ V hV (D.T ⊓ (K₁ ⊔ K₂)))
      (barSub V₀ V hV L ⊔ barSub V₀ V hV (conjSubgroup L x)) := by
    rw [← hbarA]
    exact h5
  have hTb : barSub V₀ V hV D.T ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV D.sylowM.le
  obtain ⟨u₀, hΩ, hfixT⟩ := c23_exists_fixed_omega hctx.core hTb hTbar
  have hSfix : ∀ s ∈ barSub V₀ V hV (D.T ⊓ (K₁ ⊔ K₂)), s u₀ = u₀ :=
    fun s hs => hfixT s (barSub_mono V₀ V hV inf_le_left hs)
  obtain ⟨Xb, hXbA, hXb9, hXbfix, hXbcov⟩ := c23_exists_fixed_sylow hctx.core hΩ hS hSfix
  have hXbp : IsPGroup 3 Xb := IsPGroup.of_card (n := 2) (by rw [hXb9]; norm_num)
  have hSyl3 : CFSG.ABGLocalTools.IsSylowOf 3 Xb (barSub V₀ V hV (K₁ ⊔ K₂)) := by
    rw [hbarA, CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hXbA, hXbp, ?_⟩
    have e := Subgroup.relIndex_mul_card (H := Xb)
      (K := barSub V₀ V hV L ⊔ barSub V₀ V hV (conjSubgroup L x))
    rw [inf_eq_left.2 hXbA, hXb9, c23_core_card_sup hctx.core] at e
    have hr : Xb.relIndex (barSub V₀ V hV L ⊔ barSub V₀ V hV (conjSubgroup L x)) = 3136 := by
      omega
    rw [hr]
    norm_num
  obtain ⟨X, hXsyl, hXb⟩ := s16c7_exists_lift_sylow (p := 3) V₀ V hV h𝓛s hSyl3
  have hXs : X ≤ stabTil V₀ V := hXsyl.le.trans h𝓛s
  obtain ⟨z, rfl⟩ := mkTil_surjective V₀ V hV u₀
  refine ⟨z, X, hΩ, ?_, ?_, hXsyl, ?_, ?_⟩
  ·
    intro t ht
    have hts : t ∈ stabTil V₀ V := hTs ht
    have h1 : actTil V₀ V hV ⟨t, hts⟩ (mkTil V₀ V hV z) = mkTil V₀ V hV z :=
      hfixT _ (actTil_mem_barSub V₀ V hV ht hts)
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
    exact h1
  ·
    intro g hg
    have hgs : g ∈ stabTil V₀ V := hXs hg
    have hε₀ : ∀ b ∈ X, b * z.val * b⁻¹ * (z.val)⁻¹ ∈ V₀ := by
      intro b hb
      have hbs : b ∈ stabTil V₀ V := hXs hb
      have hfix : actTil V₀ V hV ⟨b, hbs⟩ (mkTil V₀ V hV z) = mkTil V₀ V hV z :=
        hXbfix _ (by rw [← hXb]; exact actTil_mem_barSub V₀ V hV hb hbs)
      rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix
      exact hfix
    have hεV : ∀ b ∈ X, b * z.val * b⁻¹ * (z.val)⁻¹ ∈ V := by
      intro b hb
      have hbs : b ∈ stabTil V₀ V := hXs hb
      have hbn : b * z.val * b⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 hbs.1 z.val).1 z.val_mem
      exact V.mul_mem hbn (V.inv_mem z.val_mem)
    have hanti : ∀ a ∈ X, ∀ b ∈ X,
        (a * b) * z.val * (a * b)⁻¹ * (z.val)⁻¹ =
          (b * z.val * b⁻¹ * (z.val)⁻¹) * (a * z.val * a⁻¹ * (z.val)⁻¹) := by
      intro a ha b hb
      have hacent : a * (b * z.val * b⁻¹ * (z.val)⁻¹) * a⁻¹ =
          b * z.val * b⁻¹ * (z.val)⁻¹ := by
        have hc := (Subgroup.mem_centralizer_iff.1 (hctx.cent₀ (hXsyl.le ha)) _
          (hε₀ b hb)).symm
        calc a * (b * z.val * b⁻¹ * (z.val)⁻¹) * a⁻¹
            = ((b * z.val * b⁻¹ * (z.val)⁻¹) * a) * a⁻¹ := by rw [hc]
          _ = b * z.val * b⁻¹ * (z.val)⁻¹ := by group
      calc (a * b) * z.val * (a * b)⁻¹ * (z.val)⁻¹
          = a * (b * z.val * b⁻¹) * a⁻¹ * (z.val)⁻¹ := by group
        _ = (a * (b * z.val * b⁻¹ * (z.val)⁻¹) * a⁻¹) * (a * z.val * a⁻¹) *
              (z.val)⁻¹ := by group
        _ = (b * z.val * b⁻¹ * (z.val)⁻¹) * (a * z.val * a⁻¹) * (z.val)⁻¹ := by rw [hacent]
        _ = (b * z.val * b⁻¹ * (z.val)⁻¹) * (a * z.val * a⁻¹ * (z.val)⁻¹) := by group
    have hpow : ∀ b ∈ X, ∀ n : ℕ,
        (b ^ n) * z.val * (b ^ n)⁻¹ * (z.val)⁻¹ =
          (b * z.val * b⁻¹ * (z.val)⁻¹) ^ n := by
      intro b hb n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, hanti (b ^ n) (X.pow_mem hb n) b hb, ih, pow_succ']
    obtain ⟨k, hk⟩ := hXsyl.isPGroup ⟨g, hg⟩
    have hgk : g ^ (3 ^ k) = 1 := by
      have h := congrArg Subtype.val hk
      simpa using h
    have hεpow : (g * z.val * g⁻¹ * (z.val)⁻¹) ^ (3 ^ k) = 1 := by
      have h1 := hpow g hg (3 ^ k)
      rw [hgk] at h1
      simpa using h1.symm
    have hε2 : (g * z.val * g⁻¹ * (z.val)⁻¹) ^ 2 = 1 :=
      hV.2 _ (hεV g hg)
    have hord : orderOf (g * z.val * g⁻¹ * (z.val)⁻¹) = 1 :=
      Nat.eq_one_of_dvd_coprimes ((by norm_num : Nat.Coprime 2 3).pow_right k)
        (orderOf_dvd_of_pow_eq_one hε2) (orderOf_dvd_of_pow_eq_one hεpow)
    have hε1 : g * z.val * g⁻¹ * (z.val)⁻¹ = 1 := orderOf_eq_one_iff.mp hord
    have hgz : g * z.val * g⁻¹ = z.val := mul_inv_eq_one.1 hε1
    calc g * z.val = (g * z.val * g⁻¹) * g := by group
      _ = z.val * g := by rw [hgz]
  ·
    intro n hn
    obtain ⟨hnL, hnN⟩ := Subgroup.mem_inf.1 hn
    have hns : n ∈ stabTil V₀ V := h𝓛s hnL
    have hnXmap : X.map (MulAut.conj n).toMonoidHom = X := by
      simpa using Subgroup.mem_normalizer_iff_map_conj_eq.1 hnN
    have hconj := s16c7_barSub_map_conj V₀ V hV hns X
    rw [hnXmap, hXb] at hconj
    have hnbN : actTil V₀ V hV ⟨n, hns⟩ ∈
        normalizer (Xb : Set (MulAut (Vtil V₀ V hV))) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      simpa using hconj.symm
    have hnbM : actTil V₀ V hV ⟨n, hns⟩ ∈ Mbar D.M V₀ V hV :=
      actTil_mem_barSub V₀ V hV (h𝓛M hnL) hns
    have h1 : actTil V₀ V hV ⟨n, hns⟩ (mkTil V₀ V hV z) = mkTil V₀ V hV z :=
      c23_fixed_of_mem_normalizer hctx.core hXbA hXb9 hΩ hXbfix hnbM hnbN
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
    exact h1
  ·
    intro j hj hjz
    have hjs : j ∈ stabTil V₀ V := h𝓛s hj
    have hjb : actTil V₀ V hV ⟨j, hjs⟩ ∈ barSub V₀ V hV (K₁ ⊔ K₂) :=
      actTil_mem_barSub V₀ V hV hj hjs
    have hjfix : actTil V₀ V hV ⟨j, hjs⟩ (mkTil V₀ V hV z) = mkTil V₀ V hV z := by
      rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
      exact hjz
    rw [hbarA] at hjb
    obtain ⟨xb, hxb, tb, htb, hxt⟩ := hXbcov _ hjb hjfix
    rw [← hXb] at hxb
    obtain ⟨xx, hxX, rfl⟩ := (mem_barSub V₀ V hV X xb).1 hxb
    obtain ⟨s, hsTL, rfl⟩ := (mem_barSub V₀ V hV (D.T ⊓ (K₁ ⊔ K₂)) tb).1 htb
    have hxL : (xx : G) ∈ K₁ ⊔ K₂ := hXsyl.le hxX
    have hsL : (s : G) ∈ K₁ ⊔ K₂ := (Subgroup.mem_inf.1 hsTL).2
    have hsT : (s : G) ∈ D.T := (Subgroup.mem_inf.1 hsTL).1
    set q : stabTil V₀ V := (xx * s)⁻¹ * ⟨j, hjs⟩ with hqdef
    have hqG : (q : G) = ((xx : G) * (s : G))⁻¹ * j := by simp [hqdef]
    have hqL : (q : G) ∈ K₁ ⊔ K₂ := by
      rw [hqG]
      exact (K₁ ⊔ K₂).mul_mem ((K₁ ⊔ K₂).inv_mem ((K₁ ⊔ K₂).mul_mem hxL hsL)) hj
    have hqM : (q : G) ∈ D.M := h𝓛M hqL
    have hker : actTil V₀ V hV q = 1 := by
      rw [hqdef, map_mul, map_inv, map_mul, hxt]
      simp
    have hqC : (q : G) ∈ F11.CTilde D.M V₀ V :=
      (mem_cTilde_iff hV (hMs.trans (stabTil_le_normalizer V₀ V))).2
        ⟨hqM, q.2, hker⟩
    have hqQ2 : (q : G) ∈ c23neQ2 K₁ K₂ := by
      rw [← hctx.ker]
      exact ⟨hqC, hqL⟩
    have hqT : (q : G) ∈ D.T := hNT hqQ2
    refine ⟨(xx : G), hxX, (s : G) * (q : G), D.T.mul_mem hsT hqT, ?_⟩
    show j = (xx : G) * ((s : G) * (q : G))
    rw [hqG]
    group

theorem c23ne_permutes_of_cover {X T L V₀ : Subgroup G} {z : G} (hXL : X ≤ L)
    (hTL : T ≤ normalizer (L : Set G)) (hL₀ : L ≤ normalizer (V₀ : Set G))
    (hT₀ : T ≤ normalizer (V₀ : Set G)) (hTz : ∀ t ∈ T, t * z * t⁻¹ * z⁻¹ ∈ V₀)
    (hXz : ∀ g ∈ X, g * z * g⁻¹ * z⁻¹ ∈ V₀)
    (hcov : ∀ j ∈ L, j * z * j⁻¹ * z⁻¹ ∈ V₀ → ∃ g ∈ X, ∃ t ∈ T, j = g * t) :
    Permutes X T := by
  have key : ∀ x ∈ X, ∀ t ∈ T, ∃ x' ∈ X, ∃ t' ∈ T, t * x = x' * t' := by
    intro x hx t ht
    have hxN : x ∈ normalizer (V₀ : Set G) := hL₀ (hXL hx)
    have htN : t ∈ normalizer (V₀ : Set G) := hT₀ ht
    have htinvN : t⁻¹ ∈ normalizer (V₀ : Set G) := (normalizer (V₀ : Set G)).inv_mem htN
    have htxN : t * x ∈ normalizer (V₀ : Set G) := (normalizer (V₀ : Set G)).mul_mem htN hxN
    have hεtx : (t * x) * z * (t * x)⁻¹ * z⁻¹ ∈ V₀ :=
      c23ne_eps_mul htN hxN (hTz t ht) (hXz x hx)
    have hεtinv : t⁻¹ * z * (t⁻¹)⁻¹ * z⁻¹ ∈ V₀ := c23ne_eps_inv htN (hTz t ht)
    have hεj : (t * x * t⁻¹) * z * (t * x * t⁻¹)⁻¹ * z⁻¹ ∈ V₀ :=
      c23ne_eps_mul htxN htinvN hεtx hεtinv
    have hjL : t * x * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hTL ht) x).1 (hXL hx)
    obtain ⟨x', hx', t', ht', hcov'⟩ := hcov _ hjL hεj
    refine ⟨x', hx', t' * t, T.mul_mem ht' ht, ?_⟩
    calc t * x = (t * x * t⁻¹) * t := by group
      _ = (x' * t') * t := by rw [hcov']
      _ = x' * (t' * t) := by group
  show (X : Set G) * (T : Set G) = (T : Set G) * (X : Set G)
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, t, ht, rfl⟩
    obtain ⟨x', hx', t', ht', h⟩ := key x⁻¹ (X.inv_mem hx) t⁻¹ (T.inv_mem ht)
    refine ⟨t'⁻¹, T.inv_mem ht', x'⁻¹, X.inv_mem hx', ?_⟩
    calc t'⁻¹ * x'⁻¹ = (x' * t')⁻¹ := by group
      _ = (t⁻¹ * x⁻¹)⁻¹ := by rw [h]
      _ = x * t := by group
  · rintro _ ⟨t, ht, x, hx, rfl⟩
    obtain ⟨x', hx', t', ht', h⟩ := key x hx t ht
    exact ⟨x', hx', t', ht', h.symm⟩

theorem c23ne_exists_X_z {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) (hMs : D.M ≤ stabTil V₀ V) :
    ∃ (z : IntMod V hV) (X : Subgroup G),
      mkTil V₀ V hV z ∈ c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)) ∧
      (∀ g ∈ X, g * z.val = z.val * g) ∧
      CFSG.ABGLocalTools.IsSylowOf 3 X (K₁ ⊔ K₂) ∧ Permutes X D.T ∧
      ∀ n ∈ (K₁ ⊔ K₂) ⊓ normalizer (X : Set G), n * z.val * n⁻¹ * (z.val)⁻¹ ∈ V₀ := by
  obtain ⟨z, X, hΩ, hzT, hzX, hXsyl, hzN, hcov⟩ := c23ne_exists_X_cover hctx hMs
  refine ⟨z, X, hΩ, hzX, hXsyl, ?_, hzN⟩
  refine c23ne_permutes_of_cover (V₀ := V₀) (z := z.val) hXsyl.le
    (D.sylowM.le.trans (c23ne_M_le_normalizer_sup hctx))
    (hctx.cent₀.trans (Subgroup.centralizer_le_normalizer _))
    (fun t ht => (hMs (D.sylowM.le ht)).2) hzT (fun g hg => ?_) hcov
  have h : g * z.val * g⁻¹ * (z.val)⁻¹ = 1 := by rw [hzX g hg]; group
  rw [h]
  exact V₀.one_mem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
