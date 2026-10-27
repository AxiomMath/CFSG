module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineNormFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineNormSum

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c167_norm_orbit_injective (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : IsPSL 3 2 1 ↥L) {V₀ : Subgroup W} (hV₀ : XMod.IsIrr ↥L V₀) (hc : Nat.card ↥V₀ = 8)
    {Z : Subgroup (MulAut W)} (hZ : Nat.card ↥Z = 7) (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z)
    (hnt : ∃ z ∈ Z, ∃ v ∈ V₀, z v ≠ v) :
    Function.Injective fun z : ↥Z => V₀.map (z : MulAut W).toMonoidHom := by
  intro z z' hzz'
  have hzz'' : V₀.map (z : MulAut W).toMonoidHom = V₀.map (z' : MulAut W).toMonoidHom := hzz'
  let g : MulAut W := (z' : MulAut W)⁻¹ * (z : MulAut W)
  have hgZ : g ∈ Z := Z.mul_mem (Z.inv_mem z'.2) z.2
  have hgL : ∀ l ∈ L, g * l = l * g := by
    intro l hl
    have hz'l : (z' : MulAut W) * l = l * (z' : MulAut W) := hZL z' z'.2 l hl
    have hzl : (z : MulAut W) * l = l * (z : MulAut W) := hZL z z.2 l hl
    have hz'inv : (z' : MulAut W)⁻¹ * l = l * (z' : MulAut W)⁻¹ := by
      calc (z' : MulAut W)⁻¹ * l
          = (z' : MulAut W)⁻¹ * l * ((z' : MulAut W) * (z' : MulAut W)⁻¹) := by simp
        _ = (z' : MulAut W)⁻¹ * (l * (z' : MulAut W)) * (z' : MulAut W)⁻¹ := by
              simp [mul_assoc]
        _ = (z' : MulAut W)⁻¹ * ((z' : MulAut W) * l) * (z' : MulAut W)⁻¹ := by rw [← hz'l]
        _ = l * (z' : MulAut W)⁻¹ := by simp [mul_assoc]
    calc g * l = (z' : MulAut W)⁻¹ * (z : MulAut W) * l := rfl
      _ = (z' : MulAut W)⁻¹ * ((z : MulAut W) * l) := by simp [mul_assoc]
      _ = (z' : MulAut W)⁻¹ * (l * (z : MulAut W)) := by rw [hzl]
      _ = ((z' : MulAut W)⁻¹ * l) * (z : MulAut W) := by simp [mul_assoc]
      _ = (l * (z' : MulAut W)⁻¹) * (z : MulAut W) := by rw [hz'inv]
      _ = l * g := by simp [g, mul_assoc]
  have hgmap : V₀.map g.toMonoidHom = V₀ := by
    have h1 : (V₀.map (z : MulAut W).toMonoidHom).map ((z' : MulAut W)⁻¹).toMonoidHom
        = (V₀.map (z' : MulAut W).toMonoidHom).map ((z' : MulAut W)⁻¹).toMonoidHom := by
      rw [hzz'']
    rw [Subgroup.map_map, Subgroup.map_map] at h1
    have hcomp : (((z' : MulAut W)⁻¹).toMonoidHom).comp (z' : MulAut W).toMonoidHom
        = MonoidHom.id W := by
      ext u
      show (z' : MulAut W)⁻¹ ((z' : MulAut W) u) = u
      rw [mulAut_inv_apply_apply]
    rw [hcomp, Subgroup.map_id] at h1
    have hg_hom : g.toMonoidHom
        = (((z' : MulAut W)⁻¹).toMonoidHom).comp (z : MulAut W).toMonoidHom := by
      ext u
      simp [g, MulAut.mul_apply]
    rw [hg_hom]
    exact h1
  have hgV : g ∈ stabSub V₀ := StabLat.mem_stabSub_of_map_eq hgmap
  have hfix : ∀ v ∈ V₀, g v = v :=
    s16c167_norm_fixes_of_commute hW hL hV₀ hc hgL hgV
  by_cases hg1 : g = 1
  · have h2 : (z : MulAut W) = (z' : MulAut W) := by
      conv_lhs => rw [← mul_inv_cancel_left (z' : MulAut W) (z : MulAut W)]
      rw [show (z' : MulAut W)⁻¹ * (z : MulAut W) = g from rfl, hg1, mul_one]
    exact Subtype.ext h2
  · exfalso
    obtain ⟨z₀, hz₀Z, v, hvV, hzv⟩ := hnt
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hgZ1 : (⟨g, hgZ⟩ : ↥Z) ≠ 1 := fun h => hg1 (Subtype.ext_iff.mp h)
    have htop : Subgroup.zpowers (⟨g, hgZ⟩ : ↥Z) = ⊤ :=
      zpowers_eq_top_of_prime_card hZ hgZ1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (show (⟨z₀, hz₀Z⟩ : ↥Z) ∈ Subgroup.zpowers (⟨g, hgZ⟩ : ↥Z) from by
        rw [htop]; trivial)
    have hn' : g ^ n = z₀ := by
      have h := congrArg Subtype.val hn
      simpa using h
    have hg_inv_fix : ∀ w ∈ V₀, g⁻¹ w = w := by
      intro w hw
      have h1 : g⁻¹ (g w) = w := mulAut_inv_apply_apply g w
      rwa [hfix w hw] at h1
    have hpow : ∀ m : ℤ, ∀ w ∈ V₀, (g ^ m) w = w := by
      intro m
      exact zpow_induction_right (g := g)
        (P := fun a : MulAut W => ∀ w ∈ V₀, a w = w)
        (fun w _ => by simp)
        (fun a ha w hw => by
          show (a * g) w = w
          rw [MulAut.mul_apply, hfix w hw, ha w hw])
        (fun a ha w hw => by
          show (a * g⁻¹) w = w
          rw [MulAut.mul_apply, hg_inv_fix w hw, ha w hw]) m
    exact hzv (by rw [← hn']; exact hpow n v hvV)

theorem s16c167_norm_card_irr_natSum3 (hW : ∀ w : W, w ^ 2 = 1) {L Z : Subgroup (MulAut W)}
    (hL : IsPSL 3 2 1 ↥L) {J : Subgroup W} (hJ : NatSum3 L J) (hZ : Nat.card ↥Z = 7)
    (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z) (hZJ : ∀ z ∈ Z, ∀ w ∈ J, z w ∈ J)
    (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ J, z w ≠ w) {P : Subgroup (MulAut W)} (hPL : P ≤ L)
    (hP : Nat.card ↥P = 8) :
    Nat.card ↥(J ⊓ fixV P) = 8 ∧
      Nat.card {V : Subgroup W // V ≤ J ∧ XMod.IsIrr ↥L V ∧ Nat.card ↥V = 8} = 7 := by
  classical
  let X := {V : Subgroup W // V ≤ J ∧ XMod.IsIrr ↥L V ∧ Nat.card ↥V = 8}
  let A : Subgroup W := J ⊓ fixV P
  have h2 : ∀ V : Subgroup W, XMod.IsIrr ↥L V → Nat.card ↥V = 8 →
      Nat.card ↥(V ⊓ fixV P) ≤ 2 := by
    intro V hV hcV
    exact s16c167_norm_card_inf_fixV_le_two hW hcV hP
      (fun g hg v hv => hV.1 ⟨g, hPL hg⟩ v hv)
      (fun g hg hfix => rank3_inj hL (fun x hx v hv => hV.1 ⟨x, hx⟩ v hv)
        (s16c167_norm_irr_nontrivial hV hcV) g (hPL hg) hfix)
  have hAle : Nat.card ↥A ≤ 8 := s16c167_norm_card_fixV_natSum3_le hW hJ hPL h2
  have hexists : ∀ V : X, ∃ m : W, m ∈ V.1 ⊓ fixV P ∧ m ≠ 1 := by
    intro V
    obtain ⟨hVJ, hVirr, hVcard⟩ := V.2
    have hcard2 : Nat.card ↥(V.1 ⊓ fixV P) = 2 :=
      s16c167_norm_card_inf_fixV_eq_two hW hVcard hP
        (fun g hg v hv => hVirr.1 ⟨g, hPL hg⟩ v hv)
        (fun g hg hfix => rank3_inj hL (fun x hx v hv => hVirr.1 ⟨x, hx⟩ v hv)
          (s16c167_norm_irr_nontrivial hVirr hVcard) g (hPL hg) hfix)
    have hnebot : V.1 ⊓ fixV P ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hcard2
      omega
    obtain ⟨m, hm⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hnebot
    exact ⟨(m : W), m.2, fun h => hm (Subtype.ext h)⟩
  let φ : X → {a : ↥A // a ≠ 1} := fun V =>
    ⟨⟨Classical.choose (hexists V),
       V.2.1 ((inf_le_left : V.1 ⊓ fixV P ≤ V.1) (Classical.choose_spec (hexists V)).1),
       (inf_le_right : V.1 ⊓ fixV P ≤ fixV P) (Classical.choose_spec (hexists V)).1⟩,
     fun h => (Classical.choose_spec (hexists V)).2 (Subtype.ext_iff.mp h)⟩
  have hφinj : Function.Injective φ := by
    intro V V' hVV'
    have hmeq : Classical.choose (hexists V) = Classical.choose (hexists V') := by
      have h := congrArg (fun t : {a : ↥A // a ≠ 1} => ((t : ↥A) : W)) hVV'
      exact h
    have hmV : Classical.choose (hexists V) ∈ V.1 :=
      (inf_le_left : V.1 ⊓ fixV P ≤ V.1) (Classical.choose_spec (hexists V)).1
    have hmV' : Classical.choose (hexists V) ∈ V'.1 := by
      rw [hmeq]
      exact (inf_le_left : V'.1 ⊓ fixV P ≤ V'.1) (Classical.choose_spec (hexists V')).1
    have hne1 : Classical.choose (hexists V) ≠ 1 := (Classical.choose_spec (hexists V)).2
    have hinv : XMod.IsInv ↥L (V.1 ⊓ V'.1) := V.2.2.1.1.inf V'.2.2.1.1
    have hmInf : Classical.choose (hexists V) ∈ V.1 ⊓ V'.1 := ⟨hmV, hmV'⟩
    rcases V.2.2.1.2.2 (V.1 ⊓ V'.1) hinv bot_le inf_le_left with hbot | htop
    · exfalso
      rw [hbot, Subgroup.mem_bot] at hmInf
      exact hne1 hmInf
    · have hle : V.1 ≤ V'.1 := inf_eq_left.mp htop
      have hcardeq : Nat.card ↥V'.1 = Nat.card ↥V.1 := by rw [V.2.2.2, V'.2.2.2]
      exact Subtype.ext (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardeq))
  haveI : Finite X := Finite.of_injective φ hφinj
  have hXle : Nat.card X ≤ Nat.card {a : ↥A // a ≠ 1} :=
    Nat.card_le_card_of_injective φ hφinj
  have hsub_lt : Nat.card {a : ↥A // a ≠ 1} < Nat.card ↥A :=
    Finite.card_subtype_lt (p := fun a : ↥A => a ≠ 1) (x := 1) (by simp)
  have hXle7 : Nat.card X ≤ 7 := by omega
  obtain ⟨V₀, hV₀J, hV₀irr, hV₀card, hnt₀⟩ :=
    s16c167_norm_exists_summand_nontrivial hJ hZ hZf
  have hnorm : ∀ z : ↥Z, (z : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
    intro z
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext u
    constructor
    · intro hu
      obtain ⟨l, hl, hl_eq⟩ := Subgroup.mem_map.mp hu
      have h2 : (MulAut.conj (z : MulAut W)) l = l := by
        rw [MulAut.conj_apply, hZL z z.2 l hl]
        simp [mul_assoc]
      rw [← hl_eq]
      change (MulAut.conj (z : MulAut W)) l ∈ L
      rw [h2]
      exact hl
    · intro hu
      have h1 : (MulAut.conj (z : MulAut W)) u = u := by
        rw [MulAut.conj_apply, hZL z z.2 u hu]
        simp [mul_assoc]
      change u ∈ L.map (MulAut.conj (z : MulAut W)).toMonoidHom
      rw [← h1]
      exact Subgroup.mem_map_of_mem (MulAut.conj (z : MulAut W)).toMonoidHom hu
  let f : ↥Z → X := fun z =>
    ⟨V₀.map (z : MulAut W).toMonoidHom,
      (Subgroup.map_le_iff_le_comap).mpr (fun v hv => hZJ z z.2 v (hV₀J hv)),
      isIrr_map (hnorm z) hV₀irr,
      by rw [Subgroup.card_map_of_injective (z : MulAut W).injective, hV₀card]⟩
  have hfinj : Function.Injective f := by
    intro z z' hzz
    apply s16c167_norm_orbit_injective hW hL hV₀irr hV₀card hZ hZL hnt₀
    exact congrArg Subtype.val hzz
  have hZle : Nat.card ↥Z ≤ Nat.card X := Nat.card_le_card_of_injective f hfinj
  have h7le : 7 ≤ Nat.card X := by rw [hZ] at hZle; exact hZle
  have h7le' : 7 ≤ Nat.card {V : Subgroup W // V ≤ J ∧ XMod.IsIrr ↥L V ∧ Nat.card ↥V = 8} :=
    h7le
  refine ⟨?_, ?_⟩
  · change Nat.card ↥A = 8
    omega
  · change Nat.card X = 7
    omega

theorem s16c167_norm_exists_stable_irr (hW : ∀ w : W, w ^ 2 = 1) {L Z : Subgroup (MulAut W)}
    (hL : IsPSL 3 2 1 ↥L) {J : Subgroup W} (hJ : NatSum3 L J) (hZ : Nat.card ↥Z = 7)
    (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z) (hZJ : ∀ z ∈ Z, ∀ w ∈ J, z w ∈ J)
    (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ J, z w ≠ w) {x : MulAut W} {k : ℕ} (hx : x ^ 2 ^ k = 1)
    (hxL : L.map (MulAut.conj x).toMonoidHom = L) (hxJ : J.map x.toMonoidHom = J) :
    ∃ V : Subgroup W, V ≤ J ∧ XMod.IsIrr ↥L V ∧ Nat.card ↥V = 8 ∧ V.map x.toMonoidHom = V := by
  classical
  obtain ⟨P, hPL, hP⟩ := s16c167_norm_exists_subgroup_card_eight hL
  obtain ⟨-, hXcard⟩ := s16c167_norm_card_irr_natSum3 hW hL hJ hZ hZL hZJ hZf hPL hP
  let X := {V : Subgroup W // V ≤ J ∧ XMod.IsIrr ↥L V ∧ Nat.card ↥V = 8}
  have hX7 : Nat.card X = 7 := hXcard
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hX7]; norm_num)
  have hxnorm : x ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hxL
  let f : X → X := fun V =>
    ⟨V.1.map x.toMonoidHom,
      (Subgroup.map_mono (f := x.toMonoidHom) V.2.1).trans (le_of_eq hxJ),
      isIrr_map hxnorm V.2.2.1,
      by rw [Subgroup.card_map_of_injective x.injective, V.2.2.2]⟩
  have hcancel : ∀ U : Subgroup W, (U.map x.toMonoidHom).map x⁻¹.toMonoidHom = U := by
    intro U
    rw [Subgroup.map_map]
    have hcomp : (x⁻¹.toMonoidHom).comp x.toMonoidHom = MonoidHom.id W := by
      ext u
      exact mulAut_inv_apply_apply x u
    rw [hcomp, Subgroup.map_id]
  have hf_inj : Function.Injective f := by
    intro V V' hVV
    apply Subtype.ext
    have h1 : (f V).1 = (f V').1 := congrArg Subtype.val hVV
    have h2 : ((f V).1).map x⁻¹.toMonoidHom = ((f V').1).map x⁻¹.toMonoidHom := by rw [h1]
    rw [hcancel V.1, hcancel V'.1] at h2
    exact h2
  have hf_bij : Function.Bijective f :=
    ⟨hf_inj, Finite.injective_iff_surjective.mp hf_inj⟩
  let σ : Equiv.Perm X := Equiv.ofBijective f hf_bij
  have hpow : ∀ n : ℕ, ∀ V : X, ((σ ^ n) V).1 = V.1.map (x ^ n).toMonoidHom := by
    intro n
    induction n with
    | zero =>
      intro V
      rw [pow_zero, Equiv.Perm.one_apply, pow_zero]
      have hone : (1 : MulAut W).toMonoidHom = MonoidHom.id W := rfl
      rw [hone, Subgroup.map_id]
    | succ n ih =>
      intro V
      rw [pow_succ', Equiv.Perm.mul_apply]
      change (((σ ^ n) V).1.map x.toMonoidHom) = V.1.map (x ^ (n + 1)).toMonoidHom
      rw [ih V, Subgroup.map_map]
      congr 1
      ext u
      simp [pow_succ', MulAut.mul_apply]
  have hσ : σ ^ 2 ^ k = 1 := by
    refine Equiv.ext (fun V => ?_)
    apply Subtype.ext
    have h := hpow (2 ^ k) V
    rw [hx] at h
    rw [h]
    have hone : (1 : MulAut W).toMonoidHom = MonoidHom.id W := rfl
    rw [hone, Subgroup.map_id, Equiv.Perm.one_apply]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype X := Fintype.ofFinite X
  obtain ⟨V, hVfix⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := k)
    (by rw [← Nat.card_eq_fintype_card, hX7]; norm_num) hσ
  refine ⟨V.1, V.2.1, V.2.2.1, V.2.2.2, ?_⟩
  have h1 : (σ V).1 = V.1 := congrArg Subtype.val hVfix
  change (σ V).1 = V.1
  exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
