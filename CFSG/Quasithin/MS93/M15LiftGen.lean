module

public import CFSG.Quasithin.MS93.M15Sp4
public import CFSG.Quasithin.Background.B5FinSp
public import CFSG.Quasithin.H13.VolIAltCoverSix
public import CFSG.ClassicalGroups.Symplectic.Perfect
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Background.HConj
public import CFSG.Quasithin.Background.SmithB51SL3A
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Quasithin.Vol2.Ch3Sec2Inputs
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall
open scoped Matrix

namespace Sp4L

theorem eq_top_of_isPerfect {Γ : Type*} [Group Γ] [Finite Γ] [Group.IsPerfect Γ]
    {N : Subgroup Γ} [N.Normal] (h2 : ∀ g : Γ, ∃ e : ℕ, g ^ 2 ^ e ∈ N) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Γ ⧸ N) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨e, he⟩ := h2 g
    exact ⟨e, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact he⟩
  have : Group.IsPerfect (Γ ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hnil : Group.IsNilpotent (Γ ⧸ N) := hP.isNilpotent
  by_contra hne
  have : Nontrivial (Γ ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  exact Group.IsPerfect.not_isNilpotent (Γ ⧸ N) hnil

theorem isPerfect_statedSp {F : Type} [Field F] (hF : 4 ≤ Nat.card F) :
    Group.IsPerfect (StatedSp 2 F) := by
  have : Group.IsPerfect (TauCeti.GLSymplecticFin 2 F) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin F 2 (Or.inl (Or.inr hF))
  let e : TauCeti.GLSymplecticFin 2 F ≃* StatedSp 2 F :=
    (TauCeti.GLSymplecticFin.mulEquivGLSymplectic 2 F).trans
      (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
        (n := 2) (K := F)).symm)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem mem_of_pow_three {Γ : Type*} [Group Γ] {N : Subgroup Γ} {x : Γ} (hx : x ^ 3 = 1)
    {e : ℕ} (he : x ^ 2 ^ e ∈ N) : x ∈ N := by
  have hmod : ∀ n : ℕ, x ^ n = x ^ (n % 3) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hx, one_pow, one_mul]
  have h3 : 2 ^ e % 3 = 1 ∨ 2 ^ e % 3 = 2 := by
    have : ¬ 3 ∣ 2 ^ e := fun h => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    omega
  rw [hmod] at he
  rcases h3 with h | h
  · rwa [h, pow_one] at he
  · rw [h] at he
    have e4 : x = (x ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx, one_mul, pow_one]
    rw [e4]
    exact N.pow_mem he 2

theorem commV_eq_top_of_index_two {W : Type*} [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1)
    {L' N' : Subgroup (MulAut W)} {t : MulAut W} (htn : ∀ n ∈ N', t * n * t⁻¹ ∈ N')
    (htt : t * t ∈ N') (hx : ∀ x ∈ L', x ∈ N' ∨ x * t⁻¹ ∈ N') (hL : commV L' = ⊤) :
    commV N' = ⊤ := by
  have hinv : ∀ a : W, a⁻¹ = a := fun a =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hW a)
  set N := commV N' with hN
  let f : W →* W :=
    { toFun := fun w => t w * w⁻¹
      map_one' := by simp
      map_mul' := fun w w' => by rw [map_mul, mul_inv, mul_mul_mul_comm] }
  have hfw : ∀ w, f w = t w * w⁻¹ := fun _ => rfl
  have hgen : ∀ x ∈ N', ∀ w : W, x w * w⁻¹ ∈ N := fun x hx w =>
    Subgroup.subset_closure ⟨x, hx, w, rfl⟩
  have htN : ∀ n ∈ N, t n ∈ N := by
    intro n hn
    induction hn using Subgroup.closure_induction with
    | mem _ hy =>
      obtain ⟨x, hxN, w, rfl⟩ := hy
      have e : t (x w * w⁻¹) = (t * x * t⁻¹) (t w) * (t w)⁻¹ := by
        rw [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      rw [e]
      exact hgen _ (htn x hxN) _
    | one => rw [map_one]; exact N.one_mem
    | mul _ _ _ _ ha hb => rw [map_mul]; exact N.mul_mem ha hb
    | inv _ _ ha => rw [map_inv]; exact N.inv_mem ha
  have hfN : ∀ n ∈ N, f n ∈ N := fun n hn => N.mul_mem (htN n hn) (N.inv_mem hn)
  have hff : ∀ w, f (f w) ∈ N := by
    intro w
    have h2 : t w * t w = 1 := by rw [← sq]; exact hW _
    have e : f (f w) = (t * t) w * w⁻¹ := by
      simp only [hfw, hinv, map_mul, MulAut.mul_apply]
      calc t (t w) * t w * (t w * w) = t (t w) * (t w * t w) * w := by ac_rfl
        _ = t (t w) * w := by rw [h2, mul_one]
    rw [e]
    exact hgen _ htt w
  have hle : commV L' ≤ N ⊔ f.range := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hxL, w, rfl⟩
    rcases hx x hxL with hxN | hxt
    · exact Subgroup.mem_sup_left (hgen x hxN w)
    · have hy : (x * t⁻¹) (t w) = x w := by
        rw [MulAut.mul_apply, MulAut.inv_apply_self]
      have e : x w * w⁻¹ = ((x * t⁻¹) (t w) * (t w)⁻¹) * f w := by
        rw [hy, hfw]
        group
      rw [e]
      exact Subgroup.mul_mem_sup (hgen _ hxt _) ⟨w, rfl⟩
  have hfle : f.range ≤ N := by
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ N ⊔ f.range := hle (hL ▸ Subgroup.mem_top w)
    obtain ⟨n, hn, r, ⟨w', rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [map_mul]
    exact N.mul_mem (hfN n hn) (hff w')
  rw [eq_top_iff, ← hL]
  exact hle.trans (sup_le le_rfl hfle)

theorem card_le_two_of_symNatural {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L' : Subgroup (MulAut W)} {Z : Subgroup W} (hS : SymmetricNatural L' ⊤ Z 6)
    (hZ : Z ≤ fixV ⁅L', L'⁆) (hcomm : commV L' = ⊤) : Nat.card Z ≤ 2 := by
  have hA := B5.alternatingNatural_derived (by norm_num) hS
  obtain ⟨π₆, hπ₆⟩ := hS
  set ψ : Equiv.Perm (Fin 6) →* MulAut W := L'.subtype.comp π₆ with hψ
  have hrange : ψ.range = L' := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (π₆ g).2
    · intro hx
      obtain ⟨g, hg⟩ := hπ₆.1 ⟨x, hx⟩
      refine ⟨g, ?_⟩
      show ((π₆ g : ↥L') : MulAut W) = x
      rw [hg]
  have hN' : ⁅L', L'⁆ = (alternatingGroup (Fin 6)).map ψ := by
    rw [← hrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      ← alternatingGroup.commutator_perm_eq (by simp)]
    rfl
  set t : MulAut W := ψ (Equiv.swap 0 1) with ht
  have htn : ∀ n ∈ ⁅L', L'⁆, t * n * t⁻¹ ∈ ⁅L', L'⁆ := by
    rw [hN']
    rintro _ ⟨τ, hτ, rfl⟩
    refine ⟨Equiv.swap 0 1 * τ * (Equiv.swap 0 1)⁻¹, ?_, by rw [ht, map_mul, map_mul, map_inv]⟩
    exact (alternatingGroup.normal (α := Fin 6)).conj_mem τ hτ _
  have htt : t * t ∈ ⁅L', L'⁆ := by
    rw [ht, ← map_mul, Equiv.swap_mul_self, map_one]
    exact Subgroup.one_mem _
  have hx : ∀ x ∈ L', x ∈ ⁅L', L'⁆ ∨ x * t⁻¹ ∈ ⁅L', L'⁆ := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨σ, rfl⟩ := hx
    rw [hN']
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
    · exact Or.inl ⟨σ, Equiv.Perm.mem_alternatingGroup.2 h1, rfl⟩
    · refine Or.inr ⟨σ * (Equiv.swap 0 1)⁻¹, Equiv.Perm.mem_alternatingGroup.2 ?_,
        by rw [ht, map_mul, map_inv]⟩
      rw [map_mul, map_inv, h1, Equiv.Perm.sign_swap (by decide)]
      rfl
  have hcomm' : commV ⁅L', L'⁆ = ⊤ := commV_eq_top_of_index_two hW htn htt hx hcomm
  rcases H13.VolI.altNaturalCoverSix_holds W hW ⁅L', L'⁆ Z hZ hcomm' hA with h0 | ⟨h2, -, -⟩
  · rw [h0, Subgroup.card_bot]
    norm_num
  · exact h2.le

section Omega5

variable {F : Type} [Field F] [CharP F 2]

local notation "Ω5" => FFModel.omega5 F (omega5Rad F)

theorem omega5_gen_all (y : Multiplicative ((Ix → F) × F)) :
    y ∈ Subgroup.closure {x | ∃ (g : ↥(StatedSp 2 F)) (z : Multiplicative ((Ix → F) × F)),
      x = omega5Act F g z * z⁻¹} := by
  set G := Subgroup.closure {x | ∃ (g : ↥(StatedSp 2 F)) (z : Multiplicative ((Ix → F) × F)),
      x = omega5Act F g z * z⁻¹} with hG
  have hc : ∀ (g : ↥(StatedSp 2 F)) (x : Ix → F),
      Multiplicative.ofAdd (spMat g *ᵥ x - x, sp4Quad F x + sp4Quad F (spMat g *ᵥ x)) ∈ G :=
    fun g x => by
      rw [← omega5_comm g x 0]
      exact Subgroup.subset_closure ⟨g, _, rfl⟩
  have h1 : ∀ t : F, Multiplicative.ofAdd ((vec4 t 0 0 0 : Ix → F), t) ∈ G := by
    intro t
    have := hc (toStated (spX t 0 0)) (vec4 0 0 1 0)
    rw [spMat_toStated, spX_smul, vec4_sub, sp4Quad_vec4, sp4Quad_vec4] at this
    convert this using 3 <;> ring_nf
  have h2 : ∀ t : F, Multiplicative.ofAdd ((vec4 0 t 0 0 : Ix → F), t) ∈ G := by
    intro t
    have := hc (toStated (spX 0 0 t)) (vec4 0 0 0 1)
    rw [spMat_toStated, spX_smul, vec4_sub, sp4Quad_vec4, sp4Quad_vec4] at this
    convert this using 3 <;> ring_nf
  have h3 : ∀ t : F, Multiplicative.ofAdd ((vec4 0 0 t 0 : Ix → F), t) ∈ G := by
    intro t
    have := hc (toStated (spY t 0 0)) (vec4 1 0 0 0)
    rw [spMat_toStated, spY_smul, vec4_sub, sp4Quad_vec4, sp4Quad_vec4] at this
    convert this using 3 <;> ring_nf
  have h4 : ∀ t : F, Multiplicative.ofAdd ((vec4 0 0 0 t : Ix → F), t) ∈ G := by
    intro t
    have := hc (toStated (spY 0 0 t)) (vec4 0 1 0 0)
    rw [spMat_toStated, spY_smul, vec4_sub, sp4Quad_vec4, sp4Quad_vec4] at this
    convert this using 3 <;> ring_nf
  have h5 : ∀ t : F, Multiplicative.ofAdd ((vec4 0 t 0 0 : Ix → F), (0 : F)) ∈ G := by
    intro t
    have := hc (toStated (spX 0 t 0)) (vec4 0 0 1 0)
    rw [spMat_toStated, spX_smul, vec4_sub, sp4Quad_vec4, sp4Quad_vec4] at this
    convert this using 3 <;> ring_nf
  have hR : ∀ r : F, Multiplicative.ofAdd ((0 : Ix → F), r) ∈ G := by
    intro r
    have e : Multiplicative.ofAdd ((0 : Ix → F), r) =
        Multiplicative.ofAdd ((vec4 0 r 0 0 : Ix → F), r) *
          (Multiplicative.ofAdd ((vec4 0 r 0 0 : Ix → F), (0 : F)))⁻¹ := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.fst_neg, add_neg_cancel]
      · simp only [Prod.snd_add, Prod.snd_neg, neg_zero, add_zero]
    rw [e]
    exact G.mul_mem (h2 r) (G.inv_mem (h5 r))
  obtain ⟨⟨v, s⟩, rfl⟩ := Multiplicative.ofAdd.surjective y
  rw [vec4_eta v]
  set a := v (Sum.inl 0)
  set b := v (Sum.inl 1)
  set c := v (Sum.inr 0)
  set d := v (Sum.inr 1)
  have e : Multiplicative.ofAdd ((vec4 a b c d : Ix → F), s) =
      Multiplicative.ofAdd ((vec4 a 0 0 0 : Ix → F), a) *
        Multiplicative.ofAdd ((vec4 0 b 0 0 : Ix → F), b) *
        Multiplicative.ofAdd ((vec4 0 0 c 0 : Ix → F), c) *
        Multiplicative.ofAdd ((vec4 0 0 0 d : Ix → F), d) *
        Multiplicative.ofAdd ((0 : Ix → F), s - a - b - c - d) := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, vec4_add, add_zero, zero_add]
    · simp only [Prod.snd_add]
      ring
  rw [e]
  exact G.mul_mem (G.mul_mem (G.mul_mem (G.mul_mem (h1 a) (h2 b)) (h3 c)) (h4 d)) (hR _)

theorem natRealizesVia_of_omega5 {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} {π : ↥(StatedSp 2 F) →* ↥L}
    (h : (FFModel.omega5 F (omega5Rad F)).RealizesVia L U Z π) :
    (FFModel.nat (StatedSp 2 F)).RealizesVia L U Z π := by
  obtain ⟨β, hβs, hβk, hβe⟩ := omega5_coord h
  obtain ⟨hs, hZU, -, hUinv, hZinv, -, -, -⟩ := h
  refine ⟨hs, hZU, bot_le, hUinv, hZinv, (FFModel.nat_isActionModel _).sec_inv,
    (FFModel.nat_isActionModel _).ker_inv, ?_⟩
  · let β' : ↥U →* (FFModel.nat (StatedSp 2 F)).Sec :=
      (QuotientGroup.mk' _).comp (Subgroup.topEquiv.symm.toMonoidHom.comp β)
    have hβ' : ∀ u, β' u = QuotientGroup.mk ⟨β u, Subgroup.mem_top _⟩ := fun _ => rfl
    refine ⟨β', fun q => ?_, fun u => ?_, fun γ u m hu hm hum => ?_⟩
    · obtain ⟨⟨x, -⟩, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨u, hu⟩ := hβs x
      exact ⟨u, by rw [hβ']; congr 1; exact Subtype.ext hu⟩
    · rw [hβ', QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      show β u ∈ (⊥ : Subgroup (Multiplicative (Ix → F))) ↔ _
      rw [Subgroup.mem_bot]
      exact hβk u
    · rw [hβ'] at hum ⊢
      have h3 : (⟨β u, Subgroup.mem_top _⟩ : ↥(FFModel.nat (StatedSp 2 F)).sec) = m := by
        have h1 := QuotientGroup.eq.1 hum
        exact inv_mul_eq_one.1 (Subtype.ext (Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 h1)))
      subst h3
      congr 1
      apply Subtype.ext
      refine (hβe γ u hu).trans ?_
      exact congrArg Multiplicative.ofAdd (B513N.natRepSp_apply F γ (Multiplicative.toAdd (β u)))

omit [CharP F 2] in
theorem omega5Act_eq_of_mem_rad [CharP F 2] {g : ↥(StatedSp 2 F)}
    {m : Multiplicative ((Ix → F) × F)} (h : (omega5Act F g m)⁻¹ * m ∈ omega5Rad F) :
    omega5Act F g m = m := by
  have h1 : (Multiplicative.toAdd ((omega5Act F g m)⁻¹ * m)).1 = 0 := h
  rw [toAdd_mul, toAdd_inv, omega5Act_toAdd] at h1
  simp only [Prod.fst_add, Prod.fst_neg] at h1
  have hy : spMat g *ᵥ (Multiplicative.toAdd m).1 = (Multiplicative.toAdd m).1 :=
    neg_add_eq_zero.1 h1
  apply Multiplicative.toAdd.injective
  rw [omega5Act_toAdd, hy]
  refine Prod.ext rfl ?_
  show (Multiplicative.toAdd m).2 + sp4Quad F (Multiplicative.toAdd m).1 +
    sp4Quad F (Multiplicative.toAdd m).1 = (Multiplicative.toAdd m).2
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem lift_of_realizes [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) {W : Type}
    [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {Z : Subgroup W} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤) {π : ↥(StatedSp 2 F) →* ↥H}
    (hreal : (FFModel.nat (StatedSp 2 F)).RealizesVia H ⊤ Z π) :
    Nat.card Z ≤ 2 ^ n ∧ ∀ x ∈ H, ∀ w : W, x w * w⁻¹ ∈ Z → x w = w := by
  have hD : (Ω5).IsActionModel := omega5_isActionModel le_rfl
  have : Finite (Ω5).Amb := (inferInstance : Finite (Multiplicative ((Ix → F) × F)))
  have : Finite ↥(Ω5).sec := Subtype.finite
  have hE2' : ∀ m : Multiplicative ((Ix → F) × F), m ^ 2 = 1 := by
    intro m
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul F, Nat.cast_ofNat, CharTwo.two_eq_zero,
      zero_smul]
  have hE2 : ∀ m : ↥(Ω5).sec, m ^ 2 = 1 := fun m =>
    Subtype.ext (hE2' m.1)
  have hRc : Nat.card ↥((Ω5).ker.subgroupOf (Ω5).sec) = 2 ^ n := by
    show Nat.card ↥((omega5Rad F).subgroupOf ⊤) = 2 ^ n
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv, ← hF]
    have e : F ≃ ↥(omega5Rad F) :=
      { toFun := fun c => ⟨Multiplicative.ofAdd (0, c), rfl⟩
        invFun := fun x => (Multiplicative.toAdd x.1).2
        left_inv := fun _ => rfl
        right_inv := fun x => by
          obtain ⟨y, hy⟩ := x
          apply Subtype.ext
          apply Multiplicative.toAdd.injective
          exact Prod.ext (hy : (Multiplicative.toAdd y).1 = 0).symm rfl }
    exact (Nat.card_congr e).symm
  have hkfix : ∀ γ (m : ↥(Ω5).sec), (m : (Ω5).Amb) ∈ (Ω5).ker → secAut hD γ m = m :=
    fun γ m hm => Subtype.ext (omega5Act_rad γ hm)
  have hgenE : ∀ m : ↥(Ω5).sec, m ∈ Subgroup.closure {x | ∃ γ y, x = secAut hD γ y * y⁻¹} := by
    intro m
    have hle : Subgroup.closure {x : (Ω5).Amb | ∃ (g : ↥(StatedSp 2 F))
        (z : Multiplicative ((Ix → F) × F)), x = omega5Act F g z * z⁻¹} ≤
        (Subgroup.closure {x : ↥(Ω5).sec | ∃ γ y, x = secAut hD γ y * y⁻¹}).map
          (Ω5).sec.subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨g, z, rfl⟩
      exact ⟨secAut hD g ⟨z, Subgroup.mem_top _⟩ * (⟨z, Subgroup.mem_top _⟩ : ↥(Ω5).sec)⁻¹,
        Subgroup.subset_closure ⟨g, _, rfl⟩, rfl⟩
    obtain ⟨m', hm', hmm'⟩ := hle (omega5_gen_all m.1)
    rwa [show m' = m from Subtype.ext hmm'] at hm'
  have hbound : ∀ (W' : Type) [CommGroup W'] [Finite W'], (∀ w : W', w ^ 2 = 1) →
      ∀ C : H13.VolI.ModelCover (Ω5) W',
        Nat.card C.β.ker ≤ Nat.card ↥((Ω5).ker.subgroupOf (Ω5).sec) := by
    intro W' _ _ hW' C
    have hR' := MS93.ModelCover.realizesVia_range hD C
    have hfix : C.β.ker ≤ fixV C.ρ.range := by
      intro z hz x hx
      obtain ⟨γ, rfl⟩ := hx
      exact C.fix γ z (MonoidHom.mem_ker.1 hz)
    rw [hRc]
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
    · have hcomm' : commV C.ρ.range = ⊤ := eq_top_iff.2 fun v _ =>
        Subgroup.closure_mono (by
          rintro _ ⟨γ, w, rfl⟩
          exact ⟨C.ρ γ, ⟨γ, rfl⟩, w, rfl⟩) (C.gen v)
      have hS := asSp4S6 W' C.ρ.range ⊤ C.β.ker
        ⟨F, inferInstance, inferInstance, hF, ⟨_, natRealizesVia_of_omega5 hR'⟩⟩
      rw [pow_one]
      exact card_le_two_of_symNatural hW' hS
        (fun z hz x hx => hfix hz x (Subgroup.commutator_le_self _ hx)) hcomm'
    · exact card_le_of_omega5_realizesVia hW' C.ρ.range ⊤ C.β.ker le_top
        (fun z hz x hx => hfix hz x hx) (fun _ _ _ _ => Subgroup.mem_top _)
        (MS93.ModelCover.commOf_range C) hn2 hF hR'
  obtain ⟨C, π', hπ's, hρ, hβk⟩ :=
    H13.VolI.ModelCover.exists_of_realizes hZ hcomm ⟨_, omega5_realizesVia_of_nat hreal⟩
  obtain ⟨ψ, hψs, -, hψe, hψβ⟩ :=
    ModelCover.exists_quotient (secAut hD) (fun _ _ => rfl) hkfix hgenE hE2 hbound hW C
  refine ⟨?_, fun x hx w hxw => ?_⟩
  · have hZle : Z ≤ ((Ω5).ker.subgroupOf (Ω5).sec).map ψ := by
      intro z hz
      obtain ⟨m, rfl⟩ := hψs z
      refine ⟨m, ?_, rfl⟩
      have h1 : C.β (ψ m) = 1 := (hβk _).2 hz
      rw [hψβ] at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
    calc Nat.card Z ≤ Nat.card (((Ω5).ker.subgroupOf (Ω5).sec).map ψ) := Subgroup.card_le_of_le hZle
      _ ≤ Nat.card ((Ω5).ker.subgroupOf (Ω5).sec) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ ψ)
      _ = 2 ^ n := hRc
  · obtain ⟨γ, hγ⟩ := hπ's ⟨x, hx⟩
    have hxρ : x = C.ρ γ := by rw [hρ, hγ]
    obtain ⟨m, rfl⟩ := hψs w
    have h1 : C.β (x (ψ m) * (ψ m)⁻¹) = 1 := (hβk _).2 hxw
    rw [hxρ, ← hψe, map_mul, map_inv, hψβ, hψβ, mul_inv_eq_one, QuotientGroup.eq] at h1
    have hfix : secAut hD γ m = m :=
      Subtype.ext (omega5Act_eq_of_mem_rad (Subgroup.mem_subgroupOf.1 h1))
    rw [hxρ, ← hψe, hfix]

end Omega5

end Sp4L

end CFSG.Quasithin.MS93
