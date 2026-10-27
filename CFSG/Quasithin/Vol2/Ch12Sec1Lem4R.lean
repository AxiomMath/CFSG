module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4J
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNJ
public import CFSG.Quasithin.H13.NQBlockRadicalR2Max
public import CFSG.Quasithin.H13.A7Nat1238NQBase
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem9
public import CFSG.Quasithin.Vol2.Ch10SecA1012Five

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix CFSG.LieType.BorelTits
open scoped IsMulCommutative

namespace Sec1214

section Dual

variable {n : ℕ}

theorem exists_vecStab_transpose_ne (hn : 2 ≤ n) {x₀ w : Fin n → ZMod 2} (hx₀ : x₀ ≠ 0)
    (hw : x₀ ⬝ᵥ w = 1) :
    ∃ g ∈ VecStab.vecStab x₀,
      ((g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *ᵥ w ≠ w := by
  set k : Fin n := ⟨0, by omega⟩
  set j : Fin n := ⟨1, by omega⟩
  have hjk : j ≠ k := by
    intro h
    have := congrArg Fin.val h
    simp [j, k] at this
  have hk0 : (Pi.single k 1 : Fin n → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h k
    simp at this
  obtain ⟨s, hs⟩ := Sec121Q.exists_sl_mulVec_eq hk0 hx₀
  let t : SpecialLinearGroup (Fin n) (ZMod 2) :=
    ⟨Matrix.transvection k j 1, Matrix.det_transvection_of_ne k j hjk.symm 1⟩
  have htk : ((t : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ Pi.single k 1 = Pi.single k 1 := by
    funext i
    simp [t, Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Matrix.single_apply, Pi.single_apply, hjk]
  refine ⟨s * t * s⁻¹, ?_, ?_⟩
  · rw [VecStab.mem_vecStab, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ← mulVec_mulVec, ← hs,
      VecStab.inv_mulVec_mulVec, htk]
  · intro h
    set u := ((s : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *ᵥ w with hu
    have hdot : u k = x₀ ⬝ᵥ w := by
      rw [hu, ← hs, ← single_one_dotProduct k (((s : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *ᵥ w),
        dotProduct_mulVec, vecMul_transpose]
    have huk : u k = 1 := hdot.trans hw
    have htu : ((t : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *ᵥ u = u := by
      have h1 : (((s * t * s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) =
          (((s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *
            ((t : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *
            ((s : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, transpose_mul,
          transpose_mul, Matrix.mul_assoc]
      rw [h1, ← mulVec_mulVec, ← mulVec_mulVec, ← hu] at h
      have h2 := congrArg (fun y => ((s : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *ᵥ y) h
      rw [mulVec_mulVec, ← transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, transpose_one, one_mulVec, ← hu] at h2
      exact h2
    have h3 := congrFun htu j
    simp [t, Matrix.transvection, Matrix.add_mulVec, transpose_add, Matrix.single_mulVec,
      huk] at h3

end Dual

theorem eq_one_of_fixed_V₂ {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}
    {v : G} (S : Sec1216Lv.Setting T L V V₁ V₂ n v) {c : G} (hc : c ∈ V₂)
    (h : ∀ l ∈ Sec1216Lv.lv L v, l * c * l⁻¹ = c) : c = 1 := by
  by_cases hcU : S.C₁.E v ⬝ᵥ S.C₂.E c = 0
  · exact S.eq_one_of_fixed ⟨hc, hcU⟩ h
  have h01 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  obtain ⟨g, hg, hgw⟩ := exists_vecStab_transpose_ne (by rcases S.rank with h | h <;> omega)
    S.x₀_ne (h01 _ hcU)
  obtain ⟨l, hl, hlg⟩ := S.exists_mem_lv ((VecStab.vecStab (S.C₁.E v)).inv_mem hg)
  exfalso
  apply hgw
  have h1 := congrArg S.C₂.E (h l hl)
  rw [S.C₂.conj l c hc, S.hd, hlg,
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix, inv_inv] at h1
  exact h1

section Split

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem commV_invariant {K : Subgroup (MulAut W)} {k : MulAut W} (hk : k ∈ K) {w : W}
    (hw : w ∈ commV K) : k w ∈ commV K :=
  CFSG.Quasithin.commV_apply_mem_of_mem hk hw

omit [Finite W] in
theorem card_of_realizesVia {n : ℕ} {K : Subgroup (MulAut W)} {X : Subgroup W}
    {D : FFModel} (hD : D.sec = ⊤ ∧ D.ker = ⊥) (hcard : Nat.card D.Amb = 2 ^ n)
    {π : D.Gam →* ↥K} (h : D.RealizesVia K X ⊥ π) : Nat.card X = 2 ^ n := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have h1 := (hβk u).mp hu
    rw [Subgroup.mem_bot] at h1 ⊢
    exact Subtype.ext h1
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩)]
  have h2 : D.ker.subgroupOf D.sec = ⊥ := by rw [hD.2, Subgroup.bot_subgroupOf]
  rw [h2, Nat.card_congr (QuotientGroup.quotientBot (G := ↥D.sec)).toEquiv, hD.1,
    Subgroup.card_top, hcard]

theorem b51_split {J K : Subgroup (MulAut W)} (hB : B51Conclusion J K) {U₁ U₂ : Subgroup W}
    (hU₁ : ∀ k ∈ K, ∀ u ∈ U₁, k u ∈ U₁) (hU₂ : ∀ k ∈ K, ∀ u ∈ U₂, k u ∈ U₂)
    (hirr₁ : ∀ X : Subgroup W, X ≤ U₁ → (∀ k ∈ K, ∀ x ∈ X, k x ∈ X) → X = ⊥ ∨ X = U₁)
    (hirr₂ : ∀ X : Subgroup W, X ≤ U₂ → (∀ k ∈ K, ∀ x ∈ X, k x ∈ X) → X = ⊥ ∨ X = U₂)
    (h12 : U₁ ⊓ U₂ = ⊥) (hc₁ : Nat.card U₁ = 2 ^ 4) (hc₂ : Nat.card U₂ = 2 ^ 4)
    (hUc : U₁ ⊔ U₂ ≤ commV K) (hfix : fixV K ⊓ (U₁ ⊔ U₂) = ⊥)
    {P : Subgroup (MulAut W)} (hPK : P ≤ K) (hP₁ : fixV P ⊓ U₁ ≠ ⊥) (hP₂ : fixV P ⊓ U₂ = ⊥)
    (h5 : ∀ π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) →* ↥K,
      ¬ Function.Surjective π) :
    commV K = U₁ ⊔ U₂ ∧ commV K ⊔ fixV J = ⊤ := by
  classical
  obtain ⟨-, -, h3, -, h5', -⟩ := hB
  have hUinv : ∀ k ∈ K, ∀ w ∈ commV K, k w ∈ commV K := fun k hk w hw => commV_invariant hk hw
  have hcard12 : Nat.card ↥(U₁ ⊔ U₂) = 2 ^ 8 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U₁ U₂
      (fun x _ y _ => mul_comm x y)).1
    rw [h12, Subgroup.card_bot, mul_one, hc₁, hc₂] at h
    rw [h]
    norm_num
  have hU₁ne : U₁ ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hc₁; norm_num at hc₁
  have hsec : ∀ {Z Uᵢ : Subgroup W}, Z ⊓ Uᵢ = ⊥ → Uᵢ ≠ ⊥ → (∀ k ∈ K, ∀ z ∈ Z, k z = z) →
      (∀ k ∈ K, ∀ u ∈ Uᵢ, k u ∈ Uᵢ) →
      (∀ X : Subgroup W, X ≤ Uᵢ → (∀ k ∈ K, ∀ x ∈ X, k x ∈ X) → X = ⊥ ∨ X = Uᵢ) →
      XMod.IsInv ↥K (Z ⊔ Uᵢ) ∧ XMod.IsIrrSec ↥K Z (Z ⊔ Uᵢ) := by
    intro Z Uᵢ hZU hU1 hZf hUi hirr
    have hinv : XMod.IsInv ↥K (Z ⊔ Uᵢ) := by
      intro a x hx
      obtain ⟨z, hz, u, hu, rfl⟩ := Subgroup.mem_sup.mp hx
      show (a : MulAut W) (z * u) ∈ Z ⊔ Uᵢ
      rw [map_mul, hZf a a.2 z hz]
      exact Subgroup.mul_mem_sup hz (hUi a a.2 u hu)
    refine ⟨hinv, lt_of_le_of_ne le_sup_left fun h => hU1 ?_, fun J' hJ' hZJ hJU => ?_⟩
    · rw [eq_bot_iff, ← hZU]
      exact le_inf (le_sup_right.trans h.symm.le) le_rfl
    · have hXinv : ∀ k ∈ K, ∀ x ∈ J' ⊓ Uᵢ, k x ∈ J' ⊓ Uᵢ := fun k hk x hx =>
        ⟨hJ' ⟨k, hk⟩ x hx.1, hUi k hk x hx.2⟩
      rcases hirr (J' ⊓ Uᵢ) inf_le_right hXinv with h | h
      · left
        refine le_antisymm (fun j hj => ?_) hZJ
        obtain ⟨z, hz, u, hu, rfl⟩ := Subgroup.mem_sup.mp (hJU hj)
        have huJ : u ∈ J' := by
          have := J'.mul_mem (J'.inv_mem (hZJ hz)) hj
          rwa [inv_mul_cancel_left] at this
        have hu1 : u = 1 := by
          have : u ∈ J' ⊓ Uᵢ := ⟨huJ, hu⟩
          rwa [h, Subgroup.mem_bot] at this
        rw [hu1, mul_one]
        exact hz
      · right
        exact le_antisymm hJU (sup_le hZJ (h ▸ inf_le_left))
  have hUeq : commV K = U₁ ⊔ U₂ := by
    rcases h3 with hhom | ⟨n, hn, π, X₁, X₂, hX, hr₁, hr₂⟩
    · exfalso
      set Z := fixV K ⊓ commV K with hZ
      have hZf : ∀ k ∈ K, ∀ z ∈ Z, k z = z := fun k hk z hz => hz.1 k hk
      have hZ12 : ∀ {X : Subgroup W}, X ≤ U₁ ⊔ U₂ → Z ⊓ X = ⊥ := fun hX =>
        eq_bot_iff.mpr fun x hx => by
          have : x ∈ fixV K ⊓ (U₁ ⊔ U₂) := ⟨hx.1.1, hX hx.2⟩
          rwa [hfix] at this
      have hZ₁ := hZ12 (le_sup_left : U₁ ≤ U₁ ⊔ U₂)
      have hZ₂ := hZ12 (le_sup_right : U₂ ≤ U₁ ⊔ U₂)
      have hU₂ne : U₂ ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hc₂; norm_num at hc₂
      obtain ⟨hinv₁, hirr₁'⟩ := hsec hZ₁ hU₁ne hZf hU₁ hirr₁
      obtain ⟨hinv₂, hirr₂'⟩ := hsec hZ₂ hU₂ne hZf hU₂ hirr₂
      have hI₁U : Z ⊔ U₁ ≤ commV K := sup_le inf_le_right (le_sup_left.trans hUc)
      have hI₂U : Z ⊔ U₂ ≤ commV K := sup_le inf_le_right (le_sup_right.trans hUc)
      have hiso := hhom.2 (Z ⊔ U₁) (Z ⊔ U₂) ⟨le_sup_left, hI₁U, hinv₁, hirr₁'⟩
        ⟨le_sup_left, hI₂U, hinv₂, hirr₂'⟩
      obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hiso
      obtain ⟨u₁, hu₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hP₁
      have hu₁I : (u₁ : W) ∈ Z ⊔ U₁ := Subgroup.mem_sup_right (u₁.2.2)
      have hβ1 : β ⟨u₁, hu₁I⟩ ≠ 1 := by
        rw [Ne, hβk]
        intro hZu
        apply hu₁1
        have : (u₁ : W) ∈ Z ⊓ U₁ := ⟨hZu, u₁.2.2⟩
        rw [hZ₁, Subgroup.mem_bot] at this
        exact Subtype.ext this
      obtain ⟨⟨m, hmI⟩, hm⟩ := QuotientGroup.mk_surjective (β ⟨u₁, hu₁I⟩)
      change W at m
      have hmI' : m ∈ Z ⊔ U₂ := hmI
      obtain ⟨z, hz, u₂, hu₂, hzu⟩ := Subgroup.mem_sup.mp hmI'
      have hu₂P : u₂ ∈ fixV P ⊓ U₂ := by
        refine ⟨fun p hp => ?_, hu₂⟩
        have hpK := hPK hp
        have hpu : p (u₁ : W) = u₁ := u₁.2.1 p hp
        have hu : ((MonoidHom.id ↥K ⟨p, hpK⟩ : ↥K) : MulAut W)
            ((⟨(u₁ : W), hu₁I⟩ : ↥(Z ⊔ U₁)) : W) ∈ Z ⊔ U₁ := by
          show p (u₁ : W) ∈ Z ⊔ U₁
          rw [hpu]
          exact hu₁I
        have hpm : p m ∈ Z ⊔ U₂ := hinv₂ ⟨p, hpK⟩ m hmI'
        have h1 := hβe ⟨p, hpK⟩ ⟨u₁, hu₁I⟩ ⟨m, hmI⟩ hu hpm hm.symm
        have h2 : β ⟨u₁, hu₁I⟩ = β ⟨((MonoidHom.id ↥K ⟨p, hpK⟩ : ↥K) : MulAut W)
            ((⟨(u₁ : W), hu₁I⟩ : ↥(Z ⊔ U₁)) : W), hu⟩ := congrArg β (Subtype.ext hpu.symm)
        have h1' := h2.trans h1
        rw [← hm, QuotientGroup.eq] at h1'
        have h3 : m⁻¹ * p m ∈ Z := h1'
        have h4 : m⁻¹ * p m = u₂⁻¹ * p u₂ := by
          rw [← hzu, map_mul, hZf p hpK z hz]
          group
        have h5 : u₂⁻¹ * p u₂ ∈ Z ⊓ U₂ :=
          ⟨h4 ▸ h3, U₂.mul_mem (U₂.inv_mem hu₂) (hU₂ p hpK u₂ hu₂)⟩
        rw [hZ₂, Subgroup.mem_bot] at h5
        exact (inv_mul_eq_one.mp h5).symm
      rw [hP₂, Subgroup.mem_bot] at hu₂P
      apply hβ1
      rw [← hm, QuotientGroup.eq_one_iff]
      show m ∈ Z
      rw [← hzu, hu₂P, mul_one]
      exact hz
    · have hπ : Function.Surjective π := hr₁.1
      rcases hn with rfl | rfl
      · have hcardF : Nat.card (Multiplicative (Fin 4 → ZMod 2)) = 2 ^ 4 := by
          rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
            Fintype.card_fin]
        have hX₁ := card_of_realizesVia ⟨rfl, rfl⟩ hcardF hr₁
        have hX₂ := card_of_realizesVia ⟨rfl, rfl⟩ hcardF hr₂
        have hUc' : Nat.card ↥(commV K) = 2 ^ 8 := by
          have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X₁ X₂
            (fun x _ y _ => mul_comm x y)).1
          rw [hX.2, Subgroup.card_bot, mul_one, hX₁, hX₂, hX.1] at h
          rw [h]
          norm_num
        exact (Subgroup.eq_of_le_of_card_ge hUc (by rw [hUc', hcard12])).symm
      · exact absurd hπ (h5 π)
  refine ⟨hUeq, ?_⟩
  rcases h5' with h | ⟨hirr, -⟩
  · exact h
  · exfalso
    obtain ⟨-, -, -, hsec'⟩ := hirr
    have hfixed : XMod.fixed ↥K (commV K) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ fixV K ⊓ (U₁ ⊔ U₂) := ⟨fun k hk => hx.2 ⟨k, hk⟩, hUeq ▸ hx.1⟩
      rwa [hfix] at this
    rw [hfixed] at hsec'
    rcases hsec'.2 U₁ (fun a x hx => hU₁ a a.2 x hx) bot_le (hUeq ▸ le_sup_left) with h | h
    · exact hU₁ne h
    · have h1 := hc₁
      rw [h] at h1
      have h2 : Nat.card ↥(commV K) = 2 ^ 8 := by rw [hUeq, hcard12]
      rw [h2] at h1
      norm_num at h1

theorem not_surjective_statedSL_five {K : Type} [Group K] (hK : Nat.card K = 20160)
    (π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) →* K) : ¬ Function.Surjective π := by
  intro hπ
  set e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 (ZMod 2)
  set π' := π.comp e.toMonoidHom with hπ'def
  have hπ' : Function.Surjective π' := hπ.comp e.surjective
  have hs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Vol2.Ch10.SecA.isSimpleGroup_SL_two (by norm_num)
  rcases hs.eq_bot_or_eq_top_of_normal π'.ker with h | h
  · have hinj : Function.Injective π' := (MonoidHom.ker_eq_bot_iff _).mp h
    have hc := Nat.card_eq_of_bijective π' ⟨hinj, hπ'⟩
    rw [Vol2.Ch10.SecA.card_SL_five_two, hK] at hc
    norm_num at hc
  · have hall : ∀ k : K, k = 1 := by
      intro k
      obtain ⟨x, rfl⟩ := hπ' k
      exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
    have h1 : Nat.card K = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    omega

end Split

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ T₀ : Subgroup G} {v : G}
  (c : Setting T L V V₁ V₂ v T₀)
include c

theorem charTwo_M : CharTwo (Subgroup.normalizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOM1 : pCoreOf 2 (Subgroup.normalizer (L : Set G)) ≠ ⊥ := by
    intro hb
    apply Sec121Thm.ne_bot_of_hyp121 c.S.ctx.hyp
    rw [eq_bot_iff, ← hb]
    exact le_pCoreOf_of_le_normalizer 2 c.S.ctx.hyp.le
      (Sec121Q.normalizer_le_of_hyp121 c.S.ctx.hyp)
      (fun x => ⟨1, Subtype.ext (by simpa using c.S.ctx.hVe.2 x x.2)⟩)
  exact charTwo_of_inH c.S.ctx.hyp.qtke.2.1 (c.S.ctx.hyp.sylow.1.toSylow c.S.ctx.hyp.sylow.2)
    ⟨c.S.ctx.hTL, hOM1⟩

theorem charTwo_L : CharTwo L :=
  A4.charTwo_of_subnormal (A4.subnormal_of_normal Subgroup.le_normalizer
    ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl))
    c.charTwo_M

theorem isSylowTwoOf_LT₁ : IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
    (L ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G))) := by
  have := c.S.ctx.hVe.1
  exact Sec1215.isSylowTwoOf_of_le_of_le
    (Sec1215.isSylowTwoOf_inf_normalizer c.S.ctx.hyp c.S.ctx.hTL).2 le_sup_right
    (sup_le (le_inf Subgroup.le_normalizer c.S.ctx.hyp.norm₁) (le_inf c.S.ctx.T₁_le_NL inf_le_right))

theorem LT₁_le_normalizer_V : L ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)) ≤
    Subgroup.normalizer (V : Set G) :=
  sup_le (Subgroup.le_normalizer.trans (Sec121Q.normalizer_le_of_hyp121 c.S.ctx.hyp))
    (inf_le_left.trans c.T_le_normalizer_V)

theorem mem_pCore_of_mem_centralizer {x : ↥L} (hx : (x : G) ∈ Subgroup.centralizer (V : Set G)) :
    x ∈ CFSG.pCore 2 ↥L := by
  obtain ⟨hc₁, hnat₁⟩ := c.S.ctx.hyp.nat₁
  have h1 : (x : G) ∈ pCoreOf 2 L :=
    Sec121Q.inf_centralizer_le_pCoreOf_of_hyp121 c.S.ctx.hyp c.S.ctx.V₁_le c.S.ctx.hyp.norm₁
      hnat₁ ⟨x.2, Subgroup.centralizer_le (by exact_mod_cast c.S.ctx.V₁_le) hx⟩
  obtain ⟨y, hy, hyx⟩ := h1
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy

theorem isTwoReducedIn_V : IsTwoReducedIn (L ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G))) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := c.S.ctx.hVe
  have := hV.1
  refine ⟨c.S.ctx.V_le_T₁.trans le_sup_right, c.LT₁_le_normalizer_V, hV,
    fun D hDY hYD hD2 => ?_⟩
  have hDL : ∀ x ∈ D, x ∈ L → x ∈ Subgroup.centralizer (V : Set G) := by
    intro x hxD hxL
    set N : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) :=
      ((D ⊓ L).subgroupOf L).map c.S.C₁.ρ with hN
    have hNn : N.Normal := by
      refine Subgroup.Normal.map ⟨fun y hy l => ?_⟩ c.S.C₁.ρ c.S.C₁.ρ_surj
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hYD (Subgroup.mem_sup_left l.2)) _).mp hy.1,
        L.mul_mem (L.mul_mem l.2 hy.2) (L.inv_mem l.2)⟩
    have hN2 : IsPGroup 2 N := by
      rintro ⟨g, y, hy, rfl⟩
      have hy' : (y : G) ∈ D ⊓ L := hy
      obtain ⟨k, hk⟩ := hD2 y hy'.1
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : y ^ 2 ^ k ∈ CFSG.pCore 2 ↥L := c.mem_pCore_of_mem_centralizer (by simpa using hk)
      rw [← c.S.C₁.ker_eq (by norm_num) (Classical.choice c.S.ctx.hyp.iso)] at h1
      simpa [MonoidHom.mem_ker] using h1
    have hbot := KGH91.NatCoord.eq_bot_of_normal_isPGroup (by norm_num) hN2
    have h1 : c.S.C₁.ρ ⟨x, hxL⟩ = 1 := by
      have : c.S.C₁.ρ ⟨x, hxL⟩ ∈ N := ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr ⟨hxD, hxL⟩, rfl⟩
      rw [hbot] at this
      exact this
    have h2 : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← c.S.C₁.ker_eq (by norm_num) (Classical.choice c.S.ctx.hyp.iso)]
      exact h1
    have h3 : x ∈ pCoreOf 2 L := ⟨_, by exact h2, rfl⟩
    exact Sec121Q.pCoreOf_le_centralizer_of_hyp121 c.S.ctx.hyp h3
  have hca : ∀ (g : Subgroup.normalizer (V : Set G)) (r : ↥V),
      ((conjAct V g r : ↥V) : G) = g * r * (g : G)⁻¹ := fun g r =>
    Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) r
  have hYL : L ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)) ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer c.S.ctx.T₁_le_NL
  intro d hd
  have hdN : d ∈ Subgroup.normalizer (V : Set G) := c.LT₁_le_normalizer_V (hDY hd)
  have hφ : conjAct V ⟨d, hdN⟩ = 1 := by
    refine Sec121Q.eq_one_of_commute_of_hyp121 c.S.ctx.hyp fun y hy => ?_
    obtain ⟨g, hg', rfl⟩ := hy
    have hg : (g : G) ∈ L := hg'
    have hcomm : d * g * d⁻¹ * (g : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      refine hDL _ ?_ ?_
      · have h1 : (g : G) * d⁻¹ * (g : G)⁻¹ ∈ D :=
          (Subgroup.mem_normalizer_iff.mp (hYD (Subgroup.mem_sup_left hg)) _).mp (D.inv_mem hd)
        have e : d * g * d⁻¹ * (g : G)⁻¹ = d * ((g : G) * d⁻¹ * (g : G)⁻¹) := by group
        rw [e]
        exact D.mul_mem hd h1
      · have h1 : d * g * d⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hYL (hDY hd)) _).mp hg
        exact L.mul_mem h1 (L.inv_mem hg)
    refine MulEquiv.ext fun r => Subtype.ext ?_
    simp only [MulAut.mul_apply, hca]
    have hr : (g : G) * ((d * r * d⁻¹ : G)) * (g : G)⁻¹ ∈ V := by
      have h1 : d * r * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hdN _).mp r.2
      exact (Subgroup.mem_normalizer_iff.mp g.2 _).mp h1
    have h2 := Subgroup.mem_centralizer_iff.mp hcomm _ hr
    calc d * (g * r * (g : G)⁻¹) * d⁻¹
        = (d * g * d⁻¹ * (g : G)⁻¹) * ((g : G) * (d * r * d⁻¹) * (g : G)⁻¹) *
            (d * g * d⁻¹ * (g : G)⁻¹)⁻¹ := by group
      _ = ((g : G) * (d * r * d⁻¹) * (g : G)⁻¹) * (d * g * d⁻¹ * (g : G)⁻¹) *
            (d * g * d⁻¹ * (g : G)⁻¹)⁻¹ := by rw [h2]
      _ = g * (d * r * d⁻¹) * (g : G)⁻¹ := by group
  refine Subgroup.mem_centralizer_iff.mpr fun r hr => ?_
  have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨r, hr⟩ : ↥V) : G)) hφ
  simp only [hca, MulAut.one_apply] at h1
  calc r * d = (d * r * d⁻¹) * d := by rw [h1]
    _ = d * r := by group

theorem V_le_R : V ≤ reducedAggregate (L ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G))) :=
  A7.le_reducedAggregate_of_isTwoReducedIn c.isTwoReducedIn_V

theorem Z₁_le_R : omegaOneCenterOf (T ⊓ Subgroup.normalizer (V₁ : Set G)) ≤
    reducedAggregate (L ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G))) := by
  obtain ⟨-, hred⟩ := isTwoReducedIn_conjClosure_sup1527d c.isSylowTwoOf_LT₁ c.S.ctx.T₁_le_NL
    c.charTwo_L le_rfl
  exact (le_conjClosure _ _).trans (A7.le_reducedAggregate_of_isTwoReducedIn hred)

theorem R_le_T₁ : reducedAggregate (L ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G))) ≤
    T ⊓ Subgroup.normalizer (V₁ : Set G) := fun _ hx =>
  B6.pCoreOf_two_le_of_isSylowTwoOf c.isSylowTwoOf_LT₁
    (NQBlock.mem_omegaOneCenterOf_iff.mp (NQBlock.reducedAggregate_le_omegaOneCenterOf _ hx)).1

theorem exists_offender_R (hFF : LemH9FF4) :
    ∃ A₀ : Subgroup G, IsMaxElemAbelian (T ⊓ Subgroup.normalizer (V₁ : Set G)) A₀ ∧
      ¬ A₀ ≤ Subgroup.centralizer
        (reducedAggregate (L ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G))) : Set G) := by
  by_contra h
  push Not at h
  apply c.not_thompsonJ_le_Q hFF
  rw [← c.thompsonJ_T₁ hFF]
  exact iSup₂_le fun A hA => le_inf (hA.1.trans inf_le_left)
    ((h A hA).trans (Subgroup.centralizer_le (by exact_mod_cast c.V_le_R)))

theorem inf_centralizer_R : L ⊓ Subgroup.centralizer
    (reducedAggregate (L ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G))) : Set G) = pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hc₁, hnat₁⟩ := c.S.ctx.hyp.nat₁
  refine le_antisymm (fun x hx => ?_) (le_inf (pCoreOf_le 2 L) ?_)
  · exact Sec121Q.inf_centralizer_le_pCoreOf_of_hyp121 c.S.ctx.hyp c.S.ctx.V₁_le
      c.S.ctx.hyp.norm₁ hnat₁ ⟨hx.1, Subgroup.centralizer_le
        (by exact_mod_cast c.S.ctx.V₁_le.trans c.V_le_R) hx.2⟩
  · have hYL : L ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)) ≤ Subgroup.normalizer (L : Set G) :=
      sup_le Subgroup.le_normalizer c.S.ctx.T₁_le_NL
    have h1 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G))) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
        (fun g hg => normalizer_le_normalizer_pCoreOf 2 L (hYL hg)) (pCoreOf_isPGroup 2 L)
    exact h1.trans (NQBlock.pCoreOf_le_centralizer_reducedAggregate _)

theorem exists_mul_of_mem_omegaOneCenterOf (hFF : LemH9FF4) (hA21 : AsA21SQTKSection)
    (h51 : AsB51) {z : G} (hz : z ∈ omegaOneCenterOf (T ⊓ Subgroup.normalizer (V₁ : Set G))) :
    ∃ x ∈ V, ∃ y ∈ Subgroup.centralizer (L : Set G), z = x * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVc := c.S.ctx.hVe.1
  set T₁ := T ⊓ Subgroup.normalizer (V₁ : Set G) with hT₁
  set Y := L ⊔ T₁ with hY
  set R := reducedAggregate Y with hRdef
  have hred : IsTwoReducedIn Y R := NQBlock.isTwoReducedIn_reducedAggregate Y
  have hR : IsElemAbelian 2 R := hred.2.2.1
  have hRc : IsMulCommutative ↥R := hR.1
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) := hred.2.1
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans hYR
  have hT₁R : T₁ ≤ Subgroup.normalizer (R : Set G) := le_sup_right.trans hYR
  have hVR : V ≤ R := c.V_le_R
  have hV₁R : V₁ ≤ R := c.S.ctx.V₁_le.trans hVR
  have hV₂R : V₂ ≤ R := c.S.ctx.V₂_le.trans hVR
  have hca : ∀ (g : Subgroup.normalizer (R : Set G)) (r : ↥R),
      ((conjAct R g r : ↥R) : G) = g * r * (g : G)⁻¹ := fun g r =>
    Subgroup.normalizerMonoidHom_apply_apply_coe R (Subgroup.inclusion le_rfl g) r
  have hmemK : ∀ {X : Subgroup G} (hXR : X ≤ Subgroup.normalizer (R : Set G)) {k : MulAut ↥R},
      k ∈ autOn X R → ∃ g ∈ X, ∃ hg : g ∈ Subgroup.normalizer (R : Set G),
        ∀ r : ↥R, ((k r : ↥R) : G) = g * r * g⁻¹ := by
    intro X hXR k hk
    obtain ⟨g, hg, rfl⟩ := hk
    exact ⟨g, hg, g.2, fun r => hca g r⟩
  have hconjK : ∀ {X : Subgroup G} {g : G} (hg : g ∈ X) (hgR : g ∈ Subgroup.normalizer (R : Set G)),
      conjAct R ⟨g, hgR⟩ ∈ autOn X R := fun hg hgR =>
    ⟨⟨_, hgR⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  obtain ⟨A₀, hA₀, hA₀C⟩ := c.exists_offender_R hFF
  have hAs := offenderImages_isFFStarOffender hR c.R_le_T₁ hT₁R ⟨A₀, ⟨hA₀, hA₀C⟩, rfl⟩
  have hA : IsFFStarOffender (autOn Y R) (autI hR A₀) :=
    ⟨hAs.1.trans (autI_mono hR le_sup_right), hAs.2⟩
  have hSQ : SQTKGroup ↥L := by
    have hO : pCoreOf 2 (Subgroup.normalizer (L : Set G)) ≠ ⊥ := by
      intro hb
      apply Sec121Thm.ne_bot_of_hyp121 c.S.ctx.hyp
      rw [eq_bot_iff, ← hb]
      exact le_pCoreOf_of_le_normalizer 2 c.S.ctx.hyp.le
        (Sec121Q.normalizer_le_of_hyp121 c.S.ctx.hyp)
        (fun x => ⟨1, Subtype.ext (by simpa using c.S.ctx.hVe.2 x x.2)⟩)
    exact IsSQTKIn.mono (sqtkGroup_of_pCoreOf_ne_bot c.S.ctx.hyp.qtke c.S.ctx.hyp.simple
      c.S.ctx.hyp.nonabelian hO) Subgroup.le_normalizer
  have hnt : ¬ L ≤ Subgroup.centralizer (R : Set G) := fun h => by
    obtain ⟨t, ht, htV⟩ := Sec121Swap.exists_mem_not_normalizer c.S.ctx.hyp c.S.ctx.hTL
    obtain ⟨l, hl, hlv⟩ := c.exists_conj_not_mem ht htV
    have hlL : t⁻¹ * l * t ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (c.S.ctx.hTL (T.inv_mem ht)) l).mp
        (Sec1216Lv.lv_le_L L v hl)
      simpa using this
    apply hlv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (h hlL) v (hV₁R c.S.ctx.v_mem_V₁)).symm
  have h1a : pCoreOf 2 Y ≤ Y ⊓ Subgroup.centralizer (R : Set G) :=
    le_inf (pCoreOf_le 2 Y) (NQBlock.pCoreOf_le_centralizer_reducedAggregate Y)
  have hB51 := Sec1211Nq.b51Hyp_of_offender hA21 hSQ (Sec121Thm.isQuasisimple_of_hyp121 c.S.ctx.hyp)
    c.T₁_two c.S.ctx.T₁_le_NL h1a hred hnt (autI_mono hR hA₀.1) hA
  have hW2 : ∀ r : ↥R, r ^ 2 = 1 := fun r => Subtype.ext (by simpa using hR.2 r r.2)
  have hC := h51 ↥R hW2 _ _ hB51
  have hKJ : autOn L R ≤ ffJ (autOn Y R) := hB51.2.2.2.1
  have hvL : ∃ l ∈ L, l * v * l⁻¹ ≠ v := by
    obtain ⟨t, ht, htV⟩ := Sec121Swap.exists_mem_not_normalizer c.S.ctx.hyp c.S.ctx.hTL
    obtain ⟨l, hl, hlv⟩ := c.exists_conj_not_mem ht htV
    refine ⟨t⁻¹ * l * t, ?_, fun h => hlv ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (c.S.ctx.hTL (T.inv_mem ht)) l).mp
        (Sec1216Lv.lv_le_L L v hl)
      simpa using this
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc t⁻¹ * l * t * v = (t⁻¹ * l * t * v * (t⁻¹ * l * t)⁻¹) * (t⁻¹ * l * t) := by group
        _ = v * (t⁻¹ * l * t) := by rw [h]
  have hCVL : ∀ x ∈ V, (∀ l ∈ L, l * x * l⁻¹ = x) → x = 1 := by
    intro x hx hxL
    have hx' : x ∈ V₁ ⊔ V₂ := by rw [c.S.ctx.hyp.sup]; exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Sec121Thm.exists_mul_of_mem_sup
      (fun a ha b hb => c.S.ctx.comm (c.S.ctx.V₁_le ha) (c.S.ctx.V₂_le hb)) hx'
    have hfix : ∀ l ∈ L, l * a * l⁻¹ = a ∧ l * b * l⁻¹ = b := by
      intro l hl
      have h1 : (l * a * l⁻¹) * (l * b * l⁻¹) = a * b := by rw [← hxL l hl]; group
      exact Sec1212.decomp_unique c.S.ctx.hyp.inf
        ((Subgroup.mem_normalizer_iff.mp (c.S.ctx.hyp.norm₁ hl) a).mp ha)
        ((Subgroup.mem_normalizer_iff.mp (c.S.ctx.hyp.norm₂ hl) b).mp hb) ha hb h1
    have hb1 : b = 1 := eq_one_of_fixed_V₂ c.S hb fun l hl =>
      (hfix l (Sec1216Lv.lv_le_L L v hl)).2
    have hav := c.S.mem_zpowers_of_fixed ha fun l hl => (hfix l (Sec1216Lv.lv_le_L L v hl)).1
    rw [hb1, mul_one]
    rcases c.S.ctx.mem_zpowers_iff.mp hav with h | h
    · exact h
    · exfalso
      obtain ⟨l, hl, hlv⟩ := hvL
      exact hlv (h ▸ (hfix l hl).1)
  set K := autOn L R with hK
  set J := ffJ (autOn Y R) with hJ
  have hinvR : ∀ {Vᵢ : Subgroup G}, L ≤ Subgroup.normalizer (Vᵢ : Set G) →
      ∀ k ∈ K, ∀ u ∈ Vᵢ.subgroupOf R, k u ∈ Vᵢ.subgroupOf R := by
    intro Vᵢ hLV k hk u hu
    obtain ⟨g, hgL, -, hg⟩ := hmemK hLR hk
    rw [Subgroup.mem_subgroupOf, hg]
    exact (Subgroup.mem_normalizer_iff.mp (hLV hgL) _).mp hu
  have hirrR : ∀ {Vᵢ : Subgroup G} [IsMulCommutative ↥Vᵢ], Vᵢ ≤ R →
      L ≤ Subgroup.normalizer (Vᵢ : Set G) → BinaryNaturalSL (V := ↥Vᵢ) (autOn L Vᵢ) ⊤ ⊥ 4 1 →
      ∀ X : Subgroup ↥R, X ≤ Vᵢ.subgroupOf R → (∀ k ∈ K, ∀ x ∈ X, k x ∈ X) →
        X = ⊥ ∨ X = Vᵢ.subgroupOf R := by
    intro Vᵢ _ hVᵢR hLV hnat X hX hXinv
    have hXV : X.map R.subtype ≤ Vᵢ := by
      rintro _ ⟨x, hx, rfl⟩
      exact hX hx
    have hLX : L ≤ Subgroup.normalizer (X.map R.subtype : Set G) := fun l hl =>
      Sec121Swap.mem_normalizer_of_conj_mem fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        have h1 := hXinv _ (hconjK (X := L) hl (hLR hl)) x hx
        exact ⟨_, h1, hca ⟨l, hLR hl⟩ x⟩
    rcases Sec121Q.eq_bot_or_eq_of_natural hLV hnat _ hXV hLX with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective X R.subtype_injective).mp h
    · right
      ext x
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        exact hX hx
      · intro hx
        rw [← h] at hx
        obtain ⟨y, hy, hyx⟩ := hx
        rwa [Subtype.ext hyx] at hy
  obtain ⟨hc₁', hnat₁⟩ := c.S.ctx.hyp.nat₁
  obtain ⟨hc₂', hnat₂⟩ := c.S.ctx.hyp.nat₂
  have hU₁ := hinvR c.S.ctx.hyp.norm₁
  have hU₂ := hinvR c.S.ctx.hyp.norm₂
  have hirr₁ := hirrR hV₁R c.S.ctx.hyp.norm₁ hnat₁
  have hirr₂ := hirrR hV₂R c.S.ctx.hyp.norm₂ hnat₂
  have h12 : V₁.subgroupOf R ⊓ V₂.subgroupOf R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : G) ∈ V₁ ⊓ V₂ := ⟨hx.1, hx.2⟩
    rw [c.S.ctx.hyp.inf, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  obtain ⟨hcard₁, hcard₂, -⟩ := Sec1212.card_eq_of_hyp121 c.S.ctx.hyp
  have hc₁ : Nat.card ↥(V₁.subgroupOf R) = 2 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₁R).toEquiv, hcard₁]
  have hc₂ : Nat.card ↥(V₂.subgroupOf R) = 2 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₂R).toEquiv, hcard₂]
  have hUV : V₁.subgroupOf R ⊔ V₂.subgroupOf R ≤ V.subgroupOf R :=
    sup_le (Subgroup.subgroupOf_mono R c.S.ctx.V₁_le) (Subgroup.subgroupOf_mono R c.S.ctx.V₂_le)
  have hUc : V₁.subgroupOf R ⊔ V₂.subgroupOf R ≤ commV K := by
    have hcomm : ⁅V, L⁆ ≤ (commV K).map R.subtype := by
      rw [Subgroup.commutator_le]
      intro g hg l hl
      refine ⟨(conjAct R ⟨l, hLR hl⟩ ⟨g, hVR hg⟩ * (⟨g, hVR hg⟩ : ↥R)⁻¹)⁻¹,
        (commV K).inv_mem (Subgroup.subset_closure ⟨_, hconjK hl (hLR hl), ⟨g, hVR hg⟩, rfl⟩), ?_⟩
      simp only [Subgroup.subtype_apply, Subgroup.coe_inv, Subgroup.coe_mul, hca,
        commutatorElement_def]
      group
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hcomm ((Sec1219.eq_commutator_of_hyp121 c.S.ctx.hyp).le (hUV hx))
    rwa [Subtype.ext hyx] at hy
  have hfix : fixV K ⊓ (V₁.subgroupOf R ⊔ V₂.subgroupOf R) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    refine Subtype.ext (hCVL _ (hUV hx.2) fun l hl => ?_)
    have h1 := congrArg Subtype.val (hx.1 _ (hconjK hl (hLR hl)))
    rw [hca] at h1
    exact h1
  have hPK : autOn (Sec1216Lv.lv L v) R ≤ K :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ (Sec1216Lv.lv_le_L L v))
  have hP₁ : fixV (autOn (Sec1216Lv.lv L v) R) ⊓ V₁.subgroupOf R ≠ ⊥ := by
    intro hb
    have hvmem : (⟨v, hV₁R c.S.ctx.v_mem_V₁⟩ : ↥R) ∈
        fixV (autOn (Sec1216Lv.lv L v) R) ⊓ V₁.subgroupOf R := by
      refine ⟨fun k hk => ?_, c.S.ctx.v_mem_V₁⟩
      obtain ⟨g, hg, -, hgk⟩ := hmemK ((Sec1216Lv.lv_le_L L v).trans hLR) hk
      refine Subtype.ext ?_
      rw [hgk]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Sec1216Lv.lv_le_centralizer L v hg)
      show g * v * g⁻¹ = v
      rw [h1, mul_inv_cancel_right]
    rw [hb, Subgroup.mem_bot] at hvmem
    exact c.S.ctx.v_ne_one (congrArg Subtype.val hvmem)
  have hP₂ : fixV (autOn (Sec1216Lv.lv L v) R) ⊓ V₂.subgroupOf R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    refine Subtype.ext (eq_one_of_fixed_V₂ c.S hx.2 fun l hl => ?_)
    have h1 := congrArg Subtype.val (hx.1 _ (hconjK hl (hLR (Sec1216Lv.lv_le_L L v hl))))
    rw [hca] at h1
    exact h1
  have hKcard : Nat.card ↥K = 20160 := by
    rw [Nat.card_congr ((Vol2.Ch10.SecA.autOnEquivQuotOf hLR c.inf_centralizer_R).trans
      (Classical.choice c.S.ctx.hyp.iso)).toEquiv, Vol2.Ch10.SecA.card_SL_four_two]
  obtain ⟨hUeq, htop⟩ := b51_split hC hU₁ hU₂ hirr₁ hirr₂ h12 hc₁ hc₂ hUc hfix hPK hP₁ hP₂
    fun π => not_surjective_statedSL_five hKcard π
  have hzR : (⟨z, c.Z₁_le_R hz⟩ : ↥R) ∈ commV K ⊔ fixV J := htop ▸ Subgroup.mem_top _
  obtain ⟨y, hy, w, hw, hyw⟩ := Subgroup.mem_sup.mp hzR
  refine ⟨y, hUV (by rw [← hUeq]; exact hy), w, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := congrArg Subtype.val (hw _ (hKJ (hconjK hl (hLR hl))))
    rw [hca] at h1
    calc l * w = (l * w * l⁻¹) * l := by group
      _ = w * l := by rw [h1]
  · have h1 := congrArg Subtype.val hyw
    simp only [Subgroup.coe_mul] at h1
    exact h1.symm

end Setting

end Sec1214

end CFSG.Quasithin.H13
