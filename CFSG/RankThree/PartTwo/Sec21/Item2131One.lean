module

public import CFSG.RankThree.PartTwo.Sec21.Item21Statements
public import CFSG.RankThree.PartTwo.Sec21.Item211
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Sec21.CoordChange
public import CFSG.RankThree.PartTwo.KFacts.K74Bloom
public import CFSG.RankThree.PartTwo.KFacts.KP14MonomialLines
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec21.Item22Equivariance
import CFSG.RankThree.PartTwo.Sec21.Item22Refl
import CFSG.CGT.PushingUpLit.CGT6E.Emb55GL
import CFSG.RankThree.PartTwo.Sec13.Item13GL
import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts (Mat33 tr01 tr01i tr02 tr02i)
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Item2131One

variable {G : Type} [Group G]

theorem autIn_normalizer_eq_wStar (A : Subgroup G) :
    Sec4.autIn (Subgroup.normalizer (A : Set G)) A = wStar A := by
  ext σ
  rw [Sec4.mem_autIn_iff]
  constructor
  · rintro ⟨h, hN, -, rfl⟩
    exact ⟨⟨h, hN⟩, rfl⟩
  · rintro ⟨⟨h, hN⟩, rfl⟩
    exact ⟨h, hN, hN, rfl⟩

end Item2131One

namespace Item2131One

@[expose] def rot : Mat33 := !![1, 0, 0; 0, 0, 2; 0, 1, 0]

@[expose] def roti : Mat33 := !![1, 0, 0; 0, 0, 1; 0, 2, 0]

@[expose] def Spread (s : Mat33) : Prop :=
  s ≠ 1 ∧ s * s * s = 1 ∧ rot * s * roti * s = s * (rot * s * roti) ∧
    rot * s * roti ≠ 1 ∧ rot * s * roti ≠ s ∧ rot * s * roti ≠ s * s

instance (s : Mat33) : Decidable (Spread s) := by
  unfold Spread
  infer_instance

theorem rot_facts : rot * roti = 1 ∧ roti * rot = 1 ∧ rot.det = 1 ∧ rot 0 0 = 1 ∧
    rot 1 0 = 0 ∧ rot 2 0 = 0 := by
  decide +kernel

theorem spread_of_involution : ∀ p q a b c d : ZMod 3,
    (!![1, p, q; 0, a, b; 0, c, d] : Mat33) * !![1, p, q; 0, a, b; 0, c, d] = 1 →
    (!![1, p, q; 0, a, b; 0, c, d] : Mat33) ≠ 1 →
      Spread (tr01 * !![1, p, q; 0, a, b; 0, c, d] * tr01i * !![1, p, q; 0, a, b; 0, c, d]) ∨
        Spread (tr02 * !![1, p, q; 0, a, b; 0, c, d] * tr02i *
          !![1, p, q; 0, a, b; 0, c, d]) := by
  decide +kernel

theorem mem_of_not_nine_dvd {M : Type} [Group M] {N : Subgroup M} (hN0 : Nat.card N ≠ 0)
    (hN9 : ¬ 9 ∣ Nat.card N) {x y : M} (hx : x ∈ N) (hy : y ∈ N) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) : y = 1 ∨ y = x ∨ y = x ^ 2 := by
  have : Finite N := Nat.finite_of_card_ne_zero hN0
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX3 : (⟨x, hx⟩ : N) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hY3 : (⟨y, hy⟩ : N) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  have hX1 : (⟨x, hx⟩ : N) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hXY : (⟨x, hx⟩ : N) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := Subtype.ext hxy
  have hXo : orderOf (⟨x, hx⟩ : N) = 3 := orderOf_eq_prime hX3 hX1
  have hPX : IsPGroup 3 (Subgroup.zpowers (⟨x, hx⟩ : N)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hXo, pow_one])
  have hPY : IsPGroup 3 (Subgroup.zpowers (⟨y, hy⟩ : N)) :=
    IsPGroup.of_card_dvd_pow (n := 1)
      (by rw [Nat.card_zpowers, pow_one]; exact orderOf_dvd_of_pow_eq_one hY3)
  have hle : Subgroup.zpowers (⟨x, hx⟩ : N) ≤
      Subgroup.normalizer (Subgroup.zpowers (⟨y, hy⟩ : N) : Set N) := by
    rw [Subgroup.zpowers_le]
    exact Sec13.centralizer_le_normalizer_zpowers _
      (Subgroup.mem_centralizer_singleton_iff.mpr hXY)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (IsPGroup.to_sup_of_normal_right' hPX hPY hle)
  have hdvd : 3 ^ k ∣ Nat.card N := hk ▸ Subgroup.card_subgroup_dvd_card _
  have hk1 : k ≤ 1 := by
    by_contra h
    exact hN9 ((pow_dvd_pow 3 (by omega : 2 ≤ k)).trans hdvd)
  have heq : Subgroup.zpowers (⟨x, hx⟩ : N) =
      Subgroup.zpowers ⟨x, hx⟩ ⊔ Subgroup.zpowers ⟨y, hy⟩ := by
    apply Subgroup.eq_of_le_of_card_ge le_sup_left
    rw [hk, Nat.card_zpowers, hXo]
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := pow_one 3
  have hYX : (⟨y, hy⟩ : N) ∈ Subgroup.zpowers (⟨x, hx⟩ : N) := by
    rw [heq]
    exact le_sup_right (a := Subgroup.zpowers (⟨x, hx⟩ : N)) (Subgroup.mem_zpowers _)
  rcases Sec13.eq_of_mem_zpowers_of_pow_three hX3 hYX with h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (by simpa using congrArg Subtype.val h))

variable {G : Type} [Group G]

theorem exists_coords_single {A : Subgroup G} [Finite A] (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 3 ^ 3) {c : A} (hc : c ≠ 1) :
    ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
      f (Multiplicative.ofAdd (Pi.single 0 1)) = c := by
  obtain ⟨f₀⟩ := Sec12.exists_coords hA h27
  set u : Fin 3 → ZMod 3 := Multiplicative.toAdd (f₀.symm c) with hu
  have hu0 : u ≠ 0 := by
    intro h
    apply hc
    have h1 : f₀.symm c = 1 := by
      rw [← ofAdd_toAdd (f₀.symm c), ← hu, h, ofAdd_zero]
    rw [← f₀.apply_symm_apply c, h1, map_one]
  obtain ⟨h1, h2, h00, h10, h20⟩ := KFacts.colMat_facts u hu0
  refine ⟨coordsBy f₀ ⟨KFacts.colMat u, KFacts.colMatInv u, h1, h2⟩, ?_⟩
  have hPe : KFacts.colMat u *ᵥ Pi.single 0 1 = u := by
    rw [Matrix.mulVec_single_one]
    ext i
    fin_cases i
    · exact h00
    · exact h10
    · exact h20
  rw [coordsBy_apply, Units.val_mk, hPe, hu, ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem coordGL_mulVec_eq {A : Subgroup G} (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (σ : MulAut A) (v : Fin 3 → ZMod 3) :
    f (Multiplicative.ofAdd (((coordGL f σ : GL (Fin 3) (ZMod 3)) : Mat33) *ᵥ v)) =
      σ (f (Multiplicative.ofAdd v)) := by
  rw [coordGL_mulVec, coordLin3_apply, ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem apply_eq_iff_mulVec {A : Subgroup G} (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (σ : MulAut A) :
    σ (f (Multiplicative.ofAdd (Pi.single 0 1))) = f (Multiplicative.ofAdd (Pi.single 0 1)) ↔
      ((coordGL f σ : GL (Fin 3) (ZMod 3)) : Mat33) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  rw [← coordGL_mulVec_eq]
  constructor
  · intro h
    exact Multiplicative.ofAdd.injective (f.injective h)
  · intro h
    rw [h]

@[expose] noncomputable def matOf {A : Subgroup G} (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) :
    MulAut A →* Mat33 :=
  (Units.coeHom Mat33).comp (coordGL f)

theorem matOf_apply {A : Subgroup G} (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (σ : MulAut A) : matOf f σ = ((coordGL f σ : GL (Fin 3) (ZMod 3)) : Mat33) :=
  rfl

theorem matOf_injective {A : Subgroup G} (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) :
    Function.Injective (matOf f) :=
  Units.val_injective.comp (coordGL_injective f)

theorem mulVec_ne_self_of_bloomCaseA
    {H : Subgroup (GL (Fin 3) (ZMod 3))} (hA : Toolkit.BloomCaseA H) {g : GL (Fin 3) (ZMod 3)}
    (hg : g ∈ H) (hg2 : g * g = 1) (hg1 : g ≠ 1) {v : Fin 3 → ZMod 3} (hv : v ≠ 0) :
    (g : Mat33) *ᵥ v ≠ v := by
  obtain ⟨F, -, -, hF, hHN, e, μ, -, hμ, hμe, -, -, hμ26, -, -, -, hμN, hμnorm, -, -⟩ := hA
  set N := Subgroup.normalizer (F : Set (GL (Fin 3) (ZMod 3))) with hNdef
  have h78 : Nat.card N = 78 := Toolkit.card_normalizer_of_card_13 hF
  have hM : Nat.card (μ.range.subgroupOf N) = 26 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hμN).toEquiv, hμ26]
  have hidx : (μ.range.subgroupOf N).index = 3 := by
    have h := Subgroup.card_mul_index (μ.range.subgroupOf N)
    rw [hM, h78] at h
    omega
  have hgμ : g ∈ μ.range := by
    have h := Subgroup.pow_index_mem (μ.range.subgroupOf N) ⟨g, hHN hg⟩
    rw [hidx, Subgroup.mem_subgroupOf, Subgroup.coe_pow] at h
    rwa [pow_succ, pow_two, hg2, one_mul] at h
  obtain ⟨ε, rfl⟩ := hgμ
  have hε2 : ε * ε = 1 := hμ (by rw [map_mul, hg2, map_one])
  have hε : (ε : GaloisField 3 3) = 1 ∨ (ε : GaloisField 3 3) = -1 := by
    rw [← mul_self_eq_one_iff, ← Units.val_mul, hε2, Units.val_one]
  rcases hε with h1 | h1
  · have hε1 : ε = 1 := Units.ext h1
    exact absurd (show μ ε = 1 by rw [hε1, map_one]) hg1
  · intro hfix
    apply hv
    have hneg : ((μ ε : GL (Fin 3) (ZMod 3)) : Mat33) *ᵥ v = -v := by
      apply e.injective
      rw [hμe, h1, neg_one_mul, map_neg]
    rw [hneg] at hfix
    ext i
    have h := congrFun hfix i
    simp only [Pi.neg_apply, Pi.zero_apply] at h ⊢
    generalize v i = a at h ⊢
    revert a
    decide

theorem exists_matOf_eq {A : Subgroup G} (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    {S : Subgroup (MulAut A)}
    (hSL : CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ S.map (coordGL f)) {M Mi : Mat33}
    (h1 : M * Mi = 1) (h2 : Mi * M = 1) (hdet : M.det = 1) (h00 : M 0 0 = 1) (h10 : M 1 0 = 0)
    (h20 : M 2 0 = 0) :
    ∃ σ ∈ S, matOf f σ = M ∧ matOf f σ⁻¹ = Mi ∧
      σ (f (Multiplicative.ofAdd (Pi.single 0 1))) = f (Multiplicative.ofAdd (Pi.single 0 1)) := by
  have hg : (⟨M, Mi, h1, h2⟩ : GL (Fin 3) (ZMod 3)) ∈
      CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) :=
    (CFSG.RankThree.SubgroupLists.mem_statedSL_iff _).mpr hdet
  obtain ⟨σ, hσS, hσg⟩ := hSL hg
  refine ⟨σ, hσS, by rw [matOf_apply, hσg], by rw [matOf_apply, map_inv, hσg]; rfl, ?_⟩
  rw [apply_eq_iff_mulVec, hσg, Units.val_mk, Matrix.mulVec_single_one]
  ext i
  fin_cases i
  · exact h00
  · exact h10
  · exact h20

theorem false_of_statedSL_le {A : Subgroup G} (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    {S N : Subgroup (MulAut A)}
    (hSL : CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ S.map (coordGL f))
    (hnorm : ∀ σ ∈ S, σ (f (Multiplicative.ofAdd (Pi.single 0 1))) =
      f (Multiplicative.ofAdd (Pi.single 0 1)) → ∀ τ ∈ N, σ * τ * σ⁻¹ ∈ N)
    {t : MulAut A} (htN : t ∈ N) (ht2 : orderOf t = 2)
    (htc : t (f (Multiplicative.ofAdd (Pi.single 0 1))) = f (Multiplicative.ofAdd (Pi.single 0 1)))
    (hN0 : Nat.card N ≠ 0) (hN9 : ¬ 9 ∣ Nat.card N) : False := by
  have hinj := matOf_injective f
  set T := matOf f t with hT
  have htt : t * t = 1 := by
    rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hTT : T * T = 1 := by
    rw [hT, ← map_mul, htt, map_one]
  have hT1 : T ≠ 1 := by
    intro h
    have h1 : t = 1 := hinj (by rw [← hT, h, map_one])
    rw [h1, orderOf_one] at ht2
    omega
  have hTcol : T.col 0 = Pi.single 0 1 := by
    rw [← Matrix.mulVec_single_one, hT, matOf_apply]
    exact (apply_eq_iff_mulVec f t).mp htc
  have hT00 : T 0 0 = 1 := by
    simpa using congrFun hTcol 0
  have hT10 : T 1 0 = 0 := by
    simpa using congrFun hTcol 1
  have hT20 : T 2 0 = 0 := by
    simpa using congrFun hTcol 2
  have hTeta : T = !![1, T 0 1, T 0 2; 0, T 1 1, T 1 2; 0, T 2 1, T 2 2] := by
    have h := Matrix.eta_fin_three T
    rw [hT00, hT10, hT20] at h
    exact h
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := rot_facts
  obtain ⟨σR, hσRS, hσR, hσRi, hσRc⟩ := exists_matOf_eq f hSL r1 r2 r3 r4 r5 r6
  have key : ∀ {M Mi : Mat33}, M * Mi = 1 → Mi * M = 1 → M.det = 1 → M 0 0 = 1 →
      M 1 0 = 0 → M 2 0 = 0 → Spread (M * T * Mi * T) → False := by
    intro M Mi h1 h2 hdet h00 h10 h20 hsp
    obtain ⟨σg, hσgS, hσg, hσgi, hσgc⟩ := exists_matOf_eq f hSL h1 h2 hdet h00 h10 h20
    obtain ⟨x, hxdef⟩ : ∃ x, x = σg * t * σg⁻¹ * t := ⟨_, rfl⟩
    obtain ⟨y, hydef⟩ : ∃ y, y = σR * x * σR⁻¹ := ⟨_, rfl⟩
    have hxN : x ∈ N := hxdef ▸ N.mul_mem (hnorm σg hσgS hσgc t htN) htN
    have hyN : y ∈ N := hydef ▸ hnorm σR hσRS hσRc x hxN
    have hκx : matOf f x = M * T * Mi * T := by
      rw [hxdef, map_mul, map_mul, map_mul, hσg, hσgi]
    have hκy : matOf f y = rot * (M * T * Mi * T) * roti := by
      rw [hydef, map_mul, map_mul, hσR, hσRi, hκx]
    obtain ⟨hs1, hs3, hcomm, hr1, hr2, hr3⟩ := hsp
    have hx1 : x ≠ 1 := fun h => hs1 (by rw [← hκx, h, map_one])
    have hx3 : x ^ 3 = 1 :=
      hinj (by rw [map_pow, hκx, map_one, pow_three']; exact hs3)
    have hy3 : y ^ 3 = 1 := by
      rw [hydef, conj_pow, hx3, mul_one, mul_inv_cancel]
    have hxy : x * y = y * x :=
      hinj (by rw [map_mul, map_mul, hκx, hκy]; exact hcomm.symm)
    rcases mem_of_not_nine_dvd hN0 hN9 hxN hyN hx3 hy3 hxy hx1 with h | h | h
    · exact hr1 (by rw [← hκy, h, map_one])
    · exact hr2 (by rw [← hκy, h, hκx])
    · exact hr3 (by rw [← hκy, h, pow_two, map_mul, hκx])
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, -, -⟩ := KFacts.tr_facts
  rw [hTeta] at hTT hT1
  rcases spread_of_involution _ _ _ _ _ _ hTT hT1 with h | h <;> rw [← hTeta] at h
  · exact key a1 a2 a3 a4 a5 a6 h
  · exact key b1 b2 b3 b4 b5 b6 h

theorem exists_of_bloomCaseC {A : Subgroup G} (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    {S : Subgroup (MulAut A)} (hC : Toolkit.BloomCaseC (S.map (coordGL f))) :
    ∃ f' : Multiplicative (Fin 3 → ZMod 3) ≃* A, S.map (coordGL f') ≤ KFacts.KP14.monomial ∧
      ∃ G₀ : Subgroup (MulAut A), G₀ ≤ S ∧ Nonempty (G₀ ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨Ls, hLs, h1, hperm, -, -, -, G₀, -, -, ⟨e⟩, hG₀H, -⟩ := hC
  obtain ⟨P, hP⟩ := KFacts.KP14.exists_conj_monomial Ls hLs h1
  refine ⟨coordsBy f P, ?_, G₀.comap (coordGL f), ?_, ?_⟩
  · rintro _ ⟨σ, hσ, rfl⟩
    rw [coordGL_coordsBy]
    exact hP _ (hperm _ ⟨σ, hσ, rfl⟩)
  · intro σ hσ
    obtain ⟨τ, hτ, hτσ⟩ := hG₀H hσ
    rwa [coordGL_injective f hτσ] at hτ
  · have hmap : (G₀.comap (coordGL f)).map (coordGL f) = G₀ :=
      Subgroup.map_comap_eq_self (hG₀H.trans (Subgroup.map_le_range _ _))
    exact ⟨((G₀.comap (coordGL f)).equivMapOfInjective _ (coordGL_injective f)).trans
      ((MulEquiv.subgroupCongr hmap).trans e)⟩

theorem apply_eq_of_mem_starOf {A L : Subgroup G} {c : G} (hcA : c ∈ A)
    (hLC : L ≤ Subgroup.centralizer ({c} : Set G)) {τ : MulAut A} (hτ : τ ∈ starOf A L) :
    τ ⟨c, hcA⟩ = ⟨c, hcA⟩ := by
  obtain ⟨⟨l, hlN⟩, hl, rfl⟩ := hτ
  apply Subtype.ext
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hLC (Subgroup.mem_subgroupOf.mp hl))
  change l * c * l⁻¹ = c
  rw [h1, mul_inv_cancel_right]

theorem exists_mem_inf_not_mem_zpowers {A L : Subgroup G} {c : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hLC : L ≤ Subgroup.centralizer ({c} : Set G))
    {t : MulAut A} (htL : t ∈ starOf A L) (ht2 : orderOf t = 2) :
    ∃ d ∈ A, d ∈ L ∧ d ∉ Subgroup.zpowers c := by
  have hP : ∀ x y : A, x * y = y * x := fun x y => hAe.1.is_comm.comm x y
  have htt := apply_apply_of_orderOf_eq_two ht2
  have htc : t ⟨c, hcA⟩ = ⟨c, hcA⟩ := apply_eq_of_mem_starOf hcA hLC htL
  obtain ⟨a, ha⟩ : ∃ a : A, a⁻¹ * t a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : commOf t = ⊥ := by
      rw [commOf, Subgroup.closure_eq_bot_iff]
      rintro _ ⟨a, rfl⟩
      exact h a
    rw [(commOf_eq_bot_iff t).mp hbot, orderOf_one] at ht2
    omega
  obtain ⟨⟨l, hlN⟩, hl, hlt⟩ := htL
  have hlL : l ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hta : ((t a : A) : G) = l * a * l⁻¹ := by
    rw [← hlt]
    rfl
  refine ⟨((a⁻¹ * t a : A) : G), (a⁻¹ * t a).2, ?_, ?_⟩
  · have h1 : (a : G)⁻¹ * l * (a : G)⁻¹⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hAL (A.inv_mem a.2)) l).mp hlL
    have h2 := L.mul_mem h1 (L.inv_mem hlL)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hta]
    rwa [show (a : G)⁻¹ * l * (a : G)⁻¹⁻¹ * l⁻¹ = (a : G)⁻¹ * (l * a * l⁻¹) by group] at h2
  · intro hd
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd
    have hw : a⁻¹ * t a = (⟨c, hcA⟩ : A) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, ← hk])
    have hfix : t (a⁻¹ * t a) = a⁻¹ * t a := by
      rw [hw, map_zpow, htc]
    have hinv : t (a⁻¹ * t a) = (a⁻¹ * t a)⁻¹ := inv_of_mem_commOf hP htt (mem_commOf t a)
    have h2 : (a⁻¹ * t a) * (a⁻¹ * t a) = 1 := by
      rw [mul_eq_one_iff_eq_inv, ← hinv, hfix]
    have h3 : (a⁻¹ * t a) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hAe.2 _ (a⁻¹ * t a).2)
    apply ha
    rw [pow_three', h2, one_mul] at h3
    exact h3

theorem conj_mem_starOf_of_fix (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) [Finite G]
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hcA : c ∈ A)
    {t : MulAut A} (htL : t ∈ starOf A L) (ht2 : orderOf t = 2) {σ : MulAut A}
    (hσ : σ ∈ wStar A) (hσc : σ ⟨c, hcA⟩ = ⟨c, hcA⟩) {τ : MulAut A} (hτ : τ ∈ starOf A L) :
    σ * τ * σ⁻¹ ∈ starOf A L := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA hc1
      L hLc
  have hLs : L ∈ lStar A :=
    lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A c hpairs.2.2.1)
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hAe.2 c hcA) hc1
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
      ⟨hcA, Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLc⟩) ?_
    rw [Nat.card_zpowers, hc3]
    exact Sec6.card_le_three_of_isCyclic (h66 G hpair.standing A hpair.mem_S L hLs)
      fun x hx => hAe.2 x hx.1
  have hsc : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf hAL, hCA]
  obtain ⟨d, hdA, hdL, hdc⟩ := exists_mem_inf_not_mem_zpowers hAe hcA hAL hLC htL ht2
  have hHW := Sec13.normalizer_inf_le_of_mem hLc hAL hsc hdA hdL hdc
  obtain ⟨w, rfl⟩ := hσ
  have hwc : (w : G) * c * (w : G)⁻¹ = c := congrArg Subtype.val hσc
  have hwH : (w : G) ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine Sec13.centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    calc (w : G) * c = ((w : G) * c * (w : G)⁻¹) * w := by group
      _ = c * w := by rw [hwc]
  have h := conj_mem_starOf w hτ
  rwa [map_conj_eq_of_mem_normalizer (hHW ⟨hwH, w.2⟩)] at h

theorem exists_coords_of_involution
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3)
    (hirr : IsIrreducibleOn (wStar A)) {t : MulAut A} (htL : t ∈ starOf A L)
    (ht2 : orderOf t = 2) (hN0 : Nat.card (starOf A L) ≠ 0)
    (hN9 : ¬ 9 ∣ Nat.card (starOf A L)) :
    ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
      (wStar A).map (coordGL f) ≤ KFacts.KP14.monomial ∧
      ∃ G₀ : Subgroup (MulAut A), G₀ ≤ wStar A ∧ Nonempty (G₀ ≃* alternatingGroup (Fin 4)) := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt ((lZeroStarAt_subset A c) hpairs.2.2.1)
  obtain ⟨f, hf⟩ := exists_coords_single hAe hA27 (c := ⟨c, hcA⟩)
    (fun h => hc1 (congrArg Subtype.val h))
  have htc : t (f (Multiplicative.ofAdd (Pi.single 0 1))) =
      f (Multiplicative.ofAdd (Pi.single 0 1)) := by
    rw [hf]
    exact apply_eq_of_mem_starOf hcA hLC htL
  have hHirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn ((wStar A).map (coordGL f)) :=
    KFacts.isIrreducibleOn_map_glHom f hirr
  rcases (Toolkit.toolkit_clause2 _ hHirr).1 with hCA | hCB | hCC
  · exfalso
    have htt : t * t = 1 := by
      rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have hg1 : coordGL f t ≠ 1 := by
      intro h
      have h1 : t = 1 := coordGL_injective f (by rw [h, map_one])
      rw [h1, orderOf_one] at ht2
      omega
    have he0 : (Pi.single 0 1 : Fin 3 → ZMod 3) ≠ 0 := by
      intro h
      have h1 := congrFun h 0
      simp at h1
    exact mulVec_ne_self_of_bloomCaseA hCA ⟨t, starOf_le_wStar A L htL, rfl⟩
      (by rw [← map_mul, htt, map_one]) hg1 he0 ((apply_eq_iff_mulVec f t).mp htc)
  · exfalso
    refine false_of_statedSL_le f (Toolkit.statedSL_le_of_caseB hCB) ?_ htL ht2 htc hN0 hN9
    intro σ hσ hσc τ hτ
    rw [hf] at hσc
    exact conj_mem_starOf_of_fix h45 h66 hpair hcA htL ht2 hσ hσc hτ
  · exact exists_of_bloomCaseC f hCC

theorem card_perm_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem card_quaternion_two : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem card_semidihedral_four : Nat.card (CFSG.Open.SemidihedralGroup 4) = 16 :=
  CFSG.Semidihedral.card 4 (by norm_num)

theorem card_GL_two_three : Nat.card (GL (Fin 2) (ZMod 3)) = 48 :=
  CFSG.CGT.PushingUpLit.CGT6E.natCard_gl23

end Item2131One

theorem item2131One_of
    (h2130 : Item2130) (h222 : Item222) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) :
    Item2131One := by
  intro G _ _ A E U c L hpair hA27
  obtain ⟨-, ⟨t, htL, htD⟩, hcase⟩ := h222 G A E U c L hpair
  have hcard : Nat.card (starOf A L) = 6 ∨ Nat.card (starOf A L) = 8 := by
    rcases hcase t htL htD with ⟨-, n, -, -, -, -, ⟨e⟩⟩ | ⟨-, n, -, -, -, -, ⟨e⟩⟩ |
        ⟨-, n, -, -, -, -, ⟨e⟩⟩ | ⟨-, -, -, ⟨e⟩⟩ | ⟨h81, -⟩
    · exact Or.inl ((Nat.card_congr e.toEquiv).trans Item2131One.card_perm_three)
    · exact Or.inr ((Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card)
    · exact Or.inr ((Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card)
    · exact Or.inr ((Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card)
    · rw [hA27] at h81
      norm_num at h81
  refine Item2131One.exists_coords_of_involution h45 h66 hpair hA27 (h2130 G A E U c L hpair)
    htL htD.1.1 ?_ ?_
  · rcases hcard with h | h <;> rw [h] <;> norm_num
  · rcases hcard with h | h <;> rw [h] <;> norm_num

theorem item2131One_of_item211
    (h2130 : Item2130) (h211 : Item211) (h2117 : Item2117) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) : Item2131One := by
  intro G _ _ A E U c L hpair hA27
  have hcard : Nat.card (starOf A L) = 6 ∨ Nat.card (starOf A L) = 8 ∨
      Nat.card (starOf A L) = 12 ∨ Nat.card (starOf A L) = 16 ∨
      Nat.card (starOf A L) = 48 := by
    rcases h211 G A E U c L hpair with ⟨-, hM22, -, -, -⟩ | ⟨-, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩ |
        ⟨-, -, ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩⟩ | ⟨-, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩ |
        ⟨-, -, ⟨e⟩⟩ | ⟨-, h81, -⟩ | ⟨-, h81, -⟩ | ⟨-, -, ⟨e⟩⟩ | ⟨-, h81, -⟩
    · exact absurd hM22 (h2117 G A E U c L hpair)
    all_goals first
      | exact absurd (hA27.symm.trans h81) (by norm_num)
      | (rw [Nat.card_congr e.toEquiv]
         simp only [Item2131One.card_perm_three, Item2131One.card_quaternion_two,
           Item2131One.card_semidihedral_four, Item2131One.card_GL_two_three,
           DihedralGroup.nat_card]
         norm_num)
  have hN0 : Nat.card (starOf A L) ≠ 0 := by
    rcases hcard with h | h | h | h | h <;> rw [h] <;> norm_num
  have : Finite (starOf A L) := Nat.finite_of_card_ne_zero hN0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := starOf A L) 2
    (by rcases hcard with h | h | h | h | h <;> rw [h] <;> norm_num)
  refine Item2131One.exists_coords_of_involution h45 h66 hpair hA27 (h2130 G A E U c L hpair)
    x.2 (by rw [Subgroup.orderOf_coe, hx]) hN0 ?_
  rcases hcard with h | h | h | h | h <;> rw [h] <;> norm_num

end CFSG.RankThree.PartTwo.Sec21
