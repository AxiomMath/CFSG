module

public import CFSG.Quasithin.Vol2.Ch4Sec3Sp4
public import CFSG.Quasithin.Vol2.Ch4Sec3A7Perm
public import CFSG.Quasithin.Vol2.Ch4Sec3L4310Mod
import CFSG.Quasithin.Vol2.Ch4Sec3Sp4Gen

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

@[expose] def LemmaC64Ten : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L R TH Sig : Subgroup G),
    R ≤ Subgroup.normalizer (L : Set G) → pCoreOf 2 (L ⊔ R) ≤ R →
    blockU L ≠ ⊥ → IsElemAbelian 2 (blockU L) →
    IsPGroup 2 TH → R ≤ TH → TH ≤ Subgroup.normalizer (R : Set G) →
    TH ≤ Subgroup.normalizer (Sig : Set G) → (L.subgroupOf (L ⊔ TH)).IsSubnormal →
    (∀ R₀ : Subgroup G, R₀ ≠ ⊥ → R₀ ≤ R → L ⊔ TH ≤ Subgroup.normalizer (R₀ : Set G) →
      ¬ Sig ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (R₀ : Set G)) →
    TH ≤ Subgroup.normalizer (L : Set G) → IsShort2 L →
    ∀ (α : ↥L →* alternatingGroup (Fin 7)) (β : ↥(blockU L) →* Multiplicative (AltHeart 7)),
    Function.Surjective α → α.ker = CFSG.pCore 2 ↥L → Function.Surjective β →
    β.ker = (blockZ L).subgroupOf (blockU L) →
    (∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      ∀ x : ↥(evenWeight 7), (QuotientAddGroup.mk x : AltHeart 7) = Multiplicative.toAdd (β u) →
        (QuotientAddGroup.mk (permWeight 7 (α ℓ : Equiv.Perm (Fin 7)) x) : AltHeart 7) =
          Multiplicative.toAdd (β v)) →
    ∀ a b : Fin 7, a ≠ b →
    (∀ r : ↥(Subgroup.normalizer (L : Set G)), (r : G) ∈ R →
      (∀ k : ↥L, α ((conjAct L r) k) = α k) ∨
        ∀ k : ↥L, ((α ((conjAct L r) k) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
          Equiv.swap a b * (α k : Equiv.Perm (Fin 7)) * (Equiv.swap a b)⁻¹) →
    (∃ r : ↥(Subgroup.normalizer (L : Set G)), (r : G) ∈ R ∧
      ∀ k : ↥L, ((α ((conjAct L r) k) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        Equiv.swap a b * (α k : Equiv.Perm (Fin 7)) * (Equiv.swap a b)⁻¹) →
    pCoreOf 2 (L ⊔ TH) ≤ R →
    (∀ r ∈ R, (∀ l ∈ L, l * r * l⁻¹ * r⁻¹ ∈ pCoreOf 2 L) → r ∈ pCoreOf 2 (L ⊔ TH)) →
    (∀ R₀ : Subgroup G, R₀ ≠ ⊥ → R₀ ≤ R → L ⊔ TH ≤ Subgroup.normalizer (R₀ : Set G) →
      Sig ⊓ Subgroup.normalizer (R₀ : Set G) = R) →
    IsPGroup 2 Sig →
    oTwoUpper (L ⊓ Subgroup.normalizer (R : Set G)) ≤ Subgroup.normalizer (Sig : Set G) →
    ∀ u : ↥(blockU L),
      Multiplicative.toAdd (β u) = (QuotientAddGroup.mk (A7.pairVec a b) : AltHeart 7) →
        TH ⊔ Sig ≤ Subgroup.centralizer ({(u : G)} : Set G)

theorem card_quot_pCore_le_card_range {Λ X : Type} [Group Λ] [Finite Λ] [Group X]
    (φ : Λ →* X) (hker : φ.ker ≤ CFSG.pCore 2 Λ) :
    Nat.card (Λ ⧸ CFSG.pCore 2 Λ) ≤ Nat.card φ.range := by
  have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at e1
  have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 Λ)
  have hle := Subgroup.card_le_of_le hker
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  by_contra h
  push Not at h
  have : Nat.card φ.range * Nat.card φ.ker < Nat.card (Λ ⧸ CFSG.pCore 2 Λ) *
      Nat.card (CFSG.pCore 2 Λ) :=
    calc Nat.card φ.range * Nat.card φ.ker < Nat.card (Λ ⧸ CFSG.pCore 2 Λ) * Nat.card φ.ker :=
          Nat.mul_lt_mul_of_pos_right h hpos
      _ ≤ _ := Nat.mul_le_mul_left _ hle
  omega

theorem le_pCore_of_normal {Λ : Type} [Group Λ] {N : Subgroup Λ} (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N ≤ CFSG.pCore 2 Λ :=
  le_sSup ⟨hN, h2⟩

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowTwoOf_of_le_of_le {S X H : Subgroup G} (hS : IsSylowTwoOf S H) (hSX : S ≤ X)
    (hXH : X ≤ H) : IsSylowTwoOf S X :=
  ⟨hSX, hS.2.1, fun h => hS.2.2
    (h.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex S X H hSX hXH)))⟩

omit [Finite G] in
theorem le_of_noTwoQuotient {K J P : Subgroup G}
    (h1 : ∀ (N : Subgroup K) [N.Normal], IsPGroup 2 (K ⧸ N) → N = ⊤)
    (hKJ : K ≤ Subgroup.normalizer (J : Set G)) (hP : IsPGroup 2 P) (hPK : P ≤ K)
    (hK : ∀ g ∈ K, ∃ j ∈ J, ∃ p ∈ P, g = j * p) : K ≤ J := by
  have : (J.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKJ
  have h2 : IsPGroup 2 (K ⧸ J.subgroupOf K) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨j, hj, p, hp, hg⟩ := hK g g.2
    obtain ⟨m, hm⟩ := hP ⟨p, hp⟩
    have hjK : j ∈ K := by
      have e : j = (g : G) * p⁻¹ := by rw [hg]; group
      rw [e]
      exact K.mul_mem g.2 (K.inv_mem (hPK hp))
    have e : g = ⟨j, hjK⟩ * ⟨p, hPK hp⟩ := Subtype.ext hg
    have hpm : (⟨p, hPK hp⟩ : K) ^ 2 ^ m = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hm
      simpa using this
    refine ⟨m, ?_⟩
    rw [e, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hj), one_mul,
      ← QuotientGroup.mk_pow, hpm, QuotientGroup.mk_one]
  have hN := h1 _ h2
  intro g hg
  have : (⟨g, hg⟩ : K) ∈ J.subgroupOf K := by
    rw [hN]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

omit [Finite G] in
theorem commute_swap_of_mem_normalizer {K R : Subgroup G} (α : ↥K →* alternatingGroup (Fin 7))
    (hα : Function.Surjective α) {a b : Fin 7} (hab : a ≠ b)
    (hR : ∀ r : ↥(Subgroup.normalizer (K : Set G)), (r : G) ∈ R →
      (∀ k : ↥K, α ((conjAct K r) k) = α k) ∨
        ∀ k : ↥K, ((α ((conjAct K r) k) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
          Equiv.swap a b * (α k : Equiv.Perm (Fin 7)) * (Equiv.swap a b)⁻¹)
    (r₀ : ↥(Subgroup.normalizer (K : Set G))) (hr₀R : (r₀ : G) ∈ R)
    (hr₀ : ∀ k : ↥K, ((α ((conjAct K r₀) k) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
      Equiv.swap a b * (α k : Equiv.Perm (Fin 7)) * (Equiv.swap a b)⁻¹)
    (k : ↥K) (hk : (k : G) ∈ Subgroup.normalizer (R : Set G)) :
    (α k : Equiv.Perm (Fin 7)) * Equiv.swap a b = Equiv.swap a b * (α k : Equiv.Perm (Fin 7)) := by
  set σ := Equiv.swap a b with hσ
  set τ := (α k : Equiv.Perm (Fin 7)) * σ * (α k : Equiv.Perm (Fin 7))⁻¹ with hτ
  have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
  let r₁ : ↥(Subgroup.normalizer (K : Set G)) := ⟨k, hkN⟩ * r₀ * ⟨k, hkN⟩⁻¹
  have hr₁R : (r₁ : G) ∈ R := (Subgroup.mem_normalizer_iff.mp hk r₀).mp hr₀R
  have hact : ∀ k' : ↥K, ((α ((conjAct K r₁) k') : alternatingGroup (Fin 7)) :
      Equiv.Perm (Fin 7)) = τ * (α k' : Equiv.Perm (Fin 7)) * τ⁻¹ := by
    intro k'
    have e : (conjAct K r₁) k' = k * (conjAct K r₀) (k⁻¹ * k' * k) * k⁻¹ := by
      apply Subtype.ext
      simp [conjAct, r₁, mul_assoc]
    rw [e, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hr₀, map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτ]
    group
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 7
    (by norm_num)
  have hconj : ∀ π : Equiv.Perm (Fin 7),
      (∀ k' : ↥K, ((α ((conjAct K r₁) k') : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        π * (α k' : Equiv.Perm (Fin 7)) * π⁻¹) → τ = π := by
    intro π hπ
    apply hinj
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    obtain ⟨k', rfl⟩ := hα g
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply, ← hact, hπ]
  rcases hR r₁ hr₁R with h | h
  · exfalso
    have h1 : τ = 1 := hconj 1 fun k' => by rw [h k']; group
    have h2 : σ = 1 := by
      have := congrArg (fun π => (α k : Equiv.Perm (Fin 7))⁻¹ * π * α k) h1
      simpa [hτ, mul_assoc] using this
    exact hab (Equiv.swap_eq_one_iff.mp h2)
  · have h1 : τ = σ := hconj σ h
    calc (α k : Equiv.Perm (Fin 7)) * σ = τ * α k := by rw [hτ]; group
      _ = σ * α k := by rw [h1]

namespace Setting432K

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (sk : Setting432K G T M L n I H K t)
include sk

theorem not_isA7Block (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h64 : LemmaC64Ten) (hchar : CharTwo K)
    (h41 : C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
      ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K) :
    ¬ IsAltBlockType K 7 := by
  classical
  intro hblk
  set V := ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ with hV
  set S := T ⊓ H with hS
  set Rp := T ⊓ centralizerSection M L (pCoreOf 2 L) with hRp
  set R := pCoreOf 2 I with hRdef
  obtain ⟨hshort, α₀, hα₀, hker₀, -⟩ := hblk
  have hSK := sk.S_le_normalizer
  have hLK := sk.L_le_K
  have hcardK : Nat.card (ModO2 K) = 2520 := by
    rw [card_modO2_of_surjective α₀ hα₀ hker₀, A7.card_alt7]
  obtain ⟨hLblk, hVeq, hInd, hMK⟩ : IsAltBlockType (conjClosure L (H ⊓ M)) 5 ∧
      V = blockU (conjClosure L (H ⊓ M)) ∧ InducesTransposition R K 7 ∧
      H ⊓ M ⊓ K = K ⊓ Subgroup.normalizer (R : Set G) := by
    rcases h41.2.2.2 with c1 | c2 | c3 | c4
    · obtain ⟨m, hm, hLb, hVb, hKb, hIt, hMK⟩ := c1
      have hm5 : m = 5 := by
        obtain ⟨-, α₁, hα₁, hker₁, -⟩ := hKb
        have h1 := card_modO2_of_surjective α₁ hα₁ hker₁
        rw [card_of_alt' (by omega) (MulEquiv.refl _), hcardK] at h1
        rcases hm with rfl | rfl
        · rfl
        · exfalso
          simp [Nat.factorial] at h1
      subst hm5
      exact ⟨hLb, hVb, hIt, hMK⟩
    · exfalso
      obtain ⟨⟨-, F, _, _, hF, α₁, hα₁, hker₁, -⟩, -⟩ := c2
      have h1 := card_modO2_of_surjective α₁ hα₁ hker₁
      rw [card_statedSp_two_of_card_four hF, hcardK] at h1
      norm_num at h1
    · exfalso
      obtain ⟨n', F', _, _, -, hF', ⟨e⟩, -⟩ := c3
      have h1 : Nat.card (ModO2 K) = Nat.card ↥(StatedSL 3 F') := Nat.card_congr e.toEquiv
      rw [hcardK, card_statedSL_three, hF'] at h1
      exact sl3_card_ne (Or.inl rfl) h1.symm
    · exfalso
      obtain ⟨h4, -, -⟩ := c4
      rcases h4 with h | h
      · have h1 := F420.card_of_l42 h
        rw [hcardK] at h1
        norm_num at h1
      · have h1 := F420.card_of_l52 h
        rw [hcardK] at h1
        norm_num at h1
  have hLeq : conjClosure L (H ⊓ M) = L := h41.1.symm
  rw [hLeq] at hLblk hVeq
  obtain ⟨hRK, α, ⟨hα, hkerα, β, hβ, hkerβ, hequiv⟩, σ, hσ, hRact, r₀, hr₀R, hr₀⟩ := hInd
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨-, αL, hαL, hkerαL, -⟩ := hLblk
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp sk.cComp
  have hperfL : ⁅L, L⁆ = L := sk.base.hyp.commutator_eq
  have hLperf : commutator L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subtype_commutator, hperfL, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hLHMK : L ≤ H ⊓ M ⊓ K :=
    le_inf (le_inf (sk.base.L_le_I.trans sk.base.inM.2) sk.base.hyp.L_le) hLK
  have hLNR : L ≤ Subgroup.normalizer (R : Set G) := by
    have h1 := hLHMK
    rw [hMK] at h1
    exact h1.trans inf_le_right
  have hcomm : ∀ k : K, (k : G) ∈ Subgroup.normalizer (R : Set G) →
      (α k : Equiv.Perm (Fin 7)) * Equiv.swap a b = Equiv.swap a b * (α k : Equiv.Perm (Fin 7)) :=
    fun k hk => commute_swap_of_mem_normalizer α hα hab hRact r₀ hr₀R hr₀ k hk
  set φ : L →* alternatingGroup (Fin 7) := α.comp (Subgroup.inclusion hLK) with hφ
  have hφfix : ∀ l : L, ((φ l : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) a = a ∧
      ((φ l : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) b = b :=
    A7.apply_eq_of_perfect ((alternatingGroup (Fin 7)).subtype.comp φ) hab hLperf
      (fun l => hcomm _ (hLNR l.2))
  have hkerφ : φ.ker ≤ CFSG.pCore 2 L := by
    apply le_pCore_of_normal (MonoidHom.normal_ker φ)
    rintro ⟨l, hl⟩
    have h1 : Subgroup.inclusion hLK l ∈ α.ker := hl
    rw [hkerα] at h1
    have h2 : ((l : L) : G) ∈ pCoreOf 2 K := (mem_pCoreOf_iff' _).mpr h1
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 K) ⟨l, h2⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hm
    simpa using this
  have h60 : Nat.card (L ⧸ CFSG.pCore 2 L) = 60 := by
    have h1 := card_modO2_of_surjective αL hαL hkerαL
    rw [show Nat.card (ModO2 L) = Nat.card (L ⧸ CFSG.pCore 2 L) from rfl,
      nat_card_alternatingGroup] at h1
    rw [h1, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hcard60 : Nat.card ↥(A7.fixSet {a, b}) = 60 := by
    rw [A7.card_fixSet _ (by rw [Finset.card_pair hab]; norm_num), Finset.card_pair hab]
    decide
  have hrange : φ.range = A7.fixSet {a, b} := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨l, rfl⟩ x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (hφfix l).1
      · exact (hφfix l).2
    · rw [hcard60]
      have := card_quot_pCore_le_card_range φ hkerφ
      rwa [h60] at this
  have hkerφeq : φ.ker = CFSG.pCore 2 L := by
    apply Subgroup.eq_of_le_of_card_ge hkerφ
    have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hcard60] at e1
    have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 L)
    rw [h60] at e2
    omega
  have hO2LK : pCoreOf 2 L ≤ pCoreOf 2 K := by
    intro x hx
    have hxL : x ∈ L := pCoreOf_le 2 L hx
    have hl := (mem_pCoreOf_iff' (⟨x, hxL⟩ : L)).mp hx
    have h1 : (⟨x, hxL⟩ : L) ∈ φ.ker := by
      rw [hkerφeq]
      exact hl
    have h2 : Subgroup.inclusion hLK ⟨x, hxL⟩ ∈ α.ker := h1
    rw [hkerα] at h2
    exact (mem_pCoreOf_iff' _).mpr h2
  have hUQ : blockU K ≤ pCoreOf 2 K :=
    commutator_le_left_of_le_normalizer (le_normalizer_pCoreOf 2 K)
  have hQS : pCoreOf 2 K ≤ S := sk.pCoreOf_K_le_S hR hC h37 h38 h39
  have hKU : K ≤ Subgroup.normalizer (blockU K : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ K
  have hLU : L ≤ Subgroup.normalizer (blockU K : Set G) := hLK.trans hKU
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
    sk.base.hyp.normal (sk.base.hyp.T_le hx)
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := inf_le_left.trans hTL
  have hUL : blockU K ≤ Subgroup.normalizer (L : Set G) := (hUQ.trans hQS).trans hSL
  have hULV : ⁅blockU K, L⁆ ≤ V := by
    have h1 : ⁅blockU K, L⁆ ≤ L ⊓ blockU K :=
      le_inf (commutator_le_right_of_le_normalizer hUL) (commutator_le_left_of_le_normalizer hLU)
    have h2 : L ⊓ blockU K ≤ pCoreOf 2 L :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun l hl => mem_normalizer_inf (Subgroup.le_normalizer hl) (hLU hl))
        ((pCoreOf_isPGroup 2 K).to_le (inf_le_right.trans hUQ))
    rw [commutator_eq_commutator_commutator_of_perfect' hperfL hUL, hVeq]
    exact Subgroup.commutator_mono (h1.trans h2) le_rfl
  obtain ⟨x, hxa, hxb⟩ : ∃ x : Fin 7, x ≠ a ∧ x ≠ b := by
    obtain ⟨y, z, hyz, hya, hyb, -, -, -, -⟩ := A7.exists_two_ne_of_three a b a
    exact ⟨y, hya, hyb⟩
  obtain ⟨y, z, hyz, hya, hyb, hyx, hza, hzb, hzx⟩ := A7.exists_two_ne_of_three a b x
  obtain ⟨c, hc, hcc⟩ := A7.threeCycle_mem_fixSet (Ne.symm hyx) (Ne.symm hzx) hxa hxb hya hyb
    hza hzb
  obtain ⟨l₀, hl₀⟩ : c ∈ φ.range := hrange ▸ hc
  have hca : (c : Equiv.Perm (Fin 7)) a = a := (A7.mem_fixSet.mp hc) a (by simp)
  have hcx : (c : Equiv.Perm (Fin 7)) x = z := by
    rw [hcc, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hzx hyz.symm]
  obtain ⟨u₁, hu₁⟩ := hβ (Multiplicative.ofAdd (QuotientAddGroup.mk (A7.pairVec a x)))
  let c₁ : blockU K := ⟨(l₀ : G) * (u₁ : G) * (l₀ : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hLU l₀.2) u₁).mp u₁.2⟩
  have h1 := hequiv (Subgroup.inclusion hLK l₀) u₁ c₁ rfl (A7.pairVec a x)
    (by rw [hu₁, toAdd_ofAdd])
  have hαl₀ : ((α (Subgroup.inclusion hLK l₀) : alternatingGroup (Fin 7)) :
      Equiv.Perm (Fin 7)) = c := by
    have : φ l₀ = c := hl₀
    rw [← this]
    rfl
  rw [A7.permWeight_pairVec, hαl₀, hca, hcx] at h1
  set v : blockU K := u₁ * c₁⁻¹ with hvdef
  have hvV : (v : G) ∈ V := by
    apply hULV
    have e : (v : G) = ⁅(u₁ : G), (l₀ : G)⁆ := by
      show (u₁ : G) * ((l₀ : G) * (u₁ : G) * (l₀ : G)⁻¹)⁻¹ = ⁅(u₁ : G), (l₀ : G)⁆
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator u₁.2 l₀.2
  have hβv : Multiplicative.toAdd (β v) =
      (QuotientAddGroup.mk (A7.pairVec x z) : AltHeart 7) := by
    rw [hvdef, map_mul, map_inv, toAdd_mul, toAdd_inv, hu₁, toAdd_ofAdd, ← h1, ← sub_eq_add_neg,
      ← QuotientAddGroup.mk_sub, A7.pairVec_sub_pairVec]
  obtain ⟨g₁, hg₁a, hg₁b⟩ := A7.exists_alt_map_pair hab hzx.symm
  obtain ⟨k, hk⟩ := hα g₁
  let u₀ : blockU K := ⟨(k : G)⁻¹ * (v : G) * (k : G), by
    have h := (Subgroup.mem_normalizer_iff.mp (hKU (K.inv_mem k.2)) v).mp v.2
    simpa using h⟩
  have hβu₀ : Multiplicative.toAdd (β u₀) =
      (QuotientAddGroup.mk (A7.pairVec a b) : AltHeart 7) := by
    have h2 := hequiv k⁻¹ v u₀ (by simp [u₀]) (A7.pairVec x z) hβv.symm
    rw [A7.permWeight_pairVec] at h2
    have hk1 : ((α k⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        (g₁ : Equiv.Perm (Fin 7))⁻¹ := by
      rw [map_inv, hk]
      rfl
    have e1 : (g₁ : Equiv.Perm (Fin 7))⁻¹ x = a := Equiv.Perm.inv_eq_iff_eq.mpr hg₁a.symm
    have e2 : (g₁ : Equiv.Perm (Fin 7))⁻¹ z = b := Equiv.Perm.inv_eq_iff_eq.mpr hg₁b.symm
    rw [hk1, e1, e2] at h2
    exact h2.symm
  have hkerL : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)),
      αL.ker.map (conjOn L x hx).toMonoidHom = αL.ker := by
    intro x hx
    rw [hkerαL]
    exact (Subgroup.characteristic_iff_map_eq.mp inferInstance) (conjOn L x hx)
  let ψ : T →* MulAut (alternatingGroup (Fin 5)) :=
    { toFun := fun x => inducedAut αL hαL x (hTL x.2) (hkerL x (hTL x.2))
      map_one' := by
        apply MulEquiv.ext
        intro y
        obtain ⟨l, rfl⟩ := hαL y
        rw [inducedAut_apply, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        simp [conjOn_apply]
      map_mul' := by
        intro x y
        apply MulEquiv.ext
        intro w
        obtain ⟨l, rfl⟩ := hαL w
        rw [MulAut.mul_apply, inducedAut_apply, inducedAut_apply, inducedAut_apply]
        congr 1
        apply Subtype.ext
        simp [conjOn_apply, mul_assoc] }
  have hψapp : ∀ (x : T) (l : L), ψ x (αL l) = αL (conjOn L x (hTL x.2) l) := fun x l =>
    inducedAut_apply αL hαL x (hTL x.2) (hkerL x (hTL x.2)) l
  have hψ1 : ∀ x : T, ψ x = 1 ↔ (x : G) ∈ Rp := by
    intro x
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      show (x : G) ∈ centralizerSection M L (pCoreOf 2 L)
      rw [mem_centralizerSection_iff_of_le (pCoreOf_le 2 L)]
      refine ⟨sk.base.hyp.T_le x.2, fun l hl => ?_⟩
      have h1 : ψ x (αL ⟨l, hl⟩) = αL ⟨l, hl⟩ := by rw [hx]; rfl
      rw [hψapp] at h1
      have h2 : αL (conjOn L x (hTL x.2) ⟨l, hl⟩ * (⟨l, hl⟩ : L)⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      rw [← MonoidHom.mem_ker, hkerαL] at h2
      have h3 := (pCoreOf 2 L).inv_mem ((mem_pCoreOf_iff' _).mpr h2)
      have e : ((conjOn L x (hTL x.2) ⟨l, hl⟩ * (⟨l, hl⟩ : L)⁻¹ : L) : G)⁻¹ =
          l * x * l⁻¹ * (x : G)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, conjOn_apply]
        group
      rwa [e] at h3
    · intro hx
      apply MulEquiv.ext
      intro y
      obtain ⟨l, rfl⟩ := hαL y
      rw [hψapp, MulAut.one_apply]
      have hx2 : (x : G) ∈ centralizerSection M L (pCoreOf 2 L) := hx.2
      have h1 := ((mem_centralizerSection_iff_of_le (pCoreOf_le 2 L)).mp hx2).2 l l.2
      have h2 : (conjOn L x (hTL x.2) l * l⁻¹ : L) ∈ CFSG.pCore 2 L := by
        apply (mem_pCoreOf_iff' _).mp
        have e : ((conjOn L x (hTL x.2) l * l⁻¹ : L) : G) =
            ((l : G) * x * (l : G)⁻¹ * (x : G)⁻¹)⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, conjOn_apply]
          group
        rw [e]
        exact (pCoreOf 2 L).inv_mem h1
      rw [← hkerαL, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h2
      exact h2
  have hT2 : IsPGroup 2 T := sk.base.hyp.sylow.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψ8 : Nat.card ψ.range ≤ 8 := by
    have hdvd : Nat.card ψ.range ∣ 120 := by
      rw [← A7.card_mulAut_alt5]
      exact Subgroup.card_subgroup_dvd_card _
    have h2 : IsPGroup 2 ψ.range := by
      rw [MonoidHom.range_eq_map]
      exact (hT2.to_subgroup ⊤).map ψ
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h2
    rw [hm] at hdvd ⊢
    have hm3 : m ≤ 3 := by
      by_contra hm3
      push Not at hm3
      have h16 : 2 ^ 4 ∣ 2 ^ m := pow_dvd_pow 2 hm3
      exact absurd (h16.trans hdvd) (by decide)
    calc 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hm3
      _ = 8 := by norm_num
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    sk.base.le_normalizer_of_cComp hR hC h37 h38 h39 sk.cComp sk.S_le_normalizer
  have hSKsyl : IsSylowTwoOf (S ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal (sk.base.isSylowTwoOf_S_H hR hC h37 h38 h39)
      (le_of_mem_cComp sk.cComp) hHK
  have hSKT : S ⊓ K ≤ T := inf_le_left.trans inf_le_left
  set ψ₁ : ↥(S ⊓ K) →* MulAut (alternatingGroup (Fin 5)) :=
    ψ.comp (Subgroup.inclusion hSKT) with hψ₁
  set α₁ : ↥(S ⊓ K) →* alternatingGroup (Fin 7) :=
    α.comp (Subgroup.inclusion (inf_le_right : S ⊓ K ≤ K)) with hα₁
  have hker₁ : ψ₁.ker = α₁.ker := by
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have hRp' : (s : G) ∈ Rp := (hψ1 (Subgroup.inclusion hSKT s)).mp h
      have hRp2 : (s : G) ∈ centralizerSection M L (pCoreOf 2 L) := hRp'.2
      apply A7.eq_one_of_commute_fixSet hab
      intro c hc
      obtain ⟨l, rfl⟩ : c ∈ φ.range := hrange ▸ hc
      have h1 := ((mem_centralizerSection_iff_of_le (pCoreOf_le 2 L)).mp hRp2).2 l l.2
      have h2 : ((Subgroup.inclusion hLK l * Subgroup.inclusion inf_le_right s *
          (Subgroup.inclusion hLK l)⁻¹ * (Subgroup.inclusion inf_le_right s)⁻¹ : K) : G) ∈
            pCoreOf 2 K := hO2LK h1
      rw [mem_pCoreOf_iff', ← hkerα, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv,
        map_inv] at h2
      show α₁ s * φ l = φ l * α₁ s
      have e : φ l * α₁ s * (φ l)⁻¹ * (α₁ s)⁻¹ = 1 := h2
      calc α₁ s * φ l = (φ l * α₁ s * (φ l)⁻¹ * (α₁ s)⁻¹)⁻¹ * (φ l * α₁ s) := by group
        _ = φ l * α₁ s := by rw [e, inv_one, one_mul]
    · intro h
      apply (hψ1 (Subgroup.inclusion hSKT s)).mpr
      refine ⟨hSKT s.2, ?_⟩
      show (s : G) ∈ centralizerSection M L (pCoreOf 2 L)
      rw [mem_centralizerSection_iff_of_le (pCoreOf_le 2 L)]
      refine ⟨sk.base.hyp.T_le (hSKT s.2), fun l hl => ?_⟩
      have hsQ : (s : G) ∈ pCoreOf 2 K := by
        have h1 : Subgroup.inclusion inf_le_right s ∈ α.ker := h
        rw [hkerα] at h1
        exact (mem_pCoreOf_iff' _).mpr h1
      have hmemL : (l : G) * s * l⁻¹ * (s : G)⁻¹ ∈ L := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (hSL s.2.1) l⁻¹).mp (L.inv_mem hl)
        have e : (l : G) * s * l⁻¹ * (s : G)⁻¹ = l * (s * l⁻¹ * (s : G)⁻¹) := by group
        rw [e]
        exact L.mul_mem hl h1
      have hmemQ : (l : G) * s * l⁻¹ * (s : G)⁻¹ ∈ pCoreOf 2 K := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K (hLK hl)) s).mp hsQ
        exact (pCoreOf 2 K).mul_mem this ((pCoreOf 2 K).inv_mem hsQ)
      have hk1 : (⟨(l : G) * s * l⁻¹ * (s : G)⁻¹, hmemL⟩ : L) ∈ φ.ker := by
        show α (Subgroup.inclusion hLK ⟨_, hmemL⟩) = 1
        rw [← MonoidHom.mem_ker, hkerα]
        exact (mem_pCoreOf_iff' _).mp hmemQ
      rw [hkerφeq] at hk1
      exact (mem_pCoreOf_iff' _).mpr hk1
  have hα₁8 : Nat.card α₁.range = 8 := by
    apply A7.card_eq_eight_of_isPGroup
    · rw [MonoidHom.range_eq_map]
      exact (hSKsyl.2.1.to_subgroup ⊤).map α₁
    · intro h2
      apply hSKsyl.2.2
      have h3 : α₁.range = ((S ⊓ K).subgroupOf K).map α := by
        rw [hα₁, MonoidHom.range_comp, Subgroup.inclusion_range]
      rw [h3] at h2
      exact h2.trans (Subgroup.index_map_dvd _ hα)
  have hψ₁8 : Nat.card ψ₁.range = 8 := by
    rw [← hα₁8]
    exact Nat.card_congr ((QuotientGroup.quotientKerEquivRange ψ₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker₁).trans
        (QuotientGroup.quotientKerEquivRange α₁))).toEquiv
  have hψrange : ψ₁.range = ψ.range := by
    have hle : ψ₁.range ≤ ψ.range := by
      rintro _ ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hψ₁8]; exact hψ8)
  have hTSR : ∀ x ∈ T, ∃ s ∈ S, s⁻¹ * x ∈ Rp := by
    intro x hx
    obtain ⟨s, hs⟩ : ψ ⟨x, hx⟩ ∈ ψ₁.range := hψrange ▸ ⟨⟨x, hx⟩, rfl⟩
    refine ⟨s, s.2.1, ?_⟩
    have h1 : ψ (Subgroup.inclusion hSKT s)⁻¹ * ψ ⟨x, hx⟩ = 1 := by
      rw [map_inv]
      rw [show ψ (Subgroup.inclusion hSKT s) = ψ₁ s from rfl, hs, inv_mul_cancel]
    rw [← map_mul] at h1
    exact (hψ1 _).mp h1
  have hRpS : ¬ Rp ≤ S := by
    intro hle
    apply (sk.base.S_lt_T h37 h38 h39).not_ge
    intro x hx
    obtain ⟨s, hs, hsx⟩ := hTSR x hx
    have := S.mul_mem hs (hle hsx)
    rwa [mul_inv_cancel_left] at this
  have hR43 : R = S ⊓ Rp := sk.base.lemma_4_3_4
  have hRRp : R < Rp := by
    refine lt_of_le_of_ne (hR43 ▸ inf_le_right) fun h => hRpS ?_
    rw [← h, hR43]
    exact inf_le_left
  have hRS : R ≤ S := sk.base.pCoreOf_le_S
  have hKS : K ⊔ S ≤ Subgroup.normalizer (K : Set G) := _root_.sup_le Subgroup.le_normalizer hSK
  have hSRp : S ≤ Subgroup.normalizer (Rp : Set G) := inf_le_left.trans sk.base.le_normalizer_Rp
  have hSR : S ≤ Subgroup.normalizer (R : Set G) := by
    intro x hx
    rw [hR43]
    exact mem_normalizer_inf (Subgroup.le_normalizer hx) (hSRp hx)
  have hS2 : IsPGroup 2 S := hT2.to_le inf_le_left
  have hRp2 : IsPGroup 2 Rp := hT2.to_le inf_le_left
  have hKH : K ≤ H := le_of_mem_cComp sk.cComp
  have hSsylKS : IsSylowTwoOf S (K ⊔ S) :=
    isSylowTwoOf_of_le_of_le (sk.base.isSylowTwoOf_S_H hR hC h37 h38 h39) le_sup_right
      (_root_.sup_le hKH inf_le_right)
  have hO2KS : pCoreOf 2 (K ⊔ S) ≤ R := by
    have h1 : pCoreOf 2 (K ⊔ S) ≤ S := pCoreOf_two_le_of_isSylowTwoOf hSsylKS
    rw [hR43]
    refine le_inf h1 (le_inf (h1.trans inf_le_left) ?_)
    intro x hx
    show x ∈ centralizerSection M L (pCoreOf 2 L)
    rw [mem_centralizerSection_iff_of_le (pCoreOf_le 2 L)]
    refine ⟨sk.base.hyp.T_le (h1 hx).1, fun l hl => ?_⟩
    have hmemL : l * x * l⁻¹ * x⁻¹ ∈ L := by
      have h2 := (Subgroup.mem_normalizer_iff.mp (hSL (h1 hx)) l⁻¹).mp (L.inv_mem hl)
      have e : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by group
      rw [e]
      exact L.mul_mem hl h2
    have hmemQ : l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 (K ⊔ S) := by
      have h2 := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 (K ⊔ S) (Subgroup.mem_sup_left (hLK hl))) x).mp hx
      exact (pCoreOf 2 (K ⊔ S)).mul_mem h2 ((pCoreOf 2 (K ⊔ S)).inv_mem hx)
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun l' hl' => mem_normalizer_inf (Subgroup.le_normalizer hl')
        (le_normalizer_pCoreOf 2 (K ⊔ S) (Subgroup.mem_sup_left (hLK hl'))))
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right) ⟨hmemL, hmemQ⟩
  have hO2KR : pCoreOf 2 (K ⊔ R) ≤ R := by
    refine le_trans ?_ hO2KS
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (sup_le_sup_left hRS K)) ?_
      (pCoreOf_isPGroup 2 _)
    refine _root_.sup_le (fun k hk => le_normalizer_pCoreOf 2 (K ⊔ R) (Subgroup.mem_sup_left hk))
      (fun s hs => normalizer_le_normalizer_pCoreOf 2 (K ⊔ R) ?_)
    apply mem_normalizer_of_map_conj_le
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hSK hs),
      map_conj_eq_of_mem_normalizer (hSR hs)]
  have hU1 : blockU K ≠ ⊥ := blockU_ne_bot hperf (ne_bot_of_mem_cComp sk.cComp) hchar
  have hUab : ∀ u ∈ blockU K, ∀ u' ∈ blockU K, u * u' = u' * u := fun u hu u' hu' =>
    (Subgroup.mem_centralizer_iff.mp (hshort.2.2.1.1 hu).2 u' (hUQ hu')).symm
  have hUel : IsElemAbelian 2 (blockU K) :=
    ⟨⟨⟨fun x y => Subtype.ext (hUab _ x.2 _ y.2)⟩⟩, hshort.2.2.1.2⟩
  have hsub : (K.subgroupOf (K ⊔ S)).IsSubnormal :=
    (Subgroup.normal_subgroupOf_of_le_normalizer hKS).isSubnormal
  have hcent : ∀ r ∈ R, (∀ l ∈ K, l * r * l⁻¹ * r⁻¹ ∈ pCoreOf 2 K) →
      r ∈ pCoreOf 2 (K ⊔ S) := by
    intro r hr hrc
    set C := centralizerSection (K ⊔ S) K (pCoreOf 2 K) with hC
    have hrC : r ∈ C := (mem_centralizerSection_iff_of_le (pCoreOf_le 2 K)).mpr
      ⟨Subgroup.mem_sup_right (hRS hr), hrc⟩
    have hC2 : IsPGroup 2 C := by
      rintro ⟨x, hx⟩
      have hxKS := (mem_centralizerSection_iff_of_le (pCoreOf_le 2 K)).mp hx
      have hx' : x ∈ (K : Set G) * (S : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left K S hSK]
        exact hxKS.1
      obtain ⟨k, hk, s, hs, rfl⟩ := hx'
      obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
      have hsm : s ^ 2 ^ m = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      obtain ⟨k', hk', hkk'⟩ := exists_pow_eq_mul_of_mem_normalizer (hSK hs) hk (2 ^ m)
      rw [hsm, mul_one] at hkk'
      have hk'C : k' ∈ C := by
        rw [← hkk']
        exact C.pow_mem hx _
      have hk'Q : k' ∈ pCoreOf 2 K := by
        have h1 := (mem_centralizerSection_iff_of_le (pCoreOf_le 2 K)).mp hk'C
        have h2 : α ⟨k', hk'⟩ = 1 := by
          have hc : ∀ g : alternatingGroup (Fin 7), α ⟨k', hk'⟩ * g = g * α ⟨k', hk'⟩ := by
            intro g
            obtain ⟨l, rfl⟩ := hα g
            have h3 := h1.2 l l.2
            have h4 : (l * ⟨k', hk'⟩ * l⁻¹ * (⟨k', hk'⟩ : K)⁻¹ : K) ∈ α.ker := by
              rw [hkerα]
              exact (mem_pCoreOf_iff' _).mp h3
            simp only [MonoidHom.mem_ker, map_mul, map_inv] at h4
            calc α ⟨k', hk'⟩ * α l =
                (α l * α ⟨k', hk'⟩ * (α l)⁻¹ * (α ⟨k', hk'⟩)⁻¹)⁻¹ * (α l * α ⟨k', hk'⟩) := by
                  group
              _ = α l * α ⟨k', hk'⟩ := by rw [h4, inv_one, one_mul]
          exact A7.eq_one_of_commute_fixSet hab _ fun c _ => hc c
        have h3 : (⟨k', hk'⟩ : K) ∈ α.ker := h2
        rw [hkerα] at h3
        exact (mem_pCoreOf_iff' _).mpr h3
      obtain ⟨m', hm'⟩ := (pCoreOf_isPGroup 2 K) ⟨k', hk'Q⟩
      refine ⟨m + m', Subtype.ext ?_⟩
      have := congrArg Subtype.val hm'
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this ⊢
      rw [pow_add, pow_mul, hkk', this]
    refine le_pCoreOf_of_le_normalizer 2 (centralizerSection_le_left _ _ _) ?_ hC2 hrC
    intro x hx
    exact le_normalizer_centralizerSection (K ⊔ S) K ⟨hx, hKS hx⟩
  have hII : ∀ R₀ : Subgroup G, R₀ ≠ ⊥ → R₀ ≤ R → K ⊔ S ≤ Subgroup.normalizer (R₀ : Set G) →
      Rp ⊓ Subgroup.normalizer (R₀ : Set G) = R := by
    intro R₀ hR₀ hR₀R hKSR₀
    have hT₀ : T ⊓ Subgroup.normalizer (R₀ : Set G) = S := by
      refine le_antisymm ?_ (le_inf inf_le_left (le_sup_right.trans hKSR₀))
      by_contra hne
      have hlt : S < T ⊓ Subgroup.normalizer (R₀ : Set G) :=
        lt_of_le_of_ne (le_inf inf_le_left (le_sup_right.trans hKSR₀))
          (fun h => hne (h ▸ le_rfl))
      have hU := sk.base.lemma_4_3_3_a hlt inf_le_left
      have hN := isUniqueM_normalizer_le hU hR₀ (hS2.to_le (hR₀R.trans hRS))
        (_root_.sup_le ((hLK.trans le_sup_left).trans hKSR₀) inf_le_right)
      exact sk.not_le (le_inf hKH ((le_sup_left.trans hKSR₀).trans hN))
    calc Rp ⊓ Subgroup.normalizer (R₀ : Set G) =
        Rp ⊓ (T ⊓ Subgroup.normalizer (R₀ : Set G)) := by
          rw [← inf_assoc, inf_eq_left.mpr (inf_le_left : Rp ≤ T)]
      _ = Rp ⊓ S := by rw [hT₀]
      _ = R := by rw [hR43, inf_comm]
  have h623 : ∀ R₀ : Subgroup G, R₀ ≠ ⊥ → R₀ ≤ R →
      K ⊔ S ≤ Subgroup.normalizer (R₀ : Set G) →
      ¬ Rp ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (R₀ : Set G) := by
    intro R₀ hR₀ hR₀R hKSR₀ hle
    obtain ⟨y, hyRp, hyN, hyR⟩ := A4.exists_mem_normalizer_not_mem hRp2 hRRp
    have hy : y ∈ Rp ⊓ Subgroup.normalizer (R₀ : Set G) := ⟨hyRp, hle ⟨hyRp, hyN⟩⟩
    rw [hII R₀ hR₀ hR₀R hKSR₀] at hy
    exact hyR hy
  have hLRp : L ≤ Subgroup.normalizer (Rp : Set G) :=
    le_sup_left.trans (sk.base.hyp421.sup_le_normalizer_Rp sk.base.hyp.normal)
  have hO2KR' : pCoreOf 2 K ≤ R :=
    (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
      (hKS.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)).trans hO2KS
  have hIII : oTwoUpper (K ⊓ Subgroup.normalizer (R : Set G)) ≤
      Subgroup.normalizer (Rp : Set G) := by
    apply (Subgroup.closure_le _).mpr
    rintro y ⟨⟨hyK, hyN⟩, hyodd⟩
    have hc := hcomm ⟨y, hyK⟩ hyN
    have hodd : Odd (orderOf (α ⟨y, hyK⟩ : Equiv.Perm (Fin 7))) := by
      have h1 : orderOf (α ⟨y, hyK⟩ : Equiv.Perm (Fin 7)) ∣ orderOf y := by
        have h2 := orderOf_map_dvd ((alternatingGroup (Fin 7)).subtype.comp α) ⟨y, hyK⟩
        have h3 : orderOf (⟨y, hyK⟩ : K) = orderOf y := (Subgroup.orderOf_coe _).symm
        rw [← h3]
        exact h2
      exact hyodd.of_dvd_nat h1
    have hfix : (α ⟨y, hyK⟩ : Equiv.Perm (Fin 7)) a = a ∧
        (α ⟨y, hyK⟩ : Equiv.Perm (Fin 7)) b = b := by
      rcases A7.fix_or_swap_of_commute hab hc with h | ⟨h1, h2⟩
      · exact h
      · exfalso
        set g := (α ⟨y, hyK⟩ : Equiv.Perm (Fin 7))
        have hpow : ∀ j : ℕ, (g ^ (2 * j + 1)) a = b := by
          intro j
          induction j with
          | zero => simpa using h1
          | succ j ih =>
            rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, pow_add, Equiv.Perm.mul_apply,
              pow_two, Equiv.Perm.mul_apply, h1, h2, ih]
        obtain ⟨j, hj⟩ := hodd
        have h3 := hpow j
        rw [← hj, pow_orderOf_eq_one, Equiv.Perm.one_apply] at h3
        exact hab h3
    have hmem : α ⟨y, hyK⟩ ∈ φ.range := by
      rw [hrange]
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hfix.1
      · exact hfix.2
    obtain ⟨l, hl⟩ := hmem
    have hq : (Subgroup.inclusion hLK l)⁻¹ * ⟨y, hyK⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have : α (Subgroup.inclusion hLK l) = α ⟨y, hyK⟩ := hl
      rw [this, inv_mul_cancel]
    rw [hkerα] at hq
    have hqQ := (mem_pCoreOf_iff' _).mpr hq
    have e : y = (l : G) * (((Subgroup.inclusion hLK l)⁻¹ * ⟨y, hyK⟩ : K) : G) := by
      simp
    rw [e]
    exact Subgroup.mul_mem _ (hLRp l.2)
      (Subgroup.le_normalizer ((hO2KR'.trans hRRp.le) hqQ))
  have hC64 := h64 G K R S Rp hRK hO2KR hU1 hUel hS2 hRS hSR hSRp hsub h623 hSK hshort α β hα
    hkerα hβ hkerβ hequiv a b hab hRact ⟨r₀, hr₀R, hr₀⟩ hO2KS hcent hII hRp2 hIII u₀ hβu₀
  have hUK : blockU K ≤ K := hUQ.trans (pCoreOf_le 2 K)
  have hz : ∀ l : L, (l : G) * u₀ * (l : G)⁻¹ * (u₀ : G)⁻¹ ∈ blockZ K := by
    intro l
    let w : blockU K := ⟨(l : G) * u₀ * (l : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hLU l.2) u₀).mp u₀.2⟩
    have h1 := hequiv (Subgroup.inclusion hLK l) u₀ w rfl (A7.pairVec a b) hβu₀.symm
    have hfa : ((α (Subgroup.inclusion hLK l) : alternatingGroup (Fin 7)) :
        Equiv.Perm (Fin 7)) a = a := (hφfix l).1
    have hfb : ((α (Subgroup.inclusion hLK l) : alternatingGroup (Fin 7)) :
        Equiv.Perm (Fin 7)) b = b := (hφfix l).2
    rw [A7.permWeight_pairVec, hfa, hfb, ← hβu₀] at h1
    have h2 : w * u₀⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← Multiplicative.toAdd.injective h1,
        mul_inv_cancel]
    rw [hkerβ] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have hzc : ∀ l : L, ∀ g ∈ K, g * ((l : G) * u₀ * (l : G)⁻¹ * (u₀ : G)⁻¹) =
      ((l : G) * u₀ * (l : G)⁻¹ * (u₀ : G)⁻¹) * g := fun l g hg =>
    Subgroup.mem_centralizer_iff.mp (hz l).2 g hg
  let fz : L →* G :=
    { toFun := fun l => (l : G) * u₀ * (l : G)⁻¹ * (u₀ : G)⁻¹
      map_one' := by simp
      map_mul' := fun l l' => by
        obtain ⟨z', hz'⟩ : ∃ z', z' = (l' : G) * u₀ * (l' : G)⁻¹ * (u₀ : G)⁻¹ := ⟨_, rfl⟩
        have hc1 : (l : G) * z' = z' * l := by rw [hz']; exact hzc l' l (hLK l.2)
        have hwK : (l : G) * u₀ * (l : G)⁻¹ * (u₀ : G)⁻¹ ∈ K :=
          K.mul_mem (K.mul_mem (K.mul_mem (hLK l.2) (hUK u₀.2)) (K.inv_mem (hLK l.2)))
            (K.inv_mem (hUK u₀.2))
        have hc2 := hzc l' _ hwK
        rw [← hz'] at hc2
        show ((l * l' : L) : G) * u₀ * ((l * l' : L) : G)⁻¹ * (u₀ : G)⁻¹ =
          ((l : G) * u₀ * (l : G)⁻¹ * (u₀ : G)⁻¹) * ((l' : G) * u₀ * (l' : G)⁻¹ * (u₀ : G)⁻¹)
        rw [← hz', hc2]
        calc ((l * l' : L) : G) * u₀ * ((l * l' : L) : G)⁻¹ * (u₀ : G)⁻¹ =
            (l : G) * ((l' : G) * u₀ * (l' : G)⁻¹ * (u₀ : G)⁻¹) * (l : G)⁻¹ *
              ((l : G) * u₀ * (l : G)⁻¹ * (u₀ : G)⁻¹) := by
              rw [Subgroup.coe_mul]; group
          _ = (l : G) * z' * (l : G)⁻¹ * ((l : G) * u₀ * (l : G)⁻¹ * (u₀ : G)⁻¹) := by
              rw [hz']
          _ = z' * ((l : G) * u₀ * (l : G)⁻¹ * (u₀ : G)⁻¹) := by rw [hc1]; group }
  have hfz : ∀ l : L, fz l = 1 := by
    have hk : commutator L ≤ fz.ker := by
      show ⁅(⊤ : Subgroup L), ⊤⁆ ≤ fz.ker
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hzc g₂ (fz g₁) (hUK (hz g₁).1)
    rw [hLperf] at hk
    exact fun l => hk (Subgroup.mem_top l)
  have hLC : L ≤ Subgroup.centralizer ({(u₀ : G)} : Set G) := by
    intro l hl
    have h1 : (l : G) * u₀ * l⁻¹ * (u₀ : G)⁻¹ = 1 := hfz ⟨l, hl⟩
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact Subgroup.mem_centralizer_singleton_iff.mpr h1
  have hCN : Subgroup.centralizer ({(u₀ : G)} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers (u₀ : G) : Subgroup G) : Set G) := by
    intro g hg
    have hgc : Commute (u₀ : G) g := (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (hgc.zpow_left m).eq
  have hu₀1 : (u₀ : G) ≠ 1 := by
    intro h
    have h1 : β u₀ = 1 := by rw [show u₀ = 1 from Subtype.ext h, map_one]
    rw [h1, toAdd_one] at hβu₀
    exact A7.pairVec_ne_zero hab
      (A7.mk_injective_seven (hβu₀.symm.trans (QuotientAddGroup.mk_zero _).symm))
  have hu₀2 : IsPGroup 2 (Subgroup.zpowers (u₀ : G)) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hshort.2.2.1.2 _ ((blockU K).zpow_mem u₀.2 m)
  have htRp : t ∈ Rp := sk.t_Rp hRRp
  have hX : L ⊔ (T ⊓ H ⊔ Subgroup.zpowers t) ≤
      Subgroup.normalizer ((Subgroup.zpowers (u₀ : G) : Subgroup G) : Set G) :=
    (_root_.sup_le hLC (_root_.sup_le (le_sup_left.trans hC64)
      (Subgroup.zpowers_le.mpr (hC64 (Subgroup.mem_sup_right htRp))))).trans hCN
  have hNM : Subgroup.normalizer ((Subgroup.zpowers (u₀ : G) : Subgroup G) : Set G) ≤ M :=
    isUniqueM_normalizer_le sk.lemma_4_3_5 (Subgroup.zpowers_ne_bot.mpr hu₀1) hu₀2 hX
  have hVC : V ≤ Subgroup.centralizer (Rp : Set G) :=
    ((sk.base.hyp421.V_le sk.base.hyp.normal).trans (A4.omegaOneCenterOf_le_centerOf _)).trans
      (A4.centerOf_le_centralizer _)
  obtain ⟨L', hL'⟩ : ∃ L' : Subgroup G, L' = L.map (MulAut.conj (k : G)).toMonoidHom :=
    ⟨_, rfl⟩
  have hRpL' : Rp ≤ Subgroup.normalizer (L' : Set G) := by
    intro r hr
    have hrv : r * v = v * r := Subgroup.mem_centralizer_iff.mp (hVC hvV) r hr
    have hc : (k : G)⁻¹ * r * k ∈ Subgroup.centralizer ({(u₀ : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      show (k : G)⁻¹ * r * k * ((k : G)⁻¹ * (v : G) * k) =
        (k : G)⁻¹ * (v : G) * k * ((k : G)⁻¹ * r * k)
      calc (k : G)⁻¹ * r * k * ((k : G)⁻¹ * (v : G) * k) = (k : G)⁻¹ * (r * v) * k := by
            group
        _ = (k : G)⁻¹ * (v * r) * k := by rw [hrv]
        _ = (k : G)⁻¹ * (v : G) * k * ((k : G)⁻¹ * r * k) := by group
    have hN : (k : G)⁻¹ * r * k ∈ Subgroup.normalizer (L : Set G) :=
      sk.base.hyp.normal (hNM (hCN hc))
    apply mem_normalizer_of_map_conj_le
    refine le_of_eq ?_
    rw [hL', ← map_conj_mul, show r * (k : G) = (k : G) * ((k : G)⁻¹ * r * k) by group,
      map_conj_mul L (k : G) ((k : G)⁻¹ * r * k), map_conj_eq_of_mem_normalizer hN]
  have hL'K : L' ≤ K := by
    rw [hL']
    rintro _ ⟨l, hl, rfl⟩
    exact K.mul_mem (K.mul_mem k.2 (hLK hl)) (K.inv_mem k.2)
  obtain ⟨J, hJ⟩ : ∃ J : Subgroup G, J = L ⊔ L' := ⟨_, rfl⟩
  have hJK : J ≤ K := by
    rw [hJ]
    exact _root_.sup_le hLK hL'K
  have hnd : [a, b, x, z].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    exact ⟨⟨hab, hxa.symm, hza.symm⟩, ⟨hxb.symm, hzb.symm⟩, hzx.symm⟩
  have hab' : A7.fixSet {a, b} ≤ (J.subgroupOf K).map α := by
    intro c hc
    obtain ⟨l, hl⟩ : c ∈ φ.range := hrange ▸ hc
    refine ⟨Subgroup.inclusion hLK l, ?_, hl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hJ]
    exact Subgroup.mem_sup_left l.2
  have hxz' : A7.fixSet {x, z} ≤ (J.subgroupOf K).map α := by
    intro c hc
    have hcx : (c : Equiv.Perm (Fin 7)) x = x := (A7.mem_fixSet.mp hc) x (by simp)
    have hcz : (c : Equiv.Perm (Fin 7)) z = z := (A7.mem_fixSet.mp hc) z (by simp)
    have e1 : (g₁ : Equiv.Perm (Fin 7))⁻¹ x = a := Equiv.Perm.inv_eq_iff_eq.mpr hg₁a.symm
    have e2 : (g₁ : Equiv.Perm (Fin 7))⁻¹ z = b := Equiv.Perm.inv_eq_iff_eq.mpr hg₁b.symm
    have hc' : g₁⁻¹ * c * g₁ ∈ A7.fixSet {a, b} := by
      refine A7.mem_fixSet.mpr fun w hw => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      show (g₁ : Equiv.Perm (Fin 7))⁻¹ ((c : Equiv.Perm (Fin 7)) ((g₁ : Equiv.Perm (Fin 7)) w)) =
        w
      rcases hw with h | h <;> rw [h]
      · rw [hg₁a, hcx, e1]
      · rw [hg₁b, hcz, e2]
    obtain ⟨l, hl⟩ : g₁⁻¹ * c * g₁ ∈ φ.range := hrange ▸ hc'
    refine ⟨k * Subgroup.inclusion hLK l * k⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hJ]
      refine Subgroup.mem_sup_right ?_
      rw [hL']
      exact ⟨(l : G), l.2, rfl⟩
    · have hl' : α (Subgroup.inclusion hLK l) = g₁⁻¹ * c * g₁ := hl
      rw [map_mul, map_mul, map_inv, hk, hl']
      group
  have htop : (J.subgroupOf K).map α = ⊤ := A7.eq_top_of_fixSet_le hnd _ hab' hxz'
  have hKJQ : ∀ g ∈ K, ∃ j ∈ J, ∃ q ∈ pCoreOf 2 K, g = j * q := by
    intro g hg
    obtain ⟨j, hj, hjg⟩ : α ⟨g, hg⟩ ∈ (J.subgroupOf K).map α := htop ▸ Subgroup.mem_top _
    refine ⟨j, Subgroup.mem_subgroupOf.mp hj, ((j⁻¹ * ⟨g, hg⟩ : K) : G), ?_, by simp⟩
    have h3 : j⁻¹ * ⟨g, hg⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hjg, inv_mul_cancel]
    rw [hkerα] at h3
    exact (mem_pCoreOf_iff' _).mpr h3
  have hZU : blockZ K ≤ blockU K := inf_le_left
  have hZC : blockZ K ≤ Subgroup.centralizer (K : Set G) := inf_le_right
  obtain ⟨J₁, hJ₁⟩ : ∃ J₁ : Subgroup G, J₁ = J ⊔ blockZ K := ⟨_, rfl⟩
  have hJJ₁ : J ≤ J₁ := by
    rw [hJ₁]
    exact le_sup_left
  have hZJ₁ : blockZ K ≤ J₁ := by
    rw [hJ₁]
    exact le_sup_right
  have hJ₁K : J₁ ≤ K := by
    rw [hJ₁]
    exact _root_.sup_le hJK (hZU.trans hUK)
  have hQU : ∀ q ∈ pCoreOf 2 K, ∀ u ∈ blockU K, q * u = u * q := fun q hq u hu =>
    Subgroup.mem_centralizer_iff.mp (hshort.2.2.1.1 hu).2 q hq
  have hKW : K ≤ Subgroup.normalizer ((blockU K ⊓ J₁ : Subgroup G) : Set G) := by
    intro g hg
    obtain ⟨j, hj, q, hq, rfl⟩ := hKJQ g hg
    refine Subgroup.mul_mem _ (mem_normalizer_inf (hKU (hJK hj))
      (Subgroup.le_normalizer (hJJ₁ hj))) ?_
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
    exact (hQU q hq w hw.1).symm
  have hvJ₁ : (v : G) ∈ J₁ := by
    refine hJJ₁ ?_
    rw [hJ]
    exact Subgroup.mem_sup_left (sk.base.hyp421.V_le_L sk.base.hyp.normal hvV)
  have hvZ : (v : G) ∉ blockZ K := by
    intro h
    have h1 : v ∈ β.ker := by
      rw [hkerβ]
      exact Subgroup.mem_subgroupOf.mpr h
    rw [MonoidHom.mem_ker] at h1
    rw [h1, toAdd_one] at hβv
    exact A7.pairVec_ne_zero hzx.symm
      (A7.mk_injective_seven (hβv.symm.trans (QuotientAddGroup.mk_zero _).symm))
  have hUJ₁ : blockU K ≤ J₁ := by
    rcases hshort.2.2.2.2.2 (blockU K ⊓ J₁) (le_inf hZU hZJ₁) inf_le_left hKW with h | h
    · have hv : (v : G) ∈ blockU K ⊓ J₁ := ⟨v.2, hvJ₁⟩
      rw [h] at hv
      exact absurd hv hvZ
    · calc blockU K = blockU K ⊓ J₁ := h.symm
        _ ≤ J₁ := inf_le_right
  have hKJ₁ : K ≤ Subgroup.normalizer (J₁ : Set G) := by
    intro g hg
    obtain ⟨j, hj, q, hq, rfl⟩ := hKJQ g hg
    refine Subgroup.mul_mem _ (Subgroup.le_normalizer (hJJ₁ hj)) ?_
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨y, hy, rfl⟩
    have hc : q * y * q⁻¹ * y⁻¹ ∈ blockU K := by
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hq (hJ₁K hy)
    show q * y * q⁻¹ ∈ J₁
    have e : q * y * q⁻¹ = q * y * q⁻¹ * y⁻¹ * y := by group
    rw [e]
    exact J₁.mul_mem (hUJ₁ hc) hy
  have hKJ₁' : K ≤ J₁ := le_of_noTwoQuotient hshort.1 hKJ₁ (pCoreOf_isPGroup 2 K)
    (pCoreOf_le 2 K) fun g hg => by
      obtain ⟨j, hj, q, hq, e⟩ := hKJQ g hg
      exact ⟨j, hJJ₁ hj, q, hq, e⟩
  have hZJ : blockZ K ≤ Subgroup.normalizer (J : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hJK (hZC hw))
  have hKJZ : ∀ g ∈ K, ∃ j ∈ J, ∃ w ∈ blockZ K, g = j * w := by
    intro g hg
    have hg' : g ∈ (J : Set G) * (blockZ K : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left J (blockZ K) hZJ, ← hJ₁]
      exact hKJ₁' hg
    obtain ⟨j, hj, w, hw, rfl⟩ := hg'
    exact ⟨j, hj, w, hw, rfl⟩
  have hKJ : K ≤ J := by
    refine le_of_noTwoQuotient hshort.1 (fun g hg => ?_)
      ((pCoreOf_isPGroup 2 K).to_le (hZU.trans hUQ)) (hZU.trans hUK) hKJZ
    obtain ⟨j, hj, w, hw, rfl⟩ := hKJZ g hg
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hj) (hZJ hw)
  have hJeq : J = K := le_antisymm hJK hKJ
  have hRpK : Rp ≤ Subgroup.normalizer (K : Set G) := by
    intro r hr
    rw [← hJeq]
    apply mem_normalizer_of_map_conj_le
    rw [hJ, Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hTL hr.1),
      map_conj_eq_of_mem_normalizer (hRpL' hr)]
  have hQ1 : pCoreOf 2 K ≠ ⊥ := fun h => hU1 (le_bot_iff.mp (h ▸ hUQ))
  have hHQ : Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) = H :=
    sk.base.inM.1.2 _ ⟨pCoreOf 2 K, hQ1, pCoreOf_isPGroup 2 K, rfl⟩
      (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K))
  exact hRpS fun r hr => ⟨hr.1, hHQ.le (normalizer_le_normalizer_pCoreOf 2 K (hRpK hr))⟩

end Setting432K

theorem lemma437A7_holds (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h64 : LemmaC64Ten) : Lemma437A7 :=
  fun _ _ _ _ _ _ _ _ _ _ _ sk hchar h41 =>
    sk.not_isA7Block hR hC h37 h38 h39 h64 hchar h41

theorem stmt4_3_2_of_steps'' (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h436 : Lemma436Comp) (hKG : SL3ParabolicAutFact) (h136 : LemmaC136) (h64 : LemmaC64Ten)
    (hEnd : Lemma43End) (_hZ : Gap437Sp4Z) : Stmt4_3_2 :=
  stmt4_3_2_of_steps' hR hC hC48 h36 h37 h38 h39 h436
    (lemma437Sp4_holds hR hC h37 h38 h39 (gap437Sp4Z_of hR hC h37 h38 h39))
    (lemma437A7_holds hR hC h37 h38 h39 h64) hKG h136 hEnd

end CFSG.Quasithin.H13.Ch4
