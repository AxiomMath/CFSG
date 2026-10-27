module

public import CFSG.Quasithin.H13.NQRigidR2bOdd
public import CFSG.Quasithin.H13.NQRigidAsmModule
public import CFSG.Quasithin.SteinbergBQReducibleTwoNormalizers

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup Equiv CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)
open CFSG.Quasithin.SteinbergBQ
  (noncyclic_exponent_prime_projective_linear_three_subgroups_have_reducible_two_normalizers)
open scoped Pointwise IsMulCommutative

theorem exists_invariant_line_of_projectiveSL_three {H : Type} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {D : Subgroup H} (Q : Sylow 2 H) (hQD : (Q : Subgroup H) ≤ D)
    {K : Subgroup H} (hKn : K.Normal) {X : Subgroup H} (hXD : X ≤ D)
    (hXn : (X.subgroupOf D).Normal) (hXK : X ≤ K)
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) {F : Type} [Field F] [Finite F]
    (hFp : ringChar F ≠ p)
    (η : (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) ≃* LinearFlag.projectiveSL 3 F) :
    ∃ W₁ : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)), Nat.card W₁ = p ∧
      ∀ n : normalizer (X : Set H), (n : H) ∈ (Q : Subgroup H) →
        ∀ w ∈ W₁, normalizerFrattiniConj X n w ∈ W₁ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X) := isPGroup_of_exponent hexp
  have := hKn
  obtain ⟨N, hNc, hN, ι, -⟩ := exists_centerPreimage_compat K hKn hp hp2 hZ
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
  obtain ⟨hPX, hPp, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  have hPK : P ≤ K := hPX.trans hXK
  have hDN : D ≤ normalizer (X : Set H) := (normal_subgroupOf_iff_le_normalizer hXD).mp hXn
  obtain ⟨hσinj, -, -, -, -, -, bres, -, -, -, ⟨fW, hfWs, hfW⟩, -⟩ :=
    SteinbergCC.original_local_sylow_prime_action_is_quotient_of_common_normalizer_restriction
      hp hp2 Q hQD hXD hXn hXK hXA hN hP
  set ψ : (K ⧸ N) ≃* LinearFlag.projectiveSL 3 F := ι.symm.trans η with hψ
  set θ : K →* LinearFlag.projectiveSL 3 F := ψ.toMonoidHom.comp (QuotientGroup.mk' N) with hθ
  have hθinj : Function.Injective (θ.comp (P.subgroupOf K).subtype) :=
    ψ.injective.comp hσinj
  have hPexp : ∀ z ∈ P, z ^ p = 1 := pow_eq_one_of_isSylowOf hp hp2 hexp hP
  obtain ⟨Q₀, hQ₀⟩ := hP
  have hbij := NQTerm.sylow_bijective_coreQuot hp2 hXA Q₀
  have hcardP : Nat.card P = Nat.card (X ⧸ CFSG.pCore 2 X) := by
    rw [← hQ₀, card_map_of_injective X.subtype_injective]
    exact Nat.card_congr (Equiv.ofBijective _ hbij)
  have hcardW : p ^ 2 ≤ Nat.card (X ⧸ CFSG.pCore 2 X) := by
    rw [← hW]
    exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  set Pst := (P.subgroupOf K).map θ with hPst
  have hPstmap : Pst = (θ.comp (P.subgroupOf K).subtype).range := by
    rw [hPst, MonoidHom.range_comp, range_subtype]
  have hcardPst : Nat.card Pst = Nat.card P := by
    rw [hPstmap, ← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv]
    exact Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv
  have hPstexp : ∀ y ∈ Pst, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have h1 : x ^ p = 1 := Subtype.ext (by simpa using hPexp _ (mem_subgroupOf.mp hx))
    rw [h1, map_one]
  have hPstc : ¬ IsCyclic Pst := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Pst)
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using hPstexp _ g.2)
    have htop : zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
    have h1 : Nat.card Pst ≤ p := by
      have h2 : Nat.card (zpowers g) = orderOf g := Nat.card_zpowers g
      rw [htop, card_top] at h2
      rw [h2]
      exact orderOf_le_of_pow_eq_one hp.pos hgp
    rw [hcardPst, hcardP] at h1
    have h2 := hcardW.trans h1
    nlinarith [hp.two_le]
  let N₀ : Subgroup H := (Q : Subgroup H) ⊓ normalizer (P : Set H)
  let τ : N₀ →* MulAut (LinearFlag.projectiveSL 3 F) :=
    (MulAut.congr ψ).toMonoidHom.comp
      ((CFSG.SectionRank.Ccomm.autQuotient N).comp (MulAut.conjNormal.comp N₀.subtype))
  have hτ : ∀ (n : N₀) (x : K), τ n (θ x) = θ (MulAut.conjNormal (n : H) x) := by
    intro n x
    change ψ (CFSG.SectionRank.Ccomm.autQuotient N (MulAut.conjNormal (n : H))
      (ψ.symm (ψ (QuotientGroup.mk' N x)))) = ψ (QuotientGroup.mk' N (MulAut.conjNormal (n : H) x))
    rw [MulEquiv.symm_apply_apply, QuotientGroup.mk'_apply, CFSG.SectionRank.Ccomm.autQuotient_mk]
    rfl
  set B := τ.range with hB
  have hB2 : IsPGroup 2 B := by
    rw [hB, MonoidHom.range_eq_map]
    exact ((Q.isPGroup'.to_le inf_le_left).of_equiv Subgroup.topEquiv.symm).map _
  have hBP : ∀ b ∈ B, Pst.map (b : MulAut (LinearFlag.projectiveSL 3 F)).toMonoidHom = Pst := by
    rintro _ ⟨n, rfl⟩
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨MulAut.conjNormal (n : H) x, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf]
        exact (mem_normalizer_iff.mp (mem_inf.mp n.2).2 x).mp (mem_subgroupOf.mp hx)
      · exact (hτ n x).symm
    · exact (card_map_of_injective (f := (τ n).toMonoidHom) (τ n).injective).symm.le
  obtain ⟨-, -, hcard2, -, -, -, -, -, -, hred⟩ :=
    noncyclic_exponent_prime_projective_linear_three_subgroups_have_reducible_two_normalizers
      hp5 hFp Pst hPstc hPstexp
  obtain ⟨P₁, hP₁lt, hP₁card, hP₁B⟩ := hred B hB2 hBP
  have hcardXW : Nat.card (X ⧸ CFSG.pCore 2 X) =
      Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) := by
    rw [hW, ← hcardP, ← hcardPst, hcard2]
  have hWinj : Function.Injective
      (QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X))) :=
    ((Function.Surjective.bijective_of_nat_card_le (QuotientGroup.mk'_surjective _)
      hcardXW.le)).1
  set φ : X →* (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) :=
    (QuotientGroup.mk' _).comp (QuotientGroup.mk' (CFSG.pCore 2 X)) with hφ
  have hφinj : Function.Injective (φ.comp (P.subgroupOf X).subtype) := by
    have hQ' : P.subgroupOf X = (Q₀ : Subgroup X) := by
      rw [← hQ₀]
      exact comap_map_eq_self_of_injective X.subtype_injective _
    have h1 : Function.Injective ((QuotientGroup.mk' (CFSG.pCore 2 X)).comp
        (P.subgroupOf X).subtype) := by
      intro a b hab
      have ha : (a : X) ∈ (Q₀ : Subgroup X) := by
        rw [← hQ']
        exact a.2
      have hb : (b : X) ∈ (Q₀ : Subgroup X) := by
        rw [← hQ']
        exact b.2
      have h2 := hbij.1 (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab
      have h3 : (a : X) = (b : X) := congrArg (fun w : (Q₀ : Subgroup X) => (w : X)) h2
      exact Subtype.ext h3
    exact hWinj.comp h1
  set Q₁ : Subgroup H := ((P.subgroupOf K) ⊓ P₁.comap θ).map K.subtype with hQ₁
  have hQ₁P : Q₁ ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.mp (mem_inf.mp hx).1
  set W₁ := (Q₁.subgroupOf X).map φ with hW₁
  have hQ₁card : Nat.card Q₁ = p := by
    have hmap : ((P.subgroupOf K) ⊓ P₁.comap θ).map θ = P₁ := by
      refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨x, hx, rfl⟩ := hy
        exact (mem_inf.mp hx).2
      · obtain ⟨x, hx, rfl⟩ := hP₁lt.le hy
        exact ⟨x, mem_inf.mpr ⟨hx, hy⟩, rfl⟩
    have hinj : Set.InjOn θ ((P.subgroupOf K) ⊓ P₁.comap θ : Subgroup K) := by
      intro a ha b hb hab
      have h1 := hθinj (a₁ := ⟨a, (mem_inf.mp ha).1⟩) (a₂ := ⟨b, (mem_inf.mp hb).1⟩) hab
      exact congrArg Subtype.val h1
    rw [hQ₁, card_map_of_injective K.subtype_injective, ← hP₁card]
    have h1 : Nat.card ↥(((P.subgroupOf K) ⊓ P₁.comap θ).map θ) =
        Nat.card ↥((P.subgroupOf K) ⊓ P₁.comap θ) := by
      change Nat.card (θ '' (((P.subgroupOf K) ⊓ P₁.comap θ : Subgroup K) : Set K)) = _
      exact Nat.card_image_of_injOn hinj
    rw [← h1, hmap]
  have hW₁inv : ∀ n : normalizer (X : Set H), (n : H) ∈ (Q : Subgroup H) →
      (n : H) ∈ normalizer (P : Set H) → ∀ w ∈ W₁, normalizerFrattiniConj X n w ∈ W₁ := by
    intro n hnQ hnP w hw
    obtain ⟨x, hx, rfl⟩ := hw
    obtain ⟨y, hy, hyx⟩ := mem_subgroupOf.mp hx
    have hyP : (y : H) ∈ P := mem_subgroupOf.mp (mem_inf.mp hy).1
    have hyP₁ : θ y ∈ P₁ := (mem_inf.mp hy).2
    have hnN₀ : (n : H) ∈ N₀ := mem_inf.mpr ⟨hnQ, hnP⟩
    refine ⟨X.normalizerMonoidHom n x, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf]
    refine ⟨MulAut.conjNormal (n : H) y, mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [mem_subgroupOf]
      exact (mem_normalizer_iff.mp hnP y).mp hyP
    · have hb : τ ⟨n, hnN₀⟩ ∈ B := ⟨_, rfl⟩
      have h1 := hP₁B _ hb
      change θ (MulAut.conjNormal (n : H) y) ∈ P₁
      rw [← hτ ⟨n, hnN₀⟩ y, ← h1]
      exact ⟨θ y, hyP₁, rfl⟩
    · change (n : H) * (y : H) * (n : H)⁻¹ = (n : H) * (x : H) * (n : H)⁻¹
      have hyx' : (y : H) = (x : H) := hyx
      rw [hyx']
  have hW₁card : Nat.card W₁ = p := by
    have hQ₁X : Q₁.subgroupOf X ≤ P.subgroupOf X := fun z hz => hQ₁P hz
    have hinj : Set.InjOn φ (Q₁.subgroupOf X : Subgroup X) := by
      intro a ha b hb hab
      have h1 := hφinj (a₁ := ⟨a, hQ₁X ha⟩) (a₂ := ⟨b, hQ₁X hb⟩) hab
      exact congrArg Subtype.val h1
    rw [hW₁, ← hQ₁card]
    have h1 : Nat.card ((Q₁.subgroupOf X).map φ) = Nat.card (Q₁.subgroupOf X) := by
      change Nat.card (φ '' (Q₁.subgroupOf X : Set X)) = _
      exact Nat.card_image_of_injOn hinj
    rw [h1]
    exact Nat.card_congr (subgroupOfEquivOfLe (hQ₁P.trans hPX)).toEquiv
  refine ⟨W₁, hW₁card, fun n hnQ w hw => ?_⟩
  have hnQW : normalizerFrattiniConj X n ∈
      ((Q : Subgroup H).subgroupOf (normalizer (X : Set H))).map (normalizerFrattiniConj X) :=
    ⟨n, mem_subgroupOf.mpr hnQ, rfl⟩
  obtain ⟨z, hz⟩ := hfWs ⟨_, hnQW⟩
  obtain ⟨m, hm⟩ := z.2
  have hzm : z = bres.rangeRestrict m := Subtype.ext hm.symm
  have hmX : (m : H) ∈ normalizer (X : Set H) := hDN (hQD (mem_inf.mp m.2).1)
  have h1 := hfW m hmX
  rw [← hzm, hz] at h1
  have h2 : normalizerFrattiniConj X n w = normalizerFrattiniConj X ⟨(m : H), hmX⟩ w :=
    congrArg (fun φ : MulAut _ => φ w) h1
  rw [h2]
  exact hW₁inv ⟨m, hmX⟩ (mem_inf.mp m.2).1 (mem_inf.mp m.2).2 w hw

variable {G : Type} [Group G] [Finite G]

theorem isFrattiniIrreducible_sylow_of_four {T L M : Subgroup G}
    (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXc : (X.subgroupOf L).Characteristic) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {v : G} (hQ : IsSylowOf 2 (T ⊓ centralizer {v}) (M ⊓ centralizer {v}))
    (hB : ∃ B : Subgroup (L ⧸ CFSG.solvableRadical L),
      B ≤ ((centralizer ({v} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.solvableRadical L)) ∧
      CFSG.IsElementaryAbelian 2 B ∧ Nat.card B = 4) :
    IsFrattiniIrreducible X (T ⊓ centralizer {v} ⊓ L) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.solvableRadical L with hR
  have hLC := NQSetup.isCComponent_top_of_qtnq h
  have hLN : L ≤ normalizer (X : Set G) :=
    le_normalizer.trans (NQSetup.normalizer_le_normalizer_of_characteristic hXL hXc)
  have hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X) := isPGroup_of_exponent hexp
  have : Fact (IsPGroup p (X ⧸ CFSG.pCore 2 X)) := ⟨hXA⟩
  have : IsElementaryAbelian p ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    CFSG.isElementaryAbelian_quotient_frattini
  set β := (normalizerFrattiniConj X).comp (inclusion hLN) with hβ
  have hβ1 : β ≠ 1 := by
    obtain ⟨l, hlL, hl1⟩ := hLW
    intro h1
    apply hl1
    have h2 := DFunLike.congr_fun h1 ⟨l, hlL⟩
    simp only [MonoidHom.one_apply, hβ, MonoidHom.comp_apply] at h2
    rwa [show inclusion hLN ⟨(l : G), hlL⟩ = l from Subtype.ext rfl] at h2
  set α := (NQSetup.mulAutLinear p ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))).comp β
    with hα
  have hα1 : α ≠ 1 := by
    intro h1
    apply hβ1
    ext l w
    have h2 := LinearEquiv.congr_fun (DFunLike.congr_fun h1 l) (Additive.ofMul w)
    exact congrArg Additive.toMul h2
  have hfin := NQSetup.finrank_additive_eq_two hW
  set H₀ : Subgroup L := (centralizer ({v} : Set G)).subgroupOf L with hH₀
  set QL := T ⊓ centralizer ({v} : Set G) ⊓ L with hQLdef
  have hQLL : QL ≤ L := inf_le_right
  have hS : IsSylowOf 2 (QL.subgroupOf L) H₀ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L, map_subgroupOf_eq_of_le hQLL, hH₀,
      subgroupOf_map_subtype, inf_comm]
    exact NQSetup.isSylowOf_inf_of_qtnq h v hQ
  obtain ⟨S, hSeq⟩ := hS.exists_sylow_eq_subgroupOf
  obtain ⟨B, hBH, hBel, hB4⟩ := hB
  have hB2 : IsPGroup 2 B := by
    have := hBel
    exact CFSG.IsElementaryAbelian.isPGroup 2 _
  have hBnc : ¬ IsCyclic B := by
    have := hBel
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) (by rw [hB4]; norm_num)
  have hπ1 : (QuotientGroup.mk' R : L →* L ⧸ R) ≠ 1 := by
    intro h1
    apply hBnc
    have hBb : B = ⊥ := by
      rw [eq_bot_iff]
      rintro b -
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R b
      rw [h1, MonoidHom.one_apply]
      exact one_mem _
    rw [hBb]
    exact isCyclic_of_subsingleton
  have hnc := NQSetup.nontrivial_Ccomponent_images_retain_radical_quotient_Sylow_noncyclicity hLC
    (QuotientGroup.mk' R) hπ1 Nat.prime_two H₀ S ⟨B, hBH, hB2, hBnc⟩
  have hSmap : (S : Subgroup H₀).map ((QuotientGroup.mk' R).comp H₀.subtype) =
      (QL.subgroupOf L).map (QuotientGroup.mk' R) := by
    rw [← map_map, hSeq, subgroupOf_map_subtype, inf_of_le_left]
    intro x hx
    rw [hH₀, mem_subgroupOf]
    exact (mem_inf.mp (mem_inf.mp (mem_subgroupOf.mp hx)).1).2
  rw [hSmap] at hnc
  have hBcop : Nat.Coprime (Nat.card ((QL.subgroupOf L).map (QuotientGroup.mk' R))) p := by
    have h2 : IsPGroup 2 ((QL.subgroupOf L).map (QuotientGroup.mk' R)) := by
      have h3 : IsPGroup 2 (QL.subgroupOf L) :=
        (h.sylow.1.to_le (inf_le_left.trans inf_le_left)).comap_subtype
      exact h3.map _
    obtain ⟨m, hm⟩ := h2.exists_card_eq
    rw [hm]
    exact Nat.Coprime.pow_left m ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))
  intro Y hY
  set U' : Submodule (ZMod p) (Additive ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))) :=
    AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup Y) with hU'
  have hmemU' : ∀ x, x ∈ U' ↔ Additive.toMul x ∈ Y := fun _ => Iff.rfl
  rcases NQSetup.nq_noncyclic_coprime_projective_irreducibility hp5 hLC hfin α hα1
      (QL.subgroupOf L) ⟨_, le_rfl, hnc, hBcop⟩ U' (by
        intro l hl x hx
        rw [hmemU'] at hx ⊢
        exact hY ⟨l, hLN l.2⟩ (mem_subgroupOf.mp hl) _ hx) with h0 | ht
  · left
    rw [eq_bot_iff]
    intro y hy
    have h1 : Additive.ofMul y ∈ U' := (hmemU' _).mpr hy
    rw [h0, Submodule.mem_bot] at h1
    exact (mem_bot).mpr (Additive.ofMul.injective h1)
  · right
    rw [eq_top_iff]
    intro y _
    have h1 : Additive.ofMul y ∈ U' := by rw [ht]; exact Submodule.mem_top
    exact (hmemU' _).mp h1

theorem exists_four_or_deleted_weight_two {T L M : Subgroup G} (h : QTNQ T L M)
    (hmod : QTNQExplicitModule L M) {v : G} (hv : v ∈ qtnqU L M) :
    (∃ B : Subgroup (L ⧸ CFSG.solvableRadical L),
      B ≤ ((centralizer ({v} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.solvableRadical L)) ∧
      CFSG.IsElementaryAbelian 2 B ∧ Nat.card B = 4) ∨
    ∃ (Ω : Type) (_ : Fintype Ω) (_ : DecidableEq Ω), Fintype.card Ω = 5 ∧
      ∃ (β : (L ⧸ CFSG.solvableRadical L) ≃* alternatingGroup Ω)
        (θ : Additive (qtnqU L M) ≃+ evenWeight Ω),
        (∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
          (θ (Additive.ofMul y) : Ω → ZMod 2) =
            permAct (β (l : L ⧸ CFSG.solvableRadical L) : Perm Ω) (θ (Additive.ofMul x))) ∧
        (Finset.univ.filter fun ω =>
          (θ (Additive.ofMul ⟨v, hv⟩) : Ω → ZMod 2) ω ≠ 0).card = 2 := by
  classical
  rcases hmod with ha | ⟨Ω, hΩf, hΩd, hΩ, β, θ, hθ⟩ | hc1 | hc2
  · exact Or.inl (NQSetup.exists_four_of_qtnqNaturalFour h hv ha)
  · by_cases hw : (Finset.univ.filter fun ω =>
      (θ (Additive.ofMul ⟨v, hv⟩) : Ω → ZMod 2) ω ≠ 0).card = 2
    · exact Or.inr ⟨Ω, hΩf, hΩd, hΩ, β, θ, hθ, hw⟩
    · exact Or.inl (exists_four_of_deleted_weight_ne_two h hΩ β θ hθ hv hw)
  · exact Or.inl (NQSetup.exists_four_of_qtnqNaturalThreeDouble h hv hc1)
  · exact Or.inl (NQSetup.exists_four_of_qtnqNaturalThreeExtension h hv hc2)

theorem false_of_linearThree_of_four (hcen : FactCenterOddPart)
    {T L M : Subgroup G} {p : ℕ} {X : Subgroup G} {v : G}
    {K : Subgroup (centralizer ({v} : Set G))} (hcfg : RigidSingleCPUConfig T L M p X v K)
    (hB : ∃ B : Subgroup (L ⧸ CFSG.solvableRadical L),
      B ≤ ((centralizer ({v} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.solvableRadical L)) ∧
      CFSG.IsElementaryAbelian 2 B ∧ Nat.card B = 4) {f : ℕ}
    (hS : StatedClassicalModel ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSL 3 2 f) :
    False := by
  classical
  obtain ⟨h, hmod, hp, hp5, hXL, hXc, hXR, -, hXN, -, hexp, -, hW, hLW, -, hvU, hv1, -, hQM, hQH,
    -, hKn, hX'K, -, -, hKq⟩ := hcfg
  obtain ⟨-, F, _, _, hFcard, ⟨η₀⟩⟩ := hS
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hFp : ringChar F ≠ p := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨n, hr, hrn⟩ := FiniteField.card F (ringChar F)
    rw [← Nat.card_eq_fintype_card, hFcard] at hrn
    have hdvd : ringChar F ∣ 2 ^ f := by
      rw [hrn]
      exact dvd_pow_self _ n.ne_zero
    have hr2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd)
    intro hrp
    exact hp2 (hrp.symm.trans hr2)
  let η : ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃* LinearFlag.projectiveSL 3 F :=
    η₀.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center (n := 3) (K := F)).symm))
  have hXH : X ≤ centralizer ({v} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    obtain ⟨l, hl, rfl⟩ := hXR hx
    exact NQSetup.radical_commute_qtnqVc h hl (NQSetup.qtnqU_le_qtnqVc h hvU)
  have hirr : IsFrattiniIrreducible X (T ⊓ centralizer {v}) :=
    (isFrattiniIrreducible_sylow_of_four h hp hp5 hXL hXc hexp hW hLW hQM hB).mono inf_le_left
  have hMX : M ≤ normalizer (X : Set G) := hXN.ge
  have hX'D : X.subgroupOf (centralizer ({v} : Set G)) ≤
      (M ⊓ centralizer ({v} : Set G)).subgroupOf (centralizer ({v} : Set G)) :=
    fun x hx => mem_subgroupOf.mpr ⟨(hXL.trans h.l_le) (mem_subgroupOf.mp hx), x.2⟩
  have hDN : (M ⊓ centralizer ({v} : Set G)).subgroupOf (centralizer ({v} : Set G)) ≤
      normalizer ((X.subgroupOf (centralizer ({v} : Set G)) :
        Subgroup (centralizer ({v} : Set G))) : Set (centralizer ({v} : Set G))) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hMX (mem_inf.mp (mem_subgroupOf.mp ha)).1) y
  have hX'n : ((X.subgroupOf (centralizer ({v} : Set G))).subgroupOf
      ((M ⊓ centralizer ({v} : Set G)).subgroupOf (centralizer ({v} : Set G)))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hX'D).mpr hDN
  obtain ⟨Q', hQ'⟩ := hQH.exists_sylow_eq_subgroupOf
  have hQ'D : (Q' : Subgroup (centralizer ({v} : Set G))) ≤
      (M ⊓ centralizer ({v} : Set G)).subgroupOf (centralizer ({v} : Set G)) := by
    rw [hQ']
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact ⟨h.t_le hx.1, hx.2⟩
  have hexp' : Monoid.exponent (X.subgroupOf (centralizer ({v} : Set G)) ⧸
      CFSG.pCore 2 (X.subgroupOf (centralizer ({v} : Set G)))) = p := by
    rw [Monoid.exponent_eq_of_mulEquiv (coreQuotEquivSubgroupOf hXH), hexp]
  have hW' : Nat.card ((X.subgroupOf (centralizer ({v} : Set G)) ⧸
      CFSG.pCore 2 (X.subgroupOf (centralizer ({v} : Set G)))) ⧸
        frattini (X.subgroupOf (centralizer ({v} : Set G)) ⧸
          CFSG.pCore 2 (X.subgroupOf (centralizer ({v} : Set G))))) = p ^ 2 := by
    rw [card_frattini_subgroupOf hXH, hW]
  have hHSQ := isSQTKCat_centralizer h hvU hv1
  have hKSQ := isSQTKCat_subgroup_quotient_pCore hHSQ K
  have hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) := hcen _ hKq hKSQ p hp hp5
  obtain ⟨W₁', hW₁'card, hW₁'inv⟩ := exists_invariant_line_of_projectiveSL_three hp hp5 Q' hQ'D
    hKn hX'D hX'n hX'K hexp' hW' hZ hFp η
  set W₁ := W₁'.map (frattiniEquivSubgroupOf hXH).toMonoidHom with hW₁
  have hW₁card : Nat.card W₁ = p := by
    rw [hW₁, card_map_of_injective (f := (frattiniEquivSubgroupOf hXH).toMonoidHom)
      (frattiniEquivSubgroupOf hXH).injective]
    exact hW₁'card
  have hW₁inv : ∀ t : normalizer (X : Set G), (t : G) ∈ T ⊓ centralizer {v} →
      ∀ w ∈ W₁, normalizerFrattiniConj X t w ∈ W₁ := by
    intro t ht w hw
    obtain ⟨w', hw', rfl⟩ := hw
    have htH : (t : G) ∈ centralizer ({v} : Set G) := (mem_inf.mp ht).2
    have htQ' : ((⟨⟨(t : G), htH⟩, mem_normalizer_subgroupOf_of htH t.2⟩ :
        normalizer ((X.subgroupOf (centralizer ({v} : Set G)) :
          Subgroup (centralizer ({v} : Set G))) : Set (centralizer ({v} : Set G)))) :
          centralizer ({v} : Set G)) ∈ (Q' : Subgroup (centralizer ({v} : Set G))) := by
      rw [hQ', mem_subgroupOf]
      exact ht
    exact ⟨_, hW₁'inv _ htQ' w' hw', frattiniEquivSubgroupOf_conj hXH htH t.2 w'⟩
  rcases hirr W₁ hW₁inv with h0 | h1
  · rw [h0, card_bot] at hW₁card
    exact hp.one_lt.ne hW₁card
  · rw [h1, card_top, hW] at hW₁card
    have h2 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega

end CFSG.Quasithin.H13.NQRigid
