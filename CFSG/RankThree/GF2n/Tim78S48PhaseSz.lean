module

public import CFSG.RankThree.GF2n.Tim78S48PhaseSzGrp
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.RankThree.GF2n.Tim78Frattini
import CFSG.RankThree.GF2n.Tim78S48PairQuot
public import CFSG.RankThree.GF2n.Tim78S48PhaseSwap

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_lift_of_odd {Y Z : Type} [Group Y] [Finite Y] [Group Z] (ε : Y →* Z)
    (hε : Function.Surjective ε) (hN : IsPGroup 2 ε.ker) (C : Subgroup Z)
    (hC : Odd (Nat.card C)) :
    ∃ K₁ : Subgroup Y, (∀ k ∈ K₁, ε k ∈ C) ∧ K₁ ⊓ ε.ker = ⊥ ∧ Nat.card K₁ = Nat.card C := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Zc : Subgroup Y := C.comap ε with hZc
  have hkerZ : ε.ker ≤ Zc := fun x hx => by
    rw [hZc, Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact C.one_mem
  set N' : Subgroup Zc := ε.ker.subgroupOf Zc with hN'
  haveI hN'n : N'.Normal := Subgroup.Normal.subgroupOf inferInstance Zc
  let ε' : Zc →* C := (ε.comp Zc.subtype).codRestrict C fun z => z.2
  have hε'ker : ε'.ker = N' := by
    ext z
    simp only [MonoidHom.mem_ker, hN', Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have := congrArg Subtype.val h
      exact this
    · intro h
      exact Subtype.ext h
  have hε's : Function.Surjective ε' := by
    rintro ⟨t, ht⟩
    obtain ⟨y, rfl⟩ := hε t
    exact ⟨⟨y, ht⟩, rfl⟩
  have hidx : N'.index = Nat.card C := by
    rw [← hε'ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hε's, Subgroup.card_top]
  have hN'card : Nat.card N' = Nat.card ε.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerZ).toEquiv
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hN
  have hcop : Nat.Coprime (Nat.card N') N'.index := by
    rw [hN'card, hk, hidx]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hC)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHcard : Nat.card H = Nat.card C := by
    rw [← hidx]; exact (hH.symm.index_eq_card).symm
  have hdisj : Disjoint N' H := hH.disjoint
  refine ⟨H.map Zc.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact h.2
  · rw [eq_bot_iff]
    rintro _ ⟨⟨h, hh, rfl⟩, hker⟩
    have h1 : (h : Zc) ∈ N' := Subgroup.mem_subgroupOf.mpr hker
    have h2 : (h : Zc) ∈ N' ⊓ H := ⟨h1, hh⟩
    rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot, h2]
    rfl
  · rw [Subgroup.card_map_of_injective Zc.subtype_injective, hHcard]

theorem card_ne_one {H : Type*} [Group H] [Finite H] :
    Nat.card {h : H // h ≠ 1} = Nat.card H - 1 := by
  classical
  haveI := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have := Fintype.card_congr (Equiv.optionSubtypeNe (1 : H))
  rw [Fintype.card_option] at this
  omega

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

theorem mem_M_of_conj_into (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) {x : G} (hx : x ∈ T ⊔ conjSubgroup g T)
    (hcon : ∀ t ∈ T, ∃ t' ∈ T, ∃ κ ∈ kernel48 B T g, x⁻¹ * t * x = t' * κ) : x ∈ M := by
  rw [← H.normalizer_B]
  refine Subgroup.mem_normalizer_fintype fun b hb => ?_
  have hyW : x * b * x⁻¹ ∈ B ⊔ conjSubgroup g B :=
    (Subgroup.mem_normalizer_iff.mp (H.X_le_normalizer_W h48 hx) b).mp (Subgroup.mem_sup_left hb)
  refine H.W_cent_T h48 hP hTK _ hyW fun t ht => ?_
  obtain ⟨t', ht', κ, hκ, hconj⟩ := hcon t ht
  have hc1 : t' * b = b * t' := H.T_comm_B ht' hb
  have hc2 : κ * b = b * κ :=
    (Subgroup.mem_centralizer_iff.mp hκ.2 b (Subgroup.mem_sup_left hb)).symm
  have hc3 : (x⁻¹ * t * x) * b = b * (x⁻¹ * t * x) := by
    rw [hconj]
    calc t' * κ * b = t' * (κ * b) := by rw [mul_assoc]
      _ = t' * (b * κ) := by rw [hc2]
      _ = (t' * b) * κ := by rw [mul_assoc]
      _ = (b * t') * κ := by rw [hc1]
      _ = b * (t' * κ) := by rw [mul_assoc]
  calc t * (x * b * x⁻¹) = x * ((x⁻¹ * t * x) * b) * x⁻¹ := by group
    _ = x * (b * (x⁻¹ * t * x)) * x⁻¹ := by rw [hc3]
    _ = (x * b * x⁻¹) * t := by group

theorem card_ge_of_conjugates (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) {m : ℕ}
    (x : Fin m → G) (hx : ∀ i, x i ∈ T ⊔ conjSubgroup g T)
    (hinj : Function.Injective fun i => conjSubgroup (x i) B) :
    m * (Nat.card B - 1) ≤ Nat.card B ^ 2 - 1 := by
  classical
  have hmem : ∀ (i : Fin m) (b : {b : ↥B // b ≠ 1}),
      x i * ((b.1 : ↥B) : G) * (x i)⁻¹ ∈ B ⊔ conjSubgroup g B := fun i b =>
    (Subgroup.mem_normalizer_iff.mp (H.X_le_normalizer_W h48 (hx i)) _).mp
      (Subgroup.mem_sup_left b.1.2)
  have hne : ∀ (i : Fin m) (b : {b : ↥B // b ≠ 1}), x i * ((b.1 : ↥B) : G) * (x i)⁻¹ ≠ 1 := by
    intro i b h
    apply b.2
    apply Subtype.ext
    calc ((b.1 : ↥B) : G) = (x i)⁻¹ * (x i * ((b.1 : ↥B) : G) * (x i)⁻¹) * x i := by group
      _ = 1 := by rw [h]; group
  let φ : Fin m × {b : ↥B // b ≠ 1} → {w : ↥(B ⊔ conjSubgroup g B) // w ≠ 1} := fun p =>
    ⟨⟨x p.1 * ((p.2.1 : ↥B) : G) * (x p.1)⁻¹, hmem p.1 p.2⟩, fun h => hne p.1 p.2
      (congrArg Subtype.val h)⟩
  have hφ : Function.Injective φ := by
    rintro ⟨i, b⟩ ⟨j, b'⟩ h
    have h1 : x i * ((b.1 : ↥B) : G) * (x i)⁻¹ = x j * ((b'.1 : ↥B) : G) * (x j)⁻¹ :=
      congrArg (fun w : {w : ↥(B ⊔ conjSubgroup g B) // w ≠ 1} =>
        ((w.1 : ↥(B ⊔ conjSubgroup g B)) : G)) h
    have hij : i = j := by
      refine hinj (H.conj_B_eq_of_inf_ne_bot fun hbot => hne i b ?_)
      have : x i * ((b.1 : ↥B) : G) * (x i)⁻¹ ∈ conjSubgroup (x i) B ⊓ conjSubgroup (x j) B :=
        ⟨mul_mul_inv_mem_conjSubgroup _ b.1.2, h1 ▸ mul_mul_inv_mem_conjSubgroup _ b'.1.2⟩
      rwa [hbot, Subgroup.mem_bot] at this
    subst hij
    have h2 : ((b.1 : ↥B) : G) = ((b'.1 : ↥B) : G) := by
      have := mul_right_cancel h1
      exact mul_left_cancel this
    exact Prod.ext rfl (Subtype.ext (Subtype.ext h2))
  have hle := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, card_ne_one, card_ne_one, H.card_W h48 hP, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hle
  exact hle

section Cert43


theorem T0_relIndex_le_of_frobenius (h48 : Hyp48 M B T g) {n : ℕ} {K₁ : Subgroup G}
    (hK₁X : K₁ ≤ T ⊔ conjSubgroup g T) (hK₁M : K₁ ≤ M)
    (hT₀e : Assembly.IsElemAbelian 2 (T ⊓ kernel48 B T g))
    (hrel : (T ⊓ kernel48 B T g).relIndex T = 2 ^ n)
    (hK₁card : Nat.card K₁ = 2 ^ n - 1) (hK₁c : ∀ a ∈ K₁, ∀ b ∈ K₁, a * b = b * a)
    (hK₁inf : K₁ ⊓ kernel48 B T g = ⊥)
    (hfrob : ∀ k ∈ K₁, k ≠ 1 → ∀ t ∈ T, (k * t * k⁻¹)⁻¹ * t ∈ T ⊓ kernel48 B T g →
      t ∈ T ⊓ kernel48 B T g) :
    B.relIndex (T ⊓ kernel48 B T g) ≤ 2 ^ n := by
  classical
  set K := kernel48 B T g with hK
  set T₀ := T ⊓ K with hT₀
  have hBT₀ : B ≤ T₀ := le_inf H.B_le_T
    ((le_sup_left : B ≤ B ⊔ conjSubgroup g B).trans (H.W_le_kernel h48))
  by_cases hT₀B : T₀ = B
  · rw [hT₀B, Subgroup.relIndex_self]
    exact Nat.one_le_two_pow
  have hnorm : ¬ M ≤ Subgroup.normalizer (T₀ : Set G) := fun hMn =>
    hT₀B (H.eq_B_of_normal_comm hBT₀ inf_le_left hMn fun a ha b hb =>
      comm_of_isElemAbelian hT₀e ha hb)
  obtain ⟨h, hhM, hh⟩ := SetLike.not_le_iff_exists.mp hnorm
  set E := conjSubgroup h T₀ with hE
  have hhT : h ∈ Subgroup.normalizer (T : Set G) := H.M_le_normalizer_T hhM
  have hET : E ≤ T := by
    intro x hx
    rw [hE, mem_conjSubgroup] at hx
    have h1 : h⁻¹ * x * h ∈ T := hx.1
    have := (Subgroup.mem_normalizer_iff.mp hhT _).mp h1
    rwa [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at this
  have hEe : Assembly.IsElemAbelian 2 E := isElemAbelian_conjSubgroup hT₀e h
  have hEcard : Nat.card E = Nat.card T₀ := card_conjSubgroup h T₀
  have hEne : E ≠ T₀ := fun e => hh (conjSubgroup_eq_self_iff.mp e)
  have hKX : T ⊔ conjSubgroup g T ≤ Subgroup.normalizer (K : Set G) :=
    H.X_le_normalizer_kernel h48
  have hTN : T ≤ Subgroup.normalizer (T₀ : Set G) := fun t ht =>
    mem_normalizer_inf (Subgroup.le_normalizer ht) (hKX (Subgroup.mem_sup_left ht))
  have hK₁T : K₁ ≤ Subgroup.normalizer (T : Set G) := fun k hk => H.M_le_normalizer_T (hK₁M hk)
  have hK₁T₀ : K₁ ≤ Subgroup.normalizer (T₀ : Set G) := fun k hk =>
    mem_normalizer_inf (hK₁T hk) (hKX (hK₁X hk))
  have hK₁inf' : K₁ ⊓ T₀ = ⊥ := by
    rw [eq_bot_iff, ← hK₁inf]
    exact inf_le_inf_left _ inf_le_right
  have key := card_le_of_frobenius (T₀ := T₀) (T := T) (K₁ := K₁) (E := E) inf_le_left hTN hT₀e
    hK₁T hK₁T₀ hrel hK₁card hK₁c hK₁inf' hfrob hET hEe hEcard hEne
  have hCB : T₀ ⊓ Subgroup.centralizer (T : Set G) ≤ B := by
    intro x hx
    have : x ∈ T ⊓ Subgroup.centralizer (T : Set G) := ⟨hx.1.1, hx.2⟩
    rwa [H.inf_centralizer_eq_B H.B_le_T H.T_le_Q H.M_le_normalizer_T] at this
  have hcardle : Nat.card ↥(T₀ ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) ≤ Nat.card B :=
    Subgroup.card_le_of_le hCB
  have hmul : B.relIndex T₀ * Nat.card B = Nat.card T₀ := by
    have := Subgroup.relIndex_mul_card B T₀
    rwa [inf_of_le_left hBT₀] at this
  have hBpos : 0 < Nat.card B := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hBpos
  calc B.relIndex T₀ * Nat.card B = Nat.card T₀ := hmul
    _ ≤ 2 ^ n * Nat.card ↥(T₀ ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) := key
    _ ≤ 2 ^ n * Nat.card B := Nat.mul_le_mul_left _ hcardle

theorem false_of_sz (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) (C : Core48 Q B T g)
    {a : ℕ} (ha : 1 ≤ a) (hrel : (T ⊓ kernel48 B T g).relIndex T = 2 ^ (2 * a + 1))
    [((kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T)).Normal]
    (e : ↥(T ⊔ conjSubgroup g T) ⧸ (kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T) ≃*
      Sz a) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK := C.exists_T_not_kernel
  have hKe := C.phase.1
  have hKp : IsPGroup 2 (kernel48 B T g) := hKe.isPGroup
  have hT₀e : Assembly.IsElemAbelian 2 (T ⊓ kernel48 B T g) := hKe.mono inf_le_right
  have hBK : B ≤ kernel48 B T g :=
    (le_sup_left : B ≤ B ⊔ conjSubgroup g B).trans (H.W_le_kernel h48)
  have hT2 : IsPGroup 2 T := H.isPGroup_Q.to_le H.T_le_Q
  have hfr : inSubgroup frattini T = B :=
    H.frattini_eq_B_of_ne H.B_le_T H.T_le_Q H.M_le_normalizer_T H.B_ne_T
  have hTcomm : ∀ t ∈ T, ∀ t' ∈ T, ⁅t, t'⁆ ∈ B := fun t ht t' ht' => by
    rw [← hfr]; exact commutatorElement_mem_inSubgroup_frattini hT2 ht ht'
  have hTsq : ∀ t ∈ T, t * t ∈ B := fun t ht => by
    rw [← hfr, ← pow_two]; exact sq_mem_inSubgroup_frattini hT2 ht
  let ε : ↥(T ⊔ conjSubgroup g T) →* ↥(Sz a) :=
    e.toMonoidHom.comp (QuotientGroup.mk' ((kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T)))
  have hεs : Function.Surjective ε := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hε1 : ∀ x : ↥(T ⊔ conjSubgroup g T), ε x = 1 ↔ (x : G) ∈ kernel48 B T g := by
    intro x
    show e (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  have hεker : ε.ker = (kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T) := by
    ext x
    rw [MonoidHom.mem_ker, hε1, Subgroup.mem_subgroupOf]
  let E : Subgroup ↥(Sz a) := (T.subgroupOf (T ⊔ conjSubgroup g T)).map ε
  have hEcard : Nat.card E = 2 ^ (2 * a + 1) := by
    have h1 : E = ((T.subgroupOf (T ⊔ conjSubgroup g T)).map (QuotientGroup.mk'
        ((kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T)))).map e.toMonoidHom := by
      rw [Subgroup.map_map]
    rw [h1, Subgroup.card_map_of_injective e.injective]
    exact (relIndex_eq_card_map_mk (G := G) (X := T ⊔ conjSubgroup g T)
      (N := kernel48 B T g) (S := T) le_sup_left).symm.trans hrel
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    have h1 : ε ⁅s, s'⁆ = 1 := (hε1 _).mpr (hBK (hTcomm s.1 hs s'.1 hs'))
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hEsq : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul]
    exact (hε1 _).mpr (hBK (hTsq s.1 hs))
  have hEne : E ≠ ⊥ := by
    intro hb
    have h1 := hEcard
    rw [hb, Subgroup.card_bot] at h1
    have : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
    omega
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hEcard
  obtain ⟨Cs, hCcyc, hCcard, hCnorm, hCfpf⟩ := sz_torus ha E hEc hEsq hEcard
  have hCodd : Odd (Nat.card Cs) := by
    rw [hCcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  have hεkp : IsPGroup 2 ε.ker := by
    rw [hεker]; exact hKp.comap_subtype
  obtain ⟨K₁X, hK₁Xε, hK₁Xinf, hK₁Xcard⟩ := exists_lift_of_odd ε hεs hεkp Cs hCodd
  set K₁ : Subgroup G := K₁X.map (T ⊔ conjSubgroup g T).subtype with hK₁
  have hK₁X : K₁ ≤ T ⊔ conjSubgroup g T := Subgroup.map_subtype_le _
  have hK₁ε : ∀ (k : ↥(T ⊔ conjSubgroup g T)), (k : G) ∈ K₁ → ε k ∈ Cs := by
    intro k hk
    obtain ⟨k', hk', hkk'⟩ := hk
    have : k' = k := Subtype.ext hkk'
    rw [← this]
    exact hK₁Xε k' hk'
  have hK₁card : Nat.card K₁ = 2 ^ (2 * a + 1) - 1 := by
    rw [hK₁, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK₁Xcard, hCcard]
  have hK₁inf : K₁ ⊓ kernel48 B T g = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨k', hk', rfl⟩, hker⟩
    have h1 : k' ∈ K₁X ⊓ ε.ker := ⟨hk', MonoidHom.mem_ker.mpr ((hε1 k').mpr hker)⟩
    rw [hK₁Xinf, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, h1]
    rfl
  have hK₁c : ∀ a ∈ K₁, ∀ b ∈ K₁, a * b = b * a := by
    rintro _ ⟨k₁, hk₁, rfl⟩ _ ⟨l₁, hl₁, rfl⟩
    have : IsCyclic ↥Cs := hCcyc
    have hcc : ε k₁ * ε l₁ = ε l₁ * ε k₁ :=
      congrArg Subtype.val (mul_comm' (⟨ε k₁, hK₁Xε k₁ hk₁⟩ : ↥Cs) ⟨ε l₁, hK₁Xε l₁ hl₁⟩)
    have h1 : ⁅k₁, l₁⁆ ∈ K₁X ⊓ ε.ker := by
      refine ⟨K₁X.mul_mem (K₁X.mul_mem (K₁X.mul_mem hk₁ hl₁) (K₁X.inv_mem hk₁))
        (K₁X.inv_mem hl₁), ?_⟩
      exact MonoidHom.mem_ker.mpr (by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hcc)
    rw [hK₁Xinf, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h1)
  have hK₁M : K₁ ≤ M := by
    intro k hk
    obtain ⟨k₁, hk₁, rfl⟩ := hk
    refine H.mem_M_of_conj_into h48 hP hTK k₁.2 fun t ht => ?_
    have hts : ε ⟨t, Subgroup.mem_sup_left ht⟩ ∈ E := ⟨_, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    have hn : (ε k₁)⁻¹ ∈ Subgroup.normalizer (E : Set ↥(Sz a)) :=
      Subgroup.inv_mem _ (hCnorm (hK₁Xε k₁ hk₁))
    have h1 := (Subgroup.mem_normalizer_iff.mp hn _).mp hts
    obtain ⟨s', hs', hs'e⟩ := h1
    refine ⟨(s' : G), Subgroup.mem_subgroupOf.mp hs', (s' : G)⁻¹ * ((k₁ : G)⁻¹ * t * k₁), ?_, ?_⟩
    · have : ε (s'⁻¹ * (k₁⁻¹ * ⟨t, Subgroup.mem_sup_left ht⟩ * k₁)) = 1 := by
        rw [map_mul, map_inv, hs'e]
        simp only [map_mul, map_inv]
        group
      exact (hε1 _).mp this
    · simp only [Subgroup.coe_subtype]
      group
  have hfrob : ∀ k ∈ K₁, k ≠ 1 → ∀ t ∈ T, (k * t * k⁻¹)⁻¹ * t ∈ T ⊓ kernel48 B T g →
      t ∈ T ⊓ kernel48 B T g := by
    rintro _ ⟨k₁, hk₁, rfl⟩ hk1 t ht hmem
    have hk1' : k₁ ≠ 1 := fun h => hk1 (by rw [h]; rfl)
    have hc1 : ε k₁ ≠ 1 := by
      intro h
      have h2 : k₁ ∈ K₁X ⊓ ε.ker := ⟨hk₁, h⟩
      rw [hK₁Xinf, Subgroup.mem_bot] at h2
      exact hk1' h2
    have hts : ε ⟨t, Subgroup.mem_sup_left ht⟩ ∈ E := ⟨_, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    have h1 : ε ((k₁ * ⟨t, Subgroup.mem_sup_left ht⟩ * k₁⁻¹)⁻¹ * ⟨t, Subgroup.mem_sup_left ht⟩) =
        1 := (hε1 _).mpr hmem.2
    have h2 : ε k₁ * ε ⟨t, Subgroup.mem_sup_left ht⟩ * (ε k₁)⁻¹ =
        ε ⟨t, Subgroup.mem_sup_left ht⟩ := by
      simp only [map_mul, map_inv] at h1
      rw [inv_mul_eq_one] at h1
      exact h1
    have h3 := hCfpf _ (hK₁Xε k₁ hk₁) hc1 _ hts h2
    exact ⟨ht, (hε1 _).mp h3⟩
  have hE2b := H.T0_relIndex_le_of_frobenius h48 hK₁X hK₁M hT₀e hrel hK₁card hK₁c hK₁inf hfrob
  obtain ⟨y, hy⟩ := sz_many_conjugates ha E hEne hE2
  choose xs hxs using fun i => hεs (y i)
  have hconjE : ∀ u : ↥(T ⊔ conjSubgroup g T), conjSubgroup (ε u) E =
      ((conjSubgroup (u : G) T).subgroupOf (T ⊔ conjSubgroup g T)).map ε := by
    intro u
    rw [← map_conjSubgroup]
    congr 1
    ext z
    simp only [mem_conjSubgroup, Subgroup.mem_subgroupOf]
    rfl
  have hinjB : Function.Injective
      fun i => conjSubgroup ((xs i : ↥(T ⊔ conjSubgroup g T)) : G) B := by
    intro i j hij
    apply hy
    have hT : conjSubgroup ((xs i : ↥(T ⊔ conjSubgroup g T)) : G) T =
        conjSubgroup ((xs j : ↥(T ⊔ conjSubgroup g T)) : G) T := H.conj_T_eq_of_conj_B_eq hij
    show conjSubgroup (y i) E = conjSubgroup (y j) E
    rw [← hxs i, ← hxs j, hconjE, hconjE, hT]
  have hcount := H.card_ge_of_conjugates h48 hP (fun i => ((xs i : ↥(T ⊔ conjSubgroup g T)) : G))
    (fun i => (xs i).2) hinjB
  have hq2 : 2 ^ (2 * (2 * a + 1)) ≤ Nat.card B := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card B = m + 1 := ⟨Nat.card B - 1, by have := H.q4; omega⟩
    have hm3 : 3 ≤ m := by have := H.q4; omega
    rw [hm] at hcount ⊢
    have e1 : (m + 1) ^ 2 - 1 = m * (m + 2) := by
      have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
      omega
    rw [Nat.add_sub_cancel, e1] at hcount
    by_contra hlt
    have hlt' : m + 2 ≤ 2 ^ (2 * (2 * a + 1)) := by omega
    nlinarith
  have hE1 := H.cartan_on_quotient
  have hBT₀ : B ≤ T ⊓ kernel48 B T g := le_inf H.B_le_T hBK
  have hmul := Subgroup.relIndex_mul_relIndex B (T ⊓ kernel48 B T g) T hBT₀ inf_le_left
  rw [hrel] at hmul
  have hq'pos : 0 < 2 ^ (2 * a + 1) := by positivity
  have hq'sq : 2 ^ (2 * (2 * a + 1)) = 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := by
    rw [← pow_add]; ring_nf
  have h1 : B.relIndex T ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := by
    rw [← hmul]; exact Nat.mul_le_mul_right _ hE2b
  have h2 : 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) ≤ Nat.card B := hq'sq ▸ hq2
  have h3 : Nat.card B ≤ B.relIndex T := hE1.1
  have hEq : Nat.card B = B.relIndex T := le_antisymm h3 (h1.trans h2)
  have hm0 : B.relIndex (T ⊓ kernel48 B T g) = 2 ^ (2 * a + 1) := by
    have : B.relIndex (T ⊓ kernel48 B T g) * 2 ^ (2 * a + 1) =
        2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := by
      rw [hmul]; exact le_antisymm h1 (h2.trans h3)
    exact Nat.eq_of_mul_eq_mul_right hq'pos this
  have hm0ne : B.relIndex (T ⊓ kernel48 B T g) ≠ 1 := by
    rw [hm0]
    have := Nat.one_lt_two_pow (n := 2 * a + 1) (by omega)
    omega
  have hlt : B < T ⊓ kernel48 B T g :=
    lt_of_le_not_ge hBT₀ fun hle => hm0ne (Subgroup.relIndex_eq_one.mpr hle)
  obtain ⟨x₀, hx₀, hx₀B⟩ := SetLike.exists_of_lt hlt
  exact H.false_of_regular hx₀.1 hx₀B (CFSG.Open.IsElemAbelian.mul_self_eq_one hT₀e hx₀)
    (hE1.2 hEq)

end Cert43

end Hyp4

end CFSG.RankThree.GF2n.Tim78
