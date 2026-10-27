module

public import CFSG.Quasithin.MS93.S4Stmt
public import CFSG.Quasithin.MS93.ML3Facts
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
import CFSG.Quasithin.MS93.S4AM
import CFSG.Quasithin.MS93.S4AEA
import CFSG.Quasithin.Background.SmithA36

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open Matrix

namespace QjAux

section Stabilizer

variable {F : Type} [Field F]

theorem flagSpace_two_eq_ln01 :
    LinearFlag.flagSpace 3 F 2 = (ln01 : Submodule F (Fin 3 → F)) := by
  ext x
  rw [LinearFlag.mem_flagSpace, mem_ln01]
  refine ⟨fun h => h 2 le_rfl, fun h j hj => ?_⟩
  fin_cases j
  · simp at hj
  · simp at hj
  · exact h

theorem isCoatom_stabilizer_ln01 :
    IsCoatom (LinearFlag.stabilizer (ln01 : Submodule F (Fin 3 → F))) := by
  rw [← flagSpace_two_eq_ln01]
  refine ⟨LinearFlag.stabilizer_flagSpace_ne_top (by norm_num) (by norm_num), fun Q hQ => ?_⟩
  exact (LinearFlag.eq_of_stabilizer_flagSpace_le Q hQ.le).resolve_left hQ.ne'

theorem mem_stabilizer_ln01 {g : SL3 F}
    (h : ∀ x : Fin 3 → F, x 2 = 0 → ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 = 0) :
    g ∈ LinearFlag.stabilizer (ln01 : Submodule F (Fin 3 → F)) := by
  refine LinearFlag.mem_stabilizer_of_map_le ?_
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

theorem mulVec_mem_ln01 {g : SL3 F}
    (hg : g ∈ LinearFlag.stabilizer (ln01 : Submodule F (Fin 3 → F))) {x : Fin 3 → F}
    (hx : x ∈ (ln01 : Submodule F (Fin 3 → F))) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ (ln01 : Submodule F (Fin 3 → F)) := by
  rw [LinearFlag.mem_stabilizer] at hg
  rw [← hg]
  exact ⟨x, hx, rfl⟩

theorem sStar_le_stabilizer_ln01 :
    (sStar : Subgroup (SL3 F)) ≤ LinearFlag.stabilizer (ln01 : Submodule F (Fin 3 → F)) := by
  intro g hg
  obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp hg
  refine mem_stabilizer_ln01 fun x hx => ?_
  rw [uniTri_mulVec]
  simpa using hx

theorem rootElt10_mem_stabilizer_ln01 :
    rootElt 1 0 (1 : F) ∈ LinearFlag.stabilizer (ln01 : Submodule F (Fin 3 → F)) := by
  refine mem_stabilizer_ln01 fun x hx => ?_
  rw [rootElt_mulVec (by decide)]
  simp [hx]

theorem normalizer_sStar_le_stabilizer_ln01 :
    Subgroup.normalizer ((sStar : Subgroup (SL3 F)) : Set (SL3 F)) ≤
      LinearFlag.stabilizer (ln01 : Submodule F (Fin 3 → F)) := by
  intro n hn
  have hconj : (sStar : Subgroup (SL3 F)).map (MulAut.conj n).toMonoidHom = sStar := by
    ext g
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hn s).mp hs
    · intro hg
      refine ⟨n⁻¹ * g * n, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) g).mp hg
      simpa using this
  have hC := commN_map_conj n sStar
  rw [hconj, commN_sStar] at hC
  refine mem_stabilizer_ln01 fun x hx => ?_
  have hmem : (Matrix.SpecialLinearGroup.toLin' n) x ∈ (ln01 : Submodule F (Fin 3 → F)) := by
    rw [hC]
    exact Submodule.mem_map_of_mem hx
  have hmem' : (n : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ (ln01 : Submodule F (Fin 3 → F)) := by
    simpa [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply] using hmem
  exact hmem'

theorem mem_qLn_of_fix {g : SL3 F}
    (h0 : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0])
    (h1 : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] = ![0, 1, 0]) : g ∈ qLn := by
  have e0 : ∀ i, (g : Matrix (Fin 3) (Fin 3) F) i 0 = ![1, 0, 0] i := fun i => by
    have := congrFun h0 i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have e1 : ∀ i, (g : Matrix (Fin 3) (Fin 3) F) i 1 = ![0, 1, 0] i := fun i => by
    have := congrFun h1 i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hdet := g.2
  rw [Matrix.det_fin_three] at hdet
  have h00 := e0 0
  have h10 := e0 1
  have h20 := e0 2
  have h01 := e1 0
  have h11 := e1 1
  have h21 := e1 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h00 h10 h20 h01 h11 h21
  rw [h00, h10, h20, h01, h11, h21] at hdet
  have h22 : (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by linear_combination hdet
  rw [mem_qLn_iff_uniTri]
  refine ⟨(g : Matrix (Fin 3) (Fin 3) F) 0 2, (g : Matrix (Fin 3) (Fin 3) F) 1 2, ?_⟩
  apply Subtype.ext
  rw [coe_uniTri]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h20, h01, h11, h21, h22]

theorem stabilizer_ln01_le_normalizer_qLn :
    LinearFlag.stabilizer (ln01 : Submodule F (Fin 3 → F)) ≤
      Subgroup.normalizer ((qLn : Subgroup (SL3 F)) : Set (SL3 F)) := by
  have key : ∀ p ∈ LinearFlag.stabilizer (ln01 : Submodule F (Fin 3 → F)),
      ∀ r ∈ (qLn : Subgroup (SL3 F)), p * r * p⁻¹ ∈ qLn := by
    intro p hp r hr
    have hfix : ∀ v ∈ (ln01 : Submodule F (Fin 3 → F)),
        ((p * r * p⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
      intro v hv
      have hv' : ((p⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈
          (ln01 : Submodule F (Fin 3 → F)) := mulVec_mem_ln01 (inv_mem hp) hv
      have hrv : ((p⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈
          fixN (qLn : Subgroup (SL3 F)) := by
        rw [fixN_qLn]
        exact hv'
      rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hrv r hr,
        Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3, Matrix.one_mulVec]
    exact mem_qLn_of_fix (hfix _ (by simp [mem_ln01])) (hfix _ (by simp [mem_ln01]))
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨key p hp r, fun h => ?_⟩
  have := key p⁻¹ (inv_mem hp) _ h
  simpa [mul_assoc] using this

theorem le_qLn_of_normal [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) {N : Subgroup (SL3 F)}
    (hN : IsPGroup 2 N)
    (hPN : LinearFlag.stabilizer (ln01 : Submodule F (Fin 3 → F)) ≤
      Subgroup.normalizer (N : Set (SL3 F))) : N ≤ qLn := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNS : N ≤ sStar := by
    have hsup : IsPGroup 2 ↥(N ⊔ sStar) :=
      hN.to_sup_of_normal_left' (isPGroup_sStar hF) (sStar_le_stabilizer_ln01.trans hPN)
    have := ((isPGroup_sStar hF).toSylow (not_two_dvd_index_sStar hF)).is_maximal' hsup
      (by rw [IsPGroup.toSylow_coe]; exact le_sup_right)
    rw [IsPGroup.toSylow_coe] at this
    rw [← this]
    exact le_sup_left
  intro y hy
  obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp (hNS hy)
  have hwP : rootElt 1 0 (1 : F) ∈ LinearFlag.stabilizer (ln01 : Submodule F (Fin 3 → F)) :=
    rootElt10_mem_stabilizer_ln01
  have hz : (rootElt 1 0 (1 : F))⁻¹ * uniTri a b c * rootElt 1 0 1 ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hPN (inv_mem hwP)) _).mp hy
    simpa using this
  obtain ⟨a', b', c', hz'⟩ := mem_sStar_iff.mp (hNS hz)
  have heq : uniTri a b c * rootElt 1 0 1 = rootElt 1 0 (1 : F) * uniTri a' b' c' := by
    rw [hz']
    group
  have hv := congrArg (fun g : SL3 F => ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 0) heq
  simp only [coe_mul_SL3, ← Matrix.mulVec_mulVec,
    rootElt_mulVec (show (1 : Fin 3) ≠ 0 by decide), uniTri_mulVec] at hv
  simp at hv
  rw [mem_qLn_iff_uniTri]
  exact ⟨b, c, by rw [hv]⟩

theorem eq_qLn_of_card [Finite F] {A : Subgroup (SL3 F)} (hA : A ≤ sStar)
    (hcA : Nat.card A = Nat.card F ^ 2) (hcf : Nat.card (fixN A) = Nat.card F ^ 2) :
    A = qLn := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hfix : ∀ x ∈ fixN A, x 2 = 0 := by
    intro x hx
    by_contra hx2
    have hAP : A ≤ qPt := by
      intro g hg
      obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp (hA hg)
      have h1 := congrFun (hx _ hg) 1
      rw [uniTri_mulVec] at h1
      have h1' : c * x 2 = 0 := by simpa using h1
      have hc : c = 0 := (mul_eq_zero.mp h1').resolve_right hx2
      exact mem_qPt_iff_uniTri.mpr ⟨a, b, by rw [hc]⟩
    have hAeq : A = qPt := Subgroup.eq_of_le_of_card_ge hAP (by rw [card_qPt, hcA])
    rw [hAeq, fixN_qPt, Module.natCard_eq_pow_finrank (K := F), finrank_pt0, pow_one] at hcf
    have : Nat.card F < Nat.card F ^ 2 := by nlinarith
    omega
  have hle : fixN A ≤ (ln01 : Submodule F (Fin 3 → F)) := fun x hx => hfix x hx
  have heq : fixN A = (ln01 : Submodule F (Fin 3 → F)) := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [finrank_ln01]
    have h2 := card_fixN A
    rw [hcf] at h2
    exact (Nat.pow_right_injective hq h2).symm
  have hAL : A ≤ qLn := by
    intro g hg
    obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp (hA hg)
    have he1 : (![0, 1, 0] : Fin 3 → F) ∈ fixN A := by
      rw [heq]
      simp [mem_ln01]
    have h0 := congrFun (he1 _ hg) 0
    rw [uniTri_mulVec] at h0
    simp at h0
    exact mem_qLn_iff_uniTri.mpr ⟨b, c, by rw [h0]⟩
  exact Subgroup.eq_of_le_of_card_ge hAL (by rw [card_qLn, hcA])

end Stabilizer

section Parabolic

theorem isMaxParabolic2_of_isCoatom {G Y : Type} [Group G] [Group Y] {L S₀ : Subgroup G}
    (hS₀ : IsSylowTwoOf S₀ L) {ψ : ↥L →* Y} (hψ : Function.Surjective ψ) {P : Subgroup Y}
    (hP : IsCoatom P)
    (hN : Subgroup.normalizer (((S₀.subgroupOf L).map ψ : Subgroup Y) : Set Y) ≤ P) :
    IsMaxParabolic2 L ((P.comap ψ).map L.subtype) ∧
      L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ (P.comap ψ).map L.subtype := by
  have hB : L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ (P.comap ψ).map L.subtype := by
    rintro x ⟨hxL, hxN⟩
    have hxN' : x ∈ Subgroup.normalizer (S₀ : Set G) := hxN
    refine ⟨⟨x, hxL⟩, hN ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨x, hxL⟩ * s * ⟨x, hxL⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      have hs' : (s : G) ∈ S₀ := hs
      show ((⟨x, hxL⟩ * s * ⟨x, hxL⟩⁻¹ : ↥L) : G) ∈ S₀
      exact (Subgroup.mem_normalizer_iff.mp hxN' _).mp hs'
    · rintro ⟨s, hs, hsy⟩
      have hy : y = ψ (⟨x, hxL⟩⁻¹ * s * ⟨x, hxL⟩) := by
        rw [map_mul, map_mul, map_inv, hsy]
        group
      rw [hy]
      refine ⟨_, ?_, rfl⟩
      have hs' : (s : G) ∈ S₀ := hs
      show ((⟨x, hxL⟩⁻¹ * s * ⟨x, hxL⟩ : ↥L) : G) ∈ S₀
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxN') _).mp hs'
      simpa [mul_assoc] using this
  have hkP : ∀ k : ↥L, ψ k = 1 → (k : G) ∈ (P.comap ψ).map L.subtype := fun k hk =>
    ⟨k, show ψ k ∈ P by rw [hk]; exact P.one_mem, rfl⟩
  refine ⟨⟨⟨Subgroup.map_subtype_le _, S₀, hS₀, hB⟩, fun heq => hP.1 ?_,
    fun Q hQ hQL hPQ => ?_⟩, hB⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨l, rfl⟩ := hψ y
    have hl : (l : G) ∈ (P.comap ψ).map L.subtype := by rw [heq]; exact l.2
    obtain ⟨l', hl', hll'⟩ := hl
    rw [← Subtype.ext hll']
    exact hl'
  · have hQL' : Q ≤ L := hQ.1
    have hPQ' : P ≤ (Q.subgroupOf L).map ψ := by
      intro y hy
      obtain ⟨l, rfl⟩ := hψ y
      exact ⟨l, hPQ ⟨l, hy, rfl⟩, rfl⟩
    rcases hPQ'.lt_or_eq with hlt | heq'
    · exfalso
      have htop := hP.2 _ hlt
      apply hQL
      refine le_antisymm hQL' (fun x hx => ?_)
      have hy : ψ ⟨x, hx⟩ ∈ (Q.subgroupOf L).map ψ := htop ▸ Subgroup.mem_top _
      obtain ⟨q, hq, hqx⟩ := hy
      have hk : ψ (q⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hqx, inv_mul_cancel]
      have h1 := Q.mul_mem (hq : (q : G) ∈ Q) (hPQ (hkP _ hk))
      simpa using h1
    · refine le_antisymm (fun x hx => ?_) hPQ
      have hy : ψ ⟨x, hQL' hx⟩ ∈ (Q.subgroupOf L).map ψ := ⟨⟨x, hQL' hx⟩, hx, rfl⟩
      rw [← heq'] at hy
      exact ⟨⟨x, hQL' hx⟩, hy, rfl⟩

end Parabolic

section Kernel

variable {G : Type} [Group G]

theorem exists_pow_mem_of_mem_sup {L T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T) {m : G} (hm : m ∈ L ⊔ T) :
    ∃ k : ℕ, m ^ 2 ^ k ∈ L := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L T hT] at hm
  obtain ⟨l, hl, t, ht, rfl⟩ := hm
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have key : ∀ j : ℕ, (l * t) ^ j * (t ^ j)⁻¹ ∈ L := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (l * t) ^ (j + 1) * (t ^ (j + 1))⁻¹ =
          ((l * t) ^ j * (t ^ j)⁻¹) * (t ^ j * l * (t ^ j)⁻¹) := by
        rw [pow_succ, pow_succ]
        generalize (l * t) ^ j = X
        generalize t ^ j = Y
        group
      rw [e]
      refine L.mul_mem ih ?_
      have htj : t ^ j ∈ Subgroup.normalizer (L : Set G) := hT (T.pow_mem ht j)
      exact (Subgroup.mem_normalizer_iff.mp htj l).mp hl
  refine ⟨k, ?_⟩
  have := key (2 ^ k)
  rwa [hk', inv_one, mul_one] at this

theorem relIndex_mul_card_inf' (H K : Subgroup G) :
    H.relIndex K * Nat.card ↥(H ⊓ K) = Nat.card ↥K := by
  rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective K.subtype_injective,
    mul_comm]
  exact (H.subgroupOf K).card_mul_index

variable [Finite G]

theorem ker_le_pCore_of_surjective_sl3 {L : Subgroup G}
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) {ψ : ↥L →* SL3 F} (hψ : Function.Surjective ψ) :
    ψ.ker ≤ CFSG.pCore 2 ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e := specialLinearGroupEquivStatedSL 3 F
  set α : ↥L →* ↥(StatedSL 3 F) := e.toMonoidHom.comp ψ with hα
  have hαs : Function.Surjective α := e.surjective.comp hψ
  have hP₀ : CFSG.pCore 2 ↥L ≤ α.ker := pCore_le_ker_of_surjective_statedSL hαs
  set αb : ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(StatedSL 3 F) := QuotientGroup.lift _ α hP₀
  have hαbs : Function.Surjective αb := by
    intro y
    obtain ⟨l, rfl⟩ := hαs y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hne : αb.ker ≠ ⊤ := by
    intro htop
    obtain ⟨z, hz⟩ := hαbs (e (rootElt 0 1 (1 : F)))
    have h1 : αb z = 1 := (MonoidHom.mem_ker).1 (htop ▸ Subgroup.mem_top z)
    rw [hz, map_eq_one_iff e e.injective] at h1
    exact one_ne_zero ((rootElt_eq_one_iff (by decide) 1).mp h1)
  have hcen : αb.ker ≤ Subgroup.center _ := le_center_of_isQuasisimple hQ hne
  have hodd : ∀ z ∈ αb.ker, Odd (orderOf z) := by
    intro z hz
    have hzc := hcen hz
    obtain ⟨a, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
    set w := z ^ m with hw
    have hwc : w ∈ Subgroup.center _ := Subgroup.pow_mem _ hzc m
    have hw2 : w ^ 2 ^ a = 1 := by
      rw [hw, ← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
    set W : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := Subgroup.zpowers w with hW
    have hWc : W ≤ Subgroup.center _ := Subgroup.zpowers_le.mpr hwc
    have hWn : W.Normal := ⟨fun y hy g => by
      have := Subgroup.mem_center_iff.mp (hWc hy) g
      rw [this, mul_inv_cancel_right]
      exact hy⟩
    have hWp : IsPGroup 2 W := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hw2)
      exact IsPGroup.of_card (n := j) (by rw [hW, Nat.card_zpowers, hj])
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
    have hNn : (W.comap π).Normal := hWn.comap π
    have hNp : IsPGroup 2 (W.comap π) :=
      hWp.comap_of_ker_isPGroup π (by rw [QuotientGroup.ker_mk']; exact isPGroup_cfsgPCore ↥L)
    have hNle : W.comap π ≤ CFSG.pCore 2 ↥L := le_sSup ⟨hNn, hNp⟩
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective w
    have hlN : l ∈ W.comap π := by
      show π l ∈ W
      rw [hπ, QuotientGroup.mk'_apply, hl]
      exact Subgroup.mem_zpowers w
    have hw1 : w = 1 := by
      rw [← hl]
      exact (QuotientGroup.eq_one_iff l).mpr (hNle hlN)
    have hzm : orderOf z ∣ m := orderOf_dvd_of_pow_eq_one (by rw [← hw, hw1])
    exact Odd.of_dvd_nat hm hzm
  have hinj := SmithA36.injective_of_isQuasisimple_statedSL hQ (m := 2) le_rfl
    (SmithA36.ringChar_eq_two_of_card hF) (MulEquiv.refl _) hαbs hodd
  intro l hl
  have h1 : αb (QuotientGroup.mk l) = αb 1 := by
    rw [map_one]
    show α l = 1
    rw [hα, MonoidHom.comp_apply, (MonoidHom.mem_ker).1 hl, map_one]
  exact (QuotientGroup.eq_one_iff l).mp (hinj h1)

variable {M T L : Subgroup G}

theorem inf_centralizer_Uq_eq (h : PUHyp M T L) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) :
    M ⊓ Subgroup.centralizer (Uq M T L : Set G) = pCoreOf 2 M := by
  obtain ⟨⟨n, hn⟩, hφs, -, -, hnat⟩ := hφ
  have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  refine le_antisymm ?_ (le_inf (pCoreOf_le' M) (pCoreOf_le_centralizer_Uq h))
  have hKn : M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (Uq M T L : Set G) :
      Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer
      (le_normalizer_centralizer (le_normalizer_Uq h.le_normalizer))
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hKn ?_
  set ψ : ↥L →* SL3 F := (toSL3 φ).comp (Subgroup.inclusion h.L_le)
  have hψs : Function.Surjective ψ := fun y => by
    obtain ⟨ℓ, hℓL, hℓ⟩ := exists_mem_L_eq h hφs (specialLinearGroupEquivStatedSL 3 F y)
    refine ⟨⟨ℓ, hℓL⟩, ?_⟩
    have e1 : ψ ⟨ℓ, hℓL⟩ = (specialLinearGroupEquivStatedSL 3 F).symm (φ ℓ) := rfl
    rw [e1, hℓ, MulEquiv.symm_apply_apply]
  have hker := ker_le_pCore_of_surjective_sl3 h.quasisimple hF hψs
  rintro ⟨k, hkM, hkC⟩
  obtain ⟨a, ha⟩ := exists_pow_mem_of_mem_sup (h.le.trans h.le_normalizer) h.isPGroup
    (h.eq_sup ▸ hkM)
  have hkaC : k ^ 2 ^ a ∈ Subgroup.centralizer (Uq M T L : Set G) := Subgroup.pow_mem _ hkC _
  have hψ1 : ψ ⟨k ^ 2 ^ a, ha⟩ = 1 := by
    refine (toSL3_eq_one_iff hnat _).mpr fun v hv => ?_
    have := Subgroup.mem_centralizer_iff.mp hkaC v hv
    show k ^ 2 ^ a * v * (k ^ 2 ^ a)⁻¹ = v
    rw [← this, mul_inv_cancel_right]
  obtain ⟨b, hb⟩ := isPGroup_cfsgPCore ↥L ⟨_, hker hψ1⟩
  have hb' : (k ^ 2 ^ a) ^ 2 ^ b = 1 := by
    have := congrArg (fun x : ↥(CFSG.pCore 2 ↥L) => ((x : ↥L) : G)) hb
    simpa using this
  refine ⟨a + b, Subtype.ext ?_⟩
  simp [pow_add, pow_mul, hb']

end Kernel

end QjAux

open QjAux

theorem qjInfo_of_card {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
    {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ)
    (hT : (pCoreOf 2 M).relIndex T = Fintype.card F ^ 2)
    (hU : (Uq M T L ⊓ Subgroup.centralizer (T : Set G)).relIndex (Uq M T L) = Fintype.card F) :
    QjInfo T L (Uq M T L) (Fintype.card F) := by
  intro SL hSL hTSL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := inf_centralizer_Uq_eq h hφ
  obtain ⟨⟨n, hn⟩, hφs, -, -, hnat⟩ := hφ
  have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  rw [← Nat.card_eq_fintype_card] at hT hU ⊢
  set U := Uq M T L
  set ψ : ↥L →* SL3 F := (toSL3 φ).comp (Subgroup.inclusion h.L_le)
  have hψs : Function.Surjective ψ := fun y => by
    obtain ⟨ℓ, hℓL, hℓ⟩ := exists_mem_L_eq h hφs (specialLinearGroupEquivStatedSL 3 F y)
    refine ⟨⟨ℓ, hℓL⟩, ?_⟩
    have e1 : ψ ⟨ℓ, hℓL⟩ = (specialLinearGroupEquivStatedSL 3 F).symm (φ ℓ) := rfl
    rw [e1, hℓ, MulEquiv.symm_apply_apply]
  set S₀ : Subgroup (SL3 F) := (SL.subgroupOf L).map ψ with hS₀
  have hS₀p : IsPGroup 2 S₀ :=
    (hSL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSL.1).symm).map ψ
  have hS₀i : ¬ 2 ∣ S₀.index := fun h2 => hSL.2.2 (h2.trans (Subgroup.index_map_dvd _ hψs))
  obtain ⟨x, hx⟩ : ∃ x : SL3 F, S₀.map (MulAut.conj x).toMonoidHom = sStar := by
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (SL3 F) (hS₀p.toSylow hS₀i)
      ((isPGroup_sStar hF).toSylow (not_two_dvd_index_sStar hF))
    refine ⟨x, ?_⟩
    have := congrArg (fun P : Sylow 2 (SL3 F) => (P : Subgroup (SL3 F))) hx
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
    rw [Subgroup.pointwise_smul_def] at this
    exact this
  set c : SL3 F →* SL3 F := (MulAut.conj x).toMonoidHom
  have hcinj : Function.Injective c := (MulAut.conj x).injective
  set ρ : ↥M →* SL3 F := c.comp (toSL3 φ)
  set ρL : ↥L →* SL3 F := ρ.comp (Subgroup.inclusion h.L_le)
  have hρLψ : ρL = c.comp ψ := rfl
  have hρLs : Function.Surjective ρL := by
    rw [hρLψ]
    exact (MulAut.conj x).surjective.comp hψs
  have hρSL : (SL.subgroupOf L).map ρL = sStar := by
    rw [hρLψ, ← Subgroup.map_map, ← hS₀, hx]
  have hρker : ∀ m : ↥M, ρ m = 1 → (m : G) ∈ pCoreOf 2 M := by
    intro m hm
    have h1 : toSL3 φ m = 1 := hcinj (by rw [map_one]; exact hm)
    rw [← hK]
    refine ⟨m.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have := (toSL3_eq_one_iff hnat m).mp h1 v hv
    calc v * m = m * v * (m : G)⁻¹ * m := by rw [this]
      _ = m * v := by group
  have hkerρL : IsPGroup 2 ρL.ker :=
    (isPGroup_cfsgPCore ↥L).to_le (ker_le_pCore_of_surjective_sl3 h.quasisimple hF hρLs)
  set A : Subgroup (SL3 F) := (T.subgroupOf M).map ρ with hA
  have hA_eq : A = (natImage φ T).map c := by
    rw [hA, natImage, Subgroup.map_map]
  have hAS : A ≤ sStar := by
    have hJM : T ⊔ SL ≤ M := sup_le h.le (hSL.1.trans h.L_le)
    have hJp : IsPGroup 2 ↥(T ⊔ SL) := h.isPGroup.to_sup_of_normal_right' hSL.2.1 hTSL
    have hJp' : IsPGroup 2 (((T ⊔ SL).subgroupOf M).map ρ) :=
      (hJp.of_equiv (Subgroup.subgroupOfEquivOfLe hJM).symm).map ρ
    have hsS : sStar ≤ ((T ⊔ SL).subgroupOf M).map ρ := by
      rw [← hρSL]
      rintro _ ⟨l, hl, rfl⟩
      exact ⟨Subgroup.inclusion h.L_le l,
        Subgroup.mem_subgroupOf.mpr (le_sup_right (a := T) (Subgroup.mem_subgroupOf.mp hl)), rfl⟩
    have := ((isPGroup_sStar hF).toSylow (not_two_dvd_index_sStar hF)).is_maximal' hJp'
      (by rw [IsPGroup.toSylow_coe]; exact hsS)
    rw [IsPGroup.toSylow_coe] at this
    rw [← this]
    exact Subgroup.map_mono fun t ht =>
      Subgroup.mem_subgroupOf.mpr (le_sup_left (b := SL) (Subgroup.mem_subgroupOf.mp ht))
  have hTC : T ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 M := by
    refine le_antisymm (fun t ht => ?_) (le_inf h.pCore_le (pCoreOf_le_centralizer_Uq h))
    rw [← hK]
    exact ⟨h.le ht.1, ht.2⟩
  have hcA : Nat.card A = Nat.card F ^ 2 := by
    have h1 := card_natImage_mul hnat h.le
    rw [hTC] at h1
    have h2 := relIndex_mul_card_inf' (pCoreOf 2 M) T
    rw [inf_eq_left.mpr h.pCore_le, hT] at h2
    rw [hA_eq, Subgroup.card_map_of_injective hcinj]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
  have hcU : Nat.card ↥(U ⊓ Subgroup.centralizer (T : Set G)) = Nat.card F ^ 2 := by
    have h1 := relIndex_mul_card_inf' (U ⊓ Subgroup.centralizer (T : Set G)) U
    rw [inf_eq_left.mpr inf_le_left, hU, card_eq_of_natural hnat] at h1
    have hq : 0 < Nat.card F := Nat.card_pos
    have h2 : Nat.card F * Nat.card ↥(U ⊓ Subgroup.centralizer (T : Set G)) =
        Nat.card F * Nat.card F ^ 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hq h2
  have hcf : Nat.card (fixN A) = Nat.card F ^ 2 := by
    rw [hA_eq, fixN_map_conj, ← hcU, card_inf_centralizer_eq hnat h.le]
    exact (Nat.card_congr ((Matrix.SpecialLinearGroup.toLin' x).submoduleMap _).toEquiv).symm
  have hAq : A = qLn := eq_qLn_of_card hAS hcA hcf
  set P₀ := LinearFlag.stabilizer (ln01 : Submodule F (Fin 3 → F))
  obtain ⟨hPmax, hNP⟩ := isMaxParabolic2_of_isCoatom hSL hρLs isCoatom_stabilizer_ln01
    (by rw [hρSL]; exact normalizer_sStar_le_stabilizer_ln01)
  set P : Subgroup G := (P₀.comap ρL).map L.subtype
  have hSLP : SL ≤ P := fun s hs => hNP ⟨hSL.1 hs, Subgroup.le_normalizer hs⟩
  set X := pCoreOf 2 P
  have hXP : X ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hPL : P ≤ L := Subgroup.map_subtype_le _
  have hXM : X ≤ M := hXP.trans (hPL.trans h.L_le)
  have hρX : (X.subgroupOf M).map ρ = qLn := by
    apply le_antisymm
    · have hNp : IsPGroup 2 ((X.subgroupOf M).map ρ) :=
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).of_equiv
          (Subgroup.subgroupOfEquivOfLe hXM).symm).map ρ
      have hkey : ∀ y ∈ P₀, ∀ z ∈ (X.subgroupOf M).map ρ,
          y * z * y⁻¹ ∈ (X.subgroupOf M).map ρ := by
        intro y hy z hz
        obtain ⟨l, rfl⟩ := hρLs y
        obtain ⟨m, hm, rfl⟩ := hz
        have hlP : (l : G) ∈ P := ⟨l, hy, rfl⟩
        have hconj : (l : G) * m * (l : G)⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hlP) _).mp hm
        refine ⟨Subgroup.inclusion h.L_le l * m * (Subgroup.inclusion h.L_le l)⁻¹,
          Subgroup.mem_subgroupOf.mpr (by simpa using hconj), ?_⟩
        rw [map_mul, map_mul, map_inv]
        rfl
      have hPN : P₀ ≤ Subgroup.normalizer (((X.subgroupOf M).map ρ : Subgroup (SL3 F)) :
          Set (SL3 F)) := by
        intro y hy
        rw [Subgroup.mem_normalizer_iff]
        intro z
        refine ⟨hkey y hy z, fun hz => ?_⟩
        have := hkey y⁻¹ (inv_mem hy) _ hz
        simpa [mul_assoc] using this
      exact le_qLn_of_normal hF hNp hPN
    · set X' : Subgroup G := ((qLn : Subgroup (SL3 F)).comap ρL).map L.subtype
      have hX'P : X' ≤ P := Subgroup.map_mono (Subgroup.comap_mono
        (qLn_le_sStar.trans sStar_le_stabilizer_ln01))
      have hkey : ∀ p ∈ P, ∀ y ∈ X', p * y * p⁻¹ ∈ X' := by
        rintro _ ⟨lp, hlp, rfl⟩ _ ⟨ly, hly, rfl⟩
        refine ⟨lp * ly * lp⁻¹, ?_, by simp⟩
        show ρL (lp * ly * lp⁻¹) ∈ qLn
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp (stabilizer_ln01_le_normalizer_qLn hlp) _).mp hly
      have hPX' : P ≤ Subgroup.normalizer (X' : Set G) := by
        intro p hp
        rw [Subgroup.mem_normalizer_iff]
        intro y
        refine ⟨hkey p hp y, fun hy => ?_⟩
        have := hkey p⁻¹ (inv_mem hp) _ hy
        simpa [mul_assoc] using this
      have hX'p : IsPGroup 2 X' :=
        (((isPGroup_sStar hF).to_le qLn_le_sStar).comap_of_ker_isPGroup ρL hkerρL).map
          L.subtype
      have hX'X : X' ≤ X := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hX'P hPX' hX'p
      intro r hr
      obtain ⟨l, rfl⟩ := hρLs r
      exact ⟨Subgroup.inclusion h.L_le l, Subgroup.mem_subgroupOf.mpr (hX'X ⟨l, hr, rfl⟩), rfl⟩
  refine ⟨X, ⟨P, hPmax, hSLP, rfl⟩, ?_, ?_⟩
  ·
    have hnatX : natImage φ X = natImage φ T := by
      apply Subgroup.map_injective hcinj
      rw [← hA_eq, hAq, ← hρX, natImage, Subgroup.map_map]
    have hcX : Nat.card ↥(U ⊓ Subgroup.centralizer (X : Set G)) =
        Nat.card ↥(U ⊓ Subgroup.centralizer (T : Set G)) := by
      rw [card_inf_centralizer_eq hnat hXM, card_inf_centralizer_eq hnat h.le, hnatX]
    have h1 := relIndex_mul_card_inf' (U ⊓ Subgroup.centralizer (X : Set G)) U
    have h2 := relIndex_mul_card_inf' (U ⊓ Subgroup.centralizer (T : Set G)) U
    rw [inf_eq_left.mpr inf_le_left] at h1 h2
    rw [hU] at h2
    rw [hcX] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
  ·
    intro g hgX
    have hgM : g ∈ M := hXM hgX
    have hρg : ρ ⟨g, hgM⟩ ∈ A := by
      rw [hAq, ← hρX]
      exact ⟨⟨g, hgM⟩, Subgroup.mem_subgroupOf.mpr hgX, rfl⟩
    obtain ⟨t, ht, hte⟩ := hρg
    have h1 : ρ (t⁻¹ * ⟨g, hgM⟩) = 1 := by rw [map_mul, map_inv, hte, inv_mul_cancel]
    have h3 : (t : G)⁻¹ * g ∈ T := h.pCore_le (by simpa using hρker _ h1)
    have h4 : (t : G) ∈ T := ht
    have e : g = (t : G) * ((t : G)⁻¹ * g) := by group
    rw [e]
    exact T.mul_mem h4 h3

end CFSG.Quasithin.MS93.S46
