module

public import CFSG.RankThree.GF2n.Parrott.Section3Lemma34Abstract
import CFSG.GroupTheory.IndexTwoSimpleQuotient

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open scoped commutatorElement

section Lemma34Reduction

variable {X : Type} [Group X]

private theorem lemma34_mem_of_comm_mem {x : X} {E R M : Subgroup X}
    (hM : M = Subgroup.normalizer (E : Set X) ⊓ Subgroup.centralizer ({x} : Set X))
    (hE : IsMulCommutative E)
    (hK2 : ∀ r ∈ R, r ∉ E → ∃ e ∈ E, ⁅r, e⁆ = x)
    (hK1 : ∀ r ∈ R, ∀ e ∈ E, IsConj x ⁅r, e⁆ → ⁅r, e⁆ = x)
    (hRN : R ≤ Subgroup.normalizer (E : Set X))
    {r g : X} (hr : r ∈ R) (hrE : r ∉ E) (hg : g ∈ Subgroup.normalizer (E : Set X))
    (hc : ⁅g, r⁆ ∈ E) : g ∈ M := by
  obtain ⟨e₀, he₀, hx⟩ := hK2 r hr hrE
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    Subtype.ext_iff.mp (hE.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have he₁ : g * e₀ * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hg e₀).mp he₀
  have hrn : r * (g * e₀ * g⁻¹) * r⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hRN hr) _).mp he₁
  have h1 : g * x * g⁻¹ = ⁅⁅g, r⁆ * r, g * e₀ * g⁻¹⁆ := by
    rw [← hx]; simp only [commutatorElement_def]; group
  have key : ∀ (c r e₁ : X), c * (r * e₁ * r⁻¹) = (r * e₁ * r⁻¹) * c →
      ⁅c * r, e₁⁆ = ⁅r, e₁⁆ := by
    intro c r e₁ h
    simp only [commutatorElement_def]
    calc c * r * e₁ * (c * r)⁻¹ * e₁⁻¹ = (c * (r * e₁ * r⁻¹) * c⁻¹) * e₁⁻¹ := by group
      _ = ((r * e₁ * r⁻¹) * c * c⁻¹) * e₁⁻¹ := by rw [h]
      _ = r * e₁ * r⁻¹ * e₁⁻¹ := by group
  have h2 : ⁅⁅g, r⁆ * r, g * e₀ * g⁻¹⁆ = ⁅r, g * e₀ * g⁻¹⁆ := key _ _ _ (hcomm _ hc _ hrn)
  have h4 : IsConj x ⁅r, g * e₀ * g⁻¹⁆ := by
    rw [isConj_iff]
    exact ⟨g, by rw [← h2, ← h1]⟩
  have h5 : ⁅r, g * e₀ * g⁻¹⁆ = x := hK1 r hr _ he₁ h4
  rw [hM]
  refine ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have h6 : g * x * g⁻¹ = x := by rw [h1, h2, h5]
  calc g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [h6]

section Plumbing

variable {N E : Subgroup X} {Y : Type} [Group Y] {q : ↥N →* Y}

private theorem lemma34_mk_eq_iff (hqE : ∀ n : ↥N, q n = 1 ↔ (n : X) ∈ E) (a b : ↥N) :
    q a = q b ↔ (a : X)⁻¹ * b ∈ E := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, hqE]
  rfl

private theorem lemma34_mem_push_iff (hqE : ∀ n : ↥N, q n = 1 ↔ (n : X) ∈ E) {S : Subgroup X}
    (hES : E ≤ S) (n : ↥N) : q n ∈ (S.subgroupOf N).map q ↔ (n : X) ∈ S := by
  constructor
  · rintro ⟨m, hm, hmn⟩
    have h1 := (lemma34_mk_eq_iff hqE m n).mp hmn
    have h2 : (n : X) = (m : X) * ((m : X)⁻¹ * n) := by group
    rw [h2]
    exact S.mul_mem hm (hES h1)
  · intro hn
    exact ⟨n, hn, rfl⟩

private theorem lemma34_comap_push (hqE : ∀ n : ↥N, q n = 1 ↔ (n : X) ∈ E) {S : Subgroup X}
    (hES : E ≤ S) : ((S.subgroupOf N).map q).comap q = S.subgroupOf N := by
  ext n
  rw [Subgroup.mem_comap]
  exact lemma34_mem_push_iff hqE hES n

private theorem lemma34_index_push (hq : Function.Surjective q)
    (hqE : ∀ n : ↥N, q n = 1 ↔ (n : X) ∈ E) {S : Subgroup X} (hES : E ≤ S) :
    ((S.subgroupOf N).map q).index = S.relIndex N := by
  rw [← Subgroup.index_comap_of_surjective _ hq, lemma34_comap_push hqE hES]
  rfl

private theorem lemma34_relIndex_push (hqE : ∀ n : ↥N, q n = 1 ↔ (n : X) ∈ E)
    {S T : Subgroup X} (hES : E ≤ S) (hTN : T ≤ N) :
    ((S.subgroupOf N).map q).relIndex ((T.subgroupOf N).map q) = S.relIndex T := by
  rw [← Subgroup.relIndex_comap, lemma34_comap_push hqE hES, Subgroup.relIndex_subgroupOf hTN]

private theorem lemma34_card_push (hqE : ∀ n : ↥N, q n = 1 ↔ (n : X) ∈ E) {R : Subgroup X}
    (hRN : R ≤ N) : Nat.card ((R.subgroupOf N).map q) = E.relIndex R := by
  let φ : ↥R →* Y := q.comp (Subgroup.inclusion hRN)
  have hrange : φ.range = (R.subgroupOf N).map q := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : φ.ker = E.subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hqE (Subgroup.inclusion hRN r)
  rw [← hrange, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv.symm, hker]
  rfl

private theorem lemma34_isElemAbelian_push (hqE : ∀ n : ↥N, q n = 1 ↔ (n : X) ∈ E)
    {R : Subgroup X} (hRab : ∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ E) (hRsq : ∀ r ∈ R, r * r ∈ E) :
    IsElemAbelian 2 ((R.subgroupOf N).map q) := by
  have hD : ∀ d ∈ (R.subgroupOf N).map q, ∃ r : ↥N, (r : X) ∈ R ∧ q r = d := by
    rintro d ⟨r, hr, rfl⟩
    exact ⟨r, hr, rfl⟩
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun d hd => ?_⟩
  · obtain ⟨r, hr, hra⟩ := hD a a.2
    obtain ⟨s, hs, hsb⟩ := hD b b.2
    apply Subtype.ext
    show (a : Y) * b = b * a
    rw [← hra, ← hsb, ← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, hqE]
    exact hRab _ hr _ hs
  · obtain ⟨r, hr, rfl⟩ := hD d hd
    rw [sq, ← map_mul, hqE]
    exact hRsq _ hr

private theorem lemma34_trans_push (hqE : ∀ n : ↥N, q n = 1 ↔ (n : X) ∈ E) {R M : Subgroup X}
    (hMN : M ≤ N)
    (hTrans : ∀ r ∈ R, ∀ s ∈ R, r ∉ E → s ∉ E → ∃ g ∈ M, g * r * g⁻¹ * s⁻¹ ∈ E) :
    ∀ a ∈ (R.subgroupOf N).map q, ∀ b ∈ (R.subgroupOf N).map q, a ≠ 1 → b ≠ 1 →
      ∃ g ∈ (M.subgroupOf N).map q, g * a * g⁻¹ = b := by
  rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩ hr1 hs1
  obtain ⟨g, hgM, hg⟩ := hTrans r hr s hs (fun h => hr1 ((hqE r).mpr h))
    (fun h => hs1 ((hqE s).mpr h))
  refine ⟨q ⟨g, hMN hgM⟩, ⟨⟨g, hMN hgM⟩, hgM, rfl⟩, ?_⟩
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, hqE]
  exact hg

private theorem lemma34_perm_push
    (hqE : ∀ n : ↥N, q n = 1 ↔ (n : X) ∈ E) {R M : Subgroup X} (hER : E ≤ R) (hMN : M ≤ N)
    (hπ : ∃ π : ↥M →* Equiv.Perm (Fin 5), Function.Surjective π ∧ π.ker = R.subgroupOf M) :
    ∃ π' : ↥((M.subgroupOf N).map q) →* Equiv.Perm (Fin 5), Function.Surjective π' ∧
      π'.ker = ((R.subgroupOf N).map q).subgroupOf ((M.subgroupOf N).map q) := by
  obtain ⟨π, hπs, hπk⟩ := hπ
  let ψ : ↥M →* ↥((M.subgroupOf N).map q) :=
    (q.comp (Subgroup.inclusion hMN)).codRestrict _ fun m => ⟨Subgroup.inclusion hMN m, m.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, n, hn, rfl⟩
    exact ⟨⟨(n : X), hn⟩, rfl⟩
  have hψ1 : ∀ m : ↥M, ψ m = 1 ↔ (m : X) ∈ E := fun m =>
    ⟨fun h => (hqE (Subgroup.inclusion hMN m)).mp (congrArg Subtype.val h),
      fun h => Subtype.ext ((hqE (Subgroup.inclusion hMN m)).mpr h)⟩
  have hψk : ψ.ker ≤ π.ker := by
    intro m hm
    rw [hπk]
    exact hER ((hψ1 m).mp hm)
  have hcomp : ∀ m : ↥M, (ψ.liftOfSurjective hψs ⟨π, hψk⟩) (ψ m) = π m := fun m =>
    MonoidHom.liftOfRightInverse_comp_apply ψ _ _ ⟨π, hψk⟩ m
  refine ⟨ψ.liftOfSurjective hψs ⟨π, hψk⟩, ?_, ?_⟩
  · intro σ
    obtain ⟨m, rfl⟩ := hπs σ
    exact ⟨ψ m, hcomp m⟩
  · ext m'
    obtain ⟨m, rfl⟩ := hψs m'
    rw [MonoidHom.mem_ker, hcomp, ← MonoidHom.mem_ker, hπk, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    exact (lemma34_mem_push_iff hqE hER (Subgroup.inclusion hMN m)).symm

private theorem lemma34_quotient_equiv (hq : Function.Surjective q)
    (hqE : ∀ n : ↥N, q n = 1 ↔ (n : X) ∈ E) (K' : Subgroup Y) :
    ∃ (_ : (E.subgroupOf ((K'.comap q).map N.subtype)).Normal),
      Nonempty (↥((K'.comap q).map N.subtype) ⧸ E.subgroupOf ((K'.comap q).map N.subtype) ≃*
        ↥K') := by
  set K : Subgroup X := (K'.comap q).map N.subtype with hK
  have hKN : K ≤ N := Subgroup.map_subtype_le _
  have hKmem : ∀ k : ↥K, q (Subgroup.inclusion hKN k) ∈ K' := by
    rintro ⟨_, n, hn, rfl⟩
    exact hn
  let θ : ↥K →* ↥K' := (q.comp (Subgroup.inclusion hKN)).codRestrict K' hKmem
  have hθs : Function.Surjective θ := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := hq y
    exact ⟨⟨(n : X), n, hy, rfl⟩, rfl⟩
  have hker : θ.ker = E.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => (hqE (Subgroup.inclusion hKN k)).mp (congrArg Subtype.val h),
      fun h => Subtype.ext ((hqE (Subgroup.inclusion hKN k)).mpr h)⟩
  have hN : (E.subgroupOf K).Normal := hker ▸ θ.normal_ker
  refine ⟨hN, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθs)

end Plumbing

private theorem lemma34_le_of_relIndex_two {Y : Type*} [Group Y] {M' D L' : Subgroup Y}
    (hDM : D ≤ M') (hrel : L'.relIndex M' = 2) (hD : 2 < Nat.card D)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ M', g * a * g⁻¹ = b) : D ≤ L' := by
  have hmul : ∀ {a b : Y}, a ∈ M' → b ∈ M' → (a * b ∈ L' ↔ (a ∈ L' ↔ b ∈ L')) :=
    fun {a b} ha hb => Subgroup.mul_mem_iff_of_index_two (H := L'.subgroupOf M') hrel
      (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  have hconj : ∀ {g a : Y}, g ∈ M' → a ∈ M' → (g * a * g⁻¹ ∈ L' ↔ a ∈ L') := by
    intro g a hg ha
    rw [hmul (M'.mul_mem hg ha) (M'.inv_mem hg), hmul hg ha, L'.inv_mem_iff]
    tauto
  by_contra hDL
  obtain ⟨d₁, hd₁D, hd₁L⟩ := Set.not_subset.mp hDL
  have hd₁1 : d₁ ≠ 1 := fun h => hd₁L (h ▸ L'.one_mem)
  have hout : ∀ d ∈ D, d ≠ 1 → d ∉ L' := by
    intro d hd hd1 hdL
    obtain ⟨g, hg, hgd⟩ := hTrans d hd d₁ hd₁D hd1 hd₁1
    exact hd₁L (hgd ▸ (hconj hg (hDM hd)).mpr hdL)
  obtain ⟨d₂, hd₂D, hd₂1, hd₁₂⟩ : ∃ d₂ ∈ D, d₂ ≠ 1 ∧ d₁ * d₂ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (D : Set Y) ⊆ {1, d₁⁻¹} := by
      intro d hd
      by_cases hd1 : d = 1
      · exact Or.inl hd1
      · exact Or.inr (eq_inv_of_mul_eq_one_right (hcon d hd hd1))
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, d₁⁻¹} : Set Y).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    have h3 : Nat.card D = (D : Set Y).ncard := Nat.card_coe_set_eq (D : Set Y)
    rw [h3] at hD
    omega
  have h1 : d₁ * d₂ ∈ L' :=
    (hmul (hDM hd₁D) (hDM hd₂D)).mpr (iff_of_false hd₁L (hout _ hd₂D hd₂1))
  exact hout _ (D.mul_mem hd₁D hd₂D) hd₁₂ h1

end Lemma34Reduction

theorem lemma34_generic {X : Type} [Group X] [Finite X] (x : X) (E R M : Subgroup X)
    (hM : M = Subgroup.normalizer (E : Set X) ⊓ Subgroup.centralizer ({x} : Set X))
    (hE : IsElemAbelian 2 E)
    (hER : E ≤ R) (hRM : R ≤ M)
    (hR16 : E.relIndex R = 16) (hRab : ∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ E)
    (hRsq : ∀ r ∈ R, r * r ∈ E)
    (hπ : ∃ π : ↥M →* Equiv.Perm (Fin 5), Function.Surjective π ∧ π.ker = R.subgroupOf M)
    (hTrans : ∀ r ∈ R, ∀ s ∈ R, r ∉ E → s ∉ E → ∃ g ∈ M, g * r * g⁻¹ * s⁻¹ ∈ E)
    (hK2 : ∀ r ∈ R, r ∉ E → ∃ e ∈ E, ⁅r, e⁆ = x)
    (hK1 : ∀ r ∈ R, ∀ e ∈ E, IsConj x ⁅r, e⁆ → ⁅r, e⁆ = x)
    (hodd : Odd (M.relIndex (Subgroup.normalizer (E : Set X))))
    (hfus : ∃ e ∈ E, e ≠ x ∧ ∃ n ∈ Subgroup.normalizer (E : Set X), n * x * n⁻¹ = e) :
    ∃ K : Subgroup X, E ≤ K ∧ K.relIndex (Subgroup.normalizer (E : Set X)) = 2 ∧ ¬ M ≤ K ∧
      ((E.subgroupOf K).Normal ∧ Nat.card (↥K ⧸ E.subgroupOf K) = 20160 ∧
         ∀ L : Subgroup X, E ≤ L → L ≤ K → L.relIndex K ≠ 2) ∧
      R ≤ K ∧ (∀ L : Subgroup X, E ≤ L → L ≤ M → L.relIndex M = 2 → L = K ⊓ M) := by
  classical
  have hMN : M ≤ Subgroup.normalizer (E : Set X) := by rw [hM]; exact inf_le_left
  have hMC : M ≤ Subgroup.centralizer ({x} : Set X) := by rw [hM]; exact inf_le_right
  have hRN : R ≤ Subgroup.normalizer (E : Set X) := hRM.trans hMN
  have hEM : E ≤ M := hER.trans hRM
  set N : Subgroup X := Subgroup.normalizer (E : Set X) with hN
  obtain ⟨Y, instY, instYf, q, hq, hqE⟩ : ∃ (Y : Type) (_ : Group Y) (_ : Finite Y)
      (q : ↥N →* Y), Function.Surjective q ∧ ∀ n : ↥N, q n = 1 ↔ (n : X) ∈ E :=
    ⟨↥N ⧸ E.subgroupOf N, inferInstance, inferInstance, QuotientGroup.mk' (E.subgroupOf N),
      QuotientGroup.mk'_surjective _, fun n => by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        rfl⟩
  have hD16 : Nat.card ((R.subgroupOf N).map q) = 16 := by
    rw [lemma34_card_push hqE hRN]
    exact hR16
  have hDM' : (R.subgroupOf N).map q ≤ (M.subgroupOf N).map q :=
    Subgroup.map_mono fun r hr => hRM hr
  have hTrans' := lemma34_trans_push hqE hMN hTrans
  have hCent : ∀ d ∈ (R.subgroupOf N).map q, d ≠ 1 →
      Subgroup.centralizer ({d} : Set Y) ≤ (M.subgroupOf N).map q := by
    rintro _ ⟨r, hr, rfl⟩ hr1 c hc
    obtain ⟨g, rfl⟩ := hq c
    have hrE : (r : X) ∉ E := fun h => hr1 ((hqE r).mpr h)
    have hcomm : q g * q r = q r * q g := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hgE : ⁅(g : X), (r : X)⁆ ∈ E := by
      refine (hqE ⁅g, r⁆).mp ?_
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    exact ⟨g, lemma34_mem_of_comm_mem hM hE.1 hK2 hK1 hRN hr hrE g.2 hgE, rfl⟩
  have hodd' : Odd ((M.subgroupOf N).map q).index := by
    rw [lemma34_index_push hq hqE hEM]
    exact hodd
  have hfus' : 1 < ((M.subgroupOf N).map q).index := by
    rw [lemma34_index_push hq hqE hEM]
    have h0 : M.relIndex N ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : M.relIndex N ≠ 1 := by
      intro h
      have hNM : N ≤ M := Subgroup.relIndex_eq_one.mp h
      obtain ⟨e, he, hex, n, hn, hne⟩ := hfus
      have hnx : n * x = x * n := Subgroup.mem_centralizer_singleton_iff.mp (hMC (hNM hn))
      apply hex
      rw [← hne]
      calc n * x * n⁻¹ = x * n * n⁻¹ := by rw [hnx]
        _ = x := by group
    omega
  obtain ⟨K', -, hK'i, hDK', hMK', hKL, hK'card, hK'Q⟩ := lemma34_abstract
    ((M.subgroupOf N).map q) ((R.subgroupOf N).map q) hDM'
    (lemma34_isElemAbelian_push hqE hRab hRsq) hD16 (lemma34_perm_push hqE hER hMN hπ)
    hTrans' hCent hodd' hfus'
  refine ⟨(K'.comap q).map N.subtype, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    refine ⟨⟨e, Subgroup.le_normalizer he⟩, ?_, rfl⟩
    show q ⟨e, _⟩ ∈ K'
    rw [(hqE _).mpr he]
    exact K'.one_mem
  · have hK : ((K'.comap q).map N.subtype).subgroupOf N = K'.comap q :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective N) _
    rw [Subgroup.relIndex, hK, Subgroup.index_comap_of_surjective _ hq]
    exact hK'i
  · intro hMK
    apply hMK'
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨n', hn', hnn'⟩ := hMK hn
    have hnn : n' = n := Subtype.ext hnn'
    rw [← hnn]
    exact hn'
  · obtain ⟨hNorm, ⟨e⟩⟩ := lemma34_quotient_equiv hq hqE K'
    have hEK : E ≤ (K'.comap q).map N.subtype := by
      intro e he
      refine ⟨⟨e, Subgroup.le_normalizer he⟩, ?_, rfl⟩
      show q ⟨e, _⟩ ∈ K'
      rw [(hqE _).mpr he]
      exact K'.one_mem
    refine ⟨hNorm, (Nat.card_congr e.toEquiv).trans hK'card, ?_⟩
    have hQK : ∀ T : Subgroup (↥((K'.comap q).map N.subtype) ⧸
        E.subgroupOf ((K'.comap q).map N.subtype)), T.index ≠ 2 := by
      intro T hT
      let T' : Subgroup ↥K' := T.map e.toMonoidHom
      have hT' : T'.index = 2 :=
        (Subgroup.index_map_equiv (H := T) e).trans hT
      have hrel : (T'.map K'.subtype).relIndex K' = 2 := by
        change ((T'.map K'.subtype).subgroupOf K').index = 2
        rw [Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective K')]
        exact hT'
      exact hK'Q (T'.map K'.subtype) (Subgroup.map_subtype_le _) hrel
    exact (CFSG.GroupTheory.forall_relIndex_ne_two_iff_quotient hEK).mpr hQK
  · intro r hr
    exact ⟨⟨r, hRN hr⟩, hDK' ⟨⟨r, hRN hr⟩, hr, rfl⟩, rfl⟩
  · intro L hEL hLM hLrel
    have hLN : L ≤ N := hLM.trans hMN
    have hL'M' : (L.subgroupOf N).map q ≤ (M.subgroupOf N).map q :=
      Subgroup.map_mono fun l hl => hLM hl
    have hrel' : ((L.subgroupOf N).map q).relIndex ((M.subgroupOf N).map q) = 2 := by
      rw [lemma34_relIndex_push hqE hEL hMN]
      exact hLrel
    have hDL' : (R.subgroupOf N).map q ≤ (L.subgroupOf N).map q :=
      lemma34_le_of_relIndex_two hDM' hrel' (by rw [hD16]; norm_num) hTrans'
    have heq := hKL _ hDL' hL'M' hrel'
    ext l
    constructor
    · intro hl
      have hlN : l ∈ N := hLN hl
      have h1 : q ⟨l, hlN⟩ ∈ (L.subgroupOf N).map q := ⟨⟨l, hlN⟩, hl, rfl⟩
      rw [heq] at h1
      exact ⟨⟨⟨l, hlN⟩, h1.1, rfl⟩, hLM hl⟩
    · rintro ⟨⟨n, hn, hnl⟩, hlM⟩
      have hnl' : n = ⟨l, hMN hlM⟩ := Subtype.ext hnl
      have h1 : q ⟨l, hMN hlM⟩ ∈ K' ⊓ (M.subgroupOf N).map q :=
        ⟨hnl' ▸ hn, ⟨⟨l, hMN hlM⟩, hlM, rfl⟩⟩
      rw [← heq] at h1
      exact (lemma34_mem_push_iff hqE hEL ⟨l, hMN hlM⟩).mp h1

end CFSG.RankThree.GF2n.Parrott
