module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
public import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools
import CFSG.GroupTheory.WielandtProductFinal
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

section Shapes

theorem uc22p2214_one_le_of_shape {X : Type} [Group X] {n : ℕ} (hX : Shape2214 X n) : 1 ≤ n := by
  rcases hX with h | h | h | h <;> exact (CFSG.Blueprint.LieModel.admissible h).2.1

theorem uc22p2214_shape_inn {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : Shape2214 X n) {r : ℕ} (hr : r.Prime) (hrn : n < r) (hr5 : 5 ≤ r) {α : MulAut X} (hα : α ^ r = 1) :
    α ∈ (MulAut.conj : X →* MulAut X).range := by
  have hn1 := uc22p2214_one_le_of_shape hX
  have hrn' : ¬ r ∣ n := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hr6 : ¬ r ∣ 6 * n := by
    intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h6 | h6
    · rcases (Nat.Prime.dvd_mul hr).1 (show r ∣ 2 * 3 from h6) with h7 | h7
      · exact absurd (Nat.le_of_dvd (by norm_num) h7) (by omega)
      · exact absurd (Nat.le_of_dvd (by norm_num) h7) (by omega)
    · exact hrn' h6
  have hr2 : ¬ r ∣ 2 * n := fun h => hr6 (by
    obtain ⟨k, hk⟩ := h
    exact ⟨3 * k, by rw [show 6 * n = 3 * (2 * n) by ring, hk]; ring⟩)
  rcases hX with h | h | h | h
  · exact uc22p2214_inner_of_prime_L2 h hr hrn' hα
  · exact uc22p2214_inner_of_prime_Sz h hr hrn' hα
  · exact uc22p2214_inner_of_prime_Sp4 h hr hr2 hα
  · exact uc22p2214_inner_of_prime_U3 h hr hr6 hα

theorem uc22p2214_shape_solv {X : Type} [Group X] [Finite X] {n : ℕ} (hX : Shape2214 X n) {S : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {Y : Subgroup X} (hSY : S ≤ Y) (hY : Group.IsSolvable ↥Y) :
    Y ≤ normalizer (S : Set X) := by
  rcases hX with h | h | h | h
  · exact uc22p2214_solvBorel_L2 h hS hSY hY
  · exact uc22p2214_solvBorel_Sz h hS hSY hY
  · exact uc22p2214_solvBorel_Sp4 h hS hSY hY
  · exact uc22p2214_solvBorel_U3 h hS hSY hY

end Shapes

section Placement

variable {Q : Type} [Group Q] [Finite Q]

@[expose] noncomputable def uc22p2214_autQuot (L : Subgroup Q) :
    ↥(normalizer (L : Set Q)) →* MulAut (↥L ⧸ center ↥L) :=
  CFSG.LocalAnalysis.GLTheoremB.quotAutHom (center ↥L) L.normalizerMonoidHom fun _ =>
    Subgroup.characteristic_iff_map_eq.mp inferInstance _

theorem uc22p2214_autQuot_mk (L : Subgroup Q) (y : ↥(normalizer (L : Set Q))) (l : ↥L) :
    uc22p2214_autQuot L y (QuotientGroup.mk l) = QuotientGroup.mk (L.normalizerMonoidHom y l) :=
  CFSG.LocalAnalysis.GLTheoremB.quotAutHom_mk (center ↥L) L.normalizerMonoidHom _ y l

theorem uc22p2214_autQuot_of_mem (L : Subgroup Q) {s : Q} (hs : s ∈ L) :
    uc22p2214_autQuot L ⟨s, le_normalizer hs⟩ = MulAut.conj (QuotientGroup.mk ⟨s, hs⟩ : ↥L ⧸ center ↥L) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H l =>
    rw [uc22p2214_autQuot_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl

theorem uc22p2214_mem_sup_of_permutes {B T : Subgroup Q} (hperm : Permutes B T) {g : Q} (hg : g ∈ B ⊔ T) :
    ∃ b ∈ B, ∃ t ∈ T, g = b * t := by
  let H : Subgroup Q :=
    { carrier := (B : Set Q) * (T : Set Q)
      mul_mem' := by
        rintro _ _ ⟨b₁, hb₁, t₁, ht₁, rfl⟩ ⟨b₂, hb₂, t₂, ht₂, rfl⟩
        have h : t₁ * b₂ ∈ (B : Set Q) * (T : Set Q) := by
          rw [hperm]
          exact Set.mul_mem_mul ht₁ hb₂
        obtain ⟨b₃, hb₃, t₃, ht₃, h3⟩ := h
        have h3' : b₃ * t₃ = t₁ * b₂ := h3
        refine ⟨b₁ * b₃, B.mul_mem hb₁ hb₃, t₃ * t₂, T.mul_mem ht₃ ht₂, ?_⟩
        calc b₁ * b₃ * (t₃ * t₂) = b₁ * (b₃ * t₃) * t₂ := by group
          _ = b₁ * t₁ * (b₂ * t₂) := by rw [h3']; group
      one_mem' := ⟨1, B.one_mem, 1, T.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨b, hb, t, ht, rfl⟩
        have h : t⁻¹ * b⁻¹ ∈ (B : Set Q) * (T : Set Q) := by
          rw [hperm]
          exact Set.mul_mem_mul (T.inv_mem ht) (B.inv_mem hb)
        simpa [mul_inv_rev] using h }
  have hle : B ⊔ T ≤ H := sup_le (fun b hb => ⟨b, hb, 1, T.one_mem, mul_one b⟩)
    (fun t ht => ⟨1, B.one_mem, t, ht, one_mul t⟩)
  obtain ⟨b, hb, t, ht, h⟩ := hle hg
  exact ⟨b, hb, t, ht, h.symm⟩

theorem uc22p2214_isSolvable_sup {B T : Subgroup Q} (hBodd : Odd (Nat.card B)) (hBc : IsMulCommutative B)
    (hT : IsPGroup 2 T) (hperm : Permutes B T) : Group.IsSolvable ↥(B ⊔ T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBS : B ≤ B ⊔ T := le_sup_left
  have hTS : T ≤ B ⊔ T := le_sup_right
  haveI : IsMulCommutative ↥(B.subgroupOf (B ⊔ T)) :=
    ⟨⟨fun x y => Subtype.ext (Subtype.ext (by
      have h := hBc.is_comm.comm ⟨((x : ↥(B ⊔ T)) : Q), x.2⟩ ⟨((y : ↥(B ⊔ T)) : Q), y.2⟩
      exact congrArg (fun z : ↥B => (z : Q)) h))⟩⟩
  have hTp : IsPGroup 2 ↥(T.subgroupOf (B ⊔ T)) := hT.comap_subtype
  haveI : Group.IsNilpotent ↥(T.subgroupOf (B ⊔ T)) := hTp.isNilpotent
  refine CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product (B.subgroupOf (B ⊔ T))
    (T.subgroupOf (B ⊔ T)) inferInstance inferInstance ?_ ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv]
    obtain ⟨k, hk⟩ := hTp.exists_card_eq
    rw [hk]
    refine Nat.Coprime.pow_right k ?_
    exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (fun h => (Nat.not_even_iff_odd.2 hBodd) (even_iff_two_dvd.2 h))))
  · rintro ⟨g, hg⟩
    obtain ⟨b, hb, t, ht, rfl⟩ := uc22p2214_mem_sup_of_permutes hperm hg
    exact ⟨⟨b, hBS hb⟩, hb, ⟨t, hTS ht⟩, ht, rfl⟩

theorem uc22p2214_cartan {Kb Yb S₀ : Subgroup Q} (hKq : CFSG.Open.IsQuasisimple ↥Kb) {r : ℕ} (hr : r.Prime)
    (hinn : ∀ α : MulAut (↥Kb ⧸ center ↥Kb), α ^ r = 1 →
      α ∈ (MulAut.conj : (↥Kb ⧸ center ↥Kb) →* MulAut (↥Kb ⧸ center ↥Kb)).range)
    (hsolv : ∀ S : Subgroup (↥Kb ⧸ center ↥Kb), CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ →
      ∀ Y : Subgroup (↥Kb ⧸ center ↥Kb), S ≤ Y → Group.IsSolvable ↥Y → Y ≤ normalizer (S : Set (↥Kb ⧸ center ↥Kb)))
    (hKS : CFSG.ABGLocalTools.IsSylowOf 2 S₀ Kb) (hSY : S₀ ≤ Yb) (hYs : Group.IsSolvable ↥Yb) {a : Q}
    (haY : a ∈ Yb) (haN : a ∈ normalizer (Kb : Set Q)) (hao : orderOf a = r)
    (hnt : ∃ k ∈ Kb, a * k * a⁻¹ * k⁻¹ ≠ 1) :
    ∃ S : Subgroup (↥Kb ⧸ center ↥Kb), CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ ∧
      ∃ x ∈ normalizer (S : Set (↥Kb ⧸ center ↥Kb)), orderOf x = r := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact r.Prime := ⟨hr⟩
  set N := normalizer (Kb : Set Q) with hNdef
  set ψ := uc22p2214_autQuot Kb with hψ
  haveI : IsSimpleGroup (↥Kb ⧸ center ↥Kb) := hKq.2
  have hXq : CFSG.Open.IsQuasisimple (↥Kb ⧸ center ↥Kb) :=
    uc22br4_isQuasisimple_of_surjective hKq (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hZX : center (↥Kb ⧸ center ↥Kb) = ⊥ := uc22p21k_center_eq_bot hXq
  have hconj : Function.Injective (MulAut.conj : (↥Kb ⧸ center ↥Kb) →* MulAut (↥Kb ⧸ center ↥Kb)) := by
    intro x y h
    have hc : y⁻¹ * x ∈ center (↥Kb ⧸ center ↥Kb) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun σ : MulAut (↥Kb ⧸ center ↥Kb) => σ g) h
      simp only [MulAut.conj_apply] at h1
      calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹) * x := by group
        _ = y⁻¹ * (x * g * x⁻¹) * x := by rw [h1]
        _ = y⁻¹ * x * g := by group
    rw [hZX, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  set Y₀ : Subgroup ↥N := Yb.subgroupOf N with hY₀
  haveI := hYs
  have hY₀s : Group.IsSolvable ↥Y₀ := by
    let ι : ↥Y₀ →* ↥Yb := (N.subtype.comp Y₀.subtype).codRestrict _ fun x => x.2
    exact Group.isSolvable_of_isSolvable_injective (f := ι) (fun x y h => Subtype.ext (Subtype.ext (by
      have h1 := congrArg (fun z : ↥Yb => (z : Q)) h
      exact h1)))
  haveI := hY₀s
  haveI hY₀ψ : Group.IsSolvable ↥(Y₀.map ψ) := Group.isSolvable_of_surjective (ψ.subgroupMap_surjective Y₀)
  set W : Subgroup (↥Kb ⧸ center ↥Kb) := (Y₀.map ψ).comap MulAut.conj with hW
  have hWs : Group.IsSolvable ↥W := by
    let ι : ↥W →* ↥(Y₀.map ψ) := (MulAut.conj.comp W.subtype).codRestrict _ fun x => x.2
    exact Group.isSolvable_of_isSolvable_injective (f := ι) (fun x y h => Subtype.ext (hconj (by
      have h1 := congrArg (fun z : ↥(Y₀.map ψ) => (z : MulAut (↥Kb ⧸ center ↥Kb))) h
      exact h1)))
  obtain ⟨P, hP⟩ := hKS
  let Ŝ : Sylow 2 (↥Kb ⧸ center ↥Kb) := Sylow.mapSurjective (QuotientGroup.mk'_surjective (center ↥Kb)) P
  have hŜ : CFSG.ABGLocalTools.IsSylowOf 2 (Ŝ : Subgroup (↥Kb ⧸ center ↥Kb)) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, Ŝ.isPGroup', by rw [Subgroup.relIndex_top_right]; exact Ŝ.not_dvd_index⟩
  have hŜW : (Ŝ : Subgroup (↥Kb ⧸ center ↥Kb)) ≤ W := by
    intro x hx
    rw [Sylow.coe_mapSurjective] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    have hsT : (s : Q) ∈ S₀ := by
      have : (s : Q) ∈ (P : Subgroup ↥Kb).map Kb.subtype := ⟨s, hs, rfl⟩
      rwa [hP] at this
    refine ⟨⟨s, le_normalizer s.2⟩, hSY hsT, ?_⟩
    show ψ ⟨s, le_normalizer s.2⟩ = MulAut.conj (QuotientGroup.mk s)
    exact uc22p2214_autQuot_of_mem Kb s.2
  have hWN := hsolv _ hŜ W hŜW hWs
  set α := ψ ⟨a, haN⟩ with hα
  have hαr : α ^ r = 1 := by
    rw [hα, ← map_pow]
    have : (⟨a, haN⟩ : ↥N) ^ r = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ← hao, pow_orderOf_eq_one]; rfl)
    rw [this, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    obtain ⟨k, hk, hk1⟩ := hnt
    refine hk1 ?_
    have key := uc22p2214_comm_eq_one_of_central hKq.1 haN (fun l hl => ?_) k hk
    · rw [key, mul_inv_cancel]
    · have h2 := congrArg (fun β : MulAut (↥Kb ⧸ center ↥Kb) => β (QuotientGroup.mk ⟨l, hl⟩)) h1
      simp only [MulAut.one_apply] at h2
      rw [hα, uc22p2214_autQuot_mk] at h2
      have h3 := (QuotientGroup.eq_iff_div_mem (N := center ↥Kb)).1 h2
      exact ⟨_, h3, by simp [div_eq_mul_inv]⟩
  obtain ⟨x, hx⟩ := hinn α hαr
  have hxW : x ∈ W := by
    show MulAut.conj x ∈ Y₀.map ψ
    rw [hx]
    exact ⟨⟨a, haN⟩, haY, rfl⟩
  have hαo : orderOf α = r := orderOf_eq_prime hαr hα1
  have hxo : orderOf x = r := by
    rw [← orderOf_injective _ hconj x, hx, hαo]
  exact ⟨Ŝ, hŜ, x, hWN hxW, hxo⟩

end Placement

end CFSG.LocalAnalysis.UniquenessCase.UC22
