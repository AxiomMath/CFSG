module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res9ProofQuot
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofModel
import CFSG.RankThree.PartTwo.Sec14.Item148ResProofONTools
import CFSG.RankThree.PartTwo.Sec12.Item125Basic
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
public import CFSG.RankThree.PartTwo.Sec14.Item14Res7ProofDescFix
public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofA6

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Res9Fix

variable {G : Type} [Group G] [Finite G] {A X : Subgroup G} {a : G}

theorem sig_zpow {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) (i : ℤ) :
    sig X (g ^ i) = sig X g ^ i := by
  rw [sig_eq hg, sig_eq (zpow_mem hg i)]
  have h1 : (⟨g ^ i, zpow_mem hg i⟩ : Subgroup.normalizer (X : Set G)) = ⟨g, hg⟩ ^ i :=
    Subtype.ext (by simp)
  rw [h1, map_zpow, map_zpow]

theorem sig_of_mem {w : G} (hw : w ∈ X) (γ : ↥X ⧸ aschbacherSolvableCore 3 ↥X) :
    sig X w γ = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨w, hw⟩ * γ *
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨w, hw⟩)⁻¹ := by
  obtain ⟨⟨u, hu⟩, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥X) γ
  rw [sig_mk (Subgroup.le_normalizer hw) hu, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem Base.exists_zpow_of_trivial (hC : Base A a X) {D : Subgroup G} (hDA : D ≤ A) {x : G}
    (hxA : x ∈ A) (hAD : A ≤ D ⊔ Subgroup.zpowers x)
    (hD1 : ∀ δ ∈ D, ∀ γ, sig X δ γ = γ) {α : G} (hα : α ∈ A) :
    ∃ i : ℤ, ∀ γ, sig X α γ = (sig X x ^ i) γ := by
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hC.isE27.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem (fun y hy => ?_) (fun y hy => ?_)
    · rw [hcomm x hxA y (hDA hy), mul_inv_cancel_right]
      exact hy
    · rw [hcomm x⁻¹ (inv_mem hxA) y (hDA hy), inv_mul_cancel_right]
      exact hy
  obtain ⟨δ, hδ, z, hz, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hxN (hAD hα)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hδN := hC.A_le_normalizer (hDA hδ)
  have hxN' := hC.A_le_normalizer hxA
  refine ⟨i, fun γ => ?_⟩
  rw [sig_mul hδN (zpow_mem hxN' i), MulAut.mul_apply, hD1 δ hδ, sig_zpow hxN' i]

@[expose] def cyc : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 0 2

theorem cyc_mem : cyc ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  unfold cyc
  decide

theorem cyc_pow_three : cyc ^ 3 = 1 := by
  unfold cyc
  decide

theorem cyc_ne_one : cyc ≠ 1 := by
  unfold cyc
  decide

theorem cyc_pow_ne_one {s : ℕ} (hs : ¬ 3 ∣ s) : cyc ^ s ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf cyc = 3 := orderOf_eq_prime cyc_pow_three cyc_ne_one
  intro h
  exact hs (ho ▸ orderOf_dvd_of_pow_eq_one h)

theorem zpow_apply_eq_of_apply_eq {M : Type*} [Group M] {σ : MulAut M} {y : M} (h : σ y = y)
    (i : ℤ) : (σ ^ i) y = y := by
  have h1 : σ ∈ MulAction.stabilizer (MulAut M) y := h
  exact (MulAction.stabilizer (MulAut M) y).zpow_mem h1 i

theorem commutatorElement_mul_of_commute {M : Type*} [Group M] {a b z w : M}
    (hzb : z * b = b * z) (hwa : w * a = a * w) (hzw : z * w = w * z) :
    ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hwa' : w * a⁻¹ = a⁻¹ * w := by
    calc w * a⁻¹ = a⁻¹ * (a * w) * a⁻¹ := by group
      _ = a⁻¹ * (w * a) * a⁻¹ := by rw [hwa]
      _ = a⁻¹ * w := by group
  simp only [commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzb]
    _ = a * b * (z * w) * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * b * (w * z) * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzw]
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [hwa']
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem Base.sig_fixed_img (hC : Base A a X) {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G))
    (hHO : H ≤ Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G))
    (hgH : H ≤ Subgroup.centralizer ({g} : Set G)) :
    ∀ l ∈ img a X H, sig X g l = l := by
  rintro _ ⟨w, hw, rfl⟩
  have hw' := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hw)
  obtain ⟨o, ho, h, hh, hoh⟩ := Item148PtRes.exists_mul_of_mem_sup hHO hw'.1
  have hgN := hC.le_normalizer hg
  have h1 : sig X g (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) w) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)
        ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgN _).mp w.2⟩ := sig_mk hgN w.2
  rw [h1, mk_eq_mk_iff]
  refine hC.inf_le_theta (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · have hgh : g * h = h * g := (Subgroup.mem_centralizer_singleton_iff.mp (hgH hh)).symm
    have hgh' : h * g⁻¹ = g⁻¹ * h := by
      calc h * g⁻¹ = g⁻¹ * (g * h) * g⁻¹ := by group
        _ = g⁻¹ * (h * g) * g⁻¹ := by rw [hgh]
        _ = g⁻¹ * h := by group
    have e : g * (w : G) * g⁻¹ * (w : G)⁻¹ = (g * o * g⁻¹) * o⁻¹ := by
      rw [hoh]
      calc g * (o * h) * g⁻¹ * (o * h)⁻¹ = g * o * (h * g⁻¹) * h⁻¹ * o⁻¹ := by group
        _ = g * o * (g⁻¹ * h) * h⁻¹ * o⁻¹ := by rw [hgh']
        _ = g * o * g⁻¹ * o⁻¹ := by group
    rw [e]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hC.cent_le_normalizer_O hg) o).mp ho)
      (inv_mem ho)
  · exact mul_mem ((Subgroup.mem_normalizer_iff.mp hgN _).mp w.2) (inv_mem w.2)


theorem Base.exists_conj_of_mem (hC : Base A a X)
    (hT : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
      CFSG.Blueprint.NativeSporadic.ON) {α : G} (hα : α ∈ A) :
    ∃ m : ↥X ⧸ aschbacherSolvableCore 3 ↥X, m ^ 3 = 1 ∧ ∀ γ, sig X α γ = m * γ * m⁻¹ := by
  have := hC.isPerfect
  obtain ⟨ψ⟩ := ON134.nonempty_equiv_model hC.isPerfect hT
  have hσ3 := sig_pow_three (hC.A_le_normalizer hα) (hC.pow_three hα)
  obtain ⟨m, hm⟩ := ON134.aut_inner ψ (sig X α)
    (Res148.fix_center_of_pow_three (sig X α) hσ3 hT.1)
  refine ⟨m, ?_, hm⟩
  have hm3 : m ^ 3 ∈ Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    rw [Subgroup.mem_center_iff]
    intro γ
    have h1 : (sig X α ^ 3) γ = m ^ 3 * γ * (m ^ 3)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, hm]
      group
    rw [hσ3, MulAut.one_apply] at h1
    calc γ * m ^ 3 = m ^ 3 * γ * (m ^ 3)⁻¹ * m ^ 3 := by rw [← h1]
      _ = m ^ 3 * γ := by group
  have h9 : m ^ 3 ^ 2 = 1 := by
    have h1 := Subgroup.orderOf_dvd_natCard _ hm3
    rw [hT.1] at h1
    rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  exact ON134.pow_three_eq_one ψ (k := 2) h9

theorem Base.false_of_trivial (hC : Base A a X)
    (hT : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
      CFSG.Blueprint.NativeSporadic.ON)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    {D : Subgroup G} (hDA : D ≤ A) {x : G} (hxA : x ∈ A) (hAD : A ≤ D ⊔ Subgroup.zpowers x)
    (hD1 : ∀ δ ∈ D, ∀ γ, sig X δ γ = γ) (hx : ∃ γ, sig X x γ ≠ γ) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hC.isPerfect
  obtain ⟨ψ⟩ := ON134.nonempty_equiv_model hC.isPerfect hT
  obtain ⟨m, hm3, hm⟩ := hC.exists_conj_of_mem hT hxA
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) with hπ
  have hmz : m ∉ Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    intro hmz
    obtain ⟨γ, hγ⟩ := hx
    apply hγ
    rw [hm, ← Subgroup.mem_center_iff.mp hmz γ, mul_inv_cancel_right]
  obtain ⟨K, hCK, hmK, hZK, ρ, hρ, hker⟩ := Sec15.Proof156Res4.exists_centralizer_eq ψ hm3 hmz
  have hcyc : cyc ∈ ρ.range := hρ ▸ cyc_mem
  obtain ⟨⟨y, hyK⟩, hy⟩ := hcyc
  have hρpow : ∀ s : ℕ, ρ (⟨y, hyK⟩ ^ s) = cyc ^ s := fun s => by rw [map_pow, hy]
  have hyZ : ∀ s : ℕ, ¬ 3 ∣ s → y ^ s ∉ Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    intro s hs hyz
    have h1 : ρ (⟨y, hyK⟩ ^ s) = 1 := (hker _).mpr (by simpa using hyz)
    rw [hρpow] at h1
    exact cyc_pow_ne_one hs h1
  have hy3 : y ^ 3 = 1 := by
    have h1 : ((⟨y, hyK⟩ ^ 3 : ↥K) : ↥X ⧸ aschbacherSolvableCore 3 ↥X) ∈
        Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
      rw [← hker, hρpow, cyc_pow_three]
    have h2 := Subgroup.orderOf_dvd_natCard _ h1
    rw [hT.1] at h2
    have h3 : (y ^ 3) ^ 3 = 1 := by
      have := orderOf_dvd_iff_pow_eq_one.mp h2
      simpa using this
    have h4 : y ^ 3 ^ 2 = 1 := by
      rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul]
      exact h3
    exact ON134.pow_three_eq_one ψ (k := 2) h4
  have hym : m * y * m⁻¹ = y := by
    have h1 : y ∈ Subgroup.centralizer ({m} : Set (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :=
      hCK ▸ Subgroup.mem_sup_right hyK
    rw [(Subgroup.mem_centralizer_singleton_iff.mp h1).symm, mul_inv_cancel_right]
  have hσx : sig X x y = y := by rw [hm, hym]
  have hfixA : ∀ α ∈ A, sig X α y = y := by
    intro α hα
    obtain ⟨i, hi⟩ := hC.exists_zpow_of_trivial hDA hxA hAD hD1 hα
    rw [hi]
    exact zpow_apply_eq_of_apply_eq hσx i
  obtain ⟨⟨y₀, hy₀⟩, hy₀y⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥X) y
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hC.isE27.2]; norm_num)
  have hfix' : ∀ α ∈ A, y₀⁻¹ * (α * y₀ * α⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) X := by
    intro α hα
    have h1 := hfixA α hα
    rw [← hy₀y, sig_mk (hC.A_le_normalizer hα) hy₀, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq] at h1
    exact ⟨_, h1, rfl⟩
  obtain ⟨n, hn, hnfix⟩ := Sec12.exists_fixed_lift hAp hC.A_le_normalizer hfix'
  have hnX : n ∈ X := Subgroup.map_subtype_le _ hn
  have hzX : y₀ * n ∈ X := mul_mem hy₀ hnX
  have hπz : π ⟨y₀ * n, hzX⟩ = y := by
    rw [← hy₀y, hπ]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨n', hn', hn'eq⟩ := hn
    have e : (⟨y₀ * n, hzX⟩ : ↥X)⁻¹ * ⟨y₀, hy₀⟩ = n'⁻¹ := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype] at hn'eq ⊢
      rw [hn'eq]
      group)
    rw [e]
    exact inv_mem hn'
  obtain ⟨e, s, hs3, hzs⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (y₀ * n)).ne' 3 (by norm_num)
  have hwX : (y₀ * n) ^ s ∈ X := pow_mem hzX s
  have hwA : ∀ α ∈ A, α * (y₀ * n) ^ s = (y₀ * n) ^ s * α := by
    intro α hα
    have h1 : α * (y₀ * n) = (y₀ * n) * α := by
      have := hnfix α hα
      calc α * (y₀ * n) = α * (y₀ * n) * α⁻¹ * α := by group
        _ = (y₀ * n) * α := by rw [this]
    exact (Commute.pow_right h1 s : Commute α ((y₀ * n) ^ s))
  have hπw : π ⟨(y₀ * n) ^ s, hwX⟩ = y ^ s := by
    rw [← hπz, ← map_pow]
    rfl
  have hw3 : ((y₀ * n) ^ s) ^ 3 = 1 := by
    have h1 : π ⟨((y₀ * n) ^ s) ^ 3, pow_mem hwX 3⟩ = 1 := by
      have e : (⟨((y₀ * n) ^ s) ^ 3, pow_mem hwX 3⟩ : ↥X) =
          (⟨(y₀ * n) ^ s, hwX⟩ : ↥X) ^ 3 := Subtype.ext (by simp)
      rw [e, map_pow, hπw, ← pow_mul, mul_comm, pow_mul, hy3, one_pow]
    have h2 := (mk_eq_one_iff (pow_mem hwX 3)).mp h1
    have h3 : (((y₀ * n) ^ s) ^ 3) ^ (3 ^ e) = 1 := by
      rw [← pow_mul, ← pow_mul, show s * (3 * 3 ^ e) = (3 ^ e * s) * 3 by ring, pow_mul, ← hzs,
        pow_orderOf_eq_one, one_pow]
    have hθ3 : ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) X) := by
      obtain ⟨-, -, h3', -⟩ :=
        solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
      rwa [inSubgroup, Subgroup.card_map_of_injective X.subtype_injective]
    have h4 : orderOf (((y₀ * n) ^ s) ^ 3) ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one h3
    have h5 := Subgroup.orderOf_dvd_natCard _ h2
    have h6 : Nat.Coprime (3 ^ e) (Nat.card (inSubgroup (aschbacherSolvableCore 3) X)) :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
    have h7 : orderOf (((y₀ * n) ^ s) ^ 3) = 1 := by
      have := Nat.dvd_gcd h4 h5
      rw [h6] at this
      exact Nat.dvd_one.mp this
    exact orderOf_eq_one_iff.mp h7
  have hwAmem : (y₀ * n) ^ s ∈ A := Sec4.mem_of_maximal_of_commute hAmax hw3 hwA
  obtain ⟨i, hi⟩ := hC.exists_zpow_of_trivial hDA hxA hAD hD1 hwAmem
  have hσxconj : sig X x = MulAut.conj m := by
    ext γ
    rw [hm, MulAut.conj_apply]
  have hcen : (m ^ i)⁻¹ * y ^ s ∈ Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    rw [Subgroup.mem_center_iff]
    intro γ
    have h1 := hi γ
    rw [sig_of_mem hwX, hπw, hσxconj, ← map_zpow, MulAut.conj_apply] at h1
    calc γ * ((m ^ i)⁻¹ * y ^ s) = (m ^ i)⁻¹ * (m ^ i * γ * (m ^ i)⁻¹) * y ^ s := by group
      _ = (m ^ i)⁻¹ * (y ^ s * γ * (y ^ s)⁻¹) * y ^ s := by rw [h1]
      _ = (m ^ i)⁻¹ * y ^ s * γ := by group
  have hmiK : (m ^ i)⁻¹ ∈ K := by
    have e : (m ^ i)⁻¹ = ((m ^ i)⁻¹ * y ^ s) * (y ^ s)⁻¹ := by group
    rw [e]
    exact mul_mem (hZK hcen) (inv_mem (pow_mem hyK s))
  have hmi1 : (m ^ i)⁻¹ = 1 := by
    have h1 : (m ^ i)⁻¹ ∈ Subgroup.zpowers m ⊓ K :=
      Subgroup.mem_inf.mpr ⟨inv_mem (zpow_mem (Subgroup.mem_zpowers m) i), hmiK⟩
    rw [hmK] at h1
    exact (Subgroup.mem_bot.mp h1)
  rw [hmi1, one_mul] at hcen
  exact hyZ s hs3 hcen

theorem Base.exists_nontrivial (hC : Base A a X)
    (hT : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
      CFSG.Blueprint.NativeSporadic.ON)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) (ha1 : a ≠ 1)
    {D : Subgroup G} (hD : IsHyperplane A D) (haD : a ∈ D)
    (hα : ∀ B' : Subgroup G, IsHyperplane A B' → a ∈ B' → B' ≠ D →
      ¬ ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, B'⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) :
    ∃ δ ∈ D, ∃ γ, sig X δ γ ≠ γ := by
  by_contra hall
  push Not at hall
  obtain ⟨B', hB', haB', hB'D⟩ := exists_hyperplane_ne hC.isE27 hD hC.mem ha1 haD
  have hB'D' : ¬ B' ≤ D := by
    intro hle
    apply hB'D
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := hD.2
    have h2 := hB'.2
    omega
  obtain ⟨x, hxB', hxD⟩ := Set.not_subset.mp hB'D'
  have hxA : x ∈ A := hB'.1 hxB'
  have hAD := le_sup_zpowers_of_not_mem hC.isE27 hD hxA hxD
  by_cases hx : ∃ γ, sig X x γ ≠ γ
  · exact hC.false_of_trivial hT hAmax hD.1 hxA hAD hall hx
  · push Not at hx
    apply hα B' hB' haB' hB'D
    rw [Subgroup.commutator_le]
    intro m hm β hβ
    obtain ⟨o, ho, y, hy, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hC.X_le_normalizer_O hm
    obtain ⟨i, hi⟩ := hC.exists_zpow_of_trivial hD.1 hxA hAD hall (hB'.1 hβ)
    refine hC.commutator_mem_O (hC.le_centralizer (hB'.1 hβ)) ho hy ?_
    rw [hi]
    exact zpow_apply_eq_of_apply_eq (hx _) i

theorem Base.le_sup_lB_of_nontrivial (hC : Base A a X)
    (hT : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
      CFSG.Blueprint.NativeSporadic.ON)
    {D : Subgroup G} (hDA : D ≤ A) {δ : G} (hδD : δ ∈ D) (hδ : ∃ γ, sig X δ γ ≠ γ)
    (hLD : lB A D ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hcard : 1080 ≤ Nat.card (img a X (lB A D)))
    {R : Subgroup G} (hRN : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hRD : R ≤ Subgroup.centralizer (D : Set G)) (hR3 : ¬ 3 ∣ Nat.card R) :
    R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ lB A D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hC.isPerfect
  obtain ⟨ψ⟩ := ON134.nonempty_equiv_model hC.isPerfect hT
  have hδA : δ ∈ A := hDA hδD
  obtain ⟨m, hm3, hm⟩ := hC.exists_conj_of_mem hT hδA
  have hmz : m ∉ Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    intro hmz
    obtain ⟨γ, hγ⟩ := hδ
    apply hγ
    rw [hm, ← Subgroup.mem_center_iff.mp hmz γ, mul_inv_cancel_right]
  have hm1 : m ≠ 1 := fun h1 => hmz (h1 ▸ one_mem _)
  have hmo : orderOf m = 3 := orderOf_eq_prime hm3 hm1
  obtain ⟨K, hCK, hmK, hZK, ρ, hρ, hker⟩ := Sec15.Proof156Res4.exists_centralizer_eq ψ hm3 hmz
  set C := Subgroup.centralizer ({m} : Set (↥X ⧸ aschbacherSolvableCore 3 ↥X)) with hCdef
  have hK : Nat.card K = 1080 := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    have h2 : Nat.card ρ.ker =
        Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :=
      Nat.card_congr ⟨fun k => ⟨(k : ↥K), (hker _).mp k.2⟩,
        fun z => ⟨⟨z, hZK z.2⟩, (hker _).mpr z.2⟩, fun k => rfl, fun z => rfl⟩
    rw [h2, hT.1, hρ, Item148HJ.card_alternatingGroup_six] at h1
    omega
  have hKC : K ≤ C := hCK ▸ le_sup_right
  have hmcomm : ∀ k ∈ K, m * k = k * m := fun k hk =>
    Subgroup.mem_centralizer_iff.mp (hKC hk) m (Set.mem_singleton m)
  have hmN : Subgroup.zpowers m ≤ Subgroup.normalizer (K : Set _) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem (fun k hk => ?_) (fun k hk => ?_)
    · rw [hmcomm k hk, mul_inv_cancel_right]
      exact hk
    · have h1 : m⁻¹ * k = k * m⁻¹ := by
        calc m⁻¹ * k = m⁻¹ * (k * m) * m⁻¹ := by group
          _ = m⁻¹ * (m * k) * m⁻¹ := by rw [hmcomm k hk]
          _ = k * m⁻¹ := by group
      rw [h1, inv_mul_cancel_right]
      exact hk
  have hzcomm : ∀ (i : ℤ), ∀ k ∈ K, m ^ i * k = k * m ^ i := fun i k hk =>
    ((Commute.zpow_left (hmcomm k hk) i) : m ^ i * k = k * m ^ i)
  have hdecomp : ∀ g ∈ C, ∃ i : ℤ, ∃ k ∈ K, g = k * m ^ i := by
    intro g hg
    rw [hCK, sup_comm] at hg
    obtain ⟨k, hk, z, hz, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hmN hg
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨i, k, hk, rfl⟩
  have hCC : ⁅C, C⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨i, k₁, hk₁, rfl⟩ := hdecomp g₁ hg₁
    obtain ⟨j, k₂, hk₂, rfl⟩ := hdecomp g₂ hg₂
    rw [commutatorElement_mul_of_commute (hzcomm i k₂ hk₂) (hzcomm j k₁ hk₁)
      (by rw [← zpow_add, ← zpow_add, add_comm])]
    exact Subgroup.commutator_le_self K (Subgroup.commutator_mem_commutator hk₁ hk₂)
  have hLDO : lB A D ≤ Subgroup.normalizer
      (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    hLD.trans (sup_le Subgroup.le_normalizer hC.X_le_normalizer_O)
  have hδC : lB A D ≤ Subgroup.centralizer ({δ} : Set G) :=
    (lB_le_centralizer A D).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hδD))
  have hΛC : img a X (lB A D) ≤ C := by
    intro l hl
    have h1 := hC.sig_fixed_img (hC.le_centralizer hδA) hLDO hδC l hl
    rw [hm] at h1
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    calc l * m = m * l * m⁻¹ * m := by rw [h1]
      _ = m * l := by group
  have hΛp := hC.isPerfect_img (isPerfect_lB A D) hLD
  have hΛK : img a X (lB A D) ≤ K := by
    rw [← (Subgroup.isPerfect_iff).mp hΛp]
    exact (Subgroup.commutator_mono hΛC hΛC).trans hCC
  have hKΛ : K ≤ img a X (lB A D) := by
    have := Subgroup.eq_of_le_of_card_ge hΛK (by rw [hK]; exact hcard)
    rw [this]
  intro r hr
  obtain ⟨o, ho, y, hy, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hC.X_le_normalizer_O (hRN hr)
  have hδr : δ * (o * y) = o * y * δ :=
    (Subgroup.mem_centralizer_iff.mp (hRD hr) δ hδD)
  have hfix := hC.sig_fixed (hC.le_centralizer hδA) ho hy hδr
  rw [hm] at hfix
  set γ := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (⟨y, hy⟩ : ↥X) with hγ
  have hγC : γ ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    calc γ * m = m * γ * m⁻¹ * m := by rw [hfix]
      _ = m * γ := by group
  have hk3 := coprime_orderOf_of_mem hR3 hr
  have hγk := hC.mk_pow_eq_one ho hy (pow_orderOf_eq_one (o * y))
  obtain ⟨i, κ, hκ, hγeq⟩ := hdecomp γ hγC
  have hmi : m ^ i = 1 := by
    have h1 : (m ^ i * κ) ^ orderOf (o * y) = 1 := by
      rw [hzcomm i κ hκ, ← hγeq]; exact hγk
    rw [(Commute.mul_pow (hzcomm i κ hκ) _)] at h1
    have h2 : (m ^ i) ^ orderOf (o * y) ∈ Subgroup.zpowers m ⊓ K := by
      refine Subgroup.mem_inf.mpr ⟨pow_mem (zpow_mem (Subgroup.mem_zpowers m) i) _, ?_⟩
      have e : (m ^ i) ^ orderOf (o * y) = (κ ^ orderOf (o * y))⁻¹ :=
        eq_inv_of_mul_eq_one_left h1
      rw [e]
      exact inv_mem (pow_mem hκ _)
    rw [hmK, Subgroup.mem_bot] at h2
    have h3 : orderOf (m ^ i) ∣ orderOf (o * y) := orderOf_dvd_of_pow_eq_one h2
    have h4 : orderOf (m ^ i) ∣ 3 := by
      have : (m ^ i) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm3, one_zpow]
      exact orderOf_dvd_of_pow_eq_one this
    have h5 : orderOf (m ^ i) ∣ Nat.gcd (orderOf (o * y)) 3 := Nat.dvd_gcd h3 h4
    rw [hk3, Nat.dvd_one] at h5
    exact orderOf_eq_one_iff.mp h5
  rw [hmi, mul_one] at hγeq
  have hγK : γ ∈ K := by rw [hγeq]; exact hκ
  have hyO := hC.mem_sup_of_mk_mem_img hy (hKΛ hγK)
  exact mul_mem (Subgroup.mem_sup_left ho) hyO

theorem Base.card_img_lB_ge
    (hC : Base A a X)
    {L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {D : Subgroup G} {e f : G} {Le : Subgroup G} (hD : IsHyperplane A D)
    (hc : IsLBConfig A D e f Le)
    (hLD : lB A D ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) :
    1080 ≤ Nat.card (img a X (lB A D)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hO
  set J := inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({f} : Set G)) with hJdef
  have hLBJ : lB A D = J := Item148HJ.lB_eq_residual h hD hc
  obtain ⟨hdL, -, hq, hZ, -, htc, -⟩ := Item148HJ.resProj_facts h hD hc
  have hJN : J ≤ Subgroup.normalizer (O : Set G) :=
    (hLBJ ▸ hLD).trans (sup_le Subgroup.le_normalizer hC.X_le_normalizer_O)
  have hO3 : Nat.Coprime 3 (Nat.card O) := coprime_card_pPrimeCoreOf 3 _
  set M : Subgroup ↥J := O.subgroupOf J with hM
  have hMn : M.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hJN
  have hMcard : Nat.card M = Nat.card (O ⊓ J : Subgroup G) := by
    rw [hM, ← Subgroup.card_map_of_injective J.subtype_injective, Subgroup.subgroupOf_map_subtype]
  have hM3 : ¬ 3 ∣ Nat.card M := by
    rw [hMcard]
    intro h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO3
      (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hMker := Item148HJ.le_ker_of_normal (Item148HJ.resProj Le f) hq hZ hMn hM3
  have hrange : Nat.card (Item148HJ.resProj Le f).range = 1080 :=
    Res7DescFix.card_eq_of_isTripleCover_a6 htc
  have hJcard : Nat.card J = 1080 * Nat.card (Item148HJ.resProj Le f).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Item148HJ.resProj Le f).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (Item148HJ.resProj Le f)).toEquiv,
      hrange]
  have hJge : 1080 * Nat.card (J ⊓ O : Subgroup G) ≤ Nat.card J := by
    rw [hJcard, inf_comm, ← hMcard]
    exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hMker)
  have h1 := hC.card_img_mul (hLBJ ▸ hLD)
  rw [hLBJ]
  have hpos : 0 < Nat.card (J ⊓ O : Subgroup G) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [h1]
  exact hJge

theorem Base.le_qBound_on
    (hC : Base A a X)
    (hT : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
      CFSG.Blueprint.NativeSporadic.ON)
    {L : Subgroup G} {c : G} (h : Sec14Std G A c L) (ha1 : a ≠ 1) {D : Subgroup G}
    (hD : IsHyperplane A D) (haD : a ∈ D)
    (hα : ∀ B' : Subgroup G, IsHyperplane A B' → a ∈ B' → B' ≠ D →
      ¬ ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, B'⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)))
    (hLD : lB A D ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hconf : ∃ (e f : G) (Le : Subgroup G), IsLBConfig A D e f Le)
    {R : Subgroup G}
    (hRN : R ≤ (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ⊓
      Subgroup.centralizer (D : Set G))
    (hR3 : ¬ 3 ∣ Nat.card R) : R ≤ qBound A (lB A) D := by
  obtain ⟨δ, hδD, hδ⟩ := hC.exists_nontrivial hT h.maximal_isElemAbelian ha1 hD haD hα
  obtain ⟨e, f, Le, hc⟩ := hconf
  have hcard := hC.card_img_lB_ge h hD hc hLD
  have hRL := hC.le_sup_lB_of_nontrivial hT hD.1 hδD hδ hLD hcard (hRN.trans inf_le_left)
    (hRN.trans inf_le_right) hR3
  exact (le_inf hRL (hRN.trans inf_le_right)).trans ((Res7MemFix.inf_centralizer_le_of_le_sup haD
    (le_of_eq (sup_comm _ _))).trans
    (by rw [qBound]; exact sup_le (le_sup_left.trans le_sup_left) le_sup_right))

end Res9Fix

end CFSG.RankThree.PartTwo.Sec14
