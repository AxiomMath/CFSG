module

public import CFSG.LocalAnalysis.StandardType.GGPZTrivTypeA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification TypeA

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pfa_mem_subgroupOf_of_bar_eq {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {J EJ : Subgroup G} (hEJ : EJ ≤ J) (hE : IsElemAbelian p EJ)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J)) {w : ↥J} {y : ↥EJ}
    (hwy : (QuotientGroup.mk' (Subgroup.center ↥J)) w =
      (QuotientGroup.mk' (Subgroup.center ↥J)) (Subgroup.inclusion hEJ y))
    (hwp : w ^ p = 1) : w ∈ EJ.subgroupOf J := by
  have hp : p.Prime := Fact.out
  set z : ↥J := w * (Subgroup.inclusion hEJ y)⁻¹ with hz
  have hzbar : (QuotientGroup.mk' (Subgroup.center ↥J)) z = 1 := by
    rw [hz, map_mul, map_inv, hwy, mul_inv_cancel]
  have hzcenter : z ∈ Subgroup.center ↥J := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center ↥J)]
    exact MonoidHom.mem_ker.mpr hzbar
  have hy1 : (Subgroup.inclusion hEJ y) ^ p = 1 := by
    apply Subtype.ext
    have h := hE.2 (y : G) y.2
    simpa using h
  have hweq : w = z * Subgroup.inclusion hEJ y := by
    rw [hz]; group
  have hzp : z ^ p = 1 := by
    have hcomm : Commute z (Subgroup.inclusion hEJ y) :=
      (Subgroup.mem_center_iff.mp hzcenter _).symm
    have h1 : (z * Subgroup.inclusion hEJ y) ^ p = 1 := by rw [← hweq]; exact hwp
    rw [hcomm.mul_pow, hy1, mul_one] at h1
    exact h1
  have ho1 : orderOf z ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hzp
  have ho2 : orderOf z ∣ Nat.card ↥(Subgroup.center ↥J) := by
    rw [← Nat.card_zpowers z]
    exact Subgroup.card_dvd_of_le (by rw [Subgroup.zpowers_le]; exact hzcenter)
  have hcop : Nat.Coprime p (Nat.card ↥(Subgroup.center ↥J)) :=
    (hp.coprime_iff_not_dvd).mpr hZ
  have hone : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop ho1 ho2
  have hz1 : z = 1 := orderOf_eq_one_iff.mp hone
  have hwy' : w = Subgroup.inclusion hEJ y := by rw [hweq, hz1, one_mul]
  rw [hwy', Subgroup.mem_subgroupOf]
  exact y.2

theorem ggPZ_fixed_trivial_typeA
    {G : Type} [Group G] [Finite G] {p l n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {J EJ : Subgroup G} (hl : 2 ≤ l) (hpq : p ∣ 2 ^ n - 1) (hpl : p ∣ l + 3)
    (hJ : GGHasLabel ⟨.A, l, n⟩ (↥J ⧸ Subgroup.center ↥J)) (hJq : IsQuasisimple ↥J)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J)) (hEJ : EJ ≤ J) (hE : IsElemAbelian p EJ)
    (hcard : Nat.card ↥EJ = p ^ l) :
    ∀ a ∈ EJ, (∀ g ∈ J, g ∈ Subgroup.normalizer (EJ : Set G) → g * a * g⁻¹ = a) → a = 1 := by
  classical
  unfold GGHasLabel at hJ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hJ
  unfold LargeEvenRecipeLinear at hJ
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hJ
  let : Field K := hKfield
  let : Finite K := hKfin
  have : Group.IsPerfect ↥J := hJq.1
  have hp : p.Prime := Fact.out
  have hpK : p ∣ Nat.card K - 1 := by rw [hKcard]; exact hpq
  have hchar : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    refine charP_of_card_eq_prime_pow (R := K) (p := 2) (f := n) ?_
    rw [← Nat.card_eq_fintype_card, hKcard]
  let : CharP K 2 := hchar
  have hpd : ¬ p ∣ l + 1 := by
    intro h
    have h2 : p ∣ 2 := by
      have hh := Nat.dvd_sub hpl h
      rwa [show l + 3 - (l + 1) = 2 by omega] at hh
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hcop : Nat.Coprime p (l + 1) := hp.coprime_iff_not_dvd.mpr hpd
  let d := l + 1
  have hd0 : 0 < d := by omega
  have h3d : 3 ≤ d := by omega
  have hcopd : Nat.Coprime p d := hcop
  let L' : Type := ↥J ⧸ Subgroup.center ↥J
  let ψ : L' →* projectiveSL d K := (TypeA.recipeEquiv d K).toMonoidHom.comp e.toMonoidHom
  let φ : Matrix.SpecialLinearGroup (Fin d) K →* L' :=
    e.symm.toMonoidHom.comp ((TypeA.recipeEquiv d K).symm.toMonoidHom.comp (proj d K))
  have hφψ : ∀ g : Matrix.SpecialLinearGroup (Fin d) K, ψ (φ g) = proj d K g := by
    intro g
    simp only [φ, ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨y, rfl⟩ := (TypeA.recipeEquiv d K).surjective x
    obtain ⟨z, rfl⟩ := e.surjective y
    exact ⟨z, rfl⟩
  have hφs : Function.Surjective φ := by
    intro x
    obtain ⟨y, rfl⟩ := e.symm.surjective x
    obtain ⟨z, rfl⟩ := (TypeA.recipeEquiv d K).symm.surjective y
    obtain ⟨w, rfl⟩ := proj_surjective d K z
    exact ⟨w, rfl⟩
  have hker : ψ.ker ≤ Subgroup.center L' := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : e x = 1 := (TypeA.recipeEquiv d K).injective (by simpa [ψ] using hx)
    have hx1 : x = 1 := e.injective (by rw [hx', map_one])
    rw [hx1]
    exact Subgroup.one_mem _
  have hperf : commutator L' = ⊤ := by
    have hperfJ : (⁅(⊤ : Subgroup ↥J), ⊤⁆ : Subgroup ↥J) = ⊤ := hJq.1.commutator_eq_top
    have hmap := Subgroup.map_commutator (⊤ : Subgroup ↥J) (⊤ : Subgroup ↥J)
      (QuotientGroup.mk' (Subgroup.center ↥J))
    rw [hperfJ, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective (Subgroup.center ↥J))] at hmap
    exact hmap.symm
  let f0 : ↥EJ →* L' := (QuotientGroup.mk' (Subgroup.center ↥J)).comp (Subgroup.inclusion hEJ)
  let A : Subgroup (MulAut L') := f0.range.map (MulAut.conj : L' →* MulAut L')
  have hInt : (EJ.subgroupOf J) ⊓ Subgroup.center ↥J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxEJ : ((x : ↥J) : G) ∈ EJ := Subgroup.mem_subgroupOf.mp hx.1
    have hxp : x ^ p = 1 := by
      apply Subtype.ext
      have := hE.2 ((x : ↥J) : G) hxEJ
      simpa using this
    have hxZ : x ∈ Subgroup.center ↥J := hx.2
    have hdiv : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hxp
    rcases (Nat.dvd_prime hp).mp hdiv with h1 | hp'
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      have hdivc : orderOf (⟨x, hxZ⟩ : ↥(Subgroup.center ↥J)) ∣
          Nat.card ↥(Subgroup.center ↥J) := orderOf_dvd_natCard _
      rw [← Subgroup.orderOf_coe (⟨x, hxZ⟩ : ↥(Subgroup.center ↥J))] at hdivc
      rw [hp'] at hdivc
      exact hZ hdivc
  have hf0_inj : Function.Injective f0 := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    have hx1 : (Subgroup.inclusion hEJ) x ∈ (EJ.subgroupOf J) ⊓ Subgroup.center ↥J := by
      refine ⟨Subgroup.mem_subgroupOf.mpr (by rw [Subgroup.coe_inclusion]; exact x.2), ?_⟩
      rw [← QuotientGroup.ker_mk' (Subgroup.center ↥J)]
      exact MonoidHom.mem_ker.mpr hx
    rw [hInt, Subgroup.mem_bot] at hx1
    exact Subgroup.inclusion_injective hEJ hx1
  have hZc : Subgroup.center L' = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot ↥J
  have hconj_inj : Function.Injective (MulAut.conj : L' →* MulAut L') := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    have hxc : x ∈ Subgroup.center L' := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := congrArg (fun f : MulAut L' => f y) hx
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      calc y * x = (x * y * x⁻¹) * x := by rw [h]
        _ = x * y := by group
    rw [hZc] at hxc
    exact hxc
  let hiso : ↥EJ ≃* ↥A :=
    (MonoidHom.ofInjective hf0_inj).trans (Subgroup.equivMapOfInjective f0.range _ hconj_inj)
  have hiso_apply : ∀ x : ↥EJ, ((hiso x : ↥A) : MulAut L') = MulAut.conj (f0 x) :=
    fun _ => rfl
  have hcardA : Nat.card ↥A = p ^ (d - 1) := by
    rw [show d - 1 = l by omega]
    calc Nat.card ↥A = Nat.card ↥(f0.range) := Subgroup.card_map_of_injective hconj_inj
      _ = Nat.card ↥EJ := (Nat.card_congr (MonoidHom.ofInjective hf0_inj).toEquiv).symm
      _ = p ^ l := hcard
  have hA : IsElemAbelian p A := by
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      intro x y
      calc x * y = hiso (hiso.symm x * hiso.symm y) := by
            rw [map_mul, hiso.apply_symm_apply, hiso.apply_symm_apply]
        _ = hiso (hiso.symm y * hiso.symm x) :=
            congrArg hiso (hE.1.is_comm.comm (hiso.symm x) (hiso.symm y))
        _ = y * x := by rw [map_mul, hiso.apply_symm_apply, hiso.apply_symm_apply]
    · intro x hx
      have h1 : (hiso.symm ⟨x, hx⟩ : ↥EJ) ^ p = 1 := by
        apply Subtype.ext
        have hh := hE.2 ((hiso.symm ⟨x, hx⟩ : ↥EJ) : G) (hiso.symm ⟨x, hx⟩).2
        simpa using hh
      have h2 : (⟨x, hx⟩ : ↥A) ^ p = 1 := by
        rw [← hiso.apply_symm_apply (⟨x, hx⟩ : ↥A), ← map_pow, h1, map_one]
      simpa using congrArg Subtype.val h2
  have hAI : ∀ a ∈ A, ∃ φa ∈ Set.range (conjAut d K), ∀ l : L', φa (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨s, hs⟩ := proj_surjective d K (ψ (f0 x))
    refine ⟨conjAut d K (Matrix.SpecialLinearGroup.toGL s), ⟨s, rfl⟩, fun l => ?_⟩
    rw [LinearFlag.conjAut_toGL, hs, MulAut.conj_apply]
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hperfSL : commutator (Matrix.SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega : 3 ≤ d))).commutator_eq_top
  obtain ⟨φ', hφ's, hφ'ker, hdiag_data, _, hfull_data⟩ :=
    TypeA.exists_diagonal_model hp hpK hd0 hcopd hperfSL hψ hker hperf hφs hφψ hA hAI
  have huniq : ∀ (a : MulAut L') (D : Matrix.SpecialLinearGroup (Fin d) K),
      (∀ s, a (φ' s) = φ' (D * s * D⁻¹)) → a = MulAut.conj (φ' D) := by
    intro a D hact
    ext l
    obtain ⟨s, rfl⟩ := hφ's l
    rw [hact s, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hdiag : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ' a t := by
    intro a ha
    obtain ⟨D, ⟨t, hDt⟩, hDp, hact⟩ := hdiag_data a ha
    exact ⟨t, by rw [huniq a D hact]; exact TypeANbrDvd.actsDiag_conj hDt⟩
  have hAcar : ∀ a ∈ A, ∃ D : Matrix.SpecialLinearGroup (Fin d) K,
      (∃ t : Fin d → K, (D : Matrix (Fin d) (Fin d) K) = diagonal t) ∧ D ^ p = 1 ∧
        a = MulAut.conj (φ' D) := by
    intro a ha
    obtain ⟨D, hD, hDp, hact⟩ := hdiag_data a ha
    exact ⟨D, hD, hDp, huniq a D hact⟩
  have hAfull : ∀ D : Matrix.SpecialLinearGroup (Fin d) K,
      (∃ t : Fin d → K, (D : Matrix (Fin d) (Fin d) K) = diagonal t) → D ^ p = 1 →
        MulAut.conj (φ' D) ∈ A := by
    intro D ⟨t, hDt⟩ hDp
    have ht : ∀ i, t i ^ p = 1 := fun i => by
      have h := congrArg (fun M : Matrix (Fin d) (Fin d) K => M i i)
        (show (((D ^ p : Matrix.SpecialLinearGroup (Fin d) K)) : Matrix (Fin d) (Fin d) K) =
          1 by rw [hDp]; rfl)
      simp only [Matrix.SpecialLinearGroup.coe_pow, hDt, diagonal_pow,
        Matrix.diagonal_apply_eq, Pi.pow_apply, Matrix.one_apply_eq] at h
      exact h
    have htp : ∏ i, t i = 1 := by
      have h := D.2
      rwa [hDt, det_diagonal] at h
    obtain ⟨a, ha, D', hD', hact⟩ := hfull_data hcardA t ht htp
    have hD'D : D' = D := Subtype.ext (hD'.trans hDt.symm)
    have haeq : a = MulAut.conj (φ' D) := by rw [huniq a D' hact, hD'D]
    rw [haeq] at ha
    exact ha
  have hstep : ∀ (τ : Equiv.Perm (Fin d)) (b : MulAut L'),
      b ∈ A → NbrInnerWeylA.permConj φ' τ * b * (NbrInnerWeylA.permConj φ' τ)⁻¹ ∈ A := by
    intro τ b hb
    obtain ⟨D, ⟨t, hDt⟩, hDp, rfl⟩ := hAcar b hb
    have hperm : NbrInnerWeylA.permConj φ' τ = MulAut.conj (φ' (permSL τ.symm)) := rfl
    have heq : MulAut.conj (φ' (permSL τ.symm)) * MulAut.conj (φ' D) *
        (MulAut.conj (φ' (permSL τ.symm)))⁻¹ =
        MulAut.conj (φ' (permSL τ.symm * D * (permSL τ.symm)⁻¹)) := by
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      rw [map_mul, map_mul, map_inv]
    rw [hperm, heq]
    exact hAfull (permSL τ.symm * D * (permSL τ.symm)⁻¹)
      ⟨t ∘ τ.symm, TypeA.coe_permSL_conj hDt τ.symm⟩ (by
      rw [← MulAut.conj_apply, ← map_pow, hDp, map_one])
  have hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    intro σ
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · exact hstep σ b
    · intro hb
      have h1 := hstep σ⁻¹ (NbrInnerWeylA.permConj φ' σ * b * (NbrInnerWeylA.permConj φ' σ)⁻¹) hb
      have h2 : NbrInnerWeylA.permConj φ' σ⁻¹ = (NbrInnerWeylA.permConj φ' σ)⁻¹ :=
        map_inv (NbrInnerWeylA.permConj φ') σ
      rw [h2] at h1
      convert h1 using 1
      group
  intro a ha hfix
  set a₀ : ↥A := hiso ⟨a, ha⟩ with ha₀def
  obtain ⟨t, ha₀t⟩ := hdiag (a₀ : MulAut L') a₀.2
  have ha₀eq : (a₀ : MulAut L') = MulAut.conj (f0 ⟨a, ha⟩) := rfl
  have hperm : ∀ σ : Equiv.Perm (Fin d),
      MulAut.conj (φ' (permSL σ⁻¹)) * (a₀ : MulAut L') *
        (MulAut.conj (φ' (permSL σ⁻¹)))⁻¹ = (a₀ : MulAut L') := by
    intro σ
    let l : L' := φ' (permSL σ⁻¹)
    have hlN : MulAut.conj l ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
      hN σ
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) l
    have hgNorm : g ∈ Subgroup.normalizer ((EJ.subgroupOf J : Subgroup ↥J) : Set ↥J) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hxG : (x : G) ∈ EJ := Subgroup.mem_subgroupOf.mp hx
        have hxbar : QuotientGroup.mk' (Subgroup.center ↥J) x ∈ f0.range := by
          refine MonoidHom.mem_range.mpr ⟨⟨(x : G), hxG⟩, ?_⟩
          show QuotientGroup.mk' (Subgroup.center ↥J)
              (Subgroup.inclusion hEJ ⟨(x : G), hxG⟩) =
            QuotientGroup.mk' (Subgroup.center ↥J) x
          rw [show Subgroup.inclusion hEJ ⟨(x : G), hxG⟩ = x from Subtype.ext rfl]
        have hxA : MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) x) ∈ A :=
          Subgroup.mem_map_of_mem _ hxbar
        have hconjeq : MulAut.conj l *
            MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) x) * (MulAut.conj l)⁻¹ =
            MulAut.conj (l * QuotientGroup.mk' (Subgroup.center ↥J) x * l⁻¹) := by
          rw [← map_mul, ← map_inv, ← map_mul]
        have h1 : MulAut.conj (l * QuotientGroup.mk' (Subgroup.center ↥J) x * l⁻¹) ∈ A :=
          hconjeq ▸ (Subgroup.mem_normalizer_iff.mp hlN _).mp hxA
        obtain ⟨w, hw, hwconj⟩ := Subgroup.mem_map.mp h1
        have hwrange : l * QuotientGroup.mk' (Subgroup.center ↥J) x * l⁻¹ ∈ f0.range := by
          rw [hconj_inj hwconj] at hw
          exact hw
        have hbar_gx : QuotientGroup.mk' (Subgroup.center ↥J) (g * x * g⁻¹) =
            l * QuotientGroup.mk' (Subgroup.center ↥J) x * l⁻¹ := by
          rw [map_mul, map_mul, map_inv, hg]
        have hwrange' : QuotientGroup.mk' (Subgroup.center ↥J) (g * x * g⁻¹) ∈ f0.range := by
          rwa [hbar_gx]
        obtain ⟨y', hy'⟩ := MonoidHom.mem_range.mp hwrange'
        refine pfa_mem_subgroupOf_of_bar_eq (y := y') hEJ hE hZ ?_ ?_
        · exact hy'.symm
        · have hxJp : x ^ p = 1 := by
            apply Subtype.ext
            have h := hE.2 (x : G) hxG
            simpa using h
          rw [← MulAut.conj_apply g x, ← map_pow, hxJp, map_one]
      · intro hx
        set q : ↥J := g * x * g⁻¹ with hq
        have hqG : (q : G) ∈ EJ := Subgroup.mem_subgroupOf.mp hx
        have hqbar : QuotientGroup.mk' (Subgroup.center ↥J) q ∈ f0.range := by
          refine MonoidHom.mem_range.mpr ⟨⟨(q : G), hqG⟩, ?_⟩
          show QuotientGroup.mk' (Subgroup.center ↥J)
              (Subgroup.inclusion hEJ ⟨(q : G), hqG⟩) =
            QuotientGroup.mk' (Subgroup.center ↥J) q
          rw [show Subgroup.inclusion hEJ ⟨(q : G), hqG⟩ = q from Subtype.ext rfl]
        have hqA : MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) q) ∈ A :=
          Subgroup.mem_map_of_mem _ hqbar
        have hlinv : MulAut.conj l⁻¹ ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
          rw [map_inv]
          exact Subgroup.inv_mem _ hlN
        have hconjeq2 : MulAut.conj l⁻¹ *
            MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) q) *
            (MulAut.conj l⁻¹)⁻¹ =
            MulAut.conj (l⁻¹ * QuotientGroup.mk' (Subgroup.center ↥J) q * l) := by
          have hinv : (MulAut.conj l⁻¹)⁻¹ = MulAut.conj l := by
            rw [← map_inv, inv_inv]
          rw [← map_mul, hinv, ← map_mul]
        have h2 : MulAut.conj
            (l⁻¹ * QuotientGroup.mk' (Subgroup.center ↥J) q * l) ∈ A :=
          hconjeq2 ▸ (Subgroup.mem_normalizer_iff.mp hlinv _).mp hqA
        obtain ⟨w, hw, hwconj⟩ := Subgroup.mem_map.mp h2
        have hwrange : l⁻¹ * QuotientGroup.mk' (Subgroup.center ↥J) q * l ∈ f0.range := by
          rw [hconj_inj hwconj] at hw
          exact hw
        have hbarx : QuotientGroup.mk' (Subgroup.center ↥J) x =
            l⁻¹ * QuotientGroup.mk' (Subgroup.center ↥J) q * l := by
          have hxeq : x = g⁻¹ * q * g := by rw [hq]; group
          rw [hxeq, map_mul, map_mul, map_inv, hg]
        have hxrange : QuotientGroup.mk' (Subgroup.center ↥J) x ∈ f0.range := by
          rwa [hbarx]
        obtain ⟨y', hy'⟩ := MonoidHom.mem_range.mp hxrange
        refine pfa_mem_subgroupOf_of_bar_eq (y := y') hEJ hE hZ ?_ ?_
        · exact hy'.symm
        · have hqJp : q ^ p = 1 := by
            apply Subtype.ext
            have h := hE.2 (q : G) hqG
            simpa using h
          have hxconj : x = (MulAut.conj g⁻¹) q := by
            rw [MulAut.conj_apply]
            rw [hq]
            group
          rw [hxconj, ← map_pow, hqJp, map_one]
    have hgNormG : (g : G) ∈ Subgroup.normalizer (EJ : Set G) := by
      have h' := hgNorm
      rw [← Subgroup.subgroupOf_normalizer_eq hEJ, Subgroup.mem_subgroupOf] at h'
      exact h'
    have hfixg : (g : G) * a * (g : G)⁻¹ = a := hfix (g : G) g.2 hgNormG
    let y : ↥EJ := ⟨(g : G) * a * (g : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hgNormG a).mp ha⟩
    have hy : y = ⟨a, ha⟩ := Subtype.ext hfixg
    have hinc : (Subgroup.inclusion hEJ y : ↥J) =
        g * Subgroup.inclusion hEJ ⟨a, ha⟩ * g⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion,
        Subgroup.coe_inclusion]
    have hf0y : f0 y = l * f0 ⟨a, ha⟩ * l⁻¹ := by
      show QuotientGroup.mk' (Subgroup.center ↥J) (Subgroup.inclusion hEJ y) =
        l * f0 ⟨a, ha⟩ * l⁻¹
      rw [hinc, map_mul, map_mul, map_inv, hg]
      rfl
    have hconj : (hiso y : MulAut L') =
        MulAut.conj l * (a₀ : MulAut L') * (MulAut.conj l)⁻¹ := by
      rw [hiso_apply, hf0y, ha₀eq, ← map_mul, (map_inv (MulAut.conj) l).symm, ← map_mul]
    have hmain : MulAut.conj l * (a₀ : MulAut L') * (MulAut.conj l)⁻¹ =
        (a₀ : MulAut L') := by
      rw [← hconj, hy]
    exact hmain
  have hc : ∀ k m : Fin d, t k = t m := by
    intro k m
    by_cases hkm : k = m
    · rw [hkm]
    · obtain ⟨j, hjk, hjm⟩ := TypeANbrDvd.exists_ne_of_two h3d k m
      have hconjact := ha₀t.conj_perm (Equiv.swap k m)⁻¹
      rw [hperm (Equiv.swap k m)] at hconjact
      have hratio := ha₀t.ratio hφ'ker hconjact hjk.symm
      simp only [Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hjk hjm] at hratio
      exact mul_right_cancel₀ (inv_ne_zero (ha₀t.ne_zero j)) hratio
  have ha₀one : (a₀ : MulAut L') = 1 := ha₀t.eq_one hd0 hφ's hc
  have hmem : hiso ⟨a, ha⟩ = hiso 1 := by
    rw [map_one, ← ha₀def]
    exact Subtype.ext ha₀one
  have hsub : (⟨a, ha⟩ : ↥EJ) = 1 := hiso.injective hmem
  exact Subtype.ext_iff.mp hsub

end CFSG.StandardType

end
