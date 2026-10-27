module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreElt
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB TableBSymp NbrOrth Multiplicative

namespace CorFourTwoMore

section Coord

variable {p m : ℕ}

theorem eq_mulSingle_of_dinv (hp : p.Prime) (hp2 : p ≠ 2) {i j k : Fin m} (hjk : j ≠ k)
    {g : Fin m → Multiplicative (ZMod p)} (hj : dinv i j g = g⁻¹) (hk : dinv i k g = g⁻¹) :
    g = Pi.mulSingle i (g i) := by
  funext l
  by_cases hli : l = i
  · subst hli
    rw [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hli]
    have key : ∀ t, l ≠ t → dinv i t g = g⁻¹ → g l = 1 := by
      intro t hlt ht
      have h1 := congrFun ht l
      rw [dinv, Function.update_of_ne hli, Function.update_of_ne hlt, Pi.inv_apply] at h1
      have h2 : toAdd (g l) = -toAdd (g l) := by
        rw [← toAdd_inv]
        exact congrArg toAdd h1
      rw [← ofAdd_toAdd (g l), SpCoord.coord_eq_zero_of_eq_neg hp hp2 h2, ofAdd_zero]
    by_cases hlj : l = j
    · exact key k (by rw [hlj]; exact hjk) hk
    · exact key j hlj hj

end Coord

section Torus

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem ggTorusIrredSecElt_of_torus {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    {Ω : Subgroup (GL ι K)} (T : (Fin m → Multiplicative (ZMod p)) →* GL ι K)
    (hTΩ : ∀ f, T f ∈ Ω) (s : Fin m → Fin m → GL ι K) (hsΩ : ∀ i k, s i k ∈ Ω)
    (hs : ∀ i k, i ≠ k → ∀ f, s i k * T f * (s i k)⁻¹ = T (dinv i k f))
    (P : Equiv.Perm (Fin m) →* GL ι K)
    (hPΩ : ∀ σ τ : Equiv.Perm (Fin m), P σ * P τ * (P σ)⁻¹ * (P τ)⁻¹ ∈ Ω)
    (hP : ∀ σ f, P σ * T f * (P σ)⁻¹ = T (f ∘ ⇑σ⁻¹))
    (htor : ∀ E : Subgroup Ω, IsElemAbelian p E → p ^ m ≤ Nat.card E →
      ∃ g : GL ι K, (∀ x ∈ Ω, g⁻¹ * x * g ∈ Ω) ∧
        ∀ x : Ω, x ∈ E ↔ ∃ f, T f = g * x * g⁻¹) :
    GGTorusIrredSecElt p m Ω := by
  classical
  have := Fact.mk hp
  intro E hE hr h3
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨g, hgΩ, hmemE⟩ := htor E hE hr
  set c : GL ι K →* GL ι K := (MulAut.conj g⁻¹).toMonoidHom with hc
  have hcapp : ∀ x, c x = g⁻¹ * x * g := fun x => by
    rw [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hcΩ : ∀ x ∈ Ω, c x ∈ Ω := fun x hx => by rw [hcapp]; exact hgΩ x hx
  set τ : (Fin m → Multiplicative (ZMod p)) →* Ω :=
    (c.comp T).codRestrict Ω fun f => hcΩ _ (hTΩ f) with hτ
  have hτapp : ∀ f, ((τ f : Ω) : GL ι K) = g⁻¹ * T f * g := fun f => hcapp (T f)
  have hτE : τ.range = E := by
    ext x
    rw [MonoidHom.mem_range, hmemE]
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f, by rw [hτapp]; group⟩
    · rintro ⟨f, hf⟩
      exact ⟨f, Subtype.ext (by rw [hτapp, hf]; group)⟩
  have hτmem : ∀ x ∈ E, ∃ f, τ f = x := fun x hx => by
    rw [← hτE] at hx
    exact hx
  set S : Fin m → Fin m → Ω := fun i k => ⟨c (s i k), hcΩ _ (hsΩ i k)⟩ with hS
  set C : Equiv.Perm (Fin m) → Equiv.Perm (Fin m) → Ω := fun σ σ' =>
    ⟨c (P σ * P σ' * (P σ)⁻¹ * (P σ')⁻¹), hcΩ _ (hPΩ σ σ')⟩ with hC
  have hSconj : ∀ i k, i ≠ k → ∀ f, S i k * τ f * (S i k)⁻¹ = τ (dinv i k f) := by
    intro i k hik f
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hτapp, hτapp]
    change c (s i k) * (g⁻¹ * T f * g) * (c (s i k))⁻¹ = _
    rw [hcapp, ← hs i k hik f]
    group
  have hCconj : ∀ σ σ' f, C σ σ' * τ f * (C σ σ')⁻¹ = τ (f ∘ ⇑(σ * σ' * σ⁻¹ * σ'⁻¹)⁻¹) := by
    intro σ σ' f
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hτapp, hτapp]
    change c (P σ * P σ' * (P σ)⁻¹ * (P σ')⁻¹) * (g⁻¹ * T f * g) *
      (c (P σ * P σ' * (P σ)⁻¹ * (P σ')⁻¹))⁻¹ = _
    have e : P σ * P σ' * (P σ)⁻¹ * (P σ')⁻¹ = P (σ * σ' * σ⁻¹ * σ'⁻¹) := by
      simp only [map_mul, map_inv]
    rw [hcapp, e, ← hP]
    group
  set W : Set Ω := {w | (∃ i k, i ≠ k ∧ w = S i k) ∨
    ∃ j t u : Fin m, j ≠ t ∧ j ≠ u ∧ t ≠ u ∧ w = C (Equiv.swap j t) (Equiv.swap j u)} with hW
  have hWE : ∀ w ∈ W, ∀ e ∈ E, w * e * w⁻¹ ∈ E := by
    rintro w hw e he
    obtain ⟨f, rfl⟩ := hτmem e he
    rw [← hτE]
    rcases hw with ⟨i, k, hik, rfl⟩ | ⟨j, t, u, -, -, -, rfl⟩
    · exact ⟨_, (hSconj i k hik f).symm⟩
    · exact ⟨_, (hCconj _ _ f).symm⟩
  have hirrE : ∀ E' : Subgroup Ω, E' ≤ E → (∀ w ∈ W, ∀ e ∈ E', w * e * w⁻¹ ∈ E') →
      E' = ⊥ ∨ E' = E := by
    intro E' hE'E hE'inv
    have hinvF : ∀ i k, i ≠ k → ∀ f ∈ E'.comap τ, dinv i k f ∈ E'.comap τ := by
      intro i k hik f hf
      rw [Subgroup.mem_comap, ← hSconj i k hik]
      exact hE'inv _ (Or.inl ⟨i, k, hik, rfl⟩) _ hf
    have hpermF : ∀ j t u : Fin m, j ≠ t → j ≠ u → t ≠ u → ∀ f ∈ E'.comap τ,
        f ∘ ⇑(swapComm j t u)⁻¹ ∈ E'.comap τ := by
      intro j t u hjt hju htu f hf
      rw [Subgroup.mem_comap, swapComm, ← hCconj]
      exact hE'inv _ (Or.inr ⟨j, t, u, hjt, hju, htu, rfl⟩) _ hf
    rcases eq_bot_or_eq_top_of_dinv hp hp2 hm _ hinvF hpermF with hbot | htop
    · left
      rw [eq_bot_iff]
      intro e he
      obtain ⟨f, rfl⟩ := hτmem e (hE'E he)
      have hf : f ∈ E'.comap τ := he
      rw [hbot, Subgroup.mem_bot] at hf
      rw [hf, map_one]
      exact Subgroup.one_mem _
    · right
      refine le_antisymm hE'E fun e he => ?_
      obtain ⟨f, rfl⟩ := hτmem e he
      have hf : f ∈ E'.comap τ := htop ▸ Subgroup.mem_top f
      exact hf
  have hτinj : Function.Injective τ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hinvK : ∀ i k, i ≠ k → ∀ f ∈ τ.ker, dinv i k f ∈ τ.ker := by
      intro i k hik f hf
      rw [MonoidHom.mem_ker] at hf ⊢
      rw [← hSconj i k hik, hf, mul_one, mul_inv_cancel]
    have hpermK : ∀ j t u : Fin m, j ≠ t → j ≠ u → t ≠ u → ∀ f ∈ τ.ker,
        f ∘ ⇑(swapComm j t u)⁻¹ ∈ τ.ker := by
      intro j t u _ _ _ f hf
      rw [MonoidHom.mem_ker] at hf ⊢
      rw [swapComm, ← hCconj, hf, mul_one, mul_inv_cancel]
    rcases eq_bot_or_eq_top_of_dinv hp hp2 hm _ hinvK hpermK with hbot | htop
    · exact hbot
    · exfalso
      have hEb : E = ⊥ := by
        rw [← hτE, eq_bot_iff]
        rintro _ ⟨f, rfl⟩
        have hf : f ∈ τ.ker := htop ▸ Subgroup.mem_top f
        rw [MonoidHom.mem_ker] at hf
        rw [hf]
        exact Subgroup.one_mem _
      rw [hEb, Subgroup.card_bot] at h3
      exact absurd h3 (not_le.mpr (Nat.one_lt_pow (by norm_num) hp.one_lt))
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    TableB.IsElemAbelian.comm hE hx hy
  set i₀ : Fin m := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin m := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin m := ⟨2, by omega⟩ with hi₂
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [hi₀, hi₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [hi₁, hi₂, Fin.ext_iff]
  set δ : Fin m → Multiplicative (ZMod p) := Pi.mulSingle i₀ (ofAdd 1) with hδ
  have hδE : τ δ ∈ E := hτE ▸ ⟨δ, rfl⟩
  have hδinv : ∀ k, i₀ ≠ k → S i₀ k * τ δ * (S i₀ k)⁻¹ = (τ δ)⁻¹ := fun k hk => by
    rw [hSconj i₀ k hk, hδ, dinv_mulSingle_self hk, map_inv]
  have hδ1 : τ δ ≠ 1 := by
    intro h1
    have h2 := congrFun (hτinj (h1.trans (map_one τ).symm)) i₀
    rw [hδ, Pi.mulSingle_eq_same, Pi.one_apply] at h2
    have h3 : (1 : ZMod p) = 0 := by simpa using congrArg toAdd h2
    exact one_ne_zero h3
  refine ⟨m, τ, W, hτE, fun L' _ ψ hψ hker => exists_torus_section hψ hker hodd τ
    fun i j => ?_, hWE, hirrE, ?_, fun F hFE hFmul hFW => ?_⟩
  · obtain ⟨k, hki, hkj⟩ := exists_ne_ne_of_three_le hm i j
    refine ⟨S i k, ?_, fun hji => ?_⟩
    · rw [torusBasis, hSconj i k (Ne.symm hki), dinv_mulSingle_self (Ne.symm hki), map_inv]
    · rw [torusBasis, hSconj i k (Ne.symm hki), dinv_mulSingle_of_ne hji (Ne.symm hkj)]
  ·
    refine ⟨S i₀ i₁, Or.inl ⟨i₀, i₁, h01, rfl⟩, τ δ, hδE, fun heq => hδ1 ?_⟩
    rw [hδinv i₁ h01] at heq
    have h2 : τ δ ^ 2 = 1 := by
      rw [sq]
      calc τ δ * τ δ = (τ δ)⁻¹ * τ δ := by rw [heq]
        _ = 1 := inv_mul_cancel _
    have hpu : τ δ ^ p = 1 := hE.2 _ hδE
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hpu))
  ·
    have hF1 : F 1 = 1 := by
      have h1 := hFmul 1 E.one_mem 1 E.one_mem
      rw [mul_one] at h1
      exact mul_eq_left.mp h1.symm
    have hFinv : ∀ x ∈ E, F x⁻¹ = (F x)⁻¹ := by
      intro x hx
      have h1 := hFmul x hx x⁻¹ (E.inv_mem hx)
      rw [mul_inv_cancel, hF1] at h1
      exact eq_inv_of_mul_eq_one_right h1.symm
    obtain ⟨g', hg'⟩ := hτmem (F (τ δ)) (hFE _ hδE)
    have hinvS : ∀ k, i₀ ≠ k → dinv i₀ k g' = g'⁻¹ := by
      intro k hk
      apply hτinj
      have h2 := hFW (S i₀ k) (Or.inl ⟨i₀, k, hk, rfl⟩) _ hδE
      rw [hδinv k hk, hFinv _ hδE, ← hg'] at h2
      rw [← hSconj i₀ k hk, ← h2]
      exact (map_inv τ g').symm
    have hgsupp := eq_mulSingle_of_dinv hp hp2 h12 (hinvS i₁ h01) (hinvS i₂ h02)
    set cc := (toAdd (g' i₀)).val with hcc
    have hFδ : F (τ δ) = τ δ ^ cc := by
      rw [← hg', ← map_pow]
      congr 1
      rw [hgsupp, hδ, ← Pi.mulSingle_pow]
      congr 1
      rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, hcc, ZMod.natCast_zmod_val, ofAdd_toAdd]
    refine ⟨cc, ?_⟩
    let E₁ : Subgroup Ω :=
      { carrier := {x | x ∈ E ∧ F x = x ^ cc}
        mul_mem' := fun {x y} hx hy => ⟨E.mul_mem hx.1 hy.1, by
          rw [hFmul x hx.1 y hy.1, hx.2, hy.2,
            (Commute.mul_pow (hcomm x hx.1 y hy.1 : Commute x y) cc)]⟩
        one_mem' := ⟨E.one_mem, by rw [hF1, one_pow]⟩
        inv_mem' := fun {x} hx => ⟨E.inv_mem hx.1, by rw [hFinv x hx.1, hx.2, inv_pow]⟩ }
    rcases hirrE E₁ (fun x hx => hx.1) (fun w hw x hx => ⟨hWE w hw x hx.1, by
        rw [hFW w hw x hx.1, hx.2, conj_pow]⟩) with hb | htop
    · exfalso
      have : τ δ ∈ E₁ := ⟨hδE, hFδ⟩
      rw [hb, Subgroup.mem_bot] at this
      exact hδ1 this
    · intro x hx
      have : x ∈ E₁ := htop ▸ hx
      exact this.2

end Torus

section Omega

variable {K : Type} [Field K]

open TableBOrth in
theorem ggTorusIrredSecElt_omegaPlusGroup [Finite K] [CharP K 2] {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) :
    GGTorusIrredSecElt p m (LargeEvenOmega (LargeEvenQPlus K m)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := @exists_orderOf_eq_of_dvd K _ _ p ⟨hp⟩ hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set P : Equiv.Perm (Fin m) →* GL (Fin m ⊕ Fin m) K :=
    (TauCeti.permutationGL (k := K)).comp ((Equiv.Perm.sumCongrHom (Fin m) (Fin m)).comp
      ((MonoidHom.id _).prod (MonoidHom.id _))) with hPdef
  have hPapp : ∀ σ, P σ = TauCeti.permutationGL (Equiv.Perm.sumCongr σ σ) := fun σ => rfl
  refine ggTorusIrredSecElt_of_torus hp hp2 hm (spTorusGL hζ) (spTorusGL_mem_omegaPlus hζ hodd)
    (fun i k => TauCeti.permutationGL (pairSwap i * pairSwap k))
    (fun i k => permutationGL_pairSwap_mul_mem_omegaPlus) (fun i k _ f => ?_) P
    (fun σ τ => ?_) (fun σ f => ?_) (fun E hE hr => ?_)
  · rw [spTorusGL_apply, spTorusGL_apply, pairSwap_mul_conj, map_dinv]
  · have h := Subgroup.commutator_mem_commutator (sumCongr_mem_orthPlus (K := K) σ)
      (sumCongr_mem_orthPlus (K := K) τ)
    rw [commutatorElement_def] at h
    rw [hPapp, hPapp]
    exact h
  · rw [hPapp, spTorusGL_apply, spTorusGL_apply, NbrSp.permutationGL_conj_diagGL]
    exact congrArg TauCeti.diagGL (NbrSp.pairedUnits_comp_pairPerm _ σ)
  · have hE₁O : E.map (LargeEvenOmega (LargeEvenQPlus K m)).subtype ≤
        LargeEvenOrthGroup (LargeEvenQPlus K m) :=
      (Subgroup.map_subtype_le _).trans (omega_le_orth _)
    have hE₁ := isElemAbelian_map hE (LargeEvenOmega (LargeEvenQPlus K m)).subtype
    have hcard : p ^ m ≤ Nat.card (E.map (LargeEvenOmega (LargeEvenQPlus K m)).subtype) := by
      rw [← Nat.card_congr (E.equivMapOfInjective _
        (LargeEvenOmega (LargeEvenQPlus K m)).subtype_injective).toEquiv]
      exact hr
    obtain ⟨g, hg, χ, hχ, hsurj⟩ := by
      have := Fact.mk hp
      exact exists_orth_conj_plus hp2 hζo hE₁O hE₁ hcard
    refine ⟨g, fun x hx => ?_, mem_iff_of_conj hζo hζ (MonoidHom.id _) hE (fun x => hχ x)
      hsurj⟩
    have h := map_conj_omega (inv_mem hg)
    rw [← h]
    exact ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩

open TableBOrth in
theorem ggTorusIrredSecElt_omegaMinusGroup [Finite K] [CharP K 2] {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGTorusIrredSecElt p m (LargeEvenOmega (LargeEvenQMinus m b c)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := @exists_orderOf_eq_of_dvd K _ _ p ⟨hp⟩ hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨P, hPapp⟩ : ∃ P : Equiv.Perm (Fin m) →* GL (Fin m ⊕ Fin m) K,
      ∀ σ, P σ = TauCeti.permutationGL (Equiv.Perm.sumCongr σ σ) :=
    ⟨(TauCeti.permutationGL (k := K)).comp ((Equiv.Perm.sumCongrHom (Fin m) (Fin m)).comp
      ((MonoidHom.id _).prod (MonoidHom.id _))), fun σ => rfl⟩
  refine ggTorusIrredSecElt_of_torus hp hp2 hm (blockInl.comp (spTorusGL hζ))
    (fun f => blockInl_mem_omegaMinus b c (spTorusGL_mem_omegaPlus hζ hodd f))
    (fun i k => blockInl (TauCeti.permutationGL (pairSwap i * pairSwap k)))
    (fun i k => blockInl_mem_omegaMinus b c permutationGL_pairSwap_mul_mem_omegaPlus)
    (fun i k _ f => ?_) (blockInl.comp P) (fun σ τ => ?_) (fun σ f => ?_) (fun E hE hr => ?_)
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul,
      spTorusGL_apply, spTorusGL_apply, pairSwap_mul_conj, map_dinv]
  · have h := Subgroup.commutator_mem_commutator (sumCongr_mem_orthPlus (K := K) σ)
      (sumCongr_mem_orthPlus (K := K) τ)
    rw [commutatorElement_def] at h
    have e : (blockInl.comp P) σ * (blockInl.comp P) τ * ((blockInl.comp P) σ)⁻¹ *
        ((blockInl.comp P) τ)⁻¹ = blockInl (P σ * P τ * (P σ)⁻¹ * (P τ)⁻¹) := by
      simp only [MonoidHom.comp_apply, map_mul, map_inv]
    rw [e, hPapp, hPapp]
    exact blockInl_mem_omegaMinus b c h
  · have e : (blockInl.comp P) σ * (blockInl.comp (spTorusGL hζ)) f * ((blockInl.comp P) σ)⁻¹ =
        blockInl (P σ * spTorusGL hζ f * (P σ)⁻¹) := by
      simp only [MonoidHom.comp_apply, map_mul, map_inv]
    rw [e, MonoidHom.comp_apply, hPapp, spTorusGL_apply, spTorusGL_apply,
      NbrSp.permutationGL_conj_diagGL]
    exact congrArg (fun d => blockInl (TauCeti.diagGL d)) (NbrSp.pairedUnits_comp_pairPerm _ σ)
  · have hE₁O : E.map (LargeEvenOmega (LargeEvenQMinus m b c)).subtype ≤
        LargeEvenOrthGroup (LargeEvenQMinus m b c) :=
      (Subgroup.map_subtype_le _).trans (omega_le_orth _)
    have hE₁ := isElemAbelian_map hE (LargeEvenOmega (LargeEvenQMinus m b c)).subtype
    have hcard : p ^ m ≤ Nat.card (E.map (LargeEvenOmega (LargeEvenQMinus m b c)).subtype) := by
      rw [← Nat.card_congr (E.equivMapOfInjective _
        (LargeEvenOmega (LargeEvenQMinus m b c)).subtype_injective).toEquiv]
      exact hr
    obtain ⟨g, hg, χ, hχ, hsurj⟩ := by
      have := Fact.mk hp
      exact exists_orth_conj_minus hp2 hζo hirr hE₁O hE₁ hcard
    refine ⟨g, fun x hx => ?_, mem_iff_of_conj hζo hζ blockInl hE hχ hsurj⟩
    have h := map_conj_omega (inv_mem hg)
    rw [← h]
    exact ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩

open TableBOrth in
theorem ggTorusIrred_omegaPlus [Finite K] [CharP K 2] {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) :
    GGTorusIrred p m (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _) :=
  ggTorusIrred_of_irredSecElt hp subset_rfl (center_omegaPlus_eq_bot hp hp2 hpq hm)
    (ggTorusIrredSecElt_of_mulEquiv
      (projMkEquiv (scalars_subgroupOf_omegaPlus_eq_bot (by omega))).symm
      (ggTorusIrredSecElt_omegaPlusGroup hp hp2 hpq hm))

open TableBOrth in
theorem ggTorusIrred_omegaMinus [Finite K] [CharP K 2] {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGTorusIrred p m (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
      (LargeEvenInnSet _) :=
  ggTorusIrred_of_irredSecElt hp subset_rfl (center_omegaMinus_eq_bot hp hp2 hpq hm hirr)
    (ggTorusIrredSecElt_of_mulEquiv (projMkEquiv (scalars_subgroupOf_omegaMinus_eq_bot b c)).symm
      (ggTorusIrredSecElt_omegaMinusGroup hp hp2 hpq hm hirr))

theorem recipeOmegaPlus_torusIrred {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hl : 3 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusIrred p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l, ggTorusLift_omegaPlus hp hp2 hpq hl,
    ggTorusIrred_omegaPlus hp hp2 hpq hl⟩

theorem recipeOmegaMinus_torusIrred {m n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hm : 3 ≤ m) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusIrred p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, m,
    ggTorusLift_omegaMinus hp hp2 hpq hm b c, ggTorusIrred_omegaMinus hp hp2 hpq hm hbc⟩

end Omega

end CorFourTwoMore

open CorFourTwoMore

theorem largeEvenLabelAll_torusIrred_orthSplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGCorFourTwoOrthSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusIrred p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hpn⟩ := h
  dsimp only at htag hl hpn ⊢
  have hp2 := ne_two_of_dvd_two_pow_sub_one' hlab.1 hpn
  intro Q hQ
  rcases htag with h | h <;> subst h <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
  · split_ifs at hQ ⊢ with h3
    · omega
    · exact recipeOmegaPlus_torusIrred hp hp2 hpn (by omega) hQ
  · split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · exact recipeOmegaMinus_torusIrred hp hp2 hpn (by omega) hQ

theorem ggTableBIrredInputOn_orthSplit : GGTableBIrredInputOn GGCorFourTwoOrthSplitLabel :=
  ggTableBIrredInputOn_of_labels fun _ _ hp hlab h =>
    largeEvenLabelAll_torusIrred_orthSplit hp hlab h

theorem ggBstarInnerDiagLInputOn_orthSplit_self :
    GGBstarInnerDiagLInputOn GGCorFourTwoOrthSplitLabel :=
  fun G _ _ p B Bs x L D J hC hL =>
    (ggBstarInnerDiagLInputOn_orthSplit (fun _ _ => True) G p B Bs x L D J hC
      (hL.mono fun _ _ h => ⟨trivial, h⟩)).mono fun _ _ h => h.2

theorem ggTableBCxInputOn_orthSplit : GGTableBCxInputOn GGCorFourTwoOrthSplitLabel :=
  ggTableBCxInputOn_of_irred ggBstarInnerDiagLInputOn_orthSplit_self ggTableBIrredInputOn_orthSplit

theorem ggTableBModuleInputOn_orthSplit : GGTableBModuleInputOn GGCorFourTwoOrthSplitLabel :=
  ggTableBModuleInputOn_of_irred ggBstarInnerDiagLInputOn_orthSplit_self
    ggTableBIrredInputOn_orthSplit

theorem ggTableBActionInputOn_orthSplit : GGTableBActionInputOn GGCorFourTwoOrthSplitLabel :=
  ggTableBActionInputOn_of_irred ggBstarInnerDiagLInputOn_orthSplit_self
    ggTableBIrredInputOn_orthSplit

end CFSG.StandardType

end
