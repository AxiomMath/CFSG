module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerSp
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB TableBSymp

namespace NbrOrth

section Coord

variable {p m : ℕ}

@[expose] def dinv (i k : Fin m) (f : Fin m → Multiplicative (ZMod p)) :
    Fin m → Multiplicative (ZMod p) :=
  Function.update (Function.update f k (f k)⁻¹) i ((Function.update f k (f k)⁻¹) i)⁻¹

theorem mul_inv_dinv {i k : Fin m} (hik : i ≠ k) (f : Fin m → Multiplicative (ZMod p)) :
    f * (dinv i k f)⁻¹ = Pi.mulSingle i (f i ^ 2) * Pi.mulSingle k (f k ^ 2) := by
  funext j
  simp only [dinv, Pi.mul_apply, Pi.inv_apply]
  by_cases hji : j = i
  · subst hji
    simp [Function.update_of_ne hik, Pi.mulSingle_eq_of_ne hik, sq]
  · by_cases hjk : j = k
    · subst hjk
      simp [Function.update_of_ne hji, Pi.mulSingle_eq_of_ne hji, sq]
    · simp [Function.update_of_ne hji, Function.update_of_ne hjk, Pi.mulSingle_eq_of_ne hji,
        Pi.mulSingle_eq_of_ne hjk]

theorem exists_pow_eq_of_ne_one (hp : p.Prime) {a : Multiplicative (ZMod p)} (ha : a ≠ 1)
    (b : Multiplicative (ZMod p)) : ∃ n : ℕ, a ^ n = b := by
  have := Fact.mk hp
  have ha' : Multiplicative.toAdd a ≠ 0 := by
    intro h
    apply ha
    rw [← ofAdd_toAdd a, h, ofAdd_zero]
  refine ⟨(Multiplicative.toAdd b / Multiplicative.toAdd a).val, ?_⟩
  rw [← ofAdd_toAdd a, ← ofAdd_nsmul, ← ofAdd_toAdd b]
  congr 1
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  exact div_mul_cancel₀ _ ha'

theorem eq_one_of_pow_eq_one (hp : p.Prime) {n : ℕ} (hn : ¬ p ∣ n)
    {a : Multiplicative (ZMod p)} (ha : a ^ n = 1) : a = 1 := by
  have := Fact.mk hp
  have h1 : (n : ZMod p) * Multiplicative.toAdd a = 0 := by
    rw [← nsmul_eq_mul, ← toAdd_pow, ha, toAdd_one]
  have hn' : (n : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have h2 : Multiplicative.toAdd a = 0 := (mul_eq_zero.mp h1).resolve_left hn'
  rw [← ofAdd_toAdd a, h2, ofAdd_zero]

theorem mulSingle_comp_inv (j : Fin m) (a : Multiplicative (ZMod p)) (σ : Equiv.Perm (Fin m)) :
    (Pi.mulSingle j a : Fin m → Multiplicative (ZMod p)) ∘ ⇑σ⁻¹ = Pi.mulSingle (σ j) a := by
  funext x
  simp only [Function.comp_apply]
  by_cases hx : x = σ j
  · subst hx
    simp
  · have : σ⁻¹ x ≠ j := fun h => hx (by rw [← h]; simp)
    rw [Pi.mulSingle_eq_of_ne this, Pi.mulSingle_eq_of_ne hx]

@[expose] def swapComm (j t u : Fin m) : Equiv.Perm (Fin m) :=
  Equiv.swap j t * Equiv.swap j u * (Equiv.swap j t)⁻¹ * (Equiv.swap j u)⁻¹

theorem swapComm_apply {j t u : Fin m} (hju : j ≠ u) (htu : t ≠ u) : swapComm j t u j = t := by
  rw [swapComm, Equiv.swap_inv, Equiv.swap_inv]
  simp only [Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hju) (Ne.symm htu),
    Equiv.swap_apply_right, Equiv.swap_apply_left]

theorem eq_bot_or_eq_top_of_dinv (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (F : Subgroup (Fin m → Multiplicative (ZMod p)))
    (hinv : ∀ i k, i ≠ k → ∀ f ∈ F, dinv i k f ∈ F)
    (hperm : ∀ j t u : Fin m, j ≠ t → j ≠ u → t ≠ u → ∀ f ∈ F, f ∘ ⇑(swapComm j t u)⁻¹ ∈ F) :
    F = ⊥ ∨ F = ⊤ := by
  classical
  by_cases hF : F = ⊥
  · exact Or.inl hF
  right
  have h2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have h4 : ¬ p ∣ 4 := fun h => h2 (by
    have := (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 2 by simpa using h)
    exact this.elim id id)
  obtain ⟨⟨f, hfF⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 1 := by
    by_contra h
    push Not at h
    exact hf1' (funext h)
  obtain ⟨k, hki, -⟩ := exists_ne_ne_of_three_le hm i i
  have hg₁ : Pi.mulSingle i (f i ^ 2) * Pi.mulSingle k (f k ^ 2) ∈ F := by
    rw [← mul_inv_dinv (Ne.symm hki)]
    exact F.mul_mem hfF (F.inv_mem (hinv i k (Ne.symm hki) f hfF))
  obtain ⟨j, b, hb1, hbF⟩ : ∃ j b, b ≠ 1 ∧ Pi.mulSingle j b ∈ F := by
    by_cases hk1 : f k = 1
    · refine ⟨i, f i ^ 2, fun h => hi (eq_one_of_pow_eq_one hp h2 h), ?_⟩
      rw [hk1, one_pow, Pi.mulSingle_one, mul_one] at hg₁
      exact hg₁
    · obtain ⟨l, hli, hlk⟩ := exists_ne_ne_of_three_le hm i k
      refine ⟨k, (f k ^ 2) ^ 2, fun h => hk1 (eq_one_of_pow_eq_one hp h4 ?_), ?_⟩
      · rw [← pow_mul] at h
        exact h
      · set g : Fin m → Multiplicative (ZMod p) :=
          Pi.mulSingle i (f i ^ 2) * Pi.mulSingle k (f k ^ 2) with hg
        have hgk : g k = f k ^ 2 := by
          rw [hg, Pi.mul_apply, Pi.mulSingle_eq_of_ne hki, Pi.mulSingle_eq_same, one_mul]
        have hgl : g l = 1 := by
          rw [hg, Pi.mul_apply, Pi.mulSingle_eq_of_ne hli, Pi.mulSingle_eq_of_ne hlk, one_mul]
        have h := F.mul_mem hg₁ (F.inv_mem (hinv k l (Ne.symm hlk) g hg₁))
        rw [mul_inv_dinv (Ne.symm hlk), hgk, hgl, one_pow, Pi.mulSingle_one, mul_one] at h
        exact h
  have hδ : ∀ t (a : Multiplicative (ZMod p)), Pi.mulSingle t a ∈ F := by
    intro t a
    obtain ⟨n, hn⟩ := exists_pow_eq_of_ne_one hp hb1 a
    have hja : Pi.mulSingle j a ∈ F := by
      rw [← hn, Pi.mulSingle_pow]
      exact F.pow_mem hbF n
    by_cases htj : t = j
    · subst htj
      exact hja
    · obtain ⟨u, huj, hut⟩ := exists_ne_ne_of_three_le hm j t
      have h := hperm j t u (Ne.symm htj) (Ne.symm huj) (Ne.symm hut) _ hja
      rwa [mulSingle_comp_inv, swapComm_apply (Ne.symm huj) (Ne.symm hut)] at h
  rw [eq_top_iff]
  intro g _
  rw [← Finset.univ_prod_mulSingle g]
  exact Subgroup.prod_mem _ fun t _ => hδ t (g t)


theorem dinv_mulSingle_self {i k : Fin m} (hik : i ≠ k) (a : Multiplicative (ZMod p)) :
    dinv i k (Pi.mulSingle i a) = (Pi.mulSingle i a : Fin m → Multiplicative (ZMod p))⁻¹ := by
  funext j
  simp only [dinv, Pi.inv_apply]
  by_cases hji : j = i
  · subst hji
    simp [Function.update_of_ne hik, Pi.mulSingle_eq_of_ne (Ne.symm hik)]
  · by_cases hjk : j = k
    · subst hjk
      simp [Function.update_of_ne hji, Pi.mulSingle_eq_of_ne hji]
    · simp [Function.update_of_ne hji, Function.update_of_ne hjk, Pi.mulSingle_eq_of_ne hji]

theorem dinv_mulSingle_of_ne {i k j : Fin m} (hji : j ≠ i) (hjk : j ≠ k)
    (a : Multiplicative (ZMod p)) :
    dinv i k (Pi.mulSingle j a) = (Pi.mulSingle j a : Fin m → Multiplicative (ZMod p)) := by
  have h1 : ∀ l, j ≠ l → Function.update (Pi.mulSingle j a : Fin m → Multiplicative (ZMod p)) l
      ((Pi.mulSingle j a : Fin m → Multiplicative (ZMod p)) l)⁻¹ = Pi.mulSingle j a :=
    fun l hjl => Function.update_eq_self_iff.mpr
      (by rw [Pi.mulSingle_eq_of_ne (Ne.symm hjl), inv_one])
  rw [dinv, h1 k hjk, h1 i hji]

end Coord

section Torus

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem ggTorusIrredElt_of_torus {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    {Ω : Subgroup (GL ι K)} (T : (Fin m → Multiplicative (ZMod p)) →* GL ι K)
    (hTΩ : ∀ f, T f ∈ Ω) (s : Fin m → Fin m → GL ι K) (hsΩ : ∀ i k, s i k ∈ Ω)
    (hs : ∀ i k, i ≠ k → ∀ f, s i k * T f * (s i k)⁻¹ = T (dinv i k f))
    (P : Equiv.Perm (Fin m) →* GL ι K)
    (hPΩ : ∀ σ τ : Equiv.Perm (Fin m), P σ * P τ * (P σ)⁻¹ * (P τ)⁻¹ ∈ Ω)
    (hP : ∀ σ f, P σ * T f * (P σ)⁻¹ = T (f ∘ ⇑σ⁻¹))
    (htor : ∀ E : Subgroup Ω, IsElemAbelian p E → p ^ m ≤ Nat.card E →
      ∃ g : GL ι K, (∀ x ∈ Ω, g⁻¹ * x * g ∈ Ω) ∧
        ∀ x : Ω, x ∈ E ↔ ∃ f, T f = g * x * g⁻¹) :
    GGTorusIrredElt p m Ω := by
  classical
  intro E hE hr _
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
  refine ⟨m, τ, W, hτE, fun i j => ?_, ?_, fun E' hE'E hE'inv => ?_⟩
  · obtain ⟨k, hki, hkj⟩ := exists_ne_ne_of_three_le hm i j
    refine ⟨S i k, ?_, fun hji => ?_⟩
    · rw [torusBasis, hSconj i k (Ne.symm hki), dinv_mulSingle_self (Ne.symm hki), map_inv]
    · rw [torusBasis, hSconj i k (Ne.symm hki), dinv_mulSingle_of_ne hji (Ne.symm hkj)]
  · rintro w hw e he
    obtain ⟨f, rfl⟩ := hτmem e he
    rw [← hτE]
    rcases hw with ⟨i, k, hik, rfl⟩ | ⟨j, t, u, -, -, -, rfl⟩
    · exact ⟨_, (hSconj i k hik f).symm⟩
    · exact ⟨_, (hCconj _ _ f).symm⟩
  · have hinvF : ∀ i k, i ≠ k → ∀ f ∈ E'.comap τ, dinv i k f ∈ E'.comap τ := by
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

end Torus

section Omega

variable {K : Type} [Field K]

theorem map_dinv {M : Type*} [Group M] {p m : ℕ} (φ : Multiplicative (ZMod p) →* M)
    (i k : Fin m) (f : Fin m → Multiplicative (ZMod p)) :
    (fun j => φ (dinv i k f j)) = Function.update (Function.update (fun j => φ (f j)) k
      (φ (f k))⁻¹) i ((Function.update (fun j => φ (f j)) k (φ (f k))⁻¹) i)⁻¹ := by
  funext j
  simp only [dinv, Function.update_apply]
  split_ifs <;> simp [map_inv]

theorem mem_iff_of_conj {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Subgroup (GL ι K)}
    {p m : ℕ} [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (B : GL (Fin m ⊕ Fin m) K →* GL ι K) {E : Subgroup Ω} (hE : IsElemAbelian p E)
    {g : GL ι K} {χ : Fin m → E.map Ω.subtype →* Kˣ}
    (hχ : ∀ x : E.map Ω.subtype,
      g * (x : GL ι K) * g⁻¹ = B (TauCeti.diagGL (pairedUnits fun k => χ k x)))
    (hsurj : ∀ u : Fin m → Kˣ, (∀ k, u k ^ p = 1) → ∃ x : E.map Ω.subtype, ∀ k, χ k x = u k)
    (x : Ω) : x ∈ E ↔ ∃ f, B (spTorusGL hζ f) = g * x * g⁻¹ := by
  have hprim : IsPrimitiveRoot ζ p := hζo ▸ IsPrimitiveRoot.orderOf ζ
  constructor
  · intro hx
    set x₁ : E.map Ω.subtype := ⟨x, x, hx, rfl⟩ with hx₁
    have hxp : x₁ ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      change (x : GL ι K) ^ p = 1
      rw [← Subgroup.coe_pow, hE.2 x hx, Subgroup.coe_one])
    have hk : ∀ k, ∃ n < p, ζ ^ n = χ k x₁ := fun k =>
      hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p _).mpr (by
        rw [← map_pow, hxp, map_one]))
    choose n _ hn using hk
    refine ⟨fun k => Multiplicative.ofAdd ((n k : ℕ) : ZMod p), ?_⟩
    rw [show g * (x : GL ι K) * g⁻¹ = g * (x₁ : GL ι K) * g⁻¹ from rfl, hχ x₁, spTorusGL_apply]
    congr 3
    funext k
    rw [zmodPowHom_natCast, hn]
  · rintro ⟨f, hf⟩
    obtain ⟨x', hx'⟩ := hsurj (fun k => zmodPowHom hζ (f k)) (fun k => by
      rw [← map_pow, show f k ^ p = 1 from congrFun (pow_card_eq_one_zmod f) k, map_one])
    have h1 : g * (x' : GL ι K) * g⁻¹ = g * x * g⁻¹ := by
      rw [hχ x', ← hf, spTorusGL_apply]
      congr 3
      funext k
      exact hx' k
    have h2 : (x' : GL ι K) = x := mul_left_cancel (mul_right_cancel h1)
    obtain ⟨_, e, he, rfl⟩ := x'
    have : e = x := Subtype.ext h2
    exact this ▸ he

open TableBOrth in
theorem ggTorusIrredElt_omegaPlusGroup [Finite K] [CharP K 2] {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) :
    GGTorusIrredElt p m (LargeEvenOmega (LargeEvenQPlus K m)) := by
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
  refine ggTorusIrredElt_of_torus hp hp2 hm (spTorusGL hζ) (spTorusGL_mem_omegaPlus hζ hodd)
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
theorem ggTorusIrredElt_omegaMinusGroup [Finite K] [CharP K 2] {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGTorusIrredElt p m (LargeEvenOmega (LargeEvenQMinus m b c)) := by
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
  refine ggTorusIrredElt_of_torus hp hp2 hm (blockInl.comp (spTorusGL hζ))
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
theorem ggTorusNbr_omegaPlus [Finite K] [CharP K 2] {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) :
    GGTorusNbr p m (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _) :=
  ggTorusNbr_of_irredElt hp hp2 subset_rfl (center_omegaPlus_eq_bot hp hp2 hpq hm)
    (ggTorusIrredElt_of_mulEquiv
      (projMkEquiv (scalars_subgroupOf_omegaPlus_eq_bot (by omega))).symm
      (ggTorusIrredElt_omegaPlusGroup hp hp2 hpq hm))

open TableBOrth in
theorem ggTorusNbr_omegaMinus [Finite K] [CharP K 2] {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGTorusNbr p m (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
      (LargeEvenInnSet _) :=
  ggTorusNbr_of_irredElt hp hp2 subset_rfl (center_omegaMinus_eq_bot hp hp2 hpq hm hirr)
    (ggTorusIrredElt_of_mulEquiv (projMkEquiv (scalars_subgroupOf_omegaMinus_eq_bot b c)).symm
      (ggTorusIrredElt_omegaMinusGroup hp hp2 hpq hm hirr))

theorem recipeOmegaPlus_torusNbr {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hl : 3 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusNbr p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l, ggTorusLift_omegaPlus hp hp2 hpq hl,
    ggTorusNbr_omegaPlus hp hp2 hpq hl⟩

theorem recipeOmegaMinus_torusNbr {m n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hm : 3 ≤ m) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusNbr p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, m,
    ggTorusLift_omegaMinus hp hp2 hpq hm b c, ggTorusNbr_omegaMinus hp hp2 hpq hm hbc⟩

theorem largeEvenLabelAll_torusNbr_orthogonal {lab : LargeEvenLabel}
    (htag : lab.tag = .D ∨ lab.tag = .twD) (hlab : LargeEvenInLambda2 lab) (hl : 4 ≤ lab.rank)
    {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpn ⊢
  have hp2 := ne_two_of_dvd_two_pow_sub_one' hlab.1 hpn
  intro Q hQ
  rcases htag with h | h <;> subst h <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
  · split_ifs at hQ ⊢ with h3
    · omega
    · exact recipeOmegaPlus_torusNbr hp hp2 hpn (by omega) hQ
  · split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · exact recipeOmegaMinus_torusNbr hp hp2 hpn (by omega) hQ

end Omega

end NbrOrth

open NbrOrth

theorem ggTableBNbrInnerInputOn_orthogonal :
    GGTableBNbrInnerInputOn fun p lab =>
      (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1 :=
  ggTableBNbrInnerInputOn_of_labels fun _ _ hp hlab h =>
    largeEvenLabelAll_torusNbr_orthogonal h.1 hlab h.2.1 hp h.2.2

theorem ggTableBNbrInnerInput_of_rest_orthogonal
    (h : GGTableBNbrInnerInputOn fun p lab => GGCorFourTwoRestLabel p lab ∧
      ¬ ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1) ∧
      ¬ ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1)) :
    GGTableBNbrInnerInput :=
  (((ggTableBNbrInnerInputOn_typeA.or ggTableBNbrInnerInputOn_symplectic).or
      ggTableBNbrInnerInputOn_orthogonal).or h).of_cover
    fun p lab _ _ => by
      by_cases h1 : GGTypeALabel p lab
      · exact Or.inl (Or.inl (Or.inl h1))
      · by_cases h2 : (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1
        · exact Or.inl (Or.inl (Or.inr h2))
        · by_cases h3 : (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1
          · exact Or.inl (Or.inr h3)
          · exact Or.inr ⟨h1, h2, h3⟩

end CFSG.StandardType

end
