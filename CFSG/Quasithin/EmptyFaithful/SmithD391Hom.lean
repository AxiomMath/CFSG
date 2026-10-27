module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.S153ZH

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391
open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]
  {Λ : Subgroup Γ}

@[expose] def IsEqv (Λ : Subgroup Γ) {V : Subgroup Q} (φ : ↥V →* Q) : Prop :=
  ∀ (l : ↥Λ) (v w : ↥V), (l : Γ) • (v : Q) = (w : Q) → φ w = (l : Γ) • φ v

section Endo

variable {V : Subgroup Q} (hirr : XMod.IsIrr ↥Λ V)
  (hAut : ∀ ψ : ↥V ≃* ↥V, ∃ l : ↥Λ, ∀ v : ↥V, (l : Γ) • (v : Q) = ((ψ v : ↥V) : Q))
  (hinj : ∀ l : ↥Λ, (∀ v ∈ V, (l : Γ) • v = v) → l = 1)
  (hZ : ∀ l : ↥Λ, (∀ l' : ↥Λ, l * l' = l' * l) → l = 1)

include hirr hAut hinj hZ in
theorem endo_eq_one_or_eq_id [Finite Q] (θ : ↥V →* ↥V) (hθ : IsEqv Λ (V.subtype.comp θ)) :
    θ = 1 ∨ θ = MonoidHom.id ↥V := by
  by_cases h1 : θ = 1
  · exact Or.inl h1
  right
  have hker : θ.ker = ⊥ := by
    set K : Subgroup Q := θ.ker.map V.subtype with hK
    have hKinv : XMod.IsInv ↥Λ K := by
      rintro l _ ⟨k, hk, rfl⟩
      have hw : (l : Γ) • (k : Q) ∈ V := hirr.1 l k k.2
      refine ⟨⟨_, hw⟩, ?_, rfl⟩
      have h2 := hθ l k ⟨_, hw⟩ rfl
      simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at h2
      show θ ⟨_, hw⟩ = 1
      apply Subtype.ext
      rw [h2, show θ k = 1 from hk]
      simp
    rcases hirr.2.2 K hKinv bot_le (Subgroup.map_subtype_le _) with h | h
    · refine (Subgroup.eq_bot_iff_forall _).2 fun k hk => ?_
      have : (k : Q) ∈ K := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · exfalso
      apply h1
      refine MonoidHom.ext fun v => ?_
      have : (v : Q) ∈ K := by rw [h]; exact v.2
      obtain ⟨v', hv', he⟩ := this
      rw [show v' = v from Subtype.ext he] at hv'
      exact hv'
  have hθinj : Function.Injective θ := (MonoidHom.ker_eq_bot_iff θ).1 hker
  have hθbij : Function.Bijective θ := by
    have : Finite ↥V := inferInstance
    exact ⟨hθinj, Finite.surjective_of_injective hθinj⟩
  let θe : ↥V ≃* ↥V := MulEquiv.ofBijective θ hθbij
  obtain ⟨l₀, hl₀⟩ := hAut θe
  have hθv : ∀ v : ↥V, ((θ v : ↥V) : Q) = (l₀ : Γ) • (v : Q) := fun v => (hl₀ v).symm
  have hagree : ∀ l' : ↥Λ, ∀ v ∈ V, ((l₀ * l' : ↥Λ) : Γ) • v = ((l' * l₀ : ↥Λ) : Γ) • v := by
    intro l' v hv
    have hw : (l' : Γ) • v ∈ V := hirr.1 l' v hv
    have h1 := hθ l' ⟨v, hv⟩ ⟨_, hw⟩ rfl
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at h1
    rw [hθv, hθv] at h1
    simp only [Subgroup.coe_mul, mul_smul]
    exact h1
  have hcen : ∀ l' : ↥Λ, l₀ * l' = l' * l₀ := by
    intro l'
    have hc : (l₀ * l') * (l' * l₀)⁻¹ = 1 := by
      apply hinj
      intro v hv
      set u : Q := (((l' * l₀)⁻¹ : ↥Λ) : Γ) • v with hu
      have hw : u ∈ V := hirr.1 _ v hv
      calc (((l₀ * l') * (l' * l₀)⁻¹ : ↥Λ) : Γ) • v = ((l₀ * l' : ↥Λ) : Γ) • u := by
            rw [hu, ← mul_smul]; rfl
        _ = ((l' * l₀ : ↥Λ) : Γ) • u := hagree l' u hw
        _ = v := by
            rw [hu, ← mul_smul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, one_smul]
    rw [mul_inv_eq_one] at hc
    exact hc
  have hl₁ : l₀ = 1 := hZ l₀ hcen
  refine MonoidHom.ext fun v => Subtype.ext ?_
  rw [MonoidHom.id_apply, hθv, hl₁]
  simp

include hirr hAut hinj hZ in
theorem eqv_eq_of_ne_one [Finite Q] {S : Subgroup Q} (e : ↥V ≃* ↥S)
    (he : IsEqv Λ (S.subtype.comp e.toMonoidHom)) {β β' : ↥V →* ↥S}
    (hβ : IsEqv Λ (S.subtype.comp β)) (hβ' : IsEqv Λ (S.subtype.comp β')) (h1 : β ≠ 1)
    (h1' : β' ≠ 1) : β = β' := by
  have he' : ∀ (l : ↥Λ) (s s' : ↥S), (l : Γ) • (s : Q) = (s' : Q) →
      ((e.symm s' : ↥V) : Q) = (l : Γ) • ((e.symm s : ↥V) : Q) := by
    intro l s s' hss'
    have hw : (l : Γ) • ((e.symm s : ↥V) : Q) ∈ V := hirr.1 l _ (e.symm s).2
    have h2 := he l (e.symm s) ⟨_, hw⟩ rfl
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h2
    have h3 : e ⟨_, hw⟩ = s' := Subtype.ext (h2.trans hss')
    rw [← h3, MulEquiv.symm_apply_apply]
  have key : ∀ γ : ↥V →* ↥S, IsEqv Λ (S.subtype.comp γ) → γ ≠ 1 → γ = e.toMonoidHom := by
    intro γ hγ hγ1
    have hc : IsEqv Λ (V.subtype.comp (e.symm.toMonoidHom.comp γ)) :=
      fun l v w hvw => he' l (γ v) (γ w) (hγ l v w hvw).symm
    rcases endo_eq_one_or_eq_id hirr hAut hinj hZ _ hc with h | h
    · exfalso
      apply hγ1
      refine MonoidHom.ext fun v => ?_
      have h2 := congrArg (fun θ : ↥V →* ↥V => e (θ v)) h
      simpa using h2
    · refine MonoidHom.ext fun v => ?_
      have h2 := congrArg (fun θ : ↥V →* ↥V => e (θ v)) h
      simpa using h2
  rw [key β hβ h1, key β' hβ' h1']

end Endo

section Split

variable {V S : Subgroup Q}

theorem exists_mulEquiv_prod (hVS : V ⊓ S = ⊥) :
    ∃ E : ↥V × ↥S ≃* ↥(V ⊔ S), ∀ p : ↥V × ↥S, (E p : Q) = (p.1 : Q) * (p.2 : Q) := by
  set μ : ↥V × ↥S →* Q := V.subtype.coprod S.subtype with hμ
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    have h1 : (a : Q) * (b : Q) = 1 := h
    have hb : (b : Q) = (a : Q)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have ha : (a : Q) ∈ V ⊓ S :=
      ⟨a.2, by rw [← inv_inv (a : Q), ← hb]; exact S.inv_mem b.2⟩
    rw [hVS, Subgroup.mem_bot] at ha
    have hb1 : (b : Q) = 1 := by rw [hb, ha, inv_one]
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb1)
  have hrange : μ.range = V ⊔ S := by
    ext q
    rw [MonoidHom.mem_range, Subgroup.mem_sup]
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨a, a.2, b, b.2, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  exact ⟨(MonoidHom.ofInjective hμinj).trans (MulEquiv.subgroupCongr hrange), fun p => rfl⟩

theorem isEqv_fst_snd (hV : XMod.IsInv ↥Λ V) (hS : XMod.IsInv ↥Λ S) (hVS : V ⊓ S = ⊥)
    {E : ↥V × ↥S ≃* ↥(V ⊔ S)} (hE : ∀ p : ↥V × ↥S, (E p : Q) = (p.1 : Q) * (p.2 : Q))
    {P : Subgroup Q} {φ : ↥P →* ↥(V ⊔ S)} (hφ : IsEqv Λ ((V ⊔ S).subtype.comp φ)) :
    IsEqv Λ (V.subtype.comp ((MonoidHom.fst ↥V ↥S).comp (E.symm.toMonoidHom.comp φ))) ∧
      IsEqv Λ (S.subtype.comp ((MonoidHom.snd ↥V ↥S).comp (E.symm.toMonoidHom.comp φ))) := by
  have hdec : ∀ u : ↥P, ((φ u : ↥(V ⊔ S)) : Q) =
      ((E.symm (φ u)).1 : Q) * ((E.symm (φ u)).2 : Q) := by
    intro u
    rw [← hE, MulEquiv.apply_symm_apply]
  have key : ∀ (l : ↥Λ) (u w : ↥P), (l : Γ) • (u : Q) = (w : Q) →
      ((E.symm (φ w)).1 : Q) = (l : Γ) • ((E.symm (φ u)).1 : Q) ∧
      ((E.symm (φ w)).2 : Q) = (l : Γ) • ((E.symm (φ u)).2 : Q) := by
    intro l u w huw
    have h1 := hφ l u w huw
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at h1
    rw [hdec, hdec, smul_mul'] at h1
    exact eq_of_mul_eq_of_disjoint hVS (E.symm (φ w)).1.2 (hV l _ (E.symm (φ u)).1.2)
      (E.symm (φ w)).2.2 (hS l _ (E.symm (φ u)).2.2) h1
  exact ⟨fun l u w huw => (key l u w huw).1, fun l u w huw => (key l u w huw).2⟩

end Split

section Prime

variable {V : Subgroup Q} (hirr : XMod.IsIrr ↥Λ V)
  (hAut : ∀ ψ : ↥V ≃* ↥V, ∃ l : ↥Λ, ∀ v : ↥V, (l : Γ) • (v : Q) = ((ψ v : ↥V) : Q))
  (hinj : ∀ l : ↥Λ, (∀ v ∈ V, (l : Γ) • v = v) → l = 1)
  (hZ : ∀ l : ↥Λ, (∀ l' : ↥Λ, l * l' = l' * l) → l = 1)

theorem smul_eq_of_pow_smul_eq {x : Γ} {p : ℕ} (hp : p.Prime) (hxp : x ^ p = 1) {d : ℕ}
    (hd0 : d ≠ 0) (hdp : d < p) {q : Q} (hq : x ^ d • q = q) : x • q = q := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.coprime_of_lt_prime hd0 hdp hp).symm hp.one_lt
  have hx : x = (x ^ d) ^ m := by
    rw [← pow_mul, pow_eq_pow_mod (d * m) hxp, hm, pow_one]
  have hpow : ∀ k : ℕ, (x ^ d) ^ k • q = q := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_smul]
    | succ k ih => rw [pow_succ, mul_smul, hq, ih]
  rw [hx]
  exact hpow m

include hirr hAut hinj hZ in
theorem smul_eqv_eq_of_prime [Finite Q] {S : Subgroup Q} (hS : XMod.IsInv ↥Λ S)
    (hVS : V ⊓ S = ⊥) (e : ↥V ≃* ↥S) (he : IsEqv Λ (S.subtype.comp e.toMonoidHom)) {x : Γ}
    (hxΛ : ∀ l ∈ Λ, x * l = l * x) (hxQ : ∀ q ∈ V ⊔ S, x • q ∈ V ⊔ S) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hxp : x ^ p = 1) (φ : ↥V →* Q) (hφ : IsEqv Λ φ) (hφQ : ∀ v, φ v ∈ V ⊔ S)
    (v : ↥V) : x • φ v = φ v := by
  classical
  obtain ⟨E, hE⟩ := exists_mulEquiv_prod hVS
  have hxQn : ∀ (i : ℕ), ∀ q ∈ V ⊔ S, x ^ i • q ∈ V ⊔ S := by
    intro i
    induction i with
    | zero => intro q hq; rwa [pow_zero, one_smul]
    | succ i ih => intro q hq; rw [pow_succ, mul_smul]; exact ih _ (hxQ q hq)
  have hxΛn : ∀ (i : ℕ) (l : ↥Λ) (q : Q), x ^ i • (l : Γ) • q = (l : Γ) • x ^ i • q := by
    intro i l q
    rw [smul_smul, smul_smul, ((Commute.pow_left (hxΛ l l.2) i)).eq]
  let f : ℕ → (↥V →* ↥(V ⊔ S)) := fun i =>
    ((MulDistribMulAction.toMonoidHom Q (x ^ i)).comp φ).codRestrict (V ⊔ S)
      (fun v => hxQn i _ (hφQ v))
  have hf : ∀ i, IsEqv Λ ((V ⊔ S).subtype.comp (f i)) := by
    intro i l u w huw
    show x ^ i • φ w = (l : Γ) • x ^ i • φ u
    rw [hφ l u w huw, hxΛn]
  let a : ℕ → (↥V →* ↥V) := fun i =>
    (MonoidHom.fst ↥V ↥S).comp (E.symm.toMonoidHom.comp (f i))
  let b : ℕ → (↥V →* ↥S) := fun i =>
    (MonoidHom.snd ↥V ↥S).comp (E.symm.toMonoidHom.comp (f i))
  have hab : ∀ i, IsEqv Λ (V.subtype.comp (a i)) ∧ IsEqv Λ (S.subtype.comp (b i)) :=
    fun i => isEqv_fst_snd hirr.1 hS hVS hE (hf i)
  have hid : MonoidHom.id ↥V ≠ 1 := by
    intro h
    apply hirr.2.1.ne'
    refine (Subgroup.eq_bot_iff_forall _).2 fun v hv => ?_
    have h2 := DFunLike.congr_fun h ⟨v, hv⟩
    exact congrArg Subtype.val h2
  have hendo : ∀ i j, (a i = 1 ↔ a j = 1) → a i = a j := by
    intro i j hij
    rcases endo_eq_one_or_eq_id hirr hAut hinj hZ _ (hab i).1 with h | h <;>
      rcases endo_eq_one_or_eq_id hirr hAut hinj hZ _ (hab j).1 with h' | h'
    · rw [h, h']
    · exact absurd (h' ▸ hij.1 h) hid
    · exact absurd (h ▸ hij.2 h') hid
    · rw [h, h']
  let g : Fin 5 → Bool × Bool := fun i => (decide (a i = 1), decide (b i = 1))
  obtain ⟨i, j, hij, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt g (by simp)
  have hg1 : (a i = 1 ↔ a j = 1) := by
    have h2 := congrArg Prod.fst hg
    simpa [g] using h2
  have hg2 : (b i = 1 ↔ b j = 1) := by
    have h2 := congrArg Prod.snd hg
    simpa [g] using h2
  have haij : a i = a j := hendo i j hg1
  have hbij : b i = b j := by
    by_cases hbi : b i = 1
    · rw [hbi, hg2.1 hbi]
    · exact eqv_eq_of_ne_one hirr hAut hinj hZ e he (hab i).2 (hab j).2 hbi
        (fun h => hbi (hg2.2 h))
  have hfij : ∀ u : ↥V, x ^ (i : ℕ) • φ u = x ^ (j : ℕ) • φ u := by
    intro u
    have h1 : E.symm (f i u) = E.symm (f j u) :=
      Prod.ext (DFunLike.congr_fun haij u) (DFunLike.congr_fun hbij u)
    have h2 := congrArg Subtype.val (E.symm.injective h1)
    exact h2
  have hcancel : ∀ (k l : ℕ), k < l → (∀ u : ↥V, x ^ k • φ u = x ^ l • φ u) →
      ∀ u : ↥V, x ^ (l - k) • φ u = φ u := by
    intro k l hkl h u
    have h2 := h u
    rw [show l = k + (l - k) by omega, pow_add, mul_smul] at h2
    exact (smul_left_cancel_iff (x ^ k)).1 h2.symm
  have hi5 := i.2
  have hj5 := j.2
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact smul_eq_of_pow_smul_eq hp hxp (by omega) (by omega)
      (hcancel (i : ℕ) (j : ℕ) hlt hfij v)
  · exact smul_eq_of_pow_smul_eq hp hxp (by omega) (by omega)
      (hcancel (j : ℕ) (i : ℕ) hlt (fun u => (hfij u).symm) v)

include hirr hAut hinj hZ in
theorem fix_of_prime_ge_five [Finite Q] {S : Subgroup Q} (hS : XMod.IsInv ↥Λ S)
    (hVS : V ⊓ S = ⊥) (hiso : XMod.Iso ↥Λ V S) {x : Γ} (hxΛ : ∀ l ∈ Λ, x * l = l * x)
    (hxQ : ∀ q ∈ V ⊔ S, x • q ∈ V ⊔ S) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hxp : x ^ p = 1) :
    ∀ q ∈ V ⊔ S, x • q = q := by
  obtain ⟨e, he⟩ := hiso
  have he' : IsEqv Λ (S.subtype.comp e.toMonoidHom) := fun l v w hvw => (he l v w hvw).symm
  have h1 := smul_eqv_eq_of_prime hirr hAut hinj hZ hS hVS e he' hxΛ hxQ hp hp5 hxp V.subtype
    (fun l v w hvw => hvw.symm) (fun v => Subgroup.mem_sup_left v.2)
  have h2 := smul_eqv_eq_of_prime hirr hAut hinj hZ hS hVS e he' hxΛ hxQ hp hp5 hxp
    (S.subtype.comp e.toMonoidHom) he' (fun v => Subgroup.mem_sup_right (e v).2)
  intro q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hq
  have hb' : x • b = b := by
    have h3 := h2 (e.symm ⟨b, hb⟩)
    simpa using h3
  have ha' : x • a = a := h1 ⟨a, ha⟩
  rw [smul_mul', ha', hb']

end Prime

section Twisted

variable {V : Subgroup Q} (hirr : XMod.IsIrr ↥Λ V)
  (hAut : ∀ ψ : ↥V ≃* ↥V, ∃ l : ↥Λ, ∀ v : ↥V, (l : Γ) • (v : Q) = ((ψ v : ↥V) : Q))
  (hinj : ∀ l : ↥Λ, (∀ v ∈ V, (l : Γ) • v = v) → l = 1)

include hirr hAut hinj in
theorem mem_of_iso_smul (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    (hC : ∀ c : Γ, (∀ l ∈ Λ, c * l = l * c) → c = 1) {g : Γ}
    (hg : XMod.Iso ↥Λ (g • V) V) : g ∈ Λ := by
  obtain ⟨φ, hφ⟩ := hg
  obtain ⟨l₀, hl₀⟩ := hAut ((XMod.smulEquiv g V).trans φ)
  have hl₀' : ∀ u : ↥V, (l₀ : Γ) • (u : Q) =
      ((φ ⟨g • (u : Q), Subgroup.smul_mem_pointwise_smul _ _ _ u.2⟩ : ↥V) : Q) := hl₀
  have hconj : ∀ l ∈ Λ, g * l * g⁻¹ = (l₀ : Γ) * l * (l₀ : Γ)⁻¹ := by
    intro l hl
    have hk : (g * l * g⁻¹)⁻¹ * ((l₀ : Γ) * l * (l₀ : Γ)⁻¹) ∈ Λ :=
      Λ.mul_mem (Λ.inv_mem (hΛ g l hl)) (Λ.mul_mem (Λ.mul_mem l₀.2 hl) (Λ.inv_mem l₀.2))
    have h1 := hinj ⟨_, hk⟩ ?_
    · have h2 := congrArg Subtype.val h1
      simp only [OneMemClass.coe_one] at h2
      rw [inv_mul_eq_one] at h2
      exact h2
    intro v hv
    obtain ⟨u, hu⟩ : ∃ u : Q, u = (l₀ : Γ)⁻¹ • v := ⟨_, rfl⟩
    have huV : u ∈ V := hu ▸ hirr.1 l₀⁻¹ v hv
    have hluV : (l : Γ) • u ∈ V := hirr.1 ⟨l, hl⟩ u huV
    have hv' : v = (l₀ : Γ) • u := by rw [hu, smul_inv_smul]
    have hgu : g • u ∈ g • V := Subgroup.smul_mem_pointwise_smul _ _ _ huV
    have hglu : g • (l : Γ) • u ∈ g • V := Subgroup.smul_mem_pointwise_smul _ _ _ hluV
    have h3 : (g * l * g⁻¹) • (g • u) = g • (l : Γ) • u := by
      rw [smul_smul, smul_smul, show g * l * g⁻¹ * g = g * l by group]
    have h4 := hφ ⟨g * l * g⁻¹, hΛ g l hl⟩ ⟨_, hgu⟩ ⟨_, hglu⟩ h3
    have h5 : (l₀ : Γ) • u = ((φ ⟨g • u, hgu⟩ : ↥V) : Q) := hl₀' ⟨u, huV⟩
    have h6 : (l₀ : Γ) • (l : Γ) • u = ((φ ⟨g • (l : Γ) • u, hglu⟩ : ↥V) : Q) :=
      hl₀' ⟨_, hluV⟩
    have h7 : ((l₀ : Γ) * l * (l₀ : Γ)⁻¹) • v = (g * l * g⁻¹) • v := by
      calc ((l₀ : Γ) * l * (l₀ : Γ)⁻¹) • v = (l₀ : Γ) • (l : Γ) • u := by
            rw [hv', smul_smul, smul_smul, inv_mul_cancel_right]
        _ = ((φ ⟨g • (l : Γ) • u, hglu⟩ : ↥V) : Q) := h6
        _ = (g * l * g⁻¹) • ((φ ⟨g • u, hgu⟩ : ↥V) : Q) := h4.symm
        _ = (g * l * g⁻¹) • v := by rw [← h5, ← hv']
    show ((g * l * g⁻¹)⁻¹ * ((l₀ : Γ) * l * (l₀ : Γ)⁻¹)) • v = v
    rw [mul_smul, h7, inv_smul_smul]
  have hc := hC ((l₀ : Γ)⁻¹ * g) fun l hl => by
    have h1 := hconj l hl
    calc (l₀ : Γ)⁻¹ * g * l = (l₀ : Γ)⁻¹ * (g * l * g⁻¹) * g := by group
      _ = (l₀ : Γ)⁻¹ * ((l₀ : Γ) * l * (l₀ : Γ)⁻¹) * g := by rw [h1]
      _ = l * ((l₀ : Γ)⁻¹ * g) := by group
  rw [inv_mul_eq_one] at hc
  rw [← hc]
  exact l₀.2

end Twisted


end CFSG.Quasithin.SmithD391
