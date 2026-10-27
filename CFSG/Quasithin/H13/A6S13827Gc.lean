module

public import CFSG.Quasithin.H13.A6S13827Gb
public import CFSG.Quasithin.Background.F918J3

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.B42U33
open scoped Pointwise IsMulCommutative

namespace A6G2

theorem b42TypeU33_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : B42TypeU33 X) : B42TypeU33 Y := by
  obtain ⟨hZ, hP⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← Subgroup.map_center_eq e, hZ, Subgroup.map_bot]
  · exact IsPSU.of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hP

theorem exists_equiv_Q
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (h64 : Nat.card V = 2 ^ 6)
    {L : Subgroup (MulAut V)} (hP : B42TypeU33 ↥L) :
    ∃ e : V ≃* ModQ, L.map (MulAut.congr e).toMonoidHom =
      (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) :=
  exists_equiv_of_g2NaturalDerived (u33SixNatural V hV h64 L hP)

variable {Λ : Type} [Group Λ] {V₁ V₂ : Type} [CommGroup V₁] [Finite V₁] [CommGroup V₂]
  [Finite V₂]

theorem exists_equivariant
    (hV₁ : ∀ v : V₁, v ^ 2 = 1) (hV₂ : ∀ v : V₂, v ^ 2 = 1) (h₁ : Nat.card V₁ = 2 ^ 6)
    (h₂ : Nat.card V₂ = 2 ^ 6) {ρ₁ : Λ →* MulAut V₁} {ρ₂ : Λ →* MulAut V₂}
    (hρ₁ : Function.Injective ρ₁) (hρ₂ : Function.Injective ρ₂) (hP₁ : B42TypeU33 ↥ρ₁.range)
    (hP₂ : B42TypeU33 ↥ρ₂.range) :
    ∃ φ : V₁ ≃* V₂, ∀ x v, φ (ρ₁ x v) = ρ₂ x (φ v) := by
  obtain ⟨e₁, he₁⟩ := exists_equiv_Q hV₁ h₁ hP₁
  obtain ⟨e₂, he₂⟩ := exists_equiv_Q hV₂ h₂ hP₂
  set D₀ := (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) with hD₀
  set σ₁ : Λ →* MulAut ModQ := (MulAut.congr e₁).toMonoidHom.comp ρ₁ with hσ₁
  set σ₂ : Λ →* MulAut ModQ := (MulAut.congr e₂).toMonoidHom.comp ρ₂ with hσ₂
  have hr₁ : σ₁.range = D₀ := by rw [hσ₁, MonoidHom.range_comp, he₁]
  have hr₂ : σ₂.range = D₀ := by rw [hσ₂, MonoidHom.range_comp, he₂]
  have hi₁ : Function.Injective σ₁ := (MulAut.congr e₁).injective.comp hρ₁
  have hi₂ : Function.Injective σ₂ := (MulAut.congr e₂).injective.comp hρ₂
  let θ : ↥(g2Derived (ZMod 2)) ≃* ↥D₀ :=
    (g2Derived (ZMod 2)).equivMapOfInjective (g2QAct (ZMod 2)) g2QAct_injective
  let s₁ : Λ ≃* ↥D₀ := (MonoidHom.ofInjective hi₁).trans (MulEquiv.subgroupCongr hr₁)
  let s₂ : Λ ≃* ↥D₀ := (MonoidHom.ofInjective hi₂).trans (MulEquiv.subgroupCongr hr₂)
  have hs₁ : ∀ x, ((s₁ x : ↥D₀) : MulAut ModQ) = σ₁ x := fun _ => rfl
  have hs₂ : ∀ x, ((s₂ x : ↥D₀) : MulAut ModQ) = σ₂ x := fun _ => rfl
  have hθ : ∀ d, ((θ d : ↥D₀) : MulAut ModQ) = g2QAct (ZMod 2) (d : ↥(quasithinG2 (ZMod 2))) :=
    fun _ => rfl
  let τ : MulAut ↥(g2Derived (ZMod 2)) := ((θ.trans s₁.symm).trans s₂).trans θ.symm
  obtain ⟨g, hg⟩ := conjNormal_bijective.2 τ
  have key : ∀ x, σ₂ x = g2QAct (ZMod 2) g * σ₁ x * (g2QAct (ZMod 2) g)⁻¹ := by
    intro x
    set d := θ.symm (s₁ x) with hd
    have h1 : g2QAct (ZMod 2) (d : ↥(quasithinG2 (ZMod 2))) = σ₁ x := by
      rw [← hθ, hd, MulEquiv.apply_symm_apply, hs₁]
    have h2 : τ d = θ.symm (s₂ x) := by
      show θ.symm (s₂ (s₁.symm (θ d))) = θ.symm (s₂ x)
      rw [hd, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
    have h3 : ((τ d : ↥(g2Derived (ZMod 2))) : ↥(quasithinG2 (ZMod 2))) =
        g * (d : ↥(quasithinG2 (ZMod 2))) * g⁻¹ := by
      rw [← hg, MulAut.conjNormal_apply]
    have h4 : g2QAct (ZMod 2) ((τ d : ↥(g2Derived (ZMod 2))) : ↥(quasithinG2 (ZMod 2))) =
        σ₂ x := by
      rw [← hθ, h2, MulEquiv.apply_symm_apply, hs₂]
    rw [← h4, h3, map_mul, map_mul, map_inv, h1]
  set γ := g2QAct (ZMod 2) g with hγ
  refine ⟨(e₁.trans γ).trans e₂.symm, fun x v => ?_⟩
  have hk := congrArg (fun f : MulAut ModQ => f (γ (e₁ v))) (key x)
  simp only [MulAut.mul_apply, MulAut.inv_apply_self] at hk
  apply e₂.injective
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hσ₁v : σ₁ x (e₁ v) = e₁ (ρ₁ x v) := by
    simp [hσ₁, MulAut.congr_apply]
  have hσ₂v : ∀ w, σ₂ x w = e₂ (ρ₂ x (e₂.symm w)) := fun w => by
    simp [hσ₂, MulAut.congr_apply]
  rw [← hσ₁v, ← hk, hσ₂v]

omit [Finite V₂] in
theorem equivariant_unique
    (hV₁ : ∀ v : V₁, v ^ 2 = 1) (h₁ : Nat.card V₁ = 2 ^ 6) {ρ₁ : Λ →* MulAut V₁}
    {ρ₂ : Λ →* MulAut V₂} (hP₁ : B42TypeU33 ↥ρ₁.range) {φ φ' : V₁ ≃* V₂}
    (hφ : ∀ x v, φ (ρ₁ x v) = ρ₂ x (φ v)) (hφ' : ∀ x v, φ' (ρ₁ x v) = ρ₂ x (φ' v)) :
    φ = φ' := by
  obtain ⟨e₁, he₁⟩ := exists_equiv_Q hV₁ h₁ hP₁
  set μ : MulAut V₁ := φ.trans φ'.symm with hμ
  have hμc : ∀ x, μ * ρ₁ x = ρ₁ x * μ := by
    intro x
    refine MulEquiv.ext fun v => ?_
    simp only [MulAut.mul_apply, hμ, MulEquiv.trans_apply]
    rw [hφ, MulEquiv.symm_apply_eq, hφ', MulEquiv.apply_symm_apply]
  have h1 : MulAut.congr e₁ μ = 1 := by
    apply schur_Q
    rintro _ hh
    rw [← he₁] at hh
    obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hh
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hμc]
  have h2 : μ = 1 := (MulAut.congr e₁).injective (by rw [h1, map_one])
  refine MulEquiv.ext fun v => ?_
  have h3 := congrArg (fun f : MulAut V₁ => f v) h2
  simp only [hμ, MulEquiv.trans_apply, MulAut.one_apply] at h3
  calc φ v = φ' (φ'.symm (φ v)) := (MulEquiv.apply_symm_apply _ _).symm
    _ = φ' v := by rw [h3]


section Inv

variable {E : Type} [CommGroup E] [Finite E] {LE : Subgroup (MulAut E)}

theorem isSimpleGroup_of_b42 {Y : Type} [Group Y] (hP : B42TypeU33 Y) : IsSimpleGroup Y := by
  obtain ⟨hZ, hPSU⟩ := hP
  have h1 : IsSimpleGroup (Y ⧸ Subgroup.center Y) :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hPSU).2
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

omit [Finite E] in
theorem le_stabSub_of_inv {M : Subgroup E} (hM : ∀ l ∈ LE, ∀ v ∈ M, l v ∈ M) :
    LE ≤ stabSub M := by
  intro l hl u
  refine ⟨fun h => ?_, fun h => hM l hl u h⟩
  have := hM l⁻¹ (LE.inv_mem hl) _ h
  simpa using this

omit [Finite E] in
theorem faithful_of_inv (hP : B42TypeU33 ↥LE) (hfix : fixV LE = ⊥) {M : Subgroup E}
    (hM : ∀ l ∈ LE, ∀ v ∈ M, l v ∈ M) (hMb : M ≠ ⊥) : LE ⊓ centSub M = ⊥ := by
  have hsimpL := isSimpleGroup_of_b42 hP
  have hn : ((LE ⊓ centSub M).subgroupOf LE).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨LE.mul_mem (LE.mul_mem g.2 hn.1) (LE.inv_mem g.2), fun u hu => ?_⟩
    show (g : MulAut E) ((n : MulAut E) ((g : MulAut E)⁻¹ u)) = u
    have hgu : (g : MulAut E)⁻¹ u ∈ M := hM _ (LE.inv_mem g.2) u hu
    rw [hn.2 _ hgu]
    simp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((LE ⊓ centSub M).subgroupOf LE) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : ↥LE) ∈ (LE ⊓ centSub M).subgroupOf LE := Subgroup.mem_subgroupOf.2 hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · exfalso
    apply hMb
    rw [eq_bot_iff, ← hfix]
    intro u hu l hl
    have : (⟨l, hl⟩ : ↥LE) ∈ (LE ⊓ centSub M).subgroupOf LE := by rw [h]; trivial
    exact (Subgroup.mem_subgroupOf.1 this).2 u hu

omit [Finite E] in
theorem b42_resHomOn (hP : B42TypeU33 ↥LE) (hfix : fixV LE = ⊥) {M : Subgroup E}
    (hM : ∀ l ∈ LE, ∀ v ∈ M, l v ∈ M) (hMb : M ≠ ⊥) :
    B42TypeU33 ↥(resHomOn M (le_stabSub_of_inv hM)).range := by
  rw [← autSub_eq_range_resHomOn]
  exact b42TypeU33_of_mulEquiv
    (autSubEquivOfFaithful (le_stabSub_of_inv hM) (faithful_of_inv hP hfix hM hMb)) hP

theorem six_le_card_of_inv (hV : ∀ v : E, v ^ 2 = 1) (hP : B42TypeU33 ↥LE) (hfix : fixV LE = ⊥)
    {M : Subgroup E} (hM : ∀ l ∈ LE, ∀ v ∈ M, l v ∈ M) (hMb : M ≠ ⊥) :
    2 ^ 6 ≤ Nat.card ↥M := by
  have e := autSubEquivOfFaithful (le_stabSub_of_inv hM) (faithful_of_inv hP hfix hM hMb)
  have hc : Nat.card ↥(autSub LE M) = 6048 := by
    rw [← Nat.card_congr e.toEquiv, card_of_b42TypeU33 hP]
  have hVM : ∀ v : ↥M, v ^ 2 = 1 := fun v => Subtype.ext (by simp [hV])
  obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥M = 2 ^ k :=
    (IsPGroup.iff_card).1 (isPGroup_two_of_sq_eq_one hVM)
  have := six_le_of_card_dvd hVM hk (autSub LE M) hc
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) this

theorem classify_six
    (hV : ∀ v : E, v ^ 2 = 1) (hP : B42TypeU33 ↥LE) (hfix : fixV LE = ⊥) {M N : Subgroup E}
    (hMinv : ∀ l ∈ LE, ∀ v ∈ M, l v ∈ M) (hNinv : ∀ l ∈ LE, ∀ v ∈ N, l v ∈ N)
    (hMN : M ⊓ N = ⊥) (hM64 : Nat.card ↥M = 2 ^ 6) (hN64 : Nat.card ↥N = 2 ^ 6)
    (hE : Nat.card E = 2 ^ 12) :
    ∃ D : Subgroup E, (∀ l ∈ LE, ∀ v ∈ D, l v ∈ D) ∧ Nat.card ↥D = 2 ^ 6 ∧ D ⊓ M = ⊥ ∧
      D ⊓ N = ⊥ ∧ ∀ M' : Subgroup E, (∀ l ∈ LE, ∀ v ∈ M', l v ∈ M') →
        Nat.card ↥M' = 2 ^ 6 → M' = M ∨ M' = N ∨ M' = D := by
  classical
  have hMb : M ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hM64; norm_num at hM64
  have hNb : N ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hN64; norm_num at hN64
  have hVsub : ∀ M' : Subgroup E, ∀ v : ↥M', v ^ 2 = 1 := fun M' v =>
    Subtype.ext (by simp [hV])
  let Φ : ↥M × ↥N →* E := M.subtype.coprod N.subtype
  have hΦ : ∀ m n, Φ (m, n) = (m : E) * (n : E) := fun _ _ => rfl
  have hΦi : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨m, n⟩ h1
    rw [hΦ] at h1
    have hmN : (m : E) = (n : E)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hm : (m : E) ∈ M ⊓ N := ⟨m.2, by rw [hmN]; exact N.inv_mem n.2⟩
    rw [hMN, Subgroup.mem_bot] at hm
    have hn : (n : E) = 1 := by rw [hm, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext hm) (Subtype.ext hn)
  have hΦb : Function.Bijective Φ :=
    hΦi.bijective_of_nat_card_le (by rw [Nat.card_prod, hM64, hN64, hE]; norm_num)
  let ΦE : ↥M × ↥N ≃* E := MulEquiv.ofBijective Φ hΦb
  set ρM := resHomOn M (le_stabSub_of_inv hMinv) with hρM
  set ρN := resHomOn N (le_stabSub_of_inv hNinv) with hρN
  have hρMi : Function.Injective ρM :=
    resHomOn_injective_of_faithful _ (faithful_of_inv hP hfix hMinv hMb)
  have hρNi : Function.Injective ρN :=
    resHomOn_injective_of_faithful _ (faithful_of_inv hP hfix hNinv hNb)
  have hρMv : ∀ (x : ↥LE) (m : ↥M), ((ρM x m : ↥M) : E) = (x : MulAut E) m := fun _ _ => rfl
  have hρNv : ∀ (x : ↥LE) (n : ↥N), ((ρN x n : ↥N) : E) = (x : MulAut E) n := fun _ _ => rfl
  obtain ⟨φ, hφ⟩ := exists_equivariant (hVsub M) (hVsub N) hM64 hN64 hρMi hρNi
    (b42_resHomOn hP hfix hMinv hMb) (b42_resHomOn hP hfix hNinv hNb)
  let f : ↥M →* E := M.subtype * (N.subtype.comp φ.toMonoidHom)
  have hf : ∀ m, f m = (m : E) * (φ m : E) := fun _ => rfl
  have hDinv : ∀ l ∈ LE, ∀ v ∈ f.range, l v ∈ f.range := by
    rintro l hl _ ⟨m, rfl⟩
    refine ⟨ρM ⟨l, hl⟩ m, ?_⟩
    rw [hf, hf, map_mul, hφ, hρMv, hρNv]
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro m h1
    rw [hf] at h1
    have hmN : (m : E) ∈ M ⊓ N := ⟨m.2, by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact N.inv_mem (φ m).2⟩
    rw [hMN, Subgroup.mem_bot] at hmN
    exact Subtype.ext hmN
  have hcardD : Nat.card ↥f.range = 2 ^ 6 := by
    rw [← hM64]
    exact Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv.symm
  have hDM : f.range ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨m, rfl⟩, hdM⟩
    rw [hf] at hdM
    have h1 : (φ m : E) ∈ M ⊓ N := ⟨by
      have := M.mul_mem (M.inv_mem m.2) hdM
      simpa using this, (φ m).2⟩
    rw [hMN, Subgroup.mem_bot] at h1
    have h2 : φ m = 1 := Subtype.ext h1
    have h3 : m = 1 := φ.injective (by rw [h2, map_one])
    rw [Subgroup.mem_bot, hf, h3]
    simp
  have hDN : f.range ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨m, rfl⟩, hdN⟩
    rw [hf] at hdN
    have h1 : (m : E) ∈ M ⊓ N := ⟨m.2, by
      have := N.mul_mem hdN (N.inv_mem (φ m).2)
      simpa using this⟩
    rw [hMN, Subgroup.mem_bot] at h1
    have h3 : m = 1 := Subtype.ext h1
    rw [Subgroup.mem_bot, hf, h3]
    simp
  refine ⟨f.range, hDinv, hcardD, hDM, hDN, fun M' hM' hc => ?_⟩
  have hinvM : ∀ l ∈ LE, ∀ v ∈ M' ⊓ M, l v ∈ M' ⊓ M := fun l hl v hv =>
    ⟨hM' l hl v hv.1, hMinv l hl v hv.2⟩
  have hinvN : ∀ l ∈ LE, ∀ v ∈ M' ⊓ N, l v ∈ M' ⊓ N := fun l hl v hv =>
    ⟨hM' l hl v hv.1, hNinv l hl v hv.2⟩
  by_cases h1 : M' ⊓ M = ⊥
  swap
  · left
    have h2 := six_le_card_of_inv hV hP hfix hinvM h1
    have h3 : M' ⊓ M = M := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hM64]; exact h2)
    exact (Subgroup.eq_of_le_of_card_ge (h3 ▸ inf_le_left : M ≤ M') (by rw [hc, hM64])).symm
  by_cases h2 : M' ⊓ N = ⊥
  swap
  · right; left
    have h3 := six_le_card_of_inv hV hP hfix hinvN h2
    have h4 : M' ⊓ N = N := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hN64]; exact h3)
    exact (Subgroup.eq_of_le_of_card_ge (h4 ▸ inf_le_left : N ≤ M') (by rw [hc, hN64])).symm
  right; right
  let p₁ : ↥M' →* ↥M := (MonoidHom.fst _ _).comp (ΦE.symm.toMonoidHom.comp M'.subtype)
  let p₂ : ↥M' →* ↥N := (MonoidHom.snd _ _).comp (ΦE.symm.toMonoidHom.comp M'.subtype)
  have hp : ∀ x : ↥M', ((p₁ x : ↥M) : E) * ((p₂ x : ↥N) : E) = x := by
    intro x
    rw [← hΦ]
    exact ΦE.apply_symm_apply (x : E)
  have hp₁i : Function.Injective p₁ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h3 := hp x
    rw [hx, OneMemClass.coe_one, one_mul] at h3
    have h4 : (x : E) ∈ M' ⊓ N := ⟨x.2, h3 ▸ (p₂ x).2⟩
    rw [h2, Subgroup.mem_bot] at h4
    exact Subtype.ext h4
  have hp₁b : Function.Bijective p₁ := hp₁i.bijective_of_nat_card_le (by rw [hc, hM64])
  let q₁ : ↥M' ≃* ↥M := MulEquiv.ofBijective p₁ hp₁b
  let μ : ↥M →* ↥N := p₂.comp q₁.symm.toMonoidHom
  have hμi : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h3 := hp (q₁.symm m)
    have hq : p₁ (q₁.symm m) = m := q₁.apply_symm_apply m
    have h4 : ((p₂ (q₁.symm m) : ↥N) : E) = 1 := by
      have : p₂ (q₁.symm m) = 1 := hm
      rw [this, OneMemClass.coe_one]
    rw [hq, h4, mul_one] at h3
    have h5 : ((q₁.symm m : ↥M') : E) ∈ M' ⊓ M := ⟨(q₁.symm m).2, h3 ▸ m.2⟩
    rw [h1, Subgroup.mem_bot] at h5
    have h6 : q₁.symm m = 1 := Subtype.ext h5
    rw [← hq, h6, map_one]
  have hμb : Function.Bijective μ := hμi.bijective_of_nat_card_le (by rw [hM64, hN64])
  let μ' : ↥M ≃* ↥N := MulEquiv.ofBijective μ hμb
  have hμe : ∀ (x : ↥LE) (m : ↥M), μ' (ρM x m) = ρN x (μ' m) := by
    intro x m
    set y := q₁.symm m with hy
    have hym : p₁ y = m := q₁.apply_symm_apply m
    have hxy : (x : MulAut E) y ∈ M' := hM' x x.2 y y.2
    set y' : ↥M' := ⟨(x : MulAut E) y, hxy⟩ with hy'
    have hsplit : ΦE.symm (y' : E) = (ρM x m, ρN x (p₂ y)) := by
      apply ΦE.injective
      rw [MulEquiv.apply_symm_apply]
      show (x : MulAut E) y = ((ρM x m : ↥M) : E) * ((ρN x (p₂ y) : ↥N) : E)
      rw [hρMv, hρNv, ← map_mul, ← hym, hp]
    have hp₁y' : p₁ y' = ρM x m := congrArg Prod.fst hsplit
    have hp₂y' : p₂ y' = ρN x (p₂ y) := congrArg Prod.snd hsplit
    have hq' : q₁.symm (ρM x m) = y' := by
      apply q₁.injective
      rw [MulEquiv.apply_symm_apply]
      exact hp₁y'.symm
    show p₂ (q₁.symm (ρM x m)) = ρN x (p₂ (q₁.symm m))
    rw [hq', hp₂y']
  have hμφ : μ' = φ :=
    equivariant_unique (hVsub M) hM64 (b42_resHomOn hP hfix hMinv hMb) hμe hφ
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hc, hcardD])
  intro x hx
  refine ⟨p₁ ⟨x, hx⟩, ?_⟩
  have h3 : φ (p₁ ⟨x, hx⟩) = p₂ ⟨x, hx⟩ := by
    rw [← hμφ]
    show p₂ (q₁.symm (p₁ ⟨x, hx⟩)) = p₂ ⟨x, hx⟩
    rw [show q₁.symm (p₁ ⟨x, hx⟩) = ⟨x, hx⟩ from q₁.symm_apply_apply _]
  rw [hf, h3]
  exact hp ⟨x, hx⟩

end Inv

end A6G2

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace SecHyp

variable {H K X W : Subgroup G} (hs : S.SecHyp H K X W) [IsMulCommutative ↥X]
include hs

theorem isIrr_autSec_K
    (hU : IsPSU 3 3 1 ↥(S.KSt H K))
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    (hcard : W.relIndex X ≤ 2 ^ 12) (J : Subgroup (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)))
    (hJ : ∀ l ∈ autSec (autOn K X) ⊤ (W.subgroupOf X), ∀ v ∈ J, l v ∈ J) :
    J = ⊥ ∨ J = ⊤ := by
  classical
  set E := Sec (⊤ : Subgroup ↥X) (W.subgroupOf X) with hE
  set LE := autSec (autOn K X) ⊤ (W.subgroupOf X) with hLE
  have hV : ∀ v : E, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hs.sec_sq v
  have hfix : fixV LE = ⊥ := hs.fixV_eq_bot hirr
  have hP : B42TypeU33 ↥LE := hs.b42TypeU33 hU
  have hcardE : Nat.card E ≤ 2 ^ 12 := by rw [card_sec]; exact hcard
  by_contra hJne
  push Not at hJne
  obtain ⟨hJb, hJt⟩ := hJne
  obtain ⟨M, ⟨hMb, hMJ, hMinv⟩, hMmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup E))
    {M : Subgroup E | M ≠ ⊥ ∧ M ≤ J ∧ ∀ l ∈ LE, ∀ v ∈ M, l v ∈ M} ⟨J, hJb, le_rfl, hJ⟩
  have hMt : M ≠ ⊤ := fun h => hJt (eq_top_iff.2 (h ▸ hMJ))
  have hMH : ¬ ∀ h : ↥H, ∀ v ∈ M, hs.act h v ∈ M := by
    intro hall
    rcases hs.irr hirr M hall with h | h
    · exact hMb h
    · exact hMt h
  push Not at hMH
  obtain ⟨h, v₀, hv₀M, hv₀⟩ := hMH
  set a := hs.act h with ha
  have haN := Subgroup.mem_normalizer_iff.1
    (hs.autSec_le_normalizer ((hs.mem_autSec_iff le_rfl).2 ⟨h, h.2, rfl⟩))
  set N := M.map a.toMonoidHom with hN
  have hNinv : ∀ l ∈ LE, ∀ v ∈ N, l v ∈ N := by
    rintro l hl _ ⟨m, hm, rfl⟩
    refine ⟨(a⁻¹ * l * a) m, hMinv _ ?_ m hm, ?_⟩
    · rw [haN]
      have e : a * (a⁻¹ * l * a) * a⁻¹ = l := by group
      rw [e]
      exact hl
    · simp [MulAut.mul_apply]
  have hcardN : Nat.card ↥N = Nat.card ↥M := Subgroup.card_map_of_injective a.injective
  have hMN : M ⊓ N = ⊥ := by
    by_contra hne
    have hinv : ∀ l ∈ LE, ∀ v ∈ M ⊓ N, l v ∈ M ⊓ N := fun l hl v hv =>
      ⟨hMinv l hl v hv.1, hNinv l hl v hv.2⟩
    have h1 : M ⊓ N = M := by
      by_contra h2
      exact hMmin (M ⊓ N) ⟨hne, inf_le_left.trans hMJ, hinv⟩ (lt_of_le_of_ne inf_le_left h2)
    have hMleN : M ≤ N := h1 ▸ inf_le_right
    have hMeqN : M = N := Subgroup.eq_of_le_of_card_ge hMleN (by rw [hcardN])
    apply hv₀
    have h2 : a v₀ ∈ N := ⟨v₀, hv₀M, rfl⟩
    rwa [← hMeqN] at h2
  let Φ : ↥M × ↥N →* E := M.subtype.coprod N.subtype
  have hΦi : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨m, n⟩ h1
    change (m : E) * (n : E) = 1 at h1
    have hm : (m : E) ∈ M ⊓ N := ⟨m.2, by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact N.inv_mem n.2⟩
    rw [hMN, Subgroup.mem_bot] at hm
    have hn : (n : E) = 1 := by rw [hm, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext hm) (Subtype.ext hn)
  have hcardMN : Nat.card ↥M * Nat.card ↥N ≤ Nat.card E := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective Φ hΦi
  have hM6 := A6G2.six_le_card_of_inv hV hP hfix hMinv hMb
  have hM64 : Nat.card ↥M = 2 ^ 6 := by
    rw [hcardN] at hcardMN
    by_contra hne
    have hlt : 2 ^ 6 < Nat.card ↥M := lt_of_le_of_ne hM6 (Ne.symm hne)
    have := Nat.mul_lt_mul'' hlt hlt
    omega
  have hcardE' : Nat.card E = 2 ^ 12 := by
    rw [hcardN, hM64] at hcardMN
    omega
  obtain ⟨D, hDinv, hcardD, hDM, hDN, hclass⟩ := A6G2.classify_six hV hP hfix hMinv hNinv hMN
    hM64 (by rw [hcardN, hM64]) hcardE'
  have hTH : T ≤ H := hs.hHK ▸ le_sup_right
  have hT2 : IsPGroup 2 ↥T := (hs.hS.hF H hs.hH).toHypF91.sylow.2.1
  let ψT : ↥T →* MulAut E := hs.act.comp (Subgroup.inclusion hTH)
  have hψinv : ∀ (t : ↥T) (M' : Subgroup E), (∀ l ∈ LE, ∀ v ∈ M', l v ∈ M') →
      ∀ l ∈ LE, ∀ v ∈ M'.map (ψT t).toMonoidHom, l v ∈ M'.map (ψT t).toMonoidHom := by
    intro t M' hM' l hl
    have hN' := Subgroup.mem_normalizer_iff.1 (hs.autSec_le_normalizer
      ((hs.mem_autSec_iff le_rfl).2 ⟨Subgroup.inclusion hTH t, hTH t.2, rfl⟩))
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨((ψT t)⁻¹ * l * ψT t) m, hM' _ ?_ m hm, ?_⟩
    · rw [hN']
      show ψT t * ((ψT t)⁻¹ * l * ψT t) * (ψT t)⁻¹ ∈ autSec (autOn K X) ⊤ (W.subgroupOf X)
      have e : ψT t * ((ψT t)⁻¹ * l * ψT t) * (ψT t)⁻¹ = l := by group
      rw [e]
      exact hl
    · simp [MulAut.mul_apply]
  let α := {M' : Subgroup E // (∀ l ∈ LE, ∀ v ∈ M', l v ∈ M') ∧ Nat.card ↥M' = 2 ^ 6}
  let _ : MulAction ↥T α :=
    { smul := fun t M' => ⟨M'.1.map (ψT t).toMonoidHom, hψinv t M'.1 M'.2.1,
        (Subgroup.card_map_of_injective (f := (ψT t).toMonoidHom) (ψT t).injective).trans
          M'.2.2⟩
      one_smul := fun M' => Subtype.ext (by
        ext v
        show v ∈ M'.1.map (ψT 1).toMonoidHom ↔ v ∈ M'.1
        rw [map_one]
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact hw
        · intro hv
          exact ⟨v, hv, rfl⟩)
      mul_smul := fun t₁ t₂ M' => Subtype.ext (by
        ext v
        show v ∈ M'.1.map (ψT (t₁ * t₂)).toMonoidHom ↔
          v ∈ (M'.1.map (ψT t₂).toMonoidHom).map (ψT t₁).toMonoidHom
        rw [map_mul]
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact ⟨(ψT t₂) w, ⟨w, hw, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
          exact ⟨w, hw, rfl⟩) }
  have hNb : N ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot, hM64] at hcardN
    norm_num at hcardN
  have hMN' : M ≠ N := fun h1 => hMb (by rw [← inf_idem M]; nth_rw 2 [h1]; exact hMN)
  have hMD : M ≠ D := fun h1 => hMb (by rw [← inf_idem M]; nth_rw 1 [h1]; exact hDM)
  have hND : N ≠ D := fun h1 => hNb (by rw [← inf_idem N]; nth_rw 1 [h1]; exact hDN)
  have hα : Nat.card α = 3 := by
    have e : α ≃ {M' : Subgroup E // M' ∈ ({M, N, D} : Finset (Subgroup E))} :=
      Equiv.subtypeEquivRight fun M' => by
        constructor
        · rintro ⟨h1, h2⟩
          rcases hclass M' h1 h2 with h3 | h3 | h3 <;> simp [h3]
        · intro hM'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hM'
          rcases hM' with h3 | h3 | h3 <;> rw [h3]
          · exact ⟨hMinv, hM64⟩
          · exact ⟨hNinv, by rw [hcardN, hM64]⟩
          · exact ⟨hDinv, hcardD⟩
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
      Finset.card_insert_of_notMem (by simp [hMN', hMD]),
      Finset.card_insert_of_notMem (by simp [hND]), Finset.card_singleton]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hT2.card_modEq_card_fixedPoints α
  rw [hα] at hmod
  have hne : Nat.card (MulAction.fixedPoints ↥T α) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨⟨⟨⟨M₀, hM₀inv, hM₀c⟩, hfixM₀⟩⟩, -⟩ := Nat.card_ne_zero.1 hne
  have hM₀H : ∀ h' : ↥H, ∀ v ∈ M₀, hs.act h' v ∈ M₀ := by
    intro h' v hv
    have hh' : (h' : G) ∈ ((T ⊔ K : Subgroup G) : Set G) := by
      rw [sup_comm, ← hs.hHK]
      exact h'.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T K (hTH.trans hs.hKn)] at hh'
    obtain ⟨t, ht, k, hk, htk⟩ := hh'
    have e : h' = (⟨t, hTH ht⟩ : ↥H) * ⟨k, hs.hKH hk⟩ := Subtype.ext htk.symm
    rw [e, map_mul, MulAut.mul_apply]
    have hkv : hs.act ⟨k, hs.hKH hk⟩ v ∈ M₀ :=
      hM₀inv _ ((hs.mem_autSec_iff hs.hKH).2 ⟨_, hk, rfl⟩) v hv
    have h1 : M₀.map (ψT ⟨t, ht⟩).toMonoidHom = M₀ :=
      congrArg Subtype.val (hfixM₀ ⟨t, ht⟩)
    have h2 : (ψT ⟨t, ht⟩) (hs.act ⟨k, hs.hKH hk⟩ v) ∈ M₀.map (ψT ⟨t, ht⟩).toMonoidHom :=
      ⟨_, hkv, rfl⟩
    rw [h1] at h2
    exact h2
  rcases hs.irr hirr M₀ hM₀H with h0 | h0
  · rw [h0, Subgroup.card_bot] at hM₀c
    norm_num at hM₀c
  · rw [h0, Subgroup.card_top, hcardE'] at hM₀c
    norm_num at hM₀c

end SecHyp

end Setting4

end CFSG.Quasithin.H13.A6
