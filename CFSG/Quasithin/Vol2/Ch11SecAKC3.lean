module

public import CFSG.Quasithin.Vol2.Ch11SecAKC2
public import CFSG.Quasithin.Vol2.Ch11G2Q8ParG2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Quasithin.Vol2.Ch11.G2Q8

namespace KC3

variable {G : Type*} [Group G]

@[expose] def normSub (S : Set G) : Submonoid G where
  carrier := {x | ∀ s ∈ S, x * s * x⁻¹ ∈ S}
  one_mem' := fun s hs => by simpa using hs
  mul_mem' := by
    intro x y hx hy s hs
    have h := hx _ (hy s hs)
    rwa [show x * (y * s * y⁻¹) * x⁻¹ = x * y * s * (x * y)⁻¹ by group] at h

theorem inv_conj_mem {τ : G} {k : ℕ} (hk : τ ^ 2 ^ k = 1) {S : Set G}
    (h : ∀ s ∈ S, τ * s * τ⁻¹ ∈ S) {s : G} (hs : s ∈ S) : τ⁻¹ * s * τ ∈ S := by
  have hτ : τ⁻¹ = τ ^ (2 ^ k - 1) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, hk]
  have hmem : τ ^ (2 ^ k - 1) ∈ normSub S := (normSub S).pow_mem (show τ ∈ normSub S from h) _
  have h2 := hmem s hs
  rwa [← hτ, inv_inv] at h2

end KC3

open KC2 KC3 in
theorem factRadicalPointG2_holds : FactRadicalPointG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU τ ⟨k, hk⟩ hτZ hτH hτP₁ hτc
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have := finite_cayleyGroup (F := K)
  have h4 := four_le_card hn hK
  have hRF := factRadicalFixedG2_holds K n hn hK W hW H Z π hπ P hP U hU
  have hPt := factPointG2A_holds K n hn hK W hW H Z π hπ P hP U hU
  set P₁ := perfectCore (H ⊓ stabW U) with hP₁
  set O := pCoreOf 2 P₁ with hO
  have hOτ : ∀ x ∈ O, τ * x * τ⁻¹ ∈ O := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hτc x
    rw [Subgroup.coe_subtype, hyx]
    refine O.mul_mem ⟨y, by exact hy, rfl⟩ ⟨x, hx, rfl⟩
  have hOτ' : ∀ x ∈ O, τ⁻¹ * x * τ ∈ O := fun x hx =>
    inv_conj_mem hk (S := (O : Set (MulAut W))) hOτ hx
  have hτZ' : τ⁻¹ ∈ stabW Z := (stabW Z).inv_mem hτZ
  have hmapU : ∀ s : MulAut W, s ∈ stabW Z → (∀ x ∈ O, s⁻¹ * x * s ∈ O) →
      ∀ u ∈ U, s u ∈ U := by
    intro s hsZ hsO u hu
    refine hRF (s u) fun x hx => ?_
    have hx' : s⁻¹ * (x : MulAut W) * s ∈ O :=
      hsO _ ⟨x, by exact hx, rfl⟩
    have h1 := hPt _ (Subgroup.map_subtype_le _ hx') u hu
    obtain ⟨z, hz, hze⟩ : ∃ z ∈ Z, (s⁻¹ * (x : MulAut W) * s) u = z * u :=
      ⟨_, h1, by group⟩
    have e : (x : MulAut W) (s u) = s ((s⁻¹ * (x : MulAut W) * s) u) := by
      simp [MulAut.mul_apply]
    rw [e, hze, map_mul, mul_inv_cancel_right]
    exact (mem_stabW.mp hsZ z).mp hz
  have hτU : τ ∈ stabW U := mem_stabW.mpr fun u => by
    refine ⟨hmapU τ hτZ hOτ' u, fun h => ?_⟩
    have h1 := hmapU τ⁻¹ hτZ' (by simpa using hOτ) _ h
    rwa [MulAut.inv_apply_self] at h1
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hU1 := eq_U1_of_isFlagWG hW hf hc0 hc1 hg (by rw [hK]; exact hU)
  subst hU1
  have hτZz : ∀ z ∈ Z, τ z ∈ Z := fun z hz => (mem_stabW.mp hτZ z).mp hz
  have hτZz' : ∀ z ∈ Z, τ⁻¹ z ∈ Z := fun z hz => (mem_stabW.mp hτZ' z).mp hz
  have hτH' : ∀ h ∈ H, τ⁻¹ * h * τ ∈ H := fun h hh =>
    inv_conj_mem hk (S := (H : Set (MulAut W))) hτH hh
  have hU₃f : IsFlagW H P Z (2 ^ n) 3 (hf.pre (gmapG g (stdF K 3)).toAddSubgroup) := by
    rw [← hK]
    exact isFlagW_preG hW hf hc0 hc1 hg (stdF_stable 3) (card_stdF (by norm_num))
  have hτU₃ := (factN13G2_holds K n hn hK W hW H Z π hπ P hP _ _ hU hU₃f τ hτZ hτH).mp hτU
  have hx0 : (q6 (1 : K) 0 0 0 0 0) ≠ 0 := fun h => one_ne_zero (congrFun h (.inl 0))
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_g2Derived hc0 hc1 _ T hT)
    hx0 τ hτZz hτZz' hτH'
  have hcomm : ∀ k' ∈ P₁, τ * k' * τ⁻¹ * k'⁻¹ ∈ O := by
    intro k' hk'
    obtain ⟨y, hy, hyx⟩ := hτc ⟨k', hk'⟩
    rw [hyx, mul_inv_cancel_right]
    exact ⟨y, by exact hy, rfl⟩
  have hσid := sigma_eq_id_of_centralizesG h4 hf hc0 hc1 g hτZz hτU hτU₃ hcomm hσ
  set T := hf.autMap τ hτZz with hTdef
  have hTf : ∀ w, T (f w) = f (τ w) := hf.autMap_apply τ hτZz
  have hTlin : ∀ (c : K) (x : Ix3 → K), T (c • x) = c • T x := fun c x => by
    rw [hσ, hσid]
  obtain ⟨w₀, hw₀⟩ := hf.surj (g2Act g (eu 0 (1 : K)))
  have hw₀U : w₀ ∈ hf.pre (gmapG g (stdF K 1)).toAddSubgroup := by
    change f w₀ ∈ gmapG g (stdF K 1)
    rw [hw₀, mem_gmapG_stdF_one_iff]
    exact ⟨1, (one_smul _ _).symm⟩
  have hτw₀ : f (τ w₀) ∈ gmapG g (stdF K 1) := (mem_stabW.mp hτU w₀).mp hw₀U
  obtain ⟨l, hl⟩ := mem_gmapG_stdF_one_iff.mp hτw₀
  have hTy : T (g2Act g (eu 0 (1 : K))) = l • g2Act g (eu 0 (1 : K)) := by
    rw [← hl, ← hTf, hw₀]
  have hpow : ∀ m : ℕ, f ((τ ^ m) w₀) = l ^ m • g2Act g (eu 0 (1 : K)) := by
    intro m
    induction m with
    | zero => simp [hw₀]
    | succ m ih =>
      rw [pow_succ', MulAut.mul_apply, ← hTf, ih, hTlin, hTy, smul_smul, pow_succ]
  have hl1 : l ^ 2 ^ k = 1 := by
    have h := hpow (2 ^ k)
    rw [hk, MulAut.one_apply, hw₀] at h
    have h2 : (l ^ 2 ^ k - 1) • g2Act g (eu 0 (1 : K)) = 0 := by
      rw [sub_smul, one_smul, ← h, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 (g2Act_eu_ne_zero g)
  have hl' : l = 1 := by
    have h0 : (l - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, hl1, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h0)
  intro u hu
  rw [← hf.ker, hf.map_mul_inv, ← hTf, sub_eq_zero]
  obtain ⟨t, ht⟩ := mem_gmapG_stdF_one_iff.mp (show f u ∈ gmapG g (stdF K 1) from hu)
  rw [ht, hTlin, hTy, hl', one_smul]

end CFSG.Quasithin.Vol2.Ch11.SecA
