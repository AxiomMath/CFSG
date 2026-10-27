module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.Quasithin.Background.G10Basic
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.G9StmtsModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace S143V

section Faithful

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem faithful_of_solvable {Γ A : Subgroup (GLV V)} (hAΓ : A ≤ Γ) (hA2 : IsPGroup 2 A)
    (hsolv : Group.IsSolvable ↥Γ) (hO2 : pCoreOf 2 Γ = ⊥) :
    ∀ a ∈ A, (∀ f ∈ (genFittingFitting ↥Γ).map Γ.subtype, a * f = f * a) → a = 1 := by
  intro a haA hcomm
  set F : Subgroup ↥Γ := genFittingFitting ↥Γ with hF
  have hFn : F.Normal := inferInstanceAs (CFSG.fittingSubgroup ↥Γ).Normal
  let a' : ↥Γ := ⟨a, hAΓ haA⟩
  have hcent : a' ∈ Subgroup.centralizer (F : Set ↥Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have := hcomm (f : GLV V) (Subgroup.mem_map_of_mem Γ.subtype hf)
    exact Subtype.ext this.symm
  have ha'F : a' ∈ F :=
    CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hcent
  obtain ⟨j, hj⟩ : ∃ j : ℕ, a ^ 2 ^ j = 1 := by
    obtain ⟨j, hj⟩ := hA2 ⟨a, haA⟩
    exact ⟨j, by simpa using congrArg Subtype.val hj⟩
  have hja' : a' ^ 2 ^ j = 1 := Subtype.ext (by simpa using hj)
  have hconj_cent : ∀ g : ↥Γ, g * a' * g⁻¹ ∈ F ∧ ∀ f ∈ F, f * (g * a' * g⁻¹) = (g * a' * g⁻¹) * f := by
    intro g
    refine ⟨hFn.conj_mem _ ha'F g, fun f hf => ?_⟩
    have h1 : g⁻¹ * f * g ∈ F := by
      have := hFn.conj_mem f hf g⁻¹
      simpa [mul_assoc] using this
    have h2 := Subgroup.mem_centralizer_iff.mp hcent _ h1
    calc f * (g * a' * g⁻¹) = g * ((g⁻¹ * f * g) * a') * g⁻¹ := by group
      _ = g * (a' * (g⁻¹ * f * g)) * g⁻¹ := by rw [h2]
      _ = (g * a' * g⁻¹) * f := by group
  set N : Subgroup ↥Γ := Subgroup.normalClosure {a'} with hN
  have hall : ∀ x ∈ N, (∃ k : ℕ, x ^ 2 ^ k = 1) ∧ x ∈ F ∧ ∀ f ∈ F, f * x = x * f := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => (∃ k : ℕ, x ^ 2 ^ k = 1) ∧ x ∈ F ∧
      ∀ f ∈ F, f * x = x * f) ?_ ?_ ?_ ?_ hx
    · intro y hy
      obtain ⟨g, hg⟩ : ∃ g : ↥Γ, y = g * a' * g⁻¹ := by
        obtain ⟨z, hz, hzy⟩ := Group.mem_conjugatesOfSet_iff.mp hy
        rw [Set.mem_singleton_iff] at hz
        subst hz
        obtain ⟨g, hg⟩ := isConj_iff.mp hzy
        exact ⟨g, hg.symm⟩
      refine ⟨⟨j, ?_⟩, ?_, ?_⟩
      · rw [hg, conj_pow, hja']
        simp
      · rw [hg]; exact (hconj_cent g).1
      · rw [hg]; exact (hconj_cent g).2
    · exact ⟨⟨0, by simp⟩, F.one_mem, fun f _ => by simp⟩
    · rintro x y - - ⟨⟨k, hk⟩, hxF, hxc⟩ ⟨⟨l, hl⟩, hyF, hyc⟩
      refine ⟨⟨k + l, ?_⟩, F.mul_mem hxF hyF, fun f hf => ?_⟩
      · have hcomm' : Commute x y := hyc x hxF
        rw [hcomm'.mul_pow]
        have h1 : x ^ 2 ^ (k + l) = 1 := by
          rw [pow_add, pow_mul, hk, one_pow]
        have h2 : y ^ 2 ^ (k + l) = 1 := by
          rw [add_comm, pow_add, pow_mul, hl, one_pow]
        rw [h1, h2, one_mul]
      · rw [← mul_assoc, hxc f hf, mul_assoc, hyc f hf, mul_assoc]
    · rintro x - ⟨⟨k, hk⟩, hxF, hxc⟩
      refine ⟨⟨k, ?_⟩, F.inv_mem hxF, fun f hf => ?_⟩
      · rw [inv_pow, hk, inv_one]
      · have := hxc f hf
        calc f * x⁻¹ = x⁻¹ * (x * f) * x⁻¹ := by group
          _ = x⁻¹ * (f * x) * x⁻¹ := by rw [this]
          _ = x⁻¹ * f := by group
  have hNp : IsPGroup 2 N := by
    refine isPGroup_two_of_forall (K := N) fun c hc => (hall c hc).1
  have hNnorm : N.Normal := inferInstance
  have hNle : N ≤ CFSG.Open.pCore 2 ↥Γ := le_pCore 2 hNnorm hNp
  have hpc : CFSG.Open.pCore 2 ↥Γ = ⊥ := by
    have h1 : (CFSG.Open.pCore 2 ↥Γ).map Γ.subtype = ⊥ := hO2
    exact (Subgroup.map_eq_bot_iff_of_injective _ Γ.subtype_injective).mp h1
  have ha'N : a' ∈ N := Subgroup.subset_normalClosure (Set.mem_singleton a')
  have : a' = 1 := by
    have h1 := hNle ha'N
    rw [hpc] at h1
    exact Subgroup.mem_bot.mp h1
  exact congrArg Subtype.val this

end Faithful

section Extraction

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem normalClosure_le_of_le {Γ A : Subgroup (GLV V)} (hAΓ : A ≤ Γ) :
    normalClosure Γ A ≤ Γ := by
  refine (Subgroup.closure_le Γ).mpr ?_
  rintro x ⟨γ, hγ, l, hl, rfl⟩
  exact Γ.mul_mem (Γ.mul_mem hγ (hAΓ hl)) (Γ.inv_mem hγ)

theorem conj_mem_normalClosure {Γ A : Subgroup (GLV V)} {γ : GLV V} (hγ : γ ∈ Γ)
    {x : GLV V} (hx : x ∈ normalClosure Γ A) : γ * x * γ⁻¹ ∈ normalClosure Γ A := by
  unfold normalClosure at hx ⊢
  refine Subgroup.closure_induction (p := fun x _ => γ * x * γ⁻¹ ∈
    Subgroup.closure {x | ∃ γ ∈ Γ, ∃ l ∈ A, x = γ * l * γ⁻¹}) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨δ, hδ, l, hl, rfl⟩
    apply Subgroup.subset_closure
    exact ⟨γ * δ, Γ.mul_mem hγ hδ, l, hl, by group⟩
  · simp
  · intro x y _ _ hx hy
    have : γ * (x * y) * γ⁻¹ = (γ * x * γ⁻¹) * (γ * y * γ⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have : γ * x⁻¹ * γ⁻¹ = (γ * x * γ⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem dihedral_five_pow_five_eq_one : ∀ y : DihedralGroup 5, y ^ 5 = 1 →
    ∃ k : Fin 5, y = DihedralGroup.r 1 ^ (k : ℕ) := by
  decide

theorem exists_normal_five_of_dihedral {Γ A : Subgroup (GLV V)} (hAΓ : A ≤ Γ)
    (e : ↥(normalClosure Γ A) ≃* DihedralGroup 5) :
    ∃ N : Subgroup (GLV V), N ≤ Γ ∧ (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) ∧ Nat.card N = 5 := by
  set Dg := normalClosure Γ A with hDg
  let R : Subgroup (DihedralGroup 5) := Subgroup.zpowers (DihedralGroup.r 1)
  let N : Subgroup (GLV V) := (R.map e.symm.toMonoidHom).map Dg.subtype
  refine ⟨N, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact normalClosure_le_of_le hAΓ y.2
  · intro γ hγ n hn
    obtain ⟨y, ⟨r, hr, rfl⟩, rfl⟩ := hn
    have hr5 : r ^ 5 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      have : (DihedralGroup.r 1 : DihedralGroup 5) ^ 5 = 1 := by decide
      rw [this, one_zpow]
    set x : GLV V := γ * ((e.symm r : ↥Dg) : GLV V) * γ⁻¹ with hx
    have hxD : x ∈ Dg := conj_mem_normalClosure hγ (e.symm r).2
    have hx5 : (⟨x, hxD⟩ : ↥Dg) ^ 5 = 1 := by
      apply Subtype.ext
      have h1 : ((e.symm r : ↥Dg) : GLV V) ^ 5 = 1 := by
        have := congrArg (fun z : ↥Dg => (z : GLV V)) (show (e.symm r) ^ 5 = 1 by
          rw [← map_pow, hr5, map_one])
        simpa using this
      show x ^ 5 = 1
      rw [hx, conj_pow, h1]
      simp
    have he5 : e ⟨x, hxD⟩ ^ 5 = 1 := by rw [← map_pow, hx5, map_one]
    obtain ⟨k, hk⟩ := dihedral_five_pow_five_eq_one _ he5
    refine ⟨⟨x, hxD⟩, ⟨e ⟨x, hxD⟩, ?_, ?_⟩, rfl⟩
    · rw [hk]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · simp
  · have h1 : Nat.card N = Nat.card (R.map e.symm.toMonoidHom) :=
      Subgroup.card_map_of_injective Dg.subtype_injective
    have h2 : Nat.card (R.map e.symm.toMonoidHom) = Nat.card R :=
      Subgroup.card_map_of_injective e.symm.injective
    have h3 : Nat.card R = 5 := by
      rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
    rw [h1, h2, h3]

theorem exists_normal_three_of_gammaL24 {Γ : Subgroup (GLV V)} (h : IsGammaL24 Γ) :
    ∃ N : Subgroup (GLV V), N ≤ Γ ∧ (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) ∧ Nat.card N = 3 := by
  obtain ⟨B, hB3, -, hΓ⟩ := h
  refine ⟨B, ?_, ?_, hB3⟩
  · rw [hΓ]
    exact Subgroup.le_normalizer
  · intro γ hγ n hn
    rw [hΓ] at hγ
    exact (Subgroup.mem_normalizer_iff.mp hγ n).mp hn

theorem exists_normal_three_of_concl3 {Γ : Subgroup (GLV V)} (h : G112Concl3 Γ) :
    ∃ N : Subgroup (GLV V), N ≤ Γ ∧ (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) ∧ Nat.card N = 3 := by
  obtain ⟨-, P, hPn, hPe, -⟩ := h
  have := hPe
  let Zc : Subgroup ↥Γ := (Subgroup.center ↥P).map P.subtype
  let N : Subgroup (GLV V) := Zc.map Γ.subtype
  refine ⟨N, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.2
  · intro γ hγ n hn
    obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hn
    let g' : ↥Γ := ⟨γ, hγ⟩
    have hzP : (z : ↥Γ) ∈ P := z.2
    have hwP : g' * (z : ↥Γ) * g'⁻¹ ∈ P := hPn.conj_mem _ hzP g'
    refine ⟨g' * (z : ↥Γ) * g'⁻¹, ⟨⟨_, hwP⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩, rfl⟩
    intro p
    have hq : g'⁻¹ * (p : ↥Γ) * g'⁻¹⁻¹ ∈ P := hPn.conj_mem _ p.2 g'⁻¹
    have hzc := Subgroup.mem_center_iff.mp hz ⟨_, hq⟩
    have hzc' : (g'⁻¹ * (p : ↥Γ) * g') * (z : ↥Γ) = (z : ↥Γ) * (g'⁻¹ * (p : ↥Γ) * g') := by
      have := congrArg (fun w : ↥P => (w : ↥Γ)) hzc
      simpa using this
    apply Subtype.ext
    show (p : ↥Γ) * (g' * (z : ↥Γ) * g'⁻¹) = (g' * (z : ↥Γ) * g'⁻¹) * (p : ↥Γ)
    calc (p : ↥Γ) * (g' * (z : ↥Γ) * g'⁻¹)
        = g' * ((g'⁻¹ * (p : ↥Γ) * g') * (z : ↥Γ)) * g'⁻¹ := by group
      _ = g' * ((z : ↥Γ) * (g'⁻¹ * (p : ↥Γ) * g')) * g'⁻¹ := by rw [hzc']
      _ = (g' * (z : ↥Γ) * g'⁻¹) * (p : ↥Γ) := by group
  · have h1 : Nat.card N = Nat.card Zc := Subgroup.card_map_of_injective Γ.subtype_injective
    have h2 : Nat.card Zc = Nat.card (Subgroup.center ↥P) :=
      Subgroup.card_map_of_injective P.subtype_injective
    rw [h1, h2]
    exact CFSG.IsExtraspecial.center_order_p 3 ↥P

end Extraction

end S143V

end CFSG.Quasithin
