module

public import CFSG.Quasithin.Vol2.Ch11SecBL2UCase
public import CFSG.Quasithin.Vol2.Ch11SecBL2OQ

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

theorem le_ker_of_simple {K S : Type} [Group K] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) {N : Subgroup K} [N.Normal] (hN : IsPGroup 2 N)
    (f : K →* S) (hf : Function.Surjective f) : N ≤ f.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with h | h
  · intro x hx
    have hx' : f x ∈ N.map f := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact hx'
  · exfalso
    have hP : IsPGroup 2 S := by
      intro s
      have hs : s ∈ N.map f := by rw [h]; trivial
      obtain ⟨n, hn, rfl⟩ := hs
      obtain ⟨e, he⟩ := hN ⟨n, hn⟩
      exact ⟨e, by rw [← map_pow]; simpa using congrArg (fun x : N => f x) he⟩
    have hnt := hP.center_nontrivial
    rw [center_eq_bot_of_nonabelian hS] at hnt
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hnt

theorem exists_surjective_of_modO2_equiv {K Kp Y : Type} [Group K] [Group Kp] [Group Y]
    [Finite Y] [IsSimpleGroup Y] (hY : ∃ a b : Y, a * b ≠ b * a)
    (e : (K ⧸ CFSG.pCore 2 K) ≃* (Kp ⧸ CFSG.pCore 2 Kp)) (ψ : K →* Y)
    (hψ : Function.Surjective ψ) : ∃ ψ' : Kp →* Y, Function.Surjective ψ' := by
  have hn : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
  have hn' : (CFSG.pCore 2 Kp).Normal := CFSG.pCore_normal
  have hle := le_ker_of_simple hY CFSG.pCore_isPGroup ψ hψ
  set ψ₀ : K ⧸ CFSG.pCore 2 K →* Y := QuotientGroup.lift _ ψ hle with hψ₀
  have hψ₀s : Function.Surjective ψ₀ := by
    intro y
    obtain ⟨x, rfl⟩ := hψ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  exact ⟨(ψ₀.comp e.symm.toMonoidHom).comp (QuotientGroup.mk' _),
    (hψ₀s.comp e.symm.surjective).comp (QuotientGroup.mk'_surjective _)⟩

variable {G : Type} [Group G] [Finite G]

theorem overgroup_iso_or_a312Out
    (hM : FactMathieuOrders) {T K Kp : Subgroup G} {Y : Type}
    [Group Y] [Finite Y] {k : ℕ} (hk : 2 ≤ k) (hY : L2BadType k Y)
    (hKl : quasithinIsLocal T K) (hKpl : quasithinIsLocal T Kp) (hKKp : K ≤ Kp)
    (hKq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)) (ψ : ↥K →* Y)
    (hψ : Function.Surjective ψ)
    (h312 : A312Refined (↥(Kp ⊔ T) ⧸ CFSG.pCore 2 ↥(Kp ⊔ T))) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥Kp ⧸ CFSG.pCore 2 ↥Kp)) ∨ A312Out Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Kp ⊔ T with hHdef
  have hS : IsSylowTwoOf T H := ⟨le_sup_right, hKpl.1, hKpl.2.2.1⟩
  have hBH : K ≤ H := hKKp.trans le_sup_left
  have hL : Kp ∈ cComp H := hKpl.2.1
  have hB : K ∈ lFamily T := hKl.2.1
  have hKp : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKl.2.1
  have hYs : IsSimpleGroup Y := hY.isSimpleGroup hk
  have hYab : ∃ a b : Y, a * b ≠ b * a := nonabelian_of_perfect_surjective ψ hψ
  set σ : ↥K →* ↥(modO2Image H K) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (K.subgroupOf H)).comp
      (Subgroup.subgroupOfEquivOfLe hBH).symm.toMonoidHom with hσ
  have hσs : Function.Surjective σ :=
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hBH).symm.surjective
  have hBL : modO2Image H K ≤ modO2Image H Kp := Subgroup.map_mono fun x hx => hKKp hx
  have hN : IsPGroup 2 (CFSG.Open.pCore 2 ↥K) := by
    exact CFSG.pCore_isPGroup
  have hNn : (CFSG.Open.pCore 2 ↥K).Normal := by
    exact CFSG.pCore_normal
  rcases lemma_1_2_4_refined h312 hS hBH hB hL hKKp with heq | ⟨-, hcase⟩ | ⟨-, hnon⟩
  · exact Or.inl (nonempty_mulEquiv_modO2_of_eq hBH hL heq)
  · exact Or.inr (a312Out_of_case hM hYab hN hKq ψ hψ σ hσs hcase)
  · exact (false_of_a312Nonquasi hk hY hKq ψ hψ hBL σ hσs hnon).elim

end CFSG.Quasithin.Vol2.Ch11.SecB
