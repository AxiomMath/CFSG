module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57ModelBasic
public import CFSG.Quasithin.Background.B5FinG2U33
public import CFSG.Quasithin.Background.JonesParshallG2Field

public section

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.QuasithinUnique.Bridge.Alt57Model CFSG.Open
open scoped commutatorElement

namespace CFSG.Quasithin.FFC

open CFSG.Quasithin CFSG.Open

section G2Faithful

variable {K : Type} [Field K] [CharP K 2]

theorem zornAuto_eq_one {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : IsZornAuto g)
    (hO : ∀ x : quasithinZorn K, x.1 + x.2.2.2 = 0 → ∃ c : K, g x = x + (c, 0, 0, c)) :
    ∀ x, g x = x := by
  have hc : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hneg : ∀ y : K, -y = y := fun y => CharTwo.neg_eq y
  have h1 : ∀ x : quasithinZorn K, x.1 + x.2.2.2 = 0 → g x = x := by
    intro x hx
    obtain ⟨c, hcx⟩ := hO x hx
    have hs : x.2.2.2 = x.1 := by
      have := eq_neg_of_add_eq_zero_right hx
      rw [this, hneg]
    set N : K := x.1 * x.1 + ∑ i, x.2.1 i * x.2.2.1 i with hN
    have hxx : quasithinZornMul x x = ((N, 0, 0, N) : quasithinZorn K) := by
      rw [zornMul_self]
      refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
      · simp [hx]
      · simp [hx]
      · simp only [hs, hN]
        congr 1
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hyy := hg x x
    rw [hxx, hg.map_smul_one, hcx, zornMul_self] at hyy
    have h1' := congrArg Prod.fst hyy
    simp only [Prod.fst_add] at h1'
    have h2 : c * c = 0 := by
      have h3 : N = (x.1 + c) * (x.1 + c) + ∑ i, x.2.1 i * x.2.2.1 i := by
        simpa [Prod.fst_add, Prod.snd_add] using h1'
      rw [hN] at h3
      linear_combination (-1 : K) * h3 - (x.1 * c) * hc
    have hc0 : c = 0 := mul_self_eq_zero.mp h2
    rw [hcx, hc0]
    simp
  have h2 : g ((1, 0, 0, 0) : quasithinZorn K) = (1, 0, 0, 0) := by
    set a : quasithinZorn K := (0, ![1, 0, 0], 0, 0) with ha
    set b : quasithinZorn K := (0, 0, ![1, 0, 0], 0) with hb
    have hab : quasithinZornMul a b = ((1, 0, 0, 0) : quasithinZorn K) := by
      simp [ha, hb, quasithinZornMul, quasithinCross, Fin.sum_univ_three]
      all_goals (funext i; fin_cases i <;> simp)
    have hga : g a = a := h1 a (by simp [ha])
    have hgb : g b = b := h1 b (by simp [hb])
    rw [← hab, hg, hga, hgb]
  intro x
  obtain ⟨r, u, v, s⟩ := x
  have hx : ((r, u, v, s) : quasithinZorn K) =
      ((s, u, v, s) : quasithinZorn K) + (r + s) • ((1, 0, 0, 0) : quasithinZorn K) := by
    refine Prod.ext ?_ (Prod.ext (by simp) (Prod.ext (by simp) (by simp)))
    show r = s + (r + s) * 1
    linear_combination (-s) * hc
  have h3 : g ((s, u, v, s) : quasithinZorn K) = (s, u, v, s) := h1 _ (by
    show s + s = 0
    linear_combination s * hc)
  rw [hx, map_add, map_smul, h3, h2]


theorem injective_of_zornQ_realizes {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {π : ↥(quasithinG2 K) →* ↥H}
    (h : (FFModel.zornQ (quasithinG2 K)).RealizesVia H ⊤ ⊥ π) : Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨-, -, -, -, -, hsec, -, β, hβs, -, hβe⟩ := h
  have hO : ∀ x : quasithinZorn K, x.1 + x.2.2.2 = 0 →
      ∃ c : K, (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x = x + (c, 0, 0, c) := by
    intro x hx
    have hm0 : Multiplicative.ofAdd x ∈ (FFModel.zornQ (quasithinG2 K)).sec := hx
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨_, hm0⟩)
    have hm' := hsec γ _ hm0
    have h1 := hβe γ u ⟨_, hm0⟩ trivial hm' hu
    have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), (by trivial)⟩ : ↥(⊤ : Subgroup V)) = u := by
      apply Subtype.ext
      show ((π γ : ↥H) : MulAut V) (u : V) = (u : V)
      rw [hγ]
      rfl
    have h1' : β u = ((⟨(FFModel.zornQ (quasithinG2 K)).act γ (Multiplicative.ofAdd x), hm'⟩ :
        ↥(FFModel.zornQ (quasithinG2 K)).sec) :
        ↥(FFModel.zornQ (quasithinG2 K)).sec ⧸
          (FFModel.zornQ (quasithinG2 K)).ker.subgroupOf (FFModel.zornQ (quasithinG2 K)).sec) :=
      (congrArg β h2).symm.trans h1
    rw [hu] at h1'
    have h3 := QuotientGroup.eq.1 h1'
    rw [Subgroup.mem_subgroupOf] at h3
    obtain ⟨c, hc⟩ := h3
    refine ⟨c, ?_⟩
    have h5 : -x + (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x = (c, 0, 0, c) := hc
    exact neg_add_eq_iff_eq_add.1 h5
  have h4 := zornAuto_eq_one (mem_quasithinG2_isZornAuto γ.2) hO
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact h4 x

end G2Faithful


section G2Derived

theorem commutator_data_g2
    {Ω : Type*} [Group Ω] {H : Subgroup Ω} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (e : ↥H ≃* ↥(quasithinG2 K)) :
    IsSimpleGroup ↥⁅H, H⁆ ∧ (∃ a b : ↥⁅H, H⁆, a * b ≠ b * a) ∧
      Nat.card (MulAut ↥⁅H, H⁆) ≤ 2 * Nat.card ↥⁅H, H⁆ := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  obtain ⟨f1⟩ := nonempty_commutator_equiv e
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ = ⁅cayleyGroup K, cayleyGroup K⁆ := by
    rw [quasithinG2_eq_cayleyGroup]
  let f2 : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥⁅cayleyGroup K, cayleyGroup K⁆ :=
    MulEquiv.subgroupCongr hc
  let f3 : ↥⁅cayleyGroup K, cayleyGroup K⁆ ≃* ↥subG2 :=
    ((zornConj ε).subgroupMap _).trans
      (MulEquiv.subgroupCongr ((map_cayley_commutator ε).trans g2Two_commutator_eq))
  let F : ↥⁅H, H⁆ ≃* U33G := (((f1.trans f2).trans f3).trans u33EquivSubG2.symm)
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  have hs : IsSimpleGroup ↥⁅H, H⁆ := MulEquiv.isSimpleGroup F
  refine ⟨hs, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := u33Pres_nonabelian
    refine ⟨F.symm x, F.symm y, fun h => hxy ?_⟩
    have := congrArg F h
    simpa using this
  · rw [Nat.card_congr (MulAut.congr F).toEquiv, Nat.card_congr F.toEquiv]
    have h1 := card_mulAut_u33Pres_le
    have h2 : Nat.card U33G = 6048 := card_u33Pres
    omega

end G2Derived

end CFSG.Quasithin.FFC
