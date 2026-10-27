module

public import CFSG.RankThree.GF2n.Tim79a34QaFacts
public import CFSG.GroupTheory.GroupAction.CoprimeSeriesTrivial

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open CFSG.LargeExtraspecial.Timmesfeld (Qa IsExtraspecial2 HasWidth)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem sh_exists_v {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) : ∃ v ∈ V, v ∉ wOf V H := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  by_contra hcon
  push Not at hcon
  exact hc.not_V_le_wOf (fun v hv => hcon v hv)

theorem sh_Q_eq_P {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) : Q = P :=
  le_antisymm cfg.qp cfg.hyp.setup.mc.toMinCex.P_le_Q

theorem sh_coatom_avoid {P : Subgroup G} (hP2 : IsPGroup 2 P) {v : G} (hvP : v ∈ P)
    (hv : v ∉ inSubgroup frattini P) :
    ∃ K : Subgroup P, IsCoatom K ∧ K.index = 2 ∧ (⟨v, hvP⟩ : P) ∉ K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hex : ∃ K : Subgroup P, IsCoatom K ∧ (⟨v, hvP⟩ : P) ∉ K := by
    by_contra hcon
    push Not at hcon
    apply hv
    refine ⟨⟨v, hvP⟩, ?_, rfl⟩
    show (⟨v, hvP⟩ : P) ∈ (⨅ a ∈ {H : Subgroup P | IsCoatom H}, a : Subgroup P)
    rw [Subgroup.mem_iInf]
    intro K
    rw [Subgroup.mem_iInf]
    intro hK
    exact hcon K hK
  obtain ⟨K, hK, hvK⟩ := hex
  haveI : Group.IsNilpotent P := hP2.isNilpotent
  exact ⟨K, hK, (IsPGroup.isCoatom_iff_index_eq_prime hP2).mp hK, hvK⟩

theorem sh_mem_sup_of_commute (E F : Subgroup G) (hc : ∀ e ∈ E, ∀ f ∈ F, Commute e f)
    {x : G} (hx : x ∈ E ⊔ F) : ∃ e ∈ E, ∃ f ∈ F, e * f = x := by
  let S : Subgroup G :=
    { carrier := {x | ∃ e ∈ E, ∃ f ∈ F, e * f = x}
      mul_mem' := by
        rintro _ _ ⟨e₁, he₁, f₁, hf₁, rfl⟩ ⟨e₂, he₂, f₂, hf₂, rfl⟩
        refine ⟨e₁ * e₂, E.mul_mem he₁ he₂, f₁ * f₂, F.mul_mem hf₁ hf₂, ?_⟩
        have h12 : f₁ * e₂ = e₂ * f₁ := (hc e₂ he₂ f₁ hf₁).symm.eq
        calc e₁ * e₂ * (f₁ * f₂) = e₁ * (e₂ * f₁) * f₂ := by group
          _ = e₁ * (f₁ * e₂) * f₂ := by rw [h12]
          _ = e₁ * f₁ * (e₂ * f₂) := by group
      one_mem' := ⟨1, E.one_mem, 1, F.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨e, he, f, hf, rfl⟩
        refine ⟨e⁻¹, E.inv_mem he, f⁻¹, F.inv_mem hf, ?_⟩
        rw [mul_inv_rev]
        exact (hc e he f hf).inv_inv.eq }
  have hle : E ⊔ F ≤ S := sup_le (fun e he => ⟨e, he, 1, F.one_mem, mul_one e⟩)
    (fun f hf => ⟨1, E.one_mem, f, hf, one_mul f⟩)
  obtain ⟨e, he, f, hf, h⟩ := hle hx
  exact ⟨e, he, f, hf, h⟩

theorem sh_exists_F {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h11b : Lemma11bStatement) (cfg : QPCfg M V Q P H Φ ψ a T) {v : G} (hvV : v ∈ V)
    (hvW : v ∉ wOf V H) :
    ∃ F : Subgroup G, F ≤ Q ∧ v ∉ F ∧ Nat.card F * 2 = Nat.card Q ∧
      ∀ X : Subgroup G, F ≤ X → X ≤ Q → v ∈ X → X = Q := by
  have hH := cfg.hyp
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hQP : Q = P := sh_Q_eq_P cfg
  have hfr : inSubgroup frattini P = V ⊓ wOf V H :=
    (h11b G M V Q P H hH cfg.centre cfg.iw).2.1
  have hvP : v ∈ P := hc.V_le_P hvV
  have hv : v ∉ inSubgroup frattini P := by
    rw [hfr]
    exact fun h => hvW (Subgroup.mem_inf.mp h).2
  obtain ⟨K, hK, hKidx, hvK⟩ := sh_coatom_avoid hc.isPGroup_P hvP hv
  rw [hQP]
  refine ⟨K.map P.subtype, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  · intro h
    obtain ⟨y, hy, hyv⟩ := Subgroup.mem_map.mp h
    have hy' : y = ⟨v, hvP⟩ := Subtype.ext hyv
    exact hvK (hy' ▸ hy)
  · have hcard : Nat.card (K.map P.subtype) = Nat.card K :=
      (Nat.card_congr (K.equivMapOfInjective P.subtype P.subtype_injective).toEquiv).symm
    have hm := Subgroup.card_mul_index K
    rw [hKidx] at hm
    rw [hcard]
    exact hm
  · intro X hFX hXP hvX
    have hle : K ≤ X.subgroupOf P := by
      intro y hy
      rw [Subgroup.mem_subgroupOf]
      exact hFX (Subgroup.mem_map_of_mem P.subtype hy)
    have hne : K ≠ X.subgroupOf P := by
      intro h
      apply hvK
      rw [h]
      exact Subgroup.mem_subgroupOf.mpr hvX
    have htop : X.subgroupOf P = ⊤ := hK.2 _ (lt_of_le_of_ne hle hne)
    apply le_antisymm hXP
    intro y hy
    have hyX : (⟨y, hy⟩ : P) ∈ X.subgroupOf P := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hyX

theorem sh_sup_eq_Q {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) {v : G} (hvV : v ∈ V) {F : Subgroup G} (hFQ : F ≤ Q)
    (hFmax : ∀ X : Subgroup G, F ≤ X → X ≤ Q → v ∈ X → X = Q) :
    Subgroup.zpowers v ⊔ F = Q := by
  have hX : Subgroup.zpowers v ⊔ F ≤ Q :=
    sup_le (Subgroup.zpowers_le.mpr (cfg.hyp.setup.mc.toMinCex.V_le_Q hvV)) hFQ
  exact hFmax _ le_sup_right hX (Subgroup.mem_sup_left (Subgroup.mem_zpowers v))

theorem sh_commute {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h11b : Lemma11bStatement) (cfg : QPCfg M V Q P H Φ ψ a T) {v : G} (hvV : v ∈ V)
    {F : Subgroup G} (hFQ : F ≤ Q) :
    ∀ e ∈ Subgroup.zpowers v, ∀ f ∈ F, Commute e f := by
  intro e he f hf
  have heV : e ∈ V := (Subgroup.zpowers_le.mpr hvV) he
  have heZ : e ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
    rw [← centerIn_Q_eq h11b cfg] at heV
    exact heV
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp heZ).2 f (hFQ hf)).symm

theorem sh_elemAbelian (v : G) (hv2 : v ^ 2 = 1) : IsElemAbelian 2 (Subgroup.zpowers v) := by
  refine ⟨?_, ?_⟩
  · infer_instance
  · intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hv2, one_zpow]

theorem sh_two_le_card (v : G) (hv2 : v ^ 2 = 1) (hv1 : v ≠ 1) :
    2 ≤ Nat.card (Subgroup.zpowers v) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers, orderOf_eq_prime hv2 hv1]

theorem sh_inf_eq_bot (v : G) (hv2 : v ^ 2 = 1) (hv1 : v ≠ 1) {F : Subgroup G} (hvF : v ∉ F) :
    Subgroup.zpowers v ⊓ F = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf v = 2 := orderOf_eq_prime hv2 hv1
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxE, hxF⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxE
  have hk : v ^ k = v ^ (k % 2) := by
    have hv2z : v ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact hv2
    have hkd : k = k % 2 + 2 * (k / 2) := by omega
    conv_lhs => rw [hkd]
    rw [zpow_add, zpow_mul, hv2z, one_zpow, mul_one]
  rw [hk] at hxF
  rw [Subgroup.mem_bot, hk]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero]
  · rw [h1, zpow_one] at hxF
    exact absurd hxF hvF

theorem sh_comm_factor {Q : Subgroup G} {e e' f f' : G}
    (he : ∀ q ∈ Q, Commute e q) (he' : ∀ q ∈ Q, Commute e' q)
    (heQ : e ∈ Q) (he'Q : e' ∈ Q) (hf : f ∈ Q) (hf' : f' ∈ Q) :
    ⁅e * f, e' * f'⁆ = ⁅f, f'⁆ := by
  have hc1 : ⁅e, e' * f'⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (he _ (Q.mul_mem he'Q hf')).eq
  have hc2 : ⁅f, e'⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ((he' f hf).eq).symm
  have hL : ⁅e * f, e' * f'⁆ = e * ⁅f, e' * f'⁆ * e⁻¹ := by
    rw [commutatorElement_mul_left_eq_conj_mul, hc1, mul_one]
  have hR : ⁅f, e' * f'⁆ = e' * ⁅f, f'⁆ * e'⁻¹ := by
    rw [commutatorElement_mul_right_eq_mul_conj, hc2, one_mul]
  have hX : ⁅f, f'⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hf hf') (Q.inv_mem hf)) (Q.inv_mem hf')
  have h1 : e' * ⁅f, f'⁆ * e'⁻¹ = ⁅f, f'⁆ := by
    rw [(he' _ hX).eq, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : e * ⁅f, f'⁆ * e⁻¹ = ⁅f, f'⁆ := by
    rw [(he _ hX).eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [hL, hR, h1, h2]

theorem sh_derived_le {F : Subgroup G} : ⁅F, F⁆ ≤ F := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  exact F.mul_mem (F.mul_mem (F.mul_mem hg hh) (F.inv_mem hg)) (F.inv_mem hh)

theorem sh_V_four {V : Subgroup G} (hcard : Nat.card V = 4) {z v : G} (hz : z ∈ V)
    (hv : v ∈ V) (hz1 : z ≠ 1) (hv1 : v ≠ 1) (hzv : z ≠ v) (hvz : v * z ≠ 1) :
    ∀ x ∈ V, x = 1 ∨ x = z ∨ x = v ∨ x = v * z := by
  have hsub : ({1, z, v, v * z} : Set G) ⊆ (V : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact V.one_mem
    · exact hz
    · exact hv
    · exact V.mul_mem hv hz
  have h1 : (1 : G) ∉ ({z, v, v * z} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hz1.symm, hv1.symm, hvz.symm⟩
  have h2 : z ∉ ({v, v * z} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hzv, fun h => hv1 (mul_right_cancel (h.symm.trans (one_mul z).symm))⟩
  have h3 : v ≠ v * z := fun h => hz1 (mul_left_cancel (h.symm.trans (mul_one v).symm))
  have hcard4 : ({1, z, v, v * z} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair h3]
  have hVn : (V : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have heq : ({1, z, v, v * z} : Set G) = (V : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (by omega)
  intro x hx
  have hx' : x ∈ ({1, z, v, v * z} : Set G) := by
    rw [heq]
    exact hx
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx'

theorem sh_odd_conj_contra {k z v : G} {m : ℕ} (hm : Odd m) (hkm : k ^ m = 1)
    (hkz : k * z = z * k) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hkv : k * v = v * z * k) :
    False := by
  have hcz : Commute k z := hkz
  have key : ∀ n : ℕ, k ^ n * v = v * z ^ n * k ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : Commute (k ^ n) z := hcz.pow_left n
      calc k ^ (n + 1) * v = k ^ n * (k * v) := by rw [pow_succ, mul_assoc]
        _ = k ^ n * (v * z * k) := by rw [hkv]
        _ = (k ^ n * v) * z * k := by simp only [mul_assoc]
        _ = v * z ^ n * k ^ n * z * k := by rw [ih]
        _ = v * z ^ n * (k ^ n * z) * k := by simp only [mul_assoc]
        _ = v * z ^ n * (z * k ^ n) * k := by rw [hc.eq]
        _ = v * z ^ (n + 1) * k ^ (n + 1) := by
          rw [pow_succ, pow_succ]
          simp only [mul_assoc]
  have h1 := key m
  rw [hkm, one_mul, mul_one] at h1
  have h2 : (1 : G) = z ^ m := mul_left_cancel (a := v) (by rw [mul_one]; exact h1)
  obtain ⟨j, rfl⟩ := hm
  have h3 : z ^ (2 * j + 1) = z := by
    rw [pow_succ, pow_mul, sq, hz2, one_pow, one_mul]
  rw [h3] at h2
  exact hz1 h2.symm

theorem sh_odd_kill_fix {M V : Subgroup G} {k z v : G} {m : ℕ} (hkM : k ∈ M)
    (hMV : ∀ y ∈ V, k * y * k⁻¹ ∈ V) (hvV : v ∈ V)
    (hV4 : ∀ x ∈ V, x = 1 ∨ x = z ∨ x = v ∨ x = v * z)
    (hkz : k * z = z * k) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hv1 : v ≠ 1) (hvz : v ≠ z)
    (hm : Odd m) (hkm : k ^ m = 1) : k * v = v * k := by
  rcases hV4 _ (hMV v hvV) with h | h | h | h
  · exfalso
    apply hv1
    calc v = k⁻¹ * (k * v * k⁻¹) * k⁻¹⁻¹ := by group
      _ = 1 := by rw [h]; group
  · exfalso
    have hkzk : k * z * k⁻¹ = z := by rw [hkz]; group
    have h2 : k * v * k⁻¹ = k * z * k⁻¹ := by rw [h, hkzk]
    exact hvz (mul_left_cancel (mul_right_cancel h2))
  · calc k * v = k * v * k⁻¹ * k := by group
      _ = v * k := by rw [h]
  · exfalso
    have hkv : k * v = v * z * k := by
      calc k * v = k * v * k⁻¹ * k := by group
        _ = v * z * k := by rw [h]
    exact sh_odd_conj_contra hm hkm hkz hz2 hz1 hkv

theorem sh_zpow_comm {k y : G} (hky : k * y = y * k) {a : G} (ha : a ∈ Subgroup.zpowers k) :
    a * y = y * a := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact ((show Commute k y from hky).zpow_left i).eq

theorem sh_conj_mem_V {M V Q : Subgroup G} (hMN : M ≤ Subgroup.normalizer (Q : Set G))
    (hV : V = Q ⊓ Subgroup.centralizer (Q : Set G)) {g : G} (hg : g ∈ M) {y : G}
    (hy : y ∈ V) : g * y * g⁻¹ ∈ V := by
  rw [hV] at hy ⊢
  obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hMN hg) y).mp hyQ,
    Subgroup.mem_centralizer_iff.mpr (fun q hq => ?_)⟩
  have hq' : g⁻¹ * q * g ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hMN hg) (g⁻¹ * q * g)).mpr
      (by rw [show g * (g⁻¹ * q * g) * g⁻¹ = q by group]; exact hq)
  have hcm : (g⁻¹ * q * g) * y = y * (g⁻¹ * q * g) :=
    Subgroup.mem_centralizer_iff.mp hyC _ hq'
  calc q * (g * y * g⁻¹) = g * ((g⁻¹ * q * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * q * g)) * g⁻¹ := by rw [hcm]
    _ = (g * y * g⁻¹) * q := by group

theorem sh_mem_V_iff_conj {M V Q : Subgroup G} (hMN : M ≤ Subgroup.normalizer (Q : Set G))
    (hV : V = Q ⊓ Subgroup.centralizer (Q : Set G)) {g : G} (hg : g ∈ M) (y : G) :
    y ∈ V ↔ g * y * g⁻¹ ∈ V := by
  refine ⟨sh_conj_mem_V hMN hV hg, fun h => ?_⟩
  have h' := sh_conj_mem_V hMN hV (M.inv_mem hg) h
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h'

@[expose] def sh_K {M V Q : Subgroup G} (hMN : M ≤ Subgroup.normalizer (Q : Set G))
    (hV : V = Q ⊓ Subgroup.centralizer (Q : Set G)) : Subgroup G where
  carrier := {k | k ∈ M ∧ ∀ x ∈ Q, ⁅k, x⁆ ∈ V}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨M.mul_mem ha hb, fun x hx => ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact V.mul_mem (sh_conj_mem_V hMN hV ha (hb' x hx)) (ha' x hx)
  one_mem' := by
    refine ⟨M.one_mem, fun x _ => ?_⟩
    rw [commutatorElement_def]
    simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨M.inv_mem ha, fun x hx => ?_⟩
    have e : ⁅a⁻¹, x⁆ = a⁻¹ * (⁅a, x⁆)⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact sh_conj_mem_V hMN hV (M.inv_mem ha) (V.inv_mem (ha' x hx))

theorem sh_mem_K_iff {M V Q : Subgroup G} (hMN : M ≤ Subgroup.normalizer (Q : Set G))
    (hV : V = Q ⊓ Subgroup.centralizer (Q : Set G)) {k : G} :
    k ∈ sh_K hMN hV ↔ k ∈ M ∧ ∀ x ∈ Q, ⁅k, x⁆ ∈ V := Iff.rfl

theorem sh_K_conj {M V Q : Subgroup G} (hMN : M ≤ Subgroup.normalizer (Q : Set G))
    (hV : V = Q ⊓ Subgroup.centralizer (Q : Set G)) {g k : G} (hg : g ∈ M)
    (hk : k ∈ sh_K hMN hV) : g * k * g⁻¹ ∈ sh_K hMN hV := by
  obtain ⟨hkM, hkQ⟩ := (sh_mem_K_iff hMN hV).mp hk
  refine (sh_mem_K_iff hMN hV).mpr ⟨M.mul_mem (M.mul_mem hg hkM) (M.inv_mem hg),
    fun x hx => ?_⟩
  have hy : g⁻¹ * x * g ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hMN hg) (g⁻¹ * x * g)).mpr
      (by rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact hx)
  have e : ⁅g * k * g⁻¹, x⁆ = g * ⁅k, g⁻¹ * x * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact sh_conj_mem_V hMN hV hg (hkQ _ hy)

theorem sh_coprime_step {M V Q : Subgroup G} (hMN : M ≤ Subgroup.normalizer (Q : Set G))
    (hV : V = Q ⊓ Subgroup.centralizer (Q : Set G)) (hVQ : V ≤ Q) (hQM : Q ≤ M)
    (hQ2 : IsPGroup 2 Q) {k : G} (hkM : k ∈ M)
    (hkK : ∀ a ∈ Subgroup.zpowers k, a ∈ M ∧ ∀ x ∈ Q, ⁅a, x⁆ ∈ V)
    (hkV : ∀ y ∈ V, k * y = y * k) (hodd : Odd (Nat.card (Subgroup.zpowers k))) :
    ∀ x ∈ Q, k * x = x * k := by
  haveI hnorm : Subgroup.Normalizes (Subgroup.zpowers k) Q :=
    ⟨Subgroup.zpowers_le.mpr (hMN hkM)⟩
  have hMVn : M ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr (fun y => sh_mem_V_iff_conj hMN hV hg y)
  have hVn : (V.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVQ).mpr (fun q hq => hMVn (hQM hq))
  have hsmul : ∀ (a : ↥(Subgroup.zpowers k)) (x : ↥Q),
      ((a • x : ↥Q) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun a x => Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe (Subgroup.zpowers k) Q a x
  have hWinv : IsInvariant ↥(Subgroup.zpowers k) ↥Q (⊥ : Subgroup ↥Q) := by
    refine ⟨fun a g => ?_⟩
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      rw [h]
      exact MulDistribMulAction.smul_one a
    · intro h
      have h' := congrArg (fun y => a⁻¹ • y) h
      simpa using h'
  have hNinv : IsInvariant ↥(Subgroup.zpowers k) ↥Q (V.subgroupOf Q) := by
    refine ⟨fun a g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hsmul]
    exact sh_mem_V_iff_conj hMN hV (hkK (a : G) a.2).1 (g : G)
  have hWN_triv : ∀ a : ↥(Subgroup.zpowers k), ∀ m : ↥Q, m ∈ V.subgroupOf Q →
      (a • m) * m⁻¹ ∈ (⊥ : Subgroup ↥Q) := by
    intro a m hm
    rw [Subgroup.mem_subgroupOf] at hm
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hsmul, Subgroup.coe_one]
    have hcm : (a : G) * (m : G) = (m : G) * (a : G) := sh_zpow_comm (hkV _ hm) a.2
    rw [hcm]
    group
  have hNQ_triv : ∀ a : ↥(Subgroup.zpowers k), ∀ x : ↥Q,
      (a • x) * x⁻¹ ∈ V.subgroupOf Q := by
    intro a x
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hsmul,
      ← commutatorElement_def]
    exact (hkK (a : G) a.2).2 _ x.2
  have hres := CFSG.coprime_action_trivial_mod_of_fixed_normal_and_quotient
    (A := ↥(Subgroup.zpowers k)) (G := ↥Q) hodd hQ2 ⊥ (V.subgroupOf Q) bot_le hWinv hNinv
    hWN_triv hNQ_triv
  intro x hx
  have h1 := hres ⟨k, Subgroup.mem_zpowers k⟩ ⟨x, hx⟩
  rw [Subgroup.mem_bot] at h1
  have h3 := congrArg Subtype.val h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hsmul, Subgroup.coe_one] at h3
  have h4 : k * x * k⁻¹ * x⁻¹ = 1 := h3
  have h5 : k * x * k⁻¹ = x := mul_inv_eq_one.mp h4
  calc k * x = k * x * k⁻¹ * k := by group
    _ = x * k := by rw [h5]

section Cfg

variable {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}

theorem sh_central_comm (h11b : Lemma11bStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {e : G} (he : e ∈ V) : ∀ q ∈ Q, Commute e q := by
  intro q hq
  have heZ : e ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
    rw [← centerIn_Q_eq h11b cfg] at he
    exact he
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp heZ).2 q hq).symm

theorem sh_derived_eq (h11b : Lemma11bStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {v : G} (hvV : v ∈ V) {F : Subgroup G} (hFQ : F ≤ Q)
    (hsup : Subgroup.zpowers v ⊔ F = Q) : ⁅F, F⁆ = V ⊓ wOf V H := by
  have hcomm := sh_commute h11b cfg hvV hFQ
  have hVc : ∀ e ∈ Subgroup.zpowers v, e ∈ V := fun e he => (Subgroup.zpowers_le.mpr hvV) he
  have hVQ : V ≤ Q := cfg.hyp.setup.mc.toMinCex.V_le_Q
  have hle1 : ⁅F, F⁆ ≤ ⁅Q, Q⁆ := Subgroup.commutator_mono hFQ hFQ
  have hle2 : ⁅Q, Q⁆ ≤ ⁅F, F⁆ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hx' : x ∈ Subgroup.zpowers v ⊔ F := by rw [hsup]; exact hx
    have hy' : y ∈ Subgroup.zpowers v ⊔ F := by rw [hsup]; exact hy
    obtain ⟨e, he, f, hf, rfl⟩ := sh_mem_sup_of_commute _ _ hcomm hx'
    obtain ⟨e', he', f', hf', rfl⟩ := sh_mem_sup_of_commute _ _ hcomm hy'
    rw [sh_comm_factor (sh_central_comm h11b cfg (hVc e he))
      (sh_central_comm h11b cfg (hVc e' he')) (hVQ (hVc e he)) (hVQ (hVc e' he'))
      (hFQ hf) (hFQ hf')]
    exact Subgroup.commutator_mem_commutator hf hf'
  have hQQ : ⁅Q, Q⁆ = V ⊓ wOf V H := by
    have h := (h11b G M V Q P H cfg.hyp cfg.centre cfg.iw).1
    rw [sh_Q_eq_P cfg]
    exact h
  exact (le_antisymm hle1 hle2).trans hQQ

theorem sh_inf_V_F (h11b : Lemma11bStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {v : G} (hvV : v ∈ V) (hvW : v ∉ wOf V H) {F : Subgroup G} (hFQ : F ≤ Q) (hvF : v ∉ F)
    (hAF : V ⊓ wOf V H ≤ F) : V ⊓ F = V ⊓ wOf V H := by
  have hH := cfg.hyp
  have hAV : V ⊓ wOf V H ≤ V ⊓ F := le_inf inf_le_left hAF
  have hcardA : Nat.card ↥(V ⊓ wOf V H) = 2 := hH.module.trans hH.q_two
  have hcardV : Nat.card ↥V = 4 := qpCfg_card_V cfg
  have hne : V ⊓ F ≠ V := by
    intro h
    apply hvF
    have hv' : v ∈ V ⊓ F := by rw [h]; exact hvV
    exact (Subgroup.mem_inf.mp hv').2
  have hdvd : Nat.card ↥(V ⊓ F) ∣ 4 := hcardV ▸ Subgroup.card_dvd_of_le inf_le_left
  have hge : 2 ≤ Nat.card ↥(V ⊓ F) := hcardA ▸ Subgroup.card_le_of_le hAV
  have hcases : Nat.card ↥(V ⊓ F) = 2 ∨ Nat.card ↥(V ⊓ F) = 4 := by
    have hle4 : Nat.card ↥(V ⊓ F) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card ↥(V ⊓ F) = n at hdvd hge hle4 ⊢
    interval_cases n <;> first | omega | norm_num at hdvd
  rcases hcases with h2 | h4
  · exact (Subgroup.eq_of_le_of_card_ge hAV (by omega)).symm
  · exfalso
    apply hne
    exact Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)

theorem sh_centre_F (h11b : Lemma11bStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {v : G} (hvV : v ∈ V) (hvW : v ∉ wOf V H) {F : Subgroup G} (hFQ : F ≤ Q) (hvF : v ∉ F)
    (hsup : Subgroup.zpowers v ⊔ F = Q) (hder : ⁅F, F⁆ = V ⊓ wOf V H) :
    (Subgroup.center F).map F.subtype = V ⊓ wOf V H := by
  have hAF : V ⊓ wOf V H ≤ F := hder ▸ sh_derived_le
  have hVF : V ⊓ F = V ⊓ wOf V H := sh_inf_V_F h11b cfg hvV hvW hFQ hvF hAF
  apply le_antisymm
  · rintro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyF : (y : G) ∈ F := y.2
    have hyQ : ∀ q ∈ Q, q * (y : G) = (y : G) * q := by
      intro q hq
      have hq' : q ∈ Subgroup.zpowers v ⊔ F := by rw [hsup]; exact hq
      obtain ⟨e, he, f, hf, rfl⟩ :=
        sh_mem_sup_of_commute _ _ (sh_commute h11b cfg hvV hFQ) hq'
      have hfy : f * (y : G) = (y : G) * f :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨f, hf⟩)
      have hey : e * (y : G) = (y : G) * e :=
        (sh_central_comm h11b cfg (Subgroup.zpowers_le.mpr hvV he) (y : G) (hFQ hyF)).eq
      calc e * f * (y : G) = e * (f * y) := by rw [mul_assoc]
        _ = e * (y * f) := by rw [hfy]
        _ = (e * y) * f := by rw [mul_assoc]
        _ = (y * e) * f := by rw [hey]
        _ = y * (e * f) := by rw [mul_assoc]
    have hyZ : (y : G) ∈ centerIn Q :=
      Subgroup.mem_inf.mpr ⟨hFQ hyF, Subgroup.mem_centralizer_iff.mpr hyQ⟩
    rw [centerIn_Q_eq h11b cfg] at hyZ
    have hyVF : (y : G) ∈ V ⊓ F := Subgroup.mem_inf.mpr ⟨hyZ, hyF⟩
    rw [hVF] at hyVF
    exact hyVF
  · rintro x hx
    have hxF : x ∈ F := hAF hx
    have hxV : x ∈ V := (Subgroup.mem_inf.mp hx).1
    refine Subgroup.mem_map.mpr ⟨⟨x, hxF⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact ((sh_central_comm h11b cfg hxV (g : G) (hFQ g.2)).eq).symm

theorem sh_centralizer_mp (h11b : Lemma11bStatement) (h12 : Lemma12Statement)
    (cfg : QPCfg M V Q P H Φ ψ a T) {h : G}
    (hh : h ∈ Subgroup.centralizer ({cfg.aG} : Set G))
    (hcomm : ∀ x ∈ Q, ⁅h, x⁆ ∈ V) : h ∈ Q := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hcent : Subgroup.centralizer ({cfg.aG} : Set G) = M :=
    (h12 G M V Q P H cfg.hyp cfg.centre Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1
  have hhM : h ∈ M := by
    rw [← hcent]
    exact hh
  have hMQ : Q = inSubgroup (pCore 2) M := hc.hQ
  have hMN : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hMQ]
    exact (inSubgroup_pCore_two M).2.2
  have hQM : Q ≤ M := by
    rw [hMQ]
    exact (inSubgroup_pCore_two M).2.1
  have hQ2 : IsPGroup 2 Q := by
    rw [hMQ]
    exact (inSubgroup_pCore_two M).1
  have hV : V = Q ⊓ Subgroup.centralizer (Q : Set G) := (centerIn_Q_eq h11b cfg).symm
  have hVQ : V ≤ Q := hc.V_le_Q
  have hz1 : cfg.aG ≠ 1 := qpCfg_aG_ne_one cfg
  have hzV : cfg.aG ∈ V := qpCfg_aG_mem_V cfg
  have hz2 : cfg.aG * cfg.aG = 1 := by
    rw [← pow_two]
    exact hc.elemAb.2 _ hzV
  have hMz : ∀ g ∈ M, g * cfg.aG = cfg.aG * g := by
    intro g hg
    rw [← hcent] at hg
    exact (Subgroup.mem_centralizer_iff.mp hg cfg.aG (Set.mem_singleton _)).symm
  obtain ⟨v, hvV, hvW⟩ := sh_exists_v cfg
  have hv1 : v ≠ 1 := fun h => hvW (by rw [h]; exact (wOf V H).one_mem)
  have hvz : v ≠ cfg.aG := fun h => hvW (by rw [h]; exact qpCfg_aG_mem_W cfg)
  have hvz1 : v * cfg.aG ≠ 1 := by
    intro h
    apply hvz
    calc v = v * (cfg.aG * cfg.aG) := by rw [hz2, mul_one]
      _ = (v * cfg.aG) * cfg.aG := by rw [mul_assoc]
      _ = cfg.aG := by rw [h, one_mul]
  have hV4 := sh_V_four (qpCfg_card_V cfg) hzV hvV hz1 hv1 (Ne.symm hvz) hvz1
  have hKdef : ∀ k ∈ M, ∀ y ∈ V, k * y * k⁻¹ ∈ V :=
    fun k hk y hy => sh_conj_mem_V hMN hV hk hy
  have hodd_kill : ∀ k ∈ sh_K hMN hV, ∀ m : ℕ, Odd m → k ^ m = 1 → k = 1 := by
    intro k hk m hm hkm
    obtain ⟨hkM, hkQ⟩ := (sh_mem_K_iff hMN hV).mp hk
    have hkz : k * cfg.aG = cfg.aG * k := hMz k hkM
    have hkvv : k * v = v * k :=
      sh_odd_kill_fix hkM (fun y hy => hKdef k hkM y hy) hvV hV4 hkz hz2 hz1 hv1 hvz hm hkm
    have hkV : ∀ y ∈ V, k * y = y * k := by
      intro y hy
      rcases hV4 y hy with rfl | rfl | rfl | rfl
      · simp
      · exact hkz
      · exact hkvv
      · calc k * (v * cfg.aG) = (k * v) * cfg.aG := (mul_assoc k v _).symm
          _ = (v * k) * cfg.aG := by rw [hkvv]
          _ = v * (k * cfg.aG) := mul_assoc v k _
          _ = v * (cfg.aG * k) := by rw [hkz]
          _ = v * cfg.aG * k := (mul_assoc v _ k).symm
    have hodd : Odd (Nat.card (Subgroup.zpowers k)) := by
      rw [Nat.card_zpowers]
      exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hkm)
    have hkK' : ∀ a ∈ Subgroup.zpowers k, a ∈ M ∧ ∀ x ∈ Q, ⁅a, x⁆ ∈ V := fun a ha =>
      (sh_mem_K_iff hMN hV).mp (Subgroup.zpowers_le.mpr hk ha)
    have hcs := sh_coprime_step hMN hV hVQ hQM hQ2 hkM hkK' hkV hodd
    have hkC : k ∈ M ⊓ Subgroup.centralizer (Q : Set G) :=
      Subgroup.mem_inf.mpr ⟨hkM, Subgroup.mem_centralizer_iff.mpr (fun q hq => (hcs q hq).symm)⟩
    have hfit := Tim78.inf_centralizer_le_of_generalizedFitting_eq hc.fitting
    rw [← hMQ] at hfit
    have hkQ' : k ∈ Q := hfit hkC
    obtain ⟨j, hj⟩ := hQ2 ⟨k, hkQ'⟩
    have hkj : k ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hcop : Nat.Coprime (2 ^ j) m :=
      Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm.not_two_dvd_nat)
    have h1 : orderOf k ∣ Nat.gcd (2 ^ j) m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hkj) (orderOf_dvd_of_pow_eq_one hkm)
    have h2 : Nat.gcd (2 ^ j) m = 1 := hcop
    rw [h2] at h1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hK2 : IsPGroup 2 (sh_K hMN hV) := by
    show ∀ g : ↥(sh_K hMN hV), ∃ n : ℕ, g ^ 2 ^ n = 1
    intro g
    have hgK : (g : G) ∈ sh_K hMN hV := g.2
    obtain ⟨j, m, hm, hdec⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
    have hk'K : (g : G) ^ 2 ^ j ∈ sh_K hMN hV := (sh_K hMN hV).pow_mem hgK _
    have hk'm : ((g : G) ^ 2 ^ j) ^ m = 1 := by
      rw [← pow_mul, ← hdec, pow_orderOf_eq_one]
    refine ⟨j, Subtype.ext ?_⟩
    have := hodd_kill _ hk'K m hm hk'm
    simpa using this
  have hKM : sh_K hMN hV ≤ M := fun k hk => ((sh_mem_K_iff hMN hV).mp hk).1
  have hMK : M ≤ Subgroup.normalizer ((sh_K hMN hV : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact sh_K_conj hMN hV hg hk
    · intro hk
      have h' := sh_K_conj hMN hV (M.inv_mem hg) hk
      have h'' : k ∈ sh_K hMN hV := by
        rw [show g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k by group] at h'
        exact h'
      exact h''
  have hfin := Tim78.le_inSubgroup_pCore hKM hMK hK2
  rw [← hMQ] at hfin
  exact hfin ((sh_mem_K_iff hMN hV).mpr ⟨hhM, hcomm⟩)

theorem sh_centralizer_mpr (h11b : Lemma11bStatement) (h12 : Lemma12Statement)
    (cfg : QPCfg M V Q P H Φ ψ a T) {h : G} (hh : h ∈ Q) :
    h ∈ Subgroup.centralizer ({cfg.aG} : Set G) ∧ ∀ x ∈ Q, ⁅h, x⁆ ∈ V := by
  refine ⟨Subgroup.mem_centralizer_iff.mpr (fun g hg => ?_), fun x hx => ?_⟩
  · rw [Set.mem_singleton_iff.mp hg]
    exact (sh_central_comm h11b cfg (qpCfg_aG_mem_V cfg) h hh).eq
  · have hcc : ⁅h, x⁆ ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator hh hx
    have hPP := (h11b G M V Q P H cfg.hyp cfg.centre cfg.iw).1
    rw [sh_Q_eq_P cfg, hPP] at hcc
    exact (Subgroup.mem_inf.mp hcc).1

theorem sh_centralizer_quotient (h11b : Lemma11bStatement) (h12 : Lemma12Statement)
    (cfg : QPCfg M V Q P H Φ ψ a T) : ∀ h : G,
    (h ∈ Subgroup.centralizer ({cfg.aG} : Set G) ∧
      ∀ x ∈ Qa cfg.aG, h * x * h⁻¹ * x⁻¹ ∈ centerIn (Qa cfg.aG)) ↔ h ∈ Qa cfg.aG := by
  intro h
  rw [qa_aG_eq h12 cfg, centerIn_Q_eq h11b cfg]
  constructor
  · rintro ⟨hh, hcomm⟩
    exact sh_centralizer_mp h11b h12 cfg hh hcomm
  · intro hh
    exact sh_centralizer_mpr h11b h12 cfg hh

end Cfg

theorem ntStrothHyp_holds (h11a : Lemma11aStatement) (h11b : Lemma11bStatement)
    (h12 : Lemma12Statement) : NTStrothHypStatement := by
  intro G _ _ M V Q P H n Φ ψ a T cfg
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hQP : Q = P := sh_Q_eq_P cfg
  obtain ⟨v, hvV, hvW⟩ := sh_exists_v cfg
  obtain ⟨F, hFQ, hvF, hFcard, hFmax⟩ := sh_exists_F h11b cfg hvV hvW
  have hv2 : v ^ 2 = 1 := hc.elemAb.2 v hvV
  have hv1 : v ≠ 1 := fun h => hvW (by rw [h]; exact (wOf V H).one_mem)
  have hsup : Subgroup.zpowers v ⊔ F = Q := sh_sup_eq_Q cfg hvV hFQ hFmax
  have hder : ⁅F, F⁆ = V ⊓ wOf V H := sh_derived_eq h11b cfg hvV hFQ hsup
  have hcen : (Subgroup.center F).map F.subtype = V ⊓ wOf V H :=
    sh_centre_F h11b cfg hvV hvW hFQ hvF hsup hder
  have hPcard : Nat.card P = 2 ^ (4 * n - 2) :=
    (h11a G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).2.2.2
  have hn3 : 3 ≤ n := cfg.three
  have hcardF : Nat.card F = 2 ^ (2 * (2 * n - 2) + 1) := by
    have hexp : 2 * (2 * n - 2) + 1 + 1 = 4 * n - 2 := by omega
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
    rw [hFcard, hQP, hPcard, ← pow_succ, hexp]
  have hFP : F ≤ P := by
    rw [← hQP]
    exact hFQ
  refine ⟨Subgroup.zpowers v, F, 2 * n - 2, ?_, rfl, hcardF⟩
  refine
    { orderOf_z := qpCfg_orderOf_aG cfg
      elemAbelian := sh_elemAbelian v hv2
      two_le_card := sh_two_le_card v hv2 hv1
      extraspecial := ?_
      mem_derived := ?_
      inf_eq_bot := sh_inf_eq_bot v hv2 hv1 hvF
      commute := sh_commute h11b cfg hvV hFQ
      sup_eq := ?_
      centralizer_quotient := sh_centralizer_quotient h11b h12 cfg }
  · unfold IsExtraspecial2
    refine ⟨hc.isPGroup_P.to_le hFP, ?_, ?_⟩
    · rw [hder]
      exact hcen.symm
    · rw [hder]
      exact cfg.hyp.module.trans cfg.hyp.q_two
  · rw [hder]
    exact Subgroup.mem_inf.mpr ⟨qpCfg_aG_mem_V cfg, qpCfg_aG_mem_W cfg⟩
  · rw [qa_aG_eq h12 cfg]
    exact hsup

end CFSG.RankThree.GF2n.Tim79a
