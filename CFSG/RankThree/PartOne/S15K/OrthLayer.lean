module

public import CFSG.RankThree.PartOne.S15K.LayerData
public import CFSG.RankThree.PartOne.S15K.OrthLayerT
public import CFSG.RankThree.PartOne.S15K.OrthLifts
import CFSG.RankThree.PartOne.S15K.LayerFactor
import CFSG.RankThree.PartOne.S15K.LayerTransport

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.RankThree.Classical2 CFSG.ComponentClassification

section Transport

variable {G : Type*} [Group G]

theorem layer_of_family {I : Subgroup G} {T : Type*} [Group T] (φ : ↥I ≃* T) {b : G}
    (hb : b ∈ Subgroup.normalizer (I : Set G)) {a : T}
    (hcompat : ∀ x : ↥I, φ (I.normalizerMonoidHom ⟨b, hb⟩ x) = a * φ x * a⁻¹) {p : ℕ} {ι : Type*}
    {F : ι → Subgroup T} (hF : LayerFamily p a F) :
    ∃ Q : ι → Subgroup G, (∀ i, Q i ≤ I ⊓ Subgroup.centralizer ({b} : Set G)) ∧
      (∀ i, IsComponent ((Q i).subgroupOf (I ⊓ Subgroup.centralizer ({b} : Set G)))) ∧
      ⁅I ⊓ Subgroup.centralizer ({b} : Set G), I ⊓ Subgroup.centralizer ({b} : Set G)⁆ =
        ⨆ i, Q i ∧
      ∀ i (x : G), x ∈ Q i ↔ ∃ hx : x ∈ I, φ ⟨x, hx⟩ ∈ F i := by
  classical
  set ψ : ↥I →* T := φ.toMonoidHom with hψdef
  have hψ : Function.Injective ψ := φ.injective
  set H₀ := I ⊓ Subgroup.centralizer ({b} : Set G) with hH₀
  set Φ := centRestrict ψ b with hΦdef
  have hΦ : Function.Injective Φ := centRestrict_injective hψ b
  have hψtop : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr φ.surjective
  have hrange : Φ.range = Subgroup.centralizer ({a} : Set T) := by
    rw [hΦdef, range_centRestrict ψ hψ hb hcompat, hψtop, top_inf_eq]
  have hJ : ∀ i, F i ≤ Φ.range := fun i => by rw [hrange]; exact hF.le i
  have hcomp : ∀ i, IsComponent ((F i).subgroupOf Φ.range) := fun i => by
    rw [hrange]
    exact hF.comp i
  have hder : ⁅Φ.range, Φ.range⁆ = ⨆ i, F i := by
    rw [hrange]
    exact hF.derived
  obtain ⟨h1, h2, h3⟩ := layer_transport Φ hΦ F hJ hcomp hder
  refine ⟨fun i => ((F i).comap Φ).map H₀.subtype, h1, h2, h3, fun i x => ?_⟩
  simp only [Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2.1, hy⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨y, hyy⟩ := hJ i hy
    have hyx : Subgroup.inclusion (inf_le_left : H₀ ≤ I) y = ⟨x, hx⟩ := hψ hyy
    refine ⟨y, ?_, congrArg Subtype.val hyx⟩
    show Φ y ∈ F i
    rw [hyy]
    exact hy

end Transport

section Plane

theorem exists_plane_through {T : Type*} [Group T] {p : ℕ} (hp : p.Prime) {E : Type*} [Group E]
    [Finite E] (hEcard : Nat.card E = p ^ 3) (aHom : E →* T) (hinj : Function.Injective aHom)
    (hexp : ∀ e, aHom e ^ p = 1) (hcomm : ∀ e e', aHom e * aHom e' = aHom e' * aHom e) (b : E)
    (hbp : b ^ p = 1) (hb : b ≠ 1) :
    ∃ A : Subgroup T, IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧ aHom b ∈ A := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hbo : orderOf b = p := orderOf_eq_prime hbp hb
  have hcardz : Nat.card (Subgroup.zpowers b) = p ^ 1 := by
    rw [Nat.card_zpowers, hbo, pow_one]
  obtain ⟨K₀, hK₀, hbK⟩ := Sylow.exists_subgroup_card_pow_prime_le p (n := 1) (m := 2)
    (by rw [hEcard]; exact pow_dvd_pow p (by norm_num)) (Subgroup.zpowers b) hcardz (by norm_num)
  refine ⟨K₀.map aHom, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_, ⟨b, hbK (Subgroup.mem_zpowers b), rfl⟩⟩
  · rintro ⟨_, k, hk, rfl⟩ ⟨_, k', hk', rfl⟩
    exact Subtype.ext (hcomm k k')
  · rintro _ ⟨k, hk, rfl⟩
    exact hexp k
  · rw [Subgroup.card_map_of_injective hinj, hK₀]

end Plane

variable {G : Type} [Group G] [Finite G]

theorem LayerFamily.commute_of_ne {T : Type*} [Group T] [Finite T] {p : ℕ} {a : T} {ι : Type*}
    {F : ι → Subgroup T} (hF : LayerFamily p a F) (i : ι) :
    ∀ j, F j ≠ F i → ∀ u ∈ F i, ∀ v ∈ F j, u * v = v * u := by
  intro j hji u hu v hv
  rcases eq_or_commutator_eq_bot_of_components (hF.le i) (hF.le j) (hF.comp i) (hF.comp j) with h | h
  · exact absurd h.symm hji
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hu v hv |>.symm

omit [Finite G] in
theorem compat_of_lifts {E I : Subgroup G} {T : Type*} [Group T] (φ : ↥I ≃* T)
    (hEI : E ≤ Subgroup.normalizer (I : Set G)) (a : ↥E → T)
    (hac : ∀ e : ↥E, MulAut.conj (a e) = actP φ ⟨(e : G), hEI e.2⟩) (g' : ↥E) (y : ↥I) :
    φ (I.normalizerMonoidHom ⟨(g' : G), hEI g'.2⟩ y) = a g' * φ y * (a g')⁻¹ := by
  rw [← actP_apply φ ⟨(g' : G), hEI g'.2⟩ y, ← hac g']
  rfl

theorem exists_plane_of_lifts {p : ℕ} (hp : p.Prime) {E : Type*} [Group E] [Finite E]
    {T : Type*} [Group T] (hEcard : Nat.card E = p ^ 3) (a : E → T) (hap : ∀ e, a e ^ p = 1)
    (hacomm : ∀ e e', a e * a e' = a e' * a e) (hmul : ∀ e e', a (e * e') = a e * a e')
    (hao : ∀ e : E, e ≠ 1 → orderOf (a e) = p) (b : E) (hb : b ≠ 1) :
    ∃ A : Subgroup T, IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧ a b ∈ A ∧ a b ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  let aHom : E →* T := MonoidHom.mk' a hmul
  have haHinj : Function.Injective aHom := by
    rw [injective_iff_map_eq_one]
    intro e he
    by_contra hne
    have h1 : a e = 1 := he
    have := hao e hne
    rw [h1, orderOf_one] at this
    exact hp.one_lt.ne this
  have hEpow : ∀ e : E, e ^ p = 1 := fun e => by
    apply haHinj
    rw [map_pow, map_one]
    exact hap e
  have habne : a b ≠ 1 := fun h => by
    have := hao b hb
    rw [h, orderOf_one] at this
    exact hp.one_lt.ne this
  obtain ⟨A, hA, hAcard, haA⟩ := exists_plane_through hp hEcard aHom haHinj hap hacomm b (hEpow b) hb
  exact ⟨A, hA, hAcard, haA, habne⟩

theorem layerData_clauses_of_family {p : ℕ} (hp : p.Prime) {E I : Subgroup G} {T : Type*} [Group T]
    [Finite T] (φ : ↥I ≃* T) (hEI : E ≤ Subgroup.normalizer (I : Set G)) (a : ↥E → T)
    (hap : ∀ e, a e ^ p = 1)
    (hcompat : ∀ (g' : ↥E) (y : ↥I), φ (I.normalizerMonoidHom ⟨(g' : G), hEI g'.2⟩ y) =
      a g' * φ y * (a g')⁻¹)
    (hacomm : ∀ e e' : ↥E, a e * a e' = a e' * a e) (b : ↥E) {ι : Type*} (F : ι → Subgroup T)
    (hF : LayerFamily p (a b) F) :
    ∃ Qf : ι → Subgroup G, (∀ i, Qf i ≤ I ⊓ Subgroup.centralizer ({(b : G)} : Set G)) ∧
      (∀ i, IsComponent ((Qf i).subgroupOf (I ⊓ Subgroup.centralizer ({(b : G)} : Set G)))) ∧
      ⁅I ⊓ Subgroup.centralizer ({(b : G)} : Set G), I ⊓ Subgroup.centralizer ({(b : G)} : Set G)⁆ =
        ⨆ i, Qf i ∧
      (∀ i, (∀ e ∈ E, ∃ x ∈ Qf i, ∃ y ∈ Subgroup.centralizer (Qf i : Set G), e = x * y) ∧
        ¬ p ∣ Nat.card ↥(Qf i ⊓ Subgroup.centralizer (Qf i : Set G))) ∧
      ∀ i (y : G), y ∈ Qf i ↔ ∃ hy : y ∈ I, φ ⟨y, hy⟩ ∈ F i := by
  classical
  obtain ⟨Qf, hQH, hQc, hder, hmem⟩ := layer_of_family φ (hEI b.2) (hcompat b) hF
  refine ⟨Qf, hQH, hQc, hder, fun i => ⟨?_, ?_⟩, hmem⟩
  · intro e' he'
    set eE : ↥E := ⟨e', he'⟩ with heE
    have hN : a eE ∈ Subgroup.centralizer ({a b} : Set T) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hacomm eE b)
    obtain ⟨z, k, hzk, hzc, hk⟩ := hF.factor (a eE) hN (hap eE)
    obtain ⟨X, hX, k', hk', hkX⟩ := exists_mul_of_mem_iSup_of_commute F i (hF.commute_of_ne i) hk
    refine exists_mul_mem_centralizer_of_decomp' φ.toMonoidHom φ.injective (J := F i)
      (hmem i) (fun y _ => ⟨φ.symm y, by simp⟩) (hEI he') (hcompat eE) (X := X) (y := z * k')
      ?_ hX ?_
    · have hzX : z * X = X * z := hzc X (hF.le i hX)
      rw [hzk, hkX]
      calc z * (X * k') = (z * X) * k' := by group
        _ = X * z * k' := by rw [hzX]
        _ = X * (z * k') := by group
    · intro f hf
      have h1 : z * f = f * z := hzc f (hF.le i hf)
      have h2 : k' * f = f * k' := hk' f hf
      calc z * k' * f = z * (k' * f) := by group
        _ = z * (f * k') := by rw [h2]
        _ = (z * f) * k' := by group
        _ = f * z * k' := by rw [h1]
        _ = f * (z * k') := by group
  · have hQ' : ∀ y : G, y ∈ Qf i ↔
        ∃ hy : y ∈ I, φ.toMonoidHom ⟨y, hy⟩ ∈ (F i).map (MonoidHom.id _) := by
      intro y
      rw [hmem i y, Subgroup.map_id]
      rfl
    exact not_dvd_card_inf_centralizer φ.toMonoidHom φ.injective (MonoidHom.id _) (F := F i) hQ'
      (by rw [Subgroup.map_id]; exact fun y _ => ⟨φ.symm y, by simp⟩) (fun u _ h => h) hp
      (hF.center i)

theorem layerData_of_lifts_orth {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {E I : Subgroup G} {K : Type}
    [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hdim : finrank K V = 8)
    (hq : 3 < Nat.card K) (hEcard : Nat.card E = p ^ 3) (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (φ : ↥I ≃* ProjOrthDerived Q) (a : ↥E → ProjOrthDerived Q) (hap : ∀ e, a e ^ p = 1)
    (hac : ∀ e : ↥E, MulAut.conj (a e) = actP φ ⟨(e : G), hEI e.2⟩)
    (hacomm : ∀ e e' : ↥E, a e * a e' = a e' * a e) (hao : ∀ e : ↥E, e ≠ 1 → orderOf (a e) = p)
    (hmul : ∀ e e' : ↥E, a (e * e') = a e * a e') : LayerData p E I := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Finite (ProjOrthDerived Q) := inferInstance
  intro b hb hb1
  set bE : ↥E := ⟨b, hb⟩ with hbE
  have hbne : bE ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  obtain ⟨A, hA, hAcard, haA, habne⟩ := exists_plane_of_lifts hp hEcard a hap hacomm hmul hao bE hbne
  obtain ⟨x, Rep, n, C, -, -, -, -, hFam⟩ := exists_layerFamily hQ hT hdim hp hp5 hq A hA hAcard
    (a bE) haA habne
  obtain ⟨Qf, h1, h2, h3, h4, -⟩ := layerData_clauses_of_family hp φ hEI a hap
    (compat_of_lifts φ hEI a hac) hacomm bE _ hFam
  exact ⟨_, Qf, h1, h2, h3, h4⟩

section Rows

open CFSG.Assembly.RankThreeEven (projOmegaMinus)
open CFSG.LieType.Universal.Spin (quadMinus)

theorem layerData_of_orthMinus {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (h13 : Sec13Facts G p A c L E) (hEA : E = A) {f : ℕ} (hf : 1 ≤ f)
    (hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) {b c' : GaloisField 2 f}
    (hbc : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c' ≠ 0)
    (φ₀ : ↥(lieGenerated p E) ≃* projOmegaMinus 3 (GaloisField 2 f) b c') :
    LayerData p E (lieGenerated p E) := by
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hq : 3 < Nat.card (GaloisField 2 f) := by
    rw [hK]
    rcases hpq with hd | hd
    · have hpos : 0 < 2 ^ f - 1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
      have := Nat.le_of_dvd hpos hd
      omega
    · have := Nat.le_of_dvd (by positivity) hd
      omega
  have hEcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  let φ : ↥(lieGenerated p E) ≃* ProjOrthDerived (quadMinus 4 (GaloisField 2 f) b c') :=
    φ₀.trans (projOmegaMinusEquivOrth (GaloisField 2 f) b c')
  have hOut := outPNice_of_projOmegaMinus (X := ProjOrthDerived (quadMinus 4 (GaloisField 2 f) b c'))
    hp (by omega) hf hbc (projOmegaMinusEquivOrth (GaloisField 2 f) b c').symm
  have hpI : p ∣ Nat.card (lieGenerated p E) := dvd_card_of_projOmegaMinus hf hbc φ₀ hpq
  have hQ := polar_nondegenerate_quadMinus hbc
  have hT := exists_three_totSing_quadMinus (GaloisField 2 f) b c'
  have hdim : finrank (GaloisField 2 f)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 2 f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨a, hap, hac, hacomm, hao, hmul⟩ := orth_lifts h h13 hEA hQ hT hOut hpI φ
  exact layerData_of_lifts_orth hp h5 hQ hT hdim hq hEcard (E_le_normalizer_lieGenerated hp) φ a
    hap hac hacomm hao hmul

theorem layerRowThree : LayerRowThree := by
  intro G _ _ p A c L E h15 hF h13 hout
  obtain ⟨f, hf, hpq, ⟨b, c', hbc, ⟨φ₀⟩⟩, -, hEA, -⟩ := hout
  exact layerData_of_orthMinus h15.h12 h13 hEA hf (Or.inl hpq) hbc φ₀

theorem layerRowFour : LayerRowFour := by
  intro G _ _ p A c L E h15 hF h13 hout
  obtain ⟨f, hf, hpq, ⟨b, c', hbc, ⟨φ₀⟩⟩, -, hEA, -⟩ := hout
  exact layerData_of_orthMinus h15.h12 h13 hEA hf (Or.inr hpq) hbc φ₀

end Rows

end CFSG.RankThree.PartOne.S15K
