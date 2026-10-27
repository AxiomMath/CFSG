module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DA
public import CFSG.Quasithin.Vol2.Ch6Sec1GreenBook
public import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Cases

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

theorem card_le_of_isSpecialPow_ch615 {P : Type} [Group P] [Finite P]
    (hP : IsSpecialPow 2 2 4 P) {E : Subgroup P} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    Nat.card E ≤ 2 ^ 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hP2, hsp⟩, hcard, hZc⟩ := hP
  have : Fact (IsPGroup 2 P) := ⟨hP2⟩
  have h512 : Nat.card P = 512 := by rw [hcard]; norm_num
  obtain ⟨hZ, hsq⟩ : Subgroup.center P = commutator P ∧ ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
    rcases hsp with ⟨hab, -⟩ | ⟨hcomm, hfr, -⟩
    · exfalso
      have htop : Subgroup.center P = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_center_iff]
        intro y
        exact hab.is_comm.comm y x
      rw [htop, Subgroup.card_top, h512] at hZc
      omega
    · exact ⟨hcomm.symm, fun x => hfr ▸ CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) x⟩
  have hexp : ∀ v : Additive (Abelianization P), 2 • v = 0 := by
    intro v
    obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = v := ⟨Additive.toMul v, rfl⟩
    induction u using QuotientGroup.induction_on with
    | H x =>
      change 2 • Additive.ofMul (Abelianization.of x) = 0
      rw [← ofMul_pow, ← map_pow]
      have hx2 : x ^ 2 ∈ (Abelianization.of : P →* Abelianization P).ker := by
        rw [Abelianization.ker_of, ← hZ]
        exact hsq x
      rw [MonoidHom.mem_ker.1 hx2]
      rfl
  let _ : Module (ZMod 2) (Additive (Abelianization P)) := AddCommGroup.zmodModule hexp
  obtain ⟨ε⟩ := CFSG.OddSolvableUnitary.nonempty_center_mulEquiv hZc
  obtain ⟨B, hBa, hBn, hB⟩ := CFSG.OddSolvableUnitary.exists_commForm hZ ε
  have hfin : Finite (Additive (Abelianization P)) :=
    Finite.of_surjective (fun x : P => Additive.ofMul (Abelianization.of x))
      fun v => QuotientGroup.mk_surjective (Additive.toMul v)
  have : Module.Finite (ZMod 2) (Additive (Abelianization P)) := Module.Finite.of_finite
  have hcardV : Nat.card (Additive (Abelianization P)) = 2 ^ 8 := by
    have h := CFSG.OddSolvableUnitary.card_eq_card_abelianization_mul hZ hZc
    rw [h512] at h
    have h2 : Nat.card (Abelianization P) = 2 ^ 8 := by omega
    rw [← h2]
    exact Nat.card_congr Additive.toMul
  set g : P → Additive (Abelianization P) := fun x => Additive.ofMul (Abelianization.of x)
    with hg
  set W : Submodule (ZMod 2) (Additive (Abelianization P)) :=
    Submodule.span (ZMod 2) (g '' (E : Set P)) with hW
  have hBE : ∀ a ∈ E, ∀ b ∈ E, B (g a) (g b) = 0 := by
    intro a ha b hb
    rw [hg, hB]
    have h1 : (⟨⁅a, b⁆, CFSG.OddSolvableUnitary.commutatorElement_mem_center hZ a b⟩ :
        Subgroup.center P) = 1 := Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr
          (hE a ha b hb))
    rw [h1, map_one, toAdd_one]
  have hWW : W ≤ B.orthogonal W := by
    rw [hW, Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      exact hBE a ha b hb
    | zero =>
      show B 0 (g b) = 0
      rw [map_zero, LinearMap.zero_apply]
    | add x y _ _ hx hy =>
      show B (x + y) (g b) = 0
      rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx =>
      show B (c • x) (g b) = 0
      rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  have hrefl : B.IsRefl := hBa.isRefl
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal hrefl W
  have htop : B.orthogonal ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    refine hBn.2 v fun w => ?_
    exact hv w Submodule.mem_top
  rw [htop, inf_bot_eq, finrank_bot, add_zero] at hdim
  have hfr8 : Module.finrank (ZMod 2) (Additive (Abelianization P)) = 8 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (Abelianization P))
    rw [hcardV, Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hle := Submodule.finrank_mono hWW
  have hW4 : Module.finrank (ZMod 2) W ≤ 4 := by omega
  have hcardW : Nat.card W ≤ 2 ^ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by norm_num) hW4
  set φ : E →* Abelianization P := (Abelianization.of : P →* Abelianization P).comp E.subtype
    with hφ
  have hrange : Nat.card φ.range ≤ Nat.card W := by
    refine Nat.card_le_card_of_injective (fun x => (⟨Additive.ofMul (x : Abelianization P),
      ?_⟩ : W)) ?_
    · obtain ⟨e, he⟩ := x.2
      rw [← he]
      exact Submodule.subset_span ⟨e, e.2, rfl⟩
    · intro x y hxy
      apply Subtype.ext
      have := congrArg Subtype.val hxy
      exact Additive.ofMul.injective this
  have hker : Nat.card φ.ker ≤ 2 := by
    have hle : φ.ker.map E.subtype ≤ Subgroup.center P := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hZ, ← Abelianization.ker_of]
      exact hx
    calc Nat.card φ.ker = Nat.card (φ.ker.map E.subtype) :=
          (Subgroup.card_map_of_injective E.subtype_injective).symm
      _ ≤ Nat.card (Subgroup.center P) := Subgroup.card_le_of_le hle
      _ = 2 := hZc
  have hE' : Nat.card E = Nat.card φ.range * Nat.card φ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rw [hE']
  calc Nat.card φ.range * Nat.card φ.ker ≤ 2 ^ 4 * 2 :=
        Nat.mul_le_mul (hrange.trans hcardW) hker
    _ = 2 ^ 5 := by norm_num

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615B

theorem commutator_le_pCoreOf_ch615 (c : Cx615B G T M L V H n) : ⁅V, L⁆ ≤ pCoreOf 2 L := by
  have h := c.hyp
  obtain ⟨hVel, hLTV, hVT⟩ := c.toCx615.V_facts
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hVL : V ≤ Subgroup.normalizer (L : Set G) := hVT.trans (h.T_le.trans h.normal)
  have hWV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hWL : ⁅V, L⁆ ≤ L := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hVL
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWL
    (Subgroup.normalizer_commutator_ge_right V L) (B2F.isPGroup_of_isElemAbelian
      (B2F.isElemAbelian_mono hWV hVel))

theorem card_commutator_ge_ch615 (c : Cx615B G T M L V H n) :
    2 ^ (2 * n) ≤ Nat.card (⁅V, L⁆ : Subgroup G) := by
  obtain ⟨F, _, _, _, hF, ψ, Y, hc⟩ := c.nat.commutator.exists_qcoord c.toCx615.isSylowTwoOf_inf
  have h1 := Nat.card_le_card_of_surjective Y hc.surj
  have h2 : Nat.card (Multiplicative (Fin 2 → F)) = 2 ^ (2 * n) := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, hF, ← pow_mul, mul_comm]
  omega

theorem not_isQ8D8_ch615 (c : Cx615B G T M L V H n) : ¬ IsQ8D8 ↥(pCoreOf 2 L) := by
  intro hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := c.hyp
  set W := ⁅V, L⁆ with hW
  have hWO := c.commutator_le_pCoreOf_ch615
  have hWel : IsElemAbelian 2 W := B2F.isElemAbelian_mono
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans c.V_facts.2.1))
    c.V_facts.1
  have hW2 : IsPGroup 2 W := B2F.isPGroup_of_isElemAbelian hWel
  obtain ⟨k, hk⟩ := hW2.exists_card_eq
  have hcard := c.card_commutator_ge_ch615
  have h16 : 2 ^ 4 ∣ Nat.card W := by
    rw [hk]
    refine pow_dvd_pow 2 ?_
    have h2n : 2 ^ 4 ≤ 2 ^ k := by
      calc 2 ^ 4 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by have := h.two_le; omega)
        _ ≤ 2 ^ k := hk ▸ hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2n
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime 2 h16
  set A : Subgroup ↥(pCoreOf 2 L) := (E.map W.subtype).subgroupOf (pCoreOf 2 L) with hA
  have hEW : E.map W.subtype ≤ pCoreOf 2 L := (Subgroup.map_subtype_le E).trans hWO
  refine false_of_isQ8D8_of_elemAbelian hQ (A := A) ?_ ?_
  · intro x hx
    rw [hA, Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, -, hy⟩ := hx
    apply Subtype.ext
    show (x : G) ^ 2 = 1
    rw [← hy]
    exact hWel.2 (y : G) y.2
  · rw [hA, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEW).toEquiv,
      Subgroup.card_map_of_injective W.subtype_injective, hE]
    norm_num

theorem not_isSpecialPow_ch615 (c : Cx615B G T M L V H n) (hn : 3 ≤ n) :
    ¬ IsSpecialPow 2 2 4 ↥(pCoreOf 2 L) := by
  intro hQ
  set W := ⁅V, L⁆ with hW
  have hWO := c.commutator_le_pCoreOf_ch615
  have hWel : IsElemAbelian 2 W := B2F.isElemAbelian_mono
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans c.V_facts.2.1))
    c.V_facts.1
  set A : Subgroup ↥(pCoreOf 2 L) := W.subgroupOf (pCoreOf 2 L) with hA
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    rw [hA, Subgroup.mem_subgroupOf] at ha hb
    exact Subtype.ext (B2F.isElemAbelian_comm hWel ha hb)
  have h1 := card_le_of_isSpecialPow_ch615 hQ hcomm
  rw [hA, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWO).toEquiv] at h1
  have h2 := c.card_commutator_ge_ch615
  have h3 : 2 ^ 6 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ^ 6 ≤ 2 ^ 5 := h3.trans (h2.trans h1)
  norm_num at this

theorem not_isQ8D8_of_commutator_le_ch615 (c : Cx615B G T M L V H n) {P : Subgroup G}
    (hWP : ⁅V, L⁆ ≤ P) : ¬ IsQ8D8 ↥P := by
  intro hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := c.hyp
  set W := ⁅V, L⁆ with hW
  have hWel : IsElemAbelian 2 W := B2F.isElemAbelian_mono
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans c.V_facts.2.1))
    c.V_facts.1
  have hW2 : IsPGroup 2 W := B2F.isPGroup_of_isElemAbelian hWel
  obtain ⟨k, hk⟩ := hW2.exists_card_eq
  have hcard := c.card_commutator_ge_ch615
  have h16 : 2 ^ 4 ∣ Nat.card W := by
    rw [hk]
    refine pow_dvd_pow 2 ?_
    have h2n : 2 ^ 4 ≤ 2 ^ k := by
      calc 2 ^ 4 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by have := h.two_le; omega)
        _ ≤ 2 ^ k := hk ▸ hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2n
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime 2 h16
  set A : Subgroup ↥P := (E.map W.subtype).subgroupOf P with hA
  have hEW : E.map W.subtype ≤ P := (Subgroup.map_subtype_le E).trans hWP
  refine false_of_isQ8D8_of_elemAbelian hQ (A := A) ?_ ?_
  · intro x hx
    rw [hA, Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, -, hy⟩ := hx
    apply Subtype.ext
    show (x : G) ^ 2 = 1
    rw [← hy]
    exact hWel.2 (y : G) y.2
  · rw [hA, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEW).toEquiv,
      Subgroup.card_map_of_injective W.subtype_injective, hE]
    norm_num

theorem not_isSpecialPow_of_commutator_le_ch615 (c : Cx615B G T M L V H n) (hn : 3 ≤ n)
    {P : Subgroup G} (hWP : ⁅V, L⁆ ≤ P) : ¬ IsSpecialPow 2 2 4 ↥P := by
  intro hQ
  set W := ⁅V, L⁆ with hW
  have hWel : IsElemAbelian 2 W := B2F.isElemAbelian_mono
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans c.V_facts.2.1))
    c.V_facts.1
  set A : Subgroup ↥P := W.subgroupOf P with hA
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    rw [hA, Subgroup.mem_subgroupOf] at ha hb
    exact Subtype.ext (B2F.isElemAbelian_comm hWel ha hb)
  have h1 := card_le_of_isSpecialPow_ch615 hQ hcomm
  rw [hA, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWP).toEquiv] at h1
  have h2 := c.card_commutator_ge_ch615
  have h3 : 2 ^ 6 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ^ 6 ≤ 2 ^ 5 := h3.trans (h2.trans h1)
  norm_num at this

theorem false_of_isAltType_ch615 (c : Cx615B G T M L V H n) (hn : n = 2) (hA : IsAltType L 5) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := c.hyp
  obtain ⟨α, hαs, -, β, -, hβk, hβe⟩ := hA
  set N := ⁅⁅V, L⁆, L⁆ with hNdef
  have hNat : IsNatQuotCh5 L N n := c.nat.commutator.commutator
  obtain ⟨F, _, _, _, hF, ψ, Y, hc⟩ := hNat.exists_qcoord c.toCx615.isSylowTwoOf_inf
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := hc.le_normalizer
  have hNU : N ≤ blockU L := Subgroup.commutator_mono c.commutator_le_pCoreOf_ch615 le_rfl
  set φ : ↥N →* Multiplicative (evenWeight 5) := β.comp (Subgroup.inclusion hNU) with hφ
  have hker : ∀ x : ↥N, φ x = 1 ↔ Y x = 1 := by
    intro x
    rw [hc.ker]
    have e1 : φ x = 1 ↔ Subgroup.inclusion hNU x ∈ β.ker := MonoidHom.mem_ker.symm
    rw [e1, hβk, Subgroup.mem_subgroupOf]
    exact ⟨fun hx => hx.2, fun hx => ⟨hNU x.2, hx⟩⟩
  have hYker : φ.ker = Y.ker := by
    ext x
    simp only [MonoidHom.mem_ker]
    exact hker x
  have hcardY : Nat.card Y.range = 16 := by
    rw [MonoidHom.range_eq_top.mpr hc.surj, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_fin, hF, hn]
    norm_num
  have hcardφ : Nat.card φ.range = 16 := by
    have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup Y.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at e1
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange Y).toEquiv] at e2
    rw [hYker] at e1
    have hpos : 0 < Nat.card Y.ker := Nat.card_pos
    have e3 := e1.symm.trans e2
    rw [hcardY] at e3
    exact Nat.eq_of_mul_eq_mul_right hpos e3
  have hφs : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [hcardφ, Nat.card_congr Multiplicative.toAdd, card_evenWeight_five']
  obtain ⟨v, hv⟩ := hφs (Multiplicative.ofAdd evenWeightVec)
  obtain ⟨ℓ₀, hℓ₀⟩ := hαs cycle012
  obtain ⟨k, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos ℓ₀).ne' 2 (by norm_num)
  set ℓ := ℓ₀ ^ 2 ^ k with hℓ
  have hαℓ : α ℓ = cycle012 ^ 2 ^ k := by rw [hℓ, map_pow, hℓ₀]
  have hℓord : orderOf ℓ = m := by
    rw [hℓ, orderOf_pow_of_dvd (by positivity : 0 < 2 ^ k).ne' ⟨m, hord⟩, hord,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hℓodd : Odd (orderOf (ℓ : G)) := by
    rw [Subgroup.orderOf_coe, hℓord]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm)
  have hαℓ1 : α ℓ ≠ 1 := by
    rw [hαℓ]
    refine cycle012_pow_ne_one fun h3 => ?_
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hvmem : (ℓ : G) * v * (ℓ : G)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hLN ℓ.2) v).mp v.2
  have hfix : φ ⟨_, hvmem⟩ = φ v := by
    have he := hβe ℓ (Subgroup.inclusion hNU v) (Subgroup.inclusion hNU ⟨_, hvmem⟩) rfl
    have hv' : Multiplicative.toAdd (φ v) = evenWeightVec := by rw [hv]; rfl
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    have e2 := he i
    change ((Multiplicative.toAdd (φ ⟨_, hvmem⟩) : evenWeight 5) : Fin 5 → ZMod 2) i =
      ((Multiplicative.toAdd (φ v) : evenWeight 5) : Fin 5 → ZMod 2)
        ((α ℓ : Equiv.Perm (Fin 5))⁻¹ i) at e2
    rw [e2, hv', hαℓ]
    exact cycle012_pow_fix (2 ^ k) i
  have hYfix : Y ⟨_, hvmem⟩ = Y v := by
    have h1 : φ (⟨_, hvmem⟩ * v⁻¹) = 1 := by rw [map_mul, map_inv, hfix, mul_inv_cancel]
    have h2 := (hker _).mp h1
    rwa [map_mul, map_inv, mul_inv_eq_one] at h2
  have hYv : Multiplicative.toAdd (Y v) ≠ 0 := by
    intro h0
    have h1 : Y v = 1 := Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
    have h2 := (hker v).mpr h1
    rw [hv] at h2
    have h3 := congrArg (fun x => ((Multiplicative.toAdd x : evenWeight 5) : Fin 5 → ZMod 2) 3)
      h2
    simp [evenWeightVec] at h3
  have hint := hc.intertwine (autHom hLN ℓ) v
  have hconj : ((autHom hLN ℓ : ↥(autOn L N)) : MulAut ↥N) v = ⟨_, hvmem⟩ :=
    Subtype.ext (autHom_apply_coe hLN ℓ v)
  rw [hconj, hYfix] at hint
  have hsq := sl2_mul_self_eq_one_ch6 (ψ (autHom hLN ℓ)).2 hYv hint.symm
  have hψ2 : autHom hLN (ℓ * ℓ) = 1 :=
    ψ.injective (by rw [map_mul, map_mul, map_one]; exact Subtype.ext hsq)
  have hℓ2 := mem_centralizer_of_autHom_eq_one hLN hψ2
  have hℓN : (ℓ : G) ∈ Subgroup.centralizer (N : Set G) := by
    obtain ⟨j, hj⟩ := hℓodd
    have hd : (ℓ : G) = ((ℓ : G) * ℓ) ^ (j + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (j + 1) = orderOf (ℓ : G) + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [hd]
    exact Subgroup.pow_mem _ hℓ2 _
  have hNL : ¬ L ≤ Subgroup.centralizer (N : Set G) := by
    intro hle
    obtain ⟨x, hx⟩ := hc.surj (Multiplicative.ofAdd ![1, 0])
    have hxL : (x : G) ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun l hl =>
        (Subgroup.mem_centralizer_iff.mp (hle hl) x x.2).symm
    have h1 := (hc.ker x).mpr hxL
    rw [hx] at h1
    have h2 := congrArg (fun y => (Multiplicative.toAdd y) 0) h1
    simp at h2
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hS := h.toHyp5_0_1.setting516 hD h.module
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hTN : T ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_commutator_ch6 (le_normalizer_commutator_ch6
      (le_sup_right.trans c.V_facts.2.1) hTL) hTL
  have hℓT : (ℓ : G) ∈ T :=
    hS.sup_inf_centralizer_le (sup_le hLN hTN) hNL ⟨Subgroup.mem_sup_left ℓ.2, hℓN⟩
  obtain ⟨j, hj⟩ := h.sylow.1 ⟨ℓ, hℓT⟩
  have hj' : (ℓ : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime (orderOf (ℓ : G)) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hℓodd)
  have hℓ1 : (ℓ : G) = 1 :=
    orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hj'))
  exact hαℓ1 (by rw [show ℓ = 1 from Subtype.ext hℓ1, map_one])

theorem isL2Quot_ch615 (c : Cx615B G T M L V H n) : IsL2Quot n (oTwoQuot ↥L) := by
  obtain ⟨e'⟩ := isL2Quot_of_lieModel (by have := c.hyp.two_le; omega) c.hyp.lie
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥L)).symm.trans e'⟩

theorem card_oTwoQuot_ch615 (c : Cx615B G T M L V H n) :
    Nat.card (oTwoQuot ↥L) = 2 ^ n * (4 ^ n - 1) :=
  c.isL2Quot_ch615.card (by have := c.hyp.two_le; omega)

end Cx615B

end CFSG.Quasithin.H13
