module

public import CFSG.Quasithin.Background.F6Faithful
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.A1bGL2
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.Quasithin.Background.A1cRankLemmas
public import CFSG.Quasithin.Background.A1cA132Struct
public import CFSG.Quasithin.Background.F6Components
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Background.F6Solvable

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.SectionRank
open CFSG.SectionRank.Ccomm

namespace F6

variable {D : Type*} [Group D]

section Frattini

variable (P : Subgroup D) [P.Normal] (X₀ : Subgroup ↥P) [X₀.Characteristic]

@[expose] noncomputable def frattiniConj : D →* MulAut (↥X₀ ⧸ frattini ↥X₀) :=
  (frattiniAction X₀).comp MulAut.conjNormal

variable {P X₀}

theorem mem_ker_frattiniConj {g : D} : g ∈ (frattiniConj P X₀).ker ↔
    ∀ x ∈ X₀, x⁻¹ * MulAut.conjNormal g x ∈ frattiniIn X₀ := by
  rw [frattiniConj, ← MonoidHom.comap_ker, Subgroup.mem_comap]
  exact mem_ker_frattiniAction_iff X₀ _

theorem mem_centralizer_of_mem_ker_frattiniConj
    (hfaith : ∀ α : MulAut ↥P, (orderOf α).Coprime 3 →
      (∀ x ∈ X₀, x⁻¹ * α x ∈ frattiniIn X₀) → α = 1)
    {g : D} (hg : g ∈ (frattiniConj P X₀).ker) (hco : (orderOf g).Coprime 3) :
    g ∈ Subgroup.centralizer (P : Set D) := by
  have hα : (orderOf (MulAut.conjNormal g : MulAut ↥P)).Coprime 3 :=
    Nat.Coprime.coprime_dvd_left (orderOf_map_dvd _ g) hco
  have h1 := hfaith _ hα (mem_ker_frattiniConj.mp hg)
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have h2 := congrArg (fun α : MulAut ↥P => ((α ⟨p, hp⟩ : ↥P) : D)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc p * g = g * p * g⁻¹ * g := by rw [h2]
    _ = g * p := by group

theorem exists_eq_conj_of_mem_ker {X : Type*} [Group X] [Finite X]
    (hexp : ∀ x : X, x ^ 3 = 1)
    (hcases : (∀ a b : X, a * b = b * a) ∨ IsPOnePlusTwo 3 X) {β : MulAut X}
    (hβ : β ∈ (autQuotient (frattini X)).ker) : ∃ y : X, ∀ x : X, β x = y * x * y⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hcases with hcomm | h12
  · refine ⟨1, fun x => ?_⟩
    have hΦ : frattini X = ⊥ := A1c.frattini_eq_bot_of_commutative (p := 3) hcomm hexp
    have h1 := (mem_ker_autQuotient (frattini X)).mp hβ x
    rw [hΦ, Subgroup.mem_bot] at h1
    rw [one_mul, inv_one, mul_one]
    calc β x = x * (x⁻¹ * β x) := by group
      _ = x := by rw [h1, mul_one]
  · have : CFSG.IsExtraspecial 3 X := h12.1
    rw [← range_conj_eq_ker_autQuotient_frattini (p := 3)] at hβ
    obtain ⟨y, rfl⟩ := hβ
    exact ⟨y, fun x => rfl⟩

theorem mem_of_mem_ker_frattiniConj [Finite D] {P : Subgroup D} [P.Normal] {X₀ : Subgroup ↥P}
    [X₀.Characteristic] (hexp : ∀ x ∈ X₀, x ^ 3 = 1)
    (hcases : (∀ a b : ↥X₀, a * b = b * a) ∨ IsPOnePlusTwo 3 ↥X₀) {E : Subgroup D}
    (hE : IsElemAbelian 3 E) (hEX : E ≤ X₀.map P.subtype) (hEcard : Nat.card E = 3 ^ 2)
    (hm : Open.pRank 3 (⊤ : Subgroup D) ≤ 2) {u : D} (hu : orderOf u = 3)
    (huk : u ∈ (frattiniConj P X₀).ker) : u ∈ X₀.map P.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := X₀.map P.subtype with hXdef
  set β : MulAut ↥X₀ := MulAut.characteristic X₀ (MulAut.conjNormal u) with hβdef
  have hβ : β ∈ (autQuotient (frattini ↥X₀)).ker := huk
  have hexp' : ∀ x : ↥X₀, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  obtain ⟨y, hy⟩ := exists_eq_conj_of_mem_ker hexp' hcases hβ
  set y' : D := ((y : ↥P) : D) with hy'def
  have hy'X : y' ∈ X := ⟨(y : ↥P), y.2, rfl⟩
  have hconj : ∀ x ∈ X, u * x * u⁻¹ = y' * x * y'⁻¹ := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := congrArg (fun w : ↥X₀ => ((w : ↥P) : D)) (hy ⟨x, hx⟩)
    simpa [hβdef] using h1
  by_contra hux
  set z : D := y'⁻¹ * u with hzdef
  have hzX : z ∉ X := fun hz => hux (by
    have := X.mul_mem hy'X hz
    rwa [hzdef, mul_inv_cancel_left] at this)
  have hzc : ∀ x ∈ X, Commute x z := by
    intro x hx
    have h1 := hconj x hx
    show x * (y'⁻¹ * u) = y'⁻¹ * u * x
    calc x * (y'⁻¹ * u) = y'⁻¹ * (y' * x * y'⁻¹) * u := by group
      _ = y'⁻¹ * (u * x * u⁻¹) * u := by rw [h1]
      _ = y'⁻¹ * u * x := by group
  have hz3 : z ^ 3 = 1 := by
    have hc : Commute y' z := hzc y' hy'X
    have hu' : u = y' * z := by rw [hzdef, mul_inv_cancel_left]
    have hy3 : y' ^ 3 = 1 := by
      have := hexp (y : ↥P) y.2
      simpa [hy'def] using congrArg Subtype.val this
    have h1 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    rw [hu', hc.mul_pow, hy3, one_mul] at h1
    exact h1
  have hz1 : z ≠ 1 := fun h => hzX (h ▸ X.one_mem)
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hzE : z ∉ E := fun h => hzX (hEX h)
  obtain ⟨hel, hcard⟩ := exists_elemAbelian_sup_zpowers hE hzord
    (fun e he => hzc e (hEX he)) hzE
  rw [hEcard, ← pow_succ] at hcard
  have := CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hel hcard
  omega

theorem exists_hom_GL_ker_eq [Finite D] {P : Subgroup D} [P.Normal] {X₀ : Subgroup ↥P}
    [X₀.Characteristic] (hP : IsPGroup 3 ↥P) (hexp : ∀ x ∈ X₀, x ^ 3 = 1)
    (hr : Open.pRank 3 (⊤ : Subgroup ↥X₀) ≤ 2) :
    ∃ ψ : D →* GL (Fin 2) (ZMod 3), ψ.ker = (frattiniConj P X₀).ker := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXp : IsPGroup 3 ↥X₀ := hP.to_subgroup X₀
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hXp
  obtain ⟨m, hm⟩ := (hXp.to_quotient (frattini ↥X₀)).exists_card_eq
  have hexp' : ∀ x : ↥X₀, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hcardW := (rank_two_exponent_prime_order_bound hXp hexp' hr).2
  have hmle : m ≤ 2 := by
    rw [hm] at hcardW
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcardW
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hm
  obtain ⟨ι, hι⟩ := exists_injective_GL_le_two (R := ZMod 3) hmle
  refine ⟨(ι.comp (elemAutEquivGL e).toMonoidHom).comp (frattiniConj P X₀), ?_⟩
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h
    exact (elemAutEquivGL e).injective (hι (by rw [h, map_one, map_one]))
  · intro h
    rw [h, map_one, map_one]

end Frattini

section Vertex

variable [Finite D] {G₁ G₂ : Subgroup D}

theorem perm_three_cube_mem_alternating : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 →
    Equiv.Perm.sign σ = 1 := by
  decide +kernel

theorem perm_three_alternating_cube : ∀ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 →
    σ ^ 3 = 1 := by
  decide +kernel

theorem inf_twoResidual_le_pCoreOf_left (h : IsGoldschmidtTriple G₁ G₂) :
    G₁ ⊓ G₂ ⊓ twoResidual G₁ ≤ pCoreOf 2 G₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h.quotient₁
  set φ : ↥G₁ →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Open.pCore 2 ↥G₁)) with hφ
  have hL : twoResidual G₁ ≤ ((alternatingGroup (Fin 3)).comap φ).map G₁.subtype := by
    rw [twoResidual_eq_oTwoUpper]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    show φ ⟨x, hx.1⟩ ∈ alternatingGroup (Fin 3)
    rw [Equiv.Perm.mem_alternatingGroup]
    refine perm_three_cube_mem_alternating _ ?_
    have h3 : x ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_three_of_odd h hx.1 hx.2)
    rw [← map_pow]
    have : (⟨x, hx.1⟩ : ↥G₁) ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [this, map_one]
  intro t ht
  obtain ⟨htT, htL⟩ := Subgroup.mem_inf.mp ht
  obtain ⟨⟨t', ht'⟩, ht'A, rfl⟩ := hL htL
  change φ ⟨t', ht'⟩ ∈ alternatingGroup (Fin 3) at ht'A
  rw [Equiv.Perm.mem_alternatingGroup] at ht'A
  have h3 := perm_three_alternating_cube _ ht'A
  obtain ⟨k, hk⟩ := h.isPGroup_inf ⟨t', htT⟩
  have hk' : (⟨t', ht'⟩ : ↥G₁) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  have h2 : φ ⟨t', ht'⟩ ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hd3 : orderOf (φ ⟨t', ht'⟩) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hd2 : orderOf (φ ⟨t', ht'⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have h1 : φ ⟨t', ht'⟩ = 1 := orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd3 hcop) hd2)
  have hmem : (⟨t', ht'⟩ : ↥G₁) ∈ Open.pCore 2 ↥G₁ := by
    rw [← QuotientGroup.eq_one_iff]
    apply e.injective
    rw [map_one]
    exact h1
  exact ⟨⟨t', ht'⟩, hmem, rfl⟩

theorem card_twoResidual_left (h : IsGoldschmidtTriple G₁ G₂) :
    Nat.card ↥(twoResidual G₁) = 3 * Nat.card ↥(G₁ ⊓ G₂ ⊓ twoResidual G₁) := by
  set T := G₁ ⊓ G₂ with hTdef
  set L := twoResidual G₁ with hLdef
  have hTN : T ≤ Subgroup.normalizer (L : Set D) :=
    inf_le_left.trans (le_normalizer_twoResidual G₁)
  have h1 := A4.relIndex_sup_eq_of_le_normalizer' hTN
  rw [inf_sup_twoResidual_left h] at h1
  have ha := Subgroup.relIndex_mul_card (H := L) (K := G₁)
  rw [inf_eq_left.mpr (twoResidual_le G₁)] at ha
  have hb := Subgroup.relIndex_mul_card (H := L) (K := T)
  have hc := card_left h
  rw [inf_comm] at hb
  have hpos : 0 < Nat.card ↥T := Nat.card_pos
  have key : Nat.card ↥T * (3 * Nat.card ↥(T ⊓ L)) = Nat.card ↥T * Nat.card ↥L := by
    calc Nat.card ↥T * (3 * Nat.card ↥(T ⊓ L))
        = 3 * Nat.card ↥T * Nat.card ↥(T ⊓ L) := by ring
      _ = L.relIndex G₁ * Nat.card ↥L * Nat.card ↥(T ⊓ L) := by
          rw [hLdef, ha, hc]
      _ = L.relIndex T * Nat.card ↥(T ⊓ L) * Nat.card ↥L := by rw [h1]; ring
      _ = Nat.card ↥T * Nat.card ↥L := by rw [hb]
  exact (Nat.eq_of_mul_eq_mul_left hpos key).symm

theorem relIndex_inf_twoResidual_left (h : IsGoldschmidtTriple G₁ G₂) :
    (G₁ ⊓ G₂ ⊓ twoResidual G₁).relIndex (twoResidual G₁) = 3 := by
  have h1 := Subgroup.relIndex_mul_card (H := G₁ ⊓ G₂ ⊓ twoResidual G₁) (K := twoResidual G₁)
  rw [inf_eq_left.mpr inf_le_right, card_twoResidual_left h] at h1
  have hpos : 0 < Nat.card ↥(G₁ ⊓ G₂ ⊓ twoResidual G₁) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1])

omit [Finite D] in
theorem exists_mul_zpow_of_relIndex_eq_three {R L : Subgroup D}
    (hRn : L ≤ Subgroup.normalizer (R : Set D)) (h3 : R.relIndex L = 3) {u : D} (hu : u ∈ L)
    (huR : u ∉ R) {x : D} (hx : x ∈ L) : ∃ r ∈ R, ∃ k : ℤ, x = r * u ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : (R.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hRn
  set π := QuotientGroup.mk' (R.subgroupOf L)
  have hcard : Nat.card (↥L ⧸ R.subgroupOf L) = 3 := by
    rw [← Subgroup.index, ← Subgroup.relIndex, h3]
  have hu1 : π ⟨u, hu⟩ ≠ 1 := by
    rw [QuotientGroup.mk'_apply, ne_eq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact huR
  have htop := zpowers_eq_top_of_prime_card hcard hu1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top (π ⟨x, hx⟩))
  refine ⟨x * (u ^ k)⁻¹, ?_, k, by group⟩
  have h1 : π (⟨x, hx⟩ * (⟨u, hu⟩ ^ k)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  simpa using h1

theorem pCoreOf_twoResidual_right_eq (h : IsGoldschmidtTriple G₁ G₂) :
    pCoreOf 2 (twoResidual G₂) = G₂ ⊓ G₁ ⊓ twoResidual G₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRL : pCoreOf 2 (twoResidual G₂) ≤ twoResidual G₂ := pCoreOf_le 2 _
  have hG₂R : G₂ ≤ Subgroup.normalizer (pCoreOf 2 (twoResidual G₂) : Set D) :=
    (le_normalizer_twoResidual G₂).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hRQ : pCoreOf 2 (twoResidual G₂) ≤ pCoreOf 2 G₂ :=
    le_pCoreOf_of_le_normalizer 2 (hRL.trans (twoResidual_le G₂)) hG₂R (pCoreOf_isPGroup 2 _)
  have hTR : G₂ ⊓ G₁ ⊓ twoResidual G₂ ≤ pCoreOf 2 (twoResidual G₂) := by
    have h1 := inf_twoResidual_le_pCoreOf_left h.symm
    have h2 : pCoreOf 2 G₂ ⊓ twoResidual G₂ ≤ pCoreOf 2 (twoResidual G₂) := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        ((pCoreOf_isPGroup 2 G₂).to_le inf_le_left)
      intro g hg
      exact mem_normalizer_inf (le_normalizer_pCoreOf 2 G₂ (twoResidual_le G₂ hg))
        (le_normalizer_twoResidual G₂ (twoResidual_le G₂ hg))
    exact (le_inf h1 inf_le_right).trans h2
  refine le_antisymm (le_inf (le_inf ?_ ?_) hRL) hTR
  · exact hRQ.trans (pCoreOf_le 2 G₂)
  · exact hRQ.trans ((pCoreOf_le_inf_right h).trans inf_le_left)

theorem pCoreOf_twoResidual_le_ker (h : IsGoldschmidtTriple G₁ G₂)
    (ψ : D →* GL (Fin 2) (ZMod 3)) (hR2 : ∀ r ∈ pCoreOf 2 (twoResidual G₂), r ^ 2 = 1)
    (hRc : ∀ r ∈ pCoreOf 2 (twoResidual G₂), ∀ r' ∈ pCoreOf 2 (twoResidual G₂),
      r * r' = r' * r) :
    pCoreOf 2 (twoResidual G₂) ≤ ψ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L₂ := twoResidual G₂ with hL₂def
  set R := pCoreOf 2 L₂ with hRdef
  have hRL : R ≤ L₂ := pCoreOf_le 2 L₂
  have hG₂R : G₂ ≤ Subgroup.normalizer (R : Set D) :=
    (le_normalizer_twoResidual G₂).trans (normalizer_le_normalizer_pCoreOf 2 L₂)
  have hReq : R = G₂ ⊓ G₁ ⊓ L₂ := pCoreOf_twoResidual_right_eq h
  have h3 : R.relIndex L₂ = 3 := by rw [hReq]; exact relIndex_inf_twoResidual_left h.symm
  obtain ⟨u, huG, hu3⟩ := exists_orderOf_eq_three_left h.symm
  have huL : u ∈ L₂ := mem_twoResidual_of_odd huG (by rw [hu3]; decide)
  have huR : u ∉ R := by
    intro hur
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L₂) ⟨u, hur⟩
    have : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 := orderOf_dvd_of_pow_eq_one this
    rw [hu3] at h1
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h1)
    omega
  have hcent : ∀ x ∈ G₂, Odd (orderOf x) → ∀ r ∈ R, ψ x * ψ r = ψ r * ψ x := by
    intro x hx hxo r hr
    refine A1b.GL2.centralizes_of_odd_order (A := R.map ψ) (by norm_num) ?_ ?_ ?_ ?_
      (Subgroup.mem_map_of_mem ψ hr)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, ← pow_two, hR2 a ha, map_one]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hRc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨x * a * x⁻¹, (Subgroup.mem_normalizer_iff.mp (hG₂R hx) a).mp ha, ?_⟩
      simp
    · exact Odd.of_dvd_nat hxo (orderOf_map_dvd ψ x)
  have hu3' : ψ u ^ 3 = 1 := by
    have : u ^ 3 = 1 := hu3 ▸ pow_orderOf_eq_one u
    rw [← map_pow, this, map_one]
  have hL₂ : L₂ ≤ (Subgroup.zpowers (ψ u)).comap ψ := by
    rw [hL₂def, twoResidual_eq_oTwoUpper]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hxL : x ∈ L₂ := mem_twoResidual_of_odd hx.1 hx.2
    obtain ⟨r, hr, k, rfl⟩ := exists_mul_zpow_of_relIndex_eq_three
      (fun g hg => hG₂R (twoResidual_le G₂ hg)) h3 huL huR hxL
    have hx3 : (r * u ^ k) ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_three_of_odd h.symm hx.1 hx.2)
    have hc : Commute (ψ r) (ψ u) := (hcent u huG (by rw [hu3]; decide) r hr).symm
    have hψr : ψ r = 1 := by
      have h1 : (ψ r * ψ u ^ k) ^ 3 = 1 := by
        rw [← map_zpow, ← map_mul, ← map_pow, hx3, map_one]
      have h4 : (ψ u ^ k) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3', one_zpow]
      rw [(hc.zpow_right k).mul_pow, h4, mul_one] at h1
      have h2 : ψ r ^ 2 = 1 := by rw [← map_pow, hR2 r hr, map_one]
      calc ψ r = ψ r ^ 3 * (ψ r ^ 2)⁻¹ := by group
        _ = 1 := by rw [h1, h2, inv_one, mul_one]
    show ψ (r * u ^ k) ∈ Subgroup.zpowers (ψ u)
    rw [map_mul, hψr, one_mul, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  intro r hr
  have h1 := hL₂ (hRL hr)
  rw [Subgroup.mem_comap] at h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  have h3' : ψ r ^ 3 = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3', one_zpow]
  have h2 : ψ r ^ 2 = 1 := by rw [← map_pow, hR2 r hr, map_one]
  rw [MonoidHom.mem_ker]
  calc ψ r = ψ r ^ 3 * (ψ r ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3', h2, inv_one, mul_one]

theorem card_twoResidual_right_of_le (h : IsGoldschmidtTriple G₁ G₂) (hQ : Open.pCore 2 D = ⊥)
    {P : Subgroup D} [P.Normal] (hP : IsPGroup 3 P) {X₀ : Subgroup ↥P} [X₀.Characteristic]
    (hfaith : ∀ α : MulAut ↥P, (orderOf α).Coprime 3 →
      (∀ x ∈ X₀, x⁻¹ * α x ∈ frattiniIn X₀) → α = 1)
    (ψ : D →* GL (Fin 2) (ZMod 3)) (hψ : ψ.ker = (frattiniConj P X₀).ker)
    (hL₁ : twoResidual G₁ ≤ P) : Nat.card ↥(twoResidual G₂) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL₁3 := card_twoResidual_eq_three_of_le h hP hL₁
  obtain ⟨⟨hQel, -⟩, -, hO⟩ := f6_13_three h hQ hL₁3
  have hReq := pCoreOf_twoResidual_right_eq h
  set R := pCoreOf 2 (twoResidual G₂) with hRdef
  have hRQ : R ≤ pCoreOf 2 G₂ := by
    rw [hReq]
    exact inf_twoResidual_le_pCoreOf_left h.symm
  have hR2 : ∀ r ∈ R, r ^ 2 = 1 := fun r hr => by
    have := hQel.2 r (hRQ hr)
    exact this
  have hRc : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r := fun r hr r' hr' => by
    have := hQel.1.1.comm ⟨r, hRQ hr⟩ ⟨r', hRQ hr'⟩
    exact congrArg Subtype.val this
  have hker := pCoreOf_twoResidual_le_ker h ψ hR2 hRc
  have hcent : R ≤ Subgroup.centralizer (P : Set D) := by
    intro r hr
    refine mem_centralizer_of_mem_ker_frattiniConj hfaith (hψ ▸ hker hr) ?_
    have hdvd : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (hR2 r hr)
    exact Nat.Coprime.coprime_dvd_left hdvd (by norm_num)
  have hnorm : pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤ Subgroup.normalizer (R : Set D) := by
    refine sup_le ((pCoreOf_le 2 G₂).trans ?_) ?_
    · exact (le_normalizer_twoResidual G₂).trans (normalizer_le_normalizer_pCoreOf 2 _)
    · intro l hl
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact ((Subgroup.mem_centralizer_iff.mp (hcent hr)) l (hL₁ hl)).symm
  have hR1 : R = ⊥ := hO hnorm
  have h3 := relIndex_inf_twoResidual_left h.symm
  rw [← hReq, hR1, Subgroup.relIndex_bot_left] at h3
  exact h3

theorem isPGroup_three_of_inf_le (h : IsGoldschmidtTriple G₁ G₂) (hO : CFSG.pPrimeCore 3 D = ⊥)
    {K : Subgroup D} [hKn : K.Normal] (h₁ : G₁ ⊓ K ≤ pCoreOf 2 G₁)
    (h₂ : G₂ ⊓ K ≤ pCoreOf 2 G₂)
    (hcent : ∀ k ∈ K, (orderOf k).Coprime 3 →
      k ∈ Subgroup.centralizer (Open.pCore 3 D : Set D)) :
    IsPGroup 3 ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : Open.pCore 2 D = ⊥ := le_bot_iff.mp (hO ▸ pCore_le_pPrimeCore)
  have hodd : Odd (Nat.card ↥K) := by
    have := odd_card_map_of_normal h h₁ h₂
    rwa [card_map_mk, hQ, Subgroup.relIndex_bot_left] at this
  have hsolv : Group.IsSolvable ↥K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hcore : CFSG.pPrimeCore 3 ↥K = ⊥ := by
    have hle : (CFSG.pPrimeCore 3 ↥K).map K.subtype ≤ CFSG.pPrimeCore 3 D := by
      refine le_pPrimeCore_of_normal ?_
      rw [Subgroup.card_map_of_injective K.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    rw [hO] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp (le_bot_iff.mp hle)
  have hF := CFSG.Fitting_eq_pcore ↥K 3 hcore
  have hC := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  rw [hF] at hC
  have hPK : (CFSG.pCore 3 ↥K).map K.subtype ≤ Open.pCore 3 D :=
    CFSG.LieType.BorelTits.le_pCore 3 inferInstance (CFSG.pCore_isPGroup.map _)
  have key : ∀ k : ↥K, (orderOf k).Coprime 3 → k = 1 := by
    intro k hk
    have hkD : ((k : D)) ∈ Subgroup.centralizer (Open.pCore 3 D : Set D) :=
      hcent k k.2 (by rwa [Subgroup.orderOf_coe])
    have hkF : k ∈ CFSG.pCore 3 ↥K := by
      refine hC ?_
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have hfD : (f : D) ∈ Open.pCore 3 D := hPK ⟨f, hf, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hkD _ hfD)
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup ⟨k, hkF⟩
    have hn' : k ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h1 := orderOf_dvd_of_pow_eq_one hn'
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n hk) h1)
  intro k
  obtain ⟨a, b, hab, -, ⟨e, he⟩, hb, -, -⟩ := exists_mul_eq_pPart Nat.prime_three k
  rw [key b hb, mul_one] at hab
  exact ⟨e, hab ▸ he⟩

theorem mat_three_sq_det : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 3), A * A = 1 → A.det = 1 →
    A = 1 ∨ A = -1 := by
  decide +kernel

theorem mat_three_neg_one_cube : (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 3 ≠ 1 := by
  decide +kernel

theorem eq_neg_one_of_sq_eq_one_of_det {A : GL (Fin 2) (ZMod 3)} (h2 : A ^ 2 = 1) (h1 : A ≠ 1)
    (hdet : Matrix.GeneralLinearGroup.det A = 1) : A = -1 := by
  have hA2 : (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) * A = 1 := by
    rw [← Units.val_mul, ← pow_two, h2, Units.val_one]
  have hAd : (A : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  rcases mat_three_sq_det _ hA2 hAd with h | h
  · exact absurd (Units.ext (by rw [h, Units.val_one])) h1
  · exact Units.ext (by rw [h, Units.val_neg, Units.val_one]; rfl)

theorem det_eq_one_of_odd {A : GL (Fin 2) (ZMod 3)} (hA : Odd (orderOf A)) :
    Matrix.GeneralLinearGroup.det A = 1 := by
  have h1 : orderOf (Matrix.GeneralLinearGroup.det A) ∣ orderOf A := orderOf_map_dvd _ A
  have h2 : orderOf (Matrix.GeneralLinearGroup.det A) ∣ 2 := by
    have hc : Nat.card (ZMod 3)ˣ = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card_units]
    have := orderOf_dvd_natCard (Matrix.GeneralLinearGroup.det A)
    rwa [hc] at this
  have hc : Nat.Coprime (orderOf (Matrix.GeneralLinearGroup.det A)) 2 :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.coprime_two_right.mpr hA)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc h2)

theorem exists_orderOf_eq_three_not_mem (h : IsGoldschmidtTriple G₁ G₂) {X : Subgroup D}
    [X.Normal] (hL : ¬ twoResidual G₁ ≤ X) : ∃ x ∈ G₁, orderOf x = 3 ∧ x ∉ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, h3⟩ := exists_orderOf_eq_three_left h
  refine ⟨x, hx, h3, fun hxX => ?_⟩
  have h1 := ((tfae_inf_le_pCoreOf h isSubnormal_top_of_normal).out 3 1).mp hL
  have hxQ := h1 ⟨hx, hxX⟩
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 G₁) ⟨x, hxQ⟩
  have : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 := orderOf_dvd_of_pow_eq_one this
  rw [h3] at h2
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h2)
  omega

theorem zpowers_neg_one_normal : (Subgroup.zpowers (-1 : GL (Fin 2) (ZMod 3))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hc : Commute ((-1 : GL (Fin 2) (ZMod 3)) ^ k) g := (Commute.neg_one_left g).zpow_left k
  rw [← hc.eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers _ k

theorem eq_one_of_mem_zpowers_neg_one {A : GL (Fin 2) (ZMod 3)}
    (hA : A ∈ Subgroup.zpowers (-1 : GL (Fin 2) (ZMod 3))) (h3 : A ^ 3 = 1) : A = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hA
  rcases Int.even_or_odd k with hk | hk
  · exact hk.neg_one_zpow
  · rw [hk.neg_one_zpow] at h3 ⊢
    exfalso
    apply mat_three_neg_one_cube
    have := congrArg Units.val h3
    rwa [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at this

theorem false_of_not_le (h : IsGoldschmidtTriple G₁ G₂) (hO : CFSG.pPrimeCore 3 D = ⊥)
    (ψ : D →* GL (Fin 2) (ZMod 3))
    (hcent : ∀ k ∈ ψ.ker, (orderOf k).Coprime 3 →
      k ∈ Subgroup.centralizer (Open.pCore 3 D : Set D))
    {X : Subgroup D} [X.Normal] (hmem : ∀ u : D, orderOf u = 3 → u ∈ ψ.ker → u ∈ X)
    (h₁ : ¬ twoResidual G₁ ≤ X) (h₂ : ¬ twoResidual G₂ ≤ X)
    (hL : ¬ IsPGroup 3 ↥(twoResidual (⊤ : Subgroup D))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : Open.pCore 2 D = ⊥ := le_bot_iff.mp (hO ▸ pCore_le_pPrimeCore)
  obtain ⟨x₁, hx₁, hx₁3, hx₁X⟩ := exists_orderOf_eq_three_not_mem h h₁
  obtain ⟨x₂, hx₂, hx₂3, hx₂X⟩ := exists_orderOf_eq_three_not_mem h.symm h₂
  have hx₁L : x₁ ∈ twoResidual G₁ := mem_twoResidual_of_odd hx₁ (by rw [hx₁3]; decide)
  have hx₂L : x₂ ∈ twoResidual G₂ := mem_twoResidual_of_odd hx₂ (by rw [hx₂3]; decide)
  have hx₁K : x₁ ∉ ψ.ker := fun h' => hx₁X (hmem x₁ hx₁3 h')
  have hx₂K : x₂ ∉ ψ.ker := fun h' => hx₂X (hmem x₂ hx₂3 h')
  have hKs : IsSubnormal ψ.ker ⊤ := isSubnormal_top_of_normal
  have hK₁ : G₁ ⊓ ψ.ker ≤ pCoreOf 2 G₁ :=
    ((tfae_inf_le_pCoreOf h hKs).out 3 1).mp
      fun (hle : twoResidual G₁ ≤ ψ.ker) => hx₁K (hle hx₁L)
  have hK₂ : G₂ ⊓ ψ.ker ≤ pCoreOf 2 G₂ :=
    ((tfae_inf_le_pCoreOf h.symm hKs).out 3 1).mp
      fun (hle : twoResidual G₂ ≤ ψ.ker) => hx₂K (hle hx₂L)
  have hK3 := isPGroup_three_of_inf_le h hO hK₁ hK₂ hcent
  set L := twoResidual (⊤ : Subgroup D) with hLdef
  have hLψ : ¬ IsPGroup 3 ↥(L.map ψ) := fun h3 =>
    hL ((h3.comap_of_ker_isPGroup ψ hK3).to_le (Subgroup.le_comap_map ψ L))
  have h2 : 2 ∣ Nat.card ↥(L.map ψ) := by
    by_contra h2
    apply hLψ
    have hGL : Nat.card (GL (Fin 2) (ZMod 3)) = 2 ^ 4 * 3 := by
      rw [card_GL_zmod (p := 3) 2]
      simp [Fin.prod_univ_two]
    have hdvd : Nat.card ↥(L.map ψ) ∣ 2 ^ 4 * 3 := by
      rw [← hGL]
      exact Subgroup.card_subgroup_dvd_card _
    have hc : Nat.Coprime (Nat.card ↥(L.map ψ)) (2 ^ 4) :=
      Nat.Coprime.pow_right 4
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
    have h3 : Nat.card ↥(L.map ψ) ∣ 3 := hc.dvd_of_dvd_mul_left hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])
  obtain ⟨A, hA⟩ := exists_prime_orderOf_dvd_card' (G := ↥(L.map ψ)) 2 h2
  obtain ⟨g, hgL, hgA⟩ := A.2
  have hψg2 : orderOf (ψ g) = 2 := by rw [hgA, Subgroup.orderOf_coe, hA]
  have hLdet : L ≤ (Matrix.GeneralLinearGroup.det.comp ψ).ker := by
    rw [hLdef, twoResidual_eq_oTwoUpper]
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    show Matrix.GeneralLinearGroup.det (ψ y) = 1
    exact det_eq_one_of_odd (Odd.of_dvd_nat hy.2 (orderOf_map_dvd ψ y))
  have hψg : ψ g = -1 := by
    refine eq_neg_one_of_sq_eq_one_of_det ?_ ?_ (hLdet hgL)
    · have := pow_orderOf_eq_one (ψ g)
      rwa [hψg2] at this
    · intro h1
      rw [h1, orderOf_one] at hψg2
      omega
  have hZ := zpowers_neg_one_normal
  set N := (Subgroup.zpowers (-1 : GL (Fin 2) (ZMod 3))).comap ψ with hNdef
  have hNn : N.Normal := hZ.comap ψ
  have hNs : IsSubnormal N ⊤ := isSubnormal_top_of_normal
  have hxN : ∀ x : D, orderOf x = 3 → x ∉ ψ.ker → x ∉ N := by
    intro x hx3 hxK hxN
    apply hxK
    rw [MonoidHom.mem_ker]
    refine eq_one_of_mem_zpowers_neg_one hxN ?_
    have : x ^ 3 = 1 := hx3 ▸ pow_orderOf_eq_one x
    rw [← map_pow, this, map_one]
  have hN₁ : G₁ ⊓ N ≤ pCoreOf 2 G₁ :=
    ((tfae_inf_le_pCoreOf h hNs).out 3 1).mp
      fun (hle : twoResidual G₁ ≤ N) => hxN x₁ hx₁3 hx₁K (hle hx₁L)
  have hN₂ : G₂ ⊓ N ≤ pCoreOf 2 G₂ :=
    ((tfae_inf_le_pCoreOf h.symm hNs).out 3 1).mp
      fun (hle : twoResidual G₂ ≤ N) => hxN x₂ hx₂3 hx₂K (hle hx₂L)
  have hodd : Odd (Nat.card ↥N) := by
    have := odd_card_map_of_normal h hN₁ hN₂
    rwa [card_map_mk, hQ, Subgroup.relIndex_bot_left] at this
  have hgN : g ∈ N := by
    show ψ g ∈ Subgroup.zpowers (-1 : GL (Fin 2) (ZMod 3))
    rw [hψg]
    exact Subgroup.mem_zpowers _
  have h2g : 2 ∣ orderOf (⟨g, hgN⟩ : ↥N) := by
    rw [Subgroup.orderOf_mk, ← hψg2]
    exact orderOf_map_dvd ψ g
  have := (Nat.odd_iff.mp hodd)
  have h2N : 2 ∣ Nat.card ↥N := h2g.trans (orderOf_dvd_natCard _)
  omega

theorem isPGroup_twoResidual_of_noncyclic (h : IsGoldschmidtTriple G₁ G₂)
    (hO : CFSG.pPrimeCore 3 D = ⊥) (hm : Open.pRank 3 (⊤ : Subgroup D) ≤ 2)
    (hnc : ¬ IsCyclic ↥(Open.pCore 3 D)) : IsPGroup 3 ↥(twoResidual (⊤ : Subgroup D)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp1 : 1 < 3 := Nat.prime_three.one_lt
  have hQ : Open.pCore 2 D = ⊥ := le_bot_iff.mp (hO ▸ pCore_le_pPrimeCore)
  set P := Open.pCore 3 D with hPdef
  have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal 3
  have hP : IsPGroup 3 ↥P := CFSG.LieType.BorelTits.pCore_isPGroup 3
  have hPr2 : Open.pRank 3 (⊤ : Subgroup ↥P) ≤ 2 := by
    refine (pRank_le_map hp1 P.subtype P.subtype_injective ⊤).trans ?_
    exact (pRank_mono hp1 le_top).trans hm
  have hnc' : ¬ IsCyclic ↥(⊤ : Subgroup ↥P) := fun hc =>
    hnc (isCyclic_of_surjective (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥P) ≃* ↥P).toMonoidHom
      (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥P) ≃* ↥P).surjective)
  have hPr1 : 1 < Open.pRank 3 (⊤ : Subgroup ↥P) := by
    obtain ⟨E, -, hE, hEc⟩ := A1c.exists_isElemAbelian_card_sq (p := 3) (by norm_num)
      (hP.to_subgroup ⊤) hnc'
    have := CFSG.SectionRank.le_pRank hp1 le_top hE hEc
    omega
  have hPnt : Nontrivial ↥P := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hnc isCyclic_of_subsingleton
  obtain ⟨X₀, hX, hfaith⟩ := exists_isSupercritical_faithful (p := 3) (by norm_num) hP
  have : X₀.Characteristic := hX.characteristic
  have hXrank := hX.pRank_eq hP hPr2
  have hX2 : Open.pRank 3 X₀ = 2 := by omega
  obtain ⟨E₀, hE₀X, hE₀, hE₀c⟩ := exists_pRank hp1 X₀
  rw [hX2] at hE₀c
  have hE : IsElemAbelian 3 (E₀.map P.subtype) := isElemAbelian_map hE₀ _
  have hEc : Nat.card ↥(E₀.map P.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hE₀c]
  have hEX : E₀.map P.subtype ≤ X₀.map P.subtype := Subgroup.map_mono hE₀X
  have hcases : (∀ a b : ↥X₀, a * b = b * a) ∨ IsPOnePlusTwo 3 ↥X₀ := by
    rcases hX.iso_cases (by norm_num) hP hPr2 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | h12
    · exact Or.inl fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])
    · exact Or.inl fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])
    · exact Or.inr h12
  have hexp : ∀ x ∈ X₀, x ^ 3 = 1 := hX.pow_eq_one
  have hXr : Open.pRank 3 (⊤ : Subgroup ↥X₀) ≤ 2 := by rw [pRank_top_subtype, hX2]
  obtain ⟨ψ, hψ⟩ := exists_hom_GL_ker_eq hP hexp hXr
  set X := X₀.map P.subtype with hXdef
  have hXP : X ≤ P := Subgroup.map_subtype_le X₀
  have hX3 : IsPGroup 3 ↥X := (hP.to_subgroup X₀).map P.subtype
  have hcent : ∀ k ∈ ψ.ker, (orderOf k).Coprime 3 →
      k ∈ Subgroup.centralizer (P : Set D) := fun k hk hc =>
    mem_centralizer_of_mem_ker_frattiniConj hfaith (hψ ▸ hk) hc
  have hmem : ∀ u : D, orderOf u = 3 → u ∈ ψ.ker → u ∈ X := fun u hu huk =>
    mem_of_mem_ker_frattiniConj hexp hcases hE hEX hEc hm hu (hψ ▸ huk)
  by_contra hL
  by_cases hX₁ : twoResidual G₁ ≤ X
  · apply hL
    have h2 := card_twoResidual_right_of_le h hQ hP hfaith ψ hψ (hX₁.trans hXP)
    have hL₂3 : IsPGroup 3 ↥(twoResidual G₂) := IsPGroup.of_card (n := 1) (by rw [h2, pow_one])
    rw [twoResidual_top_eq h]
    exact (hX3.to_sup_of_normal_left hL₂3).to_le (sup_le_sup_right hX₁ _)
  by_cases hX₂ : twoResidual G₂ ≤ X
  · apply hL
    have h2 := card_twoResidual_right_of_le h.symm hQ hP hfaith ψ hψ (hX₂.trans hXP)
    have hL₁3 : IsPGroup 3 ↥(twoResidual G₁) := IsPGroup.of_card (n := 1) (by rw [h2, pow_one])
    rw [twoResidual_top_eq h.symm]
    exact (hX3.to_sup_of_normal_left hL₁3).to_le (sup_le_sup_right hX₂ _)
  exact false_of_not_le h hO ψ hcent hmem hX₁ hX₂ hL

end Vertex

end F6

end CFSG.Quasithin
