module

public import CFSG.GroupTheory.OddOrderClosure

public section

namespace CFSG.RankThree.GF2n.Stroth78.Sec4PSU

open CFSG.Open (IsElemAbelian pCoreOf)

variable {G : Type*} [Group G]

theorem pCoreOf_two_le (H : Subgroup G) : pCoreOf 2 H ≤ H := by
  rw [pCoreOf]
  exact Subgroup.map_subtype_le _

theorem isPGroup_pCoreOf_two (H : Subgroup G) : IsPGroup 2 (pCoreOf 2 H) := by
  rw [pCoreOf]
  exact CFSG.pCore_isPGroup.map _

theorem le_normalizer_pCoreOf_two (H : Subgroup G) :
    H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
  have key : ∀ k ∈ H, ∀ o ∈ pCoreOf 2 H, k * o * k⁻¹ ∈ pCoreOf 2 H := by
    intro k hk o ho
    rw [pCoreOf] at ho ⊢
    obtain ⟨o', ho', rfl⟩ := ho
    exact ⟨⟨k, hk⟩ * o' * ⟨k, hk⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro o
  refine ⟨key g hg o, fun h => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem le_pCoreOf_two_of_le_normalizer {N H : Subgroup G} (hNH : N ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (N : Set G)) (hp : IsPGroup 2 N) : N ≤ pCoreOf 2 H := by
  have hN : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hnorm
  have hsub : IsPGroup 2 (N.subgroupOf H) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hcore : N.subgroupOf H ≤ CFSG.pCore 2 ↥H := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (N.subgroupOf H) (le_iSup_of_le hN (le_iSup_of_le hsub le_rfl))
  rw [pCoreOf, ← Subgroup.map_subgroupOf_eq_of_le hNH]
  exact Subgroup.map_mono hcore

theorem mem_zpowers_iff_of_mul_self {w g : G} (hw : w * w = 1) (hw1 : w ≠ 1) :
    g ∈ Subgroup.zpowers w ↔ g = 1 ∨ g = w := by
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hord : orderOf w = 2 := orderOf_eq_prime (by rw [sq, hw]) hw1
    rw [← zpow_mod_orderOf, hord]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

theorem normalizer_zpowers_of_mul_self {w : G} (hw : w * w = 1) (hw1 : w ≠ 1) :
    Subgroup.normalizer (Subgroup.zpowers w : Set G) = Subgroup.centralizer {w} := by
  ext g
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rcases (mem_zpowers_iff_of_mul_self hw hw1).1 ((h _).1 (Subgroup.mem_zpowers _)) with h1 | h1
    · exfalso
      apply hw1
      have := congrArg (fun x => g⁻¹ * x * g) h1
      simpa [mul_assoc] using this
    · calc g * w = g * w * g⁻¹ * g := by group
        _ = w * g := by rw [h1]
  · intro hg x
    have hcomm : ∀ y : G, y = 1 ∨ y = w → g * y * g⁻¹ = y := by
      intro y hy
      rcases hy with h | h
      · rw [h]
        group
      · rw [h, hg, mul_inv_cancel_right]
    have hcomm' : ∀ y : G, y = 1 ∨ y = w → g⁻¹ * y * g = y := by
      intro y hy
      rcases hy with h | h
      · rw [h]
        group
      · rw [h]
        calc g⁻¹ * w * g = g⁻¹ * (w * g) := by group
          _ = g⁻¹ * (g * w) := by rw [hg]
          _ = w := by group
    constructor
    · intro hx
      rw [hcomm x ((mem_zpowers_iff_of_mul_self hw hw1).1 hx)]
      exact hx
    · intro hx
      have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [e, hcomm' _ ((mem_zpowers_iff_of_mul_self hw hw1).1 hx)]
      exact hx

variable {G' : Type*} [Group G'] (φ : G →* G')

theorem eq_one_of_mem_ker_of_pow (hodd : ∀ ζ ∈ φ.ker, Odd (orderOf ζ)) {ζ : G}
    (hζ : ζ ∈ φ.ker) {k : ℕ} (hk : ζ ^ 2 ^ k = 1) : ζ = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have ho := hodd ζ hζ
  rw [hj] at ho
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.1 hj
  · exfalso
    rw [pow_succ, Nat.odd_mul] at ho
    exact (Nat.not_even_iff_odd.2 ho.2) even_two

theorem eq_one_of_mem_ker_of_isPGroup (hodd : ∀ ζ ∈ φ.ker, Odd (orderOf ζ)) {S : Subgroup G}
    (hS : IsPGroup 2 S) {x : G} (hxS : x ∈ S) (hx : φ x = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨x, hxS⟩
  exact eq_one_of_mem_ker_of_pow φ hodd hx (k := k) (by simpa using congrArg Subtype.val hk)

theorem centralizer_map_eq (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (hodd : ∀ ζ ∈ φ.ker, Odd (orderOf ζ)) {z : G} (hz : z * z = 1) :
    Subgroup.centralizer {φ z} = (Subgroup.centralizer {z}).map φ := by
  apply le_antisymm
  · intro y hy
    obtain ⟨g, rfl⟩ := hφ y
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    set ζ := g * z * g⁻¹ * z⁻¹ with hζdef
    have hζ : ζ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hζdef, map_mul, map_mul, map_mul, map_inv, map_inv, hy]
      group
    have hzζ : z * ζ = ζ * z := Subgroup.mem_center_iff.1 (hker hζ) z
    have hgz : g * z * g⁻¹ = ζ * z := by
      rw [hζdef]
      group
    have hsq : ζ ^ 2 ^ 1 = 1 := by
      have e1 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
        calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
          _ = 1 := by rw [hz]; group
      rw [hgz] at e1
      calc ζ ^ 2 ^ 1 = ζ * ζ * (z * z) := by rw [hz, mul_one, pow_one, sq]
        _ = ζ * (z * ζ) * z := by rw [hzζ]; group
        _ = ζ * z * (ζ * z) := by group
        _ = 1 := e1
    have h1 := eq_one_of_mem_ker_of_pow φ hodd hζ hsq
    have hgzc : g * z = z * g := by
      have : g * z * g⁻¹ = z := by rw [hgz, h1, one_mul]
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [this]
    exact ⟨g, Subgroup.mem_centralizer_singleton_iff.2 hgzc, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    have hg' := Subgroup.mem_centralizer_singleton_iff.1 hg
    exact Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, hg', map_mul])

theorem exists_twoPart [Finite G] (hker : φ.ker ≤ Subgroup.center G) {H : Subgroup G}
    (hH : IsPGroup 2 (H.map φ)) :
    ∃ S : Subgroup G, S ≤ H ∧ IsPGroup 2 S ∧ S.map φ = H.map φ ∧
      ∀ h ∈ H, (∃ k : ℕ, h ^ 2 ^ k = 1) → h ∈ S := by
  classical
  set ψ₀ : ↥H →* G' := φ.comp H.subtype with hψ₀
  have hrange : ψ₀.range = H.map φ := by
    rw [hψ₀, MonoidHom.range_comp, Subgroup.range_subtype]
  set ψ : ↥H →* ↥ψ₀.range := ψ₀.rangeRestrict with hψ
  have hψs : Function.Surjective ψ := MonoidHom.rangeRestrict_surjective _
  have hR2 : IsPGroup 2 ψ₀.range := by
    rw [hrange]
    exact hH
  haveI : Finite ↥ψ₀.range := Finite.of_surjective ψ hψs
  haveI : Group.IsNilpotent ↥ψ₀.range := hR2.isNilpotent
  have hkerψ : ψ.ker ≤ Subgroup.center ↥H := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : (x : G) ∈ φ.ker := by
      rw [MonoidHom.mem_ker] at hx ⊢
      have := congrArg Subtype.val hx
      simpa [hψ, hψ₀] using this
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker hx') y)
  haveI : Group.IsNilpotent ↥H := isNilpotent_of_ker_le_center ψ hkerψ
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥H) := Sylow.nonempty
  letI : Unique (Sylow 2 ↥H) := Sylow.unique_of_normal P inferInstance
  refine ⟨(P : Subgroup ↥H).map H.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_, ?_⟩
  · apply le_antisymm
    · exact Subgroup.map_mono (Subgroup.map_subtype_le _)
    · have htop : (P.mapSurjective hψs : Subgroup ↥ψ₀.range) = ⊤ := by
        have h2top : IsPGroup 2 (⊤ : Subgroup ↥ψ₀.range) := fun g => by
          obtain ⟨k, hk⟩ := hR2 g.1
          exact ⟨k, Subtype.ext (by simpa using hk)⟩
        exact ((P.mapSurjective hψs).is_maximal' h2top le_top).symm
      intro y hy
      have hy' : y ∈ ψ₀.range := by
        rw [hrange]
        exact hy
      have hmem : (⟨y, hy'⟩ : ↥ψ₀.range) ∈ (P.mapSurjective hψs : Subgroup ↥ψ₀.range) := by
        rw [htop]
        trivial
      rw [Sylow.coe_mapSurjective] at hmem
      obtain ⟨x, hxP, hxy⟩ := hmem
      refine ⟨H.subtype x, ⟨x, hxP, rfl⟩, ?_⟩
      have := congrArg Subtype.val hxy
      simpa [hψ, hψ₀] using this
  · rintro h hh ⟨k, hk⟩
    have hk' : (⟨h, hh⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    have h2 : IsPGroup 2 (Subgroup.zpowers (⟨h, hh⟩ : ↥H)) := by
      rintro ⟨y, hy⟩
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      refine ⟨k, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk', one_zpow]
    obtain ⟨Q, hQ⟩ := h2.exists_le_sylow
    have hQP : Q = P := Subsingleton.elim _ _
    exact ⟨⟨h, hh⟩, hQP ▸ hQ (Subgroup.mem_zpowers _), rfl⟩

theorem pCoreOf_centralizer_le_map [Finite G] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) (hodd : ∀ ζ ∈ φ.ker, Odd (orderOf ζ)) {z : G}
    (hz : z * z = 1) :
    pCoreOf 2 (Subgroup.centralizer {φ z}) ≤ (pCoreOf 2 (Subgroup.centralizer {z})).map φ := by
  have hC := centralizer_map_eq φ hφ hker hodd hz
  set C := Subgroup.centralizer {z} with hCdef
  set P' := pCoreOf 2 (Subgroup.centralizer {φ z}) with hP'
  set H := P'.comap φ ⊓ C with hH
  have hHmap : H.map φ = P' := by
    apply le_antisymm
    · rintro _ ⟨h, ⟨hP, -⟩, rfl⟩
      exact hP
    · intro y hy
      have hyC : y ∈ C.map φ := hC ▸ pCoreOf_two_le _ hy
      obtain ⟨c, hcC, rfl⟩ := hyC
      exact ⟨c, ⟨hy, hcC⟩, rfl⟩
  obtain ⟨S, hSH, hS2, hSmap, hSall⟩ := exists_twoPart φ hker (H := H)
    (by rw [hHmap]; exact isPGroup_pCoreOf_two _)
  have hconj : ∀ c ∈ C, ∀ s ∈ S, c * s * c⁻¹ ∈ S := by
    intro c hc s hs
    have hsH := hSH hs
    have hφc : φ c ∈ Subgroup.centralizer {φ z} := hC ▸ ⟨c, hc, rfl⟩
    have hmemH : c * s * c⁻¹ ∈ H := by
      refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hc (Subgroup.mem_inf.1 hsH).2) (inv_mem hc)⟩
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf_two _ hφc) _).1
        (Subgroup.mem_inf.1 hsH).1
    obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
    refine hSall _ hmemH ⟨k, ?_⟩
    rw [conj_pow, show s ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk, mul_one,
      mul_inv_cancel]
  have hSO : S ≤ pCoreOf 2 C := by
    refine le_pCoreOf_two_of_le_normalizer (hSH.trans inf_le_right) (fun c hc => ?_) hS2
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨hconj c hc s, fun h => ?_⟩
    have := hconj c⁻¹ (inv_mem hc) _ h
    simpa [mul_assoc] using this
  rw [← hHmap, ← hSmap]
  exact Subgroup.map_mono hSO

theorem map_coreProperties [Finite G] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) (hodd : ∀ ζ ∈ φ.ker, Odd (orderOf ζ)) {z : G}
    (hz : z * z = 1) (hz1 : z ≠ 1) {W : Subgroup G}
    (h1 : W ≤ ⁅⁅Subgroup.centralizer {z}, Subgroup.centralizer {z}⁆,
      ⁅Subgroup.centralizer {z}, Subgroup.centralizer {z}⁆⁆)
    (h2 : CFSG.GroupTheory.oddOrderClosure W = W)
    (h3 : pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers z : Set G)) ≤ W)
    (h4 : ∀ E : Subgroup G, IsElemAbelian 2 E → Subgroup.zpowers z ≤ E →
      E ≤ Subgroup.centralizer {z} → (∀ x ∈ W, ∀ e ∈ E, x * e * x⁻¹ ∈ E) →
        E = Subgroup.zpowers z)
    (h5 : ∀ s ∈ pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers z : Set G)),
      (∀ x ∈ W, x⁻¹ * s⁻¹ * x * s ∈ Subgroup.zpowers z) → s ∈ Subgroup.zpowers z) :
    W.map φ ≤ ⁅⁅Subgroup.centralizer {φ z}, Subgroup.centralizer {φ z}⁆,
        ⁅Subgroup.centralizer {φ z}, Subgroup.centralizer {φ z}⁆⁆ ∧
      CFSG.GroupTheory.oddOrderClosure (W.map φ) = W.map φ ∧
      pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers (φ z) : Set G')) ≤ W.map φ ∧
      (∀ E : Subgroup G', IsElemAbelian 2 E → Subgroup.zpowers (φ z) ≤ E →
        E ≤ Subgroup.centralizer {φ z} → (∀ x ∈ W.map φ, ∀ e ∈ E, x * e * x⁻¹ ∈ E) →
          E = Subgroup.zpowers (φ z)) ∧
      (∀ s ∈ pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers (φ z) : Set G')),
        (∀ x ∈ W.map φ, x⁻¹ * s⁻¹ * x * s ∈ Subgroup.zpowers (φ z)) →
          s ∈ Subgroup.zpowers (φ z)) := by
  have hφz : φ z * φ z = 1 := by rw [← map_mul, hz, map_one]
  have hφz1 : φ z ≠ 1 := fun h =>
    hz1 (eq_one_of_mem_ker_of_pow φ hodd h (k := 1) (by rw [pow_one, sq, hz]))
  have hC := centralizer_map_eq φ hφ hker hodd hz
  have hN := normalizer_zpowers_of_mul_self hz hz1
  have hN' := normalizer_zpowers_of_mul_self hφz hφz1
  have hzp : (Subgroup.zpowers z).map φ = Subgroup.zpowers (φ z) := MonoidHom.map_zpowers φ z
  set C := Subgroup.centralizer {z} with hCdef
  have hle : ∀ K : Subgroup G, ⁅K, K⁆ ≤ K := fun K =>
    Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hWC : W ≤ C := h1.trans ((hle _).trans (hle _))
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hZ2 : IsPGroup 2 (Subgroup.zpowers z) := by
    rintro ⟨y, hy⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hy2 : y ^ 2 = 1 := by
      rcases (mem_zpowers_iff_of_mul_self hz hz1).1 hy with h | h
      · rw [h, one_pow]
      · rw [h, sq, hz]
    simpa using hy2
  have hZO : Subgroup.zpowers z ≤ pCoreOf 2 C := by
    refine le_pCoreOf_two_of_le_normalizer ((Subgroup.zpowers_le).2 hzC) ?_ hZ2
    rw [← hN]
  have hO := pCoreOf_centralizer_le_map φ hφ hker hodd hz
  have hlift : ∀ E : Subgroup G', E ≤ Subgroup.centralizer {φ z} →
      (E.comap φ ⊓ C).map φ = E := by
    intro E hE
    apply le_antisymm
    · rintro _ ⟨h, ⟨hP, -⟩, rfl⟩
      exact hP
    · intro y hy
      have hyC : y ∈ C.map φ := hC ▸ hE hy
      obtain ⟨c, hcC, rfl⟩ := hyC
      exact ⟨c, ⟨hy, hcC⟩, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hC, ← Subgroup.map_commutator, ← Subgroup.map_commutator]
    exact Subgroup.map_mono h1
  · refine le_antisymm (CFSG.GroupTheory.oddOrderClosure_le _) ?_
    calc W.map φ = (CFSG.GroupTheory.oddOrderClosure W).map φ := by rw [h2]
      _ ≤ _ := CFSG.GroupTheory.map_oddOrderClosure_le φ W
  · rw [hN']
    refine hO.trans (Subgroup.map_mono ?_)
    rw [← normalizer_zpowers_of_mul_self hz hz1]
    exact h3
  · intro E hE hzE hEC hWE
    set H := E.comap φ ⊓ C with hH
    have hHmap := hlift E hEC
    have hE2 : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact hE.2 g g.2)⟩
    obtain ⟨S, hSH, hS2, hSmap, hSall⟩ := exists_twoPart φ hker (H := H) (by rw [hHmap]; exact hE2)
    have hφS : ∀ s ∈ S, φ s ∈ E := fun s hs => (Subgroup.mem_inf.1 (hSH hs)).1
    have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
      intro a ha b hb
      have h0 : a * b * a⁻¹ * b⁻¹ = 1 := by
        refine eq_one_of_mem_ker_of_isPGroup φ hodd hS2
          (mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) ?_
        have hc := congrArg Subtype.val (hE.1.is_comm.comm ⟨φ a, hφS a ha⟩ ⟨φ b, hφS b hb⟩)
        simp only [MulMemClass.mk_mul_mk] at hc
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
        group
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h0, one_mul]
    have hsq : ∀ a ∈ S, a ^ 2 = 1 := fun a ha =>
      eq_one_of_mem_ker_of_isPGroup φ hodd hS2 (pow_mem ha 2)
        (by rw [map_pow]; exact hE.2 _ (hφS a ha))
    have hSel : IsElemAbelian 2 S :=
      ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, hsq⟩
    have hzS : Subgroup.zpowers z ≤ S := by
      rw [Subgroup.zpowers_le]
      exact hSall z (Subgroup.mem_inf.2 ⟨hzE (Subgroup.mem_zpowers _), hzC⟩)
        ⟨1, by rw [pow_one, sq, hz]⟩
    have hSC : S ≤ C := hSH.trans inf_le_right
    have hWS : ∀ x ∈ W, ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
      intro x hx s hs
      have hxC := hWC hx
      have hmem : x * s * x⁻¹ ∈ H := by
        refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hxC (hSC hs)) (inv_mem hxC)⟩
        rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
        exact hWE (φ x) ⟨x, hx, rfl⟩ (φ s) (hφS s hs)
      obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
      refine hSall _ hmem ⟨k, ?_⟩
      rw [conj_pow, show s ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk, mul_one,
        mul_inv_cancel]
    have hSeq := h4 S hSel hzS hSC hWS
    rw [← hHmap, ← hSmap, hSeq, hzp]
  · intro s' hs' hc'
    rw [hN'] at hs'
    obtain ⟨s, hsO, rfl⟩ := hO hs'
    have hs : s ∈ Subgroup.zpowers z := by
      refine h5 s (by rw [hN]; exact hsO) fun x hx => ?_
      have hx' := hc' (φ x) ⟨x, hx, rfl⟩
      rw [← hzp] at hx'
      obtain ⟨y, hy, hyeq⟩ := hx'
      have hxC := hWC hx
      have ht : x⁻¹ * s⁻¹ * x * s ∈ pCoreOf 2 C := by
        refine mul_mem ?_ hsO
        have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf_two C (inv_mem hxC))
          s⁻¹).1 (inv_mem hsO)
        simpa using this
      have h0 : y⁻¹ * (x⁻¹ * s⁻¹ * x * s) = 1 :=
        eq_one_of_mem_ker_of_isPGroup φ hodd (isPGroup_pCoreOf_two C)
          (mul_mem (inv_mem (hZO hy)) ht) (by
            rw [map_mul, map_inv, hyeq, map_mul, map_mul, map_mul, map_inv, map_inv]
            group)
      have : x⁻¹ * s⁻¹ * x * s = y := by
        calc x⁻¹ * s⁻¹ * x * s = y * (y⁻¹ * (x⁻¹ * s⁻¹ * x * s)) := by group
          _ = y := by rw [h0, mul_one]
      rw [this]
      exact hy
    rw [← hzp]
    exact ⟨s, hs, rfl⟩

end CFSG.RankThree.GF2n.Stroth78.Sec4PSU
