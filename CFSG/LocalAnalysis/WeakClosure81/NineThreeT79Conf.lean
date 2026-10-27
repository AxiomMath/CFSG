module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Quot
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCoreLift
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Config

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}
variable {Y : Type} [Group Y]

theorem nine3_config (h : Nine3T79Setup V T A K S X p g x) {ρ : ↥K →* Equiv.Perm (ZMod p)}
    (hρ : Nine3FibreAct K S p x ρ) {π : ↥(nineH0 V K g) →* Y}
    (hπ : Nine3QuotHyp (nineH0 V K g) π) :
    ∃ (U : Subgroup G) (c : ZMod p) (a e a' v : ↥(nineH0 V K g)),
      U ∈ omegaIn V K (nineE V K) ∧ Nine3Fib K p ρ U c ∧ c ≠ 0 ∧
      (a : G) ∈ A ∧ (a : G) ∉ pCoreOf 2 K ∧ (e : G) ∈ U ∧ (e : G) ∉ pCoreOf 2 K ∧
      (v : G) ∈ V ∧ Nine3Config (π v) (π a) (π e) (π a') (π v) := by
  have hc : Nine3Choice V T A K S X p g x := h.hc
  have hc' : Nine3Choice V T A K S X p g⁻¹ x := h.hc'
  have hI : Nine3IFacts V K S := h.hI
  have h35 : Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5 := h.h35
  have hN : nineH0 V K g ≤ normalizer (nineI0 V K g : Set G) := h.hN
  haveI : Fact p.Prime := ⟨hc.core.hyp.base.prime⟩
  have hp3 : p = 3 := nine3_p_eq_three hc hI h35
  have hAΩ : A ∈ omegaIn V K (nineE V K) :=
    ⟨hc.core.A_mem_nineOmegaIn.1, hc.core.nineOmegaIn_le_K hc.core.A_mem_nineOmegaIn⟩
  have hA0 : Nine3Fib K p ρ A 0 := (nine3_fib_zero_iff hc hρ hAΩ).mpr hc.core.A_mem_nineOmegaIn.2
  have hVle : V ≤ nineH0 V K g := nine3_V_le_H0 hc
  have hV0 : V ∈ nine3Dcal V (nineH0 V K g) :=
    ⟨1, (nineH0 V K g).one_mem, (CFSG.Quasithin.conjSubgroup_one V).symm⟩
  obtain ⟨U, hUΩ, hUfib⟩ := nine3_exists_fib_over hc hρ (1 : ZMod p)
  have hUc0 : (1 : ZMod p) ≠ 0 := one_ne_zero
  obtain ⟨e, heU, heR⟩ : ∃ e ∈ U, e ∉ pCoreOf 2 K := by
    obtain ⟨-, -, -, hnle⟩ := mem_omegaSet.mp hUΩ.1
    exact SetLike.not_le_iff_exists.mp hnle
  obtain ⟨a, haA, haR⟩ : ∃ a ∈ A, a ∉ pCoreOf 2 K := by
    obtain ⟨-, -, -, hnle⟩ := mem_omegaSet.mp hAΩ.1
    exact SetLike.not_le_iff_exists.mp hnle
  have hcard2 : 2 ≤ Nat.card ↥(nineOmegaIn V K S) := by
    obtain ⟨n, hn1, hn2⟩ := Nine3Core.card_nineOmegaIn hc.core
    have h2n : 2 ^ n = 2 ∨ 2 ^ n = 4 := by
      rcases h35 with h3 | h5
      · left; omega
      · right; omega
    rw [hn1]
    rcases h2n with h | h <;> omega
  obtain ⟨A', hA'mem, hA'ne⟩ : ∃ A' ∈ nineOmegaIn V K S, A' ≠ A := by
    have hgt1 : 1 < (nineOmegaIn V K S).ncard := by
      rw [← Nat.card_coe_set_eq]; omega
    exact Set.exists_ne_of_one_lt_ncard hgt1 A
  have hA'Ω : A' ∈ omegaIn V K (nineE V K) :=
    ⟨hA'mem.1, hc.core.nineOmegaIn_le_K hA'mem⟩
  have hA'0 : Nine3Fib K p ρ A' 0 := (nine3_fib_zero_iff hc hρ hA'Ω).mpr hA'mem.2
  have hA'leH : A' ≤ nineH V K := le_iSup₂_of_le A' hA'Ω le_rfl
  have hA'dcal : A' ∈ nine3Dcal V (nineH0 V K g) := (nine3_omega_le_dcal h hA'Ω).1
  have hA'delta : A' ∈ nineDelta V S := (hc.core.mem_nineDelta_iff).mpr (Or.inr hA'mem)
  have hA'ginv_mem : conjSubgroup A' g⁻¹ ∈ nineOmegaIn V K S := by
    have hginv : g⁻¹ ∈ nineDeltaStab V S := (nineDeltaStab V S).inv_mem hc.g_mem
    have hdelta : conjSubgroup A' g⁻¹ ∈ nineDelta V S := (mem_nineDeltaStab.mp hginv A').mp hA'delta
    refine ((hc.core.mem_nineDelta_iff).mp hdelta).resolve_left ?_
    intro heq
    apply hA'ne
    have h1 : A' = conjSubgroup (conjSubgroup A' g⁻¹) g := by
      rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
        CFSG.Quasithin.conjSubgroup_one]
    rw [h1, heq, hc.V_g]
  have hA'ginv_Ω : conjSubgroup A' g⁻¹ ∈ omegaIn V K (nineE V K) :=
    ⟨hA'ginv_mem.1, hc.core.nineOmegaIn_le_K hA'ginv_mem⟩
  have hA'notleR : ¬ A' ≤ pCoreOf 2 K := by
    obtain ⟨-, -, -, hnle⟩ := mem_omegaSet.mp hA'Ω.1
    exact hnle
  have hA'notleRg : ¬ A' ≤ conjSubgroup (pCoreOf 2 K) g := by
    intro hle
    obtain ⟨y, hyA'g, hyR⟩ : ∃ y ∈ conjSubgroup A' g⁻¹, y ∉ pCoreOf 2 K := by
      obtain ⟨-, -, -, hnle⟩ := mem_omegaSet.mp hA'ginv_Ω.1
      exact SetLike.not_le_iff_exists.mp hnle
    have hyconj : g⁻¹ * y * g ∈ A' := by simpa using mem_conjSubgroup_iff.mp hyA'g
    have hyRg : g⁻¹ * y * g ∈ conjSubgroup (pCoreOf 2 K) g := hle hyconj
    have hy : y ∈ pCoreOf 2 K := by
      have hh := mem_conjSubgroup_iff.mp hyRg
      simpa [mul_assoc] using hh
    exact hyR hy
  obtain ⟨a', ha'A', ha'R, ha'Rg⟩ : ∃ a' ∈ A', a' ∉ pCoreOf 2 K ∧
      a' ∉ conjSubgroup (pCoreOf 2 K) g := by
    by_contra hcon
    have hcon' : ∀ x, x ∈ A' → x ∈ pCoreOf 2 K ∨ x ∈ conjSubgroup (pCoreOf 2 K) g := by
      intro x hx
      by_contra h
      push Not at h
      exact hcon ⟨x, hx, h.1, h.2⟩
    have hcover : (A' : Set G) ⊆
        ((A' ⊓ pCoreOf 2 K : Subgroup G) : Set G) ∪
          ((A' ⊓ conjSubgroup (pCoreOf 2 K) g : Subgroup G) : Set G) := by
      intro x hx
      rcases hcon' x hx with h1 | h1
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr ⟨hx, h1⟩
    rcases (SubgroupClass.subset_union.mp hcover) with hle | hle
    · exact hA'notleR (le_trans hle inf_le_right)
    · exact hA'notleRg (le_trans hle inf_le_right)
  obtain ⟨v, hvV, hvO0⟩ : ∃ v ∈ V, v ∉ pCoreOf 2 (nineH0 V K g) :=
    SetLike.not_le_iff_exists.mp (nine3_dcal_not_le_pCore h hV0).1
  have hHnorm : nineH V K ≤
      Subgroup.normalizer ((pCoreOf 2 (nineH0 V K g) ⊓ nineH V K : Subgroup G) : Set G) :=
    (le_inf ((le_sup_left : nineH V K ≤ nineH0 V K g).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (nineH0 V K g)))
      Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hO2H0H_le : pCoreOf 2 (nineH0 V K g) ⊓ nineH V K ≤ pCoreOf 2 (nineH V K) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hHnorm
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (nineH0 V K g)).to_le inf_le_left)
  have hDinf_le_R : ∀ D : Subgroup G, D ≤ nineH V K →
      D ⊓ pCoreOf 2 (nineH0 V K g) ≤ pCoreOf 2 K := by
    intro D hDH
    calc D ⊓ pCoreOf 2 (nineH0 V K g)
        ≤ nineH V K ⊓ pCoreOf 2 (nineH0 V K g) := inf_le_inf hDH le_rfl
      _ = pCoreOf 2 (nineH0 V K g) ⊓ nineH V K := inf_comm _ _
      _ ≤ pCoreOf 2 (nineH V K) := hO2H0H_le
      _ ≤ pCoreOf 2 K := pCoreOf_nineH_le_pCoreOf V K
  have haO0 : a ∉ pCoreOf 2 (nineH0 V K g) := fun hmem =>
    haR (hDinf_le_R A (le_iSup₂_of_le A hAΩ le_rfl)
      (Subgroup.mem_inf.mpr ⟨haA, hmem⟩))
  have heO0 : e ∉ pCoreOf 2 (nineH0 V K g) := fun hmem =>
    heR (hDinf_le_R U (le_iSup₂_of_le U hUΩ le_rfl)
      (Subgroup.mem_inf.mpr ⟨heU, hmem⟩))
  have ha'O0 : a' ∉ pCoreOf 2 (nineH0 V K g) := fun hmem =>
    ha'R (hDinf_le_R A' hA'leH (Subgroup.mem_inf.mpr ⟨ha'A', hmem⟩))
  have hA_le_nineH : A ≤ nineH V K := le_iSup₂_of_le A hAΩ le_rfl
  have hA_le_H0 : A ≤ nineH0 V K g := hA_le_nineH.trans le_sup_left
  have hU_le_nineH : U ≤ nineH V K := le_iSup₂_of_le U hUΩ le_rfl
  have hU_le_H0 : U ≤ nineH0 V K g := hU_le_nineH.trans le_sup_left
  let aH : ↥(nineH0 V K g) := ⟨a, hA_le_H0 haA⟩
  let eH : ↥(nineH0 V K g) := ⟨e, hU_le_H0 heU⟩
  let a'H : ↥(nineH0 V K g) := ⟨a', hA'leH.trans le_sup_left ha'A'⟩
  let vH : ↥(nineH0 V K g) := ⟨v, hVle hvV⟩
  have ha1 : π aH ≠ 1 := fun h1 =>
    haO0 ((nine3_dcal_inf_ker h hπ (nine3_omega_le_dcal h hAΩ).1 (d := aH) haA).mp h1)
  have he1 : π eH ≠ 1 := fun h1 =>
    heO0 ((nine3_dcal_inf_ker h hπ (nine3_omega_le_dcal h hUΩ).1 (d := eH) heU).mp h1)
  have ha'1 : π a'H ≠ 1 := fun h1 =>
    ha'O0 ((nine3_dcal_inf_ker h hπ hA'dcal (d := a'H) ha'A').mp h1)
  have hv1 : π vH ≠ 1 := fun h1 =>
    hvO0 ((nine3_dcal_inf_ker h hπ hV0 (d := vH) hvV).mp h1)
  have hVri : (V ⊓ pCoreOf 2 (nineH0 V K g)).relIndex V = 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact (nine3_dcal_not_le_pCore h hV0).2
  have hpiV_eq : ∀ w : ↥(nineH0 V K g), (w : G) ∈ V → π w ≠ 1 → π w = π vH := by
    intro w hwV hw1
    have hHπ : (⟨(w : G), hwV⟩ : ↥V) ∉ (V ⊓ pCoreOf 2 (nineH0 V K g)).subgroupOf V := by
      intro hmem
      exact hw1 (hπ.pcore_le w (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2)
    have hHπ' : (⟨(vH : G)⁻¹, V.inv_mem hvV⟩ : ↥V) ∉
        (V ⊓ pCoreOf 2 (nineH0 V K g)).subgroupOf V := by
      intro hmem
      have hO : (vH : G)⁻¹ ∈ pCoreOf 2 (nineH0 V K g) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
      have h1 : π vH⁻¹ = 1 := hπ.pcore_le vH⁻¹ (by simpa using hO)
      exact hv1 (inv_eq_one.mp (by simpa using h1))
    have hmem : (⟨(w : G), hwV⟩ : ↥V) * ⟨(vH : G)⁻¹, V.inv_mem hvV⟩ ∈
        (V ⊓ pCoreOf 2 (nineH0 V K g)).subgroupOf V := by
      rw [Subgroup.mul_mem_iff_of_index_two
        (H := (V ⊓ pCoreOf 2 (nineH0 V K g)).subgroupOf V) hVri]
      exact ⟨fun h1 => (hHπ h1).elim, fun h2 => (hHπ' h2).elim⟩
    have hO : (((⟨(w : G), hwV⟩ : ↥V) * ⟨(vH : G)⁻¹, V.inv_mem hvV⟩ : ↥V) : G) ∈
        V ⊓ pCoreOf 2 (nineH0 V K g) := Subgroup.mem_subgroupOf.mp hmem
    have hO' : (w : G) * (vH : G)⁻¹ ∈ pCoreOf 2 (nineH0 V K g) :=
      (Subgroup.mem_inf.mp hO).2
    have hw0 : π (w * vH⁻¹) = 1 := hπ.pcore_le (w * vH⁻¹) (by simpa using hO')
    have : π w * (π vH)⁻¹ = 1 := by rw [← map_inv, ← map_mul]; exact hw0
    exact eq_of_mul_inv_eq_one this
  have conj_of : ∀ (D : Subgroup G), D ∈ omegaIn V K (nineE V K) →
      ∀ d : ↥(nineH0 V K g), (d : G) ∈ D → π d ≠ 1 → IsConj (π vH) (π d) := by
    intro D hDΩ d hd hd1
    obtain ⟨hD, hhD, hD_eq⟩ := (nine3_omega_le_dcal h hDΩ).1
    have hv'd : hD * (d : G) * hD⁻¹ ∈ V := mem_conjSubgroup_iff.mp (hD_eq ▸ hd)
    let vd : ↥(nineH0 V K g) := ⟨hD * (d : G) * hD⁻¹, hVle hv'd⟩
    have hd_eq : d = (⟨hD, hhD⟩ : ↥(nineH0 V K g))⁻¹ * vd * ⟨hD, hhD⟩ := by
      apply Subtype.ext
      simp only [vd, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      group
    have hvd_ne : π vd ≠ 1 := by
      intro hvd1
      apply hd1
      rw [hd_eq, map_mul, map_mul, map_inv, hvd1, mul_one, inv_mul_cancel]
    have hd_eq' : π d = (π ⟨hD, hhD⟩)⁻¹ * π vH * π ⟨hD, hhD⟩ := by
      rw [hd_eq, map_mul, map_mul, map_inv, hpiV_eq vd hv'd hvd_ne]
    exact isConj_iff.mpr ⟨(π ⟨hD, hhD⟩)⁻¹, by rw [hd_eq', inv_inv]⟩
  have hAel : IsElemAbelian 2 A := by
    rw [← hc.V_g]
    exact E3.isElemAbelian_conjSubgroup hc.core.hyp7.1 g
  obtain ⟨yU, hUy, -, -⟩ := mem_omegaSet.mp hUΩ.1
  have hUel : IsElemAbelian 2 U := by
    rw [hUy]
    exact E3.isElemAbelian_conjSubgroup hc.core.hyp7.1 yU
  obtain ⟨yA', hA'y, -, -⟩ := mem_omegaSet.mp hA'Ω.1
  have hA'el : IsElemAbelian 2 A' := by
    rw [hA'y]
    exact E3.isElemAbelian_conjSubgroup hc.core.hyp7.1 yA'
  have ha2G : a * a = 1 := by
    have := hAel.2 a haA
    rwa [pow_two] at this
  have he2G : e * e = 1 := by
    have := hUel.2 e heU
    rwa [pow_two] at this
  have ha'2G : a' * a' = 1 := by
    have := hA'el.2 a' ha'A'
    rwa [pow_two] at this
  have hv2G : v * v = 1 := by
    have := hc.core.hyp7.1.2 v hvV
    rwa [pow_two] at this
  have ha2 : aH * aH = 1 := by
    apply Subtype.ext; change a * a = 1; exact ha2G
  have he2 : eH * eH = 1 := by
    apply Subtype.ext; change e * e = 1; exact he2G
  have ha'2 : a'H * a'H = 1 := by
    apply Subtype.ext; change a' * a' = 1; exact ha'2G
  have hv2 : vH * vH = 1 := by
    apply Subtype.ext; change v * v = 1; exact hv2G
  have hae3 : (aH * eH) ^ 3 = 1 := by
    apply Subtype.ext; change (a * e) ^ 3 = 1
    rw [← hp3]
    exact nine3_fib_pow hc hρ hAΩ hUΩ hA0 hUfib zero_ne_one a haA haR e heU heR
  have hea'3 : (eH * a'H) ^ 3 = 1 := by
    apply Subtype.ext; change (e * a') ^ 3 = 1
    rw [← hp3]
    exact nine3_fib_pow hc hρ hUΩ hA'Ω hUfib hA'0 one_ne_zero e heU heR a' ha'A' ha'R
  have haa' : aH * a'H = a'H * aH := by
    apply Subtype.ext; change a * a' = a' * a
    exact nine3_fib_comm hc hρ hAΩ hA'Ω hA0 hA'0 a haA a' ha'A'
  have hHcV : nineH V K ≤ Subgroup.centralizer (V : Set G) := by
    refine iSup₂_le fun D hD => ?_
    obtain ⟨k, hk, rfl⟩ := hc.nineH_transitive hD
    have hkK : k ∈ K := Nine3Choice.nineH_le_K hk
    have hVk : conjSubgroup V k = V :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (hc.core.hyp.base.le hkK)
    have hA_le_nineW : A ≤ nineW V S :=
      (le_iSup₂_of_le A hc.core.A_mem_nineDelta le_rfl : A ≤ ⨆ B ∈ nineDelta V S, B)
    have hV_le_nineW : V ≤ nineW V S :=
      (le_iSup₂_of_le V hc.core.V_mem_nineDelta le_rfl : V ≤ ⨆ B ∈ nineDelta V S, B)
    have hA_C : A ≤ Subgroup.centralizer (V : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hc.core.nineW_mul_comm (hA_le_nineW hx) (hV_le_nineW hy)).symm
    calc conjSubgroup A k ≤ conjSubgroup (Subgroup.centralizer (V : Set G)) k :=
          E3.conjSubgroup_mono_left k hA_C
      _ = Subgroup.centralizer (conjSubgroup V k : Set G) := E3.conjSubgroup_centralizer V k
      _ = Subgroup.centralizer (V : Set G) := by rw [hVk]
  have hHgcA : conjSubgroup (nineH V K) g ≤ Subgroup.centralizer (A : Set G) := by
    have h1 : conjSubgroup (nineH V K) g ≤
        conjSubgroup (Subgroup.centralizer (V : Set G)) g := E3.conjSubgroup_mono_left g hHcV
    rwa [E3.conjSubgroup_centralizer, hc.V_g] at h1
  have hva : vH * aH = aH * vH := by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hHcV (hA_le_nineH haA)) v hvV)
  have hve : vH * eH = eH * vH := by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hHcV (hU_le_nineH heU)) v hvV)
  have hva' : vH * a'H = a'H * vH := by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hHcV (hA'leH ha'A')) v hvV)
  have hfH : g⁻¹ * e * g ∈ conjSubgroup (nineH V K) g :=
    mem_conjSubgroup_iff.mpr (by
      rw [show g * (g⁻¹ * e * g) * g⁻¹ = e by group]
      exact hU_le_nineH heU)
  let fH : ↥(nineH0 V K g) :=
    ⟨g⁻¹ * e * g, (le_sup_right : conjSubgroup (nineH V K) g ≤ nineH0 V K g) hfH⟩
  have hbB : g * a' * g⁻¹ ∈ conjSubgroup A' g⁻¹ :=
    mem_conjSubgroup_iff.mpr (by
      have h : g⁻¹ * (g * a' * g⁻¹) * g⁻¹⁻¹ = a' := by group
      rwa [h])
  have hbR : g * a' * g⁻¹ ∉ pCoreOf 2 K := fun hh =>
    ha'Rg (mem_conjSubgroup_iff.mpr hh)
  have hBΩ : conjSubgroup A' g⁻¹ ∈ omegaIn V K (nineE V K) := hA'ginv_Ω
  have hB0 : Nine3Fib K p ρ (conjSubgroup A' g⁻¹) 0 :=
    (nine3_fib_zero_iff hc hρ hBΩ).mpr hA'ginv_mem.2
  have hbe3 : (g * a' * g⁻¹ * e) ^ 3 = 1 := by
    have h := nine3_fib_pow hc hρ hBΩ hUΩ hB0 hUfib zero_ne_one
      (g * a' * g⁻¹) hbB hbR e heU heR
    rwa [hp3] at h
  have hf2G : (g⁻¹ * e * g) * (g⁻¹ * e * g) = 1 := by
    calc (g⁻¹ * e * g) * (g⁻¹ * e * g) = g⁻¹ * (e * e) * g := by group
      _ = 1 := by rw [he2G]; group
  have hfaG : a * (g⁻¹ * e * g) = (g⁻¹ * e * g) * a :=
    Subgroup.mem_centralizer_iff.mp (hHgcA hfH) a haA
  have haf2G : (a * (g⁻¹ * e * g)) * (a * (g⁻¹ * e * g)) = 1 := by
    calc (a * (g⁻¹ * e * g)) * (a * (g⁻¹ * e * g))
        = a * ((g⁻¹ * e * g) * a) * (g⁻¹ * e * g) := by group
      _ = a * (a * (g⁻¹ * e * g)) * (g⁻¹ * e * g) := by rw [← hfaG]
      _ = (a * a) * ((g⁻¹ * e * g) * (g⁻¹ * e * g)) := by group
      _ = 1 := by rw [ha2G, hf2G, one_mul]
  have ha'f3G : (a' * (g⁻¹ * e * g)) ^ 3 = 1 := by
    have h : a' * (g⁻¹ * e * g) = g⁻¹ * (g * a' * g⁻¹ * e) * g := by group
    rw [show (a' * (g⁻¹ * e * g)) ^ 3
        = (g⁻¹ * (g * a' * g⁻¹ * e) * g) ^ 3 by rw [h]]
    rw [show (g⁻¹ * (g * a' * g⁻¹ * e) * g) ^ 3
        = g⁻¹ * (g * a' * g⁻¹ * e) ^ 3 * g by
      have h2 : g⁻¹ * (g * a' * g⁻¹ * e) * g
          = (MulAut.conj g⁻¹) (g * a' * g⁻¹ * e) := by
        rw [MulAut.conj_apply]; group
      rw [h2, ← map_pow, MulAut.conj_apply]; group]
    rw [hbe3]
    group
  have haf2 : (aH * fH) * (aH * fH) = 1 := by
    apply Subtype.ext
    change (a * (g⁻¹ * e * g)) * (a * (g⁻¹ * e * g)) = 1
    exact haf2G
  have hne_aa' : π aH * π a'H ≠ 1 := by
    intro hprod
    have hker : π (aH * a'H) = 1 := by rw [map_mul, hprod]
    have hnH : ((aH * a'H : ↥(nineH0 V K g)) : G) ∈ pCoreOf 2 (nineH0 V K g) := by
      have hsq : (aH * a'H) ^ 2 = 1 := by
        rw [pow_two]
        calc (aH * a'H) * (aH * a'H) = aH * (a'H * aH) * a'H := by group
          _ = aH * (aH * a'H) * a'H := by rw [← haa']
          _ = (aH * aH) * (a'H * a'H) := by group
          _ = 1 := by rw [ha2, ha'2, one_mul]
      rcases (Nat.dvd_prime Nat.prime_two).mp
          (orderOf_dvd_iff_pow_eq_one.mpr hsq) with h1 | h2
      · exact hπ.two_elt (aH * a'H) hker 0 (by rw [h1, pow_zero])
      · exact hπ.two_elt (aH * a'H) hker 1 (by rw [h2, pow_one])
    let N : Subgroup ↥(nineH0 V K g) := (pCoreOf 2 (nineH0 V K g)).subgroupOf (nineH0 V K g)
    have hNnormal : N.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (nineH0 V K g))).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (nineH0 V K g))
    have hnH_N : aH * a'H ∈ N := Subgroup.mem_subgroupOf.mpr hnH
    have ha'eq : a'H = aH * (aH * a'H) := by
      rw [← mul_assoc, ha2, one_mul]
    have haHinv : aH⁻¹ = aH := inv_eq_of_mul_eq_one_right ha2
    have hafa : aH * fH * aH = fH⁻¹ := by
      have h := congrArg (fun z => z * fH⁻¹) haf2
      simpa [mul_assoc] using h
    have hfa' : fH * aH = aH * fH⁻¹ := by
      have h : aH * (aH * fH * aH) = aH * fH⁻¹ := congrArg (fun z => aH * z) hafa
      have h1 : aH * (aH * fH * aH) = fH * aH := by
        calc aH * (aH * fH * aH) = (aH * aH) * (fH * aH) := by group
          _ = fH * aH := by rw [ha2, one_mul]
      rwa [h1] at h
    have hnH' : aH * (aH * a'H) * aH ∈ N := by
      have h := hNnormal.conj_mem (aH * a'H) hnH_N aH
      simpa [haHinv, mul_assoc] using h
    have hfnf : fH⁻¹ * (aH * a'H) * fH ∈ N := by
      have h := hNnormal.conj_mem (aH * a'H) hnH_N fH⁻¹
      simpa using h
    have hx2 : (a'H * fH) * (a'H * fH) ∈ N := by
      have heq : (a'H * fH) * (a'H * fH)
          = (aH * (aH * a'H) * aH) * (fH⁻¹ * (aH * a'H) * fH) := by
        conv_lhs => rw [ha'eq]
        calc (aH * (aH * a'H) * fH) * (aH * (aH * a'H) * fH)
            = aH * (aH * a'H) * (fH * aH) * (aH * a'H) * fH := by group
          _ = aH * (aH * a'H) * (aH * fH⁻¹) * (aH * a'H) * fH := by rw [hfa']
          _ = (aH * (aH * a'H) * aH) * (fH⁻¹ * (aH * a'H) * fH) := by group
      rw [heq]
      exact N.mul_mem hnH' hfnf
    have hx3 : (a'H * fH) ^ 3 = 1 := by
      apply Subtype.ext; change (a' * (g⁻¹ * e * g)) ^ 3 = 1; exact ha'f3G
    have hxmem : a'H * fH ∈ N := by
      have hx : a'H * fH = (a'H * fH) ^ 3 * ((a'H * fH) ^ 2)⁻¹ := by group
      rw [hx, hx3, one_mul]
      exact N.inv_mem (by rw [pow_two]; exact hx2)
    have hx1 : a'H * fH = 1 := by
      by_contra hne
      have h2 : IsPGroup 2 ↥N :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (nineH0 V K g)).of_equiv
          (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 (nineH0 V K g))).symm
      have hne' : (⟨a'H * fH, hxmem⟩ : ↥N) ≠ 1 := fun hh => hne (Subtype.ext_iff.mp hh)
      have hdvd2 : 2 ∣ orderOf (⟨a'H * fH, hxmem⟩ : ↥N) := IsPGroup.dvd_orderOf h2 hne'
      have hdvd3 : orderOf (⟨a'H * fH, hxmem⟩ : ↥N) ∣ 3 := by
        rw [orderOf_dvd_iff_pow_eq_one]
        apply Subtype.ext
        simpa using hx3
      exact absurd (Nat.dvd_trans hdvd2 hdvd3) (by norm_num)
    have ha'eq2 : a' = g⁻¹ * e * g := by
      have h : a' * (g⁻¹ * e * g) = 1 := by
        have := congrArg (fun z : ↥(nineH0 V K g) => (z : G)) hx1
        simpa [a'H, fH] using this
      calc a' = a' * (g⁻¹ * e * g) * (g⁻¹ * e * g)⁻¹ := by group
        _ = (g⁻¹ * e * g)⁻¹ := by rw [h, one_mul]
        _ = g⁻¹ * e * g := by
          rw [mul_inv_rev, mul_inv_rev,
            show e⁻¹ = e from inv_eq_of_mul_eq_one_right he2G]
          group
    have hbU : g * a' * g⁻¹ ∈ U := by
      rw [ha'eq2, show g * (g⁻¹ * e * g) * g⁻¹ = e by group]
      exact heU
    obtain ⟨hB, hhB, hB_eq⟩ := (nine3_omega_le_dcal h hBΩ).1
    have hBneU : conjSubgroup A' g⁻¹ ≠ U := by
      intro hBU
      have hUS : U ≤ S := hBU ▸ hA'ginv_mem.2
      have hU0 : Nine3Fib K p ρ U 0 := (nine3_fib_zero_iff hc hρ hUΩ).mpr hUS
      have hUK : e ∈ K := hUΩ.2 heU
      have h1 : ρ ⟨e, hUK⟩ = zmodRefl p 1 := hUfib ⟨e, hUK⟩ heU heR
      have h0 : ρ ⟨e, hUK⟩ = zmodRefl p 0 := hU0 ⟨e, hUK⟩ heU heR
      exact hUc0 (zmodRefl_inj hc.core.hyp.base.prime hc.core.hyp.base.odd
        (h1.symm.trans h0))
    have hBU_bot : conjSubgroup A' g⁻¹ ⊓ U = ⊥ := by
      have h := inf_conjSubgroup_eq_bot_or_eq hc.core.hyp7.2.2 hB yU
      rw [← hB_eq, ← hUy] at h
      exact h.resolve_right hBneU
    have heB : e ∈ conjSubgroup A' g⁻¹ := by
      rw [mem_conjSubgroup_iff, inv_inv]
      rw [← ha'eq2]
      exact ha'A'
    have he1' : e = 1 := by
      have : e ∈ (⊥ : Subgroup G) := by
        rw [← hBU_bot]
        exact Subgroup.mem_inf.mpr ⟨heB, heU⟩
      simpa using this
    exact heR (he1' ▸ (pCoreOf 2 K).one_mem)
  exact ⟨U, 1, aH, eH, a'H, vH, hUΩ, hUfib, hUc0, haA, haR, heU, heR, hvV,
    { conj_a := conj_of A hAΩ aH haA ha1
      conj_e := conj_of U hUΩ eH heU he1
      conj_a' := conj_of A' hA'Ω a'H ha'A' ha'1
      conj_v := IsConj.refl _
      sq_a := by rw [← map_mul, ha2, map_one]
      sq_e := by rw [← map_mul, he2, map_one]
      sq_a' := by rw [← map_mul, ha'2, map_one]
      sq_v := by rw [← map_mul, hv2, map_one]
      ne_v := hv1
      pow_ae := by rw [← map_mul, ← map_pow, hae3, map_one]
      pow_ea' := by rw [← map_mul, ← map_pow, hea'3, map_one]
      comm_aa' := by rw [← map_mul, ← map_mul, haa']
      ne_aa' := hne_aa'
      comm_va := by rw [← map_mul, ← map_mul, hva]
      comm_ve := by rw [← map_mul, ← map_mul, hve]
      comm_va' := by rw [← map_mul, ← map_mul, hva'] }⟩

end CFSG.LocalAnalysis.WeakClosure81
