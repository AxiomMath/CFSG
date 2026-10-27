module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFibreIota

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nine3_conjSubgroup_iSup {ι : Sort*} (B : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, B i) g = ⨆ i, conjSubgroup (B i) g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_iSup _ _

theorem nine3_oddFrame_trans (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {ρ : ↥K →* Equiv.Perm (ZMod p)} (hρ : Nine3FibreAct K S p x ρ) (a b : ZMod p) (hab : a ≠ b)
    {d e : Nine3Hbar V K} (hd : d ∈ Nine3Dbar V K)
    (hda : nine3Pi V K ρ hρ.le_ker d = zmodRefl p a) (he : e ∈ Nine3Dbar V K)
    (hea : nine3Pi V K ρ hρ.le_ker e = zmodRefl p a) :
    ∃ z ∈ Subgroup.closure {f | f ∈ Nine3Dbar V K ∧ nine3Pi V K ρ hρ.le_ker f = zmodRefl p b} ⊓
        (nine3Pi V K ρ hρ.le_ker).ker, z * d * z⁻¹ = e := by
  classical
  obtain ⟨B, hBΩ, hBfib, u, huB, huR, hd_eq⟩ := nine3_dbar_over hc hρ hd hda
  obtain ⟨B', hB'Ω, hB'fib, u', hu'B', hu'R, he_eq⟩ := nine3_dbar_over hc hρ he hea
  obtain ⟨k, hkX, -, hk_trans⟩ := nine3_exists_translation hc hρ a
  obtain ⟨y, hyX, hy_ne0, hy_trans⟩ := nine3_exists_translation hc hρ (a - b)
  have hy1 : (y : G) ≠ 1 := hy_ne0 (sub_ne_zero.2 hab)
  have hAΩ : A ∈ omegaIn V K (nineE V K) :=
    ⟨hc.core.A_mem_nineOmegaIn.1, hc.core.nineOmegaIn_le_K hc.core.A_mem_nineOmegaIn⟩
  have hA0 : Nine3Fib K p ρ A 0 :=
    (nine3_fib_zero_iff hc hρ hAΩ).mpr hc.core.A_mem_nineOmegaIn.2
  let Fb : Set (Nine3Hbar V K) :=
    {f | f ∈ Nine3Dbar V K ∧ nine3Pi V K ρ hρ.le_ker f = zmodRefl p b}
  have hBkΩ : conjSubgroup B (k : G) ∈ omegaIn V K (nineE V K) :=
    conjSubgroup_mem_omegaIn hBΩ k.2
  have hBk0 : Nine3Fib K p ρ (conjSubgroup B (k : G)) 0 := by
    have h := nine3_fib_conj (U := B) (c := a) (t := a) hBfib hk_trans
    simpa using h
  have hBkN : conjSubgroup B (k : G) ∈ nineOmegaIn V K S :=
    ⟨hBkΩ.1, (nine3_fib_zero_iff hc hρ hBkΩ).mp hBk0⟩
  have hB'kΩ : conjSubgroup B' (k : G) ∈ omegaIn V K (nineE V K) :=
    conjSubgroup_mem_omegaIn hB'Ω k.2
  have hB'k0 : Nine3Fib K p ρ (conjSubgroup B' (k : G)) 0 := by
    have h := nine3_fib_conj (U := B') (c := a) (t := a) hB'fib hk_trans
    simpa using h
  have hB'kN : conjSubgroup B' (k : G) ∈ nineOmegaIn V K S :=
    ⟨hB'kΩ.1, (nine3_fib_zero_iff hc hρ hB'kΩ).mp hB'k0⟩
  obtain ⟨δ, hδD, hδeq⟩ := hc.core.nineD_transitive hyX hy1 hBkN hB'kN
  let δ' : G := (k : G) * δ * (k : G)⁻¹
  have hB'eq_conj : conjSubgroup B' (k : G) = conjSubgroup B ((k : G) * δ) := by
    rw [hδeq, CFSG.Quasithin.conjSubgroup_conjSubgroup]
  have hB'eq : B' = conjSubgroup B δ' := by
    have h2 := congrArg (fun Q : Subgroup G => conjSubgroup Q (k : G)⁻¹) hB'eq_conj
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, CFSG.Quasithin.conjSubgroup_conjSubgroup,
      mul_inv_cancel, CFSG.Quasithin.conjSubgroup_one] at h2
    exact h2
  have hδ'R : δ' ∈ pCoreOf 2 K := by
    have := (Nine3Core.mem_pCoreOf_conj_iff K k.2).mp hδD.2
    simpa [δ'] using this
  have hδ'J : δ' ∈ ⨆ r ∈ pCoreOf 2 K, conjSubgroup A ((y : G) * r * (k : G)⁻¹) := by
    have hmem : δ' ∈ conjSubgroup (⨆ r ∈ pCoreOf 2 K, conjSubgroup A ((y : G) * r))
        (k : G)⁻¹ := by
      refine mem_conjSubgroup_iff.mpr ?_
      have heq : (k : G)⁻¹ * δ' * ((k : G)⁻¹)⁻¹ = δ := by
        change (k : G)⁻¹ * ((k : G) * δ * (k : G)⁻¹) * ((k : G)⁻¹)⁻¹ = δ
        group
      rw [heq]
      exact hδD.1
    have hJeq : conjSubgroup (⨆ r ∈ pCoreOf 2 K, conjSubgroup A ((y : G) * r)) (k : G)⁻¹ =
        ⨆ r ∈ pCoreOf 2 K, conjSubgroup A ((y : G) * r * (k : G)⁻¹) := by
      simp only [nine3_conjSubgroup_iSup, CFSG.Quasithin.conjSubgroup_conjSubgroup]
    rwa [hJeq] at hmem
  have hJ'leH : (⨆ r ∈ pCoreOf 2 K, conjSubgroup A ((y : G) * r * (k : G)⁻¹)) ≤
      nineH V K := by
    refine iSup₂_le fun r hr => ?_
    have hrK : r ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hr
    exact le_iSup₂_of_le (conjSubgroup A ((y : G) * r * (k : G)⁻¹))
      (conjSubgroup_mem_omegaIn hAΩ (K.mul_mem (K.mul_mem y.2 hrK) (K.inv_mem k.2))) le_rfl
  have hδ'H : δ' ∈ nineH V K := hJ'leH hδ'J
  let δ'' : ↥(nineH V K) := ⟨δ', hδ'H⟩
  have hUrOmega : ∀ r : G, r ∈ pCoreOf 2 K →
      conjSubgroup A ((y : G) * r * (k : G)⁻¹) ∈ omegaIn V K (nineE V K) := by
    intro r hr
    exact conjSubgroup_mem_omegaIn hAΩ
      (K.mul_mem (K.mul_mem y.2 (CFSG.LieType.BorelTits.pCoreOf_le 2 K hr)) (K.inv_mem k.2))
  have hUrFib : ∀ r : G, r ∈ pCoreOf 2 K →
      Nine3Fib K p ρ (conjSubgroup A ((y : G) * r * (k : G)⁻¹)) b := by
    intro r hr
    have hrK : r ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hr
    let rK : ↥K := ⟨r, hrK⟩
    let yrk : ↥K := y * rK * k⁻¹
    have hρr : ρ rK = 1 := hρ.le_ker rK hr
    have hyrk : ∀ i : ZMod p, ρ yrk i = i + (-b) := by
      intro i
      have h1 : ρ yrk = ρ y * ρ rK * (ρ k)⁻¹ := by
        rw [show yrk = y * rK * k⁻¹ from rfl, map_mul, map_mul, map_inv]
      have hkinv : (ρ k)⁻¹ i = i - a := by
        rw [Equiv.Perm.inv_eq_iff_eq, hk_trans, sub_add_cancel]
      calc ρ yrk i = (ρ y * ρ rK * (ρ k)⁻¹) i := by rw [h1]
        _ = ρ y (ρ rK ((ρ k)⁻¹ i)) := by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
        _ = ρ y ((ρ k)⁻¹ i) := by simp [hρr]
        _ = ((ρ k)⁻¹ i) + (a - b) := hy_trans _
        _ = (i - a) + (a - b) := by rw [hkinv]
        _ = i + (-b) := by ring
    have h := nine3_fib_conj (U := A) (c := 0) (k := yrk) (t := -b) hA0 hyrk
    simpa [yrk, rK] using h
  let N : Subgroup ↥(nineH V K) := (nineI V K).subgroupOf (nineH V K)
  let P : Subgroup ↥(nineH V K) := (Subgroup.closure Fb).comap (QuotientGroup.mk' N)
  have hUrP : ∀ r : G, r ∈ pCoreOf 2 K →
      conjSubgroup A ((y : G) * r * (k : G)⁻¹) ≤ P.map (nineH V K).subtype := by
    intro r hr m hm
    have hUrΩ := hUrOmega r hr
    have hmH : m ∈ nineH V K := by
      show m ∈ ⨆ U ∈ omegaIn V K (nineE V K), U
      exact Subgroup.mem_iSup_of_mem (conjSubgroup A ((y : G) * r * (k : G)⁻¹))
        (Subgroup.mem_iSup_of_mem hUrΩ hm)
    refine Subgroup.mem_map.mpr ⟨⟨m, hmH⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    show (QuotientGroup.mk (⟨m, hmH⟩ : ↥(nineH V K)) : Nine3Hbar V K) ∈ Subgroup.closure Fb
    by_cases hmR : m ∈ pCoreOf 2 K
    · have hmI : m ∈ nineI V K := by
        show m ∈ ⨆ U ∈ omegaIn V K (nineE V K), U ⊓ pCoreOf 2 K
        exact Subgroup.mem_iSup_of_mem (conjSubgroup A ((y : G) * r * (k : G)⁻¹))
          (Subgroup.mem_iSup_of_mem hUrΩ ⟨hm, hmR⟩)
      have h1 : (QuotientGroup.mk (⟨m, hmH⟩ : ↥(nineH V K)) : Nine3Hbar V K) = 1 := by
        rw [QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hmI
      rw [h1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (nine3_mk_mem_dbar hUrΩ hρ.le_ker (hUrFib r hr) hm hmR)
  have hJ'leP : (⨆ r ∈ pCoreOf 2 K, conjSubgroup A ((y : G) * r * (k : G)⁻¹)) ≤
      P.map (nineH V K).subtype := iSup₂_le hUrP
  have hδ''P : δ'' ∈ P := by
    have hmem : (δ'' : G) ∈ P.map (nineH V K).subtype := hJ'leP hδ'J
    obtain ⟨x, hxP, hxeq⟩ := Subgroup.mem_map.mp hmem
    have hx : x = δ'' := Subtype.ext hxeq
    rwa [hx] at hxP
  have hδ''cl : (QuotientGroup.mk δ'' : Nine3Hbar V K) ∈ Subgroup.closure Fb := by
    have h := Subgroup.mem_comap.mp hδ''P
    simpa using h
  have hπδ'' : nine3Pi V K ρ hρ.le_ker (QuotientGroup.mk δ'') = 1 := by
    rw [nine3Pi_mk]
    exact hρ.le_ker ⟨δ'', Nine3Choice.nineH_le_K δ''.2⟩ hδ'R
  let w : ↥(nineH V K) := δ''⁻¹ * u * δ''
  have hwB' : (w : G) ∈ B' := by
    show δ'⁻¹ * (u : G) * δ' ∈ B'
    rw [hB'eq]
    refine mem_conjSubgroup_iff.mpr ?_
    have : δ' * (δ'⁻¹ * (u : G) * δ') * δ'⁻¹ = (u : G) := by group
    rw [this]
    exact huB
  have hwR : (w : G) ∉ pCoreOf 2 K := by
    show δ'⁻¹ * (u : G) * δ' ∉ pCoreOf 2 K
    intro hh
    have hδ'K : δ' ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hδ'R
    have hconj := (Nine3Core.mem_pCoreOf_conj_iff K hδ'K).mp hh
    have : δ' * (δ'⁻¹ * (u : G) * δ') * δ'⁻¹ = (u : G) := by group
    rw [this] at hconj
    exact huR hconj
  have hmkw : (QuotientGroup.mk w : Nine3Hbar V K) = (QuotientGroup.mk u' : Nine3Hbar V K) :=
    nine3_mk_eq_of_mem hc hB'Ω hwB' hu'B' hwR hu'R
  have hmul : (QuotientGroup.mk w : Nine3Hbar V K) =
      (QuotientGroup.mk δ'')⁻¹ * (QuotientGroup.mk u : Nine3Hbar V K) *
        (QuotientGroup.mk δ'') := by
    rw [show w = δ''⁻¹ * u * δ'' from rfl, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
  have hfinal : (QuotientGroup.mk δ'')⁻¹ * d * ((QuotientGroup.mk δ'')⁻¹)⁻¹ = e := by
    rw [inv_inv, ← he_eq, ← hmkw, hmul, hd_eq]
  have hπz : nine3Pi V K ρ hρ.le_ker (QuotientGroup.mk δ'')⁻¹ = 1 := by
    rw [map_inv, hπδ'', inv_one]
  exact ⟨(QuotientGroup.mk δ'')⁻¹,
    ⟨Subgroup.inv_mem _ hδ''cl, MonoidHom.mem_ker.mpr hπz⟩, hfinal⟩

end CFSG.LocalAnalysis.WeakClosure81
