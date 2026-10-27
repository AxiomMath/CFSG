module

public import CFSG.Quasithin.H13.L32A771a
public import CFSG.Quasithin.H13.L32A72b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem perm5_exists_conj_mul_five : ∀ s : Equiv.Perm (Fin 5), s * s = 1 → s ≠ 1 →
    Equiv.Perm.sign s = 1 → ∃ g : Equiv.Perm (Fin 5),
      (s * (g * s * g⁻¹)) ^ 5 = 1 ∧ s * (g * s * g⁻¹) ≠ 1 := by
  decide +kernel

omit [Finite G] in
theorem sign_phi_of_mem_sup {H : Subgroup G} {φ : ↥H →* Equiv.Perm (Fin 5)}
    (hk : φ.ker = CFSG.Open.pCore 2 ↥H) {x : ↥H} (hx : (x : G) ∈ oTwoUpper H ⊔ pCoreOf 2 H) :
    Equiv.Perm.sign (φ x) = 1 := by
  have hKN : oTwoUpper H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (oTwoUpper_le H).trans (le_normalizer_pCoreOf 2 H)
  have hx' : (x : G) ∈ ((oTwoUpper H : Set G) * (pCoreOf 2 H : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKN]
    exact hx
  obtain ⟨k, hkK, q, hqQ, hkq⟩ := hx'
  have hkH : k ∈ H := oTwoUpper_le H hkK
  have hqH : q ∈ H := pCoreOf_le 2 H hqQ
  have e : x = ⟨k, hkH⟩ * ⟨q, hqH⟩ := Subtype.ext (by simp [hkq])
  have hq1 : φ ⟨q, hqH⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hk]
    exact mem_pCoreOf_iff'.mp hqQ
  rw [e, map_mul, hq1, mul_one]
  exact sign_phi_kz hkK

variable {T L V : Subgroup G}

theorem commutator_le_fsuU_of (h : Hyp147 G T L V) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {l₀ : G} (hl₀ : l₀ ∈ L)
    (hR : conjSub l₀ (fsuU T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub l₀ (fsuU T V) ⊔ pCoreOf 2 (hz T V)) = 2)
    (hcap : fsuU T V ⊓ conjSub l₀ (fsuU T V) = V ⊔ u0 T V) :
    ⁅pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G), kz T V⁆ ≤ fsuU T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨-, -, hLTV, -, -⟩ := hMod G T L V h.hyp h.fsu
  set Uα := conjSub l₀ (fsuU T V) with hUα
  set X := pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) with hX
  have hUe := isElemAbelian_fsuU_of h hMod
  have hUc : fsuU T V = conjClosure V (hz T V) := fsuU_eq_conjClosure_hz hMod h
  have hHU : hz T V ≤ Subgroup.normalizer (fsuU T V : Set G) := by
    rw [hUc]
    exact le_normalizer_conjClosure V _
  have hUQ : fsuU T V ≤ pCoreOf 2 (hz T V) := by
    rw [hUc]
    exact hF.conjClosure_Vp_le_pCoreOf
  have hTH : T ≤ hz T V := hF.T_le_H
  have hR1T : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T := pCoreOf_le_of_le h le_sup_right
  have hUαH : Uα ≤ hz T V := hR.trans (hR1T.trans hTH)
  have hQHn : hz T V ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hHC : hz T V ≤
      Subgroup.normalizer (Subgroup.centralizer (fsuU T V : Set G) : Set G) := by
    intro k hk
    rw [← conjSub_eq_self_iff, ← conjSub_centralizer, conjSub_eq_self_iff.mpr (hHU hk)]
  have hHX : hz T V ≤ Subgroup.normalizer (X : Set G) := by
    intro k hk
    rw [← conjSub_eq_self_iff, hX, conjSub_inf, conjSub_eq_self_iff.mpr (hQHn hk),
      conjSub_eq_self_iff.mpr (hHC hk)]
  have hXH : X ≤ hz T V := inf_le_left.trans (pCoreOf_le 2 _)
  have hXU : X ≤ Subgroup.normalizer (fsuU T V : Set G) := hXH.trans hHU
  have hXUα : X ≤ Subgroup.normalizer (Uα : Set G) := by
    intro c hc
    have hcV : c ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.centralizer_le (fun v hv => v_le_fsuU hv) (Subgroup.mem_inf.mp hc).2
    rw [hUα, conjSub_normalizer, mem_conjSub]
    apply hHU
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzV : z ∈ V := (Subgroup.mem_inf.mp (SetLike.mem_coe.mp hz)).1
    have hz' : l₀ * z * l₀⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hl₀) z).mp hzV
    have hc' := Subgroup.mem_centralizer_iff.mp hcV _ hz'
    calc z * (l₀⁻¹ * c * l₀) = l₀⁻¹ * ((l₀ * z * l₀⁻¹) * c) * l₀ := by group
      _ = l₀⁻¹ * (c * (l₀ * z * l₀⁻¹)) * l₀ := by rw [hc']
      _ = (l₀⁻¹ * c * l₀) * z := by group
  set D := Uα ⊓ pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) with hD
  have hA2 : ∀ a ∈ Uα, ∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ D := by
    intro a ha x hx
    have haH := hUαH ha
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [show a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) by group]
      exact mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hXUα hx) _).mp (inv_mem ha))
    · exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hQHn haH) x).mp hxQ) (inv_mem hxQ)
    · exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hHC haH) x).mp hxC) (inv_mem hxC)
  have hDU : D ⊓ fsuU T V = fsuU T V ⊓ Uα := by
    ext w
    simp only [hD, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨⟨h1, -⟩, -⟩, h4⟩
      exact ⟨h4, h1⟩
    · rintro ⟨h4, h1⟩
      exact ⟨⟨⟨h1, hUQ h4⟩, Subgroup.mem_centralizer_iff.mpr fun u hu =>
        F7.isElemAbelian_comm hUe hu h4⟩, h4⟩
  have hcardUα : Nat.card ↥Uα = Nat.card ↥(fsuU T V) := by
    rw [hUα, conjSub]
    exact Subgroup.card_map_of_injective (MulAut.conj l₀).injective
  have hcap4 : 4 * Nat.card ↥(fsuU T V ⊓ Uα) = Nat.card ↥(fsuU T V) := by
    have h1 := Subgroup.relIndex_mul_card (V ⊔ u0 T V) (fsuU T V)
    rw [(relIndex_sup_u0 h hMod h63 hF).2, inf_eq_left.mpr sup_u0_le_fsuU, ← hcap] at h1
    exact h1
  have hUαQ : Nat.card ↥Uα = 2 * Nat.card ↥(Uα ⊓ pCoreOf 2 (hz T V)) := by
    have h1 := L32NSet14.card_sup_mul_card_inf (hUαH.trans hQHn)
    have h3 := Subgroup.relIndex_mul_card (pCoreOf 2 (hz T V)) (Uα ⊔ pCoreOf 2 (hz T V))
    rw [inf_eq_left.mpr le_sup_right, h2] at h3
    rw [← h3] at h1
    have hpos : 0 < Nat.card ↥(pCoreOf 2 (hz T V)) := Nat.card_pos
    have e : Nat.card ↥Uα * Nat.card ↥(pCoreOf 2 (hz T V)) =
        2 * Nat.card ↥(Uα ⊓ pCoreOf 2 (hz T V)) * Nat.card ↥(pCoreOf 2 (hz T V)) := by
      rw [← h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos e
  have hD2 : (D ⊓ fsuU T V).relIndex D ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card (D ⊓ fsuU T V) D
    rw [inf_eq_left.mpr (inf_le_left : D ⊓ fsuU T V ≤ D)] at h1
    have hc : Nat.card ↥(D ⊓ fsuU T V) = Nat.card ↥(fsuU T V ⊓ Uα) := by rw [hDU]
    have hDle : Nat.card ↥D ≤ Nat.card ↥(Uα ⊓ pCoreOf 2 (hz T V)) :=
      Subgroup.card_le_of_le inf_le_left
    have hpos : 0 < Nat.card ↥(D ⊓ fsuU T V) := Nat.card_pos
    have h3 : (D ⊓ fsuU T V).relIndex D * Nat.card ↥(D ⊓ fsuU T V) ≤
        2 * Nat.card ↥(D ⊓ fsuU T V) := by
      calc (D ⊓ fsuU T V).relIndex D * Nat.card ↥(D ⊓ fsuU T V) = Nat.card ↥D := h1
        _ ≤ Nat.card ↥(Uα ⊓ pCoreOf 2 (hz T V)) := hDle
        _ = 2 * Nat.card ↥(D ⊓ fsuU T V) := by omega
    exact Nat.le_of_mul_le_mul_right h3 hpos
  obtain ⟨t, htUα, htQ⟩ : ∃ t ∈ Uα, t ∉ pCoreOf 2 (hz T V) := by
    by_contra hne
    push Not at hne
    rw [sup_eq_right.mpr hne, Subgroup.relIndex_self] at h2
    exact absurd h2 (by norm_num)
  have htH := hUαH htUα
  have hF2 : (fixMod t X (fsuU T V)).relIndex X ≤ 2 :=
    relIndex_fixMod_le_two hXU (hA2 t htUα) hD2
  obtain ⟨φ, hs, hk⟩ := exists_phi h h63
  have hφ1 : ∀ x : ↥(hz T V), φ x = 1 ↔ (x : G) ∈ pCoreOf 2 (hz T V) := fun x => by
    rw [← MonoidHom.mem_ker, hk, ← mem_pCoreOf_iff']
  have ht2 : t * t = 1 := by
    have h1 := F7.isElemAbelian_pow_eq_one hUe (mem_conjSub.mp htUα)
    rw [pow_two] at h1
    calc t * t = l₀ * ((l₀⁻¹ * t * l₀) * (l₀⁻¹ * t * l₀)) * l₀⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hφt2 : φ ⟨t, htH⟩ * φ ⟨t, htH⟩ = 1 := by
    rw [← map_mul]
    have e : (⟨t, htH⟩ * ⟨t, htH⟩ : ↥(hz T V)) = 1 := Subtype.ext ht2
    rw [e, map_one]
  have hφt1 : φ ⟨t, htH⟩ ≠ 1 := fun h' => htQ ((hφ1 _).mp h')
  have hφtA : Equiv.Perm.sign (φ ⟨t, htH⟩) = 1 :=
    sign_phi_of_mem_sup hk ((R1_le_kz_sup ⟨h, h.isHzOne_hz h63⟩ hF h63 h1222 h1332 h1334).1
      (hR htUα))
  obtain ⟨g, hg5, hg1⟩ := perm5_exists_conj_mul_five _ hφt2 hφt1 hφtA
  obtain ⟨k, hkg⟩ := hs g
  have hkH := k.2
  set t' := (k : G) * t * (k : G)⁻¹ with ht'
  have ht'H : t' ∈ hz T V := mul_mem (mul_mem hkH htH) (inv_mem hkH)
  set y₀ := t * t' with hy₀
  have hy₀H : y₀ ∈ hz T V := mul_mem htH ht'H
  have hφy₀ : φ ⟨y₀, hy₀H⟩ = φ ⟨t, htH⟩ * (g * φ ⟨t, htH⟩ * g⁻¹) := by
    rw [← hkg]
    have e : (⟨y₀, hy₀H⟩ : ↥(hz T V)) = ⟨t, htH⟩ * (k * ⟨t, htH⟩ * k⁻¹) :=
      Subtype.ext (by simp [hy₀, ht'])
    rw [e, map_mul, map_mul, map_mul, map_inv]
  have hq5 : ((⟨y₀, hy₀H⟩ ^ 5 : ↥(hz T V)) : G) ∈ pCoreOf 2 (hz T V) :=
    (hφ1 _).mp (by rw [map_pow, hφy₀, hg5])
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (hz T V)) ⟨_, hq5⟩
  have hm' : (y₀ ^ 5) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  set y := y₀ ^ 2 ^ m with hy
  have hy5 : y ^ 5 = 1 := by rw [hy, ← pow_mul, mul_comm, pow_mul, hm']
  have hyH : y ∈ hz T V := pow_mem hy₀H _
  have hφy : φ ⟨y, hyH⟩ = φ ⟨y₀, hy₀H⟩ ^ 2 ^ m := by
    rw [← map_pow]
    rfl
  have hφy1 : φ ⟨y, hyH⟩ ≠ 1 := by
    rw [hφy, hφy₀]
    intro h1
    apply hg1
    have hord := Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 5 2))
      (orderOf_dvd_of_pow_eq_one hg5) (orderOf_dvd_of_pow_eq_one h1)
    exact orderOf_eq_one_iff.mp hord
  have hφy5 : φ ⟨y, hyH⟩ ^ 5 = 1 := by
    rw [← map_pow]
    have e : (⟨y, hyH⟩ ^ 5 : ↥(hz T V)) = 1 := Subtype.ext (by simpa using hy5)
    rw [e, map_one]
  have hF2' : (fixMod t' X (fsuU T V)).relIndex X ≤ 2 := by
    rw [ht', fixMod_conj (hHX hkH) (hHU hkH)]
    have e := F9.relIndex_conjSub (k : G) (fixMod t X (fsuU T V)) X
    rw [conjSub_eq_self_iff.mpr (hHX hkH)] at e
    rw [e]
    exact hF2
  have hle : fixMod t X (fsuU T V) ⊓ fixMod t' X (fsuU T V) ≤ fixMod y X (fsuU T V) :=
    fun x hx => mem_fixMod_pow (hHU hy₀H)
      (mem_fixMod_mul (hHU htH) (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2) _
  have hF4 : (fixMod y X (fsuU T V)).relIndex X ≤ 4 := by
    have hne0 : (fixMod t X (fsuU T V) ⊓ fixMod t' X (fsuU T V)).relIndex X ≠ 0 := by
      show ((fixMod t X (fsuU T V) ⊓ fixMod t' X (fsuU T V)).subgroupOf X).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite
    calc (fixMod y X (fsuU T V)).relIndex X ≤
          (fixMod t X (fsuU T V) ⊓ fixMod t' X (fsuU T V)).relIndex X :=
          Subgroup.relIndex_le_of_le_left hle hne0
      _ ≤ (fixMod t X (fsuU T V)).relIndex X * (fixMod t' X (fsuU T V)).relIndex X :=
          Subgroup.relIndex_inf_le
      _ ≤ 2 * 2 := Nat.mul_le_mul hF2 hF2'
  have h5X : ¬ 5 ∣ Nat.card ↥X := by
    obtain ⟨n, hn⟩ := ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (hz T V)).to_le
      (inf_le_left : X ≤ pCoreOf 2 (hz T V))).exists_card_eq
    rw [hn]
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd
    omega
  have hfix := fixMod_eq_of_pow_five hy5 (hHX hyH) (hHU hyH) hXU h5X hF4
  have hyN : y ∈ hz T V ⊓ L32NSet14.trivSub X (fsuU T V) := by
    refine Subgroup.mem_inf.mpr ⟨hyH, hHX hyH, hHU hyH, fun x hx => ?_⟩
    rw [← hfix] at hx
    exact hx.2.2
  have hKN := oTwoUpper_le_of_mem_perm5 hs hk inf_le_left
    (fun h' hh' n hn => Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hh' (Subgroup.mem_inf.mp hn).1)
      (inv_mem hh'), L32NSet14.conj_mem_trivSub (hHX hh') (hHU hh') (Subgroup.mem_inf.mp hn).2⟩)
    hyN hφy5 hφy1
  rw [Subgroup.commutator_le]
  intro x hx k' hk'
  have hkN := hKN hk'
  have h1 := (L32NSet14.mem_trivSub.mp (Subgroup.mem_inf.mp hkN).2).2.2 x⁻¹ (inv_mem hx)
  rw [commutatorElement_def]
  have h3 := (Subgroup.mem_normalizer_iff.mp (hXU hx) _).mp h1
  rwa [show x * (k' * x⁻¹ * k'⁻¹ * x⁻¹⁻¹) * x⁻¹ = x * k' * x⁻¹ * k'⁻¹ by group] at h3

end CFSG.Quasithin.H13.L32A
