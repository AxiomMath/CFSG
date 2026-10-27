module

public import CFSG.Quasithin.H13.L32A770b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem perm5_comm_two_elt : ∀ c σ : Equiv.Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 → σ ^ 4 = 1 →
    σ ≠ 1 → Equiv.Perm.sign σ = 1 → c * σ = σ * c → False := by
  decide +kernel

theorem exists_x3_l1 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    ∃ x ∈ L₁Of L (fsuV1 T V), x ^ 3 = 1 ∧ x ≠ 1 := by
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz0, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis
  have hzV₂ : z ∈ V₂ := hV2.1 hz0
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
  have haV' : a ∈ V := hV2.2.1 ha
  obtain ⟨x, hxL0, hx3, hxz, hxa, -⟩ := S14.exists_rot hzV haV' hb
    (fun h => haV (h ▸ one_mem _)) (fun h => hbV (h ▸ one_mem _))
    (fun h => haV (h ▸ hz0)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ ha))
    (fun h => hbV (h ▸ mul_mem hzV₂ ha))
  have hxa' : x * a * x⁻¹ ≠ a := by
    rw [hxa]
    exact fun h => hbV (h ▸ ha)
  exact ⟨x, Subgroup.subset_closure ⟨⟨hxL0, S14.mem_g1 hz0 hz1 hxz⟩, 3, by decide, hx3⟩, hx3,
    fun h => hxa' (by rw [h]; group)⟩

omit [Finite G] in
theorem eq_one_of_pow_three_of_isPGroup {X : Subgroup G} (hX : IsPGroup 2 ↥X) {x : G}
    (hxX : x ∈ X) (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨n, hn⟩ := hX ⟨x, hxX⟩
  have h2 : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hd1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have hd2 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have h1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact orderOf_eq_one_iff.mp h1

theorem exists_pow_conj_mem (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {x : G} (hxL1 : x ∈ L₁Of L (fsuV1 T V)) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {s r : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) (hr : r ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hrQ : r ∉ pCoreOf 2 (hz T V)) :
    ∃ i : ℕ, i < 3 ∧ r⁻¹ * (x ^ i * s * (x ^ i)⁻¹) ∈ pCoreOf 2 (hz T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  obtain ⟨-, hR4⟩ := R1_le_kz_sup S0 hF h63 h1222 h1332 h1334
  obtain ⟨φ, -, hφk⟩ := exists_phi h h63
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hRdef
  set Q := pCoreOf 2 (hz T V) with hQdef
  have hRH : R ≤ hz T V := (pCoreOf_le_of_le h le_sup_right).trans hF.T_le_H
  have hxH : x ∈ hz T V := oTwoUpper_le _ (l1_le_kz h hMod hxL1)
  have hxQ : x ∉ Q := fun hxQ => hx1 (eq_one_of_pow_three_of_isPGroup
    (pCoreOf_isPGroup 2 _) hxQ hx3)
  have hxR : x ∈ Subgroup.normalizer (R : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hxL1)
  have hφ1 : ∀ (a : G) (ha : a ∈ hz T V), φ ⟨a, ha⟩ = 1 ↔ a ∈ Q := fun a ha => by
    rw [← MonoidHom.mem_ker, hφk, ← mem_pCoreOf_iff']
  set N := (R.subgroupOf (hz T V)).map φ with hN
  have hN4 : Nat.card ↥N = 4 := by rw [card_map_phi hφk hRH, hR4]
  have hmemN : ∀ (a : G) (ha : a ∈ R), φ ⟨a, hRH ha⟩ ∈ N := fun a ha =>
    ⟨⟨a, hRH ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  set c := φ ⟨x, hxH⟩ with hc
  have hc3 : c ^ 3 = 1 := by
    rw [hc, ← map_pow]
    have : (⟨x, hxH⟩ : ↥(hz T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hc1 : c ≠ 1 := fun e => hxQ ((hφ1 x hxH).mp e)
  have hxi : ∀ i : ℕ, x ^ i * s * (x ^ i)⁻¹ ∈ R := fun i =>
    (Subgroup.mem_normalizer_iff.mp (pow_mem hxR i) s).mp hs
  have hφxi : ∀ i : ℕ, φ ⟨x ^ i * s * (x ^ i)⁻¹, hRH (hxi i)⟩ = c ^ i * φ ⟨s, hRH hs⟩ * (c ^ i)⁻¹ := by
    intro i
    have e : (⟨x ^ i * s * (x ^ i)⁻¹, hRH (hxi i)⟩ : ↥(hz T V)) =
        ⟨x, hxH⟩ ^ i * ⟨s, hRH hs⟩ * (⟨x, hxH⟩ ^ i)⁻¹ := Subtype.ext (by simp)
    rw [e, map_mul, map_mul, map_inv, map_pow]
  set σ := φ ⟨s, hRH hs⟩ with hσ
  have hσ1 : σ ≠ 1 := fun e => hsQ ((hφ1 s (hRH hs)).mp e)
  have hσN : σ ∈ N := hmemN s hs
  have hσ4 : σ ^ 4 = 1 := by
    have h1 := orderOf_dvd_natCard (⟨σ, hσN⟩ : ↥N)
    rw [hN4] at h1
    have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
    simpa using congrArg Subtype.val h2
  have hσsign : Equiv.Perm.sign σ = 1 :=
    sign_phi_of_card_four hφk hRH hR4 hxH hx3 hxQ hxR hs
  have hcσ : c * σ ≠ σ * c := fun e => perm5_comm_two_elt c σ hc3 hc1 hσ4 hσ1 hσsign e
  have hc2_3 : (c ^ 2) ^ 3 = 1 := by rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hc3,
    one_pow]
  have hc2_1 : c ^ 2 ≠ 1 := by
    intro e
    apply hc1
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, e]; group
  have hc2σ : c ^ 2 * σ ≠ σ * c ^ 2 :=
    fun e => perm5_comm_two_elt (c ^ 2) σ hc2_3 hc2_1 hσ4 hσ1 hσsign e
  have hd01 : σ ≠ c * σ * c⁻¹ := fun e => hcσ (by
    calc c * σ = c * σ * c⁻¹ * c := by group
      _ = σ * c := by rw [← e])
  have hd02 : σ ≠ c ^ 2 * σ * (c ^ 2)⁻¹ := fun e => hc2σ (by
    calc c ^ 2 * σ = c ^ 2 * σ * (c ^ 2)⁻¹ * c ^ 2 := by group
      _ = σ * c ^ 2 := by rw [← e])
  have hd12 : c * σ * c⁻¹ ≠ c ^ 2 * σ * (c ^ 2)⁻¹ := fun e => hd01 (by
    calc σ = c⁻¹ * (c * σ * c⁻¹) * c := by group
      _ = c⁻¹ * (c ^ 2 * σ * (c ^ 2)⁻¹) * c := by rw [e]
      _ = c * σ * c⁻¹ := by group)
  have h1N : (1 : Equiv.Perm (Fin 5)) ∈ N := one_mem N
  have hσ1N : c * σ * c⁻¹ ∈ N := by
    have := hmemN _ (hxi 1)
    rwa [hφxi 1, pow_one] at this
  have hσ2N : c ^ 2 * σ * (c ^ 2)⁻¹ ∈ N := by
    have := hmemN _ (hxi 2)
    rwa [hφxi 2] at this
  have hne1 : c * σ * c⁻¹ ≠ 1 := fun e => hσ1 (by
    calc σ = c⁻¹ * (c * σ * c⁻¹) * c := by group
      _ = 1 := by rw [e]; group)
  have hne2 : c ^ 2 * σ * (c ^ 2)⁻¹ ≠ 1 := fun e => hσ1 (by
    calc σ = (c ^ 2)⁻¹ * (c ^ 2 * σ * (c ^ 2)⁻¹) * c ^ 2 := by group
      _ = 1 := by rw [e]; group)
  have hnd : [1, σ, c * σ * c⁻¹, c ^ 2 * σ * (c ^ 2)⁻¹].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      not_false_eq_true, and_true, not_or]
    exact ⟨⟨hσ1.symm, hne1.symm, hne2.symm⟩, ⟨hd01, hd02⟩, hd12⟩
  have hsub : (↑([1, σ, c * σ * c⁻¹, c ^ 2 * σ * (c ^ 2)⁻¹].toFinset) :
      Set (Equiv.Perm (Fin 5))) ⊆ (N : Set (Equiv.Perm (Fin 5))) := by
    intro y hy
    simp only [List.coe_toFinset, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_ofPred_eq] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact h1N
    · exact hσN
    · exact hσ1N
    · exact hσ2N
  have hcardS : (↑([1, σ, c * σ * c⁻¹, c ^ 2 * σ * (c ^ 2)⁻¹].toFinset) :
      Set (Equiv.Perm (Fin 5))).ncard = 4 := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
    rfl
  have hcardN : (N : Set (Equiv.Perm (Fin 5))).ncard = 4 := hN4
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcardN, hcardS]) (Set.toFinite _)
  have hρN : φ ⟨r, hRH hr⟩ ∈ (N : Set (Equiv.Perm (Fin 5))) := hmemN r hr
  rw [← heq] at hρN
  simp only [List.coe_toFinset, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_ofPred_eq] at hρN
  have hρ1 : φ ⟨r, hRH hr⟩ ≠ 1 := fun e => hrQ ((hφ1 r (hRH hr)).mp e)
  have key : ∀ i : ℕ, φ ⟨r, hRH hr⟩ = c ^ i * σ * (c ^ i)⁻¹ →
      r⁻¹ * (x ^ i * s * (x ^ i)⁻¹) ∈ Q := by
    intro i hi
    have hm : r⁻¹ * (x ^ i * s * (x ^ i)⁻¹) ∈ hz T V :=
      mul_mem (inv_mem (hRH hr)) (hRH (hxi i))
    refine (hφ1 _ hm).mp ?_
    have e : (⟨r⁻¹ * (x ^ i * s * (x ^ i)⁻¹), hm⟩ : ↥(hz T V)) =
        (⟨r, hRH hr⟩)⁻¹ * ⟨x ^ i * s * (x ^ i)⁻¹, hRH (hxi i)⟩ := rfl
    rw [e, map_mul, map_inv, hφxi i, hi, inv_mul_cancel]
  rcases hρN with e | e | e | e
  · exact absurd e hρ1
  · exact ⟨0, by norm_num, key 0 (by rw [e]; simp)⟩
  · exact ⟨1, by norm_num, key 1 (by rw [e, pow_one])⟩
  · exact ⟨2, by norm_num, key 2 e⟩

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem mem_or_mul_mem (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) {s : G} (hsW : s ∈ conjSub ((k : G) * g) (fsuU T V))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) :
    ∀ w ∈ conjSub ((k : G) * g) (fsuU T V),
      w ∈ pCoreOf 2 (hz T V) ∨ s⁻¹ * w ∈ pCoreOf 2 (hz T V) := by
  have hWN := N.uα_le_normalizer h hF
  rw [A4.relIndex_sup_eq_of_le_normalizer' hWN] at h2
  rw [uα_eq (g := g) (k := k) h hMod] at h2
  intro w hw
  by_cases hwQ : w ∈ pCoreOf 2 (hz T V)
  · exact Or.inl hwQ
  · right
    have key := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨s, hsW⟩ : ↥(conjSub ((k : G) * g)
      (fsuU T V)))⁻¹) (b := ⟨w, hw⟩)).mpr
    have h3 := key ⟨fun h' => absurd (by
      have := inv_mem (Subgroup.mem_subgroupOf.mp h')
      simpa using this) hsQ, fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hwQ⟩
    rw [Subgroup.mem_subgroupOf] at h3
    simpa using h3

theorem exists_central (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    ∃ k' : ↥((L ⊔ T) ⊔ hz T V), Not1471 T L V (hz T V) γ γ' g k' ∧
      ∃ s ∈ conjSub ((k' : G) * g) (fsuU T V), s ∉ pCoreOf 2 (hz T V) ∧
        ∀ t ∈ T, t * s * t⁻¹ * s⁻¹ ∈ pCoreOf 2 (hz T V) := by
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  obtain ⟨-, hR4⟩ := R1_le_kz_sup S0 hF h63 h1222 h1332 h1334
  obtain ⟨s₀, hs₀W, hs₀Q, -⟩ := N.exists_mem_not_mem h hMod hF h2
  have hWR : conjSub ((k : G) * g) (fsuU T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    rw [← uα_eq (g := g) (k := k) h hMod]
    exact N.uα_le hF
  have hTH : T ≤ hz T V := hF.T_le_H
  have hQR := pCoreOf_hz_le_R1 h hF
  have hlt : pCoreOf 2 (hz T V) < pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    refine lt_of_le_of_ne hQR fun e => ?_
    rw [e, Subgroup.relIndex_self] at hR4
    exact absurd hR4 (by norm_num)
  obtain ⟨r, hrR, hrQ, hrT⟩ := exists_fixed_mod hF.sylow.2.1 (pCoreOf_le_of_le h le_sup_right)
    hlt (le_sup_right.trans (le_normalizer_pCoreOf 2 _))
    (hTH.trans (le_normalizer_pCoreOf 2 _))
  obtain ⟨x, hxL1, hx3, hx1⟩ := exists_x3_l1 h hMod h1222 h1332 h1334
  obtain ⟨i, -, hi⟩ := exists_pow_conj_mem h hMod h63 hF h1222 h1332 h1334 hxL1 hx3 hx1
    (hWR hs₀W) hs₀Q hrR hrQ
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  have hxH : x ∈ hz T V := oTwoUpper_le _ (l1_le_kz h hMod hxL1)
  set l := x ^ i with hl
  have hlL : l ∈ L := pow_mem hxL i
  have hlH : l ∈ hz T V := pow_mem hxH i
  refine ⟨_, N.mul_left hF hlL hlH, l * s₀ * l⁻¹, ?_, ?_, fun t ht => ?_⟩
  · rw [Subgroup.coe_mul, mul_assoc, conjSub_mul]
    exact mul_mem_conjSub hs₀W
  · intro hm
    apply hs₀Q
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hlH) s₀).mpr hm
    exact this
  ·
    have htH := hTH ht
    set q := r⁻¹ * (l * s₀ * l⁻¹) with hq
    have hqQ : q ∈ pCoreOf 2 (hz T V) := hi
    have hs : l * s₀ * l⁻¹ = r * q := by rw [hq]; group
    have hrH : r ∈ hz T V := ((pCoreOf_le_of_le h le_sup_right).trans hTH) hrR
    have h1 := hrT t ht
    have h2' : t * q * t⁻¹ * q⁻¹ ∈ pCoreOf 2 (hz T V) :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ htH) q).mp hqQ)
        (inv_mem hqQ)
    have h3 : r * (t * q * t⁻¹ * q⁻¹) * r⁻¹ ∈ pCoreOf 2 (hz T V) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hrH) _).mp h2'
    rw [hs, show t * (r * q) * t⁻¹ * (r * q)⁻¹ =
      (t * r * t⁻¹ * r⁻¹) * (r * (t * q * t⁻¹ * q⁻¹) * r⁻¹) by group]
    exact mul_mem h1 h3

end Not1471

end CFSG.Quasithin.H13.L32A
