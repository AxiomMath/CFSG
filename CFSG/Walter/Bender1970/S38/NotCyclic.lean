module

public import CFSG.Walter.Bender1970.S38.Main
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

theorem le_of_isPerfect_of_odd_index {X : Type*} [Group X] [Finite X] {P N : Subgroup X}
    [N.Normal] (hP : Group.IsPerfect P) (hN : Odd N.index) : P ≤ N := by
  have hPP : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.mp hP
  set φ := QuotientGroup.mk' N with hφ
  have hodd : Odd (Nat.card (X ⧸ N)) := hN
  have hsolv : Group.IsSolvable (X ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  set Pb := P.map φ with hPb
  have hPbPb : ⁅Pb, Pb⁆ = Pb := by rw [hPb, ← Subgroup.map_commutator, hPP]
  have hle : ∀ k : ℕ, Pb ≤ derivedSeries (X ⧸ N) k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [derivedSeries_succ, ← hPbPb]
      exact Subgroup.commutator_mono ih ih
  obtain ⟨k, hk⟩ := hsolv.solvable
  have hbot : Pb = ⊥ := le_bot_iff.mp (hk ▸ hle k)
  rw [hPb, Subgroup.map_eq_bot_iff, hφ, QuotientGroup.ker_mk'] at hbot
  exact hbot

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_le_sylow_of_isPGroup {H : Subgroup G} (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) {V : Subgroup G} (hVH : V ≤ H) (hVp : IsPGroup 2 V) :
    ∃ h ∈ H, ∀ x ∈ V, h⁻¹ * x * h ∈ (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp' : IsPGroup 2 (V.subgroupOf H) :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
  obtain ⟨S, hS⟩ := hVp'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H (T.subtype hTH) S
  refine ⟨h, h.2, fun x hx => ?_⟩
  have hxS : (⟨x, hVH hx⟩ : H) ∈ (S : Subgroup H) := hS hx
  rw [← hh, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Sylow.coe_subtype,
    Subgroup.mem_subgroupOf] at hxS
  convert hxS using 1
  simp [MulAut.inv_def, MulAut.conj_symm_apply]

namespace BenderCounterexample

variable (hG : BenderCounterexample G)
include hG

theorem mem_inf_centralizer_of_isCyclic
    {t : G} (ht : orderOf t = 2) {H : Subgroup G}
    (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : IsComponentOf K H)
    (hWcyc : IsCyclic ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G)) :
    t ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hHA := hG.isAStar_of_isCoatom hH.1
  have hTab := hG.hasAbelianSylowTwo T
  have hKQ := hG.bender38Component' hH T htT hK
  have hWne := hG.centralizer_inf_ne_bot ht hH T htT hK
  set W := (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) with hWdef
  set Q := (T : Subgroup G) ⊓ K with hQdef
  have hW2 : 2 ∣ Nat.card W := by
    have : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hWne
    obtain ⟨k, hk⟩ := ((T.isPGroup').to_le (inf_le_left : W ≤ T)).exists_card_eq
    rw [hk]
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hk
    exact dvd_pow_self 2 hk0
  obtain ⟨w₀, hw₀⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 hW2
  have hw₀2 : orderOf (w₀ : G) = 2 := by rw [Subgroup.orderOf_coe, hw₀]
  obtain ⟨n, hnN, hnt⟩ := hG.exists_conj_of_isCyclic ht hH T htT hK hWcyc w₀.2.1 hw₀2 htT ht
  set c := MulAut.conj n with hc
  set K' := K.map c.toMonoidHom with hK'
  have hK'C : K' ≤ Subgroup.centralizer ({t} : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hnt]
    have h1 : k * w₀ = w₀ * k := Subgroup.mem_centralizer_iff.mp w₀.2.2 k hk
    simp only [MulEquiv.coe_toMonoidHom, hc, MulAut.conj_apply]
    calc n * k * n⁻¹ * (n * ↑w₀ * n⁻¹) = n * (k * w₀) * n⁻¹ := by group
      _ = n * (w₀ * k) * n⁻¹ := by rw [h1]
      _ = n * ↑w₀ * n⁻¹ * (n * k * n⁻¹) := by group
  have hK'H : K' ≤ H := hK'C.trans (centralizer_le_of_mem_benderM hH)
  have hKN : H ≤ Subgroup.normalizer (K : Set G) := fun h hh =>
    map_conj_eq_iff_mem_normalizer.mp (eq_of_isComponentOf_of_isCyclic hHA hK T hTH hTab hWcyc
      (isComponentOf_map_conj hK (Subgroup.le_normalizer hh)))
  set C := H ⊓ Subgroup.centralizer (K : Set G) with hCdef
  have hCn : ∀ h ∈ H, ∀ x ∈ C, h * x * h⁻¹ ∈ C := by
    intro h hh x hx
    refine ⟨H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh), ?_⟩
    show h * x * h⁻¹ ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : h⁻¹ * y * h ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hKN hh)) y).mp hy
      simpa using this
    have h1 := (Subgroup.mem_centralizer_iff.mp hx.2) _ hy'
    calc y * (h * x * h⁻¹) = h * ((h⁻¹ * y * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * y * h)) * h⁻¹ := by rw [h1]
      _ = h * x * h⁻¹ * y := by group
  have hCH : C ≤ H := inf_le_left
  have hCN : H ≤ Subgroup.normalizer (C : Set G) := fun h hh =>
    mem_normalizer_of_conj_mem' fun x hx => hCn h hh x hx
  have hKC : ∀ x ∈ K, x ∈ C → x ∈ (Subgroup.center K).map K.subtype := by
    intro x hxK hxC
    refine ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC.2) y y.2)
  let eK : K ≃* K' := K.equivMapOfInjective c.toMonoidHom c.injective
  have hK'q : GorensteinWalter.IsQuasisimple K' := isQuasisimple_of_mulEquiv' eK hK.2.2
  have hK'q' : CFSG.IsQuasisimple K' :=
    ⟨⟨hK'q.2.1⟩, hK'q.2.2, IsQuasisimple.exists_mul_ne_mul hK'q⟩
  have hKCH : K ⊔ C ≤ H := sup_le hK.1 hCH
  have hTKC : (T : Subgroup G) ≤ K ⊔ C := by
    intro s hs
    obtain ⟨w, hw, v, hv, rfl⟩ := exists_mul_of_mem_sylow hHA hK T hTH hs
    rw [sup_comm]
    exact Subgroup.mul_mem_sup ⟨hTH hw.1, hw.2⟩ hv.2
  have hK'KC : K' ≤ K ⊔ C := by
    set N := (K ⊔ C).subgroupOf H with hN
    have hNn : N.Normal := ⟨fun x hx g => by
      rw [hN, Subgroup.mem_subgroupOf] at hx ⊢
      have hg : (g : G) ∈ Subgroup.normalizer ((K ⊔ C : Subgroup G) : Set G) :=
        mem_normalizer_sup (hKN g.2) (hCN g.2)
      exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx⟩
    have hNodd : Odd N.index := by
      have h1 : (T : Subgroup G).subgroupOf H ≤ N := fun x hx => hTKC hx
      have h2 : N.index ∣ ((T : Subgroup G).subgroupOf H).index := Subgroup.index_dvd_of_le h1
      have h3 := (T.subtype hTH).not_dvd_index
      rw [Sylow.coe_subtype] at h3
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact fun h => h3 (h.trans h2)
    have hP : Group.IsPerfect (K'.subgroupOf H) := by
      have : Group.IsPerfect K' := ⟨hK'q.2.1⟩
      exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hK'H).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hK'H).symm.surjective
    have h := le_of_isPerfect_of_odd_index hP hNodd
    intro x hx
    have : (⟨x, hK'H hx⟩ : H) ∈ N := h hx
    exact this
  have hK'notC : ¬ K' ≤ C := by
    intro hle
    set Q' := Q.map c.toMonoidHom with hQ'
    have hQ'K' : Q' ≤ K' := Subgroup.map_mono inf_le_right
    have hQ'p : IsPGroup 2 Q' := (T.isPGroup'.to_le inf_le_left).map c.toMonoidHom
    obtain ⟨h, hh, hconj⟩ := exists_conj_le_sylow_of_isPGroup T hTH (hQ'K'.trans hK'H) hQ'p
    have hQ'card : 4 ≤ Nat.card Q' := by
      rw [hQ', Subgroup.card_map_of_injective c.injective]
      exact hKQ.four_le_card
    obtain ⟨a, ha, ha1, -⟩ := exists_mem_ne_one_ne (Q := Q') (by omega) 1
    obtain ⟨b, hb, hb1, hba⟩ := exists_mem_ne_one_ne (Q := Q') (by omega) a
    have hsq' : ∀ x ∈ Q', x ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hKQ.sq_eq_one x hx, map_one]
    have hmemW : ∀ x ∈ Q', h⁻¹ * x * h ∈ W := by
      intro x hx
      refine ⟨hconj x hx, ?_⟩
      have := (hCn h⁻¹ (H.inv_mem hh) x (hle (hQ'K' hx))).2
      simpa using this
    have hconj1 : ∀ x : G, x ≠ 1 → h⁻¹ * x * h ≠ 1 := fun x hx h1 => hx (by
      calc x = h * (h⁻¹ * x * h) * h⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    have hconjsq : ∀ x ∈ Q', (h⁻¹ * x * h) ^ 2 = 1 := fun x hx => by
      calc (h⁻¹ * x * h) ^ 2 = h⁻¹ * x ^ 2 * h := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hsq' x hx]; group
    have h1 := eq_of_sq_eq_one_of_isCyclic hWcyc (hmemW b hb) (hmemW a ha) (hconj1 b hb1)
      (hconj1 a ha1) (hconjsq b hb) (hconjsq a ha)
    apply hba
    have := congrArg (fun z => h * z * h⁻¹) h1
    simpa [mul_assoc] using this
  have hNZ : C.subgroupOf K' ≤ Subgroup.center K' := by
    have hNn : (C.subgroupOf K').Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hCn g (hK'H g.2) x hx⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hK'q' hNn with h | h
    · exfalso
      apply hK'notC
      intro x hx
      have : (⟨x, hx⟩ : K') ∈ C.subgroupOf K' := h ▸ Subgroup.mem_top _
      exact this
    · exact h
  have hK'NK : K' ≤ Subgroup.normalizer (K : Set G) := hK'H.trans hKN
  set φ' : K' →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hK'NK) with hφ'
  set φ : K →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion Subgroup.le_normalizer)
    with hφ
  have hφ'app : ∀ (x : K') (y : K), ((φ' x y : K) : G) = x * y * (x : G)⁻¹ :=
    fun x y => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hφapp : ∀ (x : K) (y : K), ((φ x y : K) : G) = x * y * (x : G)⁻¹ :=
    fun x y => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hker'C : ∀ x : K', φ' x = 1 → (x : G) ∈ C := by
    intro x hx
    refine ⟨hK'H x.2, ?_⟩
    show (x : G) ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun ψ : MulAut K => ((ψ ⟨y, hy⟩ : K) : G)) hx
    simp only [hφ'app, MulAut.one_apply] at h1
    calc y * x = x * y * (x : G)⁻¹ * x := by rw [h1]
      _ = x * y := by group
  have hker'Z : φ'.ker ≤ Subgroup.center K' := fun x hx => hNZ (hker'C x hx)
  have hkerZ : φ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hx y
      have h1 := congrArg (fun ψ : MulAut K => ((ψ y : K) : G)) hx
      simp only [hφapp, MulAut.one_apply] at h1
      apply Subtype.ext
      show (y : G) * x = x * y
      calc (y : G) * x = x * y * (x : G)⁻¹ * x := by rw [h1]
        _ = x * y := by group
    · intro hx
      ext y
      rw [hφapp, MulAut.one_apply]
      have := congrArg Subtype.val (hx y)
      simp only [Subgroup.coe_mul] at this
      rw [← this, mul_inv_cancel_right]
  have hcard' : Nat.card φ'.ker * Nat.card φ'.range = Nat.card K' := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hcard : Nat.card φ.ker * Nat.card φ.range = Nat.card K := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hK'K : Nat.card K' = Nat.card K := (Nat.card_congr eK.toEquiv).symm
  have hZZ : Nat.card (Subgroup.center K') = Nat.card (Subgroup.center K) := by
    rw [← Subgroup.map_center_eq eK, Subgroup.card_map_of_injective eK.injective]
  have hker'le : Nat.card φ'.ker ≤ Nat.card (Subgroup.center K) :=
    hZZ ▸ Subgroup.card_le_of_le hker'Z
  have hrange_le : φ'.range ≤ φ.range := by
    rintro _ ⟨x, rfl⟩
    have hx : (x : G) ∈ ((K ⊔ C : Subgroup G) : Set G) := hK'KC x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K C (hK.1.trans hCN)] at hx
    obtain ⟨k, hk, c', hc', hkc⟩ := hx
    refine ⟨⟨k, hk⟩, ?_⟩
    ext y
    rw [hφapp, hφ'app, ← hkc]
    have h1 : c' * y = y * c' := ((Subgroup.mem_centralizer_iff.mp hc'.2) y y.2).symm
    calc k * (y : G) * k⁻¹ = k * (c' * y * c'⁻¹) * k⁻¹ := by rw [h1, mul_inv_cancel_right]
      _ = k * c' * y * (k * c')⁻¹ := by group
  have hrange_eq : φ'.range = φ.range := by
    refine Subgroup.eq_of_le_of_card_ge hrange_le ?_
    have hZpos : 0 < Nat.card (Subgroup.center K) := Nat.card_pos
    have h1 : Nat.card φ.ker = Nat.card (Subgroup.center K) := by rw [hkerZ]
    rw [h1] at hcard
    rw [hK'K, ← hcard] at hcard'
    by_contra hlt
    push Not at hlt
    have := Nat.mul_lt_mul_of_le_of_lt hker'le hlt hZpos
    omega
  have hdec : ∀ k ∈ K, ∃ k' ∈ K', ∃ c' ∈ C, k = k' * c' := by
    intro k hk
    obtain ⟨x, hx⟩ : φ ⟨k, hk⟩ ∈ φ'.range := hrange_eq ▸ ⟨⟨k, hk⟩, rfl⟩
    refine ⟨x, x.2, (x : G)⁻¹ * k, ⟨H.mul_mem (H.inv_mem (hK'H x.2)) (hK.1 hk), ?_⟩, by group⟩
    show (x : G)⁻¹ * k ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun ψ : MulAut K => ((ψ ⟨y, hy⟩ : K) : G)) hx
    simp only [hφapp, hφ'app] at h1
    calc y * ((x : G)⁻¹ * k) = (x : G)⁻¹ * (x * y * (x : G)⁻¹) * k := by group
      _ = (x : G)⁻¹ * (k * y * k⁻¹) * k := by rw [h1]
      _ = (x : G)⁻¹ * k * y := by group
  have htN : t ∈ Subgroup.normalizer (K : Set G) := hKN (hTH htT)
  refine ⟨htT, mem_centralizer_of_commutator_mem_center hK.2.2.2.1 fun x hx => ?_⟩
  obtain ⟨k', hk', c', hc', rfl⟩ := hdec x hx
  have htk' : t * k' = k' * t := (Subgroup.mem_centralizer_singleton_iff.mp (hK'C hk')).symm
  have helt : t * (k' * c') * t⁻¹ * (k' * c')⁻¹ = k' * (t * c' * t⁻¹ * c'⁻¹) * k'⁻¹ := by
    calc t * (k' * c') * t⁻¹ * (k' * c')⁻¹ = (t * k') * c' * t⁻¹ * c'⁻¹ * k'⁻¹ := by group
      _ = (k' * t) * c' * t⁻¹ * c'⁻¹ * k'⁻¹ := by rw [htk']
      _ = k' * (t * c' * t⁻¹ * c'⁻¹) * k'⁻¹ := by group
  have hinC : t * (k' * c') * t⁻¹ * (k' * c')⁻¹ ∈ C := by
    rw [helt]
    exact hCn k' (hK'H hk') _ (C.mul_mem (hCn t (hTH htT) c' hc') (C.inv_mem hc'))
  have hinK : t * (k' * c') * t⁻¹ * (k' * c')⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp htN _).mp hx) (K.inv_mem hx)
  exact hKC _ hinK hinC

end BenderCounterexample

theorem bender1970_3_8_not_isCyclic
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G))
    {K : Subgroup G} (hK : IsComponentOf K H)
    (hFstar : ∀ s : G, orderOf s = 2 → ∀ M ∈ benderM s, s ∈ generalizedFittingSubgroupOf M) :
    ¬ IsCyclic ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := by
  intro hWcyc
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hHA := hG.isAStar_of_isCoatom hH.1
  have hTab := hG.hasAbelianSylowTwo T
  have hKQ := hG.bender38Component' hH T htT hK
  have hne1 : ∀ x : G, orderOf x = 2 → x ≠ 1 := fun x hx h => by
    rw [h, orderOf_one] at hx
    omega
  have htW := hG.mem_inf_centralizer_of_isCyclic ht hH T htT hK hWcyc
  have htZ := mem_center_of_isCyclic hHA hK T hTH hTab hWcyc htW ht (hFstar t ht H hH)
  obtain ⟨hHt, hMt⟩ := hG.centralizer_eq_of_central hH.1 (hne1 t ht) htZ
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have hM : ∀ s ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G), orderOf s = 2 →
      benderM s = {H} := by
    intro s hs hs2
    have hs2' : s ^ 2 = 1 := by rw [← hs2, pow_orderOf_eq_one]
    rw [eq_of_sq_eq_one_of_isCyclic hWcyc hs htW (hne1 s hs2) (hne1 t ht) hs2' ht2]
    exact hMt
  have hNT := bender1970_3_8 hG ht hH T htT hK hFstar hM
  obtain ⟨q, hq, hq1, hqt⟩ := exists_mem_ne_one_ne (Q := (T : Subgroup G) ⊓ K)
    (by have := hKQ.four_le_card; omega) t
  have hq2 : orderOf q = 2 := orderOf_eq_prime (hKQ.sq_eq_one q hq) hq1
  obtain ⟨n, hn, hnq⟩ := hG.exists_conj_of_isCyclic ht hH T htT hK hWcyc htT ht hq.1 hq2
  have hnH := hNT hn
  rw [← hHt, Subgroup.mem_centralizer_singleton_iff] at hnH
  apply hqt
  rw [← hnq]
  calc n * t * n⁻¹ = t * n * n⁻¹ := by rw [hnH]
    _ = t := by group

theorem bender1970_3_8_not_isCyclic_of_isComponentOf_layer
    (hG : BenderCounterexample G)
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G)
    (htT : t ∈ (T : Subgroup G)) {K : Subgroup G} (hK : IsComponentOf K (componentLayerOf H))
    (hFstar : ∀ s : G, orderOf s = 2 → ∀ M ∈ benderM s, s ∈ generalizedFittingSubgroupOf M) :
    ¬ IsCyclic ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :=
  bender1970_3_8_not_isCyclic hG ht hH T htT (isComponentOf_of_isSubnormal
    (componentLayerOf_isNormalIn H).1
    (isSubnormal_subgroupOf_of_isNormalIn (componentLayerOf_isNormalIn H)) hK) hFstar

end CFSG.Walter
