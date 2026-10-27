module

public import CFSG.Walter.Bender1970.S38.Construct
public import CFSG.Walter.Bender1970.S38.Basic
public import CFSG.Walter.Bender1970.S38.ActionMain

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace BenderCounterexample

variable (hG : BenderCounterexample G)
include hG

theorem card_eq_two_and_four
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t)
    (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) {K : Subgroup G} (hK : IsComponentOf K H)
    (hM : ∀ s ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G), orderOf s = 2 →
      benderM s = {H})
    (hN : ¬ Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ H) :
    Nat.card ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) = 2 ∧
      Nat.card ((T : Subgroup G) ⊓ K : Subgroup G) = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hHA := hG.isAStar_of_isCoatom hH.1
  have hTab := hG.hasAbelianSylowTwo T
  have hKQ := hG.bender38Component' hH T htT hK
  have hsq := hG.sq_eq_one_of_not_le hH T htT hK hM hN
  have hWne := hG.centralizer_inf_ne_bot ht hH T htT hK
  have hWQ := hG.card_centralizer_inf_le hH T htT hK hM hN
  have hKN := le_normalizer_of_card_le hHA hK T hTH hTab hWne hWQ
  set Tg := (T : Subgroup G) with hTg
  set W := Tg ⊓ Subgroup.centralizer (K : Set G) with hW
  set Q := Tg ⊓ K with hQ
  have hWQb := inf_inf_eq_bot T.isPGroup' hKQ
  have hHQ : ∀ h ∈ H, h ∈ Subgroup.normalizer (Tg : Set G) → ∀ v ∈ Q, h * v * h⁻¹ ∈ Q :=
    fun h hh hhT v hv => ⟨(Subgroup.mem_normalizer_iff.mp hhT v).mp hv.1,
      (Subgroup.mem_normalizer_iff.mp (hKN hh) v).mp hv.2⟩
  have hHW : ∀ h ∈ H, h ∈ Subgroup.normalizer (Tg : Set G) → ∀ w ∈ W, h * w * h⁻¹ ∈ W := by
    intro h hh hhT w hw
    refine ⟨(Subgroup.mem_normalizer_iff.mp hhT w).mp hw.1, ?_⟩
    show h * w * h⁻¹ ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : h⁻¹ * x * h ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hKN hh)) x).mp hx
      simpa using this
    have h1 := (Subgroup.mem_centralizer_iff.mp hw.2) _ hx'
    calc x * (h * w * h⁻¹) = h * ((h⁻¹ * x * h) * w) * h⁻¹ := by group
      _ = h * (w * (h⁻¹ * x * h)) * h⁻¹ := by rw [h1]
      _ = h * w * h⁻¹ * x := by group
  have hKNT : ∀ k ∈ K, (∀ x ∈ Q, k * x * k⁻¹ ∈ Q) → k ∈ Subgroup.normalizer (Tg : Set G) := by
    intro k hk hkQ
    refine mem_normalizer_of_conj_mem' fun s hs => ?_
    obtain ⟨w, hw, v, hv, rfl⟩ := exists_mul_of_mem_sylow hHA hK T hTH hs
    have hkw : k * w * k⁻¹ = w := by
      rw [(Subgroup.mem_centralizer_iff.mp hw.2) k hk, mul_inv_cancel_right]
    have : k * (w * v) * k⁻¹ = (k * w * k⁻¹) * (k * v * k⁻¹) := by group
    rw [this, hkw]
    exact Tg.mul_mem hw.1 (hkQ v hv).1
  let _ : CommGroup Tg := IsMulCommutative.instCommGroup
  set NT := Subgroup.normalizer (Tg : Set G) with hNT
  set φ : NT →* MulAut Tg := Tg.normalizerMonoidHom with hφ
  set Yg := φ.range with hYg
  set φ' : NT →* Yg := φ.rangeRestrict with hφ'
  have hφ's : Function.Surjective φ' := φ.rangeRestrict_surjective
  set ρ : Yg →* MulAut Tg := Yg.subtype with hρ
  have hρφ : ∀ (n : NT) (a : Tg), ((ρ (φ' n) a : Tg) : G) = (n : G) * a * (n : G)⁻¹ :=
    fun n a => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  set W' : Subgroup Tg := W.subgroupOf Tg with hW'
  set Q' : Subgroup Tg := Q.subgroupOf Tg with hQ'
  set X : Subgroup Yg := (H.subgroupOf NT).map φ' with hX
  set Nk : Subgroup Yg := ((K ⊓ Subgroup.normalizer (Q : Set G)).subgroupOf NT).map φ' with hNk
  have hmemX : ∀ n : NT, φ' n ∈ X ↔ (n : G) ∈ H := by
    intro n
    constructor
    · rintro ⟨m, hm, hmn⟩
      have hker : n * m⁻¹ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
        exact (congrArg Subtype.val hmn).symm
      rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
      have hC : ((n * m⁻¹ : NT) : G) ∈ H :=
        hG.sylow_le_centralizer T htT |> fun h' => by
          have h1 : ((n * m⁻¹ : NT) : G) ∈ Subgroup.centralizer ({t} : Set G) := by
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact (Subgroup.mem_centralizer_iff.mp hker t htT).symm
          exact centralizer_le_of_mem_benderM hH h1
      have : (n : G) = ((n * m⁻¹ : NT) : G) * m := by simp
      rw [this]
      exact H.mul_mem hC hm
    · intro h
      exact ⟨n, h, rfl⟩
  have hYodd : Odd (Nat.card Yg) := by
    have hTN : Tg ≤ NT := Subgroup.le_normalizer
    have hker : Tg.subgroupOf NT ≤ φ.ker := by
      rw [hφ, Subgroup.normalizerMonoidHom_ker]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hTab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
    have h1 : φ.ker.index = Nat.card Yg := Subgroup.index_ker φ
    have h2 : φ.ker.index ∣ (Tg.subgroupOf NT).index := Subgroup.index_dvd_of_le hker
    have h3 : (Tg.subgroupOf NT).index ∣ Tg.index := Subgroup.relIndex_dvd_index_of_le hTN
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h
    rw [← h1] at h
    exact T.not_dvd_index (h.trans (h2.trans h3))
  have hinf' : W' ⊓ Q' = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨haW, haQ⟩
    have : (a : G) ∈ W ⊓ Q := ⟨haW, haQ⟩
    rw [hWQb, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hsup' : W' ⊔ Q' = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨w, hw, v, hv, hwv⟩ := exists_mul_of_mem_sylow hHA hK T hTH a.2
    have : a = ⟨w, hw.1⟩ * ⟨v, hv.1⟩ := Subtype.ext hwv.symm
    rw [this]
    exact Subgroup.mul_mem_sup hw hv
  have hW'ne : W' ≠ ⊥ := by
    obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨⟨w, hw.1⟩, hw⟩, fun h => hw1 (Subtype.ext ?_)⟩
    exact congrArg (fun z : W' => ((z : Tg) : G)) h
  have hcardW' : Nat.card W' = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcardQ' : Nat.card Q' = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hsq' : ∀ a : Tg, a ^ 2 = 1 := fun a => Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hsq a a.2)
  have hXW : ∀ x ∈ X, ∀ w ∈ W', ρ x w ∈ W' := by
    rintro _ ⟨n, hn, rfl⟩ w hw
    show ((ρ (φ' n) w : Tg) : G) ∈ W
    rw [hρφ]
    exact hHW n hn n.2 w hw
  have hXQ : ∀ x ∈ X, ∀ v ∈ Q', ρ x v ∈ Q' := by
    rintro _ ⟨n, hn, rfl⟩ v hv
    show ((ρ (φ' n) v : Tg) : G) ∈ Q
    rw [hρφ]
    exact hHQ n hn n.2 v hv
  have hmemX' : ∀ y : Yg, ∀ w ∈ W', w ≠ 1 → ρ y w ∈ W' → y ∈ X := by
    intro y w hw hw1 hyw
    obtain ⟨n, rfl⟩ := hφ's y
    rw [hmemX]
    have hw1' : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
    have hw2 : orderOf (w : G) = 2 := orderOf_eq_prime (hsq w w.2) hw1'
    refine hG.mem_of_conj_mem_of_benderM hH.1 hM hw hw2 ?_
    have : ((ρ (φ' n) w : Tg) : G) ∈ W := hyw
    rwa [hρφ] at this
  have hNkX : Nk ≤ X := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨n, hK.1 hn.1, rfl⟩
  have hXNk : ∀ x ∈ X, ∀ n ∈ Nk, x * n * x⁻¹ ∈ Nk := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨k, hk, rfl⟩
    refine ⟨a * k * a⁻¹, ⟨?_, ?_⟩, by simp only [map_mul, map_inv]⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hKN ha) k).mp hk.1
    · have haQ : (a : G) ∈ Subgroup.normalizer (Q : Set G) :=
        mem_normalizer_of_conj_mem' (hHQ a ha a.2)
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haQ hk.2) (Subgroup.inv_mem _ haQ)
  have hNkW : ∀ n ∈ Nk, ∀ w ∈ W', ρ n w = w := by
    rintro _ ⟨k, hk, rfl⟩ w hw
    apply Subtype.ext
    have h1 : (k : G) * w = w * k := (Subgroup.mem_centralizer_iff.mp hw.2) k hk.1
    rw [hρφ, h1, mul_inv_cancel_right]
  have hNktrans : ∀ u ∈ Q', u ≠ 1 → ∀ v ∈ Q', v ≠ 1 → ∃ n ∈ Nk, ρ n u = v := by
    intro u hu hu1 v hv hv1
    obtain ⟨k, hk, hkQ, hkuv⟩ := hKQ.trans u hu (fun h => hu1 (Subtype.ext h)) v hv
      (fun h => hv1 (Subtype.ext h))
    have hkNT := hKNT k hk hkQ
    refine ⟨φ' ⟨k, hkNT⟩, ⟨⟨k, hkNT⟩, ⟨hk, mem_normalizer_of_conj_mem' hkQ⟩, rfl⟩,
      Subtype.ext ?_⟩
    rw [hρφ]
    exact hkuv
  have hcase : Nat.card Q' ≤ 8 ∨ ∃ d ∈ Nk, (∀ n ∈ Nk, ∃ m : ℕ, ∀ v ∈ Q', ρ n v = ρ (d ^ m) v) ∧
      (∀ n ∈ Nk, ∀ u ∈ Q', u ≠ 1 → ρ n u = u → ∀ v ∈ Q', ρ n v = v) := by
    by_cases h8 : Nat.card Q' ≤ 8
    · exact Or.inl h8
    right
    obtain ⟨d, hdK, hdQ, hcyc, hfree⟩ := hKQ.even (by rw [← hcardQ']; omega)
    have hdNT := hKNT d hdK hdQ
    refine ⟨φ' ⟨d, hdNT⟩, ⟨⟨d, hdNT⟩, ⟨hdK, mem_normalizer_of_conj_mem' hdQ⟩, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨k, hk, rfl⟩
      obtain ⟨m, hm⟩ := hcyc k hk.1 (fun x hx => (Subgroup.mem_normalizer_iff.mp hk.2 x).mp hx)
      refine ⟨m, fun v hv => Subtype.ext ?_⟩
      rw [← map_pow, hρφ, hρφ]
      simpa using hm v hv
    · rintro _ ⟨k, hk, rfl⟩ u hu hu1 hku v hv
      apply Subtype.ext
      rw [hρφ]
      refine hfree k hk.1 (fun x hx => (Subgroup.mem_normalizer_iff.mp hk.2 x).mp hx) u hu
        (fun h => hu1 (Subtype.ext h)) ?_ v hv
      have := congrArg Subtype.val hku
      rwa [hρφ] at this
  obtain ⟨R, hRX, hRn, hRcyc, hRW, hRfree, hRtrans⟩ := exists_regular_subgroup
    Yg.subtype_injective hYodd hsq' hsup' (by rw [hcardQ']; exact hKQ.four_le_card) hXQ hNkX
    hXNk hNkW hNktrans hcase
  have hD : Bender38Action ρ W' Q' X R :=
    { sq_eq_one := hsq'
      injective := Yg.subtype_injective
      odd_card := hYodd
      inf_eq_bot := hinf'
      sup_eq_top := hsup'
      ne_bot := hW'ne
      four_le_card := by rw [hcardQ']; exact hKQ.four_le_card
      map_mem_W := hXW
      mem_X := hmemX'
      map_mem_Q := hXQ
      le_X := hRX
      conj_mem := hRn
      isCyclic := hRcyc
      fix_W := hRW
      free := hRfree
      trans := hRtrans }
  have hXY : X ≠ ⊤ := by
    intro htop
    apply hN
    intro n hn
    exact (hmemX ⟨n, hn⟩).mp (htop ▸ Subgroup.mem_top _)
  obtain ⟨h1, h2⟩ := hD.card_eq_of_ne_top hXY
  exact ⟨hcardW' ▸ h1, hcardQ' ▸ h2⟩

end BenderCounterexample

end CFSG.Walter
