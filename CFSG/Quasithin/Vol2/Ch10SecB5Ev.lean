module

public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Vol2.Ch10SecBXi

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem mem_T1_of_comm (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) {y : G} (hy : y ∈ T)
    (hc : ∀ x ∈ XOf T L Ψ A, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 (XOf T L Ψ A)) : y ∈ T1 T L := by
  by_contra hyT1
  have hyN : y ∉ Subgroup.normalizer (L : Set G) := fun hN => hyT1 ⟨hy, hN⟩
  obtain ⟨k, hkK, hkE⟩ : ∃ k ∈ K, k ∉ E := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show K ≤ E from fun k hk => hcon k hk)
    rw [hD.cardK, hD.cardE] at this
    omega
  have hmem : ((1 : L32.Γ), k) ∈ imgIn Ψ (XOf T L Ψ A) := by
    rw [imgIn_XOf h hD]
    exact ⟨K.one_mem, hkK⟩
  obtain ⟨x, hxL0, hxX, hΨx⟩ := mem_imgIn.mp hmem
  have hs : y * t ∈ T1 T L := by
    refine ⟨T.mul_mem hy h.ht, ?_⟩
    have h1 := SecA.mul_inv_mem_normalizer h.h37 h.h38 h.hyp h.ht h.htn hy hyN
    have h2 := SecA.mul_self_mem_normalizer h.h37 h.h38 h.hyp h.ht h.htn
    have := Subgroup.mul_mem _ h1 h2
    simpa [mul_assoc] using this
  obtain ⟨u, v, -, -, huv⟩ := h.hC.T1act _ hs
  have hM : ∀ g ∈ T, ∀ z ∈ fsuL0 T L, g * z * g⁻¹ ∈ fsuL0 T L := fun g hg z hz =>
    (Subgroup.mem_normalizer_iff.mp (SecA.le_fsuM T L hg) z).mp hz
  have hz : t⁻¹ * x * t ∈ fsuL0 T L := by
    have := hM _ (T.inv_mem h.ht) x hxL0
    simpa using this
  have hsz : y * t * (t⁻¹ * x * t) * (y * t)⁻¹ ∈ fsuL0 T L := hM _ (T.mul_mem hy h.ht) _ hz
  have h1 := h.hC.swap ⟨x, hxL0⟩ hz
  have h2 := huv ⟨t⁻¹ * x * t, hz⟩ hsz
  have hO := hc x hxX
  rw [pCoreOf_XOf h hD] at hO
  obtain ⟨hOL0, hOE⟩ := mem_preIn.mp hO.2
  have h3 : (⟨y * x * y⁻¹ * x⁻¹, hOL0⟩ : ↥(fsuL0 T L)) =
      ⟨y * t * (t⁻¹ * x * t) * (y * t)⁻¹, hsz⟩ * (⟨x, hxL0⟩ : ↥(fsuL0 T L))⁻¹ :=
    Subtype.ext (by simp [mul_assoc])
  rw [h3, map_mul, map_inv, h2, h1, hΨx] at hOE
  have h4 := hOE.2
  simp only [Prod.snd_mul, Prod.snd_inv, mul_one, mul_inv_cancel, one_mul] at h4
  exact hkE (by simpa using E.inv_mem h4)

theorem pCoreOf_sup_le (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) {Kc : Subgroup G}
    (hXK : XOf T L Ψ A ≤ Kc) (hS : IsSylowTwoOf (T ⊓ Kc) Kc) :
    pCoreOf 2 (XOf T L Ψ A ⊔ T ⊓ Kc) ≤ T1 T L ⊓ Kc := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := XOf T L Ψ A with hXdef
  set Y := X ⊔ T ⊓ Kc with hYdef
  have hSY : IsSylowTwoOf (T ⊓ Kc) Y :=
    B6.isSylowTwoOf_mono hS le_sup_right (sup_le hXK inf_le_right)
  have hWS : pCoreOf 2 Y ≤ T ⊓ Kc := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hSY
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := (isXi_XOf h hD).2.1
  have hWX : pCoreOf 2 Y ⊓ X ≤ pCoreOf 2 X := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le inf_le_left)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 := Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y (Subgroup.mem_sup_left hx)) z
    have h2 : z ∈ X ↔ x * z * x⁻¹ ∈ X := by
      constructor
      · intro hz
        exact X.mul_mem (X.mul_mem hx hz) (X.inv_mem hx)
      · intro hz
        have := X.mul_mem (X.mul_mem (X.inv_mem hx) hz) hx
        simpa [mul_assoc] using this
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  intro w hw
  refine ⟨mem_T1_of_comm h hD (hWS hw).1 fun x hx => hWX ⟨?_, ?_⟩, (hWS hw).2⟩
  ·
    have hwi : x * w⁻¹ * x⁻¹ ∈ pCoreOf 2 Y :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y (Subgroup.mem_sup_left hx)) _).mp
        ((pCoreOf 2 Y).inv_mem hw)
    have := (pCoreOf 2 Y).mul_mem hw hwi
    simpa [mul_assoc] using this
  ·
    have hwx : w * x * w⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hTX (hWS hw).1) x).mp hx
    exact X.mul_mem hwx (X.inv_mem hx)

theorem eq_closure_three (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) {Kc : Subgroup G}
    (hXK : XOf T L Ψ A ≤ Kc)
    (h3 : ∀ g ∈ Kc ⊓ Subgroup.normalizer (pCoreOf 2 (XOf T L Ψ A ⊔ T ⊓ Kc) : Set G),
      orderOf g = 3 → g ∈ XOf T L Ψ A) :
    XOf T L Ψ A = Subgroup.closure {g | g ∈ Kc ⊓
      Subgroup.normalizer (pCoreOf 2 (XOf T L Ψ A ⊔ T ⊓ Kc) : Set G) ∧ orderOf g = 3} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun g hg => h3 g hg.1 hg.2)
  have hX : XOf T L Ψ A = oTwoUpper (XOf T L Ψ A) := (oTwoUpper_oTwoUpper' _).symm
  conv_lhs => rw [hX]
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨hxX, hodd⟩ := hx
  have hx3 : x ^ 3 = 1 := by
    have hO := pow_three_mem h hD hxX
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (XOf T L Ψ A)) ⟨_, hO⟩
    rw [Subgroup.orderOf_mk] at hn
    have hd : orderOf (x ^ 3) ∣ orderOf x := orderOf_pow_dvd 3
    rw [hn] at hd
    have h1 : 2 ^ n = 1 := by
      rcases n with _ | n
      · rfl
      · exfalso
        have h2 : 2 ∣ orderOf x := (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hd
        exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h2)
    rw [h1, orderOf_eq_one_iff] at hn
    exact hn
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx3) with h1 | h1
  · rw [orderOf_eq_one_iff] at h1
    rw [h1]
    exact Subgroup.one_mem _
  · refine Subgroup.subset_closure ⟨⟨hXK hxX, ?_⟩, h1⟩
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hxX)

theorem normalizer_T1_le_of_weakClosed (h : MaxCtx T L I t Ψ c) (hD : ParData A K E)
    {Kc : Subgroup G} (hXK : XOf T L Ψ A ≤ Kc) (hS : IsSylowTwoOf (T ⊓ Kc) Kc)
    (hNK : Subgroup.normalizer (T1 T L : Set G) ≤ Subgroup.normalizer (Kc : Set G))
    (hwc : ∀ g ∈ Subgroup.normalizer (Kc : Set G),
      (pCoreOf 2 (XOf T L Ψ A ⊔ T ⊓ Kc)).map (MulAut.conj g).toMonoidHom ≤ T ⊓ Kc →
        (pCoreOf 2 (XOf T L Ψ A ⊔ T ⊓ Kc)).map (MulAut.conj g).toMonoidHom =
          pCoreOf 2 (XOf T L Ψ A ⊔ T ⊓ Kc))
    (h3 : ∀ g ∈ Kc ⊓ Subgroup.normalizer (pCoreOf 2 (XOf T L Ψ A ⊔ T ⊓ Kc) : Set G),
      orderOf g = 3 → g ∈ XOf T L Ψ A) :
    Subgroup.normalizer (T1 T L : Set G) ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) := by
  set W := pCoreOf 2 (XOf T L Ψ A ⊔ T ⊓ Kc) with hWdef
  intro n hn
  have hnK := hNK hn
  have hnK' : Kc.map (MulAut.conj n).toMonoidHom = Kc := by
    rw [MulEquiv.toMonoidHom_eq_coe]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hnK
  have hnT1 : (T1 T L).map (MulAut.conj n).toMonoidHom = T1 T L := by
    rw [MulEquiv.toMonoidHom_eq_coe]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hnW : n ∈ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
    refine hwc n hnK ?_
    calc W.map (MulAut.conj n).toMonoidHom ≤ (T1 T L ⊓ Kc).map (MulAut.conj n).toMonoidHom :=
          Subgroup.map_mono (pCoreOf_sup_le h hD hXK hS)
      _ ≤ (T1 T L).map (MulAut.conj n).toMonoidHom ⊓ Kc.map (MulAut.conj n).toMonoidHom :=
          Subgroup.map_inf_le _ _ _
      _ = T1 T L ⊓ Kc := by rw [hnT1, hnK']
      _ ≤ T ⊓ Kc := inf_le_inf_right _ inf_le_left
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
  have hX := eq_closure_three h hD hXK h3
  have hle : (XOf T L Ψ A).map (MulAut.conj n).toMonoidHom ≤ XOf T L Ψ A := by
    rw [hX, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨g, ⟨⟨hgK, hgW⟩, hg3⟩, rfl⟩
    refine ⟨?_, by rw [orderOf_injective _ (MulAut.conj n).injective]; exact hg3⟩
    have e : (MulAut.conj n).toMonoidHom g = n * g * n⁻¹ := by simp [MulAut.conj_apply]
    rw [e]
    exact ⟨(Subgroup.mem_normalizer_iff.mp hnK g).mp hgK, (Subgroup.normalizer _).mul_mem
      ((Subgroup.normalizer _).mul_mem hnW hgW) ((Subgroup.normalizer _).inv_mem hnW)⟩
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj n).injective).ge

end CFSG.Quasithin.Vol2.Ch10.SecB
