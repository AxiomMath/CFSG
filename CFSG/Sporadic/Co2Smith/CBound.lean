module

public import CFSG.Sporadic.Co2Smith.C27S
public import CFSG.Sporadic.Co2Smith.CFinal
public import CFSG.Sporadic.Co2Smith.CSylow
public import CFSG.Sporadic.Co2Smith.C27

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open Subgroup

universe u

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem natCard_Cz :
    Nat.card Cz = 743178240 := natCard_centralizer_z0

theorem natCard_XC
    (hc : CCFacts) (i : Fin 9) : Nat.card (XC i) * Native.ccCls[(i : ℕ)]! = 743178240 := by
  rw [← (cz_classes hc).2 i, mul_comm, ncard_conjSet_mul, natCard_Cz]

theorem invEInv_mul_pCore
    {q : Cz} (hq : q ∈ CFSG.pCore 2 Cz) (m : Cz) :
    invEInv (q * m) = invEInv m := by
  have hn : (CFSG.pCore 2 Cz).Normal := CFSG.pCore_normal
  have hq' : m⁻¹ * q * m ∈ CFSG.pCore 2 Cz := by simpa using hn.conj_mem _ hq m⁻¹
  unfold invEInv
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨m⁻¹ * q * m * x, mul_mem hq' x.1.2⟩, ?_⟩
      invFun := fun x => ⟨⟨(m⁻¹ * q * m)⁻¹ * x, mul_mem (inv_mem hq') x.1.2⟩, ?_⟩
      left_inv := fun x => Subtype.ext (Subtype.ext (by
        show (m⁻¹ * q * m)⁻¹ * (m⁻¹ * q * m * x.1) = x.1
        group))
      right_inv := fun x => Subtype.ext (Subtype.ext (by
        show m⁻¹ * q * m * ((m⁻¹ * q * m)⁻¹ * x.1) = x.1
        group)) }
  · have e := x.2
    calc m * (m⁻¹ * q * m * x) * (m * (m⁻¹ * q * m * x)) = q * m * x * (q * m * x) := by group
      _ = 1 := e
  · have e := x.2
    calc q * m * ((m⁻¹ * q * m)⁻¹ * x) * (q * m * ((m⁻¹ * q * m)⁻¹ * x)) =
        m * x * (m * x) := by group
      _ = 1 := e

theorem invEInv_pCore
    (hc : CCFacts) {q : Cz} (hq : q ∈ CFSG.pCore 2 Cz) : invEInv q = 272 := by
  have h0 : cR 0 ∈ CFSG.pCore 2 Cz := by
    rw [show cR 0 = (qE 1 : Cz) from Subtype.ext (by
      show cElt 1 0 = qElt 1
      rw [cElt, sElt_zero, one_mul])]
    exact (qE 1).2
  have e1 := invEInv_mul_pCore hq 1
  have e2 := invEInv_mul_pCore h0 1
  rw [mul_one] at e1 e2
  rw [e1, ← e2]
  exact cz_invE hc 0

theorem second_of_invE
    (hc : CCFacts) {m : Cz} (hm : m * m = 1) (h80 : invEInv m = 80) :
    ∃ k < 3, ∃ h : Cz, h * m * h⁻¹ = cR (k + 3) := by
  have hm1 : m ≠ 1 := fun e => by
    rw [e, invEInv_pCore hc (one_mem _)] at h80
    exact absurd h80 (by norm_num)
  have hmz : m ≠ zCz := fun e => by
    rw [e, invEInv_pCore hc (show zCz ∈ CFSG.pCore 2 Cz from z0_mem_E)] at h80
    exact absurd h80 (by norm_num)
  obtain ⟨i, h, hh⟩ := (((cz_classes hc).1 m hm).resolve_left hm1).resolve_left hmz
  have hi : invEInv (cR i) = 80 := by rw [← hh, invEInv_conj, h80]
  rw [cz_invE hc i] at hi
  have hk : ∀ i : Fin 9, Native.ccInvE[(i : ℕ)]! = 80 → 3 ≤ (i : ℕ) ∧ (i : ℕ) < 6 := by decide
  obtain ⟨h1, h2⟩ := hk i hi
  exact ⟨i - 3, by omega, h, by rw [hh, show (i : ℕ) - 3 + 3 = i by omega]⟩

variable {G : Type u} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem cent2_le_centralizer {γ : G} : cent2 z γ ≤ centralizer ({γ} : Set G) := fun _ hx =>
  mem_centralizer_singleton_iff.mpr (mem_cent2.mp hx).2

noncomputable abbrev iC
    (φ : centralizer ({z} : Set G) ≃* Cz) (x : Cz) : G :=
  ((φ.symm x : centralizer ({z} : Set G)) : G)

theorem ccSylSize_eq {k : ℕ} (hk : k < 3) :
    ∃ n ≤ 16, Native.ccSylSize[k]! = 2 ^ n ∧
      Native.ccSylSize[k]! * (743178240 / Native.ccCls[k + 3]! / Native.ccSylSize[k]!) =
        743178240 / Native.ccCls[k + 3]! ∧
      Nat.Coprime 2 (743178240 / Native.ccCls[k + 3]! / Native.ccSylSize[k]!) := by
  interval_cases k
  · exact ⟨16, by norm_num, by decide, by decide, by decide⟩
  · exact ⟨15, by norm_num, by decide, by decide, by decide⟩
  · exact ⟨16, by norm_num, by decide, by decide, by decide⟩

theorem a2_bound
    (hc : CCFacts) (hG : SmithHyp G z) (φ : centralizer ({z} : Set G) ≃* Cz)
    (hA : ∀ g : G, ∀ ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G), ∀ h : Cz,
      h * φ ⟨_, ht⟩ * h⁻¹ ≠ cR 5)
    {k : ℕ} (hk : k < 3) {Q : Subgroup G}
    (hQx : Q ≤ centralizer ({iC φ (cR (k + 3))} : Set G)) (hQ : IsPGroup 2 Q) :
    Nat.card Q ≤ 2 ^ 16 := by
  obtain ⟨U, hUX, hUc, hzU, hZU⟩ := syl_facts hc hk
  obtain ⟨n, hn, hn2, hdiv, hcop⟩ := ccSylSize_eq hk
  have hφz := φ_zC hc hG φ
  have hcardU : Nat.card (U.map (ιM φ)) = Native.ccSylSize[k]! := by
    rw [Subgroup.card_map_of_injective (ιM_injective φ), hUc]
  have hX := cent2_eq_map φ (cR (k + 3))
  have hUx : U.map (ιM φ) ≤ centralizer ({iC φ (cR (k + 3))} : Set G) := by
    refine (Subgroup.map_mono hUX).trans ?_
    rw [← hX]
    exact cent2_le_centralizer
  have hUH : U.map (ιM φ) ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨u, -, rfl⟩
    exact ιM_mem φ u
  have h2U : IsPGroup 2 (U.map (ιM φ)) := IsPGroup.of_card (n := n) (hcardU.trans hn2)
  have hXcard : Nat.card (XC (k + 3)) = 743178240 / Native.ccCls[k + 3]! := by
    have h := natCard_XC hc ⟨k + 3, by omega⟩
    simp only at h
    have hpos : 0 < Native.ccCls[k + 3]! := by interval_cases k <;> decide
    rw [← h, Nat.mul_div_cancel _ hpos]
  refine le_trans (card_le_of_sylow hUx hUH h2U ?_ ?_ ?_ hQx hQ) (hcardU ▸ hn2 ▸
    Nat.pow_le_pow_right (by norm_num) hn)
  ·
    intro V hVx hVH hV hUV
    refine (Subgroup.eq_of_le_of_card_ge hUV ?_).symm
    set V' := V.comap (ιM φ)
    have hVV' : V'.map (ιM φ) = V := by
      refine le_antisymm (Subgroup.map_comap_le _ _) fun v hv => ?_
      refine ⟨φ ⟨v, hVH hv⟩, ?_, ιM_φ φ _⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, ιM_φ]
      exact hv
    have hcV : Nat.card V' = Nat.card V := by
      rw [← Subgroup.card_map_of_injective (ιM_injective φ), hVV']
    have hV'X : V' ≤ XC (k + 3) := fun v hv => mem_centralizer_iM φ (hVx hv)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hV
    have hdvd : Nat.card V' ∣ Nat.card (XC (k + 3)) := Subgroup.card_dvd_of_le hV'X
    rw [hcV, hb, hXcard, ← hdiv] at hdvd
    have h2 := (Nat.Coprime.pow_left b hcop).dvd_of_dvd_mul_right hdvd
    rw [hcardU, hb]
    exact Nat.le_of_dvd (by rw [hn2]; positivity) h2
  · exact ⟨zCz, hzU, ιM_zM φ hφz⟩
  · intro g hgU hcen
    by_contra hne
    obtain ⟨m, hmU, hm⟩ := hgU
    have hs : (g⁻¹)⁻¹ * z * g⁻¹ ∈ centralizer ({z} : Set G) := by
      rw [inv_inv, ← hm]
      exact ιM_mem φ m
    have hφs : φ ⟨_, hs⟩ = m := by
      have : (⟨_, hs⟩ : centralizer ({z} : Set G)) = φ.symm m := Subtype.ext (by
        show (g⁻¹)⁻¹ * z * g⁻¹ = _
        rw [inv_inv]
        exact hm.symm)
      rw [this, MulEquiv.apply_symm_apply]
    have hz2 := hG.orderOf_eq
    have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
    rcases smith_conj_classes hc hG φ g⁻¹ hs with h1 | ⟨i, hi, h, hh⟩
    · exact hne (by rwa [inv_inv] at h1)
    have hi5 : i ≠ 5 := fun e => hA g⁻¹ hs h (by rw [hh, e]; rfl)
    have hk' : ∀ i : Fin 9, i ∈ ({1, 2, 5} : Finset (Fin 9)) → i ≠ 5 →
        Native.ccInvE[(i : ℕ)]! = 32 := by decide
    have h32 : invEInv m = 32 := by
      rw [← hφs, ← invEInv_conj h, hh, cz_invE hc i]
      exact hk' i hi hi5
    refine hZU m hmU (fun u hu => ιM_injective φ ?_) ?_ (fun e => ?_) (fun e => ?_) h32
    · rw [map_mul, map_mul, hm]
      exact hcen _ ⟨u, hu, rfl⟩
    · apply ιM_injective φ
      rw [map_mul, hm, map_one]
      calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hzz]; group
    · have : g * z * g⁻¹ = 1 := by rw [← hm, e, map_one]
      have hz1 : z = 1 := by
        calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
          _ = 1 := by rw [this]; group
      rw [hz1, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    · exact hne (by rw [← hm, e, ιM_zM φ hφz])

theorem e_bound
    (hc : CCFacts) (hG : SmithHyp G z) (φ : centralizer ({z} : Set G) ≃* Cz)
    {e : centralizer ({z} : Set G)} (heE : e ∈ CFSG.pCore 2 (centralizer ({z} : Set G)))
    (he2 : e * e = 1) (he1 : e ≠ 1) (hez : e ≠ zC z) :
    ∃ Q : Subgroup G, Q ≤ centralizer ({(e : G)} : Set G) ∧ IsPGroup 2 Q ∧
      Nat.card Q = 2 ^ 17 := by
  have hφz := φ_zC hc hG φ
  have hmE : φ e ∈ CFSG.pCore 2 Cz := apply_mem_pCore_two φ heE
  have hm2 : φ e * φ e = 1 := by rw [← map_mul, he2, map_one]
  have hm1 : φ e ≠ 1 := fun h => he1 (φ.injective (h.trans (map_one φ).symm))
  have hmz : φ e ≠ zCz := fun h => hez (φ.injective (h.trans hφz.symm))
  obtain ⟨i, h, hh⟩ := (((cz_classes hc).1 (φ e) hm2).resolve_left hm1).resolve_left hmz
  have hi0 : (i : ℕ) = 0 := by
    by_contra h0
    apply cR_not_mem_pCore i.2 h0
    rw [← hh]
    exact (CFSG.pCore_normal (p := 2) (G := Cz)).conj_mem _ hmE h
  have hh0 : h * φ e * h⁻¹ = cR 0 := by rw [hh, hi0]
  have hcard : Nat.card (XC 0) = 2 ^ 17 * 21 := by
    have h1 : Nat.card (XC 0) * 270 = 743178240 := natCard_XC hc 0
    rw [show (2 : ℕ) ^ 17 * 21 = 2752512 by norm_num]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 270) (h1.trans (by norm_num))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := XC 0) 2 (n := 17)
    (by rw [hcard]; exact Dvd.intro 21 rfl)
  refine ⟨((K.map (XC 0).subtype).map (MulAut.conj h⁻¹).toMonoidHom).map (ιM φ), ?_, ?_, ?_⟩
  · rintro _ ⟨y, ⟨y', ⟨y'', -, rfl⟩, rfl⟩, rfl⟩
    rw [mem_centralizer_singleton_iff, ← ιM_φ φ e, ← map_mul, ← map_mul]
    congr 1
    have hc0 : (y'' : Cz) * cR 0 = cR 0 * y'' := mem_centralizer_singleton_iff.mp y''.2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype]
    calc h⁻¹ * (y'' : Cz) * h * φ e = h⁻¹ * ((y'' : Cz) * (h * φ e * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * φ e * h⁻¹) * y'') * h := by rw [hh0, hc0]
      _ = φ e * (h⁻¹ * y'' * h) := by group
  · refine IsPGroup.of_card (n := 17) ?_
    rw [Subgroup.card_map_of_injective (ιM_injective φ),
      Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective,
      Subgroup.card_map_of_injective (XC 0).subtype_injective, hK]
  · rw [Subgroup.card_map_of_injective (ιM_injective φ),
      Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective,
      Subgroup.card_map_of_injective (XC 0).subtype_injective, hK]

end CFSG.Sporadic.Co2Smith
