module

public import CFSG.Quasithin.EmptyFaithful.S1421QA27Mod
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Recognition.AS14216QO2Core

public section

namespace CFSG.Quasithin.AS14216

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.LargeExtraspecial.S63

section Lift

variable {G : Type*} [Group G]

theorem commute_of_comm_mem {k z q : G} {m : ℕ} (hm : Odd m) (hk : k ^ m = 1)
    (hkz : k * z * k⁻¹ = z) (hzz : z * z = 1) (hzq : z * q = q * z)
    (h : k * q * k⁻¹ * q⁻¹ = 1 ∨ k * q * k⁻¹ * q⁻¹ = z) : k * q = q * k := by
  rcases h with h | h
  · calc k * q = k * q * k⁻¹ * q⁻¹ * (q * k) := by group
      _ = q * k := by rw [h, one_mul]
  have h1 : k * q * k⁻¹ = z * q := by
    calc k * q * k⁻¹ = k * q * k⁻¹ * q⁻¹ * q := by group
      _ = z * q := by rw [h]
  have h2 : k ^ 2 * q * (k ^ 2)⁻¹ = q := by
    calc k ^ 2 * q * (k ^ 2)⁻¹ = k * (k * q * k⁻¹) * k⁻¹ := by
          simp only [pow_two, mul_inv_rev]; group
      _ = k * (z * q) * k⁻¹ := by rw [h1]
      _ = k * z * k⁻¹ * (k * q * k⁻¹) := by group
      _ = z * (z * q) := by rw [hkz, h1]
      _ = q := by rw [← mul_assoc, hzz, one_mul]
  have hpow : ∀ n : ℕ, (k ^ 2) ^ n * q * ((k ^ 2) ^ n)⁻¹ = q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (k ^ 2) ^ (n + 1) * q * ((k ^ 2) ^ (n + 1))⁻¹
          = (k ^ 2) ^ n * (k ^ 2 * q * (k ^ 2)⁻¹) * ((k ^ 2) ^ n)⁻¹ := by
            rw [pow_succ, mul_inv_rev]; group
        _ = q := by rw [h2, ih]
  obtain ⟨t, rfl⟩ := hm
  have hk' : k = (k ^ 2) ^ (t + 1) := by
    rw [← pow_mul]
    calc k = k ^ (2 * t + 1) * k := by rw [hk, one_mul]
      _ = k ^ (2 * (t + 1)) := by rw [← pow_succ, show 2 * (t + 1) = 2 * t + 1 + 1 by omega]
  have h4 : k * q * k⁻¹ = q := by
    rw [hk']
    exact hpow (t + 1)
  calc k * q = k * q * k⁻¹ * k := by group
    _ = q * k := by rw [h4]

end Lift

variable {G : Type} [Group G] [Finite G]

theorem conj_eq_of_center {Q : Subgroup G} {k z : G}
    (hkQ : k ∈ Subgroup.normalizer (Q : Set G)) (hzQ : z ∈ Q) (hz1 : z ≠ 1)
    (hzc : ∀ q ∈ Q, z * q = q * z)
    (hcen : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = z) : k * z * k⁻¹ = z := by
  have hkQ' : ∀ q ∈ Q, k * q * k⁻¹ ∈ Q := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp hkQ q).mp hq
  have hkQi : ∀ q ∈ Q, k⁻¹ * q * k ∈ Q := fun q hq => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkQ) q).mp hq
    simpa using this
  have hc : ∀ q ∈ Q, k * z * k⁻¹ * q = q * (k * z * k⁻¹) := by
    intro q hq
    have h1 := hzc _ (hkQi q hq)
    calc k * z * k⁻¹ * q = k * (z * (k⁻¹ * q * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * q * k) * z) * k⁻¹ := by rw [h1]
      _ = q * (k * z * k⁻¹) := by group
  rcases hcen _ (hkQ' z hzQ) hc with h | h
  · exfalso
    apply hz1
    calc z = k⁻¹ * (k * z * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  · exact h

theorem special_facts {Q : Subgroup G} (hsp : IsSpecialPow 2 2 4 ↥Q) :
    Nat.card Q = 512 ∧ ∃ z ∈ Q, z ≠ 1 ∧ z * z = 1 ∧ (∀ q ∈ Q, z * q = q * z) ∧
      (∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = z) ∧
      ∀ W : Subgroup G, W ≤ Q → W ⊔ Subgroup.zpowers z = Q → W = Q := by
  classical
  have hQ : Nat.card Q = 512 := by rw [hsp.2.1]; norm_num
  have hZ : Nat.card (Subgroup.center ↥Q) = 2 := hsp.2.2
  obtain ⟨z0, hz0, hz01⟩ := (Subgroup.bot_or_exists_ne_one (Subgroup.center ↥Q)).resolve_left
    (fun h => by rw [h, Subgroup.card_bot] at hZ; norm_num at hZ)
  have hcen0 : ∀ c ∈ Subgroup.center ↥Q, c = 1 ∨ c = z0 := fun c hc =>
    eq_one_or_eq_of_card_le_two hZ.le hz0 hz01 hc
  have hfr : frattini ↥Q = Subgroup.center ↥Q := by
    rcases hsp.1.2 with ⟨hcomm, -⟩ | ⟨-, hf, -⟩
    · exfalso
      have htop : Subgroup.center ↥Q = ⊤ := by
        ext x
        simp only [Subgroup.mem_top, iff_true]
        rw [Subgroup.mem_center_iff]
        intro y
        exact hcomm.is_comm.comm y x
      rw [htop, Subgroup.card_top, hQ] at hZ
      norm_num at hZ
    · exact hf
  refine ⟨hQ, (z0 : G), z0.2, fun h => hz01 (Subtype.ext h), ?_, fun q hq => ?_,
    fun c hc hcq => ?_, fun W hWQ hWz => ?_⟩
  · have hzz : z0 * z0 ∈ Subgroup.center ↥Q := Subgroup.mul_mem _ hz0 hz0
    rcases hcen0 _ hzz with h | h
    · exact congrArg Subtype.val h
    · exact absurd (mul_eq_left.mp h) hz01
  · have := Subgroup.mem_center_iff.mp hz0 ⟨q, hq⟩
    exact (congrArg Subtype.val this).symm
  · have hcc : (⟨c, hc⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      exact Subtype.ext (hcq q q.2).symm
    rcases hcen0 _ hcc with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  ·
    have hsup : W.subgroupOf Q ⊔ frattini ↥Q = ⊤ := by
      rw [hfr, eq_top_iff]
      rintro q -
      have hmap : W ⊔ Subgroup.zpowers (z0 : G) ≤
          (W.subgroupOf Q ⊔ Subgroup.center ↥Q).map Q.subtype := by
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hWQ]
        refine sup_le_sup le_rfl ?_
        rw [Subgroup.zpowers_le]
        exact ⟨z0, hz0, rfl⟩
      rw [hWz] at hmap
      exact (Subgroup.mem_map_iff_mem (f := Q.subtype) (Subgroup.subtype_injective _)).mp
        (hmap q.2)
    have htop := frattini_nongenerating hsup
    apply le_antisymm hWQ
    intro q hq
    have : (⟨q, hq⟩ : ↥Q) ∈ W.subgroupOf Q := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

section Main

theorem pCoreOf_le_pCoreOf_of_d4 {X K1 : Subgroup G} (hKX : K1 ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K1 : Set G)) (hct : CharTwo X)
    (hsp : IsSpecialPow 2 2 4 ↥(pCoreOf 2 X)) (hK1 : Nat.card (OTwoQuot K1) = 504)
    {Y : Type} [Group Y] (hY : IsLieOverTwo .trialityD4 0 1 Y) (ψ : ↥X →* Y)
    (hψ : Function.Injective ψ) : pCoreOf 2 X ≤ pCoreOf 2 K1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set Q := pCoreOf 2 X with hQdef
  have hQX : Q ≤ X := pCoreOf_le 2 X
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 X
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 X
  obtain ⟨hQ512, z, hzQ, hz1, hzz, hzc, hcen, hfrat⟩ := special_facts hsp
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have hXz : ∀ x ∈ X, x * z = z * x := fun x hx => by
    have h := conj_eq_of_center (hXQ hx) hzQ hz1 hzc hcen
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [h]
  have hO2K : Q ⊓ K1 ≤ pCoreOf 2 K1 := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (hQ2.to_le inf_le_left)
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hXQ (hKX hk)) g,
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) g]
  have hcK1 : Nat.card K1 = 504 * Nat.card (pCoreOf 2 K1) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥K1)
    rw [hK1] at h
    rw [h, pCoreOf, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hge : 258048 ≤ Nat.card X := by
    have hr1 := Subgroup.relIndex_mul_card (H := Q) (K := K1)
    have hr2 := Subgroup.relIndex_mul_card (H := Q) (K := X)
    rw [inf_eq_left.mpr hQX, hQ512] at hr2
    have hle : Q.relIndex K1 ≤ Q.relIndex X :=
      Subgroup.relIndex_le_of_le_right hKX
        (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
    have hcI : Nat.card ↥(Q ⊓ K1) ≤ Nat.card (pCoreOf 2 K1) := Subgroup.card_le_of_le hO2K
    have hpos : 0 < Nat.card (pCoreOf 2 K1) := Nat.card_pos
    have h504 : 504 ≤ Q.relIndex K1 := by
      by_contra hlt
      push Not at hlt
      have : Q.relIndex K1 * Nat.card ↥(Q ⊓ K1) < 504 * Nat.card (pCoreOf 2 K1) :=
        lt_of_le_of_lt (Nat.mul_le_mul_left _ hcI) (Nat.mul_lt_mul_of_pos_right hlt hpos)
      omega
    calc 258048 = 504 * 512 := by norm_num
      _ ≤ Q.relIndex X * 512 := Nat.mul_le_mul_right _ (h504.trans hle)
      _ = Nat.card X := hr2
  have hzX : z ∈ X := hQX hzQ
  obtain ⟨e⟩ := CFSG.LargeExtraspecial.S63.nonempty_equiv_trialityGroup8 Y hY
  have hzY : orderOf (ψ ⟨z, hzX⟩) = 2 := by
    rw [orderOf_injective ψ hψ]
    exact (Subgroup.orderOf_coe (⟨z, hzX⟩ : ↥X)).symm.trans hz2
  obtain ⟨e', he'⟩ := S1421QA27.exists_iso_conj e hzY
  have hfi : Function.Injective (e'.toMonoidHom.comp ψ) := e'.injective.comp hψ
  have hcard : Nat.card ((⊤ : Subgroup ↥X).map (e'.toMonoidHom.comp ψ)) = Nat.card X := by
    rw [Subgroup.card_map_of_injective hfi, Subgroup.card_top]
  have hcent : (⊤ : Subgroup ↥X).map (e'.toMonoidHom.comp ψ) ≤
      Subgroup.centralizer ({e' (ψ ⟨z, hzX⟩)} : Set ↥trialityGroup8) := by
    rintro _ ⟨x, -, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx : (⟨z, hzX⟩ : ↥X) * x = x * ⟨z, hzX⟩ := Subtype.ext (hXz x x.2).symm
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,← map_mul, ← map_mul, ← map_mul, ← map_mul, hx]
  have hfin := S1421QA27.finite_trialityGroup8
  have hle1 := Subgroup.card_le_of_le hcent
  have hX : Nat.card X = 258048 := by
    rcases he' with h | h
    · rw [h] at hle1
      have := card_centralizer_d4z_le
      omega
    · rw [h] at hle1
      have := card_centralizer_d4t_le
      omega
  set W := Q ⊓ K1 with hW
  have hWX : ∀ x ∈ X, W.map (MulAut.conj x).toMonoidHom ≤ W := by
    rintro x hx _ ⟨w, hw, rfl⟩
    obtain ⟨hwQ, hwK⟩ := Subgroup.mem_inf.mp hw
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hXQ hx) w).mp hwQ,
      (Subgroup.mem_normalizer_iff.mp (hXK hx) w).mp hwK⟩
  have hW2 : ∀ x ∈ X, ∀ w ∈ W ⊔ Subgroup.zpowers z, x * w * x⁻¹ ∈ W ⊔ Subgroup.zpowers z := by
    intro x hx w hw
    have hm : (W ⊔ Subgroup.zpowers z).map (MulAut.conj x).toMonoidHom ≤
        W ⊔ Subgroup.zpowers z := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      refine sup_le_sup (hWX x hx) (le_of_eq ?_)
      congr 1
      show x * z * x⁻¹ = z
      calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [hXz x hx]
        _ = z := by group
    exact hm ⟨w, hw, rfl⟩
  have hWQ2 : W ⊔ Subgroup.zpowers z ≤ Q :=
    sup_le inf_le_left ((Subgroup.zpowers_le).mpr hzQ)
  have hirr := S1421QA27.irred_of_embedding (S1421QA27.irredModel_of_lieModel hY) hψ hz2 hX
    hXz hQX (fun k hk q hq => (Subgroup.mem_normalizer_iff.mp (hXQ hk) q).mp hq) hQ512
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)) hWQ2 hW2
  have hQK : Q ≤ K1 := by
    rcases hirr with h | h
    ·
      exfalso
      have h7 : 7 ∣ Nat.card K1 := by
        rw [hcK1]
        exact Dvd.dvd.mul_right (by norm_num) _
      obtain ⟨k0, hk0⟩ := exists_prime_orderOf_dvd_card' (G := ↥K1) 7 h7
      set k : G := (k0 : G) with hkdef
      have hk : orderOf k = 7 := by rw [hkdef, Subgroup.orderOf_coe, hk0]
      have hkK : k ∈ K1 := k0.2
      have hk7 : k ^ 7 = 1 := hk ▸ pow_orderOf_eq_one k
      have hkz : k * z * k⁻¹ = z := by
        calc k * z * k⁻¹ = z * k * k⁻¹ := by rw [hXz k (hKX hkK)]
          _ = z := by group
      have hZ2 : ∀ c ∈ Subgroup.zpowers z, c = 1 ∨ c = z := fun c hc =>
        eq_one_or_eq_of_card_le_two (by rw [Nat.card_zpowers, hz2])
          (Subgroup.mem_zpowers z) hz1 hc
      have hcomm : ∀ q ∈ Q, k * q = q * k := by
        intro q hq
        have hmem : k * q * k⁻¹ * q⁻¹ ∈ W := by
          refine Subgroup.mem_inf.mpr ⟨Q.mul_mem
            ((Subgroup.mem_normalizer_iff.mp (hXQ (hKX hkK)) q).mp hq) (Q.inv_mem hq), ?_⟩
          have h1 : q * k⁻¹ * q⁻¹ ∈ K1 :=
            (Subgroup.mem_normalizer_iff.mp (hXK (hQX hq)) _).mp (K1.inv_mem hkK)
          have := K1.mul_mem hkK h1
          simpa [mul_assoc] using this
        have hmz : k * q * k⁻¹ * q⁻¹ ∈ Subgroup.zpowers z :=
          h ▸ Subgroup.mem_sup_left hmem
        exact commute_of_comm_mem (by decide) hk7 hkz hzz (hzc q hq) (hZ2 _ hmz)
      have hkC : k ∈ X ⊓ Subgroup.centralizer (Q : Set G) :=
        Subgroup.mem_inf.mpr ⟨hKX hkK,
          Subgroup.mem_centralizer_iff.mpr fun q hq' => (hcomm q hq').symm⟩
      have hkQ : k ∈ Q := hct hkC
      have hd : orderOf k ∣ Nat.card Q := Subgroup.orderOf_dvd_natCard Q hkQ
      rw [hk, hQ512] at hd
      norm_num at hd
    · have hWQ : W = Q := hfrat W inf_le_left h
      exact hWQ ▸ (inf_le_right : Q ⊓ K1 ≤ K1)
  exact le_pCoreOf_of_le_normalizer 2 hQK (hKX.trans hXQ) hQ2

variable {T M H K1 : Subgroup G}

end Main

end CFSG.Quasithin.AS14216
