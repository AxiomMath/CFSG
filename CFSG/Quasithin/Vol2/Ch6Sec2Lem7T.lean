module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7T2
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7Q
public import CFSG.Quasithin.H13.U3S1348H
public import CFSG.Quasithin.Vol2.Ch11SecD556A
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11B
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11F
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD

section PartB

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement Pointwise

theorem res627T_of (hG31 : Ch6G31O2) : Res627T := by
  intro G _ _ T M L V h t A D g ht hf U H UH R LU B a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 hBU
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUUH, hUHH, hHUH, hHU, -, hO2t⟩ := a13
  have hUHc : ∀ a ∈ UH, ∀ b ∈ UH, a * b = b * a := fun a ha b hb => B2F.isElemAbelian_comm a9 ha hb
  have hnorm : (U.subgroupOf UH).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have e : ((y * x * y⁻¹ : ↥UH) : G) = (x : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hUHc _ y.2 _ x.2, mul_inv_cancel_right]
    rw [e]
    exact hx
  have hcomm : CommModCh611 UH U := ⟨fun a ha b hb => by
    rw [hUHc a ha b hb, mul_inv_cancel_right, mul_inv_cancel]
    exact U.one_mem⟩
  set Q := ↥UH ⧸ U.subgroupOf UH with hQdef
  have hQsq : ∀ x : Q, x ^ 2 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [← QuotientGroup.mk_pow, show u ^ 2 = 1 from Subtype.ext (by simpa using a9.2 u u.2),
        QuotientGroup.mk_one]
  have : Finite (MulAut Q) :=
    Finite.of_injective (fun g : MulAut Q => (g : Q → Q)) DFunLike.coe_injective
  have hDL : D ≤ L := a31.trans ((oTwoUpper_le _).trans inf_le_left)
  have hDNU : D ≤ Subgroup.normalizer (U : Set G) := a31.trans ((oTwoUpper_le _).trans inf_le_right)
  have hDNV : D ≤ Subgroup.normalizer (V : Set G) := hDL.trans h.toHyp611.L_le_normalizer
  have hDNH : D ≤ Subgroup.normalizer (H : Set G) := fun d hd =>
    mem_normalizer_centralizer_ch62 (hDNU hd)
  have hDNUH : D ≤ Subgroup.normalizer (UH : Set G) := fun d hd =>
    mem_normalizer_conjClosure_ch62 (hDNV hd) (hDNH hd)
  have hD3 : ∀ d ∈ D, d ^ 3 = 1 := by
    intro d hd
    have := Subgroup.orderOf_dvd_natCard D hd
    rw [a32] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  set HD := H ⊔ D with hHDdef
  have hHDUH : HD ≤ Subgroup.normalizer (UH : Set G) := sup_le hHUH hDNUH
  have hHDU : HD ≤ Subgroup.normalizer (U : Set G) := sup_le hHU hDNU
  set ρ := actQuot UH U H hHUH hHU with hρ
  set ρ' := actQuot UH U HD hHDUH hHDU with hρ'
  set Gm := ρ.range with hGm
  set Gm' := ρ'.range with hGm'
  have hρρ' : ∀ (x : G) (hx : x ∈ H), ρ ⟨x, hx⟩ = ρ' ⟨x, (le_sup_left : H ≤ HD) hx⟩ :=
    fun x hx => rfl
  have hGmGm' : Gm ≤ Gm' := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact ⟨⟨x, (le_sup_left : H ≤ HD) hx⟩, rfl⟩
  have hconjρ : ∀ (y : G) (hy : y ∈ HD) (x : G) (hx : x ∈ H) (hyx : y * x * y⁻¹ ∈ H),
      ρ' ⟨y, hy⟩ * ρ ⟨x, hx⟩ * (ρ' ⟨y, hy⟩)⁻¹ = ρ ⟨y * x * y⁻¹, hyx⟩ := by
    intro y hy x hx hyx
    rw [hρρ' x hx, hρρ' _ hyx, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hHDNH : HD ≤ Subgroup.normalizer (H : Set G) := sup_le Subgroup.le_normalizer hDNH
  have hNGm : ∀ (y : G) (hy : y ∈ HD), ρ' ⟨y, hy⟩ ∈ Subgroup.normalizer (Gm : Set (MulAut Q)) := by
    intro y hy
    have key : ∀ (y : G) (hy : y ∈ HD), ∀ z ∈ Gm, ρ' ⟨y, hy⟩ * z * (ρ' ⟨y, hy⟩)⁻¹ ∈ Gm := by
      rintro y hy _ ⟨⟨x, hx⟩, rfl⟩
      have hyx : y * x * y⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hHDNH hy) x).mp hx
      rw [hconjρ y hy x hx hyx]
      exact ⟨_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨key y hy z, fun hz => ?_⟩
    have h1 := key y⁻¹ (HD.inv_mem hy) _ hz
    have e : ρ' ⟨y⁻¹, HD.inv_mem hy⟩ = (ρ' ⟨y, hy⟩)⁻¹ := by rw [← map_inv]; rfl
    rw [e, inv_inv] at h1
    simpa [mul_assoc] using h1
  have hcoe : ((HD : Subgroup G) : Set G) = (H : Set G) * (D : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H D hDNH
  have hstar : ∀ x ∈ Gm', (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ Gm := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩ ⟨k, hk⟩
    have hy' : y ∈ (H : Set G) * (D : Set G) := hcoe ▸ hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    have hbHD : b ∈ HD := (le_sup_right : D ≤ HD) hb
    have e : ρ' ⟨a * b, hy⟩ = ρ ⟨a, ha⟩ * ρ' ⟨b, hbHD⟩ := by
      rw [hρρ' a ha, ← map_mul]
      rfl
    rw [e] at hk ⊢
    refine mem_of_two_elem627 (Gm := Gm) ?_ (hNGm b hbHD) ⟨_, rfl⟩ hk
    rw [← map_pow]
    have : (⟨b, hbHD⟩ : ↥HD) ^ 3 = 1 := Subtype.ext (by simpa using hD3 b hb)
    rw [this, map_one]
  have hO2 : pCoreOf 2 Gm = ⊥ := pCoreOf_range_actQuot_eq_bot hO2t
  have hO2' : pCoreOf 2 Gm' = ⊥ := by
    set P := pCoreOf 2 Gm' with hP
    have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hPGm : P ≤ Gm := fun x hx => by
      obtain ⟨k, hk⟩ := hP2 ⟨x, hx⟩
      exact hstar x (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx)
        ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hGmP : Gm ≤ Subgroup.normalizer (P : Set (MulAut Q)) :=
      hGmGm'.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Gm')
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPGm hGmP hP2
    rw [hO2] at this
    exact le_bot_iff.mp this
  have hAUH : ∀ a ∈ A, ∀ u ∈ UH, a * u * a⁻¹ * u⁻¹ ∈ B := by
    intro a ha u hu
    rw [← a27]
    have := Subgroup.commutator_mem_commutator hu ha
    have h1 := (⁅UH, A⁆).inv_mem this
    rw [commutatorElement_def] at h1
    convert h1 using 1
    group
  have hBUH : B ≤ UH := by
    rw [← a27]
    rw [Subgroup.commutator_le]
    intro u hu a ha
    rw [commutatorElement_def]
    have hau : a * u⁻¹ * a⁻¹ ∈ UH :=
      (Subgroup.mem_normalizer_iff.mp (hHUH (a20 ha)) _).mp (UH.inv_mem hu)
    have e : u * a * u⁻¹ * a⁻¹ = u * (a * u⁻¹ * a⁻¹) := by group
    rw [e]
    exact UH.mul_mem hu hau
  have hV16 : Nat.card V = 16 := by rw [h.natural.card_eq]; norm_num
  have hA16 : Nat.card A = 16 := by rw [a16, E3.card_conjSubgroup, hV16]
  set X₀ := quotSub UH U (U ⊔ B) with hX₀
  have hUBU : U ≤ U ⊔ B := le_sup_left
  have hBUUH : U ⊔ B ≤ UH := sup_le hUUH hBUH
  have hX₀U := card_quotSub (U := UH) (Z := U) hUBU hBUUH
  have hUB : U ≤ Subgroup.normalizer (B : Set G) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
      hUHc b (hBUH hb) u (hUUH hu))
  have e1 : U.relIndex (U ⊔ B) = (U ⊓ B).relIndex B := (B6.relIndex_inf_eq_relIndex_sup hUB).symm
  have e2 := Subgroup.relIndex_mul_card U (U ⊔ B)
  rw [inf_eq_left.mpr le_sup_left] at e2
  have e3 := Subgroup.relIndex_mul_card (U ⊓ B) B
  rw [show U ⊓ B ⊓ B = U ⊓ B from inf_eq_left.mpr inf_le_right] at e3
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have hX₀eq : Nat.card X₀ = (U ⊓ B).relIndex B := by
    rw [← e1]
    have := hX₀U.trans e2.symm
    exact Nat.eq_of_mul_eq_mul_right hUpos this
  have hUBne : Nat.card ↥(U ⊓ B) ≠ 1 := by
    intro h1
    apply hBU
    rw [inf_comm]
    exact Subgroup.eq_bot_of_card_eq _ h1
  rw [a23] at e3
  have hcpos : 0 < Nat.card ↥(U ⊓ B) := Nat.card_pos
  have hBnotU : ¬ B ≤ U := by
    intro hBU'
    have hAC : A ≤ A ⊓ centralizerMod U H UH := fun a ha =>
      ⟨ha, a20 ha, hHU (a20 ha), fun u hu => hBU' (hAUH a ha u hu)⟩
    rw [a30] at hAC
    have := Subgroup.card_le_of_le hAC
    rw [hA16, a23] at this
    omega
  have hX₀2 : Nat.card X₀ = 2 := by
    rw [hX₀eq]
    have hr1 : (U ⊓ B).relIndex B ≠ 1 := by
      intro hr
      apply hBnotU
      exact (Subgroup.relIndex_eq_one.mp hr).trans inf_le_left
    have hdvd : Nat.card ↥(U ⊓ B) ∣ 4 := ⟨_, by rw [← e3, mul_comm]⟩
    have hc4 : Nat.card ↥(U ⊓ B) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hc : Nat.card ↥(U ⊓ B) <;> omega
  set Astar := (A.subgroupOf H).map ρ with hAstar
  have hAstarT : Astar ≤ transvGroup Gm' X₀ := by
    rintro _ ⟨⟨a, haH⟩, haA, rfl⟩
    have haA' : a ∈ A := haA
    refine Subgroup.subset_closure ⟨hGmGm' ⟨_, rfl⟩, fun q => ?_⟩
    induction q using QuotientGroup.induction_on with
    | H u =>
      rw [actQuot_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mem_quotSub_iff hUBU]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (le_sup_right : B ≤ U ⊔ B) (hAUH a haA' u u.2)
  have hker : ρ.ker = (centralizerMod U H UH).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centralizerMod_iff_actQuot']
  have hAstar4 : Nat.card Astar = 4 := by
    rw [hAstar, ← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf a20]
    have h1 := Subgroup.relIndex_mul_card (centralizerMod U H UH) A
    rw [inf_comm, a30, a23, hA16] at h1
    omega
  have hA4 : 4 ≤ Nat.card (transvGroup Gm' X₀) := by
    rw [← hAstar4]
    exact Subgroup.card_le_of_le hAstarT
  obtain ⟨Dg⟩ := g31_apply_ch611 hG31 hQsq hO2' hX₀2 hA4
  set i0 : Fin Dg.s := ⟨0, Dg.hs⟩ with hi0
  set V0 := g31V (Dg.Δ i0) with hV0
  set G0 := g31G Gm' (Dg.Δ i0) with hG0
  have hG0all : g31G Gm' (orbitCh611 Gm' X₀) ≤ Gm := by
    refine iSup₂_le fun X hX => ?_
    rw [transvGroup, Subgroup.closure_le]
    rintro x ⟨hxGm', hxX⟩
    refine hstar x hxGm' ⟨1, ?_⟩
    rw [pow_one]
    exact sq_eq_one_of_moves627 hQsq (card_of_mem_orbitCh611 hX₀2 hX) hxX
  have hG0le : G0 ≤ g31G Gm' (orbitCh611 Gm' X₀) := by
    rw [← Dg.supG]
    exact le_iSup (fun i => g31G Gm' (Dg.Δ i)) i0
  have hfaith : ∀ x ∈ G0, (∀ v ∈ V0, x v = v) → x = 1 := fun x hx hfix =>
    Dg.eq_one_of_fix0_627 hQsq hO2' hx hfix
  have hU2 : IsPGroup 2 U := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    have hxV : (x : G) ∈ V := x.2.1
    simpa using h.toHyp611.isElemAbelian.2 _ hxV
  have hUne : U ≠ ⊥ := fun h0 => hBU (by rw [h0, inf_bot_eq])
  have hev : CFSG.Assembly.evenRank G ≤ 2 := h.qtke.2.2
  have hrankH : ∀ F : Subgroup G, F ≤ H → IsElemAbelian 3 F → ∀ r, Nat.card F = 3 ^ r →
      r ≤ 2 := fun F hFH hFab r hFr =>
    Vol2.Ch11.SecD.le_two_of_elemAbelian hev hUne hU2 Nat.prime_three (by norm_num)
      (hFH.trans hHU) hFab hFr
  have hkerρ : ∀ x : ↥H, ρ.rangeRestrict x = 1 → ∃ i : ℕ, x ^ 2 ^ i = 1 := by
    intro x hx
    have h1 : ρ x = 1 := congrArg Subtype.val hx
    have hxC := (mem_centralizerMod_iff_actQuot' x).mpr h1
    rw [a12] at hxC
    obtain ⟨i, hi⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨_, hxC⟩
    exact ⟨i, Subtype.ext (by simpa using congrArg Subtype.val hi)⟩
  have hblock : ∀ (d : G) (hd : d ∈ D),
      X₀.map (ρ' ⟨d, (le_sup_right : D ≤ HD) hd⟩).toMonoidHom ∈ Dg.Δ i0 := by
    intro d hd
    by_contra hmove
    set δ := ρ' ⟨d, (le_sup_right : D ≤ HD) hd⟩ with hδ
    have hδ3 : δ ^ 3 = 1 := by
      rw [hδ, ← map_pow]
      have : (⟨d, (le_sup_right : D ≤ HD) hd⟩ : ↥HD) ^ 3 = 1 :=
        Subtype.ext (by simpa using hD3 d hd)
      rw [this, map_one]
    have h3 := Dg.three_le_s627 ⟨_, rfl⟩ hδ3 hmove
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨E, hEG, hEab, hE27⟩ := Dg.exists_elemAbelian_27_627 hQsq hfaith h3
    have hEGm : E ≤ Gm := hEG.trans hG0all
    have hE3 : IsPGroup 3 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hEab.2 x x.2)⟩
    obtain ⟨r, hr⟩ := hE3.exists_card_eq
    have hr3 : 3 ≤ r := by
      by_contra hcon
      push Not at hcon
      have : 3 ^ r ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    set E' := E.subgroupOf Gm with hE'
    have hE'card : Nat.card E' = 3 ^ r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEGm).toEquiv, hr]
    have hE'ab : IsElemAbelian 3 E' := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · have := hEab.1.is_comm.comm ⟨(a : ↥Gm), a.2⟩ ⟨(b : ↥Gm), b.2⟩
        have this' : ((a : ↥Gm) : MulAut Q) * ((b : ↥Gm) : MulAut Q) =
            ((b : ↥Gm) : MulAut Q) * ((a : ↥Gm) : MulAut Q) := congrArg Subtype.val this
        exact Subtype.ext (Subtype.ext this')
      · apply Subtype.ext
        simpa using hEab.2 _ hx
    have := U3.le_two_of_elemAbelian_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
      hkerρ Nat.prime_three (by norm_num) hrankH hE'ab hE'card
    omega
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.toHyp611.toHyp5_0_1.T_le_normalizer
  have hQeq : ch6Q T V = pCoreOf 2 (L ⊔ T) := h.toHyp611.centralizer_eq
  have hO2L : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) (sup_le ?_ ?_)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
    · exact hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have htU : ∀ u ∈ U, u * t = t * u := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mp hu.2
  have hdtQ : ∀ d ∈ D, d * t * d⁻¹ * t⁻¹ ∈ ch6Q T V := by
    intro d hd
    have hdL : d ∈ L := hDL hd
    have hcL : d * t * d⁻¹ * t⁻¹ ∈ L := by
      have h1 : t * d⁻¹ * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hTL ht) _).mp (L.inv_mem hdL)
      have e : d * t * d⁻¹ * t⁻¹ = d * (t * d⁻¹ * t⁻¹) := by group
      rw [e]
      exact L.mul_mem hdL h1
    have hcU : d * t * d⁻¹ * t⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : d⁻¹ * u * d ∈ U := by
        simpa using (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem
          (hDNU hd)) u).mp hu
      have h1 := htU u hu
      have h2 := htU _ hu'
      calc u * (d * t * d⁻¹ * t⁻¹) = d * ((d⁻¹ * u * d) * t) * d⁻¹ * t⁻¹ := by group
        _ = d * (t * (d⁻¹ * u * d)) * d⁻¹ * t⁻¹ := by rw [h2]
        _ = d * t * d⁻¹ * (u * t⁻¹) := by group
        _ = d * t * d⁻¹ * (t⁻¹ * u) := by
            congr 1
            calc u * t⁻¹ = t⁻¹ * (t * u) * t⁻¹ := by group
              _ = t⁻¹ * (u * t) * t⁻¹ := by rw [h1]
              _ = t⁻¹ * u := by group
        _ = d * t * d⁻¹ * t⁻¹ * u := by group
    have hcV := h.toHyp611Nat.mem_centralizer_V_of_U ht hf hcL hcU
    rw [hQeq]
    exact hO2L (h.toHyp611.toHyp5_0_1.inf_centralizer_le h.toHyp611.L_le_normalizer
      h.toHyp611.module.2.2 ⟨hcL, hcV⟩)
  have hDR : ∀ d ∈ D, d ∈ Subgroup.normalizer (R : Set G) := by
    intro d hd
    have hdQ : d ∈ Subgroup.normalizer (ch6Q T V : Set G) := by
      rw [hQeq]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
        ((le_sup_left : L ≤ L ⊔ T) (hDL hd))
    have hQmap : (ch6Q T V).map (MulAut.conj d).toMonoidHom = ch6Q T V :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hdQ
    have hle : R.map (MulAut.conj d).toMonoidHom ≤ R := by
      rw [Subgroup.map_sup, hQmap]
      refine sup_le le_sup_left ?_
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      have e : (MulAut.conj d).toMonoidHom t = (d * t * d⁻¹ * t⁻¹) * t := by
        simp [MulAut.conj_apply]
      rw [e]
      exact R.mul_mem ((le_sup_left : ch6Q T V ≤ R) (hdtQ d hd))
        ((le_sup_right : Subgroup.zpowers t ≤ R) (Subgroup.mem_zpowers t))
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj d).injective]))
  set Rs := (R.subgroupOf H).map ρ with hRs
  have hRsyl : CFSG.QuasithinUnique.IsSylowTwoOf Rs Gm := by
    refine ⟨Subgroup.map_le_range _ _, ?_, ?_⟩
    · have hR2 : IsPGroup 2 (R.subgroupOf H) := by
        intro x
        obtain ⟨k, hk⟩ := a3.2.1 ⟨(x : ↥H), x.2⟩
        exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
      exact hR2.map ρ
    · intro h2
      apply a3.2.2
      have e : Rs.relIndex Gm = ((R.subgroupOf H) ⊔ ρ.ker).index := by
        rw [hRs, hGm, MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
          Subgroup.relIndex_top_right]
      have h3 : 2 ∣ ((R.subgroupOf H) ⊔ ρ.ker).index := e ▸ h2
      exact h3.trans (Subgroup.index_dvd_of_le le_sup_left)
  have hδmain : ∀ (d : G) (hd : d ∈ D),
      (∀ v ∈ V0, ρ' ⟨d, (le_sup_right : D ≤ HD) hd⟩ v = v) ∧
        ∀ x ∈ G0, ρ' ⟨d, (le_sup_right : D ≤ HD) hd⟩ * x =
          x * ρ' ⟨d, (le_sup_right : D ≤ HD) hd⟩ := by
    intro d hd
    set δ := ρ' ⟨d, (le_sup_right : D ≤ HD) hd⟩ with hδ
    have hδ3 : δ ^ 3 = 1 := by
      rw [hδ, ← map_pow]
      have : (⟨d, (le_sup_right : D ≤ HD) hd⟩ : ↥HD) ^ 3 = 1 :=
        Subtype.ext (by simpa using hD3 d hd)
      rw [this, map_one]
    obtain ⟨hδG0, hδV0⟩ := Dg.normalizes_block0_627 ⟨_, rfl⟩ (hblock d hd)
    have hδR : δ ∈ Subgroup.normalizer (Rs : Set (MulAut Q)) := by
      have key : ∀ (e : G) (he : e ∈ D), ∀ x ∈ Rs, ρ' ⟨e, (le_sup_right : D ≤ HD) he⟩ * x *
          (ρ' ⟨e, (le_sup_right : D ≤ HD) he⟩)⁻¹ ∈ Rs := by
        rintro e he _ ⟨⟨r, hrH⟩, hrR, rfl⟩
        have hrR' : r ∈ R := hrR
        have heR : e * r * e⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hDR e he) r).mp hrR'
        have heH : e * r * e⁻¹ ∈ H := a3.1 heR
        rw [hconjρ e _ r hrH heH]
        exact ⟨⟨_, heH⟩, heR, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨key d hd x, fun hx => ?_⟩
      have h1 := key d⁻¹ (D.inv_mem hd) _ hx
      have e : ρ' ⟨d⁻¹, (le_sup_right : D ≤ HD) (D.inv_mem hd)⟩ = δ⁻¹ := by
        rw [hδ, ← map_inv]
        rfl
      rw [e, inv_inv] at h1
      simpa [mul_assoc] using h1
    have hPsyl := Dg.isSylowTwoOf_inf_G0_627' hRsyl hGmGm' hG0all
    have hδP : δ ∈ Subgroup.normalizer ((Rs ⊓ G0 : Subgroup (MulAut Q)) : Set (MulAut Q)) := by
      rw [Subgroup.mem_normalizer_iff] at hδR hδG0 ⊢
      intro x
      simp only [Subgroup.mem_inf]
      exact ⟨fun hx => ⟨(hδR x).mp hx.1, (hδG0 x).mp hx.2⟩,
        fun hx => ⟨(hδR x).mpr hx.1, (hδG0 x).mpr hx.2⟩⟩
    have hodd : Odd (orderOf δ) := by
      have h1 : orderOf δ ∣ 3 := orderOf_dvd_of_pow_eq_one hδ3
      exact Odd.of_dvd_nat (by decide) h1
    have hfixδ := Dg.fix_V0_of_normalizes_sylow627 hQsq hδV0 inf_le_right hPsyl.2.1 hPsyl.2.2
      hδP hodd
    refine ⟨hfixδ, fun x hx => ?_⟩
    have hxS : x ∈ stabSubCh611 V0 := Dg.g31G_le_stab i0 hx
    have hc : δ * x * δ⁻¹ * x⁻¹ ∈ G0 :=
      G0.mul_mem ((Subgroup.mem_normalizer_iff.mp hδG0 x).mp hx) (G0.inv_mem hx)
    have hcfix : ∀ v ∈ V0, (δ * x * δ⁻¹ * x⁻¹) v = v := by
      intro v hv
      have h1 : x⁻¹ v ∈ V0 := (hxS v hv).2
      have h2 : δ⁻¹ (x⁻¹ v) = x⁻¹ v := by
        conv_lhs => rw [← hfixδ _ h1]
        exact MulAut.inv_apply_self _ δ (x⁻¹ v)
      simp only [MulAut.mul_apply]
      rw [h2, MulAut.apply_inv_self, hfixδ v hv]
    have h1 := hfaith _ hc hcfix
    have e : δ * x = (δ * x * δ⁻¹ * x⁻¹) * (x * δ) := by group
    rw [e, h1, one_mul]
  set K : Subgroup G := (G0.comap ρ).map H.subtype with hKdef
  have hKH : K ≤ H := Subgroup.map_subtype_le _
  have hmemK : ∀ {k : G}, k ∈ K → ∃ hk : k ∈ H, ρ ⟨k, hk⟩ ∈ G0 := by
    rintro _ ⟨⟨k, hk⟩, hkG, rfl⟩
    exact ⟨hk, hkG⟩
  have hAK : A ≤ K := by
    intro a ha
    refine ⟨⟨a, a20 ha⟩, ?_, rfl⟩
    have h1 : ρ ⟨a, a20 ha⟩ ∈ Astar := ⟨⟨a, a20 ha⟩, ha, rfl⟩
    exact transvGroup_le_g31G Gm' Dg.mem0 (hAstarT h1)
  have hKD : ∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ * d⁻¹ ∈
      centralizerMod U (Subgroup.normalizer (U : Set G)) UH := by
    intro k hk d hd
    obtain ⟨hkH, hkG⟩ := hmemK hk
    have hkHD : k ∈ HD := (le_sup_left : H ≤ HD) hkH
    have hdHD : d ∈ HD := (le_sup_right : D ≤ HD) hd
    have hcHD : k * d * k⁻¹ * d⁻¹ ∈ HD :=
      HD.mul_mem (HD.mul_mem (HD.mul_mem hkHD hdHD) (HD.inv_mem hkHD)) (HD.inv_mem hdHD)
    have hcN : k * d * k⁻¹ * d⁻¹ ∈ Subgroup.normalizer (U : Set G) := hHDU hcHD
    refine ⟨hcN, hcN, ?_⟩
    have hρc : ρ' ⟨k * d * k⁻¹ * d⁻¹, hcHD⟩ = 1 := by
      have e : ρ' ⟨k * d * k⁻¹ * d⁻¹, hcHD⟩ =
          ρ ⟨k, hkH⟩ * ρ' ⟨d, hdHD⟩ * (ρ ⟨k, hkH⟩)⁻¹ * (ρ' ⟨d, hdHD⟩)⁻¹ := by
        rw [hρρ' k hkH, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      rw [e, ← (hδmain d hd).2 _ hkG]
      group
    exact (actQuot_eq_one_iff (U := UH) (Z := U) _).mp hρc
  set W : Subgroup G := (V0.comap (QuotientGroup.mk' (U.subgroupOf UH))).map UH.subtype with hWdef
  have hUHK : ⁅UH, K⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    obtain ⟨hkH, hkG⟩ := hmemK hk
    have hku : k * u⁻¹ * k⁻¹ ∈ UH :=
      (Subgroup.mem_normalizer_iff.mp (hHUH hkH) _).mp (UH.inv_mem hu)
    have hcUH : ⁅u, k⁆ ∈ UH := by
      rw [commutatorElement_def]
      have e : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
      rw [e]
      exact UH.mul_mem hu hku
    refine ⟨⟨_, hcUH⟩, ?_, rfl⟩
    show (QuotientGroup.mk' (U.subgroupOf UH)) ⟨⁅u, k⁆, hcUH⟩ ∈ V0
    have hmove := g31G_le_moveIn627 Gm' (Dg.Δ i0) hkG ((⟨u, hu⟩ : ↥UH) : Q)
    have e : (QuotientGroup.mk' (U.subgroupOf UH)) ⟨⁅u, k⁆, hcUH⟩ =
        (ρ ⟨k, hkH⟩ ((⟨u, hu⟩ : ↥UH) : Q) * ((⟨u, hu⟩ : ↥UH) : Q)⁻¹)⁻¹ := by
      rw [actQuot_mk, mul_inv_rev, inv_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        QuotientGroup.mk'_apply]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact V0.inv_mem hmove
  have hWD : ⁅W, D⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨⟨w, hwUH⟩, hwV, rfl⟩ d hd
    have hwV' : ((⟨w, hwUH⟩ : ↥UH) : Q) ∈ V0 := hwV
    have h1 := (hδmain d hd).1 _ hwV'
    have h2 := (actQuot_mk_eq_iff (U := UH) (Z := U) (K := HD) (hKU := hHDUH) (hKZ := hHDU)
      ⟨d, (le_sup_right : D ≤ HD) hd⟩ ⟨w, hwUH⟩).mp h1
    have h3 := U.inv_mem h2
    rw [commutatorElement_def]
    simp only [Subgroup.coe_subtype]
    convert h3 using 1
    group
  exact a34 K hKH hAK hKD ((Subgroup.commutator_mono hUHK le_rfl).trans hWD)

end PartB

theorem res627FF_of_Q (hG31 : Ch6G31O2) (hQ : Res627Q) : Res627FF :=
  res627FF_of_TQ (res627T_of hG31) hQ

end CFSG.Quasithin.H13
