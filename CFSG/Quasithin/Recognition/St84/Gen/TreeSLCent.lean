module

public import CFSG.Quasithin.Recognition.St84.AppTreeSAE
import CFSG.Quasithin.Recognition.St84.TransferSetup
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining
import CFSG.CGT.PushingUpLit.SolKR2.WeakInner
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_mem_centerOf_conj_eq {X T : Subgroup G} [Finite ↥X]
    (hX : CharTwo X) (hT : IsSylowTwoOf T X) {u : G}
    (hu : u ∈ Subgroup.normalizer (X : Set G)) (hu2 : u * u = 1)
    (huT : ∀ t ∈ T, u * t = t * u) :
    ∃ c ∈ centerOf (pCoreOf 2 X), ∀ x ∈ X, u * x * u⁻¹ = c * x * c⁻¹ := by
  classical
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  let Q : Subgroup G := pCoreOf 2 X
  have hQX : Q ≤ X := pCoreOf_le 2 X
  have hQT : Q ≤ T := hT.pCoreOf_le
  have huQ : ∀ q ∈ Q, u * q = q * u := fun q hq => huT q (hQT hq)
  let f : ↥X → G := fun x => u * (x : G) * u⁻¹ * (x : G)⁻¹
  have huX : ∀ x ∈ X, u * x * u⁻¹ ∈ X := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hu x).mp hx
  have hfX : ∀ x : ↥X, f x ∈ X := fun x => X.mul_mem (huX x x.2) (X.inv_mem x.2)
  have hfCentQ : ∀ x : ↥X, f x ∈ Subgroup.centralizer (Q : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hxq : (x : G) * q * (x : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf (r := 2) X x.2) q).mp hq
    have hxq' : (x : G)⁻¹ * q * (x : G) ∈ Q := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf (r := 2) X (X.inv_mem x.2)) q).mp hq
    have hfixq : u * q * u⁻¹ = q := by
      rw [huQ q hq]
      group
    have hfix1 : u * ((x : G) * q * (x : G)⁻¹) * u⁻¹ =
        (x : G) * q * (x : G)⁻¹ := by
      rw [huQ _ hxq]
      group
    have hfix2 : u⁻¹ * ((x : G)⁻¹ * q * (x : G)) * u =
        (x : G)⁻¹ * q * (x : G) := by
      rw [hu_inv]
      calc u * ((x : G)⁻¹ * q * (x : G)) * u
          = ((x : G)⁻¹ * q * (x : G)) * u * u := by rw [huQ _ hxq']
        _ = (x : G)⁻¹ * q * (x : G) := by rw [mul_assoc, hu2, mul_one]
    have hconj : f x * q * (f x)⁻¹ = q := by
      calc f x * q * (f x)⁻¹
          = u * (x : G) * (u⁻¹ * ((x : G)⁻¹ * q * (x : G)) * u) *
              (x : G)⁻¹ * u⁻¹ := by
            simp only [f]
            group
        _ = u * (x : G) * ((x : G)⁻¹ * q * (x : G)) * (x : G)⁻¹ * u⁻¹ := by
            rw [hfix2]
        _ = u * q * u⁻¹ := by group
        _ = q := hfixq
    have hcomm : q * f x = f x * q := by
      calc q * f x = (f x * q * (f x)⁻¹) * f x := by rw [hconj]
        _ = f x * q := by group
    exact hcomm
  have hfQ : ∀ x : ↥X, f x ∈ Q := fun x => hX ⟨hfX x, hfCentQ x⟩
  have hfZ : ∀ x : ↥X, f x ∈ centerOf Q := fun x => ⟨hfQ x, hfCentQ x⟩
  have hf_inv : ∀ x : ↥X, (f x)⁻¹ = f x := by
    intro x
    calc (f x)⁻¹ = (x : G) * u * (x : G)⁻¹ * u := by
          simp only [f, mul_inv_rev, hu_inv, inv_inv]
          group
      _ = u * f x * u⁻¹ := by
          simp only [f]
          rw [hu_inv]
          symm
          calc u * (u * (x : G) * u * (x : G)⁻¹) * u
              = (u * u) * (x : G) * u * (x : G)⁻¹ * u := by group
            _ = (x : G) * u * (x : G)⁻¹ * u := by rw [hu2, one_mul]
      _ = f x := by
          rw [huT (f x) (hQT (hfQ x))]
          group
  have hf_sq : ∀ x : ↥X, f x * f x = 1 := by
    intro x
    rw [mul_eq_one_iff_eq_inv]
    exact (hf_inv x).symm
  have hZcomm : ∀ a ∈ centerOf Q, ∀ b ∈ centerOf Q, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (A4.centerOf_le_centralizer Q ha) b
      (A4.centerOf_le Q hb)).symm
  let N : Subgroup G :=
    Subgroup.closure {x : G | x ∈ centerOf Q ∧ x * x = 1}
  have hNZ : N ≤ centerOf Q :=
    (Subgroup.closure_le (centerOf Q)).mpr fun _ hx => hx.1
  have hNelem : CFSG.Open.IsElemAbelian 2 N :=
    CFSG.Open.IsElemAbelian.closure_of_commute
      (fun a ha b hb => hZcomm a ha.1 b hb.1)
      (fun a ha => by simpa [pow_two] using ha.2)
  have hNX : N ≤ X := hNZ.trans ((A4.centerOf_le Q).trans hQX)
  have hXZ : X ≤ Subgroup.normalizer (centerOf Q : Set G) :=
    (le_normalizer_pCoreOf (r := 2) X).trans (A4.normalizer_le_normalizer_centerOf Q)
  have hXn : X ≤ Subgroup.normalizer (N : Set G) := by
    refine F7.le_normalizer_closure (X := X) {x : G | x ∈ centerOf Q ∧ x * x = 1} ?_
    intro g hg s hs
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hXZ hg) s).mp hs.1, ?_⟩
    rw [show g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ by group, hs.2, mul_one,
      mul_inv_cancel]
  have hNc : ∀ m ∈ N, ∀ n ∈ N, m * n = n * m := fun m hm n hn => hNelem.comm hm hn
  have hN2 : ∀ n ∈ N, n * n = 1 := fun n hn => hNelem.mul_self_eq_one hn
  have hodd : Odd (T.subgroupOf X).index :=
    Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hT.2.2)
  let δ : ↥X → ↥X := fun z => ⟨f z, hfX z⟩
  have hδN : ∀ z : ↥X, δ z ∈ N.subgroupOf X := fun z =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure
      ⟨hfZ z, by simpa [pow_two] using hf_sq z⟩)
  have hδmul : ∀ z z' : ↥X, δ (z * z') = δ z * (z * δ z' * z⁻¹) := by
    intro z z'
    apply Subtype.ext
    change f (z * z') = f z * ((z : G) * f z' * (z : G)⁻¹)
    simp only [f, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hu_inv]
    have hred : u * (z : G) * u * (z : G)⁻¹ *
        ((z : G) * (u * (z' : G) * u * (z' : G)⁻¹) * (z : G)⁻¹) =
        u * (z : G) * (z' : G) * u * (z' : G)⁻¹ * (z : G)⁻¹ := by
      calc u * (z : G) * u * (z : G)⁻¹ *
          ((z : G) * (u * (z' : G) * u * (z' : G)⁻¹) * (z : G)⁻¹)
          = u * (z : G) * (u * u) * (z' : G) * u * (z' : G)⁻¹ * (z : G)⁻¹ := by
              group
        _ = u * (z : G) * (z' : G) * u * (z' : G)⁻¹ * (z : G)⁻¹ := by
              rw [hu2, mul_one]
    rw [hred]
    group
  have hδΛ : ∀ s ∈ T.subgroupOf X, δ s = 1 := by
    intro s hs
    apply Subtype.ext
    have hsT : (s : G) ∈ T := Subgroup.mem_subgroupOf.mp hs
    have hcomm : u * (s : G) = (s : G) * u := huT _ hsT
    change f s = 1
    simp only [f]
    rw [hcomm]
    group
  haveI hNnorm : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hXn
  have hNc' : ∀ m ∈ N.subgroupOf X, ∀ n ∈ N.subgroupOf X, m * n = n * m := by
    intro m hm n hn
    apply Subtype.ext
    exact hNc m (Subgroup.mem_subgroupOf.mp hm) n (Subgroup.mem_subgroupOf.mp hn)
  have hN2' : ∀ n ∈ N.subgroupOf X, n * n = 1 := by
    intro n hn
    apply Subtype.ext
    exact hN2 n (Subgroup.mem_subgroupOf.mp hn)
  obtain ⟨m, hmN, hmδ⟩ :=
    CFSG.CGT.PushingUpLit.SolKR2.exists_coboundary (N.subgroupOf X) (T.subgroupOf X)
      hNc' hN2' hodd δ hδN hδmul hδΛ
  let c : G := (m : G)
  have hc : c ∈ centerOf Q := hNZ (Subgroup.mem_subgroupOf.mp hmN)
  refine ⟨c, hc, ?_⟩
  intro x hx
  let z : ↥X := ⟨x, hx⟩
  have h := congrArg (fun y : ↥X => (y : G)) (hmδ z)
  have h' : f z = c * (x * c⁻¹ * x⁻¹) := by
    simpa [δ, c, z, Subgroup.coe_mul, Subgroup.coe_inv] using h
  calc u * x * u⁻¹ = f z * x := by
        simp only [f, z]
        group
    _ = (c * (x * c⁻¹ * x⁻¹)) * x := by rw [h']
    _ = c * x * c⁻¹ := by group

end CFSG.Quasithin

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.LieType.BorelTits CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem f112sl_mem_K_of_commute_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S)
    (hZ : L2 ≤ Subgroup.centralizer (centerOf (S ⊓ f112saK L1 L2 S) : Set H))
    {u : H} (hu : u ∈ S) (hu2 : u * u = 1)
    (huT : ∀ t ∈ S ⊓ f112saK L1 L2 S, u * t = t * u) :
    u ∈ f112saK L1 L2 S := by
  classical
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  let K := f112saK L1 L2 S
  let T := S ⊓ K
  let P1' := f112saP1' L1 L2 S
  let P2' := f112saP2' L1 L2 S
  let B := bigB L1 L2 S
  have hT1 : IsSylowTwoOf T P1' := f112sa_T_sylow_P1'_of_hyp111R hF.toW hR
  have hT2 : IsSylowTwoOf T P2' := f112sa_T_sylow_P2'_of_hyp111R hF.toW hR
  have hC1 : CharTwo P1' := f112sa_charTwo_P1'_of_hyp111R hF.toW hR
  have hC2 : CharTwo P2' := f112sa_charTwo_P2'_of_hyp111R hF.toW hR
  have hSB : S ≤ B := le_sup_right
  have hB1 : B ≤ f112P1 L1 L2 S := le_sup_right
  have hB2 : B ≤ f112P2 L1 L2 S := le_sup_right
  have huN1 : u ∈ Subgroup.normalizer (P1' : Set H) :=
    (f112sa_P1_le_normalizer_P1' hF.toW) (hB1 (hSB hu))
  have huN2 : u ∈ Subgroup.normalizer (P2' : Set H) :=
    (f112sa_P2_le_normalizer_P2' hF.toW) (hB2 (hSB hu))
  obtain ⟨c1, hc1Z, hconj1⟩ := exists_mem_centerOf_conj_eq hC1 hT1 huN1 hu2 huT
  obtain ⟨c2, hc2Z, hconj2⟩ := exists_mem_centerOf_conj_eq hC2 hT2 huN2 hu2 huT
  have hc1T : c1 ∈ T := hT1.pCoreOf_le hc1Z.1
  have hc2T : c2 ∈ T := hT2.pCoreOf_le hc2Z.1
  have hc1S : c1 ∈ S := hc1T.1
  have hK1 : K ≤ P1' := by
    change f112saX1 L1 L2 S ⊔ f112saX2 L1 L2 S ≤ oTwoRes L1 ⊔ f112saX2 L1 L2 S
    exact sup_le ((f112sa_X1_le_oTwoRes L1 L2 S).trans le_sup_left) le_sup_right
  have hK2 : K ≤ P2' := by
    change f112saX1 L1 L2 S ⊔ f112saX2 L1 L2 S ≤ oTwoRes L2 ⊔ f112saX1 L1 L2 S
    exact sup_le le_sup_right ((f112sa_X2_le_oTwoRes L1 L2 S).trans le_sup_left)
  let m := c1⁻¹ * c2
  have hmT : m ∈ T := T.mul_mem (T.inv_mem hc1T) hc2T
  have hmKcomm : ∀ k ∈ K, m * k = k * m := by
    intro k hk
    have h12 : c1 * k * c1⁻¹ = c2 * k * c2⁻¹ :=
      (hconj1 k (hK1 hk)).symm.trans (hconj2 k (hK2 hk))
    calc m * k = c1⁻¹ * (c2 * k * c2⁻¹) * c2 := by
          simp only [m]
          group
      _ = c1⁻¹ * (c1 * k * c1⁻¹) * c2 := by rw [← h12]
      _ = k * m := by
          simp only [m]
          group
  have hmCentT : m ∈ Subgroup.centralizer (T : Set H) :=
    Subgroup.mem_centralizer_iff.mpr fun t ht => (hmKcomm t ((inf_le_right : T ≤ K) ht)).symm
  have hmCenter : m ∈ centerOf T := ⟨hmT, hmCentT⟩
  have hmCentL2 : ∀ l ∈ L2, m * l = l * m := fun l hl =>
    Subgroup.mem_centralizer_iff.mp (hZ hl) m hmCenter
  have hmCentO2 : ∀ l ∈ oTwoRes L2, m * l = l * m := fun l hl =>
    hmCentL2 l (oTwoRes_le L2 hl)
  have hmCentP2' : P2' ≤ Subgroup.centralizer ({m} : Set H) := by
    change oTwoRes L2 ⊔ f112saX1 L1 L2 S ≤ Subgroup.centralizer ({m} : Set H)
    refine sup_le ?_ ?_
    · intro l hl
      exact Subgroup.mem_centralizer_iff.mpr fun t ht => by
        rw [Set.mem_singleton_iff] at ht
        subst ht
        exact hmCentO2 l hl
    · intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun t ht => by
        rw [Set.mem_singleton_iff] at ht
        subst ht
        exact hmKcomm x ((le_sup_left : f112saX1 L1 L2 S ≤ K) hx)
  have hmConjP2' : ∀ p ∈ P2', m * p * m⁻¹ = p := by
    intro p hp
    have h := Subgroup.mem_centralizer_iff.mp (hmCentP2' hp) m (Set.mem_singleton m)
    rw [h]
    group
  have hc2u_inv : (c2⁻¹ * u)⁻¹ = u * c2 := by
    rw [mul_inv_rev, hu_inv, inv_inv]
  have hc2uCentP2' : ∀ p ∈ P2', (c2⁻¹ * u) * p * (c2⁻¹ * u)⁻¹ = p := by
    intro p hp
    have h := hconj2 p hp
    calc (c2⁻¹ * u) * p * (c2⁻¹ * u)⁻¹
        = c2⁻¹ * (u * p * u⁻¹) * c2 := by
          rw [hc2u_inv, hu_inv]
          group
      _ = c2⁻¹ * (c2 * p * c2⁻¹) * c2 := by rw [h]
      _ = p := by group
  let w := c1⁻¹ * u
  have hwm : w = m * (c2⁻¹ * u) := by
    simp only [w, m]
    group
  have hwP2' : ∀ p ∈ P2', w * p * w⁻¹ = p := by
    intro p hp
    calc w * p * w⁻¹
        = (m * (c2⁻¹ * u)) * p * (m * (c2⁻¹ * u))⁻¹ := by rw [hwm]
      _ = m * ((c2⁻¹ * u) * p * (c2⁻¹ * u)⁻¹) * m⁻¹ := by group
      _ = m * p * m⁻¹ := by rw [hc2uCentP2' p hp]
      _ = p := hmConjP2' p hp
  have hw_inv : w⁻¹ = u * c1 := by
    simp only [w]
    rw [mul_inv_rev, hu_inv, inv_inv]
  have hwP1' : ∀ p ∈ P1', w * p * w⁻¹ = p := by
    intro p hp
    have h := hconj1 p hp
    calc w * p * w⁻¹
        = c1⁻¹ * u * p * (u * c1) := by rw [hw_inv]
      _ = c1⁻¹ * (u * p * u⁻¹) * c1 := by
          rw [hu_inv]
          group
      _ = c1⁻¹ * (c1 * p * c1⁻¹) * c1 := by rw [h]
      _ = p := by group
  have hwS : w ∈ S := S.mul_mem (S.inv_mem hc1S) hu
  have hwB : w ∈ B := hSB hwS
  have hwC1 : w ∈ Subgroup.centralizer (P1' : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    calc p * w = (w * p * w⁻¹) * w := by rw [hwP1' p hp]
      _ = w * p := by group
  have hwC2 : w ∈ Subgroup.centralizer (P2' : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    calc p * w = (w * p * w⁻¹) * w := by rw [hwP2' p hp]
      _ = w * p := by group
  have hwbot : w ∈ (⊥ : Subgroup H) := by
    rw [← f112sa_core_free_of_hyp111R hF.toW hR]
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hwB, hwC1⟩, hwC2⟩
  have hw1 : w = 1 := Subgroup.mem_bot.mp hwbot
  have hu_eq : u = c1 := by
    have h : c1⁻¹ * u = 1 := hw1
    calc u = c1 * (c1⁻¹ * u) := by group
      _ = c1 * 1 := by rw [h]
      _ = c1 := mul_one c1
  rw [hu_eq]
  exact hc1T.2

theorem f112sl_mem_centerOf_of_commute_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S)
    (hZ : L2 ≤ Subgroup.centralizer (centerOf (S ⊓ f112saK L1 L2 S) : Set H))
    {u : H} (hu : u ∈ S) (hu2 : u * u = 1) (huS : ∀ s ∈ S, u * s = s * u) :
    u ∈ centerOf (S ⊓ f112saK L1 L2 S) := by
  have huK : u ∈ f112saK L1 L2 S :=
    f112sl_mem_K_of_commute_of_hyp111R hF hR hZ hu hu2 fun t ht => huS t ht.1
  refine ⟨⟨hu, huK⟩, ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr fun t ht => (huS t ht.1).symm

end CFSG.Quasithin.F112R.St84
