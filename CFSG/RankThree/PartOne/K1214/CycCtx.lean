module

public import CFSG.RankThree.PartOne.K1214.Omega
public import CFSG.RankThree.PartOne.K1214.CycMain
public import CFSG.RankThree.PartOne.S12.Sec15Frattini
import CFSG.RankThree.PartOne.S12.Sec12Three
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.Blueprint
open CFSG.RankThree.PartOne.S12K (LieRigidity3)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {b : G} {K I X P Q : Subgroup G}

theorem QE_of_gen (ctx : Fus12Ctx G p A c L E) (hF : Field1213 p A c L b K I)
    (hC : Choice1212 p E b I X P Q) (hgen : ∃ f ∈ P, P = Q ⊔ Subgroup.zpowers f) :
    Q ⊓ E = E ⊓ L := by
  have hp : p.Prime := ctx.hyp.prime
  have hEP := E_le_P hC
  have hcE := c_mem_E ctx
  have hcP : c ∈ P := hEP hcE
  have hcQ := c_not_mem_Q hF hC
  obtain ⟨f, hfP, hPf⟩ := hgen
  have hQ := Sec12Fus.q_normal hC
  have hab := quotient_abelian_of_sup_zpowers hQ.1 hQ.2 hfP hPf
  have hD := data_of_ctx ctx
  have hcB := c_not_mem_B ctx
  have hBQ : ∀ z ∈ E ⊓ L, z ∈ Q := by
    intro z hz
    have hzE : z ∈ E := hz.1
    have hzB : (⟨z, hzE⟩ : ↥E) ∈ (E ⊓ L).subgroupOf E := Subgroup.mem_subgroupOf.2 hz
    obtain ⟨w, hw⟩ := hD.xiHom_surjective hcB ⟨⟨z, hzE⟩, hzB⟩
    have hw' := congrArg (fun t : ↥((E ⊓ L).subgroupOf E) => ((t : ↥E) : G)) hw
    obtain ⟨y, hyX, hy, hyw⟩ := exists_mem_X_conjAut hp hC w.2
    have h1 := Equivariance.coe_conjAut hy ⟨c, hcE⟩
    rw [hyw] at h1
    have h2 : y * c * y⁻¹ * c⁻¹ = z := by
      have h3 : (((torusWeyl E).subtype (w : ↥(torusWeyl E)) ⟨c, hcE⟩ * (⟨c, hcE⟩ : ↥E)⁻¹ : ↥E) : G)
          = z := hw'
      rw [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      rw [← h3]
      show y * c * y⁻¹ * c⁻¹ = (((w : ↥(torusWeyl E)) : MulAut E) ⟨c, hcE⟩ : G) * c⁻¹
      rw [h1]
    have h4 := hab ⟨y, hC.P_sylow.2 hyX⟩ ⟨c, hcP⟩
    rw [← h2]
    exact Subgroup.mem_subgroupOf.1 h4
  apply le_antisymm
  · rintro e ⟨heQ, heE⟩
    obtain ⟨b', hb', a, hba⟩ := hD.exists_decomp hcB ⟨e, heE⟩
    have hb'G : (b' : G) ∈ E ⊓ L := Subgroup.mem_subgroupOf.1 hb'
    have he_eq : e = (b' : G) * c ^ a := by
      have := congrArg Subtype.val hba
      simpa using this
    have hca : c ^ a ∈ Q := by
      have h1 : c ^ a = (b' : G)⁻¹ * e := by
        rw [he_eq]
        group
      rw [h1]
      exact Q.mul_mem (Q.inv_mem (hBQ _ hb'G)) heQ
    have hbot := Sec12Three.zpowers_inf_eq_bot hp (Sec12Three.orderOf_c ctx.hyp) hcQ
    have hca1 : c ^ a = 1 := by
      have hmem : c ^ a ∈ Subgroup.zpowers c ⊓ Q :=
        ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) a, hca⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    rw [he_eq, hca1, mul_one]
    exact hb'G
  · intro z hz
    exact ⟨hBQ z hz, hz.1⟩

omit [Finite G] in
theorem mem_xPreimage_iff {y : G} :
    y ∈ xPreimage p E ↔ ∃ hy : y ∈ Subgroup.normalizer (E : Set G),
      ∃ w ∈ CFSG.pCore p ↥(torusWeyl E), ((w : ↥(torusWeyl E)) : MulAut E) = conjAut E y hy := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨w, hw, hwn⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hn)
    exact ⟨n.2, w, hw, hwn⟩
  · rintro ⟨hy, w, hw, hwy⟩
    exact ⟨⟨y, hy⟩, Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨w, hw, hwy⟩), rfl⟩

omit [Finite G] in
theorem conj_mem_xPreimage {n y : G} (hn : n ∈ Subgroup.normalizer (E : Set G))
    (hy : y ∈ xPreimage p E) : n * y * n⁻¹ ∈ xPreimage p E := by
  obtain ⟨hyN, w, hw, hwy⟩ := mem_xPreimage_iff.1 hy
  have hnyn : n * y * n⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hyN) (Subgroup.inv_mem _ hn)
  refine mem_xPreimage_iff.2 ⟨hnyn, ?_⟩
  set ν : ↥(torusWeyl E) := ⟨conjAut E n hn, ⟨⟨n, hn⟩, rfl⟩⟩ with hν
  refine ⟨ν * w * ν⁻¹, (CFSG.pCore_normal (p := p) (G := ↥(torusWeyl E))).conj_mem w hw ν, ?_⟩
  have h1 := Equivariance.conj_conjAut_normalizerMonoidHom hn ⟨y, hyN⟩
  have h2 : conjAut E (n * y * n⁻¹) hnyn =
      E.normalizerMonoidHom (⟨n, hn⟩ * ⟨y, hyN⟩ * ⟨n, hn⟩⁻¹) := by
    unfold conjAut
    rfl
  rw [h2, ← h1]
  show conjAut E n hn * (w : MulAut E) * (conjAut E n hn)⁻¹ =
    (MulAut.conj (conjAut E n hn)) (E.normalizerMonoidHom ⟨y, hyN⟩)
  rw [hwy, MulAut.conj_apply]
  rfl

theorem fix_of_mem_xPreimage (ctx : Fus12Ctx G p A c L E) {k z : G} (hk : k ∈ xPreimage p E)
    (hz : z ∈ E ⊓ L) : k * z * k⁻¹ = z := by
  obtain ⟨hkN, w, hw, hwk⟩ := mem_xPreimage_iff.1 hk
  have hz' : z ∈ pCoreFixed p E := ctx.ten.1.ge hz
  obtain ⟨hzE, hfix⟩ := mem_pCoreFixed.1 hz'
  have h1 := hfix w hw
  rw [hwk] at h1
  have h2 := Equivariance.coe_conjAut hkN ⟨z, hzE⟩
  rw [h1] at h2
  exact h2.symm

theorem frame_inv_of_le (ctx : Fus12Ctx G p A c L E)
    (hnH : ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c)))
    (hX : IsSylowOf p X (xPreimage p E)) {T : Subgroup G}
    (hTp : IsPGroup p ↥T) (hXT : X ≤ T) (hTE : T ≤ Subgroup.normalizer (E : Set G))
    {U : Subgroup G} (hUB : U ≤ E ⊓ L)
    (hUi : ∀ m ∈ Subgroup.normalizer (T : Set G), ∀ u ∈ U, m * u * m⁻¹ ∈ U) :
    U = ⊥ ∨ U = E ⊓ L := by
  classical
  have hp : p.Prime := ctx.hyp.prime
  have : Fact p.Prime := ⟨hp⟩
  have hPW : T ≤ xPreimage p E := by
    intro y hy
    obtain ⟨m, hm⟩ := hTp ⟨y, hy⟩
    obtain ⟨w, hw, hwy⟩ := exists_conjAut_mem_pCore ctx hnH (hTE hy)
      ⟨m, by simpa using congrArg Subtype.val hm⟩
    exact mem_xPreimage_iff.2 ⟨hTE hy, w, hw, hwy⟩
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p T (xPreimage p E) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hPW, hTp, ?_⟩
    have h1 : T.relIndex (xPreimage p E) ∣ X.relIndex (xPreimage p E) :=
      Subgroup.relIndex_dvd_of_le_left _ hXT
    exact fun hd => hX.2.2 (hd.trans h1)
  have hUn : ∀ n ∈ Subgroup.normalizer (E : Set G), ∀ u ∈ U, n * u * n⁻¹ ∈ U := by
    intro n hn u hu
    have hnW : n ∈ Subgroup.normalizer (xPreimage p E : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => conj_mem_xPreimage hn hy, fun hy => ?_⟩
      have := conj_mem_xPreimage (Subgroup.inv_mem _ hn) hy
      simpa [mul_assoc] using this
    obtain ⟨k, hk, hkn⟩ := Sec15Frattini.exists_mem_normalizer_of_isSylowOf hsyl hnW
    have h1 := hUi _ hkn u hu
    have h2 : n * u * n⁻¹ = k * ((k⁻¹ * n) * u * (k⁻¹ * n)⁻¹) * k⁻¹ := by group
    rw [h2, fix_of_mem_xPreimage ctx hk (hUB h1)]
    exact h1
  have hD := data_of_ctx ctx
  have hUE : U ≤ E := hUB.trans inf_le_left
  set S : Subgroup ↥E := U.subgroupOf E with hS
  have hSB : S ≤ (E ⊓ L).subgroupOf E := fun s hs => hUB hs
  have hSinv : ∀ w : ↥(torusWeyl E), ∀ s ∈ S, ((w : ↥(torusWeyl E)) : MulAut E) s ∈ S := by
    intro w s hs
    obtain ⟨⟨n, hn⟩, hnw⟩ := w.2
    have h1 : ((((w : ↥(torusWeyl E)) : MulAut E) s : ↥E) : G) = n * (s : G) * n⁻¹ := by
      rw [← hnw]
      exact Equivariance.coe_conjAut hn s
    show ((((w : ↥(torusWeyl E)) : MulAut E) s : ↥E) : G) ∈ U
    rw [h1]
    exact hUn n hn s hs
  rcases hD.B_irr S hSB hSinv with h0 | h1
  · left
    rw [eq_bot_iff]
    intro u hu
    have hmem : (⟨u, hUE hu⟩ : ↥E) ∈ S := hu
    rw [h0, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hmem)
  · right
    apply le_antisymm hUB
    intro x hx
    have hmem : (⟨x, hx.1⟩ : ↥E) ∈ (E ⊓ L).subgroupOf E := hx
    rw [← h1] at hmem
    exact hmem

theorem cycBase_of_ctx (h112 : InSec11Two) (ctx : Fus12Ctx G p A c L E)
    (hL : Layer1212 p A c L E b K I) (hC : Choice1212 p E b I X P Q) (hF : Field1213 p A c L b K I)
    (hgen : ∃ f ∈ P, P = Q ⊔ Subgroup.zpowers f) {r e : ℕ} (hr : r = 1 ∨ r = 2) (he2 : 2 ≤ e)
    (hEcard : Nat.card E = p ^ (r + 2)) (φ : ↥(P ⊓ I) ≃* (Fin r → Multiplicative (ZMod (p ^ e)))) :
    CycBase p c b E P Q (P ⊓ I) (Subgroup.centralizer (I : Set G) ⊓ P) := by
  obtain ⟨hp, hp5⟩ := prime_five_le ctx
  have : Fact p.Prime := ⟨hp⟩
  have hEP := E_le_P hC
  have hcE := c_mem_E ctx
  have hPp : IsPGroup p ↥P := P_isPGroup hC
  have hQ := Sec12Fus.q_normal hC
  have hbA := hL.b_mem
  have hbE : b ∈ E := ctx.hyp.A_le_E hbA.1
  refine
    { prime := hp
      p5 := hp5
      P_p := hPp
      Q_le := hQ.1
      Q_norm := fun x hx q hq => by
        have := hQ.2.conj_mem ⟨q, hQ.1 hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨x, hx⟩
        simpa using Subgroup.mem_subgroupOf.1 this
      P_gen := hgen
      Q_eq := hC.Q_eq
      Z_le := inf_le_right
      R_le := inf_le_left
      ZR := fun z hz r' hr' => (Subgroup.mem_centralizer_iff.1 hz.1 r' hr'.2).symm
      ZR_bot := ?_
      Z_norm := fun x hx z hz => by
        have hxN : x ∈ Subgroup.normalizer
            ((Subgroup.centralizer (I : Set G) ⊓ P : Subgroup G) : Set G) :=
          le_normalizer_centralizer_inf P I ⟨hx, hC.P_norm hx⟩
        exact (Subgroup.mem_normalizer_iff.1 hxN z).1 hz
      R_norm := fun x hx r' hr' =>
        (Subgroup.mem_normalizer_iff.1 (mem_normalizer_inf hx (hC.P_norm hx)) r').1 hr'
      c_P := hEP hcE
      c_E := hcE
      c_Q := c_not_mem_Q hF hC
      c_p := Sec12Three.pow_eq_one_of_mem_E ctx.hyp hcE
      b_E := hbE
      b_Z := ⟨Subgroup.mem_centralizer_iff.2 fun i hi => by
        have := Subgroup.mem_centralizer_iff.1 (I_le_centralizer hL hi) b (Set.mem_singleton b)
        exact this.symm, hEP hbE⟩
      b_ne := hbA.2.2
      b_cent := fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (hC.P_sylow.1.1 hx)
      E_le := hEP
      E_elem := ctx.hyp.E_elem
      E_max := fun F hF' hEF => ctx.hyp.E_max F hF' (fun f hf a ha =>
        Torsion37.mul_comm_of_isElementaryAbelian hF' (hEF (ctx.hyp.A_le_E ha)) hf) hEF
      shape := ⟨r, e, hr, he2, ⟨φ⟩, hEcard⟩ }
  refine eq_bot_of_pGroup_le (N := I ⊓ Subgroup.centralizer (I : Set G))
    (hPp.to_le (fun x hx => hx.1.1)) (fun x hx => ⟨hx.1.2, hx.2.1⟩) ?_
  rw [card_inf_centralizer]
  exact zI_pPrime h112 ctx hL hF

theorem cycData_of_ctx (h112 : InSec11Two) (ctx : Fus12Ctx G p A c L E)
    (hL : Layer1212 p A c L E b K I) (hC : Choice1212 p E b I X P Q) (hF : Field1213 p A c L b K I)
    (hgen : ∃ f ∈ P, P = Q ⊔ Subgroup.zpowers f) {r e : ℕ} (hr : r = 1 ∨ r = 2) (he2 : 2 ≤ e)
    (hEcard : Nat.card E = p ^ (r + 2)) (φ : ↥(P ⊓ I) ≃* (Fin r → Multiplicative (ZMod (p ^ e))))
    (hZab : ∀ z ∈ Subgroup.centralizer (I : Set G) ⊓ P, ∀ z' ∈ Subgroup.centralizer (I : Set G) ⊓ P,
      z * z' = z' * z)
    (_hZcard : Nat.card ↥(Subgroup.centralizer (I : Set G) ⊓ P) = p ^ e)
    (_hZY : Nat.card ↥(Subgroup.centralizer (I : Set G) ⊓ P) =
      p * Nat.card ↥(Subgroup.centralizer (I : Set G) ⊓ P ⊓ Subgroup.centralizer ({c} : Set G))) :
    CycData p c b E P Q (P ⊓ I) (Subgroup.centralizer (I : Set G) ⊓ P) :=
  { cycBase_of_ctx h112 ctx hL hC hF hgen hr he2 hEcard φ with Z_ab := hZab }

end CFSG.RankThree.PartOne.K1214
