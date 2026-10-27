module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7AmbientModel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UInterMCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCentralized
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The odd image in the A₇ branch has nontrivial 3-part

The quotient centralizer of the distinguished involution contains a
3-cycle.  We map a Sylow-3 subgroup of the centralizer through the quotient
and then use `H = S U` to place its odd ambient image inside `U ∩ M`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem secondCase_a7_u_inter_m_quotient_card_dvd_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    3 ∣ Nat.card (((c.U ⊓ w.M).subgroupOf w.M).map
      (QuotientGroup.mk' (pPrimeCore 2 w.M))) := by
  classical
  let M : Subgroup G := w.M
  let O : Subgroup M := pPrimeCore 2 M
  let : O.Normal := by
    dsimp [O]
    infer_instance
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  let Y : Subgroup M := (c.U ⊓ M).subgroupOf M
  let Ybar : Subgroup (M ⧸ O) := Y.map q
  have htM : c.t ∈ M :=
    (componentLayerOf_isNormalIn M).1 w.t_mem_componentLayer
  let tM : M := ⟨c.t, htM⟩
  have htMi : IsInvolution tM := by
    constructor
    · intro h
      exact c.t_involution.1 (by simpa [tM] using congrArg Subtype.val h)
    · exact Subtype.ext c.t_involution.2
  let T : Subgroup M := Subgroup.zpowers tM
  have hTcard : Nat.card T = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime htMi.2 htMi.1
  have hTp : IsPGroup 2 T := by
    apply IsPGroup.of_card (G := T) (n := 1)
    simpa [hTcard]
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 (↥T)) := ⟨hTp⟩
  have hOcop : Nat.Coprime 2 (Nat.card O) :=
    pPrimeCore_coprime_card (p := 2) (G := M)
  have hcentmap :
      Subgroup.centralizer ((T.map q : Subgroup (M ⧸ O)) : Set (M ⧸ O)) =
        (Subgroup.centralizer (T : Set M)).map q := by
    simpa [q] using
      (centralizer_map_quotient_eq_map_centralizer
        (G := M) (p := 2) T O (by infer_instance) hOcop)
  have hTsingle : Subgroup.centralizer (T : Set M) =
      Subgroup.centralizer ({tM} : Set M) := by
    dsimp [T]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hqT : T.map q = Subgroup.zpowers (q tM) := by
    simpa [T] using MonoidHom.map_zpowers q tM
  have hTqsingle : Subgroup.centralizer
      ((T.map q : Subgroup (M ⧸ O)) : Set (M ⧸ O)) =
      Subgroup.centralizer ({q tM} : Set (M ⧸ O)) := by
    rw [hqT, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp hOcop
  have hqt : IsInvolution (q tM) := by
    constructor
    · intro h
      have htO : tM ∈ O := (QuotientGroup.eq_one_iff (N := O) tM).mp h
      have h2dvd : 2 ∣ Nat.card O := by
        rw [← orderOf_eq_prime htMi.2 htMi.1]
        exact Subgroup.orderOf_dvd_natCard O htO
      exact hOodd.not_two_dvd_nat h2dvd
    · simpa [map_pow] using congrArg q htMi.2
  have hAmbient := secondCase_a7_ambient_quotient_model hmin c w d hA7 hmodel
  let eQ : (M ⧸ O) ≃* alternatingGroup (Fin 7) := hAmbient.some
  let qt : alternatingGroup (Fin 7) := eQ (q tM)
  have hqtI : IsInvolution qt := by
    constructor
    · intro h
      apply hqt.1
      apply eQ.injective
      simpa [qt] using h
    · simpa [qt, map_pow] using congrArg eQ hqt.2
  obtain ⟨g, hgt⟩ := aSeven_involutions_conjugate qt a7t (by
    simpa using hqtI) (by constructor <;> decide)
  have ha_ne : a7a ≠ (1 : alternatingGroup (Fin 7)) := by decide
  have ha_pow : a7a ^ 3 = (1 : alternatingGroup (Fin 7)) := by decide
  have ha_cent : a7a * a7t = a7t * a7a := by decide
  let b : alternatingGroup (Fin 7) := g⁻¹ * a7a * g
  have hb_pow : b ^ 3 = (1 : alternatingGroup (Fin 7)) := by
    dsimp [b]
    calc
      (g⁻¹ * a7a * g) ^ 3 =
          (g⁻¹ * a7a * g) * (g⁻¹ * a7a * g) * (g⁻¹ * a7a * g) := by
        change (g⁻¹ * a7a * g) * (g⁻¹ * a7a * g) *
          (g⁻¹ * a7a * g) = _
        rfl
      _ = g⁻¹ * a7a ^ 3 * g := by
        rw [show a7a ^ 3 = a7a * a7a * a7a by
          rw [pow_succ, pow_two]]
        group
      _ = 1 := by rw [ha_pow]; simp
  have hb_ne : b ≠ (1 : alternatingGroup (Fin 7)) := by
    intro hb
    apply ha_ne
    calc
      a7a = g * (g⁻¹ * a7a * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by change g * b * g⁻¹ = _; rw [hb]
      _ = 1 := by simp
  have hb_order : orderOf b = 3 := orderOf_eq_prime hb_pow hb_ne
  have hb_cent : b ∈ Subgroup.centralizer ({qt} : Set (alternatingGroup (Fin 7))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      b * qt = (g⁻¹ * a7a * g) * qt := rfl
      _ = g⁻¹ * a7a * (g * qt) := by group
      _ = g⁻¹ * a7a * (a7t * g) := by rw [← hgt]; group
      _ = g⁻¹ * (a7a * a7t) * g := by group
      _ = g⁻¹ * (a7t * a7a) * g := by rw [ha_cent]
      _ = (g⁻¹ * a7t * g) * (g⁻¹ * a7a * g) := by group
      _ = qt * b := by
        have hgt' : g⁻¹ * a7t * g = qt := by
          rw [← hgt]
          group
        rw [hgt']
  have hbq_cent : eQ.symm b ∈
      Subgroup.centralizer ({q tM} : Set (M ⧸ O)) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply eQ.injective
    simpa [qt, map_mul, map_inv] using
      (Subgroup.mem_centralizer_singleton_iff.mp hb_cent)
  have hbq_mem : eQ.symm b ∈
      Subgroup.centralizer ((T.map q : Subgroup (M ⧸ O)) : Set (M ⧸ O)) := by
    rw [hTqsingle]
    exact hbq_cent
  have h3cardCq : 3 ∣ Nat.card
      (Subgroup.centralizer ({q tM} : Set (M ⧸ O))) := by
    have hdiv : orderOf (eQ.symm b) ∣ Nat.card
        (Subgroup.centralizer ((T.map q : Subgroup (M ⧸ O)) : Set (M ⧸ O))) := by
      exact Subgroup.orderOf_dvd_natCard _ hbq_mem
    rw [hTqsingle] at hdiv
    have hord : orderOf (eQ.symm b) = orderOf b := by
      simpa using (MulEquiv.orderOf_eq eQ (eQ.symm b)).symm
    rw [hord, hb_order] at hdiv
    exact hdiv
  let C0 : Subgroup M := Subgroup.centralizer ({tM} : Set M)
  let Cq : Subgroup (M ⧸ O) := C0.map q
  have hCq_eq : Cq = Subgroup.centralizer ({q tM} : Set (M ⧸ O)) := by
    calc
      Cq = (Subgroup.centralizer ({tM} : Set M)).map q := rfl
      _ = (Subgroup.centralizer (T : Set M)).map q := by rw [hTsingle]
      _ = Subgroup.centralizer ((T.map q : Subgroup (M ⧸ O)) : Set (M ⧸ O)) :=
        hcentmap.symm
      _ = Subgroup.centralizer ({q tM} : Set (M ⧸ O)) := hTqsingle
  have hCqcard3 : 3 ∣ Nat.card Cq := by
    rw [hCq_eq]
    exact h3cardCq
  obtain ⟨P⟩ : Nonempty (Sylow 3 C0) := inferInstance
  let fr : C0 →* Cq := (q.comp C0.subtype).codRestrict Cq (by
    intro x
    exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  have hfr : Function.Surjective fr := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
    let x0 : C0 := ⟨x, hx⟩
    refine ⟨x0, ?_⟩
    apply Subtype.ext
    simpa [fr, x0] using hxy
  let Q : Sylow 3 Cq := P.mapSurjective (f := fr) hfr
  have hQmap : (Q : Subgroup Cq) = (P : Subgroup C0).map fr :=
    Sylow.coe_mapSurjective hfr P
  have hQne : (Q : Subgroup Cq) ≠ ⊥ := by
    intro hbot
    have hQcard : Nat.card (Q : Subgroup Cq) = 1 := by
      simpa [hbot]
    have hmul := Subgroup.card_mul_index (Q : Subgroup Cq)
    rw [hQcard] at hmul
    simp at hmul
    have h3idx : 3 ∣ Q.index := by
      rw [hmul]
      exact hCqcard3
    exact Q.not_dvd_index h3idx
  have hQ3 : 3 ∣ Nat.card (Q : Subgroup Cq) := by
    obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
    have hnne : n ≠ 0 := by
      intro hn0
      apply hQne
      have hcardone : Nat.card (Q : Subgroup Cq) = 1 := by
        subst n
        simpa using hn
      exact (Subgroup.eq_bot_iff_card (H := (Q : Subgroup Cq))).mpr hcardone
    rw [hn]
    exact dvd_pow_self 3 hnne
  let PM : Subgroup M := (P : Subgroup C0).map C0.subtype
  let Qamb : Subgroup (M ⧸ O) := (Q : Subgroup Cq).map Cq.subtype
  have hQamb_eq : Qamb = PM.map q := by
    have hfrcomp : Cq.subtype.comp fr = q.comp C0.subtype := by
      ext z
      rfl
    dsimp [Qamb, PM]
    rw [hQmap]
    simpa [hfrcomp, Subgroup.map_map]
  have hQamb3 : 3 ∣ Nat.card Qamb := by
    have hcard : Nat.card Qamb = Nat.card (Q : Subgroup Cq) :=
      Subgroup.card_map_of_injective Cq.subtype_injective
    rw [hcard]
    exact hQ3
  have hC0leH : C0.map M.subtype ≤ c.H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, rfl⟩
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hx0
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    simpa [tM] using congrArg Subtype.val hcomm
  have hPodd : Odd (Nat.card (P : Subgroup C0)) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    exact hn ▸ Odd.pow (by decide)
  have hPMleU : PM.map M.subtype ≤ c.U := by
    exact odd_order_subgroup_le_U_of_H_eq_SU hmin c
      ((Subgroup.map_mono (Subgroup.map_subtype_le (P : Subgroup C0))).trans hC0leH)
      (Nat.coprime_two_left.mpr (by
        have hPMcard : Nat.card (PM.map M.subtype) =
            Nat.card (P : Subgroup C0) := by
          calc
            Nat.card (PM.map M.subtype) = Nat.card PM :=
              Subgroup.card_map_of_injective M.subtype_injective
            _ = Nat.card (P : Subgroup C0) := by
              dsimp [PM]
              exact Subgroup.card_map_of_injective C0.subtype_injective
        rw [hPMcard]
        exact hPodd))
  have hPMleY : PM ≤ Y := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr ⟨hPMleU
      (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩), x.2⟩
  have hQamb_le_Ybar : Qamb ≤ Ybar := by
    rw [hQamb_eq]
    exact Subgroup.map_mono hPMleY
  exact dvd_trans hQamb3 (Subgroup.card_dvd_of_le hQamb_le_Ybar)

end CFSG.GorensteinWalter
