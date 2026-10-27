module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3

namespace CFSG
end CFSG
open CFSG

/-!
# A normal Sylow intersection lemma for Proposition 8.4

The proper-predecessor argument intersects the unique Sylow `2`-subgroup of
`M ∩ F₀` with `M ∩ F`.  The theorem below isolates the general finite-group
fact used there.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open scoped Pointwise

universe u

/-- If `P` is a normal Sylow `p`-subgroup of `G`, then `P ∩ H` is a normal
Sylow `p`-subgroup of every subgroup `H ≤ G`. -/
public theorem exists_sylow_inf_of_normal_sylow
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hPnormal : (P : Subgroup G).Normal)
    (H : Subgroup G) :
    ∃ Q : Sylow p H,
      (Q : Subgroup H).map H.subtype = (P : Subgroup G) ⊓ H ∧
        (Q : Subgroup H).Normal := by
  let R : Subgroup G := (P : Subgroup G) ⊓ H
  let RH : Subgroup H := R.subgroupOf H
  have hRHp : IsPGroup p RH := by
    let f : RH →* (P : Subgroup G) :=
      { toFun := fun r => ⟨(r : G), r.property.1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact P.isPGroup'.of_injective f (by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : (P : Subgroup G) => (z : G)) hab)
  obtain ⟨Q, hRHQ⟩ := hRHp.exists_le_sylow
  have hQmapP : IsPGroup p ((Q : Subgroup H).map H.subtype) :=
    Q.isPGroup'.map H.subtype
  obtain ⟨T, hQT⟩ := hQmapP.exists_le_sylow
  letI : Unique (Sylow p G) := Sylow.unique_of_normal P hPnormal
  have hTP : T = P := Subsingleton.elim _ _
  have hQleP : (Q : Subgroup H).map H.subtype ≤ (P : Subgroup G) := by
    rw [← hTP]
    exact hQT
  have hmap : (Q : Subgroup H).map H.subtype = R := le_antisymm (by
      intro x hx
      exact ⟨hQleP hx, Subgroup.map_subtype_le (Q : Subgroup H) hx⟩) (by
      intro x hx
      rw [Subgroup.mem_map]
      let xH : H := ⟨x, hx.2⟩
      refine ⟨xH, hRHQ ?_, rfl⟩
      exact hx)
  have hQleRH : (Q : Subgroup H) ≤ RH := by
    intro q hq
    change ((q : G) ∈ P ∧ (q : G) ∈ H)
    have hqmap : (q : G) ∈ (Q : Subgroup H).map H.subtype :=
      ⟨q, hq, rfl⟩
    have hqR : (q : G) ∈ R := by
      rw [← hmap]
      exact hqmap
    change (q : G) ∈ (P : Subgroup G) ∧ (q : G) ∈ H at hqR
    exact hqR
  have hQRH : (Q : Subgroup H) = RH := le_antisymm hQleRH hRHQ
  have hRHnormal : RH.Normal := by
    have hcomap : ((P : Subgroup G).comap H.subtype).Normal :=
      hPnormal.comap H.subtype
    simpa [RH, R] using hcomap
  refine ⟨Q, ?_, ?_⟩
  · simpa [R] using hmap
  · simpa [hQRH] using hRHnormal

/-- Ambient version of `exists_sylow_inf_of_normal_sylow`: both the large
and small groups are literal subgroups of the same group. -/
public theorem exists_sylow_map_eq_inf_of_normal_sylow_map
    {X : Type u} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (G H : Subgroup X) (hHG : H ≤ G)
    (P : Sylow p G) (hPnormal : (P : Subgroup G).Normal) :
    ∃ Q : Sylow p H,
      (Q : Subgroup H).map H.subtype =
          (P : Subgroup G).map G.subtype ⊓ H ∧
        (Q : Subgroup H).Normal := by
  let K : Subgroup G := H.subgroupOf G
  obtain ⟨R, hRmap, hRnormal⟩ :=
    exists_sylow_inf_of_normal_sylow P hPnormal K
  let e : K ≃* H := Subgroup.subgroupOfEquivOfLe hHG
  let Q : Sylow p H :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective R
  have hQmap : (Q : Subgroup H) =
      (R : Subgroup K).map e.toMonoidHom := by
    exact Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective R
  have hQnormal : (Q : Subgroup H).Normal := by
    rw [hQmap]
    exact hRnormal.map e.toMonoidHom e.surjective
  refine ⟨Q, ?_, hQnormal⟩
  calc
    (Q : Subgroup H).map H.subtype =
        ((R : Subgroup K).map e.toMonoidHom).map H.subtype := by
          exact congrArg (fun L : Subgroup H => L.map H.subtype) hQmap
    _ = (R : Subgroup K).map (H.subtype.comp e.toMonoidHom) := by
          rw [Subgroup.map_map]
    _ = (R : Subgroup K).map (G.subtype.comp K.subtype) := by
          congr 1
    _ = ((R : Subgroup K).map K.subtype).map G.subtype := by
          rw [Subgroup.map_map]
    _ = ((P : Subgroup G) ⊓ K).map G.subtype := by rw [hRmap]
    _ = (P : Subgroup G).map G.subtype ⊓ K.map G.subtype := by
          exact Subgroup.map_inf _ _ _ G.subtype_injective
    _ = (P : Subgroup G).map G.subtype ⊓ H := by
          rw [show K.map G.subtype = H by
            simpa [K, inf_eq_left.mpr hHG] using
              Subgroup.subgroupOf_map_subtype H G]

/-- A characteristic subgroup of a subgroup normal in `N` is normal in `N`,
after all subgroup inclusions are mapped into the same ambient group. -/
public theorem normal_subgroupOf_map_of_characteristic_of_normal
    {X : Type u} [Group X]
    (H K N : Subgroup X) (hHN : H ≤ N)
    (hHnormal : (H.subgroupOf N).Normal)
    (P : Subgroup H) (hPchar : P.Characteristic)
    (hKmap : K = P.map H.subtype) (hKN : K ≤ N) :
    (K.subgroupOf N).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hKN]
  intro k n hk hn
  change n * k * n⁻¹ ∈ K
  have hnNormH : n ∈ Subgroup.normalizer (H : Set X) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hHN).mp hHnormal) hn
  rw [hKmap] at hk ⊢
  rcases hk with ⟨p, hp, rfl⟩
  let nn : Subgroup.normalizer (H : Set X) := ⟨n, hnNormH⟩
  let e : H ≃* H := H.normalizerMonoidHom nn
  have hfixed : P.comap e.toMonoidHom = P := hPchar.fixed e
  refine ⟨e p, ?_, ?_⟩
  · change p ∈ P.comap e.toMonoidHom
    rw [hfixed]
    exact hp
  · simp [e, nn, Subgroup.normalizerMonoidHom_apply_apply_coe]

/-- If a normal complement is centralized by its complementary subgroup,
then the complementary subgroup is normal as well. -/
public theorem normal_of_complement_centralizes
    {G : Type u} [Group G]
    {K P : Subgroup G} [K.Normal]
    (hcomp : K.IsComplement' P)
    (hcent : P ≤ Subgroup.centralizer (K : Set G)) :
    P.Normal := by
  have hK_le_normP : K ≤ Subgroup.normalizer (P : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      have hpcent := Subgroup.mem_centralizer_iff.mp (hcent hp) k hk
      have hconj : k * p * k⁻¹ = p := by
        calc
          k * p * k⁻¹ = (p * k) * k⁻¹ := by rw [hpcent]
          _ = p := by simp [mul_assoc]
      simpa [hconj] using hp
    · intro hconj
      let s : G := k * p * k⁻¹
      have hscent := Subgroup.mem_centralizer_iff.mp (hcent hconj) k hk
      have hback : k⁻¹ * s * k = s := by
        calc
          k⁻¹ * s * k = k⁻¹ * (s * k) := by rw [mul_assoc]
          _ = k⁻¹ * (k * s) := by rw [← hscent]
          _ = s := by simp
      have hp_eq : p = s := by
        calc
          p = k⁻¹ * (k * p * k⁻¹) * k := by simp [mul_assoc]
          _ = k⁻¹ * s * k := by rfl
          _ = s := hback
      rw [hp_eq]
      exact hconj
  have htop_le : (⊤ : Subgroup G) ≤
      Subgroup.normalizer (P : Set G) := by
    rw [← hcomp.sup_eq_top]
    exact sup_le hK_le_normP Subgroup.le_normalizer
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop_le)

/-- Lift a normal Sylow `2`-subgroup through a central odd-order kernel.
The lifted Sylow is normal, has the prescribed quotient image, and the
quotient map is injective on its ambient image. -/
public theorem sylow_lift_of_central_odd_core
    {F : Type u} [Group F] [Finite F]
    (K H : Subgroup F) [K.Normal]
    (hKH : K ≤ H)
    (hKodd : Nat.Coprime 2 (Nat.card K))
    (hKcentral : K ≤ Subgroup.center F)
    (Pbar : Sylow 2 (H.map (QuotientGroup.mk' K)))
    (hPbarNormal :
      (Pbar : Subgroup (H.map (QuotientGroup.mk' K))).Normal) :
    ∃ P : Sylow 2 H,
      (P : Subgroup H).Normal ∧
      ((P : Subgroup H).map H.subtype).map (QuotientGroup.mk' K) =
        (Pbar : Subgroup (H.map (QuotientGroup.mk' K))).map
          (H.map (QuotientGroup.mk' K)).subtype ∧
      Function.Injective
        ((QuotientGroup.mk' K).comp
          ((P : Subgroup H).map H.subtype).subtype) := by
  let q : F →* (F ⧸ K) := QuotientGroup.mk' K
  let B : Subgroup (F ⧸ K) := H.map q
  let qH : H →* B :=
    (q.comp H.subtype).codRestrict B (by
      intro h
      exact ⟨h, h.property, rfl⟩)
  have hqHsurj : Function.Surjective qH := by
    intro b
    rcases b.property with ⟨h, hh, hb⟩
    refine ⟨⟨h, hh⟩, Subtype.ext ?_⟩
    exact hb
  let P : Sylow 2 H := default
  let Pmap : Sylow 2 B := P.mapSurjective (f := qH) hqHsurj
  have hPmap : (Pmap : Subgroup B) = (Pbar : Subgroup B) := by
    letI : Unique (Sylow 2 B) :=
      Sylow.unique_of_normal Pbar hPbarNormal
    exact congrArg Sylow.toSubgroup (Subsingleton.elim Pmap Pbar)
  have hPmapSub :
      ((P : Subgroup H).map H.subtype).map q =
        (Pbar : Subgroup B).map B.subtype := by
    calc
      ((P : Subgroup H).map H.subtype).map q =
          (P : Subgroup H).map (q.comp H.subtype) := by
        rw [Subgroup.map_map]
      _ = ((P : Subgroup H).map qH).map B.subtype := by
        rw [Subgroup.map_map]
        rfl
      _ = (Pmap : Subgroup B).map B.subtype := by rfl
      _ = (Pbar : Subgroup B).map B.subtype := by rw [hPmap]
  have hK_Hcard : Nat.card (K.subgroupOf H) = Nat.card K := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hP_Kcop : Nat.Coprime (Nat.card (P : Subgroup H))
      (Nat.card (K.subgroupOf H)) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn, hK_Hcard]
    exact hKodd.pow_left n
  have hPKbot : (P : Subgroup H) ⊓ K.subgroupOf H = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime hP_Kcop
  let E : Subgroup H := (Pbar : Subgroup B).comap qH
  have hP_le_E : (P : Subgroup H) ≤ E := by
    intro p hp
    change qH p ∈ (Pbar : Subgroup B)
    rw [← hPmap]
    change qH p ∈ (P : Subgroup H).map qH
    exact Subgroup.mem_map_of_mem qH hp
  have hE_normal_H : E.Normal := by
    exact hPbarNormal.comap qH
  have hKsub_le_E : K.subgroupOf H ≤ E := by
    intro k hk
    change qH k ∈ (Pbar : Subgroup B)
    have hkone : qH k = 1 := by
      apply Subtype.ext
      change q (k : F) = 1
      exact (QuotientGroup.eq_one_iff (N := K) (k : F)).2 hk
    rw [hkone]
    exact (Pbar : Subgroup B).one_mem
  have hsup_E :
      (P : Subgroup H) ⊔ K.subgroupOf H = E := by
    apply le_antisymm
    · exact sup_le hP_le_E hKsub_le_E
    · intro h hh
      have hqmem : qH h ∈ (Pbar : Subgroup B) := hh
      rw [← hPmap] at hqmem
      change qH h ∈ (P : Subgroup H).map qH at hqmem
      rcases Subgroup.mem_map.mp hqmem with ⟨p, hp, hqp⟩
      let pP : P := ⟨p, hp⟩
      have hkp : h * p⁻¹ ∈ K.subgroupOf H := by
        change (h : F) * (p : F)⁻¹ ∈ K
        apply (QuotientGroup.eq_one_iff (N := K) _).1
        change q ((h : F) * (p : F)⁻¹) = 1
        rw [map_mul, map_inv]
        have hqpval : q (p : F) = q (h : F) := by
          exact congrArg Subtype.val hqp
        rw [hqpval]
        simp
      have hmul : (h * p⁻¹) * p = h := by group
      rw [← hmul]
      apply ((P : Subgroup H) ⊔ K.subgroupOf H).mul_mem
      · exact (show K.subgroupOf H ≤
          (P : Subgroup H) ⊔ K.subgroupOf H from le_sup_right) hkp
      · exact (show (P : Subgroup H) ≤
          (P : Subgroup H) ⊔ K.subgroupOf H from le_sup_left) hp
  have hcomp :
      let PE : Subgroup E := (P : Subgroup H).subgroupOf E
      let KE : Subgroup E := (K.subgroupOf H).subgroupOf E
      KE.IsComplement' PE := by
    let PE : Subgroup E := (P : Subgroup H).subgroupOf E
    let KE : Subgroup E := (K.subgroupOf H).subgroupOf E
    letI : (K.subgroupOf H).Normal :=
      (inferInstance : K.Normal).subgroupOf H
    letI : KE.Normal :=
      (inferInstance : (K.subgroupOf H).Normal).subgroupOf E
    have hdisj : Disjoint KE PE := by
      rw [Subgroup.disjoint_def]
      intro x hxK hxP
      apply Subtype.ext
      have hxPK : (x : H) ∈
          (P : Subgroup H) ⊓ K.subgroupOf H := ⟨hxP, hxK⟩
      rw [hPKbot] at hxPK
      simpa using hxPK
    have hsup : KE ⊔ PE = ⊤ := by
      have hPEKE : PE ⊔ KE = ⊤ := by
        simpa [PE, KE, hsup_E] using
          (Subgroup.subgroupOf_sup hP_le_E hKsub_le_E).symm
      simpa [sup_comm] using hPEKE
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      KE PE hdisj hsup
  let PE : Subgroup E := (P : Subgroup H).subgroupOf E
  let KE : Subgroup E := (K.subgroupOf H).subgroupOf E
  letI : (K.subgroupOf H).Normal :=
    (inferInstance : K.Normal).subgroupOf H
  letI : E.Normal := hE_normal_H
  letI : KE.Normal :=
    (inferInstance : (K.subgroupOf H).Normal).subgroupOf E
  have hPEcentral : PE ≤ Subgroup.centralizer (KE : Set E) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    apply Subtype.ext
    change (k : H) * (p : H) = (p : H) * (k : H)
    apply Subtype.ext
    exact ((Subgroup.mem_center_iff.mp (hKcentral hk)) (p : F)).symm
  have hPENormal : PE.Normal :=
    normal_of_complement_centralizes hcomp hPEcentral
  have hPNormal : (P : Subgroup H).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    intro h _hh
    apply Subgroup.mem_normalizer_fintype
    intro p hp
    let e : E ≃* E := MulAut.conjNormal h
    let PEsyl : Sylow 2 E := P.subtype hP_le_E
    have hPEsylNormal : (PEsyl : Subgroup E).Normal := by
      simpa [PEsyl, PE, Sylow.coe_subtype] using hPENormal
    let Pconj : Sylow 2 E :=
      PEsyl.mapSurjective (f := e.toMonoidHom) e.surjective
    letI : Unique (Sylow 2 E) :=
      Sylow.unique_of_normal PEsyl hPEsylNormal
    have hPconj : (Pconj : Subgroup E) = (PEsyl : Subgroup E) :=
      congrArg Sylow.toSubgroup (Subsingleton.elim Pconj PEsyl)
    let pE : E := ⟨p, hP_le_E hp⟩
    have hep : e pE ∈ (Pconj : Subgroup E) := by
      change e pE ∈ (PEsyl : Subgroup E).map e.toMonoidHom
      have hpPE : pE ∈ (PEsyl : Subgroup E) := by
        exact hp
      exact Subgroup.mem_map_of_mem e.toMonoidHom hpPE
    rw [hPconj] at hep
    change h * p * h⁻¹ ∈ (P : Subgroup H)
    have hep' : (e pE : H) ∈ (P : Subgroup H) := by
      have hep'' := Subgroup.mem_subgroupOf.mp hep
      simpa [PEsyl, Sylow.coe_subtype] using hep''
    simpa [e, pE, MulAut.conjNormal_apply, MulAut.conj_apply] using hep'
  have hinj : Function.Injective
      (q.comp (((P : Subgroup H).map H.subtype)).subtype) := by
    intro x y hxy
    rcases Subgroup.mem_map.mp x.property with ⟨px, hpx, hpxval⟩
    rcases Subgroup.mem_map.mp y.property with ⟨py, hpy, hpyval⟩
    apply Subtype.ext
    have hqxy : q (px : F) = q (py : F) := by
      change q (x : F) = q (y : F) at hxy
      calc
        q (px : F) = q (x : F) := congrArg q hpxval
        _ = q (y : F) := hxy
        _ = q (py : F) := (congrArg q hpyval).symm
    have hdivK : (px : F) / (py : F) ∈ K :=
      QuotientGroup.eq_iff_div_mem.mp hqxy
    have hdivKH : px / py ∈ K.subgroupOf H := hdivK
    have hdivP : px / py ∈ (P : Subgroup H) :=
      (P : Subgroup H).div_mem hpx hpy
    have hdivBot : px / py ∈ (⊥ : Subgroup H) := by
      rw [← hPKbot]
      exact ⟨hdivP, hdivKH⟩
    have hpxy : px = py := div_eq_one.mp (by simpa using hdivBot)
    calc
      (x : F) = (px : F) := hpxval.symm
      _ = (py : F) := congrArg Subtype.val hpxy
      _ = (y : F) := hpyval
  exact ⟨P, hPNormal, by simpa [q, B] using hPmapSub,
    by simpa [q] using hinj⟩

/-! ## Sylow transfer through a normalizer factor -/

private theorem natCard_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type u} [Group G] (A B : Subgroup G)
    (hnorm : B ≤ Subgroup.normalizer (A : Set G))
    (hdisj : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G),
      Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have hinj : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisj
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective toSup := by
    intro x
    have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnorm]
      exact x.property
    rcases hx with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinj, hsurj⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

/-- Low-layer form of the normalizer criterion used by the Section 9
Sylow transfer. -/
private theorem exists_sylow_map_eq_of_normalizer_le_low
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M : Subgroup G} (P : Sylow p M)
    (hN : Subgroup.normalizer
      (((P : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M) :
    ∃ P0 : Sylow p G,
      (P0 : Subgroup G) = (P : Subgroup M).map M.subtype := by
  classical
  let P0sub : Subgroup G := (P : Subgroup M).map M.subtype
  have hP0p : IsPGroup p P0sub :=
    IsPGroup.map P.isPGroup' M.subtype
  refine ⟨⟨P0sub, hP0p, ?_⟩, rfl⟩
  intro Q hQp hP0Q
  have hQ_le_P0 : Q ≤ P0sub := by
    let K : Subgroup Q := P0sub.subgroupOf Q
    haveI : Fact (IsPGroup p Q) := ⟨hQp⟩
    have hQnil : Group.IsNilpotent Q :=
      IsPGroup.isNilpotent (p := p) (G := Q) hQp
    have hnc : NormalizerCondition Q := by
      letI : Group.IsNilpotent Q := hQnil
      exact normalizerCondition_of_isNilpotent (G := Q)
    have hnormalizerK_le : Subgroup.normalizer (K : Set Q) ≤ K := by
      intro x hxnormalizer
      have hxnormalizerP0 :
          (x : G) ∈ Subgroup.normalizer (P0sub : Set G) := by
        refine Subgroup.mem_normalizer_fintype ?_
        intro y hyP0
        have hyQ : y ∈ Q := hP0Q hyP0
        have hyK : (⟨y, hyQ⟩ : Q) ∈ K := hyP0
        have hconjK :
            x * (⟨y, hyQ⟩ : Q) * x⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp hxnormalizer
            (⟨y, hyQ⟩ : Q)).1 hyK
        exact hconjK
      have hxM : (x : G) ∈ M := hN hxnormalizerP0
      let R : Subgroup M := (Q ⊓ M).subgroupOf M
      have hRp : IsPGroup p R := by
        have hInfp : IsPGroup p (Q ⊓ M : Subgroup G) :=
          hQp.to_inf_left
        have e : R ≃* (Q ⊓ M : Subgroup G) :=
          Subgroup.subgroupOfEquivOfLe
            (H := Q ⊓ M) (K := M) inf_le_right
        exact hInfp.of_equiv e.symm
      have hP_le_R : (P : Subgroup M) ≤ R := by
        intro y hyP
        have hyP0 : (y : G) ∈ P0sub :=
          Subgroup.mem_map_of_mem M.subtype hyP
        exact ⟨hP0Q hyP0, y.property⟩
      have hR_eq : R = (P : Subgroup M) :=
        P.is_maximal' hRp hP_le_R
      have hxR : (⟨(x : G), hxM⟩ : M) ∈ R :=
        ⟨x.property, hxM⟩
      have hxP : (⟨(x : G), hxM⟩ : M) ∈ (P : Subgroup M) := by
        simpa [hR_eq] using hxR
      have hxP0 : (x : G) ∈ P0sub :=
        Subgroup.mem_map_of_mem M.subtype hxP
      exact hxP0
    have hnormalizerK_eq : Subgroup.normalizer (K : Set Q) = K :=
      le_antisymm hnormalizerK_le Subgroup.le_normalizer
    have hKtop : K = ⊤ :=
      normalizerCondition_iff_only_full_group_self_normalizing.mp
        hnc K hnormalizerK_eq
    intro x hxQ
    have hxK : (⟨x, hxQ⟩ : Q) ∈ K := by simp [hKtop]
    exact hxK
  exact le_antisymm hQ_le_P0 hP0Q

private theorem exists_sylow_map_eq_of_le_of_sylow_map_eq
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {Y H E : Subgroup G}
    (hYH : Y ≤ H) (hHE : H ≤ E)
    (P : Sylow p E)
    (hPmap : (P : Subgroup E).map E.subtype = Y) :
    ∃ Q : Sylow p H,
      (Q : Subgroup H).map H.subtype = Y := by
  classical
  have hYE : Y ≤ E := hYH.trans hHE
  have hPE : (P : Subgroup E) = Y.subgroupOf E := by
    apply Subgroup.map_injective E.subtype_injective
    rw [hPmap]
    exact (Subgroup.map_subgroupOf_eq_of_le hYE).symm
  let YH : Subgroup H := Y.subgroupOf H
  have hYp : IsPGroup p Y := by
    have hPp := P.isPGroup'.map E.subtype
    rw [hPmap] at hPp
    exact hPp
  have hYHp : IsPGroup p YH := by
    exact hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYH).symm
  have hnot : ¬ p ∣ YH.index := by
    change ¬ p ∣ Y.relIndex H
    intro hp
    have hpE : p ∣ Y.relIndex E := by
      rw [← Subgroup.relIndex_mul_relIndex Y H E hYH hHE]
      exact dvd_mul_of_dvd_left hp _
    apply P.not_dvd_index
    simpa [Subgroup.relIndex, hPE] using hpE
  let Q : Sylow p H := hYHp.toSylow hnot
  refine ⟨Q, ?_⟩
  change YH.map H.subtype = Y
  exact Subgroup.map_subgroupOf_eq_of_le hYH

private theorem disjoint_of_isPGroup_two_of_odd_card
    {G : Type u} [Group G] [Finite G]
    (S H : Subgroup G) (hS2 : IsPGroup 2 S)
    (hHodd : Odd (Nat.card H)) :
    Disjoint S H := by
  rw [disjoint_iff]
  let I : Subgroup G := S ⊓ H
  have hI2 : IsPGroup 2 I := by
    exact (hS2.to_subgroup (I.subgroupOf S)).of_equiv
      (Subgroup.subgroupOfEquivOfLe inf_le_left)
  have hIodd : Odd (Nat.card I) := by
    apply hHodd.of_dvd_nat
    exact Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨n, hn⟩ := hI2.exists_card_eq
  have hnzero : n = 0 := by
    by_contra hnne
    have hIeven : Even (Nat.card I) := by
      rw [hn]
      exact even_two.pow_of_ne_zero hnne
    exact (Nat.not_even_iff_odd.mpr hIodd) hIeven
  have hIcard : Nat.card I = 1 := by simpa [hnzero] using hn
  simpa [I] using (Subgroup.card_eq_one.mp hIcard)

private theorem sylow_sup_of_sylow_right_of_two_left
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpne2 : p ≠ 2)
    {S H Y : Subgroup G}
    (hS2 : IsPGroup 2 S)
    (hnorm : H ≤ Subgroup.normalizer (S : Set G))
    (hdisj : Disjoint S H)
    (P : Sylow p H)
    (hPmap : (P : Subgroup H).map H.subtype = Y) :
    ∃ Q : Sylow p ↥(S ⊔ H : Subgroup G),
      (Q : Subgroup ↥(S ⊔ H : Subgroup G)).map
        (S ⊔ H : Subgroup G).subtype = Y := by
  classical
  have hYH : Y ≤ H := by
    rw [← hPmap]
    exact Subgroup.map_subtype_le (P : Subgroup H)
  have hYsup : Y ≤ S ⊔ H := hYH.trans le_sup_right
  let Ysup : Subgroup ↥(S ⊔ H : Subgroup G) :=
    Y.subgroupOf (S ⊔ H : Subgroup G)
  have hYp : IsPGroup p Y := by
    have hPp := P.isPGroup'.map H.subtype
    rw [hPmap] at hPp
    exact hPp
  have hYsupp : IsPGroup p Ysup := by
    exact hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYsup).symm
  have hcardY : Nat.card Y = Nat.card (P : Subgroup H) := by
    have hcard := Subgroup.card_map_of_injective
      (K := (P : Subgroup H)) H.subtype_injective
    simpa [hPmap] using hcard
  have hcardYsup : Nat.card Ysup = Nat.card (P : Subgroup H) := by
    calc
      Nat.card Ysup = Nat.card Y := by
        simpa [Ysup] using
          natCard_subgroupOf_eq Y (S ⊔ H) hYsup
      _ = Nat.card (P : Subgroup H) := hcardY
  obtain ⟨n, hn⟩ := hS2.exists_card_eq
  have hcopS : Nat.Coprime p (Nat.card S) := by
    rw [hn]
    exact ((Nat.coprime_primes (Fact.out : Nat.Prime p)
      Nat.prime_two).2 hpne2).pow_right n
  have hcardSup : Nat.card (S ⊔ H : Subgroup G) =
      Nat.card S * Nat.card H :=
    natCard_sup_eq_mul_of_disjoint_of_le_normalizer S H hnorm hdisj
  have hindex : Ysup.index = Nat.card S * P.index := by
    apply Nat.mul_left_cancel
      (Nat.card_pos : 0 < Nat.card (P : Subgroup H))
    calc
      Nat.card (P : Subgroup H) * Ysup.index =
          Nat.card Ysup * Ysup.index := by rw [hcardYsup]
      _ = Nat.card ↥(S ⊔ H : Subgroup G) := Ysup.card_mul_index
      _ = Nat.card S * Nat.card H := hcardSup
      _ = Nat.card S *
          (Nat.card (P : Subgroup H) * P.index) := by
            rw [P.1.card_mul_index]
      _ = Nat.card (P : Subgroup H) *
          (Nat.card S * P.index) := by ac_rfl
  have hnot : ¬ p ∣ Ysup.index := by
    rw [hindex]
    exact (Fact.out : Nat.Prime p).not_dvd_mul
      ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcopS)
      P.not_dvd_index
  let Q : Sylow p ↥(S ⊔ H : Subgroup G) := hYsupp.toSylow hnot
  refine ⟨Q, ?_⟩
  change Ysup.map (S ⊔ H : Subgroup G).subtype = Y
  exact Subgroup.map_subgroupOf_eq_of_le hYsup

private theorem exists_sylow_normalizerIn_of_two_factor
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {C E S Y : Subgroup G}
    (hEC : E ≤ C) (hYE : Y ≤ E)
    (hEodd : Odd (Nat.card E))
    (hSN : S ≤ normalizerIn C Y)
    (hS2 : IsPGroup 2 S)
    (hSnormal : (S.subgroupOf (normalizerIn C Y)).Normal)
    (hfactor :
      (normalizerIn C Y : Set G) =
        (S : Set G) * (normalizerIn E Y : Set G))
    (P : Sylow p E)
    (hPmap : (P : Subgroup E).map E.subtype = Y) :
    ∃ Q : Sylow p (normalizerIn C Y),
      (Q : Subgroup (normalizerIn C Y)).map
        (normalizerIn C Y).subtype = Y := by
  classical
  let N : Subgroup G := normalizerIn C Y
  let H : Subgroup G := normalizerIn E Y
  have hHN : H ≤ N := by
    intro x hx
    exact ⟨hEC hx.1, hx.2⟩
  have hHE : H ≤ E := inf_le_left
  have hYH : Y ≤ H := by
    intro y hy
    exact ⟨hYE hy, Subgroup.le_normalizer hy⟩
  obtain ⟨PH, hPHmap⟩ :=
    exists_sylow_map_eq_of_le_of_sylow_map_eq hYH hHE P hPmap
  have hHodd : Odd (Nat.card H) := by
    apply hEodd.of_dvd_nat
    exact Subgroup.card_dvd_of_le hHE
  have hdisj : Disjoint S H :=
    disjoint_of_isPGroup_two_of_odd_card S H hS2 hHodd
  have hNnormS : N ≤ Subgroup.normalizer (S : Set G) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).mp hSnormal
  have hHnormS : H ≤ Subgroup.normalizer (S : Set G) :=
    hHN.trans hNnormS
  have hsupN : S ⊔ H = N := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_mul_of_right_le_normalizer_left S H hHnormS]
    exact hfactor.symm
  have hpne2 : p ≠ 2 := by
    intro hp2
    subst p
    exact (by decide : ¬ Odd 2) hpodd
  obtain ⟨Q, hQmap⟩ :=
    sylow_sup_of_sylow_right_of_two_left hpne2 hS2 hHnormS hdisj PH hPHmap
  subst N
  rw [← hsupN]
  exact ⟨Q, hQmap⟩

private theorem exists_sylow_of_sylow_normalizerIn
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {C Y : Subgroup G} (hYC : Y ≤ C)
    (P : Sylow p (normalizerIn C Y))
    (hPmap : (P : Subgroup (normalizerIn C Y)).map
      (normalizerIn C Y).subtype = Y) :
    ∃ Q : Sylow p C,
      (Q : Subgroup C).map C.subtype = Y := by
  classical
  let N : Subgroup G := normalizerIn C Y
  have hNC : N ≤ C := inf_le_left
  let NC : Subgroup C := N.subgroupOf C
  let YC : Subgroup C := Y.subgroupOf C
  have hNCeq : NC = Subgroup.normalizer (YC : Set C) := by
    calc
      NC = (Subgroup.normalizer (Y : Set G)).subgroupOf C := by
        ext x
        simp [NC, N, normalizerIn]
      _ = Subgroup.normalizer (YC : Set C) := by
        simpa [YC] using Subgroup.subgroupOf_normalizer_eq hYC
  let e : NC ≃* N := Subgroup.subgroupOfEquivOfLe hNC
  let PNC : Sylow p NC :=
    Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective P
  have hPNCmap : (PNC : Subgroup NC).map NC.subtype = YC := by
    apply Subgroup.map_injective C.subtype_injective
    calc
      ((PNC : Subgroup NC).map NC.subtype).map C.subtype =
          (P : Subgroup N).map N.subtype := by
            rw [Subgroup.map_map, show (PNC : Subgroup NC) =
              (P : Subgroup N).map e.symm.toMonoidHom by
                exact Sylow.coe_mapSurjective
                  (f := e.symm.toMonoidHom) e.symm.surjective P,
              Subgroup.map_map]
            congr 1
      _ = Y := by simpa [N] using hPmap
      _ = YC.map C.subtype := by
        simpa [YC] using (Subgroup.map_subgroupOf_eq_of_le hYC).symm
  let eEq : NC ≃* Subgroup.normalizer (YC : Set C) :=
    MulEquiv.subgroupCongr hNCeq
  let PNorm : Sylow p (Subgroup.normalizer (YC : Set C)) :=
    Sylow.mapSurjective (f := eEq.toMonoidHom) eEq.surjective PNC
  have hPNormMap :
      (PNorm : Subgroup (Subgroup.normalizer (YC : Set C))).map
        (Subgroup.normalizer (YC : Set C)).subtype = YC := by
    rw [show (PNorm : Subgroup (Subgroup.normalizer (YC : Set C))) =
      (PNC : Subgroup NC).map eEq.toMonoidHom by
        exact Sylow.coe_mapSurjective
          (f := eEq.toMonoidHom) eEq.surjective PNC,
      Subgroup.map_map]
    have hfEq :
        (Subgroup.normalizer (YC : Set C)).subtype.comp eEq.toMonoidHom = NC.subtype := by
      ext x
      rfl
    rw [hfEq]
    exact hPNCmap
  obtain ⟨Q, hQ⟩ := exists_sylow_map_eq_of_normalizer_le_low PNorm (by
    rw [hPNormMap])
  refine ⟨Q, ?_⟩
  calc
    (Q : Subgroup C).map C.subtype =
        ((PNorm : Subgroup (Subgroup.normalizer (YC : Set C))).map
          (Subgroup.normalizer (YC : Set C)).subtype).map C.subtype := by
            rw [hQ, Subgroup.map_map]
    _ = YC.map C.subtype := by rw [hPNormMap]
    _ = Y := by
      simpa [YC] using Subgroup.map_subgroupOf_eq_of_le hYC

/-- A normal `2`-factor in `N_C(Y)` promotes a chosen odd Sylow subgroup
of `E` first to `N_C(Y)` and then to `C`. -/
public theorem exists_sylow_of_two_factor
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {C E S Y : Subgroup G}
    (hEC : E ≤ C) (hYE : Y ≤ E)
    (hEodd : Odd (Nat.card E))
    (hSN : S ≤ normalizerIn C Y)
    (hS2 : IsPGroup 2 S)
    (hSnormal : (S.subgroupOf (normalizerIn C Y)).Normal)
    (hfactor :
      (normalizerIn C Y : Set G) =
        (S : Set G) * (normalizerIn E Y : Set G))
    (P : Sylow p E)
    (hPmap : (P : Subgroup E).map E.subtype = Y) :
    ∃ Q : Sylow p C,
      (Q : Subgroup C).map C.subtype = Y := by
  obtain ⟨PN, hPNmap⟩ := exists_sylow_normalizerIn_of_two_factor
    hpodd hEC hYE hEodd hSN hS2 hSnormal hfactor P hPmap
  exact exists_sylow_of_sylow_normalizerIn
    (hYE.trans hEC) PN hPNmap

/-- Frattini's argument in an ambient subgroup: if `C ◁ M` and the
ambient image of a Sylow subgroup of `C` is `Y`, then
`C N_M(Y) = M`. -/
public theorem normal_sup_normalizerIn_eq_of_sylow
    {X : Type u} [Group X] [Finite X]
    {M C Y : Subgroup X} {p : ℕ} [Fact p.Prime]
    (hCM : C ≤ M)
    (hCnormal : (C.subgroupOf M).Normal)
    (P : Sylow p C)
    (hPmap : (P : Subgroup C).map C.subtype = Y) :
    C ⊔ normalizerIn M Y = M := by
  let N : Subgroup M := C.subgroupOf M
  let e : N ≃* C := Subgroup.subgroupOfEquivOfLe hCM
  let PN : Sylow p N :=
    Sylow.mapSurjective (f := e.symm.toMonoidHom)
      e.symm.surjective P
  have hYC : Y ≤ C := by
    rw [← hPmap]
    exact Subgroup.map_subtype_le (P : Subgroup C)
  have hYM : Y ≤ M := hYC.trans hCM
  have hPNmap :
      (PN : Subgroup N).map N.subtype = Y.subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    calc
      ((PN : Subgroup N).map N.subtype).map M.subtype =
          (PN : Subgroup N).map (M.subtype.comp N.subtype) := by
        rw [Subgroup.map_map]
      _ = ((P : Subgroup C).map e.symm.toMonoidHom).map
          (M.subtype.comp N.subtype) := by
        rw [show (PN : Subgroup N) =
            (P : Subgroup C).map e.symm.toMonoidHom by
          simpa [PN] using
            (Sylow.coe_mapSurjective
              (f := e.symm.toMonoidHom) e.symm.surjective P)]
      _ = (P : Subgroup C).map
          ((M.subtype.comp N.subtype).comp e.symm.toMonoidHom) := by
        rw [Subgroup.map_map]
      _ = (P : Subgroup C).map C.subtype := by
        congr 1
      _ = Y := hPmap
      _ = (Y.subgroupOf M).map M.subtype := by
        symm
        simpa [Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hYM]
  letI : N.Normal := by simpa [N] using hCnormal
  have hFrattini :
      Subgroup.normalizer ((Y.subgroupOf M : Subgroup M) : Set M) ⊔
        N = ⊤ := by
    simpa [hPNmap] using
      (Sylow.normalizer_sup_eq_top (G := M) (N := N) PN)
  have hnormalizerLocal :
      (normalizerIn M Y).subgroupOf M =
        Subgroup.normalizer ((Y.subgroupOf M : Subgroup M) : Set M) := by
    calc
      (normalizerIn M Y).subgroupOf M =
          (Subgroup.normalizer (Y : Set X)).subgroupOf M := by
        ext m
        simp [normalizerIn]
      _ = Subgroup.normalizer
          ((Y.subgroupOf M : Subgroup M) : Set M) :=
        Subgroup.subgroupOf_normalizer_eq hYM
  have hlocalSup :
      C.subgroupOf M ⊔ (normalizerIn M Y).subgroupOf M = ⊤ := by
    rw [sup_comm, hnormalizerLocal]
    simpa [N] using hFrattini
  have hsubgroupOfSup :
      (C ⊔ normalizerIn M Y).subgroupOf M = ⊤ := by
    have hNM : normalizerIn M Y ≤ M := inf_le_left
    calc
      (C ⊔ normalizerIn M Y).subgroupOf M =
          C.subgroupOf M ⊔ (normalizerIn M Y).subgroupOf M :=
        Subgroup.subgroupOf_sup hCM hNM
      _ = ⊤ := hlocalSup
  apply le_antisymm
  · exact sup_le hCM inf_le_left
  · intro x hxM
    let xM : M := ⟨x, hxM⟩
    have hxTop : xM ∈ ((C ⊔ normalizerIn M Y).subgroupOf M) := by
      rw [hsubgroupOfSup]
      trivial
    exact hxTop

end CFSG.BenderSuzuki
