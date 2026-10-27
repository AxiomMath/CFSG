module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CAssembly
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUAJPerm
import CFSG.LocalAnalysis.StandardType.GGHdRo7SULStab

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem su_lin_of_leaves (hN : SUNormalizerLeaf) (hU : SUNormalizerLeaf → ∀ (p : ℕ) [Fact p.Prime]
    (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (b : Module.Basis (Fin m) (ZMod p) V) (H
    A : Subgroup (V ≃ₗ[ZMod p] V)), SULinData p m V b H A → (∀ r ∈ H, GGLinRefl r → ggLinMove r ≤
    SUAug p b) → SUClassReady p m H) (hV : SUNormalizerLeaf → ∀ (p
    : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (b : Module.Basis
    (Fin m) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)), SULinData p m V b H A → (∃ r ∈ H,
    GGLinRefl r ∧ ¬ ggLinMove r ≤ SUAug p b) → SUClassReady p m H)
    (hC : SUClassLargeLeaf) (hS : SULinSmallLeaf) (hKG : GGReflClassLargeInput') {p : ℕ}
    [Fact p.Prime] {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {b : Module.Basis (Fin m) (ZMod p) V} {H A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hD : SULinData p m V b H A) : ZS.LinWeyl p H := by
  have hm7 := hD.hm
  have h3 := hD.h3
  by_cases hsmall : m = 7 ∨ m = 8
  · exact hS p m V b H A hD hsmall
  · have hm10 : 10 ≤ m := by omega
    have hR : SUClassReady p m H := by
      by_cases hspan : ∃ r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ SUAug p b
      · exact hV hN p m V b H A hD hspan
      · exact hU hN p m V b H A hD fun r hr hrf => by
          by_contra hn
          exact hspan ⟨r, hr, hrf, hn⟩
    obtain ⟨d, W, _, _, R, hd, hfin, hirr, hgen, hcard, hlift⟩ := hR
    exact hlift (hC hKG p hD.hp d (by omega) W hfin R hirr hgen hcard)

theorem su_core {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hX : GGResXDichotomyInput) (hNoTV : NoTVLeaf) (hXD : XDatumGraphLeaf) (hGr : SUGraphLeaf)
    (hLin : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (b : Module.Basis (Fin m) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
      SULinData p m V b H A → ZS.LinWeyl p H)
    (hp3 : p = 3)
    (hAJ : (∃ a ∈ ggAutomizer J Bs, ∃ b ∈ ggAutomizer J Bs, a * b ≠ b * a) ∧
      ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs)
    {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin m) (ZMod p) V) (hm : 7 ≤ m) (h3 : ¬ 3 ∣ m)
    (hPH : ∀ a, SUPerm p b a →
      a ∈ (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι))
    (hstab : ∀ a ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι), a (SUOnes p b) = SUOnes p b →
      ∀ s, SUPerm p b s → SUPerm p b (a * s * a⁻¹)) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hDL : GGResXDatum p Bs L := by
    rcases (hX G p B Bs x L D J y K hH).1 with hD | h7
    · exact hD
    · exfalso
      obtain ⟨-, -, -, -, -, -, h7p, -⟩ := h7
      omega
  have hDK : GGResXDatum p Bs K := by
    rcases (hX G p B Bs x L D J y K hH).2 with hD | h7
    · exact hD
    · exfalso
      obtain ⟨-, -, -, -, -, -, h7p, -⟩ := h7
      omega
  obtain ⟨SL, hSL, hQL, hcL⟩ := hXD G p Bs L hDL V ι
  obtain ⟨SK, hSK, hQK, hcK⟩ := hXD G p Bs K hDK V ι
  obtain ⟨⟨a, haJ, c, hcJ, hac⟩, hJle⟩ := hAJ
  obtain ⟨S, hS, hQ, hconn⟩ := hGr p V _ _ ((ggAutomizer J Bs).map (ggLin (p := p) ι)) SL SK
    hSL hQL hcL hSK hQK hcK (Subgroup.map_mono (hJle.trans inf_le_left))
    (Subgroup.map_mono (hJle.trans inf_le_right))
    ⟨ggLin (p := p) ι a, Subgroup.mem_map_of_mem _ haJ, ggLin (p := p) ι c,
      Subgroup.mem_map_of_mem _ hcJ, fun h => hac (ggLin_injective (p := p) ι (by
        simpa [← map_mul] using h))⟩
  rw [← Subgroup.map_sup] at hS hQ
  have hDat : SULinData p m V b ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι))
      ((ggAutomizer ⊤ Bs).map (ggLin (p := p) ι)) :=
    { hp := hp3
      hm := hm
      h3 := h3
      hPH := hPH
      hHA := Subgroup.map_mono (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top))
      hStab := hstab
      hNoT := hNoTV G p Bs hH.2.2.2.1 V ι
      hgen := ⟨S, hS, hQ, hconn⟩ }
  exact ggRC_weylReflGroup_of_linWeyl ι _ (hLin m V b _ _ hDat)


private theorem su_commonJ_of_data
    {G : Type} [Group G] [Finite G]
    {Bs J : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    (X : Subgroup (MulAut ↥Bs))
    (ML : CoxeterMatrix Λ) (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (hsurv : 2 ≤ Nat.card {i : Λ // i ∉ S})
    (hdel : GGDeletedConnectedS ML S)
    (fL : ML.Group ≃* ↥X)
    (hfL : ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i))
    (hgenJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {i : Λ // i ∉ S} => φ (Sum.inl j))) :
    ∃ a ∈ ggAutomizer J Bs, ∃ b ∈ ggAutomizer J Bs, a * b ≠ b * a := by
  classical
  have hedge : ∃ u v : {i : Λ // i ∉ S}, u ≠ v ∧ ML.M u v ≠ 2 := by
    by_contra h
    push Not at h
    have hnoedge : ∀ u v : {i : Λ // i ∉ S}, u ≠ v → ML.M u v = 2 := by
      intro u v huv
      by_contra hm
      exact hm (h u v huv)
    have hcard : 1 < (Finset.univ : Finset {i : Λ // i ∉ S}).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      omega
    obtain ⟨u, -, v, -, huv⟩ := Finset.one_lt_card.mp hcard
    have hEq : u = v := by
      induction hdel u v with
      | refl => rfl
      | tail _ hstep _ => exact (hstep.2 (hnoedge _ _ hstep.1)).elim
    exact huv hEq
  obtain ⟨u, v, huv, huvM⟩ := hedge
  have hJnab : ∃ a ∈ ggAutomizer J Bs, ∃ b ∈ ggAutomizer J Bs, a * b ≠ b * a := by
    refine ⟨φ (Sum.inl u.1), ?_, φ (Sum.inl v.1), ?_, ?_⟩
    · rw [hgenJ]
      exact Subgroup.subset_closure ⟨u, rfl⟩
    · rw [hgenJ]
      exact Subgroup.subset_closure ⟨v, rfl⟩
    · intro hcomm
      have hcomm' : (fL (ML.simple u) : MulAut ↥Bs) * (fL (ML.simple v) : MulAut ↥Bs) =
          (fL (ML.simple v) : MulAut ↥Bs) * (fL (ML.simple u) : MulAut ↥Bs) := by
        rw [hfL u, hfL v]
        exact hcomm
      have hsimple_comm : ML.simple u * ML.simple v = ML.simple v * ML.simple u := by
        apply fL.injective
        rw [map_mul, map_mul]
        exact Subtype.ext hcomm'
      have hsq : (ML.simple u * ML.simple v) ^ 2 = 1 := by
        have hc : Commute (ML.simple u) (ML.simple v) := hsimple_comm
        rw [hc.mul_pow]
        rw [show ML.simple u ^ 2 = 1 from by
              rw [pow_two, ← CoxeterMatrix.toCoxeterSystem_simple]
              exact CoxeterSystem.simple_mul_simple_self ML.toCoxeterSystem u,
            show ML.simple v ^ 2 = 1 from by
              rw [pow_two, ← CoxeterMatrix.toCoxeterSystem_simple]
              exact CoxeterSystem.simple_mul_simple_self ML.toCoxeterSystem v]
        simp
      have horder : orderOf (ML.simple u * ML.simple v) = ML.M u v := by
        rw [← CoxeterMatrix.toCoxeterSystem_simple]
        exact CoxeterSystem.orderOf_simple_mul_simple ML.toCoxeterSystem u v
      have hdvd : ML.M u v ∣ 2 := by
        rw [← horder]
        exact orderOf_dvd_iff_pow_eq_one.mpr hsq
      have huv' : (u : Λ) ≠ (v : Λ) := fun h => huv (Subtype.ext h)
      have h1 : ML.M u v ≠ 1 := ML.off_diagonal u v huv'
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact (h1 h).elim
      · exact huvM h
  exact hJnab

private theorem su_commonJ_of_exact2_left
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin m) (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (hpermL : ∀ a, a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ↔ SUPerm p b a)
    (hm7 : 7 ≤ m)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    (∃ a ∈ ggAutomizer J Bs, ∃ b ∈ ggAutomizer J Bs, a * b ≠ b * a) ∧
      ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs := by
  classical
  obtain ⟨Λ, hΛ, hΛd, S, Λa, hΛa, hΛad, ML, CL, MK, CK, V₀, hV₀, hV₀d, ι₀, φ, hvec, α, hP⟩ := hD
  let : Fintype Λ := hΛ
  let : DecidableEq Λ := hΛd
  let : Fintype Λa := hΛa
  let : DecidableEq Λa := hΛad
  rcases hP with ⟨hScard, -, -, -, -, -, -, -, -, hrefl, -, -, -, ⟨fL, hfL⟩, -,
    hgenL, hgenK, hdel, hgenJ⟩
  have hml : m ≤ Nat.card Λ + 1 :=
    hdRo7SUAJPerm_model_card_le (X := L) (M := ML) b ι hpermL
      (φ := fun i => φ (Sum.inl i)) fL (hf := fun i => hfL i) hgenL
      (hrefl := fun i => hrefl (Sum.inl i)) hm7
  have hcardSurv : Nat.card {i : Λ // i ∉ S} = Nat.card Λ - S.card := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (p := fun i : Λ => i ∈ S), Fintype.card_coe]
  have hSle : S.card ≤ Nat.card Λ := by
    rw [Nat.card_eq_fintype_card]
    exact S.card_le_univ
  have hsurv : 2 ≤ Nat.card {i : Λ // i ∉ S} := by
    omega
  have hJnab := su_commonJ_of_data (X := ggAutomizer L Bs) ML φ hsurv hdel fL
    (fun i => hfL i) hgenJ
  have hJle : ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs := by
    rw [hgenJ]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨j, rfl⟩
    constructor
    · rw [hgenL]
      exact Subgroup.subset_closure ⟨j.1, rfl⟩
    · rw [hgenK]
      exact Subgroup.subset_closure (Set.mem_union_left _ ⟨j, rfl⟩)
  exact ⟨hJnab, hJle⟩

private theorem su_commonJ_of_exact2_right
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin m) (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (hpermL : ∀ a, a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ↔ SUPerm p b a)
    (hm7 : 7 ≤ m)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    (∃ a ∈ ggAutomizer J Bs, ∃ b ∈ ggAutomizer J Bs, a * b ≠ b * a) ∧
      ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs := by
  classical
  obtain ⟨Λ, hΛ, hΛd, S, Λa, hΛa, hΛad, ML, CL, MK, CK, V₀, hV₀, hV₀d, ι₀, φ, hvec, α, hP⟩ := hD
  let : Fintype Λ := hΛ
  let : DecidableEq Λ := hΛd
  let : Fintype Λa := hΛa
  let : DecidableEq Λa := hΛad
  rcases hP with ⟨-, -, hΛa3, -, -, -, -, -, -, hrefl, -, -, -, ⟨fL, hfL⟩, ⟨fK, hfK⟩,
    hgenK, hgenL, hdel, hgenJ⟩
  have hgenL' : ggAutomizer L Bs = Subgroup.closure
      (Set.range fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id)) := by
    rw [hgenL]
    congr 1
    ext x
    constructor
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
    · rintro ⟨o, rfl⟩
      cases o with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
  have hml : m ≤ Nat.card ({i : Λ // i ∉ S} ⊕ Λa) + 1 :=
    hdRo7SUAJPerm_model_card_le (X := L) (M := MK) b ι hpermL
      (φ := fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id))
      fK (hf := fun o => hfK o) hgenL'
      (hrefl := fun o => hrefl (o.map Subtype.val id)) hm7
  have hcardPair : Nat.card ({i : Λ // i ∉ S} ⊕ Λa) =
      Nat.card {i : Λ // i ∉ S} + Nat.card Λa := Nat.card_sum
  have hsurv : 2 ≤ Nat.card {i : Λ // i ∉ S} := by
    omega
  have hJnab := su_commonJ_of_data (X := ggAutomizer K Bs) ML φ hsurv hdel fL
    (fun i => hfL i) hgenJ
  have hJle : ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs := by
    rw [hgenJ]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨j, rfl⟩
    constructor
    · rw [hgenL]
      exact Subgroup.subset_closure (Set.mem_union_left _ ⟨j, rfl⟩)
    · rw [hgenK]
      exact Subgroup.subset_closure ⟨j.1, rfl⟩
  exact ⟨hJnab, hJle⟩

theorem su_core_of_exact2 {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p = 3)
    (hD2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hNoTV : NoTVLeaf) (hXD : XDatumGraphLeaf) (hGr : SUGraphLeaf)
    (hLin : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (b : Module.Basis (Fin m) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
      SULinData p m V b H A → ZS.LinWeyl p H)
    {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin m) (ZMod p) V) (hx : x ∈ Bs) (hm : 7 ≤ m) (h3 : ¬ 3 ∣ m)
    (hxb : ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) = SUOnes p b)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hAL : ∀ a, a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ↔ SUPerm p b a) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hDL : GGResXDatum p Bs L := by
    rcases hD2 with hD | hD
    · exact ggResXDatum_left_of_exact2 hD
    · exact ggResXDatum_right_of_exact2 hD
  have hDK : GGResXDatum p Bs K := by
    rcases hD2 with hD | hD
    · exact ggResXDatum_right_of_exact2 hD
    · exact ggResXDatum_left_of_exact2 hD
  obtain ⟨SL, hSL, hQL, hcL⟩ := hXD G p Bs L hDL V ι
  obtain ⟨SK, hSK, hQK, hcK⟩ := hXD G p Bs K hDK V ι
  have hJdata :
      (∃ a ∈ ggAutomizer J Bs, ∃ b ∈ ggAutomizer J Bs, a * b ≠ b * a) ∧
        ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs := by
    rcases hD2 with hD | hD
    · exact su_commonJ_of_exact2_left b ι hAL hm hD
    · exact su_commonJ_of_exact2_right b ι hAL hm hD
  obtain ⟨⟨a, haJ, c, hcJ, hac⟩, hJle⟩ := hJdata
  obtain ⟨S, hS, hQ, hconn⟩ := hGr p V _ _ ((ggAutomizer J Bs).map (ggLin (p := p) ι)) SL SK
    hSL hQL hcL hSK hQK hcK (Subgroup.map_mono (hJle.trans inf_le_left))
    (Subgroup.map_mono (hJle.trans inf_le_right))
    ⟨ggLin (p := p) ι a, Subgroup.mem_map_of_mem _ haJ, ggLin (p := p) ι c,
      Subgroup.mem_map_of_mem _ hcJ, fun h => hac (ggLin_injective (p := p) ι (by
        simpa [← map_mul] using h))⟩
  rw [← Subgroup.map_sup] at hS hQ
  have hstab := hdRo7SULStabAux_main hH hnc ι b hx hxb hAL
  have hPH : ∀ a, SUPerm p b a →
      a ∈ (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) :=
    fun a ha => Subgroup.map_mono le_sup_left ((hAL a).mpr ha)
  have hDat : SULinData p m V b ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι))
      ((ggAutomizer ⊤ Bs).map (ggLin (p := p) ι)) :=
    { hp := hp3
      hm := hm
      h3 := h3
      hPH := hPH
      hHA := Subgroup.map_mono (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top))
      hStab := hstab
      hNoT := hNoTV G p Bs hH.2.2.2.1 V ι
      hgen := ⟨S, hS, hQ, hconn⟩ }
  exact ggRC_weylReflGroup_of_linWeyl ι _ (hLin m V b _ _ hDat)

theorem ggResSUCorank2Input_of_leaves (hX : GGResXDichotomyInput) (hJ : GGTBJInputR)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hKG : GGReflClassLargeInput')
    (hN : SUNormalizerLeaf) (hU : SUNormalizerLeaf → ∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (V : Type)
        [AddCommGroup V] [Module (ZMod p) V] (b : Module.Basis (Fin m) (ZMod p) V) (H A : Subgroup
        (V ≃ₗ[ZMod p] V)), SULinData p m V b H A → (∀ r ∈ H, GGLinRefl r → ggLinMove r ≤ SUAug p b)
        → SUClassReady p m H) (hV : SUNormalizerLeaf → ∀ (p : ℕ) [Fact p.Prime]
        (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (b : Module.Basis (Fin m) (ZMod p)
        V) (H A : Subgroup (V ≃ₗ[ZMod p] V)), SULinData p m V b H A → (∃ r ∈ H, GGLinRefl r ∧ ¬
        ggLinMove r ≤ SUAug p b) → SUClassReady p m H) (hC : SUClassLargeLeaf)
    (hS : SULinSmallLeaf) (hGr : SUGraphLeaf) (hNoTV : NoTVLeaf) (hXD : XDatumGraphLeaf)
    (hLM : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup
        G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime], GGResRowAt
        ggRowSUCorank2 p J L → SUModelAt p Bs L x) (hKM : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x :
        G) (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact
        p.Prime], GGResRowAt ggRowSUCorank2 p J K → SUModelAt p Bs K y) (hKS : SUKStabLeaf)
    (hAJ : SUAJLeaf) : GGResSUCorank2Input := by
  have hLS := su_lstab_holds
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hrow
  have hp3 : p = 3 := by
    rcases hrow with ⟨-, -, -, -, -, -, h3, -⟩ | ⟨-, -, -, -, -, -, h3, -⟩ <;> exact h3
  have hLin : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (b : Module.Basis (Fin m) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
      SULinData p m V b H A → ZS.LinWeyl p H :=
    fun m V _ _ b H A hD => su_lin_of_leaves hN hU hV hC hS hKG hD
  have hAJ' := hAJ hX hJ hRig hLB G p B Bs x L D J y K hH
    (fun hr => hLM G p B Bs x L D J y K hH hr) (fun hr => hKM G p B Bs x L D J y K hH hr) hrow
  rcases hrow with hrow | hrow
  · obtain ⟨m, V, _, _, ι, b, hx, -, hm, h3, hxb, hAL⟩ := hLM G p B Bs x L D J y K hH hrow
    exact su_core hH hX hNoTV hXD hGr hLin hp3 hAJ' ι b hm h3
      (fun a ha => Subgroup.map_mono le_sup_left ((hAL a).mpr ha))
      (hLS G p B Bs x L D J y K hH hrow m V ι b hx hp3 hm h3 hxb hAL)
  · obtain ⟨m, V, _, _, ι, b, hy, -, hm, h3, hyb, hAK⟩ := hKM G p B Bs x L D J y K hH hrow
    exact su_core hH hX hNoTV hXD hGr hLin hp3 hAJ' ι b hm h3
      (fun a ha => Subgroup.map_mono le_sup_right ((hAK a).mpr ha))
      (hKS G p B Bs x L D J y K hH hrow m V ι b hy hp3 hm h3 hyb hAK)

end CFSG.StandardType.HdRo7SU
