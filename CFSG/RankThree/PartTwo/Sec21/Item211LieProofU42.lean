module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofSylow
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofU4
import CFSG.RankThree.PartTwo.Sec4.Item462ProofCent
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLie
import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)

open CFSG.Assembly (IsElemAbelian)

open Item211Res2Proof
open scoped commutatorElement

@[expose] def KS211U42FourGroup : Prop :=
  ∀ D T : Subgroup (projSU 4 2 1), IsElemAbelian 3 D → Nat.card D = 9 → IsElemAbelian 2 T →
    Nat.card T = 4 → D ≤ Subgroup.normalizer (T : Set (projSU 4 2 1)) →
    D ≤ Subgroup.centralizer (T : Set (projSU 4 2 1))


@[expose] def KS211U42CharThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSU 4 2 1) →
    ∀ D : Subgroup (MulAut X), D ≤ (MulAut.conj : X →* MulAut X).range →
      IsElemAbelian 3 D → Nat.card D = 9 →
      ∀ τ : MulAut X, (∃ k : ℕ, τ ^ (2 ^ k) = 1) →
        τ ∈ Subgroup.centralizer (D : Set (MulAut X)) →
        τ ∈ Subgroup.centralizer ((inSubgroup (CFSG.pCore 3)
          ((MulAut.conj : X →* MulAut X).range ⊓ Subgroup.centralizer (D : Set (MulAut X))) :
            Subgroup (MulAut X)) : Set (MulAut X)) →
        τ = 1

namespace Item211LieProof

variable {G : Type} [Group G] [Finite G] {A E U L : Subgroup G} {c : G}

theorem barImage_E_le_range_conj_of_projSU (h : PairFacts A E U c L) (hG : TheoremFourHyp G)
    {m : ℕ} (hm : 1 ≤ m) (e₀ : lBar L ≃* projSU 4 2 m) :
    barImage L E ≤ (MulAut.conj : lBar L →* MulAut (lBar L)).range := by
  intro d hd
  obtain ⟨e, heN, heE, rfl⟩ := mem_barImage_iff.mp hd
  have hout := Item223PrintProof.not_inducesOuterTheta_of_mem_thetaComponentsAt hG h.c3 h.c1
    h.Lc hm e₀ (x := e) (h.E_comm e heE c h.cE) (h.Ee.2 e heE)
  by_contra hd'
  exact hout ⟨heN, hd'⟩

theorem le_centralizer_of_comap_conj {X : Type*} [Group X] {D T : Subgroup (MulAut X)}
    (hD : D ≤ (MulAut.conj : X →* MulAut X).range) (hT : T ≤ (MulAut.conj : X →* MulAut X).range)
    (hC : D.comap (MulAut.conj : X →* MulAut X) ≤
      Subgroup.centralizer ((T.comap (MulAut.conj : X →* MulAut X) : Subgroup X) : Set X)) :
    D ≤ Subgroup.centralizer (T : Set (MulAut X)) := by
  intro d hd
  obtain ⟨x, rfl⟩ := hD hd
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  obtain ⟨y, rfl⟩ := hT ht
  have h1 := Subgroup.mem_centralizer_iff.mp (hC (show x ∈ D.comap MulAut.conj from hd)) y
    (show y ∈ T.comap MulAut.conj from ht)
  rw [← map_mul, ← map_mul, h1]

theorem comap_conj_le_normalizer {X : Type*} [Group X] {D T : Subgroup (MulAut X)}
    (hT : T ≤ (MulAut.conj : X →* MulAut X).range)
    (hDT : D ≤ Subgroup.normalizer (T : Set (MulAut X))) :
    D.comap (MulAut.conj : X →* MulAut X) ≤
      Subgroup.normalizer ((T.comap (MulAut.conj : X →* MulAut X) : Subgroup X) : Set X) := by
  rw [← Subgroup.comap_normalizer_eq_of_le_range hT]
  exact Subgroup.comap_mono hDT

theorem map_le_normalizer_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {D T : Subgroup X} (hDT : D ≤ Subgroup.normalizer (T : Set X)) :
    D.map e.toMonoidHom ≤ Subgroup.normalizer ((T.map e.toMonoidHom : Subgroup Y) : Set Y) := by
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hDT

theorem le_centralizer_of_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {D T : Subgroup X}
    (hC : D.map e.toMonoidHom ≤ Subgroup.centralizer ((T.map e.toMonoidHom : Subgroup Y) : Set Y)) :
    D ≤ Subgroup.centralizer (T : Set X) := by
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h1 := Subgroup.mem_centralizer_iff.mp (hC ⟨d, hd, rfl⟩) (e t) ⟨t, ht, rfl⟩
  apply e.injective
  rw [map_mul, map_mul]
  exact h1

theorem le_centralizer_of_ks211U42 (hK : KS211U42FourGroup) {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X) (e₀ : X ≃* projSU 4 2 1) {D T : Subgroup (MulAut X)}
    (hD : D ≤ (MulAut.conj : X →* MulAut X).range) (hT : T ≤ (MulAut.conj : X →* MulAut X).range)
    (hDe : IsElemAbelian 3 D) (hD9 : Nat.card D = 9) (hTe : IsElemAbelian 2 T)
    (hT4 : Nat.card T = 4) (hDT : D ≤ Subgroup.normalizer (T : Set (MulAut X))) :
    D ≤ Subgroup.centralizer (T : Set (MulAut X)) := by
  have : IsSimpleGroup (projSU 4 2 1) := isSimpleGroup_projSU le_rfl le_rfl
  have hZ : Subgroup.center X = ⊥ := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq e₀
  have hinj := conj_injective_of_center_eq_bot hZ
  set D₀ := D.comap (MulAut.conj : X →* MulAut X) with hD₀
  set T₀ := T.comap (MulAut.conj : X →* MulAut X) with hT₀
  refine le_centralizer_of_comap_conj hD hT (le_centralizer_of_map e₀ ?_)
  refine hK _ _ (Sec4.Item462Proof.isElemAbelian_map' _ (isElemAbelian_comap_of_injective hinj hDe))
    ?_ (Sec4.Item462Proof.isElemAbelian_map' _ (isElemAbelian_comap_of_injective hinj hTe)) ?_
    (map_le_normalizer_map e₀ (comap_conj_le_normalizer hT hDT))
  · rw [Subgroup.card_map_of_injective e₀.injective, card_comap_conj hZ hD, hD9]
  · rw [Subgroup.card_map_of_injective e₀.injective, card_comap_conj hZ hT, hT4]


theorem exists_lift_fixed (h : PairFacts A E U c L) {z : lBar L}
    (hz : ∀ e ∈ E, ∀ he : e ∈ Subgroup.normalizer (L : Set G), barAct L ⟨e, he⟩ z = z) :
    ∃ w ∈ L, w ∈ Subgroup.centralizer (E : Set G) ∧ ∀ hw : w ∈ L,
      ((⟨w, hw⟩ : L) : lBar L) = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
  set θ := inSubgroup (aschbacherSolvableCore 3) L with hθ
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using h.Ee.2 _ g.2)⟩
  have hθ3 : ¬ 3 ∣ Nat.card θ := by
    rw [hθ, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore L
  have hNθ := normalizer_le_normalizer_theta L
  obtain ⟨w, hwL, hwl, hwE⟩ := exists_fixed_conj_of_coprime hE3 h.EL (Subgroup.map_subtype_le _)
    (fun x hx => hNθ (Subgroup.le_normalizer hx)) (h.EL.trans hNθ) hθ3 l.2 fun g hg => by
      have h1 := hz g hg (h.EL hg)
      rw [barAct_mk, eq_comm, QuotientGroup.eq] at h1
      exact ⟨_, h1, rfl⟩
  refine ⟨w, hwL, ?_, fun hw => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h1 := hwE e he
    calc e * w = e * w * e⁻¹ * e := by group
      _ = w * e := by rw [h1]
  · rw [QuotientGroup.eq]
    have h1 : (l : G)⁻¹ * w ∈ θ := by
      have h2 := (Subgroup.mem_normalizer_iff.mp (hNθ (Subgroup.le_normalizer
        (L.inv_mem l.2))) _).mp hwl
      rw [inv_inv] at h2
      have e : (l : G)⁻¹ * w = (l : G)⁻¹ * (w * (l : G)⁻¹) * (l : G) := by group
      rw [e]
      exact h2
    obtain ⟨t, ht, hte⟩ := h1
    have : t = l⁻¹ * ⟨w, hw⟩ := Subtype.ext (by simpa using hte)
    rw [this] at ht
    have h3 := (aschbacherSolvableCore 3 L).inv_mem ht
    rwa [mul_inv_rev, inv_inv] at h3

theorem barImage_U_comm_O3 (hS : A ∈ partTwoS G) (hst : PartTwoStanding G)
    (hEmem : E ∈ partTwoE G) (h : PairFacts A E U c L) [IsSimpleGroup (lBar L)]
    (hP : U ∈ fourGroupsPlus E) :
    ∀ a ∈ barImage L U, ∀ r ∈ (inSubgroup (CFSG.pCore 3)
      ((MulAut.conj : lBar L →* MulAut (lBar L)).range ⊓
        Subgroup.centralizer (barImage L E : Set (MulAut (lBar L)))) :
          Subgroup (MulAut (lBar L))), a * r = r * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center (lBar L) = ⊥ :=
    Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup h.q (MulEquiv.refl _)
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set Inn := (MulAut.conj : lBar L →* MulAut (lBar L)).range with hInn
  set C₀ := Inn ⊓ Subgroup.centralizer (barImage L E : Set (MulAut (lBar L))) with hC₀
  set R := inSubgroup (CFSG.pCore 3) C₀ with hR
  have hR3 : IsPGroup 3 R := (CFSG.pCore_isPGroup).map C₀.subtype
  have hRC : R ≤ C₀ := Subgroup.map_subtype_le _
  have hUC : U ≤ Subgroup.centralizer (E : Set G) := by
    have hEC := (mem_fourGroupsPlus_iff.mp hP).2
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp (hEC he) u hu).symm
  have hUEα := barImage_U_comm_E_of_plus (L := L) hP
  have hUR : ∀ u ∈ U, ∀ hu : u ∈ N, barAct L ⟨u, hu⟩ ∈ Subgroup.normalizer (R : Set _) := by
    intro u hu huN
    refine CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 3 C₀
      (Subgroup.mem_normalizer_fintype fun x hx => Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · obtain ⟨y, hy⟩ := (Subgroup.mem_inf.mp hx).1
      rw [← hy, KFacts.mul_mulAutConj_mul_inv]
      exact ⟨_, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 d hd
      have h2 := hUEα _ (mem_barImage_iff.mpr ⟨u, huN, hu, rfl⟩) d hd
      set σ := barAct L ⟨u, huN⟩ with hσ
      have h3 : d = σ * d * σ⁻¹ := by rw [h2]; group
      calc d * (σ * x * σ⁻¹) = (σ * d * σ⁻¹) * (σ * x * σ⁻¹) := by rw [← h3]
        _ = σ * (d * x) * σ⁻¹ := by group
        _ = σ * (x * d) * σ⁻¹ := by rw [h1]
        _ = (σ * x * σ⁻¹) * (σ * d * σ⁻¹) := by group
        _ = (σ * x * σ⁻¹) * d := by rw [← h3]
  set P : Subgroup G := (L ⊓ Subgroup.centralizer (E : Set G)) ⊓
    (R.comap (barAct L)).map N.subtype with hPdef
  have hPL : P ≤ L := inf_le_left.trans inf_le_left
  have hPE : P ≤ Subgroup.centralizer (E : Set G) := inf_le_left.trans inf_le_right
  have hPN : P ≤ N := fun y hy => Subgroup.le_normalizer (hPL hy)
  have hmemP : ∀ y : G, ∀ hy : y ∈ N, y ∈ P ↔ y ∈ L ∧ y ∈ Subgroup.centralizer (E : Set G) ∧
      barAct L ⟨y, hy⟩ ∈ R := by
    intro y hy
    constructor
    · rintro ⟨⟨hyL, hyE⟩, ⟨n, hn, rfl⟩⟩
      exact ⟨hyL, hyE, hn⟩
    · rintro ⟨hyL, hyE, hyR⟩
      exact ⟨⟨hyL, hyE⟩, ⟨⟨y, hy⟩, hyR, rfl⟩⟩
  have himg : barImage L P = R := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨⟨y, hyN⟩, hyP, rfl⟩
      exact ((hmemP y hyN).mp (Subgroup.mem_subgroupOf.mp hyP)).2.2
    · intro r hr
      obtain ⟨z, hz⟩ := (Subgroup.mem_inf.mp (hRC hr)).1
      have hfix : ∀ e ∈ E, ∀ he : e ∈ N, barAct L ⟨e, he⟩ z = z := by
        intro e he heN
        have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hRC hr)).2 _
          (mem_barImage_iff.mpr ⟨e, heN, he, rfl⟩)
        rw [← hz] at h1
        have h2 : MulAut.conj (barAct L ⟨e, heN⟩ z) = MulAut.conj z := by
          rw [← KFacts.mul_mulAutConj_mul_inv, h1]
          group
        exact conj_injective_of_center_eq_bot hZ h2
      obtain ⟨w, hwL, hwE, hwz⟩ := exists_lift_fixed h hfix
      have hwβ : barAct L ⟨w, Subgroup.le_normalizer hwL⟩ = r := by
        rw [barAct_of_mem hwL, hwz hwL, hz]
      refine mem_barImage_iff.mpr ⟨w, Subgroup.le_normalizer hwL, ?_, hwβ⟩
      exact (hmemP w _).mpr ⟨hwL, hwE, hwβ ▸ hr⟩
  set θ := inSubgroup (aschbacherSolvableCore 3) L with hθ
  set Oθ := inSubgroup (pPrimeCore 2) θ with hOθ
  set K := P ⊓ θ with hK
  set O := P ⊓ Oθ with hO
  have hNθ := normalizer_le_normalizer_theta L
  have hNO : N ≤ Subgroup.normalizer (Oθ : Set G) :=
    hNθ.trans (Commute33Steps.normalizer_le_normalizer_oddCore θ)
  have hOθθ : Oθ ≤ θ := Subgroup.map_subtype_le _
  have hθ3 : ¬ 3 ∣ Nat.card θ := by
    rw [hθ, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore L
  have hinf : ∀ {H₁ H₂ : Subgroup G} {g : G}, g ∈ Subgroup.normalizer (H₁ : Set G) →
      g ∈ Subgroup.normalizer (H₂ : Set G) → g ∈ Subgroup.normalizer ((H₁ ⊓ H₂ : Subgroup G) :
        Set G) := fun h₁ h₂ => Subgroup.mem_normalizer_fintype fun x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp h₁ x).mp hx.1, (Subgroup.mem_normalizer_iff.mp h₂ x).mp hx.2⟩
  have hkerP : P ⊓ Sec4.thetaQuotCentralizer L = K := by
    ext y
    constructor
    · rintro ⟨hyP, hyK⟩
      exact ⟨hyP, mem_theta_of_mem_thetaQuotCentralizer hZ (hPL hyP) hyK⟩
    · rintro ⟨hyP, hyθ⟩
      exact ⟨hyP, theta_le_thetaQuotCentralizer L hyθ⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR3
  have hcardP : Nat.card P = Nat.card K * 3 ^ m := by
    have h1 := card_barImage_mul hPN
    rw [himg, hkerP, hm] at h1
    rw [← h1, mul_comm]
  have hUP : U ≤ Subgroup.normalizer (P : Set G) := by
    intro u hu
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have huN := h.UN hu
    have hyN := hPN hy
    obtain ⟨hyL, hyE, hyR⟩ := (hmemP y hyN).mp hy
    have hzN : u * y * u⁻¹ ∈ N := N.mul_mem (N.mul_mem huN hyN) (N.inv_mem huN)
    refine (hmemP _ hzN).mpr ⟨(Subgroup.mem_normalizer_iff.mp huN y).mp hyL, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hUC hu) hyE) (Subgroup.inv_mem _ (hUC hu))
    · have e : (⟨u * y * u⁻¹, hzN⟩ : N) = ⟨u, huN⟩ * ⟨y, hyN⟩ * (⟨u, huN⟩ : N)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hUR u hu huN) _).mp hyR
  obtain ⟨Q, hQP, hQc, hUQ⟩ := exists_normalized_threeSubgroup (P := P) (K := K) (O := O)
    (U := U) inf_le_left (fun y hy => hinf (Subgroup.le_normalizer hy) (hNθ (hPN hy)))
    (fun h3 => hθ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_right))) hcardP
    (inf_le_inf_left P hOθθ) (fun y hy => hinf (Subgroup.le_normalizer hy) (hNO (hPN hy)))
    ((Commute33Steps.odd_card_inSubgroup_pPrimeCore θ).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_right))
    (fun q hq k hk => ⟨P.mul_mem (P.mul_mem (P.mul_mem hq hk.1) (P.inv_mem hq)) (P.inv_mem hk.1),
      commutator_mem_oddCore hS h q (hPL hq) k hk.2⟩)
    h.U2 hUP (fun u hu => hinf (hUP hu) (hNO (h.UN hu)))
  have hQN : Q ≤ N := hQP.trans hPN
  have hQR : barImage L Q = R := by
    refine Subgroup.eq_of_le_of_card_ge (himg ▸ Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hQP (Subgroup.mem_subgroupOf.mp hx))) ?_
    have h1 := card_barImage_mul hQN
    have hQK : Q ⊓ Sec4.thetaQuotCentralizer L = ⊥ := by
      refine Subgroup.disjoint_def.mpr ?_ |>.eq_bot
      intro x hxQ hxK
      have hxPK : x ∈ P ⊓ Sec4.thetaQuotCentralizer L := Subgroup.mem_inf.mpr ⟨hQP hxQ, hxK⟩
      rw [hkerP] at hxPK
      have hxθ : x ∈ θ := (Subgroup.mem_inf.mp hxPK).2
      have h2 : orderOf x ∣ 3 ^ m := by
        rw [← hQc]
        exact Subgroup.orderOf_dvd_natCard Q hxQ
      have h3 : orderOf x ∣ Nat.card θ := Subgroup.orderOf_dvd_natCard θ hxθ
      have hcop : Nat.Coprime (3 ^ m) (Nat.card θ) :=
        Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
      exact orderOf_eq_one_iff.mp
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h3)
    rw [hQK, Subgroup.card_bot, mul_one, hQc] at h1
    rw [h1, hm]
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using h.Ee.2 _ g.2)⟩
  have hQE : Q ≤ Subgroup.normalizer (E : Set G) :=
    (hQP.trans hPE).trans (Subgroup.centralizer_le_normalizer _)
  have hQE3 : IsPGroup 3 (Q ⊔ E : Subgroup G) :=
    (IsPGroup.of_card hQc).to_sup_of_normal_right' hE3 hQE
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have h1 := Subgroup.mem_centralizer_iff.mp (hPE (hQP hx)) e he
    rw [h1, mul_inv_cancel_right]
    exact hx
  have hUE : U ≤ Subgroup.normalizer (E : Set G) := hUC.trans (Subgroup.centralizer_le_normalizer _)
  have hNQE : E ⊔ U ≤ Subgroup.normalizer ((Q ⊔ E : Subgroup G) : Set G) := by
    refine sup_le (fun e he => ?_) (fun u hu => ?_)
    · exact mem_normalizer_sup_of' (fun x hx => Subgroup.mem_sup_left
        ((Subgroup.mem_normalizer_iff.mp (hEQ he) x).mp hx)) (fun x hx => Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer he) x).mp hx))
    · exact mem_normalizer_sup_of' (fun x hx => Subgroup.mem_sup_left
        ((Subgroup.mem_normalizer_iff.mp (hUQ hu) x).mp hx)) (fun x hx => Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (hUE hu) x).mp hx))
  have hUinv : U ∈ invariantPiSubgroups ⊤ E (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, h.U2, h.EU⟩
  have hQEinv : (Q ⊔ E : Subgroup G) ∈ invariantPiSubgroups ⊤ (E ⊔ U) (piOf 3) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_three).mpr ⟨le_top, hQE3, hNQE⟩
  have hQU : Q ⊔ E ≤ Subgroup.centralizer (U : Set G) :=
    Sec6.rank3II_6_4_2 G hst E hEmem U hP U hUinv le_rfl _ hQEinv
  rw [← hQR]
  exact barImage_commute fun u hu q hq =>
    Subgroup.mem_centralizer_iff.mp (hQU (Subgroup.mem_sup_left hq)) u hu

end Item211LieProof

open Item211LieProof

section Certs


theorem item211LieMinusU42_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hK : KS211U42FourGroup) : Item211LieMinusU42 := by
  intro G _ _ A E U c L hpair _ hM hcase
  obtain ⟨-, ⟨e₀⟩, -⟩ := hcase
  have h := pairFacts h45 h66 hpair
  have hG := hpair.standing.toTheoremFourHyp
  have hEi := barImage_E_le_range_conj_of_projSU h hG le_rfl e₀
  have hUeq := barImage_U_eq_comm_of_minus h hM
  have hUi : barImage L U ≤ (MulAut.conj : lBar L →* MulAut (lBar L)).range := by
    rw [hUeq]
    exact commutator_le_range_conj _ _ hEi
  have hC := le_centralizer_of_ks211U42 hK h.q e₀ hEi hUi (isElemAbelian_barImage_E h)
    (card_barImage_E h) (isElemAbelian_barImage_U h) (card_barImage_U_of_minus h hM)
    (barImage_E_le_normalizer_U h)
  apply barImage_U_ne_bot h
  rw [hUeq, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact (Subgroup.le_centralizer_iff).mp hC

theorem item211LiePlusU42_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hK : KS211U42CharThree) : Item211LiePlusU42 := by
  intro G _ _ A E U c L hpair _ hP hcase
  obtain ⟨-, ⟨e₀⟩, -⟩ := hcase
  have h := pairFacts h45 h66 hpair
  have hG := hpair.standing.toTheoremFourHyp
  have : IsSimpleGroup (projSU 4 2 1) := isSimpleGroup_projSU le_rfl le_rfl
  have : IsSimpleGroup (lBar L) := e₀.isSimpleGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEi := barImage_E_le_range_conj_of_projSU h hG le_rfl e₀
  have hUR := barImage_U_comm_O3 hpair.mem_S hpair.standing hpair.mem_E.1 h hP
  apply barImage_U_ne_bot h
  rw [eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := (isPGroup_barImage_U h) ⟨τ, hτ⟩
  refine hK (lBar L) ⟨e₀⟩ (barImage L E) hEi (isElemAbelian_barImage_E h) (card_barImage_E h) τ
    ⟨k, by simpa using congrArg Subtype.val hk⟩ ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (barImage_U_comm_E_of_plus hP τ hτ d hd).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (hUR τ hτ r hr).symm

end Certs

end CFSG.RankThree.PartTwo.Sec21
