module

public import CFSG.Quasithin.Background.E1Amb
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.E1Inherit

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem comm_mul_left (x y a : G) : ⁅x * y, a⁆ = x * ⁅y, a⁆ * x⁻¹ * ⁅x, a⁆ := by
  simp only [commutatorElement_def]; group

theorem comm_mul_right (x y a : G) : ⁅x, y * a⁆ = ⁅x, y⁆ * (y * ⁅x, a⁆ * y⁻¹) := by
  simp only [commutatorElement_def]; group

section IBar

variable [Finite G]

theorem oTwoP_eq_top_of_forall {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (h : ∀ q : Q, ∃ k : ℕ, q ^ p ^ k ∈ CFSG.Open.pCore 2 Q) : oTwoP Q p = ⊤ :=
  top_le_iff.mp (le_oTwoP_of_series (N := CFSG.Open.pCore 2 Q) (R := ⊤)
    (CFSG.LieType.BorelTits.pCore_isPGroup 2) fun x _ => h x)

omit [Finite G] in
theorem commutator_mem_pCoreOf {S : Subgroup G} {o g : G} (ho : o ∈ pCoreOf 2 S) (hg : g ∈ S) :
    ⁅o, g⁆ ∈ pCoreOf 2 S := by
  have h1 := (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 S hg) o⁻¹).mp (Subgroup.inv_mem _ ho)
  have : ⁅o, g⁆ = o * (g * o⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact Subgroup.mul_mem _ ho h1

omit [Finite G] in
theorem comm_le_of_le_sup {S A R : Subgroup G} (hAS : A ≤ S)
    (hRU : R ≤ twoResidual S ⊔ pCoreOf 2 S) : ⁅R, A⁆ ≤ ⁅twoResidual S, A⁆ ⊔ pCoreOf 2 S := by
  have hUS : twoResidual S ≤ S := twoResidual_le S
  have hUnorm : S ≤ Subgroup.normalizer (twoResidual S : Set G) := le_normalizer_twoResidual S
  refine Subgroup.commutator_le.mpr fun r hr a ha => ?_
  have hr' : r ∈ twoResidual S ⊔ pCoreOf 2 S := hRU hr
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (twoResidual S)
    (pCoreOf 2 S) ((CFSG.LieType.BorelTits.pCoreOf_le 2 S).trans hUnorm)] at hr'
  obtain ⟨u, hu, o, ho, rfl⟩ := hr'
  have haS : a ∈ S := hAS ha
  have huS : u ∈ S := hUS hu
  have hoa : ⁅o, a⁆ ∈ pCoreOf 2 S := by
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 S haS) o⁻¹).mp (Subgroup.inv_mem _ ho)
    have : ⁅o, a⁆ = o * (a * o⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact Subgroup.mul_mem _ ho h1
  have h2 : u * ⁅o, a⁆ * u⁻¹ ∈ pCoreOf 2 S :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 S huS) ⁅o, a⁆).mp hoa
  rw [comm_mul_left]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h2)
    (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu ha))

theorem eOneAmb_facts {S A : Subgroup G} (hAS : A ≤ S) (h : EOneAmb S A) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ IsPGroup 2 (twoResidual S) ∧
      (∀ x ∈ twoResidual S, ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 S) ∧
      (∀ u ∈ twoResidual S, (∃ j : ℕ, u ^ 2 ^ j = 1) → u ∈ pCoreOf 2 S) ∧
      twoResidual S ≤ ⁅twoResidual S, A⁆ ⊔ pCoreOf 2 S ∧ (pCoreOf 2 S).relIndex A = 2 := by
  obtain ⟨p, hp, hp2, R, hRS, hSR, hNR, hR1, hR2, hRne, hRcomm, hrel⟩ := h
  have hU : twoResidual S ≤ R := by
    refine twoResidual_le_of_isTwoQuotient hRS hSR fun y hy => hR2 y hy
  have hUS : twoResidual S ≤ S := twoResidual_le S
  have hUnorm : S ≤ Subgroup.normalizer (twoResidual S : Set G) := le_normalizer_twoResidual S
  have hRU : R ≤ twoResidual S ⊔ pCoreOf 2 S := by
    intro x hx
    obtain ⟨k, hk⟩ := hR1 x hx
    obtain ⟨j, hj⟩ := twoResidual_isTwoQuotient S x (hRS hx)
    exact mem_of_pow_mem_two_p hp hp2 (Subgroup.mem_sup_right hk) (Subgroup.mem_sup_left hj)
  refine ⟨p, hp, hp2, ?_, fun x hx => ?_, fun u hu ⟨j, hj⟩ => ?_, ?_, hrel⟩
  · intro h2
    apply hRne
    have hUO : twoResidual S ≤ pCoreOf 2 S :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUS hUnorm h2
    exact le_antisymm ((hRU.trans (sup_le hUO le_rfl))) hNR
  · exact hR1 x (hU hx)
  · obtain ⟨k, hk⟩ := hR1 u (hU hu)
    exact mem_of_pow_mem_two_p hp hp2 hk (by rw [hj]; exact Subgroup.one_mem _)
  · intro x hx
    have hx' : x ∈ ⁅R, A⁆ ⊔ pCoreOf 2 S := hRcomm (hU hx)
    have hle : ⁅R, A⁆ ⊔ pCoreOf 2 S ≤ ⁅twoResidual S, A⁆ ⊔ pCoreOf 2 S :=
      sup_le (comm_le_of_le_sup hAS hRU) le_sup_right
    exact hle hx'

end IBar

section Normalizers

theorem mem_normalizer_sup {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  have e₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hH
  have e₂ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hK
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, e₁, e₂]

theorem mem_normalizer_inf {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro w
  simp only [Subgroup.mem_inf]
  rw [hH w, hK w]

theorem mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have e₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hH
  have e₂ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hK
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator, e₁, e₂]

theorem mem_normalizer_of_conj_mem [Finite G] {X : Subgroup G} {g : G}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : X.map (MulAut.conj g).toMonoidHom ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using h x hx
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

theorem commutator_le_of_le_normalizer {R X : Subgroup G} (h : X ≤ Subgroup.normalizer (R : Set G)) :
    ⁅R, X⁆ ≤ R := by
  refine Subgroup.commutator_le.mpr fun r hr x hx => ?_
  have h1 : ⁅r, x⁆ = r * (x * r⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
  rw [h1]
  exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (h hx) r⁻¹).mp (R.inv_mem hr))

theorem commutator_sup_le {R A P : Subgroup G} (hR : R ≤ Subgroup.normalizer (P : Set G))
    (hA : A ≤ Subgroup.normalizer (P : Set G)) : ⁅R, A ⊔ P⁆ ≤ ⁅R, A⁆ ⊔ P := by
  refine Subgroup.commutator_le.mpr fun r hr x hx => ?_
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A P hA] at hx
  obtain ⟨a, ha, q, hq, rfl⟩ := hx
  rw [comm_mul_right]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hr ha))
    (Subgroup.mem_sup_right ?_)
  have h1 : ⁅r, q⁆ ∈ P := by
    have e : ⁅r, q⁆ = (r * q * r⁻¹) * q⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hR hr) q).mp hq) (P.inv_mem hq)
  exact (Subgroup.mem_normalizer_iff.mp (hA ha) ⁅r, q⁆).mp h1

end Normalizers

section Images

variable {G' : Type*} [Group G']

theorem isElemAbelian_map' {p : ℕ} (f : G →* G') {A : Subgroup G} (h : IsElemAbelian p A) :
    IsElemAbelian p (A.map f) := CFSG.Open.IsElemAbelian.map h _

theorem isSylowIn_two_map_top [Finite G] [Finite G'] {f : G →* G'} (hf : Function.Surjective f)
    {T : Subgroup G} (hT : IsSylowIn 2 T ⊤) : IsSylowIn 2 (T.map f) ⊤ := by
  have hidx : ¬ 2 ∣ T.index := by
    have := hT.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at this
  let C : Sylow 2 G := hT.isPGroup.toSylow hidx
  have hC : (C : Subgroup G) = T := rfl
  have := isSylowIn_top (C.mapSurjective hf)
  rwa [Sylow.coe_mapSurjective, hC] at this

end Images

section Main

variable [Finite G]

theorem ten_seven_eOne {T A Y : Subgroup G} [Y.Normal] (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T)
    (hAab : IsElemAbelian 2 A) {i : ℕ} {I : Subgroup (G ⧸ Y)}
    (hI : IsE i ⊤ (T.map (QuotientGroup.mk' Y)) (A.map (QuotientGroup.mk' Y)) I)
    (hE : EOne ↥I ((A.map (QuotientGroup.mk' Y)).subgroupOf I) ∧
      Nat.card (barO2 ↥I ((A.map (QuotientGroup.mk' Y)).subgroupOf I)) ≤ 2 ^ i) :
    ∃ J : Subgroup G, IsE i ⊤ T A J ∧
      twoResidual I = (twoResidual J).map (QuotientGroup.mk' Y) := by
  set π := QuotientGroup.mk' Y with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  have hI' := hI
  obtain ⟨-, hIτ, hIS, -⟩ := hI
  set Tb : Subgroup (G ⧸ Y) := T.map π with hTb
  set Ab : Subgroup (G ⧸ Y) := A.map π with hAb
  have hTb' : IsSylowIn 2 Tb ⊤ := isSylowIn_two_map_top hπs hT
  have hAbT : Ab ≤ Tb := Subgroup.map_mono hA
  have hAbab : IsElemAbelian 2 Ab := isElemAbelian_map' π hAab
  have hAbI : Ab ≤ I := by
    have h1 : Ab ⊔ pCoreOf 2 ⊤ ≤ tauOf ⊤ Tb Ab := le_tauOf hTb' hAbT hAbab
    exact (le_sup_left.trans (h1.trans hIτ)).trans inf_le_right
  have hAbTI : Ab ≤ Tb ⊓ I := le_inf hAbT hAbI
  set U : Subgroup (G ⧸ Y) := twoResidual I with hU
  set tb : Subgroup (G ⧸ Y) := tauOf I (Tb ⊓ I) Ab with htb
  set G1 : Subgroup (G ⧸ Y) := U ⊔ tb with hG1
  have htbT : tb ≤ Tb ⊓ I := tauOf_le _ _ _
  have htbI : tb ≤ I := htbT.trans inf_le_right
  have hAbtb : Ab ≤ tb := le_sup_left.trans (le_tauOf hIS hAbTI hAbab)
  have hUI : U ≤ I := twoResidual_le I
  have hUnorm : I ≤ Subgroup.normalizer (U : Set (G ⧸ Y)) := le_normalizer_twoResidual I
  have hG1I : G1 ≤ I := sup_le hUI htbI
  have hUG1 : U ≤ G1 := le_sup_left
  have htbG1 : tb ≤ G1 := le_sup_right
  have hG1norm : G1 ≤ Subgroup.normalizer (U : Set (G ⧸ Y)) := hG1I.trans hUnorm
  have hτbar : tauOf ⊤ Tb Ab ≤ tb := by
    have hI'' : IsE i ⊤ (Tb ⊓ ⊤) Ab I := by rw [inf_top_eq]; exact hI'
    have := (eight_one (H₁ := ⊤) (H₂ := ⊤) hTb' hAbT hAbab le_rfl
      (by rw [inf_top_eq]; exact hIτ.trans inf_le_left) (by rw [inf_top_eq]; exact hTb')
      hI'').2.2.1
    rwa [inf_top_eq] at this
  set H1 : Subgroup G := G1.comap π with hH1
  set X1 : Subgroup G := U.comap π with hX1
  set T1 : Subgroup G := T ⊓ H1 with hT1
  have hYX1 : Y ≤ X1 := fun y hy => by
    show π y ∈ U
    have h1 : π y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    rw [h1]
    exact Subgroup.one_mem _
  have hX1H1 : X1 ≤ H1 := Subgroup.comap_mono hUG1
  have hH1X1 : H1 ≤ Subgroup.normalizer (X1 : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 := Subgroup.mem_normalizer_iff.mp (hG1norm (show π h ∈ G1 from hh)) (π w)
    show π w ∈ U ↔ π (h * w * h⁻¹) ∈ U
    simpa using h1
  have hmapH1 : H1.map π = G1 := Subgroup.map_comap_eq_self_of_surjective hπs _
  have hmapX1 : X1.map π = U := Subgroup.map_comap_eq_self_of_surjective hπs _
  have hT1H1 : T1 ≤ H1 := inf_le_right
  have hπT1 : T1.map π = Tb ⊓ G1 := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨Subgroup.mem_map_of_mem _ ht.1, ht.2⟩
    · rintro _ ⟨⟨t, ht, rfl⟩, h2⟩
      exact ⟨t, ⟨ht, h2⟩, rfl⟩
  have hTb2 : IsPGroup 2 Tb := hTb'.isPGroup
  have hUtb : U ⊔ (Tb ⊓ G1) = G1 :=
    le_antisymm (sup_le hUG1 inf_le_right)
      (sup_le_sup_left (le_inf (htbT.trans inf_le_left) htbG1) U |>.trans' (by rw [hG1]))
  have hUN : (U.subgroupOf I).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUI).mpr hUnorm
  have hSylG1 : IsSylowIn 2 (Tb ⊓ G1) G1 := by
    have h1 : IsSylowIn 2 ((Tb ⊓ G1) ⊓ U) U := by
      have := hIS.inf_normal hUI hUN
      have e : (Tb ⊓ G1) ⊓ U = (Tb ⊓ I) ⊓ U := by
        rw [inf_assoc, inf_assoc, inf_eq_right.mpr hUG1, inf_eq_right.mpr hUI]
      rwa [← e] at this
    have h2 := isSylowIn_two_of_sup_inf (N := U) (S := Tb ⊓ G1) (inf_le_right.trans hG1norm)
      (hTb2.to_le inf_le_left) h1
    rwa [hUtb] at h2
  have hSyl1 : IsSylowIn 2 T1 H1 := by
    have hidx : ¬ 2 ∣ T.index := by
      have := hT.not_dvd_relIndex
      rwa [Subgroup.relIndex_top_right] at this
    let C : Sylow 2 G := hT.isPGroup.toSylow hidx
    have hC : (C : Subgroup G) = T := rfl
    have := isSylowIn_inf_of_quotient Y (hYX1.trans hX1H1) C (by rw [hC, hmapH1]; exact hSylG1)
    rwa [hC] at this
  have hT1X1 : T1 ≤ Subgroup.normalizer (X1 : Set G) := hT1H1.trans hH1X1
  have hτT1 : tauOf ⊤ T A ≤ T1 := by
    intro t ht
    refine ⟨tauOf_le _ _ _ ht, ?_⟩
    have h1 : (tauOf ⊤ T A).map π ≤ tauOf ⊤ Tb Ab := by
      have := tauOf_map_le π (A := A) (le_top : T ≤ ⊤)
      rwa [Subgroup.map_top_of_surjective π hπs] at this
    exact (hτbar.trans htbG1) (h1 (Subgroup.mem_map_of_mem π ht))
  have hAT1 : A ≤ T1 := fun a ha => hτT1 (le_tauOf hT hA hAab (Subgroup.mem_sup_left ha))
  obtain ⟨J, hJmin⟩ := (Set.toFinite {K' : Subgroup G | K' ≤ X1 ⊔ T1 ∧ T1 ≤ K' ∧
      X1 ⊔ T1 = K' ⊔ Y}).exists_minimal ⟨X1 ⊔ T1, le_rfl, le_sup_right,
      (sup_eq_left.mpr (hYX1.trans le_sup_left)).symm⟩
  have hJ : J ∈ sFamily T1 X1 Y :=
    ⟨hJmin.prop.1, hJmin.prop.2.1, hJmin.prop.2.2,
      fun K' h1 h2 h3 h4 => hJmin.eq_of_le ⟨h1, h2, h3⟩ h4⟩
  obtain ⟨hJle, hT1J, hEq, hmin⟩ := hJ
  have hJH1 : J ≤ H1 := hJle.trans (sup_le hX1H1 hT1H1)
  have hker : π.ker = Y := QuotientGroup.ker_mk' Y
  have hYbot : Y.map π = ⊥ := (Subgroup.map_eq_bot_iff Y).mpr hker.ge
  have hπJ : J.map π = G1 := by
    have h1 : (X1 ⊔ T1).map π = G1 := by rw [Subgroup.map_sup, hmapX1, hπT1, hUtb]
    have h2 : (J ⊔ Y).map π = J.map π := by rw [Subgroup.map_sup, hYbot, sup_bot_eq]
    calc J.map π = (J ⊔ Y).map π := h2.symm
      _ = (X1 ⊔ T1).map π := by rw [hEq]
      _ = G1 := h1
  have hJU : twoResidual I = (twoResidual J).map π := by
    rw [map_twoResidual π J, hπJ]
    exact (twoResidual_sup_eq htbI).symm
  have hJX1 : (J ⊓ X1).map π = U := by
    have := (ten_one hT1X1 hYX1 ⟨hJle, hT1J, hEq, hmin⟩).2.1
    rw [this]
    exact hmapX1
  obtain ⟨p, hp, hp2, hnotP, hpow, h2el, hcomm, hrelI⟩ :=
    eOneAmb_facts hAbI ((eOne_iff_amb hAbI).mp hE.1)
  have : Fact p.Prime := ⟨hp⟩
  have hJ' : J ∈ sFamily T1 X1 Y := ⟨hJle, hT1J, hEq, hmin⟩
  have hAJ : A ≤ J := hAT1.trans hT1J
  have hT1' : IsPGroup 2 T1 := hSyl1.isPGroup
  have hoU : oTwoP ↥((J ⊓ X1).map π) p = ⊤ := by
    rw [hJX1]
    refine oTwoP_eq_top_of_forall fun q => ?_
    obtain ⟨k, hk⟩ := hpow (q : G ⧸ Y) q.2
    refine ⟨k, ?_⟩
    have hmem : (q : G ⧸ Y) ^ p ^ k ∈ pCoreOf 2 U := by
      have h1 : U ⊓ pCoreOf 2 I ≤ pCoreOf 2 U := by
        refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
        · intro u hu
          exact mem_normalizer_inf (Subgroup.le_normalizer hu)
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I (hUI hu))
        · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).to_le inf_le_right
      exact h1 ⟨U.pow_mem q.2 _, hk⟩
    obtain ⟨y, hy, hyq⟩ := hmem
    have : y = q ^ p ^ k := Subtype.ext (by simpa using hyq)
    rwa [← this]
  obtain ⟨R, hRdef, hRJ, hJR, hZR, hRpow, hJ2⟩ :=
    ten_three_data hT1X1 hYX1 hX1H1 hSyl1 hJ' hp hoU
  obtain ⟨hPsyl, hJP, hfac⟩ := ten_two_core hSyl1 hX1H1 hJ'
  set Z : Subgroup G := preO2 J Y with hZ
  set P : Subgroup G := T1 ⊓ Z with hP
  have hZJ : Z ≤ J := preO2_le J Y
  have hPZ : P ≤ Z := inf_le_right
  have hPJ : P ≤ J := hPZ.trans hZJ
  have hP2 : IsPGroup 2 P := hT1'.to_le inf_le_left
  have hPO : P ≤ pCoreOf 2 J := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPJ hJP hP2
  have hZO : pCoreOf 2 J ≤ Z := fun o ho =>
    ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 J ho,
      map_pCoreOf_le π J (Subgroup.mem_map_of_mem π ho)⟩
  have hPR : P ≤ R := hPZ.trans hZR
  have hJXR : J ⊓ X1 ≤ R := hRdef ▸ le_sup_left
  have hA1 : A ≤ Subgroup.normalizer (P : Set G) := hAJ.trans hJP
  have hT1P : T1 ≤ Subgroup.normalizer (P : Set G) := hT1J.trans hJP
  have hRP : R ≤ Subgroup.normalizer (P : Set G) := hRJ.trans hJP
  have hG1O : pCoreOf 2 I ⊓ G1 ≤ pCoreOf 2 (J.map π) := by
    rw [hπJ]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).to_le inf_le_left)
    intro g hg
    exact mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I (hG1I hg))
      (Subgroup.le_normalizer hg)
  have hRne : R ≠ pCoreOf 2 J := by
    intro h
    apply hnotP
    have hRp : IsPGroup 2 R := h ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J
    have hUle : U ≤ R.map π := by
      rw [← hJX1]
      exact Subgroup.map_mono hJXR
    exact (hRp.map π).to_le hUle
  have hTb2' : IsPGroup 2 Tb := hTb2
  have hTA : ∀ t ∈ T1, ∀ a ∈ A, ⁅t, a⁆ ∈ P := by
    intro t ht a ha
    have ht' : π t ∈ Tb ⊓ G1 := by rw [← hπT1]; exact Subgroup.mem_map_of_mem π ht
    have hπtG1 : π t ∈ G1 := ht'.2
    have hmem : π t ∈ G1 := hπtG1
    rw [hG1, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_right_le_normalizer_left U tb (htbI.trans hUnorm)] at hmem
    obtain ⟨u, hu, s, hs, hus⟩ := hmem
    have huT : u ∈ Tb := by
      have : u = π t * s⁻¹ := by rw [← hus]; group
      rw [this]
      exact Tb.mul_mem ht'.1 (Tb.inv_mem (htbT hs).1)
    obtain ⟨j, hj⟩ := hTb2' ⟨u, huT⟩
    have huo : u ∈ pCoreOf 2 I := by
      refine h2el u hu ⟨j, ?_⟩
      have := congrArg Subtype.val hj
      simpa using this
    have hAba : π a ∈ Ab := Subgroup.mem_map_of_mem π ha
    have h1 : ⁅s, π a⁆ ∈ pCoreOf 2 I := (mem_tauOf.mp hs).2.2 (π a) hAba
    have h2 : u * ⁅s, π a⁆ * u⁻¹ ∈ pCoreOf 2 I :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I (hUI hu)) ⁅s, π a⁆).mp h1
    have h3 : ⁅u, π a⁆ ∈ pCoreOf 2 I := commutator_mem_pCoreOf huo (hAbI hAba)
    have h4 : ⁅π t, π a⁆ ∈ pCoreOf 2 I := by
      rw [← hus, comm_mul_left]
      exact Subgroup.mul_mem _ h2 h3
    have h5 : ⁅π t, π a⁆ ∈ G1 := by
      have e : ⁅π t, π a⁆ = π t * π a * (π t)⁻¹ * (π a)⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact G1.mul_mem (G1.mul_mem (G1.mul_mem hπtG1 (htbG1 (hAbtb hAba)))
        (G1.inv_mem hπtG1)) (G1.inv_mem (htbG1 (hAbtb hAba)))
    have h6 : π ⁅t, a⁆ ∈ pCoreOf 2 (J.map π) := by
      rw [map_commutatorElement]
      exact hG1O ⟨h4, h5⟩
    have h7 : ⁅t, a⁆ ∈ Z := ⟨J.mul_mem (J.mul_mem (J.mul_mem (hT1J ht) (hAJ ha))
      (J.inv_mem (hT1J ht))) (J.inv_mem (hAJ ha)), h6⟩
    exact ⟨T1.mul_mem (T1.mul_mem (T1.mul_mem ht (hAT1 ha)) (T1.inv_mem ht)) (T1.inv_mem (hAT1 ha)),
      h7⟩
  set R0 : Subgroup G := ⁅R, A ⊔ P⁆ ⊔ P with hR0
  have hT1AP : ∀ t ∈ T1, t ∈ Subgroup.normalizer ((A ⊔ P : Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_of_conj_mem
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A P hA1] at hx
    obtain ⟨a, ha, q, hq, rfl⟩ := hx
    have e : t * (a * q) * t⁻¹ = (⁅t, a⁆ * a) * (t * q * t⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (A ⊔ P).mul_mem ((A ⊔ P).mul_mem (Subgroup.mem_sup_right (hTA t ht a ha))
      (Subgroup.mem_sup_left ha)) (Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (hT1P ht) q).mp hq))
  have hT1R0 : T1 ≤ Subgroup.normalizer (R0 : Set G) := fun t ht =>
    mem_normalizer_sup (mem_normalizer_commutator (hJR (hT1J ht)) (hT1AP t ht)) (hT1P ht)
  have hR0R : R0 ≤ R := by
    refine sup_le ?_ hPR
    exact commutator_le_of_le_normalizer (sup_le (hAJ.trans hJR) (hPJ.trans hJR))
  have hAR0 : ⁅R, A⁆ ≤ R0 :=
    (Subgroup.commutator_mono le_rfl le_sup_left).trans le_sup_left
  have hPR0 : P ≤ R0 := le_sup_right
  have hOR : pCoreOf 2 J ≤ R := hZO.trans hZR
  have hUR : U ≤ R.map π := by
    rw [← hJX1]
    exact Subgroup.map_mono hJXR
  have hcU : ⁅U, Ab⁆ ≤ U := commutator_le_of_le_normalizer (hAbI.trans hUnorm)
  have hcomI : ⁅U, Ab⁆ ≤ I := hcU.trans hUI
  have hUR0 : U ≤ R0.map π := by
    intro x hx
    have hx' : x ∈ ⁅U, Ab⁆ ⊔ pCoreOf 2 I := hcomm hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right ⁅U, Ab⁆ (pCoreOf 2 I)
      (hcomI.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I))] at hx'
    obtain ⟨c, hc, o, ho, rfl⟩ := hx'
    have hc1 : c ∈ (⁅R, A⁆).map π := by
      have : ⁅U, Ab⁆ ≤ (⁅R, A⁆).map π := by
        rw [Subgroup.map_commutator]
        exact Subgroup.commutator_mono hUR le_rfl
      exact this hc
    have hc2 : c ∈ R0.map π := Subgroup.map_mono hAR0 hc1
    have hoU : o ∈ U := by
      have : o = c⁻¹ * (c * o) := by group
      rw [this]
      exact U.mul_mem (U.inv_mem (hcU hc)) hx
    have hoJ : o ∈ pCoreOf 2 (J.map π) := hG1O ⟨ho, hUG1 hoU⟩
    obtain ⟨j, hj, hjo⟩ := CFSG.LieType.BorelTits.pCoreOf_le 2 (J.map π) hoJ
    have hjZ : j ∈ Z := ⟨hj, by show π j ∈ pCoreOf 2 (J.map π); rw [hjo]; exact hoJ⟩
    obtain ⟨s, hs, y, hy, hjsy⟩ := hfac j hjZ
    have hπy : π y = 1 := (QuotientGroup.eq_one_iff y).mpr hy.2
    have hos : o = π s := by rw [← hjo, hjsy, map_mul, hπy, mul_one]
    have ho2 : o ∈ R0.map π := hos ▸ Subgroup.mem_map_of_mem π (hPR0 hs)
    exact (R0.map π).mul_mem hc2 ho2
  have hJ'le : R0 ⊔ T1 ≤ J := sup_le (hR0R.trans hRJ) hT1J
  have hG1J' : G1 ≤ (R0 ⊔ T1).map π := by
    rw [← hUtb, Subgroup.map_sup]
    exact sup_le (hUR0.trans le_sup_left) ((le_of_eq hπT1.symm).trans le_sup_right)
  have hEq' : X1 ⊔ T1 = (R0 ⊔ T1) ⊔ Y := by
    refine le_antisymm (fun z hz => ?_) (sup_le (hJ'le.trans hJle) (hYX1.trans le_sup_left))
    have hzH1 : z ∈ H1 := (sup_le hX1H1 hT1H1) hz
    obtain ⟨w, hw, hwz⟩ := hG1J' hzH1
    have hwy : w⁻¹ * z ∈ Y := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hwz]
      simp
    have : z = w * (w⁻¹ * z) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hwy)
  have hJ'J : R0 ⊔ T1 = J := hmin (R0 ⊔ T1) (hJ'le.trans hJle) le_sup_right hEq' hJ'le
  have hRR0 : R ≤ R0 := by
    intro r hr
    have hrJ : r ∈ R0 ⊔ T1 := hJ'J.symm ▸ hRJ hr
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left R0 T1 hT1R0] at hrJ
    obtain ⟨ρ, hρ, t, ht, rfl⟩ := hrJ
    have htR : t ∈ R := by
      have : t = ρ⁻¹ * (ρ * t) := by group
      rw [this]
      exact R.mul_mem (R.inv_mem (hR0R hρ)) hr
    obtain ⟨k, hk⟩ := hRpow t htR
    obtain ⟨j, hj⟩ := hT1' ⟨t, ht⟩
    have hj' : t ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have htR0 : t ∈ R0 :=
      mem_of_pow_mem_two_p hp hp2 (hPR0 hk) (by rw [hj']; exact Subgroup.one_mem _)
    exact R0.mul_mem hρ htR0
  have hRcomm : R ≤ ⁅R, A⁆ ⊔ pCoreOf 2 J := by
    intro r hr
    have h1 : R0 ≤ ⁅R, A⁆ ⊔ pCoreOf 2 J :=
      sup_le ((commutator_sup_le hRP hA1).trans (sup_le_sup_left hPO _))
        (hPO.trans le_sup_right)
    exact h1 (hRR0 hr)
  have hWrel : ((pCoreOf 2 I).comap π).relIndex A = 2 := by
    rw [Subgroup.relIndex_comap]
    exact hrelI
  have hAW : A ⊓ (pCoreOf 2 I).comap π ≤ pCoreOf 2 J := by
    intro a ha
    have haT1 := hAT1 ha.1
    have h1 : π a ∈ pCoreOf 2 (J.map π) := hG1O ⟨ha.2, hT1H1 haT1⟩
    exact hPO ⟨haT1, ⟨hAJ ha.1, h1⟩⟩
  have hdvd : (pCoreOf 2 J).relIndex A ∣ 2 := by
    have h1 : (A ⊓ pCoreOf 2 J).relIndex A ∣ (A ⊓ (pCoreOf 2 I).comap π).relIndex A :=
      Subgroup.relIndex_dvd_of_le_left A (le_inf inf_le_left hAW)
    rwa [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left, hWrel] at h1
  have hrelJ : (pCoreOf 2 J).relIndex A = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exfalso
      apply hRne
      have hAN : A ≤ pCoreOf 2 J := Subgroup.relIndex_eq_one.mp h1
      have hRA : ⁅R, A⁆ ≤ pCoreOf 2 J := by
        refine Subgroup.commutator_le.mpr fun r hr a ha => ?_
        have e : ⁅r, a⁆ = (r * a * r⁻¹) * a⁻¹ := by simp only [commutatorElement_def]
        rw [e]
        exact (pCoreOf 2 J).mul_mem
          ((Subgroup.mem_normalizer_iff.mp
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J (hRJ hr)) a).mp (hAN ha))
          ((pCoreOf 2 J).inv_mem (hAN ha))
      exact le_antisymm (fun r hr => (sup_le hRA le_rfl) (hRcomm hr)) hOR
    · exact h2
  have hEJ : EOne ↥J (A.subgroupOf J) :=
    (eOne_iff_amb hAJ).mpr ⟨p, hp, hp2, R, hRJ, hJR, hOR,
      fun x hx => let ⟨k, hk⟩ := hRpow x hx; ⟨k, hPO hk⟩, hJ2, hRne, hRcomm, hrelJ⟩
  have hcard : Nat.card (barO2 ↥J (A.subgroupOf J)) ≤ 2 ^ i := by
    obtain ⟨_, _, _, _, _, _, hc⟩ := hEJ
    obtain ⟨_, _, _, _, _, _, hc'⟩ := hE.1
    have := hE.2
    rw [hc'] at this
    rwa [hc]
  have hSylJ : IsSylowIn 2 (T1 ⊓ J) J := by
    rw [inf_eq_left.mpr hT1J]
    exact B6.isSylowTwoOf_mono hSyl1 hT1J hJH1
  have hK : IsE i H1 (T ⊓ H1) A J :=
    ⟨hJH1, (tauOf_le H1 T1 A).trans (le_inf le_rfl hT1J), hSylJ, Or.inl ⟨hEJ, hcard⟩⟩
  exact ⟨J, eight_two hT hA hAab le_top hτT1 hSyl1 hK, hJU⟩

end Main

end E1

end CFSG.Quasithin
