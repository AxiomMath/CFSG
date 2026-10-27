module

public import CFSG.Quasithin.EmptyFaithful.S153LSolv
public import CFSG.Quasithin.EmptyFaithful.S153LNsf3
public import CFSG.Quasithin.EmptyFaithful.S153LComp
public import CFSG.Quasithin.EmptyFaithful.S153LList3

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace S153L

section Conj

variable {Ω : Type} [Group Ω]

theorem comp_map_conj_eq {J : Subgroup Ω} {y : Ω} (hy : ∀ x, x ∈ J ↔ y * x * y⁻¹ ∈ J) :
    J.map (MulAut.conj y).toMonoidHom = J := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hy z).mp hz
  · intro hx
    refine ⟨y⁻¹ * x * y, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    exact (hy _).mpr (by simpa [mul_assoc] using hx)

theorem comp_mem_normalizer_of_map_eq {K : Subgroup Ω} {y : Ω}
    (h : K.map (MulAut.conj y).toMonoidHom = K) : y ∈ Subgroup.normalizer (K : Set Ω) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have : y * k * y⁻¹ ∈ K.map (MulAut.conj y).toMonoidHom := ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rwa [h] at this
  · intro hk
    rw [← h] at hk
    obtain ⟨k', hk', e⟩ := hk
    have : k' = k := (MulAut.conj y).injective (by simpa using e)
    rwa [← this]

theorem comp_map_conj_three {K : Subgroup Ω} {y : Ω} (hy3 : y ^ 3 = 1) :
    ((K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj y).toMonoidHom).map
      (MulAut.conj y).toMonoidHom = K := by
  simp only [Subgroup.map_map]
  have hyyy : y * (y * y) = 1 := by rw [← pow_three]; exact hy3
  have : ((MulAut.conj y).toMonoidHom.comp
      ((MulAut.conj y).toMonoidHom.comp (MulAut.conj y).toMonoidHom)) = MonoidHom.id Ω := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
    calc y * (y * (y * x * y⁻¹) * y⁻¹) * y⁻¹ = (y * (y * y)) * x * (y * (y * y))⁻¹ := by group
      _ = x := by rw [hyyy]; simp
  rw [this, Subgroup.map_id]

variable [Finite Ω]

omit [Finite Ω] in
theorem comp_conj_mem_cComp {J K : Subgroup Ω} {y : Ω} (hy : ∀ x, x ∈ J ↔ y * x * y⁻¹ ∈ J)
    (hK : K ∈ cComp J) : K.map (MulAut.conj y).toMonoidHom ∈ cComp J := by
  have h := cComp_map_mulEquiv (MulAut.conj y) hK
  rwa [comp_map_conj_eq hy] at h

omit [Finite Ω] in
theorem comp_normalizes_of_two {J N₁ N₂ K : Subgroup Ω} {y : Ω}
    (hall : ∀ K' ∈ cComp J, K' = N₁ ∨ K' = N₂) (hK : K ∈ cComp J)
    (hy : ∀ x, x ∈ J ↔ y * x * y⁻¹ ∈ J) (hy3 : y ^ 3 = 1) :
    y ∈ Subgroup.normalizer (K : Set Ω) := by
  set c := (MulAut.conj y).toMonoidHom with hc
  have hK₁ : K.map c ∈ cComp J := comp_conj_mem_cComp hy hK
  have hK₂ : (K.map c).map c ∈ cComp J := comp_conj_mem_cComp hy hK₁
  by_cases h1 : K.map c = K
  · exact comp_mem_normalizer_of_map_eq h1
  · exfalso
    have h2 : (K.map c).map c ≠ K.map c := fun h =>
      h1 (Subgroup.map_injective (MulAut.conj y).injective h)
    have h3 : (K.map c).map c = K := by
      rcases hall K hK with a | a <;> rcases hall (K.map c) hK₁ with b | b <;>
        rcases hall ((K.map c).map c) hK₂ with d | d <;>
        first
          | exact d.trans a.symm
          | exact absurd (d.trans b.symm) h2
          | exact absurd (b.trans a.symm) h1
    apply h1
    have := comp_map_conj_three (K := K) hy3
    rw [h3] at this
    exact this

end Conj

section Main

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem comp_not_isSolvable_of_quasisimple {J N : Subgroup (MulAut V)} (hNJ : N ≤ J)
    (hq : CFSG.IsQuasisimple ↥N) : ¬ Group.IsSolvable ↥J := by
  intro hs
  have hNs : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNJ)
      (Subgroup.inclusion_injective hNJ)
  have hnt : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr (SBc3.ne_bot_of_isQuasisimple hq)
  have hperf : Group.IsPerfect ↥N := hq.1
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥N
  rw [Group.IsPerfect.commutator_eq_top] at this
  exact lt_irrefl _ this

theorem ns_main (h56 : AsB56) (hV : ∀ v : V, v ^ 2 = 1)
    (Hs Js Ms Ys Ts Bs : Subgroup (MulAut V))
    (hJH : Js ≤ Hs) (hJn : ∀ h ∈ Hs, ∀ j ∈ Js, h * j * h⁻¹ ∈ Js)
    (hO2 : pCoreOf 2 Hs = ⊥) (hSQ : SQTKGroup ↥Js)
    (hYM : Ys ≤ Ms) (hMH : Ms ≤ Hs)
    (hBoff : IsFFStarOffender Hs Bs) (hBJ : Bs ≤ Js) (hBR : Bs ≤ pCoreOf 2 (Ys ⊔ Ts))
    (hJgen : Js = conjClosure Bs Hs)
    (hθ : ∀ x ∈ Ms, orderOf x = 3 → x ∈ Ys)
    (hYgen : Ys = Subgroup.closure {y | y ∈ Ys ∧ orderOf y = 3})
    (hKL : ∀ X : Subgroup (MulAut V), X ≤ Hs → (∀ x ∈ X, ∀ y ∈ Ys, x * y = y * x) → X ≤ Ms)
    (hY3 : ∀ E : Subgroup (MulAut V), E ≤ Ys → IsPGroup 3 E → Nat.card E ≤ 3) :
    ¬ Group.IsSolvable ↥Js ∧
      ∀ K ∈ cComp Js, Ys ≤ Subgroup.normalizer (K : Set (MulAut V)) ∧ ⁅K, Ys⁆ = K := by
  have hJnorm : ∀ y ∈ Hs, ∀ x, x ∈ Js ↔ y * x * y⁻¹ ∈ Js := fun y hy x =>
    ⟨hJn y hy x, fun hx => by simpa [mul_assoc] using hJn y⁻¹ (Hs.inv_mem hy) _ hx⟩
  have hJne : Js ≠ ⊥ := fun h => hBoff.2.1 (le_bot_iff.mp (h ▸ hBJ))
  have hO2J : pCoreOf 2 Js = ⊥ := by
    have hn : Hs ≤ Subgroup.normalizer (Js : Set (MulAut V)) := fun y hy => by
      rw [Subgroup.mem_normalizer_iff]
      exact hJnorm y hy
    have : pCoreOf 2 Js ≤ pCoreOf 2 Hs :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Js).trans hJH)
        (fun g hg => normalizer_le_normalizer_pCoreOf 2 _ (hn hg)) (pCoreOf_isPGroup 2 Js)
    rw [hO2] at this
    exact le_bot_iff.mp this
  have hffJ : Js = ffJ Js := by
    refine le_antisymm ?_ (B6.ffJ_le Js)
    have hle : conjClosure Bs Hs ≤ ffJ Js := by
      refine conjClosure_le fun h hh b hb => ?_
      have hoff := B1.isFFStarOffender_conjAut hBoff hh
      have hle : B1.conjAut h Bs ≤ Js := by
        intro x hx
        have h1 := hJn h hh _ (hBJ (B1.mem_conjAut.mp hx))
        simpa [mul_assoc] using h1
      have hoffJ : IsFFStarOffender Js (B1.conjAut h Bs) :=
        ⟨hle, hoff.2.1, hoff.2.2.1, hoff.2.2.2⟩
      exact B6.le_ffJ hoffJ (B1.mem_conjAut.mpr (by simpa [mul_assoc] using hb))
    rwa [← hJgen] at hle
  have hB53 : B53Hyp Js :=
    ⟨hO2J, hffJ, ↥Js, inferInstance, inferInstance, ⊥, inferInstance, hSQ,
      ⟨(QuotientGroup.quotientBot).symm⟩⟩
  have hcases := h56 V hV Js hJne hB53
  have hR : ∃ R : Subgroup (MulAut V), IsPGroup 2 R ∧ Bs ≤ R ∧
      ∀ x ∈ Ys ⊔ Ts, ∀ r ∈ R, x * r * x⁻¹ ∈ R :=
    ⟨pCoreOf 2 (Ys ⊔ Ts), pCoreOf_isPGroup 2 _, hBR, fun x hx r hr =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hx) r).mp hr⟩
  rcases b56_components hcases with hs3 | hs33 | ⟨N₁, N₂, hne, hN₁J, hN₂J, hn₁, hn₂, hq₁, hq₂, hall⟩
  · exact (solv_absurd Hs Js Ms Ys Ts Bs hJH hJn hYM hMH hBJ hBoff.2.1 hR hθ hYgen hKL
      (Or.inl hs3)).elim
  · exact (solv_absurd Hs Js Ms Ys Ts Bs hJH hJn hYM hMH hBJ hBoff.2.1 hR hθ hYgen hKL
      (Or.inr hs33)).elim
  · have hns : ¬ Group.IsSolvable ↥Js := by
      rcases hne with h | h
      · rcases hq₁ with h' | ⟨hq, -⟩
        · exact absurd h' h
        · exact comp_not_isSolvable_of_quasisimple hN₁J hq
      · rcases hq₂ with h' | ⟨hq, -⟩
        · exact absurd h' h
        · exact comp_not_isSolvable_of_quasisimple hN₂J hq
    refine ⟨hns, fun K hK => ?_⟩
    have hKne := ne_bot_of_mem_cComp hK
    have hq : CFSG.IsQuasisimple ↥K ∧ B56QuasisimpleList ↥K := by
      rcases hall K hK with rfl | rfl
      · rcases hq₁ with h | h
        · exact absurd h hKne
        · exact h
      · rcases hq₂ with h | h
        · exact absurd h hKne
        · exact h
    have hKJ : K ≤ Js := le_of_mem_cComp hK
    have hnormY : Ys ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
      rw [hYgen]
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hyY, hy3⟩
      exact comp_normalizes_of_two hall hK (hJnorm y (hMH (hYM hyY)))
        (by rw [← hy3]; exact pow_orderOf_eq_one y)
    refine ⟨hnormY, ?_⟩
    have hle : ⁅K, Ys⁆ ≤ K := Subgroup.commutator_le.mpr fun k hk y hy => by
      have hyn := Subgroup.mem_normalizer_iff.mp (hnormY hy) k⁻¹
      have : y * k⁻¹ * y⁻¹ ∈ K := hyn.mp (K.inv_mem hk)
      rw [commutatorElement_def]
      have e : k * y * k⁻¹ * y⁻¹ = k * (y * k⁻¹ * y⁻¹) := by group
      rw [e]
      exact K.mul_mem hk this
    have hnorm : (⁅K, Ys⁆.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff hle).2 fun h k hh hk =>
        (Subgroup.mem_normalizer_iff.mp (A3.le_normalizer_commutator_left K Ys hk) h).mp hh
    rcases A3.eq_top_or_le_center_of_subnormal hq.1 hnorm.isSubnormal with htop | hcen
    · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.1 htop)
    · exfalso
      have hcommz : ∀ z ∈ ⁅K, Ys⁆, ∀ k ∈ K, k * z = z * k := fun z hz k hk => by
        have h1 := Subgroup.mem_center_iff.mp
          (hcen (show (⟨z, hle hz⟩ : ↥K) ∈ ⁅K, Ys⁆.subgroupOf K from hz)) ⟨k, hk⟩
        exact congrArg Subtype.val h1
      have hb1 : ⁅⁅K, Ys⁆, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun z hz =>
        Subgroup.mem_centralizer_iff.mpr fun k hk => hcommz z hz k hk
      have hb2 : ⁅⁅Ys, K⁆, K⁆ = ⊥ := by
        rw [Subgroup.commutator_comm Ys K]
        exact hb1
      have hb3 : ⁅⁅K, K⁆, Ys⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate hb1 hb2
      have hKY0 : ⁅K, Ys⁆ = ⊥ := by
        rw [perfect_of_mem_cComp hK] at hb3
        exact hb3
      have hcomm : ∀ x ∈ K, ∀ y ∈ Ys, x * y = y * x := fun x hx y hy =>
        ((Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKY0 hx) y hy)).symm
      have hKM : K ≤ Ms := hKL K (hKJ.trans hJH) hcomm
      refine noncentral_three_absurd K Ys (perfect_of_mem_cComp hK)
        (three_dvd_card_of_b56QL hq.2 hq.1) (fun x hx h3 k hk => ?_)
        (fun x hx h3 => hθ x (hKM hx) h3) hY3
      exact (hcomm k hk x (hθ x (hKM hx) h3)).symm

end Main

end S153L

end CFSG.Quasithin
