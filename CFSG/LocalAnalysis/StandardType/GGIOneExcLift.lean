module

public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly
open scoped commutatorElement

section Lift

variable {L' : Type} [Group L'] [Finite L'] {R : Type} [Group R]

theorem ggIE_exists_twoSubgroup (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') {U : Subgroup R} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    {E : Subgroup (MulAut L')} (hEU : ∀ a ∈ E, ∀ l : L', ψ l ∈ U → ψ (a l) ∈ U) :
    ∃ T : Subgroup L', T ≠ ⊥ ∧ IsPGroup 2 T ∧ ∀ a ∈ E, ∀ t ∈ T, a t ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite R := Finite.of_surjective ψ hψ
  set H : Subgroup L' := U.comap ψ with hH
  let f : H →* U := (ψ.comp H.subtype).codRestrict U (fun h => h.2)
  have hf : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨⟨l, hr⟩, rfl⟩
  have hker' : f.ker ≤ Subgroup.center H := by
    intro h hh
    have h1 : ψ h = 1 := congrArg Subtype.val hh
    have h2 : (h : L') ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr h1)
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro k
    exact Subtype.ext (h2 k)
  have : Group.IsNilpotent U := hU2.isNilpotent
  have : Group.IsNilpotent H := Subgroup.isNilpotent_of_ker_le_center f hker'
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 H))
  have hPn : (P : Subgroup H).Normal := inferInstance
  have htop : (⊤ : Subgroup U) = (P : Subgroup H).map f := by
    have h := (P.mapSurjective hf).is_maximal' (Q := ⊤)
      (hU2.of_equiv Subgroup.topEquiv.symm) le_top
    rwa [Sylow.coe_mapSurjective] at h
  have hmemP : ∀ h : H, ∀ k : ℕ, h ^ 2 ^ k = 1 → h ∈ (P : Subgroup H) := by
    intro h k hk
    obtain ⟨Q, hQ⟩ := (isPGroup_two_zpowers hk).exists_le_sylow
    have := Sylow.unique_of_normal P hPn
    have hQP : Q = P := Subsingleton.elim Q P
    rw [← hQP]
    exact hQ (Subgroup.mem_zpowers h)
  refine ⟨(P : Subgroup H).map H.subtype, ?_, ?_, ?_⟩
  · intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at hbot
    rw [hbot, Subgroup.map_bot] at htop
    apply hU
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hu⟩ : U) ∈ (⊥ : Subgroup U) := htop ▸ Subgroup.mem_top _
    exact congrArg Subtype.val (Subgroup.mem_bot.mp this)
  · rintro ⟨x, hx⟩
    obtain ⟨h, hP, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨h, hP⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun z : (P : Subgroup H) => ((z : H) : L')) hk
    simpa using this
  · intro a ha t ht
    obtain ⟨h, hP, rfl⟩ := Subgroup.mem_map.mp ht
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨h, hP⟩
    have hk' : (h : H) ^ 2 ^ k = 1 := by
      have := congrArg (fun z : (P : Subgroup H) => ((z : H)) ) hk
      simpa using this
    have hmem : a (h : L') ∈ H := hEU a ha _ h.2
    have hh' : (⟨a (h : L'), hmem⟩ : H) ∈ (P : Subgroup H) := by
      refine hmemP _ k (Subtype.ext ?_)
      show a (h : L') ^ 2 ^ k = 1
      rw [← map_pow, show (h : L') ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk', map_one]
    exact Subgroup.mem_map.mpr ⟨_, hh', rfl⟩

theorem ggIE_false_of_noTwoBetween {A As : Subgroup (MulAut L')} (hA : A < As)
    (hnone : GGNoTwoBetween A As) (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') {U : Subgroup R} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hEU : ∀ a ∈ As, ∀ l : L', ψ l ∈ U → ψ (a l) ∈ U) : False := by
  obtain ⟨T, hT, hT2, hTA⟩ := ggIE_exists_twoSubgroup ψ hψ hker hU hU2 hEU
  exact hT (hnone As hA le_rfl T hT2 hTA)

end Lift

section Induced

variable {L' : Type} [Group L'] [Finite L'] {R : Type} [Group R]

theorem ggIE_center_le_ker {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hZ : Subgroup.center R = ⊥) : Subgroup.center L' ≤ ψ.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hr : ψ z ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) l]
  rw [hZ, Subgroup.mem_bot] at hr
  exact hr

theorem ggIE_ker_eq_center {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hZ : Subgroup.center R = ⊥) (hker : ψ.ker ≤ Subgroup.center L') :
    ψ.ker = Subgroup.center L' :=
  le_antisymm hker (ggIE_center_le_ker hψ hZ)

theorem ggIE_map_ker (ψ : L' →* R) (hψ : Function.Surjective ψ) (hZ : Subgroup.center R = ⊥)
    (hker : ψ.ker ≤ Subgroup.center L') (a : MulAut L') :
    ψ.ker.map (a : L' →* L') = ψ.ker := by
  rw [ggIE_ker_eq_center hψ hZ hker]
  exact Subgroup.map_center_eq a

@[expose] noncomputable def ggIE_indAut {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hZ : Subgroup.center R = ⊥) (hker : ψ.ker ≤ Subgroup.center L') (a : MulAut L') :
    MulAut R :=
  (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    ((QuotientGroup.congr ψ.ker ψ.ker a (ggIE_map_ker ψ hψ hZ hker a)).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))

theorem ggIE_indAut_apply {ψ : L' →* R} (hψ : Function.Surjective ψ) (hZ : Subgroup.center R = ⊥)
    (hker : ψ.ker ≤ Subgroup.center L') (a : MulAut L') (l : L') :
    ggIE_indAut hψ hZ hker a (ψ l) = ψ (a l) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ l) =
      (QuotientGroup.mk l : L' ⧸ ψ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  unfold ggIE_indAut
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
  rfl

theorem ggIE_eq_indAut_of_forall {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hZ : Subgroup.center R = ⊥) (hker : ψ.ker ≤ Subgroup.center L') {a : MulAut L'}
    {φ : MulAut R} (h : ∀ l : L', φ (ψ l) = ψ (a l)) : φ = ggIE_indAut hψ hZ hker a := by
  ext r
  obtain ⟨l, rfl⟩ := hψ r
  rw [ggIE_indAut_apply, h]

@[expose] noncomputable def ggIE_indAutHom {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hZ : Subgroup.center R = ⊥) (hker : ψ.ker ≤ Subgroup.center L') :
    MulAut L' →* MulAut R where
  toFun := ggIE_indAut hψ hZ hker
  map_one' := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [ggIE_indAut_apply]
    rfl
  map_mul' a b := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [MulAut.mul_apply, ggIE_indAut_apply, ggIE_indAut_apply, ggIE_indAut_apply, MulAut.mul_apply]

theorem ggIE_eq_one_of_indAut {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hZ : Subgroup.center R = ⊥) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {a : MulAut L'} (ha : ggIE_indAut hψ hZ hker a = 1) : a = 1 := by
  have hψa : ∀ l, ψ (a l) = ψ l := fun l => by
    have h := ggIE_indAut_apply hψ hZ hker a l
    rw [ha, MulAut.one_apply] at h
    exact h.symm
  have hcen : ∀ l, a l * l⁻¹ ∈ Subgroup.center L' := fun l =>
    hker (MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hψa l, mul_inv_cancel]))
  have hmul : ∀ x y : L', a (x * y) * (x * y)⁻¹ = (a x * x⁻¹) * (a y * y⁻¹) := by
    intro x y
    have h1 := Subgroup.mem_center_iff.mp (hcen y) (a x)
    have h2 := Subgroup.mem_center_iff.mp (hcen x) (a y * y⁻¹)
    calc a (x * y) * (x * y)⁻¹ = a x * (a y * y⁻¹) * x⁻¹ := by rw [map_mul]; group
      _ = (a y * y⁻¹) * a x * x⁻¹ := by rw [h1]
      _ = (a y * y⁻¹) * (a x * x⁻¹) := by rw [mul_assoc]
      _ = (a x * x⁻¹) * (a y * y⁻¹) := h2
  let S : Subgroup L' :=
    { carrier := {l | a l * l⁻¹ = 1}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [hmul, hx, hy, one_mul]
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        have h := hmul x x⁻¹
        rw [mul_inv_cancel, map_one, inv_one, mul_one, hx, one_mul] at h
        exact h.symm }
  have hGinv : ∀ x : L', a x⁻¹ * x⁻¹⁻¹ = (a x * x⁻¹)⁻¹ := by
    intro x
    have h := hmul x x⁻¹
    rw [mul_inv_cancel, map_one, inv_one, mul_one] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hcomm_elt : ∀ x y : L', a ⁅x, y⁆ * ⁅x, y⁆⁻¹ = 1 := by
    intro x y
    have hcxy : (a y * y⁻¹) * (a x * x⁻¹) = (a x * x⁻¹) * (a y * y⁻¹) :=
      Subgroup.mem_center_iff.mp (hcen x) (a y * y⁻¹)
    rw [commutatorElement_def, hmul, hmul, hmul, hGinv, hGinv]
    calc a x * x⁻¹ * (a y * y⁻¹) * (a x * x⁻¹)⁻¹ * (a y * y⁻¹)⁻¹
        = (a y * y⁻¹) * (a x * x⁻¹) * (a x * x⁻¹)⁻¹ * (a y * y⁻¹)⁻¹ := by rw [hcxy]
      _ = 1 := by group
  have hle : commutator L' ≤ S := by
    show ⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ ≤ S
    exact Subgroup.commutator_le.mpr fun x _ y _ => hcomm_elt x y
  have hall : ∀ l : L', a l * l⁻¹ = 1 := by
    intro l
    have htop : (⊤ : Subgroup L') ≤ S := by rw [← hperf]; exact hle
    exact htop (Subgroup.mem_top l)
  ext l
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp (hall l)

theorem ggIE_indAutHom_injective {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hZ : Subgroup.center R = ⊥) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) : Function.Injective (ggIE_indAutHom hψ hZ hker) :=
  (injective_iff_map_eq_one (ggIE_indAutHom hψ hZ hker)).mpr fun a ha =>
    ggIE_eq_one_of_indAut hψ hZ hker hperf ha

theorem ggIE_isElemAbelian_map {p : ℕ} {G H : Type*} [Group G] [Group H] (f : G →* H)
    {E : Subgroup G} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  have hr : E.map f = (f.comp E.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hr]
  exact isElemAbelian_range
    (fun x y => Subtype.ext (CFSG.StandardType.TableB.IsElemAbelian.comm hE x.2 y.2))
    (fun x => Subtype.ext (by simpa using hE.2 x x.2)) _

theorem ggIE_mul_card_le {p : ℕ} (hp : p.Prime) {A As : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hAs : IsElemAbelian p As) (hlt : A < As) :
    p * Nat.card A ≤ Nat.card As := by
  have : Fact p.Prime := ⟨hp⟩
  have hPA : IsPGroup p A := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hA.2 _ g.2)⟩
  have hPAs : IsPGroup p As := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hAs.2 _ g.2)⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hPA
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hPAs
  have hdvd : Nat.card A ∣ Nat.card As := Subgroup.card_dvd_of_le hlt.le
  have hlt' : Nat.card A < Nat.card As := Subgroup.card_lt_of_lt hlt
  rw [ha, hb] at hdvd hlt' ⊢
  have hab : a ≤ b := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  have hab' : a < b := lt_of_le_of_ne hab fun h => by
    rw [h] at hlt'
    exact lt_irrefl _ hlt'
  calc p * p ^ a = p ^ (a + 1) := (pow_succ' p a).symm
    _ ≤ p ^ b := Nat.pow_le_pow_right hp.pos hab'

theorem ggIE_endNodeIOne_of_bounds {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hZ : Subgroup.center R = ⊥)
    (hB : (∃ φ : MulAut R, φ ^ p = 1 ∧ φ ∉ I) → GGInnerDiagBound p r R I)
    (hT : ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E →
      p ^ (r + 1) ≤ Nat.card E → ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧
        ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U) :
    GGEndNodeIOne p r R I := by
  intro L' _ _ ψ hψ hker hperf A As hA hAAs hAs hcard hAI hr h3 _ hnone
  have hinj : Function.Injective (ggIE_indAutHom hψ hZ hker) :=
    ggIE_indAutHom_injective hψ hZ hker hperf
  have hEbA : IsElemAbelian p (A.map (ggIE_indAutHom hψ hZ hker)) := ggIE_isElemAbelian_map _ hA
  have hEhA : IsElemAbelian p (As.map (ggIE_indAutHom hψ hZ hker)) :=
    ggIE_isElemAbelian_map _ hAs
  have hEbEh : A.map (ggIE_indAutHom hψ hZ hker) ≤ As.map (ggIE_indAutHom hψ hZ hker) :=
    Subgroup.map_mono hAAs.le
  have hcardb : Nat.card (A.map (ggIE_indAutHom hψ hZ hker)) = Nat.card A :=
    Subgroup.card_map_of_injective hinj
  have hcardh : Nat.card (As.map (ggIE_indAutHom hψ hZ hker)) = Nat.card As :=
    Subgroup.card_map_of_injective hinj
  have hcardle : Nat.card (As.map (ggIE_indAutHom hψ hZ hker)) ≤
      p * Nat.card (A.map (ggIE_indAutHom hψ hZ hker)) := by
    rw [hcardh, hcardb]
    exact hcard
  have hEbI : ((A.map (ggIE_indAutHom hψ hZ hker) : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hφa := ggIE_eq_indAut_of_forall hψ hZ hker hφ
    show ggIE_indAut hψ hZ hker a ∈ I
    rw [← hφa]
    exact hφI
  by_cases hInn : ∀ a ∈ As, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)
  · have hEhI : ((As.map (ggIE_indAutHom hψ hZ hker) : Subgroup (MulAut R)) :
        Set (MulAut R)) ⊆ I := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨φ, hφI, hφ⟩ := hInn a ha
      have hφa := ggIE_eq_indAut_of_forall hψ hZ hker hφ
      show ggIE_indAut hψ hZ hker a ∈ I
      rw [← hφa]
      exact hφI
    have hbig : p ^ (r + 1) ≤ Nat.card (As.map (ggIE_indAutHom hψ hZ hker)) := by
      rw [hcardh, pow_succ]
      calc p ^ r * p = p * p ^ r := mul_comm _ _
        _ ≤ p * Nat.card A := Nat.mul_le_mul_left p hr
        _ ≤ Nat.card As := ggIE_mul_card_le hp hA hAs hAAs
    obtain ⟨U, hU1, hU2, hUE⟩ := hT _ hEhI hEhA hbig
    refine (ggIE_false_of_noTwoBetween hAAs hnone ψ hψ hker hU1 hU2
      (fun a ha l hl => ?_)).elim
    have h1 := hUE (ggIE_indAutHom hψ hZ hker a) (Subgroup.mem_map_of_mem _ ha) (ψ l) hl
    have h2 : ggIE_indAutHom hψ hZ hker a (ψ l) = ψ (a l) := ggIE_indAut_apply hψ hZ hker a l
    rwa [h2] at h1
  · push Not at hInn
    obtain ⟨a₀, ha₀, hnI⟩ := hInn
    have hρI : ggIE_indAutHom hψ hZ hker a₀ ∉ I := fun h => by
      obtain ⟨l, hl⟩ := hnI _ h
      exact hl (ggIE_indAut_apply hψ hZ hker a₀ l)
    have hpow : ggIE_indAutHom hψ hZ hker a₀ ^ p = 1 := by
      rw [← map_pow, hAs.2 a₀ ha₀, map_one]
    have hnotI : ¬ ((As.map (ggIE_indAutHom hψ hZ hker) : Subgroup (MulAut R)) :
        Set (MulAut R)) ⊆ I :=
      fun hsub => hρI (hsub (Subgroup.mem_map_of_mem _ ha₀))
    obtain ⟨U, hU1, hU2, hUE⟩ := hB ⟨_, hpow, hρI⟩ _ _ hEbI hEbA
      (by rw [hcardb]; exact hr) (by rw [hcardb]; exact h3) hEbEh hEhA hcardle hnotI
    refine (ggIE_false_of_noTwoBetween hAAs hnone ψ hψ hker hU1 hU2
      (fun a ha l hl => ?_)).elim
    have h1 := hUE (ggIE_indAutHom hψ hZ hker a) (Subgroup.mem_map_of_mem _ ha) (ψ l) hl
    have h2 : ggIE_indAutHom hψ hZ hker a (ψ l) = ψ (a l) := ggIE_indAut_apply hψ hZ hker a l
    rwa [h2] at h1

end Induced

end CFSG.StandardType
