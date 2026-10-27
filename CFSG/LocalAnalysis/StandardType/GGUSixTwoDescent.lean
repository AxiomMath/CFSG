module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofLift
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.StandardType CFSG.StandardType.Line63 CFSG.StandardType.Line63.H5

section Basic

variable {L' : Type} [Group L'] [Finite L']

@[expose] def zTwo (L' : Type) [Group L'] [Finite L'] : Subgroup L' where
  carrier := {z | z ∈ Subgroup.center L' ∧ z ^ (2 ^ Nat.card L') = 1}
  one_mem' := ⟨Subgroup.one_mem _, one_pow _⟩
  mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
    rw [Commute.mul_pow (Subgroup.mem_center_iff.mp hy.1 x), hx.2, hy.2, one_mul]⟩
  inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem zTwo_le_center : zTwo L' ≤ Subgroup.center L' := fun _ hz => hz.1

theorem zTwo_comm {z : L'} (hz : z ∈ zTwo L') (g : L') : g * z = z * g :=
  Subgroup.mem_center_iff.mp hz.1 g

theorem isPGroup_zTwo : IsPGroup 2 (zTwo L') :=
  fun z => ⟨Nat.card L', Subtype.ext z.2.2⟩

instance zTwo_normal : (zTwo L').Normal :=
  ⟨fun y hy g => by rw [zTwo_comm hy g, mul_inv_cancel_right]; exact hy⟩

theorem zTwo_invariant (a : MulAut L') {z : L'} (hz : z ∈ zTwo L') : a z ∈ zTwo L' := by
  refine ⟨?_, by rw [← map_pow, hz.2, map_one]⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have h := zTwo_comm hz (a⁻¹ g)
  have h2 := congrArg a h
  rw [map_mul, map_mul, MulAut.apply_inv_self] at h2
  exact h2

theorem zTwo_map_eq (a : MulAut L') : (zTwo L').map a.toMonoidHom = zTwo L' := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact zTwo_invariant a hz
  · intro z hz
    refine ⟨a⁻¹ z, zTwo_invariant a⁻¹ hz, ?_⟩
    simp

abbrev Qt (L' : Type) [Group L'] [Finite L'] : Type := L' ⧸ zTwo L'

@[expose] def qmk (L' : Type) [Group L'] [Finite L'] : L' →* Qt L' :=
  QuotientGroup.mk' (zTwo L')

theorem qmk_eq_one_iff {l : L'} : qmk L' l = 1 ↔ l ∈ zTwo L' := QuotientGroup.eq_one_iff l

theorem qmk_surjective : Function.Surjective (qmk L') := QuotientGroup.mk'_surjective _

theorem qmk_ker_le_center : (qmk L').ker ≤ Subgroup.center L' := by
  intro x hx
  exact zTwo_le_center ((qmk_eq_one_iff).mp (MonoidHom.mem_ker.mp hx))

@[expose] def qAut (a : MulAut L') : MulAut (Qt L') :=
  QuotientGroup.congr (zTwo L') (zTwo L') a (zTwo_map_eq a)

theorem qAut_mk (a : MulAut L') (l : L') : qAut a (qmk L' l) = qmk L' (a l) :=
  QuotientGroup.congr_mk _ _ _ _ l

@[expose] def qAutHom (L' : Type) [Group L'] [Finite L'] : MulAut L' →* MulAut (Qt L') where
  toFun := qAut
  map_one' := by
    ext x
    obtain ⟨l, rfl⟩ := qmk_surjective x
    rw [qAut_mk]
    rfl
  map_mul' := fun a b => by
    ext x
    obtain ⟨l, rfl⟩ := qmk_surjective x
    simp only [MulAut.mul_apply, qAut_mk]

theorem qAutHom_mk (a : MulAut L') (l : L') : qAutHom L' a (qmk L' l) = qmk L' (a l) :=
  qAut_mk a l

theorem qAutHom_injective (hperf : commutator L' = ⊤) :
    Function.Injective (qAutHom L') := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hfixl : ∀ l : L', l⁻¹ * a l ∈ zTwo L' := by
    intro l
    have h := qAutHom_mk a l
    rw [ha, MulAut.one_apply] at h
    rw [← qmk_eq_one_iff, map_mul, map_inv, ← h, inv_mul_cancel]
  letI : CommGroup (zTwo L') :=
    { (inferInstance : Group (zTwo L')) with
      mul_comm := fun x y => Subtype.ext (zTwo_comm x.2 y).symm }
  let f : L' →* zTwo L' :=
    { toFun := fun l => ⟨l⁻¹ * a l, hfixl l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun l m => Subtype.ext (by
        show (l * m)⁻¹ * a (l * m) = l⁻¹ * a l * (m⁻¹ * a m)
        have hc := zTwo_comm (hfixl l) m⁻¹
        calc (l * m)⁻¹ * a (l * m) = m⁻¹ * (l⁻¹ * a l) * a m := by rw [map_mul]; group
          _ = (l⁻¹ * a l) * m⁻¹ * a m := by rw [hc]
          _ = l⁻¹ * a l * (m⁻¹ * a m) := by group) }
  have hf : ∀ l, f l = 1 := fun l =>
    Abelianization.commutator_subset_ker f (by rw [hperf]; exact Subgroup.mem_top l)
  ext l
  have h1 : l⁻¹ * a l = 1 := congrArg Subtype.val (hf l)
  exact (inv_mul_eq_one.mp h1).symm

end Basic

section Ext

variable {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}

theorem zTwo_le_ker (hψ : Function.Surjective ψ) (hcenR : Subgroup.center R = ⊥) :
    zTwo L' ≤ ψ.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hmem : ψ z ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    rw [← map_mul, ← map_mul, zTwo_comm hz l]
  rw [hcenR] at hmem
  exact Subgroup.mem_bot.mp hmem

@[expose] def qLift (ψ : L' →* R) (h : zTwo L' ≤ ψ.ker) : Qt L' →* R :=
  QuotientGroup.lift (zTwo L') ψ h

theorem qLift_mk (h : zTwo L' ≤ ψ.ker) (l : L') : qLift ψ h (qmk L' l) = ψ l :=
  QuotientGroup.lift_mk _ _ _

theorem qLift_surjective (h : zTwo L' ≤ ψ.ker) (hψ : Function.Surjective ψ) :
    Function.Surjective (qLift ψ h) := fun r => by
  obtain ⟨l, rfl⟩ := hψ r
  exact ⟨qmk L' l, qLift_mk h l⟩

theorem qLift_ker_le_center (h : zTwo L' ≤ ψ.ker) (hker : ψ.ker ≤ Subgroup.center L') :
    (qLift ψ h).ker ≤ Subgroup.center (Qt L') := by
  intro x hx
  obtain ⟨l, rfl⟩ := qmk_surjective x
  have hl : l ∈ ψ.ker := by rw [MonoidHom.mem_ker, ← qLift_mk h]; exact hx
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g, rfl⟩ := qmk_surjective g
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hker hl) g]

theorem qmk_perfect (hperf : commutator L' = ⊤) : commutator (Qt L') = ⊤ := by
  have : (commutator L').map (qmk L') = commutator (Qt L') := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ qmk_surjective]
  rw [← this, hperf, Subgroup.map_top_of_surjective _ qmk_surjective]

theorem qLift_odd_ker (h : zTwo L' ≤ ψ.ker) (hker : ψ.ker ≤ Subgroup.center L') :
    Odd (Nat.card (qLift ψ h).ker) := by
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hne)
  obtain ⟨l, hl⟩ := qmk_surjective x.1
  have hx2 : x.1 ^ 2 = 1 := by
    have := congrArg Subtype.val (pow_orderOf_eq_one x)
    rw [hx] at this
    simpa using this
  have hl2 : l ^ 2 ∈ zTwo L' := by
    rw [← qmk_eq_one_iff, map_pow, hl, hx2]
  have hlker : l ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, ← qLift_mk h, hl]
    exact x.2
  have hlZ : l ∈ zTwo L' := ⟨hker hlker, pow_two_pow_card l (j := Nat.card L' + 1)
    (by rw [pow_succ, pow_mul', hl2.2])⟩
  have : x = 1 := Subtype.ext (by rw [← hl]; exact (qmk_eq_one_iff).mpr hlZ)
  rw [this, orderOf_one] at hx
  norm_num at hx

theorem qLift_qAut (h : zTwo L' ≤ ψ.ker) (a : MulAut L') (x : MulAut R)
    (hx : ∀ l : L', x (ψ l) = ψ (a l)) (lb : Qt L') :
    x (qLift ψ h lb) = qLift ψ h (qAutHom L' a lb) := by
  obtain ⟨l, rfl⟩ := qmk_surjective lb
  rw [qLift_mk, qAutHom_mk, qLift_mk, hx]

theorem qAutHom_conj (l : L') :
    qAutHom L' (MulAut.conj l) = MulAut.conj (qmk L' l) := by
  ext x
  obtain ⟨y, rfl⟩ := qmk_surjective x
  rw [qAutHom_mk]
  simp only [MulAut.conj_apply, map_mul, map_inv]

end Ext

section Lift

variable {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}

theorem exists_fixed_lift_mem (hA3 : IsPGroup 3 A) {H : Subgroup L'}
    (hH : ∀ a ∈ A, ∀ h ∈ H, a h ∈ H) {xb : Qt L'} (hxb : xb ∈ H.map (qmk L'))
    (hfix : ∀ a ∈ A, qAutHom L' a xb = xb) :
    ∃ x ∈ H, qmk L' x = xb ∧ ∀ a ∈ A, a x = x := by
  obtain ⟨x₀, hx₀H, rfl⟩ := hxb
  set Y : Subgroup L' := H ⊓ zTwo L' with hY
  have hYc : Y ≤ Subgroup.center L' := fun y hy => zTwo_le_center hy.2
  have hY2 : IsPGroup 2 Y := isPGroup_zTwo.to_le inf_le_right
  have hYA : ∀ a ∈ A, ∀ y ∈ Y, a y ∈ Y := fun a ha y hy =>
    ⟨hH a ha y hy.1, zTwo_invariant a hy.2⟩
  have hT3 : IsPGroup 3 (⊥ : Subgroup L') := fun g => ⟨0, Subsingleton.elim _ _⟩
  have hTA : ∀ a ∈ A, ∀ t ∈ (⊥ : Subgroup L'), a t = t := fun a _ t ht => by
    rw [Subgroup.mem_bot] at ht
    rw [ht, map_one]
  have hn₀ : ∀ a ∈ A, x₀ * (a x₀)⁻¹ ∈ (⊥ : Subgroup L') ⊔ Y := by
    intro a ha
    refine Subgroup.mem_sup_right ?_
    have h1 : qmk L' (a x₀) = qmk L' x₀ := by
      rw [← qAutHom_mk]
      exact hfix a ha
    have hc : x₀⁻¹ * a x₀ ∈ zTwo L' := by
      rw [← qmk_eq_one_iff, map_mul, map_inv, h1, inv_mul_cancel]
    have hcY : x₀⁻¹ * a x₀ ∈ Y := ⟨H.mul_mem (H.inv_mem hx₀H) (hH a ha x₀ hx₀H), hc⟩
    have hz' : a x₀ = x₀ * (x₀⁻¹ * a x₀) := by group
    have e : x₀ * (a x₀)⁻¹ = (x₀⁻¹ * a x₀)⁻¹ := by
      calc x₀ * (a x₀)⁻¹ = x₀ * (x₀ * (x₀⁻¹ * a x₀))⁻¹ := by rw [← hz']
        _ = (x₀ * (x₀⁻¹ * a x₀)⁻¹) * x₀⁻¹ := by group
        _ = ((x₀⁻¹ * a x₀)⁻¹ * x₀) * x₀⁻¹ := by
          rw [zTwo_comm ((zTwo L').inv_mem hc) x₀]
        _ = (x₀⁻¹ * a x₀)⁻¹ := by group
    rw [e]
    exact Y.inv_mem hcY
  obtain ⟨z, hz, hzT⟩ := exists_lift_weyl hYc hY2 hT3 hA3 hYA hTA x₀ hn₀
  refine ⟨x₀ * z, H.mul_mem hx₀H hz.1, ?_, fun a ha => ?_⟩
  · rw [map_mul, (qmk_eq_one_iff).mpr hz.2, mul_one]
  · have h1 := hzT a ha
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1.symm

theorem exists_fixed_cube_lift (hA3 : IsPGroup 3 A) {H : Subgroup L'}
    (hH : ∀ a ∈ A, ∀ h ∈ H, a h ∈ H) {xb : Qt L'} (hxb : xb ∈ H.map (qmk L'))
    (hfix : ∀ a ∈ A, qAutHom L' a xb = xb) (hx3 : xb ^ 3 = 1) :
    ∃ x ∈ H, qmk L' x = xb ∧ x ^ 3 = 1 ∧ ∀ a ∈ A, a x = x := by
  obtain ⟨x₁, hx₁H, hx₁, hx₁fix⟩ := exists_fixed_lift_mem hA3 hH hxb hfix
  set m : ℕ := 4 ^ Nat.card L' with hm
  have hm3 : m % 3 = 1 := by
    rw [hm, Nat.pow_mod]
    norm_num
  have h13 : x₁ ^ 3 ∈ zTwo L' := by
    rw [← qmk_eq_one_iff, map_pow, hx₁, hx3]
  have hmx : (x₁ ^ 3) ^ m = 1 := by
    rw [hm, show (4 : ℕ) = 2 * 2 by norm_num, mul_pow, pow_mul, h13.2, one_pow]
  obtain ⟨k, hk⟩ : ∃ k, m = 3 * k + 1 := ⟨m / 3, by omega⟩
  refine ⟨x₁ ^ m, H.pow_mem hx₁H m, ?_, ?_, fun a ha => by rw [map_pow, hx₁fix a ha]⟩
  · rw [map_pow, hx₁, hk, pow_succ, pow_mul, hx3, one_pow, one_mul]
  · rw [← pow_mul, mul_comm, pow_mul, hmx]

theorem ggTorusSelfCent_descent {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} (hA3 : IsPGroup 3 A) (hsc : GGTorusSelfCent 3 A) :
    GGTorusSelfCent 3 (A.map (qAutHom L')) := by
  intro q hfix hq3
  obtain ⟨n, -, hnq, hn3, hnfix⟩ := exists_fixed_cube_lift hA3 (H := ⊤)
    (fun a _ _ _ => Subgroup.mem_top _)
    (by rw [Subgroup.map_top_of_surjective _ qmk_surjective]; exact Subgroup.mem_top q)
    (fun a ha => hfix _ ⟨a, ha, rfl⟩) hq3
  refine ⟨MulAut.conj n, hsc n hnfix hn3, ?_⟩
  rw [qAutHom_conj, hnq]

@[expose] def fixIn (A : Subgroup (MulAut L')) (H : Subgroup L') : Subgroup L' where
  carrier := {x | x ∈ H ∧ ∀ a ∈ A, a x = x}
  one_mem' := ⟨H.one_mem, fun a _ => map_one a⟩
  mul_mem' := fun {x y} hx hy => ⟨H.mul_mem hx.1 hy.1, fun a ha => by
    rw [map_mul, hx.2 a ha, hy.2 a ha]⟩
  inv_mem' := fun {x} hx => ⟨H.inv_mem hx.1, fun a ha => by rw [map_inv, hx.2 a ha]⟩

theorem exists_elemAbelian_lift_fixed (hA3 : IsPGroup 3 A) {H : Subgroup L'}
    (hH : ∀ a ∈ A, ∀ h ∈ H, a h ∈ H) {Eb : Subgroup (Qt L')}
    (hEb : CFSG.Open.IsElemAbelian 3 Eb) (hEbH : Eb ≤ H.map (qmk L'))
    (hfix : ∀ a ∈ A, ∀ x ∈ Eb, qAutHom L' a x = x) :
    ∃ E : Subgroup L', E ≤ H ∧ CFSG.Open.IsElemAbelian 3 E ∧ E.map (qmk L') = Eb ∧
      (∀ a ∈ A, ∀ e ∈ E, a e = e) ∧ Nat.card E = Nat.card Eb := by
  set πA : ↥(fixIn A H) →* Qt L' := (qmk L').comp (fixIn A H).subtype with hπA
  have hker : IsPGroup 2 πA.ker := by
    intro g
    have h1 : ((g : ↥(fixIn A H)) : L') ∈ zTwo L' := by
      have := MonoidHom.mem_ker.mp g.2
      exact (qmk_eq_one_iff).mp this
    refine ⟨Nat.card L', Subtype.ext (Subtype.ext ?_)⟩
    simpa using h1.2
  have hEb3 : IsPGroup 3 Eb := isPGroup_three_of_isElemAbelian hEb
  have hr : Eb ≤ πA.range := by
    intro xb hxb
    obtain ⟨x, hxH, hx, hxfix⟩ := exists_fixed_lift_mem hA3 hH (hEbH hxb) (hfix · · xb hxb)
    exact ⟨⟨x, hxH, hxfix⟩, hx⟩
  obtain ⟨S, -, hS3, hSmap, hSinj⟩ := exists_sylow_lift πA hker hEb3 hr
    (B := ⊥) (fun g => ⟨0, Subsingleton.elim _ _⟩)
    (by rw [Subgroup.map_bot]; exact bot_le)
  set E : Subgroup L' := S.map (fixIn A H).subtype with hE
  have hEmap : E.map (qmk L') = Eb := by
    rw [hE, Subgroup.map_map]
    exact hSmap
  have hEmem : ∀ e ∈ E, ∃ s ∈ S, ((s : ↥(fixIn A H)) : L') = e := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  have hinjE : ∀ e ∈ E, qmk L' e = 1 → e = 1 := by
    intro e he h1
    obtain ⟨s, hs, rfl⟩ := hEmem e he
    have : s = 1 := hSinj s hs h1
    rw [this]
    rfl
  have hEEb : ∀ e ∈ E, qmk L' e ∈ Eb := fun e he => by
    rw [← hEmap]
    exact ⟨e, he, rfl⟩
  refine ⟨E, fun e he => ?_, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, hEmap, fun a ha e he => ?_, ?_⟩
  · obtain ⟨s, -, rfl⟩ := hEmem e he
    exact s.2.1
  · apply Subtype.ext
    show (x : L') * y = y * x
    have hcomm : qmk L' (x * y) = qmk L' (y * x) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hEb.1.is_comm.comm ⟨_, hEEb x x.2⟩ ⟨_, hEEb y y.2⟩)
    have hmem : ((y : L') * x)⁻¹ * (x * y) ∈ E :=
      E.mul_mem (E.inv_mem (E.mul_mem y.2 x.2)) (E.mul_mem x.2 y.2)
    have h1 : qmk L' (((y : L') * x)⁻¹ * (x * y)) = 1 := by
      rw [map_mul, map_inv, hcomm, inv_mul_cancel]
    exact (inv_mul_eq_one.mp (hinjE _ hmem h1)).symm
  · exact hinjE _ (E.pow_mem hx 3) (by rw [map_pow]; exact hEb.2 _ (hEEb x hx))
  · obtain ⟨s, -, rfl⟩ := hEmem e he
    exact s.2.2 a ha
  · refine Nat.card_congr (Equiv.ofBijective (fun e : E => (⟨qmk L' e, hEEb e e.2⟩ : Eb))
      ⟨fun e e' h => ?_, fun xb => ?_⟩)
    · have h2 : qmk L' (e : L') = qmk L' (e' : L') := congrArg Subtype.val h
      have hmem : (e : L')⁻¹ * (e' : L') ∈ E := E.mul_mem (E.inv_mem e.2) e'.2
      have h1 : qmk L' ((e : L')⁻¹ * (e' : L')) = 1 := by
        rw [map_mul, map_inv, h2, inv_mul_cancel]
      exact Subtype.ext (inv_mul_eq_one.mp (hinjE _ hmem h1))
    · have hx : (xb : Qt L') ∈ E.map (qmk L') := by rw [hEmap]; exact xb.2
      obtain ⟨e, he, hee⟩ := hx
      exact ⟨⟨e, he⟩, Subtype.ext hee⟩

theorem isPGroup_two_inf_comap {Ub : Subgroup (Qt L')} (hU : IsPGroup 2 Ub) (H : Subgroup L') :
    IsPGroup 2 ↥(H ⊓ Ub.comap (qmk L')) := by
  rintro ⟨x, hxH, hxU⟩
  obtain ⟨k, hk⟩ := hU ⟨qmk L' x, hxU⟩
  have hk' : (qmk L' x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h1 : x ^ 2 ^ k ∈ zTwo L' := by
    rw [← qmk_eq_one_iff, map_pow]
    exact hk'
  refine ⟨k + Nat.card L', Subtype.ext ?_⟩
  show x ^ 2 ^ (k + Nat.card L') = 1
  rw [pow_add, pow_mul]
  exact h1.2

theorem exists_elemAbelian_lift (Eb : Subgroup (Qt L')) (hEb : CFSG.Open.IsElemAbelian 3 Eb) :
    ∃ E : Subgroup L', CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = Nat.card Eb := by
  obtain ⟨E, -, hE, -, -, hc⟩ := exists_elemAbelian_lift_fixed (A := (⊥ : Subgroup (MulAut L')))
    (fun g => ⟨0, Subsingleton.elim _ _⟩) (H := ⊤) (fun a _ h _ => Subgroup.mem_top _) hEb
    (by rw [Subgroup.map_top_of_surjective _ qmk_surjective]; exact le_top)
    (fun a ha x _ => by rw [Subgroup.mem_bot.mp ha, map_one]; rfl)
  exact ⟨E, hE, hc⟩

end Lift

section Delta

variable {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}

theorem qAutHom_not_mem_range_conj (hperf : commutator L' = ⊤) {a : MulAut L'}
    (ha : a ∉ (MulAut.conj : L' →* MulAut L').range) :
    qAutHom L' a ∉ (MulAut.conj : Qt L' →* MulAut (Qt L')).range := by
  rintro ⟨lb, hlb⟩
  obtain ⟨l, rfl⟩ := qmk_surjective lb
  apply ha
  refine ⟨l, qAutHom_injective hperf ?_⟩
  rw [qAutHom_conj]
  exact hlb

theorem three_dvd_orderOf_qmk {x : L'} (h : 3 ∣ orderOf x) : 3 ∣ orderOf (qmk L' x) := by
  set m := orderOf (qmk L' x) with hm
  have h1 : x ^ m ∈ zTwo L' := by
    rw [← qmk_eq_one_iff, map_pow]
    exact pow_orderOf_eq_one _
  have h2 : x ^ (m * 2 ^ Nat.card L') = 1 := by
    rw [pow_mul]
    exact h1.2
  have h4 : 3 ∣ m * 2 ^ Nat.card L' := h.trans (orderOf_dvd_of_pow_eq_one h2)
  exact Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 3 2)) h4

theorem ggDeltaAdm_descent (hperf : commutator L' = ⊤) (hA : CFSG.Open.IsElemAbelian 3 A)
    (hadm : GGDeltaAdm 3 L' A) : GGDeltaAdm 3 (Qt L') (A.map (qAutHom L')) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 A := isPGroup_three_of_isElemAbelian hA
  have hcard : Nat.card (A.map (qAutHom L')) = Nat.card A :=
    Subgroup.card_map_of_injective (qAutHom_injective hperf)
  refine ⟨fun eb he3 hfix => ?_, ?_⟩
  · obtain ⟨e, -, he, he3', hefix⟩ := exists_fixed_cube_lift hA3 (H := ⊤)
      (fun a _ h _ => Subgroup.mem_top _) (xb := eb)
      (by rw [Subgroup.map_top_of_surjective _ qmk_surjective]; exact Subgroup.mem_top _)
      (fun a ha => hfix _ ⟨a, ha, rfl⟩) he3
    refine ⟨MulAut.conj e, hadm.1 e he3' hefix, ?_⟩
    rw [qAutHom_conj, he]
  · rcases hadm.2 with ⟨⟨a, ha, hna⟩, hbound⟩ | ⟨hZ, hbound, hex⟩
    · refine Or.inl ⟨⟨qAutHom L' a, ⟨a, ha, rfl⟩, qAutHom_not_mem_range_conj hperf hna⟩,
        fun Eb hEb => ?_⟩
      obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_lift Eb hEb
      rw [← hEc, hcard]
      exact hbound E hE
    · refine Or.inr ⟨?_, fun Eb hEb => ?_, ?_⟩
      · obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center L')) 3 hZ
        have hzo : orderOf (z : L') = 3 := by rw [Subgroup.orderOf_coe]; exact hz
        have hzc : (z : L') ∈ Subgroup.center L' := z.2
        have hw3 : (qmk L' (z : L')) ^ 3 = 1 := by
          rw [← map_pow, ← hzo, pow_orderOf_eq_one, map_one]
        have hw1 : qmk L' (z : L') ≠ 1 := by
          intro h1
          have hzZ : (z : L') ∈ zTwo L' := (qmk_eq_one_iff).mp h1
          have h2 : orderOf (z : L') ∣ 2 ^ Nat.card L' := orderOf_dvd_of_pow_eq_one hzZ.2
          rw [hzo] at h2
          have h3 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
          omega
        have hwo : orderOf (qmk L' (z : L')) = 3 := orderOf_eq_prime hw3 hw1
        have hwc : qmk L' (z : L') ∈ Subgroup.center (Qt L') := by
          rw [Subgroup.mem_center_iff]
          intro g
          obtain ⟨g, rfl⟩ := qmk_surjective g
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzc g]
        have := orderOf_dvd_natCard (⟨qmk L' (z : L'), hwc⟩ : Subgroup.center (Qt L'))
        rwa [Subgroup.orderOf_mk, hwo] at this
      · obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_lift Eb hEb
        rw [← hEc, hcard]
        exact hbound E hE
      · obtain ⟨a, ha, h⟩ := hex
        refine ⟨qAutHom L' a, ⟨a, ha, rfl⟩, ?_⟩
        rcases h with hna | hall
        · exact Or.inl (qAutHom_not_mem_range_conj hperf hna)
        · refine Or.inr fun lb hlb => ?_
          obtain ⟨l, rfl⟩ := qmk_surjective lb
          have hl : MulAut.conj l = a := qAutHom_injective hperf (by rw [qAutHom_conj]; exact hlb)
          have h3 := three_dvd_orderOf_qmk (hall l hl)
          rwa [← map_pow]

end Delta

end CFSG.StandardType.USixTwo

end
