module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QLine
public import CFSG.CGT.PushingUpLit.BHS.SL2Normalizer

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.Campbell
open scoped IsMulCommutative MatrixGroups Matrix Pointwise
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL)

variable {G : Type} [Group G]

namespace Setting516

variable {T L D R : Subgroup G}

theorem le_pCoreOf_of_inf_le [Finite G] (hS : Setting516 T L D R) {K : Subgroup G}
    (hK : K ≤ L ⊔ T) (hKn : L ⊔ T ≤ Subgroup.normalizer (K : Set G))
    (hKL : L ⊓ K ≤ pCoreOf 2 L) : K ≤ pCoreOf 2 (L ⊔ T) := by
  have hTN := hS.le_normalizer
  have hK2 : IsPGroup 2 ↥K := by
    rintro ⟨x, hxK⟩
    have hx : x ∈ ((L : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTN]
      exact hK hxK
    obtain ⟨l, hl, t, ht, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hS.isPGroup ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨l', hl', he⟩ := pow_mul_mem_of_mem_normalizer hl (hTN ht) (2 ^ a)
    rw [hta, mul_one] at he
    have hC : (l * t) ^ 2 ^ a ∈ K := Subgroup.pow_mem _ hxK _
    rw [he] at hC
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨l', hKL ⟨hl', hC⟩⟩
    have hk' : l' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨a + k, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, he, hk']
  exact le_pCoreOf_of_le_normalizer 2 hK hKn hK2

end Setting516

namespace QCoord

abbrev normNL (N L : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (N : Set G) ⊓ Subgroup.normalizer (L : Set G)

variable {L N S : Subgroup G} {F : Type} [Field F] {ψ : ↥(autOn L N) ≃* SL(2, F)}
  {Y : ↥N →* Multiplicative (Fin 2 → F)}

theorem exists_perm (hc : QCoord L N S F ψ Y) (x : ↥(normNL N L)) :
    ∃ π : Equiv.Perm (Fin 2 → F), ∀ w : ↥N,
      Multiplicative.toAdd (Y (conjAct N ⟨x, x.2.1⟩ w)) = π (Multiplicative.toAdd (Y w)) := by
  set f := conjAct N ⟨(x : G), x.2.1⟩ with hf
  have hker : ∀ w, Y (f w) = 1 ↔ Y w = 1 := fun w => by
    rw [hc.ker, hc.ker, hf, conjAct_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp
      (F7.normalizer_le_normalizer_centralizer L x.2.2) w).symm
  have hmap : Y.ker.map f.toMonoidHom = Y.ker := by
    ext d
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hker w).2 hw
    · intro hd
      exact ⟨f.symm d, (hker (f.symm d)).1 (by rw [f.apply_symm_apply]; exact hd), by simp⟩
  let e1 := QuotientGroup.quotientKerEquivOfSurjective Y hc.surj
  let e2 := QuotientGroup.congr Y.ker Y.ker f hmap
  refine ⟨(Multiplicative.ofAdd.trans (e1.symm.trans (e2.trans e1)).toEquiv).trans
    Multiplicative.toAdd, fun w => ?_⟩
  have h1 : e1.symm (Y w) = (w : ↥N ⧸ Y.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show Multiplicative.toAdd (Y (f w)) =
    Multiplicative.toAdd (e1 (e2 (e1.symm (Multiplicative.ofAdd (Multiplicative.toAdd (Y w))))))
  rw [ofAdd_toAdd, h1]
  rfl

noncomputable def permFun (hc : QCoord L N S F ψ Y) (x : ↥(normNL N L)) :
    Equiv.Perm (Fin 2 → F) :=
  Classical.choose (hc.exists_perm x)

theorem permFun_spec (hc : QCoord L N S F ψ Y) (x : ↥(normNL N L)) (w : ↥N) :
    Multiplicative.toAdd (Y (conjAct N ⟨x, x.2.1⟩ w)) =
      hc.permFun x (Multiplicative.toAdd (Y w)) :=
  Classical.choose_spec (hc.exists_perm x) w

theorem perm_ext (hc : QCoord L N S F ψ Y) {π π' : Equiv.Perm (Fin 2 → F)}
    (h : ∀ w : ↥N, π (Multiplicative.toAdd (Y w)) = π' (Multiplicative.toAdd (Y w))) :
    π = π' := by
  refine Equiv.ext fun v => ?_
  obtain ⟨w, hw⟩ := hc.surj (Multiplicative.ofAdd v)
  have := h w
  rwa [hw, toAdd_ofAdd] at this

noncomputable def permHom (hc : QCoord L N S F ψ Y) :
    ↥(normNL N L) →* Equiv.Perm (Fin 2 → F) :=
  MonoidHom.mk' hc.permFun fun a b => by
    refine hc.perm_ext fun w => ?_
    rw [Equiv.Perm.mul_apply, ← hc.permFun_spec (a * b) w, ← hc.permFun_spec b w,
      ← hc.permFun_spec a]
    show Multiplicative.toAdd (Y (conjAct N (⟨a, a.2.1⟩ * ⟨b, b.2.1⟩) w)) =
      Multiplicative.toAdd (Y (conjAct N ⟨a, a.2.1⟩ (conjAct N ⟨b, b.2.1⟩ w)))
    rw [map_mul, MulAut.mul_apply]

theorem permHom_spec (hc : QCoord L N S F ψ Y) (x : ↥(normNL N L)) (w : ↥N) :
    Multiplicative.toAdd (Y (conjAct N ⟨x, x.2.1⟩ w)) =
      hc.permHom x (Multiplicative.toAdd (Y w)) :=
  hc.permFun_spec x w

theorem permHom_add (hc : QCoord L N S F ψ Y) (x : ↥(normNL N L)) (v v' : Fin 2 → F) :
    hc.permHom x (v + v') = hc.permHom x v + hc.permHom x v' := by
  obtain ⟨w, hw⟩ := hc.surj (Multiplicative.ofAdd v)
  obtain ⟨w', hw'⟩ := hc.surj (Multiplicative.ofAdd v')
  have hv : Multiplicative.toAdd (Y w) = v := by rw [hw, toAdd_ofAdd]
  have hv' : Multiplicative.toAdd (Y w') = v' := by rw [hw', toAdd_ofAdd]
  rw [← hv, ← hv', ← toAdd_mul, ← map_mul, ← hc.permHom_spec x (w * w'),
    ← hc.permHom_spec x w, ← hc.permHom_spec x w', map_mul, map_mul, toAdd_mul]

theorem permHom_of_mem (hc : QCoord L N S F ψ Y) (g : G) (hg : g ∈ normNL N L) (hgL : g ∈ L) :
    hc.permHom ⟨g, hg⟩ = slPerm F (ψ (autHom hc.le_normalizer ⟨g, hgL⟩)) := by
  refine hc.perm_ext fun w => ?_
  rw [← hc.permHom_spec, slPerm_apply]
  exact hc.intertwine (autHom hc.le_normalizer ⟨g, hgL⟩) w

theorem permHom_eq_one (hc : QCoord L N S F ψ Y) (x : ↥(normNL N L))
    (hx : (x : G) ∈ Subgroup.centralizer (N : Set G)) : hc.permHom x = 1 := by
  refine hc.perm_ext fun w => ?_
  rw [← hc.permHom_spec, Equiv.Perm.one_apply]
  congr 2
  apply Subtype.ext
  rw [conjAct_apply_coe]
  show (x : G) * w * (x : G)⁻¹ = w
  rw [← Subgroup.mem_centralizer_iff.mp hx w w.2, mul_inv_cancel_right]

end QCoord

namespace Setting516

variable {T L D R N : Subgroup G} {F : Type} [Field F] {ψ : ↥(autOn L N) ≃* SL(2, F)}
  {Y : ↥N →* Multiplicative (Fin 2 → F)}

theorem exists_mul_of_isMaxElemAbelian [Finite G] [Finite F] [CharP F 2]
    (hS : Setting516 T L D R) (hNR : N ≤ R) (hLTN : L ⊔ T ≤ Subgroup.normalizer (N : Set G))
    (hc : QCoord L N (T ⊓ L) F ψ Y) {A : Subgroup G} (hA : IsMaxElemAbelian T A) {a : G}
    (ha : a ∈ A) : ∃ s ∈ T ⊓ L, a * s⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
  classical
  have hLTX : L ⊔ T ≤ QCoord.normNL N L :=
    le_inf hLTN (sup_le Subgroup.le_normalizer hS.le_normalizer)
  have hAT : A ≤ T := hA.1
  have hAX : A ≤ QCoord.normNL N L := hAT.trans (le_sup_right.trans hLTX)
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup G,
      K = (hc.permHom.comp (Subgroup.inclusion hLTX)).ker.map (L ⊔ T).subtype := ⟨_, rfl⟩
  have hmemK : ∀ (x : G) (hx : x ∈ L ⊔ T), hc.permHom ⟨x, hLTX hx⟩ = 1 → x ∈ K := by
    intro x hx h1
    rw [hKdef]
    exact ⟨⟨x, hx⟩, h1, rfl⟩
  have hKmem : ∀ x ∈ K, ∃ hx : x ∈ L ⊔ T, hc.permHom ⟨x, hLTX hx⟩ = 1 := by
    intro x hx
    rw [hKdef] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y.2, hy⟩
  have hKLT : K ≤ L ⊔ T := fun x hx => (hKmem x hx).1
  have hKn : L ⊔ T ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    mem_normalizer_of_conj_mem fun x hx => by
      obtain ⟨hxLT, hx1⟩ := hKmem x hx
      refine hmemK _ (mul_mem (mul_mem hg hxLT) (inv_mem hg)) ?_
      have e : (⟨g * x * g⁻¹, hLTX (mul_mem (mul_mem hg hxLT) (inv_mem hg))⟩ :
          ↥(QCoord.normNL N L)) = ⟨g, hLTX hg⟩ * ⟨x, hLTX hxLT⟩ * ⟨g, hLTX hg⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, hx1, mul_one, map_inv, mul_inv_cancel]
  have hKL : L ⊓ K ≤ pCoreOf 2 L := by
    have hnorm : L ≤ Subgroup.normalizer ((L ⊓ K : Subgroup G) : Set G) := fun l hl =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl,
        hKn (Subgroup.mem_sup_left hl)⟩
    rcases hS.simple _ inf_le_left hnorm with hle | heq
    · exact hle
    · exfalso
      obtain ⟨g, hgL, hg⟩ := mem_autOn_iff.mp (ψ.symm (unipSL 1)).2
      obtain ⟨hgLT, hg1⟩ := hKmem _ (heq.symm.le hgL).2
      rw [hc.permHom_of_mem (g : G) (hLTX hgLT) hgL] at hg1
      have h2 : autHom hc.le_normalizer ⟨(g : G), hgL⟩ = ψ.symm (unipSL 1) := Subtype.ext hg
      rw [h2, MulEquiv.apply_symm_apply] at hg1
      have h3 : unipSL (1 : F) = 1 := slPerm_injective (by rw [hg1, map_one])
      have h4 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h3
      simp [coe_unipSL] at h4
  have hKO := hS.le_pCoreOf_of_inf_le hKLT hKn hKL
  have hKT : K ≤ T := hKO.trans (F7.isSylowTwoOf_pCoreOf_le hS.sylow_sup)
  have hKR : K ≤ Subgroup.centralizer (R : Set G) :=
    hKO.trans (A4.pCoreOf_le_centralizer_of_isTwoReducedIn hS.reduced)
  have haLT : a ∈ L ⊔ T := Subgroup.mem_sup_right (hAT ha)
  by_cases ha1 : hc.permHom ⟨a, hAX ha⟩ = 1
  · refine ⟨1, one_mem _, ?_⟩
    rw [inv_one, mul_one]
    exact hKR (hmemK a haLT ha1)
  obtain ⟨B, hB⟩ : ∃ B : Subgroup (Equiv.Perm (Fin 2 → F)),
      B = (hc.permHom.comp (Subgroup.inclusion hAX)).range := ⟨_, rfl⟩
  have hadd : ∀ b ∈ B, ∀ w w' : Fin 2 → F, b (w + w') = b w + b w' := by
    intro b hb w w'
    rw [hB] at hb
    obtain ⟨x, rfl⟩ := hb
    exact hc.permHom_add _ w w'
  have hnorm : ∀ b ∈ B, ∀ g : SL(2, F),
      ∃ g' : SL(2, F), b * slPerm F g * b⁻¹ = slPerm F g' := by
    intro b hb g
    rw [hB] at hb
    obtain ⟨x, rfl⟩ := hb
    obtain ⟨l, hlL, hl⟩ := mem_autOn_iff.mp (ψ.symm g).2
    have hxL : (x : G) ∈ Subgroup.normalizer (L : Set G) := hS.le_normalizer (hAT x.2)
    have hxl : (x : G) * l * (x : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxL l).mp hlL
    refine ⟨ψ (autHom hc.le_normalizer ⟨_, hxl⟩), ?_⟩
    have h2 : autHom hc.le_normalizer ⟨(l : G), hlL⟩ = ψ.symm g := Subtype.ext hl
    have h1 : slPerm F g = hc.permHom ⟨l, hLTX (Subgroup.mem_sup_left hlL)⟩ := by
      rw [hc.permHom_of_mem (l : G) _ hlL, h2, MulEquiv.apply_symm_apply]
    rw [h1, ← hc.permHom_of_mem ((x : G) * l * (x : G)⁻¹) (hLTX (Subgroup.mem_sup_left hxl)) hxl,
      MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hcomm : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    intro b hb b' hb'
    rw [hB] at hb hb'
    obtain ⟨x, rfl⟩ := hb
    obtain ⟨y, rfl⟩ := hb'
    have hxy : x * y = y * x := hA.2.1.1.is_comm.comm x y
    rw [← map_mul, ← map_mul, hxy]
  have hsq : ∀ b ∈ B, b * b = 1 := by
    intro b hb
    rw [hB] at hb
    obtain ⟨x, rfl⟩ := hb
    rw [← map_mul]
    have hx : x * x = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← sq]
      exact hA.2.1.2 x x.2)
    rw [hx, map_one]
  have hne : B ≠ ⊥ := by
    intro hbot
    apply ha1
    have hmem : (hc.permHom.comp (Subgroup.inclusion hAX)) ⟨a, ha⟩ ∈ B := by
      rw [hB]
      exact ⟨⟨a, ha⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hge : Nat.card F ^ 2 ≤ Nat.card B * Nat.card (fixSet B) := by
    have hker : (hc.permHom.comp (Subgroup.inclusion hAX)).ker =
        (Subgroup.centralizer (N : Set G)).subgroupOf A := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        exact Subgroup.centralizer_le hNR (hKR (hmemK x (Subgroup.mem_sup_right (hAT x.2)) hx))
      · intro hx
        rw [MonoidHom.comp_apply]
        exact hc.permHom_eq_one _ hx
    have hBcard : Nat.card B = (A ⊓ Subgroup.centralizer (N : Set G)).relIndex A := by
      rw [hB, Subgroup.inf_relIndex_left, ← Subgroup.index_ker, hker]
      rfl
    let cd : Subgroup (Multiplicative (Fin 2 → F)) :=
      { carrier := {d | ∀ b ∈ B, b (Multiplicative.toAdd d) = Multiplicative.toAdd d}
        one_mem' := fun b hb => by
          have h0 := hadd b hb 0 0
          rw [add_zero] at h0
          exact add_eq_left.mp h0.symm
        mul_mem' := fun {d d'} hd hd' b hb => by
          show b (Multiplicative.toAdd d + Multiplicative.toAdd d') =
            Multiplicative.toAdd d + Multiplicative.toAdd d'
          rw [hadd b hb, hd b hb, hd' b hb]
        inv_mem' := fun {d} hd b hb => by
          show b (-Multiplicative.toAdd d) = -Multiplicative.toAdd d
          have h0 := hadd b hb (Multiplicative.toAdd d) (-Multiplicative.toAdd d)
          have hz : b 0 = 0 := by
            have h00 := hadd b hb 0 0
            rw [add_zero] at h00
            exact add_eq_left.mp h00.symm
          rw [add_neg_cancel, hz, hd b hb] at h0
          exact (neg_eq_of_add_eq_zero_right h0.symm).symm }
    have hcd : Nat.card cd = Nat.card (fixSet B) :=
      Nat.card_congr ⟨fun d => ⟨Multiplicative.toAdd d.1, d.2⟩,
        fun v => ⟨Multiplicative.ofAdd v.1, v.2⟩, fun _ => rfl, fun _ => rfl⟩
    have hMcd : ((Subgroup.centralizer (A : Set G)).subgroupOf N).map Y ≤ cd := by
      rintro _ ⟨w, hw, rfl⟩ b hb
      rw [hB] at hb
      obtain ⟨x, rfl⟩ := hb
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hw
      rw [MonoidHom.comp_apply, ← hc.permHom_spec]
      congr 2
      apply Subtype.ext
      rw [conjAct_apply_coe]
      show (x : G) * w * (x : G)⁻¹ = w
      rw [Subgroup.mem_centralizer_iff.mp hw x x.2, mul_inv_cancel_right]
    have h1 : cd.index ≤ (((Subgroup.centralizer (A : Set G)).subgroupOf N).map Y).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hMcd)
    have h2 : (((Subgroup.centralizer (A : Set G)).subgroupOf N).map Y).index ≤
        (Subgroup.centralizer (A : Set G)).relIndex N := by
      rw [Subgroup.index_map, MonoidHom.range_eq_top.mpr hc.surj, Subgroup.index_top, mul_one]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le le_sup_left)
    have hNe : IsElemAbelian 2 N :=
      ⟨⟨⟨fun x y => Subtype.ext (by
        have h := congrArg Subtype.val
          (hS.reduced.2.2.1.1.is_comm.comm ⟨x, hNR x.2⟩ ⟨y, hNR y.2⟩)
        exact h)⟩⟩,
        fun x hx => hS.reduced.2.2.1.2 x (hNR hx)⟩
    have hoff := card_le_relIndex_mul_card hNe (hNR.trans hS.le_T) hA
    have h3 : (Subgroup.centralizer (A : Set G)).relIndex N ≤
        (A ⊓ Subgroup.centralizer (N : Set G)).relIndex A := by
      have h4 := Subgroup.relIndex_mul_card (Subgroup.centralizer (A : Set G)) N
      rw [inf_comm] at h4
      have hpos : 0 < Nat.card ↥(N ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
      have h5 : (Subgroup.centralizer (A : Set G)).relIndex N *
          Nat.card ↥(N ⊓ Subgroup.centralizer (A : Set G)) ≤
          (A ⊓ Subgroup.centralizer (N : Set G)).relIndex A *
            Nat.card ↥(N ⊓ Subgroup.centralizer (A : Set G)) := by
        rw [h4]
        exact hoff
      exact Nat.le_of_mul_le_mul_right h5 hpos
    have h6 : Nat.card cd * cd.index = Nat.card F ^ 2 := by
      rw [Subgroup.card_mul_index, Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
      simp
    rw [← h6, hBcard, ← hcd, mul_comm (Nat.card cd)]
    exact Nat.mul_le_mul_right _ (h1.trans (h2.trans h3))
  obtain ⟨ℓ, hℓ⟩ := CFSG.CGT.PushingUpLit.BHS.eq_rootPerm_of_offender_normalizer B hadd hnorm
    hcomm hsq hne hge
  have hmem : (hc.permHom.comp (Subgroup.inclusion hAX)) ⟨a, ha⟩ ∈ rootPerm ℓ := by
    rw [← hℓ, hB]
    exact ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨g, -, hg⟩ := mem_rootPerm.mp hmem
  obtain ⟨l, hlL, hl⟩ := mem_autOn_iff.mp (ψ.symm g).2
  have h2 : autHom hc.le_normalizer ⟨(l : G), hlL⟩ = ψ.symm g := Subtype.ext hl
  have hlX : (l : G) ∈ QCoord.normNL N L := hLTX (Subgroup.mem_sup_left hlL)
  have h3 : hc.permHom ⟨l, hlX⟩ = hc.permHom ⟨a, hAX ha⟩ := by
    rw [hc.permHom_of_mem (l : G) hlX hlL, h2, MulEquiv.apply_symm_apply, hg]
    rfl
  have hal : a * (l : G)⁻¹ ∈ K := by
    refine hmemK _ (mul_mem haLT (inv_mem (Subgroup.mem_sup_left hlL))) ?_
    have e : (⟨a * (l : G)⁻¹, hLTX (mul_mem haLT (inv_mem (Subgroup.mem_sup_left hlL)))⟩ :
        ↥(QCoord.normNL N L)) = ⟨a, hAX ha⟩ * ⟨l, hlX⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, h3, mul_inv_cancel]
  refine ⟨l, Subgroup.mem_inf.mpr ⟨?_, hlL⟩, hKR hal⟩
  have hl' : (l : G) = (a * (l : G)⁻¹)⁻¹ * a := by group
  rw [hl']
  exact mul_mem (inv_mem (hKT hal)) (hAT ha)

theorem thompsonJ_le_centralizer [Finite G] [Finite F] [CharP F 2] (hS : Setting516 T L D R)
    (hNR : N ≤ R) (hLTN : L ⊔ T ≤ Subgroup.normalizer (N : Set G))
    (hc : QCoord L N (T ⊓ L) F ψ Y) {W : Subgroup G} (hWR : W ≤ R)
    (hWS : W ≤ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) :
    thompsonJ T ≤ Subgroup.centralizer (W : Set G) := by
  unfold thompsonJ
  refine iSup₂_le fun A hA => fun a ha => ?_
  obtain ⟨s, hs, has⟩ := hS.exists_mul_of_isMaxElemAbelian hNR hLTN hc hA ha
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h1 := Subgroup.mem_centralizer_iff.mp has w (hWR hw)
  have h2 := Subgroup.mem_centralizer_iff.mp (hWS hw) s hs
  calc w * a = w * (a * s⁻¹) * s := by group
    _ = a * s⁻¹ * w * s := by rw [h1]
    _ = a * s⁻¹ * (w * s) := by group
    _ = a * s⁻¹ * (s * w) := by rw [h2]
    _ = a * w := by group

end Setting516

end CFSG.Quasithin.H13
