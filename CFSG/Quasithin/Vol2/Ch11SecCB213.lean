module

public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
public import CFSG.Quasithin.Background.A3ComponentsQuotient
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B6Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open

variable {G : Type} [Group G]

theorem mem_sup_of_le_normalizer {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G))
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have h : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hB] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact ⟨a, ha, b, hb, rfl⟩

theorem le_normalizer_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [← h a ha b hb, mul_inv_cancel_right]
    exact ha
  · intro ha
    have h1 := h _ ha b hb
    rw [show b * a * b⁻¹ * b = b * a by group] at h1
    have h2 : a = b * a * b⁻¹ := mul_left_cancel h1
    rw [h2]
    exact ha

variable [Finite G]

theorem exists_compl_of_elem {E U : Subgroup G} (hE : IsElemAbelian 2 E) (hUE : U ≤ E) :
    ∃ C : Subgroup G, C ≤ E ∧ C ⊓ U = ⊥ ∧ C ⊔ U = E := by
  classical
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  let _ : Fintype (Subgroup G) := Fintype.ofFinite _
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun C : Subgroup G => C ≤ E ∧ C ⊓ U = ⊥)
    (fun C : Subgroup G => Nat.card C) ⟨⊥, by simp⟩
  obtain ⟨hCE, hCU⟩ := (Finset.mem_filter.mp hC).2
  refine ⟨C, hCE, hCU, le_antisymm (sup_le hCE hUE) ?_⟩
  by_contra hne
  obtain ⟨e, heE, heCU⟩ : ∃ e ∈ E, e ∉ C ⊔ U := by
    by_contra h
    push Not at h
    exact hne h
  have he2 : e ^ 2 = 1 := hE.2 e heE
  set C' := C ⊔ Subgroup.zpowers e
  have hC'E : C' ≤ E := sup_le hCE (Subgroup.zpowers_le.mpr heE)
  have hmemC' : ∀ x ∈ C', ∃ c ∈ C, x = c ∨ x = c * e := by
    intro x hx
    have hcm : ∀ a ∈ C, ∀ b ∈ Subgroup.zpowers e, a * b = b * a := fun a ha b hb =>
      hcomm a (hCE ha) b ((Subgroup.zpowers_le.mpr heE) hb)
    obtain ⟨c, hc, b, hb, rfl⟩ := mem_sup_of_le_normalizer (le_normalizer_of_commute hcm) hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · refine ⟨c, hc, Or.inl ?_⟩
      rw [zpow_mul, show e ^ (2 : ℤ) = 1 by exact_mod_cast he2, one_zpow, mul_one]
    · refine ⟨c, hc, Or.inr ?_⟩
      rw [zpow_add, zpow_mul, show e ^ (2 : ℤ) = 1 by exact_mod_cast he2, one_zpow, one_mul,
        zpow_one]
  have hC'U : C' ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨c, hc, rfl | rfl⟩ := hmemC' x hx1
    · rw [← hCU]; exact ⟨hc, hx2⟩
    · exfalso
      apply heCU
      have : e = c⁻¹ * (c * e) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (C.inv_mem hc))
        (Subgroup.mem_sup_right hx2)
  have hlt : C < C' := lt_of_le_of_ne le_sup_left fun h =>
    heCU (Subgroup.mem_sup_left (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers e)))
  have hcard := hmax C' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC'E, hC'U⟩)
  exact absurd hcard (not_le.mpr (Subgroup.card_lt_of_lt hlt))

theorem exists_invariant_compl {X T W N C₀ : Subgroup G} (hodd : ¬ 2 ∣ T.relIndex X)
    (hW : IsElemAbelian 2 W) (hXW : X ≤ Subgroup.normalizer (W : Set G)) (hNW : N ≤ W)
    (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hTC₀ : T ⊓ X ≤ Subgroup.normalizer (C₀ : Set G)) (hC₀N : C₀ ⊓ N = ⊥) (hsup : C₀ ⊔ N = W) :
    ∃ C : Subgroup G, C ≤ W ∧ X ≤ Subgroup.normalizer (C : Set G) ∧ C ⊓ N = ⊥ ∧ C ⊔ N = W := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC₀W : C₀ ≤ W := hsup ▸ le_sup_left
  let φ : ↥X →* MulAut ↥W := (W.normalizerMonoidHom).comp (Subgroup.inclusion hXW)
  have hφ : ∀ (x : ↥X) (w : ↥W), ((φ x w : ↥W) : G) = (x : G) * w * (x : G)⁻¹ := fun x w =>
    Subgroup.normalizerMonoidHom_apply_apply_coe W (Subgroup.inclusion hXW x) w
  have : Finite (↥W ⋊[φ] ↥X) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hWc : ∀ a b : ↥W, a * b = b * a := fun a b => hW.1.is_comm.comm a b
  set N' : Subgroup (↥W ⋊[φ] ↥X) := (N.subgroupOf W).map SemidirectProduct.inl
  have hφN : ∀ (x : ↥X) (w : ↥W), (w : G) ∈ N → ((φ x w : ↥W) : G) ∈ N := fun x w hw => by
    rw [hφ]; exact (Subgroup.mem_normalizer_iff.mp (hXN x.2) w).mp hw
  have hconj : ∀ (g : ↥W ⋊[φ] ↥X) (w : ↥W),
      g * SemidirectProduct.inl w * g⁻¹ = SemidirectProduct.inl (φ g.right w) := by
    intro g w
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
    have e1 : (SemidirectProduct.inl g.left : ↥W ⋊[φ] ↥X) * SemidirectProduct.inr g.right *
        SemidirectProduct.inl w * (SemidirectProduct.inl g.left * SemidirectProduct.inr g.right)⁻¹ =
        (SemidirectProduct.inl g.left : ↥W ⋊[φ] ↥X) * (SemidirectProduct.inr g.right *
          SemidirectProduct.inl w * SemidirectProduct.inr g.right⁻¹) *
          SemidirectProduct.inl g.left⁻¹ := by
      rw [mul_inv_rev, ← map_inv, ← map_inv]
      simp only [mul_assoc]
    rw [e1, ← SemidirectProduct.inl_aut, ← map_mul, ← map_mul, hWc g.left, mul_inv_cancel_right]
  have hN'n : N'.Normal := by
    refine ⟨fun y hy g => ?_⟩
    obtain ⟨w, hw, rfl⟩ := hy
    rw [hconj]
    exact ⟨_, hφN _ _ hw, rfl⟩
  have hN'c : IsMulCommutative ↥N' := IsMulCommutative.of_comm fun a b => by
    obtain ⟨wa, -, ha⟩ := a.2
    obtain ⟨wb, -, hb⟩ := b.2
    apply Subtype.ext
    show (a : ↥W ⋊[φ] ↥X) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, hWc]
  have hright : ∀ y ∈ N', y.right = 1 := by
    rintro _ ⟨w, -, rfl⟩
    rfl
  set H : Subgroup (↥W ⋊[φ] ↥X) := (T.subgroupOf X).comap SemidirectProduct.rightHom
  let K : Subgroup (↥W ⋊[φ] ↥X) :=
    { carrier := {y | (y.left : G) ∈ C₀ ∧ (y.right : G) ∈ T}
      one_mem' := ⟨C₀.one_mem, T.one_mem⟩
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, T.mul_mem ha2 hb2⟩
        simp only [SemidirectProduct.mul_left, Subgroup.coe_mul, hφ]
        exact C₀.mul_mem ha1 ((Subgroup.mem_normalizer_iff.mp
          (hTC₀ ⟨ha2, a.right.2⟩) _).mp hb1)
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨?_, T.inv_mem ha2⟩
        simp only [SemidirectProduct.inv_left, hφ, InvMemClass.coe_inv]
        exact (Subgroup.mem_normalizer_iff.mp
          (hTC₀ ⟨T.inv_mem ha2, X.inv_mem a.right.2⟩) _).mp (C₀.inv_mem ha1) }
  have hNK : N' ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨w, hw, rfl⟩, hK⟩
    have hw1 : (w : G) ∈ C₀ ⊓ N := ⟨hK.1, hw⟩
    rw [hC₀N, Subgroup.mem_bot] at hw1
    rw [Subgroup.mem_bot, show w = 1 from Subtype.ext hw1, map_one]
  have hNKH : N' ⊔ K = H := by
    refine le_antisymm (sup_le ?_ ?_) ?_
    · rintro _ ⟨w, -, rfl⟩
      show ((SemidirectProduct.rightHom
        (SemidirectProduct.inl w : ↥W ⋊[φ] ↥X) : ↥X) : G) ∈ T
      rw [SemidirectProduct.rightHom_inl]
      exact T.one_mem
    · intro y hy
      exact hy.2
    · intro y hy
      have hyT : (y.right : G) ∈ T := hy
      have hyW : (y.left : G) ∈ C₀ ⊔ N := hsup ▸ y.left.2
      obtain ⟨c, hc, m, hm, hcm⟩ := mem_sup_of_le_normalizer
        (le_normalizer_of_commute fun a ha b hb => congrArg Subtype.val
          (hWc ⟨a, hC₀W ha⟩ ⟨b, hNW hb⟩)) hyW
      have hy' : y = (SemidirectProduct.inl ⟨m, hNW hm⟩ : ↥W ⋊[φ] ↥X) *
          (SemidirectProduct.inl ⟨c, hC₀W hc⟩ * SemidirectProduct.inr y.right) := by
        apply SemidirectProduct.ext
        · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
            SemidirectProduct.right_inl, SemidirectProduct.left_inr, map_one, MulAut.one_apply,
            mul_one]
          apply Subtype.ext
          rw [Subgroup.coe_mul, hcm]
          exact congrArg Subtype.val (hWc ⟨c, hC₀W hc⟩ ⟨m, hNW hm⟩)
        · simp
      rw [hy']
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, hm, rfl⟩) (Subgroup.mem_sup_right ?_)
      refine ⟨?_, ?_⟩
      · simpa using hc
      · simpa using hyT
  have hcop : Nat.Coprime H.index (Nat.card N') := by
    have hHi : H.index = T.relIndex X :=
      Subgroup.index_comap_of_surjective (T.subgroupOf X) SemidirectProduct.rightHom_surjective
    have hNp : IsPGroup 2 ↥N := (B6.isPGroup_of_isElemAbelian hW).to_le hNW
    obtain ⟨k, hk⟩ := hNp.exists_card_eq
    have hcN : Nat.card ↥N' = Nat.card ↥N :=
      (Nat.card_congr ((N.subgroupOf W).equivMapOfInjective _
        SemidirectProduct.inl_injective).toEquiv).symm.trans
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv)
    rw [hcN, hk, hHi]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
  obtain ⟨D, -, hND, hNDt⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting N' H K hcop hNK hNKH
  have hdec : ∀ y : ↥W ⋊[φ] ↥X, ∃ m ∈ N', ∃ d ∈ D, y = m * d := fun y =>
    mem_sup_of_le_normalizer (fun d _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hN'n]; exact Subgroup.mem_top d)
      (hNDt ▸ Subgroup.mem_top y)
  have hconjN' : ∀ m ∈ N', ∀ w : ↥W,
      m * SemidirectProduct.inl w * m⁻¹ = SemidirectProduct.inl w := by
    intro m hm w
    rw [hconj, hright m hm, map_one, MulAut.one_apply]
  refine ⟨(D.comap SemidirectProduct.inl).map W.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  ·
    have key : ∀ x ∈ X, ∀ c ∈ (D.comap SemidirectProduct.inl).map W.subtype,
        x * c * x⁻¹ ∈ (D.comap SemidirectProduct.inl).map W.subtype := by
      rintro x hx _ ⟨w, hw, rfl⟩
      obtain ⟨m, hm, d, hd, hmd⟩ := hdec (SemidirectProduct.inr ⟨x, hx⟩)
      refine ⟨φ ⟨x, hx⟩ w, ?_, (hφ ⟨x, hx⟩ w).symm ▸ rfl⟩
      show SemidirectProduct.inl (φ ⟨x, hx⟩ w) ∈ D
      have e1 : (SemidirectProduct.inl (φ ⟨x, hx⟩ w) : ↥W ⋊[φ] ↥X) =
          SemidirectProduct.inr ⟨x, hx⟩ * SemidirectProduct.inl w *
            (SemidirectProduct.inr ⟨x, hx⟩)⁻¹ := by
        rw [SemidirectProduct.inl_aut, map_inv]
      have hw' : (SemidirectProduct.inl w : ↥W ⋊[φ] ↥X) ∈ D := hw
      rw [e1, hmd, mul_inv_rev, show m * d * (SemidirectProduct.inl w : ↥W ⋊[φ] ↥X) *
        (d⁻¹ * m⁻¹) = m * (d * SemidirectProduct.inl w * d⁻¹) * m⁻¹ by group, hconj d w,
        hconjN' m hm, ← hconj d w]
      exact D.mul_mem (D.mul_mem hd hw') (D.inv_mem hd)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨key x hx c, fun hc => ?_⟩
    have := key x⁻¹ (X.inv_mem hx) _ hc
    simpa [mul_assoc] using this
  ·
    rw [eq_bot_iff]
    rintro _ ⟨⟨w, hw, rfl⟩, hwN⟩
    have h1 : (SemidirectProduct.inl w : ↥W ⋊[φ] ↥X) ∈ N' ⊓ D := ⟨⟨w, hwN, rfl⟩, hw⟩
    rw [hND, Subgroup.mem_bot, map_eq_one_iff _ SemidirectProduct.inl_injective] at h1
    rw [Subgroup.mem_bot, h1]
    rfl
  ·
    refine le_antisymm (sup_le (Subgroup.map_subtype_le _) hNW) fun w hw => ?_
    obtain ⟨m, ⟨n, hn, rfl⟩, d, hd, hmd⟩ := hdec (SemidirectProduct.inl ⟨w, hw⟩)
    have hd' : d = (SemidirectProduct.inl (n⁻¹ * ⟨w, hw⟩) : ↥W ⋊[φ] ↥X) := by
      rw [map_mul, map_inv, hmd, inv_mul_cancel_left]
    have hC : ((n⁻¹ * ⟨w, hw⟩ : ↥W) : G) ∈ (D.comap SemidirectProduct.inl).map W.subtype :=
      ⟨_, show SemidirectProduct.inl _ ∈ D from hd' ▸ hd, rfl⟩
    have : w = ((n⁻¹ * ⟨w, hw⟩ : ↥W) : G) * (n : G) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [show ((n : ↥W) : G)⁻¹ * w * n = w from by
        rw [mul_assoc, show w * (n : G) = n * w from
          congrArg Subtype.val (hWc ⟨w, hw⟩ n), ← mul_assoc, inv_mul_cancel, one_mul]]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hC) (Subgroup.mem_sup_right hn)

theorem conjClosure_eq_commutator_sup {X T Z : Subgroup G} (hodd : ¬ 2 ∣ T.relIndex X)
    (hW : IsElemAbelian 2 (conjClosure Z X)) (hTZ : T ≤ Subgroup.centralizer (Z : Set G)) :
    conjClosure Z X =
      ⁅conjClosure Z X, X⁆ ⊔ (conjClosure Z X ⊓ Subgroup.centralizer (X : Set G)) := by
  have hXW : X ≤ Subgroup.normalizer (conjClosure Z X : Set G) := le_normalizer_conjClosure Z X
  have hNW : ⁅conjClosure Z X, X⁆ ≤ conjClosure Z X := by
    rw [Subgroup.commutator_le]
    intro w hw x hx
    have := (Subgroup.mem_normalizer_iff.mp (hXW hx) w⁻¹).mp ((conjClosure Z X).inv_mem hw)
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc x]
    exact (conjClosure Z X).mul_mem hw this
  have hXN : X ≤ Subgroup.normalizer ((⁅conjClosure Z X, X⁆ : Subgroup G) : Set G) :=
    le_sup_right.trans (A3.sup_le_normalizer_commutator _ X)
  have hZW : Z ≤ conjClosure Z X := le_conjClosure Z X
  have hZel : IsElemAbelian 2 Z :=
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext
      (show (a : G) * b = b * a from
        congrArg Subtype.val (hW.1.is_comm.comm ⟨a, hZW a.2⟩ ⟨b, hZW b.2⟩)),
      fun z hz => hW.2 z (hZW hz)⟩
  have hWZN : conjClosure Z X ≤ Z ⊔ ⁅conjClosure Z X, X⁆ := by
    refine conjClosure_le fun x hx z hz => ?_
    have hc : x * z * x⁻¹ * z⁻¹ ∈ ⁅conjClosure Z X, X⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hx (hZW hz)
    have : x * z * x⁻¹ = (x * z * x⁻¹ * z⁻¹) * z := by group
    rw [this, sup_comm]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hz)
  obtain ⟨C₀, hC₀Z, hC₀ZN, hC₀sup⟩ := exists_compl_of_elem hZel
    (inf_le_left : Z ⊓ ⁅conjClosure Z X, X⁆ ≤ Z)
  have hTC₀ : T ⊓ X ≤ Subgroup.normalizer (C₀ : Set G) := fun t ht =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hC₀Z (hTZ ht.1))
  have h1 : C₀ ⊓ ⁅conjClosure Z X, X⁆ = ⊥ := by
    rw [eq_bot_iff, ← hC₀ZN]
    exact fun x hx => ⟨hx.1, hC₀Z hx.1, hx.2⟩
  have h2 : C₀ ⊔ ⁅conjClosure Z X, X⁆ = conjClosure Z X := by
    refine le_antisymm (sup_le (hC₀Z.trans hZW) hNW) (hWZN.trans (sup_le ?_ le_sup_right))
    exact hC₀sup.ge.trans (sup_le le_sup_left (inf_le_right.trans le_sup_right))
  obtain ⟨C, hCW, hXC, hCN, hCNsup⟩ := exists_invariant_compl hodd hW hXW hNW hXN hTC₀ h1 h2
  have hCX : C ≤ Subgroup.centralizer (X : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h3 : x * c * x⁻¹ * c⁻¹ ∈ C ⊓ ⁅conjClosure Z X, X⁆ := by
      refine ⟨C.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXC hx) c).mp hc) (C.inv_mem hc), ?_⟩
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hx (hCW hc)
    rw [hCN, Subgroup.mem_bot] at h3
    have : x * c * x⁻¹ = c := by rw [← mul_inv_eq_one]; exact h3
    calc x * c = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [this]
  refine le_antisymm ?_ (sup_le hNW inf_le_left)
  calc conjClosure Z X = C ⊔ ⁅conjClosure Z X, X⁆ := hCNsup.symm
    _ ≤ _ := sup_le (le_sup_of_le_right (le_inf hCW hCX)) le_sup_left

end CFSG.Quasithin.Vol2.Ch11.SecC
