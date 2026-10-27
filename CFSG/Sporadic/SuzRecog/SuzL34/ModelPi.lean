module

public import CFSG.Sporadic.SuzRecog.SuzL34.Facts
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34Cert

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0

@[expose] def IsPi {H : Type*} [Group H] (P : Subgroup H) : Prop :=
  Nat.card P = 1024 ∧ CFSG.Open.IsElemAbelian 2 (Subgroup.center ↥P) ∧
    Nat.card (Subgroup.center ↥P) = 16

theorem isPi_iff_of_mulEquiv {H K : Type*} [Group H] [Group K] {P : Subgroup H}
    {Q : Subgroup K} (e : ↥P ≃* ↥Q) : IsPi P ↔ IsPi Q := by
  have hcard : Nat.card P = Nat.card Q := Nat.card_congr e.toEquiv
  have hmap : (Subgroup.center ↥P).map e.toMonoidHom = Subgroup.center ↥Q :=
    Subgroup.map_center_eq e
  let eC : ↥(Subgroup.center ↥P) ≃* ↥(Subgroup.center ↥Q) :=
    (Subgroup.equivMapOfInjective (Subgroup.center ↥P) e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hcardC : Nat.card ↥(Subgroup.center ↥P) = Nat.card ↥(Subgroup.center ↥Q) :=
    Nat.card_congr eC.toEquiv
  have hea : CFSG.Open.IsElemAbelian 2 (Subgroup.center ↥P) ↔
      CFSG.Open.IsElemAbelian 2 (Subgroup.center ↥Q) := by
    constructor
    · intro h
      haveI : CFSG.IsElementaryAbelian 2 (Subgroup.center ↥Q) :=
        CFSG.IsElementaryAbelian.of_mulEquiv eC h.isElementaryAbelian
      exact CFSG.Open.isElemAbelian_of_isElementaryAbelian
    · intro h
      haveI : CFSG.IsElementaryAbelian 2 (Subgroup.center ↥P) :=
        CFSG.IsElementaryAbelian.of_mulEquiv eC.symm h.isElementaryAbelian
      exact CFSG.Open.isElemAbelian_of_isElementaryAbelian
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hcard ▸ h1, hea.mp h2, hcardC ▸ h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hcard.symm ▸ h1, hea.mpr h2, hcardC.symm ▸ h3⟩

theorem isPi_map_iff {H K : Type*} [Group H] [Group K] {f : H →* K}
    (hf : Function.Injective f) (P : Subgroup H) : IsPi (P.map f) ↔ IsPi P :=
  isPi_iff_of_mulEquiv (Subgroup.equivMapOfInjective P f hf).symm

theorem l1_le_m1 (hF1M : F1MProp) : decSubgroup l1Decs ≤ decSubgroup m1Decs := by
  have h := hF1M
  dsimp only [F1MProp] at h
  intro x hx
  exact (h.2 x).1 hx |>.1

theorem m1_le_centralizer_l1 (hF1M : F1MProp) :
    decSubgroup m1Decs ≤
      Subgroup.centralizer (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h := hF1M
  dsimp only [F1MProp] at h
  exact ((h.2 y).1 hy).2 x hx

theorem le_m1_of_isPGroup (hF1M : F1MProp) (hF2 : F2Prop)
    (hM : decSubgroup m1Decs ≤ invE 1)
    {P : Subgroup (Equiv.Perm (Fin 1782))}
    (hP : P ≤ Subgroup.centralizer (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) ⊓ invE 1)
    (h2 : IsPGroup 2 P) : P ≤ decSubgroup m1Decs := by
  classical
  have hF2' := hF2
  dsimp only [F2Prop] at hF2'
  obtain ⟨-, -, hCL_eq, hCLcard, hMnormal, -⟩ := hF2'
  have hMleCent : decSubgroup m1Decs ≤
      Subgroup.centralizer (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) :=
    m1_le_centralizer_l1 hF1M
  have hMleCL : decSubgroup m1Decs ≤ decSubgroup cl1Decs := by
    rw [← hCL_eq]; exact le_inf hMleCent hM
  have hPleCL : P ≤ decSubgroup cl1Decs := by
    rw [← hCL_eq]; exact hP
  have hMcard : Nat.card (decSubgroup m1Decs) = 1024 := by
    have := hF1M; dsimp only [F1MProp] at this; exact this.1
  let CL := decSubgroup cl1Decs
  let M := decSubgroup m1Decs
  let Q := M.subgroupOf CL
  have hQcard : Nat.card ↥Q = 1024 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMleCL).toEquiv]
    exact hMcard
  have hQindex : Q.index = 3 := by
    have h := Subgroup.card_mul_index Q
    rw [hQcard, hCLcard] at h
    omega
  have hQp : IsPGroup 2 Q :=
    IsPGroup.of_card (n := 10) (by rw [hQcard]; norm_num)
  have hP'p : IsPGroup 2 (P.subgroupOf CL) := h2.comap_subtype
  let R := P.subgroupOf CL ⊔ Q
  have hRp : IsPGroup 2 R := IsPGroup.to_sup_of_normal_right hP'p hQp
  let q : CL →* CL ⧸ Q := QuotientGroup.mk' Q
  have hRimg : IsPGroup 2 (R.map q) := hRp.map q
  have hdiv : Nat.card ↥(R.map q) ∣ 3 := by
    calc Nat.card ↥(R.map q) ∣ Nat.card (CL ⧸ Q) := Subgroup.card_subgroup_dvd_card _
      _ = Q.index := rfl
      _ = 3 := hQindex
  have hRimg_bot : R.map q = ⊥ := by
    obtain ⟨k, hk⟩ := hRimg.exists_card_eq
    apply Subgroup.eq_bot_of_card_eq
    have hk3 : 2 ^ k ∣ 3 := hk ▸ hdiv
    have hk0 : k = 0 := by
      by_contra hkne
      have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hkne
      exact absurd (h2dvd.trans hk3) (by norm_num)
    rw [hk, hk0, pow_zero]
  have hRleQ : R ≤ Q := by
    have := (Subgroup.map_eq_bot_iff (H := R) (f := q)).1 hRimg_bot
    rwa [QuotientGroup.ker_mk'] at this
  have hPQ : P.subgroupOf CL ≤ Q := le_sup_left.trans hRleQ
  intro x hx
  have hxCL : x ∈ CL := hPleCL hx
  have hxQ : (⟨x, hxCL⟩ : ↥CL) ∈ Q := hPQ (Subgroup.mem_subgroupOf.2 hx)
  exact Subgroup.mem_subgroupOf.1 hxQ

theorem centralizer_l1_inf_s1p (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hS : decSubgroup s1pDecs ≤ invE 1) (hM : decSubgroup m1Decs ≤ invE 1) :
    Subgroup.centralizer (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) ⊓
        decSubgroup s1pDecs = decSubgroup m1Decs := by
  have h1 := hF1
  dsimp only [F1Prop] at h1
  obtain ⟨hS1card, -, -, -, -, -, hcentcard, -⟩ := h1
  have hMcard : Nat.card (decSubgroup m1Decs) = 1024 := by
    have := hF1M; dsimp only [F1MProp] at this; exact this.1
  have hS1p : IsPGroup 2 (decSubgroup s1pDecs) :=
    IsPGroup.of_card (n := 13) (by rw [hS1card]; norm_num)
  have hle : Subgroup.centralizer (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) ⊓
      decSubgroup s1pDecs ≤ decSubgroup m1Decs := by
    refine le_m1_of_isPGroup hF1M hF2 hM ?_ (hS1p.to_le inf_le_right)
    exact le_inf inf_le_left (inf_le_right.trans hS)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcentcard, hMcard]

theorem isPi_m1 (hF1 : F1Prop) (hF1M : F1MProp) : IsPi (decSubgroup m1Decs) := by
  have hM := hF1M
  dsimp only [F1MProp] at hM
  obtain ⟨hMcard, hMiff⟩ := hM
  have h1 := hF1
  dsimp only [F1Prop] at h1
  obtain ⟨-, -, -, -, hL1ea, hL1card, -, -⟩ := h1
  have hL1leM : decSubgroup l1Decs ≤ decSubgroup m1Decs := l1_le_m1 hF1M
  have hcenter : Subgroup.center ↥(decSubgroup m1Decs) =
      (decSubgroup l1Decs).subgroupOf (decSubgroup m1Decs) := by
    ext x
    rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
    rw [hMiff ((x : ↥(decSubgroup m1Decs)) : Equiv.Perm (Fin 1782))]
    constructor
    · intro h
      exact ⟨x.2, fun y hy =>
        (congrArg Subtype.val (h ⟨y, hy⟩)).symm⟩
    · rintro ⟨-, h⟩ y
      exact Subtype.ext (h (y : Equiv.Perm (Fin 1782)) y.2).symm
  refine ⟨hMcard, ?_, ?_⟩
  · rw [hcenter]
    exact hL1ea.subgroupOf (decSubgroup m1Decs)
  · rw [hcenter]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL1leM).toEquiv]
    exact hL1card

theorem fixedCard_of_mem_l1 (hF1 : F1Prop) (hF4 : F4Prop) (hF5 : F5Prop)
    {x : Equiv.Perm (Fin 1782)} (hx : x ∈ decSubgroup l1Decs) (hx1 : x ≠ 1) :
    fixedCard x = 54 := by
  have h5 := hF5
  dsimp only [F5Prop] at h5
  obtain ⟨-, hL1T0, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h5
  have h4 := hF4
  dsimp only [F4Prop] at h4
  obtain ⟨-, -, -, h54⟩ := h4
  have h1 := hF1
  dsimp only [F1Prop] at h1
  obtain ⟨-, -, -, -, hL1ea, -, -, -⟩ := h1
  have hxT0 : x ∈ tabSubgroup t0Tabs := hL1T0 hx
  have hx2 : x * x = 1 := by
    have := hL1ea.2 x hx
    simpa [pow_two] using this
  refine h54 ⟨x, hxT0⟩ ?_ ?_
  · exact Subtype.ext hx2
  · intro h
    exact hx1 (congrArg Subtype.val h)

private theorem ncard_conjugatesOf_eq {G : Type*} [Group G] {S : Subgroup G} {e : G}
    (he : e ∈ S) :
    (conjugatesOf (⟨e, he⟩ : S)).ncard =
      Nat.card ↥{x : G | ∃ g ∈ S, x = g * e * g⁻¹} := by
  classical
  have himg : (Subtype.val : S → G) '' (conjugatesOf (⟨e, he⟩ : S)) =
      {x : G | ∃ g ∈ S, x = g * e * g⁻¹} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, hc⟩ := isConj_iff.1 hy
      exact ⟨(c : S), c.2, by
        have hc' := congrArg (fun z : S => (z : G)) hc
        simpa using hc'.symm⟩
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g * e * g⁻¹, S.mul_mem (S.mul_mem hg he) (S.inv_mem hg)⟩, ?_, rfl⟩
      exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext rfl⟩
  calc (conjugatesOf (⟨e, he⟩ : S)).ncard
      = ((Subtype.val : S → G) '' (conjugatesOf (⟨e, he⟩ : S))).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ = {x : G | ∃ g ∈ S, x = g * e * g⁻¹}.ncard := by rw [himg]
    _ = Nat.card ↥{x : G | ∃ g ∈ S, x = g * e * g⁻¹} := (Nat.card_coe_set_eq _).symm

private theorem card_centralizer_subgroup {G : Type*} [Group G] {S : Subgroup G} {e : G}
    (he : e ∈ S) :
    Nat.card ↥(Subgroup.centralizer ({e} : Set G) ⊓ S) =
      Nat.card ↥(Subgroup.centralizer ({⟨e, he⟩} : Set S)) := by
  have hcent_eq : Subgroup.centralizer ({⟨e, he⟩} : Set S) =
      (Subgroup.centralizer ({e} : Set G)).subgroupOf S := by
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  rw [hcent_eq]
  have hsub : (Subgroup.centralizer ({e} : Set G)).subgroupOf S =
      (Subgroup.centralizer ({e} : Set G) ⊓ S).subgroupOf S := by
    ext g
    simp [Subgroup.mem_subgroupOf]
  rw [hsub]
  exact (Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Subgroup.centralizer ({e} : Set G) ⊓ S ≤ S)).toEquiv).symm

private theorem class_card_le_eight (hF1 : F1Prop)
    {P : Subgroup (Equiv.Perm (Fin 1782))} (hPle : P ≤ decSubgroup s1pDecs)
    (hPcard : Nat.card P = 1024) {z : ↥P} (hz : z ∈ Subgroup.center ↥P) :
    Nat.card ↥{x : Equiv.Perm (Fin 1782) |
      ∃ g ∈ decSubgroup s1pDecs, x = g * (z : Equiv.Perm (Fin 1782)) * g⁻¹} ≤ 8 := by
  classical
  have hF1' := hF1
  dsimp only [F1Prop] at hF1'
  obtain ⟨hScard, -, -, -, -, -, -, -⟩ := hF1'
  set S := decSubgroup s1pDecs with hSdef
  have hzS : (z : Equiv.Perm (Fin 1782)) ∈ S := hPle z.2
  let e' : S := ⟨(z : Equiv.Perm (Fin 1782)), hzS⟩
  have hclass := ncard_conjugatesOf_eq hzS
  have hcentcard := card_centralizer_subgroup hzS
  have hPleStab : P.subgroupOf S ≤ Subgroup.centralizer ({e'} : Set S) := by
    intro p hp
    rw [Subgroup.mem_subgroupOf] at hp
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    apply Subtype.ext
    have hc := (Subgroup.mem_center_iff.1 hz) ⟨(p : Equiv.Perm (Fin 1782)), hp⟩
    exact (congrArg Subtype.val hc).symm
  have hP'card : Nat.card ↥(P.subgroupOf S) = 1024 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv, hPcard]
  have hle : 1024 ≤ Nat.card ↥(Subgroup.centralizer ({e'} : Set S)) := by
    rw [← hP'card]
    exact Subgroup.card_le_of_le hPleStab
  have hmul := Subgroup.card_mul_index (Subgroup.centralizer ({e'} : Set S))
  have hidx := Subgroup.index_centralizer_eq_ncard (G := S) e'
  rw [hidx] at hmul
  have hle' : 1024 ≤ Nat.card ↥(Subgroup.centralizer
      ({(z : Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782))) ⊓ S) :=
    hcentcard.symm ▸ hle
  have hprod : Nat.card ↥(Subgroup.centralizer
        ({(z : Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782))) ⊓ S) *
      Nat.card ↥{x : Equiv.Perm (Fin 1782) |
        ∃ g ∈ S, x = g * (z : Equiv.Perm (Fin 1782)) * g⁻¹} = 8192 := by
    rw [hScard] at hmul
    rw [← hcentcard, hclass] at hmul
    exact hmul
  have h1 : 1024 * Nat.card ↥{x : Equiv.Perm (Fin 1782) |
      ∃ g ∈ S, x = g * (z : Equiv.Perm (Fin 1782)) * g⁻¹} ≤ 8192 := by
    calc 1024 * Nat.card ↥{x : Equiv.Perm (Fin 1782) |
          ∃ g ∈ S, x = g * (z : Equiv.Perm (Fin 1782)) * g⁻¹}
        ≤ Nat.card ↥(Subgroup.centralizer
            ({(z : Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782))) ⊓ S) *
          Nat.card ↥{x : Equiv.Perm (Fin 1782) |
            ∃ g ∈ S, x = g * (z : Equiv.Perm (Fin 1782)) * g⁻¹} :=
          Nat.mul_le_mul_right _ hle'
      _ = 8192 := hprod
  have h2 : 1024 * Nat.card ↥{x : Equiv.Perm (Fin 1782) |
      ∃ g ∈ S, x = g * (z : Equiv.Perm (Fin 1782)) * g⁻¹} ≤ 1024 * 8 := by
    rw [show (1024 : ℕ) * 8 = 8192 by norm_num]
    exact h1
  exact Nat.le_of_mul_le_mul_left h2 (by norm_num)

theorem eq_m1_of_isPi (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hS : decSubgroup s1pDecs ≤ invE 1) (hM : decSubgroup m1Decs ≤ invE 1)
    {P : Subgroup (Equiv.Perm (Fin 1782))} (hP : P ≤ decSubgroup s1pDecs) (hPi : IsPi P) :
    P = decSubgroup m1Decs := by
  classical
  have hF1' := hF1
  dsimp only [F1Prop] at hF1'
  obtain ⟨-, -, -, -, -, -, -, hclass9⟩ := hF1'
  have hMcard : Nat.card (decSubgroup m1Decs) = 1024 := by
    have := hF1M; dsimp only [F1MProp] at this; exact this.1
  have hL1card : Nat.card (decSubgroup l1Decs) = 16 := by
    have := hF1; dsimp only [F1Prop] at this; exact this.2.2.2.2.2.1
  have hcenter_le : (Subgroup.center ↥P).map P.subtype ≤ decSubgroup l1Decs := by
    rintro x ⟨w, hw, rfl⟩
    by_cases hw1 : w = 1
    · rw [hw1]
      exact (decSubgroup l1Decs).one_mem
    · by_contra hxL
      have hx2 : ((w : ↥P) : Equiv.Perm (Fin 1782)) *
          ((w : ↥P) : Equiv.Perm (Fin 1782)) = 1 := by
        have hpow := hPi.2.1.2 w hw
        have := congrArg (fun y : ↥P => (y : Equiv.Perm (Fin 1782))) hpow
        simpa [Subgroup.coe_pow, pow_two] using this
      have h9 := hclass9 ((w : ↥P) : Equiv.Perm (Fin 1782)) (hP w.2) hx2
        (fun h => hw1 (Subtype.ext h)) hxL
      have h8 := class_card_le_eight hF1 hP hPi.1 hw
      omega
  have hcenter_card : Nat.card ↥((Subgroup.center ↥P).map P.subtype) = 16 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact hPi.2.2
  have hcenter_eq : (Subgroup.center ↥P).map P.subtype = decSubgroup l1Decs :=
    Subgroup.eq_of_le_of_card_ge hcenter_le (by rw [hL1card, hcenter_card])
  have hPleCent : P ≤
      Subgroup.centralizer (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    rw [← hcenter_eq] at hl
    obtain ⟨w, hw, rfl⟩ := hl
    have hc := (Subgroup.mem_center_iff.1 hw) ⟨p, hp⟩
    exact (congrArg Subtype.val hc).symm
  have hPleM : P ≤ decSubgroup m1Decs := by
    have hle : P ≤ Subgroup.centralizer
        (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) ⊓ decSubgroup s1pDecs :=
      le_inf hPleCent hP
    rwa [centralizer_l1_inf_s1p hF1 hF1M hF2 hS hM] at hle
  exact Subgroup.eq_of_le_of_card_ge hPleM (by rw [hMcard, hPi.1])

private theorem l1_eq_closure_l1BasisPerm :
    decSubgroup l1Decs = Subgroup.closure
      (Set.range fun i : Fin 4 => l1BasisPerm i.val) := by
  rw [decSubgroup]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨d, hd, rfl⟩
    simp only [l1Decs, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · have hb : (fun i : Fin 4 => l1BasisPerm i.val) 0 = decPerm ([], 1) := by
        simp [l1BasisPerm, l1Decs]
      rw [← hb]
      exact Subgroup.subset_closure ⟨0, rfl⟩
    · have hb : (fun i : Fin 4 => l1BasisPerm i.val) 1 = decPerm ([], 10) := by
        simp [l1BasisPerm, l1Decs]
      rw [← hb]
      exact Subgroup.subset_closure ⟨1, rfl⟩
    · have hb : (fun i : Fin 4 => l1BasisPerm i.val) 2 = decPerm ([], 93) := by
        simp [l1BasisPerm, l1Decs]
      rw [← hb]
      exact Subgroup.subset_closure ⟨2, rfl⟩
    · have hb : (fun i : Fin 4 => l1BasisPerm i.val) 3 = decPerm ([8, 9, 8, 9, 4], 99) := by
        simp [l1BasisPerm, l1Decs]
      rw [← hb]
      exact Subgroup.subset_closure ⟨3, rfl⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact Subgroup.subset_closure ⟨([], 1), by simp [l1Decs], by simp [l1BasisPerm, l1Decs]⟩
    · exact Subgroup.subset_closure
        ⟨([], 10), by simp [l1Decs], by simp [l1BasisPerm, l1Decs]⟩
    · exact Subgroup.subset_closure
        ⟨([], 93), by simp [l1Decs], by simp [l1BasisPerm, l1Decs]⟩
    · exact Subgroup.subset_closure
        ⟨([8, 9, 8, 9, 4], 99), by simp [l1Decs], by simp [l1BasisPerm, l1Decs]⟩

theorem card_normalizer_l1 (hF1 : F1Prop) (hF2 : F2Prop)
    (hcard : Nat.card ↥(invE 1) = 3317760) (hL : decSubgroup l1Decs ≤ invE 1) :
    Nat.card ↥(Subgroup.normalizer (decSubgroup l1Decs : Set (Equiv.Perm (Fin 1782))) ⊓
      invE 1) = 73728 := by
  classical
  have hF2' := hF2
  dsimp only [F2Prop] at hF2'
  obtain ⟨-, h24, hCL_eq, hCLcard, -, -⟩ := hF2'
  let G := Equiv.Perm (Fin 1782)
  let b : Fin 4 → G := fun i => l1BasisPerm i.val
  have hL_eq : decSubgroup l1Decs = Subgroup.closure (Set.range b) := by
    dsimp only [b]
    exact l1_eq_closure_l1BasisPerm
  set N := Subgroup.normalizer (decSubgroup l1Decs : Set G) ⊓ invE 1 with hN
  have hCLleN : decSubgroup cl1Decs ≤ N := by
    intro g hg
    have h' := hg
    rw [← hCL_eq] at h'
    exact ⟨Subgroup.centralizer_le_normalizer _ h'.1, h'.2⟩
  let S24 : Set (Fin 4 → G) :=
    {x | (∃ g ∈ invE 1, ∀ i, x i = g * b i * g⁻¹) ∧ ∀ i, x i ∈ decSubgroup l1Decs}
  have hS24 : Nat.card ↥S24 = 24 := h24
  have hstab : ∀ n : ↥N, (∀ i : Fin 4, (n : G) * b i * (n : G)⁻¹ = b i) ↔
      (n : G) ∈ decSubgroup cl1Decs := by
    intro n
    constructor
    · intro h
      have hc : (n : G) ∈ Subgroup.centralizer (decSubgroup l1Decs : Set G) := by
        rw [hL_eq, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨i, rfl⟩ := hy
        have hbg : b i * (n : G) = (n : G) * b i := by
          have h' : (n : G) * b i = b i * (n : G) := mul_inv_eq_iff_eq_mul.1 (h i)
          exact h'.symm
        exact hbg
      have hmem : (n : G) ∈ Subgroup.centralizer (decSubgroup l1Decs : Set G) ⊓ invE 1 :=
        ⟨hc, n.2.2⟩
      rwa [hCL_eq] at hmem
    · intro hn
      have hc : (n : G) ∈ Subgroup.centralizer (decSubgroup l1Decs : Set G) := by
        have h' := hn
        rw [← hCL_eq] at h'
        exact h'.1
      intro i
      have hbL : b i ∈ decSubgroup l1Decs := by
        rw [hL_eq]; exact Subgroup.subset_closure ⟨i, rfl⟩
      have hcomm := (Subgroup.mem_centralizer_iff.1 hc (b i) hbL).symm
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hphi_mem : ∀ g : ↥N, (fun i : Fin 4 => (g : G) * b i * (g : G)⁻¹) ∈ S24 := by
    intro g
    refine ⟨⟨(g : G), g.2.2, fun i => rfl⟩, fun i => ?_⟩
    have hbL : b i ∈ decSubgroup l1Decs := by
      rw [hL_eq]; exact Subgroup.subset_closure ⟨i, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 g.2.1 (b i)).1 hbL
  let φ : ↥N → ↥S24 := fun g => ⟨fun i => (g : G) * b i * (g : G)⁻¹, hphi_mem g⟩
  have hφ_surj : Function.Surjective φ := by
    intro x
    obtain ⟨⟨g, hgC, hgx⟩, hxL⟩ := x.2
    have hgN : g ∈ Subgroup.normalizer (decSubgroup l1Decs : Set G) := by
      refine Subgroup.mem_normalizer_fintype ?_
      intro n hn
      have hconj : decSubgroup l1Decs ≤ Subgroup.comap (MulAut.conj g).toMonoidHom
          (decSubgroup l1Decs) := by
        rw [hL_eq, Subgroup.closure_le]
        rintro y ⟨i, rfl⟩
        have hxi : (MulEquiv.toMonoidHom (MulAut.conj g)) (b i) = x.1 i := by
          change (MulAut.conj g) (b i) = x.1 i
          rw [hgx i]
          rfl
        exact Subgroup.mem_comap.mpr (by
          rw [hxi, ← hL_eq]
          exact hxL i)
      exact hconj hn
    refine ⟨⟨g, ⟨hgN, hgC⟩⟩, ?_⟩
    apply Subtype.ext
    funext i
    exact (hgx i).symm
  have hc_stab : ∀ (c : decSubgroup cl1Decs) (i : Fin 4),
      (c : G) * b i * (c : G)⁻¹ = b i := by
    intro c i
    exact (hstab ⟨c, hCLleN c.2⟩).2 c.2 i
  have hφ_mul_cl : ∀ (g : ↥N) (c : decSubgroup cl1Decs),
      φ (g * ⟨c.1, hCLleN c.2⟩) = φ g := by
    intro g c
    apply Subtype.ext
    funext i
    show (((g * ⟨c.1, hCLleN c.2⟩ : ↥N)) : G) * b i *
        (((g * ⟨c.1, hCLleN c.2⟩ : ↥N)) : G)⁻¹ = (g : G) * b i * (g : G)⁻¹
    rw [Subgroup.coe_mul, mul_inv_rev]
    calc (g : G) * (c : G) * b i * ((c : G)⁻¹ * (g : G)⁻¹)
        = (g : G) * ((c : G) * b i * (c : G)⁻¹) * (g : G)⁻¹ := by group
      _ = (g : G) * b i * (g : G)⁻¹ := by rw [hc_stab c i]
  let QN := (decSubgroup cl1Decs).subgroupOf N
  let ψ : (↥N ⧸ QN) → ↥S24 :=
    Quotient.lift (fun g : ↥N => φ g) (by
      intro g h hgh
      have hkCL : (((g⁻¹ * h : ↥N) : G)) ∈ decSubgroup cl1Decs :=
        Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hgh)
      have hh : h = g * ⟨(((g⁻¹ * h : ↥N) : G)), hCLleN hkCL⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      calc φ g = φ (g * ⟨(((g⁻¹ * h : ↥N) : G)), hCLleN hkCL⟩) :=
            (hφ_mul_cl g ⟨(((g⁻¹ * h : ↥N) : G)), hkCL⟩).symm
        _ = φ h := by rw [← hh])
  have hψ_surj : Function.Surjective ψ := by
    intro x
    obtain ⟨g, hg⟩ := hφ_surj x
    exact ⟨QuotientGroup.mk g, hg⟩
  have hψ_inj : Function.Injective ψ := by
    intro q₁ q₂ hq
    revert hq
    refine Quotient.inductionOn₂' q₁ q₂ ?_
    intro g h hab
    have hphi : φ g = φ h := hab
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    apply (hstab (g⁻¹ * h)).1
    intro i
    have hphi_i : (g : G) * b i * (g : G)⁻¹ = (h : G) * b i * (h : G)⁻¹ := by
      have := congrFun (congrArg Subtype.val hphi) i
      exact this
    have hconj : (((g⁻¹ * h : ↥N) : G)) = (g : G)⁻¹ * (h : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hconj]
    calc (g : G)⁻¹ * (h : G) * b i * ((g : G)⁻¹ * (h : G))⁻¹
        = (g : G)⁻¹ * ((h : G) * b i * (h : G)⁻¹) * (g : G) := by group
      _ = (g : G)⁻¹ * ((g : G) * b i * (g : G)⁻¹) * (g : G) := by rw [← hphi_i]
      _ = b i := by group
  have hψ_bij : Function.Bijective ψ := ⟨hψ_inj, hψ_surj⟩
  have hcard_quot : Nat.card (↥N ⧸ QN) = 24 := by
    rw [Nat.card_congr (Equiv.ofBijective ψ hψ_bij), hS24]
  have hQNcard : Nat.card ↥QN = 3072 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCLleN).toEquiv]
    exact hCLcard
  have hindex : QN.index = 24 := hcard_quot
  have hmul := Subgroup.card_mul_index QN
  rw [hQNcard, hindex] at hmul
  change Nat.card ↥N = 73728
  have hval : Nat.card ↥N = 3072 * 24 := hmul.symm
  rw [hval]

theorem exists_conj_w0 (hF3 : F3Prop)
    (hw : permC 1782 w0T * permC 1782 w0T = 1)
    {x : Equiv.Perm (Fin 1782)} (hxM : x ∈ decSubgroup m1Decs) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hxL : x ∉ decSubgroup l1Decs) :
    ∃ g ∈ decSubgroup nl1Decs, x = g * permC 1782 w0T * g⁻¹ := by
  classical
  have hF3' := hF3
  dsimp only [F3Prop] at hF3'
  obtain ⟨horbcard, horbM, horbL, -, hinvcard⟩ := hF3'
  let W : Equiv.Perm (Fin 1782) := permC 1782 w0T
  let orb : Set (Equiv.Perm (Fin 1782)) :=
    {y | ∃ g ∈ decSubgroup nl1Decs, y = g * W * g⁻¹}
  have horbcard' : Nat.card ↥orb = 288 := horbcard
  have horbM' : ∀ y ∈ orb, y ∈ decSubgroup m1Decs := horbM
  have horbL' : ∀ y ∈ orb, y ∉ decSubgroup l1Decs := horbL
  have huniq : ∀ y ∈ orb, y * y = 1 := by
    intro y hy
    obtain ⟨g, -, rfl⟩ := hy
    calc (g * W * g⁻¹) * (g * W * g⁻¹) = g * (W * W) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [show W * W = 1 from hw]
      _ = 1 := by group
  let Inv := {y : decSubgroup m1Decs // y * y = 1 ∧ y ≠ 1 ∧
    ((y : decSubgroup m1Decs) : Equiv.Perm (Fin 1782)) ∉ decSubgroup l1Decs}
  let InvSet : Set (Equiv.Perm (Fin 1782)) :=
    {y | y ∈ decSubgroup m1Decs ∧ y * y = 1 ∧ y ≠ 1 ∧ y ∉ decSubgroup l1Decs}
  have hInvSet_card : Nat.card ↥InvSet = 288 := by
    let e : Inv ≃ ↥InvSet :=
      { toFun y := ⟨((y.1 : decSubgroup m1Decs) : Equiv.Perm (Fin 1782)), y.1.2,
          congrArg (fun z : decSubgroup m1Decs => (z : Equiv.Perm (Fin 1782))) y.2.1,
          fun h => y.2.2.1 (Subtype.ext h), y.2.2.2⟩
        invFun z := ⟨⟨z.1, z.2.1⟩, Subtype.ext z.2.2.1,
          fun h => z.2.2.2.1 (congrArg Subtype.val h), z.2.2.2.2⟩
        left_inv y := by apply Subtype.ext; rfl
        right_inv z := by apply Subtype.ext; rfl }
    rw [← Nat.card_congr e]
    exact hinvcard
  have hsub : orb ⊆ InvSet := by
    intro y hy
    exact ⟨horbM' y hy, huniq y hy, by
      intro h
      exact horbL' y hy (h ▸ (decSubgroup l1Decs).one_mem), horbL' y hy⟩
  have heq : orb = InvSet := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hInvSet_card, horbcard']
  have hxInvSet : x ∈ InvSet := ⟨hxM, hx2, hx1, hxL⟩
  rw [← heq] at hxInvSet
  exact hxInvSet

end CFSG.Sporadic.SuzRecog.SuzL34Cert
