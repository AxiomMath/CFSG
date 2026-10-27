module

public import CFSG.RankThree.GF2n.Tim77.Defs
public import CFSG.Adapters.Involutions
public import CFSG.Walter.Bender1970.S4.Rank
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.Quasithin.Background.F1Models
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.RankThree.GF2n.Tim77

namespace Tim77Lemma21

open CFSG.CGT.Timmesfeld75 CFSG.Open

structure Hyp (Y : Type) [Group Y] [Finite Y] (D : Set Y) (d₀ : Y) : Prop where
  root : CFSG.Timmesfeld.IsRootInvolutionSet D
  cls : D = {g | IsConj d₀ g}
  solv : Group.IsSolvable Y
  ab : ∀ d ∈ D, IsMulCommutative (Subgroup.closure {e | e ∈ D ∧ e * d = d * e})

instance oddCore_normal' (Y : Type) [Group Y] : (CFSG.oddCore Y).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

theorem mul_self_eq_one_of_orderOf_two {Y : Type} [Group Y] {x : Y}
    (hx : orderOf x = 2) : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [hx, sq] at this

theorem root_order_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n = 2 ∨ n = 4 ∨ Odd n) :
    m = 2 ∨ m = 4 ∨ Odd m := by
  rcases hn with rfl | rfl | hodd
  · rcases (Nat.dvd_prime Nat.prime_two).mp hmn with h | h
    · subst h; exact Or.inr (Or.inr odd_one)
    · exact Or.inl h
  · have h4 : m ∣ 2 ^ 2 := by norm_num; exact hmn
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
    interval_cases j
    · exact Or.inr (Or.inr odd_one)
    · exact Or.inl (by norm_num)
    · exact Or.inr (Or.inl (by norm_num))
  · exact Or.inr (Or.inr (hodd.of_dvd_nat hmn))

theorem odd_card_oddCore (Y : Type) [Group Y] [Finite Y] : Odd (Nat.card (CFSG.oddCore Y)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (CFSG.oddCore Y) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := CFSG.oddCore Y) 2 h2
  have hodd' := CFSG.Adapters.odd_orderOf_of_mem_oddCore x.2
  rw [Subgroup.orderOf_coe, hx] at hodd'
  exact absurd hodd' (by decide)

theorem conj_inv_mem_D {Y : Type} [Group Y] [Finite Y] {D : Set Y} {d₀ : Y}
    (h : Hyp Y D d₀) {g : Y} (hg : g ∈ D) (c : Y) : c⁻¹ * g * c ∈ D := by
  rw [h.cls] at hg ⊢
  have hg' : IsConj d₀ g := hg
  obtain ⟨c₀, rfl⟩ := isConj_iff.mp hg'
  show IsConj d₀ (c⁻¹ * (c₀ * d₀ * c₀⁻¹) * c)
  exact isConj_iff.mpr ⟨c⁻¹ * c₀, by group⟩

theorem commute_of_mem_oddCore {Y : Type} [Group Y] [Finite Y] {D : Set Y} {d₀ : Y}
    (h : Hyp Y D d₀) {d e x : Y} (hd : d ∈ D) (he : e ∈ D) (hde : d * e = e * d)
    (hx : x ∈ CFSG.oddCore Y) (hxd : x * d = d * x) : x * e = e * x := by
  have he' : x⁻¹ * e * x ∈ D := conj_inv_mem_D h he x
  have hxinv : x⁻¹ * d = d * x⁻¹ := (Commute.inv_left (show Commute x d from hxd)).eq
  have hcomm_ed : (x⁻¹ * e * x) * d = d * (x⁻¹ * e * x) := by
    calc x⁻¹ * e * x * d = x⁻¹ * e * (x * d) := by group
      _ = x⁻¹ * e * (d * x) := by rw [hxd]
      _ = x⁻¹ * (e * d) * x := by group
      _ = x⁻¹ * (d * e) * x := by rw [← hde]
      _ = (x⁻¹ * d) * (e * x) := by group
      _ = (d * x⁻¹) * (e * x) := by rw [hxinv]
      _ = d * (x⁻¹ * e * x) := by group
  have hS_e : e ∈ {g : Y | g ∈ D ∧ g * d = d * g} := ⟨he, hde.symm⟩
  have hS_e' : x⁻¹ * e * x ∈ {g : Y | g ∈ D ∧ g * d = d * g} := ⟨he', hcomm_ed⟩
  have key : e * (x⁻¹ * e * x) = (x⁻¹ * e * x) * e :=
    congrArg Subtype.val
      ((h.ab d hd).is_comm.comm ⟨e, Subgroup.subset_closure hS_e⟩
        ⟨x⁻¹ * e * x, Subgroup.subset_closure hS_e'⟩)
  have hee : e * e = 1 := mul_self_eq_one_of_orderOf_two (h.root.1 e he)
  have he'e' : (x⁻¹ * e * x) * (x⁻¹ * e * x) = 1 :=
    mul_self_eq_one_of_orderOf_two (h.root.1 _ he')
  have he_inv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hu_eq : e * (x⁻¹ * e * x) = (e * x⁻¹ * e⁻¹) * x := by rw [he_inv]; group
  have hu : e * (x⁻¹ * e * x) ∈ CFSG.oddCore Y := by
    rw [hu_eq]
    exact Subgroup.mul_mem _ (Subgroup.Normal.conj_mem inferInstance x⁻¹ (inv_mem hx) e) hx
  have hu2 : (e * (x⁻¹ * e * x)) * (e * (x⁻¹ * e * x)) = 1 := by
    calc e * (x⁻¹ * e * x) * (e * (x⁻¹ * e * x))
        = e * ((x⁻¹ * e * x) * e) * (x⁻¹ * e * x) := by group
      _ = e * (e * (x⁻¹ * e * x)) * (x⁻¹ * e * x) := by rw [← key]
      _ = (e * e) * ((x⁻¹ * e * x) * (x⁻¹ * e * x)) := by group
      _ = 1 := by rw [hee, he'e', one_mul]
  have hodd := CFSG.Adapters.odd_orderOf_of_mem_oddCore hu
  have hdvd : orderOf (e * (x⁻¹ * e * x)) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hu2)
  have h1 : orderOf (e * (x⁻¹ * e * x)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
    · exact h'
    · rw [h'] at hodd; exact absurd hodd (by decide)
  have hu1 : e * (x⁻¹ * e * x) = 1 := orderOf_eq_one_iff.mp h1
  have hconj : x⁻¹ * e * x = e := by
    have := eq_inv_of_mul_eq_one_right hu1
    rw [he_inv] at this
    exact this
  calc x * e = x * (x⁻¹ * e * x) := by rw [hconj]
    _ = e * x := by group

theorem oddCore_centralizes_pair {Y : Type} [Group Y] [Finite Y] {D : Set Y} {d₀ : Y}
    (h : Hyp Y D d₀) {d e : Y} (hd : d ∈ D) (he : e ∈ D) (hde : d * e = e * d) (hne : d ≠ e)
    {x : Y} (hx : x ∈ CFSG.oddCore Y) : x * (d * e) = d * e * x := by
  have hd2 : d * d = 1 := mul_self_eq_one_of_orderOf_two (h.root.1 d hd)
  have he2 : e * e = 1 := mul_self_eq_one_of_orderOf_two (h.root.1 e he)
  have hd1 : d ≠ 1 := by
    intro h1
    have := h.root.1 d hd
    rw [h1, orderOf_one] at this
    exact absurd this (by decide)
  have he1 : e ≠ 1 := by
    intro h1
    have := h.root.1 e he
    rw [h1, orderOf_one] at this
    exact absurd this (by decide)
  have hcomm : Commute d e := hde
  have hV := CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions d e hd2 he2
    hd1 he1 hne hcomm
  set V := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions d e hd2 he2 hcomm with hVdef
  have hVmem : ∀ v ∈ V, v = d * e ∨ v = d ∨ v = e ∨ v = 1 := by
    intro v hv
    have : v ∈ ({d * e, d, e, 1} : Set Y) := hv
    simpa using this
  have hcard : 2 ^ 2 ≤ Nat.card V := by
    rw [hV.card_four]
    norm_num
  haveI := hV
  haveI : CFSG.IsElementaryAbelian 2 V :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  letI : MulDistribMulAction V (CFSG.oddCore Y) :=
    MulDistribMulAction.compHom (CFSG.oddCore Y)
      ((MulAut.conjNormal (H := CFSG.oddCore Y)).comp V.subtype)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := V)
    (H := CFSG.oddCore Y) hcard
    (fun h2 => (Nat.not_even_iff_odd.mpr (odd_card_oddCore Y)) (even_iff_two_dvd.mpr h2))
  let K : Subgroup (CFSG.oddCore Y) :=
    (Subgroup.centralizer ({d * e} : Set Y)).comap (CFSG.oddCore Y).subtype
  have hle : (⨆ (a : V) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a)
      (CFSG.oddCore Y)) ≤ K := by
    refine iSup₂_le fun a ha => ?_
    intro y hy
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
    have hay : (a : Y) * (y : Y) * (a : Y)⁻¹ = (y : Y) := congrArg Subtype.val hy
    have hay' : (a : Y) * (y : Y) = (y : Y) * (a : Y) := by
      calc (a : Y) * (y : Y) = (a : Y) * (y : Y) * (a : Y)⁻¹ * (a : Y) := by group
        _ = (y : Y) * (a : Y) := by rw [hay]
    have ha1 : (a : Y) ≠ 1 := fun h1 => ha (Subtype.ext h1)
    have hyO : (y : Y) ∈ CFSG.oddCore Y := y.2
    show (y : Y) ∈ Subgroup.centralizer ({d * e} : Set Y)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rcases hVmem (a : Y) a.2 with h1 | h1 | h1 | h1
    · rw [h1] at hay'
      exact hay'
    · rw [h1] at hay'
      have hye : (y : Y) * e = e * (y : Y) :=
        commute_of_mem_oddCore h hd he hde hyO hay'.symm
      calc d * e * (y : Y) = d * (e * (y : Y)) := by group
        _ = d * ((y : Y) * e) := by rw [← hye]
        _ = (d * (y : Y)) * e := by group
        _ = ((y : Y) * d) * e := by rw [hay']
        _ = (y : Y) * (d * e) := by group
    · rw [h1] at hay'
      have hyd : (y : Y) * d = d * (y : Y) :=
        commute_of_mem_oddCore h he hd hde.symm hyO hay'.symm
      calc d * e * (y : Y) = d * (e * (y : Y)) := by group
        _ = d * ((y : Y) * e) := by rw [hay']
        _ = (d * (y : Y)) * e := by group
        _ = ((y : Y) * d) * e := by rw [← hyd]
        _ = (y : Y) * (d * e) := by group
    · exact absurd h1 ha1
  rw [hgen] at hle
  have hxC : x ∈ Subgroup.centralizer ({d * e} : Set Y) :=
    hle (Subgroup.mem_top (⟨x, hx⟩ : CFSG.oddCore Y))
  exact (Subgroup.mem_centralizer_iff.mp hxC (d * e) (Set.mem_singleton _)).symm

theorem qCoreOf_le_pCore {Y : Type} [Group Y] [Finite Y] (Q : Subgroup Y) (hQ : Q.Normal) :
    CFSG.GorensteinWalter.qCoreOf Q 2 ≤ CFSG.pCore 2 Y := by
  have hchar : (CFSG.pCore 2 ↥Q).Characteristic :=
    CFSG.BaerSuzuki.Helpers.pCore_characteristic 2
  have hpg : IsPGroup 2 (CFSG.GorensteinWalter.qCoreOf Q 2) :=
    IsPGroup.map CFSG.pCore_isPGroup Q.subtype
  have hnorm : (CFSG.GorensteinWalter.qCoreOf Q 2).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    have hφ : (MulAut.conjNormal (H := Q) g) m ∈ CFSG.pCore 2 ↥Q :=
      (Subgroup.characteristic_iff_map_le.mp hchar (MulAut.conjNormal (H := Q) g))
        (Subgroup.mem_map_of_mem _ hm)
    exact Subgroup.mem_map.mpr ⟨(MulAut.conjNormal (H := Q) g) m, hφ,
      MulAut.conjNormal_apply g m⟩
  exact le_sSup ⟨hnorm, hpg⟩

theorem mem_fittingSubgroupOf_of_centralizes {Y : Type} [Group Y] [Finite Y] {Q : Subgroup Y}
    (hsolv : Group.IsSolvable ↥Q) {x : Y} (hxQ : x ∈ Q)
    (hx : ∀ f ∈ CFSG.fittingSubgroupOf Q, f * x = x * f) : x ∈ CFSG.fittingSubgroupOf Q := by
  have hc : (⟨x, hxQ⟩ : ↥Q) ∈
      Subgroup.centralizer ((CFSG.fittingSubgroup ↥Q : Subgroup ↥Q) : Set ↥Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    apply Subtype.ext
    exact hx (g : Y) (Subgroup.mem_map_of_mem Q.subtype hg)
  have hmem := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hc
  exact Subgroup.mem_map_of_mem Q.subtype hmem

theorem odd_card_of_no_involution {Y : Type} [Group Y] [Finite Y] (F : Subgroup Y)
    (h : ∀ x ∈ F, orderOf x ≠ 2) : Odd (Nat.card F) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card F := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := F) 2 h2
  have hxY : orderOf (x : Y) = 2 := by rw [Subgroup.orderOf_coe, hx]
  exact h x x.2 hxY

theorem fittingSubgroupOf_no_involution {Y : Type} [Group Y] [Finite Y] {Q : Subgroup Y}
    (hQ : Q.Normal) (h2 : CFSG.pCore 2 Y = ⊥) {x : Y}
    (hx : x ∈ CFSG.fittingSubgroupOf Q) : orderOf x ≠ 2 := by
  intro hx2
  have hE : Subgroup.zpowers x ≤ CFSG.fittingSubgroupOf Q := Subgroup.zpowers_le.mpr hx
  have hEp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])
  have hxq : x ∈ CFSG.GorensteinWalter.qCoreOf Q 2 :=
    (CFSG.Walter.le_qCoreOf_of_le_fittingSubgroupOf Nat.prime_two hE hEp)
      (Subgroup.mem_zpowers x)
  have hx1 : x ∈ CFSG.pCore 2 Y := qCoreOf_le_pCore Q hQ hxq
  rw [h2, Subgroup.mem_bot] at hx1
  rw [hx1, orderOf_one] at hx2
  exact absurd hx2 (by decide)

theorem eq_of_commute_mem {Y : Type} [Group Y] [Finite Y] {D : Set Y} {d₀ : Y}
    (h : Hyp Y D d₀) (h2 : CFSG.pCore 2 Y = ⊥) {d e : Y} (hd : d ∈ D) (he : e ∈ D)
    (hde : d * e = e * d) : d = e := by
  haveI : Group.IsSolvable Y := h.solv
  by_contra hne
  have hd2 : d * d = 1 := mul_self_eq_one_of_orderOf_two (h.root.1 d hd)
  have he2 : e * e = 1 := mul_self_eq_one_of_orderOf_two (h.root.1 e he)
  set S : Set Y := {x | ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ a * b = b * a ∧ x = a * b} with hS
  have hmemS : d * e ∈ S := ⟨d, hd, e, he, hne, hde, rfl⟩
  have hSconj : ∀ g : Y, ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
    rintro g x ⟨a, ha, b, hb, hab, hcomm, rfl⟩
    have ha' : g * a * g⁻¹ ∈ D := by simpa using conj_inv_mem_D h ha g⁻¹
    have hb' : g * b * g⁻¹ ∈ D := by simpa using conj_inv_mem_D h hb g⁻¹
    refine ⟨g * a * g⁻¹, ha', g * b * g⁻¹, hb', ?_, ?_, ?_⟩
    · intro heq
      apply hab
      have := congrArg (fun y => g⁻¹ * y * g) heq
      simpa using this
    · calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
        _ = g * (b * a) * g⁻¹ := by rw [hcomm]
        _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
    · group
  have hQn : (Subgroup.closure S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj g).toMonoidHom :=
      (Subgroup.closure_le _).mpr fun x hx => Subgroup.subset_closure (hSconj g x hx)
    exact hle hn
  have hQC : Subgroup.closure S ≤
      Subgroup.centralizer ((CFSG.oddCore Y : Subgroup Y) : Set Y) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨a, ha, b, hb, hab, hcomm, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      oddCore_centralizes_pair h ha hb hcomm hab hy
  have ht1 : d * e ≠ 1 := fun h1 =>
    hne (((eq_inv_of_mul_eq_one_right h1).trans (inv_eq_of_mul_eq_one_right hd2)).symm)
  have htt : (d * e) * (d * e) = 1 := by
    calc d * e * (d * e) = d * (e * d) * e := by group
      _ = d * (d * e) * e := by rw [← hde]
      _ = (d * d) * (e * e) := by group
      _ = 1 := by rw [hd2, he2, one_mul]
  have htord : orderOf (d * e) = 2 := by
    have hdvd : orderOf (d * e) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact htt)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
    · exact absurd (orderOf_eq_one_iff.mp h') ht1
    · exact h'
  have ht_mem : d * e ∈ Subgroup.closure S := Subgroup.subset_closure hmemS
  have h2Q : 2 ∣ Nat.card (Subgroup.closure S) := by
    have := orderOf_dvd_natCard (⟨d * e, ht_mem⟩ : Subgroup.closure S)
    rwa [Subgroup.orderOf_mk, htord] at this
  haveI hFn : (CFSG.fittingSubgroupOf (Subgroup.closure S)).Normal :=
    CFSG.fittingSubgroupOf_normal _ hQn
  have hFodd : Odd (Nat.card (CFSG.fittingSubgroupOf (Subgroup.closure S))) :=
    odd_card_of_no_involution _
      (fun x hx => fittingSubgroupOf_no_involution hQn h2 hx)
  have hFO : CFSG.fittingSubgroupOf (Subgroup.closure S) ≤ CFSG.oddCore Y :=
    le_sSup ⟨hFn, hFodd⟩
  have hQF : Subgroup.closure S ≤ CFSG.fittingSubgroupOf (Subgroup.closure S) := by
    intro x hx
    refine mem_fittingSubgroupOf_of_centralizes inferInstance hx ?_
    intro f hf
    exact Subgroup.mem_centralizer_iff.mp (hQC hx) f (hFO hf)
  have hdvdO : Nat.card (Subgroup.closure S) ∣ Nat.card (CFSG.oddCore Y) :=
    Subgroup.card_dvd_of_le (hQF.trans hFO)
  exact (Nat.not_even_iff_odd.mpr ((odd_card_oddCore Y).of_dvd_nat hdvdO))
    (even_iff_two_dvd.mpr h2Q)

theorem sylow_centralizes {Y : Type} [Group Y] [Finite Y] {D : Set Y} {d₀ : Y}
    (h : Hyp Y D d₀) (h2 : CFSG.pCore 2 Y = ⊥) {d : Y} (hd : d ∈ D) {S : Subgroup Y}
    (hS : IsPGroup 2 S) (hdS : d ∈ S) {s : Y} (hs : s ∈ S) : s * d = d * s := by
  haveI : Group.IsSolvable Y := h.solv
  have hyD : s⁻¹ * d * s ∈ D := conj_inv_mem_D h hd s
  have hyS : s⁻¹ * d * s ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hs) hdS) hs
  have hyd : s⁻¹ * d * s = d := by
    by_contra hne
    obtain ⟨y, hy_def⟩ : ∃ y, y = s⁻¹ * d * s := ⟨_, rfl⟩
    rw [← hy_def] at hyD hyS hne
    have hyy : y * y = 1 := mul_self_eq_one_of_orderOf_two (h.root.1 y hyD)
    have hd2 : d * d = 1 := mul_self_eq_one_of_orderOf_two (h.root.1 d hd)
    obtain ⟨t, ht⟩ : ∃ t, t = d * y := ⟨_, rfl⟩
    have ht_mem : t ∈ S := by
      rw [ht]
      exact S.mul_mem hdS hyS
    have ht1 : t ≠ 1 := by
      intro h1
      apply hne
      have hdy : d * y = 1 := ht.symm.trans h1
      exact (eq_inv_of_mul_eq_one_right hdy).trans (inv_eq_of_mul_eq_one_right hd2)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS) ⟨t, ht_mem⟩
    rw [Subgroup.orderOf_mk] at hk
    have hroot := h.root.2.1 d hd y hyD
    rw [← ht] at hroot
    rcases hroot with h4' | h4' | hodd
    ·
      have htt : t * t = 1 := mul_self_eq_one_of_orderOf_two h4'
      have hcomm : d * y = y * d := by
        calc d * y = t := ht.symm
          _ = t⁻¹ := (inv_eq_of_mul_eq_one_right htt).symm
          _ = y⁻¹ * d⁻¹ := by rw [ht, mul_inv_rev]
          _ = y * d := by rw [inv_eq_of_mul_eq_one_right hyy, inv_eq_of_mul_eq_one_right hd2]
      exact hne (eq_of_commute_mem h h2 hd hyD hcomm).symm
    ·
      have hsqD : (d * y) ^ 2 ∈ D := h.root.2.2 d hd y hyD (by rw [← ht]; exact h4')
      rw [sq, ← ht] at hsqD
      have h4'' : t * t * (t * t) = 1 := by
        have h := pow_orderOf_eq_one t
        rw [h4'] at h
        calc t * t * (t * t) = t ^ 2 * t ^ 2 := by rw [sq]
          _ = t ^ (2 + 2) := (pow_add t 2 2).symm
          _ = t ^ 4 := rfl
          _ = 1 := h
      have hu_inv : (t * t)⁻¹ = t * t := inv_eq_of_mul_eq_one_right h4''
      have hdtd : d * t * d⁻¹ = t⁻¹ := by
        rw [ht, mul_inv_rev, inv_eq_of_mul_eq_one_right hyy, inv_eq_of_mul_eq_one_right hd2]
        calc d * (d * y) * d = (d * d) * (y * d) := by group
          _ = y * d := by rw [hd2, one_mul]
      have hcomm_u : d * (t * t) = (t * t) * d := by
        calc d * (t * t) = (d * t * d⁻¹) * (d * t * d⁻¹) * d := by group
          _ = t⁻¹ * t⁻¹ * d := by rw [hdtd]
          _ = (t * t)⁻¹ * d := by group
          _ = (t * t) * d := by rw [hu_inv]
      have hdu : d = t * t := eq_of_commute_mem h h2 hd hsqD hcomm_u
      have htd : t * d = d * t := by
        rw [hdu]
        exact (mul_assoc t t t).symm
      have hy_eq : y = d * t := by
        rw [ht, ← mul_assoc, hd2, one_mul]
      have hyd_comm : d * y = y * d := by
        rw [hy_eq, mul_assoc, htd]
      exact hne (eq_of_commute_mem h h2 hd hyD hyd_comm).symm
    ·
      exfalso
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · have h1 : orderOf t = 1 := by rw [hk, hk0, pow_zero]
        exact ht1 (orderOf_eq_one_iff.mp h1)
      · rw [hk] at hodd
        exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hkpos.ne'⟩)
  calc s * d = s * (s⁻¹ * d * s) := by rw [hyd]
    _ = d * s := by group

theorem mem_center_mk {Y : Type} [Group Y] [Finite Y] {D : Set Y} {d₀ : Y}
    (h : Hyp Y D d₀) (h2 : CFSG.pCore 2 Y = ⊥) {d : Y} (hd : d ∈ D) :
    (QuotientGroup.mk d : Y ⧸ CFSG.oddCore Y) ∈ Subgroup.center (Y ⧸ CFSG.oddCore Y) := by
  haveI : Group.IsSolvable Y := h.solv
  have hdP : IsPGroup 2 (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.root.1 d hd, pow_one])
  obtain ⟨S, hS⟩ := hdP.exists_le_sylow
  have hdS : d ∈ (S : Subgroup Y) := hS (Subgroup.mem_zpowers d)
  have hzZ : (⟨d, hdS⟩ : (S : Subgroup Y)) ∈ Subgroup.center (S : Subgroup Y) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact sylow_centralizes h h2 hd S.isPGroup' hdS g.2
  have hz : orderOf (⟨d, hdS⟩ : (S : Subgroup Y)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h.root.1 d hd
  have hwc : ∀ g : Y, g⁻¹ * ((⟨d, hdS⟩ : (S : Subgroup Y)) : Y) * g ∈ (S : Subgroup Y) →
      g⁻¹ * ((⟨d, hdS⟩ : (S : Subgroup Y)) : Y) * g = d := by
    intro g hg
    have hxD : g⁻¹ * d * g ∈ D := conj_inv_mem_D h hd g
    have hc := Subgroup.mem_center_iff.mp hzZ ⟨g⁻¹ * d * g, hg⟩
    have hcomm : g⁻¹ * d * g * d = d * (g⁻¹ * d * g) := congrArg Subtype.val hc
    exact eq_of_commute_mem h h2 hxD hd hcomm
  exact (CFSG.Adapters.glauberman_zStar S ⟨d, hdS⟩ hzZ hz hwc).2

theorem zStarCase_of_pCore_eq_bot {Y : Type} [Group Y] [Finite Y] {D : Set Y} {d₀ : Y}
    (h : Hyp Y D d₀) (h2 : CFSG.pCore 2 Y = ⊥) (hgen : Subgroup.closure D = ⊤) :
    ZStarCase Y := by
  have hle : Subgroup.closure D ≤ fusionZStar Y := by
    refine (Subgroup.closure_le _).mpr fun d hd => ?_
    exact mem_center_mk h h2 hd
  rw [hgen] at hle
  exact eq_top_iff.mpr hle

theorem d0_mem {Y : Type} [Group Y] [Finite Y] {D : Set Y} {d₀ : Y} (h : Hyp Y D d₀)
    {g : Y} (hg : g ∈ D) (hgN : g ∈ CFSG.pCore 2 Y) : d₀ ∈ CFSG.pCore 2 Y := by
  haveI : (CFSG.pCore 2 Y).Normal := CFSG.pCore_normal
  have hg' : IsConj d₀ g := by
    rw [h.cls] at hg
    exact hg
  obtain ⟨c, hc⟩ := isConj_iff.mp hg'
  have hdc : d₀ = c⁻¹ * g * c := by
    rw [← hc]
    group
  rw [hdc]
  have := Subgroup.Normal.conj_mem inferInstance g hgN c⁻¹
  simpa using this

theorem pCore_quot_bot (Y : Type) [Group Y] [Finite Y] :
    CFSG.pCore 2 (Y ⧸ CFSG.pCore 2 Y) = ⊥ := by
  haveI : (CFSG.pCore 2 Y).Normal := CFSG.pCore_normal
  obtain ⟨K, hK⟩ : ∃ K : Subgroup Y,
      K = (CFSG.pCore 2 (Y ⧸ CFSG.pCore 2 Y)).comap (QuotientGroup.mk' (CFSG.pCore 2 Y)) :=
    ⟨_, rfl⟩
  have hKn : K.Normal := by
    rw [hK]
    infer_instance
  have hKp : IsPGroup 2 K := by
    refine IsPGroup.iff_orderOf.mpr fun g => ?_
    obtain ⟨g, hg⟩ := g
    have hgbar : QuotientGroup.mk' (CFSG.pCore 2 Y) g ∈ CFSG.pCore 2 (Y ⧸ CFSG.pCore 2 Y) := by
      rw [hK] at hg
      exact hg
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp
      (CFSG.pCore_isPGroup (p := 2) (G := Y ⧸ CFSG.pCore 2 Y))) ⟨_, hgbar⟩
    rw [Subgroup.orderOf_mk] at hk
    have hpow : (QuotientGroup.mk' (CFSG.pCore 2 Y) g) ^ (2 ^ k) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one _
    have hgN : g ^ (2 ^ k) ∈ CFSG.pCore 2 Y := by
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 Y) (g ^ (2 ^ k)) = 1 := by
        rw [map_pow]
        exact hpow
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp
      (CFSG.pCore_isPGroup (p := 2) (G := Y))) ⟨g ^ (2 ^ k), hgN⟩
    rw [Subgroup.orderOf_mk] at hj
    have hpow2 : (g ^ (2 ^ k)) ^ (2 ^ j) = 1 := by
      rw [← hj]
      exact pow_orderOf_eq_one _
    have hgord : orderOf g ∣ 2 ^ (k + j) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_add, pow_mul]
      exact hpow2
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hgord
    exact ⟨i, by rw [Subgroup.orderOf_mk]; exact hi⟩
  have hKle : K ≤ CFSG.pCore 2 Y := le_sSup ⟨hKn, hKp⟩
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 Y) z
  have hy : y ∈ K := by
    rw [hK]
    exact hz
  have hyN := hKle hy
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff y).mpr hyN

theorem lift_commute {Y : Type} [Group Y] [Finite Y] {D : Set Y} {d₀ : Y} (h : Hyp Y D d₀)
    (hd0 : d₀ ∉ CFSG.pCore 2 Y) {d e : Y} (hd : d ∈ D) (he : e ∈ D)
    (hcomm : QuotientGroup.mk' (CFSG.pCore 2 Y) e * QuotientGroup.mk' (CFSG.pCore 2 Y) d =
      QuotientGroup.mk' (CFSG.pCore 2 Y) d * QuotientGroup.mk' (CFSG.pCore 2 Y) e) :
    e * d = d * e := by
  haveI : (CFSG.pCore 2 Y).Normal := CFSG.pCore_normal
  have hd2 : d * d = 1 := mul_self_eq_one_of_orderOf_two (h.root.1 d hd)
  have he2 : e * e = 1 := mul_self_eq_one_of_orderOf_two (h.root.1 e he)
  have hπd : QuotientGroup.mk' (CFSG.pCore 2 Y) d * QuotientGroup.mk' (CFSG.pCore 2 Y) d = 1 := by
    rw [← map_mul, hd2, map_one]
  have hπe : QuotientGroup.mk' (CFSG.pCore 2 Y) e * QuotientGroup.mk' (CFSG.pCore 2 Y) e = 1 := by
    rw [← map_mul, he2, map_one]
  have hsq : QuotientGroup.mk' (CFSG.pCore 2 Y) ((d * e) * (d * e)) = 1 := by
    calc QuotientGroup.mk' (CFSG.pCore 2 Y) ((d * e) * (d * e))
        = QuotientGroup.mk' (CFSG.pCore 2 Y) d * (QuotientGroup.mk' (CFSG.pCore 2 Y) e *
            QuotientGroup.mk' (CFSG.pCore 2 Y) d) * QuotientGroup.mk' (CFSG.pCore 2 Y) e := by
          simp only [map_mul]
          group
      _ = QuotientGroup.mk' (CFSG.pCore 2 Y) d * (QuotientGroup.mk' (CFSG.pCore 2 Y) d *
            QuotientGroup.mk' (CFSG.pCore 2 Y) e) * QuotientGroup.mk' (CFSG.pCore 2 Y) e := by
          rw [hcomm]
      _ = (QuotientGroup.mk' (CFSG.pCore 2 Y) d * QuotientGroup.mk' (CFSG.pCore 2 Y) d) *
            (QuotientGroup.mk' (CFSG.pCore 2 Y) e * QuotientGroup.mk' (CFSG.pCore 2 Y) e) := by
          group
      _ = 1 := by rw [hπd, hπe, one_mul]
  have hsqN : (d * e) * (d * e) ∈ CFSG.pCore 2 Y := (QuotientGroup.eq_one_iff _).mp hsq
  rcases h.root.2.1 d hd e he with htt | h4 | hodd
  · have hdd := mul_self_eq_one_of_orderOf_two htt
    calc e * d = (d * e)⁻¹ := by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right he2, inv_eq_of_mul_eq_one_right hd2]
      _ = d * e := inv_eq_of_mul_eq_one_right hdd
  · have hsqD : (d * e) ^ 2 ∈ D := h.root.2.2 d hd e he h4
    rw [sq] at hsqD
    exact absurd (d0_mem h hsqD hsqN) hd0
  · obtain ⟨j, hj⟩ := hodd
    have hexp : 2 * (j + 1) = orderOf (d * e) + 1 := by omega
    have hdeN : d * e ∈ CFSG.pCore 2 Y := by
      have h1 : (d * e) ^ (2 * (j + 1)) ∈ CFSG.pCore 2 Y := by
        rw [pow_mul, sq]
        exact (CFSG.pCore 2 Y).pow_mem hsqN (j + 1)
      have h2' : (d * e) ^ (2 * (j + 1)) = d * e := by
        rw [hexp, pow_succ, pow_orderOf_eq_one, one_mul]
      rw [h2'] at h1
      exact h1
    obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp
      (CFSG.pCore_isPGroup (p := 2) (G := Y))) ⟨d * e, hdeN⟩
    rw [Subgroup.orderOf_mk] at hi
    have hord1 : orderOf (d * e) = 1 := by
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · rw [hi, hi0, pow_zero]
      · exfalso
        have hev : Even (orderOf (d * e)) := by
          rw [hi]
          exact Nat.even_pow.mpr ⟨even_two, hipos.ne'⟩
        exact (Nat.not_even_iff_odd.mpr ⟨j, hj⟩) hev
    have hde1 : d * e = 1 := orderOf_eq_one_iff.mp hord1
    have hed : e = d := by
      have := eq_inv_of_mul_eq_one_right hde1
      rw [inv_eq_of_mul_eq_one_right hd2] at this
      exact this
    rw [hed]

theorem quot_root {Y : Type} [Group Y] [Finite Y] {D : Set Y} {d₀ : Y} (h : Hyp Y D d₀)
    (hd0 : d₀ ∉ CFSG.pCore 2 Y) :
    CFSG.Timmesfeld.IsRootInvolutionSet (QuotientGroup.mk' (CFSG.pCore 2 Y) '' D) := by
  haveI : (CFSG.pCore 2 Y).Normal := CFSG.pCore_normal
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 Y) d) ∣ orderOf d :=
      orderOf_map_dvd _ d
    rw [h.root.1 d hd] at hdvd
    have hne : QuotientGroup.mk' (CFSG.pCore 2 Y) d ≠ 1 := by
      intro h1
      exact hd0 (d0_mem h hd ((QuotientGroup.eq_one_iff d).mp h1))
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
    · exact absurd (orderOf_eq_one_iff.mp h') hne
    · exact h'
  · rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
    rw [← map_mul]
    exact root_order_of_dvd (orderOf_map_dvd _ _) (h.root.2.1 d hd e he)
  · rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩ h4
    rw [← map_mul] at h4 ⊢
    have h4d : orderOf (QuotientGroup.mk' (CFSG.pCore 2 Y) (d * e)) ∣ orderOf (d * e) :=
      orderOf_map_dvd _ _
    rw [h4] at h4d
    have hn4 : orderOf (d * e) = 4 := by
      rcases h.root.2.1 d hd e he with h' | h' | ⟨j, hj⟩
      · rw [h'] at h4d
        omega
      · exact h'
      · omega
    have hsqD : (d * e) ^ 2 ∈ D := h.root.2.2 d hd e he hn4
    exact ⟨(d * e) ^ 2, hsqD, map_pow _ (d * e) 2⟩

theorem quot_cls {Y : Type} [Group Y] [Finite Y] {D : Set Y} {d₀ : Y} (h : Hyp Y D d₀) :
    QuotientGroup.mk' (CFSG.pCore 2 Y) '' D =
      {g | IsConj (QuotientGroup.mk' (CFSG.pCore 2 Y) d₀) g} := by
  haveI : (CFSG.pCore 2 Y).Normal := CFSG.pCore_normal
  ext g
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hd' : IsConj d₀ d := by
      rw [h.cls] at hd
      exact hd
    obtain ⟨c, hc⟩ := isConj_iff.mp hd'
    show IsConj _ _
    refine isConj_iff.mpr ⟨QuotientGroup.mk' (CFSG.pCore 2 Y) c, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hc]
  · intro hg
    obtain ⟨cb, hcb⟩ := isConj_iff.mp hg
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 Y) cb
    have hd0D : d₀ ∈ D := by
      rw [h.cls]
      exact IsConj.refl d₀
    have hmem : c * d₀ * c⁻¹ ∈ D := by
      simpa using conj_inv_mem_D h hd0D c⁻¹
    refine ⟨c * d₀ * c⁻¹, hmem, ?_⟩
    rw [← hcb]
    simp [map_mul, map_inv]

theorem quot_gen {Y : Type} [Group Y] [Finite Y] {D : Set Y} (hgen : Subgroup.closure D = ⊤) :
    Subgroup.closure (QuotientGroup.mk' (CFSG.pCore 2 Y) '' D) = ⊤ := by
  haveI : (CFSG.pCore 2 Y).Normal := CFSG.pCore_normal
  rw [← MonoidHom.map_closure, hgen]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem isMulCommutative_closure_of_subset {G : Type} [Group G] {T : Set G} {K : Subgroup G}
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hT : T ⊆ K) :
    IsMulCommutative (Subgroup.closure T) := by
  have hle : Subgroup.closure T ≤ K := (Subgroup.closure_le _).mpr hT
  exact ⟨⟨fun a b => Subtype.ext (hK a (hle a.2) b (hle b.2))⟩⟩

theorem quot_ab {Y : Type} [Group Y] [Finite Y] {D : Set Y} {d₀ : Y} (h : Hyp Y D d₀)
    (hd0 : d₀ ∉ CFSG.pCore 2 Y) :
    ∀ db ∈ QuotientGroup.mk' (CFSG.pCore 2 Y) '' D,
      IsMulCommutative (Subgroup.closure
        {eb | eb ∈ QuotientGroup.mk' (CFSG.pCore 2 Y) '' D ∧ eb * db = db * eb}) := by
  haveI : (CFSG.pCore 2 Y).Normal := CFSG.pCore_normal
  rintro _ ⟨d, hd, rfl⟩
  have hHc : ∀ a ∈ Subgroup.closure {e | e ∈ D ∧ e * d = d * e},
      ∀ b ∈ Subgroup.closure {e | e ∈ D ∧ e * d = d * e}, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val ((h.ab d hd).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  apply isMulCommutative_closure_of_subset
    (K := (Subgroup.closure {e | e ∈ D ∧ e * d = d * e}).map
      (QuotientGroup.mk' (CFSG.pCore 2 Y)))
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hHc a ha b hb]
  · rintro _ ⟨⟨e, he, rfl⟩, hcomm⟩
    exact Subgroup.mem_map_of_mem _
      (Subgroup.subset_closure ⟨he, lift_commute h hd0 hd he hcomm⟩)

theorem quot_hyp {Y : Type} [Group Y] [Finite Y] {D : Set Y} {d₀ : Y} (h : Hyp Y D d₀)
    (hd0 : d₀ ∉ CFSG.pCore 2 Y) :
    Hyp (Y ⧸ CFSG.pCore 2 Y) (QuotientGroup.mk' (CFSG.pCore 2 Y) '' D)
      (QuotientGroup.mk' (CFSG.pCore 2 Y) d₀) := by
  haveI : (CFSG.pCore 2 Y).Normal := CFSG.pCore_normal
  haveI : Group.IsSolvable Y := h.solv
  exact ⟨quot_root h hd0, quot_cls h, Group.isSolvable_of_surjective
    (QuotientGroup.mk'_surjective (CFSG.pCore 2 Y)), quot_ab h hd0⟩

end Tim77Lemma21

open Tim77Lemma21 in
theorem tim77Lemma21_holds : Tim77Lemma21Statement := by
  intro Y _ _ D hD hcls hgen hsolv hab
  obtain ⟨d₀, hD₀⟩ := hcls
  haveI : (CFSG.pCore 2 Y).Normal := CFSG.pCore_normal
  have h : Hyp Y D d₀ := ⟨hD, hD₀, hsolv, hab⟩
  by_cases hd0 : d₀ ∈ CFSG.pCore 2 Y
  ·
    have hDle : Subgroup.closure D ≤ CFSG.pCore 2 Y := by
      refine (Subgroup.closure_le _).mpr fun d hd => ?_
      have hdc : IsConj d₀ d := by
        rw [hD₀] at hd
        exact hd
      obtain ⟨c, rfl⟩ := isConj_iff.mp hdc
      exact Subgroup.Normal.conj_mem inferInstance d₀ hd0 c
    rw [hgen] at hDle
    have htop : CFSG.pCore 2 Y = ⊤ := eq_top_iff.mpr hDle
    haveI : Subsingleton (Y ⧸ CFSG.pCore 2 Y) := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 Y) a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 Y) b
      exact (QuotientGroup.eq).mpr (by rw [htop]; exact Subgroup.mem_top _)⟩
    exact eq_top_iff.mpr fun x _ => by
      rw [Subsingleton.elim x 1]
      exact one_mem _
  ·
    exact zStarCase_of_pCore_eq_bot (quot_hyp h hd0) (pCore_quot_bot Y) (quot_gen hgen)

end CFSG.RankThree.GF2n.Tim77

end
