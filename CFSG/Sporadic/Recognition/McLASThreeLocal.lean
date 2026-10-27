module

public import CFSG.Sporadic.Recognition.McLASEnum
public import CFSG.Sporadic.Recognition.McLASClasses

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem eq_or_eq_inv_of_mem_zpowers {M : Type*} [Group M] {x y : M} (hx : orderOf x = 3)
    (hy : y ∈ zpowers x) (hyo : orderOf y = 3) : y = x ∨ y = x⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  have hx3 : x ^ 3 = 1 := by rw [← hx, pow_orderOf_eq_one]
  have hk : x ^ k = x ^ (k % 3) := by
    rw [← zpow_mod_orderOf, hx]; rfl
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [hk, h0, zpow_zero, orderOf_one] at hyo
    exact absurd hyo (by norm_num)
  · left; rw [hk, h1, zpow_one]
  · right
    rw [hk, h2]
    have : x ^ (2 : ℤ) * x = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, ← pow_succ]
      exact hx3
    exact eq_inv_of_mul_eq_one_left this

theorem mem_normalizer_zpowers_iff {M : Type*} [Group M] {x g : M} :
    g ∈ normalizer (zpowers x : Set M) ↔ g * x * g⁻¹ ∈ zpowers x ∧ g⁻¹ * x * g ∈ zpowers x := by
  constructor
  · intro hg
    exact ⟨(mem_normalizer_iff.1 hg x).1 (mem_zpowers x),
      (mem_normalizer_iff''.1 hg x).1 (mem_zpowers x)⟩
  · rintro ⟨h1, h2⟩
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      rw [← conj_zpow]
      exact zpow_mem h1 k
    · intro hy
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy
      have : y = (g⁻¹ * x * g) ^ k := by
        have hc := conj_zpow (a := g⁻¹) (b := x) (i := k)
        rw [inv_inv] at hc
        rw [hc, hk]
        group
      rw [this]
      exact zpow_mem h2 k

theorem card_normalizer_zpowers_of_inverting {M : Type*} [Group M] [Finite M] {Q : Subgroup M}
    {x h : M} (hx : orderOf x = 3) (hh : h ∈ Q) (hinv : h * x * h⁻¹ = x⁻¹) :
    Nat.card ↥(Q ⊓ normalizer (zpowers x : Set M)) =
      2 * Nat.card ↥(Q ⊓ centralizer ({x} : Set M)) := by
  set N : Subgroup M := Q ⊓ normalizer (zpowers x : Set M) with hN
  set C : Subgroup M := Q ⊓ centralizer ({x} : Set M) with hC
  have hxne : x⁻¹ ≠ x := by
    intro h1
    have h2 : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel x
    have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hx] at this
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by norm_num)
  have hinv' : h⁻¹ * x * h = x⁻¹ := by
    have h1 : h * x⁻¹ * h⁻¹ = x := by
      have := congrArg (fun z => z⁻¹) hinv
      simpa [mul_assoc] using this
    calc h⁻¹ * x * h = h⁻¹ * (h * x⁻¹ * h⁻¹) * h := by rw [h1]
      _ = x⁻¹ := by group
  have hxz : x⁻¹ ∈ zpowers x := inv_mem (mem_zpowers x)
  have hmemC : ∀ g : M, g ∈ C ↔ g ∈ Q ∧ g * x * g⁻¹ = x := by
    intro g
    rw [hC, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hgQ, hg⟩
      exact ⟨hgQ, by rw [hg]; group⟩
    · rintro ⟨hgQ, hg⟩
      exact ⟨hgQ, mul_inv_eq_iff_eq_mul.1 hg⟩
  have hCN : C ≤ N := by
    intro g hg
    obtain ⟨hgQ, hgx⟩ := (hmemC g).1 hg
    have hgc : g * x = x * g := mul_inv_eq_iff_eq_mul.1 hgx
    have hgx' : g⁻¹ * x * g = x := by
      calc g⁻¹ * x * g = g⁻¹ * (x * g) := by rw [mul_assoc]
        _ = g⁻¹ * (g * x) := by rw [hgc]
        _ = x := by rw [inv_mul_cancel_left]
    refine mem_inf.2 ⟨hgQ, ?_⟩
    rw [mem_normalizer_zpowers_iff, hgx, hgx']
    exact ⟨mem_zpowers x, mem_zpowers x⟩
  have hhN : h ∈ N := by
    refine mem_inf.2 ⟨hh, ?_⟩
    rw [mem_normalizer_zpowers_iff, hinv, hinv']
    exact ⟨hxz, hxz⟩
  have hidx : (C.subgroupOf N).index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨⟨h, hhN⟩, fun b => ?_⟩
    have hbQ : (b : M) ∈ Q := (mem_inf.1 b.2).1
    have hb1 := (mem_normalizer_zpowers_iff.1 (mem_inf.1 b.2).2).1
    have hbord : orderOf ((b : M) * x * (b : M)⁻¹) = 3 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
    have hbn := eq_or_eq_inv_of_mem_zpowers hx hb1 hbord
    simp only [mem_subgroupOf, Subgroup.coe_mul]
    rcases hbn with hb | hb
    · have hbC : (b : M) ∈ C := (hmemC _).2 ⟨hbQ, hb⟩
      right
      refine ⟨hbC, fun hbh => ?_⟩
      obtain ⟨-, hbh2⟩ := (hmemC _).1 hbh
      apply hxne
      calc x⁻¹ = ((b : M) * x * (b : M)⁻¹)⁻¹ := by rw [hb]
        _ = (b : M) * x⁻¹ * (b : M)⁻¹ := by group
        _ = (b : M) * (h * x * h⁻¹) * (b : M)⁻¹ := by rw [hinv]
        _ = (b : M) * h * x * ((b : M) * h)⁻¹ := by group
        _ = x := hbh2
    · left
      have hbhC : (b : M) * h ∈ C := (hmemC _).2 ⟨Q.mul_mem hbQ hh, by
        calc (b : M) * h * x * ((b : M) * h)⁻¹ = (b : M) * (h * x * h⁻¹) * (b : M)⁻¹ := by group
          _ = (b : M) * x⁻¹ * (b : M)⁻¹ := by rw [hinv]
          _ = ((b : M) * x * (b : M)⁻¹)⁻¹ := by group
          _ = x := by rw [hb]; group⟩
      refine ⟨hbhC, fun hbC => ?_⟩
      obtain ⟨-, hbx⟩ := (hmemC _).1 hbC
      exact hxne (hb.symm.trans hbx)
  have hcard := Subgroup.card_mul_index (C.subgroupOf N)
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv] at hcard
  omega

theorem centralizer_le_normalizer_zpowers {M : Type*} [Group M] (x : M) :
    centralizer ({x} : Set M) ≤ normalizer (zpowers x : Set M) := by
  intro g hg
  have hgc : g * x = x * g := mem_centralizer_singleton_iff.1 hg
  have h1 : g * x * g⁻¹ = x := by rw [hgc]; group
  have h2 : g⁻¹ * x * g = x := by
    calc g⁻¹ * x * g = g⁻¹ * (x * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * x) := by rw [hgc]
      _ = x := by rw [inv_mul_cancel_left]
  rw [mem_normalizer_zpowers_iff, h1, h2]
  exact ⟨mem_zpowers x, mem_zpowers x⟩

theorem normalizer_zpowers_cases {M : Type*} [Group M] {x g : M} (hx : orderOf x = 3)
    (hg : g ∈ normalizer (zpowers x : Set M)) : g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹ := by
  have hord : orderOf (g * x * g⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  exact eq_or_eq_inv_of_mem_zpowers hx (mem_normalizer_zpowers_iff.1 hg).1 hord

theorem mem_centralizer_or_of_mem_normalizer {M : Type*} [Group M] {Q : Subgroup M} {x h g : M}
    (hx : orderOf x = 3) (hh : h ∈ Q) (hinv : h * x * h⁻¹ = x⁻¹)
    (hg : g ∈ Q ⊓ normalizer (zpowers x : Set M)) :
    g ∈ Q ⊓ centralizer ({x} : Set M) ∨ h⁻¹ * g ∈ Q ⊓ centralizer ({x} : Set M) := by
  obtain ⟨hgQ, hgn⟩ := mem_inf.1 hg
  rcases normalizer_zpowers_cases hx hgn with h1 | h1
  · left
    exact mem_inf.2 ⟨hgQ, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h1)⟩
  · right
    refine mem_inf.2 ⟨Q.mul_mem (Q.inv_mem hh) hgQ, mem_centralizer_singleton_iff.2 ?_⟩
    have hinv' : h⁻¹ * x * h = x⁻¹ := by
      have h1' : h * x⁻¹ * h⁻¹ = x := by
        have := congrArg (fun z => z⁻¹) hinv
        simpa [mul_assoc] using this
      calc h⁻¹ * x * h = h⁻¹ * (h * x⁻¹ * h⁻¹) * h := by rw [h1']
        _ = x⁻¹ := by group
    have : h⁻¹ * g * x * (h⁻¹ * g)⁻¹ = x := by
      calc h⁻¹ * g * x * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * x * g⁻¹) * h := by group
        _ = h⁻¹ * x⁻¹ * h := by rw [h1]
        _ = (h⁻¹ * x * h)⁻¹ := by group
        _ = x := by rw [hinv', inv_inv]
    exact mul_inv_eq_iff_eq_mul.1 this

noncomputable abbrev gx : Subgroup (Equiv.Perm (Fin 275)) :=
  mclP ⊓ normalizer (zpowers three₁ : Set (Equiv.Perm (Fin 275)))

noncomputable abbrev gxh : Subgroup (Equiv.Perm (Fin 275)) :=
  mclR ⊓ normalizer (zpowers three₁ : Set (Equiv.Perm (Fin 275)))

theorem relIndex_mclP_mclR :
    mclP.relIndex mclR = 2 := by
  have hPR : mclP ≤ mclR := le_sup_left
  have hcardR : Nat.card mclR = 1796256000 := by
    obtain ⟨-, -, -, -, -, -, -, -, hR, -⟩ := mcl_normalizing_model
    exact hR
  have h1 := Subgroup.relIndex_mul_card (H := mclP) (K := mclR)
  have hc' : Nat.card ↥(mclP ⊓ mclR) = 898128000 := by
    rw [inf_of_le_left hPR]; exact card_mclP
  rw [hcardR, hc'] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 898128000)
    (h1.trans (by norm_num : 1796256000 = 2 * 898128000))

theorem gxCheck_spec
    (h : gxCheck = true) :
    (tp 275 invHTab ∈ mclP ∧ tp 275 invHTab * three₁ * (tp 275 invHTab)⁻¹ = three₁⁻¹ ∧
      Rep 275 invHTab (tp 275 invHTab) ∧ Rep 275 (invT 275 invHTab) (tp 275 invHTab)⁻¹) ∧
      (tp 275 outerOTab ∈ mclR ∧ tp 275 outerOTab ∉ mclP ∧
        tp 275 outerOTab * three₁ = three₁ * tp 275 outerOTab) := by
  have hD : GroupData 275 mclP mclPGTbls mclGen mclSift := mcl_groupData
  simp only [gxCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h0'⟩, hu⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  have hx : Rep 275 (threeTbl 0) three₁ := rep_tp h0
  have hxi : Rep 275 (invT 275 (threeTbl 0)) three₁⁻¹ := Rep.inv_of_invOK hx h0'
  have hh : Rep 275 invHTab (tp 275 invHTab) := rep_tp h1
  have hhi : Rep 275 (invT 275 invHTab) (tp 275 invHTab)⁻¹ := Rep.inv_of_invOK hh h2
  have hoR : Rep 275 outerOTab (tp 275 outerOTab) := rep_tp h5
  obtain ⟨hU2, -, hUP, hmap, -⟩ := mcl_normalizing_model
  have hUn : ∀ p ∈ mclP, mclU * p * mclU⁻¹ ∈ mclP := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  have hUrep : Rep 275 mclOuterTbl mclU := rep_tp hu
  refine ⟨⟨(hD.sift _ _ hh).1 h3, (tblEq_iff_eq (rep_conjT hh hhi hx) hxi).1 h4, hh, hhi⟩,
    ?_, ?_, ?_⟩
  · exact mem_R_of_sift hD hU2 hUn hUrep hoR (by rw [h9, Bool.or_true])
  · intro hm
    have := (hD.sift _ _ hoR).2 hm
    rw [h8] at this
    exact Bool.noConfusion this
  · exact (commTT_iff hoR hx).1 h7

theorem three₁_facts (h : ThreeFacts) :
    three₁ ∈ mclP ∧ orderOf three₁ = 3 ∧
      Nat.card ↥(mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275)))) = 29160 ∧
      (conjClass mclP three₁).ncard = 30800 := by
  have f₁ := h.row₁
  have c₁ := f₁.cent
  have k₁ := f₁.cls
  have m₁ := f₁.mem
  have o₁ := f₁.order
  dsimp only [threeRow₁] at c₁ k₁ m₁ o₁
  exact ⟨m₁, o₁, c₁, k₁⟩

theorem card_gx
    (hrows : ThreeFacts) (hg : gxCheck = true) :
    Nat.card gx = 58320 ∧ Nat.card gxh = 116640 := by
  obtain ⟨hxP, hx3, hc, -⟩ := three₁_facts hrows
  obtain ⟨⟨hh₀, hinv, -, -⟩, ⟨hoR, hoP, hoc⟩⟩ := gxCheck_spec hg
  have hPR : mclP ≤ mclR := le_sup_left
  have hCR : Nat.card ↥(mclR ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275)))) = 58320 := by
    have hidx := relIndex_mclP_mclR
    have hoC : tp 275 outerOTab ∈ mclR ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))) :=
      mem_inf.2 ⟨hoR, mem_centralizer_singleton_iff.2 hoc⟩
    have := card_inf_mul_two hidx (inf_le_left : mclR ⊓ centralizer ({three₁} :
      Set (Equiv.Perm (Fin 275))) ≤ mclR) hoC hoP
    have e : mclP ⊓ (mclR ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275)))) =
        mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))) := by
      ext y
      simp only [mem_inf]
      exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, hPR a, c⟩⟩
    rw [e, hc] at this
    omega
  constructor
  · rw [card_normalizer_zpowers_of_inverting hx3 hh₀ hinv, hc]
  · rw [card_normalizer_zpowers_of_inverting hx3 (hPR hh₀) hinv, hCR]

noncomputable abbrev sylowT : Subgroup (Equiv.Perm (Fin 275)) :=
  closure (tp 275 '' {x | x ∈ sylowThreeGens.toArray})

noncomputable abbrev subR3 : Subgroup (Equiv.Perm (Fin 275)) :=
  closure (tp 275 '' {x | x ∈ rGens3})

noncomputable abbrev subA3 : Subgroup (Equiv.Perm (Fin 275)) :=
  closure (tp 275 '' {x | x ∈ aGens3})

theorem memT_iff_mem_conjClass {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))}
    {tg : Equiv.Perm (Fin n)} {o : Closure}
    (horb : ∀ k < o.1.size, ∃ c ∈ P, Rep n o.1[k]! (c * tg * c⁻¹))
    (hcover : ∀ y ∈ conjClass P tg, ∃ k < o.1.size, Rep n o.1[k]! y) {t : Table}
    {g : Equiv.Perm (Fin n)} (ht : Rep n t g) : memT n o.1 t = true ↔ g ∈ conjClass P tg := by
  have hrep : ∀ k < o.1.size, Rep n o.1[k]! (tablePerm n o.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hcrep⟩ := horb k hk
    rw [tablePerm_eq hcrep]
    exact hcrep
  constructor
  · intro hmem
    obtain ⟨j, hj, hg⟩ := memT_spec hrep ht hmem
    obtain ⟨c, hc, hcrep⟩ := horb j hj
    rw [tablePerm_eq hcrep] at hg
    exact ⟨c, hc, hg⟩
  · intro hy
    obtain ⟨k, hk, hkrep⟩ := hcover g hy
    rw [memT, Array.any_eq_true]
    refine ⟨k, hk, ?_⟩
    rw [getElem!_pos o.1 k hk] at hkrep
    exact (tblEq_iff_eq ht hkrep).2 rfl

theorem threeEnumCheck_spec
    (hrows : ThreeFacts) (h : threeEnumCheck = true) :
    SubEnumFacts 275 mclP sylowThreeGens.toArray enumT.1 729 sylowT ∧
    SubEnumFacts 275 mclP rGens3 enumR3.1 243 subR3 ∧
    SubEnumFacts 275 mclP aGens3 enumA3.1 81 subA3 ∧
    Rep 275 (threeTbl 0) three₁ ∧ Rep 275 (invT 275 (threeTbl 0)) three₁⁻¹ ∧
    (∀ (t : Table) (g : Equiv.Perm (Fin 275)), Rep 275 t g →
      (memT 275 enumClass.1 t = true ↔ g ∈ conjClass mclP three₁)) := by
  have hD : GroupData 275 mclP mclPGTbls mclGen mclSift := mcl_groupData
  simp only [threeEnumCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h5'⟩, h6⟩, h7⟩, h8⟩ := h
  have hpgi : ∀ l < mclPGTbls.size, Rep 275 mclPGInvTbls[l]! (mclGen l)⁻¹ := fun l hl =>
    Rep.inv_of_invOK (hD.rep l hl) (allIn_eq_true.1 h4 l (Nat.zero_le _) hl)
  have hx : Rep 275 (threeTbl 0) three₁ := rep_tp h5
  obtain ⟨-, -, -, k₁⟩ := three₁_facts hrows
  obtain ⟨horb, hcover⟩ := conjClosure_cover hD hpgi hx h6 h7 (by rw [k₁, h8])
  exact ⟨subEnumOK_spec hD h1, subEnumOK_spec hD h2, subEnumOK_spec hD h3, hx,
    Rep.inv_of_invOK hx h5', fun t g ht => memT_iff_mem_conjClass horb hcover ht⟩

theorem mem_normalizer_of_map_le {M : Type*} [Group M] [Finite M] {H : Subgroup M} {g : M}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ normalizer (H : Set M) := by
  rw [mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge h
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

theorem mem_normalizer_closure {M : Type*} [Group M] [Finite M] {S : Set M} {g : M}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ closure S) : g ∈ normalizer (closure S : Set M) := by
  refine mem_normalizer_of_map_le ?_
  rw [MonoidHom.map_closure, closure_le]
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

theorem rInTCheck_spec
    (hrows : ThreeFacts) (he : threeEnumCheck = true) (h : rInTCheck = true) :
    subR3 ≤ sylowT ∧ subA3 ≤ sylowT ∧
      subR3 ≤ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))) ∧
      sylowT ≤ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))) := by
  obtain ⟨hT, hR, hA, hx, -, -⟩ := threeEnumCheck_spec hrows he
  simp only [rInTCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hin : ∀ {E : Array Table} {K : Subgroup (Equiv.Perm (Fin 275))},
      EnumFacts 275 E K → E.all (memT 275 enumT.1) = true → K ≤ sylowT := by
    intro E K hE hall y hy
    obtain ⟨k, hk, hkrep⟩ := hE.cover y hy
    exact hT.enum.mem_of_memT hkrep (Array.all_eq_true'.1 hall E[k]! (getElem!_mem_array hk))
  have hcomm : ∀ {sg : Array Table}, (∀ g ∈ sg, Rep 275 g (tp 275 g)) →
      (∀ g ∈ sg, commTT 275 (threeTbl 0) g = true) →
      closure (tp 275 '' {x | x ∈ sg}) ≤ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))) := by
    intro sg hrep hall
    rw [closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact ((commTT_iff hx (hrep g hg)).1 (hall g hg)).symm
  refine ⟨hin hR.enum h1, hin hA.enum h2, hcomm hR.rep (Array.all_eq_true'.1 h3),
    hcomm hT.rep ?_⟩
  intro g hg
  rw [List.all_eq_true] at h4
  exact h4 g (by simpa using hg)

theorem three₁_cent_gens (h : ThreeFacts) :
    closure (tp 275 '' {x | x ∈ cpGens3}) =
      mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))) := by
  have := h.row₁.gens
  dsimp only [threeRow₁] at this
  exact this

theorem rNormalCheck_spec
    (hrows : ThreeFacts) (he : threeEnumCheck = true)
    (hg : gxCheck = true) (h : rNormalCheck = true) : gx ≤ normalizer (subR3 : Set _) := by
  obtain ⟨-, hR, -, -, -, -⟩ := threeEnumCheck_spec hrows he
  obtain ⟨hx3, hinvh, hhrep, hhirep⟩ := (gxCheck_spec hg).1
  obtain ⟨hxP, hx3o, -, -⟩ := three₁_facts hrows
  simp only [rNormalCheck, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hgen : ∀ c ∈ gxGens, tp 275 c ∈ normalizer (subR3 : Set (Equiv.Perm (Fin 275))) := by
    intro c hc
    have hc1 := Array.all_eq_true'.1 h1 c hc
    simp only [Bool.and_eq_true] at hc1
    have hcrep : Rep 275 c (tp 275 c) := rep_tp hc1.1
    have hcirep : Rep 275 (invT 275 c) (tp 275 c)⁻¹ := Rep.inv_of_invOK hcrep hc1.2
    apply mem_normalizer_closure
    rintro _ ⟨r, hr, rfl⟩
    have hmem := Array.all_eq_true'.1 (Array.all_eq_true'.1 h2 c hc) r hr
    exact hR.enum.mem_of_memT (rep_conjT hcrep hcirep (hR.rep r hr)) hmem
  have hC : mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))) ≤
      normalizer (subR3 : Set (Equiv.Perm (Fin 275))) := by
    rw [← three₁_cent_gens hrows, closure_le]
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c ∈ cpGens3 := hc
    exact hgen c (by rw [gxGens, Array.mem_push]; exact Or.inl hc')
  have hhn : tp 275 invHTab ∈ normalizer (subR3 : Set (Equiv.Perm (Fin 275))) :=
    hgen _ (by rw [gxGens, Array.mem_push]; exact Or.inr rfl)
  intro g hgx
  rcases mem_centralizer_or_of_mem_normalizer hx3o hx3 hinvh hgx with hg1 | hg2
  · exact hC hg1
  · have := (normalizer (subR3 : Set (Equiv.Perm (Fin 275)))).mul_mem hhn (hC hg2)
    simpa using this

theorem mem_normalizer_of_conj_eq {M : Type*} [Group M] {x g : M}
    (h : g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹) : g ∈ normalizer (zpowers x : Set M) := by
  rw [mem_normalizer_zpowers_iff]
  rcases h with h | h
  · have hgc : g * x = x * g := mul_inv_eq_iff_eq_mul.1 h
    have h2 : g⁻¹ * x * g = x := by
      calc g⁻¹ * x * g = g⁻¹ * (x * g) := by rw [mul_assoc]
        _ = g⁻¹ * (g * x) := by rw [hgc]
        _ = x := by rw [inv_mul_cancel_left]
    rw [h, h2]
    exact ⟨mem_zpowers x, mem_zpowers x⟩
  · have h2 : g⁻¹ * x * g = x⁻¹ := by
      have h1 : g * x⁻¹ * g⁻¹ = x := by
        have := congrArg (fun z => z⁻¹) h
        simpa [mul_assoc] using this
      calc g⁻¹ * x * g = g⁻¹ * (g * x⁻¹ * g⁻¹) * g := by rw [h1]
        _ = x⁻¹ := by group
    rw [h, h2]
    exact ⟨inv_mem (mem_zpowers x), inv_mem (mem_zpowers x)⟩

theorem sylowIntCheck_spec
    (hrows : ThreeFacts) (he : threeEnumCheck = true) (h : sylowIntCheck = true) :
    tp 275 conjGTab ∈ gx ∧
      ∀ y ∈ sylowT, (tp 275 conjGTab)⁻¹ * y * ((tp 275 conjGTab)⁻¹)⁻¹ ∈ sylowT → y ∈ subR3 := by
  have hD : GroupData 275 mclP mclPGTbls mclGen mclSift := mcl_groupData
  obtain ⟨hT, hR, -, hx, hxi, -⟩ := threeEnumCheck_spec hrows he
  simp only [sylowIntCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hg : Rep 275 conjGTab (tp 275 conjGTab) := rep_tp h1
  have hgi : Rep 275 (invT 275 conjGTab) (tp 275 conjGTab)⁻¹ := Rep.inv_of_invOK hg h2
  have hgcj := rep_conjT hg hgi hx
  refine ⟨mem_inf.2 ⟨(hD.sift _ _ hg).1 h3, ?_⟩, fun y hy hy' => ?_⟩
  · apply mem_normalizer_of_conj_eq
    rcases Bool.or_eq_true_iff.1 h4 with h4 | h4
    · exact Or.inl ((tblEq_iff_eq hgcj hx).1 h4)
    · exact Or.inr ((tblEq_iff_eq hgcj hxi).1 h4)
  · obtain ⟨k, hk, hkrep⟩ := hT.enum.cover y hy
    have hgi' : Rep 275 conjGTab ((tp 275 conjGTab)⁻¹)⁻¹ := by rw [inv_inv]; exact hg
    have hrep := rep_conjT hgi hgi' hkrep
    have hmem := hT.enum.memT_of_mem hrep hy'
    have h5k := Array.all_eq_true'.1 h5 enumT.1[k]! (getElem!_mem_array hk)
    rw [hmem] at h5k
    have h5k' : memT 275 enumR3.1 enumT.1[k]! = true := by simpa using h5k
    exact hR.enum.mem_of_memT hkrep h5k'

theorem sylowT_le_gx
    (hrows : ThreeFacts) (he : threeEnumCheck = true) (hin : rInTCheck = true) :
    sylowT ≤ gx ∧ subR3 ≤ gx := by
  obtain ⟨hT, hR, -, -, -, -⟩ := threeEnumCheck_spec hrows he
  obtain ⟨-, -, hRc, hTc⟩ := rInTCheck_spec hrows he hin
  exact ⟨fun y hy => mem_inf.2 ⟨hT.le hy, centralizer_le_normalizer_zpowers _ (hTc hy)⟩,
    fun y hy => mem_inf.2 ⟨hR.le hy, centralizer_le_normalizer_zpowers _ (hRc hy)⟩⟩

theorem pCore_gx
    (hrows : ThreeFacts) (he : threeEnumCheck = true)
    (hg : gxCheck = true) (hrin : rInTCheck = true) (hrn : rNormalCheck = true)
    (hs : sylowIntCheck = true) : CFSG.inSubgroup (CFSG.pCore 3) gx = subR3 := by
  obtain ⟨hT, hR, -, -, -, -⟩ := threeEnumCheck_spec hrows he
  obtain ⟨-, -, hRc, hTc⟩ := rInTCheck_spec hrows he hrin
  have hnorm := rNormalCheck_spec hrows he hg hrn
  obtain ⟨hgg, hint⟩ := sylowIntCheck_spec hrows he hs
  obtain ⟨hcardgx, -⟩ := card_gx hrows hg
  have hTgx : sylowT ≤ gx := fun y hy =>
    mem_inf.2 ⟨hT.le hy, centralizer_le_normalizer_zpowers _ (hTc hy)⟩
  have hRgx : subR3 ≤ gx := fun y hy =>
    mem_inf.2 ⟨hR.le hy, centralizer_le_normalizer_zpowers _ (hRc hy)⟩
  have hfac : (Nat.card ↥gx).factorization 3 = 6 := by
    rw [hcardgx, show (58320 : ℕ) = 3 ^ 6 * 80 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 3), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply le_antisymm
  ·
    have hKn : (CFSG.pCore 3 ↥gx).Normal := CFSG.pCore_normal
    have hKp : IsPGroup 3 (CFSG.pCore 3 ↥gx) := CFSG.pCore_isPGroup
    let S₁ : Sylow 3 ↥gx := Sylow.ofCard (sylowT.subgroupOf gx) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hTgx).toEquiv, hT.card, hfac]; norm_num)
    let T' : Subgroup (Equiv.Perm (Fin 275)) :=
      sylowT.map (MulAut.conj (tp 275 conjGTab)).toMonoidHom
    have hT'gx : T' ≤ gx := by
      rintro _ ⟨y, hy, rfl⟩
      exact gx.mul_mem (gx.mul_mem hgg (hTgx hy)) (gx.inv_mem hgg)
    let S₂ : Sylow 3 ↥gx := Sylow.ofCard (T'.subgroupOf gx) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hT'gx).toEquiv,
        Subgroup.card_map_of_injective (MulAut.conj (tp 275 conjGTab)).injective, hT.card, hfac]
      norm_num)
    have hK1 := hKp.le_sylow_of_normal S₁
    have hK2 := hKp.le_sylow_of_normal S₂
    rintro _ ⟨k, hk, rfl⟩
    have h1 : (k : Equiv.Perm (Fin 275)) ∈ sylowT := hK1 hk
    have h2 : (k : Equiv.Perm (Fin 275)) ∈ T' := hK2 hk
    obtain ⟨t, ht, hkt⟩ := h2
    refine hint _ h1 ?_
    change (tp 275 conjGTab)⁻¹ * (k : Equiv.Perm (Fin 275)) * ((tp 275 conjGTab)⁻¹)⁻¹ ∈ sylowT
    have : (tp 275 conjGTab)⁻¹ * (k : Equiv.Perm (Fin 275)) * ((tp 275 conjGTab)⁻¹)⁻¹ = t := by
      rw [← hkt]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact ht
  ·
    have hRg : (subR3.subgroupOf gx).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRgx).2 hnorm
    have hRp : IsPGroup 3 ↥(subR3.subgroupOf gx) := IsPGroup.of_card (n := 5) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hRgx).toEquiv, hR.card]; norm_num)
    have hle : subR3.subgroupOf gx ≤ CFSG.pCore 3 ↥gx := le_sSup ⟨hRg, hRp⟩
    intro y hy
    have hy' : y ∈ (subR3.subgroupOf gx).map gx.subtype := by
      rw [Subgroup.map_subgroupOf_eq_of_le hRgx]
      exact hy
    obtain ⟨k, hk, rfl⟩ := hy'
    exact ⟨k, hle hk, rfl⟩

theorem rStructCheck_spec
    (hrows : ThreeFacts) (he : threeEnumCheck = true) (hin : rInTCheck = true)
    (h : rStructCheck = true) :
    (∀ r ∈ subR3, r ^ 3 = 1) ∧
      subR3 ⊓ centralizer (subR3 : Set (Equiv.Perm (Fin 275))) = zpowers three₁ ∧
      ⁅subR3, subR3⁆ = zpowers three₁ := by
  obtain ⟨-, hR, -, hx, hxi, -⟩ := threeEnumCheck_spec hrows he
  obtain ⟨-, -, hRc, -⟩ := rInTCheck_spec hrows he hin
  obtain ⟨hxP, hx3, -, -⟩ := three₁_facts hrows
  simp only [rStructCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  have hn : (275 : ℕ) < 2 ^ 32 := by norm_num
  have hexp : ∀ r ∈ subR3, r ^ 3 = 1 := by
    intro r hr
    obtain ⟨k, hk, hkrep⟩ := hR.enum.cover r hr
    have := (tblEq_idT_iff hn (Rep.powT hn hkrep 3)).1
      (Array.all_eq_true'.1 h2 _ (getElem!_mem_array hk))
    exact this
  have hcentral : ∀ (t : Table) (g : Equiv.Perm (Fin 275)), Rep 275 t g →
      ((rGens3.all fun r => commTT 275 t r) = true ↔
        g ∈ centralizer (subR3 : Set (Equiv.Perm (Fin 275)))) := by
    intro t g ht
    constructor
    · intro hall
      rw [mem_centralizer_iff]
      intro y hy
      have : subR3 ≤ centralizer ({g} : Set (Equiv.Perm (Fin 275))) := by
        rw [closure_le]
        rintro _ ⟨r, hr, rfl⟩
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        exact ((commTT_iff ht (hR.rep r hr)).1 ((Array.all_eq_true'.1 hall) r hr)).symm
      exact (mem_centralizer_singleton_iff.1 (this hy))
    · intro hg
      rw [Array.all_eq_true']
      intro r hr
      refine (commTT_iff ht (hR.rep r hr)).2 ?_
      exact ((mem_centralizer_iff.1 hg (tp 275 r) (subset_closure ⟨r, hr, rfl⟩))).symm
  have hncard := hR.enum.ncard_filter (fun e => rGens3.all fun r => commTT 275 e r)
    (fun g => g ∈ centralizer (subR3 : Set (Equiv.Perm (Fin 275)))) hcentral
  have hZcard : Nat.card ↥(subR3 ⊓ centralizer (subR3 : Set (Equiv.Perm (Fin 275)))) = 3 := by
    have e1 : Nat.card ↥(subR3 ⊓ centralizer (subR3 : Set (Equiv.Perm (Fin 275)))) =
        ({x : Equiv.Perm (Fin 275) | x ∈ subR3 ∧ x ∈ centralizer (subR3 : Set _)}).ncard := by
      have hset : {x : Equiv.Perm (Fin 275) | x ∈ subR3 ∧ x ∈ centralizer (subR3 : Set _)} =
          ((subR3 ⊓ centralizer (subR3 : Set _) : Subgroup _) : Set (Equiv.Perm (Fin 275))) := by
        ext y
        simp
      rw [hset]
      exact Nat.card_coe_set_eq _
    rw [e1, hncard]
    exact h3
  have hxR : three₁ ∈ subR3 := hR.enum.mem_of_memT hx h4
  have hxZ : three₁ ∈ subR3 ⊓ centralizer (subR3 : Set (Equiv.Perm (Fin 275))) := by
    refine mem_inf.2 ⟨hxR, mem_centralizer_iff.2 fun y hy => ?_⟩
    exact mem_centralizer_singleton_iff.1 (hRc hy)
  have hZeq : zpowers three₁ = subR3 ⊓ centralizer (subR3 : Set (Equiv.Perm (Fin 275))) := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hxZ) ?_
    rw [hZcard, Nat.card_zpowers, hx3]
  have hcomm : ⁅subR3, subR3⁆ = zpowers three₁ := by
    apply le_antisymm
    · rw [Subgroup.commutator_def, closure_le]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      obtain ⟨ka, hka, hkarep⟩ := hR.enum.cover a ha
      obtain ⟨kb, hkb, hkbrep⟩ := hR.enum.cover b hb
      have hia : Rep 275 (invT 275 enumR3.1[ka]!) a⁻¹ :=
        Rep.inv_of_invOK hkarep (Array.all_eq_true'.1 h1 _ (getElem!_mem_array hka))
      have hib : Rep 275 (invT 275 enumR3.1[kb]!) b⁻¹ :=
        Rep.inv_of_invOK hkbrep (Array.all_eq_true'.1 h1 _ (getElem!_mem_array hkb))
      have hcrep := Rep.compT (Rep.compT hkarep hkbrep) (Rep.compT hia hib)
      have hc5 := Array.all_eq_true'.1 (Array.all_eq_true'.1 h5 _ (getElem!_mem_array hka)) _
        (getElem!_mem_array hkb)
      simp only [Bool.or_eq_true] at hc5
      rw [commutatorElement_def]
      have e1 : a * b * a⁻¹ * b⁻¹ = a * b * (a⁻¹ * b⁻¹) := by group
      rcases hc5 with (hc | hc) | hc
      · rw [e1, (tblEq_idT_iff hn hcrep).1 hc]; exact one_mem _
      · rw [e1, (tblEq_iff_eq hcrep hx).1 hc]; exact mem_zpowers _
      · rw [e1, (tblEq_iff_eq hcrep hxi).1 hc]; exact inv_mem (mem_zpowers _)
    · rw [zpowers_le]
      have hpa : Rep 275 commATab (tp 275 commATab) := rep_tp h6
      have hpb : Rep 275 commBTab (tp 275 commBTab) := rep_tp h7
      have hpai := Rep.inv_of_invOK hpa h10
      have hpbi := Rep.inv_of_invOK hpb h11
      have hrep := Rep.compT (Rep.compT hpa hpb) (Rep.compT hpai hpbi)
      have heq := (tblEq_iff_eq hrep hx).1 h12
      have haR := hR.enum.mem_of_memT hpa h8
      have hbR := hR.enum.mem_of_memT hpb h9
      refine Subgroup.subset_closure ⟨tp 275 commATab, haR, tp 275 commBTab, hbR, ?_⟩
      rw [commutatorElement_def]
      rw [← heq]
      group
  exact ⟨hexp, hZeq.symm, hcomm⟩

theorem aStructCheck_spec
    (hrows : ThreeFacts) (he : threeEnumCheck = true) (hin : rInTCheck = true)
    (h : aStructCheck = true) :
    CFSG.IsElementaryAbelian 3 ↥subA3 ∧ Nat.card ↥(subR3 ⊓ subA3) = 27 ∧ subR3 ⊔ subA3 = sylowT ∧
      (∀ y ∈ sylowT, orderOf y = 3 → y ∈ subR3 ∨ y ∈ subA3) ∧
      subA3 = closure ((sylowT : Set (Equiv.Perm (Fin 275))) ∩ conjClass mclP three₁) ∧
      ({y : Equiv.Perm (Fin 275) | y ∈ sylowT ∧ y ∈ conjClass mclP three₁}).ncard = 20 := by
  obtain ⟨hT, hR, hA, hx, hxi, hclass⟩ := threeEnumCheck_spec hrows he
  obtain ⟨hRT, hAT, -, -⟩ := rInTCheck_spec hrows he hin
  simp only [aStructCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  have hn : (275 : ℕ) < 2 ^ 32 := by norm_num
  have hAcomm : ∀ a ∈ subA3, ∀ b ∈ subA3, a * b = b * a := by
    intro a ha b hb
    obtain ⟨ka, hka, hkarep⟩ := hA.enum.cover a ha
    obtain ⟨kb, hkb, hkbrep⟩ := hA.enum.cover b hb
    exact (commTT_iff hkarep hkbrep).1
      (Array.all_eq_true'.1 (Array.all_eq_true'.1 h2 _ (getElem!_mem_array hka)) _
        (getElem!_mem_array hkb))
  have hAexp : ∀ a ∈ subA3, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨k, hk, hkrep⟩ := hA.enum.cover a ha
    exact (tblEq_idT_iff hn (Rep.powT hn hkrep 3)).1
      (Array.all_eq_true'.1 h3 _ (getElem!_mem_array hk))
  have hAel : CFSG.IsElementaryAbelian 3 ↥subA3 :=
    { is_comm := ⟨fun a b => Subtype.ext (hAcomm a.1 a.2 b.1 b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (hAexp a.1 a.2) }
  refine ⟨hAel, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hn27 := hA.enum.ncard_filter (memT 275 enumR3.1) (fun g => g ∈ subR3)
      (fun t g ht => (hR.enum.mem_iff_memT ht).symm)
    have hset : {x : Equiv.Perm (Fin 275) | x ∈ subA3 ∧ x ∈ subR3} =
        ((subR3 ⊓ subA3 : Subgroup _) : Set (Equiv.Perm (Fin 275))) := by
      ext y
      simp [and_comm]
    have e1 : Nat.card ↥(subR3 ⊓ subA3) =
        ({x : Equiv.Perm (Fin 275) | x ∈ subA3 ∧ x ∈ subR3}).ncard := by
      rw [hset]
      exact Nat.card_coe_set_eq _
    rw [e1, hn27]
    exact h4
  ·
    refine le_antisymm (sup_le hRT hAT) ?_
    intro y hy
    obtain ⟨k, hk, hkrep⟩ := hT.enum.cover y hy
    have hk5 := Array.all_eq_true'.1 h5 _ (getElem!_mem_array hk)
    obtain ⟨j, hj, hjp⟩ := Array.any_eq_true.1 hk5
    rw [← getElem!_pos enumR3.1 j hj] at hjp
    have hjrep := hR.enum.rep j hj
    have hjmem := hR.enum.mem j hj
    have hiv : Rep 275 (invT 275 enumR3.1[j]!) (tablePerm 275 enumR3.1[j]!)⁻¹ :=
      Rep.inv_of_invOK hjrep (Array.all_eq_true'.1 h1 _ (getElem!_mem_array hj))
    have hAmem := hA.enum.mem_of_memT (Rep.compT hiv hkrep) hjp
    have := Subgroup.mul_mem_sup hjmem hAmem
    simpa using this
  ·
    intro y hy hy3
    obtain ⟨k, hk, hkrep⟩ := hT.enum.cover y hy
    have hk6 := Array.all_eq_true'.1 h6 _ (getElem!_mem_array hk)
    have hord : ordTest 275 3 enumT.1[k]! = true :=
      (ordTest_iff_perm hkrep (by norm_num)).2 hy3
    simp only [Bool.or_eq_true, Bool.not_eq_true', hord] at hk6
    rcases hk6 with (hk6 | hk6) | hk6
    · exact absurd hk6 (by decide)
    · exact Or.inl (hR.enum.mem_of_memT hkrep hk6)
    · exact Or.inr (hA.enum.mem_of_memT hkrep hk6)
  ·
    apply le_antisymm
    · refine (closure_le _).2 ?_
      rintro _ ⟨g, hg, rfl⟩
      exact subset_closure ⟨hAT (subset_closure ⟨g, hg, rfl⟩),
        (hclass g (tp 275 g) (hA.rep g hg)).1 (Array.all_eq_true'.1 h7 g hg)⟩
    · refine (closure_le _).2 ?_
      rintro y ⟨hyT, hyc⟩
      obtain ⟨k, hk, hkrep⟩ := hT.enum.cover y hyT
      have hmc : memT 275 enumClass.1 enumT.1[k]! = true := (hclass _ _ hkrep).2 hyc
      have hk8 := Array.all_eq_true'.1 h8 _ (getElem!_mem_array hk)
      simp only [Bool.or_eq_true, Bool.not_eq_true', hmc] at hk8
      rcases hk8 with hk8 | hk8
      · exact absurd hk8 (by decide)
      · exact hA.enum.mem_of_memT hkrep hk8
  · exact (hT.enum.ncard_filter (memT 275 enumClass.1) (fun g => g ∈ conjClass mclP three₁)
      hclass).trans h9

theorem inv_of_gens_of_comm {M : Type*} [Group M] {σ : M} {S : Set M}
    (hc : ∀ a ∈ closure S, ∀ b ∈ closure S, a * b = b * a)
    (hS : ∀ a ∈ S, σ * a * σ⁻¹ = a⁻¹) : ∀ a ∈ closure S, σ * a * σ⁻¹ = a⁻¹ := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have := hc x hx y hy
    calc σ * (x * y) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * y * σ⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [ihx, ihy]
      _ = (y * x)⁻¹ := by group
      _ = (x * y)⁻¹ := by rw [← this]
  | inv x hx ihx =>
    calc σ * x⁻¹ * σ⁻¹ = (σ * x * σ⁻¹)⁻¹ := by group
      _ = (x⁻¹)⁻¹ := by rw [ihx]

theorem aInvCheck_spec
    (hrows : ThreeFacts) (he : threeEnumCheck = true)
    (hin : rInTCheck = true) (hA : aStructCheck = true) (h : aInvCheck = true) :
    tp 275 sigmaTab ∈ mclR ∧ tp 275 sigmaTab ∉ mclP ∧ orderOf (tp 275 sigmaTab) = 2 ∧
      ∀ a ∈ subA3, tp 275 sigmaTab * a * (tp 275 sigmaTab)⁻¹ = a⁻¹ := by
  have hD : GroupData 275 mclP mclPGTbls mclGen mclSift := mcl_groupData
  have hn : (275 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, hAe, -, -, -⟩ := threeEnumCheck_spec hrows he
  obtain ⟨hAel, -, -, -, -, -⟩ := aStructCheck_spec hrows he hin hA
  simp only [aInvCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, hu⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have hs : Rep 275 sigmaTab (tp 275 sigmaTab) := rep_tp h1
  have hsi : Rep 275 (invT 275 sigmaTab) (tp 275 sigmaTab)⁻¹ := Rep.inv_of_invOK hs h2
  obtain ⟨hU2, -, hUP, hmap, -⟩ := mcl_normalizing_model
  have hUn : ∀ p ∈ mclP, mclU * p * mclU⁻¹ ∈ mclP := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  have hUrep : Rep 275 mclOuterTbl mclU := rep_tp hu
  have hσP : tp 275 sigmaTab ∉ mclP := by
    intro hm
    have := (hD.sift _ _ hs).2 hm
    rw [h4] at this
    exact Bool.noConfusion this
  have hσ2 : tp 275 sigmaTab * tp 275 sigmaTab = 1 :=
    (tblEq_idT_iff hn (Rep.compT hs hs)).1 h6
  refine ⟨mem_R_of_sift hD hU2 hUn hUrep hs (by rw [h5, Bool.or_true]), hσP, ?_, ?_⟩
  · exact orderOf_eq_prime (by rw [pow_two]; exact hσ2) (fun h1' => hσP (h1' ▸ one_mem _))
  · have hcomm : ∀ a ∈ subA3, ∀ b ∈ subA3, a * b = b * a := by
      intro a ha b hb
      have := (IsMulCommutative.is_comm (M := ↥subA3)).comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
    refine inv_of_gens_of_comm hcomm ?_
    rintro _ ⟨g, hg, rfl⟩
    exact (tblEq_iff_eq (rep_conjT hs hsi (hAe.rep g hg)) (hAe.repInv g hg)).1
      (Array.all_eq_true'.1 h7 g hg)

theorem weakCheck_spec
    (hrows : ThreeFacts) (he : threeEnumCheck = true) (h : weakCheck = true) :
    ∀ r ∈ subR3, r ∈ conjClass mclP three₁ → r = three₁ ∨ r = three₁⁻¹ := by
  obtain ⟨-, hR, -, hx, hxi, hclass⟩ := threeEnumCheck_spec hrows he
  intro r hr hrc
  obtain ⟨k, hk, hkrep⟩ := hR.enum.cover r hr
  have hk' := Array.all_eq_true'.1 h _ (getElem!_mem_array hk)
  have hmc : memT 275 enumClass.1 enumR3.1[k]! = true := (hclass _ _ hkrep).2 hrc
  simp only [Bool.or_eq_true, Bool.not_eq_true', hmc] at hk'
  rcases hk' with (hk' | hk') | hk'
  · exact absurd hk' (by decide)
  · exact Or.inl ((tblEq_iff_eq hkrep hx).1 hk')
  · exact Or.inr ((tblEq_iff_eq hkrep hxi).1 hk')

theorem thompsonCheck_spec
    (hrows : ThreeFacts) (he : threeEnumCheck = true) (h : thompsonCheck = true) :
    (∀ t ∈ sylowT, t ∉ subA3 →
      Nat.card ↥(subA3 ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 275)))) ≤ 9) ∧
    Nat.card ↥(sylowT ⊓ centralizer (sylowT : Set (Equiv.Perm (Fin 275)))) = 3 := by
  obtain ⟨hT, -, hA, -, -, -⟩ := threeEnumCheck_spec hrows he
  simp only [thompsonCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro t ht htA
    obtain ⟨k, hk, hkrep⟩ := hT.enum.cover t ht
    have hk1 := Array.all_eq_true'.1 h1 _ (getElem!_mem_array hk)
    have hnA : memT 275 enumA3.1 enumT.1[k]! = false := by
      cases hm : memT 275 enumA3.1 enumT.1[k]!
      · rfl
      · exact absurd ((hA.enum.mem_iff_memT hkrep).2 hm) htA
    rw [hnA, Bool.false_or] at hk1
    have hcommp : ∀ (u : Table) (g : Equiv.Perm (Fin 275)), Rep 275 u g →
        (commTT 275 enumT.1[k]! u = true ↔
          g ∈ centralizer ({t} : Set (Equiv.Perm (Fin 275)))) := by
      intro u g hu
      rw [commTT_iff hkrep hu, mem_centralizer_singleton_iff]
      exact eq_comm
    have hncard := hA.enum.ncard_filter (commTT 275 enumT.1[k]!)
      (fun g => g ∈ centralizer ({t} : Set (Equiv.Perm (Fin 275)))) hcommp
    have hset : {y : Equiv.Perm (Fin 275) | y ∈ subA3 ∧
        y ∈ centralizer ({t} : Set (Equiv.Perm (Fin 275)))} =
        ((subA3 ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 275))) : Subgroup _) :
          Set (Equiv.Perm (Fin 275))) := by
      ext y
      simp
    have e1 : Nat.card ↥(subA3 ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 275)))) =
        {y : Equiv.Perm (Fin 275) | y ∈ subA3 ∧
          y ∈ centralizer ({t} : Set (Equiv.Perm (Fin 275)))}.ncard := by
      rw [hset]
      exact Nat.card_coe_set_eq _
    rw [e1, hncard]
    exact Nat.le_of_ble_eq_true hk1
  · have hcentral : ∀ (t : Table) (g : Equiv.Perm (Fin 275)), Rep 275 t g →
        ((sylowThreeGens.toArray.all fun r => commTT 275 t r) = true ↔
          g ∈ centralizer (sylowT : Set (Equiv.Perm (Fin 275)))) := by
      intro t g ht
      constructor
      · intro hall
        rw [mem_centralizer_iff]
        intro y hy
        have : sylowT ≤ centralizer ({g} : Set (Equiv.Perm (Fin 275))) := by
          rw [closure_le]
          rintro _ ⟨r, hr, rfl⟩
          rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
          exact ((commTT_iff ht (hT.rep r hr)).1 ((Array.all_eq_true' (p := _)).1 hall r hr)).symm
        exact mem_centralizer_singleton_iff.1 (this hy)
      · intro hg
        rw [Array.all_eq_true']
        intro r hr
        refine (commTT_iff ht (hT.rep r hr)).2 ?_
        exact ((mem_centralizer_iff.1 hg (tp 275 r) (subset_closure ⟨r, hr, rfl⟩))).symm
    have hncard := hT.enum.ncard_filter
      (fun e => sylowThreeGens.toArray.all fun r => commTT 275 e r)
      (fun g => g ∈ centralizer (sylowT : Set (Equiv.Perm (Fin 275)))) hcentral
    have e1 : Nat.card ↥(sylowT ⊓ centralizer (sylowT : Set (Equiv.Perm (Fin 275)))) =
        {y : Equiv.Perm (Fin 275) | y ∈ sylowT ∧
          y ∈ centralizer (sylowT : Set (Equiv.Perm (Fin 275)))}.ncard := by
      have hset : {y : Equiv.Perm (Fin 275) | y ∈ sylowT ∧
          y ∈ centralizer (sylowT : Set (Equiv.Perm (Fin 275)))} =
          ((sylowT ⊓ centralizer (sylowT : Set (Equiv.Perm (Fin 275))) : Subgroup _) :
            Set (Equiv.Perm (Fin 275))) := by
        ext y
        simp
      rw [hset]
      exact Nat.card_coe_set_eq _
    rw [e1, hncard]
    exact h2

end CFSG.Sporadic.Recognition.McLAS
