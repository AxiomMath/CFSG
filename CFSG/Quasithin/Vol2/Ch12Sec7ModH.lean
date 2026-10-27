module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModG
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
import all CFSG.Quasithin.Vol2.Ch12Sec2Ident
public import CFSG.Quasithin.Vol2.Ch12Sec7L23b

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

section Codes

variable {V : Type} [CommGroup V] [Finite V]

theorem pow_mem_of_comp_mem {l : List B6} (h1 : B6.id ∈ l) (hmul : ∀ x ∈ l, ∀ y ∈ l, x.comp y ∈ l)
    {B : B6} (hB : B ∈ l) : ∀ n, B.pow n ∈ l
  | 0 => h1
  | n + 1 => hmul _ hB _ (pow_mem_of_comp_mem h1 hmul hB n)

@[expose] noncomputable def Coding.subOf (C : Coding V) (l : List B6) (h1 : B6.id ∈ l)
    (hmul : ∀ x ∈ l, ∀ y ∈ l, x.comp y ∈ l) : Subgroup (MulAut V) where
  carrier := {a | C.cB a ∈ l}
  one_mem' := by
    show C.cB 1 ∈ l
    rw [C.cB_one]
    exact h1
  mul_mem' {a b} ha hb := by
    show C.cB (a * b) ∈ l
    rw [C.cB_mul]
    exact hmul _ ha _ hb
  inv_mem' {a} ha := by
    show C.cB a⁻¹ ∈ l
    have hfin : IsOfFinOrder a := isOfFinOrder_of_finite a
    have hpos := hfin.orderOf_pos
    have e : a⁻¹ = a ^ (orderOf a - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hpos,
        pow_orderOf_eq_one]
    rw [e, C.cB_pow]
    exact pow_mem_of_comp_mem h1 hmul ha _

theorem Coding.mem_subOf (C : Coding V) {l : List B6} {h1 : B6.id ∈ l}
    {hmul : ∀ x ∈ l, ∀ y ∈ l, x.comp y ∈ l} {a : MulAut V} :
    a ∈ C.subOf l h1 hmul ↔ C.cB a ∈ l := Iff.rfl

theorem Coding.card_subOf (C : Coding V) {l : List B6} {h1 : B6.id ∈ l}
    {hmul : ∀ x ∈ l, ∀ y ∈ l, x.comp y ∈ l} (hnd : l.Nodup)
    (hsurj : ∀ B ∈ l, ∃ a : MulAut V, C.cB a = B) : Nat.card (C.subOf l h1 hmul) = l.length := by
  classical
  have e : C.subOf l h1 hmul ≃ {B : B6 // B ∈ l} :=
    Equiv.ofBijective (fun a => ⟨C.cB a, a.2⟩) ⟨fun a b hab => Subtype.ext (C.cB_injective
      (congrArg Subtype.val hab)), fun B => by
        obtain ⟨a, ha⟩ := hsurj B.1 B.2
        exact ⟨⟨a, show C.cB a ∈ l by rw [ha]; exact B.2⟩, Subtype.ext ha⟩⟩
  rw [Nat.card_congr e]
  have e2 : {B : B6 // B ∈ l} ≃ ↥l.toFinset := Equiv.subtypeEquivRight fun B => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnd]

theorem exists_conj_of_card_eight {H S S' : Subgroup (MulAut V)} (hH : Nat.card H = 1080)
    (hS : S ≤ H) (hS' : S' ≤ H) (h8 : Nat.card S = 8) (h8' : Nat.card S' = 8) :
    ∃ b ∈ H, ∀ a, a ∈ S ↔ b * a * b⁻¹ ∈ S' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : ∀ {K : Subgroup (MulAut V)}, K ≤ H → Nat.card K = 8 →
      Nat.card (K.subgroupOf H) = 8 := fun {K} hK h => by
    rw [← h]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have hp : ∀ {K : Subgroup (MulAut V)}, K ≤ H → Nat.card K = 8 →
      IsPGroup 2 (K.subgroupOf H) := fun {K} hK h =>
    IsPGroup.of_card (n := 3) (by rw [hc hK h]; norm_num)
  have hi : ∀ {K : Subgroup (MulAut V)}, K ≤ H → Nat.card K = 8 →
      ¬ 2 ∣ (K.subgroupOf H).index := fun {K} hK h => by
    have e := (K.subgroupOf H).card_mul_index
    rw [hc hK h, hH] at e
    omega
  let Q := (hp hS h8).toSylow (hi hS h8)
  let Q' := (hp hS' h8').toSylow (hi hS' h8')
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) Q Q'
  have key : ∀ x : ↥H, x ∈ S'.subgroupOf H ↔ g⁻¹ * x * g ∈ S.subgroupOf H := by
    intro x
    have h1 : x ∈ (Q' : Subgroup ↥H) ↔ x ∈ ((g • Q : Sylow 2 ↥H) : Subgroup ↥H) := by rw [hg]
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    simp only [MulAut.smul_def, MulAut.conj_inv_apply] at h1
    exact h1
  refine ⟨g, g.2, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · have hx : g * a * g⁻¹ ∈ H := H.mul_mem (H.mul_mem g.2 (hS ha)) (H.inv_mem g.2)
    have := (key ⟨_, hx⟩).2 (by
      rw [Subgroup.mem_subgroupOf]
      simpa [mul_assoc] using ha)
    exact this
  · have hx := hS' ha
    have := (key ⟨_, hx⟩).1 (by rw [Subgroup.mem_subgroupOf]; exact ha)
    rw [Subgroup.mem_subgroupOf] at this
    simpa [mul_assoc] using this

theorem s0_closed : ∀ x ∈ s0, ∀ y ∈ s0, x.comp y ∈ s0 := by decide

theorem id_mem_s0 : B6.id ∈ s0 := by decide

theorem s0_nodup : s0.Nodup := by decide

theorem s0m_inGm : ∀ A ∈ s0m, A.Valid ∧ inGm A = true := by decide

theorem s0_sub_gm6 : ∀ B ∈ s0, B ∈ gm6 := by
  intro B hB
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hB
  have hall := cert_gmList_complete
  obtain ⟨⟨h0, h1, h2⟩, hin⟩ := s0m_inGm A hA
  exact List.mem_map.2 ⟨A, hall _ (List.mem_range.2 h0) _ (List.mem_range.2 h1) _
    (List.mem_range.2 h2) hin, rfl⟩

theorem IdentL.exists_sylow {C : Coding V}
    {H : Subgroup (MulAut V)} (hC : IdentL C H) (hH : Nat.card H = 1080)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS : Nat.card S = 8) :
    ∃ C' : Coding V, IdentL C' H ∧ ∀ a, a ∈ S ↔ C'.cB a ∈ s0 := by
  set S' := C.subOf s0 id_mem_s0 s0_closed with hS'
  have hS'H : S' ≤ H := fun a ha => (hC.1 a).2 (s0_sub_gm6 _ ha)
  have hS'8 : Nat.card S' = 8 :=
    C.card_subOf s0_nodup (fun B hB => hC.2 B (s0_sub_gm6 B hB))
  obtain ⟨b, hbH, hb⟩ := exists_conj_of_card_eight hH hSH hS'H hS hS'8
  refine ⟨C.recode b, hC.recode hbH, fun a => ?_⟩
  rw [hb a, C.recode_cB]
  rfl

end Codes

section Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem L_le_normalizer (h : Hyp1271 G T L V) : L ≤ Subgroup.normalizer (V : Set G) :=
  h.hyp.irrPlus.2.2.1

theorem T_le_normalizer (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    T ≤ Subgroup.normalizer (V : Set G) :=
  (card_eq_of_1222 h1222 h).2.2

variable [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem sq_eq_one_V (h : Hyp1271 G T L V) (v : ↥V) : v ^ 2 = 1 :=
  Subtype.ext (by simpa using sq_eq_one_of_mem h.hyp v.2)

omit [IsMulCommutative ↥V] in
theorem card_V (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) : Nat.card ↥V = 2 ^ 6 :=
  (card_eq_of_1222 h1222 h).2.1

theorem exists_orbit18 (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    ∃ t : ↥V, Nat.card (Orbit.orbitIn (autOn L V) t) = 18 := by
  obtain ⟨-, -, t, ht, -, h18, -⟩ := orbits_of_1222 h1222 h
  exact ⟨⟨t, ht⟩, by rw [card_orbitIn_autOn (L_le_normalizer h)]; exact h18⟩

theorem exists_identL_G (h1222 : Stmt12_2_2)
    (h : Hyp1271 G T L V) : ∃ C : Coding ↥V, IdentL C (autOn L V) := by
  obtain ⟨hperf, hZ, he⟩ := autOn_hat h.hatA6 (L_le_normalizer h)
  obtain ⟨t, ht⟩ := exists_orbit18 h1222 h
  exact exists_identL (sq_eq_one_V h) (card_V h1222 h) _ hperf hZ he ht

omit [IsMulCommutative ↥V] in
theorem odd_index_inf (h : Hyp1271 G T L V) :
    ¬ 2 ∣ ((T ⊓ L).subgroupOf L).index := by
  have hT := h.hyp.sylow
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := h.hyp.normalizes
  set K := L ⊔ T with hK
  have hprod : ∀ x ∈ K, ∃ l ∈ L, ∃ t ∈ T, x = l * t := by
    intro x hx
    have hx' : x ∈ ((L ⊔ T : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T hTN] at hx'
    obtain ⟨l, hl, t, ht, rfl⟩ := hx'
    exact ⟨l, hl, t, ht, rfl⟩
  have key : ((T ⊓ L).subgroupOf L).index = (T.subgroupOf K).index := by
    unfold Subgroup.index
    let f : ↥L ⧸ (T ⊓ L).subgroupOf L → ↥K ⧸ T.subgroupOf K :=
      Quotient.map' (fun l : ↥L => (⟨l, le_sup_left (a := L) l.2⟩ : ↥K)) (by
        intro a b hab
        have h1 : a⁻¹ * b ∈ (T ⊓ L).subgroupOf L := QuotientGroup.leftRel_apply.mp hab
        rw [QuotientGroup.leftRel_apply]
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp h1).1)
    have hf : Function.Bijective f := by
      constructor
      · intro a b
        induction a using Quotient.inductionOn' with | _ a => ?_
        induction b using Quotient.inductionOn' with | _ b => ?_
        intro hab
        have h1 : (⟨(a : G), le_sup_left (a := L) a.2⟩ : ↥K)⁻¹ *
            ⟨(b : G), le_sup_left (a := L) b.2⟩ ∈ T.subgroupOf K :=
          QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply]
        exact Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp h1,
          L.mul_mem (L.inv_mem a.2) b.2⟩
      · intro q
        induction q using Quotient.inductionOn' with | _ x => ?_
        obtain ⟨l, hl, t, ht, hx⟩ := hprod x x.2
        refine ⟨Quotient.mk'' ⟨l, hl⟩, ?_⟩
        show Quotient.mk'' (⟨l, le_sup_left (a := L) hl⟩ : ↥K) = Quotient.mk'' x
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply]
        refine Subgroup.mem_subgroupOf.mpr ?_
        show l⁻¹ * (x : G) ∈ T
        rw [hx]
        simpa using ht
    exact Nat.card_congr (Equiv.ofBijective f hf)
  rw [key]
  intro h2
  apply hT.2
  have e := Subgroup.relIndex_mul_index (le_sup_right : T ≤ K)
  rw [← e]
  exact Dvd.dvd.mul_right h2 _

omit [IsMulCommutative ↥V] in
theorem card_autOn_inf (h : Hyp1271 G T L V) : Nat.card (autOn (T ⊓ L) V) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV := L_le_normalizer h
  have h1080 := card_autOn_L h.hatA6 hLV
  set f := autOnSurj hLV with hf
  have hmap : ((T ⊓ L).subgroupOf L).map f = (autOn (T ⊓ L) V).subgroupOf (autOn L V) := by
    ext ⟨a, ha⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨l, hl, hla⟩
      have ha' : a = A4.actionOn V L hLV l := (congrArg Subtype.val hla).symm
      rw [ha']
      exact (A4.mem_autOn_iff (le_trans inf_le_right hLV)).2 ⟨⟨l, hl⟩, rfl⟩
    · intro h'
      obtain ⟨x, rfl⟩ := (A4.mem_autOn_iff (le_trans inf_le_right hLV)).1 h'
      exact ⟨⟨x, x.2.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have hdvd := Subgroup.index_map_dvd ((T ⊓ L).subgroupOf L) (autOnSurj_surjective hLV)
  rw [hmap] at hdvd
  have hodd : ¬ 2 ∣ ((autOn (T ⊓ L) V).subgroupOf (autOn L V)).index := fun h2 =>
    odd_index_inf h (dvd_trans h2 hdvd)
  have hle : autOn (T ⊓ L) V ≤ autOn L V := A4.autOn_mono inf_le_right
  have hp : IsPGroup 2 (autOn (T ⊓ L) V) := by
    have h1 : IsPGroup 2 (T ⊓ L : Subgroup G) := h.hyp.sylow.1.to_le inf_le_left
    have h2 : IsPGroup 2 ((T ⊓ L).subgroupOf (Subgroup.normalizer (V : Set G))) :=
      h1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hLV)).symm
    exact h2.map _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  have e := Subgroup.card_mul_index ((autOn (T ⊓ L) V).subgroupOf (autOn L V))
  rw [h1080, show Nat.card ((autOn (T ⊓ L) V).subgroupOf (autOn L V)) =
    Nat.card (autOn (T ⊓ L) V) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hk] at e
  rw [hk]
  have hk3 : k ≤ 3 := by
    by_contra hk3
    have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have : 2 ^ 4 ∣ 1080 := dvd_trans h16 ⟨_, e.symm⟩
    norm_num at this
  interval_cases k
  · omega
  · omega
  · omega
  · rfl

@[expose] def Std (C : Coding ↥V) (T L : Subgroup G) : Prop :=
  IdentL C (autOn L V) ∧ ∀ a, a ∈ autOn (T ⊓ L) V ↔ C.cB a ∈ s0

theorem exists_std (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    ∃ C : Coding ↥V, Std C T L := by
  obtain ⟨C, hC⟩ := exists_identL_G h1222 h
  exact hC.exists_sylow (card_autOn_L h.hatA6 (L_le_normalizer h)) (A4.autOn_mono inf_le_right)
    (card_autOn_inf h)

end Setting

end CFSG.Quasithin.H13.S127.Mod

end
