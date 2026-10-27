module

public import CFSG.Quasithin.EmptyFaithful.ModEFin
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.Quasithin.ModE

abbrev P24 := Equiv.Perm (Fin 24)

@[expose] def tP : P24 := wP (tgW.getD 0 [])

@[expose] def uP : P24 := wP (tgW.getD 1 [])

@[expose] def vP : P24 := wP (tgW.getD 2 [])

@[expose] def lt0 : List P24 := [tP, uP, vP, tP⁻¹, uP⁻¹, vP⁻¹]

@[expose] def T0 : Subgroup P24 := Subgroup.closure {tP, uP, vP}

@[expose] def z0P : P24 := wP zW

@[expose] def g3P : P24 := wP gW

@[expose] def g3iP : P24 := wP giW

theorem pk_inv_of {a b : P24} (h : comp (pk a) (pk b) = kId) : pk a⁻¹ = pk b := by
  have h1 : pk (a * b) = pk 1 := by rw [pk_mul, h, pk_one]
  have h2 : a * b = 1 := pk_injective h1
  rw [eq_inv_of_mul_eq_one_right h2]

theorem pk_lt0 : lt0.map pk = lt0K := by
  have e0 : pk tP = wK (tgW.getD 0 []) := pk_wP _
  have e1 : pk uP = wK (tgW.getD 1 []) := pk_wP _
  have e2 : pk vP = wK (tgW.getD 2 []) := pk_wP _
  have h0 := lt0K_inv0
  have h1 := lt0K_inv1
  have h2 := lt0K_inv2
  have i0 : pk tP⁻¹ = wK (tgiW.getD 0 []) := by
    rw [pk_inv_of, pk_wP]
    rw [e0, pk_wP]
    exact Nat.eq_of_beq_eq_true h0
  have i1 : pk uP⁻¹ = wK (tgiW.getD 1 []) := by
    rw [pk_inv_of, pk_wP]
    rw [e1, pk_wP]
    exact Nat.eq_of_beq_eq_true h1
  have i2 : pk vP⁻¹ = wK (tgiW.getD 2 []) := by
    rw [pk_inv_of, pk_wP]
    rw [e2, pk_wP]
    exact Nat.eq_of_beq_eq_true h2
  rw [lt0K_gen]
  show [pk tP, pk uP, pk vP, pk tP⁻¹, pk uP⁻¹, pk vP⁻¹] = _
  rw [e0, e1, e2, i0, i1, i2]

theorem tP_mem : tP ∈ T0 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem uP_mem : uP ∈ T0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem vP_mem : vP ∈ T0 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem lt0_mem (x : P24) (hx : x ∈ lt0) : x ∈ T0 := by
  rcases List.mem_cons.1 hx with rfl | hx
  · exact tP_mem
  rcases List.mem_cons.1 hx with rfl | hx
  · exact uP_mem
  rcases List.mem_cons.1 hx with rfl | hx
  · exact vP_mem
  rcases List.mem_cons.1 hx with rfl | hx
  · exact T0.inv_mem tP_mem
  rcases List.mem_cons.1 hx with rfl | hx
  · exact T0.inv_mem uP_mem
  rcases List.mem_cons.1 hx with rfl | hx
  · exact T0.inv_mem vP_mem
  exact (List.not_mem_nil hx).elim

theorem tlK_mem_one : memB kId tlK = true := by decide +kernel

theorem pk_mem_lt0K {x : P24} (hx : x ∈ lt0) : pk x ∈ lt0K := by
  rw [← pk_lt0]
  exact List.mem_map_of_mem hx

theorem tP_mem_lt0 : tP ∈ lt0 := List.mem_cons_self ..

theorem uP_mem_lt0 : uP ∈ lt0 := List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem vP_mem_lt0 : vP ∈ lt0 :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem tPi_mem_lt0 : tP⁻¹ ∈ lt0 :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem uPi_mem_lt0 : uP⁻¹ ∈ lt0 :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem vPi_mem_lt0 : vP⁻¹ ∈ lt0 :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))

theorem pk_mul_lt0_mem {g y : P24} (hg : g ∈ lt0) (hy : pk y ∈ tlK) : pk (g * y) ∈ tlK := by
  have h1 := allB_iff.1 tlK_closed (pk y) hy
  have h2 := allB_iff.1 h1 (pk g) (pk_mem_lt0K hg)
  rw [pk_mul]
  exact memB_iff.1 h2

theorem mem_T0_iff (x : P24) : x ∈ T0 ↔ pk x ∈ tlK := by
  constructor
  · intro hx
    refine Subgroup.closure_induction_left (p := fun y _ => pk y ∈ tlK) ?_ ?_ ?_ hx
    · rw [pk_one]
      exact memB_iff.1 tlK_mem_one
    · intro g hg y _ hy
      rcases hg with rfl | hg
      · exact pk_mul_lt0_mem tP_mem_lt0 hy
      rcases hg with rfl | hg
      · exact pk_mul_lt0_mem uP_mem_lt0 hy
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact pk_mul_lt0_mem vP_mem_lt0 hy
    · intro g hg y _ hy
      rcases hg with rfl | hg
      · exact pk_mul_lt0_mem tPi_mem_lt0 hy
      rcases hg with rfl | hg
      · exact pk_mul_lt0_mem uPi_mem_lt0 hy
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact pk_mul_lt0_mem vPi_mem_lt0 hy
  · intro hx
    have hspec := chainR_spec lt0 rfl T0 lt0_mem tab0 [kId] (by rw [pk_lt0]; exact chain0)
      (by
        intro c hc
        refine ⟨1, T0.one_mem, ?_⟩
        rw [pk_one]
        exact (List.mem_singleton.1 hc).symm)
    rw [tlK_eq] at hx
    obtain ⟨e, he, hpe⟩ := hspec _ hx
    rw [← pk_injective hpe]
    exact he

theorem exists_of_mem_tlK {c : ℕ} (hc : c ∈ tlK) : ∃ e ∈ T0, pk e = c := by
  have hspec := chainR_spec lt0 rfl T0 lt0_mem tab0 [kId] (by rw [pk_lt0]; exact chain0)
    (by
      intro c hc
      refine ⟨1, T0.one_mem, ?_⟩
      rw [pk_one]
      exact (List.mem_singleton.1 hc).symm)
  rw [tlK_eq] at hc
  exact hspec _ hc

theorem card_T0 : Nat.card T0 = 128 := by
  let f : T0 → {c : ℕ // c ∈ tlK.toFinset} := fun x => ⟨pk x, List.mem_toFinset.2 ((mem_T0_iff x).1 x.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact Subtype.ext (pk_injective (congrArg Subtype.val hxy))
    · rintro ⟨c, hc⟩
      obtain ⟨e, he, hpe⟩ := exists_of_mem_tlK (List.mem_toFinset.1 hc)
      exact ⟨⟨e, he⟩, Subtype.ext hpe⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup (nodupB_iff.1 tlK_nodup), tlK_len]

theorem pk_z0P : pk z0P = zk := by
  rw [z0P, pk_wP, zk_eq]

theorem eq_z0P_of_central {z : P24} (hz1 : z ≠ 1) (hz2 : z * z = 1) (hzT : z ∈ T0)
    (hzc : ∀ t ∈ T0, t * z = z * t) : z = z0P := by
  have hx : pk z ∈ tlK := (mem_T0_iff z).1 hzT
  have h := allB_iff.1 zk_unique (pk z) hx
  have h1 : Nat.beq (pk z) kId = false := by
    cases hb : Nat.beq (pk z) kId
    · rfl
    · exact absurd (pk_injective ((Nat.eq_of_beq_eq_true hb).trans pk_one.symm)) hz1
  have h2 : Nat.beq (comp (pk z) (pk z)) kId = true := by
    have : comp (pk z) (pk z) = kId := by rw [← pk_mul, hz2, pk_one]
    rw [this]
    exact Nat.beq_refl _
  have h3 : allB (fun g => Nat.beq (comp (pk z) g) (comp g (pk z))) lt0K = true := by
    rw [allB_iff]
    intro g hg
    rw [← pk_lt0, List.mem_map] at hg
    obtain ⟨t, ht, rfl⟩ := hg
    have := hzc t (lt0_mem t ht)
    have h4 : comp (pk z) (pk t) = comp (pk t) (pk z) := by
      rw [← pk_mul, ← pk_mul, this]
    rw [h4]
    exact Nat.beq_refl _
  rw [h1, h2, h3] at h
  have h5 : Nat.beq (pk z) zk = true := by simpa using h
  exact pk_injective ((Nat.eq_of_beq_eq_true h5).trans pk_z0P.symm)

theorem pk_g3P : pk g3P = gk := by rw [g3P, pk_wP, gk_eq]

theorem pk_g3iP : pk g3iP = gik := by rw [g3iP, pk_wP, gik_eq]

theorem g3P_mul_g3iP : g3P * g3iP = 1 := by
  apply pk_injective
  rw [pk_mul, pk_g3P, pk_g3iP, pk_one]
  exact Nat.eq_of_beq_eq_true g_inv

theorem g3iP_eq : g3iP = g3P⁻¹ := eq_inv_of_mul_eq_one_right g3P_mul_g3iP

theorem g3P_comm : g3P * z0P = z0P * g3P := by
  apply pk_injective
  rw [pk_mul, pk_mul, pk_g3P, pk_z0P]
  exact Nat.eq_of_beq_eq_true g_comm

theorem mem_qgK_of {a : P24} (ha : a ∈ T0) (h1 : g3P * a * g3P⁻¹ ∈ T0)
    (h2 : g3P⁻¹ * a * g3P ∈ T0) : pk a ∈ qgK := by
  have hx : pk a ∈ tlK := (mem_T0_iff a).1 ha
  have h := allB_iff.1 qg_sub (pk a) hx
  have e1 : pk (g3P * a * g3P⁻¹) = comp (comp gk (pk a)) gik := by
    rw [pk_mul, pk_mul, pk_g3P, ← g3iP_eq, pk_g3iP]
  have e2 : pk (g3P⁻¹ * a * g3P) = comp (comp gik (pk a)) gk := by
    rw [pk_mul, pk_mul, pk_g3P, ← g3iP_eq, pk_g3iP]
  have m1 : memB (comp (comp gk (pk a)) gik) tlK = true := by
    rw [← e1]
    exact memB_iff.2 ((mem_T0_iff _).1 h1)
  have m2 : memB (comp (comp gik (pk a)) gk) tlK = true := by
    rw [← e2]
    exact memB_iff.2 ((mem_T0_iff _).1 h2)
  rw [m1, m2] at h
  have h' : memB (pk a) qgK = true := by simpa using h
  exact memB_iff.1 h'

theorem card_le_twelve (A : Subgroup P24) {x : P24} (hxA : x ∈ A) (hx1 : x ≠ 1) (hxz : x ≠ z0P)
    (hqg : ∀ a ∈ A, pk a ∈ qgK) (hsq : ∀ a ∈ A, a * a = 1) (hcomm : ∀ a ∈ A, x * a = a * x) :
    Nat.card A ≤ 12 := by
  let q : ℕ → Bool := fun y => Nat.beq (comp y y) kId && Nat.beq (comp (pk x) y) (comp y (pk x))
  have hxq := hqg x hxA
  have hcount := allB_iff.1 qg_count (pk x) hxq
  have hb1 : Nat.beq (pk x) kId = false := by
    cases hb : Nat.beq (pk x) kId
    · rfl
    · exact absurd (pk_injective ((Nat.eq_of_beq_eq_true hb).trans pk_one.symm)) hx1
  have hb2 : Nat.beq (comp (pk x) (pk x)) kId = true := by
    have : comp (pk x) (pk x) = kId := by rw [← pk_mul, hsq x hxA, pk_one]
    rw [this]
    exact Nat.beq_refl _
  have hb3 : Nat.beq (pk x) zk = false := by
    cases hb : Nat.beq (pk x) zk
    · rfl
    · exact absurd (pk_injective ((Nat.eq_of_beq_eq_true hb).trans pk_z0P.symm)) hxz
  rw [hb1, hb2, hb3] at hcount
  have hle : cntB q qgK ≤ 12 := by simpa using hcount
  rw [cntB_eq] at hle
  let S : Finset ℕ := (qgK.filter q).toFinset
  have hS : S.card ≤ 12 := (List.toFinset_card_le _).trans hle
  let f : A → {c : ℕ // c ∈ S} := fun a => ⟨pk a, by
    rw [List.mem_toFinset, List.mem_filter]
    refine ⟨hqg a a.2, ?_⟩
    show (Nat.beq (comp (pk a) (pk a)) kId && Nat.beq (comp (pk x) (pk a)) (comp (pk a) (pk x))) = true
    have e1 : comp (pk a) (pk a) = kId := by rw [← pk_mul, hsq a a.2, pk_one]
    have e2 : comp (pk x) (pk a) = comp (pk a) (pk x) := by
      rw [← pk_mul, ← pk_mul, hcomm a a.2]
    rw [e1, e2, Nat.beq_refl, Nat.beq_refl]
    rfl⟩
  have hinj : Function.Injective f := fun a b hab => Subtype.ext (pk_injective (congrArg Subtype.val hab))
  have h1 := Nat.card_le_card_of_injective f hinj
  have e : Nat.card {c : ℕ // c ∈ S} = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [e] at h1
  exact h1.trans hS

end CFSG.Quasithin.ModE
