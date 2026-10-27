module

public import CFSG.RankThree.GF2n.Tim77.Sec53Hyp
public import CFSG.RankThree.GF2n.Tim77.Sec51Basic
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

theorem sec53n_pair [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hq : Section3.q A Abar = 2) {a : G} (ha2 : a * a = 1)
    (hcomm0 : ∀ x ∈ Section3.Abar0 A Abar, ∀ y ∈ conjSubgroup a (Section3.Abar0 A Abar),
      x * y = y * x)
    (hnc : ¬ ∀ x ∈ Abar, ∀ y ∈ conjSubgroup a Abar, x * y = y * x) :
    Prop24Setup Abar (conjSubgroup a Abar) (Section3.Abar0 A Abar)
      (conjSubgroup a (Section3.Abar0 A Abar))
      (Section3.Abar0 A Abar ⊔ conjSubgroup a (Section3.Abar0 A Abar)) := by
  have hS := h.setup
  unfold Section3.q at hq
  have hTI : IsTI (conjSubgroup a Abar) := isTI_conjSubgroup hS.ti_Ab a
  have hle : Section3.Abar0 A Abar ≤ normalizer (conjSubgroup a Abar : Set G) := by
    intro e he
    obtain ⟨u, hu, hu1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hS.Lb_ne_bot
    have hmemC : a * u * a⁻¹ ∈ conjSubgroup a Abar :=
      (mem_conjSubgroup_conj_t77 a u Abar).2 (hS.Lb_le hu)
    have hmem0 : a * u * a⁻¹ ∈ conjSubgroup a (Section3.Abar0 A Abar) :=
      (mem_conjSubgroup_conj_t77 a u _).2 hu
    exact mem_normalizer_of_commute_of_isTI hTI hmemC
      (fun e1 => hu1 ((conj_eq_one_iff_t77 a u).1 e1)) (hcomm0 e he _ hmem0)
  have hne : Abar ⊓ normalizer (conjSubgroup a Abar : Set G) ≠ Abar := by
    intro heq
    apply hnc
    have hAN : Abar ≤ normalizer (conjSubgroup a Abar : Set G) := fun x hx => by
      have : x ∈ Abar ⊓ normalizer (conjSubgroup a Abar : Set G) := by rw [heq]; exact hx
      exact (Subgroup.mem_inf.mp this).2
    have key := sec51_comm_of_le_normalizer (isElemAbelian_conj hS.elem_Ab a) hTI
      (sec51_conj_of_conj (X := Abar) (Y := conjSubgroup a Abar) (k := a) rfl) hAN
    intro x hx y hy
    exact (key y hy x hx).symm
  have hsqAb : ∀ x ∈ Abar, x * x = 1 := fun x hx => hS.sq_Ab hx
  have hcAb : ∀ x ∈ Abar, ∀ y ∈ Abar, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hS.elem_Ab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hle2 : Abar ⊓ normalizer (conjSubgroup a Abar : Set G) ≤ Section3.Abar0 A Abar := by
    intro e he
    by_contra he0
    apply hne
    refine le_antisymm inf_le_left (fun y hy => ?_)
    by_cases hy0 : y ∈ Section3.Abar0 A Abar
    · exact Subgroup.mem_inf.mpr ⟨hy, hle hy0⟩
    · have hmul : e * y ∈ Section3.Abar0 A Abar :=
        sec53_mul_mem_of_relIndex_two hcAb hsqAb hq (Subgroup.mem_inf.mp he).1 hy he0 hy0
      have h1 : e⁻¹ * (e * y) ∈ Abar ⊓ normalizer (conjSubgroup a Abar : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ he) (Subgroup.mem_inf.mpr ⟨hS.Lb_le hmul, hle hmul⟩)
      simpa using h1
  have hL : Section3.Abar0 A Abar = Abar ⊓ normalizer (conjSubgroup a Abar : Set G) :=
    le_antisymm (le_inf hS.Lb_le hle) hle2
  refine
    { elem := hS.elem_Ab
      ti := hS.ti_Ab
      conj := ⟨a, rfl⟩
      hL := hL
      hLb := ?_
      hM := rfl
      ne_bot := hS.Lb_ne_bot
      ne := hS.Lb_ne }
  rw [hL, conjSubgroup_inf, conjSubgroup_map_normalizer, ← conjSubgroup_mul, ha2,
    conjSubgroup_one]

theorem sec53n_dih [Finite G] {Abar L L' M' : Subgroup G} {a : G} (ha2 : a * a = 1)
    (P : Prop24Setup Abar (conjSubgroup a Abar) L L' M') {x : G} (hx : x ∈ Abar) (hxL : x ∉ L) :
    ∃ g z : G, g ∈ normalizer (M' : Set G) ∧ z * z = 1 ∧ z * a = a * z ∧ z * x = x * z ∧
      g⁻¹ * x * g = z * a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hy : a * x * a ∈ conjSubgroup a Abar := by
    have := (mem_conjSubgroup_conj_t77 a x Abar).2 hx
    rwa [hai] at this
  have hyL' : a * x * a ∉ L' := by
    intro hmem
    apply hxL
    rw [P.mem_L]
    refine ⟨hx, ?_⟩
    have h1 := (P.mem_Lb.mp hmem).2
    rw [← conjSubgroup_map_normalizer, mem_conjSubgroup, hai]
    exact h1
  have hodd := P.odd_orderOf_mul hx hxL hy hyL'
  have hx2 : x * x = 1 := P.sq_A hx
  obtain ⟨hz2, hza, hzx, -, hg⟩ := sec51_dih_odd hx2 ha2 hodd (by
    have e : (x * a) * (x * a) = x * (a * x * a) := by group
    rw [e])
  have hrM : x * a ∈ normalizer (M' : Set G) :=
    Subgroup.mul_mem _ (P.A_le_normalizer_M hx) (sec51_swap_M ha2 P)
  exact ⟨(x * a) ^ ((orderOf (x * (a * x * a)) + 1) / 2), (x * a) ^ orderOf (x * (a * x * a)),
    Subgroup.pow_mem _ hrM _, hz2, hza, hzx, hg⟩

theorem sec53n_two_ne_one [Finite G] {D : Subgroup G} (h : 2 < Nat.card D) :
    ∃ d₁ ∈ D, ∃ d₂ ∈ D, d₁ ≠ 1 ∧ d₂ ≠ 1 ∧ d₁ ≠ d₂ := by
  haveI : Fintype D := Fintype.ofFinite D
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h
  by_cases ha : (a : G) = 1
  · have hb : (b : G) ≠ 1 := fun hb => hab (Subtype.ext (ha.trans hb.symm))
    have hc : (c : G) ≠ 1 := fun hc => hac (Subtype.ext (ha.trans hc.symm))
    exact ⟨(b : G), b.2, (c : G), c.2, hb, hc, fun e => hbc (Subtype.ext e)⟩
  · by_cases hb : (b : G) = 1
    · have hc : (c : G) ≠ 1 := fun hc => hbc (Subtype.ext (hb.trans hc.symm))
      exact ⟨(a : G), a.2, (c : G), c.2, ha, hc, fun e => hac (Subtype.ext e)⟩
    · exact ⟨(a : G), a.2, (b : G), b.2, ha, hb, fun e => hab (Subtype.ext e)⟩

theorem sec53n_card_le_sq_fixed [Finite G] {V : Subgroup G} {a : G}
    (ha2 : a * a = 1) (hc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hsq : ∀ x ∈ V, x * x = 1)
    (haV : ∀ x ∈ V, a * x * a ∈ V) :
    Nat.card V ≤ Nat.card (V ⊓ Subgroup.centralizer {a} : Subgroup G) ^ 2 := by
  have hconj : ∀ x y : G, a * x * a * (a * y * a) = a * (x * y) * a := by
    intro x y
    calc a * x * a * (a * y * a) = a * x * (a * a) * y * a := by simp only [mul_assoc]
      _ = a * (x * y) * a := by rw [ha2]; simp only [mul_one, mul_assoc]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : V →* V, ∀ v : V, ((ψ v : V) : G) = (v : G) * (a * (v : G) * a) := by
    refine ⟨MonoidHom.mk' (fun v : V => (⟨(v : G) * (a * (v : G) * a),
      V.mul_mem v.2 (haV _ v.2)⟩ : V)) ?_, fun v => rfl⟩
    intro v w
    apply Subtype.ext
    show (v : G) * (w : G) * (a * ((v : G) * (w : G)) * a)
      = (v : G) * (a * (v : G) * a) * ((w : G) * (a * (w : G) * a))
    rw [← hconj (v : G) (w : G)]
    have hcomm : (w : G) * (a * (v : G) * a) = (a * (v : G) * a) * (w : G) :=
      hc _ w.2 _ (haV _ v.2)
    calc (v : G) * (w : G) * (a * (v : G) * a * (a * (w : G) * a))
        = (v : G) * ((w : G) * (a * (v : G) * a)) * (a * (w : G) * a) := by
          simp only [mul_assoc]
      _ = (v : G) * ((a * (v : G) * a) * (w : G)) * (a * (w : G) * a) := by
          rw [hcomm]
      _ = (v : G) * (a * (v : G) * a) * ((w : G) * (a * (w : G) * a)) := by
          simp only [mul_assoc]
  have hW : ∀ x : G, x ∈ V →
      x * (a * x * a) ∈ (V ⊓ Subgroup.centralizer {a} : Subgroup G) := by
    intro x hx
    have hu : a * x * a ∈ V := haV x hx
    have key : a * x * a * x = x * (a * x * a) := hc _ hu _ hx
    have hcomm : a * (x * (a * x * a)) = x * (a * x * a) * a := by
      calc a * (x * (a * x * a)) = a * x * a * x * a := by simp only [mul_assoc]
        _ = x * (a * x * a) * a := by rw [key]
    rw [Subgroup.mem_inf]
    refine ⟨V.mul_mem hx hu, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hcomm
  have hK : ∀ x : V, ψ x = 1 → (x : G) ∈ (V ⊓ Subgroup.centralizer {a} : Subgroup G) := by
    intro x hx
    have h1 : (x : G) * (a * (x : G) * a) = 1 := by
      rw [← hψ x]
      simp [hx]
    have hxx : (x : G) * (x : G) = 1 := hsq (x : G) x.2
    have h2 : a * (x : G) * a = (x : G) := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_eq_of_mul_eq_one_right hxx
    have h5 : a * (x : G) = a * (x : G) * a * a := by
      rw [mul_assoc (a * (x : G)) a a, ha2, mul_one]
    have h4 : a * (x : G) = (x : G) * a := by
      rw [h5, h2]
    rw [Subgroup.mem_inf]
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact h4
  have hR : ∀ y : V, y ∈ ψ.range → (y : G) ∈ (V ⊓ Subgroup.centralizer {a} : Subgroup G) := by
    intro y hy
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [hψ v]
    exact hW (v : G) v.2
  have hk : Nat.card ψ.ker ≤ Nat.card (V ⊓ Subgroup.centralizer {a} : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun x : ψ.ker => (⟨((x : V) : G), hK (x : V) (MonoidHom.mem_ker.mp x.2)⟩ :
        (V ⊓ Subgroup.centralizer {a} : Subgroup G))) ?_
    intro x y hxy
    have h := congrArg (fun z : (V ⊓ Subgroup.centralizer {a} : Subgroup G) => (z : G)) hxy
    exact Subtype.ext (Subtype.ext h)
  have hr : Nat.card ψ.range ≤ Nat.card (V ⊓ Subgroup.centralizer {a} : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun y : ψ.range => (⟨((y : V) : G), hR (y : V) y.2⟩ :
        (V ⊓ Subgroup.centralizer {a} : Subgroup G))) ?_
    intro x y hxy
    have h := congrArg (fun z : (V ⊓ Subgroup.centralizer {a} : Subgroup G) => (z : G)) hxy
    exact Subtype.ext (Subtype.ext h)
  have hcard : Nat.card V = Nat.card ψ.ker * Nat.card ψ.range := by
    have h := Subgroup.card_mul_index (H := ψ.ker)
    rw [Subgroup.index_ker] at h
    exact h.symm
  rw [hcard, sq]
  exact Nat.mul_le_mul hk hr

theorem sec53n_F1 [Finite G] {A Ab L Lb M Z : Subgroup G} (S : Prop24Setup A Ab L Lb M)
    (hq : L.relIndex A = 2) (hZ : Z ≤ L) (hZi : Z.relIndex L = 2) :
    ∃ F : Subgroup G, F ≤ Lb ∧ F.relIndex Lb = 2 ∧
      ∀ u ∈ F, ∀ x ∈ A, x * u * x⁻¹ * u⁻¹ ∈ Z := by
  have hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => S.comm_A hx hy
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => S.sq_A hx
  obtain ⟨t, ht, htL⟩ : ∃ t ∈ A, t ∉ L := by
    by_contra hcon
    push Not at hcon
    exact S.ne (le_antisymm S.L_le (fun x hx => hcon x hx))
  let χ : ↥Lb →* ↥L := MonoidHom.mk'
    (fun n : ↥Lb => (⟨t * (n : G) * t⁻¹ * (n : G)⁻¹, S.commutator_mem_L ht n.2⟩ : ↥L))
    (fun n m => Subtype.ext
      (sec53_commutator_mul_right (S.comm_L_Lb (S.commutator_mem_L ht m.2) n.2).symm))
  have hinj : Function.Injective χ := S.commutator_injective ht htL
  have hχsurj : Function.Surjective χ :=
    (Function.Injective.bijective_of_nat_card_le hinj S.card_Lb_eq.ge).2
  obtain ⟨F', hF'⟩ : ∃ F' : Subgroup Lb, F' = (Z.subgroupOf L).comap χ := ⟨_, rfl⟩
  have hF'idx : F'.index = 2 := by
    rw [hF', Subgroup.index_comap_of_surjective _ hχsurj]
    exact hZi
  have hkey : ∀ n ∈ F', t * (n : G) * t⁻¹ * (n : G)⁻¹ ∈ Z := by
    intro n hn
    rw [hF', Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hn
    exact hn
  have hP : ∀ x ∈ F'.map Lb.subtype, ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ Z := by
    intro x hx a ha
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    show a * (n : G) * a⁻¹ * (n : G)⁻¹ ∈ Z
    have hnLb : (n : G) ∈ Lb := n.2
    have hnN : (n : G) ∈ Subgroup.normalizer (A : Set G) := (S.mem_Lb.mp hnLb).2
    by_cases haL : a ∈ L
    · have hcomm : a * (n : G) = (n : G) * a := S.comm_L_Lb haL hnLb
      have e : a * (n : G) * a⁻¹ * (n : G)⁻¹ = 1 := by
        calc a * (n : G) * a⁻¹ * (n : G)⁻¹ = (n : G) * a * a⁻¹ * (n : G)⁻¹ := by rw [hcomm]
          _ = 1 := by group
      rw [e]
      exact Subgroup.one_mem _
    · have hat : a * t ∈ L := sec53_mul_mem_of_relIndex_two hA hsq hq ha ht haL htL
      have hatA : a * t ∈ A := A.mul_mem ha ht
      have hcomm : (a * t) * (n : G) = (n : G) * (a * t) := S.comm_L_Lb hat hnLb
      have h1 : (a * t) * (n : G) * (a * t)⁻¹ * (n : G)⁻¹ = 1 := by
        calc (a * t) * (n : G) * (a * t)⁻¹ * (n : G)⁻¹
            = (n : G) * (a * t) * (a * t)⁻¹ * (n : G)⁻¹ := by rw [hcomm]
          _ = 1 := by group
      have ea : a * t * t = a := by rw [mul_assoc, hsq t ht, mul_one]
      have e2 : a * (n : G) * a⁻¹ * (n : G)⁻¹ = t * (n : G) * t⁻¹ * (n : G)⁻¹ := by
        calc a * (n : G) * a⁻¹ * (n : G)⁻¹
            = (a * t * t) * (n : G) * (a * t * t)⁻¹ * (n : G)⁻¹ := by rw [ea]
          _ = ((a * t) * (n : G) * (a * t)⁻¹ * (n : G)⁻¹) *
                (t * (n : G) * t⁻¹ * (n : G)⁻¹) :=
              sec53_commutator_mul_left hA hnN hatA ht
          _ = t * (n : G) * t⁻¹ * (n : G)⁻¹ := by rw [h1, one_mul]
      rw [e2]
      exact hkey n hn
  have hsub : (F'.map Lb.subtype).subgroupOf Lb = F' := by
    ext n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, hmn⟩
      have hmn' : m = n := Subtype.ext hmn
      rw [← hmn']
      exact hm
    · intro hn
      exact ⟨n, hn, rfl⟩
  have hrel : (F'.map Lb.subtype).relIndex Lb = 2 := by
    show ((F'.map Lb.subtype).subgroupOf Lb).index = 2
    rw [hsub]
    exact hF'idx
  exact ⟨F'.map Lb.subtype, Subgroup.map_subtype_le F', hrel, hP⟩

theorem sec53n_K {A Z : Subgroup G} {a u : G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hZA : Z ≤ A) (ha2 : a * a = 1) (hu2 : u * u = 1) (hau : Sec51Tr A Z a)
    (huu : Sec51Tr A Z u) {x : G} (hx : x ∈ A) :
    u * (a * u * a) * x = x * (u * (a * u * a)) := by
  have h := Sec51Tr.sq_comm hA hZA hu2 ha2 huu hau hx
  rwa [show u * a * (u * a) = u * (a * u * a) by group] at h

theorem sec53n_exists_v [Finite G] {E E' F V : Subgroup G} {a : G} (ha2 : a * a = 1)
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEs : ∀ x ∈ E, x * x = 1)
    (hEE' : ∀ x ∈ E, ∀ y ∈ E', x * y = y * x) (hinf : E ⊓ E' = ⊥)
    (hswap : ∀ x ∈ E, a * x * a ∈ E') (hswap' : ∀ y ∈ E', a * y * a ∈ E)
    (hFE : F ≤ E) (hF : F.relIndex E = 2)
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVs : ∀ x ∈ V, x * x = 1)
    (hVM : V ≤ E ⊔ E') (haV : ∀ x ∈ V, a * x * a ∈ V) (hVcard : 8 ≤ Nat.card V) :
    ∃ u ∈ F, u * (a * u * a) ∈ V ∧ u * (a * u * a) ≠ 1 := by
  have hφ : ∀ e ∈ E, ∀ e' ∈ E, e * (a * e * a) * (e' * (a * e' * a)) =
      (e * e') * (a * (e * e') * a) := by
    intro e he e' he'
    have hc : (a * e * a) * e' = e' * (a * e * a) := (hEE' e' he' _ (hswap e he)).symm
    have hcc : (a * e * a) * (a * e' * a) = a * (e * e') * a := by
      calc (a * e * a) * (a * e' * a) = a * e * (a * a) * e' * a := by group
        _ = a * (e * e') * a := by rw [ha2]; group
    calc e * (a * e * a) * (e' * (a * e' * a))
        = e * ((a * e * a) * e') * (a * e' * a) := by group
      _ = e * (e' * (a * e * a)) * (a * e' * a) := by rw [hc]
      _ = (e * e') * ((a * e * a) * (a * e' * a)) := by group
      _ = (e * e') * (a * (e * e') * a) := by rw [hcc]
  have hφ1 : ∀ e ∈ E, e * (a * e * a) = 1 → e = 1 := by
    intro e he h1
    have hmem : e ∈ E' := by
      have h2 : e = (a * e * a)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact E'.inv_mem (hswap e he)
    have : e ∈ E ⊓ E' := Subgroup.mem_inf.mpr ⟨he, hmem⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  have hD : 2 < Nat.card (V ⊓ Subgroup.centralizer {a} : Subgroup G) := by
    by_contra hle
    push Not at hle
    have h1 := sec53n_card_le_sq_fixed ha2 hVc hVs haV
    have h2 : Nat.card (V ⊓ Subgroup.centralizer {a} : Subgroup G) ^ 2 ≤ 2 ^ 2 :=
      Nat.pow_le_pow_left hle 2
    omega
  obtain ⟨d₁, hd₁, d₂, hd₂, h1, h2, h12⟩ := sec53n_two_ne_one hD
  have hdec : ∀ d ∈ V ⊓ Subgroup.centralizer {a}, ∃ e ∈ E, d = e * (a * e * a) := by
    intro d hd
    obtain ⟨hdV, hdC⟩ := Subgroup.mem_inf.mp hd
    have hcomm : a * d = d * a := Subgroup.mem_centralizer_iff.mp hdC a (Set.mem_singleton a)
    exact sec51_fixed_decomp ha2 hEE' hinf hswap hswap' (hVM hdV) hcomm
  have hV₁ : d₁ ∈ V := (Subgroup.mem_inf.mp hd₁).1
  have hV₂ : d₂ ∈ V := (Subgroup.mem_inf.mp hd₂).1
  obtain ⟨e₁, he₁, rfl⟩ := hdec d₁ hd₁
  obtain ⟨e₂, he₂, rfl⟩ := hdec d₂ hd₂
  by_cases hF1 : e₁ ∈ F
  · exact ⟨e₁, hF1, hV₁, h1⟩
  by_cases hF2 : e₂ ∈ F
  · exact ⟨e₂, hF2, hV₂, h2⟩
  refine ⟨e₁ * e₂, sec53_mul_mem_of_relIndex_two hEc hEs hF he₁ he₂ hF1 hF2, ?_, ?_⟩
  · rw [← hφ e₁ he₁ e₂ he₂]
    exact V.mul_mem hV₁ hV₂
  · intro h0
    have h3 : e₁ * e₂ = 1 := hφ1 (e₁ * e₂) (E.mul_mem he₁ he₂) h0
    apply h12
    have h4 : e₂ = e₁ := by
      rw [eq_inv_of_mul_eq_one_right h3]
      exact inv_eq_of_mul_eq_one_right (hEs e₁ he₁)
    rw [h4]

theorem sec53n_heart [Finite G] {A Abar S₀ B Z F₁ L' M₁ : Subgroup G}
    (h : Sec3Ctx A Abar S₀ B) {a : G} (ha2 : a * a = 1)
    (P : Prop24Setup Abar (conjSubgroup a Abar) (Section3.Abar0 A Abar) L' M₁)
    (hZ : Z ≤ Section3.A0 A Abar) (hTra : Sec51Tr A Z a)
    (hFle : F₁ ≤ Section3.Abar0 A Abar) (hFi : F₁.relIndex (Section3.Abar0 A Abar) = 2)
    (hFc : ∀ u ∈ F₁, ∀ x ∈ A, x * u * x⁻¹ * u⁻¹ ∈ Z)
    (h8 : 8 ≤ Nat.card (Section3.A0 A Abar)) {x g z : G} (hxA : x ∈ Abar)
    (hxL : x ∉ Section3.Abar0 A Abar) (hgM : g ∈ normalizer (M₁ : Set G))
    (hza : z * a = a * z) (hg : g⁻¹ * x * g = z * a) :
    ∀ w ∈ A, (z * a) * w = w * (z * a) := by
  have hS := h.setup
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  obtain ⟨g₀, hg₀⟩ := h.exists_abar_eq
  have hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hS.comm_A hx hy
  have hx1 : x ≠ 1 := fun e => hxL (e ▸ Subgroup.one_mem _)
  have hVel : IsElemAbelian 2 (conjSubgroup g⁻¹ Abar) := isElemAbelian_conj hS.elem_Ab g⁻¹
  have hVTI : IsTI (conjSubgroup g⁻¹ Abar) := isTI_conjSubgroup hS.ti_Ab g⁻¹
  have hVconj : conjSubgroup g⁻¹ Abar = conjSubgroup (g⁻¹ * g₀) A := by
    rw [hg₀, conjSubgroup_mul]
  have hcV : z * a ∈ conjSubgroup g⁻¹ Abar := by
    have := (mem_conjSubgroup_conj_t77 g⁻¹ x Abar).2 hxA
    rw [inv_inv] at this
    rwa [← hg]
  have hc1 : z * a ≠ 1 := by
    rw [← hg]
    intro e
    apply hx1
    exact (conj_eq_one_iff_t77 g⁻¹ x).1 (by rwa [inv_inv])
  have haV : a ∈ normalizer (conjSubgroup g⁻¹ Abar : Set G) := by
    refine mem_normalizer_of_commute_of_isTI hVTI hcV hc1 ?_
    calc a * (z * a) = (a * z) * a := by group
      _ = (z * a) * a := by rw [hza]
  have haM : a ∈ normalizer (M₁ : Set G) := sec51_swap_M ha2 P
  have haVM : a ∈ normalizer ((conjSubgroup g⁻¹ Abar ⊓ M₁ : Subgroup G) : Set G) :=
    mem_normalizer_inf haV haM
  have hV0 : conjSubgroup g⁻¹ Abar ⊓ M₁ = conjSubgroup g⁻¹ (Section3.Abar0 A Abar) := by
    have h1 : conjSubgroup g⁻¹ M₁ = M₁ := conjSubgroup_eq_self_iff.mpr (Subgroup.inv_mem _ hgM)
    calc conjSubgroup g⁻¹ Abar ⊓ M₁ = conjSubgroup g⁻¹ Abar ⊓ conjSubgroup g⁻¹ M₁ := by
          rw [h1]
      _ = conjSubgroup g⁻¹ (Abar ⊓ M₁) := (conjSubgroup_inf _ _ _).symm
      _ = conjSubgroup g⁻¹ (Section3.Abar0 A Abar) := by rw [P.inf_M]
  have hinf : Section3.Abar0 A Abar ⊓ L' = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf P.L_le P.Lb_le) (le_of_eq P.inf_eq_bot))
  obtain ⟨hswap, hswap'⟩ := sec51_swap_L ha2 P
  obtain ⟨u, huF, huV, hu1⟩ := sec53n_exists_v (E := Section3.Abar0 A Abar) (E' := L')
    (F := F₁) (V := conjSubgroup g⁻¹ Abar ⊓ M₁) ha2
    (fun x hx y hy => P.comm_A (hS.Lb_le hx) (hS.Lb_le hy))
    (fun x hx => P.sq_A (hS.Lb_le hx)) (fun x hx y hy => P.comm_L_Lb hx hy) hinf hswap hswap'
    hFle hFi
    (fun x hx y hy => P.comm_M (Subgroup.mem_inf.mp hx).2 (Subgroup.mem_inf.mp hy).2)
    (fun x hx => by
      rw [← sq]
      exact P.isElemAbelian_M.2 x (Subgroup.mem_inf.mp hx).2)
    (inf_le_right.trans (le_of_eq P.hM))
    (fun x hx => by
      have := (Subgroup.mem_normalizer_iff.mp haVM x).mp hx
      rwa [hai] at this)
    (by rw [hV0, card_conjSubgroup, hS.card_Lb_eq]; exact h8)
  have hu0 : u ∈ Section3.Abar0 A Abar := hFle huF
  have hu2 : u * u = 1 := P.sq_A (hS.Lb_le hu0)
  have hTru : Sec51Tr A Z u :=
    { mem_normalizer := (hS.mem_Lb.mp hu0).2
      comm_zero := fun y hy => (hS.comm_L_Lb (hZ hy) hu0).symm
      commutator_mem := fun x hx => by
        have h1 := Z.inv_mem (hFc u huF x hx)
        have e : u * x * u⁻¹ * x⁻¹ = (x * u * x⁻¹ * u⁻¹)⁻¹ := by group
        rw [e]
        exact h1 }
  have hK : ∀ w ∈ A, u * (a * u * a) * w = w * (u * (a * u * a)) := fun w hw =>
    sec53n_K hA (hZ.trans hS.L_le) ha2 hu2 hTra hTru hw
  have hvV : u * (a * u * a) ∈ conjSubgroup g⁻¹ Abar := (Subgroup.mem_inf.mp huV).1
  have hAN : A ≤ normalizer (conjSubgroup g⁻¹ Abar : Set G) := fun w hw =>
    mem_normalizer_of_commute_of_isTI hVTI hvV hu1 (hK w hw).symm
  have hVA := sec51_comm_of_le_normalizer hVel hVTI (sec51_conj_of_conj hVconj) hAN
  intro w hw
  exact hVA _ hcV w hw

theorem sec53n_mem_normalizer_of_comm {A : Subgroup G} {c : G}
    (hc : ∀ w ∈ A, c * w = w * c) : c ∈ normalizer (A : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · have e : c * w * c⁻¹ = w := by rw [hc w hw]; group
    rw [e]
    exact hw
  · have e : w = c * w * c⁻¹ := by
      calc w = c⁻¹ * ((c * w * c⁻¹) * c) := by group
        _ = c⁻¹ * (c * (c * w * c⁻¹)) := by rw [← hc _ hw]
        _ = c * w * c⁻¹ := by group
    rw [e]
    exact hw

theorem sec53_nonelem [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hq : Section3.q A Abar = 2) {a : G}
    (haN : a ∈ normalizer (A : Set G)) (haN0 : a ∈ normalizer (Section3.A0 A Abar : Set G))
    (ha2 : a * a = 1) {Z : Subgroup G} (hZ : Z ≤ Section3.A0 A Abar)
    (hZi : Z.relIndex (Section3.A0 A Abar) = 2)
    (haZ : ∀ x ∈ A, a * x * a * x⁻¹ ∈ Z)
    (hCa : ∀ x ∈ Section3.A0 A Abar, (a * x * a = x ↔ x ∈ Z))
    (h8 : 8 ≤ Nat.card (Section3.A0 A Abar))
    (hcomm0 : ∀ x ∈ Section3.Abar0 A Abar, ∀ y ∈ conjSubgroup a (Section3.Abar0 A Abar),
      x * y = y * x)
    (hnc : ¬ ∀ x ∈ Abar, ∀ y ∈ conjSubgroup a Abar, x * y = y * x) :
    ∃ y : G, y ∈ normalizer (A : Set G) ∧ y ∈ normalizer (Abar : Set G) ∧
      ∀ x ∈ A, y * x * y⁻¹ = a * x * a⁻¹ := by
  have hS := h.setup
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have P := sec53n_pair h hq ha2 hcomm0 hnc
  have hq' : (Section3.A0 A Abar).relIndex A = 2 := by
    rw [← hS.relIndex_Lb]
    exact hq
  obtain ⟨F₁, hFle, hFi, hFc⟩ := sec53n_F1 hS hq' hZ hZi
  have hTra : Sec51Tr A Z a :=
    { mem_normalizer := haN
      comm_zero := fun y hy => by
        have h1 : a * y * a = y := (hCa y (hZ hy)).mpr hy
        calc a * y = a * y * a * a := by rw [mul_assoc _ a a, ha2, mul_one]
          _ = y * a := by rw [h1]
      commutator_mem := fun x hx => by
        rw [hai]
        exact haZ x hx }
  obtain ⟨x, hxA, hxL⟩ : ∃ x ∈ Abar, x ∉ Section3.Abar0 A Abar :=
    SetLike.exists_of_lt (lt_of_le_of_ne hS.Lb_le hS.Lb_ne)
  have hx1 : x ≠ 1 := fun e => hxL (e ▸ Subgroup.one_mem _)
  obtain ⟨g, z, hgM, -, hza, hzx, hg⟩ := sec53n_dih ha2 P hxA hxL
  have hcen := sec53n_heart h ha2 P hZ hTra hFle hFi hFc h8 hxA hxL hgM hza hg
  have hzc : z = (z * a) * a := by rw [mul_assoc, ha2, mul_one]
  have hcN : z * a ∈ normalizer (A : Set G) := sec53n_mem_normalizer_of_comm hcen
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [hzc]
    exact Subgroup.mul_mem _ hcN haN
  · exact mem_normalizer_of_commute_of_isTI hS.ti_Ab hxA hx1 hzx
  · intro w hw
    have hw' : a * w * a⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp haN w).mp hw
    have e1 : (z * a) * (a * w * a⁻¹) = (a * w * a⁻¹) * (z * a) := hcen _ hw'
    calc z * w * z⁻¹ = ((z * a) * a) * w * ((z * a) * a)⁻¹ := by rw [← hzc]
      _ = (z * a) * (a * w * a⁻¹) * (z * a)⁻¹ := by group
      _ = (a * w * a⁻¹) * (z * a) * (z * a)⁻¹ := by rw [e1]
      _ = a * w * a⁻¹ := by group

end CFSG.RankThree.GF2n.Tim77
