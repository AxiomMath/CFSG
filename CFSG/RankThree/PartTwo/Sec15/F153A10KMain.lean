module

public import CFSG.RankThree.PartTwo.Sec15.F153A10KDefs
public import CFSG.RankThree.PartTwo.Sec15.F153A10

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153A10K

open Equiv
open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator

theorem fixV_sup {V : Type} [CommGroup V] (A B : Subgroup (MulAut V)) :
    fixV (A ⊔ B) = fixV A ⊓ fixV B := by
  ext v
  simp only [Subgroup.mem_inf, mem_fixV]
  constructor
  · intro hv
    exact ⟨fun x hx => hv x ((le_sup_left : A ≤ A ⊔ B) hx),
      fun x hx => hv x ((le_sup_right : B ≤ A ⊔ B) hx)⟩
  · rintro ⟨hA, hB⟩
    obtain ⟨S, hS⟩ : ∃ S : Subgroup (MulAut V), ∀ x : MulAut V, x ∈ S ↔ x v = v := by
      refine ⟨{ carrier := {x | x v = v}
                mul_mem' := ?_
                one_mem' := ?_
                inv_mem' := ?_ }, fun x => Iff.rfl⟩
      · intro a b ha hb
        have ha' : a v = v := ha
        have hb' : b v = v := hb
        show (a * b) v = v
        rw [MulAut.mul_apply, hb', ha']
      · show (1 : MulAut V) v = v
        rfl
      · intro a ha
        have ha' : a v = v := ha
        show a⁻¹ v = v
        rw [MulAut.inv_apply]
        exact (MulEquiv.symm_apply_eq a).mpr ha'.symm
    have hABS : A ⊔ B ≤ S :=
      sup_le (fun x hx => (hS x).mpr (hA x hx)) (fun x hx => (hS x).mpr (hB x hx))
    intro x hx
    exact (hS x).mp (hABS hx)

theorem fixV_map_conj {V : Type} [CommGroup V] (A : Subgroup (MulAut V)) (g : MulAut V) :
    fixV (A.map (MulAut.conj g).toMonoidHom) = (fixV A).map g.toMonoidHom := by
  ext v
  constructor
  · intro h
    rw [mem_fixV] at h
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ v, ?_, ?_⟩
    · rw [mem_fixV]
      intro a ha
      have hx : (g * a * g⁻¹) v = v := h _ (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
      rw [MulAut.mul_apply, MulAut.mul_apply] at hx
      calc a (g⁻¹ v) = g⁻¹ (g (a (g⁻¹ v))) := (MulAut.inv_apply_self V g _).symm
        _ = g⁻¹ v := by rw [hx]
    · show g (g⁻¹ v) = v
      exact MulAut.apply_inv_self V g v
  · intro h
    rw [Subgroup.mem_map] at h
    obtain ⟨w, hw, rfl⟩ := h
    rw [mem_fixV] at hw ⊢
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have haw : a w = w := hw a ha
    show (g * a * g⁻¹) (g w) = g w
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self V g w, haw]

theorem index_fixV_map_conj {V : Type} [CommGroup V] [Finite V] (A : Subgroup (MulAut V))
    (g : MulAut V) : (fixV (A.map (MulAut.conj g).toMonoidHom)).index = (fixV A).index := by
  rw [fixV_map_conj]
  exact Subgroup.index_map_equiv (fixV A) g

private theorem a10k_isPGroup_two {G : Type*} [Group G] (K : Subgroup G)
    (hK : ∀ x ∈ K, x ^ 2 = 1) : IsPGroup 2 ↥K := by
  intro x
  refine ⟨1, ?_⟩
  show x ^ 2 = 1
  exact Subtype.ext (hK x.1 x.2)

theorem eq_one_of_mem_center {V : Type} [CommGroup V] [Finite V] {H L : Subgroup (MulAut V)}
    (hFF : FFHyp H L) {z : ↥L} (hz : z ∈ Subgroup.center ↥L) (hz2 : z ^ 2 = 1) : z = 1 := by
  have hLH : L ≤ H := by
    rw [hFF.1]
    exact quasithinGenFitting_le H
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    rw [hFF.1]
    exact le_normalizer_quasithinGenFitting H
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Subgroup ↥L,
      ∀ c : ↥L, c ∈ Ω ↔ c ∈ Subgroup.center ↥L ∧ c ^ 2 = 1 := by
    refine ⟨{ carrier := {c | c ∈ Subgroup.center ↥L ∧ c ^ 2 = 1}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun c => Iff.rfl⟩
    · rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
      show a * b ∈ Subgroup.center ↥L ∧ (a * b) ^ 2 = 1
      refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
      have hcomm : Commute a b := (Subgroup.mem_center_iff.mp ha b).symm
      rw [hcomm.mul_pow, ha2, hb2, mul_one]
    · show (1 : ↥L) ∈ Subgroup.center ↥L ∧ (1 : ↥L) ^ 2 = 1
      exact ⟨Subgroup.one_mem _, one_pow 2⟩
    · rintro a ⟨ha, ha2⟩
      show a⁻¹ ∈ Subgroup.center ↥L ∧ a⁻¹ ^ 2 = 1
      exact ⟨Subgroup.inv_mem _ ha, by rw [inv_pow, ha2, inv_one]⟩
  have hconjL : ∀ (g : ↥H) (y : ↥L),
      (g : MulAut V) * (y : MulAut V) * (g : MulAut V)⁻¹ ∈ L := by
    intro g y
    exact (Subgroup.mem_normalizer_iff.mp (hHN g.2) (y : MulAut V)).mp y.2
  have hconjL' : ∀ (g : ↥H) (y : ↥L),
      (g : MulAut V)⁻¹ * (y : MulAut V) * (g : MulAut V) ∈ L := by
    intro g y
    exact (Subgroup.mem_normalizer_iff''.mp (hHN g.2) (y : MulAut V)).mp y.2
  have hΩconj : ∀ (g : ↥H) (c : ↥L), c ∈ Ω →
      (g : MulAut V) * (c : MulAut V) * (g : MulAut V)⁻¹ ∈ Ω.map L.subtype := by
    intro g c hc
    obtain ⟨hcZ, hc2⟩ := (hΩ c).mp hc
    have hc'Ω : (⟨(g : MulAut V) * (c : MulAut V) * (g : MulAut V)⁻¹, hconjL g c⟩ : ↥L) ∈ Ω := by
      rw [hΩ]
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_center_iff]
        intro l
        apply Subtype.ext
        have hl' : (g : MulAut V)⁻¹ * (l : MulAut V) * (g : MulAut V) ∈ L := hconjL' g l
        have hcomm : (⟨(g : MulAut V)⁻¹ * (l : MulAut V) * (g : MulAut V), hl'⟩ : ↥L) * c
            = c * ⟨(g : MulAut V)⁻¹ * (l : MulAut V) * (g : MulAut V), hl'⟩ :=
          Subgroup.mem_center_iff.mp hcZ _
        have hcomm' : ((g : MulAut V)⁻¹ * (l : MulAut V) * (g : MulAut V)) * (c : MulAut V)
            = (c : MulAut V) * ((g : MulAut V)⁻¹ * (l : MulAut V) * (g : MulAut V)) :=
          congrArg Subtype.val hcomm
        show (l : MulAut V) * ((g : MulAut V) * (c : MulAut V) * (g : MulAut V)⁻¹)
          = ((g : MulAut V) * (c : MulAut V) * (g : MulAut V)⁻¹) * (l : MulAut V)
        calc (l : MulAut V) * ((g : MulAut V) * (c : MulAut V) * (g : MulAut V)⁻¹)
            = (g : MulAut V) * (((g : MulAut V)⁻¹ * (l : MulAut V) * (g : MulAut V))
                * (c : MulAut V)) * (g : MulAut V)⁻¹ := by group
          _ = (g : MulAut V) * ((c : MulAut V)
                * ((g : MulAut V)⁻¹ * (l : MulAut V) * (g : MulAut V))) * (g : MulAut V)⁻¹ := by
              rw [hcomm']
          _ = ((g : MulAut V) * (c : MulAut V) * (g : MulAut V)⁻¹) * (l : MulAut V) := by group
      · apply Subtype.ext
        show ((g : MulAut V) * (c : MulAut V) * (g : MulAut V)⁻¹) ^ 2 = 1
        have hc2' : (c : MulAut V) ^ 2 = 1 := congrArg Subtype.val hc2
        rw [conj_pow, hc2']
        simp
    exact Subgroup.mem_map.mpr ⟨_, hc'Ω, rfl⟩
  have hΩsq : ∀ y ∈ Ω.map L.subtype, y ^ 2 = 1 := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
    have hc2 : c ^ 2 = 1 := ((hΩ c).mp hc).2
    rw [← map_pow, hc2, map_one]
  have hnorm : ((Ω.map L.subtype).subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨c, hc, hcn⟩ := Subgroup.mem_map.mp hn
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hcn]
    exact hΩconj g c hc
  have hp : IsPGroup 2 ↥((Ω.map L.subtype).subgroupOf H) := by
    apply a10k_isPGroup_two
    intro x hx
    apply Subtype.ext
    exact hΩsq _ (Subgroup.mem_subgroupOf.mp hx)
  have hle := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hnorm hp
  rw [hFF.2.2.1, le_bot_iff] at hle
  have hzΩ : z ∈ Ω := (hΩ z).mpr ⟨hz, hz2⟩
  have hmem : (⟨(z : MulAut V), hLH z.2⟩ : ↥H) ∈ (Ω.map L.subtype).subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨z, hzΩ, rfl⟩)
  rw [hle, Subgroup.mem_bot] at hmem
  have hz1 : (z : MulAut V) = 1 := congrArg (Subtype.val : ↥H → MulAut V) hmem
  exact Subtype.ext hz1

private theorem a10k_map_conj_map {G N : Type*} [Group G] [Group N] (φ : G →* N) (x : G)
    (T : Subgroup G) :
    (T.map (MulAut.conj x).toMonoidHom).map φ
      = (T.map φ).map (MulAut.conj (φ x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  refine congrArg (fun h => Subgroup.map h T) ?_
  ext a
  simp [MulAut.conj_apply]

private theorem a10k_card_map_of_injOn {G N : Type*} [Group G] [Group N] (T : Subgroup G)
    (f : G →* N) (hinj : ∀ a ∈ T, ∀ b ∈ T, f a = f b → a = b) :
    Nat.card (T.map f) = Nat.card T := by
  have hinj' : Set.InjOn f (T : Set G) := by
    intro a ha b hb hab
    exact hinj a ha b hb hab
  have h := Nat.card_image_of_injOn hinj'
  rw [← Subgroup.coe_map] at h
  exact h

private theorem a10k_subgroupOf_map_subtype {G : Type*} [Group G] {E L : Subgroup G}
    (hEL : E ≤ L) : (E.subgroupOf L).map L.subtype = E :=
  (Subgroup.subgroupOf_map_subtype E L).trans (inf_eq_left.mpr hEL)

private theorem a10k_card_two_or_four {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (hK : ∀ x ∈ K, x ^ 2 = 1) (hK1 : K ≠ ⊥) (hK4 : Nat.card K ≤ 4) :
    Nat.card K = 2 ∨ Nat.card K = 4 := by
  obtain ⟨n, hn⟩ := (a10k_isPGroup_two K hK).exists_card_eq
  have h1 : Nat.card K ≠ 1 := fun h => hK1 (Subgroup.card_eq_one.mp h)
  have hn3 : n < 3 := by
    by_contra hc
    have hc' : 3 ≤ n := not_lt.mp hc
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc'
    rw [← hn] at h8
    norm_num at h8
    omega
  interval_cases n
  · rw [pow_zero] at hn
    exact absurd hn h1
  · rw [pow_one] at hn
    exact Or.inl hn
  · rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hn
    exact Or.inr hn

private theorem a10k_index_fixV_sup_le {V : Type} [CommGroup V] (A B : Subgroup (MulAut V)) :
    (fixV (A ⊔ B)).index ≤ (fixV A).index * (fixV B).index := by
  rw [fixV_sup]
  exact Subgroup.index_inf_le

private theorem a10k_index_fixV_sup_conj_le {V : Type} [CommGroup V] [Finite V]
    (A : Subgroup (MulAut V)) (g : MulAut V) :
    (fixV (A ⊔ A.map (MulAut.conj g).toMonoidHom)).index ≤ (fixV A).index * (fixV A).index := by
  calc (fixV (A ⊔ A.map (MulAut.conj g).toMonoidHom)).index
      ≤ (fixV A).index * (fixV (A.map (MulAut.conj g).toMonoidHom)).index :=
        a10k_index_fixV_sup_le _ _
    _ = (fixV A).index * (fixV A).index := by rw [index_fixV_map_conj]

theorem a10NoV4Offender_of (hP2 : P2Stmt) (hP4 : P4Stmt)
    (h25 : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ X : Subgroup (MulAut W), (fixV X).index ≤ 2 ^ 6 → ¬ 25 ∣ Nat.card X)
    (h5 : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ X : Subgroup (MulAut W), (fixV X).index ≤ 2 ^ 3 → ¬ 5 ∣ Nat.card X) :
    CFSG.RankThree.PartTwo.Sec15.F153.A10NoV4Offender := by
  classical
  intro V _ _ hV H L E hFF hφ hEL hE1 hEab hE4
  obtain ⟨φ⟩ := hφ
  obtain ⟨-, hEsq⟩ := hEab
  by_contra hlt
  have hlt' : Nat.card V ≤ Nat.card E * Nat.card (fixV E) := not_lt.mp hlt
  have hidxE : (fixV E).index ≤ Nat.card E := by
    haveI : Nonempty (fixV E) := ⟨1⟩
    have hpos : 0 < Nat.card (fixV E) := Nat.card_pos
    have h1 : (fixV E).index * Nat.card (fixV E) ≤ Nat.card E * Nat.card (fixV E) := by
      rw [Subgroup.index_mul_card]
      exact hlt'
    exact Nat.le_of_mul_le_mul_right h1 hpos
  have hEcard : Nat.card E = 2 ∨ Nat.card E = 4 := a10k_card_two_or_four E hEsq hE1 hE4
  obtain ⟨f, hf_def⟩ : ∃ f : ↥L →* Perm (Fin 10), ∀ x : ↥L,
      f x = ((φ (QuotientGroup.mk' (Subgroup.center ↥L) x) : alternatingGroup (Fin 10)) :
        Perm (Fin 10)) :=
    ⟨(alternatingGroup (Fin 10)).subtype.comp
      (φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))), fun x => rfl⟩
  have hf_mem : ∀ x : ↥L, f x ∈ alternatingGroup (Fin 10) := by
    intro x
    rw [hf_def]
    exact (φ _).2
  have hf_ker : ∀ x : ↥L, f x = 1 → x ∈ Subgroup.center ↥L := by
    intro x hx
    rw [hf_def] at hx
    have h1 : φ (QuotientGroup.mk' (Subgroup.center ↥L) x) = 1 := Subtype.ext hx
    have h2 : QuotientGroup.mk' (Subgroup.center ↥L) x = 1 :=
      φ.injective (h1.trans (map_one φ).symm)
    exact (QuotientGroup.eq_one_iff x).mp h2
  have hf_surj : ∀ a : Perm (Fin 10), a ∈ alternatingGroup (Fin 10) → ∃ x : ↥L, f x = a := by
    intro a ha
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) (φ.symm ⟨a, ha⟩)
    exact ⟨y, by rw [hf_def, hy, MulEquiv.apply_symm_apply]⟩
  have hEL_inj : ∀ a ∈ E.subgroupOf L, ∀ b ∈ E.subgroupOf L, f a = f b → a = b := by
    intro a ha b hb hab
    have ha' : (a : MulAut V) ∈ E := Subgroup.mem_subgroupOf.mp ha
    have hb' : (b : MulAut V) ∈ E := Subgroup.mem_subgroupOf.mp hb
    have hz1 : f (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have hz2 : (a⁻¹ * b) ^ 2 = 1 := by
      apply Subtype.ext
      exact hEsq _ (E.mul_mem (E.inv_mem ha') hb')
    exact inv_mul_eq_one.mp (eq_one_of_mem_center hFF (hf_ker _ hz1) hz2)
  have hEb_card : Nat.card ↥((E.subgroupOf L).map f) = Nat.card E := by
    rw [a10k_card_map_of_injOn _ f hEL_inj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  have hEb_le : (E.subgroupOf L).map f ≤ alternatingGroup (Fin 10) := by
    rintro _ ⟨x, _, rfl⟩
    exact hf_mem x
  have hEb_sq : ∀ y ∈ (E.subgroupOf L).map f, y ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx2 : x ^ 2 = 1 := by
      apply Subtype.ext
      exact hEsq _ (Subgroup.mem_subgroupOf.mp hx)
    rw [← map_pow, hx2, map_one]
  rcases hEcard with hE2 | hE4
  ·
    have hEb2 : Nat.card ↥((E.subgroupOf L).map f) = 2 := by rw [hEb_card, hE2]
    obtain ⟨g, hgA, hdiv⟩ := hP2 _ hEb_le hEb2
    obtain ⟨g', hg'⟩ := hf_surj g hgA
    have himg : ((E.subgroupOf L) ⊔ (E.subgroupOf L).map (MulAut.conj g').toMonoidHom).map f
        = (E.subgroupOf L).map f ⊔ ((E.subgroupOf L).map f).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_sup, a10k_map_conj_map f g' (E.subgroupOf L), hg']
    have hXL : 5 ∣ Nat.card ↥((E.subgroupOf L) ⊔ (E.subgroupOf L).map (MulAut.conj g').toMonoidHom) := by
      have h1 : 5 ∣ Nat.card ↥(((E.subgroupOf L) ⊔
          (E.subgroupOf L).map (MulAut.conj g').toMonoidHom).map f) := by
        rw [himg]
        exact hdiv
      exact dvd_trans h1 (Subgroup.card_map_dvd _ f)
    have hXeq : E ⊔ E.map (MulAut.conj (g' : MulAut V)).toMonoidHom
        = ((E.subgroupOf L) ⊔ (E.subgroupOf L).map (MulAut.conj g').toMonoidHom).map L.subtype := by
      rw [Subgroup.map_sup, a10k_map_conj_map L.subtype g' (E.subgroupOf L),
        a10k_subgroupOf_map_subtype hEL]
      try rfl
    have h5dvd : 5 ∣ Nat.card ↥(E ⊔ E.map (MulAut.conj (g' : MulAut V)).toMonoidHom) := by
      rw [hXeq, Subgroup.card_map_of_injective L.subtype_injective]
      exact hXL
    have hidx : (fixV (E ⊔ E.map (MulAut.conj (g' : MulAut V)).toMonoidHom)).index ≤ 2 ^ 3 := by
      have h2 : (fixV E).index ≤ 2 := hidxE.trans (le_of_eq hE2)
      calc (fixV (E ⊔ E.map (MulAut.conj (g' : MulAut V)).toMonoidHom)).index
          ≤ (fixV E).index * (fixV E).index := a10k_index_fixV_sup_conj_le E (g' : MulAut V)
        _ ≤ 2 * 2 := Nat.mul_le_mul h2 h2
        _ ≤ 2 ^ 3 := by norm_num
    exact h5 V hV _ hidx h5dvd
  ·
    have hEb4 : Nat.card ↥((E.subgroupOf L).map f) = 4 := by rw [hEb_card, hE4]
    obtain ⟨g, hgA, k, hkA, hdiv⟩ := hP4 _ hEb_le hEb_sq hEb4
    obtain ⟨g', hg'⟩ := hf_surj g hgA
    obtain ⟨k', hk'⟩ := hf_surj k hkA
    have himg : (((E.subgroupOf L) ⊔ (E.subgroupOf L).map (MulAut.conj g').toMonoidHom)
          ⊔ (E.subgroupOf L).map (MulAut.conj k').toMonoidHom).map f
        = ((E.subgroupOf L).map f ⊔ ((E.subgroupOf L).map f).map (MulAut.conj g).toMonoidHom)
          ⊔ ((E.subgroupOf L).map f).map (MulAut.conj k).toMonoidHom := by
      rw [Subgroup.map_sup, Subgroup.map_sup, a10k_map_conj_map f g' (E.subgroupOf L),
        a10k_map_conj_map f k' (E.subgroupOf L), hg', hk']
    have hXL : 25 ∣ Nat.card ↥(((E.subgroupOf L) ⊔ (E.subgroupOf L).map (MulAut.conj g').toMonoidHom)
          ⊔ (E.subgroupOf L).map (MulAut.conj k').toMonoidHom) := by
      have h1 : 25 ∣ Nat.card ↥((((E.subgroupOf L) ⊔
            (E.subgroupOf L).map (MulAut.conj g').toMonoidHom)
          ⊔ (E.subgroupOf L).map (MulAut.conj k').toMonoidHom).map f) := by
        rw [himg]
        exact hdiv
      exact dvd_trans h1 (Subgroup.card_map_dvd _ f)
    have hXeq : (E ⊔ E.map (MulAut.conj (g' : MulAut V)).toMonoidHom)
          ⊔ E.map (MulAut.conj (k' : MulAut V)).toMonoidHom
        = (((E.subgroupOf L) ⊔ (E.subgroupOf L).map (MulAut.conj g').toMonoidHom)
          ⊔ (E.subgroupOf L).map (MulAut.conj k').toMonoidHom).map L.subtype := by
      rw [Subgroup.map_sup, Subgroup.map_sup, a10k_map_conj_map L.subtype g' (E.subgroupOf L),
        a10k_map_conj_map L.subtype k' (E.subgroupOf L), a10k_subgroupOf_map_subtype hEL]
      try rfl
    have h25dvd : 25 ∣ Nat.card ↥((E ⊔ E.map (MulAut.conj (g' : MulAut V)).toMonoidHom)
          ⊔ E.map (MulAut.conj (k' : MulAut V)).toMonoidHom) := by
      rw [hXeq, Subgroup.card_map_of_injective L.subtype_injective]
      exact hXL
    have hidx : (fixV ((E ⊔ E.map (MulAut.conj (g' : MulAut V)).toMonoidHom)
          ⊔ E.map (MulAut.conj (k' : MulAut V)).toMonoidHom)).index ≤ 2 ^ 6 := by
      have h4 : (fixV E).index ≤ 4 := hidxE.trans (le_of_eq hE4)
      have hk_idx := index_fixV_map_conj E (k' : MulAut V)
      have hsum := a10k_index_fixV_sup_le (E ⊔ E.map (MulAut.conj (g' : MulAut V)).toMonoidHom)
        (E.map (MulAut.conj (k' : MulAut V)).toMonoidHom)
      have hg_le := a10k_index_fixV_sup_conj_le E (g' : MulAut V)
      calc (fixV ((E ⊔ E.map (MulAut.conj (g' : MulAut V)).toMonoidHom)
            ⊔ E.map (MulAut.conj (k' : MulAut V)).toMonoidHom)).index
          ≤ (fixV (E ⊔ E.map (MulAut.conj (g' : MulAut V)).toMonoidHom)).index
              * (fixV (E.map (MulAut.conj (k' : MulAut V)).toMonoidHom)).index := hsum
        _ = (fixV (E ⊔ E.map (MulAut.conj (g' : MulAut V)).toMonoidHom)).index
              * (fixV E).index := by rw [hk_idx]
        _ ≤ ((fixV E).index * (fixV E).index) * (fixV E).index := Nat.mul_le_mul hg_le (le_refl _)
        _ ≤ 4 * 4 * 4 := Nat.mul_le_mul (Nat.mul_le_mul h4 h4) h4
        _ ≤ 2 ^ 6 := by norm_num
    exact h25 V hV _ hidx h25dvd

end CFSG.RankThree.PartTwo.Sec15.F153A10K
