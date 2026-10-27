module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenMod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenModOdd
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

theorem s16c167_commSub_top_conj (φ : MulAut W) (Y : Subgroup (MulAut W)) :
    commSub (⊤ : Subgroup W) (Y.map (MulAut.conj φ).toMonoidHom) =
      (commSub (⊤ : Subgroup W) Y).map φ.toMonoidHom := by
  have hgen : {c : W | ∃ x ∈ Y.map (MulAut.conj φ).toMonoidHom,
        ∃ w ∈ (⊤ : Subgroup W), x w * w⁻¹ = c} =
      φ.toMonoidHom '' {c : W | ∃ x ∈ Y, ∃ w ∈ (⊤ : Subgroup W), x w * w⁻¹ = c} := by
    ext c
    constructor
    · rintro ⟨x, hx, w, -, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨y (φ⁻¹ w) * (φ⁻¹ w)⁻¹, ⟨y, hy, φ⁻¹ w, Subgroup.mem_top _, rfl⟩, by
        simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv]⟩
    · rintro ⟨d, ⟨y, hy, w, -, rfl⟩, rfl⟩
      exact ⟨MulAut.conj φ y, Subgroup.mem_map_of_mem _ hy, φ w, Subgroup.mem_top _, by
        simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv]⟩
  unfold commSub
  rw [hgen, MonoidHom.map_closure]

theorem s16c167_normalizes_of_stab {X L : Subgroup (MulAut W)}
    (hcls : Set.ncard {Y : Subgroup (MulAut W) |
      ∃ φ ∈ X, Y = L.map (MulAut.conj φ).toMonoidHom} = 2)
    (horb : (conjSubs X (commSub (⊤ : Subgroup W) L)).ncard = 2) :
    ∀ Y ∈ {Y : Subgroup (MulAut W) | ∃ φ ∈ X, Y = L.map (MulAut.conj φ).toMonoidHom},
      ∀ t ∈ X, (commSub (⊤ : Subgroup W) Y).map t.toMonoidHom = commSub (⊤ : Subgroup W) Y →
        Y.map (MulAut.conj t).toMonoidHom = Y := by
  let f : Subgroup (MulAut W) → Subgroup W := fun Y => commSub (⊤ : Subgroup W) Y
  have hfin : ({Y : Subgroup (MulAut W) |
      ∃ φ ∈ X, Y = L.map (MulAut.conj φ).toMonoidHom}).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hcls]; norm_num)
  have himage : f '' {Y : Subgroup (MulAut W) |
      ∃ φ ∈ X, Y = L.map (MulAut.conj φ).toMonoidHom}
      = conjSubs X (commSub (⊤ : Subgroup W) L) := by
    ext Z
    constructor
    · rintro ⟨Y, ⟨φ, hφX, rfl⟩, rfl⟩
      exact ⟨φ, hφX, s16c167_commSub_top_conj φ L⟩
    · rintro ⟨φ, hφX, rfl⟩
      exact ⟨L.map (MulAut.conj φ).toMonoidHom, ⟨φ, hφX, rfl⟩,
        s16c167_commSub_top_conj φ L⟩
  have hinj : Set.InjOn f {Y : Subgroup (MulAut W) |
      ∃ φ ∈ X, Y = L.map (MulAut.conj φ).toMonoidHom} :=
    (Set.ncard_image_iff hfin).mp (by rw [himage, horb, hcls])
  intro Y hY t htX hstab
  obtain ⟨φ, hφX, rfl⟩ := hY
  have hmem1 : L.map (MulAut.conj (t * φ)).toMonoidHom ∈
      {Y : Subgroup (MulAut W) | ∃ ψ ∈ X, Y = L.map (MulAut.conj ψ).toMonoidHom} :=
    ⟨t * φ, X.mul_mem htX hφX, rfl⟩
  have hmem2 : L.map (MulAut.conj φ).toMonoidHom ∈
      {Y : Subgroup (MulAut W) | ∃ ψ ∈ X, Y = L.map (MulAut.conj ψ).toMonoidHom} :=
    ⟨φ, hφX, rfl⟩
  have hcomp : (MulAut.conj t).toMonoidHom.comp (MulAut.conj φ).toMonoidHom =
      (MulAut.conj (t * φ)).toMonoidHom := by
    rw [map_mul (MulAut.conj) t φ]
    ext y
    rfl
  have hmap2 : (L.map (MulAut.conj φ).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      L.map (MulAut.conj (t * φ)).toMonoidHom := by
    rw [Subgroup.map_map, hcomp]
  have hfeq : f (L.map (MulAut.conj (t * φ)).toMonoidHom) =
      f (L.map (MulAut.conj φ).toMonoidHom) := by
    have h1 : f (L.map (MulAut.conj (t * φ)).toMonoidHom) =
        (commSub (⊤ : Subgroup W) (L.map (MulAut.conj φ).toMonoidHom)).map
          t.toMonoidHom := by
      change commSub (⊤ : Subgroup W) (L.map (MulAut.conj (t * φ)).toMonoidHom) = _
      rw [← hmap2, s16c167_commSub_top_conj t (L.map (MulAut.conj φ).toMonoidHom)]
    rw [h1, hstab]
  exact hmap2.trans (hinj hmem1 hmem2 hfeq)

variable [Finite W]

theorem s16c167_cyclic3_block (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hY : IsCyclicOrd ↥Y 3) (hrk : 4 ≤ rk ↥(commSub (⊤ : Subgroup W) Y)) {t : MulAut W}
    (ht : t * t = 1) (hn : Y.map (MulAut.conj t).toMonoidHom = Y) :
    commSub (⊤ : Subgroup W) Y ≤ fixV (Subgroup.zpowers t) ∨
      2 ≤ E3.mQuot (commSub (⊤ : Subgroup W) Y)
        (commSub (⊤ : Subgroup W) Y ⊓ fixV (Subgroup.zpowers t)) := by
  obtain ⟨a, ha⟩ := hY.1.exists_generator
  have hord : orderOf a = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, hY.2]
  let a' : MulAut W := (a : MulAut W)
  have ha' : orderOf a' = 3 := by
    change orderOf (a : MulAut W) = 3
    rw [Subgroup.orderOf_coe]
    exact hord
  have hYeq : Y = Subgroup.zpowers a' := by
    haveI : Finite ↥Y := Nat.finite_of_card_ne_zero (by rw [hY.2]; norm_num)
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · exact Subgroup.zpowers_le.mpr a.2
    · have hcard : Nat.card (Subgroup.zpowers a') = Nat.card ↥Y := by
        rw [Nat.card_zpowers, ha', hY.2]
      omega
  have stable_of_normalizes : ∀ {g : MulAut W},
      (∀ x ∈ Y, g * x * g⁻¹ ∈ Y) →
      (commSub (⊤ : Subgroup W) Y).map g.toMonoidHom = commSub (⊤ : Subgroup W) Y := by
    intro g hg
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro c hc
      rw [Subgroup.mem_map] at hc
      obtain ⟨d, hd, rfl⟩ := hc
      exact commSub_top_stable151b hg d hd
    · rw [Subgroup.card_map_of_injective g.injective]
  have hIa : (commSub (⊤ : Subgroup W) Y).map a'.toMonoidHom = commSub (⊤ : Subgroup W) Y :=
    stable_of_normalizes fun x hx => Y.mul_mem (Y.mul_mem a.2 hx) (Y.inv_mem a.2)
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one]; exact ht
  have hIt : (commSub (⊤ : Subgroup W) Y).map t.toMonoidHom = commSub (⊤ : Subgroup W) Y := by
    refine stable_of_normalizes fun x hx => ?_
    have h : (MulAut.conj t) x ∈ Y.map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hx
    rw [hn] at h
    simpa [MulAut.conj_apply, htinv] using h
  have hfix : commSub (⊤ : Subgroup W) Y ⊓ fixV (Subgroup.zpowers a') = ⊥ := by
    have hodd : Odd (Nat.card ↥Y) := by rw [hY.2]; norm_num
    have hcop := (coprime_decomp (P := Y) hodd hW
      (W := (⊤ : Subgroup W)) (fun g _ w _ => Subgroup.mem_top w)).2
    have hYfix : fixV Y = fixV (Subgroup.zpowers a') := by rw [hYeq]
    rwa [top_inf_eq, hYfix] at hcop
  have hmem : t * a' * t ∈ Subgroup.zpowers a' := by
    have h : (MulAut.conj t) a' ∈ Y.map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom a.2
    rw [hn, hYeq] at h
    simpa [MulAut.conj_apply, htinv] using h
  have hta : t * a' * t = a'⁻¹ ∨ t * a' = a' * t := by
    rcases s16c167_conj_eq_or_inv Nat.prime_three ha' ht hmem with h | h
    · right
      calc t * a' = t * a' * (t * t) := by rw [ht, mul_one]
        _ = t * a' * t * t := by group
        _ = a' * t := by rw [h]
    · left; exact h
  exact s16c167_oe3 hW ha' ht hta hIa hIt hfix hrk

theorem s16c167_cfg10_abstract (hW : ∀ w : W, w ^ 2 = 1) {X L : Subgroup (MulAut W)}
    (hL : IsCyclicOrd ↥L 3) (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 4)
    (hcls : Set.ncard {Y : Subgroup (MulAut W) |
      ∃ φ ∈ X, Y = L.map (MulAut.conj φ).toMonoidHom} = 2)
    (horb : (conjSubs X (commSub (⊤ : Subgroup W) L)).ncard = 2)
    (hind : sSupIndep (conjSubs X (commSub (⊤ : Subgroup W) L)))
    (hsup : sSup (conjSubs X (commSub (⊤ : Subgroup W) L)) = ⊤) :
    (∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L), rk ↥I = 4) ∧
      (∀ t ∈ X, ∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L),
        I.map t.toMonoidHom = I ∨ I ⊓ I.map t.toMonoidHom = ⊥) ∧
      (∀ t ∈ X, t * t = 1 → ∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L),
        I.map t.toMonoidHom = I → I ≤ fixV (Subgroup.zpowers t) ∨
          2 ≤ E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t))) ∧
      2 ≤ E3.mParam X := by
  obtain ⟨I₁, I₂, hne, hset⟩ := Set.ncard_eq_two.1 horb
  have hdisj : I₁ ⊓ I₂ = ⊥ :=
    disjoint_iff.mp ((sSupIndep_pair hne).mp (hset ▸ hind))
  have hsup' : I₁ ⊔ I₂ = ⊤ := by
    have h : sSup ({I₁, I₂} : Set (Subgroup W)) = ⊤ := by rw [← hset]; exact hsup
    rwa [sSup_pair] at h
  have hrank : ∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L), rk ↥I = 4 := by
    intro I hI
    obtain ⟨φ, hφX, rfl⟩ := hI
    rw [rk_map_aut_eq]
    exact hrk
  have hperm' : ∀ t ∈ X, ∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L),
      I.map t.toMonoidHom = I ∨ I ⊓ I.map t.toMonoidHom = ⊥ := by
    intro t htX I hI
    exact s16c167_perm_of_orbit hne hdisj hset t htX I (hset ▸ hI)
  have hloc' : ∀ t ∈ X, t * t = 1 → ∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L),
      I.map t.toMonoidHom = I → I ≤ fixV (Subgroup.zpowers t) ∨
        2 ≤ E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) := by
    intro t htX ht I hI hstab
    obtain ⟨φ, hφX, rfl⟩ := hI
    have hcomm := s16c167_commSub_top_conj φ L
    rw [← hcomm] at hstab ⊢
    have e : ↥L ≃* ↥(L.map (MulAut.conj φ).toMonoidHom) :=
      Subgroup.equivMapOfInjective L (MulAut.conj φ).toMonoidHom (MulAut.conj φ).injective
    have hYcyc : IsCyclic ↥(L.map (MulAut.conj φ).toMonoidHom) :=
      (MulEquiv.isCyclic e).mp hL.1
    have hYcard : Nat.card ↥(L.map (MulAut.conj φ).toMonoidHom) = 3 := by
      rw [← Nat.card_congr e.toEquiv, hL.2]
    have hY : IsCyclicOrd ↥(L.map (MulAut.conj φ).toMonoidHom) 3 := ⟨hYcyc, hYcard⟩
    have hn' : (L.map (MulAut.conj φ).toMonoidHom).map (MulAut.conj t).toMonoidHom =
        L.map (MulAut.conj φ).toMonoidHom :=
      s16c167_normalizes_of_stab hcls horb (L.map (MulAut.conj φ).toMonoidHom)
        ⟨φ, hφX, rfl⟩ t htX hstab
    have hrk' : 4 ≤ rk ↥(commSub (⊤ : Subgroup W) (L.map (MulAut.conj φ).toMonoidHom)) := by
      have h4 : rk ↥(commSub (⊤ : Subgroup W) (L.map (MulAut.conj φ).toMonoidHom)) = 4 := by
        rw [hcomm, rk_map_aut_eq]
        exact hrk
      omega
    exact s16c167_cyclic3_block hW hY hrk' ht hn'
  have hI₁ : I₁ ∈ conjSubs X (commSub (⊤ : Subgroup W) L) := by rw [hset]; simp
  have hI₂ : I₂ ∈ conjSubs X (commSub (⊤ : Subgroup W) L) := by rw [hset]; simp
  have hn₁ : 2 ≤ rk ↥I₁ := by have := hrank I₁ hI₁; omega
  have hn₂ : 2 ≤ rk ↥I₂ := by have := hrank I₂ hI₂; omega
  have hperm : ∀ t ∈ X, t * t = 1 → ∀ I ∈ ({I₁, I₂} : Set (Subgroup W)),
      I.map t.toMonoidHom = I ∨ I ⊓ I.map t.toMonoidHom = ⊥ := by
    intro t htX _ I hI
    exact hperm' t htX I (hset ▸ hI)
  have hloc : ∀ t ∈ X, t * t = 1 → ∀ I ∈ ({I₁, I₂} : Set (Subgroup W)),
      I.map t.toMonoidHom = I → I ≤ fixV (Subgroup.zpowers t) ∨
        2 ≤ E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) := by
    intro t htX ht I hI
    exact hloc' t htX ht I (hset ▸ hI)
  exact ⟨hrank, hperm', hloc',
    s16c167_le_mParam_of_blocks hW X (n := 2) hdisj hsup' hn₁ hn₂ hperm hloc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
